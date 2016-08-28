/*
 * heap_tcmalloc.c
 *
 *  Created on: August 27, 2016
 *      Author: myan
 */

#include "heap_tcmalloc.h"
#include "segment.h"


#define CA_DEBUG 0
#if CA_DEBUG
#define CA_PRINT_DBG CA_PRINT
#else
#define CA_PRINT_DBG(format,args...)
#endif


/*
 * This Implementation uses gdb specific types
 */

/*
 * Globals
 */
static bool g_initialized = false;

static struct ca_config g_config;

static struct ca_span *g_spans;
static unsigned long g_spans_capacity;
static unsigned long g_spans_count;
static unsigned long skip_npage;

static address_t *g_cached_blocks;
static unsigned long g_cached_blocks_capacity;
static unsigned long g_cached_blocks_count;

/*
 * Forward declaration
 */
static void gdb_symbol_prelude(void);
static int type_field_name2no(struct type *, const char *);
static bool parse_config(void);
static bool parse_pagemap(void);
static bool parse_thread_cache(void);
static bool parse_central_cache(void);
static bool parse_leaf(struct value *, struct type *);
static bool parse_span(struct value *);
static bool parse_thread_cache_lists(struct value *);
static bool parse_central_freelist(struct value *);
static bool parse_central_freelist_tcentry(struct value *, bool *);

static bool cached_block_add(address_t);
static int cached_block_compare(const void *, const void *);
static int cached_block_search_compare(const void *, const void *);
static bool verify_sorted_cached_blocks(void);
static bool is_block_cached(address_t);

static struct ca_span *span_get(address_t);
static int span_search_compare(const void *, const void *);
static bool verify_sorted_spans(void);
static bool span_block_free(struct ca_span*, address_t);
static bool span_populate_free_bitmap(struct ca_span*);

/******************************************************************************
 * Exposed functions
 *****************************************************************************/
bool
init_heap(void)
{
	unsigned long i;

	gdb_symbol_prelude();

	if (parse_config() == false ||
	    parse_pagemap() == false ||
	    parse_thread_cache() == false ||
	    parse_central_cache() == false) {
		return false;
	}

	qsort(g_cached_blocks, g_cached_blocks_count, sizeof(*g_cached_blocks),
	    cached_block_compare);
	if (verify_sorted_cached_blocks() == false ||
	    verify_sorted_spans() == false) {
		return false;
	}

	/*
	 * Show result
	 */
	CA_PRINT_DBG("%ld Spans are found\n", g_spans_count);
	for (i = 0; i < g_spans_count; i++) {
		struct ca_span *span = &g_spans[i];

		CA_PRINT_DBG("[%ld] {\n"
		    "\tstart %ld\n"
		    "\tlength %ld\n"
		    "\tnext %#lx\n"
		    "\tprev %#lx\n"
		    "\tobjects %#lx\n"
		    "\trefcount %d\n"
		    "\tsizeclass %d\n"
		    "\tlocation %d\n"
		    "\tsample %d\n"
		    "}\n",
		    i, span->start, span->length, span->next, span->prev,
		    span->objects, span->refcount, span->sizeclass,
		    span->location, span->sample);
	}
	CA_PRINT_DBG("thread/central cached blocks %ld\n", g_cached_blocks_count);

	CA_PRINT_DBG("tcmalloc heap is initialized successfully\n");
	g_initialized = true;
	return true;
}

bool
get_heap_block_info(address_t addr, struct heap_block* blk)
{
	struct ca_span *span;
	address_t base;

	if (g_initialized == false) {
		CA_PRINT("tcmalloc heap was not initialized successfully\n");
		return false;
	}

	/*
	 * No span means the address is not managed by tcmalloc
	 */
	span = span_get(addr);
	if (span == NULL)
		return false;

	/*
	 * The whole span is free
	 */
	if (span->location != IN_USE) {
		blk->inuse = false;
		blk->addr = span->start << g_config.kPageShift;
		blk->size = span->length << g_config.kPageShift;
		return true;
	}

	/*
	 * Block size by class
	 */
	if (span->sizeclass != 0)
		blk->size = g_config.sizemap.class_to_size[span->sizeclass];
	else
		blk->size = span->length << g_config.kPageShift;

	/*
	 * Block address is on fixed-size boundary
	 */
	base = span->start << g_config.kPageShift;
	blk->addr = addr - ((addr - base) % blk->size);

	/*
	 * Block status needs to consult span's object list and all cache lists
	 */
	span_populate_free_bitmap(span);
	if (span_block_free(span, blk->addr) == true)
		blk->inuse = false;
	else
		blk->inuse = true;

	return true;
}

bool
get_next_heap_block(address_t addr, struct heap_block* blk)
{
	struct ca_span *span, *last_span, *next;
	unsigned long pageid;

	if (g_initialized == false) {
		CA_PRINT("tcmalloc heap was not initialized successfully\n");
		return false;
	}

	if (addr == 0) {
		if (g_spans_count == 0) {
			CA_PRINT("There is not heap block\n");
			return false;
		}
		/*
		* Return the first block with lowest address
		*/
		span = &g_spans[0];
	} else {
		span = span_get(addr);
		if (span == NULL) {
			CA_PRINT("The input address %#lx doesn't belong to "
			    "the heap\n", addr);
			return false;
		}

		if (span->location == IN_USE && span->sizeclass != 0) {
			size_t blk_sz = g_config.sizemap.class_to_size[span->sizeclass];
			address_t base = span->start << g_config.kPageShift;
			unsigned int index = (addr - base) / blk_sz;
			unsigned n, bit;
			if (index < span->count -1 ) {
				index++;
				blk->addr = base + index * blk_sz;
				blk->size = blk_sz;
				n = index / UINT_BITS;
				bit = index - n * UINT_BITS;
				blk->inuse = !(span->bitmap[n] & (1 << bit));
				return true;
			}
		}

		/*
		* The next block is in the next span
		*/
		last_span = &g_spans[g_spans_count - 1];
		next = NULL;
		for (pageid = span->start + span->length;
		    pageid <= last_span->start;
		    pageid++) {
			next = span_get(pageid << g_config.kPageShift);
			if (next != NULL)
				break;
		}
		if (next == NULL)
			return false;
		span = next;
	}

	span_populate_free_bitmap(span);
	blk->addr = span->start << g_config.kPageShift;
	if (span->location != IN_USE) {
		blk->size = span->length << g_config.kPageShift;
		blk->inuse = false;
	} else if (span->sizeclass == 0) {
		blk->size = span->length << g_config.kPageShift;
		blk->inuse = true;
	} else {
		blk->size = g_config.sizemap.class_to_size[span->sizeclass];
		blk->inuse = !(span->bitmap[0] & 1);
	}

	return true;
}

/* Return true if the block belongs to a heap */
bool
is_heap_block(address_t addr)
{

	if (g_initialized == false) {
		CA_PRINT("tcmalloc heap was not initialized successfully\n");
		return false;
	}

	return span_get(addr) != NULL;
}

/*
 * Traverse all heaps unless a non-zero address is given, in which case the
 * specific heap is used
 */
bool
heap_walk(address_t heapaddr, bool verbose)
{

	if (g_initialized == false) {
		CA_PRINT("tcmalloc heap was not initialized successfully\n");
		return false;
	}

	CA_PRINT("heap API heap_walk() is yet Implemented\n");
	return true;
}

bool
get_biggest_blocks(struct heap_block* blks, unsigned int num)
{

	if (g_initialized == false) {
		CA_PRINT("tcmalloc heap was not initialized successfully\n");
		return false;
	}

	CA_PRINT("heap API get_biggest_blocks() is yet Implemented\n");
	return true;
}

bool
walk_inuse_blocks(struct inuse_block* opBlocks, unsigned long* opCount)
{
	unsigned long i;
	struct ca_span *span;

	if (g_initialized == false) {
		CA_PRINT("tcmalloc heap was not initialized successfully\n");
		return false;
	}

	*opCount = 0;
	for (i = 0; i < g_spans_count; i++) {
		span = &g_spans[i];
		span_populate_free_bitmap(span);

		if (span->location != IN_USE)
			continue;

		if (span->sizeclass == 0) {
			(*opCount)++;
			if (opBlocks != NULL) {
				opBlocks->addr = span->start << g_config.kPageShift;
				opBlocks->size = span->length << g_config.kPageShift;
				opBlocks++;
			}
		} else {
			address_t base = span->start << g_config.kPageShift;
			unsigned int index;
			size_t blk_sz = g_config.sizemap.class_to_size[span->sizeclass];

			for (index = 0; index < span->count; index++) {
				unsigned int n, bit;

				n = index / UINT_BITS;
				bit = index - n * UINT_BITS;
				if (!(span->bitmap[n] & (1 << bit))) {
					(*opCount)++;
					if (opBlocks != NULL) {
						opBlocks->addr = base + index * blk_sz;
						opBlocks->size = blk_sz;
						opBlocks++;
					}
				}
			}
		}
	}

	return true;
}

/******************************************************************************
 * Helper Functions
 *****************************************************************************/

void
gdb_symbol_prelude(void)
{
	struct symbol *pagemap3;

	/*
	 * template <int BITS>
	 *     class TCMalloc_PageMap3 
	 */
	pagemap3 = lookup_symbol("TCMalloc_PageMap3<35>", 0, VAR_DOMAIN, 0);
	if (pagemap3 == NULL) {
		CA_PRINT_DBG("Failed to lookup type \"TCMalloc_PageMap3<35>\""
		    "\n");
	}

	return;
}

struct ca_span *
span_get(address_t addr)
{
	struct ca_span *span;
	unsigned long pageid;

	pageid = addr >> g_config.kPageShift;
	span = bsearch(&pageid, (void *)g_spans, g_spans_count,
	    sizeof(struct ca_span), span_search_compare);

	return span;
}

bool
parse_config(void)
{
	struct symbol *pageshift_;
	struct symbol *sizemap_;
	struct value *sizemap;
	struct value *class_to_size;
	int fieldno;
	LONGEST low_bound, high_bound, index;

	/*
	 * Global var
	 * static const size_t kPageShift;
	 */
	pageshift_ = lookup_symbol("kPageShift", 0, VAR_DOMAIN, 0);
	if (pageshift_ == NULL) {
		CA_PRINT("Failed to lookup gv \"kPageShift\"\n");
		return false;
	}
	g_config.kPageShift = value_as_long(value_of_variable(pageshift_, 0));

	/*
	 * Global var
	 * tcmalloc::Static::sizemap_
	 */
	sizemap_ = lookup_symbol_global("tcmalloc::Static::sizemap_", 0,
	    VAR_DOMAIN);
	if (sizemap_ == NULL) {
		CA_PRINT("Failed to lookup gv "
		    "\"tcmalloc::Static::sizemap_\"\n");
		return false;
	}
	sizemap = value_of_variable(sizemap_, 0);

	/*
	 * tcmalloc::Static::sizemap_.class_to_size_
	 */
	fieldno = type_field_name2no(value_type(sizemap), "class_to_size_");
	if (fieldno < 0) {
		CA_PRINT("Failed to find member \"class_to_size_\"\n");
		return false;
	}
	class_to_size = value_field (sizemap, fieldno);
	if (TYPE_CODE (value_type(class_to_size)) != TYPE_CODE_ARRAY) {
		CA_PRINT("Unexpected \"class_to_size\" is not an array\n");
		return false;
	}
	if (get_array_bounds (value_type(class_to_size), &low_bound,
	    &high_bound) == 0) {
		CA_PRINT("Could not determine \"class_to_size\" bounds\n");
		return false;
	}

	g_config.kNumClasses = high_bound - low_bound + 1;
	g_config.sizemap.class_to_size = calloc(g_config.kNumClasses,
	    sizeof(size_t));
	g_config.sizemap.class_to_pages = calloc(g_config.kNumClasses,
	    sizeof(size_t));
	g_config.sizemap.num_objects_to_move = calloc(g_config.kNumClasses,
	    sizeof(int));
	if (g_config.sizemap.class_to_size == NULL ||
	    g_config.sizemap.class_to_pages == NULL ||
	    g_config.sizemap.num_objects_to_move == NULL) {
		CA_PRINT("Out of memory\n");
		return false;
	}

	/*
	 * tcmalloc::Static::sizemap_.class_to_size_[index]
	 */
	for (index = low_bound; index <= high_bound; index++) {
		struct value *v;

		v = value_subscript(class_to_size, index);
		g_config.sizemap.class_to_size[index] = value_as_long(v);
	}

	return true;
}

bool
parse_pagemap(void)
{
	struct symbol *pageheap_;
	struct value *pageheap_p, *pageheap;
	struct value *pagemap;
	struct value *root_p, *root;
	struct value *ptrs;
	int fieldno;
	LONGEST low_bound, high_bound, index;
	struct type *leaf_type, *span_type;

	/*
	 * We need to cast a void* to this type later
	 */
	leaf_type = lookup_transparent_type("TCMalloc_PageMap3<35>::Leaf");
	span_type = lookup_transparent_type("tcmalloc::Span");
	if (leaf_type == NULL || span_type == NULL) {
		CA_PRINT("Failed to lookup type "
		    "\"TCMalloc_PageMap3<35>::Leaf\" and "
		    "\"tcmalloc::Span\"\n");
		CA_PRINT("Do you forget to download debug symbol of "
		    "libtcmalloc?\n");
		return false;
	}
	leaf_type = lookup_pointer_type(leaf_type);
	span_type = lookup_pointer_type(span_type);

	/*
	 * Global var
	 * tcmalloc::PageHeap *tcmalloc::Static::pageheap_;
	 */
	pageheap_ = lookup_symbol_global("tcmalloc::Static::pageheap_", 0,
	    VAR_DOMAIN);
	if (pageheap_ == NULL) {
		CA_PRINT("Failed to lookup gv "
		    "\"tcmalloc::Static::pageheap_\"\n");
		return false;
	}
	pageheap_p = value_of_variable(pageheap_, 0);
	pageheap = value_ind(pageheap_p);

	/*
	 * tcmalloc::Static::pageheap_->pagemap_
	 */
	fieldno = type_field_name2no(value_type(pageheap), "pagemap_");
	if (fieldno < 0) {
		CA_PRINT("Failed to find member \"pagemap_\"\n");
		return false;
	}
	pagemap = value_field (pageheap, fieldno);

	/*
	 * tcmalloc::Static::pageheap_->pagemap_.root_
	 */
	fieldno = type_field_name2no(value_type(pagemap), "root_");
	if (fieldno < 0) {
		CA_PRINT("Failed to find member \"root_\"\n");
		return false;
	}
	root_p = value_field(pagemap, fieldno);
	root = value_ind(root_p);

	/*
	 * tcmalloc::Static::pageheap_->pagemap_.root_->ptrs
	 */
	fieldno = type_field_name2no(value_type(root), "ptrs");
	ptrs = value_field(root, fieldno);
	if (TYPE_CODE (value_type(ptrs)) != TYPE_CODE_ARRAY) {
		CA_PRINT("Unexpected \"ptrs\" is not an array\n");
		return false;
	}
	if (get_array_bounds (value_type(ptrs), &low_bound, &high_bound) == 0) {
		CA_PRINT("Could not determine \"ptrs\" bounds\n");
		return false;
	}
	CA_PRINT_DBG("tcmalloc::Static::pageheap_->pagemap_.root_->ptrs[%ld-%ld] "
	    "array length %ld\n", low_bound, high_bound,
	    high_bound - low_bound + 1);

	/*
	 * tcmalloc::Static::pageheap_->pagemap_.root_->ptrs[index]
	 */
	for (index = low_bound; index <= high_bound; index++) {
		struct value *ptr, *node;
		struct value *ptrs2;
		LONGEST low_bound2, high_bound2, index2;

		ptr = value_subscript(ptrs, index);
		if (value_as_address(ptr) == 0)
			continue;
		node = value_ind(ptr);
		/*
		 * tcmalloc::Static::pageheap_->pagemap_.root_->ptrs[index]->ptrs
		 */
		fieldno = type_field_name2no(value_type(node), "ptrs");
		ptrs2 = value_field(node, fieldno);
		get_array_bounds (value_type(ptrs2), &low_bound2, &high_bound2);
		CA_PRINT_DBG("tcmalloc::Static::pageheap_->pagemap_.root_->ptrs[%ld]->ptrs[%ld-%ld] "
		    "array length %ld\n", index, low_bound2, high_bound2,
		    high_bound2 - low_bound2 + 1);

		/*
		 * tcmalloc::Static::pageheap_->pagemap_.root_->ptrs[index]->ptrs[index2]
		 */
		for (index2 = low_bound2; index2 <= high_bound2; index2++) {
			struct value *node2;
			struct value *leaf_p, *leaf;

			node2 = value_subscript(ptrs2, index2);
			if (value_as_address(node2) == 0)
				continue;
			leaf_p = value_cast(leaf_type, node2);
			leaf = value_ind(leaf_p);
			if (parse_leaf(leaf, span_type) == false)
				return false;
		}
	}

	return true;
}

bool
parse_central_cache(void)
{
	struct symbol *central_cache_;
	struct value *central_cache;
	LONGEST low_bound, high_bound, index;

	/*
	 * Global var
	 * tcmalloc::CentralFreeListPadded tcmalloc::Static::central_cache_[88]
	 */
	central_cache_ = lookup_symbol_global("tcmalloc::Static::central_cache_",
	    0, VAR_DOMAIN);
	if (central_cache_ == NULL) {
		CA_PRINT("Failed to lookup gv "
		    "\"tcmalloc::Static::central_cache_\"\n");
		return false;
	}
	central_cache = value_of_variable(central_cache_, 0);
	if (TYPE_CODE (value_type(central_cache)) != TYPE_CODE_ARRAY) {
		CA_PRINT("Unexpected \"central_cache_\" is not an array\n");
		return false;
	}
	if (get_array_bounds (value_type(central_cache), &low_bound,
	    &high_bound) == 0) {
		CA_PRINT("Could not determine \"central_cache_\" bounds\n");
		return false;
	}
	if (g_config.kNumClasses == 0)
		g_config.kNumClasses = high_bound - low_bound + 1;
	else if (g_config.kNumClasses != high_bound - low_bound + 1) {
		CA_PRINT("Inconsistent kNumClasses in central_cache\n");
		return false;
	}

	/*
	 * tcmalloc::Static::central_cache_[index]
	 */
	for (index = low_bound; index <= high_bound; index++) {
		struct value *v;
		struct value *cfl;	/* CentralFreeListPadded */
		struct type *cfl_type;

		v = value_subscript(central_cache, index);
		/*
		 * We need to work with tcmalloc::CentralFreeList,
		 * which is base class of tcmalloc::CentralFreeListPaddedTo<16>,
		 * which is base class of tcmalloc::CentralFreeListPadded
		 */
		cfl_type = TYPE_BASECLASS(value_type(v), 0);
		cfl_type = TYPE_BASECLASS(cfl_type, 0);
		cfl = value_cast(cfl_type, v);

		if (parse_central_freelist(cfl) == false)
			return false;
	}

	return true;
}

bool
parse_central_freelist(struct value *cfl)
{
	int fieldno;
	int used_slots, count;
	struct value *tc_slots;
	LONGEST low_bound, high_bound, index;

	/*
	 * tcmalloc::CentralFreeList::used_slots_
	 */
	fieldno = type_field_name2no(value_type(cfl), "used_slots_");
	if (fieldno < 0) {
		CA_PRINT("failed to find member \"used_slots_\"\n");
		return false;
	}
	used_slots = value_as_long(value_field(cfl, fieldno));

	/*
	 * tcmalloc::CentralFreeList::used_slots_
	 */
	fieldno = type_field_name2no(value_type(cfl), "tc_slots_");
	if (fieldno < 0) {
		CA_PRINT("failed to find member \"tc_slots_\"\n");
		return false;
	}
	tc_slots = value_field(cfl, fieldno);
	if (TYPE_CODE (value_type(tc_slots)) != TYPE_CODE_ARRAY) {
		CA_PRINT("Unexpected \"tc_slots\" is not an array\n");
		return false;
	}
	if (get_array_bounds (value_type(tc_slots), &low_bound,
	    &high_bound) == 0) {
		CA_PRINT("Could not determine \"tc_slots\" bounds\n");
		return false;
	}

	/*
	 * tcmalloc::CentralFreeList::used_slots_[index]
	 */
	count = 0;
	for (index = low_bound; index <= high_bound; index++) {
		struct value *tcentry;	/* tcmalloc::CentralFreeList::TCEntry */
		bool empty_slot;

		tcentry = value_subscript(tc_slots, index);
		if (parse_central_freelist_tcentry(tcentry, &empty_slot) ==
		    false) {
			return false;
		}

		if (empty_slot == false)
			count++;
	}
	if (count != used_slots) {
		/* FIXME */
		CA_PRINT("Heap corruption: CentralFreeList records %d slots "
		    "are used while tc_slots_ shows %d\n", used_slots, count);
	}

	return true;
}

bool
parse_central_freelist_tcentry(struct value *tcentry, bool *empty_slot)
{
	int fieldno;
	struct value *head, *tail;
	int count;
	struct type *void_p, *void_pp;

	/*
	 * tcmalloc::CentralFreeList::TCEntry::head
	 */
	fieldno = type_field_name2no(value_type(tcentry), "head");
	if (fieldno < 0) {
		CA_PRINT("failed to find member \"head\"\n");
		return false;
	}
	head = value_field(tcentry, fieldno);
	void_p = value_type(head);
	void_pp = lookup_pointer_type(void_p);

	/*
	 * tcmalloc::CentralFreeList::TCEntry::tail
	 */
	fieldno = type_field_name2no(value_type(tcentry), "tail");
	if (fieldno < 0) {
		CA_PRINT("failed to find member \"tail\"\n");
		return false;
	}
	tail = value_field(tcentry, fieldno);

	count = 0;
	while (value_as_address(head) != 0) {
		struct value *v;

		count++;
		/* FIXME validate the address */
		if (cached_block_add(value_as_address(head)) == false)
			return false;

		/* FIXME count < sizemap_.num_objects_to_move[cl] */
		if (count > 1024) {
			CA_PRINT("tcentry's list is too long > 1024\n");
			return false;
		}

		if (value_as_address(head) == value_as_address(tail))
			break;

		v = value_cast(void_pp, head);
		head = value_ind(v);
	}
	if (count > 0)
		*empty_slot = false;
	else
		*empty_slot = true;

	return true;
}

bool
span_populate_free_bitmap(struct ca_span *span)
{
	size_t blk_sz, n_uint;
	address_t base, end, cursor, next;
	unsigned long i;
	unsigned int index, n, bit;

	if (span->bitmap != NULL ||
	    span->sizeclass == 0 ||
	    span->location != IN_USE) {
		return true;
	}

	/*
	 * Allocate space for the bitmap
	 */
	blk_sz = g_config.sizemap.class_to_size[span->sizeclass];
	span->count = (span->length << g_config.kPageShift) / blk_sz;
	n_uint = (span->count + UINT_BITS - 1) / UINT_BITS;
	span->bitmap = calloc(n_uint, sizeof(unsigned int));
	if (span->bitmap == NULL) {
		CA_PRINT("%s: out out memory\n", __FUNCTION__);
		return false;
	}

	/*
	 * Walk objects list for free blocks
	 */
	base = span->start << g_config.kPageShift;
	end = base + span->count * blk_sz;
	cursor = span->objects;
	while (cursor != 0) {
		/*
		 * Address check
		 */
		if (cursor < base || cursor >= end) {
			/* FIXME */
			CA_PRINT("Heap corruption: objects list node %#lx is "
			    "out of span's range\n", cursor);
			break;
		}
		index = (cursor - base) / blk_sz;
		if (base + index * blk_sz != cursor) {
			/* FIXME */
			CA_PRINT("Heap corruption: invalid free %#lx\n",
			    cursor);
			break;
		}

		/*
		 * Set bitmap
		 */
		n = index / UINT_BITS;
		bit = index - n * UINT_BITS;
		span->bitmap[n] |= 1 << bit;

		/*
		 * Move to the next link node
		 */
		if (read_memory_wrapper(NULL, cursor, &next, sizeof(void*)) ==
		    false) {
			break;
		}
		cursor = next;
	}
	/*
	 * Cached blocks are free blocks as well
	 * g_cached_blocks has been sorted by now
	 */
	for (i = 0; i < g_cached_blocks_count; i++) {
		address_t addr = g_cached_blocks[i];
	
		if (addr < base)
			continue;
		else if (addr >= end)
			break;

		index = (addr - base) / blk_sz;
		n = index / UINT_BITS;
		bit = index - n * UINT_BITS;
		span->bitmap[n] |= 1 << bit;
	}

	return true;
}

bool
span_block_free(struct ca_span *span, address_t addr)
{
	address_t base;
	unsigned int index, n, bit;
	size_t blk_sz;

	if (span->location != IN_USE)
		return true;
	else if (span->sizeclass == 0)
		return false;

	base = span->start << g_config.kPageShift;
	blk_sz = g_config.sizemap.class_to_size[span->sizeclass];
	index = (addr - base) / blk_sz;
	n = index / UINT_BITS;
	bit = index - n * UINT_BITS;

	return span->bitmap[n] & (1 << bit);
}

int
type_field_name2no(struct type *type, const char *field_name)
{
	int n;

	if (type == NULL)
		return -1;

	type = check_typedef (type);

	for (n = 0; n < TYPE_NFIELDS (type); n++) {
		if (strcmp (field_name, TYPE_FIELD_NAME (type, n)) == 0)
			return n;
	}
	return -1;
}

bool
parse_leaf(struct value *leaf, struct type *span_type)
{
	int fieldno;
	struct value *values;
	LONGEST low_bound, high_bound, index;

	/*
	 * leaf->values
	 */
	fieldno = type_field_name2no(value_type(leaf), "values");
	if (fieldno < 0) {
		CA_PRINT("failed to find member \"values\"\n");
		return false;
	}
	values = value_field(leaf, fieldno);
	if (TYPE_CODE (value_type(values)) != TYPE_CODE_ARRAY) {
		CA_PRINT("Unexpected: \"values\" is not an array\n");
		return false;
	}
	if (get_array_bounds (value_type(values), &low_bound, &high_bound) == 0) {
		CA_PRINT("Could not determine \"values\" bounds\n");
		return false;
	}
	CA_PRINT_DBG("TCMalloc_PageMap3<35>::Leaf::values[%ld-%ld] array "
	    "length %ld\n", low_bound, high_bound, high_bound - low_bound + 1);

	/*
	 * leaf->values[index]
	 */
	for (index = low_bound; index <= high_bound; index++) {
		struct value *v, *span_p, *span;

		if (skip_npage > 0) {
			skip_npage--;
			continue;
		}

		v = value_subscript(values, index);
		if (value_as_address(v) == 0)
			continue;
		/*
		 * (tcmalloc::Span*)leaf->values[index]
		 */
		span_p = value_cast(span_type, v);
		span = value_ind(span_p);
		if (parse_span(span) == false)
			return false;
	}
	return true;
}

bool
parse_span(struct value *span)
{
	int fieldno;
	struct ca_span *my_span;
	struct value *m;
	struct type *type = value_type(span);
	struct ca_segment *segment;

	if (g_spans_count >= g_spans_capacity) {
		unsigned long goal;

		if (g_spans_capacity == 0)
			goal = 1024;
		else
			goal = g_spans_capacity * 2;
		g_spans = realloc(g_spans, goal * sizeof(struct ca_span));
		if (g_spans == NULL)
			return false;
		g_spans_capacity = goal;
	}
	my_span = &g_spans[g_spans_count++];

	fieldno = type_field_name2no(type, "start");
	m = value_field(span, fieldno);
	my_span->start = value_as_long(m);

	fieldno = type_field_name2no(type, "length");
	m = value_field(span, fieldno);
	my_span->length = value_as_long(m);

	fieldno = type_field_name2no(type, "next");
	m = value_field(span, fieldno);
	my_span->next = value_as_address(m);

	fieldno = type_field_name2no(type, "prev");
	m = value_field(span, fieldno);
	my_span->prev = value_as_address(m);

	fieldno = type_field_name2no(type, "objects");
	m = value_field(span, fieldno);
	my_span->objects = value_as_address(m);

	fieldno = type_field_name2no(type, "refcount");
	m = value_field(span, fieldno);
	my_span->refcount = value_as_long(m);

	fieldno = type_field_name2no(type, "sizeclass");
	m = value_field(span, fieldno);
	my_span->sizeclass = value_as_long(m);

	fieldno = type_field_name2no(type, "location");
	m = value_field(span, fieldno);
	my_span->location = value_as_long(m);

	fieldno = type_field_name2no(type, "sample");
	m = value_field(span, fieldno);
	my_span->sample = value_as_long(m);

	skip_npage = my_span->length - 1;

	segment = get_segment(my_span->start << g_config.kPageShift,
	    my_span->length << g_config.kPageShift);
	if (segment != NULL)
		segment->m_type = ENUM_HEAP;

	return true;
}

bool
parse_thread_cache(void)
{
	struct symbol *thread_heaps_;
	struct value *thread_heaps_p, *thread_heaps;

	/*
	 * Global var
	 * tcmalloc::ThreadCache *tcmalloc::ThreadCache::thread_heaps_
	 */
	thread_heaps_ = lookup_symbol_global("tcmalloc::ThreadCache::thread_heaps_",
	    0, VAR_DOMAIN);
	if (thread_heaps_ == NULL) {
		CA_PRINT("Failed to lookup gv "
		    "\"tcmalloc::ThreadCache::thread_heaps_\"\n");
		return false;
	}
	thread_heaps_p = value_of_variable(thread_heaps_, 0);
	/*
	 * thread_heaps_ is a link list of ThreadCache objects
	 */
	while (value_as_address(thread_heaps_p) != 0) {
		struct value *lists;
		int fieldno;
		LONGEST low_bound, high_bound;

		thread_heaps = value_ind(thread_heaps_p);
		fieldno = type_field_name2no(value_type(thread_heaps), "list_");
		lists = value_field(thread_heaps, fieldno);
		if (TYPE_CODE (value_type(lists)) != TYPE_CODE_ARRAY) {
			CA_PRINT("Unexpected \"list_\" is not an array\n");
			return false;
		}
		if (get_array_bounds (value_type(lists), &low_bound,
		    &high_bound) == 0) {
			CA_PRINT("Could not determine \"list_\" bounds\n");
			return false;
		}
		CA_PRINT_DBG("thread_heaps_->list_[%ld-%ld] array length %ld\n",
		    low_bound, high_bound, high_bound - low_bound + 1);

		if (g_config.kNumClasses == 0)
			g_config.kNumClasses = high_bound - low_bound + 1;
		else if (g_config.kNumClasses != high_bound - low_bound + 1) {
			CA_PRINT("Inconsistent kNumClasses\n");
			return false;
		}

		if (parse_thread_cache_lists(lists) == false)
			return false;

		/* next ThreadCache on link list */
		fieldno = type_field_name2no(value_type(thread_heaps), "next_");
		thread_heaps_p = value_field(thread_heaps, fieldno);
	}

	return true;
}

bool
parse_thread_cache_lists(struct value *lists)
{
	unsigned int index;

	for (index = 0; index < g_config.kNumClasses; index++) {
		struct value *freelist, *list;
		int fieldno;
		unsigned int len, count;
		struct type *void_p, *void_pp;

		freelist = value_subscript(lists, index);

		fieldno = type_field_name2no(value_type(freelist), "length_");
		len = value_as_address(value_field(freelist, fieldno));

		fieldno = type_field_name2no(value_type(freelist), "list_");
		list = value_field(freelist, fieldno);
		void_p = value_type(list);
		void_pp = lookup_pointer_type(void_p);
		count = 0;
		while (value_as_address(list) != 0) {
			struct value *v;

			count++;
			/* FIXME validate the address */
			if (cached_block_add(value_as_address(list)) == false)
				return false;
			CA_PRINT_DBG("->%#lx", value_as_address(list));

			if (count > len)
				break;

			v = value_cast(void_pp, list);
			list = value_ind(v);
		}
		if (count > 0) {
			CA_PRINT_DBG("\n");
		}
		if (len != count) {
			CA_PRINT("Heap corruption: ThreadCache::FreeList::length_ %d "
			    "while ThreadCache::FreeList::list_ %d\n", len, count);
		}
	}

	return true;
}

bool
cached_block_add(address_t addr)
{

	if (g_cached_blocks_count >= g_cached_blocks_capacity) {
		unsigned long goal;

		if (g_cached_blocks_capacity == 0)
			goal = 1024;
		else
			goal = g_cached_blocks_capacity * 2;
		g_cached_blocks = realloc(g_cached_blocks, goal * sizeof(address_t));
		if (g_cached_blocks == NULL)
			return false;
		g_cached_blocks_capacity = goal;
	}
	g_cached_blocks[g_cached_blocks_count++] = addr;
	return true;
}

int
cached_block_compare(const void *l, const void *r)
{
	const address_t la = *(const address_t *)l;
	const address_t ra = *(const address_t *)r;

	return (la > ra) - (ra > la);
}

int
cached_block_search_compare(const void *k, const void *m)
{
	const address_t a = *(const address_t *)k;
	const address_t c = *(const address_t *)m;

	return (a > c) - (c > a);
}

int
span_search_compare(const void *k, const void *m)
{
	const unsigned long *pageid = k;
	const struct ca_span *span = m;

	return (*pageid >= span->start) - (*pageid < span->start +
	    span->length);
}

bool
is_block_cached(address_t addr)
{
	address_t *a;

	a = bsearch(&addr, g_cached_blocks, g_cached_blocks_count,
	    sizeof(address_t), cached_block_search_compare);
	return a != NULL;
}

bool
verify_sorted_cached_blocks(void)
{
	unsigned long i;

	if (g_cached_blocks_count < 2)
		return true;

	for (i = 0; i < g_cached_blocks_count - 1; i++) {
		if (g_cached_blocks[i] > g_cached_blocks[i + 1]) {
			CA_PRINT("cached blocks are not sorted properly at "
			    "%ld\n", i);
			return false;
		} else if (g_cached_blocks[i] == g_cached_blocks[i + 1]) {
			CA_PRINT("found duplicate cached blocks at %ld\n", i);
		}
	}

	for (i = 0; i < g_cached_blocks_count; i++) {
		address_t addr = g_cached_blocks[i];

		if (is_block_cached(addr) == false) {
			CA_PRINT("failed to query cached block %#lx at %ld\n",
			    addr, i);
			return false;
		} else if (is_block_cached(addr + 1) == true) {
			CA_PRINT("false positive to query cached block %#lx",
			    addr + 1);
			return false;
		}
	}

	return true;
}

bool
verify_sorted_spans(void)
{
	unsigned long i, l;

	if (g_spans_count < 2)
		return true;

	for (i = 0; i < g_spans_count - 1; i++) {
		if (g_spans[i].start + g_spans[i].length >
		    g_spans[i + 1].start) {
			CA_PRINT("Spans are not sorted properly at "
			    "%ld\n", i);
			return false;
		}
	}

	for (i = 0; i < g_spans_count; i++) {
		for (l = 0; l < g_spans[i].length; l++) {
			address_t addr = ((g_spans[i].start + l) <<
			    g_config.kPageShift) + 1;

			if (span_get(addr) == false) {
				CA_PRINT("failed to query span with address "
				    "%#lx\n",addr);
				return false;
			}
		}
	}

	return true;
}
