/*
  Written by Jackson Murphy for CS4400 - Computer Systems.
  Last modified on April 10, 2017.

  This is a dynamic storage allocator for C programs.
  It provides 2 functions that are intended to replace the malloc()
  and free() functions of the C standard library (mm_malloc and mm_free).

  The features of this allocator include an explicit free list,
  coalescing of free blocks, and unmapping of free chunks of pages.

  Notes on terminology:
  The variable names bp and fp are often used.
  bp means "block pointer", and fp means "free block pointer".

  A "chunk" is a page or group of pages returned by the operating system on a single call
  to mem_map()
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

typedef struct {
  size_t size; // the number of bytes in a block
  char allocated; // 1 if the block is allocated, 0 if it is free
} block_header;

typedef struct {
  size_t size; // the number of bytes in a block
  int filler;
} block_footer;

/* This program uses 2 separate linked lists: 1) free blocks  2) chunks */
typedef struct list_node {
  struct list_node* next;
  struct list_node* prev;
} list_node;

typedef struct {
  size_t size; // the number of bytes in a chunk. Includes all overhead
  int filler;
} chunk_info;

// These vars are defined and initialized in reset_vars()
static void* first_bp;
static list_node* first_fp;
static void* bp;
static list_node* last_chunk_ptr;
static size_t PAGE_SIZE;
static size_t pages_in_use;
static size_t chunks_in_use;
static size_t INITIAL_PAGES ;
static size_t MAX_PAGES_IN_CHUNK;
// Only unmap a chunk when there are at least this many pages in use
static size_t CHUNK_UNMAP_THRESHOLD;

/* always use 16-byte alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

/* rounds up to the nearest multiple of mem_pagesize() */
#define PAGE_ALIGN(size) (((size) + (mem_pagesize()-1)) & ~(mem_pagesize()-1))

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define BLOCK_OVERHEAD (sizeof(block_header) + sizeof(block_footer))
#define CHUNK_OVERHEAD (sizeof(list_node) + sizeof(block_footer) + (2 * sizeof(block_header)) + sizeof(chunk_info))
#define HDRP(bp) ((char*) (bp) - sizeof(block_header))
#define FTRP(bp) ((char*) (bp) + GET_SIZE(HDRP(bp)) - BLOCK_OVERHEAD)

#define GET_SIZE(p) ((block_header*)(p))->size
#define GET_ALLOC(p) ((block_header*)(p))->allocated

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE((char*)(bp) - BLOCK_OVERHEAD))

static void* coalesce(void* bp);
static void set_allocated(void* bp, size_t size);
static void* set_new_chunk(size_t size);
static void add_chunklist_ptr(list_node* chunk_ptr);
static void* init_free_block(list_node* first_chunk, size_t size);
static void set_chunk_info(list_node* chunk_ptr, size_t size);
static void set_start_terminator(list_node* chunk_ptr);
static void set_end_terminator(list_node* chunk_ptr, size_t chunk_size);
static void possibly_unmap_chunk(void* fp);
static void reset_vars();
static void replace_list_node(list_node* new_node, list_node* old_node);
static void remove_list_node(list_node* node);
static void add_to_free_list(list_node* bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  // reset allocator to initial state
  reset_vars();

  PAGE_SIZE = mem_pagesize();
  set_new_chunk(PAGE_SIZE * INITIAL_PAGES);

  return 0;
}

/*
 mm_malloc - Allocate a block by finding the first free block with sufficient space.
 If no such free block can be found, requests additional page(s) from the OS
 via mem_map() and allocates a block from that. Returns a pointer to the
 beginning of the block's payload.
 */
void *mm_malloc(size_t size)
{
  size_t need_size = MAX(size, sizeof(list_node));
  size_t new_size = ALIGN(need_size + BLOCK_OVERHEAD);
  list_node* fp = first_fp;
  list_node* sufficiently_large_fp = NULL; // For first-fit allocating

  if(first_fp){
    while(1){
      if(GET_SIZE(HDRP((void*)fp)) >= new_size){
          sufficiently_large_fp = fp;
          break;
      }
      if(fp->next == NULL)
        break;
      fp = fp->next;
    }
  }

  if(sufficiently_large_fp){
    set_allocated((void*)sufficiently_large_fp, new_size);
    return (void*)sufficiently_large_fp;
  }

  // no free block big enough, or no free block at all
  void* bp = set_new_chunk(new_size);
  set_allocated(bp, new_size);

  return bp;
}

/*
 * Frees a previously allocated block. The pointer given as input must have been
  previously returned with a call to mm_malloc, or else this function is undefined
 */
void mm_free(void* bp)
{
  GET_ALLOC(HDRP(bp)) = 0;
  void* fp = coalesce(bp);

  // If the freed block was the only one in the chunk, unmap the chunk.
  // But not if it's the only chunk we've allocated so far.
  if(pages_in_use > CHUNK_UNMAP_THRESHOLD)
    possibly_unmap_chunk(fp);
}

/* Merges adjacent free blocks together. Updates the explicit free
  list if necessary */
  static void* coalesce(void* bp){
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    size_t new_size = size;

    if(prev_alloc && next_alloc){ // Case 1
      add_to_free_list((list_node*)bp);
    }

    else if(prev_alloc && !next_alloc){ // Case 2
      replace_list_node((list_node*)bp, (list_node*)NEXT_BLKP(bp));
      new_size = size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
      GET_SIZE(HDRP(bp)) = new_size;
      GET_SIZE(FTRP(bp)) = new_size;
    }

    else if(!prev_alloc && next_alloc){ // Case 3
      new_size = size + GET_SIZE(HDRP(PREV_BLKP(bp)));
      GET_SIZE(FTRP(bp)) = new_size;
      GET_SIZE(HDRP(PREV_BLKP(bp))) = new_size;
      bp = PREV_BLKP(bp);
    }

    else{ // Case 4
      remove_list_node((list_node*)NEXT_BLKP(bp));
      new_size = size + (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))));
      GET_SIZE(FTRP(NEXT_BLKP(bp))) = new_size;
      GET_SIZE(HDRP(PREV_BLKP(bp))) = new_size;
      bp = PREV_BLKP(bp);
    }

    return bp;
  }

/* Given a pointer to the beginning of a block's payload, sets the header's
  "allocated" bit to 1. Also splits the block into 2 smaller blocks if
  the requested size is small enough such that another usable block could be made
  from a split.  */
static void set_allocated(void* bp, size_t size){
  size_t extra_size = GET_SIZE(HDRP(bp)) - size;
  if(extra_size > ALIGN(sizeof(list_node) + BLOCK_OVERHEAD)){
    GET_SIZE(HDRP(bp)) = size;
    GET_SIZE(FTRP(bp)) = size;
    GET_SIZE(HDRP(NEXT_BLKP(bp))) = extra_size;
    GET_SIZE(FTRP(NEXT_BLKP(bp))) = extra_size;
    GET_ALLOC(HDRP(NEXT_BLKP(bp))) = 0;
    GET_ALLOC(HDRP((bp))) = 1;

    // Adjust free list pointers
    replace_list_node((list_node*)NEXT_BLKP(bp), (list_node*)bp);

  }
  else{
    GET_ALLOC(HDRP(bp)) = 1;
    remove_list_node((void*)bp);
  }
}

/* Gets more pages from the kernel. Tries to minimize the number of
  future calls to this method by possibly asking the kernel for twice the number
  of pages than are currently in use. Returns a pointer to the first free block
  of the chunk */
static void* set_new_chunk(size_t size){
  // Decide how many pages to call for
  size_t pages_requested = PAGE_ALIGN(size) / PAGE_SIZE;
  size_t new_pages_requested = MAX(pages_requested, pages_in_use);
  if(new_pages_requested > MAX_PAGES_IN_CHUNK)
    new_pages_requested = MAX_PAGES_IN_CHUNK;
  pages_in_use += new_pages_requested;
  size_t new_size = new_pages_requested * PAGE_SIZE;

  list_node* chunk_ptr = mem_map(new_size);

  add_chunklist_ptr(chunk_ptr);
  set_chunk_info(chunk_ptr, new_size);
  set_start_terminator(chunk_ptr);
  set_end_terminator(chunk_ptr, new_size);

  size_t free_block_size = new_size - CHUNK_OVERHEAD;
  void* bp = init_free_block(chunk_ptr, free_block_size);

  chunks_in_use++;
  return bp;
}

/* Adds a chunk pointer to the doubly linked list of chunk pointers*/
static void add_chunklist_ptr(list_node* chunk_ptr){
  if(last_chunk_ptr){
    last_chunk_ptr->next = chunk_ptr;
    chunk_ptr->prev = last_chunk_ptr;
    last_chunk_ptr = chunk_ptr;
    assert(chunk_ptr->prev != chunk_ptr);
    chunk_ptr->next = NULL;
  }
  else{
    chunk_ptr->next = chunk_ptr->prev = NULL;
    last_chunk_ptr = chunk_ptr;
  }
}


/* Sets the header and footer of the first free block of a newly allocated chunk,
  and adds it to the free list*/
static void* init_free_block(list_node* first_chunk, size_t size){
  void* bp = (void*)first_chunk + CHUNK_OVERHEAD;

  GET_SIZE(HDRP(bp)) = size;
  GET_ALLOC(HDRP(bp)) = 0;
  GET_SIZE(FTRP(bp)) = size;
  GET_ALLOC(FTRP(bp)) = 0;

  // Add free block to the explicit free list
 add_to_free_list((list_node*)bp);

  return bp;
}

/* We need to store the size of the chunk for later unmapping. */
static void set_chunk_info(list_node* chunk_ptr, size_t size){
  chunk_info* info_ptr = (void*)chunk_ptr + ALIGN(sizeof(list_node));
  info_ptr->size = size;
}

/* The start terminator is a sentinel node at the beginning of a chunk.
  It has no payload. */
static void set_start_terminator(list_node* chunk_ptr){
  void* terminator_ptr = (void*)chunk_ptr + ALIGN(sizeof(list_node) + sizeof(chunk_info) + sizeof(block_header));
  GET_SIZE(HDRP(terminator_ptr)) = ALIGN(sizeof(block_header) + sizeof(block_footer));
  GET_ALLOC(HDRP(terminator_ptr)) = 1;
  GET_SIZE(FTRP(terminator_ptr)) = ALIGN(sizeof(block_header) + sizeof(block_footer));
  GET_ALLOC(FTRP(terminator_ptr)) = 1;
}

static void set_end_terminator(list_node* chunk_ptr, size_t chunk_size){
  void* terminator_ptr = (void*)chunk_ptr + chunk_size;
  GET_SIZE(HDRP(terminator_ptr)) = 0;
  GET_ALLOC(HDRP(terminator_ptr)) = 1;
}

/* If the free block passed into this function is the only block in the
  chunk, unmap the chunk*/
static void possibly_unmap_chunk(void* fp){
  size_t free_block_size = GET_SIZE(HDRP(fp));

  // Check if the block is the first one in the chunk
  if(GET_SIZE(HDRP(PREV_BLKP(fp))) == (sizeof(block_header) + sizeof(block_footer))){
    chunk_info* info = (chunk_info*)(PREV_BLKP(fp) - sizeof(block_header) - sizeof(chunk_info));
    size_t chunk_size = info->size;

    // Check if the block is the only 1 in the chunk
    if(free_block_size == (chunk_size - CHUNK_OVERHEAD)){

      // Unmap the chunk
      remove_list_node(fp);
      void* chunk_ptr = (void*)info - sizeof(list_node);
      remove_list_node(chunk_ptr);
      mem_unmap(chunk_ptr, chunk_size);
      chunks_in_use--;
      pages_in_use -= (chunk_size / PAGE_SIZE);
    }
  }
}

/* Resets the allocator's static variables*/
static void reset_vars(){
   first_bp = NULL;
   first_fp = NULL;
   bp = NULL;
   last_chunk_ptr = NULL;
   PAGE_SIZE = 0;
   pages_in_use = 0;
   chunks_in_use = 0;
   CHUNK_UNMAP_THRESHOLD = 15;
   INITIAL_PAGES = 1;
   MAX_PAGES_IN_CHUNK = 32;
}

/* Replaces 1 doubly-linked list node with another */
static void replace_list_node(list_node* new_node, list_node* old_node){
  new_node->next = old_node->next;
  new_node->prev = old_node->prev;

  if(old_node->prev)
    old_node->prev->next = new_node;
  if(old_node->next)
    old_node->next->prev = new_node;

  if(old_node == first_fp)
    first_fp = new_node;
}

/* Removes a node from a doubly-linked list*/
static void remove_list_node(list_node* node){
  if(node == first_fp){
    if(node->next){
      node->next->prev = NULL;
      first_fp = node->next;
    }
    else
      first_fp = NULL;
  }

  else if(node == last_chunk_ptr){
    if(node->prev){
      node->prev->next = NULL;
      last_chunk_ptr = node->prev;
    }
    else
      last_chunk_ptr = NULL;
  }

  else{
    if(node->prev && node->next){
      node->prev->next = node->next;
      node->next->prev = node->prev;
    }
    else if(node->next)
      node->next->prev = NULL;
    else if(node->prev)
      node->prev->next = NULL;
  }
}

/* Adds a free block to the beginning of the free list*/
static void add_to_free_list(list_node* fp){
  if(first_fp){
    first_fp->prev = fp;
    fp->next = first_fp;
  }
  else{
    fp->next = NULL;
  }
  fp->prev = NULL;
  first_fp = fp;
}
