/*
  Written by Jackson Murphy and the teaching staff of cs 4400.

  This is a dynamic storage allocator for C programs.
  It provides 2 functions that are intended to replace the malloc()
  and free() functions of the C standard library.

 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

typedef struct {
  size_t size;
  char allocated;
} block_header;

typedef struct {
  size_t size;
  int filler;
} block_footer;

typedef struct list_node {
  struct list_node* next;
  struct list_node* prev;
} list_node;

static void* first_bp = NULL;
static list_node* first_free_bp = NULL;
static void* bp = NULL;
static void* current_avail = NULL;
static int current_avail_size = 0;


/* always use 16-byte alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

/* rounds up to the nearest multiple of mem_pagesize() */
#define PAGE_ALIGN(size) (((size) + (mem_pagesize()-1)) & ~(mem_pagesize()-1))

#define OVERHEAD (sizeof(block_header) + sizeof(block_footer))
#define HDRP(bp) ((char*) (bp) - sizeof(block_header))
#define FTRP(bp) ((char*) (bp) + GET_SIZE(HDRP(bp)) - OVERHEAD)

#define GET_SIZE(p) ((block_header*)(p))->size
#define GET_ALLOC(p) ((block_header*)(p))->allocated

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE((char*)(bp) - OVERHEAD))

static void check_heap_correctness(char* first_bp);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  current_avail = NULL;
  current_avail_size = 0;

  return 0;
}

/*
 * mm_malloc - Allocate a block by using bytes from current_avail,
 *     grabbing a new page if necessary.
 */
void *mm_malloc(size_t size)
{
  int newsize = ALIGN(size);
  void *p;

  if (current_avail_size < newsize) {
    current_avail_size = PAGE_ALIGN(newsize);
    current_avail = mem_map(current_avail_size);
    if (current_avail == NULL)
      return NULL;
  }

  p = current_avail;
  current_avail += newsize;
  current_avail_size -= newsize;

  //check_heap_correctness(first_bp);
  return p;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
  //check_heap_correctness(first_bp);
}

/* Internal test to ensure correct allocation */
static void check_heap_correctness(char* first_bp){
  if(GET_SIZE(HDRP(first_bp)) == 0)
    exit(-1);

  // Ensure there are no contiguous free blocks
  void* bp = first_bp;
  while(GET_SIZE(HDRP(bp)) != 0){
    char curr_alloc = GET_ALLOC(HDRP(bp));
    if(curr_alloc == 0 && GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0)
      exit(-2);
    bp = NEXT_BLKP(bp);
  }

  // Ensure all free blocks are also in free list
  bp = first_bp;
  size_t implicit_free_count = 0;
  size_t explicit_free_count = 0;
  while(GET_SIZE(HDRP(NEXT_BLKP(bp))) != 0){
    if(GET_ALLOC(HDRP(bp)) == 0)
      implicit_free_count++;
    bp = NEXT_BLKP(bp);
  }
  if(GET_ALLOC(HDRP(bp)) == 0)
    implicit_free_count++;

  list_node* fp  = first_free_bp;
  if(fp != NULL){
    explicit_free_count++;
    while(fp->next != NULL){
      explicit_free_count++;
      fp = fp->next;
    }
  }

  if(explicit_free_count != implicit_free_count)
    exit(-3);

  // Ensure every block in free list is free, and is valid with size greater than 0
   fp = first_free_bp;
  while(fp != NULL){
    if(GET_ALLOC(HDRP(fp)) != 0 || GET_SIZE(HDRP(fp)) <= 0)
      exit(-4);
    fp = fp->next;
  }

  // Ensure no allocated blocks overlap
  bp = first_bp;
  while(1){
    if(bp + GET_SIZE(bp) != NEXT_BLKP(bp))
      exit(-5);
    if(GET_SIZE(NEXT_BLKP(bp)) == 0)
      break;
  }
}
