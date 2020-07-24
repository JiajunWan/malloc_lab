/*
 ******************************************************************************
 *                                   mm.c                                     *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *  Jiajun Wan                                                                *
 *  jiajunw2                                                                  *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 * Structure Design:                                                          *
 * Segregated free list: 16, 32, 64, 96, 128, 56,                             *
 * 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, Inf                      *
 * List is sorted as LIFO sequence                                            *
 * Header:                                                                    *
 * |Size | mini block bit | prev mini block bit | prev alloc bit | alloc bit| *
 * Mini block:                                                                *
 * Alloc: |Header | Payload| (16 bytes)                                       *
 * Free: |Next pointer : lower 4 bits | Prev pointer : lower 4 bits|          *
 * Normal block:                                                              *
 * Alloc: |Header | Payload| (Varable size) (footerless in alloced blocks)    *
 * Free: |Header | Next pointer | Prev pointer | Footer|                      *
 *                                                                            *
 ******************************************************************************
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined (such as when running mdriver-dbg), these macros
 * are enabled. You can use them to print debugging output and to check
 * contracts only in debug mode.
 *
 * Only debugging macros with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/* Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/* Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/* Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/* Expand heap by at least chunksize (4096) each time no free space (Must be
 * divisible by dsize) */
static const size_t chunksize = (1L << 12);

/* Heap init size */
static const size_t initsize = (1L << 6);

/* Mask to get the alloc bit */
static const word_t alloc_mask = 0x1;

/* Mask to get the size */
static const word_t size_mask = ~(word_t)0xF;

/* Lower four bits mask 1111 */
static const word_t lower_bits_mask = (word_t)0xF;
/* Prev alloc mask 0010 */
static const word_t alloc_prev_mask = (word_t)0x2;
/* Prev mini size mask 0100 */
static const word_t prev_mini_mask = (word_t)0x4;
/* Prev alloc mini size mask 0110 */
static const word_t alloc_prev_mini_mask = (word_t)0x6;
/* Current block mini mask 1000 */
static const word_t alloc_mini_mask = (word_t)0x8;
/* Current block is mini block, prev alloc mask 1010 */
static const word_t alloc_mini_alloc_prev = (word_t)0xA;
/* Address mask 1111111....0000 */
static const word_t addr_mask = ~(word_t)0x7;

/* Seg list buckets count */
static const size_t seg_count = 15;

/* Seg list size const array */
static const size_t seg_size[seg_count] = {
    16,   32,   64,   96,    128,   256,   512,      1024,
    2048, 4096, 8192, 16384, 32768, 65536, INT64_MAX};

/* Represents the header and payload of one block in the heap */
typedef struct block {
  /* Header contains size + allocation flag */
  word_t header;
  char payload[0];
} block_t;

/* Free alias struct for payload area usage */
struct free {
  block_t *next;
  block_t *prev;
  char payload[0];
};

/* Global variables */

/* Explicit free list root pointer, lowest address, insert starting point */
block_t *seg_list_root[seg_count];

/* Pointer to first block */
static block_t *heap_start = NULL;

/* Function prototypes for internal helper routines */

/* My own helpers */

/* Remove free list block */
void remove_block(block_t *block, block_t **root, bool is_mini);
/* Insert before one block */
void insert_block_before(block_t *block, block_t **block_next, bool is_root,
                         bool is_mini);
/* Block size to correct seg bucket list */
block_t **size_to_root(size_t size);
/* Write header */
static void write_header(block_t *block, size_t size, bool alloc,
                         word_t alloc_prev);
/* Write footer */
static void write_footer(block_t *block, size_t size, bool alloc,
                         word_t alloc_prev);
/* Pack Header/Footer */
static word_t pack(size_t size, bool alloc, word_t alloc_prev);
/* Get prev alloc */
static bool get_prev_alloc(block_t *block);
/* Print the whole heap helper */
void print_heap();

bool mm_checkheap(int lineno);

static block_t *extend_heap(size_t size);
static block_t *find_fit(size_t asize);
static block_t *coalesce_block(block_t *block, bool is_mini);
static void split_block(block_t *block, size_t asize);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static word_t *header_to_footer(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/*
 * Initialize the prologue, epilogue, and global variables for the heap
 * Return if init succeeded
 * Pre: Empty heap
 * Post: heap of initsize
 */
bool mm_init(void) {
  /* Create the initial empty heap */
  word_t *start = (word_t *)(mem_sbrk(2 * wsize));

  if (start == (void *)-1) {
    return false;
  }
  /* Heap prologue and epilogue preventing heap boundary coalescing */
  start[0] = pack(0, true, alloc_prev_mask); // Heap prologue (block footer)
  start[1] = pack(0, true, alloc_prev_mask); // Heap epilogue (block header)

  /* Heap starts with first "block header", currently the epilogue */
  heap_start = (block_t *)&(start[1]);
  /* Init seg list */
  for (size_t i = 0; i < seg_count; i++) {
    seg_list_root[i] = NULL;
  }

  /* Extend the empty heap with a free block of chunksize bytes */
  if (extend_heap(initsize) == NULL) {
    return false;
  }
  return true;
}

/*
 * Dynamic memory allocation
 * Allocation size as argument
 * Return pointer to allocated payload area,
 * or return NULL on FAIL
 * Argv: allocation size
 * Pre: size is non-negative
 * Post: Heap is allocated with the request
 */
void *malloc(size_t size) {
  dbg_requires(mm_checkheap(__LINE__));

  size_t asize;      // Adjusted block size
  size_t extendsize; // Amount to extend heap if no fit is found
  /* Block to allocate */
  block_t *block;
  void *bp = NULL;

  /* Initialize heap if it isn't initialized */
  if (heap_start == NULL) {
    mm_init();
  }

  /* Ignore spurious request */
  if (size == 0) {
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
  }

  /* Adjust block size to include overhead and to meet alignment requirements */
  asize = round_up(size + wsize, dsize);
  /* Search the free list for a fit */
  block = find_fit(asize);

  /* If no fit is found, request more memory, and then and place the block */
  if (block == NULL) {
    /* Always request at least chunksize */
    extendsize = max(asize, chunksize);
    block = extend_heap(extendsize);
    /* Extend_heap returns an error */
    if (block == NULL) {
      return bp;
    }
  }
  /* Check if find fit block is a mini block */
  bool block_mini = block->header & alloc_mini_mask;
  /* he block should be marked as free */
  dbg_assert(!get_alloc(block));

  /* Mark block as allocated */
  /* If mini block */
  if (block_mini) {
    /* First remove the mini block from seg list */
    remove_block(block, size_to_root(asize), block_mini);
    /* Get the prev mini and alloc bits */
    word_t alloc_prev = block->header & alloc_prev_mini_mask;
    /* Write the block header as alloc mini block and keep the middle prev two
     * bits */
    write_header(block, dsize, true, alloc_prev | alloc_mini_mask);
    block_t *block_next = (block_t *)(block + 2);
    /* Write alloc mini prev bits of next block */
    block_next->header = block_next->header | alloc_prev_mini_mask;
  } else {
    size_t block_size = get_size(block);
    /* Get the prev mini and alloc bits */
    word_t alloc_prev = block->header & alloc_prev_mini_mask;
    /* Write the block header as alloc block and keep the middle prev two bits
     */
    write_header(block, block_size, true, alloc_prev);
    /* Write alloc prev of next block */
    block_t *block_next = find_next(block);
    block_next->header = block_next->header | alloc_prev_mask;
    /* Try to split the block if too large */
    split_block(block, asize);
  }

  bp = header_to_payload(block);

  dbg_ensures(mm_checkheap(__LINE__));
  return bp;
}

/*
 * Give back the allocated space to the free space
 * Argv: payload pointer bp to the starting address of payload
 * Does not return
 * Pre: bp payload pointer is pointing to a allocated space
 * Post: The allocated space is freed
 */
void free(void *bp) {
  dbg_requires(mm_checkheap(__LINE__));

  if (bp == NULL) {
    return;
  }

  block_t *block = payload_to_header(bp);
  size_t size;
  bool mini = (bool)(block->header & alloc_mini_mask);
  if (mini) {
    size = dsize;
  } else {
    size = get_size(block);
  }

  /* The block should be marked as allocated */
  dbg_assert(get_alloc(block));

  word_t alloc_prev = block->header & alloc_prev_mini_mask;

  /* Mark the block as free */
  if (mini) {
    write_header(block, size, false, alloc_prev | alloc_mini_mask);
    write_footer(block, size, false, alloc_prev | alloc_mini_mask);
  } else {
    write_header(block, size, false, alloc_prev);
    write_footer(block, size, false, alloc_prev);
  }

  /* Try to coalesce the block with its neighbors */
  block = coalesce_block(block, mini);

  dbg_ensures(mm_checkheap(__LINE__));
}

/*
 * Redo the dynamic memory allocation
 * copy the old data to new space
 * return NULL on FAIL or size of zero
 * Argv: ptr to old payload starting address and realloc size
 * Pre: ptr is legal pointer to payload starting address
 * Post: The old payload of size size is in a new allocated space
 */
void *realloc(void *ptr, size_t size) {
  block_t *block = payload_to_header(ptr);
  size_t copysize;
  void *newptr;

  /* If size == 0, then free block and return NULL */
  if (size == 0) {
    free(ptr);
    return NULL;
  }

  /* If ptr is NULL, then equivalent to malloc */
  if (ptr == NULL) {
    return malloc(size);
  }

  /* Otherwise, proceed with reallocation */
  bool block_mini = (bool)(block->header & alloc_mini_mask);
  if (block_mini) {
    copysize = wsize;
  } else {
    copysize = get_payload_size(block); /* gets size of old payload */
  }

  newptr = malloc(size);
  /* If malloc fails, the original block is left untouched */
  if (newptr == NULL) {
    return NULL;
  }
  /* Copy the old data */
  if (size < copysize) {
    copysize = size;
  }
  memcpy(newptr, ptr, copysize);

  /* Free the old block */
  free(ptr);

  return newptr;
}

/*
 * Allocate elements elements of size bytes each
 * all initialized to 0 or return NULL on FAIL
 * Argv: Number of elements and size
 * Pre: Elements and size are non-negative
 * Post: Heap is allocated and zeroed with the request
 */
void *calloc(size_t elements, size_t size) {
  void *bp;
  size_t asize = elements * size;

  if (asize / elements != size) {
    /* Multiplication overflowed */
    return NULL;
  }

  bp = malloc(asize);
  if (bp == NULL) {
    return NULL;
  }

  /* Initialize all bits to 0 */
  memset(bp, 0, asize);

  return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * Extend the heap from the end
 * Get more free space
 * Argv: Size of heap to extend
 * Return the block pointer to the new free space,
 * coalesced if free block before extended area
 * Pre: No free block at least size bytes
 * Post: Free block at least size bytes is at the
 * end of the heap
 */
static block_t *extend_heap(size_t size) {
  void *bp;

  /* Allocate an even number of words to maintain alignment */
  size = round_up(size, dsize);
  if ((bp = mem_sbrk(size)) == (void *)-1) {
    return NULL;
  }

  /* Initialize free block header/footer */
  /* The bp returned by mem_sbrk as the payload pointer. Payload to header will
   * lead to the previous epilogue. Overwrite this epilogue as the new header.
   */
  block_t *block = payload_to_header(bp);
  /* Write the block as free block and keep the prev mini alloc bits */
  word_t alloc_prev = block->header & alloc_prev_mini_mask;
  write_header(block, size, false, alloc_prev);
  write_footer(block, size, false, alloc_prev);

  /* Create new epilogue header */
  block_t *block_epilogue = find_next(block);
  /* Alloc prev is zero, new extended free block, just normal write header */
  write_header(block_epilogue, 0, true, 0x0L);

  /* Coalesce in case the previous block was free */
  block = coalesce_block(block, false);

  return block;
}

/*
 * Coalesce adjacent free blocks
 * Argv: Block pointer and if it is mini block
 * Return the block pointer to the coalesced block
 * Pre: Block is free block
 * Post: Coalesced block is free block and no mini block
 * if coalescing happened
 */
static block_t *coalesce_block(block_t *block, bool is_mini) {
  dbg_requires(!get_alloc(block));

  size_t size;

  /* Consecutive next block, not free list next block */
  block_t *block_next;
  if (is_mini) {
    block_next = (block_t *)(block + 2);
    size = dsize;
  } else {
    block_next = find_next(block);
    size = get_size(block);
  }

  /* Get header prev alloc bit */
  bool prev_alloc = get_prev_alloc(block);
  /* Get header alloc bit */
  bool next_alloc = get_alloc(block_next);

  /* Prev and next both alloc */
  if (prev_alloc && next_alloc) {

    /* Update alloc prev bit of next block to zero (free) */
    block_next->header = block_next->header & ~((word_t)alloc_prev_mask);
    /* Update the prev mini bit for next block */
    if (is_mini) {
      block_next->header = block_next->header | prev_mini_mask;
    }

    /* LIFO seg size insertion */
    insert_block_before(block, size_to_root(size), true, is_mini);
  }

  /* Prev alloc and next free */
  else if (prev_alloc && !next_alloc) {
    /* Update the size of new free block */
    bool next_mini = (bool)(block_next->header & alloc_mini_mask);
    size_t next_size;
    /* Get the size of next block */
    if (next_mini) {
      next_size = dsize;
    } else {
      next_size = get_size(block_next);
    }
    /* Remove next block from list */
    remove_block(block_next, size_to_root(next_size), next_mini);
    size += next_size;
    /* Update header and footer */
    word_t alloc_prev = block->header & alloc_prev_mini_mask;
    write_header(block, size, false, alloc_prev);
    write_footer(block, size, false, alloc_prev);

    block_t *block_next_next = find_next(block);
    /* Change the prev mini of next block to zero */
    block_next_next->header =
        block_next_next->header & ~((word_t)prev_mini_mask);

    /* LIFO seg size insertion */
    insert_block_before(block, size_to_root(size), true, false);
  }

  /* Prev free and next alloc */
  else if (!prev_alloc && next_alloc) {
    /* Get prev mini */
    bool prev_mini = (bool)(block->header & prev_mini_mask);

    /* Consecutive prev block, not free list prev block */
    block_t *block_prev;
    size_t prev_size;
    /* Get the size of prev block */
    if (prev_mini) {
      block_prev = (block_t *)(block - 2);
      prev_size = dsize;
    } else {
      block_prev = find_prev(block);
      prev_size = get_size(block_prev);
    }

    /* LIFO remove */
    remove_block(block_prev, size_to_root(prev_size), prev_mini);

    size += prev_size;
    /* Update header and footer */
    word_t alloc_prev = block_prev->header & alloc_prev_mini_mask;
    write_header(block_prev, size, false, alloc_prev);
    write_footer(block_prev, size, false, alloc_prev);
    /* Update alloc prev bit of next block to zero (free) */
    block_next->header = block_next->header & ~((word_t)alloc_prev_mask);
    /* Change the prev mini of next block to zero */
    block_next->header = block_next->header & ~((word_t)prev_mini_mask);
    block = block_prev;

    /* LIFO seg size insertion */
    insert_block_before(block, size_to_root(size), true, false);
  }

  /* Next and prev block are both free */
  else {
    /* Consecutive prev block, not free list prev block */
    bool prev_mini = (bool)(block->header & prev_mini_mask);
    block_t *block_prev;
    size_t prev_size;
    /* Get the size of prev block */
    if (prev_mini) {
      block_prev = (block_t *)(block - 2);
      prev_size = dsize;
    } else {
      block_prev = find_prev(block);
      prev_size = get_size(block_prev);
    }
    bool next_mini = (bool)(block_next->header & alloc_mini_mask);
    size_t next_size;
    /* Get the size of next block */
    if (next_mini) {
      next_size = dsize;
    } else {
      next_size = get_size(block_next);
    }
    /* LIFO remove next and prev free blocks */
    remove_block(block_next, size_to_root(next_size), next_mini);
    remove_block(block_prev, size_to_root(prev_size), prev_mini);

    size += next_size + prev_size;
    /* Update header and footer */
    word_t alloc_prev = block_prev->header & alloc_prev_mini_mask;
    write_header(block_prev, size, false, alloc_prev);
    write_footer(block_prev, size, false, alloc_prev);
    block = block_prev;

    block_t *block_next_next = find_next(block_prev);
    /* Change the prev mini of next block to zero */
    block_next_next->header =
        block_next_next->header & ~((word_t)prev_mini_mask);

    /* LIFO seg size insertion */
    insert_block_before(block, size_to_root(size), true, false);
  }

  dbg_ensures(!get_alloc(block));

  return block;
}

/*
 * Split the allocated block if too big
 * Argv: Block pointer and adjusted size
 * Does not return
 * Pre: Block is marked as allocated,
 * adjusted size is smaller than the block size
 * Post: the Block is split if enough free space,
 * otherwise the block is allocated fully
 */
static void split_block(block_t *block, size_t asize) {
  dbg_requires(get_alloc(block));

  size_t block_size = get_size(block);
  /* Free space left */
  size_t left_size = block_size - asize;

  /* Remove split block */
  remove_block(block, size_to_root(block_size), false);

  /* Check if the allocated block is mini block */
  bool left_mini = asize == min_block_size ? true : false;
  /* Split if there is enough free space */
  block_t *block_new;
  /* Free space is not mini block */
  if (left_size > min_block_size) {
    word_t alloc_prev = block->header & alloc_prev_mini_mask;
    /* Allocated block is mini block */
    if (left_mini) {
      write_header(block, asize, true, alloc_prev | alloc_mini_mask);
      /* Split new block */
      block_new = find_next(block);
      write_header(block_new, left_size, false, alloc_prev_mini_mask);
      write_footer(block_new, left_size, false, alloc_prev_mini_mask);
    }
    /* Allocated block is not mini block */
    else {
      write_header(block, asize, true, alloc_prev);
      /* Split new block */
      block_new = find_next(block);
      write_header(block_new, left_size, false, alloc_prev_mask);
      write_footer(block_new, left_size, false, alloc_prev_mask);
    }

    /* Free space block */
    block_t *block_next = find_next(block_new);
    /* Change the prev alloc of next block to zero */
    block_next->header = block_next->header & ~((word_t)alloc_prev_mask);

    /* LIFO seg size insertion */
    insert_block_before(block_new, size_to_root(left_size), true, false);
  }
  /* Split block is mini block */
  else if (left_size == min_block_size) {
    word_t alloc_prev = block->header & alloc_prev_mini_mask;
    /* Allocated block is mini block */
    if (left_mini) {
      write_header(block, asize, true, alloc_prev | alloc_mini_mask);
      /* Split new block is mini block */
      block_new = find_next(block);
      write_header(block_new, left_size, false,
                   alloc_prev_mini_mask | alloc_mini_mask);
    }
    /* Allocated block is not mini block */
    else {
      write_header(block, asize, true, alloc_prev);
      /* Split new block is mini block */
      block_new = find_next(block);
      write_header(block_new, left_size, false, alloc_mini_alloc_prev);
    }

    /* Get free space mini block */
    block_t *block_next = (block_t *)(block_new + 2);
    /* Change the prev alloc of next block to zero and prev mini to one */
    block_next->header = block_next->header & ~((word_t)alloc_prev_mask);
    block_next->header = block_next->header | prev_mini_mask;

    /* LIFO seg size insertion */
    insert_block_before(block_new, size_to_root(left_size), true, true);
  }

  dbg_ensures(get_alloc(block));
}

/*
 * Find a free block for malloc
 * Argv: Adjusted size of the malloc request
 * Return the found free block or NULL on not found
 * Pre: asize is double word aligned
 * Post: Return the found free block or NULL on not found
 */
static block_t *find_fit(size_t asize) {
  block_t *block = NULL;
  block_t *block_best = NULL;
  size_t size = 0;
  size_t size_best = 0;
  /* Segregated list index */
  size_t n;
  /* Best fit bound */
  int timeout = 4;
  int i = 0;
  bool found_fit = false;

  /* Find the correct size bucket */
  /* Increase n until found correct size or the end */
  for (n = 0; n < seg_count; n++) {
    if (asize <= seg_size[n]) {
      break;
    }
  }
  /* Traverse the free list */
  while (n < seg_count && !found_fit) {
    block = seg_list_root[n];
    if (block != NULL) {
      do {
        if (n == 0) {
          /* Find mini block fit */
          if (asize <= min_block_size) {
            return seg_list_root[n];
          }
          break;
        } else {
          size = get_size(block);
          /* Find best (better) fit */
          if (asize <= size) {
            if (!found_fit) {
              block_best = block;
              size_best = size;
              found_fit = true;
            }
            if (size <= size_best) {
              block_best = block;
              size_best = size;
            }
            i++;
          }
          block = ((struct free *)block->payload)->next;
        }
      } while (i < timeout && block != seg_list_root[n]);
    }
    /* Increase n to next seg list */
    n++;
  }
  return block_best;
}

/*
 * Check the consistency of the heap
 * - heap_start
 * - prologue
 * - alignment
 * - heap boundaries (between prologue and epilogue)
 * - minimum size
 * - header and footer matching
 * - coalescing
 * - next/prev pointers consistency
 * - next/prev pointers heap boundary
 * - block bucket size range
 * - free block numbers consistency
 * - epilogue
 */
bool mm_checkheap(int line) {
  size_t num_free_block = 0;
  size_t num_free_list = 0;
  /* Check heap_start */
  if (!heap_start) {
    perror("Heap start error!\n");
    return false;
  } else {
    /* Low prologue address as heap first byte */
    void *low = mem_heap_lo();
    /* High epilogue address as 7 bytes backward from last byte */
    void *high = mem_heap_hi() - 7;

    /* Check prologue */
    if (get_size((block_t *)low) || !get_alloc((block_t *)low)) {
      perror("Prologue error!\n");
      return false;
    }

    block_t *block = heap_start;
    size_t size;
    bool alloc;
    bool alloc_next;
    bool alloc_next_prev;
    word_t *footer = NULL;

    /* Check all blocks one by one */
    do {
      size = get_size(block);
      alloc = get_alloc(block);
      alloc_next = get_alloc(find_next(block));
      alloc_next_prev = get_prev_alloc(find_next(block));
      footer = header_to_footer(block);

      /* Check alignment */
      if (size != round_up(size, dsize)) {
        perror("Alignment error!\n");
        return false;
      }

      /* Check heap boundaries */
      /* Low address as 8 bytes forward from prologue */
      if (((void *)block < low + 8) || ((void *)block > high)) {
        perror("Heap boundary error!\n");
        return false;
      }

      /* Check header and footer */
      /* Check minimum size */
      if (size < min_block_size) {
        perror("Size error!\n");
        return false;
      }

      /* Check free block header and footer matching */
      if (block->header != *(footer) && !alloc) {
        perror("Header and footer matching error!\n");
        return false;
      }

      /* Check alloc prev bit correctness */
      if (alloc != alloc_next_prev) {
        perror("Alloc prev bit matching error!\n");
        return false;
      }

      /* Count free blocks */
      if (!alloc) {
        num_free_block++;
        /* Check heap boundaries */
        /* Low address as 8 bytes forward from prologue */
        if (((void *)((struct free *)block->payload)->next < low + 8) ||
            ((void *)((struct free *)block->payload)->next > high) ||
            ((void *)((struct free *)block->payload)->prev < low + 8) ||
            ((void *)((struct free *)block->payload)->prev > high)) {
          perror("Next/prev pointers heap boundary error!\n");
          return false;
        }
      }

      /* Check coalescing */
      if (!alloc && !alloc_next) {
        perror("Coalescing error!\n");
        return false;
      }

      block = find_next(block);
    } while (block != (block_t *)high);

    /* Check free list */
    block_t *block_curr;
    block_t *block_next;
    size_t i = 0;
    /* Check each bucket */
    while (i < seg_count) {
      block_curr = seg_list_root[i];
      if (block_curr != NULL) {
        /* Check from root */
        do {
          block_next = ((struct free *)block_curr->payload)->next;
          /* Check next/prev pointers consistency */
          if (block_curr != ((struct free *)block_next->payload)->prev) {
            printf("Curr address: %#011lx\n", (word_t) & (block_curr->header));
            printf("Next address: %#011lx\n", (word_t) & (block_next->header));
            printf("Prev address: %#011lx\n",
                   (word_t) &
                       ((((struct free *)block_next->payload)->prev)->header));
            perror("Next/prev pointers inconsistent error!\n");
            return false;
          }

          /* Check heap boundaries */
          /* Low address as 8 bytes forward from prologue */
          if (((void *)((struct free *)block_curr->payload)->next < low + 8) ||
              ((void *)((struct free *)block_curr->payload)->next > high) ||
              ((void *)((struct free *)block_curr->payload)->prev < low + 8) ||
              ((void *)((struct free *)block_curr->payload)->prev > high)) {
            perror("Next/prev pointers heap boundary error!\n");
            return false;
          }

          /* Check block bucket size range */
          if (get_size(block_curr) > seg_size[i]) {
            printf("block_curr size: %lu\n", get_size(block_curr));
            printf("seg_size   size: %lu\n", seg_size[i]);
            perror("Block bucket size range error!\n");
            return false;
          }

          /* Count free list */
          num_free_list++;

          block_curr = ((struct free *)block_curr->payload)->next;
        } while (block_curr != seg_list_root[i]);
      }
      i++;
    }

    /* Check free block/free list numbers consistency */
    if (num_free_block != num_free_list) {
      perror("Free block numbers inconsistent error!");
      return false;
    }

    /* Check epilogue */
    if (get_size((block_t *)high) || !get_alloc((block_t *)high)) {
      perror("Epilogue error!\n");
      return false;
    }
  }
  return true;
}

/* Remove block from the free list pointed by root. Do a different
 * mini block remove if the block is mini block */
void remove_block(block_t *block, block_t **root, bool is_mini) {
  if (!is_mini) {
    /* Case 1: Only one block */
    if (*root == ((struct free *)(*root)->payload)->next) {
      *root = NULL;
    }

    /* Case 2: Block is root */
    else if (block == *root) {
      block_t *tail = ((struct free *)(*root)->payload)->prev;
      *root = ((struct free *)block->payload)->next;
      ((struct free *)(*root)->payload)->prev = tail;
      ((struct free *)tail->payload)->next = *root;
    }

    /* Case 3: Block is else where */
    else {
      block_t *block_next = ((struct free *)block->payload)->next;
      block_t *block_prev = ((struct free *)block->payload)->prev;
      ((struct free *)block_prev->payload)->next = block_next;
      ((struct free *)block_next->payload)->prev = block_prev;
    }
  }
  /* Mini seg list */
  else {
    /* Case 1: Only one block */
    if (*root == (block_t *)((word_t)((*root)->header & addr_mask))) {
      *root = NULL;
    }

    /* Case 2: Block is root */
    else if (block == *root) {
      block_t *tail = (block_t *)(*(word_t *)((*root)->payload) & addr_mask);
      word_t tail_addr = (word_t)tail & addr_mask;
      word_t tail_lower_bits = (word_t)(tail->header) & lower_bits_mask;
      *root = (block_t *)((word_t)(block->header) & addr_mask);
      word_t root_addr = (word_t)(*root) & addr_mask;
      word_t root_lower_bits = (word_t)((*root)->header) & lower_bits_mask;

      *(word_t *)((*root)->payload) = tail_addr | root_lower_bits;
      *(word_t *)tail = root_addr | tail_lower_bits;
    }

    /* Case 3: Block is else where */
    else {
      block_t *block_next = (block_t *)(block->header & addr_mask);
      word_t next_addr = (word_t)block_next & addr_mask;
      word_t next_lower_bits = block_next->header & lower_bits_mask;
      block_t *block_prev =
          (block_t *)(*((word_t *)block->payload) & addr_mask);
      word_t prev_addr = (word_t)block_prev & addr_mask;
      word_t prev_lower_bits = block_prev->header & lower_bits_mask;

      *(word_t *)block_prev = next_addr | prev_lower_bits;
      *(word_t *)(block_next->payload) = prev_addr | next_lower_bits;
    }
  }
}

/* LIFO Insert block before the block pointed by block_next. Update root
 * if next block is root. Do a different mini block insertion if the
 * block is a mini block
 */
void insert_block_before(block_t *block, block_t **block_next, bool is_root,
                         bool is_mini) {
  /* Not mini seg list */
  if (!is_mini) {
    /* Case 1: No next block, empty list */
    if (*block_next == NULL) {
      *block_next = block;
      ((struct free *)block->payload)->next = block;
      ((struct free *)block->payload)->prev = block;
    }
    /* Case 2: Not empty free list */
    else {
      block_t *block_prev = ((struct free *)(*block_next)->payload)->prev;
      ((struct free *)block_prev->payload)->next = block;
      ((struct free *)block->payload)->next = (*block_next);
      ((struct free *)(*block_next)->payload)->prev = block;
      ((struct free *)block->payload)->prev = block_prev;
      /* Update root if next block is root */
      if (is_root) {
        (*block_next) = block;
      }
    }
  }
  /* Mini seg list */
  else {
    /* Case 1: No next block, empty list */
    if (*block_next == NULL) {
      word_t block_addr = (word_t)block & addr_mask;
      word_t lower_bits = block->header & lower_bits_mask;
      *block_next = block;
      *(word_t *)block = block_addr | lower_bits;
      *(word_t *)(block->payload) = block_addr | lower_bits;
    }
    /* Case 2: Not empty free list */
    else {
      word_t block_addr = (word_t)block & addr_mask;
      word_t lower_bits = block->header & lower_bits_mask;
      block_t *block_prev =
          (block_t *)(*(word_t *)((*block_next)->payload) & addr_mask);
      word_t prev_addr = (word_t)block_prev & addr_mask;
      word_t prev_lower_bits = block_prev->header & lower_bits_mask;
      word_t next_addr = (word_t)(*block_next) & addr_mask;
      word_t next_lower_bits = (*block_next)->header & lower_bits_mask;

      *(word_t *)block_prev = block_addr | prev_lower_bits;
      *(word_t *)block = next_addr | lower_bits;
      *(word_t *)((*block_next)->payload) = block_addr | next_lower_bits;
      *(word_t *)(block->payload) = prev_addr | lower_bits;
      /* Update root if next block is root */
      if (is_root) {
        *block_next = block;
      }
    }
  }
}

/* Return the pointer to the root of seg free list pointer that adjusted
 * size is in the size range
 */
block_t **size_to_root(size_t asize) {
  for (size_t i = 0; i < seg_count; i++) {
    if (asize <= seg_size[i]) {
      return &seg_list_root[i];
    }
  }
  return &seg_list_root[seg_count];
}

/* Print the whole heap for debugging */
void print_heap() {
  block_t *block = heap_start;
  word_t size;
  word_t alloc;
  word_t alloc_next;
  word_t num_free_block = 0;

  /* High epilogue address as 7 bytes backward from last byte */
  void *high = mem_heap_hi() - 7;

  do {
    if (block->header & alloc_mini_mask) {
      size = dsize;
      alloc = get_alloc(block);
      alloc_next = get_alloc((block_t *)(block + 2));
    } else {
      size = get_size(block);
      alloc = get_alloc(block);
      alloc_next = get_alloc(find_next(block));
    }
    if (alloc) {
      printf("alloc: %#011lx: %#011lx %-7lu\n", (word_t) & (block->header),
             (word_t)block->header, size);
    }
    if (!alloc) {
      num_free_block++;
      if (block->header & alloc_mini_mask) {
        printf("free : %#011lx: %#011lx %-7lu next: %#011lx prev: %#011lx\n",
               (word_t) & (block->header), (word_t)block->header, size,
               (word_t)(block->header), (word_t)(block->payload));
      } else {
        printf("free : %#011lx: %#011lx %-7lu next: %#011lx prev: %#011lx\n",
               (word_t) & (block->header), (word_t)block->header, size,
               (word_t)(((struct free *)block->payload)->next),
               (word_t)(((struct free *)block->payload)->prev));
      }
    }
    if (block->header & alloc_mini_mask) {
      block = (block_t *)(block + 2);
    } else {
      block = find_next(block);
    }
  } while (block != (block_t *)high);
  /* Print epilogue */
  printf("alloc: %#011lx: %#011lx %-7lu\n", (word_t) & (block->header),
         (word_t)block->header, size);
  printf("Free blocks: %lu\n", num_free_block);
}

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ba c1 e1 52 13 0a               *
 *                                                                           *
 *****************************************************************************
 */

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) { return (x > y) ? x : y; }

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n) {
  return n * ((size + (n - 1)) / n);
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc, word_t alloc_prev) {
  return alloc ? (size | alloc_mask | alloc_prev) : size | alloc_prev;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word) { return (word & size_mask); }

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block) { return extract_size(block->header); }

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block) {
  size_t asize = get_size(block);
  return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word) { return (bool)(word & alloc_mask); }

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block) { return extract_alloc(block->header); }

/* Get the prev alloc bit from current block */
static bool get_prev_alloc(block_t *block) {
  return (bool)((block->header) & alloc_prev_mask);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 * Pre: Block is a valid block pointer, size is non-negative
 * Post: The header is written based on the given size and lower bits
 */
static void write_header(block_t *block, size_t size, bool alloc,
                         word_t alloc_prev) {
  dbg_requires(block != NULL);
  block->header = pack(size, alloc, alloc_prev);
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 * Pre: Block is a valid block pointer, size is non-negative
 * Post: The footer is written based on the given size and lower bits
 */
static void write_footer(block_t *block, size_t size, bool alloc,
                         word_t alloc_prev) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) == size && size > 0);
  word_t *footerp = header_to_footer(block);
  *footerp = pack(size, alloc, alloc_prev);
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) != 0);
  return (block_t *)((char *)block + get_size(block));
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block) {
  // Compute previous footer position as one word before the header
  return &(block->header) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) != 0);
  word_t *footerp = find_prev_footer(block);
  size_t size = extract_size(*footerp);
  return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp) {
  return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block) {
  return (void *)(block->payload);
}

/*
 * header_to_footer: given a block pointer, returns a pointer to the
 *                   corresponding footer.
 */
static word_t *header_to_footer(block_t *block) {
  return (word_t *)(block->payload + get_size(block) - dsize);
}