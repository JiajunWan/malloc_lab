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

// Word and header size (bytes)
static const size_t wsize = sizeof(word_t);

// Double word size (bytes)
static const size_t dsize = 2 * wsize;

// Minimum block size (bytes)
static const size_t min_block_size = 2 * dsize;

// Expand heap by at least chunksize (4096) each time no free space
// (Must be divisible by dsize)
static const size_t chunksize = (1L << 12);

/* Heap init size */
static const size_t initsize = (1L << 6);

// Mask to get the alloc bit
static const word_t alloc_mask = 0x1;

// Mask to get the size
static const word_t size_mask = ~(word_t)0xF;

/* Seg list buckets count */
static const size_t seg_count = 14;

/* Seg list size const array */
static const size_t seg_size[seg_count] = {32,    64,    96,    128,      256,
                                           512,   1024,  2048,  4096,     8192,
                                           16384, 32768, 65536, INT64_MAX};

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

// Pointer to first block
static block_t *heap_start = NULL;

/* Function prototypes for internal helper routines */

/* Own helpers */
/* Remove free list block */
void remove_block(block_t *block, block_t **root);
/* Insert before one block */
void insert_block_before(block_t *block, block_t **block_next, bool is_root);
/* Block size to correct seg bucket list */
block_t **size_to_root(size_t size);
/* Print the whole heap helper */
void print_heap();

bool mm_checkheap(int lineno);

static block_t *extend_heap(size_t size);
static block_t *find_fit(size_t asize);
static block_t *coalesce_block(block_t *block);
static void split_block(block_t *block, size_t asize);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static word_t *header_to_footer(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
bool mm_init(void) {
  // Create the initial empty heap
  word_t *start = (word_t *)(mem_sbrk(2 * wsize));

  if (start == (void *)-1) {
    return false;
  }
  /* Heap prologue and epilogue preventing heap boundary coalescing */
  start[0] = pack(0, true); // Heap prologue (block footer)
  start[1] = pack(0, true); // Heap epilogue (block header)

  // Heap starts with first "block header", currently the epilogue
  heap_start = (block_t *)&(start[1]);
  /* Init seg list */
  for (size_t i = 0; i < seg_count; i++) {
    seg_list_root[i] = NULL;
  }

  // Extend the empty heap with a free block of chunksize bytes
  if (extend_heap(initsize) == NULL) {
    return false;
  }

  return true;
}

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
void *malloc(size_t size) {
  dbg_requires(mm_checkheap(__LINE__));
  // malloc_count++;

  size_t asize;      // Adjusted block size
  size_t extendsize; // Amount to extend heap if no fit is found
  block_t *block;
  void *bp = NULL;

  if (heap_start == NULL) { // Initialize heap if it isn't initialized
    mm_init();
  }

  if (size == 0) { // Ignore spurious request
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
  }

  // Adjust block size to include overhead and to meet alignment requirements
  asize = round_up(size + dsize, dsize);

  // Search the free list for a fit
  block = find_fit(asize);

  // If no fit is found, request more memory, and then and place the block
  if (block == NULL) {
    // Always request at least chunksize
    extendsize = max(asize, chunksize);
    block = extend_heap(extendsize);
    if (block == NULL) { // extend_heap returns an error
      return bp;
    }
  }

  // The block should be marked as free
  dbg_assert(!get_alloc(block));

  // Mark block as allocated
  size_t block_size = get_size(block);
  write_header(block, block_size, true);
  write_footer(block, block_size, true);

  // Try to split the block if too large
  split_block(block, asize);

  bp = header_to_payload(block);

  dbg_ensures(mm_checkheap(__LINE__));
  return bp;
}

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
void free(void *bp) {
  dbg_requires(mm_checkheap(__LINE__));

  if (bp == NULL) {
    return;
  }

  block_t *block = payload_to_header(bp);
  size_t size = get_size(block);

  // The block should be marked as allocated
  dbg_assert(get_alloc(block));

  // Mark the block as free
  write_header(block, size, false);
  write_footer(block, size, false);

  // Try to coalesce the block with its neighbors
  block = coalesce_block(block);

  dbg_ensures(mm_checkheap(__LINE__));
}

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
/* Can optimize realloc */
void *realloc(void *ptr, size_t size) {
  block_t *block = payload_to_header(ptr);
  size_t copysize;
  void *newptr;

  // If size == 0, then free block and return NULL
  if (size == 0) {
    free(ptr);
    return NULL;
  }

  // If ptr is NULL, then equivalent to malloc
  if (ptr == NULL) {
    return malloc(size);
  }

  // Otherwise, proceed with reallocation
  newptr = malloc(size);

  // If malloc fails, the original block is left untouched
  if (newptr == NULL) {
    return NULL;
  }

  // Copy the old data
  copysize = get_payload_size(block); // gets size of old payload
  if (size < copysize) {
    copysize = size;
  }
  memcpy(newptr, ptr, copysize);

  // Free the old block
  free(ptr);

  return newptr;
}

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
void *calloc(size_t elements, size_t size) {
  void *bp;
  size_t asize = elements * size;

  if (asize / elements != size) {
    // Multiplication overflowed
    return NULL;
  }

  bp = malloc(asize);
  if (bp == NULL) {
    return NULL;
  }

  // Initialize all bits to 0
  memset(bp, 0, asize);

  return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
static block_t *extend_heap(size_t size) {
  void *bp;

  // Allocate an even number of words to maintain alignment
  size = round_up(size, dsize);
  if ((bp = mem_sbrk(size)) == (void *)-1) {
    return NULL;
  }

  // Initialize free block header/footer
  /* The bp returned by mem_sbrk as the payload pointer. Payload to header will
   * lead to the previous epilogue. Overwrite this epilogue as the new header.
   */
  block_t *block = payload_to_header(bp);
  write_header(block, size, false);
  write_footer(block, size, false);

  // Create new epilogue header
  block_t *block_epilogue = find_next(block);
  write_header(block_epilogue, 0, true);

  // Coalesce in case the previous block was free
  block = coalesce_block(block);

  return block;
}

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
static block_t *coalesce_block(block_t *block) {
  dbg_requires(!get_alloc(block));

  size_t size = get_size(block);

  /* Consecutive next and prev blocks, not free list next or prev block */
  block_t *block_next = find_next(block);
  block_t *block_prev = find_prev(block);

  /* Extract footer alloc bit */
  bool prev_alloc = extract_alloc(*find_prev_footer(block));
  /* Get header alloc bit */
  bool next_alloc = get_alloc(block_next);

  if (prev_alloc && next_alloc) { // Case 1
    /* FIFO insert */
    insert_block_before(block, size_to_root(size), true);
  }

  else if (prev_alloc && !next_alloc) { // Case 2
    /* Update the size of new free block */
    size += get_size(block_next);
    write_header(block, size, false);
    write_footer(block, size, false);

    /* Remove next block from list and insert at root */
    remove_block(block_next, size_to_root(get_size(block_next)));
    insert_block_before(block, size_to_root(size), true);
  }

  else if (!prev_alloc && next_alloc) { // Case 3
    /* FIFO remove */
    remove_block(block_prev, size_to_root(get_size(block_prev)));

    size += get_size(block_prev);
    write_header(block_prev, size, false);
    write_footer(block_prev, size, false);
    block = block_prev;

    /* FIFO seg size insertion */
    insert_block_before(block, size_to_root(size), true);

  }

  else { // Case 4
    /* FIFO remove */
    remove_block(block_next, size_to_root(get_size(block_next)));
    remove_block(block_prev, size_to_root(get_size(block_prev)));

    size += get_size(block_next) + get_size(block_prev);
    write_header(block_prev, size, false);
    write_footer(block_prev, size, false);
    block = block_prev;

    /* FIFO seg size insertion */
    insert_block_before(block, size_to_root(size), true);

  }

  dbg_ensures(!get_alloc(block));

  return block;
}

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
static void split_block(block_t *block, size_t asize) {
  dbg_requires(get_alloc(block));
  /* TODO: Can you write a precondition about the value of asize? */

  size_t block_size = get_size(block);

  /* Remove splitted block */
  remove_block(block, size_to_root(block_size));

  /* Split if there is enough free space */
  if ((block_size - asize) >= min_block_size) {
    write_header(block, asize, true);
    write_footer(block, asize, true);

    /* Splited new block */
    block_t *block_new = find_next(block);
    write_header(block_new, block_size - asize, false);
    write_footer(block_new, block_size - asize, false);

    /* FIFO seg size insertion */
    insert_block_before(block_new, size_to_root(block_size - asize), true);

  }

  dbg_ensures(get_alloc(block));
}

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
static block_t *find_fit(size_t asize) {
  block_t *block = NULL;
  block_t *block_best = NULL;
  size_t size = 0;
  size_t size_best = 0;
  int timeout = 4;
  int i = 0;
  size_t n;
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
        size = get_size(block);
        /* Find best fit */
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
      } while (i < timeout && block != seg_list_root[n]);
    }
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
  word_t num_free_block = 0;
  word_t num_free_list = 0;
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
    word_t size;
    word_t alloc;
    word_t alloc_next;
    word_t *footer = NULL;

    /* Check all blocks one by one */
    do {
      size = get_size(block);
      alloc = get_alloc(block);
      alloc_next = get_alloc(find_next(block));
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

      /* Check header and footer matching */
      if (block->header != *(footer)) {
        perror("Header and footer matching error!\n");
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

void remove_block(block_t *block, block_t **root) {
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

void insert_block_before(block_t *block, block_t **block_next, bool is_root) {
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

block_t **size_to_root(size_t asize) {
  for (size_t i = 0; i < seg_count; i++) {
    if (asize <= seg_size[i]) {
      return &seg_list_root[i];
    }
  }
  return &seg_list_root[seg_count];
}

void print_heap() {
  block_t *block = heap_start;
  word_t size;
  word_t alloc;
  word_t alloc_next;
  word_t num_free_block = 0;

  /* High epilogue address as 7 bytes backward from last byte */
  void *high = mem_heap_hi() - 7;

  do {
    size = get_size(block);
    alloc = get_alloc(block);
    alloc_next = get_alloc(find_next(block));
    if (alloc) {
      printf("alloc: %#011lx: %-7lu\n", (word_t) & (block->header), size);
    }
    if (!alloc) {
      num_free_block++;
      printf("free : %#011lx: %-7lu next: %#011lx prev: %#011lx\n",
             (word_t) & (block->header), size,
             (word_t)(((struct free *)block->payload)->next),
             (word_t)(((struct free *)block->payload)->prev));
    }

    block = find_next(block);
  } while (block != (block_t *)high);
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
static word_t pack(size_t size, bool alloc) {
  return alloc ? (size | alloc_mask) : size;
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
  return asize - dsize;
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

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 * TODO: Are there any preconditions or postconditions?
 */
static void write_header(block_t *block, size_t size, bool alloc) {
  dbg_requires(block != NULL);
  block->header = pack(size, alloc);
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 * TODO: Are there any preconditions or postconditions?
 */
static void write_footer(block_t *block, size_t size, bool alloc) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) == size && size > 0);
  word_t *footerp = header_to_footer(block);
  *footerp = pack(size, alloc);
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