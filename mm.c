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

// Expand heap by chunksize (4096)
// each time no free space
// (Must be divisible by dsize)
static const size_t chunksize = (1L << 12);

// Mask to get the alloc bit
static const word_t alloc_mask = 0x1;

// Mask to get the size
static const word_t size_mask = ~(word_t)0xF;

/* Represents the header and payload of one block in the heap */
typedef struct block {
  /* Header contains size + allocation flag */
  word_t header;

  /* For this lab, we will
   * allow you to include a zero-length array in a union, as long as the
   * union is the last field in its containing struct. However, this is
   * compiler-specific behavior and should be avoided in general.
   *
   * WARNING: DO NOT cast this pointer to/from other types! Instead, you
   * should use a union to alias this zero-length array with another struct,
   * in order to store additional types of data in the payload memory.
   */
  char payload[0];

} block_t;

/* Global variables */

/* Explicit free list root pointer, always points to the first inserted free
 * block (LIFO) */
block_t *explicit_list_root = NULL;
/* Explicit free list tail pointer, always points to the last inserted free
 * block (LIFO) */
block_t *explicit_list_tail = NULL;

size_t malloc_count = 0;
size_t free_no_coal_count = 0;

// Pointer to first block
static block_t *heap_start = NULL;

/* Function prototypes for internal helper routines */

/* Own helpers */
void remove_block(block_t *block);
void insert_block(block_t *block, block_t *block_next);
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

  // Extend the empty heap with a free block of chunksize bytes
  if (extend_heap(chunksize) == NULL) {
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
  malloc_count++;
  // printf("1 ");

  size_t asize;      // Adjusted block size
  size_t extendsize; // Amount to extend heap if no fit is found
  block_t *block;
  void *bp = NULL;

  if (heap_start == NULL) // Initialize heap if it isn't initialized
  {
    mm_init();
  }

  if (size == 0) // Ignore spurious request
  {
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
  }

  // Adjust block size to include overhead and to meet alignment requirements
  asize = round_up(size + dsize, dsize);

  // Search the free list for a fit
  block = find_fit(asize);

  // If no fit is found, request more memory, and then and place the block
  if (block == NULL) {
    /* Deferred coalescing */
    block = heap_start;
    do {
      if (!get_alloc(block)) {
        block = coalesce_block(block);
        if (asize <= get_size(block)) {
          break;
        }
      }
      block = find_next(block);
    } while (block != (block_t *)(mem_heap_hi() - 7));

    // block = find_fit(asize);

    if (block == (block_t *)(mem_heap_hi() - 7)) {
      // Always request at least chunksize
      extendsize = max(asize, chunksize);
      block = extend_heap(extendsize);
      if (block == NULL) // extend_heap returns an error
      {
        return bp;
      }
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
  malloc_count--;
  // printf("2 ");

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
  // block = coalesce_block(block);

  /* Deferred coalescing, just insert */
  insert_block(block, explicit_list_root);
  free_no_coal_count++;

  if (malloc_count == 0 || free_no_coal_count > 3) {
    /* Deferred coalescing */
    block = explicit_list_root;
    block_t *block_next = (block_t *)*(word_t *)(block->payload);
    do {
      if (!get_alloc(block)) {
        block_next = (block_t *)*(word_t *)(block->payload);
        block = coalesce_block(block);
        /* Check if next is coalesced */
        if (block_next != (block_t *)*(word_t *)(block->payload)) {
          block_next = (block_t *)*(word_t *)(block_next->payload);
        }
      }
      block = block_next;
    } while (block != explicit_list_root);
  }

  dbg_ensures(mm_checkheap(__LINE__));
}

/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
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
  // block = coalesce_block(block);

  insert_block(block, explicit_list_root);
  free_no_coal_count++;

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
  // if (block_prev == block) {
  //   prev_alloc = true;
  // }
  /* Get header alloc bit */
  bool next_alloc = get_alloc(block_next);

  if (prev_alloc && next_alloc) // Case 1
  {
    /* Insert at root */
    /* Deferred coelascing comment out */
    // insert_block(block, explicit_list_root);
  }

  else if (prev_alloc && !next_alloc) // Case 2
  {
    /* Update the size of new free block */
    size += get_size(block_next);
    write_header(block, size, false);
    write_footer(block, size, false);

    /* Remove next block from list and insert at root */
    remove_block(block_next);

    /* Deferred coalescing */
    remove_block(block);
    free_no_coal_count--;

    insert_block(block, explicit_list_root);
  }

  else if (!prev_alloc && next_alloc) // Case 3
  {
    remove_block(block_prev);

    /* Deferred coalescing */
    remove_block(block);
    free_no_coal_count--;

    size += get_size(block_prev);
    write_header(block_prev, size, false);
    write_footer(block_prev, size, false);
    block = block_prev;

    /* Remove block from list and insert at root */
    insert_block(block, explicit_list_root);
  }

  else // Case 4
  {
    /* Deferred coalescing */
    remove_block(block);
    free_no_coal_count--;

    size += get_size(block_next) + get_size(block_prev);
    write_header(block_prev, size, false);
    write_footer(block_prev, size, false);
    block = block_prev;

    /* Remove next block and block from list and insert at root */
    remove_block(block_next);
    remove_block(block);
    insert_block(block, explicit_list_root);
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

  /* Get next block */
  block_t *block_next = (block_t *)*(word_t *)(block->payload);
  // block_t *block_prev = (block_t *)*(word_t *)(block->payload + wsize);

  /* Split if there is enough free space */
  if ((block_size - asize) >= min_block_size) {
    write_header(block, asize, true);
    write_footer(block, asize, true);

    /* Splited new block */
    block_t *block_new = find_next(block);
    write_header(block_new, block_size - asize, false);
    write_footer(block_new, block_size - asize, false);

    /* Check if there is only one free block in the list */
    if (explicit_list_root == explicit_list_tail) {
      remove_block(block);
      insert_block(block_new, explicit_list_root);
    }
    /* More than one free block in the list */
    else {
      /* Remove old block and insert new block before next block */
      remove_block(block);
      insert_block(block_new, block_next);
    }
  }
  /* No split, update the next and prev pointers */
  else {
    remove_block(block);
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
  if (explicit_list_root == NULL) {
    return NULL;
  }
  block_t *block = explicit_list_root;
  block_t *block_best = NULL;
  size_t size = 0;
  size_t size_best = 0;
  int timeout = 4;
  int i = 0;
  bool found_fit = false;

  /* Traverse the free list */
  do {
    // block = coalesce_block(block);
    size = get_size(block);
    /* Find best fit */
    if (asize <= size) {
      if (!found_fit) {
        block_best = block;
        size_best = size;
        found_fit = true;
      }
      if (size <= size_best) {
        // block = coalesce_block(block);
        block_best = block;
        size_best = size;
      }
      i++;
    }
    block = (block_t *)*(word_t *)(block->payload);
  } while (i < timeout && block != explicit_list_root);

  return block_best;
}

void print_heap() {
  block_t *block = heap_start;
  word_t size;
  word_t alloc;
  word_t alloc_next;
  word_t num_free_block = 0;

  /* High epilogue address as 7 bytes backward from last byte */
  void *high = mem_heap_hi() - 7;

  /* Check all blocks one by one */
  do {
    size = get_size(block);
    alloc = get_alloc(block);
    alloc_next = get_alloc(find_next(block));
    if (alloc) {
      printf("alloc: %#011lx: %lu\n", (word_t) & (block->header), size);
    }
    if (!alloc) {
      num_free_block++;
      printf("free : %#011lx: %lu next: %#011lx, prev: %#011lx\n",
             (word_t) & (block->header), size, *(word_t *)(block->payload),
             *(word_t *)(block->payload + wsize));
    }

    /* Check coalescing */
    // if (!alloc && !alloc_next) {
    //   printf("Deferred coalescing at: %#011lx\n", (word_t) &
    //   (block->header));
    // }

    block = find_next(block);
  } while (block != (block_t *)high);
  printf("Free blocks: %lu\n", num_free_block);
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
 * - free block numbers consistency
 * - epilogue
 */
bool mm_checkheap(int line) {
  word_t num_free_block = 0;
  word_t num_free_list_root_tail = 0;
  word_t num_free_list_tail_root = 0;
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
        if (((void *)*(word_t *)(block->payload) < low + 8) ||
            ((void *)*(word_t *)(block->payload) > high) ||
            ((void *)*(word_t *)(block->payload + wsize) < low + 8) ||
            ((void *)*(word_t *)(block->payload + wsize) > high)) {
          perror("Next/prev pointers heap boundary error!\n");
          return false;
        }
      }

      /* Check coalescing */
      // if (!alloc && !alloc_next) {
      //   perror("Coalescing error!\n");
      //   return false;
      // }

      block = find_next(block);
    } while (block != (block_t *)high);

    /* Check free list */
    block_t *block_curr;
    block_t *block_next;
    block_t *block_prev;

    block_curr = explicit_list_root;
    if (explicit_list_root != NULL & explicit_list_tail != NULL) {
      /* Check from root to tail */
      do {
        block_next = (block_t *)*(word_t *)(block_curr->payload);
        /* Check next/prev pointers consistency */
        if (block_curr != (block_t *)*(word_t *)(block_next->payload + wsize)) {
          perror("next/prev pointers inconsistent error!\n");
          return false;
        }

        /* Check heap boundaries */
        /* Low address as 8 bytes forward from prologue */
        if (((void *)*(word_t *)(block_curr->payload) < low + 8) ||
            ((void *)*(word_t *)(block_curr->payload) > high) ||
            ((void *)*(word_t *)(block_curr->payload + wsize) < low + 8) ||
            ((void *)*(word_t *)(block_curr->payload + wsize) > high)) {
          perror("Next/prev pointers heap boundary error!\n");
          return false;
        }
        /* Count free list */
        num_free_list_root_tail++;

        block_curr = (block_t *)*(word_t *)(block_curr->payload);
      } while (block_curr != explicit_list_root);

      block_curr = explicit_list_tail;
      /* Check from tail to root */
      do {
        block_prev = (block_t *)*(word_t *)(block_curr->payload + wsize);
        /* Check next/prev pointers consistency */
        if (block_curr != (block_t *)*(word_t *)(block_prev->payload)) {
          perror("Next/prev pointers inconsistent error!\n");
          return false;
        }

        /* Check heap boundaries */
        /* Low address as 8 bytes forward from prologue */
        if (((void *)*(word_t *)(block_curr->payload) < low + 8) ||
            ((void *)*(word_t *)(block_curr->payload) > high) ||
            ((void *)*(word_t *)(block_curr->payload + wsize) < low + 8) ||
            ((void *)*(word_t *)(block_curr->payload + wsize) > high)) {
          perror("Next/prev pointers heap boundary error!\n");
          return false;
        }
        /* Count free list */
        num_free_list_tail_root++;

        block_curr = (block_t *)*(word_t *)(block_curr->payload + wsize);
      } while (block_curr != explicit_list_tail);
    }

    /* Check free block/free list numbers consistency */
    if (num_free_block != num_free_list_root_tail ||
        num_free_block != num_free_list_tail_root ||
        num_free_list_root_tail != num_free_list_tail_root) {
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

void remove_block(block_t *block) {
  /* Case 1: Only one block */
  if (block == explicit_list_root && block == explicit_list_tail) {
    explicit_list_root = explicit_list_tail = NULL;
  }

  /* Case 2: Block is root */
  else if (block == explicit_list_root) {
    /* Root is next block */
    explicit_list_root = (block_t *)*(word_t *)(block->payload);
    *(word_t *)(explicit_list_root->payload + wsize) =
        (word_t) & (explicit_list_tail->header);
    *(word_t *)(explicit_list_tail->payload) =
        (word_t) & (explicit_list_root->header);
  }

  /* Case 3: Block is tail */
  else if (block == explicit_list_tail) {
    /* Tail is prev block */
    explicit_list_tail = (block_t *)*(word_t *)(block->payload + wsize);
    *(word_t *)(explicit_list_root->payload + wsize) =
        (word_t) & (explicit_list_tail->header);
    *(word_t *)(explicit_list_tail->payload) =
        (word_t) & (explicit_list_root->header);
  }

  /* Case 4: Block is in the middle */
  else {
    block_t *block_next = (block_t *)*(word_t *)(block->payload);
    block_t *block_prev = (block_t *)*(word_t *)(block->payload + wsize);
    *(word_t *)(block_prev->payload) = (word_t) & (block_next->header);
    *(word_t *)(block_next->payload + wsize) = (word_t) & (block_prev->header);
  }
}

void insert_block(block_t *block, block_t *block_next) {
  /* Case 1: No next block, empty list */
  if (block_next == NULL) {
    explicit_list_root = explicit_list_tail = block;
    *(word_t *)(explicit_list_root->payload) =
        (word_t) & (explicit_list_tail->header);
    *(word_t *)(explicit_list_root->payload + wsize) =
        (word_t) & (explicit_list_tail->header);
  }

  /* Case 2: Only one block */
  else if (block_next == explicit_list_root &&
           block_next == explicit_list_tail) {
    explicit_list_root = block;
    *(word_t *)(explicit_list_root->payload) =
        (word_t) & (explicit_list_tail->header);
    *(word_t *)(explicit_list_root->payload + wsize) =
        (word_t) & (explicit_list_tail->header);
    *(word_t *)(explicit_list_tail->payload) =
        (word_t) & (explicit_list_root->header);
    *(word_t *)(explicit_list_tail->payload + wsize) =
        (word_t) & (explicit_list_root->header);
  }

  /* Case 3: Block_next is root */
  else if (block_next == explicit_list_root) {
    *(word_t *)(block->payload) = (word_t) & (explicit_list_root->header);
    *(word_t *)(explicit_list_root->payload + wsize) =
        (word_t) & (block->header);
    *(word_t *)(block->payload + wsize) =
        (word_t) & (explicit_list_tail->header);
    *(word_t *)(explicit_list_tail->payload) = (word_t) & (block->header);
    explicit_list_root = block;
  }

  /* Case 4: Insert in the middle */
  else {
    block_t *block_prev = (block_t *)*(word_t *)(block_next->payload + wsize);
    *(word_t *)(block->payload) = (word_t) & (block_next->header);
    *(word_t *)(block->payload + wsize) = (word_t) & (block_prev->header);
    *(word_t *)(block_prev->payload) = (word_t) & (block->header);
    *(word_t *)(block_next->payload + wsize) = (word_t) & (block->header);
  }
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
