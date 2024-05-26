/*
 * mm-implicit.c
 * 
 * code is based on CSAPP 3e textbook section 9.9
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static char *heap_listp;
const int MAX_SIZE=15;

/*
 * mm_init
 */
int mm_init(void) {
    int heap_listp=mem_sbrk(4*WSIZE);
    if(heap_listp==(void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); 
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); 
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); 
    heap_listp += (2 * WSIZE);

    if (extend_heap(115) == NULL)
        return -1;
    return 0;
}

/*
 * malloc
 */
void *malloc(size_t size) {
    size_t bias;
    size_t extend;
    char *first;
    if(size == 0)
        return NULL;
    if(size <= DSIZE)
        bias = 2*DSIZE;
    else
        bias = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if((first = find_fit(bias)) != NULL){
        place(first, bias);
        return first;
    }
    extend = MAX(bias, CHUNKSIZE);
    if((first = extend_heap(extend/WSIZE)) == NULL)
        return NULL;
    place(first, bias);
    return first;
}

/*
 * free
 */
void free(void *ptr) {
    if (ptr==0){
        return;
    }
    size_t size=GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(SUCC(ptr),0);
    PUT(PRED(ptr),0);
    coalesce(ptr);
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize, asize;
    void *newptr, *bp;

    if (size == 0) {
        free(oldptr);
        return NULL;
    }

    if (oldptr == NULL) {
        return malloc(size);
    }

    oldsize = GET_SIZE(HDRP(oldptr));
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if (oldsize >= asize) {
        // free the remaining bytes in this block
        if ((oldsize - asize) >= (2 * DSIZE)) {
            PUT(HDRP(oldptr), PACK(asize, 1));
            PUT(FTRP(oldptr), PACK(asize, 1));
            bp = NEXT_BLKP(oldptr);
            PUT(HDRP(bp), PACK(oldsize - asize, 0));
            PUT(FTRP(bp), PACK(oldsize - asize, 0));
            // need to coalesce this free block with next block if possible
            coalesce(bp);
        }
        return oldptr;
    } else {
        // need to allocate large block
        if ((newptr = malloc(size)) == NULL)
            return NULL;

        memcpy(newptr, oldptr, oldsize - 2 * WSIZE);
        free(oldptr);

        return newptr;
    }
}

/*
 * calloc
 */
void *calloc(size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    if ((newptr = malloc(bytes)) != NULL)
        memset(newptr, 0, bytes);
    return newptr;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {
    return (bool)lineno;
}

/* 
 * extend_heap
 * Extend the heap by `words` words. Return a pointer to the new free block on
 * success. Otherwise return NULL.
*/
// HINT: Make sure the heap size is properly aligned. Don't forget to coalesce
// free blocks.
static void *extend_heap(size_t words) {
    char* block;
    size_t size;

    if(words%2==0){
        size=words*WSIZE;
    }
    else{
        size=(words+1)*WSIZE;
    }

    if ((long)(block = mem_sbrk(size)) == -1)
        return NULL;


    PUT(HDRP(block), PACK(size, 0)); 
    PUT(FTRP(block), PACK(size, 0)); 
    PUT(SUCC(block),0);
    PUT(PRED(block),0);
    PUT(HDRP(NEXT_BLKP(block)), PACK(0, 1)); 

    return coalesce(block); 

}

/*
 * coalesce
 * Merge two adjacent free memory chunks, return the merged block.
*/
static void *coalesce(void *bp) {

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));                     

    /* Case 1 */
    if (prev_alloc && next_alloc) {
        return bp;
    }

    /* Case 2 */
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  
        PUT(HDRP(bp), PACK(size, 0));           
        PUT(FTRP(bp), PACK(size, 0));  
    }

    /* Case 3 */
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* Case 4 */
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
    }
    return bp;

}

/* First-fit search */
// Return the first fit block, if not find, return NULL

static void *find_fit(size_t asize) {
   void *p=heap_listp;
   while(GET_SIZE(HDRP(p))>0) {
       if (!GET_ALLOC(HDRP(p))&&(asize<=GET_SIZE(HDRP(p)))) {
           return p;
       }
       p=NEXT_BLKP(p);
   }
   return NULL; 
}


// Place the block
static void place(void *bp, size_t asize) {
    
    size_t total = GET_SIZE(HDRP(bp));
    size_t now_size = total - asize;

    if (now_size >= 16) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(now_size, 0));
        PUT(FTRP(bp), PACK(now_size, 0));
        PUT(PRED(bp),0);
        PUT(SUCC(bp),0);
    } else {
        PUT(HDRP(bp), PACK(total, 1));
        PUT(FTRP(bp), PACK(total, 1));
    }
}
