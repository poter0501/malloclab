/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* Basic contants and macros */
#define WSIZE 4             /* Word and header/footer size (byte) */
#define DSIZE 8             /* Double word size (byte) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (byte) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size | alloc))

/* Read and write a word at address p */
/* doyoung
argument p is usually (void*) pointer.
*/
#define GET(p) (*(unsigned int *)(p))      /* read a word at address p -> word is 4 byte, and int is also have same 4 byte size */
#define PUT(p, val) (*(unsigned int *)(p)) /* write a word at address p -> word is 4 byte, and int is also have same 4 byte size */

/* Read the size and allocated fields from address p */
/* doyoung
return the allocation bit or size of the header or footer block
~ is a bit operator. bit NOT operation. ex) ~0x7= ~111 = 000
p is a word that means 4byte and the last 3bit is a allocation bit and the other bits mean size of block
*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of it's header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

static char *heap_listp;
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
// static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
/* doyoung
Before using mm_malloc or mm_free function,
application have to initialize the heap using mm_init function
*/
int mm_init(void)
{
    /* doyoung
    1. Get the 4 word from the memory system and then initialze that for empty available list
    2. Call extend_heap, so the size of heap is extend at CHUNKSIZE, and then create the init available blocks(Prologue header, Prologue footer, Epliogue footer)
    */
    /* Create the initial empty heap */
    if (((heap_listp = mem_sbrk(4 * WSIZE))) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    size_t asize;      /* Adjusted block size */
    size_t extenedize; /* Amount to extend heap if no fit */
    char *bp;
    /* Ignore spurious request */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead andn alignment reqs. */
    /* douyoung
     asize = size + headr/footer(overhead) -> size + 2 word
     and then round to close alignment size.
    */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extenedize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extenedize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/* doyoung
extend_heap 함수는 두가지의 경우에 호출된다.
1. 힙이 초기화될 떄
2. mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때,
정렬을 유지하기 위해서 요청한 크기를 인접 2워드의 배수(8 byte)로 반올림하여, 메모리 시스템에 추가적인 공간 요청
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    /* doyoung
    Case 1: both prev and next are allocated block.
    Case 2: prev is allocated block and next is free block
    Case 3: prev is free block and next is allocated block
    Case 4: both prev and next are free block
    */
    if (prev_alloc && next_alloc) /* Case 1 */
    {
        return bp;
    }
    else if (prev_alloc && !next_alloc) /* Case 2 */
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) /* Case 3 */
    {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else /* Case 4 */
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(FTRP(NEXT_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}
/* first fit */
static void *find_fit(size_t asize)
{
    char *curr = heap_listp - WSIZE;
    size_t size = GET_SIZE(curr);
    while (FTRP(curr) < mem_sbrk)
    {
        if (!GET_ALLOC(HDRP(curr)))
        {
            if (GET_SIZE(HDRP(curr)) >= asize)
            {
                printf("asize = {%d}", asize);
                return HDRP(curr);
            }
        }
        else
        {
            curr +=size;
            size = GET_SIZE(HDRP(curr));
        }
    }
    return NULL;
}
/*  */
static void place(void *bp, size_t asize)
{
    
}