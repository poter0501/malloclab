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
#define GET(p) (*(unsigned int *)(p))              /* read a word at address p -> word is 4 byte, and int is also have same 4 byte size */
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* write a word at address p -> word is 4 byte, and int is also have same 4 byte size */

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

#define SUCC_BP(bp) (char **)(bp + WSIZE)
#define PRED_BP(bp) (char **)(bp)

static char *heap_listp;
static char *heap_last;
static char *heap_last_old;
static char *free_block_last;
// static char *free_last;
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *add_free_list(void *bp);
static void *del_free_list(void *bp);

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
    if (((heap_listp = mem_sbrk(6 * WSIZE))) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), 0);                  /* Prologue header */
    PUT(heap_listp + (3 * WSIZE), 0);                  /* Prologue header */
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         /* Epilogue header */
    heap_listp += WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
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

    // printf("mem_heap_hi = %x, mem_heap_lo = %x , mem_heap_size = %x\n",
    //        (unsigned int *)mem_heap_hi() + 1, (unsigned int *)mem_heap_lo(), (unsigned int *)mem_heapsize());
    heap_last_old = heap_last;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    heap_last = HDRP(NEXT_BLKP(bp));
    // printf("mem_heap_hi = %x, mem_heap_lo = %x , mem_heap_size = %x\n",
    //        (unsigned int *)mem_heap_hi() + 1, (unsigned int *)mem_heap_lo(), (unsigned int *)mem_heapsize());

    // 가용 블럭이 없는 경우 프롤로그 블럭의 succ가 에필로그 블록을 가르키고 있게 한다.
    if (GET(heap_listp + DSIZE) == (unsigned int *)heap_last_old || GET(heap_listp + DSIZE) == NULL)
    {
        PUT(heap_listp + DSIZE, (unsigned int *)heap_last);
    }
    /* 가용 블럭 리스트의 마지막 블럭의 succ를 새로 갱신된 에필로그 블럭의 주소로 갱신 */
    unsigned int *curr = GET(heap_listp + DSIZE);
    // if (curr != (unsigned int *)heap_last) /* free block list 가 null이 아닐 경우 */
    // {
    //     unsigned int *succ = GET(curr + 2);
    //     while (succ != (unsigned int *)heap_last_old)
    //     {
    //         curr = succ;
    //         succ = GET(curr + 2);
    //     }
    //     PUT(curr + 2, (unsigned int *)heap_last);
    // }
    if (free_block_last != NULL)
    {
        unsigned int *last = free_block_last;
        unsigned int *succ = GET(last + 2);
        if (succ == heap_last_old)
        {
            PUT(last+2, (unsigned int *)heap_last);
        }
    }

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
        add_free_list(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) /* Case 2 */
    {
        del_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        // del_free_list(bp);
    }
    else if (!prev_alloc && next_alloc) /* Case 3 */
    {
        del_free_list(PREV_BLKP(bp));
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // del_free_list(bp);
    }
    else /* Case 4 */
    {
        del_free_list(NEXT_BLKP(bp));
        del_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // del_free_list(bp);
    }

    add_free_list(bp);
    return bp;
}
/* first fit */
static void *find_fit(size_t asize)
{
    unsigned int *curr = GET(heap_listp + DSIZE);
    if (curr == (unsigned int *)heap_last)
        return NULL;

    for (curr; GET_ALLOC(curr) == 0; curr = GET(curr + 2))
    {
        if (GET_SIZE(curr) >= asize)
            return curr + 1;
    }

    return NULL;
}
/*  */
static void place(void *bp, size_t asize)
{
    size_t total_size = GET_SIZE(HDRP(bp));
    size_t empty_size = total_size - asize;

    if (empty_size >= 2 * DSIZE)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        del_free_list(bp);

        // PUT(HDRP(NEXT_BLKP(bp)) + WSIZE, (unsigned int*)(HDRP(bp) + WSIZE));
        // PUT(HDRP(NEXT_BLKP(bp)) + DSIZE, (unsigned int*)(HDRP(bp) + DSIZE));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(empty_size, 0));
        PUT(FTRP(bp), PACK(empty_size, 0));
        add_free_list(bp);
        return;
    }
    PUT(HDRP(bp), PACK(total_size, 1));
    PUT(FTRP(bp), PACK(total_size, 1));
    del_free_list(bp);
}
static void *add_free_list(void *bp)
{
    unsigned int *curr = GET(heap_listp + DSIZE);
    if (curr == NULL || curr == (unsigned int *)heap_last)
    {
        PUT(heap_listp + DSIZE, (unsigned int *)HDRP(bp));
        PUT(HDRP(bp) + WSIZE, (unsigned int *)heap_listp);
        PUT(HDRP(bp) + DSIZE, heap_last);
        free_block_last = HDRP(bp);
        return;
    }

    unsigned int *temp = GET(curr + 2);
    while (GET_ALLOC(curr) == 0) /* 위치를 찾아가 삽입 */
    {
        if (curr < HDRP(bp)) /* curr -> new(bp) */
        {
            temp = curr;
            curr = GET(curr + 2);

            if (curr == heap_last)
            {
                PUT(temp + 2, (unsigned int *)HDRP(bp));
                PUT(HDRP(bp) + WSIZE, temp);
                PUT(HDRP(bp) + DSIZE, heap_last);
                free_block_last = HDRP(bp);
                return;
            }
        }
        else /* new(bp) -> curr */
        {
            unsigned int *pred = GET(curr + 1);
            if (pred == (unsigned int *)heap_listp) /* start -> new -> curr */
            {
                PUT(heap_listp + DSIZE, (unsigned int *)HDRP(bp));
                PUT(HDRP(bp) + WSIZE, (unsigned int *)heap_listp);
                PUT(HDRP(bp) + DSIZE, curr);
                if (curr != heap_last)
                    PUT(curr + 1, (unsigned int *)HDRP(bp));
                else
                    free_block_last = HDRP(bp);

                return;
            }
            else /*  pred -> new -> curr */
            {
                PUT(pred + 2, (unsigned int *)HDRP(bp));
                PUT(HDRP(bp) + WSIZE, pred);
                PUT(HDRP(bp) + DSIZE, curr);
                if (curr != heap_last)
                    PUT(curr + 1, (unsigned int *)HDRP(bp));
                else
                    free_block_last = HDRP(bp);

                return;
            }
        }
    }
}
static void *del_free_list(void *bp)
{
    unsigned int *curr = HDRP(bp);
    unsigned int *pred = GET(curr + 1);
    unsigned int *succ = GET(curr + 2);
    /*
    case 1: start -> curr -> last
    case 2: start -> curr -> succ
    case 3: pred -> curr -> last
    case 4: pred -> curr -> succ
    */
    if (pred == heap_listp && succ == heap_last) /* case 1 */
    {
        PUT(heap_listp + DSIZE, (unsigned int *)heap_last);
        PUT(curr + 1, 0);
        PUT(curr + 2, 0);
        free_block_last = NULL;
    }
    else if (pred == heap_listp && succ != heap_last) /* case 2 */
    {
        PUT(heap_listp + DSIZE, succ);
        PUT(succ + 1, (unsigned int *)heap_listp);
        PUT(curr + 1, 0);
        PUT(curr + 2, 0);
    }
    else if (pred != heap_listp && succ == heap_last) /* case 3 */
    {
        PUT(pred + 2, (unsigned int *)heap_last);
        PUT(curr + 1, 0);
        PUT(curr + 2, 0);
        free_block_last = pred;
    }
    else if (pred != heap_listp && succ != heap_last)
    {
        PUT(pred + 2, succ);
        PUT(succ + 1, pred);
        PUT(curr + 1, 0);
        PUT(curr + 2, 0);
    }
    else
    {
        printf("fault !!!!!\n");
    }
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;        /* Adjusted block size */
    size_t extendedsize; /* Amount to extend heap if no fit */
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
        size_t temp_size = GET_SIZE(HDRP(bp));
        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendedsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendedsize / WSIZE)) == NULL)
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

    copySize = GET_SIZE(HDRP(ptr));
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);

    if (copySize <= DSIZE)
        copySize = 2 * DSIZE;
    else
        copySize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}