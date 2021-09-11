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
    "8-Jo",
    /* First member's full name */
    "Roegan Kim",
    /* First member's email address */
    "Roegan.kim@gmail.com",
    /* Second member's full name (leave blank if none) */
    "HoDoll Kim",
    /* Second member's email address (leave blank if none) */
    "unalloacted"};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* ------------------------------------------------------------------ */

/* CSAPP figure 9.43 */

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes 단위)  */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this (12) amount (bytes) heap의 초기 사이즈 설정용 */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word / 헤더와 푸터에 넣기전 블록 크기와, 할당,가용 여부를 합친다 */
#define PACK(size, alloc) ((size) | (alloc)) /* or | 비트 연산자 */

/* Read and write a word at address p */
/* 함수형 매크로 */
#define GET(p) (*(unsigned int *)(p))              /* 인자 p가 참조하는 워드를 읽고 리턴. */
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* 인자 p가 가리키는 워드에 val을 저장 */

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) /* 주소 p에 있는 헤더 혹은 푸터의 size를 리턴 16진수로 4비트 이상부터 = ~0x7 */
#define GET_ALLOC(p) (GET(p) & 0x1) /* 헤더 혹은 푸터의 alloc(할당,가용 비트)를 리턴 */

/* Given block ptr bp, compute address of its header and footer */
/* 각각 블록포인터가 주어지면, 블록 헤더와 풋터를 가르키는 포인터를 리턴 */
#define HDRP(bp) ((char *)(bp)-WSIZE)                        /**/
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /**/

/* Given block ptr bp, compute address of its next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) /**/
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   /**/

/* 함수 선언*/
static char *heap_listp;
static void *find_fit(size_t asize);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
// int mm_init(void);
// void *mm_malloc(size_t size);
// void *mm_realloc(void *ptr, size_t size);

/* mm_init - initialize the malloc package.*/
int mm_init(void)
{
    /* Create the initial empty heap */
    /* 메모리 시스템에서 4워드를 가져온다. 가상메모리 구현까지는 libc의 malloc을 사용한다. (memlib.c init 참조)*/

    // 어디서 선언됐지?
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    /* 동적할당기를 위한 초기화. 빈 가상 메모리 가용 리스트 만들기 */

    /* PUT(p, val) 인자 p가 가르키는 워드에 val 저장 */
    PUT(heap_listp, 0); /* Alignment padding */
    /* Prolog block consist 2 word, header, footer, therefore size == DSIZE */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prolog header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prolog footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */

    heap_listp += (2 * WSIZE); /* prolog footer 의 시작을 가리킨다. */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    /* chunksize는 byte 단위로, wsize로 나누면 워드 단위로 바뀐다. */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    /* sbrk는 size로 음수가 주어지거나, 가상메모리 공간을 초과할 경우 -1을 retrun */
    /* 성공적일 경우, brk ptr에 incr 즉 size를 더해주고, 더하기 이전 주소를 return */
    /* mm_init()에서 한번 콜된 sbrk 덕분에 mem_brk가 새로운 top을 가르키고 있다. */
    /* 그렇기에 sbrk가 다시 콜되면 올바르게 힙이 커진다. 그리고 bp에는 return된 old brk가 대입된다.*/
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilouge header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilouge header */

    /* coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* ignore spurious request */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment requests */
    /* 삽입하려는 데이터 크기(size)를 정렬 기준에 따라 조절한 값을 asize에 담아준다.*/
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    /* 적절한 가용 블록이 없다면 find_fit은 NULL을 리턴 */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

    /* old ver */
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

/* 묵시적 가용리스트에서 first fit 검색을 수행 */
static void *find_fit(size_t asize)
{
    /* first fit search */
    void *bp;

    /* heap_listp 는 시작 포인트, prolog의 header 다음을 가르키고 있다. */
    /* GET_SIZE(HDRP(bp)) 가 0보다 작을 경우는 epilouge block을 만났을 때다.*/
    /* for문의 스탭마다 bp를 다음 블록으로 옮긴다. */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        /* free block 이고, asize 가 들어갈 수 있다면*/
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }

    return NULL; /* no fit */
}

/* ? */
static void place(void *bp, size_t asize)
{
    /* 현재 가용 블록의 크기 c(urrent)ize */
    size_t csize = GET_SIZE(HDRP(bp));

    /* csize와 asize의 차이가 2*Dsize 보다 크다면, 새로운 블록을 만들 공간이 되기에 */
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        /* 새 가용 블록 생성  */
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    /* 남는 공간이 새 블록을 만들기 부족하다면, */
    else
    {
        /* cszie를 size로 배정한다. 1 워드 정도 차이가 난다면 이는 padding 워드가 된다. */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1 : prev & next all alloc */
    if (prev_alloc && next_alloc)
        return bp;

    /* case 2 : prev  alloc & next free */
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(bp), PACK(size, 0));
        /* def FTRP에 get_size(HDRP(bp))가 포함되어있기에 HDRP 이후 바로 FTRP 가능 */
        PUT(FTRP(bp), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }
    /* case 3 : prev free & next alloc */
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        /*  */
        bp = PREV_BLKP(bp);
    }
    /* case 4 : prev free & next free */
    else
    {
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    /* equivalent to mm_free(ptr). if size <= 0 */
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }

    /* equivalent to mm_malloc(size). if bp == NULL */
    if (bp == NULL)
    {
        return mm_malloc(size);
    }

    /* re-allocation begin  */
    /* 새롭게 요청된 size에 맞는 블록을 할당해준다. */
    void *newp = mm_malloc(size); //new pointer.

    if (newp == NULL)
    {
        return 0;
    }

    size_t oldsize = GET_SIZE(HDRP(bp));

    if (size < oldsize)
    {
        oldsize = size; //shrink size.
    }
    /* 메모리의 값을 복사하는 함수 memcpy */
    /* 1st 인자: 복사받을 메모리를 주소 */
    /* 2nd 인자: 복사할 메모리를 주소 */
    /* 3rd 인자: 복사할 메모리 길이 (bytes) */

    /* 원래 블록을 새롭게 할당한 블록에 복사해준다. */
    memcpy(newp, bp, oldsize); //cover.

    /* 원 메모리를 해제해준다*/
    mm_free(bp);
    return newp;

    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;

    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //     return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // if (size < copySize)
    //     copySize = size;
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;
}
