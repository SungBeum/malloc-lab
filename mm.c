/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
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
    "malloc-lab team1",
    /* First member's full name */
    "An Sung Beum",
    /* First member's email address */
    "an4126@gmail.com",
    /* Second member's full name (leave blank if none) */
    "Cho Min Ki",
    /* Second member's email address (leave blank if none) */
    
    /* third member's full name (leave blank if none) */
    "Lim Hye Jung",
    /* third member's email address (leave blank if none) */
    
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


// 추가내용 - 가용 리스트 조작을 위한 기본 상수와 매크로
// 기본 size 상수를 정의
// 워드 크기
#define WSIZE 4
// 더블워드
#define DSIZE 8
// 초기 가용 블록과 힙 확장을 위한 기본 크기
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴
#define PACK(size, alloc) ((size) | (alloc))

// 인자 p가 참조하는 워드를 읽어서 리턴
#define GET(p)      (*(unsigned int *)(p))
// 인자 p가 가리키는 워드에 val을 저장
#define PUT(p, val) (*(unsigned int *)(p) = (val))
// 각각 주소 p에 있는 헤더 또는 풋터의 size와 할당 비트를 리턴
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)
// 각각 블록 헤더와 풋터를 가리키는 포인터를 리턴
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *){bp} + GET_SIZE(HDRP(bp)) - DSIZE)
// 다음과 이전 블록의 블록 포인터를 각각 리턴
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))
static void *coalesce(void *bp);


// 새 가용 블록으로 힙 확장하는 extend_heap 함수
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    // 인접 2워드의 배수(8배수)로 반올림하며, 그 후에 메모리 시스템으로부터 추가적인 힙공간을 요청한다
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE ;
    // mem_sbrk로의 모든 호출은 에필로그 블록의 헤더에 이어서 더블 워드 정렬된 메모리 블록을 리턴한다
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    // 이 헤더는 가용 블록의 헤더가 되고
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // 이 블록의 마지막 워드는 새 에필로그 블록 헤더가 된다
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
    // 이전 힙이 가용 블록으로 끝났다면, 두 개의 가용 블록을 통합하기 위해 coalesce 함수를 호출한다
    return coalesce(bp);
}
/* 
 * mm_init - initialize the malloc package.
 */
//  find-fit 함수에서 써야하므로, 전역변수 선언
static char *heap_listp;
int mm_init(void)
{   
    // 메모리시스템에서 4워드를 가져와서 빈 가용 리스트를 만들 수 있도록 이들을 초기화한다
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    // heap_list 에 16바이트의 크기가 있느냐 를 묻는 if문
    return -1;
    // 힙 패딩영역 ( 시작 영역 )
    PUT(heap_listp, 0);
    // 프롤로그의 헤더  ( PACK == 비트연산 )
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    // 프롤로그의 풋터
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    // 에필로그의 헤더
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    // 프롤로그의 헤더와 풋터사이에서 기준잡으려고 2워드 이동
    heap_listp += (2*WSIZE);
    // 힙을 CHUNKSIZE 바이트로 확장하고 초기 가용 블록을 생성한다
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *find_fit(size_t asize)
{
    char *bp = heap_listp + DSIZE;
    size_t size = GET_SIZE(bp);
    size_t state = GET_ALLOC(bp);
    while (size != 0)
    {
        bp -= WSIZE;
        if (state == 1 && size >= asize)
        {
            return bp + WSIZE;
        }
        bp += asize;
    }
    return NULL;
}
static void place(void *bp, size_t asize)
{
    size_t origin_size = GET_SIZE(bp);
    if (origin_size - asize >= 2*DSIZE)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp+asize-WSIZE), PACK(asize, 1));
        PUT(HDRP(bp+asize), PACK(origin_size-asize, 0));
        PUT(FTRP(bp+asize), PACK(origin_size-asize, 0));
    }
    else 
    {
        PUT(HDRP(bp), PACK(origin_size, 1));
        PUT(FTRP(bp+origin_size-WSIZE), PACK(origin_size, 1));
    }
    // return 0;
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
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
    {
        return NULL;
    }
    // 최소 16바이트 크기의 블록을 구성 (8바이트는 정렬 요건을 만족시키기 위해, 추가적인 8바이트는 헤더와 풋터 오버헤드를 위해서)
    if (size <= DSIZE)
    {
        asize = 2*DSIZE;
    }
    // 8바이트를 넘는 요청에 대해
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    // 할당기가 요청한 크기를 조정한 후 적절한 가용 블록을 가용 리스트에서 검색한다
    if ((bp = find_fit(asize)) != NULL)
    {   // 만약 맞는 블록을 찾으면 요청한 블록 배치, 초과부분 분할
        place(bp, asize);
        return bp;
    }
    // 만약 맞는 블록을 찾지 못하면, 새로운 가용 블록으로 확장
    extendsize = MAX(asize, CHUNKSIZE);
    // 더이상 늘릴 수 없을때
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    {
        return NULL;
    }
    // 필요하다면, 블록을 분할
    place(bp, asize);
    return bp;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc)
    {
        /* case 1 */
        return bp;
    }
    else if (prev_alloc && !next_alloc) 
    {
        /* case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        /* case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    {
        /* case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
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