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
    ""
};

#define WSIZE 4             // header/footer 사이즈 = 1 Word
#define DSIZE 8             // 더블워드 크기         = 2 Word
#define CHUNKSIZE (1<<6)   // 초기 가용블록과 힙 확장을 위한 기본 크기

#define MAX(x,y) ((x) > (y)? (x) : (y))

// size와 할당 비트(alloc) OR Header, Footer 에 들어갈 값 반환
#define PACK(size, alloc) ((size) | (alloc))    // Header : 사이즈를 PACK 한 후 word 안의 bit 할당  (size와 alloc을 비트연산)

// 주소 p에서 words를 읽기 / 쓰기
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (int)(val))

// 주소 p 로부터 size 를 읽고 fields들을 할당
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// 블록 ptr bp를 받고, 해당 블록의 Header와 Footer의 주소를 계산하기
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 블록 ptr bp를 받고, 그것의 이전&다음 블록들의 주소를 계산하기 (앞뒤로 가용 블럭 있는지 확인)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *) (bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *) (bp) - DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SUCC(bp) (*(char **)(bp + WSIZE)) // 다음 가용 블록의 주소
#define PRED(bp) (*(char **)(bp))         // 이전 가용 블록의 주소

#define CLASS_LEN 14

static char *size_class[CLASS_LEN];
static char *heap_listp;

/*
 * 블록 크기가 들어갈 수 있는 size_class의 idx 찾기
 */
static int get_cls_idx(size_t size)
{
    int i= 0;
    while(size >>= 1) i++;
    // -1 인덱스 보다 큰 size 는 모두 마지막 인덱스로
    return (i > CLASS_LEN-2) ? CLASS_LEN-1 : i;
}

/*
 * 가용블록 삭제 
 * Target 블록과 연결되어 있던 가용블록끼리 연결
 */
static void *remove_free(char *bp)
{
    // size_class 인덱스 찾기
    int idx = get_cls_idx(GET_SIZE(HDRP(bp)));

    // Target이 class ROOT 라면,
    if (bp == size_class[ idx ])
    {
        // 다음 블록을 ROOT 로 만들어주기
        size_class[ idx ] = SUCC(bp);

        // 다음 블록의 PRED 를 NULL 로 설정
        if(SUCC(bp)) PUT(SUCC(bp), NULL);

        /* 다음 블록이 없는 경우는 ROOT 만 존재했으므로 따로 설정해줄 필요 없음 */
    }
    // Target이 class list 중간에 있다면,
    else{
        // Target이 list 마지막 블록인 경우,
        if(SUCC(bp)) PUT(SUCC(bp), PRED(bp));       // 나의 이후를 나의 이전과 연결

        PUT(PRED(bp)+WSIZE, SUCC(bp));              // 나의 이전을 나의 이후와 연결
    }
}

/*
 * LIFO 방식으로 삽입
 */
static void *insert_free(char *bp)
{
    // size_class 인덱스 찾기
    int idx = get_cls_idx(GET_SIZE(HDRP(bp)));

    // 이전블록 : NULL 
    PUT(bp, NULL);

    // Target 의 class list 가 비어있다면,
    if(size_class[ idx ] == NULL)
        PUT(bp+WSIZE, NULL);               // 다음 가용블록은 NULL 이 된다.
    else{
        PUT(bp+WSIZE, size_class[ idx ]);  // 이전 첫번째 가용블록은 두번째 가용블록이 된다.
        PUT(size_class[ idx ], bp);        // 이전 첫번째 가용블록의 앞에는 새로운 가용블록이 세팅된다.
    }
    size_class[ idx ] = bp;

}

/* 
 * 가용블록 합치기
 * Param : 가용블록 주소
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    // Case 1. 이전블록 할당상태 & 다음블록 가용상태 --> (remove free 할 필요 없음)
    // Case 2. 이전블록 가용상태 & 다음블록 할당상태 --> 이전+현재
    if (prev_alloc && !next_alloc){
        remove_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // 헤더에 사이즈를 저장했기 때문에 해당 사이즈만큼 푸터를 이동시키므로 해당 블럭의 푸터는 새로 설정할 필요가 없다
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // Case 3. 이전블록 가용상태 & 다음블록 할당상태 --> 이전+현재
    else if (!prev_alloc && next_alloc){
        remove_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // Case 4. 이전블록 가용상태 & 다음블록 가용상태 --> 이전+현재+다음
    else if(!prev_alloc && !next_alloc)
    {
        remove_free(NEXT_BLKP(bp));
        remove_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_free(bp);
    return bp;
}

/* 
 * 새 가용블록으로 힙 확장
 * Param : word 개수
 */
static void *extend_heap(size_t words)
{
    // 할당된 메모리의 시작 포인터
    char *bp;
    size_t size;

    // 맞춤 fit 없어 정렬 유지위해 반올림 후에 추가적인 힙 공간 요청할 때 작동하는 함수
    size = (words % 2) ? (words + 1)*WSIZE : words* WSIZE;   // 홀수+1 * 4 || 짝수 * 4
    if((long)(bp = mem_sbrk(size)) == -1)                    // mem_sbrk 반환 포인터이므로 long형으로 캐스팅
        return NULL;
    
    // 새로운 가용 블록의 Header & Footer 주소 계산 로직
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 새로운 Epilogue 의 Header
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 가용블록 합치기
    return coalesce(bp);
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    for(int i = 1; i< CLASS_LEN; i++)
    {
        // i번째 class list의 ROOT를 초기화
        size_class[i] = NULL;
    }
    // 초기 빈 heap 생성
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // 함수 반환에 실패 할 때 관행적 처리 (void *) -1
        return -1;
        
    // PUT(주소 포인터, 값)
    PUT(heap_listp, 0);                             // Padding 정렬
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE*2, 1));  // Prologue - Header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE*2, 1));  // Prologue - Footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // Epilogoue - Footer

    // 확장을 통해 시작시 heap 을 한번 늘려주기
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
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
 * first fit : 처음부터 가용블록 탐색
   가용 블럭이 있는지 확인하는 절차
 */
static void *find_fit(size_t asize)
{
    void *bp;
    int size_class_idx = get_cls_idx(asize);

    for(int i = size_class_idx; i < CLASS_LEN; i++) {
        for (bp = size_class[ i ]; bp != NULL; bp=SUCC(bp))
        {
            // 가용블록인지 확인 && 가용블록 size에 요청 asize 가 fit 하다!
            if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))){
                return bp;
            }
        }
    } 
    // NOT Fit..
    return NULL;
}

static void place(void *bp, size_t asize)
{
    // 가용블럭의 크기
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free(bp);

    //  가용블록 패딩이 최소 블록 크기 (16)와 같거나 큰 경우에 분할 = 새로운 가용블록 만들 수 있음
    if( (csize-asize) >= (ALIGNMENT) )
    {
        // Header , Footer
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK((csize-asize), 0));
        PUT(FTRP(bp), PACK((csize-asize), 0));
        insert_free(bp);

    }else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * 
 * 가용 리스트에서 블록 할당 하기.
 * 
 * return bp
 */
void *mm_malloc(size_t size)
{
    size_t asize;               // 블록 size 조정 목적
    size_t extendsize;          // heap에 fit 한 블록이 없을 때, 확장을 위한 사이즈
    char *bp;

    // 리스트 탐색 전
    if (size == 0) return NULL; // 거짓된 요청 무시

    if (size <= DSIZE) asize = ALIGNMENT;       // alignment 요청으로 블록 size 조정 (최소 블록 크기 16 )
    else asize = ALIGN(size + SIZE_T_SIZE);     // overhead 한 요청으로 블록 size 조정 --> if) payload 8 넘는 요청 = block size는 16 초과

    // fit한 가용 리스트 찾기
    if ((bp = find_fit(asize)) != NULL){    
        place(bp,asize);
        return bp;
    }
    // fit 한 가용블럭 못 찾았다면, 메모리를 더 가져와 block을 위치
    extendsize = MAX(asize,CHUNKSIZE);

    if ((bp=extend_heap(extendsize/WSIZE)) == NULL) return NULL;   // extend_size : byte ,extend_heap : 워드 개수 

    place(bp,asize);
    return bp;

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

    copySize = GET_SIZE(HDRP(oldptr)); 
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}