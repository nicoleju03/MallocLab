/*
 * mm.c -  Simple allocator based on implicit free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has 4-byte header and 4-byte footer of the form:
 *
 *     16            1   0
 *      -------------------
 *     | block_size | a/f |
 *      -------------------
 *
 * a/f is 1 if the block is allocated.
 *
 * Free blocks have the form:
 *
 * | header | next | previous | ... | footer |
 *
 * where next represents a pointer to the next free block in the free list and previous represents a pointer to the previous free block in the free list.
 *
 *
 * Allocated blocks have the form:
 *
 * | header | payload | footer |
 *
 * The minimum block size is 24: 4 bytes for the header, 8 bytes for the next pointer, 8 bytes for the previuos pointer, and 4 bytes for the footer.
 *
 *
 * The heap has the form:
 *
 * | padding (4) | prologue header (4) | prologue footer (4) |   ...   | epilogue header (4) |
 *                                      ^                     ^
 *                                   heap_listp              free_listp
 *
 * The padding guarantees that the first payload will start at an aligned boundary.
 *
 *
 * Lastly, the free list has the form:
 *
 * | NULL | <-- free block 1 --> | <-- free block 2 --> | ... | <-- free block n --> | NULL |
 *         ^
 *         free_listp
 *
 * where the arrows represent the next and previous free blocks in the list.
 * The first free block in the list is represented by a block with a NULL previous pointer. The last block in the list is represented by a block with a NULL next pointer.
 * The free_listp points to the first free block in the list (points to the spot right after the header).

 */
#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Your info */
team_t team = {
    /* First and last name */
    "Nicole Ju",
    /* UID */
    "605691503",
    /* Custom message (16 chars) */
    "no more",
};

//global variables
static char *heap_listp = NULL;
static char *free_listp = NULL;
static char *seg_arrayp = NULL;


/* define macros */
#define WSIZE 4
#define DSIZE 8
#define SEG_ARRAY_SIZE 32 //idk

#define MAX(x,y) ((x) > (y)? (x):(y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fileds from address p*/
#define GET_SIZE(p) (GET(p) &~0x7)
#define GET_ALLOC(p) (GET(p) &0x1)
//#define GET_ALLOC_PREV(p) (GET(p) &0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//#define NEXT_FREEP(ptr)  (*(char **)((char *)(ptr) + DSIZE))
//#define PREV_FREEP(ptr)  (*(char **)((char * )(ptr)))
#define NEXT_FREEP(bp)  (*(char **)(bp))
#define PREV_FREEP(bp)  (*(char **)(bp + DSIZE))


typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0];
    } body;
} block_t;

/* This enum can be used to set the allocated bit in the block */
enum block_state { FREE,
                   ALLOC };

#define CHUNKSIZE (1 << 16) /* initial heap size (bytes) */
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t)) /* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (24) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */

/* Global variables */
static block_t *prologue; /* pointer to first block */

/* function prototypes for internal helper routines */
//static void *extend_heap(size_t words);
//static void place(void *bp, size_t asize);
//static void *find_fit(size_t asize);
//static void *coalesce(void *bp);
//static void printblock(void *bp);
//static void checkblock(void *bp);
//void mm_checkheap(int verbose);

/* function prototypes for internal helper routines */
static block_t *extend_heap(size_t words);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);


static void addfree(void* fp);
static void removefree(void* fp);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
    //create the initial empty heap
    if((heap_listp = mem_sbrk(WSIZE<<2)) == (void*)-1)
        return -1;
    PUT(heap_listp, 0); //padding
    //heap_listp += SEG_ARRAY_SIZE;
    PUT(heap_listp + (WSIZE), PACK(DSIZE,1)); //prologue header
    PUT(heap_listp + (DSIZE), PACK(DSIZE,1)); //prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); //epilogue
    heap_listp += (DSIZE);
    
    //extend empty heap with free block of CHUNKSIZE bytes
    if(extend_heap(CHUNKSIZE/WSIZE)==NULL)
        return -1;
    
    //set free_listp to point to the first free block
    free_listp = heap_listp + DSIZE;
    //set previous and next pointers to null
    PREV_FREEP(free_listp) = NULL;
    NEXT_FREEP(free_listp) = NULL;
    
    return 0;
    
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
    size_t asize; //adjusted block size
    size_t extendsize; //amt to extend heap if no fit
    char *bp;
    
    //ignore spurious requests
    if (size==0)
        return NULL;
    
    //adjust block size to include overhead and alignment reqs
    if (size<=DSIZE<<1)
        asize = MIN_BLOCK_SIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/DSIZE);
    
    //search free list for a fit
    if ((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }
    
    //no fit found. get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    
    place(bp,asize);
    //mm_checkheap(1);
    return bp;

}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *payload) {
    size_t size = GET_SIZE(HDRP(payload));
    PUT(HDRP(payload),PACK(size,0));
    PUT(FTRP(payload), PACK(size,0));
    coalesce(payload); //coalesce updates the free list
    
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void *mm_realloc(void *ptr, size_t size) {
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    block_t* block = ptr - sizeof(header_t);
    copySize = block->block_size;
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose) {
    void *bp = heap_listp - WSIZE; //at the prologue
    
    //check prologue
    if(GET_SIZE(bp) != DSIZE || GET_SIZE(bp+WSIZE) != DSIZE || !GET_ALLOC(bp) || !GET_ALLOC(bp+WSIZE)){
        printf("Bad prologue\n");
    }
    checkblock(bp);
    
    int actualnumfree = 0;
    //check each of the blocks after the prologue
    for(bp = heap_listp + DSIZE; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){
        checkblock(bp);
        //check coalescing
        if(!GET_ALLOC(HDRP(bp))){
            actualnumfree++;
            if(PREV_BLKP(bp)!=NULL && !(GET_ALLOC(HDRP(PREV_BLKP(bp)))) ){
                printf("Error: Coalescing Issue\n");
            }
            if(NEXT_BLKP(bp)!=NULL && !(GET_ALLOC(HDRP(NEXT_BLKP(bp)))) ){
                printf("Error: Coalescing Issue\n");
            }
                
        }
    }
    
    int numinfreelist = 0;
    //check the free list
    void* fp;
    for (fp = free_listp; fp!=NULL ; fp = NEXT_FREEP(fp)){
        numinfreelist++;
       // make sure the blocks in the free list are valid
        checkblock(fp);
        //make sure the blocks in the free list are free
        if(GET_ALLOC(HDRP(fp))){
            printf("Error: A block in the free list is not free\n");
        }
        
    }
    if(actualnumfree != numinfreelist){
        printf("Error: Number of free blocks does not match number in free list\n");
    }
    
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words) {
    char *bp;
    size_t size;
    // Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ( (long)(bp = mem_sbrk(size)) == -1 )
        return NULL;
        
    // Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size,0)); // Free block header
    PUT(FTRP(bp), PACK(size,0)); // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // New epilogue header
        
    //Coalesce if the previous block was free
    return coalesce(bp);
    
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(block_t *block, size_t asize) {
   // mm_checkheap(1);
    void* bp = (void*)(block);
    size_t og_size = GET_SIZE(HDRP(bp));
    size_t split_size = GET_SIZE(HDRP(bp)) - asize;
    //remove free block from free list
    //removefree(bp);
    
    if (split_size >= MIN_BLOCK_SIZE){
        void* prev = PREV_FREEP(bp);
        void* next = NEXT_FREEP(bp);
        
        //split the block by updating the header and marking it allocated
        PUT(HDRP(bp),PACK(asize,1));
        //set footer of allocated block
        PUT(FTRP(bp),PACK(asize,1));
        //update header of new free block
        PUT(HDRP(NEXT_BLKP(bp)), PACK(split_size,0));
        //update footer of new free block
        PUT(FTRP(NEXT_BLKP(bp)),PACK(split_size,0));
        
        
        if(next == NULL && prev == NULL){
            free_listp = NEXT_BLKP(bp);
            NEXT_FREEP(NEXT_BLKP(bp)) = NULL;
            PREV_FREEP(NEXT_BLKP(bp)) = NULL;
        }
        else{
            if(prev==NULL){
                free_listp = NEXT_BLKP(bp);
                PREV_FREEP(NEXT_BLKP(bp)) = prev;
            }
            if (prev!=NULL){
                NEXT_FREEP(prev) = NEXT_BLKP(bp);
                PREV_FREEP(NEXT_BLKP(bp)) = prev;
            }
            if(next==NULL){
                NEXT_FREEP(NEXT_BLKP(bp)) = next;
            }
            if(next != NULL){
                PREV_FREEP(next) = NEXT_BLKP(bp);
                NEXT_FREEP(NEXT_BLKP(bp)) = next;
            }
        }
       //add the free block to the free list
        
     //   coalesce(NEXT_BLKP(bp));
    }
    else{
        removefree(bp);
        PUT(HDRP(bp),PACK(og_size,1));
        PUT(FTRP(bp),PACK(og_size,1));
    }
    
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static block_t *find_fit(size_t asize) {
//    size_t sizeclass = size_t asize/32;
//    if(sizeclass > (SEG_ARRAY_SIZE-1)){
//        sizeclass = SEG_ARRAY_SIZE-1;
//    }
//
//    void* ptr;
//    for(ptr = seg_arrayp + (DSIZE * sizeclass); ptr = NEXTFREEP(ptr)){
//        if(asize<GET_SIZE(HDRP(ptr))){
//            return (block_t*)(ptr);
//        }
//    }
    
    /* first fit search */
    void* fp;
    for(fp=free_listp; fp != NULL; fp = NEXT_FREEP(fp)){
        if(asize <= GET_SIZE(HDRP(fp)) ){
            return (block_t*)(fp);
        }
    }
    
    return NULL;
    
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static block_t *coalesce(block_t *block) {
    void* bp = (void*)(block);
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
        
    if(prev_alloc && next_alloc){
        addfree(bp);
        return (block_t*)(bp);
    }
        
        else if (prev_alloc && !next_alloc) { //prev allocated, next free
            size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
            //remove next free block from free list
            removefree(NEXT_BLKP(bp));
            PUT(HDRP(bp), PACK(size, 0));
            PUT(FTRP(bp), PACK(size, 0));
            //add the coalesced free block to the free list
            addfree(bp);
        }
        
        else if (!prev_alloc && next_alloc) { //prev free, next allocated
            size += GET_SIZE(HDRP(PREV_BLKP(bp)));
            //remove prev block from free list
            removefree(PREV_BLKP(bp));
            bp = PREV_BLKP(bp);
            PUT(HDRP(bp), PACK(size, 0));
            PUT(FTRP(bp), PACK(size, 0));
            //add the coalesced free block to the free list
            addfree(bp);
        }
        
        else {  //both free
            size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
            //remove the prev and next blocks from the free list
            removefree(PREV_BLKP(bp));
            removefree(NEXT_BLKP(bp));
            bp = PREV_BLKP(bp);
            PUT(HDRP((bp)), PACK(size, 0));
            PUT(FTRP((bp)), PACK(size, 0));
            //add coalesced free block to the free list
            addfree(bp);
        }
        return (block_t*)(bp);
}

static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t *block) {
    void* bp = (void*)(block);
    size_t hsize, halloc, fsize, falloc;
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));
    
    if(hsize == 0){
        printf("%p: EOL\n",bp);
        return;
    }
//    uint32_t hsize, halloc, fsize, falloc;
//
//    hsize = block->block_size;
//    halloc = block->allocated;
//    footer_t *footer = get_footer(block);
//    fsize = footer->block_size;
//    falloc = footer->allocated;
//
//    if (hsize == 0) {
//        printf("%p: EOL\n", block);
//        return;
//    }
//
    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(block_t *block) {
    void* bp = (void*)(block);
    if(bp == NULL){
        return;
    }
    if(GET_SIZE(HDRP(bp))%8){
        printf("Error: payload for block at %p is not aligned\n",bp);
    }
    if(GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))){
        printf("Error: header size does not match footer\n");
    }
    if(GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))){
        printf("Error: header allocation status does not match footer\n");
    }
    if(bp<mem_heap_lo() || bp > mem_heap_hi()){
        printf("Error: block is outside the heap\n");
    }
    if(GET_SIZE(HDRP(bp)) > mem_heapsize()){
        printf("Error: block is bigger than heap size\n");
    }
    
//    if ((uint64_t)block->body.payload % 8) {
//        printf("Error: payload for block at %p is not aligned\n", block);
//    }
//    footer_t *footer = get_footer(block);
//    if (block->block_size != footer->block_size) {
//        printf("Error: header does not match footer\n");
//    }
}

//remove free block fp from the free list
static void removefree(void* fp){
    void* prev = PREV_FREEP(fp);
    void* next = NEXT_FREEP(fp);
    
    if(free_listp == NULL){
        return;
    }
    else if(prev==NULL && next==NULL){
        free_listp = NULL;
    }
    else if(prev == NULL){
        //then it is the root
        free_listp = next;
        PREV_FREEP(free_listp) = NULL;
    }
    else if(next==NULL){
        NEXT_FREEP(prev) = NULL;
    }
    else{
        //change the previous free block's next pointer to the current block's next
        NEXT_FREEP(prev) = next;
        //change next free block's previous pointer to current block's prev
        PREV_FREEP(next) = prev;
    }
}

//add a free block to the beginning of the free list
static void addfree(void* fp){
    if(free_listp==NULL){
        free_listp = fp;
        NEXT_FREEP(fp) = NULL;
        PREV_FREEP(fp) = NULL;
    }
    //set next and prev of free block to be added
    else{
        NEXT_FREEP(fp) = free_listp;
        PREV_FREEP(fp) = NULL;
        
        //change the pointers for the head of the list
        PREV_FREEP(free_listp) = fp;
        free_listp = fp;
    }
    
}

