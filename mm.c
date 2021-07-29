/*
 * mm.c
 *
 * Name: [Yao Xu]
 *
 * This malloc is implemented by segregated list and first fit algorithm in terms of finding free blocks
 * every block has a 8B header and a 8B footer
 * address of previous and next blk in seg list is stored in payload in each free list
 *credit:textbook
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h" 
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16
#define WSIZE 8
#define DSIZE 16
#define SEGLISTNUM 16
#define CHUNKSIZE (1 << 12)


/******************** Helper function ********************/

static size_t align(size_t x)            /* rounds up to the nearest multiple of ALIGNMENT*/
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

static size_t PACK(size_t size, size_t alloc)    // from text book, used to pack the infomation for header or footer
{
    return (size_t)(size | alloc);
}

static size_t GET(void *p)      // from text book, read a word at p
{
    return (*(size_t *)(p));
}

static void PUT(void *p, size_t val)      // from text book, write a word at p
{
    (*(size_t *)(p)) = val;
}

static void PUT_ADDRESS(void *p, void *val)      // same as PUT but a pointer should be passed in because we are using it to store an address
{
    (*(size_t *)(p)) = (size_t )val;
}

static size_t GET_SIZE(void *p)      // from text book, pass in a pointer pointing to the header or footer then return the size of this blk
{
    return GET(p) & ~0X7;
}

static size_t GET_ALLOC(void *p)      // from text book, pass in a pointer pointing to the header or footer then return if this blk is free or not
{
    return GET(p) & 0x1;
}

static size_t PREV_ALLOC(void *p)     // pass in a pointer pointing to the header or footer then return if previous blk in heap is free or not
{                                     // I am using the last bit for alloc info of this blk and using the second last bit for alloc info of previous blk
    return GET(p) & 0x2;
}

static char *HDRP(void *bp)           // from text book, Return address the first byte of a header
{
    return ((char *)(bp) - WSIZE);
}

static char *FTRP(void *bp)          // from text book, Return address the first byte of a footer
{
    return ((char *)(bp) + (GET_SIZE(HDRP(bp)) - DSIZE));
}


static char *N_ADD(void *bp)      // return address of where the address of "next" blk(in free list) stored
{                                   // I am using the first word in payload of a free blk to store the address of "next" blk in one free linked list
    return (char*)(bp);             // so this function is just cast the pointer to char* because bp is the address of where the address of "next" blk stored.
}

static char *P_ADD(void *bp)      // return address of where the address of "previous"(in free list) blk stored
{                                   // I am using the second word in payload of a free blk to store the address of "previous" blk in one free linked list
    return (char *)(bp) + WSIZE;    // so this function is just cast the pointer to char* then + 8B because bp+8B is the address of where the address of "previous" blk stored.
}

static char *NEXT_BLK(void *bp)    // from book, given blk ptr, compute address of next and previous blks(payload)
{
    return ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE));
}

static char *PREV_BLK(void *bp)
{
    return ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE));
}


/*********************************************************/

/* Global pointers */
static char *heap_listp = NULL;
static char *list_header_ptr = NULL;


/* function protocals */
void *coalesce(void *bp);
void *extend_heap(size_t words);
void addtoSeg(char *bp, size_t size);
int getlistNum(size_t size);
void *find (size_t size);
void *search (size_t startlist, size_t size);




/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{  
   
    if ((list_header_ptr = mem_sbrk(SEGLISTNUM * WSIZE)) == (void *)-1){  // first extend the heap to fit all roots for seglists to store the first blk addresses in each seglists
         return -1;                                                       // list_header_ptr is the first byte of the address of the first root
    }
   
    for (int i = 0; i < SEGLISTNUM; i++) {
         PUT_ADDRESS(list_header_ptr + (i * WSIZE), NULL);    // initialize the roots of seg lists to point to NULL because there is no free blk in them
    }
    
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1){   // following text book to initialize the heap
        return -1;
    }
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // alignment padding
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (3 * WSIZE), PACK(0, 2|1));   // Epilogue header
    
    heap_listp += 4 * WSIZE;
    
    // extend the empty heap with a free blk of chunksize bytes
    if (extend_heap(CHUNKSIZE) == NULL){
        return -1;
    }
    return true;
}


/*
 * extend_heap: called from malloc ot init to increase the heap
 */

void *extend_heap(size_t words)
{
    char *bp;
    
    if ((long) (bp = mem_sbrk(words)) < 0){                // bp is pointing to the next byte of heap_high which is the first byte of the new block payload
	      return NULL;                                       // so we have to use HDRP to find header position and then set it 
    }  
    
    PUT(HDRP(bp), PACK(words, PREV_ALLOC(HDRP(bp))));      //Setting the new block header
    PUT(FTRP(bp), GET(HDRP(bp)));                          //Setting the new block footer
                              
    addtoSeg(bp, words);                                   //add newly allocated blk to a free list which is fit for its size because we have to place it in malloc
    PUT(HDRP(NEXT_BLK(bp)), PACK(0, 1));                   //new epilogue header
    
    return coalesce(bp);                                   //try to coalesce
}


/*
 * addtoseg: pass in blk pointer and add this blk to be the first in the fit free list
 */


void addtoSeg(char *bp, size_t size)
{   
    char *first, *start;
    int id = getlistNum(size);  // calculate the seg list ID number that should be added to
    
    start = list_header_ptr + id*WSIZE;    // this is the root of the that fit free list
    first = (char *) GET(start);           // this is address of currrent first blk this free list
    
    if ( first == NULL )         // if this free list is empty, put bp in the root of this free list so that next and prev is pointing to null
    {    
         PUT_ADDRESS(start, bp);
         PUT_ADDRESS(N_ADD(bp), NULL); 
         PUT_ADDRESS(P_ADD(bp), NULL);
         
    } else {                    // if the free list is not empty, we add this free blk to the first of the free list
         PUT_ADDRESS(start, bp);
         PUT_ADDRESS(P_ADD(bp), NULL);
         PUT_ADDRESS(N_ADD(bp), first);
         PUT_ADDRESS(P_ADD(first), bp);
    }
}


/*
 * remfromseg: remove a list from a seg list
 */

void remfromSeg(char *bp, size_t size)
{
    char *next = (char *) GET(N_ADD(bp));    // address of next blk in seg list
    char *prev = (char *) GET(P_ADD(bp));
    
    int startinglist = getlistNum(size);      // calculate the seg list ID number that should be removed from
    
    if (prev == NULL && next != NULL) {                        // case1: this blk is the first blk in this seg list
      PUT_ADDRESS(list_header_ptr + startinglist*WSIZE, next); // put the address of second blk into the root of seg list
      PUT_ADDRESS(P_ADD(next), NULL);                          // set the previous blk of the new root to be null

    } else if (prev == NULL && next == NULL) {      
      PUT_ADDRESS(list_header_ptr + startinglist*WSIZE, NULL);     // case2: the empty seg list. 
      
    } else if (prev != NULL && next == NULL) {              // case3: blk is at the end of the seg list
      PUT_ADDRESS(N_ADD(prev), NULL);                       // set the previous blk's next to be NULL
      
    } else {                                        // case 4: previous's next is current's next; next's previous is current's previous
      PUT_ADDRESS(P_ADD(next), prev);    
	    PUT_ADDRESS(N_ADD(prev), next);

    }
}

/*
 * find: using sizeof blk to search a free blk
 */

void *find (size_t size)
{
     int i, startinglist= getlistNum(size);    // calculate the smallest seg list ID which its size can fit our request
     char *bp ;
     
     
     for (i = startinglist; i < SEGLISTNUM; i++) {    //search through all seg list whihch its ID is larger than "startinglist"
         if ((bp = search(i, size)) != NULL){
             
             return bp;  // if find one, return that blk
         }  
	   }
     return NULL;
}

/*
 * search:  search through a given seg list for free blk
 */

void *search (size_t startlist, size_t size)    
{

     char *current = (char *) GET( list_header_ptr + startlist*WSIZE ); // let current be the address of first blk in this list

     while (current != NULL){                  // we search through this list to find first fit free blk
         if (size <= GET_SIZE(HDRP(current)) ){
              
              break;
         } 
         current = (char *) GET(N_ADD(current)); // let current point to the next blk in this free list
         
     }
     return current;
}


/*
 * coalesce: try to coalesce the previous and next blk in heap
 */



void *coalesce(void *bp)
{
     size_t prev_alloc = PREV_ALLOC(HDRP(bp));          
     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLK(bp)));    // get if previous and next allocated or not
     size_t size = GET_SIZE(HDRP(bp));
     char *next, *prev, *prevheader, *nextheader;
     size_t prevsize, nextsize;
   
     
     if (prev_alloc && next_alloc) {      // if the previous and next are both allocated, we cannnot coalesce
         return bp;
         
     } else if (prev_alloc && !next_alloc) {    // if next is not allocated, we can coalesce
         next =  NEXT_BLK(bp);
  
         remfromSeg(bp, size);
         remfromSeg(next, GET_SIZE(HDRP(next))); // remove bp blk and next from their free lists
         
         size += GET_SIZE(HDRP(next));
         PUT(HDRP(bp), PACK(size, prev_alloc));
         PUT(FTRP(bp), PACK(size, prev_alloc));  // set this new large blk 's header and footer
         
         addtoSeg(bp, size);// add it to a free list
         return bp;
         
     }  else if (!prev_alloc && next_alloc) {   // if previous is not allocated, we can coalesce
         prev = PREV_BLK(bp);
         prevsize = GET_SIZE(HDRP(prev));
         
         remfromSeg(bp, size);
         remfromSeg(prev, prevsize);      // remove bp blk and last from their free lists
         
         size = size + prevsize;
         
         PUT(HDRP(prev), PACK(size, PREV_ALLOC(HDRP(prev))));
         PUT(FTRP(prev), GET(HDRP(prev)));            // set this new large blk 's header and footer
         addtoSeg(prev, size);      // add it to a free list
         
         return prev;
         
     } else {                // if the previous and next are both not allocated, we can coalesce
         prev = PREV_BLK(bp);
         prevheader = HDRP(prev);
         next = NEXT_BLK(bp);
         nextheader = HDRP(next);
         
         prevsize = GET_SIZE(prevheader);
         nextsize = GET_SIZE(nextheader);
         
         remfromSeg(bp, size);
         remfromSeg(prev, prevsize);
         remfromSeg(next, nextsize);        // remove bp blk and last and next from their free lists
         
         size += prevsize + nextsize;
         
         PUT(prevheader, PACK(size, PREV_ALLOC(prevheader)));
         PUT(FTRP(prev), GET(prevheader));      // set this new large blk 's header and footer
         addtoSeg(prev, size);      // add it to a free list
         
         return prev;
     }
     
}

/*
 * place: place a blk: remove a blk from seg list and split it if possible
 */


void place(void *bp, size_t asize)
{
    size_t rsize = GET_SIZE(HDRP(bp));
    size_t remainsize = rsize - asize;
    char *next = NEXT_BLK(bp);
    
    remfromSeg(bp, rsize); //remove bp blk from list
    
    if (remainsize >= 2*DSIZE) {    // if the real size - size is grater than 32 B and we split it into  two plk
	      PUT(HDRP(bp), PACK(asize, PREV_ALLOC(HDRP(bp)) | 1));    //reset the size and allocation bit
	      next = NEXT_BLK(bp);
	      PUT(HDRP(next), remainsize | 2);
	      PUT(FTRP(next), remainsize | 2); // set header and footer of the blk we splited
	      addtoSeg(next, remainsize); //add this newly splited blk to seg list
        
             
    } else {
	      PUT(HDRP(bp), PACK(rsize, PREV_ALLOC(HDRP(bp)) | 1));  // if the real size - size is smaller than 32 B and we don't split it into two plk
        PUT(HDRP(next), GET(HDRP(next)) | 2);  // set header and footer of the bp blk and next blk
      	if (!GET_ALLOC(HDRP(next)))
      	    PUT(FTRP(next), GET(HDRP(next)));
      }
  }





/*
 * malloc
 */
void* malloc(size_t size)
{
    
    
    size_t asize;
    char *bp;
    
    if (size <= 0){
	      return NULL;
    }
    
    asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE); // adjust the size to make it no less than 32 B

    
    if ((bp = find(asize)) != NULL) { // call find to find a free blk and then place it
        place(bp, asize);
	      return bp;
    }
    
 
    if ((bp = extend_heap(asize)) == NULL){ // if no fit free blk, extend the heap
        return NULL;
    }
    place(bp, asize);	

        
    return bp;
    
}


/*
 * free
 */
void free(void* ptr)
{  
    size_t size;
    char *next = NEXT_BLK(ptr);
    
    if (ptr == NULL){
         return;
    }
    size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), size | PREV_ALLOC(HDRP(ptr))); // set the ptr blk not allocated  for header, footer and next blk's header and footer
    PUT(FTRP(ptr), GET(HDRP(ptr)));
    PUT(HDRP(next), GET_SIZE(HDRP(next)) | GET_ALLOC(HDRP(next)));
    
    addtoSeg(ptr, size);     // add freed blk to seg list
    coalesce(ptr);          //try to coalesce
    
     
    
}



 
 
  
/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
  char *newadd;
    
    if ( oldptr == NULL ){    // if ptr is NULL, do malloc
         return malloc(size);
    }
    newadd = malloc(size);  //malloc for a new blk
    
    mem_memcpy(newadd, oldptr, size); //copy content to new blk

    free(oldptr);  //free the old blk

    return newadd;

}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}


int getlistNum(size_t size)
{
    int idx;
    
    if (size <= 32  ) {
       idx = 0;
    } else if (size <= 48) {
       idx = 1;
    } else if (size <= 64) {
       idx = 2;
    } else if (size <= 112) {
       idx = 3;
    } else if (size <= 160) {
       idx = 4;
    } else if (size <= 208) {
       idx = 5;
    } else if (size <= 512) {
       idx = 6;
    } else if (size <=1024) {
       idx = 7;
    } else if (size <= 2016) {
       idx = 8;
    } else if (size <= 4016) {
       idx = 9;
    } else if (size <=8016) {
       idx = 10;
    } else if (size <= 15360) {
       idx = 11;
    } else if (size <= 30720) {
       idx = 12;
    } else if (size <= 61440) {
       idx = 13;
    } else {
       idx = 14;
    }
    
    return idx;
 
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    /* IMPLEMENT THIS */
    
    //basic infos 
   dbg_printf("Heap low address is :%p, Heap high address is :%p At line %d\n ", mem_heap_lo(), mem_heap_hi(), lineno);
    char *bp;
    size_t free_count=0, free_count_heap=0;
    char *current_free_blk;
    
    
    // Is every blk marked as free in seg lists?
    //Do pointers in the free list point to valid free blks?
    
    for (int i=0; i<SEGLISTNUM; i++){
         current_free_blk = (char *) GET( list_header_ptr + i*WSIZE ); // let current be the address of first blk in this list
         while (current_free_blk != NULL){                  // we search through this list to find first fit free blk
             free_count = free_count+1;
             if ( GET_ALLOC(HDRP(current_free_blk)) == 1 ){      // if there is a blk which is allocated but still in free list, return false
                 dbg_printf("In seg list %d,  there is a blk is alloced at line %d\n", i, lineno);
                 return false;
             }
             if ( GET_SIZE(HDRP(current_free_blk)) ==0 || current_free_blk< (char*)mem_heap_lo() || current_free_blk> (char*)mem_heap_hi() ){
                 dbg_printf("This pointer:%p is not valid in the free list at line %d\n", current_free_blk, lineno);    // cheak if the free blk pointer is valid or not
                 return false;
             }
             
             current_free_blk = (char *) GET(N_ADD(current_free_blk)); // let current point to the next blk in this free list
         }
    }
    
      
    // Is every free blk actually in the free list?
    // Are all blk pointers valid?
    bp = heap_listp;
    while ( GET_SIZE(HDRP(bp))>0 ){
      if ( GET_ALLOC(HDRP(bp)) == 0){
          free_count_heap = free_count_heap+1;    // go through the entire heap and count free blks
      }
      if ( bp< (char*)mem_heap_lo() || bp> (char*)mem_heap_hi() ||bp ==NULL ){
          dbg_printf("blk pointer %p is invalid at line %d\n", bp, lineno);    //go through the entire heap to check every blk pointer is valid or not
          return false;
      }
    
      bp = NEXT_BLK(bp);
    }
    if (free_count != free_count_heap){    // compare number of free blks in seglists and number of free blks in heap, if they are not equal, it means there are some free blks are not in seg lists
        dbg_printf("Some free blks is not in seg lists. Free blk in heap:%zu, Free blk in lists:%zu ,at line %d\n", free_count_heap, free_count, lineno);
        return false;
    }
    
    //Are there any free blks escaped from coalescing?
    bp = heap_listp;
    while ( GET_SIZE(HDRP(bp))>0 ){
      if ( GET_ALLOC(HDRP(bp)) == 0){    //go through all free blks in heap to check is there is a free blk's previous is free
          if ( PREV_ALLOC(HDRP(bp))!=2 ){
              dbg_printf("blk:%p and its previous blk escaped from coalescing, at line %d\n", bp, lineno);
              return false;
          } 
      }
      
      if ( bp + GET_SIZE(HDRP(bp))-WSIZE > HDRP(NEXT_BLK(bp)) ){     //go through the heap to cheak if there is a blk that overlaps with the next blk
          dbg_printf("Current blk %p is overlapped with the next blk %p in heap at line %d\n", bp, NEXT_BLK(bp), lineno);
          return false;
      }
    
      bp = NEXT_BLK(bp);
    }
    
    
#endif /* DEBUG */
    return true;
}
