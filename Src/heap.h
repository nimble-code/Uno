/***** uno: heap.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#ifndef max
#define max(a,b)	((a)>=(b)?(a):(b))
#endif

#ifndef    HEAP_H
#define    HEAP_H

#define MIN_HUNK_ARRY	  8
#define DEFLT_RATIO	256

/* machine-dependent */

#define PNTR_SZE	(sizeof(void *))
#define ALGN_SZE	(sizeof(double))
#define MIN_SZE		max(PNTR_SZE,ALGN_SZE)

typedef struct hp_strt {
	unsigned int chnk_sze;
	unsigned int ch_ratio;

	unsigned int num_alloc;
	unsigned int num_free;
	unsigned int num_hunks;

	unsigned int hunk_array_sze;
	unsigned int next_chunk;

	void  *free_list;
	void **hunks;
} Heap;

Heap *CreateHeap(unsigned int, unsigned int);
void  DestroyHeap(Heap *);
void  FreeHeap(Heap *);
void *HeapAlloc_Gen(Heap *);
void *HeapAlloc(Heap *);
void  HeapFree(Heap *, void *);

#endif    /* HEAP_H  */
