/***** uno: heap.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>

#include "heap.h"
#include "treestk.h"

extern void	*emalloc(size_t);
extern void	efree(void *);

Heap *
CreateHeap(unsigned int chunk_size, unsigned int chnk_hunk_ratio )
{	Heap    *heap;
	unsigned int     unit;

	heap = (Heap *) emalloc(sizeof(Heap));

	unit  = max(chunk_size, MIN_SZE);
	if (unit % ALGN_SZE != 0)
		unit += ALGN_SZE - (unit % ALGN_SZE);
	heap->chnk_sze = unit;

	if (chnk_hunk_ratio)
		heap->ch_ratio = chnk_hunk_ratio; 
	else
		heap->ch_ratio = DEFLT_RATIO;

	heap->num_alloc = 0; 
	heap->num_free  = 0; 
	heap->num_hunks = 0; 

	heap->next_chunk = 0;
	heap->hunk_array_sze = MIN_HUNK_ARRY;
	heap->free_list = (void *) NULL;

	heap->hunks = (void **) emalloc(MIN_HUNK_ARRY * PNTR_SZE);

	return(heap);
}

typedef struct FC FC;
struct FC {
	union {
		FC	*nxt;
		char	*base[MX_NODE_SZE];
	} fc;
};
static FC *free_chunks;	/* gh */
#ifdef DEBUG
static int gh_sz;
#endif

#ifdef DEBUG
int
check_chunks(void *y)
{	FC *x;

	for (x = free_chunks; x; x = x->fc.nxt)
	{	if ((int) x < 1000)
		{	printf("memory corrupted \n");
			abort();
		}
		if (x == y)
		{	printf("double release %p\n", x);
			x = (FC *) 0; x = x->fc.nxt;	/* cause crash */
			return 0;
		}
	}
	return 1;
}
#endif

void
rel_chunk(void *x)
{	FC *y;

#ifdef DEBUG
	if (!check_chunks(x)) return;
#endif
	memset(x, 0, MX_NODE_SZE);
	y = (FC *) x;
	y->fc.nxt = free_chunks;
	free_chunks = y;

#ifdef DEBUG
	printf("++ %p	-- %d\n", x, ++gh_sz);
#endif
}

void
DestroyHeap(Heap *heap)
{
#if 0
	int j, k;
	char *v;
#endif
	if (heap)
	{
#if 0
		for (j = 0; j < (int) heap->num_hunks; j++)
		for (k = 0; k < (int) heap->ch_ratio; k++)
		{	v = (char *) heap->hunks[j] + (k * (MX_NODE_SZE));
			rel_chunk((void *) v);	/* leads to double frees */
		}
#endif
		memset(heap, 0, sizeof(Heap));
	}
}

void *
HeapAlloc_Gen(Heap *heap)
{	int     asze, chnk;
	void   *avail, *pnt;

	if (!heap)
		return ((void *) NULL);

	if (free_chunks)
	{
#ifdef DEBUG
		printf("-- %p	%d\n", free_chunks, --gh_sz);
#endif
		avail = (void *) free_chunks;
		free_chunks = free_chunks->fc.nxt;
		memset(avail, 0, sizeof(void *));
		return avail;
	}

	if (heap->num_hunks)
	{	chnk = (heap->next_chunk)++;

		if (chnk == (int) heap->ch_ratio)
		{
			if (heap->num_hunks == heap->hunk_array_sze)
			{	asze = heap->hunk_array_sze * 2;	/* double array size */
				pnt = (void *) emalloc(asze * PNTR_SZE);
	
				memcpy(pnt, (void *) heap->hunks, (heap->hunk_array_sze * PNTR_SZE));
	
				efree(heap->hunks);
				heap->hunks = pnt;
				heap->hunk_array_sze = asze;
			}
	
			heap->hunks[heap->num_hunks] =
				(void *) emalloc(heap->chnk_sze * heap->ch_ratio);
	
#ifdef DEBUG
	printf("2 chunk allocate at %p -- %d * %d bytes\n",
		heap->hunks[heap->num_hunks],
		heap->chnk_sze, heap->ch_ratio);
#endif
			(heap->num_hunks)++;
			heap->next_chunk = 1;
			(heap->num_alloc)++;
			return (heap->hunks[(heap->num_hunks)-1]);
		} else
		{	(heap->num_alloc)++;
			return((void *) ((char*) (heap->hunks[(heap->num_hunks)-1])
				+ (heap->chnk_sze * chnk))); 
		}
	} else
	{	heap->hunks[0] = (void *) emalloc(heap->chnk_sze * heap->ch_ratio);
#ifdef DEBUG
	printf("1 chunk allocate at %p -- %d * %d bytes\n",
		heap->hunks[0], heap->chnk_sze, heap->ch_ratio);
#endif
		heap->num_hunks = 1;
		heap->next_chunk = 1;
		(heap->num_alloc)++;
		return (heap->hunks[0]);
	}
}

void
HeapFree(Heap *unused_heap, void *chunk)
{
	if (chunk) rel_chunk(chunk);
}

void *
HeapAlloc(Heap *heap)
{
	return HeapAlloc_Gen(heap);
}
