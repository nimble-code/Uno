/***** uno: nmetab.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original by Shaun Flisakowski, Jan 11, 1995 */

#include <limits.h>
#include "globals.h"
#include "lexer.h"
#include "nmetab.h"

#define BITS_IN_int	(sizeof(int) * CHAR_BIT)
#define THREE_QUARTERS	((int) ((BITS_IN_int * 3) / 4))
#define ONE_EIGHTH	((int) (BITS_IN_int / 8))
#define HIGH_BITS	(~((unsigned int)(~0) >> ONE_EIGHTH))

#define HASH_ITEM_SZE	(sizeof(HashItem))
#define MAX_HASH_BCKTS	1023

typedef struct hi {
    str_t      sym;
    struct hi *next;
} HashItem;

static HashItem *NmeTab[MAX_HASH_BCKTS];

extern void *emalloc(size_t);

char *
nmestr(str_t *sym)
{
	if (sym) return sym->str;

	return NULL;
}

static unsigned int
calc_hash(char *str)	/* pjw's hash */
{	unsigned int hsh = 0, i;

	while (*str)
	{	hsh = (hsh << ONE_EIGHTH) + *str++;
		if ((i = hsh & HIGH_BITS) != 0)
			hsh = (hsh ^ ( i >> THREE_QUARTERS)) & ~HIGH_BITS;
	}
	return hsh;
}

void
init_nmetab(void)
{	int j;

	for (j = 0; j < MAX_HASH_BCKTS; j++)
		NmeTab[j] = (HashItem *) NULL;
}

str_t *
nmelook(char *sym, int len)
{	HashItem *hptr;
	unsigned int hsh;
	int bckt;

	hsh  = calc_hash(sym);
	bckt = hsh % MAX_HASH_BCKTS;

	for (hptr=NmeTab[bckt]; hptr; hptr=hptr->next)
	{	if ((hptr->sym.hash == hsh)
		&&  (strcmp(sym, hptr->sym.str) == 0))
			return(&(hptr->sym));
	} 

	hptr = (HashItem *) emalloc(HASH_ITEM_SZE);

	if (!len) len = strlen(sym);

	hptr->sym.str = emalloc(len+1);
	hptr->sym.hash = hsh;
	strncpy(hptr->sym.str, sym, len);

	hptr->next = NmeTab[bckt];
	NmeTab[bckt] = hptr;

	return(&(hptr->sym));
}
