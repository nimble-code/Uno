/***** uno: dflow.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

typedef struct ArSize	ArSize;
typedef struct ArBound	ArBound;
typedef struct SymList	SymList;
typedef struct ArList	ArList;
typedef struct DefUse	DefUse;
typedef struct DuG	DuG;
typedef struct DuGP	DuGP;
typedef struct BoundStack BoundStack;

struct SymList {
	int	selected;
	unsigned int	mark;
	struct symentry *sm;
	SymList	*nxt;
	SymList *all;
};

struct ArList {
	struct	treenode *tn;
	ArList   *nxt;
};

struct ArSize {
	struct symentry	*s;	/* basename */
	struct treenode	*b;	/* declared size */
	ArSize	*nxt;
};

/* need flags for: originate, kill, propagate */

struct ArBound {
	struct symentry *s;
	struct symentry *sameas;
	ArBound	*dup;		/* effective array bound for sameas */
	short	bounds;		/* flags defined in uno_bounds.c */
	int	ub, lb;
	int	level_set;	/* at which step set */
	ArBound	*nxt;
};

struct DefUse {
	int	special;	/* for override markings */
	SymList	*def;
	SymList	*use;
	SymList *other;
	ArList	*aio;		/* array index operations */
	char	*der_type;	/* derived type -- new 1/06 */
};

struct DuG {		/* variable dependency graph */
	struct	symentry *sm;	/* ptr to symbol table */
	int	marks;		/* decl, def, use, hide info */
	int	rdcls;		/* set inside or outside procedure */
	DuGP	*d_e;	/* llist of outgoing edges */
	DuG	*nxt;	/* llist of all nodes */
};

struct DuGP {
	DuG	*ptr;
	int	dist;		/* distance in dependency chain */
	DuGP	*nxt;
};

struct BoundStack {
	ArBound		*curbounds;
	BoundStack	*nxt;
};

#define UB		1
#define LB		2
#define UNK		4	/* unknown */
#define FROMASGN	8
#define FROMEXPR	16
#define DUP		32
#define NEG		64

#include "dtags.h"
