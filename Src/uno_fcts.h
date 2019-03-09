/***** uno: uno_fcts.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

typedef struct Arc	Arc;
typedef struct BSym	BSym;
typedef struct BFct	BFct;
typedef struct Label	Label;
typedef struct NList	NList;
typedef struct Node	Node;
typedef struct Pool	Pool;
typedef struct Report	Report;
typedef struct Rstack	Rstack;
typedef struct Stack	Stack;
typedef struct VList	VList;
typedef struct Var	Var;
typedef struct Vis	Vis;

struct Report {
	int	n;
	Report	*nxt;
};

struct Var {
	char	*s;
	char	*loc;
	int	sel;
	int	stat;
	int	mark;
	Var	*nxt;
};

struct BSym {
	char	*s;
	BSym	*nxt;
};

struct Label {
	unsigned char	*label;
	Label	*nxt;
};

struct NList {
	Node	*n;
	NList	*nxt;
};
struct VList {
	Var	*v;
	VList	*nxt;
};

struct Vis {
	VList	*v;			/* marked variables */
	NList	*r;			/* callpts on Rstack */
	unsigned long	uno_state;	/* bitmask of states seen */
	short	zerostack;		/* empty Rstack */
	short	zeromarks;		/* no markings */
};

struct Node {
	int	nid;
	Label	*lab;
	Arc	*succ;
	Vis	*vis;	/* states from prop seen */
	Node	*nxt;
};

struct Arc {
	Node	*to;
	Label	*lab;
	Arc	*nxt;
};

struct BFct {
	char	*fnm;
	BSym	*calls;
	Node	*root;

	short	visited;	/* dfs */
	BFct	*nxt;		/* linked list of fcts */
};

struct Stack {
	Arc	*move;
#if 0
	Node	*prop;
#endif
	short	uno_state;	/* val range 0..30 */
	Var	*sels;
	BSym	*knz;		/* known nonzero vars */
	Label	*n;
	BFct	*fc;
	BFct	*fr;
	Stack	*nxt;
};

struct Rstack {
	BFct	*f;
	Node	*n;
	Rstack	*nxt;
};

struct Pool {
	char *s;
	Pool *nxt;
};

