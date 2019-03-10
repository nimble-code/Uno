/***** uno: uno_lts.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#ifndef UNOLTS_H
#define UNOLTS_H

typedef struct Trans	Trans;
typedef struct State	State;
typedef struct Graphs	Graphs;
typedef struct LNode	LNode;
typedef struct Stack	Stack;
typedef struct SwStack	SwStack;
typedef struct DfStack	DfStack;
typedef struct SymRef	SymRef;
typedef struct SymExt	SymExt;
typedef struct PathCond PathCond;

struct Trans {
	treenode *cond;	/* if conditional, expr to be matched for this branch */
	SymRef	*knz;	/* vars known to be nonzero after this branch */
	State *branch;	/* successor chain */
	Trans *nxt;	/* next successor chain */
};

struct Stack {		/* stack for parsing of for, do, while structures */
	treenode *n;
	int	status;
	Stack	*nxt;
};

struct SwStack {	/* state stack */
	State	*s;
	SwStack	*nxt;
};

struct SymRef {
	symentry_t	*sm;
	treenode	*n;
	int		status;	/* typically def/use info */
	int		s_val;	/* in uno_generic, symbol can be given state value */
	SymRef		*nxt;
};

struct SymExt {
	symentry_t	*sm;
	treenode	*n;
	int		status;
	SymExt		*nxt;
};

struct DfStack {
	SymRef		*symrefs;	/* tracks use of locals */
	SymRef		*globrefs;	/* tracks use of globals */
	PathCond	*state;
	DfStack		*nxt;
};

struct State {
	treenode *n;		/* defining node */

	SymRef	*snapshot;	/* union of all versions of dfstack->symrefs when visited */

	SymRef	*gi;		/* vars of dfstack->globrefs seen at this state */
	SymRef	*il;		/* intersection: vars common to all earlier visits */

	PathCond *pc;		/* pathconds seen at earlier visits */
	PathCond *ip;		/* intersection: pathconds common to all earlier visits */

	short	seenempty;	/* visited state with zero entries in globrefs? */
	short	seennone;	/* visited state with zero entries in knzv? */

	ArBound *pvb;		/* previously seen bounds at this stmnt */
	unsigned long	uno_state;	/* bitvector of uno_states seen - dfs_generic */

	short	iscond;		/* set if conditional branch point */
	short	visited;	/* dfs */

	Trans	*succ;		/* successor chain(s) */
	Trans	*direct;	/* direct route for nut connections */
	State	*nxt;		/* temporary slot for immediate successor */

	State	*all;		/* linked list of all states created */
};

struct Graphs {
	char	*fctnm;		/* name of this fct, or _globals_ */
	State	*cfg;		/* start node for a procedure cfg */
	State	*all;		/* linked list of all states in this graph */

	SymRef	*def_use;	/* records def and useb4def info on globals */
	SymRef	*locs;		/* list of locals, declared but not yet used in fct */

	SymExt	*fcalls;	/* list of all fcts called in this fct */
	SymExt	*suspect;	/* globals with local useb4def + fcts called so far */

#if 0
	Graphs	*prev;		/* to record calling chains in ana_graph */
#endif
	char	*scope;		/* set if function declared static */
	short	visited;
	short	status;		/* records if values are (always/never) returned */
	short	hasnuts;	/* has info in cfg for global defuse analysis */
	Graphs	*nxt;		/* all cfg's created */
};

struct LNode {
	char *s;	/* label name */
	char *f;	/* function name */
	State *n;
	LNode *nxt;
};

struct PathCond {
	treenode *exp;
	treenode *val;
	PathCond *nxt;
};

extern char	*want, *file_name;
extern char	*x_stmnt(treenode *);
extern int	uno, Verbose;

extern leafnode	*mk_ident(void);	/* c_gram.y */
extern treenode *mk_bool(char *);	/* c_gram.y */
extern treenode *mk_deflt(void);	/* c_gram.y */
extern treenode *mk_int(int);		/* c_gram.y */
extern void	uno_bounds(SymList *, ArList *, treenode *);
extern void	bound_stats(void);
extern void	*emalloc(size_t);
extern void	efree(void *);

#define ZT	(treenode *) 0
#define ZS	(State *) 0

#endif
