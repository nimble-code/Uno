/***** uno: uno_global.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

typedef struct CallStack CallStack;
typedef struct Fct	Fct;
typedef struct Place	Place;
typedef struct PlaceName PlaceName;
typedef struct Seen	Seen;
typedef struct Sym	Sym;

struct Place {
	char	*fnm;
	int	line;
};

struct PlaceName {
	Place	*n;
	char	*s;	/* struct field */
	int	used;
	PlaceName *nxt;
};

struct Seen {
	Place	*n;
	Seen	*nxt;
};

struct Sym {
	char	*s;
	Place	*n;
	int	bits;
	Sym	*nxt;
};

struct Fct {
	char	*fnm;
	Place	*n;
	short	is_static;
	short	rval;
	short	special; /* if set, dunno when called */
	Sym	*defs;
	Sym	*uses;
	Sym	*deref;
	Sym	*calls;
#if 0
	Sym	*import;
#endif

	short	visited;	/* tarjan dfs */
#if 0
	short	onstack;
	int	scc_nr, low_link, dfs_nr;
	Fct	*t_nxt;		/* tarjan stack */
#endif
	Fct	*nxt;		/* linked list of fcts */
};
#if 0
struct CallStack {
	Fct	*f;
	Sym	*r;
	CallStack	*nxt;
};
#endif
