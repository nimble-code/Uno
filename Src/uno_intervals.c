/***** uno: uno_intervals.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include "symtab.h"
#include "uno_lts.h"
#include "c_gram.h"

static int	debug = 0;
extern int	size_ok, size_nok;

extern void	explain_bound(char *, ArBound *, treenode *);
extern void	uno_assert(int, char *);

/* defined in this file: */
static void	and_bounds(ArBound *, ArBound *);
static void	copy_bound(ArBound *, ArBound *);

void	negate_bound(ArBound *);
int	check_bounds(ArBound *, int, treenode *);
int	merge_bounds(ArBound *, ArBound *);
int	same_bounds(ArBound *, ArBound *);
void	sanitize(ArBound *);

extern void	uno_warn(char *, treenode *, symentry_t *);

/* in intervals: lowerbounds are included, upperbounds are excluded */

void
negate_bound(ArBound *b)
{
	if (debug>1) explain_bound("negating", b, ZT);

	uno_assert(!(b->bounds & (DUP|UNK)), "dup or unk in negate");

	if ((b->bounds & LB)
	&&  (b->bounds & UB))
	{	if (b->bounds & NEG)
			b->bounds &= ~NEG;
		else
			b->bounds |= NEG;
	} else if (b->bounds & LB)
	{	b->bounds &= ~LB;
		b->bounds |= UB;
		b->ub = b->lb;
	} else if (b->bounds & UB)
	{	b->bounds &= ~UB;
		b->bounds |= LB;
		b->lb = b->ub;
	} else
	{	printf("uno: zero bounds, cannot happen\n");
		exit(1);
	}
}

int
unsatisfiable(ArBound *a)
{
	if (a->bounds & UNK) return 0;

	return ((a->bounds & LB) && (a->bounds & UB) && a->ub <= a->lb);
}

int
first_inside_second(ArBound *a, ArBound *b)	/* is interval a inside interval b? */
{
	sanitize(a);
	sanitize(b);

	if (unsatisfiable(a)
	||  unsatisfiable(b))
		return 0;

	if (!(a->bounds&NEG) && !(b->bounds&NEG))	/* ...[-2..-1]...[1>... */
		return ((a->lb >= b->lb) && (a->ub <= b->ub));

	if ((a->bounds&NEG) && (b->bounds&NEG))
		return ((a->lb <= b->lb) && (a->ub >= b->ub));

	if (!(a->bounds&NEG) && (b->bounds&NEG))
		return (a->ub <= b->lb || a->lb >= b->ub);

	if ((a->bounds&NEG) && !(b->bounds&NEG))
		return (b->lb >= a->ub || b->ub <= a->lb);

	/* unreachable */
	return 0;
}

int
check_bounds(ArBound *b, int x, treenode *nn)	/* is bound within interval 0..x-1 ? */
{	char buf[512];
	int result = 1;

	if (b->bounds & DUP)
	{	if (!b->dup)
		{	if (debug>1) printf("dup not set\n");
			return 1;
		}
		b = b->dup;	/* one step only */
	}

	if (unsatisfiable(b))
	{	if (debug) explain_bound("unsatisfiable", b, nn);
		return 1;	/* no run can get here, so this is no error */
	}
	if (!(b->bounds&NEG))
	{	if ((b->bounds&LB) && b->lb < 0)
		{	result = 0;
			sprintf(buf, "array index can be negative (%d)", b->lb);
		}
		if ((b->bounds&UB) && b->ub > x)
		{	result = 0;
			sprintf(buf, "array index can exceed upper-bound (%d>%d), var",
				b->ub-1, x-1);
		}
	} else
	{	result = 0;
		uno_assert((b->bounds & UB) && (b->bounds & LB), "negated non-interval");
		if (b->lb == b->ub - 1)
		{	sprintf(buf, "array index can be unequal to %d", b->lb);
			if (debug)
				printf("	dubious: <%s>\n", buf);
			result = 1;	/* dubious report */
		} else
			sprintf(buf, "array index can be <%d or >=%d", b->lb, b->ub);
	}

	if (result == 0)
	{	size_nok++;
		if (nn)
			uno_warn(buf, nn, b->s);
		else if (debug)
			printf("<<%s>>\n", buf);
	}  else
	{	size_ok++;
		if (debug>1) printf(" satisfied..\n");
	}

	return result;
}

void
sanitize(ArBound *a)
{
	if ((a->bounds&UNK)
	||  (a->bounds&DUP))
		return;

	if (!(a->bounds&LB) && !(a->bounds & UB))
		explain_bound("error", a, ZT);

	uno_assert((a->bounds&LB) || (a->bounds & UB), "zerobound error");

	if (!(a->bounds&UB)) a->ub =  INT_MAX;
	if (!(a->bounds&LB)) a->lb = -INT_MAX;

	if (!(a->bounds & NEG)
	||   ((a->bounds & LB) && (a->bounds & UB)))	/* bug found by codesurfer: ; */
		return;

	if (a->bounds & LB)
	{	a->bounds &= ~NEG;
		a->bounds &= ~LB;
		a->bounds |= UB;
		a->ub = a->lb;
	} else if (a->bounds & UB)
	{	a->bounds &= ~NEG;
		a->bounds &= ~UB;
		a->bounds |= LB;
		a->lb = a->ub;
	}
}

static void
and_bounds(ArBound *a, ArBound *b)	/* replace 'a' with 'a/\b' */
{
	if (debug>1)
	{	printf("start and-bounds:\n");
		explain_bound("a:", a, ZT);
		explain_bound("b:", b, ZT);
	}

	sanitize(a);
	sanitize(b);
	if (!(a->bounds&NEG)
	&&  !(b->bounds&NEG))
	{	if ((a->bounds & UB) && (b->bounds & UB))
		{	if (b->ub < a->ub)
				a->ub = b->ub;
		}
		if ((a->bounds & LB) && (b->bounds & LB))
		{	if (b->lb > a->lb)
				a->lb = b->lb;
		}

		if (!(a->bounds & UB) && (b->bounds & UB))
		{	a->bounds |= UB;
			a->ub = b->ub;
		}

		if (!(a->bounds & LB) && (b->bounds & LB))
		{	a->bounds |= LB;
			a->lb = b->lb;
		}
		goto done;
	}

	if ((a->bounds&NEG)
	&&  (b->bounds&NEG))		/* both known to be intervals */
	{	if (b->ub > a->ub)
			a->ub = b->ub;
		if (b->lb < a->lb)
			a->lb = b->lb;
		goto done;
	}

	if (!(a->bounds&NEG)
	&&   (b->bounds&NEG))		/* b known to be an interval */
	{	if ((a->bounds & UB)
		&&  (a->bounds & LB))
		{	if (a->lb < b->lb)
			{	if (a->ub > b->ub)
					a->bounds |= UNK; /* creates 2 intervals */
				else
					a->ub = b->lb;
				goto done;
			}
			if (a->ub > b->ub)
			{	a->lb = b->ub;
				goto done;
			} else
			{	a->lb = a->ub = 0;	/* not satisfiable */
				goto done;
			}
		} else if (a->bounds & UB)
		{	if (a->ub > b->ub)
				a->bounds |= UNK;	/* creates 2 intervals */
			else
				a->ub = b->lb;
		} else if (a->bounds & LB)
		{	if (a->lb < b->lb)
				a->bounds |= UNK;	/* creates 2 intervals */
			else
				a->lb = b->ub;
		}
		goto done;
	}
	if ( (a->bounds&NEG)		/* a known to be an interval */
	&&  !(b->bounds&NEG))
	{	a->bounds &= ~NEG;

		if ((b->bounds & UB)
		&&  (b->bounds & LB))
		{	if (b->lb < a->lb)
			{	if (b->ub > a->ub)
					a->bounds |= UNK; /* creates 2 intervals */
				else
					a->lb = b->lb;
				goto done;
			}
			if (a->ub > b->ub)
			{	a->lb = b->ub;
				goto done;
			} else
			{	a->lb = a->ub = 0;	/* not satisfiable */
				goto done;
			}
		} else if (a->bounds & UB)
		{	if (a->ub > b->ub)
				a->bounds |= UNK;	/* creates 2 intervals */
			else
				a->ub = b->lb;
		} else if (a->bounds & LB)
		{	if (a->lb < b->lb)
				a->bounds |= UNK;	/* creates 2 intervals */
			else
				a->lb = b->ub;
		}
		goto done;
	}
done:
	a->bounds &= ~FROMASGN;
	a->bounds &= ~FROMEXPR;
	sanitize(a);
}

static void
copy_bound(ArBound *to, ArBound *from)
{
	to->s       = from->s;
	to->sameas = from->sameas;
	to->dup    = from->dup;
	to->bounds = from->bounds;
	to->lb     = from->lb;
	to->ub     = from->ub;
}

int
same_bounds(ArBound *a, ArBound *b)	/* true if bound a includes bound b */
{
	if (strcmp(a->s->nme->str, b->s->nme->str) != 0
	||  (a->bounds & UNK) != (b->bounds & UNK))
		return 0;

	if (a->bounds & UNK)
		return 1;

	return first_inside_second(b, a);
}

int
merge_bounds(ArBound *a, ArBound *b)	/* rewrite a as (a/\b)  FIX! */
{	/* returns 1 if nothing   changed */
	/* returns 0 if something changed */

	if (debug>1)
	{	printf("merge_bounds\n");
		explain_bound("a:", a, ZT);
		explain_bound("b:", b, ZT);
	}
	uno_assert(!(a->bounds & UNK), "merging unknown a");
	uno_assert(!(b->bounds & UNK), "merging unknown b");
	uno_assert(!(b->bounds & DUP), "merging dup b");

	if (a->bounds & DUP)
	{	if (debug>1) printf("	a was dup, now unknown\n");
		a->bounds |= UNK;	/* fixable dups were resolved before we got here */
		return 0;
	}

	if (first_inside_second(a, b))
	{	if (debug>1) printf("	a inside b\n");
		return 1;
	}
	if (first_inside_second(b, a))
	{	if (debug>1) printf("	b inside a\n");
		copy_bound(a, b);
		return 0;
	}

	and_bounds(a, b);

	if (debug>1)
	{	printf("result of AND:\n");
		explain_bound("a:", a, ZT);
	}

	return 0;
}
