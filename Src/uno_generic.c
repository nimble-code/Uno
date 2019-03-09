/***** uno: uno_generic.c *****/

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
#include "c_gram.h"
#include "symtab.h"
#include "uno_lts.h"

static int	debug = 0;

typedef struct GenStack GenStack;

struct GenStack {
	SymRef	*symrefs;
	int	uno_state;
	treenode *e, *c;
	GenStack *nxt;
};

static GenStack	*gen_stack = (GenStack *) 0;
static GenStack	*gen_free = (GenStack *) 0;
static treenode *witness = (treenode *) 0;
static int	ruledout = 0;

extern State	*uno_prop;
extern Graphs	*curgraph;

static int	steps = 0;
static int	path_ends = 0;
static int	ErrCnt = 0;
extern int	depth, Verbose, nopaths;
extern int	nogood, picky, allerrs;
       int	err_path;

/* Names used in user-code inside C procedure specifying the property */
const char *property  = "uno_check";	/* name of prop, specified as C procedure in src */

static const char *errname   = "error";	/* name of error procedure */
static const char *callname  = "fct_call";	/* name of procedure used to check for fcts called */
static const char *endname   = "path_ends";	/* name of procedure used to check for end-state */
static const char *selname   = "select";
static const char *refname   = "refine";
static const char *matchname = "match";
static const char *markedname = "marked";
static const char *excname   = "unselect";

/* variables that can be set within the property */
       const char *statename = "uno_state";	/* to refer to the state of the prop automaton */
static const char *s_name    = "s_name";	/* to refer to target symbol name */
static const char *s_val     = "s_mark";	/* to refer to target symbol state_value */

static char	*user_name;	/* remembers a user-defined symbol name - for use in select() */
static int	user_val;	/* remembers a user-defined state value - for use in select() */

/* dealing with symbols: */
#define Add_track	"add_track"
#define List_select	"list"
#define Skip_name	"no_error"
#define Del_track	"del_track"
#define Del_name	"del_name"
#define On_track	"on_track"
#define Any_track	"any_track"
#define Match_track	"match_track"
#define Known_zero	"known_zero"
#define Known_nonzero	"known_nonzero"
#define Update		"mark"
#define Unmark		"unmark"

extern SymRef	*rev_release(SymRef *);
extern SymRef	*uno_getref(symentry_t *);
extern int	eval_const_expr(treenode *, treenode *);
extern int	infeasible(treenode *, treenode *);
extern int	snap_add(State *, SymRef *);
extern int	v_matched(treenode *);
extern int	v_reported(treenode *);
extern void	dflow_mark(FILE *, int);
extern void	dump_defuse(DefUse *, FILE *);
extern void	uno_assert(int, char *);
static void	selected_symbol(treenode *);

static int
has_ident(treenode *n, char *s)
{
	if (!n) return 0;

	if (n->hdr.type == TN_IDENT)
		return (strcmp(((leafnode *)n)->data.sval->str, s) == 0);

	if (n->hdr.which != LEAF_T)
		switch (n->hdr.type) {
		case TN_SWITCH:
		case TN_WHILE:
		case TN_DOWHILE:
			return has_ident(n->lnode, s);
		default:
			return has_ident(n->lnode, s) || has_ident(n->rnode, s);
		}
	return 0;
}

static int
err_matched(GenStack *g)
{
	if (!g) return 0;

	return err_matched(g->nxt)
	|| (witness
	&&  witness == g->e
	&&  v_matched(g->e));
}

static void
err_reversed(GenStack *g)
{
	if (!g) return;

	if (!nopaths)
		err_reversed(g->nxt);
#if 0
	if (!debug && witness)
	{	if (g->e != witness)
			return;
		if (v_reported(g->e))
		{	fprintf(stderr, "\t--:\t%s:%d: <%s> matches an earlier case\n",
				g->e->hdr.fnm,
				g->e->hdr.line,
				x_stmnt(g->e));
			return;
		}
	}
	witness = ZT;
#endif

	if (g->e
	&&  g->e->hdr.type != TN_SWITCH
	&&  g->e->hdr.type != TN_WHILE
	&&  g->e->hdr.type != TN_DOWHILE)
	{
		if (g->e == witness) printf("*");
		if (g->c) printf("C");

		if (!nopaths) printf("\t%d:", steps++);

		printf("\t%s:%d: <%s>",
			g->e->hdr.fnm,
			g->e->hdr.line,
			x_stmnt(g->e));
		if (g->c)
			printf(" == <%s>", x_stmnt(g->c));

		if (debug) dump_defuse(g->e->hdr.defuse, stdout);
		printf(";\n");
	} else if (nopaths) err_reversed(g->nxt);
}

static int
same_expr(treenode *a, treenode *b)
{	leafnode *n, *m;

	if (!a && b) return 0;
	if (a && !b) return 0;
	if (a == b)  return 1;

	if (a->hdr.tok != b->hdr.tok
	||  a->hdr.which != b->hdr.which
	||  a->hdr.type != b->hdr.type)
		return 0;

	if (a->hdr.which == LEAF_T)
	{	n = (leafnode *) a;
		m = (leafnode *) b;

		switch (a->hdr.type) {
		case TN_INT:
			return n->data.ival == m->data.ival;
		case TN_REAL:
			return n->data.dval == m->data.dval;
		case TN_STRING:
			return n->data.sval->str == m->data.sval->str;
		case TN_IDENT:
			return (strcmp(n->data.sval->str, m->data.sval->str) == 0);
		case TN_TYPE:
			if (a->hdr.tok == TYPEDEF_NAME)
				return n->data.sval->str == m->data.sval->str;
			return (a->hdr.tok != b->hdr.tok);
		default:
			fprintf(stderr, "uno: %s:%d: %s:%d: cannot happen, same_expr: %s\n",
				a->hdr.fnm, a->hdr.line,
				b->hdr.fnm, b->hdr.line,
				name_of_node(a->hdr.type));
			exit(1);
		}
	}

	return same_expr(a->lnode, b->lnode)
	&&     same_expr(a->rnode, b->rnode);
}

static treenode *
path_not_feasible(void)
{	GenStack *f, *g;
	char *s, *t;
	SymList *x, *y;

	for (g = gen_stack; g; g = g->nxt)
	{	if (!g->c
		||   g->c->hdr.tok != IDENT)	/* not a conditional */
			continue;

		s = ((leafnode *)g->c)->data.sval->str;

		if (strcmp(s, "_false_") != 0
		&&  strcmp(s, "_true_")  != 0)
			continue;		/* not simple */

		for (f = g->nxt; f; f = f->nxt)
		{
#if 1
			/* if a symbol with USE in g->e appears with DEF in f->e
			   then the condition could well change in value
			 */

			if (f->e->hdr.defuse && g->e->hdr.defuse)
			for (x = f->e->hdr.defuse->other; x; x = x->nxt)
			{	if ((x->mark & DEF) && !(x->mark & (REF0|REF1)))
				for (y = g->e->hdr.defuse->other; y; y = y->nxt)
					if (strcmp(x->sm->nme->str, y->sm->nme->str) == 0
					&&  (y->mark & USE))
					{	if (debug)
						{	fprintf(stderr, "consistency check on %s\t",
								x_stmnt(g->e));
							fprintf(stderr, "voided by asgn in %s\n",
								x_stmnt(f->e));
						}
						goto done;
			}		}
#endif
			if (!same_expr(f->e, g->e)
			|| !f->c
			||  f->c->hdr.tok != IDENT)
				continue;

			t = ((leafnode *)f->c)->data.sval->str;
			if (strcmp(t, "_false_") != 0
			&&  strcmp(t, "_true_")  != 0)
				continue;	/* not simple */

			if (strcmp(s, t) != 0)	/* found contradiction */
			{	ruledout++;
				if (Verbose)
				{	printf("(Infeasible path)\n");
					return (treenode *) 0;
				}
				return g->e;
		}	}
done:		;
	}
	return (treenode *) 0;
}

static int
err_report(char *m, treenode *e)
{	GenStack *g;
	treenode *x;

	x = path_not_feasible();

	if ((!debug && x)
	||  err_matched(gen_stack))
	{	if (debug)
		fprintf(stderr, "err_report suppressed 1 x=%p\n", x);
		return 0;
	}

	if ((!allerrs && v_reported(e))
	|| (witness == e && picky))
	{	if (debug)
		fprintf(stderr, "err_report suppressed 2\n");
		return 0;
	}

	if (picky)
	{	int cnt = 0;
		for (g = gen_stack; g; g = g->nxt)
			if (g->c)
				cnt++;
		if (cnt >= picky)
		{	if (debug)
			fprintf(stderr, "err_report suppressed 3 (cnt %d, picky %d)\n",
				cnt, picky);
			return 0;	/* no paths with >= picky conditionals */
	}	}

	ErrCnt++;

	printf("uno: %d: %s() '%s'%s",
		ErrCnt, curgraph->fctnm, m,
		(witness && witness == e)? " (in cyclic path)":"");

	selected_symbol(e);

	if (x)
	printf(" (fails consistency check on %s)", x_stmnt(x));
	printf("\n");

	steps = 1;
	err_path = 1;
	err_reversed(gen_stack);
	err_path = 0;
	printf("\n");

	if (0) abort();

	return 1;
}

static int
gen_push(State *s)
{	GenStack *g;
	SymRef *r, *t;
	int any_added = 0;

	if (gen_free)
	{	g = gen_free;
		gen_free = gen_free->nxt;
	} else
		g = (GenStack *) emalloc(sizeof(GenStack));

	if (gen_stack)
	{	g->uno_state = gen_stack->uno_state;	/* copy state-bits */

		for (r = gen_stack->symrefs; r; r = r->nxt)
		{	if (snap_add(s, r))		/* not tracked from s before */
				any_added = 1;

			t = uno_getref(r->sm);
			t->status = r->status;
			t->s_val = r->s_val;
			t->n = r->n;
			t->nxt = g->symrefs;
			g->symrefs = t;
	}	}

	g->nxt = gen_stack;
	gen_stack = g;

	return any_added;
}

static void
gen_pop(GenStack *g)
{
	g->symrefs = rev_release(g->symrefs);
	g->uno_state = 0;

	uno_assert((gen_stack != NULL), "gen_stack error");

	gen_stack = gen_stack->nxt;	/* pop stack */
	g->nxt = gen_free;
	gen_free = g;
}

static int
good_target(treenode *n, SymList *r)
{
	if (!n) return 0;

	if (n->hdr.type == TN_IDENT) return 1;

	if (n->hdr.type == TN_ASSIGN
	&&  n->lnode
	&&  n->lnode->hdr.type == TN_IDENT
	&&  strcmp(r->sm->nme->str, ((leafnode *) n->lnode)->data.sval->str) == 0)
		return 1;

	return 0;
}

static int
basiczero(treenode *n, SymList *r)	/* 1 = zero, -1 = nonzero, 0 = don't know */
{
	if (n->hdr.type == TN_IDENT
	||  n->hdr.type == TN_ASSIGN
	||  n->hdr.type == TN_FUNC_CALL)
		return -1;		/* implicit ZERO_TEST - nonzero if true */

	if (n->hdr.type != TN_EXPR)
	{	if (debug) printf("basiczero: not an expr\n");
		return 0;		/* don't know */
	}

	if (n->hdr.tok == NOT
	&&  (n->rnode->hdr.type == TN_IDENT
	||   n->rnode->hdr.type == TN_ASSIGN))
		return 1;		/* implicit NONZERO_TEST - zero if true */

	if (n->hdr.tok == EQUAL)
	{	if ((n->rnode && n->rnode->hdr.type == TN_INT
		&&   ((leafnode *)n->rnode)->data.ival == 0
		&&     good_target(n->lnode, r))	/* new */
		||  (n->lnode && n->lnode->hdr.type == TN_INT
		&&   ((leafnode *)n->lnode)->data.ival == 0
		&&     good_target(n->rnode, r)))	/* new */
			return 1;	/* explicit ZERO_TEST - zero if true */

		if (debug) printf("basiczero: equal fail\n");
		return 0;		/* don't know */
	}
	if (n->hdr.tok == NOT_EQ)
	{	if ((n->rnode && n->rnode->hdr.type == TN_INT
		&&   ((leafnode *)n->rnode)->data.ival == 0
		&&     good_target(n->lnode, r))	/* new */
		||  (n->lnode && n->lnode->hdr.type == TN_INT
		&&   ((leafnode *)n->lnode)->data.ival == 0
		&&     good_target(n->rnode, r)))	/* new */
			return -1;	/* explicit NONZERO_TEST - nonzero if true */
		if (debug) printf("basiczero: not_equal fail\n");
		return 0;		/* don't know */
	}

	if (debug) printf("basiczero: other fail\n");
	return 0;
}

static void
sym_unmark(treenode *unused0, int unused1, int unused2)
{	SymRef *s, *os = (SymRef *) 0;

	for (s = gen_stack->symrefs; s; s = s->nxt)
		if (s->status & SELECTED)
		{	if (!os)
				gen_stack->symrefs = s->nxt;
			else
				os->nxt = s->nxt;

			if (debug) fprintf(stderr, "\tdeleted %s (line %d)\n",
				s->sm->nme->str, s->n?s->n->hdr.line:-1);
		} else
			os = s;
}

static void
sym_update(treenode *m, int val, int unused2)
{	SymRef *s;
	SymList *r;
	treenode *n;

	n = (m && m->hdr.type == TN_IF) ? ((if_node *)m)->cond : m;

	/* if any items on the stack were selected
	 * then a match() operations was executed
	 * which voids the select bits in defuse
	 */
	for (s = gen_stack->symrefs; s; s = s->nxt)
		if (s->status & SELECTED)
			goto after;

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
		if (r->selected)
		{	s = uno_getref(r->sm);
			s->nxt = gen_stack->symrefs;
			s->status = r->mark | SELECTED;
			s->n = n;
			gen_stack->symrefs = s;
			if (debug)
			printf("\tadded %s (line %d)\n",
				s->sm->nme->str, s->n?s->n->hdr.line:-1);
		}

	for (s = gen_stack->symrefs; s; s = s->nxt)
		if (s->status & SELECTED)
		{	if (debug)
			printf("\tmarked %s = %d (line %d)\n",
				s->sm->nme->str, val, s->n?s->n->hdr.line:-1);
after:			s->s_val = val;
		}
}

static int
known_details(treenode *m, int want)
{	SymRef *s, *t;
	SymList *r;
	GenStack *g = (GenStack *) 0;
	int v = -2;
	int w = 0;
	int anyhits;
#if 0
	for each symbol selected on dfs_stack
	search path backwards for USE of symbol in conditionals
	and determine if this renders its zero-ness known
#endif
	anyhits = 0;
	for (s = gen_stack->symrefs; s; s = s->nxt)
	{
		if (debug)
		fprintf(stderr, "stack: %s -- selected: %d\n", s->sm->nme->str, s->status & SELECTED);

		if (s->status & SELECTED)
		for (g = gen_stack->nxt; g; g = g->nxt)
		{
w = 1;
			/* should still appear in symrefs */
			for (t = g->symrefs; t; t = t->nxt)
				if (t->sm == s->sm)
					break;
			if (!t) goto unknown;
w = 2;
			r = (SymList *) 0;
			if (g->e->hdr.defuse && g->c)
			for (r = g->e->hdr.defuse->other; r; r = r->nxt)
				if (strcmp(r->sm->nme->str, s->sm->nme->str) == 0
				&& ((r->mark & USEafterdef)	/* test after assign */
				||  (r->mark & USE)))		/* straight test */
					break;

/* this doesn't check if the use doesn't appear inside a different context, eg. a fct call .... */

w = 3;
			if (r)
			{	anyhits = 1;
				v = basiczero(g->e, r);		/* 1=known zero, -1=nonzero */
				if (v == 0) goto unknown;	/* i.e., value unknown */
w = 4;
				if (strcmp(((leafnode *)g->c)->data.sval->str, "_true_") == 0)
				{	if (v == want)
					{
	if (debug)
	printf("want=%d, v=%d, known because of: %s == true\n",
		want, v, x_stmnt(g->e));
#if 0
                       v ==  0  -> false (unknown value)
	(want ==  1 && v ==  1) && _true_ -> true  (KNOWN ZERO)
	(want == -1 && v == -1) && _true_ -> true  KNOWN NONZERO

	 want ==  1 && v == -1) && _true_ -> false (not known zero)
	 want == -1 && v ==  1  && _true_ -> false (not knwon nonzero)
#endif
						break;		/* this symbol known zero */
					} else
						goto unknown;	/* unknown or nonzero */
				}
w = 5;
				if (strcmp(((leafnode *)g->c)->data.sval->str, "_false_") == 0)
				{	if (v == -want)		/* known nonzero */
					{
	if (debug)
	printf("want=%d, v=%d, known because of: %s == false\n",
		want, v, x_stmnt(g->e));
#if 0
	 want ==  1 && v == -1) && _false_ -> true (known zero)
	 want == -1 && v ==  1  && _false_ -> true (known nonzero)

	(want ==  1 && v ==  1) && _false_ -> false  (KNOWN ZERO)
	(want == -1 && v == -1) && _false_ -> false  KNOWN NONZERO
#endif
						break;
					} else
						goto unknown;	/* unknown or not zero */
				}
w = 6;
				goto unknown;			/* cannot tell */
			}
		}
	}
	if (!anyhits) goto unknown;

	if (debug)
	{	fprintf(stderr, "+preknown (want=%d) <%s>:\n", want, x_stmnt(m));
		if (s) fprintf(stderr, "	-- symbol %s -- v=%d\n", s->sm->nme->str, v);
		if (g) fprintf(stderr, " -- step <%s>\n", x_stmnt(g->e));
		if (g) fprintf(stderr, " -- cond <%s>\n", x_stmnt(g->c));
	}
	return 1;
unknown:
	if (debug)
	{	fprintf(stderr, "-preknown (want=%d) <%s> -- w=%d:\n", want, x_stmnt(m), w);
	/*	if (s) fprintf(stderr, "	-- symbol %s -- v=%d\n", s->sm->nme->str, v); */
		if (g) fprintf(stderr, " -- step <%s>\n", x_stmnt(g->e));
		if (g) fprintf(stderr, " -- cond <%s>\n", x_stmnt(g->c));
	}
	return 0;
}
static int
known_zero(treenode *m, int unused1, int unused2)
{	int r = known_details(m, 1);
	if (debug) fprintf(stderr, ">>knowzero returns %d\n", r);
	return r;
}
static int
known_nonzero(treenode *m, int unused1, int unused2)
{	int r = known_details(m, -1);
	if (debug) fprintf(stderr, ">>know_nonzero returns %d\n", r);
	return r;
}


static void
do_nothing(treenode *unused0, int unused1, int unused2)
{
	return;
}

static void
selected_symbol(treenode *n)
{	SymRef *s;
	SymList *r;

	for (s = gen_stack->symrefs; s; s = s->nxt)
		if (s->status & SELECTED)
			printf(" [%s]", s->sm->nme->str);

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
	{	if (!r->selected)
			continue;

		for (s = gen_stack->symrefs; s; s = s->nxt)
		{	if (s->status & SELECTED
			&&  strcmp(s->sm->nme->str, r->sm->nme->str) == 0)
				break;
		}
		if (!s) printf(" [%s]", r->sm->nme->str);
	}
}

static void
list_select(treenode *n, int unused1, int unused2)
{	SymRef *s;
	SymList *r;
	int cnt = 0;

	if (n)
		printf("uno: %s:%d: symbols (*=selected):\n",
			n->hdr.fnm, n->hdr.line);
	else
		printf("uno: symbols (*=selected):\n");

	for (s = gen_stack->symrefs; s; s = s->nxt)
		{	printf("	%3d%s:\t%s [",
				++cnt,
				(s->status & SELECTED)?"*":"",
				s->sm->nme->str);
			dflow_mark(stdout, s->status);
			printf("]	(stack - mark %d)\n", s->s_val);
		}

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
		{	printf("	%3d%s:	%s [",
				++cnt,
				r->selected?"*":"",
				r->sm->nme->str);
			dflow_mark(stdout, r->mark);
			printf("]	(stmnt)\n");
		}
}

static void
sym_add(treenode *m, int allow, int forbid)
{	SymRef *s;
	SymList *r;
	treenode *n;

	n = (m && m->hdr.type == TN_IF) ? ((if_node *)m)->cond : m;
	if (!n || !n->hdr.defuse)
	{	if (debug) printf("	symadd - nothing to add\n");
		return;
	}

	for (r = n->hdr.defuse->other; r; r = r->nxt)
	{	if (debug) printf("\tsymadd sees %s mark %d, looking for %d & !%d\n",
			r->sm->nme->str, r->mark, allow, forbid);

		if ((r->mark & allow) && !(r->mark & forbid))
		{	for (s = gen_stack->symrefs; s; s = s->nxt)
				if (strcmp(s->sm->nme->str, r->sm->nme->str) == 0
				&&  (unsigned int) s->status == r->mark)
				{	if (debug) printf("\tsymadd %s - already there\n",
						s->sm->nme->str);
					break;
				}
			if (!s)
			{	s = uno_getref(r->sm);
				s->nxt = gen_stack->symrefs;
				s->status = r->mark;
				s->n = n;
				gen_stack->symrefs = s;
				if (debug) printf("\tadded %s (line %d)\n",
					s->sm->nme->str, s->n?s->n->hdr.line:-1);
		}	}
	}
	if (debug) printf("\tsymadd - done\n");
}

static void
sym_del(treenode *m, int allow, int forbid)
{	SymRef *s, *os;
	SymList *r;
	treenode *n;

	n = (m && m->hdr.type == TN_IF) ? ((if_node *)m)->cond : m;

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
	{	if ((r->mark & allow) && !(r->mark & forbid))
		{	os = (SymRef *) 0;
again:			for (s = gen_stack->symrefs; s; os = s, s = s->nxt)
			{	if (strcmp(s->sm->nme->str, r->sm->nme->str) == 0
				&&  (s->status & allow)
				&& !(s->status & forbid))
				{	if (!os)
						gen_stack->symrefs = s->nxt;
					else
						os->nxt = s->nxt;

					if (debug) printf("\tdeleted %s\n",
						s->sm->nme->str);

					goto again;
	}	}	}	}
}

static void
sym_del_name(treenode *m, int allow, int forbid)
{	SymRef *s, *os;
	SymList *r;
	treenode *n;

	n = (m && m->hdr.type == TN_IF) ? ((if_node *)m)->cond : m;

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
	{	if ((r->mark & allow) && !(r->mark & forbid))
		{	os = (SymRef *) 0;
again:			for (s = gen_stack->symrefs; s; os = s, s = s->nxt)
			{	if (strcmp(s->sm->nme->str, r->sm->nme->str) == 0)
				{	if (!os)
						gen_stack->symrefs = s->nxt;
					else
						os->nxt = s->nxt;

					if (debug) printf("\tdeleted %s\n",
						s->sm->nme->str);

					goto again;
	}	}	}	}
}

static int
on_track(treenode *m, int allow, int forbid)
{	SymRef *s;
	SymList *r;
	treenode *n;

	n = (m && m->hdr.type == TN_IF) ? ((if_node *)m)->cond : m;

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
		if ((r->mark & allow) && !(r->mark & forbid))
		{	for (s = gen_stack->symrefs; s; s = s->nxt)
			{	if (strcmp(s->sm->nme->str, r->sm->nme->str) == 0
				&&  (s->status & allow)
				&& !(s->status & forbid))
				{	if (m != s->n)
						witness = s->n;
					if (debug) printf("\tsym present %s (line %d)\n",
						r->sm->nme->str, s->n?s->n->hdr.line:-1);
					return 1;
		}	}	}

	if (debug)
	{	printf("on_track: no matching syms\n");
		if (n && n->hdr.defuse)
		for (r = n->hdr.defuse->other; r; r = r->nxt)
			printf("\tdefuse have %s %d\n", r->sm->nme->str, r->mark);
		for (s = gen_stack->symrefs; s; s = s->nxt)
			printf("\tgenstack have %s %d\n", s->sm->nme->str, s->status);
	}
	return 0;
}

static int
match_track(treenode *m, int allow, int forbid)
{	SymRef *s;
	SymList *r;
	treenode *n;	/* var with allow and !forbid on defuse - that is also on_track? */

	n = (m && m->hdr.type == TN_IF) ? ((if_node *)m)->cond : m;

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
		if ((r->mark & allow) && !(r->mark & forbid))
		{	for (s = gen_stack->symrefs; s; s = s->nxt)
			{	if (strcmp(s->sm->nme->str, r->sm->nme->str) == 0)
				{	if (m != s->n)
						witness = s->n;
					if (debug) printf("\tsym matched %s (line %d)\n",
						r->sm->nme->str, s->n?s->n->hdr.line:-1);
					return 1;
		}	}	}

	if (debug) printf("match_track: no matching syms\n");
	return 0;
}

static int
any_track(treenode *m, int allow, int forbid)
{	SymRef *s;

	for (s = gen_stack->symrefs; s; s = s->nxt)
	{	if ((s->status & allow)
		&& !(s->status & forbid))
		{	if (m != s->n)
				witness = s->n;
			if (debug) printf("\tanytrack sym present %s (line %d)\n",
				s->sm->nme->str, s->n?s->n->hdr.line:-1);
			return 1;
	}	}

	if (debug) printf("any_track: no matching syms\n");
	return 0;
}

static struct Cmd {
	const char *cmd;
	void (*fn)(treenode *, int, int);
} cmds[] = {
	{ Add_track,	sym_add },
	{ Del_track,	sym_del },
	{ Del_name,	sym_del_name },
	{ Skip_name,	do_nothing },
	{ List_select,	list_select },
	{ Update,	sym_update },
	{ Unmark,	sym_unmark }
	/* adjust size of hit_cmds when adding more */
};

static struct Fct {
	const char *cmd;
	int (*fn)(treenode *, int, int);
} evals[] = {
	{ On_track,	on_track },
	{ Any_track,	any_track },
	{ Match_track,	match_track },
	{ Known_zero,   known_zero },
	{ Known_nonzero, known_nonzero }
	/* adjust size of hit_fcts when adding more */
};

static int hit_cmds[8];
static int hit_fcts[8];	/* room for 8 fcts */

static void
prop_reached(State *s)
{	Trans *t;

	if (!s || !s->n) return;

	if (!s->visited
	&&  !strstr(s->n->hdr.fnm, " after "))
		printf("uno: %s:%d: not reached\n",
			s->n->hdr.fnm, s->n->hdr.line);

	s->visited = 1;	/* prevent duplicate reports */

	for (t = s->succ; t && t->branch; t = t->nxt)
		prop_reached(t->branch);
}

void
gen_stats(void)
{	int i;
	int cnt;

	for (i = cnt = 0; i < 5; i++)
		if (hit_cmds[i])
			cnt++;
	if (cnt)
	{	printf("uno: commands in property executed\n");
		for (i = 0; i < 5; i++)
			if (hit_cmds[i])
			printf("\t%d\t%s\n", hit_cmds[i], cmds[i].cmd);
	}
	for (i = cnt = 0; i < 5; i++)
		if (hit_cmds[i])
			cnt++;
	if (cnt)
	{	printf("uno: fcts in property executed\n");
		for (i = 0; i < 3; i++)
			if (hit_fcts[i])
			printf("\t%d\t%s\n", hit_fcts[i], evals[i].cmd);
	}

	prop_reached(uno_prop);

	if (ruledout)
	printf("uno: %3d errorpaths generated, but ruled out as infeasible\n",
		ruledout);
}

static void
exec_fct(treenode *n, treenode *m)
{	SymRef *s;
	leafnode *leaf;
	int i, val1, val2;

	if (!n) return;

	if (n->lnode->hdr.type != TN_IDENT)
	{	err_path++;
		printf("exec_fct:\n\t%s:%d: expect ident for fctname, got %s in %s\n",
			n->hdr.fnm,
			n->hdr.line,
			name_of_node(n->lnode->hdr.type),
			x_stmnt(n));
		exit(1);
	}

	leaf = (leafnode *) n->lnode;

	for (i = 0; i < (int) (sizeof(cmds)/sizeof(struct Cmd)); i++)
		if (strcmp(leaf->data.sval->str, cmds[i].cmd) == 0)
		{
			if (strcmp(leaf->data.sval->str, Skip_name) == 0
			||  strcmp(leaf->data.sval->str, List_select) == 0)
			{	if (debug)
				printf("\tsaw: %s\n", leaf->data.sval->str);

				if (n->rnode
				&&  n->rnode->hdr.type == TN_STRING)
					printf("%s(\"%s\")\n",
						leaf->data.sval->str,
						((leafnode *) n->rnode)->data.str);

				hit_cmds[i]++;
				cmds[i].fn(m, 0, 0);
				return;
			}

			if (strcmp(leaf->data.sval->str, Unmark) == 0)
			{	nogood = val1 = val2 = 0;
				goto doit;	/* 'unmark()' means 'mark(0)' */
			}

			if (strcmp(cmds[i].cmd, Update) == 0)	/* one arg */
			{	nogood = val2 = 0;
				val1 = eval_const_expr(n->rnode, m);
				if (nogood)
				{	fprintf(stderr, "uno: expecting mark(const)\n");
					exit(1);
				}
				goto doit;
			}

			if (!n->rnode
			||   n->rnode->hdr.type != TN_EXPR_LIST)
			{
bad:				fprintf(stderr, "uno: expecting %s(const_expr, const_expr), saw %s(%s)\n",
					cmds[i].cmd, cmds[i].cmd,
					n->rnode?name_of_node(n->rnode->hdr.type):"");
				exit(1);
			}
			nogood = 0;
			val1 = eval_const_expr(n->rnode->lnode, m);
			val2 = eval_const_expr(n->rnode->rnode, m);
			if (nogood) goto bad;

doit:			cmds[i].fn(m, val1, val2);
			hit_cmds[i]++;

			if (debug)
			{	printf("\tgen_stack %s(", cmds[i].cmd);
				if (i < 2) dflow_mark(stdout, val1); else printf("%d", val1);
				printf(", ");
				if (i < 2) dflow_mark(stdout, val2); else printf("%d", val2);
				printf(") <%s>:\n", x_stmnt(m));
				for (s = gen_stack->symrefs; s; s = s->nxt)
				{	printf("\t%s\t(", s->sm->nme->str);
					dflow_mark(stdout, (s->status & ANY));
					printf(")\n");
				}
			}
			return;
		}

	if (strcmp(leaf->data.sval->str, errname) != 0
	||  n->rnode->hdr.type != TN_STRING)
	{	printf("\t\texpect '%s(\"...\")', saw '%s(%s)'\n",
			errname, leaf->data.sval->str,
			name_of_node(n->rnode->hdr.type));
		exit(1);
	}

	leaf = (leafnode *) n->rnode;

	if (debug) printf("<<%s>>\n", leaf->data.str);

	if (err_report(leaf->data.str, m))
	{	fflush(stdout);
		fflush(stderr);
		if (0) exit(1);
	}
	witness = ZT;
}

static int
do_oper(treenode *m, int sign)
{	treenode *n;

	/* either --x (rnode) or x-- (lnode) */
	/* executed as stmnt, net effect the same */

	if (m->rnode) n = m->rnode; else n = m->lnode;

	if (!n
	||   n->hdr.type != TN_IDENT
	||  strcmp(((leafnode *) n)->data.sval->str, statename) != 0)
		return 0;

	gen_stack->uno_state += sign;

	return 1;
}

static void
exec_step(treenode *n, treenode *m)
{	leafnode *leaf;

	switch (n->hdr.type) {
	case TN_FUNC_DECL:
	case TN_DECL:
	case TN_LABEL:
		break;

	case TN_FUNC_CALL:
		exec_fct(n, m);
		break;

	case TN_ASSIGN:
		if (n->lnode->hdr.type == TN_IDENT)
		{	leaf = (leafnode *) n->lnode;
			if (strcmp(leaf->data.sval->str, statename) == 0)
			{	nogood = 0;
				gen_stack->uno_state = eval_const_expr(n->rnode, m);
				if (nogood) goto bad;
			} else if (strcmp(leaf->data.sval->str, s_name) == 0)
			{	if (n->rnode->hdr.type == TN_STRING)
					user_name = ((leafnode *)n->rnode)->data.str;
				else if (n->rnode->hdr.type == TN_IDENT
				&& strcmp(((leafnode *)n->rnode)->data.sval->str, "MATCH") == 0)
					user_name = "_M_A_T_C_H_";
				else goto bad;
			} else if (strcmp(leaf->data.sval->str, s_val) == 0)
			{	nogood = 0;
				user_val = eval_const_expr(n->rnode, m);
				if (nogood) goto bad;
			}
		} else
		{
bad:			err_path++;
			printf("unrecognized assignment <%s>\n",
				x_stmnt(n->rnode));
			exit(1);
		}
		break;

	case TN_EXPR:	/* i++, i-- */
		switch (n->hdr.tok) {
		case INCR:
			if (!do_oper(n, 1)) goto bad;
			break;
		case DECR:
			if (!do_oper(n, -1)) goto bad;
			break;
		default:
			goto nogood;
		}
		break;

	default:
nogood:		err_path++;
		printf("\texec: unknown stmnt type '%s' <%s>\n",
			name_of_node(n->hdr.type),
			x_stmnt(n));
		if (n->lnode) printf("\t\tL = %s\n", name_of_node(n->lnode->hdr.type));
		if (n->rnode) printf("\t\tR = %s\n", name_of_node(n->rnode->hdr.type));
		exit(1);
	}
}

int
get_state_val(void)
{
	if (!gen_stack)
	{	nogood = 1;
		return 0;
	}
	return gen_stack->uno_state;
}

static int
dosel(treenode *m, char *nm, int allow, int forbid, int which)	/* 1:select, 2:unselect */
{	SymRef *s;
	SymList *r;
	treenode *n;
	int nonempty = 0;

	n = (m && m->hdr.type == TN_IF) ? ((if_node *)m)->cond : m;

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
		r->selected = 0;
	if (gen_stack)
	for (s = gen_stack->symrefs; s; s = s->nxt)
		s->status &= ~SELECTED;

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
	{	if (debug)
		printf(">> select saw: %s mark=%d\n",
			r->sm->nme->str, r->mark);

		if (strlen(nm) > 0
		&&  strcmp(nm, r->sm->nme->str) != 0)
			continue;

		switch (which) {
		case 1:	/* select */
			if ((r->mark & allow)
			&& !(r->mark & forbid))
			{	r->selected = 1;
				nonempty = 1;
			}
			break;

		case 2:	/* unselect */
			if (r->selected)
			{	if ((r->mark & allow)
				&& !(r->mark & forbid))
					r->selected = 0;
				else
					nonempty = 1;
			}
			break;
	}	}

	return nonempty;
}

static int
sel_args(treenode *e, treenode *n, int which)	/* 1:select(name,with,without), 2:unselect() */
{	treenode *f, *g;
	int val1, val2;

	/*	   TN_FUNC_CALL:e
		      /    \
		     /      \
		TN_IDENT  TN_EXPR_LIST:f
		   /          /         \
		select       /       TN_INT:val2
	                    /
	           TN_EXPR_LIST:g
	                  /      \
		 TN_STRING       TN_INT:val1
	      or TN_IDENT:MATCH:arg1
	 */
		if (!e->rnode
		||   e->rnode->hdr.type != TN_EXPR_LIST)
			goto bad1;
	f = e->rnode;
		if (!f->lnode
		||   f->lnode->hdr.type != TN_EXPR_LIST)
			goto bad1;
	g = f->lnode;
		if (!g->lnode || !g->rnode)
			goto bad1;
	nogood = 0;
	val1 = eval_const_expr(g->rnode, n);
	val2 = eval_const_expr(f->rnode, n);
	if (nogood || g->lnode->hdr.type != TN_STRING)
	{
bad1:		err_path++;
		fprintf(stderr, "\t\t%s:%d: error expecting string in '%s' [%d:%d]\n",
			n?n->hdr.fnm:"--",
			n?n->hdr.line:0,
			x_stmnt(e),
			nogood,
			(!nogood)?g->lnode->hdr.type:-1);
		exit(1);
	}

	user_name = ((leafnode *)g->lnode)->data.str;

	if (debug)
	printf(">>saw %s(%s,%d,%d)\n", x_stmnt(e), user_name, val1, val2);

	return dosel(n, user_name, val1, val2, which);
}

static int
doref(treenode *m, int allow, int forbid)	/* refine -- unselect nonmatches */
{	SymList *r;
	treenode *n;
	int nonempty = 0;

	n = (m && m->hdr.type == TN_IF) ? ((if_node *)m)->cond : m;

	if (n && n->hdr.defuse)
	for (r = n->hdr.defuse->other; r; r = r->nxt)
	{	if (debug)
		printf(">> refine/unselect saw: %s mark=%d\n",
			r->sm->nme->str, r->mark);

		if (r->selected)
		{	if (!(r->mark & allow)
			||   (r->mark & forbid))
				r->selected = 0;
			else
				nonempty = 1;
	}	}

	return nonempty;
}

static int
ref_args(treenode *e, treenode *n)	/* 1: refine(with,without), 2: unselect(with,without) */
{	treenode *f;
	int val1, val2;

	/*	   TN_FUNC_CALL:e
		      /    \
		     /      \
		TN_IDENT  TN_EXPR_LIST:f
		   /          /         \
		refine       /       TN_INT:val2
		     TN_INT:val1
	 */
		if (!e->rnode
		||   e->rnode->hdr.type != TN_EXPR_LIST)
			goto bad1;
	f = e->rnode;
		if (!f->lnode || !f->rnode)
			goto bad1;
	nogood = 0;
	val1 = eval_const_expr(f->lnode, n);
	val2 = eval_const_expr(f->rnode, n);
	if (nogood)
	{
bad1:		err_path++;
		fprintf(stderr, "\t\t%s:%d: error in args in '%s'\n",
			n?n->hdr.fnm:"--", n?n->hdr.line:0, x_stmnt(e));
		exit(1);
	}

	if (debug)
	printf(">>saw %s(%s,%d,%d,%d)\n", x_stmnt(e), user_name, user_val, val1, val2);

	return doref(n, val1, val2);
}

static int
domatch(treenode *n, int mark, int allow, int forbid, int which)	/* 1: match, 2: marked */
{	SymRef *s;
	SymList *r;
	int nonempty = 0;

	/* select names in dfstack that match selection in defuse */

	if (!n || (which != 2 && !n->hdr.defuse))
		return 0;

	if (debug)
	printf("domatch mark=%d, allow=%d, forbid=%d, which=%d\n",
		mark, allow, forbid, which);

	for (s = gen_stack->symrefs; s; s = s->nxt)
	{	if (debug)
		printf(">> stack: %s s_val=%d status=%d\n",
			s->sm->nme->str, s->s_val, s->status);

		if (s->s_val == mark
		&&  (s->status & allow)
		&& !(s->status & forbid))
		{	if (which == 2)	/* marked */
			{	if (s->s_val == mark
				&&  (s->status & allow)
				&& !(s->status & forbid))
				{	s->status |= SELECTED;
					if (debug) printf("	YES marked\n");
					nonempty = 1;
				}
			} else		/* match */
			{	for (r = n->hdr.defuse->other; r; r = r->nxt)
					if (r->selected
					&&  strcmp(r->sm->nme->str, s->sm->nme->str) == 0)
					{	s->status |= SELECTED;
						nonempty = 1;
						if (debug) printf("	YES matched\n");
						break;
		}	}		}
	}
	return nonempty;
}

static int
match_args(treenode *e, treenode *n, int which)	/* 1:match(mark,with,without) 2:marked(x,with,without) */
{	treenode *f, *g;
	int val1, val2, mark;

	/*	   TN_FUNC_CALL:e
		      /    \
		     /      \
		TN_IDENT  TN_EXPR_LIST:f
		   /          /         \
		match        /       TN_INT:val2
	           TN_EXPR_LIST:g
	                  /      \
		  TN_INT:mark    TN_INT:val1
	 */
		if (!e->rnode
		||   e->rnode->hdr.type != TN_EXPR_LIST)
			goto bad1;
	f = e->rnode;
		if (!f->lnode
		||   f->lnode->hdr.type != TN_EXPR_LIST)
			goto bad1;
	g = f->lnode;
		if (!g->lnode || !g->rnode)
			goto bad1;
	nogood = 0;
	val1 = eval_const_expr(g->rnode, n);
	val2 = eval_const_expr(f->rnode, n);
	mark = eval_const_expr(g->lnode, n);
	if (nogood)
	{
bad1:		err_path++;
		fprintf(stderr, "\t\t%s:%d: error match_args in '%s'\n",
			n?n->hdr.fnm:"--", n?n->hdr.line:0, x_stmnt(e));
		exit(1);
	}

	if (debug)
	{	err_path++;
		printf("%3d>>saw %s(%s,%d,%d)\n", depth, x_stmnt(e), user_name, val1, val2);
		err_path--;
	}
	return domatch(n, mark, val1, val2, which);
}

int
eval_fct(treenode *e, treenode *n)
{	leafnode *leaf;
	int i, val1, val2;

	if (!e) return 0;

	if (e->lnode->hdr.type != TN_IDENT)
	{
bad1:		err_path++;
		fprintf(stderr, "eval_fct:\n\t%s:%d: expect ident for fctname, got %s in %s\n",
			n?n->hdr.fnm:"--",
			n?n->hdr.line:0,
			name_of_node(e->lnode->hdr.type), x_stmnt(e));
		exit(1);
	}

	leaf = (leafnode *) e->lnode;
	if (strcmp(leaf->data.sval->str, endname) == 0)
		return path_ends;

	if (strcmp(leaf->data.sval->str, callname) == 0)
	{	if (e->rnode
		&&  e->rnode->hdr.type == TN_STRING)
		{	leaf = (leafnode *) e->rnode;

			if (debug) printf("saw %s(%s)\n", callname, leaf->data.str);

			return has_ident(n, leaf->data.str);
		}
		goto bad1;
	}

	if (strcmp(leaf->data.sval->str, selname) == 0)
		return sel_args(e, n, 1);

	if (strcmp(leaf->data.sval->str, refname) == 0)
		return ref_args(e, n);

	if (strcmp(leaf->data.sval->str, excname) == 0)
		return sel_args(e, n, 2);

	if (strcmp(leaf->data.sval->str, matchname) == 0)
		return match_args(e, n, 1);

	if (strcmp(leaf->data.sval->str, markedname) == 0)
		return match_args(e, n, 2);

	for (i = 0; i < (int) (sizeof(evals)/sizeof(struct Cmd)); i++)
		if (strcmp(leaf->data.sval->str, evals[i].cmd) == 0)
		{
			val1 = val2 = 0;	/* set defaults */
			nogood = 0;

			if (strncmp(evals[i].cmd, "known_", strlen("known_")) == 0)
				goto doit;	/* no args */

			/* everything else has two args */

			if (!e->rnode
			||   e->rnode->hdr.type != TN_EXPR_LIST)
			{
bad2:				fprintf(stderr, "uno: bad fct args %s(%s)\n",
					evals[i].cmd, x_stmnt(e->rnode));
				exit(1);
			}

			val1 = eval_const_expr(e->rnode->lnode, n);
			val2 = eval_const_expr(e->rnode->rnode, n);
doit:			if (nogood) goto bad2;

			hit_fcts[i]++;
			if (debug) printf("saw %s(%d,%d)\n", evals[i].cmd, val1, val2);
			return evals[i].fn(n, val1, val2);
		}
	goto bad1;
}

static int
eval_step(treenode *e, treenode *v, treenode *n)
{	leafnode *leaf;
	int val, arg1_val = -1;

	uno_assert(e && v, "bad call to eval_step");

	if (debug)
	{	printf("\teval %s <%s> ",
			name_of_node(e->hdr.type),
			x_stmnt(e));
		printf(":: %s <%s>\n",
			name_of_node(v->hdr.type),
			x_stmnt(v));
	}
	switch (e->hdr.type) {
	case TN_IDENT:
		leaf = (leafnode *) e;
		if (strcmp(leaf->data.sval->str, statename) != 0)
		{	printf("\t\texpected '%s', saw %s\n",
				statename, leaf->data.sval->str);
			exit(1);
		}
		arg1_val = gen_stack->uno_state;
		if (debug) printf("\t\targ1 %s (==%d)\n",
				leaf->data.sval->str, arg1_val);
		break;

	case TN_FUNC_CALL:
		arg1_val = eval_fct(e, n);
		break;

	case TN_EXPR:
		nogood = 0;
		arg1_val = eval_const_expr(e, n);
		if (nogood)
		{	printf("\t\tbad expression (%s == ?), saw %s <%s>\n",
				statename, name_of_node(e->hdr.type), x_stmnt(e));
			exit(1);
		} else
		{	if (debug) printf("\t\targ1 = %d\n", arg1_val);
		}
		break;
	default:
		printf("\t\targ1 expecting func_call or ident, saw %s <%s>\n",
			name_of_node(e->hdr.type), x_stmnt(e));
		exit(1);
	}

	switch (v->hdr.type) {
	case TN_IDENT:
		leaf = (leafnode *) v;

		if (debug) printf("\t\targ2 = %s\n", leaf->data.sval->str);

		if (strcmp(leaf->data.sval->str, "_true_") == 0)
		{	if (arg1_val) goto yes; else goto no;
		} else if (strcmp(leaf->data.sval->str, "_false_") == 0)
		{	if (arg1_val) goto no; else goto yes;
		} else if (strcmp(leaf->data.sval->str, statename) == 0)
		{	if (arg1_val == gen_stack->uno_state) goto yes;
			goto no;
		}
		printf("\t\texpected true, false, or %s, saw %s\n",
			statename, leaf->data.sval->str);			
		break;

	case TN_EXPR:
		nogood = 0;
		val = eval_const_expr(v, n);
		if (!nogood)
		{	if (debug) printf("\t\targ2 = %d\n", val);
			if (arg1_val == val) goto yes;
			goto no;
		}
		printf("\t\tbad expression arg2 = ?, saw <%s>\n", x_stmnt(v));
		break;
	default:
		printf("\t\targ2 expecting expr or ident, saw %s\n",
			name_of_node(v->hdr.type));
		break;
	}

	if (debug) printf("Don't Know\n");
	exit(1);
yes:
	if (debug) printf("Yes\n");
	return 1;
no:
	if (debug) printf("No\n");
	return 0;
}

static State *
exec_lastfirst(State *s, Trans *t, treenode *e, treenode *n)
{	State *x;

	if (!t || !t->branch)
	{	if (debug>1) printf("\t(%d) lastfirst. no branch\n", s->n->hdr.line);
		return ZS;
	}

	if ((x = exec_lastfirst(s, t->nxt, e, n)) != NULL)	/* assign x */
	{	if (debug>1) printf("\t(%d) lastfirst. gottcha\n", s->n->hdr.line);
		return x;
	}

	if (e && !eval_step(e, t->cond, n))
	{	if (debug>1) printf("\t(%d) lastfirst. fail eval\n", s->n->hdr.line);
		return ZS;
	}

	if (debug>1) printf("\t(%d) lastfirst. pass eval\n", s->n->hdr.line);

	return t->branch;
}

static void
exec_prop(State *s, treenode *n)
{	treenode *exp = ZT;
	State *ns = ZS;

	if (!s) return;

	if (debug) printf("exec_prop %s:%d: %s <%s>\n",
			s->n->hdr.fnm,
			s->n->hdr.line,
			name_of_node(s->n->hdr.type),
			x_stmnt(s->n));

	s->visited = 1;	/* to determine effective coverage of property */

	if (s->iscond && s->n)
	{	exp = (s->n->hdr.type == TN_IF) ? ((if_node *)s->n)->cond : s->n;
		ns = exec_lastfirst(s, s->succ, exp, n);	/* eval_step(exp) */
	} else
	{	exec_step(s->n, n);
		if (s->succ) ns = s->succ->branch;
	}

	exec_prop(ns, n);
}

void
dfs_generic(State *s)
{	GenStack *g;
	Trans *t;
	SymRef *r;
	treenode *exp = ZT;
	int any_added = 0;

	if (!s || !s->n) return;

	depth++;

	if (debug)
	{	printf("%3d: dfs %s:%d: <%s>\t",
			depth,
			s->n->hdr.fnm,
			s->n->hdr.line,
			x_stmnt(s->n));
		if (s->n->hdr.type == TN_IF)
			dump_defuse(((if_node *)s->n)->cond->hdr.defuse, stdout);
		else
			dump_defuse(s->n->hdr.defuse, stdout);
		printf("\n");
		if (gen_stack)
		for (r = gen_stack->symrefs; r; r = r->nxt)
			printf("\tGenStack %s %d\n", r->sm->nme->str, r->status);

	}

	if (s->iscond && s->n)
	exp = (s->n->hdr.type == TN_IF) ? ((if_node *)s->n)->cond : s->n;

	any_added = gen_push(s);	/* checks symrefs to state snapshot -- updates snapshot*/
	g = gen_stack;
	g->e = exp?exp:s->n;

	path_ends = !(s->succ && s->succ->branch);

	user_val = 0;
	user_name = "";
	exec_prop(uno_prop, g->e);	/* can modify uno_state/symrefs */

	if (g->uno_state >= (int) sizeof(unsigned long)*8)
	{	fprintf(stderr, "uno: too many states in property (max %d)\n",
			(int) sizeof(unsigned long)*8 - 1);
		exit(1);
	}

	if (debug)
		printf("\t%s = %d (stack) %lu (state-bits)\n",
			statename,
			g->uno_state,
			s->uno_state);

	if (any_added == 0 && (s->uno_state & (1 << g->uno_state)))
	{	if (s->visited)
		{	if (debug) printf("\told\n");
			goto pop;
		} else
		{	if (debug) printf("\tnew\n");
		}
	} else
	{	if (debug)
			printf("\t%s\n", s->visited?"revisit":"new");
	}
	s->uno_state |= (1<<g->uno_state);	/* updates uno_state snapshot */
	s->visited = 1;

	for (t = s->succ; t && t->branch; t = t->nxt)
		if (!infeasible(exp, t->cond))	/* e.g. 0 == _true_ */
		{	g->c = t->cond;
			dfs_generic(t->branch);
		}

pop:	gen_pop(g);

	if (debug)
	{	printf("%3d: dfs up\n", depth);
		if (gen_stack)
		for (r = gen_stack->symrefs; r; r = r->nxt)
			printf("\tGenStack %s %d\n", r->sm->nme->str, r->status);
	}
	
	depth--;
}

void
gen_reset(void)
{
	gen_stack = (GenStack *) 0;
	witness = (treenode *) 0;
	ruledout = 0;
}
