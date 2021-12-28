/***** uno: uno_fcts.c *****/

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
#include <malloc.h>
#include <ctype.h>
#include "dtags.h"
#include "uno_fcts.h"

extern int	longtrace, verbose;
static int	debug = 0;

static BFct	*fcts = (BFct *) 0, *prop_fct = (BFct *) 0;
static BSym	*free_sym = (BSym *) 0;
static NList	*free_n = (NList *) 0;
static Node	*prop_start = (Node *) 0;
static Pool	*free_pool = (Pool *) 0;
static Pool	*pool[512];
static Report	*report = (Report *) 0;
static Rstack	*rstack = (Rstack *) 0, *free_rstack = (Rstack *) 0;
static Stack	*stack = (Stack *) 0, *free_stack = (Stack *) 0, init;
static VList	*free_v = (VList *) 0;
static Var	*free_var = (Var *) 0;
static char	*glob_prop = "uno_check";
static int	ErrCnt = 1;
static int	depth = 0, oid = 0, tabs = 0;

static void	check_prop(Arc *);
static void	end_of_path(void);

extern void	handle_fct(char *);
extern void	add_fct(char *);
extern void	*emalloc(size_t);
extern void	add_call(char *, char *);
extern void	add_glob_defs(void);

static char *BuiltinCheck[] = {
	": uno_check	0",
	">1>",
	">2>",
	"[select('',1,0) == _true_]",		/* if (select("", DEF, NONE)) */
	">3>",
	"[mark(1)]",				/*	mark(1);                 */
	">4>",
	"[select('',68,0) == _true_]",		/* if (select("", USE|DEREF, NONE)) */
	">5>",
	"[match(1,1,0) == _true_]",		/* if (match(1, DEF, NONE))    */
	">6>",
	"[no_error()]",				/*	no_error();              */
	"<5<",
	"<4<",
	">7>",
	"[match(1,1,0) == _false_]",		/* else */
	">8>",
	"[known_nonzero() == _true_]",		/*	if (known_nonzero()) */
	"{6}",
	"[no_error()]",				/*		no_error();  */
	"<8<",
	"<7<",
	">9>",
	"[known_nonzero() == _false_]",		/* 	else                 */
	"{6}",
	"[error('possible global use or deref before def')]", /*	error(); */
	"<9<",
	"<7<",
	"<4<",
	"<3<",
	"{6}",
	"[select('',68,0) == _false_]",
	"<3<",
	"<2<",
	"<1<",
	"{3}",
	"[select('',1,0) == _false_]",
	"<1<",
	"<0<",
	0
};

static void
builtin_check(void)
{	int i;

	add_fct(glob_prop);
	for (i = 0; BuiltinCheck[i]; i++)
		handle_fct(BuiltinCheck[i]);
}

static char *
new_str(char *s)
{	Pool *p;
	char *t;
	int n;

	n = strlen(s);
	if (n > 0 && n < 512 && pool[n])
	{	p = pool[n];
		pool[n] = p->nxt;
		p->nxt = free_pool;
		free_pool = p;
		t = p->s;
	} else
		t = (char *) emalloc(n+1);
	strcpy(t, s);
	return t;
}

static Var *
new_var(char *s)
{	Var *f;

	if (free_var)
	{	f = free_var;
		free_var = f->nxt;
		memset(f, 0, sizeof(Var));
	} else
		f = (Var *) emalloc(sizeof(Var));

	f->s = new_str(s);
	return f;
}

static BSym *
new_sym(char *s)
{	BSym *f;

	if (free_sym)
	{	f = free_sym;
		free_sym = f->nxt;
		memset(f, 0, sizeof(BSym));
	} else
		f = (BSym *) emalloc(sizeof(BSym));

	f->s = new_str(s);
	return f;
}

static BSym *
rev_symrel(BSym *s)
{	int n;

	if (!s) return (BSym *) 0;
	rev_symrel(s->nxt);

	n = strlen(s->s);
	if (n > 0 && n < 512)
	{	Pool *p;
		if (free_pool)
		{	p = free_pool;
			free_pool = p->nxt;
			memset(p, 0, sizeof(Pool));
		} else
			p = (Pool *) emalloc(sizeof(Pool));
		p->s = s->s;
		p->nxt = pool[n];
		pool[n] = p;
	}
	s->s = (char *) 0;

	s->nxt = free_sym;
	free_sym = s;

	return (BSym *) 0;
}

static Var *
rev_release(Var *v)
{	int n;

	if (!v) return (Var *) 0;
	rev_release(v->nxt);

	n = strlen(v->s);
	if (n > 0 && n < 512)
	{	Pool *p;
		if (free_pool)
		{	p = free_pool;
			free_pool = p->nxt;
			memset(p, 0, sizeof(Pool));
		} else
			p = (Pool *) emalloc(sizeof(Pool));
		p->s = v->s;
		p->nxt = pool[n];
		pool[n] = p;
	}
	v->s = (char *) 0;

	v->nxt = free_var;
	free_var = v;

	return (Var *) 0;
}

static BFct *
find_function(char *s)
{	BFct *f;

	for (f = fcts; f; f = f->nxt)
		if (strcmp(f->fnm, s) == 0)
			return f;
	return (BFct *) 0;
}

void
add_fct(char *s)
{	BFct *f;

	if (0 && debug) printf("adding fct %s\n", s);

	for (f = fcts; f; f = f->nxt)
		if (strcmp(f->fnm, s) == 0)
			return;	/* reported in uno_global.c */

	f = (BFct *) emalloc(sizeof(BFct));
	f->fnm = new_str(s);
	f->nxt = fcts;
	fcts = f;

	f->root = (Node *) emalloc(sizeof(Node));
	f->root->nid = 0;
	return;
}

void
add_call(char *fnm, char *c)
{	BFct *f;
	BSym *s;

	f = find_function(fnm);
	if (!f)
	{	fprintf(stderr, "error: bad input sequence (%s)\n",
			fnm);
		exit(1);
	}

	for (s = f->calls; s; s = s->nxt)
		if (strcmp(s->s, c) == 0)
			return;

	s = (BSym *) emalloc(sizeof(BSym));
	s->s = new_str(c);
	s->nxt = f->calls;
	f->calls = s;
}

extern int indirect_calls(char *);

void
find_roots(void)
{	BFct *f, *g;
	BSym *h;
	int ncalls;

	for (f = fcts; f; f = f->nxt)
	{	if (strcmp(f->fnm, "_global_") == 0)
			continue;
		ncalls = 0;
		for (g = fcts; g; g = g->nxt)
		{	if (g != f)
			{	for (h = g->calls; h; h = h->nxt)
				{	if (strcmp(h->s, f->fnm) == 0)
					{	ncalls++;
						break;
				}	}
				if (ncalls > 0)
				{	break;
		}	}	}
		if (ncalls == 0 && indirect_calls(f->fnm) == 0)
			printf("root: %s\n", f->fnm);
	}
	fflush(stdout);
}

static Node *
find_node(BFct *f, int id)
{	Node *n;

	for (n = f->root; n; n = n->nxt)
		if (n->nid == id)
			break;

	if (!n)
	{	n = (Node *) emalloc(sizeof(Node));
		n->nid  = id;
		n->nxt  = f->root;
		f->root = n;
	}
	return n;
}

static Arc *
add_arc(BFct *f, int from, int to)
{	Arc *a;
	Node *n;

	a = (Arc *) emalloc(sizeof(Arc));
	n = find_node(f, from);
	a->to   = find_node(f, to);
	a->nxt  = n->succ;
	n->succ = a;

	return a;
}

static void
add_label(BFct *f, Arc *a, char *s)
{	Label *n;
	char  *p;

	while ((p = strchr(s, '\t')) != NULL)
		*p = ' ';

	n = (Label *) emalloc(sizeof(Label));
	n->label = (unsigned char *) new_str(s);

	if (strcmp(f->fnm, glob_prop) == 0)
	{	n->nxt = a->lab;	/* prop: labels on arcs */
		a->lab = n;
		return;
	} else
	{	n->nxt = a->to->lab;	/* sys: labels on nodes */
		a->to->lab = n;
	}

	if (strlen(s) <= 2)
		return;

	switch (s[1]) {
	case ' ':	p = strchr(&s[2], ' '); break;
	case '\t':	p = strchr(&s[2], '\t'); break;
	default:
bad:		fprintf(stderr, "uno:global: unexpected type of label: '%s'\n", s);
		return;
	}

	if (!p) goto bad;
	*p = '\0';
	switch (s[0]) {
	case 'C': 
	case 'c': 
	case 'b': 
	case 'h': 
	case 'i': 
	case 'j':
		/* add_call(f->fnm, &s[2]); */
		break;
	case 'N':
	case 'G':
	case 'D':
	case 'U':
	case 'R': break;
	default : goto bad;
	}
	*p = ' ';	/* restore */
}

static void
ini_prop(void)
{	Node *n;

	prop_fct = find_function(glob_prop);
	if (!prop_fct)
	{	if (verbose)
			printf("uno:global: using builtin property check\n");
		builtin_check();
		prop_fct = find_function(glob_prop);
		if (!prop_fct)
		{	fprintf(stderr, "uno:global: error, could not load builtin property\n");
			exit(1);
		}
	}
	n = find_node(prop_fct, 0);
	if (n && n->succ)
		prop_start = n->succ->to;
}

static BFct *
fct_in_lab(char *s)
{	BFct *f = (BFct *) 0;
	char *t;

	for (t = s+2; *t != '\0' && *t != ' '; t++)
		;

	if (*t == ' ')
	{	*t = '\0';
		f = find_function(s+2); /* 2 char prefix */
		*t = ' ';
	}
	return f;
}

static int
n_reported(Stack *s)
{	Report *r;
	int n;

	if (s && s->move && s->move->to)
		n = s->move->to->nid;
	else
		return 0;

	for (r = report; r; r = r->nxt)
		if (r->n > n-3
		&&  r->n < n+3)	/* within a range of subsequent states */
			return 1;
	r = (Report *) emalloc(sizeof(Report));
	r->n = n;
	r->nxt = report;
	report = r;

	if (debug) printf("NID=%d\n", n);

	return 0;
}

static int
print_fnm(Rstack *s, char *p)
{
	if (!s) return 0;

	if (s->n && s->n->lab)
		printf("	%s %s\n", p, &s->n->lab->label[2]);
	else if (strcmp(s->f->fnm, "_global_") != 0)
		printf("	%s %s()\n", p, s->f->fnm);
	return 1;
}

static void
print_rstack(Rstack *s, char *p)
{
	if (print_fnm(s, p))
		print_rstack(s->nxt, p);
}

static void
print_stack(Stack *s, int d)
{	Arc *a;
	int i;

	if (!s) return;
	print_stack(s->nxt, d-1);

	a = s->move;

	if (a
	&&  a->to->lab
	&&  strlen((char *) a->to->lab->label) > 0)
	{	for (i = 0; i < tabs; i++)
			printf("   ");
		printf("%3d:\t[%d]\t%s\n", d,
			a->to->nid, a->to->lab->label);
	}

	if (s->fc)
	{	tabs++;
		for (i = 0; i < tabs; i++)
			printf("   ");
		printf("%3d: BFct call to %s\n", d, s->fc->fnm);
	}
	if (s->fr)
	{	for (i = 0; i < tabs; i++)
			printf("   ");
		tabs--;
		printf("%3d: Return to %s\n", d, s->fr->fnm);
	}
}

static void
do_fct_call(BFct *f, Node *sys)
{	Rstack *r, *or;
	BFct *g;
	BSym *s;
	Node *n;

	f->visited = 1;	/* prevent fct call cycles */

	if (free_rstack)
	{	r = free_rstack;
		free_rstack = free_rstack->nxt;
		memset(r, 0, sizeof(Rstack));
	} else
		r = (Rstack *) emalloc(sizeof(Rstack));

	r->f = f;
	r->n = sys;	/* continuation point for return from fct in end_of_path */
	r->nxt = rstack;
	rstack = r;

	stack->fc = f;	/* remember for error trace */

	n = find_node(f, 0);
	if (n && n->succ)
	{	if (debug) printf("%3d: dive in\n", depth);
		check_prop(n->succ);
		if (debug) printf("%3d: undive\n", depth);
	} else
	{	if (debug) printf("%3d: no visible operations (calls: %p)\n", depth, f->calls);

		/* if we're here, then probably f->calls is also nil, or else
		 * there would be an abstract call graph for this fct with the
		 * call points recorded...
		 */

		if (!f->calls)	/* expected */
		{	end_of_path();	/* continuation with sys */
		} else
		{	fprintf(stderr, "%3d: unexpected...\n", depth);
			for (s = f->calls; s; s = s->nxt)
			{	g = find_function(s->s);
				if (g && !g->visited)
				{	if (debug) printf("	ByPass Call on %s\n", s->s);
					do_fct_call(g, (Node *) 0); /* no continuation within this fct */
					if (debug) printf("	Return from ByPass Call on %s\n", s->s);
	}	}	}	}

	stack->fc = (BFct *) 0;

	or = rstack;
	rstack = rstack->nxt;
	or->nxt = free_rstack;
	free_rstack = or;

	f->visited = 0;
}

static int
same_markings(Vis *v)
{	Var   *p;
	VList *q;
	int cnt = 0;

	if (!v->v && !stack->sels)
	{	if (v->zeromarks)
			return 1;
		v->zeromarks = 1;
		return 0;
	}

	for (p = stack->sels; p; p = p->nxt)
	{	for (q = v->v; q; q = q->nxt)
		{	if (strcmp(q->v->s, p->s) == 0
			&&  q->v->mark == p->mark)
				break;
		}
		if (!q)	/* add p */
		{	if (free_v)
			{	q = free_v;
				free_v = q->nxt;
				memset(q, 0, sizeof(VList));
			} else
				q = (VList *) emalloc(sizeof(VList));
			
			q->v = new_var(p->s);
			q->v->mark = p->mark;
			q->nxt = v->v;
			v->v = q;
			cnt++;
	}	}

	return (cnt == 0);
}

static int
same_callpts(Vis *v)
{	Rstack *p;
	NList *q;
	int cnt = 0;

	if (!v->r && !rstack)
	{	if (v->zerostack)
			return 1;
		v->zerostack = 1;
		return 0;
	}

	for (p = rstack; p; p = p->nxt)
	{	for (q = v->r; q; q = q->nxt)
		{	if (p->n == q->n)
				break;
		}
		if (!q)	/* add p->n */
		{	if (free_v)
			{	q = free_n;
				free_n = q->nxt;
				memset(q, 0, sizeof(NList));
			} else
				q = (NList *) emalloc(sizeof(NList));
			q->n = p->n;
			q->nxt = v->r;
			v->r = q;
			cnt++;
	}	}

	return (cnt == 0);
}

static int
same_unostate(Vis *v)
{
	if (v->uno_state & (1<<stack->uno_state))
		return 1;
	v->uno_state |= (1<<stack->uno_state);
	return 0;
}

static int
same_state(Arc *in)
{	Stack	*s;
	Var	*e, *f;
	BSym	*x, *y;
	Node	*sys = in->to;

	if (!sys->vis)
		sys->vis = (Vis *) emalloc(sizeof(Vis));

	if (same_unostate(sys->vis)
	&&  same_callpts(sys->vis)
	&&  same_markings(sys->vis))
		return 1;			/* been here before with that state */

	if (free_stack)
	{	s = free_stack;
		free_stack = s->nxt;
		memset(s, 0, sizeof(Stack));
	} else
		s = (Stack *) emalloc(sizeof(Stack));
	s->move = in;
	s->uno_state = stack->uno_state;

	for (e = stack->sels; e; e = e->nxt)		/* copy marked vars forward */
	{	f = new_var(e->s);
		f->loc = e->loc;
		f->sel = 0;
		f->stat = e->stat;
		f->mark = e->mark;
		f->nxt = s->sels;
		s->sels = f;
	}
	for (x = stack->knz; x; x = x->nxt)
	{	y = new_sym(x->s);
		y->nxt = s->knz;
		s->knz = y;
	}

	s->nxt = stack;
	stack = s;					/* stack trace for error reports */

	return 0;
}

static void
end_of_path(void)
{	Arc	*a;
	Rstack	*r;

	if (!rstack) return;

	r = rstack;
	rstack = rstack->nxt;

	stack->fr = rstack?rstack->f:(BFct *) 0;	/* remember for error traces */

	if (debug)
	printf("%3d:\tFCT EXITS -- %s -- return to %s\n", depth,
		r->f->fnm, rstack?rstack->f->fnm:"--");

	if (!r->n || !r->n->succ)		/* no continuation point */
	{	if (debug) printf("%3d: no continuation point\n", depth);
		end_of_path();			/* ? */
	} else
		for (a = r->n->succ; a; a = a->nxt)	/* continuation in caller */
		{	if (debug) printf("%3d:\tCONTinuation in %s [%d->%d]\n", depth,
				rstack?rstack->f->fnm:"--", r->n->nid, a->to->nid);
			check_prop(a);
			if (debug) printf("%3d:\tUN_CONT %s [%d->%d]\n", depth,
				rstack?rstack->f->fnm:"--", a->to->nid, r->n->nid);
		}
	r->nxt = rstack;
	rstack = r;

	stack->fr = (BFct *) 0;

	if (debug)
	printf("%3d:\tFCT UN_EXITS -- %s\n", depth, r->f->fnm);
}

static void
f2d_assert(int p, char *s)
{
	if (!p)
	{	printf("uno:global: %s\n", s);
		exit(1);
	}
}

static int
has_fct_match(Label *n, Label *m)
{	char *p, *q = (char *) 0, *r, *s = (char *) 0;
	char took = '(';
	char c = '\"';
	int t;

	if (strncmp((char *) n->label, "C ", strlen("C ")) == 0
	||  strncmp((char *) n->label, "c ", strlen("c ")) == 0)
	{	/* either: fct_call("qlock()") or fct_call("qlock") */
		p = strchr((char *) m->label, c);	/* start of fct name */

		if (p)
		{	q = strchr(p+1, '(');	/* has () */
		} else
		{	c = '\'';		/* single quotes? */
			p = strchr((char *) m->label, c);
			if (!p) return 0;	/* give up */
			q = strchr(p+1, '(');
		}

		if (!q)
		{	q = strchr(p+1, c);	/* no (), find closing quote */
			took = c;
		}
	
		r = (char *) &(n->label[2]);
		if (r) s = strchr(r+1, ' ');

		f2d_assert((int) (p && q && r && s && q > p+1), "bad fct_call() arg");

		*q = *s = '\0';
		t = (strcmp(p+1, r) == 0);
		*q = took; *s = ' ';	/* restore */
		if (t) return 1;
	}
	return 0;
}

static void
unselect(void)
{	Var *v;

	if (stack)
	for (v = stack->sels; v; v = v->nxt)
		v->sel = 0;

	if (debug) printf("UnSeLecting\n");
}

void
set_select(char *name, char *loc, int stat)
{	Var *v;

	for (v = stack->sels; v; v = v->nxt)
		if (strcmp(v->s, name) == 0)
		{	v->sel  |= 1;
			v->stat |= stat;
			if (debug) printf("	>Select old '%s' - stat %d\n", v->s, v->stat);
			return;
		}
	v = new_var(name);
	v->loc = new_str(loc);
	v->sel = 1;
	if (debug) printf("	>Select new '%s', stat %d\n", v->s, stat);
	v->stat = stat;
	v->nxt = stack->sels;
	stack->sels = v;
}

int
mark_select(int x)
{	Var *v;
	int cnt = 0;

	for (v = stack->sels; v; v = v->nxt)
		if (v->sel)
		{	v->mark = x;
			cnt++;
			if (debug) printf("\tset mark %s to %d\n", v->s, x);
		}
	return cnt;
}

static void
list_sel(void)
{	Var *v;

	for (v = stack->sels; v; v = v->nxt)
		if (v->sel)
		printf("%3d:\t\tvars: %s (%s), mark %d, selection %d\n",
			depth, v->s, v->loc, v->mark, v->sel);
}

static int
has_sel_match(Label *n, int match, int dont)
{	char *r, *s;
	int typ = 0;

	if (strlen((char *) n->label) <= 2
	||  n->label[1] != ' ')
		return 0;

	switch (n->label[0]) {
	case 'G':
		if (!(match & (DECL|DEF)) || (dont & (DECL|DEF))) return 0;
		typ = DECL|DEF;
		break;
	case 'D':
		if (!(match & DEF) || (dont & DEF)) return 0;
		typ = DEF;
		break;
	case 'U':
		if (!(match & USE) || (dont & USE)) return 0;
		typ = USE;
		break;
	case 'R':
		if (!(match & DEREF) || (dont & DEREF)) return 0;
		typ = DEREF;
		break;
	default:
		return 0;
	}

	r = (char *) &(n->label[2]);
	s = strchr(r+1, ' ');

	if (!(r && s && s > r)) fprintf(stderr, "bad label: '%s' -- %p %p\n", n->label, r, s);
	f2d_assert((int) (r && s && s > r), "bad sel match");
	*s = '\0';
	set_select(r, s+1, typ); /* r = name, s+1 = location */
	*s = ' ';	/* restore */

	return 1;
}

static int
has_ref_match(int mark, int match, int dont)
{	Var *v;
	int hasmatch = 0;

	if (debug)
	for (v = stack->sels; v; v = v->nxt)
		printf("\tSel: '%s', stat %d, mark %d -- looking for mark %d, +%d -%d\n",
			v->s, v->stat, v->mark, mark, match, dont);

	for (v = stack->sels; v; v = v->nxt)
		if (v->sel == 1
		&&  v->mark == mark
		&& (v->stat & match)
		&& !(v->stat & dont))
		{	hasmatch = 1;
			break;
		}

	if (hasmatch)
	for (v = stack->sels; v; v = v->nxt)
		if (v->sel == 1
		&& (v->mark != mark
		|| !(v->stat & match)
		||  (v->stat & dont)))
			v->sel = 0;

	return hasmatch;
}

static void
notyet(Label *m, char *s)
{
	fflush(stdout);
	fprintf(stderr, "uno:global: unhandled type of label '%s' (%s)\n", m->label, s);
	exit(1);
}

static int
known_nz(void)
{	Var *v;
	BSym *s;

	for (v = stack->sels; v; v = v->nxt)
	{	if (v->sel == 1)
		{	if (debug) printf("	is %s known_nonzero? ", v->s);
			for (s = stack->knz; s; s = s->nxt)
				if (strcmp(v->s, s->s) == 0)
				{	if (debug) printf("yes!\n");
					break;
				}
			if (!s)
			{	if (debug)
				{	printf("no!\n");
					for (s = stack->knz; s; s = s->nxt)
						printf("	knownonzero: %s\n", s->s);
				}
				return 0;
			}
		}
	}
	if (debug) printf("all selected vars known nonzero\n");
	return 1;
}

extern int      suppress(char *, int);

static int
take_action(Label *m)
{	char *p, *q;
	Label *lb;
	int x, y;
	char c = '\"';

	if (strncmp((char *) m->label, "error(", strlen("error(")) == 0)
	{	p = strchr((char *) m->label, c);
		if (p)
		{	q = strchr(p+1, c);
		} else
		{	c = '\'';
			p = strchr((char *) m->label, c);
			if (!p) return 0;
			q = strchr(p+1, c);
		}
		f2d_assert((int) (p && q && q > p+1), "bad error() arg");
		*q = '\0';

		if (n_reported(stack))
			goto shortcut;

		printf("uno:#%d: %s", ErrCnt++, p+1);
		if (stack->move)
		for (lb = stack->move->to->lab; lb; lb = lb->nxt)
			if (strlen((char *) lb->label) > 0)
				printf(": [%s]", lb->label);
		printf("\n");

		if (print_fnm(rstack, "in fct"))
		print_rstack(rstack->nxt, "called from");

		if (debug) list_sel();

		if (longtrace)
		{	printf("Trace Detail (length %d):\n", depth);
			tabs = 0;
			print_stack(stack, depth);
			printf("\n");
		}
shortcut:		*q = c;
		if (debug) printf("	STOP '%s'\n", m->label);
		if (debug) exit(0);
		return 0;	/* i.e., stop search along this path */
	}

	if (strncmp((char *) m->label, "mark(", strlen("mark(")) == 0)
	{	x = strlen("mark(");
		if (!isdigit(m->label[x])) notyet(m, "arg to mark()");
		x = atoi((char *) &(m->label[x]));
		y = mark_select(x);
		if (debug) printf("	mark '%d' [cnt=%d]\n", x, y);
		return 1;
	}
	if (strncmp((char *) m->label, "unmark()", strlen("unmark()")) == 0)
	{	y = mark_select(0);
		if (debug) printf("	unmark [cnt=%d]\n", y);
		return 1;
	}
	if (strncmp((char *) m->label, "list()", strlen("list()")) == 0)
	{	list_sel();
		if (debug) printf("	list\n");
		return 1;
	}
	if (strncmp((char *) m->label, "no_error()", strlen("no_error()")) == 0)
	{	p = strchr((char *) m->label, c);
		if (p)
		{	q = strchr(p+1, c);
			f2d_assert((int) (p && q && q > p+1), "bad no_error() arg");
			*q = '\0';
			printf("%s", p+1);
			*q = c;
		} else
		{	c = '\'';
			p = strchr((char *) m->label, c);
			if (!p) return 0;
			q = strchr(p+1, c);
			f2d_assert((int) (p && q && q > p+1), "bad no_error() arg");
			*q = '\0';
			printf("%s", p+1);
			*q = c;
		}
		if (debug) printf("	no_error\n");
		return 1;
	}

	/* other types of stmnts, e.g., uno_state++, uno_state--, uno_state = N */
	if (strncmp((char *) m->label, "uno_state--", strlen("uno_state--")) == 0)
		stack->uno_state--;
	else if (strncmp((char *) m->label, "uno_state++", strlen("uno_state++")) == 0)
		stack->uno_state++;
	else if (strncmp((char *) m->label, "uno_state=", strlen("uno_state=")) == 0
	     && isdigit(m->label[strlen("uno_state=")]))
		stack->uno_state = atoi((char *) &(m->label[strlen("uno_state=")]));
	else
		notyet(m, "expecting uno_state = N");

	if (debug) printf("\taction '%s' (uno_state = %d)\n", m->label, stack->uno_state);
	return 1;
}

static int
act_cond(Label *m, int t)	/* match or non_zero -- conditionals indep of sys labels */
{	int ret = 0;
	int x, y, z;
	int truth = t;

	if (strncmp((char *) m->label, "!match(", strlen("!match(")) == 0)
	{	truth = (truth == 1) ? -1 : 1;
		x = strlen("!match(,");
		goto n_ref;
	}
	if (strncmp((char *) m->label, "!known_nonzero()", strlen("!known_nonzero()")) == 0)
	{	truth = (truth == 1) ? -1 : 1;
		goto n_nz;
	}

	if (strncmp((char *) m->label, "match(", strlen("match(")) == 0)
	{	x = strlen("match(");		/* match(mark, domatch, nomatch) */
n_ref:		if (!isdigit(m->label[x])
		||  sscanf((char *) &(m->label[x]), "%d,%d,%d", &z, &x, &y) != 3)
			notyet(m, "args to match");

		if ((x|y) & ~(DEF|USE|DEREF))	/* only D, U, or R marks matter */
			notyet(m, "2nd or 3rd arg to match");

		ret = has_ref_match(z, x, y);
		if (truth == -1) ret = 1 - ret;

		if (debug) printf("ac: %s -- returns %d\n", m->label, ret);
	} else if (strncmp((char *) m->label, "known_nonzero()", strlen("known_nonzero()")) == 0)
	{
n_nz:		ret = known_nz();
		if (truth == -1) ret = 1 - ret;

		if (debug) printf("ac: %s -- returns %d\n", m->label, ret);
	}

	return ret;
}

static int
act_select(Label *n, Label *m, int t)
{	unsigned char *p;
	int ret = 0;
	int x, y, xx;
	int truth = t;

	/*
	 *  n = sys  -- e.g. "C nm file line -- R x file line"
	 *  m = prop -- e.g. "ftc_call('nm') -- select('x', DEREF, NONE)"
	 */

	if (strncmp((char *) m->label, "!fct_call(", strlen("!fct_call(")) == 0)
	{	truth = (truth == 1) ? -1 : 1;
		goto n_fct;
	}
	if (strncmp((char *) m->label, "!select(", strlen("!select(")) == 0)
	{	truth = (truth == 1) ? -1 : 1;
		xx = x = strlen("select('',");
		goto n_sel;
	}
	if (strncmp((char *) m->label, "!(uno_state", strlen("!(uno_state")) == 0)
	{	truth = (truth == 1) ? -1 : 1;
		p = &(m->label[strlen("!(uno_state")]);
		goto n_uno;
	}

	if (strncmp((char *) m->label, "fct_call(", strlen("fct_call(")) == 0)
	{
n_fct:		if (has_fct_match(n, m))
		{	if (debug)
			printf("\tfct match '%s' <-> '%s' (want %d)\n",
				n->label, m->label, truth);

			if (truth ==  1) return 1;
			if (truth == -1) return 0;
			return 1;	/* fct_call as stmnt, matching */
		} else
		{	if (truth ==  1) return 0;
			if (truth == -1) return 1;
			return 0;	/* fct_call as stmnt, not matching */
	}	}

	if (strncmp((char *) m->label, "select(", strlen("select(")) == 0)
	{
		/* 4 args:  name, domatch, nomatch, mark */
		/* name must be "" or '' for now */
		xx = strlen("select('',");
n_sel:
		if ((!strstr((char *) m->label, "(\"\",")
		  && !strstr((char *) m->label, "('',"))
		||  !isdigit(m->label[xx]))
		{
 if (0)
 { fprintf(stderr, "<%s> %d '%s' %p,%d\n", &(m->label[xx]),
	xx, m->label,
	strstr((char *) m->label, "('',"),
	isdigit(m->label[xx]));
 }
			notyet(m, "args to select1");
		}
		if (sscanf((char *) &(m->label[xx]), "%d,%d", &x, &y) != 2)
		{	notyet(m, "args to select2");
		}

		if ((x|y) & ~(DEF|USE|DEREF|PARAM))	/* only D, U, or R marks matter */
		{
 if (0)
 { fprintf(stderr, "x=%d, y=%d\n", x, y);
 }
			notyet(m, "2nd or 3rd arg to select");
		}

		ret = has_sel_match(n, x, y);
		if (truth == -1) ret = 1 - ret;

		if (debug) printf("lm: %s <-> %s -- returns %d\n", n->label, m->label, ret);
		return ret;
	}

	if (strncmp((char *) m->label, "(uno_state", strlen("(uno_state")) == 0)
	{	p = &(m->label[strlen("(uno_state")]);
n_uno:		switch (*p) {
		case '!':
			if (*(p+1) != '=' || !isdigit(*(p+2))) notyet(m, "operator");
			ret = (stack->uno_state != atoi((char *) p+2));
			break;
		case '=':
			if (*(p+1) != '=' || !isdigit(*(p+2))) notyet(m, "operator");
			ret = (stack->uno_state == atoi((char *) p+2));
			break;
		case '>':
			if (*(p+1) == '=')
			{	if (!isdigit(*(p+2))) notyet(m, "operator");
				ret = (stack->uno_state >= atoi((char *) p+2));
			} else
			{	if (!isdigit(*(p+1))) notyet(m, "operator");
				ret = (stack->uno_state > atoi((char *) p+1));
			}
			break;
		case '<':
			if (*(p+1) == '=')
			{	if (!isdigit(*(p+2))) notyet(m, "operator");
				ret = (stack->uno_state <= atoi((char *) p+2));
			} else
			{	if (!isdigit(*(p+1))) notyet(m, "operator");
				ret = (stack->uno_state < atoi((char *) p+1));
			}
			break;
		default:
			notyet(m, "operator");
		}
		if (truth == -1) ret = 1 - ret;

		if (debug)
		printf("\tcmd '%s' == %d\n", m->label, ret);
		return ret;
	}
	if (debug)
	{	notyet(m, "unrecognized command");
	}
	return ret;
}

static void
addtostack(char *s)	/* info on var known to be nonzero */
{	char *p;
	BSym *r;

	p = strchr(s, ' ');
	if (!p)
	{	fprintf(stderr, "bad label: %s\n", s);
		return;
	}
	*p = '\0'; /* p now points to location */
	r = new_sym(s);
	r->nxt = stack->knz;
	stack->knz = r;
	*p = ' ';	/* restore */
	if (debug) printf("KnownNonZero var: '%s'\n", s);
}

static int
eval_prop(Node *sys, Node *prop)
{	Arc	*b;
	Label	*n, *m;
	int	nzs = 0, truth = 0, x;

	if (!prop) return 1;			/* reached end of prop */

	for (n = sys->lab; n; n = n->nxt)	/* is this a knz inserted state? */
		if (strncmp((char *) n->label, "N ", strlen("N ")) == 0)
		{	addtostack((char *) &n->label[2]);
			nzs = 1;
		}
	if (nzs) return 1;

#if 0
	the only possible labels, so far, are:
	condnts:	select, fct_call	<- true/false arcs, dependent on sys
	condnts:	match, known_nonzero	<- true/false arcs, independent of sys
	actions:	error, no_error, mark	<- single label and independent of sys
#endif

	for (b = prop->succ; b; b = b->nxt)	/* all edges to succ states of prop */
	for (m = b->lab; m; m = m->nxt)		/* all tags on those states */
	{
		if (debug) printf("	>proplabel '%s'\n", m->label);

		if (strstr((char *) m->label, "||")
		||  strstr((char *) m->label, "&&"))
			notyet(m, "composite expr");

		if (strstr((char *) m->label, "== _true") != NULL)
			truth = 1;	/* true branch */
		else if (strstr((char *) m->label, "== _false") != NULL)
			truth = -1;	/* false branch */
		else if (strstr((char *) m->label, " == ") != NULL)
			notyet(m, "case switch");
		else
		{	/* action: error, no_error, mark */
			if (!take_action(m))	/* independent of sys labels */
				return 0;	/* error - do not proceed */
			x = 1;			/* no_error, mark */
			goto down;
		}
		if (strstr((char *) m->label, "match(")
		||  strstr((char *) m->label, "known_nonzero("))
			x = act_cond(m, truth);	/* eval independent of sys labs */
		else
		{	x = 0;
			if (strstr((char *) m->label, "select("))
				unselect();			/* new selection erases old */
			for (n = sys->lab; n; n = n->nxt)	/* tags on current system state */
				x += act_select(n, m, truth);	/* collect info from all matches */
			/* unless 'notyet' is declared as an exit fct, uno
			   will not be able to tell that 'truth' was initialized
			 */
		}
down:		if (x)
		{	if (debug) printf("	>down in prop\n");
			eval_prop(sys, b->to);
			if (debug) printf("	>up in prop\n");
		}
	}

	if (debug) printf("uno:global: end of property\n");
	return 1;	/* reached the end */
}

static void
check_prop(Arc	*in)
{	Stack	*os;
	BFct	*f;
	Label	*n;
	Arc	*a;
	Node	*sys;
	int	hit;

	if (!in || !in->to)
	{	end_of_path();	/* find continuations in callstack */
		return;
	}

	sys = in->to;

	if (same_state(in))
	{	if (debug)
		printf("\tREVISIT nid %d state_bits %lu - callpt %d\n",
			sys->nid,
			sys->vis->uno_state,	/* bit mask */
			(rstack && rstack->n)?rstack->n->nid:-1);
		return;
	}

	depth++;

	if (debug)
	printf("%3d: [%d, %d] callpt %d -- %s\n", depth, sys?sys->nid:0,
		stack->uno_state,
		(rstack && rstack->n)?rstack->n->nid:-1,
		(sys && sys->lab)?(char *) sys->lab->label:"--");

	if (debug) printf("%3d: evalprop starts (%p)\n", depth, prop_start);

	if (!eval_prop(sys, prop_start))		/* complains on errors */
		goto done;

	if (debug) printf("%3d: evalprop ended\n", depth);

	hit = 0;
	for (n = sys->lab; n; n = n->nxt)		/* check tags on current state */
	{	f = fct_in_lab((char *) n->label);		/* to find all fct calls */
		if (f && !f->visited)			/* effect not already in call chain */
		{	if (debug) printf("%3d:\tCALL to %s [%d]\n", depth, f->fnm, sys->nid);
			do_fct_call(f, sys);
			if (debug) printf("%3d:\tUN_CALL %s [%d]\n", depth, f->fnm, sys->nid);
			hit++;	/* continuation is explored on return from fct */
	}	}
	if (hit) goto done;

	if (!sys->succ) end_of_path();

	for (a = sys->succ; a; a = a->nxt)		/* explore all next states */
	{	if (debug)
		{ printf("%3d:\tDOWN (uno_state=%d)\n", depth, stack->uno_state); list_sel(); }
		check_prop(a);	/* are explored */
		if (debug)
		{ printf("%3d:\tUP (uno_state=%d)\n", depth, stack->uno_state); list_sel(); }
	}
done:
	depth--;
	os = stack;
	stack->sels = rev_release(stack->sels);
	stack->knz  = rev_symrel(stack->knz);
	stack = stack->nxt;
	os->nxt = free_stack;
	free_stack = os;
}

void
run_check(void)
{	BFct *f;

	if (!fcts) return;

	stack = &init;
	memset(stack, 0, sizeof(Stack));
	ini_prop();
	add_glob_defs();

	f = find_function("_global_");	/* start execution with global defs */
	if (f)
	{	if (debug) printf("	CHECK %s\n", f->fnm);
		do_fct_call(f, (Node *) 0);
	} else
		printf("uno:global: internal error, no _global_\n");
	if (verbose)
	printf("uno:global: %d scenarios reported in property check\n", ErrCnt-1);
}

void
handle_fct(char *p_in)
{	static BFct *f;
	static Arc *a;
	int id;
	char *t;
	char p[512];

	if (strlen(p_in) >= 512)
	{	fprintf(stderr, "uno:global: very long fct name <%s>\n", p_in);
		exit(1);
	}
	strcpy(p, p_in);	/* p_in could be a constant string */

	t = strchr(p, '\r');
	if (t) *t = '\0';
	t = strchr(p, '\n');
	if (t) *t = '\0';

	if (0) { printf("'%s' (%d)\n", p, (int) strlen(p)); fflush(stdout); }

	switch (*p) {
	case ':':	/* reminder of fct name - already created */
		t = strchr(p+2, '\t');
		if (!t) goto bad1;
		*t = '\0';
		f = find_function(p+2);
		if (!f)
		{
bad1:			fprintf(stderr, "uno:global: fct reminder invalid '%s'\n", p);
			exit(1);
		}
		*t = '\t';
		oid = 0;
		break;

	case '{':
		if (sscanf(p, "{%d}", &id) != 1)
bad:			fprintf(stderr, "uno:global: bad fct delimiter: '%s'\n", p);
		else
			a = add_arc(f, oid, id);	/* uno can't tell that f was initialized */
		break;

	case '<':
		if (sscanf(p, "<%d>", &id) != 1)
			goto bad;
		else
			oid = id;
		break;

	case '>':
		if (sscanf(p, ">%d>", &id) != 1)
			goto bad;
		else
		{	a = add_arc(f, oid, id);
			oid = id;
		}
		break;

	case '[':
		t = strrchr(p, ']');
		if (!t) goto bad;
		*t = '\0';
		if (t > p+1)
		{	if (!a)
			{	fprintf(stderr, "uno:global: zero arc error\n");
				exit(1);
			}
			add_label(f, a, p+1);
		}
		*t = ']';
		break;
	}
}
