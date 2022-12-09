/***** uno: uno_lts.c *****/

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
#include <stdarg.h>
#include <ctype.h>
#include "prnttree.h"
#include "c_gram.h"
#include "symtab.h"
#include "uno_lts.h"

/* Names used in user-code inside C procedure specifying the property */
extern char	*property;
extern int	localonly, lintlike, usecheck, show_sharing, picky, cyclo;
extern char	*file_name;	/* uno_local.c */
extern char	*working_dir;

static int	debug = 0;

static DfStack	*dfs_frame;
static DfStack	*dfstack;
static DfStack	*safe_stack;

static FILE	*fd_uno;

       Graphs	*curgraph;	/* set during uno checking */
static Graphs	*find_graph(char *);
static Graphs	*glob_decls;
static Graphs	*graph;		/* all graphs - last created first */
static Graphs	*freegraph;

static LNode	*lnodes;	/* label nodes in cfg */

static PathCond *pathcond = 0;
static PathCond *pathfree = 0;

static Stack	*eol = 0;		/* end of loop */
static Stack	*fol = 0;		/* free frames */
static Stack	*sol = 0;		/* start of loop */

typedef struct Gst Gst;

struct Gst {
	Graphs	*gnm;
	Gst	*nxt;
};

static Gst *grst;	/* fcts that contain calls of other fcts via ptrs */
static Gst *frst;	/* fcts that can be called via a ptr */

static SymExt	*freesymext;
static SymRef	*freesymref;
static Trans	*freetrans;
static State	*freestate;
static State	*NS = (State *) 0;		/* no state */
static State	*lts_dowhile(State *, treenode *);
static State	*lts_for(State *, for_node *);
static State	*lts_if (State *, if_node *);
static State	*lts_node(State *, treenode *);
static State	*lts_switch(State *, treenode *);
static State	*lts_tree(State *, treenode *);
static State	*lts_while(State *, treenode *);
#if 0
static symentry_t	*mksym(char *, treenode *);
#endif
       void	debug_node(treenode *, int, char *);
static int	simple_zero(symentry_t *, treenode *);
static int	simple_nonzero(symentry_t *, treenode *);
extern void	dflow_mark(FILE *, int);

static SwStack	*stck;		/* to detect goto cycles */
static SwStack	*swol = 0;		/* switch structures */

static SymRef	*dfs_free;
static SymRef	*globs;		/* list of global objects being tracked */
static SymRef	*globuse;	/* list of unused global objects */

extern char	*cur_path, *cur_dir, *cur_file;

static int	checkpathcond(symentry_t *, treenode *, int);
static int	is_static_fct;
static int	not_a_prototype;
static int	sawdefault;	/* xtract.c has its own copy */

static treenode	*mk_label_node(leafnode *, treenode *n, char *);
static treenode *mk_goto_node(leafnode *);
static Graphs	*new_graph(treenode *, char *);
static SymRef	*add_gstack(symentry_t *, treenode *, int);
static PathCond *getpathframe(void);

static void	dfs_uno(State *);
#if 0
static void	putpathcond(symentry_t *);
#endif
static void	attach_nut(char *, symentry_t *, treenode *);

extern char	*buf_recur(treenode *);
extern char	*toksym(int, int);
extern int	has_node_comp_ops(treenode *);
extern int	has_node_type(treenode *, int);
extern int	is_constant(char *);
extern int	is_recorded(char *, char *);
extern int	v_reported(treenode *);
extern void	bound_reset(void);
extern void	dfs_bound(State *, treenode *, treenode *, State *);
extern void	dfs_generic(State *);
extern void	dump_defuse(DefUse *, FILE *);
extern void	explain_bound(char *, ArBound *, treenode *);
extern void	gen_reset(void);
extern void	gen_stats(void);
extern void	struct_fields(FILE *);

int	depth = 0, saw_a_typedef_name;
State	*uno_prop;

typedef struct ST {
	char *name;
	int line;
	int reported;
	struct ST *nxt;
} ST;

static ST *st;

static void
get_suppressors(FILE *fd)
{	char *p, buf[1024];
	ST *nst;

	while (fgets(buf, sizeof(buf), fd))
	{	if ((p = strchr(buf, '\t')) == NULL)
		{	fprintf(stderr, "uno: suppress file format <%s>\n", buf);
		} else
		{	*p++ = '\0';
			nst = (ST *) emalloc(sizeof(ST));
			nst->name = (char *) emalloc(strlen(buf)+1);
			strcpy(nst->name, buf);
			if (!isdigit((int) *p))
			{	nst->line = 0;	/* meaning all lines */
			} else
			{	nst->line = atoi(p);
			}
			nst->nxt = st;
			st = nst;
	}	}
}

void
find_suppress_lines(char *fn)
{	FILE	*fd;
	char	buf[1024];
	int	cnt = 0;
	ST	*nst;

	if ((fd = fopen(fn, "r")) == NULL)
	{	return;
	}

	while (fgets(buf, sizeof(buf), fd) != NULL)
	{	cnt++;
		if (strstr(buf, "@uno_suppress") != NULL)
		{	nst = (ST *) emalloc(sizeof(ST));
			nst->name = (char *) emalloc(strlen(fn)+1);
			strcpy(nst->name, fn);
			nst->line = cnt;
			nst->nxt = st;
			st = nst;
	}	}

	fclose(fd);
}

void
read_suppress(void)
{	FILE *fd;

	if ((fd = fopen("uno_suppress", "r")) != NULL)
	{	get_suppressors(fd);
		fclose(fd);
	}

	if (working_dir != NULL)
	{	char *efn;

		efn = emalloc(strlen(working_dir)+strlen("/uno_suppress")+1);
		sprintf(efn, "%s/uno_suppress", working_dir);

		if ((fd = fopen(efn, "r")) != NULL)
		{	get_suppressors(fd);
			fclose(fd);
		}
	}
}

int
suppress(char *fn, int ln)
{	ST *nst;

	for (nst = st; nst; nst = nst->nxt)
		if ((nst->line == 0 || nst->line == ln)
		&& (strcmp(nst->name, fn) == 0
		|| (strncmp(fn, "./", 2) == 0 && strcmp(nst->name, fn+2) == 0)))
		{
#if 0
			if (!nst->reported)
			fprintf(stderr, "uno: %s:%d: suppressing error report\n", fn, ln);
#endif
			nst->reported++;
			return 1;
		}

	return 0;
}

void
uno_assert(int cond, char *s)
{
	if (!cond)
	{	fprintf(stderr, "uno: %s\n", s);
		exit(1);
	}
}

int
uno_ignore(symentry_t *sm)
{	/* filter out std library fcts and data objects */
	return (sm
	&&  strncmp(sm->fn, "/usr/include", strlen("/usr/include")) == 0);
}

void
uno_warn(char *msg, treenode *n, symentry_t *s)
{	char *str;

	if (n)
	{	if (suppress(n->hdr.fnm, n->hdr.line))
			return;
	} else if (s)
	{	if (suppress(s->fn, s->ln))
			return;
	}

	uno_assert(curgraph && s, "bad input to uno_warn");

	if (strcmp(msg, "variable never used (evaluated)") == 0)
	{
		if (s
		&& strncmp(s->nme->str, "unused", strlen("unused")) == 0)
			return;

		if (n)
			str = x_stmnt(n);
		else
			str = "(declaration)";

		fprintf(stdout, "uno: ");

		if (n)	fprintf(stdout, "%s:%d:", n->hdr.fnm, n->hdr.line);
		else if (s) fprintf(stdout, "%s:%d", s->fn, s->ln);

		fprintf(stdout, "\tin fct %s, %s '%s' ",
			curgraph->fctnm, msg, s->nme->str);

	} else if (n && n->hdr.type != TN_EMPTY)
	{	if (strstr(x_stmnt(s->node), "va_list") != NULL)
			return;

		fprintf(stdout, "uno: %s/%s:%d: in fct %s, %s '%s'",
			cur_dir, cur_file, n->hdr.line,
			curgraph->fctnm, msg, s->nme->str);

 if (n->hdr.fnm)
 {		fprintf(stdout, "\n     statement  : %s:%d: ",
			n->hdr.fnm, n->hdr.line);
 } else
 {		fprintf(stdout, "\n     statement  : %s/%s:%d: ",
			cur_dir, cur_file, n->hdr.line);

 }
		if (n->hdr.type != TN_IF)
		{	str = x_stmnt(n);
			if (!str || strlen(str) == 0)
				str = "<stmnt>";
			fprintf(stdout, "%s", str);	/* src of offending stmnt */
		} else
		{	str = x_stmnt(((if_node *)n)->cond);
			if (!str || strlen(str) == 0)
				str = "<cond>";
			fprintf(stdout, "%s", str);	/* src of offending stmnt */
		}

		if (n->hdr.line != s->ln)		/* if different from above */
		{
 if (s->fn)
 {			fprintf(stdout, "\n     declaration: %s:%d: %s",
				s->fn, s->ln, x_stmnt(s->node)); /* decl src */
 } else
 {			fprintf(stdout, "\n     declaration: %s/%s:%d: %s",
				cur_dir, cur_file, s->ln, x_stmnt(s->node)); /* decl src */
 }
		}
	} else
	{	fprintf(stdout, "uno: in fct %s, %s '%s'",
			curgraph->fctnm, msg, s->nme->str);
	}

	fprintf(stdout, "\n");
}

static State *
create_state(Graphs *g)
{	State *s;

	if (freestate)
	{	s = freestate;
		freestate = s->all;
		memset(s, 0, sizeof(State));
	} else
		s = (State *) emalloc(sizeof(State));

	s->all = g->all;
	g->all = s;
	return s;
}

static void
lts_push_switch(State *stc)
{	SwStack *s;

	s = (SwStack *) emalloc(sizeof(SwStack));
	s->s = stc;
	s->nxt = swol;
	swol = s;
}

static State *
lts_top_switch(treenode *n)
{
	if (!swol && n) printf("uno: %s:%d error\n", n->hdr.fnm, n->hdr.line);
	uno_assert((swol != NULL), "switch stack (top)");
	return swol->s;		/* uno cannot tell that swol will be nonzero */
}

static void
lts_pop_switch(void)
{
	uno_assert((swol != NULL), "switch stack (pop)");
	swol = swol->nxt;
}

static Stack *
lts_new_stack(void)
{	Stack *f;

	if (!fol)
		return (Stack *) emalloc(sizeof(Stack));

	f = fol;
	fol = fol->nxt;
	f->nxt = (Stack *) 0;
	return f;
}

static void
lts_push_start(treenode *n)
{	Stack *f;

	f = lts_new_stack();
	f->n = n;
	f->nxt = sol;
	sol = f;
}

static void
lts_push_end(treenode *n)
{	Stack *f;

	f = lts_new_stack();
	f->status = 1;
	f->n = n;
	f->nxt = eol;
	eol = f;
}

static int
has_fctcalls(DefUse *d)
{	SymList *s;

	if (d)
	for (s = d->other; s; s = s->nxt)
		if (s->mark & FCALL)
			return 1;
	return 0;
}

static void
saw_break(void)
{
	if (eol) eol->status = 1;
}

static Stack *fallthru;

static void
show_fall(void)
{	Stack *f;
	int cnt = 0;
	Stack *lst = (Stack *) 0;
	char *s, *t;

	if (!fallthru) return;

	for (f = fallthru; f; lst = f, f = f->nxt)
	{	if (lst && lst->n->hdr.line == f->n->hdr.line + 1)
		{	f->status = 1;
			lst->status = 1;
		} else if (suppress(f->n->hdr.fnm, f->n->hdr.line))
			f->status = 1;
	}

	for (f = fallthru; f; lst = f, f = f->nxt)
		if (f->status == 0)
			cnt++;

	if (cnt == 0) return;

	fprintf(stdout, "uno: fallthroughs in switch stmnt:");
	for (f = fallthru; f; f = f->nxt)
	{
		if (f->status != 0)
			continue;

		s = x_stmnt(f->n);
		if (strlen(s) > 0)
		{	t = strchr(s, ':');
			if (t) *t = '\0';
		}
		fprintf(stdout, "\n");
		fprintf(stdout, "\t%s:%d:",
			f->n->hdr.fnm, f->n->hdr.line);
		if (strlen(s) > 0)
			fprintf(stdout, " <%s>", s);
	}
	fprintf(stdout, "\n");
}

static void
want_break(treenode *n)
{	Stack *f;
	uno_assert((eol != NULL), "case outside switch");

	if (lintlike && !eol->status)	/* uno cannot tell that eol is nonzero */
	{	if (fol)
		{	f = fol;
			fol = fol->nxt;
			memset(f, 0, sizeof(Stack));
		} else
			f = (Stack *) emalloc(sizeof(Stack));
		f->n = n;
		f->nxt = fallthru;
		fallthru = f;
	}
	eol->status = 0;
}

static Stack *
rel_sframe(Stack *f)
{
	if (f)
	{	rel_sframe(f->nxt);
		f->nxt = fol;
		fol = f;
	}
	return (Stack *) 0;
}

static void
lts_pop_start(void)
{	Stack *f;

	uno_assert((sol != NULL), "start stack underflow");
	f = sol;
	sol = sol->nxt;

	f->nxt = fol;
	fol = f;
}

static void
lts_pop_end(void)
{	Stack *f;

	uno_assert((eol != NULL), "end stack underflow");

	f = eol;
	eol = eol->nxt;

	f->nxt = fol;
	fol = f;
}

static treenode *
lts_top_start(void)
{
	uno_assert((sol != NULL), "start stack (top)");
	return sol->n;		/* uno cannot tell that sol will be nonzero */
}

static treenode *
lts_top_end(void)
{
	uno_assert((eol != NULL), "end stack (top)");
	eol->status = 1;	/* uno cannot tell that eol will be nonzero */
	return eol->n;
}

static LNode *freelabels;

static LNode *
rel_label(LNode *n)
{
	if (n)
	{	rel_label(n->nxt);
		n->nxt = freelabels;
		freelabels = n;
	}
	return (LNode *) 0;
}

static void
record_label(treenode *s, State *n)	/* associate symentry with state in cfg */
{	LNode *ln;
	leafnode *x = (leafnode *) s;

	uno_assert((int) (x && n), "bad call to record_label");

	if (freelabels)
	{	ln = freelabels;
		freelabels = ln->nxt;
		memset(ln, 0, sizeof(LNode));
	} else
		ln = (LNode *) emalloc(sizeof(LNode));
	ln->s = x->data.sval->str;
	ln->f = curgraph?curgraph->fctnm:"_noname_";
	ln->n = n;
	ln->nxt = lnodes;
	lnodes = ln;
}

static State *
lts_label_find(char *s)
{	LNode *ln;

	uno_assert((s != NULL), "bad call to lts_label_find");

	for (ln = lnodes; ln; ln = ln->nxt)
		if (ln->s == s
		&&  ln->f == curgraph->fctnm)
		{	if (0)
			fprintf(stderr, "label match %s (N%p)\n", s, ln->n->n);
			return ln->n;
		}

	fprintf(stderr, "error: label %s not defined\n", s);
	return NS;
}

static State *
lts_redirect(State *s)
{	State *stc = s;
	leafnode *ln;
	SwStack *frame;

	if (!s || !s->n) return s;

	for (frame = stck; frame; frame = frame->nxt)
		if (frame->s == s)
		{	fprintf(stderr, "uno: %s:%d: goto cycle\n",
				s->n->hdr.fnm,
				s->n->hdr.line);
			return s;
		}

	frame = (SwStack *) emalloc(sizeof(SwStack));
	frame->s = s;
	frame->nxt = stck;
	stck = frame;

	if (s->n->hdr.which == NODE_T)
	{	switch (s->n->hdr.type) {
		case TN_JUMP:
			if (s->n->hdr.tok == RETURN)
				break;
			if ((ln = (leafnode *) s->n->lnode) != NULL)	/* assign */
			{	stc = lts_label_find(ln->data.sval->str);
				if (!stc) stc = s;
			}
			break;

		case TN_BLOCK:
		case TN_STEMNT:
		case TN_LABEL:	/* skip fillers, if unique successor */
			if (!s->succ)	/* not yet set, but already known to be unique */
				stc = s->nxt;
			else if (!s->succ->nxt)
				stc = s->succ->branch;

			if (!stc) stc = s;
			break;
		default:
			break;
	}	}

	if (stc != s)
		stc = lts_redirect(stc);

	stck = stck->nxt;	/* pop frame stack */

	return stc;
}

SymRef *
rev_release(SymRef *r)	/* release a list of symrefs */
{
	if (r)
	{	rev_release(r->nxt);
		r->nxt = dfs_free;
		dfs_free = r;
	}
	return (SymRef *) 0;
}

static void
cfg_unvisit(State *t)
{	State *s;

	for (s = t; s; s = s->all)
	{	s->visited = 0;
		s->snapshot = rev_release(s->snapshot);
	}
}

typedef struct EX	EX;
struct EX {
	char	*f;
	int	has_arg;	/* is next field used or not */
	int	arg_val;	/* optionally, a value for the first arg that should match */
	EX	*nxt;
};
static EX *exs;

void
custom_exit(const char *s)
{	EX *nx;
	char *col;

	nx = (EX *) emalloc(sizeof(EX));
	nx->f = (char *) emalloc(strlen(s)+1);
	strcpy(nx->f, s);

	col = strchr(s, ':');
	if (col)
	{	*col = '\0';
		col++;
		nx->has_arg = 1;
		nx->arg_val = atoi(col);
	}
	else
	{	nx->has_arg = 0;
		nx->arg_val = 0;
	}

	nx->nxt = exs;
	exs = nx;
}

static int
no_return(char *s, int has_arg, int with_arg)
{	EX *nx;

	for (nx = exs; nx; nx = nx->nxt)
		if (strcmp(nx->f, s) == 0
		&&  (nx->has_arg == 0
		||   (has_arg && nx->arg_val == with_arg)))
			return 1;
	return 0;
}

static Trans *
get_trans(void)
{	Trans *t;

	if (freetrans)
	{	t = freetrans;
		freetrans = t->nxt;
		memset(t, 0, sizeof(Trans));
	} else
		t = (Trans *) emalloc(sizeof(Trans));
	return t;
}

static int
killpath(treenode *z)
{	int hasval = 0, thisval = 0;

	if (z->hdr.type == TN_EXPR
	&&  z->hdr.tok  == COMMA)	/* foo(),goo() */
		return killpath(z->rnode) || killpath(z->lnode);

	if (z->hdr.type == TN_FUNC_CALL
	&&  z->lnode->hdr.type == TN_IDENT) /* function call */
	{
		/* check if the first argument is an int */
		if (z->rnode)
		{	treenode *t = z->rnode;

			while (t && t->hdr.type == TN_EXPR_LIST)
				t = t->lnode; /* leftmost */
		 	if (t
		 	&& t->hdr.which == LEAF_T
		 	&& t->hdr.type == TN_INT)
			{	hasval = 1;
				thisval = ((leafnode *)t)->data.ival;
		}	}

		return (no_return(((leafnode *)z->lnode)->data.sval->str, hasval, thisval));
	}

	return 0;
}

static void
prep_graph(Graphs *g)
{	State *s;
	Trans *t;
	int cnt;

	curgraph = g;

	for (s = g->all; s; s = s->all)
	{	s->visited = 0;
		if (!s->succ)
		{	if (s->n)
			{	if (s->n->hdr.tok == RETURN)
					continue;

				if (killpath(s->n))	/* non-returning fct called */
					continue;
			}

			if (s->n
			&&  s->n->hdr.tok != GOTO
			&&  s->n->hdr.tok != COLON
			&& !s->nxt
			&&  (!s->n->hdr.fnm || strcmp(s->n->hdr.fnm, "-1") != 0))
			{	g->status |= 2;	/* no value returned */

				if (0) printf("no value returned at %s:%d: -- %s = %d\n",
					s->n->hdr.fnm, s->n->hdr.line,
					toksym(s->n->hdr.tok,0),
					s->n->hdr.tok);
				if (debug)
				printf("prepgraph %s adds 2 <%d:%d> %s:%d\n",
					g->fctnm,
					(int) s->n->hdr.type,
					s->n->hdr.tok,
					s->n->hdr.fnm,
					s->n->hdr.line);
			}

			t = get_trans();
			t->branch = lts_redirect(s->nxt);
			t->nxt = (Trans *) 0;
			s->succ = t;
		} else
		{	cnt = 0;
			for (t = s->succ; t; t = t->nxt)
			{	t->branch = lts_redirect(t->branch);
				cnt++;
			}
			s->iscond = (cnt > 1);

			/* find cases like "if (c);" */
			if (picky == 1
			&&  s->n
			&&  suppress(s->n->hdr.fnm, s->n->hdr.line) == 0
			&&  cnt == 2
			&&  s->n->hdr.type == TN_IF
			&&  s->succ->branch == s->succ->nxt->branch)
				printf("uno: %s:%d: in fct %s, 'if' followed by null-statement\n",
					s->n->hdr.fnm, s->n->hdr.line, curgraph->fctnm);
	}	}
}

static void
nut_prepare(State *from, State *to)	/* insert forward arcs to nodes with a nut attached */
{	Trans *t;

	if (!to || !to->n || to->visited)
		return;
	to->visited = 1;

	if (to->n->hdr.nuts
	|| !(to->succ && to->succ->branch))
	{	for (t = from->direct; t; t = t->nxt)
			if (t->branch == to)
				break;
		if (!t)
		{	t = get_trans();
			t->branch = to;
			t->nxt = from->direct;
			from->direct = t;
		}
		return;
	}

	for (t = to->succ; t; t = t->nxt)
		nut_prepare(from, t->branch);
}

static void
nuts_forward(Graphs *g, State *s)
{	Trans *t;

	if (!s->direct)
	for (t = s->succ; t; t = t->nxt)
	{	cfg_unvisit(g->all);
		s->visited = 1;
		nut_prepare(s, t->branch);
	}
}

static void
dumknow(treenode *n, Trans *t)
{	SymRef *r;

	printf("KnownNonZero @ %s:%d: ",
		n?n->hdr.fnm:"--",
		n?n->hdr.line:0);
	for (r = t->knz; r; r = r->nxt)
		printf("%s, ", r->sm->nme->str);
	printf("\n");
}

static treenode *
clone_node(treenode *r)
{	treenode *n;
	n = (treenode *) emalloc(sizeof(treenode));
	memcpy(n, r, sizeof(treenode));
	n->hdr.nuts = (Nuts *) 0;
	n->hdr.defuse = (DefUse *) 0;
	return n;
}

static void
nut_insertion(Graphs *g, State *s, Trans *t)
{	State  *ns;
	Trans  *nt;
	SymRef *r = t->knz;

	if (debug) dumknow(s->n, t);
	 /*
	  * insert dummy state between s and t->branch,
	  * to attach nut knz info
	  */
	nt = get_trans();
	nt->branch = t->branch;

	ns = create_state(g);	/* inserted new state */
	ns->n = clone_node(s->n);	/* points to the same node */
	ns->succ = nt;		/* goes to the original successor */
	t->branch = ns;		/* the old transition now points to inserted state */

	for (r = t->knz; r; r = r->nxt)
		attach_nut("N", r->sm, ns->n);	/* non-zero vars */
}

static void
nut_setup(Graphs *g)	/* build abstracted graph */
{	State *s;
	Trans *t;

	for (s = g->all; s; s = s->all)
	for (t = s->succ; t; t = t->nxt)
		if (t->knz)
			nut_insertion(g, s, t);

	for (s = g->all; s; s = s->all)
		nuts_forward(g, s);
}

static unsigned long Cnt = 1;

static void
nut_hunt(FILE *fd, State *s)
{	Trans *t;
	Nuts *q;

	if (!s || !s->n) return;

	if (s->visited)
	{	fprintf(fd, "{%lu}\n", s->uno_state);
		return;
	}
	s->visited = 1;
	s->uno_state = Cnt++;

	fprintf(fd, ">%lu>\n", s->uno_state);

	if (!s->n->hdr.nuts)
		fprintf(fd, "[]\n");
	for (q = s->n->hdr.nuts; q; q = q->nxt)
		fprintf(fd, "[%s]\n", q->nut);

	for (t = s->direct; t; t = t->nxt)
	{	nut_hunt(fd, t->branch);
		fprintf(fd, "<%lu<\n", s->uno_state);
	}
}

static void
fct_details(FILE *fd, State *s)
{	Trans *t;
	State *ns;
	treenode *exp = (treenode *) 0;

	if (!s || !s->n || s->visited)
		return;

	s->visited = 1;

	if (s->n->hdr.type == TN_IF)
		exp = ((if_node *)s->n)->cond;
	else if (s->n->hdr.type != TN_LABEL)
		exp = s->n;

	for (t = s->succ; t; t = t->nxt)
	{	ns = t->branch;
		if (!ns || !ns->n)
		{	if (exp)
				fprintf(fd, ">0>\n[%s]\n<%lu<\n",
				x_stmnt(exp), s->uno_state);
			continue;
		}
		if (ns->visited)
			fprintf(fd, "{%lu}\n", ns->uno_state);
		else
		{	ns->uno_state = Cnt++;
			fprintf(fd, ">%lu>\n", ns->uno_state);
		}
		fprintf(fd, "[%s", x_stmnt(exp));
		if (t->cond) fprintf(fd, " == %s", x_stmnt(t->cond));
		fprintf(fd, "]\n");
		fct_details(fd, ns);
		fprintf(fd, "<%lu<\n", s->uno_state);
	}
}

static void
nut_start(void)
{	Graphs *g;
	State *x;

	for (g = graph; g; g = g->nxt)
	{	if (g == glob_decls)
			continue;

		cfg_unvisit(g->all);
		fprintf(fd_uno, ": %s	%d\n", g->fctnm, g->status);	/* reminder of fct name */

		if (g->cfg == uno_prop)
		{	extern int err_path;
			err_path++;
			fct_details(fd_uno, uno_prop);
			err_path--;
		} else if (g->hasnuts)
		{	nut_setup(g);
			cfg_unvisit(g->all);
			x = g->cfg;
#if 1
			while (!x->n->hdr.nuts && x->direct && !x->direct->nxt)
				x = x->direct->branch;
#endif
			nut_hunt(fd_uno, x);
		}
		fprintf(fd_uno, "\n");
	}
}

static void
gen_lts(State *s)
{	State *n;
	Trans *t;
	ArBound *b;
	char *z, *zz;
	int cnt;

	if (!s || !s->n || s->visited) return;

	s->visited = 1;

	for (z = zz = x_stmnt(s->n), cnt=0; *zz; zz++) {
		if (*zz == '"') *zz = '\'';
		if (*zz == '\n') *zz = ' ';
		if (*zz == '\r') *zz = ' ';
		if (++cnt > 16) { *zz = '\0'; break; }
	}
#if 1
	printf("N%p [label=\"%d : %s : %s : ",
		s->n,
		s->n->hdr.line,
		name_of_node(s->n->hdr.type),
		z );
#else
	printf("N%p [label=\"%s : %d : %s <%d> : %s : ",
		s->n,
		s->n->hdr.fnm,
		s->n->hdr.line,
		name_of_node(s->n->hdr.type),
		s->iscond,
		x_stmnt(s->n) );
#endif

	if (s->n->hdr.type == TN_IF)
		dump_defuse(((if_node *)s->n)->cond->hdr.defuse, stdout);
	else
		dump_defuse(s->n->hdr.defuse, stdout);

	for (b = s->pvb; b; b = b->nxt)
	{	explain_bound("", b, (treenode *)0);
		printf(",");
	}

	printf("\"];\n");

	for (t = s->succ; t && t->branch; t = t->nxt)
	{	n = t->branch;
		printf("N%p -> N%p;\n", s->n, n->n);
		gen_lts(n);
	}
}

SymRef *
uno_getref(symentry_t *t)
{	SymRef *r;

	if (dfs_free)
	{	r = dfs_free;
		dfs_free = dfs_free->nxt;
		r->sm = (symentry_t *) 0;
		r->n  = ZT;
		r->nxt = (SymRef *) 0;
		r->status = 0;
		r->s_val = 0;
	} else
		r = (SymRef *) emalloc(sizeof(SymRef));

	r->sm = t;

	return r;
}

SymRef *
uno_copy_ref(SymRef *r)
{	SymRef *q;
	q = uno_getref(r->sm);
	q->n = r->n;
	q->status = r->status;
	q->s_val = r->s_val;
	return q;
}

SymExt *
uno_getext(symentry_t *t)
{	SymExt *r;

	if (freesymext)
	{	r = freesymext;
		freesymext = r->nxt;
		memset(r, 0, sizeof(SymExt));
	} else
		r = (SymExt *) emalloc(sizeof(SymExt));
	r->sm = t;

	return r;
}

static DfStack *
uno_getframe(void)
{	DfStack *r;

	if (dfs_frame)
	{	r = dfs_frame;
		dfs_frame = dfs_frame->nxt;
		r->symrefs = (SymRef *) 0;
		r->globrefs = (SymRef *) 0;
		r->nxt = (DfStack *) 0;
	} else
		r = (DfStack *) emalloc(sizeof(DfStack));

	return r;
}

static void
uno_report0(FILE *fd, char *s, int t, SymRef *d)
{	SymRef *r;

	for (r = d; r; r = r->nxt)
		if (t == -1
		||  r->status == t)
		fprintf(fd, "%s\t%s\t%s\t%d\n",
			s,
			r->sm->nme->str,
			r->n->hdr.fnm,
			r->n->hdr.line);
}

static void
uno_report1(FILE *fd, char *s, int t, SymExt *d)
{	SymExt *r;

	for (r = d; r; r = r->nxt)
	{	if (t == -1
		||  t == r->status)
		fprintf(fd, "%s\t%s\t%s\t%d\n",
			s, r->sm->nme->str,
			r->n->hdr.fnm,
			r->n->hdr.line);
	}
}

static void
add_glob(symentry_t *t, treenode *n, int stc)
{	SymRef *r;

	if (debug) printf("Adding Global %s to globs\n", t->nme->str);

	for (r = globs; r; r = r->nxt)
		if (r->sm == t)
		{	r->status |= stc;
			return;
		}

	r = uno_getref(t);
	r->n = n;
	r->status = stc;
	r->nxt = globs;
	globs = r;
}

static int
on_glob(symentry_t *t)
{	SymRef *r;

	for (r = globs; r; r = r->nxt)
		if (r->sm == t)
			return ((r->status & ~2) == 0);
	return 0;
}

static void
mark_guse(symentry_t *t, treenode *n, int stc)
{	SymRef *r;

	if (0)
	printf("mark_guse: %s:%d: - %s - %d\n", n->hdr.fnm, n->hdr.line, t->nme->str, stc);

	if (is_enum_const(t)) return;

	for (r = globuse; r; r = r->nxt)
		if (r->sm == t)
		{	r->status |= stc;
			return;
		}

	r = uno_getref(t);
	r->status = stc;
	r->n = n;
	r->nxt = globuse;
	globuse = r;
#if 0
	/* 128 - array_decl, 64 - fct param, 2 - static, 4 - extern */
	if (show_sharing && !(stc&64) && ((stc&4) || !(stc&2)))
		printf("%s:%d:\t%s\t\t%s\n",
			n->hdr.fnm, n->hdr.line, t->nme->str,
			(stc&4)?"imported":"exported");
#endif
}

static void
uno_complain(SymRef *r, char *qualify, char *issue)
{
	if (strcmp(qualify, "extern ") == 0)	/* unused extern */
	{	char *p = strstr(r->n->hdr.fnm, ".h");
		if (p && strcmp(p, ".h") == 0)	/* in header file */
			return;			/* too fussy */
	}

	fprintf(stdout, "uno: ");
	if (r->n) fprintf(stdout, "%s:%d:", r->n->hdr.fnm, r->n->hdr.line);
	fprintf(stdout, "\t%sglobal variable '%s' %s\n",
		qualify, r->sm->nme->str, issue);
}

static void
uno_shared(void)
{	SymRef *r;
	int stc;

	for (r = globuse; r; r = r->nxt)
	{	stc = r->status;

		if (Verbose
		|| (((stc&8) || (stc&32)) && (stc&4)))	/* imported + defined or aliased */

		if (!(stc&64) && ((stc&4) || !(stc&2)))
		{
			printf("%s:%d:\t%s\t\t%s",
			r->n->hdr.fnm, r->n->hdr.line, r->sm->nme->str,
			(stc&4)?"imported":"exported");

			if (stc&1) printf(" U"); else printf("  ");
			if (stc&8) printf(" D"); else printf("  ");
			if (stc&32) printf(" &"); else printf("  ");
			if (stc&128) printf(" [array]");
			printf("\n");
	}	}
}

static void
uno_guse(void)
{	SymRef *r;
	Graphs *g;

	/* flags: 1 - used, 2 - static, 4 - extern, 8 - def-ed, 16 - useb4def, 32 - alias */
	/* 64 - fct param, 128 - array decl */

	/* local check of unused globals in this file */

	if (usecheck)
	for (r = globuse; r; r = r->nxt)
	{	int stc;

		if (0)	printf("%s - %d \t%s:%d: <-> %s\n",
			r->sm->nme->str,
			r->status,
			r->n->hdr.fnm,
			r->n->hdr.line,
			file_name);

		if (r->n
		&&  r->n->hdr.fnm
		&&  strcmp(r->n->hdr.fnm, file_name) != 0)
			continue;

		stc = r->status&~128;
		if (r->status & 128) stc |= 8; /* array decl */

		if (!(stc & 32)	/* no alias taken */
		&&  !(stc & 64))	/* no fct param */
		switch (stc) {
		case   0: /* normal -def -use */
			uno_complain(r, "", "not assigned to or used in this file");
			break;

		case     8: /* normal +def -use */
			if (picky || Verbose)
			uno_complain(r, "", "assigned to but not used in this file");
			break;

		case   2: /* static -def -use */
			uno_complain(r, "static ", "never assigned to or used");
			break;

		case 2|8: /* static +def -use */
			uno_complain(r, "static ", "assigned to but not used");
			break;

		case 1|2: /* static -def +use */
		case 1|2|16: /* static -def  +use +useb4def */
			if (on_glob(r->sm))
			uno_complain(r, "static ", "used but never assigned to");
			break;

		case 1|2|8|16: /* static +def  +use +useb4def */
			if (lintlike && on_glob(r->sm))	/* picky mode */
			uno_complain(r, "static ", "may be used before set");
			/*
			 * also picks up cases of globals assumed to be 0-init
			 * only dereference operations are trouble in this case
			 * - these are reported elsewhere
			 */
			break;

		case   4: /* extern -def -use */
			uno_complain(r, "extern ", "not assigned to or used in this file");
			break;

		case  1:	/* normal -def +use */
		case  1|4:	/* extern -def +use */
		case  1|8:	/* normal +def +use */
		case 1|2|8:	/* static +def +use */
		case 1|4|8:	/* extern +def +use */
		case 1|16:	/* normal -def  +use +useb4def */
		case 1|4|16:	/* extern -def  +use +useb4def */
		case 4|8:	/* extern +def -use */
			break;	/* ok */

		case 1|8|16:	/* normal +def  +use +useb4def */
		case 1|4|8|16:	/* extern +def  +use +useb4def */
			/* should be improved */
			if (!on_glob(r->sm)) continue;

			for (g = graph; g; g = g->nxt)
			{	if (g == glob_decls
				||  g->cfg == uno_prop
				||  strcmp(g->fctnm, "main") == 0)
					continue;
				break;
			}
			if (!g)	/* main is the only procedure */
			uno_complain(r, "", "may be used before set in main()");
			break;

		default: /* 4&2 or 4&2&1 -- var has both static and extern flags */
			fprintf(stderr, "uno: internal error, invalid status %d, uno_guse\n",
				r->status);
			break;
	}	}
}

static void
fct_retval(treenode *n)
{
	if (!n->lnode)
	{	curgraph->status |= 2;	/* no return value */
		if (debug) printf("fct_retval %s adds 2\n", curgraph->fctnm);
	} else
		curgraph->status |= 1;	/* return value used */
}

static void
make_suspect(symentry_t *t, treenode *n, int tags)
{	SymExt *v;

	if (localonly) return;

	for (v = curgraph->suspect; v; v = v->nxt)
		if (v->sm == t
		&&  v->n == n)
		{	v->status |= tags;
			break;
		}
	if (!v)
	{	v = uno_getext(t);
		v->n = n;
		v->status = tags;
		v->nxt = curgraph->suspect;
		curgraph->suspect = v;
	}
}

static int
not_fcall(symentry_t *t)
{	SymExt *r;

	for (r = curgraph->fcalls; r; r = r->nxt)
		if (r->sm == t)
			return 0;
	return 1;
}

static void
add_fcall(symentry_t *t, treenode *n, int status)
{	SymExt *r;

	if (debug)
		printf("fct %s calls fct %s status %d\n",
		curgraph->fctnm, t->nme->str, status);

	for (r = curgraph->fcalls; r; r = r->nxt)
		if (r->sm == t)
		{	if (status & DEF)
				r->n = n;	/* remember failures to use ret value */
			break;
		}
	if (!r)
	{	r = uno_getext(t);
		r->n = n;
		r->nxt = curgraph->fcalls;
		curgraph->fcalls = r;
	}

	r->status |= status;

	switch (r->status) {
	case DEF:		attach_nut("C", t, n); break;
	case USE:		attach_nut("c", t, n); break;
	case DEF|USE:		attach_nut("b", t, n); break;
	case DEF|HIDE:		attach_nut("h", t, n); break;
	case USE|HIDE:		attach_nut("i", t, n); break;
	case DEF|USE|HIDE:	attach_nut("j", t, n); break;
	}
}

static Graphs *
find_graph(char *s)
{	Graphs *g;

	for (g = graph; g; g = g->nxt)
	{	if (g == glob_decls)
			continue;
		if (strcmp(s, g->fctnm) == 0)
			return g;
	}

	if (0) printf("uno: no graph %s\n", s);
	return (Graphs *) 0;
}

static void
add_locs(symentry_t *t, treenode *n)
{	SymRef *r;

	for (r = curgraph->locs; r; r = r->nxt)
		if (r->sm == t)
			return;

	r = uno_getref(t);
	r->n = n;
	r->nxt = curgraph->locs;
	curgraph->locs = r;
}

static int
is_local(symentry_t *t)
{	SymRef *r;

	for (r = curgraph->locs; r; r = r->nxt)
		if (r->sm == t)
			return r->status;
	return 0;
}

void
could_be_fct(char *s)
{	Graphs *g;

	for (g = graph; g; g = g->nxt)
		if (strcmp(s, g->fctnm) == 0)
		{	if (debug)
			printf("uno: marking %s as fct in disguise\n", s);
			g->status |= 4;		/* cannot tell when this fct is called */
			break;
		}
}

static void
mark_locs(symentry_t *t, treenode *n, int status)
{	Graphs *g;
	SymRef *r;

	if (debug)
	printf("%d: mark_locs %s -- status %d\n",
	n->hdr.line, t->nme->str, status);

	for (r = curgraph->locs; r; r = r->nxt)
		if (r->sm == t)
		{	r->status |= status;	/* was: = (status & ~FCALL); */

			if (n && (status & USEbeforedef))
				r->n = n;
			return;
		}

	if (! ((status & USE) || (status & FCALL)))	/* missed braces to group !() */
		return;

	for (g = graph; g; g = g->nxt)
	{	if (strcmp(t->nme->str, g->fctnm) == 0)
		{	Gst *k;
			if (debug)
			printf("uno: status %d old status %d, decl_level %d marking %s at %s:%d as hide\n",
				status, g->status, t->decl_level,
				t->nme->str, n->hdr.fnm, n->hdr.line);

			g->status |= 4;		/* cannot tell when this fct is called */
			add_fcall(t, n, USE|HIDE);	/* ptr to fct name */

			if (Verbose)
			{	static int warned;
				if (!warned)
				{	warned++;
					printf("%s:%d fct %s is called via ptr\n",
						n->hdr.fnm, n->hdr.line, t->nme->str);
			}	}

			k = (Gst *) emalloc(sizeof(Gst));
			k->gnm = find_graph(t->nme->str);
			k->nxt = frst;
			frst = k;

			break;
	}	}
}

static void
ana_locs(Graphs *g)
{	SymRef *r;

	if (uno_p != 4) return;

	if (g)
	for (r = g->locs; r; r = r->nxt)
	{
#if 0
		if ((r->status & PARAM) && (r->status & (REF0|DEREF)))
		{	if (r->n)
			fprintf(stderr, "%s:%d: parameter %s: ",
				r->n->hdr.fnm, r->n->hdr.line, r->sm->nme->str);
			else
			fprintf(stderr, "%s:%d: parameter %s: ",
				r->sm->fn, r->sm->ln, r->sm->nme->str);
			dflow_mark(stderr, r->status);
			fprintf(stderr, "\n");
		}
#endif
		if (r->status & ALIAS)
			continue;	/* can't tell */

		if (r->status & USEbeforedef)	/* at least one use before def */
		{
			if (r->status & DEREF)	/* a local ptr, zero/non_zero test is ok */
			{	treenode *rn = r->n;
				if (r->n->hdr.type == TN_IF)
					rn = ((if_node *)r->n)->cond;
				if (simple_zero(r->sm, rn)
				|| simple_nonzero(r->sm, rn))
				{	if (debug)
						uno_warn("[non-]zero test of uninit ptr",
							r->n, r->sm);
					continue;
			}	}

			if (r->status & PARAM)
			{	/* check if this is a fct name, if so mark g->status |= 4 */
				could_be_fct(r->sm->nme->str);
				continue;
			}

			if ((r->status & IN_SIZEOF)
			|| ((r->status & ISTATIC) && !lintlike))
				continue;

			saw_a_typedef_name = 0;
			buf_recur(r->sm->node);	/* intercept typedefs of structs only */

			if ((r->status & DEF) || saw_a_typedef_name)	/* at least one def before use */
				uno_warn("possibly uninitialized variable", r->n, r->sm);
			else
			{	if (debug) printf("status: %d\n", r->status);
				uno_warn("uninitialized variable", r->n, r->sm);
			}
			continue;
		}

		/* printf("status %d name %s fcall %d\n", r->status, r->sm->nme->str, not_fcall(r->sm)); */

		if (usecheck
		&&  strncmp(r->sm->nme->str, "unused", strlen("unused")) != 0
		&&  not_fcall(r->sm)
		&& !(r->status & USE))
			uno_warn("local variable never used (evaluated)", r->n, r->sm);
	}
}

static void
mark_defuse(symentry_t *t, treenode *n, int stc)
{	SymRef *r;

	for (r = curgraph->def_use; r; r = r->nxt)
		if (r->sm == t)
		{	r->status |= stc;
			if (n && (stc & DEREF))
				r->n = n;
			return;
		}

	r = uno_getref(t);
	r->n = n;
	r->status = stc;
	r->nxt = curgraph->def_use;
	curgraph->def_use = r;
}

static void
attach_nut(char *pref, symentry_t *t, treenode *n)
{	char nr[16];
	char *newnut;
	Nuts *q;

	if (!t || !n) return;

	sprintf(nr, "%d", n->hdr.line);
	if (!n->hdr.fnm) n->hdr.fnm = "--";
	newnut = (char *) emalloc(
			  strlen(pref)
			+ strlen("\t\t\t")
			+ strlen(t->nme->str)
			+ strlen(n->hdr.fnm?n->hdr.fnm:"")
			+ strlen(nr)
			+ 1);
	sprintf(newnut, "%s\t%s\t%s\t%s", pref, t->nme->str, n->hdr.fnm?n->hdr.fnm:"", nr);

	for (q = n->hdr.nuts; q; q = q->nxt)
		if (strcmp(q->nut, newnut) == 0)
			break;	/* already there */
	if (!q)
	{	q = (Nuts *) emalloc(sizeof(Nuts));
		q->nut = newnut;
		q->nxt = n->hdr.nuts;
		n->hdr.nuts = q;
		curgraph->hasnuts = 1;
	}
}

static void
add_defs(symentry_t *t, treenode *n)
{
	mark_defuse(t, n, DEF);
	attach_nut("D", t, n);
}

static void
add_uses(symentry_t *t, treenode *n)
{
	mark_defuse(t, n, USE);

	if (!on_glob(t))
	{	make_suspect(t, n, USE);	/* use of non-ptrs only */
		attach_nut("U", t, n);
	}
}

static void
add_derefs(symentry_t *t, treenode *n)
{
	mark_defuse(t, n, USE|DEREF);
	if (on_glob(t))
	{	make_suspect(t, n, USE|DEREF);	/* pointer dereference */
		attach_nut("R", t, n);
	}
}

#if 0
static int
on_uses(symentry_t *t)
{	SymRef *r;

	for (r = curgraph->def_use; r; r = r->nxt)
		if (r->sm == t)
			return (r->status & USE);
	return 0;
}
#endif

static void
add_safe(symentry_t *t, treenode *n)
{	SymRef *r;

	r = uno_getref(t);
	r->n = n;
	r->nxt = safe_stack->symrefs;
	safe_stack->symrefs = r;

}

static SymRef *
add_gstack(symentry_t *t, treenode *n, int mark)
{	SymRef *r, *s, *lr;
	int x;

	uno_assert((dfstack != NULL), "no dfstack - add_gstack");

/*	if (is_enum_const(t)) return;	*/

	if (debug)
	printf("\tadd_gstack %s [%s:%d] + %d\n",
		t->nme->str, n->hdr.fnm, n->hdr.line, mark);

	if (!dfstack->globrefs)	/* empty list */
	{	r = uno_getref(t);
		r->n = n;
		r->status = mark;
		dfstack->globrefs = r;
		goto done;
	}

	lr = (SymRef *) 0;
	for (r = dfstack->globrefs; r; lr = r, r = r->nxt)	/* keep list sorted */
	{	if (debug) printf("\t<%s> status: [%d]\n", r->sm->nme->str, r->status);
		x = strcmp(r->sm->nme->str, t->nme->str);

		if (x < 0)
			continue;

		if (x == 0)
			r->status |= mark;
		else
		{	s = uno_getref(t);
			s->n = n;
			s->status = mark;
			s->nxt = r;	/* insert before r */
			if (!lr)	/* at head of list */
				dfstack->globrefs = s;
			else
				lr->nxt = s;
			r = s;
		}
		goto done;
	}
	/* fell off the end of the list - item should go at the end */
	r = uno_getref(t);
	r->n = n;
	r->status = mark;
	lr->nxt = r;	/* list had at least 1 item, so lr is set */
done:
	if (!(r->status & DEF))
		return r;

	return (SymRef *) 0;
}

static void
add_stack(symentry_t *t, treenode *n)	/* locals only */
{	SymRef *r;

	uno_assert((dfstack != NULL), "no dfstack - add_stack");

	r = uno_getref(t);
	r->n = n;
	r->nxt = dfstack->symrefs;
	dfstack->symrefs = r;

	if (debug) printf("ADD_STACK %s\n", t->nme->str);
}

static void
del_stack(symentry_t *t, int w)	/* locals only */
{	SymRef *r, *or = (SymRef *) 0;

	if (dfstack)
	for (r = dfstack->symrefs; r; or = r, r = r->nxt)
		if (r->sm == t)
		{	if (!or)
				dfstack->symrefs = r->nxt;
			else
				or->nxt = r->nxt;

			r->nxt = dfs_free;
			dfs_free = r;

			if (debug) printf("DEL_STACK %s [%d]\n", t->nme->str, w);

			break;
		}
}

static int
on_stack(symentry_t *t)		/* locals only */
{	SymRef *r;

	if (dfstack)
	for (r = dfstack->symrefs; r; r = r->nxt)
		if (r->sm == t)
			return 1;
	return 0;
}

static int
on_safe(symentry_t *t)
{	SymRef *r;

	if (safe_stack)
	for (r = safe_stack->symrefs; r; r = r->nxt)
		if (r->sm == t)
			return 1;
	return 0;
}

int
snap_add(State *s, SymRef *r)
{	SymRef *t;

	for (t = s->snapshot; t; t = t->nxt)
		if (t->sm == r->sm
		&&  t->status == r->status)
			return 0;

	t = uno_getref(r->sm);
	t->status = r->status;
	t->n = r->n;
	t->nxt = s->snapshot;
	s->snapshot = t;

	return 1;
}

static SymRef *
copy_list(SymRef *s)
{	SymRef *r;

	if (!s) return (SymRef *) 0;

	r = uno_getref(s->sm);
	r->n = s->n;
	r->status = s->status;
	r->s_val = s->s_val;
	r->nxt = copy_list(s->nxt);

	return r;	/* maintains list in order */
}

static int
relevant(treenode *n)
{
	if (!n) return 0;

	if (n->syment
	&&  (on_glob(n->syment) || on_stack(n->syment)))
	{	if (debug)
			printf("---%s is relevant (%d)\n",
			n->syment->nme->str, on_glob(n->syment));
		return 1;
	}

	if (n->hdr.which == LEAF_T)
		return 0;

	return relevant(n->lnode) || relevant(n->rnode);
}

static PathCond *
copy_pc(PathCond *n)
{	PathCond *r;
	PathCond *s = n;

	while (s && !relevant(s->exp))	/* ! was missing... gjh 3/19/2002 */
		s = s->nxt;

	if (!s) return (PathCond *) 0;

	r = getpathframe();
	r->exp = s->exp;
	r->val = s->val;
	r->nxt = copy_pc(s->nxt);

	return r;	/* maintains list in order */
}

static int
in_lst(SymRef *list, SymRef *r)
{	SymRef *q;

	for (q = list; q; q = q->nxt)
		if (q->sm == r->sm
		&&  (q->status & DEF) == (r->status & DEF))
			return 1;
	return 0;
}

static int
same_pc(State *s)	/* for comments see 'covered(...)' */
{	PathCond *r, *q, *lq;
	int cnt = 0;

	if (!pathcond)
	{
here:		if (!s->seennone)
		{	s->seennone = 1;
			cnt++;
			if (debug) printf("seenone (%p)\n", pathcond);
		}
		goto done;
	}

	if (!s->pc)
	{	s->pc = copy_pc(pathcond);
		s->ip = copy_pc(s->pc);

		if (!s->pc)	/* nothing was relevant */
			goto here;

		cnt++;
		if (debug) printf("first setting of pc and ip (%p, %p)\n", s->pc, s->ip);
		goto done;
	}

	for (r = pathcond; r; r = r->nxt)
	{	if (!relevant(r->exp))
			continue;
		for (q = s->pc; q; q = q->nxt)
			if (q->exp == r->exp
			&&  q->val == r->val)
				break;
		if (!q)
		{	q = getpathframe();
			q->exp = r->exp;
			q->val = r->val;
			q->nxt = s->pc;
			s->pc = q;
			cnt++;
			if (debug) printf("adding to pc\n");
	}	}

	lq = (PathCond *) 0;
	for (r = s->ip; r; r = r->nxt)
	{	for (q = pathcond; q; q = q->nxt)
			if (q->exp == r->exp
			&&  q->val == r->val)
				break;
		if (!q)
		{	if (!lq)
				s->ip = r->nxt;
			else
				lq->nxt = r->nxt;
			cnt++;
			if (debug) printf("adding to ip\n");
		} else
			lq = r;
	}
done:
	if (debug)
	{	printf("PC Covered %s:\n", (cnt==0)?"yes":"no");
		for (r = pathcond; r; r = r->nxt)
		{	printf("	%s", x_stmnt(r->exp));
			printf("	%s\n", x_stmnt(r->val));
		}
		printf("PC:\n");
		for (r = s->pc; r; r = r->nxt)
		{	printf("	%s", x_stmnt(r->exp));
			printf("	%s\n", x_stmnt(r->val));
		}
		printf("IP:\n");
		for (r = s->ip; r; r = r->nxt)
		{	printf("	%s", x_stmnt(r->exp));
			printf("	%s\n", x_stmnt(r->val));
		}
	}
	return (cnt == 0);
}

static int
covered(State *s, SymRef *gr)
{	SymRef *r, *q, *lq;
	int cnt = 0;
#if 0
	this check secures coverage of global variables use only
	we are interested in U or R before D errors
	so the presence or absence of a DEF (1) on any gvar is important
	and determines its uniqueness
	we do not care about combinations of variables - just if
	individual variables have been seen with certain flags
#endif

	/* 1: each var in gr must have appeared in at least one
	 *    previous visit with the same DEF status, as recorded
	 *    in a list s->gi stored at state s for this purpose
	 */
	if (!gr)
	{	if (!s->seenempty)
		{	s->seenempty = 1;
			cnt++;
		}
		goto done;
	}

	if (!(s->gi))	/* first visit */
	{	s->gi = copy_list(gr);	/* seed initial visit list */
		s->il = copy_list(gr);	/* seed intersection list */
		cnt++;
		goto done;
	} else
	for (r = gr; r; r = r->nxt)		/* each var in gr (dfstack->globrefs) */
	{	for (q = s->gi; q; q = q->nxt)	/* see if already covered in s->gi */
			if (q->sm == r->sm
			&&  (r->status & DEF) == (q->status & DEF))
				break;
		if (!q)	/* not covered yet */
		{	q = uno_copy_ref(r);
			q->nxt = s->gi;
			s->gi = q;
			cnt++;
	}	}

	/* 2: each var absent from gr
		must have been absent in at least one previous visit
		i.e., must be absent from the intersection list
	 */
	lq = (SymRef *) 0;
	for (r = s->il; r; r = r->nxt)
	{	if (!in_lst(gr, r))	/* should drop r from il */
		{	if (!lq)
				s->il = r->nxt;
			else
				lq->nxt = r->nxt;
			cnt++;
		} else
			lq = r;		/* good, it's there */
	}
done:
	if (debug)
	{	printf("Covered %s:\n", (cnt==0)?"yes":"no");
		for (r = gr; r; r = r->nxt)
			printf("	%s	%d\n", r->sm->nme->str, r->status);
		printf("GI:\n");
		for (r = s->gi; r; r = r->nxt)
			printf("	%s	%d\n", r->sm->nme->str, r->status);
		printf("IL:\n");
		for (r = s->il; r; r = r->nxt)
			printf("	%s	%d\n", r->sm->nme->str, r->status);
	}

	return (cnt == 0);	/* true if nothing needed adding */
}

static int
dfs_push(State *s)
{	DfStack *d;
	SymRef *r, *n;
	int any_added = 0;

	d = uno_getframe();

	if (debug) printf("	--dfs_push <%p>\n", dfstack);

	if (dfstack)
	{	for (r = dfstack->symrefs; r; r = r->nxt)
		{	if (debug)
			printf("\t--cp symrefs %s status %d\n",
				r->sm->nme->str, r->status);

			if (snap_add(s, r))	/* local var not tracked from s before */
			{	n = uno_getref(r->sm);
				n->n = r->n;
				n->nxt = d->symrefs;
				d->symrefs = n;
				any_added = 1;
		}	}

		if (!covered(s, dfstack->globrefs))
			any_added = 1;	/* don't combine with next if */

		if (!same_pc(s))	/* matching path conditions */
			any_added = 1;

		if (any_added)
			d->globrefs = copy_list(dfstack->globrefs);	/* preserves order */
	}

	d->nxt = dfstack;
	dfstack = d;

	d = uno_getframe();
	if (safe_stack)
	for (r = safe_stack->symrefs; r; r = r->nxt)	/* copy sym refs */
	{	n = uno_getref(r->sm);
		n->n = r->n;
		n->nxt = d->symrefs;
		d->symrefs = n;
	}
	d->nxt = safe_stack;
	safe_stack = d;

	return any_added;
}

static void
dfs_pop(void)
{	DfStack *d;
	SymRef *r, *n;

	uno_assert((dfstack != NULL && safe_stack != NULL), "no dfstack or safe_stack");

	for (r = dfstack->symrefs; r; r = n)	/* free stack items */
	{	n = r->nxt;
		r->nxt = dfs_free;
		dfs_free = r;
	}
	for (r = dfstack->globrefs; r; r = n)
	{	n = r->nxt;
		r->nxt = dfs_free;
		dfs_free = r;
	}

	d = dfstack;
	dfstack = dfstack->nxt;
	d->nxt = dfs_frame;			/* free stackframe */
	dfs_frame = d;

	for (r = safe_stack->symrefs; r; r = n)	/* free sym refs */
	{	n = r->nxt;
		r->nxt = dfs_free;
		dfs_free = r;
	}
	d = safe_stack;
	safe_stack = safe_stack->nxt;
	d->nxt = dfs_frame;			/* free stackframe */
	dfs_frame = d;
}

static void
global_var(SymList *s, treenode *n)	/* track global, default-initialized, pointers */
{	leafnode *l;
	int extra = 0;

	if (s->mark & DECL)
	{	l = leftmost(n);

		if (s->mark & DEF)
			extra |= 8;

		if (s->mark & ARRAY_DECL)
			extra |= 128;		/* was 8 */

		if ((s->mark & PARAM)
		&&  (s->mark & USE))		/* comes from prototype decl or enum */
			extra |= 64;		/* suppress complaints -- was 1 */

		if  (s->mark & UNO_CONST)	/* enum constant */
			extra |= 8;		/* suppress complaints about lack of def */

		if (l)
		{	if (l->hdr.tok == STATIC) extra |= 2;	/* static global */
			if (l->hdr.tok == EXTRN)  extra |= 4;	/* extern global */
		}

		mark_guse(s->sm, n, extra);	/* global declared - see if used */

		if ((s->mark & IS_PTR)			/* pointer */
		&& !(extra & (64|128)))			/* not a param or array */
		{	if (!(s->mark & DEF))		/* uninitialized */
				add_glob(s->sm, n, 0);	/* an interesting global */
			else
				add_defs(s->sm, n);	/* def_b4_use of global ptr */
		}
	} else	/* not a declaration */
	{
		if ((s->mark & USE) && is_constant(s->sm->nme->str))
			s->mark |= UNO_CONST;	/* was s->mark |= DEF; */

		if ((s->mark & (USE|USEafterdef|REF0|REF1))
		||  (s->mark & DEREF))
		{	mark_guse(s->sm, n, 1);		/* at least one USE */
			add_gstack(s->sm, n, USE);	/* global used in this procedure */
		}

		if (s->mark & ALIAS)	/* address taken - def could happen via ptr */
		{	mark_guse(s->sm, n, 32);	/* flag to void global checks on this var */
			add_gstack(s->sm, n, ALIAS);	/* mark it as aliased */
		}

		if ((s->mark & (DEF|UNO_CONST)) && !(s->mark & DEREF))
		{	mark_guse(s->sm, n, 8);		/* at least one DEF */
			add_gstack(s->sm, n, DEF);	/* global set in this procedure */
		}

		if (on_glob(s->sm)	/* of interest: an uninitialized global ptr */
		&& !on_safe(s->sm))	/* not already declared moot on this path */
		{	if (((s->mark & (DEF|UNO_CONST))	/* defined */
			&& !(s->mark & REF0)
			&& !(s->mark & DEREF))
			||   (s->mark & ALIAS))		/* or address taken */
			{	add_defs(s->sm, n);	/* record def of global ptr */
				add_safe(s->sm, n);	/* moot in remainder of path */
			}
			if (s->mark & USE)		/* direct use */
			{
				if (checkpathcond(s->sm, n, 1))	/* unless value known */
					add_uses(s->sm, n);	/* use_b4_def in fct */
			}
			if ((s->mark & REF0)		/* ref0->x */
			||  (s->mark == DEREF)		/* *ptr = x; */
			|| ((s->mark & DEREF) && (s->mark & (USE|DEF|FCALL))))	/* ptr deref */
			{
				if (checkpathcond(s->sm, n, 2))	/* unless known value */
					add_derefs(s->sm, n);	/* use_b4_def in fct */
				else if (0) printf("check %s - %d - <%s>\n",
					s->sm->nme->str,
					checkpathcond(s->sm, n, 3),
					x_stmnt(n));
	}	}	}
}

static void
local_var(SymList *s, treenode *n)	/* track local, uninitialized non-array objects */
{	leafnode *l;

	if (debug)
		printf("mark %s, %d\n", s->sm->nme->str, s->mark);

	if (s->mark & DECL)			/* declaration */
	{	l = leftmost(n);
		if (l && l->hdr.tok == EXTRN)	/* extern declared locally */
		{	s->sm->decl_level = FILE_SCOPE;	/* fix */
			global_var(s, n);	/* global in disguise */
			return;
		}
		if (!(s->mark & (USE | USEafterdef)))
		{	add_locs(s->sm, n);	/* check if this local can remain un-used */
			if (s->mark & PARAM)
				mark_locs(s->sm, n, PARAM|(s->mark&FCALL));
			if (s->mark & IS_PTR)			/* a local pointer variable */
				mark_locs(s->sm, n, IS_PTR);	/* remember that */
			if (l && l->hdr.tok == STATIC)
				mark_locs(s->sm, n, ISTATIC);
		}

		if ((!l || l->hdr.tok != STATIC || (s->mark & IS_PTR))	/* not static, unless ptr */
		&&  !(s->mark & DEF)		/* not initialized in decl */
		&&  !(s->mark & ARRAY_DECL)	/* arraynames are initialized ptrs */
		&&  !(s->mark & USEafterdef))	/* a USEafterdef implies a DEF */
			add_stack(s->sm, n);	/* track this local */
	} else
	{
		if (s->mark & IN_SIZEOF)
			mark_locs(s->sm, n, IN_SIZEOF);	/* means: used in sizeof operation */

		if (s->mark & ALIAS)	/* address taken - def could happen via ptr */
		{	mark_locs(s->sm, n, ALIAS|(s->mark&FCALL));
			del_stack(s->sm, 0);	/* no point in keeping track */
		}

		if (s->mark & REF1)	/* x.y means x has a use and a def -- 5/2004 */
		{	/* printf("REF1 mark %s: %d\n", s->sm->nme->str, s->mark);	*/
			mark_locs(s->sm, n, USE|DEF);
			del_stack(s->sm, 1);
		}
#if 1
		/* added 12/2004 */
		if (s->mark & REF0)			/* x->y */
			mark_locs(s->sm, n, REF0);
		if (s->mark & DEREF)			/* *x */
			mark_locs(s->sm, n, DEREF);
#endif
		if ((s->mark & (USE|USEafterdef|REF0))	/* REF1 x.y is not a deref of x */
		||  (s->mark & DEREF))			/* deref counts as use */
			mark_locs(s->sm, n, USE|(s->mark&FCALL));	/* no longer un-used */

		if (n && n->hdr.tok == RETURN)
		{	extern int err_path;
			int x = is_local(s->sm);

			x = (x & ~DEREF);
			if (x != 0
			&& !(x& (PARAM | IN_SIZEOF | ISTATIC))
			&& !(s->mark & (DEREF|REF0))
			&&  (s->mark & ALIAS)		/* taking address */
			&& !has_fctcalls(n->hdr.defuse)
			&& !suppress(n->hdr.fnm, n->hdr.line))
			{	err_path++;	/* print fct args as well */
				fprintf(stdout, "uno: %s:%d: fct %s, returning address of local '%s' in <%s>\n",
					n->hdr.fnm, n->hdr.line,
					curgraph?curgraph->fctnm:"-",
					s->sm->nme->str, x_stmnt(n));
				err_path--;
				if (debug || Verbose) {
				fprintf(stdout, "s\t"); dflow_mark(stdout, s->mark); fprintf(stdout, "\n");
				fprintf(stdout, "x\t"); dflow_mark(stdout, x); fprintf(stdout, "\n");
				fprintf(stdout, "d\t"); dump_defuse(n->hdr.defuse, stdout); fprintf(stdout, "\n");
				}
			}	/* should also complain about basenames of arrays */
		}
	}

	if (on_stack(s->sm))				/* seen local decl */
	{	if (!(s->mark & USEafterdef)
		&&  (s->mark & (USE | REF0 | DEREF)))
		{	mark_locs(s->sm, n, USEbeforedef|(s->mark&FCALL));
			if (!(s->mark & INCOND))	/* could be benign nil-test */
				del_stack(s->sm, 2);	/* else we're done with it  */
		} else if (s->mark & (DEF | UNO_CONST))
		{	mark_locs(s->sm, n, DEF|(s->mark&FCALL));	/* def before use */
			del_stack(s->sm, 3);
	}	}
	else if (debug)
		printf("variable is not on stack\n");
}

static void
ana_work(DefUse *d, SymList *s, treenode *n)
{
	if (debug)
	{	printf("\tanawork: %s: ", s->sm->nme->str);
		dump_defuse(d, stdout);
		printf("\n");
	}
	if (0)
	{	printf("%s:%d: %s here: %d <<%s>>\t<%p>\n\t",
		n->hdr.fnm, n->hdr.line, s->sm->nme->str, s->mark, x_stmnt(n), s->sm);
		dump_defuse(d, stdout);
		printf("\n");
	}

	if (uno_ignore(s->sm)		/* symbol declared in "/usr/include/.." */
	||  (s->mark & REF2))		/* x->ref2 or x.ref2 -- compounds not yet   */
	{	return;
	}

	if (uno_p == 4)	/* the default */
	{	uno_bounds(s, d->aio, n);	/* array bounds */
	}

try_again:
	if (s->mark & FCALL)
	{	if (debug) printf("anawork->add_fcall\n");

		add_fcall(s->sm, n, (s->mark&USE)?USE:DEF);

		/* collect all places where a fct is called thru a ptr */
		/* and remember in which fct this happens... */
		if (s->mark & DEREF)
		{	Gst *g;
			if (Verbose)
				printf("%s:%d fct %s calls another fct via a ptr: %s...\n",
				n->hdr.fnm, n->hdr.line, curgraph->fctnm, s->sm->nme->str);
			g = (Gst *) emalloc(sizeof(Gst));
			g->gnm = curgraph;
			g->nxt = grst;
			grst = g;
		}
		return;
	} else if (is_recorded(s->sm->nme->str, n->hdr.fnm))	/* function name from prototype def */
	{	s->mark |= FCALL;
		goto try_again;
	} else
	{	if (debug) printf("\tnot a fcall...\n");
	}

	if (s->sm->decl_level < FUNCTION_SCOPE)
	{	global_var(s, n);
	} else
	{	local_var(s, n);
	}
}

static void
ana_reversed(DefUse *d, SymList *s, treenode *n)
{
	if (!s)	return;
	ana_reversed(d, s->nxt, n);
	ana_work(d, s, n);	/* last entry checked first */
}

static void
ana_defuse(treenode *n)
{	DefUse *d;
	SymList *e;

	if (!n) return;

	if (n->hdr.type == TN_IF)
	{	d = ((if_node *)n)->cond->hdr.defuse;

		if (lintlike && d
		&& !suppress(n->hdr.fnm, n->hdr.line))
		{	if (has_node_type(((if_node *)n)->cond, (int) TN_ASSIGN)
			&& !has_node_comp_ops(((if_node *)n)->cond)
			&& !v_reported(n))
				fprintf(stdout, "uno: warning, %s:%d: assignment in condition <%s>\n",
					n->hdr.fnm, n->hdr.line, x_stmnt(((if_node *)n)->cond));
			else
			for (e = d->other; e; e = e->nxt)
			if ((e->mark & DEF)
			&&  !(e->mark & UNO_CONST)
			&&  !v_reported(n))
				fprintf(stdout, "uno: warning, %s:%d: condition has side effect on '%s'\n",
					n->hdr.fnm, n->hdr.line, e->sm->nme->str);
		}
	} else
		d = n->hdr.defuse;

	if (debug && d)
	{	printf("uno: ==> ");
		dump_defuse(d, stdout);
		printf("\n");
	}

	if (d) ana_reversed(d, d->other, n);
}

static PathCond *
getpathframe(void)
{	PathCond *np;

	if (pathfree)
	{	np = pathfree;
		pathfree = pathfree->nxt;
	} else
		np = (PathCond *) emalloc(sizeof(PathCond));

	return np;
}

static void
newpathcond(treenode *exp, treenode *val)
{	PathCond *np;

	if (debug) printf("New Pathcondition <%s>\n", x_stmnt(exp));

	np = getpathframe();
	np->exp = exp;
	np->val = val;
	np->nxt = pathcond;
	pathcond = np;
}

static void
prevpathcond(void)
{	PathCond *np;

	np = pathcond;
	pathcond = pathcond->nxt;	/* uno cannot exclude nill-deref here */
	np->nxt = pathfree;
	pathfree = np;
}

static int
has_symbol(symentry_t *s, treenode *n)
{
	if (!n) return 0;

	if (n->syment == s)
		return 1;

	if (n->hdr.which == LEAF_T)
		return 0;

	return has_symbol(s, n->lnode) || has_symbol(s, n->rnode);
}

int
infeasible(treenode *e, treenode *v)
{	int w;
	char *s;

	if (!e || !v) return 0;

	if (e->hdr.type == TN_INT
	&&  v->hdr.tok  == IDENT)
	{	w = ((leafnode *)e)->data.ival;		/* could use const_expr evaluator here */
		s = ((leafnode *)v)->data.sval->str;

		if ((w != 0 && strcmp(s, "_false_") == 0)
		||  (w == 0 && strcmp(s,  "_true_") == 0))
			return 1;
	}

	return 0;
}

static int
is_zero_val(treenode *n)
{
	if (!n) return 0;

	if (n->hdr.type == TN_CAST)
		return is_zero_val(n->rnode);

	return (n->hdr.type == TN_INT
		&&  ((leafnode *)n)->data.ival == 0);
}

int
zero_test(treenode *ex)	/* true if condition ex is a simple comparison against 0 */
{
	if (!ex) return 0;

	if (ex->hdr.type == TN_IDENT)
		return 1;	/* s */

	if (ex->hdr.type != TN_EXPR
	||  ex->hdr.tok == AND
	||  ex->hdr.tok == OR)
		return 0;

	if (ex->hdr.tok == NOT
	&&  ex->lnode == ZT)
	{	if (ex->rnode->hdr.type == TN_IDENT)
			return 1;	/* !s */

		if (ex->rnode->hdr.type == TN_EXPR
		&&  ex->rnode->hdr.tok == NOT_EQ
		&&  ex->rnode->lnode
		&&  ex->rnode->lnode->hdr.type == TN_IDENT
		&&  is_zero_val(ex->rnode->rnode))
			return 1;	/* !(s != 0) */

		if (ex->rnode->hdr.type == TN_EXPR
		&&  ex->rnode->hdr.tok == EQUAL
		&&  ex->rnode->lnode
		&&  ex->rnode->lnode->hdr.type == TN_IDENT
		&&  is_zero_val(ex->rnode->rnode))
			return 1;	/* !(s == 0) */
	} else {
		if ((ex->hdr.tok == EQUAL || ex->hdr.tok == NOT_EQ)
		&&  ex->lnode
		&&  ex->lnode->hdr.type == TN_IDENT
		&&  is_zero_val(ex->rnode))
			return 1;	/* (s == 0) or (s != 0) */
	}
	return 0;
}

static int
simple_zero(symentry_t *s, treenode *ex)
{
	if (!ex) return 0;

	if (debug)
	printf("SZ %s, %s <%s>\n", s->nme->str, name_of_node(ex->hdr.type), x_stmnt(ex));

	if (ex->hdr.type == TN_IDENT
	&&  ex->syment == s)
		return 0;	/* s */

	if (ex->hdr.type != TN_EXPR)
		return 0;

	if (ex->hdr.tok == AND)
		return simple_zero(s, ex->lnode)
		||     simple_zero(s, ex->rnode);

	if (ex->hdr.tok == OR)
		return simple_zero(s, ex->lnode)
		&&     simple_zero(s, ex->rnode);

	if (ex->hdr.tok == NOT
	&&  ex->lnode == ZT
	&&  ex->rnode->hdr.type == TN_IDENT
	&&  ex->rnode->syment == s)
		return 1;	/* !s */

	if (ex->hdr.tok == NOT
	&&  ex->lnode == ZT
	&&  ex->rnode->hdr.type == TN_EXPR
	&&  ex->rnode->hdr.tok == NOT_EQ
	&&  ex->rnode->lnode->hdr.type == TN_IDENT
	&&  ex->rnode->lnode->syment == s
	&&  is_zero_val(ex->rnode->rnode))
		return 1;	/* !(s != 0) */

	if (ex->hdr.tok == EQUAL
	&&  ex->lnode
	&&  ex->lnode->hdr.type == TN_IDENT
	&&  ex->lnode->syment == s
	&&  is_zero_val(ex->rnode))
		return 1;	/* (s == 0) */

	return 0;
}

static int
simple_nonzero(symentry_t *s, treenode *ex)
{
	if (!ex) return 0;

	if (debug)
	printf("SNZ %s, %s <%s>\n", s->nme->str, name_of_node(ex->hdr.type), x_stmnt(ex));

	if (ex->hdr.type == TN_IDENT
	&&  ex->syment == s)
	{	if (debug) printf("	s -- pattern matches\n");
		return 1;	/* s */
	}

	if (ex->hdr.type != TN_EXPR)
		return 0;

	if (ex->hdr.tok == AND)
		return simple_nonzero(s, ex->lnode)
		||     simple_nonzero(s, ex->rnode);

	if (ex->hdr.tok == OR)
		return simple_nonzero(s, ex->lnode)
		&&     simple_nonzero(s, ex->rnode);

	if (ex->hdr.tok == NOT
	&&  ex->lnode == ZT
	&&  ex->rnode->hdr.type == TN_EXPR
	&&  ex->rnode->hdr.tok == EQUAL
	&&  ex->rnode->lnode
	&&  ex->rnode->lnode->hdr.type == TN_IDENT
	&&  ex->rnode->lnode->syment == s
	&&  is_zero_val(ex->rnode->rnode))
	{	if (debug) printf("	!(s == 0) -- pattern matches\n");
		return 1;	/* !(s == 0) */
	}

	if (ex->hdr.tok == NOT_EQ
	&&  ex->lnode
	&&  ex->lnode->hdr.type == TN_IDENT
	&&  ex->lnode->syment == s
	&&  is_zero_val(ex->rnode))
	{	if (debug) printf("	(s != 0) -- pattern matches\n");
		return 1;	/* (s != 0) */
	}

	if (debug) printf("	nonoftheabove (%d %p)\n", ex->hdr.tok, ex->lnode);
	return 0;
}

static int
simple_form(symentry_t *s, PathCond *np)	/* can we deduce that s is nonzero from np */
{	treenode *ex = np->exp;

	if (!((leafnode *)np->val)->data.sval) return 0;

	if (debug) printf("\t\tsimpleform: %s\n", ((leafnode *)np->val)->data.sval->str);

	if (strcmp(((leafnode *)np->val)->data.sval->str, "_true_") == 0)
		return simple_nonzero(s, ex);

	if (strcmp(((leafnode *)np->val)->data.sval->str, "_false_") == 0)
		return simple_zero(s, ex);

	return 0;
}

static int
checkpathcond(symentry_t *s, treenode *n, int callpt)
{	PathCond *np;

	if (debug) printf("%s:%d, CPC: symbol %s %s -- callpt %d\n",
		n->hdr.fnm, n->hdr.line, s->nme->str,
		name_of_node(n->hdr.type), callpt);

	if (n
	&&  n->hdr.type == TN_IF	/* current statement is conditional */
	&&  simple_nonzero(s, ((if_node *)n)->cond))
	{	if (debug)
		printf("CPC: symbol %s in cond, known nonzero <%s>\n",
			s->nme->str, x_stmnt(n));
		return 0;
	} else
	{	if (debug)
		printf("CPC: not known nonzero <%s>\n", x_stmnt(n));
	}

	for (np = pathcond; np; np = np->nxt)
	{
		if (debug)
		{	printf("\tcheckpathcond: val=%s exp=%s (%s)",
				toksym(np->val->hdr.tok, 1),
				x_stmnt(np->exp),
				name_of_node(np->exp->hdr.type));
			printf("\tval=%s\n", x_stmnt(np->val));
		}

		if (has_symbol(s, np->exp))
		{	if (debug) printf("	1\n");
			if (np->val->hdr.tok == IDENT
			&&  simple_form(s, np))
			{	if (debug) printf("	2\n");
				return 0;	/* voids insertion */
			}
			if (debug) printf("	3\n");
			continue;	/* can't tell from this condition */
		}
		if (has_symbol(s, np->val))
		{	if (debug) printf("	4\n");
			break;	/* can't tell -- and this may change the value */
		}
	}
	if (debug) printf("	5\n");

	return 1;
}

#if 0
void
debug_node(treenode *n, int tabs, char *p)
{	int i;

	if (!n) return;
	printf(p);
	for (i = 0; i < tabs; i++)
		fprintf(stdout, "   ");
	printf("%s\n", name_of_node(n->hdr.type));

	if (n->hdr.which == NODE_T)
	{	debug_node(n->lnode, tabs+1, "L");
		debug_node(n->rnode, tabs+1, "R");
	}
}

static void
putpathcond(symentry_t *s)
{	PathCond *np;

	for (np = pathcond; np; np = np->nxt)
	{
		fprintf(stderr, "checkpathcond: val=%s exp=%s %s  ==  ",
			toksym(np->val->hdr.tok, 1),
			name_of_node(np->exp->hdr.type),
			x_stmnt(np->exp));
		fprintf(stderr, "%s\n", x_stmnt(np->val));

		if (has_symbol(s, np->exp))
		{	fprintf(stderr, "	1\n");
			if (np->val->hdr.tok == IDENT
			&&  simple_form(s, np))
			{	fprintf(stderr, "	2\n");
				return;
			}
			fprintf(stderr, "	3\n");
			debug_node(np->exp, 0, "");
			return;
		}
		if (has_symbol(s, np->val))
		{	fprintf(stderr, "	4\n");
			return;
		}
	}
	fprintf(stderr, "	5\n");
}
#endif

static void
setknownzeros(treenode *n, Trans *t, PathCond *np)
{	DefUse *d;
	SymList *s;
	SymRef *r;

	if (!n) return;

	if (n->hdr.type == TN_IF)
		d = ((if_node *)n)->cond->hdr.defuse;
	else
		d = n->hdr.defuse;

	if (d)
	for (s = d->other; s; s = s->nxt)
		if (s->sm->decl_level < FUNCTION_SCOPE	/* global */
		&&  (s->mark & USE))
			if (simple_form(s->sm, np))
			{	/* s known nonzero */
				r = uno_getref(s->sm);
				r->nxt = t->knz;
				t->knz = r;
			}
}

static void
dfs_uno(State *s)
{	Trans *t;
	treenode *exp = ZT;

	if (!s) return;

	depth++;
	if (debug)
	{	if (s->n && s->n->hdr.which == LEAF_T)
			printf("%3d: Down <%s> %p <%d: %s>\n",
			depth,
			name_of_node(s->n->hdr.type),
			(s->n->hdr.defuse),
			s->n->hdr.line,
			x_stmnt(s->n));
		else
			printf("%3d: Down <%s:%s:%s> %p <%d: %s>\n",
			depth,
			s->n?name_of_node(s->n->hdr.type):"",
			(s->n && s->n->lnode)?name_of_node(s->n->lnode->hdr.type):"",
			(s->n && s->n->rnode)?name_of_node(s->n->rnode->hdr.type):"",
			(s->n?(s->n->hdr.defuse):0),
			s->n?s->n->hdr.line:-1,
			s->n?x_stmnt(s->n):"--");
		if (s->n->hdr.defuse) dump_defuse(s->n->hdr.defuse, stdout);
		fflush(stdout);
	}

	if (!dfs_push(s)	/* nothing new to track */
	&&   s->visited)	/* been here before     */
	{	if (debug)
			printf("	old\n");
		goto done;
	}
	if (debug)
	{	if (s->visited)
			printf("	revisit\n");
		else
			printf("	new\n");
	}
	s->visited = 1;

	ana_defuse(s->n);	/* uninitialized var analysis */

	if (s->iscond && s->n)
	{	if (s->n->hdr.type == TN_IF)
			exp = ((if_node *)s->n)->cond;
		else
			exp = s->n;
	}

	for (t = s->succ; t && t->branch; t = t->nxt)
	{	if (exp)
		{	if (debug)
			{	printf("Feasible?: %s", x_stmnt(exp));
				printf(" <==> %s\n", x_stmnt(t->cond));
			}
			if (infeasible(exp, t->cond))
			{	if (debug) printf("infeasible path\n");
				continue;	/* e.g. 0 == _true_ */
			}
			newpathcond(exp, t->cond);
#if 0
			if (inconsistent(s->n, pathcond))
			{	/*
				 * s->n has symbols that are known nonzero from previous pathconds
				 * and known zero from the current pathcond -- or vice versa
				 */
				prevpathcond();
				continue;
			}
#endif
			if (!t->knz) setknownzeros(s->n, t, pathcond);

			if (debug) dumknow(s->n, t);

			dfstack->state = pathcond;
		} else
		{	dfstack->state = getpathframe();
			dfstack->state->exp = s->n;
			dfstack->state->val = ZT;
		}
		dfs_uno(t->branch);

		if (exp)
		{	prevpathcond();
		} else
		{	dfstack->state->nxt = pathfree;
			pathfree = dfstack->state;
			dfstack->state = (PathCond *) 0;
		}
	}
done:
	if (debug) printf("%3d: Up\n", depth);
	depth--;
	dfs_pop();
}

static void
uno_statistics(void)
{	Graphs *g;
	SymRef *r;
	int cnt;

	if (1 || Verbose || lintlike || debug)
		bound_stats();

	if (!Verbose) return;

	if (uno_prop) gen_stats();

	g = find_graph("main");

	if (!g)
		return;

	for (cnt=0, g = graph; g; g = g->nxt)
		if (g != glob_decls)
			cnt++;

	if (localonly)
	{	printf("uno: %3d function declarations\n", cnt);

		for (cnt = 0, r = globs; r; r = r->nxt)
			cnt++;
		printf("uno: %3d uninitialized global pointers\n", cnt);
	}
}

static void
uno_indirect_calls(FILE *fd)
{	Gst *k, *m;
	/* for each fct in grst, add all entries of frst */
	/* assumes that any fct that can call another fct through a ptr,
	   can in principle call any of the fcts that are passed around
	   with fct ptrs */

	for (k = grst; k; k = k->nxt)
	for (m = frst; m; m = m->nxt)
		fprintf(fd, "p\t%s\t%s\t%d\n",
			k->gnm->fctnm, m->gnm->fctnm, m->gnm->status);

	/* separately also list all fcts that could be called indirectly */
	for (m = frst; m; m = m->nxt)
		fprintf(fd, "q\t%s\t%s\t%d\n",
			m->gnm->fctnm, "indirect", m->gnm->status);
}

static void
uno_snapshot(Graphs *g)
{
	if (localonly) return;

	fprintf(fd_uno, "%c\t%s\t%s\t%d\n",	/* function */
		(strcmp(g->scope, "global") == 0)? 'F' : 'f',
		g->fctnm,
		g->cfg->n->hdr.fnm,
		g->cfg->n->hdr.line);

	fprintf(fd_uno, "X\treturns_a\tvalue\t");
	if (g->status & (1|2|4))	/* 1:return value, 2:no return value, 4: cannot tell */
		fprintf(fd_uno, "%d\n", g->status);
	else
	{	fprintf(fd_uno, "2\n");
		if (debug)
		fprintf(stderr, "uno: using default return value status for %s\n",
			g->fctnm);
	}

	if (0) { SymRef *r; for (r = g->def_use; r; r = r->nxt)
	fprintf(fd_uno, "X\t%s\t%d\n", r->sm->nme->str, r->status); }

	/* record information in use of *globals* within this function */

	uno_report0(fd_uno, "D", DEF,           g->def_use);	/* def */
	uno_report0(fd_uno, "D", DEF|USE,       g->def_use);
	uno_report0(fd_uno, "D", DEF|USE|DEREF, g->def_use);

	uno_report0(fd_uno, "D", UNO_CONST,           g->def_use);
	uno_report0(fd_uno, "D", UNO_CONST|USE,       g->def_use);
	uno_report0(fd_uno, "D", UNO_CONST|USE|DEREF, g->def_use);

	uno_report1(fd_uno, "R", USE|DEREF,     g->suspect);	/* possible deref_useb4def */
	uno_report1(fd_uno, "U", USE,           g->suspect);	/* possible useb4def */

	uno_report1(fd_uno, "C", DEF,           g->fcalls);	/* fcts called, - return vals used */
	uno_report1(fd_uno, "c", USE,           g->fcalls);	/* fcts called, + return vals used */
	uno_report1(fd_uno, "b", DEF|USE,       g->fcalls);
#if 1
	/* fcts called through ptrs */
	uno_report1(fd_uno, "h", DEF|HIDE,      g->fcalls);	/* fcts called - can't tell retval */
	uno_report1(fd_uno, "i", USE|HIDE,      g->fcalls);
	uno_report1(fd_uno, "j", DEF|USE|HIDE,  g->fcalls);
#endif
	fprintf(fd_uno, "\n");
}

static void
gen_graph(Graphs *g)
{
	if (!g || g->visited) return;
	g->visited = 1;

	curgraph = g;

	dfs_uno(g->cfg);		/* collect info */

	if (!uno_prop) ana_locs(g);	/* check for unreferenced locals */

	uno_assert((dfstack == NULL), "internal error, dfstack non-zero");

	if (uno_p == 4)	/* -U3 or -local */
	{	if (!localonly)
			uno_snapshot(g);	/* write the .uno file */
		if (!uno_prop)
		{	cfg_unvisit(g->all);
			if (debug) printf("\n============\n");
			dfs_bound(g->cfg, ZT, ZT, ZS);	/* check for array indexing errors */
	}	}

	if (uno_prop && g->cfg != uno_prop)
	{	cfg_unvisit(g->all);
		dfs_generic(g->cfg);
	}
}

static void
dfs_reset(void)
{	Graphs *g;

	for (g = graph; g; g = g->nxt)
		g->visited = 0;
}

#if 0
static symentry_t *
mksym(char *s, treenode *n)
{
	return mk_vardecl(nmelook(s, strlen(s)+1), n);
}
#endif

static void
dup_graph(Graphs *g, treenode *n)
{	int d, r;

	d = (strcmp(g->scope, "global") != 0);
	r = is_static_fct;

	fprintf(stderr, "uno: fct %s redefined\n", g->fctnm);
	fprintf(stderr, "\tdefined%sat %s:%d, redefined%sat %s:%d\n",
		d?" file-static ":" ",
		g->cfg->n->hdr.fnm, g->cfg->n->hdr.line,
		r?" file-static ":" ",
		n->hdr.fnm, n->hdr.line);
}

static Graphs *
new_graph(treenode *n, char *str)
{	Graphs *g;

	for (g = graph; g; g = g->nxt)
		if (g != glob_decls
		&&  g->cfg != uno_prop
		&&  strcmp(g->fctnm, str) == 0
		&&  strcmp(g->cfg->n->hdr.fnm, "-1") == 0)
		{	if (debug)
			printf("uno: replacing template for %s\n", g->fctnm);
			break;
		}

	if (!g)
	for (g = graph; g; g = g->nxt)
	{	if (g == glob_decls
		||  g->cfg == uno_prop)
			continue;

		if (usecheck)
		if (g->cfg->n == n			/* unlikely conflict - or */
		||  (strcmp(g->fctnm, str) == 0		/* same name - and */
		&&   (!is_static_fct			/* new decl has global scope - or */
		||    strcmp(g->scope, "global") == 0	/* previous decl had global scope - or */
		||    strcmp(g->scope, cur_path) == 0)))/* prev decl has same file scope - or */
			dup_graph(g, n);		/* no break - look for other trouble */
	}

	if (!g)
	{	if (freegraph)
		{	g = freegraph;
			freegraph = g->nxt;
			memset(g, 0, sizeof(Graphs));
		} else
			g = (Graphs *) emalloc(sizeof(Graphs));
		if (!graph)
			graph = g;
		else
		{	g->nxt = graph;
			graph = g;
	}	}

	if (is_static_fct)
	{	g->scope = (char *) emalloc(strlen(cur_path)+1);
		strcpy(g->scope, cur_path);
	} else
		g->scope = "global";

	g->fctnm = (char *) emalloc(strlen(str)+1);
	strcpy(g->fctnm, str);
	g->cfg = create_state(g);
	g->cfg->n = n;

	curgraph = g;

	if (debug)
	printf("uno: new graph for fct %s, status %d (%s)\n", str, g->status, g->cfg->n->hdr.fnm);

	return g;
}

static void
uno_local(void)
{	Graphs *g;
	char *z, *unof;

	if (uno_p == 4 && !localonly)
	{	z = strstr(cur_file, ".c");
		uno_assert((z != NULL), "bad filename");
		*z = '\0';

		if (working_dir != NULL)
		{	unof = emalloc(strlen(working_dir)+1+strlen(cur_file)+strlen(".uno")+1);
			sprintf(unof, "%s/%s.uno", working_dir, cur_file);
		} else
		{	unof = emalloc(strlen(cur_dir)+strlen(cur_file)+strlen(".uno")+2);
			sprintf(unof, "%s/%s.uno", cur_dir, cur_file);
		}
		*z = '.';	/* restore */
		fd_uno = fopen(unof, "w");
		uno_assert((fd_uno != NULL), "cannot create .uno file");
	}

	dfstack = (DfStack *) 0;
	curgraph = glob_decls;

	if (debug) printf("== GLOBALS\n");

	dfs_uno(glob_decls->cfg); /* collect global declarations - build lists */

	if (debug) printf("== done with GLOBALS\n");

	dfstack = (DfStack *) 0;
	dfs_reset();

	for (g = graph; g; g = g->nxt)
		if (strcmp(g->fctnm, property) == 0)
		{	uno_prop = g->cfg;
			break;
		}

	for (g = graph; g; g = g->nxt)
		if (g != glob_decls)
		{	if (debug) printf("== GEN_GRAPH %s\n", g->fctnm); fflush(stdout);
			gen_graph(g);	/* the local check */
		}

	if (uno_p == 4 && !localonly)	/* add info on globals to snapshot file */
	{	SymRef *r;
		char c;

		uno_report0(fd_uno, "G", DEF,     glob_decls->def_use);	/* global def */
		uno_report0(fd_uno, "G", DEF|USE, glob_decls->def_use);

		/* 1 - use, 2 - static, 4 - extern, 8 - def, 16 - ub4d, 32 - alias */
		/* 4: imported, !2: exported */

		for (r = globuse; r; r = r->nxt)
		{
			if (r->status & 64)
				continue;	/* fct param */

			if (r->status & 32)	/* address taken & at least once */
				c = 'a';
			else
			{	int stc = r->status&~128;

				if (r->status & 128)
					stc |= 8;

				switch(stc) {
				case 0:		/* normal -def -use */
				case 4:		/* extern -def -use */
					c = 'v';
					break;

				case 8:		/* normal +def -use */
				case 8|16:	/* normal +def -use +useb4def */
				case 4|8:	/* extern +def -use */
				case 4|8|16:	/* extern +def -use +useb4def */
					c = 's';
					break;

				case 1:		/* normal -def +use */
				case 1|4:	/* extern -def +use */
				case 1|16:	/* normal -def +use +useb4def */
				case 1|4|16:	/* extern -def +use +useb4def */
					c = 'u';
					break;

				case 1|8:	/* normal +def +use */
				case 1|8|16:	/* normal +def +use +useb4def */
				case 1|4|8:	/* extern +def +use */
				case 1|4|8|16:	/* extern +def +use +useb4def */
					c = 't';
					break;
#if 0
				case 4|16:	/* extern +ub4d */
				case 16:	/* normal +ub4def */
				case 2:		/* static -- no use or def */
				case 1|2:	/* static +use  -- no def */
				case 2|16:	/* static +ub4d -- no def */
				case 2|8:	/* static +def -- no use */
				case 1|2|16:	/* statis +use +ub4d -- no def */
				case 1|2|8:	/* static +use +def */
				case 2|8|16:	/* static +def +ub4d */
				case 1|2|8|16:	/* static +use +def + ub4d */
				case 2|4:	/* impossible: static + extern */
				case 1|2|4:
				case 2|4|8:
				case 2|4|16:
				case 2|4|8|16:
				case 1|2|4|16:
				case 1|2|4|8:
				case 1|2|4|8|16:
#endif
				default: /* not relevant for global analysis */
					continue;
			}	}

			fprintf(fd_uno, "%c\t%s\t%s\t%d\n",
					c, r->sm->nme->str,
					r->n->hdr.fnm,
					r->n->hdr.line);
		}
		struct_fields(fd_uno);
		/* codes "y" and "z" identify used and unused fields in structs in this file */
		uno_indirect_calls(fd_uno);
	}
}

static int cnodes, cedges;

static void
cyclo_dfs(State *s)
{	State *n = (State *) 0, *lastn;
	Trans *t;

	if (!s || !s->n || s->visited) return;

	s->visited = 1;

	cnodes++;
	for (t = s->succ; t && t->branch; t = t->nxt)
	{	lastn = n;
		n = t->branch;
		cedges++;

		if (s->iscond && n == lastn)
			cedges--;
		/* case X: case Y: case Z: ...; break; */

		if (s->n->hdr.type == TN_JUMP)
			cedges++;
		cyclo_dfs(n);
	}
}

static void
cyclomatic(void)
{	Graphs *g;

	for (g = graph; g; g = g->nxt)
	{	if (strcmp("_globals_", g->fctnm) == 0)
			continue;

		cnodes = cedges = 0;
		cfg_unvisit(g->all);
		cyclo_dfs(g->cfg);
		printf("%10s\t%6d nodes\t%6d edges\tcyclo %6d\n",
			g->fctnm, cnodes, cedges, cedges - cnodes + 2 +1);
		/* +1 for the return node, which doesn't appear separately */
	}
}

static void
gen_dot(void)
{	Graphs *g;

	printf("digraph dodot {\n");
	printf("	ratio=auto;\n");

	for (g = graph; g; g = g->nxt)
	{	/* printf("want %s, got %s\n", want, g->fctnm); */
		if (strcmp(want, g->fctnm) == 0)
		{	printf("N00 [label=\"%s\"];\n", want);
			printf("N00 -> N%p;\n", g->cfg->n);
			cfg_unvisit(g->all);
			gen_lts(g->cfg);
			printf("\n");
			break;
	}	}
	printf("}\n");
}

static State *
add_seq(State *cur, treenode *n)
{	State *s;

	if (!cur) return cur;

	uno_assert((n != NULL), "bad call of add_seq");

	s = create_state(curgraph);
	s->n = n;

	cur->nxt = s;
	return s;
}

static State *
lts_node(State *n, treenode *root)
{	Graphs *g;
	State *now = n;

	if (!root) return n;

	switch (root->hdr.type) {
	case TN_FUNC_DECL:
		if (not_a_prototype)
		{	g = new_graph(root, nmestr(((leafnode *)(root->lnode))->data.sval));
			now = g->cfg;
		}	/* parentheses were missing, bug found by uno 10/7/01 */
		break;

	case TN_DECL:
		if (curgraph == glob_decls)
			add_seq(curgraph->all, root);
		else
			now = add_seq(now, root);
		break;

	case TN_LABEL:
		if (root->lnode->hdr.tok == CASE
		||  root->lnode->hdr.tok == DEFLT)	/* case label */
		{	State *t, *stc;
			Trans *tr;
			leafnode *si;
			treenode *sl, *sn;

			t = lts_top_switch(root);	/* innermost switch stmnt */
			si = mk_ident();	/* start of this case */
			sl = mk_label_node(si, root, "case");
			sn = mk_goto_node(si);

			/* make new label; insert here
			 * add goto to this label into t->succ
			 */
			now = add_seq(now, sl);
			record_label(sl->lnode, now);

			stc = create_state(curgraph);
			stc->n = sn;		/* jump to this case */

			tr = get_trans();
			tr->branch = stc;
			tr->cond = root->lnode;	/* the expr to be matched */
			tr->nxt = t->succ;
			t->succ = tr;
			now = add_seq(now, root);

			if (root->lnode->hdr.tok == DEFLT)
				sawdefault = 1;

			if (!root->rnode
			||  !root->rnode->rnode
			||  root->rnode->rnode->hdr.type != TN_LABEL)
				want_break(root);
		} else
		{	now = add_seq(now, root);
			record_label(root->lnode, now);
		}
		now = lts_tree(now, root->rnode);	/* stmnt labeled */
		break;

	case TN_JUMP:
		switch (root->hdr.tok) {
		case CONT:
			root = lts_top_start();
			saw_break();
			break;
		case BREAK:
			root = lts_top_end();
			saw_break();
			break;
		case GOTO:
			saw_break();
			break;
		case RETURN:
			/* lnode has a return expr, if any */
			fct_retval(root);
			saw_break();
			break;
		}
		now = add_seq(now, root);
		break;


	case TN_SWITCH:
		now = lts_switch(now, root);
		break;
	case TN_WHILE:
		now = lts_while(now, root);
		break;
	case TN_DOWHILE:
		now = lts_dowhile(now, root);
		break;

	case TN_TYPE_NME:
	case TN_NAME_LIST:
	case TN_FIELD_LIST:
	case TN_IDENT_LIST:
	case TN_TYPE_LIST:
	case TN_TRANS_LIST:
	case TN_INIT_LIST:
	case TN_PARAM_LIST:
	case TN_ENUM_LIST:
	case TN_EXPR_LIST:
	case TN_BLOCK:
	case TN_STEMNT_LIST:
	case TN_DECL_LIST:
	case TN_DECLS:
		now = lts_tree(now, root->lnode);
		now = lts_tree(now, root->rnode);
		break;

	case TN_EXPR:
	case TN_SELECT:
	case TN_DEREF:
	case TN_ARRAY_DECL:
	case TN_COMP_DECL:
	case TN_BIT_FIELD:
	case TN_PNTR:
	case TN_OBJ_DEF:
	case TN_OBJ_REF:
	case TN_INIT_BLK:
	case TN_ASSIGN:
	case TN_FUNC_CALL:
	case TN_INDEX:
	case TN_EMPTY:
		break;

	case TN_STEMNT:
		if (root->rnode
		&&  root->rnode->hdr.type != TN_LABEL
		&&  (root->rnode->hdr.type != TN_JUMP
		||   root->rnode->hdr.tok == RETURN))
			now = add_seq(now, root->rnode);

		/* could be a piece of code in the sequel
		   that is reachable only via a goto
		 */
		now = lts_tree(now, root->rnode);
		break;

	case TN_CAST:
		now = lts_tree(now, root->rnode);	/* operand */
		break;

	default:
		fprintf(stderr, "uno: line %3d unexpected node %s\n",
			root->hdr.line, name_of_node(root->hdr.type));
		break;
	}

	return now;
}

static treenode *
mk_label_node(leafnode *ident, treenode *n, char *s)
{	treenode *t;

	t = (treenode *) emalloc(sizeof(treenode));
	t->hdr.which = NODE_T;
	t->hdr.type = TN_LABEL;	/* just a place holder */
	t->hdr.tok = COLON;

	t->hdr.fnm = (char *) emalloc(strlen(n->hdr.fnm)+strlen(" after ''")+strlen(s)+1);
	sprintf(t->hdr.fnm, "%s after '%s'", n->hdr.fnm, s);

	t->hdr.line = n->hdr.line;
	t->lnode = (treenode *) ident;
	/* t->rnode -- normally points to stmnt labeled */
	return t;
}

static treenode *
mk_goto_node(leafnode *ident)
{	treenode *t;

	t = (treenode *) emalloc(sizeof(treenode));
	t->hdr.which = NODE_T;
	t->hdr.type = TN_JUMP;
	t->hdr.tok = GOTO;
	t->hdr.fnm = "UNO2";
	t->lnode = (treenode *) ident;

	return t;
}

static State *
lts_if(State *n, if_node *ifn)
{	State *now = n;

	if (!ifn) return now;

	if (ifn->hdr.tok == QUESTMARK)		/* cond?then:else */
	{	lts_tree(NS, ifn->cond);
		lts_tree(NS, ifn->then_n);
		lts_tree(NS, ifn->else_n);
	} else					/* if-then-else */
	{	State *ts, *es;
		Trans *tr;
		leafnode *ln;
		treenode *tn;
		treenode *tg;

		if (now->n->hdr.which != IF_T)
		{	fprintf(stderr, "\nuno: expected if (got %s)\n",
				name_of_nodetype(now->n->hdr.which));
		}
#if 0
		now->n = ifn->cond;	/* the condition */
#endif
		ts = create_state(curgraph);
		ts->n = ifn->then_n;
		es = create_state(curgraph);
		es->n = ifn->else_n;

		tr = get_trans();
		tr->cond = mk_bool("_true_");
		tr->branch = ts;
		tr->nxt = get_trans();
		tr->nxt->cond = mk_bool("_false_");
		tr->nxt->branch = es;

		now->succ = tr;

		ts = lts_tree(ts, ts->n);
		es = lts_tree(es, es->n);

		ln = mk_ident();
		tn = mk_goto_node(ln);
		tg = mk_label_node(ln, (treenode *) ifn, "if");

		if (!ifn->else_n)
			es->n = tn;
		else
			lts_tree(es, tn);

		now = lts_tree(ts, tg);
	}
	return now;
}

static treenode *
find_func_decl(treenode *n)
{
	uno_assert((n != NULL), "no funcdef");

	if (n->hdr.type == TN_FUNC_DECL)
		return n;

	/* must be a tn_pntr on lnode */

	return find_func_decl(n->rnode);
}

static State *
lts_for(State *n, for_node *forn)
{	State *now = n;
	leafnode *l;

	if (!forn) return now;

	if (forn->hdr.type == TN_FUNC_DEF)
	{
		if (!forn->stemnt)	/* no body */
			return now;	/* result of parse error */

		l = leftmost(forn->init);
		is_static_fct = (l && l->hdr.tok == STATIC);

		lts_tree(NS, forn->init);	/* type returned by fct */
		not_a_prototype++;
		now = lts_tree(NS, find_func_decl(forn->test));	/* fct name and param decls */
		not_a_prototype--;

		if (now) lts_tree(now, forn->stemnt);	/* fct body */

		curgraph = glob_decls;		/* back to global scope */
		now = curgraph->all;		/* last state from this scope */

	} else	/* for(init;test;incr) { stemnt; } */
	{
		State *ts, *es;
		Trans *tr;
		leafnode *si, *ci, *ei;
		treenode *el, *en, *sl, *cl, *sn, *cn;
		if_node *t;

		if (!forn->init)
			forn->init = mk_int(1);
		if (!forn->test)
			forn->test = mk_int(1);
		if (!forn->incr)
			forn->incr = mk_int(1);

		si = mk_ident();	/* start of loop */
		sl = mk_label_node(si, (treenode *) forn, "for");
		sn = mk_goto_node(si);

		ci = mk_ident();	/* continuation of loop */
		cl = mk_label_node(ci, (treenode *) forn, "for");
		cn = mk_goto_node(ci);

		ei = mk_ident();	/*   end of loop */
		el = mk_label_node(ei, (treenode *) forn, "for");
		en = mk_goto_node(ei);

		lts_push_start(cn);	/* set continuation point */
		lts_push_end(en);

		ts = create_state(curgraph);	/* then branch */
		ts->n = forn->stemnt;
		es = create_state(curgraph);	/* else branch */
		es->n = en;

		tr = get_trans();
		tr->cond = mk_bool("_true_");
		tr->branch = ts;
		tr->nxt = get_trans();
		tr->nxt->cond = mk_bool("_false_");
		tr->nxt->branch = es;

		if (now->n->hdr.which != FOR_T)
		{	fprintf(stderr, "\nuno: expected for (got %s)\n",
				name_of_nodetype(now->n->hdr.which));
		}

		now->n = forn->init;		/* replace for-node */
		now = lts_tree(now, sl);	/* add start label */

		t = (if_node *) emalloc(sizeof(if_node));
		t->hdr.which = IF_T;
		t->hdr.type = TN_IF;
		t->hdr.fnm = forn->hdr.fnm;
		t->hdr.line = forn->hdr.line;
		if (forn->test)
		{	t->hdr.defuse = forn->test->hdr.defuse;
#ifdef DEFTYP
			t->hdr.deftyp = forn->test->hdr.deftyp;
#endif
		}
		t->cond = forn->test;
		t->then_n = ts->n;		/* just for form, */
		t->else_n = es->n;		/* the real info is in tr */

		now = add_seq(now, (treenode *) t); /* add loop test */
		now->succ = tr;			/* with its two branches */

		ts = lts_tree(ts, ts->n);	/* find end of loop body */

		ts = lts_tree(ts, cl);		/* add continuation label */

		ts = add_seq(ts, forn->incr);	/* add loop increment */
		ts = lts_tree(ts, sn);		/* add jump back to start */
		now = lts_tree(ts, el);		/* place the end label after that */

		lts_pop_start();
		lts_pop_end();
	}
	return now;
}

static State *
lts_while(State *now, treenode *node)	/* lnode - cond; rnode - body */
{	State *ts, *es;
	Trans *tr;
	leafnode *si, *ei;
	treenode *el, *en;
	treenode *sl, *sn;
	if_node *t;

	if (!node->lnode)
		node->lnode = mk_int(1);
	if (!node->rnode)
		node->rnode = mk_int(1);

	si = mk_ident();	/* start of loop */
	sl = mk_label_node(si, node, "while");
	sn = mk_goto_node(si);

	ei = mk_ident();	/*   end of loop */
	el = mk_label_node(ei, node, "while");
	en = mk_goto_node(ei);

	lts_push_start(sn);
	lts_push_end(en);

	ts = create_state(curgraph);	/* then branch */
	ts->n = node->rnode;		/* while body */
	es = create_state(curgraph);	/* else branch */
	es->n = en;

	tr = get_trans();
	tr->cond = mk_bool("_true_");
	tr->branch = ts;
	tr->nxt = get_trans();
	tr->nxt->cond = mk_bool("_false_");
	tr->nxt->branch = es;

	now = lts_tree(now, sl);	/* add start label */

	t = (if_node *) emalloc(sizeof(if_node));
	t->hdr.which = IF_T;
	t->hdr.type = TN_IF;

	t->hdr.fnm = node->hdr.fnm;
	t->hdr.line = node->hdr.line;
	t->hdr.defuse = node->lnode->hdr.defuse;
#ifdef DEFTYP
	t->hdr.deftyp = node->lnode->hdr.deftyp;
#endif

	t->cond = node->lnode;		/* loop condition */
	t->then_n = ts->n;		/* just for form, */
	t->else_n = es->n;		/* the real info is in tr */

	now = add_seq(now, (treenode *) t); /* add loop test */
	now->succ = tr;			/* with its two branches */

	ts = lts_tree(ts, ts->n);	/* find end of loop body */
	ts = lts_tree(ts, sn);		/* add jump back to start */
	now = lts_tree(ts, el);		/* place the end label after that */

	lts_pop_start();
	lts_pop_end();

	return now;
}

static State *
lts_dowhile(State *now, treenode *node)	/* lnode - cond; rnode - body */
{	State *ts, *es;
	Trans *tr;
	leafnode *si, *ei;
	treenode *el, *en;
	treenode *sl, *sn;
	if_node *t;

	if (!node->lnode)
		node->lnode = mk_int(1);
	if (!node->rnode)
		node->rnode = mk_int(1);

	si = mk_ident();	/* start of loop */
	sl = mk_label_node(si, node, "do-while");
	sn = mk_goto_node(si);

	ei = mk_ident();	/*   end of loop */
	el = mk_label_node(ei, node, "do-while");
	en = mk_goto_node(ei);

	lts_push_start(sn);
	lts_push_end(en);

	ts = create_state(curgraph);	/* then branch */
	ts->n = sn;				/* jump to start */
	es = create_state(curgraph);	/* else branch */
	es->n = en;				/* jump to end */

	tr = get_trans();
	tr->cond = mk_bool("_true_");
	tr->branch = ts;
	tr->nxt = get_trans();
	tr->nxt->cond = mk_bool("_false_");
	tr->nxt->branch = es;

	now = lts_tree(now, sl);		/* place start label */
	now = lts_tree(now, node->rnode);	/* loop body */

	t = (if_node *) emalloc(sizeof(if_node));
	t->hdr.which = IF_T;
	t->hdr.type = TN_IF;

	t->hdr.fnm = node->hdr.fnm;
	t->hdr.line = node->hdr.line;
	t->hdr.defuse = node->lnode->hdr.defuse;
#ifdef DEFTYP
	t->hdr.deftyp = node->lnode->hdr.deftyp;
#endif

	t->cond = node->lnode;		/* loop condition */
	t->then_n = ts->n;		/* just for form, */
	t->else_n = es->n;		/* the real info is in tr */

	now = add_seq(now, (treenode *) t); /* add loop test */
	now->succ = tr;			/* with its two branches */

	now = lts_tree(now, el);	/* place end label */

	lts_pop_start();
	lts_pop_end();

	return now;
}

static State *
lts_switch(State *now, treenode *node)
{	leafnode *ei;
	treenode *el, *en;
	int osaw;

	ei = mk_ident();	/* end of switch */
	el = mk_label_node(ei, node, "switch");
	en = mk_goto_node(ei);

	lts_push_end(en);	/* set break destination */

	if (!node->lnode)
		node->lnode = mk_int(1);

	/* lnode - switch expr
	 * rnode - cases
	 */
	lts_push_switch(now);	/* this is where jumps to case labels will go */
	now->n = node->lnode;	/* the switch expression */

	osaw = sawdefault;
	sawdefault = 0;

	now = lts_tree(now, node->rnode); /* process breaks and case labels */

	if (!sawdefault)	/* add nil jump to end */
	{	State *t, *stc;
		Trans *tr;

		want_break(node);

		stc = create_state(curgraph);
		stc->n = lts_top_end();		/* jump to endlabel */

		t = lts_top_switch(node);	/* add to switch stmnt */

		tr = get_trans();
		tr->branch = stc;
		tr->cond = mk_deflt();

		tr->nxt = t->succ;
		t->succ = tr;

		now = add_seq(now, stc->n);
	}

	sawdefault = osaw;

	now = lts_tree(now, el);	/* place end label */

	lts_pop_end();
	lts_pop_switch();
	return now;
}

static State *
lts_tree(State *n, treenode *root)
{	State *now = n;

	if (!root) return n;

	switch (root->hdr.which) {
	case IF_T:
		now = lts_if(now, (if_node *) root);
		break;

	case FOR_T:
		now = lts_for(now, (for_node *) root);
		break;

	case NODE_T:
		now = lts_node(now, root);
		break;

	case LEAF_T:
	case NONE_T:
		break;

	default:
		fprintf(stderr, "uno: unhandled type %s\n",
			name_of_nodetype(root->hdr.which));
		break;
	}
	return now;
}

static SymExt *
rel_symext(SymExt *s)
{
	if (s)
	{	rel_symext(s->nxt);
		s->nxt = freesymext;
		freesymext = s;
	}
	return (SymExt *) 0;
}

static SymRef *
rel_symref(SymRef *s)
{
	if (s)
	{	rel_symref(s->nxt);
		s->nxt = freesymref;
		freesymref = s;
	}
	return (SymRef *) 0;
}

static Trans *
rel_trans(Trans *t)
{
	if (t)
	{	rel_trans(t->nxt);
		t->knz = rel_symref(t->knz);
		t->nxt = freetrans;
		freetrans = t;
	}

	return (Trans *) 0;
}

static State *
rel_state(State *s)
{
	if (s)
	{	rel_state(s->all);
		s->gi = rel_symref(s->gi);
		s->il = rel_symref(s->il);
		s->snapshot = rel_symref(s->snapshot);
		s->succ = rel_trans(s->succ);
		s->direct = rel_trans(s->direct);

		s->all = freestate;
		freestate = s;
	}
	return (State *) 0;
}

static Graphs *
rel_graph(Graphs *g)
{
	if (g)
	{	rel_graph(g->nxt);
		g->all = rel_state(g->all);
		g->fcalls  = rel_symext(g->fcalls);
		g->suspect = rel_symext(g->suspect);
		g->def_use = rel_symref(g->def_use);
		g->locs = rel_symref(g->locs);

		g->nxt = freegraph;
		freegraph = g;
	}
	return (Graphs *) 0;
}

void
lts_start(treenode *root)
{	Graphs *g;
	State *now;
	treenode *n;

	stck    = (SwStack *) 0;
	graph   = rel_graph(graph);
	glob_decls = (Graphs *) 0;
	globs   = rev_release(globs);
	globuse = rev_release(globuse);
	lnodes  = rel_label(lnodes);
	depth   = 0;
	uno_prop = (State *) 0;

	bound_reset();
	gen_reset();
	fallthru = rel_sframe(fallthru);

	n = (treenode *) emalloc(sizeof(treenode));
#if 0
	n->hdr.fnm = (char *) emalloc(strlen(file_name)+1);
	strcpy(n->hdr.fnm, file_name);
#else
	n->hdr.fnm = (char *) emalloc(strlen(cur_dir)+strlen(cur_file)+2);
	strcpy(n->hdr.fnm, cur_dir);
	strcat(n->hdr.fnm, "/");
	strcat(n->hdr.fnm, cur_file);
#endif
	n->hdr.line = 0;

	g = new_graph(n, "_globals_");
	now = g->cfg;
	glob_decls = curgraph;

	lts_tree(now, root);	/* basic construction of cfg */

	for (g = graph; g; g = g->nxt)
		prep_graph(g);	/* fixing links in cfg */

	if (uno_p == 2)		/* -cfg    */
	{	gen_dot();
		return;
	}
	if (cyclo)		/* -cyclo */
	{	cyclomatic();
		return;
	}

	uno_local();		/* check local vars */

	if (show_sharing)
		uno_shared();

	if (!uno_prop)
	{	uno_guse();	/* check for unused globals */
		show_fall();	/* fallthru in switches */
	}

	uno_statistics();

	if (!localonly)
	{	nut_start();
		fclose(fd_uno);
	}
}
