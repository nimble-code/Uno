/***** uno: dflow.c *****/

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
#include "prnttree.h"
#include "c_gram.h"
#include "symtab.h"

#define VERY_LARGE	131072
#define MEDIUM_LARGE	4096

extern int	Verbose, uno_p, vis_p, type_check, picky;
extern int	check_else_chains, check_compounds, xrepro;
extern char	*want, *progname;

       void	bugger(char *, treenode *, int);
extern void	*emalloc(size_t);
extern char	*x_stmnt(treenode *);
extern int	find_symbol(scopetab_t *, symentry_t *);
extern symentry_t *new_symentry(void);
extern void	location(treenode *);
extern int	has_upper(char *);
extern int	exclude_location(treenode *);

static char SaveMe[1024];
static int  is_a_prototype = 1;

static char	*Fct_name;
static int	RealDecls;
static int	watch;	/* debugging */
static int	is_final;
static char	complaint[MEDIUM_LARGE];
static char	c_origin[VERY_LARGE];
static DuG	*d_g;

static SymList	*freesyml = NULL;
static SymList	*allsym = NULL;
#if 0
static ArList	*freelar = NULL;
#endif

char *
doit(leafnode *leaf, int how)
{	scopetab_t *z;
	static char bstr[1024];
	static char lstr[1024];

	if (!leaf) return (char *) 0;

	if (leaf->syment && leaf->syment->nes)
		z = leaf->syment->nes;
	else
		z = (scopetab_t *) 0;

	strcpy(lstr, "");
	switch (how) {
	case 2:	sprintf(bstr, "%d:", leaf->hdr.line);
		strcat(lstr, bstr);	/* fall thru */
	case 0:	sprintf(bstr, "%s::", z?z->owner:"-");
		strcat(lstr, bstr);	/* fall thru */
	case 1:	sprintf(bstr, "%s%s", nmestr(leaf->data.sval), (!how)?" ":"");
		strcat(lstr, bstr);
	}
	return &lstr[0];
}

DuG *
dep_node(SymList *a, int imark)
{	DuG *g;

	for (g = d_g; g; g = g->nxt)
		if (g->sm == a->sm)
		{	g->marks |= imark;
			goto done;
		}

	g = (DuG *) emalloc(sizeof(DuG));

	if (!a->sm) printf("%s: dep_node without symbol\n", progname);

	g->sm = a->sm;
	g->marks = imark;
	g->rdcls |= RealDecls;
	g->d_e = (DuGP *) 0;
	g->nxt = d_g;
	d_g = g;
done:
	return g;
}

int
dep_edge(DuG *a, DuG *b, int dist)
{	DuGP *e;

	if (a->sm == b->sm)
		return 0;		/* self-loop */

	for (e = a->d_e; e; e = e->nxt)
	{	if (e->ptr == b)
			return 0;	/* already there */
	}

	e = (DuGP *) emalloc(sizeof(DuGP));
	e->ptr = b;
	e->dist = dist;
	e->nxt = a->d_e;
	a->d_e = e;

	return 1;
}

void
dep_graph(DefUse *d)
{	SymList *s, *t;
	DuG *a, *b;

	if (!d || uno_p) return;

	if (!d->def)
	for (t = d->use; t; t = t->nxt)
		dep_node(t, USE);

	for (s = d->def; s; s = s->nxt)
	{	a = dep_node(s, DEF);
		for (t = d->use; t; t = t->nxt)
		{	b = dep_node(t, USE);
			if (s->sm != t->sm)
				dep_edge(a, b, 1);
		}
	}
}

void
dump_defuse(DefUse *d, FILE *fp)
{	SymList *s;
	ArList *a;

	if (!d) return;

	if (d->def)
	{	fprintf(fp, "[D: ");
		for (s = d->def; s; s = s->nxt)
			fprintf(fp, "%s ", s->sm->nme->str);
		fprintf(fp, "] ");
	}
	if (d->use)
	{	fprintf(fp, "[U: ");
		for (s = d->use; s; s = s->nxt)
			fprintf(fp, "%s ", s->sm->nme->str);
		fprintf(fp, "] ");
	}
	if (d->other)
	{	fprintf(fp, "[O: ");
		for (s = d->other; s; s = s->nxt)
		{	fprintf(fp, "%s=", s->sm->nme->str);
			if (s->mark & DEF)	fprintf(fp, "D");
			if (s->mark & USE)	fprintf(fp, "U");
			if (s->mark & FCALL)	fprintf(fp, "F");
			if (s->mark & (REF0|REF1)) fprintf(fp, "r");
			if (s->mark & REF2)	fprintf(fp, "R");
			if (s->mark & DEREF)	fprintf(fp, "*");
			if (s->mark & ALIAS)	fprintf(fp, "&");
			if (s->mark & ARRAY_DECL)	fprintf(fp, "A");
			if (s->mark & HIDE)	fprintf(fp, "H");
			if (s->mark & DECL)	fprintf(fp, "T");

			if (s->mark & USEafterdef)	fprintf(fp, "Ua");
			if (s->mark & USEbeforedef)	fprintf(fp, "Ub");
			if (s->mark & PARAM)	fprintf(fp, "P");
			if (s->mark & IN_SIZEOF)	fprintf(fp, "S");
			if (s->mark & IS_PTR)	fprintf(fp, "p");

		/*	fprintf(fp, " <%d>", s->sm->decl_level);	*/
			fprintf(fp, " ");
		}
		fprintf(fp, "] ");
	}

	if (d->aio && 0)
		for (a = d->aio; a; a = a->nxt)
			fprintf(fp, "ar=%s ", x_stmnt(a->tn));
}

static int
same_defuse(DefUse *a, DefUse *b)
{	SymList *s, *t;

	if (!a && !b)
		return 1;
	if (!a || !b)
		return 0;

	for (s = a->def, t = b->def; s && t; s = s->nxt, t = t->nxt)
		if (s->sm != t->sm)
			return 0;
	if (s || t)
		return 0;
	for (s = a->use, t = b->use; s && t; s = s->nxt, t = t->nxt)
		if (s->sm != t->sm)
			return 0;
	if (s || t)
		return 0;

	for (s = a->other, t = b->other; s && t; s = s->nxt, t = t->nxt)
		if (s->sm != t->sm
		||  s->mark != t->mark)
			return 0;

	if (s || t)
		return 0;
	return 1;
}

void
attach_defuse(treenode *n, char *t, DefUse *d)
{
	if (!d || !n) return;

	if (d->def || d->use)
		dep_graph(d);	/* update the graph */

	if (n->hdr.defuse)
	{	if (n->hdr.defuse != d
		&&  !same_defuse(d, n->hdr.defuse))
		{	printf("%s: %s:%d attach_defuse conflict %s %s\n",
				progname, n->hdr.fnm, n->hdr.line,
#ifdef DEFTYP
				n->hdr.deftyp,
#else
				"",
#endif
				t);
			printf("OLD:\n");
			dump_defuse(n->hdr.defuse, stdout);
			printf("\nNEW:\n");
			dump_defuse(d, stdout);
			printf("\n");
		}
	} else
	{	n->hdr.defuse = d;
#ifdef DEFTYP
		n->hdr.deftyp = t;
#endif
	}
}

void
rel_all(SymList *s)
{
	if (!s) return;

	rel_all(s->all);
	s->all = freesyml;
	freesyml = s;
}

void
dflow_reset(void)
{
	rel_all(allsym);
	allsym = (SymList *) 0;
}

SymList *
symadd(symentry_t *sm, int mark)
{	SymList *sl;

	if (freesyml)
	{	sl = freesyml;
		freesyml = freesyml->all;
		memset(sl, 0, sizeof(SymList));
	} else
		sl = (SymList *) emalloc(sizeof(SymList));

	sl->nxt = (SymList *) 0;
	sl->mark = mark;
	sl->sm  = sm;

	sl->all = allsym;
	allsym = sl;

	return sl;
}

static ArList *
get_arlist(void)
{	ArList *ns;
#if 0
	if (freelar)
	{	ns = freelar;
		freelar = ns->nxt;
		memset(ns, 0, sizeof(ArList));
	} else
#endif
		ns = (ArList *) emalloc(sizeof(ArList));
	return ns;
}

static ArList *
merge_aio(ArList *a1, ArList *a2)
{	ArList *s, *t, *ns;
	ArList *add_to_a1 = (ArList *) 0;
	ArList *last_in   = (ArList *) 0;

	if (!a1) return a2;
	if (!a2) return a1;

	for (t = a2; t; t = t->nxt)
	{	for (s = a1; s; s = s->nxt)
			if (s->tn == t->tn)
				break;

		if (!s) /* add t */
		{	ns = get_arlist();
			ns->tn = t->tn;
			if (!last_in)	/* preserve relative order */
				add_to_a1 = last_in = ns;
			else
			{	last_in->nxt = ns;
				last_in = ns;
	}	}	}

	if (!last_in)
		return a1;
	last_in->nxt = a1;
	a1 = add_to_a1;
	return a1;
}

static SymList *
merge_syms(SymList *s1, SymList *s2)
{	SymList *s, *t, *ns;
	SymList *add_to_s1 = (SymList *) 0;
	SymList *last_in   = (SymList *) 0;

	/* static int mcnt=1; */

	if (!s1) return s2;
	if (!s2) return s1;

	for (t = s2; t; t = t->nxt)
	{	for (s = s1; s; s = s->nxt)
			if (s->sm == t->sm
			&&  s->mark == t->mark)
				break;

		if (!s) /* add t */
		{	ns = symadd(t->sm, t->mark);
			/* preserve relative order */
			if (!last_in)
				add_to_s1 = last_in = ns;
			else
			{	last_in->nxt = ns;
				last_in = ns;
			}
	}	}

	if (!last_in)
		return s1;
	last_in->nxt = s1;
	s1 = add_to_s1;
	return s1;
}

static void
track_clr(void)
{
	memset(complaint, 0, sizeof(complaint));
}

static DefUse *
merge_lists(DefUse *d1, DefUse *d2)
{	DefUse *nd;

	if (!d1) return d2;
	if (!d2) return d1;

	nd = (DefUse *) emalloc(sizeof(DefUse));
	if (!uno_p)
	{	nd->def   = merge_syms(d1->def, d2->def);
		nd->use   = merge_syms(d1->use, d2->use);
	}
	nd->other = merge_syms(d1->other, d2->other);
	nd->aio   = merge_aio(d1->aio, d2->aio);

	if (type_check)
	{	if (!d1->der_type)
		{	nd->der_type = d2->der_type;
		} else if (!d2->der_type)
		{	nd->der_type = d1->der_type;
		} else if (strcmp(d1->der_type, d2->der_type) == 0)
		{	nd->der_type = d1->der_type;
		} else
		{	nd->der_type = NULL;
			strcpy(complaint, d1->der_type);
			strcat(complaint, " <-> ");
			strcat(complaint, d2->der_type);
		}
		if (is_final > 0)
		{	nd->der_type = NULL;
			if (strlen(complaint) > 0
			&&  strchr(complaint, '?') == NULL)
			{	printf("%s :: %s\n", c_origin, complaint);
				memset(complaint, 0, sizeof(complaint));
				memset(c_origin,  0, sizeof(c_origin));
	}	}	}
	return nd;
}

static int
def_and_use(int tok)
{
	switch (tok) {
	case PLUS_EQ:
	case MINUS_EQ:
	case STAR_EQ:
	case DIV_EQ:
	case MOD_EQ:
	case B_NOT_EQ:
	case B_AND_EQ:
	case B_OR_EQ:
	case B_XOR_EQ:
	case L_SHIFT_EQ:
	case R_SHIFT_EQ:
		return 1;
	}
	return 0;
}

static char ref1_pref[1024];

static char *
set_u(struct symentry *x, char *nu)
{	char *u;

	if (!Fct_name) goto isglob;

	if (!x)
	{	u = (char *) emalloc(strlen(nu)+strlen(Fct_name)+1-1 + strlen(ref1_pref)+2);
		sprintf(u, "%s%s", Fct_name, &nu[1]);
	} else if (x->decl_level == 0)
	{	u = (char *) emalloc(strlen(nu)+strlen("fct")+1-1 + strlen(ref1_pref)+2);
		sprintf(u, "%s%s", "fct", &nu[1]);
	} else if (x->decl_level == 3)	/* is local */
	{	u = (char *) emalloc(strlen(nu)+strlen(Fct_name)+1-1 + strlen(ref1_pref)+2);
		sprintf(u, "%s%s", Fct_name, &nu[1]);
	} else	/* extern 1 or global 2 */
	{
isglob:		u = (char *) emalloc(strlen(nu)+strlen("glob")+1-1 + strlen(ref1_pref)+2);
		sprintf(u, "%s%s", "glob", &nu[1]);
	}
	return u;
}

typedef struct Fbase {
	char *nm;
	int   ln;
	struct Fbase *fcalls;
	struct Fbase *nxt;
} Fbase;

static Fbase *fbase;

void
set_fbase(int ln, char *s)
{	Fbase *f;

	fbase = (Fbase *) 0;

	f = (Fbase *) emalloc(sizeof(Fbase));
	f->nm = (char *) emalloc(strlen(s)+1);
	strcpy(f->nm, s);
	f->ln = ln;
	f->fcalls = (Fbase *) 0;
	f->nxt = fbase;
	fbase = f;
}

static void
add_fbase(int ln, char *s)
{	Fbase *f, *g;

	if (!vis_p) return;

	if (!fbase)
		set_fbase(0, want);

	f = (Fbase *) emalloc(sizeof(Fbase));
	f->nm = (char *) emalloc(strlen(s)+1);
	strcpy(f->nm, s);
	f->ln = ln;
	f->nxt = f->fcalls = (Fbase *) 0;

	for (g = fbase->fcalls; g; g = g->fcalls)
		if (strcmp(g->nm, s) == 0)	/* follows a match */
		{	f->fcalls = g->fcalls;
			g->fcalls = f;
			return;
		}

	f->fcalls = fbase->fcalls;	/* or at the front */
	fbase->fcalls = f;
}

void
storefname(treenode *child)
{
	strcpy(SaveMe, "");
	bugger(SaveMe, child->lnode, 1);
	add_fbase(child->hdr.line, SaveMe);
}

void
dflow_mark(FILE *fd, int mark)
{	int i;

	for (i = 1; i <= ANY; i *= 2)
		switch (mark&i) {
		case   DEF: fprintf(fd, "DEF "); break;
		case FCALL: fprintf(fd, "FCALL "); break;
		case   USE: fprintf(fd, "USE "); break;
		case  REF0: fprintf(fd, "REF0 "); break;
		case  REF1: fprintf(fd, "REF1 "); break;
		case  REF2: fprintf(fd, "REF2 "); break;
		case DEREF: fprintf(fd, "DEREF "); break;
		case ALIAS: fprintf(fd, "ALIAS "); break;
		case ARRAY_DECL: fprintf(fd, "ARRAY_DECL "); break;
		case HIDE: fprintf(fd, "HIDE "); break;
		case DECL: fprintf(fd, "DECL "); break;
		case USEafterdef: fprintf(fd, "USEafterdef "); break;
		case USEbeforedef: fprintf(fd, "USEbeforedef "); break;
		case UNO_CONST: fprintf(fd, "CONST "); break;
		case PARAM: fprintf(fd, "PARAM "); break;
		case IN_SIZEOF: fprintf(fd, "IN_SIZEOF "); break;
		case IS_PTR: fprintf(fd, "IS_PTR "); break;
		case INCOND: fprintf(fd, "INCOND "); break;
		}
}

static void
add_aio(DefUse *d, treenode *n)
{	ArList *nio;

	if (!d)
	{	if (0 && !exclude_location(n))
			printf("uno: %s:%d aio without d to attach to\n",
			n->hdr.fnm, n->hdr.line);
		return;
	}
	for (nio = d->aio; nio; nio = nio->nxt)
		if (nio->tn == n)
			return;

	nio = get_arlist();
	nio->tn = n;
	nio->nxt = d->aio;
	d->aio = nio;
}

static void
sym_babble(leafnode *leaf, unsigned long mark)
{	char *q = "--";
	scopetab_t *s = (scopetab_t *) 0;

	if (!leaf) return;

	if (leaf->syment
	&&  leaf->syment->nes)
		s = leaf->syment->nes;	/* name enclosing scope */

	fprintf(stdout, "%3d, %s::%s\t",
		leaf->hdr.line, s?s->owner:"-",
		nmestr(leaf->data.sval)); fflush(stdout);
	if (s)
	switch (s->owner_t) {
	case TN_OBJ_DEF: q = "struct/union"; break;
	case TN_FUNC_DEF: q = "fnct"; break;
	}

	fprintf(stdout, "(%s) ", q);
	dflow_mark(stdout, mark);

	if (s && leaf->syment)
	{	find_symbol(leaf->syment->nes, leaf->syment);
		if (s->owner_t == TN_OBJ_DEF)
			printf(" prior use: %d",
				leaf->syment->used);
	}
	fprintf(stdout, "\n");
}

int zero_test(treenode *ex);	/* true if condition ex is a simple comparison against 0 */

typedef struct Cached Cached;
struct Cached {
	char *nm;
	Cached *nxt;
};

static Cached *cst = NULL;

static char *
cache_str(char *s)
{	Cached *c;
	for (c = cst; c; c = c->nxt)
	{	if (strcmp(c->nm, s) == 0)
		{	return c->nm;
	}	}
	c = (Cached *) emalloc(sizeof(Cached));
	c->nm = (char *) emalloc(strlen(s)+1);
	strcpy(c->nm, s);
	c->nxt = cst;
	cst = c;
	return c->nm;
}

static char	*xtable[] = {
	"extern",
	"static",
	"struct",
	NULL
};

static void
track_types(DefUse *d1, leafnode *leaf)		/* Experimental */
{	symentry_t	*se;
	char	*x, *y, *k, *m;
	int	z;

	if (!type_check)
		return;

	if (d1 == NULL
	||  leaf == NULL
	||  leaf->syment == NULL)
	{	return;
	}

	se = leaf->syment;

	if (se == NULL || se->fn[0] == '/')
	{	return;
	}

	if (se->kind == TYPEDEF_ENTRY)
	{	x = se->nme->str;
	} else
	{	x = x_stmnt(se->node);
		for (z = 0; xtable[z] != NULL; z++)
		{	if (strncmp(x, xtable[z], strlen(xtable[z])) == 0)
			{	x += strlen(xtable[z]);
				while (*x == ' ') x++;
		}	}
		y = (char *) 1;
		for (k = x; y != NULL; k = ++y)
		{	y = strstr(k, se->nme->str);
			if (y != NULL)
			{	m = y+strlen(se->nme->str);
				if ((*(y-1) == ' ' || *(y-1) == '\t' || *(y-1) == '*')
				&&  (*m == ';' || *m == ' ' || *m == '\t'
				  || *m == '=' || *m == '(' || *m == ',' || *m == '*'))
				{	*y = '\0';
					break;
				}
			} else
			{
				break;
		}	}
		if (strchr(x, ';') != NULL
		||  strchr(x, '=') != NULL
		||  strchr(x, ',') != NULL)
		{	x = "?";
		}
	}

	if (se->kind != PARAM_ENTRY)
	{	d1->der_type = cache_str(x);
	}

	if (0) printf("%s:%d: [%d] <%s> -- %s (type)\n",
		se->fn, se->ln,
		se->kind,
		se->nme->str,
		x);
}

/* NEW 07/28/09 */

void
check_compound(treenode *p, treenode *n)
{
	if (n
	&&  n->hdr.which == NODE_T
	&&  n->hdr.type == TN_STEMNT) /* instead of TN_BLOCK */
	{
	if (0)	printf("uno: %s:%d: missing compound\n", p->hdr.fnm, p->hdr.line);
	}
}

void
check_else(treenode *p, treenode *n, int depth)	/* check that any if-then-else-if-then chain ends with and else block */
{	if_node *ifn;

	if (Verbose)
	{	if (p)
			printf("%d	B %s:%d -> %d (if=%d) %d\n",
			depth, p->hdr.fnm, p->hdr.line, (n)?n->hdr.which:0, IF_T, (n)?n->hdr.type:0);
		if (n)
			printf("%d	C %s:%d \n", depth, n->hdr.fnm, n->hdr.line);
	}

	if (n)
	{	switch (n->hdr.which) {
		case IF_T:	/* 2	-- if or a cond-expr */
			ifn = (if_node *) n;
			if (ifn->hdr.type == TN_IF)	/* 27 */
			{	if (ifn->else_n == NULL && depth > 0)
				{	printf("uno: %s:%d: missing else\n",
						n->hdr.fnm, n->hdr.line);
				} else
				{	check_else(p, (treenode *) ifn->else_n, depth+1);
				}
			}
			break;
		case NODE_T:	/* 4 */
			if (n->hdr.type == TN_STEMNT	/* 35 */
			||  n->hdr.type == TN_BLOCK)	/* 4 */
			{	check_else(p, n->lnode, depth+1);
				check_else(p, n->rnode, depth+1);
			}
			break;
		default:
			break;
	}	}
}

/* END */

DefUse *
walk_tree(treenode *child, unsigned long markin)
{	leafnode *leaf;
	if_node *ifn;
	for_node *forn;
	unsigned long mark = markin;
	DefUse *d1 = (DefUse *) 0;
	DefUse *d2 = (DefUse *) 0;
	char *u = " ";	/* first bug found by uno 8/9/2001 */
	char *nu;

	if (0 && child)	/* XXX */
	{	printf("%d: walk_tree\t", child->hdr.line);
		printf("%s\t", name_of_nodetype(child->hdr.which));
		printf("%s\t", name_of_node(child->hdr.type));
		dflow_mark(stdout, markin);
		printf("\n");
		fflush(stdout);
	}

	if (child)
	switch (child->hdr.which){
	case LEAF_T:
		leaf = (leafnode *) child;
		if (leaf->hdr.type == TN_IDENT)
		{
			if (0 || (Verbose&2))
				sym_babble(leaf, mark);

			if (leaf->syment)
				leaf->syment->used = 1;

			if (!leaf->syment
			&&  uno_p && mark
			&&  leaf->data.sval)
			{	symentry_t *t;

				t = new_symentry();
				t->nme = leaf->data.sval;
				t->node = child;
				t->ln = child->hdr.line;
				t->fn = child->hdr.fnm;
				t->used = 1;
				leaf->syment = t;
				goto go4it;
			}

			if (!leaf->syment
			||  is_typedef(leaf->syment)
			||  (leaf->syment->nes
			&&   leaf->syment->nes->owner_t == TN_OBJ_DEF	/* struct/union/enum */
			&&  !(mark&FCALL) /* some fcalls are erroneously tagged as OBJ_DEF... */
			))
			{
				if (0 || (Verbose&2))
				{	fprintf(stdout, "--tn_ident - %s -- mark %lu\n",
						nmestr(leaf->data.sval), mark);
					if (!leaf->syment)
						fprintf(stdout, "\tignored (zero syment)\n");
					else if (!leaf->syment->nes)
						fprintf(stdout, "\tignored (zero syment->nes)\n");
					else
						fprintf(stdout, "\tignored (%d==%d)\n",
						leaf->syment->nes->owner_t, TN_OBJ_DEF);
				}
				return (DefUse *) 0; /* defuse info not relevant */
			}
			if (0)
			{
			fprintf(stdout, "--TN_ident - %s -- mark %lu - decl_level %d\t",
			nmestr(leaf->data.sval), mark, leaf->syment->decl_level);
			dflow_mark(stdout, mark);
			printf("\n");
			}

			if (!mark)
			{	if (0) fprintf(stdout, "no mark -- ");
				if (0) fprintf(stdout, "%d:%s\n",
					leaf->hdr.line, nmestr(leaf->data.sval));

				if (Verbose&2) printf("using default mark\n");

				mark |= USE;	/* expr with 1 ident */
			}

			if (mark&(REF0|REF1|REF2))
			{
				if (0) fprintf(stdout, "saw a %s: %s\n",
					(mark&REF1)?"ref1":"ref2", doit(leaf, 0));

				if (mark&(REF1|REF0))	/* lhs of struct reference: ref0->x, ref1.x */
				{	strcat(ref1_pref, doit(leaf, 1));
				} else if (mark&REF2)	/* rhs of struct reference: x->ref2, x.ref2 */
				{	strcat(ref1_pref, doit(leaf, 1));
				}

				if (leaf
				&&  leaf->syment
				&&  leaf->syment->nes
				&&  leaf->syment->nes->owner)
				{	if (leaf->syment->nes->owner[0]  == '-')
						u = set_u(leaf->syment, u);
					else
					{	u = (char *) emalloc(strlen(leaf->syment->nes->owner)
								+strlen(ref1_pref)+2+1);
						strcpy(u, leaf->syment->nes->owner);
					}
				} else
				{	u = (char *) emalloc(1+strlen(ref1_pref)+2+1);
					strcpy(u, "-");
				}
				strcat(u, "::");
				strcat(u, ref1_pref);

				strcpy(ref1_pref, "");
				goto go4it;
			} else
			{	nu = doit(leaf, 0);
				if (nu[0] == '-')
				{	u = set_u(leaf->syment, nu);
				} else
				{	u = (char *) emalloc(strlen(nu)+1);
					strcpy(u, nu);
				}
go4it:
				if (mark & PARAM)
					leaf->syment->kind = PARAM_ENTRY;
				else if (leaf->syment->kind & PARAM_ENTRY)
					mark |= PARAM;

				if (0)	/* XXX */
				{	printf("WT %s:%d\t%s\t",
						child->hdr.fnm,
						child->hdr.line,
						nmestr(leaf->data.sval));
				
					dflow_mark(stdout, mark);
				
					if (leaf->syment)
						printf("\t(owner %s) -- (%s)\n",
							x_stmnt(leaf->syment->container), u);

					printf("	is prototype: %d\n",
						is_a_prototype);
					fflush(stdout);
				}

				d1 = (DefUse *) emalloc(sizeof(DefUse));
				d1->der_type = NULL;
				if (uno_p)
				{	if (mark)
					d1->other = symadd(leaf->syment, mark);
				} else
				{	d1->special = 0;

					if (!(mark&FCALL)
					&&  strncmp(u, "fct", strlen("fct")) != 0)
					{
						if ((mark&USE) && !(mark&ALIAS))
							d1->use   = symadd(leaf->syment, mark);
						if ((mark&DEF) && !(mark&DEREF))
							d1->def   = symadd(leaf->syment, mark);
						if (mark&(DEREF|ALIAS|DECL|ARRAY_DECL))
							d1->other = symadd(leaf->syment, mark);
					}
				}
				if ((mark&(REF1|REF0)) == 0)
					track_types(d1, leaf);
			}

			if (0)
			{	fprintf(stderr, "tn_ident - %s -- mark %lu\t",
					nmestr(leaf->data.sval), mark);
				dump_defuse(d1, stderr);
				fprintf(stderr, "\n");
			}
			if (d1 && d1->other && !exclude_location(child))
			{	SymList *s;
				for (s = d1->other; s; s = s->nxt)
				{	if ((s->mark & (DECL|ARRAY_DECL))
					&& !(s->mark & HIDE)
					&&  has_upper(nmestr(leaf->data.sval)))
					{	location(child);
						printf("variable name '%s' has upper-case\n",
							nmestr(leaf->data.sval));
				}	}
			}

			return d1;
		}
		break;

	case IF_T:
		ifn = (if_node *) child;
		switch (ifn->hdr.type) {
		case TN_IF:
			if (zero_test(ifn->cond))
				d1 = walk_tree(ifn->cond, mark|USE|INCOND);
			else
				d1 = walk_tree(ifn->cond, mark|USE);
			attach_defuse(ifn->cond, "if_cond", d1);	/* was child i.s.o. ifn->cond */
			d2 = walk_tree(ifn->then_n, mark);
			d1 = merge_lists(d1, d2);
			d2 = walk_tree(ifn->else_n, mark);

			if (check_else_chains)
			{	if (Verbose) printf("A %s:%d\n", child->hdr.fnm, child->hdr.line);
				check_else(child, (treenode *) ifn->else_n, 0);
			}
			if (check_compounds)
			{	check_compound(child, (treenode *) ifn->then_n);
				check_compound(child, (treenode *) ifn->else_n);
			}

			break;
		case TN_COND_EXPR:
			if (zero_test(ifn->cond))
				d1 = walk_tree(ifn->cond, mark|USE|INCOND);
			else
				d1 = walk_tree(ifn->cond, mark|USE);
			d2 = walk_tree(ifn->then_n, mark);
			d1 = merge_lists(d1, d2);
			d2 = walk_tree(ifn->else_n, mark);
			/* alas an uninit var in the else branch can be
			   obscured by an assign in the then branch */
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "c_expr", d1);
			return d1;
		default:
			fprintf(stderr, "cannot happen - bad if_t\n");
			exit(1);
		}
		break;

	case FOR_T:	/* either a function or a for-loop */
		RealDecls++;
		forn = (for_node *) child;
		d1 = walk_tree(forn->init, mark);

		if (forn->hdr.type == TN_FUNC_DEF)
		{	is_a_prototype = 0;
			d2 = walk_tree(forn->test, mark);
			is_a_prototype = 1;
		} else
			d2 = walk_tree(forn->test, mark|USE);
		if (forn->hdr.type == TN_FOR)
			attach_defuse(forn->test, "cond", d2);
		d1 = merge_lists(d1, d2);
		d1 = merge_lists(d1, walk_tree(forn->incr, mark));
		d2 = walk_tree(forn->stemnt, mark);	/* body */
		RealDecls--;
		break;

	case NODE_T:
		switch(child->hdr.type){
		case TN_FUNC_DECL:	/* name on lnode, params on rnode */
			if (child->lnode
			&&  child->lnode->hdr.which == LEAF_T
			&&  child->lnode->hdr.type == TN_IDENT)
				Fct_name = nmestr(((leafnode *)(child->lnode))->data.sval);

			if (RealDecls
			&& (strcmp(Fct_name, want) == 0))
			{	if (vis_p)
					set_fbase(child->hdr.line, Fct_name);
				if (0) fprintf(stdout, "%3d: %s\n",
					child->hdr.line, Fct_name);
			}
			if (is_a_prototype)
				d1 = walk_tree(child->rnode, mark|DEF|USE|PARAM);
				/* suppress complaints about disuse */
			else
				d1 = walk_tree(child->rnode, mark|DEF|PARAM);
			attach_defuse(child, "decl1", d1);
			return d1;

		case TN_DECLS:
			d1 = walk_tree(child->lnode, mark|DECL);
			d2 = walk_tree(child->rnode, mark|DECL);
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "decls", d1);
			return d1;

		case TN_DECL:
			if (!child->lnode) break;	/* prototype */
			if (child->lnode->hdr.type == TN_PNTR)
				d1 = walk_tree(child->rnode, mark|IS_PTR|DECL);
			else /* lnode has type information only */
				d1 = walk_tree(child->rnode, mark|DECL);

			attach_defuse(child, "decl2", d1);
			return d1;

		case TN_ARRAY_DECL:
			d1 = walk_tree(child->lnode, mark|ARRAY_DECL);	/* base name */
			d2 = walk_tree(child->rnode, USE);		/* index: size */
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "decl3", d1);
			add_aio(d1, child);
			return d1;

		case TN_SELECT:	/* access of structure element */
			if (child->hdr.tok == ARROW)
			{	d1 = walk_tree(child->lnode, (mark & ~(ALIAS|DEF|DEREF))|REF0);
				strcat(ref1_pref, "->");
			} else
			{	d1 = walk_tree(child->lnode, (mark & ~(ALIAS|DEF|DEREF))|REF1);
				strcat(ref1_pref, ".");
			}
			d2 = walk_tree(child->rnode, mark|REF2);
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "select", d1);
			return d1;

		case TN_CAST:	/* e.g.,: (void) fcall(args); */
			d1 = walk_tree(child->rnode, mark);
if (type_check && d1) d1->der_type = cache_str(x_stmnt(child->lnode));
			attach_defuse(child, "cast", d1);
			return d1;

		case TN_FUNC_CALL:
			storefname(child);
			d1 = walk_tree(child->lnode, mark|FCALL);
			d2 = walk_tree(child->rnode, (mark&~FCALL)|USE);
if (type_check && d2) d2->der_type = NULL;
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "fnct", d1);
			return d1;

		case TN_EXPR:	
			switch (child->hdr.tok) {
			case INCR:
			case DECR:	/* either --x (rnode) or x-- (lnode) */
				/* for structs, only rightmost member gets DEF */

				if (child->rnode
				&&  child->rnode->hdr.type == TN_SELECT)
				{	int xx = (mark & ~ALIAS);
					if (child->rnode->hdr.tok == ARROW)
						d1 = walk_tree(child->rnode->lnode, xx|USE|REF0);
					else
						d1 = walk_tree(child->rnode->lnode, xx|USE|REF1);
					d2 = walk_tree(child->rnode->rnode, mark|USE|DEF|REF2);
					d1 = merge_lists(d1, d2);
					d2 = (DefUse *) 0;
				} else
					d1 = walk_tree(child->rnode, mark|DEF|USE);

				if (child->lnode
				&&  child->lnode->hdr.type == TN_SELECT)
				{	int xx = (mark & ~ALIAS);
					if (child->lnode->hdr.tok == ARROW)
						d1 = walk_tree(child->lnode->lnode, xx|USE|REF0);
					else
						d1 = walk_tree(child->lnode->lnode, xx|USE|REF1);
					d2 = walk_tree(child->lnode->rnode, mark|USE|DEF|REF2);
					d1 = merge_lists(d1, d2);
					d2 = (DefUse *) 0;
				} else
					d2 = walk_tree(child->lnode, mark|DEF|USE);

				d1 = merge_lists(d1, d2);

				attach_defuse(child, "incr", d1);
				return d1;

			case ALIGNOF:
			case SIZEOF:
				d1 = walk_tree(child->rnode, (mark & ~USE)|IN_SIZEOF);
				/* avoid complaints on things like sizeof (*ptr) */
				attach_defuse(child, "sizeof", d1);
				return d1;

			case CASE:
				if (child->lnode)
				{	fprintf(stderr, "%s: unexpected lnode, case\n", progname);
					d1 = walk_tree(child->lnode, mark);
					d2 = walk_tree(child->rnode, mark|USE);
					d1 = merge_lists(d1, d2);
				} else
					d1 = walk_tree(child->rnode, mark|USE);
				attach_defuse(child, "case", d1);
				break;

			case B_AND:
				if (child->lnode == NULL) /* aliasing - takes address of name */
					return walk_tree(child->rnode, mark|ALIAS);

				/* else part of an expression */
				mark |= USE;
				/* fall through */

			default:	/* all other forms of an expression */
				d1 = walk_tree(child->lnode, mark);
				d2 = walk_tree(child->rnode, mark);
if (0) is_final++;
				d1 = merge_lists(d1, d2);
if (0) is_final--;
				attach_defuse(child, "expr", d1);
				return d1;
			}
			break;

		case TN_SWITCH:
		case TN_WHILE:
		case TN_DOWHILE:
			d1 = walk_tree(child->lnode, mark|USE);	/* condition */
			attach_defuse(child->lnode, "cond", d1);
			d2 = walk_tree(child->rnode, mark);
			d1 = merge_lists(d1, d2);
			return d1;

		case TN_ASSIGN:
		{	watch = 0;
sprintf(c_origin, "%s:%4d ", child->hdr.fnm, child->hdr.line);
strcat(c_origin, x_stmnt(child));
track_clr();

			if (watch) printf("A - mark = %lu -- %s\n", mark, x_stmnt(child));

			if (def_and_use(child->hdr.tok))
			{
				if (child->lnode->hdr.type == TN_DEREF)
					d1 = walk_tree(child->lnode, mark|DEREF|USE);
				else
					d1 = walk_tree(child->lnode, mark|DEF|USE);
			} else
			{	int nmark = mark;

				if (watch) printf("B - mark = %d -- %s\n", nmark, x_stmnt(child->lnode));

				if (nmark&USE)
				{	nmark &= ~USE;
					nmark |= USEafterdef;
				}
				if (watch) printf("C - mark = %d -- %s -- lnode=%s\n",
					nmark, x_stmnt(child->lnode),
					name_of_node(child->lnode->hdr.type));

				if (child->lnode->hdr.type == TN_DEREF)
					d1 = walk_tree(child->lnode, nmark|DEREF);
				else
					d1 = walk_tree(child->lnode, nmark|DEF);

				if (watch) { printf("Bd1: "); dump_defuse(d1, stdout); printf("\n"); }
			}
			if (picky
			&&  d1 != NULL
			&&  child->rnode
			&&  child->lnode
			&&  child->rnode->hdr.which == LEAF_T
			&&  child->rnode->hdr.type  == TN_INT
			&&  child->lnode->hdr.which == NODE_T
			&&  child->lnode->hdr.type  == TN_DECL
			&&  ((leafnode *) child->rnode)->data.ival == 0)
			{	SymList *s;
				for (s = d1->other; s; s = s->nxt)
				{	if (s->mark & IS_PTR)
					{	/* printf("%d: 0 ptr init\n", child->rnode->hdr.line); */
						break;
				}	}
				if (s != NULL)
				for (s = d1->other; s; s = s->nxt)	/* remove DEF - not a useful init */
				{	if (s->mark & DEF)
					{	s->mark = (s->mark & ~DEF)|IS_PTR;
			}	}	}

			d2 = walk_tree(child->rnode, (mark&~DECL)|USE);

			if (watch)	{ printf("D1: "); dump_defuse(d1, stdout); printf("\n");
				  printf("D2: "); dump_defuse(d2, stdout); printf("\n");
				}
if (1) is_final++;
			d1 = merge_lists(d2, d1);	/* d1 after d2 */
if (1) is_final--;
			if (watch)	{ printf("D1+D2: "); dump_defuse(d1, stdout); printf("\n"); }

			attach_defuse(child, "asgn", d1);


			if (child->lnode
			&&  child->lnode->hdr.type == TN_ARRAY_DECL
			&&  child->lnode->lnode
			&&  child->lnode->lnode->hdr.type == TN_IDENT
			&&  child->rnode->hdr.type == TN_STRING
			&&  child->lnode->rnode
			&&  child->lnode->rnode->hdr.type == TN_INT)
			{	int xx = ((leafnode *)child->lnode->rnode)->data.ival;	/* simple array bound */
				int yy = strlen(((leafnode *)child->rnode)->data.str);	/* initializing string */
				
				if (yy >= xx)
				printf("uno: %s:%d: array '%s' of %d bytes initialized with %d bytes\n",
					child->hdr.fnm, child->hdr.line,
					((leafnode *)child->lnode->lnode)->data.sval->str,
					xx, yy+1);
			}

			return d1;
		}

		case TN_DEREF:
			d1 = walk_tree(child->lnode, mark|DEREF);
			d2 = walk_tree(child->rnode, mark|DEREF);
			d1 = merge_lists(d1, d2);
			return d1;

		case TN_JUMP:
			if (child->hdr.tok != RETURN)
				goto out;	/* no var refs */
			d1 = walk_tree(child->lnode, mark|USE);
			attach_defuse(child, "return", d1);
			return d1;

		case TN_INDEX:
			d1 = walk_tree(child->lnode, mark | DEREF);	/* indexing an array derefs basename */
			if (strlen(ref1_pref) > 0)
				strcat(ref1_pref, "[");
			d2 = walk_tree(child->rnode, (mark&(~(DEF|ALIAS|DEREF))));
			if (strlen(ref1_pref) > 0)
				strcat(ref1_pref, "]");
if (type_check && d2) d2->der_type = NULL;
			d1 = merge_lists(d1, d2);
			add_aio(d1, child);
			return d1;

		case TN_TRANS_LIST:
			walk_tree(child->lnode, mark);
			walk_tree(child->rnode, mark);
			return (DefUse *) 0;	/* was d1 */

		case TN_TYPE_LIST: /* no defuse info below here */
			return (DefUse *) 0;

		default:
			break;
		}
		d1 = walk_tree(child->lnode, mark);
		d2 = walk_tree(child->rnode, mark);
		break;
	case NONE_T:
		/* suppress parser warning */
		break;
	}
out:
	return merge_lists(d1, d2);
}

void
bugger(char *store, treenode *root, int top)
{	leafnode *leaf;

	if (!root) return;

	switch (root->hdr.which) {
	case LEAF_T:
		leaf = (leafnode *) root;
		switch (leaf->hdr.type) {
		case TN_IDENT:
			strcat(store, leaf->data.sval->str);
			break;
		default:
			goto bad;
		}
		break;
	case NODE_T:
		switch (root->hdr.type) {
		case TN_SELECT:
			bugger(store, root->lnode, 0);
			if (root->hdr.tok == ARROW)
				strcat(store, "->");
			else
				strcat(store, ".");
			bugger(store, root->rnode, 0);
			break;
		case TN_FUNC_CALL:
			bugger(store, root->lnode, 0);
			strcat(store, "()");
			break;
		default:
			goto bad;
		}
		break;
	default:
bad:		strcat(store, "<unknown type>");
		break;
	}

	if (top) strcat(store, "()");
}
