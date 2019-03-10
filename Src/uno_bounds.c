/***** uno: uno_bounds.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#include <stdio.h>
#include <string.h>
#include "symtab.h"
#include "uno_lts.h"
#include "c_gram.h"

static int	debug = 0;

static BoundStack	*boundstack = (BoundStack *) 0;
static BoundStack	*freestack = (BoundStack *) 0;

static ArBound	*bounded = (ArBound *) 0;
static ArBound	*freebounds = (ArBound *) 0;

static ArSize	*arsize = (ArSize *) 0, *freears = (ArSize *) 0;
static ArSize	*arnosize = (ArSize *) 0;

       int	nogood;
static int	size_seen, size_notfound, size_outofscope, size_is_simple, simple_checked, size_other;
static int	size_dunno, size_deref, size_zero, size_zero_resolved, simple_known;
       int	size_ok, size_nok;

extern int	check_bounds(ArBound *, int, treenode *);
extern int	infeasible(treenode *, treenode *);
extern int	merge_bounds(ArBound *, ArBound *);
extern int	same_bounds(ArBound *, ArBound *);
extern int	uno_ignore(symentry_t *);
extern void	negate_bound(ArBound *);
extern void	uno_assert(int, char *);
extern int	eval_fct(treenode *, treenode *);
extern void	print_recur(treenode *, FILE *);
extern void	dump_defuse(DefUse *, FILE *);
extern int	suppress(char *, int);
extern char	*toksym(int, int);
extern int	unsatisfiable(ArBound *);
extern int	get_state_val(void);

extern char	*statename;
extern State	*uno_prop;

void explain_bound(char *, ArBound *, treenode *);

extern int	Verbose, depth, uno;

extern void	could_be_fct(char *);

static int
count_leafs(treenode *n)
{
	if (!n) return 0;

	if (n->hdr.which == LEAF_T)
	{	if (n->hdr.type == TN_IDENT)
			could_be_fct(((leafnode*)n)->data.sval->str);
		return 1;
	}

	return count_leafs(n->lnode)+count_leafs(n->rnode);
}

static int
has_right_decl(symentry_t *s, treenode *n)
{
	if (n->hdr.type == TN_ARRAY_DECL
	&&  n->lnode->hdr.type == TN_IDENT
	&&  ((leafnode *)(n->lnode))->syment == s)
		return 1;
	if (n->hdr.type == TN_DECL
	&&  n->lnode->hdr.type == TN_PNTR
	&&  has_right_decl(s, n->rnode))
		return 1;
	return 0;
}

static int
find_ininode(symentry_t *s, treenode *n)
{
	/* find a TN_ASSIGN with lnode equal to b
	   and rnode TN_INIT_BLK
	 */
	if (!n || n->hdr.which == LEAF_T)
		return 0;

	if (n->hdr.type == TN_ASSIGN
	&&  n->rnode->hdr.type == TN_INIT_BLK
	&&  has_right_decl(s, n->lnode))
		return count_leafs(n->rnode);

	return find_ininode(s, n->lnode) + find_ininode(s, n->rnode);
}

static ArSize *
getars(void)
{	ArSize *a;

	if (freears)
	{	a = freears;
		freears = freears->nxt;
		memset(a, 0, sizeof(ArSize));
	} else
		a = (ArSize *) emalloc(sizeof(ArSize));

	return a;
}

static void
add_size(symentry_t *s, treenode *b, treenode *n)
{	ArSize *a;
	int cnt;
	leafnode *q;

	for (a = arsize; a; a = a->nxt)
		if (a->s == s)
			return;

	if (!b)
	{	if ((cnt = find_ininode(s, n)) != 0)
		{	size_zero_resolved++;
			if (Verbose || debug > 1)
			printf("uno:	bound for array %s\tresolved: %d\n",
				s->nme->str, cnt);
			q = (leafnode *) emalloc(sizeof(leafnode));
			q->hdr.which = LEAF_T;
			q->hdr.type = TN_INT;
			q->data.ival = cnt;
			b = (treenode *) q;
		} else
		{	size_zero++;
			if (Verbose || debug > 1)
			printf("uno:	bound for array %s\tnot resolved\n", s->nme->str);
			return;
		}
	}

	if (Verbose>1) 
	printf("uno: %s:%d have array bound for %s\n",
		n->hdr.fnm,
		n->hdr.line,
		s->nme->str);

	a = getars();
	a->s = s;
	a->b = b;
	a->nxt = arsize;
	arsize = a;
}

static treenode *
find_size(symentry_t *s, treenode *nn)
{	ArSize *a, *r = (ArSize *) 0;
	int cnt = 0;

	if (!s) return ZT;

	for (a = arsize; a; a = a->nxt)
	{	if (a->s == s)
			return a->b;
		else
		if (strcmp(a->s->nme->str, s->nme->str) == 0
		&&       a->s->decl_level == s->decl_level)
		{	cnt++;
			r = a;
#if 0
			printf("same name %s, different symbol:\n", s->nme->str);
			printf("	level %d %d\n",
				a->s->decl_level,
				s->decl_level);
			printf("	line %d %d\n", a->s->ln, s->ln);
			printf("	scopetab %u %u\n", a->s->nes, s->nes);
			printf("	tree %u %u\n", a->s->node, s->node);
			printf("	tree ln %u %u\n",
				a->s->node->hdr.line, s->node->hdr.line);
#endif
		}
	}
	if (cnt == 1) return r->b;	/* uno can't tell that r is initialized here */

	for (a = arnosize; a; a = a->nxt)
		if (strcmp(a->s->nme->str, s->nme->str) == 0)
			break;	/* somehow the symentry's may differ */

	if (!a)
	{	a = getars();
		a->s = s;
		a->nxt = arnosize;
		arnosize = a;
		/* avoid reporting more than once */
		if (Verbose)
		printf("uno: %s:%d could not determine array bound for %s\n",
			nn->hdr.fnm,
			nn->hdr.line,
			s->nme->str);
		size_other++;
	}
	return ZT;
}

int
has_node_comp_ops(treenode *n)
{
	if (!n)
		return 0;

	if (n->hdr.type == (unsigned int) TN_EXPR)
	{	switch (n->hdr.tok) {
		case NOT:
		case EQUAL:
		case LESS:
		case LESS_EQ:
		case GRTR:
		case GRTR_EQ:
		case NOT_EQ:
		case AND:
		case OR:
		case B_NOT_EQ:	return 1;

		default:	return 0;
	}	}

	if (n->hdr.type == TN_EMPTY
	||  n->hdr.which == LEAF_T
	||  n->hdr.type == TN_IDENT)
	{	return 0;
	}

	return (has_node_comp_ops(n->lnode)
	||	has_node_comp_ops(n->rnode));
}

int
has_node_type(treenode *n, int t)
{
	if (!n)
		return 0;

	if (n->hdr.type == (unsigned int) t)
		return 1;

	if (n->hdr.which == LEAF_T)
		return 0;

	return (has_node_type(n->lnode, t)
	||	has_node_type(n->rnode, t));
}

static symentry_t *
simple_node_type(treenode *n)
{
	if (n && n->hdr.type == TN_IDENT)
		return n->syment;

	return (symentry_t *) 0;

}

int
eval_const_expr(treenode *n, treenode *m)
{	int a=0, b=0;

	if (!n) return 0;

	if (n->hdr.type == TN_INT)
		return ((leafnode *)n)->data.ival;

	if (n->hdr.type == TN_IDENT)
	{	if (strcmp(((leafnode *)n)->data.sval->str, statename) == 0)
			return get_state_val();
	}

	if (uno_prop
	&&  n->hdr.type == TN_FUNC_CALL)
	{
		return eval_fct(n, m);
	}

	if (n->hdr.type == TN_EXPR)
	{
		if (n->lnode)
			a = eval_const_expr(n->lnode, m);
		if (n->rnode)
			b = eval_const_expr(n->rnode, m);

		if (!nogood)
		switch (n->hdr.tok) {
		case NOT:	return !b;
		case B_NOT:	return ~b;
		case CASE:	return b;

		case PLUS:	return a+b;
		case MINUS:	return a-b;
		case STAR:	return a*b;
		case DIV:	if (b == 0)
				{	fprintf(stderr, "uno: %s:%d division by zero error\n",
						n->hdr.fnm, n->hdr.line);
					break;
				}
				return a/b;
		case MOD:	if (b == 0)
				{	fprintf(stderr, "uno: %s:%d division by zero error\n",
						n->hdr.fnm, n->hdr.line);
					break;
				}
				return a%b;

		case EQUAL:	return (a == b);
		case LESS:	return (a < b);
		case LESS_EQ:	return (a <= b);
		case GRTR:	return (a > b);
		case GRTR_EQ:	return (a >= b);
		case NOT_EQ:	return (a != b);

		case AND:	return (a && b);
		case OR:	return (a || b);
		case B_OR:	return (a | b);
		case B_AND:	return (a & b);
		case B_XOR:	return (a ^ b);
		case B_NOT_EQ:	return (a != b);
		case L_SHIFT:	return (a << b);
		case R_SHIFT:	return (a >> b);

		default:
				printf("saw token type: %s (%s)\n",
					(char *) toksym(n->hdr.tok,0),
					x_stmnt(n));
				break;
		}
	}
	nogood = 1;
	return 0;
}

static int
eval_cond(treenode *a, treenode *b)	/* is a < b ? */
{	int ix, bnd;
	nogood = 0;

	ix  = eval_const_expr(a, ZT);

	if (ix < 0) return 0;		/* definitely wrong */

	bnd = eval_const_expr(b, ZT);

	if (nogood) return -2;		/* can't tell */

	if (ix == bnd) return -1;	/* equal to bound */

	return (ix < bnd);	/* satisfied */
}

static Stack *v_reps = (Stack *) 0;

int
v_matched(treenode *n)
{	Stack *w;

	for (w = v_reps; w; w = w->nxt)
		if (n == w->n)
			return 1;

	if (suppress(n->hdr.fnm, n->hdr.line))
		return 1;

	return 0;
}

int
v_reported(treenode *n)
{	Stack *w;

	if (v_matched(n))
		return 1;

	w = (Stack *) emalloc(sizeof(Stack));
	w->n = n;
	w->nxt = v_reps;
	v_reps = w;
	return 0;
}

static void
ana_aio_ix(State *s, treenode *tn)
{	treenode	*nn = s->n;
	treenode	*n;
	symentry_t	*v;
	ArBound		*b;
	int		x = -2;

	if (tn->lnode->hdr.type != TN_IDENT	/* basename is not simple */
	||  tn->hdr.type != TN_INDEX)		/* decls are handled elsewhere */
		return;

	if (debug>1)
	{	printf("uno: ana_aio for %s\t(stmnt %s)\tbase:",
			tn->lnode->syment->nme->str, x_stmnt(nn));
		print_recur(tn->lnode, stdout);
		printf("\tindex: ");
		print_recur(tn->rnode, stdout);
		printf("\n");
	}

	size_seen++;
	if (has_node_type(tn->rnode, (int) TN_DEREF))
	{	if (debug>1) printf("	cannot handle\n");
		size_deref++;
		return;
	}

	if (!(n = find_size(tn->lnode->syment, nn)))	/* assign */
	{	if (debug>1) printf("	no bound\n");
		size_notfound++;
		return;
	}

	if (has_node_type(tn->rnode, (int) TN_IDENT))
	{	if (!(v = simple_node_type(tn->rnode)))	/* assignment */
		{	if (debug>1) printf("	not simple\n");
			size_outofscope++;
		} else
		{	size_is_simple++;
			if (debug>1) printf("	simple\n");

			nogood = 0;
			x = eval_const_expr(n, ZT);
			if (nogood)
			{	if (debug>1)
				printf("\tsimple bound, but no simple size\n");
				size_outofscope++;
			} else
			{	simple_checked++;

				if (debug>1)
				{	printf("\tsimple bound for %s\t(stmnt %s)\tbase:",
						tn->lnode->syment->nme->str, x_stmnt(nn));
					print_recur(tn->lnode, stdout);
					printf("\tindex: ");
					print_recur(tn->rnode, stdout);
					printf("\n");
					if (!boundstack->curbounds)
						printf("	no known bounds\n");
				}

				for (b = boundstack->curbounds; b; b = b->nxt)
				{	if (debug>1) explain_bound("Known:", b, nn);
					if (b->s == v && !(b->bounds & UNK))
					{	/* the value of v has to be >= 0 and <= x */
						simple_known++;	/* should equal simple_checked */
						check_bounds(b, x, nn);
						break;
					}
				}
				if (debug>1)
				{	if (!b)
					{	printf("simple check for %s, but no known bound\n", v->nme->str);
						for (b = boundstack->curbounds; b; b = b->nxt)
							explain_bound("knew:", b, nn);
				}	}
			}
		}
	} else
	{	char *p = "";
		x = eval_cond(tn->rnode, n);
		if (x == 1)	/* satisfied */
		{	if (debug>1) printf("	satisfied.\n");
			size_ok++;
			return;
		}
		if (x == -1)	/* equal to bound */
		{	/* likely used to find end of array */
			p ="possible ";
			x = 0;
		}
		if (x == 0)	/* not satisfied */
		{	if (!v_reported(tn))
			{	fprintf(stdout, "uno: %s:%4d %sarray indexing error '%s",
					tn->hdr.fnm,
					tn->hdr.line, p,
					x_stmnt(tn->lnode));
				fprintf(stdout, "[%s]'", x_stmnt(tn->rnode));
				fprintf(stdout, " (array-size: %s)\n", x_stmnt(n));
				size_nok++;
			}
			return;
		} /* else cannot tell */

		if (debug>1) printf("	cannot tell (x=%d)\n", x);

		size_dunno++;
	} /* else cannot tell */
	if (debug>1)
	{	printf("uno: %s:%4d bound-check %s",
			tn->hdr.fnm,
			tn->hdr.line,
			x_stmnt(tn->lnode));
		printf("[ %s", x_stmnt(tn->rnode));
		printf(" < %s ? ]\n", x_stmnt(n));	/* within bound? */
	}
}

static void
ana_aio_decl(SymList *s, treenode *tn, treenode *nn)
{
	if (!tn) return;

	if (tn->hdr.type == TN_DECL
	&&  tn->rnode
	&&  tn->lnode
	&&  tn->lnode->hdr.type == TN_PNTR)
	{	ana_aio_decl(s, tn->rnode, nn);
		return;
	}

	if (tn->hdr.type == TN_ARRAY_DECL
	&&  tn->lnode->hdr.type == TN_IDENT	/* the index: the array size */
	&&  tn->lnode->syment == s->sm)
	{	add_size(s->sm, tn->rnode, nn);
		if (debug>1)
		{	printf("uno: set bound ana_aio for %s\n",
				s->sm->nme->str);
			printf("uno: %s:%d basename %s",
				tn->hdr.fnm,
				tn->hdr.line,
				x_stmnt(tn->lnode));
			printf("[ %s ]\t",
				x_stmnt(tn->rnode));
			printf("=====%s\n\t", name_of_node(nn->hdr.type));
			print_recur(nn, stdout);
			printf("\n");
	}	}
}

static ArBound *
uno_freshbound(void)
{	ArBound *b;

	if (freebounds)
	{	b = freebounds;
		freebounds = freebounds->nxt;
		b->sameas = (symentry_t *) 0;
		b->dup = (ArBound *) 0;
		b->nxt = (ArBound *) 0;
	} else
		b = (ArBound *) emalloc(sizeof(ArBound));

	b->level_set = depth;
	return b;
}

static ArBound *
loose_bound(symentry_t *s, int lb, int ub, int bounds)
{	ArBound *b;

	uno_assert((s != NULL), "saw bound without name");

	b = uno_freshbound();
	b->s = s;
	b->ub = ub;
	b->lb = lb;
	b->bounds = bounds;
	return b;
}

static ArBound *
add_bound(symentry_t *s, int lb, int ub, int bounds)
{	ArBound *b;

	if (!s) return (ArBound *) 0;	/* probably undeclared var such as 'errno' */

	for (b = bounded; b; b = b->nxt)	/* record best guess at values of vars */
		if (b->s == s && !(b->bounds & UNK))
		{	if (bounds & FROMASGN)	/* new bound is definitive */
			{	if (debug>1)
				printf("	old bound on %s removed\n",
					s->nme->str);
				b->bounds |= UNK;	/* continue, there may be more */
			} else if (b->bounds & FROMASGN)	/* and bounds&FORMEXPR */
			{	if (debug>1)
				printf("	ignore new non-asgn bound on %s\n",
					s->nme->str);	/* new bound was not from asgn */
				return (ArBound *) 0;	/* already have a definitive value */
		}	}

	b = loose_bound(s, lb, ub, bounds);	/* this can add multiple FROMEXPR bounds on a var */

	b->nxt = bounded;
	bounded = b;
	return b;
}

static ArBound *
bound_from_asgn(symentry_t *s, treenode *nn)
{	ArBound *b = (ArBound *) 0;
	int n;

	if (!nn
	||  !nn->lnode
	||   nn->lnode->hdr.type != TN_IDENT
	||  (nn->lnode->syment != s && s))
		return b;

	if (nn->rnode->hdr.type == TN_IDENT)
	{	/* see if we have a bound on this ident already
		 * if so, copy the bounds over to the lnode var
		 */
		if (s != nn->rnode->syment)
		{	b = add_bound(nn->lnode->syment, 0, 0, DUP|FROMASGN);
			b->sameas = nn->rnode->syment;
			/* b->dup set later in fix_dups */
		}
	} else
	{	nogood = 0;
		n = eval_const_expr(nn->rnode, ZT);
		if (!nogood)
			b = add_bound(nn->lnode->syment, n, n+1, (LB|UB|FROMASGN));
	}

	if (debug && b) printf("UU: set bound from asignment\n");
	return b;
}

static ArBound *
uno_dig(symentry_t *s, treenode *n)
{	ArBound *b = (ArBound *) 0;

	switch (n->hdr.type) {
	case TN_ASSIGN:
		b = bound_from_asgn(s, n);
		break;
	case TN_DECL:
	case TN_DECLS:
		b = uno_dig(s, n->lnode);
		if (!b)
		b = uno_dig(s, n->rnode);
		/* fall thru */
	default:
		break;
	}
	return b;
}

static void
dual_work(State *z)
{	SymList *s;
	leafnode *l;
	ArBound *b;
	treenode *n;

	if (!z) return;

	n = z->n;

	if (!n || !n->hdr.defuse)
		return;

	l = leftmost(n);
	if (l && l->hdr.tok == EXTRN)
		return;	

	for (s = n->hdr.defuse->other; s; s = s->nxt)
	{
		if ((s->sm->decl_level >= FUNCTION_SCOPE)	/* local */
		&&  (s->mark & DECL)				/* declaration */
		&&  (s->mark & DEF)				/* with initializer */
		&& !(s->mark & ARRAY_DECL)			/* not array decl */
		&& !uno_ignore(s->sm)				/* not from /usr/include */
		&& !(s->mark & REF2))				/* not compound x->ref2 or x.ref2 */
		{	b = uno_dig(s->sm, n);			/* try to derive initial bounds on var */
			if (debug>1)
			explain_bound("newbound", b, n);
	}	}
}

static ArSize *
uno_freears(ArSize *a)
{
	if (a)
	{	uno_freears(a->nxt);
		a->nxt = freears;
		freears = a;
	}
	return (ArSize *) 0;
}

static ArBound *
uno_dumpbounds(ArBound *b)
{
	if (b)
	{	uno_dumpbounds(b->nxt);
		b->nxt = freebounds;
		freebounds = b;
	}
	return (ArBound *) 0;
}

static ArBound *
bound_from_expr(treenode *nn)
{	ArBound *b = (ArBound *) 0;
	symentry_t *s;
	int n;

	if (!nn
	||  !nn->lnode
	||   nn->lnode->hdr.type != TN_IDENT)
		return (ArBound *) 0;

	nogood = 0;
	n = eval_const_expr(nn->rnode, ZT);
	if (nogood)
		return (ArBound *) 0;

	s = nn->lnode->syment;

	switch (nn->hdr.tok) {
	case EQUAL:
		b = add_bound(s, n, n+1, LB|UB|FROMEXPR);
		break;
	case NOT_EQ:
		b = add_bound(s, n, n+1, LB|UB|NEG|FROMEXPR);
		break;
	case LESS:
		b = add_bound(s, 0, n, UB|FROMEXPR);
		break;
	case LESS_EQ:
		b = add_bound(s, 0, n+1, UB|FROMEXPR);
		break;
	case GRTR:
		b = add_bound(s, n+1, 0, LB|FROMEXPR);
		break;
	case GRTR_EQ:
		b = add_bound(s, n, 0, LB|FROMEXPR);
		break;
	}

	return b;
}

void
explain_bound(char *m, ArBound *b, treenode *n)
{
	if (!b) return;

	if (0)
	{	printf("{");
		if (b->bounds & UNK) printf("U");
		if (b->bounds & DUP) printf("(%s:%s)",
			b->s->nme->str,
			b->sameas->nme->str);
		if (b->bounds & NEG) printf("!");
		if ((b->bounds & LB)
		&&  (b->bounds & UB)
		&&  (b->lb == b->ub-1))
			printf("(%s==%d)", b->s->nme->str, b->lb);
		else
		{	if (b->bounds & LB)  printf("(%s>=%d)", b->s->nme->str, b->lb);
			if (b->bounds & UB)  printf("(%s<%d)",  b->s->nme->str, b->ub);
		}
		if (b->bounds & FROMASGN) printf("a");
		if (b->bounds & FROMEXPR) printf("e");
		printf("}");
		return;
	}

	printf("\tuno: %s:%d (%s) %s bound on %s:",
		n?n->hdr.fnm:"",
		n?n->hdr.line:0,
		m,
		n?x_stmnt(n):"",
		b->s->nme->str);

	if (b->bounds & UNK)
		printf(" <unknown>");
	if (b->bounds & NEG)
		printf("<negated>");
	if (b->bounds & DUP)
		printf(" <duplicate of %s>", b->sameas?b->sameas->nme->str:"?");
	else
	{	switch (b->bounds & (LB|UB)) {
		case UB:
			printf("UB < %d", b->ub);
			break;
		case LB:
			printf("LB >= %d", b->lb);
			break;
		case (LB|UB):
			printf(">= %d and < %d", b->lb, b->ub);
			break;
		}
	}
	if (b->bounds & FROMASGN)
		printf(" (from asgn)");
	if (b->bounds & FROMEXPR)
		printf(" (from expr)");

	printf(" set at level %d", b->level_set);
	printf("\n");
}

static void
expr_bound(treenode *n, treenode *v)		/* try to derive bounds on scalars from cond */
{	ArBound *b = (ArBound *) 0;
	char *s;

	if (!n || !v) return;	/* branch conditions only */

	if (n && n->hdr.type == TN_EXPR)
		b = bound_from_expr(n);
	if (!b) return;

	if (v->hdr.tok == IDENT)
	{	s = ((leafnode *)v)->data.sval->str;

		if (strcmp(s, "_false_") == 0)
		{	if (debug>1)
			printf("	negating bound\n");

			negate_bound(b);
		} else if (strcmp(s,  "_true_") != 0)
			goto not_yet;
	} else
	{	/* remove bound b from bounded */
not_yet:
		if (debug>1)
		{	printf("uno: complex condition, removing last derived bound\n");
			explain_bound("expr_bound", b, n);
		}
		uno_assert((int) (b == bounded), "exprbound error");
		bounded = bounded->nxt;

		b->nxt = freebounds;
		freebounds = b;
		return;
	}

	if (debug>1)
	explain_bound("expr_bound", b, n);
}

static void
asgn_bound(State *s)		/* try to derive bounds on scalars from asgn */
{	ArBound *b = (ArBound *) 0;
	treenode *n;

	if (!s) return;
	n = s->n;

	if (n
	&&  n->hdr.type == TN_ASSIGN
	&&  n->hdr.tok == EQ)
		b = bound_from_asgn((symentry_t *)0, n);

	if (debug>1)
	explain_bound("asgn_bound", b, n);
}

static void
gather_bounds(State *z)
{	ArBound *a, *b;
	SymList *s;
	treenode *e;
	int hit;

	if (!z) return;

	if (debug>1)
	{	if (z->n && z->n->hdr.defuse)
		{	printf("	defuse on last step: ");
			dump_defuse(z->n->hdr.defuse, stdout);
			printf("\n");
		}
		for (b = bounded; b; b = b->nxt)
			explain_bound("gather", b, z->n);
	}

	if (z->n && z->n->hdr.type == TN_IF)
		e = ((if_node *)z->n)->cond;
	else
		e = z->n;

	if (e && e->hdr.defuse)
	for (s = e->hdr.defuse->other; s; s = s->nxt)
	{	if (!(s->mark & DEF))	/* set, so must have added bound FROMASGN or INCR... */
			continue;
if (debug)
printf("UU: saw def on %s\n", s->sm->nme->str);

		for (b = bounded; b; b = b->nxt)
		{
if (debug)
printf("UU:	check with bound on %s %d,%d [%d] (set at level %d)\n",
	b->s->nme->str,
	b->lb, b->ub, b->bounds,
	b->level_set);
			if (strcmp(b->s->nme->str, s->sm->nme->str) == 0
#if 1
			&&  b->level_set < depth
#else
			&& (b->bounds & FROMEXPR)
#endif
			)
				b->bounds |= UNK;	/* no longer valid */
		}
		for (b = boundstack->curbounds; b; b = b->nxt)
		{
if (debug)
printf("UU:	previous bound on %s %d,%d [%d] (set at level %d)\n",
	b->s->nme->str,
	b->lb, b->ub, b->bounds,
	b->level_set);
			if (strcmp(b->s->nme->str, s->sm->nme->str) == 0)
			{
if (debug)
printf("UU:	now expired\n");
				b->bounds |= UNK;	/* all previous bounds expire */
			}
		}
	}

	for (b = bounded; b; b = b->nxt)	/* save bounds on stack */
	{	hit = 0;
		if ((b->bounds & FROMASGN)
		||  (b->bounds & UNK))
		{	for (a = boundstack->curbounds; a; a = a->nxt)
				if (a->s == b->s)
					a->bounds |= UNK;	/* remove */
		} else	/* FROMEXPR */
		{	for (a = boundstack->curbounds; a; a = a->nxt)
				if (a->s == b->s)
				{	merge_bounds(a, b);	/* rewrites a as (a/\b) */
					hit = 1;
		}		}

		if (!hit)
		{	a = loose_bound(b->s, b->lb, b->ub, b->bounds);	/* add new bound */
			a->sameas = b->sameas;				/* even if UNK */
			a->dup = b->dup;
			a->nxt = boundstack->curbounds;
			a->level_set = b->level_set;
			boundstack->curbounds = a;

			if (debug>1)
			explain_bound("attach", b, e);
		}
	}

	uno_dumpbounds(bounded);	/* forget all bounds for next step */
	bounded = (ArBound *) 0;
}

void
bound_stats(void)
{
	if (!Verbose) return;

	if (size_zero_resolved)
	printf("%4d\tstatic initializers resolved\n", size_zero_resolved);

	if (size_zero)
	printf("%4d\tarrays declared without size\n", size_zero);

	if (size_seen)
	printf("%4d\tarray indices seen\n", size_seen);

	if (size_notfound)
	printf("%4d\tcould not determine array bound (%d distinct vars)\n",
		size_notfound, size_other);

	if (size_deref)
	printf("%4d\tptr derefs in index (not handled yet)\n", size_deref);

	if (size_outofscope)
	printf("%4d\tnon-checked indices (out of scope)\n", size_outofscope);

	if (size_dunno)
	printf("%4d\tarray indices could not be evaluated\n", size_dunno);

	if (simple_checked > simple_known)
	printf("%4d\tarray indices had no known bound\n", simple_checked-simple_known);

	if (size_ok + size_nok)
	printf("%4d\tarray indices checked (%d violations reported)\n",
			size_ok + size_nok, size_nok);

	if (size_is_simple + simple_checked)
	printf("%4d\tsimple indices - %d of which could be and %d were checked)\n",
		size_is_simple, simple_checked, simple_known);

	if (simple_checked > simple_known)
	printf("	(%d had no known bound)\n", simple_checked-simple_known);
}

void
uno_bounds(SymList *s, ArList *d, treenode *n)
{	ArList *a;

	for (a = d; a; a = a->nxt)
		ana_aio_decl(s, a->tn, n);
}

void
uno_index(State *s)
{	ArList *a;
	treenode *e;

	if (!s) return;

	if (s->n && s->n->hdr.type == TN_IF)
		e = ((if_node *)s->n)->cond;
	else
		e = s->n;

	if (e && e->hdr.defuse)
	for (a = e->hdr.defuse->aio; a; a = a->nxt)		/* index operations */
		ana_aio_ix(s, a->tn);
}

static void
fix_dups(State *s)
{	ArBound *a, *b;
	int cnt = 0;

	for (a = boundstack->curbounds; a; a = a->nxt)
		if (a->bounds & DUP)
		{	a->dup = (ArBound *) 0;
			if (a->s == a->sameas)
			{	if (Verbose)
				{	printf("uno: warning: reflexive dup\n");
					explain_bound("target:", a, s->n);
				}
				a->bounds &= ~DUP;
				a->sameas = (symentry_t *) 0;
			}
			cnt = 0;
again:
			for (b = boundstack->curbounds; b; b = b->nxt)
			{	if (b == a) continue;

				if (b->s == a->sameas)
				{	if (debug>1)
					{	printf("\tdup on '%s' picked up from stack\n",
						a->s->nme->str);
						explain_bound("from", b, ZT);
					}

					if (b->bounds & UNK)
					{	a->bounds |= UNK;
						a->bounds &= ~DUP;
						a->sameas = (symentry_t *) 0;
						break;
					}

					if (!(b->bounds & DUP))
						a->dup = b;
					else
					{	if (b->s == b->sameas)
						{	printf("uno: warning: reflextive dup target\n");
							explain_bound("target:", b, ZT);
							b->bounds &= ~DUP;
							b->sameas = (symentry_t *) 0;
							a->dup = b;
						} else
						{	a->sameas = b->sameas;
							if (cnt++ <= 10)
								goto again;
							printf("dup cycle\n");
							explain_bound("member:", a, s->n);
							a->bounds |= UNK;
							a->bounds &= ~DUP;
							a->sameas = (symentry_t *) 0;
							a->dup = (ArBound *) 0;
					}	}
					break;
				}
			}
			if (!b)
			{	if (debug>1)
				printf("\tcould not find dup for %s on stack\n",
					a->s->nme->str);
				a->bounds |= UNK;
				a->bounds &= ~DUP;
				a->sameas = (symentry_t *) 0;
				a->dup = (ArBound *) 0;
			}
		}
}

static BoundStack *
uno_bframe(void)
{	BoundStack *f;

	if (freestack)
	{	f = freestack;
		freestack = freestack->nxt;
		f->nxt = (BoundStack *) 0;
	} else
		f = (BoundStack *) emalloc(sizeof(BoundStack));
	return f;
}

static int
bound_push(State *s, treenode *exp_in, treenode *t_cond, State *prev_s)
{	ArBound	*a, *b;
	BoundStack *f;
	int any_updates;

	f = uno_bframe();
	f->curbounds = (ArBound *) 0;

	if (boundstack)		/* carry known bounds forward onto new stackframe */
	for (b = boundstack->curbounds; b; b = b->nxt)
	{	if (b->bounds&UNK)
			continue;
		if (debug>1) explain_bound("imprt", b, ZT);

		a = loose_bound(b->s, b->lb, b->ub, b->bounds);
		a->sameas = b->sameas;
		a->dup = b->dup;
		a->nxt = f->curbounds;
		a->level_set = b->level_set;
		f->curbounds = a;
	}

	f->nxt = boundstack;
	boundstack = f;

	/* pick up new bounds from the immediately preceding step that brought us here */
	dual_work(prev_s);		/* possible initializers in decls */
	expr_bound(exp_in, t_cond);	/* possible bound from branch cond */
	asgn_bound(prev_s);		/* possible bound from asgn */
	gather_bounds(prev_s);		/* reconcile the bounds */

	any_updates = 0;
	fix_dups(s);

	for (b = boundstack->curbounds; b; b = b->nxt)
	{
#if 0
		/* bound could have been known before */
		if (b->bounds & UNK)
			continue;
#endif
		if (debug>1) explain_bound("stack", b, ZT);

		if (unsatisfiable(b))	/* something became unsatisfiable at this step */
		{	if (debug) explain_bound("unsatisfiable", b, s->n);
			return 3;	/* don't update state - no run can get here */
		}

		for (a = s->pvb; a; a = a->nxt)	/* previously seen bounds at this step */
			if (same_bounds(a, b))
				break;

		if (!a)
		{	any_updates = 1;
			a = loose_bound(b->s, b->lb, b->ub, b->bounds);
			a->sameas = b->sameas;
			a->dup = b->dup;
			a->nxt = s->pvb;
			a->level_set = b->level_set;
			s->pvb = a;
	}	}

	if (debug>1)
	{	for (b = s->pvb; b; b = b->nxt)
			explain_bound("pvb", b, s->n);
	}

	if (!any_updates)		/* bounds stored @ state are unchanged */
	{	if (s->visited)
			return 2;	/* old state */
		s->visited = 1;
		return 1;		/* new state */
	}
	s->visited = 1;
	return 0;			/* revisit state */
}

static void
bound_pop(void)
{	BoundStack *f;

	uno_assert((boundstack != NULL), "boundstack pop error");
	uno_dumpbounds(boundstack->curbounds);	/* recycle */

	f = boundstack;
	boundstack = boundstack->nxt;		/* pop */

	f->nxt = freestack;			/* recycle */
	freestack = f;
}

void
bound_reset(void)
{
	bounded = uno_dumpbounds(bounded);
	arsize = uno_freears(arsize);
	arnosize = uno_freears(arnosize);
	v_reps = (Stack *) 0;
}

int
dfs_bound(State *s, treenode *exp_in, treenode *t_cond, State *prev_s)
{	Trans *t;
	treenode *exp;
	int result = 1;

	if (!s) return result;

	depth++;
	if (debug)
	{	printf("%3d: dfs_bound %s:%d <%s>\n",
			depth,
			s->n->hdr.fnm,
			s->n->hdr.line,
			x_stmnt(exp_in));
	}

	switch (bound_push(s, exp_in, t_cond, prev_s)) {
	case 3:	/* unsatisfiable bound */
		result = 0;
		goto done;
	case 2:	
		if (debug) printf("\told state\n");
		goto done;
	case 1:
		if (debug) printf("\tnew state\n");
		break;
	case 0:
		if (debug) printf("\trevisit state\n");
		break;
	}

	uno_index(s);	/* attempt to find out of bound array indices */

	if (s->iscond && s->n)
	{	if (s->n->hdr.type == TN_IF)
			exp = ((if_node *)s->n)->cond;
		else
			exp = s->n;
	} else
		exp = ZT;

	for (t = s->succ; t && t->branch; t = t->nxt)
		if (!infeasible(exp, t->cond))	/* e.g. 0 == _true_ */
			dfs_bound(t->branch, exp, t->cond, s);

done:	bound_pop();

	if (debug)
		printf("%3d: dfs_bound up\n", depth);
	depth--;

	return result;
}
