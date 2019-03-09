/***** uno: tree.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/*  Original version by Shawn Flisakowski, Jan 21, 1995 */

#ifndef   TREE_H
#define   TREE_H

#include  "nmetab.h"
#include  "dflow.h"

typedef enum {
	TN_EMPTY,
	TN_FUNC_DEF,
	TN_FUNC_DECL,
	TN_FUNC_CALL,
	TN_BLOCK,
	TN_DECL,
	TN_ARRAY_DECL,
	TN_TRANS_LIST,
	TN_DECL_LIST,
	TN_STEMNT_LIST,
		TN_EXPR_LIST,	/* 10 */
	TN_NAME_LIST,
	TN_ENUM_LIST,
	TN_FIELD_LIST,
	TN_PARAM_LIST,
	TN_IDENT_LIST,
	TN_DECLS,
	    /* Dumb, but I'm not sure what to do yet */
	TN_COMP_DECL,
	TN_BIT_FIELD,
	TN_PNTR,
	        /* Stores a list of type specifiers/qualifers (int,const,etc) */
		TN_TYPE_LIST,	/* 20 */
	TN_TYPE_NME,
	        /* Stores initial values for arrays */
	TN_INIT_LIST,
	TN_INIT_BLK,

	TN_OBJ_DEF,    /* Definition of struct, union, or enum */
	TN_OBJ_REF,    /* Reference to struct, union, or enum */

	    /* More vague */
	TN_CAST,
	TN_IF,
	TN_ASSIGN,
	TN_JUMP,
		TN_FOR,		/* 30 */
	TN_WHILE,
	TN_DOWHILE,
	TN_SWITCH,
	TN_LABEL,
	TN_STEMNT,

	TN_INDEX,     /* Index with [] */
	TN_ADDROF,    /* Address of via & */
	TN_DEREF,     /* Dereference with * */
	TN_SELECT,    /* -> and . */

		TN_EXPR,	/* 40 */
	TN_COND_EXPR,

	TN_COMMENT,
	TN_CPP,

	TN_ELLIPSIS,
	TN_IDENT,
	TN_TYPE,
	TN_STRING,
	TN_INT,
	TN_REAL			/* 49 */
} tn_t;

typedef enum { NONE_T, LEAF_T, IF_T, FOR_T, NODE_T } node_type;

typedef struct Nuts Nuts;
struct Nuts {
	char	*nut;
	Nuts	*nxt;
};

struct common {
	node_type which;
	char	*fnm;
	int	line;
	int	col;
	int	tok;
	tn_t	type;

	Nuts	*nuts;		/* gjh - annotations for global analysis */
	DefUse	*defuse;	/* gjh - dataflow information */
	int	warned;		/* gjh - set if a warning for this node was already issued */
#if 0
	char	udefined;	/* gjh - remembers if this was a user-defined typedef name */
				/* but, can use is_typedef() instead */
#endif
#ifdef DEFTYP
	char	*deftyp;	/* gjh - debugging */
#endif
};

typedef struct treenode {
	struct common	hdr;
	struct symentry *syment;	/* labelname */

	struct treenode *lnode;
	struct treenode *rnode;

} treenode;

typedef struct if_node {
	struct common    hdr;
	struct symentry    *syment;

	struct treenode *cond;
	struct treenode *then_n;
	struct treenode *else_n;
} if_node;

typedef struct for_node {
	struct common    hdr;
	struct symentry    *syment;

	struct treenode *init;
	struct treenode *test;
	struct treenode *incr;
	struct treenode *stemnt;
} for_node;

typedef struct leafnode {
	struct common       hdr;
	struct symentry    *syment;	/* node in symbol table */

	union {
	  int               cval;
	  str_t            *sval;
	  char             *str;
	  int               ival;
	  double            dval;
	} data;
} leafnode;

typedef  void (*FindFunction)(leafnode*, treenode*, treenode*);

char	*name_of_node(tn_t);
char	*name_of_nodetype(node_type);

leafnode	*make_leaf(tn_t);
if_node		*make_if(tn_t);
for_node	*make_for(tn_t);

treenode	*make_node(tn_t);
treenode	*copy_tree(treenode *);

leafnode 	*leftmost(treenode *);
leafnode 	*rightmost(treenode *);
leafnode 	*find_func_name(treenode *);

void	free_tree(treenode *);
void	find_typedef_name(treenode *, treenode *, FindFunction);
void	find_ident_name(treenode *, treenode *, treenode *, FindFunction);
void	find_params(treenode *, FindFunction);
void	find_components(treenode *, treenode *, treenode *, FindFunction);

#endif    /* TREE_H */
