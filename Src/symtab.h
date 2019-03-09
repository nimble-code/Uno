/***** uno: symtab.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/*  Original by Shaun Flisakowski, Jul 12, 1997 */

/*  
    SymTab:  A tree of scope tables,
             one for each scope that declares something, or has a
             child scope that declares something:

         Level
           1              external
                         /        \
           2          file        file 
                      scope       scope 
                                /       \
           3              prototype    function
                            scope        scope
                                        /     \
           4                         block    block
                                     scope    scope    
                                                 \
           5                                     block
                                                 scope    
                                                    \
                                                   (etc.)

    At any particular point you can see all the symbols 
    (variables, types, functions, etc) declared above you in the tree.

    The scope tables are recreated in a lazy fashion, so entering
    and exiting scopes that don't declare new symbols is cheap.
 */
   
#ifndef   SYMTAB_H
#define   SYMTAB_H

#include  "nmetab.h"
#include  "tree.h"

/* kinds of entries in the symbol table. */

/* in the same namespace: */
#define TYPEDEF_ENTRY	(1)	/* type def */
#define FUNCDEF_ENTRY	(2)	/* function def */
#define VARDECL_ENTRY	(3)	/* variable decl */
#define ENUM_ENTRY	(4)	/* enum constants. */

/* in seperate namespaces: */
#define LABEL_ENTRY	(5)	/* label def */
#define TAG_ENTRY	(6)	/* struct/union/enum tags */

/* separate namespace for each struct/union: */
#define COMP_ENTRY	(7)	/* components of struct/union */

#define PARAM_ENTRY	(8)	/* added gjh - set and checked in dflow.c */

#define CURRENT_SCOPE	(0)	/* default */
#define EXTERN_SCOPE	(1)
#define FILE_SCOPE	(2)
#define FUNCTION_SCOPE	(3)
#define BLOCK_SCOPE	(4)	/* really 4 and up */

typedef struct symentry {
	int		kind;	/* TYPEDEF, ENUM, FUNCDEF, VARDECL, PARAM, LABEL, TAG, COMP */
	str_t		*nme;	/* name */
	treenode	*node;	/* ptr to def/decl */

	struct scopetab	*nes;	/* ptr to enclosing scope */
	short		decl_level;	/* added gjh */
	short		used;	/* for struct elements, to see if used */
	int		ln;	/*	linenumber */
	char		*fn;	/*	file name */

	treenode	*container; /* for struct/union component, ptr to def of container */
	struct symentry	*next;
} symentry_t;

symentry_t *mk_typedef(str_t *sym, treenode *);
symentry_t *mk_funcdef(str_t *sym, treenode *);
symentry_t *mk_vardecl(str_t *sym, treenode *);
symentry_t *mk_enum_const(str_t *, treenode *);
symentry_t *mk_label(str_t *, treenode *);
symentry_t *mk_tag(str_t *, treenode *);
symentry_t *mk_component(str_t *, treenode *, treenode *);

int is_typedef(symentry_t *);
int is_funcdef(symentry_t *);
int is_vardecl(symentry_t *);
int is_enum_const(symentry_t *);

#define    INIT_HASHTAB_SIZE    (17)	/* was (5) -- should be prime */

typedef struct hashtab {
    int		tsize;	/* The current size of the table */
    int		nent;	/* The number of entries being stored */
    symentry_t	**tab;	/* The table */
    struct hashtab *nxt; /* for freelist */
} hashtab_t;

hashtab_t  *new_hashtab(void);
symentry_t *hashtab_lookup(hashtab_t *, str_t *);
symentry_t *hashtab_insert(hashtab_t *, symentry_t *);

#define    INIT_CHILD_SIZE     4

typedef struct scopetab {
	int               nsyms;	/* nr of syms declared at this scope. */
	int               level;	/* This scopetab's scoping level. */
	hashtab_t        *htab;		/* hash table - to store the symbols. */
	struct scopetab  *parent;	/* The scope enclosing us, if any. */

	char *owner;			/* name of owner of this scope, functio/file/object */
	int   owner_t;			/* type: TN_OBJ_DEF, TN_FUNC_DEF or NONE_T for Filescope */

	int		  visited;	/* gjh -- facilitate searches */
	int               nchild;
	int               size;
	struct scopetab **children;	/* doubling array of scopes we enclose */
} scopetab_t;

scopetab_t *new_scopetab(scopetab_t *);
symentry_t *scopetab_lookup(scopetab_t *, str_t *);
symentry_t *scopetab_find(scopetab_t *, str_t *);
symentry_t *scopetab_insert(scopetab_t *, symentry_t *);

typedef struct symtab {
	scopetab_t	*root;	/*	The top scopetab - external scope. */
	int		clevel;	/*	The current level. */
	scopetab_t	*current; /*	The current scopetab, or one of its
					ancestors, if it doesn't exist yet. */
	struct symtab	*nxt;	/* for freelist - gh */
} symtab_t;

symtab_t   *new_symtab(void);
symentry_t *symtab_lookup(symtab_t *, str_t *);
symentry_t *symtab_insert(symtab_t *, symentry_t *);
symentry_t *symtab_insert_at(symtab_t *, symentry_t *, int);

int	st_enter_scope(symtab_t *);
void	st_exit_scope(symtab_t *);
void	show_symtab(symtab_t *, FILE *);

typedef struct context {
	symtab_t *labels;	/* Statement labels. */
	symtab_t *tags;		/* Struct/Union/Enum tags. */
	symtab_t *syms;		/* Vars, Types, Functions, etc. */
} context_t;

context_t  *new_context(void);
void  free_context(context_t *);
int   enter_scope(context_t *);
void  exit_scope(context_t *);
void  exit_scopes(context_t *, int);

#endif    /* SYMTAB_H */
