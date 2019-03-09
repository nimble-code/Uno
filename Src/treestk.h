/***** uno: treestk.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shawn Flisakowski, Apr 7, 1995 */

#ifndef TREE_STK_H
#define TREE_STK_H

#include <stdio.h>
#include "heap.h"
#include "tree.h"
#include "symtab.h"

#define    YYBUFF_SIZE    4096

/*  Redefinition - original provided by flex/lex */
#ifndef    YY_BUFFER_STATE_DEFD
typedef  struct yy_buffer_state  *YY_BUFFER_STATE;
#endif

#define    MX_NODE_1      max(sizeof(leafnode), sizeof(treenode))
#define    MX_NODE_2      max(sizeof(if_node), sizeof(for_node))
#define    MX_NODE_SZE    max( MX_NODE_1 , MX_NODE_2 )

typedef  struct stk_item {

    treenode          *parse_tree;  /* Pointer to the parse tree */
    Heap              *node_heap;   /* Allocated tree nodes */

    char              *filename;    /* The name of the file */
    FILE              *yyin;        /* A pointer to an open file */

    int                yylineno;    /* Line number */
    int                yycolno;     /* Column number */
    int                yynxtcol;    /* next Column number */

    YY_BUFFER_STATE    yybuff;      /* A buffer for the lexer */

    struct stk_item   *next;        /* Ptr to next item in the stack */

} Stk_Item;

#define    STK_ITEM_SZE    (sizeof(Stk_Item))

typedef struct treestk {

    Stk_Item    *top;
    Stk_Item    *bottom;

    context_t   *contxt;

} TreeStack;

#define    TREESTK_SZE    (sizeof(TreeStack))

TreeStack	*new_treestk(void);

Stk_Item	*new_stk_item(FILE *, char *);
Stk_Item	*pop(TreeStack *);
Stk_Item	*top_of_stack(TreeStack *);
void	delete_stk_item(Stk_Item *);
void	push(TreeStack *, Stk_Item *);
void	reset_position(TreeStack *);
void	handle_new_file(TreeStack *, FILE *, char *);
int	is_empty(TreeStack *);
int	tree_parse(TreeStack *, int);
int	get_next_file(TreeStack *);

FILE	*top_file(TreeStack *);
char	*top_filename(TreeStack *);

#ifdef    DEBUG 
void show_stack(TreeStack *);
#endif

#endif    /* TREE_STK_H  */
