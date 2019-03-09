/***** uno: treestk.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shaun Flisakowski, Apr 7, 1995 */

#include "globals.h"

extern FILE     *yyin;
extern int	yyparse(void);
extern YY_BUFFER_STATE yy_create_buffer( FILE *file, int size );
extern void	yy_switch_to_buffer( YY_BUFFER_STATE buff );
extern void	yy_delete_buffer( YY_BUFFER_STATE buff );
extern void	*emalloc(size_t);
extern void	efree(void *);

extern TreeStack *DoneStack;	/* uno_local.c */
extern Stk_Item *Parse_TOS;	/* uno_local.c */

static Stk_Item *freestk = (Stk_Item *) 0;

Stk_Item  *
new_stk_item( FILE *fp, char *fname )
{
    Stk_Item *stk_item;

	if (freestk)
	{	stk_item = freestk;
		freestk = freestk->next;
		memset(stk_item, 0, STK_ITEM_SZE);
	} else
		stk_item = emalloc(STK_ITEM_SZE);

    stk_item->filename = emalloc(strlen(fname)+1);
    strcpy(stk_item->filename, fname);

    if ((stk_item->yybuff = yy_create_buffer(fp, YYBUFF_SIZE )) == NULL){
        efree(stk_item->filename);
        efree(stk_item);
        return((Stk_Item *) NULL);
    }

    if ((stk_item->node_heap  = CreateHeap(MX_NODE_SZE, 0)) == NULL){
        efree(stk_item->filename);
        yy_delete_buffer( stk_item->yybuff );
        efree(stk_item);
        return((Stk_Item *) NULL);
    }

    stk_item->yyin     = fp;

    stk_item->yylineno = 1;
    stk_item->yycolno  = 0;
    stk_item->yynxtcol = 0;

    stk_item->parse_tree = (treenode *) NULL;

    stk_item->next = (Stk_Item *) NULL;

    return(stk_item);
}

void
delete_stk_item(Stk_Item *stk_item)
{
	if (!stk_item)
		return;
#ifdef PC
	if (stk_item->yybuff)
		yy_delete_buffer(stk_item->yybuff);
#endif
	if (stk_item->node_heap)
	{	DestroyHeap(stk_item->node_heap);
		memset(stk_item, 0, sizeof(Stk_Item));
	}

	stk_item->next = freestk;
	freestk = stk_item;
}

TreeStack *
new_treestk(void)
{	TreeStack *treestk;

	treestk = (TreeStack *) emalloc(sizeof(TreeStack));
	treestk->top    = NULL;
	treestk->bottom = NULL;

	treestk->contxt = NULL;
	return treestk;
}

void
push(TreeStack *treestk, Stk_Item *stk_item )
{
    if (! treestk || ! stk_item)
        return;

    stk_item->next = treestk->top;

    if (! treestk->top)
        treestk->bottom = stk_item;

    treestk->top = stk_item;
}

Stk_Item *
pop(TreeStack *treestk)
{
    Stk_Item *stk_item, *nxt_item;

    if (is_empty(treestk))
        return((Stk_Item *) NULL);

    stk_item = treestk->top;
    nxt_item = treestk->top->next;

    if (! nxt_item)
        treestk->bottom = (Stk_Item *) NULL;

    treestk->top = nxt_item;

    return(stk_item);
}

int
is_empty(TreeStack *treestk)
{
	if (!treestk)
		return(1);

	return(treestk->top == NULL);
}

Stk_Item *
top_of_stack(TreeStack *treestk)
{
    if (is_empty(treestk))
        return((Stk_Item *) NULL);
    else
        return(treestk->top);
}

FILE *
top_file(TreeStack *treestk)
{
    if (is_empty(treestk))
        return((FILE *) NULL);
    else
        return(treestk->top->yyin);
}

void
reset_position(TreeStack *treestk)
{
    if ( !(Parse_TOS = top_of_stack(treestk)))
        return;

    yy_switch_to_buffer(Parse_TOS->yybuff);
    yyin = top_file(treestk);
}

int
tree_parse(TreeStack *treestk, int parse_all)
{
    int cnt = 0;

    if (is_empty(treestk))
        return(0);

    do {
	yyparse();	/* returns 1 on error 0 on accept */
        cnt++;
        get_next_file(treestk);

        if (is_empty(treestk))
            break;

    } while (parse_all);

    return(cnt);
}

void
handle_new_file(TreeStack *treestk, FILE *fp, char *fname)
{
    Stk_Item *stk_item;

    if ((stk_item = new_stk_item(fp, fname)) == NULL)
        return;

    push(treestk, stk_item);
    reset_position(treestk);
}

int
get_next_file(TreeStack *treestk)
{
    if (is_empty(treestk)){
        Parse_TOS = (Stk_Item *) NULL;
        return(0);
    }

    if (DoneStack)
        push(DoneStack, pop(treestk));
    else {
        fputs("DoneStack was NULL.\n", stdout);
        delete_stk_item(pop(treestk));
    }

    reset_position(treestk);

    if (is_empty(treestk))
        return(0);

    return(1);
}

#ifdef DEBUG
void
show_stack(TreeStack *treestk)
{
    Stk_Item *tmp;

    fputs("-----Showing Stack: \n",stderr);
    if (treestk && treestk->top){

        fputs("Starting at top (current item being Parsed).\n",stderr);
        for (tmp=treestk->top; tmp; tmp=tmp->next){
            if (tmp->filename)
                fprintf(stderr, "%s:\t", tmp->filename);
            else
                fputs("--no name--:\t", stderr);
            fprintf(stderr, "Line: %d  Column: %d\n", tmp->yylineno, 
                    tmp->yycolno );
        }

    } else
        fputs("Stack is Empty.\n",stderr);

    fputs("-----Done Showing Stack \n",stderr);
}
#endif
