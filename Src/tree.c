/***** uno: tree.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shaun Flisakowski, Jan 21, 1995 */
/* Revisions by Kurt Cockrum */
/* Extensions and revisions for Uno by Gerard Holzmann */

#include    "globals.h"
#include    "tree.h"
#include    "c_gram.h"
#include    "prnttree.h"

extern void	efree(void *);
extern char	*progname;
extern Stk_Item *Parse_TOS;	/* uno_local.c */

char*
print_ptr(void *ptr)
{	static char buf[32];

	sprintf(buf, "%p", ptr);

	return buf;
}

if_node *
make_if(tn_t type)
{
    if_node *tmp_node;

    tmp_node = (if_node *) HeapAlloc(Parse_TOS->node_heap);
    if (tmp_node == NULL)
    {
        fputs("Error: Out of memory in make_if.\n",stderr);
        exit(1);
    }

    tmp_node->hdr.which = IF_T;
    tmp_node->hdr.type  = type;
    tmp_node->hdr.defuse = 0;
    tmp_node->cond  = (treenode *) NULL;
    tmp_node->then_n = (treenode *) NULL;
    tmp_node->else_n = (treenode *) NULL;
    return tmp_node;
}

for_node *
make_for(tn_t type)
{
    for_node *tmp_node;

    tmp_node = (for_node *) HeapAlloc(Parse_TOS->node_heap);

    if (tmp_node == NULL)
    {
        fputs("Error: Out of memory in make_for.\n",stderr);
        exit(1);
    }

    tmp_node->hdr.which = FOR_T;
    tmp_node->hdr.type = type;
    tmp_node->hdr.defuse = 0;
    tmp_node->init = (treenode *) NULL;
    tmp_node->test = (treenode *) NULL;
    tmp_node->incr = (treenode *) NULL;
    tmp_node->stemnt = (treenode *) NULL;
    return tmp_node;
}

leafnode *
make_leaf(tn_t type)
{
    leafnode *tmp_node;

    tmp_node = (leafnode *) HeapAlloc(Parse_TOS->node_heap);

    if (tmp_node == NULL)
    {
        fputs("Error: Out of memory in make_leaf.\n",stderr);
        exit(1);
    }

    tmp_node->hdr.which = LEAF_T;
    tmp_node->hdr.type = type;
    tmp_node->hdr.defuse = 0;

    tmp_node->syment = (symentry_t *) NULL;
    return tmp_node;
}

treenode *
make_node(tn_t type)
{
    treenode *tmp_node;

    tmp_node = (treenode *) HeapAlloc(Parse_TOS->node_heap);

    if (tmp_node == NULL)
    {
        fputs("Error: Out of memory in make_node.\n",stderr);
        exit(1);
    }

    tmp_node->hdr.which = NODE_T;
    tmp_node->hdr.type  = type;
    tmp_node->hdr.defuse = 0;
    tmp_node->hdr.fnm = Parse_TOS->filename;
    tmp_node->hdr.line = Parse_TOS->yylineno;

    tmp_node->lnode = (treenode *) NULL;
    tmp_node->rnode = (treenode *) NULL;
    tmp_node->syment = (symentry_t *) NULL;

    return tmp_node;
}

void
free_tree(treenode *root)
{
    leafnode *leaf;
    if_node  *ifn;
    for_node *forn;

    if (!root)
        return;

    switch (root->hdr.which){

    case LEAF_T:
        leaf = (leafnode *) root;
        if (leaf->hdr.tok == STRING)
           efree(leaf->data.str);
        break;

    case NODE_T:
        free_tree(root->lnode);
        free_tree(root->rnode);
        break;

    case IF_T:
        ifn = (if_node *) root;
        free_tree(ifn->cond);
        free_tree(ifn->then_n);
        free_tree(ifn->else_n);
        break;

    case FOR_T:
        forn = (for_node *) root;
        free_tree(forn->init);
        free_tree(forn->test);
        free_tree(forn->incr);
        free_tree(forn->stemnt);
        break;

    default:
    case NONE_T:
        break;
    }

    HeapFree(Parse_TOS->node_heap,root);
}

leafnode *
leftmost(treenode *root)
{
    if_node *ifn;
    for_node *forn;

	if (!root) return (leafnode *) 0;

    switch (root->hdr.which){

    case LEAF_T:
        return((leafnode *) root);

    case NODE_T:
        if (root->lnode)
            return(leftmost(root->lnode));
        else if (root->rnode)
            return(leftmost(root->rnode));
        fprintf(stderr,
            "Tree node %s with no children reached in leftmost.\n",
                print_ptr(root));
        break;

    case IF_T:
        ifn = (if_node *) root;
        if (ifn->cond)
            return(leftmost(ifn->cond));
        else if (ifn->then_n)
            return(leftmost(ifn->then_n));
        else if (ifn->else_n)
            return(leftmost(ifn->else_n));
        fprintf(stderr,
            "If-node %s with no children reached in leftmost.\n",
                print_ptr(root));
        break;

    case FOR_T:
        forn = (for_node *) root;
        if (forn->init)
            return(leftmost(forn->init));
        else if (forn->test)
            return(leftmost(forn->test));
        else if (forn->incr)
            return(leftmost(forn->incr));
        else if (forn->stemnt)
            return(leftmost(forn->stemnt));
        fprintf(stderr,
            "For-node %s with no children reached in leftmost.\n",
                print_ptr(root));
        break;

    case NONE_T:
	break;

    default:
        fprintf(stderr, "%s: parse error: unknown node %s in leftmost; "
         "  type: %s\n", progname, print_ptr(root), name_of_nodetype(root->hdr.which));
        break;
    }

    return((leafnode *) NULL);
}

/* Scans typedef declaration node n for the ident naming the new type. --jsh */

void
find_typedef_name(treenode *n, treenode *def, FindFunction find)
{
    if (!n)
        return;

    if (0)
	printf("%s: find_typedef_name %s - %s\n",
		progname, name_of_nodetype(n->hdr.which), name_of_node(n->hdr.type));

    switch(n->hdr.which) {
        case LEAF_T:
            (find)((leafnode*) n, def, NULL);
            break;

        case NODE_T:
        {
            switch(n->hdr.type) {
            case TN_DECL:
                find_typedef_name(n->rnode,def,find);
                break;

            case TN_ARRAY_DECL:
                find_typedef_name(n->lnode,def,find);
                break;

            case TN_PNTR:
#if 0
                fprintf(stderr,
                    "%s: parse error: TN_PNTR reached in find_typedef_name\n", progname);
		/* can happen, e.g.: typedef long name(int *); */
#endif
                break;

            case TN_DECL_LIST:
            case TN_DECLS:
                find_typedef_name(n->lnode,def,find);
                find_typedef_name(n->rnode,def,find);
                break;

            case TN_FUNC_DECL:

		if (0) printf("lnode=%s %s rnode=%s %s\n",
		name_of_nodetype(n->lnode->hdr.which), name_of_node(n->lnode->hdr.type),
		name_of_nodetype(n->rnode->hdr.which), name_of_node(n->rnode->hdr.type));

		if (n->lnode->hdr.which == LEAF_T)		/* gjh added */
			find_typedef_name(n->lnode,def,find);
		else if (n->lnode->hdr.type == TN_DECL)
                    find_typedef_name(n->lnode,def,find);
                else
                    find_typedef_name(n->rnode,def,find);
                break;

	    case TN_PARAM_LIST:
		return;

            default:
                fprintf(stderr,
                        "%s: parse error: "
                        "unknown node type (%s) in find_typedef_name\n",
                        progname, name_of_node(n->hdr.type));
                break;
            }
        }
        break;

        case IF_T:
        case FOR_T:
        case NONE_T:
        default:
            fprintf(stderr,
                "%s: parse error: unknown node %s in find_typedef_name;"
                "  type: %s\n", progname, print_ptr(n), name_of_nodetype(n->hdr.which));
            break;
    }
}

void
find_ident_name(treenode *n, treenode *def, treenode *container, FindFunction find)
{
    if (!n)
        return;

    switch(n->hdr.which) {
    case LEAF_T:
        (find)((leafnode*) n,def,container);
        break;

    case NODE_T:
    {
        switch(n->hdr.type) {
        case TN_IDENT:
            (find)((leafnode*) n,def,container);
            break;

        case TN_DECL:
            find_ident_name(n->rnode,def,container,find);
            break;

        case TN_COMP_DECL:
            find_ident_name(n->rnode,def,container,find);
            break;

        case TN_ASSIGN:
        case TN_ARRAY_DECL:
            find_ident_name(n->lnode,def,container,find);
            break;

        case TN_FIELD_LIST:
        case TN_DECL_LIST:
        case TN_DECLS:
        case TN_PARAM_LIST:
	case TN_IDENT_LIST:
            find_ident_name(n->lnode,def,container,find);
            find_ident_name(n->rnode,def,container,find);
            break;

        case TN_ELLIPSIS:
            break;

        case TN_PNTR:
            break;

        case TN_FUNC_DECL:
            find_ident_name(n->lnode,def,container,find);
            break;

	case TN_BIT_FIELD:	/* added gjh */
		break;

        default:
            fprintf(stderr,
                    "%s: parse error:%d: "
                    "unknown node type (%s) in find_ident_name\n",
                    progname, n->hdr.line, name_of_node(n->hdr.type));
            break;
        }
    }
    break;

    case IF_T:
    case FOR_T:
    case NONE_T:
    default:
        fprintf(stderr,
            "%s: parse error:%d: unknown node in find_ident_name: %s\n",
            progname, n->hdr.line, name_of_nodetype(n->hdr.which));
        break;
    }
}

/* Scan fct decl node n for identifier naming the new function. */

leafnode *
find_func_name(treenode *n)
{
	while (n && (n->hdr.which != LEAF_T))
	{	switch(n->hdr.which) {
		case NODE_T:
			switch(n->hdr.type) {
			case TN_DECL:
				n = n->rnode;
				break;
			case TN_FUNC_DECL:
				n = n->lnode;
				break;
			case TN_ARRAY_DECL:
				fprintf(stderr,
					"%s: error: unexpected node in find_func_name;\n"
					"\tnode: %s, type: %s (%s:%d)\n", progname,
						name_of_nodetype(n->hdr.which),
						name_of_node(n->hdr.type),
						n->hdr.fnm, n->hdr.line);
				n = n->rnode;	/* 1/4/10: a guess */
				break;
			default:
				goto bad;
			}
			break;
		case FOR_T:
			if (n->hdr.type == TN_FUNC_DEF)
				n = ((for_node *) n)->test;
			break;
		default:
bad:			fprintf(stderr,
				"%s: error: bad node in find_func_name;\n"
				"	node: %s, type: %s\n",
				progname, name_of_nodetype(n->hdr.which),
				name_of_node(n->hdr.type));
			n = NULL;
			break;
	}	}

	return (leafnode*) n;
}

void
find_params(treenode *decl, FindFunction find)
{
	if (!decl)
		return;

	switch(decl->hdr.which) {
	case NODE_T:
	        switch(decl->hdr.type) {
		case TN_DECL:
			if (decl->rnode
			&&  decl->rnode->hdr.which == NODE_T
			&&  decl->rnode->hdr.type == TN_FUNC_DECL)
				find_params(decl->rnode, find);
			else
				find_ident_name(decl,decl,NULL,find);
			break;
	
		case TN_DECL_LIST:
		case TN_DECLS:
			find_params(decl->lnode,find);
			find_params(decl->rnode,find);
			break;

		case TN_IDENT_LIST:
		case TN_PARAM_LIST:
			find_ident_name(decl->lnode,decl->lnode,NULL,find);
			find_ident_name(decl->rnode,decl->rnode,NULL,find);
			break;
	
		case TN_FUNC_DECL:
			find_params(decl->rnode,find);
			break;
	
		default:
			fprintf(stderr, "%s: parse error:%d: "
				"unknown node type (%s) in find_params\n",
				progname, decl->hdr.line,
				name_of_node(decl->hdr.type));
			break;
		}
		break;

	case LEAF_T:
		if (0) {	leafnode *leaf = (leafnode *) decl;
			switch (leaf->hdr.type) {
			case TN_IDENT:
				printf("	%s\n", leaf->data.sval->str);
				break;
			default:
				printf("	<leaftype: %d>\n", (int) leaf->hdr.type);
				break;
			}
		}
		find_ident_name(decl,decl,NULL,find);
		break;

	case IF_T:
	case FOR_T:
	case NONE_T:
	default:
		fprintf(stderr, "%s: parse error:%d: unknown node in find_params,"
			"  type: %s\n", progname, decl->hdr.line,
			name_of_nodetype(decl->hdr.which));
		break;
	}
}

void
find_components(treenode *decl, treenode *def,
                treenode *container, FindFunction find)
{
    if (!decl)
        return;

    switch(decl->hdr.which)
    {
        case NODE_T:
        {
            switch(decl->hdr.type)
            {
            case TN_COMP_DECL:
            case TN_DECL:
                find_ident_name(decl,decl,container,find);
                break;

            case TN_DECL_LIST:
            case TN_DECLS:
                find_components(decl->lnode,def,container,find);
                find_components(decl->rnode,def,container,find);
                break;

            case TN_FIELD_LIST:
                find_components(decl->lnode,def,container,find);
                find_components(decl->rnode,def,container,find);
                break;

            case TN_FUNC_DECL:
                find_components(decl->rnode,def,container,find);
                break;

            default:
                fprintf(stderr,
                    "%s: parse error: "
                    "unknown node type (%s) in find_components\n",
                    progname, name_of_node(decl->hdr.type));
                break;
            }
        }
    break;

    case LEAF_T:
    case IF_T:
    case FOR_T:
    case NONE_T:
    default:
        fprintf(stderr,
         "%s: parse error: unknown node %s in find_components;\n"
         "  type is: %s\n", progname, print_ptr(decl), name_of_nodetype(decl->hdr.which));
        break;
    }
}

#define    SHOW(X)    #X

char*
name_of_node(tn_t val)
{
    switch (val)
    {
    case TN_EMPTY:
        return SHOW(TN_EMPTY);

    case TN_FUNC_DEF:
        return SHOW(TN_FUNC_DEF);
    case TN_FUNC_DECL:
        return SHOW(TN_FUNC_DECL);
    case TN_FUNC_CALL:
        return SHOW(TN_FUNC_CALL);
    case TN_BLOCK:
        return SHOW(TN_BLOCK);
    case TN_DECL:
        return SHOW(TN_DECL);
    case TN_ARRAY_DECL:
        return SHOW(TN_ARRAY_DECL);

    case TN_TRANS_LIST:
        return SHOW(TN_TRANS_LIST);
    case TN_DECL_LIST:
        return SHOW(TN_DECL_LIST);
    case TN_DECLS:
        return SHOW(TN_DECLS);
    case TN_STEMNT_LIST:
        return SHOW(TN_STEMNT_LIST);
    case TN_EXPR_LIST:
        return SHOW(TN_EXPR_LIST);
    case TN_NAME_LIST:
        return SHOW(TN_NAME_LIST);
    case TN_ENUM_LIST:
        return SHOW(TN_ENUM_LIST);
    case TN_FIELD_LIST:
        return SHOW(TN_FIELD_LIST);
    case TN_PARAM_LIST:
        return SHOW(TN_PARAM_LIST);
    case TN_IDENT_LIST:
        return SHOW(TN_IDENT_LIST);

    case TN_COMP_DECL:
        return SHOW(TN_COMP_DECL);
    case TN_BIT_FIELD:
        return SHOW(TN_BIT_FIELD);
    case TN_PNTR:
        return SHOW(TN_PNTR);

    case TN_TYPE_LIST:
        return SHOW(TN_TYPE_LIST);
    case TN_TYPE_NME:
        return SHOW(TN_TYPE_NME);

    case TN_INIT_LIST:
        return SHOW(TN_INIT_LIST);
    case TN_INIT_BLK:
        return SHOW(TN_INIT_BLK);

    case TN_OBJ_DEF:
        return SHOW(TN_OBJ_DEF);
    case TN_OBJ_REF:
        return SHOW(TN_OBJ_REF);

    case TN_CAST:
        return SHOW(TN_CAST);
    case TN_IF:
        return SHOW(TN_IF);
    case TN_ASSIGN:
        return SHOW(TN_ASSIGN);
    case TN_JUMP:
        return SHOW(TN_JUMP);
    case TN_FOR:
        return SHOW(TN_FOR);
    case TN_WHILE:
        return SHOW(TN_WHILE);
    case TN_DOWHILE:
        return SHOW(TN_DOWHILE);
    case TN_SWITCH:
        return SHOW(TN_SWITCH);
    case TN_LABEL:
        return SHOW(TN_LABEL);
    case TN_STEMNT:
        return SHOW(TN_STEMNT);

    case TN_INDEX:
        return SHOW(TN_INDEX);
    case TN_DEREF:
        return SHOW(TN_DEREF);
    case TN_SELECT:
        return SHOW(TN_SELECT);

    case TN_EXPR:
        return SHOW(TN_EXPR);
    case TN_COND_EXPR:
        return SHOW(TN_COND_EXPR);

    case TN_COMMENT:
        return SHOW(TN_COMMENT);
    case TN_CPP:
        return SHOW(TN_CPP);

    case TN_ELLIPSIS:
        return SHOW(TN_ELLIPSIS);
    case TN_IDENT:
        return SHOW(TN_IDENT);
    case TN_TYPE:
        return SHOW(TN_TYPE);
    case TN_STRING:
        return SHOW(TN_STRING);

    case TN_INT:
        return SHOW(TN_INT);

    case TN_REAL:
        return SHOW(TN_REAL);

    default:
        return "<Unknown Node Name>";
    }
}

char*
name_of_nodetype(node_type val)
{
    switch (val)
    {
    case NONE_T:
        return SHOW(NONE_T);
    case LEAF_T:
        return SHOW(LEAF_T);
    case IF_T:
        return SHOW(IF_T);
    case FOR_T:
        return SHOW(FOR_T);
    case NODE_T:
        return SHOW(NODE_T);
    default:
        return "<Unknown Node Type>";
    }
}
#undef SHOW
