/***** uno: explore.c *****/

#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include "prnttree.h"
#include "c_gram.h"
#include "symtab.h"

#define BufLimit	64000

static int	decl_cnt = 0;
static int	enum_list_cnt = 0;

static char	IBuf[BufLimit];
static char	*Xbuf = IBuf;

extern int	Verbose, xrepro;
extern void	clean_tmps(void);

extern void	fput_meta(int c, int in_str);
extern void	fput_meta2(char *str);
extern void	location(treenode *);

static int nest;
static char *fnm;	/* set  to filename */

static void walker(treenode *, int, int);	/* query engine */

static void
explore_tree(treenode *root, int level)
{	if_node  *ifn;
	for_node *forn;
	leafnode *leaf;

	if (!root) return;

	nest++;

	assert(Xbuf != NULL);

	if (strlen(Xbuf) > BufLimit-10)
	{	if (0) { puts(Xbuf); fflush(stdout); }
		fprintf(stderr, "uno: error: %s:%d overflow - buffer limit is %d bytes\n",
			root->hdr.fnm, root->hdr.line, BufLimit);
		if (1)
		{	strcpy(Xbuf, ""); /* attempt to continue */
		} else
		{	clean_tmps();
			exit(1);
	}	}

	if (0)
	{	printf("%s:%4d:\t", root->hdr.fnm, root->hdr.line);
		printf("[%d:%d:%d]\t", strlen(Xbuf), level, nest);
		printf("%s\t", name_of_nodetype(root->hdr.which));
		printf("%s\t", name_of_node(root->hdr.type));
		if (root->hdr.type == TN_IDENT) printf("%s", ((leafnode *)root)->data.sval->str);
		printf("\n");
		fflush(stdout);
	}

	walker(root, level, 1);

    switch (root->hdr.which) {
    default:
    case NONE_T:
        fprintf(stderr, "uno: error: Node with no type\n");
	goto done;

    case LEAF_T:
        leaf = (leafnode *) root;
        switch (leaf->hdr.type) {

        case TN_LABEL:
            if (leaf->hdr.tok == DEFLT)
              strcat(Xbuf, "default");
            else
              strcat(Xbuf, leaf->data.sval->str);
            strcat(Xbuf, ":");
            break;

        case TN_IDENT:
            strcat(Xbuf, leaf->data.sval->str);
            break;

        case TN_COMMENT:
            strcat(Xbuf, "/* ");
            strcat(Xbuf, leaf->data.str);
            strcat(Xbuf, " */");
            break;

        case TN_ELLIPSIS:
            strcat(Xbuf, "...");
            break;

        case TN_STRING:
            strcat(Xbuf, "\"");
            fput_meta2(leaf->data.str);
            strcat(Xbuf, "\"");
            break;

        case TN_TYPE:
		if (leaf->hdr.tok != TYPEDEF_NAME)
		{	strcat(Xbuf, toksym(leaf->hdr.tok,1));
		} else
		{	strcat(Xbuf, leaf->data.sval->str);
			strcat(Xbuf, " ");
		}
		break;

        case TN_INT:
            if (leaf->hdr.tok == CHAR_CONST)
	    { strcat(Xbuf, "'");
              fput_meta(leaf->data.ival, 0);
              strcat(Xbuf, "'");
            } else
            { char nr[64];
	      sprintf(nr, "%d", leaf->data.ival);
	      strcat(Xbuf, nr);
	    }
            break;

        case TN_REAL:
            { char nr[64];
              sprintf(nr, "%f", leaf->data.dval);
	      strcat(Xbuf, nr);
	    }
            break;

        default:
            fprintf(stderr, "uno: Unknown leaf value %d\n",
		(int) leaf->hdr.type);

	case TN_INIT_BLK:
            break;
        }
        break;

    case IF_T:
        ifn = (if_node *) root;
        switch (ifn->hdr.type) {

        case TN_IF:
            strcat(Xbuf, "if (");
            explore_tree(ifn->cond, level);
            strcat(Xbuf, ") ");
            explore_tree(ifn->then_n, level+1);	/* could add braces here if needed */
            if (ifn->else_n) {
                strcat(Xbuf, ";");
                strcat(Xbuf, "else ");
                explore_tree(ifn->else_n, level+1);
            }
            break;

        case TN_COND_EXPR:
            strcat(Xbuf, "(");
            explore_tree(ifn->cond, level);
            strcat(Xbuf, ") ? (");
            explore_tree(ifn->then_n, level);
            strcat(Xbuf, ") : (");
            explore_tree(ifn->else_n, level);
            strcat(Xbuf, ")");
            break;

        default:
            fprintf(stderr, "uno: Unknown type of if node %d\n", (int) ifn->hdr.which);
            break;
        }
        break;

    case FOR_T:
        forn = (for_node *) root;
        switch (forn->hdr.type) {

        case TN_FUNC_DEF:
            explore_tree(forn->init, level);
            explore_tree(forn->test, level);
            if (forn->test->hdr.which == LEAF_T)
                strcat(Xbuf, "()");
            explore_tree(forn->incr, level);
            strcat(Xbuf, " ");
            explore_tree(forn->stemnt, level);
            strcat(Xbuf, " ");
            break;

        case TN_FOR:
            strcat(Xbuf, "for (");
            explore_tree(forn->init, level);
            strcat(Xbuf, ";1 ");
            explore_tree(forn->test, level);
            strcat(Xbuf, ";2 ");
            explore_tree(forn->incr, level);
            strcat(Xbuf, ") ");
            explore_tree(forn->stemnt, level+1);
            break;

        default:
            fprintf(stderr, "uno: Unknown type of for node %d\n", (int) forn->hdr.which);
            break;
        }
        break;

    case NODE_T:
        switch (root->hdr.type) {

        case TN_TRANS_LIST:
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            break;

        case TN_FUNC_DECL:
            decl_cnt++;
            if (root->lnode && (root->lnode->hdr.type == TN_IDENT))
            {   explore_tree(root->lnode, level);
            } else
	    {
                strcat(Xbuf, "(");
                explore_tree(root->lnode, level);
                strcat(Xbuf, ")");
            }
            strcat(Xbuf, "(");
            explore_tree(root->rnode, level);
            strcat(Xbuf, ")");
            decl_cnt--;
            break;

        case TN_FUNC_CALL:
	    explore_tree(root->lnode, level);
            strcat(Xbuf, "(");
            explore_tree(root->rnode, level);
            strcat(Xbuf, ")");
            break;

        case TN_BLOCK:
            strcat(Xbuf, "{");
            explore_tree(root->lnode, level+1);
            explore_tree(root->rnode, level+1);
            strcat(Xbuf, "}");
            break;

        case TN_ARRAY_DECL:
            explore_tree(root->lnode, level);
            strcat(Xbuf, "[");
            explore_tree(root->rnode, level);
            strcat(Xbuf, "]");
            break;

        case TN_EXPR_LIST:
            explore_tree(root->lnode, level);
            if (root->rnode)
              strcat(Xbuf, ",");
            explore_tree(root->rnode, level);
            break;

        case TN_NAME_LIST:
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            break;

        case TN_ENUM_LIST:
            enum_list_cnt++;
            explore_tree(root->lnode, level);
            if (root->rnode)
              strcat(Xbuf, ", ");
            explore_tree(root->rnode, level);
            if (--enum_list_cnt == 0)
              strcat(Xbuf, " ");
            break;

        case TN_FIELD_LIST:
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            break;

        case TN_PARAM_LIST:
            explore_tree(root->lnode, level);
            if (root->rnode)
              strcat(Xbuf, ",");
            explore_tree(root->rnode, level);
            break;

        case TN_IDENT_LIST:
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            break;

        case TN_TYPE_LIST:
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            break;

        case TN_DECL:
            decl_cnt++;
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            if (--decl_cnt == 0)
            {  strcat(Xbuf, "; ");
	    }
            break;

        case TN_DECL_LIST:
            explore_tree(root->lnode, level);
            if ((root->rnode
	    && (root->rnode->hdr.type == TN_IDENT))
            || (root->rnode->lnode
            && ((root->rnode->lnode->hdr.type == TN_IDENT)
            || (root->rnode->lnode->hdr.type == TN_PNTR))) )
              strcat(Xbuf, ",");
            explore_tree(root->rnode, level);
            break;

        case TN_DECLS:
            explore_tree(root->lnode, level);
            if ((root->rnode && (root->rnode->hdr.type == TN_IDENT))
            || (root->rnode->lnode
            && ((root->rnode->lnode->hdr.type == TN_IDENT)
            || (root->rnode->lnode->hdr.type == TN_PNTR))) )
              strcat(Xbuf, ",");
            explore_tree(root->rnode, level);
            break;

        case TN_STEMNT_LIST:
            explore_tree(root->lnode, level);
            if (root->lnode
            && (root->lnode->hdr.type != TN_STEMNT_LIST))
                strcat(Xbuf, ";3 ");

            if (root->rnode != NULL) {
                explore_tree(root->rnode, level);
                strcat(Xbuf, ";4 ");
            }
            break;

        case TN_STEMNT:
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
		{ char *p = strrchr(Xbuf, (int) '5');
		  if (!p || *(p+2) != '\0')
			strcat(Xbuf, ";5 ");
		}
            break;

        case TN_COMP_DECL:
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            strcat(Xbuf, ";6 ");
            break;

        case TN_BIT_FIELD:
            explore_tree(root->lnode, level);
            strcat(Xbuf, ":");
            explore_tree(root->rnode, level);
            break;

        case TN_PNTR:
            strcat(Xbuf, "*");
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            break;

        case TN_TYPE_NME:
            explore_tree(root->lnode, level);
            explore_tree(root->rnode, level);
            break;

        case TN_INIT_LIST:
#if 1
		strcat(Xbuf, "...");
		/* avoid the excessive sizes in lexer.c etc. */
#else
            explore_tree(root->lnode, level);
            strcat(Xbuf, ",");
            explore_tree(root->rnode, level);
#endif
            break;

        case TN_INIT_BLK:
            strcat(Xbuf, "{");
            explore_tree(root->lnode, level);
            strcat(Xbuf, ",");
            explore_tree(root->rnode, level);
            strcat(Xbuf, "}");
            break;

        case TN_OBJ_DEF:
            leaf = (leafnode *) root;
            strcat(Xbuf, toksym(leaf->hdr.tok,1));
            explore_tree(root->lnode, level);
            strcat(Xbuf, " { ");
            explore_tree(root->rnode, level+1);
            strcat(Xbuf, "}");
            break;

        case TN_OBJ_REF:
            leaf = (leafnode *) root;
            strcat(Xbuf, toksym(leaf->hdr.tok,1));
            explore_tree(root->lnode, level);
            strcat(Xbuf, " ");
            explore_tree(root->rnode, level);
            break;

        case TN_CAST:
            decl_cnt++;    /* Not really, it's a hack. */
            strcat(Xbuf, "(");
            explore_tree(root->lnode, level);
            strcat(Xbuf, ")");
            decl_cnt--;
            explore_tree(root->rnode, level);
            break;

        case TN_JUMP:
            strcat(Xbuf, toksym(root->hdr.tok,1));
            if ((root->hdr.tok == RETURN)
	    || (root->hdr.tok == GOTO))
               explore_tree(root->lnode, level);
            break;

        case TN_SWITCH:
            strcat(Xbuf, "switch (");
            explore_tree(root->lnode, level);
            strcat(Xbuf, ") ");
            explore_tree(root->rnode, level+1);
            break;

        case TN_INDEX:
            explore_tree(root->lnode, level);
            strcat(Xbuf, "[");
            explore_tree(root->rnode, level);
            strcat(Xbuf, "]");
            break;

        case TN_DEREF:
            strcat(Xbuf, "*");
            explore_tree(root->lnode, level);
            if (root->rnode && (root->rnode->hdr.type == TN_IDENT))
              explore_tree(root->rnode, level);
            else
            { strcat(Xbuf, "(");
              explore_tree(root->rnode, level);
              strcat(Xbuf, ")");
            }
            break;

        case TN_SELECT:
            explore_tree(root->lnode, level);
            strcat(Xbuf, (root->hdr.tok == ARROW)? "->" : ".");
            explore_tree(root->rnode, level);
            break;

        case TN_ASSIGN:
            explore_tree(root->lnode, level);
            strcat(Xbuf, toksym(root->hdr.tok,1));
            explore_tree(root->rnode, level);
            break;

        case TN_EXPR:
            switch (root->hdr.tok) {
              case CASE:
                strcat(Xbuf, toksym(root->hdr.tok,1));
                explore_tree(root->lnode, level);
                explore_tree(root->rnode, level);
                break;

              case SIZEOF:
                strcat(Xbuf, toksym(root->hdr.tok,0));
                strcat(Xbuf, "(");
                explore_tree(root->lnode, level);
                explore_tree(root->rnode, level);
                strcat(Xbuf, ")");
                break;

              case INCR:
              case DECR:
                explore_tree(root->lnode, level);
                strcat(Xbuf, toksym(root->hdr.tok,1));
                explore_tree(root->rnode, level);
                break;

              case B_AND:
                if (root->lnode == NULL) {
                  strcat(Xbuf, toksym(root->hdr.tok,1));
                  strcat(Xbuf, "(");
                  explore_tree(root->rnode, level);
                  strcat(Xbuf, ")");
                  break;
                } /* else fall thru */

              default:
                strcat(Xbuf, "(");
                explore_tree(root->lnode, level);
                strcat(Xbuf, toksym(root->hdr.tok,1));
                explore_tree(root->rnode, level);
                strcat(Xbuf, ")");
		break;
            }
            break;

        case TN_WHILE:
            strcat(Xbuf, "while (");
            explore_tree(root->lnode, level);
            strcat(Xbuf, ") ");
            explore_tree(root->rnode, level+1);
            break;

        case TN_DOWHILE:
            strcat(Xbuf, "do ");
            explore_tree(root->rnode, level+1);
            if ((root->rnode->hdr.type == TN_STEMNT)
                    && (root->rnode->rnode->hdr.type != TN_BLOCK))
                strcat(Xbuf, ";7");
            strcat(Xbuf, " ");
            strcat(Xbuf, "while (");
            explore_tree(root->lnode, level);
            strcat(Xbuf, ")");
            break;

        case TN_LABEL:
            explore_tree(root->lnode, level);
            if (root->lnode && (root->lnode->hdr.type != TN_LABEL))
              strcat(Xbuf, ": ");
            explore_tree(root->rnode, level);
            break;

        case TN_EMPTY:
        default:
            fprintf(stderr, "uno: Unknown type of tree node (%d).\n",
		(int) root->hdr.type);
            break;
        }
        break;
    }
done:
    nest--;
    walker(root, level, 0);
}

void
set_fnm(char *f)
{
	fnm = f;
}

void
explore(char *f, treenode *root)
{
	set_fnm(f);
	strcpy(Xbuf, "");
	explore_tree(root, 0);
	if (0) puts(Xbuf);
}

#define B_TYPE(n)	n->hdr.which
#define W_TYPE(n)	n->hdr.type
#define W_LINE(n)	n->hdr.line
#define W_FILE		((n->hdr.fnm)?n->hdr.fnm:fnm)

#define IF_THEN(n)	(W_TYPE(n) == TN_IF)
#define IF_ELSE(n)	(((if_node *) n)->else_n)
#define IF_THEN_ELSE(n)	(IF_THEN(n) && IF_ELSE(n))
#define IF_BODY(n)	(((if_node *) n)->then_n)
#define ELSE_BODY(n)	(((if_node *) n)->else_n)

#define SWITCH(n)	(W_TYPE(n) == TN_SWITCH)
#define SWITCH_BODY(n)	(n->rnode)

#define FOR_LOOP(n)	(W_TYPE(n) == TN_FOR)
#define WHILE_LOOP(n)	(W_TYPE(n) == TN_WHILE)
#define UNTIL_LOOP(n)	(W_TYPE(n) == TN_DOWHILE)
#define LOOP(n)		(FOR_LOOP(n) || WHILE_LOOP(n) || UNTIL_LOOP(n))

#define FOR_BODY(n)	(((for_node *) n)->stemnt)
#define WHILE_BODY(n)	(n->rnode)
#define UNTIL_BODY(n)	(n->rnode)

static char *XBuf_Levels[512];
extern char *emalloc(size_t);

static int found_4_1_14;	/* if/then/else/if chains end with an else */
static int found_4_1_4;

int
exclude_location(treenode *n)
{
	if (!xrepro || !n || !n->hdr.fnm) return 1;

	if (Verbose) return 0;

	return (strncmp(W_FILE, "./_", 3) == 0
	     || strncmp(W_FILE, "/usr/include", strlen("/usr/include")) == 0
	     || strncmp(W_FILE, "/usr/lib", strlen("/usr/lib")) == 0);
}

int
follow_chain(treenode *n)
{
	if (IF_THEN_ELSE(n))
	{	return follow_chain(IF_ELSE(n)->rnode);
	} else if (IF_THEN(n))
	{	return 1;	/* last leg is not an else */
	}
	return 0;
}

void
location(treenode *n)
{
	n->hdr.warned++;
	printf("%s:%d: ", W_FILE, W_LINE(n));
	fflush(stdout);
}

int
has_default(treenode *n)
{
	if (!n
	||  SWITCH(n)
	||  B_TYPE(n) == LEAF_T)
	{	return 0;
	}

        if (B_TYPE(n) == NODE_T
	&&  W_TYPE(n) == TN_LABEL
	&&  B_TYPE(n->lnode) == LEAF_T)
	{	return (n->lnode->hdr.tok == DEFLT);
	}

	return has_default(n->rnode) || has_default(n->lnode);
}

static char *
has_lower_case(treenode *n)
{	char *ptr;

	if (!n || n->hdr.warned)
	{	return NULL;
	}

	if (B_TYPE(n) == LEAF_T)
	{	if (W_TYPE(n) == TN_IDENT)
		{	char *p = ((leafnode *)n)->data.sval->str;
			while (*p != '\0')
			{	if (islower((int) *p++))
				{	n->hdr.warned++;
					return ((leafnode *)n)->data.sval->str;
		}	}	}
		return NULL;
	}

	if ((ptr = has_lower_case(n->lnode)) != NULL)
	{	n->hdr.warned++;
		return ptr;
	}
	return has_lower_case(n->rnode);
}

int
has_extern(treenode *n)
{
	assert(W_TYPE(n) == TN_TYPE_LIST);
	assert(n->lnode != NULL);
	
	return (B_TYPE(n->lnode) == LEAF_T
	     && W_TYPE(n->lnode) == TN_TYPE
	     && n->lnode->hdr.tok == EXTRN);
}

int
has_non_obj(treenode *n)
{	/* at least one child node is different from TN_OBJ_DEF */

	assert(W_TYPE(n) == TN_TYPE_LIST);

	if (n->lnode)
	{	if (W_TYPE(n->lnode) != TN_OBJ_DEF)
			return 1;
		if (W_TYPE(n->lnode) == TN_TYPE_LIST)
			return has_non_obj(n->lnode);
	}

	if (n->rnode)
	{	if (W_TYPE(n->rnode) != TN_OBJ_DEF)
			return 1;
		if (W_TYPE(n->rnode) == TN_TYPE_LIST)
			return has_non_obj(n->rnode);
	}

	return 0;
}

void
walker(treenode *n, int level, int pre)
{
	if (level >= sizeof(XBuf_Levels)/sizeof(char *))
	{	fprintf(stderr, "error: exceeded builtin depth limit\n");
		clean_tmps();
		exit(1);
	}
	if (!XBuf_Levels[level])
	{	XBuf_Levels[level] = emalloc(BufLimit * sizeof(char));
	}
	Xbuf = XBuf_Levels[level];

	if (n->hdr.warned || exclude_location(n))
	{	return;
	}

	/**** rule 4.1.14  all if/then/else/if chains must end with an else */
	/**** rule 4.1.13  all if stmnts must be compound statements */

	if (IF_THEN_ELSE(n))
	{	if (follow_chain(IF_ELSE(n)->rnode))
		{	if (pre)
			{	found_4_1_14++;
				Xbuf[0] = '\0';
			} else
			{	if (--found_4_1_14 == 0)
				{	location(n);
					printf("if-then-else-if chain does not end with 'else' (%s)\n",
					Xbuf);
		}	}	}

		if (IF_BODY(n)->rnode == NULL
		|| (W_TYPE(IF_BODY(n)->rnode) != TN_BLOCK && W_TYPE(IF_BODY(n)->rnode) != TN_IF ))
		{	location(n);
			printf("body of if-statement is not enclosed in braces\n");
		}
		if (ELSE_BODY(n)->rnode == NULL
		|| (W_TYPE(ELSE_BODY(n)->rnode) != TN_BLOCK && W_TYPE(ELSE_BODY(n)->rnode) != TN_IF ))
		{	location(n);
			printf("body of else is not enclosed in braces\n");
	}	}

	/**** rule 4.1.13  all if stmnts must be compound statements */
	if (IF_THEN(n))
	{	if (IF_BODY(n)->rnode == NULL
		|| (W_TYPE(IF_BODY(n)->rnode) != TN_BLOCK && W_TYPE(IF_BODY(n)->rnode) != TN_IF ))
		{	location(n);
			printf("body of if-statement is not enclosed in braces\n");
	}	}


	/**** rule 4.1.12 all loops must be compound statements */

	if (pre && FOR_LOOP(n)
	&& (FOR_BODY(n)->rnode == NULL || W_TYPE(FOR_BODY(n)->rnode) != TN_BLOCK))
	{	location(n);
		printf("body of for-stmnt is not enclosed in braces\n");
		/* name_of_node(W_TYPE(FOR_BODY(n))) */
	}

	if (pre && (WHILE_LOOP(n) || UNTIL_LOOP(n))
	&& W_TYPE(WHILE_BODY(n->rnode)) != TN_BLOCK)
	{	location(n);
		printf("body of while is not enclosed in braces\n");
		/* name_of_node(W_TYPE(WHILE_BODY(n->rnode))) */
	}

	/**** rule 4.1.15 every switch statement must have a default */

	if (pre && SWITCH(n) && W_TYPE(SWITCH_BODY(n)->rnode) == TN_BLOCK)
	{	if (!has_default(SWITCH_BODY(n)->rnode->lnode))
		{	location(n);
			printf("switch has no default case\n");
		}
	}

	/**** rule 4.9.5 enum and macro names must be in upper case */
	if (pre && B_TYPE(n) == NODE_T && W_TYPE(n) == TN_ENUM_LIST)
	{	char *p = has_lower_case(n);
		if (p)
		{	location(n);
			printf("enum name '%s' has lower-case characters\n", p);
	}	}

	/**** rule 4.9.4 variable and function names, and tags, have no uppercase */
	/**** rule 4.1.5 function prototypes must be declared at file scope */
	if (pre && B_TYPE(n) == NODE_T && W_TYPE(n) == TN_FUNC_DECL)
	{	extern int has_upper(char *);

		if (n->lnode
		&&  W_TYPE(n->lnode) == TN_IDENT)
		{	if (has_upper(((leafnode *)n->lnode)->data.sval->str))
			{	location(n);
				printf("function name '%s' has uppercase chars\n",
					((leafnode *)n->lnode)->data.sval->str);
			}
			if (n->lnode->syment->nes->level > 3)
			{	location(n);
				printf("function prototype '%s' not declared at file-scope\n",
					((leafnode *)n->lnode)->data.sval->str);
	}	}	}

	/**** rule 4.1.4 no objects or functions may be defined in header files */

	if (W_TYPE(n) == TN_DECL
	&&  strstr(W_FILE, ".h")
	&&  n->lnode
	&&  n->rnode
	&&  W_TYPE(n->lnode) == TN_TYPE_LIST
	&&  has_non_obj(n->lnode))
	{	if (has_extern(n->lnode))
		{	if (pre)
			{	found_4_1_4++;
			} else
			{	found_4_1_4--;
			}
		} else if (n->rnode)
		{	if (found_4_1_4 == 0)
			{	if (pre)
				{	Xbuf[0] = '\0';
				} else
				{	location(n);
					printf("object '%s' defined in header file\n", Xbuf);
					Xbuf[0] = '\0';
	}	}	}	}
}
