/***** uno: lexer.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#ifndef LEXER_H
#define LEXER_H

#include <stdio.h>
#include "tree.h"

#define MAX_STRING_LEN	 512	/* max length for strings and identifiers */

/* If we allow a comment as a token, we need to let them be larger. */
#define MAX_TOKN_LEN	8192

typedef union {
	treenode *node;
	leafnode *leaf;
	if_node  *ifn;
	for_node *forn;
} tree_union;

/* Flex compatibility:  */
#undef  YYSTYPE
#define YYSTYPE	tree_union

void get_lineno (int);
void yywarn  (char *s);
int  yyerror (const char *s);
int  yyerr   (char *s);

#endif  /* LEXER_H */
