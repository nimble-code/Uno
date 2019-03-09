/***** uno: nmetab.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#ifndef     NMETAB_H
#define     NMETAB_H

typedef struct string_str {
	unsigned int	hash;
	char		*str;
} str_t;

extern void	init_nmetab(void);	/* uno_local.c */
extern str_t	*nmelook(char *, int);	/* c_gram.y, lexer.l, uno_lts.c */
extern char	*nmestr(str_t *);		/* c_gram.y, dflow.c, uno_lts.c */

#endif    /* NMETAB_H */
