/***** uno: dtags.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* dataflow tags used in dflow.c, uno_lts.c, and uno_global.c:
 * bitfields stored in a 32bit unsigned integer field called 'mark'
 */

#define DEF		1		/*       1  x = y */
#define FCALL		(1<<1)		/*       2  f()   */
#define USE		(1<<2)		/*       4  y = x */
#define REF0		(1<<3)		/*       8  x->y  */
#define REF1		(1<<4)		/*      16  x.y   */
#define REF2		(1<<5)		/*      32  y.x or y->x */
#define DEREF		(1<<6)		/*      64  *x    */
#define ALIAS		(1<<7)		/*     128  &x    */
#define ARRAY_DECL	(1<<8)		/*     256  x[]   */
#define HIDE		(1<<9)		/*     512        */
#define DECL		(1<<10)		/*    1024        */
#define USEafterdef	(1<<11)		/*    2048  y = x++ */
#define USEbeforedef	(1<<12)		/*    4096  x++   */
#define UNO_CONST	(1<<13)		/*    8192  f(x)  */
#define PARAM		(1<<14)		/*   16384        */
#define INCOND		(1<<15)		/*   32768  if (x) */
#define ISTATIC		(1<<16)		/*   65536  static int x */
#define IN_SIZEOF	(1<<17)		/*  131072  sizeof(x) */
#define IS_PTR		(1<<18)		/*  262144  decl of ptr */

#define NONE		0
#define ANY		((1<<20)-1)

#define SELECTED	(1<<24)		/* 16777216 outside ANY, below 31 */
