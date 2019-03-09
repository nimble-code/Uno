%{
/***** uno: lexer.l *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */
/* small tweask by Russ Cox to allow wide characters and string consts    */

/*************************************************
 *	Shaun Flisakowski
 *	revised 1996 Kurt Cockrum <kurt@grogatch.seaslug.org>
 *	revised 2000 Gerard Holzmann <gholzmann [atsignhere] acm.org>
 *	revised 2003 Russ Cox     <rsc@achille.cs.bell-labs.com<
 *************************************************/

#define DBG	0	/* debugging */
#define ECHO	/* flex may insert an unwanted ECHO */

#undef yywrap
int yywrap(void);

#define YY_BUFFER_STATE_DEFD
#define YY_NO_INPUT

#include "globals.h"
#include "c_gram.h"
#include "lexer.h"
#include "nmetab.h"
#include "symtab.h"

FILE *yyin;
static char line_buf[MAX_TOKN_LEN];

       int  err_cnt = 0;
static int  err_tok = 0;
static int  err_type = 0;
static int  in_preprocess = 0;
static int  gcc2_paren_cnt = 0;

static char  tokn_buff[MAX_TOKN_LEN];
static char *tokn_end = &tokn_buff[MAX_TOKN_LEN-1];
static char *tokn_ptr = 0;

extern TreeStack *ParseStack;	/* uno_local.c */
extern Stk_Item  *Parse_TOS;		/* uno_local.c */

int cnt_nl(char *, int);
extern void *emalloc(size_t);
extern char *toksym(int, int);

#undef YY_INPUT

#ifdef STRING_PARSE

#define    min(X,Y)    ((X)<(Y) ? (X) : (Y))

    /* Scan input from a string instead */
#define YY_INPUT(buf,result,max_size) \
  {  int n = min(max_size, Parse_TOS->parselimit - Parse_TOS->parseptr);\
     if (n>0){ \
        memcpy(buf,Parse_TOS->parseptr,(unsigned int) n); \
        Parse_TOS->parseptr += n; \
        result = n; \
     } else \
        result = YY_NULL; \
  }

#else    /* not STRING_PARSE */

    /* Scan input from a file pointer (default) */
#define YY_INPUT(buf,result,max_size) \
    {   if (fgets((char*) (buf),max_size,yyin) == NULL) { \
           result = YY_NULL; \
        } else { \
           result = strlen((char*)(buf)); \
           strncpy(line_buf, (char*)(buf), result+1 /* MAX_TOKN_LEN */); \
        } \
    }

#endif    /* not STRING_PARSE */

#define YY_USER_ACTION \
    {   Parse_TOS->yycolno = Parse_TOS->yynxtcol; \
        Parse_TOS->yynxtcol += yyleng; \
    }

#undef SETPOS_NDE
#define SETPOS_NDE(TYPE) \
	{ err_type = 0; \
          lvalp->node = make_node(TN_EMPTY); \
          lvalp->node->hdr.line = Parse_TOS->yylineno; \
          lvalp->node->hdr.col  = Parse_TOS->yycolno; \
	  lvalp->node->hdr.fnm = Parse_TOS->filename; \
          err_tok = lvalp->node->hdr.tok = (int) (TYPE); \
	}

#undef SETPOS_LEAF
#define SETPOS_LEAF(TOK_TYPE,PRSE_TYPE) \
	{ lvalp->leaf = make_leaf((err_type= (int) PRSE_TYPE)); \
          lvalp->leaf->hdr.line = Parse_TOS->yylineno; \
          lvalp->leaf->hdr.col  = Parse_TOS->yycolno; \
	  lvalp->leaf->hdr.fnm = Parse_TOS->filename; \
          err_tok = lvalp->leaf->hdr.tok  = (int) (TOK_TYPE); \
	}

#undef SETPOS_IF
#define SETPOS_IF(TYPE) \
	{ err_type = 0; \
          lvalp->ifn = make_if(err_type= (int) TN_IF); \
          lvalp->ifn->hdr.line = Parse_TOS->yylineno; \
          lvalp->ifn->hdr.col  = Parse_TOS->yycolno; \
	  lvalp->ifn->hdr.fnm = Parse_TOS->filename; \
          err_tok = lvalp->ifn->hdr.tok  = (int) (TYPE); \
	}

#undef SETPOS_FOR
#define SETPOS_FOR(TYPE) \
	{ err_type = 0; \
          lvalp->forn = make_for(err_type= (int) TN_FOR); \
          lvalp->forn->hdr.line = Parse_TOS->yylineno; \
          lvalp->forn->hdr.col  = Parse_TOS->yycolno; \
	  lvalp->forn->hdr.fnm = Parse_TOS->filename; \
          err_tok = lvalp->forn->hdr.tok  = (int) (TYPE); \
	}

#undef  LAST_STATE
#define LAST_STATE() \
        { if (in_preprocess) \
            BEGIN(PP); \
          else \
            BEGIN(INITIAL); \
        }

#undef  BEGIN_PP
#define BEGIN_PP() \
        { BEGIN(PP); \
          in_preprocess = 1; \
        }

/* YYSTYPE my_var;	not used, gjh */

extern int yylex(YYSTYPE *);

/*  To give some args to yylex */
#undef YY_DECL
#ifdef  __STDC__
/*  #define YY_DECL int yylex YY_PROTO((YYSTYPE *lvalp))  */
#define YY_DECL int yylex (YYSTYPE *lvalp)
#else
#define YY_DECL int yylex(lvalp) YYSTYPE *lvalp;
#endif
%}
%option nounput
%option never-interactive

%x Start PP CMMT CC STR GCC2
%a 9000
%o 9000

dot		"."
digit		[0-9]
octdigit	[0-7]
hexdigit	[0-9a-fA-F]
digits          {digit}+
alpha		[a-zA-Z_]
alphanum	{alpha}|{digit}

usuffix         [uU]
lsuffix         [lL]
intsuffix       {usuffix}{lsuffix}*|{lsuffix}+{usuffix}?
intnum		{digit}+{intsuffix}?
octnum		0{octdigit}+{intsuffix}?
hexnum		0[xX]{hexdigit}+{intsuffix}*

exponent	[Ee][+-]?{digits}
floatsuffix     [fFlL]

whitespace      [ \t\f\v\r]
allwhite        [ \t\f\b\v\r\n]

pp_strt         ^{whitespace}*"#"{whitespace}*

%%
<INITIAL>"/*"       { BEGIN(CMMT);
                      tokn_ptr = tokn_buff;
                     *tokn_ptr++ = '/';
                     *tokn_ptr++ = '*';
                      SETPOS_LEAF(COMMENT,TN_COMMENT);
                    }
<INITIAL>L?"'"        { BEGIN(CC);    SETPOS_LEAF(CHAR_CONST,TN_INT); }
<INITIAL>L?\"         { BEGIN(STR);   tokn_ptr = tokn_buff;
                         SETPOS_LEAF(STRING,TN_STRING);
                    }

<INITIAL>"//*"      {    yywarn(
                            "Ambiguous C++ comment, use '/ /*' -or- '// *'");
                         yyless(1);
                         SETPOS_NDE(DIV);
                         return(DIV);
                    }
<INITIAL>"//"[^*].*$ { /* C++ style comment */ }

<INITIAL>"auto"     { SETPOS_LEAF(AUTO,TN_TYPE); return(AUTO); }
<INITIAL>"break"    { SETPOS_NDE(BREAK); return(BREAK); }
<INITIAL>"case"     { SETPOS_NDE(CASE); return(CASE); }
<INITIAL>"char"     { SETPOS_LEAF(CHAR,TN_TYPE); return(CHAR); }
<INITIAL>"const"    { SETPOS_LEAF(CONST,TN_TYPE); return(CONST); }
<INITIAL>"continue" { SETPOS_NDE(CONT); return(CONT); }
<INITIAL>"default"  { SETPOS_LEAF(DEFLT,TN_LABEL); return(DEFLT); }
<INITIAL>"do"       { SETPOS_NDE(DO); return(DO); }
<INITIAL>"double"   { SETPOS_LEAF(DOUBLE,TN_TYPE); return(DOUBLE); }
<INITIAL>"else"     { SETPOS_NDE(ELSE); return(ELSE); }
<INITIAL>"enum"     { SETPOS_NDE(ENUM); return(ENUM); }
<INITIAL>"extern"   { SETPOS_LEAF(EXTRN,TN_TYPE); return(EXTRN); }
<INITIAL>"float"    { SETPOS_LEAF(FLOAT,TN_TYPE); return(FLOAT); }
<INITIAL>"for"      { SETPOS_FOR(FOR); return(FOR); }
<INITIAL>"goto"     { SETPOS_NDE(GOTO); return(GOTO); }
<INITIAL>"if"       { SETPOS_IF(IF); return(IF); }
<INITIAL>"__int8"   { SETPOS_LEAF(CHAR,TN_TYPE); return(CHAR);	/* VC++ */ }
<INITIAL>"__int16"  { SETPOS_LEAF(SHORT,TN_TYPE); return(SHORT);/* VC++ */ }
<INITIAL>"__int32"  { SETPOS_LEAF(INT,TN_TYPE); return(INT);	/* VC++ */ }
<INITIAL>"__int64"  { SETPOS_LEAF(LONG,TN_TYPE); return(LONG);	/* VC++ */ }
<INITIAL>"int"      { SETPOS_LEAF(INT,TN_TYPE); return(INT); }
<INITIAL>"long"     { SETPOS_LEAF(LONG,TN_TYPE); return(LONG); }
<INITIAL>"register" { SETPOS_LEAF(REGISTR,TN_TYPE); return(REGISTR); }
<INITIAL>"return"   { SETPOS_NDE(RETURN); return(RETURN); }
<INITIAL>"short"    { SETPOS_LEAF(SHORT,TN_TYPE); return(SHORT); }
<INITIAL>"signed"   { SETPOS_LEAF(SGNED,TN_TYPE); return(SGNED); }
<INITIAL>"sizeof"   { SETPOS_NDE(SIZEOF); return(SIZEOF); }
<INITIAL>"static"   { SETPOS_LEAF(STATIC,TN_TYPE); return(STATIC); }
<INITIAL>"struct"   { SETPOS_NDE(STRUCT); return(STRUCT); }
<INITIAL>"switch"   { SETPOS_NDE(SWITCH); return(SWITCH); }
<INITIAL>"typedef"  { SETPOS_LEAF(TYPEDEF,TN_TYPE); return(TYPEDEF); }
<INITIAL>"union"    { SETPOS_NDE(UNION); return(UNION); }
<INITIAL>"unsigned" { SETPOS_LEAF(UNSGNED,TN_TYPE); return(UNSGNED); }
<INITIAL>"void"     { SETPOS_LEAF(VOID,TN_TYPE); return(VOID); }
<INITIAL>"volatile" { SETPOS_LEAF(VOLATILE,TN_TYPE); return(VOLATILE); }
<INITIAL>"while"    { SETPOS_NDE(WHILE); return(WHILE); }

   /* GCC2 Extensions */
<INITIAL>"__attribute"    { /* gcc2 extension - get rid of it. */
                            BEGIN(GCC2);
                          }

<INITIAL>"__attribute__"  { BEGIN(GCC2); }
<INITIAL>"__declspec"     { BEGIN(GCC2); /* MS Visual Studio */ }
<INITIAL>"restrict"	  { /* C99 */ }
<INITIAL>"__restrict"     { }
<INITIAL>"__restrict__"   { }

<GCC2>"("[^()]*           { gcc2_paren_cnt++; }
<GCC2>[^()]*              { /* Throw away */ }
<GCC2>")"                 { if (--gcc2_paren_cnt == 0)
                              BEGIN(INITIAL);
                          }

<INITIAL>"__const"    { SETPOS_LEAF(CONST,TN_TYPE); return(CONST); }
<INITIAL>"__const__"  { SETPOS_LEAF(CONST,TN_TYPE); return(CONST); }
<INITIAL>"__signed" { SETPOS_LEAF(SGNED,TN_TYPE); return(SGNED); }
<INITIAL>"__signed__" { SETPOS_LEAF(SGNED,TN_TYPE); return(SGNED); }
<INITIAL>"__volatile" { SETPOS_LEAF(VOLATILE,TN_TYPE); return(VOLATILE); }
<INITIAL>"__volatile__" { SETPOS_LEAF(VOLATILE,TN_TYPE); return(VOLATILE); }

<INITIAL>"typeof"      { }
<INITIAL>"__typeof"    { }
<INITIAL>"__typeof__"  { }

<INITIAL>"inline"      { }
<INITIAL>"__inline"    { }
<INITIAL>"__inline__"  { }
<INITIAL>"__packed"    { }
<INITIAL>"__packed__"  { /* seen in Nexabit Code */ }
<INITIAL>"__cdecl"     { /* MS Visual Studio */ }

<INITIAL>"__extension__"  { }

<INITIAL>"alignof"      { /* gjh */ SETPOS_NDE(ALIGNOF); return(ALIGNOF); }
<INITIAL>"__alignof"    { /* gjh */ SETPOS_NDE(ALIGNOF); return(ALIGNOF); }
<INITIAL>"__alignof__"  { /* gjh */ SETPOS_NDE(ALIGNOF); return(ALIGNOF); }

<INITIAL>"__asm"      { /* gjh added: */ BEGIN(GCC2); }
<INITIAL>"__asm__"    { /* gjh added: */ BEGIN(GCC2); }

<INITIAL>"__imag"     { }
<INITIAL>"__imag__"   { }
<INITIAL>"__real"     { }
<INITIAL>"__real__"   { }
<INITIAL>"__complex"    { }
<INITIAL>"__complex__"  { }
<INITIAL>"__iterator"   { }
<INITIAL>"__iterator__" { }
<INITIAL>"__label__"    { }

<INITIAL>"+"        { SETPOS_NDE(PLUS); return(PLUS); }
<INITIAL>"-"        { SETPOS_NDE(MINUS); return(MINUS); }
<INITIAL>"*"        { SETPOS_NDE(STAR); return(STAR); }
<INITIAL>"/"        { SETPOS_NDE(DIV); return(DIV); }
<INITIAL>"%"        { SETPOS_NDE(MOD); return(MOD); }

<INITIAL>"+="       { SETPOS_NDE(PLUS_EQ); return(ASSIGN); }
<INITIAL>"-="       { SETPOS_NDE(MINUS_EQ); return(ASSIGN); }
<INITIAL>"*="       { SETPOS_NDE(STAR_EQ); return(ASSIGN); }
<INITIAL>"/="       { SETPOS_NDE(DIV_EQ); return(ASSIGN); }
<INITIAL>"%="       { SETPOS_NDE(MOD_EQ); return(ASSIGN); }

<INITIAL>"!"        { SETPOS_NDE(NOT); return(NOT); }
<INITIAL>"&&"       { SETPOS_NDE(AND); return(AND); }
<INITIAL>"||"       { SETPOS_NDE(OR); return(OR); }

<INITIAL>"~"        { SETPOS_NDE(B_NOT); return(B_NOT); }
<INITIAL>"&"        { SETPOS_NDE(B_AND); return(B_AND); }
<INITIAL>"|"        { SETPOS_NDE(B_OR); return(B_OR); }
<INITIAL>"^"        { SETPOS_NDE(B_XOR); return(B_XOR); }

<INITIAL>"~="       { SETPOS_NDE(B_NOT_EQ); return(ASSIGN); }
<INITIAL>"&="       { SETPOS_NDE(B_AND_EQ); return(ASSIGN); }
<INITIAL>"|="       { SETPOS_NDE(B_OR_EQ); return(ASSIGN); }
<INITIAL>"^="       { SETPOS_NDE(B_XOR_EQ); return(ASSIGN); }

<INITIAL>"<<"       { SETPOS_NDE(L_SHIFT); return(L_SHIFT); }
<INITIAL>">>"       { SETPOS_NDE(R_SHIFT); return(R_SHIFT); }
<INITIAL>"<<="      { SETPOS_NDE(L_SHIFT_EQ); return(ASSIGN); }
<INITIAL>">>="      { SETPOS_NDE(R_SHIFT_EQ); return(ASSIGN); }

<INITIAL>"=="       { SETPOS_NDE(EQUAL); return(COMP_EQ); }
<INITIAL>"<"        { SETPOS_NDE(LESS); return(COMP_ARITH); }
<PP>"<"             { SETPOS_NDE(LESS); return(LESS); }
<INITIAL>"<="       { SETPOS_NDE(LESS_EQ); return(COMP_ARITH); }
<INITIAL>">"        { SETPOS_NDE(GRTR); return(COMP_ARITH); }
<PP>">"             { SETPOS_NDE(GRTR); return(GRTR); }
<INITIAL>">="       { SETPOS_NDE(GRTR_EQ); return(COMP_ARITH); }
<INITIAL>"!="       { SETPOS_NDE(NOT_EQ); return(COMP_EQ); }

<INITIAL>"="        { SETPOS_NDE(EQ); return(EQ); }
<INITIAL>"++"       { SETPOS_NDE(INCR); return(INCR); }
<INITIAL>"--"       { SETPOS_NDE(DECR); return(DECR); }

<INITIAL>"("        { SETPOS_NDE(LPAREN); return(LPAREN); }
<INITIAL>")"        { SETPOS_NDE(RPAREN); return(RPAREN); }
<INITIAL>"["        { SETPOS_NDE(LBRCKT); return(LBRCKT); }
<INITIAL>"]"        { SETPOS_NDE(RBRCKT); return(RBRCKT); }
<INITIAL>"{"        { SETPOS_NDE(LBRACE); return(LBRACE); }
<INITIAL>"}"        { SETPOS_NDE(RBRACE); return(RBRACE); }

<INITIAL>"."        { SETPOS_NDE(DOT); return(DOT); }
<INITIAL>"->"       { SETPOS_NDE(ARROW); return(ARROW); }

<INITIAL>"?"        { SETPOS_NDE(QUESTMARK); return(QUESTMARK); }
<INITIAL>":"        { SETPOS_NDE(COLON); return(COLON); }
<INITIAL>";"        { SETPOS_NDE(SEMICOLON); return(SEMICOLON); }
<INITIAL>","        { SETPOS_NDE(COMMA); return(COMMA); }
<INITIAL>"..."      { SETPOS_LEAF(ELLIPSIS,TN_ELLIPSIS); return(ELLIPSIS); }

	/* Unused (invalid) characters */
<INITIAL>"`"        { SETPOS_NDE(BACKQUOTE); return(BACKQUOTE); }
<INITIAL>"@"        { SETPOS_NDE(AT); return(AT); }
<INITIAL>"$"        { SETPOS_NDE(DOLLAR); return(DOLLAR); }

	/* Preprocessor Stuff */
<INITIAL>{pp_strt}\n       { Parse_TOS->yylineno++; Parse_TOS->yynxtcol = 0;
			   }
<INITIAL>{pp_strt}{digits}.*$ { BEGIN_PP(); get_lineno(1); }
<INITIAL>{pp_strt}"define" {
                             int n = yyleng;
                             BEGIN_PP();
                             tokn_ptr = tokn_buff;
                             if (tokn_ptr + n < tokn_end) {
                                 memcpy(tokn_ptr,yytext,n);
                                 tokn_ptr += n;
                             } else 
                                yywarn("Preprocessor line too long");
                             SETPOS_LEAF(PP_DEFINE,TN_CPP);
                           }
<INITIAL>{pp_strt}"include" { BEGIN_PP(); }
<INITIAL>{pp_strt}"line"   { BEGIN_PP(); get_lineno(2); }
<INITIAL>{pp_strt}"pragma" { BEGIN_PP(); }
<INITIAL>{pp_strt}"ident"  { BEGIN_PP(); }
<INITIAL>{pp_strt}"if"     { BEGIN_PP(); }
<INITIAL>{pp_strt}"ifdef"  { BEGIN_PP(); }
<INITIAL>{pp_strt}"ifndef" { BEGIN_PP(); }
<INITIAL>{pp_strt}"else"   { BEGIN_PP(); }
<INITIAL>{pp_strt}"elif"   { BEGIN_PP(); }
<INITIAL>{pp_strt}"endif"  { BEGIN_PP(); }
<INITIAL>{pp_strt}"error"  { BEGIN_PP(); }
<INITIAL>{pp_strt}"undef"  { BEGIN_PP(); }

<PP>"#"                { SETPOS_NDE(LB_SIGN); return(LB_SIGN); }
<PP>"##"               { SETPOS_NDE(DOUB_LB_SIGN); return(DOUB_LB_SIGN); }

<PP>\\(\n)             {  /* Preprocessor continuation line */
                         Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 0;
                       }

<PP>\n                 {  /* End of this preprocessor logical line */
                         lvalp->node = (treenode *) NULL;
                         in_preprocess = 0;
                         yyless(0);    /* Hack! */
                         BEGIN(INITIAL);
                       }

<PP>[^\n\\]+           { /* Swallow cpp junk to prevent it being echo'd */
                       }

<INITIAL>{alpha}{alphanum}*  {    /* Identifier */
                         int last_was_type = (err_type == TN_TYPE)
                                          && (err_tok != TYPEDEF)
                                          && (err_tok != AUTO)
                                          && (err_tok != EXTRN)
                                          && (err_tok != STATIC)
                                          && (err_tok != VOLATILE)
                                          && (err_tok != CONST)
                                          && (err_tok != REGISTR);

                         SETPOS_LEAF(IDENT,TN_IDENT);

                         lvalp->leaf->data.sval = nmelook(yytext,yyleng+1);

                         /* Check symbol table and insert */
                         /* ptr back to definition.       */
                         {	symentry_t *se;

				if (DBG)	printf("%s:%d lookup %s <%s>\n",
						lvalp->leaf->hdr.fnm,
						lvalp->leaf->hdr.line,
						yytext, lvalp->leaf->data.sval->str);

				se = symtab_lookup(ParseStack->contxt->syms,
                                              lvalp->leaf->data.sval);
				if (DBG)
				{ if (!se) printf("	new\n");
				  else
				  {	extern void show_hashtab(hashtab_t *that, int, FILE *fp);
					printf("	old (%p) -- owner %s %p\n", se,
					se->nes && se->nes->owner ? se->nes->owner : "no owner",
					se && se->nes? se->nes : 0);
					if (se && se->nes && se->nes->htab)
					show_hashtab(se->nes->htab, 1, stdout);
				  }
				}

				lvalp->leaf->syment = se;

				if (!last_was_type)
				{	if (se && is_typedef(se))
					{	err_type = lvalp->leaf->hdr.type = TN_TYPE;
						err_tok = lvalp->leaf->hdr.tok = TYPEDEF_NAME;
						return(TYPEDEF_NAME);
			 }	}	}
                         return(IDENT);
                       }

<INITIAL>{octnum}  |
<INITIAL>{intnum}  |
<INITIAL>{hexnum}   {  /* An integer */
                         SETPOS_LEAF(INUM,TN_INT);
                         lvalp->leaf->data.ival 
                                = strtol(yytext,(char **) NULL,0);
                         return(INUM);
                    }
          
<INITIAL>{digits}{dot}{digits}{exponent}?{floatsuffix}? |
<INITIAL>{digits}{dot}{exponent}?{floatsuffix}?         |
<INITIAL>{dot}{digits}{exponent}?{floatsuffix}?         |
<INITIAL>{digits}{exponent}{floatsuffix}? {
                         /*
                         ** Note: The floatsuffix, if any, will be
                         ** ignored by atof().
                         */
                         SETPOS_LEAF(RNUM,TN_REAL);
                         lvalp->leaf->data.dval = atof(yytext);
                         return(RNUM);
                       }

<STR>\"{allwhite}*\"   {   /* String Pasting */
                         cnt_nl(yytext,yyleng);
                       }

<STR>\"                {   /* Closing quote */
                         LAST_STATE();
                         *tokn_ptr = '\0';
                         lvalp->leaf->data.str = emalloc(strlen(tokn_buff)+1);
                         strcpy(lvalp->leaf->data.str,tokn_buff);
                         return(STRING);
                       }

<STR>\n                { /* Error - unterminated string constant */
                         yyerr("Unterminated string constant starting");
                         LAST_STATE();
                         return(INVALID);
                       }

<STR>\\[0-7]{1,3}      {   /* octal escape sequence */
                         unsigned int result;

                         if (sscanf(yytext+1, "%o", &result ) < 1)
                         {
                             yyerr("Invalid octal escape sequence");
                             LAST_STATE();
                             return(INVALID);
                         }

                             /* error, constant is out-of-bounds */
                         if ( result > 0xff ){
                            yyerr("Escape sequence out-of-bounds");
                         }

                         if (tokn_ptr < tokn_end)
                            *tokn_ptr++ = result;
                         else
                            yywarn("String constant too long");
                       }

<STR>\\x{hexdigit}+    {   /* hex escape sequence - ISO C */
                         unsigned int result;

                         if (sscanf(yytext+2, "%x", &result ) < 1)
                         {
                             yyerr("Invalid hex escape sequence");
                             LAST_STATE();
                             return(INVALID);
                         }

                             /* error, constant is out-of-bounds */
                         if ( result > 0xff ){
                            yyerr("Escape sequence out-of-bounds");
                         } else if (yyleng > 4){
                            yywarn("Hexadecimal escape exceeds two chars");
                         }

                         if (tokn_ptr < tokn_end)
                            *tokn_ptr++ = result;
                         else
                            yywarn("String constant too long");
                       }

<STR>\\{digits}        {  /* Bad escape sequence */
                         yywarn("Bad escape sequence in string");
                        *tokn_ptr++ = '?';
                       }

<STR>\\n               {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = '\n';
                         else
                            yywarn("String constant too long");
                       }

<STR>\\t               {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = '\t';
                         else
                            yywarn("String constant too long");
                       }

<STR>\\r               {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = '\r';
                         else
                            yywarn("String constant too long");
                       }

<STR>\\b               {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = '\b';
                         else
                            yywarn("String constant too long");
                       }

<STR>\\f               {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = '\f';
                         else
                            yywarn("String constant too long");
                       }

<STR>\\v               {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = '\v';
                         else
                            yywarn("String constant too long");
                       }

<STR>\\a               {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = '\a';
                         else
                            yywarn("String constant too long");
                       }

<STR>\\(\n)            {  /* String continuation */
                         Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 0;
                       }

<STR>\\.               {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = yytext[1];
                         else
                            yywarn("String constant too long");
                       }

<STR>[^\\\n\"]+        {
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("String constant too long");
                       }

<CMMT>[^*\n/\\]*       {   /* Inside C-style comment */
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");
                       }

<CMMT>[^*\n/\\]*\n     {
                         int n = yyleng;
                         Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 0;
                         in_preprocess = 0;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");
                       }
<CMMT>"/"[^*\n]        {
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");
                       }
<CMMT>\\\n             {
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");
                         Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 0;
                       }
<CMMT>\\[^\n]          {
                         if (tokn_ptr < tokn_end)
                           *tokn_ptr++ = yytext[1];
                         else
                            yywarn("Comment too long");
                         yyless(1);
                       }
<CMMT>"/"\n            {
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");
                         Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 0;
                         in_preprocess = 0;
                       }
<CMMT>"/*"             {
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");
                         yywarn("/* inside comment");
                       }
<CMMT>"*"+[^*/\n\\]*   {   /* Stars */
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");
                       }
<CMMT>"*"+[^*/\n\\]*\n {
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");
                         Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 0;
                         in_preprocess = 0;
                       }
<CMMT>"*"+"/"          {
                         int n = yyleng;
                         if (tokn_ptr + n < tokn_end) {
                             memcpy(tokn_ptr,yytext,n);
                             tokn_ptr += n;
                         } else 
                            yywarn("Comment too long");

                         LAST_STATE();
                         *tokn_ptr = '\0';
                         lvalp->leaf->data.str = emalloc(strlen(tokn_buff)+1);
                         strcpy(lvalp->leaf->data.str,tokn_buff);
                         return(COMMENT);
                       }

<CC>\\[0-7]{1,3}"'"    {   /* octal escape sequence */
                         unsigned int result;

                         if (sscanf(yytext+1, "%o", &result ) < 1)
                         {
                             yyerr("Invalid octal escape sequence");
                             LAST_STATE();
                             return(INVALID);
                         }
                         
                             /* error, constant is out-of-bounds */
                         if ( result > 0xff ){
                             yywarn("Escape sequence out-of-bounds");
                             result = 0;
                         }

                         lvalp->leaf->data.cval = result;
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\x{hexdigit}+"'"  {   /* hex escape sequence - ISO C */
                         unsigned int result;

                         if (sscanf(yytext+2, "%x", &result ) < 1)
                         {
                             yyerr("Invalid hex escape sequence");
                             LAST_STATE();
                             return(INVALID);
                         }

                             /* error, constant is out-of-bounds */
                         if ( result > 0xff ){
                             yywarn("Escape sequence out-of-bounds");
                             result = 0;
                         } else if (yyleng > 5){
                             yywarn("Hexadecimal escape exceeds two chars");
                             result = 0;
                         }

                         lvalp->leaf->data.cval = (char) result;
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\{digits}"'"      {  /* Bad escape sequence */
                         yywarn("Bad escape sequence in char constant");
                         lvalp->leaf->data.cval = '\0';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\n                 { /* Error unterminated char constant */
                         Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 0;
                         yywarn("Unterminated char constant");
                         lvalp->leaf->data.cval = '\0';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\n"'"             {
                         lvalp->leaf->data.cval = '\n';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\t"'"             {
                         lvalp->leaf->data.cval = '\t';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\r"'"             {
                         lvalp->leaf->data.cval = '\r';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\b"'"             {
                         lvalp->leaf->data.cval = '\b';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\f"'"             {
                         lvalp->leaf->data.cval = '\f';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\v"'"             {
                         lvalp->leaf->data.cval = '\v';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\a"'"             {
                         lvalp->leaf->data.cval = '\a';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\\n"'"            {
                         Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 1;  /* Oddity */
                         lvalp->leaf->data.cval = '\n';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>\\."'"             {
                         lvalp->leaf->data.cval = yytext[1];
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>[^']"'"            {
                         lvalp->leaf->data.cval = *yytext;
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>"'"                { /* Empty */
                         yywarn("Empty character constant");
                         lvalp->leaf->data.cval = '\0';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<CC>[^\\\n][^']+"'"    { /* Multiple characters */
                         yywarn("Invalid character constant");
                         lvalp->leaf->data.cval = '\0';
                         LAST_STATE();
                         return(CHAR_CONST);
                       }

<INITIAL>{whitespace}+ ;   /* space/tab/formfeed/vertical tab (ignore) */

<INITIAL,CMMT>\n       { Parse_TOS->yylineno++;
                         Parse_TOS->yynxtcol = 0;
                         in_preprocess = 0;
			 if (DBG) printf("ln<%d> - [[<%s><%d>]]\n\n",
				Parse_TOS->yylineno, yytext, (int) strlen(yytext));
                       }

<CMMT><<EOF>>          { 
                         yyerr("EOF reached inside comment");
                         in_preprocess = 0;
                         return(0);
                       }

<CC><<EOF>>            { 
                         yyerr("EOF reached inside character constant");
                         return(0);
                       }

<STR><<EOF>>           { 
                         yyerr("EOF reached inside string constant");
                         return(0);
                       }

.                      { /* Any unknown char is an error */
                        fprintf(stderr,
                            "Error: Line %d: Illegal Character",
                            Parse_TOS->yylineno);
                        if ((yytext[0] >= ' ') && (yytext[0] <= '~'))
                            fprintf(stderr,": '%c'\n", yytext[0]);
                        else
                            fprintf(stderr,
                                ", ASCII: %03o (octal)\n", yytext[0]);
                       }

%%

/************************************************************************
//
// yywrap() - This function is called by the lexer [yylex() or sslex()] when
//            the end-of-file (or end-of-string for sslex()) is reached.
//            It gets the next file/string ready (if any) and returns 1
//            which indicates to the lexer that there are no more files
//            remaining.  The lexer returns 0 to the parser, indicating
//            no more tokens are remaining. The parser function, yyparse(),
//            then returns 0, indicating that the parse is done.  This
//            behaviour allows a single item to be parsed to be placed
//            on the stack and parsed without the entire stack being consumed.
//
// **********************************************************************/

int yywrap(void)
{
    in_preprocess = 0;

    /* Prepare the next file if there is one but return 1 */
    /* so that yyparse returns anyway. */

    /*  get_next_file(ParseStack);  */
    return(1);
}

/***********************************************************************/
int cnt_nl(char *txt, int len)
{
  int ret = 0;

  do {
    switch (*txt++) {
      case '\n':
        ret++;
        Parse_TOS->yylineno++;
        Parse_TOS->yynxtcol = 0;
        break;

      default:
        break;
    }
  } while(--len > 0);

  return ret;
}

void
get_lineno(int caller)	/*  Process a #line directive */
{	char	*pnt;
	int	ln = 0, before = 0;

	pnt = strchr(line_buf, '#');

	if (pnt)
	{
recover:	pnt++;
		while (*pnt == ' ')
			pnt++;
		if (*pnt == 'l')	/* #line */
			pnt += 4;
	} else
	{	/* behavior observed on linux, where the string with the directive
		   sits in yytext, but isn't in line_buf, and doesn't get there.
		   some unclear interaction with flex about when YYINPUT is called.
		   recover by scanning yytext in this case */
		pnt = strchr(yytext, '#');
		if (pnt)
			goto recover;
		return;	/* not a directive */
	}

	do {	if (*pnt != '\0')
		{	if (sscanf(pnt, "%d", &ln) < 1)
			{	if (before)
				{	printf("no line number\n");
					fflush(stdout);
				}
				break;
			}
			Parse_TOS->yylineno = ln - 1;
			pnt = strchr(pnt, '"');

			if (pnt)
			{	char *pnt_end;

				pnt++;
				pnt_end = strchr(pnt, '"');

				if (pnt_end)
					*pnt_end = '\0';
				else
				{	if (before)
					{	printf("warning: no closing quote mark in <<%s>>\n", yytext);
						fflush(stdout);
					}
					break;
				}

				/* free(Parse_TOS->filename);	gjh */
				Parse_TOS->filename = emalloc(strlen(pnt)+1);
				strcpy(Parse_TOS->filename, pnt);
			}
			return;
		} else
		{	if (before)
			{	printf("%d: no opening quote mark in <<%s>>\n", caller, yytext);
				fflush(stdout);
		}	}
	} while(0);	/* so we can use break to exit this block */

	pnt = strchr(yytext, '#');	/* behavior observed on linux -- see above */
	if (pnt && !before)
	{	before = 1;
		goto recover; /* else yywarn */
	}

	yywarn("Malformed #line directive");
}

void
print_caret(char *s, int pos)
{
    char *str;
    int i = 0;

    for (str=s; *str && (i<pos); i++, str++)
        if (*str=='\t')
            fputs("\t",stderr);
        else
            fputs(" ",stderr);

    fputs("^\n",stderr);
}
 
void
yywarn(char *s)
{
    fprintf(stderr,"%s:%d: Warning - %s:\n%s",
         Parse_TOS->filename, Parse_TOS->yylineno, s, line_buf); 
    print_caret(line_buf,Parse_TOS->yycolno);
}

int
yyerr(char *s)
{
    fprintf(stderr,"%s:%d: %s:\n%s",
         Parse_TOS->filename, Parse_TOS->yylineno, s, line_buf); 
    print_caret(line_buf,Parse_TOS->yycolno);

    if (++err_cnt >= 10){
        fprintf(stderr,"Too many errors (%d detected) - quitting.\n",
                err_cnt );
        fclose(yyin);
        return(1);
    }
    return(0); 
}

int
yyerror(const char *s)
{	extern int uno, allerr;

	line_buf[MAX_TOKN_LEN-1] = '\0';	/* ensure temination */
	fprintf(stderr,"%s:%d: Error (%s) before '%s'\n%s",
		Parse_TOS->filename, Parse_TOS->yylineno,
		s, toksym(err_tok,0), line_buf); 
	print_caret(line_buf,Parse_TOS->yycolno);

	err_cnt++;

	if ((uno == 0 || allerr) && err_cnt >= 10)
	{	fprintf(stderr,"too many errors (%d detected)\n",
			err_cnt);
		fclose(yyin);
		return(1);
	}
	return(0);
}
