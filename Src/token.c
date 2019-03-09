/***** uno: token.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shaun Flisakowski, Dec 24, 1994 */

#include    <stdio.h>
#include    <string.h>
#include    <stdlib.h>
#include    <assert.h>
#include    "c_gram.h"

char *
toksym(int tok, int white)
{
    switch (tok) {
    case IDENT:		return("Identifier");
    case TYPEDEF_NAME:	return("Typedef Name");
    case STRING:	return("String Constant");
    case COMMENT:	return("Comment");
    case CHAR_CONST:	return("Character Constant");
    case INUM:		return("Integer Constant");
    case RNUM:		return("Real Constant");

    /* Regular keywords */
    case AUTO:
        if (white)
          return("auto ");
        else
          return("auto");

    case BREAK:
        return("break");

    case CASE:
        if (white)
          return("case ");
        else
          return("case");

    case CHAR:
        if (white)
          return("char ");
        else
          return("char");

    case CONST:
        if (white)
          return("const ");
        else
          return("const");

    case CONT:
        return("continue");

    case DEFLT:
        return("default");

    case DO:
        if (white)
          return("do ");
        else
          return("do");

    case DOUBLE:
        if (white)
          return("double ");
        else
          return("double");

    case ELSE:
        return("else");

    case ENUM:
        if (white)
          return("enum ");
        else
          return("enum");

    case EXTRN:
        if (white)
          return("extern ");
        else
          return("extern");

    case FLOAT:
        if (white)
          return("float ");
        else
          return("float");

    case FOR:
        if (white)
          return("for ");
        else
          return("for");

    case GOTO:
        if (white)
          return("goto ");
        else
          return("goto");

    case IF:
        if (white)
          return("if ");
        else
          return("if");

    case INT:
        if (white)
          return("int ");
        else
          return("int");

    case LONG:
        if (white)
          return("long ");
        else
          return("long");

    case REGISTR:
        if (white)
          return("register ");
        else
          return("register");

    case RETURN:
        if (white)
          return("return ");
        else
          return("return");

    case SHORT:
        if (white)
          return("short ");
        else
          return("short");

    case SGNED:
        if (white)
          return("signed ");
        else
          return("signed");

    case SIZEOF:
        return("sizeof");

    case STATIC:
        if (white)
          return("static ");
        else
          return("static");

    case STRUCT:
        if (white)
          return("struct ");
        else
          return("struct");

    case SWITCH:
        if (white)
          return("switch ");
        else
          return("switch");

    case TYPEDEF:
        if (white)
          return("typedef ");
        else
          return("typedef");

    case UNION:
        if (white)
          return("union ");
        else
          return("union");

    case UNSGNED:
        if (white)
          return("unsigned ");
        else
          return("unsigned");

    case VOID:
        if (white)
          return("void ");
        else
          return("void");

    case VOLATILE:
        if (white)
          return("volatile ");
        else
          return("volatile");

    case WHILE:
        if (white)
          return("while ");
        else
          return("while");

    case PLUS:		return("+");
    case MINUS:		return("-");
    case STAR:		return("*");
    case DIV:		return("/");
    case MOD:		return("%");
    case EQ:		return("=");
    case PLUS_EQ:	return("+=");
    case MINUS_EQ:	return("-=");
    case STAR_EQ:	return("*=");
    case DIV_EQ:	return("/=");
    case MOD_EQ:	return("%=");
    case NOT:		return("!");
    case AND:		return("&&");
    case OR:		return("||");
    case B_NOT:		return("~");
    case B_AND:		return("&");
    case B_OR:		return("|");
    case B_XOR:		return("^");
    case B_NOT_EQ:	return("~=");
    case B_AND_EQ:	return("&=");
    case B_OR_EQ:	return("|=");
    case B_XOR_EQ:	return("^=");
    case L_SHIFT:	return("<<");
    case R_SHIFT:	return(">>");
    case L_SHIFT_EQ:	return("<<=");
    case R_SHIFT_EQ:	return(">>=");
    case EQUAL:		return("==");
    case LESS:		return("<");
    case LESS_EQ:	return("<=");
    case GRTR:		return(">");
    case GRTR_EQ:	return(">=");
    case NOT_EQ:	return("!=");
    case ASSIGN:	return("Invalid (assignment)");
    case INCR:		return("++");
    case DECR:		return("--");
    case LPAREN:	return("(");
    case RPAREN:	return(")");
    case LBRCKT:	return("[");
    case RBRCKT:	return("]");
    case LBRACE:	return("{");
    case RBRACE:	return("}");
    case DOT:		return(".");
    case ARROW:		return("->");
    case QUESTMARK:	return("?");
    case COLON:		return(":");
    case SEMICOLON:	return(";");
    case COMMA:		return(",");
    case ELLIPSIS:	return("...");
    case LB_SIGN:	return("#");
    case DOUB_LB_SIGN:	return("##");  
    case BACKQUOTE:	return("`");
    case AT:	return("@");
    case DOLLAR:	return("$");
    default:
    case INVALID:	return("?");
    }
}
