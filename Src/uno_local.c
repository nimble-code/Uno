/***** uno: uno_local.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#include "globals.h"
#include <unistd.h>
#include "uno_version.h"

char		*file_name  = 0;	/* uno_lts.c */
TreeStack	*ParseStack = 0;	/*            c_gram.y, lexer.l */
Stk_Item	*Parse_TOS  = 0;	/* treestk.c, c_gram.y, lexer.l, tree.c */
TreeStack	*DoneStack  = 0;	/* treestk.c */

static int	do_dflow = 1, nopre, keeptmps, show_syms, no_va=1;
static char	*preproc_info = "", *never, *master_dfn = "_uno_.dfn";
static char	*CPRE;	/* set in process_input() below */
static treenode	*parse_tree;
static char	*cpp1, *cpp2, *cpp_cmd;

int	Verbose, type_check, check_else_chains, check_compounds;
int	uno_p = 4, list_typedefs, cyclo, xrepro, viewtree;
int	localonly, nopaths = 1;
int	usecheck, allerr, allerrs, lintlike, picky, show_sharing;
int	see_static_fcts, see_extern_fcts;
char	*want = "main", *cur_file, *cur_dir = ".", *cur_path;
char	*progname = "uno:local";
char	*working_dir = (char *) 0;

context_t	*contxt = 0;

extern char	*buf_recur(treenode *);
extern char	*current_filename(void);
extern DefUse	*walk_tree(treenode *, unsigned long);
extern void	custom_exit(const char *);
extern void	dflow_reset(void);
extern void	dot_start(treenode *);
extern void	*emalloc(size_t);
extern void	explore(char *, treenode *);
extern void	find_suppress_lines(char *);
extern void	lts_start(treenode *);
extern void	memstats(void);
extern void	name_scope(context_t *, char *, int);
extern void	print_recur(treenode *, FILE *);
extern void	read_suppress(void);
extern void	set_fnm(char *);

void
Usage(char *prog)
{
	fprintf(stderr, "%s\n", VERSION);
	fprintf(stderr, "=======================\n");
	fprintf(stderr,"Usage: %s [option] file.c\n", prog);
	fprintf(stderr,"\t-V\tversion information\n");
	fprintf(stderr,"\t-s\tsymbol table information\n");

	fprintf(stderr,"\t-CPP=...\tset preprocessor\n");
	fprintf(stderr,"\t-D...\tdefine macro name (preprocessor)\n");
	fprintf(stderr,"\t-U...\tundefine macro name (preprocessor)\n");
	fprintf(stderr,"\t-I...\tdirectory to search for include files\n");
	fprintf(stderr,"\t-W...\tset working directory to store .uno files\n");

	fprintf(stderr, "\t-localonly\tdo not generate intermediate .uno file\n");
	fprintf(stderr, "\t-master x\tprepend file x to source before parsing\n");
	fprintf(stderr, "\t-nopre \tignore #include directives\n");
	fprintf(stderr, "\t-nova \tdo not redefine va_start, va_arg, and va_end\n");

	fprintf(stderr, "\t-prop x\tapply user-defined property def in file x\n");
	fprintf(stderr, "\t-allerr\treport all error paths, not a selection\n");
	fprintf(stderr, "\t-fullpaths \tgive full error paths on property violations\n");
	fprintf(stderr, "\t-exit x\tadd x to list of fcts known to have no return\n");

	fprintf(stderr, "\t-picky\tmore picky and verbose, includes -use\n");
	fprintf(stderr, "\t-use\tcomplain about redundancies\n");
	fprintf(stderr, "\t-else\tcheck else chains\n");
	fprintf(stderr, "\t-rules\tcheck some coding-style rules\n");

	fprintf(stderr, "\t-extern\tlist all fcts declared non-static\n");
	fprintf(stderr, "\t-static\tlist all fcts declared static\n");
	fprintf(stderr, "\t-typedefs\tlist all user-defined type names\n");
	fprintf(stderr, "\t-shared\tlist all global variables imported or exported\n");
	fprintf(stderr, "\t-t\tvery weak attempt at finding type mismatches\n");

	fprintf(stderr, "\t-cfg\tgenerate control flow graph (from main) in dot format\n");
	fprintf(stderr, "\t-cfg fct\tgenerate control flow graph (from fct) in dot format\n");
	fprintf(stderr, "\t-cyclo\tcompute (edges - nodes + 2) for all functions\n");
	fprintf(stderr, "\t-local\tignored (for backward compatability)\n");
	fprintf(stderr, "\t-v\tverbose (multiple -v's add verbosity)\n");
	fprintf(stderr, "\t-w\tdo not remove temporary files (debugging)\n");
	exit(1);
}

void
add_never(FILE *fo)
{	FILE *fd;
	char buf[1024];

	if ((fd = fopen(never, "r")) == NULL)
	{	fprintf(stderr, "uno: cannot open %s\n", never);
		return;
	}

	fprintf(fo, "/** property from %s: **/\n", never);
	fprintf(fo, "#undef ANY\n");
	fprintf(fo, "#undef NONE\n");
	fprintf(fo, "#undef DEF\n");
	fprintf(fo, "#undef USE\n");
	fprintf(fo, "#undef FCALL\n");
	fprintf(fo, "#undef REF0\n");
	fprintf(fo, "#undef REF1\n");
	fprintf(fo, "#undef REF2\n");
	fprintf(fo, "#undef DEREF\n");
	fprintf(fo, "#undef ALIAS\n");
	fprintf(fo, "#undef ARRAY_DECL\n");
	fprintf(fo, "#undef HIDE\n");
	fprintf(fo, "#undef DECL\n");
	fprintf(fo, "#undef USEafterdef\n");
	fprintf(fo, "#undef USEbeforedef\n");
	fprintf(fo, "#undef UNO_CONST\n");
	fprintf(fo, "#undef PARAM\n");
	fprintf(fo, "#undef IN_SIZEOF\n");
	fprintf(fo, "#undef IS_PTR\n");
	fprintf(fo, "#undef NOT_SCALAR\n");
	fprintf(fo, "#undef INCOND\n");

	fprintf(fo, "#define NONE	%d\n", NONE);
	fprintf(fo, "#define ANY	%d\n", ANY);
	fprintf(fo, "#define DEF	%d\n", DEF);
	fprintf(fo, "#define FCALL	%d\n", FCALL);
	fprintf(fo, "#define USE	%d\n", USE);
	fprintf(fo, "#define REF0	%d\n", REF0);
	fprintf(fo, "#define REF1	%d\n", REF1);
	fprintf(fo, "#define REF2	%d\n", REF2);
	fprintf(fo, "#define DEREF	%d\n", DEREF);
	fprintf(fo, "#define ALIAS	%d\n", ALIAS);
	fprintf(fo, "#define ARRAY_DECL	%d\n", ARRAY_DECL);
	fprintf(fo, "#define HIDE	%d\n", HIDE);
	fprintf(fo, "#define DECL	%d\n", DECL);
	fprintf(fo, "#define USEafterdef	%d\n", USEafterdef);
	fprintf(fo, "#define USEbeforedef	%d\n", USEbeforedef);
	fprintf(fo, "#define UNO_CONST	%d\n", UNO_CONST);
	fprintf(fo, "#define PARAM	%d\n", PARAM);
	fprintf(fo, "#define IN_SIZEOF	%d\n", IN_SIZEOF);
	fprintf(fo, "#define IS_PTR	%d\n", IS_PTR);
	fprintf(fo, "#define INCOND	%d\n", INCOND);
	fprintf(fo, "#define NOT_SCALAR	(REF0|REF1|REF2|ALIAS|DEREF)\n");
	fprintf(fo, "#line 1 \"%s\"\n", never);

	while (fgets(buf, 1024, fd))
		fprintf(fo, "%s", buf);
	fclose(fd);
}

void
add_pieces(FILE *fp, char *f)
{	FILE *x;
	char buf[1024];

	if (!nopre) fprintf(fp, "#define UnoType typedef int\n");

	fprintf(fp, "typedef int __builtin_va_list;\n"); /* gcc-ism */
	fprintf(fp, "typedef int __w64;\n"); /* cl-ism */
	fprintf(fp, "#define __builtin_va_start(v,l)\n");
	fprintf(fp, "#define __builtin_va_arg(v,l)	(l)0\n");
	fprintf(fp, "#define __builtin_va_end(v)\n");

	if (no_va)
	{	fprintf(fp, "#undef va_start\n");
		fprintf(fp, "#define va_start(v,l)\n");
		fprintf(fp, "#undef va_arg\n");
		fprintf(fp, "#define va_arg(v,l)\t(l)0\n");
		fprintf(fp, "#undef va_end\n");
		fprintf(fp, "#define va_end(v)\n");
	}
	fprintf(fp, "#define UNO\n");
	fprintf(fp, "#define __builtin_offsetof(TYPE, MEMBER) ((size_t) &((TYPE *)0)->MEMBER)\n");

	if ((x = fopen(master_dfn, "r")) != NULL)
	{	fprintf(fp, "/* from %s */\n", master_dfn);
		while (fgets(buf, sizeof(buf), x))
		{
			if (nopre
			&&  strncmp(buf, "UnoType", strlen("UnoType")) == 0)
				fprintf(fp, "typedef int %s", &buf[strlen("UnoType")+1]);
			else
				fprintf(fp, "%s", buf);
		}
		fclose(x);
		fprintf(fp, "/* end */\n");
	}

	if (!f) return;
#if 1
	fprintf(fp, "#include \"%s\"\n", cur_file);
#else
	/* fails to find the file, at least in cygwin */
	fprintf(fp, "#include \"%s/%s\"\n", cur_dir, cur_file);
#endif

	if (never) add_never(fp);
}

/*
   Split pathname into directory (possibly empty) and filename
   sets global var cur_path to a copy of f
   sets global var cur_dir  to directory component of f (including
   the trailing directory separator), and
   sets global var cur_file to point into cur_path at filename 
*/

static void
split_filename(const char *f)
{	char *last_slash;

	cur_path = (char *) emalloc(strlen (f) + 1);
	strcpy(cur_path, f);

	last_slash = strrchr(f, '/');
#ifdef PC
	if (!last_slash)
	{	last_slash = strrchr(f, '\\');
		if (!last_slash)
			last_slash = strrchr(f, ':');
	}
#endif
	if (!last_slash)
	{	cur_dir =".";  /* to make sure we get a valid pathname */
		cur_file = cur_path;
	} else
	{	size_t dirlen = last_slash - f;
		cur_dir = (char *) emalloc(dirlen + 1);
		strncpy(cur_dir, f, dirlen);    /* cur_dir has a zero afterward */
		cur_file = &cur_path[dirlen+1];
	}
	if (Verbose > 1) fprintf(stderr, "FILE %s -> '%s/%s'\n", f, cur_dir, cur_file);
}

void
clean_tmps(void)
{
	if (!keeptmps)
	{	unlink(cpp2);
		unlink(cpp1);
	}
}

void
process_input(char *f)
{	FILE *fp;

	if (!CPRE)		/* if not set by the user on the command line */
	{
#ifdef CPP
		CPRE = CPP;	/* optional default set at uno-compilation time */
#else
		CPRE = "gcc -E";
#endif
	}

	if (!f || strstr(f, ".c") == NULL)
	{	if (f) printf("saw: %s\n", f);
		Usage("uno_local");
	}

	split_filename(f);

	if (working_dir != NULL)
	{	cpp2 = (char *) emalloc(strlen(working_dir)+1+2+strlen(cur_file)+1);
		sprintf(cpp2, "%s/__%s", working_dir, cur_file);

		cpp1 = (char *) emalloc(strlen(working_dir)+1+1+strlen(cur_file)+1);
		sprintf(cpp1, "%s/_%s", working_dir, cur_file);
	} else
	{	cpp2 = (char *) emalloc(strlen(cur_dir)+3+strlen(cur_file)+1);
		sprintf(cpp2, "%s/__%s", cur_dir, cur_file);

		cpp1 = (char *) emalloc(strlen(cur_dir)+2+strlen(cur_file)+1);
		sprintf(cpp1, "%s/_%s", cur_dir, cur_file);
	}

	cpp_cmd = (char *) emalloc(sizeof(char)*
			(strlen(CPRE)+
			(preproc_info?strlen(preproc_info):0)+
			strlen(f)+
			strlen(cpp2)+
			strlen("-I. ")+		/* just in case */
			32 ) );

	if (nopre)
	{	FILE *f1, *f2;
		char *x, buf[4096];

		if ((f1 = fopen(f, "r")) == NULL
		||  (f2 = fopen(cpp2, "w")) == NULL)
		{	fprintf(stderr, "uno: no file '%s', or cannot create '%s'\n", f, cpp2);
			exit(1);
		}
		add_pieces(f2, (char *) 0);
		fprintf(f2, "#line 1 \"%s\"\n", f);
		while (fgets(buf, sizeof(buf), f1))
		{	for (x = buf; *x == ' ' || *x == '\t'; x++)
				;
			if (strncmp(x, "#include", strlen("#include")) != 0) /* not an include */
				fprintf(f2, "%s", buf);
			else
				fprintf(f2, "\n");	/* maintain line count */
		}
		if (never) add_never(f2);

		fclose(f1);
		fclose(f2);
	} else
	{	if ((fp = fopen(cpp2, "w")) == NULL)
		{	fprintf(stderr, "uno: cannot create '%s'\n", cpp2);
			exit(1);
		}
		add_pieces(fp, f);
		fclose(fp);
	}

	if (working_dir != NULL)
		sprintf(cpp_cmd, "%s %s -I. %s >%s",
		CPRE, preproc_info?preproc_info:"", cpp2, cpp1);
	else
		sprintf(cpp_cmd, "%s %s %s >%s",
		CPRE, preproc_info?preproc_info:"", cpp2, cpp1);

	if (Verbose>1) printf("%s\n", cpp_cmd);

	if (system(cpp_cmd) != 0)
	{	fprintf(stderr, "preprocessing command '%s' failed\n", cpp_cmd);
		goto done;
	}

	if ((fp = fopen(cpp1, "r")) == NULL)
	{	fprintf(stderr, "uno: cannot open '%s'\n", cpp2);
		goto done;
	}

	init_nmetab();
	ParseStack = new_treestk();
	DoneStack  = new_treestk();
	contxt     = new_context();
	ParseStack->contxt = contxt;
	handle_new_file(ParseStack, fp, file_name);
	enter_scope(contxt);
	tree_parse(ParseStack, 0);	/* gram.y */
	name_scope(ParseStack->contxt, current_filename(), NONE_T);
	parse_tree = (top_of_stack(DoneStack))->parse_tree;
	fclose(fp);

	if (!parse_tree)
		fprintf(stderr, "uno: no parsetree for %s\n", f);
	else if (do_dflow)
	{	dflow_reset();
		walk_tree(parse_tree, 0);	/* dflow.c */

		if (viewtree)
		{	if (xrepro)
			{	print_recur(parse_tree, stdout);
			}
		} else
		{	if (xrepro)
			{	explore(f, parse_tree);
	}	}	}
done:
	clean_tmps();

	exit_scope(contxt);
}

int
main(int argc, char **argv)
{	char *arg = NULL;

	argc--; argv++;
	file_name = "-";
	while (argc-- > 0)
	{	arg = *argv++;

		if (strcmp(arg, "-allerr") == 0)
		{	allerr = allerrs = 1;
			continue;
		} else if (strcmp(arg, "-c") == 0)
		{	continue;	/* ignore */
		} else if (strcmp(arg, "-cfg") == 0)
		{	uno_p = 2;
			if (argc > 1 && *(*argv) != '-')
			{	want = *argv++;
			}
			continue;
		} else if (strcmp(arg, "-cyclo") == 0)
		{	cyclo = 1;
			continue;
		} else if (strcmp(arg, "-localonly") == 0)
		{	localonly = 1;
			continue;
		} else if (strcmp(arg, "-picky") == 0)
		{	lintlike = picky = 1;
			usecheck = 1;
			continue;
		} else if (strcmp(arg, "-fullpaths") == 0)
		{	nopaths = 1 - nopaths;
			continue;
		} else if (strcmp(arg, "-use") == 0)
		{	usecheck = 1;
			continue;
		} else if (strcmp(arg, "-nova") == 0)
		{	no_va = 0;
			continue;
		} else if (strcmp(arg, "-nopre") == 0)
		{	nopre = 1;
			continue;
		} else if (strcmp(arg, "-local") == 0)
		{	continue;	/* backward compatibility with modex */
		} else if (strcmp(arg, "-prop") == 0)
		{	never = (char *) emalloc(strlen(*argv)+1);
			strcpy(never, *argv);
			argc--; argv++;
			continue;
		} else if (strcmp(arg, "-static") == 0)
		{	see_static_fcts = 1;
			continue;
		} else if (strcmp(arg, "-shared") == 0)
		{	show_sharing = localonly = 1;
			continue;
		} else if (strcmp(arg, "-typedefs") == 0)
		{	list_typedefs = 1;
			continue;
		} else if (strcmp(arg, "-extern") == 0)
		{	see_extern_fcts = 1;
			continue;
		} else if (strcmp(arg, "-else") == 0)
		{	check_else_chains = 1;
			continue;
		} else if (strcmp(arg, "-compound") == 0)
		{	check_compounds = 1;
			continue;
		} else if (strcmp(arg, "-exit") == 0)
		{	custom_exit((const char *) *argv);
			argc--; argv++;
			continue;
		} else if (strcmp(arg, "-master") == 0)
		{	master_dfn = (char *) emalloc(strlen(*argv)+1);
			strcpy(master_dfn, *argv);
			argc--; argv++;
			continue;
		} else if (strncmp(arg, "-W", 2) == 0 && strlen(arg) > 2)
		{	working_dir = (char *) emalloc(strlen(arg)+1-2);
			strcpy(working_dir, &arg[2]);
			continue;
		} else if (strcmp(arg, "-V") == 0)
		{	printf("%s\n", VERSION);
			exit(0);
		} else if (strcmp(arg, "-view") == 0)	/* debugging mode */
		{	viewtree++;
			continue;
		} else if (strncmp(arg, "-v", 2) == 0)
		{	Verbose++;	/* -v or e.g. -verbose */
			continue;
		} else if (strncmp(arg, "-w", 2) == 0)
		{	keeptmps = 1;	/* intermediate files */
			continue;
		} else if (strncmp(arg, "-rules", 6) == 0)
		{	xrepro = 1;
			continue;
		} else if (strcmp(arg, "-s") == 0)
		{	show_syms = 1;
			continue;
		} else if (strcmp(arg, "-t") == 0)
		{	type_check = 1;
			continue;
		}

		if (strncmp(arg, "-CPP=", strlen("-CPP=")) == 0)
		{	CPRE = arg+strlen("-CPP=");
			continue;
		}

		if (strncmp(arg, "-U", 2) == 0
		||  strncmp(arg, "-D", 2) == 0
		||  strncmp(arg, "-I", 2) == 0)
		{	if (!preproc_info)
			{	preproc_info = (char *) emalloc(strlen(arg)+1);
				strcpy(preproc_info, arg);
			} else
			{	char *pp = (char *) emalloc(strlen(arg)+strlen(preproc_info)+1+1+2);
				strcpy(pp, preproc_info);
				strcat(pp, " \""); /* quote all but the first one */
				strcat(pp, arg);
				strcat(pp, "\"");
				preproc_info = pp;
			}
			continue;
		}
		break;
	}

	custom_exit("exit");		/* fcts known not to return */
	custom_exit("fatal");
	custom_exit("panic");

	if (!arg) Usage("uno");

	read_suppress();	/* read an optional uno_suppress file */
	
	for (file_name = arg; file_name && argc >= 0; file_name = *argv++, argc--)
	{	if (Verbose)
			printf("uno: %s\n", file_name);
		set_fnm(file_name);

		find_suppress_lines(file_name);

		process_input(file_name);	/* parses file */

		if (parse_tree
		&&  !see_extern_fcts
		&&  !see_static_fcts)
			lts_start(parse_tree);		/* uno_lts.c   */

		if (show_syms)
			show_symtab(contxt->syms, stdout);

		if (Verbose)
			memstats();

		free_context(contxt);	/* done with this file */

		while (!is_empty(ParseStack))
			delete_stk_item(pop(ParseStack));

		if (Verbose>1) printf("parsestack\n");

		while (!is_empty(DoneStack))
			delete_stk_item(Parse_TOS = pop(DoneStack));
		if (Verbose>1) printf("donestack\n");

		Parse_TOS  = (Stk_Item  *) 0;
		DoneStack  = (TreeStack *) 0;
		parse_tree = (treenode *) 0;
		ParseStack = (TreeStack *) 0;
	}
	if (Verbose>1) printf("done\n");

	return 0;
}

char *
x_stmnt(treenode *n)
{
	return buf_recur(n);
}
