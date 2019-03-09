/***** uno: uno_global.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dtags.h"
#include "uno_global.h"
#include "uno_version.h"

static int	debug = 0;
int	longtrace;
int	verbose;
static char	*want = "main";

static Fct	*fcts = (Fct *) 0;
static PlaceName *fields = (PlaceName *) 0;
static Sym	*globuse = (Sym *) 0;
static char	*p_start = "main";
static char	*p_stop  = "exit";
static int	p_query = 0;
static int	reverse = 0;
static int	usecheck = 0;

static Fct	*find_fct(char *);
static void	fcts_reset(void);
static void	gen_fct(FILE *, Fct *);
static void	gen_fcts(FILE *);
static void	struct_check(void);
static void	uno_load(char *);
static void	unused_fcts(void);
static void	handle_glb(char *, char *);

extern void	run_check(void);
extern void	add_fct(char *);
extern void	handle_fct(char *);
extern void	add_call(char *, char *);

void *
emalloc(size_t n)
{	char *s;

	s = (char *) malloc(n);
	if (!s)
	{	fprintf(stderr, "uno:global: out of memory\n");
		exit(1);
	}
	memset(s, 0, n);
	return (void *) s;
}

static void
unostats(void)
{	Sym *r;
	Fct *f;
	int cnt = 0, d = 0, u = 0, c = 0, x = 0;

	for (f = fcts; f; f = f->nxt)
	{	cnt++;
		for (r = f->defs;  r; r = r->nxt)
			d++;
		for (r = f->uses;  r; r = r->nxt)
			u++;
		for (r = f->deref;  r; r = r->nxt)
			x++;
		for (r = f->calls; r; r = r->nxt)
			c++;
	}
	printf("%6d	function declarations\n", cnt-1);
	printf("%6d	function calls\n", c);
	printf("%6d	global variable definitions\n", d);
	printf("%6d	global variable uses\n", u);
	printf("%6d	global variable dereferences\n", x);

	cnt = 0;
	for (r = globuse; r; r = r->nxt)
		if (!find_fct(r->s))
			cnt++;
	printf("%6d	global ptr variables\n", cnt);
}

static void
gen_fct(FILE *fd, Fct *g)
{	Sym *r;
	Fct *f;

	if (!g || g->visited) return;
	g->visited = 1;

	fprintf(fd, "N%s [label=\"%s:%d\"];\n",
		g->fnm, g->fnm, g->n->line);

	if (reverse)
	{	for (f = fcts; f; f = f->nxt)
		for (r = f->calls; r; r = r->nxt)
			if (strcmp(r->s, g->fnm) == 0)
			{	fprintf(fd, "N%s -> N%s;\n", f->fnm, g->fnm);
				gen_fct(fd, f);
			}
	} else
	{	for (r = g->calls; r; r = r->nxt)
		{	if (!(r->bits & HIDE))
				fprintf(fd, "N%s -> N%s;\n", g->fnm, r->s);
			gen_fct(fd, find_fct(r->s));
	}	}
}

static void
gen_fcts(FILE *fd)
{
	fprintf(fd, "digraph dodot {\n\tratio=auto;\n");
	fcts_reset();
	gen_fct(fd, find_fct(want));
	fprintf(fd, "}\n");
}

static void
all_fcg(FILE *fd)
{	Fct *g;
	Sym *r;

	fprintf(fd, "digraph dodot {\n\tratio=auto;\n");
	for (g = fcts; g; g = g->nxt)
	{	fprintf(fd, "N%s [label=\"%s:%d\"];\n",
			g->fnm, g->fnm, g->n->line);

		for (r = g->calls; r; r = r->nxt)
			fprintf(fd, "N%s -> N%s;\n",
				g->fnm, r->s);
	}
	fprintf(fd, "}\n");
}

static void
glob_mark(Place *n, char *s, int bits)
{	Sym *r;

	for (r = globuse; r; r = r->nxt)
		if (strcmp(r->s, s) == 0)
		{	r->bits |= bits;
			break;
		}
	if (!r)
	{	r = (Sym *) emalloc(sizeof(Sym));
		r->s = s;
		r->bits = bits;
		r->n = n;
		r->nxt = globuse;
		globuse = r;
	}
}

static void
glob_check(void)
{	Sym *r;

	for (r = globuse; r; r = r->nxt)
	{
		if (find_fct(r->s))
			continue;	/* fct mistaken for a var */

		switch (r->bits) {	/* no match if ALIAS bits are set */
		case 0:	printf("uno:global: %s:%d '%s' never used or set\n",
				r->n->fnm, r->n->line, r->s);
			break;
		case USE:
			if (usecheck)
			printf("uno:global: %s:%d '%s' used but never set\n",
				r->n->fnm, r->n->line, r->s);
			break;
		case DEF:
			if (usecheck)
			printf("uno:global: %s:%d '%s' set but never used\n",
				r->n->fnm, r->n->line, r->s);
			break;
		}
	}
}

int
path_query(Fct *g, Fct *h)	/* from, to */
{	Sym *r;
	Fct *f;
	int found;
	
	if (!g || g->visited) return 0;
	g->visited = 1;

	found = 0;
	for (r = g->calls; r; r = r->nxt)
	{	f = find_fct(r->s);

		if (f == h)
			found = 1;
		else
			found = path_query(g, f);

		if (found)
		{	fprintf(stdout, "N%s -> N%s;\n", g->fnm, r->s);
			break;
		}
#if 0
		fprintf(stdout, "N%s [label=\"%s:%d\"];\n",
				g->fnm, g->fnm, g->n->line);
#endif
	}

	return found;
}

int
main(int argc, char **argv)
{	int fcg = 0;

	argc--;
	argv++;

	while (argc-- > 0)
	{	if (strcmp(*argv, "-V") == 0)
		{	printf("%s\n", VERSION);
			exit(0);
		}
		if (strcmp(*argv, "-v") == 0)
		{	verbose = 1;
			printf("%s\n", VERSION);
		} else if (strcmp(*argv, "-fcg") == 0
		|| strcmp(*argv, "-f") == 0)
			fcg = 1;
		else if (strcmp(*argv, "-use") == 0
		|| strcmp(*argv, "-u") == 0)
			usecheck = 1;
		else if (strcmp(*argv, "-l") == 0
		     ||  strcmp(*argv, "-1") == 0)
			longtrace = 1;
		else if (strcmp(*argv, "-r") == 0)
			reverse = 1;
		else if (strcmp(*argv, "-p") == 0)
		{	argv++; argc--;
			p_start = *argv;
			p_query = 1;
		} else if (strcmp(*argv, "-s") == 0)
		{	argv++; argc--;
			p_stop = *argv;
			p_query = 1;
		} else if (strcmp(*argv, "-a") == 0)
		{	argv++; argc--;
			want = *argv;
		} else if (strstr(*argv, ".uno"))
			uno_load(*argv);
		else
		{	fprintf(stderr, "uno_global: saw: %s\n", *argv);
			fprintf(stderr, "usage: uno:global [-a name] [-f] [-l] [-r] [-u] [-v] *.uno\n");
			fprintf(stderr, "	-a name	target fct name (default 'main')\n");
			fprintf(stderr, "	-f[cg]	function call graph (dot format) (-v -fcg all fcts)\n");
			fprintf(stderr, "	-l	more detailed error traces\n");
			fprintf(stderr, "	-r	reverse fcg from target fct back to main\n");

			fprintf(stderr, "	-p name	path query - set start of path (default is main)\n");
			fprintf(stderr, "	-s name	path query - set end   of path (default is exit)\n");

			fprintf(stderr, "	-u[se]	complain about redundancies\n");
			fprintf(stderr, "	-v	verbose, print some stats\n");
			exit(1);
		}
		argv++;
	}
	if (fcg)
	{	if (verbose)
			all_fcg(stdout);
		else
			gen_fcts(stdout);
		exit(0);
	}

	if (p_query)
	{	fprintf(stdout, "digraph dodot {\n\tratio=auto;\n");
		fcts_reset();
		path_query(find_fct(p_start), find_fct(p_stop));
		fprintf(stdout, "}\n");
		exit(0);
	}

	if (usecheck)
	{	struct_check();	/* unused fields in structures */
		glob_check();	/* redundant vars, used but not set, set but not used */
		unused_fcts();	/* consistency of use of fct return values */
	}
	run_check();	/* uno_fcts.c */

	if (verbose) unostats();

	return 0;
}

static void
new_fct(Place *n, char *nf, int is_static_fct)
{	Fct *f;

	for (f = fcts; f; f = f->nxt)
		if (strcmp(f->fnm, nf) == 0)
		{	if (f->n->line == n->line
			&&  (strstr(f->n->fnm, n->fnm)
			||   strstr(n->fnm, f->n->fnm)))
				break;	/* probably from same source */

			if (!f->is_static || !is_static_fct)
			{	fprintf(stderr, "uno:global: fct '%s' appears twice\n", nf);
					fprintf(stderr, "	old: %s:%d%s\n",
				f->n->fnm, f->n->line, f->is_static?" (static)":"");
				fprintf(stderr, "	new: %s:%d%s (ignored)\n",
					n->fnm, n->line, is_static_fct?" (static)":"");
			}
			break;
		}

	if (!f)
	{	f = (Fct *) emalloc(sizeof(Fct));
		f->fnm = nf;
		f->n = n;
		f->is_static = is_static_fct;
		f->nxt = fcts;
		fcts = f;
	}
}

static Fct *
find_fct(char *nf)
{	Fct *f = (Fct *) 0;

	if (!nf) return f;

	for (f = fcts; f; f = f->nxt)
		if (strcmp(f->fnm, nf) == 0)
			break;

	if (!f)
	{	if (strcmp(nf, "_global_") == 0)
		{	Place *n;
			n = (Place *) emalloc(sizeof(Place));
			n->fnm = "_global_";
			new_fct(n, nf, 0);
			f = fcts;

			add_fct(nf);

		} else if (debug)
			fprintf(stderr, "uno:global: unknown fct %s\n", nf);
	}
	return f;
}

extern void find_roots(void);

static void
retval(char *s, int status)
{	Fct *f;

	if (s)
	if ((f = find_fct(s)) != NULL)	/* assign f */
		f->rval = status;
}

static void
glob_def(Place *n, char *nf, char *s)
{	Sym *r;
	Fct *f;

	if (!(f = find_fct(nf))) return;

	r = (Sym *) emalloc(sizeof(Sym));
	r->s = s;
	r->n = n;
	r->nxt = f->defs;
	f->defs = r;
}

static int	special = 1000;
static char	g_buf[256];

static void
build_glob(Sym *r)
{
	if (!r) return;
	build_glob(r->nxt);
	
	sprintf(g_buf, ">%d>", special++);
	handle_fct(g_buf);

	sprintf(g_buf, "[G\t%s\t%s %d]", r->s, r->n->fnm, r->n->line);	/* G: DEF|DCL */
	handle_fct(g_buf);
}

void	/* called from uno_fcts.c */
add_glob_defs(void)
{	Fct *f;

	if (!(f = find_fct("_global_"))) return;

	handle_fct(": _global_	0");
	build_glob(f->defs);

	if (!(f = find_fct(want)))
	{	printf("uno:global: no fct '%s' found, cannot do global analysis\n", want);
		find_roots();
		return;
	}

	sprintf(g_buf, ">%d>", special++);
	handle_fct(g_buf);
	sprintf(g_buf, "[C\t%s\t%s %d]", want, f->n->fnm, f->n->line);
	handle_fct(g_buf);
}

static void
loc_fcall(Place *n, char *nf, char *s, int bits)
{	Sym *r;
	Fct *f;

	if (!(f = find_fct(nf))) return;

	r = (Sym *) emalloc(sizeof(Sym));
	r->s = s;
	r->n = n;
	r->bits = bits;
	r->nxt = f->calls;
	f->calls = r;

	if (bits & HIDE)
	{	f = find_fct(s);
		if (f) f->special |= HIDE;
	}

	add_call(nf, s);	/* uno_fcts.c */
}

static void
glob_use(Place *n, char *nf, char *s)
{	Sym *r;
	Fct *f;

	if (!(f = find_fct(nf))) return;

	r = (Sym *) emalloc(sizeof(Sym));
	r->s = s;
	r->n = n;
	r->nxt = f->uses;
	f->uses = r;
}

static void
glob_deref(Place *n, char *nf, char *s)
{	Sym *r;
	Fct *f;

	if (!(f = find_fct(nf))) return;

	r = (Sym *) emalloc(sizeof(Sym));
	r->s = s;
	r->n = n;
	r->nxt = f->deref;
	f->deref = r;
}

static char *
mknm(char *s)
{	char *n;

	n = (char *) emalloc(strlen(s)+1);
	strcpy(n, s);
	return n;
}

static void
struct_flds(Place *n, char *nm, int used)
{	PlaceName *p;

	for (p = fields; p; p = p->nxt)
		if (p->n->line == n->line
		&&  strcmp(p->n->fnm, n->fnm) == 0
		&&  strcmp(p->s, nm) == 0)
		{	p->used |= used;
			break;
		}
	if (!p)
	{	p = (PlaceName *) emalloc(sizeof(PlaceName));
		p->n = n;
		p->s = nm;
		p->used = used;
		p->nxt = fields;
		fields = p;
	}
}

static void
struct_check(void)
{	PlaceName *p;

	for (p = fields; p; p = p->nxt)
		if (p->used == 0
		&&  strncmp(p->s, "unused", strlen("unused")) != 0)
			printf("uno:global: %s:%d possibly redundant field '%s'\n",
				p->n->fnm, p->n->line, p->s);
}

static Sym *indirects;

static void
get_indirect(char *s, int b)
{	Sym *p;

	p = (Sym *) emalloc(sizeof(Sym));
	p->s = (char *) emalloc(strlen(s)+1);
	strcpy(p->s, s);
	p->bits = b;
	p->nxt = indirects;
	indirects = p;
}

extern int
indirect_calls(char *s)
{	Sym *p;

	for (p = indirects; p; p = p->nxt)
		if (strcmp(p->s, s) == 0)
			return 1;
	return 0;
}

static void
handle_glb(char *buf, char *f)
{	static	char *curfct = (char *) 0;
	char	Code, Name[512], Filename[512], *nm = NULL, *other;
	Place	*n = (Place *) 0;
	int	Linenr, ostat;

	memset(Name, 0, sizeof(Name));
	memset(Filename, 0, sizeof(Filename));

	if (sscanf(buf, "%c\t%s\t%s\t%d\n",
		&Code, Name, Filename, &Linenr) == 4)
	{
		if (Code != 'q')
		{	n = (Place *) emalloc(sizeof(Place));
			n->fnm = mknm(Filename);
			n->line = Linenr;
			nm = mknm(Name);
		}

		switch (Code) {
		case 'F': curfct = nm; new_fct(n, nm, 0); add_fct(nm); break; /* extern function */
		case 'f': curfct = nm; new_fct(n, nm, 1); add_fct(nm); break; /* static function */
		case 'X': retval(curfct, Linenr); break;	 /* return value status of last function */

		case 'D': glob_def(n, curfct, nm); break;	/* global is defined in fct */
		case 'U': glob_use(n, curfct, nm); break;	/* poss useb4def   in fct */
		case 'R': glob_deref(n, curfct, nm); break;	/* poss derefb4def in fct */

		case 'C': loc_fcall(n, curfct, nm, DEF); break;	/* fct call made, retval used */
		case 'c': loc_fcall(n, curfct, nm, USE); break;	/* fct call made, retval not used */
		case 'b': loc_fcall(n, curfct, nm, USE|DEF); break;

		case 'h': loc_fcall(n, curfct, nm, DEF|HIDE); break; /* probably can't happen */
		case 'i': loc_fcall(n, curfct, nm, USE|HIDE); break; /* can't tell when or how called */
		case 'j': loc_fcall(n, curfct, nm, USE|DEF|HIDE); break;

		case 'G': glob_def(n, "_global_", nm); break;	 /* global defined in declaration */
		case 'a': glob_mark(n, nm, ALIAS); break;	/* global var's address taken at least once */
		case 'v': glob_mark(n, nm, 0); break;		/* global var   declared but not used */
		case 's': glob_mark(n, nm, DEF); break;		/* global var   set  at least once    */
		case 'u': glob_mark(n, nm, USE); break;		/* global var   used at least once    */
		case 't': glob_mark(n, nm, DEF|USE); break;	/* global var   set and used at least once  */

		case 'y': struct_flds(n, nm, 1); break;	/* report only matching results across all files */
		case 'z': struct_flds(n, nm, 0); break;	/* report only matching results across all files */

		case 'p': /* fct 'Name' could call fct 'Filename' via a fct pointer */
			other = n->fnm; n->fnm = "---"; ostat = n->line; n->line = 0;
			loc_fcall(n, nm, other, ostat);
			break;

		case 'q': get_indirect(Name, Linenr); break;

		default : fprintf(stderr, "uno:global: bad code (%c) in %s\n", Code, f); break;
	}	}
}

static void
uno_load(char *f)
{	FILE	*fd;
	char	buf[2048];

	if (0) fprintf(stderr, "uno:global: load %s\n", f);

	if ((fd = fopen(f, "r")) == NULL)
	{	fprintf(stderr, "uno:global: cannot open %s\n", f);
		exit(1);
	}

	while (fgets(buf, sizeof(buf), fd))
		switch (buf[0]) {
		case '{':
		case '<':
		case '>':
		case '[':
		case ':':
			handle_fct(buf);
			break;
		default:
			handle_glb(buf, f);
			break;
		}

	fclose(fd);
}

static void
fcts_reset(void)
{	Fct *g;

	for (g = fcts; g; g = g->nxt)
		g->visited = 0;
}

static void
dfs(Fct *g)
{	Sym *r;

	if (!g || g->visited) return;

	g->visited = 1;

	for (r = g->calls; r; r = r->nxt)
		dfs(find_fct(r->s));
}

static void
wind_down(Fct *f)
{	Fct *g;
	Sym *c;

	if (f)
	for (c = f->calls; c; c = c->nxt)
	{	g = find_fct(c->s);
		if (g && !(g->rval & 4))
		{	g->rval |= 4;
			wind_down(g);
	}	}
}

static void
unused_fcts(void)
{	Fct *f, *g;
	Sym *c;
	int sawsome = 0;

	fcts_reset();
	dfs(find_fct("main"));	/* mark reachable fcts */

	for (f = fcts; f; f = f->nxt)
		if (f->rval & 4)	/* rval, 1: return value, 2: no return value, 4: cannot tell */
			wind_down(f);	/* propagate mark to all fcts called */

	for (f = fcts; f; f = f->nxt)
		if (!f->visited
		&&  !f->special
		&&  !(f->rval & 4)
		&&  strcmp(f->fnm, "_global_") != 0
		&&  strstr(f->n->fnm, "stdio.h") == NULL)
		{	if (!sawsome)
				printf("uno:global: functions declared but not used:");
			if ((sawsome++) % 2 == 0)
				printf("\n");
			printf("\t%s:%d %s()",
				f->n->fnm, f->n->line, f->fnm);
		}
	if (sawsome) printf("\n");

	for (f = fcts; f; f = f->nxt)
	{	if (strcmp(f->fnm, "_global_") == 0)
			continue;

		if (strcmp(f->fnm, "main") == 0
		&&  (f->rval & 2))
			printf("uno:global: %s:%d %s() can fail to return a value\n",
				f->n->fnm, f->n->line, f->fnm);


		if ((f->rval & 1) && (f->rval & 2) && !f->special)
			printf("uno:global: %s:%d %s() can fail to return a value\n",
				f->n->fnm, f->n->line, f->fnm);
		else if (f->rval == 0)
			printf("uno:global: %s:%d %s() no return value status recorded\n",
				f->n->fnm, f->n->line, f->fnm);
	}

	for (f = fcts; f; f = f->nxt)
	for (c = f->calls; c; c = c->nxt)
	{	g = find_fct(c->s);

		if (c->n->line == 0
		&&  strcmp(c->n->fnm, "---") == 0)
			continue;

		if (g
		&& (g->rval & 2)
		&& (c->bits & USE)
		&& !(c->bits & HIDE))
		printf("uno:global: %s() fails to return value%s expected at %s:%d\n",
			c->s, (c->bits&DEF)?" maybe":"", c->n->fnm, c->n->line);
	}

	if (!verbose) return;

	for (f = fcts; f; f = f->nxt)
	for (c = f->calls; c; c = c->nxt)
	{	g = find_fct(c->s);
		if (g
		&& (g->rval & 1)
		&&  c->bits == DEF)
		printf("uno:global: return value of %s() ignored at %s:%d\n",
			c->s, c->n->fnm, c->n->line);
	}
	for (f = fcts; f; f = f->nxt)
	for (c = f->calls; c; c = c->nxt)
	{	g = find_fct(c->s);
		if (g
		&& (g->rval & 1)
		&&  c->bits == (USE|DEF))
		printf("uno:global: return value of %s() maybe ignored at %s:%d\n",
			c->s, c->n->fnm, c->n->line);
	}
}
