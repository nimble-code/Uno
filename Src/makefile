#	(c) 2000-2007, Bell Labs, Lucent Technologies
#	Makefile for UNO, a C source code analyzer - September 7, 2011
#	Based on ctree version 0.14 from Shaun Flisakowski
#	contact: Gerard J. Holzmann, gholzmann@acm.org
#
#	This makefile requires
#		an ANSI compatible C compiler
#		bison and flex
#	It creates 3 separate progrsms:
#		uno, uno_local, and uno_global
#	the main command is 'uno' which calls
#	uno_local and uno_global when it executes (they can also be called
#	directly to perform local or global analyses).
#
#	To execute, uno requires:
#		Unix utility grep (in cygwin or mks toolkits on PCs)
#		and either gcc (Unix), cpp (Plan9), or cl (PC)
#		for preprocessing source files
#		the default for CPP can be overridden by compiling
#		file uno_local.c with -DCPP=...
#		or at runtime with uno -CPP=... or uno_local -CPP=...
#	use the script _pc_make to compile uno for a Windows PC
#
# Unix Makefile:
#
BINDIR=/usr/local/bin/
# note the terminal / in the above line is needed
## 2019: too make extensions are made in the gcc headerfiles to allow the
##       builtin parser to sill work reliably
CC=gcc
CFLAGS=-DPC -ansi -Wall -g -DCPP="\"gcc -E -D__extension__= -D__inline__= -D_Noreturn= -D__typeof__= \"" -DBINDIR=\"$(BINDIR)\"

# on PC add:
#	-DPC
# or use the _pc_make script
#
# if the BINDIR settings fail try:
#	-DBINDIR="$(BINDIR)"
#
# on some systems you may also need to add to CFLAGS:
#	-fwritable-strings

OFILES = uno_local.o heap.o nmetab.o symtab.o \
	token.o tree.o treestk.o lexer.o c_gram.o dflow.o \
	prnttree.o uno_lts.o explore.o \
	uno_bounds.o uno_intervals.o uno_generic.o

all:	uno uno_local uno_global

install: all
	cp uno uno_local uno_global $(BINDIR)

self_test:	c_gram.c lexer.c
	./mk_uno_suppress
	uno -u uno.c
	uno -u -x notyet uno_global.c uno_fcts.c
	uno -u uno_local.c dflow.c c_gram.c heap.c \
		nmetab.c prnttree.c symtab.c token.c tree.c \
		treestk.c uno_bounds.c lexer.c \
		uno_generic.c uno_intervals.c uno_lts.c explore.c

sharing:
	uno_local -shared uno.c	# should print nothing
	uno_local -shared uno_global.c uno_fcts.c
	uno_local -shared uno_local.c dflow.c c_gram.c heap.c \
		nmetab.c prnttree.c symtab.c token.c tree.c \
		treestk.c uno_bounds.c lexer.c \
		uno_generic.c uno_intervals.c uno_lts.c

uno:	uno.c
	$(CC) $(CFLAGS) -o uno uno.c

uno_local:	c_gram.h $(OFILES) 
	$(CC) $(CFLAGS) -o uno_local $(OFILES)

uno_global:	uno_global.o uno_fcts.o
	$(CC) $(CFLAGS) -o uno_global uno_global.o uno_fcts.o

c_gram.c c_gram.h:	c_gram.y tree.h symtab.h globals.h
	bison -v -d -o c_gram.c c_gram.y	# expect 6 shift/reduce 23 reduce/reduce conflicts

lexer.c: lexer.l c_gram.h globals.h lexer.h nmetab.h symtab.h heap.h
	flex -C -olexer.c lexer.l

lexer.o: lexer.c

c_gram.o: c_gram.c

uno_global.o:	uno_global.h uno_fcts.h dtags.h

dflow.o:	dflow.c dflow.h prnttree.h c_gram.h symtab.h

prnttree.o:	prnttree.c prnttree.h c_gram.h symtab.h

treestk.o:	treestk.c globals.h treestk.h

heap.o:		heap.c heap.h

nmetab.o:	nmetab.c globals.h lexer.h nmetab.h

symtab.o:	symtab.c symtab.h nmetab.h prnttree.h

token.o:	token.c c_gram.h

tree.o:	tree.c tree.h c_gram.h globals.h prnttree.h

uno_lts.o:	uno_lts.c uno_lts.h prnttree.h c_gram.h symtab.h

uno_bounds.o:	uno_bounds.c uno_lts.h symtab.h c_gram.h

uno_intervals.o:	uno_intervals.c uno_lts.h

uno_generic.o:	uno_generic.c uno_lts.h c_gram.h symtab.h

uno_local.o:	uno_local.c uno_version.h globals.h

explore.o:	explore.c symtab.h prnttree.h

clean:
	rm -f c_gram.[ch] *.o *.obj *.exe c_gram.output lexer.c uno_local uno_global uno *.uno

view:
	./uno_local -rules -view example.c | ./m.awk > e.dot; dotty e.dot
