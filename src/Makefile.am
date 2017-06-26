AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

AM_LDFLAGS = \
    $(BOOST_LDFLAGS) \
    $(PTHREAD_CFLAGS)

bin_PROGRAMS = \
	mdl

if SPLIT_COMPILE
mdl_SOURCES = \
	com/timer.cpp \
	com/memusage.cpp \
	com/common.cpp \
	\
	daem/daemon.cpp \
	\
	mm/cut.cpp \
	mm/ast.cpp \
	mm/sys.cpp \
	mm/merge.cpp \
	mm/parser.cpp \
	mm/show.cpp \
	mm/translate.cpp \
	\
	rus/expr/parse.cpp \
	rus/expr/unify.cpp \
	rus/parser/parse.cpp \
	rus/expr.cpp \
	rus/sys.cpp \
	rus/ast.cpp \
	rus/memvol.cpp \
	rus/show.cpp \
	rus/translate.cpp \
	rus/verify.cpp \
	\
	smm/ast.cpp \
	smm/sys.cpp \
	smm/parser.cpp \
	smm/show.cpp \
	smm/translate_mm.cpp \
	smm/translate_rus.cpp \
	smm/tree.cpp \
	smm/verify.cpp \
	\
	main.cpp
else
mdl_SOURCES = \
	all.cpp \
	main.cpp
endif

mdl_LDADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)
