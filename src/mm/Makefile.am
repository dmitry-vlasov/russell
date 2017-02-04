AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

AM_LDFLAGS = \
    $(BOOST_LDFLAGS)

bin_PROGRAMS = \
	mm
	
noinst_LTLIBRARIES = \
	libmm.la

noinst_HEADERS = \
	cut/adaptors.hpp \
	cut/ast.hpp \
	cut/grammar.hpp \
	cut/parser.hpp \
	\
	merge/ast.hpp \
	merge/grammar.hpp \
	merge/parser.hpp \
	\
	adaptors.hpp \
	spirit_grammar.hpp \
	spirit_parser.hpp \
	tree.hpp 

libmm_la_SOURCES = \
	../location.cpp \
	../timer.cpp \
	../smm/show.cpp \
	\
	cut/parser.cpp \
	cut/globals.cpp \
	cut/show.cpp \
	\
	merge/parser.cpp \
	\
	globals.cpp \
	peg_parser.cpp \
	show.cpp \
	spirit_parser.cpp \
	translate.cpp \
	tree.cpp

mm_SOURCES = \
	main.cpp

libmm_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)

mm_LDADD = \
	libmm.la \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)
