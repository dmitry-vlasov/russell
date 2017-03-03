AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

AM_LDFLAGS = \
	-L$(top_builddir)/src/com -lcom \
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
	tree.hpp 

if SPLIT_COMPILE
libmm_la_SOURCES = \
	../smm/show.cpp \
	\
	cut/parser.cpp \
	cut/globals.cpp \
	cut/show.cpp \
	\
	merge/parser.cpp \
	\
	ast.cpp \
	sys.cpp \
	parser.cpp \
	show.cpp \
	translate.cpp \
	tree.cpp
else
libmm_la_SOURCES = \
	../smm/show.cpp \
	all.cpp
endif

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
