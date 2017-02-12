AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

AM_LDFLAGS = \
	-L$(top_builddir)/src/com -lcom \
    $(BOOST_LDFLAGS)

bin_PROGRAMS = \
	smm
	
noinst_LTLIBRARIES = \
	libsmm.la

noinst_HEADERS = \
	adaptors.hpp \
	grammar.hpp \
	parser.hpp \
	tree.hpp 

if SPLIT_COMPILE
libsmm_la_SOURCES = \
	../mm/show.cpp \
	../rus/show.cpp \
	../rus/expr.cpp \
	\
	sys.cpp \
	math_symb.cpp \
	show.cpp \
	translate_mm.cpp \
	translate_rus.cpp \
	tree.cpp \
	verify.cpp
else
libsmm_la_SOURCES = \
	../mm/show.cpp \
	../rus/show.cpp \
	../rus/expr.cpp \
	all.cpp
endif

smm_SOURCES = \
	main.cpp

libsmm_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)

smm_LDADD = \
	libsmm.la \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)
