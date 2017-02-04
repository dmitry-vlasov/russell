AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

AM_LDFLAGS = \
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

libsmm_la_SOURCES = \
	../location.cpp \
	../timer.cpp \
	../mm/show.cpp \
	../rus/show.cpp \
	../rus/expr.cpp \
	\
	globals.cpp \
	math_symb.cpp \
	parser.cpp \
	show.cpp \
	parser.cpp \
	translate_mm.cpp \
	translate_rus.cpp \
	tree.cpp \
	verify.cpp

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
