AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

AM_LDFLAGS = \
	-L$(top_builddir)/src/com -lcom \
    $(BOOST_LDFLAGS)

lib_LTLIBRARIES = \
	libsmm.la

noinst_HEADERS = \
	tree.hpp 

if SPLIT_COMPILE
libsmm_la_SOURCES = \
	ast.cpp \
	sys.cpp \
	math_symb.cpp \
	parser.cpp \
	show.cpp \
	translate_mm.cpp \
	translate_rus.cpp \
	tree.cpp \
	verify.cpp
else
libsmm_la_SOURCES = \
	all.cpp
endif

libsmm_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)
