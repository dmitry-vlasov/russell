AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

AM_LDFLAGS = \
	-L$(top_builddir)/src/com -lcom \
    $(BOOST_LDFLAGS)
	
lib_LTLIBRARIES = \
	libmm.la

noinst_HEADERS = \
	cut_adaptor.hpp \
	tree.hpp 

if SPLIT_COMPILE
libmm_la_SOURCES = \
	cut.cpp \
	ast.cpp \
	sys.cpp \
	merge.cpp \
	parser.cpp \
	show.cpp \
	translate.cpp \
	tree.cpp
else
libmm_la_SOURCES = \
	all.cpp
endif

libmm_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)
