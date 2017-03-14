AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS) \
	$(PTHREAD_CFLAGS)

AM_LDFLAGS = \
	-L$(top_builddir)/src/com -lcom \
    $(BOOST_LDFLAGS) \
    $(PTHREAD_CFLAGS)
	
lib_LTLIBRARIES = \
	librus.la

noinst_HEADERS = \
	parser/adaptors.hpp \
	parser/grammar.hpp \
	parser/parse.hpp  

if SPLIT_COMPILE
librus_la_SOURCES = \
	expr/parse.cpp \
	expr/unify.cpp \
	\
	parser/parse.cpp \
	\
	expr.cpp \
	sys.cpp \
	ast.cpp \
	memvol.cpp \
	show.cpp \
	translate.cpp \
	verify.cpp
else
librus_la_SOURCES = \
	all.cpp
endif

librus_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB) \
    $(PTHREAD_CFLAGS)
