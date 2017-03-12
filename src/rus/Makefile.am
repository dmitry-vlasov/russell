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

bin_PROGRAMS = \
	rus
	
noinst_LTLIBRARIES = \
	librus.la

noinst_HEADERS = \
	parser/adaptors.hpp \
	parser/grammar.hpp \
	parser/parse.hpp  

if SPLIT_COMPILE
librus_la_SOURCES = \
	../smm/show.cpp \
	../smm/ast.cpp \
	\
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
	../smm/show.cpp \
	../smm/ast.cpp \
	all.cpp
endif

rus_SOURCES = \
	main.cpp

librus_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB) \
    $(PTHREAD_CFLAGS)

rus_LDADD = \
	librus.la \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB) \
    $(PTHREAD_CFLAGS)
