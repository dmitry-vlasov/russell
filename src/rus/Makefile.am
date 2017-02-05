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
	mdl
	
noinst_LTLIBRARIES = \
	libmdl.la

noinst_HEADERS = \
	parser/adaptors.hpp \
	parser/grammar.hpp \
	parser/parse.hpp  

if SPLIT_COMPILE
libmdl_la_SOURCES = \
	../smm/show.cpp \
	\
	expr/parse.cpp \
	expr/unify.cpp \
	\
	parser/parse.cpp \
	\
	daemon.cpp \
	expr.cpp \
	globals.cpp \
	memvol.cpp \
	show.cpp \
	translate.cpp \
	verify.cpp
else
libmdl_la_SOURCES = \
	../smm/show.cpp \
	all.cpp
endif

mdl_SOURCES = \
	main.cpp

libmdl_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB) \
    $(PTHREAD_CFLAGS)

mdl_LDADD = \
	libmdl.la \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB) \
    $(PTHREAD_CFLAGS)
