AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS) \
	$(PTHREAD_CFLAGS)

AM_LDFLAGS = \
	-L$(top_builddir)/src/com -lcom \
	-L$(top_builddir)/src/mm  -lmm  \
	-L$(top_builddir)/src/smm -lsmm \
	-L$(top_builddir)/src/rus -lrus \
    $(BOOST_LDFLAGS) \
    $(PTHREAD_CFLAGS)

lib_LTLIBRARIES = \
	libmdld.la

if SPLIT_COMPILE
libmdld_la_SOURCES = \
	daemon.cpp
else
libmdld_la_SOURCES = \
	all.cpp
endif

libmdld_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB) \
    $(PTHREAD_CFLAGS)
