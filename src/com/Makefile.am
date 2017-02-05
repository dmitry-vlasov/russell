AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

AM_LDFLAGS = \
    $(BOOST_LDFLAGS)

noinst_LTLIBRARIES = \
	libcom.la

if SPLIT_COMPILE
libcom_la_SOURCES = \
	location.cpp \
	timer.cpp \
	memusage.cpp
else
libcom_la_SOURCES = \
	all.cpp
endif

libcom_la_LIBADD = \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)
