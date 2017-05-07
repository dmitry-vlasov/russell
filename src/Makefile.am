SUBDIRS = \
	com \
	mm  \
	smm \
	rus \
	daem

AM_CPPFLAGS = \
	-I$(top_srcdir)/include \
	-I$(top_srcdir)/peglib \
	-I$(top_srcdir)/src \
	$(BOOST_CPPFLAGS)

bin_PROGRAMS = \
	mdl

mdl_SOURCES = \
	main.cpp

mdl_LDADD = \
	$(top_builddir)/lib/libmm.la \
	$(top_builddir)/lib/libmdld.la \
	$(top_builddir)/lib/librus.la \
	$(top_builddir)/lib/libsmm.la \
	$(top_builddir)/lib/libcom.la \
	$(BOOST_FILESYSTEM_LIB) \
    $(BOOST_SYSTEM_LIB) \
    $(BOOST_PROGRAM_OPTIONS_LIB)
