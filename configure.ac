#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.69])
AC_INIT(russell-formal-math, 0.9.3, vlasov@academ.org)
AC_CONFIG_SRCDIR([config.h.in])
AC_CONFIG_HEADERS([config.h])
AM_INIT_AUTOMAKE

# Checks for programs.
AC_PROG_CXX
AC_PROG_CC

# Checks for header files.
#AC_CHECK_HEADERS([stddef.h stdint.h sys/time.h unistd.h])
AC_CHECK_HEADERS

# Checks for typedefs, structures, and compiler characteristics.
AC_CHECK_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T
AC_TYPE_UINT32_T
AC_CHECK_TYPES([ptrdiff_t])

#m4_include([m4/ax_check_compile_flag.m4])
AX_CHECK_COMPILE_FLAG([-std=gnu++1z], [CXXFLAGS="$CXXFLAGS -std=gnu++1z"])

AM_INIT_AUTOMAKE([subdir-objects])

AC_CONFIG_MACRO_DIR([m4])

AX_BOOST_BASE([1.48], AC_MSG_ERROR([libfoo needs Boost, but it was not found in your system]))
AX_BOOST_SYSTEM
AX_BOOST_FILESYSTEM
AX_BOOST_PROGRAM_OPTIONS
AX_PTHREAD

AC_ARG_ENABLE(
	[split-compile],
	[  --enable-split-compile  compile all *.cpp files separately],
	[case "${enableval}" in
		yes) split_compile=yes ;;
		no)  split_compile=no ;;
		*) AC_MSG_ERROR([bad value ${enableval} for --enable-split-compile]) ;;
	esac],
	[split_compile=no]
)
AC_MSG_NOTICE([checking split-compile ... $split_compile])

AM_CONDITIONAL([SPLIT_COMPILE], [test $split_compile = yes])


AC_CONFIG_FILES([
	Makefile
	scripts/Makefile
	include/Makefile
	peglib/Makefile
	src/Makefile
	metamath/Makefile
])

AC_OUTPUT
