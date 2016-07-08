#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.69])
AC_INIT(russell-formal-math, 0.9.2, vlasov@academ.org)
AC_CONFIG_SRCDIR([config.h.in])
AC_CONFIG_HEADERS([config.h])
AM_INIT_AUTOMAKE

# Checks for programs.
AC_PROG_CXX
AC_PROG_CC

# Checks for libraries.

# Checks for header files.
#AC_CHECK_HEADERS([stddef.h stdint.h sys/time.h unistd.h])
AC_CHECK_HEADERS

# Checks for typedefs, structures, and compiler characteristics.
AC_CHECK_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T
AC_TYPE_UINT32_T
AC_CHECK_TYPES([ptrdiff_t])

# Checks for library functions.
# AC_CHECK_FUNCS([gettimeofday])

AC_CONFIG_FILES([
	Makefile
	src/mm/Makefile
	src/rus/Makefile
	src/smm/Makefile
])

AC_OUTPUT
