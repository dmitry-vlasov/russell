#pragma once
/* config.h.in.  Generated from configure.ac by autoheader.  */

/* define if the Boost library is available */
#cmakedefine  HAVE_BOOST 1

/* define if the Boost::Filesystem library is available */
#cmakedefine  HAVE_BOOST_FILESYSTEM 1

/* define if the Boost::PROGRAM_OPTIONS library is available */
#cmakedefine  HAVE_BOOST_PROGRAM_OPTIONS 1

/* define if the Boost::System library is available */
#cmakedefine  HAVE_BOOST_SYSTEM 1

/* Define to 1 if you have the <inttypes.h> header file. */
#cmakedefine  HAVE_INTTYPES_H 1

/* Define to 1 if you have the <memory.h> header file. */
#cmakedefine  HAVE_MEMORY_H 1

/* Define if you have POSIX threads libraries and header files. */
#cmakedefine  HAVE_PTHREAD 1

/* Have PTHREAD_PRIO_INHERIT. */
#cmakedefine  HAVE_PTHREAD_PRIO_INHERIT 1

/* Define to 1 if the system has the type `ptrdiff_t'. */
#cmakedefine  HAVE_PTRDIFF_T 1

/* Define to 1 if you have the <stdint.h> header file. */
#cmakedefine  HAVE_STDINT_H 1

/* Define to 1 if you have the <stdlib.h> header file. */
#cmakedefine  HAVE_STDLIB_H 1

/* Define to 1 if you have the <strings.h> header file. */
#cmakedefine  HAVE_STRINGS_H 1

/* Define to 1 if you have the <string.h> header file. */
#cmakedefine  HAVE_STRING_H 1

/* Define to 1 if you have the <sys/stat.h> header file. */
#cmakedefine  HAVE_SYS_STAT_H 1

/* Define to 1 if you have the <sys/types.h> header file. */
#cmakedefine  HAVE_SYS_TYPES_H 1

/* Define to 1 if you have the <unistd.h> header file. */
#cmakedefine  HAVE_UNISTD_H 1

/* Define to 1 if the system has the type `_Bool'. */
#cmakedefine  HAVE__BOOL 1

/* Name of package */
#cmakedefine  PACKAGE 1

/* Define to the address where bug reports for this package should be sent. */
#cmakedefine  PACKAGE_BUGREPORT 1

/* Define to the full name of this package. */
#cmakedefine  PACKAGE_NAME 1

/* Define to the full name and version of this package. */
#cmakedefine  PACKAGE_STRING 1

/* Define to the one symbol short name of this package. */
#cmakedefine  PACKAGE_TARNAME 1

/* Define to the home page for this package. */
#cmakedefine  PACKAGE_URL 1

/* Define to the version of this package. */
#cmakedefine  PACKAGE_VERSION 1

/* Define to necessary symbol if this constant uses a non-standard name on
   your system. */
#cmakedefine  PTHREAD_CREATE_JOINABLE 1

/* Define to 1 if you have the ANSI C header files. */
#cmakedefine  STDC_HEADERS 1

/* Version number of package */
#define RUSSELL_VERSION_MAJOR "@Russell_VERSION_MAJOR@"
#define RUSSELL_VERSION_MINOR "@Russell_VERSION_MINOR@"

/* Define for Solaris 2.5.1 so the uint32_t typedef from <sys/synch.h>,
   <pthread.h>, or <semaphore.h> is not used. If the typedef were allowed, the
   #define below would cause a syntax error. */
#cmakedefine  _UINT32_T 1

/* Define to `__inline__' or `__inline' if that's what the C compiler
   calls it, or to nothing if 'inline' is not supported under any name.  */
#ifndef __cplusplus
#cmakedefine  inline 1
#endif

/* Define to `unsigned int' if <sys/types.h> does not define. */
#cmakedefine  size_t 1

/* Define to the type of an unsigned integer type of width exactly 32 bits if
   such a type exists and the standard includes do not define it. */
#cmakedefine  uint32_t 1

