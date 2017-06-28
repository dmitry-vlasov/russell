#
# Russell project
#
project (Russell)

# The version number.
set (Russell_VERSION_MAJOR 0)
set (Russell_VERSION_MINOR 5)

include(CheckCXXCompilerFlag)

set(CMAKE_CXX_STANDARD 14)

# minimal requirements
cmake_minimum_required (VERSION 2.8.12 FATAL_ERROR)
set (QT_MIN_VERSION "5.4.0")
set (BOOST_MIN_VERSION 1.40)

find_package(Boost ${BOOST_MIN_VERSION} COMPONENTS 
	program_options
	filesystem
	system 
	REQUIRED 
)
find_package (Threads)

include_directories( ${Boost_INCLUDE_DIR} )

# config.h
configure_file (
	${PROJECT_SOURCE_DIR}/config.h.cmake 
	${CMAKE_CURRENT_BINARY_DIR}/config.h
)

# let our config.h be found first in any case
include_directories (BEFORE ${CMAKE_CURRENT_BINARY_DIR})

option(BUILD_SOLID "Build all sources in one *.cpp file")

if(BUILD_SOLID)
  add_definitions(-DBUILD_SOLID=1)
endif()

# sources
add_subdirectory (src)
add_subdirectory (metamath)

