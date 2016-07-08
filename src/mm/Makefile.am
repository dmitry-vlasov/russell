AM_CPPFLAGS = \
	-I$(top_srcdir)/include

bin_PROGRAMS = \
	mdl

noinst_HEADERS = \
	expr/GLR.hpp \
	expr/table.hpp \
	\
	parser/adaptors.hpp \
	parser/grammar.hpp \
	parser/ind.hpp \
	parser/parser.hpp 

mdl_SOURCES = \
	../location.cpp \
	../memusage.cpp \
	../timer.cpp \
	\
	expr/GLR.cpp \
	expr/parser.cpp \
	expr/show.cpp \
	\
	parser/parser.cpp \
	\
	expr.cpp \
	globals.cpp \
	memvol.cpp \
	modify_grammar.cpp \
	show.cpp \
	translate.cpp \
	verify.cpp \
	main.cpp
