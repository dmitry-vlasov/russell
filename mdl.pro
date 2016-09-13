TEMPLATE = subdirs
SUBDIRS = \
	src/mm \
	src/rus \
	src/smm \
	src

src/mm.depends = src src/mm
src/rus.depends = src
src/smm.depends = common