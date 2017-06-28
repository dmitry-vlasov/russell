#
# The original Metamath language implementation
#
project(Metamath)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

set (METAMATH_SRC
	mmcmdl.c
	mmcmds.c
	mmdata.c
	mmhlpa.c
	mmhlpb.c
	mminou.c
	mmmaci.c
	mmpars.c
	mmpfas.c
	mmunif.c
	mmutil.c
	mmveri.c
	mmvstr.c
	mmword.c
	mmwtex.c
	metamath.c
)

add_executable(metamath ${METAMATH_SRC})	

install(TARGETS metamath DESTINATION bin)
