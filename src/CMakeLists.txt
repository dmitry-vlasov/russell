#
# The Russell language implementation
#
project(Russell)

include_directories(
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}/../include
  ${CMAKE_CURRENT_SOURCE_DIR}/../peglib
)

if (BUILD_SOLID)
	set(RUSSELL_SRC main.cpp)
else() 
	set(RUSSELL_SRC
		com/actions.cpp 
		com/log.cpp 
		com/timer.cpp 
		com/memusage.cpp 
		com/common.cpp 
		
		daem/daemon.cpp 
		
		mm/cut.cpp 
		mm/ast.cpp 
		mm/sys.cpp 
		mm/merge.cpp 
		mm/parser.cpp 
		mm/show.cpp  
		mm/translate.cpp 
		
		rus/expr/parse.cpp 
		rus/expr/unify.cpp 
		rus/parser/parse.cpp 
		rus/expr.cpp 
		rus/sys.cpp 
		rus/ast.cpp 
		rus/memvol.cpp 
		rus/show.cpp 
		rus/translate.cpp 
		rus/verify.cpp 
		
		smm/ast.cpp 
		smm/sys.cpp 
		smm/parser.cpp 
		smm/show.cpp 
		smm/translate_mm.cpp 
		smm/translate_rus.cpp 
		smm/tree.cpp 
		smm/verify.cpp 
		
		main.cpp
	)
endif()

add_executable(mdl ${RUSSELL_SRC})	

target_link_libraries(mdl 
	${Boost_LIBRARIES}
	${Boost_PROGRAM_OPTIONS_LIBRARY}
	${Boost_LOG}
	${Boost_LOG_SETUP}
	${CMAKE_THREAD_LIBS_INIT}
)

install(TARGETS mdl DESTINATION bin)

