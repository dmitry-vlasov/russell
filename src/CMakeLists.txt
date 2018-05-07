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
		com/xml.cpp 
		
		daem.cpp 
		
		mm/mm_cut.cpp 
		mm/mm_ast.cpp 
		mm/mm_sys.cpp 
		mm/mm_merge.cpp 
		mm/mm_parser.cpp 
		mm/mm_read.cpp 
		mm/mm_show.cpp  
		mm/mm_translate_smm.cpp 
		
		mm2/mm2_cut.cpp 
		mm2/mm2_ast.cpp 
		mm2/mm2_sys.cpp 
		mm2/mm2_merge.cpp 
		mm2/mm2_parser.cpp 
		mm2/mm2_read.cpp 
		mm2/mm2_show.cpp  
		mm2/mm2_translate_smm.cpp 
		
		rus/expr/rus_expr_parse.cpp 
		rus/expr/rus_expr_unify.cpp 
		rus/parser/rus_parser.cpp
		rus/prover/rus_prover_index.cpp
		rus/prover/rus_prover_node.cpp
		rus/prover/rus_prover_proof.cpp
		rus/prover/rus_prover_show.cpp
		rus/prover/rus_prover_space.cpp
		rus/prover/rus_prover_tactics.cpp
		rus/rus_expr.cpp 
		rus/rus_sys.cpp 
		rus/rus_ast.cpp 
		rus/rus_memvol.cpp
		rus/rus_parser.cpp
		rus/rus_read.cpp  
		rus/rus_show.cpp 
		rus/rus_test.cpp 
		rus/rus_translate.cpp 
		rus/rus_verify.cpp 
		rus/rus_xml.cpp 
		
		smm/smm_ast.cpp 
		smm/smm_sys.cpp 
		smm/smm_parser.cpp 
		smm/smm_read.cpp 
		smm/smm_show.cpp 
		smm/smm_translate_mm.cpp 
		smm/smm_translate_rus.cpp 
		smm/smm_tree.cpp 
		smm/smm_verify.cpp 
		
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
	stdc++fs
	tbb
)

install(TARGETS mdl DESTINATION bin)

