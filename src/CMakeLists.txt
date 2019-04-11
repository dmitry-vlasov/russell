#
# The Russell language implementation
#
cmake_minimum_required (VERSION 3.8)
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
		mm/mm_sys.cpp 
		mm/mm_merge.cpp 
		mm/mm_inclusions.cpp
		mm/mm_lookup.cpp
		mm/mm_parser.cpp 
		mm/mm_read.cpp
		mm/mm_tree.cpp  
		mm/mm_translate.cpp
		mm/mm_verify.cpp
		
		rus/expr/rus_expr_parse.cpp 
		rus/expr/rus_expr_unify.cpp
		rus/parser/rus_parser.cpp 
		
		rus/prover/rus_prover_cartesian.cpp
		rus/prover/rus_prover_down.cpp
		rus/prover/rus_prover_node.cpp
		rus/prover/rus_prover_proof.cpp
		rus/prover/rus_prover_show.cpp
		rus/prover/rus_prover_space.cpp
		rus/prover/rus_prover_stats.cpp
		rus/prover/rus_prover_tactics.cpp
		rus/prover/rus_prover_test.cpp	
		rus/prover/rus_prover_term.cpp
		rus/prover/rus_prover_subst.cpp
		rus/prover/rus_prover_multy_subst.cpp
		rus/prover/index/rus_prover_index.cpp
		rus/prover/index/rus_prover_index_matrix.cpp
		rus/prover/index/rus_prover_index_unify.cpp
		rus/prover/index/rus_prover_index_unify_iter.cpp

		rus/rus_ast.cpp
		rus/rus_expr.cpp
		rus/rus_imports.cpp
		rus/rus_lookup.cpp
		rus/rus_memvol.cpp  
		rus/rus_sys.cpp 
		#rus/rus_parser.cpp
		rus/rus_read.cpp  
		rus/rus_show.cpp 
		rus/rus_translate.cpp 
		rus/rus_verify.cpp 
		rus/rus_xml.cpp 
		
		main.cpp
	)
endif()

add_executable(mdl ${RUSSELL_SRC})	

target_compile_features(mdl PUBLIC cxx_std_17)

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

