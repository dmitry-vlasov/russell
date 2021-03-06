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
		com/memusage.cpp 
		com/common.cpp 
		com/xml.cpp 
		
		daem.cpp 
		
		mm/mm_cut.cpp 
		mm/mm_sys.cpp
		mm/mm_fixsynt.cpp 
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
		rus/prover/rus_prover_compare.cpp
		rus/prover/rus_prover_down.cpp
		rus/prover/rus_prover_node.cpp
		rus/prover/rus_prover_proof.cpp
		rus/prover/rus_prover_prover.cpp
		rus/prover/rus_prover_maker.cpp
		rus/prover/rus_prover_show.cpp
		rus/prover/rus_prover_space.cpp
		rus/prover/rus_prover_stats.cpp
		rus/prover/rus_prover_tactics.cpp
		rus/prover/rus_prover_test_maker.cpp
		rus/prover/rus_prover_test_prover.cpp	
		rus/prover/rus_prover_term.cpp
		rus/prover/rus_prover_subst.cpp
		rus/prover/rus_prover_multy_subst.cpp
		rus/prover/unify/rus_prover_unify_index.cpp
		rus/prover/unify/rus_prover_unify_index_term.cpp
		rus/prover/unify/rus_prover_unify_indexes.cpp
		rus/prover/unify/rus_prover_unify_vector.cpp
		rus/prover/unify/rus_prover_unify_matrix.cpp
		rus/prover/unify/rus_prover_unify_general.cpp
		rus/prover/unify/rus_prover_unify_step.cpp
		rus/prover/unify/rus_prover_unify_terms.cpp
		rus/prover/unify/rus_prover_unify.cpp

		rus/transform/rus_transform_abst_proof_set.cpp
		rus/transform/rus_transform_generalize_theorems.cpp
		rus/transform/rus_transform_generalization_relation.cpp
		rus/transform/rus_transform_factor_subproofs.cpp
		rus/transform/rus_transform_duplicate_steps.cpp
		rus/transform/rus_transform_proof_shortcuts.cpp
		rus/transform/rus_transform_replace_with_optimal.cpp
		rus/transform/rus_transform_unused_hyps.cpp
		rus/transform/rus_transform_unused_steps.cpp
		rus/transform/rus_transform_insert_theorem.cpp

		rus/rus_ast.cpp
		rus/rus_beautify.cpp
		rus/rus_expr.cpp
		rus/rus_imports.cpp
		rus/rus_lookup.cpp
		rus/rus_memvol.cpp  
		rus/rus_sys.cpp
		#rus/rus_refactor.cpp  
		#rus/rus_parser.cpp
		rus/rus_fixsynt.cpp 
		rus/rus_read.cpp  
		rus/rus_show.cpp
		rus/rus_stats.cpp 
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

