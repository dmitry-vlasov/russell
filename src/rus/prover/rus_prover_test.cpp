#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

bool test_proof_with_oracle(Proof* p) {
	cout << "testing proof of " << show_id(p->theorem()->id()) << " ... " << std::endl;
	unique_ptr<prover::Space> space = make_unique<prover::Space>(*p->qeds().begin(), new prover::Oracle(p));
	cout << "SPACE INDEX: " << space->ind << " ... " << std::flush;
	Return reproved = space->prove();
	cout << "message: \"" << reproved.msg << "\"" << endl;
	return reproved.msg == "goal proved";
}

bool test_with_oracle() {
	struct SourceLess {
		bool operator () (const Source* s1, const Source* s2) {
			return s1->id() < s2->id();
		}
	};
	set<Source*, SourceLess> ordered_sources;
	for (auto& p : Sys::mod().math.get<Source>()) {
		ordered_sources.insert(p.second.data);
	}
	cout << endl;
	for (Source* src : ordered_sources) {
		//cout << "SOURCE: " << src->id() << " = " << Lex::toStr(src->id()) << endl;
		for (auto& n : src->theory.nodes) {
			if (Theory::kind(n) == Theory::PROOF) {
				if (!test_proof_with_oracle(Theory::proof(n))) {
					return false;
				}
			}
		}
	}
	cout << "Testing with oracle succeeded :)" << endl;
	return true;
}

}}}
