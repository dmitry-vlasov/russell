#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

Return test_proof_with_oracle(const Proof* p) {
	cout << "testing proof of " << show_id(p->theorem()->id()) << " ... " << std::endl;
	Oracle* oracle = new prover::Oracle(p);
	unique_ptr<prover::Space> space = make_unique<prover::Space>(*p->qeds().begin(), oracle);
	Return ret = space->prove();
	if (!ret.success()) {
		cout << "oracle status:" << endl;
		cout << oracle->show() << endl;
	}
	return ret;
}

Return test_with_oracle(string theorem) {
	if (!theorem.size()) {
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
		uint counter = 0;
		for (Source* src : ordered_sources) {
			cout << "testing source: " << Lex::toStr(src->id()) << endl;
			for (auto& n : src->theory.nodes) {
				if (Theory::kind(n) == Theory::PROOF) {
					cout << counter++ << " ";
					Return r = test_proof_with_oracle(Theory::proof(n));
					if (!r.success()) {
						debug_oracle = true;
						test_proof_with_oracle(Theory::proof(n));
						return r;
					}
				}
			}
		}
		return Return("Massive prover testing with oracle succeeded :)");
	} else {
		const rus::Assertion* ass = Sys::get().math.get<rus::Assertion>().access(Lex::toInt(theorem));
		if (const rus::Theorem* th = dynamic_cast<const rus::Theorem*>(ass)) {
			for (const auto& pr : th->proofs) {
				Return r = test_proof_with_oracle(pr.get());
					if (!r.success()) {
						debug_oracle = true;
						test_proof_with_oracle(pr.get());
						return r;
					}
			}
			return Return(string("Prover testing of ") + theorem + " with oracle succeeded :)");
		} else {
			return Return(string("Prover testing of ") + theorem + " - is not a theorem");
		}
	}
}

}}}
