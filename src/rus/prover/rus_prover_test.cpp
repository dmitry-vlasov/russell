#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

Return test_proof_with_oracle(const Proof* p, uint max_proofs) {
	cout << "testing proof of " << show_id(p->theorem()->id()) << " ... " << std::flush;
	Oracle* oracle = new prover::Oracle(p);
	unique_ptr<prover::Space> space = make_unique<prover::Space>(*p->qeds().begin(), oracle);
	space->setMaxProofs(max_proofs);
	try {
		Return ret = space->prove();
		if (!ret.success()) {
			cout << "oracle test failed" << endl;
			cout << "oracle status:" << endl;
			cout << oracle->show() << endl;
			exit(-1);
		}
		return ret;
	} catch (Error& err) {
		err.msg += "\nwhile proving: " + show_id(p->theorem()->id()) + "\n";
		throw err;
	}
}

Return test_with_oracle(string theorem, uint max_proofs) {
	if (!theorem.size()) {
		struct SourceLess {
			bool operator () (const Source* s1, const Source* s2) const {
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
					if (counter == 2100) {
						cout << "AAA" << endl;
					}
					Timer timer; timer.start();
					Return r = test_proof_with_oracle(Theory::proof(n), max_proofs);
					timer.stop();
					cout << "done in " << timer << endl;
					if (!r.success()) {
						debug_oracle = true;
						test_proof_with_oracle(Theory::proof(n), max_proofs);
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
				Return r = test_proof_with_oracle(pr.get(), max_proofs);
					if (!r.success()) {
						debug_oracle = true;
						//test_proof_with_oracle(pr.get());
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
