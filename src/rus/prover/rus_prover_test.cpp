#include "../expr/rus_expr_stats.hpp"
#include "rus_prover_tactics.hpp"
#include "rus_prover_prover.hpp"

namespace mdl { namespace rus { namespace prover {

static vector<const Proof*> prove_failed;

static bool proof_has_shared(const Proof* p) {
	map<const Step*, vector<const Step*>> parents;
	for (const auto& e : p->elems) {
		if (const Step* parent = Proof::step(e)) {
			for (const auto& ref : parent->refs) {
				if (const Step* child = ref->step()) {
					parents[child].push_back(parent);
					if (parents[child].size() > 1) {
						return true;
					}
				}
			}
		}
	}
	return false;
}

Return test_proof_with_oracle(uint i, const Proof* p, uint max_proofs) {
	cout << (i == -1 ? "" : to_string(i) + " ")  << "testing proof of " << show_id(p->theorem()->id()) << " ... " << std::flush;
	Timer timer; timer.start();
	Oracle* oracle = new prover::Oracle(p);
	unique_ptr<prover::Prover> space = make_unique<prover::Prover>(*p->qeds().begin(), oracle);
	space->setMaxProofs(max_proofs);
	try {
		bool orig_proof_has_shared = proof_has_shared(p);

		if (orig_proof_has_shared) {
			cout << "ORIG _PROOF HAS SHARED:" << endl;
			cout << *p << endl;
		}

		Return ret = space->prove();
		if (!ret.success()) {
			//cout << "oracle test failed" << endl;
			cout << "oracle status:" << endl;
			cout << oracle->show() << endl;
			//exit(-1);
			prove_failed.push_back(p);
			cout << "FAILED ";
			cout << "original proof:" << endl;
			cout << *p << endl;
			exit(-1);
		}
		bool prover_proof_has_shared = proof_has_shared(space->proved().at(0).get());
		if (prover_proof_has_shared) {
			cout << "PROVER _PROOF HAS SHARED:" << endl;
			cout << *space->proved().at(0).get() << endl;
		}
		if (orig_proof_has_shared && !prover_proof_has_shared) {
			cout << "PROVER _PROOF HAS NO REFS:" << endl;
			cout << *space->proved().at(0).get() << endl;
			//exit(0);
		}


		timer.stop();
		cout << "done in " << timer << endl;
		return ret;
	} catch (Error& err) {
		err.msg += "\nwhile proving: " + show_id(p->theorem()->id()) + "\n";
		throw err;
	}
}

#ifdef PARALLEL
//#define PARALLEL_PROVER_TEST
#endif

Return test_all_with_oracle(uint max_proofs, uint max_proof_len) {
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
	vector<const Proof*> proofs;
	const Proof* longest_proof = nullptr;
	for (Source* src : ordered_sources) {
		//cout << "adding source: " << Lex::toStr(src->id()) << " to a test sample" << endl;
		for (auto& n : src->theory.nodes) {
			if (Theory::kind(n) == Theory::PROOF) {
				const Proof* proof = Theory::proof(n);
				uint proof_len = proof->elems.size();
				if (!longest_proof  || proof_len > longest_proof->elems.size()) {
					longest_proof = proof;
				}
				if (proof_len <= max_proof_len) {
					proofs.push_back(proof);
				}
			}
		}
	}
	cout << "longest proof: " << Lex::toStr(longest_proof->thm->id()) << ", proof length: " << longest_proof->elems.size() << endl;
#ifdef PARALLEL_PROVER_TEST
	tbb::parallel_for(tbb::blocked_range<size_t>(0, proofs.size()),
		[max_proofs, &proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				Return r = test_proof_with_oracle(i, proofs.at(i), max_proofs);
				if (!r.success()) {
					debug_oracle = true;
					cout << "TEST PROOF WITH ORACLE: BEGIN" << endl;
					test_proof_with_oracle(Theory::proof(n), max_proofs);
					cout << "TEST PROOF WITH ORACLE: END" << endl;
					return r;
				}
			}
		}
	);
#else
	for (uint i = 0; i < proofs.size(); ++ i) {
		Return r = test_proof_with_oracle(i, proofs.at(i), max_proofs);
		if (!r.success()) {
			debug_oracle = true;
			cout << "TEST PROOF WITH ORACLE: BEGIN" << endl;
			test_proof_with_oracle(i, proofs.at(i), max_proofs);
			cout << "TEST PROOF WITH ORACLE: END" << endl;
			return r;
		}
	}
#endif
	cout << "max_expr_length: " << expr::Stats::stats().maxLen() << endl;
	cout << "avg_expr_length: " << expr::Stats::stats().avgLen() << endl;
	cout << "dev_expr_length: " << expr::Stats::stats().devLen() << endl;
	cout << "max_expr: " << *expr::Stats::stats().maxLenExpr() << endl;
	cout << endl;
	cout << "failed proofs number: " << prove_failed.size() << endl;
	for (const Proof* p : prove_failed) {
		cout << Lex::toStr(p->theorem()->id()) << ", ";
	}
	cout << endl;
	print_statistics();
	return Return("Massive prover testing with oracle succeeded :)");
}

Return test_with_oracle(string theorem, uint max_proofs, uint max_proof_len) {
	if (!theorem.size()) {
		return test_all_with_oracle(max_proofs, max_proof_len);
	} else {
		const rus::Assertion* ass = Sys::get().math.get<rus::Assertion>().access(Lex::toInt(theorem));
		if (const rus::Theorem* th = dynamic_cast<const rus::Theorem*>(ass)) {
			for (const auto& pr : th->proofs) {
				Return r = test_proof_with_oracle(-1, pr.get(), max_proofs);
				if (!r.success()) {
					debug_oracle = true;
					//test_proof_with_oracle(pr.get());
					return r;
				}
				cout << "max_expr_length: " << expr::Stats::stats().maxLen() << endl;
				cout << "avg_expr_length: " << expr::Stats::stats().avgLen() << endl;
				cout << "dev_expr_length: " << expr::Stats::stats().devLen() << endl;
				cout << "max_expr: " << *expr::Stats::stats().maxLenExpr() << endl;
				cout << endl;
				print_statistics();
			}
			return Return(string("Prover testing of ") + theorem + " with oracle succeeded :)");
		} else {
			return Return(string("Prover testing of ") + theorem + " - is not a theorem");
		}
	}
}

}}}
