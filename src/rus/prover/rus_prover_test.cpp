#include "../expr/rus_expr_stats.hpp"
#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

static vector<const Proof*> prove_failed;

Return test_proof_with_oracle(uint i, const Proof* p, uint max_proofs) {
	cout << (i == -1 ? "" : to_string(i) + " ")  << "testing proof of " << show_id(p->theorem()->id()) << " ... " << std::flush;
	Timer timer; timer.start();
	Oracle* oracle = new prover::Oracle(p);
	unique_ptr<prover::Space> space = make_unique<prover::Space>(*p->qeds().begin(), oracle);
	space->setMaxProofs(max_proofs);
	try {
		Return ret = space->prove();
		if (!ret.success()) {
			//cout << "oracle test failed" << endl;
			//cout << "oracle status:" << endl;
			//cout << oracle->show() << endl;
			//exit(-1);
			prove_failed.push_back(p);
			cout << "FAILED ";
			exit(-1);
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
#define PARALLEL_PROVER_TEST
#endif

Return test_all_with_oracle(uint max_proofs) {
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
	for (Source* src : ordered_sources) {
		cout << "testing source: " << Lex::toStr(src->id()) << endl;
		for (auto& n : src->theory.nodes) {
			if (Theory::kind(n) == Theory::PROOF) {
				proofs.push_back(Theory::proof(n));
			}
		}
	}
#ifdef PARALLEL_PROVER_TEST
	tbb::parallel_for(tbb::blocked_range<size_t>(0, proofs.size()),
		[max_proofs, &proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				Return r = test_proof_with_oracle(i, proofs.at(i), max_proofs);
				/*if (!r.success()) {
					debug_oracle = true;
					test_proof_with_oracle(Theory::proof(n), max_proofs);
					return r;
				}*/
			}
		}
	);
#else
	for (uint i = 0; i < proofs.size(); ++ i) {
		Return r = test_proof_with_oracle(i, proofs.at(i), max_proofs);
		/*if (!r.success()) {
			debug_oracle = true;
			test_proof_with_oracle(Theory::proof(n), max_proofs);
			return r;
		}*/
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
	print_down_unification_statistics();
	return Return("Massive prover testing with oracle succeeded :)");
}

namespace index {
	extern Timer unify_timer;
	extern Timer intersect_timer;
}
extern Timer seq_unify;
extern Timer mat_unify;

Return test_with_oracle(string theorem, uint max_proofs) {
	if (!theorem.size()) {
		return test_all_with_oracle(max_proofs);
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
				print_down_unification_statistics();
				cout << "index::unify_timer: " << index::unify_timer << endl;
				cout << "index::intersect_timer: " << index::intersect_timer << endl;
				cout << "seq_unify: " << seq_unify << endl;
				cout << "mat_unify: " << mat_unify << endl;
				cout << endl;
				cout << "index::unify_timer: " << index::unify_timer.getCumulativeSeconds() << endl;
				cout << "index::intersect_timer: " << index::intersect_timer.getCumulativeSeconds() << endl;
				cout << "seq_unify: " << seq_unify.getCumulativeSeconds() << endl;
				cout << "mat_unify: " << mat_unify.getCumulativeSeconds() << endl;

			}
			return Return(string("Prover testing of ") + theorem + " with oracle succeeded :)");
		} else {
			return Return(string("Prover testing of ") + theorem + " - is not a theorem");
		}
	}
}


}}}
