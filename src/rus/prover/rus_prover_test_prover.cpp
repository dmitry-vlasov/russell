#include "../expr/rus_expr_stats.hpp"
#include "rus_prover_tactics.hpp"
#include "rus_prover_prover.hpp"

namespace mdl { namespace rus { namespace prover {

static vector<const Proof*> prove_failed;

static bool proof_has_shared(const Proof* p) {
	map<const Step*, vector<const Step*>> parents;
	for (const auto& s : p->steps) {
		for (const auto& ref : s->refs) {
			if (const Step* child = ref->step()) {
				parents[child].push_back(s.get());
				if (parents[child].size() > 1) {
					return true;
				}
			}
		}
	}
	return false;
}

Return test_proof_with_oracle(uint i, Proof* p, uint max_proofs) {
	string msg;
	msg +=  "testing proof of " + Lex::toStr(p->theorem->id()) + string(i == -1 ? "" : " (no. " + to_string(i) + ")") + " ... ";
	Timer timer; timer.start();
	Oracle* oracle = new prover::Oracle(p);
	prover::Prover prover(p->qed(), oracle);
	prover.setMaxProofs(max_proofs);
	try {
		//bool orig_proof_has_shared = proof_has_shared(p);

		/*if (orig_proof_has_shared) {
			cout << "ORIG _PROOF HAS SHARED:" << endl;
			cout << *p << endl;
		}*/

		Return ret = prover.prove();
		if (!ret.success()) {
			//cout << "oracle test failed" << endl;
			cout << "oracle status:" << endl;
			cout << oracle->show() << endl;
			//exit(-1);
			prove_failed.push_back(p);
			cout << "FAILED ";
			cout << "original theorem:" << endl;
			cout << *p->theorem << endl;
			exit(-1);
		}
		bool prover_proof_has_shared = proof_has_shared(prover.proved().at(0).get());
		/*if (prover_proof_has_shared) {
			cout << "PROVER _PROOF HAS SHARED:" << endl;
			cout << *prover.proved().at(0).get() << endl;
		}
		if (orig_proof_has_shared && !prover_proof_has_shared) {
			cout << "PROVER _PROOF HAS NO REFS:" << endl;
			cout << *prover.proved().at(0).get() << endl;
			//exit(0);
		}*/


		timer.stop();
		msg += "done in " + timer.show() + "\n";
		Io::io().println(msg);
		return ret;
	} catch (Error& err) {
		err.msg += "\nwhile proving: " + show_id(p->theorem->id()) + "\n";
		throw err;
	}
}

#ifdef PARALLEL
#define PARALLEL_PROVER_TEST
#endif

Return test_all_with_oracle(uint max_proofs, uint max_proof_len) {
	cout << endl;
#ifdef PARALLEL_PROVER_TEST
	vector<Assertion*> assertions = Sys::mod().math.get<Assertion>().values();
#else
	vector<Assertion*> assertions = Sys::mod().math.get<Assertion>().sortedValues(
		[](const Assertion* a1, const Assertion* a2) {
			return a1->token.preceeds(a2->token);
		}
	);
#endif
	vector<Proof*> proofs;
	const Proof* longest_proof = nullptr;
	for (Assertion* ass : assertions) {
		//cout << "adding source: " << Lex::toStr(src->id()) << " to a test sample" << endl;
		if (Theorem* theorem = dynamic_cast<Theorem*>(ass)) {
			Proof* proof = theorem->proof.get();
			uint proof_len = proof->steps.size();
			if (!longest_proof  || proof_len > longest_proof->steps.size()) {
				longest_proof = proof;
			}
			if (proof_len <= max_proof_len) {
				proofs.push_back(proof);
			}
		}
	}
	Io::io().out() << "longest proof: " << Lex::toStr(longest_proof->theorem->id()) << ", proof length: " << longest_proof->steps.size() << endl;
#ifdef PARALLEL_PROVER_TEST
	tbb::parallel_for(tbb::blocked_range<size_t>(0, proofs.size()),
		[max_proofs, &proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				Return r = test_proof_with_oracle(i, proofs.at(i), max_proofs);
				if (!r.success()) {
					debug_oracle = true;
					cout << "TEST PROOF WITH ORACLE: BEGIN" << endl;
					test_proof_with_oracle(i, proofs.at(i), max_proofs);
					cout << "TEST PROOF WITH ORACLE: END" << endl;
					return r;
				}
			}
			return Return();
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
		cout << Lex::toStr(p->theorem->id()) << ", ";
	}
	cout << endl;
	print_statistics();
	return Return("Massive prover testing with oracle succeeded :)");
}

Return test_with_oracle(string theorem, uint max_proofs, uint max_proof_len) {
	if (!theorem.size()) {
		return test_all_with_oracle(max_proofs, max_proof_len);
	} else {
		rus::Assertion* ass = Sys::mod().math.get<rus::Assertion>().access(Lex::toInt(theorem));
		if (rus::Theorem* th = dynamic_cast<rus::Theorem*>(ass)) {
			if (rus::Proof* pr = th->proof.get()) {
				Return r = test_proof_with_oracle(-1, pr, max_proofs);
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
