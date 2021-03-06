#include "../expr/rus_expr_stats.hpp"
#include "rus_prover_maker.hpp"

namespace mdl { namespace rus { namespace prover {

static vector<const Proof*> prove_failed;

Return test_proof_maker(uint i, const Proof* p) {
	cout << (i == -1 ? "" : to_string(i) + " ")  << "testing proof maker of " << show_id(p->theorem->id()) << " ... " << std::flush;
	Timer timer; timer.start();
	AbstProof abstProof = p->abst();
	try {
		unique_ptr<Theorem> ret = make_theorem(abstProof, Lex::toInt("remaked_" + Lex::toStr(p->theorem->id())));
		if (!ret) {
			prove_failed.push_back(p);
			cout << "FAILED ";
			cout << "original proof:" << endl;
			cout << *p << endl;
			exit(-1);
		}
		try {
			vector<Substitution> matches1 = match(*ret, *p->theorem);
			if (!matches1.size()) {
				string err;
				err += "wrong proof remaked\n";
				err += "ret.theorem:\n" + ret->show() + "\n";
				err += "p->theorem:\n" + p->theorem->show() + "\n";
				throw Error(err);
			}
			vector<Substitution> matches2 = match(*p->theorem, *ret);
			if (!matches2.size()) {
				beautify(*ret);
				cout << "strongly more general remaked theorem" << endl;
				cout << "ret.theorem:\n" << ret->show() << endl;
				cout << "p->theorem:\n" << p->theorem->show() << endl;
			}
		} catch (Timeout& timeout) {
			cout << timeout.what();
		}

		timer.stop();
		cout << "done in " << timer << endl;
		return Return(bool(ret));
	} catch (Error& err) {
		err.msg += "\nwhile making: " + show_id(p->theorem->id()) + "\n";
		throw err;
	}
}

#ifdef PARALLEL
//#define PARALLEL_MAKER_TEST
#endif

Return test_all_maker() {
	struct SourceLess {
		bool operator () (const Source* s1, const Source* s2) const {
			return s1->id() < s2->id();
		}
	};
	set<Source*, SourceLess> ordered_sources;
	for (Source& s : Sys::mod().math.get<Source>()) {
		ordered_sources.insert(&s);
	}
	cout << endl;
	vector<const Proof*> proofs;
	for (Source* src : ordered_sources) {
		//cout << "adding source: " << Lex::toStr(src->id()) << " to a test sample" << endl;
		for (auto& n : src->theory.nodes) {
			if (const Theorem* th = Theory::theorem(n)) {
				if (th->proof) {
					proofs.push_back(th->proof.get());
				}
			}
		}
	}
#ifdef PARALLEL_MAKER_TEST
	tbb::parallel_for(tbb::blocked_range<size_t>(0, proofs.size()),
		[max_proofs, &proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				Return r = test_proof_maker(i, proofs.at(i));
				if (!r.success()) {
					debug_oracle = true;
					cout << "TEST PROOF WITH ORACLE: BEGIN" << endl;
					test_proof_maker(Theory::proof(n));
					cout << "TEST PROOF WITH ORACLE: END" << endl;
					return r;
				}
			}
		}
	);
#else
	for (uint i = 0; i < proofs.size(); ++ i) {
		Return r = test_proof_maker(i, proofs.at(i));
		if (!r.success()) {
			cout << "TEST PROOF WITH ORACLE: BEGIN" << endl;
			test_proof_maker(i, proofs.at(i));
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

Return test_maker(string theorem) {
	if (!theorem.size()) {
		return test_all_maker();
	} else {
		const rus::Assertion* ass = Sys::get().math.get<rus::Assertion>().access(Lex::toInt(theorem));
		if (const rus::Theorem* th = dynamic_cast<const rus::Theorem*>(ass)) {
			if (const Proof* pr = th->proof.get()) {
				Return r = test_proof_maker(-1, pr);
				if (!r.success()) {
					//debug_oracle = true;
					//test_proof_maker(pr.get());
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
