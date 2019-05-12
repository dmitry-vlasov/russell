#include "rus_prover_unify_general.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

/*Subst unify_step(const Subst& s, const vector<uint>& vars, Term&& term) {
	vector<Term> to_unify({s.apply(term)});
	for (auto v : vars) {
		if (s.maps(v)) {
			const Term& t = s.map(v);
			if (!t.empty()) {
				to_unify.push_back(t);
			} else {
				throw Error("empty term at unify_step_1");
			}
		}
	}
	vector<Term::Iter> iters;
	for (const auto& t : to_unify) {
		iters.emplace_back(t);
	}
	UnifyIters begin = UnifyIters(iters);
	Subst ret(s);
	try {
		vector<UnifyPair> pairs = do_unify_general(begin);
		if (pairs.size() > 1) {
			throw Error("too much unified pairs: " + to_string(pairs.size()));
		}
		if (pairs.size() == 1) {
			const UnifyPair& pair = pairs.at(0);
			if (!ret.compose(pair.end.sub)) {
				return Subst(false);
			}
			Term term_orig = pair.subTerm();
			Term unified = pair.end.sub.apply(term_orig);
			for (auto v : vars) {
				if (!ret.compose(Subst(v, unified))) {
					return Subst(false);
				}
			}
			return ret;
		}
	} catch (Error& err) {
		cout << endl << "unify_step_1: ERROR" << endl;
		for (const auto& t : to_unify) {
			cout << "TERM: " << endl;
			cout << t.show_pointers();
		}
		cout << endl;
		throw err;
	}
	return Subst(false);
}*/

}}}}
