#include "rus_prover_unify_general.hpp"
#include "rus_prover_unify_terms.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

Subst unify_step(const Subst& s, const vector<uint>& vars, Term&& term) {
	Term applied = s.apply(term);
	vector<const Term*> to_unify({&applied});
	for (auto v : vars) {
		if (s.maps(v)) {
			const Term& t = s.map(v);
			if (!t.empty()) {
				to_unify.push_back(&t);
			} else {
				throw Error("empty term at unify_step");
			}
		}
	}
	try {
		TermSubst unified = unify_terms(to_unify);
		if (!unified.sub.ok()) {
			return Subst(false);
		}
		Subst ret(s);
		if (!ret.compose(unified.sub)) {
			return Subst(false);
		}
		for (auto v : vars) {
			if (!ret.compose(v, unified.term)) {
				return Subst(false);
			}
		}
		return ret;
	} catch (Error& err) {
		cout << endl << "unify_step: ERROR" << endl;
		for (auto t : to_unify) {
			cout << "TERM: " << endl;
			cout << t->show_pointers();
		}
		cout << endl;
		throw err;
	}
	return Subst(false);
}

}}}}
