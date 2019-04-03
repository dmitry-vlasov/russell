#include "rus_prover_multy_subst.hpp"
#include "rus_prover_unify.hpp"
#include "trie_index/rus_prover_trie_unify.hpp"

namespace mdl { namespace rus { namespace prover {

MultySubst::MultySubst(const vector<const Subst*>& subs) {
	for (auto s : subs) {
		add(s);
	}
}
Subst MultySubst::makeSubs(Subst& unif) const {
	Subst ret;
	uint c = 0;
	if (debug_unify_subs_func) {
		cout << "--- MultySubst::makeSubs ---" << endl;
	}
	for (const auto& p : msub_) {
		if (debug_unify_subs_func) {
			cout << "TO UNIFY: " << c++ << endl;
			for (auto e : p.second) {
				cout << e.show() << endl;
			}
		}
		Subst unif1 = unif;
		Term term1 = trie_index::unify_general(p.second, unif1);
		Subst unif2 = unif;
		Term term2 = unify(p.second, unif2);
		if (term1 != term2) {
			cout << "vot ono, nachalos !!" << endl;
			cout << "ex:" << endl;
			for (const auto& e : p.second) {
				cout << "\t" << e.show() << endl;
			}
			cout << "unif:" << endl << unif.show() << endl;
			cout << "term1: " << term1.show() << endl;
			cout << "term2: " << term2.show() << endl;
			cout << "unif1: " << unif1.show() << endl;
			cout << "unif2: " << unif2.show() << endl;
			trie_index::debug_unify_general = true;
			trie_index::unify_general(p.second, unif);
			cout << "AAA" << endl;
			exit(-1);
		}

		Term term = unify(p.second, unif);
		if (term.empty()) {
			return Subst(false);
		}
		/*FlatTerm un = unify(p.second, unif);
		if (debug_unify_subs_func && c == 6) {
			if (c == 6) {
				cout << "AAA" << endl;
			}
			cout << "RET: " << endl;
			cout << ret.show() << endl;
			cout << "UNIF:" << endl;
			cout << unif.show() << endl;
			cout << "p.first: " << Lex::toStr(p.first) << endl;
			cout << "p.second:" << endl << "---------------" << endl;
			for (const auto& tree : p.second) {
				cout << tree.show() << endl;
			}
			cout << "---------------" << endl;
			cout << "unify(p.second, unif):" << endl;
			cout << un.show() << endl;
		}*/

		ret.compose(p.first, term);
		if (!ret.ok()) {
			if (debug_unify_subs_func) {
				cout << "SSSSSSSSSSSSSSSS" << endl;
				cout << "RET: " << endl;
				cout << ret.show() << endl;
				cout << "UNIF:" << endl;
				cout << unif.show() << endl;
			}
			break;
		}
	}
	return ret;
}

void MultySubst::add(const Subst* sub) {
	for (const auto& p : *sub) {
		msub_[p.first].push_back(p.second);
	}
}

void sub_closure(Subst& sub) {
	enum { WATCHDOG_THRESHOLD = 32 };
	uint watchdog = 0;
	while (sub.composeable(sub)) {
		if (watchdog++ > WATCHDOG_THRESHOLD) {
			cout << "SOMETHING WRONG: too much deep substitution closure" << endl;
			break;
		}
		if (!sub.compose(sub)) {
			break;
		}
	}
}

bool debug_unify_subs_func = false;

Subst unify_subs(const MultySubst& t) {
	if (debug_unify_subs_func) {
		cout << "unify_subs(const MultySubst& t): " << t.show() << endl;
	}
	Subst unif;
	Subst gen = t.makeSubs(unif);
	return unify_subs(unif, gen);
}

Subst unify_subs(Subst unif, Subst gen) {
	if (!(gen.ok() && unif.ok())) {
		return Subst(false);
	}
	if (debug_unify_subs_func) {
		cout << "--- unify_subs ---" << endl;
		cout << "UNIF:" << endl;
		cout << unif.show() << endl;
		cout << "GEN:" << endl;
		cout << gen.show() << endl;
	}
	if (!gen.intersects(unif)) {
		if (debug_unify_subs_func) {
			cout << "intersects == false" << endl;
		}
		if (gen.compose(unif)) {
			if (debug_unify_subs_func) {
				cout << "gen.compose(unif)"  << endl;
			}
			sub_closure(gen);
			return gen;
		} else {
			if (debug_unify_subs_func) {
				cout << "!!!!!!!!!! gen.compose(unif)"  << endl;
			}
			return Subst(false);
		}
	} else {
		MultySubst msub({&unif, &gen});
		Subst ret = unify_subs(msub);
		if (debug_unify_subs_func) {
			cout << "ret:" << endl;
			cout << ret.show() << endl;
		}
		return ret;
	}
}

}}}
