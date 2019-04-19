#include "rus_prover_multy_subst.hpp"
#include "index/rus_prover_index_unify.hpp"

namespace mdl { namespace rus { namespace prover {

MultySubst::MultySubst(const vector<const Subst*>& subs) {
	for (auto s : subs) {
		add(s);
	}
}

bool debug_make_subs = false;

Subst MultySubst::makeSubs(Subst& unif) const {
	Subst ret;

	set<uint> vars;
	vars.insert(var_dom);
	vars.insert(var_im);

	for (const auto& p : msub_) {

		/*bool has_vars = true;
		if (debug_test_case) {
			for (const Term& t : p.second) {
				if (!(t.vars().count(var_dom) || t.vars().count(var_im))) {
					has_vars = false;
					break;
				}
			}
			if (has_vars) {
				cout << "TERM VECTOR:" << endl;
				for (const Term& t : p.second) {
					cout << "\t" << t.show() << endl;
				}
				cout << endl;
			}
		}*/

		Term term = index::unify_general(p.second, unif);

		bool show_it = debug_make_subs || (debug_test_case && (
			(p.first == var_dom && term.kind() == Term::VAR && term.var().lit == var_im ) ||
			(p.first == var_im && term.kind() == Term::VAR && term.var().lit == var_dom ) ||
			(unif.maps(var_im) && unif.map(var_im).kind() == Term::VAR && unif.map(var_im).var().lit == var_dom) ||
			(unif.maps(var_dom) && unif.map(var_dom).kind() == Term::VAR && unif.map(var_dom).var().lit == var_im)
			));

		if (show_it) {
			cout << "VAR: " << Lex::toStr(p.first) << endl;
			cout << "UNIFIED TERM:" << endl;
			cout << "\t" << term.show() << endl;
			cout << endl;
			cout << "UNIFIER:" << endl;
			cout << unif.show() << endl;
			cout << endl;
			cout << "RET: (before)" << endl;
			cout << ret.show();
			if (term.empty()) {
				cout << "p.second:" << endl;
				for (const auto& x : p.second) {
					cout << "\t" << x.show() << endl;
				}
			}
		}

		if (term.empty()) {
			return Subst(false);
		}
		ret.compose(p.first, term);

		if (show_it) {
			cout << "RET: (after)" << endl;
			cout << ret.show();
			cout << "--------------------------" << endl << endl;
		}

		if (!ret.ok()) {
			break;
		}
	}
	if (debug_make_subs) {
		cout << "FINAL RET: " << endl;
		cout << ret.show() << endl;
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

Subst unify_subs(const MultySubst& t) {
	Subst unif;
	Subst gen = t.makeSubs(unif);
	if (debug_test_case) {
		cout << "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^" << endl;
		cout << t.show() << endl;
		cout << "GEN:" << endl;
		cout << gen.show() << endl;
		cout << "UNIF:" << endl;
		cout << unif.show() << endl;
		if (!gen.ok()) {
			debug_make_subs = true;
			Subst unif1;
			Subst gen1 = t.makeSubs(unif1);
			cout << "GEN1:" << endl;
			cout << gen1.show() << endl;
		}
	}
	Subst ret = unify_subs(unif, gen);
	if (debug_test_case) {
		cout << "RET:" << endl;
		cout << ret.show() << endl;
		cout << "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^" << endl;
	}
	return ret;
}

Subst unify_subs(Subst unif, Subst gen) {
	if (!(gen.ok() && unif.ok())) {
		return Subst(false);
	}
	if (!gen.intersects(unif)) {
		if (gen.compose(unif)) {
			sub_closure(gen);
			return gen;
		} else {
			return Subst(false);
		}
	} else {
		MultySubst msub({&unif, &gen});
		return unify_subs(msub);
	}
}

string show(const MultyUnifiedSubs& ms) {
	ostringstream oss;
	for (const auto& p : ms) {
		oss << show(p.first) << ":" << endl;
		oss << Indent::paragraph(p.second.show()) << endl;
	}
	return oss.str();
}

}}}
