#include <rus_ast.hpp>
#include <rus/prover/rus_prover_ass.hpp>
#include <rus/prover/unify/rus_prover_unify.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus {

using namespace prover;

bool debug_match = false;
extern bool debug_check_disj;

vector<Substitution> match(const Assertion& as1, const Assertion& as2) {
	Ass a0(as1, true);
	VarRepl renaming = specialFreshVars(a0.vars());
	Ass a1 = a0.apply(renaming);
	Ass a2(as2, false);

	typedef unify::IndexMap<uint> HypsMap;
	HypsMap hypsMap;
	for (uint i = 0; i < a2.hyps.size(); ++i) {
		hypsMap.add(a2.hyps.at(i), i);
	}
	Watchdog watchdog(1000, "match assertions " + Lex::toStr(as1.id()) + " and " + Lex::toStr(as2.id()));

	vector<unique_ptr<Subst>> subs;
	vector<Term> props;
	props.emplace_back(a1.prop);
	props.emplace_back(a2.prop);
	unique_ptr<Subst> new_sub = make_unique<Subst>();
	unify::unify_general(props, *new_sub);

	if (debug_match) {
		cout << "SUB_0: " << *new_sub << endl;
	}

	if (new_sub->ok()) {
		subs.emplace_back(std::move(new_sub));
	} else {
		return vector<Substitution>();
	}
	if (debug_match) {
		cout << "subs.size() = " << subs.size() << endl;
	}
	uint c = 0;
	for (const auto& a1_hyp : a1.hyps) {
		c += 1;
		if (debug_match) {
			cout << "hyp_" << c << endl;
		}
		vector<unique_ptr<Subst>> new_subs;
		for (const auto& sub : subs) {
			Term a1_hyp_prime = sub->apply(a1_hyp);
			for (auto unified : hypsMap.unify(a1_hyp_prime)) {
				watchdog.check();
				unique_ptr<Subst> new_sub = make_unique<Subst>(*sub);

				if (debug_match) {
					cout << "SUB_" << c << ": " << *new_sub << endl;
				}

				if (new_sub->compose(unified.sub)) {
					new_subs.emplace_back(std::move(new_sub));
				}
			}
			/*for (const auto& a2_hyp : a2.hyps) {
				vector<Term> hyps;
				hyps.emplace_back(a1_hyp_prime);
				hyps.emplace_back(a2_hyp);
				unique_ptr<Subst> new_sub = make_unique<Subst>(*sub);
				unify::unify_general(hyps, *new_sub);
				if (new_sub->ok()) {
					new_subs.emplace_back(std::move(new_sub));
				}
			}*/
		}
		if (!new_subs.size()) {
			return vector<Substitution>();
		}
		subs = std::move(new_subs);
	}
	vector<Substitution> ret;
	if (debug_match) {
		cout << "subs.size() = " << subs.size() << endl;
	}
	for (const auto& s : subs) {
		if (debug_match) {
				cout << "considering: " << endl << *s << endl;
			}
		if (a1.apply(*s) !=  a2) {
			string err;
			err += "wrong matching:\n";
			err += "a1:\n" + a1.show() + "\n";
			err += "a2:\n" + a2.show() + "\n";
			err += "sub:\n" + s->show() + "\n";
			if (debug_match) {
				cout << err << endl;
			}
			throw Error(err);
		}
		//Subst ss(*s);
		//renaming.inverse().apply(ss);
		Substitution sub = Subst2Substitution(*s);
		if (a1.disj.satisfies(sub, &as2.disj)) {
			if (debug_match) {
				cout << "ADDING subs.size() = " << subs.size() << endl;
			}
			ret.emplace_back(sub);
		} else {
			if (debug_match) {
				cout << "!as1.disj.satisfies(sub, as2.disj)" << endl;
				debug_check_disj = true;
				a1.disj.satisfies(sub, &as2.disj);
				cout << "as1.disj: " << a1.disj << endl;
				cout << "as2.disj: " << as2.disj << endl;
				cout << "subst: " << endl << sub << endl;
				cout << "as1: " << endl << as1 << endl;
				cout << "as2: " << endl << as2 << endl;
				debug_check_disj = false;
			}
		}
	}
	if (debug_match) {
		cout << "FINAL subs.size() = " << subs.size() << endl;
	}
	return ret;
}

}} // mdl::rus::prover
