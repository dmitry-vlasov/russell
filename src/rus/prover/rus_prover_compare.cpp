#include <rus_ast.hpp>
#include <rus/prover/rus_prover_ass.hpp>
#include <rus/prover/unify/rus_prover_unify.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus {

using namespace prover;

vector<Substitution> match(const Assertion& as1, const Assertion& as2) {
	Ass a1 = Ass(as1, ReplMode::KEEP_REPL).specialFreshVars();
	Ass a2(as2, ReplMode::DENY_REPL);

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
	if (new_sub->ok()) {
		subs.emplace_back(std::move(new_sub));
	} else {
		return vector<Substitution>();
	}
	for (const auto& a1_hyp : a1.hyps) {
		vector<unique_ptr<Subst>> new_subs;
		for (const auto& sub : subs) {
			Term a1_hyp_prime = sub->apply(a1_hyp);
			for (auto unified : hypsMap.unify(a1_hyp_prime)) {
				watchdog.check();
				unique_ptr<Subst> new_sub = make_unique<Subst>(*sub);
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
	for (const auto& s : subs) {
		if (a1.apply(*s) !=  a2) {
			string err;
			err += "wrong matching:\n";
			err += "a1:\n" + a1.show() + "\n";
			err += "a2:\n" + a2.show() + "\n";
			err += "sub:\n" + s->show() + "\n";
			throw Error(err);
		}
		Substitution sub = Subst2Substitution(*s);
		if (as1.disj.satisfies(sub)) {
			ret.emplace_back(sub);
		}
	}
	return ret;
}

}} // mdl::rus::prover
