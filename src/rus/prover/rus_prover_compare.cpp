#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus { namespace prover {

struct Ass {
	Ass(const Assertion& a, ReplMode mode) {
		for (const auto& h : a.hyps) {
			hyps.emplace_back(Tree2Term(*h->expr.tree(), mode, 0));
		}
		props.emplace_back(Tree2Term(*a.prop->expr.tree(), mode, 0));
	}
	Ass apply(const Subst& s) const {
		Ass a(*this);
		for (auto& h : a.hyps) {
			h = std::move(s.apply(h));
		}
		for (auto& p : a.props) {
			p = std::move(s.apply(p));
		}
		return a;
	}
	Ass(const Ass&) = default;
	Ass(Ass&&) = default;
	string show() const {
		string ret;
		for (auto& h : hyps) {
			ret += "hyp " + h.show() + "\n";
		}
		if (hyps.size()) {
			ret += "--------------\n";
		}
		for (auto& p : props) {
			ret += "prop " + p.show() + "\n";
		}
		return ret;
	}
	set<LightSymbol> vars() const {
		set<LightSymbol> ret;
		for (auto& h : hyps) {
			ret = std::move(sets_union(ret, h.vars()));
		}
		for (auto& p : props) {
			ret = std::move(sets_union(ret, p.vars()));
		}
		return ret;
	}
	vector<Term> hyps;
	vector<Term> props;
};

bool check_sub(const Ass& a1, const Ass& a2) {
	for (const auto& h : a1.hyps) {
		if (std::find(a2.hyps.begin(), a2.hyps.end(), h) == a2.hyps.end()) {
			return false;
		}
	}
	for (const auto& p : a2.props) {
		if (std::find(a1.props.begin(), a1.props.end(), p) == a1.props.end()) {
			return false;
		}
	}
	return true;
}

}

using namespace prover;

vector<Substitution> match(const Assertion& as1, const Assertion& as2) {
	Ass a10(as1, ReplMode::KEEP_REPL);
	Ass a2(as2, ReplMode::DENY_REPL);
	set<LightSymbol> a2_vars = a2.vars();
	set<LightSymbol> common_vars = sets_intersection(a10.vars(), a2_vars);
	Subst rename_common_vars;
	for (auto v : common_vars) {
		LightSymbol w = v;
		uint i = 0;
		while (a2_vars.find(w) != a2_vars.end()) {
			w.lit = Lex::toInt(Lex::toStr(v.lit) + "_" + to_string(i));
		}
		rename_common_vars.compose(v, w);
	}
	Ass a1 = a10.apply(rename_common_vars);
	typedef unify::IndexMap<uint> HypsMap;
	HypsMap hypsMap;
	for (uint i = 0; i < a2.hyps.size(); ++i) {
		hypsMap.add(a2.hyps.at(i), i);
	}

	//cout << "a1:" << endl << a1.show() << endl;
	//cout << "a2:" << endl << a2.show() << endl;

	Watchdog watchdog(1000, "match assertions " + Lex::toStr(as1.id()) + " and " + Lex::toStr(as2.id()));

	vector<unique_ptr<Subst>> subs;
	subs.emplace_back(make_unique<Subst>());
	for (const auto& a2_prop : a2.props) {
		vector<unique_ptr<Subst>> new_subs;
		for (const auto& sub : subs) {
			for (const auto& a1_prop : a1.props) {
				watchdog.check();
				Term a1_prop_prime = sub->apply(a1_prop);
				vector<Term> props;
				props.emplace_back(a2_prop);
				props.emplace_back(a1_prop_prime);
				unique_ptr<Subst> new_sub = make_unique<Subst>(*sub);
				unify::unify_general(props, *new_sub);
				if (new_sub->ok()) {
					new_subs.emplace_back(std::move(new_sub));
				}
			}
		}
		if (!new_subs.size()) {
			return vector<Substitution>();
		}
		subs = std::move(new_subs);
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
		if (!check_sub(a1.apply(*s), a2)) {
			string err;
			err += "wrong matching:\n";
			err += "a1:\n" + a1.show() + "\n";
			err += "a2:\n" + a2.show() + "\n";
			err += "sub:\n" + s->show() + "\n";
			throw Error(err);
		}
		ret.emplace_back(Subst2Substitution(*s));
	}
	return ret;
}

}} // mdl::rus::prover
