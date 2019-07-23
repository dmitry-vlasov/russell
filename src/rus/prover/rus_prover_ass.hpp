#pragma once

#include <rus/prover/rus_prover_subst.hpp>

namespace mdl { namespace rus { namespace prover {

struct Ass {
	Ass(const Assertion& a, ReplMode mode) : prop(Tree2Term(*a.prop->expr.tree(), mode, 0)) {
		for (const auto& h : a.hyps) {
			hyps.emplace_back(Tree2Term(*h->expr.tree(), mode, 0));
		}
	}
	Ass apply(const Subst& s) const {
		Ass a(*this);
		for (auto& h : a.hyps) {
			h = std::move(s.apply(h));
		}
		a.prop = std::move(s.apply(prop));
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
		ret += "prop " + prop.show() + "\n";
		return ret;
	}
	set<LightSymbol> vars() const {
		set<LightSymbol> ret;
		for (auto& h : hyps) {
			ret = std::move(sets_union(ret, h.vars()));
		}
		ret = std::move(sets_union(ret, prop.vars()));
		return ret;
	}
	Ass specialFreshVars() const {
		Ass a(*this);
		Subst rename_vars;
		for (auto v : vars()) {
			LightSymbol w = v;
			w.lit = Lex::toInt(Lex::toStr(v.lit) + "_,_");
			rename_vars.compose(v, w);
		}
		return a.apply(rename_vars);
	}
	bool operator == (const Ass& a) const {
		for (const auto& h : hyps) {
			if (std::find(a.hyps.begin(), a.hyps.end(), h) == a.hyps.end()) {
				return false;
			}
		}
		return prop == a.prop;
	}
	bool operator != (const Ass& a) const {
		return !operator == (a);
	}
	vector<Term> hyps;
	Term prop;
};

}}}
