#pragma once

#include <rus/prover/rus_prover_subst.hpp>

namespace mdl { namespace rus { namespace prover {

struct Ass {
	Ass(const Assertion& a, bool is_mutable) :
		disj(a.disj),
		prop(Tree2Term(*a.prop->expr.tree(), is_mutable, true))
	{
		for (const auto& h : a.hyps) {
			hyps.emplace_back(Tree2Term(*h->expr.tree(), is_mutable, true));
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
	Ass apply(const VarRepl& r) const {
		Ass a(*this);
		for (auto& h : a.hyps) {
			h = std::move(r.apply(h));
		}
		a.prop = std::move(r.apply(prop));
		a.disj.dvars.clear();
		for (auto& p : disj.dvars) {
			a.disj.dvars.emplace(r.apply(p.v), r.apply(p.w));
		}
		return a;
	}
	Ass(const Ass&) = default;
	Ass(Ass&&) = default;
	string show() const {
		string ret;
		ret += disj.show() + "\n";
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
	Disj disj;
	vector<Term> hyps;
	Term prop;
};

inline ostream& operator << (ostream& os, const Ass& a) {
	os << a.show();
	return os;
}

}}}
