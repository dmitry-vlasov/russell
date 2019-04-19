#pragma once

#include "rus_prover_term.hpp"

namespace mdl { namespace rus { namespace prover {

enum class CompMode { SEMI, NORM, DUAL, DEFAULT = NORM };

struct Subst {
	Subst(bool ok = true) : ok_(ok) { }
	Subst(uint v, const Term& t) : ok_(true) {
		if (!(t.kind() == Term::VAR && t.var() == v)) {
			sub_.emplace(v, t);
		}
	}
	Subst(const Subst& s) : ok_(s.ok_) {
		operator = (s);
	}
	Subst(Subst&& s) : ok_(s.ok_) {
		operator = (std::move(s));
	}
	void operator = (const Subst& s);
	void operator = (Subst&& s);

	bool operator == (const Subst& s) const;
	bool operator != (const Subst& s) const;

	bool consistent(const Subst& s) const;
	bool compose(const Subst& s, CompMode m = CompMode::DEFAULT, bool check = true);
	bool compose(uint v, const Term& t, CompMode m = CompMode::DEFAULT, bool check = true) {
		return compose(Subst(v, t), m, check);
	}

	bool intersects(const Subst& s) const;
	bool maps(uint v) const { return sub_.find(v) != sub_.end(); }
	bool maps(LightSymbol s) const { return maps(s.lit); }
	string show() const;
	string showVars(const set<uint>&) const;
	const Term& map(uint v) const {
		auto it = sub_.find(v);
		if (sub_.find(v) != sub_.end()) {
			return it->second;
		} else {
			static Term empty; return empty;
		}
	}
	const Term& map(LightSymbol s) const {
		return map(s.lit);
	}
	void erase(uint v) { sub_.erase(v); }

	typedef hmap<uint, Term>::const_iterator const_iterator;

	const_iterator begin() const { return sub_.cbegin(); }
	const_iterator end() const { return sub_.cend(); }

	uint size() const { return sub_.size(); }
	bool ok() const { return ok_; }
	set<uint> dom() const {
		set<uint> ret;
		for (const auto& p : sub_) {
			ret.insert(p.first);
		}
		return ret;
	}
	Subst complement(const set<uint>& vars) const {
		Subst ret(*this);
		for (const auto& v : vars) {
			ret.sub_.erase(v);
		}
		return ret;
	}
	void spoil() { ok_ = false; }
	void verify() const {
		for (const auto& p : sub_) {
			p.second.verify();
		}
	}
	uint maxExprLen() const {
		uint l = 0;
		for (const auto& p : sub_) {
			l = std::max(p.second.len(), l);
		}
		return l;
	}
	Term apply(const Term& t) const;

private:
	hmap<uint, Term> sub_;
	bool ok_;
};

Subst Substitution2FlatSubst(const Substitution&);
Substitution FlatSubst2Substitution(const Subst&);

string show_diff(const Subst& s1, const Subst& s2);

}}}
