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
	Subst(uint v, Term&& t) : ok_(true) {
		if (!(t.kind() == Term::VAR && t.var() == v)) {
			sub_.emplace(v, std::move(t));
		}
	}
	Subst(const Subst& s) = default;
	Subst(Subst&& s) = default;

	Subst& operator = (const Subst& s) = default;
	Subst& operator = (Subst&& s) = default;

	bool operator == (const Subst& s) const;
	bool operator != (const Subst& s) const;

	bool consistent(const Subst& s) const;
	bool compose(const Subst& s, CompMode m = CompMode::DEFAULT, bool check = true);
	bool compose(uint v, const Term& t, CompMode m = CompMode::DEFAULT, bool check = true) {
		return compose(Subst(v, t), m, check);
	}
	bool compose(Subst&& s, CompMode m = CompMode::DEFAULT, bool check = true);
	bool compose(uint v, Term&& t, CompMode m = CompMode::DEFAULT, bool check = true) {
		Subst s(v, t);
		return compose(std::move(s), m, check);
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
	friend struct VarRepl;
	hmap<uint, Term> sub_;
	bool ok_;
};

Subst Substitution2FlatSubst(const Substitution&);
Substitution FlatSubst2Substitution(const Subst&);
string show_diff(const Subst& s1, const Subst& s2);

struct TermSubst {
	TermSubst() = default;
	TermSubst(const Term& t, const Subst& s) : term(t), sub(s) { }
	TermSubst(Term&& t, Subst&& s) : term(std::move(t)), sub(std::move(s)) { }
	TermSubst(const TermSubst& ts) = default;
	TermSubst(TermSubst&&) = default;

	string show() const {
		return "term: " + term.show() + "\nsub:\n" + sub.show();
	}
	bool operator == (const TermSubst& ts) const {
		return term == ts.term && sub == ts.sub;
	}
	bool operator != (const TermSubst& ts) const {
		return !operator == (ts);
	}
	bool isDefault() const {
		return !term.len() && !sub.size();
	}

	Term term;
	Subst sub;
};

struct VarRepl {
	void addReplacement(uint v, uint w) {
		replacement_[v] = w;
	}
	uint replace(uint v) const {
		auto iv = replacement_.find(v);
		if (iv != replacement_.end()) {
			return iv->second;
		} else {
			return -1;
		}
	}
	void apply(Term& t) const {
		for (auto& n : t.nodes) {
			if (n.ruleVar.isVar() && n.ruleVar.var.rep) {
				auto ri = replacement_.find(n.ruleVar.var.lit);
				if (ri != replacement_.end()) {
					n.ruleVar.var.lit = ri->second;
				}
			}
		}
	}
	void apply(Subst& s) const {
		hmap<uint, Term> new_sub;
		for (auto& p : s.sub_) {
			apply(p.second);
			uint var = p.first;
			auto ri = replacement_.find(var);
			if (ri != replacement_.end()) {
				var = ri->second;
			}
			new_sub[var] = std::move(p.second);
		}
		s.sub_ = std::move(new_sub);
	}
	string show() const {
		ostringstream oss;
		for (const auto& p : replacement_) {
			oss << Lex::toStr(p.first) << " --> " << Lex::toStr(p.second) << endl;
		}
		return oss.str();
	}

private:
	hmap<uint, uint> replacement_;
};

}}}
