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
	friend struct VarMap;
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

struct VarPair {
	VarPair() : from(-1), to(-1) { }
	VarPair(uint f, uint t) : from(f), to(t) { }
	bool isDefined() const { return from == -1; }
	VarPair invert() const { return VarPair(to, from); }
	const uint from;
	const uint to;
};

struct VarMap {
	bool compose(VarPair p) {
		auto it = repl.find(p.from);
		if (it == repl.end()) {
			repl[p.from] = p.to;
			return true;
		} else {
			return it->second == p.to;
		}
	}
	uint replace(uint v) const {
		auto iv = repl.find(v);
		if (iv != repl.end()) {
			return iv->second;
		} else {
			return -1;
		}
	}
	uint apply(uint v) const {
		auto iv = repl.find(v);
		if (iv != repl.end()) {
			return iv->second;
		} else {
			return v;
		}
	}
	void apply(Term& t) const {
		for (auto& n : t.nodes) {
			if (n.ruleVar.isVar() && n.ruleVar.var.rep) {
				n.ruleVar.var.lit = apply(n.ruleVar.var.lit);
			}
		}
	}
	Term apply(const Term& t) const {
		Term ret(t);
		apply(ret);
		return ret;
	}
	void apply(Subst& s) const {
		hmap<uint, Term> new_sub;
		for (auto& p : s.sub_) {
			apply(p.second);
			new_sub[apply(p.first)] = std::move(p.second);
		}
		s.sub_ = std::move(new_sub);
	}
	Subst apply(const Subst& s) const {
		Subst ret(s);
		apply(ret);
		return ret;
	}
	void apply(VarMap& vr) const {
		hmap<uint, uint> new_repl;
		for (auto& p : vr.repl) {
			new_repl[apply(p.first)] = apply(p.second);
		}
		vr.repl = std::move(new_repl);
	}
	string show() const {
		ostringstream oss;
		for (const auto& p : repl) {
			oss << Lex::toStr(p.first) << " --> " << Lex::toStr(p.second) << endl;
		}
		return oss.str();
	}
	bool operator == (const VarMap& vr) const {
		return repl == vr.repl;
	}
	bool operator != (const VarMap& vr) const {
		return !operator == (vr);
	}
	uint size() const {
		return repl.size();
	}

private:
	hmap<uint, uint> repl;
};

struct VarRepl {
	bool compose(VarPair p) {
		return direct_.compose(p) && inverse_.compose(p.invert());
	}
	void apply(VarRepl& vr) const {
		direct_.apply(vr.direct_);
		inverse_.apply(vr.inverse_);
	}
	const VarMap& direct() const { return direct_; }
	const VarMap& inverse() const { return inverse_; }
	string show() const {
		return direct_.show();
	}
	bool operator == (const VarRepl& vr) const {
		return direct_ == vr.direct_;
	}
	bool operator != (const VarRepl& vr) const {
		return !operator == (vr);
	}
	uint size() const {
		return direct_.size();
	}

private:
	VarMap direct_;
	VarMap inverse_;
};

struct TermVarRepl {
	TermVarRepl() = default;
	TermVarRepl(const Term& t, const VarRepl& r) : term(t), repl(r) { }
	TermVarRepl(Term&& t, VarRepl&& r) : term(std::move(t)), repl(std::move(r)) { }
	TermVarRepl(const TermVarRepl&) = default;
	TermVarRepl(TermVarRepl&&) = default;

	string show() const {
		return "term: " + term.show() + "\nreplacement:\n" + repl.show();
	}
	bool operator == (const TermVarRepl& ts) const {
		return term == ts.term && repl == ts.repl;
	}
	bool operator != (const TermVarRepl& ts) const {
		return !operator == (ts);
	}
	bool isDefault() const {
		return !term.len() && !repl.size();
	}

	Term term;
	VarRepl repl;
};

}}}
