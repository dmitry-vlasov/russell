#pragma once

#include "rus_prover_term.hpp"

namespace mdl { namespace rus { namespace prover {

enum class CompMode { SEMI, NORM, DUAL, DEFAULT = NORM };

struct Subst {
	Subst(bool ok = true) : ok_(ok) { }
	Subst(LightSymbol v, const Term& t) : ok_(true) {
		if (!(t.kind() == Term::VAR && t.var() == v)) {
			sub_.emplace(v.literal(), TypeTerm(v.type, t));
		}
	}
	Subst(LightSymbol v, Term&& t) : ok_(true) {
		if (!(t.kind() == Term::VAR && t.var() == v)) {
			sub_.emplace(v.literal(), TypeTerm(v.type, std::move(t)));
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
	bool compose(LightSymbol v, const Term& t, CompMode m = CompMode::DEFAULT, bool check = true) {
		return compose(Subst(v, t), m, check);
	}
	bool compose(Subst&& s, CompMode m = CompMode::DEFAULT, bool check = true);
	bool compose(LightSymbol v, Term&& t, CompMode m = CompMode::DEFAULT, bool check = true) {
		return compose(Subst(v, t), m, check);
	}
	bool compose(LightSymbol v, LightSymbol t, CompMode m = CompMode::DEFAULT, bool check = true) {
		return compose(Subst(v, Term(t)), m, check);
	}

	bool intersects(const Subst& s) const;
	bool maps(LightSymbol v) const {
		return maps(v.lit);
	}
	bool maps(uint v) const {
		return sub_.find(v) != sub_.end();
	}
	string show() const;
	string showVars(const set<uint>&) const;
	const Term& map(LightSymbol v) const {
		return map(v.lit);
	}
	const Term& map(uint v) const {
		auto it = sub_.find(v);
		if (sub_.find(v) != sub_.end()) {
			return it->second.term;
		} else {
			static Term empty; return empty;
		}
	}
	void erase(LightSymbol v) { erase(v.lit); }
	void erase(uint v) { sub_.erase(v); }

	struct TypeTerm {
		TypeTerm(const LightSymbol& v, const Term& t) : type(v.type), term(t) { }
		TypeTerm(const Type* tp, const Term& tr) : type(tp), term(tr) { }
		TypeTerm(const Type* tp, Term&& tr) : type(tp), term(std::move(tr)) { }
		TypeTerm(TypeTerm&&) = default;
		TypeTerm(const TypeTerm& tt) : type(tt.type), term(tt.term) { }
		const Type* type;
		Term term;
	};

	typedef hmap<uint, TypeTerm> Sub_;
	typedef Sub_::const_iterator const_iterator;

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
			p.second.term.verify();
		}
	}
	uint maxExprLen() const {
		uint l = 0;
		for (const auto& p : sub_) {
			l = std::max(p.second.term.len(), l);
		}
		return l;
	}
	Term apply(const Term& t) const;

private:
	friend struct VarMap;
	Sub_ sub_;
	bool ok_;
};

inline ostream& operator << (ostream& os, const Subst& s) {
	os << s.show(); return os;
}

Substitution Subst2Substitution(const Subst&);
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

inline ostream& operator << (ostream& os, const TermSubst& ts) {
	os << ts.show(); return os;
}

struct VarPair {
	VarPair() : from(-1), to(-1) { }
	VarPair(LightSymbol f, LightSymbol t) : from(f), to(t) {
		if (from.type != to.type) {
			throw Error("at variable replacement type should be preserved");
		}
	}
	VarPair invert() const { return VarPair(to, from); }
	const LightSymbol from;
	const LightSymbol to;
};

struct VarMap {
	bool compose(VarPair p) {
		auto it = repl.find(p.from.lit);
		if (it == repl.end()) {
			repl[p.from.lit] = p.to;
			return true;
		} else {
			return it->second == p.to;
		}
	}
	LightSymbol replace(LightSymbol v) const {
		auto iv = repl.find(v.lit);
		if (iv != repl.end()) {
			return iv->second;
		} else {
			return LightSymbol();
		}
	}
	uint apply(uint v, const Type* t) const {
		auto iv = repl.find(v);
		if (iv != repl.end()) {
			if (iv->second.type != t) {
				throw Error("at variable replacement type should be preserved");
			}
			return iv->second.lit;
		} else {
			return v;
		}
	}
	LightSymbol apply(LightSymbol v) const {
		v.lit = apply(v.lit, v.type);
		return v;
	}
	void apply(Term& t) const {
		for (auto& n : t.nodes) {
			if (n.ruleVar.isVar() && n.ruleVar.var.rep) {
				n.ruleVar.var = apply(n.ruleVar.var);
			}
		}
	}
	Term apply(const Term& t) const {
		Term ret(t);
		apply(ret);
		return ret;
	}
	void apply(Subst& s) const {
		Subst::Sub_ new_sub;
		for (auto& p : s.sub_) {
			apply(p.second.term);
			new_sub.emplace(
				apply(p.first, p.second.type),
				Subst::TypeTerm(p.second.type, std::move(p.second.term))
			);
		}
		s.sub_ = std::move(new_sub);
	}
	Subst apply(const Subst& s) const {
		Subst ret(s);
		apply(ret);
		return ret;
	}
	void apply(VarMap& vr) const {
		Repl_ new_repl;
		for (auto& p : vr.repl) {
			uint v = apply(p.first, p.second.type);
			LightSymbol im = apply(p.second);
			if (v != im.lit) {
				new_repl.emplace(v, im);
			}
		}
		vr.repl = std::move(new_repl);
	}
	VarMap apply(const VarMap& vr) const {
		VarMap ret;
		for (const auto& p : vr.repl) {
			uint v = apply(p.first, p.second.type);
			LightSymbol im = apply(p.second);
			if (v != im.lit) {
				ret.repl.emplace(v, im);
			} else {
				ret.repl.emplace(v, p.second);
			}
		}
		return ret;
	}
	string show() const {
		ostringstream oss;
		for (const auto& p : repl) {
			oss << Lex::toStr(p.first) << " --> " << p.second << endl;
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
	Subst subst() const {
		Subst ret;
		for (const auto& p : repl) {
			ret.compose(
				LightSymbol(p.first, p.second.type),
				Term(p.second),
				CompMode::NORM, false
			);
		}
		return ret;
	}

private:
	typedef hmap<uint, LightSymbol> Repl_;
	Repl_ repl;
};

inline ostream& operator << (ostream& os, const VarMap& vm) {
	os << vm.show(); return os;
}

struct VarRepl {
	VarRepl() = default;
	VarRepl inversed() const {
		return VarRepl(inverse_, direct_);
	}
	bool compose(VarPair p) {
		return direct_.compose(p) && inverse_.compose(p.invert());
	}
	VarRepl apply(const VarRepl& vr) const {
		return VarRepl(
			direct_.apply(vr.direct_),
			vr.inverse_.apply(inverse_)
		);
	}
	const VarMap& direct() const { return direct_; }
	const VarMap& inverse() const { return inverse_; }
	string show() const { return direct_.show(); }
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
	VarRepl(const VarMap& d, const VarMap& i) : direct_(d), inverse_(i) { }
	VarMap direct_;
	VarMap inverse_;
};

inline ostream& operator << (ostream& os, const VarRepl& vr) {
	os << vr.show(); return os;
}

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

inline ostream& operator << (ostream& os, const TermVarRepl& tvr) {
	os << tvr.show(); return os;
}

}}}
