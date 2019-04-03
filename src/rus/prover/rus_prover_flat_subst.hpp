#pragma once

#include "rus_prover_flat_term.hpp"

namespace mdl { namespace rus { namespace prover {

struct FlatSubst {
	FlatSubst(bool ok = true) : ok_(ok) { }
	FlatSubst(uint v, const FlatTerm& t) : ok_(true) {
		if (!(t.kind() == FlatTerm::VAR && t.var() == v)) {
			sub_.emplace(v, t);
		}
	}
	FlatSubst(const FlatSubst& s) : ok_(s.ok_) {
		operator = (s);
	}
	FlatSubst(FlatSubst&& s) : ok_(s.ok_) {
		operator = (std::move(s));
	}
	void operator = (const FlatSubst& s);
	void operator = (FlatSubst&& s);

	bool operator == (const FlatSubst& s) const;
	bool operator != (const FlatSubst& s) const;

	bool consistent(const FlatSubst& s) const;
	bool compose(const FlatSubst& s, bool full = true);
	bool compose(uint v, const FlatTerm& t, bool full = true) { return compose(FlatSubst(v, t), full); }
	bool bicompose(const FlatSubst& s);
	bool intersects(const FlatSubst& s) const;
	bool composeable(const FlatSubst& s) const;

	bool maps(uint v) const { return sub_.find(v) != sub_.end(); }
	bool maps(LightSymbol s) const { return maps(s.lit); }
	string show() const;
	const FlatTerm& map(uint v) const {
		auto it = sub_.find(v);
		if (sub_.find(v) != sub_.end()) {
			return it->second;
		} else {
			static FlatTerm empty; return empty;
		}
	}
	const FlatTerm& map(LightSymbol s) const {
		return map(s.lit);
	}
	void erase(uint v) { sub_.erase(v); }

	typedef std::map<uint, FlatTerm>::const_iterator const_iterator;

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
	FlatSubst complement(const set<uint>& vars) const {
		FlatSubst ret(*this);
		for (const auto& v : vars) {
			ret.sub_.erase(v);
		}
		return ret;
	}

private:
	std::map<uint, FlatTerm> sub_;
	bool ok_;
	friend void compose(FlatSubst& s1, const FlatSubst& s2, bool full);
};

FlatTerm apply(const FlatSubst& s, const FlatTerm& t);
void compose(FlatSubst& s1, const FlatSubst& s2, bool full = true);
bool composable(const FlatSubst& s1, const FlatSubst& s2);

FlatSubst convert2flatsubst(const Subst&);
Subst convert2subst(const FlatSubst&);

FlatSubst Substitution2FlatSubst(const Substitution&);
Substitution FlatSubst2Substitution(const FlatSubst&);

extern bool debug_flat_subst;
extern bool debug_flat_apply;

}}}
