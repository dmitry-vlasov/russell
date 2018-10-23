#pragma once

#include "rus_prover_trie_flat_term.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct FlatSubst {
	FlatSubst(bool ok = true) : ok(ok) { }
	FlatSubst(LightSymbol v, const FlatTerm& t) : ok(true) {
		if (!(t.kind() == FlatTerm::VAR && t.var() == v)) {
			sub.emplace(v, t);
		}
	}
	FlatSubst(const FlatSubst& s) : ok(s.ok) {
		operator = (s);
	}
	FlatSubst(FlatSubst&& s) : ok(s.ok) {
		operator = (std::move(s));
	}
	void operator = (const FlatSubst& s);
	void operator = (FlatSubst&& s);

	bool operator == (const FlatSubst& s) const;
	bool operator != (const FlatSubst& s) const;

	bool consistent(const FlatSubst& s) const;
	bool compose(const FlatSubst& s, bool full = true);
	bool bicompose(const FlatSubst& s);
	bool intersects(const FlatSubst& s) const;
	bool composeable(const FlatSubst& s) const;

	bool maps(LightSymbol v) const { return sub.find(v) != sub.end(); }
	string show() const;

	map<LightSymbol, FlatTerm> sub;
	bool ok;
};

FlatTerm apply(const FlatSubst& s, const FlatTerm& t);
void compose(FlatSubst& s1, const FlatSubst& s2, bool full = true);
bool composable(const FlatSubst& s1, const FlatSubst& s2);

FlatSubst convert2flatsubst(const Subst&);
Subst convert2subst(const FlatSubst&);

extern bool debug_flat_subst;

}}}}
