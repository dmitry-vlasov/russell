#include "rus_prover_trie_flat_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

void FlatSubst::operator = (const FlatSubst& s) {
	ok = s.ok;
	if (ok) for (const auto& p : s.sub) {
		sub.emplace(p.first, p.second);
	}
}

void FlatSubst::operator = (FlatSubst&& s) {
	ok = s.ok;
	sub = std::move(s.sub);
	s.ok = true;
}

bool FlatSubst::operator == (const FlatSubst& s) const {
	if (ok != s.ok) {
		return false;
	}
	for (const auto& p : sub) {
		if (!s.maps(p.first)) {
			return false;
		}
		if (p.second != s.sub.at(p.first)) {
			return false;
		}
	}
	for (const auto& p : s.sub) {
		if (!maps(p.first)) {
			return false;
		}
		if (p.second != sub.at(p.first)) {
			return false;
		}
	}
	return true;
}

bool FlatSubst::operator != (const FlatSubst& s) const {
	return !operator ==(s);
}

void collect_vars(const FlatTerm& term, set<LightSymbol>& vars) {
	for (const auto& n : term.nodes) {
		if (n.ruleVar.isVar()) {
			vars.insert(n.ruleVar.var);
		}
	}
}

bool consistent(const FlatSubst* s, LightSymbol v, const FlatTerm& t) {
	set<LightSymbol> x_vars;
	collect_vars(t, x_vars);
	if (x_vars.find(v) != x_vars.end()) {
		return false;
	}
	auto j = s->sub.find(v);
	if (j != s->sub.end()) {
		if (t != j->second) {
			return false;
		}
	}
	for (LightSymbol y : x_vars) {
		auto i = s->sub.find(y);
		if (i != s->sub.end()) {
			set<LightSymbol> y_vars;
			collect_vars(i->second, y_vars);
			if (y_vars.find(v) != y_vars.end()) {
				return false;
			}
		}
	}
	return true;
}

bool FlatSubst::consistent(const FlatSubst& s) const {
	for (const auto& p : s.sub) {
		if (!trie_index::consistent(this, p.first, p.second)) {
			return false;
		}
	}
	return true;
}

void compose(FlatSubst& s1, const FlatSubst& s2, bool full) {
	/*bool sh = s.sub.size() && sub.size();
	if (sh) {
		cout << "-------------------------------------" << endl;
		cout << "BEFORE " << (full ? "FULL" : "PART") << " COMPOSE THIS:" << endl;
		cout << Indent::paragraph(show(*this)) << endl;
		cout << "BEFORE COMPOSE S:" << endl;
		cout << Indent::paragraph(show(s)) << endl;
	}*/
	FlatSubst ret;
	set<LightSymbol> vars;
	for (const auto& p : s1.sub) {
		FlatTerm ex = apply(s2, p.second);
		if (!(ex.kind() == FlatTerm::VAR && ex.var() == p.first)) {
			s1.sub.emplace(p.first, apply(s2, p.second));
			vars.insert(p.first);
		}
	}
	if (full) {
		for (const auto& p : s2.sub) {
			if (vars.find(p.first) == vars.end()) {
				s1.sub.emplace(p.first, p.second);
			}
		}
	}
	/*if (sh) {
		cout << "AFTER COMPOSE THIS:" << endl;
		cout << Indent::paragraph(show(*this)) << endl;
		cout << "-------------------------------------" << endl;
	}*/
}

bool FlatSubst::compose(const FlatSubst& s, bool full) {
	if (!consistent(s)) {
		return false;
	}
	trie_index::compose(*this, s, full);
	return true;
}

bool FlatSubst::bicompose(const FlatSubst& s) {
	if (!s.consistent(*this)) {
		return false;
	}
	FlatSubst ss(s);
	trie_index::compose(ss, *this, false);
	if (!consistent(ss)) {
		return false;
	}
	trie_index::compose(*this, ss, true);
	return true;
}

bool FlatSubst::intersects(const FlatSubst& s) const {
	for (const auto& p : sub) {
		if (s.sub.count(p.first)) {
			return true;
		}
	}
	return false;
}

bool FlatSubst::composeable(const FlatSubst& s) const {
	set<LightSymbol> vars;
	for (const auto& p : sub) {
		collect_vars(p.second, vars);
	}
	for (const auto& p : s.sub) {
		if (vars.find(p.first) != vars.end()) {
			return true;
		}
	}
	return false;
}

uint applied_len(const FlatSubst& s, const FlatTerm& t) {
	uint len = t.len();
	for (const auto& n : t.nodes) {
		if (n.ruleVar.isVar()) {
			auto it = s.sub.find(n.ruleVar.var);
			if (it != s.sub.end()) {
				len += it->second.len() - 1;
			}
		}
	}
	return len;
}

FlatTerm apply(const FlatSubst& s, const FlatTerm& t) {
	FlatTerm ret(applied_len(s, t));
	uint i = 0;
	for (const auto& n : t.nodes) {
		if (n.ruleVar.isVar()) {
			auto it = s.sub.find(n.ruleVar.var);
			if (it != s.sub.end()) {
				for (const auto& m : it->second.nodes) {
					ret.nodes[i++] = m;
				}
			}
		} else {
			ret.nodes[i++] = n;
		}
	}
	return ret;
}

FlatSubst compose(const FlatSubst& s1, const FlatSubst& s2) {
	FlatSubst ret(s1);
	ret.compose(s2);
	return ret;
}

bool composable(const FlatSubst& s1, const FlatSubst& s2) {
	for (const auto& p : s1.sub) {
		if (s2.sub.find(p.first) != s2.sub.end()) {
			return true;
		}
	}
	return false;
}

}}}}
