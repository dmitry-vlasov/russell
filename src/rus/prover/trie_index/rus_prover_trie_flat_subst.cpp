#include "rus_prover_trie_flat_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_flat_subst = false;
bool debug_flat_apply = false;

void FlatSubst::operator = (const FlatSubst& s) {
	ok_ = s.ok_;
	if (ok_) {
		for (const auto& p : s.sub_) {
			sub_.emplace(p.first, p.second);
		}
	}
}

void FlatSubst::operator = (FlatSubst&& s) {
	ok_ = s.ok_;
	sub_ = std::move(s.sub_);
	s.ok_ = true;
}

bool FlatSubst::operator == (const FlatSubst& s) const {
	if (ok_ != s.ok_ || size() != s.size()) {
		return false;
	}
	for (const auto& p : sub_) {
		if (p.second != s.maps(p.first)) {
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
	if (s->maps(v)) {
		return s->map(v) == t;
	} else {
		for (LightSymbol y : x_vars) {
			if (s->maps(y)) {
				set<LightSymbol> y_vars;
				collect_vars(s->map(y), y_vars);
				if (y_vars.find(v) != y_vars.end()) {
					return false;
				}
			}
		}
		return true;
	}
}

bool FlatSubst::consistent(const FlatSubst& sub) const {
	for (const auto& p : sub) {
		if (!trie_index::consistent(this, p.first, p.second)) {
			return false;
		}
	}
	return true;
}

void compose(FlatSubst& s1, const FlatSubst& s2, bool full) {
	FlatSubst ret;
	set<LightSymbol> vars;
	for (const auto& p : s1) {
		FlatTerm ex = apply(s2, p.second);
		if (!(ex.kind() == FlatTerm::VAR && ex.var() == p.first)) {
			s1.sub_[p.first] = std::move(ex);
			vars.insert(p.first);
		} else {
			s1.sub_.erase(p.first);
		}
	}
	if (full) {
		for (const auto& p : s2) {
			if (vars.find(p.first) == vars.end()) {
				s1.sub_.emplace(p.first, p.second);
			}
		}
	}
}

bool FlatSubst::compose(const FlatSubst& s, bool full) {
	if (!ok_ || !consistent(s)) {
		ok_ = false;
	} else {
		trie_index::compose(*this, s, full);
	}
	return ok_;
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

bool FlatSubst::intersects(const FlatSubst& sub) const {
	for (const auto& p : sub) {
		if (sub.maps(p.first)) {
			return true;
		}
	}
	return false;
}

bool FlatSubst::composeable(const FlatSubst& s) const {
	set<LightSymbol> vars;
	for (const auto& p : sub_) {
		collect_vars(p.second, vars);
	}
	for (const auto& p : s) {
		if (vars.find(p.first) != vars.end()) {
			return true;
		}
	}
	return false;
}

string FlatSubst::show() const {
	string str;
	str += "OK = " + (ok_ ? string("TRUE") : string("FALSE")) + "\n";
	if (!sub_.size()) {
		str += "empty\n";
	}
	for (const auto& p : sub_) {
		str += prover::show(p.first) + " --> " + p.second.show() + "\n";
	}
	return str;
}

uint applied_len(const FlatSubst& s, const FlatTerm& t) {
	uint len = t.len();
	for (const auto& n : t.nodes) {
		if (n.ruleVar.isVar()) {
			const FlatTerm& term = s.map(n.ruleVar.var);
			if (!term.empty()) {
				len += term.len() - 1;
			}
		}
	}
	return len;
}

FlatTerm apply(const FlatSubst& s, const FlatTerm& t) {
	uint len = 0;
	vector<uint> beg_shifts;
	vector<uint> end_shifts;
	vector<const FlatTerm*> subs;
	for (uint k = 0; k < t.len(); ++ k, ++ len) {
		const auto& n = t.nodes[k];
		beg_shifts.push_back(len);
		if (n.ruleVar.isVar()) {
			const FlatTerm& term = s.map(n.ruleVar.var);
			if (!term.empty()) {
				len += term.len() - 1;
				subs.push_back(&term);
			} else {
				subs.push_back(nullptr);
			}
		} else {
			subs.push_back(nullptr);
		}
		end_shifts.push_back(len);
	}
	FlatTerm ret(len);
	for (uint k = 0; k < t.len(); ++ k) {
		if (subs[k]) {
			copyFlatSubTerm(&ret, beg_shifts[k], subs[k]->nodes.begin());
		} else {
			const auto& n = t.nodes[k];
			ret.nodes[beg_shifts[k]] = n;
			ret.nodes[beg_shifts[k]].end = ret.nodes.begin() + end_shifts[n.end - t.nodes.begin()];
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
	for (const auto& p : s1) {
		if (s2.maps(p.first)) {
			return true;
		}
	}
	return false;
}

FlatSubst convert2flatsubst(const Subst& sub) {
	FlatSubst ret;
	for (const auto& p : sub) {
		ret.compose(p.first, std::move(convert2flatterm(p.second)));
	}
	return ret;
}

Subst convert2subst(const FlatSubst& s) {
	Subst ret;
	for (const auto& p : s) {
		ret.compose(p.first, std::move(convert2lighttree(p.second)));
	}
	return ret;
}

}}}}
