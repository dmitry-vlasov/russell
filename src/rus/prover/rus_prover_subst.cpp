#include "rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover {

void Subst::operator = (const Subst& s) {
	ok_ = s.ok_;
	if (ok_) {
		for (const auto& p : s.sub_) {
			sub_.emplace(p.first, p.second);
		}
	}
}

void Subst::operator = (Subst&& s) {
	ok_ = s.ok_;
	sub_ = std::move(s.sub_);
	s.ok_ = true;
}

bool Subst::operator == (const Subst& s) const {
	if (ok_ != s.ok_ || size() != s.size()) {
		return false;
	}
	for (const auto& p : sub_) {
		if (p.second != s.map(p.first)) {
			return false;
		}
	}
	return true;
}

bool Subst::operator != (const Subst& s) const {
	return !operator ==(s);
}

void collect_vars(const Term& term, set<uint>& vars) {
	for (const auto& n : term.nodes) {
		if (n.ruleVar.isVar()) {
			vars.insert(n.ruleVar.var.lit);
		}
	}
}

bool consistent(const Subst* s, uint v, const Term& t) {
	set<uint> x_vars;
	collect_vars(t, x_vars);
	if (x_vars.find(v) != x_vars.end()) {
		return false;
	}
	if (s->maps(v)) {
		return t == s->map(v);
	} else {
		for (uint x : x_vars) {
			if (s->maps(x)) {
				set<uint> y_vars;
				const Term& p = s->map(x);
				collect_vars(p, y_vars);
				if (y_vars.find(v) != y_vars.end()) {
					if (p.kind() == Term::VAR && p.var() == v &&
						t.kind() == Term::VAR && t.var() == x) {
						return true;
					} else {
						return false;
					}
				}
			}
		}
		return true;
	}
}

bool Subst::consistent(const Subst& sub) const {
	for (const auto& p : sub) {
		if (!prover::consistent(this, p.first, p.second)) {
			return false;
		}
	}
	return true;
}

void compose(Subst& s1, const Subst& s2, bool full) {
	Subst ret;
	hset<uint> vars;
	vector<uint> to_erase;
	for (const auto& p : s1) {
		Term ex = apply(s2, p.second);
		if (!(ex.kind() == Term::VAR && ex.var() == p.first)) {
			s1.sub_[p.first] = std::move(ex);
			vars.insert(p.first);
		} else {
			if (full) {
				to_erase.push_back(p.first);
			} else {
				vars.insert(ex.var().lit);
			}
		}
	}
	for (uint v : to_erase) {
		s1.sub_.erase(v);
	}
	if (full) {
		for (const auto& p : s2) {
			if (vars.find(p.first) == vars.end()) {
				s1.sub_[p.first] = p.second;
			}
		}
	}
}

bool Subst::compose(const Subst& s, bool full) {
	if (!ok_ || !consistent(s)) {
		ok_ = false;
	} else {
		prover::compose(*this, s, full);
	}
	return ok_;
}

bool Subst::bicompose(const Subst& s) {
	if (!s.consistent(*this)) {
		return false;
	}
	Subst ss(s);
	prover::compose(ss, *this, false);
	if (!consistent(ss)) {
		return false;
	}
	prover::compose(*this, ss, true);
	return true;
}

bool Subst::intersects(const Subst& sub) const {
	for (const auto& p : sub) {
		if (sub.maps(p.first)) {
			return true;
		}
	}
	return false;
}

bool Subst::composeable(const Subst& s) const {
	set<uint> vars;
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

string Subst::show() const {
	string str;
	str += "OK = " + (ok_ ? string("TRUE") : string("FALSE")) + "\n";
	if (!sub_.size()) {
		str += "empty\n";
	}
	for (const auto& p : sub_) {
		str += Lex::toStr(p.first) + " --> " + p.second.show() + "\n";
	}
	return str;
}

uint applied_len(const Subst& s, const Term& t) {
	uint len = t.nodes.size();
	for (const auto& n : t.nodes) {
		if (n.ruleVar.isVar() && s.maps(n.ruleVar.var)) {
			const Term& term = s.map(n.ruleVar.var);
			if (!term.empty()) {
				len += term.nodes.size() - 1;
			}
		}
	}
	return len;
}

Term apply(const Subst& s, const Term& t) {
	uint len = 0;
	vector<uint> beg_shifts;
	vector<uint> end_shifts;
	vector<const Term*> subs;
	for (uint k = 0; k < t.nodes.size(); ++ k, ++ len) {
		const auto& n = t.nodes[k];
		beg_shifts.push_back(len);
		if (n.ruleVar.isVar()) {
			const Term& term = s.map(n.ruleVar.var);
			if (!term.empty()) {
				len += term.nodes.size() - 1;
				subs.push_back(&term);
			} else {
				subs.push_back(nullptr);
			}
		} else {
			subs.push_back(nullptr);
		}
		end_shifts.push_back(len);
	}
	Term ret(len);
	for (uint k = 0; k < t.nodes.size(); ++ k) {
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

Subst compose(const Subst& s1, const Subst& s2) {
	Subst ret(s1);
	ret.compose(s2);
	return ret;
}

bool composable(const Subst& s1, const Subst& s2) {
	for (const auto& p : s1) {
		if (s2.maps(p.first)) {
			return true;
		}
	}
	return false;
}


Subst Substitution2FlatSubst(const Substitution& sub) {
	Subst ret;
	for (const auto& p : sub) {
		ret.compose(p.first, std::move(Tree2FlatTerm(*p.second)));
	}
	return ret;
}

Substitution FlatSubst2Substitution(const Subst& s) {
	Substitution ret;
	for (const auto& p : s) {
		ret.join(p.first, std::move(FlatTerm2Tree(p.second)));
	}
	return ret;
}

string show_diff(const Subst& s1, const Subst& s2) {
	if (s1 == s2) return "<no diff>"; else {
		string ret;
		ret += "iterating s1\n";
		for (const auto& p : s1) {
			if (!s2.maps(p.first)) {
				ret += "\ts2 doesn't have " + Lex::toStr(p.first) + "\n";
			} else if (p.second != s2.map(p.first)) {
				ret += "\tvalues for '" + Lex::toStr(p.first) + "' differ:\n";
				ret += "\t\t" + p.second.show() + "\n";
				ret += "\t\t" + s2.map(p.first).show() + "\n";
			}
		}
		ret += "iterating s2\n";
		for (const auto& p : s2) {
			if (!s1.maps(p.first)) {
				ret += "\ts2 doesn't have " + Lex::toStr(p.first) + "\n";
			} else if (p.second != s1.map(p.first)) {
				ret += "\tvalues for '" + Lex::toStr(p.first) + "' differ:\n";
				ret += "\t\t" + s1.map(p.first).show() + "\n";
				ret += "\t\t" + p.second.show() + "\n";
			}
		}
		return ret;
	}
}

}}}
