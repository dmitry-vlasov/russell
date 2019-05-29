#include "rus_prover_node.hpp"
#include "rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover {

//#define DEBUG_SUBST

bool Subst::operator == (const Subst& s) const {
	if (ok_ != s.ok_ || size() != s.size()) {
		return false;
	}
	for (const auto& p : sub_) {
		if (p.second.term != s.map(p.first)) {
			return false;
		}
	}
	return true;
}

bool Subst::operator != (const Subst& s) const {
	return !operator ==(s);
}

static void collect_vars(const Term& term, set<uint>& vars) {
	for (const auto& n : term.nodes) {
		if (n.ruleVar.isVar()) {
			vars.insert(n.ruleVar.var.lit);
		}
	}
}

static bool consistent(const Subst& s, uint v, const Term& t) {
	set<uint> x_vars;
	collect_vars(t, x_vars);
	if (x_vars.find(v) != x_vars.end()) {
		return false;
	}
	if (s.maps(v)) {
		return t == s.map(v);
	} else {
		for (auto x : x_vars) {
			if (s.maps(x)) {
				set<uint> y_vars;
				const Term& p = s.map(x);
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
		if (!prover::consistent(*this, p.first, p.second.term)) {
			return false;
		}
	}
	return true;
}

#ifdef DEBUG_SUBST
static void verify_chains(const Subst& s) {
	for (const auto& p : s) {
		for (auto v : p.second.vars()) {
			if (s.maps(v)) {
				throw Error("chain in composition:\n" + s.show());
			}
		}
	}
}

static void verify_composition(const Subst& comp, const Subst& s1, const Subst& s2, bool norm) {
	set<LightSymbol> vars = norm ? sets_unite<uint>(s1.dom(), s2.dom()) : s1.dom();
	for (auto v : vars) {
		LightSymbol var(v);
		Term t0(var);
		Term t1 = comp.apply(var);
		Term t2 = s2.apply(s1.apply(var));
		if (t1 != t2) {
			string msg;
			msg += "v: " + Lex::toStr(v) + "\n";
			msg += "comp(v): " + t1.show() + "\n";
			msg += "s2(s1(v)): " + t2.show() + "\n";
			throw Error("wrong composition:\n" + msg);
		}
	}
}
#endif

template<class S>
static void compose(const Subst& s1, Subst::Sub_& sub_, S s2, bool norm) {
#ifdef DEBUG_SUBST
	Subst s0(s1);
#endif
	hset<uint> vars;
	vector<uint> to_erase;
	to_erase.reserve(sub_.size());
	for (auto& p : sub_) {
		Term ex = s2.apply(p.second.term);
		if (!(ex.kind() == Term::VAR && ex.var() == p.first)) {
			p.second.term = std::move(ex);
		} else {
			to_erase.push_back(p.first);
		}
		vars.insert(p.first);
	}
	for (auto v : to_erase) {
		sub_.erase(v);
	}
	if (norm) {
		for (const auto& p : s2) {
			if (vars.find(p.first) == vars.end()) {
				sub_.emplace(p.first, p.second);
			}
		}
	}
#ifdef DEBUG_SUBST
	try {
		verify_chains(s1);
		verify_composition(s1, s0, s2, norm);
	} catch (Error& err) {
		err.msg += "s1:\n" + s0.show() + "\n";
		err.msg += "s2:\n" + s2.show() + "\n";
		err.msg += "comp:\n" + s1.show() + "\n";
		throw err;
	}
#endif
}

static Timer compose_apply_timer;

/*
static void compose(const Subst& s1, hmap<LightSymbol, Term>& sub_, Subst&& s2, bool norm) {
#ifdef DEBUG_SUBST
	Subst s0(s1);
#endif
	hset<LightSymbol, LightSymbol::Hash> vars;
	vector<LightSymbol> to_erase;
	to_erase.reserve(sub_.size());
	for (auto& p : sub_) {

		compose_apply_timer.start();
		Term ex = s2.apply(p.second);
		add_timer_stats("compose_appy", compose_apply_timer);

		if (!(ex.kind() == Term::VAR && ex.var() == p.first)) {
			p.second = std::move(ex);
		} else {
			to_erase.push_back(p.first);
		}
		vars.insert(p.first);
	}
	for (auto v : to_erase) {
		sub_.erase(v);
	}
	if (norm) {
		for (const auto& p : s2) {
			if (vars.find(p.first) == vars.end()) {
				sub_.emplace(p.first, std::move(p.second));
			}
		}
	}
#ifdef DEBUG_SUBST
	try {
		verify_chains(s1);
		verify_composition(s1, s0, s2, norm);
	} catch (Error& err) {
		err.msg += "s1:\n" + s0.show() + "\n";
		err.msg += "s2:\n" + s2.show() + "\n";
		err.msg += "comp:\n" + s1.show() + "\n";
		throw err;
	}
#endif
}*/


bool Subst::compose(const Subst& s, CompMode m, bool checked) {
#ifdef DEBUG_SUBST
	try {
#endif
	if (checked && (!ok_ || !consistent(s))) {
		ok_ = false;
	} else {
		switch (m) {
		case CompMode::SEMI: prover::compose(*this, sub_, s, false); break;
		case CompMode::NORM: prover::compose(*this, sub_, s, true);  break;
		case CompMode::DUAL: {
			Subst ss(s);
			prover::compose(ss, ss.sub_, *this, false);
			if (checked && !consistent(ss)) {
				ok_ = false;
				return false;
			}
			prover::compose(*this, sub_, ss, true);
		}
		}
	}
	return ok_;
#ifdef DEBUG_SUBST
	} catch (Error& err) {
		err.msg += "AT COMPOSITION\n";
		throw err;
	}
#endif
}

bool Subst::compose(Subst&& s, CompMode m, bool checked) {
#ifdef DEBUG_SUBST
	try {
#endif
	if (checked && (!ok_ || !consistent(s))) {
		ok_ = false;
	} else {
		switch (m) {
		case CompMode::SEMI: prover::compose(*this, sub_, std::move(s), false); break;
		case CompMode::NORM: prover::compose(*this, sub_, std::move(s), true);  break;
		case CompMode::DUAL: {
			prover::compose(s, s.sub_, *this, false);
			if (checked && !consistent(s)) {
				ok_ = false;
				return false;
			}
			prover::compose(*this, sub_, std::move(s), true);
		}
		}
	}
	return ok_;
#ifdef DEBUG_SUBST
	} catch (Error& err) {
		err.msg += "AT COMPOSITION\n";
		throw err;
	}
#endif
}

bool Subst::intersects(const Subst& sub) const {
	for (const auto& p : sub) {
		if (sub.maps(p.first)) {
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
		str += Lex::toStr(p.first) + " --> " + p.second.term.show() + "\n";
	}
	return str;
}

string Subst::showVars(const set<uint>& vars) const {
	string str;
	str += "OK = " + (ok_ ? string("TRUE") : string("FALSE")) + "\n";
	if (!sub_.size()) {
		str += "empty\n";
	}
	for (const auto& p : sub_) {
		if (vars.count(p.first)) {
			str += Lex::toStr(p.first) + " --> " + p.second.term.show() + "\n";
		}
	}
	return str;
}

Term Subst::apply(const Term& t) const {
	struct Shift {
		uint beg = -1;
		uint end = -1;
		const Term* sub = nullptr;
	};
	uint len = 0;
	Shift shifts[t.nodes.size()];
	for (uint k = 0; k < t.nodes.size(); ++ k, ++ len) {
		const auto& n = t.nodes[k];
		shifts[k].beg = len;
		if (n.ruleVar.isVar() && maps(n.ruleVar.var)) {
			const Term& term = map(n.ruleVar.var);
			len += term.nodes.size() - 1;
			shifts[k].sub = &term;
		}
		shifts[k].end = len;
	}
	Term ret(len);
	for (uint k = 0; k < t.nodes.size(); ++ k) {
		if (shifts[k].sub) {
			copySubTerm(&ret, shifts[k].beg, shifts[k].sub->nodes.begin());
		} else {
			const auto& n = t.nodes[k];
			ret.nodes[shifts[k].beg] = n;
			ret.nodes[shifts[k].end].end = ret.nodes.begin() + shifts[n.end - t.nodes.begin()].end;
		}
	}
	return ret;
}

Substitution Subst2Substitution(const Subst& s) {
	Substitution ret;
	for (const auto& p : s) {
		ret.join(p.first, p.second.type, Term2Tree(p.second.term));
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
			} else if (p.second.term != s2.map(p.first)) {
				ret += "\tvalues for '" + Lex::toStr(p.first) + "' differ:\n";
				ret += "\t\t" + p.second.term.show() + "\n";
				ret += "\t\t" + s2.map(p.first).show() + "\n";
			}
		}
		ret += "iterating s2\n";
		for (const auto& p : s2) {
			if (!s1.maps(p.first)) {
				ret += "\ts2 doesn't have " + Lex::toStr(p.first) + "\n";
			} else if (p.second.term != s1.map(p.first)) {
				ret += "\tvalues for '" + Lex::toStr(p.first) + "' differ:\n";
				ret += "\t\t" + s1.map(p.first).show() + "\n";
				ret += "\t\t" + p.second.term.show() + "\n";
			}
		}
		return ret;
	}
}

}}}
