#pragma once

#include "../rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

template<class Iter> RuleVar ruleVar(Iter);
template<>
inline RuleVar ruleVar<Term::ConstIterator>(Term::ConstIterator i) {
	return i->ruleVar;
};

template<class Iter>
struct UnifStepData {
	enum Kind { VAR, RULE, CONST_VAR };
	const Rule* rule = nullptr;
	vector<uint> vars;
	const Type* least_type = nullptr;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;
	vector<Kind> kinds;
	vector<Iter> iters;

	vector<Iter> subGoals() const {
		vector<Iter> ret;
		assert(kinds.size() == iters.size());
		for (uint i = 0; i < kinds.size(); ++ i) {
			if (kinds[i] == RULE) {
				ret.push_back(iters[i]);
			}
		}
		return ret;
	}

	vector<Iter> shiftGoals(const vector<Iter>& ends) const {
		vector<Iter> ret;
		assert(kinds.size() == iters.size());
		for (uint i = 0, j = 0; i < kinds.size(); ++ i) {
			if (kinds[i] == RULE) {
				ret.push_back(ends[j++]);
			} else {
				ret.push_back(iters[i]);
			}
		}
		return ret;
	}

	UnifStepData(const vector<Iter>& is) : iters(is) {
		least_type = ruleVar(*is.begin()).type();
		for (uint k = 0; k < is.size(); ++ k) {
			if (!(*least_type <= *(ruleVar(is[k]).type()))) {
				// There's no unification because of type constraints
				return;
			}
			if (ruleVar(is[k]).isVar()) {
				if (!track_var(ruleVar(is[k]).var)) {
					return;
				}
			} else {
				if (!track_node(is[k])) {
					return;
				}
			}
		}
		consistent = true;
	}

	bool track_var(LightSymbol v) {
		if (v.rep) {
			if (var.is_undef()) {
				var = v;
				kinds.push_back(VAR);
			} else {
				kinds.push_back(CONST_VAR);
			}
			// Collect replaceable variables
			vars.push_back(v.lit);
		} else {
			kinds.push_back(CONST_VAR);
			if (const_.is_undef()) {
				const_ = v;
			} else if (const_ != v) {
				// If we have any non-replaceable variables (constant), all other
				// constants must be the same variable (constant).
				return false;
			}
			if (rule) {
				// If we have any non-replaceable variables (constant),
				// complex terms are not allowed.
				return false;
			}
		}
		return true;
	}
	bool track_node(Iter i) {
		if (const_.is_def()) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		if (!rule) {
			rule = ruleVar(i).rule;
		} else if (rule != ruleVar(i).rule) {
			// In case we have a non-leaf with some rule,
			// all other leafs must be with the same rule.
			return false;
		}
		kinds.push_back(RULE);
		return true;
	}

	string show() const {
		cout << "rule: " << (rule ? Lex::toStr(rule->id()) : "NULL") << endl;
		cout << "vars: " << flush;
		for (const auto& v : vars) {
			cout << prover::show(v, true) << " " << flush;
		}
		cout << endl;
		cout << "consistent: " << (consistent ? "TRUE" : "FALSE") << endl;
		cout << "var: " << prover::show(var, true) << endl;
		cout << endl;

		string ret;
		ret += "rule: " + (rule ? Lex::toStr(rule->id()) : "NULL") + "\n";
		ret += "vars: ";
		for (const auto& v : vars) {
			ret += Lex::toStr(v) + " ";
		}
		ret += "\n";
		ret += string("consistent: ") + (consistent ? "TRUE" : "FALSE") + "\n";
		ret += string("var: ") + prover::show(var, true) + "\n";
		ret += "\n";
		return ret;
	}
};

}}}}

