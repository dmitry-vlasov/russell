#pragma once

#include "rus_prover_trie_flat_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

FlatTerm unify(const vector<FlatTerm>& ex, FlatSubst& sub);
FlatTerm unify_step(FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term);
FlatSubst unify_step(const FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term);

template<class Iter> RuleVar ruleVar(Iter);
template<class Iter> vector<Iter> childrenIters(Iter);

template<>
inline RuleVar ruleVar<FlatTerm::ConstIterator>(FlatTerm::ConstIterator i) {
	return i->ruleVar;
};

template<>
inline vector<FlatTerm::ConstIterator> childrenIters<FlatTerm::ConstIterator>(FlatTerm::ConstIterator it) {
	vector<FlatTerm::ConstIterator> ret;
	//cout << "childrenIters -- CHILDREN OF: " << term(it).show() << endl;
	if (it->ruleVar.isRule()) {
		FlatTerm::ConstIterator x = it + 1;
		for (uint i = 0; i < it->ruleVar.rule->arity(); ++i) {
			ret.push_back(x);
			/*cout << "\tCHILD: '";
			auto j = x;
			while (true) {
				cout << j->ruleVar.show() << " ";
				if (j == x->end) {
					break;
				}
				++j;
			}
			cout << "'" << endl;*/
			x = x->end + 1;
		}
	} else {
		throw Error("node has no children");
	}
	//cout << "childrenIters -- END CHILDREN" << endl;
	return ret;
}

template<class Iter>
struct UnifStepData {
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
	const Type* least_type = nullptr;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;

	vector<Iter> ruleIters;

	UnifStepData(const vector<Iter>& is) {
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
			}
			// Collect replaceable variables
			vars.push_back(v);
		} else {
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
			ret += prover::show(v, true) + " ";
		}
		ret += "\n";
		ret += string("consistent: ") + (consistent ? "TRUE" : "FALSE") + "\n";
		ret += string("var: ") + prover::show(var, true) + "\n";
		ret += "\n";
		return ret;
	}
};


template<class Iter>
struct FlatUnifStepData {
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
	const Type* least_type = nullptr;
	vector<vector<Iter>> children;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;

	FlatUnifStepData(const vector<Iter>& is) {
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
			}
			// Collect replaceable variables
			vars.push_back(v);
		} else {
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
		vector<Iter> ch = trie_index::childrenIters(i);
		children.push_back(trie_index::childrenIters(i));
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
		cout << "children size: " << children.size() << endl;
		int cc = 0;
		for (const auto& ch : children) {
			cout << "\tchildern of " << (cc++) << endl;
			for (auto i : ch) {
				cout << "\t\t'";
				auto j = i;
				while (true) {
					cout << j->ruleVar.show() << " " << flush;
					if (j == i->end) {
						break;
					}
					++j;
				}
				cout << "'" << endl;
			}
			cout << "end of children" << endl << endl;
		}
		cout << endl;

		string ret;
		ret += "rule: " + (rule ? Lex::toStr(rule->id()) : "NULL") + "\n";
		ret += "vars: ";
		for (const auto& v : vars) {
			ret += prover::show(v, true) + " ";
		}
		ret += "\n";
		ret += string("consistent: ") + (consistent ? "TRUE" : "FALSE") + "\n";
		ret += string("var: ") + prover::show(var, true) + "\n";
		ret += "children size: " + to_string(children.size()) + "\n";
		int c = 0;
		for (const auto& ch : children) {
			ret += "\tchildern of " + to_string(c++) + "\n";
			for (auto i : ch) {
				ret += "\t\t'";
				auto j = i;
				while (true) {
					ret += j->ruleVar.show() + " ";
					if (j == i->end) {
						break;
					}
					++j;
				}
				ret += "'\n";
			}
			ret += "end of children\n\n";
		}
		ret += "\n";
		return ret;
	}
};


extern bool debug_flat_unify;

}}}}

