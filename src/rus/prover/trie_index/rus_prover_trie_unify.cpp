#include "rus_prover_trie_unify.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct FlatUnifStepData {
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
	const Type* least_type = nullptr;
	vector<vector<FlatTerm::ConstIterator>> children;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;

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
	bool track_node(const FlatTerm& t, FlatTerm::ConstIterator i) {
		if (const_.is_def()) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		if (!rule) {
			rule = i->ruleVar.rule;
		} else if (rule != i->ruleVar.rule) {
			// In case we have a non-leaf with some rule,
			// all other leafs must be with the same rule.
			return false;
		}
		children.push_back(t.childrenIters());
		return true;
	}

	string show() const {
		string ret;
		ret += "rule: " + (rule ? Lex::toStr(rule->id()) : "NULL") + "\n";
		ret += "vars: ";
		for (const auto& v : vars) {
			ret += prover::show(v, true) + " ";
		}
		ret += "\n";
		ret += string("consistent: ") + (consistent ? "TRUE" : "FALSE") + "\n";
		ret += string("var: ") + prover::show(var, true) + "\n";
		return ret;
	}
};

static FlatUnifStepData gather_unification_data(const vector<FlatTerm>& es, const vector<FlatTerm::ConstIterator>& is) {
	/*std::sort(
		es.begin(),
		es.end(),
		[](const FlatTerm& t1, const FlatTerm& t2) {
			return *t1.type() < *t2.type();
		}
	);*/
	FlatUnifStepData ret;
	ret.least_type = (*is.begin())->ruleVar.type();
	for (uint k = 0; k < es.size(); ++ k) {
		if (!(*ret.least_type <= *is[k]->ruleVar.type())) {
			// There's no unification because of type constraints
			return ret;
		}
		if (is[k]->ruleVar.isVar()) {
			if (!ret.track_var(is[k]->ruleVar.var)) {
				return ret;
			}
		} else {
			if (!ret.track_node(es[k], is[k])) {
				return ret;
			}
		}
	}
	ret.consistent = true;
	return ret;
}

FlatTerm unify(const vector<FlatTerm>& ex, FlatSubst& sub);

FlatTerm do_unify(const vector<FlatTerm>& ex, const vector<FlatTerm::ConstIterator>& is, FlatSubst& sub);

FlatTerm unify_step(FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term) {
	vector<FlatTerm> to_unify({apply(s, term)});
	for (auto v : vars) {
		if (s.maps(v)) {
			to_unify.push_back(s.sub.at(v));
		}
	}
	FlatTerm unified = unify(to_unify, s);
	if (!unified.empty()) {
		for (auto v : vars) {
			if (!s.compose(FlatSubst(v, unified))) {
				s.ok = false;
				return FlatTerm(0);
			}
		}
		return unified;
	}
	return FlatTerm(0);
}

FlatTerm do_unify(const vector<FlatTerm>& ex, const vector<FlatTerm::ConstIterator>& is, FlatSubst& sub) {
	if (!ex.size()) {
		return FlatTerm(0);
	} else if (ex.size() == 1) {
		return apply(sub, *ex.begin());
	}
	FlatUnifStepData data = gather_unification_data(ex, is);
	if (!data.consistent) {
		return FlatTerm(0);
	}
	if (data.rule) {
		vector<FlatTerm> ch;
		for (uint i = 0; i < data.rule->arity(); ++ i) {
			vector<FlatTerm::ConstIterator> x;
			for (const auto& t : data.children) {
				x.push_back(t[i]);
			}
			FlatTerm c = do_unify(ex, x, sub);
			if (!c.empty()) {
				ch.emplace_back(c);
			} else {
				return FlatTerm(0);
			}
		}
		return unify_step(sub, data.vars, FlatTerm(data.rule, ch));
	} else {
		return unify_step(sub, data.vars, FlatTerm(data.const_.is_def() ? data.const_ : data.var));
	}
}

bool check_unification(const FlatTerm& term, const FlatSubst& sub, const vector<FlatTerm>& ex) {
	if (!term.empty()) {
		for (auto e : ex) {
			if (apply(sub, e) != term) {
				return false;
			}
		}
	}
	return true;
}

FlatTerm unify(const vector<FlatTerm>& ex, FlatSubst& sub) {
	vector<FlatTerm::ConstIterator> is;
	for (const auto& e : ex) {
		is.push_back(e.nodes.begin());
	}
	FlatTerm ret = do_unify(ex, is, sub);
	if (!check_unification(ret, sub, ex)) {
		cout << "unification error: " << endl;
		for (auto pe : ex) {
			cout << "\t" << pe.show() << endl;
		}
		cout << "sub: " << endl;
		cout << sub.show() << endl;

		cout << "term: " << endl;
		cout << ret.show() << endl;
		exit(0);
	}
	return ret;
}

}}}}
