#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

struct UnifStepData {
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
	const Type* least_type = nullptr;
	vector<const LightTree::Children*> children;
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
	bool track_node(const LightTree& t) {
		if (const_.is_def()) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		if (!rule) {
			rule = t.rule();
		} else if (rule !=t.rule()) {
			// In case we have a non-leaf with some rule,
			// all other leafs must be with the same rule.
			return false;
		}
		children.push_back(&t.children());
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

static UnifStepData gather_unification_data(vector<LightTree>& ex) {
	std::sort(
		ex.begin(),
		ex.end(),
		[](const LightTree& t1, const LightTree& t2) {
			return *t1.type() < *t2.type();
		}
	);
	UnifStepData ret;
	ret.least_type = ex.begin()->type();
	for (const auto& t : ex) {
		if (!(*ret.least_type <= *t.type())) {
			// There's no unification because of type constraints
			return ret;
		}
		switch (t.kind()) {
		case LightTree::VAR:
			if (!ret.track_var(t.var())) {
				return ret;
			}
			break;
		case LightTree::RULE:
			if (!ret.track_node(t)) {
				return ret;
			}
			break;
		default: assert(false && "no term in unify_both");
		}
	}
	ret.consistent = true;
	return ret;
}

LightTree do_unify(vector<LightTree> ex, Subst& sub);

LightTree unify_step(Subst& s, const vector<LightSymbol>& vars, const LightTree& term) {
	vector<LightTree> to_unify({apply(s, term)});
	for (auto v : vars) {
		if (s.maps(v)) {
			to_unify.push_back(s.sub[v]);
		}
	}
	LightTree unified = do_unify(to_unify, s);
	if (!unified.empty()) {
		for (auto v : vars) {
			if (!s.compose(Subst(v, unified))) {
				s.ok = false;
				return LightTree();
			}
		}
		return unified;
	}
	return LightTree();
}

LightTree do_unify(vector<LightTree> ex, Subst& sub) {
	if (!ex.size()) {
		return LightTree();
	} else if (ex.size() == 1) {
		return apply(sub, *ex.begin());
	}
	UnifStepData data = gather_unification_data(ex);
	if (!data.consistent) {
		return LightTree();
	}
	LightTree ret;
	if (data.rule) {
		LightTree::Children ch;
		for (uint i = 0; i < data.rule->arity(); ++ i) {
			vector<LightTree> x;
			for (const auto t : data.children) {
				LightTree* c = (*t)[i].get();
				x.push_back(*c);
			}
			LightTree c = do_unify(x, sub);
			if (!c.empty()) {
				ch.push_back(make_unique<LightTree>(c));
			} else {
				return LightTree();
			}
		}
		return unify_step(sub, data.vars, LightTree(data.rule, ch));
	} else {
		return unify_step(sub, data.vars, LightTree(data.const_.is_def() ? data.const_ : data.var));
	}
}

bool check_unification(const LightTree& term, const Subst& sub, const vector<LightTree>& ex) {
	/*if (debug_unify_subs_func) {
		cout << "--- check_unification ---" << endl;
		cout << "term : " << show(term) << endl;
		cout << "sub : " << show(sub) << endl;
	}*/
	if (!term.empty()) {
		for (auto e : ex) {
			/*if (debug_unify_subs_func) {
				cout << "expr: " << show(e) << endl;
				cout << "applied: " << show(apply(sub, e)) << endl;
			}*/

			if (apply(sub, e) != term) {
				return false;
			}
		}
	}
	return true;
}

LightTree unify(const vector<LightTree>& ex, Subst& sub) {
	LightTree ret = do_unify(ex, sub);
	if (!check_unification(ret, sub, ex)) {
		cout << "unification error: " << endl;
		for (auto pe : ex) {
			cout << "\t" << show(pe) << endl;
		}
		cout << "sub: " << endl;
		cout << show(sub) << endl;

		cout << "term: " << endl;
		cout << show(ret) << endl;
		exit(0);
	}
	return ret;
}

}}}

