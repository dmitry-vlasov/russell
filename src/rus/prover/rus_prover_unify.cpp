#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

struct UnifStepData {
	const Rule* rule = nullptr;
	vector<uint> vars;
	const Type* least_type = nullptr;
	vector<vector<Term>> children;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;

	bool track_var(LightSymbol v) {
		if (v.rep) {
			if (var.is_undef()) {
				var = v;
			}
			// Collect replaceable variables
			vars.push_back(v.lit);
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
	bool track_node(const Term& t) {
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
		children.push_back(t.children());
		return true;
	}

	string show() const {
		string ret;
		ret += "rule: " + (rule ? Lex::toStr(rule->id()) : "NULL") + "\n";
		ret += "vars: ";
		for (const auto& v : vars) {
			ret += Lex::toStr(v) + " ";
		}
		ret += "\n";
		ret += string("consistent: ") + (consistent ? "TRUE" : "FALSE") + "\n";
		ret += string("var: ") + prover::show(var, true) + "\n";
		return ret;
	}
};

static UnifStepData gather_unification_data(vector<Term>& ex) {
	std::sort(
		ex.begin(),
		ex.end(),
		[](const Term& t1, const Term& t2) {
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
		case Term::VAR:
			if (!ret.track_var(t.var())) {
				return ret;
			}
			break;
		case Term::RULE:
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

Term do_unify(vector<Term> ex, FlatSubst& sub);

Term unify_step(FlatSubst& s, const vector<uint>& vars, const Term& term) {
	vector<Term> to_unify({apply(s, term)});
	for (auto v : vars) {
		if (s.maps(v)) {
			to_unify.push_back(s.map(v));
		}
	}
	Term unified = do_unify(to_unify, s);
	if (!unified.empty()) {
		for (auto v : vars) {
			if (!s.compose(FlatSubst(v, unified))) {
				return Term();
			}
		}
		return unified;
	}
	return Term();
}

Term do_unify(vector<Term> ex, FlatSubst& sub) {
	if (!ex.size()) {
		return Term();
	} else if (ex.size() == 1) {
		return apply(sub, *ex.begin());
	}
	UnifStepData data = gather_unification_data(ex);
	if (!data.consistent) {
		return Term();
	}
	Term ret;
	if (data.rule) {
		vector<Term> ch;
		for (uint i = 0; i < data.rule->arity(); ++ i) {
			vector<Term> x;
			for (const auto& t : data.children) {
				x.push_back(t[i]);
			}
			Term c = do_unify(x, sub);
			if (!c.empty()) {
				ch.push_back(c);
			} else {
				return Term();
			}
		}
		return unify_step(sub, data.vars, Term(data.rule, ch));
	} else {
		return unify_step(sub, data.vars, Term(data.const_.is_def() ? data.const_ : data.var));
	}
}

bool check_unification(const Term& term, const FlatSubst& sub, const vector<Term>& ex) {
	if (!term.empty()) {
		for (auto e : ex) {
			if (apply(sub, e) != term) {
				return false;
			}
		}
	}
	return true;
}

Term unify(const vector<Term>& ex, FlatSubst& sub) {
	Term ret = do_unify(ex, sub);
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

}}}

