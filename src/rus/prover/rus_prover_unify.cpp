#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_unify_1 = false;

struct UnifStepData {
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
	const Type* least_type = nullptr;
	vector<const LightTree::Children*> children;
	bool consistent = false;
	LightSymbol var;

	bool track_var(LightSymbol v) {
		if (var.is_undef()) {
			var = v;
		}
		if (v.rep) {
			// Collect replaceable variables
			vars.push_back(v);
		} else if  (var != v || rule) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		return true;
	}
	bool track_node(const LightTree* t) {
		if (var.is_def() && !var.rep) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		if (!rule) {
			rule = t->rule();
		} else if (rule !=t->rule()) {
			// In case we have a non-leaf with some rule,
			// all other leafs must be with the same rule.
			return false;
		}
		children.push_back(&t->children());
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

static UnifStepData gather_unification_data(vector<const LightTree*>& ex) {
	std::sort(
		ex.begin(),
		ex.end(),
		[](const LightTree* t1, const LightTree* t2) {
			return *t1->type() < *t2->type();
		}
	);
	UnifStepData ret;
	ret.least_type = (*ex.begin())->type();
	for (const auto& t : ex) {
		if (!(*ret.least_type <= *t->type())) {
			// There's no unification because of type constraints
			return ret;
		}
		switch (t->kind()) {
		case LightTree::VAR:
			if (!ret.track_var(t->var())) {
				return ret;
			}
			break;
		case LightTree::NODE:
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

uint depth_counter = 0;

LightTree unify(vector<const LightTree*> ex, Subst& sub);

LightTree gather_result(UnifStepData& data, Subst& s, LightTree ret) {
	if (debug_unify_1) {
		cout << "UNIFYING:\n" << Indent::paragraph(data.show()) << endl;
		cout << "SUB:\n";
		cout << Indent::paragraph(show(s)) << endl;
		if (++depth_counter > 8) {
			cout << "AND" << endl;
			return LightTree();
		}
	}

	vector<const LightTree*> to_unify({&ret});
	for (auto v : data.vars) {
		if (s.maps(v)) {
			to_unify.push_back(&s.sub[v]);

			if (debug_unify_1) {
				cout << "to unify: " << show(v) << " --> " << show(s.sub[v]) << endl;
			}

		}
	}

	LightTree unified = unify(to_unify, s);
	if (debug_unify /*&& to_unify.size() > 1*/) {
		/*cout << "TO UNIFY:" << endl;
		for (auto e : to_unify) {
			cout << "\t" << show(*e) << endl;
		}
		cout << endl;*/
	}
	if (!unified.empty()) {
		for (auto v : data.vars) {
			LightTree term =
				(data.least_type == v.type) ?
				unified :
				LightTree(find_super(v.type, data.least_type), new LightTree(unified));

			if (debug_unify_1) {
				cout << "going to add: " << show(v) << " --> " << show(term) << endl;
				cout << "sub:" << endl;
				cout << show(s) << endl;
			}

			if (!s.compose(Subst(v, term))) {
				if (debug_unify_1) {
					cout << "SUCC" << endl;
				}
				return LightTree();
			} else {
				if (debug_unify_1) {
					cout << "FAIL" << endl;
				}
			}
		}
		return unified;
	}
	return LightTree();
}

LightTree unify(vector<const LightTree*> ex, Subst& sub) {
	if (!ex.size()) {
		return LightTree();
	} else if (ex.size() == 1) {
		return **ex.begin();
	}
	UnifStepData data = gather_unification_data(ex);
	if (!data.consistent) {
		return LightTree();
	}
	LightTree ret;
	if (data.rule) {
		LightTree::Children ch;
		for (uint i = 0; i < data.rule->arity(); ++ i) {
			vector<const LightTree*> x;
			for (const auto t : data.children) {
				x.push_back((*t)[i].get());
			}
			LightTree c = unify(x, sub);
			if (!c.empty()) {
				ch.push_back(make_unique<LightTree>(c));
			} else {
				return LightTree();
			}
		}
		return gather_result(data, sub, LightTree(data.rule, ch));
	} else {
		return gather_result(data, sub, LightTree(data.var));
	}
}

bool check_unification(const Unified& unif, const vector<const LightTree*>& ex) {
	if (unif.sub.ok) {
		for (auto e : ex) {
			if (apply(unif.sub, *e) != unif.term) {
				return false;
			}
		}
	}
	return true;
}

bool debug_unify = true;

uint c = 0;

Unified unify(const vector<const LightTree*>& ex) {

	depth_counter = 0;

	c ++;
	if (debug_unify) {
		cout << endl << "*** UNIFYING: " << c++ << endl;
		for (auto e : ex) {
			cout << "\t" << show(*e, true) << endl;
		}
		cout << endl;
	}

	Unified ret;
	ret.term = unify(ex, ret.sub);
	ret.sub.ok = !ret.term.empty();

	if (!check_unification(ret, ex)) {
		cout << "unification error: " << c << endl;
		for (auto pe : ex) {
			cout << "\t" << show(*pe) << endl;
		}
		cout << "sub: " << endl;
		cout << show(ret.sub) << endl;

		cout << "term: " << endl;
		cout << show(ret.term) << endl;
		exit(0);
	}

	if (debug_unify) {
		cout << "*** RESULT: " << show(ret.term) << endl;
		cout << "*** SUB:" << endl;
		cout << show(ret.sub) << endl << endl;
	}

	return ret;
}

}}}

