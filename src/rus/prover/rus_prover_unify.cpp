#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

bool check_unification(const Unified& unif, const vector<const LightTree*>& ex) {
	if (unif.sub.ok) {
		for (auto e : ex) {
			if (apply(unif.sub, *e) != *unif.term) {
				return false;
			}
		}
	}
	return true;
}

Unified do_unify(const vector<const LightTree*>& ex) {
	const Rule* r = nullptr;
	vector<LightSymbol> vars;
	vector<const LightTree::Children*> rules;

	enum class UnifyKind {UNDEF, VAR, CONST, RULE, DEFAULT = UNDEF};
	UnifyKind kind = UnifyKind::DEFAULT;

	for (const auto& t : ex) {
		switch (t->kind()) {
		case LightTree::VAR:
			if (t->var().rep) {
				if (kind == UnifyKind::UNDEF) {
					kind = UnifyKind::VAR;
				} else if (kind != UnifyKind::VAR) {
					return Unified();
				}
				vars.push_back(t->var());
			} else {
				if (kind == UnifyKind::UNDEF) {
					kind = UnifyKind::CONST;
				} else if (kind != UnifyKind::CONST) {
					return Unified();
				}
			}
			break;
		case LightTree::NODE:
			if (kind == UnifyKind::UNDEF) {
				kind = UnifyKind::RULE;
			} else if (kind != UnifyKind::RULE) {
				return Unified();
			}
			if (!r) {
				r = t->rule();
			} else if (r != t->rule()) {
				return Unified();
			}
			rules.push_back(&t->children());
			break;
		default: assert(false && "no term in unify_both");
		}
	}
	Unified ret(true);
	if (r) {
		LightTree::Children ch;
		for (uint i = 0; i < r->arity(); ++ i) {
			vector<const LightTree*> x;
			for (const auto t : rules) {
				x.push_back((*t)[i].get());
			}
			Unified s = do_unify(x);
			if (!ret.sub.join(s.sub)) {
				return Unified();
			}
			ch.push_back(make_unique<LightTree>(*s.term));
		}
		ret.term = new LightTree(r, ch);
		for (auto s : vars) {
			if (r->type() == s.type) {
				ret.sub.join(Subst(s.lit, *ret.term));
			} else if (Rule* sup = find_super(r->type(), s.type)) {
				ret.sub.join(Subst(s.lit, LightTree(sup, new LightTree(*ret.term))));
			} else {
				return Unified();
			}
		}
	} else {
		std::sort(
			vars.begin(),
			vars.end(),
			[](const LightSymbol& v1, const LightSymbol& v2) {
				return *v1.type < *v2.type;
			}
		);
		LightSymbol lv;
		if (!vars.size()) {
			for (const auto& t : ex) {
				if (t->kind() == LightTree::VAR) {
					if (lv.lit == -1) {
						lv = t->var();
					} else if (t->var() != lv) {
						return Unified();
					}
				} else {
					return Unified();
				}
			}
		} else {
			for (auto s : vars) {
				if (lv.lit == -1) {
					lv = s;
				}
				if (lv.type == s.type) {
					ret.sub.join(Subst(s.lit, lv));
				} else if (Rule* sup = find_super(lv.type, s.type)) {
					ret.sub.join(Subst(s.lit, LightTree(sup, new LightTree(lv))));
				} else {
					return Unified();
				}
			}
		}
		ret.term = new LightTree(lv);
	}
	return ret;
}

struct UnifStepData {
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
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
	const Type* least_type = (*ex.begin())->type();
	for (const auto& t : ex) {
		if (!(t->type() == least_type || find_super(t->type(), least_type))) {
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


unique_ptr<LightTree> do_unify_1(vector<const LightTree*> ex, Subst& sub);

unique_ptr<LightTree> gather_result(UnifStepData& data, Subst& s, LightTree* ret) {
	vector<const LightTree*> to_unify({ret});
	for (auto v : data.vars) {
		if (s.mapsVar(v.lit)) {
			to_unify.push_back(&s.sub[v.lit]);
		}
	}
	if (auto unified = do_unify_1(to_unify, s)) {
		for (auto v : data.vars) {
			if (data.rule->type() == v.type) {
				s.compose(Subst(v.lit, *unified));
			} else {
				s.compose(Subst(v.lit, LightTree(find_super(data.rule->type(), v.type), new LightTree(*unified))));
			}
		}
		return unified;
	} else {
		return nullptr;
	}
}

unique_ptr<LightTree> do_unify_1(vector<const LightTree*> ex, Subst& sub) {
	if (!ex.size()) {
		return nullptr;
	} else if (ex.size() == 1) {
		return make_unique<LightTree>(**ex.begin());
	}
	UnifStepData data = gather_unification_data(ex);
	if (!data.consistent) {
		return nullptr;
	}
	LightTree* ret;
	if (data.rule) {
		LightTree::Children ch;
		for (uint i = 0; i < data.rule->arity(); ++ i) {
			vector<const LightTree*> x;
			for (const auto t : data.children) {
				x.push_back((*t)[i].get());
			}
			if (unique_ptr<LightTree> c = do_unify_1(x, sub)) {
				ch.push_back(std::move(c));
			} else {
				return nullptr;
			}
		}
		ret = new LightTree(data.rule, ch);
	} else {
		ret = new LightTree(data.var);
	}
	return gather_result(data, sub, ret);
}


Unified unify(const vector<const LightTree*>& ex) {

	cout << endl << "UNIFYING: " << endl;
	for (auto e : ex) {
		cout << "\t" << show(*e, true) << endl;
	}
	cout << endl;

	//Unified ret = do_unify(ex);
	Unified ret;
	ret.term = do_unify_1(ex, ret.sub).release();
	assert(check_unification(ret, ex) && "unification error");

	cout << "RESULT: " << (ret.term ? show(*ret.term) : "NULL") << endl;
	cout << "SUB:" << endl;
	cout << show(ret.sub) << endl << endl;

	return ret;
}

}}}

