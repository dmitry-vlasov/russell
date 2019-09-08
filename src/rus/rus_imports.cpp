#include <rus_sys.hpp>
#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace {

inline void add_dep(const WithToken* x, set<uint>& deps) {
	if (x && x->token.src()) deps.insert(x->token.src()->id());
}

template<class T>
inline void add_dep(const User<T>& x, set<uint>& deps) {
	add_dep(x.get(), deps);
}

inline void symb_deps(const Symbol& symb, set<uint>& deps) {
	if (const Var* var = dynamic_cast<const Var*>(&symb)) {
		add_dep(var, deps);
	} else if (const Const* c = dynamic_cast<const Const*>(&symb)) {
		add_dep(c, deps);
	}
}

void tree_deps(const Tree* tree, set<uint>& deps) {
	if (!tree) return;
	if (const RuleTree* rule_tree = dynamic_cast<const RuleTree*>(tree)) {
		add_dep(rule_tree->rule.get(), deps);
		for (const auto& ch : rule_tree->children) {
			tree_deps(ch.get(), deps);
		}
	} else if (const VarTree* var_tree = dynamic_cast<const VarTree*>(tree)) {
		add_dep(var_tree->type(), deps);
	} else {
		throw Error("impossible");
	}
}

inline void expr_deps(const Expr& expr, set<uint>& deps) {
	add_dep(expr.type, deps);
	tree_deps(expr.tree(), deps);
	for (const auto& s : expr.symbols) {
		symb_deps(*s, deps);
	}
}

inline void vars_deps(const Vars& vars, set<uint>& deps) {
	for (const auto& v : vars.v) {
		symb_deps(v, deps);
	}
}

inline void type_deps(const Type* type, set<uint>& deps) {
	for (const auto& sup : type->sup) {
		add_dep(sup, deps);
	}
}

inline void rule_deps(const Rule* rule, set<uint>& deps) {
	vars_deps(rule->vars, deps);
	expr_deps(rule->term, deps);
}

inline void assertion_deps(const Assertion* ass, set<uint>& deps) {
	vars_deps(ass->vars, deps);
	for (const auto& h : ass->hyps) {
		expr_deps(h.get()->expr, deps);
	}
	expr_deps(ass->prop->expr, deps);
}

void proof_deps(const Proof* proof, set<uint>& deps);

void step_deps(const Step* step, set<uint>& deps) {
	expr_deps(step->expr, deps);
	switch (step->kind()) {
	case Step::ASS:  add_dep(step->ass(), deps);       break;
	case Step::CLAIM: proof_deps(step->claim(), deps); break;
	}
}

void proof_deps(const Proof* proof, set<uint>& deps) {
	vars_deps(proof->vars, deps);
	for (const auto& step : proof->steps) {
		step_deps(step.get(), deps);
	}
}

inline void theorem_deps(const Theorem* th, set<uint>& deps) {
	assertion_deps(th, deps);
	if (th->proof) {
		proof_deps(th->proof.get(), deps);
	}
}

void theory_deps(const Theory* th, set<uint>& deps) {
	for (const auto& n : th->nodes) {
		switch (Theory::kind(n)) {
		case Theory::CONSTANT: break;
		case Theory::TYPE:     type_deps(Theory::type(n), deps);         break;
		case Theory::RULE:     rule_deps(Theory::rule(n), deps);         break;
		case Theory::AXIOM:    assertion_deps(Theory::axiom(n), deps);   break;
		case Theory::DEF:      assertion_deps(Theory::def(n), deps);     break;
		case Theory::THEOREM:  theorem_deps(Theory::theorem(n), deps); break;
		case Theory::THEORY:   theory_deps(Theory::theory(n), deps);     break;
		default : break;
		}
	}
}

set<uint> minimize_deps(uint label, const set<uint>& deps, map<uint, set<uint>>& resolved) {
	set<uint> minimized;
	set<uint> cumulative;
	for (uint dep : deps) {
		if (!cumulative.count(dep)) {
			minimized.insert(dep);
		}
		cumulative.insert(dep);
		for (uint d : resolved[dep]) {
			cumulative.insert(d);
		}
	}
	resolved[label] = cumulative;
	while (true) {
		uint redundant = -1;
		for (uint dep_1 : minimized) {
			for (uint dep_2 : minimized) {
				if (dep_1 != dep_2) {
					if (resolved[dep_2].count(dep_1)) {
						redundant = dep_1;
						break;
					} else if (resolved[dep_1].count(dep_2)) {
						redundant = dep_2;
						break;
					}
				}
			}
			if (redundant != -1) {
				minimized.erase(redundant);
				break;
			}
		}
		if (redundant == -1) {
			break;
		}
	}
	return minimized;
}


template<class T>
void move_node(vector<Theory::Node>& nodes, Theory::Node& n) {
	nodes.emplace_back(
		unique_ptr<T>(
			std::get<unique_ptr<T>>(n).release()
		)
	);
}

void minimize_imports(Source* src, map<uint, set<uint>>& minimized) {
	if (minimized.count(src->id())) return;
	minimized[src->id()];
	for (auto& imp : src->imports) {
		minimize_imports(imp->source.get(), minimized);
	}
}

}

void min_imports(uint src) {
	map<uint, set<uint>> minimized;
	if (src == -1) {
		for (Source& s : Sys::mod().math.get<Source>()) {
			minimize_imports(&s, minimized);
		}
	} else {
		if (Source* s = Sys::mod().math.get<Source>().access(src)) {
			minimize_imports(s, minimized);
		}
	}
}

}}
