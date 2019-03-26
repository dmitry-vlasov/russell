#include <rus_sys.hpp>
#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace {

inline void add_dep(const Tokenable* x, set<uint>& deps) {
	if (x && x->token.src()) deps.insert(x->token.src()->id());
}

template<class T>
inline void add_dep(const User<T>& x, set<uint>& deps) {
	add_dep(x.get(), deps);
}

inline void const_deps(const Const* c, set<uint>& deps) {
}

inline void symb_deps(const Symbol& symb, set<uint>& deps) {
	switch (symb.kind()) {
	case Symbol::VAR:   add_dep(symb.type(), deps); break;
	case Symbol::CONST: add_dep(symb.constant(), deps); break;
	default: break;
	}
}

void tree_deps(const Tree* tree, set<uint>& deps) {
	if (!tree) return;
	if (tree->kind() == Tree::NODE) {
		add_dep(tree->rule(), deps);
		for (const auto& ch : tree->children()) {
			tree_deps(ch, deps);
		}
	} else {
		symb_deps(*tree->var(), deps);
	}
}

inline void expr_deps(const Expr& expr, set<uint>& deps) {
	add_dep(expr.type, deps);
	tree_deps(expr.tree(), deps);
	for (const auto& s : expr.symbols) {
		symb_deps(s, deps);
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
	for (const auto& p : ass->props) {
		expr_deps(p.get()->expr, deps);
	}
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
	vars_deps(proof->allvars, deps);
	for (const auto& e : proof->elems) {
		if (Proof::kind(e) == Proof::STEP) {
			step_deps(Proof::step(e), deps);
		}
	}
}

void theory_deps(const Theory* th, set<uint>& deps) {
	for (const auto& n : th->nodes) {
		switch (Theory::kind(n)) {
		case Theory::CONST:   const_deps(Theory::const_(n), deps);      break;
		case Theory::TYPE:    type_deps(Theory::type(n), deps);         break;
		case Theory::RULE:    rule_deps(Theory::rule(n), deps);         break;
		case Theory::AXIOM:   assertion_deps(Theory::axiom(n), deps);   break;
		case Theory::DEF:     assertion_deps(Theory::def(n), deps);     break;
		case Theory::THEOREM: assertion_deps(Theory::theorem(n), deps); break;
		case Theory::PROOF:   proof_deps(Theory::proof(n), deps);       break;
		case Theory::THEORY:  theory_deps(Theory::theory(n), deps);     break;
		default : break;
		}
	}
}

bool has_contents(const Source* s) {
	for (const auto& n : s->theory.nodes) {
		auto k = Theory::kind(n);
		if (k != Theory::IMPORT && k != Theory::COMMENT) {
			return true;
		}
	}
	return false;
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
	for (auto& n : src->theory.nodes) {
		if (Theory::kind(n) == Theory::IMPORT) {
			minimize_imports(Theory::import(n)->source.get(), minimized);
		}
	}
	if (has_contents(src)) {
		set<uint> deps;
		theory_deps(&src->theory, deps);
		deps.erase(src->id());
		set<uint> min_deps = minimize_deps(src->id(), deps, minimized);
		vector<Theory::Node> new_nodes;
		for (uint inc : min_deps) {
			new_nodes.emplace_back(unique_ptr<Import>(new Import(inc)));
		}
		for (auto& n : src->theory.nodes) {
			switch (Theory::kind(n)) {
			case Theory::COMMENT: move_node<Comment>(new_nodes, n); break;
			case Theory::CONST:   move_node<Const>(new_nodes, n);   break;
			case Theory::TYPE:    move_node<Type>(new_nodes, n);    break;
			case Theory::RULE:    move_node<Rule>(new_nodes, n);    break;
			case Theory::AXIOM:   move_node<Axiom>(new_nodes, n);   break;
			case Theory::DEF:     move_node<Def>(new_nodes, n);     break;
			case Theory::THEOREM: move_node<Theorem>(new_nodes, n); break;
			case Theory::PROOF:   move_node<Proof>(new_nodes, n);   break;
			case Theory::THEORY:  move_node<Theory>(new_nodes, n);  break;
			case Theory::IMPORT:  break;
			default : assert(false && "impossible");
			}
		}
		src->theory.nodes = std::move(new_nodes);
	}
}

}

void min_imports(uint src) {
	map<uint, set<uint>> minimized;
	if (src == -1) {
		for (const auto& s : Sys::mod().math.get<Source>()) {
			minimize_imports(s.second.data, minimized);
		}
	} else {
		if (Source* s = Sys::mod().math.get<Source>().access(src)) {
			minimize_imports(s, minimized);
		}
	}
}

}}
