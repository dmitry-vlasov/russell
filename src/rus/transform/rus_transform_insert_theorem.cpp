#include <rus_ast.hpp>

namespace mdl { namespace rus {

bool debug_insert_theorem = false;

vector<Token> leave_minimal(const set<Token>& src_points_set) {
	vector<Token> src_points;
	for (const Token& sp : src_points_set) {
		src_points.push_back(sp);
	}
	vector<Token> ret;
	for (uint i = 0; i < src_points.size(); ++i) {
		const Token& sp1 = src_points.at(i);
		bool is_min = true;
		for (uint j = 0; j < src_points.size(); ++j) {
			const Token& sp2 = src_points.at(j);
			if (sp1.preceeds(sp2)) {
				is_min = false;
				break;
			}
		}
		if (is_min) {
			ret.push_back(sp1);
		}
	}
	return ret;
}

vector<Source*> leave_maximal(const vector<Source*>& srcs) {
	vector<Source*> ret;
	for (Source* sp1 : srcs) {
		bool is_max = true;
		for (Source* sp2 : srcs) {
			if (sp1 != sp2 && sp1->includes(sp2)) {
				is_max = false;
				break;
			}
		}
		if (is_max) {
			ret.push_back(sp1);
		}
	}
	return ret;
}

SrcPos find_infimum(const set<Token>& src_points) {

	if (debug_insert_theorem) {
		cout << "src_points:" << endl;
		for (auto& t : src_points) {
			cout << "\t" << t.show() << endl;
		}
		cout << endl;
	}

	vector<Token> min_src_points = leave_minimal(src_points);

	if (debug_insert_theorem) {
		cout << "min_src_points:" << endl;
		for (auto& t : min_src_points) {
			cout << "\t" << t.show() << endl;
		}
		cout << endl;
	}

	set<const Source*> upper_bounds;
	for (auto& t : min_src_points) {
		upper_bounds.insert(t.src());
	}
	if (debug_insert_theorem) {
		cout << "upper_bounds:" << endl;
		for (auto& s : upper_bounds) {
			cout << "\t" << Lex::toStr(s->id()) << endl;
		}
		cout << endl;
	}
	vector<Source*> lower_bounds;
	for (Source& s : Sys::mod().math.get<Source>()) {
		bool is_lower_bound = true;
		for (Token& t : min_src_points) {
			if (!(s.includes(t.src()) || &s == t.src())) {
				is_lower_bound = false;
				break;
			}
		}
		if (is_lower_bound) {
			lower_bounds.push_back(&s);
		}
	}
	if (debug_insert_theorem) {
		cout << "lower_bounds:" << endl;
		for (auto& s : lower_bounds) {
			cout << "\t" << Lex::toStr(s->id()) << endl;
		}
		cout << endl;
	}

	SrcPos ret;
	if (lower_bounds.size()) {
		vector<Source*> max_lower_bounds = leave_maximal(lower_bounds);

		if (debug_insert_theorem) {
			cout << "max_lower_bounds:" << endl;
			for (auto& s : max_lower_bounds) {
				cout << "\t" << Lex::toStr(s->id()) << endl;
			}
			cout << endl;
		}

		vector<Source*> upper_lower;
		for (Source* s : lower_bounds) {
			if (upper_bounds.count(s)) {
				upper_lower.push_back(s);
			}
		}

		if (debug_insert_theorem) {
			cout << "upper_lower:" << endl;
			for (auto& s : upper_lower) {
				cout << "\t" << Lex::toStr(s->id()) << endl;
			}
			cout << endl;
		}

		if (upper_lower.size()) {
			ret.src = upper_lower.front();
			if (min_src_points.size() != 1) {
				string err = "min_src_points.size() != 1\n";
				for (auto& t : min_src_points) {
					err += "\t" + t.show() + "\n";
				}
				err += "\n";
				throw Error(err);
			}
			const Token& min_src_token = min_src_points.front();
			for (auto& n : ret.src->theory.nodes) {
				WithToken* with_token = Theory::getWithToken(n);
				if (min_src_token.preceeds(with_token->token)) {
					break;
				}
				ret.pos += 1;
			}
		} else {
			ret.src = max_lower_bounds.front();
			for (auto& n : ret.src->theory.nodes) {
				if (!Theory::comment(n) && !Theory::import(n)) {
					break;
				}
				ret.pos += 1;
			}
		}
	} else {
		string src_name;
		for (auto& t : min_src_points) {
			if (src_name.size()) {
				src_name += "_";
			}
			src_name += Lex::toStr(t.src()->id());
		}
		src_name = "common_for_" + src_name;
		uint src_id = Lex::toInt(src_name);
		ret.src = new Source(src_id);
		vector<Import*> imports;
		for (auto& t : min_src_points) {
			imports.push_back(new Import(t.src()->id()));
			ret.pos += 1;
		}
	}
	return ret;
}

inline void insert_dep(set<Token>& deps, const Token& token) {
	if (token.is_defined()) {
		deps.insert(token);
	}
}

void find_dependencies(const Rule& rule, set<Token>& deps) {
	insert_dep(deps, rule.token);
	for (auto& s : rule.term.symbols) {
		if (const Const* c = dynamic_cast<const Const*>(s.get())) {
			insert_dep(deps, c->constant()->token);
		} else if (const Var* v = dynamic_cast<const Var*>(s.get())) {
			insert_dep(deps, v->type()->token);
		} else {
			throw Error("must be Const or Var");
		}
	}
}

void find_dependencies(const Expr& expr, set<Token>& deps) {
	expr.tree()->traverse([&deps](const Tree& n) {
		if (const RuleTree* r = dynamic_cast<const RuleTree*>(&n)) {
			find_dependencies(*r->rule, deps);
		} else if (const VarTree* v = dynamic_cast<const VarTree*>(&n)) {
			insert_dep(deps, v->type()->token);
		} else {
			throw Error("must be RuleTree or VarTree");
		}
	});
}

void find_dependencies(const Assertion& ass, set<Token>& deps) {
	for (auto& h : ass.hyps) {
		find_dependencies(h->expr, deps);
	}
	find_dependencies(ass.prop->expr, deps);
}

void find_dependencies(const Proof& proof, set<Token>& deps) {
	for (auto& s : proof.steps) {
		find_dependencies(s->expr, deps);
		insert_dep(deps, s->ass()->token);
	}
}

void find_dependencies(const Theorem& thm, set<Token>& deps) {
	find_dependencies(static_cast<const Assertion&>(thm), deps);
	find_dependencies(*thm.proof, deps);
}

SrcPos insert_theorem(unique_ptr<Theorem>& thm) {
	set<Token> deps;
	find_dependencies(*thm, deps);
	SrcPos sp = find_infimum(deps);
	//cout << "to insert into: " << sp.show() << endl;
	sp.src->theory.insert(thm.release(), sp.pos);
	return sp;
}

}} // mdl::rus
