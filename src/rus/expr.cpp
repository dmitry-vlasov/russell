#include "rus/globals.hpp"

namespace mdl {
namespace rus {

string show(Symbol s, bool full) {
	if (!full || !s.type)
		return show_sy(s.lit);
	else {
		return string("<") + show_sy(s.lit) + ":" + show_id(s.type->id) + ">";
	}
}

Symbol::Symbol(string s, Type* t) : mdl::Symbol(Rus::mod().lex.symbs.toInt(s)), type(t) {
}

string show(const Expr& ex) {
	string str;
	for (auto s : ex.symbols) str += show(s) + " ";
	return str;
}

size_t memvol(const Expr& ex) {
	size_t s = 0;
	s += ex.symbols.capacity() * sizeof (Symbols);
	s += memvol(ex.term);
	return s;
}

string show_ast(const term::Expr& t, bool full) {
	if (t.kind == term::Expr::VAR)
		return t.val.var ? show(*t.val.var, full) : "<null>";
	else {
		string s = (t.val.rule ? show_id(t.val.rule->id) : "?") + " (";
		for (uint i = 0; i < t.children.size(); ++ i) {
			s += show_ast(t.children[i], full);
			if (i + 1 < t.children.size()) s += ", ";
		}
		s += ")";
		return s;
	}
}

string show(const term::Expr& t, bool full) {
	if (t.kind == term::Expr::VAR)
		return t.val.var ? show(*t.val.var, full) : "<null>";
	else {
		string str(" ");
		uint i = 0;
		for (auto s : t.val.rule->term.symbols) {
			if (s.type) {
				str += show(t.children[i++], full) + ' ';
			} else {
				str += show(s) + ' ';
			}
		}
		return str;
	}
}

namespace term {
	bool Expr :: operator == (const Expr& t) const {
		if (kind != t.kind) return false;
		switch (kind) {
		case VAR:  return *val.var == *t.val.var;
		case NODE: {
			if (val.rule != t.val.rule) return false;
			auto i_p = children.begin();
			auto i_q = t.children.begin();
			while (i_p != children.end()) {
				if (*i_p != *i_q) return false;
				++ i_p; ++ i_q;
			}
			return true;
		}
		default : break;
		}
		return true;
	}
}


/*
term::Expr assemble_expr(Expr& ex, const term::Expr& t) {
	if (t.isvar()) {
		ex.push_back(t.first->symb);
		ex.term = term::Expr(ex.first);
		return ex.term;
	}
	uint i = 0;
	Expr::Node* n = t.rule ? t.rule->term.first : t.first;
	vector<term::Expr> children;
	while (n) {
		if (n->symb.type) {
			if (i + 1 > t.children.size()) {
				cout << " ERROR!!" << endl;
				ex.push_back(Symbol("<<"));
				ex.push_back(n->symb);
				ex.push_back(Symbol(">>"));
			} else {
				term::Expr ch = assemble_expr(ex, t.children[i++]);
				children.push_back(ch);
			}
		} else
			ex.push_back(n->symb);
		n = n->next;
	}
	return term::Expr(ex.first, ex.last, t.rule, children);
}

Expr assemble(const term::Expr& t) {
	Expr e;
	assemble_expr(e, t);
	e.type = t.rule ? t.rule->type : t.first->symb.type;
	return e;
}

Expr assemble(const Expr& ex) {
	return assemble(ex.term);
}
*/

void parse_term(Expr& ex, Rule* rule) {
	ex.term = term::Expr(rule);
	for (auto& s : ex.symbols) {
		if (s.type)
			ex.term.children.push_back(term::Expr(s));
	}
}

bool sub::Expr::join(Expr* s) {
	for (auto& p : s->sub.m) {
		auto it = sub.m.find(p.first);
		if (it != sub.m.end()) {
			if ((*it).second != p.second) {
				return false;
			}
		} else {
			sub.m[p.first] = p.second;
		}
	}
	return true;
}

Rule*& RuleTree::add(const Expr& ex) {
	assert(ex.symbols.size());
	RuleTree* m = this;
	Node* n = nullptr;
	for (const Symbol& s : ex.symbols) {
		if (s.var) {
			n = &m->type[s.type];
			m = &n->tree;
		} else {
			n = &m->symb[s];
			m = &n->tree;
		}
	}
	return n->rule;
}

void dump(const Symbol& s) { cout << show(s) << endl; }
void dump(const Expr& ex) { cout << show(ex) << endl; }
void dump_ast(const Expr& ex) { cout << show_ast(ex) << endl; }
void dump(const term::Expr* tm) { cout << show(*tm) << endl; }
void dump_ast(const term::Expr& tm) { cout << show_ast(tm) << endl; }
void dump(const sub::Expr& sb) { cout << show(sb) << endl; }

}} // mdl::rus
