#include "rus/ast.hpp"

namespace mdl {
namespace rus {

string show(Symbol s, bool full) {
	if (!full || !s.type)
		return show_sy(s.lit);
	else {
		return string("<") + show_sy(s.lit) + ":" + show_id(s.type->id) + ">";
	}
}

Symbol::Symbol(string s, Type* t) : mdl::Symbol(Lex::toInt(s)), type(t) {
}

string show(const Expr& ex) {
	string str;
	for (auto s : ex.symbols) str += show(s) + " ";
	return str;
}

size_t memvol(const Expr& ex) {
	size_t s = 0;
	s += ex.symbols.capacity() * sizeof (Symbols);
	if (ex.tree) s += memvol(*ex.tree);
	return s;
}

string show_ast(const Tree& t, bool full) {
	if (t.kind == Tree::VAR)
		return t.var() ? show(*t.var(), full) : "<null>";
	else {
		string s = (t.rule() ? show_id(t.rule()->id) : "?") + " (";
		for (uint i = 0; i < t.children().size(); ++ i) {
			s += show_ast(*t.children()[i], full);
			if (i + 1 < t.children().size()) s += ", ";
		}
		s += ")";
		return s;
	}
}

string show(const Tree& t, bool full) {
	if (t.kind == Tree::VAR)
		return t.var() ? show(*t.var(), full) : "<null>";
	else {
		string str(" ");
		uint i = 0;
		for (auto s : t.rule()->term.symbols) {
			if (s.type) {
				str += show(*t.children()[i++], full) + ' ';
			} else {
				str += show(s) + ' ';
			}
		}
		return str;
	}
}

void parse_term(Expr& ex, Rule* rule) {
	Tree::Children children;
	for (auto& s : ex.symbols) {
		if (s.type) children.push_back(make_unique<Tree>(s));
	}
	ex.tree.reset(new Tree(rule, children));
}

vector<string> show_lines(const Rules& tr) {
	vector<string> vect;
	for (const Rules::Node& p : tr.map) {
		vector<string> v = show_lines(p.tree);
		if (p.tree.map.size()) {
			for (string& s : v)
				vect.push_back(show(p.symb) + ' ' + s);
		} else {
			vect.push_back(show(p.symb) + " --> " +
				(p.rule ? show(*p.rule) : "null")
			);
		}
	}
	return vect;
}

string show(const Rules& tr) {
	string str;
	for (string& s : show_lines(tr)) {
		str += s + "\n";
	}
	return str;
}

size_t memvol(const Rules& rt) {
	size_t vol = 0;
	vol += rt.map.capacity() * sizeof (Rules::Node);
	for (auto& p : rt.map) {
		vol += memvol(p.tree);
	}
	return vol;
}


void dump(const Symbol& s) { cout << show(s) << endl; }
void dump(const Expr& ex) { cout << show(ex) << endl; }
void dump_ast(const Expr& ex) { cout << show_ast(ex) << endl; }
void dump(const Tree* tm) { cout << show(*tm) << endl; }
void dump_ast(const Tree& tm) { cout << show_ast(tm) << endl; }
void dump(const Substitution& sb) { cout << show(sb) << endl; }

}} // mdl::rus
