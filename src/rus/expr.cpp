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

Symbol::Symbol(string s, Type* t) : mdl::Symbol(System::mod().lex.symbs.toInt(s)), type(t) {
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

string show(const term::Expr& t, bool full) {
	if (t.kind == term::Expr::VAR)
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
	ex.term = term::Expr(rule);
	for (auto& s : ex.symbols) {
		if (s.type)	ex.term.children().push_back(new term::Expr(s));
	}
}

bool Substitution::join(Substitution* s) {
	for (auto& p : s->sub) {
		auto it = sub.find(p.first);
		if (it != sub.end()) {
			if (*(*it).second != *p.second) {
				return false;
			}
		} else {
			sub[p.first] = new term::Expr(*p.second);
		}
	}
	return true;
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


Rule*& Rules::add(const Expr& ex) {
	assert(ex.symbols.size());
	Rules* m = this;
	Node* n = nullptr;
	for (const Symbol& s : ex.symbols) {
		bool new_symb = true;
		for (Node& p : m->map) {
			if (p.symb == s) {
				n = &p;
				m = &p.tree;
				new_symb = false;
				break;
			}
		}
		if (new_symb) {
			if (m->map.size()) m->map.back().symb.fin = false;
			m->map.push_back(Node(s));
			n = &m->map.back();
			n->symb.fin = true;
			m = &n->tree;
		}
	}
	return n->rule;
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
void dump(const term::Expr* tm) { cout << show(*tm) << endl; }
void dump_ast(const term::Expr& tm) { cout << show_ast(tm) << endl; }
void dump(const Substitution& sb) { cout << show(sb) << endl; }

}} // mdl::rus
