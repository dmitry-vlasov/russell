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

Symbol::Symbol(string s, Type* t) : lit(UNDEF), rep(false), type(t) {
	lit = Rus::mod().lex.symbs.toInt(s);
}

string show(const Expr& ex) {
	string s;
	Expr::Node* n = ex.first;
	while (n) {
		s += show(n->symb) + " ";
		n = n->next;
	}
	return s;
}

size_t memvol(const Expr& ex) {
	size_t s = 0;
	Expr::Node* n = ex.first;
	while (n) {
		s += memsize(*n);
		n = n->next;
	}
	s += memvol(ex.term);
	return s;
}
/*
string show_ast(const term::Expr& t, bool full) {
	if (t.isvar())
		return t.first ? show(t.first->symb, full) : "<null>";
	else {
		string s = (t.rule ? show_id(t.rule->id) : "?") + " (";
		for (uint i = 0; i < t.children.size(); ++ i) {
			s += show_ast(t.children[i], full);
			if (i + 1 < t.children.size()) s += ", ";
		}
		s += ")";
		return s;
	}
}
*/
term::Expr copy_term(const term::Expr& st, map<node::Expr*, node::Expr*>& mp) {
	if (st.kind == term::Expr::VAR)
		return term::Expr(st.val.var);

	term::Expr tt(st.val.node->rule);
	for (auto ch : st.val.node->children) {
		tt.val.node->children.push_back(copy_term(ch, mp));
	}
	return tt;
}

Expr::Expr(const Expr& ex) : first(nullptr), last(nullptr), type(ex.type), term() {
	map<Node*, Node*> mp;
	Node* n = ex.first;
	while (n){
		push_back(n->symb);
		mp[n] = last;
		n = n->next;
	}
	term = copy_term(ex.term, mp);
}
/*
Expr::Expr(Expr&& ex) : first(ex.first), last(ex.last), type(ex.type), term(ex.term) {
	ex.first = nullptr;
	ex.last  = nullptr;
	ex.type  = nullptr;
	//ex.term  = nullptr;
}
*/
Expr::~Expr() {
	Node* n = last;
	while (n) {
		Node* to_delete = n;
		n = n->prev;
		delete to_delete;
	}
}
Expr& Expr::operator = (const Expr& ex) {
	Node* n = last;
	while (n) {
		Node* to_delete = n;
		n = n->prev;
		delete to_delete;
	}
	last = nullptr;
	first = nullptr;
	type = ex.type;
	map<Node*, Node*> mp;
	n = ex.first;
	while (n){
		push_back(n->symb);
		mp[n] = last;
		n = n->next;
	}
	term = copy_term(ex.term, mp);
	return *this;
}

Expr& Expr::operator = (Expr&& ex) {
	first = ex.first;
	last  = ex.last;
	type  = ex.type;
	term  = ex.term;
	ex.first = nullptr;
	ex.last  = nullptr;
	ex.type  = nullptr;
	ex.term  = term::Expr();
	return *this;
}
void Expr::push_back(Symbol s) {
	if (!first) {
		first = new Node(s);
		last  = first;
	} else {
		last->next = new Node(s);
		last->next->prev = last;
		last = last->next;
	}
}

void Expr::push_front(Symbol s) {
	if (!first) {
		first = new Node(s);
		last  = first;
	} else {
		first->prev = new Node(s);
		first->prev->next = first;
		first = first->prev;
	}
}

Symbol Expr::pop_back() {
	assert(first);
	Symbol s = last->symb;
	if (last == first) {
		delete first;
		first = nullptr;
	} else {
		last = last->prev;
		delete last->next;
	}
	return s;
}

bool Expr::operator == (const Expr& ex) const {
	const Node* n = ex.first;
	const Node* m = first;
	while (n && m) {
		if (n->symb != m->symb) return false;
		n = n->next; m = m ->next;
	}
	return !n && !m;
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
term::Expr create_term(Expr::Node* first, Expr::Node* last, Rule* rule) {
	term::Expr term(rule);
	Expr::Node* n = first;
	while (n) {
		if (n->symb.type)
			term.val.node->children.push_back(term::Expr(n));
		n = n->next;
	}
	return term;
}

void parse_term(Expr& ex, Rule* rule) {
	ex.term = create_term(ex.first, ex.last, rule);
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

void dump(const Symbol& s) { cout << show(s) << endl; }
void dump(const Expr& ex) { cout << show(ex) << endl; }
//void dump_ast(const Expr& ex) { cout << show_ast(ex) << endl; }
//void dump(const term::Expr* tm) { cout << show(*tm) << endl; }
//void dump_ast(const term::Expr& tm) { cout << show_ast(tm) << endl; }
//void dump(const sub::Expr& sb) { cout << show(sb) << endl; }

}} // mdl::rus
