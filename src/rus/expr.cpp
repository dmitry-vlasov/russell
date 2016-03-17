#include "rus/globals.hpp"

namespace mdl {
namespace rus {

string show(Symbol s) {
	return show_sy(s.lit);
}

string show(const Expr& ex) {
	string s;
	for (auto& e : ex.term)
		s += show(e.symb) + " ";
	return s;
}

Expr::Expr(const mdl::Expr& ex) : term() {
	for (auto it = ex.symbols.begin(); it != ex.symbols.end(); ++ it) {
		// pass the first symbol
		if (it == ex.symbols.begin())
			continue;
		push_back(*it);
	}
}

/*
Expr::Expr(const mdl::Expr& ex) : term() {
	List* prev  = nullptr;
	List* first = nullptr;
	List* last  = nullptr;
	for (auto it = ex.symbols.begin(); it != ex.symbols.end(); ++ it) {
		// pass the first symbol
		if (it == ex.symbols.begin())
			continue;
		List* last = new List;
		if (!first) first = last;
		last->symb = Symbol(*it);
		last->prev = prev;
		last->next = nullptr;
		if (prev) prev->next = last;
		prev = last;
	}
	term.b = first;
	term.e = last;
}
 */

void Expr::push_back(Symbol s) {
	if (!term.b) {
		term.b = new List;
		term.b->symb = s;
		term.e = term.b;
	} else {
		List* n = new List;
		n->symb = s;
		n->prev = term.e;
		term.e->next = n;
		term.e = n;
	}
}

void Expr::parse(){
	// TODO
}


}}
