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

Expr::Expr(const mdl::Expr& ex) : term(), type(nullptr) {
	for (auto it = ex.symbols.begin(); it != ex.symbols.end(); ++ it) {
		// pass the first symbol
		if (it == ex.symbols.begin())
			continue;
		push_back(*it);
	}
}

void Expr::destroy() {
	while (term.e) {
		List* prev = term.e->prev;
		delete term.e;
		term.e = prev;
	}
	term.b = nullptr;
	term.e = nullptr;
}

void Expr::push_back(Symbol s) {
	if (!term.b) {
		term.b = new List(s);
		term.e = term.b;
	} else {
		List* n = new List(s);
		n->prev = term.e;
		term.e->next = n;
		term.e = n;
	}
}

void parse(Expr& ex, const vector<Vars>& varsStack, bool prim){
	// TODO
}


}}
