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
		Node* prev = term.e->prev;
		delete term.e;
		term.e = prev;
	}
	term.b = nullptr;
	term.e = nullptr;
}

void Expr::push_back(Symbol s) {
	if (!term.b) {
		term.b = new Node(s);
		term.e = term.b;
	} else {
		Node* n = new Node(s);
		n->prev = term.e;
		term.e->next = n;
		term.e = n;
	}
}

inline Type* find_type(Vars& vars, Symbol s) {
	for (auto var : vars.v)
		if (var.lit == s.lit) return var.type;
	return nullptr;
}

inline Type* find_type(vector<Vars>& var_stack, Symbol s) {
	for (auto& vars : var_stack)
		if (Type* tp = find_type(vars, s)) return tp;
	return nullptr;
}

void parse_prim(Expr& ex, vector<Vars>& var_stack) {
	for (auto n : ex.term) {
		n.symb.type = find_type(var_stack, n.symb);
		bool is_var = n.symb.type != nullptr;
		bool is_const = Rus::get().math.consts.has(n.symb);
		if (is_const && is_var)
			throw Error("constant symbol is marked as variable");
		if (!is_const && !is_var)
			throw Error("symbol neither constant nor variable");
	}
	ex.term.b->init.push_back(ex.term);
	ex.term.e->final.push_back(ex.term);
}

void parse_cplx(Expr& ex, vector<Vars>& var_stack) {

}

void parse(Expr& ex, vector<Vars>& var_stack, bool prim){
	if (prim)
		parse_prim(ex, var_stack);
	else
		parse_cplx(ex, var_stack);
}


}} // mdl::rus
