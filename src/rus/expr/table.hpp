#pragma once

#include "rus/expr.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace expr {

struct State;

struct Product {
	enum Kind {
		REGULAR, INIT, VAR, CHAIN
	};
	Product(Symbol l, Symbol r, Kind k = REGULAR);
	Product(Rule*, Kind k = REGULAR);
	Symbol         left;
	vector<Symbol> right;
	Kind           kind;
	Rule*          rule;
	uint           ind;
};

string show(const Product&, bool show_left = true);

struct Action {
	enum Kind {
		NONE, SHIFT, REDUCE, ACCEPT
	};
	union Value {
		void*    ptr;
		Product* prod;
		State*   state;
	};
	Action() : kind(NONE), val() {
		val.ptr = nullptr;
	}
	bool operator == (const Action& a) const {
		return kind == a.kind && val.ptr == a.val.ptr;
	}
	bool operator != (const Action& a) const {
		return !operator == (a);
	}
	bool operator < (const Action& a) const {
		if (kind < a.kind)
			return true;
		else if (kind > a.kind)
			return false;
		else
			return val.ptr < a.val.ptr;
	}
	Kind kind;
	Value val;
};

string show(const Action&);

typedef Map<State*, Map<Symbol, State*>> Gotos;
typedef Map<State*, Map<Symbol, Set<Action>>> Actions;
typedef Map<Type*, State*>               Inits;
typedef Map<Type*, Symbol>               Vars;

struct Table {
	Inits   inits;
	Vars    vars;
	Gotos   gotos;
	Actions actions;
	string show() const;
};

string show(const Symbol&, bool full = true);
string show(const Table&);
string show_lr();
string show_symbols();
string show_grammar();

void add_type(Type*);
void add_rule(Rule*);
void add_const(Const*);
//void parse(Expr& ex);

bool parse();
void enqueue(Expr& ex);

Table& table();

inline Symbol eps()        { return Symbol(-2); }
inline Symbol end_marker() { return Symbol(-3); }
inline bool is_terminal(Symbol s) { return !s.type; }
inline bool is_non_term(Symbol s) { return s.type; }


}}} // namespace mdl::rus::expr
