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

string show(const Product&);

struct Action {
	enum Kind {
		NONE, SHIFT, REDUCE, ACCEPT
	};
	union Value {
		void*    none;
		Product* prod;
		State*   state;
	};
	Action() : kind(NONE), val() {
		val.none = nullptr;
	}
	bool operator == (const Action& a) {
		return kind == a.kind && val.none == a.val.none;
	}
	bool operator != (const Action& a) {
		return !operator == (a);
	}
	Kind kind;
	Value val;
};

string show(const Action&);

typedef Map<State*, Map<Symbol, State*>> Gotos;
typedef Map<State*, Map<Symbol, Action>> Actions;
typedef Map<Type*, State*>               Inits;
typedef Map<Type*, Symbol>               Vars;

struct Table {
	Inits   inits;
	Vars    vars;
	Gotos   gotos;
	Actions actions;
};

string show(const Symbol&, bool full = true);
string show(const Table&);
string show_lr();

void add_type(Type*);
void add_rule(Rule*);
void add_const(Const*);
//void parse(Expr& ex);

void parse();
void enqueue(Expr& ex);

Table& table();

inline Symbol eps()        { return Symbol(-2); }
inline Symbol end_marker() { return Symbol(-3); }
inline bool is_terminal(Symbol s) { return !s.type; }
inline bool is_non_term(Symbol s) { return s.type; }


}}} // namespace mdl::rus::expr
