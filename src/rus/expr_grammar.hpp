#include "rus/expr.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace expr {

struct State;

struct Product {
	Product(Symbol l, Symbol r) : left(l), right(), rule(nullptr) {
		right.push_back(r);
	}
	Product(rus::Rule*);
	Symbol          left;
	vector<Symbol>  right;
	rus::Rule*      rule;
};


struct Action {
	enum Kind {
		ERROR, SHIFT, REDUCE, ACCEPT
	};
	union Value {
		void*    none;
		Product* prod;
		State*   state;
	};
	Kind kind;
	Value val;
};

typedef map<State*, map<Symbol, State*>> Gotos;
typedef map<State*, map<Symbol, Action>> Actions;
typedef map<Type*, State*>               Inits;

struct Table {
	Inits   inits;
	Gotos   gotos;
	Actions actions;
};

void add_rule(rus::Rule*);
void parse(Expr& ex);

Table& table();

inline Symbol eps()        { return Symbol(-2); }
inline Symbol end_marker() { return Symbol(-3); }
inline bool is_terminal(Symbol s) { return !s.type; }
inline bool is_non_term(Symbol s) { return s.type; }


}}} // namespace mdl::rus::expr
