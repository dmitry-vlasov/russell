#include "rus/expr.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace expr {

struct State;

struct Product {
	Product(Symbol l, Symbol r);
	Product(Rule*);
	Symbol         left;
	vector<Symbol> right;
	Rule*          rule;
	uint           ind;
};

string show(const Product&);

struct Action {
	enum Kind {
		ERROR, SHIFT, REDUCE, ACCEPT
	};
	union Value {
		void*    none;
		Product* prod;
		State*   state;
	};
	Action() : kind(ERROR), val() {
		val.none = nullptr;
	}
	Kind kind;
	Value val;
};

string show(const Action&);

typedef map<State*, map<Symbol, State*>> Gotos;
typedef map<State*, map<Symbol, Action>> Actions;
typedef map<Type*, State*>               Inits;

struct Table {
	Inits   inits;
	Gotos   gotos;
	Actions actions;
};

string show(const Table&);
string show_lr();

void add_type(Type*);
void add_rule(Rule*);
void add_const(Const*);
void parse(Expr& ex);

Table& table();

inline Symbol eps()        { return Symbol(-2); }
inline Symbol end_marker() { return Symbol(-3); }
inline bool is_terminal(Symbol s) { return !s.type; }
inline bool is_non_term(Symbol s) { return s.type; }


}}} // namespace mdl::rus::expr
