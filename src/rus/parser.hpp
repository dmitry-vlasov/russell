#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "rus/globals.hpp"
#include "rus/adaptors.hpp"

namespace mdl { namespace rus {

namespace qi = boost::spirit::qi;
namespace ascii = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

inline Type* find_type(uint id, Location* loc = nullptr) {
	if (!Rus::get().math.types.has(id))
		throw Error("unknown type", show_id(id), loc);
	return Rus::get().math.types[id];
}

struct AddToMath {
	void operator()(Const* c) const {
		Rus::mod().math.consts.s.insert(c->symb);
	}
	void operator()(Type* t) const {
		Rus::mod().math.types[t->id] = t;
	}
	void operator()(Rule* r) const {
		r->type->rules.add(r->term) = r;
		Rus::mod().math.rules[r->id] = r;
	}
	void operator()(Axiom* a) const {
		Rus::mod().math.axioms[a->ass.id] = a;
	}
	void operator()(Theorem* th) const {
		Rus::mod().math.theorems[th->ass.id] = th;
	}
	void operator()(Proof* p) const {
		// TODO:
		//Rus::mod().math.proofs[p->id] = p;
	}
};

struct SymbToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& s) const {
		string symb(s.begin(), s.end());
		return Rus::mod().lex.symbs.toInt(symb);
	}
};

struct IdToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& id) const {
		string id_str(id.begin(), id.end());
		return Rus::mod().lex.ids.toInt(id_str);
	}
};

struct AddSymbol {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Expr& ex, Symbol s) const {
		return ex.push_back(s);
	}
};

struct ParseExpr {
	template <typename T1, typename T2, typename T3>
	struct result { typedef void type; };
	void operator()(Expr& ex, Type* tp, vector<Vars> var_stack) const {
		ex.type = tp;
		parse_expr(ex, var_stack);
	}
};

struct ParseTerm {
	template <typename T1, typename T2, typename T3, typename T4>
	struct result { typedef void type; };
	void operator()(Expr& ex, Rule* r, vector<Vars> var_stack) const {
		ex.type = r->type;
		parse_term(ex, var_stack, r);
	}
};


struct ParseImport {
	template <typename T>
	struct result { typedef Source* type; };
	Source* operator()(const string& path) const {
		// TODO
		return nullptr; //parse(path);
	}
};

struct FindType {
	template <typename T>
	struct result { typedef Type* type; };
	Type* operator()(uint id) const {
		return (id == (uint)-1) ? nullptr : find_type(id);
	}
};

struct FindTheorem {
	template <typename T>
	struct result { typedef Theorem* type; };
	Theorem* operator()(uint id) const {
		if (!Rus::get().math.theorems.has(id))
			throw Error("unknown theorem", show_id(id));
		return Rus::get().math.theorems[id];
	}
};

struct FindAxiom {
	template <typename T1>
	struct result { typedef Axiom* type; };
	Axiom* operator()(uint id) const {
		if (!Rus::get().math.axioms.has(id))
			throw Error("unknown axiom", show_id(id));
		return Rus::get().math.axioms[id];
	}
};

struct FindDef {
	template <typename T1>
	struct result { typedef Def* type; };
	Def* operator()(uint id) const {
		if (!Rus::get().math.defs.has(id))
			throw Error("unknown definition", show_id(id));
		return Rus::get().math.defs[id];
	}
};

struct AddDisjVar {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(vector<vector<Symbol>>& disj, Symbol v) const {
		disj.back().push_back(v);
	}
};

struct NewDisjSet {
	template <typename T>
	struct result { typedef void type; };
	void operator()(vector<vector<Symbol>>& disj) const {
		disj.push_back(vector<Symbol>());
	}
};

struct CreateStepRef {
	template <typename T1, typename T2, typename T3>
	struct result { typedef void Ref; };
	Ref operator()(uint ind, Proof* p, Ref::Kind k) const {
		switch (k) {
		case Ref::HYP:  return Ref(p->thm->ass.hyps[ind]);
		case Ref::PROP: return Ref(p->thm->ass.props[ind]);
		case Ref::STEP: return Ref(p->elems[ind].val.step);
		default : assert(false && "impossible"); break;
		}
		return Ref();
	}
};

struct GetProp {
	template <typename T1, typename T2>
	struct result { typedef Prop* type; };
	Prop* operator()(uint ind, Proof* p) const {
		return p->thm->ass.props[ind];
	}
};

struct GetStep {
	template <typename T1, typename T2>
	struct result { typedef Step* type; };
	Step* operator()(uint ind, Proof* p) const {
		return p->elems[ind].val.step;
	}
};


template<typename Iterator>
struct SetLocation {
    template <typename T1, typename T2>
    struct result { typedef void type; };
    void operator()(Assertion* ass, Iterator it) const {
    	ass->loc = it.loc;
    }
};

struct PushVars {
	template <typename T1>
	struct result { typedef void type; };
	void operator()(vector<Vars>& var_stack) const {
		var_stack.push_back(Vars());
	}
};

struct AddVars {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(vector<Vars>& var_stack, Vars vars) const {
		for (auto v : vars.v) {
			var_stack.back().v.push_back(v);
		}
	}
	void operator()(vector<Vars>& var_stack, Theorem* thm) const {
		for (auto v : thm->ass.vars.v) {
			var_stack.back().v.push_back(v);
		}
	}
};

struct PopVars {
	template <typename T1>
	struct result { typedef void type; };
	void operator()(vector<Vars>& varStack) const {
		varStack.pop_back();
	}
};

template <typename Iterator>
struct Grammar : qi::grammar<Iterator, rus::Source(), ascii::space_type> {
	Grammar();
	void initNames();

	vector<Vars> var_stack;
	qi::rule<Iterator, qi::unused_type> bar;
	qi::rule<Iterator, Expr(Rule*), ascii::space_type> term;
	qi::rule<Iterator, Expr(Type*), ascii::space_type> expr;
	qi::rule<Iterator, Symbol(), ascii::space_type> symb;
	qi::rule<Iterator, uint(),        ascii::space_type> id;
	qi::rule<Iterator, std::string(), ascii::space_type> path;
	qi::rule<Iterator, Disj(), ascii::space_type> disj;
	qi::rule<Iterator, Vars(), qi::locals<Symbol>, ascii::space_type> vars;
	qi::rule<Iterator, Hyp*(), qi::locals<uint>, ascii::space_type> hyp;
	qi::rule<Iterator, Prop*(), qi::locals<uint>, ascii::space_type> prop;

	qi::rule<Iterator, Ref(Proof*), ascii::space_type> ref;
	qi::rule<Iterator, vector<Ref>(Proof*), ascii::space_type> refs;
	qi::rule<Iterator, Step*(Proof*), qi::locals<uint>, qi::locals<Step::Kind>, ascii::space_type> step;
	qi::rule<Iterator, Qed*(Proof*), qi::locals<uint>, ascii::space_type> qed;
	qi::rule<Iterator, Proof::Elem(Proof*), ascii::space_type> proof_elem;


	qi::rule<Iterator, void(Proof*), ascii::space_type> proof_body;
	qi::rule<Iterator, Proof*(), ascii::space_type> proof;
	qi::rule<Iterator, Theorem*(), qi::locals<Assertion*>, ascii::space_type> theorem;
	qi::rule<Iterator, Def*(),qi::locals<Assertion*>, ascii::space_type> def;
	qi::rule<Iterator, Axiom*(), qi::locals<Assertion*>, ascii::space_type> axiom;
	qi::rule<Iterator, void(Assertion*), ascii::space_type> assertion;
	qi::rule<Iterator, Rule*(), ascii::space_type> rule;
	qi::rule<Iterator, Type*(), ascii::space_type> type;
	qi::rule<Iterator, Const*(), ascii::space_type> constant;
	qi::rule<Iterator, Source*(), ascii::space_type> import;
	qi::rule<Iterator, qi::unused_type, ascii::space_type> comment;
	qi::rule<Iterator, Source(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	bar.name("bar");
	expr.name("expr");
	symb.name("symbol");
	id.name("id");
	path.name("path");
	disj.name("disjointed");
	vars.name("variables");
	prop.name("prop");
	hyp.name("hyp");
	proof.name("proof");
	theorem.name("theorem");
	def.name("def");
	axiom.name("axiom");
	assertion.name("assertion");
	rule.name("rule");
	type.name("type");
	constant.name("constant");
	comment.name("comment");
	import.name("import");
	source.name("source");
}

}} // mdl::rus
