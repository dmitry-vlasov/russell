#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "rus/globals.hpp"
#include "rus/parser/adaptors.hpp"

namespace mdl { namespace rus { namespace parser {

namespace qi      = boost::spirit::qi;
namespace unicode = boost::spirit::unicode;
namespace phoenix = boost::phoenix;

struct MakeString {
	template <typename T>
	struct result { typedef string type; };
	string operator()(const vector<uint>& s) const {
		return string(s.begin(), s.end());
	}
};

struct IncInd {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()() const {
		return inc_ind();
	}
};

struct VarStack {
	vector<Vars> stack;
	map<Symbol, Type*> mapping;
};

struct PushVars {
	template <typename T1>
	struct result { typedef void type; };
	void operator()(VarStack& var_stack) const {
		var_stack.stack.push_back(Vars());
	}
};

struct AddVars {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(VarStack& var_stack, Vars vars) const {
		for (auto v : vars.v) {
			var_stack.stack.back().v.push_back(v);
			var_stack.mapping[v.lit] = v.type;
		}
	}
	void operator()(VarStack& var_stack, Theorem* thm) const {
		for (auto v : thm->ass.vars.v) {
			var_stack.stack.back().v.push_back(v);
			var_stack.mapping[v.lit] = v.type;
		}
	}
};

struct PopVars {
	template <typename T1>
	struct result { typedef void type; };
	void operator()(VarStack& var_stack) const {
		Vars& vars = var_stack.stack.back();
		for (auto v : vars.v)
			var_stack.mapping.erase(v.lit);
		var_stack.stack.pop_back();
	}
};

static void mark_vars(Expr& ex, VarStack& var_stack) {
	for (auto& s : ex.symbols) {
		bool is_var = var_stack.mapping.count(s.lit);
		bool is_const = System::get().math.consts.count(s.lit);
		if (is_const && is_var)
			throw Error("constant symbol is marked as variable");
		if (!is_const && !is_var) {
			string msg = "symbol " + Lex::toStr(s.lit) + " ";
			msg += " neither constant nor variable";
			throw Error(msg);
		}
		if (is_var) s.type = var_stack.mapping[s.lit];
	}
}

inline Type* find_type(uint id, Location* loc = nullptr) {
	if (!System::get().math.types.count(id))
		throw Error("unknown type", show_id(id), loc);
	return System::mod().math.types[id];
}

inline uint create_id(string pref, string s1, string s2) {
	return Lex::toInt(pref + "_" + s1 + "_" + s2);
}

inline Symbol create_symbol(string str, Type* tp) {
	return Symbol(Lex::toInt(str), tp, tp);
}

Rule* create_super(Type* inf, Type* sup) {
	Rule* rule = new Rule;
	rule->id = create_id("sup", show_id(inf->id), show_id(sup->id));
	rule->vars.v.push_back(create_symbol("x", inf));
	rule->term.push_back(create_symbol("x", inf));
	rule->type = sup;

	VarStack var_stack;
	AddVars add_vars;
	PushVars push_vars;
	push_vars(var_stack);
	add_vars(var_stack, rule->vars);
	mark_vars(rule->term, var_stack);
	parse_term(rule->term, rule);
	return rule;
}

void collect_supers(Type* inf, Type* s) {
	for (auto sup : s->sup) {
		Rule* super = create_super(inf, sup);
		inf->supers[sup] = super;
		collect_supers(inf, sup);
	}
}

void enqueue_expressions(Assertion& ass) {
	for (Hyp* hyp : ass.hyps)
		expr::enqueue(hyp->expr);
	for (Prop* prop : ass.props)
		expr::enqueue(prop->expr);
}

void enqueue_expressions(Proof* proof) {
	for (auto& el : proof->elems) {
		if (el.kind == Proof::Elem::STEP) {
			Step* step = el.val.step;
			expr::enqueue(step->expr);
			if (step->kind == Step::CLAIM)
				enqueue_expressions(step->proof);
		}
	}
}

void enqueue_expressions(Def* def) {
	expr::enqueue(def->dfm);
	expr::enqueue(def->dfs);
	enqueue_expressions(def->ass);
}

struct AddToMath {
	void operator()(Const* c) const {
		//cout << "c: " << show(c->symb) << endl;
		System::mod().math.consts[c->symb.lit] = c;
	}
	void operator()(Type* t) const {
		//cout << "tp: " << show_id(t->id) << endl;
		collect_supers(t, t);
		System::mod().math.types[t->id] = t;
	}
	void operator()(Rule* r) const {
		//cout << "ru: " << show_id(r->id) << endl;
		r->type->rules.add(r->term) = r;
		//cout << show(r->type->rules) << endl;
		System::mod().math.rules[r->id] = r;
	}
	void operator()(Axiom* a) const {
		//cout << "ax: " << show_id(a->ass.id) << endl;
		System::mod().math.axioms[a->ass.id] = a;
		enqueue_expressions(a->ass);
	}
	void operator()(Def* d) const {
		//cout << "def: " << show_id(d->ass.id) << endl;
		System::mod().math.defs[d->ass.id] = d;
		enqueue_expressions(d);
	}
	void operator()(Theorem* th) const {
		//cout << "th: " << show_id(th->ass.id) << endl;
		System::mod().math.theorems[th->ass.id] = th;
		enqueue_expressions(th->ass);
	}
	void operator()(Proof* p) const {
		//cout << "pr: " << show_id(p->thm->ass.id) << endl;
		p->has_id = !Undef<uint>::is(p->id);
		if (!p->has_id) p->id = Lex::toInt(to_string(p->ind));
		System::mod().math.proofs[p->id] = p;
		enqueue_expressions(p);
	}
};

struct SymbToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<uint>& s) const {
		string symb(s.begin(), s.end());
		return Lex::toInt(symb);
	}
};

struct IdToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<uint>& id) const {
		string id_str(id.begin(), id.end());
		return Lex::toInt(id_str);
	}
};

struct AddSymbol {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Expr& ex, Symbol s) const {
		return ex.push_back(s);
	}
};

struct CreateSymb {
	template <typename T>
	struct result { typedef Symbol type; };
	Symbol operator()(const std::vector<uint>& s) const {
		string symb(s.begin(), s.end());
		return Symbol(Lex::toInt(symb));
	}
};

struct ParseExpr {
	template <typename T1, typename T2, typename T3>
	struct result { typedef void type; };
	void operator()(Expr& ex, Type* tp, VarStack& var_stack) const {
		ex.type = tp;
		mark_vars(ex, var_stack);
	}
};

struct ParseTerm {
	template <typename T1, typename T2, typename T3, typename T4>
	struct result { typedef void type; };
	void operator()(Expr& ex, Rule* r, VarStack& var_stack) const {
		ex.type = r->type;
		mark_vars(ex, var_stack);
		parse_term(ex, r);
	}
};

template<class> class Grammar;

struct ParseImport {
	template <typename T>
	struct result { typedef Import* type; };
	Import* operator()(string path) const {
		typedef Grammar<LocationIter> Parser;
		return
			mdl::include<Source, Parser, Import>(
				path,
				System::get().config.root,
				unicode::space,
				[] (Import* inc) -> Source* { return inc->source; }
			);
	}
};

struct FindType {
	template <typename T>
	struct result { typedef Type* type; };
	Type* operator()(uint id) const {
		return Undef<uint>::is(id) ? nullptr : find_type(id);
	}
};

struct FindTheorem {
	template <typename T>
	struct result { typedef Theorem* type; };
	Theorem* operator()(uint id) const {
		if (!System::get().math.theorems.count(id))
			throw Error("unknown theorem", show_id(id));
		return System::mod().math.theorems[id];
	}
};

struct FindAxiom {
	template <typename T1>
	struct result { typedef Axiom* type; };
	Axiom* operator()(uint id) const {
		if (!System::get().math.axioms.count(id))
			throw Error("unknown axiom", show_id(id));
		return System::mod().math.axioms[id];
	}
};

struct FindDef {
	template <typename T1>
	struct result { typedef Def* type; };
	Def* operator()(uint id) const {
		if (!System::get().math.defs.count(id))
			throw Error("unknown definition", show_id(id));
		return System::mod().math.defs[id];
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

struct AssembleDef {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Def* d, VarStack& varsStack) const {
		static Symbol dfm(Lex::toInt("defiendum"));
		static Symbol dfs(Lex::toInt("definiens"));
		Prop* prop = new Prop;
		for (auto s : d->prop.symbols) {
			if (s == dfm) {
				for (auto s_dfm : d->dfm.symbols)
					prop->expr.push_back(s_dfm);
			} else if (s == dfs) {
				for (auto s_dfs : d->dfs.symbols)
					prop->expr.push_back(s_dfs);
			} else
				prop->expr.push_back(s);
		}
		prop->ind = 0;
		prop->expr.type = d->prop.type;
		mark_vars(prop->expr, varsStack);
		d->ass.props.push_back(prop);
	}
};


struct DeleteComment {
	template <typename T>
	struct result { typedef void type; };
	void operator()(Comment* c) const {
		delete c;
	}
};

struct AppendComment {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Comment* c1, Comment* c2) const {
		c1->text += show(*c2);
		delete c2;
	}
};

template <typename Iterator>
struct Grammar : qi::grammar<Iterator, rus::Source(), unicode::space_type> {
	Grammar();
	void initNames();

	VarStack var_stack;
	qi::rule<Iterator, qi::unused_type> bar;
	qi::rule<Iterator, Symbol(), unicode::space_type> var;
	qi::rule<Iterator, Symbol(), unicode::space_type> symb;
	qi::rule<Iterator, uint(), unicode::space_type> id;
	qi::rule<Iterator, string(), unicode::space_type> path;
	qi::rule<Iterator, void(Expr&, Rule*), unicode::space_type> term;
	qi::rule<Iterator, void(Expr&, Type*), unicode::space_type> expr;
	qi::rule<Iterator, void(Expr&, Type*), unicode::space_type> plain;
	qi::rule<Iterator, Disj(), unicode::space_type> disj;
	qi::rule<Iterator, Vars(), qi::locals<Symbol>, unicode::space_type> vars;
	qi::rule<Iterator, Hyp*(), qi::locals<uint>, unicode::space_type> hyp;
	qi::rule<Iterator, Prop*(), qi::locals<uint>, unicode::space_type> prop;
	qi::rule<Iterator, Ref(Proof*), unicode::space_type> ref;
	qi::rule<Iterator, vector<Ref>(Proof*), unicode::space_type> refs;
	qi::rule<Iterator, Step*(Proof*), qi::locals<uint, Step::Kind>, unicode::space_type> step;
	qi::rule<Iterator, Qed*(Proof*), qi::locals<uint>, unicode::space_type> qed;
	qi::rule<Iterator, Proof::Elem(Proof*), unicode::space_type> proof_elem;
	qi::rule<Iterator, void(Proof*), unicode::space_type> proof_body;
	qi::rule<Iterator, Proof*(), unicode::space_type> proof;
	qi::rule<Iterator, Theorem*(), qi::locals<Assertion*>, unicode::space_type> theorem;
	qi::rule<Iterator, Def*(), qi::locals<Assertion*, Type*>, unicode::space_type> def;
	qi::rule<Iterator, Axiom*(), qi::locals<Assertion*>, unicode::space_type> axiom;
	qi::rule<Iterator, void(Assertion*), unicode::space_type> assertion;
	qi::rule<Iterator, Rule*(), unicode::space_type> rule;
	qi::rule<Iterator, Type*(), unicode::space_type> type;
	qi::rule<Iterator, Const*(), unicode::space_type> constant;
	qi::rule<Iterator, Import*(), unicode::space_type> import;
	qi::rule<Iterator, string(), qi::unused_type> comment_text;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment_ml;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment_sl;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment;
	qi::rule<Iterator, Source(), unicode::space_type> source;

	static bool parse(Iterator& beg, Iterator& end, auto space, Source& src) {
		return qi::phrase_parse(beg, end, Grammar(), space, src);
	}
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	bar.name("bar");
	var.name("var");
	symb.name("symbol");
	expr.name("expr");
	id.name("id");
	path.name("path");
	term.name("term");
	plain.name("plain");
	disj.name("disjointed");
	vars.name("variables");
	prop.name("prop");
	hyp.name("hyp");
	ref.name("ref");
	refs.name("refs");
	step.name("step");
	qed.name("qed");
	proof_elem.name("proof_elem");
	proof_body.name("proof_body");
	proof.name("proof");
	theorem.name("theorem");
	def.name("def");
	axiom.name("axiom");
	assertion.name("assertion");
	rule.name("rule");
	type.name("type");
	constant.name("constant");
	comment_text.name("comment text");
	comment_ml.name("multiline comment");
	comment_sl.name("singleline comment");
	comment.name("comment");
	import.name("import");
	source.name("source");
}

}}} // mdl::rus::parser
