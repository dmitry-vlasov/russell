#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/qi_uint.hpp>

#include "rus/ast.hpp"
#include "rus/parser/adaptors.hpp"

namespace mdl { namespace rus {

Source* parse(uint);

namespace parser {

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

struct VarStack {
	stack<vector<uint>> vstack;
	map<uint, Type*> mapping;
};

struct PushVars {
	template <typename T1>
	struct result { typedef void type; };
	void operator()(VarStack& var_stack) const {
		var_stack.vstack.push(vector<uint>());
	}
};

struct AddVars {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(VarStack& var_stack, Vars& vars) const {
		for (auto& v : vars.v) {
			var_stack.vstack.top().push_back(v.lit);
			var_stack.mapping[v.lit] = v.type();
		}
	}
	void operator()(VarStack& var_stack, Theorem* thm) const {
		for (auto& v : thm->ass.vars.v) {
			var_stack.vstack.top().push_back(v.lit);
			var_stack.mapping[v.lit] = v.type();
		}
	}
};

struct PopVars {
	template <typename T1>
	struct result { typedef void type; };
	void operator()(VarStack& var_stack) const {
		vector<uint>& vars = var_stack.vstack.top();
		for (uint v : vars)
			var_stack.mapping.erase(v);
		var_stack.vstack.pop();
	}
};

static void mark_vars(Expr& ex, VarStack& var_stack) {
	for (auto& s : ex.symbols) {
		bool is_var = var_stack.mapping.count(s.lit);
		bool is_const = Sys::get().math.get<Const>().has(s.lit);
		if (is_const && is_var)
			throw Error("constant symbol is marked as variable");
		if (!is_const && !is_var) {
			string msg = "symbol " + Lex::toStr(s.lit) + " ";
			msg += " neither constant nor variable";
			throw Error(msg);
		}
		if (is_var) s.set_type(var_stack.mapping[s.lit]);
		else s.set_const(Sys::mod().math.get<Const>().access(s.lit));
	}
}

inline Type* find_type(uint id, const Location* loc = nullptr) {
	if (!Sys::get().math.get<Type>().has(id))
		throw Error("unknown type", show_id(id), loc);
	return Sys::mod().math.get<Type>().access(id);
}

inline uint create_id(string pref, string s1, string s2) {
	return Lex::toInt(pref + "_" + s1 + "_" + s2);
}

inline Symbol create_var(string str, Type* tp) {
	return Symbol(Lex::toInt(str), tp);
}

inline Symbol create_const(string str, Const* c) {
	return Symbol(Lex::toInt(str), c);
}

Rule* create_super(Type* inf, Type* sup) {
	uint id = create_id("sup", show_id(inf->id()), show_id(sup->id()));
	Rule* rule = new Rule(id, sup->id());
	rule->vars.v.push_back(create_var("x", inf));
	rule->term.push_back(create_var("x", inf));

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
	for (auto& sup : s->sup) {
		Rule* super = create_super(inf, sup.get());
		inf->supers[sup.get()] = super;
		collect_supers(inf, sup.get());
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
			if (step->kind() == Step::CLAIM)
				enqueue_expressions(step->proof());
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
	}
	void operator()(Type* t) const {
		collect_supers(t, t);
	}
	void operator()(Rule* r) const {
		r->type.get()->rules.add(r->term, r->id());
	}
	void operator()(Axiom* a) const {
		enqueue_expressions(a->ass);
	}
	void operator()(Def* d) const {
		enqueue_expressions(d);
	}
	void operator()(Theorem* th) const {
		enqueue_expressions(th->ass);
	}
	void operator()(Proof* p) const {
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
		ex.type = r->type.get();
		mark_vars(ex, var_stack);
		parse_term(ex, r);
	}
};

struct ParseImport {
	template <typename T1, typename T2>
	struct result { typedef Import* type; };
	Import* operator()(string name, Source* src) const {
		static map<string, Import*> imported;
		Path::remove_ext(name);
		Import* imp = nullptr;
		if (imported.count(name)) {
			imp = new Import(imported[name]->source.id(), false);
		} else {
			imp = new Import(true);
			imported[name] = imp;
			imp->source = parse(Lex::toInt(name));
		}
		src->include(imp->source.get());
		return imp;
	}
};

struct FindType {
	template <typename T>
	struct result { typedef Type* type; };
	Type* operator()(uint id) const {
		return Undef<uint>::is(id) ? nullptr : find_type(id);
	}
};

struct SetType {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Symbol& s, Type* t) const {
		s.set_type(t);
	}
};

struct FindTheorem {
	template <typename T>
	struct result { typedef Theorem* type; };
	Theorem* operator()(uint id) const {
		if (!Sys::get().math.get<Assertion>().has(id))
			throw Error("unknown theorem", show_id(id));
		Theorem* ret = dynamic_cast<Theorem*>(Sys::mod().math.get<Assertion>().access(id));
		if (!ret)
			throw Error("not a theorem", show_id(id));
		return ret;
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
struct SetToken {
    template <typename T1, typename T2, typename T3, typename T4>
    struct result { typedef void type; };
    void operator()(Token& token, Iterator beg, Iterator end, Source* src) const {
    	token.beg = &*beg;
    	token.end = &*end;
    	token.src = src;
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
		prop->expr.token = d->prop.token;
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
	Grammar(Source*);
	void initNames();

	VarStack var_stack;
	qi::rule<Iterator, qi::unused_type> bar;
	qi::rule<Iterator, uint(), unicode::space_type> liter;
	qi::rule<Iterator, Symbol(), unicode::space_type> var;
	qi::rule<Iterator, Symbol(), unicode::space_type> symb;
	qi::rule<Iterator, uint(), unicode::space_type> id;
	qi::rule<Iterator, string(), unicode::space_type> path;
	qi::rule<Iterator, Expr(Rule*), unicode::space_type> term;
	qi::rule<Iterator, Expr(Type*), unicode::space_type> expr;
	qi::rule<Iterator, Expr(Type*), unicode::space_type> plain;
	qi::rule<Iterator, Disj(), unicode::space_type> disj;
	qi::rule<Iterator, Vars(), qi::locals<Symbol>, unicode::space_type> vars;
	qi::rule<Iterator, Hyp*(), qi::locals<uint>, unicode::space_type> hyp;
	qi::rule<Iterator, Prop*(), qi::locals<uint>, unicode::space_type> prop;
	qi::rule<Iterator, Ref(Proof*), unicode::space_type> ref;
	qi::rule<Iterator, vector<Ref>(Proof*), unicode::space_type> refs;
	qi::rule<Iterator, Step*(Proof*), qi::locals<uint, uint, Step::Kind, Assertion::Kind, uint, vector<Ref>>, unicode::space_type> step;
	qi::rule<Iterator, Qed*(Proof*), qi::locals<uint>, unicode::space_type> qed;
	qi::rule<Iterator, Proof::Elem(Proof*), unicode::space_type> proof_elem;
	qi::rule<Iterator, void(Proof*), unicode::space_type> proof_body;
	qi::rule<Iterator, Proof*(), qi::locals<uint>, unicode::space_type> proof;
	qi::rule<Iterator, Theorem*(), qi::locals<Assertion*>, unicode::space_type> theorem;
	qi::rule<Iterator, Def*(), qi::locals<Assertion*, Type*>, unicode::space_type> def;
	qi::rule<Iterator, Axiom*(), qi::locals<Assertion*>, unicode::space_type> axiom;
	qi::rule<Iterator, Rule*(), qi::locals<uint, Vars, uint>, unicode::space_type> rule;
	qi::rule<Iterator, Type*(), qi::locals<uint, vector<Type*>>, unicode::space_type> type;
	qi::rule<Iterator, Const*(), qi::locals<uint, uint, uint>, unicode::space_type> constant;
	qi::rule<Iterator, Import*(), unicode::space_type> import;
	qi::rule<Iterator, string(), qi::unused_type> comment_text;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment_ml;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment_sl;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment;
	qi::rule<Iterator, Source(), unicode::space_type> source;

	static bool parse(Iterator& beg, Iterator& end, auto space, Source& src) {
		return qi::phrase_parse(beg, end, Grammar(&src), space, src);
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
