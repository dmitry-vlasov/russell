#define PARALLEL_PARSE

#include <rus_ast.hpp>
#include "boost.hpp"
#include "rus_parser_adaptors.hpp"

namespace mdl { namespace rus {

void parse_src_spirit(uint);

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
	map<uint, uint> mapping;
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
			var_stack.mapping[v.lit] = v.type_id();
		}
	}
	void operator()(VarStack& var_stack, User<Assertion>& thm) const {
		for (auto& v : thm.get()->vars.v) {
			var_stack.vstack.top().push_back(v.lit);
			var_stack.mapping[v.lit] = v.type_id();
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
		if (is_var) s.set_type(var_stack.mapping[s.lit]);
		else s.set_const();
	}
}

struct Enqueue {
	void operator()(Assertion* ass) const {
		for (auto& h : ass->hyps) {
			expr::enqueue(h.get()->expr);
		}
		for (auto& p : ass->props) {
			expr::enqueue(p.get()->expr);
		}
	}
	void operator()(Def* def) const {
		expr::enqueue(def->dfm);
		expr::enqueue(def->dfs);
		operator()(static_cast<Assertion*>(def));
	}
	void operator()(Proof* proof) const {
		for (auto& e : proof->elems) {
			if (Proof::kind(e) == Proof::STEP) {
				Step* step = Proof::step(e);
				expr::enqueue(step->expr);
				if (step->kind() == Step::CLAIM)
					operator()(step->proof());
			}
		}
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
	struct result { typedef Id type; };
	Id operator()(const std::vector<uint>& id) const {
		string id_str(id.begin(), id.end());
		return Lex::toInt(id_str);
	}
};

struct ParsePlain {
	struct result { typedef void type; };
	void operator()(Expr& ex, const vector<uint>& symbs, Id tp) const {
		ex.symbols.reserve(symbs.size());
		for (uint s : symbs) {
			ex.symbols.emplace_back(s);
		}
		ex.type.set(tp);
	}
};

struct ParseExpr {
	struct result { typedef void type; };
	void operator()(Expr& ex, const vector<uint>& symbs, Id tp, VarStack& var_stack) const {
		static ParsePlain plain;
		plain(ex, symbs, tp);
		mark_vars(ex, var_stack);
	}
};

struct ParseTerm {
	struct result { typedef void type; };
	void operator()(Expr& ex, const vector<uint>& symbs, Id id, Id tp, VarStack& var_stack) const {
		static ParseExpr expr;
		expr(ex, symbs, tp, var_stack);
		Tree::Children children;
		for (auto& s : ex.symbols) {
			if (s.var) children.push_back(make_unique<Tree>(s));
		}
		ex.set(new Tree(id, children));
	}
};

struct ParseImport {
	template <typename T1, typename T2>
	struct result { typedef Import* type; };
	Import* operator()(string name, Source* src) const {
		uint id = Sys::make_name(name);
#ifndef PARALLEL_PARSE
		Source* imp_src = Sys::mod().math.get<Source>().access(id);
		if (!imp_src->parsed) parse_src_spirit(id);
#endif
		return new Import(id);
	}
};

struct SetType {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Symbol& s, Id t) const {
		s.set_type(t);
	}
};

struct AddDisjVar {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(vector<vector<Symbol>>& disj, uint v) const {
		disj.back().emplace_back(v);
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
	Ref* operator()(uint ind, Proof* p, Ref::Kind k) const {
		switch (k) {
		case Ref::HYP:  return new Ref(p->thm.get()->hyps[ind].get());
		case Ref::PROP: return new Ref(p->thm.get()->props[ind].get());
		case Ref::STEP: return new Ref(Proof::step(p->elems[ind]));
		default : assert(false && "impossible"); break;
		}
		return nullptr;
	}
};

struct GetProp {
	template <typename T1, typename T2>
	struct result { typedef Prop* type; };
	Prop* operator()(uint ind, Proof* p) const {
		return p->thm.get()->props[ind].get();
	}
};

struct GetStep {
	template <typename T1, typename T2>
	struct result { typedef Step* type; };
	Step* operator()(uint ind, Proof* p) const {
		return Proof::step(p->elems[ind]);
	}
};


template<typename Iterator>
struct SetToken {
    template <typename T1, typename T2, typename T3, typename T4>
    struct result { typedef void type; };
    void operator()(Tokenable& tokenable, Iterator beg, Iterator end, Source* src) const {
    	tokenable.token.set(src, &*beg, &*end);
    }
};

static Symbol dfm(Lex::toInt("defiendum"));
static Symbol dfs(Lex::toInt("definiens"));

struct AssembleDef {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Def* d, VarStack& varsStack) const {
		Prop* prop = new Prop(0);
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
		prop->expr.type = d->prop.type;
		prop->expr.token = d->prop.token;
		mark_vars(prop->expr, varsStack);
		d->props.emplace_back(prop);
	}
};

struct AppendComment {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Comment* c1, Comment* c2) const {
		c1->text += show(*c2);
		delete c2;
	}
	void operator()(Comment* c1, const string& c2) const {
		c1->text += c2;
	}
};

struct AddProofElem {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Proof* p, Step* s) const {
		p->elems.emplace_back(unique_ptr<Step>(s));
	}
	void operator()(Proof* p, Qed* q) const {
		p->elems.emplace_back(unique_ptr<Qed>(q));
	}
};

struct AddStepRefs {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Step* s, vector<Ref*> rs) const {
		s->refs.reserve(rs.size());
		for (Ref* r : rs) {
			s->refs.emplace_back(r);
		}
	}
};

struct AddToAssertion {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Assertion* a, Hyp* h) const {
		a->hyps.emplace_back(h);
	}
	void operator()(Assertion* a, Prop* p) const {
		a->props.emplace_back(p);
	}
};

struct AddToTheory {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Theory* t, Const* c) const {
		t->nodes.emplace_back(unique_ptr<Const>(c));
	}
	void operator()(Theory* t, Type* tp) const {
		t->nodes.emplace_back(unique_ptr<Type>(tp));
	}
	void operator()(Theory* t, Rule* r) const {
		t->nodes.emplace_back(unique_ptr<Rule>(r));
	}
	void operator()(Theory* t, Axiom* a) const {
		t->nodes.emplace_back(unique_ptr<Axiom>(a));
	}
	void operator()(Theory* t, Def* d) const {
		t->nodes.emplace_back(unique_ptr<Def>(d));
	}
	void operator()(Theory* t, Theorem* th) const {
		t->nodes.emplace_back(unique_ptr<Theorem>(th));
	}
	void operator()(Theory* t, Proof* p) const {
		t->nodes.emplace_back(unique_ptr<Proof>(p));
	}
	void operator()(Theory* t, Theory* th) const {
		t->nodes.emplace_back(unique_ptr<Theory>(th));
	}
	void operator()(Theory* t, Import* i) const {
		t->nodes.emplace_back(unique_ptr<Import>(i));
	}
	void operator()(Theory* t, Comment* c) const {
		t->nodes.emplace_back(unique_ptr<Comment>(c));
	}
};

template <typename Iterator>
struct Grammar : qi::grammar<Iterator, rus::Source*(), unicode::space_type> {
	Grammar(Source*);
	void initNames();

	VarStack var_stack;
	qi::rule<Iterator, qi::unused_type> bar;
	qi::rule<Iterator, uint(), unicode::space_type> liter;
	qi::rule<Iterator, uint(), unicode::space_type> var;
	qi::rule<Iterator, uint(), unicode::space_type> symb;
	qi::rule<Iterator, Id(), unicode::space_type> id;
	qi::rule<Iterator, string(), unicode::space_type> path;
	qi::rule<Iterator, Expr*(Id, Id, Expr&), qi::locals<vector<uint>>, unicode::space_type> term;
	qi::rule<Iterator, Expr*(Id, Expr&), qi::locals<vector<uint>>, unicode::space_type> expr;
	qi::rule<Iterator, Expr*(Id, Expr&), qi::locals<vector<uint>>, unicode::space_type> plain;
	qi::rule<Iterator, Disj(), unicode::space_type> disj;
	qi::rule<Iterator, Vars(), qi::locals<Symbol>, unicode::space_type> vars;
	qi::rule<Iterator, Hyp*(), qi::locals<Id>, unicode::space_type> hyp;
	qi::rule<Iterator, Prop*(), qi::locals<Id>, unicode::space_type> prop;
	qi::rule<Iterator, Ref*(Proof*), unicode::space_type> ref;
	qi::rule<Iterator, vector<Ref*>(Proof*), unicode::space_type> refs;
	qi::rule<Iterator, Step*(Proof*), qi::locals<uint, Id, Step::Kind, Id, vector<Ref*>>, unicode::space_type> step;
	qi::rule<Iterator, Qed*(Proof*), qi::locals<uint>, unicode::space_type> qed;
	qi::rule<Iterator, void(Proof*), unicode::space_type> proof_elem;
	qi::rule<Iterator, void(Proof*), unicode::space_type> proof_body;
	qi::rule<Iterator, Proof*(), qi::locals<Id>, unicode::space_type> proof;
	qi::rule<Iterator, Theorem*(), unicode::space_type> theorem;
	qi::rule<Iterator, Def*(), qi::locals<Id>, unicode::space_type> def;
	qi::rule<Iterator, Axiom*(), unicode::space_type> axiom;
	qi::rule<Iterator, Rule*(), qi::locals<Id, Vars, Id>, unicode::space_type> rule;
	qi::rule<Iterator, Type*(), qi::locals<Id, vector<Id>>, unicode::space_type> type;
	qi::rule<Iterator, Const*(), qi::locals<uint, uint, uint>, unicode::space_type> constant;
	qi::rule<Iterator, Import*(), unicode::space_type> import;
	qi::rule<Iterator, string(), qi::unused_type> comment_text;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment_ml;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment_sl;
	qi::rule<Iterator, Comment*(), qi::unused_type> comment;
	qi::rule<Iterator, Source*(), unicode::space_type> source;
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
