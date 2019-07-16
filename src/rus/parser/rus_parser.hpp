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
	struct result { typedef void type; };
	void operator()(VarStack& var_stack, Vars& vars) const {
		for (auto& v : vars.v) {
			var_stack.vstack.top().push_back(v.lit());
			var_stack.mapping[v.lit()] = v.typeId();
		}
	}
	void operator()(VarStack& var_stack, const Assertion* thm) const {
		for (auto& v : thm->vars.v) {
			var_stack.vstack.top().push_back(v.lit());
			var_stack.mapping[v.lit()] = v.typeId();
		}
	}
};

struct AddVar {
	struct result { typedef void type; };
	void operator()(vector<Var>& vars, uint var, Id type) const {
		vars.emplace_back(var, type.id());
	}
};

struct PopVars {
	struct result { typedef void type; };
	void operator()(VarStack& var_stack) const {
		vector<uint>& vars = var_stack.vstack.top();
		for (uint v : vars) {
			var_stack.mapping.erase(v);
		}
		var_stack.vstack.pop();
	}
};

static void mark_vars(Expr& ex, VarStack& var_stack) {
	for (auto& s : ex.symbols) {
		auto i = var_stack.mapping.find(s->lit());
		if (i != var_stack.mapping.end()) {
			s.reset(new Var(s->lit(), i->second, Token()));
		} else {
			s.reset(new Const(s->lit(), Token()));
		}
	}
}

struct Enqueue {
	void operator()(Assertion* ass) const {
		for (auto& h : ass->hyps) {
			expr::enqueue(h.get()->expr);
		}
		expr::enqueue(ass->prop->expr);
	}
	void operator()(Def* def) const {
		expr::enqueue(def->dfm);
		expr::enqueue(def->dfs);
		operator()(static_cast<Assertion*>(def));
	}
	void operator()(Proof* proof) const {
		for (auto& s : proof->steps) {
			expr::enqueue(s->expr);
			if (s->kind() == Step::CLAIM) {
				operator()(s->proof());
			}
		}
	}
};

struct SymbToInt {
	struct result { typedef uint type; };
	uint operator()(const std::vector<uint>& s) const {
		string symb(s.begin(), s.end());
		return Lex::toInt(symb);
	}
};

struct IdToInt {
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
			ex.symbols.push_back(make_unique<Literal>(s));
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
		create_rule_term(ex, id);
	}
};

struct ParseImport {
	struct result { typedef Import* type; };
	Import* operator()(string name, Source* src) const {
		uint id = Sys::make_name(name);
		return new Import(id, Token(src));
	}
};

struct SetType {
	struct result { typedef void type; };
	void operator()(unique_ptr<Symbol>& s, Id t) const {
		s.reset(new Var(s->lit(), t.id(), Token()));
	}
};

struct AddDisjVar {
	struct result { typedef void type; };
	void operator()(Disj& disj, set<uint>& dis, uint v) const {
		for (uint w : dis) {
			disj.dvars.emplace(v, w);
		}
		dis.insert(v);
	}
};

struct NewDisjSet {
	struct result { typedef void type; };
	void operator()(set<uint>& dis) const {
		dis.clear();
	}
};

struct CreateStepRef {
	struct result { typedef void Ref; };
	Ref* operator()(uint ind, Proof* p, Ref::Kind k) const {
		switch (k) {
		case Ref::HYP:  return new Ref(p->theorem->hyps[ind].get());
		case Ref::STEP: return new Ref(p->steps[ind].get());
		default : assert(false && "impossible"); break;
		}
		return nullptr;
	}
};

struct GetProp {
	struct result { typedef Prop* type; };
	Prop* operator()(Proof* p) const {
		return p->theorem->prop.get();
	}
};

struct GetStep {
	struct result { typedef Step* type; };
	Step* operator()(uint ind, Proof* p) const {
		return p->steps[ind].get();
	}
};

struct SetToken {
    struct result { typedef void type; };
    void operator()(WithToken& with_token, LocationIter beg, LocationIter end, Source* src) const {
    	with_token.token.set(src, &*beg, &*end);
    }
};

static Literal dfm(Lex::toInt("defiendum"));
static Literal dfs(Lex::toInt("definiens"));

struct AssembleDef {
	struct result { typedef void type; };
	void operator()(Def* d, VarStack& varsStack) const {
		d->prop = make_unique<Prop>();
		for (auto& s : d->def.symbols) {
			if (*s == dfm) {
				for (auto& s_dfm : d->dfm.symbols) {
					d->prop->expr.symbols.emplace_back(s_dfm->clone());
				}
			} else if (*s == dfs) {
				for (auto& s_dfs : d->dfs.symbols) {
					d->prop->expr.symbols.emplace_back(s_dfs->clone());
				}
			} else {
				d->prop->expr.symbols.emplace_back(s->clone());
			}
		}
		d->prop->expr.type = d->def.type;
		d->prop->expr.token = d->def.token;
		mark_vars(d->prop->expr, varsStack);
	}
};

struct AppendComment {
	struct result { typedef void type; };
	void operator()(Comment* c1, Comment* c2) const {
		c1->text += c2->show();
		delete c2;
	}
	void operator()(Comment* c1, const string& c2) const {
		c1->text += c2;
	}
};

struct AddProofStep {
	struct result { typedef void type; };
	void operator()(Proof* p, Step* s) const {
		p->steps.emplace_back(unique_ptr<Step>(s));
	}
};

struct AddProofQed {
	struct result { typedef void type; };
	void operator()(Proof* p, Qed* q) const {
		p->qed.reset(q);
	}
};

struct AddStepRefs {
	struct result { typedef void type; };
	void operator()(Step* s, vector<Ref*> rs) const {
		s->refs.reserve(rs.size());
		for (Ref* r : rs) {
			s->refs.emplace_back(r);
		}
	}
};

struct AddToAssertion {
	struct result { typedef void type; };
	void operator()(Assertion* a, Hyp* h) const {
		a->hyps.emplace_back(h);
	}
	void operator()(Assertion* a, Prop* p) const {
		a->prop.reset(p);
	}
	void operator()(Theorem* t, Proof* p) const {
		t->proof.reset(p);
	}
};

struct AddToTheory {
	struct result { typedef void type; };
	void operator()(Theory* t, Constant* c) const {
		t->nodes.emplace_back(unique_ptr<Constant>(c));
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

struct Grammar : qi::grammar<LocationIter, rus::Source*(), unicode::space_type> {
	Grammar(Source*);
	void initNames();

	VarStack var_stack;
	qi::rule<LocationIter, qi::unused_type> bar;
	qi::rule<LocationIter, uint(), unicode::space_type> liter;
	qi::rule<LocationIter, uint(), unicode::space_type> var;
	qi::rule<LocationIter, uint(), unicode::space_type> symb;
	qi::rule<LocationIter, Id(), unicode::space_type> id;
	qi::rule<LocationIter, string(), unicode::space_type> path;
	qi::rule<LocationIter, Expr*(Id, Id, Expr&), qi::locals<vector<uint>>, unicode::space_type> term;
	qi::rule<LocationIter, Expr*(Id, Expr&), qi::locals<vector<uint>>, unicode::space_type> expr;
	qi::rule<LocationIter, Expr*(Id, Expr&), qi::locals<vector<uint>>, unicode::space_type> plain;
	qi::rule<LocationIter, Disj*(Disj&), qi::locals<set<uint>>, unicode::space_type> disj;
	qi::rule<LocationIter, Vars*(Vars&), qi::locals<uint, Id>, unicode::space_type> vars;
	qi::rule<LocationIter, Hyp*(), qi::locals<Id>, unicode::space_type> hyp;
	qi::rule<LocationIter, Prop*(), qi::locals<Id>, unicode::space_type> prop;
	qi::rule<LocationIter, Ref*(Proof*), unicode::space_type> ref;
	qi::rule<LocationIter, vector<Ref*>(Proof*), unicode::space_type> refs;
	qi::rule<LocationIter, Step*(Proof*), qi::locals<uint, Id, Step::Kind, Id, vector<Ref*>>, unicode::space_type> step;
	qi::rule<LocationIter, Qed*(Proof*), unicode::space_type> qed;
	qi::rule<LocationIter, void(Proof*), unicode::space_type> proof_body;
	qi::rule<LocationIter, Proof*(Theorem*), unicode::space_type> proof;
	qi::rule<LocationIter, Theorem*(), unicode::space_type> theorem;
	qi::rule<LocationIter, Def*(), qi::locals<Id>, unicode::space_type> def;
	qi::rule<LocationIter, Axiom*(), unicode::space_type> axiom;
	qi::rule<LocationIter, Rule*(), qi::locals<Id, Id>, unicode::space_type> rule;
	qi::rule<LocationIter, Type*(), qi::locals<Id, vector<Id>>, unicode::space_type> type;
	qi::rule<LocationIter, Constant*(), qi::locals<uint, uint, uint>, unicode::space_type> constant;
	qi::rule<LocationIter, Import*(), unicode::space_type> import;
	qi::rule<LocationIter, string(), qi::unused_type> comment_text;
	qi::rule<LocationIter, Comment*(), qi::unused_type> comment_ml;
	qi::rule<LocationIter, Comment*(), qi::unused_type> comment_sl;
	qi::rule<LocationIter, Comment*(), qi::unused_type> comment;
	qi::rule<LocationIter, Source*(), unicode::space_type> source;
};

inline void Grammar::initNames() {
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
