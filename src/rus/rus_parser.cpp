#include <rus_ast.hpp>
#include "peglib.h"

namespace mdl { namespace rus {

struct Parser {
private:
	struct Stacks {
		vector<Vars>     vars;
		vector<Proof*>   proofs;
		map<uint, Type*> typing;
		void pushVars() {
			vars.push_back(Vars());
		}
		void popVars() {
			Vars& vs = vars.back();
			for (auto v : vs.v) typing.erase(v.lit);
			vs.pop_back();
		}
		void addVar(Symbol v) {
			vars.back().v.push_back(v);
			typing[v.lit] = v.type;
		}
		Type* type(uint v) const {
			if (!typing.count(v)) throw Error("unknown type", Lex::getStr(v));
			return typing.at(v);
		}
		void markType(Symbol& s) const {
			if (typing.count(s.lit)) s.type = typing.at(s.lit);
		}
	};
	struct Context {
		Context() : ind(0), stacks(), source(nullptr) { }
		uint    ind;
		Stacks  stacks;
		Id      type;
		Source* source;
		Token token(const peg::SemanticValues& sv) const {
			return Token(source, sv.c_str(), sv.c_str() + sv.length());
		}
	};
	peg::parser parser;

public:
	static const char* run_syntax() {
		return R"(
			# Russell grammar
		
            SOURCE   <- ELEMENT*
			ELEMENT  <- COMMENT / IMPORT / CONST / TYPE / RULE / AXIOM / DEF / THEOREM / PROOF
 
			IMPORT   <- 'import' PATH ';;'
			CONST    <- 'constant' '{' 'symbol' SYMB ';;' ('ascii' SYMB ';;')? ('latex' SYMB ';;')? '}'
			SUPERS   <- ':' ID_REF (',' ID_REF)*

			TYPE     <- 'type'       ID_NAME SUPERS ';;' 
			RULE     <- 'rule'       ID_NAME '(' VARS ')'      '{' TERM '}'
			AXIOM    <- 'axiom'      ID_NAME '(' VARS ')' DISJ '{' (HYP+ BAR)? PROP '}'
			THEOREM  <- 'theorem'    ID_NAME '(' VARS ')'      '{' (HYP+ BAR)? PROP '}'
			DEF      <- 'definition' ID_NAME '(' VARS ')' DISJ '{' HYP* DEF_M DEF_S BAR PROP '}'
			PROOF    <- 'proof'      ID_NAME? 'of' ID_REF '{' PROOF_BD '}'

			TERM_    <- 'term'      ':' ID_REF '=' '#'  EXPR ';;' 
			DEF_M    <- 'defiendum' ':' ID_REF '=' '#'  EXPR ';;' 
			DEF_S    <- 'definiens' ':' ID_REF '=' '#'  EXPR ';;' 
			HYP      <- 'hyp'  IND  ':' ID_REF '=' '|-' EXPR ';;' 
			PROP     <- 'prop' IND  ':' ID_REF '=' '|-' EXPR ';;' 

			PROOF_BD <- PROOF_EL+
			PROOF_EL <- VAR_DECL / STEP / QED
			DISJ     <- 'disjointed' '(' DISJ_SET (',' DISJ_SET)* ')'
			DISJ_SET <- ID_REF+

			STEP     <- 'step' IND ':' ID_REF '=' (APPLY | '?') '|-' EXPR ';;'
			APPLY    <- ID_REF ('(' REFS ')')?
			REFS     <- ID_REF (',' ID_REF)*
			QED      <- 'qed' 'prop' ID_REF '=' 'step' ID_REF ';;'

			VAR_DECL <- 'var' VARS ';;'
			VARS     <- (VAR (',' VAR)*)?
			VAR      <- SYMB : ID_REF
            BAR      <- '-----' '-'*

			EXPR <- (SYMB / COMMENT)+

			SYMB     <- < (![ \t\r\n$] .)+ >
			ID_REF   <- < (![,(=;:{ \t\r\n$] .)+ >
			ID_NAME  <- < (![,(=;:{ \t\r\n$] .)+ >
			PATH     <- < (![ \t\r\n$] .)+ >
			IND      <- < [0-9]+ >
			COMMENT    <- COMMENT_ML / COMMENT_SL 
			COMMENT_ML <- '/*' < (!'*/' .)* > '*/'
			COMMENT_SL <- '//' < (![\n$] .)+ >
		
			%whitespace <- [ \t\r\n]*
		)";
	}
	Parser(const Path& path) : parser(mm_syntax()) {

		parser["SYMB"] = [](const peg::SemanticValues& sv) {
			return Symbol(Lex::toInt(sv.token()));
		};
		parser["ID_NAME"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser["ID_REF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return Id(Lex::toInt(sv.token()), c->token(sv));
		};
		parser["IND"] = [](const peg::SemanticValues& sv) {
			return (uint)std::stoul(sv.token());
		};
		parser["PATH"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser["EXPR"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			vector<Symbol> vect(sv.size());
			for (auto& s : sv) {
				if (s.is<Symbol>()) vect.push_back(s);
				else delete s.get<Comment*>();
			}
			return vect;
		};
		parser["VARS"] = [](const peg::SemanticValues& sv) {
			return Vars(sv.transform<Symbol>());
		};
		// VAR_DECL <- 'var' VARS ';;'
		parser["VAR_DECL"] = [](const peg::SemanticValues& sv) {
			return new Vars(sv[0].get<Vars>());
		};
		parser["DISJ_SET"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* context = ctx.get<Context*>();
			Disj disj;
			disj.d.push_back(vector<Symbol>());
			vector<Symbol>& set = disj.d.back();
			for (auto& v : sv) {
				context->stacks.markType(v);
				set.push_back(v);
			}
			return disj;
		};
		parser["CONST"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Const* c = nullptr;
			switch (sv.size()) {
			case 1 : c = new Const(sv[0].get<Vect>()); break;
			case 2 : c = new Const(sv[0].get<Vect>(), sv[1].get<Vect>()); break;
			case 3 : c = new Const(sv[0].get<Vect>(), sv[1].get<Vect>(), sv[2].get<Vect>()); break;
			default : throw Error("syntax error");
			}
			return c;
		};
		parser["SUPERS"] = [](const peg::SemanticValues& sv) {
			return sv.transform<Id>();
		};
		parser["TYPE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return new Type(sv[0].get<uint>(), sv[1].get<vector<Id>>());
		};
		parser["TERM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return Expr(sv[0].get<Id>(), sv[1].get<vector<Symbol>>());
		};
		parser["RULE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint id     = sv[0].get<uint>();
			Vars vars = sv[1].get<Vars>();
			Expr term = sv[2].get<Expr>();
			Rule* r = new Rule(Id(id));
			r->vars = std::move(vars);
			r->term = std::move(term);
			return r;
		};
		parser["AXIOM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint id   = sv[0].get<uint>();
			Vars vars = sv[1].get<Vars>();
			Disj disj = sv[2].get<Disj>();
			vector<Hyp*>  hyps  = sv[3].get<vector<Hyp>>();
			vector<Prop*> props = sv[4].get<vector<Prop>>();
			Axiom* a = new Axiom(Id(id));
			a->vars  = std::move(vars);
			a->disj  = std::move(fisj);
			a->hyps  = std::move(hyps);
			a->props = std::move(props);
			return a;
		};
		parser["THEOREM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint id   = sv[0].get<uint>();
			Vars vars = sv[1].get<Vars>();
			vector<Hyp*>  hyps  = sv[2].get<vector<Hyp>>();
			vector<Prop*> props = sv[3].get<vector<Prop>>();
			Theorem* t = new Theorem(Id(id));
			t->vars  = std::move(vars);
			t->hyps  = std::move(hyps);
			t->props = std::move(props);
			return t;
		};
		parser["DEF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint id   = sv[0].get<uint>();
			Vars vars = sv[1].get<Vars>();
			Disj disj = sv[2].get<Disj>();
			vector<Hyp*> hyps  = sv[3].get<vector<Hyp>>();
			Expr defiendum = sv[4].get<Expr>();
			Expr definiens = sv[5].get<Expr>();
			Prop* Prop = sv[4].get<Expr>();
			Def* a = new Def(Id(id));
			a->vars  = std::move(vars);
			a->disj  = std::move(fisj);
			a->hyps  = std::move(hyps);
			//a->props = std::move(props);
			return a;
		};

		//	APPLY <- ID_REF ('(' REFS ')')?
		//	REFS  <- ID_REF (',' ID_REF)*
		//	QED <- 'qed' 'prop' ID_REF '=' 'step' ID_REF ';;'

		//  STEP  <- 'step' IND ':' ID_REF '=' (APPLY | '?') '|-' EXPR ';;'
		parser["STEP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			uint ind = sv[0].get<uint>();
			Id  type = sv[1].get<Id>();

		};

		// PROOF_EL <- VAR_DECL / STEP / QED
		parser["PROOF_EL"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Proof::Elem el;
			switch (sv.choice()) {
			case 0: el = Proof::Elem(sv[0].get<Vars*>()); break;
			case 1: el = Proof::Elem(sv[0].get<Step*>()); break;
			case 2: el = Proof::Elem(sv[0].get<Qed*>());  break;
			}
			return el;
		};
		parser["PROOF_BD"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv.transform<Proof::Elem>();
		};
		// PROOF <- 'proof' ID_NAME? 'of' ID_REF '{' PROOF_BD '}'
		parser["PROOF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint id   = sv[0].is_undefined() ? UNDEF : sv[0].get<uint>();
			Id   ref  = sv[1].get<Id>();
			vector<Proof::Elem> body = sv[2].get<vector<Proof::Elem>>();
			return a;
		};








		parser["ESS"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Essential* ess = new Essential { sv[0].get<uint>(), sv[1].get<Vect>() };
			markVars(ess->expr, context.get<std::shared_ptr<Context>>()->vars);
			System::mod().math.essentials[ess->label] = ess;
			return ess;
		};
		parser["FLO"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Floating* flo = new Floating { sv[0].get<uint>(), sv[1].get<Vect>() };
			markVars(flo->expr, context.get<std::shared_ptr<Context>>()->vars);
			System::mod().math.floatings[flo->label] = flo;
			return flo;
		};
		parser["AX"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Axiom* ax = new Axiom { sv[0].get<uint>(), sv[1].get<Vect>(), (uint) -1 };
			markVars(ax->expr, context.get<std::shared_ptr<Context>>()->vars);
			System::mod().math.axioms[ax->label] = ax;
			return ax;
		};
		parser["TH"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Theorem* th = new Theorem();
			th->label = sv[0].get<uint>();
			th->expr  = sv[1].get<Vect>();
			th->proof = sv[2].get<Proof*>();
			markVars(th->expr, context.get<std::shared_ptr<Context>>()->vars);
			System::mod().math.theorems[th->label] = th;
			return th;
		};
		parser["PROOF"] = [](const peg::SemanticValues& sv) {
			Proof* pr = new Proof();
			pr->refs = sv.transform<Ref*>();
			return pr;
		};
		parser["REF"] = [](const peg::SemanticValues& sv) {
			uint lab = sv[0].get<uint>();
			System::Math& math = System::mod().math;
			if (math.floatings.count(lab))
				return new Ref(math.floatings[lab]);
			else if (math.essentials.count(lab))
				return new Ref(math.essentials[lab]);
			else if (math.axioms.count(lab))
				return new Ref(math.axioms[lab]);
			else if (math.theorems.count(lab))
				return new Ref(math.theorems[lab]);
			else
				throw Error("unknown label in proof", Lex::toStr(lab));
		};
		parser["COMMENT"] = [](const peg::SemanticValues& sv) {
			string text = sv.token();
			return new Comment(text.front() == ' ' ? text : " " + text);
		};
		parser["ELEMENT"] = [&](const peg::SemanticValues& sv, peg::any& context) {
			// COMMENT / DISJ / ESS / TH / '${' BLOCK '$}'/ AX / CONST / VAR / FLO / INCLUDE
			Node node;
			switch (sv.choice()) {
			case 0: node = Node(sv[0].get<Comment*>());   break;
			case 1: node = Node(sv[0].get<Disjointed*>());break;
			case 2: node = Node(sv[0].get<Essential*>()); break;
			case 3: node = Node(sv[0].get<Theorem*>());   break;
			case 4: node = Node(sv[0].get<Block*>());     break;
			case 5: node = Node(sv[0].get<Axiom*>());     break;
			case 6: node = Node(sv[0].get<Constants*>()); break;
			case 7: node = Node(sv[0].get<Variables*>()); break;
			case 8: node = Node(sv[0].get<Floating*>());  break;
			case 9: node = Node(sv[0].get<Inclusion*>()); break;
			}
			context.get<std::shared_ptr<Context>>()->block->contents.push_back(node);
			return node;
		};
		parser["BLOCK"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Block* b = context.get<std::shared_ptr<Context>>()->block;
			b->contents = sv.transform<Node>();
			init_indexes(b->contents);
			return b;
		};
		parser["BLOCK"].enter = [](peg::any& c) {
			Context* context = c.get<std::shared_ptr<Context>>().get();
			context->block = new Block(context->block);
			if (!context->source) {
				context->vars.push_back(Scope());
			} else {
				context->src_blocks.insert(context->block);
			}
			context->source = false;
		};
		parser["BLOCK"].leave = [](peg::any& c) {
			Context* context = c.get<std::shared_ptr<Context>>().get();
			if (!context->src_blocks.count(context->block)) {
				context->vars.pop_back();
			} else {
				context->src_blocks.erase(context->block);
			}
			context->block = context->block->parent;
		};
		parser["SOURCE"] = [path](const peg::SemanticValues& sv, peg::any& context) {
			Source* src = new Source(Lex::toInt(path.name));
			src->block = sv[0].get<Block*>();
			return src;
		};
		parser["SOURCE"].enter = [](peg::any& context) {
			context.get<std::shared_ptr<Context>>()->source = true;
		};
		parser["INCLUDE"] = [path](const peg::SemanticValues& sv, peg::any& context) {
			string name = sv.token();
			static map<string, mm::Inclusion*> included;
			if (included.count(name)) {
				mm::Inclusion* inc = included[name];
				return new mm::Inclusion(inc->source, false);
			} else {
				Path new_path(path);
				new_path.name_ext(name);
				mm::Inclusion* inc = new mm::Inclusion(nullptr, true);
				included[name] = inc;
				inc->source = parse(new_path, context.get<std::shared_ptr<Context>>());
				return inc;
			}
		};
	}

	static Source* parse(uint label) {
		Path path;
		string data;
		path.read(data);
		Parser p(path);
		mdl::mm::Source* src = nullptr;
		peg::any ctx(new Context());
		p.parser.parse<mdl::mm::Source*>(data.c_str(), ctx, src);
		delete ctx.get<Context*>();
		std::swap(data, src->data);
		return src;
	}

private:
	static void mark_vars(Expr* ex, Stacks& stacks) {
		for (auto& s : ex->symbols) {
			bool is_var = stacks.typing.count(s.lit);
			bool is_const = System::get().math.consts.count(s.lit);
			if (is_const && is_var)
				throw Error("constant symbol is marked as variable");
			if (!is_const && !is_var) {
				string msg = "symbol " + Lex::toStr(s.lit) + " ";
				msg += " neither constant nor variable";
				throw Error(msg);
			}
			if (is_var) s.type = stacks.typing[s.lit];
		}
	}
	static Rule* create_super(Type* inf, Type* sup) {
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
	static void collect_supers(Type* inf, Type* s) {
		for (auto sup : s->sup) {
			Rule* super = create_super(inf, sup);
			inf->supers[sup] = super;
			collect_supers(inf, sup);
		}
	}

};

Source* parse(uint label) {
	return Parser::parse(label);
}

}} // mdl::mm
