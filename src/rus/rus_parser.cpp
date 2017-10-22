#include <rus_ast.hpp>
#include "peglib.h"

namespace mdl { namespace rus {

struct Parser {
private:
	struct Stacks {
		void pushVars() {
			vars.push_back(Vars());
		}
		void popVars() {
			Vars& vs = vars.back();
			for (auto v : vs.v) typing.erase(v.lit);
			vars.pop_back();
		}
		void addVar(Symbol v) {
			vars.back().v.push_back(v);
			typing[v.lit] = v.type();
		}
		Type* type(uint v) const {
			if (!typing.count(v)) throw Error("unknown type", Lex::toStr(v));
			return typing.at(v);
		}
		void markType(Symbol& s) const {
			if (typing.count(s.lit)) s.set_type(typing.at(s.lit));
			else s.set_const(Sys::mod().math.get<Const>().access(s.lit));
		}
		Symbol makeSymb(uint lit, bool strict, const Token& token) const {
			Symbol s(lit);
			if (typing.count(lit)) {
				s.set_type(typing.at(s.lit));
			} else if (Sys::mod().math.get<Const>().access(s.lit)) {
				s.set_const(Sys::mod().math.get<Const>().access(s.lit));
			} else if (strict) {
				throw Error("symbol is not a constant nor variable", Lex::toStr(lit));
			}
			return s;
		}
		void pushProof(Proof* p) {
			proofs.push_back(p);
		}
		Proof* popProof() {
			Proof* p = proofs.back();
			proofs.pop_back();
			return p;
		}
		Proof* proof() {
			return proofs.back();
		}

	private:
		vector<Vars>     vars;
		vector<Proof*>   proofs;
		map<uint, Type*> typing;
	};
	struct Context {
		Context() : ind(0), stacks(), theory(nullptr), source(nullptr) { }
		uint    ind;
		Stacks  stacks;
		Id      type;
		Theory* theory;
		Source* source;
		Token token(const peg::SemanticValues& sv) const {
			return Token(source, sv.c_str(), sv.c_str() + sv.length());
		}
	};
	static peg::parser& parser() { static peg::parser p(rus_syntax()); return p; }

public:
	static const char* rus_syntax() {
		return R"(
			# Russell grammar
		
            SOURCE   <- ELEMENT*
            THEORY   <- TH_DECL '{' ELEMENT* '}'
            TH_DECL  <- 'theory' ID_NAME 
			ELEMENT  <- COMMENT / IMPORT / CONST / TYPE / RULE / AXIOM / DEF / THEOREM / PROOF / THEORY
 
			IMPORT   <- 'import' PATH ';;'
			CONST    <- 'constant' '{' 'symbol' ID_NAME ';;' ('ascii' ID_NAME ';;' ('latex' ID_NAME ';;')?)? '}'
			SUPERS   <- ':' ID_REF (',' ID_REF)*

			TYPE     <- 'type'       ID_NAME SUPERS ';;' 
			RULE     <- 'rule'       ID_NAME '(' VARS ')'      '{' 'term' TERM '}'
			AXIOM    <- 'axiom'      ID_NAME '(' VARS ')' DISJ '{' (HYP+ BAR)? PROP '}'
			THEOREM  <- 'theorem'    ID_NAME '(' VARS ')'      '{' (HYP+ BAR)? PROP '}'
			DEF      <- 'definition' ID_NAME '(' VARS ')' DISJ '{'  HYP* DEF_M DEF_S BAR DEF_P '}'

			PROOF    <- PROOF_DECL '{' PROOF_BODY '}'
			PROOF_DECL <- 'proof' ID_NAME? 'of' ID_REF '{' PROOF_BODY '}'
			PROOF_BODY <- PROOF_ELEM+
			PROOF_ELEM <- VAR_DECL / STEP / QED

            TERM     <- 'term'      EX_TERM
			DEF_M    <- 'defiendum' EX_TERM 
			DEF_S    <- 'definiens' EX_TERM
            DEF_P    <- 'prop'      EX_PLAIN 
			HYP      <- 'hyp'  IND  EX_STAT
			PROP     <- 'prop' IND  EX_STAT 

            EX_TERM  <- ':' ID_REF '=' '#'  SYMBS_TYPED ';;'
            EX_STAT  <- ':' ID_REF '=' '|-' SYMBS_TYPED ';;'
            EX_PLAIN <- ':' ID_REF '=' '|-' SYMBS_PLAIN ';;' 

			DISJ       <- 'disjointed' '(' DISJ_SET (',' DISJ_SET)* ')'
			DISJ_SET   <- ID_REF+

			STEP       <- STEP_ASS / STEP_QST / STEP_CLAIM
			STEP_ASS   <- 'step' IND ':' ID_REF '=' ID_REF  '(' REFS ')' '|-' EX_STAT ';;'
			# CLAIM_DECL <- 'step' IND ':' ID_REF '=' 'claim' '(' REFS ')' '|-' EX_STAT ';;'
			# STEP_CLM   <- CLAIM_DECL '{' PROOF_BODY '}'
			STEP_QST   <- 'step' IND ':' ID_REF '=' ? '|-' EX_STAT ';;'
			REFS       <- (REF (',' REF)*)?
			REF        <- REF_HYP / REF_PROP / REF_STEP
			REF_HYP    <- 'hyp' IND
			REF_PROP   <- 'prop' IND
			REF_STEP   <- 'step' IND
			QED        <- 'qed' 'prop' IND '=' 'step' IND ';;'

			VAR_DECL   <- 'var' VARS ';;'
			VARS       <- (VAR (',' VAR)*)?
			VAR        <- SYMB : ID_REF
            BAR        <- '-----' '-'*

			SYMBS_TYPED <- (SYMB_TYPED / COMMENT)+
            SYMBS_PLAIN <- (SYMB_PLAIN / COMMENT)+

			SYMB_TYPED <- < (![ \t\r\n$] .)+ >
            SYMB_PLAIN <- < (![ \t\r\n$] .)+ >
			ID_REF     <- < (![,(=;:{ \t\r\n$] .)+ >
			ID_NAME    <- < (![,(=;:{ \t\r\n$] .)+ >
			PATH       <- < (![ \t\r\n$] .)+ >
			IND        <- < [0-9]+ >
			COMMENT    <- COMMENT_ML / COMMENT_SL 
			COMMENT_ML <- '/*' < (!'*/' .)* > '*/'
			COMMENT_SL <- '//' < (![\n$] .)+ >
		
			%whitespace <- [ \t\r\n]*
		)";
	}
	Parser(uint src) {

		parser()["SYMB_TYPED"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return c->stacks.makeSymb(Lex::toInt(sv.token()), true, c->token(sv));
		};
		parser()["SYMB_PLAIN"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return c->stacks.makeSymb(Lex::toInt(sv.token()), false, c->token(sv));
		};
		parser()["ID_NAME"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser()["ID_REF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return Id(Lex::toInt(sv.token()), c->token(sv));
		};
		parser()["IND"] = [](const peg::SemanticValues& sv) {
			return (uint)std::stoul(sv.token());
		};
		parser()["PATH"] = [](const peg::SemanticValues& sv) {
			return Sys::make_name(sv.token());
		};
		parser()["SYMBS_TYPED"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			vector<Symbol> vect(sv.size());
			for (auto& s : sv) {
				if (s.is<Symbol>()) vect.emplace_back(s.get<Symbol>());
				else delete s.get<Comment*>();
			}
			return vect;
		};
		parser()["SYMBS_PLAIN"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			vector<Symbol> vect(sv.size());
			for (auto& s : sv) {
				if (s.is<Symbol>()) vect.emplace_back(s.get<Symbol>());
				else delete s.get<Comment*>();
			}
			return vect;
		};
		parser()["EX_TERM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return Expr(sv[0].get<Id>(), std::move(sv[1].get<vector<Symbol>&>()));
		};
		parser()["EX_STAT"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Expr e(sv[0].get<Id>(), std::move(sv[1].get<vector<Symbol>&>()));
			e.parse();
			return e;
		};
		parser()["EX_PLAIN"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Expr e(sv[0].get<Id>(), std::move(sv[1].get<vector<Symbol>&>()));
			return e;
		};
		parser()["VARS"] = [](const peg::SemanticValues& sv) {
			return Vars(sv.transform<Symbol>());
		};
		parser()["VAR_DECL"] = [](const peg::SemanticValues& sv) {
			return new Vars(sv[0].get<Vars>());
		};
		parser()["DISJ_SET"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* context = ctx.get<Context*>();
			Disj disj;
			disj.d.push_back(vector<Symbol>());
			vector<Symbol>& set = disj.d.back();
			for (auto& v : sv) {
				Symbol s = v.get<Symbol>();
				context->stacks.markType(s);
				set.emplace_back(s);
			}
			return disj;
		};
		parser()["CONST"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Const* c = nullptr;
			switch (sv.size()) {
			case 1 : c = new Const(sv[0].get<uint>(), -1, -1); break;
			case 2 : c = new Const(sv[0].get<uint>(), sv[1].get<uint>(), -1); break;
			case 3 : c = new Const(sv[0].get<uint>(), sv[1].get<uint>(), sv[2].get<uint>()); break;
			default : throw Error("syntax error");
			}
			return c;
		};
		parser()["SUPERS"] = [](const peg::SemanticValues& sv) {
			return sv.transform<Id>();
		};
		parser()["TYPE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return new Type(sv[0].get<uint>(), std::move(sv[1].get<vector<Id>>()), c->token(sv));
		};
		parser()["RULE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return new Rule(
				Id(sv[0].get<uint>()),
				std::move(sv[1].get<Vars>()),
				std::move(sv[2].get<Expr>()),
				c->token(sv)
			);
		};
		parser()["AXIOM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Axiom* a = new Axiom(Id(sv[0].get<uint>()), c->token(sv));
			a->vars  = std::move(sv[1].get<Vars&>());
			a->disj  = std::move(sv[2].get<Disj&>());
			a->hyps  = std::move(sv[3].get<vector<Hyp*>&>());
			a->props = std::move(sv[4].get<vector<Prop*>&>());
			return a;
		};
		parser()["THEOREM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Theorem* t = new Theorem(Id(sv[0].get<uint>()), c->token(sv));
			t->vars  = std::move(sv[1].get<Vars&>());
			t->hyps  = std::move(sv[2].get<vector<Hyp*>&>());
			t->props = std::move(sv[3].get<vector<Prop*>&>());
			return t;
		};
		parser()["DEF_M"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return Expr(sv[0].get<Id>(), std::move(sv[1].get<vector<Symbol>&>()), c->token(sv));
		};
		parser()["DEF_S"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return Expr(sv[0].get<Id>(), std::move(sv[1].get<vector<Symbol>&>()), c->token(sv));
		};
		parser()["DEF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Def* a = new Def(Id(sv[0].get<uint>()), c->token(sv));
			a->vars = std::move(sv[1].get<Vars&>());
			a->disj = std::move(sv[2].get<Disj&>());
			a->hyps = std::move(sv[3].get<vector<Hyp*>&>());
			a->dfm  = std::move(sv[4].get<Expr&>());
			a->dfs  = std::move(sv[5].get<Expr&>());
			a->prop = std::move(sv[6].get<Expr&>());
			return a;
		};

		// STEP <- STEP_ASS / STEP_CLAIM / STEP_QST
		parser()["STEP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv[0].get<Step*>();
		};
		// STEP_ASS <- 'step' IND ':' ID_REF '=' ID_REF  '(' REFS ')' '|-' EXPR ';;'
		parser()["STEP_ASS"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Id  type = sv[1].get<Id>();
			Id  ass  = sv[2].get<uint>();
			vector<Ref*> refs = sv[3].get<vector<Ref*>>();
			Expr expr = sv[4].get<Expr>();
			return new Step(ind, Step::ASS, ass, c->stacks.proof(), c->token(sv));
		};
		// STEP_CLM <- 'step' IND ':' ID_REF '=' 'claim' '(' REFS ')' '|-' EXPR ';;' '{' PROOF_BODY '}'
		/*parser()["STEP_CLM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Id  type = sv[1].get<Id>();
			Id  ass  = sv[2].get<uint>();
			vector<Ref*> refs = sv[3].get<vector<Ref*>>();
			Expr expr = sv[4].get<Expr>();
			return new Step(ind, Step::ASS, ass, c->stacks.proof(), c->token(sv));
		}*/
		// STEP_QST <- 'step' IND ':' ID_REF '=' ? '|-' EXPR ';;'
		parser()["STEP_QST"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Id  type = sv[1].get<Id>();
			Expr expr = sv[4].get<Expr>();
			return new Step(ind, Step::NONE, Id(), c->stacks.proof(), c->token(sv));
		};
		// REF_HYP <- 'hyp' IND
		parser()["REF_HYP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Proof* p = c->stacks.proof();
			return new Ref(p->theorem()->hyps[ind - 1]);
		};
		// REF_PROP <- 'prop' IND
		parser()["REF_PROP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Proof* p = c->stacks.proof();
			return new Ref(p->theorem()->props[ind - 1]);
		};
		// REF_STEP <- 'step' IND
		parser()["REF_STEP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Proof* p = c->stacks.proof();
			return new Ref(p->elems[ind - 1].val.step);
		};
		// REF <- REF_HYP / REF_PROP / REF_STEP
		parser()["REF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv[0].get<Ref*>();
		};
		// REFS <- (ID_REF (',' ID_REF)*)?
		parser()["REFS"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv.transform<Ref*>();
		};
		// QED <- 'qed' 'prop' ID_REF '=' 'step' ID_REF ';;'
		parser()["QED"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint prop = sv[0].get<uint>();
			uint step = sv[1].get<uint>();
			Proof* p = c->stacks.proof();
			return new Qed(p->theorem()->props[prop - 1], p->elems[step - 1].val.step);
		};

		// PROOF_EL <- VAR_DECL / STEP / QED
		parser()["PROOF_EL"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Proof::Elem el;
			switch (sv.choice()) {
			case 0: el = Proof::Elem(sv[0].get<Vars*>()); break;
			case 1: el = Proof::Elem(sv[0].get<Step*>()); break;
			case 2: el = Proof::Elem(sv[0].get<Qed*>());  break;
			}
			return el;
		};
		// PROOF_BODY <- PROOF_ELEM+
		parser()["PROOF_BD"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv.transform<Proof::Elem>();
		};
		// PROOF_DECL <- 'proof' ID_NAME? 'of' ID_REF
		parser()["PROOF_DECL"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint id   = sv[0].is_undefined() ? -1 : sv[0].get<uint>();
			Id   ref  = sv[1].get<Id>();
			Proof* proof = new Proof(ref, id, c->token(sv));
			proof->elems = std::move(sv[2].get<vector<Proof::Elem>&>());
			return proof;
		};
		// PROOF <- PROOF_DECL '{' PROOF_BODY '}'
		parser()["PROOF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv[1].get<Proof*>();
		};
		// PROOF_BODY <- PROOF_ELEM+
		parser()["PROOF_BODY"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return c->stacks.popProof();
		};

		parser()["COMMENT"] = [](const peg::SemanticValues& sv) {
			string text = sv.token();
			return new Comment(text.front() == ' ' ? text : " " + text);
		};
		parser()["ELEMENT"] = [&](const peg::SemanticValues& sv, peg::any& context) {
			// COMMENT / IMPORT / CONST / TYPE / RULE / AXIOM / DEF / THEOREM / PROOF / THEORY
			Node node;
			switch (sv.choice()) {
			case 0: node = Node(sv[0].get<Comment*>()); break;
			case 1: node = Node(sv[0].get<Import*>());  break;
			case 2: node = Node(sv[0].get<Const*>());   break;
			case 3: node = Node(sv[0].get<Type*>());    break;
			case 4: node = Node(sv[0].get<Rule*>());    break;
			case 5: node = Node(sv[0].get<Axiom*>());   break;
			case 6: node = Node(sv[0].get<Def*>());     break;
			case 7: node = Node(sv[0].get<Theorem*>()); break;
			case 8: node = Node(sv[0].get<Proof*>());   break;
			case 9: node = Node(sv[0].get<Theory*>());  break;
			}
			return node;
		};
		parser()["TH_DECL"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			c->theory = new Theory(sv[0].get<uint>(), c->theory);
		};
		parser()["THEORY"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Theory* th = c->theory;
			th->nodes = std::move(sv[1].get<vector<Node>&>());
			c->theory = th->parent;
			return th;
		};
		parser()["SOURCE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			c->source->theory->nodes = std::move(sv[0].get<vector<Node>&>());
			return c->source;
		};
		parser()["IMPORT"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint id = sv[0].get<uint>();
			const bool primary = !Sys::get().math.get<Source>().has(id);
			if (primary) parse(id);
			c->source->include(Sys::mod().math.get<Source>().access(id));
			return new Import(id, primary);
		};
	}

	static void parse(uint label) {
		Context* ctx = new Context();
		ctx->source = new Source(label);
		ctx->source->read();
		Parser p(label);
		peg::any c(ctx);
		p.parser().parse<Source*>(ctx->source->data().c_str(), c, ctx->source);
		delete ctx;
	}

private:
	static Rule* create_super(Type* inf, Type* sup) {
		return nullptr;
		/*Rule* rule = new Rule(
			create_id("sup", show_id(inf->id()), show_id(sup->id())),
			Vars(vector<Symbol>({create_symbol("x", inf)})),
			Expr({create_symbol("x", inf)}, sup)
		);
		*/

		//rule->id = create_id("sup", show_id(inf->id), show_id(sup->id));
		//rule->vars.v.push_back(create_symbol("x", inf));
		//rule->term.push_back(create_symbol("x", inf));
		//rule->type = sup;

		/*
		VarStack var_stack;
		AddVars add_vars;
		PushVars push_vars;
		push_vars(var_stack);
		add_vars(var_stack, rule->vars);
		mark_vars(rule->term, var_stack);
		parse_term(rule->term, rule);
		*/
		//return rule;
	}
	/*
	static void collect_supers(Type* inf, Type* s) {
		for (auto sup : s->sup) {
			Rule* super = create_super(inf, sup);
			inf->supers[sup] = super;
			collect_supers(inf, sup);
		}
	}
*/
};

void parse_peg(uint label) {
	Parser::parse(label);
}

}} // mdl::mm
