#include <rus_ast.hpp>
#include "peglib.h"

namespace mdl { namespace rus {

#define PARALLEL_PARSE

static const Symbol dfm(Lex::toInt("defiendum"));
static const Symbol dfs(Lex::toInt("definiens"));

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
			typing[v.lit] = v.type_id();
		}
		void markType(Symbol& s) const {
			if (typing.count(s.lit)) s.set_type(typing.at(s.lit));
			else s.set_const();
		}
		Symbol makeSymb(uint lit, bool strict, const Token& token) const {
			Symbol s(lit);
			if (typing.count(lit)) {
				s.set_type(typing.at(lit));
			} else if (strict || !(lit == dfm.lit || lit == dfs.lit)) {
				s.set_const();
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
		map<uint, uint> typing;
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
	peg::parser parser_;

	static const char* rus_syntax() {
		return R"(
			# Russell grammar
		
            SOURCE     <-  ELEMENT*
            THEORY     <-  TH_DECL '{' ELEMENT* '}'
            TH_DECL    <- 'theory' ID_NAME 
			ELEMENT    <-  COMMENT / IMPORT / CONST / TYPE / RULE / AXIOM / DEF / THEOREM / PROOF / THEORY
 
			IMPORT     <- 'import' PATH ';;'
			CONST      <- 'constant' '{' 'symbol' SYMB_CONST ';;' ('ascii' SYMB_CONST ';;' ('latex' SYMB_CONST ';;')?)? '}'

			TYPE       <- 'type' ID_NAME (SUPERS)? ';;' 
			SUPERS     <- ':' ID_REF (',' ID_REF)*

			RULE       <- 'rule'       ID_NAME '(' VARS ')'      '{' TERM '}'
			AXIOM      <- 'axiom'      ID_NAME '(' VARS ')' DISJ '{' HYPS PROPS '}'
			THEOREM    <- 'theorem'    ID_NAME '(' VARS ')' DISJ '{' HYPS PROPS '}'
			DEF        <- 'definition' ID_NAME '(' VARS ')' DISJ '{' DEF_H DEF_M DEF_S BAR DEF_P '}'

			PROOF      <-  PROOF_DECL '{' PROOF_BODY '}'
			PROOF_DECL <-  PROOF_ANON / PROOF_NAME 
			PROOF_NAME <- 'proof' ID_NAME 'of' ID_REF
			PROOF_ANON <- 'proof' 'of' ID_REF
			PROOF_BODY <-  PROOF_ELEM+
			PROOF_ELEM <-  VAR_DECL / STEP / QED

            TERM       <- 'term'      EX_TERM
			DEF_M      <- 'defiendum' EX_TERM 
			DEF_S      <- 'definiens' EX_TERM
           	DEF_P      <- 'prop'      EX_PLAIN
			DEF_H      <-  HYP*
			HYPS       <- (HYP+ BAR)?
			PROPS      <-  PROP+
			HYP        <- 'hyp'  IND  EX_STAT
			PROP       <- 'prop' IND  EX_STAT 

            EX_TERM    <- ':' ID_REF '=' '#'  SYMBS_TYPED ';;'
            EX_STAT    <- ':' ID_REF '=' '|-' SYMBS_TYPED ';;'
            EX_PLAIN   <- ':' ID_REF '=' '|-' SYMBS_PLAIN ';;' 

			DISJ       <- ('disjointed' '(' DISJ_SET (',' DISJ_SET)* ')')?
			DISJ_SET   <-  DISJ_VAR+

			STEP       <-  STEP_ASS / STEP_QST
			STEP_ASS   <- 'step' IND ':' ID_REF '=' ID_REF  '(' REFS ')' '|-' SYMBS_TYPED ';;'
			
			STEP_QST   <- 'step' IND ':' ID_REF '=' ? '|-' EX_STAT ';;'
			REFS       <- (REF (',' REF)*)?
			REF        <-  REF_HYP / REF_PROP / REF_STEP
			REF_HYP    <- 'hyp'  IND
			REF_PROP   <- 'prop' IND
			REF_STEP   <- 'step' IND
			QED        <- 'qed' 'prop' IND '=' 'step' IND ';;'

			VAR_DECL   <- 'var' VARS ';;'
			VARS       <- (VAR (',' VAR)*)?
			VAR        <-  ID_NAME ':' ID_REF
            BAR        <- '-----' '-'*

			SYMBS_TYPED <- (SYMB_TYPED / COMMENT)+
            SYMBS_PLAIN <- (SYMB_PLAIN / COMMENT)+

			SYMB_TYPED <- < (![; \t\r\n$] .)+ >
            SYMB_PLAIN <- < (![; \t\r\n$] .)+ >
			SYMB_CONST <- < (![; \t\r\n$] .)+ >
			ID_REF     <- < (![,(=;:){ \t\r\n$] .)+ >
			ID_NAME    <- < (![,(=;:){ \t\r\n$] .)+ >
			DISJ_VAR   <- < (![,) \t\r\n$] .)+ >
			PATH       <- < (![; \t\r\n$] .)+ >
			IND        <- < [0-9]+ >
			COMMENT    <- COMMENT_ML / COMMENT_SL 
			COMMENT_ML <- '/*' < (!'*/' .)* > '*/'
			COMMENT_SL <- '//' < (![\n$] .)+ >
		
			%whitespace <- [ \t\r\n]*
		)";
	}
	Parser(uint src) {
		parser_.log = [src](size_t ln, size_t col, const std::string& err_msg) {
			std::stringstream ss;
			ss << "file: " << Lex::toStr(src) << ", line: " << ln << ", col: " << col << ": " << err_msg << "\n";
			throw Error(ss.str());
		};
		parser_.load_grammar(rus_syntax());
		if (!parser_) {
			cerr << "Russell grammar is not correct" << endl;
			exit(1);
		}
		parser_["SYMB_TYPED"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return c->stacks.makeSymb(Lex::toInt(sv.token()), true, c->token(sv));
		};
		parser_["DISJ_VAR"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser_["SYMB_PLAIN"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return c->stacks.makeSymb(Lex::toInt(sv.token()), false, c->token(sv));
		};
		parser_["SYMB_CONST"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser_["ID_NAME"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser_["ID_REF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return Id(Lex::toInt(sv.token()), c->token(sv));
		};
		parser_["IND"] = [](const peg::SemanticValues& sv) {
			return (uint)std::stoul(sv.token());
		};
		parser_["PATH"] = [](const peg::SemanticValues& sv) {
			return Sys::make_name(sv.token());
		};
		parser_["SYMBS_TYPED"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			vector<Symbol> vect;
			vect.reserve(sv.size());
			for (auto& s : sv) {
				if (s.is<Symbol>()) vect.push_back(s.get<Symbol>());
				else delete s.get<Comment*>();
			}
			return vect;
		};
		parser_["SYMBS_PLAIN"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			vector<Symbol> vect;
			vect.reserve(sv.size());
			for (auto& s : sv) {
				if (s.is<Symbol>()) vect.push_back(s.get<Symbol>());
				else delete s.get<Comment*>();
			}
			return vect;
		};
		parser_["EX_TERM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Id id = sv[0].get<Id>();
			vector<Symbol> term = sv[1].get<vector<Symbol>>();
			return Expr(id, std::move(term), c->token(sv));
		};
		parser_["EX_STAT"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Id id = sv[0].get<Id>();
			vector<Symbol> expr = sv[1].get<vector<Symbol>>();
			return Expr(id, std::move(expr), c->token(sv));
		};
		parser_["EX_PLAIN"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			vector<Symbol> expr = sv[1].get<vector<Symbol>>();
			return Expr(sv[0].get<Id>(), std::move(expr), c->token(sv));
		};
		parser_["VAR"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint v = sv[0].get<uint>();
			Id tp = sv[1].get<Id>();
			Symbol va = Symbol(v, tp, Symbol::VAR);
			c->stacks.addVar(va);
			return va;
		};
		parser_["VARS"].enter = [](peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			c->stacks.pushVars();
		};
		parser_["VARS"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return Vars(sv.transform<Symbol>());
		};
		parser_["VAR_DECL"] = [](const peg::SemanticValues& sv) {
			return new Vars(sv[0].get<Vars>());
		};
		parser_["DISJ_SET"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			set<uint> disj;
			for (const auto& v : sv) {
				disj.insert(v.get<uint>());
			}
			return disj;
		};
		parser_["DISJ"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			if (sv.size()) {
				Disj disj;
				for (const auto& dis : sv) {
					const set<uint>& d = dis.get<set<uint>>();
					for (auto v : d) {
						for (auto w : d) {
							if (v != w) {
								disj.dmap.emplace(v, w);
							}
						}
					}
				}
				return disj;
			} else {
				return Disj();
			}
		};
		parser_["CONST"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Const* c = nullptr;
			switch (sv.size()) {
			case 1 : c = new Const(sv[0].get<uint>(), Symbol::undef(), Symbol::undef()); break;
			case 2 : c = new Const(sv[0].get<uint>(), sv[1].get<uint>(), Symbol::undef()); break;
			case 3 : c = new Const(sv[0].get<uint>(), sv[1].get<uint>(), sv[2].get<uint>()); break;
			default : throw Error("syntax error");
			}
			return c;
		};
		parser_["SUPERS"] = [](const peg::SemanticValues& sv) {
			return sv.transform<Id>();
		};
		parser_["TYPE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			vector<Id> supers = (sv.size() == 1) ? vector<Id>() : sv[1].get<vector<Id>>();
			return new Type(sv[0].get<uint>(), std::move(supers), c->token(sv));
		};
		parser_["RULE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			c->stacks.popVars();
			Rule* r = new Rule(
				Id(sv[0].get<uint>()),
				std::move(sv[1].get<Vars>()),
				std::move(sv[2].get<Expr>()),
				c->token(sv)
			);
			return r;
		};
		// HYP <- 'hyp'  IND  EX_STAT
		parser_["HYP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return new Hyp(sv[0].get<uint>() - 1, std::move(sv[1].get<Expr>()), c->token(sv));
		};
		// HYPS -> (HYP+ BAR)?
		parser_["HYPS"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			vector<Hyp*> hyps;
			hyps.reserve(sv.size());
			for (auto& s : sv) {
				if (s.is<Hyp*>()) hyps.push_back(s.get<Hyp*>());
			}
			return hyps;
		};
		// PROP <- 'prop'  IND  EX_STAT
		parser_["PROP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return new Prop(sv[0].get<uint>() - 1, std::move(sv[1].get<Expr>()), c->token(sv));
		};
		// PROPS -> PROP+
		parser_["PROPS"] = [](const peg::SemanticValues& sv) {
			return sv.transform<Prop*>();
		};
		parser_["AXIOM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Id id(sv[0].get<uint>());
			Axiom* a = new Axiom(id, c->token(sv));
			a->vars  = std::move(sv[1].get<Vars>());
			a->disj  = std::move(sv[2].get<Disj>());
			for (Hyp* h : sv[3].get<vector<Hyp*>>()) {
				a->hyps.emplace_back(h);
			}
			for (Prop* p : sv[4].get<vector<Prop*>>()) {
				a->props.emplace_back(p);
			}
			enqueue_expr(a);
			return a;
		};
		parser_["THEOREM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Id id(sv[0].get<uint>());
			Theorem* t = new Theorem(id, c->token(sv));
			t->vars  = std::move(sv[1].get<Vars>());
			t->disj  = std::move(sv[2].get<Disj>());
			for (Hyp* h : sv[3].get<vector<Hyp*>>()) {
				t->hyps.emplace_back(h);
			}
			for (Prop* p : sv[4].get<vector<Prop*>>()) {
				t->props.emplace_back(p);
			}
			enqueue_expr(t);
			return t;
		};
		parser_["DEF_M"] = [](const peg::SemanticValues& sv) {
			return sv[0].get<Expr>();
		};
		parser_["DEF_S"] = [](const peg::SemanticValues& sv) {
			return sv[0].get<Expr>();
		};
		parser_["DEF_H"] = [](const peg::SemanticValues& sv) {
			return sv.transform<Hyp*>();
		};
		parser_["DEF_P"] = [](const peg::SemanticValues& sv) {
			return sv[0].get<Expr>();
		};
		// DEF <- 'definition' ID_NAME '(' VARS ')' DISJ '{' DEF_H DEF_M DEF_S BAR DEF_P '}'
		parser_["DEF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Def* d = new Def(Id(sv[0].get<uint>()), c->token(sv));
			d->vars = std::move(sv[1].get<Vars>());
			d->disj = std::move(sv[2].get<Disj>());
			vector<Hyp*> hyps = sv[3].get<vector<Hyp*>>();
			d->hyps.reserve(hyps.size());
			for (Hyp* h : hyps) d->hyps.emplace_back(h);
			d->dfm  = std::move(sv[4].get<Expr>());
			d->dfs  = std::move(sv[5].get<Expr>());
			d->prop = std::move(sv[7].get<Expr>());
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
			d->props.emplace_back(prop);
			enqueue_expr(d);
			return d;
		};
		// STEP <- STEP_ASS / STEP_QST
		parser_["STEP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv[0].get<Step*>();
		};
		// STEP_ASS <- 'step' IND ':' ID_REF '=' ID_REF  '(' REFS ')' '|-' EXPR ';;'
		parser_["STEP_ASS"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Id  type = sv[1].get<Id>();
			Id  ass  = sv[2].get<Id>();
			vector<Symbol> expr = sv[4].get<vector<Symbol>>();
			vector<Ref*> refs = sv[3].get<vector<Ref*>>();
			Step* s = new Step(ind, Step::ASS, ass, c->stacks.proof(), c->token(sv));
			s->refs.reserve(refs.size());
			for (Ref* r : refs) {
				s->refs.emplace_back(r);
			}
			s->expr = std::move(Expr(type, std::move(expr), c->token(sv)));
			expr::enqueue(s->expr);
			return s;
		};
		// STEP_QST <- 'step' IND ':' ID_REF '=' ? '|-' EXPR ';;'
		parser_["STEP_QST"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Id  type = sv[1].get<Id>();
			vector<Symbol> expr = sv[4].get<vector<Symbol>>();
			Step* s = new Step(ind, Step::CLAIM, Id(), c->stacks.proof(), c->token(sv));
			s->expr = std::move(Expr(type, std::move(expr), c->token(sv)));
			expr::enqueue(s->expr);
			return s;
		};
		// REF_HYP <- 'hyp' IND
		parser_["REF_HYP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Proof* p = c->stacks.proof();
			return new Ref(p->theorem()->hyps[ind - 1].get());
		};
		// REF_PROP <- 'prop' IND
		parser_["REF_PROP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>();
			Proof* p = c->stacks.proof();
			return new Ref(p->theorem()->props[ind - 1].get());
		};
		// REF_STEP <- 'step' IND
		parser_["REF_STEP"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint ind = sv[0].get<uint>() - 1;
			Proof* p = c->stacks.proof();
			if (ind >= p->elems.size()) {
				throw Error("invalid step index", sv.token());
			}
			Proof::Elem& e = p->elems[ind];
			if (Proof::kind(e) != Proof::STEP) {
				throw Error("by reference is not a step", sv.token());
			}
			return new Ref(Proof::step(e));
		};
		// REF <- REF_HYP / REF_PROP / REF_STEP
		parser_["REF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv[0].get<Ref*>();
		};
		// REFS <- (ID_REF (',' ID_REF)*)?
		parser_["REFS"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv.transform<Ref*>();
		};
		// QED <- 'qed' 'prop' ID_REF '=' 'step' ID_REF ';;'
		parser_["QED"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint prop = sv[0].get<uint>();
			uint step = sv[1].get<uint>();
			Proof* p = c->stacks.proof();
			return new Qed(
				p->theorem()->props[prop - 1].get(),
				Proof::step(p->elems[step - 1])
			);
		};
		// PROOF_ELEM <- VAR_DECL / STEP / QED
		parser_["PROOF_ELEM"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Proof* p = c->stacks.proof();
			switch (sv.choice()) {
			case 0: p->elems.emplace_back(unique_ptr<Vars>(sv[0].get<Vars*>())); break;
			case 1: p->elems.emplace_back(unique_ptr<Step>(sv[0].get<Step*>())); break;
			case 2: p->elems.emplace_back(unique_ptr<Qed>(sv[0].get<Qed*>()));  break;
			}
			Proof::Elem& e = p->elems.back();

			// TODO: Do a right var/elem tracking!
			if (Proof::kind(e) == Proof::VARS) {
				for (const auto& v : Proof::vars(e)->v) {
					p->allvars.v.push_back(v);
				}
			}
		};
		// PROOF_BODY <- PROOF_ELEM+
		parser_["PROOF_BD"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			//return sv.transform<Proof::Elem>();
		};
		// PROOF_NAME -> ID_NAME?
		parser_["PROOF_NAME"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return (sv.size() == 0) ? Id() : Id(sv[0].get<uint>(), c->token(sv));
		};
		// PROOF_NAME <- 'proof' ID_NAME 'of' ID_REF
		parser_["PROOF_NAME"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			uint id  = sv[0].get<uint>();
			Id   ref = sv[1].get<Id>();
			return new Proof(ref, id, c->token(sv));
		};
		// PROOF_ANON <- 'proof' 'of' ID_REF
		parser_["PROOF_ANON"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Id ref = sv[0].get<Id>();
			return new Proof(ref, Id(), c->token(sv));
		};

		// PROOF_DECL <- 'proof' ID_NAME? 'of' ID_REF
		parser_["PROOF_DECL"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Proof* p  = sv[0].get<Proof*>();
			c->stacks.pushProof(p);
			return p;
		};
		// PROOF <- PROOF_DECL '{' PROOF_BODY '}'
		parser_["PROOF"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			return sv[1].get<Proof*>();
		};
		// PROOF_BODY <- PROOF_ELEM+
		parser_["PROOF_BODY"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			Proof* p = c->stacks.popProof();
			enqueue_expr(p);
			return p;
		};
		parser_["COMMENT_ML"] = [](const peg::SemanticValues& sv) {
			string text = sv.token();
			return new Comment(true, text.front() == ' ' ? text : " " + text);
		};
		parser_["COMMENT_SL"] = [](const peg::SemanticValues& sv) {
			string text = sv.token();
			return new Comment(false, text.front() == ' ' ? text : " " + text);
		};
		// ELEMENT <- COMMENT / IMPORT / CONST / TYPE / RULE / AXIOM / DEF / THEOREM / PROOF / THEORY
		parser_["ELEMENT"] = [&](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			switch (sv.choice()) {
			case 0: c->theory->nodes.emplace_back(unique_ptr<Comment>(sv[0].get<Comment*>())); break;
			case 1: c->theory->nodes.emplace_back(unique_ptr<Import>(sv[0].get<Import*>()));   break;
			case 2: c->theory->nodes.emplace_back(unique_ptr<Const>(sv[0].get<Const*>()));     break;
			case 3: c->theory->nodes.emplace_back(unique_ptr<Type>(sv[0].get<Type*>()));       break;
			case 4: c->theory->nodes.emplace_back(unique_ptr<Rule>(sv[0].get<Rule*>()));       break;
			case 5: c->theory->nodes.emplace_back(unique_ptr<Axiom>(sv[0].get<Axiom*>()));     break;
			case 6: c->theory->nodes.emplace_back(unique_ptr<Def>(sv[0].get<Def*>()));         break;
			case 7: c->theory->nodes.emplace_back(unique_ptr<Theorem>(sv[0].get<Theorem*>())); break;
			case 8: c->theory->nodes.emplace_back(unique_ptr<Proof>(sv[0].get<Proof*>()));     break;
			case 9: c->theory->nodes.emplace_back(unique_ptr<Theory>(sv[0].get<Theory*>()));   break;
			}
		};
		parser_["TH_DECL"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			c->theory = new Theory(sv[0].get<uint>(), c->theory);
		};
		parser_["THEORY"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			c->theory = c->theory->parent;
		};
		parser_["SOURCE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* c = ctx.get<Context*>();
			return c->source;
		};
		parser_["IMPORT"] = [](const peg::SemanticValues& sv) {
			uint id = sv[0].get<uint>();
#ifndef PARALLEL_PARSE
			Source* s = Sys::mod().math.get<Source>().access(id);
			if (!s->parsed) parse(id);
#endif
			return new Import(id);
		};
	}

	static void enqueue_expr(Assertion* ass) {
		for (auto& h : ass->hyps) {
			expr::enqueue(h.get()->expr);
		}
		for (auto& p : ass->props) {
			expr::enqueue(p.get()->expr);
		}
	}
	static void enqueue_expr(Proof* proof) {
		for (const auto& e : proof->elems) {
			if (Proof::kind(e) == Proof::STEP) {
				Step* step = Proof::step(e);
				expr::enqueue(step->expr);
				if (step->kind() == Step::CLAIM)
					enqueue_expr(step->claim());
			}
		}
	}
	static void enqueue_expr(Def* def) {
		expr::enqueue(def->dfm);
		expr::enqueue(def->dfs);
		enqueue_expr(static_cast<Assertion*>(def));
	}

public:
	static void parse(uint label) {
		Context* ctx = new Context();
		ctx->source = Sys::mod().math.get<Source>().access(label);
		ctx->theory = &ctx->source->theory;
		peg::any c(ctx);
		Parser p(label);
		if (!p.parser_.parse<Source*>(ctx->source->data().c_str(), c, ctx->source)) {
			throw Error("parsing of " + Lex::toStr(label) + " failed");
		}
		delete ctx;
		ctx->source->parsed = true;
	}
};

void parse_src_peg() {
#ifdef PARALLEL_PARSE
	vector<uint> labels;
	for (auto p : Sys::mod().math.get<Source>())
		if (!p.second.data->parsed) labels.push_back(p.first);
	tbb::parallel_for (tbb::blocked_range<size_t>(0, labels.size()),
		[labels] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				Parser::parse(labels[i]);
		}
	);
#else
	for (auto p : Sys::mod().math.get<Source>())
		if (!p.second.data->parsed) Parser::parse(p.first);
#endif
}

}} // mdl::mm
