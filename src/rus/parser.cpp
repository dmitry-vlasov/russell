#include "rus/sys.hpp"
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
		Context() : ind(0), stacks(), expr(nullptr), type(nullptr), vars(nullptr), disj(nullptr) { }
		uint  ind;
		Stacks stacks;
		Expr* expr;
		Type* type;
		Vars* vars;
		Disj* disj;
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
			TYPE     <- 'type' LAB (':' LAB (',' LAB)*) ';;' 
			RULE     <- 'rule' LAB '(' VARS ')' '{' TERM '}'
			TERM     <- 'term' ':' LAB '=' '#' EXPR_TR ';;' 
			DEF      <- 'definition' LAB '(' VARS ')' DISJ '{' HYP* DEF_M DEF_S BAR PROP '}'
			DEF_M    <- 'defiendum' ':' LAB '=' '#' EXPR ';;' 
			DEF_S    <- 'definiens' ':' LAB '=' '#' EXPR ';;' 
			HYP      <- 'hyp' IND ':' LAB '=' '|-' EXPR ';;' 
			PROP     <- 'prop' IND ':' LAB '=' '|-' EXPR ';;'
			TERM     <- 'term' ':' LAB '=' '#' EXPR_TR ';;' 
			AXIOM    <- 'axiom' LAB '(' VARS ')' DISJ '{' (HYP+ BAR)? PROP '}'
			THEOREM  <- 'theorem' LAB '(' VARS ')' DISJ '{' (HYP+ BAR)? PROP '}'
			PROOF    <- 'proof' LAB? 'of' LAB '{' PROOF_EL+ '}'
			PROOF_EL <- 'var' VARS ';;' / STEP / QED
			DISJ     <- 'disjointed' '(' DISJ_SET (',' DISJ_SET)* ')'
			DISJ_SET <- LAB+

			STEP     <- 'step' IND ':' LAB '=' STEP_TP LAB ('(' REFS ')')? '|-' EXPR ';;'
			STEP_TP  <- 'thm' / 'def' / 'axm' / 'claim' / '?'
			QED      <- 'qed' 'prop' LAB '=' 'step' LAB ';;'

			VARS     <- (VAR (',' VAR)*)?
			VAR      <- SYMB : LAB
            BAR      <- '-----' '-'*

			EXPR     <- (SYMB / COMMENT)+
			SYMB     <- < (![ \t\r\n$] .)+ >
			LAB      <- < (![,(=;:{ \t\r\n$] .)+ >
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
		parser["LAB"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser["IND"] = [](const peg::SemanticValues& sv) {
			return (uint)std::stoul(sv.token());
		};
		parser["PATH"] = [](const peg::SemanticValues& sv) {
			return sv.token();
		};
		parser["EXPR"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* context = ctx.get<Context*>();
			Expr expr;
			expr.type = context->type;
			expr.symbols.reserve(sv.size());
			for (auto& s : sv) {
				if (s.is<Symbol>()) expr.symbols.push_back(s);
				else delete s.get<Comment*>();
			}
			mark_vars(expr, context->stacks);
			return expr;
		};
		parser["VAR"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* context = ctx.get<Context*>();
			Symbol v = sv[0].get<Symbol>();
			v.type = Sys::get().math.get<Type>().access(sv[1].get<uint>());
			return v;
		};
		parser["VARS"] = [](const peg::SemanticValues& sv) {
			return sv.transform<Symbol>();
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
			case 1 : c = new Const{sv[0].get<Vect>()}; break;
			case 2 : c = new Const{sv[0].get<Vect>(), sv[1].get<Vect>()}; break;
			case 3 : c = new Const{sv[0].get<Vect>(), sv[1].get<Vect>(), sv[2].get<Vect>()}; break;
			default : throw Error("syntax error");
			}
			return c;
		};
		parser["TYPE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* context = ctx.get<Context*>();
			Type* t = new Type(sv[0].get<uint>());
			collect_supers(t, t);
			return t;
		};
		parser["RULE"] = [](const peg::SemanticValues& sv, peg::any& ctx) {
			Context* context = ctx.get<Context*>();
			uint id   = sv[0].get<uint>();
			Vars vars = sv[1].get<Vars>();
			Expr term = sv[2].get<Expr>();
			Rule* r = new Rule(id, term.type->id());
			r->vars = vars;
			r->term = term;
			return r;
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
