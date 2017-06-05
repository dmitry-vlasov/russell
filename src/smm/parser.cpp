#include "smm/ast.hpp"
#include "peglib.h"

namespace mdl { namespace smm {

struct Parser {
private:
	struct Context {
		void clear() {
			variables.clear();
			disjointed.clear();
			essential.clear();
			floating.clear();
			inner.clear();
			proof = nullptr;
		}
		vector<Variables*>  variables;
		vector<Disjointed*> disjointed;
		vector<Essential*>  essential;
		vector<Floating*>   floating;
		vector<Inner*>      inner;

		Proposition prop;
		Proof*      proof;
		Ref::Type   ref;
		Source*     source;

		Token token(const peg::SemanticValues& sv) const {
			return Token(source, sv.c_str(), sv.c_str() + sv.length());
		}
	};
	peg::parser parser;

	template<class T>
	static void check_vector(const vector<T*>& container, uint ind) {
		if (ind >= container.size())
			throw Error("array index out of boundaries", to_string(ind) + " >= " + to_string(container.size()));
	}
	template<class T>
	static void check_table(const Table<T>& table, uint lab) {
		if (!table.has(lab))
			throw Error("table doesn't have key", to_string(lab));
	}

public:
	static const char* smm_syntax() {
		return R"(
			# Simplified Metamath grammar

            SOURCE    <- ELEMENT+
			ELEMENT   <- COMMENT / '${' ASSERTION '$}'/ CONST / INCLUDE
			ASSERTION <- VAR* DISJ* ESS* FLO* INNER* PROP

			PROP    <- AX / TH
			EXPR    <- (SYMB / COMMENT)+
			CONST   <- '$c' SYMB '$.'
			VAR     <- '$v' EXPR '$.'
			DISJ    <- '$d' EXPR '$.'
			FLO     <- 'f' IND  '$f' EXPR '$.'
			ESS     <- 'e' IND  '$e' EXPR '$.'
			INNER   <- 'i' IND  '$f' EXPR '$.'
			AX      <- 'a' LAB  '$a' EXPR '$.'
			TH      <- 'p' LAB  '$p' EXPR '$=' PROOF
			PROOF   <- REF+ '$.'

			REF      <- REF_TYPE REF_VAL
			REF_TYPE <- < [efiap] >
			REF_VAL  <- < (![ \t\r\n$] .)+ >

			SYMB    <- < (![ \t\r\n$] .)+ >
			LAB     <- < (![ \t\r\n$] .)+ >
			IND     <- < [0-9]+ >
			COMMENT <- '$(' < (!'$)' .)* > '$)'
            INCLUDE <- '$[' < (!'$]' .)* > '$]'

			%whitespace <- [ \t\r\n]*
		)";
	}
	Parser(uint label) : parser(smm_syntax()) {

		parser["SYMB"] = [](const peg::SemanticValues& sv) {
			return Symbol(Lex::toInt(sv.token()));
		};
		parser["LAB"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser["IND"] = [](const peg::SemanticValues& sv) {
			return (uint)std::stoul(sv.token());
		};
		parser["EXPR"] = [](const peg::SemanticValues& sv) {
			Vect expr;
			expr.reserve(sv.size());
			for (auto& s : sv) {
				if (s.is<Symbol>()) expr += s.get<Symbol>();
				else delete s.get<Comment*>();
			}
			return expr;
		};
		parser["CONST"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Symbol s = sv[0].get<Symbol>();
			Constant* constant = new Constant(s);
			constant->token = c.token(sv);
			//Sys::mod().math.constants.insert(s);
			return constant;
		};
		parser["VAR"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Variables* vars = new Variables{sv[0].get<Vect>(), c.token(sv)};
			c.variables.push_back(vars);
			return vars;
		};
		parser["DISJ"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Disjointed* disj = new Disjointed{sv[0].get<Vect>(), c.token(sv)};
			c.disjointed.push_back(disj);
			return disj;
		};
		parser["ESS"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Essential* ess = new Essential{sv[0].get<uint>(), sv[1].get<Vect>(), c.token(sv)};
			c.essential.push_back(ess);
			return ess;
		};
		parser["FLO"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Floating* flo = new Floating{sv[0].get<uint>(), sv[1].get<Vect>(), c.token(sv)};
			c.floating.push_back(flo);
			return flo;
		};
		parser["INNER"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Inner* inn = new Inner{sv[0].get<uint>(), sv[1].get<Vect>(), c.token(sv)};
			c.inner.push_back(inn);
			return inn;
		};
		parser["AX"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			c.prop = {true, sv[0].get<uint>(), sv[1].get<Vect>(), c.token(sv)};
		};
		parser["TH"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			c.prop = {false, sv[0].get<uint>(), sv[1].get<Vect>(), c.token(sv) };
			c.proof = sv[2].get<Proof*>();
		};
		parser["PROOF"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Proof* pr = new Proof();
			pr->refs = sv.transform<Ref*>();
			pr->token = c.token(sv);
			return pr;
		};
		parser["REF_TYPE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			// REF_TYPE <- 'e' / 'f' / 'i' / 'a' / 'p'
			Ref::Type ref = Ref::Type::ESSENTIAL;
			switch (sv.token()[0]) {
			case 'e' : ref = Ref::Type::ESSENTIAL; break;
			case 'f' : ref = Ref::Type::FLOATING;  break;
			case 'i' : ref = Ref::Type::INNER;     break;
			case 'a' : ref = Ref::Type::AXIOM;     break;
			case 'p' : ref = Ref::Type::THEOREM;   break;
			default  : throw Error("unknown reference type in proof", sv.token());
			}
			context.get<Context*>()->ref = ref;
			return ref;
		};
		parser["REF_VAL"] = [](const peg::SemanticValues& sv, peg::any& context) {
			switch (context.get<Context*>()->ref) {
			case Ref::Type::ESSENTIAL : return (uint)std::stoul(sv.token());
			case Ref::Type::FLOATING  : return (uint)std::stoul(sv.token());
			case Ref::Type::INNER     : return (uint)std::stoul(sv.token());
			case Ref::Type::AXIOM     : return Lex::toInt(sv.token());
			case Ref::Type::THEOREM   : return Lex::toInt(sv.token());
			default  : throw Error("unknown reference val in proof", sv.token());
			}
		};
		parser["REF"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Ref::Type type = sv[0].get<Ref::Type>();
			uint lab = sv[1].get<uint>();
			Sys::Math& math = Sys::mod().math;
			switch (type) {
			case Ref::Type::ESSENTIAL : check_vector(c.essential, lab); return new Ref(c.essential[lab]);
			case Ref::Type::FLOATING  : check_vector(c.floating, lab);  return new Ref(c.floating[lab]);
			case Ref::Type::INNER     : check_vector(c.inner, lab);     return new Ref(c.inner[lab]);
			case Ref::Type::AXIOM     : check_table(math.get<Assertion>(), lab);  return new Ref(lab, true);
			case Ref::Type::THEOREM   : check_table(math.get<Assertion>(), lab);  return new Ref(lab, false);
			default  : throw Error("unknown reference type in proof", sv.token());
			}
		};
		parser["ASSERTION"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Assertion* ass = new Assertion(c.prop.label);
			ass->variables  = c.variables;
			ass->disjointed = c.disjointed;
			ass->floating   = c.floating;
			ass->inner      = c.inner;
			ass->essential  = c.essential;
			ass->proof      = c.proof;
			ass->prop       = c.prop;
			ass->token      = c.token(sv);
			c.clear();
			makeVars(ass->variables);
			makeVars(ass->disjointed);
			markVars(ass->variables, ass->floating);
			markVars(ass->variables, ass->inner);
			markVars(ass->variables, ass->essential);
			markVars(ass->variables, ass->prop.expr);
			return ass;
		};
		parser["COMMENT"] = [](const peg::SemanticValues& sv) {
			string text = sv.token();
			return new Comment(text.front() == ' ' ? text : " " + text);
		};
		parser["ELEMENT"] = [&](const peg::SemanticValues& sv, peg::any& context) {
			// COMMENT / '${' ASSERTION '$}'/ CONST / INCLUDE
			Node node;
			switch (sv.choice()) {
			case 0: node = Node(sv[0].get<Comment*>());   break;
			case 1: node = Node(sv[0].get<Assertion*>());break;
			case 2: node = Node(sv[0].get<Constant*>()); break;
			case 3: node = Node(sv[0].get<Inclusion*>()); break;
			default : throw Error("unknown smm syntax construction", sv.token());
			}
			return node;
		};
		parser["SOURCE"].enter = [label](peg::any& context) {
			Context& c = *context.get<Context*>();
			c.source = new Source(label);
		};
		parser["SOURCE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			c.source->contents = sv.transform<Node>();
			return c.source;
		};
		parser["INCLUDE"] = [](const peg::SemanticValues& sv) {
			uint id = Sys::make_name(sv.token());
			const bool primary = !Sys::get().math.get<Source>().has(id);
			if (primary) parse(id);
			return new Inclusion(id, primary);
		};
		parser.log = [label](size_t ln, size_t col, const std::string& err_msg) {
			std::stringstream ss;
			ss << "file: " << Lex::toStr(label) << ", line: " << ln << ", col: " << col << ": " << err_msg << std::endl;
			throw Error(ss.str());
		};
	}

	static Source* parse(uint label) {
		Path path(Lex::toStr(label), Sys::conf().get("root"), "smm");
		string data;
		path.read(data);
		Source* src = nullptr;
		Parser p(label);
		Context* context = new Context();
		peg::any c(context);
		if (!p.parser.parse<Source*>(data.c_str(), c, src)) return nullptr;
		std::swap(data, src->data);
		delete context;
		return src;
	}

private:
	static void makeVars(Vect& expr) {
		for (auto& symb : expr) symb.var = true;
	}
	template<typename T>
	static void makeVars(vector<T*>& vars) {
		for (auto& v_it : vars) makeVars(v_it->expr);
	}
	static void markVars(Vect& ex, const Vect& vars) {
		for (auto& s : ex) {
			if (contains(vars, s.lit)) s.var = true;
		}
	}
	static void markVars(const vector<Variables*>& vars, Vect& expr) {
		for (auto& v_it : vars) markVars(expr, v_it->expr);
	}
	template<class T>
	static void markVars(const vector<Variables*>& vars, vector<T>& components) {
		for (auto& comp : components) markVars(vars, comp->expr);
	}
};

void parse(uint label) {
	delete Sys::get().math.get<Source>().access(label);
	if (!Parser::parse(label))
		throw Error("parsing of " + Lex::toStr(label) + " failed");
}

}} // mdl::smm
