#include "smm/sys.hpp"
#include "peglib.h"

namespace mdl { namespace smm {

struct Parser {
private:
	struct Context {
		~Context() { clear(); }
		void clear() {
			ass.variables.clear();
			ass.disjointed.clear();
			ass.essential.clear();
			ass.floating.clear();
			ass.inner.clear();
			ass.proof = nullptr;
		}
		Assertion ass;
		Ref::Type ref;
	};
	peg::parser parser;

	template<class T>
	static void check_vector(const vector<T*>& container, uint ind) {
		if (ind >= container.size())
			throw Error("array index out of boundaries", to_string(ind) + " >= " + to_string(container.size()));
	}
	template<class T>
	static void check_map(const map<uint, T*>& container, uint lab) {
		if (!container.count(lab))
			throw Error("map doesn't have key", to_string(lab));
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
			CONST   <- '$c' EXPR '$.'
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
	Parser(const Path& path) : parser(smm_syntax()) {

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
		parser["CONST"] = [](const peg::SemanticValues& sv) {
			Constants* consts = new Constants { sv[0].get<Vect>() };
			for (Symbol c : consts->expr)
				System::mod().math.constants.insert(c);
			return consts;
		};
		parser["VAR"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Variables* vars = new Variables { sv[0].get<Vect>() };
			context.get<std::shared_ptr<Context>>()->ass.variables.push_back(vars);
			return vars;
		};
		parser["DISJ"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Disjointed* disj = new Disjointed { sv[0].get<Vect>() };
			context.get<std::shared_ptr<Context>>()->ass.disjointed.push_back(disj);
			return disj;
		};
		parser["ESS"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Essential* ess = new Essential { sv[0].get<uint>(), sv[1].get<Vect>() };
			context.get<std::shared_ptr<Context>>()->ass.essential.push_back(ess);
			return ess;
		};
		parser["FLO"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Floating* flo = new Floating { sv[0].get<uint>(), sv[1].get<Vect>() };
			context.get<std::shared_ptr<Context>>()->ass.floating.push_back(flo);
			return flo;
		};
		parser["INNER"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Inner* inn = new Inner { sv[0].get<uint>(), sv[1].get<Vect>() };
			context.get<std::shared_ptr<Context>>()->ass.inner.push_back(inn);
			return inn;
		};
		parser["AX"] = [](const peg::SemanticValues& sv, peg::any& context) {
			context.get<std::shared_ptr<Context>>()->ass.prop = { true, sv[0].get<uint>(), sv[1].get<Vect>() };
		};
		parser["TH"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Assertion& a = context.get<std::shared_ptr<Context>>()->ass;
			a.prop = { false, sv[0].get<uint>(), sv[1].get<Vect>() };
			a.proof = sv[2].get<Proof*>();
		};
		parser["PROOF"] = [](const peg::SemanticValues& sv) {
			Proof* pr = new Proof();
			pr->refs = sv.transform<Ref*>();
			return pr;
		};
		parser["REF_TYPE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			// REF_TYPE <- 'e' / 'f' / 'i' / 'a' / 'p'
			Ref::Type ref = Ref::Type::NONE;
			switch (sv.token()[0]) {
			case 'e' : ref = Ref::Type::ESSENTIAL; break;
			case 'f' : ref = Ref::Type::FLOATING;  break;
			case 'i' : ref = Ref::Type::INNER;     break;
			case 'a' : ref = Ref::Type::AXIOM;     break;
			case 'p' : ref = Ref::Type::THEOREM;   break;
			default  : throw Error("unknown reference type in proof", sv.token());
			}
			context.get<std::shared_ptr<Context>>()->ref = ref;
			return ref;
		};
		parser["REF_VAL"] = [](const peg::SemanticValues& sv, peg::any& context) {
			switch (context.get<std::shared_ptr<Context>>()->ref) {
			case Ref::Type::ESSENTIAL : return (uint)std::stoul(sv.token());
			case Ref::Type::FLOATING  : return (uint)std::stoul(sv.token());
			case Ref::Type::INNER     : return (uint)std::stoul(sv.token());
			case Ref::Type::AXIOM     : return Lex::toInt(sv.token());
			case Ref::Type::THEOREM   : return Lex::toInt(sv.token());
			default  : throw Error("unknown reference val in proof", sv.token());
			}
		};
		parser["REF"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Assertion& ass = context.get<std::shared_ptr<Context>>()->ass;
			Ref::Type type = sv[0].get<Ref::Type>();
			uint lab = sv[1].get<uint>();
			System::Math& math = System::mod().math;
			switch (type) {
			case Ref::Type::ESSENTIAL : check_vector(ass.essential, lab); return new Ref(ass.essential[lab]);
			case Ref::Type::FLOATING  : check_vector(ass.floating, lab);  return new Ref(ass.floating[lab]);
			case Ref::Type::INNER     : check_vector(ass.inner, lab);     return new Ref(ass.inner[lab]);
			case Ref::Type::AXIOM     : check_map(math.assertions, lab);  return new Ref(math.assertions[lab], true);
			case Ref::Type::THEOREM   : check_map(math.assertions, lab);  return new Ref(math.assertions[lab], false);
			default  : throw Error("unknown reference type in proof", sv.token());
			}
		};
		parser["ASSERTION"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Assertion& a = context.get<std::shared_ptr<Context>>()->ass;
			Assertion* ass = new Assertion();
			*ass = a;
			context.get<std::shared_ptr<Context>>()->clear();
			makeVars(ass->variables);
			makeVars(ass->disjointed);
			markVars(ass->variables, ass->floating);
			markVars(ass->variables, ass->inner);
			markVars(ass->variables, ass->essential);
			markVars(ass->variables, ass->prop.expr);
			System::mod().math.assertions[ass->prop.label] = ass;
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
			case 2: node = Node(sv[0].get<Constants*>()); break;
			case 3: node = Node(sv[0].get<Inclusion*>()); break;
			default : throw Error("unknown smm syntax construction", sv.token());
			}
			return node;
		};
		parser["SOURCE"] = [path](const peg::SemanticValues& sv) {
			Source* src = new Source(Lex::toInt(path.name));
			src->contents = sv.transform<Node>();
			return src;
		};
		parser["INCLUDE"] = [path](const peg::SemanticValues& sv, peg::any& context) {
			string name = sv.token();
			static map<string, Inclusion*> included;
			if (included.count(name)) {
				Inclusion* inc = included[name];
				return new Inclusion(inc->source, false);
			} else {
				Path new_path(path);
				new_path.name_ext(name);
				Inclusion* inc = new Inclusion(nullptr, true);
				included[name] = inc;
				inc->source = parse(new_path);
				return inc;
			}
		};
	}

	static Source* parse(Path path) {
		path = path.verify();
		string data;
		path.read(data);
		Parser p(path);
		Source* src = nullptr;
		peg::any context(std::make_shared<Context>());
		if (!p.parser.parse<Source*>(data.c_str(), context, src)) return nullptr;
		std::swap(data, src->data);
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

Source* parse(const Path& path) {
	return Parser::parse(path);
}

}} // mdl::smm
