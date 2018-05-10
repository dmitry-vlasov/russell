//#include <boost/variant/recursive_variant.hpp>
#include <mm2_ast.hpp>
#include "peglib.h"

namespace mdl { namespace mm2 { namespace {

#define PARALLEL_PARSE

struct Disj {
	vector<uint> disj;
	vector<uint>* make(const set<uint>& vars) const {
		vector<uint>* dvars = new vector<uint>();
		dvars->reserve(disj.size());
		for (uint dv : disj) {
			if (vars.find(dv) != vars.end()) {
				dvars->emplace_back(dv);
			}
		}
		return dvars;
	}
};

struct Hyp  {
	uint label;
	vector<uint> expr;
	mm2::Hyp* make(uint index, const set<uint>& vars) const {
		mm2::Hyp* h = new mm2::Hyp(index, label);
		h->expr.reserve(expr.size());
		for (uint s : expr) {
			h->expr.emplace_back(s, vars.find(s) != vars.end());
		}
		return h;
	}
};

struct Var  {
	uint label;
	uint type;
	uint var;
	mm2::Var* make(bool inner, uint index) const {
		return new mm2::Var(inner, index, label, type, var);
	}
};

struct Block {
	typedef variant<Disj, Hyp, Var> Node;

	Block(Block* p = nullptr) : parent(p) { }

	Assertion* create_assertion(uint label, const vector<uint>& expr, const vector<uint>& proof) {
		vector<const Hyp*>  essentials = gather<Hyp>();
		vector<const Var*>  all_floatings  = gather<Var>();
		vector<const Disj*> all_disjointed = gather<Disj>();

		// Gather all symbols, used in assertion hypotheses and statement (header).
		set<uint> ass_symbs;
		gather_symbs(ass_symbs, expr);
		for (const Hyp* ess : essentials) {
			gather_symbs(ass_symbs, ess->expr);
		}

		// Collect floatings, which refer to assertion, and all variables.
		vector<const Var*> floatings;
		set<uint> flo_vars;
		map<uint, const Var*> flo_map;
		for (const Var* flo : all_floatings) {
			flo_map[flo->label] = flo;
			if (ass_symbs.find(flo->var) != ass_symbs.end()) {
				floatings.push_back(flo);
				flo_vars.insert(flo->var);
			}
		}

		// Collect inner variables from proof.
		set<uint> inner_vars;
		for (uint l : proof) {
			auto flo_it = flo_map.find(l);
			if (flo_it != flo_map.end()) {
				const Var* flo = (*flo_it).second;
				if (ass_symbs.find(flo->var) == ass_symbs.end()) {
					inner_vars.insert(flo->var);
				}
			}
		}

		// Collect inner proof floating declarations.
		vector<const Var*> inners;
		for (const Var* flo : all_floatings) {
			if (inner_vars.find(flo->var) != inner_vars.end()) {
				inners.push_back(flo);
			}
		}

		// Gather all assertion vars;
		set<uint> vars(flo_vars);
		for (uint i : inner_vars) {
			vars.insert(i);
		}

		Assertion* ass = new Assertion(label);
		ass->vars.vars.reserve(vars.size());
		for (uint v : vars) ass->vars.vars.emplace_back(v);

		// Make final set of disjointeds.
		ass->disj.vect.reserve(all_disjointed.size());
		for (const Disj* disj : all_disjointed) {
			ass->disj.vect.emplace_back(disj->make(vars));
		}

		// Make final set of essentials.
		uint i = 0;
		ass->hyps.reserve(essentials.size());
		for (const Hyp* hyp : essentials) {
			ass->hyps.emplace_back(hyp->make(i++, vars));
		}

		// Make final set of floatings.
		ass->outerVars.reserve(floatings.size());
		i = 0;
		for (const Var* flo : floatings) {
			ass->outerVars.emplace_back(flo->make(i++, false));
		}

		// Make final set of inners.
		ass->innerVars.reserve(inners.size());
		for (const Var* flo : inners) {
			ass->innerVars.emplace_back(flo->make(i++, true));
		}

		ass->expr.reserve(expr.size());
		for (uint s : expr) {
			ass->expr.emplace_back(s, vars.find(s) != vars.end());
		}

		return ass;
	}

	template<class N>
	vector<const N*> gather() const {
		vector<const N*> vect;
		if (parent) {
			vect = std::move(parent->gather<N>());
		}
		for (const auto& n : nodes) {
			if (std::holds_alternative<N>(n)) {
				vect.emplace_back(&std::get<N>(n));
			}
		}
		return vect;
	}
	template<class N, class M>
	vector<const N*> gather() const {
		vector<const N*> vect;
		if (parent) {
			vect = std::move(parent->gather<N, M>());
		}
		for (const auto& n : nodes) {
			if (std::holds_alternative<N>(n)) {
				vect.emplace_back(&std::get<N>(n));
			}
			if (std::holds_alternative<M>(n)) {
				vect.emplace_back(&std::get<M>(n));
			}
		}
		return vect;
	}
	void gather_symbs(set<uint>& symbs, const vector<uint>& expr) {
		for (uint s : expr) {
			symbs.insert(s);
		}
	}

	Block* parent;
	vector<Node> nodes;
};

struct Parser {
private:
	struct Context {
		stack<Block> blocks;
		Source*      source;

		Token token(const peg::SemanticValues& sv) const {
			return Token(source, sv.c_str(), sv.c_str() + sv.length());
		}
	};
	peg::parser parser;

public:
	static const char* mm_syntax() {
		return R"(
			# Metamath grammar
		
            SOURCE  <- BLOCK
			BLOCK   <- ELEMENT*
			ELEMENT <- COMMENT / DISJ / ESS / TH / '${' BLOCK '$}'/ AX / CONST / VAR / FLO / INCLUDE 
			EXPR    <- (SYMB / COMMENT)+
			CONST   <-      '$c' SYMB '$.'
			VAR     <-      '$v' SYMB '$.'
			DISJ    <-      '$d' EXPR '$.'
			FLO     <- LAB  '$f' SYMB SYMB '$.'
			ESS     <- LAB  '$e' EXPR '$.'
			AX      <- LAB  '$a' EXPR '$.'
			TH      <- LAB  '$p' EXPR '$=' PROOF
			PROOF   <- LAB+ '$.'
		
			SYMB    <- < (![ \t\r\n$] .)+ >
			LAB     <- < (![ \t\r\n$] .)+ >
			COMMENT <- '$(' < (!'$)' .)* > '$)'
            INCLUDE <- '$[' < (!'$]' .)* > '$]'
		
			%whitespace <- [ \t\r\n]*
		)";
	}
	Parser(uint label) : parser(mm_syntax()) {

		parser["SYMB"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser["LAB"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser["EXPR"] = [](const peg::SemanticValues& sv) {
			vector<uint> expr;
			expr.reserve(sv.size());
			for (auto& s : sv) {
				if (s.is<uint>()) expr.emplace_back(s.get<uint>());
				else delete s.get<Comment*>();
			}
			return expr;
		};
		parser["CONST"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			c->source->contents.emplace_back(unique_ptr<Const>(new Const(sv[0].get<uint>())));
		};
		parser["DISJ"] = [](const peg::SemanticValues& sv, peg::any& context) {
			context.get<Context*>()->blocks.top().nodes.emplace_back(Disj{sv[0].get<vector<uint>>()});
		};
		parser["ESS"] = [](const peg::SemanticValues& sv, peg::any& context) {
			context.get<Context*>()->blocks.top().nodes.emplace_back(Hyp{sv[0].get<uint>(), sv[1].get<vector<uint>>()});
		};
		parser["FLO"] = [](const peg::SemanticValues& sv, peg::any& context) {
			context.get<Context*>()->blocks.top().nodes.emplace_back(Var{sv[0].get<uint>(), sv[1].get<uint>()});
		};
		parser["AX"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			context.get<Context*>()->source->contents.emplace_back(
				unique_ptr<Assertion>(c->blocks.top().create_assertion(sv[0].get<uint>(), sv[1].get<vector<uint>>(), vector<uint>()))
			);
		};
		parser["TH"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			context.get<Context*>()->source->contents.emplace_back(
				unique_ptr<Assertion>(c->blocks.top().create_assertion(sv[0].get<uint>(), sv[1].get<vector<uint>>(), sv[2].get<vector<uint>>()))
			);
		};
		parser["PROOF"] = [](const peg::SemanticValues& sv) {
			return vector<uint>(std::move(sv.transform<uint>()));
		};
		parser["COMMENT"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			c->source->contents.emplace_back(unique_ptr<Comment>(new Comment(sv.token())));
		};
		parser["INCLUDE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			uint id = Sys::make_name(sv.token());
			c->source->contents.emplace_back(unique_ptr<Import>(new Import(id)));
		};
		parser["BLOCK"].enter = [](peg::any& c) {
			Context* context = c.get<Context*>();
			context->blocks.push(Block(&context->blocks.top()));
		};
		parser["BLOCK"].leave = [](peg::any& c) {
			c.get<Context*>()->blocks.pop();
		};
		parser["SOURCE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			return context.get<Context*>()->source;
		};
		parser["SOURCE"].enter = [] (peg::any& c) {
			c.get<Context*>()->blocks.push(Block());
		};
		parser["BLOCK"].leave = [](peg::any& c) {
			c.get<Context*>()->blocks.pop();
		};

		parser.log = [label](size_t ln, size_t col, const std::string& err_msg) {
			std::stringstream ss;
			ss << "file: " << Lex::toStr(label) << ", line: " << ln << ", col: " << col << ": " << err_msg << std::endl;
			throw Error(ss.str());
		};
	}

	static void parse(uint label) {
		Context* c = new Context();
		try {
			c->source = Sys::mod().math.get<Source>().access(label);
			Parser p(label);
			peg::any ctx(c);
			if (!p.parser.parse<Source*>(c->source->data().c_str(), ctx, c->source)) {
				throw Error("parsing of " + Lex::toStr(label) + " failed");
			}
			c->source->parsed = true;
		} catch(Error& e) {
			delete c;
			throw e;
		}
		delete c;
	}
};

}

void parse() {
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
