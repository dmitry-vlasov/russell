#include "mm_ast.hpp"
#include "peglib.h"

namespace mdl { namespace mm {

Var* VarDecl::make(bool inner, uint index) const {
	return new mm::Var(inner, index, label, type, var);
}

namespace parser {

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
	mm::Hyp* make(uint index, const set<uint>& vars) const {
		mm::Hyp* h = new mm::Hyp(index, label);
		h->expr.reserve(expr.size());
		for (uint s : expr) {
			h->expr.emplace_back(s, vars.find(s) != vars.end());
		}
		return h;
	}
};

struct Block {
	typedef variant<Disj, Hyp, VarDecl> Node;

	Block(Block* p = nullptr) : parent(p) { }

	static vector<const VarDecl*> create_initial_vars() {
		vector<const VarDecl*> vars;
		for (const VarDecl& decl : Sys::get().math.decls) {
			vars.push_back(&decl);
		}
		return vars;
	}

	Assertion* create_assertion(uint label, const vector<uint>& expr, const vector<uint>& proof, const Token& token) {
		static vector<const VarDecl*> initial_vars = create_initial_vars();

		vector<const VarDecl*> all_floatings = gather<VarDecl>(initial_vars);
		vector<const Hyp*>     essentials = gather<Hyp>();
		vector<const Disj*>    all_disjointed = gather<Disj>();

		// Gather all symbols, used in assertion hypotheses and statement (header).
		set<uint> ass_symbs;
		gather_symbs(ass_symbs, expr);
		for (const Hyp* ess : essentials) {
			gather_symbs(ass_symbs, ess->expr);
		}

		// Collect floatings, which refer to assertion, and all variables.
		vector<const VarDecl*> floatings;
		set<uint> flo_vars;
		map<uint, const VarDecl*> flo_map;
		for (const VarDecl* flo : all_floatings) {
			flo_map[flo->label] = flo;
			if (ass_symbs.find(flo->var) != ass_symbs.end()) {
				if (flo_vars.find(flo->var) != flo_vars.end()) {
					for (auto it = floatings.begin(); it != floatings.end(); ++ it) {
						if ((*it)->var == flo->var) {
							floatings.erase(it);
							break;
						}
					}
				}
				floatings.push_back(flo);
				flo_vars.insert(flo->var);
			}
		}

		// Collect inner variables from proof.
		set<uint> inner_vars;
		for (uint l : proof) {
			auto flo_it = flo_map.find(l);
			if (flo_it != flo_map.end()) {
				const VarDecl* flo = (*flo_it).second;
				if (ass_symbs.find(flo->var) == ass_symbs.end()) {
					inner_vars.insert(flo->var);
				}
			}
		}

		// Collect inner proof floating declarations.
		vector<const VarDecl*> inners;
		for (const VarDecl* flo : all_floatings) {
			if (inner_vars.find(flo->var) != inner_vars.end()) {
				inners.push_back(flo);
			}
		}

		// Gather all assertion vars;
		set<uint> vars(flo_vars);
		for (uint i : inner_vars) {
			vars.insert(i);
		}

		Assertion* ass = new Assertion(label, token);
		ass->vars.vars.reserve(vars.size());
		for (uint v : vars) ass->vars.vars.emplace_back(v);

		// Make final set of disjointeds.
		ass->disj.vect.reserve(all_disjointed.size());
		for (const Disj* disj : all_disjointed) {
			vector<uint>* d = disj->make(vars);
			if (d->size() > 1) {
				ass->disj.vect.emplace_back(disj->make(vars));
			} else {
				delete d;
			}
		}

		// Make final set of essentials.
		uint i = 0;
		map<uint, mm::Hyp*> hyps_map;
		map<uint, mm::Var*> vars_map;
		ass->hyps.reserve(essentials.size());
		for (const Hyp* hyp : essentials) {
			ass->hyps.emplace_back(hyp->make(i++, vars));
			hyps_map[hyp->label] = ass->hyps.back().get();
		}

		// Make final set of floatings.
		ass->outerVars.reserve(floatings.size());
		i = 0;
		for (const VarDecl* flo : floatings) {
			ass->outerVars.emplace_back(flo->make(false, i++));
			vars_map[flo->label] = ass->outerVars.back().get();
		}

		// Make final set of inners.
		ass->innerVars.reserve(inners.size());
		for (const VarDecl* flo : inners) {
			ass->innerVars.emplace_back(flo->make(true, i++));
			vars_map[flo->label] = ass->innerVars.back().get();
		}

		ass->expr.reserve(expr.size());
		for (uint s : expr) {
			ass->expr.emplace_back(s, vars.find(s) != vars.end());
		}

		ass->proof.refs.reserve(proof.size());
		for (uint r : proof) {
			auto h = hyps_map.find(r);
			if (h != hyps_map.end()) {
				ass->proof.refs.emplace_back((*h).second);
				continue;
			}
			auto v = vars_map.find(r);
			if (v != vars_map.end()) {
				ass->proof.refs.emplace_back((*v).second);
				continue;
			}
			ass->proof.refs.emplace_back(r);
		}
		return ass;
	}

	template<class N>
	vector<const N*> gather(const vector<const N*>& initial = vector<const N*>()) const {
		vector<const N*> vect;
		if (parent) {
			vect = std::move(parent->gather<N>(initial));
		} else {
			vect = initial;
		}
		for (const auto& n : nodes) {
			if (std::holds_alternative<N>(n)) {
				vect.emplace_back(&std::get<N>(n));
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
		Source*      source = nullptr;
		bool         in_expr = false;

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
			VAR     <-      '$v' EXPR '$.'
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
				if (s.is_defined()) {
					expr.emplace_back(s.get<uint>());
				}
			}
			return expr;
		};
		parser["EXPR"].enter = [](peg::any& c) { c.get<Context*>()->in_expr = true; };
		parser["EXPR"].leave = [](peg::any& c) { c.get<Context*>()->in_expr = false; };
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
			Context* c = context.get<Context*>();
			if (c->blocks.top().parent) {
				c->blocks.top().nodes.emplace_back(VarDecl{sv[0].get<uint>(), sv[1].get<uint>(), sv[2].get<uint>()});
			}
		};
		parser["AX"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			context.get<Context*>()->source->contents.emplace_back(
				unique_ptr<Assertion>(c->blocks.top().create_assertion(sv[0].get<uint>(), sv[1].get<vector<uint>>(), vector<uint>(), c->token(sv)))
			);
		};
		parser["TH"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			context.get<Context*>()->source->contents.emplace_back(
				unique_ptr<Assertion>(c->blocks.top().create_assertion(sv[0].get<uint>(), sv[1].get<vector<uint>>(), sv[2].get<vector<uint>>(), c->token(sv)))
			);
		};
		parser["PROOF"] = [](const peg::SemanticValues& sv) {
			return vector<uint>(std::move(sv.transform<uint>()));
		};
		parser["COMMENT"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			if (!c->in_expr) {
				c->source->contents.emplace_back(unique_ptr<Comment>(new Comment(sv.token())));
			}
		};
		parser["INCLUDE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context* c = context.get<Context*>();
			uint id = Sys::make_name(sv.token());
			c->source->contents.emplace_back(unique_ptr<Import>(new Import(id)));
#ifndef PARALLEL_PARSE
			if (!Sys::get().math.get<Source>().access(id)->parsed) parse(id);
#endif
		};
		parser["BLOCK"].enter = [](peg::any& c) {
			Context* context = c.get<Context*>();
			context->blocks.push(Block(context->blocks.empty() ? nullptr : &context->blocks.top()));
		};
		parser["BLOCK"].leave = [](peg::any& c) {
			c.get<Context*>()->blocks.pop();
		};
		parser["SOURCE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			return context.get<Context*>()->source;
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

} // namespace parser

using parser::Parser;

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
