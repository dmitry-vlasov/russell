#include "rus_lookup.hpp"

namespace mdl { namespace rus {

/*
template<class T>
static const Token* find_ref(const User<T>& user, const char* pos) {
	return user.token.includes(pos) ? user.get() : nullptr;
}

static const Token* find_ref(const Symbol& symb, const char* pos) {
	return symb.token()->includes(pos) ? symb.tokenable() : nullptr;
}

static const Token* find_ref(const Vars& vars, const char* pos) {
	if (vars.token.includes(pos)) {
		for (const auto& var : vars.v) {
			if (const Token* tok = find_ref(var, pos)) {
				return tok;
			}
		}
	}
	return nullptr;
}

static const Token* find_ref(const Type* type, const char* pos) {
	if (type->token.includes(pos)) {
		for (const auto& sup : type->sup) {
			if (const Token* tok = find_ref(sup, pos)) {
				return tok;
			}
		}
	}
	return nullptr;
}

static const Token* find_ref(const Rule* rule, const char* pos) {
	if (rule->token.includes(pos)) {
		if (const Token* tok = find_ref(rule->vars, pos)) {
			return tok;
		}
		if (const Token* tok = find_ref(rule->term.type, pos)) {
			return tok;
		}
	}
	return nullptr;
}

static const Token* find_ref(const Assertion* ass, const char* pos) {
	if (ass->token.includes(pos)) {
		if (const Token* tok = find_ref(ass->vars, pos)) {
			return tok;
		}
		for (const auto& hyp : ass->hyps) {
			if (const Token* tok = find_ref(hyp.get()->expr.type, pos)) {
				return tok;
			}
		}
		for (const auto& prop : ass->props) {
			if (const Token* tok = find_ref(prop.get()->expr.type, pos)) {
				return tok;
			}
		}
	}
	return nullptr;
}

static const Token* find_ref(const Step* step, const char* pos) {
	if (step->token.includes(pos)) {
		if (step->kind() == Step::ASS && step->ass_token().includes(pos)) {
			return step->ass();
		}
		if (const Token* tok = find_ref(step->expr.type, pos)) {
			return tok;
		}
	}
	return nullptr;
}

static const Token* find_ref(const Proof::Elem& e, const char* pos) {
	switch (Proof::kind(e)) {
	case Proof::VARS: return find_ref(*Proof::vars(e), pos);
	case Proof::STEP: return find_ref(Proof::step(e), pos);
	case Proof::QED:  return nullptr;
	default: assert(false && "impossible"); return nullptr;
	}
}

static const Token* find_ref(const Proof* proof, const char* pos) {
	if (proof->token.includes(pos)) {
		if (const Token* tok = find_ref(proof->allvars, pos)) {
			return tok;
		}
		for (const auto& e : proof->elems) {
			if (const Token* tok = find_ref(e, pos)) {
				return tok;
			}
		}
	}
	return nullptr;
}

static const Token* find_ref(const Theory* theory, const char* pos);

static const Token* find_ref(const Theory::Node& n, const char* pos) {
	switch(Theory::kind(n)) {
	case Theory::TYPE:    return find_ref(Theory::type(n), pos);
	case Theory::RULE:    return find_ref(Theory::rule(n), pos);
	case Theory::AXIOM:   return find_ref(Theory::axiom(n), pos);
	case Theory::DEF:     return find_ref(Theory::def(n), pos);
	case Theory::THEOREM: return find_ref(Theory::theorem(n), pos);
	case Theory::PROOF:   return find_ref(Theory::proof(n), pos);
	case Theory::THEORY:  return find_ref(Theory::theory(n), pos);
	default : return nullptr;
	}
}

static const Token* find_ref(const Theory* theory, const char* pos) {
	if (theory->token.includes(pos)) {
		for (auto& n : theory->nodes) {
			if (const Token* tok = find_ref(n, pos)) {
				return tok;
			}
		}
	}
	return nullptr;
}

static const Token* find_ref(const Source* source, const char* pos) {
	for (auto& n : source->theory.nodes) {
		if (const Token* tok = find_ref(n, pos)) {
			return tok;
		}
	}
	return nullptr;
}

*/

Return lookup_ref(uint src, uint line, uint col, string what) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	const char* pos = locate_position(line, col, source->data().c_str());
	const Token* tok = nullptr; //find_ref(source, pos);
	if (what == "def")
		return tok ? Return("definition found", tok->str()) : Return("definition not found", false);
	else if (what == "loc")
		return tok ? Return("location found", tok->locate().show()) : Return("definition not found", false);
	else
		return Return("incorrect lookup mode: " + what, false);
}

}}
