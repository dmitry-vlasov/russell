#pragma once

#include <rus_ast.hpp>

namespace mdl { namespace rus {

template<class T>
static T* find_obj(Vars& vars, const char* pos) {
	return vars.token.includes(pos) ? dynamic_cast<T*>(&vars) : nullptr;
}

template<class T>
static T* find_obj(Expr& expr, const char* pos) {
	return expr.token.includes(pos) ? dynamic_cast<T*>(&expr) : nullptr;
}

template<class T>
static T* find_obj(Type* type, const char* pos) {
	return type->token.includes(pos) ? dynamic_cast<T*>(type) : nullptr;
}

template<class T>
static T* find_obj(Rule* rule, const char* pos) {
	if (rule->token.includes(pos)) {
		if (T* t = find_obj<T>(rule->vars, pos)) {
			return t;
		}
		if (T* t = find_obj<T>(rule->term, pos)) {
			return t;
		}
		return dynamic_cast<T*>(rule);
	}
	return nullptr;
}

template<class T>
static T* find_obj(Hyp* hyp, const char* pos) {
	if (hyp->token.includes(pos)) {
		if (T* t = find_obj<T>(hyp->expr, pos)) {
			return t;
		}
		return dynamic_cast<T*>(hyp);
	}
	return nullptr;
}

template<class T>
static T* find_obj(Prop* prop, const char* pos) {
	if (prop->token.includes(pos)) {
		if (T* t = find_obj<T>(prop->expr, pos)) {
			return t;
		}
		return dynamic_cast<T*>(prop);
	}
	return nullptr;
}

template<class T>
static T* find_obj(Assertion* ass, const char* pos) {
	if (ass->token.includes(pos)) {
		if (T* t = find_obj<T>(ass->vars, pos)) {
			return t;
		}
		for (auto& hyp : ass->hyps) {
			if (T* t = find_obj<T>(hyp.get(), pos)) {
				return t;
			}
		}
		if (T* t = find_obj<T>(ass->prop.get(), pos)) {
			return t;
		}
		return dynamic_cast<T*>(ass);
	}
	return nullptr;
}

template<class T>
static T* find_obj(Step* step, const char* pos) {
	if (step->token.includes(pos)) {
		if (T* t = find_obj<T>(step->expr, pos)) {
			return t;
		}
		return dynamic_cast<T*>(step);
	}
	return nullptr;
}

template<class T>
static T* find_obj(Qed* qed, const char* pos) {
	return qed->token.includes(pos) ? dynamic_cast<T*>(qed) : nullptr;
}

template<class T>
static T* find_obj(Proof* proof, const char* pos) {
	if (proof->token.includes(pos)) {
		if (T* t = find_obj<T>(proof->vars, pos)) {
			return t;
		}
		if (T* t = find_obj<T>(proof->qed, pos)) {
			return t;
		}
		for (auto& step : proof->steps) {
			if (T* t = find_obj<T>(step.get(), pos)) {
				return t;
			}
		}
		return dynamic_cast<T*>(proof);
	}
	return nullptr;
}

template<class T>
static T* find_obj(Import* import, const char* pos) {
	return import->token.includes(pos) ? dynamic_cast<T*>(import) : nullptr;
}

template<class T>
static T* find_obj(Comment* comment, const char* pos) {
	return comment->token.includes(pos) ? dynamic_cast<T*>(comment) : nullptr;
}

template<class T>
static T* find_obj(Constant* cons, const char* pos) {
	return cons->token.includes(pos) ? dynamic_cast<T*>(cons) : nullptr;
}

template<class T>
static T* find_obj(Theory* theory, const char* pos);

template<class T>
static T* find_obj(Theory::Node& n, const char* pos) {
	switch(Theory::kind(n)) {
	case Theory::CONSTANT: return find_obj<T>(Theory::constant(n), pos);
	case Theory::TYPE:     return find_obj<T>(Theory::type(n), pos);
	case Theory::RULE:     return find_obj<T>(Theory::rule(n), pos);
	case Theory::AXIOM:    return find_obj<T>(Theory::axiom(n), pos);
	case Theory::DEF:      return find_obj<T>(Theory::def(n), pos);
	case Theory::THEOREM:  return find_obj<T>(Theory::theorem(n), pos);
	case Theory::THEORY:   return find_obj<T>(Theory::theory(n), pos);
	case Theory::COMMENT:  return find_obj<T>(Theory::comment(n), pos);
	default : return nullptr;
	}
}

template<class T>
static T* find_obj(Theory* theory, const char* pos) {
	if (theory->token.includes(pos)) {
		for (auto& n : theory->nodes) {
			if (T* t = find_obj<T>(n, pos)) {
				return t;
			}
		}
		return dynamic_cast<T*>(theory);
	}
	return nullptr;
}

template<class T>
T* find_obj(Source* source, const char* pos) {
	for (auto& n : source->theory.nodes) {
		if (T* t = find_obj<T>(n, pos)) {
			return t;
		}
	}
	return nullptr;
}

}}
