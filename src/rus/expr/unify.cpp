#include "rus/ast.hpp"

namespace mdl {
namespace rus {

inline Rule* find_super(const Type* type, const Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

Substitution* unify(const Tree* p, const Tree* q) {
	switch (p->kind) {
	case Tree::VAR: {
		Symbol var = *p->var();
		if (var.type == q->type()) {
			return new Substitution(var, new Tree(*q));
		} else if (Rule* super = find_super(q->type(), var.type)) {
			return new Substitution(var, new Tree(super, {new Tree(*q)}));
		}
		return nullptr;
	}
	case Tree::NODE: {
		if (p->rule() != q->rule()) return nullptr;
		Substitution* sub = new Substitution();
		auto p_ch = p->children().begin();
		auto q_ch = q->children().begin();
		while (p_ch != p->children().end()) {
			if (Substitution* s = unify(p_ch->get(), q_ch->get())) {
				if (!sub->join(s)) {
					delete sub;
					return nullptr;
				}
				delete s;
			} else {
				delete sub;
				return nullptr;
			}
			++p_ch;
			++q_ch;
		}
		return sub;
	}
	default: return nullptr;
	}
}

}} // mdl::rus
