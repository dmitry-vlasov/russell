#include "rus/globals.hpp"

namespace mdl {
namespace rus {

inline Rule* find_super(const Type* type, const Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

Substitution* unify(const term::Expr* p, const term::Expr* q) {
	switch (p->kind) {
	case term::Expr::VAR: {
		Symbol var = *p->var();
		if (var.type == q->type()) {
			Substitution* s = new Substitution();
			s->sub[var] = new term::Expr(*q);
			return s;
		} else if (Rule* super = find_super(q->type(), var.type)) {
			Substitution* s = new Substitution();
			s->sub[var] = new term::Expr(super);
			s->sub[var]->children().push_back(new term::Expr(*q));
			return s;
		}
		return nullptr;
	}
	case term::Expr::NODE: {
		if (p->rule() != q->rule()) return nullptr;
		Substitution* sub = new Substitution();
		auto p_ch = p->children().begin();
		auto q_ch = q->children().begin();
		while (p_ch != p->children().end()) {
			if (Substitution* s = unify(*p_ch, *q_ch)) {
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
