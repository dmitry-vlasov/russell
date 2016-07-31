#include "rus/globals.hpp"

namespace mdl {
namespace rus {

template<typename T>
inline Type* type(const T& t) {
	return t.rule ? t.rule->type : t.first->symb.type;
}

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}


sub::Expr* unify(const term::Expr& p, const term::Expr& q) {
	if (p.isvar()) {
		Symbol var = p.first->symb;
		if (var.type == type(q)) {
			sub::Expr* s = new sub::Expr();
			s->sub[var] = q;
			return s;
		} else if (Rule* super = find_super(type(q), const_cast<Type*>(var.type))) {
			sub::Expr* s = new sub::Expr();
			s->sub[var] = term::Expr(q.first, q.last, super);
			s->sub[var].children.push_back(q);
			return s;
		}
		return nullptr;
	} else {
		if (p.rule != q.rule) {
			return nullptr;
		}
		sub::Expr* sub = new sub::Expr();
		auto p_ch = p.children.begin();
		auto q_ch = q.children.begin();
		while (p_ch != p.children.end()) {
			if (sub::Expr* s = unify(*p_ch, *q_ch)) {
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
}

}} // mdl::rus
