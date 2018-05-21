#include <rus_ast.hpp>

namespace mdl {
namespace rus {

Rule* find_super(const Type* type, const Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second.get();
	else
		return nullptr;
}

Substitution unify_forth(const Tree* p, const Tree* q) {
	switch (p->kind()) {
	case Tree::VAR: {
		Symbol var = *p->var();
		if (var.type() == q->type())
			return Substitution(var, *q);
		else if (Rule* super = find_super(q->type(), var.type()))
			return Substitution(var, Tree(super->id(), {new Tree(*q)}));
		else
			return Substitution(false);
	}
	case Tree::NODE: {
		if (p->rule() != q->rule()) return Substitution(false);
		Substitution sub;
		auto p_ch = p->children().begin();
		auto q_ch = q->children().begin();
		while (p_ch != p->children().end()) {
			if (Substitution s = std::move(unify_forth(p_ch->get(), q_ch->get()))) {
				if (!sub.join(s)) return sub;
			} else {
				return sub;
			}
			++p_ch;
			++q_ch;
		}
		return sub;
	}
	default: return Substitution(false);
	}
}

}} // mdl::rus
