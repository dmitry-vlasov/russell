#include <rus_ast.hpp>

namespace mdl {
namespace rus {

Rule* find_super(const Type* type, const Type* super) {
	auto it = type->supers.find(super);
	return it != type->supers.end() ? it->second.get() : nullptr;
}

Substitution unify_forth(const Tree* p, const Tree* q) {
	switch (p->kind()) {
	case Tree::VAR: {
		const Var& var = dynamic_cast<const VarTree*>(p)->var;
		if (var.type() == q->type()) {
			return Substitution(var.lit(), *q);
		} else if (Rule* super = find_super(q->type(), var.type())) {
			return Substitution(var.lit(), RuleTree(super->id(), q->clone()));
		} else {
			return Substitution(false);
		}
	}
	case Tree::RULE: {
		const RuleTree* pr = dynamic_cast<const RuleTree*>(p);
		const RuleTree* qr = dynamic_cast<const RuleTree*>(q);
		if (!qr || pr->rule.id() != qr->rule.id()) {
			return Substitution(false);
		}
		Substitution sub;
		auto p_ch = pr->children.begin();
		auto q_ch = qr->children.begin();
		while (p_ch != pr->children.end()) {
			if (Substitution s = unify_forth(p_ch->get(), q_ch->get())) {
				if (!sub.join(std::move(s))) {
					return sub;
				}
			} else {
				return sub;
			}
			++p_ch;
			++q_ch;
		}
		return sub;
	}
	default: throw Error("impossible switch case");
	}
}

}} // mdl::rus
