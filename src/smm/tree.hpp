#pragma once

#include "smm/globals.hpp"

namespace mdl { namespace smm {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;
typedef map<Symbol, Expr> Subst;

inline string show (const Subst& subst) {
	string str;
	for (auto it : subst)
		str += show_sy(it.first) + " = > " + show_ex(it.second) + "\n";
	return str;
}
Expr apply(const Subst& sub, const Expr& expr);

Proof* to_tree(const Proof* pr);
Proof* to_rpn(const Proof* pr);
void transform(Proof* proof, const Transform& trans, bool forward = true);
Expr eval(Proof* proof);

}} // mdl::smm
