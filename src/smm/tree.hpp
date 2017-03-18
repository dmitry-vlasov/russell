#pragma once

#include "smm/ast.hpp"

namespace mdl { namespace smm {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;
typedef map<Symbol, Vect> Subst;

inline string show (const Subst& subst) {
	string str;
	for (auto it : subst)
		str += show_sy(it.first) + " = > " + show_ex(it.second) + "\n";
	return str;
}
Vect apply(const Subst& sub, const Vect& expr);

Proof* to_tree(const Proof* pr);
Proof* to_rpn(const Proof* pr);
void transform(Proof* proof, const Transform& trans, bool forward = true);
Vect eval(Proof* proof);
Vect eval(Ref*);

}} // mdl::smm
