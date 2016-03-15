#pragma once

#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;

//ostream& operator << (ostream& os, const tree::Perm&);

Proof* to_tree(const Proof* pr);
Proof* to_rpn(const Proof* pr);
void transform(Proof* proof, const Transform& trans, bool forward = true);

}} // mdl::smm
