#pragma once

#include "mm/ast.hpp"

namespace mdl { namespace mm {

typedef Map<uint, uint> Perm;
typedef Map<uint, Perm> Transform;

Proof* to_tree(const Proof* pr);
Proof* to_rpn(const Proof* pr);
void transform(Proof* proof, const Transform& trans, bool forward = true);
void reduce(Proof*& pr, const Set<uint>& red);

}}
