#pragma once

#include "mm/ast.hpp"

namespace mdl { namespace mm {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;

Tree* to_tree(const Proof* pr);
Proof* to_proof(const Tree* pr);
void transform(Tree* tree, Transform& trans, bool forward = true);
Tree* reduce(Tree* t, const set<uint>& red);

}}
