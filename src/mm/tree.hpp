#pragma once

#include "mm/ast.hpp"

namespace mdl { namespace mm {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;

Proof* to_tree(const Proof* pr);
Proof* to_rpn(const Proof* pr);
void transform(Proof* proof, const Transform& trans);

inline uint ass_label(const Node& node) {
	return node.type == Node::AXIOM ? node.val.ax->label : node.val.th->label;
}

inline Expr& ass_expr(const Node& node) {
	return node.type == Node::AXIOM ? node.val.ax->expr : node.val.th->expr;
}

inline const Proof* ass_proof(const Node& node) {
	return node.type == Node::AXIOM ? nullptr : node.val.th->proof;
}

inline uint hyp_label(const Node& node) {
	return node.type == Node::FLOATING ? node.val.flo->label : node.val.ess->label;
}

inline uint& ass_arity(const Node& node) {
	return node.type == Node::AXIOM ? node.val.ax->arity : node.val.th->arity;
}

}}
