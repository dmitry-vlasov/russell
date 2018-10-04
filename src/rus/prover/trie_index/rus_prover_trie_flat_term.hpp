#pragma once

#include "../rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct RuleVar {
	const Rule* rule = nullptr;
	LightSymbol var;
	bool operator == (const RuleVar& rv) const { return rule == rv.rule && var == rv.var; }
	bool operator != (const RuleVar& rv) const { return !operator == (rv); }
	string show() const { return rule ? Lex::toStr(rule->id()) : prover::show(var); }
};

struct FlatTerm {
	struct Node {
		Node() { }
		Node(const RuleVar& rv) : ruleVar(rv) { }
		RuleVar ruleVar;
		vector<Node>::iterator end;
	};
	FlatTerm(uint s) : nodes(s) { }
	FlatTerm(const FlatTerm&);
	vector<Node> nodes;
	string show() const;
};

FlatTerm convert2flatterm(const LightTree&);
LightTree convert2lighttree(const FlatTerm&);

}}}}
