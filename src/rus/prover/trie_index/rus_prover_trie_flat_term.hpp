#pragma once

#include "../rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct RuleVar {
	const Rule* rule = nullptr;
	LightSymbol var;
	bool operator == (const RuleVar& rv) const { return rule == rv.rule && var == rv.var; }
	bool operator != (const RuleVar& rv) const { return !operator == (rv); }
	string show() const { return rule ? Lex::toStr(rule->id()) : prover::show(var); }
	bool isVar() const  { return var.is_def(); }
	bool isRule() const { return rule; }
};

struct FlatTerm {
	enum Kind { RULE, VAR };
	struct Node {
		Node() { }
		Node(const RuleVar& rv) : ruleVar(rv) { }
		Node(const Node& n) : ruleVar(n.ruleVar) { }
		Node(Node&&) = delete;
		bool operator == (const Node& n) const { return ruleVar == n.ruleVar; }
		bool operator != (const Node& n) const { return ruleVar != n.ruleVar; }
		Node& operator = (const Node& n) { ruleVar = n.ruleVar; return *this;}
		Node& operator = (Node&&) = delete;
		RuleVar ruleVar;
		vector<Node>::iterator end;
	};
	FlatTerm(uint s) : nodes(s) { }
	FlatTerm(const FlatTerm&);
	FlatTerm(FlatTerm&&) = default;

	bool operator == (const FlatTerm& t) const { return nodes == t.nodes; }
	bool operator != (const FlatTerm& t) const { return nodes != t.nodes; }

	FlatTerm& operator = (const FlatTerm&);
	FlatTerm& operator = (FlatTerm&&) = default;

	Kind kind() const {
		return (nodes.size() == 1 && nodes[0].ruleVar.isVar()) ? VAR : RULE;
	}
	LightSymbol var() const { assert(kind() == VAR); return nodes[0].ruleVar.var; }
	const Rule* rule() const { assert(kind() == RULE); return nodes[0].ruleVar.rule; }
	bool empty() const { return !nodes.size(); }
	uint len() const { return nodes.size(); }

	vector<Node> nodes;
	string show() const;
};

FlatTerm convert2flatterm(const LightTree&);
LightTree convert2lighttree(const FlatTerm&);

}}}}
