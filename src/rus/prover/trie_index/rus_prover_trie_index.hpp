#pragma once

#include "rus_prover_trie_flatterm.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct TrieIndex {
	struct Node {
		Node(const RuleVar& rv) : ruleVar(rv) { }
		RuleVar ruleVar;
		uint ind = -1;
		unique_ptr<Node> next;
		unique_ptr<Node> side;
		vector<Node*> ends;
	};

	typedef map<uint, Subst> Unified;

	void add(const FlatTerm& t);
	Unified unify(const FlatTerm&) const;
	vector<pair<FlatTerm, uint>> unpack() const;
	string show() const;

	uint size = 0;
	unique_ptr<Node> root;
};

}}}}
