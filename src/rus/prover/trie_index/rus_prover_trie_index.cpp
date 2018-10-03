#include "rus_prover_trie_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct NodePair {
	NodePair(unique_ptr<TrieIndex::Node>* t, vector<FlatTerm::Node>::const_iterator e) : trie(t), end(e) { }
	unique_ptr<TrieIndex::Node>* trie;
	vector<FlatTerm::Node>::const_iterator end;
};

void TrieIndex::add(const FlatTerm& t) {
	stack<NodePair> st;
	unique_ptr<Node>* n = &root;
	auto i = t.nodes.begin();
	while (i != t.nodes.end()) {
		st.emplace(n, i->end);
		if (!*n) {
			n->reset(new Node(i->ruleVar));
			n = &(*n)->next;
		} else {
			while (n) {
				if ((*n)->ruleVar == i->ruleVar) {
					n = &(*n)->next;
					break;
				} else {
					n = &(*n)->side;
				}
			}
		}
		++i;
		while (st.top().end == i) {
			(*n)->ends.push_back(st.top().trie->get());
			st.pop();
		}
	}
	(*n)->ind = size++;
}

vector<pair<FlatTerm, uint>> unpack_trie(const unique_ptr<TrieIndex::Node>* n) {
	vector<pair<FlatTerm, uint>> ret;
	while (*n) {
		if ((*n)->next) {
			for (auto p : unpack_trie(&(*n)->next)) {
				p.first.nodes.emplace(p.first.nodes.begin(), (*n)->ruleVar);
				ret.push_back(p);
			}
		}
		if ((*n)->ind != -1) {
			FlatTerm leaf(1);
			leaf.nodes[0].ruleVar = (*n)->ruleVar;
			ret.push_back(pair<FlatTerm, uint>(leaf, (*n)->ind));
		}
		n = &(*n)->side;
	}
	return ret;
}

vector<pair<FlatTerm, uint>> TrieIndex::unpack() const {
	vector<pair<FlatTerm, uint>> ret;
	vector<Node*> branch;
	branch.push_back(root.get());
	while (branch.size()) {
		Node* n = branch.back();
		if (n->ind != -1) {
			FlatTerm ft(branch.size());
			for (uint i = 0; i < branch.size(); ++i) {
				ft.nodes[i].ruleVar = branch[i]->ruleVar;
				for (auto e : n->ends) {
					for (uint j = i + 1; j < branch.size(); ++ j) {
						if (branch[j] == e) {
							ft.nodes[i].end = ft.nodes.begin() + j;
							goto out;
						}
					}
				}
				out:;
			}
			ret.emplace_back(ft, n->ind);
		}
		branch.pop_back();
		if (n->side) {
			branch.push_back(n->side.get());
		}
		if (n->next) {
			branch.push_back(n->next.get());
		}
	}
	return ret;
}

string TrieIndex::show() const {
	string ret;
	for (const auto& p : unpack()) {
		ret += p.first.show() + " --> " + to_string(p.second) + "\n";
	}
	return ret;
}

TrieIndex::Unified TrieIndex::unify(const FlatTerm& t) const {
	Unified ret;
	return ret;
}

}}}}

