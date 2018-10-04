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
	while (true) {
		if (!*n) {
			n->reset(new Node(i->ruleVar));
		}
		while (!st.empty() && st.top().end == i) {
			(*st.top().trie)->ends.push_back(n->get());
			st.pop();
		}
		if (i != t.nodes.end()) {
			while (*n) {
				if ((*n)->ruleVar == i->ruleVar) {
					st.emplace(n, i->end);
					n = &(*n)->next;
					++i;
					break;
				} else {
					n = &(*n)->side;
				}
			}
		} else {
			break;
		}
	}
	(*n)->ind = size++;
}

static FlatTerm create_flatterm(const vector<TrieIndex::Node*>& branch) {
	FlatTerm ft(branch.size() - 1);
	for (uint i = 0; i < branch.size() - 1; ++i) {
		ft.nodes[i].ruleVar = branch[i]->ruleVar;
		for (auto e : branch[i]->ends) {
			for (uint j = i + 1; j < branch.size(); ++ j) {
				if (branch[j] == e) {
					ft.nodes[i].end = ft.nodes.begin() + j;
					goto out;
				}
			}
		}
		out:;
	}
	return ft;
}

vector<pair<FlatTerm, uint>> TrieIndex::unpack() const {
	vector<pair<FlatTerm, uint>> ret;
	if (root) {
		vector<Node*> branch;
		branch.push_back(root.get());
		while (branch.size()) {
			Node* n = branch.back();
			if (n->ind != -1) {
				ret.emplace_back(create_flatterm(branch), n->ind);
			}
			if (n->next) {
				branch.push_back(n->next.get());
			} else {
				while (true) {
					branch.pop_back();
					if (n->side) {
						branch.push_back(n->side.get());
						break;
					}
					if (branch.empty()) {
						break;
					}
					n = branch.back();
				}
			}
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

