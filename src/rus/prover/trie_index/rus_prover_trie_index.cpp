#include "rus_prover_trie_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct NodePair {
	NodePair(TrieIndex::Node* t, vector<FlatTerm::Node>::const_iterator e) : trie(t), end(e) { }
	TrieIndex::Node* trie;
	vector<FlatTerm::Node>::const_iterator end;
};

void TrieIndex::add(const FlatTerm& t) {

	cout << "ADDING: " << t.show() << endl;

	stack<NodePair> st;
	Node* n = &root;
	for (auto i = t.nodes.begin(); i != t.nodes.end(); ++i) {
		while (!st.empty() && st.top().end == i) {
			st.top().trie->ends.push_back(n);
			st.pop();
		}
		n = &n->nodes[i->ruleVar];
		st.emplace(n, i->end);
	}
	n->inds.push_back(size++);


	cout << "THIS: " << endl;
	cout << show() << endl;
	static int c = 0;
	if (c ++ == 128) {
		exit(0);
	}
}

struct UnpackPair {
	UnpackPair(TrieIndex::ConstIterator i, TrieIndex::ConstIterator e) : iter(i), end(e) { }
	bool isEnd() const { return iter == end; }
	UnpackPair side() { return UnpackPair(++iter, end); }
	TrieIndex::ConstIterator iter;
	TrieIndex::ConstIterator end;
};

static FlatTerm create_flatterm(const vector<UnpackPair>& branch) {
	FlatTerm ft(branch.size() - 1);
	for (uint i = 0; i < branch.size() - 1; ++i) {
		ft.nodes[i].ruleVar = branch[i].iter->first;
		for (auto e : branch[i].iter->second.ends) {
			for (uint j = i + 1; j < branch.size(); ++ j) {
				if (&branch[j].iter->second == e) {
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
	vector<UnpackPair> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root.nodes.begin(), root.nodes.end());
		while (branch.size()) {
			UnpackPair n = branch.back();
			for (uint ind :  n.iter->second.inds) {
				ret.emplace_back(create_flatterm(branch), ind);
			}
			if (n.iter->second.nodes.size()) {
				branch.emplace_back(n.iter->second.nodes.begin(), n.iter->second.nodes.end());
			} else {
				while (true) {
					branch.pop_back();
					UnpackPair m = n.side();
					if (!m.isEnd()) {
						branch.push_back(m);
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

