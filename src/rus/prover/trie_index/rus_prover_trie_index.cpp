#include "rus_prover_trie_index.hpp"

#include "rus_prover_trie_unify_step.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_trie_index = false;
bool debug_trie_profile = false;
bool debug_trie_aftermath = false;

void TrieIndex::add(const FlatTerm& t, uint val) {
	struct NodePair {
		NodePair(TrieIndex::Iterator t, FlatTerm::ConstIterator e) : trie(t), end(e) { }
		TrieIndex::Iterator trie;
		FlatTerm::ConstIterator end;
	};
	stack<NodePair> st;
	Node* n = &root;
	TrieIndex::Iterator it;
	for (auto i = t.nodes.begin(); i != t.nodes.end(); ++i) {
		auto p = it;
		auto ni = n->nodes.emplace(i->ruleVar, Node()).first;
		n = &ni->second;
		it = ni;
		it->second.parent = p;
		st.emplace(ni, i->end);
		while (!st.empty() && st.top().end == i) {
			st.top().trie->second.ends.insert(ni);
			st.pop();
		}
	}
	n->inds.push_back(val == -1 ? size : val);
	++size;
}

static FlatTerm create_flatterm(const vector<TrieIndex::TrieIter>& branch) {
	FlatTerm ft(branch.size());
	for (uint i = 0; i < branch.size(); ++i) {
		ft.nodes[i].ruleVar = branch[i].iter()->first;
		for (auto end : branch[i].iter()->second.ends) {
			for (uint j = i; j < branch.size(); ++ j) {
				if (branch[j].iter() == end) {
					ft.nodes[i].end = ft.nodes.begin() + j;
					goto out;
				}
			}
		}
		out:;
	}
	try {
		ft.verify();
	} catch (Error& err) {
		cout << "at : create_flatterm" << endl;
		for (const auto& i : branch) {
			cout << i.ruleVar().show() << " ";
		}
		cout << endl;
		throw err;
	}
	return ft;
}

bool debug_trie_subterm = false;

FlatTerm TrieIndex::TrieIter::subTerm(ConstIterator i) const {
	vector<TrieIter> branch;
	ConstIterator start = i;
	while (i != ConstIterator()) {
		branch.emplace_back(i);
		if (iter_ == i) {
			break;
		}
		i = i->second.parent;
	}
	std::reverse(branch.begin(), branch.end());

	if (debug_trie_subterm) {
		cout << "SUBTERM BRANCH:" << endl;
		for (auto i : branch) {
			cout << i.ruleVar().show() << ", ";
		}
		cout << endl;
	}

	try {
		auto ret = create_flatterm(branch);
		//if (debug_trie_index) {
		//	cout << "SUBTERM: " << ret.show() << endl;
		//}
		return ret;
	} catch (Error& err) {
		cout << "start: " << start->first.show() << " - " << (void*)&*start << endl;
		cout << "this: " << ruleVar().show() << " - " << (void*)&*iter_ << endl;
		i = start;
		while (i != ConstIterator()) {
			cout << "i: " << i->first.show() << " - " << (void*)&*i << endl;
			if (iter_ == i) {
				break;
			}
			if (i->second.parent == ConstIterator()) {
				cout << endl << endl << "FUCK" << endl;
				cout << TrieIndex::show_pointers(i->second) << endl;
			}
			i = i->second.parent;
		}
		throw err;
	}
}

vector<pair<FlatTerm, uint>> TrieIndex::unpack() const {
	vector<pair<FlatTerm, uint>> ret;
	vector<TrieIter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			TrieIter n = branch.back();
			for (uint ind : n.iter()->second.inds) {
				ret.emplace_back(create_flatterm(branch), ind);
			}
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
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

string TrieIndex::show_pointers() const {
	vector<pair<vector<TrieIter>, uint>> vect;
	vector<TrieIter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			TrieIter n = branch.back();
			for (uint ind : n.iter()->second.inds) {
				vect.emplace_back(branch, ind);
			}
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
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
	ostringstream oss;
	oss << "ROOT: " << (void*)&root << endl;
	for (const auto& p : vect) {
		for (const auto& i : p.first) {
			oss << i.ruleVar().show() << "=(" << (void*)&*i.iter() << ") ";
		}
		oss << " --> " << p.second << "\n";
	}
	return oss.str();
}


vector<pair<FlatTerm, uint>> TrieIndex::unpack(const Node& root) {
	vector<pair<FlatTerm, uint>> ret;
	vector<TrieIter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			TrieIter n = branch.back();
			for (uint ind : n.iter()->second.inds) {
				ret.emplace_back(create_flatterm(branch), ind);
			}
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
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

string TrieIndex::show(const Node& root) {
	string ret;
	for (const auto& p : unpack(root)) {
		ret += p.first.show() + " --> " + to_string(p.second) + "\n";
	}
	return ret;
}

string TrieIndex::show_pointers(const Node& root) {
	vector<pair<vector<TrieIter>, uint>> vect;
	vector<TrieIter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			TrieIter n = branch.back();
			for (uint ind : n.iter()->second.inds) {
				vect.emplace_back(branch, ind);
			}
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
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
	ostringstream oss;
	oss << "RELATIVE ROOT: " << (void*)&root << endl;
	for (const auto& p : vect) {
		for (const auto& i : p.first) {
			oss << i.ruleVar().show() << "=(" << (void*)&*i.iter() << ") ";
		}
		oss << " --> " << p.second << "\n";
	}
	return oss.str();
}



uint TrieIndex::totalNodes() const {
	uint ret = 0;
	vector<TrieIter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			TrieIter n = branch.back();
			ret += n.iter()->second.inds.size();
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
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

}}}}

