#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

void Index::add(const Term& t, uint val) {
	struct NodePair {
		NodePair(Index::Iterator t, Term::ConstIterator e) : trie(t), end(e) { }
		Index::Iterator trie;
		Term::ConstIterator end;
	};
	stack<NodePair> st;
	Node* n = &root;
	Index::Iterator it;
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

static Term create_flatterm(const vector<Index::Iter>& branch) {
	Term ft(branch.size());
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
	return ft;
}

Term Index::Iter::subTerm(ConstIterator i) const {
	vector<Iter> branch;
	ConstIterator start = i;
	while (i != ConstIterator()) {
		branch.emplace_back(i);
		if (iter_ == i) {
			break;
		}
		i = i->second.parent;
	}
	std::reverse(branch.begin(), branch.end());
	return create_flatterm(branch);
}

vector<pair<Term, uint>> Index::unpack() const {
	vector<pair<Term, uint>> ret;
	vector<Iter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			Iter n = branch.back();
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

string Index::show() const {
	string ret;
	for (const auto& p : unpack()) {
		ret += p.first.show() + " --> " + to_string(p.second) + "\n";
	}
	return ret;
}

string Index::show_pointers() const {
	vector<pair<vector<Iter>, uint>> vect;
	vector<Iter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			Iter n = branch.back();
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


vector<pair<Term, uint>> Index::unpack(const Node& root) {
	vector<pair<Term, uint>> ret;
	vector<Iter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			Iter n = branch.back();
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

string Index::show(const Node& root) {
	string ret;
	for (const auto& p : unpack(root)) {
		ret += p.first.show() + " --> " + to_string(p.second) + "\n";
	}
	return ret;
}

string Index::show_pointers(const Node& root) {
	vector<pair<vector<Iter>, uint>> vect;
	vector<Iter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			Iter n = branch.back();
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

uint Index::totalNodes() const {
	uint ret = 0;
	vector<Iter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			Iter n = branch.back();
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
