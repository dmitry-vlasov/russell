#include "rus_prover_trie_index.hpp"
#include "rus_prover_trie_unify.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_trie_index = false;

void TrieIndex::add(const FlatTerm& t, uint val) {
	struct NodePair {
		NodePair(TrieIndex::Iterator t, FlatTerm::ConstIterator e) : trie(t), end(e) { }
		TrieIndex::Iterator trie;
		FlatTerm::ConstIterator  end;
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

FlatTerm TrieIndex::TrieIter::subTerm(ConstIterator i) const {
	vector<TrieIter> branch;
	ConstIterator start = i;
	while (i != ConstIterator()) {
		branch.emplace_back(i);
		if (iter_ == i) {
			break;
		}
		i = i->second.parent;
		/*if (i == ConstIterator()) {
			cout << "i == ConstIterator() " << endl;
			cout << "start: " << start->first.show() << " - " << (void*)&*start << endl;
			cout << "this: " << ruleVar().show() << " - " << (void*)&*iter_ << endl;
			i = start;
			while (i != ConstIterator()) {
				cout << "i: " << i->first.show() << " - " << (void*)&*i << endl;
				if (iter_ == i) {
					break;
				}
				i = i->second.parent;
			}
			std::reverse(branch.begin(), branch.end());
			cout << "SUBTERM: " << create_flatterm(branch).show() << endl;
			throw Error("TrieIndex::TrieIter::subTerm");
		}*/
	}
	std::reverse(branch.begin(), branch.end());
	try {
		auto ret = create_flatterm(branch);
		if (debug_trie_index) {
			cout << "SUBTERM: " << ret.show() << endl;
		}
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
		//std::reverse(branch.begin(), branch.end());
		//cout << "SUBTERM: " << create_flatterm(branch).show() << endl;
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

struct UnifyIter {
	UnifyIter(TrieIndex::TrieIter i1, FlatTerm::TermIter i2, const FlatSubst& ps = FlatSubst(), const FlatSubst& s = FlatSubst()) :
		trieIter(i1), termIter(i2), parentSub(ps), sub(s) { }
	UnifyIter(TrieIndex::TrieIter i1, FlatTerm::TermIter i2, FlatSubst&& ps, FlatSubst&& s) :
		trieIter(i1), termIter(i2), parentSub(std::move(ps)), sub(std::move(s)) { }
	UnifyIter(const UnifyIter&) = default;
	UnifyIter& operator = (const UnifyIter&) = default;
	UnifyIter side() {
		return UnifyIter(trieIter.side(), termIter, parentSub, parentSub);
	}
	UnifyIter next() const { return UnifyIter(trieIter.next(), termIter.next(), sub, sub); }
	bool isNextEnd() const { return sub.ok ? (trieIter.isNextEnd() || termIter.isNextEnd()) : true; }
	bool isTermEnd() const { return sub.ok ? (trieIter.isNextEnd() && termIter.isNextEnd()) : true; }
	bool isSideEnd() const { return sub.ok ? (trieIter.isSideEnd() && termIter.isSideEnd()) : true; }
	bool equals() const { return trieIter.iter()->first == termIter.iter()->ruleVar; }

	vector<UnifyIter> unify() const {
		vector<UnifyIter> ret;
		if (equals()) {
			if (debug_trie_index) {
				cout << "equals" << endl;
			}
			ret.emplace_back(*this);
		} else {
			if (trieIter.isVar()) {
				for (const auto& p : termIter.subTerms()) {
					FlatSubst s = unify_step(sub, {trieIter.var()}, p.first);
					if (s.ok) {
						ret.emplace_back(trieIter, p.second, parentSub, s);
					}
				}
			} else if (termIter.isVar()) {
				for (const auto& p : trieIter.subTerms()) {
					FlatSubst s = unify_step(sub, {termIter.var()}, p.first);
					if (s.ok) {
						ret.emplace_back(p.second, termIter, parentSub, s);
					}
				}
			}
		}
		return ret;
	}

	string show(bool full = false) const {
		string ret;
		ret += "trie: " + trieIter.show(full) + "\n";
		ret += "term: " + termIter.show(full) + "\n";
		return ret;
	}
	string showBranch() const {
		string ret;
		ret += "trie: " + trieIter.showBranch() + "\n";
		ret += "term: " + termIter.showBranch() + "\n";
		return ret;
	}
	TrieIndex::TrieIter trieIter;
	FlatTerm::TermIter  termIter;
	FlatSubst parentSub;
	FlatSubst sub;
};

string showBranches(const vector<UnifyIter>& branch) {
	string ret;
	ret += "trie: \n";
	for (auto i : branch) {
		ret += i.showBranch() + "\n";
	}
	ret += "==================\n";
	return ret;
}

TrieIndex::Unified TrieIndex::unify(const FlatTerm& t) const {
	static uint c = 0;
	Unified ret;
	vector<UnifyIter> branch;
	branch.reserve(256);
	//cout << "entering TrieIndex::unify ... " << ++c << flush;
	//if (c == 3) {
	//	debug_trie_index = true;
	//}
	if (root.nodes.size()) {
		uint totalN = totalNodes();
		//cout << "UNIFYING c = " << ++c << endl;
		//cout << "TOTAL NODES: " << totalN << endl;
		//cout << "FLATTERM: " << t.show() << endl;
		branch.emplace_back(TrieIndex::TrieIter(root), FlatTerm::TermIter(t));
		static uint cc = 0;
		while (branch.size()) {
			UnifyIter n = branch.back();
			if (debug_trie_index) {
				//cout << "BRANCHES cc = " << ++cc << ": " << trie_index::showBranches(branch) << endl;
				//cout << "n:" << endl << Indent::paragraph(n.showBranch()) << endl << endl;
			}
			branch.pop_back();
			if (debug_trie_index) {
				//cout << "BRANCHES AFTER " << trie_index::showBranches(branch) << endl;
			}
			for (const auto& i : n.unify()) {
				if (i.isTermEnd()) {
					for (uint ind :  i.trieIter.iter()->second.inds) {
						if (debug_trie_index) {
							cout << "ADDING TO RET: " << ind << endl;
							cout << "SUB: " << i.sub.show() << endl;
						}
						ret.emplace(ind, std::move(i.sub));
					}
				}
				if (!i.isNextEnd()) {
					if (debug_trie_index) {
						//cout << "next:" << endl << Indent::paragraph(i.next().showBranch()) << endl;
					}
					branch.push_back(i.next());
				}
			}
			if (!n.isSideEnd()) {
				if (debug_trie_index) {
					//cout << "side:" << endl << Indent::paragraph(n.side().showBranch()) << endl;
				}
				branch.push_back(n.side());
			}
			if (cc > totalN * 10) {
				cout << "TOO MUCH: " << cc << endl;
				exit(-2);
				break;
			}
		}
	}
	//cout << "leaving TrieIndex::unify " << endl;
	return ret;
}

}}}}

