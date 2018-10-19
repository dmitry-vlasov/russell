#include "rus_prover_trie_index.hpp"
#include "rus_prover_trie_unify.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_trie_index = false;

void TrieIndex::add(const FlatTerm& t) {
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
			st.top().trie->second.ends.push_back(ni);
			st.pop();
		}
	}
	n->inds.push_back(size++);
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
	return ft;
}

FlatTerm TrieIndex::TrieIter::subTerm(ConstIterator i) const {
	vector<TrieIter> branch;
	while (i != ConstIterator()) {
		branch.emplace_back(i);
		if (iter_ == i) {
			break;
		}
		i = i->second.parent;
	}
	std::reverse(branch.begin(), branch.end());
	auto ret = create_flatterm(branch);
	if (debug_trie_index) {
		cout << "SUBTERM: " << ret.show() << endl;
	}
	return ret;
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
	UnifyIter(TrieIndex::TrieIter i1, FlatTerm::TermIter i2, const FlatSubst& s = FlatSubst()) :
		trieIter(i1), termIter(i2), sub(s) { }
	UnifyIter(TrieIndex::TrieIter i1, FlatTerm::TermIter i2, FlatSubst&& s) :
		trieIter(i1), termIter(i2), sub(std::move(s)) { }
	UnifyIter(const UnifyIter&) = default;
	UnifyIter& operator = (const UnifyIter&) = default;
	UnifyIter side() {
		return UnifyIter(trieIter.side(), termIter, sub);
	}
	UnifyIter next() const { return UnifyIter(trieIter.next(), termIter.next(), sub); }
	bool isNextEnd() const { return sub.ok ? (trieIter.isNextEnd() || termIter.isNextEnd()) : true; }
	bool isTermEnd() const { return sub.ok ? (trieIter.isNextEnd() && termIter.isNextEnd()) : true; }
	bool isSideEnd() const { return sub.ok ? (trieIter.isSideEnd() && termIter.isSideEnd()) : true; }
	bool equals() const { return trieIter.iter()->first == termIter.iter()->ruleVar; }

	vector<UnifyIter> unify() const {
		vector<UnifyIter> ret;
		if (equals()) {
			ret.emplace_back(*this);
		} else {
			if (trieIter.iter()->first.isVar() && trieIter.iter()->first.var.rep) {
				//debug_flatterm = true;
				FlatTerm subterm = termIter.subTerm();
				FlatSubst s = unify_step(sub, {trieIter.iter()->first.var}, subterm);
				if (s.ok) {
					ret.emplace_back(trieIter, termIter.fastForward(), s);
				}
			} else if (termIter.iter()->ruleVar.isVar() && termIter.iter()->ruleVar.var.rep) {
				if (debug_trie_index) {
					cout << "termIter.iter()->ruleVar.isVar() && termIter.iter()->ruleVar.var.rep" << endl;
				}
				for (auto e : trieIter.iter()->second.ends) {
					if (debug_trie_index) {
						cout << "got end: " << (*e).first.show() << endl;
						debug_flat_unify = true;
					}
					FlatSubst s = unify_step(sub, {termIter.iter()->ruleVar.var}, trieIter.subTerm(e));
					if (s.ok) {
						ret.emplace_back(TrieIndex::TrieIter(e), termIter, s);
					}
				}
			}
		}
		return ret;
	}
	TrieIndex::TrieIter trieIter;
	FlatTerm::TermIter  termIter;
	FlatSubst sub;
};

string show(const vector<UnifyIter>& branch) {
	string ret;
	ret += "trie: ";
	for (auto i : branch) {
		if (i.trieIter.isValid()) {
			ret += i.trieIter.show() + " ";
		} else {
			ret += "<UNDEF> ";
		}
	}
	ret += "\n";
	ret += "term: ";
	for (auto i : branch) {
		if (i.termIter.isValid()) {
			ret += i.termIter.iter()->ruleVar.show() + " ";
		} else {
			ret += "<UNDEF> ";
		}
	}
	ret += "\n";
	return ret;
}

TrieIndex::Unified TrieIndex::unify(const FlatTerm& t) const {
	static uint c = 0;
	Unified ret;
	vector<UnifyIter> branch;
	if (root.nodes.size()) {
		uint totalN = totalNodes();
		//cout << "UNIFYING c = " << ++c << endl;
		//cout << "TOTAL NODES: " << totalN << endl;
		//cout << "FLATTERM: " << t.show() << endl;
		branch.emplace_back(TrieIndex::TrieIter(root), FlatTerm::TermIter(t));
		if (!branch.back().termIter.isValid()) {
			cout << "XXX" << endl;
		}
		static uint cc = 0;
		while (branch.size()) {
			if (debug_trie_index) {
				cout << "BRANCH cc = " << ++cc << ": " << trie_index::show(branch) << endl;
			}
			UnifyIter n = branch.back();
			vector<UnifyIter> unified = n.unify();
			for (const auto& i : unified) {
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
					branch.push_back(i.next());
				} else {
					auto j = i;
					while (true) {
						branch.pop_back();
						if (!j.isSideEnd()) {
							branch.push_back(j.side());
							break;
						}
						if (branch.empty()) {
							break;
						}
						j = branch.back();
					}
				}
			}
			if (!unified.size()) {
				if (debug_trie_index) {
					cout << "!unified.size()" << endl;
				}
				branch.pop_back();
			}
			if (cc > totalN) {
				cout << "TOO MUCH: " << cc << endl;
				break;
			}
		}
	}
	return ret;
}

}}}}

