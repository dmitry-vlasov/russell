#include "rus_prover_trie_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct NodePair {
	NodePair(TrieIndex::Node* t, vector<FlatTerm::Node>::const_iterator e) : trie(t), end(e) { }
	TrieIndex::Node* trie;
	vector<FlatTerm::Node>::const_iterator end;
};

void TrieIndex::add(const FlatTerm& t) {
	stack<NodePair> st;
	Node* n = &root;
	for (auto i = t.nodes.begin(); i != t.nodes.end(); ++i) {
		Node* p = n;
		n = &n->nodes[i->ruleVar];
		n->parent = p;
		st.emplace(n, i->end);
		while (!st.empty() && st.top().end == i) {
			st.top().trie->ends.push_back(n);
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
				if (&branch[j].iter()->second == end) {
					ft.nodes[i].end = ft.nodes.begin() + j;
					goto out;
				}
			}
		}
		out:;
	}
	return ft;
}

FlatTerm TrieIndex::TrieIter::subTerm(const Node* n) const {
	vector<const TrieIndex::Node*> branch;
	/*while (n) {
		branch.push_back(n);
		if (&*iter_ == n) {
			break;
		}
		n = n->parent;
	}
	branch.reverse();
	return create_flatterm(branch);*/
}

vector<pair<FlatTerm, uint>> TrieIndex::unpack() const {
	vector<pair<FlatTerm, uint>> ret;
	vector<TrieIter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			TrieIter n = branch.back();
			for (uint ind :  n.iter()->second.inds) {
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

struct UnifyIter {
	UnifyIter(TrieIndex::TrieIter i1, FlatTerm::TermIter i2, const FlatSubst& s = FlatSubst(), bool v = true) :
		valid_(v), trieIter(i1), termIter(i2), sub(s) { }
	UnifyIter(const UnifyIter&) = default;
	UnifyIter& operator = (const UnifyIter&) = default;
	UnifyIter side() {
		return UnifyIter(trieIter.side(), termIter);
	}
	UnifyIter next() const { return UnifyIter(trieIter.next(), termIter.next()); }
	bool isNextEnd() const { return trieIter.isNextEnd() || termIter.isNextEnd(); }
	bool isTermEnd() const { return trieIter.isNextEnd() && termIter.isNextEnd(); }
	bool isSideEnd() const { return trieIter.isSideEnd() && termIter.isSideEnd(); }
	bool equals() const { return trieIter.iter()->first == termIter.iter()->ruleVar; }

	vector<UnifyIter> unify() const {
		if (equals()) {
			return vector<UnifyIter>(1, next());
		}
		if (trieIter.iter()->first.isVar()) {
			return vector<UnifyIter>(1, UnifyIter(
				trieIter,
				termIter.fastForward(),
				FlatSubst(trieIter.iter()->first.var, termIter.subTerm())
			));
		} else if (termIter.iter()->ruleVar.isVar()) {
			vector<UnifyIter> ret;
			/*for (auto e : trieIter.iter()->second.ends) {
				ret.push_back(UnifyIter(
						e,
						termIter,
						FlatSubst(
							termIter.iter()->ruleVar.var,
							FlatTerm(0) //trieIter.subTerm()
						)
					)
				);
			}*/
			return ret;
		} else {
			return vector<UnifyIter>();
		}
	}

	bool valid_;
	TrieIndex::TrieIter trieIter;
	FlatTerm::TermIter  termIter;
	FlatSubst sub;
};

TrieIndex::Unified TrieIndex::unify(const FlatTerm& t) const {
	Unified ret;
	vector<UnifyIter> branch;
	branch.emplace_back(TrieIndex::TrieIter(root), FlatTerm::TermIter(t));
	while (branch.size()) {
		UnifyIter n = branch.back();
		if (n.isTermEnd()) {
			for (uint ind :  n.trieIter.iter()->second.inds) {
				ret.emplace(ind, n.sub);
			}
		}
		/*if (n.equals() && !n.isNextEnd()) {
			branch.push_back(n.next());
		} else if (n.trieIter.iter()->first.isVar()) {
			return UnifyIterm(
				trieIter,
				termIter.fastForward(),
				FlatSubst(trieIter.iter()->first.var, termIter.subTerm())
			);
		} else if (termIter.iter()->isVar()) {

		}*/


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
	return ret;
}

}}}}

