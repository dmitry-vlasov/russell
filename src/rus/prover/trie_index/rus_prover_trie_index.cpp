#include "rus_prover_trie_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

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
	return create_flatterm(branch);
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
			return vector<UnifyIter>(1, *this);
		}
		if (trieIter.iter()->first.isVar()) {
			return vector<UnifyIter>(1,
				UnifyIter(
					trieIter,
					termIter.fastForward(),
					FlatSubst(trieIter.iter()->first.var, termIter.subTerm())
				)
			);
		} else if (termIter.iter()->ruleVar.isVar()) {
			vector<UnifyIter> ret;
			for (auto e : trieIter.iter()->second.ends) {
				ret.push_back(
					UnifyIter(
						TrieIndex::TrieIter(e),
						termIter,
						FlatSubst(
							termIter.iter()->ruleVar.var,
							trieIter.subTerm(e)
						)
					)
				);
			}
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
		for (auto i : n.unify()) {
			if (i.isTermEnd()) {
				for (uint ind :  i.trieIter.iter()->second.inds) {
					ret.emplace(ind, i.sub);
				}
			}
			if (!i.isNextEnd()) {
				branch.push_back(i.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!i.isSideEnd()) {
						branch.push_back(i.side());
						break;
					}
					if (branch.empty()) {
						break;
					}
					i = branch.back();
				}
			}
		}
	}
	return ret;
}

}}}}

