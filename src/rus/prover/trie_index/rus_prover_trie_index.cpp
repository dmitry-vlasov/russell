#include "rus_prover_trie_index.hpp"
#include "rus_prover_trie_unify.hpp"

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
	auto ret = create_flatterm(branch);
	cout << "SUBTERM: " << ret.show() << endl;
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

struct UnifyIter {
	struct VarTerm {
		VarTerm() : term(0) { }
		VarTerm(LightSymbol v, const FlatTerm& t) : var(v), term(t) { }
		VarTerm(LightSymbol v, FlatTerm&& t) : var(v), term(std::move(t)) { }
		VarTerm(const VarTerm&) = default;
		VarTerm(VarTerm&&) = default;
		VarTerm& operator = (const VarTerm&) = default;
		LightSymbol var;
		FlatTerm term;
	};

	UnifyIter(TrieIndex::TrieIter i1, FlatTerm::TermIter i2, const VarTerm& vt = VarTerm(), bool v = true) :
		valid_(v), trieIter(i1), termIter(i2), varTerm(vt) { }
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
					std::move(VarTerm(
						trieIter.iter()->first.var,
						std::move(termIter.subTerm())
					))
				)
			);
		} else if (termIter.iter()->ruleVar.isVar()) {
			vector<UnifyIter> ret;
			for (auto e : trieIter.iter()->second.ends) {
				ret.push_back(
					UnifyIter(
						TrieIndex::TrieIter(e),
						termIter,
						std::move(VarTerm(
							termIter.iter()->ruleVar.var,
							std::move(trieIter.subTerm(e))
						))
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
	VarTerm varTerm;
};

FlatSubst gatherSub(const vector<UnifyIter>& branch, UnifyIter end) {
	FlatSubst ret;
	for (auto i : branch) {
		FlatTerm t = unify_step(ret, {i.varTerm.var}, i.varTerm.term);
		if (t.empty()) {
			break;
		}
	}
	FlatTerm t = unify_step(ret, {end.varTerm.var}, end.varTerm.term);
	if (t.empty()) {
		return FlatSubst(false);
	} else {
		return ret;
	}
}

string show(const vector<UnifyIter>& branch) {
	string ret;
	ret += "trie: ";
	for (auto i : branch) {
		ret += i.trieIter.iter()->first.show() + " ";
	}
	ret += "\n";
	ret += "term: ";
	for (auto i : branch) {
		ret += i.termIter.iter()->ruleVar.show() + " ";
	}
	ret += "\n";
	return ret;
}

TrieIndex::Unified TrieIndex::unify(const FlatTerm& t) const {
	static uint c = 0;
	Unified ret;
	vector<UnifyIter> branch;
	branch.emplace_back(TrieIndex::TrieIter(root), FlatTerm::TermIter(t));
	while (branch.size()) {
		cout << "BRANCH " << ++c << ": " << trie_index::show(branch) << endl;
		if (c == 2) {
			cout << "AAA" << endl;
		}
		UnifyIter n = branch.back();
		for (auto i : n.unify()) {
			if (i.isTermEnd()) {
				for (uint ind :  i.trieIter.iter()->second.inds) {
					FlatSubst sub = gatherSub(branch, i);
					if (sub.ok) {
						ret.emplace(ind, std::move(sub));
					}
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

