#include "rus_prover_trie_index.hpp"


namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct TrieIter {
	typedef TrieIndex::ConstIterator Iter;
	TrieIter(Iter b, Iter e) : beg(b), iter(b), end(e) { }
	TrieIter(Iter b, Iter i, Iter e) : beg(b), iter(i), end(e) { }
	TrieIter(const TrieIter&) = default;
	TrieIter reset() const { return TrieIter(beg, end); }
	TrieIter side() const { auto i = iter; return TrieIter(beg, ++i, end); }
	TrieIter next() const { return TrieIter(iter->second.nodes.begin(), iter->second.nodes.end()); }
	bool isNextEnd() const { return iter->second.nodes.size() == 0; }
	bool isSideEnd() const { auto i = iter; return ++i == end; }
	const Iter beg;
	const Iter iter;
	const Iter end;
};

struct TrieIterVect {
	TrieIterVect(const vector<TrieIter>& v) : vect(v) { }
	TrieIterVect(const TrieIterVect&) = default;
	TrieIterVect side() {
		vector<TrieIter> side;
		bool chosen = false;
		for (const auto& i : vect) {
			if (!i.isSideEnd()) {
				side.push_back(i.side());
				chosen = true;
			} else if (chosen) {
				side.push_back(i);
			} else {
				side.push_back(i.reset());
			}
		}
		return TrieIterVect(side);
	}
	TrieIterVect next() const {
		vector<TrieIter> next;
		for (const auto& i : vect) {
			next.push_back(i.next());
		}
		return TrieIterPair(next);
	}
	bool isNextEnd() const {
		for (const auto& i : vect) {
			if (i.isNextEnd()) {
				return true;
			}
		}
		return false;
	}
	bool isTermEnd() const {
		for (const auto& i : vect) {
			if (!i.isNextEnd()) {
				return false;
			}
		}
		return true;
	}
	bool isSideEnd() const {
		for (const auto& i : vect) {
			if (!i.isSideEnd()) {
				return false;
			}
		}
		return true;
	}
	vector<TrieIter> vect;
};

struct UnifyTuple {
	UnifyTuple(const TrieIterVect& i) : iter(i) { }
	TrieIterVect iter;
	FlatSubst sub;
};

TrieIndex::Unified TrieIndex::unify(const FlatTerm& t) const {
	Unified ret;
	return ret;
}

struct UnifiedRet {
	uint ind1;
	uint ind2;
	Subst sub;
};

vector<UnifiedRet> unify(TrieIterPair p) {
	vector<UnifiedRet> ret;
	vector<UnifyPair> branch;
	branch.emplace_back(p);
	while (branch.size()) {
		UnifyPair n = branch.back();
		if (n.iter.isTermEnd()) {
			for (uint ind1 :  n.iter.i1->second.inds) {
				for (uint ind2 :  n.iter.i2->second.inds) {
					ret.emplace(ind1, ind2, n.sub);
				}
			}
		}
		if (!n.iter.isIndTermEnd()) {
			UnifyPair m = n.next();
			branch.push_back(m);
		} else {
			while (true) {
				branch.pop_back();
				UnifyPair m = n.side();
				if (!m.isIndSideEnd()) {
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
	return ret;
}

}}}}

