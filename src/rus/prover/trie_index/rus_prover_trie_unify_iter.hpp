#pragma once

#include "rus_prover_trie_index.hpp"
#include "rus_prover_trie_unify.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

extern bool debug_trie_index_vector;

struct BothIter {
	enum Kind { NONE, TRIE, TERM };
	BothIter() : kind_(NONE) { }
	BothIter(TrieIndex::TrieIter i) : kind_(TRIE), trieIter(i) { }
	BothIter(FlatTerm::TermIter i) : kind_(TERM), termIter(i) { }
	BothIter(const BothIter&) = default;
	BothIter& operator = (const BothIter&) = default;

	bool operator == (const BothIter& i) const {
		switch (kind_) {
		case TRIE: return trieIter == i.trieIter;
		case TERM: return termIter == i.termIter;
		default:   return true;
		}
	}
	bool operator != (const BothIter& i) const {
		switch (kind_) {
		case TRIE: return trieIter != i.trieIter;
		case TERM: return termIter != i.termIter;
		default:   return false;
		}
	}

	Kind kind() const { return kind_; }
	BothIter side() const {
		switch (kind_) {
		case TRIE: return BothIter(trieIter.side());
		case TERM: return BothIter(termIter.side());
		default:   return BothIter();
		}
	}
	BothIter next() const {
		switch (kind_) {
		case TRIE: return BothIter(trieIter.next());
		case TERM: return BothIter(termIter.next());
		default:   return BothIter();
		}
	}
	BothIter prev() const {
		switch (kind_) {
		case TRIE: return BothIter(trieIter.prev());
		case TERM: return BothIter(termIter.prev());
		default:   return BothIter();
		}
	}
	BothIter reset() const {
		switch (kind_) {
		case TRIE: return BothIter(trieIter.reset());
		case TERM: return BothIter(termIter.reset());
		default:   return BothIter();
		}
	}
	bool isNextEnd() const {
		switch (kind_) {
		case TRIE: return trieIter.isNextEnd();
		case TERM: return termIter.isNextEnd();
		default:   return true;
		}
	}
	bool isSideEnd() const {
		switch (kind_) {
		case TRIE: return trieIter.isSideEnd();
		case TERM: return termIter.isSideEnd();
		default:   return true;
		}
	}
	bool isValid() const {
		switch (kind_) {
		case TRIE: return trieIter.isValid();
		case TERM: return termIter.isValid();
		default:   return false;
		}
	}
	FlatTerm subTerm(const BothIter& i) const {
		switch (kind_) {
		case TRIE: return trieIter.subTerm(i.trieIter);
		case TERM: return termIter.subTerm();
		default:   return FlatTerm();
		}
	}

	vector<uint> inds() const {
		switch (kind_) {
		case TRIE: return trieIter.iter()->second.inds;
		case TERM: return {0};
		default:   return {};
		}
	}
	vector<pair<FlatTerm, BothIter>> subTerms() const {
		vector<pair<FlatTerm, BothIter>> ret;
		switch (kind_) {
		case TRIE: {
			auto subterms = trieIter.subTerms();
			for (auto st : subterms) {
				ret.emplace_back(std::move(st.first), BothIter(st.second));
			}
			break;
		}
		case TERM: {
			auto subterms = termIter.subTerms();
			for (auto st : subterms) {
				ret.emplace_back(std::move(st.first), BothIter(st.second));
			}
			break;
		}
		default: break;
		}
		return ret;
	}
	vector<BothIter> ends() const {
		vector<BothIter> ret;
		switch (kind_) {
		case TRIE: {
			auto ends = trieIter.ends();
			for (auto end : ends) {
				ret.emplace_back(end);
			}
			break;
		}
		case TERM: {
			auto ends = termIter.ends();
			for (auto end : ends) {
				ret.emplace_back(end);
			}
			break;
		}
		default: break;
		}
		return ret;
	}
	bool isEnd(const BothIter& i) const {
		switch (kind_) {
		case TRIE: return trieIter.isEnd(i.trieIter);
		case TERM: return termIter.isEnd(i.termIter);
		default:   return true;
		}
	}
	bool isVar() const {
		switch (kind_) {
		case TRIE: return trieIter.isVar();
		case TERM: return termIter.isVar();
		default:   return false;
		}
	}
	LightSymbol var() const {
		switch (kind_) {
		case TRIE: return trieIter.var();
		case TERM: return termIter.var();
		default:   return LightSymbol();
		}
	}
	RuleVar ruleVar() const {
		switch (kind_) {
		case TRIE: return trieIter.ruleVar();
		case TERM: return termIter.ruleVar();
		default:   return RuleVar();
		}
	}

	string show() const {
		switch (kind_) {
		case TRIE: return trieIter.show();
		case TERM: return termIter.show();
		default:   return "";
		}
	}

private:
	Kind kind_;
	TrieIndex::TrieIter trieIter;
	FlatTerm::TermIter  termIter;
};

template<> inline RuleVar ruleVar<BothIter>(BothIter i) {
	return i.ruleVar();
};

struct UnifyIters {
	UnifyIters(const vector<BothIter>& i, const FlatSubst& ps = FlatSubst(), const FlatSubst& s = FlatSubst()) :
		iters(i), parentSub(ps), sub(s) { }
	UnifyIters(vector<BothIter>&& i, FlatSubst&& ps, FlatSubst&& s) :
		iters(std::move(i)), parentSub(std::move(ps)), sub(std::move(s)) { }
	UnifyIters(const UnifyIters&) = default;
	UnifyIters& operator = (const UnifyIters&) = default;

	UnifyIters side() {
		vector<BothIter> side_iters;
		bool found = false;
		for (auto i : iters) {
			if (found) {
				side_iters.push_back(i);
			} else {
				if (i.isSideEnd()) {
					side_iters.push_back(i.reset());
				} else {
					side_iters.push_back(i.side());
					found = true;
				}
			}
		}
		return UnifyIters(side_iters, parentSub, parentSub);
	}
	UnifyIters next() const {
		vector<BothIter> next_iters;
		for (auto i : iters) {
			next_iters.push_back(i.next());
		}
		return UnifyIters(next_iters, sub, sub);
	}
	bool isNextEnd() const {
		if (!sub.ok) {
			return true;
		}
		for (const auto& i : iters) {
			if (i.isNextEnd()) {
				return true;
			}
		}
		return false;
	}
	bool isTermEnd(const UnifyIters& ends) const {
		if (!sub.ok) {
			return true;
		}
		for (uint i = 0; i < iters.size(); ++i) {
			if (!ends.iters[i].isEnd(iters[i])) {
				return false;
			}
		}
		return true;
	}
	bool isTermEndOld(const UnifyIters& ends) const {
		if (!sub.ok) {
			return true;
		}
		for (uint i = 0; i < iters.size(); ++i) {
			if (ends.iters[i].isEnd(iters[i])) {
				return true;
			}
		}
		return false;
	}
	void showTermEnd(const UnifyIters& ends) const {
		if (!sub.ok) {
			cout << "!sub.ok" << endl;
		}
		for (uint i = 0; i < iters.size(); ++i) {
			cout << i << ": " << (ends.iters[i].isEnd(iters[i]) ? "END" : "X" ) << endl;
		}
	}
	bool isNextEnd(const UnifyIters& ends) const {
		if (!sub.ok) {
			return true;
		}
		for (uint i = 0; i < iters.size(); ++i) {
			if (ends.iters[i].isEnd(iters[i]) || iters[i].isNextEnd()) {
				return true;
			}
		}
		return false;
	}
	bool isSideEnd() const {
		if (!sub.ok) {
			return true;
		}
		for (const auto& i : iters) {
			if (!i.isSideEnd()) {
				return false;
			}
		}
		return true;
	}
	bool equals() const {
		if (!iters.size()) {
			return true;
		}
		RuleVar rv = iters[0].ruleVar();
		for (uint i = 1; i < iters.size(); ++ i) {
			if (rv != iters[i].ruleVar()) {
				return false;
			}
		}
		return true;
	}

	string show(bool full = false) const {
		ostringstream oss;
		uint n = 0;
		for (const auto& i : iters) {
			if (full) {
				auto j = i;
				vector<BothIter> branch;
				while (j != BothIter()) {
					branch.push_back(j);
					j = j.prev();
				}
				reverse(branch.begin(), branch.end());
				oss << n << ": ";
				for (auto x : branch) {
					oss << x.show();
				}
				oss << endl;
			} else {
				oss << n << "-iter: " << i.show() << endl;
			}
			++n;
		}
		return oss.str();
	}
	string showBranch() const {
		string ret;
		//ret += "trie: " + trieIter.showBranch() + "\n";
		//ret += "term: " + termIter.showBranch() + "\n";
		return ret;
	}
	vector<vector<uint>> inds() const;

	vector<BothIter> iters;

	FlatSubst parentSub;
	FlatSubst sub;
};

struct FlatTermSubst {
	FlatTermSubst(const FlatTerm& t, const FlatSubst& s) : term(t), sub(s) { }
	FlatTermSubst(const FlatTermSubst&) = default;
	FlatTermSubst(FlatTermSubst&&) = default;
	FlatTerm term;
	FlatSubst sub;
};

map<vector<uint>, FlatTermSubst> unify_general(const UnifyIters& i);

template<class D>
vector<typename TrieIndexMap<D>::Unified> unify_general(const TrieIndexMap<D>& m, const LightTree& t) {
	vector<typename TrieIndexMap<D>::Unified> ret;
	FlatTerm ft = convert2flatterm(t);
	vector<BothIter> iters;
	iters.emplace_back(TrieIndex::TrieIter(m.index().root));
	iters.emplace_back(FlatTerm::TermIter(ft));
	try {
		map<vector<uint>, FlatTermSubst> unif = unify_general(iters);
		for (auto& p : unif) {
			if (p.second.sub.ok) {
				//cout << "UNIFIED: " << p.first << endl;
				ret.emplace_back(m.data().at(p.first[0]), convert2subst(p.second.sub));
			}
		}
	} catch (Error& err) {
		cout << "unify_general: " << endl;
		cout << m.index().show_pointers() << endl << endl;
		throw err;
	}
	return ret;
}

}}}}
