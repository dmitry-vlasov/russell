#pragma once

#include "rus_prover_trie_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct TrieIndexVector {
	typedef map<uint, FlatSubst> Unified;

	//void add(const FlatTerm& t);
	//Unified unify(const FlatTerm&) const;
	//string show() const;

	vector<TrieIndex> indexVect;
};

extern bool debug_trie_index_vector;


struct BothIter {
	enum Kind { NONE, TRIE, TERM };
	BothIter() : kind_(NONE) { }
	BothIter(TrieIndex::TrieIter i) : kind_(TRIE), trieIter(i) { }
	BothIter(FlatTerm::TermIter i) : kind_(TERM), termIter(i2) { }
	BothIter(const BothIter&) = default;
	BothIter& operator = (const BothIter&) = default;

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

private:
	Kind kind_;
	TrieIndex::TrieIter trieIter;
	FlatTerm::TermIter  termIter;
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
	bool isNextEnd() const { return sub.ok ? (trieIter.isNextEnd() || termIter.isNextEnd()) : true; }
	bool isTermEnd() const { return sub.ok ? (trieIter.isNextEnd() && termIter.isNextEnd()) : true; }
	bool isSideEnd() const { return sub.ok ? (trieIter.isSideEnd() && termIter.isSideEnd()) : true; }
	bool equals() const {
		if (!iters.size()) {
			return true;
		}
		RuleVar rv = iters[0].ruleVar;
		for (uint i = 1; i < iters.size(); ++ i) {
			if (rv != iters[i].ruleVar) {
				return false;
			}
		}
		return true;
	}

	vector<UnifyIters> unify() const {
		vector<UnifyIters> ret;
		if (equals()) {
			ret.emplace_back(*this);
		} else {
			FlatUnifStepData data(iters);

			/*uint var_ind = -1;
			for (uint i = 0; i < iters.size(); ++ i) {
				if (iters[i].isVar()) {
					var_ind = i;
					break;
				}
			}
			if (var_ind != -1) {
				LightSymbol var = iters[var_ind].var();
				for (uint i = 0; i < iters.size(); ++i) {

				}
			}


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
			}*/
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
	vector<BothIter> iters;

	FlatSubst parentSub;
	FlatSubst sub;
};


}}}}
