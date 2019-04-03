#pragma once

#include "rus_prover_index.hpp"
#include "rus_prover_index_unify_step.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

extern bool debug_trie_index_vector;

struct EmptyIter {
	EmptyIter(const vector<uint>& i = vector<uint>()) : inds_(i) { }
	EmptyIter& operator = (const EmptyIter&) = default;

	bool operator == (const EmptyIter& i) const { return true; }
	bool operator != (const EmptyIter& i) const { return false; }

	EmptyIter side() const { return *this; }
	EmptyIter next() const { return *this; }
	EmptyIter prev() const { return *this; }
	EmptyIter reset() const { return *this; }
	bool isNextEnd() const { return false; }
	bool isSideEnd() const { return true; }
	bool isValid() const { return true; }
	Term subTerm() const { return Term(); }
	vector<uint> inds() const { return inds_; }
	bool isEnd(const EmptyIter&) const { return true; }
	bool isVar() const { return false; }
	LightSymbol var() const { return LightSymbol(); }
	RuleVar ruleVar() const { return RuleVar(); }

	string show() const {
		return "empty, inds: " + prover::show(inds_);
	}

private:
	vector<uint> inds_;
};


struct MultyIter {
	enum Kind { NONE, TRIE, TERM, EMPTY };
	MultyIter() : kind_(NONE) { }
	MultyIter(Index::Iter i) : kind_(TRIE), trieIter(i) { }
	MultyIter(Term::TermIter i) : kind_(TERM), termIter(i) { }
	MultyIter(EmptyIter i) : kind_(EMPTY), emptyIter(i) { }
	MultyIter(const MultyIter&) = default;
	MultyIter& operator = (const MultyIter&) = default;

	bool operator == (const MultyIter& i) const {
		switch (kind_) {
		case TRIE:  return trieIter == i.trieIter;
		case TERM:  return termIter == i.termIter;
		case EMPTY: return emptyIter == i.emptyIter;
		default: throw Error("impossible");
		}
	}
	bool operator != (const MultyIter& i) const {
		switch (kind_) {
		case TRIE:  return trieIter != i.trieIter;
		case TERM:  return termIter != i.termIter;
		case EMPTY: return emptyIter != i.emptyIter;
		default: throw Error("impossible");
		}
	}

	Kind kind() const { return kind_; }
	MultyIter side() const {
		switch (kind_) {
		case TRIE:  return MultyIter(trieIter.side());
		case TERM:  return MultyIter(termIter.side());
		case EMPTY: return MultyIter(emptyIter.side());
		default: throw Error("impossible");
		}
	}
	MultyIter next() const {
		switch (kind_) {
		case TRIE:  return MultyIter(trieIter.next());
		case TERM:  return MultyIter(termIter.next());
		case EMPTY: return MultyIter(emptyIter.next());
		default: throw Error("impossible");
		}
	}
	MultyIter prev() const {
		switch (kind_) {
		case TRIE:  return MultyIter(trieIter.prev());
		case TERM:  return MultyIter(termIter.prev());
		case EMPTY: return MultyIter(emptyIter.prev());
		default: throw Error("impossible");
		}
	}
	MultyIter reset() const {
		switch (kind_) {
		case TRIE:  return MultyIter(trieIter.reset());
		case TERM:  return MultyIter(termIter.reset());
		case EMPTY: return MultyIter(emptyIter.reset());
		default: throw Error("impossible");
		}
	}
	bool isNextEnd() const {
		switch (kind_) {
		case TRIE:  return trieIter.isNextEnd();
		case TERM:  return termIter.isNextEnd();
		case EMPTY: return emptyIter.isNextEnd();
		default: throw Error("impossible");
		}
	}
	bool isSideEnd() const {
		switch (kind_) {
		case TRIE:  return trieIter.isSideEnd();
		case TERM:  return termIter.isSideEnd();
		case EMPTY: return emptyIter.isSideEnd();
		default: throw Error("impossible");
		}
	}
	bool isValid() const {
		switch (kind_) {
		case TRIE:  return trieIter.isValid();
		case TERM:  return termIter.isValid();
		case EMPTY: return emptyIter.isValid();
		default: throw Error("impossible");
		}
	}
	Term subTerm(const MultyIter& i) const {
		switch (kind_) {
		case TRIE:  return trieIter.subTerm(i.trieIter);
		case TERM:  return termIter.subTerm();
		case EMPTY: return emptyIter.subTerm();
		default: throw Error("impossible");
		}
	}

	vector<uint> inds() const {
		switch (kind_) {
		case TRIE:  return trieIter.iter()->second.inds;
		case TERM:  return {0};
		case EMPTY: return emptyIter.inds();
		default: throw Error("impossible");
		}
	}
	vector<pair<Term, MultyIter>> subTerms() const {
		vector<pair<Term, MultyIter>> ret;
		switch (kind_) {
		case TRIE: {
			auto subterms = trieIter.subTerms();
			for (auto st : subterms) {
				ret.emplace_back(std::move(st.first), MultyIter(st.second));
			}
			break;
		}
		case TERM: {
			auto subterms = termIter.subTerms();
			for (auto st : subterms) {
				ret.emplace_back(std::move(st.first), MultyIter(st.second));
			}
			break;
		}
		case EMPTY: break;
		default: throw Error("impossible");
		}
		return ret;
	}
	vector<MultyIter> ends() const {
		vector<MultyIter> ret;
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
		case EMPTY: break;
		default: throw Error("impossible");
		}
		return ret;
	}
	bool isEnd(const MultyIter& i) const {
		switch (kind_) {
		case TRIE:  return trieIter.isEnd(i.trieIter);
		case TERM:  return termIter.isEnd(i.termIter);
		case EMPTY: return emptyIter.isEnd(i.emptyIter);
		default: throw Error("impossible");
		}
	}
	bool isVar() const {
		switch (kind_) {
		case TRIE:  return trieIter.isVar();
		case TERM:  return termIter.isVar();
		case EMPTY: return emptyIter.isVar();
		default: throw Error("impossible");
		}
	}
	LightSymbol var() const {
		switch (kind_) {
		case TRIE:  return trieIter.var();
		case TERM:  return termIter.var();
		case EMPTY: return emptyIter.var();
		default: throw Error("impossible");
		}
	}
	RuleVar ruleVar() const {
		switch (kind_) {
		case TRIE:  return trieIter.ruleVar();
		case TERM:  return termIter.ruleVar();
		case EMPTY: return emptyIter.ruleVar();
		default: throw Error("impossible");
		}
	}

	string show() const {
		switch (kind_) {
		case TRIE:  return trieIter.show();
		case TERM:  return termIter.show();
		case EMPTY: return emptyIter.show();
		default: throw Error("impossible");
		}
	}

private:
	Kind kind_;
	Index::Iter    trieIter;
	Term::TermIter termIter;
	EmptyIter      emptyIter;
};

template<> inline RuleVar ruleVar<MultyIter>(MultyIter i) {
	return i.ruleVar();
};

struct UnifyIters {
	UnifyIters(const vector<MultyIter>& i, const Subst& ps = Subst(), const Subst& s = Subst()) :
		iters(i), parentSub(ps), sub(s) { }
	UnifyIters(vector<MultyIter>&& i, Subst&& ps, Subst&& s) :
		iters(std::move(i)), parentSub(std::move(ps)), sub(std::move(s)) { }
	UnifyIters(const UnifyIters&) = default;
	UnifyIters& operator = (const UnifyIters&) = default;

	UnifyIters side() {
		vector<MultyIter> side_iters;
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
		vector<MultyIter> next_iters;
		for (auto i : iters) {
			next_iters.push_back(i.next());
		}
		return UnifyIters(next_iters, sub, sub);
	}
	bool isNextEnd() const {
		if (!sub.ok()) {
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
		if (!sub.ok()) {
			return true;
		}
		for (uint i = 0; i < iters.size(); ++i) {
			if (!ends.iters[i].isEnd(iters[i])) {
				return false;
			}
		}
		return true;
	}
	void showTermEnd(const UnifyIters& ends) const {
		for (uint i = 0; i < iters.size(); ++i) {
			cout << i << ": " << (ends.iters[i].isEnd(iters[i]) ? "END" : "X" ) << endl;
		}
	}
	bool isNextEnd(const UnifyIters& ends) const {
		if (!sub.ok()) {
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
		if (!sub.ok()) {
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
				vector<MultyIter> branch;
				while (j != MultyIter()) {
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
	vector<vector<uint>> inds() const;

	vector<MultyIter> iters;
	Subst parentSub;
	Subst sub;
};

struct FlatTermSubst {
	FlatTermSubst(const Term& t, const Subst& s) :
		term(make_unique<Term>(t)), sub(make_unique<Subst>(s)) { }
	FlatTermSubst(const FlatTermSubst& ts) :
		term(make_unique<Term>(*ts.term)), sub(make_unique<Subst>(*ts.sub)) { }
	FlatTermSubst(FlatTermSubst&&) = default;
	unique_ptr<Term> term;
	unique_ptr<Subst> sub;
	string show() const {
		return "term: " + term->show() + "\nsub:\n" + sub->show();
	}
};

map<vector<uint>, FlatTermSubst> unify_general(const UnifyIters& i);

template<class D>
vector<typename TrieIndexMap<D>::Unified> unify_general(const TrieIndexMap<D>& m, const Term& t) {
	vector<typename TrieIndexMap<D>::Unified> ret;
	if (!m.index().size) {
		return ret;
	}
	vector<MultyIter> iters;
	iters.emplace_back(Index::Iter(m.index().root));
	iters.emplace_back(Term::TermIter(t));
	try {
		map<vector<uint>, FlatTermSubst> unif = unify_general(iters);
		for (auto& p : unif) {
			if (p.second.sub->ok()) {
				ret.emplace_back(m.data().at(p.first[0]), std::move(*p.second.sub));
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
