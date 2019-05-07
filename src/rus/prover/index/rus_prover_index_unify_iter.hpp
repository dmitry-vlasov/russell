#pragma once

#include "../rus_prover_node.hpp"
#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

template<class Iter> RuleVar ruleVar(Iter);
template<>
inline RuleVar ruleVar<Term::ConstIterator>(Term::ConstIterator i) {
	return i->ruleVar;
};
template<> inline RuleVar ruleVar<Index::Iter>(Index::Iter i) {
	return i.ruleVar();
};
template<> inline RuleVar ruleVar<Term::Iter>(Term::Iter i) {
	return i.ruleVar();
};

struct UnifyIters {
	explicit UnifyIters(const UnifyIters& ui, const Subst& ps, const Subst& s = Subst()) :
		indexIters(ui.indexIters), termIters(ui.termIters), parentSub(ps), sub(s) { }
	explicit UnifyIters(const vector<Index::Iter>& ii, const Subst& ps = Subst(), const Subst& s = Subst()) :
		indexIters(ii), parentSub(ps), sub(s) { }
	explicit UnifyIters(const vector<Term::Iter>& ti, const Subst& ps = Subst(), const Subst& s = Subst()) :
		termIters(ti), parentSub(ps), sub(s) { }
	explicit UnifyIters(const vector<Index::Iter>& ii, const vector<Term::Iter>& ti, const Subst& ps = Subst(), const Subst& s = Subst()) :
		indexIters(ii), termIters(ti), parentSub(ps), sub(s) { }
	explicit UnifyIters(vector<Index::Iter>&& ii, vector<Term::Iter>&& ti, Subst&& ps, Subst&& s) :
		indexIters(std::move(ii)), termIters(std::move(ti)), parentSub(std::move(ps)), sub(std::move(s)) { }
	explicit UnifyIters(const UnifyIters&) = default;

	UnifyIters& operator = (const UnifyIters&) = default;

	UnifyIters side() const {
		vector<Index::Iter> side_iters;
		bool found = false;
		for (auto i : indexIters) {
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
		return UnifyIters(side_iters, termIters, parentSub, parentSub);
	}
	void setHint(const Rule* r) {
		for (auto& i : indexIters) {
			i.setHint(r);
		}
		for (auto& i : termIters) {
			i.setHint(r);
		}
	}
	UnifyIters next() const {
		vector<Index::Iter> next_index;
		for (auto i : indexIters) {
			next_index.push_back(i.next());
		}
		vector<Term::Iter> next_term;
		for (auto i : termIters) {
			next_term.push_back(i.next());
		}
		return UnifyIters(next_index, next_term, sub, sub);
	}
	bool isNextEnd() const {
		if (!sub.ok()) {
			return true;
		}
		for (const auto& i : indexIters) {
			if (i.isNextEnd()) {
				return true;
			}
		}
		for (const auto& i : termIters) {
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
		for (uint i = 0; i < indexIters.size(); ++i) {
			if (!ends.indexIters[i].isEnd(indexIters[i])) {
				return false;
			}
		}
		for (uint i = 0; i < termIters.size(); ++i) {
			if (!ends.termIters[i].isEnd(termIters[i])) {
				return false;
			}
		}
		return true;
	}
	void showTermEnd(const UnifyIters& ends) const {
		cout << "Index iters:" << endl;
		for (uint i = 0; i < indexIters.size(); ++i) {
			cout << "\t" << i << ": " << (ends.indexIters[i].isEnd(indexIters[i]) ? "END" : "X" ) << endl;
		}
		cout << "Term iters:" << endl;
		for (uint i = 0; i < termIters.size(); ++i) {
			cout << "\t" << i << ": " << (ends.termIters[i].isEnd(termIters[i]) ? "END" : "X" ) << endl;
		}
	}
	bool isNextEnd(const UnifyIters& ends) const {
		if (!sub.ok()) {
			return true;
		}
		for (uint i = 0; i < indexIters.size(); ++i) {
			if (ends.indexIters[i].isEnd(indexIters[i]) || indexIters[i].isNextEnd()) {
				return true;
			}
		}
		for (uint i = 0; i < termIters.size(); ++i) {
			if (ends.termIters[i].isEnd(termIters[i]) || termIters[i].isNextEnd()) {
				return true;
			}
		}
		return false;
	}
	bool isSideEnd() const {
		if (!sub.ok()) {
			return true;
		}
		for (const auto& i : indexIters) {
			if (!i.isSideEnd()) {
				return false;
			}
		}
		return true;
	}
	bool equals() const {
		if (!size()) {
			return true;
		}
		RuleVar rv = indexIters.size() ? indexIters[0].ruleVar() : termIters[0].ruleVar();
		for (uint i = (indexIters.size() ? 1 : 0); i < indexIters.size(); ++ i) {
			if (rv != indexIters[i].ruleVar()) {
				return false;
			}
		}
		for (uint i = (indexIters.size() ? 0 : 1); i < termIters.size(); ++ i) {
			if (rv != termIters[i].ruleVar()) {
				return false;
			}
		}
		return true;
	}
	bool isValid() const {
		if (!sub.ok()) {
			return false;
		}
		for (uint i = 0; i < indexIters.size(); ++i) {
			if (!indexIters[i].isValid()) {
				return false;
			}
		}
		for (uint i = 0; i < indexIters.size(); ++i) {
			if (!indexIters[i].isValid()) {
				return false;
			}
		}
		return true;
	}
	Term subTerm(const UnifyIters& ends) const {
		if (indexIters.size()) {
			return indexIters[0].subTerm(ends.indexIters[0]);
		} else if (termIters.size()) {
			return termIters[0].subTerm();
		} else {
			throw Error("empty subterm - impossible");
		}
	}

	string show(bool full = false) const {
		ostringstream oss;
		uint n = 0;
		cout << "Index iters:" << endl;
		for (const auto& i : indexIters) {
			if (full) {
				auto j = i;
				vector<Index::Iter> branch;
				while (j != Index::Iter()) {
					branch.push_back(j);
					j = j.prev();
				}
				reverse(branch.begin(), branch.end());
				oss << "\t" << n << ": ";
				for (auto x : branch) {
					oss << x.show();
				}
				oss << endl;
			} else {
				if (isValid()) {
					oss << "\t" << n << "-iter: " << i.show() << endl;
				} else {
					oss << "\t" << n << "-iter: NOT VALID " << i.show() << endl;
				}
			}
			++n;
		}
		cout << "Term iters:" << endl;
		n = 0;
		for (const auto& i : termIters) {
			if (isValid()) {
				oss << "\t" << n << "-iter: " << i.show() << endl;
			} else {
				oss << "\t" << n << "-iter: NOT VALID " << i.show() << endl;
			}
			++n;
		}
		return oss.str();
	}
	string showTree() const {
		ostringstream oss;
		cout << "Index iters:" << endl;
		for (uint i = 0; i < indexIters.size(); ++ i) {
			oss << i << "-iter: " << endl;
			oss << Indent::paragraph(indexIters[i].showTree()) << endl;
		}
		cout << "Term iters:" << endl;
		for (uint i = 0; i < termIters.size(); ++ i) {
			oss << i << "-iter: " << endl;
			oss << Indent::paragraph(termIters[i].showTree()) << endl;
		}
		return oss.str();
	}
	vector<vector<uint>> inds() const;
	uint size() const {
		return indexIters.size() + termIters.size();
	}
	bool operator == (const UnifyIters& ui) const {
		if (indexIters.size() != ui.indexIters.size()) {
			return false;
		}
		for (uint i = 0; i < indexIters.size(); ++i) {
			if (indexIters[i] != ui.indexIters[i]) {
				return false;
			}
		}
		if (termIters.size() != ui.termIters.size()) {
			return false;
		}
		for (uint i = 0; i < termIters.size(); ++i) {
			if (termIters[i] != ui.termIters[i]) {
				return false;
			}
		}
		return true;
	}
	bool operator != (const UnifyIters& ui) const {
		return !operator == (ui);
	}

	vector<Index::Iter> indexIters;
	vector<Term::Iter>  termIters;
	Subst parentSub;
	Subst sub;
};

struct TermSubst {
	TermSubst() = default;
	TermSubst(const Term& t, const Subst& s) : term(t), sub(s) { }
	TermSubst(Term&& t, Subst&& s) : term(std::move(t)), sub(std::move(s)) { }
	TermSubst(const TermSubst& ts) = default;
	TermSubst(TermSubst&&) = default;

	string show() const {
		return "term: " + term.show() + "\nsub:\n" + sub.show();
	}
	bool operator == (const TermSubst& ts) const {
		return term == ts.term && sub == ts.sub;
	}
	bool operator != (const TermSubst& ts) const {
		return !operator == (ts);
	}
	bool isDefault() const {
		return !term.len() && !sub.size();
	}

	Term term;
	Subst sub;
};

//map<vector<uint>, TermSubst> unify_general(const UnifyIters& i);

map<vector<uint>, TermSubst> unify_general(const vector<const Index*>& inds, const vector<const Term*>& terms);

inline map<vector<uint>, TermSubst> unify_general(const vector<const Index*>& inds) {
	return unify_general(inds, vector<const Term*>());
}

inline map<vector<uint>, TermSubst> unify_general(const vector<const Term*>& terms) {
	return unify_general(vector<const Index*>(), terms);
}

template<class D>
vector<typename IndexMap<D>::Unified> unify_general(const IndexMap<D>& m, const Term& t) {
	vector<typename IndexMap<D>::Unified> ret;
	if (!m.index().size()) {
		return ret;
	}
	try {
		Timer timer;
		timer.start();
		map<vector<uint>, TermSubst> unif = unify_general(
			vector<const Index*>(1, &m.index()),
			vector<const Term*>(1, &t)
		);
		add_timer_stats("unify_general_iters", timer);

		for (auto& p : unif) {
			if (p.second.sub.ok()) {
				ret.emplace_back(m.data().at(p.first[0]), std::move(p.second.sub));
			}
		}
	} catch (Error& err) {
		cout << "unify_general: " << endl;
		//cout << m.index().show_pointers() << endl << endl;
		cout << m.index().show() << endl << endl;
		cout << t.show() << endl << endl;
		throw err;
	}
	return ret;
}

}}}}
