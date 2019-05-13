#include "rus_prover_unify_step.hpp"
#include "rus_prover_unify_general.hpp"

#include "../rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify { namespace {

struct UnifyIters {
	explicit UnifyIters(const UnifyIters& ui, const Subst& ps, const Subst& s = Subst()) :
		indexIter(ui.indexIter), termIter(ui.termIter), parentSub(ps), sub(s) { }
	explicit UnifyIters(const UnifyIters& ui, const Subst& ps, Subst&& s) :
		indexIter(ui.indexIter), termIter(ui.termIter), parentSub(ps), sub(std::move(s)) { }
	explicit UnifyIters(UnifyIters&& ui, const Subst& ps, Subst&& s) :
		indexIter(std::move(ui.indexIter)), termIter(std::move(ui.termIter)), parentSub(ps), sub(std::move(s)) {	}
	explicit UnifyIters(const Index::Iter& ii, const Term::Iter& ti, const Subst& ps = Subst(), const Subst& s = Subst()) :
		indexIter(ii), termIter(ti), parentSub(ps), sub(s) { }

	explicit UnifyIters(const UnifyIters&) = default;
	explicit UnifyIters(UnifyIters&&) = default;

	UnifyIters& operator = (const UnifyIters&) = default;
	UnifyIters& operator = (UnifyIters&&) = default;

	UnifyIters side() const {
		return UnifyIters(indexIter.side(), termIter, parentSub, parentSub);
	}
	UnifyIters next() const {
		return UnifyIters(indexIter.next(), termIter.next(), sub, sub);
	}
	bool isNextEnd() const {
		if (!sub.ok()) {
			return true;
		}
		return indexIter.isNextEnd() || termIter.isNextEnd();
	}
	bool isTermEnd(const UnifyIters& ends) const {
		if (!sub.ok()) {
			return true;
		}
		return ends.indexIter.isEnd(indexIter) && ends.termIter.isEnd(termIter);
	}
	void showTermEnd(const UnifyIters& ends) const {
		cout << "Index iter:" << endl;
		cout << "\t" << (ends.indexIter.isEnd(indexIter) ? "END" : "X" ) << endl;
		cout << "Term iter:" << endl;
		cout << "\t" << (ends.termIter.isEnd(termIter) ? "END" : "X" ) << endl;
	}
	bool isNextEnd(const UnifyIters& ends) const {
		if (!sub.ok()) {
			return true;
		}
		return isNextEnd() || ends.indexIter.isEnd(indexIter) || ends.termIter.isEnd(termIter);
	}
	bool isSideEnd() const {
		if (!sub.ok()) {
			return true;
		}
		return indexIter.isSideEnd();
	}
	bool isValid() const {
		if (!sub.ok()) {
			return false;
		}
		return indexIter.isValid() && termIter.isValid();
	}
	Term subTerm() const {
		return termIter.subTerm();
	}

	string show(bool full = false) const {
		ostringstream oss;
		oss << "Index iter:" << endl;
		if (full) {
			auto j = indexIter;
			vector<Index::Iter> branch;
			while (j != Index::Iter()) {
				branch.push_back(j);
				j = j.prev();
			}
			reverse(branch.begin(), branch.end());
			oss << "\t: ";
			for (auto x : branch) {
				oss << x.show();
			}
			oss << endl;
		} else {
			if (indexIter.isValid()) {
				oss << "\titer: " << indexIter.show() << endl;
			} else {
				oss << "\titer: NOT VALID " << indexIter.show() << endl;
			}
		}
		oss << "Term iter:" << endl;
		if (termIter.isValid()) {
			oss << "\titer: " << termIter.show() << endl;
		} else {
			oss << "\titer: NOT VALID " << termIter.show() << endl;
		}
		oss << "sub: " << endl;
		oss << Indent::paragraph(sub.show()) << endl;
		oss << "parentSub: " << endl;
		oss << Indent::paragraph(parentSub.show()) << endl;
		return oss.str();
	}
	string showTree() const {
		ostringstream oss;
		oss << "Index iter:" << endl;
		oss << Indent::paragraph(indexIter.showTree()) << endl;
		oss << "Term iter:" << endl;
		oss << Indent::paragraph(termIter.showTree()) << endl;
		return oss.str();
	}
	vector<uint> inds() const {
		return indexIter.iter()->second.inds;
	}

	bool operator == (const UnifyIters& ui) const {
		return indexIter == ui.indexIter && termIter == ui.termIter;
	}
	bool operator != (const UnifyIters& ui) const {
		return !operator == (ui);
	}

	bool equals() const {
		return indexIter.ruleVar() == termIter.ruleVar();
	}
	bool termVar() const {
		return
			termIter.ruleVar().isVar() &&
			termIter.ruleVar().var.rep &&
			*indexIter.ruleVar().var.type <= *termIter.ruleVar().var.type;
	}
	bool indexVar() const {
		return
			indexIter.ruleVar().isVar() &&
			indexIter.ruleVar().var.rep &&
			*termIter.ruleVar().var.type <= *indexIter.ruleVar().var.type;
	}

	Index::Iter indexIter;
	Term::Iter  termIter;
	Subst parentSub;
	Subst sub;
};

string show(const vector<UnifyIters>& vi) {
	string ret;
	for (const auto& ui : vi) {
		ret += ui.show(true) + "\n";
	}
	return ret;
}

inline void dump(const vector<UnifyIters>& vi, const char* msg = "") {
	cout << msg << endl;
	cout << show(vi) << endl;
}

inline void dump(const UnifyIters& ui, const char* msg = "") {
	cout << msg << endl;
	cout << ui.show(true) << endl;
}

struct UnifyPair {
	UnifyPair(const UnifyIters& b) : is_root(true), beg(b), end(b) { }
	UnifyPair(const UnifyIters& b, const UnifyIters& e) : is_root(false), beg(b), end(e) { }
	UnifyPair(const UnifyIters& b, UnifyIters&& e) : is_root(false), beg(b), end(std::move(e)) { }

	UnifyPair(const UnifyPair&) = default;
	UnifyPair(UnifyPair&&) = default;

	Term subTerm() const {
		return beg.subTerm();
	}
	string show() const {
		ostringstream oss;
		oss << "beg: " << beg.show();
		oss << "cur: " << end.show();
		oss << "term: " << subTerm().show();
		return oss.str();
	}

	bool is_root;
	UnifyIters beg;
	UnifyIters end;
};

static vector<UnifyPair> do_unify_index_term(const UnifyIters& begins);

bool debug_unify = false;

static vector<UnifyIters> unify_iters_index_term(const UnifyIters& i) {
	vector<UnifyIters> ret;
	if (i.equals()) {
		ret.emplace_back(i);
	} else if (i.indexVar()) {
		Subst s = unify_step(i.sub, {i.indexIter.ruleVar().var.lit}, i.sub.apply(i.termIter.subTerm()));
		s.compose(i.sub.complement(s.dom()));
		if (s.ok()) {
			ret.emplace_back(i.indexIter, i.termIter.end(), i.parentSub, std::move(s));
		}
	} else if (i.termVar()) {
		for (const auto& end : i.indexIter.ends()) {
			Subst s = unify_step(i.sub, {i.termIter.ruleVar().var.lit}, i.sub.apply(i.indexIter.subTerm(end)));
			s.compose(i.sub.complement(s.dom()));
			if (s.ok()) {
				ret.emplace_back(end, i.termIter, i.parentSub, std::move(s));
			}
		}
	}
	return ret;
}

static vector<UnifyPair> do_unify_index_term(const UnifyIters& inits) {
	vector<UnifyPair> ret;
	stack<UnifyPair> st;
	st.emplace(inits);
	while (st.size()) {
		UnifyPair p = std::move(st.top());
		st.pop();
		for (auto& i : unify_iters_index_term(p.end)) {
			if (i.isTermEnd(p.beg) && i.sub.ok()) {
				ret.emplace_back(p.beg, i);
			}
			if (!i.isNextEnd(p.beg)) {
				st.emplace(p.beg, i.next());
			}
		}
		if (!p.end.isSideEnd()) {
			if (p.is_root) {
				st.emplace(p.end.side());
			} else {
				st.emplace(p.beg, p.end.side());
			}
		}
	}
	return ret;
}

}

void check_index_term_unification(const Index& ind, const Term& term, const map<uint, TermSubst>& result);

map<uint, TermSubst> unify_index_term(const Index& ind, const Term& term) {

	UnifyIters iters(ind.root(), term);

	map<uint, TermSubst> ret;

	Timer timer;
	auto unified = do_unify_index_term(iters);
	add_timer_stats("do_unify_index_term", timer);

	timer.start();
	for (auto& pair : unified) {
		const UnifyIters& end = pair.end;
		Timer t;
		Term term = end.sub.apply(pair.subTerm());
		add_timer_stats("unify_general_extract_subterm", timer);

		t.start();
		for (auto ind : end.inds()) {
			ret.emplace(ind, TermSubst(std::move(term), std::move(end.sub)));
		}
		add_timer_stats("unify_general_emplace_term_subst", timer);
	}
	add_timer_stats("unify_general_arrange_ret", timer);

	check_index_term_unification(ind, term, ret);
	return ret;
}

string show_index_term_unification_args(const Index& ind, const Term& term) {
	ostringstream oss;
	oss << "index:" << endl;
	oss << "---------" << endl;
	oss << Indent::paragraph(ind.show()) << endl;
	oss << "term: " << endl;
	oss << "---------" << endl;
	oss << term.show() << endl;
	return oss.str();
}

string show_index_term_unification_result(const map<uint, TermSubst>& result) {
	ostringstream oss;
	oss << "result:" << endl;
	oss << "---------" << endl;
	for (const auto& p : result) {
		oss << p.first << " --> " << p.second.show() << endl;
	}
	return oss.str();
}

void check_index_term_unification(const Index& ind, const Term& term, const map<uint, TermSubst>& result) {
	Index::Unpacked unpacked = ind.unpack();
	for (const auto& p : result) {
		uint key = p.first;
		const TermSubst& ts = p.second;
		Term t;
		for (const auto& p : unpacked) {
			for (uint k : p.second) {
				if (k == key) {
					t = p.first;
					break;
				}
			}
		}
		if (t.empty()) {
			string msg;
			msg += "no key " + to_string(key) + " in unpacked inds\n";
			msg += "unif. term:   " + ts.term.show() + "\n";
			msg += "unif. subst:\n";
			msg += Indent::paragraph(ts.sub.show()) + "\n";
			msg += "unpacked index:\n";
			for (const auto& p : unpacked) {
				msg += "\t" + p.first.show() + " --> " + prover::show(p.second) + "\n";
			}
			msg += show_index_term_unification_args(ind, term);
			msg += show_index_term_unification_result(result);
			throw Error(msg);
		}
		Term applied_ind = ts.sub.apply(t);
		if (applied_ind != ts.term) {
			string msg;
			msg += "wrong index unification: " + applied_ind.show() + " != " + ts.term.show() + "\n";
			msg += "orig. term:   " + t.show() + "\n";
			msg += "applied term: " + applied_ind.show() + "\n";
			msg += "unif. term:   " + ts.term.show() + "\n";
			msg += "unif. subst:\n";
			msg += Indent::paragraph(ts.sub.show()) + "\n";
			throw Error(msg);
		}

		Term applied_term = ts.sub.apply(term);
		if (applied_term != ts.term) {
			string msg;
			msg += "wrong term unification: " + applied_term.show() + " != " + ts.term.show() + "\n";
			msg += "orig. term:   " + term.show() + "\n";
			msg += "applied term: " + applied_term.show() + "\n";
			msg += "unif. term:   " + ts.term.show() + "\n";
			msg += "unif. subst:\n";
			msg += Indent::paragraph(ts.sub.show()) + "\n";
			throw Error(msg);
		}
	}
}

}}}}
