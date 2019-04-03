#include "../rus_prover_cartesian.hpp"
#include "rus_prover_index_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

bool debug_flat_unify = false;

vector<vector<uint>> UnifyIters::inds() const {
	CartesianProd<uint> inds_prod;
	for (const auto& i : iters) {
		inds_prod.addDim(i.inds());
	}
	vector<vector<uint>> ret;
	while (true) {
		ret.push_back(inds_prod.data());
		if (!inds_prod.hasNext()) {
			break;
		}
		inds_prod.makeNext();
	}
	return ret;
}

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

static vector<UnifyIters> do_unify_general(const UnifyIters& begins);

static Term unify_step(Subst& s, const vector<uint>& vars, const Term& term) {
	vector<Term> to_unify({apply(s, term)});
	for (auto v : vars) {
		if (s.maps(v)) {
			const Term& t = s.map(v);
			if (!t.empty()) {
				to_unify.push_back(t);
			} else {
				throw Error("empty term at unify_step_1");
			}
		}
	}
	vector<MultyIter> iters;
	for (const auto& t : to_unify) {
		iters.emplace_back(Term::TermIter(t));
	}
	UnifyIters begin = UnifyIters(iters);
	try {
		vector<UnifyIters> ends = do_unify_general(begin);
		assert(ends.size() <= 1);
		if (ends.size() > 0) {
			UnifyIters end = ends[0];
			s.compose(end.sub);
			Term term_orig = begin.iters[0].subTerm(end.iters[0]);
			Term unified = apply(end.sub, term_orig);
			for (auto v : vars) {
				if (!s.compose(Subst(v, unified))) {
					return Term();
				}
			}
			return unified;
		}
	} catch (Error& err) {
		cout << endl << "unify_step_1: ERROR" << endl;
		for (const auto& t : to_unify) {
			cout << "TERM: " << endl;
			cout << t.show_pointers();
		}
		cout << endl;
		throw err;
	}
	return Term();
}

static Subst unify_step(const Subst& s, const vector<uint>& vars, const Term& term) {
	Subst ret(s);
	Term unified = unify_step(ret, vars, term);
	return unified.empty() ? Subst(false) : ret;
}

static vector<UnifyIters> unify_iters(const UnifyIters& i) {
	vector<UnifyIters> ret;
	if (i.equals()) {
		ret.emplace_back(i);
	} else {
		UnifStepData<MultyIter> data(i.iters);
		if (data.consistent) {
			if (data.rule) {
				UnifyIters subBegins(data.subGoals(), i.parentSub, i.sub);
				vector<UnifyIters> subEnds = do_unify_general(subBegins);
				for (const auto& ends : subEnds) {
					MultyIter i0 = ends.iters[0];
					Term term_orig = subBegins.iters[0].subTerm(i0);
					Term term_applied = apply(ends.sub, term_orig);
					Subst s = unify_step(i.sub, data.vars, term_applied);
					s.compose(ends.sub.complement(s.dom()));
					if (s.ok()) {
						ret.emplace_back(data.shiftGoals(ends.iters), i.parentSub, s);
					}
				}
			} else {
				Subst s = unify_step(i.sub, data.vars, Term(data.const_.is_def() ? data.const_ : data.var));
				if (s.ok()) {
					ret.emplace_back(i.iters, i.parentSub, s);
				}
			}
		}
	}
	return ret;
}

static vector<UnifyIters> do_unify_general(const UnifyIters& inits) {
	vector<UnifyIters> ret;
	if (inits.iters.size() > 0) {
		if (inits.iters.size() == 1) {
			for (const auto& end : inits.iters[0].ends()) {
				ret.emplace_back(vector<MultyIter>(1, end), inits.parentSub, inits.sub);
			}
		} else {
			struct UnifyPair {
				UnifyPair(const UnifyIters& b) : is_root(true), beg(b), cur(b) { }
				UnifyPair(const UnifyIters& b, const UnifyIters& c) : is_root(false), beg(b), cur(c) { }
				bool is_root;
				UnifyIters beg;
				UnifyIters cur;
			};
			stack<UnifyPair> st;
			st.emplace(inits);
			while (st.size()) {
				UnifyPair p = st.top();
				st.pop();
				for (const auto& i : unify_iters(p.cur)) {
					if (i.isTermEnd(p.beg) && i.sub.ok()) {
						ret.push_back(i);
					}
					if (!i.isNextEnd(p.beg)) {
						st.emplace(p.beg, i.next());
					}
				}
				if (!p.cur.isSideEnd()) {
					if (p.is_root) {
						st.emplace(p.cur.side());
					} else {
						st.emplace(p.beg, p.cur.side());
					}
				}
			}
		}
	}
	return ret;
}

map<vector<uint>, FlatTermSubst> unify_general(const UnifyIters& begin) {
	map<vector<uint>, FlatTermSubst> ret;
	for (const auto& end : do_unify_general(begin)) {
		Term term = apply(end.sub, begin.iters[0].subTerm(end.iters[0]));
		for (auto ind :  end.inds()) {
			ret.emplace(ind, FlatTermSubst(term, end.sub));
		}
	}
	return ret;
}

}}}}
