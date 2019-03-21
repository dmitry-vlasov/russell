#include "../rus_prover_cartesian.hpp"
#include "rus_prover_trie_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

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

vector<UnifyIters> unify_general_2(const UnifyIters& begins);

FlatTerm unify_step_1(FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term) {

	if (debug_flat_unify) {
		cout << "vars: ";
		for (auto w : vars) {
			cout << "'" << prover::show(w) << "' ";
		}
		cout << endl;
		cout << "term: " << term.show() << endl;
		cout << "s: " << s.show() << endl;
	}

	vector<FlatTerm> to_unify({apply(s, term)});
	for (auto v : vars) {
		if (s.maps(v)) {
			const FlatTerm& t = s.map(v);
			if (!t.empty()) {
				to_unify.push_back(t);
			} else {
				throw Error("empty term at unify_step_1");
			}
		}
	}
	vector<MultyIter> iters;
	for (const auto& t : to_unify) {
		iters.emplace_back(FlatTerm::TermIter(t));
	}
	UnifyIters begin = UnifyIters(iters);
	try {
		vector<UnifyIters> ends = unify_general_2(begin);
		assert(ends.size() <= 1);
		if (ends.size() > 0) {
			UnifyIters end = ends[0];
			s.bicompose(end.sub);
			FlatTerm term_orig = begin.iters[0].subTerm(end.iters[0]);
			FlatTerm unified = apply(end.sub, term_orig);
			for (auto v : vars) {
				if (!s.compose(FlatSubst(v, unified))) {
					if (debug_flat_unify) {
						cout << "!s.compose(FlatSubst(v, unified))" << endl;
						cout << "v: " << prover::show(v) << endl;
						cout << "s: " << s.show() << endl;
					}
					return FlatTerm();
				}
			}
			return unified;
		}
		if (debug_flat_unify) {
			cout << "unified.empty()" << endl;
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
	return FlatTerm();
}

FlatSubst unify_step_1(const FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term) {
	FlatSubst ret(s);
	FlatTerm unified = unify_step_1(ret, vars, term);
	return unified.empty() ? FlatSubst(false) : ret;
}

bool verify_begins_ends(const UnifyIters& begs, const UnifyIters& ends) {
	if (begs.iters.size() != ends.iters.size()) {
		cout << "begs.iters.size() != ends.iters.size()" << endl;
		return false;
	}
	for (uint i = 0; i < begs.iters.size(); ++ i) {
		MultyIter beg = begs.iters[i];
		MultyIter end = ends.iters[i];
		MultyIter cur = end;
		bool is_ok = false;
		uint c = 0;
		while (cur != MultyIter()) {
			if (cur == beg) {
				is_ok = true;
				break;
			}
			cur = cur.prev();
			c++;
			if (c == 2048) {
				cout << "TOO MUCH C" << endl;
				c = 0;
				MultyIter x = end;
				while (x != MultyIter()) {
					cout <<  c << " -- x: " << x.ruleVar().show() << endl;
					if (x == beg) {
						cout << "WTF?..." << endl;
						break;
					}
					x = x.prev();
					c++;
					if (c == 2048) {
						cout << "FUCK THE MIDDLE EAST" << endl;
						return false;
					}
				}
				return false;
			}
		}
		if (!is_ok) {
			//cout << "NON REACHEABLE" << endl;
			return false;
		}
	}
	return true;
}

vector<UnifyIters> unify_iters_2(const UnifyIters& i) {
	vector<UnifyIters> ret;
	if (i.equals()) {
		ret.emplace_back(i);
	} else {
		UnifStepData<MultyIter> data(i.iters);
		if (data.consistent) {
			if (data.rule) {
				UnifyIters subBegins(data.subGoals(), i.parentSub, i.sub);
				vector<UnifyIters> subEnds = unify_general_2(subBegins);
				for (const auto& ends : subEnds) {
					MultyIter i0 = ends.iters[0];
					FlatTerm term_orig = subBegins.iters[0].subTerm(i0);
					FlatTerm term_applied = apply(ends.sub, term_orig);
					FlatSubst s = unify_step_1(i.sub, data.vars, term_applied);
					if (s.ok()) {
						ret.emplace_back(data.shiftGoals(ends.iters), i.parentSub, s);
					}
				}
			} else {
				FlatSubst s = unify_step_1(i.sub, data.vars, FlatTerm(data.const_.is_def() ? data.const_ : data.var));
				if (s.ok()) {
					ret.emplace_back(i.iters, i.parentSub, s);
				}
			}
		}
	}
	return ret;
}


vector<UnifyIters> unify_general_2(const UnifyIters& inits) {

	//if (debug_trie_index) {
	//	dump(inits, "unify_general_1: begins");
	//}

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
				//if (debug_trie_index) {
				//	dump(p.cur, "unify_general_1: n");
				//}
				st.pop();
				for (const auto& i : unify_iters_2(p.cur)) {
					/*if (i.isTermEndOld(p.beg) && i.sub.ok && !i.isTermEnd(p.beg)) {
						if (debug_trie_index) {
							dump(i, "i.isTermEndOld(begins) && i.sub.ok && !i.isTermEnd(begins)");
							cout << "i.showTermEnd(begins): " << endl;
							i.showTermEnd(p.beg);
							dump(p.beg, "begins:");
						}
					}*/

					if (i.isTermEnd(p.beg) && i.sub.ok()) {
						//if (debug_trie_index) {
						//	dump(i, "if (i.isTermEnd(begins) && i.sub.ok)");
						//}
						verify_begins_ends(p.beg, i);
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
	for (const auto& end : unify_general_2(begin)) {
		FlatTerm term = apply(end.sub, begin.iters[0].subTerm(end.iters[0]));
		for (auto ind :  end.inds()) {
			ret.emplace(ind, FlatTermSubst(term, end.sub));
		}
		//if (debug_trie_index) {
		//	dump(end, "unify_general RESULT:  end");
		//}
	}
	return ret;
}

}}}}
