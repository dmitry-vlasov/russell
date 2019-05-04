#include "../rus_prover_cartesian.hpp"
#include "rus_prover_index_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

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

struct UnifyPair {
	UnifyPair(const UnifyIters& b) : is_root(true), beg(b), end(b) { }
	UnifyPair(const UnifyIters& b, const UnifyIters& c) : is_root(false), beg(b), end(c) { }

	Term subTerm() const {
		return beg.iters[0].subTerm(end.iters[0]);
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

static vector<UnifyPair> do_unify_general(const UnifyIters& begins);
static vector<UnifyPair> do_unify_general_with_hint(const UnifyIters& inits, const Term& hint);

static Term unify_step(Subst& s, const vector<uint>& vars, const Term& term) {
	vector<Term> to_unify({s.apply(term)});
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
		iters.emplace_back(Term::Iter(t));
	}
	UnifyIters begin = UnifyIters(iters);
	try {
		vector<UnifyPair> pairs = do_unify_general(begin);
		if (pairs.size() > 1) {
			throw Error("too much unified pairs: " + to_string(pairs.size()));
		}
		if (pairs.size() == 1) {
			const UnifyPair& pair = pairs[0];
			s.compose(pair.end.sub);
			Term term_orig = pair.subTerm();
			Term unified = pair.end.sub.apply(term_orig);
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

template<class Iter>
struct UnifStepData {
	enum Kind { VAR, RULE, CONST_VAR };
	const Rule* rule = nullptr;
	vector<uint> vars;
	const Type* least_type = nullptr;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;
	vector<Kind> kinds;
	vector<Iter> iters;

	vector<Iter> subGoals() const {
		vector<Iter> ret;
		assert(kinds.size() == iters.size());
		for (uint i = 0; i < kinds.size(); ++ i) {
			if (kinds[i] == RULE) {
				ret.push_back(iters[i]);
			}
		}
		return ret;
	}

	vector<Iter> shiftGoals(const vector<Iter>& ends) const {
		vector<Iter> ret;
		assert(kinds.size() == iters.size());
		for (uint i = 0, j = 0; i < kinds.size(); ++ i) {
			if (kinds[i] == RULE) {
				ret.push_back(ends[j++]);
			} else {
				ret.push_back(iters[i]);
			}
		}
		return ret;
	}

	UnifStepData(const vector<Iter>& is) : iters(is) {
		least_type = ruleVar(*is.begin()).type();
		for (uint k = 0; k < is.size(); ++ k) {
			if (!(*least_type <= *(ruleVar(is[k]).type()))) {
				// There's no unification because of type constraints
				return;
			}
			if (ruleVar(is[k]).isVar()) {
				if (!track_var(ruleVar(is[k]).var)) {
					return;
				}
			} else {
				if (!track_node(is[k])) {
					return;
				}
			}
		}
		consistent = true;
	}

	bool track_var(LightSymbol v) {
		if (v.rep) {
			if (var.is_undef()) {
				var = v;
				kinds.push_back(VAR);
			} else {
				kinds.push_back(CONST_VAR);
			}
			// Collect replaceable variables
			vars.push_back(v.lit);
		} else {
			kinds.push_back(CONST_VAR);
			if (const_.is_undef()) {
				const_ = v;
			} else if (const_ != v) {
				// If we have any non-replaceable variables (constant), all other
				// constants must be the same variable (constant).
				return false;
			}
			if (rule) {
				// If we have any non-replaceable variables (constant),
				// complex terms are not allowed.
				return false;
			}
		}
		return true;
	}
	bool track_node(Iter i) {
		if (const_.is_def()) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		if (!rule) {
			rule = ruleVar(i).rule;
		} else if (rule != ruleVar(i).rule) {
			// In case we have a non-leaf with some rule,
			// all other leafs must be with the same rule.
			return false;
		}
		kinds.push_back(RULE);
		return true;
	}

	string show() const {
		cout << "rule: " << (rule ? Lex::toStr(rule->id()) : "NULL") << endl;
		cout << "vars: " << flush;
		for (const auto& v : vars) {
			cout << Lex::toStr(v) << " " << flush;
		}
		cout << endl;
		cout << "consistent: " << (consistent ? "TRUE" : "FALSE") << endl;
		cout << "var: " << prover::show(var, true) << endl;
		cout << endl;

		string ret;
		ret += "rule: " + (rule ? Lex::toStr(rule->id()) : "NULL") + "\n";
		ret += "vars: ";
		for (const auto& v : vars) {
			ret += Lex::toStr(v) + " ";
		}
		ret += "\n";
		ret += string("consistent: ") + (consistent ? "TRUE" : "FALSE") + "\n";
		ret += string("var: ") + prover::show(var, true) + "\n";
		ret += "\n";
		return ret;
	}
};

bool debug_unify = false;

static vector<UnifyIters> unify_iters(const UnifyIters& i) {
	vector<UnifyIters> ret;
	if (i.equals()) {
		ret.emplace_back(i);
	} else {
		UnifStepData<MultyIter> data(i.iters);
		if (data.consistent) {
			if (data.rule) {
				UnifyIters subBegins(data.subGoals(), i.parentSub, i.sub);
				//vector<UnifyPair> pairs1 = i.sub.maps(data.var) && i.sub.map(data.var).kind() == Term::RULE ?
				//	do_unify_general_with_hint(subBegins, i.sub.map(data.var)) :
				//	do_unify_general(subBegins);

				if (i.sub.maps(data.var) && i.sub.map(data.var).kind() == Term::RULE) {
					subBegins.iters.emplace_back(Term::Iter(i.sub.map(data.var)));
				}


				vector<UnifyPair> pairs = do_unify_general(subBegins);
				for (const auto& pair : pairs) {
					try {
						Term term_orig = pair.subTerm();
						term_orig.verify();
						Term term_applied = pair.end.sub.apply(term_orig);
						Subst s = unify_step(i.sub, data.vars, term_applied);
						s.compose(pair.end.sub.complement(s.dom()));
						if (s.ok()) {

							/*bool found = false;
							for (const auto& p : pairs1) {
								if (p.end == pair.end) {
									found = true;
									if (p.end.sub.ok() != pair.end.sub.ok()) {
										cout << "subs differ:" << endl;
										cout << "p.end.sub: " << endl << Indent::paragraph(p.end.sub.show()) << endl;
										cout << "pair.end.sub: " << endl << Indent::paragraph(pair.end.sub.show()) << endl;
										exit(0);
									}
								}
							}
							if (!found) {
								cout << "pair:" << endl;
								cout << pair.show() << endl;
								cout << "is not found" << endl;
								cout << endl;
								cout << "term_orig: " << term_orig.show() << endl;
								cout << "term_applied: " << term_applied.show() << endl;
								cout << "subst: " << endl << Indent::paragraph(s.show()) << endl;
								cout << "i.sub: " << endl << Indent::paragraph(i.sub.show()) << endl;
								cout << endl;
								cout << "hint: " << i.sub.map(data.var).show() << endl;
								cout << "i: " << endl;
								cout << i.showTree() << endl;
								cout << i.show(true) << endl;
								cout << endl;
								cout << data.show() << endl;
								cout << "-----------------------" << endl;

								debug_unify = true;
								do_unify_general_with_hint(subBegins, i.sub.map(data.var));

								exit(0);
							}*/

							ret.emplace_back(data.shiftGoals(pair.end.iters), i.parentSub, s);
						}
					} catch (Error& err) {
						err.msg += pair.show() + "\n";
						throw err;
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

static vector<UnifyPair> do_unify_general(const UnifyIters& inits) {
	vector<UnifyPair> ret;
	if (inits.iters.size() > 0) {
		if (inits.iters.size() == 1) {
			for (const auto& end : inits.iters[0].ends()) {
				UnifyIters ends(vector<MultyIter>(1, end), inits.parentSub, inits.sub);
				ret.emplace_back(inits, std::move(ends));
			}
		} else {
			stack<UnifyPair> st;
			st.emplace(inits);
			while (st.size()) {
				UnifyPair p = st.top();
				st.pop();
				for (const auto& i : unify_iters(p.end)) {
					if (i.isTermEnd(p.beg) && i.sub.ok()) {
						ret.push_back(UnifyPair(p.beg, i));
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
		}
	}
	return ret;
}

static vector<UnifyPair> do_unify_general_with_hint(const UnifyIters& inits, const Term& hint) {
	vector<UnifyPair> ret;
	if (inits.iters.size() > 0) {
		struct UnifyPairWithHint {
			UnifyPairWithHint(const UnifyIters& b, Term::Iter h) : pair(b), hint_(h) {
				if (hint_.ruleVar().rule) {
					pair.end.setHint(hint_.ruleVar().rule);
				}
			}
			UnifyPairWithHint(const UnifyIters& b, const UnifyIters& c, Term::Iter h) : pair(b, c), hint_(h) {
				if (hint_.ruleVar().rule) {
					pair.end.setHint(hint_.ruleVar().rule);
				}
			}
			bool useHint() const {
				return hint_.ruleVar().rule;
			}
			string show() const {
				ostringstream oss;
				oss << pair.show() << endl;
				oss << "hint: " << hint_.show() << endl;
				return oss.str();
			}
			UnifyPair  pair;
			Term::Iter hint_;
		};
		stack<UnifyPairWithHint> st;
		st.emplace(inits, Term::Iter(hint));
		while (st.size()) {
			UnifyPairWithHint t = st.top();
			st.pop();
			if (!t.pair.end.isValid()) {
				if (debug_unify) {
					cout << t.show() << endl;
				}
				continue;
			}
			for (const auto& i : unify_iters(t.pair.end)) {
				if (i.isTermEnd(t.pair.beg) && i.sub.ok()) {
					ret.push_back(UnifyPair(t.pair.beg, i));
				}
				Term::Iter pass_mapped(t.hint_);
				if (debug_unify) {
					cout << "t.hint_ = " << t.hint_.show() << endl;
					cout << "i.sub = " << endl << Indent::paragraph(i.sub.show()) << endl;
				}
				if (t.hint_.isVar() && i.sub.maps(t.hint_.var().lit)) {
					uint len = i.sub.map(t.hint_.var().lit).len();
					if (debug_unify) {
						cout << "LEN: " << len << endl;
					}
					while (len --) {
						pass_mapped = pass_mapped.next();
					}
				}
				if (!i.isNextEnd(t.pair.beg)) {
					st.emplace(t.pair.beg, i.next(), pass_mapped.next());
				}
			}
			if (!t.pair.end.isSideEnd()) {
				if (t.pair.is_root) {
					st.emplace(t.pair.end.side(), t.hint_);
				} else {
					st.emplace(t.pair.beg, t.pair.end.side(), t.hint_);
				}
			}
		}
	}
	return ret;
}


/*
static vector<UnifyPair> do_unify_general_with_hint(const UnifyIters& inits, const Term& hint) {
	//cout << "do_unify_general_with_hint: [" << hint.show(false) << "]   ===   [" << hint.show(true) << "]" << endl;
	//cout << "HINT ITER: " << Term::Iter(hint).show() << endl;
	//cout << "inits.iters.size(): " << inits.iters.size() << endl;

	vector<UnifyPair> ret;
	if (inits.iters.size() > 0) {
		/*if (inits.iters.size() == 1) {
			for (const auto& end : inits.iters[0].ends()) {
				ret.emplace_back(vector<MultyIter>(1, end), inits.parentSub, inits.sub);
			}
		} else {* /
			struct UnifyPairWithHint {
				UnifyPairWithHint(const UnifyIters& b, Term::Iter h) : pair(b), hint_(h) { }
				UnifyPairWithHint(const UnifyIters& b, const UnifyIters& c, Term::Iter h) : pair(b, c), hint_(h) { }

				bool useHint() const {
					if (!hint_.ruleVar().rule) {
						return false;
					} else {
						return hint() != pair.end;
					}
				}
				UnifyIters hint() const {
					return pair.end.hint(hint_.ruleVar().rule);
				}
				UnifyPair  pair;
				Term::Iter hint_;
			};
			Term::Iter hiter(hint);
			UnifyIters start = hiter.ruleVar().rule ? inits.hint(hiter.ruleVar().rule) : inits;
			if (!start.isValid()) {
				return ret;
			}

			stack<UnifyPairWithHint> st;
			st.emplace(start, hiter);
			uint c = 0;
			while (st.size()) {
				++c;
				if (c > 10000) {
					cout << "C IS TOO MUCH..." << endl;
					exit(0);
				}
				UnifyPairWithHint t = st.top();
				st.pop();
				for (const auto& i : unify_iters(t.pair.end)) {
					if (i.isTermEnd(t.pair.beg) && i.sub.ok()) {
						ret.push_back(UnifyPair(t.pair.beg, i));
					}
					if (!i.isNextEnd(t.pair.beg)) {
						//cout << "Next hint: " << t.hint.next().show() << endl;
						st.emplace(t.pair.beg, i.next(), t.hint_.next());
					} else {
						//cout << "hint end: " << t.hint.next().show() << endl;
					}
				}
				if (!t.pair.end.isSideEnd()) {
					if (t.pair.is_root) {
						if (t.useHint()) {
							cout << "USING HINT" << endl;
							st.emplace(t.hint(), t.hint_);
						} else {
							st.emplace(t.pair.end.side(), t.hint_);
						}
					} else {
						if (t.useHint()) {
							cout << "USING HINT" << endl;
							st.emplace(t.pair.beg, t.hint(), t.hint_);
						} else {
							st.emplace(t.pair.beg, t.pair.end.side(), t.hint_);
						}
					}
				}
			//}
		}
	}
	return ret;
}
*/

map<vector<uint>, TermSubst> unify_general(const UnifyIters& begin) {
	map<vector<uint>, TermSubst> ret;
	Timer timer;
	auto unified = do_unify_general(begin);
	add_timer_stats("do_unify_general", timer);

	timer.start();
	for (const auto& pair : unified) {
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
	return ret;
}

}}}}
