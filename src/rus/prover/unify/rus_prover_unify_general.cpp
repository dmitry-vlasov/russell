#include "rus_prover_unify_general.hpp"

#include "../rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

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
	explicit UnifyIters(const UnifyIters& ui, const Subst& ps, Subst&& s) :
		indexIters(ui.indexIters), termIters(ui.termIters), parentSub(ps), sub(std::move(s)) { }
	explicit UnifyIters(UnifyIters&& ui, const Subst& ps, Subst&& s) :
		indexIters(std::move(ui.indexIters)), termIters(std::move(ui.termIters)), parentSub(ps), sub(std::move(s)) {	}
	explicit UnifyIters(const vector<Index::Iter>& ii, const Subst& ps = Subst(), const Subst& s = Subst()) :
		indexIters(ii), parentSub(ps), sub(s) { }
	explicit UnifyIters(const vector<Term::Iter>& ti, const Subst& ps = Subst(), const Subst& s = Subst()) :
		termIters(ti), parentSub(ps), sub(s) { }
	explicit UnifyIters(const vector<Index::Iter>& ii, const vector<Term::Iter>& ti, const Subst& ps = Subst(), const Subst& s = Subst()) :
		indexIters(ii), termIters(ti), parentSub(ps), sub(s) { }

	explicit UnifyIters(const UnifyIters&) = default;
	explicit UnifyIters(UnifyIters&&) = default;

	UnifyIters& operator = (const UnifyIters&) = default;
	UnifyIters& operator = (UnifyIters&&) = default;

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
		oss << "Index iters:" << endl;
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
		oss << "Term iters:" << endl;
		n = 0;
		for (const auto& i : termIters) {
			if (isValid()) {
				oss << "\t" << n << "-iter: " << i.show() << endl;
			} else {
				oss << "\t" << n << "-iter: NOT VALID " << i.show() << endl;
			}
			++n;
		}
		oss << "sub: " << endl;
		oss << Indent::paragraph(sub.show()) << endl;
		oss << "parentSub: " << endl;
		oss << Indent::paragraph(parentSub.show()) << endl;
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

	const vector<Index::Iter> indexIters;
	const vector<Term::Iter>  termIters;
	const Subst parentSub;
	const Subst sub;
};


vector<vector<uint>> UnifyIters::inds() const {
	CartesianProd<uint> inds_prod;
	for (const auto& i : indexIters) {
		inds_prod.addDim(i.iter()->second.inds);
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
	UnifyPair(const UnifyIters& b, const UnifyIters& e) : is_root(false), beg(b), end(e) { }
	UnifyPair(const UnifyIters& b, UnifyIters&& e) : is_root(false), beg(b), end(std::move(e)) { }

	UnifyPair(const UnifyPair&) = default;
	UnifyPair(UnifyPair&&) = default;

	Term subTerm() const {
		return beg.subTerm(end);
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

struct UnifStepData {
	enum class Kind { VAR, RULE, CONST_VAR };
	enum class Origin { INDEX, TERM };
	const Rule* rule = nullptr;
	vector<uint> vars;
	const Type* least_type = nullptr;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;
	vector<Kind> indexKinds;
	vector<Kind> termKinds;
	const UnifyIters& iters;

	UnifyIters subGoals() const {
		vector<Index::Iter> indexIters;
		for (uint i = 0; i < indexKinds.size(); ++ i) {
			if (indexKinds[i] == Kind::RULE) {
				indexIters.push_back(iters.indexIters[i]);
			}
		}
		vector<Term::Iter> termIters;
		for (uint i = 0; i < termKinds.size(); ++ i) {
			if (termKinds[i] == Kind::RULE) {
				termIters.push_back(iters.termIters[i]);
			}
		}
		return UnifyIters(std::move(indexIters), std::move(termIters));
	}

	UnifyIters shiftGoals(const UnifyIters& ends) const {
		vector<Index::Iter> indexIters;
		for (uint i = 0, j = 0; i < indexKinds.size(); ++ i) {
			if (indexKinds[i] == Kind::RULE) {
				indexIters.push_back(ends.indexIters[j++]);
			} else {
				indexIters.push_back(iters.indexIters[i]);
			}
		}
		vector<Term::Iter> termIters;
		for (uint i = 0, j = 0; i < termKinds.size(); ++ i) {
			if (termKinds[i] == Kind::RULE) {
				termIters.push_back(ends.termIters[j++]);
			} else {
				termIters.push_back(iters.termIters[i]);
			}
		}
		return UnifyIters(std::move(indexIters), std::move(termIters));
	}

	UnifStepData(const UnifyIters& is) : iters(is) {
		least_type = nullptr;
		for (const auto& ii : is.indexIters) {
			if (!track_iter(ii, Origin::INDEX)) {
				return;
			}
		}
		for (const auto& ti : is.termIters) {
			if (!track_iter(ti, Origin::TERM)) {
				return;
			}
		}
		consistent = true;
	}

	template<class Iter>
	bool track_iter(Iter it, Origin o) {
		RuleVar rv = it.ruleVar();
		if (!least_type) {
			least_type = rv.type();
		} else {
			if (*least_type <= *rv.type()) {
				// ok
			} else if (*rv.type() <= *least_type) {
				least_type = rv.type();
			} else {
				// There's no unification because of type constraints
				return false;
			}
		}
		if (rv.isVar()) {
			if (!track_var(rv.var, o)) {
				return false;
			}
		} else {
			if (!track_rule(rv.rule, o)) {
				return false;
			}
		}
		return true;
	}

	bool track_var(LightSymbol v, Origin o) {
		if (v.rep) {
			if (var.is_undef()) {
				var = v;
				push_kind(Kind::VAR, o);
			} else {
				push_kind(Kind::CONST_VAR, o);
			}
			// Collect replaceable variables
			vars.push_back(v.lit);
		} else {
			push_kind(Kind::CONST_VAR, o);
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
	bool track_rule(const Rule* r, Origin o) {
		if (const_.is_def()) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		if (!rule) {
			rule = r;
		} else if (rule != r) {
			// In case we have a non-leaf with some rule,
			// all other leafs must be with the same rule.
			return false;
		}
		push_kind(Kind::RULE, o);
		return true;
	}
	void push_kind(Kind k, Origin o) {
		if (o == Origin::INDEX) {
			indexKinds.push_back(k);
		} else {
			termKinds.push_back(k);
		}
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

static vector<UnifyPair> do_unify_general(const UnifyIters& begins);
//static vector<UnifyPair> do_unify_general_with_hint(const UnifyIters& inits, const Term& hint);

static Subst unify_step(const Subst& s, const vector<uint>& vars, Term&& term) {
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
	vector<Term::Iter> iters;
	for (const auto& t : to_unify) {
		iters.emplace_back(t);
	}
	UnifyIters begin = UnifyIters(iters);
	Subst ret(s);
	try {
		vector<UnifyPair> pairs = do_unify_general(begin);
		if (pairs.size() > 1) {
			throw Error("too much unified pairs: " + to_string(pairs.size()));
		}
		if (pairs.size() == 1) {
			const UnifyPair& pair = pairs.at(0);
			if (!ret.compose(pair.end.sub)) {
				return Subst(false);
			}
			Term term_orig = pair.subTerm();
			Term unified = pair.end.sub.apply(term_orig);
			for (auto v : vars) {
				if (!ret.compose(Subst(v, unified))) {
					return Subst(false);
				}
			}
			return ret;
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
	return Subst(false);
}

bool debug_unify = false;

static vector<UnifyIters> unify_iters(const UnifyIters& i) {
	vector<UnifyIters> ret;
	if (i.equals()) {
		ret.emplace_back(i);
	} else {
		UnifStepData data(i);
		if (data.consistent) {
			if (data.rule) {
				UnifyIters subBegins(data.subGoals(), i.parentSub, i.sub);
				/*vector<UnifyPair> pairs1 = i.sub.maps(data.var) && i.sub.map(data.var).kind() == Term::RULE ?
					do_unify_general_with_hint(subBegins, i.sub.map(data.var)) :
					do_unify_general(subBegins);*/
				/*if (i.sub.maps(data.var) && i.sub.map(data.var).kind() == Term::RULE) {
					subBegins.termIters.emplace_back(i.sub.map(data.var));
				}*/
				for (auto& pair : do_unify_general(subBegins)) {
					try {
						Subst s = unify_step(i.sub, data.vars, pair.end.sub.apply(pair.subTerm()));
						s.compose(pair.end.sub.complement(s.dom()));
						if (s.ok()) {
							ret.emplace_back(data.shiftGoals(pair.end), i.parentSub, std::move(s));
						}
					} catch (Error& err) {
						err.msg += pair.show() + "\n";
						throw err;
					}
				}
			} else {
				Subst s = unify_step(i.sub, data.vars, Term(data.const_.is_def() ? data.const_ : data.var));
				if (s.ok()) {
					ret.emplace_back(i, i.parentSub, std::move(s));
				}
			}
		}
	}
	return ret;
}

static vector<UnifyPair> do_unify_general(const UnifyIters& inits) {
	vector<UnifyPair> ret;
	if (inits.size() > 0) {
		if (inits.size() == 1) {
			if (inits.indexIters.size() == 1) {
				for (const auto& end : inits.indexIters[0].ends()) {
					UnifyIters ends(vector<Index::Iter>(1, end), inits.parentSub, inits.sub);
					ret.emplace_back(inits, std::move(ends));
				}
			} else if (inits.termIters.size() == 1) {
				UnifyIters ends(vector<Term::Iter>(1, inits.termIters[0].end()), inits.parentSub, inits.sub);
				ret.emplace_back(inits, std::move(ends));
			} else {
				throw Error("impossible");
			}
		} else {
			stack<UnifyPair> st;
			st.emplace(inits);
			while (st.size()) {
				UnifyPair p = std::move(st.top());
				st.pop();
				for (auto& i : unify_iters(p.end)) {
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
		}
	}
	return ret;
}

void check_unification(const vector<const Index*>& inds, const vector<const Term*>& terms, const map<vector<uint>, TermSubst>& result);

map<vector<uint>, TermSubst> unify_general(const vector<const Index*>& inds, const vector<const Term*>& terms) {

	Timer timer;
	vector<Index::Iter> indexIters;
	for (auto i : inds) {
		indexIters.emplace_back(std::move(i->root()));
	}
	vector<Term::Iter> termIters;
	for (auto t : terms) {
		termIters.emplace_back(*t);
	}
	add_timer_stats("unify_general_create_iters", timer);

	UnifyIters iters(indexIters, termIters);

	map<vector<uint>, TermSubst> ret;

	auto unified = do_unify_general(iters);
	add_timer_stats("do_unify_general", timer);

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

	//check_unification(inds, terms, ret);
	return ret;
}




/*
struct UnifTermsStepData {
	enum class Kind { VAR, RULE, CONST_VAR };
	const Rule* rule = nullptr;
	vector<uint> vars;
	const Type* least_type = nullptr;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;
	vector<Kind> kinds;
	const vector<Term::Iter>& iters;

	UnifTermsStepData(const vector<Term::Iter>& is) : iters(is) {
		least_type = nullptr;
		for (const auto& i : iters) {
			if (!track_iter(i)) {
				return;
			}
		}
		consistent = true;
	}

	vector<Term::Iter> subGoals() const {
		vector<Term::Iter> termIters;
		for (uint i = 0; i < kinds.size(); ++ i) {
			if (kinds[i] == Kind::RULE) {
				termIters.push_back(iters.termIters[i]);
			}
		}
		return termIters;
	}

	vector<Term::Iter> shiftGoals(const vector<Term::Iter>& ends) const {
		vector<Term::Iter> termIters;
		for (uint i = 0, j = 0; i < kinds.size(); ++ i) {
			if (kinds[i] == Kind::RULE) {
				termIters.push_back(ends.termIters[j++]);
			} else {
				termIters.push_back(iters.termIters[i]);
			}
		}
		return termIters;
	}

	bool track_iter(Term::Iter it) {
		RuleVar rv = it.ruleVar();
		if (!least_type) {
			least_type = rv.type();
		} else {
			if (*least_type <= *rv.type()) {
				// ok
			} else if (*rv.type() <= *least_type) {
				least_type = rv.type();
			} else {
				// There's no unification because of type constraints
				return false;
			}
		}
		if (rv.isVar()) {
			if (!track_var(rv.var)) {
				return false;
			}
		} else {
			if (!track_rule(rv.rule)) {
				return false;
			}
		}
		return true;
	}

	bool track_var(LightSymbol v) {
		if (v.rep) {
			if (var.is_undef()) {
				var = v;
				kinds.push_back(Kind::VAR);
			} else {
				kinds.push_back(Kind::CONST_VAR);
			}
			// Collect replaceable variables
			vars.push_back(v.lit);
		} else {
			kinds.push_back(Kind::CONST_VAR);
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
	bool track_rule(const Rule* r) {
		if (const_.is_def()) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		if (!rule) {
			rule = r;
		} else if (rule != r) {
			// In case we have a non-leaf with some rule,
			// all other leafs must be with the same rule.
			return false;
		}
		kinds.push_back(Kind::RULE);
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

static bool equal_term_iters(const vector<Term::Iter>& iters) const {
	RuleVar rv = iters.at(0).ruleVar();
	for (uint i = 1; i < iters.size(); ++ i) {
		if (rv != iter.at(i).ruleVar()) {
			return false;
		}
	}
	return true;
}

static vector<UnifyIters> unify_term_iters(const UnifyIters& i) {
	vector<UnifyIters> ret;
	if (i.equals()) {
		ret.emplace_back(i);
	} else {
		UnifStepData data(i);
		if (data.consistent) {
			if (data.rule) {
				UnifyIters subBegins(data.subGoals(), i.parentSub, i.sub);
				for (auto& pair : do_unify_general(subBegins)) {
					try {
						Subst s = unify_step(i.sub, data.vars, pair.end.sub.apply(pair.subTerm()));
						s.compose(pair.end.sub.complement(s.dom()));
						if (s.ok()) {
							ret.emplace_back(data.shiftGoals(pair.end), i.parentSub, std::move(s));
						}
					} catch (Error& err) {
						err.msg += pair.show() + "\n";
						throw err;
					}
				}
			} else {
				Subst s = unify_step(i.sub, data.vars, Term(data.const_.is_def() ? data.const_ : data.var));
				if (s.ok()) {
					ret.emplace_back(i, i.parentSub, std::move(s));
				}
			}
		}
	}
	return ret;
}


TermSubst unify_terms(const vector<const Term*>& terms) {

	if (terms.size() == 0) {
		return TermSubst(Term(), Subst(false));
	} else if (terms.size() == 1) {
		return TermSubst(*terms.at(0), Subst());
	} else {
		Timer timer;
		vector<Term::Iter> termIters;
		for (auto t : terms) {
			termIters.emplace_back(*t);
		}
		add_timer_stats("unify_terms_create_iters", timer);

		UnifyIters iters(termIters);
		UnifyIters begin(iters);
		Subst sub;
		while (true) {
			if (!equal_term_iters(iters)) {
				UnifTermsStepData data(iters);
				if (!data.consistent) {
					return TermSubst(Term(), Subst(false));
				} else {
					if (data.rule) {
						vector<Term::Iter> subIters = data.subGoals();
						UnifyIters subBegins(data.subGoals(), i.parentSub, i.sub);
						TermSubst sub =
						for (auto& pair : do_unify_general(subBegins)) {
							try {
								Subst s = unify_step(i.sub, data.vars, pair.end.sub.apply(pair.subTerm()));
								s.compose(pair.end.sub.complement(s.dom()));
								if (s.ok()) {
									ret.emplace_back(data.shiftGoals(pair.end), i.parentSub, std::move(s));
								}
							} catch (Error& err) {
								err.msg += pair.show() + "\n";
								throw err;
							}
						}
					} else {
						Subst s = unify_step(i.sub, data.vars, Term(data.const_.is_def() ? data.const_ : data.var));
						if (s.ok()) {
							ret.emplace_back(i, i.parentSub, std::move(s));
						}
					}
				}
			}

			for (auto& i : unify_term_iters(iters)) {
				if (i.isTermEnd(p.beg) && i.sub.ok()) {
					return TermSubst(term, std::move(sub));
				}
				if (!i.isNextEnd(p.beg)) {
					st.emplace(p.beg, i.next());
				}
			}
			if (i.isTermEnd(begin) && i.sub.ok()) {
				return TermSubst(term, std::move(sub));
			}
			if (i.isNextEnd(begin)) {
				return TermSubst(Term(), Subst(false));
			}

		}


		map<vector<uint>, TermSubst> ret;

		auto unified = do_unify_terms(iters);
		add_timer_stats("do_unify_general", timer);

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

		//check_unification(inds, terms, ret);
		return ret;
	}
}
*/

string show_unification_args(const vector<const Index*>& inds, const vector<const Term*>& terms) {
	ostringstream oss;
	oss << "indexes:" << endl;
	oss << "---------" << endl;
	for (uint i = 0; i < inds.size(); ++i) {
		oss << "ind " << i << ":" << endl;
		oss << Indent::paragraph(inds[i]->show()) << endl;
	}
	oss << "terms:" << endl;
	oss << "---------" << endl;
	for (uint i = 0; i < terms.size(); ++i) {
		oss << "term " << i << ": " << terms[i]->show() << endl;
	}
	return oss.str();
}

string show_unification_result(const map<vector<uint>, TermSubst>& result) {
	ostringstream oss;
	oss << "result:" << endl;
	oss << "---------" << endl;
	for (const auto& p : result) {
		oss << prover::show(p.first) << " --> " << p.second.show() << endl;
	}
	return oss.str();
}

void check_unification(const vector<const Index*>& inds, const vector<const Term*>& terms, const map<vector<uint>, TermSubst>& result) {
	vector<Index::Unpacked> unpackedInds;
	for (auto ind : inds) {
		unpackedInds.emplace_back(std::move(ind->unpack()));
	}
	for (const auto& p : result) {
		const vector<uint>& key = p.first;
		const TermSubst& ts = p.second;
		for (uint i = 0; i < unpackedInds.size(); ++i) {
			Term t;
			for (const auto& p : unpackedInds[i]) {
				for (uint k : p.second) {
					if (k == key[i]) {
						t = p.first;
						break;
					}
				}
			}
			if (t.empty()) {
				string msg;
				msg += "no key " + prover::show(key) + " in unpacked inds\n";
				msg += "unif. term:   " + ts.term.show() + "\n";
				msg += "unif. subst:\n";
				msg += Indent::paragraph(ts.sub.show()) + "\n";
				msg += "unpacked index:\n";
				for (const auto& p : unpackedInds[i]) {
					msg += "\t" + p.first.show() + " --> " + prover::show(p.second) + "\n";
				}
				msg += show_unification_args(inds, terms);
				msg += show_unification_result(result);
				throw Error(msg);
			}
			Term applied = ts.sub.apply(t);
			if (applied != ts.term) {
				string msg;
				msg += "wrong index unification: " + applied.show() + " != " + ts.term.show() + "\n";
				msg += "orig. term:   " + t.show() + "\n";
				msg += "applied term: " + applied.show() + "\n";
				msg += "unif. term:   " + ts.term.show() + "\n";
				msg += "unif. subst:\n";
				msg += Indent::paragraph(ts.sub.show()) + "\n";
				throw Error(msg);
			}
		}
		for (auto t : terms) {
			Term applied = ts.sub.apply(*t);
			if (applied != ts.term) {
				string msg;
				msg += "wrong term unification: " + applied.show() + " != " + ts.term.show() + "\n";
				msg += "orig. term:   " + t->show() + "\n";
				msg += "applied term: " + applied.show() + "\n";
				msg += "unif. term:   " + ts.term.show() + "\n";
				msg += "unif. subst:\n";
				msg += Indent::paragraph(ts.sub.show()) + "\n";
				throw Error(msg);
			}
		}
	}
}

/*map<vector<uint>, TermSubst> unify_general(const UnifyIters& begin) {
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
}*/

/*static vector<UnifyPair> do_unify_general_with_hint(const UnifyIters& inits, const Term& hint) {
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
*/

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

}}}}
