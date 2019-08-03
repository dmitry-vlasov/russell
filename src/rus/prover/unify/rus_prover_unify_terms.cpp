#include "rus_prover_unify_step.hpp"
#include "rus_prover_unify_terms.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify { namespace {

struct UnifyIters {
	explicit UnifyIters(const UnifyIters& ui, const Subst& s) :
		iters(ui.iters), sub(s) { }
	explicit UnifyIters(const UnifyIters& ui, Subst&& s) :
		iters(ui.iters), sub(std::move(s)) { }
	explicit UnifyIters(UnifyIters&& ui, Subst&& s) :
		iters(std::move(ui.iters)), sub(std::move(s)) { }
	explicit UnifyIters(const vector<Term::Iter>& ti, const Subst& s = Subst()) :
		iters(ti), sub(s) { }
	explicit UnifyIters(const UnifyIters&) = default;
	explicit UnifyIters(UnifyIters&&) = default;
	explicit UnifyIters() { sub.spoil(); }

	UnifyIters& operator = (const UnifyIters&) = default;
	UnifyIters& operator = (UnifyIters&&) = default;

	UnifyIters next() const {
		vector<Term::Iter> next_term;
		for (auto i : iters) {
			next_term.push_back(i.next());
		}
		return UnifyIters(next_term, sub);
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
		cout << "Term iters:" << endl;
		for (uint i = 0; i < iters.size(); ++i) {
			cout << "\t" << i << ": " << (ends.iters[i].isEnd(iters[i]) ? "END" : "X" ) << endl;
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
	bool equals() const {
		if (!size()) {
			return true;
		}
		RuleVar rv = iters.at(0).ruleVar();
		for (uint i = 1; i < iters.size(); ++ i) {
			if (rv != iters.at(i).ruleVar()) {
				return false;
			}
		}
		return true;
	}
	bool isValid() const {
		if (!sub.ok()) {
			return false;
		}
		for (uint i = 0; i < iters.size(); ++i) {
			if (!iters[i].isValid()) {
				return false;
			}
		}
		return true;
	}
	Term subTerm() const {
		if (iters.size()) {
			return iters.at(0).subTerm();
		} else {
			throw Error("empty subterm - impossible");
		}
	}

	string show(bool full = false) const {
		ostringstream oss;
		uint n = 0;
		oss << "Term iters:" << endl;
		for (const auto& i : iters) {
			if (isValid()) {
				oss << "\t" << n << "-iter: " << i.show() << endl;
			} else {
				oss << "\t" << n << "-iter: NOT VALID " << i.show() << endl;
			}
			++n;
		}
		oss << "sub: " << endl;
		oss << Indent::paragraph(sub.show()) << endl;
		return oss.str();
	}

	uint size() const {
		return iters.size();
	}
	bool operator == (const UnifyIters& ui) const {
		if (iters.size() != ui.iters.size()) {
			return false;
		}
		for (uint i = 0; i < iters.size(); ++i) {
			if (iters[i] != ui.iters[i]) {
				return false;
			}
		}
		return true;
	}
	bool operator != (const UnifyIters& ui) const {
		return !operator == (ui);
	}

	vector<Term::Iter> iters;
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
	UnifyPair() : ok_(false) { }
	UnifyPair(const UnifyIters& b) : beg(b), end(b) { }
	UnifyPair(const UnifyIters& b, const UnifyIters& e) : beg(b), end(e) { }
	UnifyPair(const UnifyIters& b, UnifyIters&& e) : beg(b), end(std::move(e)) { }

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

	bool ok_ = true;
	UnifyIters beg;
	UnifyIters end;
};

struct UnifStepData {
	enum class Kind { VAR, RULE, CONST_VAR };
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
	const Type* least_type = nullptr;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;
	vector<Kind> kinds;
	const vector<Term::Iter>& iters;

	UnifStepData(const vector<Term::Iter>& is) : iters(is) {
		least_type = nullptr;
		for (const auto& i : iters) {
			if (!track_iter(i)) {
				return;
			}
		}
		consistent = true;
	}

	vector<Term::Iter> subGoals() const {
		vector<Term::Iter> ret;
		for (uint i = 0; i < kinds.size(); ++ i) {
			if (kinds[i] == Kind::RULE) {
				ret.push_back(iters[i]);
			}
		}
		return ret;
	}

	vector<Term::Iter> shiftGoals(const UnifyIters& ends) const {
		vector<Term::Iter> ret;
		for (uint i = 0, j = 0; i < kinds.size(); ++ i) {
			if (kinds[i] == Kind::RULE) {
				ret.push_back(ends.iters[j++]);
			} else {
				ret.push_back(iters[i]);
			}
		}
		return ret;
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
			vars.push_back(v);
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
		string ret;
		ret += "rule: " + (rule ? Lex::toStr(rule->id()) : "NULL") + "\n";
		ret += "vars: ";
		for (const auto& v : vars) {
			ret += v.show() + " ";
		}
		ret += "\n";
		ret += string("consistent: ") + (consistent ? "TRUE" : "FALSE") + "\n";
		ret += string("var: ") + var.show() + "\n";
		ret += "\n";
		return ret;
	}
};

static UnifyPair do_unify_terms(const UnifyIters& inits);

static UnifyIters unify_term_iters(const UnifyIters& i) {
	if (i.equals()) {
		return UnifyIters(i);
	} else {
		UnifyIters ret;
		UnifStepData data(i.iters);
		if (data.consistent) {
			if (data.rule) {
				UnifyIters subBegins(data.subGoals(), i.sub);
				UnifyPair pair = do_unify_terms(subBegins);
				if (!pair.end.sub.ok()) {
					return UnifyIters(pair.end);
				}
				try {
					Subst s = unify_step(i.sub, data.vars, pair.end.sub.apply(pair.subTerm()));
					s.compose(pair.end.sub.complement(s.dom()));
					if (s.ok()) {
						return UnifyIters(data.shiftGoals(pair.end), std::move(s));
					}
				} catch (Error& err) {
					err.msg += pair.show() + "\n";
					throw err;
				}
			} else {
				Subst s = unify_step(i.sub, data.vars, Term(data.const_.is_def() ? data.const_ : data.var));
				if (s.ok()) {
					return UnifyIters(i, std::move(s));
				}
			}
		}
		return UnifyIters();
	}
}

static UnifyPair do_unify_terms(const UnifyIters& inits) {
	if (inits.size() > 0) {
		if (inits.size() == 1) {
			UnifyIters ends(vector<Term::Iter>(1, inits.iters[0].end()), inits.sub);
			return UnifyPair(inits, std::move(ends));
		} else {
			UnifyIters begin(inits);
			UnifyIters iters(inits);
			while (true) {
				iters = unify_term_iters(iters);
				if (!iters.sub.ok()) {
					return UnifyPair();
				}
				if (iters.isTermEnd(begin)) {
					return UnifyPair(std::move(begin), std::move(iters));
				}
				if (iters.isNextEnd(begin)) {
					return UnifyPair();
				}
				iters = iters.next();
			}
		}
	} else {
		return UnifyPair();
	}
}

}

void check_term_unification(const vector<const Term*>& terms, const TermSubst& result);

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

		UnifyPair pair = do_unify_terms(iters);
		const UnifyIters& end = pair.end;
		if (end.sub.ok()) {
			Term term = end.sub.apply(pair.subTerm());
			add_timer_stats("do_unify_terms", timer);

			TermSubst ret(std::move(term), std::move(end.sub));

			check_term_unification(terms, ret);
			return ret;
		} else {
			return TermSubst(Term(), Subst(false));
		}
	}
}

string show_term_unification_args(const vector<const Term*>& terms) {
	ostringstream oss;
	oss << "terms:" << endl;
	oss << "---------" << endl;
	for (uint i = 0; i < terms.size(); ++i) {
		oss << "term " << i << ": " << terms[i]->show() << endl;
	}
	return oss.str();
}

string show_term_unification_result(const TermSubst& result) {
	ostringstream oss;
	oss << "result:" << endl;
	oss << "---------" << endl;
	oss << result.show() << endl;
	return oss.str();
}

void check_term_unification(const vector<const Term*>& terms, const TermSubst& result) {
	for (auto t : terms) {
		Term applied = result.sub.apply(*t);
		if (applied != result.term) {
			string msg;
			msg += "wrong term unification: " + applied.show() + " != " + result.term.show() + "\n";
			msg += "orig. term:   " + t->show() + "\n";
			msg += "applied term: " + applied.show() + "\n";
			msg += "unif. term:   " + result.term.show() + "\n";
			msg += "unif. subst:\n";
			msg += Indent::paragraph(result.sub.show()) + "\n";
			throw Error(msg);
		}
	}
}

}}}}
