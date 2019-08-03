#include "rus_prover_unify_step.hpp"
#include "rus_prover_unify_general.hpp"

#include "../rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify { namespace {

struct UnifyIters {
	explicit UnifyIters(const UnifyIters& ui, const Subst& ps, const Subst& s = Subst()) :
		iters(ui.iters), parentSub(ps), sub(s) { }

	explicit UnifyIters(const UnifyIters& ui, const Subst& ps, Subst&& s) :
		iters(ui.iters), parentSub(ps), sub(std::move(s)) { }

	explicit UnifyIters(UnifyIters&& ui, const Subst& ps, Subst&& s) :
		iters(std::move(ui.iters)), parentSub(ps), sub(std::move(s)) {	}

	explicit UnifyIters(const vector<Index::Iter>& ii, const Subst& ps = Subst(), const Subst& s = Subst()) :
		iters(ii), parentSub(ps), sub(s) { }

	explicit UnifyIters(const UnifyIters&) = default;
	explicit UnifyIters(UnifyIters&&) = default;

	UnifyIters& operator = (const UnifyIters&) = default;
	UnifyIters& operator = (UnifyIters&&) = default;

	UnifyIters side() const {
		vector<Index::Iter> side_iters;
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
		vector<Index::Iter> next_index;
		for (auto i : iters) {
			next_index.push_back(i.next());
		}
		return UnifyIters(next_index, sub, sub);
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
		cout << "Index iters:" << endl;
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
	Term subTerm(const UnifyIters& ends) const {
		if (iters.size()) {
			return iters[0].subTerm(ends.iters[0]);
		} else {
			throw Error("empty subterm - impossible");
		}
	}

	string show(bool full = false) const {
		ostringstream oss;
		uint n = 0;
		oss << "Index iters:" << endl;
		for (const auto& i : iters) {
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
		oss << "sub: " << endl;
		oss << Indent::paragraph(sub.show()) << endl;
		oss << "parentSub: " << endl;
		oss << Indent::paragraph(parentSub.show()) << endl;
		return oss.str();
	}
	string showTree() const {
		ostringstream oss;
		cout << "Index iters:" << endl;
		for (uint i = 0; i < iters.size(); ++ i) {
			oss << i << "-iter: " << endl;
			oss << Indent::paragraph(iters[i].showTree()) << endl;
		}
		return oss.str();
	}
	vector<vector<uint>> vals() const {
		CartesianProd<uint> vals_prod;
		for (const auto& i : iters) {
			vals_prod.addDim(i.iter()->second.vals);
		}
		vector<vector<uint>> ret;
		while (true) {
			ret.push_back(vals_prod.data());
			if (!vals_prod.hasNext()) {
				break;
			}
			vals_prod.makeNext();
		}
		return ret;
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

	const vector<Index::Iter> iters;
	const Subst parentSub;
	const Subst sub;
};

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
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
	const Type* least_type = nullptr;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;
	vector<Kind> indexKinds;
	const UnifyIters& iters;

	UnifyIters subGoals() const {
		vector<Index::Iter> indexIters;
		for (uint i = 0; i < indexKinds.size(); ++ i) {
			if (indexKinds[i] == Kind::RULE) {
				indexIters.push_back(iters.iters[i]);
			}
		}
		return UnifyIters(std::move(indexIters));
	}

	UnifyIters shiftGoals(const UnifyIters& ends) const {
		vector<Index::Iter> indexIters;
		for (uint i = 0, j = 0; i < indexKinds.size(); ++ i) {
			if (indexKinds[i] == Kind::RULE) {
				indexIters.push_back(ends.iters[j++]);
			} else {
				indexIters.push_back(iters.iters[i]);
			}
		}
		return UnifyIters(std::move(indexIters));
	}

	UnifStepData(const UnifyIters& is) : iters(is) {
		least_type = nullptr;
		for (const auto& ii : is.iters) {
			if (!track_iter(ii)) {
				return;
			}
		}
		consistent = true;
	}

	bool track_iter(Index::Iter it) {
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
				indexKinds.push_back(Kind::VAR);
			} else {
				indexKinds.push_back(Kind::CONST_VAR);
			}
			// Collect replaceable variables
			vars.push_back(v);
		} else {
			indexKinds.push_back(Kind::CONST_VAR);
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
		indexKinds.push_back(Kind::RULE);
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

static vector<UnifyPair> do_unify_indexes(const UnifyIters& begins);

bool debug_unify = false;

static vector<UnifyIters> unify_indexes_iters(const UnifyIters& i) {
	vector<UnifyIters> ret;
	if (i.equals()) {
		ret.emplace_back(i);
	} else {
		UnifStepData data(i);
		if (data.consistent) {
			if (data.rule) {
				UnifyIters subBegins(data.subGoals(), i.parentSub, i.sub);
				for (auto& pair : do_unify_indexes(subBegins)) {
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

static vector<UnifyPair> do_unify_indexes(const UnifyIters& inits) {
	vector<UnifyPair> ret;
	if (inits.iters.size() > 0) {
		if (inits.iters.size() == 1) {
			for (const auto& end : inits.iters[0].ends()) {
				UnifyIters ends(vector<Index::Iter>(1, end), inits.parentSub, inits.sub);
				ret.emplace_back(inits, std::move(ends));
			}
		} else {
			stack<UnifyPair> st;
			st.emplace(inits);
			while (st.size()) {
				UnifyPair p = std::move(st.top());
				st.pop();
				for (auto& i : unify_indexes_iters(p.end)) {
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

}

void check_indexes_unification(const vector<const Index*>& inds, const map<vector<uint>, TermSubst>& result);

map<vector<uint>, TermSubst> unify_indexes(const vector<const Index*>& inds) {

	Timer timer;
	vector<Index::Iter> indexIters;
	for (auto i : inds) {
		indexIters.emplace_back(std::move(i->root()));
	}
	add_timer_stats("unify_indexes_create_iters", timer);

	UnifyIters iters(indexIters);

	map<vector<uint>, TermSubst> ret;

	auto unified = do_unify_indexes(iters);
	add_timer_stats("do_unify_indexes", timer);

	timer.start();
	for (auto& pair : unified) {
		const UnifyIters& end = pair.end;
		Timer t;
		Term term = end.sub.apply(pair.subTerm());
		add_timer_stats("unify_idexes_extract_subterm", timer);

		t.start();
		for (vector<uint> vals : end.vals()) {
			ret.emplace(vals, TermSubst(std::move(term), std::move(end.sub)));
		}
		add_timer_stats("unify_indexes_emplace_term_subst", timer);
	}
	add_timer_stats("unify_indexes_arrange_ret", timer);

	//check_indexes_unification(inds, ret);
	return ret;
}

string show_indexes_unification_args(const vector<const Index*>& inds) {
	ostringstream oss;
	oss << "indexes:" << endl;
	oss << "---------" << endl;
	for (uint i = 0; i < inds.size(); ++i) {
		oss << "ind " << i << ":" << endl;
		oss << Indent::paragraph(inds[i]->show()) << endl;
	}
	return oss.str();
}

string show_indexes_unification_result(const map<vector<uint>, TermSubst>& result) {
	ostringstream oss;
	oss << "result:" << endl;
	oss << "---------" << endl;
	for (const auto& p : result) {
		oss << prover::show(p.first) << " --> " << p.second.show() << endl;
	}
	return oss.str();
}

void check_indexes_unification(const vector<const Index*>& inds, const map<vector<uint>, TermSubst>& result) {
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
				msg += show_indexes_unification_args(inds);
				msg += show_indexes_unification_result(result);
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
	}
}

}}}}
