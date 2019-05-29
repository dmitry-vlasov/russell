#include "../rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify { namespace {

struct VarifyIters {
	explicit VarifyIters(const VarifyIters& ui, const VarRepl& ps, const VarRepl& s = VarRepl()) :
		indexIter(ui.indexIter), termIter(ui.termIter), parentRepl(ps), repl(s) { }

	explicit VarifyIters(const VarifyIters& ui, const VarRepl& ps, VarRepl&& s) :
		indexIter(ui.indexIter), termIter(ui.termIter), parentRepl(ps), repl(std::move(s)) { }

	explicit VarifyIters(VarifyIters&& ui, const VarRepl& ps, VarRepl&& s) :
		indexIter(std::move(ui.indexIter)), termIter(std::move(ui.termIter)), parentRepl(ps), repl(std::move(s)) {	}

	explicit VarifyIters(const Index::Iter& ii, const Term::Iter& ti, const VarRepl& ps = VarRepl(), const VarRepl& s = VarRepl()) :
		indexIter(ii), termIter(ti), parentRepl(ps), repl(s) { }

	explicit VarifyIters(const VarifyIters&) = default;
	explicit VarifyIters(VarifyIters&&) = default;

	VarifyIters& operator = (const VarifyIters&) = default;
	VarifyIters& operator = (VarifyIters&&) = default;

	VarifyIters side() const {
		return VarifyIters(indexIter.side(), termIter, parentRepl, parentRepl);
	}
	VarifyIters next() const {
		return VarifyIters(indexIter.next(), termIter.next(), repl, repl);
	}
	bool isNextEnd() const {
		return indexIter.isNextEnd() || termIter.isNextEnd();
	}
	bool isTermEnd(const VarifyIters& ends) const {
		return ends.indexIter.isEnd(indexIter) && ends.termIter.isEnd(termIter);
	}
	void showTermEnd(const VarifyIters& ends) const {
		cout << "Index iter:" << endl;
		cout << "\t" << (ends.indexIter.isEnd(indexIter) ? "END" : "X" ) << endl;
		cout << "Term iter:" << endl;
		cout << "\t" << (ends.termIter.isEnd(termIter) ? "END" : "X" ) << endl;
	}
	bool isNextEnd(const VarifyIters& ends) const {
		return isNextEnd() || ends.indexIter.isEnd(indexIter) || ends.termIter.isEnd(termIter);
	}
	bool isSideEnd() const {
		return indexIter.isSideEnd();
	}
	bool isValid() const {
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
		oss << Indent::paragraph(repl.show()) << endl;
		oss << "parentSub: " << endl;
		oss << Indent::paragraph(parentRepl.show()) << endl;
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
	const vector<uint>& vals() const {
		return indexIter.iter()->second.vals;
	}

	bool operator == (const VarifyIters& ui) const {
		return indexIter == ui.indexIter && termIter == ui.termIter;
	}
	bool operator != (const VarifyIters& ui) const {
		return !operator == (ui);
	}

	bool equals() const {
		return indexIter.ruleVar() == termIter.ruleVar();
	}
	bool bothVars() const {
		return
			indexIter.ruleVar().isVar() &&
			indexIter.ruleVar().var.rep &&
			termIter.ruleVar().isVar() &&
			termIter.ruleVar().var.rep;
	}
	bool indexSubtype() const {
		return *indexIter.ruleVar().type() <= *termIter.ruleVar().type();
	}
	bool termSubtype() const {
		return *termIter.ruleVar().type() <= *indexIter.ruleVar().type();
	}
	VarPair replPair() const {
		if (bothVars()) {
			if (indexSubtype()) {
				return VarPair(termIter.ruleVar().var, indexIter.ruleVar().var);
			} else if (termSubtype()) {
				return VarPair(indexIter.ruleVar().var, termIter.ruleVar().var);
			} else {
				return VarPair();
			}
		} else {
			return VarPair();
		}
	}

	vector<VarifyIters> prepareIndexIters() const {
		vector<VarifyIters> ret;
		if (termIter.ruleVar().isRule() || (termIter.ruleVar().isVar() && !termIter.ruleVar().var.rep)) {
			/*for (Index::Iter i : indexIter.vars()) {
				ret.emplace_back(i, termIter, parentRepl, repl);
			}*/
			auto i = indexIter.node()->map.find(termIter.ruleVar());
			if (i != indexIter.node()->map.end()) {
				ret.emplace_back(Index::Iter(indexIter.node(), i), termIter, parentRepl, repl);
			}
		} else {
			/*for (auto i = indexIter.node()->map.begin(); i != indexIter.node()->map.end(); ++ i) {
				ret.emplace_back(Index::Iter(indexIter.node(), i), termIter, parentRepl, repl);
			}*/
			for (Index::Iter i : indexIter.vars()) {
				ret.emplace_back(i, termIter, parentRepl, repl);
			}
		}
		return ret;
	}

	Index::Iter indexIter;
	Term::Iter  termIter;
	VarRepl parentRepl;
	VarRepl repl;
};

string show(const vector<VarifyIters>& vi) {
	string ret;
	for (const auto& ui : vi) {
		ret += ui.show(true) + "\n";
	}
	return ret;
}

inline void dump(const vector<VarifyIters>& vi, const char* msg = "") {
	cout << msg << endl;
	cout << show(vi) << endl;
}

inline void dump(const VarifyIters& ui, const char* msg = "") {
	cout << msg << endl;
	cout << ui.show(true) << endl;
}

struct UnifyPair {
	UnifyPair(const VarifyIters& b) : is_root(true), beg(b), end(b) { }
	UnifyPair(const VarifyIters& b, const VarifyIters& e) : is_root(false), beg(b), end(e) { }
	UnifyPair(const VarifyIters& b, VarifyIters&& e) : is_root(false), beg(b), end(std::move(e)) { }

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
	VarifyIters beg;
	VarifyIters end;
};

static vector<UnifyPair> do_varify_index_term(const VarifyIters& begins);

bool debug_unify = false;

static bool varify_iters_index_term(VarifyIters& i) {
	vector<VarifyIters> ret;
	if (i.equals()) {
		return true;
	} else {
		VarPair replPair = i.replPair();
		return replPair.from.is_def() ? i.repl.compose(replPair) : false;
	}
}

void prepareIndexIters(const VarifyIters& beg, const VarifyIters& iters, std::queue<UnifyPair>& queue) {
	if (iters.termIter.ruleVar().isRule() || (iters.termIter.ruleVar().isVar() && !iters.termIter.ruleVar().var.rep)) {
		auto i = iters.indexIter.node()->map.find(iters.termIter.ruleVar());
		if (i != iters.indexIter.node()->map.end()) {
			queue.emplace(beg, VarifyIters(Index::Iter(iters.indexIter.node(), i), iters.termIter, iters.parentRepl, iters.repl));
		}
	} else {
		for (Index::Iter i : iters.indexIter.vars()) {
			queue.emplace(beg, VarifyIters(i, iters.termIter, iters.parentRepl, iters.repl));
		}
		//for (auto i = iters.indexIter.node()->map.begin(); i != iters.indexIter.node()->map.end(); ++ i) {
		//	queue.emplace(beg, VarifyIters(Index::Iter(iters.indexIter.node(), i), iters.termIter, iters.parentRepl, iters.repl));
		//}
	}
}

static vector<UnifyPair> do_varify_index_term(const VarifyIters& inits) {
	vector<UnifyPair> ret;
	std::queue<UnifyPair> queue;
	for (const auto& i : inits.prepareIndexIters()) {
		queue.emplace(i);
	}
	while (queue.size()) {
		uint n = queue.size();
		while (n--) {
			UnifyPair p = std::move(queue.front());
			queue.pop();
			if (varify_iters_index_term(p.end)) {
				if (p.end.isTermEnd(p.beg)) {
					ret.emplace_back(p);
				}
				if (!p.end.isNextEnd(p.beg)) {
					prepareIndexIters(p.beg, p.end.next(), queue);
					/*for (const auto& j : i.next().prepareIndexIters()) {
						queue.emplace(p.beg, std::move(j));
					}*/
				}
			}
		}
	}
	return ret;
}

}

void check_index_term_varification(const Index& ind, const Term& term, const map<uint, TermVarRepl>& result);

map<uint, TermVarRepl> varify_index_term(const Index& ind, const Term& term) {
	VarifyIters iters(ind.root(), term);
	map<uint, TermVarRepl> ret;

	Timer timer;
	auto unified = do_varify_index_term(iters);
	add_timer_stats("do_varify_index_term", timer);

	timer.start();
	for (auto& pair : unified) {
		const VarifyIters& end = pair.end;
		Term term = end.repl.direct().apply(pair.subTerm());
		for (uint val : end.vals()) {
			ret.emplace(val, TermVarRepl(std::move(term), std::move(end.repl)));
		}
	}
	add_timer_stats("varify_index_term: form result", timer);
	check_index_term_varification(ind, term, ret);
	return ret;
}

string show_index_term_varification_args(const Index& ind, const Term& term) {
	ostringstream oss;
	oss << "index:" << endl;
	oss << "---------" << endl;
	oss << Indent::paragraph(ind.show()) << endl;
	oss << "term: " << endl;
	oss << "---------" << endl;
	oss << term.show() << endl;
	return oss.str();
}

string show_index_term_varification_result(const map<uint, TermVarRepl>& result) {
	ostringstream oss;
	oss << "result:" << endl;
	oss << "---------" << endl;
	for (const auto& p : result) {
		oss << p.first << " --> " << p.second.show() << endl;
	}
	return oss.str();
}

void check_index_term_varification(const Index& ind, const Term& term, const map<uint, TermVarRepl>& result) {
	Index::Unpacked unpacked = ind.unpack();
	for (const auto& p : result) {
		uint key = p.first;
		const TermVarRepl& ts = p.second;
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
			msg += Indent::paragraph(ts.repl.show()) + "\n";
			msg += "unpacked index:\n";
			for (const auto& p : unpacked) {
				msg += "\t" + p.first.show() + " --> " + prover::show(p.second) + "\n";
			}
			msg += show_index_term_varification_args(ind, term);
			msg += show_index_term_varification_result(result);
			throw Error(msg);
		}
		Term applied_ind(t);
		ts.repl.direct().apply(applied_ind);
		if (applied_ind != ts.term) {
			string msg;
			msg += "wrong index varification: " + applied_ind.show() + " != " + ts.term.show() + "\n";
			msg += "orig. term:   " + t.show() + "\n";
			msg += "applied term: " + applied_ind.show() + "\n";
			msg += "unif. term:   " + ts.term.show() + "\n";
			msg += "unif. subst:\n";
			msg += Indent::paragraph(ts.repl.show()) + "\n";
			throw Error(msg);
		}

		Term applied_term = ts.repl.direct().apply(term);
		if (applied_term != ts.term) {
			string msg;
			msg += "wrong term varification: " + applied_term.show() + " != " + ts.term.show() + "\n";
			msg += "orig. term:   " + term.show() + "\n";
			msg += "applied term: " + applied_term.show() + "\n";
			msg += "unif. term:   " + ts.term.show() + "\n";
			msg += "unif. subst:\n";
			msg += Indent::paragraph(ts.repl.show()) + "\n";
			throw Error(msg);
		}
	}
}

}}}}
