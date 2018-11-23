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

vector<UnifyIters> unify_general_1(const UnifyIters& begins);

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
			to_unify.push_back(s.sub.at(v));
		}
	}
	vector<BothIter> iters;
	for (const auto& t : to_unify) {
		iters.emplace_back(FlatTerm::TermIter(t));
	}
	UnifyIters begin = UnifyIters(iters);
	vector<UnifyIters> ends = unify_general_1(begin);
	assert(ends.size() <= 1);
	if (ends.size() > 0) {
		UnifyIters end = ends[0];
		s.compose(end.sub);
		FlatTerm term_orig = begin.iters[0].subTerm(end.iters[0]);
		FlatTerm unified = apply(end.sub, term_orig);
		for (auto v : vars) {
			if (!s.compose(FlatSubst(v, unified))) {
				s.ok = false;
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
	return FlatTerm();
}

FlatSubst unify_step_1(const FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term) {
	FlatSubst ret(s);
	FlatTerm unified = unify_step_1(ret, vars, term);
	return unified.empty() ? FlatSubst(false) : ret;
}

vector<UnifyIters> unify_iters(const UnifyIters& i) {
	vector<UnifyIters> ret;
	if (i.equals()) {
		ret.emplace_back(i);
	} else {
		UnifStepData<BothIter> data(i.iters);
		if (data.consistent) {
			if (data.rule) {
				UnifyIters subBegins(data.subGoals(), i.parentSub, i.sub);
				vector<UnifyIters> subEnds = unify_general_1(subBegins);
				for (const auto& ends : subEnds) {
					BothIter i0 = ends.iters[0];
					FlatTerm term_orig = subBegins.iters[0].subTerm(i0);
					FlatTerm term_applied = apply(ends.sub, term_orig);
					FlatSubst s = unify_step_1(i.sub, data.vars, term_applied);
					if (s.ok) {
						ret.emplace_back(data.shiftGoals(ends.iters), i.parentSub, s);
					}
				}
			} else {
				FlatSubst s = unify_step_1(i.sub, data.vars, FlatTerm(data.const_.is_def() ? data.const_ : data.var));
				if (s.ok) {
					ret.emplace_back(i.iters, i.parentSub, s);
				}
			}
		}
	}
	return ret;
}

vector<UnifyIters> unify_general_1(const UnifyIters& begins) {
	vector<UnifyIters> ret;
	if (begins.iters.size() > 0) {
		if (begins.iters.size() == 1) {
			for (const auto& end : begins.iters[0].ends()) {
				ret.emplace_back(vector<BothIter>(1, end), begins.parentSub, begins.sub);
			}
		} else {
			vector<UnifyIters> branch;
			branch.push_back(begins);
			while (branch.size()) {
				UnifyIters n = branch.back();
				branch.pop_back();
				for (const auto& i : unify_iters(n)) {
					if (i.isTermEnd(begins)) {
						ret.push_back(i);
					}
					if (!i.isNextEnd(begins)) {
						branch.push_back(i.next());
					}
				}
				if (!n.isSideEnd()) {
					branch.push_back(n.side());
				}
			}
		}
	}
	return ret;
}

map<vector<uint>, FlatTermSubst> unify_general(const UnifyIters& begin) {
	map<vector<uint>, FlatTermSubst> ret;
	for (const auto& end : unify_general_1(begin)) {
		FlatTerm term = apply(end.sub, begin.iters[0].subTerm(end.iters[0]));
		for (auto ind :  end.inds()) {
			ret.emplace(ind, FlatTermSubst(term, end.sub));
		}
	}
	return ret;
}

}}}}
