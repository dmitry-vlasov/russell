#include "../rus_prover_cartesian.hpp"
#include "rus_prover_trie_index_vector.hpp"

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
					FlatSubst s = unify_step(i.sub, data.vars, term_applied);
					if (s.ok) {
						ret.emplace_back(data.shiftGoals(ends.iters), i.parentSub, s);
					}
				}
			} else {
				FlatSubst s = unify_step(i.sub, data.vars, FlatTerm(data.const_.is_def() ? data.const_ : data.var));
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
						ret.push_back(std::move(i));
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

GeneralUnified unify_general(const UnifyIters& i) {
	GeneralUnified ret;
	for (const auto& i : unify_general_1(i)) {
		for (auto ind :  i.inds()) {
			ret.emplace(ind, std::move(i.sub));
		}
	}
	return ret;
}

}}}}
