
#include "rus_prover_product_unified.hpp"

namespace mdl { namespace rus { namespace prover {

void finalize(SubstTree& st, const vector<LightSymbol>& w, const LightTree& t);

void ProductUnified::finalize(const ProdVect& leafs_vect, const vector<LightSymbol>& w, const LightTree& t) {
	unite(unif_, leafs_vect, [w,t](SubstTree& st) { prover::finalize(st, w, t); });
}

void ProductUnified::add_intersection(const vector<ProductUnified>& v, const Rule* r, const vector<LightSymbol>& w) {
	UnionVect<vector<SubstTree>> common(true);
	for (const auto& m : v) {
		common = std::move(intersect(common, m.unif_));
	}
	for (const auto& p : common.un) {
		LightTree::Children children;
		Subst unif;
		for (const auto& st : p.value) {
			if (st.tree.empty()) {
				break;
			}
			unif = unify_subs(MultySubst({&unif, &st.sub}));
			if (!unif.ok) {
				break;
			}
			children.push_back(make_unique<LightTree>(st.tree));
		}
		if (children.size() == r->arity()) {
			/*if (unif_.map_[p.first].sub.compose(unif)) {
				LightTree term = apply(unif, LightTree(r, children));
				finalize(p.first, w, term);
			}*/
		}
	}
}

std::map<vector<uint>, SubstTree> ProductUnified::map() const {
	std::map<vector<uint>, SubstTree> ret;
	return ret;
}

 MultyUnifiedSubs intersect(const map<LightSymbol, ProductUnified>& terms, MultyUnifiedSubs& unif) {
	UnionVect<vector<SubstTree>> common(true);
	vector<LightSymbol> vars;
	for (const auto& p : terms) {
		common = std::move(intersect(common, p.second.unif_));
		vars.push_back(p.first);
	}
	MultyUnifiedSubs s;
	/*for (const auto& q : common.map_) {
		vector<uint> c = q.first;
		for (uint i = 0; i < q.second.size(); ++ i) {
			const LightTree& term = q.second[i].tree;
			const Subst& sub = q.second[i].sub;
			if (!term.empty()) {
				Subst unified = unify_subs(MultySubst({&unif[c], &sub}));
				unif[c] = unified;
				s[c].sub[vars[i]] = apply(unif[c], term);
			} else {
				s[c];
				unif[c];
			}
		}
	}*/
	return s;
}

}}}
