
#include "rus_prover_product_unified.hpp"

namespace mdl { namespace rus { namespace prover {

void finalize(SubstTree& st, const vector<LightSymbol>& w, const LightTree& t, const Subst& unif = Subst());

void ProductUnified::finalize(const ProdVect& leafs_vect, const vector<LightSymbol>& w, const LightTree& t) {
	unif_.add(leafs_vect, [w,t](SubstTree& st) { prover::finalize(st, w, t); });
}

void ProductUnified::add_intersection(const vector<ProductUnified>& v, const Rule* r, const vector<LightSymbol>& w) {
	UnionVect<vector<SubstTree>> common(true);
	for (const auto& m : v) {
		common = std::move(intersect(common, m.unif_));
	}
	common.check_uniqueness();
	for (const auto& p : common.un()) {
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
			LightTree term = apply(unif, LightTree(r, children));
			unif_.add(p.key, [w, term](SubstTree& st) { prover::finalize(st, w, term); });
		}
	}
}

 MultyUnifiedSubs intersect(const map<LightSymbol, ProductUnified>& terms, MultyUnifiedSubs& unif) {
	UnionVect<vector<SubstTree>> common(true);
	vector<LightSymbol> vars;
	for (const auto& p : terms) {
		common = std::move(intersect(common, p.second.unif_));
		vars.push_back(p.first);
	}
	MultyUnifiedSubs s;
	for (const auto& q : common.un()) {
		const ProdVect& key = q.key;
		for (uint i = 0; i < q.value.size(); ++ i) {
			const LightTree& term = q.value[i].tree;
			const Subst& sub = q.value[i].sub;
			if (!term.empty()) {
				for (auto c : key.unfold()) {
					Subst unified = unify_subs(MultySubst({&unif[c], &sub}));
					unif[c] = unified;
					s[c].sub[vars[i]] = apply(unif[c], term);
				}
			} else {
				for (auto c : key.unfold()) {
					s[c];
					unif[c];
				}
			}
		}
	}
	return s;
}

 std::map<vector<uint>, SubstTree> ProductUnified::map() const {
	 std::map<vector<uint>, SubstTree> ret;
	 for (const auto& q : unif_.un()) {
		for (auto c : q.key.unfold()) {
			ret[c] = q.value;
		}
	 }
	 return ret;
 }

}}}
