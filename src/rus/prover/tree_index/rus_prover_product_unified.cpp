#include "rus_prover_product_unified.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_union_vect = false;

void finalize(SubstTree& st, const vector<LightSymbol>& w, const LightTree& t);
void finalize(SubstTree& st, const vector<LightSymbol>& w, const LightTree& t, Subst&);

void ProductUnified::finalize(const ProdVect& leafs_vect, const vector<LightSymbol>& w, const LightTree& t) {
	unif_.intersect(leafs_vect, [w, t](SubstTree& st) { prover::finalize(st, w, t); }, may_add);
}

void ProductUnified::add_intersection(const vector<ProductUnified>& v, const Rule* r, const vector<LightSymbol>& w) {
	UnionVect common(true);
	for (const auto& m : v) {
		common = std::move(intersect(common, m.unif_));
	}
	common.check_uniqueness();
	for (const auto& p : common.un()) {
		if (p->value.active()) {
			LightTree::Children children;
			Subst unif;
			const SubstTree& st = *p->value.stack.back();
			for (uint i = 0; i < st.size(); ++i) {
				if (st.tree(i).empty()) {
					break;
				}
				unif = unify_subs(MultySubst({&unif, &st.sub(i)}));
				if (!unif.ok) {
					break;
				}
				children.push_back(make_unique<LightTree>(st.tree(i)));
			}
			if (children.size() == r->arity()) {
				LightTree term = apply(unif, LightTree(r, children));
				unif_.intersect(p->key, [w, term, &unif](SubstTree& st) { prover::finalize(st, w, term, unif); }, true);
			}
		}
	}
}

void ProductUnified::add_intersection_1(const ProductUnified& v, const Rule* r, const vector<LightSymbol>& w) {
	for (const auto& p : v.unif().un()) {
		if (p->value.active()) {
			LightTree::Children children;
			Subst unif;
			const SubstTree& st = *p->value.stack.back();
			for (uint i = 0; i < st.size(); ++i) {
				if (st.tree(i).empty()) {
					break;
				}
				unif = unify_subs(MultySubst({&unif, &st.sub(i)}));
				if (!unif.ok) {
					break;
				}
				children.push_back(make_unique<LightTree>(st.tree(i)));
			}
			if (children.size() == r->arity()) {
				LightTree term = apply(unif, LightTree(r, children));
				unif_.intersect(p->key, [w, term, &unif](SubstTree& st) { prover::finalize(st, w, term, unif); }, true);
			}
		}
	}
}

 MultyUnifiedSubs intersect(const map<LightSymbol, ProductUnified>& terms, MultyUnifiedSubs& unif) {
	UnionVect common(true);
	vector<LightSymbol> vars;
	for (const auto& p : terms) {
		common = std::move(intersect(common, p.second.unif_));
		vars.push_back(p.first);
	}
	MultyUnifiedSubs s;
	for (const auto& q : common.un()) {
		if (q->value.active()) {
			const ProdVect& key = q->key;
			const SubstTree& st = *q->value.stack.back();
			for (uint i = 0; i < st.size(); ++ i) {
				const LightTree& term =st.tree(i);
				const Subst& sub = st.sub(i);
				if (!term.empty()) {
					for (auto c : key.unfold()) {
						if (unif[c].ok) {
							Subst unified = unify_subs(MultySubst({&unif[c], &sub}));
							unif[c] = unified;
							s[c].sub[vars[i]] = apply(unif[c], term);
						}
					}
				} else {
					for (auto c : key.unfold()) {
						s[c];
						unif[c];
						if (!sub.ok) {
							unif[c].ok = false;
						}
					}
				}
			}
		}
	}
	return s;
}

 std::map<vector<uint>, SubstTree> ProductUnified::map() const {
	 std::map<vector<uint>, SubstTree> ret;
	 for (const auto& q : unif_.un()) {
		if (q->value.active()) {
			for (auto c : q->key.unfold()) {
				ret[c] = *q->value.stack.back();
			}
		}
	 }
	 return ret;
 }

}}}