#pragma once

#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

extern bool debug_multy_index;
extern uint matrix_vector_counter;

struct ProductUnified {
	ProductUnified() : may_add(true) { }
	ProductUnified(const ProductUnified& pu) : may_add(pu.may_add) {
		for (auto& p : pu.unif_.un()) {
			if (!p.erased) {
				unif_.add(p.key, p.value.top());
			}
		}
	}
	ProductUnified(const ProductUnified* pu) : may_add(!pu) {
		if (pu) {
			for (auto& p : pu->unif_.un()) {
				if (!p.erased) {
					/*if (debug_multy_index && matrix_vector_counter) {
						cout << "INIT_ADDING: " << p.key.show() << endl;
						cout << "p.value.inc(): " << p.value.inc().show(true) << endl;
					}*/
					unif_.add(p.key, p.value.top().inc(), true);
				}
			}
		}
	}
	string show() const { return unif_.show(); }
	void finalize(const ProdVect& leafs_vect, const vector<LightSymbol>& w, const LightTree& t);
	void add_intersection(const vector<ProductUnified>& v, const Rule* r, const vector<LightSymbol>& w);
	void add_intersection_1(const ProductUnified& v, const Rule* r, const vector<LightSymbol>& w);
	std::map<vector<uint>, SubstTree> map() const;
	const UnionVect& unif() const { return unif_; }

private:
	friend MultyUnifiedSubs intersect(const std::map<LightSymbol, ProductUnified>& terms, MultyUnifiedSubs& unif);

	bool may_add;
	UnionVect unif_;
};

 MultyUnifiedSubs intersect(const map<LightSymbol, ProductUnified>& terms, MultyUnifiedSubs& unif);

}}}

