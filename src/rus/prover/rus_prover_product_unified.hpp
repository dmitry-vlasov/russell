#pragma once

#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

struct ProductUnified {
	ProductUnified() : may_add(true) { }
	ProductUnified(const ProductUnified& pu) : may_add(false) {
		for (auto& p : pu.unif_.un()) {
			unif_.add(p.key);
		}
	}
	string show() const { return unif_.show(); }
	void finalize(const ProdVect& leafs_vect, const vector<LightSymbol>& w, const LightTree& t);
	void add_intersection(const vector<ProductUnified>& v, const Rule* r, const vector<LightSymbol>& w);
	std::map<vector<uint>, SubstTree> map() const;

private:
	friend MultyUnifiedSubs intersect(const std::map<LightSymbol, ProductUnified>& terms, MultyUnifiedSubs& unif);

	bool may_add;
	UnionVect<SubstTree> unif_;
};

 MultyUnifiedSubs intersect(const map<LightSymbol, ProductUnified>& terms, MultyUnifiedSubs& unif);

}}}

