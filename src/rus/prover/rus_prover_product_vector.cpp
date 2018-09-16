#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

UnionVect<vector<SubstTree>> intersect(const UnionVect<vector<SubstTree>>& v, const UnionVect<SubstTree>& uv) {
	UnionVect<vector<SubstTree>> ret;
	if (v.full) {
		for (const auto& p : uv.un()) {
			ret.un_.emplace_back(p.key, vector<SubstTree>(1, p.value));
		}
	} else {
		for (const auto& p : v.un()) {
			for (const auto& q : uv.un()) {
				if (p.key.intersects_with(q.key) && q.value.sub.ok) {
					ProdVect r = intersect(p.key, q.key);
					vector<SubstTree> data = p.value;
					data.push_back(q.value);
					ret.un_.emplace_back(r, data);
				}
			}
		}
		uint c = v.un().size() * uv.un().size();
		if (c > 1024 * 16) {
			cout << "INTERSECT COUNT: " << c << endl;
		}
	}
	return ret;
}

}}}
