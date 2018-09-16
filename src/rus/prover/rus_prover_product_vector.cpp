#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

UnionVect<vector<SubstTree>> intersect(const UnionVect<vector<SubstTree>>& v, const UnionVect<SubstTree>& uv) {
	UnionVect<vector<SubstTree>> ret;
	if (v.full) {
		for (const auto& p : uv.un()) {
			ret.un_.emplace_back(p.key, vector<SubstTree>(1, p.value));
		}
	} else {
		uint c0 = 0;
		for (const auto& p : v.un()) {
			if (!p.erased) {
				for (uint i : uv.neighbourhood(p.key)) {
					const auto& q = uv.un()[i];
					if (!q.erased) {
						if (p.key.intersects_with(q.key) && q.value.sub.ok) {
							ProdVect r = intersect(p.key, q.key);
							vector<SubstTree> data = p.value;
							data.push_back(q.value);
							ret.un_.emplace_back(r, data);
							++c0;
						}
					}
				}
			}
		}
		uint c1 = v.un().size() * uv.un().size();
		if (c1 > 1024 * 16 && c0 > 128) {
			cout << "INTERSECT SIZE: " << c1  << " REAL COUNT: " << c0 << endl;
		}
	}
	return ret;
}

}}}
