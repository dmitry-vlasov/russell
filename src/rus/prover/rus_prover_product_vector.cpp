#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

set<uint> UnionVect::neighbourhood(const ProdVect& v) const {
	set<uint> ret;
	if (!maps_.size()) {
		return ret;
	}
	vector<set<uint>> sets;
	for (uint i = 0; i < v.vect.size(); ++i) {
		set<uint> inds;
		for (uint k : v.vect[i].set()) {
			if (maps_[i].count(k)) {
				for (uint j : maps_[i].at(k)) {
					inds.insert(j);
				}
			}
		}
		if (i == 0) {
			ret = inds;
		} else {
			ret = prover::intersect(ret, inds);
		}
	}
	return ret;
}

void UnionVect::add(const ProdVect& key, const SubstTree& value, bool erased) {
	if (!maps_.size()) {
		maps_ = vector<std::map<uint, vector<uint>>>(key.vect.size());
	}

	/*if (debug_multy_index && matrix_vector_counter == 1 && key.contains({0, 1})) {
		cout << "ADDING: " << key.show() << " ERASED: " << (erased ? "yes" : "no") << endl;
		cout << "data: " << value.show(true) << endl;
	}*/

	if (debug_multy_index && matrix_vector_counter == 1) {
		if (auto p = get(key)) {
			cout << "!CHECK check_uniqueness() of key: " << key.show() << endl;
			cout << "already there: " << p->show() << endl;
			cout << "adding: " << value.show(true) << endl;
		}
	}

	uint ind = un_.size();
	un_.emplace_back(key, value, erased);
	for (uint i = 0; i < key.vect.size(); ++ i) {
		const Set& s = key.vect[i];
		for (uint k : s.set()) {
			maps_[i][k].push_back(ind);
		}
	}
}

UnionVect intersect(const UnionVect& v, const UnionVect& uv) {
	UnionVect ret;
	if (v.full()) {
		for (const auto& p : uv.un()) {
			if (!p.erased) {
				ret.add(p.key, p.value.top());
			}
		}
	} else {
		uint c0 = 0;
		for (const auto& p : v.un()) {
			if (!p.erased) {
				for (uint i : uv.neighbourhood(p.key)) {
					const auto& q = uv.un()[i];
					if (!q.erased) {
						if (p.key.intersects_with(q.key) && q.value.top().sub().ok) {
							ProdVect r = intersect(p.key, q.key);
							SubstTree data = p.value.top().inc();
							data.sub() = q.value.top().sub();
							data.tree() = q.value.top().tree();
							ret.add(r, data);
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
