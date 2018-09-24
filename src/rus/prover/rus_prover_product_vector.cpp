#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

/*
void UnionVect::intersect(const ProdVect& pv, auto finalizer, bool may_add) {

	if (debug_multy_index && matrix_vector_counter == 1 && pv.contains({0, 1})) {
		cout << "INTERSECTIONG: " << pv.show() << " MAY_ADD: " << (may_add ? "yes" : "no") << endl;
		//cout << "data: " << value.show() << endl;
	}

	stack<ProdVect> to_add;
	to_add.emplace(pv);
	uint c = 0;
	while (!to_add.empty()) {
		ProdVect q = to_add.top(); to_add.pop();
		bool intersects = false;
		for (uint i : neighbourhood(q)) {
			++c;
			Pair& p = un_[i];
			if ((!p.erased || !may_add) && p.key.intersects_with(q)) {
				ProdVect inter = prover::intersect(p.key, q);
				intersects = true;
				if (inter != p.key) {
					for (const auto& part : split(p.key, inter)) {
						add(part, p.value, p.erased);
					}
					p.erased = true;
					add(inter, p.value);
					finalizer(un_.back().value);
				} else {
					finalizer(p.value);
				}
				if (inter != q) {
					for (const auto& part : split(q, inter)) {
						to_add.emplace(part);
					}
				}
			}
		}
		if (!intersects && may_add) {
			add(q);
			finalizer(un_.back().value);
		}
	}
	if (un_.size() > 256 && c > 8) {
		cout << "UN SIZE:" << un_.size() << " REAL COUNT: " << c << endl;
	}
}*/

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

	if (debug_multy_index && matrix_vector_counter == 1 && key.contains({0, 1})) {
		cout << "ADDING: " << key.show() << " ERASED: " << (erased ? "yes" : "no") << endl;
		cout << "data: " << value.show(true) << endl;
	}

	uint ind = un_.size();
	un_.emplace_back(key, value, erased);
	for (uint i = 0; i < key.vect.size(); ++ i) {
		const Set& s = key.vect[i];
		for (uint k : s.set()) {
			maps_[i][k].push_back(ind);
		}
	}
	if (debug_multy_index && matrix_vector_counter == 1) {
		if (!check_uniqueness()) {
			cout << "!check_uniqueness()" << endl;
		}
	}
}

UnionVect intersect(const UnionVect& v, const UnionVect& uv) {
	UnionVect ret;
	if (v.full()) {
		for (const auto& p : uv.un()) {
			if (!p.erased) {
				ret.add(p.key, p.value);
			}
		}
	} else {
		uint c0 = 0;
		for (const auto& p : v.un()) {
			if (!p.erased) {
				for (uint i : uv.neighbourhood(p.key)) {
					const auto& q = uv.un()[i];
					if (!q.erased) {
						if (p.key.intersects_with(q.key) && q.value.sub().ok) {
							ProdVect r = intersect(p.key, q.key);
							SubstTree data = p.value.inc();
							data.sub() = q.value.sub();
							data.tree() = q.value.tree();
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
