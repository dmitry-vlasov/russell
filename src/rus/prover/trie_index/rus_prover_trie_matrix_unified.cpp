#include "../rus_prover_cartesian.hpp"
#include "rus_prover_trie_matrix.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct IndexHelper {

	enum class HypDescr {
		FREE,  // both sides have no expression trees
		LEFT,  // Left argument has an expression tree, right doesn't have
		RIGHT, // Right argument has an expression tree, left doesn't have
		BOTH,  // Both arguments have expression trees
	};

	IndexHelper(const MatrixUnified& mu, const VectorUnified& vu) :
		dim(mu.vect.size()),
		hypDescrs(dim),
		intersectedLeft(mu),
		intersectedRight(vu), intersection(nullptr) { }

	void addCells(uint i, const CartesianCell& c1, const CartesianCell& c2) {
		auto makeHypDescr = [](const CartesianCell& c1, const CartesianCell& c2) {
			if (c1.empty_index) return c2.empty_index ? HypDescr::FREE : HypDescr::RIGHT;
			else             return c2.empty_index ? HypDescr::LEFT : HypDescr::BOTH;
		};
		hypDescrs.push_back(makeHypDescr(c1, c2));
		if (hypDescrs.back() == HypDescr::RIGHT) {
			additional.addDim(intersectedRight.vect.at(i).extra_inds);
		}
	}

	struct Keys {
		vector<uint> mappingKey;
		vector<uint> cartesianKey;
	};

	struct Iterator {
		typedef map<vector<uint>, vector<FlatTermSubst>>::const_iterator Iter1;
		typedef CartesianProd<uint> Iter2;
		Iterator(Iter1 i1, Iter1 i1e, const Iter2& i2, IndexHelper& h) :
			iter1(i1), iter1end(i1e), iter2(i2), helper(h) { }

		Keys keys() const {
			Keys ret;
			vector<uint> a = iter1->first;
			vector<uint> b = iter2.data();
			for (uint k = 0, i = 0, j = 0; k < helper.dim; ++ k) {
				switch (helper.hypDescrs.at(k)) {
				case HypDescr::FREE:  break;
				case HypDescr::LEFT:  ret.cartesianKey.push_back(a[i++]); break;
				case HypDescr::RIGHT: ret.mappingKey.push_back(b[j++]); break;
				case HypDescr::BOTH:  ret.mappingKey.push_back(a[i++]); break;
				}
			}
			return ret;
		}

		bool hasNext() const {
			auto i1 = iter1; ++i1;
			return !(i1 == iter1end && !iter2.hasNext());
		}

		void makeNext() {
			if (!iter2.hasNext()) {
				++iter1;
				iter2.reset();
			} else {
				iter2.makeNext();
			}
		}

		const vector<FlatTermSubst>& termSubstVect() const {
			return iter1->second;
		}

		Iter1 iter1;
		Iter1 iter1end;
		Iter2 iter2;
		IndexHelper& helper;
	};

	Iterator initIteration(MatrixUnified& ret) {
		intersection = &ret;
		for (uint i = 0; i < dim; ++i) {
			const auto& c1 = intersectedLeft.vect.at(i);
			const auto& c2 = intersectedRight.vect.at(i);
			addCells(i, c1, c2);
			vector<uint> c0(c1.extra_inds.size() < c2.extra_inds.size() ? c1.extra_inds.size() : c2.extra_inds.size());
			auto end = std::set_intersection(
				c1.extra_inds.begin(),
				c1.extra_inds.end(),
				c2.extra_inds.begin(),
				c2.extra_inds.end(),
				c0.begin()
			);
			c0.resize(end - c0.begin());
			ret.vect.emplace_back(c0, c1.empty_index && c2.empty_index);
		}
		return Iterator(intersectedLeft.unified.begin(), intersectedLeft.unified.end(), additional, *this);
	}

	const FlatTermSubst* inside(const Keys& keys) const {
		vector<uint> mapping_part;
		for (uint i = 0, j = 0; i < dim; ++ i) {
			if (hypDescrs.at(i) == HypDescr::LEFT) {
				if (!intersection->vect.at(i).extraContains(keys.cartesianKey[j++])) {
					return nullptr;
				}
			}
		}
		auto it = intersectedRight.unified.find(keys.mappingKey);
		if (it != intersectedRight.unified.end()) {
			return &it->second;
		} else {
			return nullptr;
		}
	}

	uint dim;
	vector<HypDescr> hypDescrs;
	CartesianProd<uint> additional;
	const MatrixUnified& intersectedLeft;
	const VectorUnified& intersectedRight;
	const MatrixUnified* intersection;
};

MatrixUnified MatrixUnified::intersect(const VectorUnified& vu) const {
	MatrixUnified ret(false);
	if (full) {
		for (const auto& c : vu.vect) {
			ret.vect.emplace_back(c);
		}
		for (const auto& p : vu.unified) {
			ret.unified.emplace(p.first, vector<FlatTermSubst>(1, p.second));
		}
	} else {
		assert(vect.size() == vu.vect.size());
		IndexHelper indexHelper(*this, vu);
		auto iter = indexHelper.initIteration(ret);
		while (true) {
			IndexHelper::Keys keys = iter.keys();
			if (const FlatTermSubst* ts = indexHelper.inside(keys)) {
				vector<FlatTermSubst> w(iter.termSubstVect());
				w.emplace_back(*ts);
				ret.unified.emplace(keys.mappingKey, w);
			}
			if (iter.hasNext()) {
				iter.makeNext();
			} else {
				break;
			}
		}
	}
	return ret;
}

map<vector<uint>, vector<FlatTermSubst>> MatrixUnified::unfold() const {
	CartesianProd<uint> additional;
	for (uint i = 0; i < vect.size(); ++ i) {
		const auto& c = vect[i];
		if (c.extra_inds.size()) {
			additional.addDim(c.extra_inds);
		}
	}
	if (!additional.size()) {
		return unified;
	}
	map<vector<uint>, vector<FlatTermSubst>> ret;
	if (empty() || !additional.card()) {
		return ret;
	}
	for (const auto& p : unified) {
		additional.reset();
		while (true) {
			vector<uint> extra = additional.data();
			vector<uint> key;
			for (uint i = 0, j = 0, k = 0; i < vect.size(); ++ i) {
				if (vect.at(i).extra_inds.size()) {
					key.push_back(extra.at(j++));
				} else {
					key.push_back(p.first[k++]);
				}
			}
			ret.emplace(key, p.second);
			if (additional.hasNext()) {
				additional.makeNext();
			} else {
				break;
			}
		}
	}
	return ret;
}

MultyUnifiedSubs intersect(const map<LightSymbol, VectorUnified>& terms, MultyUnifiedSubs& unif) {
	MatrixUnified common;
	vector<LightSymbol> vars;
	for (const auto& p : terms) {
		common = std::move(common.intersect(p.second));
		vars.push_back(p.first);
	}
	MultyUnifiedSubs s;
	for (const auto& q : common.unfold()) {
		vector<uint> c = q.first;
		for (uint i = 0; i < q.second.size(); ++ i) {
			const FlatTerm& term = q.second[i].term;
			const FlatSubst& sub = q.second[i].sub;
			if (!term.empty()) {
				if (unif[c].ok) {
					Subst sb = convert2subst(sub);
					Subst unified = unify_subs(MultySubst({&unif[c], &sb}));
					unif[c] = unified;
					s[c].sub[vars[i]] = apply(unified, convert2lighttree(term));
				}
			} else {
				if (sub.ok) {
					s[c];
					unif[c];
				} else {
					unif[c].ok = false;
				}
			}
		}
	}
	return s;
}

}}}}
