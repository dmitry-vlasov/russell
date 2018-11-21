#include "../rus_prover_cartesian.hpp"
#include "rus_prover_trie_vector_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct IndexHelper {

	enum class HypDescr {
		FREE,  // both sides have no expression trees
		LEFT,  // Left argument has an expression tree, right doesn't have
		RIGHT, // Right argument has an expression tree, left doesn't have
		BOTH,  // Both arguments have expression trees
	};

	enum class Choice {
		NONE,
		LEFT, // Left argument is
		RIGHT
	};

	IndexHelper(const VectorUnified& vu1, const VectorUnified& vu2) :
		choice(Choice::NONE),
		dim(vu1.vect.size()),
		hypDescrs(dim),
		freeIndexes(dim),
		leftIndexes(dim),
		rightIndexes(dim),
		bothIndexes(dim),
		unifiedLeft(vu1), unifiedRight(vu2) { }

	void addCells(uint i, const CartesianCell& c1, const CartesianCell& c2) {
		auto makeHypDescr = [](const CartesianCell& c1, const CartesianCell& c2) {
			if (c1.is_empty) return c2.is_empty ? HypDescr::FREE : HypDescr::RIGHT;
			else             return c2.is_empty ? HypDescr::LEFT : HypDescr::BOTH;
		};
		HypDescr descr = makeHypDescr(c1, c2);
		hypDescrs.push_back(descr);
		switch (descr) {
		case HypDescr::FREE:  freeIndexes.push_back(i); break;
		case HypDescr::LEFT:  leftIndexes.push_back(i); leftCartesianSize *= c1.extra_inds.size();  break;
		case HypDescr::RIGHT: freeIndexes.push_back(i); rightCartesianSize *= c1.extra_inds.size(); break;
		case HypDescr::BOTH:  bothIndexes.push_back(i); break;
		}
	}

	struct Iterator {
		typedef map<vector<uint>, FlatTermSubst>::const_iterator Iter1;
		typedef CartesianProd<uint> Iter2;
		Iterator(Iter1 i1, Iter1 i1e, const Iter2& i2, IndexHelper& h) :
			iter1(i1), iter1end(i1e), iter2(i2), helper(h) { }

		vector<uint> data() const {
			vector<uint> ret(helper.dim);
			vector<uint> a = iter1->first;
			vector<uint> b = iter2.data();
			for (uint k = 0, i = 0, j = 0; k < helper.dim; ++ k) {
				switch (helper.hypDescrs.at(k)) {
				case HypDescr::FREE:  break;
				case HypDescr::LEFT:  ret.push_back(b[j++]); break;
				case HypDescr::RIGHT: ret.push_back(a[i++]); break;
				case HypDescr::BOTH:  ret.push_back(a[i++]); break;
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

		const FlatTermSubst* termSubst() const {
			return &iter1->second;
		}

		Iter1 iter1;
		Iter1 iter1end;
		Iter2 iter2;
		IndexHelper& helper;
	};

	Iterator initIteration(VectorUnified& ret) {
		for (uint i = 0; i < dim; ++i) {
			const auto& c1 = unifiedLeft.vect.at(i);
			const auto& c2 = unifiedRight.vect.at(i);
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
			ret.vect.emplace_back(c0, c1.is_empty && c2.is_empty);
		}
		if (leftCartesianSize * unifiedRight.unified.size() < rightCartesianSize * unifiedLeft.unified.size()) {
			for (uint i : rightIndexes) {
				additional.addDim(unifiedRight.vect.at(i).extra_inds);
			}
			choice = Choice::LEFT;
			return Iterator(unifiedLeft.unified.begin(), unifiedLeft.unified.end(), additional, *this);
		} else {
			for (uint i : leftIndexes) {
				additional.addDim(unifiedLeft.vect.at(i).extra_inds);
			}
			choice = Choice::RIGHT;
			return Iterator(unifiedRight.unified.begin(), unifiedRight.unified.end(), additional, *this);
		}
	}

	const FlatTermSubst* inside(const vector<uint>& vect) const {
		vector<uint> mapping_part;
		for (uint i = 0, j = 0; i < dim; ++ i) {
			switch (hypDescrs.at(i)) {
			case HypDescr::FREE:  break;
			case HypDescr::LEFT:  {
				switch (choice) {
				case Choice::LEFT:
					if (!unifiedRight.vect.at(i).extraContains(vect[j++])) return nullptr;
					break;
				case Choice::RIGHT: mapping_part.push_back(vect[j++]); break;
				default: assert(false && "impossible"); return nullptr;
				}
				break;
			}
			case HypDescr::RIGHT: {
				switch (choice) {
				case Choice::LEFT:  mapping_part.push_back(vect[j++]); break;
				case Choice::RIGHT:
					if (!unifiedLeft.vect.at(i).extraContains(vect[j++])) return nullptr;
					break;
				default: assert(false && "impossible"); return nullptr;
				}
				break;
			}
			case HypDescr::BOTH:  {
				mapping_part.push_back(vect[j++]); break;
			}
			}
		}
		switch (choice) {
		case Choice::LEFT:  {
			auto it = unifiedLeft.unified.find(mapping_part);
			if (it != unifiedLeft.unified.end()) {
				return &it->second;
			} else {
				return nullptr;
			}
		}
		break;
		case Choice::RIGHT: {
			auto it = unifiedRight.unified.find(mapping_part);
			if (it != unifiedRight.unified.end()) {
				return &it->second;
			} else {
				return nullptr;
			}
		}
		break;
		default: assert(false && "impossible"); return nullptr;
		}
	}

	uint dim;
	Choice choice;
	vector<HypDescr> hypDescrs;
	vector<uint> freeIndexes;
	vector<uint> leftIndexes;
	vector<uint> rightIndexes;
	vector<uint> bothIndexes;
	uint leftCartesianSize = 1;
	uint rightCartesianSize = 1;
	CartesianProd<uint> additional;
	const VectorUnified& unifiedLeft;
	const VectorUnified& unifiedRight;
};

/*
MultyUnifiedSubs intersect(const map<LightSymbol, VectorUnified>& terms, MultyUnifiedSubs& unif) {
	VectorMap<vector<SubstTree>> common(true);
	vector<LightSymbol> vars;
	for (const auto& p : terms) {
		common = std::move(intersect(common, p.second.unif_));
		vars.push_back(p.first);
	}
	MultyUnifiedSubs s;
	for (const auto& q : common.map()) {
		vector<uint> c = q.first;
		for (uint i = 0; i < q.second.size(); ++ i) {
			const LightTree& term = q.second[i].tree();
			const Subst& sub = q.second[i].sub();
			if (!term.empty()) {
				if (unif[c].ok) {
					Subst unified = unify_subs(MultySubst({&unif[c], &sub}));
					unif[c] = unified;
					s[c].sub[vars[i]] = apply(unif[c], term);
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
 */

VectorUnified intersect(const VectorUnified& vu1, const VectorUnified& vu2) {
	assert(vu1.vect.size() == vu2.vect.size());
	VectorUnified ret;
	IndexHelper indexHelper(vu1, vu2);
	auto iter = indexHelper.initIteration(ret);
	while (true) {
		vector<uint> vect = iter.data();
		if (const FlatTermSubst* ts1 = indexHelper.inside(vect)) {
			const FlatTermSubst* ts2 = iter.termSubst();
			//Subst unified = unify_subs(MultySubst({&ts1->sub, &ts2->sub}));
			//ret.unified.emplace(vect, FlatTermSubst(, unified));
		}
		if (iter.hasNext()) {
			iter.makeNext();
		} else {
			break;
		}
	}
	return ret;
}


}}}}
