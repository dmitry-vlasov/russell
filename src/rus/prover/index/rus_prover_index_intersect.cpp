#include "../rus_prover_cartesian.hpp"
#include "rus_prover_index_matrix.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

struct IndexHelper {

	enum class HypDescr {
		CART_CART, // both sides are Cartesian products
		TREE_CART, // Left argument is an expression tree, right is Cartesian
		CART_TREE, // Right argument has an expression tree, left is Cartesian
		TREE_TREE, // Both arguments are expression trees
	};

	IndexHelper(const MatrixUnified& mu, const VectorUnified& vu) :
		dim(mu.vect.size()),
		hypDescrs(dim),
		intersectedLeft(mu),
		intersectedRight(vu), intersection(nullptr) { }

	void addCells(uint i, const CartesianCell& c1, const CartesianCell& c2) {
		auto makeHypDescr = [](const CartesianCell& c1, const CartesianCell& c2) {
			if (c1.skipped) return c2.skipped ? HypDescr::TREE_TREE : HypDescr::TREE_CART;
			else            return c2.skipped ? HypDescr::CART_TREE : HypDescr::CART_CART;
		};
		HypDescr descr = makeHypDescr(c1, c2);
		hypDescrs[i] = descr;
		if (!intersectedLeft.vect.at(i).skipped && descr == HypDescr::CART_TREE) {
			if (!intersectedLeft.vect.at(i).extra_inds.size()) {
				cout << "!intersectedLeft.vect.at(i).extra_inds.size()" << endl;
				cout << "intersectedLeft" << endl;
				cout << intersectedLeft.show() << endl;
			}
			additional.addDim(intersectedLeft.vect.at(i).extra_inds);
		}
	}

	static FlatTermSubst& emptyTermSubst() {
		static Term emptyTerm;
		static Subst emptySubst;
		static FlatTermSubst emptyTermSub(emptyTerm, emptySubst);
		return emptyTermSub;
	}

	struct Keys {
		Keys(IndexHelper& h) : helper(h) { }
		vector<uint> mappingKey;
		vector<uint> cartesianKey;
		IndexHelper& helper;
		string show() const {
			return "mappingKey: " + prover::show(mappingKey) + ", cartesianKey: " + prover::show(cartesianKey);
		}
		vector<uint> resultKey() const {
			vector<uint> ret;
			for (uint k = 0, i = 0, j = 0; k < helper.dim; ++ k) {
				switch (helper.hypDescrs[k]) {
				case HypDescr::CART_CART: break;
				case HypDescr::TREE_CART: ret.push_back(cartesianKey[i++]); break;
				case HypDescr::CART_TREE: ret.push_back(mappingKey[j++]); break;
				case HypDescr::TREE_TREE: ret.push_back(mappingKey[j++]); break;
				}
			}
			return ret;
		}
	};

	struct Iterator {
		typedef map<vector<uint>, vector<FlatTermSubst>>::const_iterator Iter1;
		typedef CartesianProd<uint> Iter2;
		Iterator(Iter1 i1, Iter1 i1e, const Iter2& i2, IndexHelper& h) :
			iter1(i1), iter1end(i1e), iter2(i2), helper(h), non_trivial_iter1(iter1 != iter1end) { }

		Keys keys() const {
			Keys ret(helper);
			if (non_trivial_iter1) {
				vector<uint> a = iter1->first;
				vector<uint> b = iter2.data();
				for (uint k = 0, i = 0, j = 0; k < helper.dim; ++ k) {
					switch (helper.hypDescrs.at(k)) {
					case HypDescr::CART_CART: break;
					case HypDescr::TREE_CART: ret.cartesianKey.push_back(a[i++]); break;
					case HypDescr::CART_TREE: {
						if (!ret.helper.intersectedLeft.vect[k].skipped) {
							ret.mappingKey.push_back(b[j++]);
						}
						break;
					}
					case HypDescr::TREE_TREE: ret.mappingKey.push_back(a[i++]); break;
					}
				}
			} else {
				vector<uint> b = iter2.data();
				for (uint k = 0, j = 0; k < helper.dim; ++ k) {
					switch (helper.hypDescrs.at(k)) {
					case HypDescr::CART_CART: break;
					case HypDescr::TREE_CART: throw Error("impossible:  IndexHelper::Iterator::keys()"); break;
					case HypDescr::CART_TREE: {
						if (!ret.helper.intersectedLeft.vect[k].skipped) {
							ret.mappingKey.push_back(b[j++]);
						}
						break;
					}
					case HypDescr::TREE_TREE: throw Error("impossible:  IndexHelper::Iterator::keys()"); break;
					}
				}
			}
			return ret;
		}

		bool hasNext() const {
			if (non_trivial_iter1) {
				auto i1 = iter1; ++i1;
				return !(i1 == iter1end && !iter2.hasNext());
			} else {
				return iter2.hasNext();
			}
		}

		void makeNext() {
			if (non_trivial_iter1) {
				if (!iter2.hasNext()) {
					++iter1;
					iter2.reset();
				} else {
					iter2.makeNext();
				}
			} else {
				iter2.makeNext();
			}
		}

		vector<FlatTermSubst> termSubstVect() const {
			if (non_trivial_iter1) {
				return iter1->second;
			} else {
				return vector<FlatTermSubst>{emptyTermSubst()};
			}
		}

		string show() const {
			ostringstream ret;
			if (non_trivial_iter1) {
				ret << "IndexHelper::Iterator: <" << prover::show(iter1->first) << ", " << prover::show(iter2.data()) << ">";
			} else {
				ret << "IndexHelper::Iterator: < -- , " << prover::show(iter2.data()) << ">";
			}
			return ret.str();
		}

		Iter1 iter1;
		Iter1 iter1end;
		Iter2 iter2;
		IndexHelper& helper;
		bool non_trivial_iter1;
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
			ret.vect.emplace_back(c0, c1.empty_index && c2.empty_index, c1.skipped || c2.skipped);
		}
		return Iterator(intersectedLeft.unified.begin(), intersectedLeft.unified.end(), additional, *this);
	}

	const FlatTermSubst* inside(const Keys& keys) const {
		for (uint i = 0, j = 0; i < dim; ++ i) {
			if (hypDescrs.at(i) == HypDescr::TREE_CART) {
				if (!intersectedRight.vect.at(i).extraContains(keys.cartesianKey[j++])) {
					return nullptr;
				}
			}
		}
		if (keys.mappingKey.size()) {
			auto it = intersectedRight.unified.find(keys.mappingKey);
			if (it != intersectedRight.unified.end()) {
				return &it->second;
			} else {
				return nullptr;
			}
		} else {
			return &emptyTermSubst();
		}
	}

	string show() const {
		auto show_descr = [](HypDescr d) {
			switch (d) {
			case HypDescr::CART_CART: return "CART_CART";
			case HypDescr::TREE_CART: return "TREE_CART";
			case HypDescr::CART_TREE: return "CART_TREE";
			case HypDescr::TREE_TREE: return "TREE_TREE";
			}
		};
		ostringstream ret;
		ret << "<IndexHelper>" << endl;
		ret << "dim: " << dim << endl;
		ret << "hyp descr: " << endl;
		for (auto d : hypDescrs) {
			ret << show_descr(d) << ", ";
		}
		ret << endl;
		ret << "additional:" << endl;
		ret << Indent::paragraph(additional.show()) << endl;
		return ret.str();
	}

	uint dim;
	vector<HypDescr> hypDescrs;
	CartesianProd<uint> additional;
	const MatrixUnified& intersectedLeft;
	const VectorUnified& intersectedRight;
	const MatrixUnified* intersection;
};

MatrixUnifiedUnion MatrixUnifiedUnion::intersect(const VectorUnifiedUnion& vuu) const {
	if (kind == EMPTY || vuu.card() == 0) {
		return MatrixUnifiedUnion(EMPTY);
	}
	MatrixUnifiedUnion ret(NORM);
	if (kind == FULL) {
		for (const auto& vu : vuu.union_) {
			MatrixUnified mu;
			for (const auto& c : vu.vect) {
				mu.vect.emplace_back(c);
			}
			for (const auto& p : vu.unified) {
				mu.unified.emplace(p.first, vector<FlatTermSubst>(1, p.second));
			}
			ret.union_.push_back(mu);
		}
	} else {
		for (const auto& vu : vuu.union_) {
			if (vu.empty()) continue;
			for (const auto& mu : union_) {
				if (mu.empty()) continue;
				assert(mu.vect.size() == vu.vect.size());
				IndexHelper indexHelper(mu, vu);
				MatrixUnified mu_new;
				auto iter = indexHelper.initIteration(mu_new);
				try {
					while (true) {
						IndexHelper::Keys keys = iter.keys();
						if (const FlatTermSubst* ts = indexHelper.inside(keys)) {
							vector<FlatTermSubst> w(iter.termSubstVect());
							w.emplace_back(*ts);
							vector<uint> resultKeys = keys.resultKey();
							mu_new.unified.emplace(resultKeys, w);
						}
						if (iter.hasNext()) {
							iter.makeNext();
						} else {
							break;
						}
					}
				} catch (Error& err) {
					cout << "IndexHelper:" << endl;
					cout << indexHelper.show() << endl;
					throw err;
				}
				if (!mu_new.empty()) {
					ret.union_.push_back(mu_new);
				}
			}
		}
	}
	return ret;
}

static vector<uint> optimize_intersection_order(const map<uint, VectorUnifiedUnion>& terms) {
	vector<uint> ret;
	for (const auto& p : terms) {
		ret.push_back(p.first);
	}
	std::sort(
		ret.begin(),
		ret.end(),
		[&terms](uint v1, uint v2) {
			return terms.at(v1).card() < terms.at(v2).card();
		}
	);
	return ret;
}

Timer intersect_unfold_timer(true, true);
Timer intersect_inner_timer(true, true);
Timer intersect_compose_timer(true, true);

MultyUnifiedSubs intersect(const map<uint, VectorUnifiedUnion>& terms, MultyUnifiedSubs& unif) {
	MatrixUnifiedUnion common;
	MultyUnifiedSubs s;

	intersect_inner_timer.start();
	vector<uint> vars = optimize_intersection_order(terms);
	for (uint v : vars) {
		Timer timer; timer.start();
		common = std::move(common.intersect1(terms.at(v)));
		//common = std::move(common.intersect(terms.at(v)));
		timer.stop();
		if (common.empty()) {
			return s;
		}
	}
	intersect_inner_timer.stop();

	intersect_unfold_timer.start();
	map<vector<uint>, vector<FlatTermSubst>> unfolded = common.unfold();
	intersect_unfold_timer.stop();


	intersect_compose_timer.start();
	for (const auto& q : unfolded) {
		vector<uint> c = q.first;
		for (uint i = 0; i < q.second.size(); ++ i) {
			const Term& term = *q.second[i].term;
			const Subst& sub = *q.second[i].sub;
			if (!term.empty()) {
				if (unif[c].ok()) {
					Subst unified = unify_subs(MultySubst({&unif[c], &sub}));
					unif[c] = unified;
					s[c].compose(vars[i], unified.apply(term), CompMode::DUAL);
				}
			} else {
				if (sub.ok()) {
					s[c];
					unif[c];
				} else {
					unif[c].spoil();
				}
			}
		}
	}
	intersect_compose_timer.stop();
	return s;
}

}}}}
