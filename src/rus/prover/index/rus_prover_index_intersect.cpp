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

	static TermSubst& emptyTermSubst() {
		static Term emptyTerm;
		static Subst emptySubst;
		static TermSubst emptyTermSub(emptyTerm, emptySubst);
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

	struct Keys2 {
		Keys2(IndexHelper& h) : helper(h) { }
		void setRight(const vector<uint>& v) {
			for (uint n = 0, i = 0; n < helper.dim; ++ n) {
				switch (helper.hypDescrs.at(n)) {
				case HypDescr::CART_CART: break;
				case HypDescr::TREE_CART: break;
				case HypDescr::CART_TREE: rightPart.push_back(v[i++]); break;
				case HypDescr::TREE_TREE: bothPart.push_back(v[i++]);  break;
				}
			}
		}
		void setLeft(const vector<uint>& v) {
			for (uint n = 0, i = 0; n < helper.dim; ++ n) {
				switch (helper.hypDescrs.at(n)) {
				case HypDescr::CART_CART: break;
				case HypDescr::TREE_CART: leftPart.push_back(v[i++]); break;
				case HypDescr::CART_TREE: break;
				case HypDescr::TREE_TREE: bothPart.push_back(v[i++]);  break;
				}
			}
		}
		vector<uint> getAll() const {
			vector<uint> ret;
			for (uint n = 0, i = 0, j = 0, k = 0; n < helper.dim; ++ n) {
				switch (helper.hypDescrs.at(n)) {
				case HypDescr::CART_CART: break;
				case HypDescr::TREE_CART: ret.push_back(leftPart[i++]);  break;
				case HypDescr::CART_TREE: ret.push_back(rightPart[j++]); break;
				case HypDescr::TREE_TREE: ret.push_back(bothPart[k++]);  break;
				}
			}
			return ret;
		}
		bool leftKeyIsInside() const {
			for (uint i = 0, j = 0; i < helper.dim; ++ i) {
				if (helper.hypDescrs.at(i) == HypDescr::TREE_CART) {
					if (!helper.intersectedRight.vect.at(i).extraContains(leftPart[j++])) {
						return false;
					}
				}
			}
			return true;
		}
		bool rightKeyIsInside() const {
			for (uint i = 0, j = 0; i < helper.dim; ++ i) {
				if (helper.hypDescrs.at(i) == HypDescr::CART_TREE) {
					if (!helper.intersectedLeft.vect.at(i).extraContains(rightPart[j++])) {
						return false;
					}
				}
			}
			return true;
		}
		string show() const {
			return "left: " + prover::show(leftPart) + ", right: " + prover::show(rightPart) + ", both: " + prover::show(bothPart);
		}

		vector<uint> leftPart;
		vector<uint> bothPart;
		vector<uint> rightPart;
		IndexHelper& helper;
	};

	struct Iterator {
		typedef map<vector<uint>, vector<TermSubst>>::const_iterator Iter1;
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

		vector<TermSubst> termSubstVect() const {
			if (non_trivial_iter1) {
				return iter1->second;
			} else {
				return vector<TermSubst>{emptyTermSubst()};
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

	const TermSubst* inside(const Keys& keys) const {
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

bool debug_intersect1;

MatrixUnifiedUnion MatrixUnifiedUnion::intersect(const VectorUnifiedUnion& vuu, uint i) const {
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
				mu.unified.emplace(p.first, vector<TermSubst>(1, p.second));
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

				/*if (!vu.unified.size()) {
					for (const auto& p : mu.unified) {
						IndexHelper::Keys2 key(indexHelper);
						key.setLeft(p.first);
						if (!key.leftKeyIsInside()) {
							continue;
						}
						vector<TermSubst> w(p.second);
						w.emplace_back();
						mu_new.unified.emplace(p.first, w);
					}
				} else if (!mu.unified.size()) {
					for (const auto& p : vu.unified) {
						IndexHelper::Keys2 key(indexHelper);
						key.setRight(p.first);
						if (!key.rightKeyIsInside()) {
							continue;
						}
						vector<TermSubst> w(i);
						w.emplace_back(p.second);
						mu_new.unified.emplace(p.first, w);
					}
				} else {*/
					try {
						while (true) {
							IndexHelper::Keys keys = iter.keys();
							if (const TermSubst* ts = indexHelper.inside(keys)) {
								vector<TermSubst> w(iter.termSubstVect());
								w.emplace_back(*ts);

								if (debug_intersect1) {
									cout << "w.size() = " << w.size() << endl;
								}

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
				//}
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

void check_unification_results_equal(const MatrixUnified& old_one, const MatrixUnified& new_one) {
	if (old_one.vect.size() != new_one.vect.size()) {
		throw Error("unification cell vect sizes differ: " + to_string(old_one.vect.size()) + " !=  " + to_string(new_one.vect.size()));
	}
	for (int i = 0; i < old_one.vect.size(); ++ i) {
		if (old_one.vect[i] != new_one.vect[i]) {
			throw Error("unification cell vect differ: " + old_one.vect[i].show() + " != " + new_one.vect[i].show());
		}
	}
	for (const auto& p : old_one.unified) {
		auto i = new_one.unified.find(p.first);
		if (i == new_one.unified.end()) {
			cout << "NEW UNIFIED:" << endl;
			for (const auto& q : new_one.unified) {
				cout << prover::show(q.first) << " --> " << endl;
			}

			throw Error("new unified does't have key: " + prover::show(p.first));
		}
	}
	for (const auto& p : new_one.unified) {
		auto i = old_one.unified.find(p.first);
		if (i == old_one.unified.end()) {
			throw Error("old unified does't have key: " + prover::show(p.first));
		}
	}
}

void check_union_unification_results_equal(const MatrixUnifiedUnion& old_one, const MatrixUnifiedUnion& new_one) {
	if (old_one.kind != new_one.kind) {
		throw Error("matrix union unification kinds differ");
	}
	if (old_one.union_.size() != new_one.union_.size()) {
		throw Error("matrix union unification sizes differ: " + to_string(old_one.union_.size()) + " != " + to_string(new_one.union_.size()));
	}
	for (int i = 0; i < old_one.union_.size(); ++ i) {
		check_unification_results_equal(old_one.union_[i], new_one.union_[i]);
	}
}

bool isDefault(const vector<TermSubst>& tsv) {
	for (const auto& ts : tsv) {
		if (!ts.isDefault()) {
			return false;
		}
	}
	return true;
}

void check_union_unification_results_equal_1(const MatrixUnifiedUnion& old_one, const MatrixUnifiedUnion& new_one, uint c) {
	map<vector<uint>, vector<TermSubst>> unfolded_old = old_one.unfold([c]() { return vector<TermSubst>(c); });
	map<vector<uint>, vector<TermSubst>> unfolded_new = new_one.unfold([c]() { return vector<TermSubst>(c); });
	string err;
	if (unfolded_old.size() != unfolded_new.size()) {
		err += "matrix union unification sizes differ: " + to_string(unfolded_old.size()) + " != " + to_string(unfolded_new.size()) + "\n";
	}
	for (const auto& p : unfolded_old) {
		if (!unfolded_new.count(p.first)) {
			err += "new unified does't have key: " + prover::show(p.first) + "\n";
		}
		const auto& v_old = p.second;
		const auto& v_new = unfolded_new.at(p.first);
		if (v_old.size() != v_new.size() && !(isDefault(v_old) && isDefault(v_new))) {
			err += "A) sizes at key: " + prover::show(p.first) + " differ: " + to_string(v_old.size()) + " != " + to_string(v_new.size()) + "\n";
			err += "c = " + to_string(c) + "\n";
			err += "old values:\n";
			err += show_MapUnified(v_old);
			err += "new values:\n";
			err += show_MapUnified(v_new);
		} else if (!(isDefault(v_old) && isDefault(v_new))) {
			for (uint i = 0; i < v_old.size(); ++i) {
				if (v_old.at(i) != v_new.at(i)) {
					err += "A) values at key: " + prover::show(p.first) + " differ:\n";
					err += show_MapUnified(v_old.at(i)) + "\n != \n";
					err += show_MapUnified(v_new.at(i)) + "\n";
				}
			}
		}
	}

	for (const auto& p : unfolded_new) {
		if (!unfolded_old.count(p.first)) {
			err += "old unified does't have key: " + prover::show(p.first) + "\n";
		}
		const auto& v_new = p.second;
		const auto& v_old = unfolded_old.at(p.first);
		if (v_old.size() != v_new.size() && !(isDefault(v_old) && isDefault(v_new))) {
			err += "B) sizes at key: " + prover::show(p.first) + " differ: " + to_string(v_old.size()) + " != " + to_string(v_new.size()) + "\n";
		} else if (!(isDefault(v_old) && isDefault(v_new))) {
			for (uint i = 0; i < v_old.size(); ++i) {
				if (v_old.at(i) != v_new.at(i)) {
					err += "B) values at key: " + prover::show(p.first) + " differ:\n";
					err += show_MapUnified(v_old.at(i)) + "\n != \n";
					err += show_MapUnified(v_new.at(i)) + "\n";
				}
			}
		}
	}

	if (err.size()) {
		throw Error(err);
	}
}


MultyUnifiedSubs intersect(const map<uint, VectorUnifiedUnion>& terms, MultyUnifiedSubs& unif) {
	MatrixUnifiedUnion common_new;
	MultyUnifiedSubs s;

	intersect_inner_timer.start();
	vector<uint> vars = optimize_intersection_order(terms);
	for (uint i = 0; i < vars.size(); ++ i) {
		uint v = vars[i];
		auto intersection = common_new.intersect1(terms.at(v), i );
		common_new = std::move(intersection);
		if (common_new.empty()) {
			return s;
		}
	}
	intersect_inner_timer.stop();

	intersect_unfold_timer.start();
	map<vector<uint>, vector<TermSubst>> unfolded = common_new.unfold([&vars]() { return vector<TermSubst>(vars.size()); });
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
