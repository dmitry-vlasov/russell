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

	struct Keys {
		Keys(IndexHelper& h) : helper(h) { }
		Keys(IndexHelper& h, const vector<uint>& a) : helper(h) { }
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
		/*vector<uint> getLeft() const {
			vector<uint> ret;
			for (uint n = 0, i = 0, j = 0; n < helper.dim; ++ n) {
				switch (helper.hypDescrs[k]) {
				case HypDescr::CART_CART: break;
				case HypDescr::TREE_CART: ret.push_back(leftPart[i++]);  break;
				case HypDescr::CART_TREE: break;
				case HypDescr::TREE_TREE: ret.push_back(bothPart[j++]);  break;
				}
			}
			return ret;
		}
		vector<uint> getRight() const {
			vector<uint> ret;
			for (uint n = 0, i = 0, j = 0; n < helper.dim; ++ n) {
				switch (helper.hypDescrs[k]) {
				case HypDescr::CART_CART: break;
				case HypDescr::TREE_CART: break;
				case HypDescr::CART_TREE: ret.push_back(rightPart[i++]); break;
				case HypDescr::TREE_TREE: ret.push_back(bothPart[j++]);  break;
				}
			}
			return ret;
		}*/
		vector<uint> getAll() const {
			vector<uint> ret;
			for (uint n = 0, i = 0, j = 0, k = 0; n < helper.dim; ++ n) {
				switch (helper.hypDescrs[k]) {
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

	map<vector<uint>, map<vector<uint>, FlatTermSubst>> splitMap(const map<vector<uint>, FlatTermSubst>& m) {
		map<vector<uint>, map<vector<uint>, FlatTermSubst>> ret;
		for (const auto& p : m) {
			Keys keys(*this);
			keys.setRight(p.first);
			ret[keys.bothPart].emplace(keys.rightPart, p.second);
		}
		return ret;
	}

	void initIteration(MatrixUnified& ret) {
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

MatrixUnifiedUnion MatrixUnifiedUnion::intersect1(const VectorUnifiedUnion& vuu) const {
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
				indexHelper.initIteration(mu_new);
				map<vector<uint>, map<vector<uint>, FlatTermSubst>> sm = indexHelper.splitMap(vu.unified);
				for (const auto& p : mu.unified) {
					IndexHelper::Keys key(indexHelper);
					key.setLeft(p.first);
					if (!key.leftKeyIsInside()) {
						continue;
					}
					for (const auto& q : sm[key.bothPart]) {
						key.rightPart = q.first;
						if (!key.rightKeyIsInside()) {
							continue;
						}
						vector<FlatTermSubst> w(p.second);
						w.emplace_back(q.second);
						mu_new.unified.emplace(key.getAll(), w);
					}
				}
				if (!mu_new.empty()) {
					ret.union_.push_back(mu_new);
				}
			}
		}
	}
	return ret;
}

}}}}
