#pragma once

#include "../rus_prover_cartesian.hpp"
#include "rus_prover_trie_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct CartesianCell {
	CartesianCell(const vector<uint>& ex, bool em, bool s = false) :
		extra_inds(ex), empty_index(em), skipped(s) {
		sort(extra_inds.begin(), extra_inds.end());
	}
	CartesianCell(const CartesianCell&) = default;
	CartesianCell(CartesianCell&&) = default;

	bool extraContains(uint i) const {
		return std::binary_search(extra_inds.begin(), extra_inds.end(), i);
	}
	bool empty() const {
		return !extra_inds.size() && empty_index;
	}
	string show() const {
		string ret;
		ret +=
			string(skipped ? "[skipped]" : "") +
			(empty_index ? "(empty index)" : "") +
			"extra_inds: " + prover::show(extra_inds) + "\n";
		return ret;
	}
	uint card() const {
		return skipped ? 1 : extra_inds.size();
	}
	vector<uint> extra_inds;
	const bool empty_index;
	const bool skipped;
};

template<class T>
string show_MapUnified(const T&);

template<>
inline string show_MapUnified<FlatTermSubst>(const FlatTermSubst& ts) {
	return ts.show();
}

template<>
inline string show_MapUnified<vector<FlatTermSubst>>(const vector<FlatTermSubst>& vect) {
	string ret;
	for (const auto& ts : vect) ret += ts.show() + "\n";
	return ret;
}

template<class T>
struct MapUnified {
	string showKeys(const vector<uint>& v) const {
		string ret;
		for (uint i = 0, j = 0; i < vect.size(); ++ i) {
			if (vect.at(i).skipped) {
				ret += to_string(v.at(j++)) + ", ";
			} else {
				ret += prover::show(vect.at(i).extra_inds) + ", ";
			}
		}
		return ret;
	}

	bool empty() const {
		for (const auto& c : vect) {
			if (c.empty()) {
				return true;
			}
		}
		return !unified.size();
	}

	string show() const {
		string ret;
		ret += "cartesian cells:\n";
		for (const auto& c : vect) {
			ret += Indent::paragraph(c.show());
		}
		ret += "unified:\n";
		for (const auto& p : unified) {
			ret += "\t" + showKeys(p.first) + " -->\n" + Indent::paragraph(show_MapUnified<T>(p.second)) + "\n";
		}
		return ret;
	}

	uint card() const {
		uint card_ = 1;
		for (const auto& c : vect) card_ *= c.card();
		return card_ * unified.size();
	}

	map<vector<uint>, T> unfold() const {
		if (card() == 0) {
			return map<vector<uint>, T>();
		}
		CartesianProd<uint> additional;
		PowerSetIter both_variants;
		enum CellDescr { CARTESIAN, INDEX, BOTH };
		vector<CellDescr> descrs;
		for (uint i = 0; i < vect.size(); ++ i) {
			const auto& c = vect[i];
			if (c.extra_inds.size()) {
				if (c.empty_index) {
					descrs.push_back(CARTESIAN);
				} else {
					descrs.push_back(BOTH);
					both_variants.addDim();
				}
				additional.addDim(c.extra_inds);
			} else {
				descrs.push_back(INDEX);
			}
		}
		if (!additional.size()) {
			return unified;
		}
		map<vector<uint>, T> ret;
		if (empty() || !additional.card()) {
			return ret;
		}
		for (const auto& p : unified) {
			additional.reset();
			while (true) {
				vector<uint> extra = additional.data();
				vector<uint> key;
				both_variants.reset();
				while (true) {
					for (uint i = 0, j = 0, k = 0, b = 0; i < vect.size(); ++ i) {
						if (vect.at(i).extra_inds.size()) {
							if (vect.at(i).empty_index) {
								key.push_back(extra.at(j++));
							} else {
								if (both_variants[b++]) {
									key.push_back(extra.at(j++)); ++k;
								} else {
									key.push_back(p.first[k++]); ++j;
								}
							}
						} else {
							key.push_back(p.first[k++]);
						}
					}
					ret.emplace(key, p.second);

					if (both_variants.hasNext()) {
						both_variants.makeNext();
					} else {
						break;
					}
				}

				if (additional.hasNext()) {
					additional.makeNext();
				} else {
					break;
				}
			}
		}
		return ret;
	}

	vector<CartesianCell> vect;
	map<vector<uint>, T> unified;
};

template<class T>
string show(const vector<MapUnified<T>>& unif) {
	string ret;
	ret += "vector<MapUnified>:\n";
	for (const auto& vu : unif) {
		ret += "----------------------\n";
		ret += vu.show() + "\n";
	}
	ret += "\n\n";
	return ret;
}

typedef MapUnified<FlatTermSubst> VectorUnified;

struct VectorUnifiedUnion {
	uint card() const {
		uint card_ = 0;
		for (const auto& vu : union_) card_ += vu.card();
		return card_;
	}
	string show() const {
		return trie_index::show(union_);
	}
	vector<VectorUnified> union_;
};

struct VectorIndex {
	VectorIndex(uint dim) {
		for (uint i = 0; i < dim; ++ i) vect.emplace_back(new Cell);
	}
	struct Cell {
		Cell() = default;
		Cell(const Cell&) = delete;
		void init(const vector<uint>& all_inds) {
			all_inds_ = all_inds;
			std::sort(exprs_inds_.begin(), exprs_inds_.end());
			for (uint i : all_inds_) {
				if (!std::binary_search(exprs_inds_.begin(), exprs_inds_.end(), i)) {
					extra_inds_.push_back(i);
				}
			}
		}
		void add(const LightTree& e, uint i) {
			exprs_inds_.push_back(i);
			exprs_.add(e, i);
		}
		bool empty() const {
			return !extra_inds_.size() && exprs_.empty();
		}
		const TrieIndex& exprs() const { return exprs_; }
		const vector<uint>& extraInds() const { return extra_inds_; }
		const vector<uint>& allInds() const { return all_inds_; }
		const vector<uint>& exprsInds() const { return exprs_inds_; }
		string show() const { return exprs_.show(); }

	private:
		TrieIndex    exprs_;
		vector<uint> extra_inds_;
		vector<uint> all_inds_;
		vector<uint> exprs_inds_;
	};
	VectorUnified unify_general(const vector<bool>& skipped) const {
		vector<MultyIter> iters;
		VectorUnified ret;
		try {
			for (uint i = 0; i < vect.size(); ++ i) {
				ret.vect.emplace_back(
					vect[i]->extraInds(),
					vect[i]->exprs().empty(),
					skipped[i]
				);
				if (skipped[i]) {
					iters.emplace_back(TrieIndex::TrieIter(vect[i]->exprs().root));
				}
			}
			ret.unified = trie_index::unify_general(iters);
		} catch (Error& err) {
			cout << endl << "VectorIndex::unify_general(): ERROR" << endl;
			for (auto& c : vect) {
				cout << "CELL: " << endl;
				cout << c->exprs().show_pointers() << endl << endl;
			}
			//debug_trie_index = true;
			ret.unified = trie_index::unify_general(iters);
			throw err;
		}
		return ret;
	}

	VectorUnifiedUnion unify_general() const {
		VectorUnifiedUnion ret;
		if (!empty()) {
			CartesianProd<bool> skipped_variants;
			for (auto& c : vect) {
				if (c->extraInds().size()) {
					if (c->exprs().empty()) {
						skipped_variants.addDim(vector<bool>{false});
					} else {
						skipped_variants.addDim(vector<bool>{false, true});
					}
				} else {
					skipped_variants.addDim(vector<bool>{true});
				}
			}
			while (true) {
				vector<bool> skipped = skipped_variants.data();
				ret.union_.push_back(std::move(unify_general(skipped)));
				if (skipped_variants.hasNext()) {
					skipped_variants.makeNext();
				} else {
					break;
				}
			}
		}
		return ret;
	}

	bool empty() const {
		for (const auto& c : vect) {
			if (c->empty()) {
				return true;
			}
		}
		return false;
	}

	vector<unique_ptr<Cell>> vect;
};

}}}}
