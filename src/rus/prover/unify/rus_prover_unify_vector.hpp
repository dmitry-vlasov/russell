#pragma once

#include "../rus_prover_cartesian.hpp"
#include "../unify/rus_prover_unify_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

struct CartesianCell {
	CartesianCell(const vector<uint>& ex, bool em, bool s) :
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
			"extra_inds: " + prover::show(extra_inds) + ", card: " + to_string(card()) + "\n";
		return ret;
	}
	uint card() const {
		return skipped ? 1 : extra_inds.size();
	}
	bool operator == (const CartesianCell& c) const {
		return extra_inds == c.extra_inds && empty_index == c.empty_index && skipped == c.skipped;
	}
	bool operator != (const CartesianCell& c) const {
		return !operator == (c);
	}
	vector<uint> extra_inds;
	const bool empty_index;
	const bool skipped;
};

template<class T>
string show_MapUnified(const T&);

template<>
inline string show_MapUnified<TermSubst>(const TermSubst& ts) {
	return ts.show();
}

template<>
inline string show_MapUnified<vector<TermSubst>>(const vector<TermSubst>& vect) {
	string ret;
	for (uint i = 0; i < vect.size(); ++ i) {
		const auto& ts = vect.at(i);
		ret += Indent::paragraph(to_string(i) + " - " + ts.show() + "\n");
	}
	return ret;
}

template<class T>
struct MapUnified {
	MapUnified() = default;
	MapUnified(vector<CartesianCell>&& v, map<vector<uint>, T>&& u) : vect(std::move(v)), unified(std::move(u)) { }
	explicit MapUnified(const MapUnified&) = default;
	MapUnified(MapUnified&&) = default;

	string showKeys(const vector<uint>& v) const {
		string ret;
		for (uint i = 0, j = 0; i < vect.size(); ++ i) {
			if (vect.at(i).skipped) {
				if (v.size() <= j) {
					cout << "CCCCFUCK!!!   i = " << i << endl;
					cout << "v: " << prover::show(v) << endl;
					cout << "cells:\n" << showCells() << endl;
				}
				ret += to_string(v.at(j++)) + ", ";
			} else {
				ret += prover::show(vect.at(i).extra_inds) + ", ";
			}
		}
		return ret;
	}
	bool empty() const { return card() == 0; }

	string showCells() const {
		string ret;
		ret += "cartesian cells:\n";
		for (const auto& c : vect) {
			ret += Indent::paragraph(c.show());
		}
		return ret;
	}

	string show() const {
		string ret;
		ret += string("empty: ") + (empty() ? "yes" : "no") + "\n";
		ret += "card: " + to_string(card()) + "\n";
		ret += showCells();
		ret += "unified:\n";
		int c = 0;
		for (const auto& p : unified) {
			ret += "\t" + showKeys(p.first) + " -->\n" + Indent::paragraph(show_MapUnified<T>(p.second)) + "\n";
			if (++c > 8) {
				ret += "\t...\n";
				break;
			}
		}
		return ret;
	}

	uint card() const {
		uint card_ = 1;
		bool all_are_cartesian = true;
		for (const auto& cell : vect) {
			card_ *= cell.card();
			if (cell.skipped) {
				all_are_cartesian = false;
			}
		}
		return card_ * (all_are_cartesian ? 1 : unified.size());
	}

	map<vector<uint>, T> unfold(std::function<T()> def_val) const {
		if (card() == 0) {
			return map<vector<uint>, T>();
		}
		CartesianProd<uint> additional;
		for (uint i = 0; i < vect.size(); ++ i) {
			if (!vect[i].skipped) {
				additional.addDim(vect[i].extra_inds);
			}
		}
		if (!additional.size()) {
			return unified;
		}
		map<vector<uint>, T> ret;
		while (true) {
			vector<uint> extra = additional.data();
			if (unified.size()) {
				for (const auto& p : unified) {
					vector<uint> key;
					for (uint i = 0, j = 0, k = 0; i < vect.size(); ++ i) {
						if (!vect.at(i).skipped) {
							key.push_back(extra.at(j++));
						} else {
							key.push_back(p.first.at(k++));
						}
					}
					ret.emplace(key, p.second);
				}
			} else {
				ret.emplace(extra, def_val());
			}
			if (additional.hasNext()) {
				additional.makeNext();
			} else {
				break;
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
	for (uint i = 0; i < unif.size(); ++i) {
		ret += "variant no. " + to_string(i) + ", card: " + to_string(unif[i].card()) + "\n";
		ret += "----------------------\n";
		ret += unif[i].show() + "\n";
	}
	ret += "\n\n";
	return ret;
}

typedef MapUnified<TermSubst> VectorUnified;

struct VectorUnifiedUnion {
	uint card() const {
		uint card_ = 0;
		for (const auto& vu : union_) card_ += vu.card();
		return card_;
	}
	bool empty() const {
		for (const auto& vu : union_) {
			if (!vu.empty()) {
				return false;
			}
		}
		return true;
	}
	string show() const {
		return "VectorUnifiedUnion:\ncard = " + to_string(card()) + "\n" + index::show(union_);
	}
	vector<VectorUnified> union_;
};

struct Vector{
	Vector(uint dim) {
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
		void add(const Term& e, uint i) {
			exprs_inds_.push_back(i);
			exprs_.add(e, i);
		}
		bool empty() const {
			return !extra_inds_.size() && exprs_.empty();
		}
		const Index& exprs() const { return exprs_; }
		const vector<uint>& extraInds() const { return extra_inds_; }
		const vector<uint>& allInds() const { return all_inds_; }
		const vector<uint>& exprsInds() const { return exprs_inds_; }
		string show() const {
			string ret;
			ret += "extra inds: " + prover::show(extra_inds_) + "\n";
			ret += "exprs inds: " + prover::show(exprs_inds_) + "\n";
			ret += "exprs:\n";
			ret += exprs_.show();
			return ret;
		}

	private:
		Index    exprs_;
		vector<uint> extra_inds_;
		vector<uint> all_inds_;
		vector<uint> exprs_inds_;
	};
	VectorUnified unify_general(const vector<bool>& skipped) const {
		vector<const Index*> inds;
		VectorUnified ret;
		try {
			uint only_iter_ind = 0;
			for (uint i = 0; i < vect.size(); ++ i) {
				ret.vect.emplace_back(
					vect[i]->extraInds(),
					vect[i]->exprs().empty(),
					skipped[i]
				);
				if (skipped[i]) {
					only_iter_ind = i;
					inds.emplace_back(&vect[i]->exprs());
				}
			}
			if (inds.size() > 0) {
				if (inds.size() == 1) {
					for (auto it = vect[only_iter_ind]->exprs().root().nodes.begin(); it != vect[only_iter_ind]->exprs().root().nodes.end(); ++it) {
						for (const auto& end : it->second.ends) {
							for (uint ind : end->second.inds) {
								Index::Iter iter(&vect[only_iter_ind]->exprs().root().nodes, it);
								ret.unified.emplace(vector<uint>{ind}, TermSubst(iter.subTerm(end), Subst()));
							}
						}
					}
				} else {
					ret.unified = index::unify_general(inds);
				}
			}
		} catch (Error& err) {
			cout << endl << "VectorIndex::unify_general(): ERROR" << endl;
			for (auto& c : vect) {
				cout << "CELL: " << endl;
				cout << c->exprs().show_pointers() << endl << endl;
			}
			ret.unified = index::unify_general(inds);
			throw err;
		}
		return ret;
	}

	VectorUnifiedUnion unify_general() const {
		VectorUnifiedUnion ret;
		if (!empty()) {
			CartesianProd<bool> skipped_variants;

			if (skipped_variants.card() > 256) {
				cout << endl << endl << endl << "SKIPPED_VARIANTS.card() = " << skipped_variants.card() << endl << endl;
			}

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
				VectorUnified vu = unify_general(skipped);
				if (!vu.empty()) {
					ret.union_.push_back(std::move(vu));
				}
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

	string show() const {
		string ret;
		ret += "=============================\n";
		for (uint i = 0; i < vect.size(); ++ i) {
			ret += Indent::paragraph(vect[i]->show()) + "\n";
			ret += "-----------------------------\n\n";
		}
		return ret;
	}

	vector<unique_ptr<Cell>> vect;
};

}}}}
