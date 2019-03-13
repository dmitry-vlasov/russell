#include "rus_prover_trie_matrix_index.hpp"

#include "../rus_prover_cartesian.hpp"

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
			else                return c2.empty_index ? HypDescr::LEFT : HypDescr::BOTH;
		};
		HypDescr descr = makeHypDescr(c1, c2);
		hypDescrs[i] = descr;
		//if (descr == HypDescr::RIGHT) {
			vector<uint> extras = std::move(unite_sorted(intersectedRight.vect.at(i).extra_inds, intersectedLeft.vect.at(i).extra_inds));
			additional.addDim(extras);
		//}
	}

	struct Keys {
		vector<uint> mappingKey;
		vector<uint> cartesianKey;
		string show() const {
			return "mappingKey: " + prover::show(mappingKey) + ", cartesianKey: " + prover::show(cartesianKey);
		}
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
				case HypDescr::LEFT:  {
					if (i >= a.size()) {
						cout << "i >= a.size(): " << i  << " >= " << a.size() << endl;
						cout << show() << endl;
						throw Error("err");
					}
					ret.cartesianKey.push_back(a[i++]); break;
				}
				case HypDescr::RIGHT: {
					if (j >= b.size()) {
						cout << "j >= b.size(): " << j << " >= " << b.size() << endl;
						cout << show() << endl;
						throw Error("err");
					}
					ret.mappingKey.push_back(b[j++]); break;
				}
				case HypDescr::BOTH:  {
					if (i >= a.size()) {
						cout << "i >= a.size(): " << i  << " >= " << a.size() << endl;
						cout << show() << endl;
						throw Error("err");
					}
					ret.mappingKey.push_back(a[i++]); break;
				}
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

		string show() const {
			vector<uint> a = iter1->first;
			vector<uint> b = iter2.data();
			ostringstream ret;
			ret << "iter1: " << prover::show(a) << endl;
			ret << "iter2: " << prover::show(b) << endl;
			return ret.str();
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

	string show() const {
		auto show_descr = [](HypDescr d) {
			switch (d) {
			case HypDescr::FREE: return "FREE";
			case HypDescr::LEFT: return "LEFT";
			case HypDescr::RIGHT: return "RIGHT";
			case HypDescr::BOTH: return "BOTH";
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
			for (const auto& mu : union_) {

				assert(mu.vect.size() == vu.vect.size());
				IndexHelper indexHelper(mu, vu);
				MatrixUnified mu_new;
				auto iter = indexHelper.initIteration(mu_new);

				if (debug_trie_index) {
					cout << "indexHelper:" << endl;
					cout << indexHelper.show() << endl;

					cout << "VectorUnified:" << endl;
					cout << vu.show() << endl;
				}

				try {
					while (true) {
						IndexHelper::Keys keys = iter.keys();

						if (debug_trie_index) {
							cout << "KEYS: " << keys.show() << endl;
						}

						if (const FlatTermSubst* ts = indexHelper.inside(keys)) {
							vector<FlatTermSubst> w(iter.termSubstVect());
							w.emplace_back(*ts);
							mu_new.unified.emplace(keys.mappingKey, w);
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
				ret.union_.push_back(mu_new);
			}
		}
	}
	return ret;
}

MultyUnifiedSubs intersect(const map<LightSymbol, VectorUnifiedUnion>& terms, MultyUnifiedSubs& unif) {

	if (debug_trie_index) {
		cout << "TO INTERSECT:" << endl;
		for (const auto& p : terms) {
			cout << "VAR: " << p.first << endl;
			cout << p.second.show() << endl;
			cout << endl;
		}
	}


	MatrixUnifiedUnion common;
	vector<LightSymbol> vars;
	for (const auto& p : terms) {
		common = std::move(common.intersect(p.second));

		if (debug_trie_index) {
			cout << "INTERSECTED:" << endl;
			cout << common.show() << endl;
		}

		vars.push_back(p.first);
	}
	MultyUnifiedSubs s;
	map<vector<uint>, vector<FlatTermSubst>> unfolded = common.unfold();

	if (debug_trie_index) {
		cout << "UNFOLDED:" << endl;
		for (const auto& p : unfolded) {
			cout << "\t" << prover::show(p.first) << " --> " << endl;
			for (const auto& t : p.second) {
				cout << "\t\t" << t.show() << endl;
			}
			cout << endl;
		}
	}

	for (const auto& q : unfolded) {
		vector<uint> c = q.first;
		for (uint i = 0; i < q.second.size(); ++ i) {
			const FlatTerm& term = *q.second[i].term;
			const FlatSubst& sub = *q.second[i].sub;
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

static void addProofs(map<LightSymbol, unique_ptr<VectorIndex>>& mindex_, vector<vector<uint>>& proofInds_, uint dim_hyp_, const Hyp::Proofs& proofs, uint i) {
	proofInds_[i] = vector<uint>(proofs.size());
	for (uint j = 0; j < proofs.size(); ++j) {
		auto p = proofs[j].get();
		for (const auto& x : p->sub.sub) {
			if (!mindex_.count(x.first)) {
				mindex_.emplace(x.first, new VectorIndex(dim_hyp_));
			}
			mindex_.at(x.first)->vect[i]->add(x.second, j);
		}
		proofInds_[i][j] = j;
	}
}

static void addProofs(map<LightSymbol, unique_ptr<VectorIndex>>& mindex_, vector<vector<uint>>& proofInds_, uint dim_hyp_, const vector<ProofHypIndexed>& hs, uint i) {
	proofInds_[i] = vector<uint>(hs.size());
	for (uint j = 0; j < hs.size(); ++j) {
		ProofHypIndexed hi = hs[j];
		for (const auto& x : hi.proof->sub.sub) {
			if (!mindex_.count(x.first)) {
				mindex_.emplace(x.first, new VectorIndex(dim_hyp_));
			}
			mindex_.at(x.first)->vect[i]->add(x.second, hi.ind);
		}
		proofInds_[i][j] = hi.ind;
	}
}

MatrixIndex::MatrixIndex(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) :
	dim_hyp_(pr->premises.size()), proofInds_(dim_hyp_), empty_(false) {
	for (uint i = 0; i < dim_hyp_; ++ i) {
		const auto& proofs = pr->premises[i]->proofs;
		if (proofs.empty()) {
			empty_ = true;
			break;
		}
		if (pr->premises[i].get() != hy) {
			addProofs(mindex_, proofInds_, dim_hyp_, proofs, i);
		} else {
			addProofs(mindex_, proofInds_, dim_hyp_, hs, i);
		}
	}
	for (auto& p : mindex_) {
		for (uint i = 0; i < dim_hyp_; ++i) {
			p.second->vect[i]->init(proofInds_[i]);
		}
	}
}

uint MatrixIndex::card() const {
	uint ret = 1;
	for (const auto& p : proofInds_) {
		ret *= p.size();
	}
	return ret;
}

string MatrixIndex::card_str() const {
	string ret;
	bool first = true;
	for (const auto& p : proofInds_) {
		if (!first) {
			ret += " x ";
		}
		ret += to_string(p.size());
		first = false;
	}
	ret += " = " + to_string(card());
	return ret;
}

uint matrix_vector_counter = 0;

MultyUnifiedSubs MatrixIndex::compute(MultyUnifiedSubs& unif) {
	if (mindex_.empty()) {
		CartesianProd<uint> proofs_prod;
		for (uint i = 0; i < dim_hyp_; ++ i) {
			proofs_prod.addDim(proofInds_[i]);
		}
		while (true) {
			vector<uint> proof_inds = proofs_prod.data();
			unif[proof_inds];
			if (!proofs_prod.hasNext()) {
				break;
			}
			proofs_prod.makeNext();
		}
		return MultyUnifiedSubs();
	}
	map<LightSymbol, VectorUnifiedUnion> unified_columns;
	matrix_vector_counter = 0;
	for (auto& p : mindex_) {
		try {
			unified_columns[p.first] = std::move(p.second->unify_general());
		} catch (Error& err) {
			cout << "while unifying matrix var: " << prover::show(p.first) << endl;
			throw err;
		}
		if (debug_trie_index) {
			cout << endl;
			cout << "var " << prover::show(p.first) << " has " << unified_columns[p.first].card() << " unified" << endl;
			cout << unified_columns[p.first].show() << endl;
			cout << endl;
		}
		matrix_vector_counter += 1;
	}
	return intersect(unified_columns, unif);
}

string MatrixIndex::show() const {
	if (empty_) {
		return "empty\n";
	}
	string ret;
	ret += "DIMENSION: " + to_string(mindex_.size()) + "x" + to_string(dim_hyp_) + "\n";
	for (auto& p : mindex_) {
		//VectorIndex vectIndex;
		//for (uint i = 0; i < dim_hyp_; ++i) {
		//	const auto& ind = p.second[i];
		//	vectIndex.add(ind, proofInds_[i]);
		//}
		ret += "\nVAR: " + prover::show(p.first) + "\n";
		ret += "==============================\n";
		for (uint i = 0; i < p.second->vect.size(); ++ i) {
			ret += "index: " + to_string(i) + "\n";
			ret += "\textra inds: " + prover::show(p.second->vect[i]->extraInds()) + "\n";
			ret += "\tall inds: " + prover::show(p.second->vect[i]->allInds()) + "\n";
			ret += "\texprs inds: " + prover::show(p.second->vect[i]->exprsInds()) + "\n";
			ret += p.second->vect[i]->show() + "\n";
			ret += "-----------------------------\n\n";
		}
	}
	return ret;
}

}}}}
