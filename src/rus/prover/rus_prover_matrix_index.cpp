#include "rus_prover_cartesian.hpp"
#include "rus_prover_down.hpp"
#include "rus_prover_matrix_index.hpp"

namespace mdl { namespace rus { namespace prover {

void MatrixIndex::addProofs(const Hyp::Proofs& proofs, uint i) {
	proofInds_[i] = vector<uint>(proofs.size());
	for (uint j = 0; j < proofs.size(); ++j) {
		auto p = proofs[j].get();
		for (const auto& x : p->sub.sub) {
			if (!mindex_.count(x.first)) {
				mindex_[x.first] = vector<IndexInt>(dim_hyp);
			}
			mindex_[x.first][i].add(x.second, j);
		}
		proofInds_[i][j] = j;
	}
}

void MatrixIndex::addProof(const ProofHyp* p, uint i, uint j) {
	proofInds_[i] = vector<uint>(1, j);
	for (const auto& x : p->sub.sub) {
		if (!mindex_.count(x.first)) {
			mindex_[x.first] = vector<IndexInt>(dim_hyp);
		}
		mindex_[x.first][i].add(x.second, j);
	}
}

MultyUnifiedSubs MatrixIndex::compute(MultyUnifiedSubs& unif) {
	if (mindex_.empty()) {
		CartesianProd<uint> proofs_prod;
		for (uint i = 0; i < dim_hyp; ++ i) {
			proofs_prod.incSize();
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
	map<LightSymbol, VectorUnified> terms;
	for (const auto& p : mindex_) {
		VectorIndex vectIndex;
		for (uint i = 0; i < dim_hyp; ++i) {
			const auto& ind = p.second[i];
			vectIndex.add(ind, proofInds_[i]);
		}
		terms[p.first] = unify(vectIndex);
		if (debug_multy_index) {
			cout << "unified terms for: " << prover::show(p.first) << endl;
			cout << Indent::paragraph(prover::show(terms[p.first])) << endl;
		}
	}
	set<vector<uint>> common;
	if (!terms.empty()) {
		for (const auto &p : terms.begin()->second) {
			bool is_common = true;
			for (const auto &q : terms) {
				if (!q.second.count(p.first)) {
					if (debug_multy_index) {
						cout << "non common = " << prover::show(p.first) << endl;
					}
					is_common = false;
					break;
				}
			}
			if (is_common) {
				if (debug_multy_index) {
					cout << "common = " << prover::show(p.first) << endl;
				}
				common.insert(p.first);
			}
		}
	}
	MultyUnifiedSubs s;
	for (const auto& c : common) {
		for (const auto& p : terms) {
			//if (p.second.at(c).tree.empty()) {
			//	continue;
			//}
			if (debug_multy_index) {
				cout << prover::show(c) << ", " << prover::show(p.first) <<  " --> term: " << prover::show(p.second.at(c).tree) << endl;
			}
			s[c].sub[p.first] = p.second.at(c).tree;
			unif[c] = p.second.at(c).sub;
		}
	}
	return s;
}

string MatrixIndex::show() const {
	string ret;
	ret += "DIMENSION: " + to_string(mindex_.size()) + "x" + to_string(dim_hyp) + "\n";
	for (const auto& p : mindex_) {
		ret += "\nVAR: " + prover::show(p.first) + "\n";
		ret += "==============================\n";
		for (uint i = 0; i < p.second.size(); ++ i) {
			ret += "index: " + to_string(i) + ", proof inds: " + prover::show(proofInds_[i]) + "\n";
			ret += p.second[i].show() + "\n";
			ret += "-----------------------------\n\n";
		}
	}
	return ret;
}

MultyUnifiedSubs unify_subs(MatrixIndex& mi, const Prop* pr) {
	MultyUnifiedSubs ret;
	MultyUnifiedSubs unif;
	MultyUnifiedSubs gen = mi.compute(unif);
	for (const auto& p : unif) {
		if (debug_multy_index) {
			cout << "unify_subs: " << prover::show(p.first) <<  " --> sub: " << endl << prover::show(p.second) << endl;
			cout << "gen[p.first]: " << prover::show(gen[p.first]) << endl;
		}
		Subst sub = unify_subs(p.second, gen[p.first]);
		if (sub.ok) {
			Subst delta = pr->sub;
			delta.compose(sub);
			ret[p.first] = delta;
			if (debug_multy_index) {
				cout << "YES" << endl;
			}
		} else {
			if (debug_multy_index) {
				cout << "NO" << endl;
			}
		}
	}
	return ret;
}

bool check_matrix_unification(const vector<uint>& leafs, const Subst& sub, Prop* pr, const ProofHyp* h) {
	uint arity = pr->premises.size();
	vector<Subst> subvector(arity);

	for (uint i = 0; i < arity; ++ i) {
		const auto& proofs = pr->premises[i]->proofs;
		if (pr->premises[i].get() != &h->node) {
			subvector[i] = proofs[leafs[i]]->sub;
		} else {
			subvector[i] = h->sub;
		}
	}

	if (debug_multy_index) {
		cout << endl << "CHECKING MATRIX UNIFICATION" << endl;
		cout << "UNIFIER: " << show(sub) << endl;
	}

	Subst common;
	bool first = true;
	for (auto& s : subvector) {
		Subst ss(s);
		ss.compose(sub);
		if (!first && common != ss) {
			cout << "MATRIX UNIFICATION FAILS" << endl;
			//cout << show(ss) << " != " << show(common) << endl << endl;
			cout << "SUB: " << show(s) << endl;
			cout << "ss: " << show(ss) << endl;
			cout << "common: " << show(common) << endl;
			return false;
		}
		if (first){
			common = ss;
			first = false;
		}
	}
	if (debug_multy_index) {
		cout << "COMMON: " << show(common) << endl;
	}
	return true;
}

MultyUnifiedSubs unify_subs_matrix(Prop* pr, const ProofHyp* h) {

	static int c = 0;
	c++;
	debug_multy_index = (c == 560);
	if (debug_multy_index) {
		cout << "AAA" << endl;
	}

	uint arity = pr->premises.size();
	MatrixIndex mi(arity);
	for (uint i = 0; i < arity; ++ i) {
		const auto& proofs = pr->premises[i]->proofs;
		if (proofs.empty()) {
			return MultyUnifiedSubs();
		}
		if (pr->premises[i].get() != &h->node) {
			mi.addProofs(proofs, i);
		} else {
			mi.addProof(h, i, find_in_vector(proofs, h));
		}
	}

	if (debug_multy_index) {
		cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
	}

	try {
		MultyUnifiedSubs ret = unify_subs(mi, pr);
		/*for (const auto& p : ret) {
			if (!check_matrix_unification(p.first, p.second, pr, h)) {
				cout << "MATRIX no. " << c << endl;
				cout << mi.show() << endl;
				throw Error("MATRIX UNIFICATION ERROR");
			}
		}*/
		return ret;
	} catch (Error& err) {
		debug_multy_index_1 = true;
		cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
		//return unify_subs(mi, pr);
		throw err;
	} catch (std::exception& e) {
		debug_multy_index_1 = true;
		cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
		return unify_subs(mi, pr);
		throw e;
	}
}

}}}

