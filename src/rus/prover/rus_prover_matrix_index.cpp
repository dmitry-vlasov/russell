#include "rus_prover_cartesian.hpp"
#include "rus_prover_down.hpp"
#include "rus_prover_matrix_index.hpp"

namespace mdl { namespace rus { namespace prover {

MatrixIndex::MatrixIndex(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) :
	dim_hyp_(pr->premises.size()), proofInds_(dim_hyp_), empty_(false) {
	for (uint i = 0; i < dim_hyp_; ++ i) {
		const auto& proofs = pr->premises[i]->proofs;
		if (proofs.empty()) {
			empty_ = true;
			break;
		}
		if (pr->premises[i].get() != hy) {
			addProofs(proofs, i);
		} else {
			addProofs(hs, i);
		}
	}
}

void MatrixIndex::addProofs(const Hyp::Proofs& proofs, uint i) {
	proofInds_[i] = vector<uint>(proofs.size());
	for (uint j = 0; j < proofs.size(); ++j) {
		auto p = proofs[j].get();
		for (const auto& x : p->sub.sub) {
			if (!mindex_.count(x.first)) {
				mindex_[x.first] = vector<IndexInt>(dim_hyp_);
			}
			mindex_[x.first][i].add(x.second, j);
		}
		proofInds_[i][j] = j;
	}
}

void MatrixIndex::addProofs(const vector<ProofHypIndexed>& hs, uint i) {
	proofInds_[i] = vector<uint>(hs.size());
	for (uint j = 0; j < hs.size(); ++j) {
		ProofHypIndexed hi = hs[j];
		for (const auto& x : hi.proof->sub.sub) {
			if (!mindex_.count(x.first)) {
				mindex_[x.first] = vector<IndexInt>(dim_hyp_);
			}
			mindex_[x.first][i].add(x.second, hi.ind);
		}
		proofInds_[i][j] = hi.ind;
	}
}

void MatrixIndex::addProof(const ProofHyp* p, uint i, uint j) {
	proofInds_[i] = vector<uint>(1, j);
	for (const auto& x : p->sub.sub) {
		if (!mindex_.count(x.first)) {
			mindex_[x.first] = vector<IndexInt>(dim_hyp_);
		}
		mindex_[x.first][i].add(x.second, j);
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
	map<LightSymbol, VectorUnified> terms;
	for (const auto& p : mindex_) {
		VectorIndex vectIndex;
		for (uint i = 0; i < dim_hyp_; ++i) {
			const auto& ind = p.second[i];
			vectIndex.add(ind, proofInds_[i]);
		}
		terms[p.first] = unify(vectIndex);
		cout << "var " << prover::show(p.first) << " has " << terms[p.first].map().size() << " unified" << endl;
	}
	return intersect(terms, unif);
}

string MatrixIndex::show() const {
	if (empty_) {
		return "empty\n";
	}
	string ret;
	ret += "DIMENSION: " + to_string(mindex_.size()) + "x" + to_string(dim_hyp_) + "\n";
	for (const auto& p : mindex_) {
		VectorIndex vectIndex;
		for (uint i = 0; i < dim_hyp_; ++i) {
			const auto& ind = p.second[i];
			vectIndex.add(ind, proofInds_[i]);
		}
		ret += "\nVAR: " + prover::show(p.first) + "\n";
		ret += "==============================\n";
		for (uint i = 0; i < p.second.size(); ++ i) {
			ret += "index: " + to_string(i) + "\n";
			ret += "\tproof inds: " + prover::show(proofInds_[i]) + "\n";
			ret += "\tabsent inds: " + prover::show(vectIndex.obligatory(i)) + "\n\n";
			ret += p.second[i].show() + "\n";
			ret += "-----------------------------\n\n";
		}
	}
	return ret;
}

void unify_subs(MatrixIndex& mi, const Prop* pr, MultyUnifiedSubs& ret) {
	MultyUnifiedSubs unif;
	MultyUnifiedSubs gen = mi.compute(unif);
	for (const auto& p : unif) {
		if (debug_multy_index && prover::show(p.first) == "(6, 32, 28, )") {
			cout << "unify_subs: " << prover::show(p.first) <<  " --> sub: " << endl << prover::show(p.second) << endl;
			cout << "gen[p.first]: " << prover::show(gen[p.first]) << endl;
		}
		Subst sub = unify_subs(p.second, gen[p.first]);
		if (sub.ok) {
			Subst delta = pr->sub;
			delta.compose(sub);
			ret[p.first] = delta;
			if (debug_multy_index && prover::show(p.first) == "(6, 32, 28, )") {
				cout << "result sub: " << Indent::paragraph(prover::show(sub)) << endl;
				cout << "result delta: " << Indent::paragraph(prover::show(delta)) << endl;
				cout << "YES" << endl;
			}
		} else {
			if (debug_multy_index && prover::show(p.first) == "(6, 32, 28, )") {
				cout << "NO" << endl;
			}
		}
	}
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

MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {

	static int c = 0;
	c++;
	//debug_multy_index = (c == 5835);
	//debug_multy_index = (c == 483);
	if (debug_multy_index) {
		cout << "AAA" << endl;
	}

	MatrixIndex mi(pr, hy, hs);
	if (mi.empty()) {
		return MultyUnifiedSubs();
	}

	cout << "MATRIX no. " << c << ", dim: " << mi.dim_vars() << "x" << mi.dim_hyp() << ", card: " << mi.card_str() << endl;
	if (debug_multy_index) {
		cout << "MATRIX no. " << c <<  ", card: " << mi.card_str() << endl ;
		cout << mi.show() << endl;
	}

	MultyUnifiedSubs ret;
	try {
		unify_subs(mi, pr, ret);
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
		unify_subs(mi, pr, ret);
		throw e;
	}
	return ret;
}


}}}

