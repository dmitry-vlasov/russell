#include "rus_prover_cartesian.hpp"
#include "rus_prover_down.hpp"
#include "rus_prover_multy_index.hpp"

namespace mdl { namespace rus { namespace prover {

struct MatrixIndex {
	MatrixIndex(uint hd) : dim_hyp(hd) { }

	void addProofs(const Hyp::Proofs& proofs, uint i) {
		for (const auto& p : proofs) {
			const Subst& s = p->sub;
			for (const auto& x : s.sub) {
				if (!mindex_.count(x.first)) {
					mindex_[x.first] = vector<Index>(dim_hyp);
				}
				mindex_[x.first][i].add(x.second);
			}
		}
	}

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif) {
		MultyUnifiedSubs s;
		for (const auto& p : mindex_) {
			vector<const Index*> x;
			for (auto& i : p.second) {
				x.push_back(&i);
			}
			MultyUnifiedTerms terms = unify(x, unif, nullptr);
			for (const auto& t : terms) {
				s[t.first].sub[p.first] = terms[t.first];
			}
		}
		return s;
	}

	string show() const {
		string ret;
		ret += "DIMENSION: " + to_string(mindex_.size()) + "\n";
		for (const auto& p : mindex_) {
			ret += "\nVAR: " + prover::show(p.first) + "\n";
			ret += "==============================\n";
			for (uint i = 0; i < p.second.size(); ++ i) {
				ret += "index: " + to_string(i) + "\n";
				ret += p.second[i].show() + "\n";
				ret += "-----------------------------\n\n";
			}
		}
		return ret;
	}

private:
	uint dim_hyp;
	map<LightSymbol, vector<Index>> mindex_;
};

MultyUnifiedSubs unify_subs(MatrixIndex& mi) {
	MultyUnifiedSubs ret;
	MultyUnifiedSubs unif;
	MultyUnifiedSubs gen = mi.compute(unif);
	for (const auto& p : unif) {
		ret[p.first] = unify_subs(p.second, gen[p.first]);
	}
	return ret;
}

MultyUnifiedSubs unify_subs_matrix(Prop* pr, const ProofHyp* h) {
	uint arity = pr->premises.size();
	MatrixIndex mi(arity);
	for (uint i = 0; i < arity; ++ i) {
		if (!pr->premises[i]->proofs.size()) {
			return MultyUnifiedSubs();
		}
		mi.addProofs(pr->premises[i]->proofs, i);
	}

	static int c = 0;
	c++;
	if (debug_multy_index) {
		cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
	}

	return unify_subs(mi);}

}}}

