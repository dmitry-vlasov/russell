
#include "rus_prover_vector_unified.hpp"

namespace mdl { namespace rus { namespace prover {

string SubstTree::show() const {
	string ret;
	ret += "expr: " + prover::show(tree) + "\n";
	ret += Indent::paragraph(prover::show(sub)) + "\n";
	return ret;
}

string VectorUnified::show() const {
	ostringstream oss;
	for (const auto& u : unif_.map()) {
		oss << prover::show(u.first) << " --> " << endl;
		oss << "term: " << prover::show(u.second.tree) << endl;
		oss << "sub: " << prover::show(u.second.sub) << endl;
	}
	return oss.str();
}

void VectorUnified::finalize(ProdVect leafs_vect, const vector<LightSymbol>& w, const LightTree& t) {
	CartesianProd<uint> leafs_prod = leafsProd(leafs_vect);
	if (leafs_prod.card() == 0) {
		return;
	}
	while (true) {
		vector<uint> leafs = leafs_prod.data();
		finalize(leafs, w, t);
		if (!leafs_prod.hasNext()) {
			break;
		}
		leafs_prod.makeNext();
	}
}

void finalize(SubstTree& st, const vector<LightSymbol>& w, const LightTree& t) {
	if (w.size()) {
		LightTree term = unify_step(st.sub, w, t);
		if (!term.empty()) {
			st.tree = apply(st.sub, term);
		}
	} else {
		st.tree = apply(st.sub, t);
	}
}

void finalize(SubstTree& st, const vector<LightSymbol>& w, const LightTree& t, Subst& unif) {
	if (!st.sub.compose(unif)) {
	//if (!st.sub.compose(unif) || !unif.compose(st.sub)) {
		st.sub.ok = false;
		st.tree = LightTree();
		unif.ok = false;
		return;
	}
	finalize(st, w, t);
}

void VectorUnified::finalize(const vector<uint> leafs, const vector<LightSymbol>& w, const LightTree& t) {
	unif_.add(leafs, [w, t](SubstTree& st) { prover::finalize(st, w, t); });
}

extern bool debug_multy_index;

void VectorUnified::add_intersection(const vector<VectorUnified>& v, const Rule* r, const vector<LightSymbol>& w) {
	VectorMap<vector<SubstTree>> common(true);
	for (const auto& m : v) {
		common = std::move(intersect(common, m.unif_));
	}
	for (const auto& p : common.map()) {
		LightTree::Children children;
		Subst unif;
		for (const auto& st : p.second) {
			if (st.tree.empty()) {
				break;
			}
			unif = unify_subs(MultySubst({&unif, &st.sub}));
			if (!unif.ok) {
				break;
			}
			children.push_back(make_unique<LightTree>(st.tree));
		}
		if (children.size() == r->arity()) {
			LightTree term = apply(unif, LightTree(r, children));
			unif_.add(p.first, [w, term, &unif](SubstTree& st) { prover::finalize(st, w, term, unif); });
		}
	}
}

CartesianProd<uint> VectorUnified::leafsProd(const ProdVect& leafs) {
	CartesianProd<uint> leafs_prod;
	for (uint i = 0; i < leafs.vect.size(); ++ i) {
		leafs_prod.incSize();
		for (uint l : leafs[i].set()) {
			leafs_prod.incDim(l);
		}
	}
	return leafs_prod;
}

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
			const LightTree& term = q.second[i].tree;
			const Subst& sub = q.second[i].sub;

			if (debug_multy_index && prover::show(c) == "(5, 8, )") {
				cout << "ST:" << endl;
				cout << Indent::paragraph(q.second[i].show()) << endl;
				cout << "unif[" << prover::show(c) << "]" << prover::show(unif[c]) << endl;
			}

			if (!term.empty()) {
				if (unif[c].ok) {
					Subst unified = unify_subs(MultySubst({&unif[c], &sub}));

					if (debug_multy_index && prover::show(c) == "(5, 8, )") {
						cout << "UNIUFIED:" << endl;
						cout << Indent::paragraph(prover::show(unified)) << endl;
					}

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

}}}
