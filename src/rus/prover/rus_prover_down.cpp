#include <cmath>
#include <numeric>
#include "../expr/rus_expr_stats.hpp"
#include "index/rus_prover_index_unify.hpp"
#include "rus_prover_cartesian.hpp"
#include "rus_prover_tactics.hpp"
#include "rus_prover_multy_subst.hpp"
#include "rus_prover_limit.hpp"

namespace mdl { namespace rus { namespace prover {

vector<uint> error_inds;
bool debug_unify_subs = false;

void unify_subs_sequent(Prop* pr, Hyp* hy, ProofHypIndexed hi, MultyUnifiedSubs& ret, const ProofsSizeLimit* limit) {
	CartesianProd<uint> ind;
	const ProofHyp* h = hi.proof;
	if (limit) {
		for (uint i = 0; i < pr->premises.size(); ++ i) {
			auto& x = pr->premises[i];
			if (x.get() != hy) {
				ind.addDim(limit->descrVect()[i].chosen);
			} else {
				vector<uint> inds;
				for (uint j : limit->descrVect()[i].chosen) {
					inds.push_back(limit->descrVect()[i].all[j]);
				}
				ind.addFixedData(inds, hi.ind);
			}
		}
	} else {
		for (auto& x : pr->premises) {
			uint i = 0;
			vector<uint> inds(x->proofs.size(), 0);
			std::generate_n(inds.begin(), x->proofs.size(), [&i]() { return i++; });
			if (x.get() != hy) {
				ind.addDim(inds);
			} else {
				ind.addFixedData(inds, hi.ind);
			}
		}
	}
	if (ind.card() == 0) {
		return;
	}
	while (true) {
		vector<const Subst*> subs;
		bool show_debug = debug_unify_subs && (!error_inds.size() || error_inds == ind.data());
		if (show_debug) {
			cout << "CURRENT: " << ind.iter().current() << endl;
			cout << "UNIFYING: \n--------------" << endl;
			cout << "PROP: " << pr->ind << endl;
		}
		vector<uint> inds = ind.data();
		for (uint i = 0; i < inds.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[inds[i]].get();
			if (show_debug) {
				cout << ph->ind << ": " << ph->expr.show() << endl;
				cout << "sub:" << endl;
				cout << Indent::paragraph(ph->sub.show()) << endl;
			}
			subs.push_back(&ph->sub);
		}
		if (show_debug) {
			cout << "-------------" << endl;
		}
		Subst sub = unify_subs(MultySubst(subs));
		if (debug_unify_subs) {
			cout << "SUB: " << sub.show() << endl;
		}
		if (sub.ok()) {
			Subst delta = pr->sub;
			if (show_debug) {
				cout << "DELTA" << endl;
				cout << delta.show() << endl;
				cout << "SUB" << endl;
				cout << sub.show() << endl;
			}
			delta.compose(sub);
			if (debug_unify_subs) {
				cout << "SUB: " << delta.show() << endl;
			}
			ret[inds] = delta;
		}
		if (!ind.hasNext()) {
			break;
		}
		ind.makeNext();
	}
}

uint unification_space_card(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {
	uint ret = 1;
	for (auto& x : pr->premises) {
		if (x.get() != hy) {
			ret *= x->proofs.size();
		} else {
			ret *= hs.size();
		}
	}
	return ret;
}

string unification_space_card_str(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {
	string ret;
	bool first = true;
	for (auto& x : pr->premises) {
		if (!first) {
			ret += " x ";
		}
		if (x.get() != hy) {
			ret += to_string(x->proofs.size());
		} else {
			ret += to_string(hs.size());
		}
		first = false;
	}
	ret += " = " + to_string(unification_space_card(pr, hy, hs));
	return ret;
}

MultyUnifiedSubs unify_subs_sequent(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs, const ProofsSizeLimit* limit) {
	MultyUnifiedSubs ret;
	if (limit) {
		for (auto i : limit->descrVect()[limit->hypInd()].chosen) {
			if (i >= hs.size()) {
				throw Error("array index overflow: " + to_string(i) + " >= " + to_string(hs.size()));
			}
			unify_subs_sequent(pr, hy, hs[i], ret, limit);
		}
	} else {
		for (auto h : hs) {
			unify_subs_sequent(pr, hy, h, ret, limit);
		}
	}
	return ret;
}

bool similar_subs(const Subst& s1, const Subst& s2, bool verbose = false) {
	if (s1 == s2) return true;
	Subst s1_vars_inv;
	Subst s1_terms;
	for (const auto& p : s1) {
		if (p.second.kind() == Term::VAR && !s2.maps(p.first)) {
			LightSymbol w(p.first);
			s1_vars_inv.compose(p.second.var().lit, Term(w));
		} else {
			s1_terms.compose(p.first, p.second);
		}
	}
	s1_terms.compose(s1_vars_inv);
	bool ret = (s2 == s1_terms);
	if (!ret && verbose) {
		cout << "diff:" << endl << Indent::paragraph(show_diff(s2, s1_terms)) << endl;
		cout << "s1: " << s1.show() << endl;
		cout << "s2: " << s2.show() << endl;
		cout << "var replacement: " << endl << s1_vars_inv.show() << endl;
	}
	return ret;
}


bool compare_unified_subs(const MultyUnifiedSubs& ms1, const MultyUnifiedSubs& ms2, bool verbose = false) {
	if (ms1.size() != ms2.size()) {
		if (verbose) {
			cout << "sizes differ: " << ms1.size() << " != " << ms2.size() << endl;
			cout << "first: " << endl;
			cout << show(ms1) << endl;
			cout << "second: " << endl;
			cout << show(ms2) << endl;
		}
		return false;
	}
	for (const auto p1 : ms1) {
		if (!ms2.count(p1.first)) {
			if (verbose) {
				cout << "second doens't have key: " << show(p1.first) << endl;
			}
			return false;
		}
		if (!similar_subs(p1.second, ms2.at(p1.first), verbose)) {
			if (verbose) {
				cout << "on key: " << show(p1.first) << endl;
			}
			return false;
		}
	}
	for (const auto p2 : ms2) {
		if (!ms1.count(p2.first)) {
			if (verbose) {
				cout << "first doens't have key: " << show(p2.first) << endl;
			}
			return false;
		}
		if (!similar_subs(p2.second, ms1.at(p2.first), verbose)) {
			if (verbose) {
				cout << "on key: " << show(p2.first) << endl;
			}
			return false;
		}
	}
	return true;
}

string unified_subs_diff(const MultyUnifiedSubs& ms1, const MultyUnifiedSubs& ms2) {
	string ret;
	if (ms1.size() != ms2.size()) {
		ret += "sequential.size() = " + to_string(ms1.size()) + " != " + to_string(ms2.size()) + " = matrix.size()\n";
	}
	for (const auto p1 : ms1) {
		if (!ms2.count(p1.first)) {
			ret += "matrix doesn't have key" + show(p1.first) + "\n";
			ret += "sequential value:\n";
			ret += Indent::paragraph(p1.second.show());
		} else if (!similar_subs(p1.second, ms2.at(p1.first), false)) {
			ret += "sequential and matrix values for key" + show(p1.first) + " differ\n";
			ret += "diff:\n";
			ret += Indent::paragraph(show_diff(p1.second, ms2.at(p1.first)));
			ret += "sequential value:\n";
			ret += Indent::paragraph(p1.second.show());
			ret += "matrix value:\n";
			ret += Indent::paragraph(ms2.at(p1.first).show());
		}
	}
	for (const auto p2 : ms2) {
		if (!ms1.count(p2.first)) {
			ret += "sequential doesn't have key" + show(p2.first) + "\n";
			ret += "matrix value:\n";
			ret += Indent::paragraph(p2.second.show());
		}
	}
	return ret;
}

#define CHECK_MATRIX_UNIFICATION
//#define SHOW_MATRIXES

inline uint expr_len_threshold() {
	return expr::Stats::stats().avgLen() + 2 * expr::Stats::stats().devLen();
	//return expr::Stats::stats().maxLen();
}

bool unify_down(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {

	ProofsSizeLimit limit(pr, hy, hs, pr->space->maxProofs());

	if (limit.empty()) {
		return false;
	}

	if (limit.cardChosen() > limit.cardLimit()) {
		cout << "Limit: " << limit.show(false) << endl << endl;
	}

	static int c = 0;
	c++;

	uint card = limit.cardChosen();

#ifdef SHOW_MATRIXES
	cout << "Matrix no. " << c << ", card: " << card << endl;
#endif

	Timer timer; timer.start();
#ifdef CHECK_MATRIX_UNIFICATION
	MultyUnifiedSubs unified_subs_1 = unify_subs_sequent(pr, hy, hs, &limit);
	timer.stop();
	stats[card].sequential.push_back(timer.getMicroseconds());
#ifdef SHOW_MATRIXES
	if (unified_subs_1.size() > 1) {
		cout << "sequntial unification: " << timer << endl;
		cout << "results with " << unified_subs_1.size() << " variants " << endl << endl;
	}
#endif
#endif
	timer.clear();
	timer.start();
	MultyUnifiedSubs unified_subs_2 = index::unify_subs_matrix(pr, hy, hs, &limit);
	timer.stop();
	stats[card].matrix.push_back(timer.getMicroseconds());
#ifdef SHOW_MATRIXES
	if (unified_subs_2.size() > 1) {
		cout << "matrix unification: " << timer << endl;
		cout << "results with " << unified_subs_2.size() << " variants " << endl;
	}
#endif

#ifdef CHECK_MATRIX_UNIFICATION
	if (!compare_unified_subs(unified_subs_2, unified_subs_1)) {
		cout << "SUB UNIFICATION DIFF" << endl;
		cout << "DIFF:" << endl;
		compare_unified_subs(unified_subs_2, unified_subs_1, true);
		cout << index::Matrix(pr, hy, hs, &limit).show() << endl;
		throw Error("SUB UNIFICATION DIFF");
	}
#endif

	for (const auto& p : unified_subs_2) {
		vector<uint> ind = p.first;
		vector<ProofHyp*> ch;
		bool hint = true;
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[ind[i]].get();
			if (!ph->hint) {
				hint = false;
			}
			ch.push_back(ph);
		}
		if (!hint && p.second.maxExprLen() > expr_len_threshold()) {
			// Expressions are too long - skip them
			continue;
		}
		try {
			ProofProp* pp = new ProofProp(*pr, ch, p.second, hint);
			if (pr->proofs.size() < 64) {
				// Don't check ALL proofs if there's too much (43050 for example)
				for (auto& h : pr->proofs) {
					if (pp->equal(h.get())) {
						cout << "DUPLICATE PROP PROOF" << endl;
						cout << pp->show() << endl;
						cout << "-----------" << endl;
						cout << h->show() << endl;
					}
				}
			}
			pr->proofs.emplace_back(pp);
		} catch (Error& err) {
			string msg;
			msg += "while unifying down:\n";
			for (auto c : ch) {
				msg += c->sub.show() + "\n";
			}
			err.msg += "\n" + msg;
			err.msg += "\nunifier: " + p.second.show();
			error_inds = ind;
			//unify_subs_sequent(pr, hy, hs);
			throw err;
		}
	}
	return unified_subs_2.size() > 0;
}

}}}

