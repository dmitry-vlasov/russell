#include <cmath>
#include <numeric>
#include "../expr/rus_expr_stats.hpp"
#include "rus_prover_cartesian.hpp"
#include "rus_prover_tactics.hpp"
#include "rus_prover_multy_subst.hpp"
#include "rus_prover_limit.hpp"
#include "unify/rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

vector<uint> error_inds;
bool debug_unify_subs = false;

void unify_subs_sequent(Prop* pr, Hyp* hy, ProofExpIndexed hi, MultyUnifiedSubs& ret, const ProofsSizeLimit* limit) {
	CartesianProd<uint> ind;
	const ProofExp* h = hi.proof;
	if (limit) {
		for (uint i = 0; i < pr->premises.size(); ++ i) {
			auto& x = pr->premises[i];
			if (x.get() != hy) {
				ind.addDim(limit->descrVect()[i].chosen);
			} else {
				uint fixed_ind = -1;
				vector<uint> inds;
				for (uint k = 0; k < limit->descrVect()[i].chosen.size(); ++ k) {
					uint j = limit->descrVect()[i].chosen[k];
					uint cur_ind = limit->descrVect()[i].all[j];
					if (cur_ind == hi.ind) {
						fixed_ind = k;
					}
					inds.push_back(cur_ind);
				}
				if (fixed_ind == -1) {
					throw Error("fixed index: " + to_string(hi.ind) + " is not found");
				}
				ind.addFixedIndex(inds, fixed_ind);
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
			ProofExp* ph = pr->premises[i].get()->proofs[inds[i]].get();
			if (show_debug) {
				cout << ph->ind << ": " << ph->expr().show() << endl;
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
			if (delta.ok()) {
				ret[inds] = delta;
			}
		}
		if (!ind.hasNext()) {
			break;
		}
		ind.makeNext();
	}
}

uint unification_space_card(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& hs) {
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

string unification_space_card_str(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& hs) {
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

MultyUnifiedSubs unify_subs_sequent(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& hs, const ProofsSizeLimit* limit) {
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
		if (p.second.term.kind() == Term::VAR && !s2.maps(p.first)) {
			LightSymbol w(p.first, p.second.type);
			s1_vars_inv.compose(p.second.term.var(), Term(w));
		} else {
			s1_terms.compose(LightSymbol(p.first, p.second.type), p.second.term);
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
				cout << "A) on key: " << show(p1.first) << endl;
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
				cout << "B) on key: " << show(p2.first) << endl;
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

vector<vector<SubstInd>> make_matr(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& hs, const ProofsSizeLimit* limit) {
	vector<vector<SubstInd>> matr;
	for (uint i = 0; i < pr->premises.size(); ++ i) {
		matr.emplace_back();
		const auto& proofs = pr->premises[i]->proofs;
		if (pr->premises[i].get() != hy) {
			if (limit) {
				if (limit->descrVect()[i].fixed) {
					throw Error("should not be fixed");
				}
				matr.back().reserve(limit->descrVect()[i].chosen.size());
				for (uint k = 0; k < limit->descrVect()[i].chosen.size(); ++ k) {
					uint j = limit->descrVect()[i].chosen[k];
					matr.back().emplace_back(&proofs[j].get()->sub, j);
				}
			} else {
				matr.back().reserve(proofs.size());
				for (uint j = 0; j < proofs.size(); ++j) {
					matr.back().emplace_back(&proofs[j].get()->sub, j);
				}
			}
		} else {
			if (limit) {
				if (!limit->descrVect()[i].fixed) {
					throw Error("should be fixed");
				}
				matr.back().reserve(limit->descrVect()[i].chosen.size());
				for (uint k = 0; k < limit->descrVect()[i].chosen.size(); ++ k) {
					uint j = limit->descrVect()[i].chosen[k];
					matr.back().emplace_back(&hs[j].proof->sub, hs[j].ind);
				}
			} else {
				matr.back().reserve(hs.size());
				for (uint j = 0; j < hs.size(); ++j) {
					ProofExpIndexed hi = hs[j];
					matr.back().emplace_back(&hs[j].proof->sub, hs[j].ind);
				}
			}
		}
	}
	return matr;
}

#define CHECK_MATRIX_UNIFICATION
//#define SHOW_MATRIXES
//#define VERIFY_UNIQUE_PROOFS

inline uint expr_len_threshold() {
	return expr::Stats::stats().avgLen() + 2 * expr::Stats::stats().devLen();
	//return expr::Stats::stats().maxLen();
}

bool unify_down(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& hs) {

	ProofsSizeLimit limit(pr, hy, hs, pr->space->maxProofs());

	if (limit.empty()) {
		return false;
	}

	if (limit.cardChosen() > limit.cardLimit()) {
		cout << "Limit: " << limit.show(false) << endl << endl;
	}

	static atomic<int> counter = 0;
	counter++;
	uint count = counter;

	uint card = limit.cardChosen();

#ifdef SHOW_MATRIXES
	cout << endl;
	cout << "Matrix no. " << count << ", card: " << card << endl;
#endif

	Timer timer;
#ifdef CHECK_MATRIX_UNIFICATION

	MultyUnifiedSubs unified_subs_1 = unify_subs_sequent(pr, hy, hs, &limit);
	add_timer_stats("down_seq_time", timer);
	uint seq_time = timer.getMicroseconds();
	add_sequential_stats(card, count, timer);


#ifdef SHOW_MATRIXES
	if (unified_subs_1.size() >= 1) {
		cout << "sequntial unification: " << timer << " results with " << unified_subs_1.size() << " variants " << endl;
	}
#endif
#endif
	timer.start();
	MultyUnifiedSubs unified_subs_2 = unify::unify_subs_matrix(pr->sub, make_matr(pr, hy, hs, &limit), &limit);
	add_timer_stats("down_mat_time", timer);
	uint mat_time = timer.getMicroseconds();
	add_matrix_stats(card, count, timer);
#ifdef SHOW_MATRIXES
	if (unified_subs_2.size() >= 1) {
		cout << "matrix unification:    " << timer << " results with " << unified_subs_2.size() << " variants " << endl;
	}
#endif

#ifdef CHECK_MATRIX_UNIFICATION
	if (!compare_unified_subs(unified_subs_2, unified_subs_1)) {
		cout << "SUB UNIFICATION DIFF" << endl;
		cout << "DIFF:" << endl;
		compare_unified_subs(unified_subs_2, unified_subs_1, true);
		cout << unify::Matrix(make_matr(pr, hy, hs, &limit), &limit).show() << endl;
		throw Error("SUB UNIFICATION DIFF");
	}
#endif

	if (mat_time > 10 * 1000 * 1000) {
		cout << "LONG MATRIX TIME: " << timer << endl;
#ifdef CHECK_MATRIX_UNIFICATION
		cout << "SEQ TIME: " << double(seq_time) / 1000000 << "s." << endl;
#endif
		cout << "MATR TIME: " << double(mat_time) / 1000000 << "s." << endl;
		cout << "CARD: " << card << endl;
		//cout << "THEOREM: " << Lex::toStr(pr->space->theoremId()) << endl;
		//cout << index::Matrix(pr, hy, hs, &limit).show() << endl;
	}

	for (const auto& p : unified_subs_2) {
		vector<uint> ind = p.first;
		vector<ProofExp*> ch;
		bool hint = true;
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofExp* ph = pr->premises[i].get()->proofs[ind[i]].get();
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
#ifdef VERIFY_UNIQUE_PROOFS
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
#endif
			pr->proofs.emplace_back(pp);

			/*cout << "ind: " << show_vector(ind) << endl;
			for (uint i = 0; i < ind.size(); ++ i) {
				ProofExp* ph = pr->premises[i].get()->proofs[ind[i]].get();
				cout << "\t" << ph->expr() << endl;
			}
			cout << "Proof: [" << endl << show_proof_struct(pp) << "]" << endl;
			cout << "subst: " << p.second.show() << endl;*/

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

