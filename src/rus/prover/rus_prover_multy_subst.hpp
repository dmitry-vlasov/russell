#pragma once

#include "rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover {

struct MultySubst {
	MultySubst(const vector<const FlatSubst*>& subs);
	FlatSubst makeSubs(FlatSubst& unif) const;

	string show() const {
		ostringstream ret;
		ret << "MultySubst" << endl;
		ret << "==========" << endl;
		uint c = 0;
		for (const auto& p : msub_) {
			ret << c++ << " VAR: " << Lex::toStr(p.first) << endl;
			ret << "TREES:" << endl;
			for (const auto& tree : p.second) {
				ret << Indent::paragraph(tree.show()) << endl;
			}
		}
		return ret.str();
	}

private:
	void add(const FlatSubst* s);
	map<uint, vector<Term>> msub_;
};

extern bool debug_unify_subs_func;
extern bool debug_compose;

void sub_closure(FlatSubst& sub);
FlatSubst unify_subs(FlatSubst unif, FlatSubst gen);
FlatSubst unify_subs(const MultySubst& t);

// Substitutions, which differ only by varaible replacement
bool similar_subs(const FlatSubst& s1, const FlatSubst& s2);

typedef map<vector<uint>, FlatSubst> MultyUnifiedSubs;

}}}
