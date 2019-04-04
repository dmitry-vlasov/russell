#pragma once

#include "rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover {

struct MultySubst {
	MultySubst(const vector<const Subst*>& subs);
	Subst makeSubs(Subst& unif) const;

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
	void add(const Subst* s);
	map<uint, vector<Term>> msub_;
};

void sub_closure(Subst& sub);
Subst unify_subs(Subst unif, Subst gen);
Subst unify_subs(const MultySubst& t);

// Substitutions, which differ only by varaible replacement
bool similar_subs(const Subst& s1, const Subst& s2);

typedef map<vector<uint>, Subst> MultyUnifiedSubs;

}}}
