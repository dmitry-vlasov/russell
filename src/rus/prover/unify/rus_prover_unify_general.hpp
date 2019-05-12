#pragma once

#include "../rus_prover_node.hpp"
#include "../unify/rus_prover_unify_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

map<vector<uint>, TermSubst> unify_general(const vector<const Index*>& inds, const vector<const Term*>& terms);

inline map<vector<uint>, TermSubst> unify_general(const vector<const Index*>& inds) {
	return unify_general(inds, vector<const Term*>());
}

inline map<vector<uint>, TermSubst> unify_general(const vector<const Term*>& terms) {
	return unify_general(vector<const Index*>(), terms);
}

template<class D>
vector<typename IndexMap<D>::Unified> unify_general(const IndexMap<D>& m, const Term& t) {
	vector<typename IndexMap<D>::Unified> ret;
	if (!m.index().size()) {
		return ret;
	}
	try {
		Timer timer;
		timer.start();
		map<vector<uint>, TermSubst> unif = unify_general(
			vector<const Index*>(1, &m.index()),
			vector<const Term*>(1, &t)
		);
		add_timer_stats("unify_general_iters", timer);

		for (auto& p : unif) {
			if (p.second.sub.ok()) {
				ret.emplace_back(m.data().at(p.first[0]), std::move(p.second.sub));
			}
		}
	} catch (Error& err) {
		cout << "unify_general: " << endl;
		//cout << m.index().show_pointers() << endl << endl;
		cout << m.index().show() << endl << endl;
		cout << t.show() << endl << endl;
		throw err;
	}
	return ret;
}

}}}}
