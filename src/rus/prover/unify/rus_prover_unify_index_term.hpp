#pragma once

#include "../rus_prover_node.hpp"
#include "../unify/rus_prover_unify_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

map<uint, TermSubst> unify_index_term(const Index& ind, const Term& term);

template<class D>
vector<typename IndexMap<D>::Unified> unify_index_term(const IndexMap<D>& m, const Term& t) {
	vector<typename IndexMap<D>::Unified> ret;
	if (!m.index().size()) {
		return ret;
	}
	try {
		Timer timer;
		timer.start();
		map<uint, TermSubst> unif = unify_index_term(m.index(), t);
		add_timer_stats("unify_index_term", timer);

		for (auto& p : unif) {
			if (p.second.sub.ok()) {
				ret.emplace_back(m.data().at(p.first), std::move(p.second.sub));
			}
		}
	} catch (Error& err) {
		cout << "unify_index_term: " << endl;
		//cout << m.index().show_pointers() << endl << endl;
		cout << m.index().show() << endl << endl;
		cout << t.show() << endl << endl;
		throw err;
	}
	return ret;
}

}}}}
