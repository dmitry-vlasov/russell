#include "rus_prover_trie_unify_step.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_flat_unify = false;

FlatTerm unify(const vector<FlatTerm>& ex, FlatSubst& sub);

FlatTerm unify_step(FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term) {

	if (debug_flat_unify) {
		cout << "vars: ";
		for (auto w : vars) {
			cout << "'" << prover::show(w) << "' ";
		}
		cout << endl;
		cout << "term: " << term.show() << endl;
		cout << "s: " << s.show() << endl;
	}

	vector<FlatTerm> to_unify({apply(s, term)});
	for (auto v : vars) {
		const FlatTerm& t = s.map(v);
		if (!t.empty()) {
			to_unify.push_back(t);
		} else {
			throw Error("empty term at unify_step");
		}
	}
	FlatTerm unified = unify(to_unify, s);
	if (!unified.empty()) {
		for (auto v : vars) {
			if (!s.bicompose(FlatSubst(v, unified))) {
				if (debug_flat_unify) {
					cout << "!s.compose(FlatSubst(v, unified))" << endl;
					cout << "v: " << prover::show(v) << endl;
					cout << "s: " << s.show() << endl;
				}
				return FlatTerm();
			}
		}
		if (debug_flat_unify) {
			cout << "s.compose(FlatSubst(v, unified)) == true" << endl;
			cout << "result s: " << s.show() << endl;
		}
		return unified;
	}
	if (debug_flat_unify) {
		cout << "unified.empty()" << endl;
	}
	return FlatTerm();
}

FlatTerm do_unify(const vector<FlatTerm::ConstIterator>& is, FlatSubst& sub);

FlatSubst unify_step(const FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term) {
	FlatSubst ret(s);
	FlatTerm unified = unify_step(ret, vars, term);
	return unified.empty() ? FlatSubst(false) : ret;
}

FlatTerm do_unify(const vector<FlatTerm::ConstIterator>& is, FlatSubst& sub) {
	if (!is.size()) {
		return FlatTerm();
	} else if (is.size() == 1) {
		return apply(sub, term(is[0]));
	}
	FlatUnifStepData data(is);
	if (!data.consistent) {
		if (debug_flat_unify) {
			cout << "!data.consistent" << endl;
		}
		return FlatTerm();
	}
	//if (debug_flat_unify) {
	//	cout << "DATA:" << endl << data.show() << endl;
	//}
	if (data.rule) {
		vector<FlatTerm> ch;
		for (uint i = 0; i < data.rule->arity(); ++ i) {
			vector<FlatTerm::ConstIterator> x;
			for (const auto& t : data.children) {
				x.push_back(t[i]);
			}
			FlatTerm c = do_unify(x, sub);
			if (!c.empty()) {
				ch.emplace_back(c);
			} else {
				if (debug_flat_unify) {
					cout << "c.empty()" << endl;
				}
				return FlatTerm();
			}
		}
		return unify_step(sub, data.vars, FlatTerm(data.rule, ch));
	} else {
		return unify_step(sub, data.vars, FlatTerm(data.const_.is_def() ? data.const_ : data.var));
	}
}

bool check_unification(const FlatTerm& term, const FlatSubst& sub, const vector<FlatTerm>& ex) {
	if (!term.empty()) {
		for (auto e : ex) {
			if (apply(sub, e) != term) {
				return false;
			}
		}
	}
	return true;
}

FlatTerm unify(const vector<FlatTerm>& ex, FlatSubst& sub) {
	vector<FlatTerm::ConstIterator> is;
	for (const auto& e : ex) {
		is.push_back(e.nodes.begin());
	}
	FlatTerm ret = do_unify(is, sub);
	if (!check_unification(ret, sub, ex)) {
		cout << "unification error: " << endl;
		for (auto pe : ex) {
			cout << "\t" << pe.show() << endl;
		}
		cout << "sub: " << endl;
		cout << sub.show() << endl;

		cout << "term: " << endl;
		cout << ret.show() << endl;
		exit(0);
	}
	return ret;
}

}}}}
