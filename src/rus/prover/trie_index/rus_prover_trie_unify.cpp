#include "rus_prover_trie_unify.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_flat_unify = false;

struct FlatUnifStepData {
	const Rule* rule = nullptr;
	vector<LightSymbol> vars;
	const Type* least_type = nullptr;
	vector<vector<FlatTerm::ConstIterator>> children;
	bool consistent = false;
	LightSymbol var;
	LightSymbol const_;

	bool track_var(LightSymbol v) {
		if (v.rep) {
			if (var.is_undef()) {
				var = v;
			}
			// Collect replaceable variables
			vars.push_back(v);
		} else {
			if (const_.is_undef()) {
				const_ = v;
			} else if (const_ != v) {
				// If we have any non-replaceable variables (constant), all other
				// constants must be the same variable (constant).
				return false;
			}
			if (rule) {
				// If we have any non-replaceable variables (constant),
				// complex terms are not allowed.
				return false;
			}
		}
		return true;
	}
	bool track_node(FlatTerm::ConstIterator i) {
		if (const_.is_def()) {
			// If we have any non-replaceable variables (constant), all other
			// terms must be the same variable (constant).
			return false;
		}
		if (!rule) {
			rule = i->ruleVar.rule;
		} else if (rule != i->ruleVar.rule) {
			// In case we have a non-leaf with some rule,
			// all other leafs must be with the same rule.
			return false;
		}
		vector<FlatTerm::ConstIterator> ch = trie_index::childrenIters(i);
		//cout << "GOT childern " << endl;
		/*for (auto i : ch) {
			cout << "\t'";
			auto j = i;
			while (true) {
				cout << j->ruleVar.show() << " " << flush;
				if (j == i->end) {
					break;
				}
				++j;
			}
			cout << "'" << endl;
		}*/
		//cout << "end of GOT" << endl << endl;

		children.push_back(trie_index::childrenIters(i));
		return true;
	}

	string show() const {
		cout << "rule: " << (rule ? Lex::toStr(rule->id()) : "NULL") << endl;
		cout << "vars: " << flush;
		for (const auto& v : vars) {
			cout << prover::show(v, true) << " " << flush;
		}
		cout << endl;
		cout << "consistent: " << (consistent ? "TRUE" : "FALSE") << endl;
		cout << "var: " << prover::show(var, true) << endl;
		cout << "children size: " << children.size() << endl;
		int cc = 0;
		for (const auto& ch : children) {
			cout << "\tchildern of " << (cc++) << endl;
			for (auto i : ch) {
				cout << "\t\t'";
				auto j = i;
				while (true) {
					cout << j->ruleVar.show() << " " << flush;
					if (j == i->end) {
						break;
					}
					++j;
				}
				cout << "'" << endl;
			}
			cout << "end of children" << endl << endl;
		}
		cout << endl;

		string ret;
		ret += "rule: " + (rule ? Lex::toStr(rule->id()) : "NULL") + "\n";
		ret += "vars: ";
		for (const auto& v : vars) {
			ret += prover::show(v, true) + " ";
		}
		ret += "\n";
		ret += string("consistent: ") + (consistent ? "TRUE" : "FALSE") + "\n";
		ret += string("var: ") + prover::show(var, true) + "\n";
		ret += "children size: " + to_string(children.size()) + "\n";
		int c = 0;
		for (const auto& ch : children) {
			ret += "\tchildern of " + to_string(c++) + "\n";
			for (auto i : ch) {
				ret += "\t\t'";
				auto j = i;
				while (true) {
					ret += j->ruleVar.show() + " ";
					if (j == i->end) {
						break;
					}
					++j;
				}
				ret += "'\n";
			}
			ret += "end of children\n\n";
		}
		ret += "\n";
		return ret;
	}
};

static FlatUnifStepData gather_unification_data(const vector<FlatTerm::ConstIterator>& is) {
	/*std::sort(
		es.begin(),
		es.end(),
		[](const FlatTerm& t1, const FlatTerm& t2) {
			return *t1.type() < *t2.type();
		}
	);*/

	/*static uint c = 0;
	++c;
	cout << "GATHERING: " << c << endl;
	cout << "is.size()  = " << is.size() << endl;
	//cout << "es.size()  = " << es.size() << endl;
	for (auto i : is) {
		cout << "\t'";
		auto j = i;
		while (true) {
			cout << j->ruleVar.show() << " ";
			if (j == i->end) {
				break;
			}
			++j;
		}
		cout << "'" << endl;
	}
	cout << "END GATH" << endl;*/


	FlatUnifStepData ret;
	ret.least_type = (*is.begin())->ruleVar.type();
	for (uint k = 0; k < is.size(); ++ k) {
		if (!is[k]->ruleVar.type()) {
			cout << "NULLL TYPE" << endl;
			exit(-7);
		}
		if (!(*ret.least_type <= *is[k]->ruleVar.type())) {
			// There's no unification because of type constraints
			return ret;
		}
		if (is[k]->ruleVar.isVar()) {
			if (!ret.track_var(is[k]->ruleVar.var)) {
				return ret;
			}
		} else {
			if (!ret.track_node(is[k])) {
				return ret;
			}
		}
	}
	//cout << "END END GATH" << endl;
	ret.consistent = true;
	return ret;
}

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
		if (s.maps(v)) {
			to_unify.push_back(s.sub.at(v));
		}
	}
	FlatTerm unified = unify(to_unify, s);
	if (!unified.empty()) {
		for (auto v : vars) {
			if (!s.compose(FlatSubst(v, unified))) {
				s.ok = false;
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
	FlatUnifStepData data = gather_unification_data(is);
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
