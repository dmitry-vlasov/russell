#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

Oracle::Oracle(const rus::Proof* p) :
	proof(p), root(p ? p->qed() : nullptr) {
}

bool debug_oracle = false;

void Oracle::add(Prop* p) {
	const Assertion* ass = p->prop.ass;
	if (debug_oracle) {
		cout << endl;
		cout << "orcale observing: " << show_id(ass->id()) << ", parent: " << p->parent->ind << endl;
	}
	auto proc_grand = [this, p, ass](Prop* grand_prop) {
		uint ind = 0;
		for (const auto& premise : grand_prop->premises) {
			if (p->parent == premise.get()) {
				break;
			}
			++ind;
		}
		if (props.count(grand_prop)) {
			const rus::Step* st = props.at(grand_prop);
			uint i = 0;
			for (const auto& r : st->refs) {
				if (r.get()->kind() == rus::Ref::STEP) {
					const rus::Step* candidate = r.get()->step();
					if (ass == candidate->ass() && !props.count(p) && /*!observed.count(candidate) &&*/ i == ind) {
						leafs.push_back(p);
						p->hint = true;
						if (debug_oracle) {
							cout << "orcale PUSHED: " << show_id(p->prop.id()) << ", index = " << p->ind << ", ref: " << i << endl;
							cout << "this: " << (void*)p << ", parent: " << (void*)grand_prop << endl << endl;
							//cout << p->show() << endl << endl;
						}
						props[p] = candidate;
						observed.insert(candidate);
					}
				}
				++i;
			}
		}
	};

	if (p->parent->root()) {
		if (ass == root->ass()) {
			leafs.push_back(p);
			p->hint = true;
			p->parent->hint = true;
			props[p] = root;
			observed.insert(root);
			if (debug_oracle) {
				cout << endl << "orcale PUSHED ROOT: " << show_id(p->prop.id()) << ", index = " << p->ind << endl;
				cout << "this: " << (void*)p << ", parent: " << (void*)root << endl << endl;
				//cout << p->show() << endl << endl;
			}
		}
	} else {
		for (Node* grand : p->parent->parents) {
			if (Prop* grand_prop = dynamic_cast<Prop*>(grand)) {
				proc_grand(grand_prop);
			} else if (Ref* grand_ref = dynamic_cast<Ref*>(grand)) {
				if (Prop* grand_prop = dynamic_cast<Prop*>(grand_ref->parent->parents[0])) {
					proc_grand(grand_prop);
				} else {
					throw Error("impossibe: grand of Ref MUST be Prop");
				}
			} else {
				throw Error("impossibe: no Proof nor Ref");
			}
		}
	}
}

void all_steps(const rus::Step* s, set<const rus::Step*>& all) {
	all.insert(s);
	for (const auto& r : s->refs) {
		if (r->kind() == rus::Ref::STEP) {
			all_steps(r->step(), all);
		}
	}
}

string Oracle::show() const {
	set<const rus::Step*> all;
	all_steps(root, all);
	string ret;
	for (auto p : props) {
		all.erase(p.second);
	}
	ret += "MISSED STEPS:\n";
	for (auto p : all) {
		ret += p->show() + "\n";
	}
	ret += "MISSED STEPS DONE\n\n";

	ret += "NODES:\n";
	for (auto p : props) {
		ret += "--------------------\n";
		ret += p.first->show(true);
		ret += p.first->parent->show(true);
		for (const auto& ch : p.first->premises) {
			ret += ch->show(true);
			if (ch->variants.size() == 1) {
				if (const Ref* r = dynamic_cast<const Ref*>(ch->variants[0].get())) {
					ret += r->show(true);
					ret += r->ancestor->show(true);
				}
			}
		}
		ret += "\n";
	}
	ret += "PROOFS DONE\n";
	return ret;
}

struct TacticsParser {
	static const char* tactics_syntax() {
		return R"(
			# Tactics grammar
		
            TACTIC  <- BREADTH / ALTER / PROXY / ORACLE
			BREADTH <- 'breadth'
			ALTER   <- 'alter(' (TACTIC (',' TACTIC)*)? ')'
            PROXY   <- 'proxy[' BITS '](' TACTIC ')'
            ORACLE  <- 'oracle'
            BITS    <- < (![ \]] .)+ >
		)";
	}
	TacticsParser() {
		parser.load_grammar(tactics_syntax());
		if (!parser) {
			cerr << "Tactics grammar is not correct" << endl;
			exit(1);
		}

		parser["BREADTH"] = [](const peg::SemanticValues& sv) {
			return new BreadthSearch;
		};
		parser["ALTER"] = [](const peg::SemanticValues& sv) {
			return new AlterTactic(std::move(sv.transform<Tactic*>()));
		};
		parser["PROXY"] = [](const peg::SemanticValues& sv) {
			return new ProxyTactic(sv[1].get<Tactic*>());
		};
		parser["ORACLE"] = [](const peg::SemanticValues& sv) {
			return new Oracle;
		};
		parser["TACTIC"] = [](const peg::SemanticValues& sv, peg::any& context) {
			switch (sv.choice()) {
			case 0: return static_cast<Tactic*>(sv[0].get<BreadthSearch*>());
			case 1: return static_cast<Tactic*>(sv[0].get<AlterTactic*>());
			case 2: return static_cast<Tactic*>(sv[0].get<ProxyTactic*>());
			case 3: return static_cast<Tactic*>(sv[0].get<Oracle*>());
			default: {
				throw  Error("unknown tactic", sv.token());
				return static_cast<Tactic*>(nullptr);
			}
			}
		};
		parser.log = [](size_t ln, size_t col, const std::string& err_msg) {
			std::stringstream ss;
			ss << "line: " << ln << ": " << err_msg << std::endl;
			throw Error(ss.str());
		};
	}
	Tactic* parse(string descr) {
		Tactic* t = nullptr;
		if (!parser.parse<Tactic*>(descr.c_str(), t))
			throw Error("tactic parsing failed", descr);
		return t;
	}
private:
	peg::parser parser;
};

Tactic* make_tactic(const string& descr) {
	static TacticsParser p;
	return p.parse(descr);
}

}}}

