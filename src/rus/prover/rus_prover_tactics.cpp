#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

Oracle::Oracle(const rus::Proof* p) :
	proof(p), root(p ? (*p->qeds().begin())->step : nullptr) {

}

bool debug_oracle = false;

void Oracle::add(Prop* p) {
	//p->autoGoDown = false;
	const Assertion* ass = p->prop.ass;
	if (debug_oracle) {
		//cout << endl;
		//cout << "orcale observing: " << show_id(ass->id()) << ", parent: " << p->parent->ind << endl;
	}
	if (props.empty()) {
		if (ass == root->ass()) {
			leafs.push_back(p);
			p->autoGoDown = true;
			props[p] = root;
			observed.insert(root);
			if (debug_oracle) {
				cout << endl << "orcale PUSHED: " << show_id(p->prop.id()) << ", index = " << p->ind << endl;
				cout << "this: " << (void*)p << ", parent: " << (void*)root << endl << endl;
				//cout << p->show() << endl << endl;
			}
		}
	} else {
		if (p->parent && !p->parent->root()) {
			Prop* grand = dynamic_cast<Prop*>(p->parent->parent);
			uint ind = 0;
			for (const auto& premise : grand->premises) {
				if (p->parent == premise.get()) {
					break;
				}
				++ind;
			}
			if (props.count(grand)) {
				const rus::Step* st = props.at(grand);
				uint i = 0;
				for (const auto& r : st->refs) {
					if (r.get()->kind() == rus::Ref::STEP) {
						const rus::Step* candidate = r.get()->step();
						if (ass == candidate->ass() && !props.count(p) && !observed.count(candidate) && i == ind) {
							leafs.push_back(p);
							p->autoGoDown = true;
							if (debug_oracle) {
								cout << "orcale PUSHED: " << show_id(p->prop.id()) << ", index = " << p->ind << ", ref: " << i << endl;
								cout << "this: " << (void*)p << ", parent: " << (void*)grand << endl << endl;
								//cout << p->show() << endl << endl;
							}
							props[p] = candidate;
							observed.insert(candidate);
						}
					}
					++i;
				}
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
	ret += "\n\n";

	for (auto p : props) {
		ret += p.first->parent->show(true);
		ret += p.first->show(true);
	}
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

