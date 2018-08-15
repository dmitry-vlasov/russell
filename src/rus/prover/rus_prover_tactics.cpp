#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

Oracle::Oracle(const rus::Proof* p) :
	proof(p), root(p ? (*p->qeds().begin())->step : nullptr) {

}

bool debug_oracle = false;

void Oracle::add(Prop* p) {
	const Assertion* ass = p->prop.ass;
	if (debug_oracle) {
		cout << "orcale observing: " << show_id(ass->id()) << ", parent: " << p->parent->ind << endl;
	}
	if (props.empty()) {
		if (ass == root->ass()) {
			leafs.push_back(p);
			props[p] = root;
			if (debug_oracle) {
				cout << "orcale ROOT: " << show_id(p->prop.id()) << ", index = " << p->ind <<  endl;
			}
		}
	} else {
		if (p->parent && p->parent->parent) {
			Prop* grand = dynamic_cast<Prop*>(p->parent->parent);
			if (props.count(grand)) {
				const rus::Step* st = props.at(grand);
				for (const auto& r : st->refs) {
					if (r.get()->kind() == rus::Ref::STEP && ass == r.get()->step()->ass()) {
						leafs.push_back(p);
						if (debug_oracle) {
							cout << "orcale PUSHED: " << show_id(p->prop.id()) << ", index = " << p->ind <<  endl;
						}
						props[p] = r.get()->step();
					}
				}
			}
		}
	}
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

