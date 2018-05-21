#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

/*
static rus::Step* root_step(rus::Proof* p) {
	for (auto e : p->elems) {
		if (e.kind == Proof::Elem::QED) {
			return e.val.qed->step;
		}
	}
	return nullptr;
}
*/
Oracle::Oracle(rus::Proof* p) : proof(p), root((*p->qeds().begin())->step) { }

void Oracle::add(Node* n) {
	if (Prop* p = dynamic_cast<Prop*>(n)) {
		const Assertion* ass = p->prop()->assertion();
		cout << endl << "orcale observing: " << show_id(ass->id()) << " ";
		if (props.empty()) {
			if (ass == root->ass()) {
				leafs.push_back(p);
				props[p] = root;
			}
		} else {
			if (p->parent && p->parent->parent) {
				Prop* grand = dynamic_cast<Prop*>(p->parent->parent);
				if (props.count(grand)) {
					rus::Step* st = props.at(grand);
					for (auto& r : st->refs) {
						if (r.get()->kind() == rus::Ref::STEP && ass == r.get()->step()->ass()) {
							leafs.push_back(p);
							props[p] = r.get()->step();
						}
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
			ALTER   <- 'alter(' (TACTIC {',' TACTIC})? ')'
            PROXY   <- 'proxy[' BITS '](' TACTIC ')'
            ORACLE  <- 'oracle'
            BITS    <- < (![ \]] .)+ >
		)";
	}
	TacticsParser() : parser(tactics_syntax()) {

		parser["BREADTH"] = [](const peg::SemanticValues& sv) {
			return new BreadthSearch;
		};
		parser["ALTER"] = [](const peg::SemanticValues& sv) {
			return new AlterTactic(std::move(sv.transform<Tactic*>()));
		};
		parser["PROXY"] = [](const peg::SemanticValues& sv) {
			return new ProxyTactic(sv[1].get<Tactic*>(), sv[0].get<string>());
		};
		parser["TACTIC"] = [](const peg::SemanticValues& sv, peg::any& context) {
			return sv[0].get<Tactic*>();
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

Tactic* make_tactic(string descr) {
	static TacticsParser p;
	return p.parse(descr);
}

}}}

