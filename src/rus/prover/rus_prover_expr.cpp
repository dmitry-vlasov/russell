#include "rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover {

unique_ptr<rus::Tree> convert_tree(const LightTree& tree) {
	switch (tree.kind()) {
	case LightTree::NODE: {
		rus::Tree::Children ch;
		for (const auto& c : tree.children()) {
			ch.push_back(convert_tree(*c.get()));
		}
		return make_unique<rus::Tree>(tree.rule()->id(), std::move(ch));
	}
	case LightTree::VAR:
		return make_unique<rus::Tree>(rus::Symbol(tree.var().lit, tree.type()->id(), rus::Symbol::VAR));
	default:
		assert(false && "impossible");
		return unique_ptr<rus::Tree>();
	}
}

unique_ptr<LightTree> convert_tree(const rus::Tree& tree) {
	switch (tree.kind()) {
	case rus::Tree::NODE: {
		LightTree::Children ch;
		for (const auto& c : tree.children()) {
			ch.push_back(convert_tree(*c.get()));
		}
		return make_unique<LightTree>(tree.rule(), std::move(ch));
	}
	case rus::Tree::VAR:
		return make_unique<LightTree>(LightSymbol(*tree.var()));
	default:
		assert(false && "impossible");
		return unique_ptr<LightTree>();
	}
}

string show(LightSymbol s, bool full) {
	if (full) {
		return Lex::toStr(s.lit) + (s.rep ? "*" : "");
	} else {
		return Lex::toStr(s.lit);
	}
}

string show(const LightTree& tree, bool full) {
	if (tree.kind() == LightTree::VAR) {
		return show(tree.var(), full);
	} else {
		string str(" ");
		uint i = 0;
		for (auto s : tree.rule()->term.symbols) {
			if (s.type()) {
				str += show(*tree.children()[i++].get(), full) + ' ';
			} else {
				str += show(s) + ' ';
			}
		}
		return str;
	}
}

}}}
