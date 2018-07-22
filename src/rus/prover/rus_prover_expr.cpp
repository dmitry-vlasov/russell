#include "rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover {

unique_ptr<rus::Tree> convert_tree_ptr(const LightTree& tree) {
	switch (tree.kind()) {
	case LightTree::NODE: {
		rus::Tree::Children ch;
		ch.reserve(tree.children().size());
		for (const auto& c : tree.children()) {
			ch.push_back(convert_tree_ptr(*c.get()));
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

unique_ptr<LightTree> convert_tree_ptr(const rus::Tree& tree, ReplMode mode) {
	switch (tree.kind()) {
	case rus::Tree::NODE: {
		LightTree::Children ch;
		ch.reserve(tree.children().size());
		for (const auto& c : tree.children()) {
			ch.push_back(convert_tree_ptr(*c.get(), mode));
		}
		return make_unique<LightTree>(tree.rule(), std::move(ch));
	}
	case rus::Tree::VAR:
		return make_unique<LightTree>(LightSymbol(*tree.var(), mode));
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

string show(const Subst& s) {
	string str;
	for (const auto& p : s.sub()) {
		str += Lex::toStr(p.first) + "* --> " + show(p.second) + "\n";
	}
	return str;
}


unique_ptr<LightTree> apply_ptr(const Subst& s, const LightTree& t) {
	if (t.kind() == LightTree::NODE) {
		LightTree::Children ch;
		ch.reserve(t.children().size());
		for (const auto& n : t.children()) {
			ch.push_back(apply_ptr(s, *n.get()));
		}
		return make_unique<LightTree>(t.rule(), ch);
	} else {
		LightSymbol v = t.var();
		if (s.sub().count(v.lit)) {
			return make_unique<LightTree>(s.sub().at(v.lit));
		} else {
			return make_unique<LightTree>(v);
		}
	}
}

unique_ptr<LightTree> apply_ptr(const Substitution& s, const LightTree& t) {
	if (t.kind() == LightTree::NODE) {
		LightTree::Children ch;
		ch.reserve(t.children().size());
		for (const auto& n : t.children()) {
			ch.push_back(apply_ptr(s, *n.get()));
		}
		return make_unique<LightTree>(t.rule(), ch);
	} else {
		LightSymbol v = t.var();
		if (s.sub().count(v.lit)) {
			return convert_tree_ptr(s.sub().at(v.lit));
		} else {
			return make_unique<LightTree>(v);
		}
	}
}

static void create_liear_expr(const LightTree& tree, vector<Symbol>& ret) {
	if (tree.kind() == LightTree::VAR) {
		ret.emplace_back(rus::Symbol(tree.var().lit, tree.type()->id(), rus::Symbol::VAR));
	} else {
		uint i = 0;
		for (const auto& s : tree.rule()->term.symbols) {
			if (s.type()) {
				create_liear_expr(*tree.children()[i++].get(), ret);
			} else {
				ret.push_back(s);
			}
		}
	}
}

rus::Expr convert_expr(const LightTree& tree) {
	rus::Expr ret;
	ret.set(convert_tree_ptr(tree).release());
	ret.type = tree.type();
	ret.symbols.reserve(tree.length());
	create_liear_expr(tree, ret.symbols);
	return ret;
}

rus::Substitution convert_sub(const Subst& s) {
	rus::Substitution ret(s.ok());
	for (const auto& p : s.sub()) {
		ret.join(p.first, convert_tree(p.second));
	}
	return ret;
}

}}}
