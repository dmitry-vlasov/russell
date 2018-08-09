#include "rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover {

void Subst::operator = (const Subst& s) {
	ok = s.ok;
	if (ok) for (const auto& p : s.sub) {
		sub.emplace(p.first, p.second);
	}
}

void Subst::operator = (Subst&& s) {
	ok = s.ok;
	sub = std::move(s.sub);
	s.ok = true;
}

bool Subst::join(uint v, const LightTree& t) {
	if (!ok) return false;
	if (t.kind() == LightTree::VAR && t.var().lit == v) {
		return true;
	}
	auto it = sub.find(v);
	if (it != sub.end()) {
		if ((*it).second != t) ok = false;
	} else {
		sub.emplace(v, t);
	}
	return ok;
}

bool Subst::join(uint v, LightTree&& t) {
	if (!ok) return false;
	if (t.kind() == LightTree::VAR && t.var().lit == v) {
		return true;
	}
	auto it = sub.find(v);
	if (it != sub.end()) {
		if ((*it).second != t) ok = false;
	} else {
		sub.emplace(v, std::move(t));
	}
	return ok;
}

bool Subst::join(const Subst& s) {
	if (s.ok) {
		for (const auto& p : s.sub) {
			if (!ok) return false;
			join(p.first, p.second);
		}
	} else {
		ok = false;
	}
	return ok;
}

bool Subst::join(Subst&& s) {
	if (s.ok) {
		for (auto&& p : s.sub) {
			if (!ok) return false;
			join(p.first, std::move(p.second));
		}
	} else {
		ok = false;
	}
	return ok;
}

void collect_vars(const LightTree& tree, set<uint> vars) {
	if (tree.kind() == LightTree::VAR) {
		vars.insert(tree.var().lit);
	} else {
		for (const auto& c : tree.children()) {
			collect_vars(*c.get(), vars);
		}
	}
}

bool consistent_for_unify(const Subst* s, uint v, const LightTree& t) {
	set<uint> x_vars;
	collect_vars(t, x_vars);
	for (uint y : x_vars) {
		auto i = s->sub.find(y);
		if (i != s->sub.end()) {
			set<uint> y_vars;
			collect_vars(i->second, y_vars);
			if (y_vars.find(v) != y_vars.end()) {
				return false;
			}
		}
	}
	return true;
}


bool Subst::consistent(uint v, const LightTree& t) const {
	return consistent_for_unify(this, v, t);
}

bool Subst::consistent(const Subst& s) const {
	for (const auto& p : s.sub) {
		if (!consistent(p.first, p.second)) {
			return false;
		}
	}
	return true;
}

void Subst::compose(const Subst& s, bool full) {
	Subst ret;
	set<uint> vars;
	for (const auto& p : sub) {
		sub[p.first] = apply(s, p.second);
		vars.insert(p.first);
	}
	if (full) {
		for (const auto& p : s.sub) {
			if (vars.find(p.first) == vars.end()) {
				sub[p.first] = p.second;
			}
		}
	}
}

Subst compose(const Subst& s1, const Subst& s2, bool full) {
	Subst ret(s1);
	ret.compose(s2, full);
	return ret;
}

bool composable(const Subst& s1, const Subst& s2) {
	for (const auto& p : s1.sub) {
		if (s2.sub.find(p.first) != s2.sub.end()) {
			return true;
		}
	}
	return false;
}


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
		if (tree.empty()) {
			return "<EMPTY>";
		} else {
			return show(tree.var(), full);
		}
	} else if (tree.kind() == LightTree::NODE) {
		string str(" ");
		uint i = 0;
		for (auto s : tree.rule()->term.symbols) {
			if (s.type()) {
				str += show(*tree.children()[i++].get(), full) + ' ';
			} else {
				str += prover::show(s, full) + ' ';
			}
		}
		return str;
	} else {
		return "<UNDEF>";
	}
}

string show_ast(const LightTree& tree) {
	if (tree.kind() == LightTree::VAR) {
		return show(tree.var(), true);
	} else {
		string str("[[");
		uint i = 0;
		for (auto s : tree.rule()->term.symbols) {
			if (s.type()) {
				str += show_ast(*tree.children()[i++].get()) + ' ';
			} else {
				str += prover::show(s) + ' ';
			}
		}
		return str + "]]";
	}
}

string show(const Subst& s) {
	string str;
	for (const auto& p : s.sub) {
		str += Lex::toStr(p.first) + "* --> " + show_ast(p.second) + "\n";
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
		if (v.rep && s.sub.count(v.lit)) {
			return make_unique<LightTree>(s.sub.at(v.lit));
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
		if (v.rep && s.sub().count(v.lit)) {
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
	rus::Substitution ret(s.ok);
	for (const auto& p : s.sub) {
		ret.join(p.first, convert_tree(p.second));
	}
	return ret;
}

}}}
