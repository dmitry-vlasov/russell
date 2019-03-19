#include "rus_prover_expr.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

void Subst::operator = (const Subst& s) {
	ok = s.ok;
	if (ok) for (const auto& p : s.sub_) {
		sub_.emplace(p.first, p.second);
	}
}

void Subst::operator = (Subst&& s) {
	ok = s.ok;
	sub_ = std::move(s.sub_);
	s.ok = true;
}

bool Subst::operator == (const Subst& s) const {
	if (ok != s.ok) {
		return false;
	}
	for (const auto& p : sub_) {
		if (!s.maps(p.first)) {
			return false;
		}
		if (p.second != s.sub_.at(p.first)) {
			return false;
		}
	}
	for (const auto& p : s.sub_) {
		if (!maps(p.first)) {
			return false;
		}
		if (p.second != sub_.at(p.first)) {
			return false;
		}
	}
	return true;
}

bool Subst::operator != (const Subst& s) const {
	return !operator ==(s);
}

void collect_vars(const LightTree& tree, set<LightSymbol>& vars) {
	if (tree.kind() == LightTree::VAR) {
		vars.insert(tree.var());
	} else {
		for (const auto& c : tree.children()) {
			collect_vars(*c, vars);
		}
	}
}

bool consistent(const Subst* s, LightSymbol v, const LightTree& t) {
	set<LightSymbol> x_vars;
	collect_vars(t, x_vars);
	if (x_vars.find(v) != x_vars.end()) {
		return false;
	}
	auto j = s->sub_.find(v);
	if (j != s->sub_.end()) {
		if (t != j->second) {
			return false;
		}
	}
	for (LightSymbol y : x_vars) {
		auto i = s->sub_.find(y);
		if (i != s->sub_.end()) {
			set<LightSymbol> y_vars;
			collect_vars(i->second, y_vars);
			if (y_vars.find(v) != y_vars.end()) {
				return false;
			}
		}
	}
	return true;
}

bool Subst::consistent(const Subst& s) const {
	for (const auto& p : s.sub_) {
		if (!prover::consistent(this, p.first, p.second)) {
			return false;
		}
	}
	return true;
}

void compose(Subst& s1, const Subst& s2, bool full) {
	/*bool sh = s.sub.size() && sub.size();
	if (sh) {
		cout << "-------------------------------------" << endl;
		cout << "BEFORE " << (full ? "FULL" : "PART") << " COMPOSE THIS:" << endl;
		cout << Indent::paragraph(show(*this)) << endl;
		cout << "BEFORE COMPOSE S:" << endl;
		cout << Indent::paragraph(show(s)) << endl;
	}*/
	Subst ret;
	set<LightSymbol> vars;
	for (const auto& p : s1.sub_) {
		LightTree ex = apply(s2, p.second);
		if (!(ex.kind() == LightTree::VAR && ex.var() == p.first)) {
			s1.sub_[p.first] = ex;
			vars.insert(p.first);
		}
	}
	if (full) {
		for (const auto& p : s2.sub_) {
			if (vars.find(p.first) == vars.end()) {
				s1.sub_[p.first] = p.second;
			}
		}
	}
	/*if (sh) {
		cout << "AFTER COMPOSE THIS:" << endl;
		cout << Indent::paragraph(show(*this)) << endl;
		cout << "-------------------------------------" << endl;
	}*/
}

bool Subst::compose(const Subst& s, bool full) {
	if (!consistent(s)) {
		return false;
	}
	prover::compose(*this, s, full);
	return true;
}

bool Subst::bicompose(const Subst& s) {
	if (!s.consistent(*this)) {
		return false;
	}
	Subst ss(s);
	prover::compose(ss, *this, false);
	if (!consistent(ss)) {
		return false;
	}
	prover::compose(*this, ss, true);
	return true;
}

bool Subst::intersects(const Subst& s) const {
	for (const auto& p : sub_) {
		if (s.sub_.count(p.first)) {
			return true;
		}
	}
	return false;
}

bool Subst::composeable(const Subst& s) const {
	set<LightSymbol> vars;
	for (const auto& p : sub_) {
		collect_vars(p.second, vars);
	}
	for (const auto& p : s.sub_) {
		if (vars.find(p.first) != vars.end()) {
			return true;
		}
	}
	return false;
}


Subst compose(const Subst& s1, const Subst& s2) {
	Subst ret(s1);
	ret.compose(s2);
	return ret;
}

bool composable(const Subst& s1, const Subst& s2) {
	for (const auto& p : s1.sub_) {
		if (s2.sub_.find(p.first) != s2.sub_.end()) {
			return true;
		}
	}
	return false;
}


unique_ptr<rus::Tree> convert_tree_ptr(const LightTree& tree) {
	switch (tree.kind()) {
	case LightTree::RULE: {
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

unique_ptr<LightTree> convert_tree_ptr(const rus::Tree& tree, ReplMode mode, uint ind) {
	switch (tree.kind()) {
	case rus::Tree::NODE: {
		LightTree::Children ch;
		ch.reserve(tree.children().size());
		for (const auto& c : tree.children()) {
			ch.push_back(convert_tree_ptr(*c.get(), mode, ind));
		}
		return make_unique<LightTree>(tree.rule(), std::move(ch));
	}
	case rus::Tree::VAR:
		return make_unique<LightTree>(LightSymbol(*tree.var(), mode, ind));
	default:
		assert(false && "impossible");
		return unique_ptr<LightTree>();
	}
}

string show(LightSymbol s, bool full) {
	string ret;
	if (s.is_undef()) {
		ret += "<UNDEF>";
	} else if (s.is_lambda()) {
		ret += "/\\";
	} else {
		ret += Lex::toStr(s.lit);
	}
	if (full && s.rep) {
		ret += "*";
	}
	return ret;
}

string show(const LightTree& tree, bool full) {
	if (tree.kind() == LightTree::VAR) {
		if (tree.empty()) {
			return "<EMPTY>";
		} else {
			return show(tree.var(), full);
		}
	} else if (tree.kind() == LightTree::RULE) {
		string str(" ");
		uint i = 0;
		for (auto s : tree.rule()->term.symbols) {
			if (s.type()) {
				str += show(*tree.children()[i++].get(), full) + ' ';
			} else {
				str += rus::show(s, full) + ' ';
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
				str += rus::show(s) + ' ';
			}
		}
		return str + "]]";
	}
}

string show(const Subst& s) {
	string str;
	str += "OK = " + (s.ok ? string("TRUE") : string("FALSE")) + "\n";
	if (!s.sub_.size()) {
		str += "empty\n";
	}
	for (const auto& p : s.sub_) {
		str += show(p.first) + " --> " + show(p.second) + "\n";
	}
	return str;
}


unique_ptr<LightTree> apply_ptr(const Subst& s, const LightTree& t) {
	if (t.kind() == LightTree::RULE) {
		LightTree::Children ch;
		ch.reserve(t.children().size());
		for (const auto& n : t.children()) {
			ch.push_back(apply_ptr(s, *n.get()));
		}
		return make_unique<LightTree>(t.rule(), ch);
	} else {
		LightSymbol v = t.var();
		if (v.rep && s.sub_.count(v)) {
			return make_unique<LightTree>(s.sub_.at(v));
		} else {
			return make_unique<LightTree>(v);
		}
	}
}

unique_ptr<LightTree> apply_ptr(const Substitution& s, const LightTree& t) {
	if (t.kind() == LightTree::RULE) {
		LightTree::Children ch;
		ch.reserve(t.children().size());
		for (const auto& n : t.children()) {
			ch.push_back(apply_ptr(s, *n.get()));
		}
		return make_unique<LightTree>(t.rule(), ch);
	} else {
		LightSymbol v = t.var();
		if (v.rep && s.sub().count(v.lit)) {
			return convert_tree_ptr(s.sub().at(v.lit), ReplMode::KEEP_REPL, LightSymbol::MATH_INDEX);
		} else {
			return make_unique<LightTree>(v);
		}
	}
}

static void create_linear_expr(const LightTree& tree, vector<Symbol>& ret) {
	if (tree.kind() == LightTree::VAR) {
		ret.emplace_back(rus::Symbol(tree.var().lit, tree.type()->id(), rus::Symbol::VAR));
	} else {
		uint i = 0;
		for (const auto& s : tree.rule()->term.symbols) {
			if (s.type()) {
				create_linear_expr(*tree.children()[i++].get(), ret);
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
	create_linear_expr(tree, ret.symbols);
	return ret;
}

rus::Substitution convert_sub(const Subst& s) {
	rus::Substitution ret(s.ok);
	for (const auto& p : s.sub_) {
		ret.join(p.first.lit, convert_tree(p.second));
	}
	return ret;
}


MultySubst::MultySubst(const vector<const Subst*>& subs) {
	for (auto s : subs) {
		add(s);
	}
}
Subst MultySubst::makeSubs(Subst& unif) const {
	Subst ret;
	uint c = 0;
	if (debug_unify_subs_func) {
		cout << "--- MultySubst::makeSubs ---" << endl;
	}
	for (const auto& p : msub_) {
		if (debug_unify_subs_func) {
			cout << "TO UNIFY: " << c++ << endl;
			for (auto e : p.second) {
				cout << prover::show(e) << endl;
			}
		}
		if (c == 2) {
			cout << "AAA" << endl;
		}
		LightTree t = unify(p.second, unif);
		if (t.kind() != LightTree::VAR || t.var() != p.first) {
			ret.sub_[p.first] = t;
		}
		if (debug_unify_subs_func) {
			cout << "RESULT: " << endl;
			cout << prover::show(ret.sub_[p.first]) << endl;
			cout << "UNIF:" << endl;
			cout << prover::show(unif) << endl;
		}
		if (ret.sub_[p.first].empty()) {
			ret.ok = false;
			break;
		}
	}
	return ret;
}

void MultySubst::add(const Subst* s) {
	for (const auto& p : s->sub_) {
		msub_[p.first].push_back(p.second);
	}
}

void sub_closure(Subst& sub) {
	enum { WATCHDOG_THRESHOLD = 32 };
	uint watchdog = 0;
	while (sub.composeable(sub)) {
		if (watchdog++ > WATCHDOG_THRESHOLD) {
			cout << "SOMETHING WRONG: too much deep substitution closure" << endl;
			break;
		}
		if (!sub.compose(sub)) {
			sub.ok = false;
			break;
		}
	}
}

bool debug_unify_subs_func = false;

Subst unify_subs(const MultySubst& t) {
	Subst unif;
	Subst gen = t.makeSubs(unif);
	return unify_subs(unif, gen);
}

Subst unify_subs(Subst unif, Subst gen) {
	if (!(gen.ok && unif.ok)) {
		return Subst(false);
	}
	if (debug_unify_subs_func) {
		cout << "--- unify_subs ---" << endl;
		cout << "UNIF:" << endl;
		cout << show(unif) << endl;
		cout << "GEN:" << endl;
		cout << show(gen) << endl;
	}
	if (!gen.intersects(unif)) {
		if (debug_unify_subs_func) {
			cout << "intersects == false" << endl;
		}
		if (gen.compose(unif)) {
			sub_closure(gen);
			return gen;
		} else {
			return Subst(false);
		}
	} else {
		MultySubst msub({&unif, &gen});
		Subst ret = unify_subs(msub);
		if (debug_unify_subs_func) {
			cout << "ret:" << endl;
			cout << show(ret) << endl;
		}
		return ret;
	}
}

}}}
