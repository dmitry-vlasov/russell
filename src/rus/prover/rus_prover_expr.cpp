#include "rus_prover_expr.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

void Subst::operator = (const Subst& s) {
	ok_ = s.ok_;
	if (ok_) for (const auto& p : s.sub_) {
		sub_.emplace(p.first, p.second);
	}
}

void Subst::operator = (Subst&& s) {
	ok_ = s.ok_;
	sub_ = std::move(s.sub_);
	s.ok_ = true;
}

bool Subst::operator == (const Subst& s) const {
	if (ok_ != s.ok_) {
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
	if (s->maps(v)) {
		return t == s->map(v);
	} else {
		for (LightSymbol x : x_vars) {
			if (s->maps(x)) {
				set<LightSymbol> y_vars;
				const LightTree& p = s->map(x);
				collect_vars(p, y_vars);
				if (y_vars.find(v) != y_vars.end()) {
					if (p.kind() == LightTree::VAR && p.var() == v &&
						t.kind() == LightTree::VAR && t.var() == x) {
						return true;
					} else {
						return false;
					}
				}
			}
		}
		return true;
	}
}

bool Subst::consistent(const Subst& s) const {
	for (const auto& p : s.sub_) {
		if (!prover::consistent(this, p.first, p.second)) {
			return false;
		}
	}
	return true;
}

bool debug_compose = false;

void compose(Subst& s1, const Subst& s2, bool full) {
	//bool sh = s.sub.size() && sub.size();
	if (debug_compose) {
		cout << "-------------------------------------" << endl;
		cout << "BEFORE " << (full ? "FULL" : "PART") << " COMPOSE THIS:" << endl;
		cout << Indent::paragraph(show(s1)) << endl;
		cout << "BEFORE COMPOSE WITH:" << endl;
		cout << Indent::paragraph(show(s2)) << endl;
	}
	Subst ret;
	set<LightSymbol> vars;
	for (const auto& p : s1) {
		LightTree ex = apply(s2, p.second);
		if (!(ex.kind() == LightTree::VAR && ex.var() == p.first)) {
			s1.sub_[p.first] = std::move(ex);
			vars.insert(p.first);
		} else {
			s1.sub_.erase(p.first);
		}
	}
	if (full) {
		for (const auto& p : s2) {
			if (vars.find(p.first) == vars.end()) {
				s1.sub_[p.first] = p.second;
			}
		}
	}
	if (debug_compose) {
		cout << "AFTER COMPOSE THIS:" << endl;
		cout << Indent::paragraph(show(s1)) << endl;
		cout << "-------------------------------------" << endl;
	}
}

bool Subst::compose(const Subst& s, bool full) {
	if (!consistent(s)) {
		ok_ = false;
	} else {
		prover::compose(*this, s, full);
	}
	return ok_;
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
	for (const auto& p : s1) {
		if (s2.maps(p.first)) {
			return true;
		}
	}
	return false;
}

unique_ptr<rus::Tree> convert_tree_ptr(const LightTree& tree) {
	switch (tree.kind()) {
	case LightTree::RULE: {
		rus::RuleTree::Children ch;
		ch.reserve(tree.children().size());
		for (const auto& c : tree.children()) {
			ch.emplace_back(convert_tree_ptr(*c).release());
		}
		return make_unique<rus::RuleTree>(tree.rule()->id(), std::move(ch));
	}
	case LightTree::VAR:
		return make_unique<rus::VarTree>(rus::Var(tree.var().lit, tree.type()->id()));
	default:
		throw Error("impossible");
	}
}

unique_ptr<LightTree> convert_tree_ptr(const rus::Tree& tree, ReplMode mode, uint ind) {
	switch (tree.kind()) {
	case rus::Tree::RULE: {
		const rus::RuleTree& rule_tree = dynamic_cast<const rus::RuleTree&>(tree);
		LightTree::Children ch;
		ch.reserve(rule_tree.children.size());
		for (const auto& c : rule_tree.children) {
			ch.push_back(convert_tree_ptr(*c, mode, ind));
		}
		return make_unique<LightTree>(rule_tree.rule.get(), std::move(ch));
	}
	case rus::Tree::VAR: {
		const rus::VarTree& var_tree = dynamic_cast<const rus::VarTree&>(tree);
		return make_unique<LightTree>(LightSymbol(var_tree.var, mode, ind));
	}
	default:
		throw Error("impossible");
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
		for (auto& s : tree.rule()->term.symbols) {
			if (s->type()) {
				str += show(*tree.children()[i++].get(), full) + ' ';
			} else {
				str += s->show() + ' ';
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
		for (auto& s : tree.rule()->term.symbols) {
			if (s->type()) {
				str += show_ast(*tree.children()[i++].get()) + ' ';
			} else {
				str += s->show() + ' ';
			}
		}
		return str + "]]";
	}
}

string show(const Subst& sub) {
	string str;
	str += "OK = " + (sub.ok() ? string("TRUE") : string("FALSE")) + "\n";
	if (!sub.size()) {
		str += "empty\n";
	}
	for (const auto& p : sub) {
		str += show(p.first) + " --> " + show(p.second) + "\n";
	}
	return str;
}

string show_diff(const Subst& s1, const Subst& s2) {
	if (s1 == s2) return "<no diff>"; else {
		string ret;
		ret += "iterating s1\n";
		for (const auto& p : s1) {
			if (!s2.maps(p.first)) {
				ret += "\ts2 doesn't have " + show(p.first) + "\n";
			} else if (p.second != s2.map(p.first)) {
				ret += "\tvalues for '" + show(p.first) + "' differ:\n";
				ret += "\t\t" + show(p.second) + "\n";
				ret += "\t\t" + show(s2.map(p.first)) + "\n";
			}
		}
		ret += "iterating s2\n";
		for (const auto& p : s2) {
			if (!s1.maps(p.first)) {
				ret += "\ts2 doesn't have " + show(p.first) + "\n";
			} else if (p.second != s1.map(p.first)) {
				ret += "\tvalues for '" + show(p.first) + "' differ:\n";
				ret += "\t\t" + show(s1.map(p.first)) + "\n";
				ret += "\t\t" + show(p.second) + "\n";
			}
		}
		return ret;
	}
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
		if (v.rep && s.maps(v)) {
			return make_unique<LightTree>(s.map(v));
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
		if (v.rep && s.maps(v.lit)) {
			return convert_tree_ptr(*s.map(v.lit), ReplMode::KEEP_REPL, LightSymbol::MATH_INDEX);
		} else {
			return make_unique<LightTree>(v);
		}
	}
}

static void create_linear_expr(const LightTree& tree, vector<unique_ptr<Symbol>>& ret) {
	if (tree.kind() == LightTree::VAR) {
		ret.push_back(make_unique<rus::Var>(tree.var().lit, tree.type()->id()));
	} else {
		uint i = 0;
		for (const auto& s : tree.rule()->term.symbols) {
			if (s->type()) {
				create_linear_expr(*tree.children()[i++].get(), ret);
			} else {
				ret.emplace_back(s->clone());
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

rus::Substitution convert_sub(const Subst& sub) {
	rus::Substitution ret(sub.ok());
	for (const auto& p : sub) {
		ret.join(p.first.lit, *convert_tree_ptr(p.second));
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
		LightTree term = unify(p.second, unif);
		if (term.empty()) {
			return Subst(false);
		}
		LightTree un = unify(p.second, unif);
		if (debug_unify_subs_func && c == 6) {
			if (c == 6) {
				cout << "AAA" << endl;
			}
			cout << "RET: " << endl;
			cout << prover::show(ret) << endl;
			cout << "UNIF:" << endl;
			cout << prover::show(unif) << endl;
			cout << "p.first: " << prover::show(p.first) << endl;
			cout << "p.second:" << endl << "---------------" << endl;
			for (const auto& tree : p.second) {
				cout << prover::show(tree) << endl;
			}
			cout << "---------------" << endl;
			cout << "unify(p.second, unif):" << endl;
			cout << prover::show(un) << endl;
		}

		ret.compose(p.first, un);
		if (!ret.ok()) {
			if (debug_unify_subs_func) {
				cout << "SSSSSSSSSSSSSSSS" << endl;
				cout << "RET: " << endl;
				cout << prover::show(ret) << endl;
				cout << "UNIF:" << endl;
				cout << prover::show(unif) << endl;
			}
			break;
		}
	}
	return ret;
}

void MultySubst::add(const Subst* sub) {
	for (const auto& p : *sub) {
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
			break;
		}
	}
}

bool debug_unify_subs_func = false;

Subst unify_subs(const MultySubst& t) {
	if (debug_unify_subs_func) {
		cout << "unify_subs(const MultySubst& t): " << t.show() << endl;
	}
	Subst unif;
	Subst gen = t.makeSubs(unif);
	return unify_subs(unif, gen);
}

Subst unify_subs(Subst unif, Subst gen) {
	if (!(gen.ok() && unif.ok())) {
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
			if (debug_unify_subs_func) {
				cout << "gen.compose(unif)"  << endl;
			}
			sub_closure(gen);
			return gen;
		} else {
			if (debug_unify_subs_func) {
				cout << "!!!!!!!!!! gen.compose(unif)"  << endl;
			}
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
