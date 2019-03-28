#include <rus_ast.hpp>

namespace mdl { namespace rus {

void Rules::add(const Expr& ex, uint id) {
	assert(ex.symbols.size());
	Rules* m = this;
	Node* n = nullptr;
	for (const auto& s : ex.symbols) {
		bool new_symb = true;
		for (auto& x : m->nodes) {
			Node* p = x.get();
			if ((s->kind() == Symbol::CONST && *p->symb == *s) ||
				(s->kind() == Symbol::VAR && p->symb->kind() == Symbol::VAR &&
				dynamic_cast<const Var*>(p->symb.get())->typeId() == dynamic_cast<const Var*>(s.get())->typeId())) {
				n = p;
				m = &p->tree;
				new_symb = false;
				break;
			}
		}
		if (new_symb) {
			if (m->nodes.size()) m->nodes.back()->final = false;
			m->nodes.emplace_back(new Node(*s, m));
			n = m->nodes.back().get();
			n->final = true;
			m = &n->tree;
		}
	}
	if (n->rule) {
		if (n->rule.id() != id) {
			string msg;
			msg += ex.show() + " - term, ";
			msg += Lex::toStr(id) + " - new id, ";
			msg += Lex::toStr(n->rule.id()) + " - old id";
			throw Error("rule already exists", msg);
		}
	} else {
		n->rule.use(id);
		uint min_dist = 0;
		while (n) {
			n->min_dist = min_dist < n->min_dist ? min_dist : n->min_dist;
			n = n->parent->parent;
			min_dist++;
		}
	}
}

void Rules::sort() {
	if (!nodes.size()) return;
	nodes.back().get()->final = false;
	std::sort(
		nodes.begin(),
		nodes.end(),
		[](const unique_ptr<Node>& p1, const unique_ptr<Node>& p2) {
			auto n1 = p1.get();
			auto n2 = p2.get();
		    if (n1->symb->kind() == Symbol::CONST && n2->symb->kind() == Symbol::VAR) {
		    	return true;
		    } else if (n1->symb->kind() == Symbol::VAR && n2->symb->kind() == Symbol::CONST) {
		    	return false;
		    } else {
		    	return n1->min_dist < n2->min_dist;
		    }
		}
	);
	nodes.back().get()->final = true;
	constLast = nodes.begin();
	for (auto it = nodes.begin(); it != nodes.end(); ++ it) {
		Node* n = it->get();
		if (n->symb->kind() == Symbol::CONST) {
			constMap[n->symb->lit()] = it;
			constLast = it;
		}
		n->tree.sort();
	}
}

vector<string> Rules::show() const {
	vector<string> ret;
	for (const auto& n : nodes)
		for (const auto& s : n->show())
			ret.push_back(s);
	return ret;
}

vector<string> Rules::Node::show() const {
	vector<string> ret;
	if (rule) {
		auto src = rule.get()->token.src();
		ret.push_back(symb->show() + " -> " + Lex::toStr(rule.id()) + " from " + (src ? Lex::toStr(src->id()) : "NULL" ));
	}
	vector<string> strs = tree.show();
	for (const auto& s : strs)
		ret.push_back(symb->show() + " " + s);
	return ret;
}

RuleTree::RuleTree(Id i) : rule(i), children() { }
RuleTree::RuleTree(Id i, const RuleTree::Children& ch) : rule(i), children() {
	children.reserve(ch.size());
	for (auto& c : ch) {
		children.emplace_back(c->clone());
	}
}
RuleTree::RuleTree(const RuleTree& n) : rule(n.rule), children() {
	children.reserve(n.children.size());
	for (auto& c : n.children) {
		children.emplace_back(c->clone());
	}
}
RuleTree::RuleTree(RuleTree&& n) : rule(n.rule), children(std::move(n.children)) { }
RuleTree::RuleTree(Id i, RuleTree::Children&& ch) : rule(i), children(std::move(ch)) { }
RuleTree::RuleTree(Id i, Tree* ch) : rule(i), children() {
	children.emplace_back(ch);
}

static void assemble(const Tree* tree, Symbols& s) {
	if (const RuleTree* rule_tree = dynamic_cast<const RuleTree*>(tree)) {
		auto i = rule_tree->children.begin();
		for (auto& x : rule_tree->rule->term) {
			switch (x->kind()) {
			case Symbol::VAR:   assemble((i++)->get(), s); break;
			case Symbol::CONST: s.push_back(make_unique<Const>(x->lit())); break;
			default: s.push_back(make_unique<Literal>(x->lit())); break;
			}
		}
	} else if (const VarTree* var_tree = dynamic_cast<const VarTree*>(tree)) {
		s.push_back(make_unique<Var>(var_tree->lit(), var_tree->type()));
	} else {
		throw Error("impossible");
	}
}

inline Expr assemble(Tree* t) {
	Symbols s;
	assemble(t, s);
	return Expr(Id(t->type()->id()), std::move(s), t);
}

void apply(const Substitution* sub, Expr& e) {
	apply(sub, e.tree());
	Symbols sym;
	assemble(e.tree(), sym);
	e.symbols = std::move(sym);
}

Tree* apply(const Substitution* s, const Tree* tree) {
	if (const RuleTree* rule_tree = dynamic_cast<const RuleTree*>(tree)) {
		RuleTree::Children ch;
		ch.reserve(rule_tree->children.size());
		for (const auto& n : rule_tree->children) {
			ch.emplace_back(apply(s, n.get()));
		}
		return new RuleTree(rule_tree->rule.id(), ch);
	} else if (const VarTree* var_tree = dynamic_cast<const VarTree*>(tree)) {
		if (s->maps(var_tree->lit())) {
			return s->map(var_tree->lit())->clone();
		} else {
			return var_tree->clone();
		}
	} else {
		throw Error("impossible");
	}
}

Expr apply(const Substitution* s, const Expr& e) {
	return assemble(apply(s, e.tree()));
}

string show_ast(const Tree* tree, bool full) {
	if (const RuleTree* rule_tree = dynamic_cast<const RuleTree*>(tree)) {
		string s = show_id(rule_tree->rule.id()) + " (";
		for (uint i = 0; i < rule_tree->children.size(); ++ i) {
			s += show_ast(rule_tree->children[i].get(), full);
			if (i + 1 < rule_tree->children.size()) s += ", ";
		}
		s += ")";
		return s;
	} else if (const VarTree* var_tree = dynamic_cast<const VarTree*>(tree)) {
		return var_tree->show();
	} else {
		throw Error("impossible");
	}
}

bool Tree::operator == (const Tree& tree) const {
	if (kind() != tree.kind()) {
		return false;
	}
	if (const RuleTree* rule_tree1 = dynamic_cast<const RuleTree*>(&tree)) {
		const RuleTree* rule_tree2 = dynamic_cast<const RuleTree*>(this);
		for (uint i = 0; i < rule_tree1->children.size(); ++ i) {
			if (*rule_tree1->children[i] != *rule_tree2->children[i]) {
				return false;
			}
		}
		return rule_tree1->rule == rule_tree2->rule;
	} else if (const VarTree* var_tree1 = dynamic_cast<const VarTree*>(&tree)) {
		const VarTree* var_tree2 = dynamic_cast<const VarTree*>(this);
		return var_tree1->lit() == var_tree2->lit();
	} else {
		throw Error("impossible");
	}
}

void VarTree::write(ostream& os, const Indent& indent) const {
	os << Lex::toStr(lit_);
}

void RuleTree::write(ostream& os, const Indent& indent) const {
	uint i = 0;
	for (auto& s : rule->term.symbols) {
		if (s->kind() == Symbol::VAR) {
			children[i++]->write(os);
			os << ' ';
		} else {
			os << *s << ' ';
		}
	}
}

void Substitution::operator = (const Substitution& s) {
	ok_ = s.ok_;
	if (ok_) for (const auto& p : s.sub_) {
		sub_.emplace(p.first, p.second->clone());
	}
}

void Substitution::operator = (Substitution&& s) {
	ok_ = s.ok_;
	sub_ = std::move(s.sub_);
	s.ok_ = true;
}

bool Substitution::join(uint v, const Tree& t) {
	if (!ok_) return false;
	auto it = sub_.find(v);
	if (it != sub_.end()) {
		if (*(*it).second != t) ok_ = false;
	} else {
		sub_.emplace(v, t.clone());
	}
	return ok_;
}

bool Substitution::join(uint v, unique_ptr<Tree>&& t) {
	if (!ok_) return false;
	auto it = sub_.find(v);
	if (it != sub_.end()) {
		if (*(*it).second != *t) ok_ = false;
	} else {
		sub_.emplace(v, std::move(t));
	}
	return ok_;
}

bool Substitution::join(const Substitution& s) {
	if (s.ok_) {
		for (const auto& p : s.sub_) {
			if (!ok_) return false;
			join(p.first, *p.second);
		}
	} else {
		ok_ = false;
	}
	return ok_;
}

bool Substitution::join(Substitution&& s) {
	if (s.ok_) {
		for (auto&& p : s.sub_) {
			if (!ok_) return false;
			join(p.first, std::move(p.second));
		}
	} else {
		ok_ = false;
	}
	return ok_;
}

}} // mdl::rus
