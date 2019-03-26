#include <rus_ast.hpp>

namespace mdl { namespace rus {

const Tokenable* Symbol::tokenable() const {
	switch (kind_) {
	case VAR: return type();
	case CONST: return constant();
	default: return nullptr;
	}
}

void Rules::add(const Expr& ex, uint id) {
	assert(ex.symbols.size());
	Rules* m = this;
	Node* n = nullptr;
	for (const Symbol& s : ex.symbols) {
		bool new_symb = true;
		for (auto& x : m->nodes) {
			Node* p = x.get();
			if ((s.kind() == Symbol::CONST && p->symb == s) ||
				(s.kind() == Symbol::VAR && p->symb.type_id() == s.type_id())) {
				n = p;
				m = &p->tree;
				new_symb = false;
				break;
			}
		}
		if (new_symb) {
			if (m->nodes.size()) m->nodes.back()->final = false;
			m->nodes.emplace_back(new Node(s, m));
			n = m->nodes.back().get();
			n->final = true;
			m = &n->tree;
		}
	}
	if (n->rule) {
		if (n->rule.id() != id) {
			string msg;
			msg += rus::show(ex) + " - term, ";
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
		    if (n1->symb.kind() == Symbol::CONST && n2->symb.kind() == Symbol::VAR) {
		    	return true;
		    } else if (n1->symb.kind() == Symbol::VAR && n2->symb.kind() == Symbol::CONST) {
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
		if (n->symb.kind() == Symbol::CONST) {
			constMap[n->symb.lit] = it;
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
		ret.push_back(rus::show(symb) + " -> " + Lex::toStr(rule.id()) + " from " + (src ? Lex::toStr(src->id()) : "NULL" ));
	}
	vector<string> strs = tree.show();
	for (const auto& s : strs)
		ret.push_back(rus::show(symb) + " " + s);
	return ret;
}

Tree::Node::Node(Id i) : rule(i), children() { }
Tree::Node::Node(Id i, const Tree::Children& ch) : rule(i), children() {
	children.reserve(ch.size());
	for (auto& c : ch) {
		children.push_back(make_unique<Tree>(*c.get()));
	}
}
Tree::Node::Node(const Node& n) : rule(n.rule), children() {
	children.reserve(n.children.size());
	for (auto& c : n.children) {
		children.push_back(make_unique<Tree>(*c.get()));
	}
}
Tree::Node::Node(Node&& n) : rule(n.rule), children(std::move(n.children)) { }
Tree::Node::Node(Id i, Tree::Children&& ch) : rule(i), children(std::move(ch)) { }
Tree::Node::Node(Id i, Tree* ch) : rule(i), children() {
	children.push_back(unique_ptr<Tree>(ch));
}
Tree::Node::~Node() {

}

static void assemble(const Tree* t, Symbols& s) {
	if (t->kind() == Tree::NODE) {
		auto i = t->children().begin();
		for (auto x : t->rule()->term) {
			switch (x.kind()) {
			case Symbol::VAR:   assemble((*i++).get(), s); break;
			case Symbol::CONST: s.push_back(x); break;
			default: s.push_back(x); break;
			}
		}
	} else if (t->kind() == Tree::VAR) {
		s.push_back(*t->var());
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

Tree* apply(const Substitution* s, const Tree* t) {
	if (t->kind() == Tree::NODE) {
		Tree::Children ch;
		ch.reserve(t->children().size());
		for (const auto& n : t->children()) {
			ch.emplace_back(apply(s, n.get()));
		}
		return new Tree(t->rule()->id(), ch);
	} else {
		const Symbol* v = t->var();
		if (s->sub().count(v->lit)) {
			return new Tree(s->sub().at(v->lit));
		} else {
			return new Tree(*v);
		}
	}
}

Expr apply(const Substitution* s, const Expr& e) {
	return assemble(apply(s, e.tree()));
}

string show_ast(const Tree* t, bool full) {
	if (t->kind() == Tree::VAR) {
		return t->var() ? show(*t->var(), full) : "<null>";
	} else {
		string s = (t->rule() ? show_id(t->rule()->id()) : "?") + " (";
		for (uint i = 0; i < t->children().size(); ++ i) {
			s += show_ast(t->children()[i].get(), full);
			if (i + 1 < t->children().size()) s += ", ";
		}
		s += ")";
		return s;
	}
}

string show(const Tree* t, bool full) {
	if (t->kind() == Tree::VAR) {
		return t->var() ? show(*t->var(), full) : "<null>";
	} else {
		string str(" ");
		uint i = 0;
		for (auto s : t->rule()->term.symbols) {
			if (s.type()) {
				str += show(t->children()[i++].get(), full) + ' ';
			} else {
				str += show(s) + ' ';
			}
		}
		return str;
	}
}

void dump(const Symbol& s) { cout << show(s) << endl; }
void dump(const Expr& ex) { cout << show(ex) << endl; }
void dump_ast(const Expr& ex) { cout << show_ast(ex) << endl; }
void dump(const Tree* tm) { cout << show(tm) << endl; }
void dump_ast(const Tree* tm) { cout << show_ast(tm) << endl; }
void dump(const Substitution& sb) { cout << show(sb) << endl; }


void Substitution::operator = (const Substitution& s) {
	ok_ = s.ok_;
	if (ok_) for (const auto& p : s.sub_) {
		sub_.emplace(p.first, p.second);
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
		if ((*it).second != t) ok_ = false;
	} else {
		sub_.emplace(v, t);
	}
	return ok_;
}

bool Substitution::join(uint v, Tree&& t) {
	if (!ok_) return false;
	auto it = sub_.find(v);
	if (it != sub_.end()) {
		if ((*it).second != t) ok_ = false;
	} else {
		sub_.emplace(v, std::move(t));
	}
	return ok_;
}

bool Substitution::join(const Substitution& s) {
	if (s.ok_) {
		for (const auto& p : s.sub_) {
			if (!ok_) return false;
			join(p.first, p.second);
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
