#include <rus_ast.hpp>

namespace mdl {
namespace rus {

Rules::~Rules() {
	for (auto n : map) delete n;
}

void Rules::add(const Expr& ex, uint id) {
	assert(ex.symbols.size());
	Rules* m = this;
	Node* n = nullptr;
	for (const Symbol& s : ex.symbols) {
		bool new_symb = true;
		for (Node* p : m->map) {
			if (p->symb == s) {
				n = p;
				m = &p->tree;
				new_symb = false;
				break;
			}
		}
		if (new_symb) {
			if (m->map.size()) m->map.back()->symb.fin = false;
			m->map.push_back(new Node(s));
			n = m->map.back();
			n->symb.fin = true;
			m = &n->tree;
		}
	}
	if (n->rule) throw Error("rule already exists", show(ex));
	n->rule.use(id);
}

Tree::Node::Node(Id i) : rule(i), children() { }
Tree::Node::Node(Id i, const Tree::Children& ch) : rule(i), children() {
	children.reserve(ch.size());
	for (auto& c : ch) children.push_back(make_unique<Tree>(*c.get()));
}
Tree::Node::Node(const Node& n) : rule(n.rule), children() {
	children.reserve(n.children.size());
	for (auto& c : n.children) children.push_back(make_unique<Tree>(*c.get()));
}
Tree::Node::Node(Node&& n) : rule(n.rule), children(std::move(n.children)) { }
Tree::Node::Node(Id i, Tree::Children&& ch) : rule(i), children(std::move(ch)) { }
Tree::Node::Node(Id i, Tree* ch) : rule(i), children() {
	children.push_back(unique_ptr<Tree>(ch));
}
Tree::Node::~Node() {

}

static void assemble(const Tree& t, Symbols& s) {
	if (t.kind == Tree::NODE) {
		auto i = t.children().begin();
		for (auto x : t.rule()->term)
			if (x.cst) s.push_back(x);
			else assemble(*(*i++).get(), s);
	} else if (t.kind == Tree::VAR)
		s.push_back(*t.var());
}

inline Expr assemble(Tree& t) {
	Symbols s;
	assemble(t, s);
	return Expr(Id(t.type()->id()), std::move(s), std::move(t));
}

void apply(const Substitution* s, Tree& t) {
	if (t.kind == Tree::NODE)
		for (auto& n : t.children())
			apply(s, *n.get());
	else {
		Symbol v = *t.var();
		if (s->sub().count(v))
			t = s->sub().at(v);
	}
}

void apply(const Substitution* sub, Expr& e) {
	apply(sub, e.tree);
	Symbols sym;
	assemble(e.tree, sym);
	e.symbols = std::move(sym);
}

Tree apply_(const Substitution* s, const Tree& t) {
	if (t.kind == Tree::NODE) {
		Tree::Children ch;
		for (const auto& n : t.children())
			ch.emplace_back(new Tree(apply_(s, *n.get())));
		return Tree(t.rule()->id(), ch);
	} else {
		Symbol v = *t.var();
		if (s->sub().count(v))
			return s->sub().at(v);
		else
			return Tree(v);
	}
}

Expr apply(const Substitution* s, const Expr& e) {
	Tree t(e.tree);
	apply(s, t);
	return assemble(t);
}

Tree::Tree() : kind(NONE) { }
Tree::Tree(const Symbol& v) : kind(VAR), val(new Symbol(v)) { }
Tree::Tree(Id i, const Tree::Children& ch) : kind(NODE), val(new Node(i, ch)) { }
Tree::Tree(Id i, Tree* ch) : kind(NODE), val(new Node(i, ch)) { }
Tree::Tree(const Tree& ex) : kind(ex.kind) {
	switch (kind) {
	case NODE: val.node = new Node(*ex.val.node);  break;
	case VAR:  val.var  = new Symbol(*ex.val.var); break;
	}
}
Tree::Tree(Tree&& ex) : kind(ex.kind), val(ex.val) { ex.val.var = nullptr; ex.kind = NONE; }
Tree::~Tree() { delete_val(); }



string show(Symbol s, bool full) {
	if (!full || !s.type())
		return show_sy(s.lit);
	else {
		return string("<") + show_sy(s.lit) + ":" + show_id(s.type()->id()) + ">";
	}
}

string show(const Expr& ex) {
	string str;
	for (auto s : ex.symbols) str += show(s) + " ";
	return str;
}

size_t memvol(const Expr& ex) {
	size_t s = 0;
	s += ex.symbols.capacity() * sizeof (Symbols);
	s += memvol(ex.tree);
	return s;
}

string show_ast(const Tree& t, bool full) {
	if (t.kind == Tree::VAR)
		return t.var() ? show(*t.var(), full) : "<null>";
	else {
		string s = (t.rule() ? show_id(t.rule()->id()) : "?") + " (";
		for (uint i = 0; i < t.children().size(); ++ i) {
			s += show_ast(*t.children()[i], full);
			if (i + 1 < t.children().size()) s += ", ";
		}
		s += ")";
		return s;
	}
}

string show(const Tree& t, bool full) {
	if (t.kind == Tree::VAR)
		return t.var() ? show(*t.var(), full) : "<null>";
	else {
		string str(" ");
		uint i = 0;
		for (auto s : t.rule()->term.symbols) {
			if (s.type()) {
				str += show(*t.children()[i++], full) + ' ';
			} else {
				str += show(s) + ' ';
			}
		}
		return str;
	}
}

vector<string> show_lines(const Rules& tr) {
	vector<string> vect;
	for (const Rules::Node* p : tr.map) {
		vector<string> v = show_lines(p->tree);
		if (p->tree.map.size()) {
			for (string& s : v)
				vect.push_back(show(p->symb) + ' ' + s);
		} else {
			vect.push_back(show(p->symb) + " --> " +
				(p->rule ? show(*p->rule.get()) : "null")
			);
		}
	}
	return vect;
}

string show(const Rules& tr) {
	string str;
	for (string& s : show_lines(tr)) {
		str += s + "\n";
	}
	return str;
}

size_t memvol(const Rules& rt) {
	size_t vol = 0;
	vol += rt.map.capacity() * sizeof (Rules::Node);
	for (auto p : rt.map) {
		vol += memvol(p->tree);
	}
	return vol;
}


void dump(const Symbol& s) { cout << show(s) << endl; }
void dump(const Expr& ex) { cout << show(ex) << endl; }
void dump_ast(const Expr& ex) { cout << show_ast(ex) << endl; }
void dump(const Tree* tm) { cout << show(*tm) << endl; }
void dump_ast(const Tree& tm) { cout << show_ast(tm) << endl; }
void dump(const Substitution& sb) { cout << show(sb) << endl; }

}} // mdl::rus
