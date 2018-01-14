#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace expr {

cvector<Expr*> queue;

struct Action {
	enum Kind { RET, BREAK, CONT };
	Kind  kind;
	Rule* rule;
	Action(Kind k, Rule* r = nullptr) : kind(k), rule(r) { }
};

inline Action act(auto& n, auto& m, Symbols::iterator ch, const Expr* e) {
	if (User<Rule>& r = (*n.top())->rule) {
		if (r.get()->token.preceeds(e->token))
			return Action(Action::RET, r.get());
		else
			return Action::BREAK;
	} else if (ch->end)
		return Action::BREAK;
	else {
		n.push((*n.top())->tree.map.begin());
		m.push(++ch);
	}
	return Action::CONT;
}

Tree* parse_LL(Symbols::iterator& x, const Type* type, const Expr* e) {
	if (type->rules.map.size()) {
		typedef Rules::Map::const_iterator MapIter;
		Tree::Children children;
		stack<MapIter> n;
		stack<Symbols::iterator> m;
		stack<MapIter> childnodes;
		n.push(type->rules.map.begin());
		m.push(x);
		while (!n.empty() && !m.empty()) {
			auto ch = m.top();
			if (const Type* tp = (*n.top())->symb.type()) {
				childnodes.push(n.top());
				if (Tree* child = parse_LL(ch, tp, e)) {
					children.push_back(unique_ptr<Tree>(child));
					Action a = act(n, m, ch, e);
					switch (a.kind) {
					case Action::RET  : x = ch; return new Tree(a.rule->id(), children);
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					childnodes.pop();
				}
			} else if ((*n.top())->symb == *m.top()) {
				Action a = act(n, m, ch, e);
				switch (a.kind) {
				case Action::RET  : x = ch; return new Tree(a.rule->id(), children);
				case Action::BREAK: goto out;
				case Action::CONT : continue;
				}
			}
			while ((*n.top())->symb.fin) {
				n.pop();
				m.pop();
				if (!childnodes.empty() && childnodes.top() == n.top()) {
					children.pop_back();
					childnodes.pop();
				}
				if (n.empty() || m.empty()) goto out;
			}
			++n.top();
		}
		out: ;
	}
	if (x->type()) {
		if (x->type() == type) {
			return new Tree(*x);
		} else if (Rule* super = find_super(x->type(), type)) {
			return new Tree(super->id(), {new Tree(*x)});
		}
	}
	return nullptr;
}

cvector<std::exception_ptr> exceptions;

void parse(Expr* ex) {
	try {
		(--ex->symbols.end())->end = true;
		auto it = ex->symbols.begin();
		if (Tree* tree = parse_LL(it, ex->type.get(), ex)) {
			ex->tree = std::move(*tree);
			delete tree;
		} else {
			/*if (const Source* src = ex->token.src()) {
				cout << src->showInclusionInfo() << endl;
			} else {
				cout << "Source: " << (void*)(ex->token.src()) << endl;
			}*/
			parse_LL(it, ex->type.get(), ex);
			throw Error("parsing", string("expression: ") + show(*ex) + " at: " + ex->token.show());
		}
	} catch (...) {
		exceptions.push_back(std::current_exception());
	}
}

void parse() {
	Sys::mod().math.get<Rule>().rehash();
	for (const auto& p : Sys::get().math.get<Rule>()) {
		Rule* r = p.second.data;
		Type* tp = r->term.type.get();
		tp->rules.add(r->term, r->id());
	}
	tbb::parallel_for (tbb::blocked_range<size_t>(0, queue.size()),
		[] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				parse(queue[i]);
		}
	);
	queue.clear();
	for (auto& ex : exceptions) {
		if (ex) std::rethrow_exception(ex);
	}
}

void enqueue(Expr& ex) {
	queue.push_back(&ex);
}

}}} // namespace mdl::rus::expr
