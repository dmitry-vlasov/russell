#include "rus/ast.hpp"

namespace mdl { namespace rus { namespace expr { namespace {

vector<Expr*> queue;

inline Rule* find_super(const Type* type, const Type* super) {
	return type->supers.count(super) ? type->supers.at(super) : nullptr;
}

struct Action {
	enum Kind { RET, BREAK, CONT };
	Kind  kind;
	Rule* rule;
	Action(Kind k, Rule* r = nullptr) : kind(k), rule(r) { }
};

inline Action act(auto& n, auto& m, Symbols::iterator ch, const Expr* e) {
	if (User<Rule>* r = (*n.top())->rule) {
		if (r->get()->token < e->token) return Action(Action::RET, r->get());
		else return Action::BREAK;
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
			if (const Type* tp = (*n.top())->symb.type.get()) {
				childnodes.push(n.top());
				if (Tree* child = parse_LL(ch, tp, e)) {
					children.push_back(unique_ptr<Tree>(child));
					Action a = act(n, m, ch, e);
					switch (a.kind) {
					case Action::RET  : x = ch; return new Tree(a.rule, children);
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					childnodes.pop();
				}
			} else if ((*n.top())->symb == *m.top()) {
				Action a = act(n, m, ch, e);
				switch (a.kind) {
				case Action::RET  : x = ch; return new Tree(a.rule, children);
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
	if (x->type) {
		if (x->type == type) {
			return new Tree(*x);
		} else if (Rule* super = find_super(x->type.get(), type)) {
			return new Tree(super, {new Tree(*x)});
		}
	}
	return nullptr;
}


void parse_LL(Expr* ex) {
	(--ex->symbols.end())->end = true;
	//cout << "parsing: " << ind << " -- " << show(*ex) << flush;
	auto it = ex->symbols.begin();
	if (Tree* tree = parse_LL(it, ex->type, ex)) {
		ex->tree.reset(tree);
	} else {
		for (Source* s : ex->token.src->includes) {
			cout << Lex::toStr(s->id()) << endl;
		}
		throw Error("parsing error", string("expression: ") + show(*ex) + " at: " + ex->token.show());
	}
	//cout << "done" << endl;
}



const uint THREADS = thread::hardware_concurrency() ? thread::hardware_concurrency() : 1;
vector<std::exception_ptr> exceptions;
mutex exc_mutex;

void parse_LL_sequent() {
	for (auto e : queue) {
		parse_LL(e);
	}
}

void parse_LL_concurrent(uint s) {
	int c = 0;
	for (auto e : queue) {
		if (c++ % THREADS != s)
			continue;
		if (exceptions.size())
			break;
		try {
			parse_LL(e);
		} catch (...) {
			exc_mutex.lock();
			exceptions.push_back(std::current_exception());
			exc_mutex.unlock();
		}
	}
}

bool parse_LL() {
	if (THREADS == 1) {
		parse_LL_sequent();
		return true;
	}
	thread* thds[THREADS];
	for (uint i = 0; i < THREADS; ++ i)
		thds[i] = new std::thread(parse_LL_concurrent, i);
	for (uint i = 0; i < THREADS; ++ i)
		thds[i]->join();
	for (uint i = 0; i < THREADS; ++ i)
		delete thds[i];
	for (auto& ex : exceptions) {
		if (ex) std::rethrow_exception(ex);
	}
	return true;
}

} // anonymous namespace

void enqueue(Expr& ex) {
	queue.push_back(&ex);
}

bool parse() {
	if (parse_LL()) {
		queue.clear();
		return true;
	} else
		return false;
}

}}} // namespace mdl::rus::expr
