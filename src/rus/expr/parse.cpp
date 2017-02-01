#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace expr { namespace {

vector<pair<Expr*, uint>> queue;

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

enum class Action { RET, BREAK, CONT };

inline Action act(auto& n, auto& m, Symbols::iterator ch, uint ind, Rule*& rule) {
	if (Rule* r = n.top()->rule) {
		if (r->ind <= ind) {
			rule = r;
			return Action::RET;
		} else
			return Action::BREAK;
	} else if (ch->end)
		return Action::BREAK;
	else {
		n.push(n.top()->tree.map.begin());
		m.push(++ch);
	}
	return Action::CONT;
}

Tree* parse_LL(Symbols::iterator& x, Type* type, uint ind) {
	if (type->rules.map.size()) {
		typedef Rules::Map::const_iterator MapIter;

		Tree::Children children;
		Rule* rule = nullptr;

		stack<MapIter> n;
		stack<Symbols::iterator> m;
		stack<MapIter> childnodes;
		n.push(type->rules.map.begin());
		m.push(x);
		while (!n.empty() && !m.empty()) {
			auto ch = m.top();
			if (Type* tp = n.top()->symb.type) {
				childnodes.push(n.top());
				if (Tree* child = parse_LL(ch, tp, ind)) {
					children.push_back(child);
					switch (act(n, m, ch, ind, rule)) {
					case Action::RET  : x = ch; return new Tree(rule, children);
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					childnodes.pop();
				}
			} else if (n.top()->symb == *m.top()) {
				switch (act(n, m, ch, ind, rule)) {
				case Action::RET  : x = ch; return new Tree(rule, children);
				case Action::BREAK: goto out;
				case Action::CONT : continue;
				}
			}
			while (n.top()->symb.fin) {
				n.pop();
				m.pop();
				if (!childnodes.empty() && childnodes.top() == n.top()) {
					delete children.back();
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
		} else if (Rule* super = find_super(x->type, type)) {
			return new Tree(super, {new Tree(*x)});
		}
	}
	return nullptr;
}


void parse_LL(Expr* ex, uint ind) {
	(--ex->symbols.end())->end = true;
	//cout << "parsing: " << ind << " -- " << show(*ex) << flush;
	auto it = ex->symbols.begin();
	if (Tree* tree = parse_LL(it, ex->type, ind)) {
		ex->tree = tree;
	} else {
		throw Error("parsing error", string("expression: ") + show(*ex));
	}
	//cout << "done" << endl;
}



const uint THREADS = thread::hardware_concurrency() ? thread::hardware_concurrency() : 1;
vector<std::exception_ptr> exceptions;
mutex exc_mutex;

void parse_LL_sequent() {
	for (auto p : queue) {
		parse_LL(p.first, p.second);
	}
}

void parse_LL_concurrent(uint s) {
	int c = 0;
	for (auto p : queue) {
		if (c++ % THREADS != s)
			continue;
		if (exceptions.size())
			break;
		try {
			parse_LL(p.first, p.second);
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
	for (auto& ex : exceptions) {
		if (ex) std::rethrow_exception(ex);
	}
	return true;
}

} // anonymous namespace

void enqueue(Expr& ex) {
	queue.push_back(pair<Expr*, uint>(&ex, parser::get_ind()));
}

bool parse() {
	if (parse_LL()) {
		queue.clear();
		return true;
	} else
		return false;
}

}}} // namespace mdl::rus::expr
