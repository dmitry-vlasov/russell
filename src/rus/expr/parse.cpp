#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace expr { namespace {

typedef term::Expr Term;
vector<pair<Expr*, uint>> queue;

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

enum class Action { RET, BREAK, CONT };

inline Action act(auto& n, auto& m, Symbols::iterator ch, Term& t, uint ind) {
	if (Rule* r = n.top()->rule) {
		if (r->ind <= ind) {
			t.val.rule = r;
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

Symbols::iterator parse_LL(Term& t, Symbols::iterator x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->rules.map.size()) {
		t.kind = term::Expr::NODE;
		typedef RuleTree::Map::const_iterator MapIter;

		stack<MapIter> n;
		stack<Symbols::iterator> m;
		stack<MapIter> childnodes;
		n.push(type->rules.map.begin());
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top()->symb.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				auto ch = parse_LL(child, m.top(), tp, ind, n.top() == type->rules.map.begin());
				if (ch != Symbols::iterator()) {
					switch (act(n, m, ch, t, ind)) {
					case Action::RET  : return ch;
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top()->symb == *m.top()) {
				switch (act(n, m, m.top(), t, ind)) {
				case Action::RET  : return m.top();
				case Action::BREAK: goto out;
				case Action::CONT : continue;
				}
			}
			while (n.top()->symb.fin) {
				n.pop();
				m.pop();
				if (!childnodes.empty() && childnodes.top() == n.top()) {
					t.children.pop_back();
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
			t = Term(*x);
			return x;
		} else if (Rule* super = find_super(x->type, type)) {
			t = Term(super);
			t.children.push_back(Term(*x));
			return x;
		}
	}
	return Symbols::iterator();
}


void parse_LL(Expr* ex, uint ind) {
	(--ex->symbols.end())->end = true;
	//cout << "parsing: " << ind << " -- " << show(*ex) << flush;
	if (parse_LL(ex->term, ex->symbols.begin(), ex->type, ind) == Symbols::iterator()) {
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
