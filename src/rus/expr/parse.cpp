#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace expr { namespace {

typedef term::Expr Term;
typedef PTree<Rule*>::Node TreeNode;

typedef node::Tree<Rule*>::Map TreeMap;
typedef BiIter<TreeMap::Map_::const_iterator> MapIter;
typedef BiIter<Symbols::iterator>             SymbIter;


vector<pair<Expr*, uint>> queue;

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

enum class Action { RET, BREAK, CONT };

inline Action act (auto& n, auto& m, SymbIter ch, Term& t, uint ind) {
	if (!n.top()->next) {
		if (n.top()->data->ind <= ind) {
			t.val.rule = n.top()->data;
			return Action::RET;
		} else
			return Action::BREAK;
	} else if (ch.is_last())
		return Action::BREAK;
	else {
		n.push(n.top()->next);
		m.push(ch.inc());
	}
	return Action::CONT;
}

SymbIter parse_LL(Term& t, SymbIter x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->prules.root) {
		t.kind = term::Expr::NODE;
		stack<TreeNode*> n;
		stack<SymbIter> m;
		stack<TreeNode*> childnodes;
		n.push(type->prules.root);
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top()->symb.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				SymbIter ch = parse_LL(child, m.top(), tp, ind, n.top() == type->prules.root);
				if (ch != SymbIter()) {
					switch (act(n, m, ch, t, ind)) {
					case Action::RET  : return ch;
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top()->symb == *m.top().it) {
				switch (act(n, m, m.top(), t, ind)) {
				case Action::RET  : return m.top();
				case Action::BREAK: goto out;
				case Action::CONT : continue;
				}
			}
			while (!n.top()->side) {
				n.pop();
				m.pop();
				if (!childnodes.empty() && childnodes.top() == n.top()) {
					t.children.pop_back();
					childnodes.pop();
				}
				if (n.empty() || m.empty()) goto out;
			}
			n.top() = n.top()->side;
		}
		out: ;
	}
	if (x.it->type) {
		if (x.it->type == type) {
			t = Term(*x.it);
			return x;
		} else if (Rule* super = find_super(x.it->type, type)) {
			t = Term(super);
			t.children.push_back(Term(*x.it));
			return x;
		}
	}
	return SymbIter();
}





inline Action act_1 (auto& n, auto& m, SymbIter ch, Term& t, uint ind) {
	if (n.top().is_last()) {
		if (n.top().it->second.data->ind <= ind) {
			t.val.rule = n.top().it->second.data;
			return Action::RET;
		} else
			return Action::BREAK;
	} else if (ch.is_last())
		return Action::BREAK;
	else {
		TreeMap tree_map = n.top().it->second.tree.map;
		MapIter next = MapIter(tree_map.m.begin(), -- tree_map.m.end());
		n.push(next);
		m.push(ch.inc());
	}
	return Action::CONT;
}



SymbIter parse_LL_1(Term& t, SymbIter x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->prules.root) {
		t.kind = term::Expr::NODE;


		stack<MapIter> n;
		stack<SymbIter> m;
		stack<MapIter> childnodes;

		//n.push(MapIter(type->rules.root.begin(), type->rules.root.end() - 1));

		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top().it->first.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				SymbIter ch = parse_LL(child, m.top(), tp, ind, false /*n.top().it->second.data->type == type->rules.root*/);
				if (ch != SymbIter()) {
					switch (act_1(n, m, ch, t, ind)) {
					case Action::RET  : return ch;
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top().it->first == *m.top().it) {
				switch (act_1(n, m, m.top(), t, ind)) {
				case Action::RET  : return m.top();
				case Action::BREAK: goto out;
				case Action::CONT : continue;
				}
			}
			while (n.top().is_last()) {
				n.pop();
				m.pop();
				if (!childnodes.empty() && childnodes.top() == n.top()) {
					t.children.pop_back();
					childnodes.pop();
				}
				if (n.empty() || m.empty()) goto out;
			}
			n.top().inc();
		}
		out: ;
	}
	if (x.it->type) {
		if (x.it->type == type) {
			t = Term(*x.it);
			return x;
		} else if (Rule* super = find_super(x.it->type, type)) {
			t = Term(super);
			t.children.push_back(Term(*x.it));
			return x;
		}
	}
	return SymbIter();
}


void parse_LL(Expr* ex, uint ind) {
	SymbIter begin(ex->symbols.begin(), ex->symbols.end() - 1);
	if (parse_LL(ex->term, begin, ex->type, ind) == SymbIter()) {
		throw Error("parsing error", string("expression: ") + show(*ex));
	}
}


const uint THREADS = thread::hardware_concurrency() ? thread::hardware_concurrency() : 1;
vector<std::exception_ptr> exceptions;
mutex exc_mutex;


void parse_LL_concur(uint s) {
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

bool parse_LL_conc() {
	thread* thds[THREADS];
	for (uint i = 0; i < THREADS; ++ i)
		thds[i] = new std::thread(parse_LL_concur, i);
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
	if (parse_LL_conc()) {
		queue.clear();
		return true;
	} else
		return false;
}

}}} // namespace mdl::rus::expr
