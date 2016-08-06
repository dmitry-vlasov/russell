#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace expr { namespace {

typedef term::Expr Term;
typedef Tree<Rule*>::Node TreeNode;
typedef Symbols::iterator Iterator;

vector<pair<Expr*, uint>> queue;

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

Iterator parse_LL(Term& t, Iterator x, Iterator last, Type* type, uint ind, bool initial = false) {
	if (!initial && type->rules.root) {
		t.kind = term::Expr::NODE;
		stack<TreeNode*> n;
		stack<Iterator> m;
		stack<TreeNode*> childnodes;
		n.push(type->rules.root);
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top()->symb.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				Iterator ch = parse_LL(child, m.top(), last, tp, ind, n.top() == type->rules.root);
				if (ch != Iterator()) {
					if (!n.top()->next) {
						if (n.top()->data->ind <= ind) {
							t.val.rule = n.top()->data;
							return ch;
						} else
							goto out;
					} else if (ch == last)
						goto out;
					else {
						n.push(n.top()->next);
						m.push(ch + 1);
					}
					continue;
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top()->symb == *m.top()) {
				if (!n.top()->next) {
					if (n.top()->data->ind <= ind) {
						t.val.rule = n.top()->data;
						return m.top();
					} else
						goto out;
				} else if (m.top() == last)
					goto out;
				else {
					n.push(n.top()->next);
					m.push(m.top() + 1);
				}
				continue;
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
	return Iterator();
}

void parse_LL(Expr* ex, uint ind) {
	Iterator begin = ex->symbols.begin();
	Iterator last  = ex->symbols.end() - 1;
	if (parse_LL(ex->term, begin, last, ex->type, ind) == Iterator()) {
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
