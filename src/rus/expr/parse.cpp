#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace expr { namespace {

typedef node::Expr Node;
typedef term::Expr Term;
typedef Tree<Rule*>::Node TreeNode;

vector<pair<Expr*, uint>> queue;

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

Node* parse_LL(Term& t, Node* x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->rules.root) {
		t.kind = term::Expr::NODE;
		stack<TreeNode*> n;
		stack<Node*> m;
		stack<TreeNode*> childnodes;
		n.push(type->rules.root);
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top()->symb.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				if (Node* ch = parse_LL(child, m.top(), tp, ind, n.top() == type->rules.root)) {
					if (!n.top()->next) {
						if (n.top()->data->ind <= ind) {
							t.val.rule = n.top()->data;
							return ch;
						} else
							goto end;
					} else if (!ch->next)
						goto end;
					else {
						n.push(n.top()->next);
						m.push(ch->next);
					}
					continue;
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top()->symb == m.top()->symb) {
				if (!n.top()->next) {
					if (n.top()->data->ind <= ind) {
						t.val.rule = n.top()->data;
						return m.top();
					} else
						goto end;
				} else if (!m.top()->next)
					goto end;
				else {
					n.push(n.top()->next);
					m.push(m.top()->next);
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
				if (n.empty() || m.empty()) goto end;
			}
			n.top() = n.top()->side;
		}
		end: ;
	}
	if (x->symb.type) {
		if (x->symb.type == type) {
			t = Term(x);
			return x;
		} else if (Rule* super = find_super(x->symb.type, type)) {
			t = Term(super);
			t.children.push_back(Term(x));
			return x;
		}
	}
	return nullptr;
}

void parse_LL(Expr* ex, uint ind) {
	if (!parse_LL(ex->term, ex->first, ex->type, ind)) {
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
