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
		m.push(ch.next());
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

SymbIter parse_LL_0(Term& t, SymbIter x, Type* type, uint ind, bool initial = false) {
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
				SymbIter ch = parse_LL_0(child, m.top(), tp, ind, n.top() == type->prules.root);
				if (ch != SymbIter()) {
					/*switch (act(n, m, ch, t, ind)) {
					case Action::RET  : return ch;
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}*/
					if (!n.top()->next) {
						if (n.top()->data->ind <= ind) {
							t.val.rule = n.top()->data;
							return ch;
						} else
							goto out;
					} else if (ch.is_last())
						goto out;
					else {
						n.push(n.top()->next);
						m.push(ch.next());
					}
					continue;
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top()->symb == *m.top().it) {
				/*switch (act(n, m, m.top(), t, ind)) {
				case Action::RET  : return m.top();
				case Action::BREAK: goto out;
				case Action::CONT : continue;
				}*/
				if (!n.top()->next) {
					if (n.top()->data->ind <= ind) {
						t.val.rule = n.top()->data;
						return m.top();
					} else
						goto out;
				} else if (m.top().is_last())
					goto out;
				else {
					n.push(n.top()->next);
					m.push(m.top().next());
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
	if (Rule* r = n.top().it->second.data) {
		if (r->ind <= ind) {
			t.val.rule = r;
			return Action::RET;
		} else
			return Action::BREAK;
	} else if (ch.is_last())
		return Action::BREAK;
	else {
		const TreeMap& tree_map = n.top().it->second.tree.map;
		MapIter next = MapIter(tree_map.m.begin(), -- tree_map.m.end());
		n.push(next);
		m.push(ch.next());
	}
	return Action::CONT;
}

SymbIter parse_LL_1(Term& t, SymbIter x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->trules.root.map.m.size()) {
		t.kind = term::Expr::NODE;
		stack<MapIter>  n;
		stack<SymbIter> m;
		stack<MapIter> childnodes;
		n.push(MapIter(type->trules.root.map.m.begin(), -- type->trules.root.map.m.end()));
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top().it->first.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				SymbIter ch = parse_LL_1(child, m.top(), tp, ind, n.top().it == type->trules.root.map.m.begin());
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


SymbIter parse_LL_2(Term& t, SymbIter x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->trules.root.map.m.size()) {
		t.kind = term::Expr::NODE;
		stack<MapIter>  n;
		stack<SymbIter> m;
		stack<MapIter> childnodes;
		n.push(MapIter(type->trules.root.map.m.begin(), -- type->trules.root.map.m.end()));
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top().it->first.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				SymbIter ch = parse_LL_2(child, m.top(), tp, ind, n.top().it == type->trules.root.map.m.begin());
				if (ch != SymbIter()) {
					if (Rule* r = n.top().it->second.data) {
						if (r->ind <= ind) {
							t.val.rule = r;
							return ch;
						} else
							goto out;
					} else if (ch.is_last())
						goto out;
					else {
						const TreeMap& tree_map = n.top().it->second.tree.map;
						MapIter next = MapIter(tree_map.m.begin(), -- tree_map.m.end());
						n.push(next);
						m.push(ch.next());
					}
					continue;
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top().it->first == *m.top().it) {
				if (Rule* r = n.top().it->second.data) {
					if (r->ind <= ind) {
						t.val.rule = r;
						return m.top();
					} else
						goto out;
				} else if (m.top().is_last())
					goto out;
				else {
					const TreeMap& tree_map = n.top().it->second.tree.map;
					MapIter next = MapIter(tree_map.m.begin(), -- tree_map.m.end());
					n.push(next);
					m.push(m.top().next());
				}
				continue;
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
















inline Action act_3(auto& n, auto& m, SymbIter ch, Term& t, uint ind) {
	if (Rule* r = n.top().it->second.rule) {
		if (r->ind <= ind) {
			t.val.rule = r;
			return Action::RET;
		} else
			return Action::BREAK;
	} else if (ch.is_last())
		return Action::BREAK;
	else {
		typedef BiIter<MRuleTree::TreeMap::Map_::const_iterator> MapIter;
		const MRuleTree::TreeMap& tree_map = n.top().it->second.tree.map;
		MapIter next = MapIter(tree_map.m.begin(), -- tree_map.m.end());
		n.push(next);
		m.push(ch.next());
	}
	return Action::CONT;
}

SymbIter parse_LL_3(Term& t, SymbIter x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->mrules.map.m.size()) {
		t.kind = term::Expr::NODE;
		typedef BiIter<MRuleTree::TreeMap::Map_::const_iterator> MapIter;

		stack<MapIter>  n;
		stack<SymbIter> m;
		stack<MapIter> childnodes;
		n.push(MapIter(type->mrules.map.m.begin(), -- type->mrules.map.m.end()));
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top().it->first.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				SymbIter ch = parse_LL_3(child, m.top(), tp, ind, n.top().it == type->mrules.map.m.begin());
				if (ch != SymbIter()) {
					switch (act_3(n, m, ch, t, ind)) {
					case Action::RET  : return ch;
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top().it->first == *m.top().it) {
				switch (act_3(n, m, m.top(), t, ind)) {
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












inline Action act_4(auto& n, auto& m, Symbols::iterator ch, Term& t, uint ind) {
	if (Rule* r = n.top()->second.rule) {
		if (r->ind <= ind) {
			t.val.rule = r;
			return Action::RET;
		} else
			return Action::BREAK;
	} else if (ch->end)
		return Action::BREAK;
	else {
		typedef MRuleTree::TreeMap::Map_::const_iterator MapIter;
		const MRuleTree::Node& nn = n.top()->second;
		const MRuleTree::TreeMap& tree_map = nn.tree.map;
		MapIter next = tree_map.m.begin();
		n.push(next);
		m.push(++ch);
	}
	return Action::CONT;
}

Symbols::iterator parse_LL_4(Term& t, Symbols::iterator x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->mrules.map.m.size()) {
		t.kind = term::Expr::NODE;
		typedef MRuleTree::TreeMap::Map_::const_iterator MapIter;

		stack<MapIter> n;
		stack<Symbols::iterator> m;
		stack<MapIter> childnodes;
		n.push(type->mrules.map.m.begin());
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top()->first.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				auto ch = parse_LL_4(child, m.top(), tp, ind, n.top() == type->mrules.map.m.begin());
				if (ch != Symbols::iterator()) {
					switch (act_4(n, m, ch, t, ind)) {
					case Action::RET  : return ch;
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top()->first == *m.top()) {
				switch (act_4(n, m, m.top(), t, ind)) {
				case Action::RET  : return m.top();
				case Action::BREAK: goto out;
				case Action::CONT : continue;
				}
			}
			while (n.top()->second.final) {
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













inline Action act_5(auto& n, auto& m, Symbols::iterator ch, Term& t, uint ind) {
	if (Rule* r = n.top()->second.rule) {
		if (r->ind <= ind) {
			t.val.rule = r;
			return Action::RET;
		} else
			return Action::BREAK;
	} else if (ch->end)
		return Action::BREAK;
	else {
		typedef RuleTree::Map::const_iterator MapIter;
		const RuleTree::Node& nn = n.top()->second;
		const RuleTree::Map& tree_map = nn.tree.map;
		MapIter next = tree_map.begin();
		n.push(next);
		m.push(++ch);
	}
	return Action::CONT;
}

Symbols::iterator parse_LL_5(Term& t, Symbols::iterator x, Type* type, uint ind, bool initial = false) {
	if (!initial && type->rules.map.size()) {
		t.kind = term::Expr::NODE;
		typedef RuleTree::Map::const_iterator MapIter;

		stack<MapIter> n;
		stack<Symbols::iterator> m;
		stack<MapIter> childnodes;
		n.push(type->rules.map.begin());
		m.push(x);
		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top()->first.type) {
				t.children.push_back(Term());
				childnodes.push(n.top());
				Term& child = t.children.back();
				auto ch = parse_LL_5(child, m.top(), tp, ind, n.top() == type->rules.map.begin());
				if (ch != Symbols::iterator()) {
					switch (act_5(n, m, ch, t, ind)) {
					case Action::RET  : return ch;
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					t.children.pop_back();
					childnodes.pop();
				}
			} else if (n.top()->first == *m.top()) {
				switch (act_5(n, m, m.top(), t, ind)) {
				case Action::RET  : return m.top();
				case Action::BREAK: goto out;
				case Action::CONT : continue;
				}
			}
			while (n.top()->second.final) {
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





void parse_LL_A(Expr* ex, uint ind) {
	auto last = --ex->symbols.end();
	last->end = true;
	SymbIter begin(ex->symbols.begin(), last);
	if (parse_LL_0(ex->term, begin, ex->type, ind) == SymbIter()) {
		throw Error("parsing error", string("expression: ") + show(*ex));
	}
}

void parse_LL_B(Expr* ex, uint ind) {
	(--ex->symbols.end())->end = true;
	cout << "parsing: " << ind << " -- " << show(*ex) << flush;
	if (parse_LL_5(ex->term, ex->symbols.begin(), ex->type, ind) == Symbols::iterator()) {
		throw Error("parsing error", string("expression: ") + show(*ex));
	}
	cout << "done" << endl;
}



const uint THREADS = 1; //thread::hardware_concurrency() ? thread::hardware_concurrency() : 1;
vector<std::exception_ptr> exceptions;
mutex exc_mutex;

void parse_LL_sequent() {
	for (auto p : queue) {
		parse_LL_B(p.first, p.second);
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
			parse_LL_B(p.first, p.second);
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
