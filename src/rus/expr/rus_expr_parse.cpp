#include <cmath>
#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace expr {

struct Action {
	enum Kind { RET, BREAK, CONT };
	Kind  kind;
	const Rule* rule;
	Action(Kind k, const Rule* r = nullptr) : kind(k), rule(r) { }
};

template<bool trace>
inline Action act(
	stack<Rules::NodeIter>& n,
	stack<Symbols::iterator>& m,
	Rules::NodeIter ni,
	Symbols::iterator ch,
	const Expr* e,
	Symbols::iterator beg,
	Symbols::iterator end
) {
	if (const User<Rule>& r = (*ni)->rule) {
		if (!r) throw Error("unknown rule", Lex::toStr(r.id()));
		if (r.get()->token.preceeds(e->token)) {
			//if (trace) cout << Indent(ch - beg) << "Act: Rule MATCHES: " << Lex::toStr(r.id()) << " = " << r.get()->term.show() <<  endl;
			return Action(Action::RET, r.get());
		} else {
			if (trace) {
				//cout << Indent(ch - beg) << "Act: Rule FAILS - follows: " << Lex::toStr(r.id()) << endl;
				cout <<  ((r.get()->token.preceeds(e->token)) ? "YEX" : "NO") << endl;
				cout << "rule.source.includes:" << endl;
				cout << (r.get()->token.src() ? r.get()->token.src()->showInclusionInfo() : " null src") << endl;

				cout << "expr.source.includes:" << endl;
				cout << (e->token.src() ? e->token.src()->showInclusionInfo() : "null src") << endl;

				cout << "r.get()->token: " << endl << r.get()->token.showRaw() << endl;
				cout << *r << endl;
				cout << "e->token: " << endl << e->token.showRaw() << endl;
				cout << *e << endl;
				exit(-1);
			}
			return Action::BREAK;
		}
	} else if (ch == end) {
		//if (trace) cout << Indent(ch - beg) << "Act: end of expression: " << endl;
		return Action::BREAK;
	} else {
		//if (trace) cout << Indent(ch - beg) << "Act: go forward one step ..." << endl;
		n.push((*ni)->tree.nodes.begin());
		m.push(++ch);
	}
	return Action::CONT;
}

template<bool trace>
Tree* parse_LL(Symbols::iterator& x, const Type* type, const Expr* e, Symbols::iterator beg, Symbols::iterator end) {
	if (type->rules.nodes.size()) {
		typedef Rules::NodeIter NodeIter;
		RuleTree::Children children;
		stack<NodeIter> n;
		stack<Symbols::iterator> m;
		stack<NodeIter> childnodes;
		n.push(type->rules.nodes.begin());
		m.push(x);
		while (!n.empty() && !m.empty()) {
			auto ch = m.top();
			//if (trace) cout << Indent(ch - beg) << "Expr symbol: " << (*ch)->showDetailed() << endl;
			//if (trace) cout << Indent(ch - beg) << "Rule tree symbol: " << (*n.top())->symb->showDetailed() << endl;
			if ((*ch)->kind() == Symbol::CONST && (*n.top())->symb->kind() == Symbol::CONST) {
				const Rules* par = (*n.top())->parent ? (*n.top())->parent : &type->rules;
				auto constIter = par->constMap.find((*ch)->lit());
				if (constIter != par->constMap.end()) {
					n.top() = constIter->second;
					//if (trace) cout << Indent(ch - beg) << "Parse: constant " << *(*n.top())->symb << " - success " << endl;
					n.top() = par->constLast;
					Action a = act<trace>(n, m, constIter->second, ch, e, beg, end);
					switch (a.kind) {
					case Action::RET  : x = ch; return new RuleTree(a.rule->id(), children);
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				}
			}
			if (const Type* tp = (*n.top())->symb->type()) {
				//if (trace) cout << Indent(ch - beg) << "Parse: variable " << *(*n.top())->symb << " of type: " << Lex::toStr(tp->id()) << endl;
				childnodes.push(n.top());
				if (Tree* child = parse_LL<trace>(ch, tp, e, beg, end)) {
					//if (trace) cout << Indent(ch - beg) << "Parse: subexpression " << child->show() << " - success " << endl;
					children.emplace_back(child);
					Action a = act<trace>(n, m, n.top(), ch, e, beg, end);
					switch (a.kind) {
					case Action::RET  : x = ch; return new RuleTree(a.rule->id(), children);
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				} else {
					childnodes.pop();
				}
			}
			while ((*n.top())->final) {
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
	if (const Var* v = dynamic_cast<const Var*>(x->get())) {
		if (v->type() == type) {
			return new VarTree(*v);
		} else if (Rule* super = find_super(v->type(), type)) {
			return new RuleTree(super->id(), new VarTree(*v));
		}
	}
	return nullptr;
}


cvector<std::exception_ptr> exceptions;

void parse(Expr* ex) {
	try {
		auto it = ex->symbols.begin();
		if (Tree* tree = parse_LL<false>(it, ex->type.get(), ex, ex->symbols.begin(), ex->symbols.end() - 1)) {
			ex->set(tree);
		} else {
 			cout << "parsing expr: " << *ex << endl << "detailed: " << ex->showDetailed() << endl;
 			cout << "source: " << Lex::toStr(ex->token.src()->id())  << endl << endl;
			parse_LL<true>(it, ex->type.get(), ex, ex->symbols.begin(), ex->symbols.end() - 1);
			exit(1);
			throw Error("parsing", string("expression: ") + ex->show() + " at: " + ex->token.show());
		}
	} catch (...) {
		exceptions.push_back(std::current_exception());
	}
}

#ifdef PARALLEL
#define PARALLEL_PARSE_EXPR
#endif

static cvector<Expr*> queue;

void parse() {
	Sys::mod().math.get<Rule>().rehash();
	for (const auto& p : Sys::get().math.get<Rule>()) {
		if (Rule* r = p.second.data) {
			Type* tp = r->term.type.get();
			tp->rules.add(r->term, r->id());
		}
	}
	Sys::mod().math.get<Type>().rehash();
	for (const auto& p : Sys::get().math.get<Type>()) {
		Type* tp = p.second.data;
		if (!tp) {
			throw Error("!tp: " + Lex::toStr(p.first) + " -- " + to_string(p.first));
		}
		tp->rules.sort();
	}
#ifdef PARALLEL_PARSE_EXPR
	tbb::parallel_for (tbb::blocked_range<size_t>(0, queue.size()),
		[] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				parse(queue[i]);
		}
	);
#else
	for (auto e : queue) parse(e);
#endif
	queue.clear();
	for (auto& ex : exceptions) {
		if (ex) std::rethrow_exception(ex);
	}
}

static cvector<uint> lengths;
static uint   max_len_ = 0;
static double avg_len_ = -1;
static double dev_len_ = -1;
static const Expr* max_len_expr_;

static void compute_expr_stats() {
	double sum_len = 0;
	for (uint len : lengths) {
		sum_len += len;
		max_len_ = std::max(len, max_len_);
	}
	avg_len_ = sum_len / lengths.size();
	double sum_dev = 0;
	for (uint len : lengths) {
		sum_dev += (len - avg_len_) * (len - avg_len_);
	}
	dev_len_ = sqrt(sum_dev / lengths.size());
}

uint max_len() {
	if (avg_len_ == -1) {
		compute_expr_stats();
	}
	return max_len_;
}

uint avg_len() {
	if (avg_len_ == -1) {
		compute_expr_stats();
	}
	return avg_len_;
}

uint dev_len() {
	if (dev_len_ == -1) {
		compute_expr_stats();
	}
	return dev_len_;
}

const Expr* max_len_expr() {
	return max_len_expr_;
}

void enqueue(Expr& ex) {
	avg_len_ = -1;
	dev_len_ = -1;
	if (!max_len_expr_ || max_len_expr_->symbols.size() < ex.symbols.size()) {
		max_len_expr_ = &ex;
	}
	lengths.push_back(ex.symbols.size());
	queue.push_back(&ex);
}

}}} // namespace mdl::rus::expr
