#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace expr {

cvector<Expr*> queue;

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
			if (trace) cout << Indent(ch - beg) << "Act: Rule MATCHES: " << Lex::toStr(r.id()) << " = " << show(r.get()->term) <<  endl;
			return Action(Action::RET, r.get());
		} else {
			if (trace) cout << Indent(ch - beg) << "Act: Rule FAILS - follows: " << Lex::toStr(r.id()) << endl;
			return Action::BREAK;
		}
	} else if (ch == end) {
		if (trace) cout << Indent(ch - beg) << "Act: end of expression: " << endl;
		return Action::BREAK;
	} else {
		if (trace) cout << Indent(ch - beg) << "Act: go forward one step ..." << endl;
		n.push((*ni)->tree.nodes.begin());
		m.push(++ch);
	}
	return Action::CONT;
}

template<bool trace>
Tree* parse_LL(Symbols::iterator& x, const Type* type, const Expr* e, Symbols::iterator beg, Symbols::iterator end) {
	if (type->rules.nodes.size()) {
		typedef Rules::NodeIter NodeIter;
		Tree::Children children;
		stack<NodeIter> n;
		stack<Symbols::iterator> m;
		stack<NodeIter> childnodes;
		n.push(type->rules.nodes.begin());
		m.push(x);
		while (!n.empty() && !m.empty()) {
			auto ch = m.top();
			if (ch->kind() == Symbol::CONST && (*n.top())->symb.kind() == Symbol::CONST) {
				const Rules* par = (*n.top())->parent ? (*n.top())->parent : &type->rules;
				auto constIter = par->constMap.find(ch->lit);
				if (constIter != par->constMap.end()) {
					n.top() = constIter->second;
					if (trace) cout << Indent(ch - beg) << "Expr const symbol: " << *m.top() << endl;
					if (trace) cout << Indent(ch - beg) << "Parse: constant " << (*n.top())->symb << " - success " << endl;
					n.top() = par->constLast;
					Action a = act<trace>(n, m, constIter->second, ch, e, beg, end);
					switch (a.kind) {
					case Action::RET  : x = ch; return new Tree(a.rule->id(), children);
					case Action::BREAK: goto out;
					case Action::CONT : continue;
					}
				}
			}
			if (const Type* tp = (*n.top())->symb.type()) {
				if (trace) cout << Indent(ch - beg) << "Expr symbol: " << *m.top() << endl;
				if (trace) cout << Indent(ch - beg) << "Parse: variable " << (*n.top())->symb << " of type: " << Lex::toStr(tp->id()) << endl;
				childnodes.push(n.top());
				if (Tree* child = parse_LL<trace>(ch, tp, e, beg, end)) {
					if (trace) cout << Indent(ch - beg) << "Parse: subexpression " << show(child) << " - success " << endl;
					children.emplace_back(child);
					Action a = act<trace>(n, m, n.top(), ch, e, beg, end);
					switch (a.kind) {
					case Action::RET  : x = ch; return new Tree(a.rule->id(), children);
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
	if (x->type()) {
		if (x->type() == type) {
			return new Tree(*x);
		} else if (Rule* super = find_super(x->type(), type)) {
			return new Tree(super->id(), new Tree(*x));
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
 			cout << "parsing expr: " <<  show(*ex)  << endl << endl;
 			cout << "source: " << Lex::toStr(ex->token.src()->id())  << endl << endl;
			parse_LL<true>(it, ex->type.get(), ex, ex->symbols.begin(), ex->symbols.end() - 1);
			throw Error("parsing", string("expression: ") + show(*ex) + " at: " + ex->token.show());
		}
	} catch (...) {
		exceptions.push_back(std::current_exception());
	}
}

#ifdef PARALLEL
#define PARALLEL_RUS_EXPR_PARSE
#endif

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
		tp->rules.sort();
	}
#ifdef PARALLEL_RUS_EXPR_PARSE
	tbb::parallel_for (tbb::blocked_range<size_t>(0, queue.size()),
		[] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				parse(queue[i]);
		}
	);
#else
	for (auto expr : queue) {
		parse(expr);
	}
#endif
	queue.clear();
	for (auto& ex : exceptions) {
		if (ex) std::rethrow_exception(ex);
	}
}

void enqueue(Expr& ex) {
	queue.push_back(&ex);
}

}}} // namespace mdl::rus::expr
