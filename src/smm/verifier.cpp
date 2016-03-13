#include <boost/range/adaptor/reversed.hpp>
#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

typedef map<Symbol, Expr> Subst;

string show (const Subst& subst) {
	string str;
	for (auto it : subst) {
		str += show(it.first);
		str += " => ";
		str += show(it.second);
		str += '\n';
	}
	return str;
}

static void checkDisjPair(const Expr& ex1, const Expr& ex2, const Assertion* th, const Assertion* ass) {
	for (auto s_1 : ex1.symbols) {
		for (auto s_2 : ex2.symbols) {
			if (s_1.var && s_1 == s_2) {
				string msg = "disjointed violation, ";
				msg += "variable " + show(s_1) + " is common for " + show(ex1) + " and " + show(ex2);
				throw Error("verification", msg, &th->loc);
			}
			if (s_1.var && s_2.var && !th->areDisjointed(s_1.lit, s_2.lit)) {
				string msg = "inherited disjointed violation, vars: ";
				msg += show(s_1) + " and " + show(s_2) + " ";
				msg += "are not disjointed in " + Smm::get().lex.labels.toStr(th->prop.label) + ", ";
				msg += "while claimed to be disjointed in " + Smm::get().lex.labels.toStr(ass->prop.label);
				throw Error("verification", msg, &th->loc);
			}
		}
	}
}

static void checkDisj(const Subst& sub, const Assertion* ass, const Assertion* th) {
	for (auto p_1 : sub) {
		for (auto p_2 : sub) {
			if (p_1.first == p_2.first)
				continue;
			if (ass->areDisjointed(p_1.first, p_2.first))
				checkDisjPair(p_1.second, p_2.second, th, ass);
		}
	}
}

static Expr apply(const Subst& sub, const Expr& expr) {
	Expr ret;
	for (auto s : expr.symbols) {
		if (s.var) {
			auto ex = sub.find(s);
			if (ex == sub.cend())
				ret += s;
			else
				ret += ex->second;
		} else
			ret += s;
	}
	return  ret;
}

static void checkSymbols(const Assertion* ass, const Expr& expr) {
	for (auto s : expr.symbols) {
		bool is_const = (Smm::get().math.constants.find(s) != Smm::get().math.constants.end());
		bool is_var = false;
		for (auto& v : ass->variables) {
			if (v.expr.contains(s)) {
				is_var = true;
				break;
			}
		}
		if (is_const && is_var)
			throw Error("constant symbol is marked as variable", &ass->loc);
		if (!is_const && !is_var)
			throw Error("symbol neither constant nor variable", &ass->loc);
	}
}

template<typename T>
static void checkSymbols(const Assertion* ass, const vector<T>& lines) {
	for (auto& line : lines)
		checkSymbols(ass, line.expr);
}

template<typename T>
static void checkFloating(const Assertion* ass, const vector<T>& floatings) {
	for (auto& flo : floatings) {
		if (flo.expr.symbols.size() != 2)
			throw Error("floating declaration must have exactly 2 symbols", &ass->loc);
		if (flo.expr.symbols[0].var)
			throw Error("floating first symbol must be type (constant)", &ass->loc);
		if (!flo.expr.symbols[1].var) {
			throw Error("floating second symbol must be type variable ", show(flo.expr), &ass->loc);
		}
	}
}

static void checkDisjointed(const Assertion* ass, Symbol var) {
	for (auto& vars : ass->variables)
		if (vars.expr.contains(var))
			return;
	throw Error("disjointed symbols must be variables", &ass->loc);
}


static void checkDisjointed(const Assertion* ass, const vector<Disjointed>& disjointeds) {
	for (auto& disj : disjointeds)
		for (auto s : disj.expr.symbols)
			checkDisjointed(ass, s);
}

static void checkSymbols(const Assertion* ass) {
	checkSymbols(ass, ass->essential);
	checkSymbols(ass, ass->floating);
	checkSymbols(ass, ass->prop.expr);
	checkFloating(ass, ass->floating);
	checkFloating(ass, ass->inner);
	checkDisjointed(ass, ass->disjointed);
}

static void apply(const Assertion* ass, const Assertion* th, stack<Expr>& expr_stack) {
	Subst sub;
	for (auto& flo : boost::adaptors::reverse(ass->floating)) {
		if (expr_stack.empty())
			throw Error("verification", "empty stack", &th->loc);
		sub[flo.var()] = expr_stack.top();
		expr_stack.pop();
	}
	for (auto& ess : boost::adaptors::reverse(ass->essential)) {
		if (expr_stack.empty())
			throw Error("verification", "empty stack", &th->loc);
		if (apply(sub, ess.expr) != expr_stack.top())
			throw Error("verification", "hypothesis mismatch", &th->loc);
		expr_stack.pop();
	}
	checkDisj(sub, ass, th);
	expr_stack.push(apply(sub, ass->prop.expr));
}

static void assertion(const Assertion* ass, const vector<Assertion*>& theory) {
	checkSymbols(ass);
	stack<Expr> expr_stack;
	const Proof* proof = ass->proof;
	if (!proof) return;
	for (auto& ref : proof->refs) {
		switch (ref.type) {
		case Ref::PREF_E : expr_stack.push(ass->essential[ref.index].expr); break;
		case Ref::PREF_F : expr_stack.push(ass->floating[ref.index].expr); break;
		case Ref::PREF_I : expr_stack.push(ass->inner[ref.index].expr); break;
		case Ref::PREF_A : // intentionally left blank
		case Ref::PREF_P : apply(theory[ref.index], ass, expr_stack); break;
		}
	}
	if (expr_stack.top() != ass->prop.expr) {
		throw Error("verification", "propositions mismatch", &ass->loc);
	}
	expr_stack.pop();
	if (!expr_stack.empty()) {
		throw Error("verification: non-empty stack at the end", &ass->loc);
	}
}

static void math(const vector<Assertion*>& theory) {
	for (auto ass : theory) {
		assertion(ass, theory);
	}
}

void verify(const vector<Assertion*>& theory) {
	math(theory);
}

}} // mdl::smm::verify
