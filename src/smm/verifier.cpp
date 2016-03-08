#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

typedef map<Symbol, Expr> Subst;

string show (const Subst& subst) {
	string str;
	for (auto it = subst.cbegin(); it != subst.cend(); ++ it) {
		it->first.show (str);
		str += " => ";
		it->second.show (str);
		str += '\n';
	}
	return str;
}

static void checkDisjPair(const Expr& ex1, const Expr& ex2, const Assertion* th) {
	for (auto it = ex1.symbols.cbegin(); it != ex1.symbols.cend(); ++ it) {
		for (auto jt = ex2.symbols.cbegin(); jt != ex2.symbols.cend(); ++ jt) {
			if (it->isVar && it == jt)
				throw Error("verification", "disjointed violation", &th->loc);
			if (it->isVar && jt->isVar && !th->areDisjointed(it->literal, jt->literal)) {
				string msg = "inherited disjointed violation, vars: ";
				it->show(msg);
				msg += " and ";
				jt->show(msg);
				throw Error("verification", msg, &th->loc);
			}
		}
	}
}

static void checkDisj(const Subst& sub, const Assertion* ass, const Assertion* th) {
	for (auto it = sub.cbegin(); it != sub.cend(); ++ it) {
		for (auto jt = sub.cbegin(); jt != sub.cend(); ++ jt) {
			if (it->first == jt->first)
				continue;
			if (ass->areDisjointed(it->first, jt->first))
				checkDisjPair(it->second, jt->second, th);
		}
	}
}

static Expr apply(const Subst& sub, const Expr& expr) {
	Expr ret;
	for (auto it = expr.symbols.cbegin(); it != expr.symbols.cend(); ++ it) {
		Symbol s = *it;
		if (s.isVar) {
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
	for (auto it = expr.symbols.cbegin(); it != expr.symbols.cend(); ++ it) {
		bool is_const = (Smm::get().math.constants.find(*it) != Smm::get().math.constants.end());
		bool is_var = false;
		for (auto jt = ass->variables.cbegin(); jt != ass->variables.cend(); ++ jt) {
			if (jt->expr.contains(*it)) {
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
	for (auto it = lines.cbegin(); it != lines.cend(); ++ it)
		checkSymbols(ass, it->expr);
}

template<typename T>
static void checkFloating(const Assertion* ass, const vector<T>& floatings) {
	for (auto it = floatings.cbegin(); it != floatings.cend(); ++ it) {
		if (it->expr.symbols.size() != 2)
			throw Error("floating declaration must have exactly 2 symbols", &ass->loc);
		if (it->expr.symbols[0].isVar)
			throw Error("floating first symbol must be type (constant)", &ass->loc);
		if (!it->expr.symbols[1].isVar) {
			string str;
			it->expr.show(str);
			throw Error("floating second symbol must be type variable ", str, &ass->loc);
		}
	}
}

static void checkDisjointed(const Assertion* ass, Symbol var) {
	for (auto it = ass->variables.cbegin(); it != ass->variables.cend(); ++ it)
		if (it->expr.contains(var))
			return;
	throw Error("disjointed symbols must be variables", &ass->loc);
}


static void checkDisjointed(const Assertion* ass, const vector<Disjointed>& disjointeds) {
	for (auto it = disjointeds.cbegin(); it != disjointeds.cend(); ++ it)
		for (auto jt = it->expr.symbols.cbegin(); jt != it->expr.symbols.cend(); ++ jt)
			checkDisjointed(ass, *jt);
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
	for (auto it = ass->floating.crbegin(); it != ass->floating.crend(); ++ it) {
		if (expr_stack.empty())
			throw Error("verification", "empty stack", &th->loc);
		sub[it->var()] = expr_stack.top();
		expr_stack.pop();
	}
	for (auto it = ass->essential.crbegin(); it != ass->essential.crend(); ++ it) {
		if (expr_stack.empty())
			throw Error("verification", "empty stack", &th->loc);
		if (apply(sub, it->expr) != expr_stack.top())
			throw Error("verification", "hypothesis mismatch", &th->loc);
		expr_stack.pop();
	}
	checkDisj(sub, ass, th);
	expr_stack.push(apply(sub, ass->prop.expr));
}

namespace verify {

void assertion(const Assertion* ass, const vector<Assertion*>& theory) {
	checkSymbols(ass);
	stack<Expr> expr_stack;
	const Proof* proof = ass->proof;
	if (!proof) return;
	for (auto it = proof->refs.cbegin(); it != proof->refs.cend(); ++ it) {
		switch (it->type) {
		case Ref::PREF_E : expr_stack.push(ass->essential[it->index].expr); break;
		case Ref::PREF_F : expr_stack.push(ass->floating[it->index].expr); break;
		case Ref::PREF_I : expr_stack.push(ass->inner[it->index].expr); break;
		case Ref::PREF_A : // intentionally left blank
		case Ref::PREF_P : apply(theory[it->index], ass, expr_stack); break;
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

void math(const vector<Assertion*>& theory) {
	for (auto it = theory.begin(); it != theory.cend(); ++ it) {
		assertion(*it, theory);
	}
}

}}} // mdl::smm::verify
