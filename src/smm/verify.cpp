#include <boost/range/adaptor/reversed.hpp>
#include "smm/tree.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

bool areDisjointed(const Assertion* ass, Symbol s1, Symbol s2) {
	for (auto it = ass->disjointed.cbegin(); it != ass->disjointed.cend(); ++ it) {
		if (contains((*it)->expr, s1) && contains((*it)->expr, s2))
			return true;
	}
	return false;
}

static void checkDisjPair(const Vect& ex1, const Vect& ex2, const Assertion* th, const Assertion* ass) {
	for (auto s_1 : ex1) {
		for (auto s_2 : ex2) {
			if (s_1.var && s_1 == s_2) {
				string msg = "disjointed violation, ";
				msg += "variable " + show_sy(s_1) + " is common for " + show_ex(ex1) + " and " + show_ex(ex2);
				throw Error("verification", msg, &th->loc);
			}
			if (s_1.var && s_2.var && !areDisjointed(th, s_1.lit, s_2.lit)) {
				string msg = "inherited disjointed violation, vars: ";
				msg += show_sy(s_1) + " and " + show_sy(s_2) + " ";
				msg += "are not disjointed in " + Lex::toStr(th->prop.label) + ", ";
				msg += "while claimed to be disjointed in " + Lex::toStr(ass->prop.label);
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
			if (areDisjointed(ass, p_1.first, p_2.first))
				checkDisjPair(p_1.second, p_2.second, th, ass);
		}
	}
}

inline void append_expr(Vect& ex_1, const Vect& ex_2) {
	auto it = ex_2.cbegin();
	++ it;
	for (; it != ex_2.cend(); ++ it)
		ex_1.push_back(*it);
}

Vect apply(const Subst& sub, const Vect& expr) {
	Vect ret;
	for (auto s : expr) {
		if (s.var) {
			auto ex = sub.find(s);
			if (ex == sub.cend())
				ret.push_back(s);
			else
				append_expr(ret, ex->second);
		} else
			ret += s;
	}
	return  ret;
}

static void checkSymbols(const Assertion* ass, const Vect& expr) {
	for (auto s : expr) {
		bool is_const = (System::get().math.constants.find(s) != System::get().math.constants.end());
		bool is_var = false;
		for (auto& v : ass->variables) {
			if (contains(v->expr, s)) {
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
static void checkSymbols(const Assertion* ass, const vector<T*>& lines) {
	for (auto& line : lines)
		checkSymbols(ass, line->expr);
}

template<typename T>
static void checkFloating(const Assertion* ass, const vector<T>& floatings) {
	for (auto flo : floatings) {
		if (flo->expr.size() != 2)
			throw Error("floating declaration must have exactly 2 symbols", &ass->loc);
		if (flo->expr[0].var)
			throw Error("floating first symbol must be type (constant)", &ass->loc);
		if (!flo->expr[1].var) {
			throw Error("floating second symbol must be type variable ", show_ex(flo->expr), &ass->loc);
		}
	}
}

static void checkDisjointed(const Assertion* ass, Symbol var) {
	for (auto vars : ass->variables)
		if (contains(vars->expr, var))
			return;
	throw Error("disjointed symbols must be variables", &ass->loc);
}


static void checkDisjointed(const Assertion* ass, const vector<Disjointed*>& disjointeds) {
	for (auto disj : disjointeds)
		for (auto s : disj->expr)
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

static void apply(const Assertion* ass, const Assertion* th, stack<Vect>& expr_stack) {
	Subst sub;
	for (auto flo : boost::adaptors::reverse(ass->floating)) {
		if (expr_stack.empty()) {
			string msg = "empty stack (floating):\n";
			msg += "theorem " + Lex::toStr(th->prop.label) + "\n";
			msg += "assertion " + Lex::toStr(ass->prop.label) + "\n";
			throw Error("verification", msg, &th->loc);
		}
		sub[flo->var()] = expr_stack.top();
		expr_stack.pop();
	}
	for (auto ess : boost::adaptors::reverse(ass->essential)) {
		if (expr_stack.empty()) {
			string msg = "empty stack (essential):\n";
			msg += "theorem " + Lex::toStr(th->prop.label) + "\n";
			msg += "assertion " + Lex::toStr(ass->prop.label) + "\n";
			throw Error("verification", msg, &th->loc);
		}
		if (apply(sub, ess->expr) != expr_stack.top()) {
			string msg = "hypothesis mismatch:\n";
			msg += show_ex(apply(sub, ess->expr)) + "\n";
			msg += "and\n";
			msg += show_ex(expr_stack.top()) + "\n";
			msg += "theorem " + Lex::toStr(th->prop.label) + "\n";
			msg += "assertion " + Lex::toStr(ass->prop.label) + "\n";
			throw Error("verification", msg, &th->loc);
		}
		expr_stack.pop();
	}
	checkDisj(sub, ass, th);
	expr_stack.push(apply(sub, ass->prop.expr));
}

static void assertion(const Assertion* ass) {
	checkSymbols(ass);
	stack<Vect> expr_stack;
	const Proof* proof = ass->proof;
	if (!proof) return;
	for (auto& ref : proof->refs) {
		switch (ref.type) {
		case Ref::ESSENTIAL : expr_stack.push(ref.val.ess->expr); break;
		case Ref::FLOATING  : expr_stack.push(ref.val.flo->expr); break;
		case Ref::INNER     : expr_stack.push(ref.val.inn->expr); break;
		case Ref::AXIOM: // intentionally left blank
		case Ref::THEOREM   : apply(ref.val.ass, ass, expr_stack); break;
		default : assert(false && "impossible"); break;
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

static void math() {
	for (auto p : System::mod().math.assertions) {
		assertion(p.second);
	}
}

void verify() {
	math();
}

}} // mdl::smm::verify
