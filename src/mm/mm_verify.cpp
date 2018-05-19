#include <boost/range/adaptor/reversed.hpp>

#include "mm_sys.hpp"
#include "mm_tree.hpp"

namespace mdl { namespace mm2 {

inline bool vect_contains(const vector<uint>& v, uint s) {
	for (uint x : v) {
		if (x == s) return true;
	}
	return false;
}

bool areDisjointed(const Assertion* ass, Symbol s1, Symbol s2) {
	for (auto it = ass->disj.vect.cbegin(); it != ass->disj.vect.cend(); ++ it) {
		if (vect_contains(*(*it).get(), s1.literal()) && vect_contains(*(*it).get(), s2.literal())) {
			return true;
		}
	}
	return false;
}

static void checkDisjPair(const Expr& ex1, const Expr& ex2, const Assertion* th, const Assertion* ass) {
	for (auto s_1 : ex1) {
		for (auto s_2 : ex2) {
			if (s_1.var && s_1 == s_2) {
				string msg = "disjointed violation, ";
				msg += "variable " + show_sy(s_1) + " is common for " + show_ex(ex1) + " and " + show_ex(ex2);
				throw Error("verification", msg, th->token);
			}
			if (s_1.var && s_2.var && !areDisjointed(th, s_1.lit, s_2.lit)) {
				string msg = "inherited disjointed violation, vars: ";
				msg += show_sy(s_1) + " and " + show_sy(s_2) + " ";
				msg += "are not disjointed in " + Lex::toStr(th->id()) + ", ";
				msg += "while claimed to be disjointed in " + Lex::toStr(ass->id());
				throw Error("verification", msg, th->token);
			}
		}
	}
}

static void checkDisj(const Subst& sub, const Assertion* ass, const Assertion* th) {
	for (auto p_1 : sub) {
		for (auto p_2 : sub) {
			if (p_1.first == p_2.first) continue;
			if (areDisjointed(ass, p_1.first, p_2.first)) {
				checkDisjPair(p_1.second, p_2.second, th, ass);
			}
		}
	}
}

static void checkSymbols(const Assertion* ass, const Expr& expr) {
	for (auto s : expr) {
		bool is_const = Sys::get().math.consts.count(s.lit);
		bool is_var = false;
		if (vect_contains(ass->vars.vars, s.literal())) {
			is_var = true;
			break;
		}
		if (is_const && is_var) {
			throw Error("constant symbol is marked as variable", Lex::toStr(s.lit), ass->token);
		}
		if (!is_const && !is_var) {
			throw Error("symbol neither constant nor variable", Lex::toStr(s.lit), ass->token);
		}
	}
}

template<typename T>
static void checkSymbols(const Assertion* ass, const vector<unique_ptr<T>>& lines) {
	for (const auto& line : lines) {
		checkSymbols(ass, line.get()->expr);
	}
}

static void checkFloating(const Assertion* ass, const vector<unique_ptr<Var>>& floatings) {
	for (const auto& flo : floatings) {
		if (flo.get()->expr.size() != 2) {
			throw Error("floating declaration must have exactly 2 symbols", ass->token);
		}
		if (flo.get()->expr[0].var) {
			throw Error("floating first symbol must be type (constant)", ass->token);
		}
		if (!flo.get()->expr[1].var) {
			throw Error("floating second symbol must be type variable ", show_ex(flo->expr), ass->token);
		}
	}
}

static void checkDisjointed(const Assertion* ass, Symbol var) {
	if (!vect_contains(ass->vars.vars, var.literal())) {
		throw Error("disjointed symbols must be variables", ass->token);
	}
}


static void checkDisjointed(const Assertion* ass, const Disj& disj) {
	for (const auto& d : disj.vect) {
		for (auto s : *d.get()) {
			checkDisjointed(ass, s);
		}
	}
}

static void checkSymbols(const Assertion* ass) {
	checkSymbols(ass, ass->hyps);
	checkSymbols(ass, ass->outerVars);
	checkSymbols(ass, ass->innerVars);
	checkSymbols(ass, ass->expr);
	checkFloating(ass, ass->outerVars);
	checkFloating(ass, ass->innerVars);
	checkDisjointed(ass, ass->disj);
}

static void apply(const Assertion* ass, const Assertion* th, stack<Expr>& expr_stack) {
	Subst sub;
	vector<pair<Expr*, Expr>> hypsPairs;
	hypsPairs.reserve(ass->hyps.size());
	for (const auto& ess : boost::adaptors::reverse(ass->hyps)) {
		if (expr_stack.empty()) {
			string msg = "empty stack (essential):\n";
			msg += "theorem " + Lex::toStr(th->id()) + "\n";
			msg += "assertion " + Lex::toStr(ass->id()) + "\n";
			throw Error("verification", msg, th->token);
		}
		hypsPairs.emplace_back(&ess->expr, expr_stack.top());
		expr_stack.pop();
	}
	for (const auto& flo : boost::adaptors::reverse(ass->outerVars)) {
		if (expr_stack.empty()) {
			string msg = "empty stack (floating):\n";
			msg += "theorem " + Lex::toStr(th->id()) + "\n";
			msg += "assertion " + Lex::toStr(ass->id()) + "\n";
			throw Error("verification", msg, th->token);
		}
		sub[flo->var()] = expr_stack.top();
		expr_stack.pop();
	}
	for (const auto& p : hypsPairs) {
		if (apply_subst(sub, *p.first) != p.second) {
			string msg = "hypothesis mismatch:\n";
			msg += show_ex(apply_subst(sub, *p.first)) + "\n";
			msg += "and\n";
			msg += show_ex(p.second) + "\n";
			msg += "theorem " + Lex::toStr(th->id()) + "\n";
			msg += "assertion " + Lex::toStr(ass->id()) + "\n";
			throw Error("verification", msg, th->token);
		}
	}
	checkDisj(sub, ass, th);
	expr_stack.push(apply_subst(sub, ass->expr));
}

static void verify_assertion(const Assertion* ass) {
	checkSymbols(ass);
	if (ass->proof.refs.empty()) return;
	stack<Expr> expr_stack;
	for (const auto& ref : ass->proof.refs) {
		switch (ref.kind()) {
		case Ref::HYP : expr_stack.push(ref.hyp()->expr); break;
		case Ref::VAR : expr_stack.push(ref.var()->expr); break;
		case Ref::ASS : apply(ref.ass(), ass, expr_stack); break;
		default : assert(false && "impossible"); break;
		}
	}
	if (expr_stack.empty()) {
		string msg("empty stack in the end of proof\n");
		msg += "theorem: " + show(*ass) + "\n";
		throw Error("verification", msg, ass->token);
	}
	if (expr_stack.top() != ass->expr) {
		string msg("propositions mismatch\n");
		msg += "on stack: " + show_ex(expr_stack.top()) + "\n";
		msg += "in assertion: " + show_ex(ass->expr) + "\n";
		throw Error("verification", msg, ass->token);
	}
	expr_stack.pop();
	if (!expr_stack.empty()) {
		throw Error("verification: non-empty stack at the end", ass->token);
	}
}

#define PARALLEL_VERIFY

void verify() {
	Sys::timer()["verify"].start();
#ifdef PARALLEL_VERIFY
	vector<const Assertion*> assertions;
	for (auto p : Sys::mod().math.get<Assertion>())
		assertions.push_back(p.second.data);
	tbb::parallel_for (tbb::blocked_range<size_t>(0, assertions.size()),
		[assertions] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				verify_assertion(assertions[i]);
		}
	);
#else
	for (auto& p : Sys::mod().math.get<Assertion>()) {
		verify_assertion(p.second.data);
	}
#endif
	Sys::timer()["verify"].stop();
}

}} // mdl::smm::verify
