#include "mm_sys.hpp"
#include "mm_ast.hpp"

namespace mdl { namespace mm {

static void fixsynt_apply(Assertion* ass, Assertion* th, stack<shared_ptr<Expr>>& expr_stack) {
	Subst sub;
	vector<pair<Expr*, shared_ptr<Expr>>> hypsPairs;
	hypsPairs.reserve(ass->hyps.size());
	for (int i = ass->hyps.size() - 1; i >= 0; --i) {
		auto& ess = ass->hyps[i];
		if (expr_stack.empty()) {
			string msg = "empty stack (essential):\n";
			msg += "\ttheorem: " + Lex::toStr(th->id()) + "\n";
			msg += "\tassertion: " + Lex::toStr(ass->id()) + "\n";
			throw Error("verification", msg, th->token);
		}
		hypsPairs.emplace_back(&ess->expr, expr_stack.top());
		expr_stack.pop();
	}
	for (int i = ass->outerVars.size() - 1; i >= 0; --i) {
		auto& flo = ass->outerVars[i];
		if (expr_stack.empty()) {
			string msg = "empty stack (floating):\n";
			msg += "\ttheorem: " + Lex::toStr(th->id()) + "\n";
			msg += "\tassertion: " + Lex::toStr(ass->id()) + "\n";
			throw Error("verification", msg, th->token);
		}
		sub[flo->var()] = *expr_stack.top();
		expr_stack.pop();
	}
	for (auto& p : hypsPairs) {
		*p.second = apply_subst(sub, *p.first);
	}
	expr_stack.push(make_shared<Expr>(apply_subst(sub, ass->expr)));
}

static void fixsynt_assertion(Assertion* ass) {
	//checkSymbols(ass);
	if (ass->proof.refs.empty()) return;
	stack<shared_ptr<Expr>> expr_stack;
	for (auto& ref : ass->proof.refs) {
		switch (ref.kind()) {
		case Ref::HYP : expr_stack.push(shared_ptr<Expr>(&ref.hyp()->expr)); break;
		case Ref::VAR : expr_stack.push(shared_ptr<Expr>(&ref.var()->expr)); break;
		case Ref::ASS : fixsynt_apply(ref.ass(), ass, expr_stack); break;
		default : assert(false && "impossible"); break;
		}
	}
	if (expr_stack.empty()) {
		string msg("empty stack in the end of proof\n");
		msg += "theorem: " + ass->show() + "\n";
		throw Error("fixsynt_assertion", msg, ass->token);
	}
	ass->expr = *expr_stack.top();
	expr_stack.pop();
}

void fix_rule(Assertion& rule) {
	// Rule body starts with variable
	if (rule.expr.size() >= 2 && rule.expr.at(1).var) {
		// Surround rule body with ( and )
		rule.expr.insert(rule.expr.begin() + 1, Literal(Lex::toInt("(")));
		rule.expr.push_back(Literal(Lex::toInt(")")));
	}
}

#ifdef PARALLEL
#define PARALLEL_MM_FIXSYNT
#endif

void fixsynt() {
	Sys::timer()["fixsynt"].start();
	vector<Assertion*> theorems;
	vector<Assertion*> rules;
	for (Assertion& a : Sys::mod().math.get<Assertion>()) {
		if (!a.proof.refs.empty()) {
			theorems.push_back(&a);
		} else {
			if (a.expr.front().lit != Lex::toInt("|-")) {
				fix_rule(a);
			}
		}
	}
#ifdef PARALLEL_MM_FIXSYNT
	tbb::parallel_for (tbb::blocked_range<size_t>(0, theorems.size()),
		[theorems] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				fixsynt_assertion(theorems[i]);
			}
		}
	);
#else
	for (auto th : theorems) {
		fixsynt_assertion(th);
	}
#endif
	Sys::timer()["fixsynt"].stop();
}

}}
