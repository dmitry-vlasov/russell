#include <rus_ast.hpp>

namespace mdl { namespace rus {

#ifdef PARALLEL
#define PARALLEL_FIXSYNT
#endif

void surround_with_parentheses(Expr& ex) {
	ex.symbols.insert(ex.symbols.begin(), make_unique<Const>(Lex::toInt("(")));
	ex.symbols.push_back(make_unique<Const>(Lex::toInt(")")));
}

void fixsynt() {
	for (Rule& r : Sys::mod().math.get<Rule>()) {
		if (r.term.symbols.front()->kind() == Symbol::VAR && r.term.symbols.size() > 1) {
			surround_with_parentheses(r.term);
		}
	}
	vector<Expr*> exprs;
	for (Assertion& a : Sys::mod().math.get<Assertion>()) {
		exprs.push_back(&a.prop->expr);
		for (auto& hyp : a.hyps) {
			exprs.push_back(&hyp->expr);
		}
		if (Theorem* t = dynamic_cast<Theorem*>(&a)) {
			for (auto& step : t->proof->steps) {
				exprs.push_back(&step->expr);
			}
		} else if (Def* d = dynamic_cast<Def*>(&a)) {
			exprs.push_back(&d->dfm);
			exprs.push_back(&d->dfs);
			if (d->def.symbols.at(1)->lit() == Lex::toInt("=") || d->def.symbols.at(1)->lit() == Lex::toInt("<->")) {
				surround_with_parentheses(d->def);
			}
		}
	}
#ifdef PARALLEL_FIXSYNT
	tbb::parallel_for (tbb::blocked_range<size_t>(0, exprs.size()),
		[exprs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				exprs.at(i)->rebuildSymbols();
		}
	);
#else
	for (auto e : exprs) {
		e->rebuildSymbols();
	}
#endif
}

}} // mdl::rus
