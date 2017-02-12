#include "rus/sys.hpp"

namespace mdl { namespace rus {

Const::Const(uint j, uint i, Symbol s, Symbol a, Symbol l) :
	ind(i), id(i), symb(s), ascii(a), latex(l) {
	Sys::mod().math.consts.add(id, this);
}
Const::~Const() {
	Sys::mod().math.consts.del(id);
}

Rule* create_super(Type* inf, Type* sup) {
	Rule* rule = new Rule;
	rule->id = create_id("sup", show_id(inf->id), show_id(sup->id));
	rule->vars.v.push_back(create_symbol("x", inf));
	rule->term.push_back(create_symbol("x", inf));
	rule->type = sup;

	VarStack var_stack;
	AddVars add_vars;
	PushVars push_vars;
	push_vars(var_stack);
	add_vars(var_stack, rule->vars);
	mark_vars(rule->term, var_stack);
	parse_term(rule->term, rule);
	return rule;
}

void collect_supers(Type* inf, Type* s) {
	for (auto sup : s->sup) {
		Rule* super = create_super(inf, sup);
		inf->supers[sup] = super;
		collect_supers(inf, sup);
	}
}

Type::Type(uint i) : ind(-1), id(), sup(), supers(), rules() {
	collect_supers(this, this);
	Sys::mod().math.types.add(id, this);
}
Type::~Type() {
	for (auto p : supers) delete p.second;
	Sys::mod().math.types.del(id);
}

Rule::Rule(uint i) : ind(-1), id(i), type(nullptr), vars(), term() {
	type->rules.add(term) = this;
	Sys::mod().math.rules.add(id, this);
}
Rule::~Rule() {
	Sys::mod().math.rules.del(id);
}

void enqueue_expressions(Assertion& ass) {
	for (Hyp* hyp : ass.hyps)
		expr::enqueue(hyp->expr);
	for (Prop* prop : ass.props)
		expr::enqueue(prop->expr);
}


void enqueue_expressions(Def* def) {

	enqueue_expressions(def->ass);
}

Assertion::Assertion(uint i) : ind(-1), id(i), vars(), disj(), hyps(), props(), loc() {
	enqueue_expressions(this);
}
Assertion::~ Assertion() {
	for (auto h : hyps) delete h;
	for (auto p : props) delete p;
}

Axiom::Axiom(uint id) : ass(id) {
	Sys::mod().math.axioms.add(ass.id, this);
}
Axiom::~Axiom() {
	Sys::mod().math.axioms.del(ass.id);
}

Def::Def(uint id) : ass(id) {
	expr::enqueue(dfm);
	expr::enqueue(dfs);
	Sys::mod().math.defs.add(ass.id, this);
}
Def::~Def() {
	Sys::mod().math.defs.del(ass.id);
}

Theorem::Theorem(uint id) : ass(id), proofs() {
	Sys::mod().math.theorems.add(ass.id, this);
}
Theorem::~Theorem() {
	Sys::mod().math.theorems.del(ass.id);
}

Proof::Proof(uint i) :
	ind(-1), id(i), vars(), elems(),
	thm(nullptr), par(nullptr), has_id(false) {
	has_id = !Undef<uint>::is(id);
	if (!has_id)
		id = Sys::mod().lex.labels.toInt(to_string(ind));
	for (auto& el : elems) {
		if (el.kind == Proof::Elem::STEP) {
			Step* step = el.val.step;
			expr::enqueue(step->expr);
			if (step->kind == Step::CLAIM)
				enqueue_expressions(step->proof);
		}
	}
}
Proof::~Proof() {
	for (auto& e : elems) e.destroy();
}


Import::Import(uint label) : source(nullptr) {
	Sys::mod().math.sources.use(label, source);
}
Import::~Import() {
	Sys::mod().math.sources.unuse(source->label, source);
}

Step::Step(uint i, Kind k, uint id, vector<Ref*> r, const Expr& e, Proof* p) :
ind(i), expr(e), kind(k), val(), refs(r), proof(p) {
	Sys::Math& math = Sys::mod().math;
	switch (kind) {
	case AXM : math.axioms.use(id, val.axm);   break;
	case THM : math.theorems.use(id, val.thm); break;
	case DEF : math.defs.use(id, val.def);     break;
	}
}
Step::Step(Proof* p) :
ind(), expr(), kind(NONE), val(), refs(), proof(p) {
}
Step::~Step() {
	Sys::Math& math = Sys::mod().math;
	switch (kind) {
	case AXM : math.axioms.unuse(id, val.axm);   break;
	case THM : math.theorems.unuse(id, val.thm); break;
	case DEF : math.defs.unuse(id, val.def);     break;
	}
}

Source::Source(uint l) : label(l), data(), block(nullptr) {
	Sys::mod().math.sources.add(label, this);
}
Path Source::path() {
	return Sys::mod().conf().in.relative(name());
}
string Source::name() {
	return Sys::get().lex.labels.toStr(label);
}
void Source::read() {
	path().read(data);
}
void Source::write() {
	path().write(data);
}
Source::~Source() {
	if (theory) delete theory;
	Sys::mod().math.sources.del(label);
}


}} // mdl::rus
