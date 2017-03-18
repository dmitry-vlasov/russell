#include "mm/ast.hpp"
#include "mm/sys.hpp"

namespace mdl { namespace mm {

Essential::Essential(uint l, const Vect& e) : label(l), expr(e)  {
	Sys::mod().math.essentials.add(label, this);
}
Essential::~Essential() {
	Sys::mod().math.essentials.del(label);
}
Floating::Floating(uint l, const Vect& e) : label(l), expr(e)  {
	Sys::mod().math.floatings.add(label, this);
}
Floating::~Floating() {
	Sys::mod().math.floatings.del(label);
}
Axiom::Axiom(uint l, const Vect& e) : label(l), expr(e), arity(Undef<uint>::get())  {
	Sys::mod().math.axioms.add(label, this);
}
Axiom::~Axiom() {
	Sys::mod().math.axioms.del(label);
}
Theorem::Theorem(uint l, const Vect& e, Proof* p) : label(l), expr(e), arity(Undef<uint>::get()), proof(p)  {
	Sys::mod().math.theorems.add(label, this);
}
Theorem::~Theorem() {
	if (proof) delete proof;
	Sys::mod().math.theorems.del(label);
}

Ref::Ref(uint label) : type(NONE), val() {
	Sys::Math& math = Sys::mod().math;
	if (math.floatings.has(label)) {
		type = FLOATING;
		math.floatings.use(label, val.flo);
	} else if (math.essentials.has(label)) {
		type = ESSENTIAL;
		math.essentials.use(label, val.ess);
	} else if (math.axioms.has(label)) {
		type = AXIOM;
		math.axioms.use(label, val.ax);
	} else if (math.theorems.has(label)) {
		type = THEOREM;
		math.theorems.use(label, val.th);
	} else
		throw Error("unknown label in proof", Lex::toStr(label));
}
Ref::Ref(const Ref& ref) : type(ref.type), val() {
	Sys::Math& math = Sys::mod().math;
	switch (type) {
	case FLOATING:  math.floatings.use(ref.label(), val.flo);  break;
	case ESSENTIAL: math.essentials.use(ref.label(), val.ess); break;
	case AXIOM:     math.axioms.use(ref.label(), val.ax);      break;
	case THEOREM:   math.theorems.use(ref.label(), val.th);    break;
	case PROOF:     val.prf = new Proof(*ref.val.prf);         break;
	}
}
Ref::~Ref() {
	if (!val.ptr) return;
	Sys::Math& math = Sys::mod().math;
	switch (type) {
	case FLOATING:  math.floatings.unuse(val.flo->label, val.flo);  break;
	case ESSENTIAL: math.essentials.unuse(val.ess->label, val.ess); break;
	case AXIOM:     math.axioms.unuse(val.ax->label, val.ax);       break;
	case THEOREM:   math.theorems.unuse(val.th->label, val.th);     break;
	case PROOF:     if (val.prf) delete val.prf;                    break;
	}
}

Proof::Proof(const vector<Ref*>& r) : refs(r) { }
Proof::Proof(vector<Ref*>&& r) : refs(std::move(r)) { }
Proof::~Proof() {
	for (auto r : refs) delete r;
}

Inclusion::Inclusion(Source* src, bool prim) : source(nullptr), primary(prim) {
	if (src) Sys::mod().math.sources.use(src->label, source);
}
Inclusion::~Inclusion() {
	if (source) Sys::mod().math.sources.unuse(source->label, source);
}

Source::Source(uint label) : mdl::Source<Source, Sys>(label), block(nullptr) {
	Sys::mod().math.sources.add(label, this);
}
Source::~Source() {
	if (block) delete block;
	Sys::mod().math.sources.del(label);
}

}} // mdl::mm
