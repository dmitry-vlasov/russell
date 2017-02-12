#include "smm/sys.hpp"

namespace mdl { namespace smm {



Assertion::Assertion() :
	variables(),
	disjointed(),
	essential(),
	floating(),
	inner(),
	prop(nullptr),
	proof(nullptr),
	loc() {
}
Assertion::~Assertion() {
	for (Variables* v : variables)   delete v;
	for (Disjointed* d : disjointed) delete d;
	for (Essential* e : essential)   delete e;
	for (Floating* f : floating)     delete f;
	for (Inner* i : inner)           delete i;
	if (prop) delete prop;
	if (proof) delete proof;
	Sys::mod().math.axioms.del(prop->label);
}

void Node::destroy() {
	switch(type) {
	case NONE: break;
	case ASSERTION: delete val.ass; break;
	case CONSTANTS: delete val.cst; break;
	case INCLUSION: delete val.inc; break;
	case COMMENT:   delete val.com; break;
	default : assert(false && "impossible");  break;
	}
	type = NONE;
}

Ref::Ref(uint label, bool ax) : type(ax ? AXIOM : THEOREM), val() {
	Sys::mod().math.assertions.use(label, val.ass);
}
Ref::Ref(const Ref& ref) : type(ref.type), val() {
	Sys::Math& math = Sys::mod().math;
	switch (type) {
	case FLOATING:  val.flo = ref.val.flo;  break;
	case ESSENTIAL: val.ess = ref.val.ess;  break;
	case AXIOM:     math.assertions.use(ref.label(), val.ax); break;
	case THEOREM:   math.assertions.use(ref.label(), val.th); break;
	case PROOF:     val.prf = new Proof(*ref.val.prf);        break;
	}
}
Ref::~Ref() {
	Sys::Math& math = Sys::mod().math;
	switch (type) {
	case AXIOM:     math.assertions.unuse(ref.label(), val.ax); break;
	case THEOREM:   math.assertions.unuse(ref.label(), val.th); break;
	case PROOF:     if (val.prf) delete val.prf;                break;
	}
}

inline Proof::~ Proof() {
	for (auto r : refs) delete r;
}

Inclusion::Inclusion(uint label) : source(nullptr) {
	Sys::mod().math.sources.use(label, source);
}
Inclusion::~Inclusion() {
	Sys::mod().math.sources.unuse(source->label, source);
}

Source::Source(uint l) : label(l), data(), block(nullptr) {
	Sys::mod().math.sources.add(label, this);
	path().read(data);
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
	for (Node& n : contents) n.destroy();
	Sys::mod().math.sources.del(label);
}


}} // mdl::smm


