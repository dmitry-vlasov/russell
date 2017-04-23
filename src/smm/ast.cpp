#include "smm/ast.hpp"

namespace mdl { namespace smm {

Ref::Ref(uint label, bool ax) : type(ax ? AXIOM : THEOREM), val() {
	val.ass = new User<Assertion>(label);
}
Ref::Ref(const Ref& ref) : type(ref.type) {
	switch (type) {
	case INNER:     val.inn = ref.val.inn; break;
	case FLOATING:  val.flo = ref.val.flo; break;
	case ESSENTIAL: val.ess = ref.val.ess; break;
	case AXIOM:     // intentionally left blank
	case THEOREM:   val.ass = new User<Assertion>(ref.label());
	}
}
Ref::~Ref() { if (is_assertion()) delete val.ass; }

Assertion::~Assertion() {
	for (Variables* v : variables)   delete v;
	for (Disjointed* d : disjointed) delete d;
	for (Essential* e : essential)   delete e;
	for (Floating* f : floating)     delete f;
	for (Inner* i : inner)           delete i;
	if (proof) delete proof;
}

Source::Source(uint l) : mdl::Source<Source, Sys>(l) { }
Source::~Source() {
	for (auto& node : contents) node.destroy();
}

}} // mdl::smm
