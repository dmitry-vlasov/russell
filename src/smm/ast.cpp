#include "smm/ast.hpp"

namespace mdl { namespace smm {

Ref::Ref(uint label, bool ax) : type_(ax ? AXIOM : THEOREM) {
	val_.ass = new User<Assertion>(label);
}
Ref::Ref(const Ref& ref) : type_(ref.type_) {
	switch (type_) {
	case INNER:     val_.inn = ref.val_.inn; break;
	case FLOATING:  val_.flo = ref.val_.flo; break;
	case ESSENTIAL: val_.ess = ref.val_.ess; break;
	case AXIOM:     // intentionally left blank
	case THEOREM:   val_.ass = new User<Assertion>(ref.label());
	}
}
Ref::~Ref() { if (is_assertion()) delete val_.ass; }

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
