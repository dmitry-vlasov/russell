#include "smm/ast.hpp"
#include "smm/sys.hpp"

namespace mdl { namespace smm {

Ref::Ref(uint label, bool ax) : type(ax ? AXIOM : THEOREM), val() {
	Sys::mod().math.assertions.use(label, val.ass);
}
Ref::~Ref() {
	if ((type == AXIOM || type == THEOREM) && val.ass)
		Sys::mod().math.assertions.unuse(val.ass->prop.label, val.ass);
	if (type == PROOF && val.prf)
		delete val.prf;
}

Assertion::Assertion(uint label) :
	variables(), disjointed(), essential(),
	floating(), inner(),
	prop(), proof(), loc() {
	Sys::mod().math.assertions.add(label, this);
}
Assertion::~Assertion() {
	Sys::mod().math.assertions.del(prop.label);
	for (Variables* v : variables)   delete v;
	for (Disjointed* d : disjointed) delete d;
	for (Essential* e : essential)   delete e;
	for (Floating* f : floating)     delete f;
	for (Inner* i : inner)           delete i;
	if (proof) delete proof;
}

Source::Source(uint l) : label(l), data(), contents() {
	Sys::mod().math.sources.add(label, this);
}
Source::~Source() {
	Sys::mod().math.sources.del(label);
	for (auto& node : contents) node.destroy();
}
Path Source::rich_path() const {
	return Sys::conf().in.relative(name());
}
void Source::read() {
	rich_path().read(data);
}
void Source::write() {
	rich_path().write(data);
}

}} // mdl::smm
