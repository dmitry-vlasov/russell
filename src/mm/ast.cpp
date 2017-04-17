#include "mm/ast.hpp"
#include "mm/sys.hpp"

namespace mdl { namespace mm {

//Constants::Constants(const Vect& ex) : expr(ex) { }

Ref::Type Ref::type(uint label) {
	Sys::Math& math = Sys::mod().math;
	if (math.get<Floating>().has(label)) {
		return FLOATING;
	} else if (math.get<Essential>().has(label)) {
		return ESSENTIAL;
	} else if (math.get<Axiom>().has(label)) {
		return AXIOM;
	} else if (math.get<Theorem>().has(label)) {
		return THEOREM;
	} else {
		throw Error("unknown label", Lex::toStr(label));
	}
}

Ref::Ref(uint l) : label_(l) {
	switch (type(label_)) {
	case FLOATING:  val = new User<Floating>(label_);  break;
	case ESSENTIAL: val = new User<Essential>(label_); break;
	case AXIOM:     val = new User<Axiom>(label_);     break;
	case THEOREM:   val = new User<Theorem>(label_);   break;
	}
}
Ref::Ref(const Ref& ref) : label_(ref.label_) {
	switch (ref.type()) {
	case FLOATING:  val = new User<Floating>(label_);  break;
	case ESSENTIAL: val = new User<Essential>(label_); break;
	case AXIOM:     val = new User<Axiom>(label_);     break;
	case THEOREM:   val = new User<Theorem>(label_);   break;
	}
}
Ref::~Ref() {
	switch (type()) {
	case FLOATING:  delete std::get<User<Floating>*>(val);  break;
	case ESSENTIAL: delete std::get<User<Essential>*>(val); break;
	case AXIOM:     delete std::get<User<Axiom>*>(val);     break;
	case THEOREM:   delete std::get<User<Theorem>*>(val);   break;
	}
}

Theorem::~Theorem() { delete proof; }

Proof::Proof(const vector<Ref*>& r) : refs(r) { }
Proof::Proof(vector<Ref*>&& r) : refs(std::move(r)) { }
Proof::~Proof() {
	for (auto r : refs) delete r;
}

Inclusion::Inclusion(Source* src, bool prim) : source(nullptr), primary(prim) {
	if (src) Sys::mod().math.get<Source>().use(src->id(), source);
}
Inclusion::~Inclusion() {
	if (source) Sys::mod().math.get<Source>().unuse(source->id(), source);
}


Source::Source(uint l) : mdl::Source<Source, Sys>(l), block(nullptr) { }

}} // mdl::mm
