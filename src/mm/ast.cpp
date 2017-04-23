#include "mm/ast.hpp"
#include "mm/sys.hpp"

namespace mdl { namespace mm {

//Constants::Constants(const Vect& ex) : expr(ex) { }

inline Ref::Type find_type(uint label) {
	Sys::Math& math = Sys::mod().math;
	if (math.get<Floating>().has(label)) {
		return Ref::FLOATING;
	} else if (math.get<Essential>().has(label)) {
		return Ref::ESSENTIAL;
	} else if (math.get<Axiom>().has(label)) {
		return Ref::AXIOM;
	} else if (math.get<Theorem>().has(label)) {
		return Ref::THEOREM;
	} else {
		throw Error("unknown label", Lex::toStr(label));
	}
}

Ref::Ref(uint l) : type_(find_type(l)), label_(l) {
	switch (type_) {
	case FLOATING:  val_.flo = new User<Floating>(label_);  break;
	case ESSENTIAL: val_.ess = new User<Essential>(label_); break;
	case AXIOM:     val_.axm = new User<Axiom>(label_);     break;
	case THEOREM:   val_.thm = new User<Theorem>(label_);   break;
	}
}
Ref::Ref(const Ref& ref) : type_(ref.type_), label_(ref.label_) {
	switch (type_) {
	case FLOATING:  val_.flo = new User<Floating>(label_);  break;
	case ESSENTIAL: val_.ess = new User<Essential>(label_); break;
	case AXIOM:     val_.axm = new User<Axiom>(label_);     break;
	case THEOREM:   val_.thm = new User<Theorem>(label_);   break;
	}
}
Ref::~Ref() {
	switch (type()) {
	case FLOATING:  delete val_.flo; break;
	case ESSENTIAL: delete val_.ess; break;
	case AXIOM:     delete val_.axm; break;
	case THEOREM:   delete val_.thm; break;
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
