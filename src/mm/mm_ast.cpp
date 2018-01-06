#include <mm_ast.hpp>
#include <mm_sys.hpp>

namespace mdl { namespace mm {

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

Ref::Ref(uint l, const Token& t) : type_(find_type(l)), label_(l) {
	switch (type_) {
	case FLOATING:  val_.flo = new User<Floating>(label_, t);  break;
	case ESSENTIAL: val_.ess = new User<Essential>(label_, t); break;
	case AXIOM:     val_.axm = new User<Axiom>(label_, t);     break;
	case THEOREM:   val_.thm = new User<Theorem>(label_, t);   break;
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

Inclusion::Inclusion(uint src, bool prim, const Token& t) : source(src, t), primary(prim) { }

Source::Source(uint l) : mdl::Source<Source, Sys>(l), block(nullptr) { }

}} // mdl::mm
