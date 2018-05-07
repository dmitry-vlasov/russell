#include <mm2_ast.hpp>
#include <mm2_sys.hpp>

namespace mdl { namespace mm2 {

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
		return Ref::UNRESOLVED;
	}
}

Ref::Ref(uint l, const Token& t) : type_(UNRESOLVED), label_(l), token_(t) {
}
Ref::Ref(const Ref& ref) : type_(ref.type_), label_(ref.label_), token_(ref.token_) {
	switch (type_) {
	case FLOATING:  val_.flo = new User<Floating>(label_);  break;
	case ESSENTIAL: val_.ess = new User<Essential>(label_); break;
	case AXIOM:     val_.axm = new User<Axiom>(label_);     break;
	case THEOREM:   val_.thm = new User<Theorem>(label_);   break;
	case UNRESOLVED: break;
	}
}
Ref::~Ref() {
	switch (type()) {
	case FLOATING:  delete val_.flo; break;
	case ESSENTIAL: delete val_.ess; break;
	case AXIOM:     delete val_.axm; break;
	case THEOREM:   delete val_.thm; break;
	case UNRESOLVED: break;
	}
}
void Ref::resolve() {
	if (type_ != UNRESOLVED) return;
	type_ = find_type(label_);
	switch (type_) {
	case FLOATING:  val_.flo = new User<Floating>(label_, token_);  break;
	case ESSENTIAL: val_.ess = new User<Essential>(label_, token_); break;
	case AXIOM:     val_.axm = new User<Axiom>(label_, token_);     break;
	case THEOREM:   val_.thm = new User<Theorem>(label_, token_);   break;
	case UNRESOLVED: throw Error("unknown label", Lex::toStr(label_));
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

}} // mdl::mm2
