#include <rus_ast.hpp>

namespace mdl { namespace rus {

void Step::verify() const {
	if (kind() == Step::CLAIM) {
		claim()->verify();
		return;
	}
	//static int c = 0;
	//cout << "\tverifying step: " << c++ << " = " << show_id(ass->id) << endl;
	Substitution ps = unify_forth(ass()->props[0]->expr, expr);
	if (!ps) {
		string msg = "proposition:\n";
		msg += show(*ass()->props[0]) + "\n";
		msg += "ref expr:\n";
		msg += show(ass()->props[0]->expr) + "\n";
		msg += show_ast(ass()->props[0]->expr, true) + "\n\n";
		msg += "step:\n";
		msg += show(*this) + "\n";
		msg += show_ast(expr, true) + "\n\n";
		msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
		throw Error("proposition unification failed", msg);
	}
	for (uint i = 0; i < ass()->arity(); ++ i) {
		Substitution hs = unify_forth(ass()->hyps[i]->expr, refs[i]->expr());
		if (!hs) {
			string msg = "\nhypothesis:\n";
			msg += show(*ass()->hyps[i]) + "\n";
			msg += "ref expr:\n";
			msg += show(refs[i]->expr()) + "\n\n";
			msg += "step:\n";
			msg += show(*this) + "\n\n";
			msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
			msg += "substitution:\n" + show(ps) + "\n";
			throw Error("hypothesis unification failed", msg);
		}
		if (!ps.join(hs)) {
			string msg = "\nhypothesis:\n";
			msg += show(*ass()->hyps[i]) + "\n";
			msg += "ref expr:\n";
			msg += show(refs[i]->expr()) + "\n\n";
			msg += "step:\n";
			msg += show(*this) + "\n\n";
			msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
			msg += "prop substitution:\n" + show(ps) + "\n";
			msg += "hyp substitution:\n" + show(hs) + "\n";
			throw Error("substitution join failed", msg);
		}
	}
}

void Qed::verify() const {
	if (prop->expr != step->expr)
		throw Error("qed prop doesn't match qed step", show(prop->expr) + " != " + show(step->expr));
}

void Proof::verify() const {
	for (auto el : elems) {
		switch (el.kind){
		case Proof::Elem::STEP: el.val.step->verify(); break;
		case Proof::Elem::QED:  el.val.qed->verify();  break;
		default : break;
		}
	}
}

void Theory::verify() const {
	for (auto n : nodes) {
		switch (n.kind) {
		case Node::THEORY: n.val.thy->verify(); break;
		case Node::IMPORT: {
			const Import* imp = n.val.imp;
			if (imp->primary) imp->source.get()->theory->verify();
			break;
		}
		case Node::THEOREM: {
			const Theorem* t = n.val.thm;
			if (!t->proofs.size()) throw Error("Theorem has no proof", show_id(t->id()));
			for (const User<Proof>& p : t->proofs) p.get()->verify();
			break;
		}
		default: break;
		}
	}
}

void verify(uint src) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	source->theory->verify();
}

void verify() {
	for (const auto& a : Sys::mod().math.get<Assertion>()) {
		if (const Theorem* t = dynamic_cast<const Theorem*>(a.second.data)) {
			if (!t->proofs.size()) throw Error("Theorem is not proved", show_id(t->id()));
			for (const User<Proof>& p : t->proofs) p.get()->verify();
		}
	}
}

}} // mdl::rus
