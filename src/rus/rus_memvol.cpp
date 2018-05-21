#include <rus_ast.hpp>

namespace mdl { namespace rus {

size_t memvol(const Symbol& s) {
	return 0;
}
size_t memvol(const Tree& t) {
	if (t.kind != Tree::NODE) return 0;
	size_t vol = 0;
	vol += t.children().capacity();
	for (auto& ch : t.children())
		vol += memvol(*ch.get());
	return vol;
}

size_t memvol(const Rules& rt) {
	size_t vol = 0;
	vol += rt.map.capacity() * sizeof (Rules::Node);
	for (auto p : rt.map) {
		vol += memvol(p->tree);
	}
	return vol;
}

size_t memvol(const Expr& ex) {
	size_t s = 0;
	s += ex.symbols.capacity() * sizeof(Symbols);
	s += memvol(ex.tree);
	return s;
}



size_t memvol(const Comment& c) {
	return c.text.capacity();
}
size_t memvol(const Const& c) {
	return 0;
}
size_t memvol(const Vars& vars) {
	return vars.v.capacity() * sizeof(Symbol);
}
size_t memvol(const Disj& disj) {
	size_t s = 0;
	for (auto& d : disj.d)
		s += d.capacity() * sizeof(Symbol);
	return s;
}
size_t memvol(const Type& type) {
	size_t s = 0;
	s += type.sup.capacity() * sizeof(Type*);
	s += memvol(type.rules);
	s += type.supers.size() * sizeof(pair<Type*, Rule*>);
	for (auto p : type.supers)
		s += memsize(*p.second);
	return s;
}
size_t memvol(const Rule& rule) {
	return sizeof(Rule) + memvol(rule.vars) + memvol(rule.term);
}
size_t memvol(const Hyp& hyp) {
	return memvol(hyp.expr);
}
size_t memvol(const Prop& prop) {
	return memvol(prop.expr);
}
size_t memvol(const Axiom& ax) {
	return memvol(ax);
}
size_t memvol(const Def& df) {
	return memvol(static_cast<const Assertion&>(df)) + memvol(df.dfm) + memvol(df.dfs) + memvol(df.prop);
}
size_t memvol(const Assertion& ass) {
	size_t s = 0;
	s += memvol(ass.vars);
	s += memvol(ass.disj);
	s += ass.hyps.capacity() * sizeof(Hyp*);
	s += ass.props.capacity() * sizeof(Prop*);
	for (auto& h : ass.hyps)
		s += memsize(*h.get());
	for (auto& p : ass.props)
		s += memsize(*p.get());
	return s;
}
size_t memvol(const Ref& ref) {
	return 0;
}
size_t memvol(const Qed& qed) {
	return 0;
}
size_t memvol(const Step& step) {
	size_t s = 0;
	s += memvol(step.expr);
	s += step.refs.capacity() * sizeof(Ref);
	if (step.kind() == Step::CLAIM)
		s += memsize(*step.proof());
	return s;
}
size_t memvol(const Proof& proof) {
	size_t s = 0;
	s += memvol(proof.vars);
	s += proof.elems.capacity() * sizeof(Proof::Elem);
	for (const auto& e : proof.elems) {
		switch (Proof::kind(e)) {
		case Proof::VARS: s += memsize(*Proof::vars(e)); break;
		case Proof::QED:  s += memsize(*Proof::qed(e));  break;
		case Proof::STEP: s += memsize(*Proof::step(e)); break;
		default: break;
		}
	}
	return s;
}

size_t memvol(const Theorem& th) {
	return memvol(static_cast<const Assertion&>(th)) + th.proofs.capacity() * sizeof(Proof*);
}
size_t memvol(const Import& imp) {
	return 0;
}
size_t memvol(const Node& n) {
	switch (n.kind) {
	case Node::CONST   : return memvol(*n.val.cst);
	case Node::TYPE    : return memvol(*n.val.tp);
	case Node::RULE    : return memvol(*n.val.rul);
	case Node::AXIOM   : return memvol(*n.val.ax);
	case Node::DEF     : return memvol(*n.val.def);
	case Node::THEOREM : return memvol(*n.val.thm);
	case Node::PROOF   : return memvol(*n.val.prf);
	case Node::THEORY  : return memvol(*n.val.thy);
	case Node::IMPORT  : return memvol(*n.val.imp);
	default: return 0;
	}
}

size_t memvol(const Theory& th) {
	size_t s = 0;
	s += th.nodes.capacity() * sizeof(Node);
	for (const Node& n : th.nodes)
		s += memvol(n);
	return s;
}
size_t memvol(const Source& src) {
	size_t s = 0;
	s += src.data().capacity() * sizeof(char);
	if (src.theory)
		s += memsize(*src.theory);
	return s;
}

}} // mdl::rus
