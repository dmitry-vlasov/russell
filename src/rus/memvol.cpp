#include "rus/ast.hpp"

namespace mdl { namespace rus {

size_t memvol(const Comment& c) {
	return c.text.size();
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
	return memvol(ax.ass);
}
size_t memvol(const Def& df) {
	return memvol(df.ass) + memvol(df.dfm) + memvol(df.dfs) + memvol(df.prop);
}
size_t memvol(const Assertion& ass) {
	size_t s = 0;
	s += memvol(ass.vars);
	s += memvol(ass.disj);
	s += ass.hyps.capacity() * sizeof(Hyp*);
	s += ass.props.capacity() * sizeof(Prop*);
	for (Hyp* h : ass.hyps)
		s += memsize(*h);
	for (Prop* p : ass.props)
		s += memsize(*p);
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
	if (step.kind == Step::CLAIM)
		s += memsize(*step.val.prf);
	return s;
}
size_t memvol(const Proof& proof) {
	size_t s = 0;
	s += memvol(proof.vars);
	s += proof.elems.capacity() * sizeof(Proof::Elem);
	for (auto& e : proof.elems) {
		switch (e.kind) {
		case Proof::Elem::VARS:
			s += memsize(*e.val.vars); break;
		case Proof::Elem::QED:
			s += memsize(*e.val.qed); break;
		case Proof::Elem::STEP:
			s += memsize(*e.val.step); break;
		default: break;
		}
	}
	return s;
}

size_t memvol(const Theorem& th) {
	return memvol(th.ass) + th.proofs.capacity() * sizeof(Proof*);
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
	s += src.data.capacity() * sizeof(char);
	if (src.theory)
		s += memsize(*src.theory);
	return s;
}

}} // mdl::rus
