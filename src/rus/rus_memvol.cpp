#include <rus_ast.hpp>

namespace mdl { namespace rus {

size_t memvol(const Symbol& s) {
	return 0;
}
size_t memvol(const Tree& tree) {
	if (const RuleTree* rule_tree = dynamic_cast<const RuleTree*>(&tree)) {
		size_t vol = 0;
		vol += rule_tree->children.capacity();
		for (auto& ch : rule_tree->children) {
			vol += memvol(*ch);
		}
		return vol;
	} else if (const VarTree* var_tree = dynamic_cast<const VarTree*>(&tree)) {
		return 0;
	} else {
		throw Error("impossible");
	}
}

size_t memvol(const Rules& rt) {
	size_t vol = 0;
	vol += rt.nodes.capacity() * sizeof (Rules::Node);
	for (auto& p : rt.nodes) {
		vol += memvol(p.get()->tree);
	}
	return vol;
}

size_t memvol(const Expr& ex) {
	size_t s = 0;
	s += ex.symbols.capacity() * sizeof(Symbols);
	if (ex.tree()) {
		s += memvol(*ex.tree());
	}
	return s;
}



size_t memvol(const Comment& c) {
	return c.text.capacity();
}
size_t memvol(const Constant& c) {
	return 0;
}
size_t memvol(const Vars& vars) {
	return vars.v.capacity() * sizeof(Symbol);
}
size_t memvol(const Disj& disj) {
	return disj.dvars.size() * sizeof(Disj::Pair);
}
size_t memvol(const Type& type) {
	size_t s = 0;
	s += type.sup.capacity() * sizeof(Type*);
	s += memvol(type.rules);
	s += type.supers.size() * sizeof(pair<Type*, Rule*>);
	for (auto& p : type.supers) {
		s += memsize(*(p.second.get()));
	}
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
size_t memvol(const Theory::Node& n) {
	switch (Theory::kind(n)) {
	case Theory::CONSTANT: return memvol(*Theory::constant(n));
	case Theory::TYPE    : return memvol(*Theory::type(n));
	case Theory::RULE    : return memvol(*Theory::rule(n));
	case Theory::AXIOM   : return memvol(*Theory::axiom(n));
	case Theory::DEF     : return memvol(*Theory::def(n));
	case Theory::THEOREM : return memvol(*Theory::theorem(n));
	case Theory::PROOF   : return memvol(*Theory::proof(n));
	case Theory::THEORY  : return memvol(*Theory::theory(n));
	case Theory::IMPORT  : return memvol(*Theory::import(n));
	case Theory::COMMENT : return memvol(*Theory::comment(n));
	default: return 0;
	}
}

size_t memvol(const Theory& th) {
	size_t s = 0;
	s += th.nodes.capacity() * sizeof(Theory::Node);
	for (const Theory::Node& n : th.nodes)
		s += memvol(n);
	return s;
}
size_t memvol(const Source& src) {
	size_t s = 0;
	s += src.data().capacity() * sizeof(char);
	s += memsize(src.theory);
	return s;
}

}} // mdl::rus
