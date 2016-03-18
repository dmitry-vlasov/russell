#include "rus/globals.hpp"

namespace mdl { namespace rus {

string show(const Const& c) {
	string s = "const {\n";
	s += "\tsymbol " + show(c.symb) + " ;\n";
	if (!c.ascii.undef())
		s += "\tascii " + show(c.ascii) + " ;\n";
	if (!c.latex.undef())
		s += "\tlatex " + show(c.latex) + " ;\n";
	s += "}";
	return s;
}

string show(const Vars& vars) {
	string s;
	for (uint i = 0; i < vars.v.size(); ++ i) {
		Symbol var = vars.v[i];
		s += show(var) + " : " + show_id(var.type->id);
		if (i + 1 < vars.v.size())
			s += ", ";
	}
	return s;
}

string show(const Disj& disj) {
	if (disj.d.size() == 0) return "";
	string s;
	s += "disjointed(";
	for (uint i = 0; i < disj.d.size(); ++ i) {
		const vector<Symbol> dis = disj.d[i];
		for (uint j = 0; j < dis.size(); ++ j) {
			Symbol var = dis[i];
			s += show(var);
			if (j + 1 < dis.size())	s += " ";
		}
		if (i + 1 < disj.d.size())	s += ", ";
	}
	s += ")";
	return s;
}

string show(const Type& type) {
	string s;
	s += "type " + show_id(type.id);
	if (type.sup.size() > 0) {
		s += " : ";
		for (uint i = 0; i < type.sup.size(); ++ i) {
			s += show_id(type.sup[i]->id);
			if (i + 1 < type.sup.size()) s += ", ";
		}
	}
	s += ";";
	return s;
}

string show(const Rule& r) {
	string s;
	s += "rule " + show_id(r.id) + " ";
	s += "(" + show(r.vars) + ") {\n";
	s += "\tterm : " + show_id(r.type->id) + " = ";
	s += "# " + show(r.term) + ";\n";
	s += "}";
	return s;
}

inline string show_type(const Expr& ex) {
	return show_id(ex.term.rule->type->id);
}

string show(const Hyp& h) {
	string s;
	s += "hyp " + to_string(h.ind + 1) + " : ";
	s += show_type(h.expr) + " = ";
	s += "|- " + show(h.expr) + ";";
	return s;
}

string show(const Prop& p) {
	string s;
	s += "prop " + to_string(p.ind + 1) + " : ";
	s += show_type(p.expr) + " = ";
	s += "|- " + show(p.expr) + ";";
	return s;
}

string show(const Assertion& a) {
	string s;
	s += show_id(a.id) + " ";
	s += "(" + show(a.vars) + ") " + show(a.disj) + "{\n";
	if (a.hyps.size() > 0) {
		for (Hyp* h : a.hyps)
			s += "\t" + show(*h) + "\n";
		s += "\t-----------------------\n";
	}
	for (const Prop* p : a.props)
		s += "\t" + show(*p) + "\n";
	s += "}";
	return s;
}

string show(const Axiom& ax) {
	string s;
	s += "axiom " + show(ax.ass);
	return s;
}

string show(const Theorem& thm) {
	string s;
	s += "theorem " + show(thm.ass);
	return s;
}

string show(const Def& def) {
	string s;
	//s += "theorem " + show(thm.ass);
	return s;
}


static string show_refs(const vector<Ref>& refs) {
	string s = "(";
	for (uint i = 0; i < refs.size(); ++ i) {
		Ref r = refs[i];
		switch (r.kind) {
		case Ref::HYP:  s += "hyp "  + to_string(r.val.hyp->ind + 1);  break;
		case Ref::PROP: s += "prop " + to_string(r.val.prop->ind + 1); break;
		case Ref::STEP: s += "step " + to_string(r.val.step->ind + 1); break;
		default : assert(false && "impossible"); break;
		}
		if (i + 1 < refs.size()) s += ", ";
	}
	s += ")";
	return s;
}

string show(const Step& st) {
	string s = "step " + to_string(st.ind + 1) + " : ";
	s += show_type(st.expr) + " = ";
	switch (st.kind) {
	case Step::AX : s += "ax "; break;
	case Step::TH : s += "th "; break;
	case Step::DF : s += "df "; break;
	}
	s += show_id(st.ass->id) + " ";
	s += show_refs(st.refs) + " ";
	s += "|- " + show(st.expr) + ";";
	return s;
}

string show(const Claim& c) {
	string s = "step " + to_string(c.ind + 1) + " : ";
	s += show_type(c.expr) + " = ";
	s += "claim " + show_refs(c.refs) + " ";
	s += "|- " + show(c.expr) + "; {\n";
	for (auto& st : c.proof.steps)
		s += "\t" + show(st) + "\n";
	s += "}";
	return s;
}

string show(const Qed& q) {
	string s = "qed ";
	s += "prop " + to_string(q.prop->ind + 1) + " = ";
	s += "step " + to_string(q.step->ind + 1) + " ;";
	return s;
}

string show(const Ref& ref) {
	switch (ref.kind) {
	case Ref::STEP:  return show(*ref.val.step);
	case Ref::CLAIM: return show(*ref.val.claim);
	case Ref::QED:   return show(*ref.val.qed);
	default : assert(false && "impossible"); break;
	}
	return "";
}

string show(const Proof& p) {
	string s = "proof ";
	if (p.id != (uint)-1) s += show_id(p.id) + " ";
	s += "of " + show_id(p.theorem->id) + " {\n";
	for (auto& st : p.steps)
		s += "\t" + show(st) + "\n";
	s += "}";
	return s;
}

string show(const Import& imp) {
	string s;
	//s += "theorem " + show(thm.ass);
	return s;
}

string show(const Node& n) {
	switch (n.kind) {
	case Node::CONST:   return show(*n.val.cst);
	case Node::TYPE:    return show(*n.val.tp);
	case Node::RULE:    return show(*n.val.rul);
	case Node::AXIOM:   return show(*n.val.ax);
	case Node::DEF:     return show(*n.val.def);
	case Node::THEOREM: return show(*n.val.thm);
	case Node::PROOF:   return show(*n.val.prf);
	case Node::THEORY:  return show(*n.val.thy);
	case Node::IMPORT:  return show(*n.val.imp);
	default : assert(false && "impossible");
	}
	return ""; // pacify the compiler
}

static int depth(const Theory& thy) {
	int d = 0;
	Theory* p = thy.parent;
	while (p) { ++ d; p = p->parent; }
	return d;
}

string show(const Theory& thy) {
	string s = "theory " + show_id(thy.id) + "{";
	for (auto& n : thy.nodes) {
		//s += indent::paragraph("\n" + show(n));
		s += show(n) + "\n\n";
	}
	s += "}";
	return s;
}

string show(const Source& c) {
	string s;
	for (auto& n : c.theory.nodes) {
		s += show(n) + "\n\n";
	}
	return s;
}

}} // mdl::smm
