#include "rus/ast.hpp"

namespace mdl { namespace rus {

string show(const Comment& c) {
	return string("/*") + c.text + "*/";
}

string show(const Const& c) {
	string s = "constant {\n";
	s += "\tsymbol " + show(c.symb) + " " + END_MARKER + "\n";
	if (!c.ascii.is_undef())
		s += "\tascii " + show(c.ascii) + " " + END_MARKER + "\n";
	if (!c.latex.is_undef())
		s += "\tlatex " + show(c.latex) + " " + END_MARKER + "\n";
	s += "}";
	return s;
}

string show(const Vars& vars) {
	string s;
	for (uint i = 0; i < vars.v.size(); ++ i) {
		Symbol var = vars.v[i];
		s += show(var) + " : " + show_id(var.type->id());
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
		const vector<Symbol>& dis = disj.d[i];
		for (uint j = 0; j < dis.size(); ++ j) {
			Symbol var = dis[j];
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
	s += "type " + show_id(type.id());
	if (type.sup.size() > 0) {
		s += " : ";
		for (uint i = 0; i < type.sup.size(); ++ i) {
			s += show_id(type.sup[i]->id());
			if (i + 1 < type.sup.size()) s += ", ";
		}
	}
	s += END_MARKER;
	return s;
}

string show(const Rule& r) {
	string s;
	s += "rule " + show_id(r.id()) + " ";
	s += "(" + show(r.vars) + ") {\n";
	s += "\tterm : " + show_id(r.type->id()) + " = ";
	s += "# " + show(r.term) + END_MARKER + "\n";
	s += "}";
	return s;
}

inline string show_type(const Expr& ex) {
	return show_id(ex.type->id());
}

string show(const Hyp& h) {
	string s;
	s += "hyp " + to_string(h.ind + 1) + " : ";
	s += show_type(h.expr) + " = ";
	s += "|- " + show(h.expr) + END_MARKER;
	return s;
}

string show(const Prop& p) {
	string s;
	s += "prop " + to_string(p.ind + 1) + " : ";
	s += show_type(p.expr) + " = ";
	s += "|- " + show(p.expr) + END_MARKER;
	return s;
}

string show(const Assertion& a) {
	string s;
	s += show_id(a.id()) + " ";
	s += "(" + show(a.vars) + ") " + show(a.disj) + " {\n";
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
	s += "definition ";
	s += show_id(def.ass.id()) + " ";
	s += "(" + show(def.ass.vars) + ") " + show(def.ass.disj) + " {\n";
	if (def.ass.hyps.size() > 0) {
		for (Hyp* h : def.ass.hyps)
			s += "\t" + show(*h) + "\n";
	}
	s += "\tdefiendum : " + show_id(def.dfm.type->id()) + " ";
	s += "= # " + show(def.dfm) + END_MARKER + "\n";
	s += "\tdefiniens : " + show_id(def.dfs.type->id()) + " ";
	s += "= # " + show(def.dfs) + END_MARKER + "\n";
	s += "\t-----------------------\n";
	s += "\tprop : " + show_id(def.prop.type->id()) + " ";
	s += "= |- " + show(def.prop) + END_MARKER + "\n";
	s += "}";
	return s;
}

string show(const Ref& ref) {
	switch (ref.kind) {
	case Ref::HYP:  return "hyp "  + to_string(ref.val.hyp->ind + 1);
	case Ref::PROP: return "prop " + to_string(ref.val.prop->ind + 1);
	case Ref::STEP: return "step " + to_string(ref.val.step->ind() + 1);
	default : assert(false && "impossible"); return string();
	}
}

static string show_refs(const vector<Ref>& refs) {
	string s = "(";
	for (uint i = 0; i < refs.size(); ++ i) {
		s += show(refs[i]);
		if (i + 1 < refs.size()) s += ", ";
	}
	s += ")";
	return s;
}

string show(const Proof::Elem& el) {
	switch (el.kind) {
	case Proof::Elem::VARS:  return show(*el.val.vars);
	case Proof::Elem::STEP:  return show(*el.val.step);
	case Proof::Elem::QED:   return show(*el.val.qed);
	default : assert(false && "impossible"); break;
	}
	return "";
}

string show(const Step& st) {
	string s = "step " + to_string(st.ind() + 1) + " : ";
	s += show_type(st.expr) + " = ";
	switch (st.kind()) {
	case Step::NONE: s += "? "; break;
	case Step::ASS: {
		switch (st.ass()->kind()) {
		case Assertion::AXM: s += "axm "; break;
		case Assertion::THM: s += "thm "; break;
		case Assertion::DEF: s += "def "; break;
		}
		s += show_id(st.ass()->id()) + " "; break;
	}
	case Step::CLAIM:s += "claim "; break;
	}
	if (st.kind() != Step::NONE)
		s += show_refs(st.refs) + " ";
	s += "|- " + show(st.expr) + END_MARKER;
	if (st.kind() == Step::CLAIM) {
		s += " {\n";
		for (auto& el : st.proof()->elems)
			s += "\t" + show(el) + "\n";
		s += "}";
	}
	return s;
}

string show(const Qed& q) {
	string s = "qed ";
	s += "prop " + to_string(q.prop->ind + 1) + " = ";
	s += "step " + to_string(q.step->ind() + 1) + " " + END_MARKER;
	return s;
}

string show(const Proof& p) {
	string s = "proof ";
	if (p.has_id) s += show_id(p.id) + " ";
	s += "of " + show_id(p.thm->ass.id()) + " {\n";
	if (p.vars.v.size())
		s += "\tvar " + show(p.vars) + END_MARKER + "\n";
	for (auto& st : p.elems)
		s += "\t" + show(st) + "\n";
	s += "}";
	return s;
}

string show(const Import& imp) {
	return string("import ") + imp.source->name() + ".rus" + END_MARKER;
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
	case Node::COMMENT: return show(*n.val.com);
	default : assert(false && "impossible");
	}
	return ""; // pacify the compiler
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
	for (auto& n : c.theory->nodes) {
		s += show(n) + "\n\n";
	}
	return s;
}


void dump(const Const& c)     { cout << show(c) << endl; }
void dump(const Vars& v)      { cout << show(v) << endl; }
void dump(const Disj& d)      { cout << show(d) << endl; }
void dump(const Type& t)      { cout << show(t) << endl; }
void dump(const Rule& r)      { cout << show(r) << endl; }
void dump(const Axiom& a)     { cout << show(a) << endl; }
void dump(const Def& d)       { cout << show(d) << endl; }
void dump(const Assertion& a) { cout << show(a) << endl; }
void dump(const Theorem& t)   { cout << show(t) << endl; }
void dump(const Proof& p)     { cout << show(p) << endl; }
void dump(const Step& s)      { cout << show(s) << endl; }
void dump(const Ref& r)       { cout << show(r) << endl; }
void dump(const Qed& q)       { cout << show(q) << endl; }
void dump(const Hyp& h)       { cout << show(h) << endl; }
void dump(const Prop& p)      { cout << show(p) << endl; }
void dump(const Node& n)      { cout << show(n) << endl; }
void dump(const Import& i)    { cout << show(i) << endl; }
void dump(const Theory& t)    { cout << show(t) << endl; }
void dump(const Source& s)    { cout << show(s) << endl; }
void dump(const Comment& c)   { cout << show(c) << endl; }

}} // mdl::smm
