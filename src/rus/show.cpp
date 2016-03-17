#include "rus/globals.hpp"

namespace mdl { namespace rus {

string show(uint id) {
	return Rus::get().lex.ids.toStr(id);
}

string show(const Const& c) {
	string s;
	s += "const {\n";
	s += "\tsymb " + show(c.symb) + "\n";
	if (!c.ascii.undef())
		s += "\tascii " + show(c.ascii) + "\n";
	if (!c.latex.undef())
		s += "\tlatex " + show(c.latex) + "\n";
	s += "}";
	return s;
}

string show(const Vars& vars) {
	string s;
	for (uint i = 0; i < vars.v.size(); ++ i) {
		Symbol var = vars.v[i];
		s += show(var) + " : " + show(var.type->name);
		if (i + 1 < vars.v.size())
			s += ", ";
	}
	return s;
}

string show(const Disj& disj) {
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
	s += "type " + show(type.name);
	if (type.super.size() > 0) {
		s += " : ";
		for (uint i = 0; i < type.super.size(); ++ i) {
			s += show(type.super[i]->name);
			if (i + 1 < type.super.size()) s += ", ";
		}
	}
	s += ";";
	return s;
}

string show(const Rule& r) {
	string s;
	s += "rule " + show(r.name) + " ";
	s += "(" + show(r.vars) + ") {\n";
	s += "\tterm : " + show(r.type->name) + " = ";
	s += "# " + show(r.term) + ";\n";
	s += "}";
	return s;
}

inline string show_type(const Expr& ex) {
	return show(ex.term.rule->type->name);
}

string show(const Hyp& h) {
	string s;
	s += "hyp " + to_string(h.index) + " : ";
	s += show_type(h.expr) + " = ";
	s += "|- " + show(h.expr) + ";";
	return s;
}

string show(const Prop& p) {
	string s;
	s += "prop " + to_string(p.index) + " : ";
	s += show_type(p.expr) + " = ";
	s += "|- " + show(p.expr) + ";";
	return s;
}

string show(const Assertion& a) {
	string s;
	s += show(a.id) + " ";
	s += show(a.vars) + " " + show(a.disj) + "{\n";
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

string show(const Theorem& th) {
	string s;
	s += "theorem " + show(th.ass);
	return s;
}



}} // mdl::smm
