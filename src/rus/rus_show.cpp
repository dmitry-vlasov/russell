#include <rus_ast.hpp>

namespace mdl { namespace rus {

static vector<string> show_lines(const Rules& tr) {
	vector<string> vect;
	for (const auto& n : tr.nodes) {
		const Rules::Node* p = n.get();
		vector<string> v = show_lines(p->tree);
		if (p->tree.nodes.size()) {
			for (string& s : v)
				vect.push_back(show(p->symb) + ' ' + s);
		} else {
			vect.push_back(show(p->symb) + " --> " +
				(p->rule ? show(*p->rule.get()) : "null")
			);
		}
	}
	return vect;
}

string show(const Rules& tr) {
	string str;
	for (string& s : show_lines(tr)) {
		str += s + "\n";
	}
	return str;
}

string show(Symbol s, bool full) {
	if (!full || s.kind() == Symbol::CONST)
		return Lex::toStr(s.lit);
	else {
		return string("<") + Lex::toStr(s.lit) + ":" + show_id(s.type()->id()) + ">";
	}
}

string show(const Expr& ex) {
	string str;
	for (const auto& s : ex.symbols) str += Lex::toStr(s.lit) + " ";
	return str;
}

void Comment::write(ostream& os, const Indent& i) const {
	if (multiline) {
		os << i << "/* " << text << " */\n";
	} else {
		os << i << "// " << text << " \n";
	}
}

void Const::write(ostream& os, const Indent& i) const {
	os << i << "constant {\n";
	os << i + 1 << "symbol " << Lex::toStr(symb) << " " << END_MARKER << "\n";
	if (ascii != -1) {
		os << i + 1 << "ascii " << Lex::toStr(ascii) << " " << END_MARKER << "\n";
	}
	if (latex != -1) {
		os << i + 1 << "latex " << Lex::toStr(latex) << " " << END_MARKER << "\n";
	}
	os << i << "}\n";
}

void Vars::write(ostream& os, const Indent&) const {
	for (uint i = 0; i < v.size(); ++ i) {
		os << Lex::toStr(v.at(i).lit) << " : " << Lex::toStr(v.at(i).type_id());
		if (i + 1 < v.size()) os << ", ";
	}
}

void Disj::write(ostream& os, const Indent&) const {
	Disj::Vector d = toVector();
	if (d.size() == 0) return;
	os << "disjointed(";
	for (uint i = 0; i < d.size(); ++ i) {
		const set<uint>& dis = *d[i];
		uint j = 0;
		for (uint v : dis) {
			os << Lex::toStr(v);
			if (++j < dis.size())	os << " ";
		}
		if (i + 1 < d.size()) os << ", ";
	}
	os << ")";
}

void Type::write(ostream& os, const Indent& i) const {
	os << i << "type " << Lex::toStr(id());
	if (sup.size() > 0) {
		os << " : ";
		for (uint i = 0; i < sup.size(); ++ i) {
			os << Lex::toStr(sup[i].id());
			if (i + 1 < sup.size()) os << ", ";
		}
	}
	os << END_MARKER << "\n";
}

void Rule::write(ostream& os, const Indent& i) const {
	os << i << "rule " << Lex::toStr(id()) << " ";
	os << "("; vars.write(os); os << ") {\n";
	os << i + 1 << "term : " << Lex::toStr(term.type.id()) << " = ";
	os << "# " << term << END_MARKER << "\n";
	os << i << "}\n";
}

void Hyp::write(ostream& os, const Indent& i) const {
	os << i << "hyp " << (ind + 1) << " : ";
	os << Lex::toStr(expr.type.id()) << " = |- " << expr << END_MARKER << "\n";
}

void Prop::write(ostream& os, const Indent& i) const {
	os << i << "prop " << (ind + 1) << " : ";
	os << Lex::toStr(expr.type.id()) << " = |- " << expr << END_MARKER << "\n";
}

void Assertion::write(ostream& os, const Indent& i) const {
	os << Lex::toStr(id()) << " ";
	os << "("; vars.write(os); os << ") "; disj.write(os); os << " {\n";
	if (hyps.size() > 0) {
		for (const auto& h : hyps) {
			h.get()->write(os, i + 1);
		}
		os << i + 1 << "-----------------------\n";
	}
	for (auto& p : props) {
		p.get()->write(os, i + 1);
	}
	os << i << "}\n";
}

void Def::write(ostream& os, const Indent& i) const {
	os << i << "definition " << Lex::toStr(id()) << " ";
	os << "("; vars.write(os); os << ") "; disj.write(os); os << " {\n";
	for (const auto& h : hyps) {
		h.get()->write(os, i + 1);
	}
	os << i + 1 << "defiendum : " << Lex::toStr(dfm.type.id()) << " ";
	os << "= # " << dfm << END_MARKER << "\n";
	os << i + 1 << "definiens : " << Lex::toStr(dfs.type.id()) << " ";
	os << "= # " << dfs << END_MARKER << "\n";
	os << i + 1 << "-----------------------\n";
	os << i + 1 << "prop : " << Lex::toStr(prop.type.id()) << " ";
	os << "= |- " << prop << END_MARKER << "\n";
	os << i << "}\n";
}

void Axiom::write(ostream& os, const Indent& i) const {
	os << i << "axiom "; Assertion::write(os, i);
}

void Theorem::write(ostream& os, const Indent& i) const {
	os << i << "theorem "; Assertion::write(os, i);
}

void Ref::write(ostream& os, const Indent& i) const {
	switch (kind()) {
		case Ref::HYP:  os << "hyp " << (hyp()->ind + 1);     break;
		case Ref::PROP: os << "prop " << (prop()->ind + 1);   break;
		case Ref::STEP: os << "step " << (step()->ind() + 1); break;
		default : assert(false && "impossible");
	}
}

void Qed::write(ostream& os, const Indent& i) const {
	os << i << "qed prop " << (prop->ind + 1) << " = ";
	os << "step " << (step->ind() + 1) << " " << END_MARKER << "\n";
}

void Proof::write(ostream& os, const Indent& i) const {
	os << i << "proof ";
	if (!inner) {
		const string& name = Lex::toStr(id());
		if (name.size() > 1 && name[0] != '_') {
			os << name << " ";
		}
		os << "of " << Lex::toStr(thm.id()) << " ";
	}
	os << "{\n";
	if (allvars.v.size()) {
		os << i + 1 << "var ";
		allvars.write(os, i + 1);
		os << END_MARKER << "\n";
	}
	for (const auto& e : elems) {
		switch (kind(e)) {
		case VARS: vars(e)->write(os, i + 1); break;
		case STEP: step(e)->write(os, i + 1); break;
		case QED: qed(e)->write(os, i + 1); break;
		}
	}
	os << "}\n";
}

void Step::write(ostream& os, const Indent& i) const {
	os << i << "step " << (ind_ + 1) << " : ";
	os << Lex::toStr(expr.type.id()) << " = ";
	bool undef = (kind() == ASS) && (ass_id() == -1);
	switch (kind()) {
	case CLAIM: os << "claim "; break;
	case ASS:   os << (undef ? "? " : Lex::toStr(ass_id())) << " "; break;
	}
	if (!undef) {
		os << "(";
		for (uint i = 0; i < refs.size(); ++ i) {
			refs[i]->write(os);
			if (i + 1 < refs.size()) os << ", ";
		}
		os << ") ";
	}
	os << "|- " << expr << END_MARKER;
	if (kind() == Step::CLAIM) {
		os << " "; claim()->write(os, i + 1);
	} else {
		os << "\n";
	}
}

void Import::write(ostream& os, const Indent& i) const {
	os << i << "import " << Lex::toStr(source.id()) << ".rus" << END_MARKER << "\n";
}

static void write_node(ostream& os, const Indent& i, const Theory::Node& n) {
	switch(Theory::kind(n)) {
	case Theory::CONST:   Theory::const_(n)->write(os, i); break;
	case Theory::TYPE:    Theory::type(n)->write(os, i);  break;
	case Theory::RULE:    Theory::rule(n)->write(os, i); break;
	case Theory::AXIOM:   Theory::axiom(n)->write(os, i);  break;
	case Theory::DEF:     Theory::def(n)->write(os, i); break;
	case Theory::THEOREM: Theory::theorem(n)->write(os, i); break;
	case Theory::PROOF:   Theory::proof(n)->write(os, i); break;
	case Theory::THEORY:  Theory::theory(n)->write(os, i); break;
	case Theory::IMPORT:  Theory::import(n)->write(os, i); break;
	case Theory::COMMENT: Theory::comment(n)->write(os, i); break;
	default : assert(false && "impossible"); break;
	}
}

void Theory::write(ostream& os, const Indent& i) const {
	os << i << "theory " << Lex::toStr(id) << " {";
	for (const auto& n : nodes) {
		write_node(os, i + 1, n);
	}
	os << "}\n";
}

void Source::write(ostream& os, const Indent& i) const {
	for (const auto& n : theory.nodes) {
		write_node(os, i + 1, n);
	}
}

}} // mdl::smm
