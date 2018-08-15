#include "rus_prover_space.hpp"
#include "rus_prover_show.hpp"

namespace mdl { namespace rus { namespace prover {

uint show_bits(string str) {
	uint ret = 0;
	while (str.size()) {
		string::size_type i = str.find(',');
		string s = str.substr(0, str.find(','));
		for (auto p : show_nodes()) {
			if (p.second.str == s) {
				ret += uint(p.second.bit);
				break;
			}
		}
		str = (i == string::npos) ? "" : str.substr(i + 1);
	}
	return ret;
}

string show_bits(uint m) {
	string ret;
	for (auto p : show_nodes()) {
		if (m & uint(p.second.bit)) {
			ret += (ret.size()? "," : "") + p.second.str;
		}
	}
	return ret;
}

bool show_bit(uint m, ShowMode n) {
	return uint(show_nodes().at(n).bit) & m;
}

template<class T>
static string show_children_idx(const vector<unique_ptr<T>>& ch) {
	string ret = "children=\"";
	bool first = true;
	for (const auto& n : ch) {
		if (!first) ret += ",";
		ret += to_string(n.get()->ind);
		first = false;
	}
	return ret + "\" ";
}

static string show_assertion(const Assertion* a) {
	if (const Axiom* ax = dynamic_cast<const Axiom*>(a)) {
		return ax->show();
	} else if (const Theorem* th = dynamic_cast<const Theorem*>(a)) {
		return th->show();
	} else if (const Def* df = dynamic_cast<const Def*>(a)) {
		return df->show();
	} else {
		assert(false && "impossible");
		throw Error("impossible");
	}
}


string Prop::show(bool with_proofs) const {
	string ret;
	ret += "<prop ";
	ret += string("name=\"") + Lex::toStr(prop.id()) + "\" ";
	ret += string("index=\"") + to_string(ind) + "\" ";
	ret += string("parent=\"") + to_string(parent->ind) + "\" ";
	ret += show_children_idx(premises);
	ret += ">\n";
	ret += "\t<assertion>\n";
	ret += "\t<![CDATA[\n";
	ret += Indent::paragraph(show_assertion(prop.ass), "\t\t");
	ret += "\t]]>";
	ret += "\t</assertion>\n";
	ret += "\t<substitution>\n";
	ret += "\t<![CDATA[\n";
	ret += Indent::paragraph(rus::prover::show(sub), "\t\t");
	ret += "\t]]>\n";
	ret += "\t</substitution>\n";
	if (with_proofs) {
		for (const auto& p : proofs) {
			ret += Indent::paragraph(p->show());
		}
	}
	ret += "</prop>\n";
	return ret;
}

string Hyp::show(bool with_proofs) const {
	string ret;
	ret += string("<") + (parent ? "hyp" : "root") + " ";
	ret += string("index=\"") + to_string(ind) + "\" ";
	if (parent) {
		ret += string("parent=\"") + to_string(parent->ind) + "\" ";
	}
	ret += show_children_idx(variants);
	ret += ">\n";
	ret += "\t<expression>";
	ret += "<![CDATA[" + rus::prover::show(expr) + "]]>";
	ret += "</expression>\n";
	if (with_proofs) {
		for (const auto& p : proofs) {
			ret += Indent::paragraph(p->show());
		}
	}
	ret += string("</") + (parent ? "hyp" : "root") + ">\n";
	return ret;
}

string ProofTop::show() const {
	ostringstream oss;
	oss << "<proof expr=\"" << prover::show(apply(sub, node.expr)) << "\" ";
	oss << "index=\"" << ind << "\">\n";
	oss << "\t<![CDATA[";
	oss << "hyp " << hyp.ind + 1;
	oss << "]]>\n";
	oss << "\t<substitution>\n";
	oss << "\t<![CDATA[\n";
	oss << Indent::paragraph(prover::show(sub), "\t\t");
	oss << "\t]]>\n";
	oss << "\t</substitution>\n";
	oss << "</proof>\n";
	return oss.str();
}

string ProofExp::show() const {
	ostringstream oss;
	rus::Step* st = child ? child->step() : nullptr;
	oss << "<proof expr=\"" << (st ? rus::show(st->expr) : prover::show(node.expr)) << "\" ";
	oss << "index=\"" << ind << "\">\n";
	oss << "\t<![CDATA[\n";
	try {
		if (rus::Proof* pr = proof()) {
			oss << Indent::paragraph(pr->show(), "\t\t") << "\n";
			delete pr;
		}
	} catch (Error&) {
		oss << "FAILED PROOF" << endl;
	}
	oss << "]]>\n";
	oss << "\t<substitution>\n";
	oss << "\t<![CDATA[\n";
	oss << Indent::paragraph(prover::show(sub), "\t\t");
	oss << "\t]]>\n";
	oss << "\t</substitution>\n";
	oss << "</proof>\n";
	return oss.str();
}

string ProofProp::show() const {
	ostringstream oss;
	if (rus::Step* st = step()) {
		oss << "<proof expr=\"" << rus::show(st->expr) << "\" ";
		oss << "index=\"" << ind << "\">\n";
		oss << "\t<![CDATA[\n";
		try {
			if (rus::Proof* pr = proof()) {
				oss << Indent::paragraph(pr->show(), "\t\t") << "\n";
				delete pr;
			}
		} catch(Error&) {
			oss << "\tFAILED PROOF" << endl;
		}
		oss << "\t]]>\n";
		oss << "\t<substitution>\n";
		oss << "\t<![CDATA[\n";
		oss << Indent::paragraph(prover::show(sub), "\t\t");
		oss << "\t]]>\n";
		oss << "\t</substitution>\n";
		oss << "</proof>\n";
	} else {
		oss << "UNFINISHED" << endl;
	}
	return oss.str();
}

string showNodeProofs(const Node* n) {
	string data;
	data += "<node index=\"" + to_string(n->ind) + "\">\n";
	data += "\t<proofs>\n";
	if (const Hyp* h = dynamic_cast<const Hyp*>(n)) {
		for (auto& p : h->proofs) {
			data += Indent::paragraph(p->show(), "\t\t");
		}
	} else if (const Prop* pr = dynamic_cast<const Prop*>(n)) {
		for (auto& p : pr->proofs) {
			data += Indent::paragraph(p->show(), "\t\t");
		}
	}
	data += "\t</proofs>\n";
	data += "</node>\n";
	return data;
}

string show_struct(const ProofNode* n) {
	ostringstream oss;
	if (const ProofProp* p = dynamic_cast<const ProofProp*>(n)) {
		oss << "ProofProp(index = " << p->ind << ", node = " << p->node.ind << endl;
		oss << "\tprop = " << Lex::toStr(p->node.prop.id()) << endl;
		oss << "\tsub = " << endl << Indent::paragraph(show(p->sub), "\t\t");
		oss << "\tnode sub = " << endl << Indent::paragraph(show(p->node.sub), "\t\t");
		for (auto h : p->premises) {
			oss << Indent::paragraph(show_struct(h));
		}
		oss << ")" << endl;
	} else if (const ProofTop* t = dynamic_cast<const ProofTop*>(n)) {
		oss << "ProofTop(index = " << t->ind << ", node = " << t->node.ind << endl;
		oss << "\thyp = " << t->hyp.ind << endl;
		oss << "\texp = " << show(t->expr) << endl;
		oss << "\tnode exp = " << show(t->node.expr) << endl;
		oss << "\tsub = " << endl << Indent::paragraph(show(t->sub), "\t\t");
		oss << ")" << endl;
	} else if (const ProofExp* e = dynamic_cast<const ProofExp*>(n)) {
		oss << "ProofExp(index = " << e->ind << ", node = " << e->node.ind << endl;
		oss << "\texp = " << show(e->expr) << endl;
		oss << "\tnode exp = " << show(e->node.expr) << endl;
		oss << "\tsub = " << endl << Indent::paragraph(show(e->sub), "\t\t");
		oss << Indent::paragraph(show_struct(e->child));
		oss << ")" << endl;
	} else {
		oss << "IMPOSSIBLE" << endl;
	}
	return oss.str();
}

}}}
