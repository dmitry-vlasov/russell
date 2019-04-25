#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

template<class T>
static string show_children_idx(const vector<unique_ptr<T>>& ch) {
	ostringstream oss;
	oss << "children=\"";
	bool first = true;
	for (const auto& n : ch) {
		if (!first) {
			oss << ",";
		}
		oss << to_string(n.get()->ind);
		first = false;
	}
	oss << "\" ";
	return oss.str();
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
	ostringstream oss;
	oss << "<prop ";
	oss << string("name=\"") << Lex::toStr(prop.id()) << "\" ";
	oss << string("index=\"") << ind << "\" ";
	oss << string("parent=\"") << parent->ind << "\" ";
	oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
	oss << show_children_idx(premises);
	oss << ">\n";
	oss << "\t<assertion>\n";
	oss << "\t<![CDATA[\n";
	oss << Indent::paragraph(show_assertion(prop.ass), "\t\t");
	oss << "\t]]>";
	oss << "\t</assertion>\n";
	oss << "\t<substitution>\n";
	oss << "\t<![CDATA[\n";
	oss << Indent::paragraph(sub.show(), "\t\t");
	oss << "\t]]>\n";
	oss << "\t</substitution>\n";
	if (with_proofs) {
		for (const auto& p : proofs) {
			oss << Indent::paragraph(p->show());
		}
	}
	oss << "</prop>\n";
	return oss.str();
}

string Hyp::show(bool with_proofs) const {
	ostringstream oss;
	oss << string("<") << (parent ? "hyp" : "root") << " ";
	oss << string("index=\"") << ind << "\" ";
	oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
	if (parent) {
		oss << string("parent=\"") << parent->ind << "\" ";
	}
	oss << show_children_idx(variants);
	oss << ">\n";
	oss << "\t<expression>";
	oss << "<![CDATA[" << expr.show() << "]]>";
	oss << "</expression>\n";
	if (with_proofs) {
		for (const auto& p : proofs) {
			oss << Indent::paragraph(p->show());
		}
	}
	oss << string("</") << (parent ? "hyp" : "root") << ">\n";
	return oss.str();
}

string ProofTop::show() const {
	ostringstream oss;
	oss << "<proof expr=\"" << sub.apply(node.expr).show() << "\" ";
	oss << "index=\"" << ind << "\" ";
	oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
	oss << ">\n";
	oss << "\t<![CDATA[";
	oss << "hyp " << hyp.ind + 1;
	oss << "]]>\n";
	oss << "\t<substitution>\n";
	oss << "\t<![CDATA[\n";
	oss << Indent::paragraph(sub.show(), "\t\t");
	oss << "\t]]>\n";
	oss << "\t</substitution>\n";
	oss << "</proof>\n";
	return oss.str();
}

string ProofExp::show() const {
	ostringstream oss;
	rus::Step* st = child ? child->step() : nullptr;
	oss << "<proof expr=\"" << (st ? st->expr.show() : node.expr.show()) << "\" ";
	oss << "index=\"" << ind << "\" ";
	oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
	oss << ">\n";
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
	oss << Indent::paragraph(sub.show(), "\t\t");
	oss << "\t]]>\n";
	oss << "\t</substitution>\n";
	oss << "</proof>\n";
	return oss.str();
}

string ProofProp::show() const {
	ostringstream oss;
	if (rus::Step* st = step()) {
		oss << "<proof expr=\"" << st->expr << "\" ";
		oss << "index=\"" << ind << "\" ";
		oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
		oss << ">\n";
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
		oss << Indent::paragraph(sub.show(), "\t\t");
		oss << "\t]]>\n";
		oss << "\t</substitution>\n";
		oss << "</proof>\n";
	} else {
		oss << "UNFINISHED" << endl;
	}
	return oss.str();
}

constexpr uint PROOF_SHOW_LIMIT = 8;

string showNodeProofs(const Node* n, uint limit) {
	string data;
	data += "<node index=\"" + to_string(n->ind) + "\">\n";
	data += "\t<proofs>\n";
	uint counter = 0;
	if (const Hyp* h = dynamic_cast<const Hyp*>(n)) {
		for (auto& p : h->proofs) {
			data += Indent::paragraph(p->show(), "\t\t");
			if (++counter > limit) break;
		}
	} else if (const Prop* pr = dynamic_cast<const Prop*>(n)) {
		for (auto& p : pr->proofs) {
			data += Indent::paragraph(p->show(), "\t\t");
			if (++counter > limit) break;
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
		oss << "\tsub = " << endl << Indent::paragraph(p->sub.show(), "\t\t");
		oss << "\tnode sub = " << endl << Indent::paragraph(p->node.sub.show(), "\t\t");
		for (auto h : p->premises) {
			oss << Indent::paragraph(show_struct(h));
		}
		oss << ")" << endl;
	} else if (const ProofTop* t = dynamic_cast<const ProofTop*>(n)) {
		oss << "ProofTop(index = " << t->ind << ", node = " << t->node.ind << endl;
		oss << "\thyp = " << t->hyp.ind << endl;
		oss << "\texp = " << t->expr.show() << endl;
		oss << "\tnode exp = " << t->node.expr.show() << endl;
		oss << "\tsub = " << endl << Indent::paragraph(t->sub.show(), "\t\t");
		oss << ")" << endl;
	} else if (const ProofExp* e = dynamic_cast<const ProofExp*>(n)) {
		oss << "ProofExp(index = " << e->ind << ", node = " << e->node.ind << endl;
		oss << "\texp = " << e->expr.show() << endl;
		oss << "\tnode exp = " << e->node.expr.show() << endl;
		oss << "\tsub = " << endl << Indent::paragraph(e->sub.show(), "\t\t");
		oss << Indent::paragraph(show_struct(e->child));
		oss << ")" << endl;
	} else {
		oss << "IMPOSSIBLE" << endl;
	}
	return oss.str();
}

string show(const set<uint>& s) {
	string ret;
	ret += "{";
	for (uint i : s) {
		ret += to_string(i) + ", ";
	}
	ret += "}";
	return ret;
}

string show(const vector<uint>& v) {
	string ret;
	ret += "(";
	for (uint i : v) {
		ret += to_string(i) + ", ";
	}
	ret += ")";
	return ret;
}

string show(const vector<bool>& v) {
	string ret;
	ret += "(";
	if (v.size()) {
		ret += v[0] ? "T" : "_|_";
		for (int i = 1; i < v.size(); ++i) {
			ret += v[i] ? "T, " : "_|_, ";
		}
	}
	ret += ")";
	return ret;
}

string show(const vector<LightSymbol>& v) {
	string ret;
	ret += "(";
	for (auto s : v) {
		ret += prover::show(s) + ", ";
	}
	ret += ")";
	return ret;
}

}}}
