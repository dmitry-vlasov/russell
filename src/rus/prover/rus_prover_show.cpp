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
	oss << "name=\"" << Lex::toStr(prop.id()) << "\" ";
	oss << "index=\"" << ind << "\" ";
	oss << "parent=\"" << parent->ind << "\" ";
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
	oss << "<" << (root() ? "root" : "hyp") << " ";
	oss << "index=\"" << ind << "\" ";
	oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
	if (parents.size()) {
		oss << "parents=\"";
		oss << parents.at(0)->ind;
		for (uint i = 1; i < parents.size(); ++i) {
			oss << "," << parents.at(i)->ind;
		}
		oss << "\" ";
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
	oss << "</" << (root() ? "root" : "hyp") << ">\n";
	return oss.str();
}

string Ref::show(bool with_proofs) const {
	ostringstream oss;
	oss << "<ref ";
	oss << "index=\"" << ind << "\" ";
	oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
	oss << "parent=\"" << parent->ind << "\" ";
	oss << "ancestor=\"" << ancestor->ind << "\" ";
	oss << ">\n";
	//oss << "\t<expression>";
	//oss << "<![CDATA[" << parent->expr.show() << "]]>";
	//oss << "</expression>\n";
	if (with_proofs) {
		for (const auto& p : proofs) {
			oss << Indent::paragraph(p->show());
		}
	}
	oss << "</ref>\n";
	return oss.str();
}

string ProofTop::show() const {
	ostringstream oss;
	oss << "<proof expr=\"" << expr().show() << "\" ";
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

string ProofHyp::show() const {
	rus::Step* st = nullptr;
	unique_ptr<rus::Proof> proof;
	try {
		proof = std::move(gen_proof(this));
		st = rus::Proof::step(proof->elems.back());
	} catch (Error& err) {
		proof.reset();
	}
	ostringstream oss;
	oss << "<proof expr=\"" << (st ? st->expr.show() : node.expr.show()) << "\" ";
	oss << "index=\"" << ind << "\" ";
	oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
	oss << ">" << endl;
	oss << "\t<![CDATA[" << endl;
	oss << (proof ? Indent::paragraph(proof->show(), "\t\t") : "\t\tFAILED PROOF") << endl;
	oss << "]]>" << endl;
	oss << "\t<substitution>" << endl;
	oss << "\t<![CDATA[" << endl;
	oss << Indent::paragraph(sub.show(), "\t\t");
	oss << "\t]]>" << endl;
	oss << "\t</substitution>" << endl;
	oss << "</proof>" << endl;
	return oss.str();
}

string ProofRef::show() const {
	rus::Step* st = nullptr;
	unique_ptr<rus::Proof> proof;
	try {
		proof = std::move(gen_proof(this));
		st = rus::Proof::step(proof->elems.back());
	} catch (Error& err) {
		proof.reset();
	}
	ostringstream oss;
	oss << "<proof expr=\"" << (st ? st->expr.show() : "") << "\" ";
	oss << "index=\"" << ind << "\" ";
	oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
	oss << ">" << endl;
	oss << "\t<![CDATA[" << endl;
	oss << (proof ? Indent::paragraph(proof->show(), "\t\t") : "\t\tFAILED PROOF") << endl;
	oss << "]]>" << endl;
	oss << "\t<substitution>" << endl;
	oss << "\t<substitution>" << endl;
	oss << "\t<![CDATA[" << endl;
	oss << Indent::paragraph(sub.show(), "\t\t");
	oss << "\t]]>" << endl;
	oss << "\t</substitution>" << endl;
	oss << "</proof>" << endl;
	return oss.str();
}

string ProofProp::show() const {
	rus::Step* st = nullptr;
	unique_ptr<rus::Proof> proof;
	try {
		proof = std::move(gen_proof(this));
		st = rus::Proof::step(proof->elems.back());
	} catch (Error& err) {
		proof.reset();
	}
	ostringstream oss;
	if (st) {
		oss << "<proof expr=\"" << st->expr << "\" ";
		oss << "index=\"" << ind << "\" ";
		oss << "hint=\"" << (hint ? "Y" : "N") <<  "\" ";
		oss << ">" << endl;
		oss << "\t<![CDATA[" << endl;
		oss << (proof ? Indent::paragraph(proof->show(), "\t\t") : "\t\tFAILED PROOF") << endl;
		oss << "]]>" << endl;
		oss << "\t<substitution>" << endl;
		oss << "\t<![CDATA[" << endl;
		oss << Indent::paragraph(sub.show(), "\t\t");
		oss << "\t]]>" << endl;
		oss << "\t</substitution>" << endl;
		oss << "</proof>" << endl;
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

string show_proof_struct(const ProofNode* n) {
	ostringstream oss;
	if (const ProofProp* p = dynamic_cast<const ProofProp*>(n)) {
		oss << "ProofProp(index = " << p->ind << ", node = " << p->node.ind << endl;
		oss << "\tprop = " << Lex::toStr(p->node.prop.id()) << endl;
		oss << "\tsub = " << endl << Indent::paragraph(p->sub.show(), "\t\t");
		oss << "\tnode sub = " << endl << Indent::paragraph(p->node.sub.show(), "\t\t");
		for (auto h : p->premises) {
			oss << Indent::paragraph(show_proof_struct(h));
		}
		oss << ")" << endl;
	} else if (const ProofTop* t = dynamic_cast<const ProofTop*>(n)) {
		oss << "ProofTop(index = " << t->ind << ", node = " << t->node.ind << endl;
		oss << "\thyp = " << t->hyp.ind << endl;
		oss << "\texp = " << t->expr().show() << endl;
		oss << "\tnode exp = " << t->node.expr.show() << endl;
		oss << "\tsub = " << endl << Indent::paragraph(t->sub.show(), "\t\t");
		oss << ")" << endl;
	} else if (const ProofRef* r = dynamic_cast<const ProofRef*>(n)) {
		oss << "ProofRef(index = " << r->ind << ", node = " << r->node.ind << endl;
		oss << "\texp = " << r->expr().show() << endl;
		oss << "\tsub = " << endl << Indent::paragraph(r->sub.show(), "\t\t");
		oss << Indent::paragraph(show_proof_struct(r->child));
		oss << ")" << endl;
	} else if (const ProofHyp* e = dynamic_cast<const ProofHyp*>(n)) {
		oss << "ProofExp(index = " << e->ind << ", node = " << e->node.ind << endl;
		oss << "\texp = " << e->expr().show() << endl;
		oss << "\tnode exp = " << e->node.expr.show() << endl;
		oss << "\tsub = " << endl << Indent::paragraph(e->sub.show(), "\t\t");
		oss << Indent::paragraph(show_proof_struct(e->child));
		oss << ")" << endl;
	} else {
		oss << "IMPOSSIBLE" << endl;
	}
	return oss.str();
}

static string show_nodes_struct(const Node* n, set<const Node*>& visited) {
	ostringstream oss;
	if (const Prop* p = dynamic_cast<const Prop*>(n)) {
		oss << "Prop(index = " << p->ind << endl;
		oss << "\tprop = " << Lex::toStr(p->prop.id()) << endl;
		oss << "\tsub = " << endl << Indent::paragraph(p->sub.show(), "\t\t");
		for (const auto& h : p->premises) {
			if (visited.count(h.get())) {
				oss << "\talready visited: " << h.get()->ind << endl;
			} else {
				visited.insert(h.get());
				oss << Indent::paragraph(show_nodes_struct(h.get(), visited));
			}
		}
		oss << ")" << endl;
	} else if (const Hyp* h = dynamic_cast<const Hyp*>(n)) {
		oss << "Hyp(index = " << h->ind << endl;
		oss << "\texp = " << h->expr << endl;
		for (const auto& v : h->variants) {
			if (visited.count(v.get())) {
				oss << "\talready visited: " << v.get()->ind << endl;
			} else {
				visited.insert(v.get());
				oss << Indent::paragraph(show_nodes_struct(v.get(), visited));
			}
		}
		oss << ")" << endl;
	} else if (const Ref* r = dynamic_cast<const Ref*>(n)) {
		oss << "Ref(index = " << r->ind << endl;
		oss << "\tparent = " << r->parent->ind << endl;
		oss << "\tancestor = " << r->ancestor->ind << endl;
		//oss << "\tnode exp = " << r->node.expr.show() << endl;
		oss << "\trepl = " << endl << Indent::paragraph(r->repl.show(), "\t\t");
		if (visited.count(r->ancestor)) {
			oss << "\talready visited: " << r->ancestor->ind << endl;
		} else {
			visited.insert(r->ancestor);
			oss << Indent::paragraph(show_nodes_struct(r->ancestor, visited));
		}
		oss << ")" << endl;
	} else {
		oss << "IMPOSSIBLE" << endl;
	}
	return oss.str();
}

string show_nodes_struct(const Node* n) {
	set<const Node*> visited;
	return show_nodes_struct(n, visited);
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
		ret += s.show() + ", ";
	}
	ret += ")";
	return ret;
}

}}}
