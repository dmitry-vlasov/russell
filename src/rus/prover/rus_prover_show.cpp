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

static string show_assertion(const Assertion* a) {
	if (const Axiom* ax = dynamic_cast<const Axiom*>(a)) {
		return mdl::show(*ax);
	} else if (const Theorem* th = dynamic_cast<const Theorem*>(a)) {
		return mdl::show(*th);
	} else if (const Def* df = dynamic_cast<const Def*>(a)) {
		return mdl::show(*df);
	} else {
		assert(false && "impossible");
		throw Error("impossible");
	}
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

string Prop::show() const {
	string ret;
	ret += "<prop ";
	ret += string("name=\"") + Lex::toStr(prop.id()) + "\" ";
	ret += string("index=\"") + to_string(ind) + "\" ";
	ret += string("parent=\"") + to_string(parent->ind) + "\" ";
	ret += show_children_idx(premises);
	ret += ">\n";
	ret += "\t<assertion>";
	ret += "<![CDATA[";
	ret += show_assertion(prop.ass);
	ret += "]]>";
	ret += "</assertion>\n";
	ret += "\t<substitution>\n";
	ret += "\t<![CDATA[\n";
	ret += rus::prover::show(sub);
	ret += "\t]]>\n";
	ret += "\t</substitution>\n";
	ret += "</prop>\n";
	return ret;
}

string Hyp::show() const {
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
	ret += string("</") + (parent ? "hyp" : "root") + ">\n";
	return ret;
}

string ProofTop::show() const {
	ostringstream oss;
	oss << "<proof expr=\"" << prover::show(apply(sub, node.expr)) << "\" ";
	oss << "index=\"" << ind << "\">";
	oss << "<![CDATA[";
	oss << "hyp " << hyp.ind + 1;
	oss << "]]>\n";
	oss << "\t<substitution>\n";
	oss << "\t\t<![CDATA[\n";
	oss << prover::show(sub);
	oss << "\t\t]]>\n";
	oss << "\t</substitution>\n";
	oss << "</proof>\n";
	return oss.str();
}

string ProofExp::show() const {
	ostringstream oss;
	rus::Step* st = child ? child->step() : nullptr;
	rus::Proof* pr = proof();
	oss << "\t\t<proof expr=\"" << (st ? rus::show(st->expr) : prover::show(node.expr)) << "\" ";
	oss << "index=\"" << ind << "\">";
	oss << "\t\t<![CDATA[\n";
	oss << *pr;
	oss << "\n";
	oss << "\t\t]]>\n";
	delete pr;
	oss << "\t\t<substitution>\n";
	oss << "\t\t<![CDATA[\n";
	oss << prover::show(sub);
	oss << "\t\t]]>\n";
	oss << "\t\t</substitution>\n";
	oss << "\t</proof>\n";
	return oss.str();
}

string ProofProp::show() const {
	ostringstream oss;
	rus::Step* st = step();
	rus::Proof* pr = proof();
	oss << "\t\t<proof expr=\"" << rus::show(st->expr) << "\" ";
	oss << "index=\"" << ind << "\">";
	oss << "\t\t<![CDATA[\n";
	oss << *pr;
	oss << "\n";
	oss << "\t\t]]>\n";
	delete pr;
	oss << "\t\t<substitution>\n";
	oss << "\t\t<![CDATA[\n";
	oss << prover::show(sub);
	oss << "\t\t]]>\n";
	oss << "\t\t</substitution>\n";
	oss << "\t</proof>\n";
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

}}}

