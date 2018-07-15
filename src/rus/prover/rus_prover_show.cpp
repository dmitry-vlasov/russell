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
	ret += "\t<substitution>";
	ret += "<![CDATA[";
	ret += rus::show(sub);
	ret += "]]>";
	ret += "</substitution>\n";
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
	ret += "<![CDATA[" + rus::show(expr) + "]]>";
	ret += "</expression>\n";
	ret += string("</") + (parent ? "hyp" : "root") + ">\n";
	return ret;
}

string ProofTop::show() const {
	string ret;
	ret += "ProofTop: ";
	return ret + "\n";
}

string ProofExp::show() const {
	string ret;
	ret += "ProofHyp: ";
	return ret + "\n";
}

string ProofProp::show() const {
	string ret;
	ret += "ProofStep: ";
	return ret + "\n";
}

}}}

