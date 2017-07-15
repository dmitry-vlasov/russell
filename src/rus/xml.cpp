#include "rus_ast.hpp"

namespace mdl { namespace rus {

void writeXMLSafe (string& str, const string& s) {
	for (char c : s) {
		switch (c) {
		case '\"': str += "&quot;"; break;
		case '\'': str += "&apos;"; break;
		case '&' : str += "&amp;";  break;
		case '<' : str += "&lt;";   break;
		case '>' : str += "&gt;";   break;
		default  : str += c;       break;
		}
	}
}

string xml(const Const& c, uint bits) {
	if (!xml_bit(bits, XmlNode::CONST)) return "";
	string ret = "<constant ";
	ret += "name=\""; writeXMLSafe (ret, Lex::toStr(c.symb)); ret += "\" ";
	ret += c.xml_id();
	ret += c.token.locate().xml();
	ret += "/>\n";
	return ret;
}

//string xml(const Vars& c, uint bits);
//string xml(const Disj&, uint bits);

string xml(const Type& t, uint bits) {
	if (!xml_bit(bits, XmlNode::TYPE)) return "";
	string ret = "<type ";
	ret += t.xml_id();
	ret += t.token.locate().xml();
	ret += ">\n";
	for (const auto& s : t.sup)
		ret += Indent::paragraph(xml(*s.get(), bits));
	ret += "</type>\n";
	return ret;
}

string xml(const Rule& r, uint bits) {
	if (!xml_bit(bits, XmlNode::RULE)) return "";
	string ret = "<rule ";
	ret += r.xml_id();
	ret += r.token.locate().xml();
	ret += "/>\n";
	return ret;
}

string xml(const Assertion& a, uint bits) {
	switch (a.kind()) {
	case Assertion::AXM: if (!xml_bit(bits, XmlNode::AXIOM))   return ""; break;
	case Assertion::DEF: if (!xml_bit(bits, XmlNode::DEF))     return ""; break;
	case Assertion::THM: if (!xml_bit(bits, XmlNode::THEOREM)) return ""; break;
	}
	string ret = "<";
	ret += a.kindStr() + " ";
	ret += a.xml_id();
	ret += a.token.locate().xml();
	ret += "/>\n";
	return ret;
}

//string xml(const Def&, uint bits);
//string xml(const Assertion&, uint bits);
//string xml(const Theorem&, uint bits);

string xml(const Proof& p, uint bits) {
	if (!xml_bit(bits, XmlNode::PROOF)) return "";
	string ret = "<proof ";
	ret += p.xml_id();
	ret += p.token.locate().xml();
	ret += "/>\n";
	return ret;
}

//string xml(const Step&, uint bits);
//string xml(const Ref&, uint bits);
//string xml(const Qed&, uint bits);
//string xml(const Hyp&, uint bits);
//string xml(const Prop&, uint bits);

string xml(const Node& n, uint bits) {
	switch (n.kind) {
	case Node::CONST:   return xml(*n.val.cst, bits);
	case Node::TYPE:    return xml(*n.val.tp, bits);
	case Node::RULE:    return xml(*n.val.rul, bits);
	case Node::AXIOM:   return xml(*n.val.ax, bits);
	case Node::DEF:     return xml(*n.val.def, bits);
	case Node::THEOREM: return xml(*n.val.thm, bits);
	case Node::PROOF:   return xml(*n.val.prf, bits);
	case Node::THEORY:  return xml(*n.val.thy, bits);
	case Node::IMPORT:  return xml(*n.val.imp, bits);
	case Node::COMMENT: return "";
	default : assert(false && "impossible"); return "";
	}
}

string xml(const Import& i, uint bits) {
	if (!xml_bit(bits, XmlNode::IMPORT)) return "";
	string ret = "<import ";
	ret += i.source.get()->xml_id();
	ret += i.token.locate().xml();
	ret += "/>\n";
	return ret;
}

string xml(const Theory& t, uint bits) {
	if (!xml_bit(bits, XmlNode::TYPE)) return "";
	string ret = "<theory ";
	ret += xml_sys_id(Sys::curr(), t.id);
	ret += t.token.locate().xml();
	ret += ">\n";
	for (const auto& n : t.nodes)
		ret += Indent::paragraph(xml(n, bits));
	ret += "</theory>\n";
	return ret;
}

string xml(const Source& s, uint bits) {
	string ret;
	ret += "<!DOCTYPE russell_mining_output>\n";
	ret += "<outline>\n";
	for (const auto& n : s.theory->nodes)
		ret += Indent::paragraph(xml(n, bits));
	ret += "</outline>\n\n";
	return ret;
}
//string xml(const Comment&, uint bits);

}}
