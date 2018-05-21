#include "rus_ast.hpp"

namespace mdl { namespace rus {

string xml(const Const& c, uint bits) {
	if (!xml_bit(bits, XmlNode::CONST)) return "";
	string ret = "<constant ";
	ret += "sys=\"" + Lex::toStr(c.sys()) + "\" ";
	ret += "id=\"" + escape_xml(Lex::toStr(c.ascii)) + "\" ";
	ret += "name=\"" + escape_xml(Lex::toStr(c.ascii)) + "\" ";
	ret += c.token.locate().xml();
	ret += ">\n";
	ret += "\t" + Lex::toStr(c.symb) + "\n";
	ret += "</constant>\n";
	return ret;
}

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
	if (!(xml_bit(bits, XmlNode::RULE) && r.token.is_defined())) return "";
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

string xml(const Proof& p, uint bits) {
	if (!xml_bit(bits, XmlNode::PROOF)) return "";
	string ret = "<proof ";
	ret += p.xml_id();
	ret += p.token.locate().xml();
	ret += "/>\n";
	return ret;
}

string xml(const Import& i, uint bits) {
	if (!xml_bit(bits, XmlNode::IMPORT)) return "";
	string ret = "<import ";
	ret += i.source.get()->xml_id();
	ret += i.token.locate().xml();
	ret += "/>\n";
	return ret;
}

string xml(const Theory& t, uint bits);

string xml(const Theory::Node& n, uint bits) {
	switch (Theory::kind(n)) {
	case Theory::CONST:   return xml(*Theory::const_(n), bits);
	case Theory::TYPE:    return xml(*Theory::type(n), bits);
	case Theory::RULE:    return xml(*Theory::rule(n), bits);
	case Theory::AXIOM:   return xml(*Theory::axiom(n), bits);
	case Theory::DEF:     return xml(*Theory::def(n), bits);
	case Theory::THEOREM: return xml(*Theory::theorem(n), bits);
	case Theory::PROOF:   return xml(*Theory::proof(n), bits);
	case Theory::THEORY:  return xml(*Theory::theory(n), bits);
	case Theory::IMPORT:  return xml(*Theory::import(n), bits);
	case Theory::COMMENT: return "";
	default : assert(false && "impossible"); return "";
	}
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

string xml_outline(const Source& s, uint bits) {
	string ret;
	ret += "<!DOCTYPE russell_mining_output>\n";
	ret += "<outline>\n";
	for (const auto& n : s.theory->nodes)
		ret += Indent::paragraph(xml(n, bits));
	ret += "</outline>\n\n";
	return ret;
}

template<class T>
string xml_struct(uint bits) {
	string  ret;
	for (auto& p : Sys::mod().math.get<T>())
		ret += xml(*p.second.data, bits);
	return ret;
}

string xml_structure(uint bits) {
	string ret;
	ret += "<!DOCTYPE russell_mining_output>\n";
	ret += "<structure>\n";
	if (xml_bit(bits, XmlNode::CONST))
		ret += Indent::paragraph(xml_struct<Const>(bits));
	if (xml_bit(bits, XmlNode::TYPE))
		ret += Indent::paragraph(xml_struct<Type>(bits));
	if (xml_bit(bits, XmlNode::RULE))
		ret += Indent::paragraph(xml_struct<Rule>(bits));
	if (xml_bit(bits, XmlNode::AXIOM) || xml_bit(bits, XmlNode::DEF))
		ret += Indent::paragraph(xml_struct<Assertion>(bits));
	ret += "</structure>\n";
	return ret;
}


}}
