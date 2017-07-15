#include "xml.hpp"

namespace mdl {

//"import,const,type,rule,axiom,def,theorem,proof,theory,problem"

// IMPORT, CONST, TYPE, RULE, AXIOM, DEF, THEOREM, PROOF, THEORY, PROBLEM

constexpr uint IMPORT_BIT  = 0x001;
constexpr uint CONST_BIT   = 0x002;
constexpr uint TYPE_BIT    = 0x004;
constexpr uint RULE_BIT    = 0x008;
constexpr uint AXIOM_BIT   = 0x010;
constexpr uint DEF_BIT     = 0x020;
constexpr uint THEOREM_BIT = 0x040;
constexpr uint PROOF_BIT   = 0x080;
constexpr uint THEORY_BIT  = 0x100;
constexpr uint PROBLEM_BIT = 0x200;

struct XmlNodeDescr {
	string str;
	uint   bit;
};

static map<XmlNode, XmlNodeDescr> xml_nodes = {
	{XmlNode::IMPORT,  {"import",  IMPORT_BIT}},
	{XmlNode::CONST,   {"const",   CONST_BIT}},
	{XmlNode::TYPE,    {"type",    TYPE_BIT}},
	{XmlNode::RULE,    {"rule",    RULE_BIT}},
	{XmlNode::AXIOM,   {"axiom",   AXIOM_BIT}},
	{XmlNode::DEF,     {"def",     DEF_BIT}},
	{XmlNode::THEOREM, {"theorem", THEOREM_BIT}},
	{XmlNode::PROOF,   {"proof",   PROOF_BIT}},
	{XmlNode::THEORY,  {"theory",  THEORY_BIT}},
	{XmlNode::PROBLEM, {"problem", PROBLEM_BIT}}
};

uint xml_bits(string str) {
	uint ret = 0;
	while (str.size()) {
		string::size_type i = str.find(',');
		string s = str.substr(0, str.find(','));
		for (auto p : xml_nodes) {
			if (p.second.str == s) {
				ret += p.second.bit;
				break;
			}
		}
		str = (i == string::npos) ? "" : str.substr(i + 1);
	}
	return ret;
}

string xml_bits(uint m) {
	string ret;
	for (auto p : xml_nodes) {
		if (m & p.second.bit) {
			ret += (ret.size()? "," : "") + p.second.str;
		}
	}
	return ret;
}
bool xml_bit(uint m, XmlNode n) {
	return xml_nodes[n].bit & m;
}

}
