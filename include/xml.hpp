#pragma once

#include "std.hpp"

namespace mdl {

enum class XmlNode {
	IMPORT, CONST, TYPE, RULE, AXIOM, DEF, THEOREM, PROOF, THEORY, PROBLEM
};

inline string escape_xml (const string& s) {
	string str;
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
	return str;
}

inline string de_escape_xml(const string& s) {
	string str;
	for (int i = 0; i < s.length(); ++ i) {
		if (s[i] == '&') {
			++i;
			if (s.substr(i, 4) == "quot") {
				i += 4;
				str += '\"';
			} else if (s.substr(i, 4) == "apos") {
				i += 4;
				str += '\'';
			} else if (s.substr(i, 3) == "amp") {
				i += 3;
				str += '&';
			} else if (s.substr(i, 2) == "lt") {
				i += 2;
				str += '<';
			} else if (s.substr(i, 2) == "gt") {
				i += 2;
				str += '>';
			} else {
				str += '&'; str += s[i];
			}
		} else str += s[i];
	}
	return str;
}

uint   xml_bits(string);
string xml_bits(uint);
bool   xml_bit(uint, XmlNode);

}
