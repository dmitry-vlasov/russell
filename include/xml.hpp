#pragma once

#include "std.hpp"

namespace mdl {

enum class XmlNode {
	IMPORT, CONST, TYPE, RULE, AXIOM, DEF, THEOREM, PROOF, THEORY, PROBLEM
};

uint   xml_bits(string);
string xml_bits(uint);
bool   xml_bit(uint, XmlNode);

}
