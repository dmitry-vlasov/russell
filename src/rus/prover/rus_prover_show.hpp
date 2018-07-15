#pragma once

#include "rus_ast.hpp"

namespace mdl { namespace rus { namespace prover {

enum class ShowMode {
	RECURS      = 0x001,
	ASS         = 0x002,
	EXPR        = 0x004,
	SUB         = 0x008,
	PRF_SZ      = 0x010,
	CHILD_NODES = 0x020,
	UP_NODE     = ASS | EXPR | CHILD_NODES,
};

struct ShowModeDescr {
	string   str;
	ShowMode bit;
};

inline const map<ShowMode, ShowModeDescr>& show_nodes() {
	static map<ShowMode, ShowModeDescr> nodes = {
		{ShowMode::RECURS,      {"recurs",  ShowMode::RECURS}},
		{ShowMode::ASS,         {"ass",     ShowMode::ASS}},
		{ShowMode::EXPR,        {"expr",    ShowMode::EXPR}},
		{ShowMode::SUB,         {"sub",     ShowMode::SUB}},
		{ShowMode::PRF_SZ,      {"prf_sz",  ShowMode::PRF_SZ}},
		{ShowMode::CHILD_NODES, {"ch_node", ShowMode::CHILD_NODES}},
		{ShowMode::UP_NODE,     {"up_node", ShowMode::UP_NODE}},
	};
	return nodes;
}

uint   show_bits(string);
string show_bits(uint);
bool   show_bit(uint, ShowMode);

}}}

