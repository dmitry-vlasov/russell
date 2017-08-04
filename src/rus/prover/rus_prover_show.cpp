#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

// THIS_IDX, CHILD_IDX, PARNT_IDX, RECURS, ASS, EXPR, SUB, PRFSIZE

constexpr uint THIS_IDX_BIT   = 0x001;
constexpr uint CHILD_IDX_BIT  = 0x002;
constexpr uint PARNT_IDX_BIT  = 0x004;
constexpr uint RECURS_BIT     = 0x008;
constexpr uint ASS_BIT        = 0x010;
constexpr uint EXPR_BIT       = 0x020;
constexpr uint SUB_BIT        = 0x040;
constexpr uint PRF_SZ_BIT     = 0x080;

struct ShowModeDescr {
	string str;
	uint   bit;
};

static map<ShowMode, ShowModeDescr> show_nodes = {
	{ShowMode::THIS_IDX,  {"idx",     THIS_IDX_BIT}},
	{ShowMode::CHILD_IDX, {"ch_idx",  CHILD_IDX_BIT}},
	{ShowMode::PARNT_IDX, {"par_idx", PARNT_IDX_BIT}},
	{ShowMode::RECURS,    {"recurs",  RECURS_BIT}},
	{ShowMode::ASS,       {"ass",     ASS_BIT}},
	{ShowMode::EXPR,      {"expr",    EXPR_BIT}},
	{ShowMode::SUB,       {"sub",     SUB_BIT}},
	{ShowMode::PRF_SZ,    {"prf_sz",  PRF_SZ_BIT}},
};

uint show_bits(string str) {
	uint ret = 0;
	while (str.size()) {
		string::size_type i = str.find(',');
		string s = str.substr(0, str.find(','));
		for (auto p : show_nodes) {
			if (p.second.str == s) {
				ret += p.second.bit;
				break;
			}
		}
		str = (i == string::npos) ? "" : str.substr(i + 1);
	}
	return ret;
}

string show_bits(uint m) {
	string ret;
	for (auto p : show_nodes) {
		if (m & p.second.bit) {
			ret += (ret.size()? "," : "") + p.second.str;
		}
	}
	return ret;
}

bool show_bit(uint m, ShowMode n) {
	return show_nodes[n].bit & m;
}

string Node::show(uint m) const {
	string ret;
	if (show_bit(m, ShowMode::RECURS)) {
		for (const auto& n : child) {
			ret += n->show(m);
		}
	}
	if (show_bit(m, ShowMode::THIS_IDX)) {
		ret += string("this=") + to_string(ind) + " ";
	}
	if (show_bit(m, ShowMode::CHILD_IDX)) {
		ret += "children=(";
		bool first = true;
		for (const auto& n : child) {
			if (!first) ret += ", ";
			ret += to_string(n->ind);
			first = false;
		}
		ret += ") ";
	}
	if (show_bit(m, ShowMode::PARNT_IDX)) {
		ret += string("parent=") + (parent ? to_string(parent->ind) : "<none>") + " ";
	}
	return ret + "\n";
}

string Prop::show(uint m) const {
	string ret;
	ret += "Prop: ";
	ret += Node::show(m);
	if (show_bit(m, ShowMode::ASS)) {
		ret += string("ass=") + show_id(prop_.assertion()->id()) + " ";
	}
	if (show_bit(m, ShowMode::SUB)) {
		ret += string("sub=") + show(sub_) + " ";
	}
	return ret + "\n";
}

string Hyp::show(uint m) const {
	string ret;
	ret += "Hyp: ";
	ret += Node::show(m);
	if (show_bit(m, ShowMode::EXPR)) {
		ret += string("expr=") + rus::show(expr_) + " ";
	}
	return ret + "\n";
}

string Ref::show(uint m) const {
	string ret;
	ret += "Ref: ";
	ret += Node::show(m);
	return ret + "\n";
}

string ProofElem::show(uint m) const {
	string ret;
	ret += "ProofElem: ";
	return ret + "\n";
}

string ProofHyp::show(uint m) const {
	string ret;
	ret += "ProofHyp: ";
	return ret + "\n";
}

string ProofStep::show(uint m) const {
	string ret;
	ret += "ProofStep: ";
	return ret + "\n";
}


}}}

