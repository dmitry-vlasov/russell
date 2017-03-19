#pragma once

#include "std.hpp"
#include "symbol.hpp"

namespace mdl {

struct Lex {
	static uint getInt(const string& str) { return get().getIndex(str); }
	static uint toInt(const string& str) { return get().toIndex(str); }
	static const string& toStr (uint i) { return get().toString(i); }

private:
	Lex() : strings(), table() { }
	static Lex& get() { static Lex lex; return lex; }
	uint getIndex(const string& str) const {
		if (table.find(str) == table.end())
			return -1;
		else
			return table.find(str)->second;
	}
	uint toIndex(const string& str) {
		if (table.find(str) == table.end()) {
			int ind = table.size();
			table[str] = ind;
			strings.push_back(str);
		}
		return table[str];
	}
	const string& toString(uint i) const {
		if (i >= strings.size()) {
			static string str = "<UNDEF>";
			return str;
		}
		return strings[i];
	}
	vector<string>    strings;
	map<string, uint> table;
};

inline string show_sy(Symbol symb) {
	return Lex::toStr(symb.lit);
}
inline string show_id(uint lab) {
	return Lex::toStr(lab);
}

} // mdl

  
