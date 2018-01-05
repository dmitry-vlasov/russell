#pragma once

#include "std.hpp"
#include "symbol.hpp"

namespace mdl {

struct Lex {
	static uint getInt(const string& str) { return get().getIndex(str); }
	static uint toInt(const string& str) { return get().toIndex(str); }
	static const string& toStr (uint i) { return get().toString(i); }

private:
	typedef cmap<string, uint> Table;
	typedef cvector<string> Strings;

	Lex() : strings(), table() { }
	static Lex& get() { static Lex lex; return lex; }
	uint getIndex(const string& str) const {
		Table::const_accessor accessor;
		return table.find(accessor, str) ? accessor->second : -1;
	}
	uint toIndex(const string& str) {
		Table::accessor accessor;
		if (table.insert(accessor, str)) {
			accessor->second = strings.size();
			strings.push_back(str);
		}
		return accessor->second;
	}
	const string& toString(uint i) const {
		if (i >= strings.size()) {
			static string str = "<UNDEF>";
			return str;
		}
		return strings[i];
	}
	Strings strings;
	Table   table;
};

inline string show_sy(Symbol symb) {
	return Lex::toStr(symb.lit);
}
inline string show_id(uint lab) {
	return Lex::toStr(lab);
}

} // mdl

  
