#pragma once

#include "std.hpp"

namespace mdl {

struct Lex {
	static uint getInt(const string& str) { return get().getIndex(str); }
	static uint toInt(const string& str) { return get().toIndex(str); }
	static const string& toStr (uint i) { return get().toString(i); }

private:
	typedef cmap<string, uint> Table;

	static Lex& get() { static Lex lex; return lex; }
	uint getIndex(const string& str) const {
		Table::const_accessor accessor;
		return table.find(accessor, str) ? accessor->second : -1;
	}
	uint toIndex(const string& str) {
		Table::accessor accessor;
		if (table.insert(accessor, str)) {
			accessor->second = table.size() - 1;
		}
		return accessor->second;
	}
	const string& toString(uint i) const {
		if (i >= table.size()) {
			static string str = "<UNDEF>";
			return str;
		}
		static map<int, string> strings;
		int n = table.size() - strings.size();
		if (n > 0) {
			static mutex m;
			m.lock();
			for (auto p : table) {
				strings[p.second] = p.first;
			}
			m.unlock();
		}
		return strings[i];
	}

	Table table;
};

} // mdl

  
