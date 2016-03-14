#pragma once

#include "std.hpp"

namespace mdl {

class Table {
	vector<string> strings;
	map<string, uint> table;
public:
	Table() : strings(), table() { }
	uint getInt(const string& str) const {
		if (table.find(str) == table.end())
			return -1;
		else
			return table.find(str)->second;
	}
	uint toInt(const string& str) {
		if (table.find(str) == table.end()) {
			int ind = table.size();
			table[str] = ind;
			strings.push_back(str);
		}
		return table[str];
	}
	const string& toStr (uint i) const {
		if (i >= strings.size()) {
			static string str = "<UNDEF>";
			return str;
		}
		return strings[i];
	}
};
  
}
