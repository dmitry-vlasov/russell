#pragma once

#include "std.hpp"

namespace mdl {

class Table {
	vector<string> strings;
	map<string, int> table;
public:
	Table() : strings(), table() { }
	uint getInt(const string& str) {
		if (table.find(str) == table.end())
			return -1;
		else
			return table[str];
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
		if (i < 0 || i >= strings.size()) {
			static string str = "<UNDEF>";
			return str;
		}
		return strings[i];
	}
	void show (string& str) const {
		uint c = 0;
		for (auto it = strings.cbegin(); it != strings.cend(); ++ it, ++ c) {
			str += std::to_string(c);
			str += " -> ";
			str += *it;
			str += "\n";
		}
	}
};
  
}
