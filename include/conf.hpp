#pragma once

#include "std.hpp"
#include "path.hpp"

namespace mdl {

enum class Lang { NONE, MM, SMM, RUS };

// Configuration for a deductive system
class Conf {
public :
	bool   has(const string& name) const { return opts.count(name); }
	string get(const string& name) const { return has(name) ? opts.at(name) : ""; }
	void   set(const string& name, const string& value = "") { opts[name] = value; }

	bool verbose() const { return has("verbose"); }
	bool deep()    const { return has("deep"); }
	bool info()    const { return has("info"); }

	Lang target() const {
		if (!has("target")) return Lang::NONE;
		const string& l = opts.at("target");
		if (l == "rus") return Lang::RUS;
		if (l == "mm")  return Lang::MM;
		if (l == "smm") return Lang::SMM;
		return Lang::NONE;
	}

private:
	map<string, string> opts;
};

}
