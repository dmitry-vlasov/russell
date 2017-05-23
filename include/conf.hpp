#pragma once

#include "std.hpp"
#include "actions.hpp"
#include "path.hpp"

namespace mdl {

enum class Lang { NONE, MM, SMM, RUS };

inline Lang chooseLang(const string& lang) {
	if (lang == "rus") return Lang::RUS;
	if (lang == "smm") return Lang::SMM;
	if (lang == "mm")  return Lang::MM;
	return Lang::NONE;
}

// Configuration for a deductive system
class Conf {
public :
	Conf() { }
	Conf(const Conf&) = delete;
	void operator = (const Conf&) = delete;

	bool   has(const string& name) const { return opts.count(name); }
	string get(const string& name) const { return has(name) ? opts.at(name) : ""; }
	void   set(const string& name, const string& value = "") { opts[name] = value; }

 	bool verbose() const { return has("verbose"); }

	Lang target() const {
		if (!has("target")) return Lang::NONE;
		const string& l = opts.at("target");
		if (l == "rus") return Lang::RUS;
		if (l == "mm")  return Lang::MM;
		if (l == "smm") return Lang::SMM;
		return Lang::NONE;
	}

	Return read(const Args& args) {
		for (auto& arg : args) {
			int i = arg.find_last_of("=");
			string name = arg.substr(0, i);
			string value = (i == string::npos) ? "" : arg.substr(i + 1);
			opts[name] = value;
		}
		return Return();
	}

	Descr descr() const {
		static Descr d("options", -1, true);
		if (d.args.empty()) {
			d.args.push_back(Descr::Arg("verbose", "", true));
			d.args.push_back(Descr::Arg("deep", "", true));
			d.args.push_back(Descr::Arg("info", "", true));
			d.args.push_back(Descr::Arg("root", "dir", true));
			d.args.push_back(Descr::Arg("target", "rus|mm|smm", true));
		}
		return d;
	}

private:
	map<string, string> opts;
};

}
