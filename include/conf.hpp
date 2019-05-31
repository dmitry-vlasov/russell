#pragma once

#include "std.hpp"
#include "actions.hpp"
#include "path.hpp"
#include "lib.hpp"

namespace mdl {

enum class Lang { NONE, MM, RUS };

inline Lang chooseLang(const string& lang) {
	if (lang.length() >= 2) {
		if (lang.length() >= 3) {
			auto lastThreeChars = lang.substr(lang.length() - 3);
			if (lastThreeChars == "rus") return Lang::RUS;
		}
		auto lastTwoChars = lang.substr(lang.length() - 2);
		if (lastTwoChars == "mm") return Lang::MM;
	}
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

 	bool verbose() const { return !has("silent"); }

	Lang target() const {
		if (!has("target")) return Lang::NONE;
		const string& l = opts.at("target");
		if (l == "rus") return Lang::RUS;
		if (l == "mm")  return Lang::MM;
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
			d.args.push_back(Descr::Arg("silent", "", true));
			d.args.push_back(Descr::Arg("root", "dir", true));
			d.args.push_back(Descr::Arg("target", "rus|mm|smm", true));
		}
		return d;
	}

	string show() const {
		string str;
		for (const auto& p : opts) {
			str += "\t" + p.first + "=" + p.second + "\n";
		}
		return str;
	}

private:
	map<string, string> opts;
};

// Parse options in the format:
//  'k1=v1,k2=v2,...,kn=vn'

inline map<string, string> parse_options(const string& options, const string& delim = ",", const string& to_trim = "'") {
	map<string, string> ret;
	for (const auto& opt : split_string(trim_string(options, to_trim), delim)) {
		vector<string> opt_vect = split_string(opt, "=");
		switch (opt_vect.size()) {
		case 0: break;
		case 1: ret.emplace(opt_vect[0], opt_vect[0]); break;
		case 2: ret.emplace(opt_vect[0], opt_vect[1]); break;
		default: ret.emplace(opt_vect[0], opt_vect[1]); break;
		}
	}
	return ret;
}

}

