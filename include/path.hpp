#pragma once

#include "std.hpp"
#include "error.hpp"

namespace mdl {

typedef pair<string, string> Patch;

struct Path {
	Path(const string& n = "", const string& r = "", const string& e = "") : root_(r), name_(n), ext_(e) {
		boost::trim(root_);
		boost::trim(name_);
		boost::trim(ext_);
		boost::erase_last(root_, "/");
		name_ext(name_);
	}
	Path(const Path& p) : root_(p.root_), name_(p.name_), ext_(p.ext_) { }
	Path& operator = (const Path& p) {
		root_ = p.root_;
		name_ = p.name_;
		ext_ = p.ext_;
		return *this;
	}
	string path() const {
		return (root_.size() ? root_ + "/" : "") + name_ + (ext_.size() ? "." + ext_ : "");
	}
	string dir() const {
		string p = path();
		int i = p.find_last_of("/");
		return (i == string::npos) ? "" : p.substr(0, i) + "/";
	}
	void read(string& data, const vector<Patch>* patches = nullptr) const;
	void write(const string& data) const;
	Path relative(const string& n) const {
		return Path(n, root_, ext_);
	}
	string root() const { return root_ ; }
	string name() const { return name_; }
	string ext()  const { return ext_; }

private:
	static void patch(string& data, const vector<Patch>& patches) {
		for (const Patch& patch : patches) {
			const string& to_replace = patch.first;
			const string& replacement = patch.second;
			size_t pos = data.find(to_replace);
			if (pos != string::npos) {
				data.replace(pos, to_replace.length(), replacement);
			}
		}
	}
	void name_ext(string ne) {
		boost::trim(ne);
		int i = ne.find_last_of(".");
		name_ = ne.substr(0, i);
		if (i != string::npos) ext_ = ne.substr(i + 1);
	}

	string root_;
	string name_;
	string ext_;
};

}
