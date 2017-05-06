#pragma once

#include "std.hpp"
#include "error.hpp"

namespace mdl {

typedef pair<string, string> Patch;

struct Path {
	Path() : root(), name(), ext() { }
	Path(const string& n, const string& r, const string& e) : root(r), name(n), ext(e) {
		boost::trim(root);
		boost::trim(name);
		boost::erase_last(root, "/");
		boost::trim(ext);
	}
	Path(const string& n, const string& r = "") : root(r), name(), ext() {
		boost::trim(root);
		boost::trim(name);
		boost::erase_last(root, "/");
		name_ext(n);
	}
	Path(const Path& p) : root(p.root), name(p.name), ext(p.ext) { }
	Path& operator = (const Path& p) {
		root = p.root;
		name = p.name;
		ext = p.ext;
		return *this;
	}
	string path() const {
		return (root.size() ? root + "/" : "") + name + (ext.size() ? "." + ext : "");
	}
	string dir() const {
		string p = path();
		int i = p.find_last_of("/");
		return (i == string::npos) ? "" : p.substr(0, i) + "/";
	}
	void name_ext(string ne) {
		boost::trim(ne);
		int i = ne.find_last_of(".");
		name = ne.substr(0, i);
		ext.clear();
		if (i != string::npos) ext = ne.substr(i + 1);
	}
	void read(string& data, const vector<Patch>* patches = nullptr) const {
		ifstream in(path());
		if (!in) throw Error("cannot read", path());
		in.unsetf(std::ios::skipws);
		std::copy(
			std::istream_iterator<char>(in),
			std::istream_iterator<char>(),
			std::back_inserter(data));
		in.close();
		if (patches) patch(data, *patches);
	}
	void write(const string& data) const {
		ofstream out(path());
		if (!out) throw Error("cannot write", path());
		std::copy(
			data.begin(),
			data.end(),
			std::ostream_iterator<char>(out));
		out.close();
	}
	Path relative(const string& n) const {
		return Path(n, root, ext);
	}
	string root;
	string name;
	string ext;

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
};

}
