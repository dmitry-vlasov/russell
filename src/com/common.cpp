#include "common.hpp"

namespace mdl {

string Timers::show() const {
	string str;
	uint ms = 0;
	for (auto& p : timers) {
		ms = std::max(ms, (uint)p.first.size());
	}
	str += "Timings:";
	for (auto& p : timers) {
		int s = p.first.size();
		str += "\n\t" + p.first + Indent(ms - s, ' ').str() + ": " + p.second.show();
	}
	return str;
}

void Path::read(string& data, const vector<Patch>* patches) const {
	if (!boost::filesystem::is_regular_file(path())) {
		throw Error("cannot read", path());
	}
	ifstream in(path());
	if (!in) {
		throw Error("cannot read", path());
	}
	in.unsetf(std::ios::skipws);
	data.clear();
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(data));
	in.close();
	if (patches) {
		patch(data, *patches);
	}
}

void Path::write(const string& data) const {
	ofstream out(path(), std::ios_base::out);
	if (!out.good()) {
		throw Error("cannot write", path());
	}
	std::copy(
		data.begin(),
		data.end(),
		std::ostream_iterator<char>(out));
	out.close();
}

} // mdl


