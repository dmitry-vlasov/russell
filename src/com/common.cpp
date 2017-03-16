#include "common.hpp"

namespace mdl { namespace {

string n_spaces(uint n) {
	string s;
	while (n--) s += ' ';
	return s;
}

}

string Timers::show() const {
	string str;
	uint ms = 0;
	for (auto& p : timers)
		ms = std::max(ms, (uint)p.first.size());
	str += "Timings:";
	for (auto& p : timers) {
		int s = p.first.size();
		str += "\n\t" + p.first + n_spaces(ms - s) + ": " + p.second.show();
	}
	return str;
}

} // mdl


