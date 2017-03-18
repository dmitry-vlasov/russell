#include "common.hpp"

namespace mdl {

string Timers::show() const {
	string str;
	uint ms = 0;
	for (auto& p : timers)
		ms = std::max(ms, (uint)p.first.size());
	str += "Timings:";
	for (auto& p : timers) {
		int s = p.first.size();
		str += "\n\t" + p.first + Indent(ms - s, ' ').str() + ": " + p.second.show();
	}
	return str;
}

} // mdl


