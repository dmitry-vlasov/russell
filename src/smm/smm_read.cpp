#include <smm_sys.hpp>
#include <smm_ast.hpp>

namespace mdl { namespace smm {

void read(uint label) {
	delete Sys::get().math.get<Source>().access(label);
	queue<uint> to_read;
	to_read.push(label);

	map<uint, set<uint>> includes;
	vector<uint> new_sources;

	while (!to_read.empty()) {
		label = to_read.front(); to_read.pop();
		if (Sys::get().math.get<Source>().has(label)) continue;

		Source* src = new Source(label);
		src->read();
		const string& data = src->data();
		new_sources.push_back(label);

		string inc;
		bool inside_inc = false;
		bool inside_comm = false;

		for (auto i = data.begin(); i != data.end(); ++ i) {
			if (*i == '$') {
				++i;
				if (*i == '[' && !inside_comm) {
					++i;
					inside_inc = true;
				}
				if (*i == ']' && !inside_comm) {
					++i;
					inside_inc = false;
					boost::trim(inc);
					uint inc_label = Lex::toInt(Path::trim_ext(inc));
					inc.clear();
					includes[label].insert(inc_label);
					to_read.push(inc_label);
				}
				if (*i == '(') { ++i; inside_comm = true; }
				if (*i == ')') { ++i; inside_comm = false; }
			} else {
				if (inside_inc) inc += *i;
			}
		}
	}
	for (auto s : new_sources) {
		for (auto inc : includes[s]) {
			auto inc_src = Sys::mod().math.get<Source>().access(inc);
			Sys::mod().math.get<Source>().access(s)->include(inc_src);
		}
	}
}

}}
