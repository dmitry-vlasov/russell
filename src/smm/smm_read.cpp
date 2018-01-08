#include <smm_sys.hpp>
#include <smm_ast.hpp>

namespace mdl { namespace smm {

void read(uint label) {
	delete Sys::get().math.get<Source>().access(label);
	queue<uint> to_read;
	set<uint> read_done;
	to_read.push(label);
	while (!to_read.empty()) {
		label = to_read.front(); to_read.pop();
		Source* src = new Source(label);
		src->read();
		const string& data = src->data();
		read_done.insert(label);

		cout << "READING: " << Lex::toStr(label) << endl;

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
					label = Lex::toInt(Path::trim_ext(inc));
					inc.clear();
					if (read_done.find(label) == read_done.end()) {
						to_read.push(label);
					}
				}
				if (*i == '(') { ++i; inside_comm = true; }
				if (*i == ')') { ++i; inside_comm = false; }
			} else {
				if (inside_inc) inc += *i;
			}
		}
	}
}

}}
