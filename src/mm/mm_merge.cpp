#include "mm_sys.hpp"

namespace mdl { namespace mm { namespace {

struct Merged {
	stringstream contents;
	set<uint>    included;
};

void parse(uint label, Merged& merged) {

	merged.included.insert(label);

	Path in(Lex::toStr(label), Sys::conf().get("root"), "mm");
	string data;
	in.read(data);

	bool inside_inc = false;
	bool inside_comm = false;

	string inc;

	auto add_inc = [](string& inc, Merged& merged) {
		boost::trim(inc);
		uint inc_label = Lex::toInt(Path::trim_ext(inc));
		if (!merged.included.count(inc_label)) {
			parse(inc_label, merged);
		}
		inc.clear();
	};

	auto beg = data.begin();
	auto end = data.begin();

	for (auto i = data.begin(); i != data.end(); ++ i) {
		end = i;
		if (*i == '$') {
			end = ++i;
			switch (*i) {
			case '[': {
				if (!inside_comm) {
					merged.contents << string(beg, end - 1);
					inside_inc = true;
				}
				++i;
				break;
			}
			case ']': {
				if (!inside_comm && inside_inc) {
					beg = i + 1;
					add_inc(inc, merged);
					inside_inc = false;
				}
				++i;
				break;
			}
			case '(': end = ++i; inside_comm = true; break;
			case ')': end = ++i; inside_comm = false; break;
			}
		} else if (inside_inc) {
			inc += *i;
		}
	}
	merged.contents << string(beg, end);
}

}

void merge(uint src, uint tgt, uint tgt_root) {
	Sys::timer()["merge"].start();
	Merged merged;
	parse(src, merged);
	Path out(Lex::toStr(tgt), Lex::toStr(tgt_root), "mm");
	ofstream os(out.path());
	os << merged.contents.str();
	os.close();
	Sys::timer()["merge"].stop();
}


}} // mdl::mm2
