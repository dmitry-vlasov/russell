
#include "../../../include/mm/sys.hpp"
#include "mm/merge/grammar.hpp"

namespace mdl { namespace mm { namespace merge {

namespace {
	void remove_commented_imports(string& src) {
		stringstream ss;
		struct state {
			state() :
			in_comment(false), in_inclusion(), is_dollar(false) { }
			bool in_comment;
			bool in_inclusion;
			bool is_dollar;
		};
		state s;
		for (char ch : src) {
			bool prev_dollar = s.is_dollar;
			switch (ch) {
			case '$' : s.is_dollar = true; break;
			case '[' : if (prev_dollar) s.in_inclusion = true; break;
			case ']' : if (prev_dollar) s.in_inclusion = false; break;
			case '(' : if (prev_dollar) s.in_comment = true; break;
			case ')' : if (prev_dollar) s.in_comment = false; break;
			default: s.is_dollar = false;
			}
			if (!s.in_comment || !s.in_inclusion) ss << ch;
		}
		src = ss.str();
	}
}

void Merger::read(Path in) {
	string data;
	in.read(data);
	remove_commented_imports(data);
	LocationIter iter(data.begin(), in.name);
	LocationIter end(data.end(), in.name);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(this), ascii::space);
	if (!r || iter != end) {
		throw Error("parsing failed", in.name);
	}
}

}}} // mdl::mm::merge
