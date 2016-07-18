#include "mm/cut/ast.hpp"

namespace mdl { namespace mm { namespace cut {

string show_contents(const Section& s) {
	string str;
	const Section* imp = &s;
	while (imp && !imp->prev_sibling)
		imp = imp->parent;
	if (imp)
		str += "\n$[ " + imp->prev_sibling->path + " $]\n\n";
	if (s.type != Type::SOURCE) {
		str += "$(\n";
		str += s.header;
		str += border(s.type);
		str += s.name;
		str += border(s.type);
		str += s.footer;
		str += "\n$)\n";
	}
	str += s.contents;
	return str;
}

string show_all(const Section& s) {
	string str;
	str += show_contents(s);
	for (auto p : s.parts)
		str += show_all(*p);
	return str;
}

}}} // mdl::mm::cut
