#include "cut/ast.hpp"

namespace mdl { namespace cut {

string show(const Section& s) {
	string str;
	if(s.type != Type::SOURCE) {
		str += "$(\n";
		str += s.header;
		str += border(s.type);
		str += s.name;
		str += border(s.type);
		str += s.footer;
		str += "$)\n";
	}
	str += s.contents;
	for (auto p : s.parts)
		str += show(*p);
	return str;
}

}} // mdl::cut
