#include "location.hpp"

namespace mdl {

std::ostream& operator << (std::ostream& os, const Location& loc){
	static string str;
	loc.show(str);
	os << str;
	return os;
}

}


