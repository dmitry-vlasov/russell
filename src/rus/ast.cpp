#include "rus/ast.hpp"
#include "rus/sys.hpp"

namespace mdl { namespace rus {

Source::Source(uint l) : label(l), data(), theory(nullptr) {
	System::mod().math.sources[label] = this;
}
Source::~Source() {
	if (theory) delete theory;
}
Path Source::rich_path() const {
	return System::mod().config.in.relative(name());
}
void Source::read() {
	rich_path().read(data);
}
void Source::write() {
	rich_path().write(data);
}

}} // mdl::rus
