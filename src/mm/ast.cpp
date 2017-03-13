#include "mm/ast.hpp"
#include "mm/sys.hpp"

namespace mdl { namespace mm {

Source::Source(uint l) : label(l), data(), block(nullptr) {
	Sys::mod().math.sources[label] = this;
}
Path Source::rich_path() const {
	return Sys::conf().in.relative(name());
}
void Source::read() {
	rich_path().read(data);
}
void Source::write() {
	rich_path().write(data);
}

}} // mdl::mm
