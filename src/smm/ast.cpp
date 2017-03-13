#include "smm/ast.hpp"
#include "smm/sys.hpp"

namespace mdl { namespace smm {

Source::Source(uint l) : label(l), data(), contents() {
	System::mod().math.sources[label] = this;
}
Path Source::rich_path() const {
	return System::conf().in.relative(name());
}
void Source::read() {
	rich_path().read(data);
}
void Source::write() {
	rich_path().write(data);
}

}} // mdl::smm
