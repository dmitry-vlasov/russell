#include "smm/tree.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {



static void translate(const Source* source, rus::Source* target) {

}


rus::Source* translate_to_rus(const Source* source) {
	rus::Source* target = new rus::Source(Smm::get().config.out);
	translate(source, target);
	return target;
}

}} // mdl::smm
