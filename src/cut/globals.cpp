#include "cut/ast.hpp"
#include "cut/globals.hpp"

namespace mdl {
namespace cut {

void Cut::run() {
	timer.start();
	if (config.verbose)
		cout << "cutting file " << config.in << " ... " << flush;
	if (!parse()) return;
	if (!save())  return;
	timer.stop();
	if (config.verbose)
		cout << "done in " << timer << endl;
}

bool Cut::parse() {
	try {
		source = cut::parse(config.in);
		//cout << endl << *source;
		return true;
	} catch (Error& err) {
		error += '\n';
		error += err.what();
		return false;
	}
}

bool Cut::save() {
	return true;
}
	
}} // mdl::cut
