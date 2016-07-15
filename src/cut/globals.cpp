#include <boost/filesystem.hpp>

#include "cut/ast.hpp"
#include "cut/globals.hpp"

namespace mdl {
namespace cut {

namespace fs = boost::filesystem;

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
		cut::parse(config.in);
		//cout << endl << show(*source);
		return true;
	} catch (Error& err) {
		error += '\n';
		error += err.what();
		return false;
	}
}

bool Cut::save() {
	try {
		if (!config.out.size()) return false;
		if (config.out.substr(config.out.size() - 3) != ".mm") return false;
		source->save();
		//ofstream out(config.out);
		//out << *source << endl;
		//out.close();
		return true;
	} catch (Error& err) {
		error += '\n';
		error += err.what();
		return false;
	}
}

void Section::save() const {
	if (type != Type::PARAGRAPH && type != Type::SOURCE)
		fs::create_directories(dir);
	ofstream out(file);
	out << show_contents(*this) << endl;
	for (Section* s : parts) {
		s->save();
		out << "[" << s->file << "]\n";
	}
	out.close();
}

}} // mdl::cut
