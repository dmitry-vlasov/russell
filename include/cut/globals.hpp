#pragma once

#include "cut/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace cut {

struct Config {
	Config() :
	verbose(false), info(false), help(false), in(), out() { }

	bool verbose;
	bool info;
	bool help;

	string in;
	string out;
};

struct Cut {
	~ Cut() {
		if (source) delete source;
	}

	Config  config;
	Timer   timer;
	Source* source;
	string  error;

	void run();
	bool parse();
	bool save();

	static const Cut& get() { return mod(); }
	static Cut& mod() { static Cut cut; return cut; }
};

//ostream& operator << (ostream& os, const Cut&);
Source* parse(const string& path);
//smm::Source* translate(const Block* source);

}} // mdl::mm

