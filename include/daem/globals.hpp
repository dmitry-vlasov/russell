#pragma once

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace daemon {

#define DEFAULT_DAEMON_LOGS "/var/tmp/mdld.log"

struct Config {
	enum {
		DEFAULT_PORT = 808011
	};
	static const Config& get() { return mod(); }
	static Config& mod() { static Config d; return d; }
	uint   port;
	string logs;

private:
	Config() : port(DEFAULT_PORT), logs(DEFAULT_DAEMON_LOGS) { }
};

}} // mdl::daemon

