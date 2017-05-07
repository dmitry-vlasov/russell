#pragma once

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace daemon {

#define DEFAULT_DAEMON_LOGS "/var/tmp/mdld.log"
#define DEFAULT_DAEMON_HOST "localhost"
#define DEFAULT_DAEMON_PORT 808011

struct Config {
	Config() : port(DEFAULT_DAEMON_PORT), host(DEFAULT_DAEMON_HOST), logs(DEFAULT_DAEMON_LOGS) { }
	uint   port;
	string host;
	string logs;
};

struct Daemon {
	Config config;
	void run();

	static const Daemon& get() { return mod(); }
	static Daemon& mod() { static Daemon d; return d; }
private:
	Daemon() : config() { }
};
}} // mdl::daemon

