#pragma once

#include "common.hpp"

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

struct State {
	enum class Work { WORK, ERROR, EXIT, DEFAULT = WORK };
	enum class Lang { MM, SMM, RUS, DEFAULT = RUS };
	State(Work w = Work::DEFAULT, Lang l = Lang::DEFAULT) : work(w), lang(l) { }
	Work work;
	Lang lang;
};

struct Response {
	Response() : state(), ret() { }
	Response(State s, const string& r = "") : state(s), ret(r) { }
	State  state;
	string ret;
};

struct Request {
	Request(State s) : state(s), args() { }
	typedef vector<string> Args;
	State state;
	Args  args;
};

typedef Response (*Command) (Request);

struct Daemon {
	Config config;
	State  state;
	void run();

	static const Daemon& get() { return mod(); }
	static Daemon& mod() { static Daemon d; return d; }
private:
	Daemon() : config(), state() { }
};




}} // mdl::daemon

