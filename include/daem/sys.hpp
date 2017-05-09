#pragma once

#include <boost/asio.hpp>
#include <boost/bind.hpp>

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace daemon {

using namespace boost::asio;

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
	enum { MAX_MESSAGE_SIZE = 1024 };
	io_service service;
	ip::tcp::endpoint endpoint;
	ip::tcp::acceptor acceptor;
	ip::tcp::socket   socket;
	char buffer[MAX_MESSAGE_SIZE];
	enum State { RUN, EXIT, CLOSE };
	State state;

	static void session();

	Daemon();

	string get_request();
	void send_response(const string& response);
};

struct Console {
	Config config;

	static const Console& get() { return mod(); }
	static Console& mod() { static Console c; return c; }

private:
	enum { MAX_MESSAGE_SIZE = 1024 };
	io_service service;
	ip::tcp::resolver resolver;
	ip::tcp::socket   socket;
	ip::tcp::endpoint endpoint;
	int  message_size;
	char buff[MAX_MESSAGE_SIZE];

	static void session();
	Console();
	string get_response();
	size_t read_complete(const boost::system::error_code& err, size_t bytes) const;
	void send_request(const string& request);
};

}} // mdl::daemon

