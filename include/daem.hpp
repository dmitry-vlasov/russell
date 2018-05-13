#pragma once

#include <boost/asio.hpp>
#include <boost/bind.hpp>

#include "mm_ast.hpp"
#include "rus_ast.hpp"
#include "smm_ast.hpp"
#include "mm2_ast.hpp"
#include "timer.hpp"

namespace mdl {

constexpr const char* default_logs() { return  "/var/tmp/mdld.log"; }
constexpr const char* default_host() { return "localhost"; }
constexpr uint default_port() { return 808011; }

struct Conn {
	Conn() : port(default_port()), host(default_host()), logs(default_logs()) { }
	uint   port;
	string host;
	string logs;
};

struct Daemon {
	Conn conn;
	void start(bool verb);
	void enqueue(const string& com) { commands.push(com); }

	static const Daemon& get() { return mod(); }
	static Daemon& mod() { static Daemon d; return d; }

private:
	boost::asio::io_service        service;
	boost::asio::ip::tcp::endpoint endpoint;
	boost::asio::ip::tcp::acceptor acceptor;
	boost::asio::ip::tcp::socket   socket;
	enum State { RUN_QUEUE, RUN_REQUEST, EXIT, CLOSE };
	State state;
	queue<string> commands;
	bool verbose = false;

	static void session();

	Daemon();

	string get_request();
	void send_response(const string& response);
	ostream& out();
};

struct Console {
	Conn conn;

	void start(bool verb);
	void enqueue(const string& com) { commands.push(com); }

	static const Console& get() { return mod(); }
	static Console& mod() { static Console c; return c; }

private:
	boost::asio::io_service        service;
	boost::asio::ip::tcp::resolver resolver;
	boost::asio::ip::tcp::socket   socket;
	boost::asio::ip::tcp::endpoint endpoint;
	queue<string> commands;
	bool verbose = false;

	static void session();
	Console();
	string get_command();
	string get_response();
	void send_request(const string& request);
	void connect();
	void disconnect();
	ostream& out();
};

} // mdl::daemon

