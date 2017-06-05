#pragma once

#include <boost/asio.hpp>
#include <boost/bind.hpp>

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "mm/ast.hpp"
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
	void start();
	void enqueue(const string& com) { commands.push(com); }

	static const Daemon& get() { return mod(); }
	static Daemon& mod() { static Daemon d; return d; }

private:
	enum { MAX_MESSAGE_SIZE = 1024 };
	boost::asio::io_service service;
	boost::asio::ip::tcp::endpoint endpoint;
	boost::asio::ip::tcp::acceptor acceptor;
	boost::asio::ip::tcp::socket   socket;
	char buffer[MAX_MESSAGE_SIZE];
	enum State { RUN_QUEUE, RUN_REQUEST, EXIT, CLOSE };
	State state;
	queue<string> commands;

	static void session();

	Daemon();

	string get_request();
	void send_response(const string& response);
};

struct Console {
	Conn conn;

	void start();
	void enqueue(const string& com) { commands.push(com); }

	static const Console& get() { return mod(); }
	static Console& mod() { static Console c; return c; }

private:
	enum { MAX_MESSAGE_SIZE = 1024 };
	boost::asio::io_service service;
	boost::asio::ip::tcp::resolver resolver;
	boost::asio::ip::tcp::socket   socket;
	boost::asio::ip::tcp::endpoint endpoint;
	int  message_size;
	char buff[MAX_MESSAGE_SIZE];
	queue<string> commands;

	static void session();
	Console();
	string get_command();
	string get_response();
	size_t read_complete(const boost::system::error_code& err, size_t bytes) const;
	void send_request(const string& request);
	void connect();
	void disconnect();
};

} // mdl::daemon

