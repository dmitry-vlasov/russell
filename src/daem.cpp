#include <cctype>

#include <error.hpp>
#include <actions.hpp>
#include <daem.hpp>

#include <rus_sys.hpp>
#include <mm2_sys.hpp>

#include "boost/iostreams/stream.hpp"
#include "boost/iostreams/device/null.hpp"
#include "boost/asio.hpp"

namespace mdl {

using namespace boost::asio;

inline bool get_nonempty_line(string& ss, string& arg) {
	arg.clear();
	int ws = 0;
	auto i = ss.cbegin();
	for (; i != ss.cend() && isspace(*i);  ++i) ++ws;
	for (; i != ss.cend() && !isspace(*i); ++i) arg += *i;
	ss = ss.substr(arg.size() + ws);
	return !arg.empty();
}

static string receive_string(boost::asio::ip::tcp::socket& socket, bool& close) {
	enum { BUFFER_MAX_SIZE = 1024 * 64 };
	close = true;
	boost::system::error_code error;
	uint msg_len;
	size_t read_len = socket.read_some(boost::asio::buffer(&msg_len, sizeof(uint)), error);
	if (read_len > BUFFER_MAX_SIZE) {
		throw Error("received corrupted message", to_string(read_len) + " is too large");
	}
	char buffer[msg_len];
	read_len = socket.read_some(boost::asio::buffer(buffer, msg_len), error);
	if (error == boost::asio::error::eof) {
		// Connection closed cleanly by peer.
		return "";
	} else if (error) {
		throw boost::system::system_error(error); // Some other error.
	}
	if (read_len != msg_len) {
		throw Error("received corrupted message", to_string(read_len) + "!=" + to_string(msg_len));
	}
	close = false;
	return string(buffer, msg_len);
}

static void send_string(boost::asio::ip::tcp::socket& socket, const string& str) {
	uint msg_len = str.size();
	boost::asio::write(socket, boost::asio::buffer(&msg_len, sizeof(uint)));
	size_t written = boost::asio::write(socket, boost::asio::buffer(str));
	if (written != msg_len) {
		throw Error("incorrect transfer");
	}
}

Return execute_command(const string& command) {
	if (command == "status") {
		return Return("russell daemon is running ...");
	}
	Lang lang = Lang::NONE;
	uint sys = -1;
	Args args;
	{
		string str = command;
		string arg;
		if (!get_nonempty_line(str, arg)) return Return("no language is chosen", false);
		int i = arg.find_last_of(":");
		lang = chooseLang(arg.substr(0, i));
		sys  = (i == string::npos) ? Lex::toInt("default") : Lex::toInt(arg.substr(i + 1));
		while (get_nonempty_line(str, arg)) args.push_back(arg);
	}
	Return ret;
	switch (lang) {
	case Lang::RUS : ret = rus::Sys::exec_and_show(args); break;
	case Lang::MM  : ret = mm2::Sys::exec_and_show(args); break;
	case Lang::NONE: {
		if (command == "help" || command == "systems" || command == "current" || command == "destroy") {
			execute_command("rus " + command);
			execute_command("smm " + command);
			execute_command("mm " + command);
		} else return Return("unknown language, command: " + command, false);
	}
	}
	return ret;
}

Return execute(const string& coms) {
	string com_list(coms);
	Return ret;
	while (com_list.size()) {
		string::size_type sep = com_list.find(';');
		string com = com_list.substr(0, sep);
		com_list = sep == string::npos ? "" : com_list.substr(sep + 1);
		Return r = execute_command(com);
		if (!r) return r;
		ret.data += com_list.size() && r.data.size() ? '\n' + r.data : r.data;
		ret.msg  += com_list.size() && r.msg.size()  ? '\n' + r.msg  : r.msg;
	}
	return ret;
}

void Daemon::session() {
	Daemon& daemon = mod();
	try {
		while (daemon.state != EXIT) {
			daemon.out() << "Daemon waiting for request ... " << endl;
			string request = daemon.get_request();
			daemon.out() << "Daemon got a request: " << request << endl;
			if ("daemon" == request.substr(0, strlen("daemon")))
				request = request.substr(strlen("daemon"));
			boost::trim(request);
			if (request == "exit" || request == "cancel" || request == "quit") {
				daemon.out() << "Daemon exiting" << endl;
				daemon.state = EXIT;
			}
			Return ret = daemon.state == EXIT ? Return() : execute(request);
			daemon.send_response(ret.to_string());
			daemon.out() << "Daemon response is sent" << endl;
		}
	} catch (std::exception& e) {
		std::cerr << "Exception in thread: " << e.what() << endl;
	}
}

Daemon::Daemon() : endpoint(ip::tcp::v4(), conn.port),
acceptor(service, endpoint), socket(service), state(RUN_QUEUE) {
}

void Daemon::start(bool verb) {
	verbose = verb;
	out() << "Daemon executing commands..." << endl;
	execute(commands);
	out() << "done" << endl;
	while (state != EXIT) {
		if (!socket.is_open()) {
			out() << "Daemon is waiting for connection ..." << endl;
			acceptor.accept(socket);
			out() << "Daemon accepted connection" << endl;
			std::thread(Daemon::session).detach();
		} else {
			std::this_thread::sleep_for(std::chrono::seconds(1));
		}
	}
}

string Daemon::get_request() {
	if (!commands.empty()) {
		string command = commands.front();
		commands.pop();
		state = RUN_QUEUE;
		return command;
	}
	state = RUN_REQUEST;
	bool close = false;
	string ret = receive_string(socket, close);
	if (close) {
		state = CLOSE; // Connection closed cleanly by peer.
		return "";
	}
	return ret;
}

void Daemon::send_response(const string& response) {
	if (RUN_QUEUE)
		out() << response << endl;
	else if (RUN_REQUEST)
		send_string(socket, response);
}

ostream& Daemon::out() {
	static boost::iostreams::stream<boost::iostreams::null_sink> nowhere((boost::iostreams::null_sink()));
	return verbose ? cout : nowhere;
}

void Console::session() {
	Console& console = mod();
	console.connect();
	while (true) {
		console.out() << "Console waiting for request...." << endl;
		string request = console.get_command();
		if (request == "exit" || request == "cancel" || request == "quit") return;
		console.out() << "Console sending a request...." << endl;
		console.send_request(request);
		console.out() << "Console is waiting for response...." << endl;
		string response = console.get_response();
		console.out() << "Console got a response: ";
		Return ret = Return::from_string(response);
		console.out() << (ret ? "success" : "fail") << ": " << ret.msg << endl;
	}
	console.disconnect();
}

Console::Console() : resolver(service), socket(service),
endpoint(*resolver.resolve({conn.host, to_string(conn.port)})) {
}

void Console::start(bool verb) {
	verbose = verb;
	out() << "Console started" << endl;
	session();
	//std::thread(Console::session).detach();
}

void Console::connect() {
	out() << "Console connecting...." << endl;
	boost::system::error_code error;
	socket.connect(endpoint, error);
	string err;
	try {
		throw boost::system::system_error(error);
	} catch(boost::system::system_error& e) {
		err = e.what();
	}
	if (error) {
		out() << "Console connection EEROR: " << err << endl;
	} else {
		out() << "Console connected" << endl;
	}
}

void Console::disconnect() {
	socket.close();
}

string Console::get_command() {
	string command;
	if (!commands.empty()) {
		command = commands.front();
		commands.pop();
		return command;
	}
	std::getline(std::cin, command);
	return command;
}

string Console::get_response() {
	bool close = false;
	string ret = receive_string(socket, close);
	if (close) {
		disconnect(); // Connection closed cleanly by peer.
		return "";
	}
	return ret;
}

void Console::send_request(const string& request) {
	send_string(socket, request);
}

ostream& Console::out() {
	static boost::iostreams::stream<boost::iostreams::null_sink> nowhere((boost::iostreams::null_sink()));
	return verbose ? cout : nowhere;
}


}
