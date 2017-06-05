#include "daem/sys.hpp"

namespace mdl {

using namespace boost::asio;

inline bool get_nonempty_line(stringstream& ss, string& arg) {
	while (getline(ss, arg, ' ')) if (!arg.empty()) return true;
	return false;
}

Return execute(const string& command) {
	Lang lang = Lang::NONE;
	uint sys = -1;
	Args args;
	{
		stringstream str(command);
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
	case Lang::SMM : ret = smm::Sys::exec_and_show(args); break;
	case Lang::MM  : ret =  mm::Sys::exec_and_show(args); break;
	case Lang::NONE: return Return("unknown language, command: " + command, false);
	}
	return ret;
}

void Daemon::session() {
	Daemon& daemon = mod();
	try {
		while (daemon.state != EXIT) {
			cout << "Waiting for request ... " << endl;
			string request = daemon.get_request();
			cout << "Got a request: " << request << endl;
			if ("daemon" == request.substr(0, strlen("daemon")))
				request = request.substr(strlen("daemon"));
			boost::trim(request);
			if (request == "exit" || request == "cancel" || request == "quit") {
				cout << "Exiting" << endl;
				daemon.state = EXIT;
			}
			Return ret = daemon.state == EXIT ? Return() : execute(request);
			cout << "Making a response: " << ret.to_string() << endl;
			daemon.send_response(ret.to_string() + "\n");
			cout << "Response is sent" << endl;
		}
	} catch (std::exception& e) {
		std::cerr << "Exception in thread: " << e.what() << endl;
	}
}

Daemon::Daemon() : endpoint(ip::tcp::v4(), conn.port),
acceptor(service, endpoint), socket(service), state(RUN_QUEUE) {
}

void Daemon::start() {
	cout << "Daemon executing commands..." << endl;
	execute(commands);
	cout << "done" << endl;
	while (state != EXIT) {
		cout << "Daemon is waiting for connection ..." << endl;
		acceptor.accept(socket);
		cout << "Daemon accepted connection" << endl;
		session();
		//std::thread(Daemon::session).detach();
	}
}

string Daemon::get_request() {
	if (!commands.empty()) {
		string command = commands.front();
		commands.pop();
		state = RUN_QUEUE;
		return command;
	}
	boost::system::error_code error;
	size_t length = socket.read_some(boost::asio::buffer(buffer), error);
	if (error == boost::asio::error::eof) {
		state = CLOSE; // Connection closed cleanly by peer.
		return "";
	} else if (error) {
		throw boost::system::system_error(error); // Some other error.
	}
	state = RUN_REQUEST;
	return string(buffer, length);
}


void Daemon::send_response(const string& response) {
	if (RUN_QUEUE)
		cout << response << endl;
	else if (RUN_REQUEST)
		boost::asio::write(socket, boost::asio::buffer(response.c_str(), response.size()));
}

void Console::session() {
	Console& console = mod();
	console.connect();
	while (true) {
		cout << "Console waiting for request...." << endl;
		string request = console.get_command();
		cout << "Console got a request: " << request << endl;
		if (request == "exit" || request == "cancel" || request == "quit") return;
		cout << "Console sending a request...." << endl;
		console.send_request(request);
		cout << "Console is waiting for response...." << endl;
		string response = console.get_response();
		cout << "Console got a response:" << response << endl;
		Return ret = Return::from_string(response);
		cout << (ret ? "success" : "fail") << ": " << ret.text << endl;
	}
	console.disconnect();
}

Console::Console() : resolver(service), socket(service),
endpoint(*resolver.resolve({conn.host, to_string(conn.port)})), message_size(-1) {
}

void Console::start() {
	cout << "Console started" << endl;
	session();
	//std::thread(Console::session).detach();
}

void Console::connect() {
	cout << "Console connecting...." << endl;
	boost::system::error_code error;
	socket.connect(endpoint, error);
	string err;
	try {
		throw boost::system::system_error(error);
	} catch(boost::system::system_error& e) {
		err = e.what();
	}
	if (error) {
		cout << "Console connection EEROR: " << err << endl;
	} else {
		cout << "Console connected" << endl;
	}
}

void Console::disconnect() {
	socket.close();
}

size_t Console::read_complete(const boost::system::error_code& err, size_t bytes) const {
	if (err) return 0;
	bool found = std::find(buff, buff + bytes, '\n') < buff + bytes;
	// we read one-by-one until we get to enter, no buffering
	return found ? 0 : 1;
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
	message_size = read(socket, boost::asio::buffer(buff), boost::bind(&Console::read_complete, this, _1, _2));
	return message_size ? std::string(buff, message_size - 1) : "";
}

void Console::send_request(const string& request) {
	socket.write_some(boost::asio::buffer(request));
}

}
