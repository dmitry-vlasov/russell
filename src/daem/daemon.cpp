#include "daem/sys.hpp"

namespace mdl { namespace daemon {

inline Lang make_args(const string& c, Args& args) {
	std::istringstream command(c);
	string lang;
	if (!getline(command, lang, ' ')) return Lang::NONE;
	string arg;
	while (getline(command, arg, ' ')) args.push_back(arg);
	return chooseLang(lang);
}

void Daemon::session() {
	Daemon& daemon = mod();
	try {
		while (true) {
			string request = daemon.get_request();
			if (request == "exit" || request == "cancel" || request == "quit") {
				daemon.state = EXIT;
				return;
			}
			Args args;
			Return ret;
			Lang lang = make_args(request, args);
			switch (lang) {
			case Lang::RUS : ret = rus::Sys::mod().execute(args); break;
			case Lang::SMM : ret = smm::Sys::mod().execute(args); break;
			case Lang::MM  : ret = mm::Sys::mod().execute(args);  break;
			case Lang::NONE: cout << "no language is chosen" << endl; return;
			}
			daemon.send_response(ret.to_string());
		}
	} catch (std::exception& e) {
		std::cerr << "Exception in thread: " << e.what() << endl;
	}
}

Daemon::Daemon() : config(), endpoint(ip::tcp::v4(), config.port),
acceptor(service, endpoint), socket(service), state(RUN) {
	while (state != EXIT) {
		acceptor.accept(socket);
		std::thread(Daemon::session).detach();
	}
}

string Daemon::get_request() {
	boost::system::error_code error;
	  size_t length = socket.read_some(boost::asio::buffer(buffer), error);
	  if (error == boost::asio::error::eof) {
		state = CLOSE; // Connection closed cleanly by peer.
		return "";
	  } else if (error) {
		throw boost::system::system_error(error); // Some other error.
	  }
	return string(buffer, length);
}


void Daemon::send_response(const string& response) {
	boost::asio::write(socket, boost::asio::buffer(response.c_str(), response.size()));
}

void Console::session() {
	Console& console = mod();
	for (std::string request; std::getline(std::cin, request);) {
		if (request == "exit" || request == "cancel" || request == "quit") return;
		console.send_request(request);
		string response = console.get_response();
		Return ret = Return::from_string(response);
		cout << (ret ? "success" : "fail") << ": " << ret.text << endl;
	}
}

Console::Console() : config(), resolver(service), socket(service),
endpoint(*resolver.resolve({config.host, to_string(config.port)})), message_size(-1) {
	socket.connect(endpoint);
	std::thread(&Console::session).detach();
}

size_t Console::read_complete(const boost::system::error_code& err, size_t bytes) const {
	if (err) return 0;
	bool found = std::find(buff, buff + bytes, '\n') < buff + bytes;
	// we read one-by-one until we get to enter, no buffering
	return found ? 0 : 1;
}

string Console::get_response() {
	message_size = 0;
	read(socket, boost::asio::buffer(buff), boost::bind(&Console::read_complete, this, _1, _2));
	return std::string(buff, message_size);
}

void Console::send_request(const string& request) {
	socket.write_some(boost::asio::buffer(request));
}

}}
