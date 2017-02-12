#include "daem/globals.hpp"

namespace mdl { namespace daemon {

Command create_command(const string& c) {
	std::istringstream command(c);
	string name;
	getline(command, name, ' ');
	if (name == "lang") return [](Request req) {
		if (req.args[1] == "mm")  return Response(State(req.state.work, State::Lang::MM));
		if (req.args[1] == "smm") return Response(State(req.state.work, State::Lang::SMM));
		if (req.args[1] == "rus") return Response(State(req.state.work, State::Lang::RUS));
		return Response(State(State::Work::ERROR));
	};
	/*
	if (name == "source") return [](Request req) {
		switch (req.state.lang) {
		case State::Lang::MM:  Lib<mm::Source>::get().current  = req.args[1]; break;
		case State::Lang::SMM: Lib<smm::Source>::get().current = req.args[1]; break;
		case State::Lang::RUS: Lib<rus::Source>::get().current = req.args[1]; break;
		}
		return Response(req.state);
	};
	if (name == "read") {
		switch (req.state.lang) {
		case State::Lang::MM:  Lib<mm::Source>::get().sys().read(); break;
		case State::Lang::SMM: Lib<smm::Source>::get().sys().read(); break;
		case State::Lang::RUS: Lib<rus::Source>::get().sys().read(); break;
		}
		return Response(req.state);
	};
	*/
/*	if (name == "write")   return new Write(d, c);
	if (name == "outline") return new Outline(d, c);
	if (name == "struct")  return new Struct(d, c);
	if (name == "def")     return new Def(d, c);
	if (name == "info") return new Info(d, c);*/
	if (name == "exit") return [](Request req) { return Response(State(State::Work::EXIT), "exiting"); };
	return [](Request) { return Response(); };
}

Request create_request(const string& c, State s) {
	Request req(s);
	std::istringstream command(c);
	string arg;
	while (getline(command, arg, ' ')) req.args.push_back(arg);
	return req;
}

string get_request() {
	return "";
}
void send_response(const string& response) {

}

void Daemon::run() {
	while (state.work != State::Work::EXIT) {
		Request request = create_request(get_request(), state);
		Command command = create_command(request.args[0]);
		Response response = command(request);
		state = response.state;
		send_response(response.ret);
	}
}

}}








