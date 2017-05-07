#include "daem/sys.hpp"

namespace mdl { namespace daemon {

Lang make_args(const string& c, Args& args) {
	std::istringstream command(c);
	string lang;
	if (!getline(command, lang, ' ')) return Lang::NONE;
	string arg;
	while (getline(command, arg, ' ')) args.push_back(arg);
	return chooseLang(lang);
}

string get_request() {
	return "";
}
void send_response(const string& response) {

}

void Daemon::run() {
	while (true) {
		string request = get_request();
		if (request == "exit" || request == "cancel" || request == "quit") return;
		Args args;
		Return ret;
		Lang lang = make_args(request, args);
		switch (lang) {
		case Lang::RUS : ret = rus::Sys::mod().execute(args); break;
		case Lang::SMM : ret = smm::Sys::mod().execute(args); break;
		case Lang::MM  : ret = mm::Sys::mod().execute(args);  break;
		case Lang::NONE: cout << "no language is chosen" << endl; return;
		}
		send_response(ret.to_string());
	}
}

}}
