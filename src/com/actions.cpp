#include "actions.hpp"

namespace mdl {

string Return::to_binary() const {
	uint len = msg.size() + data.size() + sizeof(uint) * 3;
	char array[len];
	char* arr = array;

	*reinterpret_cast<uint*>(arr) = code;
	arr += sizeof(uint);

	*reinterpret_cast<uint*>(arr) = msg.size();
	arr += sizeof(uint);
	for (char c : msg) *arr++ = c;

	*reinterpret_cast<uint*>(arr) = data.size();
	arr += sizeof(uint);
	for (char c : data) *arr++ = c;

	return string(array, len);
}

Return Return::from_binary(const string& str) {
	const char* array = str.c_str();
	Return ret;

	ret.code = *reinterpret_cast<const uint*>(array);
	array += sizeof(uint);

	uint msg_len = *reinterpret_cast<const uint*>(array);
	array += sizeof(uint);
	while (msg_len-- > 0) ret.msg += *array++;

	uint data_len = *reinterpret_cast<const uint*>(array);
	array += sizeof(uint);
	while (data_len-- > 0) ret.data += *array++;

	return ret;
}

#define ERROR_HEADER "error: "
#define DATA_HEADER  "***** DATA *****\n"

string Return::to_string() const {
	string ret;
	if (!success()) {
		ret += ERROR_HEADER + std::to_string(code) + "\n";
	}
	if (msg.size()) {
		ret += msg;
		if (msg[msg.size() - 1] != '\n') {
			ret += '\n';
		}
	}
	if (data.size()) {
		ret += DATA_HEADER;
		ret += data;
	}
	return ret;
}

Return Return::from_string(const string& str) {
	auto first_line = str.find('\n');
	auto msg_start = (str.substr(0, strlen(ERROR_HEADER)) == ERROR_HEADER) ? (first_line == string::npos ? first_line : first_line + 1) : 0;
	auto data_start = str.find(DATA_HEADER);
	Return ret;
	ret.msg = str.substr(msg_start, data_start);
	ret.data = str.substr(data_start);
	if (msg_start != 0) {
		ret.code = stoi(str.substr(strlen(ERROR_HEADER), str.find('\n')));
	}
	return ret;
}


} // mdl


