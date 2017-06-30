#include "actions.hpp"

namespace mdl {

string Return::to_string() const {
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

Return Return::from_string(const string& str) {
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

} // mdl


