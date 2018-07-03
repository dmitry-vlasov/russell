#include <mm_ast.hpp>

namespace mdl { namespace mm {

template<class T>
static const Tokenable* find_ref(const User<T>& user, const char* pos) {
	return user.token.includes(pos) ? user.get() : nullptr;
}

static const Tokenable* find_ref(const Ref& r, const char* pos) {
	if (r.is_assertion()) {
		return find_ref(std::get<User<Assertion>>(r.val), pos);
	}
	return nullptr;
}

static const Tokenable* find_ref(const Proof& proof, const char* pos) {
	for (const auto& e : proof.refs) {
		if (const Tokenable* tok = find_ref(e, pos)) {
			return tok;
		}
	}
	return nullptr;
}

static const Tokenable* find_ref(const Assertion* ass, const char* pos) {
	if (!ass->axiom() && ass->token.includes(pos)) {
		if (const Tokenable* tok = find_ref(ass->proof, pos)) {
			return tok;
		}
	}
	return nullptr;
}

static const Tokenable* find_ref(const Source* source, const char* pos) {
	for (const auto& n : source->contents) {
		if (Source::kind(n) == Source::ASSERTION) {
			if (const Tokenable* tok = find_ref(std::get<unique_ptr<Assertion>>(n).get(), pos)) {
				return tok;
			}
		}
	}
	return nullptr;
}

Return lookup_ref(uint src, uint line, uint col, string what) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	const char* pos = locate_position(line, col, source->data().c_str());
	const Tokenable* tok = find_ref(source, pos);
	if (what == "def")
		return tok ? Return("definition found", tok->token.str()) : Return("definition not found", false);
	else if (what == "loc")
		return tok ? Return("location found", tok->token.locate().show()) : Return("definition not found", false);
	else
		return Return("incorrect lookup mode: " + what, false);
}

}}
