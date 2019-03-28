#include <mm_ast.hpp>

namespace mdl { namespace mm {

static const Token* find_ref(const Ref& r, const char* pos) {
	if (r.is_assertion()) {
		return r.token.includes(pos) ? &r.ass()->token : nullptr;
	}
	return nullptr;
}

static const Token* find_ref(const Proof& proof, const char* pos) {
	for (const auto& e : proof.refs) {
		if (const Token* tok = find_ref(e, pos)) {
			return tok;
		}
	}
	return nullptr;
}

static const Token* find_ref(const Assertion* ass, const char* pos) {
	if (!ass->axiom() && ass->token.includes(pos)) {
		if (const Token* tok = find_ref(ass->proof, pos)) {
			return tok;
		}
	}
	return nullptr;
}

static const Token* find_ref(const Source* source, const char* pos) {
	for (const auto& n : source->contents) {
		if (Source::kind(n) == Source::ASSERTION) {
			if (const Token* tok = find_ref(std::get<unique_ptr<Assertion>>(n).get(), pos)) {
				return tok;
			}
		}
	}
	return nullptr;
}

Return lookup_ref(uint src, uint line, uint col, string what) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	const char* pos = locate_position(line, col, source->data().c_str());
	const Token* tok = find_ref(source, pos);
	if (what == "def")
		return tok ? Return("definition found", tok->str()) : Return("definition not found", false);
	else if (what == "loc")
		return tok ? Return("location found", tok->locate().show()) : Return("definition not found", false);
	else
		return Return("incorrect lookup mode: " + what, false);
}

}}
