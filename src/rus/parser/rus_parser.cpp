#include "rus_parser_grammar.hpp"

namespace mdl { namespace rus { namespace {

void parse_src(uint label) {
	Source* src = Sys::mod().math.get<Source>().access(label);

	LocationIter iter(src->data().begin(), label);
	LocationIter end(src->data().end(), label);

	if (!parser::Grammar<LocationIter>::parse(iter, end, parser::unicode::space, *src) || iter != end) {
		throw Error("parsing failed", Lex::toStr(label));
	}
	src->parsed = true;
}

}

void parse_spirit(uint label) {
#ifdef PARALLEL_PARSE
	vector<uint> labels;
	for (auto p : Sys::mod().math.get<Source>())
		labels.push_back(p.first);
	tbb::parallel_for (tbb::blocked_range<size_t>(0, labels.size()),
		[labels] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				parse_src(labels[i]);
		}
	);
#else
	parse_src(label);
#endif
}

}} // mdl::rus
