
#include "mm/ast.hpp"
#include "mm/globals.hpp"
#include "peglib.hpp"
#include <cstdlib>

namespace mdl { namespace mm { namespace peg_parser {

using namespace peg;
using namespace std;

struct Parser {
	Definition EXPRESSION, TERM, FACTOR, TERM_OPERATOR, FACTOR_OPERATOR, NUMBER;

	Parser() {
		auto reduce = [](const SemanticValues& sv) -> long {
			auto result = sv[0].get<long>();
			for (auto i = 1u; i < sv.size(); i += 2) {
				auto num = sv[i + 1].get<long>();
				auto ope = sv[i].get<char>();
				switch (ope) {
					case '+': result += num; break;
					case '-': result -= num; break;
					case '*': result *= num; break;
					case '/': result /= num; break;
				}
			}
			return result;
		};
		EXPRESSION      <= seq(TERM, zom(seq(TERM_OPERATOR, TERM))),         reduce;
		TERM            <= seq(FACTOR, zom(seq(FACTOR_OPERATOR, FACTOR))),   reduce;
		FACTOR          <= cho(NUMBER, seq(chr('('), EXPRESSION, chr(')')));
		TERM_OPERATOR   <= cls("+-"),                                        [](const SemanticValues& sv) { return static_cast<char>(*sv.c_str()); };
		FACTOR_OPERATOR <= cls("*/"),                                        [](const SemanticValues& sv) { return static_cast<char>(*sv.c_str()); };
		NUMBER          <= oom(cls("0-9")),                                  [](const SemanticValues& sv) { return atol(sv.c_str()); };
	}

	int parse(string src) {
		long val = 0;
		if (EXPRESSION.parse_and_get_value(src.c_str(), val).ret) {
			//cout << expr << " = " << val << endl;
			return val;
		}
		return -1;
	}

};

struct SMM_Parser {
/*
	gr
	<< Nonterms({"Source", "Import", "Comment", "Const", "Block", "Var", "Disj", "Step",
		"Essential", "Floating", "Axiomatic", "Provable", "Proof"})
	<< Keywords({"$(", "$)", "$[", "$]", "${", "$}", "$c", "$v", "$d", "$f", "$e", "$a",  "$p", "$=", "$."})
	<< Keywords({"a", "f", "e", "p"})
	<< Regexp("index", "[1-9][0-9]*") << Regexp("label", "[a-zA-Z][0-9a-zA-Z_-]*")
	<< Regexp("symbol", "[^\\s]+") << Regexp("comment", "([^\\$]|\\$[^\\)])*") << Regexp("import", "([^$]|$[^\\]])*")

	<< Rule(R("Source"),    Iter(Alt({R("Comment"), R("Import"), R("Const"), R("Block")})))
	<< Rule(R("Import"),    Seq({R("$["), R("import"), R("$]")}))
	<< Rule(R("Comment"),   Seq({R("$("), R("comment"), R("$)")}))
	<< Rule(R("Const"),     Seq({R("$c"), Iter(R("symbol")), R("$.")}))
	<< Rule(R("Var"),       Seq({R("$v"), Iter(R("symbol")), R("$.")}))
	<< Rule(R("Disj"),      Seq({R("$d"), Iter(R("symbol")), R("$.")}))
	<< Rule(R("Essential"), Seq({R("e"), R("index"), R("$e"), Iter(R("symbol")), R("$.")}))
	<< Rule(R("Floating"),  Seq({R("f"), R("index"), R("$f"), Iter(R("symbol")), R("$.")}))
	<< Rule(R("Axiomatic"), Seq({R("a"), R("label"), R("$a"), Iter(R("symbol")), R("$.")}))
	<< Rule(R("Provable"),  Seq({R("p"), R("label"), R("$p"), Iter(R("symbol")), R("$="), R("Proof")}))
	<< Rule(R("Proof"),     Seq({Iter(R("Step")), R("$.")}))
	<< Rule(R("Step"),      Alt({
			Seq({R("a"), R("label")}),
			Seq({R("p"), R("label")}),
			Seq({R("e"), R("index")}),
			Seq({R("f"), R("index")})
		})
	)
	<< Rule(R("Block"),     Seq({
			R("${"),
			Iter(Alt({
				R("Var"), R("Disj"), R("Essential"), R("Floating"), R("Axiomatic"), R("Provable")
			})),
			R("$}")
		})
	)
	;
*/

	Definition SOURCE, IMPORT, COMMENT, CONST, BLOCK, VAR, DISJ, STEP,
		ESSENTIAL, FLOATING, AXIOMATIC, PROVABLE, PROOF;

	SMM_Parser() {
		auto reduce = [](const SemanticValues& sv) -> long {
			auto result = sv[0].get<long>();
			for (auto i = 1u; i < sv.size(); i += 2) {
				auto num = sv[i + 1].get<long>();
				auto ope = sv[i].get<char>();
				switch (ope) {
					case '+': result += num; break;
					case '-': result -= num; break;
					case '*': result *= num; break;
					case '/': result /= num; break;
				}
			}
			return result;
		};
		SOURCE          <= oom(cho(COMMENT, IMPORT, CONST, BLOCK)),         reduce;
		IMPORT          <= seq(lit("$["), cls, lit("$]"))
		TERM            <= seq(FACTOR, zom(seq(FACTOR_OPERATOR, FACTOR))),   reduce;
		FACTOR          <= cho(NUMBER, seq(chr('('), EXPRESSION, chr(')')));
		TERM_OPERATOR   <= cls("+-"),                                        [](const SemanticValues& sv) { return static_cast<char>(*sv.c_str()); };
		FACTOR_OPERATOR <= cls("*/"),                                        [](const SemanticValues& sv) { return static_cast<char>(*sv.c_str()); };
		NUMBER          <= oom(cls("0-9")),                                  [](const SemanticValues& sv) { return atol(sv.c_str()); };
	}

	int parse(string src) {
		long val = 0;
		if (EXPRESSION.parse_and_get_value(src.c_str(), val).ret) {
			//cout << expr << " = " << val << endl;
			return val;
		}
		return -1;
	}

};



}}} // mdl::mm::parser
