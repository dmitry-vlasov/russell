#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "mm/sys.hpp"
#include "mm/ast.hpp"
#include "mm/adaptors.hpp"

namespace mdl {
namespace mm { namespace parser {

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct VarConst {
	set<Symbol> vars;
	set<Symbol> consts;
};
typedef vector<VarConst> Stack;
struct Context {
	Context() : stack(), parent(nullptr) { }
	Stack  stack;
	Block* parent;
};

struct Grammar : qi::grammar<LocationIter, Source(), ascii::space_type> {
	struct MakeString {
		template <typename T>
		struct result { typedef string type; };
		string operator()(const vector<char>& s) const {
			return string(s.begin(), s.end());
		}
	};

	struct CreateLabel {
		template <typename T>
		struct result { typedef uint type; };
		uint operator()(const std::vector<char>& lab) const {
			string label(lab.begin(), lab.end());
			for (char& ch : label) ch = (ch == '.') ? '_' : ch;
			return Sys::mod().lex.labels.toInt(label);
		}
	};

	struct CreateSymb {
		template <typename T>
		struct result { typedef Symbol type; };
		Symbol operator()(const std::vector<char>& s) const {
			string symb(s.begin(), s.end());
			return Symbol(Sys::mod().lex.symbols.toInt(symb));
		}
	};

	struct ParseInclusion {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		Inclusion* operator()(string name, Context& context) const {
			uint label = validate(name);
			Grammar::parse(label, context);
			return new Inclusion(label);
		}
	};

	struct PushParent {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Block* block, Block*& parent) const {
			block->parent = parent;
			parent = block;
		}
	};

	struct PopParent {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Block* block, Block*& parent) const {
			parent = block->parent;
		}
	};

	struct PushNode {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Block* block, Node node) const {
			node.ind = block->contents.size();
			block->contents.push_back(node);
		}
	};

	struct PushVC {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Stack& vc, bool doit = true) const {
			if (doit) vc.push_back(VarConst());
		}
	};

	struct PopVC {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Stack& vc, bool doit = true) const {
			if (doit) vc.pop_back();
		}
	};

	struct AddVars {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Stack& vc, const Vect& vars) const {
			for (Symbol v : vars)
				vc.back().vars.insert(v);
		}
	};

	struct AddConsts {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Stack& vc, const Vect& consts) const {
			for (Symbol c : consts)
				vc.back().consts.insert(c);
		}
	};

	struct MarkVars {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Vect& expr, const Stack& stack) const {
			for (Symbol& s : expr) {
				bool is_var   = false;
				bool is_const = false;
				for (const VarConst& vc : stack) {
					if (vc.vars.find(s) != vc.vars.end()) is_var = true;
					if (vc.consts.find(s) != vc.consts.end()) is_const = true;
				}
				if (is_var && is_const)
					throw Error("constant symbol is marked as variable", show_sy(s));
				if (!is_var && !is_const)
					throw Error("symbol is neither constant nor variable", show_sy(s));
				s.var = is_var;
			}
		}
	};

	Grammar(Context& context);
	void initNames() {
		symbol.name("symbol");
		label.name("label");
		path.name("path");
		expr.name("expr");
		ref.name("ref");
		proof.name("proof");
		theorem.name("theorem");
		axiom.name("axiom");
		essential.name("essential");
		floating.name("floating");
		disjointed.name("disjointed");
		variables.name("variables");
		node.name("node");
		block.name("block");
		constants.name("constants");
		comment.name("name");
		inclusion.name("inclusion");
		source.name("source");
	}

	qi::rule<LocationIter, Vect(), ascii::space_type> expr;
	qi::rule<LocationIter, Symbol(), ascii::space_type> symbol;
	qi::rule<LocationIter, uint(),        ascii::space_type> label;
	qi::rule<LocationIter, std::string(), ascii::space_type> path;
	qi::rule<LocationIter, Ref*(), ascii::space_type> ref;
	qi::rule<LocationIter, Proof*(), ascii::space_type> proof;
	qi::rule<LocationIter, Essential*(), qi::locals<uint, Vect>, ascii::space_type> essential;
	qi::rule<LocationIter, Floating*(), qi::locals<uint, Vect>, ascii::space_type> floating;
	qi::rule<LocationIter, Disjointed*(), ascii::space_type> disjointed;
	qi::rule<LocationIter, Variables*(), ascii::space_type> variables;
	qi::rule<LocationIter, Axiom*(), qi::locals<uint, Vect>, ascii::space_type> axiom;
	qi::rule<LocationIter, Theorem*(), qi::locals<uint, Vect, Proof*>, ascii::space_type> theorem;
	qi::rule<LocationIter, Constants*(), ascii::space_type> constants;
	qi::rule<LocationIter, Node(), ascii::space_type> node;
	qi::rule<LocationIter, Block*(), ascii::space_type> block;
	qi::rule<LocationIter, Inclusion*(), ascii::space_type> inclusion;
	qi::rule<LocationIter, Comment*(), qi::unused_type> comment;
	qi::rule<LocationIter, Source(), ascii::space_type> source;

	static void parse(uint label, Context& context) {
		if (Sys::mod().math.sources.has(label)) return;
		Source* src = new Source(label);
		src->read();
		Sys::mod().math.sources.add(label, src);
		LocationIter iter(src->data.begin(), src->name());
		LocationIter end(src->data.end(), src->name());
		if (!qi::phrase_parse(iter, end, Grammar(context), qi::ascii::space, *src) || iter != end) {
			throw Error("parsing failed", src->name());
		}
	}
};

}}} // mdl::mm::parser
