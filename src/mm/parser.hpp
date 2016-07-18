#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "mm/ast.hpp"
#include "mm/globals.hpp"
#include "mm/adaptors.hpp"

namespace mdl { namespace mm {

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct MakeString {
	template <typename T>
	struct result { typedef string type; };
	string operator()(const vector<char>& s) const {
		return string(s.begin(), s.end());
	}
};

struct AddToMath {
	template<typename T>
	struct result { typedef void type; };
	void operator()(Floating* flo) const {
		Mm::mod().math.floatings[flo->label] = flo;
	}
	void operator()(Essential* ess) const {
		Mm::mod().math.essentials[ess->label] = ess;
	}
	void operator()(Axiom* ax) const {
		Mm::mod().math.axioms[ax->label] = ax;
	}
	void operator()(Theorem* th) const {
		Mm::mod().math.theorems[th->label] = th;
	}
};

struct SymbolToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& symb) const {
		string symbol(symb.begin(), symb.end());
		return Mm::mod().lex.symbols.toInt(symbol);
	}
};

struct LabelToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& lab) const {
		string label(lab.begin(), lab.end());
		for (char& ch : label) ch = (ch == '.') ? '_' : ch;
		return Mm::mod().lex.labels.toInt(label);
	}
};

struct ParseInclusion {
	template <typename T1>
	struct result { typedef void type; };
	Inclusion* operator()(const string& path) const {
		static Set<string> included;
		if (included.has(path)) return nullptr;
		included.s.insert(path);
		return new Inclusion(parse(path));
	}
};

struct CreateRef {
	template <typename T>
	struct result { typedef Ref type; };
	Ref operator()(uint lab) const {
		Mm::Math& math = Mm::mod().math;
		if (math.floatings.has(lab))
			return Ref(math.floatings[lab]);
		else if (math.essentials.has(lab))
			return Ref(math.essentials[lab]);
		else if (math.axioms.has(lab))
			return Ref(math.axioms[lab]);
		else if (math.theorems.has(lab))
			return Ref(math.theorems[lab]);
		else
			throw Error("unknown label in proof", Mm::get().lex.labels.toStr(lab));
	}
};

/*
template<typename Iterator>
struct SetLocation {
    template <typename T1, typename T2>
    struct result { typedef void type; };
    void operator()(Assertion* ass, Iterator it) const {
    	ass->loc = it.loc;
    }
};
*/

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

    	//cout << "pushing: " << node.type << endl << node << endl;

    	if (node.type == Node::NONE) {
    		//cout << "NULL NODE: " << endl;
    		return;
    	}

    	//if (node.type == Node::COMMENT)
    	//	cout << "COMMM: " << node.val.com->text << endl;

    	node.ind = block->contents.size();
    	block->contents.push_back(node);
    }
};

struct VarConst {
	set<Symbol> vars;
	set<Symbol> consts;
};

typedef vector<VarConst> Stack;

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
    void operator()(Stack& vc, const Expr& vars) const {
    	for (Symbol v : vars.symbols)
			vc.back().vars.insert(v);
    }
};

struct AddConsts {
    template <typename T1, typename T2>
    struct result { typedef void type; };
    void operator()(Stack& vc, const Expr& consts) const {
    	for (Symbol c : consts.symbols)
			vc.back().consts.insert(c);
    }
};

struct MarkVars {
    template <typename T1, typename T2>
    struct result { typedef void type; };
    void operator()(Expr& expr, const Stack& stack) const {
    	for (Symbol& s : expr.symbols) {
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

/*struct Final {
    template <typename T1>
    struct result { typedef void type; };
    void operator()(const Block* block) const {
    	cout << "source parsed" << endl;
    	cout << "size: " << block->contents.size() << endl;
    }
};*/

/*
template <typename Iterator>
struct Comments : qi::grammar<Iterator> {
	Comments() : Comments::base_type(start) {
		qi::char_type char_;
		ascii::space_type space;
		start = space | "$(" >> *(char_ - "$)") >> "$)";
	}
	qi::rule<Iterator> start;
};
*/
template <typename Iterator>
struct Grammar : qi::grammar<Iterator, Source*(), ascii::space_type> {
	Grammar();
	void initNames();

	qi::rule<Iterator, Expr(), ascii::space_type> expr;
	qi::rule<Iterator, Symbol(), ascii::space_type> symbol;
	qi::rule<Iterator, uint(),        ascii::space_type> label;
	qi::rule<Iterator, std::string(), ascii::space_type> path;
	qi::rule<Iterator, Ref(), ascii::space_type> ref;
	qi::rule<Iterator, Proof*(), ascii::space_type> proof;
	qi::rule<Iterator, Essential*(), qi::locals<uint>, ascii::space_type> essential;
	qi::rule<Iterator, Floating*(), qi::locals<uint>, ascii::space_type> floating;
	qi::rule<Iterator, Disjointed*(), ascii::space_type> disjointed;
	qi::rule<Iterator, Variables*(), ascii::space_type> variables;
	qi::rule<Iterator, Axiom*(), qi::locals<uint>, ascii::space_type> axiom;
	qi::rule<Iterator, Theorem*(), qi::locals<uint>, ascii::space_type> theorem;
	qi::rule<Iterator, Constants*(), ascii::space_type> constants;
	qi::rule<Iterator, Node(), ascii::space_type> node;
	qi::rule<Iterator, Block*(), ascii::space_type> block;
	qi::rule<Iterator, Inclusion*(), ascii::space_type> inclusion;
	qi::rule<Iterator, Comment*(), ascii::space_type> comment;
	qi::rule<Iterator, Source*(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
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

}} // mdl::mm
