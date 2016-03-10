#define BOOST_SPIRIT_USE_PHOENIX_V3

#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/karma.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_function.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/variant/recursive_variant.hpp>
#include <boost/phoenix/object/dynamic_cast.hpp>

#include "smm/ast.hpp"
#include "smm/globals.hpp"
#include "smm/adaptors.hpp"

namespace mdl { namespace smm { namespace gen {

namespace karma   = boost::spirit::karma;
namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct IntToSymbol {
	template <typename T>
	struct result { typedef string type; };
	mdl::string operator()(uint lit) const {
		return Smm::mod().lex.symbols.toStr(lit);
	}
};

struct IntToLabel {
	template <typename T>
	struct result { typedef string type; };
	mdl::string operator()(uint lab) const {
		return Smm::mod().lex.labels.toStr(lab);
	}
};

template <typename OutIterator>
struct Expr : karma::grammar<OutIterator, mdl::Expr(), ascii::space_type> {
	Expr() : Expr::base_type(exp) {
		using phoenix::at_c;
		using namespace karma::labels;
		phoenix::function<IntToSymbol> intToSymbol;
		//exp = karma::eps << vect [_1 = at_c<0>(_val)];
		exp = vect;
		vect %= symbol % ' ';
		symbol = karma::string [_1 = intToSymbol(at_c<0>(_val))];
	}
	karma::rule<OutIterator, mdl::Symbol()> symbol;
	karma::rule<OutIterator, vector<Symbol>(), ascii::space_type> vect;
	karma::rule<OutIterator, mdl::Expr(), ascii::space_type> exp;
};

template <typename OutIterator>
struct Constants : karma::grammar<OutIterator, smm::Constants(), ascii::space_type> {
	Constants() : Constants::base_type(constants) {
		constants %= karma::lit("$c") << expr.exp << "$." << karma::eol;
	}
	Expr<OutIterator> expr;
	karma::rule<OutIterator, smm::Constants(), ascii::space_type> constants;
};

template <typename OutIterator>
struct Essential : karma::grammar<OutIterator, smm::Essential()> {
	Essential() : Essential::base_type(essential) {
		using phoenix::at_c;
		using namespace karma::labels;
		phoenix::function<IntToLabel> intToLabel;
		label = karma::string [_1 = intToLabel(_val)];
		essential &= karma::lit("e") << label << " $e " << expr.exp << " $." << karma::eol;
		floating  &= karma::lit("f") << label << " $f " << expr.exp << " $." << karma::eol;
		inner     &= karma::lit("i") << label << " $i " << expr.exp << " $." << karma::eol;
	}
	Expr<OutIterator> expr;
	karma::rule<OutIterator, uint()> label;
	karma::rule<OutIterator, smm::Essential()> essential;
	karma::rule<OutIterator, smm::Floating()> floating;
	karma::rule<OutIterator, smm::Inner()> inner;
};


template <typename OutIterator>
struct Hypothesis : karma::grammar<OutIterator, smm::Essential()> {
	Hypothesis() : Hypothesis::base_type(essential) {
		using phoenix::at_c;
		using namespace karma::labels;
		phoenix::function<IntToLabel> intToLabel;
		label = karma::string [_1 = intToLabel(_val)];
		essential &= karma::lit("e") << label << " $e " << expr.exp << " $." << karma::eol;
		floating  &= karma::lit("f") << label << " $f " << expr.exp << " $." << karma::eol;
		inner     &= karma::lit("i") << label << " $i " << expr.exp << " $." << karma::eol;
	}
	Expr<OutIterator> expr;
	karma::rule<OutIterator, uint()> label;
	karma::rule<OutIterator, smm::Essential()> essential;
	karma::rule<OutIterator, smm::Floating()> floating;
	karma::rule<OutIterator, smm::Inner()> inner;
};

template <typename OutIterator>
struct Ref : karma::grammar<OutIterator, smm::Ref()> {
	Ref() : Ref::base_type(ref) {
		using phoenix::at_c;
		using phoenix::val;
		using karma::uint_;
		using namespace karma::labels;
		phoenix::function<IntToLabel> intToLabel;

		label = karma::string [_1 = intToLabel(_val)];
		ref = karma::eps(at_c<0>(_val) == val(smm::Ref::PREF_A)) << "a" << label [_1 = at_c<1>(_val)] << ascii::space
			| karma::eps(at_c<0>(_val) == val(smm::Ref::PREF_P)) << "p" << label [_1 = at_c<1>(_val)] << ascii::space
			| karma::eps(at_c<0>(_val) == val(smm::Ref::PREF_F)) << "f" << uint_ [_1 = at_c<1>(_val)] << ascii::space
			| karma::eps(at_c<0>(_val) == val(smm::Ref::PREF_I)) << "i" << uint_ [_1 = at_c<1>(_val)] << ascii::space
			| karma::eps(at_c<0>(_val) == val(smm::Ref::PREF_E)) << "e" << uint_ [_1 = at_c<1>(_val)] << ascii::space;
	}
	karma::rule<OutIterator, uint()> label;
	karma::rule<OutIterator, smm::Ref()> ref;
};

template <typename OutIterator>
struct Proof : karma::grammar<OutIterator, smm::Proof*(), ascii::space_type> {
	Proof() : Proof::base_type(proof) {
		using phoenix::at_c;
		using namespace karma::labels;
		proof = karma::eps << vect [_1 = phoenix::at_c<0>(*_val)];
		vect %= ref.ref % ' ';
	}
	Ref<OutIterator> ref;
	karma::rule<OutIterator, vector<smm::Ref>(), ascii::space_type> vect;
	karma::rule<OutIterator, smm::Proof*(), ascii::space_type> proof;
};


template <typename OutIterator>
struct Assertion : karma::grammar<OutIterator, smm::Assertion(), ascii::space_type> {
	Assertion() : Assertion::base_type(assertion) {
		using phoenix::at_c;
		using karma::lit;
		using karma::eol;
		using namespace karma::labels;
		phoenix::function<IntToLabel> intToLabel;

		variables  %= lit("$v") << expr.exp << "$." << eol;
		disjointed %= lit("$d") << expr.exp << "$." << eol;
		varsVector %= lit("\t") << variables % '\n' << eol;
		assertion  =
			lit("${") << eol
			<< varsVector [_1 = at_c<0>(_val)]
			<< "$}" << eol;
	}
	Expr<OutIterator> expr;
	karma::rule<OutIterator, vector<smm::Variables>(), ascii::space_type> varsVector;
	karma::rule<OutIterator, smm::Ref(), ascii::space_type> ref;
	karma::rule<OutIterator, smm::Proof*(), ascii::space_type> proof;
	karma::rule<OutIterator, smm::Proposition(), ascii::space_type> provable;
	karma::rule<OutIterator, smm::Proposition(), ascii::space_type> axiomatic;
	karma::rule<OutIterator, smm::Inner(), ascii::space_type> inner;
	karma::rule<OutIterator, smm::Floating(), ascii::space_type> floating;
	karma::rule<OutIterator, smm::Essential()> essential;
	karma::rule<OutIterator, smm::Variables(), ascii::space_type> variables;
	karma::rule<OutIterator, smm::Disjointed(), ascii::space_type> disjointed;
	karma::rule<OutIterator, smm::Assertion(), ascii::space_type> assertion;
};


template <typename OutIterator>
struct Source : karma::grammar<OutIterator, smm::Source(), ascii::space_type> {
	Source() : Source::base_type(source) {
		using phoenix::at_c;
		using phoenix::dynamic_cast_;
		using karma::eps;
		using karma::eol;
		using karma::string;
		using namespace karma::labels;
		source = eps(at_c<0>(_val)) << vect [_1 = at_c<2>(_val)];
		//	| << "$[" << string [_1 = at_c<1>(_val)] << "$]" << eol;
		vect %= (
			eps(dynamic_cast_<smm::Assertion*>(_val)) << ass.assertion
			| consts.constants) % "\n";
	}
	Constants<OutIterator> consts;
	Assertion<OutIterator> ass;
	karma::rule<OutIterator, vector<mdl::Showable*>(), ascii::space_type> vect;
	karma::rule<OutIterator, smm::Source(), ascii::space_type> source;
};


string expr(const mdl::Expr& ex) {
	typedef std::back_insert_iterator<std::string> outiter;
    mdl::string out;
    outiter it(out);
    karma::generate_delimited(it, Expr<outiter>(), ascii::space, ex);
    return out;
}

string constants(const smm::Constants* consts) {
	typedef std::back_insert_iterator<std::string> outiter;
    mdl::string out;
    outiter it(out);
    karma::generate_delimited(it, Constants<outiter>(), ascii::space, *consts);
    return out;
}

string assertion(const smm::Assertion* ass) {
	typedef std::back_insert_iterator<std::string> outiter;
    mdl::string out;
    outiter it(out);
    karma::generate_delimited(it, Assertion<outiter>(), ascii::space, *ass);
    return out;
}

string source(const smm::Source* src) {
	typedef std::back_insert_iterator<std::string> outiter;
    mdl::string out;
    outiter it(out);
    karma::generate_delimited(it, Source<outiter>(), ascii::space, *src);
    return out;
}

}}} // mdl::smm::gen
