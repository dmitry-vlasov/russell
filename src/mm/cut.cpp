#define BOOST_SPIRIT_USE_PHOENIX_V3

#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>

#include "mm/sys.hpp"

namespace mdl { namespace mm {

#define PARAGRAPH_STR "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
#define CHAPTER_STR   "#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
#define PART_STR      "###############################################################################"

#define FULL_PARAGRAPH_STR "$(\n=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
#define FULL_CHAPTER_STR   "$(\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
#define FULL_PART_STR      "$(\n###############################################################################"

enum class Type { PARAGRAPH, CHAPTER, PART, SOURCE };

inline string border(const Type tp) {
	switch (tp) {
	case Type::PARAGRAPH : return PARAGRAPH_STR;
	case Type::CHAPTER   : return CHAPTER_STR;
	case Type::PART      : return PART_STR;
	case Type::SOURCE    : return "";
	default        : return "<none>";
	}
}

namespace fs = boost::filesystem;

struct Section {
	Section() : type(Type::SOURCE), header(), name(), footer(),
	contents(), root(), dir(), file(), path(),
	prev_sect(nullptr), next_sect(nullptr),
	prev_sibling(nullptr), next_sibling(nullptr),
	parent(nullptr), parts() { }
	~ Section() {
		for (auto* p : parts) delete p;
		for (auto* i : incs)  delete i;
	}
	void save() const {
		string fd = root + dir;
		if (fd.size() && !fs::exists(fd))
			fs::create_directories(fd);
		ofstream out(root + path);
		out << show() << endl;
		for (Section* s : parts) {
			out << "$[ " << s->path << " $]\n";
		}
		out.close();
	}
	void split() {
		if (type == Type::PARAGRAPH) return;
		string cont = contents;
		boost::trim(cont);
		if (!cont.size()) return;

		Section* header = new Section;
		header->name = name;
		header->footer = footer;
		header->contents = contents;

		header->root = root;
		header->file = file;
		header->dir = dir + file + "/";
		header->path = header->dir + header->file + ".mm";

		switch (type) {
		case Type::PARAGRAPH: assert(false && "impossible"); break;
		case Type::CHAPTER:   header->type = Type::PARAGRAPH; break;
		case Type::PART:      header->type = Type::CHAPTER;   break;
		case Type::SOURCE:    header->type = Type::PART;      break;
		}
		contents.clear();

		header->prev_sect = prev_sect;
		header->next_sect = this;
		header->prev_sect->next_sect = header;
		header->next_sect->prev_sect = header;

		header->prev_sibling = nullptr;
		header->next_sibling = header->next_sect;
		header->next_sibling->prev_sibling = header;
		incs.push_back(header);
	}
	string show() const {
		string str;
		const Section* imp = this;
		while (imp && !imp->prev_sibling)
			imp = imp->parent;
		if (imp)
			str += "\n$[ " + imp->prev_sibling->path + " $]\n\n";
		if (type != Type::SOURCE) {
			str += "$(\n";
			str += header;
			str += border(type);
			str += name;
			str += border(type);
			str += footer;
			str += "$)\n";
		}
		str += contents;
		return str;
	}

	Type   type;
	string header;
	string name;
	string footer;
	string contents;

	string root;
	string dir;
	string file;
	string path;

	Section* prev_sect;
	Section* next_sect;
	Section* prev_sibling;
	Section* next_sibling;
	Section* parent;
	vector<Section*> incs;
	vector<Section*> parts;
};

}} // mdl::mm

#include "cut_adaptor.hpp"

namespace mdl { namespace mm {

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

namespace {

string init_dir (Section* sect) {
	string dir;
	const Section* par = sect->parent;
	while (par && par->file.size()) {
		if (par->parent)
			dir = par->file + "/" + dir;
		else
			dir = par->dir + par->file + "/" + dir;
		par = par->parent;
	}
	return dir;
}

void init_paths(Section* sect) {
	static set<string> names;
	string dir = init_dir(sect);
	bool has_endline = (*sect->name.rbegin() == '\n');

	string orig_name = sect->name;
	boost::trim_right(orig_name);
	for (int i = 0; names.count(dir + sect->name); ++i) {
		sect->name = orig_name + "_" + to_string(i);
		//cout << "making new name: " << sect->name << endl;
	}
	names.insert(dir + sect->name);
	if (has_endline) sect->name += '\n';

	if (!sect->file.size()) {
		sect->file = sect->name;
		boost::trim(sect->file);
		boost::replace_all(sect->file, " ", "_");
		boost::replace_all(sect->file, "/", "_");
		boost::replace_all(sect->file, ":", "_");
		boost::replace_all(sect->file, ".", "_");
		boost::replace_all(sect->file, "?", "_");
		boost::replace_all(sect->file, "!", "_");
		boost::replace_all(sect->file, "$", "_");
		boost::replace_all(sect->file, "\\", "_");
		boost::replace_all(sect->file, "'", "_");
		sect->dir = dir;
		sect->path = sect->dir + sect->file + ".mm";
	}
}

struct Stack {
	Stack() :
	source(nullptr), part(nullptr), chapter(nullptr),
	paragraph(nullptr), last(nullptr) { }
	Section* source;
	Section* part;
	Section* chapter;
	Section* paragraph;
	Section* last;
};

static Stack stack;

struct Add {
	template<typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Section* sect, string root) const {
		sect->root = root;
		sect->prev_sect = stack.last;
		if (stack.last)
			stack.last->next_sect = sect;
		stack.last = sect;
		switch (sect->type) {
		case Type::PARAGRAPH:
			//cout << "paragraph: " << sect->name << endl;
			if (!stack.chapter) throw Error("empty chapter");
			sect->parent = stack.chapter;
			stack.chapter->parts.push_back(sect);
			sect->prev_sibling = stack.paragraph;
			if (stack.paragraph)
				stack.paragraph->next_sibling = sect;
			stack.paragraph = stack.chapter->parts.back();
			break;
		case Type::CHAPTER:
			//cout << "chapter: " << sect->name << endl;
			if (!stack.part) throw Error("empty part");
			sect->parent = stack.part;
			stack.part->parts.push_back(sect);
			sect->prev_sibling = stack.chapter;
			if (stack.chapter)
				stack.chapter->next_sibling = sect;
			stack.chapter = stack.part->parts.back();
			stack.paragraph = nullptr;
			break;
		case Type::PART:
			//cout << "part: " << sect->name << endl;
			if (!stack.source) throw Error("empty source");
			sect->parent = stack.source;
			stack.source->parts.push_back(sect);
			sect->prev_sibling = stack.part;
			if (stack.part)
				stack.part->next_sibling = sect;
			stack.part = stack.source->parts.back();
			stack.chapter = nullptr;
			stack.paragraph = nullptr;
			break;
		case Type::SOURCE:
			//cout << "source: " << sect->name << endl;
			if (stack.source) throw Error("source already added");
			sect->parent = nullptr;
			stack.source = sect;
			stack.part = nullptr;
			stack.chapter = nullptr;
			stack.paragraph = nullptr;
			break;
		default: throw Error("impossible");
		}
		init_paths(sect);
	}
	void operator()(string& str) const {
		stack.last->contents += str;
	}
};

struct MakeString {
	template <typename T>
	struct result { typedef string type; };
	string operator()(const vector<char>& s) const {
		return string(s.begin(), s.end());
	}
};

struct Grammar : qi::grammar<LocationIter, Section*(), qi::unused_type> {
	Grammar(string r) : Grammar::base_type(source, "cut"), root(r) {
		using qi::lit;
		using qi::uint_;
		using qi::lexeme;
		using qi::eps;
		using namespace qi::labels;
		using phoenix::at_c;
		using phoenix::new_;

		const phoenix::function<Add> add;
		const phoenix::function<MakeString> makeString;

		border =
			  lit(PARAGRAPH_STR) [_val = Type::PARAGRAPH]
			| lit(CHAPTER_STR)   [_val = Type::CHAPTER]
			| lit(PART_STR)      [_val = Type::PART];

		header %= lexeme[+(ascii::char_ - FULL_PART_STR)];

		section =
			   lit("$(\n")                         [_val = new_<Section>()]
			>> lexeme[*(ascii::char_ - "##" - "#*" - "=-")] [at_c<1>(*_val) = makeString(_1)]
			>> border                              [at_c<0>(*_val) = _1]
			>> lexeme[+(ascii::char_ - "##" - "#*" - "=-")] [at_c<2>(*_val) = makeString(_1)]
			>> border
			>> lexeme[*(ascii::char_ - "$)")]      [at_c<3>(*_val) = makeString(_1)]
			>> lit("$)\n")                         [add(_val, phoenix::ref(root))];

		contents =
			lexeme[+(ascii::char_ - FULL_PARAGRAPH_STR - FULL_CHAPTER_STR - FULL_PART_STR)] [_val = makeString(_1)];

		source =
			  eps         [add(_val, phoenix::ref(root))]
			>> header
			>> + (
				section |
				contents  [add(_1)]
			);

		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << _4
			<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
			<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
		initNames();
	}

	void initNames() {
		border.name("border");
		header.name("header");
		section.name("section");
		contents.name("contents");
		source.name("source");
	}

	string root;

	qi::rule<LocationIter, Type(), qi::unused_type> border;
	qi::rule<LocationIter, string(), qi::unused_type> header;
	qi::rule<LocationIter, Section*(), qi::unused_type> section;
	qi::rule<LocationIter, string(), qi::unused_type> contents;
	qi::rule<LocationIter, Section*(), qi::unused_type> source;
};

static pair<string, string> patches[] = {
{R"($( [18-Mar-2007] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Derive the Power Set, Infinity and Choice Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Derive the Axiom of Power Sets ~ ax-pow from the Tarksi-Grothendieck
       axiom ~ ax-groth .  That it follows is mentioned by Bob Solovay at
       ~ http://www.cs.nyu.edu/pipermail/fom/2008-March/012783.html .  Note
       that ~ ax-pow is not used by the proof.  (Contributed by G&eacute;rard
       Lang, 22-Jun-2009.) $)
    grothpw $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=)",
R"($( [18-Mar-2007] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Derive the Power Set, Infinity and Choice Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z w v u f $.
    $( Derive the Axiom of Power Sets ~ ax-pow from the Tarksi-Grothendieck
       axiom ~ ax-groth .  That it follows is mentioned by Bob Solovay at
       ~ http://www.cs.nyu.edu/pipermail/fom/2008-March/012783.html .  Note
       that ~ ax-pow is not used by the proof.  (Contributed by G&eacute;rard
       Lang, 22-Jun-2009.) $)
    grothpw $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=)"
},
{R"($(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Linear, continuous, bounded, Hermitian, unitary operators and norms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t u v w x y z $.
    $( Define the norm of a Hilbert space operator.  (Contributed by NM,
       18-Jan-2006.)  (New usage is discouraged.) $)
    df-nmop $a |- normop = ( t e. ( ~H ^m ~H ) |-> sup (
       { x | E. z e. ~H ( ( normh ` z ) <_ 1 /\ x = ( normh ` ( t ` z ) ) ) } ,
              RR* , < ) ) $.

    $( Define the set of continuous operators on Hilbert space.  For every
       "epsilon" ( ` y ` ) there is an "delta" ( ` z ` ) such that...
       (Contributed by NM, 28-Jan-2006.)  (New usage is discouraged.) $)
    df-cnop $a |- ConOp = { t e. ( ~H ^m ~H ) | A. x e. ~H A. y e. RR+
                E. z e. RR+ A. w e. ~H ( ( normh ` ( w -h x ) ) < z ->
                ( normh ` ( ( t ` w ) -h ( t ` x ) ) ) < y ) } $.

    $( Define the set of linear operators on Hilbert space.  (See ~ df-hosum
       for definition of operator.)  (Contributed by NM, 18-Jan-2006.)
       (New usage is discouraged.) $)
    df-lnop $a |- LinOp = { t e. ( ~H ^m ~H ) |
           A. x e. CC A. y e. ~H A. z e. ~H
       ( t ` ( ( x .h y ) +h z ) ) = ( ( x .h ( t ` y ) ) +h ( t ` z ) ) } $.

    $( Define the set of bounded linear Hilbert space operators.  (See
       ~ df-hosum for definition of operator.)  (Contributed by NM,
       18-Jan-2006.)  (New usage is discouraged.) $)
    df-bdop $a |- BndLinOp = { t e. LinOp | ( normop ` t ) < +oo } $.

    $( Define the set of unitary operators on Hilbert space.  (Contributed by
       NM, 18-Jan-2006.)  (New usage is discouraged.) $)
    df-unop $a |- UniOp = { t | ( t : ~H -onto-> ~H /\
         A. x e. ~H A. y e. ~H ( ( t ` x ) .ih ( t ` y ) ) = ( x .ih y ) ) } $.

    $( Define the set of Hermitian operators on Hilbert space.  Some books call
       these "symmetric operators" and others call them "self-adjoint
       operators," sometimes with slightly different technical meanings.
       (Contributed by NM, 18-Jan-2006.)  (New usage is discouraged.) $)
    df-hmop $a |- HrmOp = { t e. ( ~H ^m ~H ) | A. x e. ~H A. y e. ~H
                   ( x .ih ( t ` y ) ) = ( ( t ` x ) .ih y ) } $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Linear and continuous functionals and norms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Define the norm of a Hilbert space functional.  (Contributed by NM,
       11-Feb-2006.)  (New usage is discouraged.) $)
    df-nmfn $a |- normfn = ( t e. ( CC ^m ~H ) |-> sup (
         { x | E. z e. ~H ( ( normh ` z ) <_ 1 /\ x = ( abs ` ( t ` z ) ) ) } ,
              RR* , < ) ) $.

    $( Define the null space of a Hilbert space functional.  (Contributed by
       NM, 11-Feb-2006.)  (New usage is discouraged.) $)
    df-nlfn $a |- null = ( t e. ( CC ^m ~H ) |-> ( `' t " { 0 } ) ) $.

    $( Define the set of continuous functionals on Hilbert space.  For every
       "epsilon" ( ` y ` ) there is an "delta" ( ` z ` ) such that...
       (Contributed by NM, 11-Feb-2006.)  (New usage is discouraged.) $)
    df-cnfn $a |- ConFn = { t e. ( CC ^m ~H ) | A. x e. ~H A. y e. RR+
      E. z e. RR+ A. w e. ~H ( ( normh ` ( w -h x ) ) < z ->
      ( abs ` ( ( t ` w ) - ( t ` x ) ) ) < y ) } $.

    $( Define the set of linear functionals on Hilbert space.  (Contributed by
       NM, 11-Feb-2006.)  (New usage is discouraged.) $)
    df-lnfn $a |- LinFn = { t e. ( CC ^m ~H ) |
           A. x e. CC A. y e. ~H A. z e. ~H
       ( t ` ( ( x .h y ) +h z ) ) = ( ( x x. ( t ` y ) ) + ( t ` z ) ) } $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Adjoint
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Define the adjoint of a Hilbert space operator (if it exists).  The
       domain of ` adjh ` is the set of all adjoint operators.  Definition of
       adjoint in [Kalmbach2] p. 8.  Unlike Kalmbach (and most authors), we do
       not demand that the operator be linear, but instead show (in ~ adjbdln )
       that the adjoint exists for a bounded linear operator.  (Contributed by
       NM, 20-Feb-2006.)  (New usage is discouraged.) $)
    df-adjh $a |- adjh = { <. t , u >. | ( t : ~H --> ~H /\ u : ~H --> ~H /\
         A. x e. ~H A. y e. ~H ( ( t ` x ) .ih y ) = ( x .ih ( u ` y ) ) ) } $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Dirac bra-ket notation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Define the bra of a vector used by Dirac notation.  Based on definition
       of bra in [Prugovecki] p. 186 (p. 180 in 1971 edition).  In Dirac
       bra-ket notation, ` <. A | B >. ` is a complex number equal to the inner
       product ` ( B .ih A ) ` .  But physicists like to talk about the
       individual components ` <. A | ` and ` | B >. ` , called bra and ket
       respectively.  In order for their properties to make sense formally, we
       define the ket ` | B >. ` as the vector ` B ` itself, and the bra
       ` <. A | ` as a functional from ` ~H ` to ` CC ` .  We represent the
       Dirac notation ` <. A | B >. ` by ` ( ( bra `` A ) `` B ) ` ; see
       ~ braval .  The reversal of the inner product arguments not only makes
       the bra-ket behavior consistent with physics literature (see comments
       under ~ ax-his3 ) but is also required in order for the associative law
       ~ kbass2 to work.

       Our definition of bra and the associated outer product ~ df-kb differs
       from, but is equivalent to, a common approach in the literature that
       makes use of mappings to a dual space.  Our approach eliminates the need
       to have a parallel development of this dual space and instead keeps
       everything in Hilbert space.

       _For an extensive discussion about how our notation maps to the bra-ket
       notation in physics textbooks, see
       ~ http://us.metamath.org/mpegif/mmnotes.txt , under the 17-May-2006
       entry_.  (Contributed by NM, 15-May-2006.)
       (New usage is discouraged.) $)
    df-bra $a |- bra = ( x e. ~H |-> ( y e. ~H |-> ( y .ih x ) ) ) $.

    $( Define a commuted bra and ket juxtaposition used by Dirac notation.  In
       Dirac notation, ` | A >. ` ` <. B | ` is an operator known as the outer
       product of ` A ` and ` B ` , which we represent by ` ( A ketbra B ) ` .
       Based on Equation 8.1 of [Prugovecki] p. 376.  This definition, combined
       with definition ~ df-bra , allows any legal juxtaposition of bras and
       kets to make sense formally and also to obey the associative law when
       mapped back to Dirac notation.  (Contributed by NM, 15-May-2006.)
       (New usage is discouraged.) $)
    df-kb $a |- ketbra = ( x e. ~H , y e. ~H |->
                          ( z e. ~H |-> ( ( z .ih y ) .h x ) ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Positive operators
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Define positive operator ordering.  Definition VI.1 of [Retherford]
       p. 49.  Note that ` ( ~H X. 0H ) <_op T ` means that ` T ` is a positive
       operator.  (Contributed by NM, 23-Jul-2006.)
       (New usage is discouraged.) $)
    df-leop $a |- <_op = { <. t , u >. | ( ( u -op t ) e. HrmOp /\
               A. x e. ~H 0 <_ ( ( ( u -op t ) ` x ) .ih x ) ) } $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Eigenvectors, eigenvalues, spectrum
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Define the eigenvector function.  Theorem ~ eleigveccl shows that
       ` eigvec `` T ` , the set of eigenvectors of Hilbert space operator
       ` T ` , are Hilbert space vectors.  (Contributed by NM, 11-Mar-2006.)
       (New usage is discouraged.) $)
    df-eigvec $a |- eigvec = ( t e. ( ~H ^m ~H ) |->
         { x e. ( ~H \ 0H ) | E. z e. CC ( t ` x ) = ( z .h x ) } ) $.
)",
R"($(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Linear, continuous, bounded, Hermitian, unitary operators and norms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t u v w x y z $.
    $( Define the norm of a Hilbert space operator.  (Contributed by NM,
       18-Jan-2006.)  (New usage is discouraged.) $)
    df-nmop $a |- normop = ( t e. ( ~H ^m ~H ) |-> sup (
       { x | E. z e. ~H ( ( normh ` z ) <_ 1 /\ x = ( normh ` ( t ` z ) ) ) } ,
              RR* , < ) ) $.

    $( Define the set of continuous operators on Hilbert space.  For every
       "epsilon" ( ` y ` ) there is an "delta" ( ` z ` ) such that...
       (Contributed by NM, 28-Jan-2006.)  (New usage is discouraged.) $)
    df-cnop $a |- ConOp = { t e. ( ~H ^m ~H ) | A. x e. ~H A. y e. RR+
                E. z e. RR+ A. w e. ~H ( ( normh ` ( w -h x ) ) < z ->
                ( normh ` ( ( t ` w ) -h ( t ` x ) ) ) < y ) } $.

    $( Define the set of linear operators on Hilbert space.  (See ~ df-hosum
       for definition of operator.)  (Contributed by NM, 18-Jan-2006.)
       (New usage is discouraged.) $)
    df-lnop $a |- LinOp = { t e. ( ~H ^m ~H ) |
           A. x e. CC A. y e. ~H A. z e. ~H
       ( t ` ( ( x .h y ) +h z ) ) = ( ( x .h ( t ` y ) ) +h ( t ` z ) ) } $.

    $( Define the set of bounded linear Hilbert space operators.  (See
       ~ df-hosum for definition of operator.)  (Contributed by NM,
       18-Jan-2006.)  (New usage is discouraged.) $)
    df-bdop $a |- BndLinOp = { t e. LinOp | ( normop ` t ) < +oo } $.

    $( Define the set of unitary operators on Hilbert space.  (Contributed by
       NM, 18-Jan-2006.)  (New usage is discouraged.) $)
    df-unop $a |- UniOp = { t | ( t : ~H -onto-> ~H /\
         A. x e. ~H A. y e. ~H ( ( t ` x ) .ih ( t ` y ) ) = ( x .ih y ) ) } $.

    $( Define the set of Hermitian operators on Hilbert space.  Some books call
       these "symmetric operators" and others call them "self-adjoint
       operators," sometimes with slightly different technical meanings.
       (Contributed by NM, 18-Jan-2006.)  (New usage is discouraged.) $)
    df-hmop $a |- HrmOp = { t e. ( ~H ^m ~H ) | A. x e. ~H A. y e. ~H
                   ( x .ih ( t ` y ) ) = ( ( t ` x ) .ih y ) } $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Linear and continuous functionals and norms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t u v w x y z $.
    $( Define the norm of a Hilbert space functional.  (Contributed by NM,
       11-Feb-2006.)  (New usage is discouraged.) $)
    df-nmfn $a |- normfn = ( t e. ( CC ^m ~H ) |-> sup (
         { x | E. z e. ~H ( ( normh ` z ) <_ 1 /\ x = ( abs ` ( t ` z ) ) ) } ,
              RR* , < ) ) $.

    $( Define the null space of a Hilbert space functional.  (Contributed by
       NM, 11-Feb-2006.)  (New usage is discouraged.) $)
    df-nlfn $a |- null = ( t e. ( CC ^m ~H ) |-> ( `' t " { 0 } ) ) $.

    $( Define the set of continuous functionals on Hilbert space.  For every
       "epsilon" ( ` y ` ) there is an "delta" ( ` z ` ) such that...
       (Contributed by NM, 11-Feb-2006.)  (New usage is discouraged.) $)
    df-cnfn $a |- ConFn = { t e. ( CC ^m ~H ) | A. x e. ~H A. y e. RR+
      E. z e. RR+ A. w e. ~H ( ( normh ` ( w -h x ) ) < z ->
      ( abs ` ( ( t ` w ) - ( t ` x ) ) ) < y ) } $.

    $( Define the set of linear functionals on Hilbert space.  (Contributed by
       NM, 11-Feb-2006.)  (New usage is discouraged.) $)
    df-lnfn $a |- LinFn = { t e. ( CC ^m ~H ) |
           A. x e. CC A. y e. ~H A. z e. ~H
       ( t ` ( ( x .h y ) +h z ) ) = ( ( x x. ( t ` y ) ) + ( t ` z ) ) } $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Adjoint
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t u v w x y z $.
    $( Define the adjoint of a Hilbert space operator (if it exists).  The
       domain of ` adjh ` is the set of all adjoint operators.  Definition of
       adjoint in [Kalmbach2] p. 8.  Unlike Kalmbach (and most authors), we do
       not demand that the operator be linear, but instead show (in ~ adjbdln )
       that the adjoint exists for a bounded linear operator.  (Contributed by
       NM, 20-Feb-2006.)  (New usage is discouraged.) $)
    df-adjh $a |- adjh = { <. t , u >. | ( t : ~H --> ~H /\ u : ~H --> ~H /\
         A. x e. ~H A. y e. ~H ( ( t ` x ) .ih y ) = ( x .ih ( u ` y ) ) ) } $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Dirac bra-ket notation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t u v w x y z $.
    $( Define the bra of a vector used by Dirac notation.  Based on definition
       of bra in [Prugovecki] p. 186 (p. 180 in 1971 edition).  In Dirac
       bra-ket notation, ` <. A | B >. ` is a complex number equal to the inner
       product ` ( B .ih A ) ` .  But physicists like to talk about the
       individual components ` <. A | ` and ` | B >. ` , called bra and ket
       respectively.  In order for their properties to make sense formally, we
       define the ket ` | B >. ` as the vector ` B ` itself, and the bra
       ` <. A | ` as a functional from ` ~H ` to ` CC ` .  We represent the
       Dirac notation ` <. A | B >. ` by ` ( ( bra `` A ) `` B ) ` ; see
       ~ braval .  The reversal of the inner product arguments not only makes
       the bra-ket behavior consistent with physics literature (see comments
       under ~ ax-his3 ) but is also required in order for the associative law
       ~ kbass2 to work.

       Our definition of bra and the associated outer product ~ df-kb differs
       from, but is equivalent to, a common approach in the literature that
       makes use of mappings to a dual space.  Our approach eliminates the need
       to have a parallel development of this dual space and instead keeps
       everything in Hilbert space.

       _For an extensive discussion about how our notation maps to the bra-ket
       notation in physics textbooks, see
       ~ http://us.metamath.org/mpegif/mmnotes.txt , under the 17-May-2006
       entry_.  (Contributed by NM, 15-May-2006.)
       (New usage is discouraged.) $)
    df-bra $a |- bra = ( x e. ~H |-> ( y e. ~H |-> ( y .ih x ) ) ) $.

    $( Define a commuted bra and ket juxtaposition used by Dirac notation.  In
       Dirac notation, ` | A >. ` ` <. B | ` is an operator known as the outer
       product of ` A ` and ` B ` , which we represent by ` ( A ketbra B ) ` .
       Based on Equation 8.1 of [Prugovecki] p. 376.  This definition, combined
       with definition ~ df-bra , allows any legal juxtaposition of bras and
       kets to make sense formally and also to obey the associative law when
       mapped back to Dirac notation.  (Contributed by NM, 15-May-2006.)
       (New usage is discouraged.) $)
    df-kb $a |- ketbra = ( x e. ~H , y e. ~H |->
                          ( z e. ~H |-> ( ( z .ih y ) .h x ) ) ) $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Positive operators
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t u v w x y z $.
    $( Define positive operator ordering.  Definition VI.1 of [Retherford]
       p. 49.  Note that ` ( ~H X. 0H ) <_op T ` means that ` T ` is a positive
       operator.  (Contributed by NM, 23-Jul-2006.)
       (New usage is discouraged.) $)
    df-leop $a |- <_op = { <. t , u >. | ( ( u -op t ) e. HrmOp /\
               A. x e. ~H 0 <_ ( ( ( u -op t ) ` x ) .ih x ) ) } $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Eigenvectors, eigenvalues, spectrum
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t u v w x y z $.
    $( Define the eigenvector function.  Theorem ~ eleigveccl shows that
       ` eigvec `` T ` , the set of eigenvectors of Hilbert space operator
       ` T ` , are Hilbert space vectors.  (Contributed by NM, 11-Mar-2006.)
       (New usage is discouraged.) $)
    df-eigvec $a |- eigvec = ( t e. ( ~H ^m ~H ) |->
         { x e. ( ~H \ 0H ) | E. z e. CC ( t ` x ) = ( z .h x ) } ) $.
)"},
{R"($( [19-May-2014] $) $( [11-Feb-2006] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Riesz lemma
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( A continuous linear functional can be expressed as an inner product.
       Existence part of Theorem 3.9 of [Beran] p. 104.  (Contributed by NM,
       13-Feb-2006.)  (New usage is discouraged.) $)
    riesz3i $p |- E. w e. ~H A. v e. ~H ( T ` v ) = ( v .ih w ) $=)",
R"($( [19-May-2014] $) $( [11-Feb-2006] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Riesz lemma
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d f n u v w x T $.
    nlelch.1 $e |- T e. LinFn $.
    nlelch.2 $e |- T e. ConFn $.
    $( A continuous linear functional can be expressed as an inner product.
       Existence part of Theorem 3.9 of [Beran] p. 104.  (Contributed by NM,
       13-Feb-2006.)  (New usage is discouraged.) $)
    riesz3i $p |- E. w e. ~H A. v e. ~H ( T ` v ) = ( v .ih w ) $=)"
},
{R"($( [30-May-2006] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Positive operators (cont.)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Ordering relation for positive operators.  Definition of positive
       operator ordering in [Kreyszig] p. 470.  (Contributed by NM,
       23-Jul-2006.)  (New usage is discouraged.) $)
    leopg $p |- ( ( T e. A /\ U e. B ) -> ( T <_op U <-> ( ( U -op T ) e.
                HrmOp /\ A. x e. ~H 0 <_ ( ( ( U -op T ) ` x ) .ih x ) ) ) ) $=)",
R"($( [30-May-2006] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Positive operators (cont.)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z w A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x S $.
    $d t u x y T $.  $d t u x U $.  $d t x y z $.
    $( Ordering relation for positive operators.  Definition of positive
       operator ordering in [Kreyszig] p. 470.  (Contributed by NM,
       23-Jul-2006.)  (New usage is discouraged.) $)
    leopg $p |- ( ( T e. A /\ U e. B ) -> ( T <_op U <-> ( ( U -op T ) e.
                HrmOp /\ A. x e. ~H 0 <_ ( ( ( U -op T ) ` x ) .ih x ) ) ) ) $=)"
}
};

void patch(string& data) {
	for (auto patch : patches) {
		string& to_replace = patch.first;
		string& replacement = patch.second;
		size_t pos = data.find(to_replace);
		if (pos != string::npos) {
			//cout << "PATCH: " << endl;
			//cout << to_replace << endl;
			data.replace(pos, to_replace.length(), replacement);
		}
	}
}

Section* parse(const Path& in, const Path& out) {
	string data;
	in.read(data);
	patch(data);
	LocationIter iter(data.begin(), in.name);
	LocationIter end(data.end(), in.name);
	Section* source = new Section;
	source->root = (out.root.size() && out.root.back() != '/') ? (out.root + "/") : out.root;
	source->file = in.name;
	source->dir = "";
	source->path = source->dir + "/" + source->file + ".mm";
	source->type = Type::SOURCE;
	bool r = phrase_parse(iter, end, Grammar(source->root), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed", in.name);
	}
	return source;
}

}

void cut() {
	Sys::timer()["cut"].start();
	Section* root = parse(Sys::conf().in, Sys::conf().out);
	for (Section* sect = root; sect; sect = sect->next_sect) sect->split();
	for (const Section* sect = root; sect; sect = sect->next_sect) sect->save();
	delete root;
	Sys::timer()["cut"].stop();
}

}} // mdl::mm::cut