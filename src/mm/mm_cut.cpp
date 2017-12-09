
#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "boost.hpp"
#include <mm_sys.hpp>

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
	Section() :
	type(Type::SOURCE),
	prev_sect(nullptr),
	next_sect(nullptr),
	prev_sibling(nullptr),
	next_sibling(nullptr),
	parent(nullptr) { }

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
		if (type == Type::PARAGRAPH || (next_sect && type == next_sect->type)) return;
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
		case Type::CHAPTER: header->type = Type::PARAGRAPH; break;
		case Type::PART:    header->type = Type::CHAPTER;   break;
		case Type::SOURCE:  header->type = Type::PART;      break;
		}
		contents.clear();

		header->parent = parent;
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
		const Section* imp = prev();
		if (imp) {
			str += "\n$[ " + imp->prev_sibling->path + " $]\n\n";
		}
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

	const Section* prev() const {
		const Section* s = this;
		while (s && !s->prev_sibling) s = s->parent;
		return s;
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

}} // mdl::mm::cut

#include "mm_cut_adaptor.hpp"

namespace mdl { namespace mm {

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

namespace cut_ {

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
		boost::replace_all(sect->file, ";", "_");
		boost::replace_all(sect->file, "$", "_");
		boost::replace_all(sect->file, "\"", "_");
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
		using qi::labels::_val;
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
			>> lexeme[*(ascii::char_ - "##" - "#*" - "=-")] [at_c<1>(*_val) = makeString(qi::labels::_1)]
			>> border                              [at_c<0>(*_val) = qi::labels::_1]
			>> lexeme[+(ascii::char_ - "##" - "#*" - "=-")] [at_c<2>(*_val) = makeString(qi::labels::_1)]
			>> border
			>> lexeme[*(ascii::char_ - "$)")]      [at_c<3>(*_val) = makeString(qi::labels::_1)]
			>> lit("$)\n")                         [add(_val, phoenix::ref(root))];

		contents =
			lexeme[+(ascii::char_ - FULL_PARAGRAPH_STR - FULL_CHAPTER_STR - FULL_PART_STR)] [_val = makeString(qi::labels::_1)];

		source =
			  eps         [add(_val, phoenix::ref(root))]
			>> header
			>> + (
				section |
				contents  [add(qi::labels::_1)]
			);

		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << qi::labels::_4
			<< phoenix::val(" here: \n") << qi::labels::_3 << phoenix::val("\n")
			<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(qi::labels::_3));
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

static vector<Patch> cut_patches = {
{R"(
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Derive the Power Set, Infinity and Choice Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Derive the Axiom of Power Sets ~ ax-pow from the Tarski-Grothendieck
       axiom ~ ax-groth .  That it follows is mentioned by Bob Solovay at
       ~ http://www.cs.nyu.edu/pipermail/fom/2008-March/012783.html .  Note
       that ~ ax-pow is not used by the proof.  (Contributed by G&eacute;rard
       Lang, 22-Jun-2009.) $)
    grothpw $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=)",
R"(
  $}
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Derive the Power Set, Infinity and Choice Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  ${
    $d x y z w v u f $.
    $( Derive the Axiom of Power Sets ~ ax-pow from the Tarski-Grothendieck
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
       "epsilon" ( ` y ` ) there is a "delta" ( ` z ` ) such that...
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
       "epsilon" ( ` y ` ) there is a "delta" ( ` z ` ) such that...
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
       ~ http://us.metamath.org/mpeuni/mmnotes.txt , under the 17-May-2006
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

    $( Define the eigenvalue function.  The range of ` eigval `` T ` is the set
       of eigenvalues of Hilbert space operator ` T ` .  Theorem ~ eigvalcl
       shows that ` ( eigval `` T ) `` A ` , the eigenvalue associated with
       eigenvector ` A ` , is a complex number.  (Contributed by NM,
       11-Mar-2006.)  (New usage is discouraged.) $)
    df-eigval $a |- eigval = ( t e. ( ~H ^m ~H ) |->
                     ( x e. ( eigvec ` t ) |->
                   ( ( ( t ` x ) .ih x ) / ( ( normh ` x ) ^ 2 ) ) ) ) $.

    $( Define the spectrum of an operator.  Definition of spectrum in [Halmos]
       p. 50.  (Contributed by NM, 11-Apr-2006.)
       (New usage is discouraged.) $)
    df-spec $a |- Lambda = ( t e. ( ~H ^m ~H ) |->
        { x e. CC | -. ( t -op ( x .op ( _I |` ~H ) ) ) : ~H -1-1-> ~H } ) $.
  $}

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
       "epsilon" ( ` y ` ) there is a "delta" ( ` z ` ) such that...
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
       "epsilon" ( ` y ` ) there is a "delta" ( ` z ` ) such that...
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
       ~ http://us.metamath.org/mpeuni/mmnotes.txt , under the 17-May-2006
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

    $( Define the eigenvalue function.  The range of ` eigval `` T ` is the set
       of eigenvalues of Hilbert space operator ` T ` .  Theorem ~ eigvalcl
       shows that ` ( eigval `` T ) `` A ` , the eigenvalue associated with
       eigenvector ` A ` , is a complex number.  (Contributed by NM,
       11-Mar-2006.)  (New usage is discouraged.) $)
    df-eigval $a |- eigval = ( t e. ( ~H ^m ~H ) |->
                     ( x e. ( eigvec ` t ) |->
                   ( ( ( t ` x ) .ih x ) / ( ( normh ` x ) ^ 2 ) ) ) ) $.

    $( Define the spectrum of an operator.  Definition of spectrum in [Halmos]
       p. 50.  (Contributed by NM, 11-Apr-2006.)
       (New usage is discouraged.) $)
    df-spec $a |- Lambda = ( t e. ( ~H ^m ~H ) |->
        { x e. CC | -. ( t -op ( x .op ( _I |` ~H ) ) ) : ~H -1-1-> ~H } ) $.
  $}

)"},
{R"(
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Riesz lemma
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( A continuous linear functional can be expressed as an inner product.
       Existence part of Theorem 3.9 of [Beran] p. 104.  (Contributed by NM,
       13-Feb-2006.)  (New usage is discouraged.) $)
    riesz3i $p |- E. w e. ~H A. v e. ~H ( T ` v ) = ( v .ih w ) $=)",
R"(
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Riesz lemma
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d f n u v w x T $.
    riesz3.1 $e |- T e. LinFn $.
    riesz3.2 $e |- T e. ConFn $.
    $( A continuous linear functional can be expressed as an inner product.
       Existence part of Theorem 3.9 of [Beran] p. 104.  (Contributed by NM,
       13-Feb-2006.)  (New usage is discouraged.) $)
    riesz3i $p |- E. w e. ~H A. v e. ~H ( T ` v ) = ( v .ih w ) $=)"
},

{
R"(vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw chil wrex cT cnl cfv
      cort cfv c0h cT cnl cfv cort cfv c0h wceq c0v chil wcel vv cv cT cfv vv
      cv c0v csp co wceq vv chil wral vv cv cT cfv vv cv vw cv csp co wceq vv
      chil wral vw chil wrex ax-hv0cl cT cnl cfv cort cfv c0h wceq vv cv cT cfv
      vv cv c0v csp co wceq vv chil cT cnl cfv cort cfv c0h wceq vv cv chil
      wcel wa vv cv cT cfv cc0 vv cv c0v csp co cT cnl cfv cort cfv c0h wceq vv
      cv chil wcel wa chil cc cT wf vv cv cT cnl cfv wcel vv cv cT cfv cc0 wceq
      cT nlelch.1 lnfnfi cT cnl cfv cort cfv c0h wceq vv cv cT cnl cfv wcel vv
      cv chil wcel cT cnl cfv cort cfv c0h wceq cT cnl cfv chil vv cv cT cnl
      cfv cort cfv c0h wceq cT cnl cfv cort cfv cort cfv c0h cort cfv cT cnl
      cfv chil cT cnl cfv cort cfv c0h cort fveq2 cT cnl cfv cT nlelch.1
      nlelch.2 nlelchi ococi choc0 3eqtr3g eleq2d biimpar vv cv cT elnlfn2
      sylancr vv cv chil wcel vv cv c0v csp co cc0 wceq cT cnl cfv cort cfv c0h
      wceq vv cv hi02 adantl eqtr4d ralrimiva vv cv cT cfv vv cv vw cv csp co
      wceq vv chil wral vv cv cT cfv vv cv c0v csp co wceq vv chil wral vw c0v
      chil vw cv c0v wceq vv cv cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv
      cv c0v csp co wceq vv chil vw cv c0v wceq vv cv vw cv csp co vv cv c0v
      csp co vv cv cT cfv vw cv c0v vv cv csp oveq2 eqeq2d ralbidv rspcev
      sylancr cT cnl cfv cort cfv c0h wne vu cv c0v wne vu cT cnl cfv cort cfv
      wrex vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw chil wrex vu cT
      cnl cfv cort cfv cT cnl cfv cT nlelch.1 nlelch.2 nlelchi choccli chne0i
      vu cv c0v wne vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw chil
      wrex vu cT cnl cfv cort cfv vu cv cT cnl cfv cort cfv wcel vu cv chil
      wcel vu cv c0v wne vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw
      chil wrex wi vu cv cT cnl cfv cort cfv cT cnl cfv cT nlelch.1 nlelch.2
      nlelchi choccli cheli vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa
      vu cv c0v wne vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw chil
      wrex vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa vu cv c0v wne wa
      vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co chil wcel vv
      cv cT cfv vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm
      co csp co wceq vv chil wral vv cv cT cfv vv cv vw cv csp co wceq vv chil
      wral vw chil wrex vu cv chil wcel vu cv c0v wne vu cv cT cfv vu cv vu cv
      csp co cdiv co ccj cfv vu cv csm co chil wcel vu cv cT cnl cfv cort cfv
      wcel vu cv chil wcel vu cv c0v wne wa vu cv cT cfv vu cv vu cv csp co
      cdiv co ccj cfv cc wcel vu cv chil wcel vu cv cT cfv vu cv vu cv csp co
      cdiv co ccj cfv vu cv csm co chil wcel vu cv chil wcel vu cv c0v wne wa
      vu cv cT cfv vu cv vu cv csp co cdiv co vu cv chil wcel vu cv c0v wne wa
      vu cv cT cfv vu cv vu cv csp co vu cv chil wcel vu cv cT cfv cc wcel vu
      cv c0v wne chil cc vu cv cT cT nlelch.1 lnfnfi ffvelrni adantr vu cv chil
      wcel vu cv vu cv csp co cc wcel vu cv c0v wne vu cv chil wcel vu cv vu cv
      csp co cc wcel vu cv vu cv hicl anidms adantr vu cv chil wcel vu cv vu cv
      csp co cc0 wne vu cv c0v wne vu cv chil wcel vu cv vu cv csp co cc0 vu cv
      c0v vu cv his6 necon3bid biimpar divcld cjcld vu cv chil wcel vu cv c0v
      wne simpl vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv hvmulcl
      syl2anc adantll vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa vu cv
      c0v wne wa vv cv cT cfv vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj
      cfv vu cv csm co csp co wceq vv chil vu cv cT cnl cfv cort cfv wcel vu cv
      chil wcel wa vu cv c0v wne wa vv cv chil wcel wa vu cv cT cfv vv cv vu cv
      csp co cmul co vu cv vu cv csp co cdiv co vv cv cT cfv vv cv vu cv cT cfv
      vu cv vu cv csp co cdiv co ccj cfv vu cv csm co csp co vu cv cT cnl cfv
      cort cfv wcel vu cv chil wcel wa vu cv c0v wne wa vv cv chil wcel wa vu
      cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv co vv cv cT
      cfv wceq vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv
      csp co cmul co wceq vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa vv
      cv chil wcel vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv
      vu cv csp co cmul co wceq vu cv c0v wne vu cv cT cnl cfv cort cfv wcel vu
      cv chil wcel wa vv cv chil wcel wa vu cv cT cfv vv cv vu cv csp co cmul
      co vv cv cT cfv vu cv vu cv csp co cmul co cmin co cc0 wceq vu cv cT cfv
      vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co wceq
      vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa vv cv chil wcel wa vu
      cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul
      co cmin co vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu
      cv csp co cc0 vu cv chil wcel vv cv chil wcel vu cv cT cfv vv cv vu cv
      csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co cmin co vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv csp co wceq vu cv
      cT cnl cfv cort cfv wcel vu cv chil wcel vv cv chil wcel wa vu cv cT cfv
      vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv csp co vu cv cT cfv
      vv cv csm co vu cv csp co vv cv cT cfv vu cv csm co vu cv csp co cmin co
      vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co
      cmul co cmin co vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv csm
      co chil wcel vv cv cT cfv vu cv csm co chil wcel vu cv chil wcel vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv csp co vu cv cT
      cfv vv cv csm co vu cv csp co vv cv cT cfv vu cv csm co vu cv csp co cmin
      co wceq vu cv chil wcel vu cv cT cfv cc wcel vv cv chil wcel vu cv cT cfv
      vv cv csm co chil wcel chil cc vu cv cT cT nlelch.1 lnfnfi ffvelrni vu cv
      cT cfv vv cv hvmulcl sylan vv cv chil wcel vu cv chil wcel vv cv cT cfv
      vu cv csm co chil wcel vv cv chil wcel vv cv cT cfv cc wcel vu cv chil
      wcel vv cv cT cfv vu cv csm co chil wcel chil cc vv cv cT cT nlelch.1
      lnfnfi ffvelrni vv cv cT cfv vu cv hvmulcl sylan ancoms vu cv chil wcel
      vv cv chil wcel simpl vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co
      vu cv his2sub syl3anc vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv
      cv csm co vu cv csp co vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT
      cfv vu cv csm co vu cv csp co vv cv cT cfv vu cv vu cv csp co cmul co
      cmin vu cv chil wcel vv cv chil wcel wa vu cv cT cfv cc wcel vv cv chil
      wcel vu cv chil wcel vu cv cT cfv vv cv csm co vu cv csp co vu cv cT cfv
      vv cv vu cv csp co cmul co wceq vu cv chil wcel vu cv cT cfv cc wcel vv
      cv chil wcel chil cc vu cv cT cT nlelch.1 lnfnfi ffvelrni adantr vu cv
      chil wcel vv cv chil wcel simpr vu cv chil wcel vv cv chil wcel simpl vu
      cv cT cfv vv cv vu cv ax-his3 syl3anc vu cv chil wcel vv cv chil wcel wa
      vv cv cT cfv cc wcel vu cv chil wcel vu cv chil wcel vv cv cT cfv vu cv
      csm co vu cv csp co vv cv cT cfv vu cv vu cv csp co cmul co wceq vv cv
      chil wcel vv cv cT cfv cc wcel vu cv chil wcel chil cc vv cv cT cT
      nlelch.1 lnfnfi ffvelrni adantl vu cv chil wcel vv cv chil wcel simpl vu
      cv chil wcel vv cv chil wcel simpl vv cv cT cfv vu cv vu cv ax-his3
      syl3anc oveq12d eqtr2d adantll vu cv cT cnl cfv cort cfv wcel vu cv chil
      wcel vv cv chil wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co
      cmv co vu cv csp co cc0 wceq vu cv chil wcel vv cv chil wcel wa vu cv cT
      cnl cfv cort cfv wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co
      cmv co vu cv csp co cc0 wceq vu cv chil wcel vv cv chil wcel wa vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT cnl cfv wcel vu cv
      cT cnl cfv cort cfv wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm
      co cmv co vu cv csp co cc0 wceq vu cv chil wcel vv cv chil wcel wa vu cv
      cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co chil wcel vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT cfv cc0 wceq vu cv
      cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT cnl cfv wcel vu
      cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv csm co chil wcel vv cv
      cT cfv vu cv csm co chil wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu
      cv csm co cmv co chil wcel vu cv chil wcel vu cv cT cfv cc wcel vv cv
      chil wcel vu cv cT cfv vv cv csm co chil wcel chil cc vu cv cT cT
      nlelch.1 lnfnfi ffvelrni vu cv cT cfv vv cv hvmulcl sylan vv cv chil wcel
      vu cv chil wcel vv cv cT cfv vu cv csm co chil wcel vv cv chil wcel vv cv
      cT cfv cc wcel vu cv chil wcel vv cv cT cfv vu cv csm co chil wcel chil
      cc vv cv cT cT nlelch.1 lnfnfi ffvelrni vv cv cT cfv vu cv hvmulcl sylan
      ancoms vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co hvsubcl
      syl2anc vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv csm co vv
      cv cT cfv vu cv csm co cmv co cT cfv vu cv cT cfv vv cv csm co cT cfv vv
      cv cT cfv vu cv csm co cT cfv cmin co vu cv cT cfv vv cv cT cfv cmul co
      vu cv cT cfv vv cv cT cfv cmul co cmin co cc0 vu cv chil wcel vv cv chil
      wcel wa vu cv cT cfv vv cv csm co chil wcel vv cv cT cfv vu cv csm co
      chil wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT
      cfv vu cv cT cfv vv cv csm co cT cfv vv cv cT cfv vu cv csm co cT cfv
      cmin co wceq vu cv chil wcel vu cv cT cfv cc wcel vv cv chil wcel vu cv
      cT cfv vv cv csm co chil wcel chil cc vu cv cT cT nlelch.1 lnfnfi
      ffvelrni vu cv cT cfv vv cv hvmulcl sylan vv cv chil wcel vu cv chil wcel
      vv cv cT cfv vu cv csm co chil wcel vv cv chil wcel vv cv cT cfv cc wcel
      vu cv chil wcel vv cv cT cfv vu cv csm co chil wcel chil cc vv cv cT cT
      nlelch.1 lnfnfi ffvelrni vv cv cT cfv vu cv hvmulcl sylan ancoms vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cT nlelch.1 lnfnsubi syl2anc
      vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv csm co cT cfv vu cv
      cT cfv vv cv cT cfv cmul co vv cv cT cfv vu cv csm co cT cfv vu cv cT cfv
      vv cv cT cfv cmul co cmin vu cv chil wcel vu cv cT cfv cc wcel vv cv chil
      wcel vu cv cT cfv vv cv csm co cT cfv vu cv cT cfv vv cv cT cfv cmul co
      wceq chil cc vu cv cT cT nlelch.1 lnfnfi ffvelrni vu cv cT cfv vv cv cT
      nlelch.1 lnfnmuli sylan vv cv chil wcel vu cv chil wcel vv cv cT cfv vu
      cv csm co cT cfv vu cv cT cfv vv cv cT cfv cmul co wceq vv cv chil wcel
      vv cv cT cfv cc wcel vu cv chil wcel vv cv cT cfv vu cv csm co cT cfv vu
      cv cT cfv vv cv cT cfv cmul co wceq chil cc vv cv cT cT nlelch.1 lnfnfi
      ffvelrni vv cv cT cfv cc wcel vu cv chil wcel wa vv cv cT cfv vu cv csm
      co cT cfv vv cv cT cfv vu cv cT cfv cmul co vu cv cT cfv vv cv cT cfv
      cmul co vv cv cT cfv vu cv cT nlelch.1 lnfnmuli vu cv chil wcel vv cv cT
      cfv cc wcel vu cv cT cfv cc wcel vv cv cT cfv vu cv cT cfv cmul co vu cv
      cT cfv vv cv cT cfv cmul co wceq chil cc vu cv cT cT nlelch.1 lnfnfi
      ffvelrni vv cv cT cfv vu cv cT cfv mulcom sylan2 eqtrd sylan ancoms
      oveq12d vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv cT cfv cmul
      co vu cv chil wcel vu cv cT cfv cc wcel vv cv cT cfv cc wcel vu cv cT cfv
      vv cv cT cfv cmul co cc wcel vv cv chil wcel chil cc vu cv cT cT nlelch.1
      lnfnfi ffvelrni chil cc vv cv cT cT nlelch.1 lnfnfi ffvelrni vu cv cT cfv
      vv cv cT cfv mulcl syl2an subidd 3eqtrd chil cc cT wf vu cv cT cfv vv cv
      csm co vv cv cT cfv vu cv csm co cmv co cT cnl cfv wcel vu cv cT cfv vv
      cv csm co vv cv cT cfv vu cv csm co cmv co chil wcel vu cv cT cfv vv cv
      csm co vv cv cT cfv vu cv csm co cmv co cT cfv cc0 wceq wa wb cT nlelch.1
      lnfnfi vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT
      elnlfn ax-mp sylanbrc cT cnl cfv chil wss vu cv cT cfv vv cv csm co vv cv
      cT cfv vu cv csm co cmv co cT cnl cfv wcel vu cv cT cnl cfv cort cfv wcel
      wa vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv csp
      co cc0 wceq wi cT cnl cfv cT nlelch.1 nlelch.2 nlelchi chssii vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv cT cnl cfv ocorth
      ax-mp sylan ancoms anassrs eqtrd vu cv chil wcel vv cv chil wcel vu cv cT
      cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co
      cmin co cc0 wceq vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu
      cv vu cv csp co cmul co wceq wb vu cv cT cnl cfv cort cfv wcel vu cv chil
      wcel vv cv chil wcel wa vu cv cT cfv vv cv vu cv csp co cmul co cc wcel
      vv cv cT cfv vu cv vu cv csp co cmul co cc wcel vu cv cT cfv vv cv vu cv
      csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co cmin co cc0 wceq
      vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co
      cmul co wceq wb vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv vu
      cv csp co vu cv chil wcel vu cv cT cfv cc wcel vv cv chil wcel chil cc vu
      cv cT cT nlelch.1 lnfnfi ffvelrni adantr vv cv chil wcel vu cv chil wcel
      vv cv vu cv csp co cc wcel vv cv vu cv hicl ancoms mulcld vv cv chil wcel
      vv cv cT cfv cc wcel vu cv vu cv csp co cc wcel vv cv cT cfv vu cv vu cv
      csp co cmul co cc wcel vu cv chil wcel chil cc vv cv cT cT nlelch.1
      lnfnfi ffvelrni vu cv chil wcel vu cv vu cv csp co cc wcel vu cv vu cv
      hicl anidms vv cv cT cfv vu cv vu cv csp co mulcl syl2anr vu cv cT cfv vv
      cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co subeq0
      syl2anc adantll mpbid adantlr vu cv chil wcel vu cv c0v wne vv cv chil
      wcel vu cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv co
      vv cv cT cfv wceq vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu
      cv vu cv csp co cmul co wceq wb vu cv cT cnl cfv cort cfv wcel vu cv chil
      wcel vu cv c0v wne wa vv cv chil wcel wa vu cv cT cfv vv cv vu cv csp co
      cmul co cc wcel vv cv cT cfv cc wcel vu cv vu cv csp co cc wcel vu cv vu
      cv csp co cc0 wne wa vu cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv
      csp co cdiv co vv cv cT cfv wceq vu cv cT cfv vv cv vu cv csp co cmul co
      vv cv cT cfv vu cv vu cv csp co cmul co wceq wb vu cv chil wcel vv cv
      chil wcel vu cv cT cfv vv cv vu cv csp co cmul co cc wcel vu cv c0v wne
      vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv vu cv csp co vu cv
      chil wcel vu cv cT cfv cc wcel vv cv chil wcel chil cc vu cv cT cT
      nlelch.1 lnfnfi ffvelrni adantr vv cv chil wcel vu cv chil wcel vv cv vu
      cv csp co cc wcel vv cv vu cv hicl ancoms mulcld adantlr vv cv chil wcel
      vv cv cT cfv cc wcel vu cv chil wcel vu cv c0v wne wa chil cc vv cv cT cT
      nlelch.1 lnfnfi ffvelrni adantl vu cv chil wcel vu cv c0v wne wa vu cv vu
      cv csp co cc wcel vu cv vu cv csp co cc0 wne wa vv cv chil wcel vu cv
      chil wcel vu cv c0v wne wa vu cv vu cv csp co cc wcel vu cv vu cv csp co
      cc0 wne vu cv chil wcel vu cv vu cv csp co cc wcel vu cv c0v wne vu cv
      chil wcel vu cv vu cv csp co cc wcel vu cv vu cv hicl anidms adantr vu cv
      chil wcel vu cv vu cv csp co cc0 wne vu cv c0v wne vu cv chil wcel vu cv
      vu cv csp co cc0 vu cv c0v vu cv his6 necon3bid biimpar jca adantr vu cv
      cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co divmul3
      syl3anc adantlll mpbird vu cv chil wcel vu cv c0v wne vv cv chil wcel vu
      cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv co vv cv vu
      cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co csp co wceq vu
      cv cT cnl cfv cort cfv wcel vu cv chil wcel vu cv c0v wne wa vv cv chil
      wcel wa vu cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv
      co vu cv cT cfv vu cv vu cv csp co cdiv co vv cv vu cv csp co cmul co vv
      cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co csp co vu
      cv chil wcel vu cv c0v wne wa vv cv chil wcel wa vu cv cT cfv cc wcel vv
      cv vu cv csp co cc wcel vu cv vu cv csp co cc wcel vu cv vu cv csp co cc0
      wne wa vu cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv co
      vu cv cT cfv vu cv vu cv csp co cdiv co vv cv vu cv csp co cmul co wceq
      vu cv chil wcel vu cv c0v wne wa vu cv cT cfv cc wcel vv cv chil wcel vu
      cv chil wcel vu cv cT cfv cc wcel vu cv c0v wne chil cc vu cv cT cT
      nlelch.1 lnfnfi ffvelrni adantr adantr vu cv chil wcel vv cv chil wcel vv
      cv vu cv csp co cc wcel vu cv c0v wne vv cv chil wcel vu cv chil wcel vv
      cv vu cv csp co cc wcel vv cv vu cv hicl ancoms adantlr vu cv chil wcel
      vu cv c0v wne wa vu cv vu cv csp co cc wcel vu cv vu cv csp co cc0 wne wa
      vv cv chil wcel vu cv chil wcel vu cv c0v wne wa vu cv vu cv csp co cc
      wcel vu cv vu cv csp co cc0 wne vu cv chil wcel vu cv vu cv csp co cc
      wcel vu cv c0v wne vu cv chil wcel vu cv vu cv csp co cc wcel vu cv vu cv
      hicl anidms adantr vu cv chil wcel vu cv vu cv csp co cc0 wne vu cv c0v
      wne vu cv chil wcel vu cv vu cv csp co cc0 vu cv c0v vu cv his6 necon3bid
      biimpar jca adantr vu cv cT cfv vv cv vu cv csp co vu cv vu cv csp co
      div23 syl3anc vu cv chil wcel vu cv c0v wne wa vv cv chil wcel wa vu cv
      cT cfv vu cv vu cv csp co cdiv co cc wcel vv cv chil wcel vu cv chil wcel
      vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co csp co
      vu cv cT cfv vu cv vu cv csp co cdiv co vv cv vu cv csp co cmul co wceq
      vu cv chil wcel vu cv c0v wne wa vu cv cT cfv vu cv vu cv csp co cdiv co
      cc wcel vv cv chil wcel vu cv chil wcel vu cv c0v wne wa vu cv cT cfv vu
      cv vu cv csp co vu cv chil wcel vu cv cT cfv cc wcel vu cv c0v wne chil
      cc vu cv cT cT nlelch.1 lnfnfi ffvelrni adantr vu cv chil wcel vu cv vu
      cv csp co cc wcel vu cv c0v wne vu cv chil wcel vu cv vu cv csp co cc
      wcel vu cv vu cv hicl anidms adantr vu cv chil wcel vu cv vu cv csp co
      cc0 wne vu cv c0v wne vu cv chil wcel vu cv vu cv csp co cc0 vu cv c0v vu
      cv his6 necon3bid biimpar divcld adantr vu cv chil wcel vu cv c0v wne wa
      vv cv chil wcel simpr vu cv chil wcel vu cv c0v wne vv cv chil wcel
      simpll vu cv cT cfv vu cv vu cv csp co cdiv co vv cv vu cv his52 syl3anc
      eqtr4d adantlll eqtr3d ralrimiva vv cv cT cfv vv cv vw cv csp co wceq vv
      chil wral vv cv cT cfv vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj
      cfv vu cv csm co csp co wceq vv chil wral vw vu cv cT cfv vu cv vu cv csp
      co cdiv co ccj cfv vu cv csm co chil vw cv vu cv cT cfv vu cv vu cv csp
      co cdiv co ccj cfv vu cv csm co wceq vv cv cT cfv vv cv vw cv csp co wceq
      vv cv cT cfv vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv
      csm co csp co wceq vv chil vw cv vu cv cT cfv vu cv vu cv csp co cdiv co
      ccj cfv vu cv csm co wceq vv cv vw cv csp co vv cv vu cv cT cfv vu cv vu
      cv csp co cdiv co ccj cfv vu cv csm co csp co vv cv cT cfv vw cv vu cv cT
      cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co vv cv csp oveq2
      eqeq2d ralbidv rspcev syl2anc ex mpdan rexlimiv sylbi pm2.61ine $.)",
R"(vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw chil wrex cT cnl cfv
      cort cfv c0h cT cnl cfv cort cfv c0h wceq c0v chil wcel vv cv cT cfv vv
      cv c0v csp co wceq vv chil wral vv cv cT cfv vv cv vw cv csp co wceq vv
      chil wral vw chil wrex ax-hv0cl cT cnl cfv cort cfv c0h wceq vv cv cT cfv
      vv cv c0v csp co wceq vv chil cT cnl cfv cort cfv c0h wceq vv cv chil
      wcel wa vv cv cT cfv cc0 vv cv c0v csp co cT cnl cfv cort cfv c0h wceq vv
      cv chil wcel wa chil cc cT wf vv cv cT cnl cfv wcel vv cv cT cfv cc0 wceq
      cT nlelch.1 lnfnfi cT cnl cfv cort cfv c0h wceq vv cv cT cnl cfv wcel vv
      cv chil wcel cT cnl cfv cort cfv c0h wceq cT cnl cfv chil vv cv cT cnl
      cfv cort cfv c0h wceq cT cnl cfv cort cfv cort cfv c0h cort cfv cT cnl
      cfv chil cT cnl cfv cort cfv c0h cort fveq2 cT cnl cfv cT nlelch.1
      nlelch.2 nlelchi ococi choc0 3eqtr3g eleq2d biimpar vv cv cT elnlfn2
      sylancr vv cv chil wcel vv cv c0v csp co cc0 wceq cT cnl cfv cort cfv c0h
      wceq vv cv hi02 adantl eqtr4d ralrimiva vv cv cT cfv vv cv vw cv csp co
      wceq vv chil wral vv cv cT cfv vv cv c0v csp co wceq vv chil wral vw c0v
      chil vw cv c0v wceq vv cv cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv
      cv c0v csp co wceq vv chil vw cv c0v wceq vv cv vw cv csp co vv cv c0v
      csp co vv cv cT cfv vw cv c0v vv cv csp oveq2 eqeq2d ralbidv rspcev
      sylancr cT cnl cfv cort cfv c0h wne vu cv c0v wne vu cT cnl cfv cort cfv
      wrex vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw chil wrex vu cT
      cnl cfv cort cfv cT cnl cfv cT nlelch.1 nlelch.2 nlelchi choccli chne0i
      vu cv c0v wne vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw chil
      wrex vu cT cnl cfv cort cfv vu cv cT cnl cfv cort cfv wcel vu cv chil
      wcel vu cv c0v wne vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw
      chil wrex wi vu cv cT cnl cfv cort cfv cT cnl cfv cT nlelch.1 nlelch.2
      nlelchi choccli cheli vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa
      vu cv c0v wne vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vw chil
      wrex vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa vu cv c0v wne wa
      vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co chil wcel vv
      cv cT cfv vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm
      co csp co wceq vv chil wral vv cv cT cfv vv cv vw cv csp co wceq vv chil
      wral vw chil wrex vu cv chil wcel vu cv c0v wne vu cv cT cfv vu cv vu cv
      csp co cdiv co ccj cfv vu cv csm co chil wcel vu cv cT cnl cfv cort cfv
      wcel vu cv chil wcel vu cv c0v wne wa vu cv cT cfv vu cv vu cv csp co
      cdiv co ccj cfv cc wcel vu cv chil wcel vu cv cT cfv vu cv vu cv csp co
      cdiv co ccj cfv vu cv csm co chil wcel vu cv chil wcel vu cv c0v wne wa
      vu cv cT cfv vu cv vu cv csp co cdiv co vu cv chil wcel vu cv c0v wne wa
      vu cv cT cfv vu cv vu cv csp co vu cv chil wcel vu cv cT cfv cc wcel vu
      cv c0v wne chil cc vu cv cT cT nlelch.1 lnfnfi ffvelrni adantr vu cv chil
      wcel vu cv vu cv csp co cc wcel vu cv c0v wne vu cv chil wcel vu cv vu cv
      csp co cc wcel vu cv vu cv hicl anidms adantr vu cv chil wcel vu cv vu cv
      csp co cc0 wne vu cv c0v wne vu cv chil wcel vu cv vu cv csp co cc0 vu cv
      c0v vu cv his6 necon3bid biimpar divcld cjcld vu cv chil wcel vu cv c0v
      wne simpl vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv hvmulcl
      syl2anc adantll vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa vu cv
      c0v wne wa vv cv cT cfv vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj
      cfv vu cv csm co csp co wceq vv chil vu cv cT cnl cfv cort cfv wcel vu cv
      chil wcel wa vu cv c0v wne wa vv cv chil wcel wa vu cv cT cfv vv cv vu cv
      csp co cmul co vu cv vu cv csp co cdiv co vv cv cT cfv vv cv vu cv cT cfv
      vu cv vu cv csp co cdiv co ccj cfv vu cv csm co csp co vu cv cT cnl cfv
      cort cfv wcel vu cv chil wcel wa vu cv c0v wne wa vv cv chil wcel wa vu
      cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv co vv cv cT
      cfv wceq vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv
      csp co cmul co wceq vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa vv
      cv chil wcel vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv
      vu cv csp co cmul co wceq vu cv c0v wne vu cv cT cnl cfv cort cfv wcel vu
      cv chil wcel wa vv cv chil wcel wa vu cv cT cfv vv cv vu cv csp co cmul
      co vv cv cT cfv vu cv vu cv csp co cmul co cmin co cc0 wceq vu cv cT cfv
      vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co wceq
      vu cv cT cnl cfv cort cfv wcel vu cv chil wcel wa vv cv chil wcel wa vu
      cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul
      co cmin co vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu
      cv csp co cc0 vu cv chil wcel vv cv chil wcel vu cv cT cfv vv cv vu cv
      csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co cmin co vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv csp co wceq vu cv
      cT cnl cfv cort cfv wcel vu cv chil wcel vv cv chil wcel wa vu cv cT cfv
      vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv csp co vu cv cT cfv
      vv cv csm co vu cv csp co vv cv cT cfv vu cv csm co vu cv csp co cmin co
      vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co
      cmul co cmin co vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv csm
      co chil wcel vv cv cT cfv vu cv csm co chil wcel vu cv chil wcel vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv csp co vu cv cT
      cfv vv cv csm co vu cv csp co vv cv cT cfv vu cv csm co vu cv csp co cmin
      co wceq vu cv chil wcel vu cv cT cfv cc wcel vv cv chil wcel vu cv cT cfv
      vv cv csm co chil wcel chil cc vu cv cT cT nlelch.1 lnfnfi ffvelrni vu cv
      cT cfv vv cv hvmulcl sylan vv cv chil wcel vu cv chil wcel vv cv cT cfv
      vu cv csm co chil wcel vv cv chil wcel vv cv cT cfv cc wcel vu cv chil
      wcel vv cv cT cfv vu cv csm co chil wcel chil cc vv cv cT cT nlelch.1
      lnfnfi ffvelrni vv cv cT cfv vu cv hvmulcl sylan ancoms vu cv chil wcel
      vv cv chil wcel simpl vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co
      vu cv his2sub syl3anc vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv
      cv csm co vu cv csp co vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT
      cfv vu cv csm co vu cv csp co vv cv cT cfv vu cv vu cv csp co cmul co
      cmin vu cv chil wcel vv cv chil wcel wa vu cv cT cfv cc wcel vv cv chil
      wcel vu cv chil wcel vu cv cT cfv vv cv csm co vu cv csp co vu cv cT cfv
      vv cv vu cv csp co cmul co wceq vu cv chil wcel vu cv cT cfv cc wcel vv
      cv chil wcel chil cc vu cv cT cT nlelch.1 lnfnfi ffvelrni adantr vu cv
      chil wcel vv cv chil wcel simpr vu cv chil wcel vv cv chil wcel simpl vu
      cv cT cfv vv cv vu cv ax-his3 syl3anc vu cv chil wcel vv cv chil wcel wa
      vv cv cT cfv cc wcel vu cv chil wcel vu cv chil wcel vv cv cT cfv vu cv
      csm co vu cv csp co vv cv cT cfv vu cv vu cv csp co cmul co wceq vv cv
      chil wcel vv cv cT cfv cc wcel vu cv chil wcel chil cc vv cv cT cT
      nlelch.1 lnfnfi ffvelrni adantl vu cv chil wcel vv cv chil wcel simpl vu
      cv chil wcel vv cv chil wcel simpl vv cv cT cfv vu cv vu cv ax-his3
      syl3anc oveq12d eqtr2d adantll vu cv cT cnl cfv cort cfv wcel vu cv chil
      wcel vv cv chil wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co
      cmv co vu cv csp co cc0 wceq vu cv chil wcel vv cv chil wcel wa vu cv cT
      cnl cfv cort cfv wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co
      cmv co vu cv csp co cc0 wceq vu cv chil wcel vv cv chil wcel wa vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT cnl cfv wcel vu cv
      cT cnl cfv cort cfv wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm
      co cmv co vu cv csp co cc0 wceq vu cv chil wcel vv cv chil wcel wa vu cv
      cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co chil wcel vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT cfv cc0 wceq vu cv
      cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT cnl cfv wcel vu
      cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv csm co chil wcel vv cv
      cT cfv vu cv csm co chil wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu
      cv csm co cmv co chil wcel vu cv chil wcel vu cv cT cfv cc wcel vv cv
      chil wcel vu cv cT cfv vv cv csm co chil wcel chil cc vu cv cT cT
      nlelch.1 lnfnfi ffvelrni vu cv cT cfv vv cv hvmulcl sylan vv cv chil wcel
      vu cv chil wcel vv cv cT cfv vu cv csm co chil wcel vv cv chil wcel vv cv
      cT cfv cc wcel vu cv chil wcel vv cv cT cfv vu cv csm co chil wcel chil
      cc vv cv cT cT nlelch.1 lnfnfi ffvelrni vv cv cT cfv vu cv hvmulcl sylan
      ancoms vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co hvsubcl
      syl2anc vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv csm co vv
      cv cT cfv vu cv csm co cmv co cT cfv vu cv cT cfv vv cv csm co cT cfv vv
      cv cT cfv vu cv csm co cT cfv cmin co vu cv cT cfv vv cv cT cfv cmul co
      vu cv cT cfv vv cv cT cfv cmul co cmin co cc0 vu cv chil wcel vv cv chil
      wcel wa vu cv cT cfv vv cv csm co chil wcel vv cv cT cfv vu cv csm co
      chil wcel vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT
      cfv vu cv cT cfv vv cv csm co cT cfv vv cv cT cfv vu cv csm co cT cfv
      cmin co wceq vu cv chil wcel vu cv cT cfv cc wcel vv cv chil wcel vu cv
      cT cfv vv cv csm co chil wcel chil cc vu cv cT cT nlelch.1 lnfnfi
      ffvelrni vu cv cT cfv vv cv hvmulcl sylan vv cv chil wcel vu cv chil wcel
      vv cv cT cfv vu cv csm co chil wcel vv cv chil wcel vv cv cT cfv cc wcel
      vu cv chil wcel vv cv cT cfv vu cv csm co chil wcel chil cc vv cv cT cT
      nlelch.1 lnfnfi ffvelrni vv cv cT cfv vu cv hvmulcl sylan ancoms vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cT nlelch.1 lnfnsubi syl2anc
      vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv csm co cT cfv vu cv
      cT cfv vv cv cT cfv cmul co vv cv cT cfv vu cv csm co cT cfv vu cv cT cfv
      vv cv cT cfv cmul co cmin vu cv chil wcel vu cv cT cfv cc wcel vv cv chil
      wcel vu cv cT cfv vv cv csm co cT cfv vu cv cT cfv vv cv cT cfv cmul co
      wceq chil cc vu cv cT cT nlelch.1 lnfnfi ffvelrni vu cv cT cfv vv cv cT
      nlelch.1 lnfnmuli sylan vv cv chil wcel vu cv chil wcel vv cv cT cfv vu
      cv csm co cT cfv vu cv cT cfv vv cv cT cfv cmul co wceq vv cv chil wcel
      vv cv cT cfv cc wcel vu cv chil wcel vv cv cT cfv vu cv csm co cT cfv vu
      cv cT cfv vv cv cT cfv cmul co wceq chil cc vv cv cT cT nlelch.1 lnfnfi
      ffvelrni vv cv cT cfv cc wcel vu cv chil wcel wa vv cv cT cfv vu cv csm
      co cT cfv vv cv cT cfv vu cv cT cfv cmul co vu cv cT cfv vv cv cT cfv
      cmul co vv cv cT cfv vu cv cT nlelch.1 lnfnmuli vu cv chil wcel vv cv cT
      cfv cc wcel vu cv cT cfv cc wcel vv cv cT cfv vu cv cT cfv cmul co vu cv
      cT cfv vv cv cT cfv cmul co wceq chil cc vu cv cT cT nlelch.1 lnfnfi
      ffvelrni vv cv cT cfv vu cv cT cfv mulcom sylan2 eqtrd sylan ancoms
      oveq12d vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv cT cfv cmul
      co vu cv chil wcel vu cv cT cfv cc wcel vv cv cT cfv cc wcel vu cv cT cfv
      vv cv cT cfv cmul co cc wcel vv cv chil wcel chil cc vu cv cT cT nlelch.1
      lnfnfi ffvelrni chil cc vv cv cT cT nlelch.1 lnfnfi ffvelrni vu cv cT cfv
      vv cv cT cfv mulcl syl2an subidd 3eqtrd chil cc cT wf vu cv cT cfv vv cv
      csm co vv cv cT cfv vu cv csm co cmv co cT cnl cfv wcel vu cv cT cfv vv
      cv csm co vv cv cT cfv vu cv csm co cmv co chil wcel vu cv cT cfv vv cv
      csm co vv cv cT cfv vu cv csm co cmv co cT cfv cc0 wceq wa wb cT nlelch.1
      lnfnfi vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co cT
      elnlfn ax-mp sylanbrc cT cnl cfv chil wss vu cv cT cfv vv cv csm co vv cv
      cT cfv vu cv csm co cmv co cT cnl cfv wcel vu cv cT cnl cfv cort cfv wcel
      wa vu cv cT cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv csp
      co cc0 wceq wi cT cnl cfv cT nlelch.1 nlelch.2 nlelchi chssii vu cv cT
      cfv vv cv csm co vv cv cT cfv vu cv csm co cmv co vu cv cT cnl cfv ocorth
      ax-mp sylan ancoms anassrs eqtrd vu cv chil wcel vv cv chil wcel vu cv cT
      cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co
      cmin co cc0 wceq vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu
      cv vu cv csp co cmul co wceq wb vu cv cT cnl cfv cort cfv wcel vu cv chil
      wcel vv cv chil wcel wa vu cv cT cfv vv cv vu cv csp co cmul co cc wcel
      vv cv cT cfv vu cv vu cv csp co cmul co cc wcel vu cv cT cfv vv cv vu cv
      csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co cmin co cc0 wceq
      vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co
      cmul co wceq wb vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv vu
      cv csp co vu cv chil wcel vu cv cT cfv cc wcel vv cv chil wcel chil cc vu
      cv cT cT nlelch.1 lnfnfi ffvelrni adantr vv cv chil wcel vu cv chil wcel
      vv cv vu cv csp co cc wcel vv cv vu cv hicl ancoms mulcld vv cv chil wcel
      vv cv cT cfv cc wcel vu cv vu cv csp co cc wcel vv cv cT cfv vu cv vu cv
      csp co cmul co cc wcel vu cv chil wcel chil cc vv cv cT cT nlelch.1
      lnfnfi ffvelrni vu cv chil wcel vu cv vu cv csp co cc wcel vu cv vu cv
      hicl anidms vv cv cT cfv vu cv vu cv csp co mulcl syl2anr vu cv cT cfv vv
      cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co cmul co subeq0
      syl2anc adantll mpbid adantlr vu cv chil wcel vu cv c0v wne vv cv chil
      wcel vu cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv co
      vv cv cT cfv wceq vu cv cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu
      cv vu cv csp co cmul co wceq wb vu cv cT cnl cfv cort cfv wcel vu cv chil
      wcel vu cv c0v wne wa vv cv chil wcel wa vu cv cT cfv vv cv vu cv csp co
      cmul co cc wcel vv cv cT cfv cc wcel vu cv vu cv csp co cc wcel vu cv vu
      cv csp co cc0 wne wa vu cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv
      csp co cdiv co vv cv cT cfv wceq vu cv cT cfv vv cv vu cv csp co cmul co
      vv cv cT cfv vu cv vu cv csp co cmul co wceq wb vu cv chil wcel vv cv
      chil wcel vu cv cT cfv vv cv vu cv csp co cmul co cc wcel vu cv c0v wne
      vu cv chil wcel vv cv chil wcel wa vu cv cT cfv vv cv vu cv csp co vu cv
      chil wcel vu cv cT cfv cc wcel vv cv chil wcel chil cc vu cv cT cT
      nlelch.1 lnfnfi ffvelrni adantr vv cv chil wcel vu cv chil wcel vv cv vu
      cv csp co cc wcel vv cv vu cv hicl ancoms mulcld adantlr vv cv chil wcel
      vv cv cT cfv cc wcel vu cv chil wcel vu cv c0v wne wa chil cc vv cv cT cT
      nlelch.1 lnfnfi ffvelrni adantl vu cv chil wcel vu cv c0v wne wa vu cv vu
      cv csp co cc wcel vu cv vu cv csp co cc0 wne wa vv cv chil wcel vu cv
      chil wcel vu cv c0v wne wa vu cv vu cv csp co cc wcel vu cv vu cv csp co
      cc0 wne vu cv chil wcel vu cv vu cv csp co cc wcel vu cv c0v wne vu cv
      chil wcel vu cv vu cv csp co cc wcel vu cv vu cv hicl anidms adantr vu cv
      chil wcel vu cv vu cv csp co cc0 wne vu cv c0v wne vu cv chil wcel vu cv
      vu cv csp co cc0 vu cv c0v vu cv his6 necon3bid biimpar jca adantr vu cv
      cT cfv vv cv vu cv csp co cmul co vv cv cT cfv vu cv vu cv csp co divmul3
      syl3anc adantlll mpbird vu cv chil wcel vu cv c0v wne vv cv chil wcel vu
      cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv co vv cv vu
      cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co csp co wceq vu
      cv cT cnl cfv cort cfv wcel vu cv chil wcel vu cv c0v wne wa vv cv chil
      wcel wa vu cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv
      co vu cv cT cfv vu cv vu cv csp co cdiv co vv cv vu cv csp co cmul co vv
      cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co csp co vu
      cv chil wcel vu cv c0v wne wa vv cv chil wcel wa vu cv cT cfv cc wcel vv
      cv vu cv csp co cc wcel vu cv vu cv csp co cc wcel vu cv vu cv csp co cc0
      wne wa vu cv cT cfv vv cv vu cv csp co cmul co vu cv vu cv csp co cdiv co
      vu cv cT cfv vu cv vu cv csp co cdiv co vv cv vu cv csp co cmul co wceq
      vu cv chil wcel vu cv c0v wne wa vu cv cT cfv cc wcel vv cv chil wcel vu
      cv chil wcel vu cv cT cfv cc wcel vu cv c0v wne chil cc vu cv cT cT
      nlelch.1 lnfnfi ffvelrni adantr adantr vu cv chil wcel vv cv chil wcel vv
      cv vu cv csp co cc wcel vu cv c0v wne vv cv chil wcel vu cv chil wcel vv
      cv vu cv csp co cc wcel vv cv vu cv hicl ancoms adantlr vu cv chil wcel
      vu cv c0v wne wa vu cv vu cv csp co cc wcel vu cv vu cv csp co cc0 wne wa
      vv cv chil wcel vu cv chil wcel vu cv c0v wne wa vu cv vu cv csp co cc
      wcel vu cv vu cv csp co cc0 wne vu cv chil wcel vu cv vu cv csp co cc
      wcel vu cv c0v wne vu cv chil wcel vu cv vu cv csp co cc wcel vu cv vu cv
      hicl anidms adantr vu cv chil wcel vu cv vu cv csp co cc0 wne vu cv c0v
      wne vu cv chil wcel vu cv vu cv csp co cc0 vu cv c0v vu cv his6 necon3bid
      biimpar jca adantr vu cv cT cfv vv cv vu cv csp co vu cv vu cv csp co
      div23 syl3anc vu cv chil wcel vu cv c0v wne wa vv cv chil wcel wa vu cv
      cT cfv vu cv vu cv csp co cdiv co cc wcel vv cv chil wcel vu cv chil wcel
      vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co csp co
      vu cv cT cfv vu cv vu cv csp co cdiv co vv cv vu cv csp co cmul co wceq
      vu cv chil wcel vu cv c0v wne wa vu cv cT cfv vu cv vu cv csp co cdiv co
      cc wcel vv cv chil wcel vu cv chil wcel vu cv c0v wne wa vu cv cT cfv vu
      cv vu cv csp co vu cv chil wcel vu cv cT cfv cc wcel vu cv c0v wne chil
      cc vu cv cT cT nlelch.1 lnfnfi ffvelrni adantr vu cv chil wcel vu cv vu
      cv csp co cc wcel vu cv c0v wne vu cv chil wcel vu cv vu cv csp co cc
      wcel vu cv vu cv hicl anidms adantr vu cv chil wcel vu cv vu cv csp co
      cc0 wne vu cv c0v wne vu cv chil wcel vu cv vu cv csp co cc0 vu cv c0v vu
      cv his6 necon3bid biimpar divcld adantr vu cv chil wcel vu cv c0v wne wa
      vv cv chil wcel simpr vu cv chil wcel vu cv c0v wne vv cv chil wcel
      simpll vu cv cT cfv vu cv vu cv csp co cdiv co vv cv vu cv his52 syl3anc
      eqtr4d adantlll eqtr3d ralrimiva vv cv cT cfv vv cv vw cv csp co wceq vv
      chil wral vv cv cT cfv vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj
      cfv vu cv csm co csp co wceq vv chil wral vw vu cv cT cfv vu cv vu cv csp
      co cdiv co ccj cfv vu cv csm co chil vw cv vu cv cT cfv vu cv vu cv csp
      co cdiv co ccj cfv vu cv csm co wceq vv cv cT cfv vv cv vw cv csp co wceq
      vv cv cT cfv vv cv vu cv cT cfv vu cv vu cv csp co cdiv co ccj cfv vu cv
      csm co csp co wceq vv chil vw cv vu cv cT cfv vu cv vu cv csp co cdiv co
      ccj cfv vu cv csm co wceq vv cv vw cv csp co vv cv vu cv cT cfv vu cv vu
      cv csp co cdiv co ccj cfv vu cv csm co csp co vv cv cT cfv vw cv vu cv cT
      cfv vu cv vu cv csp co cdiv co ccj cfv vu cv csm co vv cv csp oveq2
      eqeq2d ralbidv rspcev syl2anc ex mpdan rexlimiv sylbi pm2.61ine $.)"
},



{R"($(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Positive operators (cont.)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Ordering relation for positive operators.  Definition of positive
       operator ordering in [Kreyszig] p. 470.  (Contributed by NM,
       23-Jul-2006.)  (New usage is discouraged.) $)
    leopg $p |- ( ( T e. A /\ U e. B ) -> ( T <_op U <-> ( ( U -op T ) e.
                HrmOp /\ A. x e. ~H 0 <_ ( ( ( U -op T ) ` x ) .ih x ) ) ) ) $=)",
R"(
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
},
{
R"($(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                    Zermelo-Fraenkel Set Theory
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
             ZF Set Theory - start with the Axiom of Extensionality
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Logic is a prerequisite. $)
$( $[ logic.mm $] $) $( Use this if logic is separated out of set.mm. $)
)",
R"($(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
             ZF Set Theory - start with the Axiom of Extensionality
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)
)"
},
{
R"($( Alternate version of the Tarski-Grothendieck Axiom.  (Contributed by NM,
       18-Mar-2007.) $)
    axgroth2 $p |- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\
                       E. w e. y A. v ( v C_ z -> v e. w ) ) /\
                     A. z ( z C_ y -> ( y ~<_ z \/ z e. y ) ) ) $=
      vx cv vy cv wcel vw cv vz cv wss vw cv vy cv wcel wi vw wal vv cv vz cv
      wss vv cv vw cv wcel wi vv wal vw vy cv wrex wa vz vy cv wral vz cv vy cv
      wss vy cv vz cv cdom wbr vz cv vy cv wcel wo wi vz wal w3a vy wex vx cv
      vy cv wcel vw cv vz cv wss vw cv vy cv wcel wi vw wal vv cv vz cv wss vv
      cv vw cv wcel wi vv wal vw vy cv wrex wa vz vy cv wral vz cv vy cv wss vz
      cv vy cv cen wbr vz cv vy cv wcel wo wi vz wal w3a vy wex vx vy vz vw vv
      ax-groth vx cv vy cv wcel vw cv vz cv wss vw cv vy cv wcel wi vw wal vv
      cv vz cv wss vv cv vw cv wcel wi vv wal vw vy cv wrex wa vz vy cv wral vz
      cv vy cv wss vy cv vz cv cdom wbr vz cv vy cv wcel wo wi vz wal w3a vx cv
      vy cv wcel vw cv vz cv wss vw cv vy cv wcel wi vw wal vv cv vz cv wss vv
      cv vw cv wcel wi vv wal vw vy cv wrex wa vz vy cv wral vz cv vy cv wss vz
      cv vy cv cen wbr vz cv vy cv wcel wo wi vz wal w3a vy vz cv vy cv wss vy
      cv vz cv cdom wbr vz cv vy cv wcel wo wi vz wal vz cv vy cv wss vz cv vy
      cv cen wbr vz cv vy cv wcel wo wi vz wal vx cv vy cv wcel vw cv vz cv wss
      vw cv vy cv wcel wi vw wal vv cv vz cv wss vv cv vw cv wcel wi vv wal vw
      vy cv wrex wa vz vy cv wral vz cv vy cv wss vy cv vz cv cdom wbr vz cv vy
      cv wcel wo wi vz cv vy cv wss vz cv vy cv cen wbr vz cv vy cv wcel wo wi
      vz vz cv vy cv wss vy cv vz cv cdom wbr vz cv vy cv wcel wo vz cv vy cv
      cen wbr vz cv vy cv wcel wo vz cv vy cv wss vy cv vz cv cdom wbr vz cv vy
      cv cen wbr vz cv vy cv wcel vz cv vy cv wss vy cv vz cv cdom wbr vz cv vy
      cv cdom wbr vy cv vz cv cdom wbr wa vz cv vy cv cen wbr vz cv vy cv wss
      vz cv vy cv cdom wbr vy cv vz cv cdom wbr vy cv cvv wcel vz cv vy cv wss
      vz cv vy cv cdom wbr wi vy vex vz cv vy cv cvv ssdomg ax-mp biantrurd vz
      cv vy cv sbthb syl6bb orbi1d pm5.74i albii 3anbi3i exbii mpbir $.
      $( [10-Sep-2017] $)
)",
R"($( Alternate version of the Tarski-Grothendieck Axiom.  (Contributed by NM,
       18-Mar-2007.) $)
    axgroth2 $p |- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\
                       E. w e. y A. v ( v C_ z -> v e. w ) ) /\
                     A. z ( z C_ y -> ( y ~<_ z \/ z e. y ) ) ) $=
      vx cv vy cv wcel vw cv vz cv wss vw cv vy cv wcel wi vw wal vv cv vz cv
      wss vv cv vw cv wcel wi vv wal vw vy cv wrex wa vz vy cv wral vz cv vy cv
      wss vy cv vz cv cdom wbr vz cv vy cv wcel wo wi vz wal w3a vy wex vx cv
      vy cv wcel vw cv vz cv wss vw cv vy cv wcel wi vw wal vv cv vz cv wss vv
      cv vw cv wcel wi vv wal vw vy cv wrex wa vz vy cv wral vz cv vy cv wss vz
      cv vy cv cen wbr vz cv vy cv wcel wo wi vz wal w3a vy wex vx vy vz vw vv
      ax-groth vx cv vy cv wcel vw cv vz cv wss vw cv vy cv wcel wi vw wal vv
      cv vz cv wss vv cv vw cv wcel wi vv wal vw vy cv wrex wa vz vy cv wral vz
      cv vy cv wss vy cv vz cv cdom wbr vz cv vy cv wcel wo wi vz wal w3a vx cv
      vy cv wcel vw cv vz cv wss vw cv vy cv wcel wi vw wal vv cv vz cv wss vv
      cv vw cv wcel wi vv wal vw vy cv wrex wa vz vy cv wral vz cv vy cv wss vz
      cv vy cv cen wbr vz cv vy cv wcel wo wi vz wal w3a vy vz cv vy cv wss vy
      cv vz cv cdom wbr vz cv vy cv wcel wo wi vz wal vz cv vy cv wss vz cv vy
      cv cen wbr vz cv vy cv wcel wo wi vz wal vx cv vy cv wcel vw cv vz cv wss
      vw cv vy cv wcel wi vw wal vv cv vz cv wss vv cv vw cv wcel wi vv wal vw
      vy cv wrex wa vz vy cv wral vz cv vy cv wss vy cv vz cv cdom wbr vz cv vy
      cv wcel wo wi vz cv vy cv wss vz cv vy cv cen wbr vz cv vy cv wcel wo wi
      vz vz cv vy cv wss vy cv vz cv cdom wbr vz cv vy cv wcel wo vz cv vy cv
      cen wbr vz cv vy cv wcel wo vz cv vy cv wss vy cv vz cv cdom wbr vz cv vy
      cv cen wbr vz cv vy cv wcel vz cv vy cv wss vy cv vz cv cdom wbr vz cv vy
      cv cdom wbr vy cv vz cv cdom wbr wa vz cv vy cv cen wbr vz cv vy cv wss
      vz cv vy cv cdom wbr vy cv vz cv cdom wbr vy cv cvv wcel vz cv vy cv wss
      vz cv vy cv cdom wbr wi vy vex vz cv vy cv cvv ssdomg ax-mp biantrurd vz
      cv vy cv sbthb syl6bb orbi1d pm5.74i albii 3anbi3i exbii mpbir $.
      $( [10-Sep-2017] $)
  $}
)"
},
{
R"(cfv chil wss cn chil vf cv wf cn cT cnl cfv vf cv wf vf cv vx cv chli wbr
      simpl cT cnl cfv cT nlelch.1 nlelshi shssii cn cT cnl cfv chil vf cv fss
      sylancl chil cn cT vf cv fnfco sylancr cn cc0 csn cn cc0 csn cxp wf cn
      cc0 csn cxp cn wfn cn cc0 c0ex fconst cn cc0 csn cn cc0 csn cxp ffn ax-mp
      vn cn cT vf cv ccom cn cc0 csn cxp eqfnfv sylancl mpbird cn cT cnl cfv vf
      cv wf vf cv vx cv chli wbr wa ccnfld ctopn cfv cc ctopon cfv wcel cc0 cc
      wcel c1 cz wcel cn cc0 csn cxp cc0 ccnfld ctopn cfv clm cfv wbr ccnfld
      ctopn cfv cc ctopon cfv wcel cn cT cnl cfv vf cv wf vf cv vx cv chli wbr
      wa ccnfld ctopn cfv ccnfld ctopn cfv eqid cnfldtopon a1i cc0 cc wcel cn
      cT cnl cfv vf cv wf vf cv vx cv chli wbr wa 0cn a1i c1 cz wcel cn cT cnl
      cfv vf cv wf vf cv vx cv chli wbr wa 1z a1i cc0 ccnfld ctopn cfv c1 cc cn
      nnuz lmconst syl3anc eqbrtrd lmmo chil cc cT wf vx cv cT cnl cfv wcel vx
      cv chil wcel vx cv cT cfv cc0 wceq wa wb cT nlelch.1 lnfnfi vx cv cT
      elnlfn ax-mp sylanbrc gen2 vx vf cT cnl cfv isch2 mpbir2an $.
      $( [10-Sep-2017] $))",
R"(cfv chil wss cn chil vf cv wf cn cT cnl cfv vf cv wf vf cv vx cv chli wbr
      simpl cT cnl cfv cT nlelch.1 nlelshi shssii cn cT cnl cfv chil vf cv fss
      sylancl chil cn cT vf cv fnfco sylancr cn cc0 csn cn cc0 csn cxp wf cn
      cc0 csn cxp cn wfn cn cc0 c0ex fconst cn cc0 csn cn cc0 csn cxp ffn ax-mp
      vn cn cT vf cv ccom cn cc0 csn cxp eqfnfv sylancl mpbird cn cT cnl cfv vf
      cv wf vf cv vx cv chli wbr wa ccnfld ctopn cfv cc ctopon cfv wcel cc0 cc
      wcel c1 cz wcel cn cc0 csn cxp cc0 ccnfld ctopn cfv clm cfv wbr ccnfld
      ctopn cfv cc ctopon cfv wcel cn cT cnl cfv vf cv wf vf cv vx cv chli wbr
      wa ccnfld ctopn cfv ccnfld ctopn cfv eqid cnfldtopon a1i cc0 cc wcel cn
      cT cnl cfv vf cv wf vf cv vx cv chli wbr wa 0cn a1i c1 cz wcel cn cT cnl
      cfv vf cv wf vf cv vx cv chli wbr wa 1z a1i cc0 ccnfld ctopn cfv c1 cc cn
      nnuz lmconst syl3anc eqbrtrd lmmo chil cc cT wf vx cv cT cnl cfv wcel vx
      cv chil wcel vx cv cT cfv cc0 wceq wa wb cT nlelch.1 lnfnfi vx cv cT
      elnlfn ax-mp sylanbrc gen2 vx vf cT cnl cfv isch2 mpbir2an $.
      $( [10-Sep-2017] $)
  $}
)"
},
{
R"(nlelch.1 nlelch.2 riesz3i vv cv cT cfv vv cv vw cv csp co wceq vv chil
      wral vv cv cT cfv vv cv vu cv csp co wceq vv chil wral wa vw cv vu cv
      wceq wi vw vu chil vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vv
      cv cT cfv vv cv vu cv csp co wceq vv chil wral wa vv cv vw cv csp co vv
      cv vu cv csp co cmin co cc0 wceq vv chil wral vw cv chil wcel vu cv chil
      wcel wa vw cv vu cv wceq vv cv cT cfv vv cv vw cv csp co wceq vv chil
      wral vv cv cT cfv vv cv vu cv csp co wceq vv chil wral wa vv cv cT cfv vv
      cv vw cv csp co wceq vv cv cT cfv vv cv vu cv csp co wceq wa vv chil wral
      vv cv vw cv csp co vv cv vu cv csp co cmin co cc0 wceq vv chil wral vv cv
      cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv cv vu cv csp co wceq vv
      chil r19.26 vv cv cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv cv vu cv
      csp co wceq wa vv cv vw cv csp co vv cv vu cv csp co cmin co cc0 wceq vv
      chil vv cv chil wcel vv cv cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv
      cv vu cv csp co wceq wa wa vv cv cT cfv vv cv cT cfv cmin co vv cv vw cv
      csp co vv cv vu cv csp co cmin co cc0 vv cv cT cfv vv cv vw cv csp co
      wceq vv cv cT cfv vv cv vu cv csp co wceq wa vv cv cT cfv vv cv cT cfv
      cmin co vv cv vw cv csp co vv cv vu cv csp co cmin co wceq vv cv chil
      wcel vv cv cT cfv vv cv vw cv csp co vv cv cT cfv vv cv vu cv csp co cmin
      oveq12 adantl vv cv chil wcel vv cv cT cfv vv cv cT cfv cmin co cc0 wceq
      vv cv cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv cv vu cv csp co wceq
      wa vv cv chil wcel vv cv cT cfv chil cc vv cv cT cT nlelch.1 lnfnfi)",
R"(riesz3.1 riesz3.2 riesz3i vv cv cT cfv vv cv vw cv csp co wceq vv chil
      wral vv cv cT cfv vv cv vu cv csp co wceq vv chil wral wa vw cv vu cv
      wceq wi vw vu chil vv cv cT cfv vv cv vw cv csp co wceq vv chil wral vv
      cv cT cfv vv cv vu cv csp co wceq vv chil wral wa vv cv vw cv csp co vv
      cv vu cv csp co cmin co cc0 wceq vv chil wral vw cv chil wcel vu cv chil
      wcel wa vw cv vu cv wceq vv cv cT cfv vv cv vw cv csp co wceq vv chil
      wral vv cv cT cfv vv cv vu cv csp co wceq vv chil wral wa vv cv cT cfv vv
      cv vw cv csp co wceq vv cv cT cfv vv cv vu cv csp co wceq wa vv chil wral
      vv cv vw cv csp co vv cv vu cv csp co cmin co cc0 wceq vv chil wral vv cv
      cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv cv vu cv csp co wceq vv
      chil r19.26 vv cv cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv cv vu cv
      csp co wceq wa vv cv vw cv csp co vv cv vu cv csp co cmin co cc0 wceq vv
      chil vv cv chil wcel vv cv cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv
      cv vu cv csp co wceq wa wa vv cv cT cfv vv cv cT cfv cmin co vv cv vw cv
      csp co vv cv vu cv csp co cmin co cc0 vv cv cT cfv vv cv vw cv csp co
      wceq vv cv cT cfv vv cv vu cv csp co wceq wa vv cv cT cfv vv cv cT cfv
      cmin co vv cv vw cv csp co vv cv vu cv csp co cmin co wceq vv cv chil
      wcel vv cv cT cfv vv cv vw cv csp co vv cv cT cfv vv cv vu cv csp co cmin
      oveq12 adantl vv cv chil wcel vv cv cT cfv vv cv cT cfv cmin co cc0 wceq
      vv cv cT cfv vv cv vw cv csp co wceq vv cv cT cfv vv cv vu cv csp co wceq
      wa vv cv chil wcel vv cv cT cfv chil cc vv cv cT cT riesz3.1 lnfnfi)"
},

{
R"(wa cC cB cbr cfv cfv cc wcel cD cbr cfv clf ccnfn cin wcel cC cB cbr cfv
      cfv cD cbr cfv chft co cbr ccnv cfv cC cB cbr cfv cfv ccj cfv cD cbr cfv
      cbr ccnv cfv csm co wceq cD chil wcel cB cC bracl cD bracnln cC cB cbr
      cfv cfv cD cbr cfv cnvbramul syl2an cB chil wcel cC chil wcel wa cD chil
      wcel cC cB cbr cfv cfv ccj cfv cC cB csp co ccj cfv cD cbr cfv cbr ccnv
      cfv cD csm cB chil wcel cC chil wcel wa cC cB cbr cfv cfv cC cB csp co
      ccj cB cC braval fveq2d cD cnvbrabra oveqan12d eqtr2d anasss cB chil wcel
      cC chil wcel cD chil wcel wa wa cC cB cbr cfv cfv cD cbr cfv chft co cB
      cbr cfv cC cD ck co ccom cbr ccnv cB chil wcel cC chil wcel cD chil wcel
      cC cB cbr cfv cfv cD cbr cfv chft co cB cbr cfv cC cD ck co ccom wceq cB
      cC cD kbass2 3expb fveq2d eqtr2d adantll oveq2d eqtr4d 3eqtrd $.
      $( [10-Sep-2017] $))",
R"(wa cC cB cbr cfv cfv cc wcel cD cbr cfv clf ccnfn cin wcel cC cB cbr cfv
      cfv cD cbr cfv chft co cbr ccnv cfv cC cB cbr cfv cfv ccj cfv cD cbr cfv
      cbr ccnv cfv csm co wceq cD chil wcel cB cC bracl cD bracnln cC cB cbr
      cfv cfv cD cbr cfv cnvbramul syl2an cB chil wcel cC chil wcel wa cD chil
      wcel cC cB cbr cfv cfv ccj cfv cC cB csp co ccj cfv cD cbr cfv cbr ccnv
      cfv cD csm cB chil wcel cC chil wcel wa cC cB cbr cfv cfv cC cB csp co
      ccj cB cC braval fveq2d cD cnvbrabra oveqan12d eqtr2d anasss cB chil wcel
      cC chil wcel cD chil wcel wa wa cC cB cbr cfv cfv cD cbr cfv chft co cB
      cbr cfv cC cD ck co ccom cbr ccnv cB chil wcel cC chil wcel cD chil wcel
      cC cB cbr cfv cfv cD cbr cfv chft co cB cbr cfv cC cD ck co ccom wceq cB
      cC cD kbass2 3expb fveq2d eqtr2d adantll oveq2d eqtr4d 3eqtrd $.
      $( [10-Sep-2017] $)
  $}
)"
},
{
R"(riesz1 $p |- ( T e. LinFn -> ( ( normfn ` T ) e. RR <->
                  E. y e. ~H A. x e. ~H ( T ` x ) = ( x .ih y ) ) ) $=
      cT clf wcel cT ccnfn wcel cT cnmf cfv cr wcel vx cv cT cfv vx cv vy cv
      csp co wceq vx chil wral vy chil wrex cT lnfncnbd cT clf wcel cT ccnfn
      wcel vx cv cT cfv vx cv vy cv csp co wceq vx chil wral vy chil wrex cT
      clf wcel cT ccnfn wcel vx cv cT cfv vx cv vy cv csp co wceq vx chil wral
      vy chil wrex cT clf wcel cT ccnfn wcel wa cT clf ccnfn cin wcel vx cv cT
      cfv vx cv vy cv csp co wceq vx chil wral vy chil wrex cT clf ccnfn elin
      cT clf ccnfn cin wcel vx cv cT cfv vx cv vy cv csp co wceq vx chil wral)",
R"(riesz1 $p |- ( T e. LinFn -> ( ( normfn ` T ) e. RR <->
                  E. y e. ~H A. x e. ~H ( T ` x ) = ( x .ih y ) ) ) $=
      cT clf wcel cT ccnfn wcel cT cnmf cfv cr wcel vx cv cT cfv vx cv vy cv
      csp co wceq vx chil wral vy chil wrex cT lnfncnbd cT clf wcel cT ccnfn
      wcel vx cv cT cfv vx cv vy cv csp co wceq vx chil wral vy chil wrex cT
      clf wcel cT ccnfn wcel vx cv cT cfv vx cv vy cv csp co wceq vx chil wral
      vy chil wrex cT clf wcel cT ccnfn wcel wa cT clf ccnfn cin wcel vx cv cT
      cfv vx cv vy cv csp co wceq vx chil wral vy chil wrex cT clf ccnfn elin
      cT clf ccnfn cin wcel vx cv cT cfv vx cv vy cv csp co wceq vx chil wral)"
},
{
	R"(metamath 'read set.mm' 'save proof */c/f' 'write source set.mm/rewrap')",
	R"(metamath 'read set.mm' 'save proof * /c/f' 'write source set.mm/rewrap')"
}
};

Section* parse(const Path& in, const Path& out) {
	string data;
	in.read(data, &cut_patches);
	LocationIter iter(data.begin(), Lex::toInt(in.name()));
	LocationIter end(data.end(), Lex::toInt(in.name()));
	Section* source = new Section;
	source->root = (out.root().size() && out.root().back() != '/') ? (out.root() + "/") : out.root();
	source->file = in.name();
	source->dir = "";
	source->path = source->dir + "/" + source->file + ".mm";
	source->type = Type::SOURCE;
	bool r = phrase_parse(iter, end, Grammar(source->root), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed", in.name());
	}
	return source;
}

} // cut_

void cut(uint src, uint tgt, uint tgt_root) {
	Sys::timer()["cut"].start();
	Path in(Lex::toStr(src), Sys::conf().get("root"), "mm");
	Path out(Lex::toStr(tgt), Lex::toStr(tgt_root), "mm");
	Section* root = cut_::parse(in, out);
	for (Section* sect = root; sect; sect = sect->next_sect) sect->split();
	for (const Section* sect = root; sect; sect = sect->next_sect) sect->save();
	delete root;
	Sys::timer()["cut"].stop();
}

}} // mdl::mm
