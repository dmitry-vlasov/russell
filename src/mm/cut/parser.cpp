#include <boost/algorithm/string.hpp>

#include "mm/cut/grammar.hpp"

namespace mdl { namespace mm { namespace cut {

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

Section* parse(string root_in, string in, string root_out) {
	string data;
	//ifstream ifn = open_smart(in, root);

	boost::trim(in);
	boost::trim(root_in);
	if (root_in.size() && root_in.back() != '/') root_in += '/';
	if (root_out.size() && root_out.back() != '/') root_out += '/';
	string path = (root_in.size() ? root_in : ".") + "/" + in + ".mm";
	ifstream ifn;
	ifn.open(path, std::ios_base::in);
	if (ifn.fail()) throw Error("failed to open", path);

	read_smart(data, ifn);
	patch(data);

	LocationIter iter(data.begin(), in);
	LocationIter end(data.end(), in);
	Section* source = new Section;

	size_t slash_pos = in.find_last_of("/");
	size_t dot_pos = in.find_last_of(".");
	size_t len = in.size();
	if (slash_pos != string::npos) len -= slash_pos;
	if (dot_pos != string::npos)   len -= len - dot_pos;

	source->root = root_out;
	source->file = in.substr(slash_pos == string::npos ? 0 : slash_pos, len);
	source->dir = "";
	source->path = source->dir + "/" + source->file + ".mm";
	source->type = Type::SOURCE;
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(root_out), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed", in);
	}
	return source;
}

}}} // mdl::mm::cut
