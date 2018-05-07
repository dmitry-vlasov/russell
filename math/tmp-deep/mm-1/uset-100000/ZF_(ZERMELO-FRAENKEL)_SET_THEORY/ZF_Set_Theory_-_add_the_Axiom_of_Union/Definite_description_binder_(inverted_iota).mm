$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Relations.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Definite description binder (inverted iota)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c iota  $.
$( Extend class notation with Russell's definition description binder
     (inverted iota). $)
${
	$v ph $.
	$v x $.
	fcio_0 $f wff ph $.
	fcio_1 $f set x $.
	cio $a class ( iota x ph ) $.
$}
$( Soundness justification theorem for ~ df-iota .  (Contributed by Andrew
       Salmon, 29-Jun-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x z $.
	$d ph w z $.
	$d ph w y $.
	$d x y $.
	iiotajust_0 $f set w $.
	fiotajust_0 $f wff ph $.
	fiotajust_1 $f set x $.
	fiotajust_2 $f set y $.
	fiotajust_3 $f set z $.
	iotajust $p |- U. { y | { x | ph } = { y } } = U. { z | { x | ph } = { z } } $= fiotajust_0 fiotajust_1 cab fiotajust_2 sup_set_class csn wceq fiotajust_2 cab fiotajust_0 fiotajust_1 cab fiotajust_3 sup_set_class csn wceq fiotajust_3 cab fiotajust_0 fiotajust_1 cab fiotajust_2 sup_set_class csn wceq fiotajust_2 cab fiotajust_0 fiotajust_1 cab iiotajust_0 sup_set_class csn wceq iiotajust_0 cab fiotajust_0 fiotajust_1 cab fiotajust_3 sup_set_class csn wceq fiotajust_3 cab fiotajust_0 fiotajust_1 cab fiotajust_2 sup_set_class csn wceq fiotajust_0 fiotajust_1 cab iiotajust_0 sup_set_class csn wceq fiotajust_2 iiotajust_0 fiotajust_2 sup_set_class iiotajust_0 sup_set_class wceq fiotajust_2 sup_set_class csn iiotajust_0 sup_set_class csn fiotajust_0 fiotajust_1 cab fiotajust_2 sup_set_class iiotajust_0 sup_set_class sneq eqeq2d cbvabv fiotajust_0 fiotajust_1 cab iiotajust_0 sup_set_class csn wceq fiotajust_0 fiotajust_1 cab fiotajust_3 sup_set_class csn wceq iiotajust_0 fiotajust_3 iiotajust_0 sup_set_class fiotajust_3 sup_set_class wceq iiotajust_0 sup_set_class csn fiotajust_3 sup_set_class csn fiotajust_0 fiotajust_1 cab iiotajust_0 sup_set_class fiotajust_3 sup_set_class sneq eqeq2d cbvabv eqtri unieqi $.
$}
$( Define Russell's definition description binder, which can be read as
       "the unique ` x ` such that ` ph ` ," where ` ph ` ordinarily contains
       ` x ` as a free variable.  Our definition is meaningful only when there
       is exactly one ` x ` such that ` ph ` is true (see ~ iotaval );
       otherwise, it evaluates to the empty set (see ~ iotanul ).  Russell used
       the inverted iota symbol ` iota ` to represent the binder.

       Sometimes proofs need to expand an iota-based definition.  That is,
       given "X = the x for which ... x ... x ..." holds, the proof needs to
       get to "...  X ...  X ...".  A general strategy to do this is to use
       ~ riotacl2 (or ~ iotacl for unbounded iota), as demonstrated in the
       proof of ~ supub .  This can be easier than applying ~ riotasbc or a
       version that applies an explicit substitution, because substituting an
       iota into its own property always has a bound variable clash which must
       be first renamed or else guarded with NF.

       (Contributed by Andrew Salmon, 30-Jun-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d y x $.
	$d y ph $.
	fdf-iota_0 $f wff ph $.
	fdf-iota_1 $f set x $.
	fdf-iota_2 $f set y $.
	df-iota $a |- ( iota x ph ) = U. { y | { x | ph } = { y } } $.
$}
$( Alternate definition for descriptions.  Definition 8.18 in [Quine]
       p. 56.  (Contributed by Andrew Salmon, 30-Jun-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d y x $.
	$d y ph $.
	fdfiota2_0 $f wff ph $.
	fdfiota2_1 $f set x $.
	fdfiota2_2 $f set y $.
	dfiota2 $p |- ( iota x ph ) = U. { y | A. x ( ph <-> x = y ) } $= fdfiota2_0 fdfiota2_1 cio fdfiota2_0 fdfiota2_1 cab fdfiota2_2 sup_set_class csn wceq fdfiota2_2 cab cuni fdfiota2_0 fdfiota2_1 sup_set_class fdfiota2_2 sup_set_class wceq wb fdfiota2_1 wal fdfiota2_2 cab cuni fdfiota2_0 fdfiota2_1 fdfiota2_2 df-iota fdfiota2_0 fdfiota2_1 cab fdfiota2_2 sup_set_class csn wceq fdfiota2_2 cab fdfiota2_0 fdfiota2_1 sup_set_class fdfiota2_2 sup_set_class wceq wb fdfiota2_1 wal fdfiota2_2 cab fdfiota2_0 fdfiota2_1 cab fdfiota2_2 sup_set_class csn wceq fdfiota2_0 fdfiota2_1 sup_set_class fdfiota2_2 sup_set_class wceq wb fdfiota2_1 wal fdfiota2_2 fdfiota2_0 fdfiota2_1 cab fdfiota2_2 sup_set_class csn wceq fdfiota2_0 fdfiota2_1 cab fdfiota2_1 sup_set_class fdfiota2_2 sup_set_class wceq fdfiota2_1 cab wceq fdfiota2_0 fdfiota2_1 sup_set_class fdfiota2_2 sup_set_class wceq wb fdfiota2_1 wal fdfiota2_2 sup_set_class csn fdfiota2_1 sup_set_class fdfiota2_2 sup_set_class wceq fdfiota2_1 cab fdfiota2_0 fdfiota2_1 cab fdfiota2_1 fdfiota2_2 sup_set_class df-sn eqeq2i fdfiota2_0 fdfiota2_1 sup_set_class fdfiota2_2 sup_set_class wceq fdfiota2_1 abbi bitr4i abbii unieqi eqtri $.
$}
$( Bound-variable hypothesis builder for the ` iota ` class.  (Contributed
       by Andrew Salmon, 11-Jul-2011.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	$d y ph $.
	infiota1_0 $f set y $.
	fnfiota1_0 $f wff ph $.
	fnfiota1_1 $f set x $.
	nfiota1 $p |- F/_ x ( iota x ph ) $= fnfiota1_1 fnfiota1_0 fnfiota1_1 cio fnfiota1_0 fnfiota1_1 sup_set_class infiota1_0 sup_set_class wceq wb fnfiota1_1 wal infiota1_0 cab cuni fnfiota1_0 fnfiota1_1 infiota1_0 dfiota2 fnfiota1_1 fnfiota1_0 fnfiota1_1 sup_set_class infiota1_0 sup_set_class wceq wb fnfiota1_1 wal infiota1_0 cab fnfiota1_0 fnfiota1_1 sup_set_class infiota1_0 sup_set_class wceq wb fnfiota1_1 infiota1_0 nfaba1 nfuni nfcxfr $.
$}
$( Deduction version of ~ nfiota .  (Contributed by NM, 18-Feb-2013.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d z ps $.
	$d z ph $.
	$d x z $.
	$d y z $.
	infiotad_0 $f set z $.
	fnfiotad_0 $f wff ph $.
	fnfiotad_1 $f wff ps $.
	fnfiotad_2 $f set x $.
	fnfiotad_3 $f set y $.
	enfiotad_0 $e |- F/ y ph $.
	enfiotad_1 $e |- ( ph -> F/ x ps ) $.
	nfiotad $p |- ( ph -> F/_ x ( iota y ps ) ) $= fnfiotad_0 fnfiotad_2 fnfiotad_1 fnfiotad_3 cio fnfiotad_1 fnfiotad_3 sup_set_class infiotad_0 sup_set_class wceq wb fnfiotad_3 wal infiotad_0 cab cuni fnfiotad_1 fnfiotad_3 infiotad_0 dfiota2 fnfiotad_0 fnfiotad_2 fnfiotad_1 fnfiotad_3 sup_set_class infiotad_0 sup_set_class wceq wb fnfiotad_3 wal infiotad_0 cab fnfiotad_0 fnfiotad_1 fnfiotad_3 sup_set_class infiotad_0 sup_set_class wceq wb fnfiotad_3 wal fnfiotad_2 infiotad_0 fnfiotad_0 infiotad_0 nfv fnfiotad_0 fnfiotad_1 fnfiotad_3 sup_set_class infiotad_0 sup_set_class wceq wb fnfiotad_2 fnfiotad_3 enfiotad_0 fnfiotad_0 fnfiotad_2 sup_set_class fnfiotad_3 sup_set_class wceq fnfiotad_2 wal wn wa fnfiotad_1 fnfiotad_3 sup_set_class infiotad_0 sup_set_class wceq fnfiotad_2 fnfiotad_0 fnfiotad_1 fnfiotad_2 wnf fnfiotad_2 sup_set_class fnfiotad_3 sup_set_class wceq fnfiotad_2 wal wn enfiotad_1 adantr fnfiotad_0 fnfiotad_2 sup_set_class fnfiotad_3 sup_set_class wceq fnfiotad_2 wal wn wa fnfiotad_2 fnfiotad_3 sup_set_class infiotad_0 sup_set_class fnfiotad_2 sup_set_class fnfiotad_3 sup_set_class wceq fnfiotad_2 wal wn fnfiotad_2 fnfiotad_3 sup_set_class wnfc fnfiotad_0 fnfiotad_2 fnfiotad_3 nfcvf adantl fnfiotad_0 fnfiotad_2 sup_set_class fnfiotad_3 sup_set_class wceq fnfiotad_2 wal wn wa fnfiotad_2 infiotad_0 sup_set_class nfcvd nfeqd nfbid nfald2 nfabd nfunid nfcxfrd $.
$}
$( Bound-variable hypothesis builder for the ` iota ` class.  (Contributed
       by NM, 23-Aug-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fnfiota_0 $f wff ph $.
	fnfiota_1 $f set x $.
	fnfiota_2 $f set y $.
	enfiota_0 $e |- F/ x ph $.
	nfiota $p |- F/_ x ( iota y ph ) $= fnfiota_1 fnfiota_0 fnfiota_2 cio wnfc wtru fnfiota_0 fnfiota_1 fnfiota_2 fnfiota_2 nftru fnfiota_0 fnfiota_1 wnf wtru enfiota_0 a1i nfiotad trud $.
$}
$( Change bound variables in a description binder.  (Contributed by Andrew
       Salmon, 1-Aug-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d z w x $.
	$d z w y $.
	$d z w ph $.
	$d z w ps $.
	icbviota_0 $f set z $.
	icbviota_1 $f set w $.
	fcbviota_0 $f wff ph $.
	fcbviota_1 $f wff ps $.
	fcbviota_2 $f set x $.
	fcbviota_3 $f set y $.
	ecbviota_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	ecbviota_1 $e |- F/ y ph $.
	ecbviota_2 $e |- F/ x ps $.
	cbviota $p |- ( iota x ph ) = ( iota y ps ) $= fcbviota_0 fcbviota_2 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_2 wal icbviota_1 cab cuni fcbviota_1 fcbviota_3 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_3 wal icbviota_1 cab cuni fcbviota_0 fcbviota_2 cio fcbviota_1 fcbviota_3 cio fcbviota_0 fcbviota_2 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_2 wal icbviota_1 cab fcbviota_1 fcbviota_3 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_3 wal icbviota_1 cab fcbviota_0 fcbviota_2 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_2 wal fcbviota_1 fcbviota_3 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_3 wal icbviota_1 fcbviota_0 fcbviota_2 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_2 wal fcbviota_0 fcbviota_2 icbviota_0 wsb icbviota_0 sup_set_class icbviota_1 sup_set_class wceq wb icbviota_0 wal fcbviota_1 fcbviota_3 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_3 wal fcbviota_0 fcbviota_2 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_0 fcbviota_2 icbviota_0 wsb icbviota_0 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_2 icbviota_0 fcbviota_0 fcbviota_2 sup_set_class icbviota_1 sup_set_class wceq wb icbviota_0 nfv fcbviota_0 fcbviota_2 icbviota_0 wsb icbviota_0 sup_set_class icbviota_1 sup_set_class wceq fcbviota_2 fcbviota_0 fcbviota_2 icbviota_0 nfs1v icbviota_0 sup_set_class icbviota_1 sup_set_class wceq fcbviota_2 nfv nfbi fcbviota_2 sup_set_class icbviota_0 sup_set_class wceq fcbviota_0 fcbviota_0 fcbviota_2 icbviota_0 wsb fcbviota_2 sup_set_class icbviota_1 sup_set_class wceq icbviota_0 sup_set_class icbviota_1 sup_set_class wceq fcbviota_0 fcbviota_2 icbviota_0 sbequ12 fcbviota_2 icbviota_0 icbviota_1 equequ1 bibi12d cbval fcbviota_0 fcbviota_2 icbviota_0 wsb icbviota_0 sup_set_class icbviota_1 sup_set_class wceq wb fcbviota_1 fcbviota_3 sup_set_class icbviota_1 sup_set_class wceq wb icbviota_0 fcbviota_3 fcbviota_0 fcbviota_2 icbviota_0 wsb icbviota_0 sup_set_class icbviota_1 sup_set_class wceq fcbviota_3 fcbviota_0 fcbviota_2 icbviota_0 fcbviota_3 ecbviota_1 nfsb icbviota_0 sup_set_class icbviota_1 sup_set_class wceq fcbviota_3 nfv nfbi fcbviota_1 fcbviota_3 sup_set_class icbviota_1 sup_set_class wceq wb icbviota_0 nfv icbviota_0 sup_set_class fcbviota_3 sup_set_class wceq fcbviota_0 fcbviota_2 icbviota_0 wsb fcbviota_1 icbviota_0 sup_set_class icbviota_1 sup_set_class wceq fcbviota_3 sup_set_class icbviota_1 sup_set_class wceq icbviota_0 sup_set_class fcbviota_3 sup_set_class wceq fcbviota_0 fcbviota_2 icbviota_0 wsb fcbviota_0 fcbviota_2 fcbviota_3 wsb fcbviota_1 fcbviota_0 icbviota_0 fcbviota_3 fcbviota_2 sbequ fcbviota_0 fcbviota_1 fcbviota_2 fcbviota_3 ecbviota_2 ecbviota_0 sbie syl6bb icbviota_0 fcbviota_3 icbviota_1 equequ1 bibi12d cbval bitri abbii unieqi fcbviota_0 fcbviota_2 icbviota_1 dfiota2 fcbviota_1 fcbviota_3 icbviota_1 dfiota2 3eqtr4i $.
$}
$( Change bound variables in a description binder.  (Contributed by Andrew
       Salmon, 1-Aug-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d ph y $.
	$d ps x $.
	fcbviotav_0 $f wff ph $.
	fcbviotav_1 $f wff ps $.
	fcbviotav_2 $f set x $.
	fcbviotav_3 $f set y $.
	ecbviotav_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbviotav $p |- ( iota x ph ) = ( iota y ps ) $= fcbviotav_0 fcbviotav_1 fcbviotav_2 fcbviotav_3 ecbviotav_0 fcbviotav_0 fcbviotav_3 nfv fcbviotav_1 fcbviotav_2 nfv cbviota $.
$}
$( Variable substitution in description binder.  Compare ~ sb8eu .
       (Contributed by NM, 18-Mar-2013.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w z ph $.
	$d w z x $.
	$d w z y $.
	isb8iota_0 $f set z $.
	isb8iota_1 $f set w $.
	fsb8iota_0 $f wff ph $.
	fsb8iota_1 $f set x $.
	fsb8iota_2 $f set y $.
	esb8iota_0 $e |- F/ y ph $.
	sb8iota $p |- ( iota x ph ) = ( iota y [ y / x ] ph ) $= fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 wal isb8iota_0 cab cuni fsb8iota_0 fsb8iota_1 fsb8iota_2 wsb fsb8iota_2 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_2 wal isb8iota_0 cab cuni fsb8iota_0 fsb8iota_1 cio fsb8iota_0 fsb8iota_1 fsb8iota_2 wsb fsb8iota_2 cio fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 wal isb8iota_0 cab fsb8iota_0 fsb8iota_1 fsb8iota_2 wsb fsb8iota_2 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_2 wal isb8iota_0 cab fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 wal fsb8iota_0 fsb8iota_1 fsb8iota_2 wsb fsb8iota_2 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_2 wal isb8iota_0 fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 wal fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 isb8iota_1 wsb isb8iota_1 wal fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 fsb8iota_2 wsb fsb8iota_2 wal fsb8iota_0 fsb8iota_1 fsb8iota_2 wsb fsb8iota_2 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_2 wal fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 isb8iota_1 fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb isb8iota_1 nfv sb8 fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 isb8iota_1 wsb fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 fsb8iota_2 wsb isb8iota_1 fsb8iota_2 fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 isb8iota_1 wsb fsb8iota_0 fsb8iota_1 isb8iota_1 wsb fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq fsb8iota_1 isb8iota_1 wsb wb fsb8iota_2 fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq fsb8iota_1 isb8iota_1 sbbi fsb8iota_0 fsb8iota_1 isb8iota_1 wsb fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq fsb8iota_1 isb8iota_1 wsb fsb8iota_2 fsb8iota_0 fsb8iota_1 isb8iota_1 fsb8iota_2 esb8iota_0 nfsb fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq fsb8iota_1 isb8iota_1 wsb isb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq fsb8iota_2 isb8iota_1 fsb8iota_1 isb8iota_0 sup_set_class eqsb3 isb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq fsb8iota_2 nfv nfxfr nfbi nfxfr fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 fsb8iota_2 wsb isb8iota_1 nfv fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb isb8iota_1 fsb8iota_2 fsb8iota_1 sbequ cbval fsb8iota_0 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_1 fsb8iota_2 wsb fsb8iota_0 fsb8iota_1 fsb8iota_2 wsb fsb8iota_2 sup_set_class isb8iota_0 sup_set_class wceq wb fsb8iota_2 fsb8iota_1 sup_set_class isb8iota_0 sup_set_class wceq fsb8iota_2 sup_set_class isb8iota_0 sup_set_class wceq fsb8iota_0 fsb8iota_1 fsb8iota_2 fsb8iota_2 fsb8iota_1 isb8iota_0 equsb3 sblbis albii 3bitri abbii unieqi fsb8iota_0 fsb8iota_1 isb8iota_0 dfiota2 fsb8iota_0 fsb8iota_1 fsb8iota_2 wsb fsb8iota_2 isb8iota_0 dfiota2 3eqtr4i $.
$}
$( Equality theorem for descriptions.  (Contributed by Andrew Salmon,
       30-Jun-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d y z $.
	$d x z $.
	$d ph z $.
	iiotaeq_0 $f set z $.
	fiotaeq_0 $f wff ph $.
	fiotaeq_1 $f set x $.
	fiotaeq_2 $f set y $.
	iotaeq $p |- ( A. x x = y -> ( iota x ph ) = ( iota y ph ) ) $= fiotaeq_1 sup_set_class fiotaeq_2 sup_set_class wceq fiotaeq_1 wal fiotaeq_0 fiotaeq_1 cab iiotaeq_0 sup_set_class csn wceq iiotaeq_0 cab cuni fiotaeq_0 fiotaeq_2 cab iiotaeq_0 sup_set_class csn wceq iiotaeq_0 cab cuni fiotaeq_0 fiotaeq_1 cio fiotaeq_0 fiotaeq_2 cio fiotaeq_1 sup_set_class fiotaeq_2 sup_set_class wceq fiotaeq_1 wal fiotaeq_0 fiotaeq_1 cab iiotaeq_0 sup_set_class csn wceq iiotaeq_0 cab fiotaeq_0 fiotaeq_2 cab iiotaeq_0 sup_set_class csn wceq iiotaeq_0 cab fiotaeq_1 sup_set_class fiotaeq_2 sup_set_class wceq fiotaeq_1 wal fiotaeq_0 fiotaeq_1 cab iiotaeq_0 sup_set_class csn wceq fiotaeq_0 fiotaeq_2 cab iiotaeq_0 sup_set_class csn wceq iiotaeq_0 fiotaeq_1 sup_set_class fiotaeq_2 sup_set_class wceq fiotaeq_1 wal fiotaeq_0 fiotaeq_1 cab fiotaeq_0 fiotaeq_2 cab iiotaeq_0 sup_set_class csn fiotaeq_1 sup_set_class fiotaeq_2 sup_set_class wceq fiotaeq_1 wal iiotaeq_0 fiotaeq_0 fiotaeq_1 cab fiotaeq_0 fiotaeq_2 cab fiotaeq_1 sup_set_class fiotaeq_2 sup_set_class wceq fiotaeq_1 wal fiotaeq_0 fiotaeq_1 iiotaeq_0 wsb fiotaeq_0 fiotaeq_2 iiotaeq_0 wsb iiotaeq_0 sup_set_class fiotaeq_0 fiotaeq_1 cab wcel iiotaeq_0 sup_set_class fiotaeq_0 fiotaeq_2 cab wcel fiotaeq_0 fiotaeq_1 fiotaeq_2 iiotaeq_0 drsb1 fiotaeq_0 iiotaeq_0 fiotaeq_1 df-clab fiotaeq_0 iiotaeq_0 fiotaeq_2 df-clab 3bitr4g eqrdv eqeq1d abbidv unieqd fiotaeq_0 fiotaeq_1 iiotaeq_0 df-iota fiotaeq_0 fiotaeq_2 iiotaeq_0 df-iota 3eqtr4g $.
$}
$( Equivalence theorem for descriptions.  (Contributed by Andrew Salmon,
       30-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v z $.
	$d ph z $.
	$d ps z $.
	$d x z $.
	iiotabi_0 $f set z $.
	fiotabi_0 $f wff ph $.
	fiotabi_1 $f wff ps $.
	fiotabi_2 $f set x $.
	iotabi $p |- ( A. x ( ph <-> ps ) -> ( iota x ph ) = ( iota x ps ) ) $= fiotabi_0 fiotabi_1 wb fiotabi_2 wal fiotabi_0 fiotabi_2 cab iiotabi_0 sup_set_class csn wceq iiotabi_0 cab cuni fiotabi_1 fiotabi_2 cab iiotabi_0 sup_set_class csn wceq iiotabi_0 cab cuni fiotabi_0 fiotabi_2 cio fiotabi_1 fiotabi_2 cio fiotabi_0 fiotabi_1 wb fiotabi_2 wal fiotabi_0 fiotabi_2 cab iiotabi_0 sup_set_class csn wceq iiotabi_0 cab fiotabi_1 fiotabi_2 cab iiotabi_0 sup_set_class csn wceq iiotabi_0 cab fiotabi_0 fiotabi_1 wb fiotabi_2 wal fiotabi_0 fiotabi_2 cab iiotabi_0 sup_set_class csn wceq fiotabi_1 fiotabi_2 cab iiotabi_0 sup_set_class csn wceq iiotabi_0 fiotabi_0 fiotabi_1 wb fiotabi_2 wal fiotabi_0 fiotabi_2 cab fiotabi_1 fiotabi_2 cab iiotabi_0 sup_set_class csn fiotabi_0 fiotabi_1 wb fiotabi_2 wal fiotabi_0 fiotabi_2 cab fiotabi_1 fiotabi_2 cab wceq fiotabi_0 fiotabi_1 fiotabi_2 abbi biimpi eqeq1d abbidv unieqd fiotabi_0 fiotabi_2 iiotabi_0 df-iota fiotabi_1 fiotabi_2 iiotabi_0 df-iota 3eqtr4g $.
$}
$( Part of Theorem 8.17 in [Quine] p. 56.  This theorem serves as a lemma
       for the fundamental property of iota.  (Contributed by Andrew Salmon,
       11-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	funiabio_0 $f wff ph $.
	funiabio_1 $f set x $.
	funiabio_2 $f set y $.
	uniabio $p |- ( A. x ( ph <-> x = y ) -> U. { x | ph } = y ) $= funiabio_0 funiabio_1 sup_set_class funiabio_2 sup_set_class wceq wb funiabio_1 wal funiabio_0 funiabio_1 cab cuni funiabio_2 sup_set_class csn cuni funiabio_2 sup_set_class funiabio_0 funiabio_1 sup_set_class funiabio_2 sup_set_class wceq wb funiabio_1 wal funiabio_0 funiabio_1 cab funiabio_2 sup_set_class csn funiabio_0 funiabio_1 sup_set_class funiabio_2 sup_set_class wceq wb funiabio_1 wal funiabio_0 funiabio_1 cab funiabio_1 sup_set_class funiabio_2 sup_set_class wceq funiabio_1 cab funiabio_2 sup_set_class csn funiabio_0 funiabio_1 sup_set_class funiabio_2 sup_set_class wceq wb funiabio_1 wal funiabio_0 funiabio_1 cab funiabio_1 sup_set_class funiabio_2 sup_set_class wceq funiabio_1 cab wceq funiabio_0 funiabio_1 sup_set_class funiabio_2 sup_set_class wceq funiabio_1 abbi biimpi funiabio_1 funiabio_2 sup_set_class df-sn syl6eqr unieqd funiabio_2 sup_set_class funiabio_2 vex unisn syl6eq $.
$}
$( Theorem 8.19 in [Quine] p. 57.  This theorem is the fundamental property
       of iota.  (Contributed by Andrew Salmon, 11-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d ph z $.
	$d x y z $.
	iiotaval_0 $f set z $.
	fiotaval_0 $f wff ph $.
	fiotaval_1 $f set x $.
	fiotaval_2 $f set y $.
	iotaval $p |- ( A. x ( ph <-> x = y ) -> ( iota x ph ) = y ) $= fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_1 wal fiotaval_0 fiotaval_1 cio fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal iiotaval_0 cab cuni fiotaval_2 sup_set_class fiotaval_0 fiotaval_1 iiotaval_0 dfiota2 fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_1 wal fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq wb iiotaval_0 wal fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal iiotaval_0 cab cuni fiotaval_2 sup_set_class wceq fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_1 wal fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq wb iiotaval_0 fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_1 wal fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_1 wal fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_2 sup_set_class cvv wcel fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_1 wal fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal wa iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq wi fiotaval_2 vex fiotaval_2 sup_set_class cvv wcel fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_1 wal fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal wa fiotaval_2 sup_set_class iiotaval_0 sup_set_class wceq iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_0 fiotaval_1 fiotaval_2 sup_set_class iiotaval_0 sup_set_class cvv sbeqalb fiotaval_2 iiotaval_0 equcomi syl6 ax-mp ex iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_1 wal fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq wb fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb iiotaval_0 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq fiotaval_0 fiotaval_1 sup_set_class fiotaval_2 sup_set_class wceq fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_2 sup_set_class iiotaval_0 sup_set_class fiotaval_2 iiotaval_0 fiotaval_1 equequ2 eqcoms bibi2d biimpd alimdv com12 impbid alrimiv fiotaval_0 fiotaval_1 sup_set_class iiotaval_0 sup_set_class wceq wb fiotaval_1 wal iiotaval_0 fiotaval_2 uniabio syl syl5eq $.
$}
$( Equivalence between two different forms of ` iota ` .  (Contributed by
       Andrew Salmon, 12-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v z $.
	$d ph z $.
	$d x z $.
	iiotauni_0 $f set z $.
	fiotauni_0 $f wff ph $.
	fiotauni_1 $f set x $.
	iotauni $p |- ( E! x ph -> ( iota x ph ) = U. { x | ph } ) $= fiotauni_0 fiotauni_1 weu fiotauni_0 fiotauni_1 sup_set_class iiotauni_0 sup_set_class wceq wb fiotauni_1 wal iiotauni_0 wex fiotauni_0 fiotauni_1 cio fiotauni_0 fiotauni_1 cab cuni wceq fiotauni_0 fiotauni_1 iiotauni_0 df-eu fiotauni_0 fiotauni_1 sup_set_class iiotauni_0 sup_set_class wceq wb fiotauni_1 wal fiotauni_0 fiotauni_1 cio fiotauni_0 fiotauni_1 cab cuni wceq iiotauni_0 fiotauni_0 fiotauni_1 sup_set_class iiotauni_0 sup_set_class wceq wb fiotauni_1 wal fiotauni_0 fiotauni_1 cio iiotauni_0 sup_set_class fiotauni_0 fiotauni_1 cab cuni fiotauni_0 fiotauni_1 iiotauni_0 iotaval fiotauni_0 fiotauni_1 iiotauni_0 uniabio eqtr4d exlimiv sylbi $.
$}
$( Equivalence between two different forms of ` iota ` .  (Contributed by
       Mario Carneiro, 24-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	fiotaint_0 $f wff ph $.
	fiotaint_1 $f set x $.
	iotaint $p |- ( E! x ph -> ( iota x ph ) = |^| { x | ph } ) $= fiotaint_0 fiotaint_1 weu fiotaint_0 fiotaint_1 cio fiotaint_0 fiotaint_1 cab cuni fiotaint_0 fiotaint_1 cab cint fiotaint_0 fiotaint_1 iotauni fiotaint_0 fiotaint_1 weu fiotaint_0 fiotaint_1 cab cuni fiotaint_0 fiotaint_1 cab cint wceq fiotaint_0 fiotaint_1 uniintab biimpi eqtrd $.
$}
$( Property of iota.  (Contributed by NM, 23-Aug-2011.)  (Revised by Mario
       Carneiro, 23-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v z $.
	$d ph z $.
	$d x z $.
	iiota1_0 $f set z $.
	fiota1_0 $f wff ph $.
	fiota1_1 $f set x $.
	iota1 $p |- ( E! x ph -> ( ph <-> ( iota x ph ) = x ) ) $= fiota1_0 fiota1_1 weu fiota1_0 fiota1_1 sup_set_class iiota1_0 sup_set_class wceq wb fiota1_1 wal iiota1_0 wex fiota1_0 fiota1_0 fiota1_1 cio fiota1_1 sup_set_class wceq wb fiota1_0 fiota1_1 iiota1_0 df-eu fiota1_0 fiota1_1 sup_set_class iiota1_0 sup_set_class wceq wb fiota1_1 wal fiota1_0 fiota1_0 fiota1_1 cio fiota1_1 sup_set_class wceq wb iiota1_0 fiota1_0 fiota1_1 sup_set_class iiota1_0 sup_set_class wceq wb fiota1_1 wal fiota1_0 fiota1_1 sup_set_class fiota1_0 fiota1_1 cio wceq fiota1_0 fiota1_1 cio fiota1_1 sup_set_class wceq fiota1_0 fiota1_1 sup_set_class iiota1_0 sup_set_class wceq wb fiota1_1 wal fiota1_0 fiota1_1 sup_set_class iiota1_0 sup_set_class wceq fiota1_1 sup_set_class fiota1_0 fiota1_1 cio wceq fiota1_0 fiota1_1 sup_set_class iiota1_0 sup_set_class wceq wb fiota1_1 sp fiota1_0 fiota1_1 sup_set_class iiota1_0 sup_set_class wceq wb fiota1_1 wal fiota1_0 fiota1_1 cio iiota1_0 sup_set_class fiota1_1 sup_set_class fiota1_0 fiota1_1 iiota1_0 iotaval eqeq2d bitr4d fiota1_1 sup_set_class fiota1_0 fiota1_1 cio eqcom syl6bb exlimiv sylbi $.
$}
$( Theorem 8.22 in [Quine] p. 57.  This theorem is the result if there
       isn't exactly one ` x ` that satisfies ` ph ` .  (Contributed by Andrew
       Salmon, 11-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v z $.
	$d ph z $.
	$d x z $.
	iiotanul_0 $f set z $.
	fiotanul_0 $f wff ph $.
	fiotanul_1 $f set x $.
	iotanul $p |- ( -. E! x ph -> ( iota x ph ) = (/) ) $= fiotanul_0 fiotanul_1 weu fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 wex fiotanul_0 fiotanul_1 cio c0 wceq fiotanul_0 fiotanul_1 iiotanul_0 df-eu fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 wex wn fiotanul_0 fiotanul_1 cio fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 cab cuni c0 fiotanul_0 fiotanul_1 iiotanul_0 dfiota2 fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 wex wn fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 cab cuni c0 cuni c0 fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 wex wn fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 cab c0 fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 wex wn fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn iiotanul_0 wal fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 cab c0 wceq fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 alnex fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn iiotanul_0 wal fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 cab iiotanul_0 sup_set_class iiotanul_0 sup_set_class wceq wn iiotanul_0 cab c0 fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn iiotanul_0 wal fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 sup_set_class iiotanul_0 sup_set_class wceq wn wb iiotanul_0 wal fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 cab iiotanul_0 sup_set_class iiotanul_0 sup_set_class wceq wn iiotanul_0 cab wceq fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 sup_set_class iiotanul_0 sup_set_class wceq wn wb iiotanul_0 fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn iiotanul_0 sup_set_class iiotanul_0 sup_set_class wceq fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn iiotanul_0 sup_set_class iiotanul_0 sup_set_class wceq fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn iiotanul_0 sup_set_class iiotanul_0 sup_set_class wceq ax-1 fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal wn iiotanul_0 sup_set_class eqidd impbid1 con2bid alimi fiotanul_0 fiotanul_1 sup_set_class iiotanul_0 sup_set_class wceq wb fiotanul_1 wal iiotanul_0 sup_set_class iiotanul_0 sup_set_class wceq wn iiotanul_0 abbi sylib iiotanul_0 dfnul2 syl6eqr sylbir unieqd uni0 syl6eq syl5eq sylnbi $.
$}
$( The ` iota ` class is a subset of the union of all elements satisfying
       ` ph ` .  (Contributed by Mario Carneiro, 24-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	fiotassuni_0 $f wff ph $.
	fiotassuni_1 $f set x $.
	iotassuni $p |- ( iota x ph ) C_ U. { x | ph } $= fiotassuni_0 fiotassuni_1 weu fiotassuni_0 fiotassuni_1 cio fiotassuni_0 fiotassuni_1 cab cuni wss fiotassuni_0 fiotassuni_1 weu fiotassuni_0 fiotassuni_1 cio fiotassuni_0 fiotassuni_1 cab cuni wceq fiotassuni_0 fiotassuni_1 cio fiotassuni_0 fiotassuni_1 cab cuni wss fiotassuni_0 fiotassuni_1 iotauni fiotassuni_0 fiotassuni_1 cio fiotassuni_0 fiotassuni_1 cab cuni eqimss syl fiotassuni_0 fiotassuni_1 weu wn fiotassuni_0 fiotassuni_1 cio fiotassuni_0 fiotassuni_1 cab cuni wss c0 fiotassuni_0 fiotassuni_1 cab cuni wss fiotassuni_0 fiotassuni_1 cab cuni 0ss fiotassuni_0 fiotassuni_1 weu wn fiotassuni_0 fiotassuni_1 cio c0 fiotassuni_0 fiotassuni_1 cab cuni fiotassuni_0 fiotassuni_1 iotanul sseq1d mpbiri pm2.61i $.
$}
$( Theorem 8.23 in [Quine] p. 58.  This theorem proves the existence of the
       ` iota ` class under our definition.  (Contributed by Andrew Salmon,
       11-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v z $.
	$d ph z $.
	$d x z $.
	iiotaex_0 $f set z $.
	fiotaex_0 $f wff ph $.
	fiotaex_1 $f set x $.
	iotaex $p |- ( iota x ph ) e. _V $= fiotaex_0 fiotaex_1 weu fiotaex_0 fiotaex_1 cio cvv wcel fiotaex_0 fiotaex_1 sup_set_class iiotaex_0 sup_set_class wceq wb fiotaex_1 wal iiotaex_0 wex iiotaex_0 sup_set_class fiotaex_0 fiotaex_1 cio wceq iiotaex_0 wex fiotaex_0 fiotaex_1 weu fiotaex_0 fiotaex_1 cio cvv wcel fiotaex_0 fiotaex_1 sup_set_class iiotaex_0 sup_set_class wceq wb fiotaex_1 wal iiotaex_0 sup_set_class fiotaex_0 fiotaex_1 cio wceq iiotaex_0 fiotaex_0 fiotaex_1 sup_set_class iiotaex_0 sup_set_class wceq wb fiotaex_1 wal fiotaex_0 fiotaex_1 cio iiotaex_0 sup_set_class fiotaex_0 fiotaex_1 iiotaex_0 iotaval eqcomd eximi fiotaex_0 fiotaex_1 iiotaex_0 df-eu iiotaex_0 fiotaex_0 fiotaex_1 cio isset 3imtr4i fiotaex_0 fiotaex_1 weu wn fiotaex_0 fiotaex_1 cio c0 cvv fiotaex_0 fiotaex_1 iotanul 0ex syl6eqel pm2.61i $.
$}
$( Theorem *14.22 in [WhiteheadRussell] p. 190.  (Contributed by Andrew
       Salmon, 12-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v z $.
	$d ph z $.
	$d x z $.
	iiota4_0 $f set z $.
	fiota4_0 $f wff ph $.
	fiota4_1 $f set x $.
	iota4 $p |- ( E! x ph -> [. ( iota x ph ) / x ]. ph ) $= fiota4_0 fiota4_1 weu fiota4_0 fiota4_1 sup_set_class iiota4_0 sup_set_class wceq wb fiota4_1 wal iiota4_0 wex fiota4_0 fiota4_1 fiota4_0 fiota4_1 cio wsbc fiota4_0 fiota4_1 iiota4_0 df-eu fiota4_0 fiota4_1 sup_set_class iiota4_0 sup_set_class wceq wb fiota4_1 wal fiota4_0 fiota4_1 fiota4_0 fiota4_1 cio wsbc iiota4_0 fiota4_0 fiota4_1 sup_set_class iiota4_0 sup_set_class wceq wb fiota4_1 wal fiota4_0 fiota4_1 iiota4_0 wsb fiota4_0 fiota4_1 fiota4_0 fiota4_1 cio wsbc fiota4_0 fiota4_1 sup_set_class iiota4_0 sup_set_class wceq wb fiota4_1 wal fiota4_1 sup_set_class iiota4_0 sup_set_class wceq fiota4_0 wi fiota4_1 wal fiota4_0 fiota4_1 iiota4_0 wsb fiota4_0 fiota4_1 sup_set_class iiota4_0 sup_set_class wceq wb fiota4_1 sup_set_class iiota4_0 sup_set_class wceq fiota4_0 wi fiota4_1 fiota4_0 fiota4_1 sup_set_class iiota4_0 sup_set_class wceq bi2 alimi fiota4_0 fiota4_1 iiota4_0 sb2 syl fiota4_0 fiota4_1 sup_set_class iiota4_0 sup_set_class wceq wb fiota4_1 wal iiota4_0 sup_set_class fiota4_0 fiota4_1 cio wceq fiota4_0 fiota4_1 iiota4_0 wsb fiota4_0 fiota4_1 fiota4_0 fiota4_1 cio wsbc wb fiota4_0 fiota4_1 sup_set_class iiota4_0 sup_set_class wceq wb fiota4_1 wal fiota4_0 fiota4_1 cio iiota4_0 sup_set_class fiota4_0 fiota4_1 iiota4_0 iotaval eqcomd fiota4_0 fiota4_1 iiota4_0 fiota4_0 fiota4_1 cio dfsbcq2 syl mpbid exlimiv sylbi $.
$}
$( Theorem *14.23 in [WhiteheadRussell] p. 191.  (Contributed by Andrew
     Salmon, 12-Jul-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fiota4an_0 $f wff ph $.
	fiota4an_1 $f wff ps $.
	fiota4an_2 $f set x $.
	iota4an $p |- ( E! x ( ph /\ ps ) -> [. ( iota x ( ph /\ ps ) ) / x ]. ph ) $= fiota4an_0 fiota4an_1 wa fiota4an_2 weu fiota4an_0 fiota4an_1 wa fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc fiota4an_0 fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc fiota4an_0 fiota4an_1 wa fiota4an_2 iota4 fiota4an_0 fiota4an_1 wa fiota4an_0 wi fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc fiota4an_0 fiota4an_1 wa fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc fiota4an_0 fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc wi fiota4an_0 fiota4an_1 wa fiota4an_2 cio cvv wcel fiota4an_0 fiota4an_1 wa fiota4an_0 wi fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc fiota4an_0 fiota4an_1 wa fiota4an_2 iotaex fiota4an_0 fiota4an_1 wa fiota4an_0 wi fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio cvv fiota4an_0 fiota4an_1 simpl sbcth ax-mp fiota4an_0 fiota4an_1 wa fiota4an_2 cio cvv wcel fiota4an_0 fiota4an_1 wa fiota4an_0 wi fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc fiota4an_0 fiota4an_1 wa fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc fiota4an_0 fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio wsbc wi wb fiota4an_0 fiota4an_1 wa fiota4an_2 iotaex fiota4an_0 fiota4an_1 wa fiota4an_0 fiota4an_2 fiota4an_0 fiota4an_1 wa fiota4an_2 cio cvv sbcimg ax-mp mpbi syl $.
$}
$( A method for computing iota.  (Contributed by NM, 17-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v V $.
	$v y $.
	$d x y A $.
	$d x V $.
	$d x ph $.
	$d y ps $.
	iiota5_0 $f set y $.
	fiota5_0 $f wff ph $.
	fiota5_1 $f wff ps $.
	fiota5_2 $f set x $.
	fiota5_3 $f class A $.
	fiota5_4 $f class V $.
	eiota5_0 $e |- ( ( ph /\ A e. V ) -> ( ps <-> x = A ) ) $.
	iota5 $p |- ( ( ph /\ A e. V ) -> ( iota x ps ) = A ) $= fiota5_0 fiota5_3 fiota5_4 wcel wa fiota5_1 fiota5_2 sup_set_class fiota5_3 wceq wb fiota5_2 wal fiota5_1 fiota5_2 cio fiota5_3 wceq fiota5_0 fiota5_3 fiota5_4 wcel wa fiota5_1 fiota5_2 sup_set_class fiota5_3 wceq wb fiota5_2 eiota5_0 alrimiv fiota5_3 fiota5_4 wcel fiota5_1 fiota5_2 sup_set_class fiota5_3 wceq wb fiota5_2 wal fiota5_1 fiota5_2 cio fiota5_3 wceq wi fiota5_0 fiota5_1 fiota5_2 sup_set_class iiota5_0 sup_set_class wceq wb fiota5_2 wal fiota5_1 fiota5_2 cio iiota5_0 sup_set_class wceq wi fiota5_1 fiota5_2 sup_set_class fiota5_3 wceq wb fiota5_2 wal fiota5_1 fiota5_2 cio fiota5_3 wceq wi iiota5_0 fiota5_3 fiota5_4 iiota5_0 sup_set_class fiota5_3 wceq fiota5_1 fiota5_2 sup_set_class iiota5_0 sup_set_class wceq wb fiota5_2 wal fiota5_1 fiota5_2 sup_set_class fiota5_3 wceq wb fiota5_2 wal fiota5_1 fiota5_2 cio iiota5_0 sup_set_class wceq fiota5_1 fiota5_2 cio fiota5_3 wceq iiota5_0 sup_set_class fiota5_3 wceq fiota5_1 fiota5_2 sup_set_class iiota5_0 sup_set_class wceq wb fiota5_1 fiota5_2 sup_set_class fiota5_3 wceq wb fiota5_2 iiota5_0 sup_set_class fiota5_3 wceq fiota5_2 sup_set_class iiota5_0 sup_set_class wceq fiota5_2 sup_set_class fiota5_3 wceq fiota5_1 iiota5_0 sup_set_class fiota5_3 fiota5_2 sup_set_class eqeq2 bibi2d albidv iiota5_0 sup_set_class fiota5_3 fiota5_1 fiota5_2 cio eqeq2 imbi12d fiota5_1 fiota5_2 iiota5_0 iotaval vtoclg adantl mpd $.
$}
$( Formula-building deduction rule for iota.  (Contributed by NM,
       20-Aug-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$d x ph $.
	fiotabidv_0 $f wff ph $.
	fiotabidv_1 $f wff ps $.
	fiotabidv_2 $f wff ch $.
	fiotabidv_3 $f set x $.
	eiotabidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	iotabidv $p |- ( ph -> ( iota x ps ) = ( iota x ch ) ) $= fiotabidv_0 fiotabidv_1 fiotabidv_2 wb fiotabidv_3 wal fiotabidv_1 fiotabidv_3 cio fiotabidv_2 fiotabidv_3 cio wceq fiotabidv_0 fiotabidv_1 fiotabidv_2 wb fiotabidv_3 eiotabidv_0 alrimiv fiotabidv_1 fiotabidv_2 fiotabidv_3 iotabi syl $.
$}
$( Formula-building deduction rule for iota.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fiotabii_0 $f wff ph $.
	fiotabii_1 $f wff ps $.
	fiotabii_2 $f set x $.
	eiotabii_0 $e |- ( ph <-> ps ) $.
	iotabii $p |- ( iota x ph ) = ( iota x ps ) $= fiotabii_0 fiotabii_1 wb fiotabii_0 fiotabii_2 cio fiotabii_1 fiotabii_2 cio wceq fiotabii_2 fiotabii_0 fiotabii_1 fiotabii_2 iotabi eiotabii_0 mpg $.
$}
$( Membership law for descriptions.

     This can useful for expanding an unbounded iota-based definition (see
     ~ df-iota ).  If you have a bounded iota-based definition, ~ riotacl2 may
     be useful.

     (Contributed by Andrew Salmon, 1-Aug-2011.) $)
${
	$v ph $.
	$v x $.
	fiotacl_0 $f wff ph $.
	fiotacl_1 $f set x $.
	iotacl $p |- ( E! x ph -> ( iota x ph ) e. { x | ph } ) $= fiotacl_0 fiotacl_1 weu fiotacl_0 fiotacl_1 fiotacl_0 fiotacl_1 cio wsbc fiotacl_0 fiotacl_1 cio fiotacl_0 fiotacl_1 cab wcel fiotacl_0 fiotacl_1 iota4 fiotacl_0 fiotacl_1 fiotacl_0 fiotacl_1 cio df-sbc sylib $.
$}
$( A condition that allows us to represent "the unique element such that
         ` ph ` " with a class expression ` A ` .  (Contributed by NM,
         30-Dec-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v B $.
	$v V $.
	fiota2df_0 $f wff ph $.
	fiota2df_1 $f wff ps $.
	fiota2df_2 $f wff ch $.
	fiota2df_3 $f set x $.
	fiota2df_4 $f class B $.
	fiota2df_5 $f class V $.
	eiota2df_0 $e |- ( ph -> B e. V ) $.
	eiota2df_1 $e |- ( ph -> E! x ps ) $.
	eiota2df_2 $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
	eiota2df_3 $e |- F/ x ph $.
	eiota2df_4 $e |- ( ph -> F/ x ch ) $.
	eiota2df_5 $e |- ( ph -> F/_ x B ) $.
	iota2df $p |- ( ph -> ( ch <-> ( iota x ps ) = B ) ) $= fiota2df_0 fiota2df_3 fiota2df_4 wnfc fiota2df_2 fiota2df_1 fiota2df_3 cio fiota2df_4 wceq wb fiota2df_3 wnf fiota2df_3 sup_set_class fiota2df_4 wceq fiota2df_1 fiota2df_1 fiota2df_3 cio fiota2df_3 sup_set_class wceq wb fiota2df_2 fiota2df_1 fiota2df_3 cio fiota2df_4 wceq wb wb wi fiota2df_3 wal fiota2df_1 fiota2df_1 fiota2df_3 cio fiota2df_3 sup_set_class wceq wb fiota2df_3 wal fiota2df_4 fiota2df_5 wcel fiota2df_2 fiota2df_1 fiota2df_3 cio fiota2df_4 wceq wb eiota2df_5 fiota2df_0 fiota2df_2 fiota2df_1 fiota2df_3 cio fiota2df_4 wceq fiota2df_3 eiota2df_4 fiota2df_0 fiota2df_3 fiota2df_1 fiota2df_3 cio fiota2df_4 fiota2df_3 fiota2df_1 fiota2df_3 cio wnfc fiota2df_0 fiota2df_1 fiota2df_3 nfiota1 a1i eiota2df_5 nfeqd nfbid fiota2df_0 fiota2df_3 sup_set_class fiota2df_4 wceq fiota2df_1 fiota2df_1 fiota2df_3 cio fiota2df_3 sup_set_class wceq wb fiota2df_2 fiota2df_1 fiota2df_3 cio fiota2df_4 wceq wb wb wi fiota2df_3 eiota2df_3 fiota2df_0 fiota2df_3 sup_set_class fiota2df_4 wceq fiota2df_1 fiota2df_1 fiota2df_3 cio fiota2df_3 sup_set_class wceq wb fiota2df_2 fiota2df_1 fiota2df_3 cio fiota2df_4 wceq wb wb fiota2df_0 fiota2df_3 sup_set_class fiota2df_4 wceq wa fiota2df_1 fiota2df_2 fiota2df_1 fiota2df_3 cio fiota2df_3 sup_set_class wceq fiota2df_1 fiota2df_3 cio fiota2df_4 wceq eiota2df_2 fiota2df_0 fiota2df_3 sup_set_class fiota2df_4 wceq wa fiota2df_3 sup_set_class fiota2df_4 fiota2df_1 fiota2df_3 cio fiota2df_0 fiota2df_3 sup_set_class fiota2df_4 wceq simpr eqeq2d bibi12d ex alrimi fiota2df_0 fiota2df_1 fiota2df_1 fiota2df_3 cio fiota2df_3 sup_set_class wceq wb fiota2df_3 eiota2df_3 fiota2df_0 fiota2df_1 fiota2df_3 weu fiota2df_1 fiota2df_1 fiota2df_3 cio fiota2df_3 sup_set_class wceq wb eiota2df_1 fiota2df_1 fiota2df_3 iota1 syl alrimi eiota2df_0 fiota2df_1 fiota2df_1 fiota2df_3 cio fiota2df_3 sup_set_class wceq wb fiota2df_2 fiota2df_1 fiota2df_3 cio fiota2df_4 wceq wb fiota2df_3 fiota2df_4 fiota2df_5 vtoclgft syl221anc $.
$}
$( A condition that allows us to represent "the unique element such that
       ` ph ` " with a class expression ` A ` .  (Contributed by NM,
       30-Dec-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v B $.
	$v V $.
	$d x B $.
	$d x ph $.
	$d x ch $.
	fiota2d_0 $f wff ph $.
	fiota2d_1 $f wff ps $.
	fiota2d_2 $f wff ch $.
	fiota2d_3 $f set x $.
	fiota2d_4 $f class B $.
	fiota2d_5 $f class V $.
	eiota2d_0 $e |- ( ph -> B e. V ) $.
	eiota2d_1 $e |- ( ph -> E! x ps ) $.
	eiota2d_2 $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
	iota2d $p |- ( ph -> ( ch <-> ( iota x ps ) = B ) ) $= fiota2d_0 fiota2d_1 fiota2d_2 fiota2d_3 fiota2d_4 fiota2d_5 eiota2d_0 eiota2d_1 eiota2d_2 fiota2d_0 fiota2d_3 nfv fiota2d_0 fiota2d_2 fiota2d_3 nfvd fiota2d_0 fiota2d_3 fiota2d_4 nfcvd iota2df $.
$}
$( The unique element such that ` ph ` .  (Contributed by Jeff Madsen,
       1-Jun-2011.)  (Revised by Mario Carneiro, 23-Dec-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d A x $.
	$d ps x $.
	fiota2_0 $f wff ph $.
	fiota2_1 $f wff ps $.
	fiota2_2 $f set x $.
	fiota2_3 $f class A $.
	fiota2_4 $f class B $.
	eiota2_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	iota2 $p |- ( ( A e. B /\ E! x ph ) -> ( ps <-> ( iota x ph ) = A ) ) $= fiota2_3 fiota2_4 wcel fiota2_3 cvv wcel fiota2_0 fiota2_2 weu fiota2_1 fiota2_0 fiota2_2 cio fiota2_3 wceq wb fiota2_3 fiota2_4 elex fiota2_3 cvv wcel fiota2_0 fiota2_2 weu wa fiota2_0 fiota2_1 fiota2_2 fiota2_3 cvv fiota2_3 cvv wcel fiota2_0 fiota2_2 weu simpl fiota2_3 cvv wcel fiota2_0 fiota2_2 weu simpr fiota2_2 sup_set_class fiota2_3 wceq fiota2_0 fiota2_1 wb fiota2_3 cvv wcel fiota2_0 fiota2_2 weu wa eiota2_0 adantl fiota2_3 cvv wcel fiota2_0 fiota2_2 weu fiota2_2 fiota2_3 cvv wcel fiota2_2 nfv fiota2_0 fiota2_2 nfeu1 nfan fiota2_3 cvv wcel fiota2_0 fiota2_2 weu wa fiota2_1 fiota2_2 nfvd fiota2_3 cvv wcel fiota2_0 fiota2_2 weu wa fiota2_2 fiota2_3 nfcvd iota2df sylan $.
$}
$( A class abstraction with a unique member can be expressed as a singleton.
     (Contributed by Mario Carneiro, 23-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	fsniota_0 $f wff ph $.
	fsniota_1 $f set x $.
	sniota $p |- ( E! x ph -> { x | ph } = { ( iota x ph ) } ) $= fsniota_0 fsniota_1 weu fsniota_1 sup_set_class fsniota_0 fsniota_1 cab wcel fsniota_1 sup_set_class fsniota_0 fsniota_1 cio csn wcel wb fsniota_1 wal fsniota_0 fsniota_1 cab fsniota_0 fsniota_1 cio csn wceq fsniota_0 fsniota_1 weu fsniota_1 sup_set_class fsniota_0 fsniota_1 cab wcel fsniota_1 sup_set_class fsniota_0 fsniota_1 cio csn wcel wb fsniota_1 fsniota_0 fsniota_1 nfeu1 fsniota_0 fsniota_1 weu fsniota_0 fsniota_1 sup_set_class fsniota_0 fsniota_1 cio wceq fsniota_1 sup_set_class fsniota_0 fsniota_1 cab wcel fsniota_1 sup_set_class fsniota_0 fsniota_1 cio csn wcel fsniota_0 fsniota_1 weu fsniota_0 fsniota_0 fsniota_1 cio fsniota_1 sup_set_class wceq fsniota_1 sup_set_class fsniota_0 fsniota_1 cio wceq fsniota_0 fsniota_1 iota1 fsniota_0 fsniota_1 cio fsniota_1 sup_set_class eqcom syl6bb fsniota_0 fsniota_1 abid fsniota_1 sup_set_class fsniota_0 fsniota_1 cio fsniota_1 vex elsnc 3bitr4g alrimi fsniota_1 fsniota_0 fsniota_1 cab fsniota_0 fsniota_1 cio csn fsniota_0 fsniota_1 nfab1 fsniota_1 fsniota_0 fsniota_1 cio fsniota_0 fsniota_1 nfiota1 nfsn cleqf sylibr $.
$}
$( The ` iota ` operation using the ` if ` operator.  (Contributed by Scott
       Fenton, 6-Oct-2017.) $)
${
	$v ph $.
	$v x $.
	fdfiota4_0 $f wff ph $.
	fdfiota4_1 $f set x $.
	dfiota4 $p |- ( iota x ph ) = if ( E! x ph , U. { x | ph } , (/) ) $= fdfiota4_0 fdfiota4_1 weu fdfiota4_0 fdfiota4_1 cio fdfiota4_0 fdfiota4_1 weu fdfiota4_0 fdfiota4_1 cab cuni c0 cif wceq fdfiota4_0 fdfiota4_1 weu fdfiota4_0 fdfiota4_1 cio fdfiota4_0 fdfiota4_1 cab cuni fdfiota4_0 fdfiota4_1 weu fdfiota4_0 fdfiota4_1 cab cuni c0 cif fdfiota4_0 fdfiota4_1 iotauni fdfiota4_0 fdfiota4_1 weu fdfiota4_0 fdfiota4_1 cab cuni c0 iftrue eqtr4d fdfiota4_0 fdfiota4_1 weu wn fdfiota4_0 fdfiota4_1 cio c0 fdfiota4_0 fdfiota4_1 weu fdfiota4_0 fdfiota4_1 cab cuni c0 cif fdfiota4_0 fdfiota4_1 iotanul fdfiota4_0 fdfiota4_1 weu fdfiota4_0 fdfiota4_1 cab cuni c0 iffalse eqtr4d pm2.61i $.
$}
$( Class substitution within a description binder.  (Contributed by Scott
       Fenton, 6-Oct-2017.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v V $.
	$v z $.
	$d A y z $.
	$d x y z $.
	$d ph z $.
	icsbiotag_0 $f set z $.
	fcsbiotag_0 $f wff ph $.
	fcsbiotag_1 $f set x $.
	fcsbiotag_2 $f set y $.
	fcsbiotag_3 $f class A $.
	fcsbiotag_4 $f class V $.
	csbiotag $p |- ( A e. V -> [_ A / x ]_ ( iota y ph ) = ( iota y [. A / x ]. ph ) ) $= fcsbiotag_1 icsbiotag_0 sup_set_class fcsbiotag_0 fcsbiotag_2 cio csb fcsbiotag_0 fcsbiotag_1 icsbiotag_0 wsb fcsbiotag_2 cio wceq fcsbiotag_1 fcsbiotag_3 fcsbiotag_0 fcsbiotag_2 cio csb fcsbiotag_0 fcsbiotag_1 fcsbiotag_3 wsbc fcsbiotag_2 cio wceq icsbiotag_0 fcsbiotag_3 fcsbiotag_4 icsbiotag_0 sup_set_class fcsbiotag_3 wceq fcsbiotag_1 icsbiotag_0 sup_set_class fcsbiotag_0 fcsbiotag_2 cio csb fcsbiotag_1 fcsbiotag_3 fcsbiotag_0 fcsbiotag_2 cio csb fcsbiotag_0 fcsbiotag_1 icsbiotag_0 wsb fcsbiotag_2 cio fcsbiotag_0 fcsbiotag_1 fcsbiotag_3 wsbc fcsbiotag_2 cio fcsbiotag_1 icsbiotag_0 sup_set_class fcsbiotag_3 fcsbiotag_0 fcsbiotag_2 cio csbeq1 icsbiotag_0 sup_set_class fcsbiotag_3 wceq fcsbiotag_0 fcsbiotag_1 icsbiotag_0 wsb fcsbiotag_0 fcsbiotag_1 fcsbiotag_3 wsbc fcsbiotag_2 fcsbiotag_0 fcsbiotag_1 icsbiotag_0 fcsbiotag_3 dfsbcq2 iotabidv eqeq12d fcsbiotag_1 icsbiotag_0 sup_set_class fcsbiotag_0 fcsbiotag_2 cio fcsbiotag_0 fcsbiotag_1 icsbiotag_0 wsb fcsbiotag_2 cio icsbiotag_0 vex fcsbiotag_0 fcsbiotag_1 icsbiotag_0 wsb fcsbiotag_1 fcsbiotag_2 fcsbiotag_0 fcsbiotag_1 icsbiotag_0 nfs1v nfiota fcsbiotag_1 sup_set_class icsbiotag_0 sup_set_class wceq fcsbiotag_0 fcsbiotag_0 fcsbiotag_1 icsbiotag_0 wsb fcsbiotag_2 fcsbiotag_0 fcsbiotag_1 icsbiotag_0 sbequ12 iotabidv csbief vtoclg $.
$}

