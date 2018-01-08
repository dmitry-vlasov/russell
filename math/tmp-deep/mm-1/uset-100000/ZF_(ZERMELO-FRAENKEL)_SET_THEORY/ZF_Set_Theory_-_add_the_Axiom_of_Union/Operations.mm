$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Functions.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Operations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Extend class notation to include the value of an operation ` F ` (such as
     ` + ` ) for two arguments ` A ` and ` B ` .  Note that the syntax is
     simply three class symbols in a row surrounded by parentheses.  Since
     operation values are the only possible class expressions consisting of
     three class expressions in a row surrounded by parentheses, the syntax is
     unambiguous.  (For an example of how syntax could become ambiguous if we
     are not careful, see the comment in ~ cneg .) */

$)
${
	fco_0 $f class A $.
	fco_1 $f class B $.
	fco_2 $f class F $.
	co $a class ( A F B ) $.
$}
$( /* Extend class notation to include class abstraction (class builder) of
     nested ordered pairs. */

$)
${
	fcoprab_0 $f wff ph $.
	fcoprab_1 $f set x $.
	fcoprab_2 $f set y $.
	fcoprab_3 $f set z $.
	coprab $a class { <. <. x , y >. , z >. | ph } $.
$}
$( /* Extend the definition of a class to include maps-to notation for defining
     an operation via a rule. */

$)
${
	fcmpt2_0 $f set x $.
	fcmpt2_1 $f set y $.
	fcmpt2_2 $f class A $.
	fcmpt2_3 $f class B $.
	fcmpt2_4 $f class C $.
	cmpt2 $a class ( x e. A , y e. B |-> C ) $.
$}
$( /* Define the value of an operation.  Definition of operation value in
     [Enderton] p. 79.  Note that the syntax is simply three class expressions
     in a row bracketed by parentheses.  There are no restrictions of any kind
     on what those class expressions may be, although only certain kinds of
     class expressions - a binary operation ` F ` and its arguments ` A ` and
     ` B ` - will be useful for proving meaningful theorems.  For example, if
     class ` F ` is the operation ` + ` and arguments ` A ` and ` B ` are ` 3 `
     and ` 2 ` , the expression ` ( 3 + 2 ) ` can be proved to equal ` 5 ` (see
     ~ 3p2e5 ).  This definition is well-defined, although not very meaningful,
     when classes ` A ` and/or ` B ` are proper classes (i.e. are not sets);
     see ~ ovprc1 and ~ ovprc2 .  On the other hand, we often find uses for
     this definition when ` F ` is a proper class, such as ` +o ` in ~ oav .
     ` F ` is normally equal to a class of nested ordered pairs of the form
     defined by ~ df-oprab .  (Contributed by NM, 28-Feb-1995.) */

$)
${
	fdf-ov_0 $f class A $.
	fdf-ov_1 $f class B $.
	fdf-ov_2 $f class F $.
	df-ov $a |- ( A F B ) = ( F ` <. A , B >. ) $.
$}
$( /* Define the class abstraction (class builder) of a collection of nested
       ordered pairs (for use in defining operations).  This is a special case
       of Definition 4.16 of [TakeutiZaring] p. 14.  Normally ` x ` , ` y ` ,
       and ` z ` are distinct, although the definition doesn't strictly require
       it.  See ~ df-ov for the value of an operation.  The brace notation is
       called "class abstraction" by Quine; it is also called a "class builder"
       in the literature.  The value of the most common operation class builder
       is given by ~ ovmpt2 .  (Contributed by NM, 12-Mar-1995.) */

$)
${
	$d x w $.
	$d y w $.
	$d z w $.
	$d w ph $.
	fdf-oprab_0 $f wff ph $.
	fdf-oprab_1 $f set x $.
	fdf-oprab_2 $f set y $.
	fdf-oprab_3 $f set z $.
	fdf-oprab_4 $f set w $.
	df-oprab $a |- { <. <. x , y >. , z >. | ph } = { w | E. x E. y E. z ( w = <. <. x , y >. , z >. /\ ph ) } $.
$}
$( /* Define maps-to notation for defining an operation via a rule.  Read as
       "the operation defined by the map from ` x , y ` (in ` A X. B ` ) to
       ` B ( x , y ) ` ."  An extension of ~ df-mpt for two arguments.
       (Contributed by NM, 17-Feb-2008.) */

$)
${
	$d x z $.
	$d y z $.
	$d z A $.
	$d z B $.
	$d z C $.
	fdf-mpt2_0 $f set x $.
	fdf-mpt2_1 $f set y $.
	fdf-mpt2_2 $f set z $.
	fdf-mpt2_3 $f class A $.
	fdf-mpt2_4 $f class B $.
	fdf-mpt2_5 $f class C $.
	df-mpt2 $a |- ( x e. A , y e. B |-> C ) = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ z = C ) } $.
$}
$( /* Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) */

$)
${
	foveq_0 $f class A $.
	foveq_1 $f class B $.
	foveq_2 $f class F $.
	foveq_3 $f class G $.
	oveq $p |- ( F = G -> ( A F B ) = ( A G B ) ) $= foveq_2 foveq_3 wceq foveq_0 foveq_1 cop foveq_2 cfv foveq_0 foveq_1 cop foveq_3 cfv foveq_0 foveq_1 foveq_2 co foveq_0 foveq_1 foveq_3 co foveq_0 foveq_1 cop foveq_2 foveq_3 fveq1 foveq_0 foveq_1 foveq_2 df-ov foveq_0 foveq_1 foveq_3 df-ov 3eqtr4g $.
$}
$( /* Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) */

$)
${
	foveq1_0 $f class A $.
	foveq1_1 $f class B $.
	foveq1_2 $f class C $.
	foveq1_3 $f class F $.
	oveq1 $p |- ( A = B -> ( A F C ) = ( B F C ) ) $= foveq1_0 foveq1_1 wceq foveq1_0 foveq1_2 cop foveq1_3 cfv foveq1_1 foveq1_2 cop foveq1_3 cfv foveq1_0 foveq1_2 foveq1_3 co foveq1_1 foveq1_2 foveq1_3 co foveq1_0 foveq1_1 wceq foveq1_0 foveq1_2 cop foveq1_1 foveq1_2 cop foveq1_3 foveq1_0 foveq1_1 foveq1_2 opeq1 fveq2d foveq1_0 foveq1_2 foveq1_3 df-ov foveq1_1 foveq1_2 foveq1_3 df-ov 3eqtr4g $.
$}
$( /* Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) */

$)
${
	foveq2_0 $f class A $.
	foveq2_1 $f class B $.
	foveq2_2 $f class C $.
	foveq2_3 $f class F $.
	oveq2 $p |- ( A = B -> ( C F A ) = ( C F B ) ) $= foveq2_0 foveq2_1 wceq foveq2_2 foveq2_0 cop foveq2_3 cfv foveq2_2 foveq2_1 cop foveq2_3 cfv foveq2_2 foveq2_0 foveq2_3 co foveq2_2 foveq2_1 foveq2_3 co foveq2_0 foveq2_1 wceq foveq2_2 foveq2_0 cop foveq2_2 foveq2_1 cop foveq2_3 foveq2_0 foveq2_1 foveq2_2 opeq2 fveq2d foveq2_2 foveq2_0 foveq2_3 df-ov foveq2_2 foveq2_1 foveq2_3 df-ov 3eqtr4g $.
$}
$( /* Equality theorem for operation value.  (Contributed by NM,
     16-Jul-1995.) */

$)
${
	foveq12_0 $f class A $.
	foveq12_1 $f class B $.
	foveq12_2 $f class C $.
	foveq12_3 $f class D $.
	foveq12_4 $f class F $.
	oveq12 $p |- ( ( A = B /\ C = D ) -> ( A F C ) = ( B F D ) ) $= foveq12_0 foveq12_1 wceq foveq12_2 foveq12_3 wceq foveq12_0 foveq12_2 foveq12_4 co foveq12_1 foveq12_2 foveq12_4 co foveq12_1 foveq12_3 foveq12_4 co foveq12_0 foveq12_1 foveq12_2 foveq12_4 oveq1 foveq12_2 foveq12_3 foveq12_1 foveq12_4 oveq2 sylan9eq $.
$}
$( /* Equality inference for operation value.  (Contributed by NM,
       28-Feb-1995.) */

$)
${
	foveq1i_0 $f class A $.
	foveq1i_1 $f class B $.
	foveq1i_2 $f class C $.
	foveq1i_3 $f class F $.
	eoveq1i_0 $e |- A = B $.
	oveq1i $p |- ( A F C ) = ( B F C ) $= foveq1i_0 foveq1i_1 wceq foveq1i_0 foveq1i_2 foveq1i_3 co foveq1i_1 foveq1i_2 foveq1i_3 co wceq eoveq1i_0 foveq1i_0 foveq1i_1 foveq1i_2 foveq1i_3 oveq1 ax-mp $.
$}
$( /* Equality inference for operation value.  (Contributed by NM,
       28-Feb-1995.) */

$)
${
	foveq2i_0 $f class A $.
	foveq2i_1 $f class B $.
	foveq2i_2 $f class C $.
	foveq2i_3 $f class F $.
	eoveq2i_0 $e |- A = B $.
	oveq2i $p |- ( C F A ) = ( C F B ) $= foveq2i_0 foveq2i_1 wceq foveq2i_2 foveq2i_0 foveq2i_3 co foveq2i_2 foveq2i_1 foveq2i_3 co wceq eoveq2i_0 foveq2i_0 foveq2i_1 foveq2i_2 foveq2i_3 oveq2 ax-mp $.
$}
$( /* Equality inference for operation value.  (Contributed by NM,
         28-Feb-1995.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) */

$)
${
	foveq12i_0 $f class A $.
	foveq12i_1 $f class B $.
	foveq12i_2 $f class C $.
	foveq12i_3 $f class D $.
	foveq12i_4 $f class F $.
	eoveq12i_0 $e |- A = B $.
	eoveq12i_1 $e |- C = D $.
	oveq12i $p |- ( A F C ) = ( B F D ) $= foveq12i_0 foveq12i_1 wceq foveq12i_2 foveq12i_3 wceq foveq12i_0 foveq12i_2 foveq12i_4 co foveq12i_1 foveq12i_3 foveq12i_4 co wceq eoveq12i_0 eoveq12i_1 foveq12i_0 foveq12i_1 foveq12i_2 foveq12i_3 foveq12i_4 oveq12 mp2an $.
$}
$( /* Equality inference for operation value.  (Contributed by NM,
       24-Nov-2007.) */

$)
${
	foveqi_0 $f class A $.
	foveqi_1 $f class B $.
	foveqi_2 $f class C $.
	foveqi_3 $f class D $.
	eoveqi_0 $e |- A = B $.
	oveqi $p |- ( C A D ) = ( C B D ) $= foveqi_0 foveqi_1 wceq foveqi_2 foveqi_3 foveqi_0 co foveqi_2 foveqi_3 foveqi_1 co wceq eoveqi_0 foveqi_2 foveqi_3 foveqi_0 foveqi_1 oveq ax-mp $.
$}
$( /* Equality inference for operation value.  (Contributed by FL,
       11-Jul-2010.) */

$)
${
	foveq123i_0 $f class A $.
	foveq123i_1 $f class B $.
	foveq123i_2 $f class C $.
	foveq123i_3 $f class D $.
	foveq123i_4 $f class F $.
	foveq123i_5 $f class G $.
	eoveq123i_0 $e |- A = C $.
	eoveq123i_1 $e |- B = D $.
	eoveq123i_2 $e |- F = G $.
	oveq123i $p |- ( A F B ) = ( C G D ) $= foveq123i_0 foveq123i_1 foveq123i_4 co foveq123i_2 foveq123i_3 foveq123i_4 co foveq123i_2 foveq123i_3 foveq123i_5 co foveq123i_0 foveq123i_2 foveq123i_1 foveq123i_3 foveq123i_4 eoveq123i_0 eoveq123i_1 oveq12i foveq123i_4 foveq123i_5 foveq123i_2 foveq123i_3 eoveq123i_2 oveqi eqtri $.
$}
$( /* Equality deduction for operation value.  (Contributed by NM,
       13-Mar-1995.) */

$)
${
	foveq1d_0 $f wff ph $.
	foveq1d_1 $f class A $.
	foveq1d_2 $f class B $.
	foveq1d_3 $f class C $.
	foveq1d_4 $f class F $.
	eoveq1d_0 $e |- ( ph -> A = B ) $.
	oveq1d $p |- ( ph -> ( A F C ) = ( B F C ) ) $= foveq1d_0 foveq1d_1 foveq1d_2 wceq foveq1d_1 foveq1d_3 foveq1d_4 co foveq1d_2 foveq1d_3 foveq1d_4 co wceq eoveq1d_0 foveq1d_1 foveq1d_2 foveq1d_3 foveq1d_4 oveq1 syl $.
$}
$( /* Equality deduction for operation value.  (Contributed by NM,
       13-Mar-1995.) */

$)
${
	foveq2d_0 $f wff ph $.
	foveq2d_1 $f class A $.
	foveq2d_2 $f class B $.
	foveq2d_3 $f class C $.
	foveq2d_4 $f class F $.
	eoveq2d_0 $e |- ( ph -> A = B ) $.
	oveq2d $p |- ( ph -> ( C F A ) = ( C F B ) ) $= foveq2d_0 foveq2d_1 foveq2d_2 wceq foveq2d_3 foveq2d_1 foveq2d_4 co foveq2d_3 foveq2d_2 foveq2d_4 co wceq eoveq2d_0 foveq2d_1 foveq2d_2 foveq2d_3 foveq2d_4 oveq2 syl $.
$}
$( /* Equality deduction for operation value.  (Contributed by NM,
       9-Sep-2006.) */

$)
${
	foveqd_0 $f wff ph $.
	foveqd_1 $f class A $.
	foveqd_2 $f class B $.
	foveqd_3 $f class C $.
	foveqd_4 $f class D $.
	eoveqd_0 $e |- ( ph -> A = B ) $.
	oveqd $p |- ( ph -> ( C A D ) = ( C B D ) ) $= foveqd_0 foveqd_1 foveqd_2 wceq foveqd_3 foveqd_4 foveqd_1 co foveqd_3 foveqd_4 foveqd_2 co wceq eoveqd_0 foveqd_3 foveqd_4 foveqd_1 foveqd_2 oveq syl $.
$}
$( /* Equality deduction for operation value.  (Contributed by NM,
         13-Mar-1995.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) */

$)
${
	foveq12d_0 $f wff ph $.
	foveq12d_1 $f class A $.
	foveq12d_2 $f class B $.
	foveq12d_3 $f class C $.
	foveq12d_4 $f class D $.
	foveq12d_5 $f class F $.
	eoveq12d_0 $e |- ( ph -> A = B ) $.
	eoveq12d_1 $e |- ( ph -> C = D ) $.
	oveq12d $p |- ( ph -> ( A F C ) = ( B F D ) ) $= foveq12d_0 foveq12d_1 foveq12d_2 wceq foveq12d_3 foveq12d_4 wceq foveq12d_1 foveq12d_3 foveq12d_5 co foveq12d_2 foveq12d_4 foveq12d_5 co wceq eoveq12d_0 eoveq12d_1 foveq12d_1 foveq12d_2 foveq12d_3 foveq12d_4 foveq12d_5 oveq12 syl2anc $.
$}
$( /* Equality deduction for operation value.  (Contributed by NM,
         10-Aug-1995.) */

$)
${
	foveqan12d_0 $f wff ph $.
	foveqan12d_1 $f wff ps $.
	foveqan12d_2 $f class A $.
	foveqan12d_3 $f class B $.
	foveqan12d_4 $f class C $.
	foveqan12d_5 $f class D $.
	foveqan12d_6 $f class F $.
	eoveqan12d_0 $e |- ( ph -> A = B ) $.
	eoveqan12d_1 $e |- ( ps -> C = D ) $.
	oveqan12d $p |- ( ( ph /\ ps ) -> ( A F C ) = ( B F D ) ) $= foveqan12d_0 foveqan12d_2 foveqan12d_3 wceq foveqan12d_4 foveqan12d_5 wceq foveqan12d_2 foveqan12d_4 foveqan12d_6 co foveqan12d_3 foveqan12d_5 foveqan12d_6 co wceq foveqan12d_1 eoveqan12d_0 eoveqan12d_1 foveqan12d_2 foveqan12d_3 foveqan12d_4 foveqan12d_5 foveqan12d_6 oveq12 syl2an $.
$}
$( /* Equality deduction for operation value.  (Contributed by NM,
         10-Aug-1995.) */

$)
${
	foveqan12rd_0 $f wff ph $.
	foveqan12rd_1 $f wff ps $.
	foveqan12rd_2 $f class A $.
	foveqan12rd_3 $f class B $.
	foveqan12rd_4 $f class C $.
	foveqan12rd_5 $f class D $.
	foveqan12rd_6 $f class F $.
	eoveqan12rd_0 $e |- ( ph -> A = B ) $.
	eoveqan12rd_1 $e |- ( ps -> C = D ) $.
	oveqan12rd $p |- ( ( ps /\ ph ) -> ( A F C ) = ( B F D ) ) $= foveqan12rd_0 foveqan12rd_1 foveqan12rd_2 foveqan12rd_4 foveqan12rd_6 co foveqan12rd_3 foveqan12rd_5 foveqan12rd_6 co wceq foveqan12rd_0 foveqan12rd_1 foveqan12rd_2 foveqan12rd_3 foveqan12rd_4 foveqan12rd_5 foveqan12rd_6 eoveqan12rd_0 eoveqan12rd_1 oveqan12d ancoms $.
$}
$( /* Equality deduction for operation value.  (Contributed by FL,
       22-Dec-2008.) */

$)
${
	foveq123d_0 $f wff ph $.
	foveq123d_1 $f class A $.
	foveq123d_2 $f class B $.
	foveq123d_3 $f class C $.
	foveq123d_4 $f class D $.
	foveq123d_5 $f class F $.
	foveq123d_6 $f class G $.
	eoveq123d_0 $e |- ( ph -> F = G ) $.
	eoveq123d_1 $e |- ( ph -> A = B ) $.
	eoveq123d_2 $e |- ( ph -> C = D ) $.
	oveq123d $p |- ( ph -> ( A F C ) = ( B G D ) ) $= foveq123d_0 foveq123d_1 foveq123d_3 foveq123d_5 co foveq123d_1 foveq123d_3 foveq123d_6 co foveq123d_2 foveq123d_4 foveq123d_6 co foveq123d_0 foveq123d_5 foveq123d_6 foveq123d_1 foveq123d_3 eoveq123d_0 oveqd foveq123d_0 foveq123d_1 foveq123d_2 foveq123d_3 foveq123d_4 foveq123d_6 eoveq123d_1 eoveq123d_2 oveq12d eqtrd $.
$}
$( /* Deduction version of bound-variable hypothesis builder ~ nfov .
       (Contributed by NM, 13-Dec-2005.)  (Proof shortened by Andrew Salmon,
       22-Oct-2011.) */

$)
${
	fnfovd_0 $f wff ph $.
	fnfovd_1 $f set x $.
	fnfovd_2 $f class A $.
	fnfovd_3 $f class B $.
	fnfovd_4 $f class F $.
	enfovd_0 $e |- ( ph -> F/_ x A ) $.
	enfovd_1 $e |- ( ph -> F/_ x F ) $.
	enfovd_2 $e |- ( ph -> F/_ x B ) $.
	nfovd $p |- ( ph -> F/_ x ( A F B ) ) $= fnfovd_0 fnfovd_1 fnfovd_2 fnfovd_3 fnfovd_4 co fnfovd_2 fnfovd_3 cop fnfovd_4 cfv fnfovd_2 fnfovd_3 fnfovd_4 df-ov fnfovd_0 fnfovd_1 fnfovd_2 fnfovd_3 cop fnfovd_4 enfovd_1 fnfovd_0 fnfovd_1 fnfovd_2 fnfovd_3 enfovd_0 enfovd_2 nfopd nffvd nfcxfrd $.
$}
$( /* Bound-variable hypothesis builder for operation value.  (Contributed by
       NM, 4-May-2004.) */

$)
${
	fnfov_0 $f set x $.
	fnfov_1 $f class A $.
	fnfov_2 $f class B $.
	fnfov_3 $f class F $.
	enfov_0 $e |- F/_ x A $.
	enfov_1 $e |- F/_ x F $.
	enfov_2 $e |- F/_ x B $.
	nfov $p |- F/_ x ( A F B ) $= fnfov_0 fnfov_1 fnfov_2 fnfov_3 co wnfc wtru fnfov_0 fnfov_1 fnfov_2 fnfov_3 fnfov_0 fnfov_1 wnfc wtru enfov_0 a1i fnfov_0 fnfov_3 wnfc wtru enfov_1 a1i fnfov_0 fnfov_2 wnfc wtru enfov_2 a1i nfovd trud $.
$}
$( /* The law of concretion.  Special case of Theorem 9.5 of [Quine] p. 61.
       (Contributed by Mario Carneiro, 20-Mar-2013.) */

$)
${
	$d a ph r s t w $.
	$d a r s t w x $.
	$d a r s t w y $.
	$d a r s t w z $.
	ioprabid_0 $f set w $.
	ioprabid_1 $f set t $.
	ioprabid_2 $f set s $.
	ioprabid_3 $f set r $.
	ioprabid_4 $f set a $.
	foprabid_0 $f wff ph $.
	foprabid_1 $f set x $.
	foprabid_2 $f set y $.
	foprabid_3 $f set z $.
	oprabid $p |- ( <. <. x , y >. , z >. e. { <. <. x , y >. , z >. | ph } <-> ph ) $= ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 ioprabid_0 foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop foprabid_0 foprabid_1 foprabid_2 foprabid_3 coprab foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class opex ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq wa ioprabid_1 wex ioprabid_4 wex ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq wa ioprabid_1 wex ioprabid_4 wex ioprabid_4 ioprabid_1 ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class opex foprabid_3 vex eqvinop biimpi ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq wa ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi wi ioprabid_4 ioprabid_1 ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi wi ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_4 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_4 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop eqeq1 ioprabid_4 sup_set_class ioprabid_1 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class ioprabid_4 vex ioprabid_1 vex opth1 syl6bi ioprabid_4 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi ioprabid_4 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop wceq ioprabid_4 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop wceq ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop wceq wa ioprabid_2 wex ioprabid_3 wex ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi wi wi ioprabid_3 ioprabid_2 ioprabid_4 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class foprabid_1 vex foprabid_2 vex eqvinop ioprabid_4 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop wceq ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop wceq wa ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi wi wi ioprabid_3 ioprabid_2 ioprabid_4 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi wi wi ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop wceq ioprabid_4 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi wi ioprabid_4 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop wceq ioprabid_4 sup_set_class ioprabid_1 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop ioprabid_0 sup_set_class ioprabid_4 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class opeq1 eqeq2d ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi wi foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi wi foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 wex foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 wex foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 wa foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa wa foprabid_1 foprabid_2 foprabid_3 foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 wa foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq wa foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq wa foprabid_0 wa foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq wa foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa wa foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq wa foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq wa foprabid_0 foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq w3a foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq wa foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq wa foprabid_1 sup_set_class foprabid_2 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class foprabid_3 sup_set_class ioprabid_1 sup_set_class foprabid_1 vex foprabid_2 vex foprabid_3 vex otth2 foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq df-3an bitri anbi1i foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq wa foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 anass foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa anass 3bitri 3exbii foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex wa foprabid_2 wex foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex foprabid_2 wex wa foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa wa foprabid_3 wex foprabid_1 wex foprabid_2 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex wa foprabid_1 wex foprabid_2 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex wa foprabid_2 wex foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa wa foprabid_3 wex foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex wa foprabid_1 wex foprabid_2 foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_1 foprabid_3 foprabid_1 sup_set_class foprabid_3 sup_set_class wceq foprabid_1 wal wn foprabid_3 foprabid_1 sup_set_class ioprabid_3 sup_set_class foprabid_1 foprabid_3 nfcvf2 foprabid_1 sup_set_class foprabid_3 sup_set_class wceq foprabid_1 wal wn foprabid_3 ioprabid_3 sup_set_class nfcvd nfeqd exdistrf eximi foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa wa foprabid_3 wex foprabid_1 foprabid_2 excom foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex wa foprabid_1 foprabid_2 excom 3imtr4i foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex foprabid_1 foprabid_2 foprabid_1 sup_set_class foprabid_2 sup_set_class wceq foprabid_1 wal wn foprabid_2 foprabid_1 sup_set_class ioprabid_3 sup_set_class foprabid_1 foprabid_2 nfcvf2 foprabid_1 sup_set_class foprabid_2 sup_set_class wceq foprabid_1 wal wn foprabid_2 ioprabid_3 sup_set_class nfcvd nfeqd exdistrf foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex foprabid_2 wex wa foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa wa foprabid_3 wex foprabid_2 wex foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_2 foprabid_3 foprabid_2 sup_set_class foprabid_3 sup_set_class wceq foprabid_2 wal wn foprabid_3 foprabid_2 sup_set_class ioprabid_2 sup_set_class foprabid_2 foprabid_3 nfcvf2 foprabid_2 sup_set_class foprabid_3 sup_set_class wceq foprabid_2 wal wn foprabid_3 ioprabid_2 sup_set_class nfcvd nfeqd exdistrf anim2i eximi 3syl sylbi foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 wex foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq w3a foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 wex foprabid_0 foprabid_1 sup_set_class foprabid_2 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class foprabid_3 sup_set_class ioprabid_1 sup_set_class foprabid_1 vex foprabid_2 vex foprabid_3 vex otth2 foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wi wi foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_1 weu foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wa foprabid_1 wex foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex wi foprabid_1 ioprabid_3 euequ1 foprabid_1 sup_set_class ioprabid_3 sup_set_class wceq foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex foprabid_1 eupick mpan foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wi foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_2 weu foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wa foprabid_2 wex foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex wi foprabid_2 ioprabid_2 euequ1 foprabid_2 sup_set_class ioprabid_2 sup_set_class wceq foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex foprabid_2 eupick mpan foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_3 weu foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wa foprabid_3 wex foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 wi foprabid_3 ioprabid_1 euequ1 foprabid_3 sup_set_class ioprabid_1 sup_set_class wceq foprabid_0 foprabid_3 eupick mpan syl6 syl6 3impd syl5bi com12 syl5 ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 wi ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop eqeq1 ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop eqcom syl6bb ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex foprabid_0 ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 wa foprabid_1 foprabid_2 foprabid_3 ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq foprabid_0 ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop wceq ioprabid_0 sup_set_class ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop eqeq1 ioprabid_3 sup_set_class ioprabid_2 sup_set_class cop ioprabid_1 sup_set_class cop foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop eqcom syl6bb anbi1d 3exbidv imbi1d imbi12d mpbiri syl6bi adantr exlimivv sylbi com3l mpdd adantr exlimivv mpcom ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 wex ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 19.8a ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 19.8a ioprabid_0 sup_set_class foprabid_1 sup_set_class foprabid_2 sup_set_class cop foprabid_3 sup_set_class cop wceq foprabid_0 wa foprabid_3 wex foprabid_2 wex foprabid_1 19.8a 3syl ex impbid foprabid_0 foprabid_1 foprabid_2 foprabid_3 ioprabid_0 df-oprab elab2 $.
$}
$( /* The result of an operation is a set.  (Contributed by NM, 13-Mar-1995.) */

$)
${
	fovex_0 $f class A $.
	fovex_1 $f class B $.
	fovex_2 $f class F $.
	ovex $p |- ( A F B ) e. _V $= fovex_0 fovex_1 fovex_2 co fovex_0 fovex_1 cop fovex_2 cfv cvv fovex_0 fovex_1 fovex_2 df-ov fovex_0 fovex_1 cop fovex_2 fvex eqeltri $.
$}
$( /* The result of an operation value is always a subset of the union of the
     range.  (Contributed by Mario Carneiro, 12-Jan-2017.) */

$)
${
	fovssunirn_0 $f class F $.
	fovssunirn_1 $f class X $.
	fovssunirn_2 $f class Y $.
	ovssunirn $p |- ( X F Y ) C_ U. ran F $= fovssunirn_1 fovssunirn_2 fovssunirn_0 co fovssunirn_1 fovssunirn_2 cop fovssunirn_0 cfv fovssunirn_0 crn cuni fovssunirn_1 fovssunirn_2 fovssunirn_0 df-ov fovssunirn_0 fovssunirn_1 fovssunirn_2 cop fvssunirn eqsstri $.
$}
$( /* The value of an operation when the one of the arguments is a proper
       class.  Note: this theorem is dependent on our particular definitions of
       operation value, function value, and ordered pair.  (Contributed by
       Mario Carneiro, 26-Apr-2015.) */

$)
${
	fovprc_0 $f class A $.
	fovprc_1 $f class B $.
	fovprc_2 $f class F $.
	eovprc_0 $e |- Rel dom F $.
	ovprc $p |- ( -. ( A e. _V /\ B e. _V ) -> ( A F B ) = (/) ) $= fovprc_0 cvv wcel fovprc_1 cvv wcel wa wn fovprc_0 fovprc_1 fovprc_2 co fovprc_0 fovprc_1 cop fovprc_2 cfv c0 fovprc_0 fovprc_1 fovprc_2 df-ov fovprc_0 cvv wcel fovprc_1 cvv wcel wa wn fovprc_0 fovprc_1 cop fovprc_2 cdm wcel wn fovprc_0 fovprc_1 cop fovprc_2 cfv c0 wceq fovprc_0 fovprc_1 cop fovprc_2 cdm wcel fovprc_0 cvv wcel fovprc_1 cvv wcel wa fovprc_0 fovprc_1 cop fovprc_2 cdm wcel fovprc_0 fovprc_1 fovprc_2 cdm wbr fovprc_0 cvv wcel fovprc_1 cvv wcel wa fovprc_0 fovprc_1 fovprc_2 cdm df-br fovprc_2 cdm wrel fovprc_0 fovprc_1 fovprc_2 cdm wbr fovprc_0 cvv wcel fovprc_1 cvv wcel wa eovprc_0 fovprc_0 fovprc_1 fovprc_2 cdm brrelex12 mpan sylbir con3i fovprc_0 fovprc_1 cop fovprc_2 ndmfv syl syl5eq $.
$}
$( /* The value of an operation when the first argument is a proper class.
       (Contributed by NM, 16-Jun-2004.) */

$)
${
	fovprc1_0 $f class A $.
	fovprc1_1 $f class B $.
	fovprc1_2 $f class F $.
	eovprc1_0 $e |- Rel dom F $.
	ovprc1 $p |- ( -. A e. _V -> ( A F B ) = (/) ) $= fovprc1_0 cvv wcel wn fovprc1_0 cvv wcel fovprc1_1 cvv wcel wa wn fovprc1_0 fovprc1_1 fovprc1_2 co c0 wceq fovprc1_0 cvv wcel fovprc1_1 cvv wcel wa fovprc1_0 cvv wcel fovprc1_0 cvv wcel fovprc1_1 cvv wcel simpl con3i fovprc1_0 fovprc1_1 fovprc1_2 eovprc1_0 ovprc syl $.
$}
$( /* The value of an operation when the second argument is a proper class.
       (Contributed by Mario Carneiro, 26-Apr-2015.) */

$)
${
	fovprc2_0 $f class A $.
	fovprc2_1 $f class B $.
	fovprc2_2 $f class F $.
	eovprc2_0 $e |- Rel dom F $.
	ovprc2 $p |- ( -. B e. _V -> ( A F B ) = (/) ) $= fovprc2_1 cvv wcel wn fovprc2_0 cvv wcel fovprc2_1 cvv wcel wa wn fovprc2_0 fovprc2_1 fovprc2_2 co c0 wceq fovprc2_0 cvv wcel fovprc2_1 cvv wcel wa fovprc2_1 cvv wcel fovprc2_0 cvv wcel fovprc2_1 cvv wcel simpr con3i fovprc2_0 fovprc2_1 fovprc2_2 eovprc2_0 ovprc syl $.
$}
$( /* Reverse closure for an operation value.  (Contributed by Mario Carneiro,
       5-May-2015.) */

$)
${
	fovrcl_0 $f class A $.
	fovrcl_1 $f class B $.
	fovrcl_2 $f class C $.
	fovrcl_3 $f class F $.
	eovrcl_0 $e |- Rel dom F $.
	ovrcl $p |- ( C e. ( A F B ) -> ( A e. _V /\ B e. _V ) ) $= fovrcl_2 fovrcl_0 fovrcl_1 fovrcl_3 co wcel fovrcl_0 fovrcl_1 fovrcl_3 co c0 wceq fovrcl_0 cvv wcel fovrcl_1 cvv wcel wa fovrcl_0 fovrcl_1 fovrcl_3 co fovrcl_2 n0i fovrcl_0 fovrcl_1 fovrcl_3 eovrcl_0 ovprc nsyl2 $.
$}
$( /* Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.)  (Proof shortened by Mario Carneiro, 5-Dec-2016.) */

$)
${
	$d y A $.
	$d y B $.
	$d y C $.
	$d y D $.
	$d y F $.
	$d x y $.
	icsbovg_0 $f set y $.
	fcsbovg_0 $f set x $.
	fcsbovg_1 $f class A $.
	fcsbovg_2 $f class B $.
	fcsbovg_3 $f class C $.
	fcsbovg_4 $f class D $.
	fcsbovg_5 $f class F $.
	csbovg $p |- ( A e. D -> [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B [_ A / x ]_ F [_ A / x ]_ C ) ) $= fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 fcsbovg_3 fcsbovg_5 co csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_3 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_5 csb co wceq fcsbovg_0 fcsbovg_1 fcsbovg_2 fcsbovg_3 fcsbovg_5 co csb fcsbovg_0 fcsbovg_1 fcsbovg_2 csb fcsbovg_0 fcsbovg_1 fcsbovg_3 csb fcsbovg_0 fcsbovg_1 fcsbovg_5 csb co wceq icsbovg_0 fcsbovg_1 fcsbovg_4 icsbovg_0 sup_set_class fcsbovg_1 wceq fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 fcsbovg_3 fcsbovg_5 co csb fcsbovg_0 fcsbovg_1 fcsbovg_2 fcsbovg_3 fcsbovg_5 co csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_3 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_5 csb co fcsbovg_0 fcsbovg_1 fcsbovg_2 csb fcsbovg_0 fcsbovg_1 fcsbovg_3 csb fcsbovg_0 fcsbovg_1 fcsbovg_5 csb co fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_1 fcsbovg_2 fcsbovg_3 fcsbovg_5 co csbeq1 icsbovg_0 sup_set_class fcsbovg_1 wceq fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 csb fcsbovg_0 fcsbovg_1 fcsbovg_2 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_3 csb fcsbovg_0 fcsbovg_1 fcsbovg_3 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_5 csb fcsbovg_0 fcsbovg_1 fcsbovg_5 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_1 fcsbovg_5 csbeq1 fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_1 fcsbovg_2 csbeq1 fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_1 fcsbovg_3 csbeq1 oveq123d eqeq12d fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 fcsbovg_3 fcsbovg_5 co fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_3 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_5 csb co icsbovg_0 vex fcsbovg_0 fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_3 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_5 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 nfcsb1v fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_5 nfcsb1v fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_3 nfcsb1v nfov fcsbovg_0 sup_set_class icsbovg_0 sup_set_class wceq fcsbovg_2 fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 csb fcsbovg_3 fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_3 csb fcsbovg_5 fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_5 csb fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_5 csbeq1a fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_2 csbeq1a fcsbovg_0 icsbovg_0 sup_set_class fcsbovg_3 csbeq1a oveq123d csbief vtoclg $.
$}
$( /* Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) */

$)
${
	$d x F $.
	fcsbov12g_0 $f set x $.
	fcsbov12g_1 $f class A $.
	fcsbov12g_2 $f class B $.
	fcsbov12g_3 $f class C $.
	fcsbov12g_4 $f class D $.
	fcsbov12g_5 $f class F $.
	csbov12g $p |- ( A e. D -> [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B F [_ A / x ]_ C ) ) $= fcsbov12g_1 fcsbov12g_4 wcel fcsbov12g_0 fcsbov12g_1 fcsbov12g_2 fcsbov12g_3 fcsbov12g_5 co csb fcsbov12g_0 fcsbov12g_1 fcsbov12g_2 csb fcsbov12g_0 fcsbov12g_1 fcsbov12g_3 csb fcsbov12g_0 fcsbov12g_1 fcsbov12g_5 csb co fcsbov12g_0 fcsbov12g_1 fcsbov12g_2 csb fcsbov12g_0 fcsbov12g_1 fcsbov12g_3 csb fcsbov12g_5 co fcsbov12g_0 fcsbov12g_1 fcsbov12g_2 fcsbov12g_3 fcsbov12g_4 fcsbov12g_5 csbovg fcsbov12g_1 fcsbov12g_4 wcel fcsbov12g_0 fcsbov12g_1 fcsbov12g_5 csb fcsbov12g_5 fcsbov12g_0 fcsbov12g_1 fcsbov12g_2 csb fcsbov12g_0 fcsbov12g_1 fcsbov12g_3 csb fcsbov12g_0 fcsbov12g_1 fcsbov12g_5 fcsbov12g_4 csbconstg oveqd eqtrd $.
$}
$( /* Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) */

$)
${
	$d x C $.
	$d x F $.
	fcsbov1g_0 $f set x $.
	fcsbov1g_1 $f class A $.
	fcsbov1g_2 $f class B $.
	fcsbov1g_3 $f class C $.
	fcsbov1g_4 $f class D $.
	fcsbov1g_5 $f class F $.
	csbov1g $p |- ( A e. D -> [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B F C ) ) $= fcsbov1g_1 fcsbov1g_4 wcel fcsbov1g_0 fcsbov1g_1 fcsbov1g_2 fcsbov1g_3 fcsbov1g_5 co csb fcsbov1g_0 fcsbov1g_1 fcsbov1g_2 csb fcsbov1g_0 fcsbov1g_1 fcsbov1g_3 csb fcsbov1g_5 co fcsbov1g_0 fcsbov1g_1 fcsbov1g_2 csb fcsbov1g_3 fcsbov1g_5 co fcsbov1g_0 fcsbov1g_1 fcsbov1g_2 fcsbov1g_3 fcsbov1g_4 fcsbov1g_5 csbov12g fcsbov1g_1 fcsbov1g_4 wcel fcsbov1g_0 fcsbov1g_1 fcsbov1g_3 csb fcsbov1g_3 fcsbov1g_0 fcsbov1g_1 fcsbov1g_2 csb fcsbov1g_5 fcsbov1g_0 fcsbov1g_1 fcsbov1g_3 fcsbov1g_4 csbconstg oveq2d eqtrd $.
$}
$( /* Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) */

$)
${
	$d x B $.
	$d x F $.
	fcsbov2g_0 $f set x $.
	fcsbov2g_1 $f class A $.
	fcsbov2g_2 $f class B $.
	fcsbov2g_3 $f class C $.
	fcsbov2g_4 $f class D $.
	fcsbov2g_5 $f class F $.
	csbov2g $p |- ( A e. D -> [_ A / x ]_ ( B F C ) = ( B F [_ A / x ]_ C ) ) $= fcsbov2g_1 fcsbov2g_4 wcel fcsbov2g_0 fcsbov2g_1 fcsbov2g_2 fcsbov2g_3 fcsbov2g_5 co csb fcsbov2g_0 fcsbov2g_1 fcsbov2g_2 csb fcsbov2g_0 fcsbov2g_1 fcsbov2g_3 csb fcsbov2g_5 co fcsbov2g_2 fcsbov2g_0 fcsbov2g_1 fcsbov2g_3 csb fcsbov2g_5 co fcsbov2g_0 fcsbov2g_1 fcsbov2g_2 fcsbov2g_3 fcsbov2g_4 fcsbov2g_5 csbov12g fcsbov2g_1 fcsbov2g_4 wcel fcsbov2g_0 fcsbov2g_1 fcsbov2g_2 csb fcsbov2g_2 fcsbov2g_0 fcsbov2g_1 fcsbov2g_3 csb fcsbov2g_5 fcsbov2g_0 fcsbov2g_1 fcsbov2g_2 fcsbov2g_4 csbconstg oveq1d eqtrd $.
$}
$( /* A frequently used special case of ~ rspc2ev for operation values.
       (Contributed by NM, 21-Mar-2007.) */

$)
${
	$d x A $.
	$d x y B $.
	$d x y C $.
	$d y D $.
	$d x y F $.
	$d x y S $.
	frspceov_0 $f set x $.
	frspceov_1 $f set y $.
	frspceov_2 $f class A $.
	frspceov_3 $f class B $.
	frspceov_4 $f class C $.
	frspceov_5 $f class D $.
	frspceov_6 $f class S $.
	frspceov_7 $f class F $.
	rspceov $p |- ( ( C e. A /\ D e. B /\ S = ( C F D ) ) -> E. x e. A E. y e. B S = ( x F y ) ) $= frspceov_6 frspceov_0 sup_set_class frspceov_1 sup_set_class frspceov_7 co wceq frspceov_6 frspceov_4 frspceov_5 frspceov_7 co wceq frspceov_6 frspceov_4 frspceov_1 sup_set_class frspceov_7 co wceq frspceov_0 frspceov_1 frspceov_4 frspceov_5 frspceov_2 frspceov_3 frspceov_0 sup_set_class frspceov_4 wceq frspceov_0 sup_set_class frspceov_1 sup_set_class frspceov_7 co frspceov_4 frspceov_1 sup_set_class frspceov_7 co frspceov_6 frspceov_0 sup_set_class frspceov_4 frspceov_1 sup_set_class frspceov_7 oveq1 eqeq2d frspceov_1 sup_set_class frspceov_5 wceq frspceov_4 frspceov_1 sup_set_class frspceov_7 co frspceov_4 frspceov_5 frspceov_7 co frspceov_6 frspceov_1 sup_set_class frspceov_5 frspceov_4 frspceov_7 oveq2 eqeq2d rspc2ev $.
$}
$( /* Equivalence of operation value and ordered triple membership, analogous
       to ~ fnopfvb .  (Contributed by NM, 17-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) */

$)
${
	ffnotovb_0 $f class A $.
	ffnotovb_1 $f class B $.
	ffnotovb_2 $f class C $.
	ffnotovb_3 $f class D $.
	ffnotovb_4 $f class R $.
	ffnotovb_5 $f class F $.
	fnotovb $p |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) -> ( ( C F D ) = R <-> <. C , D , R >. e. F ) ) $= ffnotovb_5 ffnotovb_0 ffnotovb_1 cxp wfn ffnotovb_2 ffnotovb_0 wcel ffnotovb_3 ffnotovb_1 wcel w3a ffnotovb_2 ffnotovb_3 cop ffnotovb_5 cfv ffnotovb_4 wceq ffnotovb_2 ffnotovb_3 cop ffnotovb_4 cop ffnotovb_5 wcel ffnotovb_2 ffnotovb_3 ffnotovb_5 co ffnotovb_4 wceq ffnotovb_2 ffnotovb_3 ffnotovb_4 cotp ffnotovb_5 wcel ffnotovb_5 ffnotovb_0 ffnotovb_1 cxp wfn ffnotovb_2 ffnotovb_0 wcel ffnotovb_3 ffnotovb_1 wcel ffnotovb_2 ffnotovb_3 cop ffnotovb_5 cfv ffnotovb_4 wceq ffnotovb_2 ffnotovb_3 cop ffnotovb_4 cop ffnotovb_5 wcel wb ffnotovb_2 ffnotovb_0 wcel ffnotovb_3 ffnotovb_1 wcel wa ffnotovb_5 ffnotovb_0 ffnotovb_1 cxp wfn ffnotovb_2 ffnotovb_3 cop ffnotovb_0 ffnotovb_1 cxp wcel ffnotovb_2 ffnotovb_3 cop ffnotovb_5 cfv ffnotovb_4 wceq ffnotovb_2 ffnotovb_3 cop ffnotovb_4 cop ffnotovb_5 wcel wb ffnotovb_2 ffnotovb_3 ffnotovb_0 ffnotovb_1 opelxpi ffnotovb_0 ffnotovb_1 cxp ffnotovb_2 ffnotovb_3 cop ffnotovb_4 ffnotovb_5 fnopfvb sylan2 3impb ffnotovb_2 ffnotovb_3 ffnotovb_5 co ffnotovb_2 ffnotovb_3 cop ffnotovb_5 cfv ffnotovb_4 ffnotovb_2 ffnotovb_3 ffnotovb_5 df-ov eqeq1i ffnotovb_2 ffnotovb_3 ffnotovb_4 cotp ffnotovb_2 ffnotovb_3 cop ffnotovb_4 cop ffnotovb_5 ffnotovb_2 ffnotovb_3 ffnotovb_4 df-ot eleq1i 3bitr4g $.
$}
$( /* Class abstraction for operations in terms of class abstraction of
       ordered pairs.  (Contributed by NM, 12-Mar-1995.) */

$)
${
	$d x z w v $.
	$d y z w v $.
	$d w ph v $.
	idfoprab2_0 $f set v $.
	fdfoprab2_0 $f wff ph $.
	fdfoprab2_1 $f set x $.
	fdfoprab2_2 $f set y $.
	fdfoprab2_3 $f set z $.
	fdfoprab2_4 $f set w $.
	dfoprab2 $p |- { <. <. x , y >. , z >. | ph } = { <. w , z >. | E. x E. y ( w = <. x , y >. /\ ph ) } $= idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_3 wex fdfoprab2_2 wex fdfoprab2_1 wex idfoprab2_0 cab idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_2 wex fdfoprab2_1 wex wa fdfoprab2_3 wex fdfoprab2_4 wex idfoprab2_0 cab fdfoprab2_0 fdfoprab2_1 fdfoprab2_2 fdfoprab2_3 coprab fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_2 wex fdfoprab2_1 wex fdfoprab2_4 fdfoprab2_3 copab idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_3 wex fdfoprab2_2 wex fdfoprab2_1 wex idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_2 wex fdfoprab2_1 wex wa fdfoprab2_3 wex fdfoprab2_4 wex idfoprab2_0 idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_2 wex fdfoprab2_1 wex fdfoprab2_4 wex fdfoprab2_3 wex idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_2 wex fdfoprab2_1 wex fdfoprab2_3 wex fdfoprab2_4 wex idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_3 wex fdfoprab2_2 wex fdfoprab2_1 wex idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_2 wex fdfoprab2_1 wex wa fdfoprab2_3 wex fdfoprab2_4 wex idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_2 wex fdfoprab2_1 wex fdfoprab2_3 fdfoprab2_4 excom idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_2 wex fdfoprab2_1 wex fdfoprab2_4 wex fdfoprab2_3 wex idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_4 wex fdfoprab2_3 wex fdfoprab2_2 wex fdfoprab2_1 wex idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_3 wex fdfoprab2_2 wex fdfoprab2_1 wex idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_3 fdfoprab2_4 fdfoprab2_1 fdfoprab2_2 exrot4 idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_4 wex idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_1 fdfoprab2_2 fdfoprab2_3 idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_4 wex idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq wa fdfoprab2_4 wex idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq wa fdfoprab2_4 idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq wa fdfoprab2_0 wa idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq wa fdfoprab2_0 wa idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq wa idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq wa idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq wa fdfoprab2_0 fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class opeq1 eqeq2d pm5.32ri anbi1i idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 anass idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 an32 3bitr3i exbii idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq wa fdfoprab2_4 wex idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_4 wex fdfoprab2_4 fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class opex isseti idfoprab2_0 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop fdfoprab2_3 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_4 19.42v mpbiran2 bitri 3exbii bitri idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa wa fdfoprab2_2 wex fdfoprab2_1 wex idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_2 wex fdfoprab2_1 wex wa fdfoprab2_4 fdfoprab2_3 idfoprab2_0 sup_set_class fdfoprab2_4 sup_set_class fdfoprab2_3 sup_set_class cop wceq fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_1 fdfoprab2_2 19.42vv 2exbii 3bitr3i abbii fdfoprab2_0 fdfoprab2_1 fdfoprab2_2 fdfoprab2_3 idfoprab2_0 df-oprab fdfoprab2_4 sup_set_class fdfoprab2_1 sup_set_class fdfoprab2_2 sup_set_class cop wceq fdfoprab2_0 wa fdfoprab2_2 wex fdfoprab2_1 wex fdfoprab2_4 fdfoprab2_3 idfoprab2_0 df-opab 3eqtr4i $.
$}
$( /* An operation class abstraction is a relation.  (Contributed by NM,
       16-Jun-2004.) */

$)
${
	$d x z w $.
	$d y z w $.
	$d w ph $.
	ireloprab_0 $f set w $.
	freloprab_0 $f wff ph $.
	freloprab_1 $f set x $.
	freloprab_2 $f set y $.
	freloprab_3 $f set z $.
	reloprab $p |- Rel { <. <. x , y >. , z >. | ph } $= ireloprab_0 sup_set_class freloprab_1 sup_set_class freloprab_2 sup_set_class cop wceq freloprab_0 wa freloprab_2 wex freloprab_1 wex ireloprab_0 freloprab_3 freloprab_0 freloprab_1 freloprab_2 freloprab_3 coprab freloprab_0 freloprab_1 freloprab_2 freloprab_3 ireloprab_0 dfoprab2 relopabi $.
$}
$( /* @{
    @d x y z w v @.  @d ph v @.
    dfoprab2f.1 @e |- ( ph -> A. w ph ) @.
    @( Class abstraction for operations in terms of class abstraction of
       ordered pairs.  This is a version of ~ dfoprab2 with bound-variable
       hypothesis instead of distinct variable requirement. @)
    dfoprab2f @p |- { <. <. x , y >. , z >. | ph } =
                   { <. w , z >. | E. x E. y ( w = <. x , y >. /\ ph ) } @=
      ( vv coprab cv cop wceq wa wex copab dfoprab2 ax-17 hban hbex weq
      eqeq1 anbi1d 2exbidv cbvopab1
      eqtri ) ABCDHGIZBICIJZKZALZCMZBMZGDNEIZUFKZALZCMBM
      ZEDNABCDGOUJUNGDEUIEBUHECUGAEUGEPFQRRUNGPGESZUHUMBCUOUGULAUEUKUFTUAUBUCUD
      @.
  @}
*/

$)
$( /* The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 25-Apr-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) */

$)
${
	$d w x $.
	$d w y $.
	$d w z $.
	$d w ph $.
	infoprab1_0 $f set w $.
	fnfoprab1_0 $f wff ph $.
	fnfoprab1_1 $f set x $.
	fnfoprab1_2 $f set y $.
	fnfoprab1_3 $f set z $.
	nfoprab1 $p |- F/_ x { <. <. x , y >. , z >. | ph } $= fnfoprab1_1 fnfoprab1_0 fnfoprab1_1 fnfoprab1_2 fnfoprab1_3 coprab infoprab1_0 sup_set_class fnfoprab1_1 sup_set_class fnfoprab1_2 sup_set_class cop fnfoprab1_3 sup_set_class cop wceq fnfoprab1_0 wa fnfoprab1_3 wex fnfoprab1_2 wex fnfoprab1_1 wex infoprab1_0 cab fnfoprab1_0 fnfoprab1_1 fnfoprab1_2 fnfoprab1_3 infoprab1_0 df-oprab infoprab1_0 sup_set_class fnfoprab1_1 sup_set_class fnfoprab1_2 sup_set_class cop fnfoprab1_3 sup_set_class cop wceq fnfoprab1_0 wa fnfoprab1_3 wex fnfoprab1_2 wex fnfoprab1_1 wex fnfoprab1_1 infoprab1_0 infoprab1_0 sup_set_class fnfoprab1_1 sup_set_class fnfoprab1_2 sup_set_class cop fnfoprab1_3 sup_set_class cop wceq fnfoprab1_0 wa fnfoprab1_3 wex fnfoprab1_2 wex fnfoprab1_1 nfe1 nfab nfcxfr $.
$}
$( /* The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 25-Apr-1995.)  (Revised by David Abernethy,
       30-Jul-2012.) */

$)
${
	$d w x $.
	$d w y $.
	$d w z $.
	$d w ph $.
	infoprab2_0 $f set w $.
	fnfoprab2_0 $f wff ph $.
	fnfoprab2_1 $f set x $.
	fnfoprab2_2 $f set y $.
	fnfoprab2_3 $f set z $.
	nfoprab2 $p |- F/_ y { <. <. x , y >. , z >. | ph } $= fnfoprab2_2 fnfoprab2_0 fnfoprab2_1 fnfoprab2_2 fnfoprab2_3 coprab infoprab2_0 sup_set_class fnfoprab2_1 sup_set_class fnfoprab2_2 sup_set_class cop fnfoprab2_3 sup_set_class cop wceq fnfoprab2_0 wa fnfoprab2_3 wex fnfoprab2_2 wex fnfoprab2_1 wex infoprab2_0 cab fnfoprab2_0 fnfoprab2_1 fnfoprab2_2 fnfoprab2_3 infoprab2_0 df-oprab infoprab2_0 sup_set_class fnfoprab2_1 sup_set_class fnfoprab2_2 sup_set_class cop fnfoprab2_3 sup_set_class cop wceq fnfoprab2_0 wa fnfoprab2_3 wex fnfoprab2_2 wex fnfoprab2_1 wex fnfoprab2_2 infoprab2_0 infoprab2_0 sup_set_class fnfoprab2_1 sup_set_class fnfoprab2_2 sup_set_class cop fnfoprab2_3 sup_set_class cop wceq fnfoprab2_0 wa fnfoprab2_3 wex fnfoprab2_2 wex fnfoprab2_2 fnfoprab2_1 infoprab2_0 sup_set_class fnfoprab2_1 sup_set_class fnfoprab2_2 sup_set_class cop fnfoprab2_3 sup_set_class cop wceq fnfoprab2_0 wa fnfoprab2_3 wex fnfoprab2_2 nfe1 nfex nfab nfcxfr $.
$}
$( /* The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 22-Aug-2013.) */

$)
${
	$d w x $.
	$d w y $.
	$d w z $.
	$d w ph $.
	infoprab3_0 $f set w $.
	fnfoprab3_0 $f wff ph $.
	fnfoprab3_1 $f set x $.
	fnfoprab3_2 $f set y $.
	fnfoprab3_3 $f set z $.
	nfoprab3 $p |- F/_ z { <. <. x , y >. , z >. | ph } $= fnfoprab3_3 fnfoprab3_0 fnfoprab3_1 fnfoprab3_2 fnfoprab3_3 coprab infoprab3_0 sup_set_class fnfoprab3_1 sup_set_class fnfoprab3_2 sup_set_class cop fnfoprab3_3 sup_set_class cop wceq fnfoprab3_0 wa fnfoprab3_3 wex fnfoprab3_2 wex fnfoprab3_1 wex infoprab3_0 cab fnfoprab3_0 fnfoprab3_1 fnfoprab3_2 fnfoprab3_3 infoprab3_0 df-oprab infoprab3_0 sup_set_class fnfoprab3_1 sup_set_class fnfoprab3_2 sup_set_class cop fnfoprab3_3 sup_set_class cop wceq fnfoprab3_0 wa fnfoprab3_3 wex fnfoprab3_2 wex fnfoprab3_1 wex fnfoprab3_3 infoprab3_0 infoprab3_0 sup_set_class fnfoprab3_1 sup_set_class fnfoprab3_2 sup_set_class cop fnfoprab3_3 sup_set_class cop wceq fnfoprab3_0 wa fnfoprab3_3 wex fnfoprab3_2 wex fnfoprab3_3 fnfoprab3_1 infoprab3_0 sup_set_class fnfoprab3_1 sup_set_class fnfoprab3_2 sup_set_class cop fnfoprab3_3 sup_set_class cop wceq fnfoprab3_0 wa fnfoprab3_3 wex fnfoprab3_3 fnfoprab3_2 infoprab3_0 sup_set_class fnfoprab3_1 sup_set_class fnfoprab3_2 sup_set_class cop fnfoprab3_3 sup_set_class cop wceq fnfoprab3_0 wa fnfoprab3_3 nfe1 nfex nfex nfab nfcxfr $.
$}
$( /* Bound-variable hypothesis builder for an operation class abstraction.
       (Contributed by NM, 22-Aug-2013.) */

$)
${
	$d v w x $.
	$d v w y $.
	$d v w z $.
	$d v ph $.
	infoprab_0 $f set v $.
	fnfoprab_0 $f wff ph $.
	fnfoprab_1 $f set x $.
	fnfoprab_2 $f set y $.
	fnfoprab_3 $f set z $.
	fnfoprab_4 $f set w $.
	enfoprab_0 $e |- F/ w ph $.
	nfoprab $p |- F/_ w { <. <. x , y >. , z >. | ph } $= fnfoprab_4 fnfoprab_0 fnfoprab_1 fnfoprab_2 fnfoprab_3 coprab infoprab_0 sup_set_class fnfoprab_1 sup_set_class fnfoprab_2 sup_set_class cop fnfoprab_3 sup_set_class cop wceq fnfoprab_0 wa fnfoprab_3 wex fnfoprab_2 wex fnfoprab_1 wex infoprab_0 cab fnfoprab_0 fnfoprab_1 fnfoprab_2 fnfoprab_3 infoprab_0 df-oprab infoprab_0 sup_set_class fnfoprab_1 sup_set_class fnfoprab_2 sup_set_class cop fnfoprab_3 sup_set_class cop wceq fnfoprab_0 wa fnfoprab_3 wex fnfoprab_2 wex fnfoprab_1 wex fnfoprab_4 infoprab_0 infoprab_0 sup_set_class fnfoprab_1 sup_set_class fnfoprab_2 sup_set_class cop fnfoprab_3 sup_set_class cop wceq fnfoprab_0 wa fnfoprab_3 wex fnfoprab_2 wex fnfoprab_4 fnfoprab_1 infoprab_0 sup_set_class fnfoprab_1 sup_set_class fnfoprab_2 sup_set_class cop fnfoprab_3 sup_set_class cop wceq fnfoprab_0 wa fnfoprab_3 wex fnfoprab_4 fnfoprab_2 infoprab_0 sup_set_class fnfoprab_1 sup_set_class fnfoprab_2 sup_set_class cop fnfoprab_3 sup_set_class cop wceq fnfoprab_0 wa fnfoprab_4 fnfoprab_3 infoprab_0 sup_set_class fnfoprab_1 sup_set_class fnfoprab_2 sup_set_class cop fnfoprab_3 sup_set_class cop wceq fnfoprab_0 fnfoprab_4 infoprab_0 sup_set_class fnfoprab_1 sup_set_class fnfoprab_2 sup_set_class cop fnfoprab_3 sup_set_class cop wceq fnfoprab_4 nfv enfoprab_0 nfan nfex nfex nfex nfab nfcxfr $.
$}
$( /* Equivalent wff's yield equal operation class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.)  (Revised by Mario Carneiro,
       24-Jun-2014.) */

$)
${
	$d x z w $.
	$d y z w $.
	$d w ph $.
	$d w ps $.
	$d w ch $.
	ioprabbid_0 $f set w $.
	foprabbid_0 $f wff ph $.
	foprabbid_1 $f wff ps $.
	foprabbid_2 $f wff ch $.
	foprabbid_3 $f set x $.
	foprabbid_4 $f set y $.
	foprabbid_5 $f set z $.
	eoprabbid_0 $e |- F/ x ph $.
	eoprabbid_1 $e |- F/ y ph $.
	eoprabbid_2 $e |- F/ z ph $.
	eoprabbid_3 $e |- ( ph -> ( ps <-> ch ) ) $.
	oprabbid $p |- ( ph -> { <. <. x , y >. , z >. | ps } = { <. <. x , y >. , z >. | ch } ) $= foprabbid_0 ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_1 wa foprabbid_5 wex foprabbid_4 wex foprabbid_3 wex ioprabbid_0 cab ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_2 wa foprabbid_5 wex foprabbid_4 wex foprabbid_3 wex ioprabbid_0 cab foprabbid_1 foprabbid_3 foprabbid_4 foprabbid_5 coprab foprabbid_2 foprabbid_3 foprabbid_4 foprabbid_5 coprab foprabbid_0 ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_1 wa foprabbid_5 wex foprabbid_4 wex foprabbid_3 wex ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_2 wa foprabbid_5 wex foprabbid_4 wex foprabbid_3 wex ioprabbid_0 foprabbid_0 ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_1 wa foprabbid_5 wex foprabbid_4 wex ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_2 wa foprabbid_5 wex foprabbid_4 wex foprabbid_3 eoprabbid_0 foprabbid_0 ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_1 wa foprabbid_5 wex ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_2 wa foprabbid_5 wex foprabbid_4 eoprabbid_1 foprabbid_0 ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_1 wa ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq foprabbid_2 wa foprabbid_5 eoprabbid_2 foprabbid_0 foprabbid_1 foprabbid_2 ioprabbid_0 sup_set_class foprabbid_3 sup_set_class foprabbid_4 sup_set_class cop foprabbid_5 sup_set_class cop wceq eoprabbid_3 anbi2d exbid exbid exbid abbidv foprabbid_1 foprabbid_3 foprabbid_4 foprabbid_5 ioprabbid_0 df-oprab foprabbid_2 foprabbid_3 foprabbid_4 foprabbid_5 ioprabbid_0 df-oprab 3eqtr4g $.
$}
$( /* Equivalent wff's yield equal operation class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.) */

$)
${
	$d x z ph $.
	$d y z ph $.
	foprabbidv_0 $f wff ph $.
	foprabbidv_1 $f wff ps $.
	foprabbidv_2 $f wff ch $.
	foprabbidv_3 $f set x $.
	foprabbidv_4 $f set y $.
	foprabbidv_5 $f set z $.
	eoprabbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	oprabbidv $p |- ( ph -> { <. <. x , y >. , z >. | ps } = { <. <. x , y >. , z >. | ch } ) $= foprabbidv_0 foprabbidv_1 foprabbidv_2 foprabbidv_3 foprabbidv_4 foprabbidv_5 foprabbidv_0 foprabbidv_3 nfv foprabbidv_0 foprabbidv_4 nfv foprabbidv_0 foprabbidv_5 nfv eoprabbidv_0 oprabbid $.
$}
$( /* Equivalent wff's yield equal operation class abstractions.  (Contributed
       by NM, 28-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) */

$)
${
	$d x z w $.
	$d y z w $.
	$d w ph $.
	$d w ps $.
	ioprabbii_0 $f set w $.
	foprabbii_0 $f wff ph $.
	foprabbii_1 $f wff ps $.
	foprabbii_2 $f set x $.
	foprabbii_3 $f set y $.
	foprabbii_4 $f set z $.
	eoprabbii_0 $e |- ( ph <-> ps ) $.
	oprabbii $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ps } $= ioprabbii_0 sup_set_class ioprabbii_0 sup_set_class wceq foprabbii_0 foprabbii_2 foprabbii_3 foprabbii_4 coprab foprabbii_1 foprabbii_2 foprabbii_3 foprabbii_4 coprab wceq ioprabbii_0 sup_set_class eqid ioprabbii_0 sup_set_class ioprabbii_0 sup_set_class wceq foprabbii_0 foprabbii_1 foprabbii_2 foprabbii_3 foprabbii_4 foprabbii_0 foprabbii_1 wb ioprabbii_0 sup_set_class ioprabbii_0 sup_set_class wceq eoprabbii_0 a1i oprabbidv ax-mp $.
$}
$( /* Equivalence of ordered pair abstraction subclass and implication.
       Compare ~ ssopab2 .  (Contributed by FL, 6-Nov-2013.)  (Proof shortened
       by Mario Carneiro, 11-Dec-2016.) */

$)
${
	$d ph w $.
	$d ps w $.
	$d x w $.
	$d y w $.
	$d z w $.
	issoprab2_0 $f set w $.
	fssoprab2_0 $f wff ph $.
	fssoprab2_1 $f wff ps $.
	fssoprab2_2 $f set x $.
	fssoprab2_3 $f set y $.
	fssoprab2_4 $f set z $.
	ssoprab2 $p |- ( A. x A. y A. z ( ph -> ps ) -> { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } ) $= fssoprab2_0 fssoprab2_1 wi fssoprab2_4 wal fssoprab2_3 wal fssoprab2_2 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex fssoprab2_3 wex fssoprab2_2 wex issoprab2_0 cab issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex fssoprab2_3 wex fssoprab2_2 wex issoprab2_0 cab fssoprab2_0 fssoprab2_2 fssoprab2_3 fssoprab2_4 coprab fssoprab2_1 fssoprab2_2 fssoprab2_3 fssoprab2_4 coprab fssoprab2_0 fssoprab2_1 wi fssoprab2_4 wal fssoprab2_3 wal fssoprab2_2 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex fssoprab2_3 wex fssoprab2_2 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex fssoprab2_3 wex fssoprab2_2 wex issoprab2_0 fssoprab2_0 fssoprab2_1 wi fssoprab2_4 wal fssoprab2_3 wal fssoprab2_2 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex fssoprab2_3 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex fssoprab2_3 wex wi fssoprab2_2 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex fssoprab2_3 wex fssoprab2_2 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex fssoprab2_3 wex fssoprab2_2 wex wi fssoprab2_0 fssoprab2_1 wi fssoprab2_4 wal fssoprab2_3 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex fssoprab2_3 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex fssoprab2_3 wex wi fssoprab2_2 fssoprab2_0 fssoprab2_1 wi fssoprab2_4 wal fssoprab2_3 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex wi fssoprab2_3 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex fssoprab2_3 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex fssoprab2_3 wex wi fssoprab2_0 fssoprab2_1 wi fssoprab2_4 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex wi fssoprab2_3 fssoprab2_0 fssoprab2_1 wi fssoprab2_4 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa wi fssoprab2_4 wal issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex wi fssoprab2_0 fssoprab2_1 wi issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa wi fssoprab2_4 fssoprab2_0 fssoprab2_1 wi fssoprab2_0 fssoprab2_1 issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 fssoprab2_1 wi id anim2d alimi issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 exim syl alimi issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex fssoprab2_3 exim syl alimi issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_0 wa fssoprab2_4 wex fssoprab2_3 wex issoprab2_0 sup_set_class fssoprab2_2 sup_set_class fssoprab2_3 sup_set_class cop fssoprab2_4 sup_set_class cop wceq fssoprab2_1 wa fssoprab2_4 wex fssoprab2_3 wex fssoprab2_2 exim syl ss2abdv fssoprab2_0 fssoprab2_2 fssoprab2_3 fssoprab2_4 issoprab2_0 df-oprab fssoprab2_1 fssoprab2_2 fssoprab2_3 fssoprab2_4 issoprab2_0 df-oprab 3sstr4g $.
$}
$( /* Equivalence of ordered pair abstraction subclass and implication.  Compare
     ~ ssopab2b .  (Contributed by FL, 6-Nov-2013.)  (Proof shortened by Mario
     Carneiro, 11-Dec-2016.) */

$)
${
	fssoprab2b_0 $f wff ph $.
	fssoprab2b_1 $f wff ps $.
	fssoprab2b_2 $f set x $.
	fssoprab2b_3 $f set y $.
	fssoprab2b_4 $f set z $.
	ssoprab2b $p |- ( { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } <-> A. x A. y A. z ( ph -> ps ) ) $= fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab wss fssoprab2b_0 fssoprab2b_1 wi fssoprab2b_4 wal fssoprab2b_3 wal fssoprab2b_2 wal fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab wss fssoprab2b_0 fssoprab2b_1 wi fssoprab2b_4 wal fssoprab2b_3 wal fssoprab2b_2 fssoprab2b_2 fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 nfoprab1 fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 nfoprab1 nfss fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab wss fssoprab2b_0 fssoprab2b_1 wi fssoprab2b_4 wal fssoprab2b_3 fssoprab2b_3 fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 nfoprab2 fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 nfoprab2 nfss fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab wss fssoprab2b_0 fssoprab2b_1 wi fssoprab2b_4 fssoprab2b_4 fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 nfoprab3 fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 nfoprab3 nfss fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab wss fssoprab2b_2 sup_set_class fssoprab2b_3 sup_set_class cop fssoprab2b_4 sup_set_class cop fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab wcel fssoprab2b_2 sup_set_class fssoprab2b_3 sup_set_class cop fssoprab2b_4 sup_set_class cop fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab wcel fssoprab2b_0 fssoprab2b_1 fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 coprab fssoprab2b_2 sup_set_class fssoprab2b_3 sup_set_class cop fssoprab2b_4 sup_set_class cop ssel fssoprab2b_0 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 oprabid fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 oprabid 3imtr3g alrimi alrimi alrimi fssoprab2b_0 fssoprab2b_1 fssoprab2b_2 fssoprab2b_3 fssoprab2b_4 ssoprab2 impbii $.
$}
$( /* Equivalence of ordered pair abstraction subclass and biconditional.
     Compare ~ eqopab2b .  (Contributed by Mario Carneiro, 4-Jan-2017.) */

$)
${
	feqoprab2b_0 $f wff ph $.
	feqoprab2b_1 $f wff ps $.
	feqoprab2b_2 $f set x $.
	feqoprab2b_3 $f set y $.
	feqoprab2b_4 $f set z $.
	eqoprab2b $p |- ( { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ps } <-> A. x A. y A. z ( ph <-> ps ) ) $= feqoprab2b_0 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab feqoprab2b_1 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab wss feqoprab2b_1 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab feqoprab2b_0 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab wss wa feqoprab2b_0 feqoprab2b_1 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 wal feqoprab2b_1 feqoprab2b_0 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 wal wa feqoprab2b_0 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab feqoprab2b_1 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab wceq feqoprab2b_0 feqoprab2b_1 wb feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 wal feqoprab2b_0 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab feqoprab2b_1 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab wss feqoprab2b_0 feqoprab2b_1 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 wal feqoprab2b_1 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab feqoprab2b_0 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab wss feqoprab2b_1 feqoprab2b_0 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 wal feqoprab2b_0 feqoprab2b_1 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 ssoprab2b feqoprab2b_1 feqoprab2b_0 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 ssoprab2b anbi12i feqoprab2b_0 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab feqoprab2b_1 feqoprab2b_2 feqoprab2b_3 feqoprab2b_4 coprab eqss feqoprab2b_0 feqoprab2b_1 wb feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 wal feqoprab2b_0 feqoprab2b_1 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_1 feqoprab2b_0 wi feqoprab2b_4 wal feqoprab2b_3 wal wa feqoprab2b_2 wal feqoprab2b_0 feqoprab2b_1 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 wal feqoprab2b_1 feqoprab2b_0 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 wal wa feqoprab2b_0 feqoprab2b_1 wb feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_0 feqoprab2b_1 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_1 feqoprab2b_0 wi feqoprab2b_4 wal feqoprab2b_3 wal wa feqoprab2b_2 feqoprab2b_0 feqoprab2b_1 feqoprab2b_3 feqoprab2b_4 2albiim albii feqoprab2b_0 feqoprab2b_1 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_1 feqoprab2b_0 wi feqoprab2b_4 wal feqoprab2b_3 wal feqoprab2b_2 19.26 bitri 3bitr4i $.
$}
$( /* An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.)  (Revised by Mario Carneiro, 19-Mar-2015.) */

$)
${
	$d x y z A $.
	$d y z B $.
	$d x y z D $.
	$d y z E $.
	$d z C $.
	$d z F $.
	impt2eq123_0 $f set z $.
	fmpt2eq123_0 $f set x $.
	fmpt2eq123_1 $f set y $.
	fmpt2eq123_2 $f class A $.
	fmpt2eq123_3 $f class B $.
	fmpt2eq123_4 $f class C $.
	fmpt2eq123_5 $f class D $.
	fmpt2eq123_6 $f class E $.
	fmpt2eq123_7 $f class F $.
	mpt2eq123 $p |- ( ( A = D /\ A. x e. A ( B = E /\ A. y e. B C = F ) ) -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $= fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral wa fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel wa impt2eq123_0 sup_set_class fmpt2eq123_4 wceq wa fmpt2eq123_0 fmpt2eq123_1 impt2eq123_0 coprab fmpt2eq123_0 sup_set_class fmpt2eq123_5 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel wa impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa fmpt2eq123_0 fmpt2eq123_1 impt2eq123_0 coprab fmpt2eq123_0 fmpt2eq123_1 fmpt2eq123_2 fmpt2eq123_3 fmpt2eq123_4 cmpt2 fmpt2eq123_0 fmpt2eq123_1 fmpt2eq123_5 fmpt2eq123_6 fmpt2eq123_7 cmpt2 fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral wa fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel wa impt2eq123_0 sup_set_class fmpt2eq123_4 wceq wa fmpt2eq123_0 sup_set_class fmpt2eq123_5 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel wa impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa fmpt2eq123_0 fmpt2eq123_1 impt2eq123_0 fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral fmpt2eq123_0 fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_0 nfv fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 nfra1 nfan fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral fmpt2eq123_1 fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_1 nfv fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_1 fmpt2eq123_0 fmpt2eq123_2 fmpt2eq123_1 fmpt2eq123_2 nfcv fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral fmpt2eq123_1 fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_1 nfv fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 nfra1 nfan nfral nfan fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral wa impt2eq123_0 nfv fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral wa fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel impt2eq123_0 sup_set_class fmpt2eq123_4 wceq wa wa fmpt2eq123_0 sup_set_class fmpt2eq123_5 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa wa fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel wa impt2eq123_0 sup_set_class fmpt2eq123_4 wceq wa fmpt2eq123_0 sup_set_class fmpt2eq123_5 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel wa impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel impt2eq123_0 sup_set_class fmpt2eq123_4 wceq wa wa fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa wa fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_0 sup_set_class fmpt2eq123_5 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa wa fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel impt2eq123_0 sup_set_class fmpt2eq123_4 wceq wa fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 wral fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel impt2eq123_0 sup_set_class fmpt2eq123_4 wceq wa fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa wb fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral wa fmpt2eq123_0 fmpt2eq123_2 rsp fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel impt2eq123_0 sup_set_class fmpt2eq123_4 wceq wa fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel impt2eq123_0 sup_set_class fmpt2eq123_4 wceq impt2eq123_0 sup_set_class fmpt2eq123_7 wceq fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 wral fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel fmpt2eq123_4 fmpt2eq123_7 wceq impt2eq123_0 sup_set_class fmpt2eq123_4 wceq impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wb fmpt2eq123_4 fmpt2eq123_7 wceq fmpt2eq123_1 fmpt2eq123_3 rsp fmpt2eq123_4 fmpt2eq123_7 impt2eq123_0 sup_set_class eqeq2 syl6 pm5.32d fmpt2eq123_3 fmpt2eq123_6 wceq fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq fmpt2eq123_3 fmpt2eq123_6 fmpt2eq123_1 sup_set_class eleq2 anbi1d sylan9bbr syl6 pm5.32d fmpt2eq123_2 fmpt2eq123_5 wceq fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_0 sup_set_class fmpt2eq123_5 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq wa fmpt2eq123_2 fmpt2eq123_5 fmpt2eq123_0 sup_set_class eleq2 anbi1d sylan9bbr fmpt2eq123_0 sup_set_class fmpt2eq123_2 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_3 wcel impt2eq123_0 sup_set_class fmpt2eq123_4 wceq anass fmpt2eq123_0 sup_set_class fmpt2eq123_5 wcel fmpt2eq123_1 sup_set_class fmpt2eq123_6 wcel impt2eq123_0 sup_set_class fmpt2eq123_7 wceq anass 3bitr4g oprabbid fmpt2eq123_0 fmpt2eq123_1 impt2eq123_0 fmpt2eq123_2 fmpt2eq123_3 fmpt2eq123_4 df-mpt2 fmpt2eq123_0 fmpt2eq123_1 impt2eq123_0 fmpt2eq123_5 fmpt2eq123_6 fmpt2eq123_7 df-mpt2 3eqtr4g $.
$}
$( /* An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	fmpt2eq12_0 $f set x $.
	fmpt2eq12_1 $f set y $.
	fmpt2eq12_2 $f class A $.
	fmpt2eq12_3 $f class B $.
	fmpt2eq12_4 $f class C $.
	fmpt2eq12_5 $f class D $.
	fmpt2eq12_6 $f class E $.
	mpt2eq12 $p |- ( ( A = C /\ B = D ) -> ( x e. A , y e. B |-> E ) = ( x e. C , y e. D |-> E ) ) $= fmpt2eq12_3 fmpt2eq12_5 wceq fmpt2eq12_2 fmpt2eq12_4 wceq fmpt2eq12_3 fmpt2eq12_5 wceq fmpt2eq12_6 fmpt2eq12_6 wceq fmpt2eq12_1 fmpt2eq12_3 wral wa fmpt2eq12_0 fmpt2eq12_2 wral fmpt2eq12_0 fmpt2eq12_1 fmpt2eq12_2 fmpt2eq12_3 fmpt2eq12_6 cmpt2 fmpt2eq12_0 fmpt2eq12_1 fmpt2eq12_4 fmpt2eq12_5 fmpt2eq12_6 cmpt2 wceq fmpt2eq12_3 fmpt2eq12_5 wceq fmpt2eq12_3 fmpt2eq12_5 wceq fmpt2eq12_6 fmpt2eq12_6 wceq fmpt2eq12_1 fmpt2eq12_3 wral wa fmpt2eq12_0 fmpt2eq12_2 fmpt2eq12_3 fmpt2eq12_5 wceq fmpt2eq12_6 fmpt2eq12_6 wceq fmpt2eq12_1 fmpt2eq12_3 wral fmpt2eq12_6 fmpt2eq12_6 wceq fmpt2eq12_1 fmpt2eq12_3 fmpt2eq12_6 eqid rgenw jctr ralrimivw fmpt2eq12_0 fmpt2eq12_1 fmpt2eq12_2 fmpt2eq12_3 fmpt2eq12_6 fmpt2eq12_4 fmpt2eq12_5 fmpt2eq12_6 mpt2eq123 sylan2 $.
$}
$( /* An equality deduction for the maps to notation.  (Contributed by Mario
         Carneiro, 26-Jan-2017.) */

$)
${
	$d z A $.
	$d z B $.
	$d z C $.
	$d z D $.
	$d z E $.
	$d x z ph $.
	$d z F $.
	$d y z ph $.
	impt2eq123dva_0 $f set z $.
	fmpt2eq123dva_0 $f wff ph $.
	fmpt2eq123dva_1 $f set x $.
	fmpt2eq123dva_2 $f set y $.
	fmpt2eq123dva_3 $f class A $.
	fmpt2eq123dva_4 $f class B $.
	fmpt2eq123dva_5 $f class C $.
	fmpt2eq123dva_6 $f class D $.
	fmpt2eq123dva_7 $f class E $.
	fmpt2eq123dva_8 $f class F $.
	empt2eq123dva_0 $e |- ( ph -> A = D ) $.
	empt2eq123dva_1 $e |- ( ( ph /\ x e. A ) -> B = E ) $.
	empt2eq123dva_2 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C = F ) $.
	mpt2eq123dva $p |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $= fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_5 wceq wa fmpt2eq123dva_1 fmpt2eq123dva_2 impt2eq123dva_0 coprab fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_6 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_7 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_8 wceq wa fmpt2eq123dva_1 fmpt2eq123dva_2 impt2eq123dva_0 coprab fmpt2eq123dva_1 fmpt2eq123dva_2 fmpt2eq123dva_3 fmpt2eq123dva_4 fmpt2eq123dva_5 cmpt2 fmpt2eq123dva_1 fmpt2eq123dva_2 fmpt2eq123dva_6 fmpt2eq123dva_7 fmpt2eq123dva_8 cmpt2 fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_5 wceq wa fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_6 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_7 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_8 wceq wa fmpt2eq123dva_1 fmpt2eq123dva_2 impt2eq123dva_0 fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_5 wceq wa fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_8 wceq wa fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_6 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_7 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_8 wceq wa fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_5 wceq impt2eq123dva_0 sup_set_class fmpt2eq123dva_8 wceq fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel wa wa fmpt2eq123dva_5 fmpt2eq123dva_8 impt2eq123dva_0 sup_set_class empt2eq123dva_2 eqeq2d pm5.32da fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel wa fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_6 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_7 wcel wa impt2eq123dva_0 sup_set_class fmpt2eq123dva_8 wceq fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel wa fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_7 wcel wa fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_6 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_7 wcel wa fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_4 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_7 wcel fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel wa fmpt2eq123dva_4 fmpt2eq123dva_7 fmpt2eq123dva_2 sup_set_class empt2eq123dva_1 eleq2d pm5.32da fmpt2eq123dva_0 fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_3 wcel fmpt2eq123dva_1 sup_set_class fmpt2eq123dva_6 wcel fmpt2eq123dva_2 sup_set_class fmpt2eq123dva_7 wcel fmpt2eq123dva_0 fmpt2eq123dva_3 fmpt2eq123dva_6 fmpt2eq123dva_1 sup_set_class empt2eq123dva_0 eleq2d anbi1d bitrd anbi1d bitrd oprabbidv fmpt2eq123dva_1 fmpt2eq123dva_2 impt2eq123dva_0 fmpt2eq123dva_3 fmpt2eq123dva_4 fmpt2eq123dva_5 df-mpt2 fmpt2eq123dva_1 fmpt2eq123dva_2 impt2eq123dva_0 fmpt2eq123dva_6 fmpt2eq123dva_7 fmpt2eq123dva_8 df-mpt2 3eqtr4g $.
$}
$( /* An equality deduction for the maps to notation.  (Contributed by NM,
       12-Sep-2011.) */

$)
${
	$d x ph $.
	$d y ph $.
	fmpt2eq123dv_0 $f wff ph $.
	fmpt2eq123dv_1 $f set x $.
	fmpt2eq123dv_2 $f set y $.
	fmpt2eq123dv_3 $f class A $.
	fmpt2eq123dv_4 $f class B $.
	fmpt2eq123dv_5 $f class C $.
	fmpt2eq123dv_6 $f class D $.
	fmpt2eq123dv_7 $f class E $.
	fmpt2eq123dv_8 $f class F $.
	empt2eq123dv_0 $e |- ( ph -> A = D ) $.
	empt2eq123dv_1 $e |- ( ph -> B = E ) $.
	empt2eq123dv_2 $e |- ( ph -> C = F ) $.
	mpt2eq123dv $p |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $= fmpt2eq123dv_0 fmpt2eq123dv_1 fmpt2eq123dv_2 fmpt2eq123dv_3 fmpt2eq123dv_4 fmpt2eq123dv_5 fmpt2eq123dv_6 fmpt2eq123dv_7 fmpt2eq123dv_8 empt2eq123dv_0 fmpt2eq123dv_0 fmpt2eq123dv_4 fmpt2eq123dv_7 wceq fmpt2eq123dv_1 sup_set_class fmpt2eq123dv_3 wcel empt2eq123dv_1 adantr fmpt2eq123dv_0 fmpt2eq123dv_5 fmpt2eq123dv_8 wceq fmpt2eq123dv_1 sup_set_class fmpt2eq123dv_3 wcel fmpt2eq123dv_2 sup_set_class fmpt2eq123dv_4 wcel wa empt2eq123dv_2 adantr mpt2eq123dva $.
$}
$( /* An equality inference for the maps to notation.  (Contributed by NM,
       15-Jul-2013.) */

$)
${
	fmpt2eq123i_0 $f set x $.
	fmpt2eq123i_1 $f set y $.
	fmpt2eq123i_2 $f class A $.
	fmpt2eq123i_3 $f class B $.
	fmpt2eq123i_4 $f class C $.
	fmpt2eq123i_5 $f class D $.
	fmpt2eq123i_6 $f class E $.
	fmpt2eq123i_7 $f class F $.
	empt2eq123i_0 $e |- A = D $.
	empt2eq123i_1 $e |- B = E $.
	empt2eq123i_2 $e |- C = F $.
	mpt2eq123i $p |- ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) $= fmpt2eq123i_0 fmpt2eq123i_1 fmpt2eq123i_2 fmpt2eq123i_3 fmpt2eq123i_4 cmpt2 fmpt2eq123i_0 fmpt2eq123i_1 fmpt2eq123i_5 fmpt2eq123i_6 fmpt2eq123i_7 cmpt2 wceq wtru fmpt2eq123i_0 fmpt2eq123i_1 fmpt2eq123i_2 fmpt2eq123i_3 fmpt2eq123i_4 fmpt2eq123i_5 fmpt2eq123i_6 fmpt2eq123i_7 fmpt2eq123i_2 fmpt2eq123i_5 wceq wtru empt2eq123i_0 a1i fmpt2eq123i_3 fmpt2eq123i_6 wceq wtru empt2eq123i_1 a1i fmpt2eq123i_4 fmpt2eq123i_7 wceq wtru empt2eq123i_2 a1i mpt2eq123dv trud $.
$}
$( /* Slightly more general equality inference for the maps to notation.
       (Contributed by NM, 17-Oct-2013.) */

$)
${
	$d x z ph $.
	$d y z ph $.
	$d z A $.
	$d z B $.
	$d z C $.
	$d z D $.
	impt2eq3dva_0 $f set z $.
	fmpt2eq3dva_0 $f wff ph $.
	fmpt2eq3dva_1 $f set x $.
	fmpt2eq3dva_2 $f set y $.
	fmpt2eq3dva_3 $f class A $.
	fmpt2eq3dva_4 $f class B $.
	fmpt2eq3dva_5 $f class C $.
	fmpt2eq3dva_6 $f class D $.
	empt2eq3dva_0 $e |- ( ( ph /\ x e. A /\ y e. B ) -> C = D ) $.
	mpt2eq3dva $p |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) ) $= fmpt2eq3dva_0 fmpt2eq3dva_1 sup_set_class fmpt2eq3dva_3 wcel fmpt2eq3dva_2 sup_set_class fmpt2eq3dva_4 wcel wa impt2eq3dva_0 sup_set_class fmpt2eq3dva_5 wceq wa fmpt2eq3dva_1 fmpt2eq3dva_2 impt2eq3dva_0 coprab fmpt2eq3dva_1 sup_set_class fmpt2eq3dva_3 wcel fmpt2eq3dva_2 sup_set_class fmpt2eq3dva_4 wcel wa impt2eq3dva_0 sup_set_class fmpt2eq3dva_6 wceq wa fmpt2eq3dva_1 fmpt2eq3dva_2 impt2eq3dva_0 coprab fmpt2eq3dva_1 fmpt2eq3dva_2 fmpt2eq3dva_3 fmpt2eq3dva_4 fmpt2eq3dva_5 cmpt2 fmpt2eq3dva_1 fmpt2eq3dva_2 fmpt2eq3dva_3 fmpt2eq3dva_4 fmpt2eq3dva_6 cmpt2 fmpt2eq3dva_0 fmpt2eq3dva_1 sup_set_class fmpt2eq3dva_3 wcel fmpt2eq3dva_2 sup_set_class fmpt2eq3dva_4 wcel wa impt2eq3dva_0 sup_set_class fmpt2eq3dva_5 wceq wa fmpt2eq3dva_1 sup_set_class fmpt2eq3dva_3 wcel fmpt2eq3dva_2 sup_set_class fmpt2eq3dva_4 wcel wa impt2eq3dva_0 sup_set_class fmpt2eq3dva_6 wceq wa fmpt2eq3dva_1 fmpt2eq3dva_2 impt2eq3dva_0 fmpt2eq3dva_0 fmpt2eq3dva_1 sup_set_class fmpt2eq3dva_3 wcel fmpt2eq3dva_2 sup_set_class fmpt2eq3dva_4 wcel wa impt2eq3dva_0 sup_set_class fmpt2eq3dva_5 wceq impt2eq3dva_0 sup_set_class fmpt2eq3dva_6 wceq fmpt2eq3dva_0 fmpt2eq3dva_1 sup_set_class fmpt2eq3dva_3 wcel fmpt2eq3dva_2 sup_set_class fmpt2eq3dva_4 wcel wa wa fmpt2eq3dva_5 fmpt2eq3dva_6 impt2eq3dva_0 sup_set_class fmpt2eq3dva_0 fmpt2eq3dva_1 sup_set_class fmpt2eq3dva_3 wcel fmpt2eq3dva_2 sup_set_class fmpt2eq3dva_4 wcel fmpt2eq3dva_5 fmpt2eq3dva_6 wceq empt2eq3dva_0 3expb eqeq2d pm5.32da oprabbidv fmpt2eq3dva_1 fmpt2eq3dva_2 impt2eq3dva_0 fmpt2eq3dva_3 fmpt2eq3dva_4 fmpt2eq3dva_5 df-mpt2 fmpt2eq3dva_1 fmpt2eq3dva_2 impt2eq3dva_0 fmpt2eq3dva_3 fmpt2eq3dva_4 fmpt2eq3dva_6 df-mpt2 3eqtr4g $.
$}
$( /* An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) */

$)
${
	fmpt2eq3ia_0 $f set x $.
	fmpt2eq3ia_1 $f set y $.
	fmpt2eq3ia_2 $f class A $.
	fmpt2eq3ia_3 $f class B $.
	fmpt2eq3ia_4 $f class C $.
	fmpt2eq3ia_5 $f class D $.
	empt2eq3ia_0 $e |- ( ( x e. A /\ y e. B ) -> C = D ) $.
	mpt2eq3ia $p |- ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) $= fmpt2eq3ia_0 fmpt2eq3ia_1 fmpt2eq3ia_2 fmpt2eq3ia_3 fmpt2eq3ia_4 cmpt2 fmpt2eq3ia_0 fmpt2eq3ia_1 fmpt2eq3ia_2 fmpt2eq3ia_3 fmpt2eq3ia_5 cmpt2 wceq wtru fmpt2eq3ia_0 fmpt2eq3ia_1 fmpt2eq3ia_2 fmpt2eq3ia_3 fmpt2eq3ia_4 fmpt2eq3ia_5 fmpt2eq3ia_0 sup_set_class fmpt2eq3ia_2 wcel fmpt2eq3ia_1 sup_set_class fmpt2eq3ia_3 wcel fmpt2eq3ia_4 fmpt2eq3ia_5 wceq wtru empt2eq3ia_0 3adant1 mpt2eq3dva trud $.
$}
$( /* Bound-variable hypothesis builder for an operation in maps-to notation.
       (Contributed by NM, 27-Aug-2013.) */

$)
${
	$d z A $.
	$d z B $.
	$d z C $.
	$d z x $.
	$d z y $.
	infmpt21_0 $f set z $.
	fnfmpt21_0 $f set x $.
	fnfmpt21_1 $f set y $.
	fnfmpt21_2 $f class A $.
	fnfmpt21_3 $f class B $.
	fnfmpt21_4 $f class C $.
	nfmpt21 $p |- F/_ x ( x e. A , y e. B |-> C ) $= fnfmpt21_0 fnfmpt21_0 fnfmpt21_1 fnfmpt21_2 fnfmpt21_3 fnfmpt21_4 cmpt2 fnfmpt21_0 sup_set_class fnfmpt21_2 wcel fnfmpt21_1 sup_set_class fnfmpt21_3 wcel wa infmpt21_0 sup_set_class fnfmpt21_4 wceq wa fnfmpt21_0 fnfmpt21_1 infmpt21_0 coprab fnfmpt21_0 fnfmpt21_1 infmpt21_0 fnfmpt21_2 fnfmpt21_3 fnfmpt21_4 df-mpt2 fnfmpt21_0 sup_set_class fnfmpt21_2 wcel fnfmpt21_1 sup_set_class fnfmpt21_3 wcel wa infmpt21_0 sup_set_class fnfmpt21_4 wceq wa fnfmpt21_0 fnfmpt21_1 infmpt21_0 nfoprab1 nfcxfr $.
$}
$( /* Bound-variable hypothesis builder for an operation in maps-to notation.
       (Contributed by NM, 27-Aug-2013.) */

$)
${
	$d z A $.
	$d z B $.
	$d z C $.
	$d z x $.
	$d z y $.
	infmpt22_0 $f set z $.
	fnfmpt22_0 $f set x $.
	fnfmpt22_1 $f set y $.
	fnfmpt22_2 $f class A $.
	fnfmpt22_3 $f class B $.
	fnfmpt22_4 $f class C $.
	nfmpt22 $p |- F/_ y ( x e. A , y e. B |-> C ) $= fnfmpt22_1 fnfmpt22_0 fnfmpt22_1 fnfmpt22_2 fnfmpt22_3 fnfmpt22_4 cmpt2 fnfmpt22_0 sup_set_class fnfmpt22_2 wcel fnfmpt22_1 sup_set_class fnfmpt22_3 wcel wa infmpt22_0 sup_set_class fnfmpt22_4 wceq wa fnfmpt22_0 fnfmpt22_1 infmpt22_0 coprab fnfmpt22_0 fnfmpt22_1 infmpt22_0 fnfmpt22_2 fnfmpt22_3 fnfmpt22_4 df-mpt2 fnfmpt22_0 sup_set_class fnfmpt22_2 wcel fnfmpt22_1 sup_set_class fnfmpt22_3 wcel wa infmpt22_0 sup_set_class fnfmpt22_4 wceq wa fnfmpt22_0 fnfmpt22_1 infmpt22_0 nfoprab2 nfcxfr $.
$}
$( /* Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by NM, 20-Feb-2013.) */

$)
${
	$d w x z $.
	$d w y z $.
	$d w A $.
	$d w B $.
	$d w C $.
	infmpt2_0 $f set w $.
	fnfmpt2_0 $f set x $.
	fnfmpt2_1 $f set y $.
	fnfmpt2_2 $f set z $.
	fnfmpt2_3 $f class A $.
	fnfmpt2_4 $f class B $.
	fnfmpt2_5 $f class C $.
	enfmpt2_0 $e |- F/_ z A $.
	enfmpt2_1 $e |- F/_ z B $.
	enfmpt2_2 $e |- F/_ z C $.
	nfmpt2 $p |- F/_ z ( x e. A , y e. B |-> C ) $= fnfmpt2_2 fnfmpt2_0 fnfmpt2_1 fnfmpt2_3 fnfmpt2_4 fnfmpt2_5 cmpt2 fnfmpt2_0 sup_set_class fnfmpt2_3 wcel fnfmpt2_1 sup_set_class fnfmpt2_4 wcel wa infmpt2_0 sup_set_class fnfmpt2_5 wceq wa fnfmpt2_0 fnfmpt2_1 infmpt2_0 coprab fnfmpt2_0 fnfmpt2_1 infmpt2_0 fnfmpt2_3 fnfmpt2_4 fnfmpt2_5 df-mpt2 fnfmpt2_0 sup_set_class fnfmpt2_3 wcel fnfmpt2_1 sup_set_class fnfmpt2_4 wcel wa infmpt2_0 sup_set_class fnfmpt2_5 wceq wa fnfmpt2_0 fnfmpt2_1 infmpt2_0 fnfmpt2_2 fnfmpt2_0 sup_set_class fnfmpt2_3 wcel fnfmpt2_1 sup_set_class fnfmpt2_4 wcel wa infmpt2_0 sup_set_class fnfmpt2_5 wceq fnfmpt2_2 fnfmpt2_0 sup_set_class fnfmpt2_3 wcel fnfmpt2_1 sup_set_class fnfmpt2_4 wcel fnfmpt2_2 fnfmpt2_2 fnfmpt2_0 fnfmpt2_3 enfmpt2_0 nfcri fnfmpt2_2 fnfmpt2_1 fnfmpt2_4 enfmpt2_1 nfcri nfan fnfmpt2_2 infmpt2_0 sup_set_class fnfmpt2_5 enfmpt2_2 nfeq2 nfan nfoprab nfcxfr $.
$}
$( /* Two ways to state the domain of an operation.  (Contributed by FL,
       24-Jan-2010.) */

$)
${
	$d x y z $.
	foprab4_0 $f wff ph $.
	foprab4_1 $f set x $.
	foprab4_2 $f set y $.
	foprab4_3 $f set z $.
	foprab4_4 $f class A $.
	foprab4_5 $f class B $.
	oprab4 $p |- { <. <. x , y >. , z >. | ( <. x , y >. e. ( A X. B ) /\ ph ) } = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $= foprab4_1 sup_set_class foprab4_2 sup_set_class cop foprab4_4 foprab4_5 cxp wcel foprab4_0 wa foprab4_1 sup_set_class foprab4_4 wcel foprab4_2 sup_set_class foprab4_5 wcel wa foprab4_0 wa foprab4_1 foprab4_2 foprab4_3 foprab4_1 sup_set_class foprab4_2 sup_set_class cop foprab4_4 foprab4_5 cxp wcel foprab4_1 sup_set_class foprab4_4 wcel foprab4_2 sup_set_class foprab4_5 wcel wa foprab4_0 foprab4_1 sup_set_class foprab4_2 sup_set_class foprab4_4 foprab4_5 opelxp anbi1i oprabbii $.
$}
$( /* Rule used to change first bound variable in an operation abstraction,
       using implicit substitution.  (Contributed by NM, 20-Dec-2008.)
       (Revised by Mario Carneiro, 5-Dec-2016.) */

$)
${
	$d x y z w v $.
	$d v ph $.
	$d v ps $.
	icbvoprab1_0 $f set v $.
	fcbvoprab1_0 $f wff ph $.
	fcbvoprab1_1 $f wff ps $.
	fcbvoprab1_2 $f set x $.
	fcbvoprab1_3 $f set y $.
	fcbvoprab1_4 $f set z $.
	fcbvoprab1_5 $f set w $.
	ecbvoprab1_0 $e |- F/ w ph $.
	ecbvoprab1_1 $e |- F/ x ps $.
	ecbvoprab1_2 $e |- ( x = w -> ( ph <-> ps ) ) $.
	cbvoprab1 $p |- { <. <. x , y >. , z >. | ph } = { <. <. w , y >. , z >. | ps } $= icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_0 wa fcbvoprab1_3 wex fcbvoprab1_2 wex icbvoprab1_0 fcbvoprab1_4 copab icbvoprab1_0 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_1 wa fcbvoprab1_3 wex fcbvoprab1_5 wex icbvoprab1_0 fcbvoprab1_4 copab fcbvoprab1_0 fcbvoprab1_2 fcbvoprab1_3 fcbvoprab1_4 coprab fcbvoprab1_1 fcbvoprab1_5 fcbvoprab1_3 fcbvoprab1_4 coprab icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_0 wa fcbvoprab1_3 wex fcbvoprab1_2 wex icbvoprab1_0 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_1 wa fcbvoprab1_3 wex fcbvoprab1_5 wex icbvoprab1_0 fcbvoprab1_4 icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_0 wa fcbvoprab1_3 wex icbvoprab1_0 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_1 wa fcbvoprab1_3 wex fcbvoprab1_2 fcbvoprab1_5 icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_0 wa fcbvoprab1_5 fcbvoprab1_3 icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_0 fcbvoprab1_5 icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_5 nfv ecbvoprab1_0 nfan nfex icbvoprab1_0 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_1 wa fcbvoprab1_2 fcbvoprab1_3 icbvoprab1_0 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_1 fcbvoprab1_2 icbvoprab1_0 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_2 nfv ecbvoprab1_1 nfan nfex fcbvoprab1_2 sup_set_class fcbvoprab1_5 sup_set_class wceq icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_0 wa icbvoprab1_0 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_1 wa fcbvoprab1_3 fcbvoprab1_2 sup_set_class fcbvoprab1_5 sup_set_class wceq icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop wceq icbvoprab1_0 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop wceq fcbvoprab1_0 fcbvoprab1_1 fcbvoprab1_2 sup_set_class fcbvoprab1_5 sup_set_class wceq fcbvoprab1_2 sup_set_class fcbvoprab1_3 sup_set_class cop fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class cop icbvoprab1_0 sup_set_class fcbvoprab1_2 sup_set_class fcbvoprab1_5 sup_set_class fcbvoprab1_3 sup_set_class opeq1 eqeq2d ecbvoprab1_2 anbi12d exbidv cbvex opabbii fcbvoprab1_0 fcbvoprab1_2 fcbvoprab1_3 fcbvoprab1_4 icbvoprab1_0 dfoprab2 fcbvoprab1_1 fcbvoprab1_5 fcbvoprab1_3 fcbvoprab1_4 icbvoprab1_0 dfoprab2 3eqtr4i $.
$}
$( /* Change the second bound variable in an operation abstraction.
       (Contributed by Jeff Madsen, 11-Jun-2010.)  (Revised by Mario Carneiro,
       11-Dec-2016.) */

$)
${
	$d v w x y z $.
	$d ph v $.
	$d ps v $.
	icbvoprab2_0 $f set v $.
	fcbvoprab2_0 $f wff ph $.
	fcbvoprab2_1 $f wff ps $.
	fcbvoprab2_2 $f set x $.
	fcbvoprab2_3 $f set y $.
	fcbvoprab2_4 $f set z $.
	fcbvoprab2_5 $f set w $.
	ecbvoprab2_0 $e |- F/ w ph $.
	ecbvoprab2_1 $e |- F/ y ps $.
	ecbvoprab2_2 $e |- ( y = w -> ( ph <-> ps ) ) $.
	cbvoprab2 $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , w >. , z >. | ps } $= icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_0 wa fcbvoprab2_4 wex fcbvoprab2_3 wex fcbvoprab2_2 wex icbvoprab2_0 cab icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_1 wa fcbvoprab2_4 wex fcbvoprab2_5 wex fcbvoprab2_2 wex icbvoprab2_0 cab fcbvoprab2_0 fcbvoprab2_2 fcbvoprab2_3 fcbvoprab2_4 coprab fcbvoprab2_1 fcbvoprab2_2 fcbvoprab2_5 fcbvoprab2_4 coprab icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_0 wa fcbvoprab2_4 wex fcbvoprab2_3 wex fcbvoprab2_2 wex icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_1 wa fcbvoprab2_4 wex fcbvoprab2_5 wex fcbvoprab2_2 wex icbvoprab2_0 icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_0 wa fcbvoprab2_4 wex fcbvoprab2_3 wex icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_1 wa fcbvoprab2_4 wex fcbvoprab2_5 wex fcbvoprab2_2 icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_0 wa fcbvoprab2_4 wex icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_1 wa fcbvoprab2_4 wex fcbvoprab2_3 fcbvoprab2_5 icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_0 wa fcbvoprab2_5 fcbvoprab2_4 icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_0 fcbvoprab2_5 icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_5 nfv ecbvoprab2_0 nfan nfex icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_1 wa fcbvoprab2_3 fcbvoprab2_4 icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_1 fcbvoprab2_3 icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_3 nfv ecbvoprab2_1 nfan nfex fcbvoprab2_3 sup_set_class fcbvoprab2_5 sup_set_class wceq icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_0 wa icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_1 wa fcbvoprab2_4 fcbvoprab2_3 sup_set_class fcbvoprab2_5 sup_set_class wceq icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq icbvoprab2_0 sup_set_class fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop wceq fcbvoprab2_0 fcbvoprab2_1 fcbvoprab2_3 sup_set_class fcbvoprab2_5 sup_set_class wceq fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_4 sup_set_class cop fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class cop icbvoprab2_0 sup_set_class fcbvoprab2_3 sup_set_class fcbvoprab2_5 sup_set_class wceq fcbvoprab2_2 sup_set_class fcbvoprab2_3 sup_set_class cop fcbvoprab2_2 sup_set_class fcbvoprab2_5 sup_set_class cop fcbvoprab2_4 sup_set_class fcbvoprab2_3 sup_set_class fcbvoprab2_5 sup_set_class fcbvoprab2_2 sup_set_class opeq2 opeq1d eqeq2d ecbvoprab2_2 anbi12d exbidv cbvex exbii abbii fcbvoprab2_0 fcbvoprab2_2 fcbvoprab2_3 fcbvoprab2_4 icbvoprab2_0 df-oprab fcbvoprab2_1 fcbvoprab2_2 fcbvoprab2_5 fcbvoprab2_4 icbvoprab2_0 df-oprab 3eqtr4i $.
$}
$( /* Rule used to change first two bound variables in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       21-Feb-2004.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) */

$)
${
	$d x y z w v u $.
	$d u ph $.
	$d u ps $.
	icbvoprab12_0 $f set u $.
	fcbvoprab12_0 $f wff ph $.
	fcbvoprab12_1 $f wff ps $.
	fcbvoprab12_2 $f set x $.
	fcbvoprab12_3 $f set y $.
	fcbvoprab12_4 $f set z $.
	fcbvoprab12_5 $f set w $.
	fcbvoprab12_6 $f set v $.
	ecbvoprab12_0 $e |- F/ w ph $.
	ecbvoprab12_1 $e |- F/ v ph $.
	ecbvoprab12_2 $e |- F/ x ps $.
	ecbvoprab12_3 $e |- F/ y ps $.
	ecbvoprab12_4 $e |- ( ( x = w /\ y = v ) -> ( ph <-> ps ) ) $.
	cbvoprab12 $p |- { <. <. x , y >. , z >. | ph } = { <. <. w , v >. , z >. | ps } $= icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop wceq fcbvoprab12_0 wa fcbvoprab12_3 wex fcbvoprab12_2 wex icbvoprab12_0 fcbvoprab12_4 copab icbvoprab12_0 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop wceq fcbvoprab12_1 wa fcbvoprab12_6 wex fcbvoprab12_5 wex icbvoprab12_0 fcbvoprab12_4 copab fcbvoprab12_0 fcbvoprab12_2 fcbvoprab12_3 fcbvoprab12_4 coprab fcbvoprab12_1 fcbvoprab12_5 fcbvoprab12_6 fcbvoprab12_4 coprab icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop wceq fcbvoprab12_0 wa fcbvoprab12_3 wex fcbvoprab12_2 wex icbvoprab12_0 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop wceq fcbvoprab12_1 wa fcbvoprab12_6 wex fcbvoprab12_5 wex icbvoprab12_0 fcbvoprab12_4 icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop wceq fcbvoprab12_0 wa icbvoprab12_0 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop wceq fcbvoprab12_1 wa fcbvoprab12_2 fcbvoprab12_3 fcbvoprab12_5 fcbvoprab12_6 icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop wceq fcbvoprab12_0 fcbvoprab12_5 icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop wceq fcbvoprab12_5 nfv ecbvoprab12_0 nfan icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop wceq fcbvoprab12_0 fcbvoprab12_6 icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop wceq fcbvoprab12_6 nfv ecbvoprab12_1 nfan icbvoprab12_0 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop wceq fcbvoprab12_1 fcbvoprab12_2 icbvoprab12_0 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop wceq fcbvoprab12_2 nfv ecbvoprab12_2 nfan icbvoprab12_0 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop wceq fcbvoprab12_1 fcbvoprab12_3 icbvoprab12_0 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop wceq fcbvoprab12_3 nfv ecbvoprab12_3 nfan fcbvoprab12_2 sup_set_class fcbvoprab12_5 sup_set_class wceq fcbvoprab12_3 sup_set_class fcbvoprab12_6 sup_set_class wceq wa icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop wceq icbvoprab12_0 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop wceq fcbvoprab12_0 fcbvoprab12_1 fcbvoprab12_2 sup_set_class fcbvoprab12_5 sup_set_class wceq fcbvoprab12_3 sup_set_class fcbvoprab12_6 sup_set_class wceq wa fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class cop fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class cop icbvoprab12_0 sup_set_class fcbvoprab12_2 sup_set_class fcbvoprab12_3 sup_set_class fcbvoprab12_5 sup_set_class fcbvoprab12_6 sup_set_class opeq12 eqeq2d ecbvoprab12_4 anbi12d cbvex2 opabbii fcbvoprab12_0 fcbvoprab12_2 fcbvoprab12_3 fcbvoprab12_4 icbvoprab12_0 dfoprab2 fcbvoprab12_1 fcbvoprab12_5 fcbvoprab12_6 fcbvoprab12_4 icbvoprab12_0 dfoprab2 3eqtr4i $.
$}
$( /* Rule used to change first two bound variables in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       8-Oct-2004.) */

$)
${
	$d x y z w v $.
	$d w v ph $.
	$d x y ps $.
	fcbvoprab12v_0 $f wff ph $.
	fcbvoprab12v_1 $f wff ps $.
	fcbvoprab12v_2 $f set x $.
	fcbvoprab12v_3 $f set y $.
	fcbvoprab12v_4 $f set z $.
	fcbvoprab12v_5 $f set w $.
	fcbvoprab12v_6 $f set v $.
	ecbvoprab12v_0 $e |- ( ( x = w /\ y = v ) -> ( ph <-> ps ) ) $.
	cbvoprab12v $p |- { <. <. x , y >. , z >. | ph } = { <. <. w , v >. , z >. | ps } $= fcbvoprab12v_0 fcbvoprab12v_1 fcbvoprab12v_2 fcbvoprab12v_3 fcbvoprab12v_4 fcbvoprab12v_5 fcbvoprab12v_6 fcbvoprab12v_0 fcbvoprab12v_5 nfv fcbvoprab12v_0 fcbvoprab12v_6 nfv fcbvoprab12v_1 fcbvoprab12v_2 nfv fcbvoprab12v_1 fcbvoprab12v_3 nfv ecbvoprab12v_0 cbvoprab12 $.
$}
$( /* Rule used to change the third bound variable in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       22-Aug-2013.) */

$)
${
	$d x z w v $.
	$d y z w v $.
	$d v ph $.
	$d v ps $.
	icbvoprab3_0 $f set v $.
	fcbvoprab3_0 $f wff ph $.
	fcbvoprab3_1 $f wff ps $.
	fcbvoprab3_2 $f set x $.
	fcbvoprab3_3 $f set y $.
	fcbvoprab3_4 $f set z $.
	fcbvoprab3_5 $f set w $.
	ecbvoprab3_0 $e |- F/ w ph $.
	ecbvoprab3_1 $e |- F/ z ps $.
	ecbvoprab3_2 $e |- ( z = w -> ( ph <-> ps ) ) $.
	cbvoprab3 $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , w >. | ps } $= icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_0 wa fcbvoprab3_3 wex fcbvoprab3_2 wex icbvoprab3_0 fcbvoprab3_4 copab icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_1 wa fcbvoprab3_3 wex fcbvoprab3_2 wex icbvoprab3_0 fcbvoprab3_5 copab fcbvoprab3_0 fcbvoprab3_2 fcbvoprab3_3 fcbvoprab3_4 coprab fcbvoprab3_1 fcbvoprab3_2 fcbvoprab3_3 fcbvoprab3_5 coprab icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_0 wa fcbvoprab3_3 wex fcbvoprab3_2 wex icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_1 wa fcbvoprab3_3 wex fcbvoprab3_2 wex icbvoprab3_0 fcbvoprab3_4 fcbvoprab3_5 icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_0 wa fcbvoprab3_3 wex fcbvoprab3_5 fcbvoprab3_2 icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_0 wa fcbvoprab3_5 fcbvoprab3_3 icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_0 fcbvoprab3_5 icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_5 nfv ecbvoprab3_0 nfan nfex nfex icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_1 wa fcbvoprab3_3 wex fcbvoprab3_4 fcbvoprab3_2 icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_1 wa fcbvoprab3_4 fcbvoprab3_3 icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_1 fcbvoprab3_4 icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_4 nfv ecbvoprab3_1 nfan nfex nfex fcbvoprab3_4 sup_set_class fcbvoprab3_5 sup_set_class wceq icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_0 wa icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq fcbvoprab3_1 wa fcbvoprab3_2 fcbvoprab3_3 fcbvoprab3_4 sup_set_class fcbvoprab3_5 sup_set_class wceq fcbvoprab3_0 fcbvoprab3_1 icbvoprab3_0 sup_set_class fcbvoprab3_2 sup_set_class fcbvoprab3_3 sup_set_class cop wceq ecbvoprab3_2 anbi2d 2exbidv cbvopab2 fcbvoprab3_0 fcbvoprab3_2 fcbvoprab3_3 fcbvoprab3_4 icbvoprab3_0 dfoprab2 fcbvoprab3_1 fcbvoprab3_2 fcbvoprab3_3 fcbvoprab3_5 icbvoprab3_0 dfoprab2 3eqtr4i $.
$}
$( /* Rule used to change the third bound variable in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       8-Oct-2004.)  (Revised by David Abernethy, 19-Jun-2012.) */

$)
${
	$d x z w $.
	$d y z w $.
	$d w ph $.
	$d z ps $.
	fcbvoprab3v_0 $f wff ph $.
	fcbvoprab3v_1 $f wff ps $.
	fcbvoprab3v_2 $f set x $.
	fcbvoprab3v_3 $f set y $.
	fcbvoprab3v_4 $f set z $.
	fcbvoprab3v_5 $f set w $.
	ecbvoprab3v_0 $e |- ( z = w -> ( ph <-> ps ) ) $.
	cbvoprab3v $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , w >. | ps } $= fcbvoprab3v_0 fcbvoprab3v_1 fcbvoprab3v_2 fcbvoprab3v_3 fcbvoprab3v_4 fcbvoprab3v_5 fcbvoprab3v_0 fcbvoprab3v_5 nfv fcbvoprab3v_1 fcbvoprab3v_4 nfv ecbvoprab3v_0 cbvoprab3 $.
$}
$( /* Rule to change the bound variable in a maps-to function, using implicit
       substitution.  This version of ~ cbvmpt2 allows ` B ` to be a function
       of ` x ` .  (Contributed by NM, 29-Dec-2014.) */

$)
${
	$d u w x y z $.
	$d u w x y z A $.
	$d u w B $.
	$d u C $.
	$d u y D $.
	$d u E $.
	icbvmpt2x_0 $f set u $.
	fcbvmpt2x_0 $f set x $.
	fcbvmpt2x_1 $f set y $.
	fcbvmpt2x_2 $f set z $.
	fcbvmpt2x_3 $f set w $.
	fcbvmpt2x_4 $f class A $.
	fcbvmpt2x_5 $f class B $.
	fcbvmpt2x_6 $f class C $.
	fcbvmpt2x_7 $f class D $.
	fcbvmpt2x_8 $f class E $.
	ecbvmpt2x_0 $e |- F/_ z B $.
	ecbvmpt2x_1 $e |- F/_ x D $.
	ecbvmpt2x_2 $e |- F/_ z C $.
	ecbvmpt2x_3 $e |- F/_ w C $.
	ecbvmpt2x_4 $e |- F/_ x E $.
	ecbvmpt2x_5 $e |- F/_ y E $.
	ecbvmpt2x_6 $e |- ( x = z -> B = D ) $.
	ecbvmpt2x_7 $e |- ( ( x = z /\ y = w ) -> C = E ) $.
	cbvmpt2x $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. D |-> E ) $= fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_6 wceq wa fcbvmpt2x_0 fcbvmpt2x_1 icbvmpt2x_0 coprab fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_8 wceq wa fcbvmpt2x_2 fcbvmpt2x_3 icbvmpt2x_0 coprab fcbvmpt2x_0 fcbvmpt2x_1 fcbvmpt2x_4 fcbvmpt2x_5 fcbvmpt2x_6 cmpt2 fcbvmpt2x_2 fcbvmpt2x_3 fcbvmpt2x_4 fcbvmpt2x_7 fcbvmpt2x_8 cmpt2 fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_6 wceq wa fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_8 wceq wa fcbvmpt2x_0 fcbvmpt2x_1 icbvmpt2x_0 fcbvmpt2x_2 fcbvmpt2x_3 fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_6 wceq fcbvmpt2x_2 fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel fcbvmpt2x_2 fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_2 nfv fcbvmpt2x_2 fcbvmpt2x_1 fcbvmpt2x_5 ecbvmpt2x_0 nfcri nfan fcbvmpt2x_2 icbvmpt2x_0 sup_set_class fcbvmpt2x_6 ecbvmpt2x_2 nfeq2 nfan fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_6 wceq fcbvmpt2x_3 fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel fcbvmpt2x_3 fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_3 nfv fcbvmpt2x_3 fcbvmpt2x_1 fcbvmpt2x_5 fcbvmpt2x_3 fcbvmpt2x_5 nfcv nfcri nfan fcbvmpt2x_3 icbvmpt2x_0 sup_set_class fcbvmpt2x_6 ecbvmpt2x_3 nfeq2 nfan fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_8 wceq fcbvmpt2x_0 fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel fcbvmpt2x_0 fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_0 nfv fcbvmpt2x_0 fcbvmpt2x_3 fcbvmpt2x_7 ecbvmpt2x_1 nfcri nfan fcbvmpt2x_0 icbvmpt2x_0 sup_set_class fcbvmpt2x_8 ecbvmpt2x_4 nfeq2 nfan fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_8 wceq fcbvmpt2x_1 fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel wa fcbvmpt2x_1 nfv fcbvmpt2x_1 icbvmpt2x_0 sup_set_class fcbvmpt2x_8 ecbvmpt2x_5 nfeq2 nfan fcbvmpt2x_0 sup_set_class fcbvmpt2x_2 sup_set_class wceq fcbvmpt2x_1 sup_set_class fcbvmpt2x_3 sup_set_class wceq wa fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel wa fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel wa icbvmpt2x_0 sup_set_class fcbvmpt2x_6 wceq icbvmpt2x_0 sup_set_class fcbvmpt2x_8 wceq fcbvmpt2x_0 sup_set_class fcbvmpt2x_2 sup_set_class wceq fcbvmpt2x_1 sup_set_class fcbvmpt2x_3 sup_set_class wceq wa fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel fcbvmpt2x_0 sup_set_class fcbvmpt2x_2 sup_set_class wceq fcbvmpt2x_0 sup_set_class fcbvmpt2x_4 wcel fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 wcel wb fcbvmpt2x_1 sup_set_class fcbvmpt2x_3 sup_set_class wceq fcbvmpt2x_0 sup_set_class fcbvmpt2x_2 sup_set_class fcbvmpt2x_4 eleq1 adantr fcbvmpt2x_0 sup_set_class fcbvmpt2x_2 sup_set_class wceq fcbvmpt2x_1 sup_set_class fcbvmpt2x_5 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_7 wcel fcbvmpt2x_1 sup_set_class fcbvmpt2x_3 sup_set_class wceq fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 wcel fcbvmpt2x_0 sup_set_class fcbvmpt2x_2 sup_set_class wceq fcbvmpt2x_5 fcbvmpt2x_7 fcbvmpt2x_1 sup_set_class ecbvmpt2x_6 eleq2d fcbvmpt2x_1 sup_set_class fcbvmpt2x_3 sup_set_class fcbvmpt2x_7 eleq1 sylan9bb anbi12d fcbvmpt2x_0 sup_set_class fcbvmpt2x_2 sup_set_class wceq fcbvmpt2x_1 sup_set_class fcbvmpt2x_3 sup_set_class wceq wa fcbvmpt2x_6 fcbvmpt2x_8 icbvmpt2x_0 sup_set_class ecbvmpt2x_7 eqeq2d anbi12d cbvoprab12 fcbvmpt2x_0 fcbvmpt2x_1 icbvmpt2x_0 fcbvmpt2x_4 fcbvmpt2x_5 fcbvmpt2x_6 df-mpt2 fcbvmpt2x_2 fcbvmpt2x_3 icbvmpt2x_0 fcbvmpt2x_4 fcbvmpt2x_7 fcbvmpt2x_8 df-mpt2 3eqtr4i $.
$}
$( /* Rule to change the bound variable in a maps-to function, using implicit
       substitution.  (Contributed by NM, 17-Dec-2013.) */

$)
${
	$d w x y z A $.
	$d w x y z B $.
	fcbvmpt2_0 $f set x $.
	fcbvmpt2_1 $f set y $.
	fcbvmpt2_2 $f set z $.
	fcbvmpt2_3 $f set w $.
	fcbvmpt2_4 $f class A $.
	fcbvmpt2_5 $f class B $.
	fcbvmpt2_6 $f class C $.
	fcbvmpt2_7 $f class D $.
	ecbvmpt2_0 $e |- F/_ z C $.
	ecbvmpt2_1 $e |- F/_ w C $.
	ecbvmpt2_2 $e |- F/_ x D $.
	ecbvmpt2_3 $e |- F/_ y D $.
	ecbvmpt2_4 $e |- ( ( x = z /\ y = w ) -> C = D ) $.
	cbvmpt2 $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. B |-> D ) $= fcbvmpt2_0 fcbvmpt2_1 fcbvmpt2_2 fcbvmpt2_3 fcbvmpt2_4 fcbvmpt2_5 fcbvmpt2_6 fcbvmpt2_5 fcbvmpt2_7 fcbvmpt2_2 fcbvmpt2_5 nfcv fcbvmpt2_0 fcbvmpt2_5 nfcv ecbvmpt2_0 ecbvmpt2_1 ecbvmpt2_2 ecbvmpt2_3 fcbvmpt2_0 sup_set_class fcbvmpt2_2 sup_set_class wceq fcbvmpt2_5 eqidd ecbvmpt2_4 cbvmpt2x $.
$}
$( /* Rule to change the bound variable in a maps-to function, using implicit
       substitution.  With a longer proof analogous to ~ cbvmpt , some distinct
       variable requirements could be eliminated.  (Contributed by NM,
       11-Jun-2013.) */

$)
${
	$d w x y z A $.
	$d w x y z B $.
	$d w z C $.
	$d x y D $.
	fcbvmpt2v_0 $f set x $.
	fcbvmpt2v_1 $f set y $.
	fcbvmpt2v_2 $f set z $.
	fcbvmpt2v_3 $f set w $.
	fcbvmpt2v_4 $f class A $.
	fcbvmpt2v_5 $f class B $.
	fcbvmpt2v_6 $f class C $.
	fcbvmpt2v_7 $f class D $.
	fcbvmpt2v_8 $f class E $.
	ecbvmpt2v_0 $e |- ( x = z -> C = E ) $.
	ecbvmpt2v_1 $e |- ( y = w -> E = D ) $.
	cbvmpt2v $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. B |-> D ) $= fcbvmpt2v_0 fcbvmpt2v_1 fcbvmpt2v_2 fcbvmpt2v_3 fcbvmpt2v_4 fcbvmpt2v_5 fcbvmpt2v_6 fcbvmpt2v_7 fcbvmpt2v_2 fcbvmpt2v_6 nfcv fcbvmpt2v_3 fcbvmpt2v_6 nfcv fcbvmpt2v_0 fcbvmpt2v_7 nfcv fcbvmpt2v_1 fcbvmpt2v_7 nfcv fcbvmpt2v_0 sup_set_class fcbvmpt2v_2 sup_set_class wceq fcbvmpt2v_1 sup_set_class fcbvmpt2v_3 sup_set_class wceq fcbvmpt2v_6 fcbvmpt2v_8 fcbvmpt2v_7 ecbvmpt2v_0 ecbvmpt2v_1 sylan9eq cbvmpt2 $.
$}
$( /* Eliminate a hypothesis which is a predicate expressing membership in the
       result of an operator (deduction version).  See ~ ghomgrplem for an
       example of its use.  (Contributed by Paul Chapman, 25-Mar-2008.) */

$)
${
	felimdelov_0 $f wff ph $.
	felimdelov_1 $f class A $.
	felimdelov_2 $f class B $.
	felimdelov_3 $f class C $.
	felimdelov_4 $f class F $.
	felimdelov_5 $f class X $.
	felimdelov_6 $f class Y $.
	felimdelov_7 $f class Z $.
	eelimdelov_0 $e |- ( ph -> C e. ( A F B ) ) $.
	eelimdelov_1 $e |- Z e. ( X F Y ) $.
	elimdelov $p |- if ( ph , C , Z ) e. ( if ( ph , A , X ) F if ( ph , B , Y ) ) $= felimdelov_0 felimdelov_0 felimdelov_3 felimdelov_7 cif felimdelov_0 felimdelov_1 felimdelov_5 cif felimdelov_0 felimdelov_2 felimdelov_6 cif felimdelov_4 co wcel felimdelov_0 felimdelov_0 felimdelov_3 felimdelov_7 cif felimdelov_1 felimdelov_2 felimdelov_4 co felimdelov_0 felimdelov_1 felimdelov_5 cif felimdelov_0 felimdelov_2 felimdelov_6 cif felimdelov_4 co felimdelov_0 felimdelov_0 felimdelov_3 felimdelov_7 cif felimdelov_3 felimdelov_1 felimdelov_2 felimdelov_4 co felimdelov_0 felimdelov_3 felimdelov_7 iftrue eelimdelov_0 eqeltrd felimdelov_0 felimdelov_0 felimdelov_1 felimdelov_5 cif felimdelov_1 felimdelov_0 felimdelov_2 felimdelov_6 cif felimdelov_2 felimdelov_4 felimdelov_0 felimdelov_1 felimdelov_5 iftrue felimdelov_0 felimdelov_2 felimdelov_6 iftrue oveq12d eleqtrrd felimdelov_0 wn felimdelov_0 felimdelov_3 felimdelov_7 cif felimdelov_5 felimdelov_6 felimdelov_4 co felimdelov_0 felimdelov_1 felimdelov_5 cif felimdelov_0 felimdelov_2 felimdelov_6 cif felimdelov_4 co felimdelov_0 wn felimdelov_0 felimdelov_3 felimdelov_7 cif felimdelov_7 felimdelov_5 felimdelov_6 felimdelov_4 co felimdelov_0 felimdelov_3 felimdelov_7 iffalse eelimdelov_1 syl6eqel felimdelov_0 wn felimdelov_0 felimdelov_1 felimdelov_5 cif felimdelov_5 felimdelov_0 felimdelov_2 felimdelov_6 cif felimdelov_6 felimdelov_4 felimdelov_0 felimdelov_1 felimdelov_5 iffalse felimdelov_0 felimdelov_2 felimdelov_6 iffalse oveq12d eleqtrrd pm2.61i $.
$}
$( /* The domain of an operation class abstraction.  (Contributed by NM,
       17-Mar-1995.)  (Revised by David Abernethy, 19-Jun-2012.) */

$)
${
	$d x z w $.
	$d y z w $.
	$d w ph $.
	idmoprab_0 $f set w $.
	fdmoprab_0 $f wff ph $.
	fdmoprab_1 $f set x $.
	fdmoprab_2 $f set y $.
	fdmoprab_3 $f set z $.
	dmoprab $p |- dom { <. <. x , y >. , z >. | ph } = { <. x , y >. | E. z ph } $= fdmoprab_0 fdmoprab_1 fdmoprab_2 fdmoprab_3 coprab cdm idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_2 wex fdmoprab_1 wex idmoprab_0 fdmoprab_3 copab cdm idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_2 wex fdmoprab_1 wex fdmoprab_3 wex idmoprab_0 cab fdmoprab_0 fdmoprab_3 wex fdmoprab_1 fdmoprab_2 copab fdmoprab_0 fdmoprab_1 fdmoprab_2 fdmoprab_3 coprab idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_2 wex fdmoprab_1 wex idmoprab_0 fdmoprab_3 copab fdmoprab_0 fdmoprab_1 fdmoprab_2 fdmoprab_3 idmoprab_0 dfoprab2 dmeqi idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_2 wex fdmoprab_1 wex idmoprab_0 fdmoprab_3 dmopab idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_2 wex fdmoprab_1 wex fdmoprab_3 wex idmoprab_0 cab idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 fdmoprab_3 wex wa fdmoprab_2 wex fdmoprab_1 wex idmoprab_0 cab fdmoprab_0 fdmoprab_3 wex fdmoprab_1 fdmoprab_2 copab idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_2 wex fdmoprab_1 wex fdmoprab_3 wex idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 fdmoprab_3 wex wa fdmoprab_2 wex fdmoprab_1 wex idmoprab_0 idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_2 wex fdmoprab_1 wex fdmoprab_3 wex idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_3 wex fdmoprab_2 wex fdmoprab_1 wex idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 fdmoprab_3 wex wa fdmoprab_2 wex fdmoprab_1 wex idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_3 fdmoprab_1 fdmoprab_2 exrot3 idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 wa fdmoprab_3 wex idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 fdmoprab_3 wex wa fdmoprab_1 fdmoprab_2 idmoprab_0 sup_set_class fdmoprab_1 sup_set_class fdmoprab_2 sup_set_class cop wceq fdmoprab_0 fdmoprab_3 19.42v 2exbii bitri abbii fdmoprab_0 fdmoprab_3 wex fdmoprab_1 fdmoprab_2 idmoprab_0 df-opab eqtr4i 3eqtri $.
$}
$( /* The domain of an operation class abstraction.  (Contributed by NM,
       24-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	fdmoprabss_0 $f wff ph $.
	fdmoprabss_1 $f set x $.
	fdmoprabss_2 $f set y $.
	fdmoprabss_3 $f set z $.
	fdmoprabss_4 $f class A $.
	fdmoprabss_5 $f class B $.
	dmoprabss $p |- dom { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } C_ ( A X. B ) $= fdmoprabss_1 sup_set_class fdmoprabss_4 wcel fdmoprabss_2 sup_set_class fdmoprabss_5 wcel wa fdmoprabss_0 wa fdmoprabss_1 fdmoprabss_2 fdmoprabss_3 coprab cdm fdmoprabss_1 sup_set_class fdmoprabss_4 wcel fdmoprabss_2 sup_set_class fdmoprabss_5 wcel wa fdmoprabss_0 wa fdmoprabss_3 wex fdmoprabss_1 fdmoprabss_2 copab fdmoprabss_4 fdmoprabss_5 cxp fdmoprabss_1 sup_set_class fdmoprabss_4 wcel fdmoprabss_2 sup_set_class fdmoprabss_5 wcel wa fdmoprabss_0 wa fdmoprabss_1 fdmoprabss_2 fdmoprabss_3 dmoprab fdmoprabss_1 sup_set_class fdmoprabss_4 wcel fdmoprabss_2 sup_set_class fdmoprabss_5 wcel wa fdmoprabss_0 wa fdmoprabss_3 wex fdmoprabss_1 fdmoprabss_2 copab fdmoprabss_1 sup_set_class fdmoprabss_4 wcel fdmoprabss_2 sup_set_class fdmoprabss_5 wcel wa fdmoprabss_0 fdmoprabss_3 wex wa fdmoprabss_1 fdmoprabss_2 copab fdmoprabss_4 fdmoprabss_5 cxp fdmoprabss_1 sup_set_class fdmoprabss_4 wcel fdmoprabss_2 sup_set_class fdmoprabss_5 wcel wa fdmoprabss_0 wa fdmoprabss_3 wex fdmoprabss_1 sup_set_class fdmoprabss_4 wcel fdmoprabss_2 sup_set_class fdmoprabss_5 wcel wa fdmoprabss_0 fdmoprabss_3 wex wa fdmoprabss_1 fdmoprabss_2 fdmoprabss_1 sup_set_class fdmoprabss_4 wcel fdmoprabss_2 sup_set_class fdmoprabss_5 wcel wa fdmoprabss_0 fdmoprabss_3 19.42v opabbii fdmoprabss_0 fdmoprabss_3 wex fdmoprabss_1 fdmoprabss_2 fdmoprabss_4 fdmoprabss_5 opabssxp eqsstri eqsstri $.
$}
$( /* The range of an operation class abstraction.  (Contributed by NM,
       30-Aug-2004.)  (Revised by David Abernethy, 19-Apr-2013.) */

$)
${
	$d x z w $.
	$d y z w $.
	$d w ph $.
	irnoprab_0 $f set w $.
	frnoprab_0 $f wff ph $.
	frnoprab_1 $f set x $.
	frnoprab_2 $f set y $.
	frnoprab_3 $f set z $.
	rnoprab $p |- ran { <. <. x , y >. , z >. | ph } = { z | E. x E. y ph } $= frnoprab_0 frnoprab_1 frnoprab_2 frnoprab_3 coprab crn irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa frnoprab_2 wex frnoprab_1 wex irnoprab_0 frnoprab_3 copab crn irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa frnoprab_2 wex frnoprab_1 wex irnoprab_0 wex frnoprab_3 cab frnoprab_0 frnoprab_2 wex frnoprab_1 wex frnoprab_3 cab frnoprab_0 frnoprab_1 frnoprab_2 frnoprab_3 coprab irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa frnoprab_2 wex frnoprab_1 wex irnoprab_0 frnoprab_3 copab frnoprab_0 frnoprab_1 frnoprab_2 frnoprab_3 irnoprab_0 dfoprab2 rneqi irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa frnoprab_2 wex frnoprab_1 wex irnoprab_0 frnoprab_3 rnopab irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa frnoprab_2 wex frnoprab_1 wex irnoprab_0 wex frnoprab_0 frnoprab_2 wex frnoprab_1 wex frnoprab_3 irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa frnoprab_2 wex frnoprab_1 wex irnoprab_0 wex irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa irnoprab_0 wex frnoprab_2 wex frnoprab_1 wex frnoprab_0 frnoprab_2 wex frnoprab_1 wex irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa irnoprab_0 frnoprab_1 frnoprab_2 exrot3 irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa irnoprab_0 wex frnoprab_0 frnoprab_1 frnoprab_2 irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 wa irnoprab_0 wex irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq irnoprab_0 wex frnoprab_0 irnoprab_0 frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop frnoprab_1 sup_set_class frnoprab_2 sup_set_class opex isseti irnoprab_0 sup_set_class frnoprab_1 sup_set_class frnoprab_2 sup_set_class cop wceq frnoprab_0 irnoprab_0 19.41v mpbiran 2exbii bitri abbii 3eqtri $.
$}
$( /* The range of a restricted operation class abstraction.  (Contributed by
       Scott Fenton, 21-Mar-2012.) */

$)
${
	$d A y $.
	$d x y z $.
	frnoprab2_0 $f wff ph $.
	frnoprab2_1 $f set x $.
	frnoprab2_2 $f set y $.
	frnoprab2_3 $f set z $.
	frnoprab2_4 $f class A $.
	frnoprab2_5 $f class B $.
	rnoprab2 $p |- ran { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } = { z | E. x e. A E. y e. B ph } $= frnoprab2_1 sup_set_class frnoprab2_4 wcel frnoprab2_2 sup_set_class frnoprab2_5 wcel wa frnoprab2_0 wa frnoprab2_1 frnoprab2_2 frnoprab2_3 coprab crn frnoprab2_1 sup_set_class frnoprab2_4 wcel frnoprab2_2 sup_set_class frnoprab2_5 wcel wa frnoprab2_0 wa frnoprab2_2 wex frnoprab2_1 wex frnoprab2_3 cab frnoprab2_0 frnoprab2_2 frnoprab2_5 wrex frnoprab2_1 frnoprab2_4 wrex frnoprab2_3 cab frnoprab2_1 sup_set_class frnoprab2_4 wcel frnoprab2_2 sup_set_class frnoprab2_5 wcel wa frnoprab2_0 wa frnoprab2_1 frnoprab2_2 frnoprab2_3 rnoprab frnoprab2_0 frnoprab2_2 frnoprab2_5 wrex frnoprab2_1 frnoprab2_4 wrex frnoprab2_1 sup_set_class frnoprab2_4 wcel frnoprab2_2 sup_set_class frnoprab2_5 wcel wa frnoprab2_0 wa frnoprab2_2 wex frnoprab2_1 wex frnoprab2_3 frnoprab2_0 frnoprab2_1 frnoprab2_2 frnoprab2_4 frnoprab2_5 r2ex abbii eqtr4i $.
$}
$( /* The domain of an operation class abstraction is a relation.
       (Contributed by NM, 17-Mar-1995.) */

$)
${
	$d x y z $.
	freldmoprab_0 $f wff ph $.
	freldmoprab_1 $f set x $.
	freldmoprab_2 $f set y $.
	freldmoprab_3 $f set z $.
	reldmoprab $p |- Rel dom { <. <. x , y >. , z >. | ph } $= freldmoprab_0 freldmoprab_3 wex freldmoprab_1 freldmoprab_2 freldmoprab_0 freldmoprab_1 freldmoprab_2 freldmoprab_3 coprab cdm freldmoprab_0 freldmoprab_1 freldmoprab_2 freldmoprab_3 dmoprab relopabi $.
$}
$( /* Structure of an operation class abstraction.  (Contributed by NM,
       28-Nov-2006.) */

$)
${
	$d x y z $.
	foprabss_0 $f wff ph $.
	foprabss_1 $f set x $.
	foprabss_2 $f set y $.
	foprabss_3 $f set z $.
	oprabss $p |- { <. <. x , y >. , z >. | ph } C_ ( ( _V X. _V ) X. _V ) $= foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab cdm foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab crn cxp cvv cvv cxp cvv cxp foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab wrel foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab cdm foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab crn cxp wss foprabss_0 foprabss_1 foprabss_2 foprabss_3 reloprab foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab relssdmrn ax-mp foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab cdm cvv cvv cxp wss foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab crn cvv wss foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab cdm foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab crn cxp cvv cvv cxp cvv cxp wss foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab cdm wrel foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab cdm cvv cvv cxp wss foprabss_0 foprabss_1 foprabss_2 foprabss_3 reldmoprab foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab cdm df-rel mpbi foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab crn ssv foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab cdm cvv cvv cxp foprabss_0 foprabss_1 foprabss_2 foprabss_3 coprab crn cvv xpss12 mp2an sstri $.
$}
$( /* The law of concretion for operation class abstraction.  Compare
       ~ elopab .  (Contributed by NM, 14-Sep-1999.)  (Unnecessary distinct
       variable restrictions were removed by David Abernethy, 19-Jun-2012.)
       (Revised by Mario Carneiro, 19-Dec-2013.) */

$)
${
	$d x y z w A $.
	$d x y z w B $.
	$d x y z w C $.
	$d w ph $.
	$d x y z w ps $.
	ieloprabga_0 $f set w $.
	feloprabga_0 $f wff ph $.
	feloprabga_1 $f wff ps $.
	feloprabga_2 $f set x $.
	feloprabga_3 $f set y $.
	feloprabga_4 $f set z $.
	feloprabga_5 $f class A $.
	feloprabga_6 $f class B $.
	feloprabga_7 $f class C $.
	feloprabga_8 $f class V $.
	feloprabga_9 $f class W $.
	feloprabga_10 $f class X $.
	eeloprabga_0 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	eloprabga $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( <. <. A , B >. , C >. e. { <. <. x , y >. , z >. | ph } <-> ps ) ) $= feloprabga_5 feloprabga_8 wcel feloprabga_5 cvv wcel feloprabga_6 feloprabga_9 wcel feloprabga_6 cvv wcel feloprabga_7 feloprabga_10 wcel feloprabga_7 cvv wcel feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab wcel feloprabga_1 wb feloprabga_5 feloprabga_8 elex feloprabga_6 feloprabga_9 elex feloprabga_7 feloprabga_10 elex feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab wcel feloprabga_1 wb wi ieloprabga_0 feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_5 feloprabga_6 cop feloprabga_7 opex feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab wcel feloprabga_1 wb feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq wa ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_1 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab wcel feloprabga_1 feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq wa ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_1 wa feloprabga_2 feloprabga_3 feloprabga_4 feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq wa ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_0 wa feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_1 wa feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq wa ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_0 feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq wa ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq wa ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq simpr eqeq1d feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop eqcom feloprabga_2 sup_set_class feloprabga_3 sup_set_class feloprabga_5 feloprabga_6 feloprabga_4 sup_set_class feloprabga_7 feloprabga_2 vex feloprabga_3 vex feloprabga_4 vex otth2 bitri syl6bb anbi1d feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_0 feloprabga_1 eeloprabga_0 pm5.32i syl6bb 3exbidv ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab wcel wb feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex ieloprabga_0 sup_set_class feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab wcel ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab wcel ieloprabga_0 sup_set_class feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab wcel ieloprabga_0 sup_set_class ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex ieloprabga_0 cab wcel ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex ieloprabga_0 cab ieloprabga_0 sup_set_class feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 ieloprabga_0 df-oprab eleq2i ieloprabga_0 sup_set_class feloprabga_2 sup_set_class feloprabga_3 sup_set_class cop feloprabga_4 sup_set_class cop wceq feloprabga_0 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex ieloprabga_0 abid bitr2i ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop feloprabga_0 feloprabga_2 feloprabga_3 feloprabga_4 coprab eleq1 syl5bb adantl feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_1 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_1 wb ieloprabga_0 sup_set_class feloprabga_5 feloprabga_6 cop feloprabga_7 cop wceq feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a feloprabga_1 feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_1 wa feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_1 wa feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_1 feloprabga_5 cvv wcel feloprabga_6 cvv wcel feloprabga_7 cvv wcel w3a feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_2 wex feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_3 wex feloprabga_4 sup_set_class feloprabga_7 wceq feloprabga_4 wex w3a feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_4 wex feloprabga_3 wex feloprabga_2 wex feloprabga_5 cvv wcel feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_2 wex feloprabga_6 cvv wcel feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_3 wex feloprabga_7 cvv wcel feloprabga_4 sup_set_class feloprabga_7 wceq feloprabga_4 wex feloprabga_2 feloprabga_5 cvv elisset feloprabga_3 feloprabga_6 cvv elisset feloprabga_4 feloprabga_7 cvv elisset 3anim123i feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq feloprabga_2 feloprabga_3 feloprabga_4 eeeanv sylibr biantrurd feloprabga_2 sup_set_class feloprabga_5 wceq feloprabga_3 sup_set_class feloprabga_6 wceq feloprabga_4 sup_set_class feloprabga_7 wceq w3a feloprabga_1 feloprabga_2 feloprabga_3 feloprabga_4 19.41vvv syl6rbbr adantr 3bitr3d expcom vtocle syl3an $.
$}
$( /* The law of concretion for operation class abstraction.  Compare
       ~ elopab .  (Contributed by NM, 14-Sep-1999.)  (Revised by David
       Abernethy, 19-Jun-2012.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z th $.
	feloprabg_0 $f wff ph $.
	feloprabg_1 $f wff ps $.
	feloprabg_2 $f wff ch $.
	feloprabg_3 $f wff th $.
	feloprabg_4 $f set x $.
	feloprabg_5 $f set y $.
	feloprabg_6 $f set z $.
	feloprabg_7 $f class A $.
	feloprabg_8 $f class B $.
	feloprabg_9 $f class C $.
	feloprabg_10 $f class V $.
	feloprabg_11 $f class W $.
	feloprabg_12 $f class X $.
	eeloprabg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eeloprabg_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	eeloprabg_2 $e |- ( z = C -> ( ch <-> th ) ) $.
	eloprabg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( <. <. A , B >. , C >. e. { <. <. x , y >. , z >. | ph } <-> th ) ) $= feloprabg_0 feloprabg_3 feloprabg_4 feloprabg_5 feloprabg_6 feloprabg_7 feloprabg_8 feloprabg_9 feloprabg_10 feloprabg_11 feloprabg_12 feloprabg_4 sup_set_class feloprabg_7 wceq feloprabg_0 feloprabg_1 feloprabg_5 sup_set_class feloprabg_8 wceq feloprabg_2 feloprabg_6 sup_set_class feloprabg_9 wceq feloprabg_3 eeloprabg_0 eeloprabg_1 eeloprabg_2 syl3an9b eloprabga $.
$}
$( /* Inference of operation class abstraction subclass from implication.
       (Contributed by NM, 11-Nov-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) */

$)
${
	$d ph w $.
	$d ps w $.
	$d x z w $.
	$d y z w $.
	issoprab2i_0 $f set w $.
	fssoprab2i_0 $f wff ph $.
	fssoprab2i_1 $f wff ps $.
	fssoprab2i_2 $f set x $.
	fssoprab2i_3 $f set y $.
	fssoprab2i_4 $f set z $.
	essoprab2i_0 $e |- ( ph -> ps ) $.
	ssoprab2i $p |- { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } $= issoprab2i_0 sup_set_class fssoprab2i_2 sup_set_class fssoprab2i_3 sup_set_class cop wceq fssoprab2i_0 wa fssoprab2i_3 wex fssoprab2i_2 wex issoprab2i_0 fssoprab2i_4 copab issoprab2i_0 sup_set_class fssoprab2i_2 sup_set_class fssoprab2i_3 sup_set_class cop wceq fssoprab2i_1 wa fssoprab2i_3 wex fssoprab2i_2 wex issoprab2i_0 fssoprab2i_4 copab fssoprab2i_0 fssoprab2i_2 fssoprab2i_3 fssoprab2i_4 coprab fssoprab2i_1 fssoprab2i_2 fssoprab2i_3 fssoprab2i_4 coprab issoprab2i_0 sup_set_class fssoprab2i_2 sup_set_class fssoprab2i_3 sup_set_class cop wceq fssoprab2i_0 wa fssoprab2i_3 wex fssoprab2i_2 wex issoprab2i_0 sup_set_class fssoprab2i_2 sup_set_class fssoprab2i_3 sup_set_class cop wceq fssoprab2i_1 wa fssoprab2i_3 wex fssoprab2i_2 wex issoprab2i_0 fssoprab2i_4 issoprab2i_0 sup_set_class fssoprab2i_2 sup_set_class fssoprab2i_3 sup_set_class cop wceq fssoprab2i_0 wa issoprab2i_0 sup_set_class fssoprab2i_2 sup_set_class fssoprab2i_3 sup_set_class cop wceq fssoprab2i_1 wa fssoprab2i_2 fssoprab2i_3 fssoprab2i_0 fssoprab2i_1 issoprab2i_0 sup_set_class fssoprab2i_2 sup_set_class fssoprab2i_3 sup_set_class cop wceq essoprab2i_0 anim2i 2eximi ssopab2i fssoprab2i_0 fssoprab2i_2 fssoprab2i_3 fssoprab2i_4 issoprab2i_0 dfoprab2 fssoprab2i_1 fssoprab2i_2 fssoprab2i_3 fssoprab2i_4 issoprab2i_0 dfoprab2 3sstr4i $.
$}
$( /* Operation with universal domain in maps-to notation.  (Contributed by
       NM, 16-Aug-2013.) */

$)
${
	$d x z $.
	$d y z $.
	$d z C $.
	fmpt2v_0 $f set x $.
	fmpt2v_1 $f set y $.
	fmpt2v_2 $f set z $.
	fmpt2v_3 $f class C $.
	mpt2v $p |- ( x e. _V , y e. _V |-> C ) = { <. <. x , y >. , z >. | z = C } $= fmpt2v_0 fmpt2v_1 cvv cvv fmpt2v_3 cmpt2 fmpt2v_0 sup_set_class cvv wcel fmpt2v_1 sup_set_class cvv wcel wa fmpt2v_2 sup_set_class fmpt2v_3 wceq wa fmpt2v_0 fmpt2v_1 fmpt2v_2 coprab fmpt2v_2 sup_set_class fmpt2v_3 wceq fmpt2v_0 fmpt2v_1 fmpt2v_2 coprab fmpt2v_0 fmpt2v_1 fmpt2v_2 cvv cvv fmpt2v_3 df-mpt2 fmpt2v_2 sup_set_class fmpt2v_3 wceq fmpt2v_0 sup_set_class cvv wcel fmpt2v_1 sup_set_class cvv wcel wa fmpt2v_2 sup_set_class fmpt2v_3 wceq wa fmpt2v_0 fmpt2v_1 fmpt2v_2 fmpt2v_0 sup_set_class cvv wcel fmpt2v_1 sup_set_class cvv wcel wa fmpt2v_2 sup_set_class fmpt2v_3 wceq fmpt2v_0 sup_set_class cvv wcel fmpt2v_1 sup_set_class cvv wcel fmpt2v_0 vex fmpt2v_1 vex pm3.2i biantrur oprabbii eqtr4i $.
$}
$( /* Express a two-argument function as a one-argument function, or
       vice-versa.  In this version ` B ( x ) ` is not assumed to be constant
       w.r.t ` x ` .  (Contributed by Mario Carneiro, 29-Dec-2014.) */

$)
${
	$d w x y z A $.
	$d w y z B $.
	$d w x y C $.
	$d w z D $.
	impt2mptx_0 $f set w $.
	fmpt2mptx_0 $f set x $.
	fmpt2mptx_1 $f set y $.
	fmpt2mptx_2 $f set z $.
	fmpt2mptx_3 $f class A $.
	fmpt2mptx_4 $f class B $.
	fmpt2mptx_5 $f class C $.
	fmpt2mptx_6 $f class D $.
	empt2mptx_0 $e |- ( z = <. x , y >. -> C = D ) $.
	mpt2mptx $p |- ( z e. U_ x e. A ( { x } X. B ) |-> C ) = ( x e. A , y e. B |-> D ) $= fmpt2mptx_2 fmpt2mptx_0 fmpt2mptx_3 fmpt2mptx_0 sup_set_class csn fmpt2mptx_4 cxp ciun fmpt2mptx_5 cmpt fmpt2mptx_2 sup_set_class fmpt2mptx_0 fmpt2mptx_3 fmpt2mptx_0 sup_set_class csn fmpt2mptx_4 cxp ciun wcel impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_2 impt2mptx_0 copab fmpt2mptx_0 fmpt2mptx_1 fmpt2mptx_3 fmpt2mptx_4 fmpt2mptx_6 cmpt2 fmpt2mptx_2 impt2mptx_0 fmpt2mptx_0 fmpt2mptx_3 fmpt2mptx_0 sup_set_class csn fmpt2mptx_4 cxp ciun fmpt2mptx_5 df-mpt fmpt2mptx_0 fmpt2mptx_1 fmpt2mptx_3 fmpt2mptx_4 fmpt2mptx_6 cmpt2 fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa fmpt2mptx_0 fmpt2mptx_1 impt2mptx_0 coprab fmpt2mptx_2 sup_set_class fmpt2mptx_0 fmpt2mptx_3 fmpt2mptx_0 sup_set_class csn fmpt2mptx_4 cxp ciun wcel impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_2 impt2mptx_0 copab fmpt2mptx_0 fmpt2mptx_1 impt2mptx_0 fmpt2mptx_3 fmpt2mptx_4 fmpt2mptx_6 df-mpt2 fmpt2mptx_2 sup_set_class fmpt2mptx_0 fmpt2mptx_3 fmpt2mptx_0 sup_set_class csn fmpt2mptx_4 cxp ciun wcel impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_2 impt2mptx_0 copab fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa wa fmpt2mptx_1 wex fmpt2mptx_0 wex fmpt2mptx_2 impt2mptx_0 copab fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa fmpt2mptx_0 fmpt2mptx_1 impt2mptx_0 coprab fmpt2mptx_2 sup_set_class fmpt2mptx_0 fmpt2mptx_3 fmpt2mptx_0 sup_set_class csn fmpt2mptx_4 cxp ciun wcel impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa wa fmpt2mptx_1 wex fmpt2mptx_0 wex fmpt2mptx_2 impt2mptx_0 fmpt2mptx_2 sup_set_class fmpt2mptx_0 fmpt2mptx_3 fmpt2mptx_0 sup_set_class csn fmpt2mptx_4 cxp ciun wcel impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa wa fmpt2mptx_1 wex fmpt2mptx_0 wex impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa wa impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_1 wex fmpt2mptx_0 wex fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa wa fmpt2mptx_1 wex fmpt2mptx_0 wex fmpt2mptx_2 sup_set_class fmpt2mptx_0 fmpt2mptx_3 fmpt2mptx_0 sup_set_class csn fmpt2mptx_4 cxp ciun wcel fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa wa fmpt2mptx_1 wex fmpt2mptx_0 wex impt2mptx_0 sup_set_class fmpt2mptx_5 wceq fmpt2mptx_0 fmpt2mptx_1 fmpt2mptx_3 fmpt2mptx_4 fmpt2mptx_2 sup_set_class eliunxp anbi1i fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa wa impt2mptx_0 sup_set_class fmpt2mptx_5 wceq fmpt2mptx_0 fmpt2mptx_1 19.41vv fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa wa impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa wa fmpt2mptx_0 fmpt2mptx_1 fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa wa impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_5 wceq anass fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_5 wceq wa fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq impt2mptx_0 sup_set_class fmpt2mptx_5 wceq impt2mptx_0 sup_set_class fmpt2mptx_6 wceq fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa fmpt2mptx_2 sup_set_class fmpt2mptx_0 sup_set_class fmpt2mptx_1 sup_set_class cop wceq fmpt2mptx_5 fmpt2mptx_6 impt2mptx_0 sup_set_class empt2mptx_0 eqeq2d anbi2d pm5.32i bitri 2exbii 3bitr2i opabbii fmpt2mptx_0 sup_set_class fmpt2mptx_3 wcel fmpt2mptx_1 sup_set_class fmpt2mptx_4 wcel wa impt2mptx_0 sup_set_class fmpt2mptx_6 wceq wa fmpt2mptx_0 fmpt2mptx_1 impt2mptx_0 fmpt2mptx_2 dfoprab2 eqtr4i eqtr4i eqtr4i $.
$}
$( /* Express a two-argument function as a one-argument function, or
       vice-versa.  (Contributed by Mario Carneiro, 17-Dec-2013.)  (Revised by
       Mario Carneiro, 29-Dec-2014.) */

$)
${
	$d x y z A $.
	$d y z B $.
	$d x y C $.
	$d z D $.
	$d x B $.
	fmpt2mpt_0 $f set x $.
	fmpt2mpt_1 $f set y $.
	fmpt2mpt_2 $f set z $.
	fmpt2mpt_3 $f class A $.
	fmpt2mpt_4 $f class B $.
	fmpt2mpt_5 $f class C $.
	fmpt2mpt_6 $f class D $.
	empt2mpt_0 $e |- ( z = <. x , y >. -> C = D ) $.
	mpt2mpt $p |- ( z e. ( A X. B ) |-> C ) = ( x e. A , y e. B |-> D ) $= fmpt2mpt_2 fmpt2mpt_0 fmpt2mpt_3 fmpt2mpt_0 sup_set_class csn fmpt2mpt_4 cxp ciun fmpt2mpt_5 cmpt fmpt2mpt_2 fmpt2mpt_3 fmpt2mpt_4 cxp fmpt2mpt_5 cmpt fmpt2mpt_0 fmpt2mpt_1 fmpt2mpt_3 fmpt2mpt_4 fmpt2mpt_6 cmpt2 fmpt2mpt_0 fmpt2mpt_3 fmpt2mpt_0 sup_set_class csn fmpt2mpt_4 cxp ciun fmpt2mpt_3 fmpt2mpt_4 cxp wceq fmpt2mpt_2 fmpt2mpt_0 fmpt2mpt_3 fmpt2mpt_0 sup_set_class csn fmpt2mpt_4 cxp ciun fmpt2mpt_5 cmpt fmpt2mpt_2 fmpt2mpt_3 fmpt2mpt_4 cxp fmpt2mpt_5 cmpt wceq fmpt2mpt_0 fmpt2mpt_3 fmpt2mpt_4 iunxpconst fmpt2mpt_2 fmpt2mpt_0 fmpt2mpt_3 fmpt2mpt_0 sup_set_class csn fmpt2mpt_4 cxp ciun fmpt2mpt_3 fmpt2mpt_4 cxp fmpt2mpt_5 mpteq1 ax-mp fmpt2mpt_0 fmpt2mpt_1 fmpt2mpt_2 fmpt2mpt_3 fmpt2mpt_4 fmpt2mpt_5 fmpt2mpt_6 empt2mpt_0 mpt2mptx eqtr3i $.
$}
$( /* Restriction of an operation class abstraction.  (Contributed by NM,
       10-Feb-2007.) */

$)
${
	$d w x y z A $.
	$d w x y z B $.
	$d w ph $.
	iresoprab_0 $f set w $.
	fresoprab_0 $f wff ph $.
	fresoprab_1 $f set x $.
	fresoprab_2 $f set y $.
	fresoprab_3 $f set z $.
	fresoprab_4 $f class A $.
	fresoprab_5 $f class B $.
	resoprab $p |- ( { <. <. x , y >. , z >. | ph } |` ( A X. B ) ) = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $= iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 fresoprab_3 copab fresoprab_4 fresoprab_5 cxp cres iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 fresoprab_3 copab fresoprab_0 fresoprab_1 fresoprab_2 fresoprab_3 coprab fresoprab_4 fresoprab_5 cxp cres fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa fresoprab_1 fresoprab_2 fresoprab_3 coprab iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 fresoprab_3 copab fresoprab_4 fresoprab_5 cxp cres iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa fresoprab_2 wex fresoprab_1 wex wa iresoprab_0 fresoprab_3 copab iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 fresoprab_3 copab iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 fresoprab_3 fresoprab_4 fresoprab_5 cxp resopab iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa fresoprab_2 wex fresoprab_1 wex wa iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 fresoprab_3 iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa fresoprab_2 wex fresoprab_1 wex wa iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa fresoprab_1 fresoprab_2 19.42vv iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa wa iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa wa fresoprab_1 fresoprab_2 iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa wa iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel fresoprab_0 wa wa iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa wa iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 an12 iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel fresoprab_0 wa fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq iresoprab_0 sup_set_class fresoprab_4 fresoprab_5 cxp wcel fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop fresoprab_4 fresoprab_5 cxp wcel fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop fresoprab_4 fresoprab_5 cxp eleq1 fresoprab_1 sup_set_class fresoprab_2 sup_set_class fresoprab_4 fresoprab_5 opelxp syl6bb anbi1d pm5.32i bitri 2exbii bitr3i opabbii eqtri fresoprab_0 fresoprab_1 fresoprab_2 fresoprab_3 coprab iresoprab_0 sup_set_class fresoprab_1 sup_set_class fresoprab_2 sup_set_class cop wceq fresoprab_0 wa fresoprab_2 wex fresoprab_1 wex iresoprab_0 fresoprab_3 copab fresoprab_4 fresoprab_5 cxp fresoprab_0 fresoprab_1 fresoprab_2 fresoprab_3 iresoprab_0 dfoprab2 reseq1i fresoprab_1 sup_set_class fresoprab_4 wcel fresoprab_2 sup_set_class fresoprab_5 wcel wa fresoprab_0 wa fresoprab_1 fresoprab_2 fresoprab_3 iresoprab_0 dfoprab2 3eqtr4i $.
$}
$( /* Restriction of an operator abstraction.  (Contributed by Jeff Madsen,
       2-Sep-2009.) */

$)
${
	$d A x y z $.
	$d B x y z $.
	$d C x y z $.
	$d D x y z $.
	fresoprab2_0 $f wff ph $.
	fresoprab2_1 $f set x $.
	fresoprab2_2 $f set y $.
	fresoprab2_3 $f set z $.
	fresoprab2_4 $f class A $.
	fresoprab2_5 $f class B $.
	fresoprab2_6 $f class C $.
	fresoprab2_7 $f class D $.
	resoprab2 $p |- ( ( C C_ A /\ D C_ B ) -> ( { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } |` ( C X. D ) ) = { <. <. x , y >. , z >. | ( ( x e. C /\ y e. D ) /\ ph ) } ) $= fresoprab2_6 fresoprab2_4 wss fresoprab2_7 fresoprab2_5 wss wa fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa fresoprab2_0 wa fresoprab2_1 fresoprab2_2 fresoprab2_3 coprab fresoprab2_6 fresoprab2_7 cxp cres fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa fresoprab2_0 wa wa fresoprab2_1 fresoprab2_2 fresoprab2_3 coprab fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_0 wa fresoprab2_1 fresoprab2_2 fresoprab2_3 coprab fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa fresoprab2_0 wa fresoprab2_1 fresoprab2_2 fresoprab2_3 fresoprab2_6 fresoprab2_7 resoprab fresoprab2_6 fresoprab2_4 wss fresoprab2_7 fresoprab2_5 wss wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa fresoprab2_0 wa wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_0 wa fresoprab2_1 fresoprab2_2 fresoprab2_3 fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa fresoprab2_0 wa wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa wa fresoprab2_0 wa fresoprab2_6 fresoprab2_4 wss fresoprab2_7 fresoprab2_5 wss wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_0 wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa fresoprab2_0 anass fresoprab2_6 fresoprab2_4 wss fresoprab2_7 fresoprab2_5 wss wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_0 fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_1 sup_set_class fresoprab2_4 wcel wa fresoprab2_2 sup_set_class fresoprab2_7 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa wa fresoprab2_6 fresoprab2_4 wss fresoprab2_7 fresoprab2_5 wss wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel an4 fresoprab2_6 fresoprab2_4 wss fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_1 sup_set_class fresoprab2_4 wcel wa fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_7 fresoprab2_5 wss fresoprab2_2 sup_set_class fresoprab2_7 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa fresoprab2_2 sup_set_class fresoprab2_7 wcel fresoprab2_6 fresoprab2_4 wss fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_1 sup_set_class fresoprab2_4 wcel wa fresoprab2_6 fresoprab2_4 wss fresoprab2_1 sup_set_class fresoprab2_6 wcel fresoprab2_1 sup_set_class fresoprab2_4 wcel fresoprab2_6 fresoprab2_4 fresoprab2_1 sup_set_class ssel pm4.71d bicomd fresoprab2_7 fresoprab2_5 wss fresoprab2_2 sup_set_class fresoprab2_7 wcel fresoprab2_2 sup_set_class fresoprab2_7 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel wa fresoprab2_7 fresoprab2_5 wss fresoprab2_2 sup_set_class fresoprab2_7 wcel fresoprab2_2 sup_set_class fresoprab2_5 wcel fresoprab2_7 fresoprab2_5 fresoprab2_2 sup_set_class ssel pm4.71d bicomd bi2anan9 syl5bb anbi1d syl5bbr oprabbidv syl5eq $.
$}
$( /* Restriction of the mapping operation.  (Contributed by Mario Carneiro,
       17-Dec-2013.) */

$)
${
	$d A x y z $.
	$d B x y z $.
	$d C x y z $.
	$d D x y z $.
	$d E z $.
	iresmpt2_0 $f set z $.
	fresmpt2_0 $f set x $.
	fresmpt2_1 $f set y $.
	fresmpt2_2 $f class A $.
	fresmpt2_3 $f class B $.
	fresmpt2_4 $f class C $.
	fresmpt2_5 $f class D $.
	fresmpt2_6 $f class E $.
	resmpt2 $p |- ( ( C C_ A /\ D C_ B ) -> ( ( x e. A , y e. B |-> E ) |` ( C X. D ) ) = ( x e. C , y e. D |-> E ) ) $= fresmpt2_4 fresmpt2_2 wss fresmpt2_5 fresmpt2_3 wss wa fresmpt2_0 sup_set_class fresmpt2_2 wcel fresmpt2_1 sup_set_class fresmpt2_3 wcel wa iresmpt2_0 sup_set_class fresmpt2_6 wceq wa fresmpt2_0 fresmpt2_1 iresmpt2_0 coprab fresmpt2_4 fresmpt2_5 cxp cres fresmpt2_0 sup_set_class fresmpt2_4 wcel fresmpt2_1 sup_set_class fresmpt2_5 wcel wa iresmpt2_0 sup_set_class fresmpt2_6 wceq wa fresmpt2_0 fresmpt2_1 iresmpt2_0 coprab fresmpt2_0 fresmpt2_1 fresmpt2_2 fresmpt2_3 fresmpt2_6 cmpt2 fresmpt2_4 fresmpt2_5 cxp cres fresmpt2_0 fresmpt2_1 fresmpt2_4 fresmpt2_5 fresmpt2_6 cmpt2 iresmpt2_0 sup_set_class fresmpt2_6 wceq fresmpt2_0 fresmpt2_1 iresmpt2_0 fresmpt2_2 fresmpt2_3 fresmpt2_4 fresmpt2_5 resoprab2 fresmpt2_0 fresmpt2_1 fresmpt2_2 fresmpt2_3 fresmpt2_6 cmpt2 fresmpt2_0 sup_set_class fresmpt2_2 wcel fresmpt2_1 sup_set_class fresmpt2_3 wcel wa iresmpt2_0 sup_set_class fresmpt2_6 wceq wa fresmpt2_0 fresmpt2_1 iresmpt2_0 coprab fresmpt2_4 fresmpt2_5 cxp fresmpt2_0 fresmpt2_1 iresmpt2_0 fresmpt2_2 fresmpt2_3 fresmpt2_6 df-mpt2 reseq1i fresmpt2_0 fresmpt2_1 iresmpt2_0 fresmpt2_4 fresmpt2_5 fresmpt2_6 df-mpt2 3eqtr4g $.
$}
$( /* "At most one" is a sufficient condition for an operation class
       abstraction to be a function.  (Contributed by NM, 28-Aug-2007.) */

$)
${
	$d x y z w $.
	$d w ph $.
	ifunoprabg_0 $f set w $.
	ffunoprabg_0 $f wff ph $.
	ffunoprabg_1 $f set x $.
	ffunoprabg_2 $f set y $.
	ffunoprabg_3 $f set z $.
	funoprabg $p |- ( A. x A. y E* z ph -> Fun { <. <. x , y >. , z >. | ph } ) $= ffunoprabg_0 ffunoprabg_3 wmo ffunoprabg_2 wal ffunoprabg_1 wal ifunoprabg_0 sup_set_class ffunoprabg_1 sup_set_class ffunoprabg_2 sup_set_class cop wceq ffunoprabg_0 wa ffunoprabg_2 wex ffunoprabg_1 wex ffunoprabg_3 wmo ifunoprabg_0 wal ffunoprabg_0 ffunoprabg_1 ffunoprabg_2 ffunoprabg_3 coprab wfun ffunoprabg_0 ffunoprabg_3 wmo ffunoprabg_2 wal ffunoprabg_1 wal ifunoprabg_0 sup_set_class ffunoprabg_1 sup_set_class ffunoprabg_2 sup_set_class cop wceq ffunoprabg_0 wa ffunoprabg_2 wex ffunoprabg_1 wex ffunoprabg_3 wmo ifunoprabg_0 ffunoprabg_0 ffunoprabg_3 ffunoprabg_1 ffunoprabg_2 ifunoprabg_0 sup_set_class mosubopt alrimiv ffunoprabg_0 ffunoprabg_1 ffunoprabg_2 ffunoprabg_3 coprab wfun ifunoprabg_0 sup_set_class ffunoprabg_1 sup_set_class ffunoprabg_2 sup_set_class cop wceq ffunoprabg_0 wa ffunoprabg_2 wex ffunoprabg_1 wex ifunoprabg_0 ffunoprabg_3 copab wfun ifunoprabg_0 sup_set_class ffunoprabg_1 sup_set_class ffunoprabg_2 sup_set_class cop wceq ffunoprabg_0 wa ffunoprabg_2 wex ffunoprabg_1 wex ffunoprabg_3 wmo ifunoprabg_0 wal ffunoprabg_0 ffunoprabg_1 ffunoprabg_2 ffunoprabg_3 coprab ifunoprabg_0 sup_set_class ffunoprabg_1 sup_set_class ffunoprabg_2 sup_set_class cop wceq ffunoprabg_0 wa ffunoprabg_2 wex ffunoprabg_1 wex ifunoprabg_0 ffunoprabg_3 copab ffunoprabg_0 ffunoprabg_1 ffunoprabg_2 ffunoprabg_3 ifunoprabg_0 dfoprab2 funeqi ifunoprabg_0 sup_set_class ffunoprabg_1 sup_set_class ffunoprabg_2 sup_set_class cop wceq ffunoprabg_0 wa ffunoprabg_2 wex ffunoprabg_1 wex ifunoprabg_0 ffunoprabg_3 funopab bitr2i sylib $.
$}
$( /* "At most one" is a sufficient condition for an operation class
       abstraction to be a function.  (Contributed by NM, 17-Mar-1995.) */

$)
${
	$d x y z $.
	ffunoprab_0 $f wff ph $.
	ffunoprab_1 $f set x $.
	ffunoprab_2 $f set y $.
	ffunoprab_3 $f set z $.
	efunoprab_0 $e |- E* z ph $.
	funoprab $p |- Fun { <. <. x , y >. , z >. | ph } $= ffunoprab_0 ffunoprab_3 wmo ffunoprab_2 wal ffunoprab_1 wal ffunoprab_0 ffunoprab_1 ffunoprab_2 ffunoprab_3 coprab wfun ffunoprab_0 ffunoprab_3 wmo ffunoprab_1 ffunoprab_2 efunoprab_0 gen2 ffunoprab_0 ffunoprab_1 ffunoprab_2 ffunoprab_3 funoprabg ax-mp $.
$}
$( /* Functionality and domain of an operation class abstraction.
       (Contributed by NM, 28-Aug-2007.) */

$)
${
	$d x y z $.
	$d z ph $.
	ffnoprabg_0 $f wff ph $.
	ffnoprabg_1 $f wff ps $.
	ffnoprabg_2 $f set x $.
	ffnoprabg_3 $f set y $.
	ffnoprabg_4 $f set z $.
	fnoprabg $p |- ( A. x A. y ( ph -> E! z ps ) -> { <. <. x , y >. , z >. | ( ph /\ ps ) } Fn { <. x , y >. | ph } ) $= ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_3 wal ffnoprabg_2 wal ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_2 ffnoprabg_3 ffnoprabg_4 coprab wfun ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_2 ffnoprabg_3 ffnoprabg_4 coprab cdm ffnoprabg_0 ffnoprabg_2 ffnoprabg_3 copab wceq ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_2 ffnoprabg_3 ffnoprabg_4 coprab ffnoprabg_0 ffnoprabg_2 ffnoprabg_3 copab wfn ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_3 wal ffnoprabg_2 wal ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wmo ffnoprabg_3 wal ffnoprabg_2 wal ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_2 ffnoprabg_3 ffnoprabg_4 coprab wfun ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wmo ffnoprabg_2 ffnoprabg_3 ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 wmo wi ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wmo ffnoprabg_1 ffnoprabg_4 weu ffnoprabg_1 ffnoprabg_4 wmo ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 eumo imim2i ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 moanimv sylibr 2alimi ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_2 ffnoprabg_3 ffnoprabg_4 funoprabg syl ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_3 wal ffnoprabg_2 wal ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_2 ffnoprabg_3 ffnoprabg_4 coprab cdm ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wex ffnoprabg_2 ffnoprabg_3 copab ffnoprabg_0 ffnoprabg_2 ffnoprabg_3 copab ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_2 ffnoprabg_3 ffnoprabg_4 dmoprab ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_3 wal ffnoprabg_2 wal ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wex ffnoprabg_0 ffnoprabg_2 ffnoprabg_3 ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_3 wal ffnoprabg_2 nfa1 ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_3 ffnoprabg_2 nfa2 ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_3 wal ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wex ffnoprabg_0 wb ffnoprabg_2 ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wex ffnoprabg_0 wb ffnoprabg_3 ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wex ffnoprabg_0 ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_0 ffnoprabg_4 ffnoprabg_0 ffnoprabg_1 simpl exlimiv ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_0 ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 wex wa ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_4 wex ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 weu wi ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 wex ffnoprabg_1 ffnoprabg_4 weu ffnoprabg_1 ffnoprabg_4 wex ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 euex imim2i ancld ffnoprabg_0 ffnoprabg_1 ffnoprabg_4 19.42v syl6ibr impbid2 sps sps opabbid syl5eq ffnoprabg_0 ffnoprabg_1 wa ffnoprabg_2 ffnoprabg_3 ffnoprabg_4 coprab ffnoprabg_0 ffnoprabg_2 ffnoprabg_3 copab df-fn sylanbrc $.
$}
$( /* The maps-to notation for an operation is always a function.
       (Contributed by Scott Fenton, 21-Mar-2012.) */

$)
${
	$d A w z $.
	$d B w z $.
	$d C w z $.
	$d x y w z $.
	impt2fun_0 $f set z $.
	impt2fun_1 $f set w $.
	fmpt2fun_0 $f set x $.
	fmpt2fun_1 $f set y $.
	fmpt2fun_2 $f class A $.
	fmpt2fun_3 $f class B $.
	fmpt2fun_4 $f class C $.
	fmpt2fun_5 $f class F $.
	empt2fun_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	mpt2fun $p |- Fun F $= fmpt2fun_5 wfun fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class fmpt2fun_4 wceq wa fmpt2fun_0 fmpt2fun_1 impt2fun_0 coprab wfun fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class fmpt2fun_4 wceq wa fmpt2fun_0 fmpt2fun_1 impt2fun_0 fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class fmpt2fun_4 wceq wa impt2fun_0 wmo fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class fmpt2fun_4 wceq wa fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_1 sup_set_class fmpt2fun_4 wceq wa wa impt2fun_0 sup_set_class impt2fun_1 sup_set_class wceq wi impt2fun_1 wal impt2fun_0 wal fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class fmpt2fun_4 wceq wa fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_1 sup_set_class fmpt2fun_4 wceq wa wa impt2fun_0 sup_set_class impt2fun_1 sup_set_class wceq wi impt2fun_0 impt2fun_1 impt2fun_0 sup_set_class fmpt2fun_4 wceq impt2fun_1 sup_set_class fmpt2fun_4 wceq impt2fun_0 sup_set_class impt2fun_1 sup_set_class wceq fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class impt2fun_1 sup_set_class fmpt2fun_4 eqtr3 ad2ant2l gen2 fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class fmpt2fun_4 wceq wa fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_1 sup_set_class fmpt2fun_4 wceq wa impt2fun_0 impt2fun_1 impt2fun_0 sup_set_class impt2fun_1 sup_set_class wceq impt2fun_0 sup_set_class fmpt2fun_4 wceq impt2fun_1 sup_set_class fmpt2fun_4 wceq fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class impt2fun_1 sup_set_class fmpt2fun_4 eqeq1 anbi2d mo4 mpbir funoprab fmpt2fun_5 fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class fmpt2fun_4 wceq wa fmpt2fun_0 fmpt2fun_1 impt2fun_0 coprab fmpt2fun_5 fmpt2fun_0 fmpt2fun_1 fmpt2fun_2 fmpt2fun_3 fmpt2fun_4 cmpt2 fmpt2fun_0 sup_set_class fmpt2fun_2 wcel fmpt2fun_1 sup_set_class fmpt2fun_3 wcel wa impt2fun_0 sup_set_class fmpt2fun_4 wceq wa fmpt2fun_0 fmpt2fun_1 impt2fun_0 coprab empt2fun_0 fmpt2fun_0 fmpt2fun_1 impt2fun_0 fmpt2fun_2 fmpt2fun_3 fmpt2fun_4 df-mpt2 eqtri funeqi mpbir $.
$}
$( /* Functionality and domain of an operation class abstraction.
       (Contributed by NM, 15-May-1995.) */

$)
${
	$d x y z $.
	$d z ph $.
	ffnoprab_0 $f wff ph $.
	ffnoprab_1 $f wff ps $.
	ffnoprab_2 $f set x $.
	ffnoprab_3 $f set y $.
	ffnoprab_4 $f set z $.
	efnoprab_0 $e |- ( ph -> E! z ps ) $.
	fnoprab $p |- { <. <. x , y >. , z >. | ( ph /\ ps ) } Fn { <. x , y >. | ph } $= ffnoprab_0 ffnoprab_1 ffnoprab_4 weu wi ffnoprab_3 wal ffnoprab_2 wal ffnoprab_0 ffnoprab_1 wa ffnoprab_2 ffnoprab_3 ffnoprab_4 coprab ffnoprab_0 ffnoprab_2 ffnoprab_3 copab wfn ffnoprab_0 ffnoprab_1 ffnoprab_4 weu wi ffnoprab_2 ffnoprab_3 efnoprab_0 gen2 ffnoprab_0 ffnoprab_1 ffnoprab_2 ffnoprab_3 ffnoprab_4 fnoprabg ax-mp $.
$}
$( /* An operation maps to a class to which all values belong.  (Contributed
       by NM, 7-Feb-2004.) */

$)
${
	$d x y w A $.
	$d x y w B $.
	$d x y w C $.
	$d x y w F $.
	iffnov_0 $f set w $.
	fffnov_0 $f set x $.
	fffnov_1 $f set y $.
	fffnov_2 $f class A $.
	fffnov_3 $f class B $.
	fffnov_4 $f class C $.
	fffnov_5 $f class F $.
	ffnov $p |- ( F : ( A X. B ) --> C <-> ( F Fn ( A X. B ) /\ A. x e. A A. y e. B ( x F y ) e. C ) ) $= fffnov_2 fffnov_3 cxp fffnov_4 fffnov_5 wf fffnov_5 fffnov_2 fffnov_3 cxp wfn iffnov_0 sup_set_class fffnov_5 cfv fffnov_4 wcel iffnov_0 fffnov_2 fffnov_3 cxp wral wa fffnov_5 fffnov_2 fffnov_3 cxp wfn fffnov_0 sup_set_class fffnov_1 sup_set_class fffnov_5 co fffnov_4 wcel fffnov_1 fffnov_3 wral fffnov_0 fffnov_2 wral wa iffnov_0 fffnov_2 fffnov_3 cxp fffnov_4 fffnov_5 ffnfv iffnov_0 sup_set_class fffnov_5 cfv fffnov_4 wcel iffnov_0 fffnov_2 fffnov_3 cxp wral fffnov_0 sup_set_class fffnov_1 sup_set_class fffnov_5 co fffnov_4 wcel fffnov_1 fffnov_3 wral fffnov_0 fffnov_2 wral fffnov_5 fffnov_2 fffnov_3 cxp wfn iffnov_0 sup_set_class fffnov_5 cfv fffnov_4 wcel fffnov_0 sup_set_class fffnov_1 sup_set_class fffnov_5 co fffnov_4 wcel iffnov_0 fffnov_0 fffnov_1 fffnov_2 fffnov_3 iffnov_0 sup_set_class fffnov_0 sup_set_class fffnov_1 sup_set_class cop wceq iffnov_0 sup_set_class fffnov_5 cfv fffnov_0 sup_set_class fffnov_1 sup_set_class fffnov_5 co fffnov_4 iffnov_0 sup_set_class fffnov_0 sup_set_class fffnov_1 sup_set_class cop wceq iffnov_0 sup_set_class fffnov_5 cfv fffnov_0 sup_set_class fffnov_1 sup_set_class cop fffnov_5 cfv fffnov_0 sup_set_class fffnov_1 sup_set_class fffnov_5 co iffnov_0 sup_set_class fffnov_0 sup_set_class fffnov_1 sup_set_class cop fffnov_5 fveq2 fffnov_0 sup_set_class fffnov_1 sup_set_class fffnov_5 df-ov syl6eqr eleq1d ralxp anbi2i bitri $.
$}
$( /* Closure law for an operation.  (Contributed by NM, 19-Apr-2007.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x y C $.
	$d x y F $.
	$d x y R $.
	$d x y S $.
	ifovcl_0 $f set x $.
	ifovcl_1 $f set y $.
	ffovcl_0 $f class A $.
	ffovcl_1 $f class B $.
	ffovcl_2 $f class C $.
	ffovcl_3 $f class R $.
	ffovcl_4 $f class S $.
	ffovcl_5 $f class F $.
	efovcl_0 $e |- F : ( R X. S ) --> C $.
	fovcl $p |- ( ( A e. R /\ B e. S ) -> ( A F B ) e. C ) $= ffovcl_0 ffovcl_3 wcel ffovcl_1 ffovcl_4 wcel wa ifovcl_0 sup_set_class ifovcl_1 sup_set_class ffovcl_5 co ffovcl_2 wcel ifovcl_1 ffovcl_4 wral ifovcl_0 ffovcl_3 wral ffovcl_0 ffovcl_1 ffovcl_5 co ffovcl_2 wcel ffovcl_3 ffovcl_4 cxp ffovcl_2 ffovcl_5 wf ifovcl_0 sup_set_class ifovcl_1 sup_set_class ffovcl_5 co ffovcl_2 wcel ifovcl_1 ffovcl_4 wral ifovcl_0 ffovcl_3 wral efovcl_0 ffovcl_3 ffovcl_4 cxp ffovcl_2 ffovcl_5 wf ffovcl_5 ffovcl_3 ffovcl_4 cxp wfn ifovcl_0 sup_set_class ifovcl_1 sup_set_class ffovcl_5 co ffovcl_2 wcel ifovcl_1 ffovcl_4 wral ifovcl_0 ffovcl_3 wral ifovcl_0 ifovcl_1 ffovcl_3 ffovcl_4 ffovcl_2 ffovcl_5 ffnov simprbi ax-mp ifovcl_0 sup_set_class ifovcl_1 sup_set_class ffovcl_5 co ffovcl_2 wcel ffovcl_0 ffovcl_1 ffovcl_5 co ffovcl_2 wcel ffovcl_0 ifovcl_1 sup_set_class ffovcl_5 co ffovcl_2 wcel ifovcl_0 ifovcl_1 ffovcl_0 ffovcl_1 ffovcl_3 ffovcl_4 ifovcl_0 sup_set_class ffovcl_0 wceq ifovcl_0 sup_set_class ifovcl_1 sup_set_class ffovcl_5 co ffovcl_0 ifovcl_1 sup_set_class ffovcl_5 co ffovcl_2 ifovcl_0 sup_set_class ffovcl_0 ifovcl_1 sup_set_class ffovcl_5 oveq1 eleq1d ifovcl_1 sup_set_class ffovcl_1 wceq ffovcl_0 ifovcl_1 sup_set_class ffovcl_5 co ffovcl_0 ffovcl_1 ffovcl_5 co ffovcl_2 ifovcl_1 sup_set_class ffovcl_1 ffovcl_0 ffovcl_5 oveq2 eleq1d rspc2v mpi $.
$}
$( /* Equality of two operations is determined by their values.  (Contributed
       by NM, 1-Sep-2005.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d z C $.
	$d z D $.
	$d x y z F $.
	$d x y z G $.
	ieqfnov_0 $f set z $.
	feqfnov_0 $f set x $.
	feqfnov_1 $f set y $.
	feqfnov_2 $f class A $.
	feqfnov_3 $f class B $.
	feqfnov_4 $f class C $.
	feqfnov_5 $f class D $.
	feqfnov_6 $f class F $.
	feqfnov_7 $f class G $.
	eqfnov $p |- ( ( F Fn ( A X. B ) /\ G Fn ( C X. D ) ) -> ( F = G <-> ( ( A X. B ) = ( C X. D ) /\ A. x e. A A. y e. B ( x F y ) = ( x G y ) ) ) ) $= feqfnov_6 feqfnov_2 feqfnov_3 cxp wfn feqfnov_7 feqfnov_4 feqfnov_5 cxp wfn wa feqfnov_6 feqfnov_7 wceq feqfnov_2 feqfnov_3 cxp feqfnov_4 feqfnov_5 cxp wceq ieqfnov_0 sup_set_class feqfnov_6 cfv ieqfnov_0 sup_set_class feqfnov_7 cfv wceq ieqfnov_0 feqfnov_2 feqfnov_3 cxp wral wa feqfnov_2 feqfnov_3 cxp feqfnov_4 feqfnov_5 cxp wceq feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_6 co feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_7 co wceq feqfnov_1 feqfnov_3 wral feqfnov_0 feqfnov_2 wral wa ieqfnov_0 feqfnov_2 feqfnov_3 cxp feqfnov_4 feqfnov_5 cxp feqfnov_6 feqfnov_7 eqfnfv2 ieqfnov_0 sup_set_class feqfnov_6 cfv ieqfnov_0 sup_set_class feqfnov_7 cfv wceq ieqfnov_0 feqfnov_2 feqfnov_3 cxp wral feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_6 co feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_7 co wceq feqfnov_1 feqfnov_3 wral feqfnov_0 feqfnov_2 wral feqfnov_2 feqfnov_3 cxp feqfnov_4 feqfnov_5 cxp wceq ieqfnov_0 sup_set_class feqfnov_6 cfv ieqfnov_0 sup_set_class feqfnov_7 cfv wceq feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_6 co feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_7 co wceq ieqfnov_0 feqfnov_0 feqfnov_1 feqfnov_2 feqfnov_3 ieqfnov_0 sup_set_class feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop wceq ieqfnov_0 sup_set_class feqfnov_6 cfv ieqfnov_0 sup_set_class feqfnov_7 cfv wceq feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop feqfnov_6 cfv feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop feqfnov_7 cfv wceq feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_6 co feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_7 co wceq ieqfnov_0 sup_set_class feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop wceq ieqfnov_0 sup_set_class feqfnov_6 cfv feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop feqfnov_6 cfv ieqfnov_0 sup_set_class feqfnov_7 cfv feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop feqfnov_7 cfv ieqfnov_0 sup_set_class feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop feqfnov_6 fveq2 ieqfnov_0 sup_set_class feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop feqfnov_7 fveq2 eqeq12d feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_6 co feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop feqfnov_6 cfv feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_7 co feqfnov_0 sup_set_class feqfnov_1 sup_set_class cop feqfnov_7 cfv feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_6 df-ov feqfnov_0 sup_set_class feqfnov_1 sup_set_class feqfnov_7 df-ov eqeq12i syl6bbr ralxp anbi2i syl6bb $.
$}
$( /* Two operators with the same domain are equal iff their values at each
       point in the domain are equal.  (Contributed by Jeff Madsen,
       7-Jun-2010.) */

$)
${
	$d A x y $.
	$d B x y $.
	$d F x y $.
	$d G x y $.
	feqfnov2_0 $f set x $.
	feqfnov2_1 $f set y $.
	feqfnov2_2 $f class A $.
	feqfnov2_3 $f class B $.
	feqfnov2_4 $f class F $.
	feqfnov2_5 $f class G $.
	eqfnov2 $p |- ( ( F Fn ( A X. B ) /\ G Fn ( A X. B ) ) -> ( F = G <-> A. x e. A A. y e. B ( x F y ) = ( x G y ) ) ) $= feqfnov2_4 feqfnov2_2 feqfnov2_3 cxp wfn feqfnov2_5 feqfnov2_2 feqfnov2_3 cxp wfn wa feqfnov2_4 feqfnov2_5 wceq feqfnov2_2 feqfnov2_3 cxp feqfnov2_2 feqfnov2_3 cxp wceq feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_4 co feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_5 co wceq feqfnov2_1 feqfnov2_3 wral feqfnov2_0 feqfnov2_2 wral wa feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_4 co feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_5 co wceq feqfnov2_1 feqfnov2_3 wral feqfnov2_0 feqfnov2_2 wral feqfnov2_0 feqfnov2_1 feqfnov2_2 feqfnov2_3 feqfnov2_2 feqfnov2_3 feqfnov2_4 feqfnov2_5 eqfnov feqfnov2_2 feqfnov2_3 cxp feqfnov2_2 feqfnov2_3 cxp wceq feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_4 co feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_5 co wceq feqfnov2_1 feqfnov2_3 wral feqfnov2_0 feqfnov2_2 wral wa feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_4 co feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_5 co wceq feqfnov2_1 feqfnov2_3 wral feqfnov2_0 feqfnov2_2 wral feqfnov2_2 feqfnov2_3 cxp feqfnov2_2 feqfnov2_3 cxp wceq feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_4 co feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_5 co wceq feqfnov2_1 feqfnov2_3 wral feqfnov2_0 feqfnov2_2 wral simpr feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_4 co feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_5 co wceq feqfnov2_1 feqfnov2_3 wral feqfnov2_0 feqfnov2_2 wral feqfnov2_2 feqfnov2_3 cxp feqfnov2_2 feqfnov2_3 cxp wceq feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_4 co feqfnov2_0 sup_set_class feqfnov2_1 sup_set_class feqfnov2_5 co wceq feqfnov2_1 feqfnov2_3 wral feqfnov2_0 feqfnov2_2 wral feqfnov2_2 feqfnov2_3 cxp eqidd ancri impbii syl6bb $.
$}
$( /* Representation of a function in terms of its values.  (Contributed by
       NM, 7-Feb-2004.)  (Revised by Mario Carneiro, 31-Aug-2015.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z F $.
	ifnov_0 $f set z $.
	ffnov_0 $f set x $.
	ffnov_1 $f set y $.
	ffnov_2 $f class A $.
	ffnov_3 $f class B $.
	ffnov_4 $f class F $.
	fnov $p |- ( F Fn ( A X. B ) <-> F = ( x e. A , y e. B |-> ( x F y ) ) ) $= ffnov_4 ffnov_2 ffnov_3 cxp wfn ffnov_4 ifnov_0 ffnov_2 ffnov_3 cxp ifnov_0 sup_set_class ffnov_4 cfv cmpt wceq ffnov_4 ffnov_0 ffnov_1 ffnov_2 ffnov_3 ffnov_0 sup_set_class ffnov_1 sup_set_class ffnov_4 co cmpt2 wceq ifnov_0 ffnov_2 ffnov_3 cxp ffnov_4 dffn5 ifnov_0 ffnov_2 ffnov_3 cxp ifnov_0 sup_set_class ffnov_4 cfv cmpt ffnov_0 ffnov_1 ffnov_2 ffnov_3 ffnov_0 sup_set_class ffnov_1 sup_set_class ffnov_4 co cmpt2 ffnov_4 ffnov_0 ffnov_1 ifnov_0 ffnov_2 ffnov_3 ifnov_0 sup_set_class ffnov_4 cfv ffnov_0 sup_set_class ffnov_1 sup_set_class ffnov_4 co ifnov_0 sup_set_class ffnov_0 sup_set_class ffnov_1 sup_set_class cop wceq ifnov_0 sup_set_class ffnov_4 cfv ffnov_0 sup_set_class ffnov_1 sup_set_class cop ffnov_4 cfv ffnov_0 sup_set_class ffnov_1 sup_set_class ffnov_4 co ifnov_0 sup_set_class ffnov_0 sup_set_class ffnov_1 sup_set_class cop ffnov_4 fveq2 ffnov_0 sup_set_class ffnov_1 sup_set_class ffnov_4 df-ov syl6eqr mpt2mpt eqeq2i bitri $.
$}
$( /* Bidirectional equality theorem for a mapping abstraction.  Equivalent to
       ~ eqfnov2 .  (Contributed by Mario Carneiro, 4-Jan-2017.) */

$)
${
	$d x y z A $.
	$d y z B $.
	$d z C $.
	$d z D $.
	impt22eqb_0 $f set z $.
	fmpt22eqb_0 $f set x $.
	fmpt22eqb_1 $f set y $.
	fmpt22eqb_2 $f class A $.
	fmpt22eqb_3 $f class B $.
	fmpt22eqb_4 $f class C $.
	fmpt22eqb_5 $f class D $.
	fmpt22eqb_6 $f class V $.
	mpt22eqb $p |- ( A. x e. A A. y e. B C e. V -> ( ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) <-> A. x e. A A. y e. B C = D ) ) $= fmpt22eqb_4 fmpt22eqb_6 wcel fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 wral fmpt22eqb_4 fmpt22eqb_5 wceq fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 wral impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 wral fmpt22eqb_0 fmpt22eqb_1 fmpt22eqb_2 fmpt22eqb_3 fmpt22eqb_4 cmpt2 fmpt22eqb_0 fmpt22eqb_1 fmpt22eqb_2 fmpt22eqb_3 fmpt22eqb_5 cmpt2 wceq fmpt22eqb_4 fmpt22eqb_6 wcel fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 wral fmpt22eqb_4 fmpt22eqb_5 wceq fmpt22eqb_1 fmpt22eqb_3 wral impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 wral wb fmpt22eqb_0 fmpt22eqb_2 wral fmpt22eqb_4 fmpt22eqb_5 wceq fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 wral impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 wral wb fmpt22eqb_4 fmpt22eqb_6 wcel fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_4 fmpt22eqb_5 wceq fmpt22eqb_1 fmpt22eqb_3 wral impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 wral wb fmpt22eqb_0 fmpt22eqb_2 fmpt22eqb_4 fmpt22eqb_6 wcel fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_4 fmpt22eqb_5 wceq impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal wb fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_4 fmpt22eqb_5 wceq fmpt22eqb_1 fmpt22eqb_3 wral impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 wral wb fmpt22eqb_4 fmpt22eqb_6 wcel fmpt22eqb_4 fmpt22eqb_5 wceq impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal wb fmpt22eqb_1 fmpt22eqb_3 impt22eqb_0 fmpt22eqb_4 fmpt22eqb_5 fmpt22eqb_6 pm13.183 ralimi fmpt22eqb_4 fmpt22eqb_5 wceq impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 ralbi syl ralimi fmpt22eqb_4 fmpt22eqb_5 wceq fmpt22eqb_1 fmpt22eqb_3 wral impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 ralbi syl fmpt22eqb_0 fmpt22eqb_1 fmpt22eqb_2 fmpt22eqb_3 fmpt22eqb_4 cmpt2 fmpt22eqb_0 fmpt22eqb_1 fmpt22eqb_2 fmpt22eqb_3 fmpt22eqb_5 cmpt2 wceq fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq wa fmpt22eqb_0 fmpt22eqb_1 impt22eqb_0 coprab fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wa fmpt22eqb_0 fmpt22eqb_1 impt22eqb_0 coprab wceq fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq wa fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wa wb impt22eqb_0 wal fmpt22eqb_1 wal fmpt22eqb_0 wal impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 wral fmpt22eqb_0 fmpt22eqb_1 fmpt22eqb_2 fmpt22eqb_3 fmpt22eqb_4 cmpt2 fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq wa fmpt22eqb_0 fmpt22eqb_1 impt22eqb_0 coprab fmpt22eqb_0 fmpt22eqb_1 fmpt22eqb_2 fmpt22eqb_3 fmpt22eqb_5 cmpt2 fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wa fmpt22eqb_0 fmpt22eqb_1 impt22eqb_0 coprab fmpt22eqb_0 fmpt22eqb_1 impt22eqb_0 fmpt22eqb_2 fmpt22eqb_3 fmpt22eqb_4 df-mpt2 fmpt22eqb_0 fmpt22eqb_1 impt22eqb_0 fmpt22eqb_2 fmpt22eqb_3 fmpt22eqb_5 df-mpt2 eqeq12i fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq wa fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wa fmpt22eqb_0 fmpt22eqb_1 impt22eqb_0 eqoprab2b fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq wa fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wa wb impt22eqb_0 wal fmpt22eqb_1 wal fmpt22eqb_0 wal fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal wi fmpt22eqb_1 wal fmpt22eqb_0 wal impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_1 fmpt22eqb_3 wral fmpt22eqb_0 fmpt22eqb_2 wral fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq wa fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wa wb impt22eqb_0 wal fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal wi fmpt22eqb_0 fmpt22eqb_1 fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq wa fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wa wb impt22eqb_0 wal fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb wi impt22eqb_0 wal fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal wi fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb wi fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq wa fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wa wb impt22eqb_0 fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq pm5.32 albii fmpt22eqb_0 sup_set_class fmpt22eqb_2 wcel fmpt22eqb_1 sup_set_class fmpt22eqb_3 wcel wa impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 19.21v bitr3i 2albii impt22eqb_0 sup_set_class fmpt22eqb_4 wceq impt22eqb_0 sup_set_class fmpt22eqb_5 wceq wb impt22eqb_0 wal fmpt22eqb_0 fmpt22eqb_1 fmpt22eqb_2 fmpt22eqb_3 r2al bitr4i 3bitri syl6rbbr $.
$}
$( /* The range of an operation given by the "maps to" notation.  (Contributed
       by FL, 20-Jun-2011.) */

$)
${
	$d y z A $.
	$d z B $.
	$d z C $.
	$d z F $.
	$d x y z $.
	$d x y $.
	frnmpt2_0 $f set x $.
	frnmpt2_1 $f set y $.
	frnmpt2_2 $f set z $.
	frnmpt2_3 $f class A $.
	frnmpt2_4 $f class B $.
	frnmpt2_5 $f class C $.
	frnmpt2_6 $f class F $.
	ernmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	rnmpt2 $p |- ran F = { z | E. x e. A E. y e. B z = C } $= frnmpt2_6 crn frnmpt2_0 sup_set_class frnmpt2_3 wcel frnmpt2_1 sup_set_class frnmpt2_4 wcel wa frnmpt2_2 sup_set_class frnmpt2_5 wceq wa frnmpt2_0 frnmpt2_1 frnmpt2_2 coprab crn frnmpt2_2 sup_set_class frnmpt2_5 wceq frnmpt2_1 frnmpt2_4 wrex frnmpt2_0 frnmpt2_3 wrex frnmpt2_2 cab frnmpt2_6 frnmpt2_0 sup_set_class frnmpt2_3 wcel frnmpt2_1 sup_set_class frnmpt2_4 wcel wa frnmpt2_2 sup_set_class frnmpt2_5 wceq wa frnmpt2_0 frnmpt2_1 frnmpt2_2 coprab frnmpt2_6 frnmpt2_0 frnmpt2_1 frnmpt2_3 frnmpt2_4 frnmpt2_5 cmpt2 frnmpt2_0 sup_set_class frnmpt2_3 wcel frnmpt2_1 sup_set_class frnmpt2_4 wcel wa frnmpt2_2 sup_set_class frnmpt2_5 wceq wa frnmpt2_0 frnmpt2_1 frnmpt2_2 coprab ernmpt2_0 frnmpt2_0 frnmpt2_1 frnmpt2_2 frnmpt2_3 frnmpt2_4 frnmpt2_5 df-mpt2 eqtri rneqi frnmpt2_2 sup_set_class frnmpt2_5 wceq frnmpt2_0 frnmpt2_1 frnmpt2_2 frnmpt2_3 frnmpt2_4 rnoprab2 eqtri $.
$}
$( /* The domain of an operation defined by maps-to notation is a relation.
       (Contributed by Stefan O'Rear, 27-Nov-2014.) */

$)
${
	$d y z A $.
	$d z B $.
	$d z C $.
	$d z F $.
	$d x y z $.
	$d x y $.
	ireldmmpt2_0 $f set z $.
	freldmmpt2_0 $f set x $.
	freldmmpt2_1 $f set y $.
	freldmmpt2_2 $f class A $.
	freldmmpt2_3 $f class B $.
	freldmmpt2_4 $f class C $.
	freldmmpt2_5 $f class F $.
	ereldmmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	reldmmpt2 $p |- Rel dom F $= freldmmpt2_5 cdm wrel freldmmpt2_0 sup_set_class freldmmpt2_2 wcel freldmmpt2_1 sup_set_class freldmmpt2_3 wcel wa ireldmmpt2_0 sup_set_class freldmmpt2_4 wceq wa freldmmpt2_0 freldmmpt2_1 ireldmmpt2_0 coprab cdm wrel freldmmpt2_0 sup_set_class freldmmpt2_2 wcel freldmmpt2_1 sup_set_class freldmmpt2_3 wcel wa ireldmmpt2_0 sup_set_class freldmmpt2_4 wceq wa freldmmpt2_0 freldmmpt2_1 ireldmmpt2_0 reldmoprab freldmmpt2_5 cdm freldmmpt2_0 sup_set_class freldmmpt2_2 wcel freldmmpt2_1 sup_set_class freldmmpt2_3 wcel wa ireldmmpt2_0 sup_set_class freldmmpt2_4 wceq wa freldmmpt2_0 freldmmpt2_1 ireldmmpt2_0 coprab cdm freldmmpt2_5 freldmmpt2_0 sup_set_class freldmmpt2_2 wcel freldmmpt2_1 sup_set_class freldmmpt2_3 wcel wa ireldmmpt2_0 sup_set_class freldmmpt2_4 wceq wa freldmmpt2_0 freldmmpt2_1 ireldmmpt2_0 coprab freldmmpt2_5 freldmmpt2_0 freldmmpt2_1 freldmmpt2_2 freldmmpt2_3 freldmmpt2_4 cmpt2 freldmmpt2_0 sup_set_class freldmmpt2_2 wcel freldmmpt2_1 sup_set_class freldmmpt2_3 wcel wa ireldmmpt2_0 sup_set_class freldmmpt2_4 wceq wa freldmmpt2_0 freldmmpt2_1 ireldmmpt2_0 coprab ereldmmpt2_0 freldmmpt2_0 freldmmpt2_1 ireldmmpt2_0 freldmmpt2_2 freldmmpt2_3 freldmmpt2_4 df-mpt2 eqtri dmeqi releqi mpbir $.
$}
$( /* Membership in the range of an operation class abstraction.  (Contributed
       by NM, 27-Aug-2007.)  (Revised by Mario Carneiro, 31-Aug-2015.) */

$)
${
	$d y z A $.
	$d z B $.
	$d z C $.
	$d z F $.
	$d x y z D $.
	$d x y $.
	ielrnmpt2g_0 $f set z $.
	felrnmpt2g_0 $f set x $.
	felrnmpt2g_1 $f set y $.
	felrnmpt2g_2 $f class A $.
	felrnmpt2g_3 $f class B $.
	felrnmpt2g_4 $f class C $.
	felrnmpt2g_5 $f class D $.
	felrnmpt2g_6 $f class F $.
	felrnmpt2g_7 $f class V $.
	eelrnmpt2g_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	elrnmpt2g $p |- ( D e. V -> ( D e. ran F <-> E. x e. A E. y e. B D = C ) ) $= ielrnmpt2g_0 sup_set_class felrnmpt2g_4 wceq felrnmpt2g_1 felrnmpt2g_3 wrex felrnmpt2g_0 felrnmpt2g_2 wrex felrnmpt2g_5 felrnmpt2g_4 wceq felrnmpt2g_1 felrnmpt2g_3 wrex felrnmpt2g_0 felrnmpt2g_2 wrex ielrnmpt2g_0 felrnmpt2g_5 felrnmpt2g_6 crn felrnmpt2g_7 ielrnmpt2g_0 sup_set_class felrnmpt2g_5 wceq ielrnmpt2g_0 sup_set_class felrnmpt2g_4 wceq felrnmpt2g_5 felrnmpt2g_4 wceq felrnmpt2g_0 felrnmpt2g_1 felrnmpt2g_2 felrnmpt2g_3 ielrnmpt2g_0 sup_set_class felrnmpt2g_5 felrnmpt2g_4 eqeq1 2rexbidv felrnmpt2g_0 felrnmpt2g_1 ielrnmpt2g_0 felrnmpt2g_2 felrnmpt2g_3 felrnmpt2g_4 felrnmpt2g_6 eelrnmpt2g_0 rnmpt2 elab2g $.
$}
$( /* Membership in the range of an operation class abstraction.
         (Contributed by NM, 1-Aug-2004.)  (Revised by Mario Carneiro,
         31-Aug-2015.) */

$)
${
	$d y z A $.
	$d z B $.
	$d z C $.
	$d z F $.
	$d x y z D $.
	$d x y $.
	ielrnmpt2_0 $f set z $.
	felrnmpt2_0 $f set x $.
	felrnmpt2_1 $f set y $.
	felrnmpt2_2 $f class A $.
	felrnmpt2_3 $f class B $.
	felrnmpt2_4 $f class C $.
	felrnmpt2_5 $f class D $.
	felrnmpt2_6 $f class F $.
	eelrnmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	eelrnmpt2_1 $e |- C e. _V $.
	elrnmpt2 $p |- ( D e. ran F <-> E. x e. A E. y e. B D = C ) $= felrnmpt2_5 felrnmpt2_6 crn wcel felrnmpt2_5 ielrnmpt2_0 sup_set_class felrnmpt2_4 wceq felrnmpt2_1 felrnmpt2_3 wrex felrnmpt2_0 felrnmpt2_2 wrex ielrnmpt2_0 cab wcel felrnmpt2_5 felrnmpt2_4 wceq felrnmpt2_1 felrnmpt2_3 wrex felrnmpt2_0 felrnmpt2_2 wrex felrnmpt2_6 crn ielrnmpt2_0 sup_set_class felrnmpt2_4 wceq felrnmpt2_1 felrnmpt2_3 wrex felrnmpt2_0 felrnmpt2_2 wrex ielrnmpt2_0 cab felrnmpt2_5 felrnmpt2_0 felrnmpt2_1 ielrnmpt2_0 felrnmpt2_2 felrnmpt2_3 felrnmpt2_4 felrnmpt2_6 eelrnmpt2_0 rnmpt2 eleq2i ielrnmpt2_0 sup_set_class felrnmpt2_4 wceq felrnmpt2_1 felrnmpt2_3 wrex felrnmpt2_0 felrnmpt2_2 wrex felrnmpt2_5 felrnmpt2_4 wceq felrnmpt2_1 felrnmpt2_3 wrex felrnmpt2_0 felrnmpt2_2 wrex ielrnmpt2_0 felrnmpt2_5 felrnmpt2_5 felrnmpt2_4 wceq felrnmpt2_1 felrnmpt2_3 wrex felrnmpt2_5 cvv wcel felrnmpt2_0 felrnmpt2_2 felrnmpt2_5 felrnmpt2_4 wceq felrnmpt2_5 cvv wcel felrnmpt2_1 felrnmpt2_3 felrnmpt2_5 felrnmpt2_4 wceq felrnmpt2_5 cvv wcel felrnmpt2_4 cvv wcel eelrnmpt2_1 felrnmpt2_5 felrnmpt2_4 cvv eleq1 mpbiri rexlimivw rexlimivw ielrnmpt2_0 sup_set_class felrnmpt2_5 wceq ielrnmpt2_0 sup_set_class felrnmpt2_4 wceq felrnmpt2_5 felrnmpt2_4 wceq felrnmpt2_0 felrnmpt2_1 felrnmpt2_2 felrnmpt2_3 ielrnmpt2_0 sup_set_class felrnmpt2_5 felrnmpt2_4 eqeq1 2rexbidv elab3 bitri $.
$}
$( /* A restricted quantifier over an image set.  (Contributed by Mario
       Carneiro, 1-Sep-2015.) */

$)
${
	$d w x $.
	$d w y z A $.
	$d w z B $.
	$d w z C $.
	$d w z F $.
	$d z ps $.
	$d x y z $.
	$d x y ph $.
	iralrnmpt2_0 $f set w $.
	fralrnmpt2_0 $f wff ph $.
	fralrnmpt2_1 $f wff ps $.
	fralrnmpt2_2 $f set x $.
	fralrnmpt2_3 $f set y $.
	fralrnmpt2_4 $f set z $.
	fralrnmpt2_5 $f class A $.
	fralrnmpt2_6 $f class B $.
	fralrnmpt2_7 $f class C $.
	fralrnmpt2_8 $f class F $.
	fralrnmpt2_9 $f class V $.
	eralrnmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	eralrnmpt2_1 $e |- ( z = C -> ( ph <-> ps ) ) $.
	ralrnmpt2 $p |- ( A. x e. A A. y e. B C e. V -> ( A. z e. ran F ph <-> A. x e. A A. y e. B ps ) ) $= fralrnmpt2_0 fralrnmpt2_4 fralrnmpt2_8 crn wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_7 fralrnmpt2_9 wcel fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_1 fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_0 fralrnmpt2_4 fralrnmpt2_8 crn wral fralrnmpt2_0 fralrnmpt2_4 iralrnmpt2_0 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_2 fralrnmpt2_5 wrex iralrnmpt2_0 cab wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_2 fralrnmpt2_5 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_0 fralrnmpt2_4 fralrnmpt2_8 crn iralrnmpt2_0 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_2 fralrnmpt2_5 wrex iralrnmpt2_0 cab fralrnmpt2_2 fralrnmpt2_3 iralrnmpt2_0 fralrnmpt2_5 fralrnmpt2_6 fralrnmpt2_7 fralrnmpt2_8 eralrnmpt2_0 rnmpt2 raleqi iralrnmpt2_0 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_2 fralrnmpt2_5 wrex fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_2 fralrnmpt2_5 wrex fralrnmpt2_0 fralrnmpt2_4 iralrnmpt2_0 iralrnmpt2_0 sup_set_class fralrnmpt2_4 sup_set_class wceq iralrnmpt2_0 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_2 fralrnmpt2_3 fralrnmpt2_5 fralrnmpt2_6 iralrnmpt2_0 sup_set_class fralrnmpt2_4 sup_set_class fralrnmpt2_7 eqeq1 2rexbidv ralab fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_4 wal fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_2 fralrnmpt2_5 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_2 fralrnmpt2_4 fralrnmpt2_5 ralcom4 fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_2 fralrnmpt2_5 wrex fralrnmpt2_0 wi fralrnmpt2_4 fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 fralrnmpt2_2 fralrnmpt2_5 r19.23v albii bitr2i 3bitri fralrnmpt2_7 fralrnmpt2_9 wcel fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_1 fralrnmpt2_3 fralrnmpt2_6 wral wb fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_2 fralrnmpt2_5 wral fralrnmpt2_1 fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_2 fralrnmpt2_5 wral wb fralrnmpt2_7 fralrnmpt2_9 wcel fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_1 fralrnmpt2_3 fralrnmpt2_6 wral wb fralrnmpt2_2 fralrnmpt2_5 fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_7 fralrnmpt2_9 wcel fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_1 fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_4 wal fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_3 fralrnmpt2_4 fralrnmpt2_6 ralcom4 fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 fralrnmpt2_3 fralrnmpt2_6 r19.23v albii bitri fralrnmpt2_7 fralrnmpt2_9 wcel fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_1 wb fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_1 fralrnmpt2_3 fralrnmpt2_6 wral wb fralrnmpt2_7 fralrnmpt2_9 wcel fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_1 wb fralrnmpt2_3 fralrnmpt2_6 fralrnmpt2_0 fralrnmpt2_1 fralrnmpt2_4 fralrnmpt2_7 fralrnmpt2_9 fralrnmpt2_1 fralrnmpt2_4 nfv eralrnmpt2_1 ceqsalg ralimi fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_1 fralrnmpt2_3 fralrnmpt2_6 ralbi syl syl5bbr ralimi fralrnmpt2_4 sup_set_class fralrnmpt2_7 wceq fralrnmpt2_3 fralrnmpt2_6 wrex fralrnmpt2_0 wi fralrnmpt2_4 wal fralrnmpt2_1 fralrnmpt2_3 fralrnmpt2_6 wral fralrnmpt2_2 fralrnmpt2_5 ralbi syl syl5bb $.
$}
$( /* A restricted quantifier over an image set.  (Contributed by Mario
       Carneiro, 1-Sep-2015.) */

$)
${
	$d y z A $.
	$d z B $.
	$d z C $.
	$d z F $.
	$d z ps $.
	$d x y z $.
	$d x y ph $.
	frexrnmpt2_0 $f wff ph $.
	frexrnmpt2_1 $f wff ps $.
	frexrnmpt2_2 $f set x $.
	frexrnmpt2_3 $f set y $.
	frexrnmpt2_4 $f set z $.
	frexrnmpt2_5 $f class A $.
	frexrnmpt2_6 $f class B $.
	frexrnmpt2_7 $f class C $.
	frexrnmpt2_8 $f class F $.
	frexrnmpt2_9 $f class V $.
	erexrnmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	erexrnmpt2_1 $e |- ( z = C -> ( ph <-> ps ) ) $.
	rexrnmpt2 $p |- ( A. x e. A A. y e. B C e. V -> ( E. z e. ran F ph <-> E. x e. A E. y e. B ps ) ) $= frexrnmpt2_7 frexrnmpt2_9 wcel frexrnmpt2_3 frexrnmpt2_6 wral frexrnmpt2_2 frexrnmpt2_5 wral frexrnmpt2_0 wn frexrnmpt2_4 frexrnmpt2_8 crn wral wn frexrnmpt2_1 wn frexrnmpt2_3 frexrnmpt2_6 wral frexrnmpt2_2 frexrnmpt2_5 wral wn frexrnmpt2_0 frexrnmpt2_4 frexrnmpt2_8 crn wrex frexrnmpt2_1 frexrnmpt2_3 frexrnmpt2_6 wrex frexrnmpt2_2 frexrnmpt2_5 wrex frexrnmpt2_7 frexrnmpt2_9 wcel frexrnmpt2_3 frexrnmpt2_6 wral frexrnmpt2_2 frexrnmpt2_5 wral frexrnmpt2_0 wn frexrnmpt2_4 frexrnmpt2_8 crn wral frexrnmpt2_1 wn frexrnmpt2_3 frexrnmpt2_6 wral frexrnmpt2_2 frexrnmpt2_5 wral frexrnmpt2_0 wn frexrnmpt2_1 wn frexrnmpt2_2 frexrnmpt2_3 frexrnmpt2_4 frexrnmpt2_5 frexrnmpt2_6 frexrnmpt2_7 frexrnmpt2_8 frexrnmpt2_9 erexrnmpt2_0 frexrnmpt2_4 sup_set_class frexrnmpt2_7 wceq frexrnmpt2_0 frexrnmpt2_1 erexrnmpt2_1 notbid ralrnmpt2 notbid frexrnmpt2_0 frexrnmpt2_4 frexrnmpt2_8 crn dfrex2 frexrnmpt2_1 frexrnmpt2_3 frexrnmpt2_6 wrex frexrnmpt2_2 frexrnmpt2_5 wrex frexrnmpt2_1 wn frexrnmpt2_3 frexrnmpt2_6 wral wn frexrnmpt2_2 frexrnmpt2_5 wrex frexrnmpt2_1 wn frexrnmpt2_3 frexrnmpt2_6 wral frexrnmpt2_2 frexrnmpt2_5 wral wn frexrnmpt2_1 frexrnmpt2_3 frexrnmpt2_6 wrex frexrnmpt2_1 wn frexrnmpt2_3 frexrnmpt2_6 wral wn frexrnmpt2_2 frexrnmpt2_5 frexrnmpt2_1 frexrnmpt2_3 frexrnmpt2_6 dfrex2 rexbii frexrnmpt2_1 wn frexrnmpt2_3 frexrnmpt2_6 wral frexrnmpt2_2 frexrnmpt2_5 rexnal bitri 3bitr4g $.
$}
$( /* Existence of an operator abstraction.  (Contributed by Jeff Madsen,
       2-Sep-2009.) */

$)
${
	$d A x y z $.
	$d B x y z $.
	$d ph x y z $.
	foprabexd_0 $f wff ph $.
	foprabexd_1 $f wff ps $.
	foprabexd_2 $f set x $.
	foprabexd_3 $f set y $.
	foprabexd_4 $f set z $.
	foprabexd_5 $f class A $.
	foprabexd_6 $f class B $.
	foprabexd_7 $f class F $.
	eoprabexd_0 $e |- ( ph -> A e. _V ) $.
	eoprabexd_1 $e |- ( ph -> B e. _V ) $.
	eoprabexd_2 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> E* z ps ) $.
	eoprabexd_3 $e |- ( ph -> F = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) } ) $.
	oprabexd $p |- ( ph -> F e. _V ) $= foprabexd_0 foprabexd_7 foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab cvv eoprabexd_3 foprabexd_0 foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab wfun foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab cdm cvv wcel foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab cvv wcel foprabexd_0 foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_4 wmo foprabexd_3 wal foprabexd_2 wal foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab wfun foprabexd_0 foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_4 wmo foprabexd_2 foprabexd_3 foprabexd_0 foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 foprabexd_4 wmo wi foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_4 wmo foprabexd_0 foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 foprabexd_4 wmo eoprabexd_2 ex foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 foprabexd_4 moanimv sylibr alrimivv foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 funoprabg syl foprabexd_0 foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab cdm foprabexd_5 foprabexd_6 cxp wss foprabexd_5 foprabexd_6 cxp cvv wcel foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab cdm cvv wcel foprabexd_1 foprabexd_2 foprabexd_3 foprabexd_4 foprabexd_5 foprabexd_6 dmoprabss foprabexd_0 foprabexd_5 cvv wcel foprabexd_6 cvv wcel foprabexd_5 foprabexd_6 cxp cvv wcel eoprabexd_0 eoprabexd_1 foprabexd_5 foprabexd_6 cvv cvv xpexg syl2anc foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab cdm foprabexd_5 foprabexd_6 cxp cvv ssexg sylancr cvv foprabexd_2 sup_set_class foprabexd_5 wcel foprabexd_3 sup_set_class foprabexd_6 wcel wa foprabexd_1 wa foprabexd_2 foprabexd_3 foprabexd_4 coprab funex syl2anc eqeltrd $.
$}
$( /* Existence of an operation class abstraction.  (Contributed by NM,
       19-Oct-2004.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	foprabex_0 $f wff ph $.
	foprabex_1 $f set x $.
	foprabex_2 $f set y $.
	foprabex_3 $f set z $.
	foprabex_4 $f class A $.
	foprabex_5 $f class B $.
	foprabex_6 $f class F $.
	eoprabex_0 $e |- A e. _V $.
	eoprabex_1 $e |- B e. _V $.
	eoprabex_2 $e |- ( ( x e. A /\ y e. B ) -> E* z ph ) $.
	eoprabex_3 $e |- F = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $.
	oprabex $p |- F e. _V $= foprabex_6 foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 wa foprabex_1 foprabex_2 foprabex_3 coprab cvv eoprabex_3 foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 wa foprabex_1 foprabex_2 foprabex_3 coprab wfun foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 wa foprabex_1 foprabex_2 foprabex_3 coprab cdm cvv wcel foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 wa foprabex_1 foprabex_2 foprabex_3 coprab cvv wcel foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 wa foprabex_1 foprabex_2 foprabex_3 foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 wa foprabex_3 wmo foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 foprabex_3 wmo wi eoprabex_2 foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 foprabex_3 moanimv mpbir funoprab foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 wa foprabex_1 foprabex_2 foprabex_3 coprab cdm foprabex_4 foprabex_5 cxp foprabex_4 foprabex_5 eoprabex_0 eoprabex_1 xpex foprabex_0 foprabex_1 foprabex_2 foprabex_3 foprabex_4 foprabex_5 dmoprabss ssexi cvv foprabex_1 sup_set_class foprabex_4 wcel foprabex_2 sup_set_class foprabex_5 wcel wa foprabex_0 wa foprabex_1 foprabex_2 foprabex_3 coprab funex mp2an eqeltri $.
$}
$( /* Existence of an operation class abstraction (special case).
       (Contributed by NM, 19-Oct-2004.) */

$)
${
	$d x y z w v u f $.
	$d x y z w v u f $.
	$d x y z w v u f $.
	$d x y z w v u f $.
	$d x y z w v u f H $.
	$d x y z R $.
	$d x y z w v u f $.
	foprabex3_0 $f set x $.
	foprabex3_1 $f set y $.
	foprabex3_2 $f set z $.
	foprabex3_3 $f set w $.
	foprabex3_4 $f set v $.
	foprabex3_5 $f set u $.
	foprabex3_6 $f class R $.
	foprabex3_7 $f set f $.
	foprabex3_8 $f class F $.
	foprabex3_9 $f class H $.
	eoprabex3_0 $e |- H e. _V $.
	eoprabex3_1 $e |- F = { <. <. x , y >. , z >. | ( ( x e. ( H X. H ) /\ y e. ( H X. H ) ) /\ E. w E. v E. u E. f ( ( x = <. w , v >. /\ y = <. u , f >. ) /\ z = R ) ) } $.
	oprabex3 $p |- F e. _V $= foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq wa foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex foprabex3_4 wex foprabex3_3 wex foprabex3_0 foprabex3_1 foprabex3_2 foprabex3_9 foprabex3_9 cxp foprabex3_9 foprabex3_9 cxp foprabex3_8 foprabex3_9 foprabex3_9 eoprabex3_0 eoprabex3_0 xpex foprabex3_9 foprabex3_9 eoprabex3_0 eoprabex3_0 xpex foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq wa foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex foprabex3_4 wex foprabex3_3 wex foprabex3_2 wmo foprabex3_0 sup_set_class foprabex3_9 foprabex3_9 cxp wcel foprabex3_1 sup_set_class foprabex3_9 foprabex3_9 cxp wcel wa foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq wa foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex foprabex3_4 wex foprabex3_3 wex foprabex3_2 wmo foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex wa foprabex3_4 wex foprabex3_3 wex foprabex3_2 wmo foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex foprabex3_2 foprabex3_3 foprabex3_4 foprabex3_0 sup_set_class foprabex3_2 sup_set_class foprabex3_6 wceq foprabex3_2 foprabex3_5 foprabex3_7 foprabex3_1 sup_set_class foprabex3_2 foprabex3_6 moeq mosubop mosubop foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq wa foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex foprabex3_4 wex foprabex3_3 wex foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex wa foprabex3_4 wex foprabex3_3 wex foprabex3_2 foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq wa foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex wa foprabex3_3 foprabex3_4 foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq wa foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq wa wa foprabex3_7 wex foprabex3_5 wex foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_7 wex foprabex3_5 wex wa foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq wa foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq wa wa foprabex3_5 foprabex3_7 foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq anass 2exbii foprabex3_0 sup_set_class foprabex3_3 sup_set_class foprabex3_4 sup_set_class cop wceq foprabex3_1 sup_set_class foprabex3_5 sup_set_class foprabex3_7 sup_set_class cop wceq foprabex3_2 sup_set_class foprabex3_6 wceq wa foprabex3_5 foprabex3_7 19.42vv bitri 2exbii mobii mpbir a1i eoprabex3_1 oprabex $.
$}
$( /* Existence of an existentially restricted operation abstraction.
       (Contributed by Jeff Madsen, 11-Jun-2010.) */

$)
${
	$d A v x y z w $.
	$d ph v $.
	ioprabrexex2_0 $f set v $.
	foprabrexex2_0 $f wff ph $.
	foprabrexex2_1 $f set x $.
	foprabrexex2_2 $f set y $.
	foprabrexex2_3 $f set z $.
	foprabrexex2_4 $f set w $.
	foprabrexex2_5 $f class A $.
	eoprabrexex2_0 $e |- A e. _V $.
	eoprabrexex2_1 $e |- { <. <. x , y >. , z >. | ph } e. _V $.
	oprabrexex2 $p |- { <. <. x , y >. , z >. | E. w e. A ph } e. _V $= foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex foprabrexex2_1 foprabrexex2_2 foprabrexex2_3 coprab ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 cab cvv foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex foprabrexex2_1 foprabrexex2_2 foprabrexex2_3 coprab ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex ioprabrexex2_0 cab ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 cab foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex foprabrexex2_1 foprabrexex2_2 foprabrexex2_3 ioprabrexex2_0 df-oprab ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_4 foprabrexex2_5 wrex foprabrexex2_1 wex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_4 foprabrexex2_1 foprabrexex2_5 rexcom4 ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_4 foprabrexex2_5 wrex foprabrexex2_2 wex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex wa foprabrexex2_3 wex foprabrexex2_2 wex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_4 foprabrexex2_2 foprabrexex2_5 rexcom4 ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex wa foprabrexex2_3 wex foprabrexex2_2 ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_4 foprabrexex2_5 wrex foprabrexex2_3 wex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex wa foprabrexex2_3 wex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_4 foprabrexex2_3 foprabrexex2_5 rexcom4 ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_4 foprabrexex2_5 wrex ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 wrex wa foprabrexex2_3 ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 foprabrexex2_4 foprabrexex2_5 r19.42v exbii bitri exbii bitri exbii bitr2i abbii eqtri ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex foprabrexex2_4 ioprabrexex2_0 foprabrexex2_5 eoprabrexex2_0 foprabrexex2_0 foprabrexex2_1 foprabrexex2_2 foprabrexex2_3 coprab ioprabrexex2_0 sup_set_class foprabrexex2_1 sup_set_class foprabrexex2_2 sup_set_class cop foprabrexex2_3 sup_set_class cop wceq foprabrexex2_0 wa foprabrexex2_3 wex foprabrexex2_2 wex foprabrexex2_1 wex ioprabrexex2_0 cab cvv foprabrexex2_0 foprabrexex2_1 foprabrexex2_2 foprabrexex2_3 ioprabrexex2_0 df-oprab eoprabrexex2_1 eqeltrri abrexex2 eqeltri $.
$}
$( /* The value of an operation class abstraction.  (Contributed by NM,
       16-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) */

$)
${
	$d x y z $.
	$d z R $.
	$d z S $.
	fovid_0 $f wff ph $.
	fovid_1 $f set x $.
	fovid_2 $f set y $.
	fovid_3 $f set z $.
	fovid_4 $f class R $.
	fovid_5 $f class S $.
	fovid_6 $f class F $.
	eovid_0 $e |- ( ( x e. R /\ y e. S ) -> E! z ph ) $.
	eovid_1 $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	ovid $p |- ( ( x e. R /\ y e. S ) -> ( ( x F y ) = z <-> ph ) ) $= fovid_1 sup_set_class fovid_2 sup_set_class fovid_6 co fovid_3 sup_set_class wceq fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_6 cfv fovid_3 sup_set_class wceq fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 fovid_1 sup_set_class fovid_2 sup_set_class fovid_6 co fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_6 cfv fovid_3 sup_set_class fovid_1 sup_set_class fovid_2 sup_set_class fovid_6 df-ov eqeq1i fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_6 cfv fovid_3 sup_set_class wceq fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_3 sup_set_class cop fovid_6 wcel fovid_0 fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_6 fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 fovid_2 copab wfn fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 fovid_2 copab wcel fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_6 cfv fovid_3 sup_set_class wceq fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_3 sup_set_class cop fovid_6 wcel wb fovid_6 fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 fovid_2 copab wfn fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 wa fovid_1 fovid_2 fovid_3 coprab fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 fovid_2 copab wfn fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 fovid_1 fovid_2 fovid_3 eovid_0 fnoprab fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 fovid_2 copab fovid_6 fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 wa fovid_1 fovid_2 fovid_3 coprab eovid_1 fneq1i mpbir fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 fovid_2 copab wcel fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 fovid_2 opabid biimpri fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_1 fovid_2 copab fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_3 sup_set_class fovid_6 fnopfvb sylancr fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_3 sup_set_class cop fovid_6 wcel fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_3 sup_set_class cop fovid_6 wcel fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_3 sup_set_class cop fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 wa fovid_1 fovid_2 fovid_3 coprab wcel fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 wa fovid_6 fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 wa fovid_1 fovid_2 fovid_3 coprab fovid_1 sup_set_class fovid_2 sup_set_class cop fovid_3 sup_set_class cop eovid_1 eleq2i fovid_1 sup_set_class fovid_4 wcel fovid_2 sup_set_class fovid_5 wcel wa fovid_0 wa fovid_1 fovid_2 fovid_3 oprabid bitri baib bitrd syl5bb $.
$}
$( /* The value of an operation class abstraction.  Compare ~ ovidi .  The
       condition ` ( x e. R /\ y e. S ) ` is been removed.  (Contributed by
       Mario Carneiro, 29-Dec-2014.) */

$)
${
	$d x y z $.
	fovidig_0 $f wff ph $.
	fovidig_1 $f set x $.
	fovidig_2 $f set y $.
	fovidig_3 $f set z $.
	fovidig_4 $f class F $.
	eovidig_0 $e |- E* z ph $.
	eovidig_1 $e |- F = { <. <. x , y >. , z >. | ph } $.
	ovidig $p |- ( ph -> ( x F y ) = z ) $= fovidig_0 fovidig_1 sup_set_class fovidig_2 sup_set_class fovidig_4 co fovidig_1 sup_set_class fovidig_2 sup_set_class cop fovidig_4 cfv fovidig_3 sup_set_class fovidig_1 sup_set_class fovidig_2 sup_set_class fovidig_4 df-ov fovidig_4 wfun fovidig_0 fovidig_1 sup_set_class fovidig_2 sup_set_class cop fovidig_3 sup_set_class cop fovidig_4 wcel fovidig_1 sup_set_class fovidig_2 sup_set_class cop fovidig_4 cfv fovidig_3 sup_set_class wceq fovidig_4 wfun fovidig_0 fovidig_1 fovidig_2 fovidig_3 coprab wfun fovidig_0 fovidig_1 fovidig_2 fovidig_3 eovidig_0 funoprab fovidig_4 fovidig_0 fovidig_1 fovidig_2 fovidig_3 coprab eovidig_1 funeqi mpbir fovidig_0 fovidig_1 sup_set_class fovidig_2 sup_set_class cop fovidig_3 sup_set_class cop fovidig_0 fovidig_1 fovidig_2 fovidig_3 coprab fovidig_4 fovidig_1 sup_set_class fovidig_2 sup_set_class cop fovidig_3 sup_set_class cop fovidig_0 fovidig_1 fovidig_2 fovidig_3 coprab wcel fovidig_0 fovidig_0 fovidig_1 fovidig_2 fovidig_3 oprabid biimpri eovidig_1 syl6eleqr fovidig_1 sup_set_class fovidig_2 sup_set_class cop fovidig_3 sup_set_class fovidig_4 funopfv mpsyl syl5eq $.
$}
$( /* The value of an operation class abstraction (weak version).
       (Contributed by Mario Carneiro, 29-Dec-2014.) */

$)
${
	$d x y z $.
	$d z R $.
	$d z S $.
	fovidi_0 $f wff ph $.
	fovidi_1 $f set x $.
	fovidi_2 $f set y $.
	fovidi_3 $f set z $.
	fovidi_4 $f class R $.
	fovidi_5 $f class S $.
	fovidi_6 $f class F $.
	eovidi_0 $e |- ( ( x e. R /\ y e. S ) -> E* z ph ) $.
	eovidi_1 $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	ovidi $p |- ( ( x e. R /\ y e. S ) -> ( ph -> ( x F y ) = z ) ) $= fovidi_1 sup_set_class fovidi_4 wcel fovidi_2 sup_set_class fovidi_5 wcel wa fovidi_0 fovidi_1 sup_set_class fovidi_2 sup_set_class fovidi_6 co fovidi_3 sup_set_class wceq fovidi_1 sup_set_class fovidi_4 wcel fovidi_2 sup_set_class fovidi_5 wcel wa fovidi_0 wa fovidi_1 fovidi_2 fovidi_3 fovidi_6 fovidi_1 sup_set_class fovidi_4 wcel fovidi_2 sup_set_class fovidi_5 wcel wa fovidi_0 wa fovidi_3 wmo fovidi_1 sup_set_class fovidi_4 wcel fovidi_2 sup_set_class fovidi_5 wcel wa fovidi_0 fovidi_3 wmo wi eovidi_0 fovidi_1 sup_set_class fovidi_4 wcel fovidi_2 sup_set_class fovidi_5 wcel wa fovidi_0 fovidi_3 moanimv mpbir eovidi_1 ovidig ex $.
$}
$( /* The value of an operation class abstraction.  (Contributed by NM,
       16-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z R $.
	$d x y z S $.
	$d x y z th $.
	fov_0 $f wff ph $.
	fov_1 $f wff ps $.
	fov_2 $f wff ch $.
	fov_3 $f wff th $.
	fov_4 $f set x $.
	fov_5 $f set y $.
	fov_6 $f set z $.
	fov_7 $f class A $.
	fov_8 $f class B $.
	fov_9 $f class C $.
	fov_10 $f class R $.
	fov_11 $f class S $.
	fov_12 $f class F $.
	eov_0 $e |- C e. _V $.
	eov_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eov_2 $e |- ( y = B -> ( ps <-> ch ) ) $.
	eov_3 $e |- ( z = C -> ( ch <-> th ) ) $.
	eov_4 $e |- ( ( x e. R /\ y e. S ) -> E! z ph ) $.
	eov_5 $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	ov $p |- ( ( A e. R /\ B e. S ) -> ( ( A F B ) = C <-> th ) ) $= fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_7 fov_8 fov_12 co fov_9 wceq fov_3 fov_7 fov_8 fov_12 co fov_9 wceq fov_7 fov_8 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab cfv fov_9 wceq fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_3 wa fov_7 fov_8 fov_12 co fov_7 fov_8 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab cfv fov_9 fov_7 fov_8 fov_12 co fov_7 fov_8 cop fov_12 cfv fov_7 fov_8 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab cfv fov_7 fov_8 fov_12 df-ov fov_7 fov_8 cop fov_12 fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab eov_5 fveq1i eqtri eqeq1i fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_7 fov_8 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab cfv fov_9 wceq fov_7 fov_8 cop fov_9 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab wcel fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_3 wa fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_4 fov_5 copab wfn fov_7 fov_8 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_4 fov_5 copab wcel fov_7 fov_8 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab cfv fov_9 wceq fov_7 fov_8 cop fov_9 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab wcel wb fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 fov_4 fov_5 fov_6 eov_4 fnoprab fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_7 fov_8 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_4 fov_5 copab wcel fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_7 fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_4 fov_5 fov_7 fov_8 fov_10 fov_11 fov_4 sup_set_class fov_7 wceq fov_4 sup_set_class fov_10 wcel fov_7 fov_10 wcel fov_5 sup_set_class fov_11 wcel fov_4 sup_set_class fov_7 fov_10 eleq1 anbi1d fov_5 sup_set_class fov_8 wceq fov_5 sup_set_class fov_11 wcel fov_8 fov_11 wcel fov_7 fov_10 wcel fov_5 sup_set_class fov_8 fov_11 eleq1 anbi2d opelopabg ibir fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_4 fov_5 copab fov_7 fov_8 cop fov_9 fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab fnopfvb sylancr fov_7 fov_10 wcel fov_8 fov_11 wcel fov_9 cvv wcel fov_7 fov_8 cop fov_9 cop fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_4 fov_5 fov_6 coprab wcel fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_3 wa wb eov_0 fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 wa fov_7 fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_1 wa fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_2 wa fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_3 wa fov_4 fov_5 fov_6 fov_7 fov_8 fov_9 fov_10 fov_11 cvv fov_4 sup_set_class fov_7 wceq fov_4 sup_set_class fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_7 fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_0 fov_1 fov_4 sup_set_class fov_7 wceq fov_4 sup_set_class fov_10 wcel fov_7 fov_10 wcel fov_5 sup_set_class fov_11 wcel fov_4 sup_set_class fov_7 fov_10 eleq1 anbi1d eov_1 anbi12d fov_5 sup_set_class fov_8 wceq fov_7 fov_10 wcel fov_5 sup_set_class fov_11 wcel wa fov_7 fov_10 wcel fov_8 fov_11 wcel wa fov_1 fov_2 fov_5 sup_set_class fov_8 wceq fov_5 sup_set_class fov_11 wcel fov_8 fov_11 wcel fov_7 fov_10 wcel fov_5 sup_set_class fov_8 fov_11 eleq1 anbi2d eov_2 anbi12d fov_6 sup_set_class fov_9 wceq fov_2 fov_3 fov_7 fov_10 wcel fov_8 fov_11 wcel wa eov_3 anbi2d eloprabg mp3an3 bitrd syl5bb bianabs $.
$}
$( /* The value of an operation class abstraction.  Compare ~ ovig .  The
       condition ` ( x e. R /\ y e. S ) ` is been removed.  (Contributed by FL,
       24-Mar-2007.)  (Revised by Mario Carneiro, 19-Dec-2013.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z ps $.
	fovigg_0 $f wff ph $.
	fovigg_1 $f wff ps $.
	fovigg_2 $f set x $.
	fovigg_3 $f set y $.
	fovigg_4 $f set z $.
	fovigg_5 $f class A $.
	fovigg_6 $f class B $.
	fovigg_7 $f class C $.
	fovigg_8 $f class F $.
	fovigg_9 $f class V $.
	fovigg_10 $f class W $.
	fovigg_11 $f class X $.
	eovigg_0 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	eovigg_1 $e |- E* z ph $.
	eovigg_2 $e |- F = { <. <. x , y >. , z >. | ph } $.
	ovigg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ps -> ( A F B ) = C ) ) $= fovigg_5 fovigg_9 wcel fovigg_6 fovigg_10 wcel fovigg_7 fovigg_11 wcel w3a fovigg_1 fovigg_5 fovigg_6 cop fovigg_7 cop fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab wcel fovigg_5 fovigg_6 fovigg_8 co fovigg_7 wceq fovigg_0 fovigg_1 fovigg_2 fovigg_3 fovigg_4 fovigg_5 fovigg_6 fovigg_7 fovigg_9 fovigg_10 fovigg_11 eovigg_0 eloprabga fovigg_5 fovigg_6 cop fovigg_7 cop fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab wcel fovigg_5 fovigg_6 fovigg_8 co fovigg_5 fovigg_6 cop fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab cfv fovigg_7 fovigg_5 fovigg_6 fovigg_8 co fovigg_5 fovigg_6 cop fovigg_8 cfv fovigg_5 fovigg_6 cop fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab cfv fovigg_5 fovigg_6 fovigg_8 df-ov fovigg_5 fovigg_6 cop fovigg_8 fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab eovigg_2 fveq1i eqtri fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab wfun fovigg_5 fovigg_6 cop fovigg_7 cop fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab wcel fovigg_5 fovigg_6 cop fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab cfv fovigg_7 wceq wi fovigg_0 fovigg_2 fovigg_3 fovigg_4 eovigg_1 funoprab fovigg_5 fovigg_6 cop fovigg_7 fovigg_0 fovigg_2 fovigg_3 fovigg_4 coprab funopfv ax-mp syl5eq syl6bir $.
$}
$( /* The value of an operation class abstraction (weak version).
       (Unnecessary distinct variable restrictions were removed by David
       Abernethy, 19-Jun-2012.)  (Contributed by NM, 14-Sep-1999.)  (Revised by
       Mario Carneiro, 19-Dec-2013.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z R $.
	$d x y z S $.
	$d x y z ps $.
	fovig_0 $f wff ph $.
	fovig_1 $f wff ps $.
	fovig_2 $f set x $.
	fovig_3 $f set y $.
	fovig_4 $f set z $.
	fovig_5 $f class A $.
	fovig_6 $f class B $.
	fovig_7 $f class C $.
	fovig_8 $f class D $.
	fovig_9 $f class R $.
	fovig_10 $f class S $.
	fovig_11 $f class F $.
	eovig_0 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	eovig_1 $e |- ( ( x e. R /\ y e. S ) -> E* z ph ) $.
	eovig_2 $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	ovig $p |- ( ( A e. R /\ B e. S /\ C e. D ) -> ( ps -> ( A F B ) = C ) ) $= fovig_5 fovig_9 wcel fovig_6 fovig_10 wcel fovig_7 fovig_8 wcel w3a fovig_5 fovig_9 wcel fovig_6 fovig_10 wcel wa fovig_1 fovig_5 fovig_6 fovig_11 co fovig_7 wceq fovig_5 fovig_9 wcel fovig_6 fovig_10 wcel fovig_7 fovig_8 wcel 3simpa fovig_2 sup_set_class fovig_9 wcel fovig_3 sup_set_class fovig_10 wcel wa fovig_0 wa fovig_5 fovig_9 wcel fovig_6 fovig_10 wcel wa fovig_1 wa fovig_2 fovig_3 fovig_4 fovig_5 fovig_6 fovig_7 fovig_11 fovig_9 fovig_10 fovig_8 fovig_2 sup_set_class fovig_5 wceq fovig_3 sup_set_class fovig_6 wceq fovig_4 sup_set_class fovig_7 wceq w3a fovig_2 sup_set_class fovig_9 wcel fovig_3 sup_set_class fovig_10 wcel wa fovig_5 fovig_9 wcel fovig_6 fovig_10 wcel wa fovig_0 fovig_1 fovig_2 sup_set_class fovig_5 wceq fovig_3 sup_set_class fovig_6 wceq fovig_2 sup_set_class fovig_9 wcel fovig_3 sup_set_class fovig_10 wcel wa fovig_5 fovig_9 wcel fovig_6 fovig_10 wcel wa wb fovig_4 sup_set_class fovig_7 wceq fovig_2 sup_set_class fovig_5 wceq fovig_2 sup_set_class fovig_9 wcel fovig_5 fovig_9 wcel fovig_3 sup_set_class fovig_6 wceq fovig_3 sup_set_class fovig_10 wcel fovig_6 fovig_10 wcel fovig_2 sup_set_class fovig_5 fovig_9 eleq1 fovig_3 sup_set_class fovig_6 fovig_10 eleq1 bi2anan9 3adant3 eovig_0 anbi12d fovig_2 sup_set_class fovig_9 wcel fovig_3 sup_set_class fovig_10 wcel wa fovig_0 wa fovig_4 wmo fovig_2 sup_set_class fovig_9 wcel fovig_3 sup_set_class fovig_10 wcel wa fovig_0 fovig_4 wmo wi eovig_1 fovig_2 sup_set_class fovig_9 wcel fovig_3 sup_set_class fovig_10 wcel wa fovig_0 fovig_4 moanimv mpbir eovig_2 ovigg mpand $.
$}
$( /* Value of a function given by the "maps to" notation.  (This is the
       operation analog of ~ fvmpt2 .)  (Contributed by NM, 21-Feb-2004.)
       (Revised by Mario Carneiro, 1-Sep-2015.) */

$)
${
	$d x y z $.
	$d z A $.
	$d z B $.
	$d z C $.
	$d z F $.
	iovmpt4g_0 $f set z $.
	fovmpt4g_0 $f set x $.
	fovmpt4g_1 $f set y $.
	fovmpt4g_2 $f class A $.
	fovmpt4g_3 $f class B $.
	fovmpt4g_4 $f class C $.
	fovmpt4g_5 $f class F $.
	fovmpt4g_6 $f class V $.
	eovmpt4g_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	ovmpt4g $p |- ( ( x e. A /\ y e. B /\ C e. V ) -> ( x F y ) = C ) $= fovmpt4g_0 sup_set_class fovmpt4g_2 wcel fovmpt4g_1 sup_set_class fovmpt4g_3 wcel fovmpt4g_4 fovmpt4g_6 wcel fovmpt4g_0 sup_set_class fovmpt4g_1 sup_set_class fovmpt4g_5 co fovmpt4g_4 wceq fovmpt4g_4 fovmpt4g_6 wcel iovmpt4g_0 sup_set_class fovmpt4g_4 wceq iovmpt4g_0 wex fovmpt4g_0 sup_set_class fovmpt4g_2 wcel fovmpt4g_1 sup_set_class fovmpt4g_3 wcel wa fovmpt4g_0 sup_set_class fovmpt4g_1 sup_set_class fovmpt4g_5 co fovmpt4g_4 wceq iovmpt4g_0 fovmpt4g_4 fovmpt4g_6 elisset fovmpt4g_0 sup_set_class fovmpt4g_2 wcel fovmpt4g_1 sup_set_class fovmpt4g_3 wcel wa iovmpt4g_0 sup_set_class fovmpt4g_4 wceq fovmpt4g_0 sup_set_class fovmpt4g_1 sup_set_class fovmpt4g_5 co fovmpt4g_4 wceq iovmpt4g_0 iovmpt4g_0 sup_set_class fovmpt4g_4 wceq fovmpt4g_0 sup_set_class fovmpt4g_1 sup_set_class fovmpt4g_5 co iovmpt4g_0 sup_set_class wceq fovmpt4g_0 sup_set_class fovmpt4g_1 sup_set_class fovmpt4g_5 co fovmpt4g_4 wceq fovmpt4g_0 sup_set_class fovmpt4g_2 wcel fovmpt4g_1 sup_set_class fovmpt4g_3 wcel wa iovmpt4g_0 sup_set_class fovmpt4g_4 wceq fovmpt4g_0 fovmpt4g_1 iovmpt4g_0 fovmpt4g_2 fovmpt4g_3 fovmpt4g_5 iovmpt4g_0 sup_set_class fovmpt4g_4 wceq iovmpt4g_0 wmo fovmpt4g_0 sup_set_class fovmpt4g_2 wcel fovmpt4g_1 sup_set_class fovmpt4g_3 wcel wa iovmpt4g_0 fovmpt4g_4 moeq a1i fovmpt4g_5 fovmpt4g_0 fovmpt4g_1 fovmpt4g_2 fovmpt4g_3 fovmpt4g_4 cmpt2 fovmpt4g_0 sup_set_class fovmpt4g_2 wcel fovmpt4g_1 sup_set_class fovmpt4g_3 wcel wa iovmpt4g_0 sup_set_class fovmpt4g_4 wceq wa fovmpt4g_0 fovmpt4g_1 iovmpt4g_0 coprab eovmpt4g_0 fovmpt4g_0 fovmpt4g_1 iovmpt4g_0 fovmpt4g_2 fovmpt4g_3 fovmpt4g_4 df-mpt2 eqtri ovidi iovmpt4g_0 sup_set_class fovmpt4g_4 fovmpt4g_0 sup_set_class fovmpt4g_1 sup_set_class fovmpt4g_5 co eqeq2 mpbidi exlimdv syl5 3impia $.
$}
$( /* Value of a function given by the "maps to" notation, expressed using
       explicit substitution.  (Contributed by Mario Carneiro, 30-Apr-2015.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	fovmpt2s_0 $f set x $.
	fovmpt2s_1 $f set y $.
	fovmpt2s_2 $f class A $.
	fovmpt2s_3 $f class B $.
	fovmpt2s_4 $f class C $.
	fovmpt2s_5 $f class D $.
	fovmpt2s_6 $f class R $.
	fovmpt2s_7 $f class F $.
	fovmpt2s_8 $f class V $.
	eovmpt2s_0 $e |- F = ( x e. C , y e. D |-> R ) $.
	ovmpt2s $p |- ( ( A e. C /\ B e. D /\ [_ A / x ]_ [_ B / y ]_ R e. V ) -> ( A F B ) = [_ A / x ]_ [_ B / y ]_ R ) $= fovmpt2s_2 fovmpt2s_4 wcel fovmpt2s_3 fovmpt2s_5 wcel fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb fovmpt2s_8 wcel fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb wceq fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb fovmpt2s_8 wcel fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb cvv wcel fovmpt2s_2 fovmpt2s_4 wcel fovmpt2s_3 fovmpt2s_5 wcel wa fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb wceq fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb fovmpt2s_8 elex fovmpt2s_2 fovmpt2s_4 wcel fovmpt2s_3 fovmpt2s_5 wcel wa fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb cvv wcel fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb wceq fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb cvv wcel fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb wceq fovmpt2s_6 cvv wcel fovmpt2s_0 sup_set_class fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_6 wceq wi fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb cvv wcel fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb wceq wi fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb cvv wcel fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb wceq wi fovmpt2s_0 fovmpt2s_1 fovmpt2s_2 fovmpt2s_3 fovmpt2s_4 fovmpt2s_5 fovmpt2s_0 fovmpt2s_2 nfcv fovmpt2s_1 fovmpt2s_2 nfcv fovmpt2s_1 fovmpt2s_3 nfcv fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb cvv wcel fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb wceq fovmpt2s_0 fovmpt2s_0 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb cvv fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 nfcsb1v nfel1 fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 fovmpt2s_0 fovmpt2s_2 nfcv fovmpt2s_0 fovmpt2s_7 fovmpt2s_0 fovmpt2s_1 fovmpt2s_4 fovmpt2s_5 fovmpt2s_6 cmpt2 eovmpt2s_0 fovmpt2s_0 fovmpt2s_1 fovmpt2s_4 fovmpt2s_5 fovmpt2s_6 nfmpt21 nfcxfr fovmpt2s_0 fovmpt2s_1 sup_set_class nfcv nfov fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 nfcsb1v nfeq nfim fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb cvv wcel fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb wceq fovmpt2s_1 fovmpt2s_1 fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb cvv fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb nfcsb1v nfel1 fovmpt2s_1 fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb fovmpt2s_1 fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 fovmpt2s_1 fovmpt2s_2 nfcv fovmpt2s_1 fovmpt2s_7 fovmpt2s_0 fovmpt2s_1 fovmpt2s_4 fovmpt2s_5 fovmpt2s_6 cmpt2 eovmpt2s_0 fovmpt2s_0 fovmpt2s_1 fovmpt2s_4 fovmpt2s_5 fovmpt2s_6 nfmpt22 nfcxfr fovmpt2s_1 fovmpt2s_3 nfcv nfov fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb nfcsb1v nfeq nfim fovmpt2s_0 sup_set_class fovmpt2s_2 wceq fovmpt2s_6 cvv wcel fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb cvv wcel fovmpt2s_0 sup_set_class fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_6 wceq fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb wceq fovmpt2s_0 sup_set_class fovmpt2s_2 wceq fovmpt2s_6 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb cvv fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csbeq1a eleq1d fovmpt2s_0 sup_set_class fovmpt2s_2 wceq fovmpt2s_0 sup_set_class fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_6 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb fovmpt2s_0 sup_set_class fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 oveq1 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csbeq1a eqeq12d imbi12d fovmpt2s_1 sup_set_class fovmpt2s_3 wceq fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb cvv wcel fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb cvv wcel fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb wceq fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb wceq fovmpt2s_1 sup_set_class fovmpt2s_3 wceq fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb cvv fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csbeq1a eleq1d fovmpt2s_1 sup_set_class fovmpt2s_3 wceq fovmpt2s_2 fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb fovmpt2s_1 sup_set_class fovmpt2s_3 fovmpt2s_2 fovmpt2s_7 oveq2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csbeq1a eqeq12d imbi12d fovmpt2s_0 sup_set_class fovmpt2s_4 wcel fovmpt2s_1 sup_set_class fovmpt2s_5 wcel fovmpt2s_6 cvv wcel fovmpt2s_0 sup_set_class fovmpt2s_1 sup_set_class fovmpt2s_7 co fovmpt2s_6 wceq fovmpt2s_0 fovmpt2s_1 fovmpt2s_4 fovmpt2s_5 fovmpt2s_6 fovmpt2s_7 cvv eovmpt2s_0 ovmpt4g 3expia vtocl2gaf fovmpt2s_2 fovmpt2s_4 wcel fovmpt2s_3 fovmpt2s_5 wcel wa fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb cvv fovmpt2s_0 fovmpt2s_1 fovmpt2s_2 fovmpt2s_3 fovmpt2s_6 fovmpt2s_4 fovmpt2s_5 csbcomg eleq1d fovmpt2s_2 fovmpt2s_4 wcel fovmpt2s_3 fovmpt2s_5 wcel wa fovmpt2s_0 fovmpt2s_2 fovmpt2s_1 fovmpt2s_3 fovmpt2s_6 csb csb fovmpt2s_1 fovmpt2s_3 fovmpt2s_0 fovmpt2s_2 fovmpt2s_6 csb csb fovmpt2s_2 fovmpt2s_3 fovmpt2s_7 co fovmpt2s_0 fovmpt2s_1 fovmpt2s_2 fovmpt2s_3 fovmpt2s_6 fovmpt2s_4 fovmpt2s_5 csbcomg eqeq2d 3imtr4d syl5 3impia $.
$}
$( /* The value of an operation class abstraction.  A version of ~ ovmpt2g
       using bound-variable hypotheses.  (Contributed by NM, 17-Aug-2006.)
       (Revised by Mario Carneiro, 19-Dec-2013.) */

$)
${
	$d x y C $.
	$d x y D $.
	fov2gf_0 $f set x $.
	fov2gf_1 $f set y $.
	fov2gf_2 $f class A $.
	fov2gf_3 $f class B $.
	fov2gf_4 $f class C $.
	fov2gf_5 $f class D $.
	fov2gf_6 $f class R $.
	fov2gf_7 $f class S $.
	fov2gf_8 $f class F $.
	fov2gf_9 $f class G $.
	fov2gf_10 $f class H $.
	eov2gf_0 $e |- F/_ x A $.
	eov2gf_1 $e |- F/_ y A $.
	eov2gf_2 $e |- F/_ y B $.
	eov2gf_3 $e |- F/_ x G $.
	eov2gf_4 $e |- F/_ y S $.
	eov2gf_5 $e |- ( x = A -> R = G ) $.
	eov2gf_6 $e |- ( y = B -> G = S ) $.
	eov2gf_7 $e |- F = ( x e. C , y e. D |-> R ) $.
	ov2gf $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $= fov2gf_2 fov2gf_4 wcel fov2gf_3 fov2gf_5 wcel fov2gf_7 fov2gf_10 wcel fov2gf_2 fov2gf_3 fov2gf_8 co fov2gf_7 wceq fov2gf_7 fov2gf_10 wcel fov2gf_7 cvv wcel fov2gf_2 fov2gf_4 wcel fov2gf_3 fov2gf_5 wcel wa fov2gf_2 fov2gf_3 fov2gf_8 co fov2gf_7 wceq fov2gf_7 fov2gf_10 elex fov2gf_6 cvv wcel fov2gf_0 sup_set_class fov2gf_1 sup_set_class fov2gf_8 co fov2gf_6 wceq wi fov2gf_9 cvv wcel fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 co fov2gf_9 wceq wi fov2gf_7 cvv wcel fov2gf_2 fov2gf_3 fov2gf_8 co fov2gf_7 wceq wi fov2gf_0 fov2gf_1 fov2gf_2 fov2gf_3 fov2gf_4 fov2gf_5 eov2gf_0 eov2gf_1 eov2gf_2 fov2gf_9 cvv wcel fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 co fov2gf_9 wceq fov2gf_0 fov2gf_0 fov2gf_9 cvv eov2gf_3 nfel1 fov2gf_0 fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 co fov2gf_9 fov2gf_0 fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 eov2gf_0 fov2gf_0 fov2gf_8 fov2gf_0 fov2gf_1 fov2gf_4 fov2gf_5 fov2gf_6 cmpt2 eov2gf_7 fov2gf_0 fov2gf_1 fov2gf_4 fov2gf_5 fov2gf_6 nfmpt21 nfcxfr fov2gf_0 fov2gf_1 sup_set_class nfcv nfov eov2gf_3 nfeq nfim fov2gf_7 cvv wcel fov2gf_2 fov2gf_3 fov2gf_8 co fov2gf_7 wceq fov2gf_1 fov2gf_1 fov2gf_7 cvv eov2gf_4 nfel1 fov2gf_1 fov2gf_2 fov2gf_3 fov2gf_8 co fov2gf_7 fov2gf_1 fov2gf_2 fov2gf_3 fov2gf_8 eov2gf_1 fov2gf_1 fov2gf_8 fov2gf_0 fov2gf_1 fov2gf_4 fov2gf_5 fov2gf_6 cmpt2 eov2gf_7 fov2gf_0 fov2gf_1 fov2gf_4 fov2gf_5 fov2gf_6 nfmpt22 nfcxfr eov2gf_2 nfov eov2gf_4 nfeq nfim fov2gf_0 sup_set_class fov2gf_2 wceq fov2gf_6 cvv wcel fov2gf_9 cvv wcel fov2gf_0 sup_set_class fov2gf_1 sup_set_class fov2gf_8 co fov2gf_6 wceq fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 co fov2gf_9 wceq fov2gf_0 sup_set_class fov2gf_2 wceq fov2gf_6 fov2gf_9 cvv eov2gf_5 eleq1d fov2gf_0 sup_set_class fov2gf_2 wceq fov2gf_0 sup_set_class fov2gf_1 sup_set_class fov2gf_8 co fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 co fov2gf_6 fov2gf_9 fov2gf_0 sup_set_class fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 oveq1 eov2gf_5 eqeq12d imbi12d fov2gf_1 sup_set_class fov2gf_3 wceq fov2gf_9 cvv wcel fov2gf_7 cvv wcel fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 co fov2gf_9 wceq fov2gf_2 fov2gf_3 fov2gf_8 co fov2gf_7 wceq fov2gf_1 sup_set_class fov2gf_3 wceq fov2gf_9 fov2gf_7 cvv eov2gf_6 eleq1d fov2gf_1 sup_set_class fov2gf_3 wceq fov2gf_2 fov2gf_1 sup_set_class fov2gf_8 co fov2gf_2 fov2gf_3 fov2gf_8 co fov2gf_9 fov2gf_7 fov2gf_1 sup_set_class fov2gf_3 fov2gf_2 fov2gf_8 oveq2 eov2gf_6 eqeq12d imbi12d fov2gf_0 sup_set_class fov2gf_4 wcel fov2gf_1 sup_set_class fov2gf_5 wcel fov2gf_6 cvv wcel fov2gf_0 sup_set_class fov2gf_1 sup_set_class fov2gf_8 co fov2gf_6 wceq fov2gf_0 fov2gf_1 fov2gf_4 fov2gf_5 fov2gf_6 fov2gf_8 cvv eov2gf_7 ovmpt4g 3expia vtocl2gaf syl5 3impia $.
$}
$( /* Value of an operation given by a maps-to rule, deduction form.
         (Contributed by Mario Carneiro, 29-Dec-2014.) */

$)
$v L $.
${
	$d x y $.
	$d x A $.
	$d y B $.
	fovmpt2dxf_0 $f wff ph $.
	fovmpt2dxf_1 $f set x $.
	fovmpt2dxf_2 $f set y $.
	fovmpt2dxf_3 $f class A $.
	fovmpt2dxf_4 $f class B $.
	fovmpt2dxf_5 $f class C $.
	fovmpt2dxf_6 $f class D $.
	fovmpt2dxf_7 $f class R $.
	fovmpt2dxf_8 $f class S $.
	fovmpt2dxf_9 $f class F $.
	fovmpt2dxf_10 $f class L $.
	fovmpt2dxf_11 $f class X $.
	eovmpt2dxf_0 $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
	eovmpt2dxf_1 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
	eovmpt2dxf_2 $e |- ( ( ph /\ x = A ) -> D = L ) $.
	eovmpt2dxf_3 $e |- ( ph -> A e. C ) $.
	eovmpt2dxf_4 $e |- ( ph -> B e. L ) $.
	eovmpt2dxf_5 $e |- ( ph -> S e. X ) $.
	eovmpt2dxf_6 $e |- F/ x ph $.
	eovmpt2dxf_7 $e |- F/ y ph $.
	eovmpt2dxf_8 $e |- F/_ y A $.
	eovmpt2dxf_9 $e |- F/_ x B $.
	eovmpt2dxf_10 $e |- F/_ x S $.
	eovmpt2dxf_11 $e |- F/_ y S $.
	ovmpt2dxf $p |- ( ph -> ( A F B ) = S ) $= fovmpt2dxf_0 fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_9 co fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 fovmpt2dxf_0 fovmpt2dxf_9 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 fovmpt2dxf_3 fovmpt2dxf_4 eovmpt2dxf_0 oveqd fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 fovmpt2dxf_4 wsbc fovmpt2dxf_1 fovmpt2dxf_3 wsbc fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 wceq fovmpt2dxf_0 fovmpt2dxf_3 fovmpt2dxf_5 wcel fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 fovmpt2dxf_4 wsbc fovmpt2dxf_1 wal fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 fovmpt2dxf_4 wsbc fovmpt2dxf_1 fovmpt2dxf_3 wsbc eovmpt2dxf_3 fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 fovmpt2dxf_4 wsbc fovmpt2dxf_1 eovmpt2dxf_6 fovmpt2dxf_0 fovmpt2dxf_4 fovmpt2dxf_10 wcel fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 wal fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 fovmpt2dxf_4 wsbc eovmpt2dxf_4 fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 eovmpt2dxf_7 fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_0 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 cvv fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 eqid ovmpt4g a1i alrimi fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 fovmpt2dxf_4 fovmpt2dxf_10 spsbc sylc alrimi fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 fovmpt2dxf_4 wsbc fovmpt2dxf_1 fovmpt2dxf_3 fovmpt2dxf_5 spsbc sylc fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_2 fovmpt2dxf_4 wsbc fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 wceq fovmpt2dxf_1 fovmpt2dxf_3 fovmpt2dxf_5 eovmpt2dxf_3 fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 wceq fovmpt2dxf_2 fovmpt2dxf_4 fovmpt2dxf_10 fovmpt2dxf_0 fovmpt2dxf_4 fovmpt2dxf_10 wcel fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq eovmpt2dxf_4 adantr fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq wa fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 wceq fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq wa fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq wi wb fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq wa fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 fovmpt2dxf_5 fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq simplr fovmpt2dxf_0 fovmpt2dxf_3 fovmpt2dxf_5 wcel fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq eovmpt2dxf_3 ad2antrr eqeltrd fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_4 fovmpt2dxf_10 wcel fovmpt2dxf_0 fovmpt2dxf_4 fovmpt2dxf_10 wcel fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq eovmpt2dxf_4 ad2antrr fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 fovmpt2dxf_6 fovmpt2dxf_10 fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq simpr fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_6 fovmpt2dxf_10 wceq fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq eovmpt2dxf_2 adantr eleq12d mpbird fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq wa fovmpt2dxf_7 fovmpt2dxf_8 cvv fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq fovmpt2dxf_7 fovmpt2dxf_8 wceq eovmpt2dxf_1 anassrs fovmpt2dxf_0 fovmpt2dxf_8 cvv wcel fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq fovmpt2dxf_0 fovmpt2dxf_8 fovmpt2dxf_11 wcel fovmpt2dxf_8 cvv wcel eovmpt2dxf_5 fovmpt2dxf_8 fovmpt2dxf_11 elex syl ad2antrr eqeltrd fovmpt2dxf_1 sup_set_class fovmpt2dxf_5 wcel fovmpt2dxf_2 sup_set_class fovmpt2dxf_6 wcel fovmpt2dxf_7 cvv wcel w3a fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 wceq biimt syl3anc fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq wa fovmpt2dxf_1 sup_set_class fovmpt2dxf_2 sup_set_class fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_7 fovmpt2dxf_8 fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq wa fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq simplr fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq simpr oveq12d fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq fovmpt2dxf_2 sup_set_class fovmpt2dxf_4 wceq fovmpt2dxf_7 fovmpt2dxf_8 wceq eovmpt2dxf_1 anassrs eqeq12d bitr3d fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq fovmpt2dxf_2 eovmpt2dxf_7 fovmpt2dxf_2 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 eovmpt2dxf_8 nfeq2 nfan fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 wceq fovmpt2dxf_2 wnf fovmpt2dxf_0 fovmpt2dxf_1 sup_set_class fovmpt2dxf_3 wceq wa fovmpt2dxf_2 fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 fovmpt2dxf_2 fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 eovmpt2dxf_8 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 nfmpt22 fovmpt2dxf_2 fovmpt2dxf_4 nfcv nfov eovmpt2dxf_11 nfeq a1i sbciedf eovmpt2dxf_6 fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 wceq fovmpt2dxf_1 wnf fovmpt2dxf_0 fovmpt2dxf_1 fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 co fovmpt2dxf_8 fovmpt2dxf_1 fovmpt2dxf_3 fovmpt2dxf_4 fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 cmpt2 fovmpt2dxf_1 fovmpt2dxf_3 nfcv fovmpt2dxf_1 fovmpt2dxf_2 fovmpt2dxf_5 fovmpt2dxf_6 fovmpt2dxf_7 nfmpt21 eovmpt2dxf_9 nfov eovmpt2dxf_10 nfeq a1i sbciedf mpbid eqtrd $.
$}
$( /* Value of an operation given by a maps-to rule, deduction form.
       (Contributed by Mario Carneiro, 29-Dec-2014.) */

$)
${
	$d x y $.
	$d x A $.
	$d y B $.
	$d y A $.
	$d x B $.
	$d x y S $.
	$d x y ph $.
	fovmpt2dx_0 $f wff ph $.
	fovmpt2dx_1 $f set x $.
	fovmpt2dx_2 $f set y $.
	fovmpt2dx_3 $f class A $.
	fovmpt2dx_4 $f class B $.
	fovmpt2dx_5 $f class C $.
	fovmpt2dx_6 $f class D $.
	fovmpt2dx_7 $f class R $.
	fovmpt2dx_8 $f class S $.
	fovmpt2dx_9 $f class F $.
	fovmpt2dx_10 $f class L $.
	fovmpt2dx_11 $f class X $.
	eovmpt2dx_0 $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
	eovmpt2dx_1 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
	eovmpt2dx_2 $e |- ( ( ph /\ x = A ) -> D = L ) $.
	eovmpt2dx_3 $e |- ( ph -> A e. C ) $.
	eovmpt2dx_4 $e |- ( ph -> B e. L ) $.
	eovmpt2dx_5 $e |- ( ph -> S e. X ) $.
	ovmpt2dx $p |- ( ph -> ( A F B ) = S ) $= fovmpt2dx_0 fovmpt2dx_1 fovmpt2dx_2 fovmpt2dx_3 fovmpt2dx_4 fovmpt2dx_5 fovmpt2dx_6 fovmpt2dx_7 fovmpt2dx_8 fovmpt2dx_9 fovmpt2dx_10 fovmpt2dx_11 eovmpt2dx_0 eovmpt2dx_1 eovmpt2dx_2 eovmpt2dx_3 eovmpt2dx_4 eovmpt2dx_5 fovmpt2dx_0 fovmpt2dx_1 nfv fovmpt2dx_0 fovmpt2dx_2 nfv fovmpt2dx_2 fovmpt2dx_3 nfcv fovmpt2dx_1 fovmpt2dx_4 nfcv fovmpt2dx_1 fovmpt2dx_8 nfcv fovmpt2dx_2 fovmpt2dx_8 nfcv ovmpt2dxf $.
$}
$( /* Value of an operation given by a maps-to rule, deduction form.
       (Contributed by Mario Carneiro, 7-Dec-2014.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y S $.
	$d x y ph $.
	fovmpt2d_0 $f wff ph $.
	fovmpt2d_1 $f set x $.
	fovmpt2d_2 $f set y $.
	fovmpt2d_3 $f class A $.
	fovmpt2d_4 $f class B $.
	fovmpt2d_5 $f class C $.
	fovmpt2d_6 $f class D $.
	fovmpt2d_7 $f class R $.
	fovmpt2d_8 $f class S $.
	fovmpt2d_9 $f class F $.
	fovmpt2d_10 $f class X $.
	eovmpt2d_0 $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
	eovmpt2d_1 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
	eovmpt2d_2 $e |- ( ph -> A e. C ) $.
	eovmpt2d_3 $e |- ( ph -> B e. D ) $.
	eovmpt2d_4 $e |- ( ph -> S e. X ) $.
	ovmpt2d $p |- ( ph -> ( A F B ) = S ) $= fovmpt2d_0 fovmpt2d_1 fovmpt2d_2 fovmpt2d_3 fovmpt2d_4 fovmpt2d_5 fovmpt2d_6 fovmpt2d_7 fovmpt2d_8 fovmpt2d_9 fovmpt2d_6 fovmpt2d_10 eovmpt2d_0 eovmpt2d_1 fovmpt2d_0 fovmpt2d_1 sup_set_class fovmpt2d_3 wceq wa fovmpt2d_6 eqidd eovmpt2d_2 eovmpt2d_3 eovmpt2d_4 ovmpt2dx $.
$}
$( /* The value of an operation class abstraction.  Variant of ~ ovmpt2ga
       which does not require ` D ` and ` x ` to be distinct.  (Contributed by
       Jeff Madsen, 10-Jun-2010.)  (Revised by Mario Carneiro, 20-Dec-2013.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y L $.
	$d x y S $.
	fovmpt2x_0 $f set x $.
	fovmpt2x_1 $f set y $.
	fovmpt2x_2 $f class A $.
	fovmpt2x_3 $f class B $.
	fovmpt2x_4 $f class C $.
	fovmpt2x_5 $f class D $.
	fovmpt2x_6 $f class R $.
	fovmpt2x_7 $f class S $.
	fovmpt2x_8 $f class F $.
	fovmpt2x_9 $f class H $.
	fovmpt2x_10 $f class L $.
	eovmpt2x_0 $e |- ( ( x = A /\ y = B ) -> R = S ) $.
	eovmpt2x_1 $e |- ( x = A -> D = L ) $.
	eovmpt2x_2 $e |- F = ( x e. C , y e. D |-> R ) $.
	ovmpt2x $p |- ( ( A e. C /\ B e. L /\ S e. H ) -> ( A F B ) = S ) $= fovmpt2x_7 fovmpt2x_9 wcel fovmpt2x_2 fovmpt2x_4 wcel fovmpt2x_3 fovmpt2x_10 wcel fovmpt2x_7 cvv wcel fovmpt2x_2 fovmpt2x_3 fovmpt2x_8 co fovmpt2x_7 wceq fovmpt2x_7 fovmpt2x_9 elex fovmpt2x_2 fovmpt2x_4 wcel fovmpt2x_3 fovmpt2x_10 wcel fovmpt2x_7 cvv wcel w3a fovmpt2x_0 fovmpt2x_1 fovmpt2x_2 fovmpt2x_3 fovmpt2x_4 fovmpt2x_5 fovmpt2x_6 fovmpt2x_7 fovmpt2x_8 fovmpt2x_10 cvv fovmpt2x_8 fovmpt2x_0 fovmpt2x_1 fovmpt2x_4 fovmpt2x_5 fovmpt2x_6 cmpt2 wceq fovmpt2x_2 fovmpt2x_4 wcel fovmpt2x_3 fovmpt2x_10 wcel fovmpt2x_7 cvv wcel w3a eovmpt2x_2 a1i fovmpt2x_0 sup_set_class fovmpt2x_2 wceq fovmpt2x_1 sup_set_class fovmpt2x_3 wceq wa fovmpt2x_6 fovmpt2x_7 wceq fovmpt2x_2 fovmpt2x_4 wcel fovmpt2x_3 fovmpt2x_10 wcel fovmpt2x_7 cvv wcel w3a eovmpt2x_0 adantl fovmpt2x_0 sup_set_class fovmpt2x_2 wceq fovmpt2x_5 fovmpt2x_10 wceq fovmpt2x_2 fovmpt2x_4 wcel fovmpt2x_3 fovmpt2x_10 wcel fovmpt2x_7 cvv wcel w3a eovmpt2x_1 adantl fovmpt2x_2 fovmpt2x_4 wcel fovmpt2x_3 fovmpt2x_10 wcel fovmpt2x_7 cvv wcel simp1 fovmpt2x_2 fovmpt2x_4 wcel fovmpt2x_3 fovmpt2x_10 wcel fovmpt2x_7 cvv wcel simp2 fovmpt2x_2 fovmpt2x_4 wcel fovmpt2x_3 fovmpt2x_10 wcel fovmpt2x_7 cvv wcel simp3 ovmpt2dx syl3an3 $.
$}
$( /* Value of an operation given by a maps-to rule.  (Contributed by Mario
       Carneiro, 19-Dec-2013.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	$d x y S $.
	fovmpt2ga_0 $f set x $.
	fovmpt2ga_1 $f set y $.
	fovmpt2ga_2 $f class A $.
	fovmpt2ga_3 $f class B $.
	fovmpt2ga_4 $f class C $.
	fovmpt2ga_5 $f class D $.
	fovmpt2ga_6 $f class R $.
	fovmpt2ga_7 $f class S $.
	fovmpt2ga_8 $f class F $.
	fovmpt2ga_9 $f class H $.
	eovmpt2ga_0 $e |- ( ( x = A /\ y = B ) -> R = S ) $.
	eovmpt2ga_1 $e |- F = ( x e. C , y e. D |-> R ) $.
	ovmpt2ga $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $= fovmpt2ga_7 fovmpt2ga_9 wcel fovmpt2ga_2 fovmpt2ga_4 wcel fovmpt2ga_3 fovmpt2ga_5 wcel fovmpt2ga_7 cvv wcel fovmpt2ga_2 fovmpt2ga_3 fovmpt2ga_8 co fovmpt2ga_7 wceq fovmpt2ga_7 fovmpt2ga_9 elex fovmpt2ga_2 fovmpt2ga_4 wcel fovmpt2ga_3 fovmpt2ga_5 wcel fovmpt2ga_7 cvv wcel w3a fovmpt2ga_0 fovmpt2ga_1 fovmpt2ga_2 fovmpt2ga_3 fovmpt2ga_4 fovmpt2ga_5 fovmpt2ga_6 fovmpt2ga_7 fovmpt2ga_8 cvv fovmpt2ga_8 fovmpt2ga_0 fovmpt2ga_1 fovmpt2ga_4 fovmpt2ga_5 fovmpt2ga_6 cmpt2 wceq fovmpt2ga_2 fovmpt2ga_4 wcel fovmpt2ga_3 fovmpt2ga_5 wcel fovmpt2ga_7 cvv wcel w3a eovmpt2ga_1 a1i fovmpt2ga_0 sup_set_class fovmpt2ga_2 wceq fovmpt2ga_1 sup_set_class fovmpt2ga_3 wceq wa fovmpt2ga_6 fovmpt2ga_7 wceq fovmpt2ga_2 fovmpt2ga_4 wcel fovmpt2ga_3 fovmpt2ga_5 wcel fovmpt2ga_7 cvv wcel w3a eovmpt2ga_0 adantl fovmpt2ga_2 fovmpt2ga_4 wcel fovmpt2ga_3 fovmpt2ga_5 wcel fovmpt2ga_7 cvv wcel simp1 fovmpt2ga_2 fovmpt2ga_4 wcel fovmpt2ga_3 fovmpt2ga_5 wcel fovmpt2ga_7 cvv wcel simp2 fovmpt2ga_2 fovmpt2ga_4 wcel fovmpt2ga_3 fovmpt2ga_5 wcel fovmpt2ga_7 cvv wcel simp3 ovmpt2d syl3an3 $.
$}
$( /* Value of an operation given by a maps-to rule.  (Contributed by NM,
       19-Dec-2013.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	$d x y S $.
	fovmpt2a_0 $f set x $.
	fovmpt2a_1 $f set y $.
	fovmpt2a_2 $f class A $.
	fovmpt2a_3 $f class B $.
	fovmpt2a_4 $f class C $.
	fovmpt2a_5 $f class D $.
	fovmpt2a_6 $f class R $.
	fovmpt2a_7 $f class S $.
	fovmpt2a_8 $f class F $.
	eovmpt2a_0 $e |- ( ( x = A /\ y = B ) -> R = S ) $.
	eovmpt2a_1 $e |- F = ( x e. C , y e. D |-> R ) $.
	eovmpt2a_2 $e |- S e. _V $.
	ovmpt2a $p |- ( ( A e. C /\ B e. D ) -> ( A F B ) = S ) $= fovmpt2a_2 fovmpt2a_4 wcel fovmpt2a_3 fovmpt2a_5 wcel fovmpt2a_7 cvv wcel fovmpt2a_2 fovmpt2a_3 fovmpt2a_8 co fovmpt2a_7 wceq eovmpt2a_2 fovmpt2a_0 fovmpt2a_1 fovmpt2a_2 fovmpt2a_3 fovmpt2a_4 fovmpt2a_5 fovmpt2a_6 fovmpt2a_7 fovmpt2a_8 cvv eovmpt2a_0 eovmpt2a_1 ovmpt2ga mp3an3 $.
$}
$( /* Alternate deduction version of ~ ovmpt2 , suitable for iteration.
         (Contributed by Mario Carneiro, 7-Jan-2017.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x y ph $.
	fovmpt2df_0 $f wff ph $.
	fovmpt2df_1 $f wff ps $.
	fovmpt2df_2 $f set x $.
	fovmpt2df_3 $f set y $.
	fovmpt2df_4 $f class A $.
	fovmpt2df_5 $f class B $.
	fovmpt2df_6 $f class C $.
	fovmpt2df_7 $f class D $.
	fovmpt2df_8 $f class R $.
	fovmpt2df_9 $f class F $.
	fovmpt2df_10 $f class V $.
	eovmpt2df_0 $e |- ( ph -> A e. C ) $.
	eovmpt2df_1 $e |- ( ( ph /\ x = A ) -> B e. D ) $.
	eovmpt2df_2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V ) $.
	eovmpt2df_3 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ( A F B ) = R -> ps ) ) $.
	eovmpt2df_4 $e |- F/_ x F $.
	eovmpt2df_5 $e |- F/ x ps $.
	eovmpt2df_6 $e |- F/_ y F $.
	eovmpt2df_7 $e |- F/ y ps $.
	ovmpt2df $p |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ps ) ) $= fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_2 wex fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_1 wi fovmpt2df_0 fovmpt2df_4 cvv wcel fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_2 wex fovmpt2df_0 fovmpt2df_4 fovmpt2df_6 wcel fovmpt2df_4 cvv wcel eovmpt2df_0 fovmpt2df_4 fovmpt2df_6 elex syl fovmpt2df_2 fovmpt2df_4 isset sylib fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_1 wi fovmpt2df_2 fovmpt2df_0 fovmpt2df_2 nfv fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_1 fovmpt2df_2 fovmpt2df_2 fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 eovmpt2df_4 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 nfmpt21 nfeq eovmpt2df_5 nfim fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_1 wi fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq wa fovmpt2df_3 sup_set_class fovmpt2df_5 wceq fovmpt2df_3 wex fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_1 wi fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq wa fovmpt2df_5 cvv wcel fovmpt2df_3 sup_set_class fovmpt2df_5 wceq fovmpt2df_3 wex fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq wa fovmpt2df_5 fovmpt2df_7 wcel fovmpt2df_5 cvv wcel eovmpt2df_1 fovmpt2df_5 fovmpt2df_7 elex syl fovmpt2df_3 fovmpt2df_5 isset sylib fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq wa fovmpt2df_3 sup_set_class fovmpt2df_5 wceq fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_1 wi fovmpt2df_3 fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq wa fovmpt2df_3 nfv fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_1 fovmpt2df_3 fovmpt2df_3 fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 eovmpt2df_6 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 nfmpt22 nfeq eovmpt2df_7 nfim fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_1 wi fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 wceq fovmpt2df_4 fovmpt2df_5 fovmpt2df_9 co fovmpt2df_4 fovmpt2df_5 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 co wceq fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa wa fovmpt2df_1 fovmpt2df_4 fovmpt2df_5 fovmpt2df_9 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 oveq fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa wa fovmpt2df_4 fovmpt2df_5 fovmpt2df_9 co fovmpt2df_4 fovmpt2df_5 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 co wceq fovmpt2df_4 fovmpt2df_5 fovmpt2df_9 co fovmpt2df_8 wceq fovmpt2df_1 fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa wa fovmpt2df_4 fovmpt2df_5 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 co fovmpt2df_8 fovmpt2df_4 fovmpt2df_5 fovmpt2df_9 co fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa wa fovmpt2df_2 sup_set_class fovmpt2df_3 sup_set_class fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 co fovmpt2df_4 fovmpt2df_5 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 co fovmpt2df_8 fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa wa fovmpt2df_2 sup_set_class fovmpt2df_4 fovmpt2df_3 sup_set_class fovmpt2df_5 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq simprl fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq simprr oveq12d fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa wa fovmpt2df_2 sup_set_class fovmpt2df_6 wcel fovmpt2df_3 sup_set_class fovmpt2df_7 wcel fovmpt2df_8 fovmpt2df_10 wcel fovmpt2df_2 sup_set_class fovmpt2df_3 sup_set_class fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 co fovmpt2df_8 wceq fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa wa fovmpt2df_2 sup_set_class fovmpt2df_4 fovmpt2df_6 fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq simprl fovmpt2df_0 fovmpt2df_4 fovmpt2df_6 wcel fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa eovmpt2df_0 adantr eqeltrd fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq wa wa fovmpt2df_3 sup_set_class fovmpt2df_5 fovmpt2df_7 fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_3 sup_set_class fovmpt2df_5 wceq simprr fovmpt2df_0 fovmpt2df_2 sup_set_class fovmpt2df_4 wceq fovmpt2df_5 fovmpt2df_7 wcel fovmpt2df_3 sup_set_class fovmpt2df_5 wceq eovmpt2df_1 adantrr eqeltrd eovmpt2df_2 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 fovmpt2df_10 fovmpt2df_2 fovmpt2df_3 fovmpt2df_6 fovmpt2df_7 fovmpt2df_8 cmpt2 eqid ovmpt4g syl3anc eqtr3d eqeq2d eovmpt2df_3 sylbid syl5 expr exlimd mpd ex exlimd mpd $.
$}
$( /* Alternate deduction version of ~ ovmpt2 , suitable for iteration.
       (Contributed by Mario Carneiro, 7-Jan-2017.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x y ph $.
	$d x y F $.
	$d x y ps $.
	fovmpt2dv_0 $f wff ph $.
	fovmpt2dv_1 $f wff ps $.
	fovmpt2dv_2 $f set x $.
	fovmpt2dv_3 $f set y $.
	fovmpt2dv_4 $f class A $.
	fovmpt2dv_5 $f class B $.
	fovmpt2dv_6 $f class C $.
	fovmpt2dv_7 $f class D $.
	fovmpt2dv_8 $f class R $.
	fovmpt2dv_9 $f class F $.
	fovmpt2dv_10 $f class V $.
	eovmpt2dv_0 $e |- ( ph -> A e. C ) $.
	eovmpt2dv_1 $e |- ( ( ph /\ x = A ) -> B e. D ) $.
	eovmpt2dv_2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V ) $.
	eovmpt2dv_3 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ( A F B ) = R -> ps ) ) $.
	ovmpt2dv $p |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ps ) ) $= fovmpt2dv_0 fovmpt2dv_1 fovmpt2dv_2 fovmpt2dv_3 fovmpt2dv_4 fovmpt2dv_5 fovmpt2dv_6 fovmpt2dv_7 fovmpt2dv_8 fovmpt2dv_9 fovmpt2dv_10 eovmpt2dv_0 eovmpt2dv_1 eovmpt2dv_2 eovmpt2dv_3 fovmpt2dv_2 fovmpt2dv_9 nfcv fovmpt2dv_1 fovmpt2dv_2 nfv fovmpt2dv_3 fovmpt2dv_9 nfcv fovmpt2dv_1 fovmpt2dv_3 nfv ovmpt2df $.
$}
$( /* Alternate deduction version of ~ ovmpt2 , suitable for iteration.
       (Contributed by Mario Carneiro, 7-Jan-2017.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y ph $.
	$d x y S $.
	fovmpt2dv2_0 $f wff ph $.
	fovmpt2dv2_1 $f set x $.
	fovmpt2dv2_2 $f set y $.
	fovmpt2dv2_3 $f class A $.
	fovmpt2dv2_4 $f class B $.
	fovmpt2dv2_5 $f class C $.
	fovmpt2dv2_6 $f class D $.
	fovmpt2dv2_7 $f class R $.
	fovmpt2dv2_8 $f class S $.
	fovmpt2dv2_9 $f class F $.
	fovmpt2dv2_10 $f class V $.
	eovmpt2dv2_0 $e |- ( ph -> A e. C ) $.
	eovmpt2dv2_1 $e |- ( ( ph /\ x = A ) -> B e. D ) $.
	eovmpt2dv2_2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V ) $.
	eovmpt2dv2_3 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
	ovmpt2dv2 $p |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ( A F B ) = S ) ) $= fovmpt2dv2_0 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_9 co fovmpt2dv2_8 wceq fovmpt2dv2_9 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 wceq fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co fovmpt2dv2_8 wceq fovmpt2dv2_0 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 wceq fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co fovmpt2dv2_8 wceq fovmpt2dv2_0 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 eqidd fovmpt2dv2_0 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co fovmpt2dv2_8 wceq fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 fovmpt2dv2_10 eovmpt2dv2_0 eovmpt2dv2_1 eovmpt2dv2_2 fovmpt2dv2_0 fovmpt2dv2_1 sup_set_class fovmpt2dv2_3 wceq fovmpt2dv2_2 sup_set_class fovmpt2dv2_4 wceq wa wa fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co fovmpt2dv2_7 wceq fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co fovmpt2dv2_8 wceq fovmpt2dv2_0 fovmpt2dv2_1 sup_set_class fovmpt2dv2_3 wceq fovmpt2dv2_2 sup_set_class fovmpt2dv2_4 wceq wa wa fovmpt2dv2_7 fovmpt2dv2_8 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co eovmpt2dv2_3 eqeq2d biimpd fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 nfmpt21 fovmpt2dv2_1 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co fovmpt2dv2_8 fovmpt2dv2_1 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 fovmpt2dv2_1 fovmpt2dv2_3 nfcv fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 nfmpt21 fovmpt2dv2_1 fovmpt2dv2_4 nfcv nfov nfeq1 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 nfmpt22 fovmpt2dv2_2 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co fovmpt2dv2_8 fovmpt2dv2_2 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 fovmpt2dv2_2 fovmpt2dv2_3 nfcv fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 nfmpt22 fovmpt2dv2_2 fovmpt2dv2_4 nfcv nfov nfeq1 ovmpt2df mpd fovmpt2dv2_9 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 wceq fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_9 co fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 co fovmpt2dv2_8 fovmpt2dv2_3 fovmpt2dv2_4 fovmpt2dv2_9 fovmpt2dv2_1 fovmpt2dv2_2 fovmpt2dv2_5 fovmpt2dv2_6 fovmpt2dv2_7 cmpt2 oveq eqeq1d syl5ibrcom $.
$}
$( /* Value of an operation given by a maps-to rule.  Special case.
       (Contributed by NM, 14-Sep-1999.)  (Revised by David Abernethy,
       19-Jun-2012.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	$d x y S $.
	fovmpt2g_0 $f set x $.
	fovmpt2g_1 $f set y $.
	fovmpt2g_2 $f class A $.
	fovmpt2g_3 $f class B $.
	fovmpt2g_4 $f class C $.
	fovmpt2g_5 $f class D $.
	fovmpt2g_6 $f class R $.
	fovmpt2g_7 $f class S $.
	fovmpt2g_8 $f class F $.
	fovmpt2g_9 $f class G $.
	fovmpt2g_10 $f class H $.
	eovmpt2g_0 $e |- ( x = A -> R = G ) $.
	eovmpt2g_1 $e |- ( y = B -> G = S ) $.
	eovmpt2g_2 $e |- F = ( x e. C , y e. D |-> R ) $.
	ovmpt2g $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $= fovmpt2g_0 fovmpt2g_1 fovmpt2g_2 fovmpt2g_3 fovmpt2g_4 fovmpt2g_5 fovmpt2g_6 fovmpt2g_7 fovmpt2g_8 fovmpt2g_10 fovmpt2g_0 sup_set_class fovmpt2g_2 wceq fovmpt2g_1 sup_set_class fovmpt2g_3 wceq fovmpt2g_6 fovmpt2g_9 fovmpt2g_7 eovmpt2g_0 eovmpt2g_1 sylan9eq eovmpt2g_2 ovmpt2ga $.
$}
$( /* Value of an operation given by a maps-to rule.  Special case.
       (Contributed by NM, 16-May-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	$d x y S $.
	fovmpt2_0 $f set x $.
	fovmpt2_1 $f set y $.
	fovmpt2_2 $f class A $.
	fovmpt2_3 $f class B $.
	fovmpt2_4 $f class C $.
	fovmpt2_5 $f class D $.
	fovmpt2_6 $f class R $.
	fovmpt2_7 $f class S $.
	fovmpt2_8 $f class F $.
	fovmpt2_9 $f class G $.
	eovmpt2_0 $e |- ( x = A -> R = G ) $.
	eovmpt2_1 $e |- ( y = B -> G = S ) $.
	eovmpt2_2 $e |- F = ( x e. C , y e. D |-> R ) $.
	eovmpt2_3 $e |- S e. _V $.
	ovmpt2 $p |- ( ( A e. C /\ B e. D ) -> ( A F B ) = S ) $= fovmpt2_2 fovmpt2_4 wcel fovmpt2_3 fovmpt2_5 wcel fovmpt2_7 cvv wcel fovmpt2_2 fovmpt2_3 fovmpt2_8 co fovmpt2_7 wceq eovmpt2_3 fovmpt2_0 fovmpt2_1 fovmpt2_2 fovmpt2_3 fovmpt2_4 fovmpt2_5 fovmpt2_6 fovmpt2_7 fovmpt2_8 fovmpt2_9 cvv eovmpt2_0 eovmpt2_1 eovmpt2_2 ovmpt2g mp3an3 $.
$}
$( /* The value of an operation class abstraction.  Special case.
       (Contributed by NM, 28-May-1995.)  (Revised by Mario Carneiro,
       29-Dec-2014.) */

$)
${
	$d f u v w x y z A $.
	$d f u v w x y z B $.
	$d x y z R $.
	$d f u v w y z C $.
	$d f u v w y z D $.
	$d f u v w x y z H $.
	$d f u v w z S $.
	fov3_0 $f set x $.
	fov3_1 $f set y $.
	fov3_2 $f set z $.
	fov3_3 $f set w $.
	fov3_4 $f set v $.
	fov3_5 $f set u $.
	fov3_6 $f class A $.
	fov3_7 $f class B $.
	fov3_8 $f class C $.
	fov3_9 $f class D $.
	fov3_10 $f class R $.
	fov3_11 $f class S $.
	fov3_12 $f set f $.
	fov3_13 $f class F $.
	fov3_14 $f class H $.
	eov3_0 $e |- S e. _V $.
	eov3_1 $e |- ( ( ( w = A /\ v = B ) /\ ( u = C /\ f = D ) ) -> R = S ) $.
	eov3_2 $e |- F = { <. <. x , y >. , z >. | ( ( x e. ( H X. H ) /\ y e. ( H X. H ) ) /\ E. w E. v E. u E. f ( ( x = <. w , v >. /\ y = <. u , f >. ) /\ z = R ) ) } $.
	ov3 $p |- ( ( ( A e. H /\ B e. H ) /\ ( C e. H /\ D e. H ) ) -> ( <. A , B >. F <. C , D >. ) = S ) $= fov3_6 fov3_14 wcel fov3_7 fov3_14 wcel wa fov3_8 fov3_14 wcel fov3_9 fov3_14 wcel wa wa fov3_2 sup_set_class fov3_11 wceq fov3_2 wex fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_11 wceq fov3_2 fov3_11 eov3_0 isseti fov3_6 fov3_14 wcel fov3_7 fov3_14 wcel wa fov3_8 fov3_14 wcel fov3_9 fov3_14 wcel wa wa fov3_2 sup_set_class fov3_11 wceq fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_11 wceq fov3_2 fov3_6 fov3_14 wcel fov3_7 fov3_14 wcel wa fov3_8 fov3_14 wcel fov3_9 fov3_14 wcel wa wa fov3_2 nfv fov3_2 fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_11 fov3_2 fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 fov3_2 fov3_6 fov3_7 cop nfcv fov3_2 fov3_13 fov3_0 sup_set_class fov3_14 fov3_14 cxp wcel fov3_1 sup_set_class fov3_14 fov3_14 cxp wcel wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex wa fov3_0 fov3_1 fov3_2 coprab eov3_2 fov3_0 sup_set_class fov3_14 fov3_14 cxp wcel fov3_1 sup_set_class fov3_14 fov3_14 cxp wcel wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex wa fov3_0 fov3_1 fov3_2 nfoprab3 nfcxfr fov3_2 fov3_8 fov3_9 cop nfcv nfov nfeq1 fov3_2 sup_set_class fov3_11 wceq fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_2 sup_set_class wceq fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_11 wceq fov3_6 fov3_14 wcel fov3_7 fov3_14 wcel wa fov3_8 fov3_14 wcel fov3_9 fov3_14 wcel wa wa fov3_6 fov3_14 wcel fov3_7 fov3_14 wcel wa fov3_8 fov3_14 wcel fov3_9 fov3_14 wcel wa wa fov3_2 sup_set_class fov3_11 wceq fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_2 sup_set_class wceq fov3_2 sup_set_class fov3_10 wceq fov3_2 sup_set_class fov3_11 wceq fov3_3 fov3_4 fov3_5 fov3_12 fov3_6 fov3_7 fov3_8 fov3_9 fov3_14 fov3_14 fov3_3 sup_set_class fov3_6 wceq fov3_4 sup_set_class fov3_7 wceq wa fov3_5 sup_set_class fov3_8 wceq fov3_12 sup_set_class fov3_9 wceq wa wa fov3_10 fov3_11 fov3_2 sup_set_class eov3_1 eqeq2d copsex4g fov3_6 fov3_14 wcel fov3_7 fov3_14 wcel wa fov3_6 fov3_7 cop fov3_14 fov3_14 cxp wcel fov3_8 fov3_9 cop fov3_14 fov3_14 cxp wcel fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_2 sup_set_class wceq wi fov3_8 fov3_14 wcel fov3_9 fov3_14 wcel wa fov3_6 fov3_7 fov3_14 fov3_14 opelxpi fov3_8 fov3_9 fov3_14 fov3_14 opelxpi fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_0 sup_set_class fov3_1 sup_set_class fov3_13 co fov3_2 sup_set_class wceq wi fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 co fov3_2 sup_set_class wceq wi fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_2 sup_set_class wceq wi fov3_0 fov3_1 fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_14 fov3_14 cxp fov3_14 fov3_14 cxp fov3_0 fov3_6 fov3_7 cop nfcv fov3_1 fov3_6 fov3_7 cop nfcv fov3_1 fov3_8 fov3_9 cop nfcv fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 co fov3_2 sup_set_class wceq fov3_0 fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_0 nfv fov3_0 fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 co fov3_2 sup_set_class fov3_0 fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 fov3_0 fov3_6 fov3_7 cop nfcv fov3_0 fov3_13 fov3_0 sup_set_class fov3_14 fov3_14 cxp wcel fov3_1 sup_set_class fov3_14 fov3_14 cxp wcel wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex wa fov3_0 fov3_1 fov3_2 coprab eov3_2 fov3_0 sup_set_class fov3_14 fov3_14 cxp wcel fov3_1 sup_set_class fov3_14 fov3_14 cxp wcel wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex wa fov3_0 fov3_1 fov3_2 nfoprab1 nfcxfr fov3_0 fov3_1 sup_set_class nfcv nfov nfeq1 nfim fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_2 sup_set_class wceq fov3_1 fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_1 nfv fov3_1 fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_2 sup_set_class fov3_1 fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 fov3_1 fov3_6 fov3_7 cop nfcv fov3_1 fov3_13 fov3_0 sup_set_class fov3_14 fov3_14 cxp wcel fov3_1 sup_set_class fov3_14 fov3_14 cxp wcel wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex wa fov3_0 fov3_1 fov3_2 coprab eov3_2 fov3_0 sup_set_class fov3_14 fov3_14 cxp wcel fov3_1 sup_set_class fov3_14 fov3_14 cxp wcel wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex wa fov3_0 fov3_1 fov3_2 nfoprab2 nfcxfr fov3_1 fov3_8 fov3_9 cop nfcv nfov nfeq1 nfim fov3_0 sup_set_class fov3_6 fov3_7 cop wceq fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_0 sup_set_class fov3_1 sup_set_class fov3_13 co fov3_2 sup_set_class wceq fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 co fov3_2 sup_set_class wceq fov3_0 sup_set_class fov3_6 fov3_7 cop wceq fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_3 fov3_4 fov3_5 fov3_12 fov3_0 sup_set_class fov3_6 fov3_7 cop wceq fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq fov3_0 sup_set_class fov3_6 fov3_7 cop wceq fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_0 sup_set_class fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop eqeq1 anbi1d anbi1d 4exbidv fov3_0 sup_set_class fov3_6 fov3_7 cop wceq fov3_0 sup_set_class fov3_1 sup_set_class fov3_13 co fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 co fov3_2 sup_set_class fov3_0 sup_set_class fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 oveq1 eqeq1d imbi12d fov3_1 sup_set_class fov3_8 fov3_9 cop wceq fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 co fov3_2 sup_set_class wceq fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_2 sup_set_class wceq fov3_1 sup_set_class fov3_8 fov3_9 cop wceq fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_3 fov3_4 fov3_5 fov3_12 fov3_1 sup_set_class fov3_8 fov3_9 cop wceq fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq fov3_1 sup_set_class fov3_8 fov3_9 cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_6 fov3_7 cop fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_8 fov3_9 cop fov3_5 sup_set_class fov3_12 sup_set_class cop eqeq1 anbi2d anbi1d 4exbidv fov3_1 sup_set_class fov3_8 fov3_9 cop wceq fov3_6 fov3_7 cop fov3_1 sup_set_class fov3_13 co fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co fov3_2 sup_set_class fov3_1 sup_set_class fov3_8 fov3_9 cop fov3_6 fov3_7 cop fov3_13 oveq2 eqeq1d imbi12d fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_0 fov3_1 fov3_2 fov3_14 fov3_14 cxp fov3_14 fov3_14 cxp fov3_13 fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_2 wmo fov3_0 sup_set_class fov3_14 fov3_14 cxp wcel fov3_1 sup_set_class fov3_14 fov3_14 cxp wcel wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_2 wmo fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex wa fov3_4 wex fov3_3 wex fov3_2 wmo fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_2 fov3_3 fov3_4 fov3_0 sup_set_class fov3_2 sup_set_class fov3_10 wceq fov3_2 fov3_5 fov3_12 fov3_1 sup_set_class fov3_2 fov3_10 moeq mosubop mosubop fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_4 wex fov3_3 wex fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex wa fov3_4 wex fov3_3 wex fov3_2 fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex wa fov3_3 fov3_4 fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq wa wa fov3_12 wex fov3_5 wex fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq wa fov3_12 wex fov3_5 wex wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq wa fov3_2 sup_set_class fov3_10 wceq wa fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq wa wa fov3_5 fov3_12 fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq anass 2exbii fov3_0 sup_set_class fov3_3 sup_set_class fov3_4 sup_set_class cop wceq fov3_1 sup_set_class fov3_5 sup_set_class fov3_12 sup_set_class cop wceq fov3_2 sup_set_class fov3_10 wceq wa fov3_5 fov3_12 19.42vv bitri 2exbii mobii mpbir a1i eov3_2 ovidi vtocl2gaf syl2an sylbird fov3_2 sup_set_class fov3_11 fov3_6 fov3_7 cop fov3_8 fov3_9 cop fov3_13 co eqeq2 mpbidi exlimd mpi $.
$}
$( /* The value of an operation class abstraction.  Special case.
       (Contributed by NM, 13-Nov-2006.) */

$)
$v J $.
${
	$d w x y z A $.
	$d w x y z B $.
	$d w x y z C $.
	$d w z R $.
	$d w x y z S $.
	iov6g_0 $f set w $.
	fov6g_0 $f set x $.
	fov6g_1 $f set y $.
	fov6g_2 $f set z $.
	fov6g_3 $f class A $.
	fov6g_4 $f class B $.
	fov6g_5 $f class C $.
	fov6g_6 $f class R $.
	fov6g_7 $f class S $.
	fov6g_8 $f class F $.
	fov6g_9 $f class G $.
	fov6g_10 $f class H $.
	fov6g_11 $f class J $.
	eov6g_0 $e |- ( <. x , y >. = <. A , B >. -> R = S ) $.
	eov6g_1 $e |- F = { <. <. x , y >. , z >. | ( <. x , y >. e. C /\ z = R ) } $.
	ov6g $p |- ( ( ( A e. G /\ B e. H /\ <. A , B >. e. C ) /\ S e. J ) -> ( A F B ) = S ) $= fov6g_3 fov6g_9 wcel fov6g_4 fov6g_10 wcel fov6g_3 fov6g_4 cop fov6g_5 wcel w3a fov6g_7 fov6g_11 wcel wa fov6g_3 fov6g_4 fov6g_8 co fov6g_3 fov6g_4 cop fov6g_8 cfv fov6g_7 fov6g_3 fov6g_4 fov6g_8 df-ov fov6g_3 fov6g_9 wcel fov6g_4 fov6g_10 wcel fov6g_3 fov6g_4 cop fov6g_5 wcel w3a fov6g_7 fov6g_11 wcel wa fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_7 fov6g_7 wceq wa fov6g_1 wex fov6g_0 wex fov6g_3 fov6g_4 cop fov6g_8 cfv fov6g_7 wceq fov6g_3 fov6g_9 wcel fov6g_4 fov6g_10 wcel fov6g_3 fov6g_4 cop fov6g_5 wcel w3a fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_7 fov6g_7 wceq wa fov6g_1 wex fov6g_0 wex fov6g_7 fov6g_11 wcel fov6g_3 fov6g_9 wcel fov6g_4 fov6g_10 wcel fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_7 fov6g_7 wceq wa fov6g_1 wex fov6g_0 wex fov6g_3 fov6g_4 cop fov6g_5 wcel fov6g_3 fov6g_9 wcel fov6g_4 fov6g_10 wcel wa fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_7 fov6g_7 wceq wa fov6g_1 wex fov6g_0 wex fov6g_7 fov6g_7 wceq fov6g_7 eqid fov6g_7 fov6g_7 wceq fov6g_7 fov6g_7 wceq fov6g_0 fov6g_1 fov6g_3 fov6g_4 fov6g_9 fov6g_10 fov6g_0 sup_set_class fov6g_3 wceq fov6g_1 sup_set_class fov6g_4 wceq wa fov6g_7 fov6g_7 wceq biidd copsex2g mpbiri 3adant3 adantr fov6g_3 fov6g_4 cop fov6g_5 wcel fov6g_3 fov6g_9 wcel fov6g_7 fov6g_11 wcel fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_7 fov6g_7 wceq wa fov6g_1 wex fov6g_0 wex fov6g_3 fov6g_4 cop fov6g_8 cfv fov6g_7 wceq wi fov6g_4 fov6g_10 wcel iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_1 wex fov6g_0 wex fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_7 wceq wa fov6g_1 wex fov6g_0 wex fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_7 fov6g_7 wceq wa fov6g_1 wex fov6g_0 wex iov6g_0 fov6g_2 fov6g_3 fov6g_4 cop fov6g_7 fov6g_5 fov6g_11 fov6g_8 iov6g_0 sup_set_class fov6g_3 fov6g_4 cop wceq iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_7 wceq wa fov6g_0 fov6g_1 iov6g_0 sup_set_class fov6g_3 fov6g_4 cop wceq iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_7 wceq wa iov6g_0 sup_set_class fov6g_3 fov6g_4 cop wceq iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq iov6g_0 sup_set_class fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop eqeq1 anbi1d fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq fov6g_2 sup_set_class fov6g_7 wceq fov6g_2 sup_set_class fov6g_6 wceq fov6g_2 sup_set_class fov6g_7 wceq wb fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_3 fov6g_4 cop wceq fov6g_6 fov6g_7 fov6g_2 sup_set_class eov6g_0 eqeq2d eqcoms pm5.32i syl6bb 2exbidv fov6g_2 sup_set_class fov6g_7 wceq fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_7 wceq wa fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_7 fov6g_7 wceq wa fov6g_0 fov6g_1 fov6g_2 sup_set_class fov6g_7 wceq fov6g_2 sup_set_class fov6g_7 wceq fov6g_7 fov6g_7 wceq fov6g_3 fov6g_4 cop fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_7 fov6g_7 eqeq1 anbi2d 2exbidv iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_1 wex fov6g_0 wex fov6g_2 wmo iov6g_0 sup_set_class fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq fov6g_2 fov6g_0 fov6g_1 iov6g_0 sup_set_class fov6g_2 fov6g_6 moeq mosubop a1i fov6g_8 fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_0 fov6g_1 fov6g_2 coprab iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa wa fov6g_1 wex fov6g_0 wex iov6g_0 fov6g_2 copab iov6g_0 sup_set_class fov6g_5 wcel iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_1 wex fov6g_0 wex wa iov6g_0 fov6g_2 copab eov6g_1 fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_0 fov6g_1 fov6g_2 iov6g_0 dfoprab2 iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa wa fov6g_1 wex fov6g_0 wex iov6g_0 sup_set_class fov6g_5 wcel iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_1 wex fov6g_0 wex wa iov6g_0 fov6g_2 iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa wa fov6g_1 wex fov6g_0 wex iov6g_0 sup_set_class fov6g_5 wcel iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa wa fov6g_1 wex fov6g_0 wex iov6g_0 sup_set_class fov6g_5 wcel iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_1 wex fov6g_0 wex wa iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa wa iov6g_0 sup_set_class fov6g_5 wcel iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa wa fov6g_0 fov6g_1 iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa wa iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq iov6g_0 sup_set_class fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa wa iov6g_0 sup_set_class fov6g_5 wcel iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa wa iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq iov6g_0 sup_set_class fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq wa iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq iov6g_0 sup_set_class fov6g_5 wcel fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop fov6g_5 eleq1 anbi1d pm5.32i iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq iov6g_0 sup_set_class fov6g_5 wcel fov6g_2 sup_set_class fov6g_6 wceq an12 bitr3i 2exbii iov6g_0 sup_set_class fov6g_5 wcel iov6g_0 sup_set_class fov6g_0 sup_set_class fov6g_1 sup_set_class cop wceq fov6g_2 sup_set_class fov6g_6 wceq wa fov6g_0 fov6g_1 19.42vv bitri opabbii 3eqtri fvopab3ig 3ad2antl3 mpd syl5eq $.
$}
$( /* The value of an operation class abstraction.  (Contributed by Jeff
       Madsen, 10-Jun-2010.) */

$)
${
	$d ph c $.
	$d ps x $.
	$d ch x y $.
	$d th x y z $.
	$d ta x y c $.
	$d R x y z c $.
	$d S x y z c $.
	$d A x y z c $.
	$d B x y z c $.
	$d C x y z c $.
	iovg_0 $f set c $.
	fovg_0 $f wff ph $.
	fovg_1 $f wff ps $.
	fovg_2 $f wff ch $.
	fovg_3 $f wff th $.
	fovg_4 $f wff ta $.
	fovg_5 $f set x $.
	fovg_6 $f set y $.
	fovg_7 $f set z $.
	fovg_8 $f class A $.
	fovg_9 $f class B $.
	fovg_10 $f class C $.
	fovg_11 $f class D $.
	fovg_12 $f class R $.
	fovg_13 $f class S $.
	fovg_14 $f class F $.
	eovg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eovg_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	eovg_2 $e |- ( z = C -> ( ch <-> th ) ) $.
	eovg_3 $e |- ( ( ta /\ ( x e. R /\ y e. S ) ) -> E! z ph ) $.
	eovg_4 $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	ovg $p |- ( ( ta /\ ( A e. R /\ B e. S /\ C e. D ) ) -> ( ( A F B ) = C <-> th ) ) $= fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel fovg_10 fovg_11 wcel w3a wa fovg_8 fovg_9 fovg_14 co fovg_10 wceq fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa fovg_3 fovg_8 fovg_9 fovg_14 co fovg_10 wceq fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 wceq fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel fovg_10 fovg_11 wcel w3a wa fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa fovg_8 fovg_9 fovg_14 co fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 fovg_8 fovg_9 fovg_14 co fovg_8 fovg_9 cop fovg_14 cfv fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_8 fovg_9 fovg_14 df-ov fovg_8 fovg_9 cop fovg_14 fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab eovg_4 fveq1i eqtri eqeq1i fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel fovg_10 fovg_11 wcel w3a wa fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 wceq fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel fovg_10 fovg_11 wcel fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 wceq fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel wb fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel fovg_10 fovg_11 wcel fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 wceq fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel wb wi fovg_10 fovg_11 wcel fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa wa fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 wceq fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel wb fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa wa fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv iovg_0 sup_set_class wceq fovg_8 fovg_9 cop iovg_0 sup_set_class cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel wb wi fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa wa fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 wceq fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel wb wi iovg_0 fovg_10 fovg_11 iovg_0 sup_set_class fovg_10 wceq fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv iovg_0 sup_set_class wceq fovg_8 fovg_9 cop iovg_0 sup_set_class cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel wb fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 wceq fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel wb fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa wa iovg_0 sup_set_class fovg_10 wceq fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv iovg_0 sup_set_class wceq fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv fovg_10 wceq fovg_8 fovg_9 cop iovg_0 sup_set_class cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel iovg_0 sup_set_class fovg_10 fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv eqeq2 iovg_0 sup_set_class fovg_10 wceq fovg_8 fovg_9 cop iovg_0 sup_set_class cop fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab iovg_0 sup_set_class fovg_10 fovg_8 fovg_9 cop opeq2 eleq1d bibi12d imbi2d fovg_4 fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_5 fovg_6 copab wfn fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_5 fovg_6 copab wcel fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab cfv iovg_0 sup_set_class wceq fovg_8 fovg_9 cop iovg_0 sup_set_class cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel wb fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_4 fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 fovg_7 weu wi fovg_6 wal fovg_5 wal fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_5 fovg_6 copab wfn fovg_4 fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 fovg_7 weu wi fovg_5 fovg_6 fovg_4 fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 fovg_7 weu eovg_3 ex alrimivv fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 fovg_5 fovg_6 fovg_7 fnoprabg syl fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_8 fovg_9 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_5 fovg_6 copab wcel fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_8 fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_5 fovg_6 fovg_8 fovg_9 fovg_12 fovg_13 fovg_5 sup_set_class fovg_8 wceq fovg_5 sup_set_class fovg_12 wcel fovg_8 fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel fovg_5 sup_set_class fovg_8 fovg_12 eleq1 anbi1d fovg_6 sup_set_class fovg_9 wceq fovg_6 sup_set_class fovg_13 wcel fovg_9 fovg_13 wcel fovg_8 fovg_12 wcel fovg_6 sup_set_class fovg_9 fovg_13 eleq1 anbi2d opelopabg ibir fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_5 fovg_6 copab fovg_8 fovg_9 cop iovg_0 sup_set_class fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab fnopfvb syl2an vtoclg com12 exp32 3imp2 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel fovg_10 fovg_11 wcel w3a fovg_8 fovg_9 cop fovg_10 cop fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_5 fovg_6 fovg_7 coprab wcel fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa wb fovg_4 fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 wa fovg_8 fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_1 wa fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_2 wa fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa fovg_5 fovg_6 fovg_7 fovg_8 fovg_9 fovg_10 fovg_12 fovg_13 fovg_11 fovg_5 sup_set_class fovg_8 wceq fovg_5 sup_set_class fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_8 fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_0 fovg_1 fovg_5 sup_set_class fovg_8 wceq fovg_5 sup_set_class fovg_12 wcel fovg_8 fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel fovg_5 sup_set_class fovg_8 fovg_12 eleq1 anbi1d eovg_0 anbi12d fovg_6 sup_set_class fovg_9 wceq fovg_8 fovg_12 wcel fovg_6 sup_set_class fovg_13 wcel wa fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_1 fovg_2 fovg_6 sup_set_class fovg_9 wceq fovg_6 sup_set_class fovg_13 wcel fovg_9 fovg_13 wcel fovg_8 fovg_12 wcel fovg_6 sup_set_class fovg_9 fovg_13 eleq1 anbi2d eovg_1 anbi12d fovg_7 sup_set_class fovg_10 wceq fovg_2 fovg_3 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa eovg_2 anbi2d eloprabg adantl bitrd syl5bb fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel fovg_10 fovg_11 wcel w3a fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa fovg_3 wb fovg_4 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa fovg_3 wb fovg_10 fovg_11 wcel fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa fovg_3 fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_8 fovg_12 wcel fovg_9 fovg_13 wcel wa fovg_3 wa biidd bianabs 3adant3 adantl bitrd $.
$}
$( /* The value of a restricted operation.  (Contributed by FL, 10-Nov-2006.) */

$)
${
	fovres_0 $f class A $.
	fovres_1 $f class B $.
	fovres_2 $f class C $.
	fovres_3 $f class D $.
	fovres_4 $f class F $.
	ovres $p |- ( ( A e. C /\ B e. D ) -> ( A ( F |` ( C X. D ) ) B ) = ( A F B ) ) $= fovres_0 fovres_2 wcel fovres_1 fovres_3 wcel wa fovres_0 fovres_1 cop fovres_4 fovres_2 fovres_3 cxp cres cfv fovres_0 fovres_1 cop fovres_4 cfv fovres_0 fovres_1 fovres_4 fovres_2 fovres_3 cxp cres co fovres_0 fovres_1 fovres_4 co fovres_0 fovres_2 wcel fovres_1 fovres_3 wcel wa fovres_0 fovres_1 cop fovres_2 fovres_3 cxp wcel fovres_0 fovres_1 cop fovres_4 fovres_2 fovres_3 cxp cres cfv fovres_0 fovres_1 cop fovres_4 cfv wceq fovres_0 fovres_1 fovres_2 fovres_3 opelxpi fovres_0 fovres_1 cop fovres_2 fovres_3 cxp fovres_4 fvres syl fovres_0 fovres_1 fovres_4 fovres_2 fovres_3 cxp cres df-ov fovres_0 fovres_1 fovres_4 df-ov 3eqtr4g $.
$}
$( /* Lemma for converting metric theorems to metric space theorems.
       (Contributed by Mario Carneiro, 2-Oct-2015.) */

$)
${
	fovresd_0 $f wff ph $.
	fovresd_1 $f class A $.
	fovresd_2 $f class B $.
	fovresd_3 $f class D $.
	fovresd_4 $f class X $.
	eovresd_0 $e |- ( ph -> A e. X ) $.
	eovresd_1 $e |- ( ph -> B e. X ) $.
	ovresd $p |- ( ph -> ( A ( D |` ( X X. X ) ) B ) = ( A D B ) ) $= fovresd_0 fovresd_1 fovresd_4 wcel fovresd_2 fovresd_4 wcel fovresd_1 fovresd_2 fovresd_3 fovresd_4 fovresd_4 cxp cres co fovresd_1 fovresd_2 fovresd_3 co wceq eovresd_0 eovresd_1 fovresd_1 fovresd_2 fovresd_4 fovresd_4 fovresd_3 ovres syl2anc $.
$}
$( /* The value of a member of the domain of a subclass of an operation.
     (Contributed by NM, 23-Aug-2007.) */

$)
${
	foprssov_0 $f class A $.
	foprssov_1 $f class B $.
	foprssov_2 $f class C $.
	foprssov_3 $f class D $.
	foprssov_4 $f class F $.
	foprssov_5 $f class G $.
	oprssov $p |- ( ( ( Fun F /\ G Fn ( C X. D ) /\ G C_ F ) /\ ( A e. C /\ B e. D ) ) -> ( A F B ) = ( A G B ) ) $= foprssov_4 wfun foprssov_5 foprssov_2 foprssov_3 cxp wfn foprssov_5 foprssov_4 wss w3a foprssov_0 foprssov_2 wcel foprssov_1 foprssov_3 wcel wa wa foprssov_0 foprssov_1 foprssov_4 foprssov_2 foprssov_3 cxp cres co foprssov_0 foprssov_1 foprssov_4 co foprssov_0 foprssov_1 foprssov_5 co foprssov_0 foprssov_2 wcel foprssov_1 foprssov_3 wcel wa foprssov_0 foprssov_1 foprssov_4 foprssov_2 foprssov_3 cxp cres co foprssov_0 foprssov_1 foprssov_4 co wceq foprssov_4 wfun foprssov_5 foprssov_2 foprssov_3 cxp wfn foprssov_5 foprssov_4 wss w3a foprssov_0 foprssov_1 foprssov_2 foprssov_3 foprssov_4 ovres adantl foprssov_4 wfun foprssov_5 foprssov_2 foprssov_3 cxp wfn foprssov_5 foprssov_4 wss w3a foprssov_0 foprssov_1 foprssov_4 foprssov_2 foprssov_3 cxp cres co foprssov_0 foprssov_1 foprssov_5 co wceq foprssov_0 foprssov_2 wcel foprssov_1 foprssov_3 wcel wa foprssov_4 wfun foprssov_5 foprssov_2 foprssov_3 cxp wfn foprssov_5 foprssov_4 wss w3a foprssov_4 foprssov_2 foprssov_3 cxp cres foprssov_5 foprssov_0 foprssov_1 foprssov_4 wfun foprssov_5 foprssov_2 foprssov_3 cxp wfn foprssov_5 foprssov_4 wss w3a foprssov_4 foprssov_5 cdm cres foprssov_4 foprssov_2 foprssov_3 cxp cres foprssov_5 foprssov_5 foprssov_2 foprssov_3 cxp wfn foprssov_4 wfun foprssov_4 foprssov_5 cdm cres foprssov_4 foprssov_2 foprssov_3 cxp cres wceq foprssov_5 foprssov_4 wss foprssov_5 foprssov_2 foprssov_3 cxp wfn foprssov_5 cdm foprssov_2 foprssov_3 cxp foprssov_4 foprssov_2 foprssov_3 cxp foprssov_5 fndm reseq2d 3ad2ant2 foprssov_4 wfun foprssov_5 foprssov_4 wss foprssov_4 foprssov_5 cdm cres foprssov_5 wceq foprssov_5 foprssov_2 foprssov_3 cxp wfn foprssov_4 foprssov_5 funssres 3adant2 eqtr3d oveqd adantr eqtr3d $.
$}
$( /* An operation's value belongs to its codomain.  (Contributed by NM,
     27-Aug-2006.) */

$)
${
	ffovrn_0 $f class A $.
	ffovrn_1 $f class B $.
	ffovrn_2 $f class C $.
	ffovrn_3 $f class R $.
	ffovrn_4 $f class S $.
	ffovrn_5 $f class F $.
	fovrn $p |- ( ( F : ( R X. S ) --> C /\ A e. R /\ B e. S ) -> ( A F B ) e. C ) $= ffovrn_3 ffovrn_4 cxp ffovrn_2 ffovrn_5 wf ffovrn_0 ffovrn_3 wcel ffovrn_1 ffovrn_4 wcel ffovrn_0 ffovrn_1 ffovrn_5 co ffovrn_2 wcel ffovrn_0 ffovrn_3 wcel ffovrn_1 ffovrn_4 wcel wa ffovrn_3 ffovrn_4 cxp ffovrn_2 ffovrn_5 wf ffovrn_0 ffovrn_1 cop ffovrn_3 ffovrn_4 cxp wcel ffovrn_0 ffovrn_1 ffovrn_5 co ffovrn_2 wcel ffovrn_0 ffovrn_1 ffovrn_3 ffovrn_4 opelxpi ffovrn_3 ffovrn_4 cxp ffovrn_2 ffovrn_5 wf ffovrn_0 ffovrn_1 cop ffovrn_3 ffovrn_4 cxp wcel wa ffovrn_0 ffovrn_1 ffovrn_5 co ffovrn_0 ffovrn_1 cop ffovrn_5 cfv ffovrn_2 ffovrn_0 ffovrn_1 ffovrn_5 df-ov ffovrn_3 ffovrn_4 cxp ffovrn_2 ffovrn_0 ffovrn_1 cop ffovrn_5 ffvelrn syl5eqel sylan2 3impb $.
$}
$( /* An operation's value belongs to its codomain.  (Contributed by Mario
       Carneiro, 29-Dec-2016.) */

$)
${
	ffovrnda_0 $f wff ph $.
	ffovrnda_1 $f class A $.
	ffovrnda_2 $f class B $.
	ffovrnda_3 $f class C $.
	ffovrnda_4 $f class R $.
	ffovrnda_5 $f class S $.
	ffovrnda_6 $f class F $.
	efovrnda_0 $e |- ( ph -> F : ( R X. S ) --> C ) $.
	fovrnda $p |- ( ( ph /\ ( A e. R /\ B e. S ) ) -> ( A F B ) e. C ) $= ffovrnda_0 ffovrnda_1 ffovrnda_4 wcel ffovrnda_2 ffovrnda_5 wcel ffovrnda_1 ffovrnda_2 ffovrnda_6 co ffovrnda_3 wcel ffovrnda_0 ffovrnda_4 ffovrnda_5 cxp ffovrnda_3 ffovrnda_6 wf ffovrnda_1 ffovrnda_4 wcel ffovrnda_2 ffovrnda_5 wcel ffovrnda_1 ffovrnda_2 ffovrnda_6 co ffovrnda_3 wcel efovrnda_0 ffovrnda_1 ffovrnda_2 ffovrnda_3 ffovrnda_4 ffovrnda_5 ffovrnda_6 fovrn syl3an1 3expb $.
$}
$( /* An operation's value belongs to its codomain.  (Contributed by Mario
       Carneiro, 29-Dec-2016.) */

$)
${
	ffovrnd_0 $f wff ph $.
	ffovrnd_1 $f class A $.
	ffovrnd_2 $f class B $.
	ffovrnd_3 $f class C $.
	ffovrnd_4 $f class R $.
	ffovrnd_5 $f class S $.
	ffovrnd_6 $f class F $.
	efovrnd_0 $e |- ( ph -> F : ( R X. S ) --> C ) $.
	efovrnd_1 $e |- ( ph -> A e. R ) $.
	efovrnd_2 $e |- ( ph -> B e. S ) $.
	fovrnd $p |- ( ph -> ( A F B ) e. C ) $= ffovrnd_0 ffovrnd_4 ffovrnd_5 cxp ffovrnd_3 ffovrnd_6 wf ffovrnd_1 ffovrnd_4 wcel ffovrnd_2 ffovrnd_5 wcel ffovrnd_1 ffovrnd_2 ffovrnd_6 co ffovrnd_3 wcel efovrnd_0 efovrnd_1 efovrnd_2 ffovrnd_1 ffovrnd_2 ffovrnd_3 ffovrnd_4 ffovrnd_5 ffovrnd_6 fovrn syl3anc $.
$}
$( /* The range of an operation expressed as a collection of the operation's
       values.  (Contributed by NM, 29-Oct-2006.) */

$)
${
	$d w x y z A $.
	$d w x y z B $.
	$d w z $.
	$d w x y z F $.
	ifnrnov_0 $f set w $.
	ffnrnov_0 $f set x $.
	ffnrnov_1 $f set y $.
	ffnrnov_2 $f set z $.
	ffnrnov_3 $f class A $.
	ffnrnov_4 $f class B $.
	ffnrnov_5 $f class F $.
	fnrnov $p |- ( F Fn ( A X. B ) -> ran F = { z | E. x e. A E. y e. B z = ( x F y ) } ) $= ffnrnov_5 ffnrnov_3 ffnrnov_4 cxp wfn ffnrnov_5 crn ffnrnov_2 sup_set_class ifnrnov_0 sup_set_class ffnrnov_5 cfv wceq ifnrnov_0 ffnrnov_3 ffnrnov_4 cxp wrex ffnrnov_2 cab ffnrnov_2 sup_set_class ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class ffnrnov_5 co wceq ffnrnov_1 ffnrnov_4 wrex ffnrnov_0 ffnrnov_3 wrex ffnrnov_2 cab ifnrnov_0 ffnrnov_2 ffnrnov_3 ffnrnov_4 cxp ffnrnov_5 fnrnfv ffnrnov_2 sup_set_class ifnrnov_0 sup_set_class ffnrnov_5 cfv wceq ifnrnov_0 ffnrnov_3 ffnrnov_4 cxp wrex ffnrnov_2 sup_set_class ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class ffnrnov_5 co wceq ffnrnov_1 ffnrnov_4 wrex ffnrnov_0 ffnrnov_3 wrex ffnrnov_2 ffnrnov_2 sup_set_class ifnrnov_0 sup_set_class ffnrnov_5 cfv wceq ffnrnov_2 sup_set_class ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class ffnrnov_5 co wceq ifnrnov_0 ffnrnov_0 ffnrnov_1 ffnrnov_3 ffnrnov_4 ifnrnov_0 sup_set_class ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class cop wceq ifnrnov_0 sup_set_class ffnrnov_5 cfv ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class ffnrnov_5 co ffnrnov_2 sup_set_class ifnrnov_0 sup_set_class ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class cop wceq ifnrnov_0 sup_set_class ffnrnov_5 cfv ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class cop ffnrnov_5 cfv ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class ffnrnov_5 co ifnrnov_0 sup_set_class ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class cop ffnrnov_5 fveq2 ffnrnov_0 sup_set_class ffnrnov_1 sup_set_class ffnrnov_5 df-ov syl6eqr eqeq2d rexxp abbii syl6eq $.
$}
$( /* An onto mapping of an operation expressed in terms of operation values.
       (Contributed by NM, 29-Oct-2006.) */

$)
${
	$d w x y z A $.
	$d w x y z B $.
	$d w z C $.
	$d w x y z F $.
	ifoov_0 $f set w $.
	ffoov_0 $f set x $.
	ffoov_1 $f set y $.
	ffoov_2 $f set z $.
	ffoov_3 $f class A $.
	ffoov_4 $f class B $.
	ffoov_5 $f class C $.
	ffoov_6 $f class F $.
	foov $p |- ( F : ( A X. B ) -onto-> C <-> ( F : ( A X. B ) --> C /\ A. z e. C E. x e. A E. y e. B z = ( x F y ) ) ) $= ffoov_3 ffoov_4 cxp ffoov_5 ffoov_6 wfo ffoov_3 ffoov_4 cxp ffoov_5 ffoov_6 wf ffoov_2 sup_set_class ifoov_0 sup_set_class ffoov_6 cfv wceq ifoov_0 ffoov_3 ffoov_4 cxp wrex ffoov_2 ffoov_5 wral wa ffoov_3 ffoov_4 cxp ffoov_5 ffoov_6 wf ffoov_2 sup_set_class ffoov_0 sup_set_class ffoov_1 sup_set_class ffoov_6 co wceq ffoov_1 ffoov_4 wrex ffoov_0 ffoov_3 wrex ffoov_2 ffoov_5 wral wa ifoov_0 ffoov_2 ffoov_3 ffoov_4 cxp ffoov_5 ffoov_6 dffo3 ffoov_2 sup_set_class ifoov_0 sup_set_class ffoov_6 cfv wceq ifoov_0 ffoov_3 ffoov_4 cxp wrex ffoov_2 ffoov_5 wral ffoov_2 sup_set_class ffoov_0 sup_set_class ffoov_1 sup_set_class ffoov_6 co wceq ffoov_1 ffoov_4 wrex ffoov_0 ffoov_3 wrex ffoov_2 ffoov_5 wral ffoov_3 ffoov_4 cxp ffoov_5 ffoov_6 wf ffoov_2 sup_set_class ifoov_0 sup_set_class ffoov_6 cfv wceq ifoov_0 ffoov_3 ffoov_4 cxp wrex ffoov_2 sup_set_class ffoov_0 sup_set_class ffoov_1 sup_set_class ffoov_6 co wceq ffoov_1 ffoov_4 wrex ffoov_0 ffoov_3 wrex ffoov_2 ffoov_5 ffoov_2 sup_set_class ifoov_0 sup_set_class ffoov_6 cfv wceq ffoov_2 sup_set_class ffoov_0 sup_set_class ffoov_1 sup_set_class ffoov_6 co wceq ifoov_0 ffoov_0 ffoov_1 ffoov_3 ffoov_4 ifoov_0 sup_set_class ffoov_0 sup_set_class ffoov_1 sup_set_class cop wceq ifoov_0 sup_set_class ffoov_6 cfv ffoov_0 sup_set_class ffoov_1 sup_set_class ffoov_6 co ffoov_2 sup_set_class ifoov_0 sup_set_class ffoov_0 sup_set_class ffoov_1 sup_set_class cop wceq ifoov_0 sup_set_class ffoov_6 cfv ffoov_0 sup_set_class ffoov_1 sup_set_class cop ffoov_6 cfv ffoov_0 sup_set_class ffoov_1 sup_set_class ffoov_6 co ifoov_0 sup_set_class ffoov_0 sup_set_class ffoov_1 sup_set_class cop ffoov_6 fveq2 ffoov_0 sup_set_class ffoov_1 sup_set_class ffoov_6 df-ov syl6eqr eqeq2d rexxp ralbii anbi2i bitri $.
$}
$( /* An operation's value belongs to its range.  (Contributed by NM,
     10-Feb-2007.) */

$)
${
	ffnovrn_0 $f class A $.
	ffnovrn_1 $f class B $.
	ffnovrn_2 $f class C $.
	ffnovrn_3 $f class D $.
	ffnovrn_4 $f class F $.
	fnovrn $p |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) -> ( C F D ) e. ran F ) $= ffnovrn_4 ffnovrn_0 ffnovrn_1 cxp wfn ffnovrn_2 ffnovrn_0 wcel ffnovrn_3 ffnovrn_1 wcel ffnovrn_2 ffnovrn_3 ffnovrn_4 co ffnovrn_4 crn wcel ffnovrn_2 ffnovrn_0 wcel ffnovrn_3 ffnovrn_1 wcel wa ffnovrn_4 ffnovrn_0 ffnovrn_1 cxp wfn ffnovrn_2 ffnovrn_3 cop ffnovrn_0 ffnovrn_1 cxp wcel ffnovrn_2 ffnovrn_3 ffnovrn_4 co ffnovrn_4 crn wcel ffnovrn_2 ffnovrn_3 ffnovrn_0 ffnovrn_1 opelxpi ffnovrn_4 ffnovrn_0 ffnovrn_1 cxp wfn ffnovrn_2 ffnovrn_3 cop ffnovrn_0 ffnovrn_1 cxp wcel wa ffnovrn_2 ffnovrn_3 ffnovrn_4 co ffnovrn_2 ffnovrn_3 cop ffnovrn_4 cfv ffnovrn_4 crn ffnovrn_2 ffnovrn_3 ffnovrn_4 df-ov ffnovrn_0 ffnovrn_1 cxp ffnovrn_2 ffnovrn_3 cop ffnovrn_4 fnfvelrn syl5eqel sylan2 3impb $.
$}
$( /* A member of an operation's range is a value of the operation.
       (Contributed by NM, 7-Feb-2007.)  (Revised by Mario Carneiro,
       30-Jan-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z F $.
	iovelrn_0 $f set z $.
	fovelrn_0 $f set x $.
	fovelrn_1 $f set y $.
	fovelrn_2 $f class A $.
	fovelrn_3 $f class B $.
	fovelrn_4 $f class C $.
	fovelrn_5 $f class F $.
	ovelrn $p |- ( F Fn ( A X. B ) -> ( C e. ran F <-> E. x e. A E. y e. B C = ( x F y ) ) ) $= fovelrn_5 fovelrn_2 fovelrn_3 cxp wfn fovelrn_4 fovelrn_5 crn wcel fovelrn_4 iovelrn_0 sup_set_class fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_1 fovelrn_3 wrex fovelrn_0 fovelrn_2 wrex iovelrn_0 cab wcel fovelrn_4 fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_1 fovelrn_3 wrex fovelrn_0 fovelrn_2 wrex fovelrn_5 fovelrn_2 fovelrn_3 cxp wfn fovelrn_5 crn iovelrn_0 sup_set_class fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_1 fovelrn_3 wrex fovelrn_0 fovelrn_2 wrex iovelrn_0 cab fovelrn_4 fovelrn_0 fovelrn_1 iovelrn_0 fovelrn_2 fovelrn_3 fovelrn_5 fnrnov eleq2d iovelrn_0 sup_set_class fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_1 fovelrn_3 wrex fovelrn_0 fovelrn_2 wrex fovelrn_4 fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_1 fovelrn_3 wrex fovelrn_0 fovelrn_2 wrex iovelrn_0 fovelrn_4 fovelrn_4 fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_1 fovelrn_3 wrex fovelrn_4 cvv wcel fovelrn_0 fovelrn_2 fovelrn_4 fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_4 cvv wcel fovelrn_1 fovelrn_3 fovelrn_4 fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_4 cvv wcel fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co cvv wcel fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 ovex fovelrn_4 fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co cvv eleq1 mpbiri rexlimivw rexlimivw iovelrn_0 sup_set_class fovelrn_4 wceq iovelrn_0 sup_set_class fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_4 fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co wceq fovelrn_0 fovelrn_1 fovelrn_2 fovelrn_3 iovelrn_0 sup_set_class fovelrn_4 fovelrn_0 sup_set_class fovelrn_1 sup_set_class fovelrn_5 co eqeq1 2rexbidv elab3 syl6bb $.
$}
$( /* Membership relation for the values of a function whose image is a
       subclass.  (Contributed by Mario Carneiro, 23-Dec-2013.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z F $.
	ifunimassov_0 $f set z $.
	ffunimassov_0 $f set x $.
	ffunimassov_1 $f set y $.
	ffunimassov_2 $f class A $.
	ffunimassov_3 $f class B $.
	ffunimassov_4 $f class C $.
	ffunimassov_5 $f class F $.
	funimassov $p |- ( ( Fun F /\ ( A X. B ) C_ dom F ) -> ( ( F " ( A X. B ) ) C_ C <-> A. x e. A A. y e. B ( x F y ) e. C ) ) $= ffunimassov_5 wfun ffunimassov_2 ffunimassov_3 cxp ffunimassov_5 cdm wss wa ffunimassov_5 ffunimassov_2 ffunimassov_3 cxp cima ffunimassov_4 wss ifunimassov_0 sup_set_class ffunimassov_5 cfv ffunimassov_4 wcel ifunimassov_0 ffunimassov_2 ffunimassov_3 cxp wral ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class ffunimassov_5 co ffunimassov_4 wcel ffunimassov_1 ffunimassov_3 wral ffunimassov_0 ffunimassov_2 wral ifunimassov_0 ffunimassov_2 ffunimassov_3 cxp ffunimassov_4 ffunimassov_5 funimass4 ifunimassov_0 sup_set_class ffunimassov_5 cfv ffunimassov_4 wcel ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class ffunimassov_5 co ffunimassov_4 wcel ifunimassov_0 ffunimassov_0 ffunimassov_1 ffunimassov_2 ffunimassov_3 ifunimassov_0 sup_set_class ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class cop wceq ifunimassov_0 sup_set_class ffunimassov_5 cfv ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class ffunimassov_5 co ffunimassov_4 ifunimassov_0 sup_set_class ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class cop wceq ifunimassov_0 sup_set_class ffunimassov_5 cfv ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class cop ffunimassov_5 cfv ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class ffunimassov_5 co ifunimassov_0 sup_set_class ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class cop ffunimassov_5 fveq2 ffunimassov_0 sup_set_class ffunimassov_1 sup_set_class ffunimassov_5 df-ov syl6eqr eleq1d ralxp syl6bb $.
$}
$( /* Operation value in an image.  (Contributed by Mario Carneiro,
       23-Dec-2013.)  (Revised by Mario Carneiro, 29-Jan-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z F $.
	iovelimab_0 $f set z $.
	fovelimab_0 $f set x $.
	fovelimab_1 $f set y $.
	fovelimab_2 $f class A $.
	fovelimab_3 $f class B $.
	fovelimab_4 $f class C $.
	fovelimab_5 $f class D $.
	fovelimab_6 $f class F $.
	ovelimab $p |- ( ( F Fn A /\ ( B X. C ) C_ A ) -> ( D e. ( F " ( B X. C ) ) <-> E. x e. B E. y e. C D = ( x F y ) ) ) $= fovelimab_6 fovelimab_2 wfn fovelimab_3 fovelimab_4 cxp fovelimab_2 wss wa fovelimab_5 fovelimab_6 fovelimab_3 fovelimab_4 cxp cima wcel iovelimab_0 sup_set_class fovelimab_6 cfv fovelimab_5 wceq iovelimab_0 fovelimab_3 fovelimab_4 cxp wrex fovelimab_5 fovelimab_0 sup_set_class fovelimab_1 sup_set_class fovelimab_6 co wceq fovelimab_1 fovelimab_4 wrex fovelimab_0 fovelimab_3 wrex iovelimab_0 fovelimab_2 fovelimab_3 fovelimab_4 cxp fovelimab_5 fovelimab_6 fvelimab iovelimab_0 sup_set_class fovelimab_6 cfv fovelimab_5 wceq fovelimab_5 fovelimab_0 sup_set_class fovelimab_1 sup_set_class fovelimab_6 co wceq iovelimab_0 fovelimab_0 fovelimab_1 fovelimab_3 fovelimab_4 iovelimab_0 sup_set_class fovelimab_0 sup_set_class fovelimab_1 sup_set_class cop wceq iovelimab_0 sup_set_class fovelimab_6 cfv fovelimab_5 wceq fovelimab_0 sup_set_class fovelimab_1 sup_set_class fovelimab_6 co fovelimab_5 wceq fovelimab_5 fovelimab_0 sup_set_class fovelimab_1 sup_set_class fovelimab_6 co wceq iovelimab_0 sup_set_class fovelimab_0 sup_set_class fovelimab_1 sup_set_class cop wceq iovelimab_0 sup_set_class fovelimab_6 cfv fovelimab_0 sup_set_class fovelimab_1 sup_set_class fovelimab_6 co fovelimab_5 iovelimab_0 sup_set_class fovelimab_0 sup_set_class fovelimab_1 sup_set_class cop wceq iovelimab_0 sup_set_class fovelimab_6 cfv fovelimab_0 sup_set_class fovelimab_1 sup_set_class cop fovelimab_6 cfv fovelimab_0 sup_set_class fovelimab_1 sup_set_class fovelimab_6 co iovelimab_0 sup_set_class fovelimab_0 sup_set_class fovelimab_1 sup_set_class cop fovelimab_6 fveq2 fovelimab_0 sup_set_class fovelimab_1 sup_set_class fovelimab_6 df-ov syl6eqr eqeq1d fovelimab_0 sup_set_class fovelimab_1 sup_set_class fovelimab_6 co fovelimab_5 eqcom syl6bb rexxp syl6bb $.
$}
$( /* The value of a constant operation.  (Contributed by NM, 5-Nov-2006.) */

$)
${
	fovconst2_0 $f class A $.
	fovconst2_1 $f class B $.
	fovconst2_2 $f class C $.
	fovconst2_3 $f class R $.
	fovconst2_4 $f class S $.
	eovconst2_0 $e |- C e. _V $.
	ovconst2 $p |- ( ( R e. A /\ S e. B ) -> ( R ( ( A X. B ) X. { C } ) S ) = C ) $= fovconst2_3 fovconst2_0 wcel fovconst2_4 fovconst2_1 wcel wa fovconst2_3 fovconst2_4 fovconst2_0 fovconst2_1 cxp fovconst2_2 csn cxp co fovconst2_3 fovconst2_4 cop fovconst2_0 fovconst2_1 cxp fovconst2_2 csn cxp cfv fovconst2_2 fovconst2_3 fovconst2_4 fovconst2_0 fovconst2_1 cxp fovconst2_2 csn cxp df-ov fovconst2_3 fovconst2_0 wcel fovconst2_4 fovconst2_1 wcel wa fovconst2_3 fovconst2_4 cop fovconst2_0 fovconst2_1 cxp wcel fovconst2_3 fovconst2_4 cop fovconst2_0 fovconst2_1 cxp fovconst2_2 csn cxp cfv fovconst2_2 wceq fovconst2_3 fovconst2_4 fovconst2_0 fovconst2_1 opelxpi fovconst2_0 fovconst2_1 cxp fovconst2_2 fovconst2_3 fovconst2_4 cop eovconst2_0 fvconst2 syl syl5eq $.
$}
$( /* Existence of a class abstraction of existentially restricted sets.
       Variables ` x ` and ` y ` are normally free-variable parameters in the
       class expression substituted for ` C ` , which can be thought of as
       ` C ( x , y ) ` .  See comments for ~ abrexex .  (Contributed by NM,
       20-Sep-2011.) */

$)
${
	$d x z A $.
	$d y z B $.
	$d z C $.
	fab2rexex_0 $f set x $.
	fab2rexex_1 $f set y $.
	fab2rexex_2 $f set z $.
	fab2rexex_3 $f class A $.
	fab2rexex_4 $f class B $.
	fab2rexex_5 $f class C $.
	eab2rexex_0 $e |- A e. _V $.
	eab2rexex_1 $e |- B e. _V $.
	ab2rexex $p |- { z | E. x e. A E. y e. B z = C } e. _V $= fab2rexex_2 sup_set_class fab2rexex_5 wceq fab2rexex_1 fab2rexex_4 wrex fab2rexex_0 fab2rexex_2 fab2rexex_3 eab2rexex_0 fab2rexex_1 fab2rexex_2 fab2rexex_4 fab2rexex_5 eab2rexex_1 abrexex abrexex2 $.
$}
$( /* Existence of an existentially restricted class abstraction. ` ph ` is
       normally has free-variable parameters ` x ` , ` y ` , and ` z ` .
       Compare ~ abrexex2 .  (Contributed by NM, 20-Sep-2011.) */

$)
${
	$d x z A $.
	$d y z B $.
	fab2rexex2_0 $f wff ph $.
	fab2rexex2_1 $f set x $.
	fab2rexex2_2 $f set y $.
	fab2rexex2_3 $f set z $.
	fab2rexex2_4 $f class A $.
	fab2rexex2_5 $f class B $.
	eab2rexex2_0 $e |- A e. _V $.
	eab2rexex2_1 $e |- B e. _V $.
	eab2rexex2_2 $e |- { z | ph } e. _V $.
	ab2rexex2 $p |- { z | E. x e. A E. y e. B ph } e. _V $= fab2rexex2_0 fab2rexex2_2 fab2rexex2_5 wrex fab2rexex2_1 fab2rexex2_3 fab2rexex2_4 eab2rexex2_0 fab2rexex2_0 fab2rexex2_2 fab2rexex2_3 fab2rexex2_5 eab2rexex2_1 eab2rexex2_2 abrexex2 abrexex2 $.
$}
$( /* Domain of closure of an operation.  (Contributed by NM, 24-Aug-1995.) */

$)
${
	$d x y S $.
	$d x y F $.
	foprssdm_0 $f set x $.
	foprssdm_1 $f set y $.
	foprssdm_2 $f class S $.
	foprssdm_3 $f class F $.
	eoprssdm_0 $e |- -. (/) e. S $.
	eoprssdm_1 $e |- ( ( x e. S /\ y e. S ) -> ( x F y ) e. S ) $.
	oprssdm $p |- ( S X. S ) C_ dom F $= foprssdm_0 foprssdm_1 foprssdm_2 foprssdm_2 cxp foprssdm_3 cdm foprssdm_2 foprssdm_2 relxp foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_2 foprssdm_2 cxp wcel foprssdm_0 sup_set_class foprssdm_2 wcel foprssdm_1 sup_set_class foprssdm_2 wcel wa foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cdm wcel foprssdm_0 sup_set_class foprssdm_1 sup_set_class foprssdm_2 foprssdm_2 opelxp foprssdm_0 sup_set_class foprssdm_2 wcel foprssdm_1 sup_set_class foprssdm_2 wcel wa foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cfv foprssdm_2 wcel foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cdm wcel foprssdm_0 sup_set_class foprssdm_2 wcel foprssdm_1 sup_set_class foprssdm_2 wcel wa foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cfv foprssdm_0 sup_set_class foprssdm_1 sup_set_class foprssdm_3 co foprssdm_2 foprssdm_0 sup_set_class foprssdm_1 sup_set_class foprssdm_3 df-ov eoprssdm_1 syl5eqelr foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cdm wcel foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cfv foprssdm_2 wcel foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cdm wcel wn foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cfv foprssdm_2 wcel c0 foprssdm_2 wcel eoprssdm_0 foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cdm wcel wn foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 cfv c0 foprssdm_2 foprssdm_0 sup_set_class foprssdm_1 sup_set_class cop foprssdm_3 ndmfv eleq1d mtbiri con4i syl sylbi relssi $.
$}
$( /* The value of an operation outside its domain.  (Contributed by NM,
     28-Mar-2008.) */

$)
${
	fndmovg_0 $f class A $.
	fndmovg_1 $f class B $.
	fndmovg_2 $f class R $.
	fndmovg_3 $f class S $.
	fndmovg_4 $f class F $.
	ndmovg $p |- ( ( dom F = ( R X. S ) /\ -. ( A e. R /\ B e. S ) ) -> ( A F B ) = (/) ) $= fndmovg_4 cdm fndmovg_2 fndmovg_3 cxp wceq fndmovg_0 fndmovg_2 wcel fndmovg_1 fndmovg_3 wcel wa wn wa fndmovg_0 fndmovg_1 fndmovg_4 co fndmovg_0 fndmovg_1 cop fndmovg_4 cfv c0 fndmovg_0 fndmovg_1 fndmovg_4 df-ov fndmovg_4 cdm fndmovg_2 fndmovg_3 cxp wceq fndmovg_0 fndmovg_2 wcel fndmovg_1 fndmovg_3 wcel wa wn fndmovg_0 fndmovg_1 cop fndmovg_4 cfv c0 wceq fndmovg_4 cdm fndmovg_2 fndmovg_3 cxp wceq fndmovg_0 fndmovg_2 wcel fndmovg_1 fndmovg_3 wcel wa wn fndmovg_0 fndmovg_1 cop fndmovg_4 cdm wcel wn fndmovg_0 fndmovg_1 cop fndmovg_4 cfv c0 wceq fndmovg_4 cdm fndmovg_2 fndmovg_3 cxp wceq fndmovg_0 fndmovg_1 cop fndmovg_4 cdm wcel fndmovg_0 fndmovg_2 wcel fndmovg_1 fndmovg_3 wcel wa fndmovg_4 cdm fndmovg_2 fndmovg_3 cxp wceq fndmovg_0 fndmovg_1 cop fndmovg_4 cdm wcel fndmovg_0 fndmovg_1 cop fndmovg_2 fndmovg_3 cxp wcel fndmovg_0 fndmovg_2 wcel fndmovg_1 fndmovg_3 wcel wa fndmovg_4 cdm fndmovg_2 fndmovg_3 cxp fndmovg_0 fndmovg_1 cop eleq2 fndmovg_0 fndmovg_1 fndmovg_2 fndmovg_3 opelxp syl6bb notbid fndmovg_0 fndmovg_1 cop fndmovg_4 ndmfv syl6bir imp syl5eq $.
$}
$( /* The value of an operation outside its domain.  (Contributed by NM,
       24-Aug-1995.) */

$)
${
	fndmov_0 $f class A $.
	fndmov_1 $f class B $.
	fndmov_2 $f class S $.
	fndmov_3 $f class F $.
	endmov_0 $e |- dom F = ( S X. S ) $.
	ndmov $p |- ( -. ( A e. S /\ B e. S ) -> ( A F B ) = (/) ) $= fndmov_3 cdm fndmov_2 fndmov_2 cxp wceq fndmov_0 fndmov_2 wcel fndmov_1 fndmov_2 wcel wa wn fndmov_0 fndmov_1 fndmov_3 co c0 wceq endmov_0 fndmov_0 fndmov_1 fndmov_2 fndmov_2 fndmov_3 ndmovg mpan $.
$}
$( /* The closure of an operation outside its domain, when the domain
         includes the empty set.  This technical lemma can make the operation
         more convenient to work in some cases.  It is dependent on our
         particular definitions of operation value, function value, and ordered
         pair.  (Contributed by NM, 24-Sep-2004.) */

$)
${
	fndmovcl_0 $f class A $.
	fndmovcl_1 $f class B $.
	fndmovcl_2 $f class S $.
	fndmovcl_3 $f class F $.
	endmovcl_0 $e |- dom F = ( S X. S ) $.
	endmovcl_1 $e |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S ) $.
	endmovcl_2 $e |- (/) e. S $.
	ndmovcl $p |- ( A F B ) e. S $= fndmovcl_0 fndmovcl_2 wcel fndmovcl_1 fndmovcl_2 wcel wa fndmovcl_0 fndmovcl_1 fndmovcl_3 co fndmovcl_2 wcel endmovcl_1 fndmovcl_0 fndmovcl_2 wcel fndmovcl_1 fndmovcl_2 wcel wa wn fndmovcl_0 fndmovcl_1 fndmovcl_3 co c0 fndmovcl_2 fndmovcl_0 fndmovcl_1 fndmovcl_2 fndmovcl_3 endmovcl_0 ndmov endmovcl_2 syl6eqel pm2.61i $.
$}
$( /* Reverse closure law, when an operation's domain doesn't contain the
         empty set.  (Contributed by NM, 3-Feb-1996.) */

$)
${
	fndmovrcl_0 $f class A $.
	fndmovrcl_1 $f class B $.
	fndmovrcl_2 $f class S $.
	fndmovrcl_3 $f class F $.
	endmovrcl_0 $e |- dom F = ( S X. S ) $.
	endmovrcl_1 $e |- -. (/) e. S $.
	ndmovrcl $p |- ( ( A F B ) e. S -> ( A e. S /\ B e. S ) ) $= fndmovrcl_0 fndmovrcl_2 wcel fndmovrcl_1 fndmovrcl_2 wcel wa fndmovrcl_0 fndmovrcl_1 fndmovrcl_3 co fndmovrcl_2 wcel fndmovrcl_0 fndmovrcl_2 wcel fndmovrcl_1 fndmovrcl_2 wcel wa wn fndmovrcl_0 fndmovrcl_1 fndmovrcl_3 co fndmovrcl_2 wcel c0 fndmovrcl_2 wcel endmovrcl_1 fndmovrcl_0 fndmovrcl_2 wcel fndmovrcl_1 fndmovrcl_2 wcel wa wn fndmovrcl_0 fndmovrcl_1 fndmovrcl_3 co c0 fndmovrcl_2 fndmovrcl_0 fndmovrcl_1 fndmovrcl_2 fndmovrcl_3 endmovrcl_0 ndmov eleq1d mtbiri con4i $.
$}
$( /* Any operation is commutative outside its domain.  (Contributed by NM,
       24-Aug-1995.) */

$)
${
	fndmovcom_0 $f class A $.
	fndmovcom_1 $f class B $.
	fndmovcom_2 $f class S $.
	fndmovcom_3 $f class F $.
	endmovcom_0 $e |- dom F = ( S X. S ) $.
	ndmovcom $p |- ( -. ( A e. S /\ B e. S ) -> ( A F B ) = ( B F A ) ) $= fndmovcom_0 fndmovcom_2 wcel fndmovcom_1 fndmovcom_2 wcel wa wn fndmovcom_0 fndmovcom_1 fndmovcom_3 co c0 fndmovcom_1 fndmovcom_0 fndmovcom_3 co fndmovcom_0 fndmovcom_1 fndmovcom_2 fndmovcom_3 endmovcom_0 ndmov fndmovcom_0 fndmovcom_2 wcel fndmovcom_1 fndmovcom_2 wcel wa fndmovcom_1 fndmovcom_2 wcel fndmovcom_0 fndmovcom_2 wcel wa fndmovcom_1 fndmovcom_0 fndmovcom_3 co c0 wceq fndmovcom_0 fndmovcom_2 wcel fndmovcom_1 fndmovcom_2 wcel ancom fndmovcom_1 fndmovcom_0 fndmovcom_2 fndmovcom_3 endmovcom_0 ndmov sylnbi eqtr4d $.
$}
$( /* Any operation is associative outside its domain, if the domain doesn't
         contain the empty set.  (Contributed by NM, 24-Aug-1995.) */

$)
${
	fndmovass_0 $f class A $.
	fndmovass_1 $f class B $.
	fndmovass_2 $f class C $.
	fndmovass_3 $f class S $.
	fndmovass_4 $f class F $.
	endmovass_0 $e |- dom F = ( S X. S ) $.
	endmovass_1 $e |- -. (/) e. S $.
	ndmovass $p |- ( -. ( A e. S /\ B e. S /\ C e. S ) -> ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $= fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel w3a wn fndmovass_0 fndmovass_1 fndmovass_4 co fndmovass_2 fndmovass_4 co c0 fndmovass_0 fndmovass_1 fndmovass_2 fndmovass_4 co fndmovass_4 co fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel w3a wn fndmovass_0 fndmovass_1 fndmovass_4 co fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel wa wn fndmovass_0 fndmovass_1 fndmovass_4 co fndmovass_2 fndmovass_4 co c0 wceq fndmovass_0 fndmovass_1 fndmovass_4 co fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel wa fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel w3a fndmovass_0 fndmovass_1 fndmovass_4 co fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel wa fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel wa fndmovass_2 fndmovass_3 wcel wa fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel w3a fndmovass_0 fndmovass_1 fndmovass_4 co fndmovass_3 wcel fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel wa fndmovass_2 fndmovass_3 wcel fndmovass_0 fndmovass_1 fndmovass_3 fndmovass_4 endmovass_0 endmovass_1 ndmovrcl anim1i fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel df-3an sylibr con3i fndmovass_0 fndmovass_1 fndmovass_4 co fndmovass_2 fndmovass_3 fndmovass_4 endmovass_0 ndmov syl fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel w3a wn fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_2 fndmovass_4 co fndmovass_3 wcel wa wn fndmovass_0 fndmovass_1 fndmovass_2 fndmovass_4 co fndmovass_4 co c0 wceq fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_2 fndmovass_4 co fndmovass_3 wcel wa fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel w3a fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_2 fndmovass_4 co fndmovass_3 wcel wa fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel wa wa fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel w3a fndmovass_1 fndmovass_2 fndmovass_4 co fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel wa fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_2 fndmovass_3 fndmovass_4 endmovass_0 endmovass_1 ndmovrcl anim2i fndmovass_0 fndmovass_3 wcel fndmovass_1 fndmovass_3 wcel fndmovass_2 fndmovass_3 wcel 3anass sylibr con3i fndmovass_0 fndmovass_1 fndmovass_2 fndmovass_4 co fndmovass_3 fndmovass_4 endmovass_0 ndmov syl eqtr4d $.
$}
$( /* Any operation is distributive outside its domain, if the domain
         doesn't contain the empty set.  (Contributed by NM, 24-Aug-1995.) */

$)
${
	fndmovdistr_0 $f class A $.
	fndmovdistr_1 $f class B $.
	fndmovdistr_2 $f class C $.
	fndmovdistr_3 $f class S $.
	fndmovdistr_4 $f class F $.
	fndmovdistr_5 $f class G $.
	endmovdistr_0 $e |- dom F = ( S X. S ) $.
	endmovdistr_1 $e |- -. (/) e. S $.
	endmovdistr_2 $e |- dom G = ( S X. S ) $.
	ndmovdistr $p |- ( -. ( A e. S /\ B e. S /\ C e. S ) -> ( A G ( B F C ) ) = ( ( A G B ) F ( A G C ) ) ) $= fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel w3a wn fndmovdistr_0 fndmovdistr_1 fndmovdistr_2 fndmovdistr_4 co fndmovdistr_5 co c0 fndmovdistr_0 fndmovdistr_1 fndmovdistr_5 co fndmovdistr_0 fndmovdistr_2 fndmovdistr_5 co fndmovdistr_4 co fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel w3a wn fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_2 fndmovdistr_4 co fndmovdistr_3 wcel wa wn fndmovdistr_0 fndmovdistr_1 fndmovdistr_2 fndmovdistr_4 co fndmovdistr_5 co c0 wceq fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_2 fndmovdistr_4 co fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel w3a fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_2 fndmovdistr_4 co fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel wa wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel w3a fndmovdistr_1 fndmovdistr_2 fndmovdistr_4 co fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_2 fndmovdistr_3 fndmovdistr_4 endmovdistr_0 endmovdistr_1 ndmovrcl anim2i fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel 3anass sylibr con3i fndmovdistr_0 fndmovdistr_1 fndmovdistr_2 fndmovdistr_4 co fndmovdistr_3 fndmovdistr_5 endmovdistr_2 ndmov syl fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel w3a wn fndmovdistr_0 fndmovdistr_1 fndmovdistr_5 co fndmovdistr_3 wcel fndmovdistr_0 fndmovdistr_2 fndmovdistr_5 co fndmovdistr_3 wcel wa wn fndmovdistr_0 fndmovdistr_1 fndmovdistr_5 co fndmovdistr_0 fndmovdistr_2 fndmovdistr_5 co fndmovdistr_4 co c0 wceq fndmovdistr_0 fndmovdistr_1 fndmovdistr_5 co fndmovdistr_3 wcel fndmovdistr_0 fndmovdistr_2 fndmovdistr_5 co fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel w3a fndmovdistr_0 fndmovdistr_1 fndmovdistr_5 co fndmovdistr_3 wcel fndmovdistr_0 fndmovdistr_2 fndmovdistr_5 co fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel wa wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel w3a fndmovdistr_0 fndmovdistr_1 fndmovdistr_5 co fndmovdistr_3 wcel fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_2 fndmovdistr_5 co fndmovdistr_3 wcel fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_1 fndmovdistr_3 fndmovdistr_5 endmovdistr_2 endmovdistr_1 ndmovrcl fndmovdistr_0 fndmovdistr_2 fndmovdistr_3 fndmovdistr_5 endmovdistr_2 endmovdistr_1 ndmovrcl anim12i fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel w3a fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel wa wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel wa wa fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel 3anass fndmovdistr_0 fndmovdistr_3 wcel fndmovdistr_1 fndmovdistr_3 wcel fndmovdistr_2 fndmovdistr_3 wcel anandi bitri sylibr con3i fndmovdistr_0 fndmovdistr_1 fndmovdistr_5 co fndmovdistr_0 fndmovdistr_2 fndmovdistr_5 co fndmovdistr_3 fndmovdistr_4 endmovdistr_0 ndmov syl eqtr4d $.
$}
$( /* Elimination of redundant antecedents in an ordering law.  (Contributed
       by NM, 7-Mar-1996.) */

$)
${
	fndmovord_0 $f class A $.
	fndmovord_1 $f class B $.
	fndmovord_2 $f class C $.
	fndmovord_3 $f class R $.
	fndmovord_4 $f class S $.
	fndmovord_5 $f class F $.
	endmovord_0 $e |- dom F = ( S X. S ) $.
	endmovord_1 $e |- R C_ ( S X. S ) $.
	endmovord_2 $e |- -. (/) e. S $.
	endmovord_3 $e |- ( ( A e. S /\ B e. S /\ C e. S ) -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $.
	ndmovord $p |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $= fndmovord_0 fndmovord_4 wcel fndmovord_1 fndmovord_4 wcel wa fndmovord_2 fndmovord_4 wcel fndmovord_0 fndmovord_1 fndmovord_3 wbr fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_3 wbr wb wi fndmovord_0 fndmovord_4 wcel fndmovord_1 fndmovord_4 wcel fndmovord_2 fndmovord_4 wcel fndmovord_0 fndmovord_1 fndmovord_3 wbr fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_3 wbr wb endmovord_3 3expia fndmovord_0 fndmovord_4 wcel fndmovord_1 fndmovord_4 wcel wa wn fndmovord_0 fndmovord_1 fndmovord_3 wbr fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_3 wbr wb fndmovord_2 fndmovord_4 wcel fndmovord_0 fndmovord_1 fndmovord_3 wbr fndmovord_0 fndmovord_4 wcel fndmovord_1 fndmovord_4 wcel wa fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_3 wbr fndmovord_0 fndmovord_1 fndmovord_4 fndmovord_4 fndmovord_3 endmovord_1 brel fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_3 wbr fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_4 wcel fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_4 wcel wa fndmovord_0 fndmovord_4 wcel fndmovord_1 fndmovord_4 wcel wa fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_4 fndmovord_4 fndmovord_3 endmovord_1 brel fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_4 wcel fndmovord_0 fndmovord_4 wcel fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_4 wcel fndmovord_1 fndmovord_4 wcel fndmovord_2 fndmovord_0 fndmovord_5 co fndmovord_4 wcel fndmovord_2 fndmovord_4 wcel fndmovord_0 fndmovord_4 wcel fndmovord_2 fndmovord_0 fndmovord_4 fndmovord_5 endmovord_0 endmovord_2 ndmovrcl simprd fndmovord_2 fndmovord_1 fndmovord_5 co fndmovord_4 wcel fndmovord_2 fndmovord_4 wcel fndmovord_1 fndmovord_4 wcel fndmovord_2 fndmovord_1 fndmovord_4 fndmovord_5 endmovord_0 endmovord_2 ndmovrcl simprd anim12i syl pm5.21ni a1d pm2.61i $.
$}
$( /* Elimination of redundant antecedent in an ordering law.  (Contributed by
       NM, 25-Jun-1998.) */

$)
${
	fndmovordi_0 $f class A $.
	fndmovordi_1 $f class B $.
	fndmovordi_2 $f class C $.
	fndmovordi_3 $f class R $.
	fndmovordi_4 $f class S $.
	fndmovordi_5 $f class F $.
	endmovordi_0 $e |- dom F = ( S X. S ) $.
	endmovordi_1 $e |- R C_ ( S X. S ) $.
	endmovordi_2 $e |- -. (/) e. S $.
	endmovordi_3 $e |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $.
	ndmovordi $p |- ( ( C F A ) R ( C F B ) -> A R B ) $= fndmovordi_2 fndmovordi_4 wcel fndmovordi_2 fndmovordi_0 fndmovordi_5 co fndmovordi_2 fndmovordi_1 fndmovordi_5 co fndmovordi_3 wbr fndmovordi_0 fndmovordi_1 fndmovordi_3 wbr fndmovordi_2 fndmovordi_0 fndmovordi_5 co fndmovordi_2 fndmovordi_1 fndmovordi_5 co fndmovordi_3 wbr fndmovordi_2 fndmovordi_0 fndmovordi_5 co fndmovordi_4 wcel fndmovordi_2 fndmovordi_4 wcel fndmovordi_2 fndmovordi_0 fndmovordi_5 co fndmovordi_2 fndmovordi_1 fndmovordi_5 co fndmovordi_3 wbr fndmovordi_2 fndmovordi_0 fndmovordi_5 co fndmovordi_4 wcel fndmovordi_2 fndmovordi_1 fndmovordi_5 co fndmovordi_4 wcel fndmovordi_2 fndmovordi_0 fndmovordi_5 co fndmovordi_2 fndmovordi_1 fndmovordi_5 co fndmovordi_4 fndmovordi_4 fndmovordi_3 endmovordi_1 brel simpld fndmovordi_2 fndmovordi_0 fndmovordi_5 co fndmovordi_4 wcel fndmovordi_2 fndmovordi_4 wcel fndmovordi_0 fndmovordi_4 wcel fndmovordi_2 fndmovordi_0 fndmovordi_4 fndmovordi_5 endmovordi_0 endmovordi_2 ndmovrcl simpld syl fndmovordi_2 fndmovordi_4 wcel fndmovordi_0 fndmovordi_1 fndmovordi_3 wbr fndmovordi_2 fndmovordi_0 fndmovordi_5 co fndmovordi_2 fndmovordi_1 fndmovordi_5 co fndmovordi_3 wbr endmovordi_3 biimprd mpcom $.
$}
$( /* Convert an operation closure law to class notation.  (Contributed by
       Mario Carneiro, 26-May-2014.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x y C $.
	$d x y D $.
	$d x y E $.
	$d x y ph $.
	$d x y F $.
	fcaovclg_0 $f wff ph $.
	fcaovclg_1 $f set x $.
	fcaovclg_2 $f set y $.
	fcaovclg_3 $f class A $.
	fcaovclg_4 $f class B $.
	fcaovclg_5 $f class C $.
	fcaovclg_6 $f class D $.
	fcaovclg_7 $f class E $.
	fcaovclg_8 $f class F $.
	ecaovclg_0 $e |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x F y ) e. E ) $.
	caovclg $p |- ( ( ph /\ ( A e. C /\ B e. D ) ) -> ( A F B ) e. E ) $= fcaovclg_0 fcaovclg_1 sup_set_class fcaovclg_2 sup_set_class fcaovclg_8 co fcaovclg_7 wcel fcaovclg_2 fcaovclg_6 wral fcaovclg_1 fcaovclg_5 wral fcaovclg_3 fcaovclg_5 wcel fcaovclg_4 fcaovclg_6 wcel wa fcaovclg_3 fcaovclg_4 fcaovclg_8 co fcaovclg_7 wcel fcaovclg_0 fcaovclg_1 sup_set_class fcaovclg_2 sup_set_class fcaovclg_8 co fcaovclg_7 wcel fcaovclg_1 fcaovclg_2 fcaovclg_5 fcaovclg_6 ecaovclg_0 ralrimivva fcaovclg_1 sup_set_class fcaovclg_2 sup_set_class fcaovclg_8 co fcaovclg_7 wcel fcaovclg_3 fcaovclg_4 fcaovclg_8 co fcaovclg_7 wcel fcaovclg_3 fcaovclg_2 sup_set_class fcaovclg_8 co fcaovclg_7 wcel fcaovclg_1 fcaovclg_2 fcaovclg_3 fcaovclg_4 fcaovclg_5 fcaovclg_6 fcaovclg_1 sup_set_class fcaovclg_3 wceq fcaovclg_1 sup_set_class fcaovclg_2 sup_set_class fcaovclg_8 co fcaovclg_3 fcaovclg_2 sup_set_class fcaovclg_8 co fcaovclg_7 fcaovclg_1 sup_set_class fcaovclg_3 fcaovclg_2 sup_set_class fcaovclg_8 oveq1 eleq1d fcaovclg_2 sup_set_class fcaovclg_4 wceq fcaovclg_3 fcaovclg_2 sup_set_class fcaovclg_8 co fcaovclg_3 fcaovclg_4 fcaovclg_8 co fcaovclg_7 fcaovclg_2 sup_set_class fcaovclg_4 fcaovclg_3 fcaovclg_8 oveq2 eleq1d rspc2v mpan9 $.
$}
$( /* Convert an operation closure law to class notation.  (Contributed by
       Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x y C $.
	$d x y D $.
	$d x y E $.
	$d x y ph $.
	$d x y F $.
	fcaovcld_0 $f wff ph $.
	fcaovcld_1 $f set x $.
	fcaovcld_2 $f set y $.
	fcaovcld_3 $f class A $.
	fcaovcld_4 $f class B $.
	fcaovcld_5 $f class C $.
	fcaovcld_6 $f class D $.
	fcaovcld_7 $f class E $.
	fcaovcld_8 $f class F $.
	ecaovcld_0 $e |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x F y ) e. E ) $.
	ecaovcld_1 $e |- ( ph -> A e. C ) $.
	ecaovcld_2 $e |- ( ph -> B e. D ) $.
	caovcld $p |- ( ph -> ( A F B ) e. E ) $= fcaovcld_0 fcaovcld_0 fcaovcld_3 fcaovcld_5 wcel fcaovcld_4 fcaovcld_6 wcel fcaovcld_3 fcaovcld_4 fcaovcld_8 co fcaovcld_7 wcel fcaovcld_0 id ecaovcld_1 ecaovcld_2 fcaovcld_0 fcaovcld_1 fcaovcld_2 fcaovcld_3 fcaovcld_4 fcaovcld_5 fcaovcld_6 fcaovcld_7 fcaovcld_8 ecaovcld_0 caovclg syl12anc $.
$}
$( /* Convert an operation closure law to class notation.  (Contributed by NM,
       4-Aug-1995.)  (Revised by Mario Carneiro, 26-May-2014.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x y F $.
	$d x y $.
	$d x y S $.
	fcaovcl_0 $f set x $.
	fcaovcl_1 $f set y $.
	fcaovcl_2 $f class A $.
	fcaovcl_3 $f class B $.
	fcaovcl_4 $f class S $.
	fcaovcl_5 $f class F $.
	ecaovcl_0 $e |- ( ( x e. S /\ y e. S ) -> ( x F y ) e. S ) $.
	caovcl $p |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S ) $= wtru fcaovcl_2 fcaovcl_4 wcel fcaovcl_3 fcaovcl_4 wcel wa fcaovcl_2 fcaovcl_3 fcaovcl_5 co fcaovcl_4 wcel tru wtru fcaovcl_0 fcaovcl_1 fcaovcl_2 fcaovcl_3 fcaovcl_4 fcaovcl_4 fcaovcl_4 fcaovcl_5 fcaovcl_0 sup_set_class fcaovcl_4 wcel fcaovcl_1 sup_set_class fcaovcl_4 wcel wa fcaovcl_0 sup_set_class fcaovcl_1 sup_set_class fcaovcl_5 co fcaovcl_4 wcel wtru ecaovcl_0 adantl caovclg mpan $.
$}
$( /* General laws for commutative, associative, distributive operations. */

$)
$( /* Convert an operation commutative law to class notation.  (Contributed
         by Mario Carneiro, 1-Jun-2013.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y $.
	$d x y $.
	$d x y ph $.
	$d x y F $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y S $.
	$d x y $.
	fcaovcomg_0 $f wff ph $.
	fcaovcomg_1 $f set x $.
	fcaovcomg_2 $f set y $.
	fcaovcomg_3 $f class A $.
	fcaovcomg_4 $f class B $.
	fcaovcomg_5 $f class S $.
	fcaovcomg_6 $f class F $.
	ecaovcomg_0 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	caovcomg $p |- ( ( ph /\ ( A e. S /\ B e. S ) ) -> ( A F B ) = ( B F A ) ) $= fcaovcomg_0 fcaovcomg_1 sup_set_class fcaovcomg_2 sup_set_class fcaovcomg_6 co fcaovcomg_2 sup_set_class fcaovcomg_1 sup_set_class fcaovcomg_6 co wceq fcaovcomg_2 fcaovcomg_5 wral fcaovcomg_1 fcaovcomg_5 wral fcaovcomg_3 fcaovcomg_5 wcel fcaovcomg_4 fcaovcomg_5 wcel wa fcaovcomg_3 fcaovcomg_4 fcaovcomg_6 co fcaovcomg_4 fcaovcomg_3 fcaovcomg_6 co wceq fcaovcomg_0 fcaovcomg_1 sup_set_class fcaovcomg_2 sup_set_class fcaovcomg_6 co fcaovcomg_2 sup_set_class fcaovcomg_1 sup_set_class fcaovcomg_6 co wceq fcaovcomg_1 fcaovcomg_2 fcaovcomg_5 fcaovcomg_5 ecaovcomg_0 ralrimivva fcaovcomg_1 sup_set_class fcaovcomg_2 sup_set_class fcaovcomg_6 co fcaovcomg_2 sup_set_class fcaovcomg_1 sup_set_class fcaovcomg_6 co wceq fcaovcomg_3 fcaovcomg_4 fcaovcomg_6 co fcaovcomg_4 fcaovcomg_3 fcaovcomg_6 co wceq fcaovcomg_3 fcaovcomg_2 sup_set_class fcaovcomg_6 co fcaovcomg_2 sup_set_class fcaovcomg_3 fcaovcomg_6 co wceq fcaovcomg_1 fcaovcomg_2 fcaovcomg_3 fcaovcomg_4 fcaovcomg_5 fcaovcomg_5 fcaovcomg_1 sup_set_class fcaovcomg_3 wceq fcaovcomg_1 sup_set_class fcaovcomg_2 sup_set_class fcaovcomg_6 co fcaovcomg_3 fcaovcomg_2 sup_set_class fcaovcomg_6 co fcaovcomg_2 sup_set_class fcaovcomg_1 sup_set_class fcaovcomg_6 co fcaovcomg_2 sup_set_class fcaovcomg_3 fcaovcomg_6 co fcaovcomg_1 sup_set_class fcaovcomg_3 fcaovcomg_2 sup_set_class fcaovcomg_6 oveq1 fcaovcomg_1 sup_set_class fcaovcomg_3 fcaovcomg_2 sup_set_class fcaovcomg_6 oveq2 eqeq12d fcaovcomg_2 sup_set_class fcaovcomg_4 wceq fcaovcomg_3 fcaovcomg_2 sup_set_class fcaovcomg_6 co fcaovcomg_3 fcaovcomg_4 fcaovcomg_6 co fcaovcomg_2 sup_set_class fcaovcomg_3 fcaovcomg_6 co fcaovcomg_4 fcaovcomg_3 fcaovcomg_6 co fcaovcomg_2 sup_set_class fcaovcomg_4 fcaovcomg_3 fcaovcomg_6 oveq2 fcaovcomg_2 sup_set_class fcaovcomg_4 fcaovcomg_3 fcaovcomg_6 oveq1 eqeq12d rspc2v mpan9 $.
$}
$( /* Convert an operation commutative law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y $.
	$d x y $.
	$d x y ph $.
	$d x y F $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y S $.
	$d x y $.
	fcaovcomd_0 $f wff ph $.
	fcaovcomd_1 $f set x $.
	fcaovcomd_2 $f set y $.
	fcaovcomd_3 $f class A $.
	fcaovcomd_4 $f class B $.
	fcaovcomd_5 $f class S $.
	fcaovcomd_6 $f class F $.
	ecaovcomd_0 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaovcomd_1 $e |- ( ph -> A e. S ) $.
	ecaovcomd_2 $e |- ( ph -> B e. S ) $.
	caovcomd $p |- ( ph -> ( A F B ) = ( B F A ) ) $= fcaovcomd_0 fcaovcomd_0 fcaovcomd_3 fcaovcomd_5 wcel fcaovcomd_4 fcaovcomd_5 wcel fcaovcomd_3 fcaovcomd_4 fcaovcomd_6 co fcaovcomd_4 fcaovcomd_3 fcaovcomd_6 co wceq fcaovcomd_0 id ecaovcomd_1 ecaovcomd_2 fcaovcomd_0 fcaovcomd_1 fcaovcomd_2 fcaovcomd_3 fcaovcomd_4 fcaovcomd_5 fcaovcomd_6 ecaovcomd_0 caovcomg syl12anc $.
$}
$( /* Convert an operation commutative law to class notation.  (Contributed
         by NM, 26-Aug-1995.)  (Revised by Mario Carneiro, 1-Jun-2013.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y F $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	fcaovcom_0 $f set x $.
	fcaovcom_1 $f set y $.
	fcaovcom_2 $f class A $.
	fcaovcom_3 $f class B $.
	fcaovcom_4 $f class F $.
	ecaovcom_0 $e |- A e. _V $.
	ecaovcom_1 $e |- B e. _V $.
	ecaovcom_2 $e |- ( x F y ) = ( y F x ) $.
	caovcom $p |- ( A F B ) = ( B F A ) $= fcaovcom_2 cvv wcel fcaovcom_2 cvv wcel fcaovcom_3 cvv wcel wa fcaovcom_2 fcaovcom_3 fcaovcom_4 co fcaovcom_3 fcaovcom_2 fcaovcom_4 co wceq ecaovcom_0 fcaovcom_2 cvv wcel fcaovcom_3 cvv wcel ecaovcom_0 ecaovcom_1 pm3.2i fcaovcom_2 cvv wcel fcaovcom_0 fcaovcom_1 fcaovcom_2 fcaovcom_3 cvv fcaovcom_4 fcaovcom_0 sup_set_class fcaovcom_1 sup_set_class fcaovcom_4 co fcaovcom_1 sup_set_class fcaovcom_0 sup_set_class fcaovcom_4 co wceq fcaovcom_2 cvv wcel fcaovcom_0 sup_set_class cvv wcel fcaovcom_1 sup_set_class cvv wcel wa wa ecaovcom_2 a1i caovcomg mp2an $.
$}
$( /* Convert an operation associative law to class notation.  (Contributed
         by Mario Carneiro, 1-Jun-2013.)  (Revised by Mario Carneiro,
         26-May-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaovassg_0 $f wff ph $.
	fcaovassg_1 $f set x $.
	fcaovassg_2 $f set y $.
	fcaovassg_3 $f set z $.
	fcaovassg_4 $f class A $.
	fcaovassg_5 $f class B $.
	fcaovassg_6 $f class C $.
	fcaovassg_7 $f class S $.
	fcaovassg_8 $f class F $.
	ecaovassg_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	caovassg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) -> ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $= fcaovassg_0 fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co wceq fcaovassg_3 fcaovassg_7 wral fcaovassg_2 fcaovassg_7 wral fcaovassg_1 fcaovassg_7 wral fcaovassg_4 fcaovassg_7 wcel fcaovassg_5 fcaovassg_7 wcel fcaovassg_6 fcaovassg_7 wcel w3a fcaovassg_4 fcaovassg_5 fcaovassg_8 co fcaovassg_6 fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_6 fcaovassg_8 co fcaovassg_8 co wceq fcaovassg_0 fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co wceq fcaovassg_1 fcaovassg_2 fcaovassg_3 fcaovassg_7 fcaovassg_7 fcaovassg_7 ecaovassg_0 ralrimivvva fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co wceq fcaovassg_4 fcaovassg_5 fcaovassg_8 co fcaovassg_6 fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_6 fcaovassg_8 co fcaovassg_8 co wceq fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co wceq fcaovassg_4 fcaovassg_5 fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co wceq fcaovassg_1 fcaovassg_2 fcaovassg_3 fcaovassg_4 fcaovassg_5 fcaovassg_6 fcaovassg_7 fcaovassg_7 fcaovassg_7 fcaovassg_1 sup_set_class fcaovassg_4 wceq fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co fcaovassg_1 sup_set_class fcaovassg_4 wceq fcaovassg_1 sup_set_class fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 fcaovassg_1 sup_set_class fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_8 oveq1 oveq1d fcaovassg_1 sup_set_class fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 oveq1 eqeq12d fcaovassg_2 sup_set_class fcaovassg_5 wceq fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co fcaovassg_2 sup_set_class fcaovassg_5 wceq fcaovassg_4 fcaovassg_2 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 fcaovassg_2 sup_set_class fcaovassg_5 fcaovassg_4 fcaovassg_8 oveq2 oveq1d fcaovassg_2 sup_set_class fcaovassg_5 wceq fcaovassg_2 sup_set_class fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_5 fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_8 fcaovassg_2 sup_set_class fcaovassg_5 fcaovassg_3 sup_set_class fcaovassg_8 oveq1 oveq2d eqeq12d fcaovassg_3 sup_set_class fcaovassg_6 wceq fcaovassg_4 fcaovassg_5 fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_8 co fcaovassg_6 fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_8 co fcaovassg_4 fcaovassg_5 fcaovassg_6 fcaovassg_8 co fcaovassg_8 co fcaovassg_3 sup_set_class fcaovassg_6 fcaovassg_4 fcaovassg_5 fcaovassg_8 co fcaovassg_8 oveq2 fcaovassg_3 sup_set_class fcaovassg_6 wceq fcaovassg_5 fcaovassg_3 sup_set_class fcaovassg_8 co fcaovassg_5 fcaovassg_6 fcaovassg_8 co fcaovassg_4 fcaovassg_8 fcaovassg_3 sup_set_class fcaovassg_6 fcaovassg_5 fcaovassg_8 oveq2 oveq2d eqeq12d rspc3v mpan9 $.
$}
$( /* Convert an operation associative law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaovassd_0 $f wff ph $.
	fcaovassd_1 $f set x $.
	fcaovassd_2 $f set y $.
	fcaovassd_3 $f set z $.
	fcaovassd_4 $f class A $.
	fcaovassd_5 $f class B $.
	fcaovassd_6 $f class C $.
	fcaovassd_7 $f class S $.
	fcaovassd_8 $f class F $.
	ecaovassd_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	ecaovassd_1 $e |- ( ph -> A e. S ) $.
	ecaovassd_2 $e |- ( ph -> B e. S ) $.
	ecaovassd_3 $e |- ( ph -> C e. S ) $.
	caovassd $p |- ( ph -> ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $= fcaovassd_0 fcaovassd_0 fcaovassd_4 fcaovassd_7 wcel fcaovassd_5 fcaovassd_7 wcel fcaovassd_6 fcaovassd_7 wcel fcaovassd_4 fcaovassd_5 fcaovassd_8 co fcaovassd_6 fcaovassd_8 co fcaovassd_4 fcaovassd_5 fcaovassd_6 fcaovassd_8 co fcaovassd_8 co wceq fcaovassd_0 id ecaovassd_1 ecaovassd_2 ecaovassd_3 fcaovassd_0 fcaovassd_1 fcaovassd_2 fcaovassd_3 fcaovassd_4 fcaovassd_5 fcaovassd_6 fcaovassd_7 fcaovassd_8 ecaovassd_0 caovassg syl13anc $.
$}
$( /* Convert an operation associative law to class notation.  (Contributed
         by NM, 26-Aug-1995.)  (Revised by Mario Carneiro, 26-May-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaovass_0 $f set x $.
	fcaovass_1 $f set y $.
	fcaovass_2 $f set z $.
	fcaovass_3 $f class A $.
	fcaovass_4 $f class B $.
	fcaovass_5 $f class C $.
	fcaovass_6 $f class F $.
	ecaovass_0 $e |- A e. _V $.
	ecaovass_1 $e |- B e. _V $.
	ecaovass_2 $e |- C e. _V $.
	ecaovass_3 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	caovass $p |- ( ( A F B ) F C ) = ( A F ( B F C ) ) $= fcaovass_3 cvv wcel fcaovass_4 cvv wcel fcaovass_5 cvv wcel fcaovass_3 fcaovass_4 fcaovass_6 co fcaovass_5 fcaovass_6 co fcaovass_3 fcaovass_4 fcaovass_5 fcaovass_6 co fcaovass_6 co wceq ecaovass_0 ecaovass_1 ecaovass_2 wtru fcaovass_3 cvv wcel fcaovass_4 cvv wcel fcaovass_5 cvv wcel w3a fcaovass_3 fcaovass_4 fcaovass_6 co fcaovass_5 fcaovass_6 co fcaovass_3 fcaovass_4 fcaovass_5 fcaovass_6 co fcaovass_6 co wceq tru wtru fcaovass_0 fcaovass_1 fcaovass_2 fcaovass_3 fcaovass_4 fcaovass_5 cvv fcaovass_6 fcaovass_0 sup_set_class fcaovass_1 sup_set_class fcaovass_6 co fcaovass_2 sup_set_class fcaovass_6 co fcaovass_0 sup_set_class fcaovass_1 sup_set_class fcaovass_2 sup_set_class fcaovass_6 co fcaovass_6 co wceq wtru fcaovass_0 sup_set_class cvv wcel fcaovass_1 sup_set_class cvv wcel fcaovass_2 sup_set_class cvv wcel w3a wa ecaovass_3 a1i caovassg mpan mp3an $.
$}
$( /* Convert an operation cancellation law to class notation.  (Contributed
         by NM, 20-Aug-1995.)  (Revised by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z T $.
	fcaovcang_0 $f wff ph $.
	fcaovcang_1 $f set x $.
	fcaovcang_2 $f set y $.
	fcaovcang_3 $f set z $.
	fcaovcang_4 $f class A $.
	fcaovcang_5 $f class B $.
	fcaovcang_6 $f class C $.
	fcaovcang_7 $f class S $.
	fcaovcang_8 $f class T $.
	fcaovcang_9 $f class F $.
	ecaovcang_0 $e |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x F y ) = ( x F z ) <-> y = z ) ) $.
	caovcang $p |- ( ( ph /\ ( A e. T /\ B e. S /\ C e. S ) ) -> ( ( A F B ) = ( A F C ) <-> B = C ) ) $= fcaovcang_0 fcaovcang_1 sup_set_class fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_1 sup_set_class fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_2 sup_set_class fcaovcang_3 sup_set_class wceq wb fcaovcang_3 fcaovcang_7 wral fcaovcang_2 fcaovcang_7 wral fcaovcang_1 fcaovcang_8 wral fcaovcang_4 fcaovcang_8 wcel fcaovcang_5 fcaovcang_7 wcel fcaovcang_6 fcaovcang_7 wcel w3a fcaovcang_4 fcaovcang_5 fcaovcang_9 co fcaovcang_4 fcaovcang_6 fcaovcang_9 co wceq fcaovcang_5 fcaovcang_6 wceq wb fcaovcang_0 fcaovcang_1 sup_set_class fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_1 sup_set_class fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_2 sup_set_class fcaovcang_3 sup_set_class wceq wb fcaovcang_1 fcaovcang_2 fcaovcang_3 fcaovcang_8 fcaovcang_7 fcaovcang_7 ecaovcang_0 ralrimivvva fcaovcang_1 sup_set_class fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_1 sup_set_class fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_2 sup_set_class fcaovcang_3 sup_set_class wceq wb fcaovcang_4 fcaovcang_5 fcaovcang_9 co fcaovcang_4 fcaovcang_6 fcaovcang_9 co wceq fcaovcang_5 fcaovcang_6 wceq wb fcaovcang_4 fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_2 sup_set_class fcaovcang_3 sup_set_class wceq wb fcaovcang_4 fcaovcang_5 fcaovcang_9 co fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_5 fcaovcang_3 sup_set_class wceq wb fcaovcang_1 fcaovcang_2 fcaovcang_3 fcaovcang_4 fcaovcang_5 fcaovcang_6 fcaovcang_8 fcaovcang_7 fcaovcang_7 fcaovcang_1 sup_set_class fcaovcang_4 wceq fcaovcang_1 sup_set_class fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_1 sup_set_class fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_4 fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_2 sup_set_class fcaovcang_3 sup_set_class wceq fcaovcang_1 sup_set_class fcaovcang_4 wceq fcaovcang_1 sup_set_class fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_4 fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_1 sup_set_class fcaovcang_3 sup_set_class fcaovcang_9 co fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co fcaovcang_1 sup_set_class fcaovcang_4 fcaovcang_2 sup_set_class fcaovcang_9 oveq1 fcaovcang_1 sup_set_class fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 oveq1 eqeq12d bibi1d fcaovcang_2 sup_set_class fcaovcang_5 wceq fcaovcang_4 fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_4 fcaovcang_5 fcaovcang_9 co fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_2 sup_set_class fcaovcang_3 sup_set_class wceq fcaovcang_5 fcaovcang_3 sup_set_class wceq fcaovcang_2 sup_set_class fcaovcang_5 wceq fcaovcang_4 fcaovcang_2 sup_set_class fcaovcang_9 co fcaovcang_4 fcaovcang_5 fcaovcang_9 co fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co fcaovcang_2 sup_set_class fcaovcang_5 fcaovcang_4 fcaovcang_9 oveq2 eqeq1d fcaovcang_2 sup_set_class fcaovcang_5 fcaovcang_3 sup_set_class eqeq1 bibi12d fcaovcang_3 sup_set_class fcaovcang_6 wceq fcaovcang_4 fcaovcang_5 fcaovcang_9 co fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co wceq fcaovcang_4 fcaovcang_5 fcaovcang_9 co fcaovcang_4 fcaovcang_6 fcaovcang_9 co wceq fcaovcang_5 fcaovcang_3 sup_set_class wceq fcaovcang_5 fcaovcang_6 wceq fcaovcang_3 sup_set_class fcaovcang_6 wceq fcaovcang_4 fcaovcang_3 sup_set_class fcaovcang_9 co fcaovcang_4 fcaovcang_6 fcaovcang_9 co fcaovcang_4 fcaovcang_5 fcaovcang_9 co fcaovcang_3 sup_set_class fcaovcang_6 fcaovcang_4 fcaovcang_9 oveq2 eqeq2d fcaovcang_3 sup_set_class fcaovcang_6 fcaovcang_5 eqeq2 bibi12d rspc3v mpan9 $.
$}
$( /* Convert an operation cancellation law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z T $.
	fcaovcand_0 $f wff ph $.
	fcaovcand_1 $f set x $.
	fcaovcand_2 $f set y $.
	fcaovcand_3 $f set z $.
	fcaovcand_4 $f class A $.
	fcaovcand_5 $f class B $.
	fcaovcand_6 $f class C $.
	fcaovcand_7 $f class S $.
	fcaovcand_8 $f class T $.
	fcaovcand_9 $f class F $.
	ecaovcand_0 $e |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x F y ) = ( x F z ) <-> y = z ) ) $.
	ecaovcand_1 $e |- ( ph -> A e. T ) $.
	ecaovcand_2 $e |- ( ph -> B e. S ) $.
	ecaovcand_3 $e |- ( ph -> C e. S ) $.
	caovcand $p |- ( ph -> ( ( A F B ) = ( A F C ) <-> B = C ) ) $= fcaovcand_0 fcaovcand_0 fcaovcand_4 fcaovcand_8 wcel fcaovcand_5 fcaovcand_7 wcel fcaovcand_6 fcaovcand_7 wcel fcaovcand_4 fcaovcand_5 fcaovcand_9 co fcaovcand_4 fcaovcand_6 fcaovcand_9 co wceq fcaovcand_5 fcaovcand_6 wceq wb fcaovcand_0 id ecaovcand_1 ecaovcand_2 ecaovcand_3 fcaovcand_0 fcaovcand_1 fcaovcand_2 fcaovcand_3 fcaovcand_4 fcaovcand_5 fcaovcand_6 fcaovcand_7 fcaovcand_8 fcaovcand_9 ecaovcand_0 caovcang syl13anc $.
$}
$( /* Commute the arguments of an operation cancellation law.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z T $.
	fcaovcanrd_0 $f wff ph $.
	fcaovcanrd_1 $f set x $.
	fcaovcanrd_2 $f set y $.
	fcaovcanrd_3 $f set z $.
	fcaovcanrd_4 $f class A $.
	fcaovcanrd_5 $f class B $.
	fcaovcanrd_6 $f class C $.
	fcaovcanrd_7 $f class S $.
	fcaovcanrd_8 $f class T $.
	fcaovcanrd_9 $f class F $.
	ecaovcanrd_0 $e |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x F y ) = ( x F z ) <-> y = z ) ) $.
	ecaovcanrd_1 $e |- ( ph -> A e. T ) $.
	ecaovcanrd_2 $e |- ( ph -> B e. S ) $.
	ecaovcanrd_3 $e |- ( ph -> C e. S ) $.
	ecaovcanrd_4 $e |- ( ph -> A e. S ) $.
	ecaovcanrd_5 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	caovcanrd $p |- ( ph -> ( ( B F A ) = ( C F A ) <-> B = C ) ) $= fcaovcanrd_0 fcaovcanrd_4 fcaovcanrd_5 fcaovcanrd_9 co fcaovcanrd_4 fcaovcanrd_6 fcaovcanrd_9 co wceq fcaovcanrd_5 fcaovcanrd_4 fcaovcanrd_9 co fcaovcanrd_6 fcaovcanrd_4 fcaovcanrd_9 co wceq fcaovcanrd_5 fcaovcanrd_6 wceq fcaovcanrd_0 fcaovcanrd_4 fcaovcanrd_5 fcaovcanrd_9 co fcaovcanrd_5 fcaovcanrd_4 fcaovcanrd_9 co fcaovcanrd_4 fcaovcanrd_6 fcaovcanrd_9 co fcaovcanrd_6 fcaovcanrd_4 fcaovcanrd_9 co fcaovcanrd_0 fcaovcanrd_1 fcaovcanrd_2 fcaovcanrd_4 fcaovcanrd_5 fcaovcanrd_7 fcaovcanrd_9 ecaovcanrd_5 ecaovcanrd_4 ecaovcanrd_2 caovcomd fcaovcanrd_0 fcaovcanrd_1 fcaovcanrd_2 fcaovcanrd_4 fcaovcanrd_6 fcaovcanrd_7 fcaovcanrd_9 ecaovcanrd_5 ecaovcanrd_4 ecaovcanrd_3 caovcomd eqeq12d fcaovcanrd_0 fcaovcanrd_1 fcaovcanrd_2 fcaovcanrd_3 fcaovcanrd_4 fcaovcanrd_5 fcaovcanrd_6 fcaovcanrd_7 fcaovcanrd_8 fcaovcanrd_9 ecaovcanrd_0 ecaovcanrd_1 ecaovcanrd_2 ecaovcanrd_3 caovcand bitr3d $.
$}
$( /* Convert an operation cancellation law to class notation.  (Contributed
         by NM, 20-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaovcan_0 $f set x $.
	fcaovcan_1 $f set y $.
	fcaovcan_2 $f set z $.
	fcaovcan_3 $f class A $.
	fcaovcan_4 $f class B $.
	fcaovcan_5 $f class C $.
	fcaovcan_6 $f class S $.
	fcaovcan_7 $f class F $.
	ecaovcan_0 $e |- C e. _V $.
	ecaovcan_1 $e |- ( ( x e. S /\ y e. S ) -> ( ( x F y ) = ( x F z ) -> y = z ) ) $.
	caovcan $p |- ( ( A e. S /\ B e. S ) -> ( ( A F B ) = ( A F C ) -> B = C ) ) $= fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_5 fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_5 wceq wi fcaovcan_3 fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_3 fcaovcan_5 fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_5 wceq wi fcaovcan_3 fcaovcan_4 fcaovcan_7 co fcaovcan_3 fcaovcan_5 fcaovcan_7 co wceq fcaovcan_4 fcaovcan_5 wceq wi fcaovcan_0 fcaovcan_1 fcaovcan_3 fcaovcan_4 fcaovcan_6 fcaovcan_6 fcaovcan_0 sup_set_class fcaovcan_3 wceq fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_5 fcaovcan_7 co wceq fcaovcan_3 fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_3 fcaovcan_5 fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_5 wceq fcaovcan_0 sup_set_class fcaovcan_3 wceq fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_3 fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_5 fcaovcan_7 co fcaovcan_3 fcaovcan_5 fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_3 fcaovcan_1 sup_set_class fcaovcan_7 oveq1 fcaovcan_0 sup_set_class fcaovcan_3 fcaovcan_5 fcaovcan_7 oveq1 eqeq12d imbi1d fcaovcan_1 sup_set_class fcaovcan_4 wceq fcaovcan_3 fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_3 fcaovcan_5 fcaovcan_7 co wceq fcaovcan_3 fcaovcan_4 fcaovcan_7 co fcaovcan_3 fcaovcan_5 fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_5 wceq fcaovcan_4 fcaovcan_5 wceq fcaovcan_1 sup_set_class fcaovcan_4 wceq fcaovcan_3 fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_3 fcaovcan_4 fcaovcan_7 co fcaovcan_3 fcaovcan_5 fcaovcan_7 co fcaovcan_1 sup_set_class fcaovcan_4 fcaovcan_3 fcaovcan_7 oveq2 eqeq1d fcaovcan_1 sup_set_class fcaovcan_4 fcaovcan_5 eqeq1 imbi12d fcaovcan_0 sup_set_class fcaovcan_6 wcel fcaovcan_1 sup_set_class fcaovcan_6 wcel wa fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_2 sup_set_class fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_2 sup_set_class wceq wi wi fcaovcan_0 sup_set_class fcaovcan_6 wcel fcaovcan_1 sup_set_class fcaovcan_6 wcel wa fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_5 fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_5 wceq wi wi fcaovcan_2 fcaovcan_5 ecaovcan_0 fcaovcan_2 sup_set_class fcaovcan_5 wceq fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_2 sup_set_class fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_2 sup_set_class wceq wi fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_5 fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_5 wceq wi fcaovcan_0 sup_set_class fcaovcan_6 wcel fcaovcan_1 sup_set_class fcaovcan_6 wcel wa fcaovcan_2 sup_set_class fcaovcan_5 wceq fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_2 sup_set_class fcaovcan_7 co wceq fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_5 fcaovcan_7 co wceq fcaovcan_1 sup_set_class fcaovcan_2 sup_set_class wceq fcaovcan_1 sup_set_class fcaovcan_5 wceq fcaovcan_2 sup_set_class fcaovcan_5 wceq fcaovcan_0 sup_set_class fcaovcan_2 sup_set_class fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_5 fcaovcan_7 co fcaovcan_0 sup_set_class fcaovcan_1 sup_set_class fcaovcan_7 co fcaovcan_2 sup_set_class fcaovcan_5 fcaovcan_0 sup_set_class fcaovcan_7 oveq2 eqeq2d fcaovcan_2 sup_set_class fcaovcan_5 fcaovcan_1 sup_set_class eqeq2 imbi12d imbi2d ecaovcan_1 vtocl vtocl2ga $.
$}
$( /* Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 31-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovordig_0 $f wff ph $.
	fcaovordig_1 $f set x $.
	fcaovordig_2 $f set y $.
	fcaovordig_3 $f set z $.
	fcaovordig_4 $f class A $.
	fcaovordig_5 $f class B $.
	fcaovordig_6 $f class C $.
	fcaovordig_7 $f class R $.
	fcaovordig_8 $f class S $.
	fcaovordig_9 $f class F $.
	ecaovordig_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y -> ( z F x ) R ( z F y ) ) ) $.
	caovordig $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) -> ( A R B -> ( C F A ) R ( C F B ) ) ) $= fcaovordig_0 fcaovordig_1 sup_set_class fcaovordig_2 sup_set_class fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_1 sup_set_class fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_7 wbr wi fcaovordig_3 fcaovordig_8 wral fcaovordig_2 fcaovordig_8 wral fcaovordig_1 fcaovordig_8 wral fcaovordig_4 fcaovordig_8 wcel fcaovordig_5 fcaovordig_8 wcel fcaovordig_6 fcaovordig_8 wcel w3a fcaovordig_4 fcaovordig_5 fcaovordig_7 wbr fcaovordig_6 fcaovordig_4 fcaovordig_9 co fcaovordig_6 fcaovordig_5 fcaovordig_9 co fcaovordig_7 wbr wi fcaovordig_0 fcaovordig_1 sup_set_class fcaovordig_2 sup_set_class fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_1 sup_set_class fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_7 wbr wi fcaovordig_1 fcaovordig_2 fcaovordig_3 fcaovordig_8 fcaovordig_8 fcaovordig_8 ecaovordig_0 ralrimivvva fcaovordig_1 sup_set_class fcaovordig_2 sup_set_class fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_1 sup_set_class fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_7 wbr wi fcaovordig_4 fcaovordig_5 fcaovordig_7 wbr fcaovordig_6 fcaovordig_4 fcaovordig_9 co fcaovordig_6 fcaovordig_5 fcaovordig_9 co fcaovordig_7 wbr wi fcaovordig_4 fcaovordig_2 sup_set_class fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_7 wbr wi fcaovordig_4 fcaovordig_5 fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_5 fcaovordig_9 co fcaovordig_7 wbr wi fcaovordig_1 fcaovordig_2 fcaovordig_3 fcaovordig_4 fcaovordig_5 fcaovordig_6 fcaovordig_8 fcaovordig_8 fcaovordig_8 fcaovordig_1 sup_set_class fcaovordig_4 wceq fcaovordig_1 sup_set_class fcaovordig_2 sup_set_class fcaovordig_7 wbr fcaovordig_4 fcaovordig_2 sup_set_class fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_1 sup_set_class fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_7 wbr fcaovordig_1 sup_set_class fcaovordig_4 fcaovordig_2 sup_set_class fcaovordig_7 breq1 fcaovordig_1 sup_set_class fcaovordig_4 wceq fcaovordig_3 sup_set_class fcaovordig_1 sup_set_class fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_7 fcaovordig_1 sup_set_class fcaovordig_4 fcaovordig_3 sup_set_class fcaovordig_9 oveq2 breq1d imbi12d fcaovordig_2 sup_set_class fcaovordig_5 wceq fcaovordig_4 fcaovordig_2 sup_set_class fcaovordig_7 wbr fcaovordig_4 fcaovordig_5 fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_5 fcaovordig_9 co fcaovordig_7 wbr fcaovordig_2 sup_set_class fcaovordig_5 fcaovordig_4 fcaovordig_7 breq2 fcaovordig_2 sup_set_class fcaovordig_5 wceq fcaovordig_3 sup_set_class fcaovordig_2 sup_set_class fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_5 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_7 fcaovordig_2 sup_set_class fcaovordig_5 fcaovordig_3 sup_set_class fcaovordig_9 oveq2 breq2d imbi12d fcaovordig_3 sup_set_class fcaovordig_6 wceq fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_5 fcaovordig_9 co fcaovordig_7 wbr fcaovordig_6 fcaovordig_4 fcaovordig_9 co fcaovordig_6 fcaovordig_5 fcaovordig_9 co fcaovordig_7 wbr fcaovordig_4 fcaovordig_5 fcaovordig_7 wbr fcaovordig_3 sup_set_class fcaovordig_6 wceq fcaovordig_3 sup_set_class fcaovordig_4 fcaovordig_9 co fcaovordig_6 fcaovordig_4 fcaovordig_9 co fcaovordig_3 sup_set_class fcaovordig_5 fcaovordig_9 co fcaovordig_6 fcaovordig_5 fcaovordig_9 co fcaovordig_7 fcaovordig_3 sup_set_class fcaovordig_6 fcaovordig_4 fcaovordig_9 oveq1 fcaovordig_3 sup_set_class fcaovordig_6 fcaovordig_5 fcaovordig_9 oveq1 breq12d imbi2d rspc3v mpan9 $.
$}
$( /* Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 31-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovordid_0 $f wff ph $.
	fcaovordid_1 $f set x $.
	fcaovordid_2 $f set y $.
	fcaovordid_3 $f set z $.
	fcaovordid_4 $f class A $.
	fcaovordid_5 $f class B $.
	fcaovordid_6 $f class C $.
	fcaovordid_7 $f class R $.
	fcaovordid_8 $f class S $.
	fcaovordid_9 $f class F $.
	ecaovordid_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y -> ( z F x ) R ( z F y ) ) ) $.
	ecaovordid_1 $e |- ( ph -> A e. S ) $.
	ecaovordid_2 $e |- ( ph -> B e. S ) $.
	ecaovordid_3 $e |- ( ph -> C e. S ) $.
	caovordid $p |- ( ph -> ( A R B -> ( C F A ) R ( C F B ) ) ) $= fcaovordid_0 fcaovordid_0 fcaovordid_4 fcaovordid_8 wcel fcaovordid_5 fcaovordid_8 wcel fcaovordid_6 fcaovordid_8 wcel fcaovordid_4 fcaovordid_5 fcaovordid_7 wbr fcaovordid_6 fcaovordid_4 fcaovordid_9 co fcaovordid_6 fcaovordid_5 fcaovordid_9 co fcaovordid_7 wbr wi fcaovordid_0 id ecaovordid_1 ecaovordid_2 ecaovordid_3 fcaovordid_0 fcaovordid_1 fcaovordid_2 fcaovordid_3 fcaovordid_4 fcaovordid_5 fcaovordid_6 fcaovordid_7 fcaovordid_8 fcaovordid_9 ecaovordid_0 caovordig syl13anc $.
$}
$( /* Convert an operation ordering law to class notation.  (Contributed by
         NM, 19-Feb-1996.)  (Revised by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovordg_0 $f wff ph $.
	fcaovordg_1 $f set x $.
	fcaovordg_2 $f set y $.
	fcaovordg_3 $f set z $.
	fcaovordg_4 $f class A $.
	fcaovordg_5 $f class B $.
	fcaovordg_6 $f class C $.
	fcaovordg_7 $f class R $.
	fcaovordg_8 $f class S $.
	fcaovordg_9 $f class F $.
	ecaovordg_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	caovordg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $= fcaovordg_0 fcaovordg_1 sup_set_class fcaovordg_2 sup_set_class fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_1 sup_set_class fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_7 wbr wb fcaovordg_3 fcaovordg_8 wral fcaovordg_2 fcaovordg_8 wral fcaovordg_1 fcaovordg_8 wral fcaovordg_4 fcaovordg_8 wcel fcaovordg_5 fcaovordg_8 wcel fcaovordg_6 fcaovordg_8 wcel w3a fcaovordg_4 fcaovordg_5 fcaovordg_7 wbr fcaovordg_6 fcaovordg_4 fcaovordg_9 co fcaovordg_6 fcaovordg_5 fcaovordg_9 co fcaovordg_7 wbr wb fcaovordg_0 fcaovordg_1 sup_set_class fcaovordg_2 sup_set_class fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_1 sup_set_class fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_7 wbr wb fcaovordg_1 fcaovordg_2 fcaovordg_3 fcaovordg_8 fcaovordg_8 fcaovordg_8 ecaovordg_0 ralrimivvva fcaovordg_1 sup_set_class fcaovordg_2 sup_set_class fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_1 sup_set_class fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_7 wbr wb fcaovordg_4 fcaovordg_5 fcaovordg_7 wbr fcaovordg_6 fcaovordg_4 fcaovordg_9 co fcaovordg_6 fcaovordg_5 fcaovordg_9 co fcaovordg_7 wbr wb fcaovordg_4 fcaovordg_2 sup_set_class fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_7 wbr wb fcaovordg_4 fcaovordg_5 fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_5 fcaovordg_9 co fcaovordg_7 wbr wb fcaovordg_1 fcaovordg_2 fcaovordg_3 fcaovordg_4 fcaovordg_5 fcaovordg_6 fcaovordg_8 fcaovordg_8 fcaovordg_8 fcaovordg_1 sup_set_class fcaovordg_4 wceq fcaovordg_1 sup_set_class fcaovordg_2 sup_set_class fcaovordg_7 wbr fcaovordg_4 fcaovordg_2 sup_set_class fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_1 sup_set_class fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_7 wbr fcaovordg_1 sup_set_class fcaovordg_4 fcaovordg_2 sup_set_class fcaovordg_7 breq1 fcaovordg_1 sup_set_class fcaovordg_4 wceq fcaovordg_3 sup_set_class fcaovordg_1 sup_set_class fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_7 fcaovordg_1 sup_set_class fcaovordg_4 fcaovordg_3 sup_set_class fcaovordg_9 oveq2 breq1d bibi12d fcaovordg_2 sup_set_class fcaovordg_5 wceq fcaovordg_4 fcaovordg_2 sup_set_class fcaovordg_7 wbr fcaovordg_4 fcaovordg_5 fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_5 fcaovordg_9 co fcaovordg_7 wbr fcaovordg_2 sup_set_class fcaovordg_5 fcaovordg_4 fcaovordg_7 breq2 fcaovordg_2 sup_set_class fcaovordg_5 wceq fcaovordg_3 sup_set_class fcaovordg_2 sup_set_class fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_5 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_7 fcaovordg_2 sup_set_class fcaovordg_5 fcaovordg_3 sup_set_class fcaovordg_9 oveq2 breq2d bibi12d fcaovordg_3 sup_set_class fcaovordg_6 wceq fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_5 fcaovordg_9 co fcaovordg_7 wbr fcaovordg_6 fcaovordg_4 fcaovordg_9 co fcaovordg_6 fcaovordg_5 fcaovordg_9 co fcaovordg_7 wbr fcaovordg_4 fcaovordg_5 fcaovordg_7 wbr fcaovordg_3 sup_set_class fcaovordg_6 wceq fcaovordg_3 sup_set_class fcaovordg_4 fcaovordg_9 co fcaovordg_6 fcaovordg_4 fcaovordg_9 co fcaovordg_3 sup_set_class fcaovordg_5 fcaovordg_9 co fcaovordg_6 fcaovordg_5 fcaovordg_9 co fcaovordg_7 fcaovordg_3 sup_set_class fcaovordg_6 fcaovordg_4 fcaovordg_9 oveq1 fcaovordg_3 sup_set_class fcaovordg_6 fcaovordg_5 fcaovordg_9 oveq1 breq12d bibi2d rspc3v mpan9 $.
$}
$( /* Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovordd_0 $f wff ph $.
	fcaovordd_1 $f set x $.
	fcaovordd_2 $f set y $.
	fcaovordd_3 $f set z $.
	fcaovordd_4 $f class A $.
	fcaovordd_5 $f class B $.
	fcaovordd_6 $f class C $.
	fcaovordd_7 $f class R $.
	fcaovordd_8 $f class S $.
	fcaovordd_9 $f class F $.
	ecaovordd_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	ecaovordd_1 $e |- ( ph -> A e. S ) $.
	ecaovordd_2 $e |- ( ph -> B e. S ) $.
	ecaovordd_3 $e |- ( ph -> C e. S ) $.
	caovordd $p |- ( ph -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $= fcaovordd_0 fcaovordd_0 fcaovordd_4 fcaovordd_8 wcel fcaovordd_5 fcaovordd_8 wcel fcaovordd_6 fcaovordd_8 wcel fcaovordd_4 fcaovordd_5 fcaovordd_7 wbr fcaovordd_6 fcaovordd_4 fcaovordd_9 co fcaovordd_6 fcaovordd_5 fcaovordd_9 co fcaovordd_7 wbr wb fcaovordd_0 id ecaovordd_1 ecaovordd_2 ecaovordd_3 fcaovordd_0 fcaovordd_1 fcaovordd_2 fcaovordd_3 fcaovordd_4 fcaovordd_5 fcaovordd_6 fcaovordd_7 fcaovordd_8 fcaovordd_9 ecaovordd_0 caovordg syl13anc $.
$}
$( /* Operation ordering law with commuted arguments.  (Contributed by Mario
         Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovord2d_0 $f wff ph $.
	fcaovord2d_1 $f set x $.
	fcaovord2d_2 $f set y $.
	fcaovord2d_3 $f set z $.
	fcaovord2d_4 $f class A $.
	fcaovord2d_5 $f class B $.
	fcaovord2d_6 $f class C $.
	fcaovord2d_7 $f class R $.
	fcaovord2d_8 $f class S $.
	fcaovord2d_9 $f class F $.
	ecaovord2d_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	ecaovord2d_1 $e |- ( ph -> A e. S ) $.
	ecaovord2d_2 $e |- ( ph -> B e. S ) $.
	ecaovord2d_3 $e |- ( ph -> C e. S ) $.
	ecaovord2d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	caovord2d $p |- ( ph -> ( A R B <-> ( A F C ) R ( B F C ) ) ) $= fcaovord2d_0 fcaovord2d_4 fcaovord2d_5 fcaovord2d_7 wbr fcaovord2d_6 fcaovord2d_4 fcaovord2d_9 co fcaovord2d_6 fcaovord2d_5 fcaovord2d_9 co fcaovord2d_7 wbr fcaovord2d_4 fcaovord2d_6 fcaovord2d_9 co fcaovord2d_5 fcaovord2d_6 fcaovord2d_9 co fcaovord2d_7 wbr fcaovord2d_0 fcaovord2d_1 fcaovord2d_2 fcaovord2d_3 fcaovord2d_4 fcaovord2d_5 fcaovord2d_6 fcaovord2d_7 fcaovord2d_8 fcaovord2d_9 ecaovord2d_0 ecaovord2d_1 ecaovord2d_2 ecaovord2d_3 caovordd fcaovord2d_0 fcaovord2d_6 fcaovord2d_4 fcaovord2d_9 co fcaovord2d_4 fcaovord2d_6 fcaovord2d_9 co fcaovord2d_6 fcaovord2d_5 fcaovord2d_9 co fcaovord2d_5 fcaovord2d_6 fcaovord2d_9 co fcaovord2d_7 fcaovord2d_0 fcaovord2d_1 fcaovord2d_2 fcaovord2d_6 fcaovord2d_4 fcaovord2d_8 fcaovord2d_9 ecaovord2d_4 ecaovord2d_3 ecaovord2d_1 caovcomd fcaovord2d_0 fcaovord2d_1 fcaovord2d_2 fcaovord2d_6 fcaovord2d_5 fcaovord2d_8 fcaovord2d_9 ecaovord2d_4 ecaovord2d_3 ecaovord2d_2 caovcomd breq12d bitrd $.
$}
$( /* Ordering law.  (Contributed by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovord3d_0 $f wff ph $.
	fcaovord3d_1 $f set x $.
	fcaovord3d_2 $f set y $.
	fcaovord3d_3 $f set z $.
	fcaovord3d_4 $f class A $.
	fcaovord3d_5 $f class B $.
	fcaovord3d_6 $f class C $.
	fcaovord3d_7 $f class D $.
	fcaovord3d_8 $f class R $.
	fcaovord3d_9 $f class S $.
	fcaovord3d_10 $f class F $.
	ecaovord3d_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	ecaovord3d_1 $e |- ( ph -> A e. S ) $.
	ecaovord3d_2 $e |- ( ph -> B e. S ) $.
	ecaovord3d_3 $e |- ( ph -> C e. S ) $.
	ecaovord3d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaovord3d_5 $e |- ( ph -> D e. S ) $.
	caovord3d $p |- ( ph -> ( ( A F B ) = ( C F D ) -> ( A R C <-> D R B ) ) ) $= fcaovord3d_4 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_6 fcaovord3d_7 fcaovord3d_10 co wceq fcaovord3d_4 fcaovord3d_6 fcaovord3d_8 wbr fcaovord3d_7 fcaovord3d_5 fcaovord3d_8 wbr wb fcaovord3d_0 fcaovord3d_4 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_6 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_8 wbr fcaovord3d_6 fcaovord3d_7 fcaovord3d_10 co fcaovord3d_6 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_8 wbr wb fcaovord3d_4 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_6 fcaovord3d_7 fcaovord3d_10 co fcaovord3d_6 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_8 breq1 fcaovord3d_0 fcaovord3d_4 fcaovord3d_6 fcaovord3d_8 wbr fcaovord3d_4 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_6 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_8 wbr fcaovord3d_7 fcaovord3d_5 fcaovord3d_8 wbr fcaovord3d_6 fcaovord3d_7 fcaovord3d_10 co fcaovord3d_6 fcaovord3d_5 fcaovord3d_10 co fcaovord3d_8 wbr fcaovord3d_0 fcaovord3d_1 fcaovord3d_2 fcaovord3d_3 fcaovord3d_4 fcaovord3d_6 fcaovord3d_5 fcaovord3d_8 fcaovord3d_9 fcaovord3d_10 ecaovord3d_0 ecaovord3d_1 ecaovord3d_3 ecaovord3d_2 ecaovord3d_4 caovord2d fcaovord3d_0 fcaovord3d_1 fcaovord3d_2 fcaovord3d_3 fcaovord3d_7 fcaovord3d_5 fcaovord3d_6 fcaovord3d_8 fcaovord3d_9 fcaovord3d_10 ecaovord3d_0 ecaovord3d_5 ecaovord3d_2 ecaovord3d_3 caovordd bibi12d syl5ibr $.
$}
$( /* Convert an operation ordering law to class notation.  (Contributed by
         NM, 19-Feb-1996.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovord_0 $f set x $.
	fcaovord_1 $f set y $.
	fcaovord_2 $f set z $.
	fcaovord_3 $f class A $.
	fcaovord_4 $f class B $.
	fcaovord_5 $f class C $.
	fcaovord_6 $f class R $.
	fcaovord_7 $f class S $.
	fcaovord_8 $f class F $.
	ecaovord_0 $e |- A e. _V $.
	ecaovord_1 $e |- B e. _V $.
	ecaovord_2 $e |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	caovord $p |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $= fcaovord_3 fcaovord_4 fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_4 fcaovord_8 co fcaovord_6 wbr wb fcaovord_3 fcaovord_4 fcaovord_6 wbr fcaovord_5 fcaovord_3 fcaovord_8 co fcaovord_5 fcaovord_4 fcaovord_8 co fcaovord_6 wbr wb fcaovord_2 fcaovord_5 fcaovord_7 fcaovord_2 sup_set_class fcaovord_5 wceq fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_4 fcaovord_8 co fcaovord_6 wbr fcaovord_5 fcaovord_3 fcaovord_8 co fcaovord_5 fcaovord_4 fcaovord_8 co fcaovord_6 wbr fcaovord_3 fcaovord_4 fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_5 wceq fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_5 fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_4 fcaovord_8 co fcaovord_5 fcaovord_4 fcaovord_8 co fcaovord_6 fcaovord_2 sup_set_class fcaovord_5 fcaovord_3 fcaovord_8 oveq1 fcaovord_2 sup_set_class fcaovord_5 fcaovord_4 fcaovord_8 oveq1 breq12d bibi2d fcaovord_2 sup_set_class fcaovord_7 wcel fcaovord_0 sup_set_class fcaovord_1 sup_set_class fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_0 sup_set_class fcaovord_8 co fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_6 wbr wb wi fcaovord_2 sup_set_class fcaovord_7 wcel fcaovord_3 fcaovord_4 fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_4 fcaovord_8 co fcaovord_6 wbr wb wi fcaovord_0 fcaovord_1 fcaovord_3 fcaovord_4 ecaovord_0 ecaovord_1 fcaovord_0 sup_set_class fcaovord_3 wceq fcaovord_1 sup_set_class fcaovord_4 wceq wa fcaovord_0 sup_set_class fcaovord_1 sup_set_class fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_0 sup_set_class fcaovord_8 co fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_6 wbr wb fcaovord_3 fcaovord_4 fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_4 fcaovord_8 co fcaovord_6 wbr wb fcaovord_2 sup_set_class fcaovord_7 wcel fcaovord_0 sup_set_class fcaovord_3 wceq fcaovord_0 sup_set_class fcaovord_1 sup_set_class fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_0 sup_set_class fcaovord_8 co fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_6 wbr wb fcaovord_3 fcaovord_1 sup_set_class fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_6 wbr wb fcaovord_1 sup_set_class fcaovord_4 wceq fcaovord_3 fcaovord_4 fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_4 fcaovord_8 co fcaovord_6 wbr wb fcaovord_0 sup_set_class fcaovord_3 wceq fcaovord_0 sup_set_class fcaovord_1 sup_set_class fcaovord_6 wbr fcaovord_3 fcaovord_1 sup_set_class fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_0 sup_set_class fcaovord_8 co fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_6 wbr fcaovord_0 sup_set_class fcaovord_3 fcaovord_1 sup_set_class fcaovord_6 breq1 fcaovord_0 sup_set_class fcaovord_3 wceq fcaovord_2 sup_set_class fcaovord_0 sup_set_class fcaovord_8 co fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_6 fcaovord_0 sup_set_class fcaovord_3 fcaovord_2 sup_set_class fcaovord_8 oveq2 breq1d bibi12d fcaovord_1 sup_set_class fcaovord_4 wceq fcaovord_3 fcaovord_1 sup_set_class fcaovord_6 wbr fcaovord_3 fcaovord_4 fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_6 wbr fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_4 fcaovord_8 co fcaovord_6 wbr fcaovord_1 sup_set_class fcaovord_4 fcaovord_3 fcaovord_6 breq2 fcaovord_1 sup_set_class fcaovord_4 wceq fcaovord_2 sup_set_class fcaovord_1 sup_set_class fcaovord_8 co fcaovord_2 sup_set_class fcaovord_4 fcaovord_8 co fcaovord_2 sup_set_class fcaovord_3 fcaovord_8 co fcaovord_6 fcaovord_1 sup_set_class fcaovord_4 fcaovord_2 sup_set_class fcaovord_8 oveq2 breq2d bibi12d sylan9bb imbi2d ecaovord_2 vtocl2 vtoclga $.
$}
$( /* (We don't bother to eliminate this redundant hypothesis.) */

$)
$( /* Operation ordering law with commuted arguments.  (Contributed by NM,
         27-Feb-1996.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovord2_0 $f set x $.
	fcaovord2_1 $f set y $.
	fcaovord2_2 $f set z $.
	fcaovord2_3 $f class A $.
	fcaovord2_4 $f class B $.
	fcaovord2_5 $f class C $.
	fcaovord2_6 $f class R $.
	fcaovord2_7 $f class S $.
	fcaovord2_8 $f class F $.
	ecaovord2_0 $e |- A e. _V $.
	ecaovord2_1 $e |- B e. _V $.
	ecaovord2_2 $e |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	ecaovord2_3 $e |- C e. _V $.
	ecaovord2_4 $e |- ( x F y ) = ( y F x ) $.
	caovord2 $p |- ( C e. S -> ( A R B <-> ( A F C ) R ( B F C ) ) ) $= fcaovord2_5 fcaovord2_7 wcel fcaovord2_3 fcaovord2_4 fcaovord2_6 wbr fcaovord2_5 fcaovord2_3 fcaovord2_8 co fcaovord2_5 fcaovord2_4 fcaovord2_8 co fcaovord2_6 wbr fcaovord2_3 fcaovord2_5 fcaovord2_8 co fcaovord2_4 fcaovord2_5 fcaovord2_8 co fcaovord2_6 wbr fcaovord2_0 fcaovord2_1 fcaovord2_2 fcaovord2_3 fcaovord2_4 fcaovord2_5 fcaovord2_6 fcaovord2_7 fcaovord2_8 ecaovord2_0 ecaovord2_1 ecaovord2_2 caovord fcaovord2_5 fcaovord2_3 fcaovord2_8 co fcaovord2_3 fcaovord2_5 fcaovord2_8 co fcaovord2_5 fcaovord2_4 fcaovord2_8 co fcaovord2_4 fcaovord2_5 fcaovord2_8 co fcaovord2_6 fcaovord2_0 fcaovord2_1 fcaovord2_5 fcaovord2_3 fcaovord2_8 ecaovord2_3 ecaovord2_0 ecaovord2_4 caovcom fcaovord2_0 fcaovord2_1 fcaovord2_5 fcaovord2_4 fcaovord2_8 ecaovord2_3 ecaovord2_1 ecaovord2_4 caovcom breq12i syl6bb $.
$}
$( /* (We don't bother to eliminate redundant hypotheses.) */

$)
$( /* Ordering law.  (Contributed by NM, 29-Feb-1996.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	$d x y z $.
	fcaovord3_0 $f set x $.
	fcaovord3_1 $f set y $.
	fcaovord3_2 $f set z $.
	fcaovord3_3 $f class A $.
	fcaovord3_4 $f class B $.
	fcaovord3_5 $f class C $.
	fcaovord3_6 $f class D $.
	fcaovord3_7 $f class R $.
	fcaovord3_8 $f class S $.
	fcaovord3_9 $f class F $.
	ecaovord3_0 $e |- A e. _V $.
	ecaovord3_1 $e |- B e. _V $.
	ecaovord3_2 $e |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	ecaovord3_3 $e |- C e. _V $.
	ecaovord3_4 $e |- ( x F y ) = ( y F x ) $.
	ecaovord3_5 $e |- D e. _V $.
	caovord3 $p |- ( ( ( B e. S /\ C e. S ) /\ ( A F B ) = ( C F D ) ) -> ( A R C <-> D R B ) ) $= fcaovord3_4 fcaovord3_8 wcel fcaovord3_5 fcaovord3_8 wcel wa fcaovord3_3 fcaovord3_4 fcaovord3_9 co fcaovord3_5 fcaovord3_6 fcaovord3_9 co wceq wa fcaovord3_3 fcaovord3_5 fcaovord3_7 wbr fcaovord3_5 fcaovord3_6 fcaovord3_9 co fcaovord3_5 fcaovord3_4 fcaovord3_9 co fcaovord3_7 wbr fcaovord3_6 fcaovord3_4 fcaovord3_7 wbr fcaovord3_4 fcaovord3_8 wcel fcaovord3_5 fcaovord3_8 wcel wa fcaovord3_3 fcaovord3_5 fcaovord3_7 wbr fcaovord3_3 fcaovord3_4 fcaovord3_9 co fcaovord3_5 fcaovord3_4 fcaovord3_9 co fcaovord3_7 wbr fcaovord3_3 fcaovord3_4 fcaovord3_9 co fcaovord3_5 fcaovord3_6 fcaovord3_9 co wceq fcaovord3_5 fcaovord3_6 fcaovord3_9 co fcaovord3_5 fcaovord3_4 fcaovord3_9 co fcaovord3_7 wbr fcaovord3_4 fcaovord3_8 wcel fcaovord3_3 fcaovord3_5 fcaovord3_7 wbr fcaovord3_3 fcaovord3_4 fcaovord3_9 co fcaovord3_5 fcaovord3_4 fcaovord3_9 co fcaovord3_7 wbr wb fcaovord3_5 fcaovord3_8 wcel fcaovord3_0 fcaovord3_1 fcaovord3_2 fcaovord3_3 fcaovord3_5 fcaovord3_4 fcaovord3_7 fcaovord3_8 fcaovord3_9 ecaovord3_0 ecaovord3_3 ecaovord3_2 ecaovord3_1 ecaovord3_4 caovord2 adantr fcaovord3_3 fcaovord3_4 fcaovord3_9 co fcaovord3_5 fcaovord3_6 fcaovord3_9 co fcaovord3_5 fcaovord3_4 fcaovord3_9 co fcaovord3_7 breq1 sylan9bb fcaovord3_5 fcaovord3_8 wcel fcaovord3_6 fcaovord3_4 fcaovord3_7 wbr fcaovord3_5 fcaovord3_6 fcaovord3_9 co fcaovord3_5 fcaovord3_4 fcaovord3_9 co fcaovord3_7 wbr wb fcaovord3_4 fcaovord3_8 wcel fcaovord3_3 fcaovord3_4 fcaovord3_9 co fcaovord3_5 fcaovord3_6 fcaovord3_9 co wceq fcaovord3_0 fcaovord3_1 fcaovord3_2 fcaovord3_6 fcaovord3_4 fcaovord3_5 fcaovord3_7 fcaovord3_8 fcaovord3_9 ecaovord3_5 ecaovord3_1 ecaovord3_2 caovord ad2antlr bitr4d $.
$}
$( /* Convert an operation distributive law to class notation.  (Contributed
         by NM, 25-Aug-1995.)  (Revised by Mario Carneiro, 26-Jul-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z G $.
	$d x y z H $.
	$d x y z K $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaovdig_0 $f wff ph $.
	fcaovdig_1 $f set x $.
	fcaovdig_2 $f set y $.
	fcaovdig_3 $f set z $.
	fcaovdig_4 $f class A $.
	fcaovdig_5 $f class B $.
	fcaovdig_6 $f class C $.
	fcaovdig_7 $f class S $.
	fcaovdig_8 $f class F $.
	fcaovdig_9 $f class G $.
	fcaovdig_10 $f class H $.
	fcaovdig_11 $f class K $.
	ecaovdig_0 $e |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) H ( x G z ) ) ) $.
	caovdig $p |- ( ( ph /\ ( A e. K /\ B e. S /\ C e. S ) ) -> ( A G ( B F C ) ) = ( ( A G B ) H ( A G C ) ) ) $= fcaovdig_0 fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co wceq fcaovdig_3 fcaovdig_7 wral fcaovdig_2 fcaovdig_7 wral fcaovdig_1 fcaovdig_11 wral fcaovdig_4 fcaovdig_11 wcel fcaovdig_5 fcaovdig_7 wcel fcaovdig_6 fcaovdig_7 wcel w3a fcaovdig_4 fcaovdig_5 fcaovdig_6 fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_5 fcaovdig_9 co fcaovdig_4 fcaovdig_6 fcaovdig_9 co fcaovdig_10 co wceq fcaovdig_0 fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co wceq fcaovdig_1 fcaovdig_2 fcaovdig_3 fcaovdig_11 fcaovdig_7 fcaovdig_7 ecaovdig_0 ralrimivvva fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co wceq fcaovdig_4 fcaovdig_5 fcaovdig_6 fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_5 fcaovdig_9 co fcaovdig_4 fcaovdig_6 fcaovdig_9 co fcaovdig_10 co wceq fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co wceq fcaovdig_4 fcaovdig_5 fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_5 fcaovdig_9 co fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co wceq fcaovdig_1 fcaovdig_2 fcaovdig_3 fcaovdig_4 fcaovdig_5 fcaovdig_6 fcaovdig_11 fcaovdig_7 fcaovdig_7 fcaovdig_1 sup_set_class fcaovdig_4 wceq fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co fcaovdig_1 sup_set_class fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 oveq1 fcaovdig_1 sup_set_class fcaovdig_4 wceq fcaovdig_1 sup_set_class fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_1 sup_set_class fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 fcaovdig_1 sup_set_class fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_9 oveq1 fcaovdig_1 sup_set_class fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 oveq1 oveq12d eqeq12d fcaovdig_2 sup_set_class fcaovdig_5 wceq fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_5 fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co fcaovdig_4 fcaovdig_5 fcaovdig_9 co fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co fcaovdig_2 sup_set_class fcaovdig_5 wceq fcaovdig_2 sup_set_class fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_5 fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_4 fcaovdig_9 fcaovdig_2 sup_set_class fcaovdig_5 fcaovdig_3 sup_set_class fcaovdig_8 oveq1 oveq2d fcaovdig_2 sup_set_class fcaovdig_5 wceq fcaovdig_4 fcaovdig_2 sup_set_class fcaovdig_9 co fcaovdig_4 fcaovdig_5 fcaovdig_9 co fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 fcaovdig_2 sup_set_class fcaovdig_5 fcaovdig_4 fcaovdig_9 oveq2 oveq1d eqeq12d fcaovdig_3 sup_set_class fcaovdig_6 wceq fcaovdig_4 fcaovdig_5 fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_5 fcaovdig_6 fcaovdig_8 co fcaovdig_9 co fcaovdig_4 fcaovdig_5 fcaovdig_9 co fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_10 co fcaovdig_4 fcaovdig_5 fcaovdig_9 co fcaovdig_4 fcaovdig_6 fcaovdig_9 co fcaovdig_10 co fcaovdig_3 sup_set_class fcaovdig_6 wceq fcaovdig_5 fcaovdig_3 sup_set_class fcaovdig_8 co fcaovdig_5 fcaovdig_6 fcaovdig_8 co fcaovdig_4 fcaovdig_9 fcaovdig_3 sup_set_class fcaovdig_6 fcaovdig_5 fcaovdig_8 oveq2 oveq2d fcaovdig_3 sup_set_class fcaovdig_6 wceq fcaovdig_4 fcaovdig_3 sup_set_class fcaovdig_9 co fcaovdig_4 fcaovdig_6 fcaovdig_9 co fcaovdig_4 fcaovdig_5 fcaovdig_9 co fcaovdig_10 fcaovdig_3 sup_set_class fcaovdig_6 fcaovdig_4 fcaovdig_9 oveq2 oveq2d eqeq12d rspc3v mpan9 $.
$}
$( /* Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z G $.
	$d x y z H $.
	$d x y z K $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaovdid_0 $f wff ph $.
	fcaovdid_1 $f set x $.
	fcaovdid_2 $f set y $.
	fcaovdid_3 $f set z $.
	fcaovdid_4 $f class A $.
	fcaovdid_5 $f class B $.
	fcaovdid_6 $f class C $.
	fcaovdid_7 $f class S $.
	fcaovdid_8 $f class F $.
	fcaovdid_9 $f class G $.
	fcaovdid_10 $f class H $.
	fcaovdid_11 $f class K $.
	ecaovdid_0 $e |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) H ( x G z ) ) ) $.
	ecaovdid_1 $e |- ( ph -> A e. K ) $.
	ecaovdid_2 $e |- ( ph -> B e. S ) $.
	ecaovdid_3 $e |- ( ph -> C e. S ) $.
	caovdid $p |- ( ph -> ( A G ( B F C ) ) = ( ( A G B ) H ( A G C ) ) ) $= fcaovdid_0 fcaovdid_0 fcaovdid_4 fcaovdid_11 wcel fcaovdid_5 fcaovdid_7 wcel fcaovdid_6 fcaovdid_7 wcel fcaovdid_4 fcaovdid_5 fcaovdid_6 fcaovdid_8 co fcaovdid_9 co fcaovdid_4 fcaovdid_5 fcaovdid_9 co fcaovdid_4 fcaovdid_6 fcaovdid_9 co fcaovdid_10 co wceq fcaovdid_0 id ecaovdid_1 ecaovdid_2 ecaovdid_3 fcaovdid_0 fcaovdid_1 fcaovdid_2 fcaovdid_3 fcaovdid_4 fcaovdid_5 fcaovdid_6 fcaovdid_7 fcaovdid_8 fcaovdid_9 fcaovdid_10 fcaovdid_11 ecaovdid_0 caovdig syl13anc $.
$}
$( /* Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z G $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaovdir2d_0 $f wff ph $.
	fcaovdir2d_1 $f set x $.
	fcaovdir2d_2 $f set y $.
	fcaovdir2d_3 $f set z $.
	fcaovdir2d_4 $f class A $.
	fcaovdir2d_5 $f class B $.
	fcaovdir2d_6 $f class C $.
	fcaovdir2d_7 $f class S $.
	fcaovdir2d_8 $f class F $.
	fcaovdir2d_9 $f class G $.
	ecaovdir2d_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) ) $.
	ecaovdir2d_1 $e |- ( ph -> A e. S ) $.
	ecaovdir2d_2 $e |- ( ph -> B e. S ) $.
	ecaovdir2d_3 $e |- ( ph -> C e. S ) $.
	ecaovdir2d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
	ecaovdir2d_5 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x G y ) = ( y G x ) ) $.
	caovdir2d $p |- ( ph -> ( ( A F B ) G C ) = ( ( A G C ) F ( B G C ) ) ) $= fcaovdir2d_0 fcaovdir2d_6 fcaovdir2d_4 fcaovdir2d_5 fcaovdir2d_8 co fcaovdir2d_9 co fcaovdir2d_6 fcaovdir2d_4 fcaovdir2d_9 co fcaovdir2d_6 fcaovdir2d_5 fcaovdir2d_9 co fcaovdir2d_8 co fcaovdir2d_4 fcaovdir2d_5 fcaovdir2d_8 co fcaovdir2d_6 fcaovdir2d_9 co fcaovdir2d_4 fcaovdir2d_6 fcaovdir2d_9 co fcaovdir2d_5 fcaovdir2d_6 fcaovdir2d_9 co fcaovdir2d_8 co fcaovdir2d_0 fcaovdir2d_1 fcaovdir2d_2 fcaovdir2d_3 fcaovdir2d_6 fcaovdir2d_4 fcaovdir2d_5 fcaovdir2d_7 fcaovdir2d_8 fcaovdir2d_9 fcaovdir2d_8 fcaovdir2d_7 ecaovdir2d_0 ecaovdir2d_3 ecaovdir2d_1 ecaovdir2d_2 caovdid fcaovdir2d_0 fcaovdir2d_1 fcaovdir2d_2 fcaovdir2d_4 fcaovdir2d_5 fcaovdir2d_8 co fcaovdir2d_6 fcaovdir2d_7 fcaovdir2d_9 ecaovdir2d_5 fcaovdir2d_0 fcaovdir2d_1 fcaovdir2d_2 fcaovdir2d_4 fcaovdir2d_5 fcaovdir2d_7 fcaovdir2d_7 fcaovdir2d_7 fcaovdir2d_8 ecaovdir2d_4 ecaovdir2d_1 ecaovdir2d_2 caovcld ecaovdir2d_3 caovcomd fcaovdir2d_0 fcaovdir2d_4 fcaovdir2d_6 fcaovdir2d_9 co fcaovdir2d_6 fcaovdir2d_4 fcaovdir2d_9 co fcaovdir2d_5 fcaovdir2d_6 fcaovdir2d_9 co fcaovdir2d_6 fcaovdir2d_5 fcaovdir2d_9 co fcaovdir2d_8 fcaovdir2d_0 fcaovdir2d_1 fcaovdir2d_2 fcaovdir2d_4 fcaovdir2d_6 fcaovdir2d_7 fcaovdir2d_9 ecaovdir2d_5 ecaovdir2d_1 ecaovdir2d_3 caovcomd fcaovdir2d_0 fcaovdir2d_1 fcaovdir2d_2 fcaovdir2d_5 fcaovdir2d_6 fcaovdir2d_7 fcaovdir2d_9 ecaovdir2d_5 ecaovdir2d_2 ecaovdir2d_3 caovcomd oveq12d 3eqtr4d $.
$}
$( /* Convert an operation reverse distributive law to class notation.
         (Contributed by Mario Carneiro, 19-Oct-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z G $.
	$d x y z H $.
	$d x y z K $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaovdirg_0 $f wff ph $.
	fcaovdirg_1 $f set x $.
	fcaovdirg_2 $f set y $.
	fcaovdirg_3 $f set z $.
	fcaovdirg_4 $f class A $.
	fcaovdirg_5 $f class B $.
	fcaovdirg_6 $f class C $.
	fcaovdirg_7 $f class S $.
	fcaovdirg_8 $f class F $.
	fcaovdirg_9 $f class G $.
	fcaovdirg_10 $f class H $.
	fcaovdirg_11 $f class K $.
	ecaovdirg_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x F y ) G z ) = ( ( x G z ) H ( y G z ) ) ) $.
	caovdirg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. K ) ) -> ( ( A F B ) G C ) = ( ( A G C ) H ( B G C ) ) ) $= fcaovdirg_0 fcaovdirg_1 sup_set_class fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_1 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co wceq fcaovdirg_3 fcaovdirg_11 wral fcaovdirg_2 fcaovdirg_7 wral fcaovdirg_1 fcaovdirg_7 wral fcaovdirg_4 fcaovdirg_7 wcel fcaovdirg_5 fcaovdirg_7 wcel fcaovdirg_6 fcaovdirg_11 wcel w3a fcaovdirg_4 fcaovdirg_5 fcaovdirg_8 co fcaovdirg_6 fcaovdirg_9 co fcaovdirg_4 fcaovdirg_6 fcaovdirg_9 co fcaovdirg_5 fcaovdirg_6 fcaovdirg_9 co fcaovdirg_10 co wceq fcaovdirg_0 fcaovdirg_1 sup_set_class fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_1 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co wceq fcaovdirg_1 fcaovdirg_2 fcaovdirg_3 fcaovdirg_7 fcaovdirg_7 fcaovdirg_11 ecaovdirg_0 ralrimivvva fcaovdirg_1 sup_set_class fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_1 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co wceq fcaovdirg_4 fcaovdirg_5 fcaovdirg_8 co fcaovdirg_6 fcaovdirg_9 co fcaovdirg_4 fcaovdirg_6 fcaovdirg_9 co fcaovdirg_5 fcaovdirg_6 fcaovdirg_9 co fcaovdirg_10 co wceq fcaovdirg_4 fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co wceq fcaovdirg_4 fcaovdirg_5 fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_5 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co wceq fcaovdirg_1 fcaovdirg_2 fcaovdirg_3 fcaovdirg_4 fcaovdirg_5 fcaovdirg_6 fcaovdirg_7 fcaovdirg_7 fcaovdirg_11 fcaovdirg_1 sup_set_class fcaovdirg_4 wceq fcaovdirg_1 sup_set_class fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_1 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co fcaovdirg_1 sup_set_class fcaovdirg_4 wceq fcaovdirg_1 sup_set_class fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_4 fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 fcaovdirg_1 sup_set_class fcaovdirg_4 fcaovdirg_2 sup_set_class fcaovdirg_8 oveq1 oveq1d fcaovdirg_1 sup_set_class fcaovdirg_4 wceq fcaovdirg_1 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 fcaovdirg_1 sup_set_class fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 oveq1 oveq1d eqeq12d fcaovdirg_2 sup_set_class fcaovdirg_5 wceq fcaovdirg_4 fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_5 fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_5 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co fcaovdirg_2 sup_set_class fcaovdirg_5 wceq fcaovdirg_4 fcaovdirg_2 sup_set_class fcaovdirg_8 co fcaovdirg_4 fcaovdirg_5 fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 fcaovdirg_2 sup_set_class fcaovdirg_5 fcaovdirg_4 fcaovdirg_8 oveq2 oveq1d fcaovdirg_2 sup_set_class fcaovdirg_5 wceq fcaovdirg_2 sup_set_class fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_5 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 fcaovdirg_2 sup_set_class fcaovdirg_5 fcaovdirg_3 sup_set_class fcaovdirg_9 oveq1 oveq2d eqeq12d fcaovdirg_3 sup_set_class fcaovdirg_6 wceq fcaovdirg_4 fcaovdirg_5 fcaovdirg_8 co fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_5 fcaovdirg_8 co fcaovdirg_6 fcaovdirg_9 co fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_5 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_10 co fcaovdirg_4 fcaovdirg_6 fcaovdirg_9 co fcaovdirg_5 fcaovdirg_6 fcaovdirg_9 co fcaovdirg_10 co fcaovdirg_3 sup_set_class fcaovdirg_6 fcaovdirg_4 fcaovdirg_5 fcaovdirg_8 co fcaovdirg_9 oveq2 fcaovdirg_3 sup_set_class fcaovdirg_6 wceq fcaovdirg_4 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_4 fcaovdirg_6 fcaovdirg_9 co fcaovdirg_5 fcaovdirg_3 sup_set_class fcaovdirg_9 co fcaovdirg_5 fcaovdirg_6 fcaovdirg_9 co fcaovdirg_10 fcaovdirg_3 sup_set_class fcaovdirg_6 fcaovdirg_4 fcaovdirg_9 oveq2 fcaovdirg_3 sup_set_class fcaovdirg_6 fcaovdirg_5 fcaovdirg_9 oveq2 oveq12d eqeq12d rspc3v mpan9 $.
$}
$( /* Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z G $.
	$d x y z H $.
	$d x y z K $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaovdird_0 $f wff ph $.
	fcaovdird_1 $f set x $.
	fcaovdird_2 $f set y $.
	fcaovdird_3 $f set z $.
	fcaovdird_4 $f class A $.
	fcaovdird_5 $f class B $.
	fcaovdird_6 $f class C $.
	fcaovdird_7 $f class S $.
	fcaovdird_8 $f class F $.
	fcaovdird_9 $f class G $.
	fcaovdird_10 $f class H $.
	fcaovdird_11 $f class K $.
	ecaovdird_0 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x F y ) G z ) = ( ( x G z ) H ( y G z ) ) ) $.
	ecaovdird_1 $e |- ( ph -> A e. S ) $.
	ecaovdird_2 $e |- ( ph -> B e. S ) $.
	ecaovdird_3 $e |- ( ph -> C e. K ) $.
	caovdird $p |- ( ph -> ( ( A F B ) G C ) = ( ( A G C ) H ( B G C ) ) ) $= fcaovdird_0 fcaovdird_0 fcaovdird_4 fcaovdird_7 wcel fcaovdird_5 fcaovdird_7 wcel fcaovdird_6 fcaovdird_11 wcel fcaovdird_4 fcaovdird_5 fcaovdird_8 co fcaovdird_6 fcaovdird_9 co fcaovdird_4 fcaovdird_6 fcaovdird_9 co fcaovdird_5 fcaovdird_6 fcaovdird_9 co fcaovdird_10 co wceq fcaovdird_0 id ecaovdird_1 ecaovdird_2 ecaovdird_3 fcaovdird_0 fcaovdird_1 fcaovdird_2 fcaovdird_3 fcaovdird_4 fcaovdird_5 fcaovdird_6 fcaovdird_7 fcaovdird_8 fcaovdird_9 fcaovdird_10 fcaovdird_11 ecaovdird_0 caovdirg syl13anc $.
$}
$( /* Convert an operation distributive law to class notation.  (Contributed
         by NM, 25-Aug-1995.)  (Revised by Mario Carneiro, 28-Jun-2013.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z G $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaovdi_0 $f set x $.
	fcaovdi_1 $f set y $.
	fcaovdi_2 $f set z $.
	fcaovdi_3 $f class A $.
	fcaovdi_4 $f class B $.
	fcaovdi_5 $f class C $.
	fcaovdi_6 $f class F $.
	fcaovdi_7 $f class G $.
	ecaovdi_0 $e |- A e. _V $.
	ecaovdi_1 $e |- B e. _V $.
	ecaovdi_2 $e |- C e. _V $.
	ecaovdi_3 $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
	caovdi $p |- ( A G ( B F C ) ) = ( ( A G B ) F ( A G C ) ) $= fcaovdi_3 cvv wcel fcaovdi_4 cvv wcel fcaovdi_5 cvv wcel fcaovdi_3 fcaovdi_4 fcaovdi_5 fcaovdi_6 co fcaovdi_7 co fcaovdi_3 fcaovdi_4 fcaovdi_7 co fcaovdi_3 fcaovdi_5 fcaovdi_7 co fcaovdi_6 co wceq ecaovdi_0 ecaovdi_1 ecaovdi_2 wtru fcaovdi_3 cvv wcel fcaovdi_4 cvv wcel fcaovdi_5 cvv wcel w3a fcaovdi_3 fcaovdi_4 fcaovdi_5 fcaovdi_6 co fcaovdi_7 co fcaovdi_3 fcaovdi_4 fcaovdi_7 co fcaovdi_3 fcaovdi_5 fcaovdi_7 co fcaovdi_6 co wceq tru wtru fcaovdi_0 fcaovdi_1 fcaovdi_2 fcaovdi_3 fcaovdi_4 fcaovdi_5 cvv fcaovdi_6 fcaovdi_7 fcaovdi_6 cvv fcaovdi_0 sup_set_class fcaovdi_1 sup_set_class fcaovdi_2 sup_set_class fcaovdi_6 co fcaovdi_7 co fcaovdi_0 sup_set_class fcaovdi_1 sup_set_class fcaovdi_7 co fcaovdi_0 sup_set_class fcaovdi_2 sup_set_class fcaovdi_7 co fcaovdi_6 co wceq wtru fcaovdi_0 sup_set_class cvv wcel fcaovdi_1 sup_set_class cvv wcel fcaovdi_2 sup_set_class cvv wcel w3a wa ecaovdi_3 a1i caovdig mpan mp3an $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaov32d_0 $f wff ph $.
	fcaov32d_1 $f set x $.
	fcaov32d_2 $f set y $.
	fcaov32d_3 $f set z $.
	fcaov32d_4 $f class A $.
	fcaov32d_5 $f class B $.
	fcaov32d_6 $f class C $.
	fcaov32d_7 $f class S $.
	fcaov32d_8 $f class F $.
	ecaov32d_0 $e |- ( ph -> A e. S ) $.
	ecaov32d_1 $e |- ( ph -> B e. S ) $.
	ecaov32d_2 $e |- ( ph -> C e. S ) $.
	ecaov32d_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaov32d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	caov32d $p |- ( ph -> ( ( A F B ) F C ) = ( ( A F C ) F B ) ) $= fcaov32d_0 fcaov32d_4 fcaov32d_5 fcaov32d_6 fcaov32d_8 co fcaov32d_8 co fcaov32d_4 fcaov32d_6 fcaov32d_5 fcaov32d_8 co fcaov32d_8 co fcaov32d_4 fcaov32d_5 fcaov32d_8 co fcaov32d_6 fcaov32d_8 co fcaov32d_4 fcaov32d_6 fcaov32d_8 co fcaov32d_5 fcaov32d_8 co fcaov32d_0 fcaov32d_5 fcaov32d_6 fcaov32d_8 co fcaov32d_6 fcaov32d_5 fcaov32d_8 co fcaov32d_4 fcaov32d_8 fcaov32d_0 fcaov32d_1 fcaov32d_2 fcaov32d_5 fcaov32d_6 fcaov32d_7 fcaov32d_8 ecaov32d_3 ecaov32d_1 ecaov32d_2 caovcomd oveq2d fcaov32d_0 fcaov32d_1 fcaov32d_2 fcaov32d_3 fcaov32d_4 fcaov32d_5 fcaov32d_6 fcaov32d_7 fcaov32d_8 ecaov32d_4 ecaov32d_0 ecaov32d_1 ecaov32d_2 caovassd fcaov32d_0 fcaov32d_1 fcaov32d_2 fcaov32d_3 fcaov32d_4 fcaov32d_6 fcaov32d_5 fcaov32d_7 fcaov32d_8 ecaov32d_4 ecaov32d_0 ecaov32d_2 ecaov32d_1 caovassd 3eqtr4d $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaov12d_0 $f wff ph $.
	fcaov12d_1 $f set x $.
	fcaov12d_2 $f set y $.
	fcaov12d_3 $f set z $.
	fcaov12d_4 $f class A $.
	fcaov12d_5 $f class B $.
	fcaov12d_6 $f class C $.
	fcaov12d_7 $f class S $.
	fcaov12d_8 $f class F $.
	ecaov12d_0 $e |- ( ph -> A e. S ) $.
	ecaov12d_1 $e |- ( ph -> B e. S ) $.
	ecaov12d_2 $e |- ( ph -> C e. S ) $.
	ecaov12d_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaov12d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	caov12d $p |- ( ph -> ( A F ( B F C ) ) = ( B F ( A F C ) ) ) $= fcaov12d_0 fcaov12d_4 fcaov12d_5 fcaov12d_8 co fcaov12d_6 fcaov12d_8 co fcaov12d_5 fcaov12d_4 fcaov12d_8 co fcaov12d_6 fcaov12d_8 co fcaov12d_4 fcaov12d_5 fcaov12d_6 fcaov12d_8 co fcaov12d_8 co fcaov12d_5 fcaov12d_4 fcaov12d_6 fcaov12d_8 co fcaov12d_8 co fcaov12d_0 fcaov12d_4 fcaov12d_5 fcaov12d_8 co fcaov12d_5 fcaov12d_4 fcaov12d_8 co fcaov12d_6 fcaov12d_8 fcaov12d_0 fcaov12d_1 fcaov12d_2 fcaov12d_4 fcaov12d_5 fcaov12d_7 fcaov12d_8 ecaov12d_3 ecaov12d_0 ecaov12d_1 caovcomd oveq1d fcaov12d_0 fcaov12d_1 fcaov12d_2 fcaov12d_3 fcaov12d_4 fcaov12d_5 fcaov12d_6 fcaov12d_7 fcaov12d_8 ecaov12d_4 ecaov12d_0 ecaov12d_1 ecaov12d_2 caovassd fcaov12d_0 fcaov12d_1 fcaov12d_2 fcaov12d_3 fcaov12d_5 fcaov12d_4 fcaov12d_6 fcaov12d_7 fcaov12d_8 ecaov12d_4 ecaov12d_1 ecaov12d_0 ecaov12d_2 caovassd 3eqtr3d $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaov31d_0 $f wff ph $.
	fcaov31d_1 $f set x $.
	fcaov31d_2 $f set y $.
	fcaov31d_3 $f set z $.
	fcaov31d_4 $f class A $.
	fcaov31d_5 $f class B $.
	fcaov31d_6 $f class C $.
	fcaov31d_7 $f class S $.
	fcaov31d_8 $f class F $.
	ecaov31d_0 $e |- ( ph -> A e. S ) $.
	ecaov31d_1 $e |- ( ph -> B e. S ) $.
	ecaov31d_2 $e |- ( ph -> C e. S ) $.
	ecaov31d_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaov31d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	caov31d $p |- ( ph -> ( ( A F B ) F C ) = ( ( C F B ) F A ) ) $= fcaov31d_0 fcaov31d_4 fcaov31d_6 fcaov31d_8 co fcaov31d_5 fcaov31d_8 co fcaov31d_6 fcaov31d_4 fcaov31d_8 co fcaov31d_5 fcaov31d_8 co fcaov31d_4 fcaov31d_5 fcaov31d_8 co fcaov31d_6 fcaov31d_8 co fcaov31d_6 fcaov31d_5 fcaov31d_8 co fcaov31d_4 fcaov31d_8 co fcaov31d_0 fcaov31d_4 fcaov31d_6 fcaov31d_8 co fcaov31d_6 fcaov31d_4 fcaov31d_8 co fcaov31d_5 fcaov31d_8 fcaov31d_0 fcaov31d_1 fcaov31d_2 fcaov31d_4 fcaov31d_6 fcaov31d_7 fcaov31d_8 ecaov31d_3 ecaov31d_0 ecaov31d_2 caovcomd oveq1d fcaov31d_0 fcaov31d_1 fcaov31d_2 fcaov31d_3 fcaov31d_4 fcaov31d_5 fcaov31d_6 fcaov31d_7 fcaov31d_8 ecaov31d_0 ecaov31d_1 ecaov31d_2 ecaov31d_3 ecaov31d_4 caov32d fcaov31d_0 fcaov31d_1 fcaov31d_2 fcaov31d_3 fcaov31d_6 fcaov31d_5 fcaov31d_4 fcaov31d_7 fcaov31d_8 ecaov31d_2 ecaov31d_1 ecaov31d_0 ecaov31d_3 ecaov31d_4 caov32d 3eqtr4d $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaov13d_0 $f wff ph $.
	fcaov13d_1 $f set x $.
	fcaov13d_2 $f set y $.
	fcaov13d_3 $f set z $.
	fcaov13d_4 $f class A $.
	fcaov13d_5 $f class B $.
	fcaov13d_6 $f class C $.
	fcaov13d_7 $f class S $.
	fcaov13d_8 $f class F $.
	ecaov13d_0 $e |- ( ph -> A e. S ) $.
	ecaov13d_1 $e |- ( ph -> B e. S ) $.
	ecaov13d_2 $e |- ( ph -> C e. S ) $.
	ecaov13d_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaov13d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	caov13d $p |- ( ph -> ( A F ( B F C ) ) = ( C F ( B F A ) ) ) $= fcaov13d_0 fcaov13d_4 fcaov13d_5 fcaov13d_8 co fcaov13d_6 fcaov13d_8 co fcaov13d_6 fcaov13d_5 fcaov13d_8 co fcaov13d_4 fcaov13d_8 co fcaov13d_4 fcaov13d_5 fcaov13d_6 fcaov13d_8 co fcaov13d_8 co fcaov13d_6 fcaov13d_5 fcaov13d_4 fcaov13d_8 co fcaov13d_8 co fcaov13d_0 fcaov13d_1 fcaov13d_2 fcaov13d_3 fcaov13d_4 fcaov13d_5 fcaov13d_6 fcaov13d_7 fcaov13d_8 ecaov13d_0 ecaov13d_1 ecaov13d_2 ecaov13d_3 ecaov13d_4 caov31d fcaov13d_0 fcaov13d_1 fcaov13d_2 fcaov13d_3 fcaov13d_4 fcaov13d_5 fcaov13d_6 fcaov13d_7 fcaov13d_8 ecaov13d_4 ecaov13d_0 ecaov13d_1 ecaov13d_2 caovassd fcaov13d_0 fcaov13d_1 fcaov13d_2 fcaov13d_3 fcaov13d_6 fcaov13d_5 fcaov13d_4 fcaov13d_7 fcaov13d_8 ecaov13d_4 ecaov13d_2 ecaov13d_1 ecaov13d_0 caovassd 3eqtr3d $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaov4d_0 $f wff ph $.
	fcaov4d_1 $f set x $.
	fcaov4d_2 $f set y $.
	fcaov4d_3 $f set z $.
	fcaov4d_4 $f class A $.
	fcaov4d_5 $f class B $.
	fcaov4d_6 $f class C $.
	fcaov4d_7 $f class D $.
	fcaov4d_8 $f class S $.
	fcaov4d_9 $f class F $.
	ecaov4d_0 $e |- ( ph -> A e. S ) $.
	ecaov4d_1 $e |- ( ph -> B e. S ) $.
	ecaov4d_2 $e |- ( ph -> C e. S ) $.
	ecaov4d_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaov4d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	ecaov4d_5 $e |- ( ph -> D e. S ) $.
	ecaov4d_6 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
	caov4d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( B F D ) ) ) $= fcaov4d_0 fcaov4d_4 fcaov4d_5 fcaov4d_6 fcaov4d_7 fcaov4d_9 co fcaov4d_9 co fcaov4d_9 co fcaov4d_4 fcaov4d_6 fcaov4d_5 fcaov4d_7 fcaov4d_9 co fcaov4d_9 co fcaov4d_9 co fcaov4d_4 fcaov4d_5 fcaov4d_9 co fcaov4d_6 fcaov4d_7 fcaov4d_9 co fcaov4d_9 co fcaov4d_4 fcaov4d_6 fcaov4d_9 co fcaov4d_5 fcaov4d_7 fcaov4d_9 co fcaov4d_9 co fcaov4d_0 fcaov4d_5 fcaov4d_6 fcaov4d_7 fcaov4d_9 co fcaov4d_9 co fcaov4d_6 fcaov4d_5 fcaov4d_7 fcaov4d_9 co fcaov4d_9 co fcaov4d_4 fcaov4d_9 fcaov4d_0 fcaov4d_1 fcaov4d_2 fcaov4d_3 fcaov4d_5 fcaov4d_6 fcaov4d_7 fcaov4d_8 fcaov4d_9 ecaov4d_1 ecaov4d_2 ecaov4d_5 ecaov4d_3 ecaov4d_4 caov12d oveq2d fcaov4d_0 fcaov4d_1 fcaov4d_2 fcaov4d_3 fcaov4d_4 fcaov4d_5 fcaov4d_6 fcaov4d_7 fcaov4d_9 co fcaov4d_8 fcaov4d_9 ecaov4d_4 ecaov4d_0 ecaov4d_1 fcaov4d_0 fcaov4d_1 fcaov4d_2 fcaov4d_6 fcaov4d_7 fcaov4d_8 fcaov4d_8 fcaov4d_8 fcaov4d_9 ecaov4d_6 ecaov4d_2 ecaov4d_5 caovcld caovassd fcaov4d_0 fcaov4d_1 fcaov4d_2 fcaov4d_3 fcaov4d_4 fcaov4d_6 fcaov4d_5 fcaov4d_7 fcaov4d_9 co fcaov4d_8 fcaov4d_9 ecaov4d_4 ecaov4d_0 ecaov4d_2 fcaov4d_0 fcaov4d_1 fcaov4d_2 fcaov4d_5 fcaov4d_7 fcaov4d_8 fcaov4d_8 fcaov4d_8 fcaov4d_9 ecaov4d_6 ecaov4d_1 ecaov4d_5 caovcld caovassd 3eqtr4d $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaov411d_0 $f wff ph $.
	fcaov411d_1 $f set x $.
	fcaov411d_2 $f set y $.
	fcaov411d_3 $f set z $.
	fcaov411d_4 $f class A $.
	fcaov411d_5 $f class B $.
	fcaov411d_6 $f class C $.
	fcaov411d_7 $f class D $.
	fcaov411d_8 $f class S $.
	fcaov411d_9 $f class F $.
	ecaov411d_0 $e |- ( ph -> A e. S ) $.
	ecaov411d_1 $e |- ( ph -> B e. S ) $.
	ecaov411d_2 $e |- ( ph -> C e. S ) $.
	ecaov411d_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaov411d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	ecaov411d_5 $e |- ( ph -> D e. S ) $.
	ecaov411d_6 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
	caov411d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) = ( ( C F B ) F ( A F D ) ) ) $= fcaov411d_0 fcaov411d_5 fcaov411d_4 fcaov411d_9 co fcaov411d_6 fcaov411d_7 fcaov411d_9 co fcaov411d_9 co fcaov411d_5 fcaov411d_6 fcaov411d_9 co fcaov411d_4 fcaov411d_7 fcaov411d_9 co fcaov411d_9 co fcaov411d_4 fcaov411d_5 fcaov411d_9 co fcaov411d_6 fcaov411d_7 fcaov411d_9 co fcaov411d_9 co fcaov411d_6 fcaov411d_5 fcaov411d_9 co fcaov411d_4 fcaov411d_7 fcaov411d_9 co fcaov411d_9 co fcaov411d_0 fcaov411d_1 fcaov411d_2 fcaov411d_3 fcaov411d_5 fcaov411d_4 fcaov411d_6 fcaov411d_7 fcaov411d_8 fcaov411d_9 ecaov411d_1 ecaov411d_0 ecaov411d_2 ecaov411d_3 ecaov411d_4 ecaov411d_5 ecaov411d_6 caov4d fcaov411d_0 fcaov411d_5 fcaov411d_4 fcaov411d_9 co fcaov411d_4 fcaov411d_5 fcaov411d_9 co fcaov411d_6 fcaov411d_7 fcaov411d_9 co fcaov411d_9 fcaov411d_0 fcaov411d_1 fcaov411d_2 fcaov411d_5 fcaov411d_4 fcaov411d_8 fcaov411d_9 ecaov411d_3 ecaov411d_1 ecaov411d_0 caovcomd oveq1d fcaov411d_0 fcaov411d_5 fcaov411d_6 fcaov411d_9 co fcaov411d_6 fcaov411d_5 fcaov411d_9 co fcaov411d_4 fcaov411d_7 fcaov411d_9 co fcaov411d_9 fcaov411d_0 fcaov411d_1 fcaov411d_2 fcaov411d_5 fcaov411d_6 fcaov411d_8 fcaov411d_9 ecaov411d_3 ecaov411d_1 ecaov411d_2 caovcomd oveq1d 3eqtr3d $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z ph $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	fcaov42d_0 $f wff ph $.
	fcaov42d_1 $f set x $.
	fcaov42d_2 $f set y $.
	fcaov42d_3 $f set z $.
	fcaov42d_4 $f class A $.
	fcaov42d_5 $f class B $.
	fcaov42d_6 $f class C $.
	fcaov42d_7 $f class D $.
	fcaov42d_8 $f class S $.
	fcaov42d_9 $f class F $.
	ecaov42d_0 $e |- ( ph -> A e. S ) $.
	ecaov42d_1 $e |- ( ph -> B e. S ) $.
	ecaov42d_2 $e |- ( ph -> C e. S ) $.
	ecaov42d_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	ecaov42d_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	ecaov42d_5 $e |- ( ph -> D e. S ) $.
	ecaov42d_6 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
	caov42d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( D F B ) ) ) $= fcaov42d_0 fcaov42d_4 fcaov42d_5 fcaov42d_9 co fcaov42d_6 fcaov42d_7 fcaov42d_9 co fcaov42d_9 co fcaov42d_4 fcaov42d_6 fcaov42d_9 co fcaov42d_5 fcaov42d_7 fcaov42d_9 co fcaov42d_9 co fcaov42d_4 fcaov42d_6 fcaov42d_9 co fcaov42d_7 fcaov42d_5 fcaov42d_9 co fcaov42d_9 co fcaov42d_0 fcaov42d_1 fcaov42d_2 fcaov42d_3 fcaov42d_4 fcaov42d_5 fcaov42d_6 fcaov42d_7 fcaov42d_8 fcaov42d_9 ecaov42d_0 ecaov42d_1 ecaov42d_2 ecaov42d_3 ecaov42d_4 ecaov42d_5 ecaov42d_6 caov4d fcaov42d_0 fcaov42d_5 fcaov42d_7 fcaov42d_9 co fcaov42d_7 fcaov42d_5 fcaov42d_9 co fcaov42d_4 fcaov42d_6 fcaov42d_9 co fcaov42d_9 fcaov42d_0 fcaov42d_1 fcaov42d_2 fcaov42d_5 fcaov42d_7 fcaov42d_8 fcaov42d_9 ecaov42d_3 ecaov42d_1 ecaov42d_5 caovcomd oveq2d eqtrd $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaov32_0 $f set x $.
	fcaov32_1 $f set y $.
	fcaov32_2 $f set z $.
	fcaov32_3 $f class A $.
	fcaov32_4 $f class B $.
	fcaov32_5 $f class C $.
	fcaov32_6 $f class F $.
	ecaov32_0 $e |- A e. _V $.
	ecaov32_1 $e |- B e. _V $.
	ecaov32_2 $e |- C e. _V $.
	ecaov32_3 $e |- ( x F y ) = ( y F x ) $.
	ecaov32_4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	caov32 $p |- ( ( A F B ) F C ) = ( ( A F C ) F B ) $= fcaov32_3 fcaov32_4 fcaov32_5 fcaov32_6 co fcaov32_6 co fcaov32_3 fcaov32_5 fcaov32_4 fcaov32_6 co fcaov32_6 co fcaov32_3 fcaov32_4 fcaov32_6 co fcaov32_5 fcaov32_6 co fcaov32_3 fcaov32_5 fcaov32_6 co fcaov32_4 fcaov32_6 co fcaov32_4 fcaov32_5 fcaov32_6 co fcaov32_5 fcaov32_4 fcaov32_6 co fcaov32_3 fcaov32_6 fcaov32_0 fcaov32_1 fcaov32_4 fcaov32_5 fcaov32_6 ecaov32_1 ecaov32_2 ecaov32_3 caovcom oveq2i fcaov32_0 fcaov32_1 fcaov32_2 fcaov32_3 fcaov32_4 fcaov32_5 fcaov32_6 ecaov32_0 ecaov32_1 ecaov32_2 ecaov32_4 caovass fcaov32_0 fcaov32_1 fcaov32_2 fcaov32_3 fcaov32_5 fcaov32_4 fcaov32_6 ecaov32_0 ecaov32_2 ecaov32_1 ecaov32_4 caovass 3eqtr4i $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaov12_0 $f set x $.
	fcaov12_1 $f set y $.
	fcaov12_2 $f set z $.
	fcaov12_3 $f class A $.
	fcaov12_4 $f class B $.
	fcaov12_5 $f class C $.
	fcaov12_6 $f class F $.
	ecaov12_0 $e |- A e. _V $.
	ecaov12_1 $e |- B e. _V $.
	ecaov12_2 $e |- C e. _V $.
	ecaov12_3 $e |- ( x F y ) = ( y F x ) $.
	ecaov12_4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	caov12 $p |- ( A F ( B F C ) ) = ( B F ( A F C ) ) $= fcaov12_3 fcaov12_4 fcaov12_6 co fcaov12_5 fcaov12_6 co fcaov12_4 fcaov12_3 fcaov12_6 co fcaov12_5 fcaov12_6 co fcaov12_3 fcaov12_4 fcaov12_5 fcaov12_6 co fcaov12_6 co fcaov12_4 fcaov12_3 fcaov12_5 fcaov12_6 co fcaov12_6 co fcaov12_3 fcaov12_4 fcaov12_6 co fcaov12_4 fcaov12_3 fcaov12_6 co fcaov12_5 fcaov12_6 fcaov12_0 fcaov12_1 fcaov12_3 fcaov12_4 fcaov12_6 ecaov12_0 ecaov12_1 ecaov12_3 caovcom oveq1i fcaov12_0 fcaov12_1 fcaov12_2 fcaov12_3 fcaov12_4 fcaov12_5 fcaov12_6 ecaov12_0 ecaov12_1 ecaov12_2 ecaov12_4 caovass fcaov12_0 fcaov12_1 fcaov12_2 fcaov12_4 fcaov12_3 fcaov12_5 fcaov12_6 ecaov12_1 ecaov12_0 ecaov12_2 ecaov12_4 caovass 3eqtr3i $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaov31_0 $f set x $.
	fcaov31_1 $f set y $.
	fcaov31_2 $f set z $.
	fcaov31_3 $f class A $.
	fcaov31_4 $f class B $.
	fcaov31_5 $f class C $.
	fcaov31_6 $f class F $.
	ecaov31_0 $e |- A e. _V $.
	ecaov31_1 $e |- B e. _V $.
	ecaov31_2 $e |- C e. _V $.
	ecaov31_3 $e |- ( x F y ) = ( y F x ) $.
	ecaov31_4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	caov31 $p |- ( ( A F B ) F C ) = ( ( C F B ) F A ) $= fcaov31_3 fcaov31_5 fcaov31_6 co fcaov31_4 fcaov31_6 co fcaov31_5 fcaov31_3 fcaov31_4 fcaov31_6 co fcaov31_6 co fcaov31_3 fcaov31_4 fcaov31_6 co fcaov31_5 fcaov31_6 co fcaov31_5 fcaov31_4 fcaov31_6 co fcaov31_3 fcaov31_6 co fcaov31_3 fcaov31_5 fcaov31_6 co fcaov31_4 fcaov31_6 co fcaov31_3 fcaov31_5 fcaov31_4 fcaov31_6 co fcaov31_6 co fcaov31_5 fcaov31_3 fcaov31_4 fcaov31_6 co fcaov31_6 co fcaov31_0 fcaov31_1 fcaov31_2 fcaov31_3 fcaov31_5 fcaov31_4 fcaov31_6 ecaov31_0 ecaov31_2 ecaov31_1 ecaov31_4 caovass fcaov31_0 fcaov31_1 fcaov31_2 fcaov31_3 fcaov31_5 fcaov31_4 fcaov31_6 ecaov31_0 ecaov31_2 ecaov31_1 ecaov31_3 ecaov31_4 caov12 eqtri fcaov31_0 fcaov31_1 fcaov31_2 fcaov31_3 fcaov31_4 fcaov31_5 fcaov31_6 ecaov31_0 ecaov31_1 ecaov31_2 ecaov31_3 ecaov31_4 caov32 fcaov31_5 fcaov31_3 fcaov31_6 co fcaov31_4 fcaov31_6 co fcaov31_5 fcaov31_4 fcaov31_6 co fcaov31_3 fcaov31_6 co fcaov31_5 fcaov31_3 fcaov31_4 fcaov31_6 co fcaov31_6 co fcaov31_0 fcaov31_1 fcaov31_2 fcaov31_5 fcaov31_3 fcaov31_4 fcaov31_6 ecaov31_2 ecaov31_0 ecaov31_1 ecaov31_3 ecaov31_4 caov32 fcaov31_0 fcaov31_1 fcaov31_2 fcaov31_5 fcaov31_3 fcaov31_4 fcaov31_6 ecaov31_2 ecaov31_0 ecaov31_1 ecaov31_4 caovass eqtr3i 3eqtr4i $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaov13_0 $f set x $.
	fcaov13_1 $f set y $.
	fcaov13_2 $f set z $.
	fcaov13_3 $f class A $.
	fcaov13_4 $f class B $.
	fcaov13_5 $f class C $.
	fcaov13_6 $f class F $.
	ecaov13_0 $e |- A e. _V $.
	ecaov13_1 $e |- B e. _V $.
	ecaov13_2 $e |- C e. _V $.
	ecaov13_3 $e |- ( x F y ) = ( y F x ) $.
	ecaov13_4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	caov13 $p |- ( A F ( B F C ) ) = ( C F ( B F A ) ) $= fcaov13_3 fcaov13_4 fcaov13_6 co fcaov13_5 fcaov13_6 co fcaov13_5 fcaov13_4 fcaov13_6 co fcaov13_3 fcaov13_6 co fcaov13_3 fcaov13_4 fcaov13_5 fcaov13_6 co fcaov13_6 co fcaov13_5 fcaov13_4 fcaov13_3 fcaov13_6 co fcaov13_6 co fcaov13_0 fcaov13_1 fcaov13_2 fcaov13_3 fcaov13_4 fcaov13_5 fcaov13_6 ecaov13_0 ecaov13_1 ecaov13_2 ecaov13_3 ecaov13_4 caov31 fcaov13_0 fcaov13_1 fcaov13_2 fcaov13_3 fcaov13_4 fcaov13_5 fcaov13_6 ecaov13_0 ecaov13_1 ecaov13_2 ecaov13_4 caovass fcaov13_0 fcaov13_1 fcaov13_2 fcaov13_5 fcaov13_4 fcaov13_3 fcaov13_6 ecaov13_2 ecaov13_1 ecaov13_0 ecaov13_4 caovass 3eqtr3i $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaov4_0 $f set x $.
	fcaov4_1 $f set y $.
	fcaov4_2 $f set z $.
	fcaov4_3 $f class A $.
	fcaov4_4 $f class B $.
	fcaov4_5 $f class C $.
	fcaov4_6 $f class D $.
	fcaov4_7 $f class F $.
	ecaov4_0 $e |- A e. _V $.
	ecaov4_1 $e |- B e. _V $.
	ecaov4_2 $e |- C e. _V $.
	ecaov4_3 $e |- ( x F y ) = ( y F x ) $.
	ecaov4_4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	ecaov4_5 $e |- D e. _V $.
	caov4 $p |- ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( B F D ) ) $= fcaov4_3 fcaov4_4 fcaov4_5 fcaov4_6 fcaov4_7 co fcaov4_7 co fcaov4_7 co fcaov4_3 fcaov4_5 fcaov4_4 fcaov4_6 fcaov4_7 co fcaov4_7 co fcaov4_7 co fcaov4_3 fcaov4_4 fcaov4_7 co fcaov4_5 fcaov4_6 fcaov4_7 co fcaov4_7 co fcaov4_3 fcaov4_5 fcaov4_7 co fcaov4_4 fcaov4_6 fcaov4_7 co fcaov4_7 co fcaov4_4 fcaov4_5 fcaov4_6 fcaov4_7 co fcaov4_7 co fcaov4_5 fcaov4_4 fcaov4_6 fcaov4_7 co fcaov4_7 co fcaov4_3 fcaov4_7 fcaov4_0 fcaov4_1 fcaov4_2 fcaov4_4 fcaov4_5 fcaov4_6 fcaov4_7 ecaov4_1 ecaov4_2 ecaov4_5 ecaov4_3 ecaov4_4 caov12 oveq2i fcaov4_0 fcaov4_1 fcaov4_2 fcaov4_3 fcaov4_4 fcaov4_5 fcaov4_6 fcaov4_7 co fcaov4_7 ecaov4_0 ecaov4_1 fcaov4_5 fcaov4_6 fcaov4_7 ovex ecaov4_4 caovass fcaov4_0 fcaov4_1 fcaov4_2 fcaov4_3 fcaov4_5 fcaov4_4 fcaov4_6 fcaov4_7 co fcaov4_7 ecaov4_0 ecaov4_2 fcaov4_4 fcaov4_6 fcaov4_7 ovex ecaov4_4 caovass 3eqtr4i $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaov411_0 $f set x $.
	fcaov411_1 $f set y $.
	fcaov411_2 $f set z $.
	fcaov411_3 $f class A $.
	fcaov411_4 $f class B $.
	fcaov411_5 $f class C $.
	fcaov411_6 $f class D $.
	fcaov411_7 $f class F $.
	ecaov411_0 $e |- A e. _V $.
	ecaov411_1 $e |- B e. _V $.
	ecaov411_2 $e |- C e. _V $.
	ecaov411_3 $e |- ( x F y ) = ( y F x ) $.
	ecaov411_4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	ecaov411_5 $e |- D e. _V $.
	caov411 $p |- ( ( A F B ) F ( C F D ) ) = ( ( C F B ) F ( A F D ) ) $= fcaov411_3 fcaov411_4 fcaov411_7 co fcaov411_5 fcaov411_7 co fcaov411_6 fcaov411_7 co fcaov411_5 fcaov411_4 fcaov411_7 co fcaov411_3 fcaov411_7 co fcaov411_6 fcaov411_7 co fcaov411_3 fcaov411_4 fcaov411_7 co fcaov411_5 fcaov411_6 fcaov411_7 co fcaov411_7 co fcaov411_5 fcaov411_4 fcaov411_7 co fcaov411_3 fcaov411_6 fcaov411_7 co fcaov411_7 co fcaov411_3 fcaov411_4 fcaov411_7 co fcaov411_5 fcaov411_7 co fcaov411_5 fcaov411_4 fcaov411_7 co fcaov411_3 fcaov411_7 co fcaov411_6 fcaov411_7 fcaov411_0 fcaov411_1 fcaov411_2 fcaov411_3 fcaov411_4 fcaov411_5 fcaov411_7 ecaov411_0 ecaov411_1 ecaov411_2 ecaov411_3 ecaov411_4 caov31 oveq1i fcaov411_0 fcaov411_1 fcaov411_2 fcaov411_3 fcaov411_4 fcaov411_7 co fcaov411_5 fcaov411_6 fcaov411_7 fcaov411_3 fcaov411_4 fcaov411_7 ovex ecaov411_2 ecaov411_5 ecaov411_4 caovass fcaov411_0 fcaov411_1 fcaov411_2 fcaov411_5 fcaov411_4 fcaov411_7 co fcaov411_3 fcaov411_6 fcaov411_7 fcaov411_5 fcaov411_4 fcaov411_7 ovex ecaov411_0 ecaov411_5 ecaov411_4 caovass 3eqtr3i $.
$}
$( /* Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaov42_0 $f set x $.
	fcaov42_1 $f set y $.
	fcaov42_2 $f set z $.
	fcaov42_3 $f class A $.
	fcaov42_4 $f class B $.
	fcaov42_5 $f class C $.
	fcaov42_6 $f class D $.
	fcaov42_7 $f class F $.
	ecaov42_0 $e |- A e. _V $.
	ecaov42_1 $e |- B e. _V $.
	ecaov42_2 $e |- C e. _V $.
	ecaov42_3 $e |- ( x F y ) = ( y F x ) $.
	ecaov42_4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	ecaov42_5 $e |- D e. _V $.
	caov42 $p |- ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( D F B ) ) $= fcaov42_3 fcaov42_4 fcaov42_7 co fcaov42_5 fcaov42_6 fcaov42_7 co fcaov42_7 co fcaov42_3 fcaov42_5 fcaov42_7 co fcaov42_4 fcaov42_6 fcaov42_7 co fcaov42_7 co fcaov42_3 fcaov42_5 fcaov42_7 co fcaov42_6 fcaov42_4 fcaov42_7 co fcaov42_7 co fcaov42_0 fcaov42_1 fcaov42_2 fcaov42_3 fcaov42_4 fcaov42_5 fcaov42_6 fcaov42_7 ecaov42_0 ecaov42_1 ecaov42_2 ecaov42_3 ecaov42_4 ecaov42_5 caov4 fcaov42_4 fcaov42_6 fcaov42_7 co fcaov42_6 fcaov42_4 fcaov42_7 co fcaov42_3 fcaov42_5 fcaov42_7 co fcaov42_7 fcaov42_0 fcaov42_1 fcaov42_4 fcaov42_6 fcaov42_7 ecaov42_1 ecaov42_5 ecaov42_3 caovcom oveq2i eqtri $.
$}
$( /* Reverse distributive law.  (Contributed by NM, 26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z G $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	fcaovdir_0 $f set x $.
	fcaovdir_1 $f set y $.
	fcaovdir_2 $f set z $.
	fcaovdir_3 $f class A $.
	fcaovdir_4 $f class B $.
	fcaovdir_5 $f class C $.
	fcaovdir_6 $f class F $.
	fcaovdir_7 $f class G $.
	ecaovdir_0 $e |- A e. _V $.
	ecaovdir_1 $e |- B e. _V $.
	ecaovdir_2 $e |- C e. _V $.
	ecaovdir_3 $e |- ( x G y ) = ( y G x ) $.
	ecaovdir_4 $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
	caovdir $p |- ( ( A F B ) G C ) = ( ( A G C ) F ( B G C ) ) $= fcaovdir_5 fcaovdir_3 fcaovdir_4 fcaovdir_6 co fcaovdir_7 co fcaovdir_5 fcaovdir_3 fcaovdir_7 co fcaovdir_5 fcaovdir_4 fcaovdir_7 co fcaovdir_6 co fcaovdir_3 fcaovdir_4 fcaovdir_6 co fcaovdir_5 fcaovdir_7 co fcaovdir_3 fcaovdir_5 fcaovdir_7 co fcaovdir_4 fcaovdir_5 fcaovdir_7 co fcaovdir_6 co fcaovdir_0 fcaovdir_1 fcaovdir_2 fcaovdir_5 fcaovdir_3 fcaovdir_4 fcaovdir_6 fcaovdir_7 ecaovdir_2 ecaovdir_0 ecaovdir_1 ecaovdir_4 caovdi fcaovdir_0 fcaovdir_1 fcaovdir_5 fcaovdir_3 fcaovdir_4 fcaovdir_6 co fcaovdir_7 ecaovdir_2 fcaovdir_3 fcaovdir_4 fcaovdir_6 ovex ecaovdir_3 caovcom fcaovdir_5 fcaovdir_3 fcaovdir_7 co fcaovdir_3 fcaovdir_5 fcaovdir_7 co fcaovdir_5 fcaovdir_4 fcaovdir_7 co fcaovdir_4 fcaovdir_5 fcaovdir_7 co fcaovdir_6 fcaovdir_0 fcaovdir_1 fcaovdir_5 fcaovdir_3 fcaovdir_7 ecaovdir_2 ecaovdir_0 ecaovdir_3 caovcom fcaovdir_0 fcaovdir_1 fcaovdir_5 fcaovdir_4 fcaovdir_7 ecaovdir_2 ecaovdir_1 ecaovdir_3 caovcom oveq12i 3eqtr3i $.
$}
$( /* Lemma used by real number construction.  (Contributed by NM,
         26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z $.
	$d x y z F $.
	$d x y z G $.
	$d x y z H $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z H $.
	$d x y z $.
	fcaovdilem_0 $f set x $.
	fcaovdilem_1 $f set y $.
	fcaovdilem_2 $f set z $.
	fcaovdilem_3 $f class A $.
	fcaovdilem_4 $f class B $.
	fcaovdilem_5 $f class C $.
	fcaovdilem_6 $f class D $.
	fcaovdilem_7 $f class F $.
	fcaovdilem_8 $f class G $.
	fcaovdilem_9 $f class H $.
	ecaovdilem_0 $e |- A e. _V $.
	ecaovdilem_1 $e |- B e. _V $.
	ecaovdilem_2 $e |- C e. _V $.
	ecaovdilem_3 $e |- ( x G y ) = ( y G x ) $.
	ecaovdilem_4 $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
	ecaovdilem_5 $e |- D e. _V $.
	ecaovdilem_6 $e |- H e. _V $.
	ecaovdilem_7 $e |- ( ( x G y ) G z ) = ( x G ( y G z ) ) $.
	caovdilem $p |- ( ( ( A G C ) F ( B G D ) ) G H ) = ( ( A G ( C G H ) ) F ( B G ( D G H ) ) ) $= fcaovdilem_3 fcaovdilem_5 fcaovdilem_8 co fcaovdilem_4 fcaovdilem_6 fcaovdilem_8 co fcaovdilem_7 co fcaovdilem_9 fcaovdilem_8 co fcaovdilem_3 fcaovdilem_5 fcaovdilem_8 co fcaovdilem_9 fcaovdilem_8 co fcaovdilem_4 fcaovdilem_6 fcaovdilem_8 co fcaovdilem_9 fcaovdilem_8 co fcaovdilem_7 co fcaovdilem_3 fcaovdilem_5 fcaovdilem_9 fcaovdilem_8 co fcaovdilem_8 co fcaovdilem_4 fcaovdilem_6 fcaovdilem_9 fcaovdilem_8 co fcaovdilem_8 co fcaovdilem_7 co fcaovdilem_0 fcaovdilem_1 fcaovdilem_2 fcaovdilem_3 fcaovdilem_5 fcaovdilem_8 co fcaovdilem_4 fcaovdilem_6 fcaovdilem_8 co fcaovdilem_9 fcaovdilem_7 fcaovdilem_8 fcaovdilem_3 fcaovdilem_5 fcaovdilem_8 ovex fcaovdilem_4 fcaovdilem_6 fcaovdilem_8 ovex ecaovdilem_6 ecaovdilem_3 ecaovdilem_4 caovdir fcaovdilem_3 fcaovdilem_5 fcaovdilem_8 co fcaovdilem_9 fcaovdilem_8 co fcaovdilem_3 fcaovdilem_5 fcaovdilem_9 fcaovdilem_8 co fcaovdilem_8 co fcaovdilem_4 fcaovdilem_6 fcaovdilem_8 co fcaovdilem_9 fcaovdilem_8 co fcaovdilem_4 fcaovdilem_6 fcaovdilem_9 fcaovdilem_8 co fcaovdilem_8 co fcaovdilem_7 fcaovdilem_0 fcaovdilem_1 fcaovdilem_2 fcaovdilem_3 fcaovdilem_5 fcaovdilem_9 fcaovdilem_8 ecaovdilem_0 ecaovdilem_2 ecaovdilem_6 ecaovdilem_7 caovass fcaovdilem_0 fcaovdilem_1 fcaovdilem_2 fcaovdilem_4 fcaovdilem_6 fcaovdilem_9 fcaovdilem_8 ecaovdilem_1 ecaovdilem_5 ecaovdilem_6 ecaovdilem_7 caovass oveq12i eqtri $.
$}
$( /* Lemma used in real number construction.  (Contributed by NM,
         26-Aug-1995.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	$d x y z $.
	$d x y z F $.
	$d x y z G $.
	$d x y z H $.
	$d x y z $.
	$d x y z R $.
	$d x y z $.
	$d x y z $.
	$d x y z H $.
	$d x y z R $.
	fcaovlem2_0 $f set x $.
	fcaovlem2_1 $f set y $.
	fcaovlem2_2 $f set z $.
	fcaovlem2_3 $f class A $.
	fcaovlem2_4 $f class B $.
	fcaovlem2_5 $f class C $.
	fcaovlem2_6 $f class D $.
	fcaovlem2_7 $f class R $.
	fcaovlem2_8 $f class F $.
	fcaovlem2_9 $f class G $.
	fcaovlem2_10 $f class H $.
	ecaovlem2_0 $e |- A e. _V $.
	ecaovlem2_1 $e |- B e. _V $.
	ecaovlem2_2 $e |- C e. _V $.
	ecaovlem2_3 $e |- ( x G y ) = ( y G x ) $.
	ecaovlem2_4 $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
	ecaovlem2_5 $e |- D e. _V $.
	ecaovlem2_6 $e |- H e. _V $.
	ecaovlem2_7 $e |- ( ( x G y ) G z ) = ( x G ( y G z ) ) $.
	ecaovlem2_8 $e |- R e. _V $.
	ecaovlem2_9 $e |- ( x F y ) = ( y F x ) $.
	ecaovlem2_10 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	caovlem2 $p |- ( ( ( ( A G C ) F ( B G D ) ) G H ) F ( ( ( A G D ) F ( B G C ) ) G R ) ) = ( ( A G ( ( C G H ) F ( D G R ) ) ) F ( B G ( ( C G R ) F ( D G H ) ) ) ) $= fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_3 fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_8 co fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_3 fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_8 co fcaovlem2_3 fcaovlem2_5 fcaovlem2_9 co fcaovlem2_4 fcaovlem2_6 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_10 fcaovlem2_9 co fcaovlem2_3 fcaovlem2_6 fcaovlem2_9 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_7 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_0 fcaovlem2_1 fcaovlem2_2 fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_3 fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 ovex fcaovlem2_4 fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 ovex fcaovlem2_3 fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 ovex ecaovlem2_9 ecaovlem2_10 fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 ovex caov42 fcaovlem2_3 fcaovlem2_5 fcaovlem2_9 co fcaovlem2_4 fcaovlem2_6 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_10 fcaovlem2_9 co fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_3 fcaovlem2_6 fcaovlem2_9 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_7 fcaovlem2_9 co fcaovlem2_3 fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_8 fcaovlem2_0 fcaovlem2_1 fcaovlem2_2 fcaovlem2_3 fcaovlem2_4 fcaovlem2_5 fcaovlem2_6 fcaovlem2_8 fcaovlem2_9 fcaovlem2_10 ecaovlem2_0 ecaovlem2_1 ecaovlem2_2 ecaovlem2_3 ecaovlem2_4 ecaovlem2_5 ecaovlem2_6 ecaovlem2_7 caovdilem fcaovlem2_0 fcaovlem2_1 fcaovlem2_2 fcaovlem2_3 fcaovlem2_4 fcaovlem2_6 fcaovlem2_5 fcaovlem2_8 fcaovlem2_9 fcaovlem2_7 ecaovlem2_0 ecaovlem2_1 ecaovlem2_5 ecaovlem2_3 ecaovlem2_4 ecaovlem2_2 ecaovlem2_8 ecaovlem2_7 caovdilem oveq12i fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_9 co fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_3 fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_4 fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_9 co fcaovlem2_8 co fcaovlem2_8 fcaovlem2_0 fcaovlem2_1 fcaovlem2_2 fcaovlem2_3 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_8 fcaovlem2_9 ecaovlem2_0 fcaovlem2_5 fcaovlem2_10 fcaovlem2_9 ovex fcaovlem2_6 fcaovlem2_7 fcaovlem2_9 ovex ecaovlem2_4 caovdi fcaovlem2_0 fcaovlem2_1 fcaovlem2_2 fcaovlem2_4 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 co fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 co fcaovlem2_8 fcaovlem2_9 ecaovlem2_1 fcaovlem2_5 fcaovlem2_7 fcaovlem2_9 ovex fcaovlem2_6 fcaovlem2_10 fcaovlem2_9 ovex ecaovlem2_4 caovdi oveq12i 3eqtr4i $.
$}
$( /* Identity element. */

$)
$( /* Uniqueness of inverse element in commutative, associative operation
         with identity.  Remark in proof of Proposition 9-2.4 of [Gleason]
         p. 119.  (Contributed by NM, 4-Mar-1996.) */

$)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z F $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	$d x y z S $.
	$d x y z $.
	$d u w A $.
	$d u v w x y B $.
	$d u v w x y z F $.
	$d w x S $.
	icaovmo_0 $f set v $.
	icaovmo_1 $f set u $.
	fcaovmo_0 $f set x $.
	fcaovmo_1 $f set y $.
	fcaovmo_2 $f set z $.
	fcaovmo_3 $f set w $.
	fcaovmo_4 $f class A $.
	fcaovmo_5 $f class B $.
	fcaovmo_6 $f class S $.
	fcaovmo_7 $f class F $.
	ecaovmo_0 $e |- B e. S $.
	ecaovmo_1 $e |- dom F = ( S X. S ) $.
	ecaovmo_2 $e |- -. (/) e. S $.
	ecaovmo_3 $e |- ( x F y ) = ( y F x ) $.
	ecaovmo_4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	ecaovmo_5 $e |- ( x e. S -> ( x F B ) = x ) $.
	caovmo $p |- E* w ( A F w ) = B $= fcaovmo_4 fcaovmo_6 wcel fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa fcaovmo_3 wmo fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_3 wmo fcaovmo_4 fcaovmo_6 wcel fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa fcaovmo_3 wmo fcaovmo_4 fcaovmo_6 wcel fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_3 wmo wi icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_3 wmo fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_3 wmo icaovmo_1 fcaovmo_4 fcaovmo_6 icaovmo_1 sup_set_class fcaovmo_4 wceq icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_3 icaovmo_1 sup_set_class fcaovmo_4 wceq icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 icaovmo_1 sup_set_class fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 oveq1 eqeq1d mobidv icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_3 wmo icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa fcaovmo_3 sup_set_class icaovmo_0 sup_set_class wceq wi icaovmo_0 wal fcaovmo_3 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_3 icaovmo_0 fcaovmo_3 sup_set_class icaovmo_0 sup_set_class wceq icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 fcaovmo_3 sup_set_class icaovmo_0 sup_set_class icaovmo_1 sup_set_class fcaovmo_7 oveq2 eqeq1d mo4 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa fcaovmo_3 sup_set_class icaovmo_0 sup_set_class wceq wi icaovmo_0 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa fcaovmo_3 sup_set_class fcaovmo_5 fcaovmo_7 co icaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co fcaovmo_3 sup_set_class icaovmo_0 sup_set_class icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa fcaovmo_3 sup_set_class icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_7 co fcaovmo_3 sup_set_class fcaovmo_5 fcaovmo_7 co icaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 fcaovmo_3 sup_set_class fcaovmo_7 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq simpr oveq2d icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_3 sup_set_class icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_7 co icaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 icaovmo_0 sup_set_class fcaovmo_7 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq simpl oveq1d icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co icaovmo_0 sup_set_class fcaovmo_7 co icaovmo_1 sup_set_class fcaovmo_3 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_7 co fcaovmo_3 sup_set_class icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_7 co fcaovmo_0 fcaovmo_1 fcaovmo_2 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 icaovmo_1 vex fcaovmo_3 vex icaovmo_0 vex ecaovmo_4 caovass fcaovmo_0 fcaovmo_1 fcaovmo_2 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 icaovmo_1 vex fcaovmo_3 vex icaovmo_0 vex ecaovmo_3 ecaovmo_4 caov12 eqtri fcaovmo_0 fcaovmo_1 fcaovmo_5 icaovmo_0 sup_set_class fcaovmo_7 fcaovmo_5 fcaovmo_6 ecaovmo_0 elexi icaovmo_0 vex ecaovmo_3 caovcom 3eqtr3g eqtr3d icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa fcaovmo_3 sup_set_class fcaovmo_6 wcel fcaovmo_3 sup_set_class fcaovmo_5 fcaovmo_7 co fcaovmo_3 sup_set_class wceq icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class fcaovmo_6 wcel fcaovmo_3 sup_set_class fcaovmo_6 wcel icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_6 wcel icaovmo_1 sup_set_class fcaovmo_6 wcel fcaovmo_3 sup_set_class fcaovmo_6 wcel wa icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 fcaovmo_6 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq simpl ecaovmo_0 syl6eqel icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_6 fcaovmo_7 ecaovmo_1 ecaovmo_2 ndmovrcl syl simprd fcaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co fcaovmo_0 sup_set_class wceq fcaovmo_3 sup_set_class fcaovmo_5 fcaovmo_7 co fcaovmo_3 sup_set_class wceq fcaovmo_0 fcaovmo_3 sup_set_class fcaovmo_6 fcaovmo_0 sup_set_class fcaovmo_3 sup_set_class wceq fcaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co fcaovmo_3 sup_set_class fcaovmo_5 fcaovmo_7 co fcaovmo_0 sup_set_class fcaovmo_3 sup_set_class fcaovmo_0 sup_set_class fcaovmo_3 sup_set_class fcaovmo_5 fcaovmo_7 oveq1 fcaovmo_0 sup_set_class fcaovmo_3 sup_set_class wceq id eqeq12d ecaovmo_5 vtoclga syl icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_0 sup_set_class fcaovmo_6 wcel icaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co icaovmo_0 sup_set_class wceq icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class fcaovmo_6 wcel icaovmo_0 sup_set_class fcaovmo_6 wcel icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_6 wcel icaovmo_1 sup_set_class fcaovmo_6 wcel icaovmo_0 sup_set_class fcaovmo_6 wcel wa icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 fcaovmo_6 icaovmo_1 sup_set_class fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_7 co fcaovmo_5 wceq simpr ecaovmo_0 syl6eqel icaovmo_1 sup_set_class icaovmo_0 sup_set_class fcaovmo_6 fcaovmo_7 ecaovmo_1 ecaovmo_2 ndmovrcl syl simprd fcaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co fcaovmo_0 sup_set_class wceq icaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co icaovmo_0 sup_set_class wceq fcaovmo_0 icaovmo_0 sup_set_class fcaovmo_6 fcaovmo_0 sup_set_class icaovmo_0 sup_set_class wceq fcaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co icaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 co fcaovmo_0 sup_set_class icaovmo_0 sup_set_class fcaovmo_0 sup_set_class icaovmo_0 sup_set_class fcaovmo_5 fcaovmo_7 oveq1 fcaovmo_0 sup_set_class icaovmo_0 sup_set_class wceq id eqeq12d ecaovmo_5 vtoclga syl 3eqtr3d ax-gen mpgbir vtoclg fcaovmo_4 fcaovmo_6 wcel fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_3 moanimv mpbir fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_4 fcaovmo_6 wcel fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq wa fcaovmo_3 fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_4 fcaovmo_6 wcel fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_4 fcaovmo_6 wcel fcaovmo_3 sup_set_class fcaovmo_6 wcel fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_6 wcel fcaovmo_4 fcaovmo_6 wcel fcaovmo_3 sup_set_class fcaovmo_6 wcel wa fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 wceq fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_6 wcel fcaovmo_5 fcaovmo_6 wcel ecaovmo_0 fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_7 co fcaovmo_5 fcaovmo_6 eleq1 mpbiri fcaovmo_4 fcaovmo_3 sup_set_class fcaovmo_6 fcaovmo_7 ecaovmo_1 ecaovmo_2 ndmovrcl syl simpld ancri moimi ax-mp $.
$}
$( /* Lemma for ~ grprinvd .  (Contributed by NM, 9-Aug-2013.) */

$)
$v .+ $.
$v O $.
${
	$d u v w x y z B $.
	$d u v w x y z O $.
	$d u v w x y z ph $.
	$d u v w y z $.
	$d u v w x y z .+ $.
	$d u v w y z X $.
	$d u v w y ps $.
	igrprinvlem_0 $f set w $.
	igrprinvlem_1 $f set v $.
	igrprinvlem_2 $f set u $.
	fgrprinvlem_0 $f wff ph $.
	fgrprinvlem_1 $f wff ps $.
	fgrprinvlem_2 $f set x $.
	fgrprinvlem_3 $f set y $.
	fgrprinvlem_4 $f set z $.
	fgrprinvlem_5 $f class B $.
	fgrprinvlem_6 $f class .+ $.
	fgrprinvlem_7 $f class O $.
	fgrprinvlem_8 $f class X $.
	egrprinvlem_0 $e |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B ) $.
	egrprinvlem_1 $e |- ( ph -> O e. B ) $.
	egrprinvlem_2 $e |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x ) $.
	egrprinvlem_3 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) ) $.
	egrprinvlem_4 $e |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O ) $.
	egrprinvlem_5 $e |- ( ( ph /\ ps ) -> X e. B ) $.
	egrprinvlem_6 $e |- ( ( ph /\ ps ) -> ( X .+ X ) = X ) $.
	grprinvlem $p |- ( ( ph /\ ps ) -> X = O ) $= fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_8 fgrprinvlem_7 wceq fgrprinvlem_0 fgrprinvlem_1 fgrprinvlem_8 fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex egrprinvlem_5 fgrprinvlem_0 fgrprinvlem_3 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_4 fgrprinvlem_5 wral fgrprinvlem_8 fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_0 fgrprinvlem_3 sup_set_class fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_2 fgrprinvlem_5 wral fgrprinvlem_3 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_4 fgrprinvlem_5 wral fgrprinvlem_0 fgrprinvlem_3 sup_set_class fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_2 fgrprinvlem_5 egrprinvlem_4 ralrimiva fgrprinvlem_3 sup_set_class fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_3 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_2 fgrprinvlem_4 fgrprinvlem_5 fgrprinvlem_2 sup_set_class fgrprinvlem_4 sup_set_class wceq fgrprinvlem_3 sup_set_class fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 fgrprinvlem_2 sup_set_class fgrprinvlem_4 sup_set_class wceq fgrprinvlem_3 sup_set_class fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_3 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 fgrprinvlem_2 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_3 sup_set_class fgrprinvlem_6 oveq2 eqeq1d rexbidv cbvralv sylib fgrprinvlem_3 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 wrex fgrprinvlem_4 fgrprinvlem_8 fgrprinvlem_5 fgrprinvlem_4 sup_set_class fgrprinvlem_8 wceq fgrprinvlem_3 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 fgrprinvlem_4 sup_set_class fgrprinvlem_8 wceq fgrprinvlem_3 sup_set_class fgrprinvlem_4 sup_set_class fgrprinvlem_6 co fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 fgrprinvlem_4 sup_set_class fgrprinvlem_8 fgrprinvlem_3 sup_set_class fgrprinvlem_6 oveq2 eqeq1d rexbidv rspccva sylan syldan fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_8 fgrprinvlem_7 wceq fgrprinvlem_3 fgrprinvlem_5 fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq fgrprinvlem_8 fgrprinvlem_7 wceq fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa wa fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_6 co fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_8 fgrprinvlem_7 fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_6 co fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co wceq fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_8 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_8 fgrprinvlem_3 sup_set_class fgrprinvlem_6 egrprinvlem_6 oveq2d adantr fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa wa fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_6 co fgrprinvlem_8 fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa wa fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 fgrprinvlem_8 fgrprinvlem_6 fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq simprr oveq1d fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa wa igrprinvlem_2 igrprinvlem_1 igrprinvlem_0 fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_8 fgrprinvlem_5 fgrprinvlem_6 fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa wa fgrprinvlem_0 igrprinvlem_2 sup_set_class fgrprinvlem_5 wcel igrprinvlem_1 sup_set_class fgrprinvlem_5 wcel igrprinvlem_0 sup_set_class fgrprinvlem_5 wcel w3a igrprinvlem_2 sup_set_class igrprinvlem_1 sup_set_class fgrprinvlem_6 co igrprinvlem_0 sup_set_class fgrprinvlem_6 co igrprinvlem_2 sup_set_class igrprinvlem_1 sup_set_class igrprinvlem_0 sup_set_class fgrprinvlem_6 co fgrprinvlem_6 co wceq fgrprinvlem_0 fgrprinvlem_1 fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa simpll fgrprinvlem_0 fgrprinvlem_2 fgrprinvlem_3 fgrprinvlem_4 igrprinvlem_2 sup_set_class igrprinvlem_1 sup_set_class igrprinvlem_0 sup_set_class fgrprinvlem_5 fgrprinvlem_6 egrprinvlem_3 caovassg sylan fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq simprl fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_8 fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa egrprinvlem_5 adantr fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_8 fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa egrprinvlem_5 adantr caovassd fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_7 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_8 wceq fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq wa fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_8 fgrprinvlem_5 wcel fgrprinvlem_7 fgrprinvlem_3 sup_set_class fgrprinvlem_6 co fgrprinvlem_3 sup_set_class wceq fgrprinvlem_3 fgrprinvlem_5 wral fgrprinvlem_7 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_8 wceq egrprinvlem_5 fgrprinvlem_0 fgrprinvlem_7 fgrprinvlem_3 sup_set_class fgrprinvlem_6 co fgrprinvlem_3 sup_set_class wceq fgrprinvlem_3 fgrprinvlem_5 wral fgrprinvlem_1 fgrprinvlem_0 fgrprinvlem_7 fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_2 sup_set_class wceq fgrprinvlem_2 fgrprinvlem_5 wral fgrprinvlem_7 fgrprinvlem_3 sup_set_class fgrprinvlem_6 co fgrprinvlem_3 sup_set_class wceq fgrprinvlem_3 fgrprinvlem_5 wral fgrprinvlem_0 fgrprinvlem_7 fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_2 sup_set_class wceq fgrprinvlem_2 fgrprinvlem_5 egrprinvlem_2 ralrimiva fgrprinvlem_7 fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_2 sup_set_class wceq fgrprinvlem_7 fgrprinvlem_3 sup_set_class fgrprinvlem_6 co fgrprinvlem_3 sup_set_class wceq fgrprinvlem_2 fgrprinvlem_3 fgrprinvlem_5 fgrprinvlem_2 sup_set_class fgrprinvlem_3 sup_set_class wceq fgrprinvlem_7 fgrprinvlem_2 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 fgrprinvlem_3 sup_set_class fgrprinvlem_6 co fgrprinvlem_2 sup_set_class fgrprinvlem_3 sup_set_class fgrprinvlem_2 sup_set_class fgrprinvlem_3 sup_set_class fgrprinvlem_7 fgrprinvlem_6 oveq2 fgrprinvlem_2 sup_set_class fgrprinvlem_3 sup_set_class wceq id eqeq12d cbvralv sylib adantr fgrprinvlem_7 fgrprinvlem_3 sup_set_class fgrprinvlem_6 co fgrprinvlem_3 sup_set_class wceq fgrprinvlem_7 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_8 wceq fgrprinvlem_3 fgrprinvlem_8 fgrprinvlem_5 fgrprinvlem_3 sup_set_class fgrprinvlem_8 wceq fgrprinvlem_7 fgrprinvlem_3 sup_set_class fgrprinvlem_6 co fgrprinvlem_7 fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_7 fgrprinvlem_6 oveq2 fgrprinvlem_3 sup_set_class fgrprinvlem_8 wceq id eqeq12d rspcv sylc adantr 3eqtr3d fgrprinvlem_0 fgrprinvlem_1 wa fgrprinvlem_3 sup_set_class fgrprinvlem_5 wcel fgrprinvlem_3 sup_set_class fgrprinvlem_8 fgrprinvlem_6 co fgrprinvlem_7 wceq simprr 3eqtr3d expr rexlimdva mpd $.
$}
$( /* Deduce right inverse from left inverse and left identity in an
         associative structure (such as a group).  (Contributed by NM,
         10-Aug-2013.)  (Proof shortened by Mario Carneiro, 6-Jan-2015.) */

$)
$v N $.
${
	$d u v w x y z B $.
	$d u v w x y z O $.
	$d u v w x y z ph $.
	$d u v w y z N $.
	$d u v w x y z .+ $.
	$d u v w y z X $.
	$d u v w y ps $.
	igrprinvd_0 $f set w $.
	igrprinvd_1 $f set v $.
	igrprinvd_2 $f set u $.
	fgrprinvd_0 $f wff ph $.
	fgrprinvd_1 $f wff ps $.
	fgrprinvd_2 $f set x $.
	fgrprinvd_3 $f set y $.
	fgrprinvd_4 $f set z $.
	fgrprinvd_5 $f class B $.
	fgrprinvd_6 $f class .+ $.
	fgrprinvd_7 $f class N $.
	fgrprinvd_8 $f class O $.
	fgrprinvd_9 $f class X $.
	egrprinvd_0 $e |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B ) $.
	egrprinvd_1 $e |- ( ph -> O e. B ) $.
	egrprinvd_2 $e |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x ) $.
	egrprinvd_3 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) ) $.
	egrprinvd_4 $e |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O ) $.
	egrprinvd_5 $e |- ( ( ph /\ ps ) -> X e. B ) $.
	egrprinvd_6 $e |- ( ( ph /\ ps ) -> N e. B ) $.
	egrprinvd_7 $e |- ( ( ph /\ ps ) -> ( N .+ X ) = O ) $.
	grprinvd $p |- ( ( ph /\ ps ) -> ( X .+ N ) = O ) $= fgrprinvd_0 fgrprinvd_1 fgrprinvd_2 fgrprinvd_3 fgrprinvd_4 fgrprinvd_5 fgrprinvd_6 fgrprinvd_8 fgrprinvd_9 fgrprinvd_7 fgrprinvd_6 co egrprinvd_0 egrprinvd_1 egrprinvd_2 egrprinvd_3 egrprinvd_4 fgrprinvd_0 fgrprinvd_1 wa igrprinvd_2 igrprinvd_1 fgrprinvd_9 fgrprinvd_7 fgrprinvd_5 fgrprinvd_5 fgrprinvd_5 fgrprinvd_6 fgrprinvd_0 igrprinvd_2 sup_set_class fgrprinvd_5 wcel igrprinvd_1 sup_set_class fgrprinvd_5 wcel wa igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class fgrprinvd_6 co fgrprinvd_5 wcel fgrprinvd_1 fgrprinvd_0 fgrprinvd_2 fgrprinvd_3 igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class fgrprinvd_5 fgrprinvd_5 fgrprinvd_5 fgrprinvd_6 fgrprinvd_0 fgrprinvd_2 sup_set_class fgrprinvd_5 wcel fgrprinvd_3 sup_set_class fgrprinvd_5 wcel fgrprinvd_2 sup_set_class fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_5 wcel egrprinvd_0 3expb caovclg adantlr egrprinvd_5 egrprinvd_6 caovcld fgrprinvd_0 fgrprinvd_1 wa fgrprinvd_9 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_9 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_6 co fgrprinvd_9 fgrprinvd_7 fgrprinvd_9 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_6 co fgrprinvd_6 co fgrprinvd_9 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_0 fgrprinvd_1 wa igrprinvd_2 igrprinvd_1 igrprinvd_0 fgrprinvd_9 fgrprinvd_7 fgrprinvd_9 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_5 fgrprinvd_6 fgrprinvd_0 igrprinvd_2 sup_set_class fgrprinvd_5 wcel igrprinvd_1 sup_set_class fgrprinvd_5 wcel igrprinvd_0 sup_set_class fgrprinvd_5 wcel w3a igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class fgrprinvd_6 co igrprinvd_0 sup_set_class fgrprinvd_6 co igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class igrprinvd_0 sup_set_class fgrprinvd_6 co fgrprinvd_6 co wceq fgrprinvd_1 fgrprinvd_0 fgrprinvd_2 fgrprinvd_3 fgrprinvd_4 igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class igrprinvd_0 sup_set_class fgrprinvd_5 fgrprinvd_6 egrprinvd_3 caovassg adantlr egrprinvd_5 egrprinvd_6 fgrprinvd_0 fgrprinvd_1 wa igrprinvd_2 igrprinvd_1 fgrprinvd_9 fgrprinvd_7 fgrprinvd_5 fgrprinvd_5 fgrprinvd_5 fgrprinvd_6 fgrprinvd_0 igrprinvd_2 sup_set_class fgrprinvd_5 wcel igrprinvd_1 sup_set_class fgrprinvd_5 wcel wa igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class fgrprinvd_6 co fgrprinvd_5 wcel fgrprinvd_1 fgrprinvd_0 fgrprinvd_2 fgrprinvd_3 igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class fgrprinvd_5 fgrprinvd_5 fgrprinvd_5 fgrprinvd_6 fgrprinvd_0 fgrprinvd_2 sup_set_class fgrprinvd_5 wcel fgrprinvd_3 sup_set_class fgrprinvd_5 wcel fgrprinvd_2 sup_set_class fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_5 wcel egrprinvd_0 3expb caovclg adantlr egrprinvd_5 egrprinvd_6 caovcld caovassd fgrprinvd_0 fgrprinvd_1 wa fgrprinvd_7 fgrprinvd_9 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_6 co fgrprinvd_7 fgrprinvd_9 fgrprinvd_6 fgrprinvd_0 fgrprinvd_1 wa fgrprinvd_7 fgrprinvd_9 fgrprinvd_6 co fgrprinvd_7 fgrprinvd_6 co fgrprinvd_8 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_7 fgrprinvd_9 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_6 co fgrprinvd_7 fgrprinvd_0 fgrprinvd_1 wa fgrprinvd_7 fgrprinvd_9 fgrprinvd_6 co fgrprinvd_8 fgrprinvd_7 fgrprinvd_6 egrprinvd_7 oveq1d fgrprinvd_0 fgrprinvd_1 wa igrprinvd_2 igrprinvd_1 igrprinvd_0 fgrprinvd_7 fgrprinvd_9 fgrprinvd_7 fgrprinvd_5 fgrprinvd_6 fgrprinvd_0 igrprinvd_2 sup_set_class fgrprinvd_5 wcel igrprinvd_1 sup_set_class fgrprinvd_5 wcel igrprinvd_0 sup_set_class fgrprinvd_5 wcel w3a igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class fgrprinvd_6 co igrprinvd_0 sup_set_class fgrprinvd_6 co igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class igrprinvd_0 sup_set_class fgrprinvd_6 co fgrprinvd_6 co wceq fgrprinvd_1 fgrprinvd_0 fgrprinvd_2 fgrprinvd_3 fgrprinvd_4 igrprinvd_2 sup_set_class igrprinvd_1 sup_set_class igrprinvd_0 sup_set_class fgrprinvd_5 fgrprinvd_6 egrprinvd_3 caovassg adantlr egrprinvd_6 egrprinvd_5 egrprinvd_6 caovassd fgrprinvd_0 fgrprinvd_1 wa fgrprinvd_7 fgrprinvd_5 wcel fgrprinvd_8 fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_3 sup_set_class wceq fgrprinvd_3 fgrprinvd_5 wral fgrprinvd_8 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_7 wceq egrprinvd_6 fgrprinvd_0 fgrprinvd_8 fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_3 sup_set_class wceq fgrprinvd_3 fgrprinvd_5 wral fgrprinvd_1 fgrprinvd_0 fgrprinvd_8 fgrprinvd_2 sup_set_class fgrprinvd_6 co fgrprinvd_2 sup_set_class wceq fgrprinvd_2 fgrprinvd_5 wral fgrprinvd_8 fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_3 sup_set_class wceq fgrprinvd_3 fgrprinvd_5 wral fgrprinvd_0 fgrprinvd_8 fgrprinvd_2 sup_set_class fgrprinvd_6 co fgrprinvd_2 sup_set_class wceq fgrprinvd_2 fgrprinvd_5 egrprinvd_2 ralrimiva fgrprinvd_8 fgrprinvd_2 sup_set_class fgrprinvd_6 co fgrprinvd_2 sup_set_class wceq fgrprinvd_8 fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_3 sup_set_class wceq fgrprinvd_2 fgrprinvd_3 fgrprinvd_5 fgrprinvd_2 sup_set_class fgrprinvd_3 sup_set_class wceq fgrprinvd_8 fgrprinvd_2 sup_set_class fgrprinvd_6 co fgrprinvd_8 fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_2 sup_set_class fgrprinvd_3 sup_set_class fgrprinvd_2 sup_set_class fgrprinvd_3 sup_set_class fgrprinvd_8 fgrprinvd_6 oveq2 fgrprinvd_2 sup_set_class fgrprinvd_3 sup_set_class wceq id eqeq12d cbvralv sylib adantr fgrprinvd_8 fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_3 sup_set_class wceq fgrprinvd_8 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_7 wceq fgrprinvd_3 fgrprinvd_7 fgrprinvd_5 fgrprinvd_3 sup_set_class fgrprinvd_7 wceq fgrprinvd_8 fgrprinvd_3 sup_set_class fgrprinvd_6 co fgrprinvd_8 fgrprinvd_7 fgrprinvd_6 co fgrprinvd_3 sup_set_class fgrprinvd_7 fgrprinvd_3 sup_set_class fgrprinvd_7 fgrprinvd_8 fgrprinvd_6 oveq2 fgrprinvd_3 sup_set_class fgrprinvd_7 wceq id eqeq12d rspcv sylc 3eqtr3d oveq2d eqtrd grprinvlem $.
$}
$( /* Deduce right identity from left inverse and left identity in an
       associative structure (such as a group).  (Contributed by NM,
       10-Aug-2013.)  (Proof shortened by Mario Carneiro, 6-Jan-2015.) */

$)
$v n $.
${
	$d n u v w x y z B $.
	$d n u v w x y z O $.
	$d n u v w x y z ph $.
	$d u v w y z $.
	$d n u v w x y z .+ $.
	$d u v w y z $.
	$d u v w y $.
	igrpridd_0 $f set w $.
	igrpridd_1 $f set v $.
	igrpridd_2 $f set u $.
	igrpridd_3 $f set n $.
	fgrpridd_0 $f wff ph $.
	fgrpridd_1 $f set x $.
	fgrpridd_2 $f set y $.
	fgrpridd_3 $f set z $.
	fgrpridd_4 $f class B $.
	fgrpridd_5 $f class .+ $.
	fgrpridd_6 $f class O $.
	egrpridd_0 $e |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B ) $.
	egrpridd_1 $e |- ( ph -> O e. B ) $.
	egrpridd_2 $e |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x ) $.
	egrpridd_3 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) ) $.
	egrpridd_4 $e |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O ) $.
	grpridd $p |- ( ( ph /\ x e. B ) -> ( x .+ O ) = x ) $= fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel wa fgrpridd_6 fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_1 sup_set_class fgrpridd_6 fgrpridd_5 co fgrpridd_1 sup_set_class fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel wa igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq igrpridd_3 fgrpridd_4 wrex fgrpridd_6 fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_1 sup_set_class fgrpridd_6 fgrpridd_5 co wceq fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel wa fgrpridd_2 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq fgrpridd_2 fgrpridd_4 wrex igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq igrpridd_3 fgrpridd_4 wrex egrpridd_4 fgrpridd_2 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq fgrpridd_2 igrpridd_3 fgrpridd_4 fgrpridd_2 sup_set_class igrpridd_3 sup_set_class wceq fgrpridd_2 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 fgrpridd_2 sup_set_class igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 oveq1 eqeq1d cbvrexv sylib fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel wa igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq fgrpridd_6 fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_1 sup_set_class fgrpridd_6 fgrpridd_5 co wceq igrpridd_3 fgrpridd_4 fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel wa igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq fgrpridd_6 fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_1 sup_set_class fgrpridd_6 fgrpridd_5 co wceq fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa fgrpridd_6 fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_1 sup_set_class fgrpridd_6 fgrpridd_5 co wceq fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa wa wa fgrpridd_1 sup_set_class igrpridd_3 sup_set_class fgrpridd_5 co fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_1 sup_set_class igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_5 co fgrpridd_6 fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_1 sup_set_class fgrpridd_6 fgrpridd_5 co fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa wa wa igrpridd_2 igrpridd_1 igrpridd_0 fgrpridd_1 sup_set_class igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_4 fgrpridd_5 fgrpridd_0 igrpridd_2 sup_set_class fgrpridd_4 wcel igrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_0 sup_set_class fgrpridd_4 wcel w3a igrpridd_2 sup_set_class igrpridd_1 sup_set_class fgrpridd_5 co igrpridd_0 sup_set_class fgrpridd_5 co igrpridd_2 sup_set_class igrpridd_1 sup_set_class igrpridd_0 sup_set_class fgrpridd_5 co fgrpridd_5 co wceq fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa wa fgrpridd_0 fgrpridd_1 fgrpridd_2 fgrpridd_3 igrpridd_2 sup_set_class igrpridd_1 sup_set_class igrpridd_0 sup_set_class fgrpridd_4 fgrpridd_5 egrpridd_3 caovassg adantlr fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa simprl fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq simprrl fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa simprl caovassd fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa wa wa fgrpridd_1 sup_set_class igrpridd_3 sup_set_class fgrpridd_5 co fgrpridd_6 fgrpridd_1 sup_set_class fgrpridd_5 fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa wa fgrpridd_1 fgrpridd_2 fgrpridd_3 fgrpridd_4 fgrpridd_5 igrpridd_3 sup_set_class fgrpridd_6 fgrpridd_1 sup_set_class egrpridd_0 egrpridd_1 egrpridd_2 egrpridd_3 egrpridd_4 fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa simprl fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq simprrl fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq simprrr grprinvd oveq1d fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq wa wa wa igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 fgrpridd_1 sup_set_class fgrpridd_5 fgrpridd_0 fgrpridd_1 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_4 wcel igrpridd_3 sup_set_class fgrpridd_1 sup_set_class fgrpridd_5 co fgrpridd_6 wceq simprrr oveq2d 3eqtr3d anassrs expr rexlimdva mpd egrpridd_2 eqtr3d $.
$}

