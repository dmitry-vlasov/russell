$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Functions.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Operations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Extend class notation to include the value of an operation ` F ` (such as
     ` + ` ) for two arguments ` A ` and ` B ` .  Note that the syntax is
     simply three class symbols in a row surrounded by parentheses.  Since
     operation values are the only possible class expressions consisting of
     three class expressions in a row surrounded by parentheses, the syntax is
     unambiguous.  (For an example of how syntax could become ambiguous if we
     are not careful, see the comment in ~ cneg .) $)

${
	$v A B F  $.
	f0_co $f class A $.
	f1_co $f class B $.
	f2_co $f class F $.
	a_co $a class ( A F B ) $.
$}

$(Extend class notation to include class abstraction (class builder) of
     nested ordered pairs. $)

${
	$v ph x y z  $.
	f0_coprab $f wff ph $.
	f1_coprab $f set x $.
	f2_coprab $f set y $.
	f3_coprab $f set z $.
	a_coprab $a class { <. <. x , y >. , z >. | ph } $.
$}

$(Extend the definition of a class to include maps-to notation for defining
     an operation via a rule. $)

${
	$v x y A B C  $.
	f0_cmpt2 $f set x $.
	f1_cmpt2 $f set y $.
	f2_cmpt2 $f class A $.
	f3_cmpt2 $f class B $.
	f4_cmpt2 $f class C $.
	a_cmpt2 $a class ( x e. A , y e. B |-> C ) $.
$}

$(Define the value of an operation.  Definition of operation value in
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
     defined by ~ df-oprab .  (Contributed by NM, 28-Feb-1995.) $)

${
	$v A B F  $.
	f0_df-ov $f class A $.
	f1_df-ov $f class B $.
	f2_df-ov $f class F $.
	a_df-ov $a |- ( A F B ) = ( F ` <. A , B >. ) $.
$}

$(Define the class abstraction (class builder) of a collection of nested
       ordered pairs (for use in defining operations).  This is a special case
       of Definition 4.16 of [TakeutiZaring] p. 14.  Normally ` x ` , ` y ` ,
       and ` z ` are distinct, although the definition doesn't strictly require
       it.  See ~ df-ov for the value of an operation.  The brace notation is
       called "class abstraction" by Quine; it is also called a "class builder"
       in the literature.  The value of the most common operation class builder
       is given by ~ ovmpt2 .  (Contributed by NM, 12-Mar-1995.) $)

${
	$v ph x y z w  $.
	$d x w  $.
	$d y w  $.
	$d z w  $.
	$d w ph  $.
	f0_df-oprab $f wff ph $.
	f1_df-oprab $f set x $.
	f2_df-oprab $f set y $.
	f3_df-oprab $f set z $.
	f4_df-oprab $f set w $.
	a_df-oprab $a |- { <. <. x , y >. , z >. | ph } = { w | E. x E. y E. z ( w = <. <. x , y >. , z >. /\ ph ) } $.
$}

$(Define maps-to notation for defining an operation via a rule.  Read as
       "the operation defined by the map from ` x , y ` (in ` A X. B ` ) to
       ` B ( x , y ) ` ."  An extension of ~ df-mpt for two arguments.
       (Contributed by NM, 17-Feb-2008.) $)

${
	$v x y z A B C  $.
	$d x z  $.
	$d y z  $.
	$d z A  $.
	$d z B  $.
	$d z C  $.
	f0_df-mpt2 $f set x $.
	f1_df-mpt2 $f set y $.
	f2_df-mpt2 $f set z $.
	f3_df-mpt2 $f class A $.
	f4_df-mpt2 $f class B $.
	f5_df-mpt2 $f class C $.
	a_df-mpt2 $a |- ( x e. A , y e. B |-> C ) = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ z = C ) } $.
$}

$(Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) $)

${
	$v A B F G  $.
	f0_oveq $f class A $.
	f1_oveq $f class B $.
	f2_oveq $f class F $.
	f3_oveq $f class G $.
	p_oveq $p |- ( F = G -> ( A F B ) = ( A G B ) ) $= f0_oveq f1_oveq a_cop f2_oveq f3_oveq p_fveq1 f0_oveq f1_oveq f2_oveq a_df-ov f0_oveq f1_oveq f3_oveq a_df-ov f2_oveq f3_oveq a_wceq f0_oveq f1_oveq a_cop f2_oveq a_cfv f0_oveq f1_oveq a_cop f3_oveq a_cfv f0_oveq f1_oveq f2_oveq a_co f0_oveq f1_oveq f3_oveq a_co p_3eqtr4g $.
$}

$(Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) $)

${
	$v A B C F  $.
	f0_oveq1 $f class A $.
	f1_oveq1 $f class B $.
	f2_oveq1 $f class C $.
	f3_oveq1 $f class F $.
	p_oveq1 $p |- ( A = B -> ( A F C ) = ( B F C ) ) $= f0_oveq1 f1_oveq1 f2_oveq1 p_opeq1 f0_oveq1 f1_oveq1 a_wceq f0_oveq1 f2_oveq1 a_cop f1_oveq1 f2_oveq1 a_cop f3_oveq1 p_fveq2d f0_oveq1 f2_oveq1 f3_oveq1 a_df-ov f1_oveq1 f2_oveq1 f3_oveq1 a_df-ov f0_oveq1 f1_oveq1 a_wceq f0_oveq1 f2_oveq1 a_cop f3_oveq1 a_cfv f1_oveq1 f2_oveq1 a_cop f3_oveq1 a_cfv f0_oveq1 f2_oveq1 f3_oveq1 a_co f1_oveq1 f2_oveq1 f3_oveq1 a_co p_3eqtr4g $.
$}

$(Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) $)

${
	$v A B C F  $.
	f0_oveq2 $f class A $.
	f1_oveq2 $f class B $.
	f2_oveq2 $f class C $.
	f3_oveq2 $f class F $.
	p_oveq2 $p |- ( A = B -> ( C F A ) = ( C F B ) ) $= f0_oveq2 f1_oveq2 f2_oveq2 p_opeq2 f0_oveq2 f1_oveq2 a_wceq f2_oveq2 f0_oveq2 a_cop f2_oveq2 f1_oveq2 a_cop f3_oveq2 p_fveq2d f2_oveq2 f0_oveq2 f3_oveq2 a_df-ov f2_oveq2 f1_oveq2 f3_oveq2 a_df-ov f0_oveq2 f1_oveq2 a_wceq f2_oveq2 f0_oveq2 a_cop f3_oveq2 a_cfv f2_oveq2 f1_oveq2 a_cop f3_oveq2 a_cfv f2_oveq2 f0_oveq2 f3_oveq2 a_co f2_oveq2 f1_oveq2 f3_oveq2 a_co p_3eqtr4g $.
$}

$(Equality theorem for operation value.  (Contributed by NM,
     16-Jul-1995.) $)

${
	$v A B C D F  $.
	f0_oveq12 $f class A $.
	f1_oveq12 $f class B $.
	f2_oveq12 $f class C $.
	f3_oveq12 $f class D $.
	f4_oveq12 $f class F $.
	p_oveq12 $p |- ( ( A = B /\ C = D ) -> ( A F C ) = ( B F D ) ) $= f0_oveq12 f1_oveq12 f2_oveq12 f4_oveq12 p_oveq1 f2_oveq12 f3_oveq12 f1_oveq12 f4_oveq12 p_oveq2 f0_oveq12 f1_oveq12 a_wceq f2_oveq12 f3_oveq12 a_wceq f0_oveq12 f2_oveq12 f4_oveq12 a_co f1_oveq12 f2_oveq12 f4_oveq12 a_co f1_oveq12 f3_oveq12 f4_oveq12 a_co p_sylan9eq $.
$}

$(Equality inference for operation value.  (Contributed by NM,
       28-Feb-1995.) $)

${
	$v A B C F  $.
	f0_oveq1i $f class A $.
	f1_oveq1i $f class B $.
	f2_oveq1i $f class C $.
	f3_oveq1i $f class F $.
	e0_oveq1i $e |- A = B $.
	p_oveq1i $p |- ( A F C ) = ( B F C ) $= e0_oveq1i f0_oveq1i f1_oveq1i f2_oveq1i f3_oveq1i p_oveq1 f0_oveq1i f1_oveq1i a_wceq f0_oveq1i f2_oveq1i f3_oveq1i a_co f1_oveq1i f2_oveq1i f3_oveq1i a_co a_wceq a_ax-mp $.
$}

$(Equality inference for operation value.  (Contributed by NM,
       28-Feb-1995.) $)

${
	$v A B C F  $.
	f0_oveq2i $f class A $.
	f1_oveq2i $f class B $.
	f2_oveq2i $f class C $.
	f3_oveq2i $f class F $.
	e0_oveq2i $e |- A = B $.
	p_oveq2i $p |- ( C F A ) = ( C F B ) $= e0_oveq2i f0_oveq2i f1_oveq2i f2_oveq2i f3_oveq2i p_oveq2 f0_oveq2i f1_oveq2i a_wceq f2_oveq2i f0_oveq2i f3_oveq2i a_co f2_oveq2i f1_oveq2i f3_oveq2i a_co a_wceq a_ax-mp $.
$}

$(Equality inference for operation value.  (Contributed by NM,
         28-Feb-1995.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)

${
	$v A B C D F  $.
	f0_oveq12i $f class A $.
	f1_oveq12i $f class B $.
	f2_oveq12i $f class C $.
	f3_oveq12i $f class D $.
	f4_oveq12i $f class F $.
	e0_oveq12i $e |- A = B $.
	e1_oveq12i $e |- C = D $.
	p_oveq12i $p |- ( A F C ) = ( B F D ) $= e0_oveq12i e1_oveq12i f0_oveq12i f1_oveq12i f2_oveq12i f3_oveq12i f4_oveq12i p_oveq12 f0_oveq12i f1_oveq12i a_wceq f2_oveq12i f3_oveq12i a_wceq f0_oveq12i f2_oveq12i f4_oveq12i a_co f1_oveq12i f3_oveq12i f4_oveq12i a_co a_wceq p_mp2an $.
$}

$(Equality inference for operation value.  (Contributed by NM,
       24-Nov-2007.) $)

${
	$v A B C D  $.
	f0_oveqi $f class A $.
	f1_oveqi $f class B $.
	f2_oveqi $f class C $.
	f3_oveqi $f class D $.
	e0_oveqi $e |- A = B $.
	p_oveqi $p |- ( C A D ) = ( C B D ) $= e0_oveqi f2_oveqi f3_oveqi f0_oveqi f1_oveqi p_oveq f0_oveqi f1_oveqi a_wceq f2_oveqi f3_oveqi f0_oveqi a_co f2_oveqi f3_oveqi f1_oveqi a_co a_wceq a_ax-mp $.
$}

$(Equality inference for operation value.  (Contributed by FL,
       11-Jul-2010.) $)

${
	$v A B C D F G  $.
	f0_oveq123i $f class A $.
	f1_oveq123i $f class B $.
	f2_oveq123i $f class C $.
	f3_oveq123i $f class D $.
	f4_oveq123i $f class F $.
	f5_oveq123i $f class G $.
	e0_oveq123i $e |- A = C $.
	e1_oveq123i $e |- B = D $.
	e2_oveq123i $e |- F = G $.
	p_oveq123i $p |- ( A F B ) = ( C G D ) $= e0_oveq123i e1_oveq123i f0_oveq123i f2_oveq123i f1_oveq123i f3_oveq123i f4_oveq123i p_oveq12i e2_oveq123i f4_oveq123i f5_oveq123i f2_oveq123i f3_oveq123i p_oveqi f0_oveq123i f1_oveq123i f4_oveq123i a_co f2_oveq123i f3_oveq123i f4_oveq123i a_co f2_oveq123i f3_oveq123i f5_oveq123i a_co p_eqtri $.
$}

$(Equality deduction for operation value.  (Contributed by NM,
       13-Mar-1995.) $)

${
	$v ph A B C F  $.
	f0_oveq1d $f wff ph $.
	f1_oveq1d $f class A $.
	f2_oveq1d $f class B $.
	f3_oveq1d $f class C $.
	f4_oveq1d $f class F $.
	e0_oveq1d $e |- ( ph -> A = B ) $.
	p_oveq1d $p |- ( ph -> ( A F C ) = ( B F C ) ) $= e0_oveq1d f1_oveq1d f2_oveq1d f3_oveq1d f4_oveq1d p_oveq1 f0_oveq1d f1_oveq1d f2_oveq1d a_wceq f1_oveq1d f3_oveq1d f4_oveq1d a_co f2_oveq1d f3_oveq1d f4_oveq1d a_co a_wceq p_syl $.
$}

$(Equality deduction for operation value.  (Contributed by NM,
       13-Mar-1995.) $)

${
	$v ph A B C F  $.
	f0_oveq2d $f wff ph $.
	f1_oveq2d $f class A $.
	f2_oveq2d $f class B $.
	f3_oveq2d $f class C $.
	f4_oveq2d $f class F $.
	e0_oveq2d $e |- ( ph -> A = B ) $.
	p_oveq2d $p |- ( ph -> ( C F A ) = ( C F B ) ) $= e0_oveq2d f1_oveq2d f2_oveq2d f3_oveq2d f4_oveq2d p_oveq2 f0_oveq2d f1_oveq2d f2_oveq2d a_wceq f3_oveq2d f1_oveq2d f4_oveq2d a_co f3_oveq2d f2_oveq2d f4_oveq2d a_co a_wceq p_syl $.
$}

$(Equality deduction for operation value.  (Contributed by NM,
       9-Sep-2006.) $)

${
	$v ph A B C D  $.
	f0_oveqd $f wff ph $.
	f1_oveqd $f class A $.
	f2_oveqd $f class B $.
	f3_oveqd $f class C $.
	f4_oveqd $f class D $.
	e0_oveqd $e |- ( ph -> A = B ) $.
	p_oveqd $p |- ( ph -> ( C A D ) = ( C B D ) ) $= e0_oveqd f3_oveqd f4_oveqd f1_oveqd f2_oveqd p_oveq f0_oveqd f1_oveqd f2_oveqd a_wceq f3_oveqd f4_oveqd f1_oveqd a_co f3_oveqd f4_oveqd f2_oveqd a_co a_wceq p_syl $.
$}

$(Equality deduction for operation value.  (Contributed by NM,
         13-Mar-1995.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)

${
	$v ph A B C D F  $.
	f0_oveq12d $f wff ph $.
	f1_oveq12d $f class A $.
	f2_oveq12d $f class B $.
	f3_oveq12d $f class C $.
	f4_oveq12d $f class D $.
	f5_oveq12d $f class F $.
	e0_oveq12d $e |- ( ph -> A = B ) $.
	e1_oveq12d $e |- ( ph -> C = D ) $.
	p_oveq12d $p |- ( ph -> ( A F C ) = ( B F D ) ) $= e0_oveq12d e1_oveq12d f1_oveq12d f2_oveq12d f3_oveq12d f4_oveq12d f5_oveq12d p_oveq12 f0_oveq12d f1_oveq12d f2_oveq12d a_wceq f3_oveq12d f4_oveq12d a_wceq f1_oveq12d f3_oveq12d f5_oveq12d a_co f2_oveq12d f4_oveq12d f5_oveq12d a_co a_wceq p_syl2anc $.
$}

$(Equality deduction for operation value.  (Contributed by NM,
         10-Aug-1995.) $)

${
	$v ph ps A B C D F  $.
	f0_oveqan12d $f wff ph $.
	f1_oveqan12d $f wff ps $.
	f2_oveqan12d $f class A $.
	f3_oveqan12d $f class B $.
	f4_oveqan12d $f class C $.
	f5_oveqan12d $f class D $.
	f6_oveqan12d $f class F $.
	e0_oveqan12d $e |- ( ph -> A = B ) $.
	e1_oveqan12d $e |- ( ps -> C = D ) $.
	p_oveqan12d $p |- ( ( ph /\ ps ) -> ( A F C ) = ( B F D ) ) $= e0_oveqan12d e1_oveqan12d f2_oveqan12d f3_oveqan12d f4_oveqan12d f5_oveqan12d f6_oveqan12d p_oveq12 f0_oveqan12d f2_oveqan12d f3_oveqan12d a_wceq f4_oveqan12d f5_oveqan12d a_wceq f2_oveqan12d f4_oveqan12d f6_oveqan12d a_co f3_oveqan12d f5_oveqan12d f6_oveqan12d a_co a_wceq f1_oveqan12d p_syl2an $.
$}

$(Equality deduction for operation value.  (Contributed by NM,
         10-Aug-1995.) $)

${
	$v ph ps A B C D F  $.
	f0_oveqan12rd $f wff ph $.
	f1_oveqan12rd $f wff ps $.
	f2_oveqan12rd $f class A $.
	f3_oveqan12rd $f class B $.
	f4_oveqan12rd $f class C $.
	f5_oveqan12rd $f class D $.
	f6_oveqan12rd $f class F $.
	e0_oveqan12rd $e |- ( ph -> A = B ) $.
	e1_oveqan12rd $e |- ( ps -> C = D ) $.
	p_oveqan12rd $p |- ( ( ps /\ ph ) -> ( A F C ) = ( B F D ) ) $= e0_oveqan12rd e1_oveqan12rd f0_oveqan12rd f1_oveqan12rd f2_oveqan12rd f3_oveqan12rd f4_oveqan12rd f5_oveqan12rd f6_oveqan12rd p_oveqan12d f0_oveqan12rd f1_oveqan12rd f2_oveqan12rd f4_oveqan12rd f6_oveqan12rd a_co f3_oveqan12rd f5_oveqan12rd f6_oveqan12rd a_co a_wceq p_ancoms $.
$}

$(Equality deduction for operation value.  (Contributed by FL,
       22-Dec-2008.) $)

${
	$v ph A B C D F G  $.
	f0_oveq123d $f wff ph $.
	f1_oveq123d $f class A $.
	f2_oveq123d $f class B $.
	f3_oveq123d $f class C $.
	f4_oveq123d $f class D $.
	f5_oveq123d $f class F $.
	f6_oveq123d $f class G $.
	e0_oveq123d $e |- ( ph -> F = G ) $.
	e1_oveq123d $e |- ( ph -> A = B ) $.
	e2_oveq123d $e |- ( ph -> C = D ) $.
	p_oveq123d $p |- ( ph -> ( A F C ) = ( B G D ) ) $= e0_oveq123d f0_oveq123d f5_oveq123d f6_oveq123d f1_oveq123d f3_oveq123d p_oveqd e1_oveq123d e2_oveq123d f0_oveq123d f1_oveq123d f2_oveq123d f3_oveq123d f4_oveq123d f6_oveq123d p_oveq12d f0_oveq123d f1_oveq123d f3_oveq123d f5_oveq123d a_co f1_oveq123d f3_oveq123d f6_oveq123d a_co f2_oveq123d f4_oveq123d f6_oveq123d a_co p_eqtrd $.
$}

$(Deduction version of bound-variable hypothesis builder ~ nfov .
       (Contributed by NM, 13-Dec-2005.)  (Proof shortened by Andrew Salmon,
       22-Oct-2011.) $)

${
	$v ph x A B F  $.
	f0_nfovd $f wff ph $.
	f1_nfovd $f set x $.
	f2_nfovd $f class A $.
	f3_nfovd $f class B $.
	f4_nfovd $f class F $.
	e0_nfovd $e |- ( ph -> F/_ x A ) $.
	e1_nfovd $e |- ( ph -> F/_ x F ) $.
	e2_nfovd $e |- ( ph -> F/_ x B ) $.
	p_nfovd $p |- ( ph -> F/_ x ( A F B ) ) $= f2_nfovd f3_nfovd f4_nfovd a_df-ov e1_nfovd e0_nfovd e2_nfovd f0_nfovd f1_nfovd f2_nfovd f3_nfovd p_nfopd f0_nfovd f1_nfovd f2_nfovd f3_nfovd a_cop f4_nfovd p_nffvd f0_nfovd f1_nfovd f2_nfovd f3_nfovd f4_nfovd a_co f2_nfovd f3_nfovd a_cop f4_nfovd a_cfv p_nfcxfrd $.
$}

$(Bound-variable hypothesis builder for operation value.  (Contributed by
       NM, 4-May-2004.) $)

${
	$v x A B F  $.
	f0_nfov $f set x $.
	f1_nfov $f class A $.
	f2_nfov $f class B $.
	f3_nfov $f class F $.
	e0_nfov $e |- F/_ x A $.
	e1_nfov $e |- F/_ x F $.
	e2_nfov $e |- F/_ x B $.
	p_nfov $p |- F/_ x ( A F B ) $= e0_nfov f0_nfov f1_nfov a_wnfc a_wtru p_a1i e1_nfov f0_nfov f3_nfov a_wnfc a_wtru p_a1i e2_nfov f0_nfov f2_nfov a_wnfc a_wtru p_a1i a_wtru f0_nfov f1_nfov f2_nfov f3_nfov p_nfovd f0_nfov f1_nfov f2_nfov f3_nfov a_co a_wnfc p_trud $.
$}

$(The law of concretion.  Special case of Theorem 9.5 of [Quine] p. 61.
       (Contributed by Mario Carneiro, 20-Mar-2013.) $)

${
	$v ph x y z  $.
	$d a ph r s t w  $.
	$d a r s t w x  $.
	$d a r s t w y  $.
	$d a r s t w z  $.
	f0_oprabid $f wff ph $.
	f1_oprabid $f set x $.
	f2_oprabid $f set y $.
	f3_oprabid $f set z $.
	i0_oprabid $f set w $.
	i1_oprabid $f set t $.
	i2_oprabid $f set s $.
	i3_oprabid $f set r $.
	i4_oprabid $f set a $.
	p_oprabid $p |- ( <. <. x , y >. , z >. e. { <. <. x , y >. , z >. | ph } <-> ph ) $= f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class p_opex f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class p_opex f3_oprabid p_vex i4_oprabid i1_oprabid i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class p_eqvinop i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq a_wa i1_oprabid a_wex i4_oprabid a_wex p_biimpi i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop p_eqeq1 i4_oprabid p_vex i1_oprabid p_vex i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class p_opth1 i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i4_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop a_wceq p_syl6bi f1_oprabid p_vex f2_oprabid p_vex i3_oprabid i2_oprabid i4_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class p_eqvinop i4_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class p_opeq1 i4_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop a_wceq i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop i0_oprabid a_sup_set_class p_eqeq2d f1_oprabid p_vex f2_oprabid p_vex f3_oprabid p_vex f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class p_otth2 f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq a_df-3an f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq a_w3a f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq a_wa f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq a_wa p_bitri f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq a_wa f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq a_wa f0_oprabid p_anbi1i f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq a_wa f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid p_anass f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa p_anass f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq a_wa f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq a_wa f0_oprabid a_wa f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq a_wa f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa a_wa p_3bitri f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa a_wa f1_oprabid f2_oprabid f3_oprabid p_3exbii f1_oprabid f3_oprabid p_nfcvf2 f1_oprabid a_sup_set_class f3_oprabid a_sup_set_class a_wceq f1_oprabid a_wal a_wn f3_oprabid i3_oprabid a_sup_set_class p_nfcvd f1_oprabid a_sup_set_class f3_oprabid a_sup_set_class a_wceq f1_oprabid a_wal a_wn f3_oprabid f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class p_nfeqd f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f1_oprabid f3_oprabid p_exdistrf f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa a_wa f3_oprabid a_wex f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex a_wa f1_oprabid a_wex f2_oprabid p_eximi f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa a_wa f3_oprabid a_wex f1_oprabid f2_oprabid p_excom f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex a_wa f1_oprabid f2_oprabid p_excom f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa a_wa f3_oprabid a_wex f1_oprabid a_wex f2_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex a_wa f1_oprabid a_wex f2_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex f1_oprabid a_wex p_3imtr4i f1_oprabid f2_oprabid p_nfcvf2 f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_wceq f1_oprabid a_wal a_wn f2_oprabid i3_oprabid a_sup_set_class p_nfcvd f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_wceq f1_oprabid a_wal a_wn f2_oprabid f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class p_nfeqd f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex f1_oprabid f2_oprabid p_exdistrf f2_oprabid f3_oprabid p_nfcvf2 f2_oprabid a_sup_set_class f3_oprabid a_sup_set_class a_wceq f2_oprabid a_wal a_wn f3_oprabid i2_oprabid a_sup_set_class p_nfcvd f2_oprabid a_sup_set_class f3_oprabid a_sup_set_class a_wceq f2_oprabid a_wal a_wn f3_oprabid f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class p_nfeqd f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f2_oprabid f3_oprabid p_exdistrf f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex f2_oprabid a_wex f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq p_anim2i f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex f2_oprabid a_wex a_wa f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid p_eximi f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa f3_oprabid a_wex f2_oprabid a_wex a_wa f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid a_wex p_3syl f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa a_wa a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid a_wex p_sylbi f1_oprabid p_vex f2_oprabid p_vex f3_oprabid p_vex f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class p_otth2 f1_oprabid i3_oprabid p_euequ1 f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex f1_oprabid p_eupick f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f1_oprabid a_weu f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wi p_mpan f2_oprabid i2_oprabid p_euequ1 f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid p_eupick f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f2_oprabid a_weu f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wi p_mpan f3_oprabid i1_oprabid p_euequ1 f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid f3_oprabid p_eupick f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f3_oprabid a_weu f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wi p_mpan f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wi p_syl6 f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wi a_wi p_syl6 f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid p_3impd f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq a_w3a f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid a_wex f0_oprabid p_syl5bi f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid a_wex f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid p_com12 f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f1_oprabid a_sup_set_class i3_oprabid a_sup_set_class a_wceq f2_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_wceq f3_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_wceq f0_oprabid a_wa f3_oprabid a_wex a_wa f2_oprabid a_wex a_wa f1_oprabid a_wex f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid p_syl5 i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop p_eqeq1 i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop p_eqcom i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq p_syl6bb i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop p_eqeq1 i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop p_eqcom i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq p_syl6bb i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid p_anbi1d i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f1_oprabid f2_oprabid f3_oprabid p_3exbidv i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid p_imbi1d i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi p_imbi12d i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi a_wi f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi a_wi p_mpbiri i4_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi a_wi p_syl6bi i4_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi a_wi a_wi i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop a_wceq p_adantr i4_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop a_wceq i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop a_wceq a_wa i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi a_wi a_wi i3_oprabid i2_oprabid p_exlimivv i4_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop a_wceq i4_oprabid a_sup_set_class i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop a_wceq i3_oprabid a_sup_set_class i2_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop a_wceq a_wa i2_oprabid a_wex i3_oprabid a_wex i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi a_wi a_wi p_sylbi i4_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi p_com3l i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i4_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi p_mpdd i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi a_wi i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq p_adantr i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq a_wa i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi a_wi i4_oprabid i1_oprabid p_exlimivv i0_oprabid a_sup_set_class i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop a_wceq i4_oprabid a_sup_set_class i1_oprabid a_sup_set_class a_cop f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq a_wa i1_oprabid a_wex i4_oprabid a_wex i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid a_wi p_mpcom i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid p_19.8a i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid p_19.8a i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid p_19.8a i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex p_3syl i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex p_ex i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid p_impbid f0_oprabid f1_oprabid f2_oprabid f3_oprabid i0_oprabid a_df-oprab i0_oprabid a_sup_set_class f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop a_wceq f0_oprabid a_wa f3_oprabid a_wex f2_oprabid a_wex f1_oprabid a_wex f0_oprabid i0_oprabid f1_oprabid a_sup_set_class f2_oprabid a_sup_set_class a_cop f3_oprabid a_sup_set_class a_cop f0_oprabid f1_oprabid f2_oprabid f3_oprabid a_coprab p_elab2 $.
$}

$(The result of an operation is a set.  (Contributed by NM, 13-Mar-1995.) $)

${
	$v A B F  $.
	f0_ovex $f class A $.
	f1_ovex $f class B $.
	f2_ovex $f class F $.
	p_ovex $p |- ( A F B ) e. _V $= f0_ovex f1_ovex f2_ovex a_df-ov f0_ovex f1_ovex a_cop f2_ovex p_fvex f0_ovex f1_ovex f2_ovex a_co f0_ovex f1_ovex a_cop f2_ovex a_cfv a_cvv p_eqeltri $.
$}

$(The result of an operation value is always a subset of the union of the
     range.  (Contributed by Mario Carneiro, 12-Jan-2017.) $)

${
	$v F X Y  $.
	f0_ovssunirn $f class F $.
	f1_ovssunirn $f class X $.
	f2_ovssunirn $f class Y $.
	p_ovssunirn $p |- ( X F Y ) C_ U. ran F $= f1_ovssunirn f2_ovssunirn f0_ovssunirn a_df-ov f0_ovssunirn f1_ovssunirn f2_ovssunirn a_cop p_fvssunirn f1_ovssunirn f2_ovssunirn f0_ovssunirn a_co f1_ovssunirn f2_ovssunirn a_cop f0_ovssunirn a_cfv f0_ovssunirn a_crn a_cuni p_eqsstri $.
$}

$(The value of an operation when the one of the arguments is a proper
       class.  Note: this theorem is dependent on our particular definitions of
       operation value, function value, and ordered pair.  (Contributed by
       Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B F  $.
	f0_ovprc $f class A $.
	f1_ovprc $f class B $.
	f2_ovprc $f class F $.
	e0_ovprc $e |- Rel dom F $.
	p_ovprc $p |- ( -. ( A e. _V /\ B e. _V ) -> ( A F B ) = (/) ) $= f0_ovprc f1_ovprc f2_ovprc a_df-ov f0_ovprc f1_ovprc f2_ovprc a_cdm a_df-br e0_ovprc f0_ovprc f1_ovprc f2_ovprc a_cdm p_brrelex12 f2_ovprc a_cdm a_wrel f0_ovprc f1_ovprc f2_ovprc a_cdm a_wbr f0_ovprc a_cvv a_wcel f1_ovprc a_cvv a_wcel a_wa p_mpan f0_ovprc f1_ovprc a_cop f2_ovprc a_cdm a_wcel f0_ovprc f1_ovprc f2_ovprc a_cdm a_wbr f0_ovprc a_cvv a_wcel f1_ovprc a_cvv a_wcel a_wa p_sylbir f0_ovprc f1_ovprc a_cop f2_ovprc a_cdm a_wcel f0_ovprc a_cvv a_wcel f1_ovprc a_cvv a_wcel a_wa p_con3i f0_ovprc f1_ovprc a_cop f2_ovprc p_ndmfv f0_ovprc a_cvv a_wcel f1_ovprc a_cvv a_wcel a_wa a_wn f0_ovprc f1_ovprc a_cop f2_ovprc a_cdm a_wcel a_wn f0_ovprc f1_ovprc a_cop f2_ovprc a_cfv a_c0 a_wceq p_syl f0_ovprc a_cvv a_wcel f1_ovprc a_cvv a_wcel a_wa a_wn f0_ovprc f1_ovprc f2_ovprc a_co f0_ovprc f1_ovprc a_cop f2_ovprc a_cfv a_c0 p_syl5eq $.
$}

$(The value of an operation when the first argument is a proper class.
       (Contributed by NM, 16-Jun-2004.) $)

${
	$v A B F  $.
	f0_ovprc1 $f class A $.
	f1_ovprc1 $f class B $.
	f2_ovprc1 $f class F $.
	e0_ovprc1 $e |- Rel dom F $.
	p_ovprc1 $p |- ( -. A e. _V -> ( A F B ) = (/) ) $= f0_ovprc1 a_cvv a_wcel f1_ovprc1 a_cvv a_wcel p_simpl f0_ovprc1 a_cvv a_wcel f1_ovprc1 a_cvv a_wcel a_wa f0_ovprc1 a_cvv a_wcel p_con3i e0_ovprc1 f0_ovprc1 f1_ovprc1 f2_ovprc1 p_ovprc f0_ovprc1 a_cvv a_wcel a_wn f0_ovprc1 a_cvv a_wcel f1_ovprc1 a_cvv a_wcel a_wa a_wn f0_ovprc1 f1_ovprc1 f2_ovprc1 a_co a_c0 a_wceq p_syl $.
$}

$(The value of an operation when the second argument is a proper class.
       (Contributed by Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B F  $.
	f0_ovprc2 $f class A $.
	f1_ovprc2 $f class B $.
	f2_ovprc2 $f class F $.
	e0_ovprc2 $e |- Rel dom F $.
	p_ovprc2 $p |- ( -. B e. _V -> ( A F B ) = (/) ) $= f0_ovprc2 a_cvv a_wcel f1_ovprc2 a_cvv a_wcel p_simpr f0_ovprc2 a_cvv a_wcel f1_ovprc2 a_cvv a_wcel a_wa f1_ovprc2 a_cvv a_wcel p_con3i e0_ovprc2 f0_ovprc2 f1_ovprc2 f2_ovprc2 p_ovprc f1_ovprc2 a_cvv a_wcel a_wn f0_ovprc2 a_cvv a_wcel f1_ovprc2 a_cvv a_wcel a_wa a_wn f0_ovprc2 f1_ovprc2 f2_ovprc2 a_co a_c0 a_wceq p_syl $.
$}

$(Reverse closure for an operation value.  (Contributed by Mario Carneiro,
       5-May-2015.) $)

${
	$v A B C F  $.
	f0_ovrcl $f class A $.
	f1_ovrcl $f class B $.
	f2_ovrcl $f class C $.
	f3_ovrcl $f class F $.
	e0_ovrcl $e |- Rel dom F $.
	p_ovrcl $p |- ( C e. ( A F B ) -> ( A e. _V /\ B e. _V ) ) $= f0_ovrcl f1_ovrcl f3_ovrcl a_co f2_ovrcl p_n0i e0_ovrcl f0_ovrcl f1_ovrcl f3_ovrcl p_ovprc f2_ovrcl f0_ovrcl f1_ovrcl f3_ovrcl a_co a_wcel f0_ovrcl f1_ovrcl f3_ovrcl a_co a_c0 a_wceq f0_ovrcl a_cvv a_wcel f1_ovrcl a_cvv a_wcel a_wa p_nsyl2 $.
$}

$(Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.)  (Proof shortened by Mario Carneiro, 5-Dec-2016.) $)

${
	$v x A B C D F  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	$d y D  $.
	$d y F  $.
	$d x y  $.
	f0_csbovg $f set x $.
	f1_csbovg $f class A $.
	f2_csbovg $f class B $.
	f3_csbovg $f class C $.
	f4_csbovg $f class D $.
	f5_csbovg $f class F $.
	i0_csbovg $f set y $.
	p_csbovg $p |- ( A e. D -> [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B [_ A / x ]_ F [_ A / x ]_ C ) ) $= f0_csbovg i0_csbovg a_sup_set_class f1_csbovg f2_csbovg f3_csbovg f5_csbovg a_co p_csbeq1 f0_csbovg i0_csbovg a_sup_set_class f1_csbovg f5_csbovg p_csbeq1 f0_csbovg i0_csbovg a_sup_set_class f1_csbovg f2_csbovg p_csbeq1 f0_csbovg i0_csbovg a_sup_set_class f1_csbovg f3_csbovg p_csbeq1 i0_csbovg a_sup_set_class f1_csbovg a_wceq f0_csbovg i0_csbovg a_sup_set_class f2_csbovg a_csb f0_csbovg f1_csbovg f2_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f3_csbovg a_csb f0_csbovg f1_csbovg f3_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f5_csbovg a_csb f0_csbovg f1_csbovg f5_csbovg a_csb p_oveq123d i0_csbovg a_sup_set_class f1_csbovg a_wceq f0_csbovg i0_csbovg a_sup_set_class f2_csbovg f3_csbovg f5_csbovg a_co a_csb f0_csbovg f1_csbovg f2_csbovg f3_csbovg f5_csbovg a_co a_csb f0_csbovg i0_csbovg a_sup_set_class f2_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f3_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f5_csbovg a_csb a_co f0_csbovg f1_csbovg f2_csbovg a_csb f0_csbovg f1_csbovg f3_csbovg a_csb f0_csbovg f1_csbovg f5_csbovg a_csb a_co p_eqeq12d i0_csbovg p_vex f0_csbovg i0_csbovg a_sup_set_class f2_csbovg p_nfcsb1v f0_csbovg i0_csbovg a_sup_set_class f5_csbovg p_nfcsb1v f0_csbovg i0_csbovg a_sup_set_class f3_csbovg p_nfcsb1v f0_csbovg f0_csbovg i0_csbovg a_sup_set_class f2_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f3_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f5_csbovg a_csb p_nfov f0_csbovg i0_csbovg a_sup_set_class f5_csbovg p_csbeq1a f0_csbovg i0_csbovg a_sup_set_class f2_csbovg p_csbeq1a f0_csbovg i0_csbovg a_sup_set_class f3_csbovg p_csbeq1a f0_csbovg a_sup_set_class i0_csbovg a_sup_set_class a_wceq f2_csbovg f0_csbovg i0_csbovg a_sup_set_class f2_csbovg a_csb f3_csbovg f0_csbovg i0_csbovg a_sup_set_class f3_csbovg a_csb f5_csbovg f0_csbovg i0_csbovg a_sup_set_class f5_csbovg a_csb p_oveq123d f0_csbovg i0_csbovg a_sup_set_class f2_csbovg f3_csbovg f5_csbovg a_co f0_csbovg i0_csbovg a_sup_set_class f2_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f3_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f5_csbovg a_csb a_co p_csbief f0_csbovg i0_csbovg a_sup_set_class f2_csbovg f3_csbovg f5_csbovg a_co a_csb f0_csbovg i0_csbovg a_sup_set_class f2_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f3_csbovg a_csb f0_csbovg i0_csbovg a_sup_set_class f5_csbovg a_csb a_co a_wceq f0_csbovg f1_csbovg f2_csbovg f3_csbovg f5_csbovg a_co a_csb f0_csbovg f1_csbovg f2_csbovg a_csb f0_csbovg f1_csbovg f3_csbovg a_csb f0_csbovg f1_csbovg f5_csbovg a_csb a_co a_wceq i0_csbovg f1_csbovg f4_csbovg p_vtoclg $.
$}

$(Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) $)

${
	$v x A B C D F  $.
	$d A  $.
	$d C  $.
	$d D  $.
	$d x F  $.
	f0_csbov12g $f set x $.
	f1_csbov12g $f class A $.
	f2_csbov12g $f class B $.
	f3_csbov12g $f class C $.
	f4_csbov12g $f class D $.
	f5_csbov12g $f class F $.
	p_csbov12g $p |- ( A e. D -> [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B F [_ A / x ]_ C ) ) $= f0_csbov12g f1_csbov12g f2_csbov12g f3_csbov12g f4_csbov12g f5_csbov12g p_csbovg f0_csbov12g f1_csbov12g f5_csbov12g f4_csbov12g p_csbconstg f1_csbov12g f4_csbov12g a_wcel f0_csbov12g f1_csbov12g f5_csbov12g a_csb f5_csbov12g f0_csbov12g f1_csbov12g f2_csbov12g a_csb f0_csbov12g f1_csbov12g f3_csbov12g a_csb p_oveqd f1_csbov12g f4_csbov12g a_wcel f0_csbov12g f1_csbov12g f2_csbov12g f3_csbov12g f5_csbov12g a_co a_csb f0_csbov12g f1_csbov12g f2_csbov12g a_csb f0_csbov12g f1_csbov12g f3_csbov12g a_csb f0_csbov12g f1_csbov12g f5_csbov12g a_csb a_co f0_csbov12g f1_csbov12g f2_csbov12g a_csb f0_csbov12g f1_csbov12g f3_csbov12g a_csb f5_csbov12g a_co p_eqtrd $.
$}

$(Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) $)

${
	$v x A B C D F  $.
	$d A  $.
	$d x C  $.
	$d D  $.
	$d x F  $.
	f0_csbov1g $f set x $.
	f1_csbov1g $f class A $.
	f2_csbov1g $f class B $.
	f3_csbov1g $f class C $.
	f4_csbov1g $f class D $.
	f5_csbov1g $f class F $.
	p_csbov1g $p |- ( A e. D -> [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B F C ) ) $= f0_csbov1g f1_csbov1g f2_csbov1g f3_csbov1g f4_csbov1g f5_csbov1g p_csbov12g f0_csbov1g f1_csbov1g f3_csbov1g f4_csbov1g p_csbconstg f1_csbov1g f4_csbov1g a_wcel f0_csbov1g f1_csbov1g f3_csbov1g a_csb f3_csbov1g f0_csbov1g f1_csbov1g f2_csbov1g a_csb f5_csbov1g p_oveq2d f1_csbov1g f4_csbov1g a_wcel f0_csbov1g f1_csbov1g f2_csbov1g f3_csbov1g f5_csbov1g a_co a_csb f0_csbov1g f1_csbov1g f2_csbov1g a_csb f0_csbov1g f1_csbov1g f3_csbov1g a_csb f5_csbov1g a_co f0_csbov1g f1_csbov1g f2_csbov1g a_csb f3_csbov1g f5_csbov1g a_co p_eqtrd $.
$}

$(Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) $)

${
	$v x A B C D F  $.
	$d A  $.
	$d x B  $.
	$d D  $.
	$d x F  $.
	f0_csbov2g $f set x $.
	f1_csbov2g $f class A $.
	f2_csbov2g $f class B $.
	f3_csbov2g $f class C $.
	f4_csbov2g $f class D $.
	f5_csbov2g $f class F $.
	p_csbov2g $p |- ( A e. D -> [_ A / x ]_ ( B F C ) = ( B F [_ A / x ]_ C ) ) $= f0_csbov2g f1_csbov2g f2_csbov2g f3_csbov2g f4_csbov2g f5_csbov2g p_csbov12g f0_csbov2g f1_csbov2g f2_csbov2g f4_csbov2g p_csbconstg f1_csbov2g f4_csbov2g a_wcel f0_csbov2g f1_csbov2g f2_csbov2g a_csb f2_csbov2g f0_csbov2g f1_csbov2g f3_csbov2g a_csb f5_csbov2g p_oveq1d f1_csbov2g f4_csbov2g a_wcel f0_csbov2g f1_csbov2g f2_csbov2g f3_csbov2g f5_csbov2g a_co a_csb f0_csbov2g f1_csbov2g f2_csbov2g a_csb f0_csbov2g f1_csbov2g f3_csbov2g a_csb f5_csbov2g a_co f2_csbov2g f0_csbov2g f1_csbov2g f3_csbov2g a_csb f5_csbov2g a_co p_eqtrd $.
$}

$(A frequently used special case of ~ rspc2ev for operation values.
       (Contributed by NM, 21-Mar-2007.) $)

${
	$v x y A B C D S F  $.
	$d x A  $.
	$d x y B  $.
	$d x y C  $.
	$d y D  $.
	$d x y F  $.
	$d x y S  $.
	f0_rspceov $f set x $.
	f1_rspceov $f set y $.
	f2_rspceov $f class A $.
	f3_rspceov $f class B $.
	f4_rspceov $f class C $.
	f5_rspceov $f class D $.
	f6_rspceov $f class S $.
	f7_rspceov $f class F $.
	p_rspceov $p |- ( ( C e. A /\ D e. B /\ S = ( C F D ) ) -> E. x e. A E. y e. B S = ( x F y ) ) $= f0_rspceov a_sup_set_class f4_rspceov f1_rspceov a_sup_set_class f7_rspceov p_oveq1 f0_rspceov a_sup_set_class f4_rspceov a_wceq f0_rspceov a_sup_set_class f1_rspceov a_sup_set_class f7_rspceov a_co f4_rspceov f1_rspceov a_sup_set_class f7_rspceov a_co f6_rspceov p_eqeq2d f1_rspceov a_sup_set_class f5_rspceov f4_rspceov f7_rspceov p_oveq2 f1_rspceov a_sup_set_class f5_rspceov a_wceq f4_rspceov f1_rspceov a_sup_set_class f7_rspceov a_co f4_rspceov f5_rspceov f7_rspceov a_co f6_rspceov p_eqeq2d f6_rspceov f0_rspceov a_sup_set_class f1_rspceov a_sup_set_class f7_rspceov a_co a_wceq f6_rspceov f4_rspceov f5_rspceov f7_rspceov a_co a_wceq f6_rspceov f4_rspceov f1_rspceov a_sup_set_class f7_rspceov a_co a_wceq f0_rspceov f1_rspceov f4_rspceov f5_rspceov f2_rspceov f3_rspceov p_rspc2ev $.
$}

$(Equivalence of operation value and ordered triple membership, analogous
       to ~ fnopfvb .  (Contributed by NM, 17-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)

${
	$v A B C D R F  $.
	f0_fnotovb $f class A $.
	f1_fnotovb $f class B $.
	f2_fnotovb $f class C $.
	f3_fnotovb $f class D $.
	f4_fnotovb $f class R $.
	f5_fnotovb $f class F $.
	p_fnotovb $p |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) -> ( ( C F D ) = R <-> <. C , D , R >. e. F ) ) $= f2_fnotovb f3_fnotovb f0_fnotovb f1_fnotovb p_opelxpi f0_fnotovb f1_fnotovb a_cxp f2_fnotovb f3_fnotovb a_cop f4_fnotovb f5_fnotovb p_fnopfvb f2_fnotovb f0_fnotovb a_wcel f3_fnotovb f1_fnotovb a_wcel a_wa f5_fnotovb f0_fnotovb f1_fnotovb a_cxp a_wfn f2_fnotovb f3_fnotovb a_cop f0_fnotovb f1_fnotovb a_cxp a_wcel f2_fnotovb f3_fnotovb a_cop f5_fnotovb a_cfv f4_fnotovb a_wceq f2_fnotovb f3_fnotovb a_cop f4_fnotovb a_cop f5_fnotovb a_wcel a_wb p_sylan2 f5_fnotovb f0_fnotovb f1_fnotovb a_cxp a_wfn f2_fnotovb f0_fnotovb a_wcel f3_fnotovb f1_fnotovb a_wcel f2_fnotovb f3_fnotovb a_cop f5_fnotovb a_cfv f4_fnotovb a_wceq f2_fnotovb f3_fnotovb a_cop f4_fnotovb a_cop f5_fnotovb a_wcel a_wb p_3impb f2_fnotovb f3_fnotovb f5_fnotovb a_df-ov f2_fnotovb f3_fnotovb f5_fnotovb a_co f2_fnotovb f3_fnotovb a_cop f5_fnotovb a_cfv f4_fnotovb p_eqeq1i f2_fnotovb f3_fnotovb f4_fnotovb a_df-ot f2_fnotovb f3_fnotovb f4_fnotovb a_cotp f2_fnotovb f3_fnotovb a_cop f4_fnotovb a_cop f5_fnotovb p_eleq1i f5_fnotovb f0_fnotovb f1_fnotovb a_cxp a_wfn f2_fnotovb f0_fnotovb a_wcel f3_fnotovb f1_fnotovb a_wcel a_w3a f2_fnotovb f3_fnotovb a_cop f5_fnotovb a_cfv f4_fnotovb a_wceq f2_fnotovb f3_fnotovb a_cop f4_fnotovb a_cop f5_fnotovb a_wcel f2_fnotovb f3_fnotovb f5_fnotovb a_co f4_fnotovb a_wceq f2_fnotovb f3_fnotovb f4_fnotovb a_cotp f5_fnotovb a_wcel p_3bitr4g $.
$}

$(Class abstraction for operations in terms of class abstraction of
       ordered pairs.  (Contributed by NM, 12-Mar-1995.) $)

${
	$v ph x y z w  $.
	$d x z w v  $.
	$d y z w v  $.
	$d w ph v  $.
	f0_dfoprab2 $f wff ph $.
	f1_dfoprab2 $f set x $.
	f2_dfoprab2 $f set y $.
	f3_dfoprab2 $f set z $.
	f4_dfoprab2 $f set w $.
	i0_dfoprab2 $f set v $.
	p_dfoprab2 $p |- { <. <. x , y >. , z >. | ph } = { <. w , z >. | E. x E. y ( w = <. x , y >. /\ ph ) } $= i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex f3_dfoprab2 f4_dfoprab2 p_excom i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f3_dfoprab2 f4_dfoprab2 f1_dfoprab2 f2_dfoprab2 p_exrot4 f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class p_opeq1 f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop i0_dfoprab2 a_sup_set_class p_eqeq2d f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq p_pm5.32ri i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq a_wa i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq a_wa f0_dfoprab2 p_anbi1i i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 p_anass i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 p_an32 i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq a_wa f0_dfoprab2 a_wa i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq a_wa f0_dfoprab2 a_wa i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq a_wa p_3bitr3i i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq a_wa f4_dfoprab2 p_exbii f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class p_opex f4_dfoprab2 f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop p_isseti i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 p_19.42v i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq a_wa f4_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_wex p_mpbiran2 i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f4_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq a_wa f4_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa p_bitri i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f4_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f1_dfoprab2 f2_dfoprab2 f3_dfoprab2 p_3exbii i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex f4_dfoprab2 a_wex f3_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f4_dfoprab2 a_wex f3_dfoprab2 a_wex f2_dfoprab2 a_wex f1_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f3_dfoprab2 a_wex f2_dfoprab2 a_wex f1_dfoprab2 a_wex p_bitri i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f1_dfoprab2 f2_dfoprab2 p_19.42vv i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex a_wa f4_dfoprab2 f3_dfoprab2 p_2exbii i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex f4_dfoprab2 a_wex f3_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex f3_dfoprab2 a_wex f4_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f3_dfoprab2 a_wex f2_dfoprab2 a_wex f1_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex a_wa f3_dfoprab2 a_wex f4_dfoprab2 a_wex p_3bitr3i i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f3_dfoprab2 a_wex f2_dfoprab2 a_wex f1_dfoprab2 a_wex i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex a_wa f3_dfoprab2 a_wex f4_dfoprab2 a_wex i0_dfoprab2 p_abbii f0_dfoprab2 f1_dfoprab2 f2_dfoprab2 f3_dfoprab2 i0_dfoprab2 a_df-oprab f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex f4_dfoprab2 f3_dfoprab2 i0_dfoprab2 a_df-opab i0_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop f3_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f3_dfoprab2 a_wex f2_dfoprab2 a_wex f1_dfoprab2 a_wex i0_dfoprab2 a_cab i0_dfoprab2 a_sup_set_class f4_dfoprab2 a_sup_set_class f3_dfoprab2 a_sup_set_class a_cop a_wceq f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex a_wa f3_dfoprab2 a_wex f4_dfoprab2 a_wex i0_dfoprab2 a_cab f0_dfoprab2 f1_dfoprab2 f2_dfoprab2 f3_dfoprab2 a_coprab f4_dfoprab2 a_sup_set_class f1_dfoprab2 a_sup_set_class f2_dfoprab2 a_sup_set_class a_cop a_wceq f0_dfoprab2 a_wa f2_dfoprab2 a_wex f1_dfoprab2 a_wex f4_dfoprab2 f3_dfoprab2 a_copab p_3eqtr4i $.
$}

$(An operation class abstraction is a relation.  (Contributed by NM,
       16-Jun-2004.) $)

${
	$v ph x y z  $.
	$d x z w  $.
	$d y z w  $.
	$d w ph  $.
	f0_reloprab $f wff ph $.
	f1_reloprab $f set x $.
	f2_reloprab $f set y $.
	f3_reloprab $f set z $.
	i0_reloprab $f set w $.
	p_reloprab $p |- Rel { <. <. x , y >. , z >. | ph } $= f0_reloprab f1_reloprab f2_reloprab f3_reloprab i0_reloprab p_dfoprab2 i0_reloprab a_sup_set_class f1_reloprab a_sup_set_class f2_reloprab a_sup_set_class a_cop a_wceq f0_reloprab a_wa f2_reloprab a_wex f1_reloprab a_wex i0_reloprab f3_reloprab f0_reloprab f1_reloprab f2_reloprab f3_reloprab a_coprab p_relopabi $.
$}

$(@{
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
$)

$(The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 25-Apr-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) $)

${
	$v ph x y z  $.
	$d w x  $.
	$d w y  $.
	$d w z  $.
	$d w ph  $.
	f0_nfoprab1 $f wff ph $.
	f1_nfoprab1 $f set x $.
	f2_nfoprab1 $f set y $.
	f3_nfoprab1 $f set z $.
	i0_nfoprab1 $f set w $.
	p_nfoprab1 $p |- F/_ x { <. <. x , y >. , z >. | ph } $= f0_nfoprab1 f1_nfoprab1 f2_nfoprab1 f3_nfoprab1 i0_nfoprab1 a_df-oprab i0_nfoprab1 a_sup_set_class f1_nfoprab1 a_sup_set_class f2_nfoprab1 a_sup_set_class a_cop f3_nfoprab1 a_sup_set_class a_cop a_wceq f0_nfoprab1 a_wa f3_nfoprab1 a_wex f2_nfoprab1 a_wex f1_nfoprab1 p_nfe1 i0_nfoprab1 a_sup_set_class f1_nfoprab1 a_sup_set_class f2_nfoprab1 a_sup_set_class a_cop f3_nfoprab1 a_sup_set_class a_cop a_wceq f0_nfoprab1 a_wa f3_nfoprab1 a_wex f2_nfoprab1 a_wex f1_nfoprab1 a_wex f1_nfoprab1 i0_nfoprab1 p_nfab f1_nfoprab1 f0_nfoprab1 f1_nfoprab1 f2_nfoprab1 f3_nfoprab1 a_coprab i0_nfoprab1 a_sup_set_class f1_nfoprab1 a_sup_set_class f2_nfoprab1 a_sup_set_class a_cop f3_nfoprab1 a_sup_set_class a_cop a_wceq f0_nfoprab1 a_wa f3_nfoprab1 a_wex f2_nfoprab1 a_wex f1_nfoprab1 a_wex i0_nfoprab1 a_cab p_nfcxfr $.
$}

$(The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 25-Apr-1995.)  (Revised by David Abernethy,
       30-Jul-2012.) $)

${
	$v ph x y z  $.
	$d w x  $.
	$d w y  $.
	$d w z  $.
	$d w ph  $.
	f0_nfoprab2 $f wff ph $.
	f1_nfoprab2 $f set x $.
	f2_nfoprab2 $f set y $.
	f3_nfoprab2 $f set z $.
	i0_nfoprab2 $f set w $.
	p_nfoprab2 $p |- F/_ y { <. <. x , y >. , z >. | ph } $= f0_nfoprab2 f1_nfoprab2 f2_nfoprab2 f3_nfoprab2 i0_nfoprab2 a_df-oprab i0_nfoprab2 a_sup_set_class f1_nfoprab2 a_sup_set_class f2_nfoprab2 a_sup_set_class a_cop f3_nfoprab2 a_sup_set_class a_cop a_wceq f0_nfoprab2 a_wa f3_nfoprab2 a_wex f2_nfoprab2 p_nfe1 i0_nfoprab2 a_sup_set_class f1_nfoprab2 a_sup_set_class f2_nfoprab2 a_sup_set_class a_cop f3_nfoprab2 a_sup_set_class a_cop a_wceq f0_nfoprab2 a_wa f3_nfoprab2 a_wex f2_nfoprab2 a_wex f2_nfoprab2 f1_nfoprab2 p_nfex i0_nfoprab2 a_sup_set_class f1_nfoprab2 a_sup_set_class f2_nfoprab2 a_sup_set_class a_cop f3_nfoprab2 a_sup_set_class a_cop a_wceq f0_nfoprab2 a_wa f3_nfoprab2 a_wex f2_nfoprab2 a_wex f1_nfoprab2 a_wex f2_nfoprab2 i0_nfoprab2 p_nfab f2_nfoprab2 f0_nfoprab2 f1_nfoprab2 f2_nfoprab2 f3_nfoprab2 a_coprab i0_nfoprab2 a_sup_set_class f1_nfoprab2 a_sup_set_class f2_nfoprab2 a_sup_set_class a_cop f3_nfoprab2 a_sup_set_class a_cop a_wceq f0_nfoprab2 a_wa f3_nfoprab2 a_wex f2_nfoprab2 a_wex f1_nfoprab2 a_wex i0_nfoprab2 a_cab p_nfcxfr $.
$}

$(The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 22-Aug-2013.) $)

${
	$v ph x y z  $.
	$d w x  $.
	$d w y  $.
	$d w z  $.
	$d w ph  $.
	f0_nfoprab3 $f wff ph $.
	f1_nfoprab3 $f set x $.
	f2_nfoprab3 $f set y $.
	f3_nfoprab3 $f set z $.
	i0_nfoprab3 $f set w $.
	p_nfoprab3 $p |- F/_ z { <. <. x , y >. , z >. | ph } $= f0_nfoprab3 f1_nfoprab3 f2_nfoprab3 f3_nfoprab3 i0_nfoprab3 a_df-oprab i0_nfoprab3 a_sup_set_class f1_nfoprab3 a_sup_set_class f2_nfoprab3 a_sup_set_class a_cop f3_nfoprab3 a_sup_set_class a_cop a_wceq f0_nfoprab3 a_wa f3_nfoprab3 p_nfe1 i0_nfoprab3 a_sup_set_class f1_nfoprab3 a_sup_set_class f2_nfoprab3 a_sup_set_class a_cop f3_nfoprab3 a_sup_set_class a_cop a_wceq f0_nfoprab3 a_wa f3_nfoprab3 a_wex f3_nfoprab3 f2_nfoprab3 p_nfex i0_nfoprab3 a_sup_set_class f1_nfoprab3 a_sup_set_class f2_nfoprab3 a_sup_set_class a_cop f3_nfoprab3 a_sup_set_class a_cop a_wceq f0_nfoprab3 a_wa f3_nfoprab3 a_wex f2_nfoprab3 a_wex f3_nfoprab3 f1_nfoprab3 p_nfex i0_nfoprab3 a_sup_set_class f1_nfoprab3 a_sup_set_class f2_nfoprab3 a_sup_set_class a_cop f3_nfoprab3 a_sup_set_class a_cop a_wceq f0_nfoprab3 a_wa f3_nfoprab3 a_wex f2_nfoprab3 a_wex f1_nfoprab3 a_wex f3_nfoprab3 i0_nfoprab3 p_nfab f3_nfoprab3 f0_nfoprab3 f1_nfoprab3 f2_nfoprab3 f3_nfoprab3 a_coprab i0_nfoprab3 a_sup_set_class f1_nfoprab3 a_sup_set_class f2_nfoprab3 a_sup_set_class a_cop f3_nfoprab3 a_sup_set_class a_cop a_wceq f0_nfoprab3 a_wa f3_nfoprab3 a_wex f2_nfoprab3 a_wex f1_nfoprab3 a_wex i0_nfoprab3 a_cab p_nfcxfr $.
$}

$(Bound-variable hypothesis builder for an operation class abstraction.
       (Contributed by NM, 22-Aug-2013.) $)

${
	$v ph x y z w  $.
	$d v w x  $.
	$d v w y  $.
	$d v w z  $.
	$d v ph  $.
	f0_nfoprab $f wff ph $.
	f1_nfoprab $f set x $.
	f2_nfoprab $f set y $.
	f3_nfoprab $f set z $.
	f4_nfoprab $f set w $.
	i0_nfoprab $f set v $.
	e0_nfoprab $e |- F/ w ph $.
	p_nfoprab $p |- F/_ w { <. <. x , y >. , z >. | ph } $= f0_nfoprab f1_nfoprab f2_nfoprab f3_nfoprab i0_nfoprab a_df-oprab i0_nfoprab a_sup_set_class f1_nfoprab a_sup_set_class f2_nfoprab a_sup_set_class a_cop f3_nfoprab a_sup_set_class a_cop a_wceq f4_nfoprab p_nfv e0_nfoprab i0_nfoprab a_sup_set_class f1_nfoprab a_sup_set_class f2_nfoprab a_sup_set_class a_cop f3_nfoprab a_sup_set_class a_cop a_wceq f0_nfoprab f4_nfoprab p_nfan i0_nfoprab a_sup_set_class f1_nfoprab a_sup_set_class f2_nfoprab a_sup_set_class a_cop f3_nfoprab a_sup_set_class a_cop a_wceq f0_nfoprab a_wa f4_nfoprab f3_nfoprab p_nfex i0_nfoprab a_sup_set_class f1_nfoprab a_sup_set_class f2_nfoprab a_sup_set_class a_cop f3_nfoprab a_sup_set_class a_cop a_wceq f0_nfoprab a_wa f3_nfoprab a_wex f4_nfoprab f2_nfoprab p_nfex i0_nfoprab a_sup_set_class f1_nfoprab a_sup_set_class f2_nfoprab a_sup_set_class a_cop f3_nfoprab a_sup_set_class a_cop a_wceq f0_nfoprab a_wa f3_nfoprab a_wex f2_nfoprab a_wex f4_nfoprab f1_nfoprab p_nfex i0_nfoprab a_sup_set_class f1_nfoprab a_sup_set_class f2_nfoprab a_sup_set_class a_cop f3_nfoprab a_sup_set_class a_cop a_wceq f0_nfoprab a_wa f3_nfoprab a_wex f2_nfoprab a_wex f1_nfoprab a_wex f4_nfoprab i0_nfoprab p_nfab f4_nfoprab f0_nfoprab f1_nfoprab f2_nfoprab f3_nfoprab a_coprab i0_nfoprab a_sup_set_class f1_nfoprab a_sup_set_class f2_nfoprab a_sup_set_class a_cop f3_nfoprab a_sup_set_class a_cop a_wceq f0_nfoprab a_wa f3_nfoprab a_wex f2_nfoprab a_wex f1_nfoprab a_wex i0_nfoprab a_cab p_nfcxfr $.
$}

$(Equivalent wff's yield equal operation class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.)  (Revised by Mario Carneiro,
       24-Jun-2014.) $)

${
	$v ph ps ch x y z  $.
	$d x z w  $.
	$d y z w  $.
	$d w ph  $.
	$d w ps  $.
	$d w ch  $.
	f0_oprabbid $f wff ph $.
	f1_oprabbid $f wff ps $.
	f2_oprabbid $f wff ch $.
	f3_oprabbid $f set x $.
	f4_oprabbid $f set y $.
	f5_oprabbid $f set z $.
	i0_oprabbid $f set w $.
	e0_oprabbid $e |- F/ x ph $.
	e1_oprabbid $e |- F/ y ph $.
	e2_oprabbid $e |- F/ z ph $.
	e3_oprabbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_oprabbid $p |- ( ph -> { <. <. x , y >. , z >. | ps } = { <. <. x , y >. , z >. | ch } ) $= e0_oprabbid e1_oprabbid e2_oprabbid e3_oprabbid f0_oprabbid f1_oprabbid f2_oprabbid i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq p_anbi2d f0_oprabbid i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f1_oprabbid a_wa i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f2_oprabbid a_wa f5_oprabbid p_exbid f0_oprabbid i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f1_oprabbid a_wa f5_oprabbid a_wex i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f2_oprabbid a_wa f5_oprabbid a_wex f4_oprabbid p_exbid f0_oprabbid i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f1_oprabbid a_wa f5_oprabbid a_wex f4_oprabbid a_wex i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f2_oprabbid a_wa f5_oprabbid a_wex f4_oprabbid a_wex f3_oprabbid p_exbid f0_oprabbid i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f1_oprabbid a_wa f5_oprabbid a_wex f4_oprabbid a_wex f3_oprabbid a_wex i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f2_oprabbid a_wa f5_oprabbid a_wex f4_oprabbid a_wex f3_oprabbid a_wex i0_oprabbid p_abbidv f1_oprabbid f3_oprabbid f4_oprabbid f5_oprabbid i0_oprabbid a_df-oprab f2_oprabbid f3_oprabbid f4_oprabbid f5_oprabbid i0_oprabbid a_df-oprab f0_oprabbid i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f1_oprabbid a_wa f5_oprabbid a_wex f4_oprabbid a_wex f3_oprabbid a_wex i0_oprabbid a_cab i0_oprabbid a_sup_set_class f3_oprabbid a_sup_set_class f4_oprabbid a_sup_set_class a_cop f5_oprabbid a_sup_set_class a_cop a_wceq f2_oprabbid a_wa f5_oprabbid a_wex f4_oprabbid a_wex f3_oprabbid a_wex i0_oprabbid a_cab f1_oprabbid f3_oprabbid f4_oprabbid f5_oprabbid a_coprab f2_oprabbid f3_oprabbid f4_oprabbid f5_oprabbid a_coprab p_3eqtr4g $.
$}

$(Equivalent wff's yield equal operation class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.) $)

${
	$v ph ps ch x y z  $.
	$d x z ph  $.
	$d y z ph  $.
	$d ps  $.
	$d ch  $.
	f0_oprabbidv $f wff ph $.
	f1_oprabbidv $f wff ps $.
	f2_oprabbidv $f wff ch $.
	f3_oprabbidv $f set x $.
	f4_oprabbidv $f set y $.
	f5_oprabbidv $f set z $.
	e0_oprabbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_oprabbidv $p |- ( ph -> { <. <. x , y >. , z >. | ps } = { <. <. x , y >. , z >. | ch } ) $= f0_oprabbidv f3_oprabbidv p_nfv f0_oprabbidv f4_oprabbidv p_nfv f0_oprabbidv f5_oprabbidv p_nfv e0_oprabbidv f0_oprabbidv f1_oprabbidv f2_oprabbidv f3_oprabbidv f4_oprabbidv f5_oprabbidv p_oprabbid $.
$}

$(Equivalent wff's yield equal operation class abstractions.  (Contributed
       by NM, 28-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)

${
	$v ph ps x y z  $.
	$d x z w  $.
	$d y z w  $.
	$d w ph  $.
	$d w ps  $.
	f0_oprabbii $f wff ph $.
	f1_oprabbii $f wff ps $.
	f2_oprabbii $f set x $.
	f3_oprabbii $f set y $.
	f4_oprabbii $f set z $.
	i0_oprabbii $f set w $.
	e0_oprabbii $e |- ( ph <-> ps ) $.
	p_oprabbii $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ps } $= i0_oprabbii a_sup_set_class p_eqid e0_oprabbii f0_oprabbii f1_oprabbii a_wb i0_oprabbii a_sup_set_class i0_oprabbii a_sup_set_class a_wceq p_a1i i0_oprabbii a_sup_set_class i0_oprabbii a_sup_set_class a_wceq f0_oprabbii f1_oprabbii f2_oprabbii f3_oprabbii f4_oprabbii p_oprabbidv i0_oprabbii a_sup_set_class i0_oprabbii a_sup_set_class a_wceq f0_oprabbii f2_oprabbii f3_oprabbii f4_oprabbii a_coprab f1_oprabbii f2_oprabbii f3_oprabbii f4_oprabbii a_coprab a_wceq a_ax-mp $.
$}

$(Equivalence of ordered pair abstraction subclass and implication.
       Compare ~ ssopab2 .  (Contributed by FL, 6-Nov-2013.)  (Proof shortened
       by Mario Carneiro, 11-Dec-2016.) $)

${
	$v ph ps x y z  $.
	$d ph w  $.
	$d ps w  $.
	$d x w  $.
	$d y w  $.
	$d z w  $.
	f0_ssoprab2 $f wff ph $.
	f1_ssoprab2 $f wff ps $.
	f2_ssoprab2 $f set x $.
	f3_ssoprab2 $f set y $.
	f4_ssoprab2 $f set z $.
	i0_ssoprab2 $f set w $.
	p_ssoprab2 $p |- ( A. x A. y A. z ( ph -> ps ) -> { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } ) $= f0_ssoprab2 f1_ssoprab2 a_wi p_id f0_ssoprab2 f1_ssoprab2 a_wi f0_ssoprab2 f1_ssoprab2 i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq p_anim2d f0_ssoprab2 f1_ssoprab2 a_wi i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa a_wi f4_ssoprab2 p_alimi i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 p_exim f0_ssoprab2 f1_ssoprab2 a_wi f4_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa a_wi f4_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex a_wi p_syl f0_ssoprab2 f1_ssoprab2 a_wi f4_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex a_wi f3_ssoprab2 p_alimi i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 p_exim f0_ssoprab2 f1_ssoprab2 a_wi f4_ssoprab2 a_wal f3_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex a_wi f3_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex a_wi p_syl f0_ssoprab2 f1_ssoprab2 a_wi f4_ssoprab2 a_wal f3_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex a_wi f2_ssoprab2 p_alimi i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex f2_ssoprab2 p_exim f0_ssoprab2 f1_ssoprab2 a_wi f4_ssoprab2 a_wal f3_ssoprab2 a_wal f2_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex a_wi f2_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex f2_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex f2_ssoprab2 a_wex a_wi p_syl f0_ssoprab2 f1_ssoprab2 a_wi f4_ssoprab2 a_wal f3_ssoprab2 a_wal f2_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex f2_ssoprab2 a_wex i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex f2_ssoprab2 a_wex i0_ssoprab2 p_ss2abdv f0_ssoprab2 f2_ssoprab2 f3_ssoprab2 f4_ssoprab2 i0_ssoprab2 a_df-oprab f1_ssoprab2 f2_ssoprab2 f3_ssoprab2 f4_ssoprab2 i0_ssoprab2 a_df-oprab f0_ssoprab2 f1_ssoprab2 a_wi f4_ssoprab2 a_wal f3_ssoprab2 a_wal f2_ssoprab2 a_wal i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f0_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex f2_ssoprab2 a_wex i0_ssoprab2 a_cab i0_ssoprab2 a_sup_set_class f2_ssoprab2 a_sup_set_class f3_ssoprab2 a_sup_set_class a_cop f4_ssoprab2 a_sup_set_class a_cop a_wceq f1_ssoprab2 a_wa f4_ssoprab2 a_wex f3_ssoprab2 a_wex f2_ssoprab2 a_wex i0_ssoprab2 a_cab f0_ssoprab2 f2_ssoprab2 f3_ssoprab2 f4_ssoprab2 a_coprab f1_ssoprab2 f2_ssoprab2 f3_ssoprab2 f4_ssoprab2 a_coprab p_3sstr4g $.
$}

$(Equivalence of ordered pair abstraction subclass and implication.  Compare
     ~ ssopab2b .  (Contributed by FL, 6-Nov-2013.)  (Proof shortened by Mario
     Carneiro, 11-Dec-2016.) $)

${
	$v ph ps x y z  $.
	f0_ssoprab2b $f wff ph $.
	f1_ssoprab2b $f wff ps $.
	f2_ssoprab2b $f set x $.
	f3_ssoprab2b $f set y $.
	f4_ssoprab2b $f set z $.
	p_ssoprab2b $p |- ( { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } <-> A. x A. y A. z ( ph -> ps ) ) $= f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_nfoprab1 f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_nfoprab1 f2_ssoprab2b f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab p_nfss f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_nfoprab2 f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_nfoprab2 f3_ssoprab2b f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab p_nfss f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_nfoprab3 f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_nfoprab3 f4_ssoprab2b f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab p_nfss f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f2_ssoprab2b a_sup_set_class f3_ssoprab2b a_sup_set_class a_cop f4_ssoprab2b a_sup_set_class a_cop p_ssel f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_oprabid f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_oprabid f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab a_wss f2_ssoprab2b a_sup_set_class f3_ssoprab2b a_sup_set_class a_cop f4_ssoprab2b a_sup_set_class a_cop f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab a_wcel f2_ssoprab2b a_sup_set_class f3_ssoprab2b a_sup_set_class a_cop f4_ssoprab2b a_sup_set_class a_cop f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab a_wcel f0_ssoprab2b f1_ssoprab2b p_3imtr3g f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab a_wss f0_ssoprab2b f1_ssoprab2b a_wi f4_ssoprab2b p_alrimi f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab a_wss f0_ssoprab2b f1_ssoprab2b a_wi f4_ssoprab2b a_wal f3_ssoprab2b p_alrimi f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab a_wss f0_ssoprab2b f1_ssoprab2b a_wi f4_ssoprab2b a_wal f3_ssoprab2b a_wal f2_ssoprab2b p_alrimi f0_ssoprab2b f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b p_ssoprab2 f0_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab f1_ssoprab2b f2_ssoprab2b f3_ssoprab2b f4_ssoprab2b a_coprab a_wss f0_ssoprab2b f1_ssoprab2b a_wi f4_ssoprab2b a_wal f3_ssoprab2b a_wal f2_ssoprab2b a_wal p_impbii $.
$}

$(Equivalence of ordered pair abstraction subclass and biconditional.
     Compare ~ eqopab2b .  (Contributed by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps x y z  $.
	f0_eqoprab2b $f wff ph $.
	f1_eqoprab2b $f wff ps $.
	f2_eqoprab2b $f set x $.
	f3_eqoprab2b $f set y $.
	f4_eqoprab2b $f set z $.
	p_eqoprab2b $p |- ( { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ps } <-> A. x A. y A. z ( ph <-> ps ) ) $= f0_eqoprab2b f1_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b p_ssoprab2b f1_eqoprab2b f0_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b p_ssoprab2b f0_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab f1_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab a_wss f0_eqoprab2b f1_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b a_wal f1_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab f0_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab a_wss f1_eqoprab2b f0_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b a_wal p_anbi12i f0_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab f1_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab p_eqss f0_eqoprab2b f1_eqoprab2b f3_eqoprab2b f4_eqoprab2b p_2albiim f0_eqoprab2b f1_eqoprab2b a_wb f4_eqoprab2b a_wal f3_eqoprab2b a_wal f0_eqoprab2b f1_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f1_eqoprab2b f0_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal a_wa f2_eqoprab2b p_albii f0_eqoprab2b f1_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f1_eqoprab2b f0_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b p_19.26 f0_eqoprab2b f1_eqoprab2b a_wb f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b a_wal f0_eqoprab2b f1_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f1_eqoprab2b f0_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal a_wa f2_eqoprab2b a_wal f0_eqoprab2b f1_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b a_wal f1_eqoprab2b f0_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b a_wal a_wa p_bitri f0_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab f1_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab a_wss f1_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab f0_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab a_wss a_wa f0_eqoprab2b f1_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b a_wal f1_eqoprab2b f0_eqoprab2b a_wi f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b a_wal a_wa f0_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab f1_eqoprab2b f2_eqoprab2b f3_eqoprab2b f4_eqoprab2b a_coprab a_wceq f0_eqoprab2b f1_eqoprab2b a_wb f4_eqoprab2b a_wal f3_eqoprab2b a_wal f2_eqoprab2b a_wal p_3bitr4i $.
$}

$(An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.)  (Revised by Mario Carneiro, 19-Mar-2015.) $)

${
	$v x y A B C D E F  $.
	$d x y z A  $.
	$d y z B  $.
	$d x y z D  $.
	$d y z E  $.
	$d z C  $.
	$d z F  $.
	f0_mpt2eq123 $f set x $.
	f1_mpt2eq123 $f set y $.
	f2_mpt2eq123 $f class A $.
	f3_mpt2eq123 $f class B $.
	f4_mpt2eq123 $f class C $.
	f5_mpt2eq123 $f class D $.
	f6_mpt2eq123 $f class E $.
	f7_mpt2eq123 $f class F $.
	i0_mpt2eq123 $f set z $.
	p_mpt2eq123 $p |- ( ( A = D /\ A. x e. A ( B = E /\ A. y e. B C = F ) ) -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $= f2_mpt2eq123 f5_mpt2eq123 a_wceq f0_mpt2eq123 p_nfv f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 p_nfra1 f2_mpt2eq123 f5_mpt2eq123 a_wceq f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral f0_mpt2eq123 p_nfan f2_mpt2eq123 f5_mpt2eq123 a_wceq f1_mpt2eq123 p_nfv f1_mpt2eq123 f2_mpt2eq123 p_nfcv f3_mpt2eq123 f6_mpt2eq123 a_wceq f1_mpt2eq123 p_nfv f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 p_nfra1 f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral f1_mpt2eq123 p_nfan f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f1_mpt2eq123 f0_mpt2eq123 f2_mpt2eq123 p_nfral f2_mpt2eq123 f5_mpt2eq123 a_wceq f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral f1_mpt2eq123 p_nfan f2_mpt2eq123 f5_mpt2eq123 a_wceq f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral a_wa i0_mpt2eq123 p_nfv f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 p_rsp f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 p_rsp f4_mpt2eq123 f7_mpt2eq123 i0_mpt2eq123 a_sup_set_class p_eqeq2 f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel f4_mpt2eq123 f7_mpt2eq123 a_wceq i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wb p_syl6 f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq p_pm5.32d f3_mpt2eq123 f6_mpt2eq123 f1_mpt2eq123 a_sup_set_class p_eleq2 f3_mpt2eq123 f6_mpt2eq123 a_wceq f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq p_anbi1d f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq a_wa f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa f3_mpt2eq123 f6_mpt2eq123 a_wceq f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa p_sylan9bbr f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq a_wa f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa a_wb p_syl6 f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq a_wa f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa p_pm5.32d f2_mpt2eq123 f5_mpt2eq123 f0_mpt2eq123 a_sup_set_class p_eleq2 f2_mpt2eq123 f5_mpt2eq123 a_wceq f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f0_mpt2eq123 a_sup_set_class f5_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa p_anbi1d f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq a_wa a_wa f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa a_wa f2_mpt2eq123 f5_mpt2eq123 a_wceq f0_mpt2eq123 a_sup_set_class f5_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa a_wa p_sylan9bbr f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq p_anass f0_mpt2eq123 a_sup_set_class f5_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq p_anass f2_mpt2eq123 f5_mpt2eq123 a_wceq f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral a_wa f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq a_wa a_wa f0_mpt2eq123 a_sup_set_class f5_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa a_wa f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel a_wa i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq a_wa f0_mpt2eq123 a_sup_set_class f5_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel a_wa i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa p_3bitr4g f2_mpt2eq123 f5_mpt2eq123 a_wceq f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral a_wa f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel a_wa i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq a_wa f0_mpt2eq123 a_sup_set_class f5_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel a_wa i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa f0_mpt2eq123 f1_mpt2eq123 i0_mpt2eq123 p_oprabbid f0_mpt2eq123 f1_mpt2eq123 i0_mpt2eq123 f2_mpt2eq123 f3_mpt2eq123 f4_mpt2eq123 a_df-mpt2 f0_mpt2eq123 f1_mpt2eq123 i0_mpt2eq123 f5_mpt2eq123 f6_mpt2eq123 f7_mpt2eq123 a_df-mpt2 f2_mpt2eq123 f5_mpt2eq123 a_wceq f3_mpt2eq123 f6_mpt2eq123 a_wceq f4_mpt2eq123 f7_mpt2eq123 a_wceq f1_mpt2eq123 f3_mpt2eq123 a_wral a_wa f0_mpt2eq123 f2_mpt2eq123 a_wral a_wa f0_mpt2eq123 a_sup_set_class f2_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f3_mpt2eq123 a_wcel a_wa i0_mpt2eq123 a_sup_set_class f4_mpt2eq123 a_wceq a_wa f0_mpt2eq123 f1_mpt2eq123 i0_mpt2eq123 a_coprab f0_mpt2eq123 a_sup_set_class f5_mpt2eq123 a_wcel f1_mpt2eq123 a_sup_set_class f6_mpt2eq123 a_wcel a_wa i0_mpt2eq123 a_sup_set_class f7_mpt2eq123 a_wceq a_wa f0_mpt2eq123 f1_mpt2eq123 i0_mpt2eq123 a_coprab f0_mpt2eq123 f1_mpt2eq123 f2_mpt2eq123 f3_mpt2eq123 f4_mpt2eq123 a_cmpt2 f0_mpt2eq123 f1_mpt2eq123 f5_mpt2eq123 f6_mpt2eq123 f7_mpt2eq123 a_cmpt2 p_3eqtr4g $.
$}

$(An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)

${
	$v x y A B C D E  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y D  $.
	f0_mpt2eq12 $f set x $.
	f1_mpt2eq12 $f set y $.
	f2_mpt2eq12 $f class A $.
	f3_mpt2eq12 $f class B $.
	f4_mpt2eq12 $f class C $.
	f5_mpt2eq12 $f class D $.
	f6_mpt2eq12 $f class E $.
	p_mpt2eq12 $p |- ( ( A = C /\ B = D ) -> ( x e. A , y e. B |-> E ) = ( x e. C , y e. D |-> E ) ) $= f6_mpt2eq12 p_eqid f6_mpt2eq12 f6_mpt2eq12 a_wceq f1_mpt2eq12 f3_mpt2eq12 p_rgenw f3_mpt2eq12 f5_mpt2eq12 a_wceq f6_mpt2eq12 f6_mpt2eq12 a_wceq f1_mpt2eq12 f3_mpt2eq12 a_wral p_jctr f3_mpt2eq12 f5_mpt2eq12 a_wceq f3_mpt2eq12 f5_mpt2eq12 a_wceq f6_mpt2eq12 f6_mpt2eq12 a_wceq f1_mpt2eq12 f3_mpt2eq12 a_wral a_wa f0_mpt2eq12 f2_mpt2eq12 p_ralrimivw f0_mpt2eq12 f1_mpt2eq12 f2_mpt2eq12 f3_mpt2eq12 f6_mpt2eq12 f4_mpt2eq12 f5_mpt2eq12 f6_mpt2eq12 p_mpt2eq123 f3_mpt2eq12 f5_mpt2eq12 a_wceq f2_mpt2eq12 f4_mpt2eq12 a_wceq f3_mpt2eq12 f5_mpt2eq12 a_wceq f6_mpt2eq12 f6_mpt2eq12 a_wceq f1_mpt2eq12 f3_mpt2eq12 a_wral a_wa f0_mpt2eq12 f2_mpt2eq12 a_wral f0_mpt2eq12 f1_mpt2eq12 f2_mpt2eq12 f3_mpt2eq12 f6_mpt2eq12 a_cmpt2 f0_mpt2eq12 f1_mpt2eq12 f4_mpt2eq12 f5_mpt2eq12 f6_mpt2eq12 a_cmpt2 a_wceq p_sylan2 $.
$}

$(An equality deduction for the maps to notation.  (Contributed by Mario
         Carneiro, 26-Jan-2017.) $)

${
	$v ph x y A B C D E F  $.
	$d z A  $.
	$d z B  $.
	$d z C  $.
	$d z D  $.
	$d z E  $.
	$d x z ph  $.
	$d z F  $.
	$d y z ph  $.
	f0_mpt2eq123dva $f wff ph $.
	f1_mpt2eq123dva $f set x $.
	f2_mpt2eq123dva $f set y $.
	f3_mpt2eq123dva $f class A $.
	f4_mpt2eq123dva $f class B $.
	f5_mpt2eq123dva $f class C $.
	f6_mpt2eq123dva $f class D $.
	f7_mpt2eq123dva $f class E $.
	f8_mpt2eq123dva $f class F $.
	i0_mpt2eq123dva $f set z $.
	e0_mpt2eq123dva $e |- ( ph -> A = D ) $.
	e1_mpt2eq123dva $e |- ( ( ph /\ x e. A ) -> B = E ) $.
	e2_mpt2eq123dva $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C = F ) $.
	p_mpt2eq123dva $p |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $= e2_mpt2eq123dva f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel a_wa a_wa f5_mpt2eq123dva f8_mpt2eq123dva i0_mpt2eq123dva a_sup_set_class p_eqeq2d f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f5_mpt2eq123dva a_wceq i0_mpt2eq123dva a_sup_set_class f8_mpt2eq123dva a_wceq p_pm5.32da e1_mpt2eq123dva f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel a_wa f4_mpt2eq123dva f7_mpt2eq123dva f2_mpt2eq123dva a_sup_set_class p_eleq2d f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f7_mpt2eq123dva a_wcel p_pm5.32da e0_mpt2eq123dva f0_mpt2eq123dva f3_mpt2eq123dva f6_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class p_eleq2d f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f1_mpt2eq123dva a_sup_set_class f6_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f7_mpt2eq123dva a_wcel p_anbi1d f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel a_wa f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f7_mpt2eq123dva a_wcel a_wa f1_mpt2eq123dva a_sup_set_class f6_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f7_mpt2eq123dva a_wcel a_wa p_bitrd f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel a_wa f1_mpt2eq123dva a_sup_set_class f6_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f7_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f8_mpt2eq123dva a_wceq p_anbi1d f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f5_mpt2eq123dva a_wceq a_wa f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f8_mpt2eq123dva a_wceq a_wa f1_mpt2eq123dva a_sup_set_class f6_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f7_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f8_mpt2eq123dva a_wceq a_wa p_bitrd f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f5_mpt2eq123dva a_wceq a_wa f1_mpt2eq123dva a_sup_set_class f6_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f7_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f8_mpt2eq123dva a_wceq a_wa f1_mpt2eq123dva f2_mpt2eq123dva i0_mpt2eq123dva p_oprabbidv f1_mpt2eq123dva f2_mpt2eq123dva i0_mpt2eq123dva f3_mpt2eq123dva f4_mpt2eq123dva f5_mpt2eq123dva a_df-mpt2 f1_mpt2eq123dva f2_mpt2eq123dva i0_mpt2eq123dva f6_mpt2eq123dva f7_mpt2eq123dva f8_mpt2eq123dva a_df-mpt2 f0_mpt2eq123dva f1_mpt2eq123dva a_sup_set_class f3_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f4_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f5_mpt2eq123dva a_wceq a_wa f1_mpt2eq123dva f2_mpt2eq123dva i0_mpt2eq123dva a_coprab f1_mpt2eq123dva a_sup_set_class f6_mpt2eq123dva a_wcel f2_mpt2eq123dva a_sup_set_class f7_mpt2eq123dva a_wcel a_wa i0_mpt2eq123dva a_sup_set_class f8_mpt2eq123dva a_wceq a_wa f1_mpt2eq123dva f2_mpt2eq123dva i0_mpt2eq123dva a_coprab f1_mpt2eq123dva f2_mpt2eq123dva f3_mpt2eq123dva f4_mpt2eq123dva f5_mpt2eq123dva a_cmpt2 f1_mpt2eq123dva f2_mpt2eq123dva f6_mpt2eq123dva f7_mpt2eq123dva f8_mpt2eq123dva a_cmpt2 p_3eqtr4g $.
$}

$(An equality deduction for the maps to notation.  (Contributed by NM,
       12-Sep-2011.) $)

${
	$v ph x y A B C D E F  $.
	$d A  $.
	$d B  $.
	$d C  $.
	$d D  $.
	$d E  $.
	$d x ph  $.
	$d F  $.
	$d y ph  $.
	f0_mpt2eq123dv $f wff ph $.
	f1_mpt2eq123dv $f set x $.
	f2_mpt2eq123dv $f set y $.
	f3_mpt2eq123dv $f class A $.
	f4_mpt2eq123dv $f class B $.
	f5_mpt2eq123dv $f class C $.
	f6_mpt2eq123dv $f class D $.
	f7_mpt2eq123dv $f class E $.
	f8_mpt2eq123dv $f class F $.
	e0_mpt2eq123dv $e |- ( ph -> A = D ) $.
	e1_mpt2eq123dv $e |- ( ph -> B = E ) $.
	e2_mpt2eq123dv $e |- ( ph -> C = F ) $.
	p_mpt2eq123dv $p |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $= e0_mpt2eq123dv e1_mpt2eq123dv f0_mpt2eq123dv f4_mpt2eq123dv f7_mpt2eq123dv a_wceq f1_mpt2eq123dv a_sup_set_class f3_mpt2eq123dv a_wcel p_adantr e2_mpt2eq123dv f0_mpt2eq123dv f5_mpt2eq123dv f8_mpt2eq123dv a_wceq f1_mpt2eq123dv a_sup_set_class f3_mpt2eq123dv a_wcel f2_mpt2eq123dv a_sup_set_class f4_mpt2eq123dv a_wcel a_wa p_adantr f0_mpt2eq123dv f1_mpt2eq123dv f2_mpt2eq123dv f3_mpt2eq123dv f4_mpt2eq123dv f5_mpt2eq123dv f6_mpt2eq123dv f7_mpt2eq123dv f8_mpt2eq123dv p_mpt2eq123dva $.
$}

$(An equality inference for the maps to notation.  (Contributed by NM,
       15-Jul-2013.) $)

${
	$v x y A B C D E F  $.
	f0_mpt2eq123i $f set x $.
	f1_mpt2eq123i $f set y $.
	f2_mpt2eq123i $f class A $.
	f3_mpt2eq123i $f class B $.
	f4_mpt2eq123i $f class C $.
	f5_mpt2eq123i $f class D $.
	f6_mpt2eq123i $f class E $.
	f7_mpt2eq123i $f class F $.
	e0_mpt2eq123i $e |- A = D $.
	e1_mpt2eq123i $e |- B = E $.
	e2_mpt2eq123i $e |- C = F $.
	p_mpt2eq123i $p |- ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) $= e0_mpt2eq123i f2_mpt2eq123i f5_mpt2eq123i a_wceq a_wtru p_a1i e1_mpt2eq123i f3_mpt2eq123i f6_mpt2eq123i a_wceq a_wtru p_a1i e2_mpt2eq123i f4_mpt2eq123i f7_mpt2eq123i a_wceq a_wtru p_a1i a_wtru f0_mpt2eq123i f1_mpt2eq123i f2_mpt2eq123i f3_mpt2eq123i f4_mpt2eq123i f5_mpt2eq123i f6_mpt2eq123i f7_mpt2eq123i p_mpt2eq123dv f0_mpt2eq123i f1_mpt2eq123i f2_mpt2eq123i f3_mpt2eq123i f4_mpt2eq123i a_cmpt2 f0_mpt2eq123i f1_mpt2eq123i f5_mpt2eq123i f6_mpt2eq123i f7_mpt2eq123i a_cmpt2 a_wceq p_trud $.
$}

$(Slightly more general equality inference for the maps to notation.
       (Contributed by NM, 17-Oct-2013.) $)

${
	$v ph x y A B C D  $.
	$d x z ph  $.
	$d y z ph  $.
	$d z A  $.
	$d z B  $.
	$d z C  $.
	$d z D  $.
	f0_mpt2eq3dva $f wff ph $.
	f1_mpt2eq3dva $f set x $.
	f2_mpt2eq3dva $f set y $.
	f3_mpt2eq3dva $f class A $.
	f4_mpt2eq3dva $f class B $.
	f5_mpt2eq3dva $f class C $.
	f6_mpt2eq3dva $f class D $.
	i0_mpt2eq3dva $f set z $.
	e0_mpt2eq3dva $e |- ( ( ph /\ x e. A /\ y e. B ) -> C = D ) $.
	p_mpt2eq3dva $p |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) ) $= e0_mpt2eq3dva f0_mpt2eq3dva f1_mpt2eq3dva a_sup_set_class f3_mpt2eq3dva a_wcel f2_mpt2eq3dva a_sup_set_class f4_mpt2eq3dva a_wcel f5_mpt2eq3dva f6_mpt2eq3dva a_wceq p_3expb f0_mpt2eq3dva f1_mpt2eq3dva a_sup_set_class f3_mpt2eq3dva a_wcel f2_mpt2eq3dva a_sup_set_class f4_mpt2eq3dva a_wcel a_wa a_wa f5_mpt2eq3dva f6_mpt2eq3dva i0_mpt2eq3dva a_sup_set_class p_eqeq2d f0_mpt2eq3dva f1_mpt2eq3dva a_sup_set_class f3_mpt2eq3dva a_wcel f2_mpt2eq3dva a_sup_set_class f4_mpt2eq3dva a_wcel a_wa i0_mpt2eq3dva a_sup_set_class f5_mpt2eq3dva a_wceq i0_mpt2eq3dva a_sup_set_class f6_mpt2eq3dva a_wceq p_pm5.32da f0_mpt2eq3dva f1_mpt2eq3dva a_sup_set_class f3_mpt2eq3dva a_wcel f2_mpt2eq3dva a_sup_set_class f4_mpt2eq3dva a_wcel a_wa i0_mpt2eq3dva a_sup_set_class f5_mpt2eq3dva a_wceq a_wa f1_mpt2eq3dva a_sup_set_class f3_mpt2eq3dva a_wcel f2_mpt2eq3dva a_sup_set_class f4_mpt2eq3dva a_wcel a_wa i0_mpt2eq3dva a_sup_set_class f6_mpt2eq3dva a_wceq a_wa f1_mpt2eq3dva f2_mpt2eq3dva i0_mpt2eq3dva p_oprabbidv f1_mpt2eq3dva f2_mpt2eq3dva i0_mpt2eq3dva f3_mpt2eq3dva f4_mpt2eq3dva f5_mpt2eq3dva a_df-mpt2 f1_mpt2eq3dva f2_mpt2eq3dva i0_mpt2eq3dva f3_mpt2eq3dva f4_mpt2eq3dva f6_mpt2eq3dva a_df-mpt2 f0_mpt2eq3dva f1_mpt2eq3dva a_sup_set_class f3_mpt2eq3dva a_wcel f2_mpt2eq3dva a_sup_set_class f4_mpt2eq3dva a_wcel a_wa i0_mpt2eq3dva a_sup_set_class f5_mpt2eq3dva a_wceq a_wa f1_mpt2eq3dva f2_mpt2eq3dva i0_mpt2eq3dva a_coprab f1_mpt2eq3dva a_sup_set_class f3_mpt2eq3dva a_wcel f2_mpt2eq3dva a_sup_set_class f4_mpt2eq3dva a_wcel a_wa i0_mpt2eq3dva a_sup_set_class f6_mpt2eq3dva a_wceq a_wa f1_mpt2eq3dva f2_mpt2eq3dva i0_mpt2eq3dva a_coprab f1_mpt2eq3dva f2_mpt2eq3dva f3_mpt2eq3dva f4_mpt2eq3dva f5_mpt2eq3dva a_cmpt2 f1_mpt2eq3dva f2_mpt2eq3dva f3_mpt2eq3dva f4_mpt2eq3dva f6_mpt2eq3dva a_cmpt2 p_3eqtr4g $.
$}

$(An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)

${
	$v x y A B C D  $.
	f0_mpt2eq3ia $f set x $.
	f1_mpt2eq3ia $f set y $.
	f2_mpt2eq3ia $f class A $.
	f3_mpt2eq3ia $f class B $.
	f4_mpt2eq3ia $f class C $.
	f5_mpt2eq3ia $f class D $.
	e0_mpt2eq3ia $e |- ( ( x e. A /\ y e. B ) -> C = D ) $.
	p_mpt2eq3ia $p |- ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) $= e0_mpt2eq3ia f0_mpt2eq3ia a_sup_set_class f2_mpt2eq3ia a_wcel f1_mpt2eq3ia a_sup_set_class f3_mpt2eq3ia a_wcel f4_mpt2eq3ia f5_mpt2eq3ia a_wceq a_wtru p_3adant1 a_wtru f0_mpt2eq3ia f1_mpt2eq3ia f2_mpt2eq3ia f3_mpt2eq3ia f4_mpt2eq3ia f5_mpt2eq3ia p_mpt2eq3dva f0_mpt2eq3ia f1_mpt2eq3ia f2_mpt2eq3ia f3_mpt2eq3ia f4_mpt2eq3ia a_cmpt2 f0_mpt2eq3ia f1_mpt2eq3ia f2_mpt2eq3ia f3_mpt2eq3ia f5_mpt2eq3ia a_cmpt2 a_wceq p_trud $.
$}

$(Bound-variable hypothesis builder for an operation in maps-to notation.
       (Contributed by NM, 27-Aug-2013.) $)

${
	$v x y A B C  $.
	$d z A  $.
	$d z B  $.
	$d z C  $.
	$d z x  $.
	$d z y  $.
	f0_nfmpt21 $f set x $.
	f1_nfmpt21 $f set y $.
	f2_nfmpt21 $f class A $.
	f3_nfmpt21 $f class B $.
	f4_nfmpt21 $f class C $.
	i0_nfmpt21 $f set z $.
	p_nfmpt21 $p |- F/_ x ( x e. A , y e. B |-> C ) $= f0_nfmpt21 f1_nfmpt21 i0_nfmpt21 f2_nfmpt21 f3_nfmpt21 f4_nfmpt21 a_df-mpt2 f0_nfmpt21 a_sup_set_class f2_nfmpt21 a_wcel f1_nfmpt21 a_sup_set_class f3_nfmpt21 a_wcel a_wa i0_nfmpt21 a_sup_set_class f4_nfmpt21 a_wceq a_wa f0_nfmpt21 f1_nfmpt21 i0_nfmpt21 p_nfoprab1 f0_nfmpt21 f0_nfmpt21 f1_nfmpt21 f2_nfmpt21 f3_nfmpt21 f4_nfmpt21 a_cmpt2 f0_nfmpt21 a_sup_set_class f2_nfmpt21 a_wcel f1_nfmpt21 a_sup_set_class f3_nfmpt21 a_wcel a_wa i0_nfmpt21 a_sup_set_class f4_nfmpt21 a_wceq a_wa f0_nfmpt21 f1_nfmpt21 i0_nfmpt21 a_coprab p_nfcxfr $.
$}

$(Bound-variable hypothesis builder for an operation in maps-to notation.
       (Contributed by NM, 27-Aug-2013.) $)

${
	$v x y A B C  $.
	$d z A  $.
	$d z B  $.
	$d z C  $.
	$d z x  $.
	$d z y  $.
	f0_nfmpt22 $f set x $.
	f1_nfmpt22 $f set y $.
	f2_nfmpt22 $f class A $.
	f3_nfmpt22 $f class B $.
	f4_nfmpt22 $f class C $.
	i0_nfmpt22 $f set z $.
	p_nfmpt22 $p |- F/_ y ( x e. A , y e. B |-> C ) $= f0_nfmpt22 f1_nfmpt22 i0_nfmpt22 f2_nfmpt22 f3_nfmpt22 f4_nfmpt22 a_df-mpt2 f0_nfmpt22 a_sup_set_class f2_nfmpt22 a_wcel f1_nfmpt22 a_sup_set_class f3_nfmpt22 a_wcel a_wa i0_nfmpt22 a_sup_set_class f4_nfmpt22 a_wceq a_wa f0_nfmpt22 f1_nfmpt22 i0_nfmpt22 p_nfoprab2 f1_nfmpt22 f0_nfmpt22 f1_nfmpt22 f2_nfmpt22 f3_nfmpt22 f4_nfmpt22 a_cmpt2 f0_nfmpt22 a_sup_set_class f2_nfmpt22 a_wcel f1_nfmpt22 a_sup_set_class f3_nfmpt22 a_wcel a_wa i0_nfmpt22 a_sup_set_class f4_nfmpt22 a_wceq a_wa f0_nfmpt22 f1_nfmpt22 i0_nfmpt22 a_coprab p_nfcxfr $.
$}

$(Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by NM, 20-Feb-2013.) $)

${
	$v x y z A B C  $.
	$d w x z  $.
	$d w y z  $.
	$d w A  $.
	$d w B  $.
	$d w C  $.
	f0_nfmpt2 $f set x $.
	f1_nfmpt2 $f set y $.
	f2_nfmpt2 $f set z $.
	f3_nfmpt2 $f class A $.
	f4_nfmpt2 $f class B $.
	f5_nfmpt2 $f class C $.
	i0_nfmpt2 $f set w $.
	e0_nfmpt2 $e |- F/_ z A $.
	e1_nfmpt2 $e |- F/_ z B $.
	e2_nfmpt2 $e |- F/_ z C $.
	p_nfmpt2 $p |- F/_ z ( x e. A , y e. B |-> C ) $= f0_nfmpt2 f1_nfmpt2 i0_nfmpt2 f3_nfmpt2 f4_nfmpt2 f5_nfmpt2 a_df-mpt2 e0_nfmpt2 f2_nfmpt2 f0_nfmpt2 f3_nfmpt2 p_nfcri e1_nfmpt2 f2_nfmpt2 f1_nfmpt2 f4_nfmpt2 p_nfcri f0_nfmpt2 a_sup_set_class f3_nfmpt2 a_wcel f1_nfmpt2 a_sup_set_class f4_nfmpt2 a_wcel f2_nfmpt2 p_nfan e2_nfmpt2 f2_nfmpt2 i0_nfmpt2 a_sup_set_class f5_nfmpt2 p_nfeq2 f0_nfmpt2 a_sup_set_class f3_nfmpt2 a_wcel f1_nfmpt2 a_sup_set_class f4_nfmpt2 a_wcel a_wa i0_nfmpt2 a_sup_set_class f5_nfmpt2 a_wceq f2_nfmpt2 p_nfan f0_nfmpt2 a_sup_set_class f3_nfmpt2 a_wcel f1_nfmpt2 a_sup_set_class f4_nfmpt2 a_wcel a_wa i0_nfmpt2 a_sup_set_class f5_nfmpt2 a_wceq a_wa f0_nfmpt2 f1_nfmpt2 i0_nfmpt2 f2_nfmpt2 p_nfoprab f2_nfmpt2 f0_nfmpt2 f1_nfmpt2 f3_nfmpt2 f4_nfmpt2 f5_nfmpt2 a_cmpt2 f0_nfmpt2 a_sup_set_class f3_nfmpt2 a_wcel f1_nfmpt2 a_sup_set_class f4_nfmpt2 a_wcel a_wa i0_nfmpt2 a_sup_set_class f5_nfmpt2 a_wceq a_wa f0_nfmpt2 f1_nfmpt2 i0_nfmpt2 a_coprab p_nfcxfr $.
$}

$(Two ways to state the domain of an operation.  (Contributed by FL,
       24-Jan-2010.) $)

${
	$v ph x y z A B  $.
	$d x y z  $.
	f0_oprab4 $f wff ph $.
	f1_oprab4 $f set x $.
	f2_oprab4 $f set y $.
	f3_oprab4 $f set z $.
	f4_oprab4 $f class A $.
	f5_oprab4 $f class B $.
	p_oprab4 $p |- { <. <. x , y >. , z >. | ( <. x , y >. e. ( A X. B ) /\ ph ) } = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $= f1_oprab4 a_sup_set_class f2_oprab4 a_sup_set_class f4_oprab4 f5_oprab4 p_opelxp f1_oprab4 a_sup_set_class f2_oprab4 a_sup_set_class a_cop f4_oprab4 f5_oprab4 a_cxp a_wcel f1_oprab4 a_sup_set_class f4_oprab4 a_wcel f2_oprab4 a_sup_set_class f5_oprab4 a_wcel a_wa f0_oprab4 p_anbi1i f1_oprab4 a_sup_set_class f2_oprab4 a_sup_set_class a_cop f4_oprab4 f5_oprab4 a_cxp a_wcel f0_oprab4 a_wa f1_oprab4 a_sup_set_class f4_oprab4 a_wcel f2_oprab4 a_sup_set_class f5_oprab4 a_wcel a_wa f0_oprab4 a_wa f1_oprab4 f2_oprab4 f3_oprab4 p_oprabbii $.
$}

$(Rule used to change first bound variable in an operation abstraction,
       using implicit substitution.  (Contributed by NM, 20-Dec-2008.)
       (Revised by Mario Carneiro, 5-Dec-2016.) $)

${
	$v ph ps x y z w  $.
	$d x y z w v  $.
	$d v ph  $.
	$d v ps  $.
	f0_cbvoprab1 $f wff ph $.
	f1_cbvoprab1 $f wff ps $.
	f2_cbvoprab1 $f set x $.
	f3_cbvoprab1 $f set y $.
	f4_cbvoprab1 $f set z $.
	f5_cbvoprab1 $f set w $.
	i0_cbvoprab1 $f set v $.
	e0_cbvoprab1 $e |- F/ w ph $.
	e1_cbvoprab1 $e |- F/ x ps $.
	e2_cbvoprab1 $e |- ( x = w -> ( ph <-> ps ) ) $.
	p_cbvoprab1 $p |- { <. <. x , y >. , z >. | ph } = { <. <. w , y >. , z >. | ps } $= i0_cbvoprab1 a_sup_set_class f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f5_cbvoprab1 p_nfv e0_cbvoprab1 i0_cbvoprab1 a_sup_set_class f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f0_cbvoprab1 f5_cbvoprab1 p_nfan i0_cbvoprab1 a_sup_set_class f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f0_cbvoprab1 a_wa f5_cbvoprab1 f3_cbvoprab1 p_nfex i0_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f2_cbvoprab1 p_nfv e1_cbvoprab1 i0_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f1_cbvoprab1 f2_cbvoprab1 p_nfan i0_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f1_cbvoprab1 a_wa f2_cbvoprab1 f3_cbvoprab1 p_nfex f2_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class p_opeq1 f2_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class a_wceq f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop i0_cbvoprab1 a_sup_set_class p_eqeq2d e2_cbvoprab1 f2_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class a_wceq i0_cbvoprab1 a_sup_set_class f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq i0_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f0_cbvoprab1 f1_cbvoprab1 p_anbi12d f2_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class a_wceq i0_cbvoprab1 a_sup_set_class f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f0_cbvoprab1 a_wa i0_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f1_cbvoprab1 a_wa f3_cbvoprab1 p_exbidv i0_cbvoprab1 a_sup_set_class f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f0_cbvoprab1 a_wa f3_cbvoprab1 a_wex i0_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f1_cbvoprab1 a_wa f3_cbvoprab1 a_wex f2_cbvoprab1 f5_cbvoprab1 p_cbvex i0_cbvoprab1 a_sup_set_class f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f0_cbvoprab1 a_wa f3_cbvoprab1 a_wex f2_cbvoprab1 a_wex i0_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f1_cbvoprab1 a_wa f3_cbvoprab1 a_wex f5_cbvoprab1 a_wex i0_cbvoprab1 f4_cbvoprab1 p_opabbii f0_cbvoprab1 f2_cbvoprab1 f3_cbvoprab1 f4_cbvoprab1 i0_cbvoprab1 p_dfoprab2 f1_cbvoprab1 f5_cbvoprab1 f3_cbvoprab1 f4_cbvoprab1 i0_cbvoprab1 p_dfoprab2 i0_cbvoprab1 a_sup_set_class f2_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f0_cbvoprab1 a_wa f3_cbvoprab1 a_wex f2_cbvoprab1 a_wex i0_cbvoprab1 f4_cbvoprab1 a_copab i0_cbvoprab1 a_sup_set_class f5_cbvoprab1 a_sup_set_class f3_cbvoprab1 a_sup_set_class a_cop a_wceq f1_cbvoprab1 a_wa f3_cbvoprab1 a_wex f5_cbvoprab1 a_wex i0_cbvoprab1 f4_cbvoprab1 a_copab f0_cbvoprab1 f2_cbvoprab1 f3_cbvoprab1 f4_cbvoprab1 a_coprab f1_cbvoprab1 f5_cbvoprab1 f3_cbvoprab1 f4_cbvoprab1 a_coprab p_3eqtr4i $.
$}

$(Change the second bound variable in an operation abstraction.
       (Contributed by Jeff Madsen, 11-Jun-2010.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)

${
	$v ph ps x y z w  $.
	$d v w x y z  $.
	$d ph v  $.
	$d ps v  $.
	f0_cbvoprab2 $f wff ph $.
	f1_cbvoprab2 $f wff ps $.
	f2_cbvoprab2 $f set x $.
	f3_cbvoprab2 $f set y $.
	f4_cbvoprab2 $f set z $.
	f5_cbvoprab2 $f set w $.
	i0_cbvoprab2 $f set v $.
	e0_cbvoprab2 $e |- F/ w ph $.
	e1_cbvoprab2 $e |- F/ y ps $.
	e2_cbvoprab2 $e |- ( y = w -> ( ph <-> ps ) ) $.
	p_cbvoprab2 $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , w >. , z >. | ps } $= i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f5_cbvoprab2 p_nfv e0_cbvoprab2 i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f0_cbvoprab2 f5_cbvoprab2 p_nfan i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f0_cbvoprab2 a_wa f5_cbvoprab2 f4_cbvoprab2 p_nfex i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f3_cbvoprab2 p_nfv e1_cbvoprab2 i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f1_cbvoprab2 f3_cbvoprab2 p_nfan i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f1_cbvoprab2 a_wa f3_cbvoprab2 f4_cbvoprab2 p_nfex f3_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class p_opeq2 f3_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_wceq f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class p_opeq1d f3_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_wceq f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop i0_cbvoprab2 a_sup_set_class p_eqeq2d e2_cbvoprab2 f3_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_wceq i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f0_cbvoprab2 f1_cbvoprab2 p_anbi12d f3_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_wceq i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f0_cbvoprab2 a_wa i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f1_cbvoprab2 a_wa f4_cbvoprab2 p_exbidv i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f0_cbvoprab2 a_wa f4_cbvoprab2 a_wex i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f1_cbvoprab2 a_wa f4_cbvoprab2 a_wex f3_cbvoprab2 f5_cbvoprab2 p_cbvex i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f0_cbvoprab2 a_wa f4_cbvoprab2 a_wex f3_cbvoprab2 a_wex i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f1_cbvoprab2 a_wa f4_cbvoprab2 a_wex f5_cbvoprab2 a_wex f2_cbvoprab2 p_exbii i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f0_cbvoprab2 a_wa f4_cbvoprab2 a_wex f3_cbvoprab2 a_wex f2_cbvoprab2 a_wex i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f1_cbvoprab2 a_wa f4_cbvoprab2 a_wex f5_cbvoprab2 a_wex f2_cbvoprab2 a_wex i0_cbvoprab2 p_abbii f0_cbvoprab2 f2_cbvoprab2 f3_cbvoprab2 f4_cbvoprab2 i0_cbvoprab2 a_df-oprab f1_cbvoprab2 f2_cbvoprab2 f5_cbvoprab2 f4_cbvoprab2 i0_cbvoprab2 a_df-oprab i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f3_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f0_cbvoprab2 a_wa f4_cbvoprab2 a_wex f3_cbvoprab2 a_wex f2_cbvoprab2 a_wex i0_cbvoprab2 a_cab i0_cbvoprab2 a_sup_set_class f2_cbvoprab2 a_sup_set_class f5_cbvoprab2 a_sup_set_class a_cop f4_cbvoprab2 a_sup_set_class a_cop a_wceq f1_cbvoprab2 a_wa f4_cbvoprab2 a_wex f5_cbvoprab2 a_wex f2_cbvoprab2 a_wex i0_cbvoprab2 a_cab f0_cbvoprab2 f2_cbvoprab2 f3_cbvoprab2 f4_cbvoprab2 a_coprab f1_cbvoprab2 f2_cbvoprab2 f5_cbvoprab2 f4_cbvoprab2 a_coprab p_3eqtr4i $.
$}

$(Rule used to change first two bound variables in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       21-Feb-2004.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)

${
	$v ph ps x y z w v  $.
	$d x y z w v u  $.
	$d u ph  $.
	$d u ps  $.
	f0_cbvoprab12 $f wff ph $.
	f1_cbvoprab12 $f wff ps $.
	f2_cbvoprab12 $f set x $.
	f3_cbvoprab12 $f set y $.
	f4_cbvoprab12 $f set z $.
	f5_cbvoprab12 $f set w $.
	f6_cbvoprab12 $f set v $.
	i0_cbvoprab12 $f set u $.
	e0_cbvoprab12 $e |- F/ w ph $.
	e1_cbvoprab12 $e |- F/ v ph $.
	e2_cbvoprab12 $e |- F/ x ps $.
	e3_cbvoprab12 $e |- F/ y ps $.
	e4_cbvoprab12 $e |- ( ( x = w /\ y = v ) -> ( ph <-> ps ) ) $.
	p_cbvoprab12 $p |- { <. <. x , y >. , z >. | ph } = { <. <. w , v >. , z >. | ps } $= i0_cbvoprab12 a_sup_set_class f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop a_wceq f5_cbvoprab12 p_nfv e0_cbvoprab12 i0_cbvoprab12 a_sup_set_class f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop a_wceq f0_cbvoprab12 f5_cbvoprab12 p_nfan i0_cbvoprab12 a_sup_set_class f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop a_wceq f6_cbvoprab12 p_nfv e1_cbvoprab12 i0_cbvoprab12 a_sup_set_class f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop a_wceq f0_cbvoprab12 f6_cbvoprab12 p_nfan i0_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop a_wceq f2_cbvoprab12 p_nfv e2_cbvoprab12 i0_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop a_wceq f1_cbvoprab12 f2_cbvoprab12 p_nfan i0_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop a_wceq f3_cbvoprab12 p_nfv e3_cbvoprab12 i0_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop a_wceq f1_cbvoprab12 f3_cbvoprab12 p_nfan f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class p_opeq12 f2_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class a_wceq f3_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_wceq a_wa f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop i0_cbvoprab12 a_sup_set_class p_eqeq2d e4_cbvoprab12 f2_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class a_wceq f3_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_wceq a_wa i0_cbvoprab12 a_sup_set_class f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop a_wceq i0_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop a_wceq f0_cbvoprab12 f1_cbvoprab12 p_anbi12d i0_cbvoprab12 a_sup_set_class f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop a_wceq f0_cbvoprab12 a_wa i0_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop a_wceq f1_cbvoprab12 a_wa f2_cbvoprab12 f3_cbvoprab12 f5_cbvoprab12 f6_cbvoprab12 p_cbvex2 i0_cbvoprab12 a_sup_set_class f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop a_wceq f0_cbvoprab12 a_wa f3_cbvoprab12 a_wex f2_cbvoprab12 a_wex i0_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop a_wceq f1_cbvoprab12 a_wa f6_cbvoprab12 a_wex f5_cbvoprab12 a_wex i0_cbvoprab12 f4_cbvoprab12 p_opabbii f0_cbvoprab12 f2_cbvoprab12 f3_cbvoprab12 f4_cbvoprab12 i0_cbvoprab12 p_dfoprab2 f1_cbvoprab12 f5_cbvoprab12 f6_cbvoprab12 f4_cbvoprab12 i0_cbvoprab12 p_dfoprab2 i0_cbvoprab12 a_sup_set_class f2_cbvoprab12 a_sup_set_class f3_cbvoprab12 a_sup_set_class a_cop a_wceq f0_cbvoprab12 a_wa f3_cbvoprab12 a_wex f2_cbvoprab12 a_wex i0_cbvoprab12 f4_cbvoprab12 a_copab i0_cbvoprab12 a_sup_set_class f5_cbvoprab12 a_sup_set_class f6_cbvoprab12 a_sup_set_class a_cop a_wceq f1_cbvoprab12 a_wa f6_cbvoprab12 a_wex f5_cbvoprab12 a_wex i0_cbvoprab12 f4_cbvoprab12 a_copab f0_cbvoprab12 f2_cbvoprab12 f3_cbvoprab12 f4_cbvoprab12 a_coprab f1_cbvoprab12 f5_cbvoprab12 f6_cbvoprab12 f4_cbvoprab12 a_coprab p_3eqtr4i $.
$}

$(Rule used to change first two bound variables in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       8-Oct-2004.) $)

${
	$v ph ps x y z w v  $.
	$d x y z w v  $.
	$d w v ph  $.
	$d x y ps  $.
	f0_cbvoprab12v $f wff ph $.
	f1_cbvoprab12v $f wff ps $.
	f2_cbvoprab12v $f set x $.
	f3_cbvoprab12v $f set y $.
	f4_cbvoprab12v $f set z $.
	f5_cbvoprab12v $f set w $.
	f6_cbvoprab12v $f set v $.
	e0_cbvoprab12v $e |- ( ( x = w /\ y = v ) -> ( ph <-> ps ) ) $.
	p_cbvoprab12v $p |- { <. <. x , y >. , z >. | ph } = { <. <. w , v >. , z >. | ps } $= f0_cbvoprab12v f5_cbvoprab12v p_nfv f0_cbvoprab12v f6_cbvoprab12v p_nfv f1_cbvoprab12v f2_cbvoprab12v p_nfv f1_cbvoprab12v f3_cbvoprab12v p_nfv e0_cbvoprab12v f0_cbvoprab12v f1_cbvoprab12v f2_cbvoprab12v f3_cbvoprab12v f4_cbvoprab12v f5_cbvoprab12v f6_cbvoprab12v p_cbvoprab12 $.
$}

$(Rule used to change the third bound variable in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       22-Aug-2013.) $)

${
	$v ph ps x y z w  $.
	$d x z w v  $.
	$d y z w v  $.
	$d v ph  $.
	$d v ps  $.
	f0_cbvoprab3 $f wff ph $.
	f1_cbvoprab3 $f wff ps $.
	f2_cbvoprab3 $f set x $.
	f3_cbvoprab3 $f set y $.
	f4_cbvoprab3 $f set z $.
	f5_cbvoprab3 $f set w $.
	i0_cbvoprab3 $f set v $.
	e0_cbvoprab3 $e |- F/ w ph $.
	e1_cbvoprab3 $e |- F/ z ps $.
	e2_cbvoprab3 $e |- ( z = w -> ( ph <-> ps ) ) $.
	p_cbvoprab3 $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , w >. | ps } $= i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f5_cbvoprab3 p_nfv e0_cbvoprab3 i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f0_cbvoprab3 f5_cbvoprab3 p_nfan i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f0_cbvoprab3 a_wa f5_cbvoprab3 f3_cbvoprab3 p_nfex i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f0_cbvoprab3 a_wa f3_cbvoprab3 a_wex f5_cbvoprab3 f2_cbvoprab3 p_nfex i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f4_cbvoprab3 p_nfv e1_cbvoprab3 i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f1_cbvoprab3 f4_cbvoprab3 p_nfan i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f1_cbvoprab3 a_wa f4_cbvoprab3 f3_cbvoprab3 p_nfex i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f1_cbvoprab3 a_wa f3_cbvoprab3 a_wex f4_cbvoprab3 f2_cbvoprab3 p_nfex e2_cbvoprab3 f4_cbvoprab3 a_sup_set_class f5_cbvoprab3 a_sup_set_class a_wceq f0_cbvoprab3 f1_cbvoprab3 i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq p_anbi2d f4_cbvoprab3 a_sup_set_class f5_cbvoprab3 a_sup_set_class a_wceq i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f0_cbvoprab3 a_wa i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f1_cbvoprab3 a_wa f2_cbvoprab3 f3_cbvoprab3 p_2exbidv i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f0_cbvoprab3 a_wa f3_cbvoprab3 a_wex f2_cbvoprab3 a_wex i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f1_cbvoprab3 a_wa f3_cbvoprab3 a_wex f2_cbvoprab3 a_wex i0_cbvoprab3 f4_cbvoprab3 f5_cbvoprab3 p_cbvopab2 f0_cbvoprab3 f2_cbvoprab3 f3_cbvoprab3 f4_cbvoprab3 i0_cbvoprab3 p_dfoprab2 f1_cbvoprab3 f2_cbvoprab3 f3_cbvoprab3 f5_cbvoprab3 i0_cbvoprab3 p_dfoprab2 i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f0_cbvoprab3 a_wa f3_cbvoprab3 a_wex f2_cbvoprab3 a_wex i0_cbvoprab3 f4_cbvoprab3 a_copab i0_cbvoprab3 a_sup_set_class f2_cbvoprab3 a_sup_set_class f3_cbvoprab3 a_sup_set_class a_cop a_wceq f1_cbvoprab3 a_wa f3_cbvoprab3 a_wex f2_cbvoprab3 a_wex i0_cbvoprab3 f5_cbvoprab3 a_copab f0_cbvoprab3 f2_cbvoprab3 f3_cbvoprab3 f4_cbvoprab3 a_coprab f1_cbvoprab3 f2_cbvoprab3 f3_cbvoprab3 f5_cbvoprab3 a_coprab p_3eqtr4i $.
$}

$(Rule used to change the third bound variable in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       8-Oct-2004.)  (Revised by David Abernethy, 19-Jun-2012.) $)

${
	$v ph ps x y z w  $.
	$d x z w  $.
	$d y z w  $.
	$d w ph  $.
	$d z ps  $.
	f0_cbvoprab3v $f wff ph $.
	f1_cbvoprab3v $f wff ps $.
	f2_cbvoprab3v $f set x $.
	f3_cbvoprab3v $f set y $.
	f4_cbvoprab3v $f set z $.
	f5_cbvoprab3v $f set w $.
	e0_cbvoprab3v $e |- ( z = w -> ( ph <-> ps ) ) $.
	p_cbvoprab3v $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , w >. | ps } $= f0_cbvoprab3v f5_cbvoprab3v p_nfv f1_cbvoprab3v f4_cbvoprab3v p_nfv e0_cbvoprab3v f0_cbvoprab3v f1_cbvoprab3v f2_cbvoprab3v f3_cbvoprab3v f4_cbvoprab3v f5_cbvoprab3v p_cbvoprab3 $.
$}

$(Rule to change the bound variable in a maps-to function, using implicit
       substitution.  This version of ~ cbvmpt2 allows ` B ` to be a function
       of ` x ` .  (Contributed by NM, 29-Dec-2014.) $)

${
	$v x y z w A B C D E  $.
	$d u w x y z  $.
	$d u w x y z A  $.
	$d u w B  $.
	$d u C  $.
	$d u y D  $.
	$d u E  $.
	f0_cbvmpt2x $f set x $.
	f1_cbvmpt2x $f set y $.
	f2_cbvmpt2x $f set z $.
	f3_cbvmpt2x $f set w $.
	f4_cbvmpt2x $f class A $.
	f5_cbvmpt2x $f class B $.
	f6_cbvmpt2x $f class C $.
	f7_cbvmpt2x $f class D $.
	f8_cbvmpt2x $f class E $.
	i0_cbvmpt2x $f set u $.
	e0_cbvmpt2x $e |- F/_ z B $.
	e1_cbvmpt2x $e |- F/_ x D $.
	e2_cbvmpt2x $e |- F/_ z C $.
	e3_cbvmpt2x $e |- F/_ w C $.
	e4_cbvmpt2x $e |- F/_ x E $.
	e5_cbvmpt2x $e |- F/_ y E $.
	e6_cbvmpt2x $e |- ( x = z -> B = D ) $.
	e7_cbvmpt2x $e |- ( ( x = z /\ y = w ) -> C = E ) $.
	p_cbvmpt2x $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. D |-> E ) $= f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f2_cbvmpt2x p_nfv e0_cbvmpt2x f2_cbvmpt2x f1_cbvmpt2x f5_cbvmpt2x p_nfcri f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel f2_cbvmpt2x p_nfan e2_cbvmpt2x f2_cbvmpt2x i0_cbvmpt2x a_sup_set_class f6_cbvmpt2x p_nfeq2 f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f6_cbvmpt2x a_wceq f2_cbvmpt2x p_nfan f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f3_cbvmpt2x p_nfv f3_cbvmpt2x f5_cbvmpt2x p_nfcv f3_cbvmpt2x f1_cbvmpt2x f5_cbvmpt2x p_nfcri f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel f3_cbvmpt2x p_nfan e3_cbvmpt2x f3_cbvmpt2x i0_cbvmpt2x a_sup_set_class f6_cbvmpt2x p_nfeq2 f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f6_cbvmpt2x a_wceq f3_cbvmpt2x p_nfan f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f0_cbvmpt2x p_nfv e1_cbvmpt2x f0_cbvmpt2x f3_cbvmpt2x f7_cbvmpt2x p_nfcri f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel f0_cbvmpt2x p_nfan e4_cbvmpt2x f0_cbvmpt2x i0_cbvmpt2x a_sup_set_class f8_cbvmpt2x p_nfeq2 f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f8_cbvmpt2x a_wceq f0_cbvmpt2x p_nfan f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel a_wa f1_cbvmpt2x p_nfv e5_cbvmpt2x f1_cbvmpt2x i0_cbvmpt2x a_sup_set_class f8_cbvmpt2x p_nfeq2 f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f8_cbvmpt2x a_wceq f1_cbvmpt2x p_nfan f0_cbvmpt2x a_sup_set_class f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x p_eleq1 f0_cbvmpt2x a_sup_set_class f2_cbvmpt2x a_sup_set_class a_wceq f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel a_wb f1_cbvmpt2x a_sup_set_class f3_cbvmpt2x a_sup_set_class a_wceq p_adantr e6_cbvmpt2x f0_cbvmpt2x a_sup_set_class f2_cbvmpt2x a_sup_set_class a_wceq f5_cbvmpt2x f7_cbvmpt2x f1_cbvmpt2x a_sup_set_class p_eleq2d f1_cbvmpt2x a_sup_set_class f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x p_eleq1 f0_cbvmpt2x a_sup_set_class f2_cbvmpt2x a_sup_set_class a_wceq f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f3_cbvmpt2x a_sup_set_class a_wceq f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel p_sylan9bb f0_cbvmpt2x a_sup_set_class f2_cbvmpt2x a_sup_set_class a_wceq f1_cbvmpt2x a_sup_set_class f3_cbvmpt2x a_sup_set_class a_wceq a_wa f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel p_anbi12d e7_cbvmpt2x f0_cbvmpt2x a_sup_set_class f2_cbvmpt2x a_sup_set_class a_wceq f1_cbvmpt2x a_sup_set_class f3_cbvmpt2x a_sup_set_class a_wceq a_wa f6_cbvmpt2x f8_cbvmpt2x i0_cbvmpt2x a_sup_set_class p_eqeq2d f0_cbvmpt2x a_sup_set_class f2_cbvmpt2x a_sup_set_class a_wceq f1_cbvmpt2x a_sup_set_class f3_cbvmpt2x a_sup_set_class a_wceq a_wa f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel a_wa f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f6_cbvmpt2x a_wceq i0_cbvmpt2x a_sup_set_class f8_cbvmpt2x a_wceq p_anbi12d f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f6_cbvmpt2x a_wceq a_wa f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f8_cbvmpt2x a_wceq a_wa f0_cbvmpt2x f1_cbvmpt2x i0_cbvmpt2x f2_cbvmpt2x f3_cbvmpt2x p_cbvoprab12 f0_cbvmpt2x f1_cbvmpt2x i0_cbvmpt2x f4_cbvmpt2x f5_cbvmpt2x f6_cbvmpt2x a_df-mpt2 f2_cbvmpt2x f3_cbvmpt2x i0_cbvmpt2x f4_cbvmpt2x f7_cbvmpt2x f8_cbvmpt2x a_df-mpt2 f0_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f1_cbvmpt2x a_sup_set_class f5_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f6_cbvmpt2x a_wceq a_wa f0_cbvmpt2x f1_cbvmpt2x i0_cbvmpt2x a_coprab f2_cbvmpt2x a_sup_set_class f4_cbvmpt2x a_wcel f3_cbvmpt2x a_sup_set_class f7_cbvmpt2x a_wcel a_wa i0_cbvmpt2x a_sup_set_class f8_cbvmpt2x a_wceq a_wa f2_cbvmpt2x f3_cbvmpt2x i0_cbvmpt2x a_coprab f0_cbvmpt2x f1_cbvmpt2x f4_cbvmpt2x f5_cbvmpt2x f6_cbvmpt2x a_cmpt2 f2_cbvmpt2x f3_cbvmpt2x f4_cbvmpt2x f7_cbvmpt2x f8_cbvmpt2x a_cmpt2 p_3eqtr4i $.
$}

$(Rule to change the bound variable in a maps-to function, using implicit
       substitution.  (Contributed by NM, 17-Dec-2013.) $)

${
	$v x y z w A B C D  $.
	$d w x y z A  $.
	$d w x y z B  $.
	f0_cbvmpt2 $f set x $.
	f1_cbvmpt2 $f set y $.
	f2_cbvmpt2 $f set z $.
	f3_cbvmpt2 $f set w $.
	f4_cbvmpt2 $f class A $.
	f5_cbvmpt2 $f class B $.
	f6_cbvmpt2 $f class C $.
	f7_cbvmpt2 $f class D $.
	e0_cbvmpt2 $e |- F/_ z C $.
	e1_cbvmpt2 $e |- F/_ w C $.
	e2_cbvmpt2 $e |- F/_ x D $.
	e3_cbvmpt2 $e |- F/_ y D $.
	e4_cbvmpt2 $e |- ( ( x = z /\ y = w ) -> C = D ) $.
	p_cbvmpt2 $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. B |-> D ) $= f2_cbvmpt2 f5_cbvmpt2 p_nfcv f0_cbvmpt2 f5_cbvmpt2 p_nfcv e0_cbvmpt2 e1_cbvmpt2 e2_cbvmpt2 e3_cbvmpt2 f0_cbvmpt2 a_sup_set_class f2_cbvmpt2 a_sup_set_class a_wceq f5_cbvmpt2 p_eqidd e4_cbvmpt2 f0_cbvmpt2 f1_cbvmpt2 f2_cbvmpt2 f3_cbvmpt2 f4_cbvmpt2 f5_cbvmpt2 f6_cbvmpt2 f5_cbvmpt2 f7_cbvmpt2 p_cbvmpt2x $.
$}

$(Rule to change the bound variable in a maps-to function, using implicit
       substitution.  With a longer proof analogous to ~ cbvmpt , some distinct
       variable requirements could be eliminated.  (Contributed by NM,
       11-Jun-2013.) $)

${
	$v x y z w A B C D E  $.
	$d w x y z A  $.
	$d w x y z B  $.
	$d w z C  $.
	$d x y D  $.
	f0_cbvmpt2v $f set x $.
	f1_cbvmpt2v $f set y $.
	f2_cbvmpt2v $f set z $.
	f3_cbvmpt2v $f set w $.
	f4_cbvmpt2v $f class A $.
	f5_cbvmpt2v $f class B $.
	f6_cbvmpt2v $f class C $.
	f7_cbvmpt2v $f class D $.
	f8_cbvmpt2v $f class E $.
	e0_cbvmpt2v $e |- ( x = z -> C = E ) $.
	e1_cbvmpt2v $e |- ( y = w -> E = D ) $.
	p_cbvmpt2v $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. B |-> D ) $= f2_cbvmpt2v f6_cbvmpt2v p_nfcv f3_cbvmpt2v f6_cbvmpt2v p_nfcv f0_cbvmpt2v f7_cbvmpt2v p_nfcv f1_cbvmpt2v f7_cbvmpt2v p_nfcv e0_cbvmpt2v e1_cbvmpt2v f0_cbvmpt2v a_sup_set_class f2_cbvmpt2v a_sup_set_class a_wceq f1_cbvmpt2v a_sup_set_class f3_cbvmpt2v a_sup_set_class a_wceq f6_cbvmpt2v f8_cbvmpt2v f7_cbvmpt2v p_sylan9eq f0_cbvmpt2v f1_cbvmpt2v f2_cbvmpt2v f3_cbvmpt2v f4_cbvmpt2v f5_cbvmpt2v f6_cbvmpt2v f7_cbvmpt2v p_cbvmpt2 $.
$}

$(Eliminate a hypothesis which is a predicate expressing membership in the
       result of an operator (deduction version).  See ~ ghomgrplem for an
       example of its use.  (Contributed by Paul Chapman, 25-Mar-2008.) $)

${
	$v ph A B C F X Y Z  $.
	f0_elimdelov $f wff ph $.
	f1_elimdelov $f class A $.
	f2_elimdelov $f class B $.
	f3_elimdelov $f class C $.
	f4_elimdelov $f class F $.
	f5_elimdelov $f class X $.
	f6_elimdelov $f class Y $.
	f7_elimdelov $f class Z $.
	e0_elimdelov $e |- ( ph -> C e. ( A F B ) ) $.
	e1_elimdelov $e |- Z e. ( X F Y ) $.
	p_elimdelov $p |- if ( ph , C , Z ) e. ( if ( ph , A , X ) F if ( ph , B , Y ) ) $= f0_elimdelov f3_elimdelov f7_elimdelov p_iftrue e0_elimdelov f0_elimdelov f0_elimdelov f3_elimdelov f7_elimdelov a_cif f3_elimdelov f1_elimdelov f2_elimdelov f4_elimdelov a_co p_eqeltrd f0_elimdelov f1_elimdelov f5_elimdelov p_iftrue f0_elimdelov f2_elimdelov f6_elimdelov p_iftrue f0_elimdelov f0_elimdelov f1_elimdelov f5_elimdelov a_cif f1_elimdelov f0_elimdelov f2_elimdelov f6_elimdelov a_cif f2_elimdelov f4_elimdelov p_oveq12d f0_elimdelov f0_elimdelov f3_elimdelov f7_elimdelov a_cif f1_elimdelov f2_elimdelov f4_elimdelov a_co f0_elimdelov f1_elimdelov f5_elimdelov a_cif f0_elimdelov f2_elimdelov f6_elimdelov a_cif f4_elimdelov a_co p_eleqtrrd f0_elimdelov f3_elimdelov f7_elimdelov p_iffalse e1_elimdelov f0_elimdelov a_wn f0_elimdelov f3_elimdelov f7_elimdelov a_cif f7_elimdelov f5_elimdelov f6_elimdelov f4_elimdelov a_co p_syl6eqel f0_elimdelov f1_elimdelov f5_elimdelov p_iffalse f0_elimdelov f2_elimdelov f6_elimdelov p_iffalse f0_elimdelov a_wn f0_elimdelov f1_elimdelov f5_elimdelov a_cif f5_elimdelov f0_elimdelov f2_elimdelov f6_elimdelov a_cif f6_elimdelov f4_elimdelov p_oveq12d f0_elimdelov a_wn f0_elimdelov f3_elimdelov f7_elimdelov a_cif f5_elimdelov f6_elimdelov f4_elimdelov a_co f0_elimdelov f1_elimdelov f5_elimdelov a_cif f0_elimdelov f2_elimdelov f6_elimdelov a_cif f4_elimdelov a_co p_eleqtrrd f0_elimdelov f0_elimdelov f3_elimdelov f7_elimdelov a_cif f0_elimdelov f1_elimdelov f5_elimdelov a_cif f0_elimdelov f2_elimdelov f6_elimdelov a_cif f4_elimdelov a_co a_wcel p_pm2.61i $.
$}

$(The domain of an operation class abstraction.  (Contributed by NM,
       17-Mar-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)

${
	$v ph x y z  $.
	$d x z w  $.
	$d y z w  $.
	$d w ph  $.
	f0_dmoprab $f wff ph $.
	f1_dmoprab $f set x $.
	f2_dmoprab $f set y $.
	f3_dmoprab $f set z $.
	i0_dmoprab $f set w $.
	p_dmoprab $p |- dom { <. <. x , y >. , z >. | ph } = { <. x , y >. | E. z ph } $= f0_dmoprab f1_dmoprab f2_dmoprab f3_dmoprab i0_dmoprab p_dfoprab2 f0_dmoprab f1_dmoprab f2_dmoprab f3_dmoprab a_coprab i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f2_dmoprab a_wex f1_dmoprab a_wex i0_dmoprab f3_dmoprab a_copab p_dmeqi i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f2_dmoprab a_wex f1_dmoprab a_wex i0_dmoprab f3_dmoprab p_dmopab i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f3_dmoprab f1_dmoprab f2_dmoprab p_exrot3 i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab f3_dmoprab p_19.42v i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f3_dmoprab a_wex i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab f3_dmoprab a_wex a_wa f1_dmoprab f2_dmoprab p_2exbii i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f2_dmoprab a_wex f1_dmoprab a_wex f3_dmoprab a_wex i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f3_dmoprab a_wex f2_dmoprab a_wex f1_dmoprab a_wex i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab f3_dmoprab a_wex a_wa f2_dmoprab a_wex f1_dmoprab a_wex p_bitri i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f2_dmoprab a_wex f1_dmoprab a_wex f3_dmoprab a_wex i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab f3_dmoprab a_wex a_wa f2_dmoprab a_wex f1_dmoprab a_wex i0_dmoprab p_abbii f0_dmoprab f3_dmoprab a_wex f1_dmoprab f2_dmoprab i0_dmoprab a_df-opab i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f2_dmoprab a_wex f1_dmoprab a_wex f3_dmoprab a_wex i0_dmoprab a_cab i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab f3_dmoprab a_wex a_wa f2_dmoprab a_wex f1_dmoprab a_wex i0_dmoprab a_cab f0_dmoprab f3_dmoprab a_wex f1_dmoprab f2_dmoprab a_copab p_eqtr4i f0_dmoprab f1_dmoprab f2_dmoprab f3_dmoprab a_coprab a_cdm i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f2_dmoprab a_wex f1_dmoprab a_wex i0_dmoprab f3_dmoprab a_copab a_cdm i0_dmoprab a_sup_set_class f1_dmoprab a_sup_set_class f2_dmoprab a_sup_set_class a_cop a_wceq f0_dmoprab a_wa f2_dmoprab a_wex f1_dmoprab a_wex f3_dmoprab a_wex i0_dmoprab a_cab f0_dmoprab f3_dmoprab a_wex f1_dmoprab f2_dmoprab a_copab p_3eqtri $.
$}

$(The domain of an operation class abstraction.  (Contributed by NM,
       24-Aug-1995.) $)

${
	$v ph x y z A B  $.
	$d x y z A  $.
	$d x y z B  $.
	f0_dmoprabss $f wff ph $.
	f1_dmoprabss $f set x $.
	f2_dmoprabss $f set y $.
	f3_dmoprabss $f set z $.
	f4_dmoprabss $f class A $.
	f5_dmoprabss $f class B $.
	p_dmoprabss $p |- dom { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } C_ ( A X. B ) $= f1_dmoprabss a_sup_set_class f4_dmoprabss a_wcel f2_dmoprabss a_sup_set_class f5_dmoprabss a_wcel a_wa f0_dmoprabss a_wa f1_dmoprabss f2_dmoprabss f3_dmoprabss p_dmoprab f1_dmoprabss a_sup_set_class f4_dmoprabss a_wcel f2_dmoprabss a_sup_set_class f5_dmoprabss a_wcel a_wa f0_dmoprabss f3_dmoprabss p_19.42v f1_dmoprabss a_sup_set_class f4_dmoprabss a_wcel f2_dmoprabss a_sup_set_class f5_dmoprabss a_wcel a_wa f0_dmoprabss a_wa f3_dmoprabss a_wex f1_dmoprabss a_sup_set_class f4_dmoprabss a_wcel f2_dmoprabss a_sup_set_class f5_dmoprabss a_wcel a_wa f0_dmoprabss f3_dmoprabss a_wex a_wa f1_dmoprabss f2_dmoprabss p_opabbii f0_dmoprabss f3_dmoprabss a_wex f1_dmoprabss f2_dmoprabss f4_dmoprabss f5_dmoprabss p_opabssxp f1_dmoprabss a_sup_set_class f4_dmoprabss a_wcel f2_dmoprabss a_sup_set_class f5_dmoprabss a_wcel a_wa f0_dmoprabss a_wa f3_dmoprabss a_wex f1_dmoprabss f2_dmoprabss a_copab f1_dmoprabss a_sup_set_class f4_dmoprabss a_wcel f2_dmoprabss a_sup_set_class f5_dmoprabss a_wcel a_wa f0_dmoprabss f3_dmoprabss a_wex a_wa f1_dmoprabss f2_dmoprabss a_copab f4_dmoprabss f5_dmoprabss a_cxp p_eqsstri f1_dmoprabss a_sup_set_class f4_dmoprabss a_wcel f2_dmoprabss a_sup_set_class f5_dmoprabss a_wcel a_wa f0_dmoprabss a_wa f1_dmoprabss f2_dmoprabss f3_dmoprabss a_coprab a_cdm f1_dmoprabss a_sup_set_class f4_dmoprabss a_wcel f2_dmoprabss a_sup_set_class f5_dmoprabss a_wcel a_wa f0_dmoprabss a_wa f3_dmoprabss a_wex f1_dmoprabss f2_dmoprabss a_copab f4_dmoprabss f5_dmoprabss a_cxp p_eqsstri $.
$}

$(The range of an operation class abstraction.  (Contributed by NM,
       30-Aug-2004.)  (Revised by David Abernethy, 19-Apr-2013.) $)

${
	$v ph x y z  $.
	$d x z w  $.
	$d y z w  $.
	$d w ph  $.
	f0_rnoprab $f wff ph $.
	f1_rnoprab $f set x $.
	f2_rnoprab $f set y $.
	f3_rnoprab $f set z $.
	i0_rnoprab $f set w $.
	p_rnoprab $p |- ran { <. <. x , y >. , z >. | ph } = { z | E. x E. y ph } $= f0_rnoprab f1_rnoprab f2_rnoprab f3_rnoprab i0_rnoprab p_dfoprab2 f0_rnoprab f1_rnoprab f2_rnoprab f3_rnoprab a_coprab i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa f2_rnoprab a_wex f1_rnoprab a_wex i0_rnoprab f3_rnoprab a_copab p_rneqi i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa f2_rnoprab a_wex f1_rnoprab a_wex i0_rnoprab f3_rnoprab p_rnopab i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa i0_rnoprab f1_rnoprab f2_rnoprab p_exrot3 f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class p_opex i0_rnoprab f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop p_isseti i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab i0_rnoprab p_19.41v i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa i0_rnoprab a_wex i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq i0_rnoprab a_wex f0_rnoprab p_mpbiran i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa i0_rnoprab a_wex f0_rnoprab f1_rnoprab f2_rnoprab p_2exbii i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa f2_rnoprab a_wex f1_rnoprab a_wex i0_rnoprab a_wex i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa i0_rnoprab a_wex f2_rnoprab a_wex f1_rnoprab a_wex f0_rnoprab f2_rnoprab a_wex f1_rnoprab a_wex p_bitri i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa f2_rnoprab a_wex f1_rnoprab a_wex i0_rnoprab a_wex f0_rnoprab f2_rnoprab a_wex f1_rnoprab a_wex f3_rnoprab p_abbii f0_rnoprab f1_rnoprab f2_rnoprab f3_rnoprab a_coprab a_crn i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa f2_rnoprab a_wex f1_rnoprab a_wex i0_rnoprab f3_rnoprab a_copab a_crn i0_rnoprab a_sup_set_class f1_rnoprab a_sup_set_class f2_rnoprab a_sup_set_class a_cop a_wceq f0_rnoprab a_wa f2_rnoprab a_wex f1_rnoprab a_wex i0_rnoprab a_wex f3_rnoprab a_cab f0_rnoprab f2_rnoprab a_wex f1_rnoprab a_wex f3_rnoprab a_cab p_3eqtri $.
$}

$(The range of a restricted operation class abstraction.  (Contributed by
       Scott Fenton, 21-Mar-2012.) $)

${
	$v ph x y z A B  $.
	$d A y  $.
	$d x y z  $.
	f0_rnoprab2 $f wff ph $.
	f1_rnoprab2 $f set x $.
	f2_rnoprab2 $f set y $.
	f3_rnoprab2 $f set z $.
	f4_rnoprab2 $f class A $.
	f5_rnoprab2 $f class B $.
	p_rnoprab2 $p |- ran { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } = { z | E. x e. A E. y e. B ph } $= f1_rnoprab2 a_sup_set_class f4_rnoprab2 a_wcel f2_rnoprab2 a_sup_set_class f5_rnoprab2 a_wcel a_wa f0_rnoprab2 a_wa f1_rnoprab2 f2_rnoprab2 f3_rnoprab2 p_rnoprab f0_rnoprab2 f1_rnoprab2 f2_rnoprab2 f4_rnoprab2 f5_rnoprab2 p_r2ex f0_rnoprab2 f2_rnoprab2 f5_rnoprab2 a_wrex f1_rnoprab2 f4_rnoprab2 a_wrex f1_rnoprab2 a_sup_set_class f4_rnoprab2 a_wcel f2_rnoprab2 a_sup_set_class f5_rnoprab2 a_wcel a_wa f0_rnoprab2 a_wa f2_rnoprab2 a_wex f1_rnoprab2 a_wex f3_rnoprab2 p_abbii f1_rnoprab2 a_sup_set_class f4_rnoprab2 a_wcel f2_rnoprab2 a_sup_set_class f5_rnoprab2 a_wcel a_wa f0_rnoprab2 a_wa f1_rnoprab2 f2_rnoprab2 f3_rnoprab2 a_coprab a_crn f1_rnoprab2 a_sup_set_class f4_rnoprab2 a_wcel f2_rnoprab2 a_sup_set_class f5_rnoprab2 a_wcel a_wa f0_rnoprab2 a_wa f2_rnoprab2 a_wex f1_rnoprab2 a_wex f3_rnoprab2 a_cab f0_rnoprab2 f2_rnoprab2 f5_rnoprab2 a_wrex f1_rnoprab2 f4_rnoprab2 a_wrex f3_rnoprab2 a_cab p_eqtr4i $.
$}

$(The domain of an operation class abstraction is a relation.
       (Contributed by NM, 17-Mar-1995.) $)

${
	$v ph x y z  $.
	$d x y z  $.
	f0_reldmoprab $f wff ph $.
	f1_reldmoprab $f set x $.
	f2_reldmoprab $f set y $.
	f3_reldmoprab $f set z $.
	p_reldmoprab $p |- Rel dom { <. <. x , y >. , z >. | ph } $= f0_reldmoprab f1_reldmoprab f2_reldmoprab f3_reldmoprab p_dmoprab f0_reldmoprab f3_reldmoprab a_wex f1_reldmoprab f2_reldmoprab f0_reldmoprab f1_reldmoprab f2_reldmoprab f3_reldmoprab a_coprab a_cdm p_relopabi $.
$}

$(Structure of an operation class abstraction.  (Contributed by NM,
       28-Nov-2006.) $)

${
	$v ph x y z  $.
	$d x y z  $.
	f0_oprabss $f wff ph $.
	f1_oprabss $f set x $.
	f2_oprabss $f set y $.
	f3_oprabss $f set z $.
	p_oprabss $p |- { <. <. x , y >. , z >. | ph } C_ ( ( _V X. _V ) X. _V ) $= f0_oprabss f1_oprabss f2_oprabss f3_oprabss p_reloprab f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab p_relssdmrn f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_wrel f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_cdm f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_crn a_cxp a_wss a_ax-mp f0_oprabss f1_oprabss f2_oprabss f3_oprabss p_reldmoprab f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_cdm a_df-rel f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_cdm a_wrel f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_cdm a_cvv a_cvv a_cxp a_wss p_mpbi f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_crn p_ssv f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_cdm a_cvv a_cvv a_cxp f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_crn a_cvv p_xpss12 f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_cdm a_cvv a_cvv a_cxp a_wss f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_crn a_cvv a_wss f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_cdm f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_crn a_cxp a_cvv a_cvv a_cxp a_cvv a_cxp a_wss p_mp2an f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_cdm f0_oprabss f1_oprabss f2_oprabss f3_oprabss a_coprab a_crn a_cxp a_cvv a_cvv a_cxp a_cvv a_cxp p_sstri $.
$}

$(The law of concretion for operation class abstraction.  Compare
       ~ elopab .  (Contributed by NM, 14-Sep-1999.)  (Unnecessary distinct
       variable restrictions were removed by David Abernethy, 19-Jun-2012.)
       (Revised by Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps x y z A B C V W X  $.
	$d x y z w A  $.
	$d x y z w B  $.
	$d x y z w C  $.
	$d w ph  $.
	$d x y z w ps  $.
	f0_eloprabga $f wff ph $.
	f1_eloprabga $f wff ps $.
	f2_eloprabga $f set x $.
	f3_eloprabga $f set y $.
	f4_eloprabga $f set z $.
	f5_eloprabga $f class A $.
	f6_eloprabga $f class B $.
	f7_eloprabga $f class C $.
	f8_eloprabga $f class V $.
	f9_eloprabga $f class W $.
	f10_eloprabga $f class X $.
	i0_eloprabga $f set w $.
	e0_eloprabga $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	p_eloprabga $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( <. <. A , B >. , C >. e. { <. <. x , y >. , z >. | ph } <-> ps ) ) $= f5_eloprabga f8_eloprabga p_elex f6_eloprabga f9_eloprabga p_elex f7_eloprabga f10_eloprabga p_elex f5_eloprabga f6_eloprabga a_cop f7_eloprabga p_opex f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq p_simpr f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq a_wa i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop p_eqeq1d f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop p_eqcom f2_eloprabga p_vex f3_eloprabga p_vex f4_eloprabga p_vex f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga f4_eloprabga a_sup_set_class f7_eloprabga p_otth2 f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a p_bitri f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq a_wa i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a p_syl6bb f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq a_wa i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f0_eloprabga p_anbi1d e0_eloprabga f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f0_eloprabga f1_eloprabga p_pm5.32i f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq a_wa i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f0_eloprabga a_wa f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f1_eloprabga a_wa p_syl6bb f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq a_wa i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f1_eloprabga a_wa f2_eloprabga f3_eloprabga f4_eloprabga p_3exbidv f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga i0_eloprabga a_df-oprab f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex i0_eloprabga a_cab i0_eloprabga a_sup_set_class p_eleq2i i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex i0_eloprabga p_abid i0_eloprabga a_sup_set_class f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab a_wcel i0_eloprabga a_sup_set_class i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex i0_eloprabga a_cab a_wcel i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex p_bitr2i i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab p_eleq1 i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex i0_eloprabga a_sup_set_class f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab a_wcel i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab a_wcel p_syl5bb i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab a_wcel a_wb f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a p_adantl f2_eloprabga f5_eloprabga a_cvv p_elisset f3_eloprabga f6_eloprabga a_cvv p_elisset f4_eloprabga f7_eloprabga a_cvv p_elisset f5_eloprabga a_cvv a_wcel f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f2_eloprabga a_wex f6_eloprabga a_cvv a_wcel f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f3_eloprabga a_wex f7_eloprabga a_cvv a_wcel f4_eloprabga a_sup_set_class f7_eloprabga a_wceq f4_eloprabga a_wex p_3anim123i f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq f2_eloprabga f3_eloprabga f4_eloprabga p_eeeanv f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f2_eloprabga a_wex f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f3_eloprabga a_wex f4_eloprabga a_sup_set_class f7_eloprabga a_wceq f4_eloprabga a_wex a_w3a f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex p_sylibr f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex f1_eloprabga p_biantrurd f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f1_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga p_19.41vvv f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a f1_eloprabga f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex f1_eloprabga a_wa f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f1_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex p_syl6rbbr f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f1_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex f1_eloprabga a_wb i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq p_adantr f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq a_wa i0_eloprabga a_sup_set_class f2_eloprabga a_sup_set_class f3_eloprabga a_sup_set_class a_cop f4_eloprabga a_sup_set_class a_cop a_wceq f0_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex f2_eloprabga a_sup_set_class f5_eloprabga a_wceq f3_eloprabga a_sup_set_class f6_eloprabga a_wceq f4_eloprabga a_sup_set_class f7_eloprabga a_wceq a_w3a f1_eloprabga a_wa f4_eloprabga a_wex f3_eloprabga a_wex f2_eloprabga a_wex f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab a_wcel f1_eloprabga p_3bitr3d f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a i0_eloprabga a_sup_set_class f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop a_wceq f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab a_wcel f1_eloprabga a_wb p_expcom f5_eloprabga a_cvv a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga a_cvv a_wcel a_w3a f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab a_wcel f1_eloprabga a_wb a_wi i0_eloprabga f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop p_vtocle f5_eloprabga f8_eloprabga a_wcel f5_eloprabga a_cvv a_wcel f6_eloprabga f9_eloprabga a_wcel f6_eloprabga a_cvv a_wcel f7_eloprabga f10_eloprabga a_wcel f7_eloprabga a_cvv a_wcel f5_eloprabga f6_eloprabga a_cop f7_eloprabga a_cop f0_eloprabga f2_eloprabga f3_eloprabga f4_eloprabga a_coprab a_wcel f1_eloprabga a_wb p_syl3an $.
$}

$(The law of concretion for operation class abstraction.  Compare
       ~ elopab .  (Contributed by NM, 14-Sep-1999.)  (Revised by David
       Abernethy, 19-Jun-2012.) $)

${
	$v ph ps ch th x y z A B C V W X  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d ph  $.
	$d x y z th  $.
	f0_eloprabg $f wff ph $.
	f1_eloprabg $f wff ps $.
	f2_eloprabg $f wff ch $.
	f3_eloprabg $f wff th $.
	f4_eloprabg $f set x $.
	f5_eloprabg $f set y $.
	f6_eloprabg $f set z $.
	f7_eloprabg $f class A $.
	f8_eloprabg $f class B $.
	f9_eloprabg $f class C $.
	f10_eloprabg $f class V $.
	f11_eloprabg $f class W $.
	f12_eloprabg $f class X $.
	e0_eloprabg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_eloprabg $e |- ( y = B -> ( ps <-> ch ) ) $.
	e2_eloprabg $e |- ( z = C -> ( ch <-> th ) ) $.
	p_eloprabg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( <. <. A , B >. , C >. e. { <. <. x , y >. , z >. | ph } <-> th ) ) $= e0_eloprabg e1_eloprabg e2_eloprabg f4_eloprabg a_sup_set_class f7_eloprabg a_wceq f0_eloprabg f1_eloprabg f5_eloprabg a_sup_set_class f8_eloprabg a_wceq f2_eloprabg f6_eloprabg a_sup_set_class f9_eloprabg a_wceq f3_eloprabg p_syl3an9b f0_eloprabg f3_eloprabg f4_eloprabg f5_eloprabg f6_eloprabg f7_eloprabg f8_eloprabg f9_eloprabg f10_eloprabg f11_eloprabg f12_eloprabg p_eloprabga $.
$}

$(Inference of operation class abstraction subclass from implication.
       (Contributed by NM, 11-Nov-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) $)

${
	$v ph ps x y z  $.
	$d ph w  $.
	$d ps w  $.
	$d x z w  $.
	$d y z w  $.
	f0_ssoprab2i $f wff ph $.
	f1_ssoprab2i $f wff ps $.
	f2_ssoprab2i $f set x $.
	f3_ssoprab2i $f set y $.
	f4_ssoprab2i $f set z $.
	i0_ssoprab2i $f set w $.
	e0_ssoprab2i $e |- ( ph -> ps ) $.
	p_ssoprab2i $p |- { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } $= e0_ssoprab2i f0_ssoprab2i f1_ssoprab2i i0_ssoprab2i a_sup_set_class f2_ssoprab2i a_sup_set_class f3_ssoprab2i a_sup_set_class a_cop a_wceq p_anim2i i0_ssoprab2i a_sup_set_class f2_ssoprab2i a_sup_set_class f3_ssoprab2i a_sup_set_class a_cop a_wceq f0_ssoprab2i a_wa i0_ssoprab2i a_sup_set_class f2_ssoprab2i a_sup_set_class f3_ssoprab2i a_sup_set_class a_cop a_wceq f1_ssoprab2i a_wa f2_ssoprab2i f3_ssoprab2i p_2eximi i0_ssoprab2i a_sup_set_class f2_ssoprab2i a_sup_set_class f3_ssoprab2i a_sup_set_class a_cop a_wceq f0_ssoprab2i a_wa f3_ssoprab2i a_wex f2_ssoprab2i a_wex i0_ssoprab2i a_sup_set_class f2_ssoprab2i a_sup_set_class f3_ssoprab2i a_sup_set_class a_cop a_wceq f1_ssoprab2i a_wa f3_ssoprab2i a_wex f2_ssoprab2i a_wex i0_ssoprab2i f4_ssoprab2i p_ssopab2i f0_ssoprab2i f2_ssoprab2i f3_ssoprab2i f4_ssoprab2i i0_ssoprab2i p_dfoprab2 f1_ssoprab2i f2_ssoprab2i f3_ssoprab2i f4_ssoprab2i i0_ssoprab2i p_dfoprab2 i0_ssoprab2i a_sup_set_class f2_ssoprab2i a_sup_set_class f3_ssoprab2i a_sup_set_class a_cop a_wceq f0_ssoprab2i a_wa f3_ssoprab2i a_wex f2_ssoprab2i a_wex i0_ssoprab2i f4_ssoprab2i a_copab i0_ssoprab2i a_sup_set_class f2_ssoprab2i a_sup_set_class f3_ssoprab2i a_sup_set_class a_cop a_wceq f1_ssoprab2i a_wa f3_ssoprab2i a_wex f2_ssoprab2i a_wex i0_ssoprab2i f4_ssoprab2i a_copab f0_ssoprab2i f2_ssoprab2i f3_ssoprab2i f4_ssoprab2i a_coprab f1_ssoprab2i f2_ssoprab2i f3_ssoprab2i f4_ssoprab2i a_coprab p_3sstr4i $.
$}

$(Operation with universal domain in maps-to notation.  (Contributed by
       NM, 16-Aug-2013.) $)

${
	$v x y z C  $.
	$d x z  $.
	$d y z  $.
	$d z C  $.
	f0_mpt2v $f set x $.
	f1_mpt2v $f set y $.
	f2_mpt2v $f set z $.
	f3_mpt2v $f class C $.
	p_mpt2v $p |- ( x e. _V , y e. _V |-> C ) = { <. <. x , y >. , z >. | z = C } $= f0_mpt2v f1_mpt2v f2_mpt2v a_cvv a_cvv f3_mpt2v a_df-mpt2 f0_mpt2v p_vex f1_mpt2v p_vex f0_mpt2v a_sup_set_class a_cvv a_wcel f1_mpt2v a_sup_set_class a_cvv a_wcel p_pm3.2i f0_mpt2v a_sup_set_class a_cvv a_wcel f1_mpt2v a_sup_set_class a_cvv a_wcel a_wa f2_mpt2v a_sup_set_class f3_mpt2v a_wceq p_biantrur f2_mpt2v a_sup_set_class f3_mpt2v a_wceq f0_mpt2v a_sup_set_class a_cvv a_wcel f1_mpt2v a_sup_set_class a_cvv a_wcel a_wa f2_mpt2v a_sup_set_class f3_mpt2v a_wceq a_wa f0_mpt2v f1_mpt2v f2_mpt2v p_oprabbii f0_mpt2v f1_mpt2v a_cvv a_cvv f3_mpt2v a_cmpt2 f0_mpt2v a_sup_set_class a_cvv a_wcel f1_mpt2v a_sup_set_class a_cvv a_wcel a_wa f2_mpt2v a_sup_set_class f3_mpt2v a_wceq a_wa f0_mpt2v f1_mpt2v f2_mpt2v a_coprab f2_mpt2v a_sup_set_class f3_mpt2v a_wceq f0_mpt2v f1_mpt2v f2_mpt2v a_coprab p_eqtr4i $.
$}

$(Express a two-argument function as a one-argument function, or
       vice-versa.  In this version ` B ( x ) ` is not assumed to be constant
       w.r.t ` x ` .  (Contributed by Mario Carneiro, 29-Dec-2014.) $)

${
	$v x y z A B C D  $.
	$d w x y z A  $.
	$d w y z B  $.
	$d w x y C  $.
	$d w z D  $.
	f0_mpt2mptx $f set x $.
	f1_mpt2mptx $f set y $.
	f2_mpt2mptx $f set z $.
	f3_mpt2mptx $f class A $.
	f4_mpt2mptx $f class B $.
	f5_mpt2mptx $f class C $.
	f6_mpt2mptx $f class D $.
	i0_mpt2mptx $f set w $.
	e0_mpt2mptx $e |- ( z = <. x , y >. -> C = D ) $.
	p_mpt2mptx $p |- ( z e. U_ x e. A ( { x } X. B ) |-> C ) = ( x e. A , y e. B |-> D ) $= f2_mpt2mptx i0_mpt2mptx f0_mpt2mptx f3_mpt2mptx f0_mpt2mptx a_sup_set_class a_csn f4_mpt2mptx a_cxp a_ciun f5_mpt2mptx a_df-mpt f0_mpt2mptx f1_mpt2mptx i0_mpt2mptx f3_mpt2mptx f4_mpt2mptx f6_mpt2mptx a_df-mpt2 f0_mpt2mptx f1_mpt2mptx f3_mpt2mptx f4_mpt2mptx f2_mpt2mptx a_sup_set_class p_eliunxp f2_mpt2mptx a_sup_set_class f0_mpt2mptx f3_mpt2mptx f0_mpt2mptx a_sup_set_class a_csn f4_mpt2mptx a_cxp a_ciun a_wcel f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa a_wa f1_mpt2mptx a_wex f0_mpt2mptx a_wex i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq p_anbi1i f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa a_wa i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq f0_mpt2mptx f1_mpt2mptx p_19.41vv f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq p_anass e0_mpt2mptx f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f5_mpt2mptx f6_mpt2mptx i0_mpt2mptx a_sup_set_class p_eqeq2d f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa p_anbi2d f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa p_pm5.32i f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa a_wa i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa a_wa f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa a_wa p_bitri f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa a_wa i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa a_wa f0_mpt2mptx f1_mpt2mptx p_2exbii f2_mpt2mptx a_sup_set_class f0_mpt2mptx f3_mpt2mptx f0_mpt2mptx a_sup_set_class a_csn f4_mpt2mptx a_cxp a_ciun a_wcel i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa a_wa f1_mpt2mptx a_wex f0_mpt2mptx a_wex i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa a_wa i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f1_mpt2mptx a_wex f0_mpt2mptx a_wex f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa a_wa f1_mpt2mptx a_wex f0_mpt2mptx a_wex p_3bitr2i f2_mpt2mptx a_sup_set_class f0_mpt2mptx f3_mpt2mptx f0_mpt2mptx a_sup_set_class a_csn f4_mpt2mptx a_cxp a_ciun a_wcel i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa a_wa f1_mpt2mptx a_wex f0_mpt2mptx a_wex f2_mpt2mptx i0_mpt2mptx p_opabbii f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa f0_mpt2mptx f1_mpt2mptx i0_mpt2mptx f2_mpt2mptx p_dfoprab2 f2_mpt2mptx a_sup_set_class f0_mpt2mptx f3_mpt2mptx f0_mpt2mptx a_sup_set_class a_csn f4_mpt2mptx a_cxp a_ciun a_wcel i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f2_mpt2mptx i0_mpt2mptx a_copab f2_mpt2mptx a_sup_set_class f0_mpt2mptx a_sup_set_class f1_mpt2mptx a_sup_set_class a_cop a_wceq f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa a_wa f1_mpt2mptx a_wex f0_mpt2mptx a_wex f2_mpt2mptx i0_mpt2mptx a_copab f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa f0_mpt2mptx f1_mpt2mptx i0_mpt2mptx a_coprab p_eqtr4i f0_mpt2mptx f1_mpt2mptx f3_mpt2mptx f4_mpt2mptx f6_mpt2mptx a_cmpt2 f0_mpt2mptx a_sup_set_class f3_mpt2mptx a_wcel f1_mpt2mptx a_sup_set_class f4_mpt2mptx a_wcel a_wa i0_mpt2mptx a_sup_set_class f6_mpt2mptx a_wceq a_wa f0_mpt2mptx f1_mpt2mptx i0_mpt2mptx a_coprab f2_mpt2mptx a_sup_set_class f0_mpt2mptx f3_mpt2mptx f0_mpt2mptx a_sup_set_class a_csn f4_mpt2mptx a_cxp a_ciun a_wcel i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f2_mpt2mptx i0_mpt2mptx a_copab p_eqtr4i f2_mpt2mptx f0_mpt2mptx f3_mpt2mptx f0_mpt2mptx a_sup_set_class a_csn f4_mpt2mptx a_cxp a_ciun f5_mpt2mptx a_cmpt f2_mpt2mptx a_sup_set_class f0_mpt2mptx f3_mpt2mptx f0_mpt2mptx a_sup_set_class a_csn f4_mpt2mptx a_cxp a_ciun a_wcel i0_mpt2mptx a_sup_set_class f5_mpt2mptx a_wceq a_wa f2_mpt2mptx i0_mpt2mptx a_copab f0_mpt2mptx f1_mpt2mptx f3_mpt2mptx f4_mpt2mptx f6_mpt2mptx a_cmpt2 p_eqtr4i $.
$}

$(Express a two-argument function as a one-argument function, or
       vice-versa.  (Contributed by Mario Carneiro, 17-Dec-2013.)  (Revised by
       Mario Carneiro, 29-Dec-2014.) $)

${
	$v x y z A B C D  $.
	$d x y z A  $.
	$d y z B  $.
	$d x y C  $.
	$d z D  $.
	$d x B  $.
	f0_mpt2mpt $f set x $.
	f1_mpt2mpt $f set y $.
	f2_mpt2mpt $f set z $.
	f3_mpt2mpt $f class A $.
	f4_mpt2mpt $f class B $.
	f5_mpt2mpt $f class C $.
	f6_mpt2mpt $f class D $.
	e0_mpt2mpt $e |- ( z = <. x , y >. -> C = D ) $.
	p_mpt2mpt $p |- ( z e. ( A X. B ) |-> C ) = ( x e. A , y e. B |-> D ) $= f0_mpt2mpt f3_mpt2mpt f4_mpt2mpt p_iunxpconst f2_mpt2mpt f0_mpt2mpt f3_mpt2mpt f0_mpt2mpt a_sup_set_class a_csn f4_mpt2mpt a_cxp a_ciun f3_mpt2mpt f4_mpt2mpt a_cxp f5_mpt2mpt p_mpteq1 f0_mpt2mpt f3_mpt2mpt f0_mpt2mpt a_sup_set_class a_csn f4_mpt2mpt a_cxp a_ciun f3_mpt2mpt f4_mpt2mpt a_cxp a_wceq f2_mpt2mpt f0_mpt2mpt f3_mpt2mpt f0_mpt2mpt a_sup_set_class a_csn f4_mpt2mpt a_cxp a_ciun f5_mpt2mpt a_cmpt f2_mpt2mpt f3_mpt2mpt f4_mpt2mpt a_cxp f5_mpt2mpt a_cmpt a_wceq a_ax-mp e0_mpt2mpt f0_mpt2mpt f1_mpt2mpt f2_mpt2mpt f3_mpt2mpt f4_mpt2mpt f5_mpt2mpt f6_mpt2mpt p_mpt2mptx f2_mpt2mpt f0_mpt2mpt f3_mpt2mpt f0_mpt2mpt a_sup_set_class a_csn f4_mpt2mpt a_cxp a_ciun f5_mpt2mpt a_cmpt f2_mpt2mpt f3_mpt2mpt f4_mpt2mpt a_cxp f5_mpt2mpt a_cmpt f0_mpt2mpt f1_mpt2mpt f3_mpt2mpt f4_mpt2mpt f6_mpt2mpt a_cmpt2 p_eqtr3i $.
$}

$(Restriction of an operation class abstraction.  (Contributed by NM,
       10-Feb-2007.) $)

${
	$v ph x y z A B  $.
	$d w x y z A  $.
	$d w x y z B  $.
	$d w ph  $.
	f0_resoprab $f wff ph $.
	f1_resoprab $f set x $.
	f2_resoprab $f set y $.
	f3_resoprab $f set z $.
	f4_resoprab $f class A $.
	f5_resoprab $f class B $.
	i0_resoprab $f set w $.
	p_resoprab $p |- ( { <. <. x , y >. , z >. | ph } |` ( A X. B ) ) = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $= i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa f2_resoprab a_wex f1_resoprab a_wex i0_resoprab f3_resoprab f4_resoprab f5_resoprab a_cxp p_resopab i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa f1_resoprab f2_resoprab p_19.42vv i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab p_an12 i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop f4_resoprab f5_resoprab a_cxp p_eleq1 f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class f4_resoprab f5_resoprab p_opelxp i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop f4_resoprab f5_resoprab a_cxp a_wcel f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa p_syl6bb i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab p_anbi1d i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel f0_resoprab a_wa f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa p_pm5.32i i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa a_wa i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel f0_resoprab a_wa a_wa i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa a_wa p_bitri i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa a_wa i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa a_wa f1_resoprab f2_resoprab p_2exbii i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa f2_resoprab a_wex f1_resoprab a_wex a_wa i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa a_wa f2_resoprab a_wex f1_resoprab a_wex i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa a_wa f2_resoprab a_wex f1_resoprab a_wex p_bitr3i i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa f2_resoprab a_wex f1_resoprab a_wex a_wa i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa a_wa f2_resoprab a_wex f1_resoprab a_wex i0_resoprab f3_resoprab p_opabbii i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa f2_resoprab a_wex f1_resoprab a_wex i0_resoprab f3_resoprab a_copab f4_resoprab f5_resoprab a_cxp a_cres i0_resoprab a_sup_set_class f4_resoprab f5_resoprab a_cxp a_wcel i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa f2_resoprab a_wex f1_resoprab a_wex a_wa i0_resoprab f3_resoprab a_copab i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa a_wa f2_resoprab a_wex f1_resoprab a_wex i0_resoprab f3_resoprab a_copab p_eqtri f0_resoprab f1_resoprab f2_resoprab f3_resoprab i0_resoprab p_dfoprab2 f0_resoprab f1_resoprab f2_resoprab f3_resoprab a_coprab i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa f2_resoprab a_wex f1_resoprab a_wex i0_resoprab f3_resoprab a_copab f4_resoprab f5_resoprab a_cxp p_reseq1i f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa f1_resoprab f2_resoprab f3_resoprab i0_resoprab p_dfoprab2 i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f0_resoprab a_wa f2_resoprab a_wex f1_resoprab a_wex i0_resoprab f3_resoprab a_copab f4_resoprab f5_resoprab a_cxp a_cres i0_resoprab a_sup_set_class f1_resoprab a_sup_set_class f2_resoprab a_sup_set_class a_cop a_wceq f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa a_wa f2_resoprab a_wex f1_resoprab a_wex i0_resoprab f3_resoprab a_copab f0_resoprab f1_resoprab f2_resoprab f3_resoprab a_coprab f4_resoprab f5_resoprab a_cxp a_cres f1_resoprab a_sup_set_class f4_resoprab a_wcel f2_resoprab a_sup_set_class f5_resoprab a_wcel a_wa f0_resoprab a_wa f1_resoprab f2_resoprab f3_resoprab a_coprab p_3eqtr4i $.
$}

$(Restriction of an operator abstraction.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)

${
	$v ph x y z A B C D  $.
	$d A x y z  $.
	$d B x y z  $.
	$d C x y z  $.
	$d D x y z  $.
	$d z  $.
	f0_resoprab2 $f wff ph $.
	f1_resoprab2 $f set x $.
	f2_resoprab2 $f set y $.
	f3_resoprab2 $f set z $.
	f4_resoprab2 $f class A $.
	f5_resoprab2 $f class B $.
	f6_resoprab2 $f class C $.
	f7_resoprab2 $f class D $.
	p_resoprab2 $p |- ( ( C C_ A /\ D C_ B ) -> ( { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } |` ( C X. D ) ) = { <. <. x , y >. , z >. | ( ( x e. C /\ y e. D ) /\ ph ) } ) $= f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa f0_resoprab2 a_wa f1_resoprab2 f2_resoprab2 f3_resoprab2 f6_resoprab2 f7_resoprab2 p_resoprab f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa f0_resoprab2 p_anass f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel p_an4 f6_resoprab2 f4_resoprab2 f1_resoprab2 a_sup_set_class p_ssel f6_resoprab2 f4_resoprab2 a_wss f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel p_pm4.71d f6_resoprab2 f4_resoprab2 a_wss f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel a_wa p_bicomd f7_resoprab2 f5_resoprab2 f2_resoprab2 a_sup_set_class p_ssel f7_resoprab2 f5_resoprab2 a_wss f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel p_pm4.71d f7_resoprab2 f5_resoprab2 a_wss f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa p_bicomd f6_resoprab2 f4_resoprab2 a_wss f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f7_resoprab2 f5_resoprab2 a_wss f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel p_bi2anan9 f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel a_wa f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa a_wa f6_resoprab2 f4_resoprab2 a_wss f7_resoprab2 f5_resoprab2 a_wss a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa p_syl5bb f6_resoprab2 f4_resoprab2 a_wss f7_resoprab2 f5_resoprab2 a_wss a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f0_resoprab2 p_anbi1d f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa f0_resoprab2 a_wa a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa a_wa f0_resoprab2 a_wa f6_resoprab2 f4_resoprab2 a_wss f7_resoprab2 f5_resoprab2 a_wss a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f0_resoprab2 a_wa p_syl5bbr f6_resoprab2 f4_resoprab2 a_wss f7_resoprab2 f5_resoprab2 a_wss a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa f0_resoprab2 a_wa a_wa f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f0_resoprab2 a_wa f1_resoprab2 f2_resoprab2 f3_resoprab2 p_oprabbidv f6_resoprab2 f4_resoprab2 a_wss f7_resoprab2 f5_resoprab2 a_wss a_wa f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa f0_resoprab2 a_wa f1_resoprab2 f2_resoprab2 f3_resoprab2 a_coprab f6_resoprab2 f7_resoprab2 a_cxp a_cres f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f1_resoprab2 a_sup_set_class f4_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f5_resoprab2 a_wcel a_wa f0_resoprab2 a_wa a_wa f1_resoprab2 f2_resoprab2 f3_resoprab2 a_coprab f1_resoprab2 a_sup_set_class f6_resoprab2 a_wcel f2_resoprab2 a_sup_set_class f7_resoprab2 a_wcel a_wa f0_resoprab2 a_wa f1_resoprab2 f2_resoprab2 f3_resoprab2 a_coprab p_syl5eq $.
$}

$(Restriction of the mapping operation.  (Contributed by Mario Carneiro,
       17-Dec-2013.) $)

${
	$v x y A B C D E  $.
	$d A x y z  $.
	$d B x y z  $.
	$d C x y z  $.
	$d D x y z  $.
	$d E z  $.
	f0_resmpt2 $f set x $.
	f1_resmpt2 $f set y $.
	f2_resmpt2 $f class A $.
	f3_resmpt2 $f class B $.
	f4_resmpt2 $f class C $.
	f5_resmpt2 $f class D $.
	f6_resmpt2 $f class E $.
	i0_resmpt2 $f set z $.
	p_resmpt2 $p |- ( ( C C_ A /\ D C_ B ) -> ( ( x e. A , y e. B |-> E ) |` ( C X. D ) ) = ( x e. C , y e. D |-> E ) ) $= i0_resmpt2 a_sup_set_class f6_resmpt2 a_wceq f0_resmpt2 f1_resmpt2 i0_resmpt2 f2_resmpt2 f3_resmpt2 f4_resmpt2 f5_resmpt2 p_resoprab2 f0_resmpt2 f1_resmpt2 i0_resmpt2 f2_resmpt2 f3_resmpt2 f6_resmpt2 a_df-mpt2 f0_resmpt2 f1_resmpt2 f2_resmpt2 f3_resmpt2 f6_resmpt2 a_cmpt2 f0_resmpt2 a_sup_set_class f2_resmpt2 a_wcel f1_resmpt2 a_sup_set_class f3_resmpt2 a_wcel a_wa i0_resmpt2 a_sup_set_class f6_resmpt2 a_wceq a_wa f0_resmpt2 f1_resmpt2 i0_resmpt2 a_coprab f4_resmpt2 f5_resmpt2 a_cxp p_reseq1i f0_resmpt2 f1_resmpt2 i0_resmpt2 f4_resmpt2 f5_resmpt2 f6_resmpt2 a_df-mpt2 f4_resmpt2 f2_resmpt2 a_wss f5_resmpt2 f3_resmpt2 a_wss a_wa f0_resmpt2 a_sup_set_class f2_resmpt2 a_wcel f1_resmpt2 a_sup_set_class f3_resmpt2 a_wcel a_wa i0_resmpt2 a_sup_set_class f6_resmpt2 a_wceq a_wa f0_resmpt2 f1_resmpt2 i0_resmpt2 a_coprab f4_resmpt2 f5_resmpt2 a_cxp a_cres f0_resmpt2 a_sup_set_class f4_resmpt2 a_wcel f1_resmpt2 a_sup_set_class f5_resmpt2 a_wcel a_wa i0_resmpt2 a_sup_set_class f6_resmpt2 a_wceq a_wa f0_resmpt2 f1_resmpt2 i0_resmpt2 a_coprab f0_resmpt2 f1_resmpt2 f2_resmpt2 f3_resmpt2 f6_resmpt2 a_cmpt2 f4_resmpt2 f5_resmpt2 a_cxp a_cres f0_resmpt2 f1_resmpt2 f4_resmpt2 f5_resmpt2 f6_resmpt2 a_cmpt2 p_3eqtr4g $.
$}

$("At most one" is a sufficient condition for an operation class
       abstraction to be a function.  (Contributed by NM, 28-Aug-2007.) $)

${
	$v ph x y z  $.
	$d x y z w  $.
	$d w ph  $.
	f0_funoprabg $f wff ph $.
	f1_funoprabg $f set x $.
	f2_funoprabg $f set y $.
	f3_funoprabg $f set z $.
	i0_funoprabg $f set w $.
	p_funoprabg $p |- ( A. x A. y E* z ph -> Fun { <. <. x , y >. , z >. | ph } ) $= f0_funoprabg f3_funoprabg f1_funoprabg f2_funoprabg i0_funoprabg a_sup_set_class p_mosubopt f0_funoprabg f3_funoprabg a_wmo f2_funoprabg a_wal f1_funoprabg a_wal i0_funoprabg a_sup_set_class f1_funoprabg a_sup_set_class f2_funoprabg a_sup_set_class a_cop a_wceq f0_funoprabg a_wa f2_funoprabg a_wex f1_funoprabg a_wex f3_funoprabg a_wmo i0_funoprabg p_alrimiv f0_funoprabg f1_funoprabg f2_funoprabg f3_funoprabg i0_funoprabg p_dfoprab2 f0_funoprabg f1_funoprabg f2_funoprabg f3_funoprabg a_coprab i0_funoprabg a_sup_set_class f1_funoprabg a_sup_set_class f2_funoprabg a_sup_set_class a_cop a_wceq f0_funoprabg a_wa f2_funoprabg a_wex f1_funoprabg a_wex i0_funoprabg f3_funoprabg a_copab p_funeqi i0_funoprabg a_sup_set_class f1_funoprabg a_sup_set_class f2_funoprabg a_sup_set_class a_cop a_wceq f0_funoprabg a_wa f2_funoprabg a_wex f1_funoprabg a_wex i0_funoprabg f3_funoprabg p_funopab f0_funoprabg f1_funoprabg f2_funoprabg f3_funoprabg a_coprab a_wfun i0_funoprabg a_sup_set_class f1_funoprabg a_sup_set_class f2_funoprabg a_sup_set_class a_cop a_wceq f0_funoprabg a_wa f2_funoprabg a_wex f1_funoprabg a_wex i0_funoprabg f3_funoprabg a_copab a_wfun i0_funoprabg a_sup_set_class f1_funoprabg a_sup_set_class f2_funoprabg a_sup_set_class a_cop a_wceq f0_funoprabg a_wa f2_funoprabg a_wex f1_funoprabg a_wex f3_funoprabg a_wmo i0_funoprabg a_wal p_bitr2i f0_funoprabg f3_funoprabg a_wmo f2_funoprabg a_wal f1_funoprabg a_wal i0_funoprabg a_sup_set_class f1_funoprabg a_sup_set_class f2_funoprabg a_sup_set_class a_cop a_wceq f0_funoprabg a_wa f2_funoprabg a_wex f1_funoprabg a_wex f3_funoprabg a_wmo i0_funoprabg a_wal f0_funoprabg f1_funoprabg f2_funoprabg f3_funoprabg a_coprab a_wfun p_sylib $.
$}

$("At most one" is a sufficient condition for an operation class
       abstraction to be a function.  (Contributed by NM, 17-Mar-1995.) $)

${
	$v ph x y z  $.
	$d x y z  $.
	$d ph  $.
	f0_funoprab $f wff ph $.
	f1_funoprab $f set x $.
	f2_funoprab $f set y $.
	f3_funoprab $f set z $.
	e0_funoprab $e |- E* z ph $.
	p_funoprab $p |- Fun { <. <. x , y >. , z >. | ph } $= e0_funoprab f0_funoprab f3_funoprab a_wmo f1_funoprab f2_funoprab p_gen2 f0_funoprab f1_funoprab f2_funoprab f3_funoprab p_funoprabg f0_funoprab f3_funoprab a_wmo f2_funoprab a_wal f1_funoprab a_wal f0_funoprab f1_funoprab f2_funoprab f3_funoprab a_coprab a_wfun a_ax-mp $.
$}

$(Functionality and domain of an operation class abstraction.
       (Contributed by NM, 28-Aug-2007.) $)

${
	$v ph ps x y z  $.
	$d x y z  $.
	$d z ph  $.
	f0_fnoprabg $f wff ph $.
	f1_fnoprabg $f wff ps $.
	f2_fnoprabg $f set x $.
	f3_fnoprabg $f set y $.
	f4_fnoprabg $f set z $.
	p_fnoprabg $p |- ( A. x A. y ( ph -> E! z ps ) -> { <. <. x , y >. , z >. | ( ph /\ ps ) } Fn { <. x , y >. | ph } ) $= f1_fnoprabg f4_fnoprabg p_eumo f1_fnoprabg f4_fnoprabg a_weu f1_fnoprabg f4_fnoprabg a_wmo f0_fnoprabg p_imim2i f0_fnoprabg f1_fnoprabg f4_fnoprabg p_moanimv f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f0_fnoprabg f1_fnoprabg f4_fnoprabg a_wmo a_wi f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wmo p_sylibr f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wmo f2_fnoprabg f3_fnoprabg p_2alimi f0_fnoprabg f1_fnoprabg a_wa f2_fnoprabg f3_fnoprabg f4_fnoprabg p_funoprabg f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f3_fnoprabg a_wal f2_fnoprabg a_wal f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wmo f3_fnoprabg a_wal f2_fnoprabg a_wal f0_fnoprabg f1_fnoprabg a_wa f2_fnoprabg f3_fnoprabg f4_fnoprabg a_coprab a_wfun p_syl f0_fnoprabg f1_fnoprabg a_wa f2_fnoprabg f3_fnoprabg f4_fnoprabg p_dmoprab f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f3_fnoprabg a_wal f2_fnoprabg p_nfa1 f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f3_fnoprabg f2_fnoprabg p_nfa2 f0_fnoprabg f1_fnoprabg p_simpl f0_fnoprabg f1_fnoprabg a_wa f0_fnoprabg f4_fnoprabg p_exlimiv f1_fnoprabg f4_fnoprabg p_euex f1_fnoprabg f4_fnoprabg a_weu f1_fnoprabg f4_fnoprabg a_wex f0_fnoprabg p_imim2i f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f0_fnoprabg f1_fnoprabg f4_fnoprabg a_wex p_ancld f0_fnoprabg f1_fnoprabg f4_fnoprabg p_19.42v f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f0_fnoprabg f0_fnoprabg f1_fnoprabg f4_fnoprabg a_wex a_wa f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wex p_syl6ibr f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wex f0_fnoprabg p_impbid2 f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wex f0_fnoprabg a_wb f3_fnoprabg p_sps f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f3_fnoprabg a_wal f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wex f0_fnoprabg a_wb f2_fnoprabg p_sps f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f3_fnoprabg a_wal f2_fnoprabg a_wal f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wex f0_fnoprabg f2_fnoprabg f3_fnoprabg p_opabbid f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f3_fnoprabg a_wal f2_fnoprabg a_wal f0_fnoprabg f1_fnoprabg a_wa f2_fnoprabg f3_fnoprabg f4_fnoprabg a_coprab a_cdm f0_fnoprabg f1_fnoprabg a_wa f4_fnoprabg a_wex f2_fnoprabg f3_fnoprabg a_copab f0_fnoprabg f2_fnoprabg f3_fnoprabg a_copab p_syl5eq f0_fnoprabg f1_fnoprabg a_wa f2_fnoprabg f3_fnoprabg f4_fnoprabg a_coprab f0_fnoprabg f2_fnoprabg f3_fnoprabg a_copab a_df-fn f0_fnoprabg f1_fnoprabg f4_fnoprabg a_weu a_wi f3_fnoprabg a_wal f2_fnoprabg a_wal f0_fnoprabg f1_fnoprabg a_wa f2_fnoprabg f3_fnoprabg f4_fnoprabg a_coprab a_wfun f0_fnoprabg f1_fnoprabg a_wa f2_fnoprabg f3_fnoprabg f4_fnoprabg a_coprab a_cdm f0_fnoprabg f2_fnoprabg f3_fnoprabg a_copab a_wceq f0_fnoprabg f1_fnoprabg a_wa f2_fnoprabg f3_fnoprabg f4_fnoprabg a_coprab f0_fnoprabg f2_fnoprabg f3_fnoprabg a_copab a_wfn p_sylanbrc $.
$}

$(The maps-to notation for an operation is always a function.
       (Contributed by Scott Fenton, 21-Mar-2012.) $)

${
	$v x y A B C F  $.
	$d A w z  $.
	$d B w z  $.
	$d C w z  $.
	$d x y w z  $.
	f0_mpt2fun $f set x $.
	f1_mpt2fun $f set y $.
	f2_mpt2fun $f class A $.
	f3_mpt2fun $f class B $.
	f4_mpt2fun $f class C $.
	f5_mpt2fun $f class F $.
	i0_mpt2fun $f set z $.
	i1_mpt2fun $f set w $.
	e0_mpt2fun $e |- F = ( x e. A , y e. B |-> C ) $.
	p_mpt2fun $p |- Fun F $= i0_mpt2fun a_sup_set_class i1_mpt2fun a_sup_set_class f4_mpt2fun p_eqtr3 i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq i1_mpt2fun a_sup_set_class f4_mpt2fun a_wceq i0_mpt2fun a_sup_set_class i1_mpt2fun a_sup_set_class a_wceq f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa p_ad2ant2l f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i1_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa a_wa i0_mpt2fun a_sup_set_class i1_mpt2fun a_sup_set_class a_wceq a_wi i0_mpt2fun i1_mpt2fun p_gen2 i0_mpt2fun a_sup_set_class i1_mpt2fun a_sup_set_class f4_mpt2fun p_eqeq1 i0_mpt2fun a_sup_set_class i1_mpt2fun a_sup_set_class a_wceq i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq i1_mpt2fun a_sup_set_class f4_mpt2fun a_wceq f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa p_anbi2d f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i1_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa i0_mpt2fun i1_mpt2fun p_mo4 f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa i0_mpt2fun a_wmo f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i1_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa a_wa i0_mpt2fun a_sup_set_class i1_mpt2fun a_sup_set_class a_wceq a_wi i1_mpt2fun a_wal i0_mpt2fun a_wal p_mpbir f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa f0_mpt2fun f1_mpt2fun i0_mpt2fun p_funoprab e0_mpt2fun f0_mpt2fun f1_mpt2fun i0_mpt2fun f2_mpt2fun f3_mpt2fun f4_mpt2fun a_df-mpt2 f5_mpt2fun f0_mpt2fun f1_mpt2fun f2_mpt2fun f3_mpt2fun f4_mpt2fun a_cmpt2 f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa f0_mpt2fun f1_mpt2fun i0_mpt2fun a_coprab p_eqtri f5_mpt2fun f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa f0_mpt2fun f1_mpt2fun i0_mpt2fun a_coprab p_funeqi f5_mpt2fun a_wfun f0_mpt2fun a_sup_set_class f2_mpt2fun a_wcel f1_mpt2fun a_sup_set_class f3_mpt2fun a_wcel a_wa i0_mpt2fun a_sup_set_class f4_mpt2fun a_wceq a_wa f0_mpt2fun f1_mpt2fun i0_mpt2fun a_coprab a_wfun p_mpbir $.
$}

$(Functionality and domain of an operation class abstraction.
       (Contributed by NM, 15-May-1995.) $)

${
	$v ph ps x y z  $.
	$d x y z  $.
	$d z ph  $.
	f0_fnoprab $f wff ph $.
	f1_fnoprab $f wff ps $.
	f2_fnoprab $f set x $.
	f3_fnoprab $f set y $.
	f4_fnoprab $f set z $.
	e0_fnoprab $e |- ( ph -> E! z ps ) $.
	p_fnoprab $p |- { <. <. x , y >. , z >. | ( ph /\ ps ) } Fn { <. x , y >. | ph } $= e0_fnoprab f0_fnoprab f1_fnoprab f4_fnoprab a_weu a_wi f2_fnoprab f3_fnoprab p_gen2 f0_fnoprab f1_fnoprab f2_fnoprab f3_fnoprab f4_fnoprab p_fnoprabg f0_fnoprab f1_fnoprab f4_fnoprab a_weu a_wi f3_fnoprab a_wal f2_fnoprab a_wal f0_fnoprab f1_fnoprab a_wa f2_fnoprab f3_fnoprab f4_fnoprab a_coprab f0_fnoprab f2_fnoprab f3_fnoprab a_copab a_wfn a_ax-mp $.
$}

$(An operation maps to a class to which all values belong.  (Contributed
       by NM, 7-Feb-2004.) $)

${
	$v x y A B C F  $.
	$d x y w A  $.
	$d x y w B  $.
	$d x y w C  $.
	$d x y w F  $.
	f0_ffnov $f set x $.
	f1_ffnov $f set y $.
	f2_ffnov $f class A $.
	f3_ffnov $f class B $.
	f4_ffnov $f class C $.
	f5_ffnov $f class F $.
	i0_ffnov $f set w $.
	p_ffnov $p |- ( F : ( A X. B ) --> C <-> ( F Fn ( A X. B ) /\ A. x e. A A. y e. B ( x F y ) e. C ) ) $= i0_ffnov f2_ffnov f3_ffnov a_cxp f4_ffnov f5_ffnov p_ffnfv i0_ffnov a_sup_set_class f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class a_cop f5_ffnov p_fveq2 f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class f5_ffnov a_df-ov i0_ffnov a_sup_set_class f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class a_cop a_wceq i0_ffnov a_sup_set_class f5_ffnov a_cfv f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class a_cop f5_ffnov a_cfv f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class f5_ffnov a_co p_syl6eqr i0_ffnov a_sup_set_class f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class a_cop a_wceq i0_ffnov a_sup_set_class f5_ffnov a_cfv f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class f5_ffnov a_co f4_ffnov p_eleq1d i0_ffnov a_sup_set_class f5_ffnov a_cfv f4_ffnov a_wcel f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class f5_ffnov a_co f4_ffnov a_wcel i0_ffnov f0_ffnov f1_ffnov f2_ffnov f3_ffnov p_ralxp i0_ffnov a_sup_set_class f5_ffnov a_cfv f4_ffnov a_wcel i0_ffnov f2_ffnov f3_ffnov a_cxp a_wral f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class f5_ffnov a_co f4_ffnov a_wcel f1_ffnov f3_ffnov a_wral f0_ffnov f2_ffnov a_wral f5_ffnov f2_ffnov f3_ffnov a_cxp a_wfn p_anbi2i f2_ffnov f3_ffnov a_cxp f4_ffnov f5_ffnov a_wf f5_ffnov f2_ffnov f3_ffnov a_cxp a_wfn i0_ffnov a_sup_set_class f5_ffnov a_cfv f4_ffnov a_wcel i0_ffnov f2_ffnov f3_ffnov a_cxp a_wral a_wa f5_ffnov f2_ffnov f3_ffnov a_cxp a_wfn f0_ffnov a_sup_set_class f1_ffnov a_sup_set_class f5_ffnov a_co f4_ffnov a_wcel f1_ffnov f3_ffnov a_wral f0_ffnov f2_ffnov a_wral a_wa p_bitri $.
$}

$(Closure law for an operation.  (Contributed by NM, 19-Apr-2007.) $)

${
	$v A B C R S F  $.
	$d x y A  $.
	$d y B  $.
	$d x y C  $.
	$d x y F  $.
	$d x y R  $.
	$d x y S  $.
	f0_fovcl $f class A $.
	f1_fovcl $f class B $.
	f2_fovcl $f class C $.
	f3_fovcl $f class R $.
	f4_fovcl $f class S $.
	f5_fovcl $f class F $.
	i0_fovcl $f set x $.
	i1_fovcl $f set y $.
	e0_fovcl $e |- F : ( R X. S ) --> C $.
	p_fovcl $p |- ( ( A e. R /\ B e. S ) -> ( A F B ) e. C ) $= e0_fovcl i0_fovcl i1_fovcl f3_fovcl f4_fovcl f2_fovcl f5_fovcl p_ffnov f3_fovcl f4_fovcl a_cxp f2_fovcl f5_fovcl a_wf f5_fovcl f3_fovcl f4_fovcl a_cxp a_wfn i0_fovcl a_sup_set_class i1_fovcl a_sup_set_class f5_fovcl a_co f2_fovcl a_wcel i1_fovcl f4_fovcl a_wral i0_fovcl f3_fovcl a_wral p_simprbi f3_fovcl f4_fovcl a_cxp f2_fovcl f5_fovcl a_wf i0_fovcl a_sup_set_class i1_fovcl a_sup_set_class f5_fovcl a_co f2_fovcl a_wcel i1_fovcl f4_fovcl a_wral i0_fovcl f3_fovcl a_wral a_ax-mp i0_fovcl a_sup_set_class f0_fovcl i1_fovcl a_sup_set_class f5_fovcl p_oveq1 i0_fovcl a_sup_set_class f0_fovcl a_wceq i0_fovcl a_sup_set_class i1_fovcl a_sup_set_class f5_fovcl a_co f0_fovcl i1_fovcl a_sup_set_class f5_fovcl a_co f2_fovcl p_eleq1d i1_fovcl a_sup_set_class f1_fovcl f0_fovcl f5_fovcl p_oveq2 i1_fovcl a_sup_set_class f1_fovcl a_wceq f0_fovcl i1_fovcl a_sup_set_class f5_fovcl a_co f0_fovcl f1_fovcl f5_fovcl a_co f2_fovcl p_eleq1d i0_fovcl a_sup_set_class i1_fovcl a_sup_set_class f5_fovcl a_co f2_fovcl a_wcel f0_fovcl f1_fovcl f5_fovcl a_co f2_fovcl a_wcel f0_fovcl i1_fovcl a_sup_set_class f5_fovcl a_co f2_fovcl a_wcel i0_fovcl i1_fovcl f0_fovcl f1_fovcl f3_fovcl f4_fovcl p_rspc2v f0_fovcl f3_fovcl a_wcel f1_fovcl f4_fovcl a_wcel a_wa i0_fovcl a_sup_set_class i1_fovcl a_sup_set_class f5_fovcl a_co f2_fovcl a_wcel i1_fovcl f4_fovcl a_wral i0_fovcl f3_fovcl a_wral f0_fovcl f1_fovcl f5_fovcl a_co f2_fovcl a_wcel p_mpi $.
$}

$(Equality of two operations is determined by their values.  (Contributed
       by NM, 1-Sep-2005.) $)

${
	$v x y A B C D F G  $.
	$d x y z A  $.
	$d x y z B  $.
	$d z C  $.
	$d z D  $.
	$d x y z F  $.
	$d x y z G  $.
	f0_eqfnov $f set x $.
	f1_eqfnov $f set y $.
	f2_eqfnov $f class A $.
	f3_eqfnov $f class B $.
	f4_eqfnov $f class C $.
	f5_eqfnov $f class D $.
	f6_eqfnov $f class F $.
	f7_eqfnov $f class G $.
	i0_eqfnov $f set z $.
	p_eqfnov $p |- ( ( F Fn ( A X. B ) /\ G Fn ( C X. D ) ) -> ( F = G <-> ( ( A X. B ) = ( C X. D ) /\ A. x e. A A. y e. B ( x F y ) = ( x G y ) ) ) ) $= i0_eqfnov f2_eqfnov f3_eqfnov a_cxp f4_eqfnov f5_eqfnov a_cxp f6_eqfnov f7_eqfnov p_eqfnfv2 i0_eqfnov a_sup_set_class f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop f6_eqfnov p_fveq2 i0_eqfnov a_sup_set_class f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop f7_eqfnov p_fveq2 i0_eqfnov a_sup_set_class f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop a_wceq i0_eqfnov a_sup_set_class f6_eqfnov a_cfv f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop f6_eqfnov a_cfv i0_eqfnov a_sup_set_class f7_eqfnov a_cfv f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop f7_eqfnov a_cfv p_eqeq12d f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f6_eqfnov a_df-ov f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f7_eqfnov a_df-ov f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f6_eqfnov a_co f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop f6_eqfnov a_cfv f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f7_eqfnov a_co f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop f7_eqfnov a_cfv p_eqeq12i i0_eqfnov a_sup_set_class f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop a_wceq i0_eqfnov a_sup_set_class f6_eqfnov a_cfv i0_eqfnov a_sup_set_class f7_eqfnov a_cfv a_wceq f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop f6_eqfnov a_cfv f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class a_cop f7_eqfnov a_cfv a_wceq f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f6_eqfnov a_co f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f7_eqfnov a_co a_wceq p_syl6bbr i0_eqfnov a_sup_set_class f6_eqfnov a_cfv i0_eqfnov a_sup_set_class f7_eqfnov a_cfv a_wceq f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f6_eqfnov a_co f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f7_eqfnov a_co a_wceq i0_eqfnov f0_eqfnov f1_eqfnov f2_eqfnov f3_eqfnov p_ralxp i0_eqfnov a_sup_set_class f6_eqfnov a_cfv i0_eqfnov a_sup_set_class f7_eqfnov a_cfv a_wceq i0_eqfnov f2_eqfnov f3_eqfnov a_cxp a_wral f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f6_eqfnov a_co f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f7_eqfnov a_co a_wceq f1_eqfnov f3_eqfnov a_wral f0_eqfnov f2_eqfnov a_wral f2_eqfnov f3_eqfnov a_cxp f4_eqfnov f5_eqfnov a_cxp a_wceq p_anbi2i f6_eqfnov f2_eqfnov f3_eqfnov a_cxp a_wfn f7_eqfnov f4_eqfnov f5_eqfnov a_cxp a_wfn a_wa f6_eqfnov f7_eqfnov a_wceq f2_eqfnov f3_eqfnov a_cxp f4_eqfnov f5_eqfnov a_cxp a_wceq i0_eqfnov a_sup_set_class f6_eqfnov a_cfv i0_eqfnov a_sup_set_class f7_eqfnov a_cfv a_wceq i0_eqfnov f2_eqfnov f3_eqfnov a_cxp a_wral a_wa f2_eqfnov f3_eqfnov a_cxp f4_eqfnov f5_eqfnov a_cxp a_wceq f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f6_eqfnov a_co f0_eqfnov a_sup_set_class f1_eqfnov a_sup_set_class f7_eqfnov a_co a_wceq f1_eqfnov f3_eqfnov a_wral f0_eqfnov f2_eqfnov a_wral a_wa p_syl6bb $.
$}

$(Two operators with the same domain are equal iff their values at each
       point in the domain are equal.  (Contributed by Jeff Madsen,
       7-Jun-2010.) $)

${
	$v x y A B F G  $.
	$d A x y  $.
	$d B x y  $.
	$d F x y  $.
	$d G x y  $.
	f0_eqfnov2 $f set x $.
	f1_eqfnov2 $f set y $.
	f2_eqfnov2 $f class A $.
	f3_eqfnov2 $f class B $.
	f4_eqfnov2 $f class F $.
	f5_eqfnov2 $f class G $.
	p_eqfnov2 $p |- ( ( F Fn ( A X. B ) /\ G Fn ( A X. B ) ) -> ( F = G <-> A. x e. A A. y e. B ( x F y ) = ( x G y ) ) ) $= f0_eqfnov2 f1_eqfnov2 f2_eqfnov2 f3_eqfnov2 f2_eqfnov2 f3_eqfnov2 f4_eqfnov2 f5_eqfnov2 p_eqfnov f2_eqfnov2 f3_eqfnov2 a_cxp f2_eqfnov2 f3_eqfnov2 a_cxp a_wceq f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f4_eqfnov2 a_co f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f5_eqfnov2 a_co a_wceq f1_eqfnov2 f3_eqfnov2 a_wral f0_eqfnov2 f2_eqfnov2 a_wral p_simpr f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f4_eqfnov2 a_co f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f5_eqfnov2 a_co a_wceq f1_eqfnov2 f3_eqfnov2 a_wral f0_eqfnov2 f2_eqfnov2 a_wral f2_eqfnov2 f3_eqfnov2 a_cxp p_eqidd f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f4_eqfnov2 a_co f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f5_eqfnov2 a_co a_wceq f1_eqfnov2 f3_eqfnov2 a_wral f0_eqfnov2 f2_eqfnov2 a_wral f2_eqfnov2 f3_eqfnov2 a_cxp f2_eqfnov2 f3_eqfnov2 a_cxp a_wceq p_ancri f2_eqfnov2 f3_eqfnov2 a_cxp f2_eqfnov2 f3_eqfnov2 a_cxp a_wceq f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f4_eqfnov2 a_co f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f5_eqfnov2 a_co a_wceq f1_eqfnov2 f3_eqfnov2 a_wral f0_eqfnov2 f2_eqfnov2 a_wral a_wa f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f4_eqfnov2 a_co f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f5_eqfnov2 a_co a_wceq f1_eqfnov2 f3_eqfnov2 a_wral f0_eqfnov2 f2_eqfnov2 a_wral p_impbii f4_eqfnov2 f2_eqfnov2 f3_eqfnov2 a_cxp a_wfn f5_eqfnov2 f2_eqfnov2 f3_eqfnov2 a_cxp a_wfn a_wa f4_eqfnov2 f5_eqfnov2 a_wceq f2_eqfnov2 f3_eqfnov2 a_cxp f2_eqfnov2 f3_eqfnov2 a_cxp a_wceq f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f4_eqfnov2 a_co f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f5_eqfnov2 a_co a_wceq f1_eqfnov2 f3_eqfnov2 a_wral f0_eqfnov2 f2_eqfnov2 a_wral a_wa f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f4_eqfnov2 a_co f0_eqfnov2 a_sup_set_class f1_eqfnov2 a_sup_set_class f5_eqfnov2 a_co a_wceq f1_eqfnov2 f3_eqfnov2 a_wral f0_eqfnov2 f2_eqfnov2 a_wral p_syl6bb $.
$}

$(Representation of a function in terms of its values.  (Contributed by
       NM, 7-Feb-2004.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)

${
	$v x y A B F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z F  $.
	f0_fnov $f set x $.
	f1_fnov $f set y $.
	f2_fnov $f class A $.
	f3_fnov $f class B $.
	f4_fnov $f class F $.
	i0_fnov $f set z $.
	p_fnov $p |- ( F Fn ( A X. B ) <-> F = ( x e. A , y e. B |-> ( x F y ) ) ) $= i0_fnov f2_fnov f3_fnov a_cxp f4_fnov p_dffn5 i0_fnov a_sup_set_class f0_fnov a_sup_set_class f1_fnov a_sup_set_class a_cop f4_fnov p_fveq2 f0_fnov a_sup_set_class f1_fnov a_sup_set_class f4_fnov a_df-ov i0_fnov a_sup_set_class f0_fnov a_sup_set_class f1_fnov a_sup_set_class a_cop a_wceq i0_fnov a_sup_set_class f4_fnov a_cfv f0_fnov a_sup_set_class f1_fnov a_sup_set_class a_cop f4_fnov a_cfv f0_fnov a_sup_set_class f1_fnov a_sup_set_class f4_fnov a_co p_syl6eqr f0_fnov f1_fnov i0_fnov f2_fnov f3_fnov i0_fnov a_sup_set_class f4_fnov a_cfv f0_fnov a_sup_set_class f1_fnov a_sup_set_class f4_fnov a_co p_mpt2mpt i0_fnov f2_fnov f3_fnov a_cxp i0_fnov a_sup_set_class f4_fnov a_cfv a_cmpt f0_fnov f1_fnov f2_fnov f3_fnov f0_fnov a_sup_set_class f1_fnov a_sup_set_class f4_fnov a_co a_cmpt2 f4_fnov p_eqeq2i f4_fnov f2_fnov f3_fnov a_cxp a_wfn f4_fnov i0_fnov f2_fnov f3_fnov a_cxp i0_fnov a_sup_set_class f4_fnov a_cfv a_cmpt a_wceq f4_fnov f0_fnov f1_fnov f2_fnov f3_fnov f0_fnov a_sup_set_class f1_fnov a_sup_set_class f4_fnov a_co a_cmpt2 a_wceq p_bitri $.
$}

$(Bidirectional equality theorem for a mapping abstraction.  Equivalent to
       ~ eqfnov2 .  (Contributed by Mario Carneiro, 4-Jan-2017.) $)

${
	$v x y A B C D V  $.
	$d x y z A  $.
	$d y z B  $.
	$d z C  $.
	$d z D  $.
	f0_mpt22eqb $f set x $.
	f1_mpt22eqb $f set y $.
	f2_mpt22eqb $f class A $.
	f3_mpt22eqb $f class B $.
	f4_mpt22eqb $f class C $.
	f5_mpt22eqb $f class D $.
	f6_mpt22eqb $f class V $.
	i0_mpt22eqb $f set z $.
	p_mpt22eqb $p |- ( A. x e. A A. y e. B C e. V -> ( ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) <-> A. x e. A A. y e. B C = D ) ) $= i0_mpt22eqb f4_mpt22eqb f5_mpt22eqb f6_mpt22eqb p_pm13.183 f4_mpt22eqb f6_mpt22eqb a_wcel f4_mpt22eqb f5_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal a_wb f1_mpt22eqb f3_mpt22eqb p_ralimi f4_mpt22eqb f5_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb p_ralbi f4_mpt22eqb f6_mpt22eqb a_wcel f1_mpt22eqb f3_mpt22eqb a_wral f4_mpt22eqb f5_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal a_wb f1_mpt22eqb f3_mpt22eqb a_wral f4_mpt22eqb f5_mpt22eqb a_wceq f1_mpt22eqb f3_mpt22eqb a_wral i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb a_wral a_wb p_syl f4_mpt22eqb f6_mpt22eqb a_wcel f1_mpt22eqb f3_mpt22eqb a_wral f4_mpt22eqb f5_mpt22eqb a_wceq f1_mpt22eqb f3_mpt22eqb a_wral i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb a_wral a_wb f0_mpt22eqb f2_mpt22eqb p_ralimi f4_mpt22eqb f5_mpt22eqb a_wceq f1_mpt22eqb f3_mpt22eqb a_wral i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb p_ralbi f4_mpt22eqb f6_mpt22eqb a_wcel f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb a_wral f4_mpt22eqb f5_mpt22eqb a_wceq f1_mpt22eqb f3_mpt22eqb a_wral i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb a_wral a_wb f0_mpt22eqb f2_mpt22eqb a_wral f4_mpt22eqb f5_mpt22eqb a_wceq f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb a_wral i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb a_wral a_wb p_syl f0_mpt22eqb f1_mpt22eqb i0_mpt22eqb f2_mpt22eqb f3_mpt22eqb f4_mpt22eqb a_df-mpt2 f0_mpt22eqb f1_mpt22eqb i0_mpt22eqb f2_mpt22eqb f3_mpt22eqb f5_mpt22eqb a_df-mpt2 f0_mpt22eqb f1_mpt22eqb f2_mpt22eqb f3_mpt22eqb f4_mpt22eqb a_cmpt2 f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq a_wa f0_mpt22eqb f1_mpt22eqb i0_mpt22eqb a_coprab f0_mpt22eqb f1_mpt22eqb f2_mpt22eqb f3_mpt22eqb f5_mpt22eqb a_cmpt2 f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wa f0_mpt22eqb f1_mpt22eqb i0_mpt22eqb a_coprab p_eqeq12i f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq a_wa f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wa f0_mpt22eqb f1_mpt22eqb i0_mpt22eqb p_eqoprab2b f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq p_pm5.32 f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb a_wi f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq a_wa f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wa a_wb i0_mpt22eqb p_albii f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb p_19.21v f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq a_wa f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wa a_wb i0_mpt22eqb a_wal f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb a_wi i0_mpt22eqb a_wal f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal a_wi p_bitr3i f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq a_wa f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wa a_wb i0_mpt22eqb a_wal f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal a_wi f0_mpt22eqb f1_mpt22eqb p_2albii i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f0_mpt22eqb f1_mpt22eqb f2_mpt22eqb f3_mpt22eqb p_r2al f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq a_wa f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wa a_wb i0_mpt22eqb a_wal f1_mpt22eqb a_wal f0_mpt22eqb a_wal f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal a_wi f1_mpt22eqb a_wal f0_mpt22eqb a_wal i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb a_wral p_bitr4i f0_mpt22eqb f1_mpt22eqb f2_mpt22eqb f3_mpt22eqb f4_mpt22eqb a_cmpt2 f0_mpt22eqb f1_mpt22eqb f2_mpt22eqb f3_mpt22eqb f5_mpt22eqb a_cmpt2 a_wceq f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq a_wa f0_mpt22eqb f1_mpt22eqb i0_mpt22eqb a_coprab f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wa f0_mpt22eqb f1_mpt22eqb i0_mpt22eqb a_coprab a_wceq f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq a_wa f0_mpt22eqb a_sup_set_class f2_mpt22eqb a_wcel f1_mpt22eqb a_sup_set_class f3_mpt22eqb a_wcel a_wa i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wa a_wb i0_mpt22eqb a_wal f1_mpt22eqb a_wal f0_mpt22eqb a_wal i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb a_wral p_3bitri f4_mpt22eqb f6_mpt22eqb a_wcel f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb a_wral f4_mpt22eqb f5_mpt22eqb a_wceq f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb a_wral i0_mpt22eqb a_sup_set_class f4_mpt22eqb a_wceq i0_mpt22eqb a_sup_set_class f5_mpt22eqb a_wceq a_wb i0_mpt22eqb a_wal f1_mpt22eqb f3_mpt22eqb a_wral f0_mpt22eqb f2_mpt22eqb a_wral f0_mpt22eqb f1_mpt22eqb f2_mpt22eqb f3_mpt22eqb f4_mpt22eqb a_cmpt2 f0_mpt22eqb f1_mpt22eqb f2_mpt22eqb f3_mpt22eqb f5_mpt22eqb a_cmpt2 a_wceq p_syl6rbbr $.
$}

$(The range of an operation given by the "maps to" notation.  (Contributed
       by FL, 20-Jun-2011.) $)

${
	$v x y z A B C F  $.
	$d x  $.
	$d y z A  $.
	$d z B  $.
	$d z C  $.
	$d z F  $.
	$d z  $.
	$d x y z  $.
	$d x y  $.
	f0_rnmpt2 $f set x $.
	f1_rnmpt2 $f set y $.
	f2_rnmpt2 $f set z $.
	f3_rnmpt2 $f class A $.
	f4_rnmpt2 $f class B $.
	f5_rnmpt2 $f class C $.
	f6_rnmpt2 $f class F $.
	e0_rnmpt2 $e |- F = ( x e. A , y e. B |-> C ) $.
	p_rnmpt2 $p |- ran F = { z | E. x e. A E. y e. B z = C } $= e0_rnmpt2 f0_rnmpt2 f1_rnmpt2 f2_rnmpt2 f3_rnmpt2 f4_rnmpt2 f5_rnmpt2 a_df-mpt2 f6_rnmpt2 f0_rnmpt2 f1_rnmpt2 f3_rnmpt2 f4_rnmpt2 f5_rnmpt2 a_cmpt2 f0_rnmpt2 a_sup_set_class f3_rnmpt2 a_wcel f1_rnmpt2 a_sup_set_class f4_rnmpt2 a_wcel a_wa f2_rnmpt2 a_sup_set_class f5_rnmpt2 a_wceq a_wa f0_rnmpt2 f1_rnmpt2 f2_rnmpt2 a_coprab p_eqtri f6_rnmpt2 f0_rnmpt2 a_sup_set_class f3_rnmpt2 a_wcel f1_rnmpt2 a_sup_set_class f4_rnmpt2 a_wcel a_wa f2_rnmpt2 a_sup_set_class f5_rnmpt2 a_wceq a_wa f0_rnmpt2 f1_rnmpt2 f2_rnmpt2 a_coprab p_rneqi f2_rnmpt2 a_sup_set_class f5_rnmpt2 a_wceq f0_rnmpt2 f1_rnmpt2 f2_rnmpt2 f3_rnmpt2 f4_rnmpt2 p_rnoprab2 f6_rnmpt2 a_crn f0_rnmpt2 a_sup_set_class f3_rnmpt2 a_wcel f1_rnmpt2 a_sup_set_class f4_rnmpt2 a_wcel a_wa f2_rnmpt2 a_sup_set_class f5_rnmpt2 a_wceq a_wa f0_rnmpt2 f1_rnmpt2 f2_rnmpt2 a_coprab a_crn f2_rnmpt2 a_sup_set_class f5_rnmpt2 a_wceq f1_rnmpt2 f4_rnmpt2 a_wrex f0_rnmpt2 f3_rnmpt2 a_wrex f2_rnmpt2 a_cab p_eqtri $.
$}

$(The domain of an operation defined by maps-to notation is a relation.
       (Contributed by Stefan O'Rear, 27-Nov-2014.) $)

${
	$v x y A B C F  $.
	$d x  $.
	$d y z A  $.
	$d z B  $.
	$d z C  $.
	$d z F  $.
	$d z  $.
	$d x y z  $.
	$d x y  $.
	f0_reldmmpt2 $f set x $.
	f1_reldmmpt2 $f set y $.
	f2_reldmmpt2 $f class A $.
	f3_reldmmpt2 $f class B $.
	f4_reldmmpt2 $f class C $.
	f5_reldmmpt2 $f class F $.
	i0_reldmmpt2 $f set z $.
	e0_reldmmpt2 $e |- F = ( x e. A , y e. B |-> C ) $.
	p_reldmmpt2 $p |- Rel dom F $= f0_reldmmpt2 a_sup_set_class f2_reldmmpt2 a_wcel f1_reldmmpt2 a_sup_set_class f3_reldmmpt2 a_wcel a_wa i0_reldmmpt2 a_sup_set_class f4_reldmmpt2 a_wceq a_wa f0_reldmmpt2 f1_reldmmpt2 i0_reldmmpt2 p_reldmoprab e0_reldmmpt2 f0_reldmmpt2 f1_reldmmpt2 i0_reldmmpt2 f2_reldmmpt2 f3_reldmmpt2 f4_reldmmpt2 a_df-mpt2 f5_reldmmpt2 f0_reldmmpt2 f1_reldmmpt2 f2_reldmmpt2 f3_reldmmpt2 f4_reldmmpt2 a_cmpt2 f0_reldmmpt2 a_sup_set_class f2_reldmmpt2 a_wcel f1_reldmmpt2 a_sup_set_class f3_reldmmpt2 a_wcel a_wa i0_reldmmpt2 a_sup_set_class f4_reldmmpt2 a_wceq a_wa f0_reldmmpt2 f1_reldmmpt2 i0_reldmmpt2 a_coprab p_eqtri f5_reldmmpt2 f0_reldmmpt2 a_sup_set_class f2_reldmmpt2 a_wcel f1_reldmmpt2 a_sup_set_class f3_reldmmpt2 a_wcel a_wa i0_reldmmpt2 a_sup_set_class f4_reldmmpt2 a_wceq a_wa f0_reldmmpt2 f1_reldmmpt2 i0_reldmmpt2 a_coprab p_dmeqi f5_reldmmpt2 a_cdm f0_reldmmpt2 a_sup_set_class f2_reldmmpt2 a_wcel f1_reldmmpt2 a_sup_set_class f3_reldmmpt2 a_wcel a_wa i0_reldmmpt2 a_sup_set_class f4_reldmmpt2 a_wceq a_wa f0_reldmmpt2 f1_reldmmpt2 i0_reldmmpt2 a_coprab a_cdm p_releqi f5_reldmmpt2 a_cdm a_wrel f0_reldmmpt2 a_sup_set_class f2_reldmmpt2 a_wcel f1_reldmmpt2 a_sup_set_class f3_reldmmpt2 a_wcel a_wa i0_reldmmpt2 a_sup_set_class f4_reldmmpt2 a_wceq a_wa f0_reldmmpt2 f1_reldmmpt2 i0_reldmmpt2 a_coprab a_cdm a_wrel p_mpbir $.
$}

$(Membership in the range of an operation class abstraction.  (Contributed
       by NM, 27-Aug-2007.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)

${
	$v x y A B C D F V  $.
	$d x  $.
	$d y z A  $.
	$d z B  $.
	$d z C  $.
	$d z F  $.
	$d z  $.
	$d x y z D  $.
	$d x y  $.
	f0_elrnmpt2g $f set x $.
	f1_elrnmpt2g $f set y $.
	f2_elrnmpt2g $f class A $.
	f3_elrnmpt2g $f class B $.
	f4_elrnmpt2g $f class C $.
	f5_elrnmpt2g $f class D $.
	f6_elrnmpt2g $f class F $.
	f7_elrnmpt2g $f class V $.
	i0_elrnmpt2g $f set z $.
	e0_elrnmpt2g $e |- F = ( x e. A , y e. B |-> C ) $.
	p_elrnmpt2g $p |- ( D e. V -> ( D e. ran F <-> E. x e. A E. y e. B D = C ) ) $= i0_elrnmpt2g a_sup_set_class f5_elrnmpt2g f4_elrnmpt2g p_eqeq1 i0_elrnmpt2g a_sup_set_class f5_elrnmpt2g a_wceq i0_elrnmpt2g a_sup_set_class f4_elrnmpt2g a_wceq f5_elrnmpt2g f4_elrnmpt2g a_wceq f0_elrnmpt2g f1_elrnmpt2g f2_elrnmpt2g f3_elrnmpt2g p_2rexbidv e0_elrnmpt2g f0_elrnmpt2g f1_elrnmpt2g i0_elrnmpt2g f2_elrnmpt2g f3_elrnmpt2g f4_elrnmpt2g f6_elrnmpt2g p_rnmpt2 i0_elrnmpt2g a_sup_set_class f4_elrnmpt2g a_wceq f1_elrnmpt2g f3_elrnmpt2g a_wrex f0_elrnmpt2g f2_elrnmpt2g a_wrex f5_elrnmpt2g f4_elrnmpt2g a_wceq f1_elrnmpt2g f3_elrnmpt2g a_wrex f0_elrnmpt2g f2_elrnmpt2g a_wrex i0_elrnmpt2g f5_elrnmpt2g f6_elrnmpt2g a_crn f7_elrnmpt2g p_elab2g $.
$}

$(Membership in the range of an operation class abstraction.
         (Contributed by NM, 1-Aug-2004.)  (Revised by Mario Carneiro,
         31-Aug-2015.) $)

${
	$v x y A B C D F  $.
	$d x  $.
	$d y z A  $.
	$d z B  $.
	$d z C  $.
	$d z F  $.
	$d z  $.
	$d x y z D  $.
	$d x y  $.
	f0_elrnmpt2 $f set x $.
	f1_elrnmpt2 $f set y $.
	f2_elrnmpt2 $f class A $.
	f3_elrnmpt2 $f class B $.
	f4_elrnmpt2 $f class C $.
	f5_elrnmpt2 $f class D $.
	f6_elrnmpt2 $f class F $.
	i0_elrnmpt2 $f set z $.
	e0_elrnmpt2 $e |- F = ( x e. A , y e. B |-> C ) $.
	e1_elrnmpt2 $e |- C e. _V $.
	p_elrnmpt2 $p |- ( D e. ran F <-> E. x e. A E. y e. B D = C ) $= e0_elrnmpt2 f0_elrnmpt2 f1_elrnmpt2 i0_elrnmpt2 f2_elrnmpt2 f3_elrnmpt2 f4_elrnmpt2 f6_elrnmpt2 p_rnmpt2 f6_elrnmpt2 a_crn i0_elrnmpt2 a_sup_set_class f4_elrnmpt2 a_wceq f1_elrnmpt2 f3_elrnmpt2 a_wrex f0_elrnmpt2 f2_elrnmpt2 a_wrex i0_elrnmpt2 a_cab f5_elrnmpt2 p_eleq2i e1_elrnmpt2 f5_elrnmpt2 f4_elrnmpt2 a_cvv p_eleq1 f5_elrnmpt2 f4_elrnmpt2 a_wceq f5_elrnmpt2 a_cvv a_wcel f4_elrnmpt2 a_cvv a_wcel p_mpbiri f5_elrnmpt2 f4_elrnmpt2 a_wceq f5_elrnmpt2 a_cvv a_wcel f1_elrnmpt2 f3_elrnmpt2 p_rexlimivw f5_elrnmpt2 f4_elrnmpt2 a_wceq f1_elrnmpt2 f3_elrnmpt2 a_wrex f5_elrnmpt2 a_cvv a_wcel f0_elrnmpt2 f2_elrnmpt2 p_rexlimivw i0_elrnmpt2 a_sup_set_class f5_elrnmpt2 f4_elrnmpt2 p_eqeq1 i0_elrnmpt2 a_sup_set_class f5_elrnmpt2 a_wceq i0_elrnmpt2 a_sup_set_class f4_elrnmpt2 a_wceq f5_elrnmpt2 f4_elrnmpt2 a_wceq f0_elrnmpt2 f1_elrnmpt2 f2_elrnmpt2 f3_elrnmpt2 p_2rexbidv i0_elrnmpt2 a_sup_set_class f4_elrnmpt2 a_wceq f1_elrnmpt2 f3_elrnmpt2 a_wrex f0_elrnmpt2 f2_elrnmpt2 a_wrex f5_elrnmpt2 f4_elrnmpt2 a_wceq f1_elrnmpt2 f3_elrnmpt2 a_wrex f0_elrnmpt2 f2_elrnmpt2 a_wrex i0_elrnmpt2 f5_elrnmpt2 p_elab3 f5_elrnmpt2 f6_elrnmpt2 a_crn a_wcel f5_elrnmpt2 i0_elrnmpt2 a_sup_set_class f4_elrnmpt2 a_wceq f1_elrnmpt2 f3_elrnmpt2 a_wrex f0_elrnmpt2 f2_elrnmpt2 a_wrex i0_elrnmpt2 a_cab a_wcel f5_elrnmpt2 f4_elrnmpt2 a_wceq f1_elrnmpt2 f3_elrnmpt2 a_wrex f0_elrnmpt2 f2_elrnmpt2 a_wrex p_bitri $.
$}

$(A restricted quantifier over an image set.  (Contributed by Mario
       Carneiro, 1-Sep-2015.) $)

${
	$v ph ps x y z A B C F V  $.
	$d w x  $.
	$d w y z A  $.
	$d w z B  $.
	$d w z C  $.
	$d w z F  $.
	$d z ps  $.
	$d x y z  $.
	$d x y ph  $.
	f0_ralrnmpt2 $f wff ph $.
	f1_ralrnmpt2 $f wff ps $.
	f2_ralrnmpt2 $f set x $.
	f3_ralrnmpt2 $f set y $.
	f4_ralrnmpt2 $f set z $.
	f5_ralrnmpt2 $f class A $.
	f6_ralrnmpt2 $f class B $.
	f7_ralrnmpt2 $f class C $.
	f8_ralrnmpt2 $f class F $.
	f9_ralrnmpt2 $f class V $.
	i0_ralrnmpt2 $f set w $.
	e0_ralrnmpt2 $e |- F = ( x e. A , y e. B |-> C ) $.
	e1_ralrnmpt2 $e |- ( z = C -> ( ph <-> ps ) ) $.
	p_ralrnmpt2 $p |- ( A. x e. A A. y e. B C e. V -> ( A. z e. ran F ph <-> A. x e. A A. y e. B ps ) ) $= e0_ralrnmpt2 f2_ralrnmpt2 f3_ralrnmpt2 i0_ralrnmpt2 f5_ralrnmpt2 f6_ralrnmpt2 f7_ralrnmpt2 f8_ralrnmpt2 p_rnmpt2 f0_ralrnmpt2 f4_ralrnmpt2 f8_ralrnmpt2 a_crn i0_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f2_ralrnmpt2 f5_ralrnmpt2 a_wrex i0_ralrnmpt2 a_cab p_raleqi i0_ralrnmpt2 a_sup_set_class f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 p_eqeq1 i0_ralrnmpt2 a_sup_set_class f4_ralrnmpt2 a_sup_set_class a_wceq i0_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f2_ralrnmpt2 f3_ralrnmpt2 f5_ralrnmpt2 f6_ralrnmpt2 p_2rexbidv i0_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f2_ralrnmpt2 f5_ralrnmpt2 a_wrex f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f2_ralrnmpt2 f5_ralrnmpt2 a_wrex f0_ralrnmpt2 f4_ralrnmpt2 i0_ralrnmpt2 p_ralab f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f2_ralrnmpt2 f4_ralrnmpt2 f5_ralrnmpt2 p_ralcom4 f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 f2_ralrnmpt2 f5_ralrnmpt2 p_r19.23v f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f2_ralrnmpt2 f5_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f2_ralrnmpt2 f5_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 p_albii f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f2_ralrnmpt2 f5_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f2_ralrnmpt2 f5_ralrnmpt2 a_wral f4_ralrnmpt2 a_wal f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f2_ralrnmpt2 f5_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal p_bitr2i f0_ralrnmpt2 f4_ralrnmpt2 f8_ralrnmpt2 a_crn a_wral f0_ralrnmpt2 f4_ralrnmpt2 i0_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f2_ralrnmpt2 f5_ralrnmpt2 a_wrex i0_ralrnmpt2 a_cab a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f2_ralrnmpt2 f5_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f2_ralrnmpt2 f5_ralrnmpt2 a_wral p_3bitri f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f3_ralrnmpt2 f4_ralrnmpt2 f6_ralrnmpt2 p_ralcom4 f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 p_r19.23v f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f3_ralrnmpt2 f6_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 p_albii f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f3_ralrnmpt2 f6_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f3_ralrnmpt2 f6_ralrnmpt2 a_wral f4_ralrnmpt2 a_wal f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal p_bitri f1_ralrnmpt2 f4_ralrnmpt2 p_nfv e1_ralrnmpt2 f0_ralrnmpt2 f1_ralrnmpt2 f4_ralrnmpt2 f7_ralrnmpt2 f9_ralrnmpt2 p_ceqsalg f7_ralrnmpt2 f9_ralrnmpt2 a_wcel f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f1_ralrnmpt2 a_wb f3_ralrnmpt2 f6_ralrnmpt2 p_ralimi f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f1_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 p_ralbi f7_ralrnmpt2 f9_ralrnmpt2 a_wcel f3_ralrnmpt2 f6_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f1_ralrnmpt2 a_wb f3_ralrnmpt2 f6_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f3_ralrnmpt2 f6_ralrnmpt2 a_wral f1_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 a_wral a_wb p_syl f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f3_ralrnmpt2 f6_ralrnmpt2 a_wral f7_ralrnmpt2 f9_ralrnmpt2 a_wcel f3_ralrnmpt2 f6_ralrnmpt2 a_wral f1_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 a_wral p_syl5bbr f7_ralrnmpt2 f9_ralrnmpt2 a_wcel f3_ralrnmpt2 f6_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f1_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 a_wral a_wb f2_ralrnmpt2 f5_ralrnmpt2 p_ralimi f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f1_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 a_wral f2_ralrnmpt2 f5_ralrnmpt2 p_ralbi f7_ralrnmpt2 f9_ralrnmpt2 a_wcel f3_ralrnmpt2 f6_ralrnmpt2 a_wral f2_ralrnmpt2 f5_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f1_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 a_wral a_wb f2_ralrnmpt2 f5_ralrnmpt2 a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f2_ralrnmpt2 f5_ralrnmpt2 a_wral f1_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 a_wral f2_ralrnmpt2 f5_ralrnmpt2 a_wral a_wb p_syl f0_ralrnmpt2 f4_ralrnmpt2 f8_ralrnmpt2 a_crn a_wral f4_ralrnmpt2 a_sup_set_class f7_ralrnmpt2 a_wceq f3_ralrnmpt2 f6_ralrnmpt2 a_wrex f0_ralrnmpt2 a_wi f4_ralrnmpt2 a_wal f2_ralrnmpt2 f5_ralrnmpt2 a_wral f7_ralrnmpt2 f9_ralrnmpt2 a_wcel f3_ralrnmpt2 f6_ralrnmpt2 a_wral f2_ralrnmpt2 f5_ralrnmpt2 a_wral f1_ralrnmpt2 f3_ralrnmpt2 f6_ralrnmpt2 a_wral f2_ralrnmpt2 f5_ralrnmpt2 a_wral p_syl5bb $.
$}

$(A restricted quantifier over an image set.  (Contributed by Mario
       Carneiro, 1-Sep-2015.) $)

${
	$v ph ps x y z A B C F V  $.
	$d x  $.
	$d y z A  $.
	$d z B  $.
	$d z C  $.
	$d z F  $.
	$d z ps  $.
	$d x y z  $.
	$d x y ph  $.
	f0_rexrnmpt2 $f wff ph $.
	f1_rexrnmpt2 $f wff ps $.
	f2_rexrnmpt2 $f set x $.
	f3_rexrnmpt2 $f set y $.
	f4_rexrnmpt2 $f set z $.
	f5_rexrnmpt2 $f class A $.
	f6_rexrnmpt2 $f class B $.
	f7_rexrnmpt2 $f class C $.
	f8_rexrnmpt2 $f class F $.
	f9_rexrnmpt2 $f class V $.
	e0_rexrnmpt2 $e |- F = ( x e. A , y e. B |-> C ) $.
	e1_rexrnmpt2 $e |- ( z = C -> ( ph <-> ps ) ) $.
	p_rexrnmpt2 $p |- ( A. x e. A A. y e. B C e. V -> ( E. z e. ran F ph <-> E. x e. A E. y e. B ps ) ) $= e0_rexrnmpt2 e1_rexrnmpt2 f4_rexrnmpt2 a_sup_set_class f7_rexrnmpt2 a_wceq f0_rexrnmpt2 f1_rexrnmpt2 p_notbid f0_rexrnmpt2 a_wn f1_rexrnmpt2 a_wn f2_rexrnmpt2 f3_rexrnmpt2 f4_rexrnmpt2 f5_rexrnmpt2 f6_rexrnmpt2 f7_rexrnmpt2 f8_rexrnmpt2 f9_rexrnmpt2 p_ralrnmpt2 f7_rexrnmpt2 f9_rexrnmpt2 a_wcel f3_rexrnmpt2 f6_rexrnmpt2 a_wral f2_rexrnmpt2 f5_rexrnmpt2 a_wral f0_rexrnmpt2 a_wn f4_rexrnmpt2 f8_rexrnmpt2 a_crn a_wral f1_rexrnmpt2 a_wn f3_rexrnmpt2 f6_rexrnmpt2 a_wral f2_rexrnmpt2 f5_rexrnmpt2 a_wral p_notbid f0_rexrnmpt2 f4_rexrnmpt2 f8_rexrnmpt2 a_crn p_dfrex2 f1_rexrnmpt2 f3_rexrnmpt2 f6_rexrnmpt2 p_dfrex2 f1_rexrnmpt2 f3_rexrnmpt2 f6_rexrnmpt2 a_wrex f1_rexrnmpt2 a_wn f3_rexrnmpt2 f6_rexrnmpt2 a_wral a_wn f2_rexrnmpt2 f5_rexrnmpt2 p_rexbii f1_rexrnmpt2 a_wn f3_rexrnmpt2 f6_rexrnmpt2 a_wral f2_rexrnmpt2 f5_rexrnmpt2 p_rexnal f1_rexrnmpt2 f3_rexrnmpt2 f6_rexrnmpt2 a_wrex f2_rexrnmpt2 f5_rexrnmpt2 a_wrex f1_rexrnmpt2 a_wn f3_rexrnmpt2 f6_rexrnmpt2 a_wral a_wn f2_rexrnmpt2 f5_rexrnmpt2 a_wrex f1_rexrnmpt2 a_wn f3_rexrnmpt2 f6_rexrnmpt2 a_wral f2_rexrnmpt2 f5_rexrnmpt2 a_wral a_wn p_bitri f7_rexrnmpt2 f9_rexrnmpt2 a_wcel f3_rexrnmpt2 f6_rexrnmpt2 a_wral f2_rexrnmpt2 f5_rexrnmpt2 a_wral f0_rexrnmpt2 a_wn f4_rexrnmpt2 f8_rexrnmpt2 a_crn a_wral a_wn f1_rexrnmpt2 a_wn f3_rexrnmpt2 f6_rexrnmpt2 a_wral f2_rexrnmpt2 f5_rexrnmpt2 a_wral a_wn f0_rexrnmpt2 f4_rexrnmpt2 f8_rexrnmpt2 a_crn a_wrex f1_rexrnmpt2 f3_rexrnmpt2 f6_rexrnmpt2 a_wrex f2_rexrnmpt2 f5_rexrnmpt2 a_wrex p_3bitr4g $.
$}

$(Existence of an operator abstraction.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)

${
	$v ph ps x y z A B F  $.
	$d A x y z  $.
	$d B x y z  $.
	$d ph x y z  $.
	f0_oprabexd $f wff ph $.
	f1_oprabexd $f wff ps $.
	f2_oprabexd $f set x $.
	f3_oprabexd $f set y $.
	f4_oprabexd $f set z $.
	f5_oprabexd $f class A $.
	f6_oprabexd $f class B $.
	f7_oprabexd $f class F $.
	e0_oprabexd $e |- ( ph -> A e. _V ) $.
	e1_oprabexd $e |- ( ph -> B e. _V ) $.
	e2_oprabexd $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> E* z ps ) $.
	e3_oprabexd $e |- ( ph -> F = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) } ) $.
	p_oprabexd $p |- ( ph -> F e. _V ) $= e3_oprabexd e2_oprabexd f0_oprabexd f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd f4_oprabexd a_wmo p_ex f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd f4_oprabexd p_moanimv f0_oprabexd f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd f4_oprabexd a_wmo a_wi f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f4_oprabexd a_wmo p_sylibr f0_oprabexd f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f4_oprabexd a_wmo f2_oprabexd f3_oprabexd p_alrimivv f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd p_funoprabg f0_oprabexd f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f4_oprabexd a_wmo f3_oprabexd a_wal f2_oprabexd a_wal f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab a_wfun p_syl f1_oprabexd f2_oprabexd f3_oprabexd f4_oprabexd f5_oprabexd f6_oprabexd p_dmoprabss e0_oprabexd e1_oprabexd f5_oprabexd f6_oprabexd a_cvv a_cvv p_xpexg f0_oprabexd f5_oprabexd a_cvv a_wcel f6_oprabexd a_cvv a_wcel f5_oprabexd f6_oprabexd a_cxp a_cvv a_wcel p_syl2anc f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab a_cdm f5_oprabexd f6_oprabexd a_cxp a_cvv p_ssexg f0_oprabexd f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab a_cdm f5_oprabexd f6_oprabexd a_cxp a_wss f5_oprabexd f6_oprabexd a_cxp a_cvv a_wcel f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab a_cdm a_cvv a_wcel p_sylancr a_cvv f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab p_funex f0_oprabexd f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab a_wfun f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab a_cdm a_cvv a_wcel f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab a_cvv a_wcel p_syl2anc f0_oprabexd f7_oprabexd f2_oprabexd a_sup_set_class f5_oprabexd a_wcel f3_oprabexd a_sup_set_class f6_oprabexd a_wcel a_wa f1_oprabexd a_wa f2_oprabexd f3_oprabexd f4_oprabexd a_coprab a_cvv p_eqeltrd $.
$}

$(Existence of an operation class abstraction.  (Contributed by NM,
       19-Oct-2004.) $)

${
	$v ph x y z A B F  $.
	$d x y z A  $.
	$d x y z B  $.
	f0_oprabex $f wff ph $.
	f1_oprabex $f set x $.
	f2_oprabex $f set y $.
	f3_oprabex $f set z $.
	f4_oprabex $f class A $.
	f5_oprabex $f class B $.
	f6_oprabex $f class F $.
	e0_oprabex $e |- A e. _V $.
	e1_oprabex $e |- B e. _V $.
	e2_oprabex $e |- ( ( x e. A /\ y e. B ) -> E* z ph ) $.
	e3_oprabex $e |- F = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $.
	p_oprabex $p |- F e. _V $= e3_oprabex e2_oprabex f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex f3_oprabex p_moanimv f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex a_wa f3_oprabex a_wmo f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex f3_oprabex a_wmo a_wi p_mpbir f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex a_wa f1_oprabex f2_oprabex f3_oprabex p_funoprab e0_oprabex e1_oprabex f4_oprabex f5_oprabex p_xpex f0_oprabex f1_oprabex f2_oprabex f3_oprabex f4_oprabex f5_oprabex p_dmoprabss f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex a_wa f1_oprabex f2_oprabex f3_oprabex a_coprab a_cdm f4_oprabex f5_oprabex a_cxp p_ssexi a_cvv f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex a_wa f1_oprabex f2_oprabex f3_oprabex a_coprab p_funex f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex a_wa f1_oprabex f2_oprabex f3_oprabex a_coprab a_wfun f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex a_wa f1_oprabex f2_oprabex f3_oprabex a_coprab a_cdm a_cvv a_wcel f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex a_wa f1_oprabex f2_oprabex f3_oprabex a_coprab a_cvv a_wcel p_mp2an f6_oprabex f1_oprabex a_sup_set_class f4_oprabex a_wcel f2_oprabex a_sup_set_class f5_oprabex a_wcel a_wa f0_oprabex a_wa f1_oprabex f2_oprabex f3_oprabex a_coprab a_cvv p_eqeltri $.
$}

$(Existence of an operation class abstraction (special case).
       (Contributed by NM, 19-Oct-2004.) $)

${
	$v x y z w v u R f F H  $.
	$d x y z w v u f  $.
	$d x y z w v u f  $.
	$d x y z w v u f  $.
	$d x y z w v u f  $.
	$d x y z w v u f H  $.
	$d x y z R  $.
	$d x y z w v u f  $.
	f0_oprabex3 $f set x $.
	f1_oprabex3 $f set y $.
	f2_oprabex3 $f set z $.
	f3_oprabex3 $f set w $.
	f4_oprabex3 $f set v $.
	f5_oprabex3 $f set u $.
	f6_oprabex3 $f class R $.
	f7_oprabex3 $f set f $.
	f8_oprabex3 $f class F $.
	f9_oprabex3 $f class H $.
	e0_oprabex3 $e |- H e. _V $.
	e1_oprabex3 $e |- F = { <. <. x , y >. , z >. | ( ( x e. ( H X. H ) /\ y e. ( H X. H ) ) /\ E. w E. v E. u E. f ( ( x = <. w , v >. /\ y = <. u , f >. ) /\ z = R ) ) } $.
	p_oprabex3 $p |- F e. _V $= e0_oprabex3 e0_oprabex3 f9_oprabex3 f9_oprabex3 p_xpex e0_oprabex3 e0_oprabex3 f9_oprabex3 f9_oprabex3 p_xpex f2_oprabex3 f6_oprabex3 p_moeq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq f2_oprabex3 f5_oprabex3 f7_oprabex3 f1_oprabex3 a_sup_set_class p_mosubop f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex f2_oprabex3 f3_oprabex3 f4_oprabex3 f0_oprabex3 a_sup_set_class p_mosubop f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq p_anass f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq a_wa f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa a_wa f5_oprabex3 f7_oprabex3 p_2exbii f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f5_oprabex3 f7_oprabex3 p_19.42vv f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq a_wa f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex a_wa p_bitri f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq a_wa f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex a_wa f3_oprabex3 f4_oprabex3 p_2exbii f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq a_wa f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex f4_oprabex3 a_wex f3_oprabex3 a_wex f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex a_wa f4_oprabex3 a_wex f3_oprabex3 a_wex f2_oprabex3 p_mobii f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq a_wa f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex f4_oprabex3 a_wex f3_oprabex3 a_wex f2_oprabex3 a_wmo f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex a_wa f4_oprabex3 a_wex f3_oprabex3 a_wex f2_oprabex3 a_wmo p_mpbir f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq a_wa f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex f4_oprabex3 a_wex f3_oprabex3 a_wex f2_oprabex3 a_wmo f0_oprabex3 a_sup_set_class f9_oprabex3 f9_oprabex3 a_cxp a_wcel f1_oprabex3 a_sup_set_class f9_oprabex3 f9_oprabex3 a_cxp a_wcel a_wa p_a1i e1_oprabex3 f0_oprabex3 a_sup_set_class f3_oprabex3 a_sup_set_class f4_oprabex3 a_sup_set_class a_cop a_wceq f1_oprabex3 a_sup_set_class f5_oprabex3 a_sup_set_class f7_oprabex3 a_sup_set_class a_cop a_wceq a_wa f2_oprabex3 a_sup_set_class f6_oprabex3 a_wceq a_wa f7_oprabex3 a_wex f5_oprabex3 a_wex f4_oprabex3 a_wex f3_oprabex3 a_wex f0_oprabex3 f1_oprabex3 f2_oprabex3 f9_oprabex3 f9_oprabex3 a_cxp f9_oprabex3 f9_oprabex3 a_cxp f8_oprabex3 p_oprabex $.
$}

$(Existence of an existentially restricted operation abstraction.
       (Contributed by Jeff Madsen, 11-Jun-2010.) $)

${
	$v ph x y z w A  $.
	$d A v x y z w  $.
	$d ph v  $.
	f0_oprabrexex2 $f wff ph $.
	f1_oprabrexex2 $f set x $.
	f2_oprabrexex2 $f set y $.
	f3_oprabrexex2 $f set z $.
	f4_oprabrexex2 $f set w $.
	f5_oprabrexex2 $f class A $.
	i0_oprabrexex2 $f set v $.
	e0_oprabrexex2 $e |- A e. _V $.
	e1_oprabrexex2 $e |- { <. <. x , y >. , z >. | ph } e. _V $.
	p_oprabrexex2 $p |- { <. <. x , y >. , z >. | E. w e. A ph } e. _V $= f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex f1_oprabrexex2 f2_oprabrexex2 f3_oprabrexex2 i0_oprabrexex2 a_df-oprab i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f4_oprabrexex2 f1_oprabrexex2 f5_oprabrexex2 p_rexcom4 i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f4_oprabrexex2 f2_oprabrexex2 f5_oprabrexex2 p_rexcom4 i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f4_oprabrexex2 f3_oprabrexex2 f5_oprabrexex2 p_rexcom4 i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 p_r19.42v i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex a_wa f3_oprabrexex2 p_exbii i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f4_oprabrexex2 f5_oprabrexex2 a_wrex f3_oprabrexex2 a_wex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex a_wa f3_oprabrexex2 a_wex p_bitri i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 p_exbii i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex f2_oprabrexex2 a_wex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex p_bitri i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 p_exbii i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex f1_oprabrexex2 a_wex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex p_bitr2i i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 p_abbii f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex f1_oprabrexex2 f2_oprabrexex2 f3_oprabrexex2 a_coprab i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex i0_oprabrexex2 a_cab i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 a_cab p_eqtri e0_oprabrexex2 f0_oprabrexex2 f1_oprabrexex2 f2_oprabrexex2 f3_oprabrexex2 i0_oprabrexex2 a_df-oprab e1_oprabrexex2 f0_oprabrexex2 f1_oprabrexex2 f2_oprabrexex2 f3_oprabrexex2 a_coprab i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex i0_oprabrexex2 a_cab a_cvv p_eqeltrri i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex f4_oprabrexex2 i0_oprabrexex2 f5_oprabrexex2 p_abrexex2 f0_oprabrexex2 f4_oprabrexex2 f5_oprabrexex2 a_wrex f1_oprabrexex2 f2_oprabrexex2 f3_oprabrexex2 a_coprab i0_oprabrexex2 a_sup_set_class f1_oprabrexex2 a_sup_set_class f2_oprabrexex2 a_sup_set_class a_cop f3_oprabrexex2 a_sup_set_class a_cop a_wceq f0_oprabrexex2 a_wa f3_oprabrexex2 a_wex f2_oprabrexex2 a_wex f1_oprabrexex2 a_wex f4_oprabrexex2 f5_oprabrexex2 a_wrex i0_oprabrexex2 a_cab a_cvv p_eqeltri $.
$}

$(The value of an operation class abstraction.  (Contributed by NM,
       16-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)

${
	$v ph x y z R S F  $.
	$d x y z  $.
	$d z R  $.
	$d z S  $.
	f0_ovid $f wff ph $.
	f1_ovid $f set x $.
	f2_ovid $f set y $.
	f3_ovid $f set z $.
	f4_ovid $f class R $.
	f5_ovid $f class S $.
	f6_ovid $f class F $.
	e0_ovid $e |- ( ( x e. R /\ y e. S ) -> E! z ph ) $.
	e1_ovid $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	p_ovid $p |- ( ( x e. R /\ y e. S ) -> ( ( x F y ) = z <-> ph ) ) $= f1_ovid a_sup_set_class f2_ovid a_sup_set_class f6_ovid a_df-ov f1_ovid a_sup_set_class f2_ovid a_sup_set_class f6_ovid a_co f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f6_ovid a_cfv f3_ovid a_sup_set_class p_eqeq1i e0_ovid f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid f1_ovid f2_ovid f3_ovid p_fnoprab e1_ovid f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid f2_ovid a_copab f6_ovid f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid a_wa f1_ovid f2_ovid f3_ovid a_coprab p_fneq1i f6_ovid f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid f2_ovid a_copab a_wfn f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid a_wa f1_ovid f2_ovid f3_ovid a_coprab f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid f2_ovid a_copab a_wfn p_mpbir f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid f2_ovid p_opabid f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid f2_ovid a_copab a_wcel f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa p_biimpri f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid f2_ovid a_copab f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f3_ovid a_sup_set_class f6_ovid p_fnopfvb f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f6_ovid f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid f2_ovid a_copab a_wfn f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid f2_ovid a_copab a_wcel f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f6_ovid a_cfv f3_ovid a_sup_set_class a_wceq f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f3_ovid a_sup_set_class a_cop f6_ovid a_wcel a_wb p_sylancr e1_ovid f6_ovid f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid a_wa f1_ovid f2_ovid f3_ovid a_coprab f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f3_ovid a_sup_set_class a_cop p_eleq2i f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid a_wa f1_ovid f2_ovid f3_ovid p_oprabid f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f3_ovid a_sup_set_class a_cop f6_ovid a_wcel f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f3_ovid a_sup_set_class a_cop f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid a_wa f1_ovid f2_ovid f3_ovid a_coprab a_wcel f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid a_wa p_bitri f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f3_ovid a_sup_set_class a_cop f6_ovid a_wcel f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid p_baib f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f6_ovid a_cfv f3_ovid a_sup_set_class a_wceq f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f3_ovid a_sup_set_class a_cop f6_ovid a_wcel f0_ovid p_bitrd f1_ovid a_sup_set_class f2_ovid a_sup_set_class f6_ovid a_co f3_ovid a_sup_set_class a_wceq f1_ovid a_sup_set_class f2_ovid a_sup_set_class a_cop f6_ovid a_cfv f3_ovid a_sup_set_class a_wceq f1_ovid a_sup_set_class f4_ovid a_wcel f2_ovid a_sup_set_class f5_ovid a_wcel a_wa f0_ovid p_syl5bb $.
$}

$(The value of an operation class abstraction.  Compare ~ ovidi .  The
       condition ` ( x e. R /\ y e. S ) ` is been removed.  (Contributed by
       Mario Carneiro, 29-Dec-2014.) $)

${
	$v ph x y z F  $.
	$d x y z  $.
	f0_ovidig $f wff ph $.
	f1_ovidig $f set x $.
	f2_ovidig $f set y $.
	f3_ovidig $f set z $.
	f4_ovidig $f class F $.
	e0_ovidig $e |- E* z ph $.
	e1_ovidig $e |- F = { <. <. x , y >. , z >. | ph } $.
	p_ovidig $p |- ( ph -> ( x F y ) = z ) $= f1_ovidig a_sup_set_class f2_ovidig a_sup_set_class f4_ovidig a_df-ov e0_ovidig f0_ovidig f1_ovidig f2_ovidig f3_ovidig p_funoprab e1_ovidig f4_ovidig f0_ovidig f1_ovidig f2_ovidig f3_ovidig a_coprab p_funeqi f4_ovidig a_wfun f0_ovidig f1_ovidig f2_ovidig f3_ovidig a_coprab a_wfun p_mpbir f0_ovidig f1_ovidig f2_ovidig f3_ovidig p_oprabid f1_ovidig a_sup_set_class f2_ovidig a_sup_set_class a_cop f3_ovidig a_sup_set_class a_cop f0_ovidig f1_ovidig f2_ovidig f3_ovidig a_coprab a_wcel f0_ovidig p_biimpri e1_ovidig f0_ovidig f1_ovidig a_sup_set_class f2_ovidig a_sup_set_class a_cop f3_ovidig a_sup_set_class a_cop f0_ovidig f1_ovidig f2_ovidig f3_ovidig a_coprab f4_ovidig p_syl6eleqr f1_ovidig a_sup_set_class f2_ovidig a_sup_set_class a_cop f3_ovidig a_sup_set_class f4_ovidig p_funopfv f4_ovidig a_wfun f0_ovidig f1_ovidig a_sup_set_class f2_ovidig a_sup_set_class a_cop f3_ovidig a_sup_set_class a_cop f4_ovidig a_wcel f1_ovidig a_sup_set_class f2_ovidig a_sup_set_class a_cop f4_ovidig a_cfv f3_ovidig a_sup_set_class a_wceq p_mpsyl f0_ovidig f1_ovidig a_sup_set_class f2_ovidig a_sup_set_class f4_ovidig a_co f1_ovidig a_sup_set_class f2_ovidig a_sup_set_class a_cop f4_ovidig a_cfv f3_ovidig a_sup_set_class p_syl5eq $.
$}

$(The value of an operation class abstraction (weak version).
       (Contributed by Mario Carneiro, 29-Dec-2014.) $)

${
	$v ph x y z R S F  $.
	$d x y z  $.
	$d z R  $.
	$d z S  $.
	f0_ovidi $f wff ph $.
	f1_ovidi $f set x $.
	f2_ovidi $f set y $.
	f3_ovidi $f set z $.
	f4_ovidi $f class R $.
	f5_ovidi $f class S $.
	f6_ovidi $f class F $.
	e0_ovidi $e |- ( ( x e. R /\ y e. S ) -> E* z ph ) $.
	e1_ovidi $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	p_ovidi $p |- ( ( x e. R /\ y e. S ) -> ( ph -> ( x F y ) = z ) ) $= e0_ovidi f1_ovidi a_sup_set_class f4_ovidi a_wcel f2_ovidi a_sup_set_class f5_ovidi a_wcel a_wa f0_ovidi f3_ovidi p_moanimv f1_ovidi a_sup_set_class f4_ovidi a_wcel f2_ovidi a_sup_set_class f5_ovidi a_wcel a_wa f0_ovidi a_wa f3_ovidi a_wmo f1_ovidi a_sup_set_class f4_ovidi a_wcel f2_ovidi a_sup_set_class f5_ovidi a_wcel a_wa f0_ovidi f3_ovidi a_wmo a_wi p_mpbir e1_ovidi f1_ovidi a_sup_set_class f4_ovidi a_wcel f2_ovidi a_sup_set_class f5_ovidi a_wcel a_wa f0_ovidi a_wa f1_ovidi f2_ovidi f3_ovidi f6_ovidi p_ovidig f1_ovidi a_sup_set_class f4_ovidi a_wcel f2_ovidi a_sup_set_class f5_ovidi a_wcel a_wa f0_ovidi f1_ovidi a_sup_set_class f2_ovidi a_sup_set_class f6_ovidi a_co f3_ovidi a_sup_set_class a_wceq p_ex $.
$}

$(The value of an operation class abstraction.  (Contributed by NM,
       16-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)

${
	$v ph ps ch th x y z A B C R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z th  $.
	f0_ov $f wff ph $.
	f1_ov $f wff ps $.
	f2_ov $f wff ch $.
	f3_ov $f wff th $.
	f4_ov $f set x $.
	f5_ov $f set y $.
	f6_ov $f set z $.
	f7_ov $f class A $.
	f8_ov $f class B $.
	f9_ov $f class C $.
	f10_ov $f class R $.
	f11_ov $f class S $.
	f12_ov $f class F $.
	e0_ov $e |- C e. _V $.
	e1_ov $e |- ( x = A -> ( ph <-> ps ) ) $.
	e2_ov $e |- ( y = B -> ( ps <-> ch ) ) $.
	e3_ov $e |- ( z = C -> ( ch <-> th ) ) $.
	e4_ov $e |- ( ( x e. R /\ y e. S ) -> E! z ph ) $.
	e5_ov $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	p_ov $p |- ( ( A e. R /\ B e. S ) -> ( ( A F B ) = C <-> th ) ) $= f7_ov f8_ov f12_ov a_df-ov e5_ov f7_ov f8_ov a_cop f12_ov f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab p_fveq1i f7_ov f8_ov f12_ov a_co f7_ov f8_ov a_cop f12_ov a_cfv f7_ov f8_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab a_cfv p_eqtri f7_ov f8_ov f12_ov a_co f7_ov f8_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab a_cfv f9_ov p_eqeq1i e4_ov f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov f4_ov f5_ov f6_ov p_fnoprab f4_ov a_sup_set_class f7_ov f10_ov p_eleq1 f4_ov a_sup_set_class f7_ov a_wceq f4_ov a_sup_set_class f10_ov a_wcel f7_ov f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel p_anbi1d f5_ov a_sup_set_class f8_ov f11_ov p_eleq1 f5_ov a_sup_set_class f8_ov a_wceq f5_ov a_sup_set_class f11_ov a_wcel f8_ov f11_ov a_wcel f7_ov f10_ov a_wcel p_anbi2d f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f7_ov f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f4_ov f5_ov f7_ov f8_ov f10_ov f11_ov p_opelopabg f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f7_ov f8_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f4_ov f5_ov a_copab a_wcel p_ibir f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f4_ov f5_ov a_copab f7_ov f8_ov a_cop f9_ov f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab p_fnopfvb f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f4_ov f5_ov a_copab a_wfn f7_ov f8_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f4_ov f5_ov a_copab a_wcel f7_ov f8_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab a_cfv f9_ov a_wceq f7_ov f8_ov a_cop f9_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab a_wcel a_wb p_sylancr e0_ov f4_ov a_sup_set_class f7_ov f10_ov p_eleq1 f4_ov a_sup_set_class f7_ov a_wceq f4_ov a_sup_set_class f10_ov a_wcel f7_ov f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel p_anbi1d e1_ov f4_ov a_sup_set_class f7_ov a_wceq f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f7_ov f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov f1_ov p_anbi12d f5_ov a_sup_set_class f8_ov f11_ov p_eleq1 f5_ov a_sup_set_class f8_ov a_wceq f5_ov a_sup_set_class f11_ov a_wcel f8_ov f11_ov a_wcel f7_ov f10_ov a_wcel p_anbi2d e2_ov f5_ov a_sup_set_class f8_ov a_wceq f7_ov f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f1_ov f2_ov p_anbi12d e3_ov f6_ov a_sup_set_class f9_ov a_wceq f2_ov f3_ov f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa p_anbi2d f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f7_ov f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f1_ov a_wa f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f2_ov a_wa f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f3_ov a_wa f4_ov f5_ov f6_ov f7_ov f8_ov f9_ov f10_ov f11_ov a_cvv p_eloprabg f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel f9_ov a_cvv a_wcel f7_ov f8_ov a_cop f9_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab a_wcel f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f3_ov a_wa a_wb p_mp3an3 f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f7_ov f8_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab a_cfv f9_ov a_wceq f7_ov f8_ov a_cop f9_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab a_wcel f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f3_ov a_wa p_bitrd f7_ov f8_ov f12_ov a_co f9_ov a_wceq f7_ov f8_ov a_cop f4_ov a_sup_set_class f10_ov a_wcel f5_ov a_sup_set_class f11_ov a_wcel a_wa f0_ov a_wa f4_ov f5_ov f6_ov a_coprab a_cfv f9_ov a_wceq f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f3_ov a_wa p_syl5bb f7_ov f10_ov a_wcel f8_ov f11_ov a_wcel a_wa f7_ov f8_ov f12_ov a_co f9_ov a_wceq f3_ov p_bianabs $.
$}

$(The value of an operation class abstraction.  Compare ~ ovig .  The
       condition ` ( x e. R /\ y e. S ) ` is been removed.  (Contributed by FL,
       24-Mar-2007.)  (Revised by Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps x y z A B C F V W X  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z ps  $.
	f0_ovigg $f wff ph $.
	f1_ovigg $f wff ps $.
	f2_ovigg $f set x $.
	f3_ovigg $f set y $.
	f4_ovigg $f set z $.
	f5_ovigg $f class A $.
	f6_ovigg $f class B $.
	f7_ovigg $f class C $.
	f8_ovigg $f class F $.
	f9_ovigg $f class V $.
	f10_ovigg $f class W $.
	f11_ovigg $f class X $.
	e0_ovigg $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	e1_ovigg $e |- E* z ph $.
	e2_ovigg $e |- F = { <. <. x , y >. , z >. | ph } $.
	p_ovigg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ps -> ( A F B ) = C ) ) $= e0_ovigg f0_ovigg f1_ovigg f2_ovigg f3_ovigg f4_ovigg f5_ovigg f6_ovigg f7_ovigg f9_ovigg f10_ovigg f11_ovigg p_eloprabga f5_ovigg f6_ovigg f8_ovigg a_df-ov e2_ovigg f5_ovigg f6_ovigg a_cop f8_ovigg f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab p_fveq1i f5_ovigg f6_ovigg f8_ovigg a_co f5_ovigg f6_ovigg a_cop f8_ovigg a_cfv f5_ovigg f6_ovigg a_cop f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab a_cfv p_eqtri e1_ovigg f0_ovigg f2_ovigg f3_ovigg f4_ovigg p_funoprab f5_ovigg f6_ovigg a_cop f7_ovigg f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab p_funopfv f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab a_wfun f5_ovigg f6_ovigg a_cop f7_ovigg a_cop f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab a_wcel f5_ovigg f6_ovigg a_cop f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab a_cfv f7_ovigg a_wceq a_wi a_ax-mp f5_ovigg f6_ovigg a_cop f7_ovigg a_cop f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab a_wcel f5_ovigg f6_ovigg f8_ovigg a_co f5_ovigg f6_ovigg a_cop f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab a_cfv f7_ovigg p_syl5eq f5_ovigg f9_ovigg a_wcel f6_ovigg f10_ovigg a_wcel f7_ovigg f11_ovigg a_wcel a_w3a f1_ovigg f5_ovigg f6_ovigg a_cop f7_ovigg a_cop f0_ovigg f2_ovigg f3_ovigg f4_ovigg a_coprab a_wcel f5_ovigg f6_ovigg f8_ovigg a_co f7_ovigg a_wceq p_syl6bir $.
$}

$(The value of an operation class abstraction (weak version).
       (Unnecessary distinct variable restrictions were removed by David
       Abernethy, 19-Jun-2012.)  (Contributed by NM, 14-Sep-1999.)  (Revised by
       Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps x y z A B C D R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z ps  $.
	f0_ovig $f wff ph $.
	f1_ovig $f wff ps $.
	f2_ovig $f set x $.
	f3_ovig $f set y $.
	f4_ovig $f set z $.
	f5_ovig $f class A $.
	f6_ovig $f class B $.
	f7_ovig $f class C $.
	f8_ovig $f class D $.
	f9_ovig $f class R $.
	f10_ovig $f class S $.
	f11_ovig $f class F $.
	e0_ovig $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	e1_ovig $e |- ( ( x e. R /\ y e. S ) -> E* z ph ) $.
	e2_ovig $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	p_ovig $p |- ( ( A e. R /\ B e. S /\ C e. D ) -> ( ps -> ( A F B ) = C ) ) $= f5_ovig f9_ovig a_wcel f6_ovig f10_ovig a_wcel f7_ovig f8_ovig a_wcel p_3simpa f2_ovig a_sup_set_class f5_ovig f9_ovig p_eleq1 f3_ovig a_sup_set_class f6_ovig f10_ovig p_eleq1 f2_ovig a_sup_set_class f5_ovig a_wceq f2_ovig a_sup_set_class f9_ovig a_wcel f5_ovig f9_ovig a_wcel f3_ovig a_sup_set_class f6_ovig a_wceq f3_ovig a_sup_set_class f10_ovig a_wcel f6_ovig f10_ovig a_wcel p_bi2anan9 f2_ovig a_sup_set_class f5_ovig a_wceq f3_ovig a_sup_set_class f6_ovig a_wceq f2_ovig a_sup_set_class f9_ovig a_wcel f3_ovig a_sup_set_class f10_ovig a_wcel a_wa f5_ovig f9_ovig a_wcel f6_ovig f10_ovig a_wcel a_wa a_wb f4_ovig a_sup_set_class f7_ovig a_wceq p_3adant3 e0_ovig f2_ovig a_sup_set_class f5_ovig a_wceq f3_ovig a_sup_set_class f6_ovig a_wceq f4_ovig a_sup_set_class f7_ovig a_wceq a_w3a f2_ovig a_sup_set_class f9_ovig a_wcel f3_ovig a_sup_set_class f10_ovig a_wcel a_wa f5_ovig f9_ovig a_wcel f6_ovig f10_ovig a_wcel a_wa f0_ovig f1_ovig p_anbi12d e1_ovig f2_ovig a_sup_set_class f9_ovig a_wcel f3_ovig a_sup_set_class f10_ovig a_wcel a_wa f0_ovig f4_ovig p_moanimv f2_ovig a_sup_set_class f9_ovig a_wcel f3_ovig a_sup_set_class f10_ovig a_wcel a_wa f0_ovig a_wa f4_ovig a_wmo f2_ovig a_sup_set_class f9_ovig a_wcel f3_ovig a_sup_set_class f10_ovig a_wcel a_wa f0_ovig f4_ovig a_wmo a_wi p_mpbir e2_ovig f2_ovig a_sup_set_class f9_ovig a_wcel f3_ovig a_sup_set_class f10_ovig a_wcel a_wa f0_ovig a_wa f5_ovig f9_ovig a_wcel f6_ovig f10_ovig a_wcel a_wa f1_ovig a_wa f2_ovig f3_ovig f4_ovig f5_ovig f6_ovig f7_ovig f11_ovig f9_ovig f10_ovig f8_ovig p_ovigg f5_ovig f9_ovig a_wcel f6_ovig f10_ovig a_wcel f7_ovig f8_ovig a_wcel a_w3a f5_ovig f9_ovig a_wcel f6_ovig f10_ovig a_wcel a_wa f1_ovig f5_ovig f6_ovig f11_ovig a_co f7_ovig a_wceq p_mpand $.
$}

$(Value of a function given by the "maps to" notation.  (This is the
       operation analog of ~ fvmpt2 .)  (Contributed by NM, 21-Feb-2004.)
       (Revised by Mario Carneiro, 1-Sep-2015.) $)

${
	$v x y A B C F V  $.
	$d x y z  $.
	$d z A  $.
	$d z B  $.
	$d z C  $.
	$d z F  $.
	f0_ovmpt4g $f set x $.
	f1_ovmpt4g $f set y $.
	f2_ovmpt4g $f class A $.
	f3_ovmpt4g $f class B $.
	f4_ovmpt4g $f class C $.
	f5_ovmpt4g $f class F $.
	f6_ovmpt4g $f class V $.
	i0_ovmpt4g $f set z $.
	e0_ovmpt4g $e |- F = ( x e. A , y e. B |-> C ) $.
	p_ovmpt4g $p |- ( ( x e. A /\ y e. B /\ C e. V ) -> ( x F y ) = C ) $= i0_ovmpt4g f4_ovmpt4g f6_ovmpt4g p_elisset i0_ovmpt4g f4_ovmpt4g p_moeq i0_ovmpt4g a_sup_set_class f4_ovmpt4g a_wceq i0_ovmpt4g a_wmo f0_ovmpt4g a_sup_set_class f2_ovmpt4g a_wcel f1_ovmpt4g a_sup_set_class f3_ovmpt4g a_wcel a_wa p_a1i e0_ovmpt4g f0_ovmpt4g f1_ovmpt4g i0_ovmpt4g f2_ovmpt4g f3_ovmpt4g f4_ovmpt4g a_df-mpt2 f5_ovmpt4g f0_ovmpt4g f1_ovmpt4g f2_ovmpt4g f3_ovmpt4g f4_ovmpt4g a_cmpt2 f0_ovmpt4g a_sup_set_class f2_ovmpt4g a_wcel f1_ovmpt4g a_sup_set_class f3_ovmpt4g a_wcel a_wa i0_ovmpt4g a_sup_set_class f4_ovmpt4g a_wceq a_wa f0_ovmpt4g f1_ovmpt4g i0_ovmpt4g a_coprab p_eqtri i0_ovmpt4g a_sup_set_class f4_ovmpt4g a_wceq f0_ovmpt4g f1_ovmpt4g i0_ovmpt4g f2_ovmpt4g f3_ovmpt4g f5_ovmpt4g p_ovidi i0_ovmpt4g a_sup_set_class f4_ovmpt4g f0_ovmpt4g a_sup_set_class f1_ovmpt4g a_sup_set_class f5_ovmpt4g a_co p_eqeq2 i0_ovmpt4g a_sup_set_class f4_ovmpt4g a_wceq f0_ovmpt4g a_sup_set_class f1_ovmpt4g a_sup_set_class f5_ovmpt4g a_co i0_ovmpt4g a_sup_set_class a_wceq f0_ovmpt4g a_sup_set_class f1_ovmpt4g a_sup_set_class f5_ovmpt4g a_co f4_ovmpt4g a_wceq f0_ovmpt4g a_sup_set_class f2_ovmpt4g a_wcel f1_ovmpt4g a_sup_set_class f3_ovmpt4g a_wcel a_wa p_mpbidi f0_ovmpt4g a_sup_set_class f2_ovmpt4g a_wcel f1_ovmpt4g a_sup_set_class f3_ovmpt4g a_wcel a_wa i0_ovmpt4g a_sup_set_class f4_ovmpt4g a_wceq f0_ovmpt4g a_sup_set_class f1_ovmpt4g a_sup_set_class f5_ovmpt4g a_co f4_ovmpt4g a_wceq i0_ovmpt4g p_exlimdv f4_ovmpt4g f6_ovmpt4g a_wcel i0_ovmpt4g a_sup_set_class f4_ovmpt4g a_wceq i0_ovmpt4g a_wex f0_ovmpt4g a_sup_set_class f2_ovmpt4g a_wcel f1_ovmpt4g a_sup_set_class f3_ovmpt4g a_wcel a_wa f0_ovmpt4g a_sup_set_class f1_ovmpt4g a_sup_set_class f5_ovmpt4g a_co f4_ovmpt4g a_wceq p_syl5 f0_ovmpt4g a_sup_set_class f2_ovmpt4g a_wcel f1_ovmpt4g a_sup_set_class f3_ovmpt4g a_wcel f4_ovmpt4g f6_ovmpt4g a_wcel f0_ovmpt4g a_sup_set_class f1_ovmpt4g a_sup_set_class f5_ovmpt4g a_co f4_ovmpt4g a_wceq p_3impia $.
$}

$(Value of a function given by the "maps to" notation, expressed using
       explicit substitution.  (Contributed by Mario Carneiro, 30-Apr-2015.) $)

${
	$v x y A B C D R F V  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y D  $.
	$d F  $.
	$d R  $.
	f0_ovmpt2s $f set x $.
	f1_ovmpt2s $f set y $.
	f2_ovmpt2s $f class A $.
	f3_ovmpt2s $f class B $.
	f4_ovmpt2s $f class C $.
	f5_ovmpt2s $f class D $.
	f6_ovmpt2s $f class R $.
	f7_ovmpt2s $f class F $.
	f8_ovmpt2s $f class V $.
	e0_ovmpt2s $e |- F = ( x e. C , y e. D |-> R ) $.
	p_ovmpt2s $p |- ( ( A e. C /\ B e. D /\ [_ A / x ]_ [_ B / y ]_ R e. V ) -> ( A F B ) = [_ A / x ]_ [_ B / y ]_ R ) $= f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb f8_ovmpt2s p_elex f0_ovmpt2s f2_ovmpt2s p_nfcv f1_ovmpt2s f2_ovmpt2s p_nfcv f1_ovmpt2s f3_ovmpt2s p_nfcv f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s p_nfcsb1v f0_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_cvv p_nfel1 f0_ovmpt2s f2_ovmpt2s p_nfcv e0_ovmpt2s f0_ovmpt2s f1_ovmpt2s f4_ovmpt2s f5_ovmpt2s f6_ovmpt2s p_nfmpt21 f0_ovmpt2s f7_ovmpt2s f0_ovmpt2s f1_ovmpt2s f4_ovmpt2s f5_ovmpt2s f6_ovmpt2s a_cmpt2 p_nfcxfr f0_ovmpt2s f1_ovmpt2s a_sup_set_class p_nfcv f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s p_nfov f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s p_nfcsb1v f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb p_nfeq f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_cvv a_wcel f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_wceq f0_ovmpt2s p_nfim f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb p_nfcsb1v f1_ovmpt2s f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv p_nfel1 f1_ovmpt2s f2_ovmpt2s p_nfcv e0_ovmpt2s f0_ovmpt2s f1_ovmpt2s f4_ovmpt2s f5_ovmpt2s f6_ovmpt2s p_nfmpt22 f1_ovmpt2s f7_ovmpt2s f0_ovmpt2s f1_ovmpt2s f4_ovmpt2s f5_ovmpt2s f6_ovmpt2s a_cmpt2 p_nfcxfr f1_ovmpt2s f3_ovmpt2s p_nfcv f1_ovmpt2s f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s p_nfov f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb p_nfcsb1v f1_ovmpt2s f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb p_nfeq f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv a_wcel f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_wceq f1_ovmpt2s p_nfim f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s p_csbeq1a f0_ovmpt2s a_sup_set_class f2_ovmpt2s a_wceq f6_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_cvv p_eleq1d f0_ovmpt2s a_sup_set_class f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s p_oveq1 f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s p_csbeq1a f0_ovmpt2s a_sup_set_class f2_ovmpt2s a_wceq f0_ovmpt2s a_sup_set_class f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f6_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb p_eqeq12d f0_ovmpt2s a_sup_set_class f2_ovmpt2s a_wceq f6_ovmpt2s a_cvv a_wcel f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_cvv a_wcel f0_ovmpt2s a_sup_set_class f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f6_ovmpt2s a_wceq f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_wceq p_imbi12d f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb p_csbeq1a f1_ovmpt2s a_sup_set_class f3_ovmpt2s a_wceq f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv p_eleq1d f1_ovmpt2s a_sup_set_class f3_ovmpt2s f2_ovmpt2s f7_ovmpt2s p_oveq2 f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb p_csbeq1a f1_ovmpt2s a_sup_set_class f3_ovmpt2s a_wceq f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb p_eqeq12d f1_ovmpt2s a_sup_set_class f3_ovmpt2s a_wceq f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_cvv a_wcel f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv a_wcel f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_wceq f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_wceq p_imbi12d e0_ovmpt2s f0_ovmpt2s f1_ovmpt2s f4_ovmpt2s f5_ovmpt2s f6_ovmpt2s f7_ovmpt2s a_cvv p_ovmpt4g f0_ovmpt2s a_sup_set_class f4_ovmpt2s a_wcel f1_ovmpt2s a_sup_set_class f5_ovmpt2s a_wcel f6_ovmpt2s a_cvv a_wcel f0_ovmpt2s a_sup_set_class f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f6_ovmpt2s a_wceq p_3expia f6_ovmpt2s a_cvv a_wcel f0_ovmpt2s a_sup_set_class f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f6_ovmpt2s a_wceq a_wi f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_cvv a_wcel f2_ovmpt2s f1_ovmpt2s a_sup_set_class f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_wceq a_wi f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv a_wcel f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_wceq a_wi f0_ovmpt2s f1_ovmpt2s f2_ovmpt2s f3_ovmpt2s f4_ovmpt2s f5_ovmpt2s p_vtocl2gaf f0_ovmpt2s f1_ovmpt2s f2_ovmpt2s f3_ovmpt2s f6_ovmpt2s f4_ovmpt2s f5_ovmpt2s p_csbcomg f2_ovmpt2s f4_ovmpt2s a_wcel f3_ovmpt2s f5_ovmpt2s a_wcel a_wa f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv p_eleq1d f0_ovmpt2s f1_ovmpt2s f2_ovmpt2s f3_ovmpt2s f6_ovmpt2s f4_ovmpt2s f5_ovmpt2s p_csbcomg f2_ovmpt2s f4_ovmpt2s a_wcel f3_ovmpt2s f5_ovmpt2s a_wcel a_wa f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co p_eqeq2d f2_ovmpt2s f4_ovmpt2s a_wcel f3_ovmpt2s f5_ovmpt2s a_wcel a_wa f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv a_wcel f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f1_ovmpt2s f3_ovmpt2s f0_ovmpt2s f2_ovmpt2s f6_ovmpt2s a_csb a_csb a_wceq f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv a_wcel f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb a_wceq p_3imtr4d f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb f8_ovmpt2s a_wcel f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb a_cvv a_wcel f2_ovmpt2s f4_ovmpt2s a_wcel f3_ovmpt2s f5_ovmpt2s a_wcel a_wa f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb a_wceq p_syl5 f2_ovmpt2s f4_ovmpt2s a_wcel f3_ovmpt2s f5_ovmpt2s a_wcel f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb f8_ovmpt2s a_wcel f2_ovmpt2s f3_ovmpt2s f7_ovmpt2s a_co f0_ovmpt2s f2_ovmpt2s f1_ovmpt2s f3_ovmpt2s f6_ovmpt2s a_csb a_csb a_wceq p_3impia $.
$}

$(The value of an operation class abstraction.  A version of ~ ovmpt2g
       using bound-variable hypotheses.  (Contributed by NM, 17-Aug-2006.)
       (Revised by Mario Carneiro, 19-Dec-2013.) $)

${
	$v x y A B C D R S F G H  $.
	$d A  $.
	$d B  $.
	$d x y C  $.
	$d R  $.
	$d x y D  $.
	$d F  $.
	$d G  $.
	$d S  $.
	f0_ov2gf $f set x $.
	f1_ov2gf $f set y $.
	f2_ov2gf $f class A $.
	f3_ov2gf $f class B $.
	f4_ov2gf $f class C $.
	f5_ov2gf $f class D $.
	f6_ov2gf $f class R $.
	f7_ov2gf $f class S $.
	f8_ov2gf $f class F $.
	f9_ov2gf $f class G $.
	f10_ov2gf $f class H $.
	e0_ov2gf $e |- F/_ x A $.
	e1_ov2gf $e |- F/_ y A $.
	e2_ov2gf $e |- F/_ y B $.
	e3_ov2gf $e |- F/_ x G $.
	e4_ov2gf $e |- F/_ y S $.
	e5_ov2gf $e |- ( x = A -> R = G ) $.
	e6_ov2gf $e |- ( y = B -> G = S ) $.
	e7_ov2gf $e |- F = ( x e. C , y e. D |-> R ) $.
	p_ov2gf $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $= f7_ov2gf f10_ov2gf p_elex e0_ov2gf e1_ov2gf e2_ov2gf e3_ov2gf f0_ov2gf f9_ov2gf a_cvv p_nfel1 e0_ov2gf e7_ov2gf f0_ov2gf f1_ov2gf f4_ov2gf f5_ov2gf f6_ov2gf p_nfmpt21 f0_ov2gf f8_ov2gf f0_ov2gf f1_ov2gf f4_ov2gf f5_ov2gf f6_ov2gf a_cmpt2 p_nfcxfr f0_ov2gf f1_ov2gf a_sup_set_class p_nfcv f0_ov2gf f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf p_nfov e3_ov2gf f0_ov2gf f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf a_co f9_ov2gf p_nfeq f9_ov2gf a_cvv a_wcel f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf a_co f9_ov2gf a_wceq f0_ov2gf p_nfim e4_ov2gf f1_ov2gf f7_ov2gf a_cvv p_nfel1 e1_ov2gf e7_ov2gf f0_ov2gf f1_ov2gf f4_ov2gf f5_ov2gf f6_ov2gf p_nfmpt22 f1_ov2gf f8_ov2gf f0_ov2gf f1_ov2gf f4_ov2gf f5_ov2gf f6_ov2gf a_cmpt2 p_nfcxfr e2_ov2gf f1_ov2gf f2_ov2gf f3_ov2gf f8_ov2gf p_nfov e4_ov2gf f1_ov2gf f2_ov2gf f3_ov2gf f8_ov2gf a_co f7_ov2gf p_nfeq f7_ov2gf a_cvv a_wcel f2_ov2gf f3_ov2gf f8_ov2gf a_co f7_ov2gf a_wceq f1_ov2gf p_nfim e5_ov2gf f0_ov2gf a_sup_set_class f2_ov2gf a_wceq f6_ov2gf f9_ov2gf a_cvv p_eleq1d f0_ov2gf a_sup_set_class f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf p_oveq1 e5_ov2gf f0_ov2gf a_sup_set_class f2_ov2gf a_wceq f0_ov2gf a_sup_set_class f1_ov2gf a_sup_set_class f8_ov2gf a_co f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf a_co f6_ov2gf f9_ov2gf p_eqeq12d f0_ov2gf a_sup_set_class f2_ov2gf a_wceq f6_ov2gf a_cvv a_wcel f9_ov2gf a_cvv a_wcel f0_ov2gf a_sup_set_class f1_ov2gf a_sup_set_class f8_ov2gf a_co f6_ov2gf a_wceq f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf a_co f9_ov2gf a_wceq p_imbi12d e6_ov2gf f1_ov2gf a_sup_set_class f3_ov2gf a_wceq f9_ov2gf f7_ov2gf a_cvv p_eleq1d f1_ov2gf a_sup_set_class f3_ov2gf f2_ov2gf f8_ov2gf p_oveq2 e6_ov2gf f1_ov2gf a_sup_set_class f3_ov2gf a_wceq f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf a_co f2_ov2gf f3_ov2gf f8_ov2gf a_co f9_ov2gf f7_ov2gf p_eqeq12d f1_ov2gf a_sup_set_class f3_ov2gf a_wceq f9_ov2gf a_cvv a_wcel f7_ov2gf a_cvv a_wcel f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf a_co f9_ov2gf a_wceq f2_ov2gf f3_ov2gf f8_ov2gf a_co f7_ov2gf a_wceq p_imbi12d e7_ov2gf f0_ov2gf f1_ov2gf f4_ov2gf f5_ov2gf f6_ov2gf f8_ov2gf a_cvv p_ovmpt4g f0_ov2gf a_sup_set_class f4_ov2gf a_wcel f1_ov2gf a_sup_set_class f5_ov2gf a_wcel f6_ov2gf a_cvv a_wcel f0_ov2gf a_sup_set_class f1_ov2gf a_sup_set_class f8_ov2gf a_co f6_ov2gf a_wceq p_3expia f6_ov2gf a_cvv a_wcel f0_ov2gf a_sup_set_class f1_ov2gf a_sup_set_class f8_ov2gf a_co f6_ov2gf a_wceq a_wi f9_ov2gf a_cvv a_wcel f2_ov2gf f1_ov2gf a_sup_set_class f8_ov2gf a_co f9_ov2gf a_wceq a_wi f7_ov2gf a_cvv a_wcel f2_ov2gf f3_ov2gf f8_ov2gf a_co f7_ov2gf a_wceq a_wi f0_ov2gf f1_ov2gf f2_ov2gf f3_ov2gf f4_ov2gf f5_ov2gf p_vtocl2gaf f7_ov2gf f10_ov2gf a_wcel f7_ov2gf a_cvv a_wcel f2_ov2gf f4_ov2gf a_wcel f3_ov2gf f5_ov2gf a_wcel a_wa f2_ov2gf f3_ov2gf f8_ov2gf a_co f7_ov2gf a_wceq p_syl5 f2_ov2gf f4_ov2gf a_wcel f3_ov2gf f5_ov2gf a_wcel f7_ov2gf f10_ov2gf a_wcel f2_ov2gf f3_ov2gf f8_ov2gf a_co f7_ov2gf a_wceq p_3impia $.
$}

$(Value of an operation given by a maps-to rule, deduction form.
         (Contributed by Mario Carneiro, 29-Dec-2014.) $)

${
	$v ph x y A B C D R S F L X  $.
	$d x y  $.
	$d x A  $.
	$d y B  $.
	$d C  $.
	$d D  $.
	$d R  $.
	$d S  $.
	f0_ovmpt2dxf $f wff ph $.
	f1_ovmpt2dxf $f set x $.
	f2_ovmpt2dxf $f set y $.
	f3_ovmpt2dxf $f class A $.
	f4_ovmpt2dxf $f class B $.
	f5_ovmpt2dxf $f class C $.
	f6_ovmpt2dxf $f class D $.
	f7_ovmpt2dxf $f class R $.
	f8_ovmpt2dxf $f class S $.
	f9_ovmpt2dxf $f class F $.
	f10_ovmpt2dxf $f class L $.
	f11_ovmpt2dxf $f class X $.
	e0_ovmpt2dxf $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
	e1_ovmpt2dxf $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
	e2_ovmpt2dxf $e |- ( ( ph /\ x = A ) -> D = L ) $.
	e3_ovmpt2dxf $e |- ( ph -> A e. C ) $.
	e4_ovmpt2dxf $e |- ( ph -> B e. L ) $.
	e5_ovmpt2dxf $e |- ( ph -> S e. X ) $.
	e6_ovmpt2dxf $e |- F/ x ph $.
	e7_ovmpt2dxf $e |- F/ y ph $.
	e8_ovmpt2dxf $e |- F/_ y A $.
	e9_ovmpt2dxf $e |- F/_ x B $.
	e10_ovmpt2dxf $e |- F/_ x S $.
	e11_ovmpt2dxf $e |- F/_ y S $.
	p_ovmpt2dxf $p |- ( ph -> ( A F B ) = S ) $= e0_ovmpt2dxf f0_ovmpt2dxf f9_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 f3_ovmpt2dxf f4_ovmpt2dxf p_oveqd e3_ovmpt2dxf e6_ovmpt2dxf e4_ovmpt2dxf e7_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 p_eqid f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_cvv p_ovmpt4g f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f0_ovmpt2dxf p_a1i f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf p_alrimi f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf f4_ovmpt2dxf f10_ovmpt2dxf p_spsbc f0_ovmpt2dxf f4_ovmpt2dxf f10_ovmpt2dxf a_wcel f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf a_wal f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf f4_ovmpt2dxf a_wsbc p_sylc f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf f4_ovmpt2dxf a_wsbc f1_ovmpt2dxf p_alrimi f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf f4_ovmpt2dxf a_wsbc f1_ovmpt2dxf f3_ovmpt2dxf f5_ovmpt2dxf p_spsbc f0_ovmpt2dxf f3_ovmpt2dxf f5_ovmpt2dxf a_wcel f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf f4_ovmpt2dxf a_wsbc f1_ovmpt2dxf a_wal f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf f4_ovmpt2dxf a_wsbc f1_ovmpt2dxf f3_ovmpt2dxf a_wsbc p_sylc e3_ovmpt2dxf e4_ovmpt2dxf f0_ovmpt2dxf f4_ovmpt2dxf f10_ovmpt2dxf a_wcel f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq p_adantr f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq p_simplr e3_ovmpt2dxf f0_ovmpt2dxf f3_ovmpt2dxf f5_ovmpt2dxf a_wcel f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq p_ad2antrr f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq a_wa f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf f5_ovmpt2dxf p_eqeltrd e4_ovmpt2dxf f0_ovmpt2dxf f4_ovmpt2dxf f10_ovmpt2dxf a_wcel f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq p_ad2antrr f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq p_simpr e2_ovmpt2dxf f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f6_ovmpt2dxf f10_ovmpt2dxf a_wceq f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq p_adantr f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf f6_ovmpt2dxf f10_ovmpt2dxf p_eleq12d f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f4_ovmpt2dxf f10_ovmpt2dxf a_wcel p_mpbird e1_ovmpt2dxf f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq f7_ovmpt2dxf f8_ovmpt2dxf a_wceq p_anassrs e5_ovmpt2dxf f8_ovmpt2dxf f11_ovmpt2dxf p_elex f0_ovmpt2dxf f8_ovmpt2dxf f11_ovmpt2dxf a_wcel f8_ovmpt2dxf a_cvv a_wcel p_syl f0_ovmpt2dxf f8_ovmpt2dxf a_cvv a_wcel f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq p_ad2antrr f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq a_wa f7_ovmpt2dxf f8_ovmpt2dxf a_cvv p_eqeltrd f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq p_biimt f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq a_wa f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi a_wb p_syl3anc f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq p_simplr f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq p_simpr f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq a_wa f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 p_oveq12d e1_ovmpt2dxf f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq f7_ovmpt2dxf f8_ovmpt2dxf a_wceq p_anassrs f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq a_wa f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf f8_ovmpt2dxf p_eqeq12d f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f2_ovmpt2dxf a_sup_set_class f4_ovmpt2dxf a_wceq a_wa f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf a_wceq p_bitr3d e7_ovmpt2dxf e8_ovmpt2dxf f2_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf p_nfeq2 f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq f2_ovmpt2dxf p_nfan e8_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf p_nfmpt22 f2_ovmpt2dxf f4_ovmpt2dxf p_nfcv f2_ovmpt2dxf f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 p_nfov e11_ovmpt2dxf f2_ovmpt2dxf f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf p_nfeq f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf a_wceq f2_ovmpt2dxf a_wnf f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa p_a1i f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f3_ovmpt2dxf a_wceq a_wa f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf a_wceq f2_ovmpt2dxf f4_ovmpt2dxf f10_ovmpt2dxf p_sbciedf e6_ovmpt2dxf f1_ovmpt2dxf f3_ovmpt2dxf p_nfcv f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf p_nfmpt21 e9_ovmpt2dxf f1_ovmpt2dxf f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 p_nfov e10_ovmpt2dxf f1_ovmpt2dxf f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf p_nfeq f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf a_wceq f1_ovmpt2dxf a_wnf f0_ovmpt2dxf p_a1i f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf f4_ovmpt2dxf a_wsbc f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf a_wceq f1_ovmpt2dxf f3_ovmpt2dxf f5_ovmpt2dxf p_sbciedf f0_ovmpt2dxf f1_ovmpt2dxf a_sup_set_class f5_ovmpt2dxf a_wcel f2_ovmpt2dxf a_sup_set_class f6_ovmpt2dxf a_wcel f7_ovmpt2dxf a_cvv a_wcel a_w3a f1_ovmpt2dxf a_sup_set_class f2_ovmpt2dxf a_sup_set_class f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f7_ovmpt2dxf a_wceq a_wi f2_ovmpt2dxf f4_ovmpt2dxf a_wsbc f1_ovmpt2dxf f3_ovmpt2dxf a_wsbc f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf a_wceq p_mpbid f0_ovmpt2dxf f3_ovmpt2dxf f4_ovmpt2dxf f9_ovmpt2dxf a_co f3_ovmpt2dxf f4_ovmpt2dxf f1_ovmpt2dxf f2_ovmpt2dxf f5_ovmpt2dxf f6_ovmpt2dxf f7_ovmpt2dxf a_cmpt2 a_co f8_ovmpt2dxf p_eqtrd $.
$}

$(Value of an operation given by a maps-to rule, deduction form.
       (Contributed by Mario Carneiro, 29-Dec-2014.) $)

${
	$v ph x y A B C D R S F L X  $.
	$d x y  $.
	$d x A  $.
	$d y B  $.
	$d C  $.
	$d D  $.
	$d R  $.
	$d S  $.
	$d y A  $.
	$d x B  $.
	$d x y S  $.
	$d x y ph  $.
	f0_ovmpt2dx $f wff ph $.
	f1_ovmpt2dx $f set x $.
	f2_ovmpt2dx $f set y $.
	f3_ovmpt2dx $f class A $.
	f4_ovmpt2dx $f class B $.
	f5_ovmpt2dx $f class C $.
	f6_ovmpt2dx $f class D $.
	f7_ovmpt2dx $f class R $.
	f8_ovmpt2dx $f class S $.
	f9_ovmpt2dx $f class F $.
	f10_ovmpt2dx $f class L $.
	f11_ovmpt2dx $f class X $.
	e0_ovmpt2dx $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
	e1_ovmpt2dx $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
	e2_ovmpt2dx $e |- ( ( ph /\ x = A ) -> D = L ) $.
	e3_ovmpt2dx $e |- ( ph -> A e. C ) $.
	e4_ovmpt2dx $e |- ( ph -> B e. L ) $.
	e5_ovmpt2dx $e |- ( ph -> S e. X ) $.
	p_ovmpt2dx $p |- ( ph -> ( A F B ) = S ) $= e0_ovmpt2dx e1_ovmpt2dx e2_ovmpt2dx e3_ovmpt2dx e4_ovmpt2dx e5_ovmpt2dx f0_ovmpt2dx f1_ovmpt2dx p_nfv f0_ovmpt2dx f2_ovmpt2dx p_nfv f2_ovmpt2dx f3_ovmpt2dx p_nfcv f1_ovmpt2dx f4_ovmpt2dx p_nfcv f1_ovmpt2dx f8_ovmpt2dx p_nfcv f2_ovmpt2dx f8_ovmpt2dx p_nfcv f0_ovmpt2dx f1_ovmpt2dx f2_ovmpt2dx f3_ovmpt2dx f4_ovmpt2dx f5_ovmpt2dx f6_ovmpt2dx f7_ovmpt2dx f8_ovmpt2dx f9_ovmpt2dx f10_ovmpt2dx f11_ovmpt2dx p_ovmpt2dxf $.
$}

$(Value of an operation given by a maps-to rule, deduction form.
       (Contributed by Mario Carneiro, 7-Dec-2014.) $)

${
	$v ph x y A B C D R S F X  $.
	$d x y A  $.
	$d x y B  $.
	$d x y S  $.
	$d x y ph  $.
	f0_ovmpt2d $f wff ph $.
	f1_ovmpt2d $f set x $.
	f2_ovmpt2d $f set y $.
	f3_ovmpt2d $f class A $.
	f4_ovmpt2d $f class B $.
	f5_ovmpt2d $f class C $.
	f6_ovmpt2d $f class D $.
	f7_ovmpt2d $f class R $.
	f8_ovmpt2d $f class S $.
	f9_ovmpt2d $f class F $.
	f10_ovmpt2d $f class X $.
	e0_ovmpt2d $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
	e1_ovmpt2d $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
	e2_ovmpt2d $e |- ( ph -> A e. C ) $.
	e3_ovmpt2d $e |- ( ph -> B e. D ) $.
	e4_ovmpt2d $e |- ( ph -> S e. X ) $.
	p_ovmpt2d $p |- ( ph -> ( A F B ) = S ) $= e0_ovmpt2d e1_ovmpt2d f0_ovmpt2d f1_ovmpt2d a_sup_set_class f3_ovmpt2d a_wceq a_wa f6_ovmpt2d p_eqidd e2_ovmpt2d e3_ovmpt2d e4_ovmpt2d f0_ovmpt2d f1_ovmpt2d f2_ovmpt2d f3_ovmpt2d f4_ovmpt2d f5_ovmpt2d f6_ovmpt2d f7_ovmpt2d f8_ovmpt2d f9_ovmpt2d f6_ovmpt2d f10_ovmpt2d p_ovmpt2dx $.
$}

$(The value of an operation class abstraction.  Variant of ~ ovmpt2ga
       which does not require ` D ` and ` x ` to be distinct.  (Contributed by
       Jeff Madsen, 10-Jun-2010.)  (Revised by Mario Carneiro, 20-Dec-2013.) $)

${
	$v x y A B C D R S F H L  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y L  $.
	$d x y S  $.
	f0_ovmpt2x $f set x $.
	f1_ovmpt2x $f set y $.
	f2_ovmpt2x $f class A $.
	f3_ovmpt2x $f class B $.
	f4_ovmpt2x $f class C $.
	f5_ovmpt2x $f class D $.
	f6_ovmpt2x $f class R $.
	f7_ovmpt2x $f class S $.
	f8_ovmpt2x $f class F $.
	f9_ovmpt2x $f class H $.
	f10_ovmpt2x $f class L $.
	e0_ovmpt2x $e |- ( ( x = A /\ y = B ) -> R = S ) $.
	e1_ovmpt2x $e |- ( x = A -> D = L ) $.
	e2_ovmpt2x $e |- F = ( x e. C , y e. D |-> R ) $.
	p_ovmpt2x $p |- ( ( A e. C /\ B e. L /\ S e. H ) -> ( A F B ) = S ) $= f7_ovmpt2x f9_ovmpt2x p_elex e2_ovmpt2x f8_ovmpt2x f0_ovmpt2x f1_ovmpt2x f4_ovmpt2x f5_ovmpt2x f6_ovmpt2x a_cmpt2 a_wceq f2_ovmpt2x f4_ovmpt2x a_wcel f3_ovmpt2x f10_ovmpt2x a_wcel f7_ovmpt2x a_cvv a_wcel a_w3a p_a1i e0_ovmpt2x f0_ovmpt2x a_sup_set_class f2_ovmpt2x a_wceq f1_ovmpt2x a_sup_set_class f3_ovmpt2x a_wceq a_wa f6_ovmpt2x f7_ovmpt2x a_wceq f2_ovmpt2x f4_ovmpt2x a_wcel f3_ovmpt2x f10_ovmpt2x a_wcel f7_ovmpt2x a_cvv a_wcel a_w3a p_adantl e1_ovmpt2x f0_ovmpt2x a_sup_set_class f2_ovmpt2x a_wceq f5_ovmpt2x f10_ovmpt2x a_wceq f2_ovmpt2x f4_ovmpt2x a_wcel f3_ovmpt2x f10_ovmpt2x a_wcel f7_ovmpt2x a_cvv a_wcel a_w3a p_adantl f2_ovmpt2x f4_ovmpt2x a_wcel f3_ovmpt2x f10_ovmpt2x a_wcel f7_ovmpt2x a_cvv a_wcel p_simp1 f2_ovmpt2x f4_ovmpt2x a_wcel f3_ovmpt2x f10_ovmpt2x a_wcel f7_ovmpt2x a_cvv a_wcel p_simp2 f2_ovmpt2x f4_ovmpt2x a_wcel f3_ovmpt2x f10_ovmpt2x a_wcel f7_ovmpt2x a_cvv a_wcel p_simp3 f2_ovmpt2x f4_ovmpt2x a_wcel f3_ovmpt2x f10_ovmpt2x a_wcel f7_ovmpt2x a_cvv a_wcel a_w3a f0_ovmpt2x f1_ovmpt2x f2_ovmpt2x f3_ovmpt2x f4_ovmpt2x f5_ovmpt2x f6_ovmpt2x f7_ovmpt2x f8_ovmpt2x f10_ovmpt2x a_cvv p_ovmpt2dx f7_ovmpt2x f9_ovmpt2x a_wcel f2_ovmpt2x f4_ovmpt2x a_wcel f3_ovmpt2x f10_ovmpt2x a_wcel f7_ovmpt2x a_cvv a_wcel f2_ovmpt2x f3_ovmpt2x f8_ovmpt2x a_co f7_ovmpt2x a_wceq p_syl3an3 $.
$}

$(Value of an operation given by a maps-to rule.  (Contributed by Mario
       Carneiro, 19-Dec-2013.) $)

${
	$v x y A B C D R S F H  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y D  $.
	$d x y S  $.
	f0_ovmpt2ga $f set x $.
	f1_ovmpt2ga $f set y $.
	f2_ovmpt2ga $f class A $.
	f3_ovmpt2ga $f class B $.
	f4_ovmpt2ga $f class C $.
	f5_ovmpt2ga $f class D $.
	f6_ovmpt2ga $f class R $.
	f7_ovmpt2ga $f class S $.
	f8_ovmpt2ga $f class F $.
	f9_ovmpt2ga $f class H $.
	e0_ovmpt2ga $e |- ( ( x = A /\ y = B ) -> R = S ) $.
	e1_ovmpt2ga $e |- F = ( x e. C , y e. D |-> R ) $.
	p_ovmpt2ga $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $= f7_ovmpt2ga f9_ovmpt2ga p_elex e1_ovmpt2ga f8_ovmpt2ga f0_ovmpt2ga f1_ovmpt2ga f4_ovmpt2ga f5_ovmpt2ga f6_ovmpt2ga a_cmpt2 a_wceq f2_ovmpt2ga f4_ovmpt2ga a_wcel f3_ovmpt2ga f5_ovmpt2ga a_wcel f7_ovmpt2ga a_cvv a_wcel a_w3a p_a1i e0_ovmpt2ga f0_ovmpt2ga a_sup_set_class f2_ovmpt2ga a_wceq f1_ovmpt2ga a_sup_set_class f3_ovmpt2ga a_wceq a_wa f6_ovmpt2ga f7_ovmpt2ga a_wceq f2_ovmpt2ga f4_ovmpt2ga a_wcel f3_ovmpt2ga f5_ovmpt2ga a_wcel f7_ovmpt2ga a_cvv a_wcel a_w3a p_adantl f2_ovmpt2ga f4_ovmpt2ga a_wcel f3_ovmpt2ga f5_ovmpt2ga a_wcel f7_ovmpt2ga a_cvv a_wcel p_simp1 f2_ovmpt2ga f4_ovmpt2ga a_wcel f3_ovmpt2ga f5_ovmpt2ga a_wcel f7_ovmpt2ga a_cvv a_wcel p_simp2 f2_ovmpt2ga f4_ovmpt2ga a_wcel f3_ovmpt2ga f5_ovmpt2ga a_wcel f7_ovmpt2ga a_cvv a_wcel p_simp3 f2_ovmpt2ga f4_ovmpt2ga a_wcel f3_ovmpt2ga f5_ovmpt2ga a_wcel f7_ovmpt2ga a_cvv a_wcel a_w3a f0_ovmpt2ga f1_ovmpt2ga f2_ovmpt2ga f3_ovmpt2ga f4_ovmpt2ga f5_ovmpt2ga f6_ovmpt2ga f7_ovmpt2ga f8_ovmpt2ga a_cvv p_ovmpt2d f7_ovmpt2ga f9_ovmpt2ga a_wcel f2_ovmpt2ga f4_ovmpt2ga a_wcel f3_ovmpt2ga f5_ovmpt2ga a_wcel f7_ovmpt2ga a_cvv a_wcel f2_ovmpt2ga f3_ovmpt2ga f8_ovmpt2ga a_co f7_ovmpt2ga a_wceq p_syl3an3 $.
$}

$(Value of an operation given by a maps-to rule.  (Contributed by NM,
       19-Dec-2013.) $)

${
	$v x y A B C D R S F  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y D  $.
	$d x y S  $.
	f0_ovmpt2a $f set x $.
	f1_ovmpt2a $f set y $.
	f2_ovmpt2a $f class A $.
	f3_ovmpt2a $f class B $.
	f4_ovmpt2a $f class C $.
	f5_ovmpt2a $f class D $.
	f6_ovmpt2a $f class R $.
	f7_ovmpt2a $f class S $.
	f8_ovmpt2a $f class F $.
	e0_ovmpt2a $e |- ( ( x = A /\ y = B ) -> R = S ) $.
	e1_ovmpt2a $e |- F = ( x e. C , y e. D |-> R ) $.
	e2_ovmpt2a $e |- S e. _V $.
	p_ovmpt2a $p |- ( ( A e. C /\ B e. D ) -> ( A F B ) = S ) $= e2_ovmpt2a e0_ovmpt2a e1_ovmpt2a f0_ovmpt2a f1_ovmpt2a f2_ovmpt2a f3_ovmpt2a f4_ovmpt2a f5_ovmpt2a f6_ovmpt2a f7_ovmpt2a f8_ovmpt2a a_cvv p_ovmpt2ga f2_ovmpt2a f4_ovmpt2a a_wcel f3_ovmpt2a f5_ovmpt2a a_wcel f7_ovmpt2a a_cvv a_wcel f2_ovmpt2a f3_ovmpt2a f8_ovmpt2a a_co f7_ovmpt2a a_wceq p_mp3an3 $.
$}

$(Alternate deduction version of ~ ovmpt2 , suitable for iteration.
         (Contributed by Mario Carneiro, 7-Jan-2017.) $)

${
	$v ph ps x y A B C D R F V  $.
	$d x y A  $.
	$d y B  $.
	$d x y ph  $.
	f0_ovmpt2df $f wff ph $.
	f1_ovmpt2df $f wff ps $.
	f2_ovmpt2df $f set x $.
	f3_ovmpt2df $f set y $.
	f4_ovmpt2df $f class A $.
	f5_ovmpt2df $f class B $.
	f6_ovmpt2df $f class C $.
	f7_ovmpt2df $f class D $.
	f8_ovmpt2df $f class R $.
	f9_ovmpt2df $f class F $.
	f10_ovmpt2df $f class V $.
	e0_ovmpt2df $e |- ( ph -> A e. C ) $.
	e1_ovmpt2df $e |- ( ( ph /\ x = A ) -> B e. D ) $.
	e2_ovmpt2df $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V ) $.
	e3_ovmpt2df $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ( A F B ) = R -> ps ) ) $.
	e4_ovmpt2df $e |- F/_ x F $.
	e5_ovmpt2df $e |- F/ x ps $.
	e6_ovmpt2df $e |- F/_ y F $.
	e7_ovmpt2df $e |- F/ y ps $.
	p_ovmpt2df $p |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ps ) ) $= e0_ovmpt2df f4_ovmpt2df f6_ovmpt2df p_elex f0_ovmpt2df f4_ovmpt2df f6_ovmpt2df a_wcel f4_ovmpt2df a_cvv a_wcel p_syl f2_ovmpt2df f4_ovmpt2df p_isset f0_ovmpt2df f4_ovmpt2df a_cvv a_wcel f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f2_ovmpt2df a_wex p_sylib f0_ovmpt2df f2_ovmpt2df p_nfv e4_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df p_nfmpt21 f2_ovmpt2df f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 p_nfeq e5_ovmpt2df f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f1_ovmpt2df f2_ovmpt2df p_nfim e1_ovmpt2df f5_ovmpt2df f7_ovmpt2df p_elex f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq a_wa f5_ovmpt2df f7_ovmpt2df a_wcel f5_ovmpt2df a_cvv a_wcel p_syl f3_ovmpt2df f5_ovmpt2df p_isset f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq a_wa f5_ovmpt2df a_cvv a_wcel f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq f3_ovmpt2df a_wex p_sylib f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq a_wa f3_ovmpt2df p_nfv e6_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df p_nfmpt22 f3_ovmpt2df f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 p_nfeq e7_ovmpt2df f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f1_ovmpt2df f3_ovmpt2df p_nfim f4_ovmpt2df f5_ovmpt2df f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 p_oveq f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq p_simprl f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq p_simprr f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa a_wa f2_ovmpt2df a_sup_set_class f4_ovmpt2df f3_ovmpt2df a_sup_set_class f5_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 p_oveq12d f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq p_simprl e0_ovmpt2df f0_ovmpt2df f4_ovmpt2df f6_ovmpt2df a_wcel f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa p_adantr f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa a_wa f2_ovmpt2df a_sup_set_class f4_ovmpt2df f6_ovmpt2df p_eqeltrd f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq p_simprr e1_ovmpt2df f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f5_ovmpt2df f7_ovmpt2df a_wcel f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq p_adantrr f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa a_wa f3_ovmpt2df a_sup_set_class f5_ovmpt2df f7_ovmpt2df p_eqeltrd e2_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 p_eqid f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 f10_ovmpt2df p_ovmpt4g f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa a_wa f2_ovmpt2df a_sup_set_class f6_ovmpt2df a_wcel f3_ovmpt2df a_sup_set_class f7_ovmpt2df a_wcel f8_ovmpt2df f10_ovmpt2df a_wcel f2_ovmpt2df a_sup_set_class f3_ovmpt2df a_sup_set_class f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_co f8_ovmpt2df a_wceq p_syl3anc f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa a_wa f2_ovmpt2df a_sup_set_class f3_ovmpt2df a_sup_set_class f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_co f4_ovmpt2df f5_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_co f8_ovmpt2df p_eqtr3d f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa a_wa f4_ovmpt2df f5_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_co f8_ovmpt2df f4_ovmpt2df f5_ovmpt2df f9_ovmpt2df a_co p_eqeq2d e3_ovmpt2df f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa a_wa f4_ovmpt2df f5_ovmpt2df f9_ovmpt2df a_co f4_ovmpt2df f5_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_co a_wceq f4_ovmpt2df f5_ovmpt2df f9_ovmpt2df a_co f8_ovmpt2df a_wceq f1_ovmpt2df p_sylbid f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f4_ovmpt2df f5_ovmpt2df f9_ovmpt2df a_co f4_ovmpt2df f5_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_co a_wceq f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq a_wa a_wa f1_ovmpt2df p_syl5 f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f1_ovmpt2df a_wi p_expr f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq a_wa f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f1_ovmpt2df a_wi f3_ovmpt2df p_exlimd f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq a_wa f3_ovmpt2df a_sup_set_class f5_ovmpt2df a_wceq f3_ovmpt2df a_wex f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f1_ovmpt2df a_wi p_mpd f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f1_ovmpt2df a_wi p_ex f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f1_ovmpt2df a_wi f2_ovmpt2df p_exlimd f0_ovmpt2df f2_ovmpt2df a_sup_set_class f4_ovmpt2df a_wceq f2_ovmpt2df a_wex f9_ovmpt2df f2_ovmpt2df f3_ovmpt2df f6_ovmpt2df f7_ovmpt2df f8_ovmpt2df a_cmpt2 a_wceq f1_ovmpt2df a_wi p_mpd $.
$}

$(Alternate deduction version of ~ ovmpt2 , suitable for iteration.
       (Contributed by Mario Carneiro, 7-Jan-2017.) $)

${
	$v ph ps x y A B C D R F V  $.
	$d x y A  $.
	$d y B  $.
	$d x y ph  $.
	$d x y F  $.
	$d x y ps  $.
	f0_ovmpt2dv $f wff ph $.
	f1_ovmpt2dv $f wff ps $.
	f2_ovmpt2dv $f set x $.
	f3_ovmpt2dv $f set y $.
	f4_ovmpt2dv $f class A $.
	f5_ovmpt2dv $f class B $.
	f6_ovmpt2dv $f class C $.
	f7_ovmpt2dv $f class D $.
	f8_ovmpt2dv $f class R $.
	f9_ovmpt2dv $f class F $.
	f10_ovmpt2dv $f class V $.
	e0_ovmpt2dv $e |- ( ph -> A e. C ) $.
	e1_ovmpt2dv $e |- ( ( ph /\ x = A ) -> B e. D ) $.
	e2_ovmpt2dv $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V ) $.
	e3_ovmpt2dv $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ( A F B ) = R -> ps ) ) $.
	p_ovmpt2dv $p |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ps ) ) $= e0_ovmpt2dv e1_ovmpt2dv e2_ovmpt2dv e3_ovmpt2dv f2_ovmpt2dv f9_ovmpt2dv p_nfcv f1_ovmpt2dv f2_ovmpt2dv p_nfv f3_ovmpt2dv f9_ovmpt2dv p_nfcv f1_ovmpt2dv f3_ovmpt2dv p_nfv f0_ovmpt2dv f1_ovmpt2dv f2_ovmpt2dv f3_ovmpt2dv f4_ovmpt2dv f5_ovmpt2dv f6_ovmpt2dv f7_ovmpt2dv f8_ovmpt2dv f9_ovmpt2dv f10_ovmpt2dv p_ovmpt2df $.
$}

$(Alternate deduction version of ~ ovmpt2 , suitable for iteration.
       (Contributed by Mario Carneiro, 7-Jan-2017.) $)

${
	$v ph x y A B C D R S F V  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ph  $.
	$d x y S  $.
	f0_ovmpt2dv2 $f wff ph $.
	f1_ovmpt2dv2 $f set x $.
	f2_ovmpt2dv2 $f set y $.
	f3_ovmpt2dv2 $f class A $.
	f4_ovmpt2dv2 $f class B $.
	f5_ovmpt2dv2 $f class C $.
	f6_ovmpt2dv2 $f class D $.
	f7_ovmpt2dv2 $f class R $.
	f8_ovmpt2dv2 $f class S $.
	f9_ovmpt2dv2 $f class F $.
	f10_ovmpt2dv2 $f class V $.
	e0_ovmpt2dv2 $e |- ( ph -> A e. C ) $.
	e1_ovmpt2dv2 $e |- ( ( ph /\ x = A ) -> B e. D ) $.
	e2_ovmpt2dv2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V ) $.
	e3_ovmpt2dv2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
	p_ovmpt2dv2 $p |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ( A F B ) = S ) ) $= f0_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 p_eqidd e0_ovmpt2dv2 e1_ovmpt2dv2 e2_ovmpt2dv2 e3_ovmpt2dv2 f0_ovmpt2dv2 f1_ovmpt2dv2 a_sup_set_class f3_ovmpt2dv2 a_wceq f2_ovmpt2dv2 a_sup_set_class f4_ovmpt2dv2 a_wceq a_wa a_wa f7_ovmpt2dv2 f8_ovmpt2dv2 f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co p_eqeq2d f0_ovmpt2dv2 f1_ovmpt2dv2 a_sup_set_class f3_ovmpt2dv2 a_wceq f2_ovmpt2dv2 a_sup_set_class f4_ovmpt2dv2 a_wceq a_wa a_wa f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co f7_ovmpt2dv2 a_wceq f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co f8_ovmpt2dv2 a_wceq p_biimpd f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 p_nfmpt21 f1_ovmpt2dv2 f3_ovmpt2dv2 p_nfcv f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 p_nfmpt21 f1_ovmpt2dv2 f4_ovmpt2dv2 p_nfcv f1_ovmpt2dv2 f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 p_nfov f1_ovmpt2dv2 f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co f8_ovmpt2dv2 p_nfeq1 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 p_nfmpt22 f2_ovmpt2dv2 f3_ovmpt2dv2 p_nfcv f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 p_nfmpt22 f2_ovmpt2dv2 f4_ovmpt2dv2 p_nfcv f2_ovmpt2dv2 f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 p_nfov f2_ovmpt2dv2 f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co f8_ovmpt2dv2 p_nfeq1 f0_ovmpt2dv2 f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co f8_ovmpt2dv2 a_wceq f1_ovmpt2dv2 f2_ovmpt2dv2 f3_ovmpt2dv2 f4_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 f10_ovmpt2dv2 p_ovmpt2df f0_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_wceq f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co f8_ovmpt2dv2 a_wceq p_mpd f3_ovmpt2dv2 f4_ovmpt2dv2 f9_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 p_oveq f9_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_wceq f3_ovmpt2dv2 f4_ovmpt2dv2 f9_ovmpt2dv2 a_co f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co f8_ovmpt2dv2 p_eqeq1d f0_ovmpt2dv2 f3_ovmpt2dv2 f4_ovmpt2dv2 f9_ovmpt2dv2 a_co f8_ovmpt2dv2 a_wceq f9_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_wceq f3_ovmpt2dv2 f4_ovmpt2dv2 f1_ovmpt2dv2 f2_ovmpt2dv2 f5_ovmpt2dv2 f6_ovmpt2dv2 f7_ovmpt2dv2 a_cmpt2 a_co f8_ovmpt2dv2 a_wceq p_syl5ibrcom $.
$}

$(Value of an operation given by a maps-to rule.  Special case.
       (Contributed by NM, 14-Sep-1999.)  (Revised by David Abernethy,
       19-Jun-2012.) $)

${
	$v x y A B C D R S F G H  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y D  $.
	$d x y S  $.
	f0_ovmpt2g $f set x $.
	f1_ovmpt2g $f set y $.
	f2_ovmpt2g $f class A $.
	f3_ovmpt2g $f class B $.
	f4_ovmpt2g $f class C $.
	f5_ovmpt2g $f class D $.
	f6_ovmpt2g $f class R $.
	f7_ovmpt2g $f class S $.
	f8_ovmpt2g $f class F $.
	f9_ovmpt2g $f class G $.
	f10_ovmpt2g $f class H $.
	e0_ovmpt2g $e |- ( x = A -> R = G ) $.
	e1_ovmpt2g $e |- ( y = B -> G = S ) $.
	e2_ovmpt2g $e |- F = ( x e. C , y e. D |-> R ) $.
	p_ovmpt2g $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $= e0_ovmpt2g e1_ovmpt2g f0_ovmpt2g a_sup_set_class f2_ovmpt2g a_wceq f1_ovmpt2g a_sup_set_class f3_ovmpt2g a_wceq f6_ovmpt2g f9_ovmpt2g f7_ovmpt2g p_sylan9eq e2_ovmpt2g f0_ovmpt2g f1_ovmpt2g f2_ovmpt2g f3_ovmpt2g f4_ovmpt2g f5_ovmpt2g f6_ovmpt2g f7_ovmpt2g f8_ovmpt2g f10_ovmpt2g p_ovmpt2ga $.
$}

$(Value of an operation given by a maps-to rule.  Special case.
       (Contributed by NM, 16-May-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) $)

${
	$v x y A B C D R S F G  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y D  $.
	$d x y S  $.
	f0_ovmpt2 $f set x $.
	f1_ovmpt2 $f set y $.
	f2_ovmpt2 $f class A $.
	f3_ovmpt2 $f class B $.
	f4_ovmpt2 $f class C $.
	f5_ovmpt2 $f class D $.
	f6_ovmpt2 $f class R $.
	f7_ovmpt2 $f class S $.
	f8_ovmpt2 $f class F $.
	f9_ovmpt2 $f class G $.
	e0_ovmpt2 $e |- ( x = A -> R = G ) $.
	e1_ovmpt2 $e |- ( y = B -> G = S ) $.
	e2_ovmpt2 $e |- F = ( x e. C , y e. D |-> R ) $.
	e3_ovmpt2 $e |- S e. _V $.
	p_ovmpt2 $p |- ( ( A e. C /\ B e. D ) -> ( A F B ) = S ) $= e3_ovmpt2 e0_ovmpt2 e1_ovmpt2 e2_ovmpt2 f0_ovmpt2 f1_ovmpt2 f2_ovmpt2 f3_ovmpt2 f4_ovmpt2 f5_ovmpt2 f6_ovmpt2 f7_ovmpt2 f8_ovmpt2 f9_ovmpt2 a_cvv p_ovmpt2g f2_ovmpt2 f4_ovmpt2 a_wcel f3_ovmpt2 f5_ovmpt2 a_wcel f7_ovmpt2 a_cvv a_wcel f2_ovmpt2 f3_ovmpt2 f8_ovmpt2 a_co f7_ovmpt2 a_wceq p_mp3an3 $.
$}

$(The value of an operation class abstraction.  Special case.
       (Contributed by NM, 28-May-1995.)  (Revised by Mario Carneiro,
       29-Dec-2014.) $)

${
	$v x y z w v u A B C D R S f F H  $.
	$d f u v w x y z A  $.
	$d f u v w x y z B  $.
	$d F  $.
	$d x y z R  $.
	$d f u v w y z C  $.
	$d f u v w y z D  $.
	$d f u v w x y z H  $.
	$d f u v w z S  $.
	f0_ov3 $f set x $.
	f1_ov3 $f set y $.
	f2_ov3 $f set z $.
	f3_ov3 $f set w $.
	f4_ov3 $f set v $.
	f5_ov3 $f set u $.
	f6_ov3 $f class A $.
	f7_ov3 $f class B $.
	f8_ov3 $f class C $.
	f9_ov3 $f class D $.
	f10_ov3 $f class R $.
	f11_ov3 $f class S $.
	f12_ov3 $f set f $.
	f13_ov3 $f class F $.
	f14_ov3 $f class H $.
	e0_ov3 $e |- S e. _V $.
	e1_ov3 $e |- ( ( ( w = A /\ v = B ) /\ ( u = C /\ f = D ) ) -> R = S ) $.
	e2_ov3 $e |- F = { <. <. x , y >. , z >. | ( ( x e. ( H X. H ) /\ y e. ( H X. H ) ) /\ E. w E. v E. u E. f ( ( x = <. w , v >. /\ y = <. u , f >. ) /\ z = R ) ) } $.
	p_ov3 $p |- ( ( ( A e. H /\ B e. H ) /\ ( C e. H /\ D e. H ) ) -> ( <. A , B >. F <. C , D >. ) = S ) $= e0_ov3 f2_ov3 f11_ov3 p_isseti f6_ov3 f14_ov3 a_wcel f7_ov3 f14_ov3 a_wcel a_wa f8_ov3 f14_ov3 a_wcel f9_ov3 f14_ov3 a_wcel a_wa a_wa f2_ov3 p_nfv f2_ov3 f6_ov3 f7_ov3 a_cop p_nfcv e2_ov3 f0_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel f1_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel a_wa f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex a_wa f0_ov3 f1_ov3 f2_ov3 p_nfoprab3 f2_ov3 f13_ov3 f0_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel f1_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel a_wa f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex a_wa f0_ov3 f1_ov3 f2_ov3 a_coprab p_nfcxfr f2_ov3 f8_ov3 f9_ov3 a_cop p_nfcv f2_ov3 f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 p_nfov f2_ov3 f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f11_ov3 p_nfeq1 e1_ov3 f3_ov3 a_sup_set_class f6_ov3 a_wceq f4_ov3 a_sup_set_class f7_ov3 a_wceq a_wa f5_ov3 a_sup_set_class f8_ov3 a_wceq f12_ov3 a_sup_set_class f9_ov3 a_wceq a_wa a_wa f10_ov3 f11_ov3 f2_ov3 a_sup_set_class p_eqeq2d f2_ov3 a_sup_set_class f10_ov3 a_wceq f2_ov3 a_sup_set_class f11_ov3 a_wceq f3_ov3 f4_ov3 f5_ov3 f12_ov3 f6_ov3 f7_ov3 f8_ov3 f9_ov3 f14_ov3 f14_ov3 p_copsex4g f6_ov3 f7_ov3 f14_ov3 f14_ov3 p_opelxpi f8_ov3 f9_ov3 f14_ov3 f14_ov3 p_opelxpi f0_ov3 f6_ov3 f7_ov3 a_cop p_nfcv f1_ov3 f6_ov3 f7_ov3 a_cop p_nfcv f1_ov3 f8_ov3 f9_ov3 a_cop p_nfcv f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f0_ov3 p_nfv f0_ov3 f6_ov3 f7_ov3 a_cop p_nfcv e2_ov3 f0_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel f1_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel a_wa f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex a_wa f0_ov3 f1_ov3 f2_ov3 p_nfoprab1 f0_ov3 f13_ov3 f0_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel f1_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel a_wa f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex a_wa f0_ov3 f1_ov3 f2_ov3 a_coprab p_nfcxfr f0_ov3 f1_ov3 a_sup_set_class p_nfcv f0_ov3 f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 p_nfov f0_ov3 f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 a_co f2_ov3 a_sup_set_class p_nfeq1 f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq f0_ov3 p_nfim f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f1_ov3 p_nfv f1_ov3 f6_ov3 f7_ov3 a_cop p_nfcv e2_ov3 f0_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel f1_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel a_wa f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex a_wa f0_ov3 f1_ov3 f2_ov3 p_nfoprab2 f1_ov3 f13_ov3 f0_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel f1_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel a_wa f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex a_wa f0_ov3 f1_ov3 f2_ov3 a_coprab p_nfcxfr f1_ov3 f8_ov3 f9_ov3 a_cop p_nfcv f1_ov3 f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 p_nfov f1_ov3 f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f2_ov3 a_sup_set_class p_nfeq1 f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq f1_ov3 p_nfim f0_ov3 a_sup_set_class f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop p_eqeq1 f0_ov3 a_sup_set_class f6_ov3 f7_ov3 a_cop a_wceq f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq p_anbi1d f0_ov3 a_sup_set_class f6_ov3 f7_ov3 a_cop a_wceq f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq p_anbi1d f0_ov3 a_sup_set_class f6_ov3 f7_ov3 a_cop a_wceq f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f3_ov3 f4_ov3 f5_ov3 f12_ov3 p_4exbidv f0_ov3 a_sup_set_class f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 p_oveq1 f0_ov3 a_sup_set_class f6_ov3 f7_ov3 a_cop a_wceq f0_ov3 a_sup_set_class f1_ov3 a_sup_set_class f13_ov3 a_co f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 a_co f2_ov3 a_sup_set_class p_eqeq1d f0_ov3 a_sup_set_class f6_ov3 f7_ov3 a_cop a_wceq f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f0_ov3 a_sup_set_class f1_ov3 a_sup_set_class f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq p_imbi12d f1_ov3 a_sup_set_class f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop p_eqeq1 f1_ov3 a_sup_set_class f8_ov3 f9_ov3 a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq p_anbi2d f1_ov3 a_sup_set_class f8_ov3 f9_ov3 a_cop a_wceq f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq p_anbi1d f1_ov3 a_sup_set_class f8_ov3 f9_ov3 a_cop a_wceq f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f3_ov3 f4_ov3 f5_ov3 f12_ov3 p_4exbidv f1_ov3 a_sup_set_class f8_ov3 f9_ov3 a_cop f6_ov3 f7_ov3 a_cop f13_ov3 p_oveq2 f1_ov3 a_sup_set_class f8_ov3 f9_ov3 a_cop a_wceq f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 a_co f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f2_ov3 a_sup_set_class p_eqeq1d f1_ov3 a_sup_set_class f8_ov3 f9_ov3 a_cop a_wceq f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq p_imbi12d f2_ov3 f10_ov3 p_moeq f2_ov3 a_sup_set_class f10_ov3 a_wceq f2_ov3 f5_ov3 f12_ov3 f1_ov3 a_sup_set_class p_mosubop f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f2_ov3 f3_ov3 f4_ov3 f0_ov3 a_sup_set_class p_mosubop f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq p_anass f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa a_wa f5_ov3 f12_ov3 p_2exbii f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f5_ov3 f12_ov3 p_19.42vv f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa a_wa f12_ov3 a_wex f5_ov3 a_wex f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex a_wa p_bitri f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex a_wa f3_ov3 f4_ov3 p_2exbii f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex a_wa f4_ov3 a_wex f3_ov3 a_wex f2_ov3 p_mobii f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f2_ov3 a_wmo f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex a_wa f4_ov3 a_wex f3_ov3 a_wex f2_ov3 a_wmo p_mpbir f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f2_ov3 a_wmo f0_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel f1_ov3 a_sup_set_class f14_ov3 f14_ov3 a_cxp a_wcel a_wa p_a1i e2_ov3 f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f0_ov3 f1_ov3 f2_ov3 f14_ov3 f14_ov3 a_cxp f14_ov3 f14_ov3 a_cxp f13_ov3 p_ovidi f0_ov3 a_sup_set_class f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f0_ov3 a_sup_set_class f1_ov3 a_sup_set_class f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq a_wi f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f1_ov3 a_sup_set_class f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f1_ov3 a_sup_set_class f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq a_wi f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq a_wi f0_ov3 f1_ov3 f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f14_ov3 f14_ov3 a_cxp f14_ov3 f14_ov3 a_cxp p_vtocl2gaf f6_ov3 f14_ov3 a_wcel f7_ov3 f14_ov3 a_wcel a_wa f6_ov3 f7_ov3 a_cop f14_ov3 f14_ov3 a_cxp a_wcel f8_ov3 f9_ov3 a_cop f14_ov3 f14_ov3 a_cxp a_wcel f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq a_wi f8_ov3 f14_ov3 a_wcel f9_ov3 f14_ov3 a_wcel a_wa p_syl2an f6_ov3 f14_ov3 a_wcel f7_ov3 f14_ov3 a_wcel a_wa f8_ov3 f14_ov3 a_wcel f9_ov3 f14_ov3 a_wcel a_wa a_wa f2_ov3 a_sup_set_class f11_ov3 a_wceq f6_ov3 f7_ov3 a_cop f3_ov3 a_sup_set_class f4_ov3 a_sup_set_class a_cop a_wceq f8_ov3 f9_ov3 a_cop f5_ov3 a_sup_set_class f12_ov3 a_sup_set_class a_cop a_wceq a_wa f2_ov3 a_sup_set_class f10_ov3 a_wceq a_wa f12_ov3 a_wex f5_ov3 a_wex f4_ov3 a_wex f3_ov3 a_wex f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq p_sylbird f2_ov3 a_sup_set_class f11_ov3 f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co p_eqeq2 f2_ov3 a_sup_set_class f11_ov3 a_wceq f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f2_ov3 a_sup_set_class a_wceq f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f11_ov3 a_wceq f6_ov3 f14_ov3 a_wcel f7_ov3 f14_ov3 a_wcel a_wa f8_ov3 f14_ov3 a_wcel f9_ov3 f14_ov3 a_wcel a_wa a_wa p_mpbidi f6_ov3 f14_ov3 a_wcel f7_ov3 f14_ov3 a_wcel a_wa f8_ov3 f14_ov3 a_wcel f9_ov3 f14_ov3 a_wcel a_wa a_wa f2_ov3 a_sup_set_class f11_ov3 a_wceq f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f11_ov3 a_wceq f2_ov3 p_exlimd f6_ov3 f14_ov3 a_wcel f7_ov3 f14_ov3 a_wcel a_wa f8_ov3 f14_ov3 a_wcel f9_ov3 f14_ov3 a_wcel a_wa a_wa f2_ov3 a_sup_set_class f11_ov3 a_wceq f2_ov3 a_wex f6_ov3 f7_ov3 a_cop f8_ov3 f9_ov3 a_cop f13_ov3 a_co f11_ov3 a_wceq p_mpi $.
$}

$(The value of an operation class abstraction.  Special case.
       (Contributed by NM, 13-Nov-2006.) $)

${
	$v x y z A B C R S F G H J  $.
	$d w x y z A  $.
	$d w x y z B  $.
	$d w x y z C  $.
	$d w z R  $.
	$d w x y z S  $.
	f0_ov6g $f set x $.
	f1_ov6g $f set y $.
	f2_ov6g $f set z $.
	f3_ov6g $f class A $.
	f4_ov6g $f class B $.
	f5_ov6g $f class C $.
	f6_ov6g $f class R $.
	f7_ov6g $f class S $.
	f8_ov6g $f class F $.
	f9_ov6g $f class G $.
	f10_ov6g $f class H $.
	f11_ov6g $f class J $.
	i0_ov6g $f set w $.
	e0_ov6g $e |- ( <. x , y >. = <. A , B >. -> R = S ) $.
	e1_ov6g $e |- F = { <. <. x , y >. , z >. | ( <. x , y >. e. C /\ z = R ) } $.
	p_ov6g $p |- ( ( ( A e. G /\ B e. H /\ <. A , B >. e. C ) /\ S e. J ) -> ( A F B ) = S ) $= f3_ov6g f4_ov6g f8_ov6g a_df-ov f7_ov6g p_eqid f0_ov6g a_sup_set_class f3_ov6g a_wceq f1_ov6g a_sup_set_class f4_ov6g a_wceq a_wa f7_ov6g f7_ov6g a_wceq p_biidd f7_ov6g f7_ov6g a_wceq f7_ov6g f7_ov6g a_wceq f0_ov6g f1_ov6g f3_ov6g f4_ov6g f9_ov6g f10_ov6g p_copsex2g f3_ov6g f9_ov6g a_wcel f4_ov6g f10_ov6g a_wcel a_wa f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f7_ov6g f7_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex f7_ov6g f7_ov6g a_wceq p_mpbiri f3_ov6g f9_ov6g a_wcel f4_ov6g f10_ov6g a_wcel f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f7_ov6g f7_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex f3_ov6g f4_ov6g a_cop f5_ov6g a_wcel p_3adant3 f3_ov6g f9_ov6g a_wcel f4_ov6g f10_ov6g a_wcel f3_ov6g f4_ov6g a_cop f5_ov6g a_wcel a_w3a f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f7_ov6g f7_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex f7_ov6g f11_ov6g a_wcel p_adantr i0_ov6g a_sup_set_class f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop p_eqeq1 i0_ov6g a_sup_set_class f3_ov6g f4_ov6g a_cop a_wceq i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq p_anbi1d e0_ov6g f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f3_ov6g f4_ov6g a_cop a_wceq f6_ov6g f7_ov6g f2_ov6g a_sup_set_class p_eqeq2d f2_ov6g a_sup_set_class f6_ov6g a_wceq f2_ov6g a_sup_set_class f7_ov6g a_wceq a_wb f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f3_ov6g f4_ov6g a_cop p_eqcoms f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq f2_ov6g a_sup_set_class f7_ov6g a_wceq p_pm5.32i i0_ov6g a_sup_set_class f3_ov6g f4_ov6g a_cop a_wceq i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f7_ov6g a_wceq a_wa p_syl6bb i0_ov6g a_sup_set_class f3_ov6g f4_ov6g a_cop a_wceq i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f7_ov6g a_wceq a_wa f0_ov6g f1_ov6g p_2exbidv f2_ov6g a_sup_set_class f7_ov6g f7_ov6g p_eqeq1 f2_ov6g a_sup_set_class f7_ov6g a_wceq f2_ov6g a_sup_set_class f7_ov6g a_wceq f7_ov6g f7_ov6g a_wceq f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq p_anbi2d f2_ov6g a_sup_set_class f7_ov6g a_wceq f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f7_ov6g a_wceq a_wa f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f7_ov6g f7_ov6g a_wceq a_wa f0_ov6g f1_ov6g p_2exbidv f2_ov6g f6_ov6g p_moeq f2_ov6g a_sup_set_class f6_ov6g a_wceq f2_ov6g f0_ov6g f1_ov6g i0_ov6g a_sup_set_class p_mosubop i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex f2_ov6g a_wmo i0_ov6g a_sup_set_class f5_ov6g a_wcel p_a1i e1_ov6g f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f0_ov6g f1_ov6g f2_ov6g i0_ov6g p_dfoprab2 i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g p_eleq1 i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq i0_ov6g a_sup_set_class f5_ov6g a_wcel f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq p_anbi1d i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq i0_ov6g a_sup_set_class f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa p_pm5.32i i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq i0_ov6g a_sup_set_class f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq p_an12 i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq i0_ov6g a_sup_set_class f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa i0_ov6g a_sup_set_class f5_ov6g a_wcel i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa p_bitr3i i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa i0_ov6g a_sup_set_class f5_ov6g a_wcel i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa f0_ov6g f1_ov6g p_2exbii i0_ov6g a_sup_set_class f5_ov6g a_wcel i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f0_ov6g f1_ov6g p_19.42vv i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa f1_ov6g a_wex f0_ov6g a_wex i0_ov6g a_sup_set_class f5_ov6g a_wcel i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa f1_ov6g a_wex f0_ov6g a_wex i0_ov6g a_sup_set_class f5_ov6g a_wcel i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex a_wa p_bitri i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa f1_ov6g a_wex f0_ov6g a_wex i0_ov6g a_sup_set_class f5_ov6g a_wcel i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex a_wa i0_ov6g f2_ov6g p_opabbii f8_ov6g f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f0_ov6g f1_ov6g f2_ov6g a_coprab i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop f5_ov6g a_wcel f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa a_wa f1_ov6g a_wex f0_ov6g a_wex i0_ov6g f2_ov6g a_copab i0_ov6g a_sup_set_class f5_ov6g a_wcel i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex a_wa i0_ov6g f2_ov6g a_copab p_3eqtri i0_ov6g a_sup_set_class f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f6_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f2_ov6g a_sup_set_class f7_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f7_ov6g f7_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex i0_ov6g f2_ov6g f3_ov6g f4_ov6g a_cop f7_ov6g f5_ov6g f11_ov6g f8_ov6g p_fvopab3ig f3_ov6g f4_ov6g a_cop f5_ov6g a_wcel f3_ov6g f9_ov6g a_wcel f7_ov6g f11_ov6g a_wcel f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f7_ov6g f7_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex f3_ov6g f4_ov6g a_cop f8_ov6g a_cfv f7_ov6g a_wceq a_wi f4_ov6g f10_ov6g a_wcel p_3ad2antl3 f3_ov6g f9_ov6g a_wcel f4_ov6g f10_ov6g a_wcel f3_ov6g f4_ov6g a_cop f5_ov6g a_wcel a_w3a f7_ov6g f11_ov6g a_wcel a_wa f3_ov6g f4_ov6g a_cop f0_ov6g a_sup_set_class f1_ov6g a_sup_set_class a_cop a_wceq f7_ov6g f7_ov6g a_wceq a_wa f1_ov6g a_wex f0_ov6g a_wex f3_ov6g f4_ov6g a_cop f8_ov6g a_cfv f7_ov6g a_wceq p_mpd f3_ov6g f9_ov6g a_wcel f4_ov6g f10_ov6g a_wcel f3_ov6g f4_ov6g a_cop f5_ov6g a_wcel a_w3a f7_ov6g f11_ov6g a_wcel a_wa f3_ov6g f4_ov6g f8_ov6g a_co f3_ov6g f4_ov6g a_cop f8_ov6g a_cfv f7_ov6g p_syl5eq $.
$}

$(The value of an operation class abstraction.  (Contributed by Jeff
       Madsen, 10-Jun-2010.) $)

${
	$v ph ps ch th ta x y z A B C D R S F  $.
	$d ph c  $.
	$d ps x  $.
	$d ch x y  $.
	$d th x y z  $.
	$d ta x y c  $.
	$d R x y z c  $.
	$d S x y z c  $.
	$d A x y z c  $.
	$d B x y z c  $.
	$d C x y z c  $.
	f0_ovg $f wff ph $.
	f1_ovg $f wff ps $.
	f2_ovg $f wff ch $.
	f3_ovg $f wff th $.
	f4_ovg $f wff ta $.
	f5_ovg $f set x $.
	f6_ovg $f set y $.
	f7_ovg $f set z $.
	f8_ovg $f class A $.
	f9_ovg $f class B $.
	f10_ovg $f class C $.
	f11_ovg $f class D $.
	f12_ovg $f class R $.
	f13_ovg $f class S $.
	f14_ovg $f class F $.
	i0_ovg $f set c $.
	e0_ovg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_ovg $e |- ( y = B -> ( ps <-> ch ) ) $.
	e2_ovg $e |- ( z = C -> ( ch <-> th ) ) $.
	e3_ovg $e |- ( ( ta /\ ( x e. R /\ y e. S ) ) -> E! z ph ) $.
	e4_ovg $e |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
	p_ovg $p |- ( ( ta /\ ( A e. R /\ B e. S /\ C e. D ) ) -> ( ( A F B ) = C <-> th ) ) $= f8_ovg f9_ovg f14_ovg a_df-ov e4_ovg f8_ovg f9_ovg a_cop f14_ovg f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab p_fveq1i f8_ovg f9_ovg f14_ovg a_co f8_ovg f9_ovg a_cop f14_ovg a_cfv f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv p_eqtri f8_ovg f9_ovg f14_ovg a_co f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg p_eqeq1i i0_ovg a_sup_set_class f10_ovg f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv p_eqeq2 i0_ovg a_sup_set_class f10_ovg f8_ovg f9_ovg a_cop p_opeq2 i0_ovg a_sup_set_class f10_ovg a_wceq f8_ovg f9_ovg a_cop i0_ovg a_sup_set_class a_cop f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab p_eleq1d i0_ovg a_sup_set_class f10_ovg a_wceq f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv i0_ovg a_sup_set_class a_wceq f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg a_wceq f8_ovg f9_ovg a_cop i0_ovg a_sup_set_class a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel p_bibi12d i0_ovg a_sup_set_class f10_ovg a_wceq f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv i0_ovg a_sup_set_class a_wceq f8_ovg f9_ovg a_cop i0_ovg a_sup_set_class a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel a_wb f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg a_wceq f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel a_wb f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa a_wa p_imbi2d e3_ovg f4_ovg f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg f7_ovg a_weu p_ex f4_ovg f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg f7_ovg a_weu a_wi f5_ovg f6_ovg p_alrimivv f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg f5_ovg f6_ovg f7_ovg p_fnoprabg f4_ovg f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg f7_ovg a_weu a_wi f6_ovg a_wal f5_ovg a_wal f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f5_ovg f6_ovg a_copab a_wfn p_syl f5_ovg a_sup_set_class f8_ovg f12_ovg p_eleq1 f5_ovg a_sup_set_class f8_ovg a_wceq f5_ovg a_sup_set_class f12_ovg a_wcel f8_ovg f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel p_anbi1d f6_ovg a_sup_set_class f9_ovg f13_ovg p_eleq1 f6_ovg a_sup_set_class f9_ovg a_wceq f6_ovg a_sup_set_class f13_ovg a_wcel f9_ovg f13_ovg a_wcel f8_ovg f12_ovg a_wcel p_anbi2d f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f8_ovg f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f5_ovg f6_ovg f8_ovg f9_ovg f12_ovg f13_ovg p_opelopabg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f5_ovg f6_ovg a_copab a_wcel p_ibir f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f5_ovg f6_ovg a_copab f8_ovg f9_ovg a_cop i0_ovg a_sup_set_class f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab p_fnopfvb f4_ovg f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f5_ovg f6_ovg a_copab a_wfn f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f5_ovg f6_ovg a_copab a_wcel f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv i0_ovg a_sup_set_class a_wceq f8_ovg f9_ovg a_cop i0_ovg a_sup_set_class a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel a_wb f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa p_syl2an f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa a_wa f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv i0_ovg a_sup_set_class a_wceq f8_ovg f9_ovg a_cop i0_ovg a_sup_set_class a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel a_wb a_wi f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa a_wa f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg a_wceq f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel a_wb a_wi i0_ovg f10_ovg f11_ovg p_vtoclg f10_ovg f11_ovg a_wcel f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa a_wa f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg a_wceq f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel a_wb p_com12 f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel f10_ovg f11_ovg a_wcel f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg a_wceq f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel a_wb a_wi p_exp32 f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel f10_ovg f11_ovg a_wcel f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg a_wceq f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel a_wb p_3imp2 f5_ovg a_sup_set_class f8_ovg f12_ovg p_eleq1 f5_ovg a_sup_set_class f8_ovg a_wceq f5_ovg a_sup_set_class f12_ovg a_wcel f8_ovg f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel p_anbi1d e0_ovg f5_ovg a_sup_set_class f8_ovg a_wceq f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f8_ovg f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg f1_ovg p_anbi12d f6_ovg a_sup_set_class f9_ovg f13_ovg p_eleq1 f6_ovg a_sup_set_class f9_ovg a_wceq f6_ovg a_sup_set_class f13_ovg a_wcel f9_ovg f13_ovg a_wcel f8_ovg f12_ovg a_wcel p_anbi2d e1_ovg f6_ovg a_sup_set_class f9_ovg a_wceq f8_ovg f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f1_ovg f2_ovg p_anbi12d e2_ovg f7_ovg a_sup_set_class f10_ovg a_wceq f2_ovg f3_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa p_anbi2d f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f8_ovg f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f1_ovg a_wa f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f2_ovg a_wa f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa f5_ovg f6_ovg f7_ovg f8_ovg f9_ovg f10_ovg f12_ovg f13_ovg f11_ovg p_eloprabg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel f10_ovg f11_ovg a_wcel a_w3a f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa a_wb f4_ovg p_adantl f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel f10_ovg f11_ovg a_wcel a_w3a a_wa f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg a_wceq f8_ovg f9_ovg a_cop f10_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_wcel f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa p_bitrd f8_ovg f9_ovg f14_ovg a_co f10_ovg a_wceq f8_ovg f9_ovg a_cop f5_ovg a_sup_set_class f12_ovg a_wcel f6_ovg a_sup_set_class f13_ovg a_wcel a_wa f0_ovg a_wa f5_ovg f6_ovg f7_ovg a_coprab a_cfv f10_ovg a_wceq f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel f10_ovg f11_ovg a_wcel a_w3a a_wa f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa p_syl5bb f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa p_biidd f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa f3_ovg p_bianabs f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa f3_ovg a_wb f10_ovg f11_ovg a_wcel p_3adant3 f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel f10_ovg f11_ovg a_wcel a_w3a f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa f3_ovg a_wb f4_ovg p_adantl f4_ovg f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel f10_ovg f11_ovg a_wcel a_w3a a_wa f8_ovg f9_ovg f14_ovg a_co f10_ovg a_wceq f8_ovg f12_ovg a_wcel f9_ovg f13_ovg a_wcel a_wa f3_ovg a_wa f3_ovg p_bitrd $.
$}

$(The value of a restricted operation.  (Contributed by FL, 10-Nov-2006.) $)

${
	$v A B C D F  $.
	f0_ovres $f class A $.
	f1_ovres $f class B $.
	f2_ovres $f class C $.
	f3_ovres $f class D $.
	f4_ovres $f class F $.
	p_ovres $p |- ( ( A e. C /\ B e. D ) -> ( A ( F |` ( C X. D ) ) B ) = ( A F B ) ) $= f0_ovres f1_ovres f2_ovres f3_ovres p_opelxpi f0_ovres f1_ovres a_cop f2_ovres f3_ovres a_cxp f4_ovres p_fvres f0_ovres f2_ovres a_wcel f1_ovres f3_ovres a_wcel a_wa f0_ovres f1_ovres a_cop f2_ovres f3_ovres a_cxp a_wcel f0_ovres f1_ovres a_cop f4_ovres f2_ovres f3_ovres a_cxp a_cres a_cfv f0_ovres f1_ovres a_cop f4_ovres a_cfv a_wceq p_syl f0_ovres f1_ovres f4_ovres f2_ovres f3_ovres a_cxp a_cres a_df-ov f0_ovres f1_ovres f4_ovres a_df-ov f0_ovres f2_ovres a_wcel f1_ovres f3_ovres a_wcel a_wa f0_ovres f1_ovres a_cop f4_ovres f2_ovres f3_ovres a_cxp a_cres a_cfv f0_ovres f1_ovres a_cop f4_ovres a_cfv f0_ovres f1_ovres f4_ovres f2_ovres f3_ovres a_cxp a_cres a_co f0_ovres f1_ovres f4_ovres a_co p_3eqtr4g $.
$}

$(Lemma for converting metric theorems to metric space theorems.
       (Contributed by Mario Carneiro, 2-Oct-2015.) $)

${
	$v ph A B D X  $.
	f0_ovresd $f wff ph $.
	f1_ovresd $f class A $.
	f2_ovresd $f class B $.
	f3_ovresd $f class D $.
	f4_ovresd $f class X $.
	e0_ovresd $e |- ( ph -> A e. X ) $.
	e1_ovresd $e |- ( ph -> B e. X ) $.
	p_ovresd $p |- ( ph -> ( A ( D |` ( X X. X ) ) B ) = ( A D B ) ) $= e0_ovresd e1_ovresd f1_ovresd f2_ovresd f4_ovresd f4_ovresd f3_ovresd p_ovres f0_ovresd f1_ovresd f4_ovresd a_wcel f2_ovresd f4_ovresd a_wcel f1_ovresd f2_ovresd f3_ovresd f4_ovresd f4_ovresd a_cxp a_cres a_co f1_ovresd f2_ovresd f3_ovresd a_co a_wceq p_syl2anc $.
$}

$(The value of a member of the domain of a subclass of an operation.
     (Contributed by NM, 23-Aug-2007.) $)

${
	$v A B C D F G  $.
	f0_oprssov $f class A $.
	f1_oprssov $f class B $.
	f2_oprssov $f class C $.
	f3_oprssov $f class D $.
	f4_oprssov $f class F $.
	f5_oprssov $f class G $.
	p_oprssov $p |- ( ( ( Fun F /\ G Fn ( C X. D ) /\ G C_ F ) /\ ( A e. C /\ B e. D ) ) -> ( A F B ) = ( A G B ) ) $= f0_oprssov f1_oprssov f2_oprssov f3_oprssov f4_oprssov p_ovres f0_oprssov f2_oprssov a_wcel f1_oprssov f3_oprssov a_wcel a_wa f0_oprssov f1_oprssov f4_oprssov f2_oprssov f3_oprssov a_cxp a_cres a_co f0_oprssov f1_oprssov f4_oprssov a_co a_wceq f4_oprssov a_wfun f5_oprssov f2_oprssov f3_oprssov a_cxp a_wfn f5_oprssov f4_oprssov a_wss a_w3a p_adantl f2_oprssov f3_oprssov a_cxp f5_oprssov p_fndm f5_oprssov f2_oprssov f3_oprssov a_cxp a_wfn f5_oprssov a_cdm f2_oprssov f3_oprssov a_cxp f4_oprssov p_reseq2d f5_oprssov f2_oprssov f3_oprssov a_cxp a_wfn f4_oprssov a_wfun f4_oprssov f5_oprssov a_cdm a_cres f4_oprssov f2_oprssov f3_oprssov a_cxp a_cres a_wceq f5_oprssov f4_oprssov a_wss p_3ad2ant2 f4_oprssov f5_oprssov p_funssres f4_oprssov a_wfun f5_oprssov f4_oprssov a_wss f4_oprssov f5_oprssov a_cdm a_cres f5_oprssov a_wceq f5_oprssov f2_oprssov f3_oprssov a_cxp a_wfn p_3adant2 f4_oprssov a_wfun f5_oprssov f2_oprssov f3_oprssov a_cxp a_wfn f5_oprssov f4_oprssov a_wss a_w3a f4_oprssov f5_oprssov a_cdm a_cres f4_oprssov f2_oprssov f3_oprssov a_cxp a_cres f5_oprssov p_eqtr3d f4_oprssov a_wfun f5_oprssov f2_oprssov f3_oprssov a_cxp a_wfn f5_oprssov f4_oprssov a_wss a_w3a f4_oprssov f2_oprssov f3_oprssov a_cxp a_cres f5_oprssov f0_oprssov f1_oprssov p_oveqd f4_oprssov a_wfun f5_oprssov f2_oprssov f3_oprssov a_cxp a_wfn f5_oprssov f4_oprssov a_wss a_w3a f0_oprssov f1_oprssov f4_oprssov f2_oprssov f3_oprssov a_cxp a_cres a_co f0_oprssov f1_oprssov f5_oprssov a_co a_wceq f0_oprssov f2_oprssov a_wcel f1_oprssov f3_oprssov a_wcel a_wa p_adantr f4_oprssov a_wfun f5_oprssov f2_oprssov f3_oprssov a_cxp a_wfn f5_oprssov f4_oprssov a_wss a_w3a f0_oprssov f2_oprssov a_wcel f1_oprssov f3_oprssov a_wcel a_wa a_wa f0_oprssov f1_oprssov f4_oprssov f2_oprssov f3_oprssov a_cxp a_cres a_co f0_oprssov f1_oprssov f4_oprssov a_co f0_oprssov f1_oprssov f5_oprssov a_co p_eqtr3d $.
$}

$(An operation's value belongs to its codomain.  (Contributed by NM,
     27-Aug-2006.) $)

${
	$v A B C R S F  $.
	f0_fovrn $f class A $.
	f1_fovrn $f class B $.
	f2_fovrn $f class C $.
	f3_fovrn $f class R $.
	f4_fovrn $f class S $.
	f5_fovrn $f class F $.
	p_fovrn $p |- ( ( F : ( R X. S ) --> C /\ A e. R /\ B e. S ) -> ( A F B ) e. C ) $= f0_fovrn f1_fovrn f3_fovrn f4_fovrn p_opelxpi f0_fovrn f1_fovrn f5_fovrn a_df-ov f3_fovrn f4_fovrn a_cxp f2_fovrn f0_fovrn f1_fovrn a_cop f5_fovrn p_ffvelrn f3_fovrn f4_fovrn a_cxp f2_fovrn f5_fovrn a_wf f0_fovrn f1_fovrn a_cop f3_fovrn f4_fovrn a_cxp a_wcel a_wa f0_fovrn f1_fovrn f5_fovrn a_co f0_fovrn f1_fovrn a_cop f5_fovrn a_cfv f2_fovrn p_syl5eqel f0_fovrn f3_fovrn a_wcel f1_fovrn f4_fovrn a_wcel a_wa f3_fovrn f4_fovrn a_cxp f2_fovrn f5_fovrn a_wf f0_fovrn f1_fovrn a_cop f3_fovrn f4_fovrn a_cxp a_wcel f0_fovrn f1_fovrn f5_fovrn a_co f2_fovrn a_wcel p_sylan2 f3_fovrn f4_fovrn a_cxp f2_fovrn f5_fovrn a_wf f0_fovrn f3_fovrn a_wcel f1_fovrn f4_fovrn a_wcel f0_fovrn f1_fovrn f5_fovrn a_co f2_fovrn a_wcel p_3impb $.
$}

$(An operation's value belongs to its codomain.  (Contributed by Mario
       Carneiro, 29-Dec-2016.) $)

${
	$v ph A B C R S F  $.
	f0_fovrnda $f wff ph $.
	f1_fovrnda $f class A $.
	f2_fovrnda $f class B $.
	f3_fovrnda $f class C $.
	f4_fovrnda $f class R $.
	f5_fovrnda $f class S $.
	f6_fovrnda $f class F $.
	e0_fovrnda $e |- ( ph -> F : ( R X. S ) --> C ) $.
	p_fovrnda $p |- ( ( ph /\ ( A e. R /\ B e. S ) ) -> ( A F B ) e. C ) $= e0_fovrnda f1_fovrnda f2_fovrnda f3_fovrnda f4_fovrnda f5_fovrnda f6_fovrnda p_fovrn f0_fovrnda f4_fovrnda f5_fovrnda a_cxp f3_fovrnda f6_fovrnda a_wf f1_fovrnda f4_fovrnda a_wcel f2_fovrnda f5_fovrnda a_wcel f1_fovrnda f2_fovrnda f6_fovrnda a_co f3_fovrnda a_wcel p_syl3an1 f0_fovrnda f1_fovrnda f4_fovrnda a_wcel f2_fovrnda f5_fovrnda a_wcel f1_fovrnda f2_fovrnda f6_fovrnda a_co f3_fovrnda a_wcel p_3expb $.
$}

$(An operation's value belongs to its codomain.  (Contributed by Mario
       Carneiro, 29-Dec-2016.) $)

${
	$v ph A B C R S F  $.
	f0_fovrnd $f wff ph $.
	f1_fovrnd $f class A $.
	f2_fovrnd $f class B $.
	f3_fovrnd $f class C $.
	f4_fovrnd $f class R $.
	f5_fovrnd $f class S $.
	f6_fovrnd $f class F $.
	e0_fovrnd $e |- ( ph -> F : ( R X. S ) --> C ) $.
	e1_fovrnd $e |- ( ph -> A e. R ) $.
	e2_fovrnd $e |- ( ph -> B e. S ) $.
	p_fovrnd $p |- ( ph -> ( A F B ) e. C ) $= e0_fovrnd e1_fovrnd e2_fovrnd f1_fovrnd f2_fovrnd f3_fovrnd f4_fovrnd f5_fovrnd f6_fovrnd p_fovrn f0_fovrnd f4_fovrnd f5_fovrnd a_cxp f3_fovrnd f6_fovrnd a_wf f1_fovrnd f4_fovrnd a_wcel f2_fovrnd f5_fovrnd a_wcel f1_fovrnd f2_fovrnd f6_fovrnd a_co f3_fovrnd a_wcel p_syl3anc $.
$}

$(The range of an operation expressed as a collection of the operation's
       values.  (Contributed by NM, 29-Oct-2006.) $)

${
	$v x y z A B F  $.
	$d w x y z A  $.
	$d w x y z B  $.
	$d w z  $.
	$d w x y z F  $.
	f0_fnrnov $f set x $.
	f1_fnrnov $f set y $.
	f2_fnrnov $f set z $.
	f3_fnrnov $f class A $.
	f4_fnrnov $f class B $.
	f5_fnrnov $f class F $.
	i0_fnrnov $f set w $.
	p_fnrnov $p |- ( F Fn ( A X. B ) -> ran F = { z | E. x e. A E. y e. B z = ( x F y ) } ) $= i0_fnrnov f2_fnrnov f3_fnrnov f4_fnrnov a_cxp f5_fnrnov p_fnrnfv i0_fnrnov a_sup_set_class f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class a_cop f5_fnrnov p_fveq2 f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class f5_fnrnov a_df-ov i0_fnrnov a_sup_set_class f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class a_cop a_wceq i0_fnrnov a_sup_set_class f5_fnrnov a_cfv f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class a_cop f5_fnrnov a_cfv f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class f5_fnrnov a_co p_syl6eqr i0_fnrnov a_sup_set_class f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class a_cop a_wceq i0_fnrnov a_sup_set_class f5_fnrnov a_cfv f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class f5_fnrnov a_co f2_fnrnov a_sup_set_class p_eqeq2d f2_fnrnov a_sup_set_class i0_fnrnov a_sup_set_class f5_fnrnov a_cfv a_wceq f2_fnrnov a_sup_set_class f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class f5_fnrnov a_co a_wceq i0_fnrnov f0_fnrnov f1_fnrnov f3_fnrnov f4_fnrnov p_rexxp f2_fnrnov a_sup_set_class i0_fnrnov a_sup_set_class f5_fnrnov a_cfv a_wceq i0_fnrnov f3_fnrnov f4_fnrnov a_cxp a_wrex f2_fnrnov a_sup_set_class f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class f5_fnrnov a_co a_wceq f1_fnrnov f4_fnrnov a_wrex f0_fnrnov f3_fnrnov a_wrex f2_fnrnov p_abbii f5_fnrnov f3_fnrnov f4_fnrnov a_cxp a_wfn f5_fnrnov a_crn f2_fnrnov a_sup_set_class i0_fnrnov a_sup_set_class f5_fnrnov a_cfv a_wceq i0_fnrnov f3_fnrnov f4_fnrnov a_cxp a_wrex f2_fnrnov a_cab f2_fnrnov a_sup_set_class f0_fnrnov a_sup_set_class f1_fnrnov a_sup_set_class f5_fnrnov a_co a_wceq f1_fnrnov f4_fnrnov a_wrex f0_fnrnov f3_fnrnov a_wrex f2_fnrnov a_cab p_syl6eq $.
$}

$(An onto mapping of an operation expressed in terms of operation values.
       (Contributed by NM, 29-Oct-2006.) $)

${
	$v x y z A B C F  $.
	$d w x y z A  $.
	$d w x y z B  $.
	$d w z C  $.
	$d w x y z F  $.
	f0_foov $f set x $.
	f1_foov $f set y $.
	f2_foov $f set z $.
	f3_foov $f class A $.
	f4_foov $f class B $.
	f5_foov $f class C $.
	f6_foov $f class F $.
	i0_foov $f set w $.
	p_foov $p |- ( F : ( A X. B ) -onto-> C <-> ( F : ( A X. B ) --> C /\ A. z e. C E. x e. A E. y e. B z = ( x F y ) ) ) $= i0_foov f2_foov f3_foov f4_foov a_cxp f5_foov f6_foov p_dffo3 i0_foov a_sup_set_class f0_foov a_sup_set_class f1_foov a_sup_set_class a_cop f6_foov p_fveq2 f0_foov a_sup_set_class f1_foov a_sup_set_class f6_foov a_df-ov i0_foov a_sup_set_class f0_foov a_sup_set_class f1_foov a_sup_set_class a_cop a_wceq i0_foov a_sup_set_class f6_foov a_cfv f0_foov a_sup_set_class f1_foov a_sup_set_class a_cop f6_foov a_cfv f0_foov a_sup_set_class f1_foov a_sup_set_class f6_foov a_co p_syl6eqr i0_foov a_sup_set_class f0_foov a_sup_set_class f1_foov a_sup_set_class a_cop a_wceq i0_foov a_sup_set_class f6_foov a_cfv f0_foov a_sup_set_class f1_foov a_sup_set_class f6_foov a_co f2_foov a_sup_set_class p_eqeq2d f2_foov a_sup_set_class i0_foov a_sup_set_class f6_foov a_cfv a_wceq f2_foov a_sup_set_class f0_foov a_sup_set_class f1_foov a_sup_set_class f6_foov a_co a_wceq i0_foov f0_foov f1_foov f3_foov f4_foov p_rexxp f2_foov a_sup_set_class i0_foov a_sup_set_class f6_foov a_cfv a_wceq i0_foov f3_foov f4_foov a_cxp a_wrex f2_foov a_sup_set_class f0_foov a_sup_set_class f1_foov a_sup_set_class f6_foov a_co a_wceq f1_foov f4_foov a_wrex f0_foov f3_foov a_wrex f2_foov f5_foov p_ralbii f2_foov a_sup_set_class i0_foov a_sup_set_class f6_foov a_cfv a_wceq i0_foov f3_foov f4_foov a_cxp a_wrex f2_foov f5_foov a_wral f2_foov a_sup_set_class f0_foov a_sup_set_class f1_foov a_sup_set_class f6_foov a_co a_wceq f1_foov f4_foov a_wrex f0_foov f3_foov a_wrex f2_foov f5_foov a_wral f3_foov f4_foov a_cxp f5_foov f6_foov a_wf p_anbi2i f3_foov f4_foov a_cxp f5_foov f6_foov a_wfo f3_foov f4_foov a_cxp f5_foov f6_foov a_wf f2_foov a_sup_set_class i0_foov a_sup_set_class f6_foov a_cfv a_wceq i0_foov f3_foov f4_foov a_cxp a_wrex f2_foov f5_foov a_wral a_wa f3_foov f4_foov a_cxp f5_foov f6_foov a_wf f2_foov a_sup_set_class f0_foov a_sup_set_class f1_foov a_sup_set_class f6_foov a_co a_wceq f1_foov f4_foov a_wrex f0_foov f3_foov a_wrex f2_foov f5_foov a_wral a_wa p_bitri $.
$}

$(An operation's value belongs to its range.  (Contributed by NM,
     10-Feb-2007.) $)

${
	$v A B C D F  $.
	f0_fnovrn $f class A $.
	f1_fnovrn $f class B $.
	f2_fnovrn $f class C $.
	f3_fnovrn $f class D $.
	f4_fnovrn $f class F $.
	p_fnovrn $p |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) -> ( C F D ) e. ran F ) $= f2_fnovrn f3_fnovrn f0_fnovrn f1_fnovrn p_opelxpi f2_fnovrn f3_fnovrn f4_fnovrn a_df-ov f0_fnovrn f1_fnovrn a_cxp f2_fnovrn f3_fnovrn a_cop f4_fnovrn p_fnfvelrn f4_fnovrn f0_fnovrn f1_fnovrn a_cxp a_wfn f2_fnovrn f3_fnovrn a_cop f0_fnovrn f1_fnovrn a_cxp a_wcel a_wa f2_fnovrn f3_fnovrn f4_fnovrn a_co f2_fnovrn f3_fnovrn a_cop f4_fnovrn a_cfv f4_fnovrn a_crn p_syl5eqel f2_fnovrn f0_fnovrn a_wcel f3_fnovrn f1_fnovrn a_wcel a_wa f4_fnovrn f0_fnovrn f1_fnovrn a_cxp a_wfn f2_fnovrn f3_fnovrn a_cop f0_fnovrn f1_fnovrn a_cxp a_wcel f2_fnovrn f3_fnovrn f4_fnovrn a_co f4_fnovrn a_crn a_wcel p_sylan2 f4_fnovrn f0_fnovrn f1_fnovrn a_cxp a_wfn f2_fnovrn f0_fnovrn a_wcel f3_fnovrn f1_fnovrn a_wcel f2_fnovrn f3_fnovrn f4_fnovrn a_co f4_fnovrn a_crn a_wcel p_3impb $.
$}

$(A member of an operation's range is a value of the operation.
       (Contributed by NM, 7-Feb-2007.)  (Revised by Mario Carneiro,
       30-Jan-2014.) $)

${
	$v x y A B C F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z F  $.
	f0_ovelrn $f set x $.
	f1_ovelrn $f set y $.
	f2_ovelrn $f class A $.
	f3_ovelrn $f class B $.
	f4_ovelrn $f class C $.
	f5_ovelrn $f class F $.
	i0_ovelrn $f set z $.
	p_ovelrn $p |- ( F Fn ( A X. B ) -> ( C e. ran F <-> E. x e. A E. y e. B C = ( x F y ) ) ) $= f0_ovelrn f1_ovelrn i0_ovelrn f2_ovelrn f3_ovelrn f5_ovelrn p_fnrnov f5_ovelrn f2_ovelrn f3_ovelrn a_cxp a_wfn f5_ovelrn a_crn i0_ovelrn a_sup_set_class f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f1_ovelrn f3_ovelrn a_wrex f0_ovelrn f2_ovelrn a_wrex i0_ovelrn a_cab f4_ovelrn p_eleq2d f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn p_ovex f4_ovelrn f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_cvv p_eleq1 f4_ovelrn f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f4_ovelrn a_cvv a_wcel f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_cvv a_wcel p_mpbiri f4_ovelrn f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f4_ovelrn a_cvv a_wcel f1_ovelrn f3_ovelrn p_rexlimivw f4_ovelrn f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f1_ovelrn f3_ovelrn a_wrex f4_ovelrn a_cvv a_wcel f0_ovelrn f2_ovelrn p_rexlimivw i0_ovelrn a_sup_set_class f4_ovelrn f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co p_eqeq1 i0_ovelrn a_sup_set_class f4_ovelrn a_wceq i0_ovelrn a_sup_set_class f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f4_ovelrn f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f0_ovelrn f1_ovelrn f2_ovelrn f3_ovelrn p_2rexbidv i0_ovelrn a_sup_set_class f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f1_ovelrn f3_ovelrn a_wrex f0_ovelrn f2_ovelrn a_wrex f4_ovelrn f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f1_ovelrn f3_ovelrn a_wrex f0_ovelrn f2_ovelrn a_wrex i0_ovelrn f4_ovelrn p_elab3 f5_ovelrn f2_ovelrn f3_ovelrn a_cxp a_wfn f4_ovelrn f5_ovelrn a_crn a_wcel f4_ovelrn i0_ovelrn a_sup_set_class f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f1_ovelrn f3_ovelrn a_wrex f0_ovelrn f2_ovelrn a_wrex i0_ovelrn a_cab a_wcel f4_ovelrn f0_ovelrn a_sup_set_class f1_ovelrn a_sup_set_class f5_ovelrn a_co a_wceq f1_ovelrn f3_ovelrn a_wrex f0_ovelrn f2_ovelrn a_wrex p_syl6bb $.
$}

$(Membership relation for the values of a function whose image is a
       subclass.  (Contributed by Mario Carneiro, 23-Dec-2013.) $)

${
	$v x y A B C F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z F  $.
	f0_funimassov $f set x $.
	f1_funimassov $f set y $.
	f2_funimassov $f class A $.
	f3_funimassov $f class B $.
	f4_funimassov $f class C $.
	f5_funimassov $f class F $.
	i0_funimassov $f set z $.
	p_funimassov $p |- ( ( Fun F /\ ( A X. B ) C_ dom F ) -> ( ( F " ( A X. B ) ) C_ C <-> A. x e. A A. y e. B ( x F y ) e. C ) ) $= i0_funimassov f2_funimassov f3_funimassov a_cxp f4_funimassov f5_funimassov p_funimass4 i0_funimassov a_sup_set_class f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class a_cop f5_funimassov p_fveq2 f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class f5_funimassov a_df-ov i0_funimassov a_sup_set_class f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class a_cop a_wceq i0_funimassov a_sup_set_class f5_funimassov a_cfv f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class a_cop f5_funimassov a_cfv f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class f5_funimassov a_co p_syl6eqr i0_funimassov a_sup_set_class f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class a_cop a_wceq i0_funimassov a_sup_set_class f5_funimassov a_cfv f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class f5_funimassov a_co f4_funimassov p_eleq1d i0_funimassov a_sup_set_class f5_funimassov a_cfv f4_funimassov a_wcel f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class f5_funimassov a_co f4_funimassov a_wcel i0_funimassov f0_funimassov f1_funimassov f2_funimassov f3_funimassov p_ralxp f5_funimassov a_wfun f2_funimassov f3_funimassov a_cxp f5_funimassov a_cdm a_wss a_wa f5_funimassov f2_funimassov f3_funimassov a_cxp a_cima f4_funimassov a_wss i0_funimassov a_sup_set_class f5_funimassov a_cfv f4_funimassov a_wcel i0_funimassov f2_funimassov f3_funimassov a_cxp a_wral f0_funimassov a_sup_set_class f1_funimassov a_sup_set_class f5_funimassov a_co f4_funimassov a_wcel f1_funimassov f3_funimassov a_wral f0_funimassov f2_funimassov a_wral p_syl6bb $.
$}

$(Operation value in an image.  (Contributed by Mario Carneiro,
       23-Dec-2013.)  (Revised by Mario Carneiro, 29-Jan-2014.) $)

${
	$v x y A B C D F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z F  $.
	f0_ovelimab $f set x $.
	f1_ovelimab $f set y $.
	f2_ovelimab $f class A $.
	f3_ovelimab $f class B $.
	f4_ovelimab $f class C $.
	f5_ovelimab $f class D $.
	f6_ovelimab $f class F $.
	i0_ovelimab $f set z $.
	p_ovelimab $p |- ( ( F Fn A /\ ( B X. C ) C_ A ) -> ( D e. ( F " ( B X. C ) ) <-> E. x e. B E. y e. C D = ( x F y ) ) ) $= i0_ovelimab f2_ovelimab f3_ovelimab f4_ovelimab a_cxp f5_ovelimab f6_ovelimab p_fvelimab i0_ovelimab a_sup_set_class f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class a_cop f6_ovelimab p_fveq2 f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class f6_ovelimab a_df-ov i0_ovelimab a_sup_set_class f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class a_cop a_wceq i0_ovelimab a_sup_set_class f6_ovelimab a_cfv f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class a_cop f6_ovelimab a_cfv f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class f6_ovelimab a_co p_syl6eqr i0_ovelimab a_sup_set_class f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class a_cop a_wceq i0_ovelimab a_sup_set_class f6_ovelimab a_cfv f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class f6_ovelimab a_co f5_ovelimab p_eqeq1d f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class f6_ovelimab a_co f5_ovelimab p_eqcom i0_ovelimab a_sup_set_class f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class a_cop a_wceq i0_ovelimab a_sup_set_class f6_ovelimab a_cfv f5_ovelimab a_wceq f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class f6_ovelimab a_co f5_ovelimab a_wceq f5_ovelimab f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class f6_ovelimab a_co a_wceq p_syl6bb i0_ovelimab a_sup_set_class f6_ovelimab a_cfv f5_ovelimab a_wceq f5_ovelimab f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class f6_ovelimab a_co a_wceq i0_ovelimab f0_ovelimab f1_ovelimab f3_ovelimab f4_ovelimab p_rexxp f6_ovelimab f2_ovelimab a_wfn f3_ovelimab f4_ovelimab a_cxp f2_ovelimab a_wss a_wa f5_ovelimab f6_ovelimab f3_ovelimab f4_ovelimab a_cxp a_cima a_wcel i0_ovelimab a_sup_set_class f6_ovelimab a_cfv f5_ovelimab a_wceq i0_ovelimab f3_ovelimab f4_ovelimab a_cxp a_wrex f5_ovelimab f0_ovelimab a_sup_set_class f1_ovelimab a_sup_set_class f6_ovelimab a_co a_wceq f1_ovelimab f4_ovelimab a_wrex f0_ovelimab f3_ovelimab a_wrex p_syl6bb $.
$}

$(The value of a constant operation.  (Contributed by NM, 5-Nov-2006.) $)

${
	$v A B C R S  $.
	f0_ovconst2 $f class A $.
	f1_ovconst2 $f class B $.
	f2_ovconst2 $f class C $.
	f3_ovconst2 $f class R $.
	f4_ovconst2 $f class S $.
	e0_ovconst2 $e |- C e. _V $.
	p_ovconst2 $p |- ( ( R e. A /\ S e. B ) -> ( R ( ( A X. B ) X. { C } ) S ) = C ) $= f3_ovconst2 f4_ovconst2 f0_ovconst2 f1_ovconst2 a_cxp f2_ovconst2 a_csn a_cxp a_df-ov f3_ovconst2 f4_ovconst2 f0_ovconst2 f1_ovconst2 p_opelxpi e0_ovconst2 f0_ovconst2 f1_ovconst2 a_cxp f2_ovconst2 f3_ovconst2 f4_ovconst2 a_cop p_fvconst2 f3_ovconst2 f0_ovconst2 a_wcel f4_ovconst2 f1_ovconst2 a_wcel a_wa f3_ovconst2 f4_ovconst2 a_cop f0_ovconst2 f1_ovconst2 a_cxp a_wcel f3_ovconst2 f4_ovconst2 a_cop f0_ovconst2 f1_ovconst2 a_cxp f2_ovconst2 a_csn a_cxp a_cfv f2_ovconst2 a_wceq p_syl f3_ovconst2 f0_ovconst2 a_wcel f4_ovconst2 f1_ovconst2 a_wcel a_wa f3_ovconst2 f4_ovconst2 f0_ovconst2 f1_ovconst2 a_cxp f2_ovconst2 a_csn a_cxp a_co f3_ovconst2 f4_ovconst2 a_cop f0_ovconst2 f1_ovconst2 a_cxp f2_ovconst2 a_csn a_cxp a_cfv f2_ovconst2 p_syl5eq $.
$}

$(Existence of a class abstraction of existentially restricted sets.
       Variables ` x ` and ` y ` are normally free-variable parameters in the
       class expression substituted for ` C ` , which can be thought of as
       ` C ( x , y ) ` .  See comments for ~ abrexex .  (Contributed by NM,
       20-Sep-2011.) $)

${
	$v x y z A B C  $.
	$d x z A  $.
	$d y z B  $.
	$d z C  $.
	f0_ab2rexex $f set x $.
	f1_ab2rexex $f set y $.
	f2_ab2rexex $f set z $.
	f3_ab2rexex $f class A $.
	f4_ab2rexex $f class B $.
	f5_ab2rexex $f class C $.
	e0_ab2rexex $e |- A e. _V $.
	e1_ab2rexex $e |- B e. _V $.
	p_ab2rexex $p |- { z | E. x e. A E. y e. B z = C } e. _V $= e0_ab2rexex e1_ab2rexex f1_ab2rexex f2_ab2rexex f4_ab2rexex f5_ab2rexex p_abrexex f2_ab2rexex a_sup_set_class f5_ab2rexex a_wceq f1_ab2rexex f4_ab2rexex a_wrex f0_ab2rexex f2_ab2rexex f3_ab2rexex p_abrexex2 $.
$}

$(Existence of an existentially restricted class abstraction. ` ph ` is
       normally has free-variable parameters ` x ` , ` y ` , and ` z ` .
       Compare ~ abrexex2 .  (Contributed by NM, 20-Sep-2011.) $)

${
	$v ph x y z A B  $.
	$d x z A  $.
	$d y z B  $.
	f0_ab2rexex2 $f wff ph $.
	f1_ab2rexex2 $f set x $.
	f2_ab2rexex2 $f set y $.
	f3_ab2rexex2 $f set z $.
	f4_ab2rexex2 $f class A $.
	f5_ab2rexex2 $f class B $.
	e0_ab2rexex2 $e |- A e. _V $.
	e1_ab2rexex2 $e |- B e. _V $.
	e2_ab2rexex2 $e |- { z | ph } e. _V $.
	p_ab2rexex2 $p |- { z | E. x e. A E. y e. B ph } e. _V $= e0_ab2rexex2 e1_ab2rexex2 e2_ab2rexex2 f0_ab2rexex2 f2_ab2rexex2 f3_ab2rexex2 f5_ab2rexex2 p_abrexex2 f0_ab2rexex2 f2_ab2rexex2 f5_ab2rexex2 a_wrex f1_ab2rexex2 f3_ab2rexex2 f4_ab2rexex2 p_abrexex2 $.
$}

$(Domain of closure of an operation.  (Contributed by NM, 24-Aug-1995.) $)

${
	$v x y S F  $.
	$d x y S  $.
	$d x y F  $.
	f0_oprssdm $f set x $.
	f1_oprssdm $f set y $.
	f2_oprssdm $f class S $.
	f3_oprssdm $f class F $.
	e0_oprssdm $e |- -. (/) e. S $.
	e1_oprssdm $e |- ( ( x e. S /\ y e. S ) -> ( x F y ) e. S ) $.
	p_oprssdm $p |- ( S X. S ) C_ dom F $= f2_oprssdm f2_oprssdm p_relxp f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class f2_oprssdm f2_oprssdm p_opelxp f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class f3_oprssdm a_df-ov e1_oprssdm f0_oprssdm a_sup_set_class f2_oprssdm a_wcel f1_oprssdm a_sup_set_class f2_oprssdm a_wcel a_wa f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cfv f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class f3_oprssdm a_co f2_oprssdm p_syl5eqelr e0_oprssdm f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm p_ndmfv f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cdm a_wcel a_wn f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cfv a_c0 f2_oprssdm p_eleq1d f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cdm a_wcel a_wn f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cfv f2_oprssdm a_wcel a_c0 f2_oprssdm a_wcel p_mtbiri f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cdm a_wcel f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cfv f2_oprssdm a_wcel p_con4i f0_oprssdm a_sup_set_class f2_oprssdm a_wcel f1_oprssdm a_sup_set_class f2_oprssdm a_wcel a_wa f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cfv f2_oprssdm a_wcel f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cdm a_wcel p_syl f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f2_oprssdm f2_oprssdm a_cxp a_wcel f0_oprssdm a_sup_set_class f2_oprssdm a_wcel f1_oprssdm a_sup_set_class f2_oprssdm a_wcel a_wa f0_oprssdm a_sup_set_class f1_oprssdm a_sup_set_class a_cop f3_oprssdm a_cdm a_wcel p_sylbi f0_oprssdm f1_oprssdm f2_oprssdm f2_oprssdm a_cxp f3_oprssdm a_cdm p_relssi $.
$}

$(The value of an operation outside its domain.  (Contributed by NM,
     28-Mar-2008.) $)

${
	$v A B R S F  $.
	f0_ndmovg $f class A $.
	f1_ndmovg $f class B $.
	f2_ndmovg $f class R $.
	f3_ndmovg $f class S $.
	f4_ndmovg $f class F $.
	p_ndmovg $p |- ( ( dom F = ( R X. S ) /\ -. ( A e. R /\ B e. S ) ) -> ( A F B ) = (/) ) $= f0_ndmovg f1_ndmovg f4_ndmovg a_df-ov f4_ndmovg a_cdm f2_ndmovg f3_ndmovg a_cxp f0_ndmovg f1_ndmovg a_cop p_eleq2 f0_ndmovg f1_ndmovg f2_ndmovg f3_ndmovg p_opelxp f4_ndmovg a_cdm f2_ndmovg f3_ndmovg a_cxp a_wceq f0_ndmovg f1_ndmovg a_cop f4_ndmovg a_cdm a_wcel f0_ndmovg f1_ndmovg a_cop f2_ndmovg f3_ndmovg a_cxp a_wcel f0_ndmovg f2_ndmovg a_wcel f1_ndmovg f3_ndmovg a_wcel a_wa p_syl6bb f4_ndmovg a_cdm f2_ndmovg f3_ndmovg a_cxp a_wceq f0_ndmovg f1_ndmovg a_cop f4_ndmovg a_cdm a_wcel f0_ndmovg f2_ndmovg a_wcel f1_ndmovg f3_ndmovg a_wcel a_wa p_notbid f0_ndmovg f1_ndmovg a_cop f4_ndmovg p_ndmfv f4_ndmovg a_cdm f2_ndmovg f3_ndmovg a_cxp a_wceq f0_ndmovg f2_ndmovg a_wcel f1_ndmovg f3_ndmovg a_wcel a_wa a_wn f0_ndmovg f1_ndmovg a_cop f4_ndmovg a_cdm a_wcel a_wn f0_ndmovg f1_ndmovg a_cop f4_ndmovg a_cfv a_c0 a_wceq p_syl6bir f4_ndmovg a_cdm f2_ndmovg f3_ndmovg a_cxp a_wceq f0_ndmovg f2_ndmovg a_wcel f1_ndmovg f3_ndmovg a_wcel a_wa a_wn f0_ndmovg f1_ndmovg a_cop f4_ndmovg a_cfv a_c0 a_wceq p_imp f4_ndmovg a_cdm f2_ndmovg f3_ndmovg a_cxp a_wceq f0_ndmovg f2_ndmovg a_wcel f1_ndmovg f3_ndmovg a_wcel a_wa a_wn a_wa f0_ndmovg f1_ndmovg f4_ndmovg a_co f0_ndmovg f1_ndmovg a_cop f4_ndmovg a_cfv a_c0 p_syl5eq $.
$}

$(The value of an operation outside its domain.  (Contributed by NM,
       24-Aug-1995.) $)

${
	$v A B S F  $.
	f0_ndmov $f class A $.
	f1_ndmov $f class B $.
	f2_ndmov $f class S $.
	f3_ndmov $f class F $.
	e0_ndmov $e |- dom F = ( S X. S ) $.
	p_ndmov $p |- ( -. ( A e. S /\ B e. S ) -> ( A F B ) = (/) ) $= e0_ndmov f0_ndmov f1_ndmov f2_ndmov f2_ndmov f3_ndmov p_ndmovg f3_ndmov a_cdm f2_ndmov f2_ndmov a_cxp a_wceq f0_ndmov f2_ndmov a_wcel f1_ndmov f2_ndmov a_wcel a_wa a_wn f0_ndmov f1_ndmov f3_ndmov a_co a_c0 a_wceq p_mpan $.
$}

$(The closure of an operation outside its domain, when the domain
         includes the empty set.  This technical lemma can make the operation
         more convenient to work in some cases.  It is dependent on our
         particular definitions of operation value, function value, and ordered
         pair.  (Contributed by NM, 24-Sep-2004.) $)

${
	$v A B S F  $.
	f0_ndmovcl $f class A $.
	f1_ndmovcl $f class B $.
	f2_ndmovcl $f class S $.
	f3_ndmovcl $f class F $.
	e0_ndmovcl $e |- dom F = ( S X. S ) $.
	e1_ndmovcl $e |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S ) $.
	e2_ndmovcl $e |- (/) e. S $.
	p_ndmovcl $p |- ( A F B ) e. S $= e1_ndmovcl e0_ndmovcl f0_ndmovcl f1_ndmovcl f2_ndmovcl f3_ndmovcl p_ndmov e2_ndmovcl f0_ndmovcl f2_ndmovcl a_wcel f1_ndmovcl f2_ndmovcl a_wcel a_wa a_wn f0_ndmovcl f1_ndmovcl f3_ndmovcl a_co a_c0 f2_ndmovcl p_syl6eqel f0_ndmovcl f2_ndmovcl a_wcel f1_ndmovcl f2_ndmovcl a_wcel a_wa f0_ndmovcl f1_ndmovcl f3_ndmovcl a_co f2_ndmovcl a_wcel p_pm2.61i $.
$}

$(Reverse closure law, when an operation's domain doesn't contain the
         empty set.  (Contributed by NM, 3-Feb-1996.) $)

${
	$v A B S F  $.
	f0_ndmovrcl $f class A $.
	f1_ndmovrcl $f class B $.
	f2_ndmovrcl $f class S $.
	f3_ndmovrcl $f class F $.
	e0_ndmovrcl $e |- dom F = ( S X. S ) $.
	e1_ndmovrcl $e |- -. (/) e. S $.
	p_ndmovrcl $p |- ( ( A F B ) e. S -> ( A e. S /\ B e. S ) ) $= e1_ndmovrcl e0_ndmovrcl f0_ndmovrcl f1_ndmovrcl f2_ndmovrcl f3_ndmovrcl p_ndmov f0_ndmovrcl f2_ndmovrcl a_wcel f1_ndmovrcl f2_ndmovrcl a_wcel a_wa a_wn f0_ndmovrcl f1_ndmovrcl f3_ndmovrcl a_co a_c0 f2_ndmovrcl p_eleq1d f0_ndmovrcl f2_ndmovrcl a_wcel f1_ndmovrcl f2_ndmovrcl a_wcel a_wa a_wn f0_ndmovrcl f1_ndmovrcl f3_ndmovrcl a_co f2_ndmovrcl a_wcel a_c0 f2_ndmovrcl a_wcel p_mtbiri f0_ndmovrcl f2_ndmovrcl a_wcel f1_ndmovrcl f2_ndmovrcl a_wcel a_wa f0_ndmovrcl f1_ndmovrcl f3_ndmovrcl a_co f2_ndmovrcl a_wcel p_con4i $.
$}

$(Any operation is commutative outside its domain.  (Contributed by NM,
       24-Aug-1995.) $)

${
	$v A B S F  $.
	f0_ndmovcom $f class A $.
	f1_ndmovcom $f class B $.
	f2_ndmovcom $f class S $.
	f3_ndmovcom $f class F $.
	e0_ndmovcom $e |- dom F = ( S X. S ) $.
	p_ndmovcom $p |- ( -. ( A e. S /\ B e. S ) -> ( A F B ) = ( B F A ) ) $= e0_ndmovcom f0_ndmovcom f1_ndmovcom f2_ndmovcom f3_ndmovcom p_ndmov f0_ndmovcom f2_ndmovcom a_wcel f1_ndmovcom f2_ndmovcom a_wcel p_ancom e0_ndmovcom f1_ndmovcom f0_ndmovcom f2_ndmovcom f3_ndmovcom p_ndmov f0_ndmovcom f2_ndmovcom a_wcel f1_ndmovcom f2_ndmovcom a_wcel a_wa f1_ndmovcom f2_ndmovcom a_wcel f0_ndmovcom f2_ndmovcom a_wcel a_wa f1_ndmovcom f0_ndmovcom f3_ndmovcom a_co a_c0 a_wceq p_sylnbi f0_ndmovcom f2_ndmovcom a_wcel f1_ndmovcom f2_ndmovcom a_wcel a_wa a_wn f0_ndmovcom f1_ndmovcom f3_ndmovcom a_co a_c0 f1_ndmovcom f0_ndmovcom f3_ndmovcom a_co p_eqtr4d $.
$}

$(Any operation is associative outside its domain, if the domain doesn't
         contain the empty set.  (Contributed by NM, 24-Aug-1995.) $)

${
	$v A B C S F  $.
	f0_ndmovass $f class A $.
	f1_ndmovass $f class B $.
	f2_ndmovass $f class C $.
	f3_ndmovass $f class S $.
	f4_ndmovass $f class F $.
	e0_ndmovass $e |- dom F = ( S X. S ) $.
	e1_ndmovass $e |- -. (/) e. S $.
	p_ndmovass $p |- ( -. ( A e. S /\ B e. S /\ C e. S ) -> ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $= e0_ndmovass e1_ndmovass f0_ndmovass f1_ndmovass f3_ndmovass f4_ndmovass p_ndmovrcl f0_ndmovass f1_ndmovass f4_ndmovass a_co f3_ndmovass a_wcel f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel a_wa f2_ndmovass f3_ndmovass a_wcel p_anim1i f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_df-3an f0_ndmovass f1_ndmovass f4_ndmovass a_co f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_wa f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel a_wa f2_ndmovass f3_ndmovass a_wcel a_wa f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_w3a p_sylibr f0_ndmovass f1_ndmovass f4_ndmovass a_co f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_wa f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_w3a p_con3i e0_ndmovass f0_ndmovass f1_ndmovass f4_ndmovass a_co f2_ndmovass f3_ndmovass f4_ndmovass p_ndmov f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_w3a a_wn f0_ndmovass f1_ndmovass f4_ndmovass a_co f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_wa a_wn f0_ndmovass f1_ndmovass f4_ndmovass a_co f2_ndmovass f4_ndmovass a_co a_c0 a_wceq p_syl e0_ndmovass e1_ndmovass f1_ndmovass f2_ndmovass f3_ndmovass f4_ndmovass p_ndmovrcl f1_ndmovass f2_ndmovass f4_ndmovass a_co f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_wa f0_ndmovass f3_ndmovass a_wcel p_anim2i f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel p_3anass f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f2_ndmovass f4_ndmovass a_co f3_ndmovass a_wcel a_wa f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_wa a_wa f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_w3a p_sylibr f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f2_ndmovass f4_ndmovass a_co f3_ndmovass a_wcel a_wa f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_w3a p_con3i e0_ndmovass f0_ndmovass f1_ndmovass f2_ndmovass f4_ndmovass a_co f3_ndmovass f4_ndmovass p_ndmov f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_w3a a_wn f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f2_ndmovass f4_ndmovass a_co f3_ndmovass a_wcel a_wa a_wn f0_ndmovass f1_ndmovass f2_ndmovass f4_ndmovass a_co f4_ndmovass a_co a_c0 a_wceq p_syl f0_ndmovass f3_ndmovass a_wcel f1_ndmovass f3_ndmovass a_wcel f2_ndmovass f3_ndmovass a_wcel a_w3a a_wn f0_ndmovass f1_ndmovass f4_ndmovass a_co f2_ndmovass f4_ndmovass a_co a_c0 f0_ndmovass f1_ndmovass f2_ndmovass f4_ndmovass a_co f4_ndmovass a_co p_eqtr4d $.
$}

$(Any operation is distributive outside its domain, if the domain
         doesn't contain the empty set.  (Contributed by NM, 24-Aug-1995.) $)

${
	$v A B C S F G  $.
	f0_ndmovdistr $f class A $.
	f1_ndmovdistr $f class B $.
	f2_ndmovdistr $f class C $.
	f3_ndmovdistr $f class S $.
	f4_ndmovdistr $f class F $.
	f5_ndmovdistr $f class G $.
	e0_ndmovdistr $e |- dom F = ( S X. S ) $.
	e1_ndmovdistr $e |- -. (/) e. S $.
	e2_ndmovdistr $e |- dom G = ( S X. S ) $.
	p_ndmovdistr $p |- ( -. ( A e. S /\ B e. S /\ C e. S ) -> ( A G ( B F C ) ) = ( ( A G B ) F ( A G C ) ) ) $= e0_ndmovdistr e1_ndmovdistr f1_ndmovdistr f2_ndmovdistr f3_ndmovdistr f4_ndmovdistr p_ndmovrcl f1_ndmovdistr f2_ndmovdistr f4_ndmovdistr a_co f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_wa f0_ndmovdistr f3_ndmovdistr a_wcel p_anim2i f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel p_3anass f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f2_ndmovdistr f4_ndmovdistr a_co f3_ndmovdistr a_wcel a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_wa a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_w3a p_sylibr f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f2_ndmovdistr f4_ndmovdistr a_co f3_ndmovdistr a_wcel a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_w3a p_con3i e2_ndmovdistr f0_ndmovdistr f1_ndmovdistr f2_ndmovdistr f4_ndmovdistr a_co f3_ndmovdistr f5_ndmovdistr p_ndmov f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_w3a a_wn f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f2_ndmovdistr f4_ndmovdistr a_co f3_ndmovdistr a_wcel a_wa a_wn f0_ndmovdistr f1_ndmovdistr f2_ndmovdistr f4_ndmovdistr a_co f5_ndmovdistr a_co a_c0 a_wceq p_syl e2_ndmovdistr e1_ndmovdistr f0_ndmovdistr f1_ndmovdistr f3_ndmovdistr f5_ndmovdistr p_ndmovrcl e2_ndmovdistr e1_ndmovdistr f0_ndmovdistr f2_ndmovdistr f3_ndmovdistr f5_ndmovdistr p_ndmovrcl f0_ndmovdistr f1_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr a_wcel f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel a_wa f0_ndmovdistr f2_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr a_wcel f0_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_wa p_anim12i f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel p_3anass f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel p_anandi f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_w3a f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_wa a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_wa a_wa p_bitri f0_ndmovdistr f1_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr a_wcel f0_ndmovdistr f2_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr a_wcel a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_wa a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_w3a p_sylibr f0_ndmovdistr f1_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr a_wcel f0_ndmovdistr f2_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr a_wcel a_wa f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_w3a p_con3i e0_ndmovdistr f0_ndmovdistr f1_ndmovdistr f5_ndmovdistr a_co f0_ndmovdistr f2_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr f4_ndmovdistr p_ndmov f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_w3a a_wn f0_ndmovdistr f1_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr a_wcel f0_ndmovdistr f2_ndmovdistr f5_ndmovdistr a_co f3_ndmovdistr a_wcel a_wa a_wn f0_ndmovdistr f1_ndmovdistr f5_ndmovdistr a_co f0_ndmovdistr f2_ndmovdistr f5_ndmovdistr a_co f4_ndmovdistr a_co a_c0 a_wceq p_syl f0_ndmovdistr f3_ndmovdistr a_wcel f1_ndmovdistr f3_ndmovdistr a_wcel f2_ndmovdistr f3_ndmovdistr a_wcel a_w3a a_wn f0_ndmovdistr f1_ndmovdistr f2_ndmovdistr f4_ndmovdistr a_co f5_ndmovdistr a_co a_c0 f0_ndmovdistr f1_ndmovdistr f5_ndmovdistr a_co f0_ndmovdistr f2_ndmovdistr f5_ndmovdistr a_co f4_ndmovdistr a_co p_eqtr4d $.
$}

$(Elimination of redundant antecedents in an ordering law.  (Contributed
       by NM, 7-Mar-1996.) $)

${
	$v A B C R S F  $.
	f0_ndmovord $f class A $.
	f1_ndmovord $f class B $.
	f2_ndmovord $f class C $.
	f3_ndmovord $f class R $.
	f4_ndmovord $f class S $.
	f5_ndmovord $f class F $.
	e0_ndmovord $e |- dom F = ( S X. S ) $.
	e1_ndmovord $e |- R C_ ( S X. S ) $.
	e2_ndmovord $e |- -. (/) e. S $.
	e3_ndmovord $e |- ( ( A e. S /\ B e. S /\ C e. S ) -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $.
	p_ndmovord $p |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $= e3_ndmovord f0_ndmovord f4_ndmovord a_wcel f1_ndmovord f4_ndmovord a_wcel f2_ndmovord f4_ndmovord a_wcel f0_ndmovord f1_ndmovord f3_ndmovord a_wbr f2_ndmovord f0_ndmovord f5_ndmovord a_co f2_ndmovord f1_ndmovord f5_ndmovord a_co f3_ndmovord a_wbr a_wb p_3expia e1_ndmovord f0_ndmovord f1_ndmovord f4_ndmovord f4_ndmovord f3_ndmovord p_brel e1_ndmovord f2_ndmovord f0_ndmovord f5_ndmovord a_co f2_ndmovord f1_ndmovord f5_ndmovord a_co f4_ndmovord f4_ndmovord f3_ndmovord p_brel e0_ndmovord e2_ndmovord f2_ndmovord f0_ndmovord f4_ndmovord f5_ndmovord p_ndmovrcl f2_ndmovord f0_ndmovord f5_ndmovord a_co f4_ndmovord a_wcel f2_ndmovord f4_ndmovord a_wcel f0_ndmovord f4_ndmovord a_wcel p_simprd e0_ndmovord e2_ndmovord f2_ndmovord f1_ndmovord f4_ndmovord f5_ndmovord p_ndmovrcl f2_ndmovord f1_ndmovord f5_ndmovord a_co f4_ndmovord a_wcel f2_ndmovord f4_ndmovord a_wcel f1_ndmovord f4_ndmovord a_wcel p_simprd f2_ndmovord f0_ndmovord f5_ndmovord a_co f4_ndmovord a_wcel f0_ndmovord f4_ndmovord a_wcel f2_ndmovord f1_ndmovord f5_ndmovord a_co f4_ndmovord a_wcel f1_ndmovord f4_ndmovord a_wcel p_anim12i f2_ndmovord f0_ndmovord f5_ndmovord a_co f2_ndmovord f1_ndmovord f5_ndmovord a_co f3_ndmovord a_wbr f2_ndmovord f0_ndmovord f5_ndmovord a_co f4_ndmovord a_wcel f2_ndmovord f1_ndmovord f5_ndmovord a_co f4_ndmovord a_wcel a_wa f0_ndmovord f4_ndmovord a_wcel f1_ndmovord f4_ndmovord a_wcel a_wa p_syl f0_ndmovord f1_ndmovord f3_ndmovord a_wbr f0_ndmovord f4_ndmovord a_wcel f1_ndmovord f4_ndmovord a_wcel a_wa f2_ndmovord f0_ndmovord f5_ndmovord a_co f2_ndmovord f1_ndmovord f5_ndmovord a_co f3_ndmovord a_wbr p_pm5.21ni f0_ndmovord f4_ndmovord a_wcel f1_ndmovord f4_ndmovord a_wcel a_wa a_wn f0_ndmovord f1_ndmovord f3_ndmovord a_wbr f2_ndmovord f0_ndmovord f5_ndmovord a_co f2_ndmovord f1_ndmovord f5_ndmovord a_co f3_ndmovord a_wbr a_wb f2_ndmovord f4_ndmovord a_wcel p_a1d f0_ndmovord f4_ndmovord a_wcel f1_ndmovord f4_ndmovord a_wcel a_wa f2_ndmovord f4_ndmovord a_wcel f0_ndmovord f1_ndmovord f3_ndmovord a_wbr f2_ndmovord f0_ndmovord f5_ndmovord a_co f2_ndmovord f1_ndmovord f5_ndmovord a_co f3_ndmovord a_wbr a_wb a_wi p_pm2.61i $.
$}

$(Elimination of redundant antecedent in an ordering law.  (Contributed by
       NM, 25-Jun-1998.) $)

${
	$v A B C R S F  $.
	f0_ndmovordi $f class A $.
	f1_ndmovordi $f class B $.
	f2_ndmovordi $f class C $.
	f3_ndmovordi $f class R $.
	f4_ndmovordi $f class S $.
	f5_ndmovordi $f class F $.
	e0_ndmovordi $e |- dom F = ( S X. S ) $.
	e1_ndmovordi $e |- R C_ ( S X. S ) $.
	e2_ndmovordi $e |- -. (/) e. S $.
	e3_ndmovordi $e |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $.
	p_ndmovordi $p |- ( ( C F A ) R ( C F B ) -> A R B ) $= e1_ndmovordi f2_ndmovordi f0_ndmovordi f5_ndmovordi a_co f2_ndmovordi f1_ndmovordi f5_ndmovordi a_co f4_ndmovordi f4_ndmovordi f3_ndmovordi p_brel f2_ndmovordi f0_ndmovordi f5_ndmovordi a_co f2_ndmovordi f1_ndmovordi f5_ndmovordi a_co f3_ndmovordi a_wbr f2_ndmovordi f0_ndmovordi f5_ndmovordi a_co f4_ndmovordi a_wcel f2_ndmovordi f1_ndmovordi f5_ndmovordi a_co f4_ndmovordi a_wcel p_simpld e0_ndmovordi e2_ndmovordi f2_ndmovordi f0_ndmovordi f4_ndmovordi f5_ndmovordi p_ndmovrcl f2_ndmovordi f0_ndmovordi f5_ndmovordi a_co f4_ndmovordi a_wcel f2_ndmovordi f4_ndmovordi a_wcel f0_ndmovordi f4_ndmovordi a_wcel p_simpld f2_ndmovordi f0_ndmovordi f5_ndmovordi a_co f2_ndmovordi f1_ndmovordi f5_ndmovordi a_co f3_ndmovordi a_wbr f2_ndmovordi f0_ndmovordi f5_ndmovordi a_co f4_ndmovordi a_wcel f2_ndmovordi f4_ndmovordi a_wcel p_syl e3_ndmovordi f2_ndmovordi f4_ndmovordi a_wcel f0_ndmovordi f1_ndmovordi f3_ndmovordi a_wbr f2_ndmovordi f0_ndmovordi f5_ndmovordi a_co f2_ndmovordi f1_ndmovordi f5_ndmovordi a_co f3_ndmovordi a_wbr p_biimprd f2_ndmovordi f4_ndmovordi a_wcel f2_ndmovordi f0_ndmovordi f5_ndmovordi a_co f2_ndmovordi f1_ndmovordi f5_ndmovordi a_co f3_ndmovordi a_wbr f0_ndmovordi f1_ndmovordi f3_ndmovordi a_wbr p_mpcom $.
$}

$(Convert an operation closure law to class notation.  (Contributed by
       Mario Carneiro, 26-May-2014.) $)

${
	$v ph x y A B C D E F  $.
	$d x y A  $.
	$d y B  $.
	$d x y C  $.
	$d x y D  $.
	$d x y E  $.
	$d x y ph  $.
	$d x y F  $.
	f0_caovclg $f wff ph $.
	f1_caovclg $f set x $.
	f2_caovclg $f set y $.
	f3_caovclg $f class A $.
	f4_caovclg $f class B $.
	f5_caovclg $f class C $.
	f6_caovclg $f class D $.
	f7_caovclg $f class E $.
	f8_caovclg $f class F $.
	e0_caovclg $e |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x F y ) e. E ) $.
	p_caovclg $p |- ( ( ph /\ ( A e. C /\ B e. D ) ) -> ( A F B ) e. E ) $= e0_caovclg f0_caovclg f1_caovclg a_sup_set_class f2_caovclg a_sup_set_class f8_caovclg a_co f7_caovclg a_wcel f1_caovclg f2_caovclg f5_caovclg f6_caovclg p_ralrimivva f1_caovclg a_sup_set_class f3_caovclg f2_caovclg a_sup_set_class f8_caovclg p_oveq1 f1_caovclg a_sup_set_class f3_caovclg a_wceq f1_caovclg a_sup_set_class f2_caovclg a_sup_set_class f8_caovclg a_co f3_caovclg f2_caovclg a_sup_set_class f8_caovclg a_co f7_caovclg p_eleq1d f2_caovclg a_sup_set_class f4_caovclg f3_caovclg f8_caovclg p_oveq2 f2_caovclg a_sup_set_class f4_caovclg a_wceq f3_caovclg f2_caovclg a_sup_set_class f8_caovclg a_co f3_caovclg f4_caovclg f8_caovclg a_co f7_caovclg p_eleq1d f1_caovclg a_sup_set_class f2_caovclg a_sup_set_class f8_caovclg a_co f7_caovclg a_wcel f3_caovclg f4_caovclg f8_caovclg a_co f7_caovclg a_wcel f3_caovclg f2_caovclg a_sup_set_class f8_caovclg a_co f7_caovclg a_wcel f1_caovclg f2_caovclg f3_caovclg f4_caovclg f5_caovclg f6_caovclg p_rspc2v f0_caovclg f1_caovclg a_sup_set_class f2_caovclg a_sup_set_class f8_caovclg a_co f7_caovclg a_wcel f2_caovclg f6_caovclg a_wral f1_caovclg f5_caovclg a_wral f3_caovclg f5_caovclg a_wcel f4_caovclg f6_caovclg a_wcel a_wa f3_caovclg f4_caovclg f8_caovclg a_co f7_caovclg a_wcel p_mpan9 $.
$}

$(Convert an operation closure law to class notation.  (Contributed by
       Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y A B C D E F  $.
	$d x y A  $.
	$d y B  $.
	$d x y C  $.
	$d x y D  $.
	$d x y E  $.
	$d x y ph  $.
	$d x y F  $.
	f0_caovcld $f wff ph $.
	f1_caovcld $f set x $.
	f2_caovcld $f set y $.
	f3_caovcld $f class A $.
	f4_caovcld $f class B $.
	f5_caovcld $f class C $.
	f6_caovcld $f class D $.
	f7_caovcld $f class E $.
	f8_caovcld $f class F $.
	e0_caovcld $e |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x F y ) e. E ) $.
	e1_caovcld $e |- ( ph -> A e. C ) $.
	e2_caovcld $e |- ( ph -> B e. D ) $.
	p_caovcld $p |- ( ph -> ( A F B ) e. E ) $= f0_caovcld p_id e1_caovcld e2_caovcld e0_caovcld f0_caovcld f1_caovcld f2_caovcld f3_caovcld f4_caovcld f5_caovcld f6_caovcld f7_caovcld f8_caovcld p_caovclg f0_caovcld f0_caovcld f3_caovcld f5_caovcld a_wcel f4_caovcld f6_caovcld a_wcel f3_caovcld f4_caovcld f8_caovcld a_co f7_caovcld a_wcel p_syl12anc $.
$}

$(Convert an operation closure law to class notation.  (Contributed by NM,
       4-Aug-1995.)  (Revised by Mario Carneiro, 26-May-2014.) $)

${
	$v x y A B S F  $.
	$d x y A  $.
	$d y B  $.
	$d x y F  $.
	$d x y  $.
	$d x y S  $.
	f0_caovcl $f set x $.
	f1_caovcl $f set y $.
	f2_caovcl $f class A $.
	f3_caovcl $f class B $.
	f4_caovcl $f class S $.
	f5_caovcl $f class F $.
	e0_caovcl $e |- ( ( x e. S /\ y e. S ) -> ( x F y ) e. S ) $.
	p_caovcl $p |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S ) $= p_tru e0_caovcl f0_caovcl a_sup_set_class f4_caovcl a_wcel f1_caovcl a_sup_set_class f4_caovcl a_wcel a_wa f0_caovcl a_sup_set_class f1_caovcl a_sup_set_class f5_caovcl a_co f4_caovcl a_wcel a_wtru p_adantl a_wtru f0_caovcl f1_caovcl f2_caovcl f3_caovcl f4_caovcl f4_caovcl f4_caovcl f5_caovcl p_caovclg a_wtru f2_caovcl f4_caovcl a_wcel f3_caovcl f4_caovcl a_wcel a_wa f2_caovcl f3_caovcl f5_caovcl a_co f4_caovcl a_wcel p_mpan $.
$}

$(General laws for commutative, associative, distributive operations. $)

$(Convert an operation commutative law to class notation.  (Contributed
         by Mario Carneiro, 1-Jun-2013.) $)

${
	$v ph x y A B S F  $.
	$d x y A  $.
	$d x y B  $.
	$d x y  $.
	$d x y  $.
	$d x y ph  $.
	$d x y F  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	$d x y S  $.
	$d x y  $.
	f0_caovcomg $f wff ph $.
	f1_caovcomg $f set x $.
	f2_caovcomg $f set y $.
	f3_caovcomg $f class A $.
	f4_caovcomg $f class B $.
	f5_caovcomg $f class S $.
	f6_caovcomg $f class F $.
	e0_caovcomg $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	p_caovcomg $p |- ( ( ph /\ ( A e. S /\ B e. S ) ) -> ( A F B ) = ( B F A ) ) $= e0_caovcomg f0_caovcomg f1_caovcomg a_sup_set_class f2_caovcomg a_sup_set_class f6_caovcomg a_co f2_caovcomg a_sup_set_class f1_caovcomg a_sup_set_class f6_caovcomg a_co a_wceq f1_caovcomg f2_caovcomg f5_caovcomg f5_caovcomg p_ralrimivva f1_caovcomg a_sup_set_class f3_caovcomg f2_caovcomg a_sup_set_class f6_caovcomg p_oveq1 f1_caovcomg a_sup_set_class f3_caovcomg f2_caovcomg a_sup_set_class f6_caovcomg p_oveq2 f1_caovcomg a_sup_set_class f3_caovcomg a_wceq f1_caovcomg a_sup_set_class f2_caovcomg a_sup_set_class f6_caovcomg a_co f3_caovcomg f2_caovcomg a_sup_set_class f6_caovcomg a_co f2_caovcomg a_sup_set_class f1_caovcomg a_sup_set_class f6_caovcomg a_co f2_caovcomg a_sup_set_class f3_caovcomg f6_caovcomg a_co p_eqeq12d f2_caovcomg a_sup_set_class f4_caovcomg f3_caovcomg f6_caovcomg p_oveq2 f2_caovcomg a_sup_set_class f4_caovcomg f3_caovcomg f6_caovcomg p_oveq1 f2_caovcomg a_sup_set_class f4_caovcomg a_wceq f3_caovcomg f2_caovcomg a_sup_set_class f6_caovcomg a_co f3_caovcomg f4_caovcomg f6_caovcomg a_co f2_caovcomg a_sup_set_class f3_caovcomg f6_caovcomg a_co f4_caovcomg f3_caovcomg f6_caovcomg a_co p_eqeq12d f1_caovcomg a_sup_set_class f2_caovcomg a_sup_set_class f6_caovcomg a_co f2_caovcomg a_sup_set_class f1_caovcomg a_sup_set_class f6_caovcomg a_co a_wceq f3_caovcomg f4_caovcomg f6_caovcomg a_co f4_caovcomg f3_caovcomg f6_caovcomg a_co a_wceq f3_caovcomg f2_caovcomg a_sup_set_class f6_caovcomg a_co f2_caovcomg a_sup_set_class f3_caovcomg f6_caovcomg a_co a_wceq f1_caovcomg f2_caovcomg f3_caovcomg f4_caovcomg f5_caovcomg f5_caovcomg p_rspc2v f0_caovcomg f1_caovcomg a_sup_set_class f2_caovcomg a_sup_set_class f6_caovcomg a_co f2_caovcomg a_sup_set_class f1_caovcomg a_sup_set_class f6_caovcomg a_co a_wceq f2_caovcomg f5_caovcomg a_wral f1_caovcomg f5_caovcomg a_wral f3_caovcomg f5_caovcomg a_wcel f4_caovcomg f5_caovcomg a_wcel a_wa f3_caovcomg f4_caovcomg f6_caovcomg a_co f4_caovcomg f3_caovcomg f6_caovcomg a_co a_wceq p_mpan9 $.
$}

$(Convert an operation commutative law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y A B S F  $.
	$d x y A  $.
	$d x y B  $.
	$d x y  $.
	$d x y  $.
	$d x y ph  $.
	$d x y F  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	$d x y S  $.
	$d x y  $.
	f0_caovcomd $f wff ph $.
	f1_caovcomd $f set x $.
	f2_caovcomd $f set y $.
	f3_caovcomd $f class A $.
	f4_caovcomd $f class B $.
	f5_caovcomd $f class S $.
	f6_caovcomd $f class F $.
	e0_caovcomd $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e1_caovcomd $e |- ( ph -> A e. S ) $.
	e2_caovcomd $e |- ( ph -> B e. S ) $.
	p_caovcomd $p |- ( ph -> ( A F B ) = ( B F A ) ) $= f0_caovcomd p_id e1_caovcomd e2_caovcomd e0_caovcomd f0_caovcomd f1_caovcomd f2_caovcomd f3_caovcomd f4_caovcomd f5_caovcomd f6_caovcomd p_caovcomg f0_caovcomd f0_caovcomd f3_caovcomd f5_caovcomd a_wcel f4_caovcomd f5_caovcomd a_wcel f3_caovcomd f4_caovcomd f6_caovcomd a_co f4_caovcomd f3_caovcomd f6_caovcomd a_co a_wceq p_syl12anc $.
$}

$(Convert an operation commutative law to class notation.  (Contributed
         by NM, 26-Aug-1995.)  (Revised by Mario Carneiro, 1-Jun-2013.) $)

${
	$v x y A B F  $.
	$d x y A  $.
	$d x y B  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	$d x y F  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	$d x y  $.
	f0_caovcom $f set x $.
	f1_caovcom $f set y $.
	f2_caovcom $f class A $.
	f3_caovcom $f class B $.
	f4_caovcom $f class F $.
	e0_caovcom $e |- A e. _V $.
	e1_caovcom $e |- B e. _V $.
	e2_caovcom $e |- ( x F y ) = ( y F x ) $.
	p_caovcom $p |- ( A F B ) = ( B F A ) $= e0_caovcom e0_caovcom e1_caovcom f2_caovcom a_cvv a_wcel f3_caovcom a_cvv a_wcel p_pm3.2i e2_caovcom f0_caovcom a_sup_set_class f1_caovcom a_sup_set_class f4_caovcom a_co f1_caovcom a_sup_set_class f0_caovcom a_sup_set_class f4_caovcom a_co a_wceq f2_caovcom a_cvv a_wcel f0_caovcom a_sup_set_class a_cvv a_wcel f1_caovcom a_sup_set_class a_cvv a_wcel a_wa a_wa p_a1i f2_caovcom a_cvv a_wcel f0_caovcom f1_caovcom f2_caovcom f3_caovcom a_cvv f4_caovcom p_caovcomg f2_caovcom a_cvv a_wcel f2_caovcom a_cvv a_wcel f3_caovcom a_cvv a_wcel a_wa f2_caovcom f3_caovcom f4_caovcom a_co f3_caovcom f2_caovcom f4_caovcom a_co a_wceq p_mp2an $.
$}

$(Convert an operation associative law to class notation.  (Contributed
         by Mario Carneiro, 1-Jun-2013.)  (Revised by Mario Carneiro,
         26-May-2014.) $)

${
	$v ph x y z A B C S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovassg $f wff ph $.
	f1_caovassg $f set x $.
	f2_caovassg $f set y $.
	f3_caovassg $f set z $.
	f4_caovassg $f class A $.
	f5_caovassg $f class B $.
	f6_caovassg $f class C $.
	f7_caovassg $f class S $.
	f8_caovassg $f class F $.
	e0_caovassg $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	p_caovassg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) -> ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $= e0_caovassg f0_caovassg f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co a_wceq f1_caovassg f2_caovassg f3_caovassg f7_caovassg f7_caovassg f7_caovassg p_ralrimivvva f1_caovassg a_sup_set_class f4_caovassg f2_caovassg a_sup_set_class f8_caovassg p_oveq1 f1_caovassg a_sup_set_class f4_caovassg a_wceq f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f2_caovassg a_sup_set_class f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg p_oveq1d f1_caovassg a_sup_set_class f4_caovassg f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg p_oveq1 f1_caovassg a_sup_set_class f4_caovassg a_wceq f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f2_caovassg a_sup_set_class f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co f4_caovassg f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co p_eqeq12d f2_caovassg a_sup_set_class f5_caovassg f4_caovassg f8_caovassg p_oveq2 f2_caovassg a_sup_set_class f5_caovassg a_wceq f4_caovassg f2_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f5_caovassg f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg p_oveq1d f2_caovassg a_sup_set_class f5_caovassg f3_caovassg a_sup_set_class f8_caovassg p_oveq1 f2_caovassg a_sup_set_class f5_caovassg a_wceq f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f5_caovassg f3_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f8_caovassg p_oveq2d f2_caovassg a_sup_set_class f5_caovassg a_wceq f4_caovassg f2_caovassg a_sup_set_class f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f5_caovassg f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co f4_caovassg f5_caovassg f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co p_eqeq12d f3_caovassg a_sup_set_class f6_caovassg f4_caovassg f5_caovassg f8_caovassg a_co f8_caovassg p_oveq2 f3_caovassg a_sup_set_class f6_caovassg f5_caovassg f8_caovassg p_oveq2 f3_caovassg a_sup_set_class f6_caovassg a_wceq f5_caovassg f3_caovassg a_sup_set_class f8_caovassg a_co f5_caovassg f6_caovassg f8_caovassg a_co f4_caovassg f8_caovassg p_oveq2d f3_caovassg a_sup_set_class f6_caovassg a_wceq f4_caovassg f5_caovassg f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f5_caovassg f8_caovassg a_co f6_caovassg f8_caovassg a_co f4_caovassg f5_caovassg f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co f4_caovassg f5_caovassg f6_caovassg f8_caovassg a_co f8_caovassg a_co p_eqeq12d f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co a_wceq f4_caovassg f5_caovassg f8_caovassg a_co f6_caovassg f8_caovassg a_co f4_caovassg f5_caovassg f6_caovassg f8_caovassg a_co f8_caovassg a_co a_wceq f4_caovassg f2_caovassg a_sup_set_class f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co a_wceq f4_caovassg f5_caovassg f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f4_caovassg f5_caovassg f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co a_wceq f1_caovassg f2_caovassg f3_caovassg f4_caovassg f5_caovassg f6_caovassg f7_caovassg f7_caovassg f7_caovassg p_rspc3v f0_caovassg f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f8_caovassg a_co f3_caovassg a_sup_set_class f8_caovassg a_co f1_caovassg a_sup_set_class f2_caovassg a_sup_set_class f3_caovassg a_sup_set_class f8_caovassg a_co f8_caovassg a_co a_wceq f3_caovassg f7_caovassg a_wral f2_caovassg f7_caovassg a_wral f1_caovassg f7_caovassg a_wral f4_caovassg f7_caovassg a_wcel f5_caovassg f7_caovassg a_wcel f6_caovassg f7_caovassg a_wcel a_w3a f4_caovassg f5_caovassg f8_caovassg a_co f6_caovassg f8_caovassg a_co f4_caovassg f5_caovassg f6_caovassg f8_caovassg a_co f8_caovassg a_co a_wceq p_mpan9 $.
$}

$(Convert an operation associative law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovassd $f wff ph $.
	f1_caovassd $f set x $.
	f2_caovassd $f set y $.
	f3_caovassd $f set z $.
	f4_caovassd $f class A $.
	f5_caovassd $f class B $.
	f6_caovassd $f class C $.
	f7_caovassd $f class S $.
	f8_caovassd $f class F $.
	e0_caovassd $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	e1_caovassd $e |- ( ph -> A e. S ) $.
	e2_caovassd $e |- ( ph -> B e. S ) $.
	e3_caovassd $e |- ( ph -> C e. S ) $.
	p_caovassd $p |- ( ph -> ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $= f0_caovassd p_id e1_caovassd e2_caovassd e3_caovassd e0_caovassd f0_caovassd f1_caovassd f2_caovassd f3_caovassd f4_caovassd f5_caovassd f6_caovassd f7_caovassd f8_caovassd p_caovassg f0_caovassd f0_caovassd f4_caovassd f7_caovassd a_wcel f5_caovassd f7_caovassd a_wcel f6_caovassd f7_caovassd a_wcel f4_caovassd f5_caovassd f8_caovassd a_co f6_caovassd f8_caovassd a_co f4_caovassd f5_caovassd f6_caovassd f8_caovassd a_co f8_caovassd a_co a_wceq p_syl13anc $.
$}

$(Convert an operation associative law to class notation.  (Contributed
         by NM, 26-Aug-1995.)  (Revised by Mario Carneiro, 26-May-2014.) $)

${
	$v x y z A B C F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caovass $f set x $.
	f1_caovass $f set y $.
	f2_caovass $f set z $.
	f3_caovass $f class A $.
	f4_caovass $f class B $.
	f5_caovass $f class C $.
	f6_caovass $f class F $.
	e0_caovass $e |- A e. _V $.
	e1_caovass $e |- B e. _V $.
	e2_caovass $e |- C e. _V $.
	e3_caovass $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	p_caovass $p |- ( ( A F B ) F C ) = ( A F ( B F C ) ) $= e0_caovass e1_caovass e2_caovass p_tru e3_caovass f0_caovass a_sup_set_class f1_caovass a_sup_set_class f6_caovass a_co f2_caovass a_sup_set_class f6_caovass a_co f0_caovass a_sup_set_class f1_caovass a_sup_set_class f2_caovass a_sup_set_class f6_caovass a_co f6_caovass a_co a_wceq a_wtru f0_caovass a_sup_set_class a_cvv a_wcel f1_caovass a_sup_set_class a_cvv a_wcel f2_caovass a_sup_set_class a_cvv a_wcel a_w3a a_wa p_a1i a_wtru f0_caovass f1_caovass f2_caovass f3_caovass f4_caovass f5_caovass a_cvv f6_caovass p_caovassg a_wtru f3_caovass a_cvv a_wcel f4_caovass a_cvv a_wcel f5_caovass a_cvv a_wcel a_w3a f3_caovass f4_caovass f6_caovass a_co f5_caovass f6_caovass a_co f3_caovass f4_caovass f5_caovass f6_caovass a_co f6_caovass a_co a_wceq p_mpan f3_caovass a_cvv a_wcel f4_caovass a_cvv a_wcel f5_caovass a_cvv a_wcel f3_caovass f4_caovass f6_caovass a_co f5_caovass f6_caovass a_co f3_caovass f4_caovass f5_caovass f6_caovass a_co f6_caovass a_co a_wceq p_mp3an $.
$}

$(Convert an operation cancellation law to class notation.  (Contributed
         by NM, 20-Aug-1995.)  (Revised by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C S T F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z T  $.
	f0_caovcang $f wff ph $.
	f1_caovcang $f set x $.
	f2_caovcang $f set y $.
	f3_caovcang $f set z $.
	f4_caovcang $f class A $.
	f5_caovcang $f class B $.
	f6_caovcang $f class C $.
	f7_caovcang $f class S $.
	f8_caovcang $f class T $.
	f9_caovcang $f class F $.
	e0_caovcang $e |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x F y ) = ( x F z ) <-> y = z ) ) $.
	p_caovcang $p |- ( ( ph /\ ( A e. T /\ B e. S /\ C e. S ) ) -> ( ( A F B ) = ( A F C ) <-> B = C ) ) $= e0_caovcang f0_caovcang f1_caovcang a_sup_set_class f2_caovcang a_sup_set_class f9_caovcang a_co f1_caovcang a_sup_set_class f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f2_caovcang a_sup_set_class f3_caovcang a_sup_set_class a_wceq a_wb f1_caovcang f2_caovcang f3_caovcang f8_caovcang f7_caovcang f7_caovcang p_ralrimivvva f1_caovcang a_sup_set_class f4_caovcang f2_caovcang a_sup_set_class f9_caovcang p_oveq1 f1_caovcang a_sup_set_class f4_caovcang f3_caovcang a_sup_set_class f9_caovcang p_oveq1 f1_caovcang a_sup_set_class f4_caovcang a_wceq f1_caovcang a_sup_set_class f2_caovcang a_sup_set_class f9_caovcang a_co f4_caovcang f2_caovcang a_sup_set_class f9_caovcang a_co f1_caovcang a_sup_set_class f3_caovcang a_sup_set_class f9_caovcang a_co f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co p_eqeq12d f1_caovcang a_sup_set_class f4_caovcang a_wceq f1_caovcang a_sup_set_class f2_caovcang a_sup_set_class f9_caovcang a_co f1_caovcang a_sup_set_class f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f4_caovcang f2_caovcang a_sup_set_class f9_caovcang a_co f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f2_caovcang a_sup_set_class f3_caovcang a_sup_set_class a_wceq p_bibi1d f2_caovcang a_sup_set_class f5_caovcang f4_caovcang f9_caovcang p_oveq2 f2_caovcang a_sup_set_class f5_caovcang a_wceq f4_caovcang f2_caovcang a_sup_set_class f9_caovcang a_co f4_caovcang f5_caovcang f9_caovcang a_co f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co p_eqeq1d f2_caovcang a_sup_set_class f5_caovcang f3_caovcang a_sup_set_class p_eqeq1 f2_caovcang a_sup_set_class f5_caovcang a_wceq f4_caovcang f2_caovcang a_sup_set_class f9_caovcang a_co f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f4_caovcang f5_caovcang f9_caovcang a_co f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f2_caovcang a_sup_set_class f3_caovcang a_sup_set_class a_wceq f5_caovcang f3_caovcang a_sup_set_class a_wceq p_bibi12d f3_caovcang a_sup_set_class f6_caovcang f4_caovcang f9_caovcang p_oveq2 f3_caovcang a_sup_set_class f6_caovcang a_wceq f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co f4_caovcang f6_caovcang f9_caovcang a_co f4_caovcang f5_caovcang f9_caovcang a_co p_eqeq2d f3_caovcang a_sup_set_class f6_caovcang f5_caovcang p_eqeq2 f3_caovcang a_sup_set_class f6_caovcang a_wceq f4_caovcang f5_caovcang f9_caovcang a_co f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f4_caovcang f5_caovcang f9_caovcang a_co f4_caovcang f6_caovcang f9_caovcang a_co a_wceq f5_caovcang f3_caovcang a_sup_set_class a_wceq f5_caovcang f6_caovcang a_wceq p_bibi12d f1_caovcang a_sup_set_class f2_caovcang a_sup_set_class f9_caovcang a_co f1_caovcang a_sup_set_class f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f2_caovcang a_sup_set_class f3_caovcang a_sup_set_class a_wceq a_wb f4_caovcang f5_caovcang f9_caovcang a_co f4_caovcang f6_caovcang f9_caovcang a_co a_wceq f5_caovcang f6_caovcang a_wceq a_wb f4_caovcang f2_caovcang a_sup_set_class f9_caovcang a_co f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f2_caovcang a_sup_set_class f3_caovcang a_sup_set_class a_wceq a_wb f4_caovcang f5_caovcang f9_caovcang a_co f4_caovcang f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f5_caovcang f3_caovcang a_sup_set_class a_wceq a_wb f1_caovcang f2_caovcang f3_caovcang f4_caovcang f5_caovcang f6_caovcang f8_caovcang f7_caovcang f7_caovcang p_rspc3v f0_caovcang f1_caovcang a_sup_set_class f2_caovcang a_sup_set_class f9_caovcang a_co f1_caovcang a_sup_set_class f3_caovcang a_sup_set_class f9_caovcang a_co a_wceq f2_caovcang a_sup_set_class f3_caovcang a_sup_set_class a_wceq a_wb f3_caovcang f7_caovcang a_wral f2_caovcang f7_caovcang a_wral f1_caovcang f8_caovcang a_wral f4_caovcang f8_caovcang a_wcel f5_caovcang f7_caovcang a_wcel f6_caovcang f7_caovcang a_wcel a_w3a f4_caovcang f5_caovcang f9_caovcang a_co f4_caovcang f6_caovcang f9_caovcang a_co a_wceq f5_caovcang f6_caovcang a_wceq a_wb p_mpan9 $.
$}

$(Convert an operation cancellation law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C S T F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z T  $.
	f0_caovcand $f wff ph $.
	f1_caovcand $f set x $.
	f2_caovcand $f set y $.
	f3_caovcand $f set z $.
	f4_caovcand $f class A $.
	f5_caovcand $f class B $.
	f6_caovcand $f class C $.
	f7_caovcand $f class S $.
	f8_caovcand $f class T $.
	f9_caovcand $f class F $.
	e0_caovcand $e |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x F y ) = ( x F z ) <-> y = z ) ) $.
	e1_caovcand $e |- ( ph -> A e. T ) $.
	e2_caovcand $e |- ( ph -> B e. S ) $.
	e3_caovcand $e |- ( ph -> C e. S ) $.
	p_caovcand $p |- ( ph -> ( ( A F B ) = ( A F C ) <-> B = C ) ) $= f0_caovcand p_id e1_caovcand e2_caovcand e3_caovcand e0_caovcand f0_caovcand f1_caovcand f2_caovcand f3_caovcand f4_caovcand f5_caovcand f6_caovcand f7_caovcand f8_caovcand f9_caovcand p_caovcang f0_caovcand f0_caovcand f4_caovcand f8_caovcand a_wcel f5_caovcand f7_caovcand a_wcel f6_caovcand f7_caovcand a_wcel f4_caovcand f5_caovcand f9_caovcand a_co f4_caovcand f6_caovcand f9_caovcand a_co a_wceq f5_caovcand f6_caovcand a_wceq a_wb p_syl13anc $.
$}

$(Commute the arguments of an operation cancellation law.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C S T F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z T  $.
	f0_caovcanrd $f wff ph $.
	f1_caovcanrd $f set x $.
	f2_caovcanrd $f set y $.
	f3_caovcanrd $f set z $.
	f4_caovcanrd $f class A $.
	f5_caovcanrd $f class B $.
	f6_caovcanrd $f class C $.
	f7_caovcanrd $f class S $.
	f8_caovcanrd $f class T $.
	f9_caovcanrd $f class F $.
	e0_caovcanrd $e |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x F y ) = ( x F z ) <-> y = z ) ) $.
	e1_caovcanrd $e |- ( ph -> A e. T ) $.
	e2_caovcanrd $e |- ( ph -> B e. S ) $.
	e3_caovcanrd $e |- ( ph -> C e. S ) $.
	e4_caovcanrd $e |- ( ph -> A e. S ) $.
	e5_caovcanrd $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	p_caovcanrd $p |- ( ph -> ( ( B F A ) = ( C F A ) <-> B = C ) ) $= e5_caovcanrd e4_caovcanrd e2_caovcanrd f0_caovcanrd f1_caovcanrd f2_caovcanrd f4_caovcanrd f5_caovcanrd f7_caovcanrd f9_caovcanrd p_caovcomd e5_caovcanrd e4_caovcanrd e3_caovcanrd f0_caovcanrd f1_caovcanrd f2_caovcanrd f4_caovcanrd f6_caovcanrd f7_caovcanrd f9_caovcanrd p_caovcomd f0_caovcanrd f4_caovcanrd f5_caovcanrd f9_caovcanrd a_co f5_caovcanrd f4_caovcanrd f9_caovcanrd a_co f4_caovcanrd f6_caovcanrd f9_caovcanrd a_co f6_caovcanrd f4_caovcanrd f9_caovcanrd a_co p_eqeq12d e0_caovcanrd e1_caovcanrd e2_caovcanrd e3_caovcanrd f0_caovcanrd f1_caovcanrd f2_caovcanrd f3_caovcanrd f4_caovcanrd f5_caovcanrd f6_caovcanrd f7_caovcanrd f8_caovcanrd f9_caovcanrd p_caovcand f0_caovcanrd f4_caovcanrd f5_caovcanrd f9_caovcanrd a_co f4_caovcanrd f6_caovcanrd f9_caovcanrd a_co a_wceq f5_caovcanrd f4_caovcanrd f9_caovcanrd a_co f6_caovcanrd f4_caovcanrd f9_caovcanrd a_co a_wceq f5_caovcanrd f6_caovcanrd a_wceq p_bitr3d $.
$}

$(Convert an operation cancellation law to class notation.  (Contributed
         by NM, 20-Aug-1995.) $)

${
	$v x y z A B C S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovcan $f set x $.
	f1_caovcan $f set y $.
	f2_caovcan $f set z $.
	f3_caovcan $f class A $.
	f4_caovcan $f class B $.
	f5_caovcan $f class C $.
	f6_caovcan $f class S $.
	f7_caovcan $f class F $.
	e0_caovcan $e |- C e. _V $.
	e1_caovcan $e |- ( ( x e. S /\ y e. S ) -> ( ( x F y ) = ( x F z ) -> y = z ) ) $.
	p_caovcan $p |- ( ( A e. S /\ B e. S ) -> ( ( A F B ) = ( A F C ) -> B = C ) ) $= f0_caovcan a_sup_set_class f3_caovcan f1_caovcan a_sup_set_class f7_caovcan p_oveq1 f0_caovcan a_sup_set_class f3_caovcan f5_caovcan f7_caovcan p_oveq1 f0_caovcan a_sup_set_class f3_caovcan a_wceq f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f3_caovcan f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f5_caovcan f7_caovcan a_co f3_caovcan f5_caovcan f7_caovcan a_co p_eqeq12d f0_caovcan a_sup_set_class f3_caovcan a_wceq f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f5_caovcan f7_caovcan a_co a_wceq f3_caovcan f1_caovcan a_sup_set_class f7_caovcan a_co f3_caovcan f5_caovcan f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f5_caovcan a_wceq p_imbi1d f1_caovcan a_sup_set_class f4_caovcan f3_caovcan f7_caovcan p_oveq2 f1_caovcan a_sup_set_class f4_caovcan a_wceq f3_caovcan f1_caovcan a_sup_set_class f7_caovcan a_co f3_caovcan f4_caovcan f7_caovcan a_co f3_caovcan f5_caovcan f7_caovcan a_co p_eqeq1d f1_caovcan a_sup_set_class f4_caovcan f5_caovcan p_eqeq1 f1_caovcan a_sup_set_class f4_caovcan a_wceq f3_caovcan f1_caovcan a_sup_set_class f7_caovcan a_co f3_caovcan f5_caovcan f7_caovcan a_co a_wceq f3_caovcan f4_caovcan f7_caovcan a_co f3_caovcan f5_caovcan f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f5_caovcan a_wceq f4_caovcan f5_caovcan a_wceq p_imbi12d e0_caovcan f2_caovcan a_sup_set_class f5_caovcan f0_caovcan a_sup_set_class f7_caovcan p_oveq2 f2_caovcan a_sup_set_class f5_caovcan a_wceq f0_caovcan a_sup_set_class f2_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f5_caovcan f7_caovcan a_co f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co p_eqeq2d f2_caovcan a_sup_set_class f5_caovcan f1_caovcan a_sup_set_class p_eqeq2 f2_caovcan a_sup_set_class f5_caovcan a_wceq f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f2_caovcan a_sup_set_class f7_caovcan a_co a_wceq f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f5_caovcan f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f2_caovcan a_sup_set_class a_wceq f1_caovcan a_sup_set_class f5_caovcan a_wceq p_imbi12d f2_caovcan a_sup_set_class f5_caovcan a_wceq f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f2_caovcan a_sup_set_class f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f2_caovcan a_sup_set_class a_wceq a_wi f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f5_caovcan f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f5_caovcan a_wceq a_wi f0_caovcan a_sup_set_class f6_caovcan a_wcel f1_caovcan a_sup_set_class f6_caovcan a_wcel a_wa p_imbi2d e1_caovcan f0_caovcan a_sup_set_class f6_caovcan a_wcel f1_caovcan a_sup_set_class f6_caovcan a_wcel a_wa f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f2_caovcan a_sup_set_class f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f2_caovcan a_sup_set_class a_wceq a_wi a_wi f0_caovcan a_sup_set_class f6_caovcan a_wcel f1_caovcan a_sup_set_class f6_caovcan a_wcel a_wa f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f5_caovcan f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f5_caovcan a_wceq a_wi a_wi f2_caovcan f5_caovcan p_vtocl f0_caovcan a_sup_set_class f1_caovcan a_sup_set_class f7_caovcan a_co f0_caovcan a_sup_set_class f5_caovcan f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f5_caovcan a_wceq a_wi f3_caovcan f1_caovcan a_sup_set_class f7_caovcan a_co f3_caovcan f5_caovcan f7_caovcan a_co a_wceq f1_caovcan a_sup_set_class f5_caovcan a_wceq a_wi f3_caovcan f4_caovcan f7_caovcan a_co f3_caovcan f5_caovcan f7_caovcan a_co a_wceq f4_caovcan f5_caovcan a_wceq a_wi f0_caovcan f1_caovcan f3_caovcan f4_caovcan f6_caovcan f6_caovcan p_vtocl2ga $.
$}

$(Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 31-Dec-2014.) $)

${
	$v ph x y z A B C R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovordig $f wff ph $.
	f1_caovordig $f set x $.
	f2_caovordig $f set y $.
	f3_caovordig $f set z $.
	f4_caovordig $f class A $.
	f5_caovordig $f class B $.
	f6_caovordig $f class C $.
	f7_caovordig $f class R $.
	f8_caovordig $f class S $.
	f9_caovordig $f class F $.
	e0_caovordig $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y -> ( z F x ) R ( z F y ) ) ) $.
	p_caovordig $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) -> ( A R B -> ( C F A ) R ( C F B ) ) ) $= e0_caovordig f0_caovordig f1_caovordig a_sup_set_class f2_caovordig a_sup_set_class f7_caovordig a_wbr f3_caovordig a_sup_set_class f1_caovordig a_sup_set_class f9_caovordig a_co f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f7_caovordig a_wbr a_wi f1_caovordig f2_caovordig f3_caovordig f8_caovordig f8_caovordig f8_caovordig p_ralrimivvva f1_caovordig a_sup_set_class f4_caovordig f2_caovordig a_sup_set_class f7_caovordig p_breq1 f1_caovordig a_sup_set_class f4_caovordig f3_caovordig a_sup_set_class f9_caovordig p_oveq2 f1_caovordig a_sup_set_class f4_caovordig a_wceq f3_caovordig a_sup_set_class f1_caovordig a_sup_set_class f9_caovordig a_co f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f7_caovordig p_breq1d f1_caovordig a_sup_set_class f4_caovordig a_wceq f1_caovordig a_sup_set_class f2_caovordig a_sup_set_class f7_caovordig a_wbr f4_caovordig f2_caovordig a_sup_set_class f7_caovordig a_wbr f3_caovordig a_sup_set_class f1_caovordig a_sup_set_class f9_caovordig a_co f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f7_caovordig a_wbr f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f7_caovordig a_wbr p_imbi12d f2_caovordig a_sup_set_class f5_caovordig f4_caovordig f7_caovordig p_breq2 f2_caovordig a_sup_set_class f5_caovordig f3_caovordig a_sup_set_class f9_caovordig p_oveq2 f2_caovordig a_sup_set_class f5_caovordig a_wceq f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f3_caovordig a_sup_set_class f5_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f7_caovordig p_breq2d f2_caovordig a_sup_set_class f5_caovordig a_wceq f4_caovordig f2_caovordig a_sup_set_class f7_caovordig a_wbr f4_caovordig f5_caovordig f7_caovordig a_wbr f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f7_caovordig a_wbr f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f5_caovordig f9_caovordig a_co f7_caovordig a_wbr p_imbi12d f3_caovordig a_sup_set_class f6_caovordig f4_caovordig f9_caovordig p_oveq1 f3_caovordig a_sup_set_class f6_caovordig f5_caovordig f9_caovordig p_oveq1 f3_caovordig a_sup_set_class f6_caovordig a_wceq f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f6_caovordig f4_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f5_caovordig f9_caovordig a_co f6_caovordig f5_caovordig f9_caovordig a_co f7_caovordig p_breq12d f3_caovordig a_sup_set_class f6_caovordig a_wceq f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f5_caovordig f9_caovordig a_co f7_caovordig a_wbr f6_caovordig f4_caovordig f9_caovordig a_co f6_caovordig f5_caovordig f9_caovordig a_co f7_caovordig a_wbr f4_caovordig f5_caovordig f7_caovordig a_wbr p_imbi2d f1_caovordig a_sup_set_class f2_caovordig a_sup_set_class f7_caovordig a_wbr f3_caovordig a_sup_set_class f1_caovordig a_sup_set_class f9_caovordig a_co f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f7_caovordig a_wbr a_wi f4_caovordig f5_caovordig f7_caovordig a_wbr f6_caovordig f4_caovordig f9_caovordig a_co f6_caovordig f5_caovordig f9_caovordig a_co f7_caovordig a_wbr a_wi f4_caovordig f2_caovordig a_sup_set_class f7_caovordig a_wbr f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f7_caovordig a_wbr a_wi f4_caovordig f5_caovordig f7_caovordig a_wbr f3_caovordig a_sup_set_class f4_caovordig f9_caovordig a_co f3_caovordig a_sup_set_class f5_caovordig f9_caovordig a_co f7_caovordig a_wbr a_wi f1_caovordig f2_caovordig f3_caovordig f4_caovordig f5_caovordig f6_caovordig f8_caovordig f8_caovordig f8_caovordig p_rspc3v f0_caovordig f1_caovordig a_sup_set_class f2_caovordig a_sup_set_class f7_caovordig a_wbr f3_caovordig a_sup_set_class f1_caovordig a_sup_set_class f9_caovordig a_co f3_caovordig a_sup_set_class f2_caovordig a_sup_set_class f9_caovordig a_co f7_caovordig a_wbr a_wi f3_caovordig f8_caovordig a_wral f2_caovordig f8_caovordig a_wral f1_caovordig f8_caovordig a_wral f4_caovordig f8_caovordig a_wcel f5_caovordig f8_caovordig a_wcel f6_caovordig f8_caovordig a_wcel a_w3a f4_caovordig f5_caovordig f7_caovordig a_wbr f6_caovordig f4_caovordig f9_caovordig a_co f6_caovordig f5_caovordig f9_caovordig a_co f7_caovordig a_wbr a_wi p_mpan9 $.
$}

$(Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 31-Dec-2014.) $)

${
	$v ph x y z A B C R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovordid $f wff ph $.
	f1_caovordid $f set x $.
	f2_caovordid $f set y $.
	f3_caovordid $f set z $.
	f4_caovordid $f class A $.
	f5_caovordid $f class B $.
	f6_caovordid $f class C $.
	f7_caovordid $f class R $.
	f8_caovordid $f class S $.
	f9_caovordid $f class F $.
	e0_caovordid $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y -> ( z F x ) R ( z F y ) ) ) $.
	e1_caovordid $e |- ( ph -> A e. S ) $.
	e2_caovordid $e |- ( ph -> B e. S ) $.
	e3_caovordid $e |- ( ph -> C e. S ) $.
	p_caovordid $p |- ( ph -> ( A R B -> ( C F A ) R ( C F B ) ) ) $= f0_caovordid p_id e1_caovordid e2_caovordid e3_caovordid e0_caovordid f0_caovordid f1_caovordid f2_caovordid f3_caovordid f4_caovordid f5_caovordid f6_caovordid f7_caovordid f8_caovordid f9_caovordid p_caovordig f0_caovordid f0_caovordid f4_caovordid f8_caovordid a_wcel f5_caovordid f8_caovordid a_wcel f6_caovordid f8_caovordid a_wcel f4_caovordid f5_caovordid f7_caovordid a_wbr f6_caovordid f4_caovordid f9_caovordid a_co f6_caovordid f5_caovordid f9_caovordid a_co f7_caovordid a_wbr a_wi p_syl13anc $.
$}

$(Convert an operation ordering law to class notation.  (Contributed by
         NM, 19-Feb-1996.)  (Revised by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovordg $f wff ph $.
	f1_caovordg $f set x $.
	f2_caovordg $f set y $.
	f3_caovordg $f set z $.
	f4_caovordg $f class A $.
	f5_caovordg $f class B $.
	f6_caovordg $f class C $.
	f7_caovordg $f class R $.
	f8_caovordg $f class S $.
	f9_caovordg $f class F $.
	e0_caovordg $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	p_caovordg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $= e0_caovordg f0_caovordg f1_caovordg a_sup_set_class f2_caovordg a_sup_set_class f7_caovordg a_wbr f3_caovordg a_sup_set_class f1_caovordg a_sup_set_class f9_caovordg a_co f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f7_caovordg a_wbr a_wb f1_caovordg f2_caovordg f3_caovordg f8_caovordg f8_caovordg f8_caovordg p_ralrimivvva f1_caovordg a_sup_set_class f4_caovordg f2_caovordg a_sup_set_class f7_caovordg p_breq1 f1_caovordg a_sup_set_class f4_caovordg f3_caovordg a_sup_set_class f9_caovordg p_oveq2 f1_caovordg a_sup_set_class f4_caovordg a_wceq f3_caovordg a_sup_set_class f1_caovordg a_sup_set_class f9_caovordg a_co f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f7_caovordg p_breq1d f1_caovordg a_sup_set_class f4_caovordg a_wceq f1_caovordg a_sup_set_class f2_caovordg a_sup_set_class f7_caovordg a_wbr f4_caovordg f2_caovordg a_sup_set_class f7_caovordg a_wbr f3_caovordg a_sup_set_class f1_caovordg a_sup_set_class f9_caovordg a_co f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f7_caovordg a_wbr f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f7_caovordg a_wbr p_bibi12d f2_caovordg a_sup_set_class f5_caovordg f4_caovordg f7_caovordg p_breq2 f2_caovordg a_sup_set_class f5_caovordg f3_caovordg a_sup_set_class f9_caovordg p_oveq2 f2_caovordg a_sup_set_class f5_caovordg a_wceq f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f3_caovordg a_sup_set_class f5_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f7_caovordg p_breq2d f2_caovordg a_sup_set_class f5_caovordg a_wceq f4_caovordg f2_caovordg a_sup_set_class f7_caovordg a_wbr f4_caovordg f5_caovordg f7_caovordg a_wbr f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f7_caovordg a_wbr f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f5_caovordg f9_caovordg a_co f7_caovordg a_wbr p_bibi12d f3_caovordg a_sup_set_class f6_caovordg f4_caovordg f9_caovordg p_oveq1 f3_caovordg a_sup_set_class f6_caovordg f5_caovordg f9_caovordg p_oveq1 f3_caovordg a_sup_set_class f6_caovordg a_wceq f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f6_caovordg f4_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f5_caovordg f9_caovordg a_co f6_caovordg f5_caovordg f9_caovordg a_co f7_caovordg p_breq12d f3_caovordg a_sup_set_class f6_caovordg a_wceq f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f5_caovordg f9_caovordg a_co f7_caovordg a_wbr f6_caovordg f4_caovordg f9_caovordg a_co f6_caovordg f5_caovordg f9_caovordg a_co f7_caovordg a_wbr f4_caovordg f5_caovordg f7_caovordg a_wbr p_bibi2d f1_caovordg a_sup_set_class f2_caovordg a_sup_set_class f7_caovordg a_wbr f3_caovordg a_sup_set_class f1_caovordg a_sup_set_class f9_caovordg a_co f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f7_caovordg a_wbr a_wb f4_caovordg f5_caovordg f7_caovordg a_wbr f6_caovordg f4_caovordg f9_caovordg a_co f6_caovordg f5_caovordg f9_caovordg a_co f7_caovordg a_wbr a_wb f4_caovordg f2_caovordg a_sup_set_class f7_caovordg a_wbr f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f7_caovordg a_wbr a_wb f4_caovordg f5_caovordg f7_caovordg a_wbr f3_caovordg a_sup_set_class f4_caovordg f9_caovordg a_co f3_caovordg a_sup_set_class f5_caovordg f9_caovordg a_co f7_caovordg a_wbr a_wb f1_caovordg f2_caovordg f3_caovordg f4_caovordg f5_caovordg f6_caovordg f8_caovordg f8_caovordg f8_caovordg p_rspc3v f0_caovordg f1_caovordg a_sup_set_class f2_caovordg a_sup_set_class f7_caovordg a_wbr f3_caovordg a_sup_set_class f1_caovordg a_sup_set_class f9_caovordg a_co f3_caovordg a_sup_set_class f2_caovordg a_sup_set_class f9_caovordg a_co f7_caovordg a_wbr a_wb f3_caovordg f8_caovordg a_wral f2_caovordg f8_caovordg a_wral f1_caovordg f8_caovordg a_wral f4_caovordg f8_caovordg a_wcel f5_caovordg f8_caovordg a_wcel f6_caovordg f8_caovordg a_wcel a_w3a f4_caovordg f5_caovordg f7_caovordg a_wbr f6_caovordg f4_caovordg f9_caovordg a_co f6_caovordg f5_caovordg f9_caovordg a_co f7_caovordg a_wbr a_wb p_mpan9 $.
$}

$(Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovordd $f wff ph $.
	f1_caovordd $f set x $.
	f2_caovordd $f set y $.
	f3_caovordd $f set z $.
	f4_caovordd $f class A $.
	f5_caovordd $f class B $.
	f6_caovordd $f class C $.
	f7_caovordd $f class R $.
	f8_caovordd $f class S $.
	f9_caovordd $f class F $.
	e0_caovordd $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	e1_caovordd $e |- ( ph -> A e. S ) $.
	e2_caovordd $e |- ( ph -> B e. S ) $.
	e3_caovordd $e |- ( ph -> C e. S ) $.
	p_caovordd $p |- ( ph -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $= f0_caovordd p_id e1_caovordd e2_caovordd e3_caovordd e0_caovordd f0_caovordd f1_caovordd f2_caovordd f3_caovordd f4_caovordd f5_caovordd f6_caovordd f7_caovordd f8_caovordd f9_caovordd p_caovordg f0_caovordd f0_caovordd f4_caovordd f8_caovordd a_wcel f5_caovordd f8_caovordd a_wcel f6_caovordd f8_caovordd a_wcel f4_caovordd f5_caovordd f7_caovordd a_wbr f6_caovordd f4_caovordd f9_caovordd a_co f6_caovordd f5_caovordd f9_caovordd a_co f7_caovordd a_wbr a_wb p_syl13anc $.
$}

$(Operation ordering law with commuted arguments.  (Contributed by Mario
         Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovord2d $f wff ph $.
	f1_caovord2d $f set x $.
	f2_caovord2d $f set y $.
	f3_caovord2d $f set z $.
	f4_caovord2d $f class A $.
	f5_caovord2d $f class B $.
	f6_caovord2d $f class C $.
	f7_caovord2d $f class R $.
	f8_caovord2d $f class S $.
	f9_caovord2d $f class F $.
	e0_caovord2d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	e1_caovord2d $e |- ( ph -> A e. S ) $.
	e2_caovord2d $e |- ( ph -> B e. S ) $.
	e3_caovord2d $e |- ( ph -> C e. S ) $.
	e4_caovord2d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	p_caovord2d $p |- ( ph -> ( A R B <-> ( A F C ) R ( B F C ) ) ) $= e0_caovord2d e1_caovord2d e2_caovord2d e3_caovord2d f0_caovord2d f1_caovord2d f2_caovord2d f3_caovord2d f4_caovord2d f5_caovord2d f6_caovord2d f7_caovord2d f8_caovord2d f9_caovord2d p_caovordd e4_caovord2d e3_caovord2d e1_caovord2d f0_caovord2d f1_caovord2d f2_caovord2d f6_caovord2d f4_caovord2d f8_caovord2d f9_caovord2d p_caovcomd e4_caovord2d e3_caovord2d e2_caovord2d f0_caovord2d f1_caovord2d f2_caovord2d f6_caovord2d f5_caovord2d f8_caovord2d f9_caovord2d p_caovcomd f0_caovord2d f6_caovord2d f4_caovord2d f9_caovord2d a_co f4_caovord2d f6_caovord2d f9_caovord2d a_co f6_caovord2d f5_caovord2d f9_caovord2d a_co f5_caovord2d f6_caovord2d f9_caovord2d a_co f7_caovord2d p_breq12d f0_caovord2d f4_caovord2d f5_caovord2d f7_caovord2d a_wbr f6_caovord2d f4_caovord2d f9_caovord2d a_co f6_caovord2d f5_caovord2d f9_caovord2d a_co f7_caovord2d a_wbr f4_caovord2d f6_caovord2d f9_caovord2d a_co f5_caovord2d f6_caovord2d f9_caovord2d a_co f7_caovord2d a_wbr p_bitrd $.
$}

$(Ordering law.  (Contributed by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C D R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovord3d $f wff ph $.
	f1_caovord3d $f set x $.
	f2_caovord3d $f set y $.
	f3_caovord3d $f set z $.
	f4_caovord3d $f class A $.
	f5_caovord3d $f class B $.
	f6_caovord3d $f class C $.
	f7_caovord3d $f class D $.
	f8_caovord3d $f class R $.
	f9_caovord3d $f class S $.
	f10_caovord3d $f class F $.
	e0_caovord3d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	e1_caovord3d $e |- ( ph -> A e. S ) $.
	e2_caovord3d $e |- ( ph -> B e. S ) $.
	e3_caovord3d $e |- ( ph -> C e. S ) $.
	e4_caovord3d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e5_caovord3d $e |- ( ph -> D e. S ) $.
	p_caovord3d $p |- ( ph -> ( ( A F B ) = ( C F D ) -> ( A R C <-> D R B ) ) ) $= f4_caovord3d f5_caovord3d f10_caovord3d a_co f6_caovord3d f7_caovord3d f10_caovord3d a_co f6_caovord3d f5_caovord3d f10_caovord3d a_co f8_caovord3d p_breq1 e0_caovord3d e1_caovord3d e3_caovord3d e2_caovord3d e4_caovord3d f0_caovord3d f1_caovord3d f2_caovord3d f3_caovord3d f4_caovord3d f6_caovord3d f5_caovord3d f8_caovord3d f9_caovord3d f10_caovord3d p_caovord2d e0_caovord3d e5_caovord3d e2_caovord3d e3_caovord3d f0_caovord3d f1_caovord3d f2_caovord3d f3_caovord3d f7_caovord3d f5_caovord3d f6_caovord3d f8_caovord3d f9_caovord3d f10_caovord3d p_caovordd f0_caovord3d f4_caovord3d f6_caovord3d f8_caovord3d a_wbr f4_caovord3d f5_caovord3d f10_caovord3d a_co f6_caovord3d f5_caovord3d f10_caovord3d a_co f8_caovord3d a_wbr f7_caovord3d f5_caovord3d f8_caovord3d a_wbr f6_caovord3d f7_caovord3d f10_caovord3d a_co f6_caovord3d f5_caovord3d f10_caovord3d a_co f8_caovord3d a_wbr p_bibi12d f4_caovord3d f5_caovord3d f10_caovord3d a_co f6_caovord3d f7_caovord3d f10_caovord3d a_co a_wceq f4_caovord3d f6_caovord3d f8_caovord3d a_wbr f7_caovord3d f5_caovord3d f8_caovord3d a_wbr a_wb f0_caovord3d f4_caovord3d f5_caovord3d f10_caovord3d a_co f6_caovord3d f5_caovord3d f10_caovord3d a_co f8_caovord3d a_wbr f6_caovord3d f7_caovord3d f10_caovord3d a_co f6_caovord3d f5_caovord3d f10_caovord3d a_co f8_caovord3d a_wbr a_wb p_syl5ibr $.
$}

$(Convert an operation ordering law to class notation.  (Contributed by
         NM, 19-Feb-1996.) $)

${
	$v x y z A B C R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovord $f set x $.
	f1_caovord $f set y $.
	f2_caovord $f set z $.
	f3_caovord $f class A $.
	f4_caovord $f class B $.
	f5_caovord $f class C $.
	f6_caovord $f class R $.
	f7_caovord $f class S $.
	f8_caovord $f class F $.
	e0_caovord $e |- A e. _V $.
	e1_caovord $e |- B e. _V $.
	e2_caovord $e |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	p_caovord $p |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $= f2_caovord a_sup_set_class f5_caovord f3_caovord f8_caovord p_oveq1 f2_caovord a_sup_set_class f5_caovord f4_caovord f8_caovord p_oveq1 f2_caovord a_sup_set_class f5_caovord a_wceq f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f5_caovord f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f4_caovord f8_caovord a_co f5_caovord f4_caovord f8_caovord a_co f6_caovord p_breq12d f2_caovord a_sup_set_class f5_caovord a_wceq f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f4_caovord f8_caovord a_co f6_caovord a_wbr f5_caovord f3_caovord f8_caovord a_co f5_caovord f4_caovord f8_caovord a_co f6_caovord a_wbr f3_caovord f4_caovord f6_caovord a_wbr p_bibi2d e0_caovord e1_caovord f0_caovord a_sup_set_class f3_caovord f1_caovord a_sup_set_class f6_caovord p_breq1 f0_caovord a_sup_set_class f3_caovord f2_caovord a_sup_set_class f8_caovord p_oveq2 f0_caovord a_sup_set_class f3_caovord a_wceq f2_caovord a_sup_set_class f0_caovord a_sup_set_class f8_caovord a_co f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f6_caovord p_breq1d f0_caovord a_sup_set_class f3_caovord a_wceq f0_caovord a_sup_set_class f1_caovord a_sup_set_class f6_caovord a_wbr f3_caovord f1_caovord a_sup_set_class f6_caovord a_wbr f2_caovord a_sup_set_class f0_caovord a_sup_set_class f8_caovord a_co f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f6_caovord a_wbr f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f6_caovord a_wbr p_bibi12d f1_caovord a_sup_set_class f4_caovord f3_caovord f6_caovord p_breq2 f1_caovord a_sup_set_class f4_caovord f2_caovord a_sup_set_class f8_caovord p_oveq2 f1_caovord a_sup_set_class f4_caovord a_wceq f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f2_caovord a_sup_set_class f4_caovord f8_caovord a_co f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f6_caovord p_breq2d f1_caovord a_sup_set_class f4_caovord a_wceq f3_caovord f1_caovord a_sup_set_class f6_caovord a_wbr f3_caovord f4_caovord f6_caovord a_wbr f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f6_caovord a_wbr f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f4_caovord f8_caovord a_co f6_caovord a_wbr p_bibi12d f0_caovord a_sup_set_class f3_caovord a_wceq f0_caovord a_sup_set_class f1_caovord a_sup_set_class f6_caovord a_wbr f2_caovord a_sup_set_class f0_caovord a_sup_set_class f8_caovord a_co f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f6_caovord a_wbr a_wb f3_caovord f1_caovord a_sup_set_class f6_caovord a_wbr f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f6_caovord a_wbr a_wb f1_caovord a_sup_set_class f4_caovord a_wceq f3_caovord f4_caovord f6_caovord a_wbr f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f4_caovord f8_caovord a_co f6_caovord a_wbr a_wb p_sylan9bb f0_caovord a_sup_set_class f3_caovord a_wceq f1_caovord a_sup_set_class f4_caovord a_wceq a_wa f0_caovord a_sup_set_class f1_caovord a_sup_set_class f6_caovord a_wbr f2_caovord a_sup_set_class f0_caovord a_sup_set_class f8_caovord a_co f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f6_caovord a_wbr a_wb f3_caovord f4_caovord f6_caovord a_wbr f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f4_caovord f8_caovord a_co f6_caovord a_wbr a_wb f2_caovord a_sup_set_class f7_caovord a_wcel p_imbi2d e2_caovord f2_caovord a_sup_set_class f7_caovord a_wcel f0_caovord a_sup_set_class f1_caovord a_sup_set_class f6_caovord a_wbr f2_caovord a_sup_set_class f0_caovord a_sup_set_class f8_caovord a_co f2_caovord a_sup_set_class f1_caovord a_sup_set_class f8_caovord a_co f6_caovord a_wbr a_wb a_wi f2_caovord a_sup_set_class f7_caovord a_wcel f3_caovord f4_caovord f6_caovord a_wbr f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f4_caovord f8_caovord a_co f6_caovord a_wbr a_wb a_wi f0_caovord f1_caovord f3_caovord f4_caovord p_vtocl2 f3_caovord f4_caovord f6_caovord a_wbr f2_caovord a_sup_set_class f3_caovord f8_caovord a_co f2_caovord a_sup_set_class f4_caovord f8_caovord a_co f6_caovord a_wbr a_wb f3_caovord f4_caovord f6_caovord a_wbr f5_caovord f3_caovord f8_caovord a_co f5_caovord f4_caovord f8_caovord a_co f6_caovord a_wbr a_wb f2_caovord f5_caovord f7_caovord p_vtoclga $.
$}

$((We don't bother to eliminate this redundant hypothesis.) $)

$(Operation ordering law with commuted arguments.  (Contributed by NM,
         27-Feb-1996.) $)

${
	$v x y z A B C R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovord2 $f set x $.
	f1_caovord2 $f set y $.
	f2_caovord2 $f set z $.
	f3_caovord2 $f class A $.
	f4_caovord2 $f class B $.
	f5_caovord2 $f class C $.
	f6_caovord2 $f class R $.
	f7_caovord2 $f class S $.
	f8_caovord2 $f class F $.
	e0_caovord2 $e |- A e. _V $.
	e1_caovord2 $e |- B e. _V $.
	e2_caovord2 $e |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	e3_caovord2 $e |- C e. _V $.
	e4_caovord2 $e |- ( x F y ) = ( y F x ) $.
	p_caovord2 $p |- ( C e. S -> ( A R B <-> ( A F C ) R ( B F C ) ) ) $= e0_caovord2 e1_caovord2 e2_caovord2 f0_caovord2 f1_caovord2 f2_caovord2 f3_caovord2 f4_caovord2 f5_caovord2 f6_caovord2 f7_caovord2 f8_caovord2 p_caovord e3_caovord2 e0_caovord2 e4_caovord2 f0_caovord2 f1_caovord2 f5_caovord2 f3_caovord2 f8_caovord2 p_caovcom e3_caovord2 e1_caovord2 e4_caovord2 f0_caovord2 f1_caovord2 f5_caovord2 f4_caovord2 f8_caovord2 p_caovcom f5_caovord2 f3_caovord2 f8_caovord2 a_co f3_caovord2 f5_caovord2 f8_caovord2 a_co f5_caovord2 f4_caovord2 f8_caovord2 a_co f4_caovord2 f5_caovord2 f8_caovord2 a_co f6_caovord2 p_breq12i f5_caovord2 f7_caovord2 a_wcel f3_caovord2 f4_caovord2 f6_caovord2 a_wbr f5_caovord2 f3_caovord2 f8_caovord2 a_co f5_caovord2 f4_caovord2 f8_caovord2 a_co f6_caovord2 a_wbr f3_caovord2 f5_caovord2 f8_caovord2 a_co f4_caovord2 f5_caovord2 f8_caovord2 a_co f6_caovord2 a_wbr p_syl6bb $.
$}

$((We don't bother to eliminate redundant hypotheses.) $)

$(Ordering law.  (Contributed by NM, 29-Feb-1996.) $)

${
	$v x y z A B C D R S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovord3 $f set x $.
	f1_caovord3 $f set y $.
	f2_caovord3 $f set z $.
	f3_caovord3 $f class A $.
	f4_caovord3 $f class B $.
	f5_caovord3 $f class C $.
	f6_caovord3 $f class D $.
	f7_caovord3 $f class R $.
	f8_caovord3 $f class S $.
	f9_caovord3 $f class F $.
	e0_caovord3 $e |- A e. _V $.
	e1_caovord3 $e |- B e. _V $.
	e2_caovord3 $e |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
	e3_caovord3 $e |- C e. _V $.
	e4_caovord3 $e |- ( x F y ) = ( y F x ) $.
	e5_caovord3 $e |- D e. _V $.
	p_caovord3 $p |- ( ( ( B e. S /\ C e. S ) /\ ( A F B ) = ( C F D ) ) -> ( A R C <-> D R B ) ) $= e0_caovord3 e3_caovord3 e2_caovord3 e1_caovord3 e4_caovord3 f0_caovord3 f1_caovord3 f2_caovord3 f3_caovord3 f5_caovord3 f4_caovord3 f7_caovord3 f8_caovord3 f9_caovord3 p_caovord2 f4_caovord3 f8_caovord3 a_wcel f3_caovord3 f5_caovord3 f7_caovord3 a_wbr f3_caovord3 f4_caovord3 f9_caovord3 a_co f5_caovord3 f4_caovord3 f9_caovord3 a_co f7_caovord3 a_wbr a_wb f5_caovord3 f8_caovord3 a_wcel p_adantr f3_caovord3 f4_caovord3 f9_caovord3 a_co f5_caovord3 f6_caovord3 f9_caovord3 a_co f5_caovord3 f4_caovord3 f9_caovord3 a_co f7_caovord3 p_breq1 f4_caovord3 f8_caovord3 a_wcel f5_caovord3 f8_caovord3 a_wcel a_wa f3_caovord3 f5_caovord3 f7_caovord3 a_wbr f3_caovord3 f4_caovord3 f9_caovord3 a_co f5_caovord3 f4_caovord3 f9_caovord3 a_co f7_caovord3 a_wbr f3_caovord3 f4_caovord3 f9_caovord3 a_co f5_caovord3 f6_caovord3 f9_caovord3 a_co a_wceq f5_caovord3 f6_caovord3 f9_caovord3 a_co f5_caovord3 f4_caovord3 f9_caovord3 a_co f7_caovord3 a_wbr p_sylan9bb e5_caovord3 e1_caovord3 e2_caovord3 f0_caovord3 f1_caovord3 f2_caovord3 f6_caovord3 f4_caovord3 f5_caovord3 f7_caovord3 f8_caovord3 f9_caovord3 p_caovord f5_caovord3 f8_caovord3 a_wcel f6_caovord3 f4_caovord3 f7_caovord3 a_wbr f5_caovord3 f6_caovord3 f9_caovord3 a_co f5_caovord3 f4_caovord3 f9_caovord3 a_co f7_caovord3 a_wbr a_wb f4_caovord3 f8_caovord3 a_wcel f3_caovord3 f4_caovord3 f9_caovord3 a_co f5_caovord3 f6_caovord3 f9_caovord3 a_co a_wceq p_ad2antlr f4_caovord3 f8_caovord3 a_wcel f5_caovord3 f8_caovord3 a_wcel a_wa f3_caovord3 f4_caovord3 f9_caovord3 a_co f5_caovord3 f6_caovord3 f9_caovord3 a_co a_wceq a_wa f3_caovord3 f5_caovord3 f7_caovord3 a_wbr f5_caovord3 f6_caovord3 f9_caovord3 a_co f5_caovord3 f4_caovord3 f9_caovord3 a_co f7_caovord3 a_wbr f6_caovord3 f4_caovord3 f7_caovord3 a_wbr p_bitr4d $.
$}

$(Convert an operation distributive law to class notation.  (Contributed
         by NM, 25-Aug-1995.)  (Revised by Mario Carneiro, 26-Jul-2014.) $)

${
	$v ph x y z A B C S F G H K  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z H  $.
	$d x y z K  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovdig $f wff ph $.
	f1_caovdig $f set x $.
	f2_caovdig $f set y $.
	f3_caovdig $f set z $.
	f4_caovdig $f class A $.
	f5_caovdig $f class B $.
	f6_caovdig $f class C $.
	f7_caovdig $f class S $.
	f8_caovdig $f class F $.
	f9_caovdig $f class G $.
	f10_caovdig $f class H $.
	f11_caovdig $f class K $.
	e0_caovdig $e |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) H ( x G z ) ) ) $.
	p_caovdig $p |- ( ( ph /\ ( A e. K /\ B e. S /\ C e. S ) ) -> ( A G ( B F C ) ) = ( ( A G B ) H ( A G C ) ) ) $= e0_caovdig f0_caovdig f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f9_caovdig a_co f1_caovdig a_sup_set_class f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co a_wceq f1_caovdig f2_caovdig f3_caovdig f11_caovdig f7_caovdig f7_caovdig p_ralrimivvva f1_caovdig a_sup_set_class f4_caovdig f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig p_oveq1 f1_caovdig a_sup_set_class f4_caovdig f2_caovdig a_sup_set_class f9_caovdig p_oveq1 f1_caovdig a_sup_set_class f4_caovdig f3_caovdig a_sup_set_class f9_caovdig p_oveq1 f1_caovdig a_sup_set_class f4_caovdig a_wceq f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f9_caovdig a_co f4_caovdig f2_caovdig a_sup_set_class f9_caovdig a_co f1_caovdig a_sup_set_class f3_caovdig a_sup_set_class f9_caovdig a_co f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig p_oveq12d f1_caovdig a_sup_set_class f4_caovdig a_wceq f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f4_caovdig f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f9_caovdig a_co f1_caovdig a_sup_set_class f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co f4_caovdig f2_caovdig a_sup_set_class f9_caovdig a_co f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co p_eqeq12d f2_caovdig a_sup_set_class f5_caovdig f3_caovdig a_sup_set_class f8_caovdig p_oveq1 f2_caovdig a_sup_set_class f5_caovdig a_wceq f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f5_caovdig f3_caovdig a_sup_set_class f8_caovdig a_co f4_caovdig f9_caovdig p_oveq2d f2_caovdig a_sup_set_class f5_caovdig f4_caovdig f9_caovdig p_oveq2 f2_caovdig a_sup_set_class f5_caovdig a_wceq f4_caovdig f2_caovdig a_sup_set_class f9_caovdig a_co f4_caovdig f5_caovdig f9_caovdig a_co f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig p_oveq1d f2_caovdig a_sup_set_class f5_caovdig a_wceq f4_caovdig f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f4_caovdig f5_caovdig f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f4_caovdig f2_caovdig a_sup_set_class f9_caovdig a_co f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co f4_caovdig f5_caovdig f9_caovdig a_co f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co p_eqeq12d f3_caovdig a_sup_set_class f6_caovdig f5_caovdig f8_caovdig p_oveq2 f3_caovdig a_sup_set_class f6_caovdig a_wceq f5_caovdig f3_caovdig a_sup_set_class f8_caovdig a_co f5_caovdig f6_caovdig f8_caovdig a_co f4_caovdig f9_caovdig p_oveq2d f3_caovdig a_sup_set_class f6_caovdig f4_caovdig f9_caovdig p_oveq2 f3_caovdig a_sup_set_class f6_caovdig a_wceq f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f4_caovdig f6_caovdig f9_caovdig a_co f4_caovdig f5_caovdig f9_caovdig a_co f10_caovdig p_oveq2d f3_caovdig a_sup_set_class f6_caovdig a_wceq f4_caovdig f5_caovdig f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f4_caovdig f5_caovdig f6_caovdig f8_caovdig a_co f9_caovdig a_co f4_caovdig f5_caovdig f9_caovdig a_co f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co f4_caovdig f5_caovdig f9_caovdig a_co f4_caovdig f6_caovdig f9_caovdig a_co f10_caovdig a_co p_eqeq12d f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f9_caovdig a_co f1_caovdig a_sup_set_class f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co a_wceq f4_caovdig f5_caovdig f6_caovdig f8_caovdig a_co f9_caovdig a_co f4_caovdig f5_caovdig f9_caovdig a_co f4_caovdig f6_caovdig f9_caovdig a_co f10_caovdig a_co a_wceq f4_caovdig f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f4_caovdig f2_caovdig a_sup_set_class f9_caovdig a_co f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co a_wceq f4_caovdig f5_caovdig f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f4_caovdig f5_caovdig f9_caovdig a_co f4_caovdig f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co a_wceq f1_caovdig f2_caovdig f3_caovdig f4_caovdig f5_caovdig f6_caovdig f11_caovdig f7_caovdig f7_caovdig p_rspc3v f0_caovdig f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f3_caovdig a_sup_set_class f8_caovdig a_co f9_caovdig a_co f1_caovdig a_sup_set_class f2_caovdig a_sup_set_class f9_caovdig a_co f1_caovdig a_sup_set_class f3_caovdig a_sup_set_class f9_caovdig a_co f10_caovdig a_co a_wceq f3_caovdig f7_caovdig a_wral f2_caovdig f7_caovdig a_wral f1_caovdig f11_caovdig a_wral f4_caovdig f11_caovdig a_wcel f5_caovdig f7_caovdig a_wcel f6_caovdig f7_caovdig a_wcel a_w3a f4_caovdig f5_caovdig f6_caovdig f8_caovdig a_co f9_caovdig a_co f4_caovdig f5_caovdig f9_caovdig a_co f4_caovdig f6_caovdig f9_caovdig a_co f10_caovdig a_co a_wceq p_mpan9 $.
$}

$(Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C S F G H K  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z H  $.
	$d x y z K  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovdid $f wff ph $.
	f1_caovdid $f set x $.
	f2_caovdid $f set y $.
	f3_caovdid $f set z $.
	f4_caovdid $f class A $.
	f5_caovdid $f class B $.
	f6_caovdid $f class C $.
	f7_caovdid $f class S $.
	f8_caovdid $f class F $.
	f9_caovdid $f class G $.
	f10_caovdid $f class H $.
	f11_caovdid $f class K $.
	e0_caovdid $e |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) H ( x G z ) ) ) $.
	e1_caovdid $e |- ( ph -> A e. K ) $.
	e2_caovdid $e |- ( ph -> B e. S ) $.
	e3_caovdid $e |- ( ph -> C e. S ) $.
	p_caovdid $p |- ( ph -> ( A G ( B F C ) ) = ( ( A G B ) H ( A G C ) ) ) $= f0_caovdid p_id e1_caovdid e2_caovdid e3_caovdid e0_caovdid f0_caovdid f1_caovdid f2_caovdid f3_caovdid f4_caovdid f5_caovdid f6_caovdid f7_caovdid f8_caovdid f9_caovdid f10_caovdid f11_caovdid p_caovdig f0_caovdid f0_caovdid f4_caovdid f11_caovdid a_wcel f5_caovdid f7_caovdid a_wcel f6_caovdid f7_caovdid a_wcel f4_caovdid f5_caovdid f6_caovdid f8_caovdid a_co f9_caovdid a_co f4_caovdid f5_caovdid f9_caovdid a_co f4_caovdid f6_caovdid f9_caovdid a_co f10_caovdid a_co a_wceq p_syl13anc $.
$}

$(Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C S F G  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovdir2d $f wff ph $.
	f1_caovdir2d $f set x $.
	f2_caovdir2d $f set y $.
	f3_caovdir2d $f set z $.
	f4_caovdir2d $f class A $.
	f5_caovdir2d $f class B $.
	f6_caovdir2d $f class C $.
	f7_caovdir2d $f class S $.
	f8_caovdir2d $f class F $.
	f9_caovdir2d $f class G $.
	e0_caovdir2d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) ) $.
	e1_caovdir2d $e |- ( ph -> A e. S ) $.
	e2_caovdir2d $e |- ( ph -> B e. S ) $.
	e3_caovdir2d $e |- ( ph -> C e. S ) $.
	e4_caovdir2d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
	e5_caovdir2d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x G y ) = ( y G x ) ) $.
	p_caovdir2d $p |- ( ph -> ( ( A F B ) G C ) = ( ( A G C ) F ( B G C ) ) ) $= e0_caovdir2d e3_caovdir2d e1_caovdir2d e2_caovdir2d f0_caovdir2d f1_caovdir2d f2_caovdir2d f3_caovdir2d f6_caovdir2d f4_caovdir2d f5_caovdir2d f7_caovdir2d f8_caovdir2d f9_caovdir2d f8_caovdir2d f7_caovdir2d p_caovdid e5_caovdir2d e4_caovdir2d e1_caovdir2d e2_caovdir2d f0_caovdir2d f1_caovdir2d f2_caovdir2d f4_caovdir2d f5_caovdir2d f7_caovdir2d f7_caovdir2d f7_caovdir2d f8_caovdir2d p_caovcld e3_caovdir2d f0_caovdir2d f1_caovdir2d f2_caovdir2d f4_caovdir2d f5_caovdir2d f8_caovdir2d a_co f6_caovdir2d f7_caovdir2d f9_caovdir2d p_caovcomd e5_caovdir2d e1_caovdir2d e3_caovdir2d f0_caovdir2d f1_caovdir2d f2_caovdir2d f4_caovdir2d f6_caovdir2d f7_caovdir2d f9_caovdir2d p_caovcomd e5_caovdir2d e2_caovdir2d e3_caovdir2d f0_caovdir2d f1_caovdir2d f2_caovdir2d f5_caovdir2d f6_caovdir2d f7_caovdir2d f9_caovdir2d p_caovcomd f0_caovdir2d f4_caovdir2d f6_caovdir2d f9_caovdir2d a_co f6_caovdir2d f4_caovdir2d f9_caovdir2d a_co f5_caovdir2d f6_caovdir2d f9_caovdir2d a_co f6_caovdir2d f5_caovdir2d f9_caovdir2d a_co f8_caovdir2d p_oveq12d f0_caovdir2d f6_caovdir2d f4_caovdir2d f5_caovdir2d f8_caovdir2d a_co f9_caovdir2d a_co f6_caovdir2d f4_caovdir2d f9_caovdir2d a_co f6_caovdir2d f5_caovdir2d f9_caovdir2d a_co f8_caovdir2d a_co f4_caovdir2d f5_caovdir2d f8_caovdir2d a_co f6_caovdir2d f9_caovdir2d a_co f4_caovdir2d f6_caovdir2d f9_caovdir2d a_co f5_caovdir2d f6_caovdir2d f9_caovdir2d a_co f8_caovdir2d a_co p_3eqtr4d $.
$}

$(Convert an operation reverse distributive law to class notation.
         (Contributed by Mario Carneiro, 19-Oct-2014.) $)

${
	$v ph x y z A B C S F G H K  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z H  $.
	$d x y z K  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovdirg $f wff ph $.
	f1_caovdirg $f set x $.
	f2_caovdirg $f set y $.
	f3_caovdirg $f set z $.
	f4_caovdirg $f class A $.
	f5_caovdirg $f class B $.
	f6_caovdirg $f class C $.
	f7_caovdirg $f class S $.
	f8_caovdirg $f class F $.
	f9_caovdirg $f class G $.
	f10_caovdirg $f class H $.
	f11_caovdirg $f class K $.
	e0_caovdirg $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x F y ) G z ) = ( ( x G z ) H ( y G z ) ) ) $.
	p_caovdirg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. K ) ) -> ( ( A F B ) G C ) = ( ( A G C ) H ( B G C ) ) ) $= e0_caovdirg f0_caovdirg f1_caovdirg a_sup_set_class f2_caovdirg a_sup_set_class f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f1_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co a_wceq f1_caovdirg f2_caovdirg f3_caovdirg f7_caovdirg f7_caovdirg f11_caovdirg p_ralrimivvva f1_caovdirg a_sup_set_class f4_caovdirg f2_caovdirg a_sup_set_class f8_caovdirg p_oveq1 f1_caovdirg a_sup_set_class f4_caovdirg a_wceq f1_caovdirg a_sup_set_class f2_caovdirg a_sup_set_class f8_caovdirg a_co f4_caovdirg f2_caovdirg a_sup_set_class f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg p_oveq1d f1_caovdirg a_sup_set_class f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg p_oveq1 f1_caovdirg a_sup_set_class f4_caovdirg a_wceq f1_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg p_oveq1d f1_caovdirg a_sup_set_class f4_caovdirg a_wceq f1_caovdirg a_sup_set_class f2_caovdirg a_sup_set_class f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f2_caovdirg a_sup_set_class f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f1_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co p_eqeq12d f2_caovdirg a_sup_set_class f5_caovdirg f4_caovdirg f8_caovdirg p_oveq2 f2_caovdirg a_sup_set_class f5_caovdirg a_wceq f4_caovdirg f2_caovdirg a_sup_set_class f8_caovdirg a_co f4_caovdirg f5_caovdirg f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg p_oveq1d f2_caovdirg a_sup_set_class f5_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg p_oveq1 f2_caovdirg a_sup_set_class f5_caovdirg a_wceq f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f5_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg p_oveq2d f2_caovdirg a_sup_set_class f5_caovdirg a_wceq f4_caovdirg f2_caovdirg a_sup_set_class f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f5_caovdirg f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f5_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co p_eqeq12d f3_caovdirg a_sup_set_class f6_caovdirg f4_caovdirg f5_caovdirg f8_caovdirg a_co f9_caovdirg p_oveq2 f3_caovdirg a_sup_set_class f6_caovdirg f4_caovdirg f9_caovdirg p_oveq2 f3_caovdirg a_sup_set_class f6_caovdirg f5_caovdirg f9_caovdirg p_oveq2 f3_caovdirg a_sup_set_class f6_caovdirg a_wceq f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f6_caovdirg f9_caovdirg a_co f5_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f5_caovdirg f6_caovdirg f9_caovdirg a_co f10_caovdirg p_oveq12d f3_caovdirg a_sup_set_class f6_caovdirg a_wceq f4_caovdirg f5_caovdirg f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f5_caovdirg f8_caovdirg a_co f6_caovdirg f9_caovdirg a_co f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f5_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co f4_caovdirg f6_caovdirg f9_caovdirg a_co f5_caovdirg f6_caovdirg f9_caovdirg a_co f10_caovdirg a_co p_eqeq12d f1_caovdirg a_sup_set_class f2_caovdirg a_sup_set_class f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f1_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co a_wceq f4_caovdirg f5_caovdirg f8_caovdirg a_co f6_caovdirg f9_caovdirg a_co f4_caovdirg f6_caovdirg f9_caovdirg a_co f5_caovdirg f6_caovdirg f9_caovdirg a_co f10_caovdirg a_co a_wceq f4_caovdirg f2_caovdirg a_sup_set_class f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co a_wceq f4_caovdirg f5_caovdirg f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f4_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f5_caovdirg f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co a_wceq f1_caovdirg f2_caovdirg f3_caovdirg f4_caovdirg f5_caovdirg f6_caovdirg f7_caovdirg f7_caovdirg f11_caovdirg p_rspc3v f0_caovdirg f1_caovdirg a_sup_set_class f2_caovdirg a_sup_set_class f8_caovdirg a_co f3_caovdirg a_sup_set_class f9_caovdirg a_co f1_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f2_caovdirg a_sup_set_class f3_caovdirg a_sup_set_class f9_caovdirg a_co f10_caovdirg a_co a_wceq f3_caovdirg f11_caovdirg a_wral f2_caovdirg f7_caovdirg a_wral f1_caovdirg f7_caovdirg a_wral f4_caovdirg f7_caovdirg a_wcel f5_caovdirg f7_caovdirg a_wcel f6_caovdirg f11_caovdirg a_wcel a_w3a f4_caovdirg f5_caovdirg f8_caovdirg a_co f6_caovdirg f9_caovdirg a_co f4_caovdirg f6_caovdirg f9_caovdirg a_co f5_caovdirg f6_caovdirg f9_caovdirg a_co f10_caovdirg a_co a_wceq p_mpan9 $.
$}

$(Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)

${
	$v ph x y z A B C S F G H K  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z H  $.
	$d x y z K  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caovdird $f wff ph $.
	f1_caovdird $f set x $.
	f2_caovdird $f set y $.
	f3_caovdird $f set z $.
	f4_caovdird $f class A $.
	f5_caovdird $f class B $.
	f6_caovdird $f class C $.
	f7_caovdird $f class S $.
	f8_caovdird $f class F $.
	f9_caovdird $f class G $.
	f10_caovdird $f class H $.
	f11_caovdird $f class K $.
	e0_caovdird $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x F y ) G z ) = ( ( x G z ) H ( y G z ) ) ) $.
	e1_caovdird $e |- ( ph -> A e. S ) $.
	e2_caovdird $e |- ( ph -> B e. S ) $.
	e3_caovdird $e |- ( ph -> C e. K ) $.
	p_caovdird $p |- ( ph -> ( ( A F B ) G C ) = ( ( A G C ) H ( B G C ) ) ) $= f0_caovdird p_id e1_caovdird e2_caovdird e3_caovdird e0_caovdird f0_caovdird f1_caovdird f2_caovdird f3_caovdird f4_caovdird f5_caovdird f6_caovdird f7_caovdird f8_caovdird f9_caovdird f10_caovdird f11_caovdird p_caovdirg f0_caovdird f0_caovdird f4_caovdird f7_caovdird a_wcel f5_caovdird f7_caovdird a_wcel f6_caovdird f11_caovdird a_wcel f4_caovdird f5_caovdird f8_caovdird a_co f6_caovdird f9_caovdird a_co f4_caovdird f6_caovdird f9_caovdird a_co f5_caovdird f6_caovdird f9_caovdird a_co f10_caovdird a_co a_wceq p_syl13anc $.
$}

$(Convert an operation distributive law to class notation.  (Contributed
         by NM, 25-Aug-1995.)  (Revised by Mario Carneiro, 28-Jun-2013.) $)

${
	$v x y z A B C F G  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caovdi $f set x $.
	f1_caovdi $f set y $.
	f2_caovdi $f set z $.
	f3_caovdi $f class A $.
	f4_caovdi $f class B $.
	f5_caovdi $f class C $.
	f6_caovdi $f class F $.
	f7_caovdi $f class G $.
	e0_caovdi $e |- A e. _V $.
	e1_caovdi $e |- B e. _V $.
	e2_caovdi $e |- C e. _V $.
	e3_caovdi $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
	p_caovdi $p |- ( A G ( B F C ) ) = ( ( A G B ) F ( A G C ) ) $= e0_caovdi e1_caovdi e2_caovdi p_tru e3_caovdi f0_caovdi a_sup_set_class f1_caovdi a_sup_set_class f2_caovdi a_sup_set_class f6_caovdi a_co f7_caovdi a_co f0_caovdi a_sup_set_class f1_caovdi a_sup_set_class f7_caovdi a_co f0_caovdi a_sup_set_class f2_caovdi a_sup_set_class f7_caovdi a_co f6_caovdi a_co a_wceq a_wtru f0_caovdi a_sup_set_class a_cvv a_wcel f1_caovdi a_sup_set_class a_cvv a_wcel f2_caovdi a_sup_set_class a_cvv a_wcel a_w3a a_wa p_a1i a_wtru f0_caovdi f1_caovdi f2_caovdi f3_caovdi f4_caovdi f5_caovdi a_cvv f6_caovdi f7_caovdi f6_caovdi a_cvv p_caovdig a_wtru f3_caovdi a_cvv a_wcel f4_caovdi a_cvv a_wcel f5_caovdi a_cvv a_wcel a_w3a f3_caovdi f4_caovdi f5_caovdi f6_caovdi a_co f7_caovdi a_co f3_caovdi f4_caovdi f7_caovdi a_co f3_caovdi f5_caovdi f7_caovdi a_co f6_caovdi a_co a_wceq p_mpan f3_caovdi a_cvv a_wcel f4_caovdi a_cvv a_wcel f5_caovdi a_cvv a_wcel f3_caovdi f4_caovdi f5_caovdi f6_caovdi a_co f7_caovdi a_co f3_caovdi f4_caovdi f7_caovdi a_co f3_caovdi f5_caovdi f7_caovdi a_co f6_caovdi a_co a_wceq p_mp3an $.
$}

$(Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) $)

${
	$v ph x y z A B C S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caov32d $f wff ph $.
	f1_caov32d $f set x $.
	f2_caov32d $f set y $.
	f3_caov32d $f set z $.
	f4_caov32d $f class A $.
	f5_caov32d $f class B $.
	f6_caov32d $f class C $.
	f7_caov32d $f class S $.
	f8_caov32d $f class F $.
	e0_caov32d $e |- ( ph -> A e. S ) $.
	e1_caov32d $e |- ( ph -> B e. S ) $.
	e2_caov32d $e |- ( ph -> C e. S ) $.
	e3_caov32d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e4_caov32d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	p_caov32d $p |- ( ph -> ( ( A F B ) F C ) = ( ( A F C ) F B ) ) $= e3_caov32d e1_caov32d e2_caov32d f0_caov32d f1_caov32d f2_caov32d f5_caov32d f6_caov32d f7_caov32d f8_caov32d p_caovcomd f0_caov32d f5_caov32d f6_caov32d f8_caov32d a_co f6_caov32d f5_caov32d f8_caov32d a_co f4_caov32d f8_caov32d p_oveq2d e4_caov32d e0_caov32d e1_caov32d e2_caov32d f0_caov32d f1_caov32d f2_caov32d f3_caov32d f4_caov32d f5_caov32d f6_caov32d f7_caov32d f8_caov32d p_caovassd e4_caov32d e0_caov32d e2_caov32d e1_caov32d f0_caov32d f1_caov32d f2_caov32d f3_caov32d f4_caov32d f6_caov32d f5_caov32d f7_caov32d f8_caov32d p_caovassd f0_caov32d f4_caov32d f5_caov32d f6_caov32d f8_caov32d a_co f8_caov32d a_co f4_caov32d f6_caov32d f5_caov32d f8_caov32d a_co f8_caov32d a_co f4_caov32d f5_caov32d f8_caov32d a_co f6_caov32d f8_caov32d a_co f4_caov32d f6_caov32d f8_caov32d a_co f5_caov32d f8_caov32d a_co p_3eqtr4d $.
$}

$(Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) $)

${
	$v ph x y z A B C S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caov12d $f wff ph $.
	f1_caov12d $f set x $.
	f2_caov12d $f set y $.
	f3_caov12d $f set z $.
	f4_caov12d $f class A $.
	f5_caov12d $f class B $.
	f6_caov12d $f class C $.
	f7_caov12d $f class S $.
	f8_caov12d $f class F $.
	e0_caov12d $e |- ( ph -> A e. S ) $.
	e1_caov12d $e |- ( ph -> B e. S ) $.
	e2_caov12d $e |- ( ph -> C e. S ) $.
	e3_caov12d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e4_caov12d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	p_caov12d $p |- ( ph -> ( A F ( B F C ) ) = ( B F ( A F C ) ) ) $= e3_caov12d e0_caov12d e1_caov12d f0_caov12d f1_caov12d f2_caov12d f4_caov12d f5_caov12d f7_caov12d f8_caov12d p_caovcomd f0_caov12d f4_caov12d f5_caov12d f8_caov12d a_co f5_caov12d f4_caov12d f8_caov12d a_co f6_caov12d f8_caov12d p_oveq1d e4_caov12d e0_caov12d e1_caov12d e2_caov12d f0_caov12d f1_caov12d f2_caov12d f3_caov12d f4_caov12d f5_caov12d f6_caov12d f7_caov12d f8_caov12d p_caovassd e4_caov12d e1_caov12d e0_caov12d e2_caov12d f0_caov12d f1_caov12d f2_caov12d f3_caov12d f5_caov12d f4_caov12d f6_caov12d f7_caov12d f8_caov12d p_caovassd f0_caov12d f4_caov12d f5_caov12d f8_caov12d a_co f6_caov12d f8_caov12d a_co f5_caov12d f4_caov12d f8_caov12d a_co f6_caov12d f8_caov12d a_co f4_caov12d f5_caov12d f6_caov12d f8_caov12d a_co f8_caov12d a_co f5_caov12d f4_caov12d f6_caov12d f8_caov12d a_co f8_caov12d a_co p_3eqtr3d $.
$}

$(Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) $)

${
	$v ph x y z A B C S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caov31d $f wff ph $.
	f1_caov31d $f set x $.
	f2_caov31d $f set y $.
	f3_caov31d $f set z $.
	f4_caov31d $f class A $.
	f5_caov31d $f class B $.
	f6_caov31d $f class C $.
	f7_caov31d $f class S $.
	f8_caov31d $f class F $.
	e0_caov31d $e |- ( ph -> A e. S ) $.
	e1_caov31d $e |- ( ph -> B e. S ) $.
	e2_caov31d $e |- ( ph -> C e. S ) $.
	e3_caov31d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e4_caov31d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	p_caov31d $p |- ( ph -> ( ( A F B ) F C ) = ( ( C F B ) F A ) ) $= e3_caov31d e0_caov31d e2_caov31d f0_caov31d f1_caov31d f2_caov31d f4_caov31d f6_caov31d f7_caov31d f8_caov31d p_caovcomd f0_caov31d f4_caov31d f6_caov31d f8_caov31d a_co f6_caov31d f4_caov31d f8_caov31d a_co f5_caov31d f8_caov31d p_oveq1d e0_caov31d e1_caov31d e2_caov31d e3_caov31d e4_caov31d f0_caov31d f1_caov31d f2_caov31d f3_caov31d f4_caov31d f5_caov31d f6_caov31d f7_caov31d f8_caov31d p_caov32d e2_caov31d e1_caov31d e0_caov31d e3_caov31d e4_caov31d f0_caov31d f1_caov31d f2_caov31d f3_caov31d f6_caov31d f5_caov31d f4_caov31d f7_caov31d f8_caov31d p_caov32d f0_caov31d f4_caov31d f6_caov31d f8_caov31d a_co f5_caov31d f8_caov31d a_co f6_caov31d f4_caov31d f8_caov31d a_co f5_caov31d f8_caov31d a_co f4_caov31d f5_caov31d f8_caov31d a_co f6_caov31d f8_caov31d a_co f6_caov31d f5_caov31d f8_caov31d a_co f4_caov31d f8_caov31d a_co p_3eqtr4d $.
$}

$(Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) $)

${
	$v ph x y z A B C S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caov13d $f wff ph $.
	f1_caov13d $f set x $.
	f2_caov13d $f set y $.
	f3_caov13d $f set z $.
	f4_caov13d $f class A $.
	f5_caov13d $f class B $.
	f6_caov13d $f class C $.
	f7_caov13d $f class S $.
	f8_caov13d $f class F $.
	e0_caov13d $e |- ( ph -> A e. S ) $.
	e1_caov13d $e |- ( ph -> B e. S ) $.
	e2_caov13d $e |- ( ph -> C e. S ) $.
	e3_caov13d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e4_caov13d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	p_caov13d $p |- ( ph -> ( A F ( B F C ) ) = ( C F ( B F A ) ) ) $= e0_caov13d e1_caov13d e2_caov13d e3_caov13d e4_caov13d f0_caov13d f1_caov13d f2_caov13d f3_caov13d f4_caov13d f5_caov13d f6_caov13d f7_caov13d f8_caov13d p_caov31d e4_caov13d e0_caov13d e1_caov13d e2_caov13d f0_caov13d f1_caov13d f2_caov13d f3_caov13d f4_caov13d f5_caov13d f6_caov13d f7_caov13d f8_caov13d p_caovassd e4_caov13d e2_caov13d e1_caov13d e0_caov13d f0_caov13d f1_caov13d f2_caov13d f3_caov13d f6_caov13d f5_caov13d f4_caov13d f7_caov13d f8_caov13d p_caovassd f0_caov13d f4_caov13d f5_caov13d f8_caov13d a_co f6_caov13d f8_caov13d a_co f6_caov13d f5_caov13d f8_caov13d a_co f4_caov13d f8_caov13d a_co f4_caov13d f5_caov13d f6_caov13d f8_caov13d a_co f8_caov13d a_co f6_caov13d f5_caov13d f4_caov13d f8_caov13d a_co f8_caov13d a_co p_3eqtr3d $.
$}

$(Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) $)

${
	$v ph x y z A B C D S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caov4d $f wff ph $.
	f1_caov4d $f set x $.
	f2_caov4d $f set y $.
	f3_caov4d $f set z $.
	f4_caov4d $f class A $.
	f5_caov4d $f class B $.
	f6_caov4d $f class C $.
	f7_caov4d $f class D $.
	f8_caov4d $f class S $.
	f9_caov4d $f class F $.
	e0_caov4d $e |- ( ph -> A e. S ) $.
	e1_caov4d $e |- ( ph -> B e. S ) $.
	e2_caov4d $e |- ( ph -> C e. S ) $.
	e3_caov4d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e4_caov4d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	e5_caov4d $e |- ( ph -> D e. S ) $.
	e6_caov4d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
	p_caov4d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( B F D ) ) ) $= e1_caov4d e2_caov4d e5_caov4d e3_caov4d e4_caov4d f0_caov4d f1_caov4d f2_caov4d f3_caov4d f5_caov4d f6_caov4d f7_caov4d f8_caov4d f9_caov4d p_caov12d f0_caov4d f5_caov4d f6_caov4d f7_caov4d f9_caov4d a_co f9_caov4d a_co f6_caov4d f5_caov4d f7_caov4d f9_caov4d a_co f9_caov4d a_co f4_caov4d f9_caov4d p_oveq2d e4_caov4d e0_caov4d e1_caov4d e6_caov4d e2_caov4d e5_caov4d f0_caov4d f1_caov4d f2_caov4d f6_caov4d f7_caov4d f8_caov4d f8_caov4d f8_caov4d f9_caov4d p_caovcld f0_caov4d f1_caov4d f2_caov4d f3_caov4d f4_caov4d f5_caov4d f6_caov4d f7_caov4d f9_caov4d a_co f8_caov4d f9_caov4d p_caovassd e4_caov4d e0_caov4d e2_caov4d e6_caov4d e1_caov4d e5_caov4d f0_caov4d f1_caov4d f2_caov4d f5_caov4d f7_caov4d f8_caov4d f8_caov4d f8_caov4d f9_caov4d p_caovcld f0_caov4d f1_caov4d f2_caov4d f3_caov4d f4_caov4d f6_caov4d f5_caov4d f7_caov4d f9_caov4d a_co f8_caov4d f9_caov4d p_caovassd f0_caov4d f4_caov4d f5_caov4d f6_caov4d f7_caov4d f9_caov4d a_co f9_caov4d a_co f9_caov4d a_co f4_caov4d f6_caov4d f5_caov4d f7_caov4d f9_caov4d a_co f9_caov4d a_co f9_caov4d a_co f4_caov4d f5_caov4d f9_caov4d a_co f6_caov4d f7_caov4d f9_caov4d a_co f9_caov4d a_co f4_caov4d f6_caov4d f9_caov4d a_co f5_caov4d f7_caov4d f9_caov4d a_co f9_caov4d a_co p_3eqtr4d $.
$}

$(Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) $)

${
	$v ph x y z A B C D S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caov411d $f wff ph $.
	f1_caov411d $f set x $.
	f2_caov411d $f set y $.
	f3_caov411d $f set z $.
	f4_caov411d $f class A $.
	f5_caov411d $f class B $.
	f6_caov411d $f class C $.
	f7_caov411d $f class D $.
	f8_caov411d $f class S $.
	f9_caov411d $f class F $.
	e0_caov411d $e |- ( ph -> A e. S ) $.
	e1_caov411d $e |- ( ph -> B e. S ) $.
	e2_caov411d $e |- ( ph -> C e. S ) $.
	e3_caov411d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e4_caov411d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	e5_caov411d $e |- ( ph -> D e. S ) $.
	e6_caov411d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
	p_caov411d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) = ( ( C F B ) F ( A F D ) ) ) $= e1_caov411d e0_caov411d e2_caov411d e3_caov411d e4_caov411d e5_caov411d e6_caov411d f0_caov411d f1_caov411d f2_caov411d f3_caov411d f5_caov411d f4_caov411d f6_caov411d f7_caov411d f8_caov411d f9_caov411d p_caov4d e3_caov411d e1_caov411d e0_caov411d f0_caov411d f1_caov411d f2_caov411d f5_caov411d f4_caov411d f8_caov411d f9_caov411d p_caovcomd f0_caov411d f5_caov411d f4_caov411d f9_caov411d a_co f4_caov411d f5_caov411d f9_caov411d a_co f6_caov411d f7_caov411d f9_caov411d a_co f9_caov411d p_oveq1d e3_caov411d e1_caov411d e2_caov411d f0_caov411d f1_caov411d f2_caov411d f5_caov411d f6_caov411d f8_caov411d f9_caov411d p_caovcomd f0_caov411d f5_caov411d f6_caov411d f9_caov411d a_co f6_caov411d f5_caov411d f9_caov411d a_co f4_caov411d f7_caov411d f9_caov411d a_co f9_caov411d p_oveq1d f0_caov411d f5_caov411d f4_caov411d f9_caov411d a_co f6_caov411d f7_caov411d f9_caov411d a_co f9_caov411d a_co f5_caov411d f6_caov411d f9_caov411d a_co f4_caov411d f7_caov411d f9_caov411d a_co f9_caov411d a_co f4_caov411d f5_caov411d f9_caov411d a_co f6_caov411d f7_caov411d f9_caov411d a_co f9_caov411d a_co f6_caov411d f5_caov411d f9_caov411d a_co f4_caov411d f7_caov411d f9_caov411d a_co f9_caov411d a_co p_3eqtr3d $.
$}

$(Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) $)

${
	$v ph x y z A B C D S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z ph  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	f0_caov42d $f wff ph $.
	f1_caov42d $f set x $.
	f2_caov42d $f set y $.
	f3_caov42d $f set z $.
	f4_caov42d $f class A $.
	f5_caov42d $f class B $.
	f6_caov42d $f class C $.
	f7_caov42d $f class D $.
	f8_caov42d $f class S $.
	f9_caov42d $f class F $.
	e0_caov42d $e |- ( ph -> A e. S ) $.
	e1_caov42d $e |- ( ph -> B e. S ) $.
	e2_caov42d $e |- ( ph -> C e. S ) $.
	e3_caov42d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) ) $.
	e4_caov42d $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
	e5_caov42d $e |- ( ph -> D e. S ) $.
	e6_caov42d $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
	p_caov42d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( D F B ) ) ) $= e0_caov42d e1_caov42d e2_caov42d e3_caov42d e4_caov42d e5_caov42d e6_caov42d f0_caov42d f1_caov42d f2_caov42d f3_caov42d f4_caov42d f5_caov42d f6_caov42d f7_caov42d f8_caov42d f9_caov42d p_caov4d e3_caov42d e1_caov42d e5_caov42d f0_caov42d f1_caov42d f2_caov42d f5_caov42d f7_caov42d f8_caov42d f9_caov42d p_caovcomd f0_caov42d f5_caov42d f7_caov42d f9_caov42d a_co f7_caov42d f5_caov42d f9_caov42d a_co f4_caov42d f6_caov42d f9_caov42d a_co f9_caov42d p_oveq2d f0_caov42d f4_caov42d f5_caov42d f9_caov42d a_co f6_caov42d f7_caov42d f9_caov42d a_co f9_caov42d a_co f4_caov42d f6_caov42d f9_caov42d a_co f5_caov42d f7_caov42d f9_caov42d a_co f9_caov42d a_co f4_caov42d f6_caov42d f9_caov42d a_co f7_caov42d f5_caov42d f9_caov42d a_co f9_caov42d a_co p_eqtrd $.
$}

$(Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) $)

${
	$v x y z A B C F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caov32 $f set x $.
	f1_caov32 $f set y $.
	f2_caov32 $f set z $.
	f3_caov32 $f class A $.
	f4_caov32 $f class B $.
	f5_caov32 $f class C $.
	f6_caov32 $f class F $.
	e0_caov32 $e |- A e. _V $.
	e1_caov32 $e |- B e. _V $.
	e2_caov32 $e |- C e. _V $.
	e3_caov32 $e |- ( x F y ) = ( y F x ) $.
	e4_caov32 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	p_caov32 $p |- ( ( A F B ) F C ) = ( ( A F C ) F B ) $= e1_caov32 e2_caov32 e3_caov32 f0_caov32 f1_caov32 f4_caov32 f5_caov32 f6_caov32 p_caovcom f4_caov32 f5_caov32 f6_caov32 a_co f5_caov32 f4_caov32 f6_caov32 a_co f3_caov32 f6_caov32 p_oveq2i e0_caov32 e1_caov32 e2_caov32 e4_caov32 f0_caov32 f1_caov32 f2_caov32 f3_caov32 f4_caov32 f5_caov32 f6_caov32 p_caovass e0_caov32 e2_caov32 e1_caov32 e4_caov32 f0_caov32 f1_caov32 f2_caov32 f3_caov32 f5_caov32 f4_caov32 f6_caov32 p_caovass f3_caov32 f4_caov32 f5_caov32 f6_caov32 a_co f6_caov32 a_co f3_caov32 f5_caov32 f4_caov32 f6_caov32 a_co f6_caov32 a_co f3_caov32 f4_caov32 f6_caov32 a_co f5_caov32 f6_caov32 a_co f3_caov32 f5_caov32 f6_caov32 a_co f4_caov32 f6_caov32 a_co p_3eqtr4i $.
$}

$(Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) $)

${
	$v x y z A B C F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caov12 $f set x $.
	f1_caov12 $f set y $.
	f2_caov12 $f set z $.
	f3_caov12 $f class A $.
	f4_caov12 $f class B $.
	f5_caov12 $f class C $.
	f6_caov12 $f class F $.
	e0_caov12 $e |- A e. _V $.
	e1_caov12 $e |- B e. _V $.
	e2_caov12 $e |- C e. _V $.
	e3_caov12 $e |- ( x F y ) = ( y F x ) $.
	e4_caov12 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	p_caov12 $p |- ( A F ( B F C ) ) = ( B F ( A F C ) ) $= e0_caov12 e1_caov12 e3_caov12 f0_caov12 f1_caov12 f3_caov12 f4_caov12 f6_caov12 p_caovcom f3_caov12 f4_caov12 f6_caov12 a_co f4_caov12 f3_caov12 f6_caov12 a_co f5_caov12 f6_caov12 p_oveq1i e0_caov12 e1_caov12 e2_caov12 e4_caov12 f0_caov12 f1_caov12 f2_caov12 f3_caov12 f4_caov12 f5_caov12 f6_caov12 p_caovass e1_caov12 e0_caov12 e2_caov12 e4_caov12 f0_caov12 f1_caov12 f2_caov12 f4_caov12 f3_caov12 f5_caov12 f6_caov12 p_caovass f3_caov12 f4_caov12 f6_caov12 a_co f5_caov12 f6_caov12 a_co f4_caov12 f3_caov12 f6_caov12 a_co f5_caov12 f6_caov12 a_co f3_caov12 f4_caov12 f5_caov12 f6_caov12 a_co f6_caov12 a_co f4_caov12 f3_caov12 f5_caov12 f6_caov12 a_co f6_caov12 a_co p_3eqtr3i $.
$}

$(Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) $)

${
	$v x y z A B C F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caov31 $f set x $.
	f1_caov31 $f set y $.
	f2_caov31 $f set z $.
	f3_caov31 $f class A $.
	f4_caov31 $f class B $.
	f5_caov31 $f class C $.
	f6_caov31 $f class F $.
	e0_caov31 $e |- A e. _V $.
	e1_caov31 $e |- B e. _V $.
	e2_caov31 $e |- C e. _V $.
	e3_caov31 $e |- ( x F y ) = ( y F x ) $.
	e4_caov31 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	p_caov31 $p |- ( ( A F B ) F C ) = ( ( C F B ) F A ) $= e0_caov31 e2_caov31 e1_caov31 e4_caov31 f0_caov31 f1_caov31 f2_caov31 f3_caov31 f5_caov31 f4_caov31 f6_caov31 p_caovass e0_caov31 e2_caov31 e1_caov31 e3_caov31 e4_caov31 f0_caov31 f1_caov31 f2_caov31 f3_caov31 f5_caov31 f4_caov31 f6_caov31 p_caov12 f3_caov31 f5_caov31 f6_caov31 a_co f4_caov31 f6_caov31 a_co f3_caov31 f5_caov31 f4_caov31 f6_caov31 a_co f6_caov31 a_co f5_caov31 f3_caov31 f4_caov31 f6_caov31 a_co f6_caov31 a_co p_eqtri e0_caov31 e1_caov31 e2_caov31 e3_caov31 e4_caov31 f0_caov31 f1_caov31 f2_caov31 f3_caov31 f4_caov31 f5_caov31 f6_caov31 p_caov32 e2_caov31 e0_caov31 e1_caov31 e3_caov31 e4_caov31 f0_caov31 f1_caov31 f2_caov31 f5_caov31 f3_caov31 f4_caov31 f6_caov31 p_caov32 e2_caov31 e0_caov31 e1_caov31 e4_caov31 f0_caov31 f1_caov31 f2_caov31 f5_caov31 f3_caov31 f4_caov31 f6_caov31 p_caovass f5_caov31 f3_caov31 f6_caov31 a_co f4_caov31 f6_caov31 a_co f5_caov31 f4_caov31 f6_caov31 a_co f3_caov31 f6_caov31 a_co f5_caov31 f3_caov31 f4_caov31 f6_caov31 a_co f6_caov31 a_co p_eqtr3i f3_caov31 f5_caov31 f6_caov31 a_co f4_caov31 f6_caov31 a_co f5_caov31 f3_caov31 f4_caov31 f6_caov31 a_co f6_caov31 a_co f3_caov31 f4_caov31 f6_caov31 a_co f5_caov31 f6_caov31 a_co f5_caov31 f4_caov31 f6_caov31 a_co f3_caov31 f6_caov31 a_co p_3eqtr4i $.
$}

$(Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) $)

${
	$v x y z A B C F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caov13 $f set x $.
	f1_caov13 $f set y $.
	f2_caov13 $f set z $.
	f3_caov13 $f class A $.
	f4_caov13 $f class B $.
	f5_caov13 $f class C $.
	f6_caov13 $f class F $.
	e0_caov13 $e |- A e. _V $.
	e1_caov13 $e |- B e. _V $.
	e2_caov13 $e |- C e. _V $.
	e3_caov13 $e |- ( x F y ) = ( y F x ) $.
	e4_caov13 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	p_caov13 $p |- ( A F ( B F C ) ) = ( C F ( B F A ) ) $= e0_caov13 e1_caov13 e2_caov13 e3_caov13 e4_caov13 f0_caov13 f1_caov13 f2_caov13 f3_caov13 f4_caov13 f5_caov13 f6_caov13 p_caov31 e0_caov13 e1_caov13 e2_caov13 e4_caov13 f0_caov13 f1_caov13 f2_caov13 f3_caov13 f4_caov13 f5_caov13 f6_caov13 p_caovass e2_caov13 e1_caov13 e0_caov13 e4_caov13 f0_caov13 f1_caov13 f2_caov13 f5_caov13 f4_caov13 f3_caov13 f6_caov13 p_caovass f3_caov13 f4_caov13 f6_caov13 a_co f5_caov13 f6_caov13 a_co f5_caov13 f4_caov13 f6_caov13 a_co f3_caov13 f6_caov13 a_co f3_caov13 f4_caov13 f5_caov13 f6_caov13 a_co f6_caov13 a_co f5_caov13 f4_caov13 f3_caov13 f6_caov13 a_co f6_caov13 a_co p_3eqtr3i $.
$}

$(Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) $)

${
	$v x y z A B C D F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caov4 $f set x $.
	f1_caov4 $f set y $.
	f2_caov4 $f set z $.
	f3_caov4 $f class A $.
	f4_caov4 $f class B $.
	f5_caov4 $f class C $.
	f6_caov4 $f class D $.
	f7_caov4 $f class F $.
	e0_caov4 $e |- A e. _V $.
	e1_caov4 $e |- B e. _V $.
	e2_caov4 $e |- C e. _V $.
	e3_caov4 $e |- ( x F y ) = ( y F x ) $.
	e4_caov4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	e5_caov4 $e |- D e. _V $.
	p_caov4 $p |- ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( B F D ) ) $= e1_caov4 e2_caov4 e5_caov4 e3_caov4 e4_caov4 f0_caov4 f1_caov4 f2_caov4 f4_caov4 f5_caov4 f6_caov4 f7_caov4 p_caov12 f4_caov4 f5_caov4 f6_caov4 f7_caov4 a_co f7_caov4 a_co f5_caov4 f4_caov4 f6_caov4 f7_caov4 a_co f7_caov4 a_co f3_caov4 f7_caov4 p_oveq2i e0_caov4 e1_caov4 f5_caov4 f6_caov4 f7_caov4 p_ovex e4_caov4 f0_caov4 f1_caov4 f2_caov4 f3_caov4 f4_caov4 f5_caov4 f6_caov4 f7_caov4 a_co f7_caov4 p_caovass e0_caov4 e2_caov4 f4_caov4 f6_caov4 f7_caov4 p_ovex e4_caov4 f0_caov4 f1_caov4 f2_caov4 f3_caov4 f5_caov4 f4_caov4 f6_caov4 f7_caov4 a_co f7_caov4 p_caovass f3_caov4 f4_caov4 f5_caov4 f6_caov4 f7_caov4 a_co f7_caov4 a_co f7_caov4 a_co f3_caov4 f5_caov4 f4_caov4 f6_caov4 f7_caov4 a_co f7_caov4 a_co f7_caov4 a_co f3_caov4 f4_caov4 f7_caov4 a_co f5_caov4 f6_caov4 f7_caov4 a_co f7_caov4 a_co f3_caov4 f5_caov4 f7_caov4 a_co f4_caov4 f6_caov4 f7_caov4 a_co f7_caov4 a_co p_3eqtr4i $.
$}

$(Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) $)

${
	$v x y z A B C D F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caov411 $f set x $.
	f1_caov411 $f set y $.
	f2_caov411 $f set z $.
	f3_caov411 $f class A $.
	f4_caov411 $f class B $.
	f5_caov411 $f class C $.
	f6_caov411 $f class D $.
	f7_caov411 $f class F $.
	e0_caov411 $e |- A e. _V $.
	e1_caov411 $e |- B e. _V $.
	e2_caov411 $e |- C e. _V $.
	e3_caov411 $e |- ( x F y ) = ( y F x ) $.
	e4_caov411 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	e5_caov411 $e |- D e. _V $.
	p_caov411 $p |- ( ( A F B ) F ( C F D ) ) = ( ( C F B ) F ( A F D ) ) $= e0_caov411 e1_caov411 e2_caov411 e3_caov411 e4_caov411 f0_caov411 f1_caov411 f2_caov411 f3_caov411 f4_caov411 f5_caov411 f7_caov411 p_caov31 f3_caov411 f4_caov411 f7_caov411 a_co f5_caov411 f7_caov411 a_co f5_caov411 f4_caov411 f7_caov411 a_co f3_caov411 f7_caov411 a_co f6_caov411 f7_caov411 p_oveq1i f3_caov411 f4_caov411 f7_caov411 p_ovex e2_caov411 e5_caov411 e4_caov411 f0_caov411 f1_caov411 f2_caov411 f3_caov411 f4_caov411 f7_caov411 a_co f5_caov411 f6_caov411 f7_caov411 p_caovass f5_caov411 f4_caov411 f7_caov411 p_ovex e0_caov411 e5_caov411 e4_caov411 f0_caov411 f1_caov411 f2_caov411 f5_caov411 f4_caov411 f7_caov411 a_co f3_caov411 f6_caov411 f7_caov411 p_caovass f3_caov411 f4_caov411 f7_caov411 a_co f5_caov411 f7_caov411 a_co f6_caov411 f7_caov411 a_co f5_caov411 f4_caov411 f7_caov411 a_co f3_caov411 f7_caov411 a_co f6_caov411 f7_caov411 a_co f3_caov411 f4_caov411 f7_caov411 a_co f5_caov411 f6_caov411 f7_caov411 a_co f7_caov411 a_co f5_caov411 f4_caov411 f7_caov411 a_co f3_caov411 f6_caov411 f7_caov411 a_co f7_caov411 a_co p_3eqtr3i $.
$}

$(Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) $)

${
	$v x y z A B C D F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caov42 $f set x $.
	f1_caov42 $f set y $.
	f2_caov42 $f set z $.
	f3_caov42 $f class A $.
	f4_caov42 $f class B $.
	f5_caov42 $f class C $.
	f6_caov42 $f class D $.
	f7_caov42 $f class F $.
	e0_caov42 $e |- A e. _V $.
	e1_caov42 $e |- B e. _V $.
	e2_caov42 $e |- C e. _V $.
	e3_caov42 $e |- ( x F y ) = ( y F x ) $.
	e4_caov42 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	e5_caov42 $e |- D e. _V $.
	p_caov42 $p |- ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( D F B ) ) $= e0_caov42 e1_caov42 e2_caov42 e3_caov42 e4_caov42 e5_caov42 f0_caov42 f1_caov42 f2_caov42 f3_caov42 f4_caov42 f5_caov42 f6_caov42 f7_caov42 p_caov4 e1_caov42 e5_caov42 e3_caov42 f0_caov42 f1_caov42 f4_caov42 f6_caov42 f7_caov42 p_caovcom f4_caov42 f6_caov42 f7_caov42 a_co f6_caov42 f4_caov42 f7_caov42 a_co f3_caov42 f5_caov42 f7_caov42 a_co f7_caov42 p_oveq2i f3_caov42 f4_caov42 f7_caov42 a_co f5_caov42 f6_caov42 f7_caov42 a_co f7_caov42 a_co f3_caov42 f5_caov42 f7_caov42 a_co f4_caov42 f6_caov42 f7_caov42 a_co f7_caov42 a_co f3_caov42 f5_caov42 f7_caov42 a_co f6_caov42 f4_caov42 f7_caov42 a_co f7_caov42 a_co p_eqtri $.
$}

$(Reverse distributive law.  (Contributed by NM, 26-Aug-1995.) $)

${
	$v x y z A B C F G  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	f0_caovdir $f set x $.
	f1_caovdir $f set y $.
	f2_caovdir $f set z $.
	f3_caovdir $f class A $.
	f4_caovdir $f class B $.
	f5_caovdir $f class C $.
	f6_caovdir $f class F $.
	f7_caovdir $f class G $.
	e0_caovdir $e |- A e. _V $.
	e1_caovdir $e |- B e. _V $.
	e2_caovdir $e |- C e. _V $.
	e3_caovdir $e |- ( x G y ) = ( y G x ) $.
	e4_caovdir $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
	p_caovdir $p |- ( ( A F B ) G C ) = ( ( A G C ) F ( B G C ) ) $= e2_caovdir e0_caovdir e1_caovdir e4_caovdir f0_caovdir f1_caovdir f2_caovdir f5_caovdir f3_caovdir f4_caovdir f6_caovdir f7_caovdir p_caovdi e2_caovdir f3_caovdir f4_caovdir f6_caovdir p_ovex e3_caovdir f0_caovdir f1_caovdir f5_caovdir f3_caovdir f4_caovdir f6_caovdir a_co f7_caovdir p_caovcom e2_caovdir e0_caovdir e3_caovdir f0_caovdir f1_caovdir f5_caovdir f3_caovdir f7_caovdir p_caovcom e2_caovdir e1_caovdir e3_caovdir f0_caovdir f1_caovdir f5_caovdir f4_caovdir f7_caovdir p_caovcom f5_caovdir f3_caovdir f7_caovdir a_co f3_caovdir f5_caovdir f7_caovdir a_co f5_caovdir f4_caovdir f7_caovdir a_co f4_caovdir f5_caovdir f7_caovdir a_co f6_caovdir p_oveq12i f5_caovdir f3_caovdir f4_caovdir f6_caovdir a_co f7_caovdir a_co f5_caovdir f3_caovdir f7_caovdir a_co f5_caovdir f4_caovdir f7_caovdir a_co f6_caovdir a_co f3_caovdir f4_caovdir f6_caovdir a_co f5_caovdir f7_caovdir a_co f3_caovdir f5_caovdir f7_caovdir a_co f4_caovdir f5_caovdir f7_caovdir a_co f6_caovdir a_co p_3eqtr3i $.
$}

$(Lemma used by real number construction.  (Contributed by NM,
         26-Aug-1995.) $)

${
	$v x y z A B C D F G H  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z H  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z H  $.
	$d x y z  $.
	f0_caovdilem $f set x $.
	f1_caovdilem $f set y $.
	f2_caovdilem $f set z $.
	f3_caovdilem $f class A $.
	f4_caovdilem $f class B $.
	f5_caovdilem $f class C $.
	f6_caovdilem $f class D $.
	f7_caovdilem $f class F $.
	f8_caovdilem $f class G $.
	f9_caovdilem $f class H $.
	e0_caovdilem $e |- A e. _V $.
	e1_caovdilem $e |- B e. _V $.
	e2_caovdilem $e |- C e. _V $.
	e3_caovdilem $e |- ( x G y ) = ( y G x ) $.
	e4_caovdilem $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
	e5_caovdilem $e |- D e. _V $.
	e6_caovdilem $e |- H e. _V $.
	e7_caovdilem $e |- ( ( x G y ) G z ) = ( x G ( y G z ) ) $.
	p_caovdilem $p |- ( ( ( A G C ) F ( B G D ) ) G H ) = ( ( A G ( C G H ) ) F ( B G ( D G H ) ) ) $= f3_caovdilem f5_caovdilem f8_caovdilem p_ovex f4_caovdilem f6_caovdilem f8_caovdilem p_ovex e6_caovdilem e3_caovdilem e4_caovdilem f0_caovdilem f1_caovdilem f2_caovdilem f3_caovdilem f5_caovdilem f8_caovdilem a_co f4_caovdilem f6_caovdilem f8_caovdilem a_co f9_caovdilem f7_caovdilem f8_caovdilem p_caovdir e0_caovdilem e2_caovdilem e6_caovdilem e7_caovdilem f0_caovdilem f1_caovdilem f2_caovdilem f3_caovdilem f5_caovdilem f9_caovdilem f8_caovdilem p_caovass e1_caovdilem e5_caovdilem e6_caovdilem e7_caovdilem f0_caovdilem f1_caovdilem f2_caovdilem f4_caovdilem f6_caovdilem f9_caovdilem f8_caovdilem p_caovass f3_caovdilem f5_caovdilem f8_caovdilem a_co f9_caovdilem f8_caovdilem a_co f3_caovdilem f5_caovdilem f9_caovdilem f8_caovdilem a_co f8_caovdilem a_co f4_caovdilem f6_caovdilem f8_caovdilem a_co f9_caovdilem f8_caovdilem a_co f4_caovdilem f6_caovdilem f9_caovdilem f8_caovdilem a_co f8_caovdilem a_co f7_caovdilem p_oveq12i f3_caovdilem f5_caovdilem f8_caovdilem a_co f4_caovdilem f6_caovdilem f8_caovdilem a_co f7_caovdilem a_co f9_caovdilem f8_caovdilem a_co f3_caovdilem f5_caovdilem f8_caovdilem a_co f9_caovdilem f8_caovdilem a_co f4_caovdilem f6_caovdilem f8_caovdilem a_co f9_caovdilem f8_caovdilem a_co f7_caovdilem a_co f3_caovdilem f5_caovdilem f9_caovdilem f8_caovdilem a_co f8_caovdilem a_co f4_caovdilem f6_caovdilem f9_caovdilem f8_caovdilem a_co f8_caovdilem a_co f7_caovdilem a_co p_eqtri $.
$}

$(Lemma used in real number construction.  (Contributed by NM,
         26-Aug-1995.) $)

${
	$v x y z A B C D R F G H  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z G  $.
	$d x y z H  $.
	$d x y z  $.
	$d x y z R  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z H  $.
	$d x y z R  $.
	f0_caovlem2 $f set x $.
	f1_caovlem2 $f set y $.
	f2_caovlem2 $f set z $.
	f3_caovlem2 $f class A $.
	f4_caovlem2 $f class B $.
	f5_caovlem2 $f class C $.
	f6_caovlem2 $f class D $.
	f7_caovlem2 $f class R $.
	f8_caovlem2 $f class F $.
	f9_caovlem2 $f class G $.
	f10_caovlem2 $f class H $.
	e0_caovlem2 $e |- A e. _V $.
	e1_caovlem2 $e |- B e. _V $.
	e2_caovlem2 $e |- C e. _V $.
	e3_caovlem2 $e |- ( x G y ) = ( y G x ) $.
	e4_caovlem2 $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
	e5_caovlem2 $e |- D e. _V $.
	e6_caovlem2 $e |- H e. _V $.
	e7_caovlem2 $e |- ( ( x G y ) G z ) = ( x G ( y G z ) ) $.
	e8_caovlem2 $e |- R e. _V $.
	e9_caovlem2 $e |- ( x F y ) = ( y F x ) $.
	e10_caovlem2 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	p_caovlem2 $p |- ( ( ( ( A G C ) F ( B G D ) ) G H ) F ( ( ( A G D ) F ( B G C ) ) G R ) ) = ( ( A G ( ( C G H ) F ( D G R ) ) ) F ( B G ( ( C G R ) F ( D G H ) ) ) ) $= f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 p_ovex f4_caovlem2 f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 p_ovex f3_caovlem2 f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 p_ovex e9_caovlem2 e10_caovlem2 f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 p_ovex f0_caovlem2 f1_caovlem2 f2_caovlem2 f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f3_caovlem2 f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 p_caov42 e0_caovlem2 e1_caovlem2 e2_caovlem2 e3_caovlem2 e4_caovlem2 e5_caovlem2 e6_caovlem2 e7_caovlem2 f0_caovlem2 f1_caovlem2 f2_caovlem2 f3_caovlem2 f4_caovlem2 f5_caovlem2 f6_caovlem2 f8_caovlem2 f9_caovlem2 f10_caovlem2 p_caovdilem e0_caovlem2 e1_caovlem2 e5_caovlem2 e3_caovlem2 e4_caovlem2 e2_caovlem2 e8_caovlem2 e7_caovlem2 f0_caovlem2 f1_caovlem2 f2_caovlem2 f3_caovlem2 f4_caovlem2 f6_caovlem2 f5_caovlem2 f8_caovlem2 f9_caovlem2 f7_caovlem2 p_caovdilem f3_caovlem2 f5_caovlem2 f9_caovlem2 a_co f4_caovlem2 f6_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f10_caovlem2 f9_caovlem2 a_co f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co f3_caovlem2 f6_caovlem2 f9_caovlem2 a_co f4_caovlem2 f5_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f7_caovlem2 f9_caovlem2 a_co f3_caovlem2 f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co f8_caovlem2 p_oveq12i e0_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 p_ovex f6_caovlem2 f7_caovlem2 f9_caovlem2 p_ovex e4_caovlem2 f0_caovlem2 f1_caovlem2 f2_caovlem2 f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f8_caovlem2 f9_caovlem2 p_caovdi e1_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 p_ovex f6_caovlem2 f10_caovlem2 f9_caovlem2 p_ovex e4_caovlem2 f0_caovlem2 f1_caovlem2 f2_caovlem2 f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f8_caovlem2 f9_caovlem2 p_caovdi f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f9_caovlem2 a_co f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f3_caovlem2 f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co f8_caovlem2 p_oveq12i f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co f3_caovlem2 f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co f8_caovlem2 a_co f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f3_caovlem2 f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co f8_caovlem2 a_co f3_caovlem2 f5_caovlem2 f9_caovlem2 a_co f4_caovlem2 f6_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f10_caovlem2 f9_caovlem2 a_co f3_caovlem2 f6_caovlem2 f9_caovlem2 a_co f4_caovlem2 f5_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f7_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f3_caovlem2 f5_caovlem2 f10_caovlem2 f9_caovlem2 a_co f6_caovlem2 f7_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f9_caovlem2 a_co f4_caovlem2 f5_caovlem2 f7_caovlem2 f9_caovlem2 a_co f6_caovlem2 f10_caovlem2 f9_caovlem2 a_co f8_caovlem2 a_co f9_caovlem2 a_co f8_caovlem2 a_co p_3eqtr4i $.
$}

$(Identity element. $)

$(Uniqueness of inverse element in commutative, associative operation
         with identity.  Remark in proof of Proposition 9-2.4 of [Gleason]
         p. 119.  (Contributed by NM, 4-Mar-1996.) $)

${
	$v x y z w A B S F  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z F  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z  $.
	$d x y z S  $.
	$d x y z  $.
	$d u w A  $.
	$d u v w x y B  $.
	$d u v w x y z F  $.
	$d w x S  $.
	f0_caovmo $f set x $.
	f1_caovmo $f set y $.
	f2_caovmo $f set z $.
	f3_caovmo $f set w $.
	f4_caovmo $f class A $.
	f5_caovmo $f class B $.
	f6_caovmo $f class S $.
	f7_caovmo $f class F $.
	i0_caovmo $f set v $.
	i1_caovmo $f set u $.
	e0_caovmo $e |- B e. S $.
	e1_caovmo $e |- dom F = ( S X. S ) $.
	e2_caovmo $e |- -. (/) e. S $.
	e3_caovmo $e |- ( x F y ) = ( y F x ) $.
	e4_caovmo $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
	e5_caovmo $e |- ( x e. S -> ( x F B ) = x ) $.
	p_caovmo $p |- E* w ( A F w ) = B $= i1_caovmo a_sup_set_class f4_caovmo f3_caovmo a_sup_set_class f7_caovmo p_oveq1 i1_caovmo a_sup_set_class f4_caovmo a_wceq i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo p_eqeq1d i1_caovmo a_sup_set_class f4_caovmo a_wceq i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f3_caovmo p_mobidv f3_caovmo a_sup_set_class i0_caovmo a_sup_set_class i1_caovmo a_sup_set_class f7_caovmo p_oveq2 f3_caovmo a_sup_set_class i0_caovmo a_sup_set_class a_wceq i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo p_eqeq1d i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f3_caovmo i0_caovmo p_mo4 i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq p_simpr i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo f3_caovmo a_sup_set_class f7_caovmo p_oveq2d i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq p_simpl i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo i0_caovmo a_sup_set_class f7_caovmo p_oveq1d i1_caovmo p_vex f3_caovmo p_vex i0_caovmo p_vex e4_caovmo f0_caovmo f1_caovmo f2_caovmo i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo p_caovass i1_caovmo p_vex f3_caovmo p_vex i0_caovmo p_vex e3_caovmo e4_caovmo f0_caovmo f1_caovmo f2_caovmo i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo p_caov12 i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co i0_caovmo a_sup_set_class f7_caovmo a_co i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f7_caovmo a_co f3_caovmo a_sup_set_class i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f7_caovmo a_co p_eqtri e0_caovmo f5_caovmo f6_caovmo p_elexi i0_caovmo p_vex e3_caovmo f0_caovmo f1_caovmo f5_caovmo i0_caovmo a_sup_set_class f7_caovmo p_caovcom i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo i0_caovmo a_sup_set_class f7_caovmo a_co f3_caovmo a_sup_set_class i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f7_caovmo a_co i0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co p_3eqtr3g i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa f3_caovmo a_sup_set_class i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f7_caovmo a_co f3_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co i0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co p_eqtr3d i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq p_simpl e0_caovmo i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo f6_caovmo p_syl6eqel e1_caovmo e2_caovmo i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f6_caovmo f7_caovmo p_ndmovrcl i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f6_caovmo a_wcel i1_caovmo a_sup_set_class f6_caovmo a_wcel f3_caovmo a_sup_set_class f6_caovmo a_wcel a_wa p_syl i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class f6_caovmo a_wcel f3_caovmo a_sup_set_class f6_caovmo a_wcel p_simprd f0_caovmo a_sup_set_class f3_caovmo a_sup_set_class f5_caovmo f7_caovmo p_oveq1 f0_caovmo a_sup_set_class f3_caovmo a_sup_set_class a_wceq p_id f0_caovmo a_sup_set_class f3_caovmo a_sup_set_class a_wceq f0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co f3_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co f0_caovmo a_sup_set_class f3_caovmo a_sup_set_class p_eqeq12d e5_caovmo f0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co f0_caovmo a_sup_set_class a_wceq f3_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co f3_caovmo a_sup_set_class a_wceq f0_caovmo f3_caovmo a_sup_set_class f6_caovmo p_vtoclga i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa f3_caovmo a_sup_set_class f6_caovmo a_wcel f3_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co f3_caovmo a_sup_set_class a_wceq p_syl i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq p_simpr e0_caovmo i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo f6_caovmo p_syl6eqel e1_caovmo e2_caovmo i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f6_caovmo f7_caovmo p_ndmovrcl i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f6_caovmo a_wcel i1_caovmo a_sup_set_class f6_caovmo a_wcel i0_caovmo a_sup_set_class f6_caovmo a_wcel a_wa p_syl i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i1_caovmo a_sup_set_class f6_caovmo a_wcel i0_caovmo a_sup_set_class f6_caovmo a_wcel p_simprd f0_caovmo a_sup_set_class i0_caovmo a_sup_set_class f5_caovmo f7_caovmo p_oveq1 f0_caovmo a_sup_set_class i0_caovmo a_sup_set_class a_wceq p_id f0_caovmo a_sup_set_class i0_caovmo a_sup_set_class a_wceq f0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co i0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co f0_caovmo a_sup_set_class i0_caovmo a_sup_set_class p_eqeq12d e5_caovmo f0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co f0_caovmo a_sup_set_class a_wceq i0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co i0_caovmo a_sup_set_class a_wceq f0_caovmo i0_caovmo a_sup_set_class f6_caovmo p_vtoclga i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa i0_caovmo a_sup_set_class f6_caovmo a_wcel i0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co i0_caovmo a_sup_set_class a_wceq p_syl i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa f3_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co i0_caovmo a_sup_set_class f5_caovmo f7_caovmo a_co f3_caovmo a_sup_set_class i0_caovmo a_sup_set_class p_3eqtr3d i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa f3_caovmo a_sup_set_class i0_caovmo a_sup_set_class a_wceq a_wi i0_caovmo a_ax-gen i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f3_caovmo a_wmo i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq i1_caovmo a_sup_set_class i0_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa f3_caovmo a_sup_set_class i0_caovmo a_sup_set_class a_wceq a_wi i0_caovmo a_wal f3_caovmo p_mpgbir i1_caovmo a_sup_set_class f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f3_caovmo a_wmo f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f3_caovmo a_wmo i1_caovmo f4_caovmo f6_caovmo p_vtoclg f4_caovmo f6_caovmo a_wcel f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f3_caovmo p_moanimv f4_caovmo f6_caovmo a_wcel f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa f3_caovmo a_wmo f4_caovmo f6_caovmo a_wcel f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f3_caovmo a_wmo a_wi p_mpbir e0_caovmo f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo f6_caovmo p_eleq1 f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f6_caovmo a_wcel f5_caovmo f6_caovmo a_wcel p_mpbiri e1_caovmo e2_caovmo f4_caovmo f3_caovmo a_sup_set_class f6_caovmo f7_caovmo p_ndmovrcl f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f6_caovmo a_wcel f4_caovmo f6_caovmo a_wcel f3_caovmo a_sup_set_class f6_caovmo a_wcel a_wa p_syl f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f4_caovmo f6_caovmo a_wcel f3_caovmo a_sup_set_class f6_caovmo a_wcel p_simpld f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f4_caovmo f6_caovmo a_wcel p_ancri f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f4_caovmo f6_caovmo a_wcel f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa f3_caovmo p_moimi f4_caovmo f6_caovmo a_wcel f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq a_wa f3_caovmo a_wmo f4_caovmo f3_caovmo a_sup_set_class f7_caovmo a_co f5_caovmo a_wceq f3_caovmo a_wmo a_ax-mp $.
$}

$(Lemma for ~ grprinvd .  (Contributed by NM, 9-Aug-2013.) $)

${
	$v ph ps x y z B .+ O X  $.
	$d u v w x y z B  $.
	$d u v w x y z O  $.
	$d u v w x y z ph  $.
	$d u v w y z  $.
	$d u v w x y z .+  $.
	$d u v w y z X  $.
	$d u v w y ps  $.
	f0_grprinvlem $f wff ph $.
	f1_grprinvlem $f wff ps $.
	f2_grprinvlem $f set x $.
	f3_grprinvlem $f set y $.
	f4_grprinvlem $f set z $.
	f5_grprinvlem $f class B $.
	f6_grprinvlem $f class .+ $.
	f7_grprinvlem $f class O $.
	f8_grprinvlem $f class X $.
	i0_grprinvlem $f set w $.
	i1_grprinvlem $f set v $.
	i2_grprinvlem $f set u $.
	e0_grprinvlem $e |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B ) $.
	e1_grprinvlem $e |- ( ph -> O e. B ) $.
	e2_grprinvlem $e |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x ) $.
	e3_grprinvlem $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) ) $.
	e4_grprinvlem $e |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O ) $.
	e5_grprinvlem $e |- ( ( ph /\ ps ) -> X e. B ) $.
	e6_grprinvlem $e |- ( ( ph /\ ps ) -> ( X .+ X ) = X ) $.
	p_grprinvlem $p |- ( ( ph /\ ps ) -> X = O ) $= e5_grprinvlem e4_grprinvlem f0_grprinvlem f3_grprinvlem a_sup_set_class f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f2_grprinvlem f5_grprinvlem p_ralrimiva f2_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f3_grprinvlem a_sup_set_class f6_grprinvlem p_oveq2 f2_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class a_wceq f3_grprinvlem a_sup_set_class f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f3_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem p_eqeq1d f2_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class a_wceq f3_grprinvlem a_sup_set_class f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem p_rexbidv f3_grprinvlem a_sup_set_class f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f3_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f2_grprinvlem f4_grprinvlem f5_grprinvlem p_cbvralv f0_grprinvlem f3_grprinvlem a_sup_set_class f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f2_grprinvlem f5_grprinvlem a_wral f3_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f4_grprinvlem f5_grprinvlem a_wral p_sylib f4_grprinvlem a_sup_set_class f8_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem p_oveq2 f4_grprinvlem a_sup_set_class f8_grprinvlem a_wceq f3_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f6_grprinvlem a_co f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem p_eqeq1d f4_grprinvlem a_sup_set_class f8_grprinvlem a_wceq f3_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem p_rexbidv f3_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f4_grprinvlem f8_grprinvlem f5_grprinvlem p_rspccva f0_grprinvlem f3_grprinvlem a_sup_set_class f4_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f4_grprinvlem f5_grprinvlem a_wral f8_grprinvlem f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex p_sylan f0_grprinvlem f1_grprinvlem f8_grprinvlem f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex p_syldan e6_grprinvlem f0_grprinvlem f1_grprinvlem a_wa f8_grprinvlem f8_grprinvlem f6_grprinvlem a_co f8_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem p_oveq2d f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f8_grprinvlem f8_grprinvlem f6_grprinvlem a_co f6_grprinvlem a_co f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co a_wceq f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa p_adantr f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq p_simprr f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa a_wa f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem f8_grprinvlem f6_grprinvlem p_oveq1d f0_grprinvlem f1_grprinvlem f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa p_simpll e3_grprinvlem f0_grprinvlem f2_grprinvlem f3_grprinvlem f4_grprinvlem i2_grprinvlem a_sup_set_class i1_grprinvlem a_sup_set_class i0_grprinvlem a_sup_set_class f5_grprinvlem f6_grprinvlem p_caovassg f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa a_wa f0_grprinvlem i2_grprinvlem a_sup_set_class f5_grprinvlem a_wcel i1_grprinvlem a_sup_set_class f5_grprinvlem a_wcel i0_grprinvlem a_sup_set_class f5_grprinvlem a_wcel a_w3a i2_grprinvlem a_sup_set_class i1_grprinvlem a_sup_set_class f6_grprinvlem a_co i0_grprinvlem a_sup_set_class f6_grprinvlem a_co i2_grprinvlem a_sup_set_class i1_grprinvlem a_sup_set_class i0_grprinvlem a_sup_set_class f6_grprinvlem a_co f6_grprinvlem a_co a_wceq p_sylan f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq p_simprl e5_grprinvlem f0_grprinvlem f1_grprinvlem a_wa f8_grprinvlem f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa p_adantr e5_grprinvlem f0_grprinvlem f1_grprinvlem a_wa f8_grprinvlem f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa p_adantr f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa a_wa i2_grprinvlem i1_grprinvlem i0_grprinvlem f3_grprinvlem a_sup_set_class f8_grprinvlem f8_grprinvlem f5_grprinvlem f6_grprinvlem p_caovassd e5_grprinvlem e2_grprinvlem f0_grprinvlem f7_grprinvlem f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f2_grprinvlem a_sup_set_class a_wceq f2_grprinvlem f5_grprinvlem p_ralrimiva f2_grprinvlem a_sup_set_class f3_grprinvlem a_sup_set_class f7_grprinvlem f6_grprinvlem p_oveq2 f2_grprinvlem a_sup_set_class f3_grprinvlem a_sup_set_class a_wceq p_id f2_grprinvlem a_sup_set_class f3_grprinvlem a_sup_set_class a_wceq f7_grprinvlem f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem a_co f2_grprinvlem a_sup_set_class f3_grprinvlem a_sup_set_class p_eqeq12d f7_grprinvlem f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f2_grprinvlem a_sup_set_class a_wceq f7_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem a_co f3_grprinvlem a_sup_set_class a_wceq f2_grprinvlem f3_grprinvlem f5_grprinvlem p_cbvralv f0_grprinvlem f7_grprinvlem f2_grprinvlem a_sup_set_class f6_grprinvlem a_co f2_grprinvlem a_sup_set_class a_wceq f2_grprinvlem f5_grprinvlem a_wral f7_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem a_co f3_grprinvlem a_sup_set_class a_wceq f3_grprinvlem f5_grprinvlem a_wral p_sylib f0_grprinvlem f7_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem a_co f3_grprinvlem a_sup_set_class a_wceq f3_grprinvlem f5_grprinvlem a_wral f1_grprinvlem p_adantr f3_grprinvlem a_sup_set_class f8_grprinvlem f7_grprinvlem f6_grprinvlem p_oveq2 f3_grprinvlem a_sup_set_class f8_grprinvlem a_wceq p_id f3_grprinvlem a_sup_set_class f8_grprinvlem a_wceq f7_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem a_co f7_grprinvlem f8_grprinvlem f6_grprinvlem a_co f3_grprinvlem a_sup_set_class f8_grprinvlem p_eqeq12d f7_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem a_co f3_grprinvlem a_sup_set_class a_wceq f7_grprinvlem f8_grprinvlem f6_grprinvlem a_co f8_grprinvlem a_wceq f3_grprinvlem f8_grprinvlem f5_grprinvlem p_rspcv f0_grprinvlem f1_grprinvlem a_wa f8_grprinvlem f5_grprinvlem a_wcel f7_grprinvlem f3_grprinvlem a_sup_set_class f6_grprinvlem a_co f3_grprinvlem a_sup_set_class a_wceq f3_grprinvlem f5_grprinvlem a_wral f7_grprinvlem f8_grprinvlem f6_grprinvlem a_co f8_grprinvlem a_wceq p_sylc f0_grprinvlem f1_grprinvlem a_wa f7_grprinvlem f8_grprinvlem f6_grprinvlem a_co f8_grprinvlem a_wceq f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa p_adantr f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa a_wa f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem f8_grprinvlem f6_grprinvlem a_co f3_grprinvlem a_sup_set_class f8_grprinvlem f8_grprinvlem f6_grprinvlem a_co f6_grprinvlem a_co f8_grprinvlem p_3eqtr3d f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq p_simprr f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq a_wa a_wa f3_grprinvlem a_sup_set_class f8_grprinvlem f8_grprinvlem f6_grprinvlem a_co f6_grprinvlem a_co f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f8_grprinvlem f7_grprinvlem p_3eqtr3d f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f5_grprinvlem a_wcel f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq f8_grprinvlem f7_grprinvlem a_wceq p_expr f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq f8_grprinvlem f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem p_rexlimdva f0_grprinvlem f1_grprinvlem a_wa f3_grprinvlem a_sup_set_class f8_grprinvlem f6_grprinvlem a_co f7_grprinvlem a_wceq f3_grprinvlem f5_grprinvlem a_wrex f8_grprinvlem f7_grprinvlem a_wceq p_mpd $.
$}

$(Deduce right inverse from left inverse and left identity in an
         associative structure (such as a group).  (Contributed by NM,
         10-Aug-2013.)  (Proof shortened by Mario Carneiro, 6-Jan-2015.) $)

${
	$v ph ps x y z B .+ N O X  $.
	$d u v w x y z B  $.
	$d u v w x y z O  $.
	$d u v w x y z ph  $.
	$d u v w y z N  $.
	$d u v w x y z .+  $.
	$d u v w y z X  $.
	$d u v w y ps  $.
	f0_grprinvd $f wff ph $.
	f1_grprinvd $f wff ps $.
	f2_grprinvd $f set x $.
	f3_grprinvd $f set y $.
	f4_grprinvd $f set z $.
	f5_grprinvd $f class B $.
	f6_grprinvd $f class .+ $.
	f7_grprinvd $f class N $.
	f8_grprinvd $f class O $.
	f9_grprinvd $f class X $.
	i0_grprinvd $f set w $.
	i1_grprinvd $f set v $.
	i2_grprinvd $f set u $.
	e0_grprinvd $e |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B ) $.
	e1_grprinvd $e |- ( ph -> O e. B ) $.
	e2_grprinvd $e |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x ) $.
	e3_grprinvd $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) ) $.
	e4_grprinvd $e |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O ) $.
	e5_grprinvd $e |- ( ( ph /\ ps ) -> X e. B ) $.
	e6_grprinvd $e |- ( ( ph /\ ps ) -> N e. B ) $.
	e7_grprinvd $e |- ( ( ph /\ ps ) -> ( N .+ X ) = O ) $.
	p_grprinvd $p |- ( ( ph /\ ps ) -> ( X .+ N ) = O ) $= e0_grprinvd e1_grprinvd e2_grprinvd e3_grprinvd e4_grprinvd e0_grprinvd f0_grprinvd f2_grprinvd a_sup_set_class f5_grprinvd a_wcel f3_grprinvd a_sup_set_class f5_grprinvd a_wcel f2_grprinvd a_sup_set_class f3_grprinvd a_sup_set_class f6_grprinvd a_co f5_grprinvd a_wcel p_3expb f0_grprinvd f2_grprinvd f3_grprinvd i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class f5_grprinvd f5_grprinvd f5_grprinvd f6_grprinvd p_caovclg f0_grprinvd i2_grprinvd a_sup_set_class f5_grprinvd a_wcel i1_grprinvd a_sup_set_class f5_grprinvd a_wcel a_wa i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class f6_grprinvd a_co f5_grprinvd a_wcel f1_grprinvd p_adantlr e5_grprinvd e6_grprinvd f0_grprinvd f1_grprinvd a_wa i2_grprinvd i1_grprinvd f9_grprinvd f7_grprinvd f5_grprinvd f5_grprinvd f5_grprinvd f6_grprinvd p_caovcld e3_grprinvd f0_grprinvd f2_grprinvd f3_grprinvd f4_grprinvd i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class i0_grprinvd a_sup_set_class f5_grprinvd f6_grprinvd p_caovassg f0_grprinvd i2_grprinvd a_sup_set_class f5_grprinvd a_wcel i1_grprinvd a_sup_set_class f5_grprinvd a_wcel i0_grprinvd a_sup_set_class f5_grprinvd a_wcel a_w3a i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class f6_grprinvd a_co i0_grprinvd a_sup_set_class f6_grprinvd a_co i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class i0_grprinvd a_sup_set_class f6_grprinvd a_co f6_grprinvd a_co a_wceq f1_grprinvd p_adantlr e5_grprinvd e6_grprinvd e0_grprinvd f0_grprinvd f2_grprinvd a_sup_set_class f5_grprinvd a_wcel f3_grprinvd a_sup_set_class f5_grprinvd a_wcel f2_grprinvd a_sup_set_class f3_grprinvd a_sup_set_class f6_grprinvd a_co f5_grprinvd a_wcel p_3expb f0_grprinvd f2_grprinvd f3_grprinvd i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class f5_grprinvd f5_grprinvd f5_grprinvd f6_grprinvd p_caovclg f0_grprinvd i2_grprinvd a_sup_set_class f5_grprinvd a_wcel i1_grprinvd a_sup_set_class f5_grprinvd a_wcel a_wa i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class f6_grprinvd a_co f5_grprinvd a_wcel f1_grprinvd p_adantlr e5_grprinvd e6_grprinvd f0_grprinvd f1_grprinvd a_wa i2_grprinvd i1_grprinvd f9_grprinvd f7_grprinvd f5_grprinvd f5_grprinvd f5_grprinvd f6_grprinvd p_caovcld f0_grprinvd f1_grprinvd a_wa i2_grprinvd i1_grprinvd i0_grprinvd f9_grprinvd f7_grprinvd f9_grprinvd f7_grprinvd f6_grprinvd a_co f5_grprinvd f6_grprinvd p_caovassd e7_grprinvd f0_grprinvd f1_grprinvd a_wa f7_grprinvd f9_grprinvd f6_grprinvd a_co f8_grprinvd f7_grprinvd f6_grprinvd p_oveq1d e3_grprinvd f0_grprinvd f2_grprinvd f3_grprinvd f4_grprinvd i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class i0_grprinvd a_sup_set_class f5_grprinvd f6_grprinvd p_caovassg f0_grprinvd i2_grprinvd a_sup_set_class f5_grprinvd a_wcel i1_grprinvd a_sup_set_class f5_grprinvd a_wcel i0_grprinvd a_sup_set_class f5_grprinvd a_wcel a_w3a i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class f6_grprinvd a_co i0_grprinvd a_sup_set_class f6_grprinvd a_co i2_grprinvd a_sup_set_class i1_grprinvd a_sup_set_class i0_grprinvd a_sup_set_class f6_grprinvd a_co f6_grprinvd a_co a_wceq f1_grprinvd p_adantlr e6_grprinvd e5_grprinvd e6_grprinvd f0_grprinvd f1_grprinvd a_wa i2_grprinvd i1_grprinvd i0_grprinvd f7_grprinvd f9_grprinvd f7_grprinvd f5_grprinvd f6_grprinvd p_caovassd e6_grprinvd e2_grprinvd f0_grprinvd f8_grprinvd f2_grprinvd a_sup_set_class f6_grprinvd a_co f2_grprinvd a_sup_set_class a_wceq f2_grprinvd f5_grprinvd p_ralrimiva f2_grprinvd a_sup_set_class f3_grprinvd a_sup_set_class f8_grprinvd f6_grprinvd p_oveq2 f2_grprinvd a_sup_set_class f3_grprinvd a_sup_set_class a_wceq p_id f2_grprinvd a_sup_set_class f3_grprinvd a_sup_set_class a_wceq f8_grprinvd f2_grprinvd a_sup_set_class f6_grprinvd a_co f8_grprinvd f3_grprinvd a_sup_set_class f6_grprinvd a_co f2_grprinvd a_sup_set_class f3_grprinvd a_sup_set_class p_eqeq12d f8_grprinvd f2_grprinvd a_sup_set_class f6_grprinvd a_co f2_grprinvd a_sup_set_class a_wceq f8_grprinvd f3_grprinvd a_sup_set_class f6_grprinvd a_co f3_grprinvd a_sup_set_class a_wceq f2_grprinvd f3_grprinvd f5_grprinvd p_cbvralv f0_grprinvd f8_grprinvd f2_grprinvd a_sup_set_class f6_grprinvd a_co f2_grprinvd a_sup_set_class a_wceq f2_grprinvd f5_grprinvd a_wral f8_grprinvd f3_grprinvd a_sup_set_class f6_grprinvd a_co f3_grprinvd a_sup_set_class a_wceq f3_grprinvd f5_grprinvd a_wral p_sylib f0_grprinvd f8_grprinvd f3_grprinvd a_sup_set_class f6_grprinvd a_co f3_grprinvd a_sup_set_class a_wceq f3_grprinvd f5_grprinvd a_wral f1_grprinvd p_adantr f3_grprinvd a_sup_set_class f7_grprinvd f8_grprinvd f6_grprinvd p_oveq2 f3_grprinvd a_sup_set_class f7_grprinvd a_wceq p_id f3_grprinvd a_sup_set_class f7_grprinvd a_wceq f8_grprinvd f3_grprinvd a_sup_set_class f6_grprinvd a_co f8_grprinvd f7_grprinvd f6_grprinvd a_co f3_grprinvd a_sup_set_class f7_grprinvd p_eqeq12d f8_grprinvd f3_grprinvd a_sup_set_class f6_grprinvd a_co f3_grprinvd a_sup_set_class a_wceq f8_grprinvd f7_grprinvd f6_grprinvd a_co f7_grprinvd a_wceq f3_grprinvd f7_grprinvd f5_grprinvd p_rspcv f0_grprinvd f1_grprinvd a_wa f7_grprinvd f5_grprinvd a_wcel f8_grprinvd f3_grprinvd a_sup_set_class f6_grprinvd a_co f3_grprinvd a_sup_set_class a_wceq f3_grprinvd f5_grprinvd a_wral f8_grprinvd f7_grprinvd f6_grprinvd a_co f7_grprinvd a_wceq p_sylc f0_grprinvd f1_grprinvd a_wa f7_grprinvd f9_grprinvd f6_grprinvd a_co f7_grprinvd f6_grprinvd a_co f8_grprinvd f7_grprinvd f6_grprinvd a_co f7_grprinvd f9_grprinvd f7_grprinvd f6_grprinvd a_co f6_grprinvd a_co f7_grprinvd p_3eqtr3d f0_grprinvd f1_grprinvd a_wa f7_grprinvd f9_grprinvd f7_grprinvd f6_grprinvd a_co f6_grprinvd a_co f7_grprinvd f9_grprinvd f6_grprinvd p_oveq2d f0_grprinvd f1_grprinvd a_wa f9_grprinvd f7_grprinvd f6_grprinvd a_co f9_grprinvd f7_grprinvd f6_grprinvd a_co f6_grprinvd a_co f9_grprinvd f7_grprinvd f9_grprinvd f7_grprinvd f6_grprinvd a_co f6_grprinvd a_co f6_grprinvd a_co f9_grprinvd f7_grprinvd f6_grprinvd a_co p_eqtrd f0_grprinvd f1_grprinvd f2_grprinvd f3_grprinvd f4_grprinvd f5_grprinvd f6_grprinvd f8_grprinvd f9_grprinvd f7_grprinvd f6_grprinvd a_co p_grprinvlem $.
$}

$(Deduce right identity from left inverse and left identity in an
       associative structure (such as a group).  (Contributed by NM,
       10-Aug-2013.)  (Proof shortened by Mario Carneiro, 6-Jan-2015.) $)

${
	$v ph x y z B .+ O  $.
	$d n u v w x y z B  $.
	$d n u v w x y z O  $.
	$d n u v w x y z ph  $.
	$d u v w y z  $.
	$d n u v w x y z .+  $.
	$d u v w y z  $.
	$d u v w y  $.
	f0_grpridd $f wff ph $.
	f1_grpridd $f set x $.
	f2_grpridd $f set y $.
	f3_grpridd $f set z $.
	f4_grpridd $f class B $.
	f5_grpridd $f class .+ $.
	f6_grpridd $f class O $.
	i0_grpridd $f set w $.
	i1_grpridd $f set v $.
	i2_grpridd $f set u $.
	i3_grpridd $f set n $.
	e0_grpridd $e |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B ) $.
	e1_grpridd $e |- ( ph -> O e. B ) $.
	e2_grpridd $e |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x ) $.
	e3_grpridd $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) ) $.
	e4_grpridd $e |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O ) $.
	p_grpridd $p |- ( ( ph /\ x e. B ) -> ( x .+ O ) = x ) $= e4_grpridd f2_grpridd a_sup_set_class i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd p_oveq1 f2_grpridd a_sup_set_class i3_grpridd a_sup_set_class a_wceq f2_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd p_eqeq1d f2_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq f2_grpridd i3_grpridd f4_grpridd p_cbvrexv f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel a_wa f2_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq f2_grpridd f4_grpridd a_wrex i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq i3_grpridd f4_grpridd a_wrex p_sylib e3_grpridd f0_grpridd f1_grpridd f2_grpridd f3_grpridd i2_grpridd a_sup_set_class i1_grpridd a_sup_set_class i0_grpridd a_sup_set_class f4_grpridd f5_grpridd p_caovassg f0_grpridd i2_grpridd a_sup_set_class f4_grpridd a_wcel i1_grpridd a_sup_set_class f4_grpridd a_wcel i0_grpridd a_sup_set_class f4_grpridd a_wcel a_w3a i2_grpridd a_sup_set_class i1_grpridd a_sup_set_class f5_grpridd a_co i0_grpridd a_sup_set_class f5_grpridd a_co i2_grpridd a_sup_set_class i1_grpridd a_sup_set_class i0_grpridd a_sup_set_class f5_grpridd a_co f5_grpridd a_co a_wceq f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa a_wa p_adantlr f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa p_simprl f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq p_simprrl f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa p_simprl f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa a_wa a_wa i2_grpridd i1_grpridd i0_grpridd f1_grpridd a_sup_set_class i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f4_grpridd f5_grpridd p_caovassd e0_grpridd e1_grpridd e2_grpridd e3_grpridd e4_grpridd f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa p_simprl f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq p_simprrl f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq p_simprrr f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa a_wa f1_grpridd f2_grpridd f3_grpridd f4_grpridd f5_grpridd i3_grpridd a_sup_set_class f6_grpridd f1_grpridd a_sup_set_class p_grprinvd f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa a_wa a_wa f1_grpridd a_sup_set_class i3_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd f1_grpridd a_sup_set_class f5_grpridd p_oveq1d f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq p_simprrr f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa a_wa a_wa i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd f1_grpridd a_sup_set_class f5_grpridd p_oveq2d f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa a_wa a_wa f1_grpridd a_sup_set_class i3_grpridd a_sup_set_class f5_grpridd a_co f1_grpridd a_sup_set_class f5_grpridd a_co f1_grpridd a_sup_set_class i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f5_grpridd a_co f6_grpridd f1_grpridd a_sup_set_class f5_grpridd a_co f1_grpridd a_sup_set_class f6_grpridd f5_grpridd a_co p_3eqtr3d f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq a_wa f6_grpridd f1_grpridd a_sup_set_class f5_grpridd a_co f1_grpridd a_sup_set_class f6_grpridd f5_grpridd a_co a_wceq p_anassrs f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel a_wa i3_grpridd a_sup_set_class f4_grpridd a_wcel i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq f6_grpridd f1_grpridd a_sup_set_class f5_grpridd a_co f1_grpridd a_sup_set_class f6_grpridd f5_grpridd a_co a_wceq p_expr f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel a_wa i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq f6_grpridd f1_grpridd a_sup_set_class f5_grpridd a_co f1_grpridd a_sup_set_class f6_grpridd f5_grpridd a_co a_wceq i3_grpridd f4_grpridd p_rexlimdva f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel a_wa i3_grpridd a_sup_set_class f1_grpridd a_sup_set_class f5_grpridd a_co f6_grpridd a_wceq i3_grpridd f4_grpridd a_wrex f6_grpridd f1_grpridd a_sup_set_class f5_grpridd a_co f1_grpridd a_sup_set_class f6_grpridd f5_grpridd a_co a_wceq p_mpd e2_grpridd f0_grpridd f1_grpridd a_sup_set_class f4_grpridd a_wcel a_wa f6_grpridd f1_grpridd a_sup_set_class f5_grpridd a_co f1_grpridd a_sup_set_class f6_grpridd f5_grpridd a_co f1_grpridd a_sup_set_class p_eqtr3d $.
$}


