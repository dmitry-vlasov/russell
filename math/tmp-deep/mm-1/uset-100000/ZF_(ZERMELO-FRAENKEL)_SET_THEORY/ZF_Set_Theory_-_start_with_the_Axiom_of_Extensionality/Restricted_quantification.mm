$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Negated_equality_and_membership.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Restricted quantification

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Extend wff notation to include restricted universal quantification. $)

${
	$v ph x A  $.
	f0_wral $f wff ph $.
	f1_wral $f set x $.
	f2_wral $f class A $.
	a_wral $a wff A. x e. A ph $.
$}

$(Extend wff notation to include restricted existential quantification. $)

${
	$v ph x A  $.
	f0_wrex $f wff ph $.
	f1_wrex $f set x $.
	f2_wrex $f class A $.
	a_wrex $a wff E. x e. A ph $.
$}

$(Extend wff notation to include restricted existential uniqueness. $)

${
	$v ph x A  $.
	f0_wreu $f wff ph $.
	f1_wreu $f set x $.
	f2_wreu $f class A $.
	a_wreu $a wff E! x e. A ph $.
$}

$(Extend wff notation to include restricted "at most one." $)

${
	$v ph x A  $.
	f0_wrmo $f wff ph $.
	f1_wrmo $f set x $.
	f2_wrmo $f class A $.
	a_wrmo $a wff E* x e. A ph $.
$}

$(Extend class notation to include the restricted class abstraction (class
     builder). $)

${
	$v ph x A  $.
	f0_crab $f wff ph $.
	f1_crab $f set x $.
	f2_crab $f class A $.
	a_crab $a class { x e. A | ph } $.
$}

$(Define restricted universal quantification.  Special case of Definition
     4.15(3) of [TakeutiZaring] p. 22.  (Contributed by NM, 19-Aug-1993.) $)

${
	$v ph x A  $.
	f0_df-ral $f wff ph $.
	f1_df-ral $f set x $.
	f2_df-ral $f class A $.
	a_df-ral $a |- ( A. x e. A ph <-> A. x ( x e. A -> ph ) ) $.
$}

$(Define restricted existential quantification.  Special case of Definition
     4.15(4) of [TakeutiZaring] p. 22.  (Contributed by NM, 30-Aug-1993.) $)

${
	$v ph x A  $.
	f0_df-rex $f wff ph $.
	f1_df-rex $f set x $.
	f2_df-rex $f class A $.
	a_df-rex $a |- ( E. x e. A ph <-> E. x ( x e. A /\ ph ) ) $.
$}

$(Define restricted existential uniqueness.  (Contributed by NM,
     22-Nov-1994.) $)

${
	$v ph x A  $.
	f0_df-reu $f wff ph $.
	f1_df-reu $f set x $.
	f2_df-reu $f class A $.
	a_df-reu $a |- ( E! x e. A ph <-> E! x ( x e. A /\ ph ) ) $.
$}

$(Define restricted "at most one".  (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph x A  $.
	f0_df-rmo $f wff ph $.
	f1_df-rmo $f set x $.
	f2_df-rmo $f class A $.
	a_df-rmo $a |- ( E* x e. A ph <-> E* x ( x e. A /\ ph ) ) $.
$}

$(Define a restricted class abstraction (class builder), which is the class
     of all ` x ` in ` A ` such that ` ph ` is true.  Definition of
     [TakeutiZaring] p. 20.  (Contributed by NM, 22-Nov-1994.) $)

${
	$v ph x A  $.
	f0_df-rab $f wff ph $.
	f1_df-rab $f set x $.
	f2_df-rab $f class A $.
	a_df-rab $a |- { x e. A | ph } = { x | ( x e. A /\ ph ) } $.
$}

$(Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)

${
	$v ph x A  $.
	f0_ralnex $f wff ph $.
	f1_ralnex $f set x $.
	f2_ralnex $f class A $.
	p_ralnex $p |- ( A. x e. A -. ph <-> -. E. x e. A ph ) $= f0_ralnex a_wn f1_ralnex f2_ralnex a_df-ral f1_ralnex a_sup_set_class f2_ralnex a_wcel f0_ralnex f1_ralnex p_alinexa f0_ralnex f1_ralnex f2_ralnex a_df-rex f1_ralnex a_sup_set_class f2_ralnex a_wcel f0_ralnex a_wn a_wi f1_ralnex a_wal f1_ralnex a_sup_set_class f2_ralnex a_wcel f0_ralnex a_wa f1_ralnex a_wex f0_ralnex f1_ralnex f2_ralnex a_wrex p_xchbinxr f0_ralnex a_wn f1_ralnex f2_ralnex a_wral f1_ralnex a_sup_set_class f2_ralnex a_wcel f0_ralnex a_wn a_wi f1_ralnex a_wal f0_ralnex f1_ralnex f2_ralnex a_wrex a_wn p_bitri $.
$}

$(Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)

${
	$v ph x A  $.
	f0_rexnal $f wff ph $.
	f1_rexnal $f set x $.
	f2_rexnal $f class A $.
	p_rexnal $p |- ( E. x e. A -. ph <-> -. A. x e. A ph ) $= f0_rexnal a_wn f1_rexnal f2_rexnal a_df-rex f1_rexnal a_sup_set_class f2_rexnal a_wcel f0_rexnal f1_rexnal p_exanali f0_rexnal f1_rexnal f2_rexnal a_df-ral f1_rexnal a_sup_set_class f2_rexnal a_wcel f0_rexnal a_wn a_wa f1_rexnal a_wex f1_rexnal a_sup_set_class f2_rexnal a_wcel f0_rexnal a_wi f1_rexnal a_wal f0_rexnal f1_rexnal f2_rexnal a_wral p_xchbinxr f0_rexnal a_wn f1_rexnal f2_rexnal a_wrex f1_rexnal a_sup_set_class f2_rexnal a_wcel f0_rexnal a_wn a_wa f1_rexnal a_wex f0_rexnal f1_rexnal f2_rexnal a_wral a_wn p_bitri $.
$}

$(Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)

${
	$v ph x A  $.
	f0_dfral2 $f wff ph $.
	f1_dfral2 $f set x $.
	f2_dfral2 $f class A $.
	p_dfral2 $p |- ( A. x e. A ph <-> -. E. x e. A -. ph ) $= f0_dfral2 f1_dfral2 f2_dfral2 p_rexnal f0_dfral2 a_wn f1_dfral2 f2_dfral2 a_wrex f0_dfral2 f1_dfral2 f2_dfral2 a_wral p_con2bii $.
$}

$(Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)

${
	$v ph x A  $.
	f0_dfrex2 $f wff ph $.
	f1_dfrex2 $f set x $.
	f2_dfrex2 $f class A $.
	p_dfrex2 $p |- ( E. x e. A ph <-> -. A. x e. A -. ph ) $= f0_dfrex2 f1_dfrex2 f2_dfrex2 p_ralnex f0_dfrex2 a_wn f1_dfrex2 f2_dfrex2 a_wral f0_dfrex2 f1_dfrex2 f2_dfrex2 a_wrex p_con2bii $.
$}

$(Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 6-Oct-2003.) $)

${
	$v ph ps ch x A  $.
	f0_ralbida $f wff ph $.
	f1_ralbida $f wff ps $.
	f2_ralbida $f wff ch $.
	f3_ralbida $f set x $.
	f4_ralbida $f class A $.
	e0_ralbida $e |- F/ x ph $.
	e1_ralbida $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_ralbida $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $= e0_ralbida e1_ralbida f0_ralbida f3_ralbida a_sup_set_class f4_ralbida a_wcel f1_ralbida f2_ralbida p_pm5.74da f0_ralbida f3_ralbida a_sup_set_class f4_ralbida a_wcel f1_ralbida a_wi f3_ralbida a_sup_set_class f4_ralbida a_wcel f2_ralbida a_wi f3_ralbida p_albid f1_ralbida f3_ralbida f4_ralbida a_df-ral f2_ralbida f3_ralbida f4_ralbida a_df-ral f0_ralbida f3_ralbida a_sup_set_class f4_ralbida a_wcel f1_ralbida a_wi f3_ralbida a_wal f3_ralbida a_sup_set_class f4_ralbida a_wcel f2_ralbida a_wi f3_ralbida a_wal f1_ralbida f3_ralbida f4_ralbida a_wral f2_ralbida f3_ralbida f4_ralbida a_wral p_3bitr4g $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 6-Oct-2003.) $)

${
	$v ph ps ch x A  $.
	f0_rexbida $f wff ph $.
	f1_rexbida $f wff ps $.
	f2_rexbida $f wff ch $.
	f3_rexbida $f set x $.
	f4_rexbida $f class A $.
	e0_rexbida $e |- F/ x ph $.
	e1_rexbida $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_rexbida $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $= e0_rexbida e1_rexbida f0_rexbida f3_rexbida a_sup_set_class f4_rexbida a_wcel f1_rexbida f2_rexbida p_pm5.32da f0_rexbida f3_rexbida a_sup_set_class f4_rexbida a_wcel f1_rexbida a_wa f3_rexbida a_sup_set_class f4_rexbida a_wcel f2_rexbida a_wa f3_rexbida p_exbid f1_rexbida f3_rexbida f4_rexbida a_df-rex f2_rexbida f3_rexbida f4_rexbida a_df-rex f0_rexbida f3_rexbida a_sup_set_class f4_rexbida a_wcel f1_rexbida a_wa f3_rexbida a_wex f3_rexbida a_sup_set_class f4_rexbida a_wcel f2_rexbida a_wa f3_rexbida a_wex f1_rexbida f3_rexbida f4_rexbida a_wrex f2_rexbida f3_rexbida f4_rexbida a_wrex p_3bitr4g $.
$}

$(Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 4-Mar-1997.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_ralbidva $f wff ph $.
	f1_ralbidva $f wff ps $.
	f2_ralbidva $f wff ch $.
	f3_ralbidva $f set x $.
	f4_ralbidva $f class A $.
	e0_ralbidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_ralbidva $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $= f0_ralbidva f3_ralbidva p_nfv e0_ralbidva f0_ralbidva f1_ralbidva f2_ralbidva f3_ralbidva f4_ralbidva p_ralbida $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 9-Mar-1997.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_rexbidva $f wff ph $.
	f1_rexbidva $f wff ps $.
	f2_rexbidva $f wff ch $.
	f3_rexbidva $f set x $.
	f4_rexbidva $f class A $.
	e0_rexbidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_rexbidva $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $= f0_rexbidva f3_rexbidva p_nfv e0_rexbidva f0_rexbidva f1_rexbidva f2_rexbidva f3_rexbidva f4_rexbidva p_rexbida $.
$}

$(Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 27-Jun-1998.) $)

${
	$v ph ps ch x A  $.
	f0_ralbid $f wff ph $.
	f1_ralbid $f wff ps $.
	f2_ralbid $f wff ch $.
	f3_ralbid $f set x $.
	f4_ralbid $f class A $.
	e0_ralbid $e |- F/ x ph $.
	e1_ralbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_ralbid $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $= e0_ralbid e1_ralbid f0_ralbid f1_ralbid f2_ralbid a_wb f3_ralbid a_sup_set_class f4_ralbid a_wcel p_adantr f0_ralbid f1_ralbid f2_ralbid f3_ralbid f4_ralbid p_ralbida $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 27-Jun-1998.) $)

${
	$v ph ps ch x A  $.
	f0_rexbid $f wff ph $.
	f1_rexbid $f wff ps $.
	f2_rexbid $f wff ch $.
	f3_rexbid $f set x $.
	f4_rexbid $f class A $.
	e0_rexbid $e |- F/ x ph $.
	e1_rexbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_rexbid $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $= e0_rexbid e1_rexbid f0_rexbid f1_rexbid f2_rexbid a_wb f3_rexbid a_sup_set_class f4_rexbid a_wcel p_adantr f0_rexbid f1_rexbid f2_rexbid f3_rexbid f4_rexbid p_rexbida $.
$}

$(Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 20-Nov-1994.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_ralbidv $f wff ph $.
	f1_ralbidv $f wff ps $.
	f2_ralbidv $f wff ch $.
	f3_ralbidv $f set x $.
	f4_ralbidv $f class A $.
	e0_ralbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_ralbidv $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $= f0_ralbidv f3_ralbidv p_nfv e0_ralbidv f0_ralbidv f1_ralbidv f2_ralbidv f3_ralbidv f4_ralbidv p_ralbid $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 20-Nov-1994.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_rexbidv $f wff ph $.
	f1_rexbidv $f wff ps $.
	f2_rexbidv $f wff ch $.
	f3_rexbidv $f set x $.
	f4_rexbidv $f class A $.
	e0_rexbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_rexbidv $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $= f0_rexbidv f3_rexbidv p_nfv e0_rexbidv f0_rexbidv f1_rexbidv f2_rexbidv f3_rexbidv f4_rexbidv p_rexbid $.
$}

$(Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 6-Apr-1997.) $)

${
	$v ph ps ch x A B  $.
	$d x ph  $.
	f0_ralbidv2 $f wff ph $.
	f1_ralbidv2 $f wff ps $.
	f2_ralbidv2 $f wff ch $.
	f3_ralbidv2 $f set x $.
	f4_ralbidv2 $f class A $.
	f5_ralbidv2 $f class B $.
	e0_ralbidv2 $e |- ( ph -> ( ( x e. A -> ps ) <-> ( x e. B -> ch ) ) ) $.
	p_ralbidv2 $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $= e0_ralbidv2 f0_ralbidv2 f3_ralbidv2 a_sup_set_class f4_ralbidv2 a_wcel f1_ralbidv2 a_wi f3_ralbidv2 a_sup_set_class f5_ralbidv2 a_wcel f2_ralbidv2 a_wi f3_ralbidv2 p_albidv f1_ralbidv2 f3_ralbidv2 f4_ralbidv2 a_df-ral f2_ralbidv2 f3_ralbidv2 f5_ralbidv2 a_df-ral f0_ralbidv2 f3_ralbidv2 a_sup_set_class f4_ralbidv2 a_wcel f1_ralbidv2 a_wi f3_ralbidv2 a_wal f3_ralbidv2 a_sup_set_class f5_ralbidv2 a_wcel f2_ralbidv2 a_wi f3_ralbidv2 a_wal f1_ralbidv2 f3_ralbidv2 f4_ralbidv2 a_wral f2_ralbidv2 f3_ralbidv2 f5_ralbidv2 a_wral p_3bitr4g $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 22-May-1999.) $)

${
	$v ph ps ch x A B  $.
	$d x ph  $.
	f0_rexbidv2 $f wff ph $.
	f1_rexbidv2 $f wff ps $.
	f2_rexbidv2 $f wff ch $.
	f3_rexbidv2 $f set x $.
	f4_rexbidv2 $f class A $.
	f5_rexbidv2 $f class B $.
	e0_rexbidv2 $e |- ( ph -> ( ( x e. A /\ ps ) <-> ( x e. B /\ ch ) ) ) $.
	p_rexbidv2 $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $= e0_rexbidv2 f0_rexbidv2 f3_rexbidv2 a_sup_set_class f4_rexbidv2 a_wcel f1_rexbidv2 a_wa f3_rexbidv2 a_sup_set_class f5_rexbidv2 a_wcel f2_rexbidv2 a_wa f3_rexbidv2 p_exbidv f1_rexbidv2 f3_rexbidv2 f4_rexbidv2 a_df-rex f2_rexbidv2 f3_rexbidv2 f5_rexbidv2 a_df-rex f0_rexbidv2 f3_rexbidv2 a_sup_set_class f4_rexbidv2 a_wcel f1_rexbidv2 a_wa f3_rexbidv2 a_wex f3_rexbidv2 a_sup_set_class f5_rexbidv2 a_wcel f2_rexbidv2 a_wa f3_rexbidv2 a_wex f1_rexbidv2 f3_rexbidv2 f4_rexbidv2 a_wrex f2_rexbidv2 f3_rexbidv2 f5_rexbidv2 a_wrex p_3bitr4g $.
$}

$(Inference adding restricted universal quantifier to both sides of an
       equivalence.  (Contributed by NM, 23-Nov-1994.)  (Revised by Mario
       Carneiro, 17-Oct-2016.) $)

${
	$v ph ps x A  $.
	f0_ralbii $f wff ph $.
	f1_ralbii $f wff ps $.
	f2_ralbii $f set x $.
	f3_ralbii $f class A $.
	e0_ralbii $e |- ( ph <-> ps ) $.
	p_ralbii $p |- ( A. x e. A ph <-> A. x e. A ps ) $= e0_ralbii f0_ralbii f1_ralbii a_wb a_wtru p_a1i a_wtru f0_ralbii f1_ralbii f2_ralbii f3_ralbii p_ralbidv f0_ralbii f2_ralbii f3_ralbii a_wral f1_ralbii f2_ralbii f3_ralbii a_wral a_wb p_trud $.
$}

$(Inference adding restricted existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 23-Nov-1994.)  (Revised by Mario
       Carneiro, 17-Oct-2016.) $)

${
	$v ph ps x A  $.
	f0_rexbii $f wff ph $.
	f1_rexbii $f wff ps $.
	f2_rexbii $f set x $.
	f3_rexbii $f class A $.
	e0_rexbii $e |- ( ph <-> ps ) $.
	p_rexbii $p |- ( E. x e. A ph <-> E. x e. A ps ) $= e0_rexbii f0_rexbii f1_rexbii a_wb a_wtru p_a1i a_wtru f0_rexbii f1_rexbii f2_rexbii f3_rexbii p_rexbidv f0_rexbii f2_rexbii f3_rexbii a_wrex f1_rexbii f2_rexbii f3_rexbii a_wrex a_wb p_trud $.
$}

$(Inference adding two restricted universal quantifiers to both sides of
       an equivalence.  (Contributed by NM, 1-Aug-2004.) $)

${
	$v ph ps x y A B  $.
	f0_2ralbii $f wff ph $.
	f1_2ralbii $f wff ps $.
	f2_2ralbii $f set x $.
	f3_2ralbii $f set y $.
	f4_2ralbii $f class A $.
	f5_2ralbii $f class B $.
	e0_2ralbii $e |- ( ph <-> ps ) $.
	p_2ralbii $p |- ( A. x e. A A. y e. B ph <-> A. x e. A A. y e. B ps ) $= e0_2ralbii f0_2ralbii f1_2ralbii f3_2ralbii f5_2ralbii p_ralbii f0_2ralbii f3_2ralbii f5_2ralbii a_wral f1_2ralbii f3_2ralbii f5_2ralbii a_wral f2_2ralbii f4_2ralbii p_ralbii $.
$}

$(Inference adding two restricted existential quantifiers to both sides of
       an equivalence.  (Contributed by NM, 11-Nov-1995.) $)

${
	$v ph ps x y A B  $.
	f0_2rexbii $f wff ph $.
	f1_2rexbii $f wff ps $.
	f2_2rexbii $f set x $.
	f3_2rexbii $f set y $.
	f4_2rexbii $f class A $.
	f5_2rexbii $f class B $.
	e0_2rexbii $e |- ( ph <-> ps ) $.
	p_2rexbii $p |- ( E. x e. A E. y e. B ph <-> E. x e. A E. y e. B ps ) $= e0_2rexbii f0_2rexbii f1_2rexbii f3_2rexbii f5_2rexbii p_rexbii f0_2rexbii f3_2rexbii f5_2rexbii a_wrex f1_2rexbii f3_2rexbii f5_2rexbii a_wrex f2_2rexbii f4_2rexbii p_rexbii $.
$}

$(Inference adding different restricted universal quantifiers to each side
       of an equivalence.  (Contributed by NM, 15-Aug-2005.) $)

${
	$v ph ps x A B  $.
	f0_ralbii2 $f wff ph $.
	f1_ralbii2 $f wff ps $.
	f2_ralbii2 $f set x $.
	f3_ralbii2 $f class A $.
	f4_ralbii2 $f class B $.
	e0_ralbii2 $e |- ( ( x e. A -> ph ) <-> ( x e. B -> ps ) ) $.
	p_ralbii2 $p |- ( A. x e. A ph <-> A. x e. B ps ) $= e0_ralbii2 f2_ralbii2 a_sup_set_class f3_ralbii2 a_wcel f0_ralbii2 a_wi f2_ralbii2 a_sup_set_class f4_ralbii2 a_wcel f1_ralbii2 a_wi f2_ralbii2 p_albii f0_ralbii2 f2_ralbii2 f3_ralbii2 a_df-ral f1_ralbii2 f2_ralbii2 f4_ralbii2 a_df-ral f2_ralbii2 a_sup_set_class f3_ralbii2 a_wcel f0_ralbii2 a_wi f2_ralbii2 a_wal f2_ralbii2 a_sup_set_class f4_ralbii2 a_wcel f1_ralbii2 a_wi f2_ralbii2 a_wal f0_ralbii2 f2_ralbii2 f3_ralbii2 a_wral f1_ralbii2 f2_ralbii2 f4_ralbii2 a_wral p_3bitr4i $.
$}

$(Inference adding different restricted existential quantifiers to each
       side of an equivalence.  (Contributed by NM, 4-Feb-2004.) $)

${
	$v ph ps x A B  $.
	f0_rexbii2 $f wff ph $.
	f1_rexbii2 $f wff ps $.
	f2_rexbii2 $f set x $.
	f3_rexbii2 $f class A $.
	f4_rexbii2 $f class B $.
	e0_rexbii2 $e |- ( ( x e. A /\ ph ) <-> ( x e. B /\ ps ) ) $.
	p_rexbii2 $p |- ( E. x e. A ph <-> E. x e. B ps ) $= e0_rexbii2 f2_rexbii2 a_sup_set_class f3_rexbii2 a_wcel f0_rexbii2 a_wa f2_rexbii2 a_sup_set_class f4_rexbii2 a_wcel f1_rexbii2 a_wa f2_rexbii2 p_exbii f0_rexbii2 f2_rexbii2 f3_rexbii2 a_df-rex f1_rexbii2 f2_rexbii2 f4_rexbii2 a_df-rex f2_rexbii2 a_sup_set_class f3_rexbii2 a_wcel f0_rexbii2 a_wa f2_rexbii2 a_wex f2_rexbii2 a_sup_set_class f4_rexbii2 a_wcel f1_rexbii2 a_wa f2_rexbii2 a_wex f0_rexbii2 f2_rexbii2 f3_rexbii2 a_wrex f1_rexbii2 f2_rexbii2 f4_rexbii2 a_wrex p_3bitr4i $.
$}

$(Equality deduction for restricted universal quantifier, changing both
       formula and quantifier domain.  Inference form.  (Contributed by David
       Moews, 1-May-2017.) $)

${
	$v ps ch x A B  $.
	f0_raleqbii $f wff ps $.
	f1_raleqbii $f wff ch $.
	f2_raleqbii $f set x $.
	f3_raleqbii $f class A $.
	f4_raleqbii $f class B $.
	e0_raleqbii $e |- A = B $.
	e1_raleqbii $e |- ( ps <-> ch ) $.
	p_raleqbii $p |- ( A. x e. A ps <-> A. x e. B ch ) $= e0_raleqbii f3_raleqbii f4_raleqbii f2_raleqbii a_sup_set_class p_eleq2i e1_raleqbii f2_raleqbii a_sup_set_class f3_raleqbii a_wcel f2_raleqbii a_sup_set_class f4_raleqbii a_wcel f0_raleqbii f1_raleqbii p_imbi12i f0_raleqbii f1_raleqbii f2_raleqbii f3_raleqbii f4_raleqbii p_ralbii2 $.
$}

$(Equality deduction for restricted existential quantifier, changing both
       formula and quantifier domain.  Inference form.  (Contributed by David
       Moews, 1-May-2017.) $)

${
	$v ps ch x A B  $.
	f0_rexeqbii $f wff ps $.
	f1_rexeqbii $f wff ch $.
	f2_rexeqbii $f set x $.
	f3_rexeqbii $f class A $.
	f4_rexeqbii $f class B $.
	e0_rexeqbii $e |- A = B $.
	e1_rexeqbii $e |- ( ps <-> ch ) $.
	p_rexeqbii $p |- ( E. x e. A ps <-> E. x e. B ch ) $= e0_rexeqbii f3_rexeqbii f4_rexeqbii f2_rexeqbii a_sup_set_class p_eleq2i e1_rexeqbii f2_rexeqbii a_sup_set_class f3_rexeqbii a_wcel f2_rexeqbii a_sup_set_class f4_rexeqbii a_wcel f0_rexeqbii f1_rexeqbii p_anbi12i f0_rexeqbii f1_rexeqbii f2_rexeqbii f3_rexeqbii f4_rexeqbii p_rexbii2 $.
$}

$(Inference adding restricted universal quantifier to both sides of an
       equivalence.  (Contributed by NM, 26-Nov-2000.) $)

${
	$v ph ps x A  $.
	f0_ralbiia $f wff ph $.
	f1_ralbiia $f wff ps $.
	f2_ralbiia $f set x $.
	f3_ralbiia $f class A $.
	e0_ralbiia $e |- ( x e. A -> ( ph <-> ps ) ) $.
	p_ralbiia $p |- ( A. x e. A ph <-> A. x e. A ps ) $= e0_ralbiia f2_ralbiia a_sup_set_class f3_ralbiia a_wcel f0_ralbiia f1_ralbiia p_pm5.74i f0_ralbiia f1_ralbiia f2_ralbiia f3_ralbiia f3_ralbiia p_ralbii2 $.
$}

$(Inference adding restricted existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 26-Oct-1999.) $)

${
	$v ph ps x A  $.
	f0_rexbiia $f wff ph $.
	f1_rexbiia $f wff ps $.
	f2_rexbiia $f set x $.
	f3_rexbiia $f class A $.
	e0_rexbiia $e |- ( x e. A -> ( ph <-> ps ) ) $.
	p_rexbiia $p |- ( E. x e. A ph <-> E. x e. A ps ) $= e0_rexbiia f2_rexbiia a_sup_set_class f3_rexbiia a_wcel f0_rexbiia f1_rexbiia p_pm5.32i f0_rexbiia f1_rexbiia f2_rexbiia f3_rexbiia f3_rexbiia p_rexbii2 $.
$}

$(Inference adding two restricted existential quantifiers to both sides of
       an equivalence.  (Contributed by NM, 1-Aug-2004.) $)

${
	$v ph ps x y A B  $.
	$d x y  $.
	$d y A  $.
	f0_2rexbiia $f wff ph $.
	f1_2rexbiia $f wff ps $.
	f2_2rexbiia $f set x $.
	f3_2rexbiia $f set y $.
	f4_2rexbiia $f class A $.
	f5_2rexbiia $f class B $.
	e0_2rexbiia $e |- ( ( x e. A /\ y e. B ) -> ( ph <-> ps ) ) $.
	p_2rexbiia $p |- ( E. x e. A E. y e. B ph <-> E. x e. A E. y e. B ps ) $= e0_2rexbiia f2_2rexbiia a_sup_set_class f4_2rexbiia a_wcel f0_2rexbiia f1_2rexbiia f3_2rexbiia f5_2rexbiia p_rexbidva f0_2rexbiia f3_2rexbiia f5_2rexbiia a_wrex f1_2rexbiia f3_2rexbiia f5_2rexbiia a_wrex f2_2rexbiia f4_2rexbiia p_rexbiia $.
$}

$(Double restricted universal quantification.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	f0_r2alf $f wff ph $.
	f1_r2alf $f set x $.
	f2_r2alf $f set y $.
	f3_r2alf $f class A $.
	f4_r2alf $f class B $.
	e0_r2alf $e |- F/_ y A $.
	p_r2alf $p |- ( A. x e. A A. y e. B ph <-> A. x A. y ( ( x e. A /\ y e. B ) -> ph ) ) $= f0_r2alf f2_r2alf f4_r2alf a_wral f1_r2alf f3_r2alf a_df-ral e0_r2alf f2_r2alf f1_r2alf f3_r2alf p_nfcri f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel f0_r2alf a_wi f2_r2alf p_19.21 f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel f0_r2alf p_impexp f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel a_wa f0_r2alf a_wi f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel f0_r2alf a_wi a_wi f2_r2alf p_albii f0_r2alf f2_r2alf f4_r2alf a_df-ral f0_r2alf f2_r2alf f4_r2alf a_wral f2_r2alf a_sup_set_class f4_r2alf a_wcel f0_r2alf a_wi f2_r2alf a_wal f1_r2alf a_sup_set_class f3_r2alf a_wcel p_imbi2i f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel f0_r2alf a_wi a_wi f2_r2alf a_wal f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel f0_r2alf a_wi f2_r2alf a_wal a_wi f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel a_wa f0_r2alf a_wi f2_r2alf a_wal f1_r2alf a_sup_set_class f3_r2alf a_wcel f0_r2alf f2_r2alf f4_r2alf a_wral a_wi p_3bitr4i f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel a_wa f0_r2alf a_wi f2_r2alf a_wal f1_r2alf a_sup_set_class f3_r2alf a_wcel f0_r2alf f2_r2alf f4_r2alf a_wral a_wi f1_r2alf p_albii f0_r2alf f2_r2alf f4_r2alf a_wral f1_r2alf f3_r2alf a_wral f1_r2alf a_sup_set_class f3_r2alf a_wcel f0_r2alf f2_r2alf f4_r2alf a_wral a_wi f1_r2alf a_wal f1_r2alf a_sup_set_class f3_r2alf a_wcel f2_r2alf a_sup_set_class f4_r2alf a_wcel a_wa f0_r2alf a_wi f2_r2alf a_wal f1_r2alf a_wal p_bitr4i $.
$}

$(Double restricted existential quantification.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	f0_r2exf $f wff ph $.
	f1_r2exf $f set x $.
	f2_r2exf $f set y $.
	f3_r2exf $f class A $.
	f4_r2exf $f class B $.
	e0_r2exf $e |- F/_ y A $.
	p_r2exf $p |- ( E. x e. A E. y e. B ph <-> E. x E. y ( ( x e. A /\ y e. B ) /\ ph ) ) $= f0_r2exf f2_r2exf f4_r2exf a_wrex f1_r2exf f3_r2exf a_df-rex e0_r2exf f2_r2exf f1_r2exf f3_r2exf p_nfcri f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel f0_r2exf a_wa f2_r2exf p_19.42 f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel f0_r2exf p_anass f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel a_wa f0_r2exf a_wa f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel f0_r2exf a_wa a_wa f2_r2exf p_exbii f0_r2exf f2_r2exf f4_r2exf a_df-rex f0_r2exf f2_r2exf f4_r2exf a_wrex f2_r2exf a_sup_set_class f4_r2exf a_wcel f0_r2exf a_wa f2_r2exf a_wex f1_r2exf a_sup_set_class f3_r2exf a_wcel p_anbi2i f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel f0_r2exf a_wa a_wa f2_r2exf a_wex f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel f0_r2exf a_wa f2_r2exf a_wex a_wa f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel a_wa f0_r2exf a_wa f2_r2exf a_wex f1_r2exf a_sup_set_class f3_r2exf a_wcel f0_r2exf f2_r2exf f4_r2exf a_wrex a_wa p_3bitr4i f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel a_wa f0_r2exf a_wa f2_r2exf a_wex f1_r2exf a_sup_set_class f3_r2exf a_wcel f0_r2exf f2_r2exf f4_r2exf a_wrex a_wa f1_r2exf p_exbii f0_r2exf f2_r2exf f4_r2exf a_wrex f1_r2exf f3_r2exf a_wrex f1_r2exf a_sup_set_class f3_r2exf a_wcel f0_r2exf f2_r2exf f4_r2exf a_wrex a_wa f1_r2exf a_wex f1_r2exf a_sup_set_class f3_r2exf a_wcel f2_r2exf a_sup_set_class f4_r2exf a_wcel a_wa f0_r2exf a_wa f2_r2exf a_wex f1_r2exf a_wex p_bitr4i $.
$}

$(Double restricted universal quantification.  (Contributed by NM,
       19-Nov-1995.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	$d y A  $.
	f0_r2al $f wff ph $.
	f1_r2al $f set x $.
	f2_r2al $f set y $.
	f3_r2al $f class A $.
	f4_r2al $f class B $.
	p_r2al $p |- ( A. x e. A A. y e. B ph <-> A. x A. y ( ( x e. A /\ y e. B ) -> ph ) ) $= f2_r2al f3_r2al p_nfcv f0_r2al f1_r2al f2_r2al f3_r2al f4_r2al p_r2alf $.
$}

$(Double restricted existential quantification.  (Contributed by NM,
       11-Nov-1995.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	$d y A  $.
	f0_r2ex $f wff ph $.
	f1_r2ex $f set x $.
	f2_r2ex $f set y $.
	f3_r2ex $f class A $.
	f4_r2ex $f class B $.
	p_r2ex $p |- ( E. x e. A E. y e. B ph <-> E. x E. y ( ( x e. A /\ y e. B ) /\ ph ) ) $= f2_r2ex f3_r2ex p_nfcv f0_r2ex f1_r2ex f2_r2ex f3_r2ex f4_r2ex p_r2exf $.
$}

$(Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 24-Feb-2004.) $)

${
	$v ph ps ch x y A B  $.
	$d x y  $.
	$d y A  $.
	f0_2ralbida $f wff ph $.
	f1_2ralbida $f wff ps $.
	f2_2ralbida $f wff ch $.
	f3_2ralbida $f set x $.
	f4_2ralbida $f set y $.
	f5_2ralbida $f class A $.
	f6_2ralbida $f class B $.
	e0_2ralbida $e |- F/ x ph $.
	e1_2ralbida $e |- F/ y ph $.
	e2_2ralbida $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) ) $.
	p_2ralbida $p |- ( ph -> ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $= e0_2ralbida e1_2ralbida f3_2ralbida a_sup_set_class f5_2ralbida a_wcel f4_2ralbida p_nfv f0_2ralbida f3_2ralbida a_sup_set_class f5_2ralbida a_wcel f4_2ralbida p_nfan e2_2ralbida f0_2ralbida f3_2ralbida a_sup_set_class f5_2ralbida a_wcel f4_2ralbida a_sup_set_class f6_2ralbida a_wcel f1_2ralbida f2_2ralbida a_wb p_anassrs f0_2ralbida f3_2ralbida a_sup_set_class f5_2ralbida a_wcel a_wa f1_2ralbida f2_2ralbida f4_2ralbida f6_2ralbida p_ralbida f0_2ralbida f1_2ralbida f4_2ralbida f6_2ralbida a_wral f2_2ralbida f4_2ralbida f6_2ralbida a_wral f3_2ralbida f5_2ralbida p_ralbida $.
$}

$(Formula-building rule for restricted universal quantifiers (deduction
       rule).  (Contributed by NM, 4-Mar-1997.) $)

${
	$v ph ps ch x y A B  $.
	$d x y ph  $.
	$d y A  $.
	f0_2ralbidva $f wff ph $.
	f1_2ralbidva $f wff ps $.
	f2_2ralbidva $f wff ch $.
	f3_2ralbidva $f set x $.
	f4_2ralbidva $f set y $.
	f5_2ralbidva $f class A $.
	f6_2ralbidva $f class B $.
	e0_2ralbidva $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) ) $.
	p_2ralbidva $p |- ( ph -> ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $= f0_2ralbidva f3_2ralbidva p_nfv f0_2ralbidva f4_2ralbidva p_nfv e0_2ralbidva f0_2ralbidva f1_2ralbidva f2_2ralbidva f3_2ralbidva f4_2ralbidva f5_2ralbidva f6_2ralbidva p_2ralbida $.
$}

$(Formula-building rule for restricted existential quantifiers (deduction
       rule).  (Contributed by NM, 15-Dec-2004.) $)

${
	$v ph ps ch x y A B  $.
	$d x y ph  $.
	$d y A  $.
	f0_2rexbidva $f wff ph $.
	f1_2rexbidva $f wff ps $.
	f2_2rexbidva $f wff ch $.
	f3_2rexbidva $f set x $.
	f4_2rexbidva $f set y $.
	f5_2rexbidva $f class A $.
	f6_2rexbidva $f class B $.
	e0_2rexbidva $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) ) $.
	p_2rexbidva $p |- ( ph -> ( E. x e. A E. y e. B ps <-> E. x e. A E. y e. B ch ) ) $= e0_2rexbidva f0_2rexbidva f3_2rexbidva a_sup_set_class f5_2rexbidva a_wcel f4_2rexbidva a_sup_set_class f6_2rexbidva a_wcel f1_2rexbidva f2_2rexbidva a_wb p_anassrs f0_2rexbidva f3_2rexbidva a_sup_set_class f5_2rexbidva a_wcel a_wa f1_2rexbidva f2_2rexbidva f4_2rexbidva f6_2rexbidva p_rexbidva f0_2rexbidva f1_2rexbidva f4_2rexbidva f6_2rexbidva a_wrex f2_2rexbidva f4_2rexbidva f6_2rexbidva a_wrex f3_2rexbidva f5_2rexbidva p_rexbidva $.
$}

$(Formula-building rule for restricted universal quantifiers (deduction
       rule).  (Contributed by NM, 28-Jan-2006.)  (Revised by Szymon
       Jaroszewicz, 16-Mar-2007.) $)

${
	$v ph ps ch x y A B  $.
	$d x ph  $.
	$d y ph  $.
	f0_2ralbidv $f wff ph $.
	f1_2ralbidv $f wff ps $.
	f2_2ralbidv $f wff ch $.
	f3_2ralbidv $f set x $.
	f4_2ralbidv $f set y $.
	f5_2ralbidv $f class A $.
	f6_2ralbidv $f class B $.
	e0_2ralbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_2ralbidv $p |- ( ph -> ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $= e0_2ralbidv f0_2ralbidv f1_2ralbidv f2_2ralbidv f4_2ralbidv f6_2ralbidv p_ralbidv f0_2ralbidv f1_2ralbidv f4_2ralbidv f6_2ralbidv a_wral f2_2ralbidv f4_2ralbidv f6_2ralbidv a_wral f3_2ralbidv f5_2ralbidv p_ralbidv $.
$}

$(Formula-building rule for restricted existential quantifiers (deduction
       rule).  (Contributed by NM, 28-Jan-2006.) $)

${
	$v ph ps ch x y A B  $.
	$d x ph  $.
	$d y ph  $.
	f0_2rexbidv $f wff ph $.
	f1_2rexbidv $f wff ps $.
	f2_2rexbidv $f wff ch $.
	f3_2rexbidv $f set x $.
	f4_2rexbidv $f set y $.
	f5_2rexbidv $f class A $.
	f6_2rexbidv $f class B $.
	e0_2rexbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_2rexbidv $p |- ( ph -> ( E. x e. A E. y e. B ps <-> E. x e. A E. y e. B ch ) ) $= e0_2rexbidv f0_2rexbidv f1_2rexbidv f2_2rexbidv f4_2rexbidv f6_2rexbidv p_rexbidv f0_2rexbidv f1_2rexbidv f4_2rexbidv f6_2rexbidv a_wrex f2_2rexbidv f4_2rexbidv f6_2rexbidv a_wrex f3_2rexbidv f5_2rexbidv p_rexbidv $.
$}

$(Formula-building rule for restricted quantifiers (deduction rule).
       (Contributed by NM, 28-Jan-2006.) $)

${
	$v ph ps ch x y A B  $.
	$d x ph  $.
	$d y ph  $.
	f0_rexralbidv $f wff ph $.
	f1_rexralbidv $f wff ps $.
	f2_rexralbidv $f wff ch $.
	f3_rexralbidv $f set x $.
	f4_rexralbidv $f set y $.
	f5_rexralbidv $f class A $.
	f6_rexralbidv $f class B $.
	e0_rexralbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_rexralbidv $p |- ( ph -> ( E. x e. A A. y e. B ps <-> E. x e. A A. y e. B ch ) ) $= e0_rexralbidv f0_rexralbidv f1_rexralbidv f2_rexralbidv f4_rexralbidv f6_rexralbidv p_ralbidv f0_rexralbidv f1_rexralbidv f4_rexralbidv f6_rexralbidv a_wral f2_rexralbidv f4_rexralbidv f6_rexralbidv a_wral f3_rexralbidv f5_rexralbidv p_rexbidv $.
$}

$(A transformation of restricted quantifiers and logical connectives.
     (Contributed by NM, 4-Sep-2005.) $)

${
	$v ph ps x A  $.
	f0_ralinexa $f wff ph $.
	f1_ralinexa $f wff ps $.
	f2_ralinexa $f set x $.
	f3_ralinexa $f class A $.
	p_ralinexa $p |- ( A. x e. A ( ph -> -. ps ) <-> -. E. x e. A ( ph /\ ps ) ) $= f0_ralinexa f1_ralinexa p_imnan f0_ralinexa f1_ralinexa a_wn a_wi f0_ralinexa f1_ralinexa a_wa a_wn f2_ralinexa f3_ralinexa p_ralbii f0_ralinexa f1_ralinexa a_wa f2_ralinexa f3_ralinexa p_ralnex f0_ralinexa f1_ralinexa a_wn a_wi f2_ralinexa f3_ralinexa a_wral f0_ralinexa f1_ralinexa a_wa a_wn f2_ralinexa f3_ralinexa a_wral f0_ralinexa f1_ralinexa a_wa f2_ralinexa f3_ralinexa a_wrex a_wn p_bitri $.
$}

$(A transformation of restricted quantifiers and logical connectives.
     (Contributed by NM, 4-Sep-2005.) $)

${
	$v ph ps x A  $.
	f0_rexanali $f wff ph $.
	f1_rexanali $f wff ps $.
	f2_rexanali $f set x $.
	f3_rexanali $f class A $.
	p_rexanali $p |- ( E. x e. A ( ph /\ -. ps ) <-> -. A. x e. A ( ph -> ps ) ) $= f0_rexanali f1_rexanali p_annim f0_rexanali f1_rexanali a_wn a_wa f0_rexanali f1_rexanali a_wi a_wn f2_rexanali f3_rexanali p_rexbii f0_rexanali f1_rexanali a_wi f2_rexanali f3_rexanali p_rexnal f0_rexanali f1_rexanali a_wn a_wa f2_rexanali f3_rexanali a_wrex f0_rexanali f1_rexanali a_wi a_wn f2_rexanali f3_rexanali a_wrex f0_rexanali f1_rexanali a_wi f2_rexanali f3_rexanali a_wral a_wn p_bitri $.
$}

$(Two ways to say " ` A ` belongs to ` B ` ."  (Contributed by NM,
       22-Nov-1994.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_risset $f set x $.
	f1_risset $f class A $.
	f2_risset $f class B $.
	p_risset $p |- ( A e. B <-> E. x e. B x = A ) $= f0_risset a_sup_set_class f2_risset a_wcel f0_risset a_sup_set_class f1_risset a_wceq f0_risset p_exancom f0_risset a_sup_set_class f1_risset a_wceq f0_risset f2_risset a_df-rex f0_risset f1_risset f2_risset a_df-clel f0_risset a_sup_set_class f2_risset a_wcel f0_risset a_sup_set_class f1_risset a_wceq a_wa f0_risset a_wex f0_risset a_sup_set_class f1_risset a_wceq f0_risset a_sup_set_class f2_risset a_wcel a_wa f0_risset a_wex f0_risset a_sup_set_class f1_risset a_wceq f0_risset f2_risset a_wrex f1_risset f2_risset a_wcel p_3bitr4ri $.
$}

$(Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by David Abernethy,
       13-Dec-2009.) $)

${
	$v ph x y A  $.
	f0_hbral $f wff ph $.
	f1_hbral $f set x $.
	f2_hbral $f set y $.
	f3_hbral $f class A $.
	e0_hbral $e |- ( y e. A -> A. x y e. A ) $.
	e1_hbral $e |- ( ph -> A. x ph ) $.
	p_hbral $p |- ( A. y e. A ph -> A. x A. y e. A ph ) $= f0_hbral f2_hbral f3_hbral a_df-ral e0_hbral e1_hbral f2_hbral a_sup_set_class f3_hbral a_wcel f0_hbral f1_hbral p_hbim f2_hbral a_sup_set_class f3_hbral a_wcel f0_hbral a_wi f1_hbral f2_hbral p_hbal f0_hbral f2_hbral f3_hbral a_wral f2_hbral a_sup_set_class f3_hbral a_wcel f0_hbral a_wi f2_hbral a_wal f1_hbral p_hbxfrbi $.
$}

$(` x ` is not free in ` A. x e. A ph ` .  (Contributed by NM,
     18-Oct-1996.) $)

${
	$v ph x A  $.
	f0_hbra1 $f wff ph $.
	f1_hbra1 $f set x $.
	f2_hbra1 $f class A $.
	p_hbra1 $p |- ( A. x e. A ph -> A. x A. x e. A ph ) $= f0_hbra1 f1_hbra1 f2_hbra1 a_df-ral f1_hbra1 a_sup_set_class f2_hbra1 a_wcel f0_hbra1 a_wi f1_hbra1 p_hba1 f0_hbra1 f1_hbra1 f2_hbra1 a_wral f1_hbra1 a_sup_set_class f2_hbra1 a_wcel f0_hbra1 a_wi f1_hbra1 a_wal f1_hbra1 p_hbxfrbi $.
$}

$(` x ` is not free in ` A. x e. A ph ` .  (Contributed by NM,
     18-Oct-1996.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x A  $.
	f0_nfra1 $f wff ph $.
	f1_nfra1 $f set x $.
	f2_nfra1 $f class A $.
	p_nfra1 $p |- F/ x A. x e. A ph $= f0_nfra1 f1_nfra1 f2_nfra1 a_df-ral f1_nfra1 a_sup_set_class f2_nfra1 a_wcel f0_nfra1 a_wi f1_nfra1 p_nfa1 f0_nfra1 f1_nfra1 f2_nfra1 a_wral f1_nfra1 a_sup_set_class f2_nfra1 a_wcel f0_nfra1 a_wi f1_nfra1 a_wal f1_nfra1 p_nfxfr $.
$}

$(Deduction version of ~ nfral .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph ps x y A  $.
	f0_nfrald $f wff ph $.
	f1_nfrald $f wff ps $.
	f2_nfrald $f set x $.
	f3_nfrald $f set y $.
	f4_nfrald $f class A $.
	e0_nfrald $e |- F/ y ph $.
	e1_nfrald $e |- ( ph -> F/_ x A ) $.
	e2_nfrald $e |- ( ph -> F/ x ps ) $.
	p_nfrald $p |- ( ph -> F/ x A. y e. A ps ) $= f1_nfrald f3_nfrald f4_nfrald a_df-ral e0_nfrald f2_nfrald f3_nfrald p_nfcvf f2_nfrald a_sup_set_class f3_nfrald a_sup_set_class a_wceq f2_nfrald a_wal a_wn f2_nfrald f3_nfrald a_sup_set_class a_wnfc f0_nfrald p_adantl e1_nfrald f0_nfrald f2_nfrald f4_nfrald a_wnfc f2_nfrald a_sup_set_class f3_nfrald a_sup_set_class a_wceq f2_nfrald a_wal a_wn p_adantr f0_nfrald f2_nfrald a_sup_set_class f3_nfrald a_sup_set_class a_wceq f2_nfrald a_wal a_wn a_wa f2_nfrald f3_nfrald a_sup_set_class f4_nfrald p_nfeld e2_nfrald f0_nfrald f1_nfrald f2_nfrald a_wnf f2_nfrald a_sup_set_class f3_nfrald a_sup_set_class a_wceq f2_nfrald a_wal a_wn p_adantr f0_nfrald f2_nfrald a_sup_set_class f3_nfrald a_sup_set_class a_wceq f2_nfrald a_wal a_wn a_wa f3_nfrald a_sup_set_class f4_nfrald a_wcel f1_nfrald f2_nfrald p_nfimd f0_nfrald f3_nfrald a_sup_set_class f4_nfrald a_wcel f1_nfrald a_wi f2_nfrald f3_nfrald p_nfald2 f1_nfrald f3_nfrald f4_nfrald a_wral f3_nfrald a_sup_set_class f4_nfrald a_wcel f1_nfrald a_wi f3_nfrald a_wal f0_nfrald f2_nfrald p_nfxfrd $.
$}

$(Deduction version of ~ nfrex .  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)

${
	$v ph ps x y A  $.
	f0_nfrexd $f wff ph $.
	f1_nfrexd $f wff ps $.
	f2_nfrexd $f set x $.
	f3_nfrexd $f set y $.
	f4_nfrexd $f class A $.
	e0_nfrexd $e |- F/ y ph $.
	e1_nfrexd $e |- ( ph -> F/_ x A ) $.
	e2_nfrexd $e |- ( ph -> F/ x ps ) $.
	p_nfrexd $p |- ( ph -> F/ x E. y e. A ps ) $= f1_nfrexd f3_nfrexd f4_nfrexd p_dfrex2 e0_nfrexd e1_nfrexd e2_nfrexd f0_nfrexd f1_nfrexd f2_nfrexd p_nfnd f0_nfrexd f1_nfrexd a_wn f2_nfrexd f3_nfrexd f4_nfrexd p_nfrald f0_nfrexd f1_nfrexd a_wn f3_nfrexd f4_nfrexd a_wral f2_nfrexd p_nfnd f1_nfrexd f3_nfrexd f4_nfrexd a_wrex f1_nfrexd a_wn f3_nfrexd f4_nfrexd a_wral a_wn f0_nfrexd f2_nfrexd p_nfxfrd $.
$}

$(Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph x y A  $.
	f0_nfral $f wff ph $.
	f1_nfral $f set x $.
	f2_nfral $f set y $.
	f3_nfral $f class A $.
	e0_nfral $e |- F/_ x A $.
	e1_nfral $e |- F/ x ph $.
	p_nfral $p |- F/ x A. y e. A ph $= f2_nfral p_nftru e0_nfral f1_nfral f3_nfral a_wnfc a_wtru p_a1i e1_nfral f0_nfral f1_nfral a_wnf a_wtru p_a1i a_wtru f0_nfral f1_nfral f2_nfral f3_nfral p_nfrald f0_nfral f2_nfral f3_nfral a_wral f1_nfral a_wnf p_trud $.
$}

$(Similar to Lemma 24 of [Monk2] p. 114, except the quantification of the
       antecedent is restricted.  Derived automatically from ~ hbra2VD .
       Contributed by Alan Sare 31-Dec-2011.  (Contributed by NM,
       31-Dec-2011.) $)

${
	$v ph x y A B  $.
	$d A y  $.
	f0_nfra2 $f wff ph $.
	f1_nfra2 $f set x $.
	f2_nfra2 $f set y $.
	f3_nfra2 $f class A $.
	f4_nfra2 $f class B $.
	p_nfra2 $p |- F/ y A. x e. A A. y e. B ph $= f2_nfra2 f3_nfra2 p_nfcv f0_nfra2 f2_nfra2 f4_nfra2 p_nfra1 f0_nfra2 f2_nfra2 f4_nfra2 a_wral f2_nfra2 f1_nfra2 f3_nfra2 p_nfral $.
$}

$(Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph x y A  $.
	f0_nfrex $f wff ph $.
	f1_nfrex $f set x $.
	f2_nfrex $f set y $.
	f3_nfrex $f class A $.
	e0_nfrex $e |- F/_ x A $.
	e1_nfrex $e |- F/ x ph $.
	p_nfrex $p |- F/ x E. y e. A ph $= f0_nfrex f2_nfrex f3_nfrex p_dfrex2 e0_nfrex e1_nfrex f0_nfrex f1_nfrex p_nfn f0_nfrex a_wn f1_nfrex f2_nfrex f3_nfrex p_nfral f0_nfrex a_wn f2_nfrex f3_nfrex a_wral f1_nfrex p_nfn f0_nfrex f2_nfrex f3_nfrex a_wrex f0_nfrex a_wn f2_nfrex f3_nfrex a_wral a_wn f1_nfrex p_nfxfr $.
$}

$(` x ` is not free in ` E. x e. A ph ` .  (Contributed by NM,
     19-Mar-1997.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x A  $.
	f0_nfre1 $f wff ph $.
	f1_nfre1 $f set x $.
	f2_nfre1 $f class A $.
	p_nfre1 $p |- F/ x E. x e. A ph $= f0_nfre1 f1_nfre1 f2_nfre1 a_df-rex f1_nfre1 a_sup_set_class f2_nfre1 a_wcel f0_nfre1 a_wa f1_nfre1 p_nfe1 f0_nfre1 f1_nfre1 f2_nfre1 a_wrex f1_nfre1 a_sup_set_class f2_nfre1 a_wcel f0_nfre1 a_wa f1_nfre1 a_wex f1_nfre1 p_nfxfr $.
$}

$(Triple restricted universal quantification.  (Contributed by NM,
       19-Nov-1995.) $)

${
	$v ph x y z A B C  $.
	$d x y z  $.
	$d y z A  $.
	$d z B  $.
	f0_r3al $f wff ph $.
	f1_r3al $f set x $.
	f2_r3al $f set y $.
	f3_r3al $f set z $.
	f4_r3al $f class A $.
	f5_r3al $f class B $.
	f6_r3al $f class C $.
	p_r3al $p |- ( A. x e. A A. y e. B A. z e. C ph <-> A. x A. y A. z ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) ) $= f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal f1_r3al f4_r3al a_df-ral f0_r3al f2_r3al f3_r3al f5_r3al f6_r3al p_r2al f0_r3al f3_r3al f6_r3al a_wral f2_r3al f5_r3al a_wral f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal f1_r3al f4_r3al p_ralbii f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel p_3anass f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_w3a f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa a_wa f0_r3al p_imbi1i f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al p_impexp f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_w3a f0_r3al a_wi f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa a_wa f0_r3al a_wi f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi a_wi p_bitri f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_w3a f0_r3al a_wi f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi a_wi f3_r3al p_albii f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al p_19.21v f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_w3a f0_r3al a_wi f3_r3al a_wal f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi a_wi f3_r3al a_wal f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal a_wi p_bitri f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_w3a f0_r3al a_wi f3_r3al a_wal f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal a_wi f2_r3al p_albii f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal f2_r3al p_19.21v f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_w3a f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal a_wi f2_r3al a_wal f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal a_wi p_bitri f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_w3a f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal a_wi f1_r3al p_albii f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal f1_r3al f4_r3al a_wral f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_wa f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal a_wi f1_r3al a_wal f0_r3al f3_r3al f6_r3al a_wral f2_r3al f5_r3al a_wral f1_r3al f4_r3al a_wral f1_r3al a_sup_set_class f4_r3al a_wcel f2_r3al a_sup_set_class f5_r3al a_wcel f3_r3al a_sup_set_class f6_r3al a_wcel a_w3a f0_r3al a_wi f3_r3al a_wal f2_r3al a_wal f1_r3al a_wal p_3bitr4i $.
$}

$(Universal quantification implies restricted quantification.  (Contributed
     by NM, 20-Oct-2006.) $)

${
	$v ph x A  $.
	f0_alral $f wff ph $.
	f1_alral $f set x $.
	f2_alral $f class A $.
	p_alral $p |- ( A. x ph -> A. x e. A ph ) $= f0_alral f1_alral a_sup_set_class f2_alral a_wcel a_ax-1 f0_alral f1_alral a_sup_set_class f2_alral a_wcel f0_alral a_wi f1_alral p_alimi f0_alral f1_alral f2_alral a_df-ral f0_alral f1_alral a_wal f1_alral a_sup_set_class f2_alral a_wcel f0_alral a_wi f1_alral a_wal f0_alral f1_alral f2_alral a_wral p_sylibr $.
$}

$(Restricted existence implies existence.  (Contributed by NM,
     11-Nov-1995.) $)

${
	$v ph x A  $.
	f0_rexex $f wff ph $.
	f1_rexex $f set x $.
	f2_rexex $f class A $.
	p_rexex $p |- ( E. x e. A ph -> E. x ph ) $= f0_rexex f1_rexex f2_rexex a_df-rex f1_rexex a_sup_set_class f2_rexex a_wcel f0_rexex p_simpr f1_rexex a_sup_set_class f2_rexex a_wcel f0_rexex a_wa f0_rexex f1_rexex p_eximi f0_rexex f1_rexex f2_rexex a_wrex f1_rexex a_sup_set_class f2_rexex a_wcel f0_rexex a_wa f1_rexex a_wex f0_rexex f1_rexex a_wex p_sylbi $.
$}

$(Restricted specialization.  (Contributed by NM, 17-Oct-1996.) $)

${
	$v ph x A  $.
	f0_rsp $f wff ph $.
	f1_rsp $f set x $.
	f2_rsp $f class A $.
	p_rsp $p |- ( A. x e. A ph -> ( x e. A -> ph ) ) $= f0_rsp f1_rsp f2_rsp a_df-ral f1_rsp a_sup_set_class f2_rsp a_wcel f0_rsp a_wi f1_rsp p_sp f0_rsp f1_rsp f2_rsp a_wral f1_rsp a_sup_set_class f2_rsp a_wcel f0_rsp a_wi f1_rsp a_wal f1_rsp a_sup_set_class f2_rsp a_wcel f0_rsp a_wi p_sylbi $.
$}

$(Restricted specialization.  (Contributed by NM, 12-Oct-1999.) $)

${
	$v ph x A  $.
	f0_rspe $f wff ph $.
	f1_rspe $f set x $.
	f2_rspe $f class A $.
	p_rspe $p |- ( ( x e. A /\ ph ) -> E. x e. A ph ) $= f1_rspe a_sup_set_class f2_rspe a_wcel f0_rspe a_wa f1_rspe p_19.8a f0_rspe f1_rspe f2_rspe a_df-rex f1_rspe a_sup_set_class f2_rspe a_wcel f0_rspe a_wa f1_rspe a_sup_set_class f2_rspe a_wcel f0_rspe a_wa f1_rspe a_wex f0_rspe f1_rspe f2_rspe a_wrex p_sylibr $.
$}

$(Restricted specialization.  (Contributed by NM, 11-Feb-1997.) $)

${
	$v ph x y A B  $.
	f0_rsp2 $f wff ph $.
	f1_rsp2 $f set x $.
	f2_rsp2 $f set y $.
	f3_rsp2 $f class A $.
	f4_rsp2 $f class B $.
	p_rsp2 $p |- ( A. x e. A A. y e. B ph -> ( ( x e. A /\ y e. B ) -> ph ) ) $= f0_rsp2 f2_rsp2 f4_rsp2 a_wral f1_rsp2 f3_rsp2 p_rsp f0_rsp2 f2_rsp2 f4_rsp2 p_rsp f0_rsp2 f2_rsp2 f4_rsp2 a_wral f1_rsp2 f3_rsp2 a_wral f1_rsp2 a_sup_set_class f3_rsp2 a_wcel f0_rsp2 f2_rsp2 f4_rsp2 a_wral f2_rsp2 a_sup_set_class f4_rsp2 a_wcel f0_rsp2 a_wi p_syl6 f0_rsp2 f2_rsp2 f4_rsp2 a_wral f1_rsp2 f3_rsp2 a_wral f1_rsp2 a_sup_set_class f3_rsp2 a_wcel f2_rsp2 a_sup_set_class f4_rsp2 a_wcel f0_rsp2 p_imp3a $.
$}

$(Restricted specialization.  (Contributed by FL, 4-Jun-2012.) $)

${
	$v ph x y A B  $.
	f0_rsp2e $f wff ph $.
	f1_rsp2e $f set x $.
	f2_rsp2e $f set y $.
	f3_rsp2e $f class A $.
	f4_rsp2e $f class B $.
	p_rsp2e $p |- ( ( x e. A /\ y e. B /\ ph ) -> E. x e. A E. y e. B ph ) $= f1_rsp2e a_sup_set_class f3_rsp2e a_wcel f2_rsp2e a_sup_set_class f4_rsp2e a_wcel f0_rsp2e p_simp1 f0_rsp2e f2_rsp2e f4_rsp2e p_rspe f2_rsp2e a_sup_set_class f4_rsp2e a_wcel f0_rsp2e f0_rsp2e f2_rsp2e f4_rsp2e a_wrex f1_rsp2e a_sup_set_class f3_rsp2e a_wcel p_3adant1 f1_rsp2e a_sup_set_class f3_rsp2e a_wcel f0_rsp2e f2_rsp2e f4_rsp2e a_wrex a_wa f1_rsp2e p_19.8a f1_rsp2e a_sup_set_class f3_rsp2e a_wcel f2_rsp2e a_sup_set_class f4_rsp2e a_wcel f0_rsp2e a_w3a f1_rsp2e a_sup_set_class f3_rsp2e a_wcel f0_rsp2e f2_rsp2e f4_rsp2e a_wrex f1_rsp2e a_sup_set_class f3_rsp2e a_wcel f0_rsp2e f2_rsp2e f4_rsp2e a_wrex a_wa f1_rsp2e a_wex p_syl2anc f0_rsp2e f2_rsp2e f4_rsp2e a_wrex f1_rsp2e f3_rsp2e a_df-rex f1_rsp2e a_sup_set_class f3_rsp2e a_wcel f2_rsp2e a_sup_set_class f4_rsp2e a_wcel f0_rsp2e a_w3a f1_rsp2e a_sup_set_class f3_rsp2e a_wcel f0_rsp2e f2_rsp2e f4_rsp2e a_wrex a_wa f1_rsp2e a_wex f0_rsp2e f2_rsp2e f4_rsp2e a_wrex f1_rsp2e f3_rsp2e a_wrex p_sylibr $.
$}

$(Specialization rule for restricted quantification.  (Contributed by NM,
       19-Nov-1994.) $)

${
	$v ph x A  $.
	f0_rspec $f wff ph $.
	f1_rspec $f set x $.
	f2_rspec $f class A $.
	e0_rspec $e |- A. x e. A ph $.
	p_rspec $p |- ( x e. A -> ph ) $= e0_rspec f0_rspec f1_rspec f2_rspec p_rsp f0_rspec f1_rspec f2_rspec a_wral f1_rspec a_sup_set_class f2_rspec a_wcel f0_rspec a_wi a_ax-mp $.
$}

$(Generalization rule for restricted quantification.  (Contributed by NM,
       19-Nov-1994.) $)

${
	$v ph x A  $.
	f0_rgen $f wff ph $.
	f1_rgen $f set x $.
	f2_rgen $f class A $.
	e0_rgen $e |- ( x e. A -> ph ) $.
	p_rgen $p |- A. x e. A ph $= f0_rgen f1_rgen f2_rgen a_df-ral e0_rgen f0_rgen f1_rgen f2_rgen a_wral f1_rgen a_sup_set_class f2_rgen a_wcel f0_rgen a_wi f1_rgen p_mpgbir $.
$}

$(Generalization rule for restricted quantification.  Note that ` x ` and
       ` y ` needn't be distinct (and illustrates the use of ~ dvelim ).
       (Contributed by NM, 23-Nov-1994.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged. $)

${
	$v ph x y A  $.
	$d y z A  $.
	$d x z  $.
	f0_rgen2a $f wff ph $.
	f1_rgen2a $f set x $.
	f2_rgen2a $f set y $.
	f3_rgen2a $f class A $.
	i0_rgen2a $f set z $.
	e0_rgen2a $e |- ( ( x e. A /\ y e. A ) -> ph ) $.
	p_rgen2a $p |- A. x e. A A. y e. A ph $= f2_rgen2a a_sup_set_class f1_rgen2a a_sup_set_class f3_rgen2a p_eleq1 e0_rgen2a f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a p_ex f2_rgen2a a_sup_set_class f1_rgen2a a_sup_set_class a_wceq f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a a_wi p_syl6bi f2_rgen2a a_sup_set_class f1_rgen2a a_sup_set_class a_wceq f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a p_pm2.43d f2_rgen2a a_sup_set_class f1_rgen2a a_sup_set_class a_wceq f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a a_wi f2_rgen2a p_alimi f2_rgen2a a_sup_set_class f1_rgen2a a_sup_set_class a_wceq f2_rgen2a a_wal f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a a_wi f2_rgen2a a_wal f1_rgen2a a_sup_set_class f3_rgen2a a_wcel p_a1d i0_rgen2a a_sup_set_class f1_rgen2a a_sup_set_class f3_rgen2a p_eleq1 i0_rgen2a a_sup_set_class f3_rgen2a a_wcel f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f2_rgen2a f1_rgen2a i0_rgen2a p_dvelimv e0_rgen2a f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a p_ex f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a a_wi f2_rgen2a p_alimi f2_rgen2a a_sup_set_class f1_rgen2a a_sup_set_class a_wceq f2_rgen2a a_wal a_wn f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f2_rgen2a a_wal f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a a_wi f2_rgen2a a_wal p_syl6 f2_rgen2a a_sup_set_class f1_rgen2a a_sup_set_class a_wceq f2_rgen2a a_wal f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a a_wi f2_rgen2a a_wal a_wi p_pm2.61i f0_rgen2a f2_rgen2a f3_rgen2a a_df-ral f1_rgen2a a_sup_set_class f3_rgen2a a_wcel f2_rgen2a a_sup_set_class f3_rgen2a a_wcel f0_rgen2a a_wi f2_rgen2a a_wal f0_rgen2a f2_rgen2a f3_rgen2a a_wral p_sylibr f0_rgen2a f2_rgen2a f3_rgen2a a_wral f1_rgen2a f3_rgen2a p_rgen $.
$}

$(Generalization rule for restricted quantification.  (Contributed by NM,
       18-Jun-2014.) $)

${
	$v ph x A  $.
	f0_rgenw $f wff ph $.
	f1_rgenw $f set x $.
	f2_rgenw $f class A $.
	e0_rgenw $e |- ph $.
	p_rgenw $p |- A. x e. A ph $= e0_rgenw f0_rgenw f1_rgenw a_sup_set_class f2_rgenw a_wcel p_a1i f0_rgenw f1_rgenw f2_rgenw p_rgen $.
$}

$(Generalization rule for restricted quantification.  Note that ` x ` and
       ` y ` needn't be distinct.  (Contributed by NM, 18-Jun-2014.) $)

${
	$v ph x y A B  $.
	f0_rgen2w $f wff ph $.
	f1_rgen2w $f set x $.
	f2_rgen2w $f set y $.
	f3_rgen2w $f class A $.
	f4_rgen2w $f class B $.
	e0_rgen2w $e |- ph $.
	p_rgen2w $p |- A. x e. A A. y e. B ph $= e0_rgen2w f0_rgen2w f2_rgen2w f4_rgen2w p_rgenw f0_rgen2w f2_rgen2w f4_rgen2w a_wral f1_rgen2w f3_rgen2w p_rgenw $.
$}

$(Modus ponens combined with restricted generalization.  (Contributed by
       NM, 10-Aug-2004.) $)

${
	$v ph ps x A  $.
	f0_mprg $f wff ph $.
	f1_mprg $f wff ps $.
	f2_mprg $f set x $.
	f3_mprg $f class A $.
	e0_mprg $e |- ( A. x e. A ph -> ps ) $.
	e1_mprg $e |- ( x e. A -> ph ) $.
	p_mprg $p |- ps $= e1_mprg f0_mprg f2_mprg f3_mprg p_rgen e0_mprg f0_mprg f2_mprg f3_mprg a_wral f1_mprg a_ax-mp $.
$}

$(Modus ponens on biconditional combined with restricted generalization.
       (Contributed by NM, 21-Mar-2004.) $)

${
	$v ph ps x A  $.
	f0_mprgbir $f wff ph $.
	f1_mprgbir $f wff ps $.
	f2_mprgbir $f set x $.
	f3_mprgbir $f class A $.
	e0_mprgbir $e |- ( ph <-> A. x e. A ps ) $.
	e1_mprgbir $e |- ( x e. A -> ps ) $.
	p_mprgbir $p |- ph $= e1_mprgbir f1_mprgbir f2_mprgbir f3_mprgbir p_rgen e0_mprgbir f0_mprgbir f1_mprgbir f2_mprgbir f3_mprgbir a_wral p_mpbir $.
$}

$(Distribution of restricted quantification over implication.  (Contributed
     by NM, 9-Feb-1997.) $)

${
	$v ph ps x A  $.
	f0_ralim $f wff ph $.
	f1_ralim $f wff ps $.
	f2_ralim $f set x $.
	f3_ralim $f class A $.
	p_ralim $p |- ( A. x e. A ( ph -> ps ) -> ( A. x e. A ph -> A. x e. A ps ) ) $= f0_ralim f1_ralim a_wi f2_ralim f3_ralim a_df-ral f2_ralim a_sup_set_class f3_ralim a_wcel f0_ralim f1_ralim a_ax-2 f2_ralim a_sup_set_class f3_ralim a_wcel f0_ralim f1_ralim a_wi a_wi f2_ralim a_sup_set_class f3_ralim a_wcel f0_ralim a_wi f2_ralim a_sup_set_class f3_ralim a_wcel f1_ralim a_wi f2_ralim p_al2imi f0_ralim f1_ralim a_wi f2_ralim f3_ralim a_wral f2_ralim a_sup_set_class f3_ralim a_wcel f0_ralim f1_ralim a_wi a_wi f2_ralim a_wal f2_ralim a_sup_set_class f3_ralim a_wcel f0_ralim a_wi f2_ralim a_wal f2_ralim a_sup_set_class f3_ralim a_wcel f1_ralim a_wi f2_ralim a_wal a_wi p_sylbi f0_ralim f2_ralim f3_ralim a_df-ral f1_ralim f2_ralim f3_ralim a_df-ral f0_ralim f1_ralim a_wi f2_ralim f3_ralim a_wral f2_ralim a_sup_set_class f3_ralim a_wcel f0_ralim a_wi f2_ralim a_wal f2_ralim a_sup_set_class f3_ralim a_wcel f1_ralim a_wi f2_ralim a_wal f0_ralim f2_ralim f3_ralim a_wral f1_ralim f2_ralim f3_ralim a_wral p_3imtr4g $.
$}

$(Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 22-Feb-2004.) $)

${
	$v ph ps x A B  $.
	f0_ralimi2 $f wff ph $.
	f1_ralimi2 $f wff ps $.
	f2_ralimi2 $f set x $.
	f3_ralimi2 $f class A $.
	f4_ralimi2 $f class B $.
	e0_ralimi2 $e |- ( ( x e. A -> ph ) -> ( x e. B -> ps ) ) $.
	p_ralimi2 $p |- ( A. x e. A ph -> A. x e. B ps ) $= e0_ralimi2 f2_ralimi2 a_sup_set_class f3_ralimi2 a_wcel f0_ralimi2 a_wi f2_ralimi2 a_sup_set_class f4_ralimi2 a_wcel f1_ralimi2 a_wi f2_ralimi2 p_alimi f0_ralimi2 f2_ralimi2 f3_ralimi2 a_df-ral f1_ralimi2 f2_ralimi2 f4_ralimi2 a_df-ral f2_ralimi2 a_sup_set_class f3_ralimi2 a_wcel f0_ralimi2 a_wi f2_ralimi2 a_wal f2_ralimi2 a_sup_set_class f4_ralimi2 a_wcel f1_ralimi2 a_wi f2_ralimi2 a_wal f0_ralimi2 f2_ralimi2 f3_ralimi2 a_wral f1_ralimi2 f2_ralimi2 f4_ralimi2 a_wral p_3imtr4i $.
$}

$(Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 19-Jul-1996.) $)

${
	$v ph ps x A  $.
	f0_ralimia $f wff ph $.
	f1_ralimia $f wff ps $.
	f2_ralimia $f set x $.
	f3_ralimia $f class A $.
	e0_ralimia $e |- ( x e. A -> ( ph -> ps ) ) $.
	p_ralimia $p |- ( A. x e. A ph -> A. x e. A ps ) $= e0_ralimia f2_ralimia a_sup_set_class f3_ralimia a_wcel f0_ralimia f1_ralimia p_a2i f0_ralimia f1_ralimia f2_ralimia f3_ralimia f3_ralimia p_ralimi2 $.
$}

$(Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 4-Aug-2007.) $)

${
	$v ph ps x A  $.
	f0_ralimiaa $f wff ph $.
	f1_ralimiaa $f wff ps $.
	f2_ralimiaa $f set x $.
	f3_ralimiaa $f class A $.
	e0_ralimiaa $e |- ( ( x e. A /\ ph ) -> ps ) $.
	p_ralimiaa $p |- ( A. x e. A ph -> A. x e. A ps ) $= e0_ralimiaa f2_ralimiaa a_sup_set_class f3_ralimiaa a_wcel f0_ralimiaa f1_ralimiaa p_ex f0_ralimiaa f1_ralimiaa f2_ralimiaa f3_ralimiaa p_ralimia $.
$}

$(Inference quantifying both antecedent and consequent, with strong
       hypothesis.  (Contributed by NM, 4-Mar-1997.) $)

${
	$v ph ps x A  $.
	f0_ralimi $f wff ph $.
	f1_ralimi $f wff ps $.
	f2_ralimi $f set x $.
	f3_ralimi $f class A $.
	e0_ralimi $e |- ( ph -> ps ) $.
	p_ralimi $p |- ( A. x e. A ph -> A. x e. A ps ) $= e0_ralimi f0_ralimi f1_ralimi a_wi f2_ralimi a_sup_set_class f3_ralimi a_wcel p_a1i f0_ralimi f1_ralimi f2_ralimi f3_ralimi p_ralimia $.
$}

$(Inference quantifying antecedent, nested antecedent, and consequent,
       with a strong hypothesis.  (Contributed by NM, 19-Dec-2006.) $)

${
	$v ph ps ch x A  $.
	f0_ral2imi $f wff ph $.
	f1_ral2imi $f wff ps $.
	f2_ral2imi $f wff ch $.
	f3_ral2imi $f set x $.
	f4_ral2imi $f class A $.
	e0_ral2imi $e |- ( ph -> ( ps -> ch ) ) $.
	p_ral2imi $p |- ( A. x e. A ph -> ( A. x e. A ps -> A. x e. A ch ) ) $= e0_ral2imi f0_ral2imi f1_ral2imi f2_ral2imi a_wi f3_ral2imi f4_ral2imi p_ralimi f1_ral2imi f2_ral2imi f3_ral2imi f4_ral2imi p_ralim f0_ral2imi f3_ral2imi f4_ral2imi a_wral f1_ral2imi f2_ral2imi a_wi f3_ral2imi f4_ral2imi a_wral f1_ral2imi f3_ral2imi f4_ral2imi a_wral f2_ral2imi f3_ral2imi f4_ral2imi a_wral a_wi p_syl $.
$}

$(Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 22-Sep-2003.) $)

${
	$v ph ps ch x A  $.
	f0_ralimdaa $f wff ph $.
	f1_ralimdaa $f wff ps $.
	f2_ralimdaa $f wff ch $.
	f3_ralimdaa $f set x $.
	f4_ralimdaa $f class A $.
	e0_ralimdaa $e |- F/ x ph $.
	e1_ralimdaa $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	p_ralimdaa $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $= e0_ralimdaa e1_ralimdaa f0_ralimdaa f3_ralimdaa a_sup_set_class f4_ralimdaa a_wcel f1_ralimdaa f2_ralimdaa a_wi p_ex f0_ralimdaa f3_ralimdaa a_sup_set_class f4_ralimdaa a_wcel f1_ralimdaa f2_ralimdaa p_a2d f0_ralimdaa f3_ralimdaa a_sup_set_class f4_ralimdaa a_wcel f1_ralimdaa a_wi f3_ralimdaa a_sup_set_class f4_ralimdaa a_wcel f2_ralimdaa a_wi f3_ralimdaa p_alimd f1_ralimdaa f3_ralimdaa f4_ralimdaa a_df-ral f2_ralimdaa f3_ralimdaa f4_ralimdaa a_df-ral f0_ralimdaa f3_ralimdaa a_sup_set_class f4_ralimdaa a_wcel f1_ralimdaa a_wi f3_ralimdaa a_wal f3_ralimdaa a_sup_set_class f4_ralimdaa a_wcel f2_ralimdaa a_wi f3_ralimdaa a_wal f1_ralimdaa f3_ralimdaa f4_ralimdaa a_wral f2_ralimdaa f3_ralimdaa f4_ralimdaa a_wral p_3imtr4g $.
$}

$(Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 22-May-1999.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_ralimdva $f wff ph $.
	f1_ralimdva $f wff ps $.
	f2_ralimdva $f wff ch $.
	f3_ralimdva $f set x $.
	f4_ralimdva $f class A $.
	e0_ralimdva $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	p_ralimdva $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $= f0_ralimdva f3_ralimdva p_nfv e0_ralimdva f0_ralimdva f1_ralimdva f2_ralimdva f3_ralimdva f4_ralimdva p_ralimdaa $.
$}

$(Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 8-Oct-2003.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_ralimdv $f wff ph $.
	f1_ralimdv $f wff ps $.
	f2_ralimdv $f wff ch $.
	f3_ralimdv $f set x $.
	f4_ralimdv $f class A $.
	e0_ralimdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_ralimdv $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $= e0_ralimdv f0_ralimdv f1_ralimdv f2_ralimdv a_wi f3_ralimdv a_sup_set_class f4_ralimdv a_wcel p_adantr f0_ralimdv f1_ralimdv f2_ralimdv f3_ralimdv f4_ralimdv p_ralimdva $.
$}

$(Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 1-Feb-2005.) $)

${
	$v ph ps ch x A B  $.
	$d x ph  $.
	f0_ralimdv2 $f wff ph $.
	f1_ralimdv2 $f wff ps $.
	f2_ralimdv2 $f wff ch $.
	f3_ralimdv2 $f set x $.
	f4_ralimdv2 $f class A $.
	f5_ralimdv2 $f class B $.
	e0_ralimdv2 $e |- ( ph -> ( ( x e. A -> ps ) -> ( x e. B -> ch ) ) ) $.
	p_ralimdv2 $p |- ( ph -> ( A. x e. A ps -> A. x e. B ch ) ) $= e0_ralimdv2 f0_ralimdv2 f3_ralimdv2 a_sup_set_class f4_ralimdv2 a_wcel f1_ralimdv2 a_wi f3_ralimdv2 a_sup_set_class f5_ralimdv2 a_wcel f2_ralimdv2 a_wi f3_ralimdv2 p_alimdv f1_ralimdv2 f3_ralimdv2 f4_ralimdv2 a_df-ral f2_ralimdv2 f3_ralimdv2 f5_ralimdv2 a_df-ral f0_ralimdv2 f3_ralimdv2 a_sup_set_class f4_ralimdv2 a_wcel f1_ralimdv2 a_wi f3_ralimdv2 a_wal f3_ralimdv2 a_sup_set_class f5_ralimdv2 a_wcel f2_ralimdv2 a_wi f3_ralimdv2 a_wal f1_ralimdv2 f3_ralimdv2 f4_ralimdv2 a_wral f2_ralimdv2 f3_ralimdv2 f5_ralimdv2 a_wral p_3imtr4g $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 10-Oct-1999.) $)

${
	$v ph ps x A  $.
	f0_ralrimi $f wff ph $.
	f1_ralrimi $f wff ps $.
	f2_ralrimi $f set x $.
	f3_ralrimi $f class A $.
	e0_ralrimi $e |- F/ x ph $.
	e1_ralrimi $e |- ( ph -> ( x e. A -> ps ) ) $.
	p_ralrimi $p |- ( ph -> A. x e. A ps ) $= e0_ralrimi e1_ralrimi f0_ralrimi f2_ralrimi a_sup_set_class f3_ralrimi a_wcel f1_ralrimi a_wi f2_ralrimi p_alrimi f1_ralrimi f2_ralrimi f3_ralrimi a_df-ral f0_ralrimi f2_ralrimi a_sup_set_class f3_ralrimi a_wcel f1_ralrimi a_wi f2_ralrimi a_wal f1_ralrimi f2_ralrimi f3_ralrimi a_wral p_sylibr $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 22-Nov-1994.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_ralrimiv $f wff ph $.
	f1_ralrimiv $f wff ps $.
	f2_ralrimiv $f set x $.
	f3_ralrimiv $f class A $.
	e0_ralrimiv $e |- ( ph -> ( x e. A -> ps ) ) $.
	p_ralrimiv $p |- ( ph -> A. x e. A ps ) $= f0_ralrimiv f2_ralrimiv p_nfv e0_ralrimiv f0_ralrimiv f1_ralrimiv f2_ralrimiv f3_ralrimiv p_ralrimi $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 2-Jan-2006.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_ralrimiva $f wff ph $.
	f1_ralrimiva $f wff ps $.
	f2_ralrimiva $f set x $.
	f3_ralrimiva $f class A $.
	e0_ralrimiva $e |- ( ( ph /\ x e. A ) -> ps ) $.
	p_ralrimiva $p |- ( ph -> A. x e. A ps ) $= e0_ralrimiva f0_ralrimiva f2_ralrimiva a_sup_set_class f3_ralrimiva a_wcel f1_ralrimiva p_ex f0_ralrimiva f1_ralrimiva f2_ralrimiva f3_ralrimiva p_ralrimiv $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 18-Jun-2014.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_ralrimivw $f wff ph $.
	f1_ralrimivw $f wff ps $.
	f2_ralrimivw $f set x $.
	f3_ralrimivw $f class A $.
	e0_ralrimivw $e |- ( ph -> ps ) $.
	p_ralrimivw $p |- ( ph -> A. x e. A ps ) $= e0_ralrimivw f0_ralrimivw f1_ralrimivw f2_ralrimivw a_sup_set_class f3_ralrimivw a_wcel p_a1d f0_ralrimivw f1_ralrimivw f2_ralrimivw f3_ralrimivw p_ralrimiv $.
$}

$(Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers (closed
       theorem version).  (Contributed by NM, 1-Mar-2008.) $)

${
	$v ph ps x A  $.
	f0_r19.21t $f wff ph $.
	f1_r19.21t $f wff ps $.
	f2_r19.21t $f set x $.
	f3_r19.21t $f class A $.
	p_r19.21t $p |- ( F/ x ph -> ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) ) $= f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f0_r19.21t f1_r19.21t p_bi2.04 f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f0_r19.21t f1_r19.21t a_wi a_wi f0_r19.21t f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f1_r19.21t a_wi a_wi f2_r19.21t p_albii f0_r19.21t f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f1_r19.21t a_wi f2_r19.21t p_19.21t f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f0_r19.21t f1_r19.21t a_wi a_wi f2_r19.21t a_wal f0_r19.21t f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f1_r19.21t a_wi a_wi f2_r19.21t a_wal f0_r19.21t f2_r19.21t a_wnf f0_r19.21t f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f1_r19.21t a_wi f2_r19.21t a_wal a_wi p_syl5bb f0_r19.21t f1_r19.21t a_wi f2_r19.21t f3_r19.21t a_df-ral f1_r19.21t f2_r19.21t f3_r19.21t a_df-ral f1_r19.21t f2_r19.21t f3_r19.21t a_wral f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f1_r19.21t a_wi f2_r19.21t a_wal f0_r19.21t p_imbi2i f0_r19.21t f2_r19.21t a_wnf f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f0_r19.21t f1_r19.21t a_wi a_wi f2_r19.21t a_wal f0_r19.21t f2_r19.21t a_sup_set_class f3_r19.21t a_wcel f1_r19.21t a_wi f2_r19.21t a_wal a_wi f0_r19.21t f1_r19.21t a_wi f2_r19.21t f3_r19.21t a_wral f0_r19.21t f1_r19.21t f2_r19.21t f3_r19.21t a_wral a_wi p_3bitr4g $.
$}

$(Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by Scott Fenton, 30-Mar-2011.) $)

${
	$v ph ps x A  $.
	f0_r19.21 $f wff ph $.
	f1_r19.21 $f wff ps $.
	f2_r19.21 $f set x $.
	f3_r19.21 $f class A $.
	e0_r19.21 $e |- F/ x ph $.
	p_r19.21 $p |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) $= e0_r19.21 f0_r19.21 f1_r19.21 f2_r19.21 f3_r19.21 p_r19.21t f0_r19.21 f2_r19.21 a_wnf f0_r19.21 f1_r19.21 a_wi f2_r19.21 f3_r19.21 a_wral f0_r19.21 f1_r19.21 f2_r19.21 f3_r19.21 a_wral a_wi a_wb a_ax-mp $.
$}

$(Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_r19.21v $f wff ph $.
	f1_r19.21v $f wff ps $.
	f2_r19.21v $f set x $.
	f3_r19.21v $f class A $.
	p_r19.21v $p |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) $= f0_r19.21v f2_r19.21v p_nfv f0_r19.21v f1_r19.21v f2_r19.21v f3_r19.21v p_r19.21 $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 16-Feb-2004.) $)

${
	$v ph ps ch x A  $.
	f0_ralrimd $f wff ph $.
	f1_ralrimd $f wff ps $.
	f2_ralrimd $f wff ch $.
	f3_ralrimd $f set x $.
	f4_ralrimd $f class A $.
	e0_ralrimd $e |- F/ x ph $.
	e1_ralrimd $e |- F/ x ps $.
	e2_ralrimd $e |- ( ph -> ( ps -> ( x e. A -> ch ) ) ) $.
	p_ralrimd $p |- ( ph -> ( ps -> A. x e. A ch ) ) $= e0_ralrimd e1_ralrimd e2_ralrimd f0_ralrimd f1_ralrimd f3_ralrimd a_sup_set_class f4_ralrimd a_wcel f2_ralrimd a_wi f3_ralrimd p_alrimd f2_ralrimd f3_ralrimd f4_ralrimd a_df-ral f0_ralrimd f1_ralrimd f3_ralrimd a_sup_set_class f4_ralrimd a_wcel f2_ralrimd a_wi f3_ralrimd a_wal f2_ralrimd f3_ralrimd f4_ralrimd a_wral p_syl6ibr $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 27-May-1998.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	$d x ps  $.
	f0_ralrimdv $f wff ph $.
	f1_ralrimdv $f wff ps $.
	f2_ralrimdv $f wff ch $.
	f3_ralrimdv $f set x $.
	f4_ralrimdv $f class A $.
	e0_ralrimdv $e |- ( ph -> ( ps -> ( x e. A -> ch ) ) ) $.
	p_ralrimdv $p |- ( ph -> ( ps -> A. x e. A ch ) ) $= f0_ralrimdv f3_ralrimdv p_nfv f1_ralrimdv f3_ralrimdv p_nfv e0_ralrimdv f0_ralrimdv f1_ralrimdv f2_ralrimdv f3_ralrimdv f4_ralrimdv p_ralrimd $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 2-Feb-2008.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	$d x ps  $.
	f0_ralrimdva $f wff ph $.
	f1_ralrimdva $f wff ps $.
	f2_ralrimdva $f wff ch $.
	f3_ralrimdva $f set x $.
	f4_ralrimdva $f class A $.
	e0_ralrimdva $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	p_ralrimdva $p |- ( ph -> ( ps -> A. x e. A ch ) ) $= e0_ralrimdva f0_ralrimdva f3_ralrimdva a_sup_set_class f4_ralrimdva a_wcel f1_ralrimdva f2_ralrimdva a_wi p_ex f0_ralrimdva f3_ralrimdva a_sup_set_class f4_ralrimdva a_wcel f1_ralrimdva f2_ralrimdva p_com23 f0_ralrimdva f1_ralrimdva f2_ralrimdva f3_ralrimdva f4_ralrimdva p_ralrimdv $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       24-Jul-2004.) $)

${
	$v ph ps x y A B  $.
	$d x y ph  $.
	$d y A  $.
	f0_ralrimivv $f wff ph $.
	f1_ralrimivv $f wff ps $.
	f2_ralrimivv $f set x $.
	f3_ralrimivv $f set y $.
	f4_ralrimivv $f class A $.
	f5_ralrimivv $f class B $.
	e0_ralrimivv $e |- ( ph -> ( ( x e. A /\ y e. B ) -> ps ) ) $.
	p_ralrimivv $p |- ( ph -> A. x e. A A. y e. B ps ) $= e0_ralrimivv f0_ralrimivv f2_ralrimivv a_sup_set_class f4_ralrimivv a_wcel f3_ralrimivv a_sup_set_class f5_ralrimivv a_wcel f1_ralrimivv p_exp3a f0_ralrimivv f2_ralrimivv a_sup_set_class f4_ralrimivv a_wcel f1_ralrimivv f3_ralrimivv f5_ralrimivv p_ralrimdv f0_ralrimivv f1_ralrimivv f3_ralrimivv f5_ralrimivv a_wral f2_ralrimivv f4_ralrimivv p_ralrimiv $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by Jeff
       Madsen, 19-Jun-2011.) $)

${
	$v ph ps x y A B  $.
	$d ph x y  $.
	$d A y  $.
	f0_ralrimivva $f wff ph $.
	f1_ralrimivva $f wff ps $.
	f2_ralrimivva $f set x $.
	f3_ralrimivva $f set y $.
	f4_ralrimivva $f class A $.
	f5_ralrimivva $f class B $.
	e0_ralrimivva $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ps ) $.
	p_ralrimivva $p |- ( ph -> A. x e. A A. y e. B ps ) $= e0_ralrimivva f0_ralrimivva f2_ralrimivva a_sup_set_class f4_ralrimivva a_wcel f3_ralrimivva a_sup_set_class f5_ralrimivva a_wcel a_wa f1_ralrimivva p_ex f0_ralrimivva f1_ralrimivva f2_ralrimivva f3_ralrimivva f4_ralrimivva f5_ralrimivva p_ralrimivv $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with triple quantification.)  (Contributed by Mario
       Carneiro, 9-Jul-2014.) $)

${
	$v ph ps x y z A B C  $.
	$d ph x y z  $.
	$d A y z  $.
	$d B z  $.
	f0_ralrimivvva $f wff ph $.
	f1_ralrimivvva $f wff ps $.
	f2_ralrimivvva $f set x $.
	f3_ralrimivvva $f set y $.
	f4_ralrimivvva $f set z $.
	f5_ralrimivvva $f class A $.
	f6_ralrimivvva $f class B $.
	f7_ralrimivvva $f class C $.
	e0_ralrimivvva $e |- ( ( ph /\ ( x e. A /\ y e. B /\ z e. C ) ) -> ps ) $.
	p_ralrimivvva $p |- ( ph -> A. x e. A A. y e. B A. z e. C ps ) $= e0_ralrimivvva f0_ralrimivvva f2_ralrimivvva a_sup_set_class f5_ralrimivvva a_wcel f3_ralrimivvva a_sup_set_class f6_ralrimivvva a_wcel f4_ralrimivvva a_sup_set_class f7_ralrimivvva a_wcel f1_ralrimivvva p_3exp2 f0_ralrimivvva f2_ralrimivvva a_sup_set_class f5_ralrimivvva a_wcel f3_ralrimivvva a_sup_set_class f6_ralrimivvva a_wcel f4_ralrimivvva a_sup_set_class f7_ralrimivvva a_wcel f1_ralrimivvva p_imp41 f0_ralrimivvva f2_ralrimivvva a_sup_set_class f5_ralrimivvva a_wcel a_wa f3_ralrimivvva a_sup_set_class f6_ralrimivvva a_wcel a_wa f1_ralrimivvva f4_ralrimivvva f7_ralrimivvva p_ralrimiva f0_ralrimivvva f2_ralrimivvva a_sup_set_class f5_ralrimivvva a_wcel a_wa f1_ralrimivvva f4_ralrimivvva f7_ralrimivvva a_wral f3_ralrimivvva f6_ralrimivvva p_ralrimiva f0_ralrimivvva f1_ralrimivvva f4_ralrimivvva f7_ralrimivvva a_wral f3_ralrimivvva f6_ralrimivvva a_wral f2_ralrimivvva f5_ralrimivvva p_ralrimiva $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       1-Jun-2005.) $)

${
	$v ph ps ch x y A B  $.
	$d x y ph  $.
	$d x y ps  $.
	$d y A  $.
	f0_ralrimdvv $f wff ph $.
	f1_ralrimdvv $f wff ps $.
	f2_ralrimdvv $f wff ch $.
	f3_ralrimdvv $f set x $.
	f4_ralrimdvv $f set y $.
	f5_ralrimdvv $f class A $.
	f6_ralrimdvv $f class B $.
	e0_ralrimdvv $e |- ( ph -> ( ps -> ( ( x e. A /\ y e. B ) -> ch ) ) ) $.
	p_ralrimdvv $p |- ( ph -> ( ps -> A. x e. A A. y e. B ch ) ) $= e0_ralrimdvv f0_ralrimdvv f1_ralrimdvv f3_ralrimdvv a_sup_set_class f5_ralrimdvv a_wcel f4_ralrimdvv a_sup_set_class f6_ralrimdvv a_wcel a_wa f2_ralrimdvv a_wi p_imp f0_ralrimdvv f1_ralrimdvv a_wa f2_ralrimdvv f3_ralrimdvv f4_ralrimdvv f5_ralrimdvv f6_ralrimdvv p_ralrimivv f0_ralrimdvv f1_ralrimdvv f2_ralrimdvv f4_ralrimdvv f6_ralrimdvv a_wral f3_ralrimdvv f5_ralrimdvv a_wral p_ex $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       2-Feb-2008.) $)

${
	$v ph ps ch x y A B  $.
	$d x y ph  $.
	$d x y ps  $.
	$d y A  $.
	f0_ralrimdvva $f wff ph $.
	f1_ralrimdvva $f wff ps $.
	f2_ralrimdvva $f wff ch $.
	f3_ralrimdvva $f set x $.
	f4_ralrimdvva $f set y $.
	f5_ralrimdvva $f class A $.
	f6_ralrimdvva $f class B $.
	e0_ralrimdvva $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) ) $.
	p_ralrimdvva $p |- ( ph -> ( ps -> A. x e. A A. y e. B ch ) ) $= e0_ralrimdvva f0_ralrimdvva f3_ralrimdvva a_sup_set_class f5_ralrimdvva a_wcel f4_ralrimdvva a_sup_set_class f6_ralrimdvva a_wcel a_wa f1_ralrimdvva f2_ralrimdvva a_wi p_ex f0_ralrimdvva f3_ralrimdvva a_sup_set_class f5_ralrimdvva a_wcel f4_ralrimdvva a_sup_set_class f6_ralrimdvva a_wcel a_wa f1_ralrimdvva f2_ralrimdvva p_com23 f0_ralrimdvva f1_ralrimdvva f2_ralrimdvva f3_ralrimdvva f4_ralrimdvva f5_ralrimdvva f6_ralrimdvva p_ralrimdvv $.
$}

$(Generalization rule for restricted quantification.  (Contributed by NM,
       30-May-1999.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	$d y A  $.
	f0_rgen2 $f wff ph $.
	f1_rgen2 $f set x $.
	f2_rgen2 $f set y $.
	f3_rgen2 $f class A $.
	f4_rgen2 $f class B $.
	e0_rgen2 $e |- ( ( x e. A /\ y e. B ) -> ph ) $.
	p_rgen2 $p |- A. x e. A A. y e. B ph $= e0_rgen2 f1_rgen2 a_sup_set_class f3_rgen2 a_wcel f0_rgen2 f2_rgen2 f4_rgen2 p_ralrimiva f0_rgen2 f2_rgen2 f4_rgen2 a_wral f1_rgen2 f3_rgen2 p_rgen $.
$}

$(Generalization rule for restricted quantification.  (Contributed by NM,
       12-Jan-2008.) $)

${
	$v ph x y z A B C  $.
	$d y z A  $.
	$d z B  $.
	$d x y z  $.
	f0_rgen3 $f wff ph $.
	f1_rgen3 $f set x $.
	f2_rgen3 $f set y $.
	f3_rgen3 $f set z $.
	f4_rgen3 $f class A $.
	f5_rgen3 $f class B $.
	f6_rgen3 $f class C $.
	e0_rgen3 $e |- ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) $.
	p_rgen3 $p |- A. x e. A A. y e. B A. z e. C ph $= e0_rgen3 f1_rgen3 a_sup_set_class f4_rgen3 a_wcel f2_rgen3 a_sup_set_class f5_rgen3 a_wcel f3_rgen3 a_sup_set_class f6_rgen3 a_wcel f0_rgen3 p_3expa f1_rgen3 a_sup_set_class f4_rgen3 a_wcel f2_rgen3 a_sup_set_class f5_rgen3 a_wcel a_wa f0_rgen3 f3_rgen3 f6_rgen3 p_ralrimiva f0_rgen3 f3_rgen3 f6_rgen3 a_wral f1_rgen3 f2_rgen3 f4_rgen3 f5_rgen3 p_rgen2 $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 20-Nov-1994.) $)

${
	$v ph ps x A  $.
	f0_r19.21bi $f wff ph $.
	f1_r19.21bi $f wff ps $.
	f2_r19.21bi $f set x $.
	f3_r19.21bi $f class A $.
	e0_r19.21bi $e |- ( ph -> A. x e. A ps ) $.
	p_r19.21bi $p |- ( ( ph /\ x e. A ) -> ps ) $= e0_r19.21bi f1_r19.21bi f2_r19.21bi f3_r19.21bi a_df-ral f0_r19.21bi f1_r19.21bi f2_r19.21bi f3_r19.21bi a_wral f2_r19.21bi a_sup_set_class f3_r19.21bi a_wcel f1_r19.21bi a_wi f2_r19.21bi a_wal p_sylib f0_r19.21bi f2_r19.21bi a_sup_set_class f3_r19.21bi a_wcel f1_r19.21bi a_wi f2_r19.21bi p_19.21bi f0_r19.21bi f2_r19.21bi a_sup_set_class f3_r19.21bi a_wcel f1_r19.21bi p_imp $.
$}

$(Specialization rule for restricted quantification.  (Contributed by NM,
       20-Nov-1994.) $)

${
	$v ph x y A B  $.
	f0_rspec2 $f wff ph $.
	f1_rspec2 $f set x $.
	f2_rspec2 $f set y $.
	f3_rspec2 $f class A $.
	f4_rspec2 $f class B $.
	e0_rspec2 $e |- A. x e. A A. y e. B ph $.
	p_rspec2 $p |- ( ( x e. A /\ y e. B ) -> ph ) $= e0_rspec2 f0_rspec2 f2_rspec2 f4_rspec2 a_wral f1_rspec2 f3_rspec2 p_rspec f1_rspec2 a_sup_set_class f3_rspec2 a_wcel f0_rspec2 f2_rspec2 f4_rspec2 p_r19.21bi $.
$}

$(Specialization rule for restricted quantification.  (Contributed by NM,
       20-Nov-1994.) $)

${
	$v ph x y z A B C  $.
	f0_rspec3 $f wff ph $.
	f1_rspec3 $f set x $.
	f2_rspec3 $f set y $.
	f3_rspec3 $f set z $.
	f4_rspec3 $f class A $.
	f5_rspec3 $f class B $.
	f6_rspec3 $f class C $.
	e0_rspec3 $e |- A. x e. A A. y e. B A. z e. C ph $.
	p_rspec3 $p |- ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) $= e0_rspec3 f0_rspec3 f3_rspec3 f6_rspec3 a_wral f1_rspec3 f2_rspec3 f4_rspec3 f5_rspec3 p_rspec2 f1_rspec3 a_sup_set_class f4_rspec3 a_wcel f2_rspec3 a_sup_set_class f5_rspec3 a_wcel a_wa f0_rspec3 f3_rspec3 f6_rspec3 p_r19.21bi f1_rspec3 a_sup_set_class f4_rspec3 a_wcel f2_rspec3 a_sup_set_class f5_rspec3 a_wcel f3_rspec3 a_sup_set_class f6_rspec3 a_wcel f0_rspec3 p_3impa $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 21-Nov-1994.) $)

${
	$v ph ps x A  $.
	f0_r19.21be $f wff ph $.
	f1_r19.21be $f wff ps $.
	f2_r19.21be $f set x $.
	f3_r19.21be $f class A $.
	e0_r19.21be $e |- ( ph -> A. x e. A ps ) $.
	p_r19.21be $p |- A. x e. A ( ph -> ps ) $= e0_r19.21be f0_r19.21be f1_r19.21be f2_r19.21be f3_r19.21be p_r19.21bi f0_r19.21be f2_r19.21be a_sup_set_class f3_r19.21be a_wcel f1_r19.21be p_expcom f0_r19.21be f1_r19.21be a_wi f2_r19.21be f3_r19.21be p_rgen $.
$}

$(Inference adding restricted existential quantifier to negated wff.
       (Contributed by NM, 16-Oct-2003.) $)

${
	$v ps x A  $.
	f0_nrex $f wff ps $.
	f1_nrex $f set x $.
	f2_nrex $f class A $.
	e0_nrex $e |- ( x e. A -> -. ps ) $.
	p_nrex $p |- -. E. x e. A ps $= e0_nrex f0_nrex a_wn f1_nrex f2_nrex p_rgen f0_nrex f1_nrex f2_nrex p_ralnex f0_nrex a_wn f1_nrex f2_nrex a_wral f0_nrex f1_nrex f2_nrex a_wrex a_wn p_mpbi $.
$}

$(Deduction adding restricted existential quantifier to negated wff.
       (Contributed by NM, 16-Oct-2003.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_nrexdv $f wff ph $.
	f1_nrexdv $f wff ps $.
	f2_nrexdv $f set x $.
	f3_nrexdv $f class A $.
	e0_nrexdv $e |- ( ( ph /\ x e. A ) -> -. ps ) $.
	p_nrexdv $p |- ( ph -> -. E. x e. A ps ) $= e0_nrexdv f0_nrexdv f1_nrexdv a_wn f2_nrexdv f3_nrexdv p_ralrimiva f1_nrexdv f2_nrexdv f3_nrexdv p_ralnex f0_nrexdv f1_nrexdv a_wn f2_nrexdv f3_nrexdv a_wral f1_nrexdv f2_nrexdv f3_nrexdv a_wrex a_wn p_sylib $.
$}

$(Theorem 19.22 of [Margaris] p. 90.  (Restricted quantifier version.)
     (Contributed by NM, 22-Nov-1994.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)

${
	$v ph ps x A  $.
	f0_rexim $f wff ph $.
	f1_rexim $f wff ps $.
	f2_rexim $f set x $.
	f3_rexim $f class A $.
	p_rexim $p |- ( A. x e. A ( ph -> ps ) -> ( E. x e. A ph -> E. x e. A ps ) ) $= f0_rexim f1_rexim p_con3 f0_rexim f1_rexim a_wi f1_rexim a_wn f0_rexim a_wn f2_rexim f3_rexim p_ral2imi f0_rexim f1_rexim a_wi f2_rexim f3_rexim a_wral f1_rexim a_wn f2_rexim f3_rexim a_wral f0_rexim a_wn f2_rexim f3_rexim a_wral p_con3d f0_rexim f2_rexim f3_rexim p_dfrex2 f1_rexim f2_rexim f3_rexim p_dfrex2 f0_rexim f1_rexim a_wi f2_rexim f3_rexim a_wral f0_rexim a_wn f2_rexim f3_rexim a_wral a_wn f1_rexim a_wn f2_rexim f3_rexim a_wral a_wn f0_rexim f2_rexim f3_rexim a_wrex f1_rexim f2_rexim f3_rexim a_wrex p_3imtr4g $.
$}

$(Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 10-Feb-1997.) $)

${
	$v ph ps x A  $.
	f0_reximia $f wff ph $.
	f1_reximia $f wff ps $.
	f2_reximia $f set x $.
	f3_reximia $f class A $.
	e0_reximia $e |- ( x e. A -> ( ph -> ps ) ) $.
	p_reximia $p |- ( E. x e. A ph -> E. x e. A ps ) $= f0_reximia f1_reximia f2_reximia f3_reximia p_rexim e0_reximia f0_reximia f1_reximia a_wi f0_reximia f2_reximia f3_reximia a_wrex f1_reximia f2_reximia f3_reximia a_wrex a_wi f2_reximia f3_reximia p_mprg $.
$}

$(Inference quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 8-Nov-2004.) $)

${
	$v ph ps x A B  $.
	f0_reximi2 $f wff ph $.
	f1_reximi2 $f wff ps $.
	f2_reximi2 $f set x $.
	f3_reximi2 $f class A $.
	f4_reximi2 $f class B $.
	e0_reximi2 $e |- ( ( x e. A /\ ph ) -> ( x e. B /\ ps ) ) $.
	p_reximi2 $p |- ( E. x e. A ph -> E. x e. B ps ) $= e0_reximi2 f2_reximi2 a_sup_set_class f3_reximi2 a_wcel f0_reximi2 a_wa f2_reximi2 a_sup_set_class f4_reximi2 a_wcel f1_reximi2 a_wa f2_reximi2 p_eximi f0_reximi2 f2_reximi2 f3_reximi2 a_df-rex f1_reximi2 f2_reximi2 f4_reximi2 a_df-rex f2_reximi2 a_sup_set_class f3_reximi2 a_wcel f0_reximi2 a_wa f2_reximi2 a_wex f2_reximi2 a_sup_set_class f4_reximi2 a_wcel f1_reximi2 a_wa f2_reximi2 a_wex f0_reximi2 f2_reximi2 f3_reximi2 a_wrex f1_reximi2 f2_reximi2 f4_reximi2 a_wrex p_3imtr4i $.
$}

$(Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 18-Oct-1996.) $)

${
	$v ph ps x A  $.
	f0_reximi $f wff ph $.
	f1_reximi $f wff ps $.
	f2_reximi $f set x $.
	f3_reximi $f class A $.
	e0_reximi $e |- ( ph -> ps ) $.
	p_reximi $p |- ( E. x e. A ph -> E. x e. A ps ) $= e0_reximi f0_reximi f1_reximi a_wi f2_reximi a_sup_set_class f3_reximi a_wcel p_a1i f0_reximi f1_reximi f2_reximi f3_reximi p_reximia $.
$}

$(Deduction from Theorem 19.22 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 31-Aug-1999.) $)

${
	$v ph ps ch x A  $.
	f0_reximdai $f wff ph $.
	f1_reximdai $f wff ps $.
	f2_reximdai $f wff ch $.
	f3_reximdai $f set x $.
	f4_reximdai $f class A $.
	e0_reximdai $e |- F/ x ph $.
	e1_reximdai $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	p_reximdai $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $= e0_reximdai e1_reximdai f0_reximdai f1_reximdai f2_reximdai a_wi f3_reximdai f4_reximdai p_ralrimi f1_reximdai f2_reximdai f3_reximdai f4_reximdai p_rexim f0_reximdai f1_reximdai f2_reximdai a_wi f3_reximdai f4_reximdai a_wral f1_reximdai f3_reximdai f4_reximdai a_wrex f2_reximdai f3_reximdai f4_reximdai a_wrex a_wi p_syl $.
$}

$(Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 17-Sep-2003.) $)

${
	$v ph ps ch x A B  $.
	$d x ph  $.
	f0_reximdv2 $f wff ph $.
	f1_reximdv2 $f wff ps $.
	f2_reximdv2 $f wff ch $.
	f3_reximdv2 $f set x $.
	f4_reximdv2 $f class A $.
	f5_reximdv2 $f class B $.
	e0_reximdv2 $e |- ( ph -> ( ( x e. A /\ ps ) -> ( x e. B /\ ch ) ) ) $.
	p_reximdv2 $p |- ( ph -> ( E. x e. A ps -> E. x e. B ch ) ) $= e0_reximdv2 f0_reximdv2 f3_reximdv2 a_sup_set_class f4_reximdv2 a_wcel f1_reximdv2 a_wa f3_reximdv2 a_sup_set_class f5_reximdv2 a_wcel f2_reximdv2 a_wa f3_reximdv2 p_eximdv f1_reximdv2 f3_reximdv2 f4_reximdv2 a_df-rex f2_reximdv2 f3_reximdv2 f5_reximdv2 a_df-rex f0_reximdv2 f3_reximdv2 a_sup_set_class f4_reximdv2 a_wcel f1_reximdv2 a_wa f3_reximdv2 a_wex f3_reximdv2 a_sup_set_class f5_reximdv2 a_wcel f2_reximdv2 a_wa f3_reximdv2 a_wex f1_reximdv2 f3_reximdv2 f4_reximdv2 a_wrex f2_reximdv2 f3_reximdv2 f5_reximdv2 a_wrex p_3imtr4g $.
$}

$(Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 14-Nov-2002.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_reximdvai $f wff ph $.
	f1_reximdvai $f wff ps $.
	f2_reximdvai $f wff ch $.
	f3_reximdvai $f set x $.
	f4_reximdvai $f class A $.
	e0_reximdvai $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	p_reximdvai $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $= f0_reximdvai f3_reximdvai p_nfv e0_reximdvai f0_reximdvai f1_reximdvai f2_reximdvai f3_reximdvai f4_reximdvai p_reximdai $.
$}

$(Deduction from Theorem 19.22 of [Margaris] p. 90.  (Restricted
       quantifier version with strong hypothesis.)  (Contributed by NM,
       24-Jun-1998.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_reximdv $f wff ph $.
	f1_reximdv $f wff ps $.
	f2_reximdv $f wff ch $.
	f3_reximdv $f set x $.
	f4_reximdv $f class A $.
	e0_reximdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_reximdv $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $= e0_reximdv f0_reximdv f1_reximdv f2_reximdv a_wi f3_reximdv a_sup_set_class f4_reximdv a_wcel p_a1d f0_reximdv f1_reximdv f2_reximdv f3_reximdv f4_reximdv p_reximdvai $.
$}

$(Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 22-May-1999.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_reximdva $f wff ph $.
	f1_reximdva $f wff ps $.
	f2_reximdva $f wff ch $.
	f3_reximdva $f set x $.
	f4_reximdva $f class A $.
	e0_reximdva $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	p_reximdva $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $= e0_reximdva f0_reximdva f3_reximdva a_sup_set_class f4_reximdva a_wcel f1_reximdva f2_reximdva a_wi p_ex f0_reximdva f1_reximdva f2_reximdva f3_reximdva f4_reximdva p_reximdvai $.
$}

$(Theorem 19.12 of [Margaris] p. 89 with restricted quantifiers.
       (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	$d y A  $.
	$d x B  $.
	f0_r19.12 $f wff ph $.
	f1_r19.12 $f set x $.
	f2_r19.12 $f set y $.
	f3_r19.12 $f class A $.
	f4_r19.12 $f class B $.
	p_r19.12 $p |- ( E. x e. A A. y e. B ph -> A. y e. B E. x e. A ph ) $= f2_r19.12 f3_r19.12 p_nfcv f0_r19.12 f2_r19.12 f4_r19.12 p_nfra1 f0_r19.12 f2_r19.12 f4_r19.12 a_wral f2_r19.12 f1_r19.12 f3_r19.12 p_nfrex f0_r19.12 f2_r19.12 f4_r19.12 a_wral f1_r19.12 f3_r19.12 a_wrex f2_r19.12 a_sup_set_class f4_r19.12 a_wcel a_ax-1 f0_r19.12 f2_r19.12 f4_r19.12 a_wral f1_r19.12 f3_r19.12 a_wrex f0_r19.12 f2_r19.12 f4_r19.12 a_wral f1_r19.12 f3_r19.12 a_wrex f2_r19.12 f4_r19.12 p_ralrimi f0_r19.12 f2_r19.12 f4_r19.12 p_rsp f0_r19.12 f2_r19.12 f4_r19.12 a_wral f2_r19.12 a_sup_set_class f4_r19.12 a_wcel f0_r19.12 p_com12 f2_r19.12 a_sup_set_class f4_r19.12 a_wcel f0_r19.12 f2_r19.12 f4_r19.12 a_wral f0_r19.12 f1_r19.12 f3_r19.12 p_reximdv f0_r19.12 f2_r19.12 f4_r19.12 a_wral f1_r19.12 f3_r19.12 a_wrex f0_r19.12 f1_r19.12 f3_r19.12 a_wrex f2_r19.12 f4_r19.12 p_ralimia f0_r19.12 f2_r19.12 f4_r19.12 a_wral f1_r19.12 f3_r19.12 a_wrex f0_r19.12 f2_r19.12 f4_r19.12 a_wral f1_r19.12 f3_r19.12 a_wrex f2_r19.12 f4_r19.12 a_wral f0_r19.12 f1_r19.12 f3_r19.12 a_wrex f2_r19.12 f4_r19.12 a_wral p_syl $.
$}

$(Closed theorem form of ~ r19.23 .  (Contributed by NM, 4-Mar-2013.)
     (Revised by Mario Carneiro, 8-Oct-2016.) $)

${
	$v ph ps x A  $.
	f0_r19.23t $f wff ph $.
	f1_r19.23t $f wff ps $.
	f2_r19.23t $f set x $.
	f3_r19.23t $f class A $.
	p_r19.23t $p |- ( F/ x ps -> ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) ) $= f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t a_wa f1_r19.23t f2_r19.23t p_19.23t f0_r19.23t f1_r19.23t a_wi f2_r19.23t f3_r19.23t a_df-ral f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t f1_r19.23t p_impexp f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t a_wa f1_r19.23t a_wi f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t f1_r19.23t a_wi a_wi f2_r19.23t p_albii f0_r19.23t f1_r19.23t a_wi f2_r19.23t f3_r19.23t a_wral f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t f1_r19.23t a_wi a_wi f2_r19.23t a_wal f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t a_wa f1_r19.23t a_wi f2_r19.23t a_wal p_bitr4i f0_r19.23t f2_r19.23t f3_r19.23t a_df-rex f0_r19.23t f2_r19.23t f3_r19.23t a_wrex f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t a_wa f2_r19.23t a_wex f1_r19.23t p_imbi1i f1_r19.23t f2_r19.23t a_wnf f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t a_wa f1_r19.23t a_wi f2_r19.23t a_wal f2_r19.23t a_sup_set_class f3_r19.23t a_wcel f0_r19.23t a_wa f2_r19.23t a_wex f1_r19.23t a_wi f0_r19.23t f1_r19.23t a_wi f2_r19.23t f3_r19.23t a_wral f0_r19.23t f2_r19.23t f3_r19.23t a_wrex f1_r19.23t a_wi p_3bitr4g $.
$}

$(Theorem 19.23 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 22-Oct-2010.)  (Proof shortened by Mario Carneiro,
       8-Oct-2016.) $)

${
	$v ph ps x A  $.
	f0_r19.23 $f wff ph $.
	f1_r19.23 $f wff ps $.
	f2_r19.23 $f set x $.
	f3_r19.23 $f class A $.
	e0_r19.23 $e |- F/ x ps $.
	p_r19.23 $p |- ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) $= e0_r19.23 f0_r19.23 f1_r19.23 f2_r19.23 f3_r19.23 p_r19.23t f1_r19.23 f2_r19.23 a_wnf f0_r19.23 f1_r19.23 a_wi f2_r19.23 f3_r19.23 a_wral f0_r19.23 f2_r19.23 f3_r19.23 a_wrex f1_r19.23 a_wi a_wb a_ax-mp $.
$}

$(Theorem 19.23 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 31-Aug-1999.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	f0_r19.23v $f wff ph $.
	f1_r19.23v $f wff ps $.
	f2_r19.23v $f set x $.
	f3_r19.23v $f class A $.
	p_r19.23v $p |- ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) $= f1_r19.23v f2_r19.23v p_nfv f0_r19.23v f1_r19.23v f2_r19.23v f3_r19.23v p_r19.23 $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 30-Nov-2003.)  (Proof
       shortened by Andrew Salmon, 30-May-2011.) $)

${
	$v ph ps x A  $.
	f0_rexlimi $f wff ph $.
	f1_rexlimi $f wff ps $.
	f2_rexlimi $f set x $.
	f3_rexlimi $f class A $.
	e0_rexlimi $e |- F/ x ps $.
	e1_rexlimi $e |- ( x e. A -> ( ph -> ps ) ) $.
	p_rexlimi $p |- ( E. x e. A ph -> ps ) $= e1_rexlimi f0_rexlimi f1_rexlimi a_wi f2_rexlimi f3_rexlimi p_rgen e0_rexlimi f0_rexlimi f1_rexlimi f2_rexlimi f3_rexlimi p_r19.23 f0_rexlimi f1_rexlimi a_wi f2_rexlimi f3_rexlimi a_wral f0_rexlimi f2_rexlimi f3_rexlimi a_wrex f1_rexlimi a_wi p_mpbi $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 20-Nov-1994.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	f0_rexlimiv $f wff ph $.
	f1_rexlimiv $f wff ps $.
	f2_rexlimiv $f set x $.
	f3_rexlimiv $f class A $.
	e0_rexlimiv $e |- ( x e. A -> ( ph -> ps ) ) $.
	p_rexlimiv $p |- ( E. x e. A ph -> ps ) $= f1_rexlimiv f2_rexlimiv p_nfv e0_rexlimiv f0_rexlimiv f1_rexlimiv f2_rexlimiv f3_rexlimiv p_rexlimi $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 18-Dec-2006.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	f0_rexlimiva $f wff ph $.
	f1_rexlimiva $f wff ps $.
	f2_rexlimiva $f set x $.
	f3_rexlimiva $f class A $.
	e0_rexlimiva $e |- ( ( x e. A /\ ph ) -> ps ) $.
	p_rexlimiva $p |- ( E. x e. A ph -> ps ) $= e0_rexlimiva f2_rexlimiva a_sup_set_class f3_rexlimiva a_wcel f0_rexlimiva f1_rexlimiva p_ex f0_rexlimiva f1_rexlimiva f2_rexlimiva f3_rexlimiva p_rexlimiv $.
$}

$(Weaker version of ~ rexlimiv .  (Contributed by FL, 19-Sep-2011.) $)

${
	$v ph ps x A  $.
	$d ps x  $.
	f0_rexlimivw $f wff ph $.
	f1_rexlimivw $f wff ps $.
	f2_rexlimivw $f set x $.
	f3_rexlimivw $f class A $.
	e0_rexlimivw $e |- ( ph -> ps ) $.
	p_rexlimivw $p |- ( E. x e. A ph -> ps ) $= e0_rexlimivw f0_rexlimivw f1_rexlimivw a_wi f2_rexlimivw a_sup_set_class f3_rexlimivw a_wcel p_a1i f0_rexlimivw f1_rexlimivw f2_rexlimivw f3_rexlimivw p_rexlimiv $.
$}

$(Deduction from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 27-May-1998.)  (Proof shortened by Andrew
       Salmon, 30-May-2011.) $)

${
	$v ph ps ch x A  $.
	f0_rexlimd $f wff ph $.
	f1_rexlimd $f wff ps $.
	f2_rexlimd $f wff ch $.
	f3_rexlimd $f set x $.
	f4_rexlimd $f class A $.
	e0_rexlimd $e |- F/ x ph $.
	e1_rexlimd $e |- F/ x ch $.
	e2_rexlimd $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	p_rexlimd $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= e0_rexlimd e2_rexlimd f0_rexlimd f1_rexlimd f2_rexlimd a_wi f3_rexlimd f4_rexlimd p_ralrimi e1_rexlimd f1_rexlimd f2_rexlimd f3_rexlimd f4_rexlimd p_r19.23 f0_rexlimd f1_rexlimd f2_rexlimd a_wi f3_rexlimd f4_rexlimd a_wral f1_rexlimd f3_rexlimd f4_rexlimd a_wrex f2_rexlimd a_wi p_sylib $.
$}

$(Version of ~ rexlimd with deduction version of second hypothesis.
       (Contributed by NM, 21-Jul-2013.)  (Revised by Mario Carneiro,
       8-Oct-2016.) $)

${
	$v ph ps ch x A  $.
	f0_rexlimd2 $f wff ph $.
	f1_rexlimd2 $f wff ps $.
	f2_rexlimd2 $f wff ch $.
	f3_rexlimd2 $f set x $.
	f4_rexlimd2 $f class A $.
	e0_rexlimd2 $e |- F/ x ph $.
	e1_rexlimd2 $e |- ( ph -> F/ x ch ) $.
	e2_rexlimd2 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	p_rexlimd2 $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= e0_rexlimd2 e2_rexlimd2 f0_rexlimd2 f1_rexlimd2 f2_rexlimd2 a_wi f3_rexlimd2 f4_rexlimd2 p_ralrimi e1_rexlimd2 f1_rexlimd2 f2_rexlimd2 f3_rexlimd2 f4_rexlimd2 p_r19.23t f0_rexlimd2 f2_rexlimd2 f3_rexlimd2 a_wnf f1_rexlimd2 f2_rexlimd2 a_wi f3_rexlimd2 f4_rexlimd2 a_wral f1_rexlimd2 f3_rexlimd2 f4_rexlimd2 a_wrex f2_rexlimd2 a_wi a_wb p_syl f0_rexlimd2 f1_rexlimd2 f2_rexlimd2 a_wi f3_rexlimd2 f4_rexlimd2 a_wral f1_rexlimd2 f3_rexlimd2 f4_rexlimd2 a_wrex f2_rexlimd2 a_wi p_mpbid $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 14-Nov-2002.)  (Proof shortened by Eric
       Schmidt, 22-Dec-2006.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_rexlimdv $f wff ph $.
	f1_rexlimdv $f wff ps $.
	f2_rexlimdv $f wff ch $.
	f3_rexlimdv $f set x $.
	f4_rexlimdv $f class A $.
	e0_rexlimdv $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	p_rexlimdv $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= f0_rexlimdv f3_rexlimdv p_nfv f2_rexlimdv f3_rexlimdv p_nfv e0_rexlimdv f0_rexlimdv f1_rexlimdv f2_rexlimdv f3_rexlimdv f4_rexlimdv p_rexlimd $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 20-Jan-2007.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_rexlimdva $f wff ph $.
	f1_rexlimdva $f wff ps $.
	f2_rexlimdva $f wff ch $.
	f3_rexlimdva $f set x $.
	f4_rexlimdva $f class A $.
	e0_rexlimdva $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	p_rexlimdva $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= e0_rexlimdva f0_rexlimdva f3_rexlimdva a_sup_set_class f4_rexlimdva a_wcel f1_rexlimdva f2_rexlimdva a_wi p_ex f0_rexlimdva f1_rexlimdva f2_rexlimdva f3_rexlimdva f4_rexlimdva p_rexlimdv $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by Mario Carneiro, 15-Jun-2016.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_rexlimdvaa $f wff ph $.
	f1_rexlimdvaa $f wff ps $.
	f2_rexlimdvaa $f wff ch $.
	f3_rexlimdvaa $f set x $.
	f4_rexlimdvaa $f class A $.
	e0_rexlimdvaa $e |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch ) $.
	p_rexlimdvaa $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= e0_rexlimdvaa f0_rexlimdvaa f3_rexlimdvaa a_sup_set_class f4_rexlimdvaa a_wcel f1_rexlimdvaa f2_rexlimdvaa p_expr f0_rexlimdvaa f1_rexlimdvaa f2_rexlimdvaa f3_rexlimdvaa f4_rexlimdvaa p_rexlimdva $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  Frequently-used variant of ~ rexlimdv .  (Contributed by NM,
       7-Jun-2015.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_rexlimdv3a $f wff ph $.
	f1_rexlimdv3a $f wff ps $.
	f2_rexlimdv3a $f wff ch $.
	f3_rexlimdv3a $f set x $.
	f4_rexlimdv3a $f class A $.
	e0_rexlimdv3a $e |- ( ( ph /\ x e. A /\ ps ) -> ch ) $.
	p_rexlimdv3a $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= e0_rexlimdv3a f0_rexlimdv3a f3_rexlimdv3a a_sup_set_class f4_rexlimdv3a a_wcel f1_rexlimdv3a f2_rexlimdv3a p_3exp f0_rexlimdv3a f1_rexlimdv3a f2_rexlimdv3a f3_rexlimdv3a f4_rexlimdv3a p_rexlimdv $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 18-Jun-2014.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_rexlimdvw $f wff ph $.
	f1_rexlimdvw $f wff ps $.
	f2_rexlimdvw $f wff ch $.
	f3_rexlimdvw $f set x $.
	f4_rexlimdvw $f class A $.
	e0_rexlimdvw $e |- ( ph -> ( ps -> ch ) ) $.
	p_rexlimdvw $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= e0_rexlimdvw f0_rexlimdvw f1_rexlimdvw f2_rexlimdvw a_wi f3_rexlimdvw a_sup_set_class f4_rexlimdvw a_wcel p_a1d f0_rexlimdvw f1_rexlimdvw f2_rexlimdvw f3_rexlimdvw f4_rexlimdvw p_rexlimdv $.
$}

$(Restricted existential elimination rule of natural deduction.
       (Contributed by Mario Carneiro, 15-Jun-2016.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	$d x ch  $.
	f0_rexlimddv $f wff ph $.
	f1_rexlimddv $f wff ps $.
	f2_rexlimddv $f wff ch $.
	f3_rexlimddv $f set x $.
	f4_rexlimddv $f class A $.
	e0_rexlimddv $e |- ( ph -> E. x e. A ps ) $.
	e1_rexlimddv $e |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch ) $.
	p_rexlimddv $p |- ( ph -> ch ) $= e0_rexlimddv e1_rexlimddv f0_rexlimddv f1_rexlimddv f2_rexlimddv f3_rexlimddv f4_rexlimddv p_rexlimdvaa f0_rexlimddv f1_rexlimddv f3_rexlimddv f4_rexlimddv a_wrex f2_rexlimddv p_mpd $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 17-Feb-2004.) $)

${
	$v ph ps x y A B  $.
	$d x y ps  $.
	$d y A  $.
	f0_rexlimivv $f wff ph $.
	f1_rexlimivv $f wff ps $.
	f2_rexlimivv $f set x $.
	f3_rexlimivv $f set y $.
	f4_rexlimivv $f class A $.
	f5_rexlimivv $f class B $.
	e0_rexlimivv $e |- ( ( x e. A /\ y e. B ) -> ( ph -> ps ) ) $.
	p_rexlimivv $p |- ( E. x e. A E. y e. B ph -> ps ) $= e0_rexlimivv f2_rexlimivv a_sup_set_class f4_rexlimivv a_wcel f0_rexlimivv f1_rexlimivv f3_rexlimivv f5_rexlimivv p_rexlimdva f0_rexlimivv f3_rexlimivv f5_rexlimivv a_wrex f1_rexlimivv f2_rexlimivv f4_rexlimivv p_rexlimiv $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 22-Jul-2004.) $)

${
	$v ph ps ch x y A B  $.
	$d x y ph  $.
	$d x y ch  $.
	$d y A  $.
	f0_rexlimdvv $f wff ph $.
	f1_rexlimdvv $f wff ps $.
	f2_rexlimdvv $f wff ch $.
	f3_rexlimdvv $f set x $.
	f4_rexlimdvv $f set y $.
	f5_rexlimdvv $f class A $.
	f6_rexlimdvv $f class B $.
	e0_rexlimdvv $e |- ( ph -> ( ( x e. A /\ y e. B ) -> ( ps -> ch ) ) ) $.
	p_rexlimdvv $p |- ( ph -> ( E. x e. A E. y e. B ps -> ch ) ) $= e0_rexlimdvv f0_rexlimdvv f3_rexlimdvv a_sup_set_class f5_rexlimdvv a_wcel f4_rexlimdvv a_sup_set_class f6_rexlimdvv a_wcel f1_rexlimdvv f2_rexlimdvv a_wi p_expdimp f0_rexlimdvv f3_rexlimdvv a_sup_set_class f5_rexlimdvv a_wcel a_wa f1_rexlimdvv f2_rexlimdvv f4_rexlimdvv f6_rexlimdvv p_rexlimdv f0_rexlimdvv f1_rexlimdvv f4_rexlimdvv f6_rexlimdvv a_wrex f2_rexlimdvv f3_rexlimdvv f5_rexlimdvv p_rexlimdva $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 18-Jun-2014.) $)

${
	$v ph ps ch x y A B  $.
	$d x y ph  $.
	$d x y ch  $.
	$d y A  $.
	f0_rexlimdvva $f wff ph $.
	f1_rexlimdvva $f wff ps $.
	f2_rexlimdvva $f wff ch $.
	f3_rexlimdvva $f set x $.
	f4_rexlimdvva $f set y $.
	f5_rexlimdvva $f class A $.
	f6_rexlimdvva $f class B $.
	e0_rexlimdvva $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) ) $.
	p_rexlimdvva $p |- ( ph -> ( E. x e. A E. y e. B ps -> ch ) ) $= e0_rexlimdvva f0_rexlimdvva f3_rexlimdvva a_sup_set_class f5_rexlimdvva a_wcel f4_rexlimdvva a_sup_set_class f6_rexlimdvva a_wcel a_wa f1_rexlimdvva f2_rexlimdvva a_wi p_ex f0_rexlimdvva f1_rexlimdvva f2_rexlimdvva f3_rexlimdvva f4_rexlimdvva f5_rexlimdvva f6_rexlimdvva p_rexlimdvv $.
$}

$(Theorem 19.26 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by NM, 28-Jan-1997.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)

${
	$v ph ps x A  $.
	f0_r19.26 $f wff ph $.
	f1_r19.26 $f wff ps $.
	f2_r19.26 $f set x $.
	f3_r19.26 $f class A $.
	p_r19.26 $p |- ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. x e. A ps ) ) $= f0_r19.26 f1_r19.26 p_simpl f0_r19.26 f1_r19.26 a_wa f0_r19.26 f2_r19.26 f3_r19.26 p_ralimi f0_r19.26 f1_r19.26 p_simpr f0_r19.26 f1_r19.26 a_wa f1_r19.26 f2_r19.26 f3_r19.26 p_ralimi f0_r19.26 f1_r19.26 a_wa f2_r19.26 f3_r19.26 a_wral f0_r19.26 f2_r19.26 f3_r19.26 a_wral f1_r19.26 f2_r19.26 f3_r19.26 a_wral p_jca f0_r19.26 f1_r19.26 p_pm3.2 f0_r19.26 f1_r19.26 f0_r19.26 f1_r19.26 a_wa f2_r19.26 f3_r19.26 p_ral2imi f0_r19.26 f2_r19.26 f3_r19.26 a_wral f1_r19.26 f2_r19.26 f3_r19.26 a_wral f0_r19.26 f1_r19.26 a_wa f2_r19.26 f3_r19.26 a_wral p_imp f0_r19.26 f1_r19.26 a_wa f2_r19.26 f3_r19.26 a_wral f0_r19.26 f2_r19.26 f3_r19.26 a_wral f1_r19.26 f2_r19.26 f3_r19.26 a_wral a_wa p_impbii $.
$}

$(Theorem 19.26 of [Margaris] p. 90 with 2 restricted quantifiers.
     (Contributed by NM, 10-Aug-2004.) $)

${
	$v ph ps x y A B  $.
	f0_r19.26-2 $f wff ph $.
	f1_r19.26-2 $f wff ps $.
	f2_r19.26-2 $f set x $.
	f3_r19.26-2 $f set y $.
	f4_r19.26-2 $f class A $.
	f5_r19.26-2 $f class B $.
	p_r19.26-2 $p |- ( A. x e. A A. y e. B ( ph /\ ps ) <-> ( A. x e. A A. y e. B ph /\ A. x e. A A. y e. B ps ) ) $= f0_r19.26-2 f1_r19.26-2 f3_r19.26-2 f5_r19.26-2 p_r19.26 f0_r19.26-2 f1_r19.26-2 a_wa f3_r19.26-2 f5_r19.26-2 a_wral f0_r19.26-2 f3_r19.26-2 f5_r19.26-2 a_wral f1_r19.26-2 f3_r19.26-2 f5_r19.26-2 a_wral a_wa f2_r19.26-2 f4_r19.26-2 p_ralbii f0_r19.26-2 f3_r19.26-2 f5_r19.26-2 a_wral f1_r19.26-2 f3_r19.26-2 f5_r19.26-2 a_wral f2_r19.26-2 f4_r19.26-2 p_r19.26 f0_r19.26-2 f1_r19.26-2 a_wa f3_r19.26-2 f5_r19.26-2 a_wral f2_r19.26-2 f4_r19.26-2 a_wral f0_r19.26-2 f3_r19.26-2 f5_r19.26-2 a_wral f1_r19.26-2 f3_r19.26-2 f5_r19.26-2 a_wral a_wa f2_r19.26-2 f4_r19.26-2 a_wral f0_r19.26-2 f3_r19.26-2 f5_r19.26-2 a_wral f2_r19.26-2 f4_r19.26-2 a_wral f1_r19.26-2 f3_r19.26-2 f5_r19.26-2 a_wral f2_r19.26-2 f4_r19.26-2 a_wral a_wa p_bitri $.
$}

$(Theorem 19.26 of [Margaris] p. 90 with 3 restricted quantifiers.
     (Contributed by FL, 22-Nov-2010.) $)

${
	$v ph ps ch x A  $.
	f0_r19.26-3 $f wff ph $.
	f1_r19.26-3 $f wff ps $.
	f2_r19.26-3 $f wff ch $.
	f3_r19.26-3 $f set x $.
	f4_r19.26-3 $f class A $.
	p_r19.26-3 $p |- ( A. x e. A ( ph /\ ps /\ ch ) <-> ( A. x e. A ph /\ A. x e. A ps /\ A. x e. A ch ) ) $= f0_r19.26-3 f1_r19.26-3 f2_r19.26-3 a_df-3an f0_r19.26-3 f1_r19.26-3 f2_r19.26-3 a_w3a f0_r19.26-3 f1_r19.26-3 a_wa f2_r19.26-3 a_wa f3_r19.26-3 f4_r19.26-3 p_ralbii f0_r19.26-3 f1_r19.26-3 a_wa f2_r19.26-3 f3_r19.26-3 f4_r19.26-3 p_r19.26 f0_r19.26-3 f1_r19.26-3 f3_r19.26-3 f4_r19.26-3 p_r19.26 f0_r19.26-3 f1_r19.26-3 a_wa f3_r19.26-3 f4_r19.26-3 a_wral f0_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral f1_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral a_wa f2_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral p_anbi1i f0_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral f1_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral f2_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral a_df-3an f0_r19.26-3 f1_r19.26-3 a_wa f3_r19.26-3 f4_r19.26-3 a_wral f2_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral a_wa f0_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral f1_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral a_wa f2_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral a_wa f0_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral f1_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral f2_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral a_w3a p_bitr4i f0_r19.26-3 f1_r19.26-3 f2_r19.26-3 a_w3a f3_r19.26-3 f4_r19.26-3 a_wral f0_r19.26-3 f1_r19.26-3 a_wa f2_r19.26-3 a_wa f3_r19.26-3 f4_r19.26-3 a_wral f0_r19.26-3 f1_r19.26-3 a_wa f3_r19.26-3 f4_r19.26-3 a_wral f2_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral a_wa f0_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral f1_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral f2_r19.26-3 f3_r19.26-3 f4_r19.26-3 a_wral a_w3a p_3bitri $.
$}

$(Theorem 19.26 of [Margaris] p. 90 with mixed quantifiers.  (Contributed by
     NM, 22-Feb-2004.) $)

${
	$v ph ps x A B  $.
	f0_r19.26m $f wff ph $.
	f1_r19.26m $f wff ps $.
	f2_r19.26m $f set x $.
	f3_r19.26m $f class A $.
	f4_r19.26m $f class B $.
	p_r19.26m $p |- ( A. x ( ( x e. A -> ph ) /\ ( x e. B -> ps ) ) <-> ( A. x e. A ph /\ A. x e. B ps ) ) $= f2_r19.26m a_sup_set_class f3_r19.26m a_wcel f0_r19.26m a_wi f2_r19.26m a_sup_set_class f4_r19.26m a_wcel f1_r19.26m a_wi f2_r19.26m p_19.26 f0_r19.26m f2_r19.26m f3_r19.26m a_df-ral f1_r19.26m f2_r19.26m f4_r19.26m a_df-ral f0_r19.26m f2_r19.26m f3_r19.26m a_wral f2_r19.26m a_sup_set_class f3_r19.26m a_wcel f0_r19.26m a_wi f2_r19.26m a_wal f1_r19.26m f2_r19.26m f4_r19.26m a_wral f2_r19.26m a_sup_set_class f4_r19.26m a_wcel f1_r19.26m a_wi f2_r19.26m a_wal p_anbi12i f2_r19.26m a_sup_set_class f3_r19.26m a_wcel f0_r19.26m a_wi f2_r19.26m a_sup_set_class f4_r19.26m a_wcel f1_r19.26m a_wi a_wa f2_r19.26m a_wal f2_r19.26m a_sup_set_class f3_r19.26m a_wcel f0_r19.26m a_wi f2_r19.26m a_wal f2_r19.26m a_sup_set_class f4_r19.26m a_wcel f1_r19.26m a_wi f2_r19.26m a_wal a_wa f0_r19.26m f2_r19.26m f3_r19.26m a_wral f1_r19.26m f2_r19.26m f4_r19.26m a_wral a_wa p_bitr4i $.
$}

$(Distribute a restricted universal quantifier over a biconditional.
     Theorem 19.15 of [Margaris] p. 90 with restricted quantification.
     (Contributed by NM, 6-Oct-2003.) $)

${
	$v ph ps x A  $.
	f0_ralbi $f wff ph $.
	f1_ralbi $f wff ps $.
	f2_ralbi $f set x $.
	f3_ralbi $f class A $.
	p_ralbi $p |- ( A. x e. A ( ph <-> ps ) -> ( A. x e. A ph <-> A. x e. A ps ) ) $= f0_ralbi f1_ralbi a_wb f2_ralbi f3_ralbi p_nfra1 f0_ralbi f1_ralbi a_wb f2_ralbi f3_ralbi p_rsp f0_ralbi f1_ralbi a_wb f2_ralbi f3_ralbi a_wral f2_ralbi a_sup_set_class f3_ralbi a_wcel f0_ralbi f1_ralbi a_wb p_imp f0_ralbi f1_ralbi a_wb f2_ralbi f3_ralbi a_wral f0_ralbi f1_ralbi f2_ralbi f3_ralbi p_ralbida $.
$}

$(Split a biconditional and distribute quantifier.  (Contributed by NM,
     3-Jun-2012.) $)

${
	$v ph ps x A  $.
	f0_ralbiim $f wff ph $.
	f1_ralbiim $f wff ps $.
	f2_ralbiim $f set x $.
	f3_ralbiim $f class A $.
	p_ralbiim $p |- ( A. x e. A ( ph <-> ps ) <-> ( A. x e. A ( ph -> ps ) /\ A. x e. A ( ps -> ph ) ) ) $= f0_ralbiim f1_ralbiim p_dfbi2 f0_ralbiim f1_ralbiim a_wb f0_ralbiim f1_ralbiim a_wi f1_ralbiim f0_ralbiim a_wi a_wa f2_ralbiim f3_ralbiim p_ralbii f0_ralbiim f1_ralbiim a_wi f1_ralbiim f0_ralbiim a_wi f2_ralbiim f3_ralbiim p_r19.26 f0_ralbiim f1_ralbiim a_wb f2_ralbiim f3_ralbiim a_wral f0_ralbiim f1_ralbiim a_wi f1_ralbiim f0_ralbiim a_wi a_wa f2_ralbiim f3_ralbiim a_wral f0_ralbiim f1_ralbiim a_wi f2_ralbiim f3_ralbiim a_wral f1_ralbiim f0_ralbiim a_wi f2_ralbiim f3_ralbiim a_wral a_wa p_bitri $.
$}

$(Restricted version of one direction of Theorem 19.27 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 3-Jun-2004.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	f0_r19.27av $f wff ph $.
	f1_r19.27av $f wff ps $.
	f2_r19.27av $f set x $.
	f3_r19.27av $f class A $.
	p_r19.27av $p |- ( ( A. x e. A ph /\ ps ) -> A. x e. A ( ph /\ ps ) ) $= f1_r19.27av f2_r19.27av a_sup_set_class f3_r19.27av a_wcel a_ax-1 f1_r19.27av f1_r19.27av f2_r19.27av f3_r19.27av p_ralrimiv f1_r19.27av f1_r19.27av f2_r19.27av f3_r19.27av a_wral f0_r19.27av f2_r19.27av f3_r19.27av a_wral p_anim2i f0_r19.27av f1_r19.27av f2_r19.27av f3_r19.27av p_r19.26 f0_r19.27av f2_r19.27av f3_r19.27av a_wral f1_r19.27av a_wa f0_r19.27av f2_r19.27av f3_r19.27av a_wral f1_r19.27av f2_r19.27av f3_r19.27av a_wral a_wa f0_r19.27av f1_r19.27av a_wa f2_r19.27av f3_r19.27av a_wral p_sylibr $.
$}

$(Restricted version of one direction of Theorem 19.28 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_r19.28av $f wff ph $.
	f1_r19.28av $f wff ps $.
	f2_r19.28av $f set x $.
	f3_r19.28av $f class A $.
	p_r19.28av $p |- ( ( ph /\ A. x e. A ps ) -> A. x e. A ( ph /\ ps ) ) $= f1_r19.28av f0_r19.28av f2_r19.28av f3_r19.28av p_r19.27av f0_r19.28av f1_r19.28av f2_r19.28av f3_r19.28av a_wral p_ancom f0_r19.28av f1_r19.28av p_ancom f0_r19.28av f1_r19.28av a_wa f1_r19.28av f0_r19.28av a_wa f2_r19.28av f3_r19.28av p_ralbii f1_r19.28av f2_r19.28av f3_r19.28av a_wral f0_r19.28av a_wa f1_r19.28av f0_r19.28av a_wa f2_r19.28av f3_r19.28av a_wral f0_r19.28av f1_r19.28av f2_r19.28av f3_r19.28av a_wral a_wa f0_r19.28av f1_r19.28av a_wa f2_r19.28av f3_r19.28av a_wral p_3imtr4i $.
$}

$(Theorem 19.29 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by NM, 31-Aug-1999.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)

${
	$v ph ps x A  $.
	f0_r19.29 $f wff ph $.
	f1_r19.29 $f wff ps $.
	f2_r19.29 $f set x $.
	f3_r19.29 $f class A $.
	p_r19.29 $p |- ( ( A. x e. A ph /\ E. x e. A ps ) -> E. x e. A ( ph /\ ps ) ) $= f0_r19.29 f1_r19.29 p_pm3.2 f0_r19.29 f1_r19.29 f0_r19.29 f1_r19.29 a_wa a_wi f2_r19.29 f3_r19.29 p_ralimi f1_r19.29 f0_r19.29 f1_r19.29 a_wa f2_r19.29 f3_r19.29 p_rexim f0_r19.29 f2_r19.29 f3_r19.29 a_wral f1_r19.29 f0_r19.29 f1_r19.29 a_wa a_wi f2_r19.29 f3_r19.29 a_wral f1_r19.29 f2_r19.29 f3_r19.29 a_wrex f0_r19.29 f1_r19.29 a_wa f2_r19.29 f3_r19.29 a_wrex a_wi p_syl f0_r19.29 f2_r19.29 f3_r19.29 a_wral f1_r19.29 f2_r19.29 f3_r19.29 a_wrex f0_r19.29 f1_r19.29 a_wa f2_r19.29 f3_r19.29 a_wrex p_imp $.
$}

$(Variation of Theorem 19.29 of [Margaris] p. 90 with restricted
     quantifiers.  (Contributed by NM, 31-Aug-1999.) $)

${
	$v ph ps x A  $.
	f0_r19.29r $f wff ph $.
	f1_r19.29r $f wff ps $.
	f2_r19.29r $f set x $.
	f3_r19.29r $f class A $.
	p_r19.29r $p |- ( ( E. x e. A ph /\ A. x e. A ps ) -> E. x e. A ( ph /\ ps ) ) $= f1_r19.29r f0_r19.29r f2_r19.29r f3_r19.29r p_r19.29 f0_r19.29r f2_r19.29r f3_r19.29r a_wrex f1_r19.29r f2_r19.29r f3_r19.29r a_wral p_ancom f0_r19.29r f1_r19.29r p_ancom f0_r19.29r f1_r19.29r a_wa f1_r19.29r f0_r19.29r a_wa f2_r19.29r f3_r19.29r p_rexbii f1_r19.29r f2_r19.29r f3_r19.29r a_wral f0_r19.29r f2_r19.29r f3_r19.29r a_wrex a_wa f1_r19.29r f0_r19.29r a_wa f2_r19.29r f3_r19.29r a_wrex f0_r19.29r f2_r19.29r f3_r19.29r a_wrex f1_r19.29r f2_r19.29r f3_r19.29r a_wral a_wa f0_r19.29r f1_r19.29r a_wa f2_r19.29r f3_r19.29r a_wrex p_3imtr4i $.
$}

$(Theorem 19.30 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by Scott Fenton, 25-Feb-2011.) $)

${
	$v ph ps x A  $.
	f0_r19.30 $f wff ph $.
	f1_r19.30 $f wff ps $.
	f2_r19.30 $f set x $.
	f3_r19.30 $f class A $.
	p_r19.30 $p |- ( A. x e. A ( ph \/ ps ) -> ( A. x e. A ph \/ E. x e. A ps ) ) $= f1_r19.30 a_wn f0_r19.30 f2_r19.30 f3_r19.30 p_ralim f0_r19.30 f1_r19.30 p_orcom f1_r19.30 f0_r19.30 a_df-or f0_r19.30 f1_r19.30 a_wo f1_r19.30 f0_r19.30 a_wo f1_r19.30 a_wn f0_r19.30 a_wi p_bitri f0_r19.30 f1_r19.30 a_wo f1_r19.30 a_wn f0_r19.30 a_wi f2_r19.30 f3_r19.30 p_ralbii f0_r19.30 f2_r19.30 f3_r19.30 a_wral f1_r19.30 a_wn f2_r19.30 f3_r19.30 a_wral a_wn p_orcom f1_r19.30 f2_r19.30 f3_r19.30 p_dfrex2 f1_r19.30 f2_r19.30 f3_r19.30 a_wrex f1_r19.30 a_wn f2_r19.30 f3_r19.30 a_wral a_wn f0_r19.30 f2_r19.30 f3_r19.30 a_wral p_orbi2i f1_r19.30 a_wn f2_r19.30 f3_r19.30 a_wral f0_r19.30 f2_r19.30 f3_r19.30 a_wral p_imor f0_r19.30 f2_r19.30 f3_r19.30 a_wral f1_r19.30 a_wn f2_r19.30 f3_r19.30 a_wral a_wn a_wo f1_r19.30 a_wn f2_r19.30 f3_r19.30 a_wral a_wn f0_r19.30 f2_r19.30 f3_r19.30 a_wral a_wo f0_r19.30 f2_r19.30 f3_r19.30 a_wral f1_r19.30 f2_r19.30 f3_r19.30 a_wrex a_wo f1_r19.30 a_wn f2_r19.30 f3_r19.30 a_wral f0_r19.30 f2_r19.30 f3_r19.30 a_wral a_wi p_3bitr4i f1_r19.30 a_wn f0_r19.30 a_wi f2_r19.30 f3_r19.30 a_wral f1_r19.30 a_wn f2_r19.30 f3_r19.30 a_wral f0_r19.30 f2_r19.30 f3_r19.30 a_wral a_wi f0_r19.30 f1_r19.30 a_wo f2_r19.30 f3_r19.30 a_wral f0_r19.30 f2_r19.30 f3_r19.30 a_wral f1_r19.30 f2_r19.30 f3_r19.30 a_wrex a_wo p_3imtr4i $.
$}

$(Theorem 19.32 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 25-Nov-2003.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_r19.32v $f wff ph $.
	f1_r19.32v $f wff ps $.
	f2_r19.32v $f set x $.
	f3_r19.32v $f class A $.
	p_r19.32v $p |- ( A. x e. A ( ph \/ ps ) <-> ( ph \/ A. x e. A ps ) ) $= f0_r19.32v a_wn f1_r19.32v f2_r19.32v f3_r19.32v p_r19.21v f0_r19.32v f1_r19.32v a_df-or f0_r19.32v f1_r19.32v a_wo f0_r19.32v a_wn f1_r19.32v a_wi f2_r19.32v f3_r19.32v p_ralbii f0_r19.32v f1_r19.32v f2_r19.32v f3_r19.32v a_wral a_df-or f0_r19.32v a_wn f1_r19.32v a_wi f2_r19.32v f3_r19.32v a_wral f0_r19.32v a_wn f1_r19.32v f2_r19.32v f3_r19.32v a_wral a_wi f0_r19.32v f1_r19.32v a_wo f2_r19.32v f3_r19.32v a_wral f0_r19.32v f1_r19.32v f2_r19.32v f3_r19.32v a_wral a_wo p_3bitr4i $.
$}

$(Restricted quantifier version of Theorem 19.35 of [Margaris] p. 90.
     (Contributed by NM, 20-Sep-2003.) $)

${
	$v ph ps x A  $.
	f0_r19.35 $f wff ph $.
	f1_r19.35 $f wff ps $.
	f2_r19.35 $f set x $.
	f3_r19.35 $f class A $.
	p_r19.35 $p |- ( E. x e. A ( ph -> ps ) <-> ( A. x e. A ph -> E. x e. A ps ) ) $= f0_r19.35 f1_r19.35 a_wn f2_r19.35 f3_r19.35 p_r19.26 f0_r19.35 f1_r19.35 p_annim f0_r19.35 f1_r19.35 a_wn a_wa f0_r19.35 f1_r19.35 a_wi a_wn f2_r19.35 f3_r19.35 p_ralbii f0_r19.35 f2_r19.35 f3_r19.35 a_wral f1_r19.35 a_wn f2_r19.35 f3_r19.35 a_wral a_df-an f0_r19.35 f1_r19.35 a_wn a_wa f2_r19.35 f3_r19.35 a_wral f0_r19.35 f2_r19.35 f3_r19.35 a_wral f1_r19.35 a_wn f2_r19.35 f3_r19.35 a_wral a_wa f0_r19.35 f1_r19.35 a_wi a_wn f2_r19.35 f3_r19.35 a_wral f0_r19.35 f2_r19.35 f3_r19.35 a_wral f1_r19.35 a_wn f2_r19.35 f3_r19.35 a_wral a_wn a_wi a_wn p_3bitr3i f0_r19.35 f1_r19.35 a_wi a_wn f2_r19.35 f3_r19.35 a_wral f0_r19.35 f2_r19.35 f3_r19.35 a_wral f1_r19.35 a_wn f2_r19.35 f3_r19.35 a_wral a_wn a_wi p_con2bii f1_r19.35 f2_r19.35 f3_r19.35 p_dfrex2 f1_r19.35 f2_r19.35 f3_r19.35 a_wrex f1_r19.35 a_wn f2_r19.35 f3_r19.35 a_wral a_wn f0_r19.35 f2_r19.35 f3_r19.35 a_wral p_imbi2i f0_r19.35 f1_r19.35 a_wi f2_r19.35 f3_r19.35 p_dfrex2 f0_r19.35 f2_r19.35 f3_r19.35 a_wral f1_r19.35 a_wn f2_r19.35 f3_r19.35 a_wral a_wn a_wi f0_r19.35 f1_r19.35 a_wi a_wn f2_r19.35 f3_r19.35 a_wral a_wn f0_r19.35 f2_r19.35 f3_r19.35 a_wral f1_r19.35 f2_r19.35 f3_r19.35 a_wrex a_wi f0_r19.35 f1_r19.35 a_wi f2_r19.35 f3_r19.35 a_wrex p_3bitr4ri $.
$}

$(One direction of a restricted quantifier version of Theorem 19.36 of
       [Margaris] p. 90.  The other direction doesn't hold when ` A ` is
       empty.  (Contributed by NM, 22-Oct-2003.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	f0_r19.36av $f wff ph $.
	f1_r19.36av $f wff ps $.
	f2_r19.36av $f set x $.
	f3_r19.36av $f class A $.
	p_r19.36av $p |- ( E. x e. A ( ph -> ps ) -> ( A. x e. A ph -> ps ) ) $= f0_r19.36av f1_r19.36av f2_r19.36av f3_r19.36av p_r19.35 f2_r19.36av a_sup_set_class f3_r19.36av a_wcel f1_r19.36av p_idd f1_r19.36av f1_r19.36av f2_r19.36av f3_r19.36av p_rexlimiv f1_r19.36av f2_r19.36av f3_r19.36av a_wrex f1_r19.36av f0_r19.36av f2_r19.36av f3_r19.36av a_wral p_imim2i f0_r19.36av f1_r19.36av a_wi f2_r19.36av f3_r19.36av a_wrex f0_r19.36av f2_r19.36av f3_r19.36av a_wral f1_r19.36av f2_r19.36av f3_r19.36av a_wrex a_wi f0_r19.36av f2_r19.36av f3_r19.36av a_wral f1_r19.36av a_wi p_sylbi $.
$}

$(Restricted version of one direction of Theorem 19.37 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by FL, 13-May-2012.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)

${
	$v ph ps x A  $.
	f0_r19.37 $f wff ph $.
	f1_r19.37 $f wff ps $.
	f2_r19.37 $f set x $.
	f3_r19.37 $f class A $.
	e0_r19.37 $e |- F/ x ph $.
	p_r19.37 $p |- ( E. x e. A ( ph -> ps ) -> ( ph -> E. x e. A ps ) ) $= f0_r19.37 f1_r19.37 f2_r19.37 f3_r19.37 p_r19.35 e0_r19.37 f0_r19.37 f2_r19.37 a_sup_set_class f3_r19.37 a_wcel a_ax-1 f0_r19.37 f0_r19.37 f2_r19.37 f3_r19.37 p_ralrimi f0_r19.37 f0_r19.37 f2_r19.37 f3_r19.37 a_wral f1_r19.37 f2_r19.37 f3_r19.37 a_wrex p_imim1i f0_r19.37 f1_r19.37 a_wi f2_r19.37 f3_r19.37 a_wrex f0_r19.37 f2_r19.37 f3_r19.37 a_wral f1_r19.37 f2_r19.37 f3_r19.37 a_wrex a_wi f0_r19.37 f1_r19.37 f2_r19.37 f3_r19.37 a_wrex a_wi p_sylbi $.
$}

$(Restricted version of one direction of Theorem 19.37 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_r19.37av $f wff ph $.
	f1_r19.37av $f wff ps $.
	f2_r19.37av $f set x $.
	f3_r19.37av $f class A $.
	p_r19.37av $p |- ( E. x e. A ( ph -> ps ) -> ( ph -> E. x e. A ps ) ) $= f0_r19.37av f2_r19.37av p_nfv f0_r19.37av f1_r19.37av f2_r19.37av f3_r19.37av p_r19.37 $.
$}

$(Restricted quantifier version of Theorem 19.40 of [Margaris] p. 90.
     (Contributed by NM, 2-Apr-2004.) $)

${
	$v ph ps x A  $.
	f0_r19.40 $f wff ph $.
	f1_r19.40 $f wff ps $.
	f2_r19.40 $f set x $.
	f3_r19.40 $f class A $.
	p_r19.40 $p |- ( E. x e. A ( ph /\ ps ) -> ( E. x e. A ph /\ E. x e. A ps ) ) $= f0_r19.40 f1_r19.40 p_simpl f0_r19.40 f1_r19.40 a_wa f0_r19.40 f2_r19.40 f3_r19.40 p_reximi f0_r19.40 f1_r19.40 p_simpr f0_r19.40 f1_r19.40 a_wa f1_r19.40 f2_r19.40 f3_r19.40 p_reximi f0_r19.40 f1_r19.40 a_wa f2_r19.40 f3_r19.40 a_wrex f0_r19.40 f2_r19.40 f3_r19.40 a_wrex f1_r19.40 f2_r19.40 f3_r19.40 a_wrex p_jca $.
$}

$(Restricted quantifier version of Theorem 19.41 of [Margaris] p. 90.
       (Contributed by NM, 1-Nov-2010.) $)

${
	$v ph ps x A  $.
	f0_r19.41 $f wff ph $.
	f1_r19.41 $f wff ps $.
	f2_r19.41 $f set x $.
	f3_r19.41 $f class A $.
	e0_r19.41 $e |- F/ x ps $.
	p_r19.41 $p |- ( E. x e. A ( ph /\ ps ) <-> ( E. x e. A ph /\ ps ) ) $= f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 f1_r19.41 p_anass f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 a_wa f1_r19.41 a_wa f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 f1_r19.41 a_wa a_wa f2_r19.41 p_exbii e0_r19.41 f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 a_wa f1_r19.41 f2_r19.41 p_19.41 f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 f1_r19.41 a_wa a_wa f2_r19.41 a_wex f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 a_wa f1_r19.41 a_wa f2_r19.41 a_wex f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 a_wa f2_r19.41 a_wex f1_r19.41 a_wa p_bitr3i f0_r19.41 f1_r19.41 a_wa f2_r19.41 f3_r19.41 a_df-rex f0_r19.41 f2_r19.41 f3_r19.41 a_df-rex f0_r19.41 f2_r19.41 f3_r19.41 a_wrex f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 a_wa f2_r19.41 a_wex f1_r19.41 p_anbi1i f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 f1_r19.41 a_wa a_wa f2_r19.41 a_wex f2_r19.41 a_sup_set_class f3_r19.41 a_wcel f0_r19.41 a_wa f2_r19.41 a_wex f1_r19.41 a_wa f0_r19.41 f1_r19.41 a_wa f2_r19.41 f3_r19.41 a_wrex f0_r19.41 f2_r19.41 f3_r19.41 a_wrex f1_r19.41 a_wa p_3bitr4i $.
$}

$(Restricted quantifier version of Theorem 19.41 of [Margaris] p. 90.
       (Contributed by NM, 17-Dec-2003.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	f0_r19.41v $f wff ph $.
	f1_r19.41v $f wff ps $.
	f2_r19.41v $f set x $.
	f3_r19.41v $f class A $.
	p_r19.41v $p |- ( E. x e. A ( ph /\ ps ) <-> ( E. x e. A ph /\ ps ) ) $= f1_r19.41v f2_r19.41v p_nfv f0_r19.41v f1_r19.41v f2_r19.41v f3_r19.41v p_r19.41 $.
$}

$(Restricted version of Theorem 19.42 of [Margaris] p. 90.  (Contributed
       by NM, 27-May-1998.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_r19.42v $f wff ph $.
	f1_r19.42v $f wff ps $.
	f2_r19.42v $f set x $.
	f3_r19.42v $f class A $.
	p_r19.42v $p |- ( E. x e. A ( ph /\ ps ) <-> ( ph /\ E. x e. A ps ) ) $= f1_r19.42v f0_r19.42v f2_r19.42v f3_r19.42v p_r19.41v f0_r19.42v f1_r19.42v p_ancom f0_r19.42v f1_r19.42v a_wa f1_r19.42v f0_r19.42v a_wa f2_r19.42v f3_r19.42v p_rexbii f0_r19.42v f1_r19.42v f2_r19.42v f3_r19.42v a_wrex p_ancom f1_r19.42v f0_r19.42v a_wa f2_r19.42v f3_r19.42v a_wrex f1_r19.42v f2_r19.42v f3_r19.42v a_wrex f0_r19.42v a_wa f0_r19.42v f1_r19.42v a_wa f2_r19.42v f3_r19.42v a_wrex f0_r19.42v f1_r19.42v f2_r19.42v f3_r19.42v a_wrex a_wa p_3bitr4i $.
$}

$(Restricted version of Theorem 19.43 of [Margaris] p. 90.  (Contributed by
     NM, 27-May-1998.)  (Proof shortened by Andrew Salmon, 30-May-2011.) $)

${
	$v ph ps x A  $.
	f0_r19.43 $f wff ph $.
	f1_r19.43 $f wff ps $.
	f2_r19.43 $f set x $.
	f3_r19.43 $f class A $.
	p_r19.43 $p |- ( E. x e. A ( ph \/ ps ) <-> ( E. x e. A ph \/ E. x e. A ps ) ) $= f0_r19.43 a_wn f1_r19.43 f2_r19.43 f3_r19.43 p_r19.35 f0_r19.43 f1_r19.43 a_df-or f0_r19.43 f1_r19.43 a_wo f0_r19.43 a_wn f1_r19.43 a_wi f2_r19.43 f3_r19.43 p_rexbii f0_r19.43 f2_r19.43 f3_r19.43 a_wrex f1_r19.43 f2_r19.43 f3_r19.43 a_wrex a_df-or f0_r19.43 f2_r19.43 f3_r19.43 p_ralnex f0_r19.43 a_wn f2_r19.43 f3_r19.43 a_wral f0_r19.43 f2_r19.43 f3_r19.43 a_wrex a_wn f1_r19.43 f2_r19.43 f3_r19.43 a_wrex p_imbi1i f0_r19.43 f2_r19.43 f3_r19.43 a_wrex f1_r19.43 f2_r19.43 f3_r19.43 a_wrex a_wo f0_r19.43 f2_r19.43 f3_r19.43 a_wrex a_wn f1_r19.43 f2_r19.43 f3_r19.43 a_wrex a_wi f0_r19.43 a_wn f2_r19.43 f3_r19.43 a_wral f1_r19.43 f2_r19.43 f3_r19.43 a_wrex a_wi p_bitr4i f0_r19.43 a_wn f1_r19.43 a_wi f2_r19.43 f3_r19.43 a_wrex f0_r19.43 a_wn f2_r19.43 f3_r19.43 a_wral f1_r19.43 f2_r19.43 f3_r19.43 a_wrex a_wi f0_r19.43 f1_r19.43 a_wo f2_r19.43 f3_r19.43 a_wrex f0_r19.43 f2_r19.43 f3_r19.43 a_wrex f1_r19.43 f2_r19.43 f3_r19.43 a_wrex a_wo p_3bitr4i $.
$}

$(One direction of a restricted quantifier version of Theorem 19.44 of
       [Margaris] p. 90.  The other direction doesn't hold when ` A ` is
       empty.  (Contributed by NM, 2-Apr-2004.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	f0_r19.44av $f wff ph $.
	f1_r19.44av $f wff ps $.
	f2_r19.44av $f set x $.
	f3_r19.44av $f class A $.
	p_r19.44av $p |- ( E. x e. A ( ph \/ ps ) -> ( E. x e. A ph \/ ps ) ) $= f0_r19.44av f1_r19.44av f2_r19.44av f3_r19.44av p_r19.43 f2_r19.44av a_sup_set_class f3_r19.44av a_wcel f1_r19.44av p_idd f1_r19.44av f1_r19.44av f2_r19.44av f3_r19.44av p_rexlimiv f1_r19.44av f2_r19.44av f3_r19.44av a_wrex f1_r19.44av f0_r19.44av f2_r19.44av f3_r19.44av a_wrex p_orim2i f0_r19.44av f1_r19.44av a_wo f2_r19.44av f3_r19.44av a_wrex f0_r19.44av f2_r19.44av f3_r19.44av a_wrex f1_r19.44av f2_r19.44av f3_r19.44av a_wrex a_wo f0_r19.44av f2_r19.44av f3_r19.44av a_wrex f1_r19.44av a_wo p_sylbi $.
$}

$(Restricted version of one direction of Theorem 19.45 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	f0_r19.45av $f wff ph $.
	f1_r19.45av $f wff ps $.
	f2_r19.45av $f set x $.
	f3_r19.45av $f class A $.
	p_r19.45av $p |- ( E. x e. A ( ph \/ ps ) -> ( ph \/ E. x e. A ps ) ) $= f0_r19.45av f1_r19.45av f2_r19.45av f3_r19.45av p_r19.43 f2_r19.45av a_sup_set_class f3_r19.45av a_wcel f0_r19.45av p_idd f0_r19.45av f0_r19.45av f2_r19.45av f3_r19.45av p_rexlimiv f0_r19.45av f2_r19.45av f3_r19.45av a_wrex f0_r19.45av f1_r19.45av f2_r19.45av f3_r19.45av a_wrex p_orim1i f0_r19.45av f1_r19.45av a_wo f2_r19.45av f3_r19.45av a_wrex f0_r19.45av f2_r19.45av f3_r19.45av a_wrex f1_r19.45av f2_r19.45av f3_r19.45av a_wrex a_wo f0_r19.45av f1_r19.45av f2_r19.45av f3_r19.45av a_wrex a_wo p_sylbi $.
$}

$(Commutation of restricted quantifiers.  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	f0_ralcomf $f wff ph $.
	f1_ralcomf $f set x $.
	f2_ralcomf $f set y $.
	f3_ralcomf $f class A $.
	f4_ralcomf $f class B $.
	e0_ralcomf $e |- F/_ y A $.
	e1_ralcomf $e |- F/_ x B $.
	p_ralcomf $p |- ( A. x e. A A. y e. B ph <-> A. y e. B A. x e. A ph ) $= f1_ralcomf a_sup_set_class f3_ralcomf a_wcel f2_ralcomf a_sup_set_class f4_ralcomf a_wcel f0_ralcomf p_ancomsimp f1_ralcomf a_sup_set_class f3_ralcomf a_wcel f2_ralcomf a_sup_set_class f4_ralcomf a_wcel a_wa f0_ralcomf a_wi f2_ralcomf a_sup_set_class f4_ralcomf a_wcel f1_ralcomf a_sup_set_class f3_ralcomf a_wcel a_wa f0_ralcomf a_wi f1_ralcomf f2_ralcomf p_2albii f2_ralcomf a_sup_set_class f4_ralcomf a_wcel f1_ralcomf a_sup_set_class f3_ralcomf a_wcel a_wa f0_ralcomf a_wi f1_ralcomf f2_ralcomf p_alcom f1_ralcomf a_sup_set_class f3_ralcomf a_wcel f2_ralcomf a_sup_set_class f4_ralcomf a_wcel a_wa f0_ralcomf a_wi f2_ralcomf a_wal f1_ralcomf a_wal f2_ralcomf a_sup_set_class f4_ralcomf a_wcel f1_ralcomf a_sup_set_class f3_ralcomf a_wcel a_wa f0_ralcomf a_wi f2_ralcomf a_wal f1_ralcomf a_wal f2_ralcomf a_sup_set_class f4_ralcomf a_wcel f1_ralcomf a_sup_set_class f3_ralcomf a_wcel a_wa f0_ralcomf a_wi f1_ralcomf a_wal f2_ralcomf a_wal p_bitri e0_ralcomf f0_ralcomf f1_ralcomf f2_ralcomf f3_ralcomf f4_ralcomf p_r2alf e1_ralcomf f0_ralcomf f2_ralcomf f1_ralcomf f4_ralcomf f3_ralcomf p_r2alf f1_ralcomf a_sup_set_class f3_ralcomf a_wcel f2_ralcomf a_sup_set_class f4_ralcomf a_wcel a_wa f0_ralcomf a_wi f2_ralcomf a_wal f1_ralcomf a_wal f2_ralcomf a_sup_set_class f4_ralcomf a_wcel f1_ralcomf a_sup_set_class f3_ralcomf a_wcel a_wa f0_ralcomf a_wi f1_ralcomf a_wal f2_ralcomf a_wal f0_ralcomf f2_ralcomf f4_ralcomf a_wral f1_ralcomf f3_ralcomf a_wral f0_ralcomf f1_ralcomf f3_ralcomf a_wral f2_ralcomf f4_ralcomf a_wral p_3bitr4i $.
$}

$(Commutation of restricted quantifiers.  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	f0_rexcomf $f wff ph $.
	f1_rexcomf $f set x $.
	f2_rexcomf $f set y $.
	f3_rexcomf $f class A $.
	f4_rexcomf $f class B $.
	e0_rexcomf $e |- F/_ y A $.
	e1_rexcomf $e |- F/_ x B $.
	p_rexcomf $p |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph ) $= f1_rexcomf a_sup_set_class f3_rexcomf a_wcel f2_rexcomf a_sup_set_class f4_rexcomf a_wcel p_ancom f1_rexcomf a_sup_set_class f3_rexcomf a_wcel f2_rexcomf a_sup_set_class f4_rexcomf a_wcel a_wa f2_rexcomf a_sup_set_class f4_rexcomf a_wcel f1_rexcomf a_sup_set_class f3_rexcomf a_wcel a_wa f0_rexcomf p_anbi1i f1_rexcomf a_sup_set_class f3_rexcomf a_wcel f2_rexcomf a_sup_set_class f4_rexcomf a_wcel a_wa f0_rexcomf a_wa f2_rexcomf a_sup_set_class f4_rexcomf a_wcel f1_rexcomf a_sup_set_class f3_rexcomf a_wcel a_wa f0_rexcomf a_wa f1_rexcomf f2_rexcomf p_2exbii f2_rexcomf a_sup_set_class f4_rexcomf a_wcel f1_rexcomf a_sup_set_class f3_rexcomf a_wcel a_wa f0_rexcomf a_wa f1_rexcomf f2_rexcomf p_excom f1_rexcomf a_sup_set_class f3_rexcomf a_wcel f2_rexcomf a_sup_set_class f4_rexcomf a_wcel a_wa f0_rexcomf a_wa f2_rexcomf a_wex f1_rexcomf a_wex f2_rexcomf a_sup_set_class f4_rexcomf a_wcel f1_rexcomf a_sup_set_class f3_rexcomf a_wcel a_wa f0_rexcomf a_wa f2_rexcomf a_wex f1_rexcomf a_wex f2_rexcomf a_sup_set_class f4_rexcomf a_wcel f1_rexcomf a_sup_set_class f3_rexcomf a_wcel a_wa f0_rexcomf a_wa f1_rexcomf a_wex f2_rexcomf a_wex p_bitri e0_rexcomf f0_rexcomf f1_rexcomf f2_rexcomf f3_rexcomf f4_rexcomf p_r2exf e1_rexcomf f0_rexcomf f2_rexcomf f1_rexcomf f4_rexcomf f3_rexcomf p_r2exf f1_rexcomf a_sup_set_class f3_rexcomf a_wcel f2_rexcomf a_sup_set_class f4_rexcomf a_wcel a_wa f0_rexcomf a_wa f2_rexcomf a_wex f1_rexcomf a_wex f2_rexcomf a_sup_set_class f4_rexcomf a_wcel f1_rexcomf a_sup_set_class f3_rexcomf a_wcel a_wa f0_rexcomf a_wa f1_rexcomf a_wex f2_rexcomf a_wex f0_rexcomf f2_rexcomf f4_rexcomf a_wrex f1_rexcomf f3_rexcomf a_wrex f0_rexcomf f1_rexcomf f3_rexcomf a_wrex f2_rexcomf f4_rexcomf a_wrex p_3bitr4i $.
$}

$(Commutation of restricted quantifiers.  (Contributed by NM,
       13-Oct-1999.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	$d x B  $.
	$d y A  $.
	f0_ralcom $f wff ph $.
	f1_ralcom $f set x $.
	f2_ralcom $f set y $.
	f3_ralcom $f class A $.
	f4_ralcom $f class B $.
	p_ralcom $p |- ( A. x e. A A. y e. B ph <-> A. y e. B A. x e. A ph ) $= f2_ralcom f3_ralcom p_nfcv f1_ralcom f4_ralcom p_nfcv f0_ralcom f1_ralcom f2_ralcom f3_ralcom f4_ralcom p_ralcomf $.
$}

$(Commutation of restricted quantifiers.  (Contributed by NM,
       19-Nov-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d x y  $.
	$d x B  $.
	$d y A  $.
	f0_rexcom $f wff ph $.
	f1_rexcom $f set x $.
	f2_rexcom $f set y $.
	f3_rexcom $f class A $.
	f4_rexcom $f class B $.
	p_rexcom $p |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph ) $= f2_rexcom f3_rexcom p_nfcv f1_rexcom f4_rexcom p_nfcv f0_rexcom f1_rexcom f2_rexcom f3_rexcom f4_rexcom p_rexcomf $.
$}

$(Swap 1st and 3rd restricted existential quantifiers.  (Contributed by
       NM, 8-Apr-2015.) $)

${
	$v ph x y z A B C  $.
	$d y z A  $.
	$d x z B  $.
	$d x y C  $.
	f0_rexcom13 $f wff ph $.
	f1_rexcom13 $f set x $.
	f2_rexcom13 $f set y $.
	f3_rexcom13 $f set z $.
	f4_rexcom13 $f class A $.
	f5_rexcom13 $f class B $.
	f6_rexcom13 $f class C $.
	p_rexcom13 $p |- ( E. x e. A E. y e. B E. z e. C ph <-> E. z e. C E. y e. B E. x e. A ph ) $= f0_rexcom13 f3_rexcom13 f6_rexcom13 a_wrex f1_rexcom13 f2_rexcom13 f4_rexcom13 f5_rexcom13 p_rexcom f0_rexcom13 f1_rexcom13 f3_rexcom13 f4_rexcom13 f6_rexcom13 p_rexcom f0_rexcom13 f3_rexcom13 f6_rexcom13 a_wrex f1_rexcom13 f4_rexcom13 a_wrex f0_rexcom13 f1_rexcom13 f4_rexcom13 a_wrex f3_rexcom13 f6_rexcom13 a_wrex f2_rexcom13 f5_rexcom13 p_rexbii f0_rexcom13 f1_rexcom13 f4_rexcom13 a_wrex f2_rexcom13 f3_rexcom13 f5_rexcom13 f6_rexcom13 p_rexcom f0_rexcom13 f3_rexcom13 f6_rexcom13 a_wrex f2_rexcom13 f5_rexcom13 a_wrex f1_rexcom13 f4_rexcom13 a_wrex f0_rexcom13 f3_rexcom13 f6_rexcom13 a_wrex f1_rexcom13 f4_rexcom13 a_wrex f2_rexcom13 f5_rexcom13 a_wrex f0_rexcom13 f1_rexcom13 f4_rexcom13 a_wrex f3_rexcom13 f6_rexcom13 a_wrex f2_rexcom13 f5_rexcom13 a_wrex f0_rexcom13 f1_rexcom13 f4_rexcom13 a_wrex f2_rexcom13 f5_rexcom13 a_wrex f3_rexcom13 f6_rexcom13 a_wrex p_3bitri $.
$}

$(Rotate existential restricted quantifiers twice.  (Contributed by NM,
       8-Apr-2015.) $)

${
	$v ph x y z w A B C D  $.
	$d w z A  $.
	$d w z B  $.
	$d w x y C  $.
	$d x y z D  $.
	f0_rexrot4 $f wff ph $.
	f1_rexrot4 $f set x $.
	f2_rexrot4 $f set y $.
	f3_rexrot4 $f set z $.
	f4_rexrot4 $f set w $.
	f5_rexrot4 $f class A $.
	f6_rexrot4 $f class B $.
	f7_rexrot4 $f class C $.
	f8_rexrot4 $f class D $.
	p_rexrot4 $p |- ( E. x e. A E. y e. B E. z e. C E. w e. D ph <-> E. z e. C E. w e. D E. x e. A E. y e. B ph ) $= f0_rexrot4 f2_rexrot4 f3_rexrot4 f4_rexrot4 f6_rexrot4 f7_rexrot4 f8_rexrot4 p_rexcom13 f0_rexrot4 f4_rexrot4 f8_rexrot4 a_wrex f3_rexrot4 f7_rexrot4 a_wrex f2_rexrot4 f6_rexrot4 a_wrex f0_rexrot4 f2_rexrot4 f6_rexrot4 a_wrex f3_rexrot4 f7_rexrot4 a_wrex f4_rexrot4 f8_rexrot4 a_wrex f1_rexrot4 f5_rexrot4 p_rexbii f0_rexrot4 f2_rexrot4 f6_rexrot4 a_wrex f1_rexrot4 f4_rexrot4 f3_rexrot4 f5_rexrot4 f8_rexrot4 f7_rexrot4 p_rexcom13 f0_rexrot4 f4_rexrot4 f8_rexrot4 a_wrex f3_rexrot4 f7_rexrot4 a_wrex f2_rexrot4 f6_rexrot4 a_wrex f1_rexrot4 f5_rexrot4 a_wrex f0_rexrot4 f2_rexrot4 f6_rexrot4 a_wrex f3_rexrot4 f7_rexrot4 a_wrex f4_rexrot4 f8_rexrot4 a_wrex f1_rexrot4 f5_rexrot4 a_wrex f0_rexrot4 f2_rexrot4 f6_rexrot4 a_wrex f1_rexrot4 f5_rexrot4 a_wrex f4_rexrot4 f8_rexrot4 a_wrex f3_rexrot4 f7_rexrot4 a_wrex p_bitri $.
$}

$(Commutation of restricted quantifiers.  Note that ` x ` and ` y `
       needn't be distinct (this makes the proof longer).  (Contributed by NM,
       24-Nov-1994.)  (Proof shortened by Mario Carneiro, 17-Oct-2016.) $)

${
	$v ph x y A  $.
	$d y A  $.
	$d x A  $.
	f0_ralcom2 $f wff ph $.
	f1_ralcom2 $f set x $.
	f2_ralcom2 $f set y $.
	f3_ralcom2 $f class A $.
	p_ralcom2 $p |- ( A. x e. A A. y e. A ph -> A. y e. A A. x e. A ph ) $= f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class f3_ralcom2 p_eleq1 f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel a_wb f1_ralcom2 p_sps f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class f3_ralcom2 p_eleq1 f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel a_wb f1_ralcom2 p_sps f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 p_imbi1d f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 a_wi f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 a_wi f1_ralcom2 f2_ralcom2 p_dral1 f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 a_wi f1_ralcom2 a_wal f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 a_wi f2_ralcom2 a_wal p_bicomd f0_ralcom2 f2_ralcom2 f3_ralcom2 a_df-ral f0_ralcom2 f1_ralcom2 f3_ralcom2 a_df-ral f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 a_wi f2_ralcom2 a_wal f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 a_wi f1_ralcom2 a_wal f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral p_3bitr4g f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral p_imbi12d f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral a_wi f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral a_wi f1_ralcom2 f2_ralcom2 p_dral1 f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_df-ral f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 f3_ralcom2 a_df-ral f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral a_wi f1_ralcom2 a_wal f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral a_wi f2_ralcom2 a_wal f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 f3_ralcom2 a_wral p_3bitr4g f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 f3_ralcom2 a_wral p_biimpd f1_ralcom2 f2_ralcom2 f2_ralcom2 p_nfnae f0_ralcom2 f1_ralcom2 f2_ralcom2 f3_ralcom2 f3_ralcom2 p_nfra2 f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 p_nfan f1_ralcom2 f2_ralcom2 f1_ralcom2 p_nfnae f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 p_nfra1 f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f1_ralcom2 p_nfan f1_ralcom2 f2_ralcom2 p_nfcvf f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f1_ralcom2 f2_ralcom2 a_sup_set_class a_wnfc f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral p_adantr f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral a_wa f1_ralcom2 f3_ralcom2 p_nfcvd f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral a_wa f1_ralcom2 f2_ralcom2 a_sup_set_class f3_ralcom2 p_nfeld f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral a_wa f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f1_ralcom2 p_nfan1 f0_ralcom2 f1_ralcom2 f2_ralcom2 f3_ralcom2 f3_ralcom2 p_rsp2 f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 p_ancomsd f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 p_expdimp f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f1_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 a_wi f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn p_adantll f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral a_wa f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel a_wa f0_ralcom2 f1_ralcom2 f3_ralcom2 p_ralrimi f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral a_wa f2_ralcom2 a_sup_set_class f3_ralcom2 a_wcel f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral p_ex f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral a_wa f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 f3_ralcom2 p_ralrimi f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal a_wn f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 f3_ralcom2 a_wral p_ex f1_ralcom2 a_sup_set_class f2_ralcom2 a_sup_set_class a_wceq f1_ralcom2 a_wal f0_ralcom2 f2_ralcom2 f3_ralcom2 a_wral f1_ralcom2 f3_ralcom2 a_wral f0_ralcom2 f1_ralcom2 f3_ralcom2 a_wral f2_ralcom2 f3_ralcom2 a_wral a_wi p_pm2.61i $.
$}

$(A commutative law for restricted quantifiers that swaps the domain of
       the restriction.  (Contributed by NM, 22-Feb-2004.) $)

${
	$v ph x A B  $.
	f0_ralcom3 $f wff ph $.
	f1_ralcom3 $f set x $.
	f2_ralcom3 $f class A $.
	f3_ralcom3 $f class B $.
	p_ralcom3 $p |- ( A. x e. A ( x e. B -> ph ) <-> A. x e. B ( x e. A -> ph ) ) $= f1_ralcom3 a_sup_set_class f2_ralcom3 a_wcel f1_ralcom3 a_sup_set_class f3_ralcom3 a_wcel f0_ralcom3 p_pm2.04 f1_ralcom3 a_sup_set_class f3_ralcom3 a_wcel f0_ralcom3 a_wi f1_ralcom3 a_sup_set_class f2_ralcom3 a_wcel f0_ralcom3 a_wi f1_ralcom3 f2_ralcom3 f3_ralcom3 p_ralimi2 f1_ralcom3 a_sup_set_class f3_ralcom3 a_wcel f1_ralcom3 a_sup_set_class f2_ralcom3 a_wcel f0_ralcom3 p_pm2.04 f1_ralcom3 a_sup_set_class f2_ralcom3 a_wcel f0_ralcom3 a_wi f1_ralcom3 a_sup_set_class f3_ralcom3 a_wcel f0_ralcom3 a_wi f1_ralcom3 f3_ralcom3 f2_ralcom3 p_ralimi2 f1_ralcom3 a_sup_set_class f3_ralcom3 a_wcel f0_ralcom3 a_wi f1_ralcom3 f2_ralcom3 a_wral f1_ralcom3 a_sup_set_class f2_ralcom3 a_wcel f0_ralcom3 a_wi f1_ralcom3 f3_ralcom3 a_wral p_impbii $.
$}

$(Rearrange existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Proof shortened by Andrew Salmon, 30-May-2011.) $)

${
	$v ph ps x y A B  $.
	$d y A  $.
	$d x B  $.
	$d x y  $.
	f0_reean $f wff ph $.
	f1_reean $f wff ps $.
	f2_reean $f set x $.
	f3_reean $f set y $.
	f4_reean $f class A $.
	f5_reean $f class B $.
	e0_reean $e |- F/ y ph $.
	e1_reean $e |- F/ x ps $.
	p_reean $p |- ( E. x e. A E. y e. B ( ph /\ ps ) <-> ( E. x e. A ph /\ E. y e. B ps ) ) $= f2_reean a_sup_set_class f4_reean a_wcel f3_reean a_sup_set_class f5_reean a_wcel f0_reean f1_reean p_an4 f2_reean a_sup_set_class f4_reean a_wcel f3_reean a_sup_set_class f5_reean a_wcel a_wa f0_reean f1_reean a_wa a_wa f2_reean a_sup_set_class f4_reean a_wcel f0_reean a_wa f3_reean a_sup_set_class f5_reean a_wcel f1_reean a_wa a_wa f2_reean f3_reean p_2exbii f2_reean a_sup_set_class f4_reean a_wcel f3_reean p_nfv e0_reean f2_reean a_sup_set_class f4_reean a_wcel f0_reean f3_reean p_nfan f3_reean a_sup_set_class f5_reean a_wcel f2_reean p_nfv e1_reean f3_reean a_sup_set_class f5_reean a_wcel f1_reean f2_reean p_nfan f2_reean a_sup_set_class f4_reean a_wcel f0_reean a_wa f3_reean a_sup_set_class f5_reean a_wcel f1_reean a_wa f2_reean f3_reean p_eean f2_reean a_sup_set_class f4_reean a_wcel f3_reean a_sup_set_class f5_reean a_wcel a_wa f0_reean f1_reean a_wa a_wa f3_reean a_wex f2_reean a_wex f2_reean a_sup_set_class f4_reean a_wcel f0_reean a_wa f3_reean a_sup_set_class f5_reean a_wcel f1_reean a_wa a_wa f3_reean a_wex f2_reean a_wex f2_reean a_sup_set_class f4_reean a_wcel f0_reean a_wa f2_reean a_wex f3_reean a_sup_set_class f5_reean a_wcel f1_reean a_wa f3_reean a_wex a_wa p_bitri f0_reean f1_reean a_wa f2_reean f3_reean f4_reean f5_reean p_r2ex f0_reean f2_reean f4_reean a_df-rex f1_reean f3_reean f5_reean a_df-rex f0_reean f2_reean f4_reean a_wrex f2_reean a_sup_set_class f4_reean a_wcel f0_reean a_wa f2_reean a_wex f1_reean f3_reean f5_reean a_wrex f3_reean a_sup_set_class f5_reean a_wcel f1_reean a_wa f3_reean a_wex p_anbi12i f2_reean a_sup_set_class f4_reean a_wcel f3_reean a_sup_set_class f5_reean a_wcel a_wa f0_reean f1_reean a_wa a_wa f3_reean a_wex f2_reean a_wex f2_reean a_sup_set_class f4_reean a_wcel f0_reean a_wa f2_reean a_wex f3_reean a_sup_set_class f5_reean a_wcel f1_reean a_wa f3_reean a_wex a_wa f0_reean f1_reean a_wa f3_reean f5_reean a_wrex f2_reean f4_reean a_wrex f0_reean f2_reean f4_reean a_wrex f1_reean f3_reean f5_reean a_wrex a_wa p_3bitr4i $.
$}

$(Rearrange existential quantifiers.  (Contributed by NM, 9-May-1999.) $)

${
	$v ph ps x y A B  $.
	$d y ph  $.
	$d x ps  $.
	$d x y  $.
	$d y A  $.
	$d x B  $.
	f0_reeanv $f wff ph $.
	f1_reeanv $f wff ps $.
	f2_reeanv $f set x $.
	f3_reeanv $f set y $.
	f4_reeanv $f class A $.
	f5_reeanv $f class B $.
	p_reeanv $p |- ( E. x e. A E. y e. B ( ph /\ ps ) <-> ( E. x e. A ph /\ E. y e. B ps ) ) $= f0_reeanv f3_reeanv p_nfv f1_reeanv f2_reeanv p_nfv f0_reeanv f1_reeanv f2_reeanv f3_reeanv f4_reeanv f5_reeanv p_reean $.
$}

$(Rearrange three existential quantifiers.  (Contributed by Jeff Madsen,
       11-Jun-2010.) $)

${
	$v ph ps ch x y z A B C  $.
	$d ph y z  $.
	$d ps x z  $.
	$d ch x y  $.
	$d A y  $.
	$d B x z  $.
	$d C x y  $.
	f0_3reeanv $f wff ph $.
	f1_3reeanv $f wff ps $.
	f2_3reeanv $f wff ch $.
	f3_3reeanv $f set x $.
	f4_3reeanv $f set y $.
	f5_3reeanv $f set z $.
	f6_3reeanv $f class A $.
	f7_3reeanv $f class B $.
	f8_3reeanv $f class C $.
	p_3reeanv $p |- ( E. x e. A E. y e. B E. z e. C ( ph /\ ps /\ ch ) <-> ( E. x e. A ph /\ E. y e. B ps /\ E. z e. C ch ) ) $= f0_3reeanv f1_3reeanv a_wa f4_3reeanv f7_3reeanv a_wrex f2_3reeanv f5_3reeanv f8_3reeanv a_wrex f3_3reeanv f6_3reeanv p_r19.41v f0_3reeanv f1_3reeanv f3_3reeanv f4_3reeanv f6_3reeanv f7_3reeanv p_reeanv f0_3reeanv f1_3reeanv a_wa f4_3reeanv f7_3reeanv a_wrex f3_3reeanv f6_3reeanv a_wrex f0_3reeanv f3_3reeanv f6_3reeanv a_wrex f1_3reeanv f4_3reeanv f7_3reeanv a_wrex a_wa f2_3reeanv f5_3reeanv f8_3reeanv a_wrex p_anbi1i f0_3reeanv f1_3reeanv a_wa f4_3reeanv f7_3reeanv a_wrex f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_wa f3_3reeanv f6_3reeanv a_wrex f0_3reeanv f1_3reeanv a_wa f4_3reeanv f7_3reeanv a_wrex f3_3reeanv f6_3reeanv a_wrex f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_wa f0_3reeanv f3_3reeanv f6_3reeanv a_wrex f1_3reeanv f4_3reeanv f7_3reeanv a_wrex a_wa f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_wa p_bitri f0_3reeanv f1_3reeanv f2_3reeanv a_df-3an f0_3reeanv f1_3reeanv f2_3reeanv a_w3a f0_3reeanv f1_3reeanv a_wa f2_3reeanv a_wa f4_3reeanv f5_3reeanv f7_3reeanv f8_3reeanv p_2rexbii f0_3reeanv f1_3reeanv a_wa f2_3reeanv f4_3reeanv f5_3reeanv f7_3reeanv f8_3reeanv p_reeanv f0_3reeanv f1_3reeanv f2_3reeanv a_w3a f5_3reeanv f8_3reeanv a_wrex f4_3reeanv f7_3reeanv a_wrex f0_3reeanv f1_3reeanv a_wa f2_3reeanv a_wa f5_3reeanv f8_3reeanv a_wrex f4_3reeanv f7_3reeanv a_wrex f0_3reeanv f1_3reeanv a_wa f4_3reeanv f7_3reeanv a_wrex f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_wa p_bitri f0_3reeanv f1_3reeanv f2_3reeanv a_w3a f5_3reeanv f8_3reeanv a_wrex f4_3reeanv f7_3reeanv a_wrex f0_3reeanv f1_3reeanv a_wa f4_3reeanv f7_3reeanv a_wrex f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_wa f3_3reeanv f6_3reeanv p_rexbii f0_3reeanv f3_3reeanv f6_3reeanv a_wrex f1_3reeanv f4_3reeanv f7_3reeanv a_wrex f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_df-3an f0_3reeanv f1_3reeanv a_wa f4_3reeanv f7_3reeanv a_wrex f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_wa f3_3reeanv f6_3reeanv a_wrex f0_3reeanv f3_3reeanv f6_3reeanv a_wrex f1_3reeanv f4_3reeanv f7_3reeanv a_wrex a_wa f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_wa f0_3reeanv f1_3reeanv f2_3reeanv a_w3a f5_3reeanv f8_3reeanv a_wrex f4_3reeanv f7_3reeanv a_wrex f3_3reeanv f6_3reeanv a_wrex f0_3reeanv f3_3reeanv f6_3reeanv a_wrex f1_3reeanv f4_3reeanv f7_3reeanv a_wrex f2_3reeanv f5_3reeanv f8_3reeanv a_wrex a_w3a p_3bitr4i $.
$}

$(Distribute quantification over "or".  (Contributed by Jeff Madsen,
       19-Jun-2010.) $)

${
	$v ph ps x y A B  $.
	$d ph y  $.
	$d ps x  $.
	$d A y  $.
	$d B x  $.
	$d x y  $.
	f0_2ralor $f wff ph $.
	f1_2ralor $f wff ps $.
	f2_2ralor $f set x $.
	f3_2ralor $f set y $.
	f4_2ralor $f class A $.
	f5_2ralor $f class B $.
	p_2ralor $p |- ( A. x e. A A. y e. B ( ph \/ ps ) <-> ( A. x e. A ph \/ A. y e. B ps ) ) $= f0_2ralor f2_2ralor f4_2ralor p_rexnal f1_2ralor f3_2ralor f5_2ralor p_rexnal f0_2ralor a_wn f2_2ralor f4_2ralor a_wrex f0_2ralor f2_2ralor f4_2ralor a_wral a_wn f1_2ralor a_wn f3_2ralor f5_2ralor a_wrex f1_2ralor f3_2ralor f5_2ralor a_wral a_wn p_anbi12i f0_2ralor f1_2ralor p_ioran f0_2ralor f1_2ralor a_wo a_wn f0_2ralor a_wn f1_2ralor a_wn a_wa f3_2ralor f5_2ralor p_rexbii f0_2ralor f1_2ralor a_wo f3_2ralor f5_2ralor p_rexnal f0_2ralor a_wn f1_2ralor a_wn a_wa f3_2ralor f5_2ralor a_wrex f0_2ralor f1_2ralor a_wo a_wn f3_2ralor f5_2ralor a_wrex f0_2ralor f1_2ralor a_wo f3_2ralor f5_2ralor a_wral a_wn p_bitr3i f0_2ralor a_wn f1_2ralor a_wn a_wa f3_2ralor f5_2ralor a_wrex f0_2ralor f1_2ralor a_wo f3_2ralor f5_2ralor a_wral a_wn f2_2ralor f4_2ralor p_rexbii f0_2ralor a_wn f1_2ralor a_wn f2_2ralor f3_2ralor f4_2ralor f5_2ralor p_reeanv f0_2ralor f1_2ralor a_wo f3_2ralor f5_2ralor a_wral f2_2ralor f4_2ralor p_rexnal f0_2ralor a_wn f1_2ralor a_wn a_wa f3_2ralor f5_2ralor a_wrex f2_2ralor f4_2ralor a_wrex f0_2ralor f1_2ralor a_wo f3_2ralor f5_2ralor a_wral a_wn f2_2ralor f4_2ralor a_wrex f0_2ralor a_wn f2_2ralor f4_2ralor a_wrex f1_2ralor a_wn f3_2ralor f5_2ralor a_wrex a_wa f0_2ralor f1_2ralor a_wo f3_2ralor f5_2ralor a_wral f2_2ralor f4_2ralor a_wral a_wn p_3bitr3ri f0_2ralor f2_2ralor f4_2ralor a_wral f1_2ralor f3_2ralor f5_2ralor a_wral p_ioran f0_2ralor a_wn f2_2ralor f4_2ralor a_wrex f1_2ralor a_wn f3_2ralor f5_2ralor a_wrex a_wa f0_2ralor f2_2ralor f4_2ralor a_wral a_wn f1_2ralor f3_2ralor f5_2ralor a_wral a_wn a_wa f0_2ralor f1_2ralor a_wo f3_2ralor f5_2ralor a_wral f2_2ralor f4_2ralor a_wral a_wn f0_2ralor f2_2ralor f4_2ralor a_wral f1_2ralor f3_2ralor f5_2ralor a_wral a_wo a_wn p_3bitr4i f0_2ralor f1_2ralor a_wo f3_2ralor f5_2ralor a_wral f2_2ralor f4_2ralor a_wral f0_2ralor f2_2ralor f4_2ralor a_wral f1_2ralor f3_2ralor f5_2ralor a_wral a_wo p_con4bii $.
$}

$(` x ` is not free in ` E! x e. A ph ` .  (Contributed by NM,
     19-Mar-1997.) $)

${
	$v ph x A  $.
	f0_nfreu1 $f wff ph $.
	f1_nfreu1 $f set x $.
	f2_nfreu1 $f class A $.
	p_nfreu1 $p |- F/ x E! x e. A ph $= f0_nfreu1 f1_nfreu1 f2_nfreu1 a_df-reu f1_nfreu1 a_sup_set_class f2_nfreu1 a_wcel f0_nfreu1 a_wa f1_nfreu1 p_nfeu1 f0_nfreu1 f1_nfreu1 f2_nfreu1 a_wreu f1_nfreu1 a_sup_set_class f2_nfreu1 a_wcel f0_nfreu1 a_wa f1_nfreu1 a_weu f1_nfreu1 p_nfxfr $.
$}

$(` x ` is not free in ` E* x e. A ph ` .  (Contributed by NM,
     16-Jun-2017.) $)

${
	$v ph x A  $.
	f0_nfrmo1 $f wff ph $.
	f1_nfrmo1 $f set x $.
	f2_nfrmo1 $f class A $.
	p_nfrmo1 $p |- F/ x E* x e. A ph $= f0_nfrmo1 f1_nfrmo1 f2_nfrmo1 a_df-rmo f1_nfrmo1 a_sup_set_class f2_nfrmo1 a_wcel f0_nfrmo1 a_wa f1_nfrmo1 p_nfmo1 f0_nfrmo1 f1_nfrmo1 f2_nfrmo1 a_wrmo f1_nfrmo1 a_sup_set_class f2_nfrmo1 a_wcel f0_nfrmo1 a_wa f1_nfrmo1 a_wmo f1_nfrmo1 p_nfxfr $.
$}

$(Deduction version of ~ nfreu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 8-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d x  $.
	$d y  $.
	$d A  $.
	$d ph  $.
	f0_nfreud $f wff ph $.
	f1_nfreud $f wff ps $.
	f2_nfreud $f set x $.
	f3_nfreud $f set y $.
	f4_nfreud $f class A $.
	e0_nfreud $e |- F/ y ph $.
	e1_nfreud $e |- ( ph -> F/_ x A ) $.
	e2_nfreud $e |- ( ph -> F/ x ps ) $.
	p_nfreud $p |- ( ph -> F/ x E! y e. A ps ) $= f1_nfreud f3_nfreud f4_nfreud a_df-reu e0_nfreud f2_nfreud f3_nfreud p_nfcvf f2_nfreud a_sup_set_class f3_nfreud a_sup_set_class a_wceq f2_nfreud a_wal a_wn f2_nfreud f3_nfreud a_sup_set_class a_wnfc f0_nfreud p_adantl e1_nfreud f0_nfreud f2_nfreud f4_nfreud a_wnfc f2_nfreud a_sup_set_class f3_nfreud a_sup_set_class a_wceq f2_nfreud a_wal a_wn p_adantr f0_nfreud f2_nfreud a_sup_set_class f3_nfreud a_sup_set_class a_wceq f2_nfreud a_wal a_wn a_wa f2_nfreud f3_nfreud a_sup_set_class f4_nfreud p_nfeld e2_nfreud f0_nfreud f1_nfreud f2_nfreud a_wnf f2_nfreud a_sup_set_class f3_nfreud a_sup_set_class a_wceq f2_nfreud a_wal a_wn p_adantr f0_nfreud f2_nfreud a_sup_set_class f3_nfreud a_sup_set_class a_wceq f2_nfreud a_wal a_wn a_wa f3_nfreud a_sup_set_class f4_nfreud a_wcel f1_nfreud f2_nfreud p_nfand f0_nfreud f3_nfreud a_sup_set_class f4_nfreud a_wcel f1_nfreud a_wa f2_nfreud f3_nfreud p_nfeud2 f1_nfreud f3_nfreud f4_nfreud a_wreu f3_nfreud a_sup_set_class f4_nfreud a_wcel f1_nfreud a_wa f3_nfreud a_weu f0_nfreud f2_nfreud p_nfxfrd $.
$}

$(Deduction version of ~ nfrmo .  (Contributed by NM, 17-Jun-2017.) $)

${
	$v ph ps x y A  $.
	$d x  $.
	$d y  $.
	$d A  $.
	$d ph  $.
	f0_nfrmod $f wff ph $.
	f1_nfrmod $f wff ps $.
	f2_nfrmod $f set x $.
	f3_nfrmod $f set y $.
	f4_nfrmod $f class A $.
	e0_nfrmod $e |- F/ y ph $.
	e1_nfrmod $e |- ( ph -> F/_ x A ) $.
	e2_nfrmod $e |- ( ph -> F/ x ps ) $.
	p_nfrmod $p |- ( ph -> F/ x E* y e. A ps ) $= f1_nfrmod f3_nfrmod f4_nfrmod a_df-rmo e0_nfrmod f2_nfrmod f3_nfrmod p_nfcvf f2_nfrmod a_sup_set_class f3_nfrmod a_sup_set_class a_wceq f2_nfrmod a_wal a_wn f2_nfrmod f3_nfrmod a_sup_set_class a_wnfc f0_nfrmod p_adantl e1_nfrmod f0_nfrmod f2_nfrmod f4_nfrmod a_wnfc f2_nfrmod a_sup_set_class f3_nfrmod a_sup_set_class a_wceq f2_nfrmod a_wal a_wn p_adantr f0_nfrmod f2_nfrmod a_sup_set_class f3_nfrmod a_sup_set_class a_wceq f2_nfrmod a_wal a_wn a_wa f2_nfrmod f3_nfrmod a_sup_set_class f4_nfrmod p_nfeld e2_nfrmod f0_nfrmod f1_nfrmod f2_nfrmod a_wnf f2_nfrmod a_sup_set_class f3_nfrmod a_sup_set_class a_wceq f2_nfrmod a_wal a_wn p_adantr f0_nfrmod f2_nfrmod a_sup_set_class f3_nfrmod a_sup_set_class a_wceq f2_nfrmod a_wal a_wn a_wa f3_nfrmod a_sup_set_class f4_nfrmod a_wcel f1_nfrmod f2_nfrmod p_nfand f0_nfrmod f3_nfrmod a_sup_set_class f4_nfrmod a_wcel f1_nfrmod a_wa f2_nfrmod f3_nfrmod p_nfmod2 f1_nfrmod f3_nfrmod f4_nfrmod a_wrmo f3_nfrmod a_sup_set_class f4_nfrmod a_wcel f1_nfrmod a_wa f3_nfrmod a_wmo f0_nfrmod f2_nfrmod p_nfxfrd $.
$}

$(Bound-variable hypothesis builder for restricted uniqueness.
       (Contributed by NM, 30-Oct-2010.)  (Revised by Mario Carneiro,
       8-Oct-2016.) $)

${
	$v ph x y A  $.
	f0_nfreu $f wff ph $.
	f1_nfreu $f set x $.
	f2_nfreu $f set y $.
	f3_nfreu $f class A $.
	e0_nfreu $e |- F/_ x A $.
	e1_nfreu $e |- F/ x ph $.
	p_nfreu $p |- F/ x E! y e. A ph $= f2_nfreu p_nftru e0_nfreu f1_nfreu f3_nfreu a_wnfc a_wtru p_a1i e1_nfreu f0_nfreu f1_nfreu a_wnf a_wtru p_a1i a_wtru f0_nfreu f1_nfreu f2_nfreu f3_nfreu p_nfreud f0_nfreu f2_nfreu f3_nfreu a_wreu f1_nfreu a_wnf p_trud $.
$}

$(Bound-variable hypothesis builder for restricted uniqueness.
       (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph x y A  $.
	f0_nfrmo $f wff ph $.
	f1_nfrmo $f set x $.
	f2_nfrmo $f set y $.
	f3_nfrmo $f class A $.
	e0_nfrmo $e |- F/_ x A $.
	e1_nfrmo $e |- F/ x ph $.
	p_nfrmo $p |- F/ x E* y e. A ph $= f0_nfrmo f2_nfrmo f3_nfrmo a_df-rmo f2_nfrmo p_nftru f1_nfrmo f2_nfrmo p_nfcvf e0_nfrmo f1_nfrmo f3_nfrmo a_wnfc f1_nfrmo a_sup_set_class f2_nfrmo a_sup_set_class a_wceq f1_nfrmo a_wal a_wn p_a1i f1_nfrmo a_sup_set_class f2_nfrmo a_sup_set_class a_wceq f1_nfrmo a_wal a_wn f1_nfrmo f2_nfrmo a_sup_set_class f3_nfrmo p_nfeld e1_nfrmo f0_nfrmo f1_nfrmo a_wnf f1_nfrmo a_sup_set_class f2_nfrmo a_sup_set_class a_wceq f1_nfrmo a_wal a_wn p_a1i f1_nfrmo a_sup_set_class f2_nfrmo a_sup_set_class a_wceq f1_nfrmo a_wal a_wn f2_nfrmo a_sup_set_class f3_nfrmo a_wcel f0_nfrmo f1_nfrmo p_nfand f1_nfrmo a_sup_set_class f2_nfrmo a_sup_set_class a_wceq f1_nfrmo a_wal a_wn f2_nfrmo a_sup_set_class f3_nfrmo a_wcel f0_nfrmo a_wa f1_nfrmo a_wnf a_wtru p_adantl a_wtru f2_nfrmo a_sup_set_class f3_nfrmo a_wcel f0_nfrmo a_wa f1_nfrmo f2_nfrmo p_nfmod2 f2_nfrmo a_sup_set_class f3_nfrmo a_wcel f0_nfrmo a_wa f2_nfrmo a_wmo f1_nfrmo a_wnf p_trud f0_nfrmo f2_nfrmo f3_nfrmo a_wrmo f2_nfrmo a_sup_set_class f3_nfrmo a_wcel f0_nfrmo a_wa f2_nfrmo a_wmo f1_nfrmo p_nfxfr $.
$}

$(An "identity" law of concretion for restricted abstraction.  Special case
     of Definition 2.1 of [Quine] p. 16.  (Contributed by NM, 9-Oct-2003.) $)

${
	$v ph x A  $.
	f0_rabid $f wff ph $.
	f1_rabid $f set x $.
	f2_rabid $f class A $.
	p_rabid $p |- ( x e. { x e. A | ph } <-> ( x e. A /\ ph ) ) $= f0_rabid f1_rabid f2_rabid a_df-rab f1_rabid a_sup_set_class f2_rabid a_wcel f0_rabid a_wa f1_rabid f0_rabid f1_rabid f2_rabid a_crab p_abeq2i $.
$}

$(An "identity" law for restricted class abstraction.  (Contributed by NM,
       9-Oct-2003.)  (Proof shortened by Andrew Salmon, 30-May-2011.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_rabid2 $f wff ph $.
	f1_rabid2 $f set x $.
	f2_rabid2 $f class A $.
	p_rabid2 $p |- ( A = { x e. A | ph } <-> A. x e. A ph ) $= f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wa f1_rabid2 f2_rabid2 p_abeq2 f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 p_pm4.71 f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wi f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wa a_wb f1_rabid2 p_albii f2_rabid2 f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wa f1_rabid2 a_cab a_wceq f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wa a_wb f1_rabid2 a_wal f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wi f1_rabid2 a_wal p_bitr4i f0_rabid2 f1_rabid2 f2_rabid2 a_df-rab f0_rabid2 f1_rabid2 f2_rabid2 a_crab f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wa f1_rabid2 a_cab f2_rabid2 p_eqeq2i f0_rabid2 f1_rabid2 f2_rabid2 a_df-ral f2_rabid2 f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wa f1_rabid2 a_cab a_wceq f1_rabid2 a_sup_set_class f2_rabid2 a_wcel f0_rabid2 a_wi f1_rabid2 a_wal f2_rabid2 f0_rabid2 f1_rabid2 f2_rabid2 a_crab a_wceq f0_rabid2 f1_rabid2 f2_rabid2 a_wral p_3bitr4i $.
$}

$(Equivalent wff's correspond to equal restricted class abstractions.
       Closed theorem form of ~ rabbidva .  (Contributed by NM,
       25-Nov-2013.) $)

${
	$v ps ch x A  $.
	f0_rabbi $f wff ps $.
	f1_rabbi $f wff ch $.
	f2_rabbi $f set x $.
	f3_rabbi $f class A $.
	p_rabbi $p |- ( A. x e. A ( ps <-> ch ) <-> { x e. A | ps } = { x e. A | ch } ) $= f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi a_wa f2_rabbi a_sup_set_class f3_rabbi a_wcel f1_rabbi a_wa f2_rabbi p_abbi f0_rabbi f1_rabbi a_wb f2_rabbi f3_rabbi a_df-ral f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi f1_rabbi p_pm5.32 f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi f1_rabbi a_wb a_wi f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi a_wa f2_rabbi a_sup_set_class f3_rabbi a_wcel f1_rabbi a_wa a_wb f2_rabbi p_albii f0_rabbi f1_rabbi a_wb f2_rabbi f3_rabbi a_wral f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi f1_rabbi a_wb a_wi f2_rabbi a_wal f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi a_wa f2_rabbi a_sup_set_class f3_rabbi a_wcel f1_rabbi a_wa a_wb f2_rabbi a_wal p_bitri f0_rabbi f2_rabbi f3_rabbi a_df-rab f1_rabbi f2_rabbi f3_rabbi a_df-rab f0_rabbi f2_rabbi f3_rabbi a_crab f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi a_wa f2_rabbi a_cab f1_rabbi f2_rabbi f3_rabbi a_crab f2_rabbi a_sup_set_class f3_rabbi a_wcel f1_rabbi a_wa f2_rabbi a_cab p_eqeq12i f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi a_wa f2_rabbi a_sup_set_class f3_rabbi a_wcel f1_rabbi a_wa a_wb f2_rabbi a_wal f2_rabbi a_sup_set_class f3_rabbi a_wcel f0_rabbi a_wa f2_rabbi a_cab f2_rabbi a_sup_set_class f3_rabbi a_wcel f1_rabbi a_wa f2_rabbi a_cab a_wceq f0_rabbi f1_rabbi a_wb f2_rabbi f3_rabbi a_wral f0_rabbi f2_rabbi f3_rabbi a_crab f1_rabbi f2_rabbi f3_rabbi a_crab a_wceq p_3bitr4i $.
$}

$(Swap with a membership relation in a restricted class abstraction.
     (Contributed by NM, 4-Jul-2005.) $)

${
	$v x A B  $.
	f0_rabswap $f set x $.
	f1_rabswap $f class A $.
	f2_rabswap $f class B $.
	p_rabswap $p |- { x e. A | x e. B } = { x e. B | x e. A } $= f0_rabswap a_sup_set_class f1_rabswap a_wcel f0_rabswap a_sup_set_class f2_rabswap a_wcel p_ancom f0_rabswap a_sup_set_class f1_rabswap a_wcel f0_rabswap a_sup_set_class f2_rabswap a_wcel a_wa f0_rabswap a_sup_set_class f2_rabswap a_wcel f0_rabswap a_sup_set_class f1_rabswap a_wcel a_wa f0_rabswap p_abbii f0_rabswap a_sup_set_class f2_rabswap a_wcel f0_rabswap f1_rabswap a_df-rab f0_rabswap a_sup_set_class f1_rabswap a_wcel f0_rabswap f2_rabswap a_df-rab f0_rabswap a_sup_set_class f1_rabswap a_wcel f0_rabswap a_sup_set_class f2_rabswap a_wcel a_wa f0_rabswap a_cab f0_rabswap a_sup_set_class f2_rabswap a_wcel f0_rabswap a_sup_set_class f1_rabswap a_wcel a_wa f0_rabswap a_cab f0_rabswap a_sup_set_class f2_rabswap a_wcel f0_rabswap f1_rabswap a_crab f0_rabswap a_sup_set_class f1_rabswap a_wcel f0_rabswap f2_rabswap a_crab p_3eqtr4i $.
$}

$(The abstraction variable in a restricted class abstraction isn't free.
       (Contributed by NM, 19-Mar-1997.) $)

${
	$v ph x A  $.
	$d x  $.
	f0_nfrab1 $f wff ph $.
	f1_nfrab1 $f set x $.
	f2_nfrab1 $f class A $.
	p_nfrab1 $p |- F/_ x { x e. A | ph } $= f0_nfrab1 f1_nfrab1 f2_nfrab1 a_df-rab f1_nfrab1 a_sup_set_class f2_nfrab1 a_wcel f0_nfrab1 a_wa f1_nfrab1 p_nfab1 f1_nfrab1 f0_nfrab1 f1_nfrab1 f2_nfrab1 a_crab f1_nfrab1 a_sup_set_class f2_nfrab1 a_wcel f0_nfrab1 a_wa f1_nfrab1 a_cab p_nfcxfr $.
$}

$(A variable not free in a wff remains so in a restricted class
       abstraction.  (Contributed by NM, 13-Oct-2003.)  (Revised by Mario
       Carneiro, 9-Oct-2016.) $)

${
	$v ph x y A  $.
	$d x z  $.
	$d y z  $.
	$d z A  $.
	f0_nfrab $f wff ph $.
	f1_nfrab $f set x $.
	f2_nfrab $f set y $.
	f3_nfrab $f class A $.
	i0_nfrab $f set z $.
	e0_nfrab $e |- F/ x ph $.
	e1_nfrab $e |- F/_ x A $.
	p_nfrab $p |- F/_ x { y e. A | ph } $= f0_nfrab f2_nfrab f3_nfrab a_df-rab f2_nfrab p_nftru e1_nfrab f1_nfrab i0_nfrab f3_nfrab p_nfcri i0_nfrab a_sup_set_class f2_nfrab a_sup_set_class f3_nfrab p_eleq1 i0_nfrab a_sup_set_class f3_nfrab a_wcel f2_nfrab a_sup_set_class f3_nfrab a_wcel f1_nfrab f2_nfrab i0_nfrab p_dvelimnf e0_nfrab f0_nfrab f1_nfrab a_wnf f1_nfrab a_sup_set_class f2_nfrab a_sup_set_class a_wceq f1_nfrab a_wal a_wn p_a1i f1_nfrab a_sup_set_class f2_nfrab a_sup_set_class a_wceq f1_nfrab a_wal a_wn f2_nfrab a_sup_set_class f3_nfrab a_wcel f0_nfrab f1_nfrab p_nfand f1_nfrab a_sup_set_class f2_nfrab a_sup_set_class a_wceq f1_nfrab a_wal a_wn f2_nfrab a_sup_set_class f3_nfrab a_wcel f0_nfrab a_wa f1_nfrab a_wnf a_wtru p_adantl a_wtru f2_nfrab a_sup_set_class f3_nfrab a_wcel f0_nfrab a_wa f1_nfrab f2_nfrab p_nfabd2 f1_nfrab f2_nfrab a_sup_set_class f3_nfrab a_wcel f0_nfrab a_wa f2_nfrab a_cab a_wnfc p_trud f1_nfrab f0_nfrab f2_nfrab f3_nfrab a_crab f2_nfrab a_sup_set_class f3_nfrab a_wcel f0_nfrab a_wa f2_nfrab a_cab p_nfcxfr $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by Mario Carneiro, 19-Nov-2016.) $)

${
	$v ph ps ch x A  $.
	f0_reubida $f wff ph $.
	f1_reubida $f wff ps $.
	f2_reubida $f wff ch $.
	f3_reubida $f set x $.
	f4_reubida $f class A $.
	e0_reubida $e |- F/ x ph $.
	e1_reubida $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_reubida $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $= e0_reubida e1_reubida f0_reubida f3_reubida a_sup_set_class f4_reubida a_wcel f1_reubida f2_reubida p_pm5.32da f0_reubida f3_reubida a_sup_set_class f4_reubida a_wcel f1_reubida a_wa f3_reubida a_sup_set_class f4_reubida a_wcel f2_reubida a_wa f3_reubida p_eubid f1_reubida f3_reubida f4_reubida a_df-reu f2_reubida f3_reubida f4_reubida a_df-reu f0_reubida f3_reubida a_sup_set_class f4_reubida a_wcel f1_reubida a_wa f3_reubida a_weu f3_reubida a_sup_set_class f4_reubida a_wcel f2_reubida a_wa f3_reubida a_weu f1_reubida f3_reubida f4_reubida a_wreu f2_reubida f3_reubida f4_reubida a_wreu p_3bitr4g $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 13-Nov-2004.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_reubidva $f wff ph $.
	f1_reubidva $f wff ps $.
	f2_reubidva $f wff ch $.
	f3_reubidva $f set x $.
	f4_reubidva $f class A $.
	e0_reubidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_reubidva $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $= f0_reubidva f3_reubidva p_nfv e0_reubidva f0_reubidva f1_reubidva f2_reubidva f3_reubidva f4_reubidva p_reubida $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 17-Oct-1996.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_reubidv $f wff ph $.
	f1_reubidv $f wff ps $.
	f2_reubidv $f wff ch $.
	f3_reubidv $f set x $.
	f4_reubidv $f class A $.
	e0_reubidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_reubidv $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $= e0_reubidv f0_reubidv f1_reubidv f2_reubidv a_wb f3_reubidv a_sup_set_class f4_reubidv a_wcel p_adantr f0_reubidv f1_reubidv f2_reubidv f3_reubidv f4_reubidv p_reubidva $.
$}

$(Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 14-Nov-2004.) $)

${
	$v ph ps x A  $.
	f0_reubiia $f wff ph $.
	f1_reubiia $f wff ps $.
	f2_reubiia $f set x $.
	f3_reubiia $f class A $.
	e0_reubiia $e |- ( x e. A -> ( ph <-> ps ) ) $.
	p_reubiia $p |- ( E! x e. A ph <-> E! x e. A ps ) $= e0_reubiia f2_reubiia a_sup_set_class f3_reubiia a_wcel f0_reubiia f1_reubiia p_pm5.32i f2_reubiia a_sup_set_class f3_reubiia a_wcel f0_reubiia a_wa f2_reubiia a_sup_set_class f3_reubiia a_wcel f1_reubiia a_wa f2_reubiia p_eubii f0_reubiia f2_reubiia f3_reubiia a_df-reu f1_reubiia f2_reubiia f3_reubiia a_df-reu f2_reubiia a_sup_set_class f3_reubiia a_wcel f0_reubiia a_wa f2_reubiia a_weu f2_reubiia a_sup_set_class f3_reubiia a_wcel f1_reubiia a_wa f2_reubiia a_weu f0_reubiia f2_reubiia f3_reubiia a_wreu f1_reubiia f2_reubiia f3_reubiia a_wreu p_3bitr4i $.
$}

$(Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 22-Oct-1999.) $)

${
	$v ph ps x A  $.
	f0_reubii $f wff ph $.
	f1_reubii $f wff ps $.
	f2_reubii $f set x $.
	f3_reubii $f class A $.
	e0_reubii $e |- ( ph <-> ps ) $.
	p_reubii $p |- ( E! x e. A ph <-> E! x e. A ps ) $= e0_reubii f0_reubii f1_reubii a_wb f2_reubii a_sup_set_class f3_reubii a_wcel p_a1i f0_reubii f1_reubii f2_reubii f3_reubii p_reubiia $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph ps ch x A  $.
	f0_rmobida $f wff ph $.
	f1_rmobida $f wff ps $.
	f2_rmobida $f wff ch $.
	f3_rmobida $f set x $.
	f4_rmobida $f class A $.
	e0_rmobida $e |- F/ x ph $.
	e1_rmobida $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_rmobida $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $= e0_rmobida e1_rmobida f0_rmobida f3_rmobida a_sup_set_class f4_rmobida a_wcel f1_rmobida f2_rmobida p_pm5.32da f0_rmobida f3_rmobida a_sup_set_class f4_rmobida a_wcel f1_rmobida a_wa f3_rmobida a_sup_set_class f4_rmobida a_wcel f2_rmobida a_wa f3_rmobida p_mobid f1_rmobida f3_rmobida f4_rmobida a_df-rmo f2_rmobida f3_rmobida f4_rmobida a_df-rmo f0_rmobida f3_rmobida a_sup_set_class f4_rmobida a_wcel f1_rmobida a_wa f3_rmobida a_wmo f3_rmobida a_sup_set_class f4_rmobida a_wcel f2_rmobida a_wa f3_rmobida a_wmo f1_rmobida f3_rmobida f4_rmobida a_wrmo f2_rmobida f3_rmobida f4_rmobida a_wrmo p_3bitr4g $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_rmobidva $f wff ph $.
	f1_rmobidva $f wff ps $.
	f2_rmobidva $f wff ch $.
	f3_rmobidva $f set x $.
	f4_rmobidva $f class A $.
	e0_rmobidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_rmobidva $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $= f0_rmobidva f3_rmobidva p_nfv e0_rmobidva f0_rmobidva f1_rmobidva f2_rmobidva f3_rmobidva f4_rmobidva p_rmobida $.
$}

$(Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_rmobidv $f wff ph $.
	f1_rmobidv $f wff ps $.
	f2_rmobidv $f wff ch $.
	f3_rmobidv $f set x $.
	f4_rmobidv $f class A $.
	e0_rmobidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_rmobidv $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $= e0_rmobidv f0_rmobidv f1_rmobidv f2_rmobidv a_wb f3_rmobidv a_sup_set_class f4_rmobidv a_wcel p_adantr f0_rmobidv f1_rmobidv f2_rmobidv f3_rmobidv f4_rmobidv p_rmobidva $.
$}

$(Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph ps x A  $.
	f0_rmobiia $f wff ph $.
	f1_rmobiia $f wff ps $.
	f2_rmobiia $f set x $.
	f3_rmobiia $f class A $.
	e0_rmobiia $e |- ( x e. A -> ( ph <-> ps ) ) $.
	p_rmobiia $p |- ( E* x e. A ph <-> E* x e. A ps ) $= e0_rmobiia f2_rmobiia a_sup_set_class f3_rmobiia a_wcel f0_rmobiia f1_rmobiia p_pm5.32i f2_rmobiia a_sup_set_class f3_rmobiia a_wcel f0_rmobiia a_wa f2_rmobiia a_sup_set_class f3_rmobiia a_wcel f1_rmobiia a_wa f2_rmobiia p_mobii f0_rmobiia f2_rmobiia f3_rmobiia a_df-rmo f1_rmobiia f2_rmobiia f3_rmobiia a_df-rmo f2_rmobiia a_sup_set_class f3_rmobiia a_wcel f0_rmobiia a_wa f2_rmobiia a_wmo f2_rmobiia a_sup_set_class f3_rmobiia a_wcel f1_rmobiia a_wa f2_rmobiia a_wmo f0_rmobiia f2_rmobiia f3_rmobiia a_wrmo f1_rmobiia f2_rmobiia f3_rmobiia a_wrmo p_3bitr4i $.
$}

$(Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph ps x A  $.
	f0_rmobii $f wff ph $.
	f1_rmobii $f wff ps $.
	f2_rmobii $f set x $.
	f3_rmobii $f class A $.
	e0_rmobii $e |- ( ph <-> ps ) $.
	p_rmobii $p |- ( E* x e. A ph <-> E* x e. A ps ) $= e0_rmobii f0_rmobii f1_rmobii a_wb f2_rmobii a_sup_set_class f3_rmobii a_wcel p_a1i f0_rmobii f1_rmobii f2_rmobii f3_rmobii p_rmobiia $.
$}

$(Equality theorem for restricted universal quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 7-Mar-2004.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)

${
	$v ph x A B  $.
	$d A  $.
	$d B  $.
	f0_raleqf $f wff ph $.
	f1_raleqf $f set x $.
	f2_raleqf $f class A $.
	f3_raleqf $f class B $.
	e0_raleqf $e |- F/_ x A $.
	e1_raleqf $e |- F/_ x B $.
	p_raleqf $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ph ) ) $= e0_raleqf e1_raleqf f1_raleqf f2_raleqf f3_raleqf p_nfeq f2_raleqf f3_raleqf f1_raleqf a_sup_set_class p_eleq2 f2_raleqf f3_raleqf a_wceq f1_raleqf a_sup_set_class f2_raleqf a_wcel f1_raleqf a_sup_set_class f3_raleqf a_wcel f0_raleqf p_imbi1d f2_raleqf f3_raleqf a_wceq f1_raleqf a_sup_set_class f2_raleqf a_wcel f0_raleqf a_wi f1_raleqf a_sup_set_class f3_raleqf a_wcel f0_raleqf a_wi f1_raleqf p_albid f0_raleqf f1_raleqf f2_raleqf a_df-ral f0_raleqf f1_raleqf f3_raleqf a_df-ral f2_raleqf f3_raleqf a_wceq f1_raleqf a_sup_set_class f2_raleqf a_wcel f0_raleqf a_wi f1_raleqf a_wal f1_raleqf a_sup_set_class f3_raleqf a_wcel f0_raleqf a_wi f1_raleqf a_wal f0_raleqf f1_raleqf f2_raleqf a_wral f0_raleqf f1_raleqf f3_raleqf a_wral p_3bitr4g $.
$}

$(Equality theorem for restricted existential quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 9-Oct-2003.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)

${
	$v ph x A B  $.
	$d A  $.
	$d B  $.
	f0_rexeqf $f wff ph $.
	f1_rexeqf $f set x $.
	f2_rexeqf $f class A $.
	f3_rexeqf $f class B $.
	e0_rexeqf $e |- F/_ x A $.
	e1_rexeqf $e |- F/_ x B $.
	p_rexeqf $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ph ) ) $= e0_rexeqf e1_rexeqf f1_rexeqf f2_rexeqf f3_rexeqf p_nfeq f2_rexeqf f3_rexeqf f1_rexeqf a_sup_set_class p_eleq2 f2_rexeqf f3_rexeqf a_wceq f1_rexeqf a_sup_set_class f2_rexeqf a_wcel f1_rexeqf a_sup_set_class f3_rexeqf a_wcel f0_rexeqf p_anbi1d f2_rexeqf f3_rexeqf a_wceq f1_rexeqf a_sup_set_class f2_rexeqf a_wcel f0_rexeqf a_wa f1_rexeqf a_sup_set_class f3_rexeqf a_wcel f0_rexeqf a_wa f1_rexeqf p_exbid f0_rexeqf f1_rexeqf f2_rexeqf a_df-rex f0_rexeqf f1_rexeqf f3_rexeqf a_df-rex f2_rexeqf f3_rexeqf a_wceq f1_rexeqf a_sup_set_class f2_rexeqf a_wcel f0_rexeqf a_wa f1_rexeqf a_wex f1_rexeqf a_sup_set_class f3_rexeqf a_wcel f0_rexeqf a_wa f1_rexeqf a_wex f0_rexeqf f1_rexeqf f2_rexeqf a_wrex f0_rexeqf f1_rexeqf f3_rexeqf a_wrex p_3bitr4g $.
$}

$(Equality theorem for restricted uniqueness quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 5-Apr-2004.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)

${
	$v ph x A B  $.
	$d A  $.
	$d B  $.
	f0_reueq1f $f wff ph $.
	f1_reueq1f $f set x $.
	f2_reueq1f $f class A $.
	f3_reueq1f $f class B $.
	e0_reueq1f $e |- F/_ x A $.
	e1_reueq1f $e |- F/_ x B $.
	p_reueq1f $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ph ) ) $= e0_reueq1f e1_reueq1f f1_reueq1f f2_reueq1f f3_reueq1f p_nfeq f2_reueq1f f3_reueq1f f1_reueq1f a_sup_set_class p_eleq2 f2_reueq1f f3_reueq1f a_wceq f1_reueq1f a_sup_set_class f2_reueq1f a_wcel f1_reueq1f a_sup_set_class f3_reueq1f a_wcel f0_reueq1f p_anbi1d f2_reueq1f f3_reueq1f a_wceq f1_reueq1f a_sup_set_class f2_reueq1f a_wcel f0_reueq1f a_wa f1_reueq1f a_sup_set_class f3_reueq1f a_wcel f0_reueq1f a_wa f1_reueq1f p_eubid f0_reueq1f f1_reueq1f f2_reueq1f a_df-reu f0_reueq1f f1_reueq1f f3_reueq1f a_df-reu f2_reueq1f f3_reueq1f a_wceq f1_reueq1f a_sup_set_class f2_reueq1f a_wcel f0_reueq1f a_wa f1_reueq1f a_weu f1_reueq1f a_sup_set_class f3_reueq1f a_wcel f0_reueq1f a_wa f1_reueq1f a_weu f0_reueq1f f1_reueq1f f2_reueq1f a_wreu f0_reueq1f f1_reueq1f f3_reueq1f a_wreu p_3bitr4g $.
$}

$(Equality theorem for restricted uniqueness quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph x A B  $.
	$d A  $.
	$d B  $.
	f0_rmoeq1f $f wff ph $.
	f1_rmoeq1f $f set x $.
	f2_rmoeq1f $f class A $.
	f3_rmoeq1f $f class B $.
	e0_rmoeq1f $e |- F/_ x A $.
	e1_rmoeq1f $e |- F/_ x B $.
	p_rmoeq1f $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ph ) ) $= e0_rmoeq1f e1_rmoeq1f f1_rmoeq1f f2_rmoeq1f f3_rmoeq1f p_nfeq f2_rmoeq1f f3_rmoeq1f f1_rmoeq1f a_sup_set_class p_eleq2 f2_rmoeq1f f3_rmoeq1f a_wceq f1_rmoeq1f a_sup_set_class f2_rmoeq1f a_wcel f1_rmoeq1f a_sup_set_class f3_rmoeq1f a_wcel f0_rmoeq1f p_anbi1d f2_rmoeq1f f3_rmoeq1f a_wceq f1_rmoeq1f a_sup_set_class f2_rmoeq1f a_wcel f0_rmoeq1f a_wa f1_rmoeq1f a_sup_set_class f3_rmoeq1f a_wcel f0_rmoeq1f a_wa f1_rmoeq1f p_mobid f0_rmoeq1f f1_rmoeq1f f2_rmoeq1f a_df-rmo f0_rmoeq1f f1_rmoeq1f f3_rmoeq1f a_df-rmo f2_rmoeq1f f3_rmoeq1f a_wceq f1_rmoeq1f a_sup_set_class f2_rmoeq1f a_wcel f0_rmoeq1f a_wa f1_rmoeq1f a_wmo f1_rmoeq1f a_sup_set_class f3_rmoeq1f a_wcel f0_rmoeq1f a_wa f1_rmoeq1f a_wmo f0_rmoeq1f f1_rmoeq1f f2_rmoeq1f a_wrmo f0_rmoeq1f f1_rmoeq1f f3_rmoeq1f a_wrmo p_3bitr4g $.
$}

$(Equality theorem for restricted universal quantifier.  (Contributed by
       NM, 16-Nov-1995.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_raleq $f wff ph $.
	f1_raleq $f set x $.
	f2_raleq $f class A $.
	f3_raleq $f class B $.
	p_raleq $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ph ) ) $= f1_raleq f2_raleq p_nfcv f1_raleq f3_raleq p_nfcv f0_raleq f1_raleq f2_raleq f3_raleq p_raleqf $.
$}

$(Equality theorem for restricted existential quantifier.  (Contributed by
       NM, 29-Oct-1995.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rexeq $f wff ph $.
	f1_rexeq $f set x $.
	f2_rexeq $f class A $.
	f3_rexeq $f class B $.
	p_rexeq $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ph ) ) $= f1_rexeq f2_rexeq p_nfcv f1_rexeq f3_rexeq p_nfcv f0_rexeq f1_rexeq f2_rexeq f3_rexeq p_rexeqf $.
$}

$(Equality theorem for restricted uniqueness quantifier.  (Contributed by
       NM, 5-Apr-2004.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_reueq1 $f wff ph $.
	f1_reueq1 $f set x $.
	f2_reueq1 $f class A $.
	f3_reueq1 $f class B $.
	p_reueq1 $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ph ) ) $= f1_reueq1 f2_reueq1 p_nfcv f1_reueq1 f3_reueq1 p_nfcv f0_reueq1 f1_reueq1 f2_reueq1 f3_reueq1 p_reueq1f $.
$}

$(Equality theorem for restricted uniqueness quantifier.  (Contributed by
       Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rmoeq1 $f wff ph $.
	f1_rmoeq1 $f set x $.
	f2_rmoeq1 $f class A $.
	f3_rmoeq1 $f class B $.
	p_rmoeq1 $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ph ) ) $= f1_rmoeq1 f2_rmoeq1 p_nfcv f1_rmoeq1 f3_rmoeq1 p_nfcv f0_rmoeq1 f1_rmoeq1 f2_rmoeq1 f3_rmoeq1 p_rmoeq1f $.
$}

$(Equality inference for restricted universal qualifier.  (Contributed by
       Paul Chapman, 22-Jun-2011.) $)

${
	$v ph x A B  $.
	$d A x  $.
	$d B x  $.
	f0_raleqi $f wff ph $.
	f1_raleqi $f set x $.
	f2_raleqi $f class A $.
	f3_raleqi $f class B $.
	e0_raleqi $e |- A = B $.
	p_raleqi $p |- ( A. x e. A ph <-> A. x e. B ph ) $= e0_raleqi f0_raleqi f1_raleqi f2_raleqi f3_raleqi p_raleq f2_raleqi f3_raleqi a_wceq f0_raleqi f1_raleqi f2_raleqi a_wral f0_raleqi f1_raleqi f3_raleqi a_wral a_wb a_ax-mp $.
$}

$(Equality inference for restricted existential qualifier.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph x A B  $.
	$d A x  $.
	$d B x  $.
	f0_rexeqi $f wff ph $.
	f1_rexeqi $f set x $.
	f2_rexeqi $f class A $.
	f3_rexeqi $f class B $.
	e0_rexeqi $e |- A = B $.
	p_rexeqi $p |- ( E. x e. A ph <-> E. x e. B ph ) $= e0_rexeqi f0_rexeqi f1_rexeqi f2_rexeqi f3_rexeqi p_rexeq f2_rexeqi f3_rexeqi a_wceq f0_rexeqi f1_rexeqi f2_rexeqi a_wrex f0_rexeqi f1_rexeqi f3_rexeqi a_wrex a_wb a_ax-mp $.
$}

$(Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 13-Nov-2005.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_raleqdv $f wff ph $.
	f1_raleqdv $f wff ps $.
	f2_raleqdv $f set x $.
	f3_raleqdv $f class A $.
	f4_raleqdv $f class B $.
	e0_raleqdv $e |- ( ph -> A = B ) $.
	p_raleqdv $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ps ) ) $= e0_raleqdv f1_raleqdv f2_raleqdv f3_raleqdv f4_raleqdv p_raleq f0_raleqdv f3_raleqdv f4_raleqdv a_wceq f1_raleqdv f2_raleqdv f3_raleqdv a_wral f1_raleqdv f2_raleqdv f4_raleqdv a_wral a_wb p_syl $.
$}

$(Equality deduction for restricted existential quantifier.  (Contributed
       by NM, 14-Jan-2007.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rexeqdv $f wff ph $.
	f1_rexeqdv $f wff ps $.
	f2_rexeqdv $f set x $.
	f3_rexeqdv $f class A $.
	f4_rexeqdv $f class B $.
	e0_rexeqdv $e |- ( ph -> A = B ) $.
	p_rexeqdv $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ps ) ) $= e0_rexeqdv f1_rexeqdv f2_rexeqdv f3_rexeqdv f4_rexeqdv p_rexeq f0_rexeqdv f3_rexeqdv f4_rexeqdv a_wceq f1_rexeqdv f2_rexeqdv f3_rexeqdv a_wrex f1_rexeqdv f2_rexeqdv f4_rexeqdv a_wrex a_wb p_syl $.
$}

$(Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 16-Nov-1995.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_raleqbi1dv $f wff ph $.
	f1_raleqbi1dv $f wff ps $.
	f2_raleqbi1dv $f set x $.
	f3_raleqbi1dv $f class A $.
	f4_raleqbi1dv $f class B $.
	e0_raleqbi1dv $e |- ( A = B -> ( ph <-> ps ) ) $.
	p_raleqbi1dv $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ps ) ) $= f0_raleqbi1dv f2_raleqbi1dv f3_raleqbi1dv f4_raleqbi1dv p_raleq e0_raleqbi1dv f3_raleqbi1dv f4_raleqbi1dv a_wceq f0_raleqbi1dv f1_raleqbi1dv f2_raleqbi1dv f4_raleqbi1dv p_ralbidv f3_raleqbi1dv f4_raleqbi1dv a_wceq f0_raleqbi1dv f2_raleqbi1dv f3_raleqbi1dv a_wral f0_raleqbi1dv f2_raleqbi1dv f4_raleqbi1dv a_wral f1_raleqbi1dv f2_raleqbi1dv f4_raleqbi1dv a_wral p_bitrd $.
$}

$(Equality deduction for restricted existential quantifier.  (Contributed
       by NM, 18-Mar-1997.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rexeqbi1dv $f wff ph $.
	f1_rexeqbi1dv $f wff ps $.
	f2_rexeqbi1dv $f set x $.
	f3_rexeqbi1dv $f class A $.
	f4_rexeqbi1dv $f class B $.
	e0_rexeqbi1dv $e |- ( A = B -> ( ph <-> ps ) ) $.
	p_rexeqbi1dv $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ps ) ) $= f0_rexeqbi1dv f2_rexeqbi1dv f3_rexeqbi1dv f4_rexeqbi1dv p_rexeq e0_rexeqbi1dv f3_rexeqbi1dv f4_rexeqbi1dv a_wceq f0_rexeqbi1dv f1_rexeqbi1dv f2_rexeqbi1dv f4_rexeqbi1dv p_rexbidv f3_rexeqbi1dv f4_rexeqbi1dv a_wceq f0_rexeqbi1dv f2_rexeqbi1dv f3_rexeqbi1dv a_wrex f0_rexeqbi1dv f2_rexeqbi1dv f4_rexeqbi1dv a_wrex f1_rexeqbi1dv f2_rexeqbi1dv f4_rexeqbi1dv a_wrex p_bitrd $.
$}

$(Equality deduction for restricted uniqueness quantifier.  (Contributed
       by NM, 5-Apr-2004.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_reueqd $f wff ph $.
	f1_reueqd $f wff ps $.
	f2_reueqd $f set x $.
	f3_reueqd $f class A $.
	f4_reueqd $f class B $.
	e0_reueqd $e |- ( A = B -> ( ph <-> ps ) ) $.
	p_reueqd $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ps ) ) $= f0_reueqd f2_reueqd f3_reueqd f4_reueqd p_reueq1 e0_reueqd f3_reueqd f4_reueqd a_wceq f0_reueqd f1_reueqd f2_reueqd f4_reueqd p_reubidv f3_reueqd f4_reueqd a_wceq f0_reueqd f2_reueqd f3_reueqd a_wreu f0_reueqd f2_reueqd f4_reueqd a_wreu f1_reueqd f2_reueqd f4_reueqd a_wreu p_bitrd $.
$}

$(Equality deduction for restricted uniqueness quantifier.  (Contributed
       by Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rmoeqd $f wff ph $.
	f1_rmoeqd $f wff ps $.
	f2_rmoeqd $f set x $.
	f3_rmoeqd $f class A $.
	f4_rmoeqd $f class B $.
	e0_rmoeqd $e |- ( A = B -> ( ph <-> ps ) ) $.
	p_rmoeqd $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ps ) ) $= f0_rmoeqd f2_rmoeqd f3_rmoeqd f4_rmoeqd p_rmoeq1 e0_rmoeqd f3_rmoeqd f4_rmoeqd a_wceq f0_rmoeqd f1_rmoeqd f2_rmoeqd f4_rmoeqd p_rmobidv f3_rmoeqd f4_rmoeqd a_wceq f0_rmoeqd f2_rmoeqd f3_rmoeqd a_wrmo f0_rmoeqd f2_rmoeqd f4_rmoeqd a_wrmo f1_rmoeqd f2_rmoeqd f4_rmoeqd a_wrmo p_bitrd $.
$}

$(Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 6-Nov-2007.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_raleqbidv $f wff ph $.
	f1_raleqbidv $f wff ps $.
	f2_raleqbidv $f wff ch $.
	f3_raleqbidv $f set x $.
	f4_raleqbidv $f class A $.
	f5_raleqbidv $f class B $.
	e0_raleqbidv $e |- ( ph -> A = B ) $.
	e1_raleqbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_raleqbidv $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $= e0_raleqbidv f0_raleqbidv f1_raleqbidv f3_raleqbidv f4_raleqbidv f5_raleqbidv p_raleqdv e1_raleqbidv f0_raleqbidv f1_raleqbidv f2_raleqbidv f3_raleqbidv f5_raleqbidv p_ralbidv f0_raleqbidv f1_raleqbidv f3_raleqbidv f4_raleqbidv a_wral f1_raleqbidv f3_raleqbidv f5_raleqbidv a_wral f2_raleqbidv f3_raleqbidv f5_raleqbidv a_wral p_bitrd $.
$}

$(Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 6-Nov-2007.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_rexeqbidv $f wff ph $.
	f1_rexeqbidv $f wff ps $.
	f2_rexeqbidv $f wff ch $.
	f3_rexeqbidv $f set x $.
	f4_rexeqbidv $f class A $.
	f5_rexeqbidv $f class B $.
	e0_rexeqbidv $e |- ( ph -> A = B ) $.
	e1_rexeqbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_rexeqbidv $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $= e0_rexeqbidv f0_rexeqbidv f1_rexeqbidv f3_rexeqbidv f4_rexeqbidv f5_rexeqbidv p_rexeqdv e1_rexeqbidv f0_rexeqbidv f1_rexeqbidv f2_rexeqbidv f3_rexeqbidv f5_rexeqbidv p_rexbidv f0_rexeqbidv f1_rexeqbidv f3_rexeqbidv f4_rexeqbidv a_wrex f1_rexeqbidv f3_rexeqbidv f5_rexeqbidv a_wrex f2_rexeqbidv f3_rexeqbidv f5_rexeqbidv a_wrex p_bitrd $.
$}

$(Equality deduction for restricted universal quantifier.  (Contributed by
       Mario Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_raleqbidva $f wff ph $.
	f1_raleqbidva $f wff ps $.
	f2_raleqbidva $f wff ch $.
	f3_raleqbidva $f set x $.
	f4_raleqbidva $f class A $.
	f5_raleqbidva $f class B $.
	e0_raleqbidva $e |- ( ph -> A = B ) $.
	e1_raleqbidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_raleqbidva $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $= e1_raleqbidva f0_raleqbidva f1_raleqbidva f2_raleqbidva f3_raleqbidva f4_raleqbidva p_ralbidva e0_raleqbidva f0_raleqbidva f2_raleqbidva f3_raleqbidva f4_raleqbidva f5_raleqbidva p_raleqdv f0_raleqbidva f1_raleqbidva f3_raleqbidva f4_raleqbidva a_wral f2_raleqbidva f3_raleqbidva f4_raleqbidva a_wral f2_raleqbidva f3_raleqbidva f5_raleqbidva a_wral p_bitrd $.
$}

$(Equality deduction for restricted universal quantifier.  (Contributed by
       Mario Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_rexeqbidva $f wff ph $.
	f1_rexeqbidva $f wff ps $.
	f2_rexeqbidva $f wff ch $.
	f3_rexeqbidva $f set x $.
	f4_rexeqbidva $f class A $.
	f5_rexeqbidva $f class B $.
	e0_rexeqbidva $e |- ( ph -> A = B ) $.
	e1_rexeqbidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_rexeqbidva $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $= e1_rexeqbidva f0_rexeqbidva f1_rexeqbidva f2_rexeqbidva f3_rexeqbidva f4_rexeqbidva p_rexbidva e0_rexeqbidva f0_rexeqbidva f2_rexeqbidva f3_rexeqbidva f4_rexeqbidva f5_rexeqbidva p_rexeqdv f0_rexeqbidva f1_rexeqbidva f3_rexeqbidva f4_rexeqbidva a_wrex f2_rexeqbidva f3_rexeqbidva f4_rexeqbidva a_wrex f2_rexeqbidva f3_rexeqbidva f5_rexeqbidva a_wrex p_bitrd $.
$}

$(Unrestricted "at most one" implies restricted "at most one".  (Contributed
     by NM, 16-Jun-2017.) $)

${
	$v ph x A  $.
	f0_mormo $f wff ph $.
	f1_mormo $f set x $.
	f2_mormo $f class A $.
	p_mormo $p |- ( E* x ph -> E* x e. A ph ) $= f0_mormo f1_mormo a_sup_set_class f2_mormo a_wcel f1_mormo p_moan f0_mormo f1_mormo f2_mormo a_df-rmo f0_mormo f1_mormo a_wmo f1_mormo a_sup_set_class f2_mormo a_wcel f0_mormo a_wa f1_mormo a_wmo f0_mormo f1_mormo f2_mormo a_wrmo p_sylibr $.
$}

$(Restricted uniqueness in terms of "at most one."  (Contributed by NM,
     23-May-1999.)  (Revised by NM, 16-Jun-2017.) $)

${
	$v ph x A  $.
	f0_reu5 $f wff ph $.
	f1_reu5 $f set x $.
	f2_reu5 $f class A $.
	p_reu5 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ E* x e. A ph ) ) $= f1_reu5 a_sup_set_class f2_reu5 a_wcel f0_reu5 a_wa f1_reu5 p_eu5 f0_reu5 f1_reu5 f2_reu5 a_df-reu f0_reu5 f1_reu5 f2_reu5 a_df-rex f0_reu5 f1_reu5 f2_reu5 a_df-rmo f0_reu5 f1_reu5 f2_reu5 a_wrex f1_reu5 a_sup_set_class f2_reu5 a_wcel f0_reu5 a_wa f1_reu5 a_wex f0_reu5 f1_reu5 f2_reu5 a_wrmo f1_reu5 a_sup_set_class f2_reu5 a_wcel f0_reu5 a_wa f1_reu5 a_wmo p_anbi12i f1_reu5 a_sup_set_class f2_reu5 a_wcel f0_reu5 a_wa f1_reu5 a_weu f1_reu5 a_sup_set_class f2_reu5 a_wcel f0_reu5 a_wa f1_reu5 a_wex f1_reu5 a_sup_set_class f2_reu5 a_wcel f0_reu5 a_wa f1_reu5 a_wmo a_wa f0_reu5 f1_reu5 f2_reu5 a_wreu f0_reu5 f1_reu5 f2_reu5 a_wrex f0_reu5 f1_reu5 f2_reu5 a_wrmo a_wa p_3bitr4i $.
$}

$(Restricted unique existence implies restricted existence.  (Contributed by
     NM, 19-Aug-1999.) $)

${
	$v ph x A  $.
	f0_reurex $f wff ph $.
	f1_reurex $f set x $.
	f2_reurex $f class A $.
	p_reurex $p |- ( E! x e. A ph -> E. x e. A ph ) $= f0_reurex f1_reurex f2_reurex p_reu5 f0_reurex f1_reurex f2_reurex a_wreu f0_reurex f1_reurex f2_reurex a_wrex f0_reurex f1_reurex f2_reurex a_wrmo p_simplbi $.
$}

$(Restricted existential uniqueness implies restricted "at most one."
     (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph x A  $.
	f0_reurmo $f wff ph $.
	f1_reurmo $f set x $.
	f2_reurmo $f class A $.
	p_reurmo $p |- ( E! x e. A ph -> E* x e. A ph ) $= f0_reurmo f1_reurmo f2_reurmo p_reu5 f0_reurmo f1_reurmo f2_reurmo a_wreu f0_reurmo f1_reurmo f2_reurmo a_wrex f0_reurmo f1_reurmo f2_reurmo a_wrmo p_simprbi $.
$}

$(Restricted "at most one" in term of uniqueness.  (Contributed by NM,
     16-Jun-2017.) $)

${
	$v ph x A  $.
	f0_rmo5 $f wff ph $.
	f1_rmo5 $f set x $.
	f2_rmo5 $f class A $.
	p_rmo5 $p |- ( E* x e. A ph <-> ( E. x e. A ph -> E! x e. A ph ) ) $= f1_rmo5 a_sup_set_class f2_rmo5 a_wcel f0_rmo5 a_wa f1_rmo5 a_df-mo f0_rmo5 f1_rmo5 f2_rmo5 a_df-rmo f0_rmo5 f1_rmo5 f2_rmo5 a_df-rex f0_rmo5 f1_rmo5 f2_rmo5 a_df-reu f0_rmo5 f1_rmo5 f2_rmo5 a_wrex f1_rmo5 a_sup_set_class f2_rmo5 a_wcel f0_rmo5 a_wa f1_rmo5 a_wex f0_rmo5 f1_rmo5 f2_rmo5 a_wreu f1_rmo5 a_sup_set_class f2_rmo5 a_wcel f0_rmo5 a_wa f1_rmo5 a_weu p_imbi12i f1_rmo5 a_sup_set_class f2_rmo5 a_wcel f0_rmo5 a_wa f1_rmo5 a_wmo f1_rmo5 a_sup_set_class f2_rmo5 a_wcel f0_rmo5 a_wa f1_rmo5 a_wex f1_rmo5 a_sup_set_class f2_rmo5 a_wcel f0_rmo5 a_wa f1_rmo5 a_weu a_wi f0_rmo5 f1_rmo5 f2_rmo5 a_wrmo f0_rmo5 f1_rmo5 f2_rmo5 a_wrex f0_rmo5 f1_rmo5 f2_rmo5 a_wreu a_wi p_3bitr4i $.
$}

$(Nonexistence implies restricted "at most one".  (Contributed by NM,
     17-Jun-2017.) $)

${
	$v ph x A  $.
	f0_nrexrmo $f wff ph $.
	f1_nrexrmo $f set x $.
	f2_nrexrmo $f class A $.
	p_nrexrmo $p |- ( -. E. x e. A ph -> E* x e. A ph ) $= f0_nrexrmo f1_nrexrmo f2_nrexrmo a_wrex f0_nrexrmo f1_nrexrmo f2_nrexrmo a_wreu p_pm2.21 f0_nrexrmo f1_nrexrmo f2_nrexrmo p_rmo5 f0_nrexrmo f1_nrexrmo f2_nrexrmo a_wrex a_wn f0_nrexrmo f1_nrexrmo f2_nrexrmo a_wrex f0_nrexrmo f1_nrexrmo f2_nrexrmo a_wreu a_wi f0_nrexrmo f1_nrexrmo f2_nrexrmo a_wrmo p_sylibr $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 7-Mar-2004.)  (Revised by Mario Carneiro,
       9-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d x z  $.
	$d y z  $.
	$d z A  $.
	$d z ps  $.
	$d z ph  $.
	f0_cbvralf $f wff ph $.
	f1_cbvralf $f wff ps $.
	f2_cbvralf $f set x $.
	f3_cbvralf $f set y $.
	f4_cbvralf $f class A $.
	i0_cbvralf $f set z $.
	e0_cbvralf $e |- F/_ x A $.
	e1_cbvralf $e |- F/_ y A $.
	e2_cbvralf $e |- F/ y ph $.
	e3_cbvralf $e |- F/ x ps $.
	e4_cbvralf $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvralf $p |- ( A. x e. A ph <-> A. y e. A ps ) $= f2_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf a_wi i0_cbvralf p_nfv e0_cbvralf f2_cbvralf i0_cbvralf f4_cbvralf p_nfcri f0_cbvralf f2_cbvralf i0_cbvralf p_nfs1v i0_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf f2_cbvralf i0_cbvralf a_wsb f2_cbvralf p_nfim f2_cbvralf a_sup_set_class i0_cbvralf a_sup_set_class f4_cbvralf p_eleq1 f0_cbvralf f2_cbvralf i0_cbvralf p_sbequ12 f2_cbvralf a_sup_set_class i0_cbvralf a_sup_set_class a_wceq f2_cbvralf a_sup_set_class f4_cbvralf a_wcel i0_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf f0_cbvralf f2_cbvralf i0_cbvralf a_wsb p_imbi12d f2_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf a_wi i0_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf f2_cbvralf i0_cbvralf a_wsb a_wi f2_cbvralf i0_cbvralf p_cbval e1_cbvralf f3_cbvralf i0_cbvralf f4_cbvralf p_nfcri e2_cbvralf f0_cbvralf f2_cbvralf i0_cbvralf f3_cbvralf p_nfsb i0_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf f2_cbvralf i0_cbvralf a_wsb f3_cbvralf p_nfim f3_cbvralf a_sup_set_class f4_cbvralf a_wcel f1_cbvralf a_wi i0_cbvralf p_nfv i0_cbvralf a_sup_set_class f3_cbvralf a_sup_set_class f4_cbvralf p_eleq1 f0_cbvralf i0_cbvralf f3_cbvralf f2_cbvralf p_sbequ e3_cbvralf e4_cbvralf f0_cbvralf f1_cbvralf f2_cbvralf f3_cbvralf p_sbie i0_cbvralf a_sup_set_class f3_cbvralf a_sup_set_class a_wceq f0_cbvralf f2_cbvralf i0_cbvralf a_wsb f0_cbvralf f2_cbvralf f3_cbvralf a_wsb f1_cbvralf p_syl6bb i0_cbvralf a_sup_set_class f3_cbvralf a_sup_set_class a_wceq i0_cbvralf a_sup_set_class f4_cbvralf a_wcel f3_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf f2_cbvralf i0_cbvralf a_wsb f1_cbvralf p_imbi12d i0_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf f2_cbvralf i0_cbvralf a_wsb a_wi f3_cbvralf a_sup_set_class f4_cbvralf a_wcel f1_cbvralf a_wi i0_cbvralf f3_cbvralf p_cbval f2_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf a_wi f2_cbvralf a_wal i0_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf f2_cbvralf i0_cbvralf a_wsb a_wi i0_cbvralf a_wal f3_cbvralf a_sup_set_class f4_cbvralf a_wcel f1_cbvralf a_wi f3_cbvralf a_wal p_bitri f0_cbvralf f2_cbvralf f4_cbvralf a_df-ral f1_cbvralf f3_cbvralf f4_cbvralf a_df-ral f2_cbvralf a_sup_set_class f4_cbvralf a_wcel f0_cbvralf a_wi f2_cbvralf a_wal f3_cbvralf a_sup_set_class f4_cbvralf a_wcel f1_cbvralf a_wi f3_cbvralf a_wal f0_cbvralf f2_cbvralf f4_cbvralf a_wral f1_cbvralf f3_cbvralf f4_cbvralf a_wral p_3bitr4i $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by FL, 27-Apr-2008.)  (Revised by Mario Carneiro,
       9-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d x  $.
	$d y  $.
	$d A  $.
	$d ps  $.
	$d ph  $.
	f0_cbvrexf $f wff ph $.
	f1_cbvrexf $f wff ps $.
	f2_cbvrexf $f set x $.
	f3_cbvrexf $f set y $.
	f4_cbvrexf $f class A $.
	e0_cbvrexf $e |- F/_ x A $.
	e1_cbvrexf $e |- F/_ y A $.
	e2_cbvrexf $e |- F/ y ph $.
	e3_cbvrexf $e |- F/ x ps $.
	e4_cbvrexf $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrexf $p |- ( E. x e. A ph <-> E. y e. A ps ) $= e0_cbvrexf e1_cbvrexf e2_cbvrexf f0_cbvrexf f3_cbvrexf p_nfn e3_cbvrexf f1_cbvrexf f2_cbvrexf p_nfn e4_cbvrexf f2_cbvrexf a_sup_set_class f3_cbvrexf a_sup_set_class a_wceq f0_cbvrexf f1_cbvrexf p_notbid f0_cbvrexf a_wn f1_cbvrexf a_wn f2_cbvrexf f3_cbvrexf f4_cbvrexf p_cbvralf f0_cbvrexf a_wn f2_cbvrexf f4_cbvrexf a_wral f1_cbvrexf a_wn f3_cbvrexf f4_cbvrexf a_wral p_notbii f0_cbvrexf f2_cbvrexf f4_cbvrexf p_dfrex2 f1_cbvrexf f3_cbvrexf f4_cbvrexf p_dfrex2 f0_cbvrexf a_wn f2_cbvrexf f4_cbvrexf a_wral a_wn f1_cbvrexf a_wn f3_cbvrexf f4_cbvrexf a_wral a_wn f0_cbvrexf f2_cbvrexf f4_cbvrexf a_wrex f1_cbvrexf f3_cbvrexf f4_cbvrexf a_wrex p_3bitr4i $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 31-Jul-2003.) $)

${
	$v ph ps x y A  $.
	$d x A  $.
	$d y A  $.
	$d ph  $.
	$d ps  $.
	f0_cbvral $f wff ph $.
	f1_cbvral $f wff ps $.
	f2_cbvral $f set x $.
	f3_cbvral $f set y $.
	f4_cbvral $f class A $.
	e0_cbvral $e |- F/ y ph $.
	e1_cbvral $e |- F/ x ps $.
	e2_cbvral $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvral $p |- ( A. x e. A ph <-> A. y e. A ps ) $= f2_cbvral f4_cbvral p_nfcv f3_cbvral f4_cbvral p_nfcv e0_cbvral e1_cbvral e2_cbvral f0_cbvral f1_cbvral f2_cbvral f3_cbvral f4_cbvral p_cbvralf $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 31-Jul-2003.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)

${
	$v ph ps x y A  $.
	$d x A  $.
	$d y A  $.
	$d ph  $.
	$d ps  $.
	f0_cbvrex $f wff ph $.
	f1_cbvrex $f wff ps $.
	f2_cbvrex $f set x $.
	f3_cbvrex $f set y $.
	f4_cbvrex $f class A $.
	e0_cbvrex $e |- F/ y ph $.
	e1_cbvrex $e |- F/ x ps $.
	e2_cbvrex $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrex $p |- ( E. x e. A ph <-> E. y e. A ps ) $= f2_cbvrex f4_cbvrex p_nfcv f3_cbvrex f4_cbvrex p_nfcv e0_cbvrex e1_cbvrex e2_cbvrex f0_cbvrex f1_cbvrex f2_cbvrex f3_cbvrex f4_cbvrex p_cbvrexf $.
$}

$(Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d x z A  $.
	$d y z A  $.
	$d z ph  $.
	$d z ps  $.
	f0_cbvreu $f wff ph $.
	f1_cbvreu $f wff ps $.
	f2_cbvreu $f set x $.
	f3_cbvreu $f set y $.
	f4_cbvreu $f class A $.
	i0_cbvreu $f set z $.
	e0_cbvreu $e |- F/ y ph $.
	e1_cbvreu $e |- F/ x ps $.
	e2_cbvreu $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvreu $p |- ( E! x e. A ph <-> E! y e. A ps ) $= f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu a_wa i0_cbvreu p_nfv f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu a_wa f2_cbvreu i0_cbvreu p_sb8eu f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu f2_cbvreu i0_cbvreu p_sban f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu a_wa f2_cbvreu i0_cbvreu a_wsb f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f2_cbvreu i0_cbvreu a_wsb f0_cbvreu f2_cbvreu i0_cbvreu a_wsb a_wa i0_cbvreu p_eubii i0_cbvreu f2_cbvreu f4_cbvreu p_clelsb3 f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f2_cbvreu i0_cbvreu a_wsb i0_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu f2_cbvreu i0_cbvreu a_wsb p_anbi1i f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f2_cbvreu i0_cbvreu a_wsb f0_cbvreu f2_cbvreu i0_cbvreu a_wsb a_wa i0_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu f2_cbvreu i0_cbvreu a_wsb a_wa i0_cbvreu p_eubii i0_cbvreu a_sup_set_class f4_cbvreu a_wcel f3_cbvreu p_nfv e0_cbvreu f0_cbvreu f2_cbvreu i0_cbvreu f3_cbvreu p_nfsb i0_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu f2_cbvreu i0_cbvreu a_wsb f3_cbvreu p_nfan f3_cbvreu a_sup_set_class f4_cbvreu a_wcel f1_cbvreu a_wa i0_cbvreu p_nfv i0_cbvreu a_sup_set_class f3_cbvreu a_sup_set_class f4_cbvreu p_eleq1 f0_cbvreu i0_cbvreu f3_cbvreu f2_cbvreu p_sbequ e1_cbvreu e2_cbvreu f0_cbvreu f1_cbvreu f2_cbvreu f3_cbvreu p_sbie i0_cbvreu a_sup_set_class f3_cbvreu a_sup_set_class a_wceq f0_cbvreu f2_cbvreu i0_cbvreu a_wsb f0_cbvreu f2_cbvreu f3_cbvreu a_wsb f1_cbvreu p_syl6bb i0_cbvreu a_sup_set_class f3_cbvreu a_sup_set_class a_wceq i0_cbvreu a_sup_set_class f4_cbvreu a_wcel f3_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu f2_cbvreu i0_cbvreu a_wsb f1_cbvreu p_anbi12d i0_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu f2_cbvreu i0_cbvreu a_wsb a_wa f3_cbvreu a_sup_set_class f4_cbvreu a_wcel f1_cbvreu a_wa i0_cbvreu f3_cbvreu p_cbveu f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f2_cbvreu i0_cbvreu a_wsb f0_cbvreu f2_cbvreu i0_cbvreu a_wsb a_wa i0_cbvreu a_weu i0_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu f2_cbvreu i0_cbvreu a_wsb a_wa i0_cbvreu a_weu f3_cbvreu a_sup_set_class f4_cbvreu a_wcel f1_cbvreu a_wa f3_cbvreu a_weu p_bitri f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu a_wa f2_cbvreu a_weu f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu a_wa f2_cbvreu i0_cbvreu a_wsb i0_cbvreu a_weu f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f2_cbvreu i0_cbvreu a_wsb f0_cbvreu f2_cbvreu i0_cbvreu a_wsb a_wa i0_cbvreu a_weu f3_cbvreu a_sup_set_class f4_cbvreu a_wcel f1_cbvreu a_wa f3_cbvreu a_weu p_3bitri f0_cbvreu f2_cbvreu f4_cbvreu a_df-reu f1_cbvreu f3_cbvreu f4_cbvreu a_df-reu f2_cbvreu a_sup_set_class f4_cbvreu a_wcel f0_cbvreu a_wa f2_cbvreu a_weu f3_cbvreu a_sup_set_class f4_cbvreu a_wcel f1_cbvreu a_wa f3_cbvreu a_weu f0_cbvreu f2_cbvreu f4_cbvreu a_wreu f1_cbvreu f3_cbvreu f4_cbvreu a_wreu p_3bitr4i $.
$}

$(Change the bound variable of restricted "at most one" using implicit
       substitution.  (Contributed by NM, 16-Jun-2017.) $)

${
	$v ph ps x y A  $.
	$d x A  $.
	$d y A  $.
	$d ph  $.
	$d ps  $.
	f0_cbvrmo $f wff ph $.
	f1_cbvrmo $f wff ps $.
	f2_cbvrmo $f set x $.
	f3_cbvrmo $f set y $.
	f4_cbvrmo $f class A $.
	e0_cbvrmo $e |- F/ y ph $.
	e1_cbvrmo $e |- F/ x ps $.
	e2_cbvrmo $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrmo $p |- ( E* x e. A ph <-> E* y e. A ps ) $= e0_cbvrmo e1_cbvrmo e2_cbvrmo f0_cbvrmo f1_cbvrmo f2_cbvrmo f3_cbvrmo f4_cbvrmo p_cbvrex e0_cbvrmo e1_cbvrmo e2_cbvrmo f0_cbvrmo f1_cbvrmo f2_cbvrmo f3_cbvrmo f4_cbvrmo p_cbvreu f0_cbvrmo f2_cbvrmo f4_cbvrmo a_wrex f1_cbvrmo f3_cbvrmo f4_cbvrmo a_wrex f0_cbvrmo f2_cbvrmo f4_cbvrmo a_wreu f1_cbvrmo f3_cbvrmo f4_cbvrmo a_wreu p_imbi12i f0_cbvrmo f2_cbvrmo f4_cbvrmo p_rmo5 f1_cbvrmo f3_cbvrmo f4_cbvrmo p_rmo5 f0_cbvrmo f2_cbvrmo f4_cbvrmo a_wrex f0_cbvrmo f2_cbvrmo f4_cbvrmo a_wreu a_wi f1_cbvrmo f3_cbvrmo f4_cbvrmo a_wrex f1_cbvrmo f3_cbvrmo f4_cbvrmo a_wreu a_wi f0_cbvrmo f2_cbvrmo f4_cbvrmo a_wrmo f1_cbvrmo f3_cbvrmo f4_cbvrmo a_wrmo p_3bitr4i $.
$}

$(Change the bound variable of a restricted universal quantifier using
       implicit substitution.  (Contributed by NM, 28-Jan-1997.) $)

${
	$v ph ps x y A  $.
	$d x A  $.
	$d y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvralv $f wff ph $.
	f1_cbvralv $f wff ps $.
	f2_cbvralv $f set x $.
	f3_cbvralv $f set y $.
	f4_cbvralv $f class A $.
	e0_cbvralv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvralv $p |- ( A. x e. A ph <-> A. y e. A ps ) $= f0_cbvralv f3_cbvralv p_nfv f1_cbvralv f2_cbvralv p_nfv e0_cbvralv f0_cbvralv f1_cbvralv f2_cbvralv f3_cbvralv f4_cbvralv p_cbvral $.
$}

$(Change the bound variable of a restricted existential quantifier using
       implicit substitution.  (Contributed by NM, 2-Jun-1998.) $)

${
	$v ph ps x y A  $.
	$d x A  $.
	$d y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvrexv $f wff ph $.
	f1_cbvrexv $f wff ps $.
	f2_cbvrexv $f set x $.
	f3_cbvrexv $f set y $.
	f4_cbvrexv $f class A $.
	e0_cbvrexv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrexv $p |- ( E. x e. A ph <-> E. y e. A ps ) $= f0_cbvrexv f3_cbvrexv p_nfv f1_cbvrexv f2_cbvrexv p_nfv e0_cbvrexv f0_cbvrexv f1_cbvrexv f2_cbvrexv f3_cbvrexv f4_cbvrexv p_cbvrex $.
$}

$(Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by NM, 5-Apr-2004.)  (Revised by
       Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d x A  $.
	$d y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvreuv $f wff ph $.
	f1_cbvreuv $f wff ps $.
	f2_cbvreuv $f set x $.
	f3_cbvreuv $f set y $.
	f4_cbvreuv $f class A $.
	e0_cbvreuv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvreuv $p |- ( E! x e. A ph <-> E! y e. A ps ) $= f0_cbvreuv f3_cbvreuv p_nfv f1_cbvreuv f2_cbvreuv p_nfv e0_cbvreuv f0_cbvreuv f1_cbvreuv f2_cbvreuv f3_cbvreuv f4_cbvreuv p_cbvreu $.
$}

$(Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by Alexander van der Vekens,
       17-Jun-2017.) $)

${
	$v ph ps x y A  $.
	$d x A  $.
	$d y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvrmov $f wff ph $.
	f1_cbvrmov $f wff ps $.
	f2_cbvrmov $f set x $.
	f3_cbvrmov $f set y $.
	f4_cbvrmov $f class A $.
	e0_cbvrmov $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrmov $p |- ( E* x e. A ph <-> E* y e. A ps ) $= f0_cbvrmov f3_cbvrmov p_nfv f1_cbvrmov f2_cbvrmov p_nfv e0_cbvrmov f0_cbvrmov f1_cbvrmov f2_cbvrmov f3_cbvrmov f4_cbvrmov p_cbvrmo $.
$}

$(Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution which also changes the quantifier
       domain.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph ps ch x y A B  $.
	$d A y  $.
	$d ps y  $.
	$d B x  $.
	$d ch x  $.
	$d x ph y  $.
	f0_cbvraldva2 $f wff ph $.
	f1_cbvraldva2 $f wff ps $.
	f2_cbvraldva2 $f wff ch $.
	f3_cbvraldva2 $f set x $.
	f4_cbvraldva2 $f set y $.
	f5_cbvraldva2 $f class A $.
	f6_cbvraldva2 $f class B $.
	e0_cbvraldva2 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	e1_cbvraldva2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
	p_cbvraldva2 $p |- ( ph -> ( A. x e. A ps <-> A. y e. B ch ) ) $= f0_cbvraldva2 f3_cbvraldva2 a_sup_set_class f4_cbvraldva2 a_sup_set_class a_wceq p_simpr e1_cbvraldva2 f0_cbvraldva2 f3_cbvraldva2 a_sup_set_class f4_cbvraldva2 a_sup_set_class a_wceq a_wa f3_cbvraldva2 a_sup_set_class f4_cbvraldva2 a_sup_set_class f5_cbvraldva2 f6_cbvraldva2 p_eleq12d e0_cbvraldva2 f0_cbvraldva2 f3_cbvraldva2 a_sup_set_class f4_cbvraldva2 a_sup_set_class a_wceq a_wa f3_cbvraldva2 a_sup_set_class f5_cbvraldva2 a_wcel f4_cbvraldva2 a_sup_set_class f6_cbvraldva2 a_wcel f1_cbvraldva2 f2_cbvraldva2 p_imbi12d f0_cbvraldva2 f3_cbvraldva2 a_sup_set_class f5_cbvraldva2 a_wcel f1_cbvraldva2 a_wi f4_cbvraldva2 a_sup_set_class f6_cbvraldva2 a_wcel f2_cbvraldva2 a_wi f3_cbvraldva2 f4_cbvraldva2 p_cbvaldva f1_cbvraldva2 f3_cbvraldva2 f5_cbvraldva2 a_df-ral f2_cbvraldva2 f4_cbvraldva2 f6_cbvraldva2 a_df-ral f0_cbvraldva2 f3_cbvraldva2 a_sup_set_class f5_cbvraldva2 a_wcel f1_cbvraldva2 a_wi f3_cbvraldva2 a_wal f4_cbvraldva2 a_sup_set_class f6_cbvraldva2 a_wcel f2_cbvraldva2 a_wi f4_cbvraldva2 a_wal f1_cbvraldva2 f3_cbvraldva2 f5_cbvraldva2 a_wral f2_cbvraldva2 f4_cbvraldva2 f6_cbvraldva2 a_wral p_3bitr4g $.
$}

$(Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution which also changes the quantifier
       domain.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph ps ch x y A B  $.
	$d A y  $.
	$d ps y  $.
	$d B x  $.
	$d ch x  $.
	$d x ph y  $.
	f0_cbvrexdva2 $f wff ph $.
	f1_cbvrexdva2 $f wff ps $.
	f2_cbvrexdva2 $f wff ch $.
	f3_cbvrexdva2 $f set x $.
	f4_cbvrexdva2 $f set y $.
	f5_cbvrexdva2 $f class A $.
	f6_cbvrexdva2 $f class B $.
	e0_cbvrexdva2 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	e1_cbvrexdva2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
	p_cbvrexdva2 $p |- ( ph -> ( E. x e. A ps <-> E. y e. B ch ) ) $= f0_cbvrexdva2 f3_cbvrexdva2 a_sup_set_class f4_cbvrexdva2 a_sup_set_class a_wceq p_simpr e1_cbvrexdva2 f0_cbvrexdva2 f3_cbvrexdva2 a_sup_set_class f4_cbvrexdva2 a_sup_set_class a_wceq a_wa f3_cbvrexdva2 a_sup_set_class f4_cbvrexdva2 a_sup_set_class f5_cbvrexdva2 f6_cbvrexdva2 p_eleq12d e0_cbvrexdva2 f0_cbvrexdva2 f3_cbvrexdva2 a_sup_set_class f4_cbvrexdva2 a_sup_set_class a_wceq a_wa f3_cbvrexdva2 a_sup_set_class f5_cbvrexdva2 a_wcel f4_cbvrexdva2 a_sup_set_class f6_cbvrexdva2 a_wcel f1_cbvrexdva2 f2_cbvrexdva2 p_anbi12d f0_cbvrexdva2 f3_cbvrexdva2 a_sup_set_class f5_cbvrexdva2 a_wcel f1_cbvrexdva2 a_wa f4_cbvrexdva2 a_sup_set_class f6_cbvrexdva2 a_wcel f2_cbvrexdva2 a_wa f3_cbvrexdva2 f4_cbvrexdva2 p_cbvexdva f1_cbvrexdva2 f3_cbvrexdva2 f5_cbvrexdva2 a_df-rex f2_cbvrexdva2 f4_cbvrexdva2 f6_cbvrexdva2 a_df-rex f0_cbvrexdva2 f3_cbvrexdva2 a_sup_set_class f5_cbvrexdva2 a_wcel f1_cbvrexdva2 a_wa f3_cbvrexdva2 a_wex f4_cbvrexdva2 a_sup_set_class f6_cbvrexdva2 a_wcel f2_cbvrexdva2 a_wa f4_cbvrexdva2 a_wex f1_cbvrexdva2 f3_cbvrexdva2 f5_cbvrexdva2 a_wrex f2_cbvrexdva2 f4_cbvrexdva2 f6_cbvrexdva2 a_wrex p_3bitr4g $.
$}

$(Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution.  Deduction form.  (Contributed by
       David Moews, 1-May-2017.) $)

${
	$v ph ps ch x y A  $.
	$d ps y  $.
	$d ch x  $.
	$d A x y  $.
	$d x ph y  $.
	f0_cbvraldva $f wff ph $.
	f1_cbvraldva $f wff ps $.
	f2_cbvraldva $f wff ch $.
	f3_cbvraldva $f set x $.
	f4_cbvraldva $f set y $.
	f5_cbvraldva $f class A $.
	e0_cbvraldva $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	p_cbvraldva $p |- ( ph -> ( A. x e. A ps <-> A. y e. A ch ) ) $= e0_cbvraldva f0_cbvraldva f3_cbvraldva a_sup_set_class f4_cbvraldva a_sup_set_class a_wceq a_wa f5_cbvraldva p_eqidd f0_cbvraldva f1_cbvraldva f2_cbvraldva f3_cbvraldva f4_cbvraldva f5_cbvraldva f5_cbvraldva p_cbvraldva2 $.
$}

$(Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution.  Deduction form.  (Contributed by
       David Moews, 1-May-2017.) $)

${
	$v ph ps ch x y A  $.
	$d ps y  $.
	$d ch x  $.
	$d A x y  $.
	$d x ph y  $.
	f0_cbvrexdva $f wff ph $.
	f1_cbvrexdva $f wff ps $.
	f2_cbvrexdva $f wff ch $.
	f3_cbvrexdva $f set x $.
	f4_cbvrexdva $f set y $.
	f5_cbvrexdva $f class A $.
	e0_cbvrexdva $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	p_cbvrexdva $p |- ( ph -> ( E. x e. A ps <-> E. y e. A ch ) ) $= e0_cbvrexdva f0_cbvrexdva f3_cbvrexdva a_sup_set_class f4_cbvrexdva a_sup_set_class a_wceq a_wa f5_cbvrexdva p_eqidd f0_cbvrexdva f1_cbvrexdva f2_cbvrexdva f3_cbvrexdva f4_cbvrexdva f5_cbvrexdva f5_cbvrexdva p_cbvrexdva2 $.
$}

$(Change bound variables of double restricted universal quantification,
       using implicit substitution.  (Contributed by NM, 10-Aug-2004.) $)

${
	$v ph ps ch x y z w A B  $.
	$d x A  $.
	$d z A  $.
	$d x y B  $.
	$d z y B  $.
	$d w B  $.
	$d z ph  $.
	$d y ps  $.
	$d x ch  $.
	$d w ch  $.
	f0_cbvral2v $f wff ph $.
	f1_cbvral2v $f wff ps $.
	f2_cbvral2v $f wff ch $.
	f3_cbvral2v $f set x $.
	f4_cbvral2v $f set y $.
	f5_cbvral2v $f set z $.
	f6_cbvral2v $f set w $.
	f7_cbvral2v $f class A $.
	f8_cbvral2v $f class B $.
	e0_cbvral2v $e |- ( x = z -> ( ph <-> ch ) ) $.
	e1_cbvral2v $e |- ( y = w -> ( ch <-> ps ) ) $.
	p_cbvral2v $p |- ( A. x e. A A. y e. B ph <-> A. z e. A A. w e. B ps ) $= e0_cbvral2v f3_cbvral2v a_sup_set_class f5_cbvral2v a_sup_set_class a_wceq f0_cbvral2v f2_cbvral2v f4_cbvral2v f8_cbvral2v p_ralbidv f0_cbvral2v f4_cbvral2v f8_cbvral2v a_wral f2_cbvral2v f4_cbvral2v f8_cbvral2v a_wral f3_cbvral2v f5_cbvral2v f7_cbvral2v p_cbvralv e1_cbvral2v f2_cbvral2v f1_cbvral2v f4_cbvral2v f6_cbvral2v f8_cbvral2v p_cbvralv f2_cbvral2v f4_cbvral2v f8_cbvral2v a_wral f1_cbvral2v f6_cbvral2v f8_cbvral2v a_wral f5_cbvral2v f7_cbvral2v p_ralbii f0_cbvral2v f4_cbvral2v f8_cbvral2v a_wral f3_cbvral2v f7_cbvral2v a_wral f2_cbvral2v f4_cbvral2v f8_cbvral2v a_wral f5_cbvral2v f7_cbvral2v a_wral f1_cbvral2v f6_cbvral2v f8_cbvral2v a_wral f5_cbvral2v f7_cbvral2v a_wral p_bitri $.
$}

$(Change bound variables of double restricted universal quantification,
       using implicit substitution.  (Contributed by FL, 2-Jul-2012.) $)

${
	$v ph ps ch x y z w A B  $.
	$d A x  $.
	$d A z  $.
	$d B w  $.
	$d B x y  $.
	$d B z y  $.
	$d ch w  $.
	$d ch x  $.
	$d ph z  $.
	$d ps y  $.
	f0_cbvrex2v $f wff ph $.
	f1_cbvrex2v $f wff ps $.
	f2_cbvrex2v $f wff ch $.
	f3_cbvrex2v $f set x $.
	f4_cbvrex2v $f set y $.
	f5_cbvrex2v $f set z $.
	f6_cbvrex2v $f set w $.
	f7_cbvrex2v $f class A $.
	f8_cbvrex2v $f class B $.
	e0_cbvrex2v $e |- ( x = z -> ( ph <-> ch ) ) $.
	e1_cbvrex2v $e |- ( y = w -> ( ch <-> ps ) ) $.
	p_cbvrex2v $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B ps ) $= e0_cbvrex2v f3_cbvrex2v a_sup_set_class f5_cbvrex2v a_sup_set_class a_wceq f0_cbvrex2v f2_cbvrex2v f4_cbvrex2v f8_cbvrex2v p_rexbidv f0_cbvrex2v f4_cbvrex2v f8_cbvrex2v a_wrex f2_cbvrex2v f4_cbvrex2v f8_cbvrex2v a_wrex f3_cbvrex2v f5_cbvrex2v f7_cbvrex2v p_cbvrexv e1_cbvrex2v f2_cbvrex2v f1_cbvrex2v f4_cbvrex2v f6_cbvrex2v f8_cbvrex2v p_cbvrexv f2_cbvrex2v f4_cbvrex2v f8_cbvrex2v a_wrex f1_cbvrex2v f6_cbvrex2v f8_cbvrex2v a_wrex f5_cbvrex2v f7_cbvrex2v p_rexbii f0_cbvrex2v f4_cbvrex2v f8_cbvrex2v a_wrex f3_cbvrex2v f7_cbvrex2v a_wrex f2_cbvrex2v f4_cbvrex2v f8_cbvrex2v a_wrex f5_cbvrex2v f7_cbvrex2v a_wrex f1_cbvrex2v f6_cbvrex2v f8_cbvrex2v a_wrex f5_cbvrex2v f7_cbvrex2v a_wrex p_bitri $.
$}

$(Change bound variables of triple restricted universal quantification,
       using implicit substitution.  (Contributed by NM, 10-May-2005.) $)

${
	$v ph ps ch th x y z w v u A B C  $.
	$d w ph  $.
	$d z ps  $.
	$d x ch  $.
	$d v ch  $.
	$d y u th  $.
	$d x A  $.
	$d w A  $.
	$d x y B  $.
	$d w y B  $.
	$d v B  $.
	$d x y z C  $.
	$d w y z C  $.
	$d v z C  $.
	$d z y C  $.
	$d z C  $.
	$d u C  $.
	f0_cbvral3v $f wff ph $.
	f1_cbvral3v $f wff ps $.
	f2_cbvral3v $f wff ch $.
	f3_cbvral3v $f wff th $.
	f4_cbvral3v $f set x $.
	f5_cbvral3v $f set y $.
	f6_cbvral3v $f set z $.
	f7_cbvral3v $f set w $.
	f8_cbvral3v $f set v $.
	f9_cbvral3v $f set u $.
	f10_cbvral3v $f class A $.
	f11_cbvral3v $f class B $.
	f12_cbvral3v $f class C $.
	e0_cbvral3v $e |- ( x = w -> ( ph <-> ch ) ) $.
	e1_cbvral3v $e |- ( y = v -> ( ch <-> th ) ) $.
	e2_cbvral3v $e |- ( z = u -> ( th <-> ps ) ) $.
	p_cbvral3v $p |- ( A. x e. A A. y e. B A. z e. C ph <-> A. w e. A A. v e. B A. u e. C ps ) $= e0_cbvral3v f4_cbvral3v a_sup_set_class f7_cbvral3v a_sup_set_class a_wceq f0_cbvral3v f2_cbvral3v f5_cbvral3v f6_cbvral3v f11_cbvral3v f12_cbvral3v p_2ralbidv f0_cbvral3v f6_cbvral3v f12_cbvral3v a_wral f5_cbvral3v f11_cbvral3v a_wral f2_cbvral3v f6_cbvral3v f12_cbvral3v a_wral f5_cbvral3v f11_cbvral3v a_wral f4_cbvral3v f7_cbvral3v f10_cbvral3v p_cbvralv e1_cbvral3v e2_cbvral3v f2_cbvral3v f1_cbvral3v f3_cbvral3v f5_cbvral3v f6_cbvral3v f8_cbvral3v f9_cbvral3v f11_cbvral3v f12_cbvral3v p_cbvral2v f2_cbvral3v f6_cbvral3v f12_cbvral3v a_wral f5_cbvral3v f11_cbvral3v a_wral f1_cbvral3v f9_cbvral3v f12_cbvral3v a_wral f8_cbvral3v f11_cbvral3v a_wral f7_cbvral3v f10_cbvral3v p_ralbii f0_cbvral3v f6_cbvral3v f12_cbvral3v a_wral f5_cbvral3v f11_cbvral3v a_wral f4_cbvral3v f10_cbvral3v a_wral f2_cbvral3v f6_cbvral3v f12_cbvral3v a_wral f5_cbvral3v f11_cbvral3v a_wral f7_cbvral3v f10_cbvral3v a_wral f1_cbvral3v f9_cbvral3v f12_cbvral3v a_wral f8_cbvral3v f11_cbvral3v a_wral f7_cbvral3v f10_cbvral3v a_wral p_bitri $.
$}

$(Change bound variable by using a substitution.  (Contributed by NM,
       20-Nov-2005.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)

${
	$v ph x y A  $.
	$d z x A  $.
	$d y A  $.
	$d z y ph  $.
	f0_cbvralsv $f wff ph $.
	f1_cbvralsv $f set x $.
	f2_cbvralsv $f set y $.
	f3_cbvralsv $f class A $.
	i0_cbvralsv $f set z $.
	p_cbvralsv $p |- ( A. x e. A ph <-> A. y e. A [ y / x ] ph ) $= f0_cbvralsv i0_cbvralsv p_nfv f0_cbvralsv f1_cbvralsv i0_cbvralsv p_nfs1v f0_cbvralsv f1_cbvralsv i0_cbvralsv p_sbequ12 f0_cbvralsv f0_cbvralsv f1_cbvralsv i0_cbvralsv a_wsb f1_cbvralsv i0_cbvralsv f3_cbvralsv p_cbvral f0_cbvralsv f2_cbvralsv p_nfv f0_cbvralsv f1_cbvralsv i0_cbvralsv f2_cbvralsv p_nfsb f0_cbvralsv f1_cbvralsv f2_cbvralsv a_wsb i0_cbvralsv p_nfv f0_cbvralsv i0_cbvralsv f2_cbvralsv f1_cbvralsv p_sbequ f0_cbvralsv f1_cbvralsv i0_cbvralsv a_wsb f0_cbvralsv f1_cbvralsv f2_cbvralsv a_wsb i0_cbvralsv f2_cbvralsv f3_cbvralsv p_cbvral f0_cbvralsv f1_cbvralsv f3_cbvralsv a_wral f0_cbvralsv f1_cbvralsv i0_cbvralsv a_wsb i0_cbvralsv f3_cbvralsv a_wral f0_cbvralsv f1_cbvralsv f2_cbvralsv a_wsb f2_cbvralsv f3_cbvralsv a_wral p_bitri $.
$}

$(Change bound variable by using a substitution.  (Contributed by NM,
       2-Mar-2008.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)

${
	$v ph x y A  $.
	$d z x A  $.
	$d y z ph  $.
	$d y A  $.
	f0_cbvrexsv $f wff ph $.
	f1_cbvrexsv $f set x $.
	f2_cbvrexsv $f set y $.
	f3_cbvrexsv $f class A $.
	i0_cbvrexsv $f set z $.
	p_cbvrexsv $p |- ( E. x e. A ph <-> E. y e. A [ y / x ] ph ) $= f0_cbvrexsv i0_cbvrexsv p_nfv f0_cbvrexsv f1_cbvrexsv i0_cbvrexsv p_nfs1v f0_cbvrexsv f1_cbvrexsv i0_cbvrexsv p_sbequ12 f0_cbvrexsv f0_cbvrexsv f1_cbvrexsv i0_cbvrexsv a_wsb f1_cbvrexsv i0_cbvrexsv f3_cbvrexsv p_cbvrex f0_cbvrexsv f2_cbvrexsv p_nfv f0_cbvrexsv f1_cbvrexsv i0_cbvrexsv f2_cbvrexsv p_nfsb f0_cbvrexsv f1_cbvrexsv f2_cbvrexsv a_wsb i0_cbvrexsv p_nfv f0_cbvrexsv i0_cbvrexsv f2_cbvrexsv f1_cbvrexsv p_sbequ f0_cbvrexsv f1_cbvrexsv i0_cbvrexsv a_wsb f0_cbvrexsv f1_cbvrexsv f2_cbvrexsv a_wsb i0_cbvrexsv f2_cbvrexsv f3_cbvrexsv p_cbvrex f0_cbvrexsv f1_cbvrexsv f3_cbvrexsv a_wrex f0_cbvrexsv f1_cbvrexsv i0_cbvrexsv a_wsb i0_cbvrexsv f3_cbvrexsv a_wrex f0_cbvrexsv f1_cbvrexsv f2_cbvrexsv a_wsb f2_cbvrexsv f3_cbvrexsv a_wrex p_bitri $.
$}

$(Implicit to explicit substitution that swaps variables in a quantified
       expression.  (Contributed by NM, 5-Sep-2004.) $)

${
	$v ph ps x y  $.
	$d x y z  $.
	$d y z ph  $.
	$d x z ps  $.
	f0_sbralie $f wff ph $.
	f1_sbralie $f wff ps $.
	f2_sbralie $f set x $.
	f3_sbralie $f set y $.
	i0_sbralie $f set z $.
	e0_sbralie $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_sbralie $p |- ( [ x / y ] A. x e. y ph <-> A. y e. x ps ) $= f0_sbralie f2_sbralie i0_sbralie f3_sbralie a_sup_set_class p_cbvralsv f0_sbralie f2_sbralie f3_sbralie a_sup_set_class a_wral f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f3_sbralie a_sup_set_class a_wral f3_sbralie f2_sbralie p_sbbii f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f2_sbralie a_sup_set_class a_wral f3_sbralie p_nfv f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f3_sbralie a_sup_set_class f2_sbralie a_sup_set_class p_raleq f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f3_sbralie a_sup_set_class a_wral f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f2_sbralie a_sup_set_class a_wral f3_sbralie f2_sbralie p_sbie f0_sbralie f2_sbralie f3_sbralie a_sup_set_class a_wral f3_sbralie f2_sbralie a_wsb f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f3_sbralie a_sup_set_class a_wral f3_sbralie f2_sbralie a_wsb f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f2_sbralie a_sup_set_class a_wral p_bitri f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f3_sbralie f2_sbralie a_sup_set_class p_cbvralsv f0_sbralie i0_sbralie p_nfv f0_sbralie f2_sbralie f3_sbralie i0_sbralie p_sbco2 f1_sbralie f2_sbralie p_nfv e0_sbralie f0_sbralie f1_sbralie f2_sbralie f3_sbralie p_sbie f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f3_sbralie a_wsb f0_sbralie f2_sbralie f3_sbralie a_wsb f1_sbralie p_bitri f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f3_sbralie a_wsb f1_sbralie f3_sbralie f2_sbralie a_sup_set_class p_ralbii f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f2_sbralie a_sup_set_class a_wral f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f3_sbralie a_wsb f3_sbralie f2_sbralie a_sup_set_class a_wral f1_sbralie f3_sbralie f2_sbralie a_sup_set_class a_wral p_bitri f0_sbralie f2_sbralie f3_sbralie a_sup_set_class a_wral f3_sbralie f2_sbralie a_wsb f0_sbralie f2_sbralie i0_sbralie a_wsb i0_sbralie f2_sbralie a_sup_set_class a_wral f1_sbralie f3_sbralie f2_sbralie a_sup_set_class a_wral p_bitri $.
$}

$(Equivalent wff's yield equal restricted class abstractions (inference
       rule).  (Contributed by NM, 22-May-1999.) $)

${
	$v ph ps x A  $.
	f0_rabbiia $f wff ph $.
	f1_rabbiia $f wff ps $.
	f2_rabbiia $f set x $.
	f3_rabbiia $f class A $.
	e0_rabbiia $e |- ( x e. A -> ( ph <-> ps ) ) $.
	p_rabbiia $p |- { x e. A | ph } = { x e. A | ps } $= e0_rabbiia f2_rabbiia a_sup_set_class f3_rabbiia a_wcel f0_rabbiia f1_rabbiia p_pm5.32i f2_rabbiia a_sup_set_class f3_rabbiia a_wcel f0_rabbiia a_wa f2_rabbiia a_sup_set_class f3_rabbiia a_wcel f1_rabbiia a_wa f2_rabbiia p_abbii f0_rabbiia f2_rabbiia f3_rabbiia a_df-rab f1_rabbiia f2_rabbiia f3_rabbiia a_df-rab f2_rabbiia a_sup_set_class f3_rabbiia a_wcel f0_rabbiia a_wa f2_rabbiia a_cab f2_rabbiia a_sup_set_class f3_rabbiia a_wcel f1_rabbiia a_wa f2_rabbiia a_cab f0_rabbiia f2_rabbiia f3_rabbiia a_crab f1_rabbiia f2_rabbiia f3_rabbiia a_crab p_3eqtr4i $.
$}

$(Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  (Contributed by NM, 28-Nov-2003.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_rabbidva $f wff ph $.
	f1_rabbidva $f wff ps $.
	f2_rabbidva $f wff ch $.
	f3_rabbidva $f set x $.
	f4_rabbidva $f class A $.
	e0_rabbidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_rabbidva $p |- ( ph -> { x e. A | ps } = { x e. A | ch } ) $= e0_rabbidva f0_rabbidva f1_rabbidva f2_rabbidva a_wb f3_rabbidva f4_rabbidva p_ralrimiva f1_rabbidva f2_rabbidva f3_rabbidva f4_rabbidva p_rabbi f0_rabbidva f1_rabbidva f2_rabbidva a_wb f3_rabbidva f4_rabbidva a_wral f1_rabbidva f3_rabbidva f4_rabbidva a_crab f2_rabbidva f3_rabbidva f4_rabbidva a_crab a_wceq p_sylib $.
$}

$(Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  (Contributed by NM, 10-Feb-1995.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_rabbidv $f wff ph $.
	f1_rabbidv $f wff ps $.
	f2_rabbidv $f wff ch $.
	f3_rabbidv $f set x $.
	f4_rabbidv $f class A $.
	e0_rabbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_rabbidv $p |- ( ph -> { x e. A | ps } = { x e. A | ch } ) $= e0_rabbidv f0_rabbidv f1_rabbidv f2_rabbidv a_wb f3_rabbidv a_sup_set_class f4_rabbidv a_wcel p_adantr f0_rabbidv f1_rabbidv f2_rabbidv f3_rabbidv f4_rabbidv p_rabbidva $.
$}

$(Equality theorem for restricted class abstractions, with bound-variable
       hypotheses instead of distinct variable restrictions.  (Contributed by
       NM, 7-Mar-2004.) $)

${
	$v ph x A B  $.
	$d A  $.
	$d B  $.
	f0_rabeqf $f wff ph $.
	f1_rabeqf $f set x $.
	f2_rabeqf $f class A $.
	f3_rabeqf $f class B $.
	e0_rabeqf $e |- F/_ x A $.
	e1_rabeqf $e |- F/_ x B $.
	p_rabeqf $p |- ( A = B -> { x e. A | ph } = { x e. B | ph } ) $= e0_rabeqf e1_rabeqf f1_rabeqf f2_rabeqf f3_rabeqf p_nfeq f2_rabeqf f3_rabeqf f1_rabeqf a_sup_set_class p_eleq2 f2_rabeqf f3_rabeqf a_wceq f1_rabeqf a_sup_set_class f2_rabeqf a_wcel f1_rabeqf a_sup_set_class f3_rabeqf a_wcel f0_rabeqf p_anbi1d f2_rabeqf f3_rabeqf a_wceq f1_rabeqf a_sup_set_class f2_rabeqf a_wcel f0_rabeqf a_wa f1_rabeqf a_sup_set_class f3_rabeqf a_wcel f0_rabeqf a_wa f1_rabeqf p_abbid f0_rabeqf f1_rabeqf f2_rabeqf a_df-rab f0_rabeqf f1_rabeqf f3_rabeqf a_df-rab f2_rabeqf f3_rabeqf a_wceq f1_rabeqf a_sup_set_class f2_rabeqf a_wcel f0_rabeqf a_wa f1_rabeqf a_cab f1_rabeqf a_sup_set_class f3_rabeqf a_wcel f0_rabeqf a_wa f1_rabeqf a_cab f0_rabeqf f1_rabeqf f2_rabeqf a_crab f0_rabeqf f1_rabeqf f3_rabeqf a_crab p_3eqtr4g $.
$}

$(Equality theorem for restricted class abstractions.  (Contributed by NM,
       15-Oct-2003.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rabeq $f wff ph $.
	f1_rabeq $f set x $.
	f2_rabeq $f class A $.
	f3_rabeq $f class B $.
	p_rabeq $p |- ( A = B -> { x e. A | ph } = { x e. B | ph } ) $= f1_rabeq f2_rabeq p_nfcv f1_rabeq f3_rabeq p_nfcv f0_rabeq f1_rabeq f2_rabeq f3_rabeq p_rabeqf $.
$}

$(Equality of restricted class abstractions.  (Contributed by Jeff Madsen,
       1-Dec-2009.) $)

${
	$v ph ps ch x A B  $.
	$d A x  $.
	$d B x  $.
	$d ph x  $.
	f0_rabeqbidv $f wff ph $.
	f1_rabeqbidv $f wff ps $.
	f2_rabeqbidv $f wff ch $.
	f3_rabeqbidv $f set x $.
	f4_rabeqbidv $f class A $.
	f5_rabeqbidv $f class B $.
	e0_rabeqbidv $e |- ( ph -> A = B ) $.
	e1_rabeqbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_rabeqbidv $p |- ( ph -> { x e. A | ps } = { x e. B | ch } ) $= e0_rabeqbidv f1_rabeqbidv f3_rabeqbidv f4_rabeqbidv f5_rabeqbidv p_rabeq f0_rabeqbidv f4_rabeqbidv f5_rabeqbidv a_wceq f1_rabeqbidv f3_rabeqbidv f4_rabeqbidv a_crab f1_rabeqbidv f3_rabeqbidv f5_rabeqbidv a_crab a_wceq p_syl e1_rabeqbidv f0_rabeqbidv f1_rabeqbidv f2_rabeqbidv f3_rabeqbidv f5_rabeqbidv p_rabbidv f0_rabeqbidv f1_rabeqbidv f3_rabeqbidv f4_rabeqbidv a_crab f1_rabeqbidv f3_rabeqbidv f5_rabeqbidv a_crab f2_rabeqbidv f3_rabeqbidv f5_rabeqbidv a_crab p_eqtrd $.
$}

$(Equality of restricted class abstractions.  (Contributed by Mario
       Carneiro, 26-Jan-2017.) $)

${
	$v ph ps ch x A B  $.
	$d A x  $.
	$d B x  $.
	$d ph x  $.
	f0_rabeqbidva $f wff ph $.
	f1_rabeqbidva $f wff ps $.
	f2_rabeqbidva $f wff ch $.
	f3_rabeqbidva $f set x $.
	f4_rabeqbidva $f class A $.
	f5_rabeqbidva $f class B $.
	e0_rabeqbidva $e |- ( ph -> A = B ) $.
	e1_rabeqbidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_rabeqbidva $p |- ( ph -> { x e. A | ps } = { x e. B | ch } ) $= e1_rabeqbidva f0_rabeqbidva f1_rabeqbidva f2_rabeqbidva f3_rabeqbidva f4_rabeqbidva p_rabbidva e0_rabeqbidva f2_rabeqbidva f3_rabeqbidva f4_rabeqbidva f5_rabeqbidva p_rabeq f0_rabeqbidva f4_rabeqbidva f5_rabeqbidva a_wceq f2_rabeqbidva f3_rabeqbidva f4_rabeqbidva a_crab f2_rabeqbidva f3_rabeqbidva f5_rabeqbidva a_crab a_wceq p_syl f0_rabeqbidva f1_rabeqbidva f3_rabeqbidva f4_rabeqbidva a_crab f2_rabeqbidva f3_rabeqbidva f4_rabeqbidva a_crab f2_rabeqbidva f3_rabeqbidva f5_rabeqbidva a_crab p_eqtrd $.
$}

$(Inference rule from equality of a class variable and a restricted class
       abstraction.  (Contributed by NM, 16-Feb-2004.) $)

${
	$v ph x A B  $.
	f0_rabeq2i $f wff ph $.
	f1_rabeq2i $f set x $.
	f2_rabeq2i $f class A $.
	f3_rabeq2i $f class B $.
	e0_rabeq2i $e |- A = { x e. B | ph } $.
	p_rabeq2i $p |- ( x e. A <-> ( x e. B /\ ph ) ) $= e0_rabeq2i f2_rabeq2i f0_rabeq2i f1_rabeq2i f3_rabeq2i a_crab f1_rabeq2i a_sup_set_class p_eleq2i f0_rabeq2i f1_rabeq2i f3_rabeq2i p_rabid f1_rabeq2i a_sup_set_class f2_rabeq2i a_wcel f1_rabeq2i a_sup_set_class f0_rabeq2i f1_rabeq2i f3_rabeq2i a_crab a_wcel f1_rabeq2i a_sup_set_class f3_rabeq2i a_wcel f0_rabeq2i a_wa p_bitri $.
$}

$(Rule to change the bound variable in a restricted class abstraction,
       using implicit substitution.  This version has bound-variable hypotheses
       in place of distinct variable conditions.  (Contributed by Andrew
       Salmon, 11-Jul-2011.)  (Revised by Mario Carneiro, 9-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d x z  $.
	$d y z  $.
	$d A z  $.
	$d ph z  $.
	$d ps z  $.
	f0_cbvrab $f wff ph $.
	f1_cbvrab $f wff ps $.
	f2_cbvrab $f set x $.
	f3_cbvrab $f set y $.
	f4_cbvrab $f class A $.
	i0_cbvrab $f set z $.
	e0_cbvrab $e |- F/_ x A $.
	e1_cbvrab $e |- F/_ y A $.
	e2_cbvrab $e |- F/ y ph $.
	e3_cbvrab $e |- F/ x ps $.
	e4_cbvrab $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrab $p |- { x e. A | ph } = { y e. A | ps } $= f2_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab a_wa i0_cbvrab p_nfv e0_cbvrab f2_cbvrab i0_cbvrab f4_cbvrab p_nfcri f0_cbvrab f2_cbvrab i0_cbvrab p_nfs1v i0_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab f2_cbvrab i0_cbvrab a_wsb f2_cbvrab p_nfan f2_cbvrab a_sup_set_class i0_cbvrab a_sup_set_class f4_cbvrab p_eleq1 f0_cbvrab f2_cbvrab i0_cbvrab p_sbequ12 f2_cbvrab a_sup_set_class i0_cbvrab a_sup_set_class a_wceq f2_cbvrab a_sup_set_class f4_cbvrab a_wcel i0_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab f0_cbvrab f2_cbvrab i0_cbvrab a_wsb p_anbi12d f2_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab a_wa i0_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab f2_cbvrab i0_cbvrab a_wsb a_wa f2_cbvrab i0_cbvrab p_cbvab e1_cbvrab f3_cbvrab i0_cbvrab f4_cbvrab p_nfcri e2_cbvrab f0_cbvrab f2_cbvrab i0_cbvrab f3_cbvrab p_nfsb i0_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab f2_cbvrab i0_cbvrab a_wsb f3_cbvrab p_nfan f3_cbvrab a_sup_set_class f4_cbvrab a_wcel f1_cbvrab a_wa i0_cbvrab p_nfv i0_cbvrab a_sup_set_class f3_cbvrab a_sup_set_class f4_cbvrab p_eleq1 f0_cbvrab i0_cbvrab f3_cbvrab f2_cbvrab p_sbequ e3_cbvrab e4_cbvrab f0_cbvrab f1_cbvrab f2_cbvrab f3_cbvrab p_sbie i0_cbvrab a_sup_set_class f3_cbvrab a_sup_set_class a_wceq f0_cbvrab f2_cbvrab i0_cbvrab a_wsb f0_cbvrab f2_cbvrab f3_cbvrab a_wsb f1_cbvrab p_syl6bb i0_cbvrab a_sup_set_class f3_cbvrab a_sup_set_class a_wceq i0_cbvrab a_sup_set_class f4_cbvrab a_wcel f3_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab f2_cbvrab i0_cbvrab a_wsb f1_cbvrab p_anbi12d i0_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab f2_cbvrab i0_cbvrab a_wsb a_wa f3_cbvrab a_sup_set_class f4_cbvrab a_wcel f1_cbvrab a_wa i0_cbvrab f3_cbvrab p_cbvab f2_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab a_wa f2_cbvrab a_cab i0_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab f2_cbvrab i0_cbvrab a_wsb a_wa i0_cbvrab a_cab f3_cbvrab a_sup_set_class f4_cbvrab a_wcel f1_cbvrab a_wa f3_cbvrab a_cab p_eqtri f0_cbvrab f2_cbvrab f4_cbvrab a_df-rab f1_cbvrab f3_cbvrab f4_cbvrab a_df-rab f2_cbvrab a_sup_set_class f4_cbvrab a_wcel f0_cbvrab a_wa f2_cbvrab a_cab f3_cbvrab a_sup_set_class f4_cbvrab a_wcel f1_cbvrab a_wa f3_cbvrab a_cab f0_cbvrab f2_cbvrab f4_cbvrab a_crab f1_cbvrab f3_cbvrab f4_cbvrab a_crab p_3eqtr4i $.
$}

$(Rule to change the bound variable in a restricted class abstraction,
       using implicit substitution.  (Contributed by NM, 26-May-1999.) $)

${
	$v ph ps x y A  $.
	$d x y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvrabv $f wff ph $.
	f1_cbvrabv $f wff ps $.
	f2_cbvrabv $f set x $.
	f3_cbvrabv $f set y $.
	f4_cbvrabv $f class A $.
	e0_cbvrabv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrabv $p |- { x e. A | ph } = { y e. A | ps } $= f2_cbvrabv f4_cbvrabv p_nfcv f3_cbvrabv f4_cbvrabv p_nfcv f0_cbvrabv f3_cbvrabv p_nfv f1_cbvrabv f2_cbvrabv p_nfv e0_cbvrabv f0_cbvrabv f1_cbvrabv f2_cbvrabv f3_cbvrabv f4_cbvrabv p_cbvrab $.
$}


