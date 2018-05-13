$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_union_of_a_class.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The intersection of a class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare class intersection symbol. $)

$c |^| $.

$(Big cap $)

$(Extend class notation to include the intersection of a class (read:
     'intersect ` A ` '). $)

${
	$v A  $.
	f0_cint $f class A $.
	a_cint $a class |^| A $.
$}

$(Define the intersection of a class.  Definition 7.35 of [TakeutiZaring]
       p. 44.  For example, ` |^| { { 1 , 3 } , { 1 , 8 } } = { 1 } ` .
       Compare this with the intersection of two classes, ~ df-in .
       (Contributed by NM, 18-Aug-1993.) $)

${
	$v x y A  $.
	$d x y A  $.
	f0_df-int $f set x $.
	f1_df-int $f set y $.
	f2_df-int $f class A $.
	a_df-int $a |- |^| A = { x | A. y ( y e. A -> x e. y ) } $.
$}

$(Alternate definition of class intersection.  (Contributed by NM,
       28-Jun-1998.) $)

${
	$v x y A  $.
	$d x y A  $.
	f0_dfint2 $f set x $.
	f1_dfint2 $f set y $.
	f2_dfint2 $f class A $.
	p_dfint2 $p |- |^| A = { x | A. y e. A x e. y } $= f0_dfint2 f1_dfint2 f2_dfint2 a_df-int f0_dfint2 a_sup_set_class f1_dfint2 a_sup_set_class a_wcel f1_dfint2 f2_dfint2 a_df-ral f0_dfint2 a_sup_set_class f1_dfint2 a_sup_set_class a_wcel f1_dfint2 f2_dfint2 a_wral f1_dfint2 a_sup_set_class f2_dfint2 a_wcel f0_dfint2 a_sup_set_class f1_dfint2 a_sup_set_class a_wcel a_wi f1_dfint2 a_wal f0_dfint2 p_abbii f2_dfint2 a_cint f1_dfint2 a_sup_set_class f2_dfint2 a_wcel f0_dfint2 a_sup_set_class f1_dfint2 a_sup_set_class a_wcel a_wi f1_dfint2 a_wal f0_dfint2 a_cab f0_dfint2 a_sup_set_class f1_dfint2 a_sup_set_class a_wcel f1_dfint2 f2_dfint2 a_wral f0_dfint2 a_cab p_eqtr4i $.
$}

$(Equality law for intersection.  (Contributed by NM, 13-Sep-1999.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_inteq $f class A $.
	f1_inteq $f class B $.
	i0_inteq $f set x $.
	i1_inteq $f set y $.
	p_inteq $p |- ( A = B -> |^| A = |^| B ) $= i0_inteq a_sup_set_class i1_inteq a_sup_set_class a_wcel i1_inteq f0_inteq f1_inteq p_raleq f0_inteq f1_inteq a_wceq i0_inteq a_sup_set_class i1_inteq a_sup_set_class a_wcel i1_inteq f0_inteq a_wral i0_inteq a_sup_set_class i1_inteq a_sup_set_class a_wcel i1_inteq f1_inteq a_wral i0_inteq p_abbidv i0_inteq i1_inteq f0_inteq p_dfint2 i0_inteq i1_inteq f1_inteq p_dfint2 f0_inteq f1_inteq a_wceq i0_inteq a_sup_set_class i1_inteq a_sup_set_class a_wcel i1_inteq f0_inteq a_wral i0_inteq a_cab i0_inteq a_sup_set_class i1_inteq a_sup_set_class a_wcel i1_inteq f1_inteq a_wral i0_inteq a_cab f0_inteq a_cint f1_inteq a_cint p_3eqtr4g $.
$}

$(Equality inference for class intersection.  (Contributed by NM,
       2-Sep-2003.) $)

${
	$v A B  $.
	f0_inteqi $f class A $.
	f1_inteqi $f class B $.
	e0_inteqi $e |- A = B $.
	p_inteqi $p |- |^| A = |^| B $= e0_inteqi f0_inteqi f1_inteqi p_inteq f0_inteqi f1_inteqi a_wceq f0_inteqi a_cint f1_inteqi a_cint a_wceq a_ax-mp $.
$}

$(Equality deduction for class intersection.  (Contributed by NM,
       2-Sep-2003.) $)

${
	$v ph A B  $.
	f0_inteqd $f wff ph $.
	f1_inteqd $f class A $.
	f2_inteqd $f class B $.
	e0_inteqd $e |- ( ph -> A = B ) $.
	p_inteqd $p |- ( ph -> |^| A = |^| B ) $= e0_inteqd f1_inteqd f2_inteqd p_inteq f0_inteqd f1_inteqd f2_inteqd a_wceq f1_inteqd a_cint f2_inteqd a_cint a_wceq p_syl $.
$}

$(Membership in class intersection.  (Contributed by NM, 21-May-1994.) $)

${
	$v x A B  $.
	$d x A y  $.
	$d x B y  $.
	f0_elint $f set x $.
	f1_elint $f class A $.
	f2_elint $f class B $.
	i0_elint $f set y $.
	e0_elint $e |- A e. _V $.
	p_elint $p |- ( A e. |^| B <-> A. x ( x e. B -> A e. x ) ) $= e0_elint i0_elint a_sup_set_class f1_elint f0_elint a_sup_set_class p_eleq1 i0_elint a_sup_set_class f1_elint a_wceq i0_elint a_sup_set_class f0_elint a_sup_set_class a_wcel f1_elint f0_elint a_sup_set_class a_wcel f0_elint a_sup_set_class f2_elint a_wcel p_imbi2d i0_elint a_sup_set_class f1_elint a_wceq f0_elint a_sup_set_class f2_elint a_wcel i0_elint a_sup_set_class f0_elint a_sup_set_class a_wcel a_wi f0_elint a_sup_set_class f2_elint a_wcel f1_elint f0_elint a_sup_set_class a_wcel a_wi f0_elint p_albidv i0_elint f0_elint f2_elint a_df-int f0_elint a_sup_set_class f2_elint a_wcel i0_elint a_sup_set_class f0_elint a_sup_set_class a_wcel a_wi f0_elint a_wal f0_elint a_sup_set_class f2_elint a_wcel f1_elint f0_elint a_sup_set_class a_wcel a_wi f0_elint a_wal i0_elint f1_elint f2_elint a_cint p_elab2 $.
$}

$(Membership in class intersection.  (Contributed by NM, 14-Oct-1999.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_elint2 $f set x $.
	f1_elint2 $f class A $.
	f2_elint2 $f class B $.
	e0_elint2 $e |- A e. _V $.
	p_elint2 $p |- ( A e. |^| B <-> A. x e. B A e. x ) $= e0_elint2 f0_elint2 f1_elint2 f2_elint2 p_elint f1_elint2 f0_elint2 a_sup_set_class a_wcel f0_elint2 f2_elint2 a_df-ral f1_elint2 f2_elint2 a_cint a_wcel f0_elint2 a_sup_set_class f2_elint2 a_wcel f1_elint2 f0_elint2 a_sup_set_class a_wcel a_wi f0_elint2 a_wal f1_elint2 f0_elint2 a_sup_set_class a_wcel f0_elint2 f2_elint2 a_wral p_bitr4i $.
$}

$(Membership in class intersection, with the sethood requirement expressed
       as an antecedent.  (Contributed by NM, 20-Nov-2003.) $)

${
	$v x A B V  $.
	$d x y A  $.
	$d x y B  $.
	f0_elintg $f set x $.
	f1_elintg $f class A $.
	f2_elintg $f class B $.
	f3_elintg $f class V $.
	i0_elintg $f set y $.
	p_elintg $p |- ( A e. V -> ( A e. |^| B <-> A. x e. B A e. x ) ) $= i0_elintg a_sup_set_class f1_elintg f2_elintg a_cint p_eleq1 i0_elintg a_sup_set_class f1_elintg f0_elintg a_sup_set_class p_eleq1 i0_elintg a_sup_set_class f1_elintg a_wceq i0_elintg a_sup_set_class f0_elintg a_sup_set_class a_wcel f1_elintg f0_elintg a_sup_set_class a_wcel f0_elintg f2_elintg p_ralbidv i0_elintg p_vex f0_elintg i0_elintg a_sup_set_class f2_elintg p_elint2 i0_elintg a_sup_set_class f2_elintg a_cint a_wcel i0_elintg a_sup_set_class f0_elintg a_sup_set_class a_wcel f0_elintg f2_elintg a_wral f1_elintg f2_elintg a_cint a_wcel f1_elintg f0_elintg a_sup_set_class a_wcel f0_elintg f2_elintg a_wral i0_elintg f1_elintg f3_elintg p_vtoclbg $.
$}

$(Membership in class intersection.  (Contributed by NM, 14-Oct-1999.)
       (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_elinti $f class A $.
	f1_elinti $f class B $.
	f2_elinti $f class C $.
	i0_elinti $f set x $.
	p_elinti $p |- ( A e. |^| B -> ( C e. B -> A e. C ) ) $= i0_elinti f0_elinti f1_elinti f1_elinti a_cint p_elintg i0_elinti a_sup_set_class f2_elinti f0_elinti p_eleq2 f0_elinti i0_elinti a_sup_set_class a_wcel f0_elinti f2_elinti a_wcel i0_elinti f2_elinti f1_elinti p_rspccv f0_elinti f1_elinti a_cint a_wcel f0_elinti f1_elinti a_cint a_wcel f0_elinti i0_elinti a_sup_set_class a_wcel i0_elinti f1_elinti a_wral f2_elinti f1_elinti a_wcel f0_elinti f2_elinti a_wcel a_wi p_syl6bi f0_elinti f1_elinti a_cint a_wcel f2_elinti f1_elinti a_wcel f0_elinti f2_elinti a_wcel a_wi p_pm2.43i $.
$}

$(Bound-variable hypothesis builder for intersection.  (Contributed by NM,
       2-Feb-1997.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.) $)

${
	$v x A  $.
	$d y z A  $.
	$d x y z  $.
	f0_nfint $f set x $.
	f1_nfint $f class A $.
	i0_nfint $f set y $.
	i1_nfint $f set z $.
	e0_nfint $e |- F/_ x A $.
	p_nfint $p |- F/_ x |^| A $= i0_nfint i1_nfint f1_nfint p_dfint2 e0_nfint i0_nfint a_sup_set_class i1_nfint a_sup_set_class a_wcel f0_nfint p_nfv i0_nfint a_sup_set_class i1_nfint a_sup_set_class a_wcel f0_nfint i1_nfint f1_nfint p_nfral i0_nfint a_sup_set_class i1_nfint a_sup_set_class a_wcel i1_nfint f1_nfint a_wral f0_nfint i0_nfint p_nfab f0_nfint f1_nfint a_cint i0_nfint a_sup_set_class i1_nfint a_sup_set_class a_wcel i1_nfint f1_nfint a_wral i0_nfint a_cab p_nfcxfr $.
$}

$(Membership in the intersection of a class abstraction.  (Contributed by
       NM, 30-Aug-1993.) $)

${
	$v ph x A  $.
	$d A x y  $.
	$d ph y  $.
	f0_elintab $f wff ph $.
	f1_elintab $f set x $.
	f2_elintab $f class A $.
	i0_elintab $f set y $.
	e0_elintab $e |- A e. _V $.
	p_elintab $p |- ( A e. |^| { x | ph } <-> A. x ( ph -> A e. x ) ) $= e0_elintab i0_elintab f2_elintab f0_elintab f1_elintab a_cab p_elint f0_elintab f1_elintab i0_elintab p_nfsab1 f2_elintab i0_elintab a_sup_set_class a_wcel f1_elintab p_nfv i0_elintab a_sup_set_class f0_elintab f1_elintab a_cab a_wcel f2_elintab i0_elintab a_sup_set_class a_wcel f1_elintab p_nfim f0_elintab f2_elintab f1_elintab a_sup_set_class a_wcel a_wi i0_elintab p_nfv i0_elintab a_sup_set_class f1_elintab a_sup_set_class f0_elintab f1_elintab a_cab p_eleq1 f0_elintab f1_elintab p_abid i0_elintab a_sup_set_class f1_elintab a_sup_set_class a_wceq i0_elintab a_sup_set_class f0_elintab f1_elintab a_cab a_wcel f1_elintab a_sup_set_class f0_elintab f1_elintab a_cab a_wcel f0_elintab p_syl6bb i0_elintab a_sup_set_class f1_elintab a_sup_set_class f2_elintab p_eleq2 i0_elintab a_sup_set_class f1_elintab a_sup_set_class a_wceq i0_elintab a_sup_set_class f0_elintab f1_elintab a_cab a_wcel f0_elintab f2_elintab i0_elintab a_sup_set_class a_wcel f2_elintab f1_elintab a_sup_set_class a_wcel p_imbi12d i0_elintab a_sup_set_class f0_elintab f1_elintab a_cab a_wcel f2_elintab i0_elintab a_sup_set_class a_wcel a_wi f0_elintab f2_elintab f1_elintab a_sup_set_class a_wcel a_wi i0_elintab f1_elintab p_cbval f2_elintab f0_elintab f1_elintab a_cab a_cint a_wcel i0_elintab a_sup_set_class f0_elintab f1_elintab a_cab a_wcel f2_elintab i0_elintab a_sup_set_class a_wcel a_wi i0_elintab a_wal f0_elintab f2_elintab f1_elintab a_sup_set_class a_wcel a_wi f1_elintab a_wal p_bitri $.
$}

$(Membership in the intersection of a class abstraction.  (Contributed by
       NM, 17-Oct-1999.) $)

${
	$v ph x A B  $.
	$d A x  $.
	$d ph  $.
	f0_elintrab $f wff ph $.
	f1_elintrab $f set x $.
	f2_elintrab $f class A $.
	f3_elintrab $f class B $.
	e0_elintrab $e |- A e. _V $.
	p_elintrab $p |- ( A e. |^| { x e. B | ph } <-> A. x e. B ( ph -> A e. x ) ) $= e0_elintrab f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab a_wa f1_elintrab f2_elintrab p_elintab f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab f2_elintrab f1_elintrab a_sup_set_class a_wcel p_impexp f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab a_wa f2_elintrab f1_elintrab a_sup_set_class a_wcel a_wi f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab f2_elintrab f1_elintrab a_sup_set_class a_wcel a_wi a_wi f1_elintrab p_albii f2_elintrab f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab a_wa f1_elintrab a_cab a_cint a_wcel f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab a_wa f2_elintrab f1_elintrab a_sup_set_class a_wcel a_wi f1_elintrab a_wal f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab f2_elintrab f1_elintrab a_sup_set_class a_wcel a_wi a_wi f1_elintrab a_wal p_bitri f0_elintrab f1_elintrab f3_elintrab a_df-rab f0_elintrab f1_elintrab f3_elintrab a_crab f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab a_wa f1_elintrab a_cab p_inteqi f0_elintrab f1_elintrab f3_elintrab a_crab a_cint f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab a_wa f1_elintrab a_cab a_cint f2_elintrab p_eleq2i f0_elintrab f2_elintrab f1_elintrab a_sup_set_class a_wcel a_wi f1_elintrab f3_elintrab a_df-ral f2_elintrab f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab a_wa f1_elintrab a_cab a_cint a_wcel f1_elintrab a_sup_set_class f3_elintrab a_wcel f0_elintrab f2_elintrab f1_elintrab a_sup_set_class a_wcel a_wi a_wi f1_elintrab a_wal f2_elintrab f0_elintrab f1_elintrab f3_elintrab a_crab a_cint a_wcel f0_elintrab f2_elintrab f1_elintrab a_sup_set_class a_wcel a_wi f1_elintrab f3_elintrab a_wral p_3bitr4i $.
$}

$(Membership in the intersection of a class abstraction.  (Contributed by
       NM, 17-Feb-2007.) $)

${
	$v ph x A B V  $.
	$d x y A  $.
	$d y B  $.
	$d y ph  $.
	f0_elintrabg $f wff ph $.
	f1_elintrabg $f set x $.
	f2_elintrabg $f class A $.
	f3_elintrabg $f class B $.
	f4_elintrabg $f class V $.
	i0_elintrabg $f set y $.
	p_elintrabg $p |- ( A e. V -> ( A e. |^| { x e. B | ph } <-> A. x e. B ( ph -> A e. x ) ) ) $= i0_elintrabg a_sup_set_class f2_elintrabg f0_elintrabg f1_elintrabg f3_elintrabg a_crab a_cint p_eleq1 i0_elintrabg a_sup_set_class f2_elintrabg f1_elintrabg a_sup_set_class p_eleq1 i0_elintrabg a_sup_set_class f2_elintrabg a_wceq i0_elintrabg a_sup_set_class f1_elintrabg a_sup_set_class a_wcel f2_elintrabg f1_elintrabg a_sup_set_class a_wcel f0_elintrabg p_imbi2d i0_elintrabg a_sup_set_class f2_elintrabg a_wceq f0_elintrabg i0_elintrabg a_sup_set_class f1_elintrabg a_sup_set_class a_wcel a_wi f0_elintrabg f2_elintrabg f1_elintrabg a_sup_set_class a_wcel a_wi f1_elintrabg f3_elintrabg p_ralbidv i0_elintrabg p_vex f0_elintrabg f1_elintrabg i0_elintrabg a_sup_set_class f3_elintrabg p_elintrab i0_elintrabg a_sup_set_class f0_elintrabg f1_elintrabg f3_elintrabg a_crab a_cint a_wcel f0_elintrabg i0_elintrabg a_sup_set_class f1_elintrabg a_sup_set_class a_wcel a_wi f1_elintrabg f3_elintrabg a_wral f2_elintrabg f0_elintrabg f1_elintrabg f3_elintrabg a_crab a_cint a_wcel f0_elintrabg f2_elintrabg f1_elintrabg a_sup_set_class a_wcel a_wi f1_elintrabg f3_elintrabg a_wral i0_elintrabg f2_elintrabg f4_elintrabg p_vtoclbg $.
$}

$(The intersection of the empty set is the universal class.  Exercise 2 of
       [TakeutiZaring] p. 44.  (Contributed by NM, 18-Aug-1993.) $)

${
	$v  $.
	$d x y  $.
	$d y  $.
	$d y  $.
	i0_int0 $f set x $.
	i1_int0 $f set y $.
	p_int0 $p |- |^| (/) = _V $= i1_int0 a_sup_set_class p_noel i1_int0 a_sup_set_class a_c0 a_wcel i0_int0 a_sup_set_class i1_int0 a_sup_set_class a_wcel p_pm2.21i i1_int0 a_sup_set_class a_c0 a_wcel i0_int0 a_sup_set_class i1_int0 a_sup_set_class a_wcel a_wi i1_int0 a_ax-gen i0_int0 a_sup_set_class p_eqid i1_int0 a_sup_set_class a_c0 a_wcel i0_int0 a_sup_set_class i1_int0 a_sup_set_class a_wcel a_wi i1_int0 a_wal i0_int0 a_sup_set_class i0_int0 a_sup_set_class a_wceq p_2th i1_int0 a_sup_set_class a_c0 a_wcel i0_int0 a_sup_set_class i1_int0 a_sup_set_class a_wcel a_wi i1_int0 a_wal i0_int0 a_sup_set_class i0_int0 a_sup_set_class a_wceq i0_int0 p_abbii i0_int0 i1_int0 a_c0 a_df-int i0_int0 a_df-v i1_int0 a_sup_set_class a_c0 a_wcel i0_int0 a_sup_set_class i1_int0 a_sup_set_class a_wcel a_wi i1_int0 a_wal i0_int0 a_cab i0_int0 a_sup_set_class i0_int0 a_sup_set_class a_wceq i0_int0 a_cab a_c0 a_cint a_cvv p_3eqtr4i $.
$}

$(An element of a class includes the intersection of the class.  Exercise
       4 of [TakeutiZaring] p. 44 (with correction), generalized to classes.
       (Contributed by NM, 18-Nov-1995.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	$d y  $.
	f0_intss1 $f class A $.
	f1_intss1 $f class B $.
	i0_intss1 $f set x $.
	i1_intss1 $f set y $.
	p_intss1 $p |- ( A e. B -> |^| B C_ A ) $= i0_intss1 p_vex i1_intss1 i0_intss1 a_sup_set_class f1_intss1 p_elint i1_intss1 a_sup_set_class f0_intss1 f1_intss1 p_eleq1 i1_intss1 a_sup_set_class f0_intss1 i0_intss1 a_sup_set_class p_eleq2 i1_intss1 a_sup_set_class f0_intss1 a_wceq i1_intss1 a_sup_set_class f1_intss1 a_wcel f0_intss1 f1_intss1 a_wcel i0_intss1 a_sup_set_class i1_intss1 a_sup_set_class a_wcel i0_intss1 a_sup_set_class f0_intss1 a_wcel p_imbi12d i1_intss1 a_sup_set_class f1_intss1 a_wcel i0_intss1 a_sup_set_class i1_intss1 a_sup_set_class a_wcel a_wi f0_intss1 f1_intss1 a_wcel i0_intss1 a_sup_set_class f0_intss1 a_wcel a_wi i1_intss1 f0_intss1 f1_intss1 p_spcgv i1_intss1 a_sup_set_class f1_intss1 a_wcel i0_intss1 a_sup_set_class i1_intss1 a_sup_set_class a_wcel a_wi i1_intss1 a_wal f0_intss1 f1_intss1 a_wcel i0_intss1 a_sup_set_class f0_intss1 a_wcel p_pm2.43a i0_intss1 a_sup_set_class f1_intss1 a_cint a_wcel i1_intss1 a_sup_set_class f1_intss1 a_wcel i0_intss1 a_sup_set_class i1_intss1 a_sup_set_class a_wcel a_wi i1_intss1 a_wal f0_intss1 f1_intss1 a_wcel i0_intss1 a_sup_set_class f0_intss1 a_wcel p_syl5bi f0_intss1 f1_intss1 a_wcel i0_intss1 f1_intss1 a_cint f0_intss1 p_ssrdv $.
$}

$(Subclass of a class intersection.  Theorem 5.11(viii) of [Monk1] p. 52
       and its converse.  (Contributed by NM, 14-Oct-1999.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	$d y  $.
	f0_ssint $f set x $.
	f1_ssint $f class A $.
	f2_ssint $f class B $.
	i0_ssint $f set y $.
	p_ssint $p |- ( A C_ |^| B <-> A. x e. B A C_ x ) $= i0_ssint f1_ssint f2_ssint a_cint p_dfss3 i0_ssint p_vex f0_ssint i0_ssint a_sup_set_class f2_ssint p_elint2 i0_ssint a_sup_set_class f2_ssint a_cint a_wcel i0_ssint a_sup_set_class f0_ssint a_sup_set_class a_wcel f0_ssint f2_ssint a_wral i0_ssint f1_ssint p_ralbii i0_ssint a_sup_set_class f0_ssint a_sup_set_class a_wcel i0_ssint f0_ssint f1_ssint f2_ssint p_ralcom i0_ssint f1_ssint f0_ssint a_sup_set_class p_dfss3 f1_ssint f0_ssint a_sup_set_class a_wss i0_ssint a_sup_set_class f0_ssint a_sup_set_class a_wcel i0_ssint f1_ssint a_wral f0_ssint f2_ssint p_ralbii i0_ssint a_sup_set_class f0_ssint a_sup_set_class a_wcel f0_ssint f2_ssint a_wral i0_ssint f1_ssint a_wral i0_ssint a_sup_set_class f0_ssint a_sup_set_class a_wcel i0_ssint f1_ssint a_wral f0_ssint f2_ssint a_wral f1_ssint f0_ssint a_sup_set_class a_wss f0_ssint f2_ssint a_wral p_bitr4i f1_ssint f2_ssint a_cint a_wss i0_ssint a_sup_set_class f2_ssint a_cint a_wcel i0_ssint f1_ssint a_wral i0_ssint a_sup_set_class f0_ssint a_sup_set_class a_wcel f0_ssint f2_ssint a_wral i0_ssint f1_ssint a_wral f1_ssint f0_ssint a_sup_set_class a_wss f0_ssint f2_ssint a_wral p_3bitri $.
$}

$(Subclass of the intersection of a class abstraction.  (Contributed by
       NM, 31-Jul-2006.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph x A  $.
	$d x y A  $.
	$d x y  $.
	$d y ph  $.
	f0_ssintab $f wff ph $.
	f1_ssintab $f set x $.
	f2_ssintab $f class A $.
	i0_ssintab $f set y $.
	p_ssintab $p |- ( A C_ |^| { x | ph } <-> A. x ( ph -> A C_ x ) ) $= i0_ssintab f2_ssintab f0_ssintab f1_ssintab a_cab p_ssint i0_ssintab a_sup_set_class f1_ssintab a_sup_set_class f2_ssintab p_sseq2 f0_ssintab f2_ssintab i0_ssintab a_sup_set_class a_wss f2_ssintab f1_ssintab a_sup_set_class a_wss i0_ssintab f1_ssintab p_ralab2 f2_ssintab f0_ssintab f1_ssintab a_cab a_cint a_wss f2_ssintab i0_ssintab a_sup_set_class a_wss i0_ssintab f0_ssintab f1_ssintab a_cab a_wral f0_ssintab f2_ssintab f1_ssintab a_sup_set_class a_wss a_wi f1_ssintab a_wal p_bitri $.
$}

$(Subclass of the least upper bound.  (Contributed by NM, 8-Aug-2000.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	$d y  $.
	f0_ssintub $f set x $.
	f1_ssintub $f class A $.
	f2_ssintub $f class B $.
	i0_ssintub $f set y $.
	p_ssintub $p |- A C_ |^| { x e. B | A C_ x } $= i0_ssintub f1_ssintub f1_ssintub f0_ssintub a_sup_set_class a_wss f0_ssintub f2_ssintub a_crab p_ssint f0_ssintub a_sup_set_class i0_ssintub a_sup_set_class f1_ssintub p_sseq2 f1_ssintub f0_ssintub a_sup_set_class a_wss f1_ssintub i0_ssintub a_sup_set_class a_wss f0_ssintub i0_ssintub a_sup_set_class f2_ssintub p_elrab i0_ssintub a_sup_set_class f1_ssintub f0_ssintub a_sup_set_class a_wss f0_ssintub f2_ssintub a_crab a_wcel i0_ssintub a_sup_set_class f2_ssintub a_wcel f1_ssintub i0_ssintub a_sup_set_class a_wss p_simprbi f1_ssintub f1_ssintub f0_ssintub a_sup_set_class a_wss f0_ssintub f2_ssintub a_crab a_cint a_wss f1_ssintub i0_ssintub a_sup_set_class a_wss i0_ssintub f1_ssintub f0_ssintub a_sup_set_class a_wss f0_ssintub f2_ssintub a_crab p_mprgbir $.
$}

$(Subclass of the minimum value of class of supersets.  (Contributed by
       NM, 10-Aug-2006.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x  $.
	$d ph  $.
	f0_ssmin $f wff ph $.
	f1_ssmin $f set x $.
	f2_ssmin $f class A $.
	p_ssmin $p |- A C_ |^| { x | ( A C_ x /\ ph ) } $= f2_ssmin f1_ssmin a_sup_set_class a_wss f0_ssmin a_wa f1_ssmin f2_ssmin p_ssintab f2_ssmin f1_ssmin a_sup_set_class a_wss f0_ssmin p_simpl f2_ssmin f2_ssmin f1_ssmin a_sup_set_class a_wss f0_ssmin a_wa f1_ssmin a_cab a_cint a_wss f2_ssmin f1_ssmin a_sup_set_class a_wss f0_ssmin a_wa f2_ssmin f1_ssmin a_sup_set_class a_wss a_wi f1_ssmin p_mpgbir $.
$}

$(Any member of a class is the smallest of those members that include it.
       (Contributed by NM, 13-Aug-2002.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	$d y  $.
	f0_intmin $f set x $.
	f1_intmin $f class A $.
	f2_intmin $f class B $.
	i0_intmin $f set y $.
	p_intmin $p |- ( A e. B -> |^| { x e. B | A C_ x } = A ) $= i0_intmin p_vex f1_intmin f0_intmin a_sup_set_class a_wss f0_intmin i0_intmin a_sup_set_class f2_intmin p_elintrab f1_intmin p_ssid f0_intmin a_sup_set_class f1_intmin f1_intmin p_sseq2 f0_intmin a_sup_set_class f1_intmin i0_intmin a_sup_set_class p_eleq2 f0_intmin a_sup_set_class f1_intmin a_wceq f1_intmin f0_intmin a_sup_set_class a_wss f1_intmin f1_intmin a_wss i0_intmin a_sup_set_class f0_intmin a_sup_set_class a_wcel i0_intmin a_sup_set_class f1_intmin a_wcel p_imbi12d f1_intmin f0_intmin a_sup_set_class a_wss i0_intmin a_sup_set_class f0_intmin a_sup_set_class a_wcel a_wi f1_intmin f1_intmin a_wss i0_intmin a_sup_set_class f1_intmin a_wcel a_wi f0_intmin f1_intmin f2_intmin p_rspcv f1_intmin f2_intmin a_wcel f1_intmin f0_intmin a_sup_set_class a_wss i0_intmin a_sup_set_class f0_intmin a_sup_set_class a_wcel a_wi f0_intmin f2_intmin a_wral f1_intmin f1_intmin a_wss i0_intmin a_sup_set_class f1_intmin a_wcel p_mpii i0_intmin a_sup_set_class f1_intmin f0_intmin a_sup_set_class a_wss f0_intmin f2_intmin a_crab a_cint a_wcel f1_intmin f0_intmin a_sup_set_class a_wss i0_intmin a_sup_set_class f0_intmin a_sup_set_class a_wcel a_wi f0_intmin f2_intmin a_wral f1_intmin f2_intmin a_wcel i0_intmin a_sup_set_class f1_intmin a_wcel p_syl5bi f1_intmin f2_intmin a_wcel i0_intmin f1_intmin f0_intmin a_sup_set_class a_wss f0_intmin f2_intmin a_crab a_cint f1_intmin p_ssrdv f0_intmin f1_intmin f2_intmin p_ssintub f1_intmin f1_intmin f0_intmin a_sup_set_class a_wss f0_intmin f2_intmin a_crab a_cint a_wss f1_intmin f2_intmin a_wcel p_a1i f1_intmin f2_intmin a_wcel f1_intmin f0_intmin a_sup_set_class a_wss f0_intmin f2_intmin a_crab a_cint f1_intmin p_eqssd $.
$}

$(Intersection of subclasses.  (Contributed by NM, 14-Oct-1999.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	$d y  $.
	f0_intss $f class A $.
	f1_intss $f class B $.
	i0_intss $f set x $.
	i1_intss $f set y $.
	p_intss $p |- ( A C_ B -> |^| B C_ |^| A ) $= i1_intss a_sup_set_class f0_intss a_wcel i1_intss a_sup_set_class f1_intss a_wcel i0_intss a_sup_set_class i1_intss a_sup_set_class a_wcel p_imim1 i1_intss a_sup_set_class f0_intss a_wcel i1_intss a_sup_set_class f1_intss a_wcel a_wi i1_intss a_sup_set_class f1_intss a_wcel i0_intss a_sup_set_class i1_intss a_sup_set_class a_wcel a_wi i1_intss a_sup_set_class f0_intss a_wcel i0_intss a_sup_set_class i1_intss a_sup_set_class a_wcel a_wi i1_intss p_al2imi i0_intss p_vex i1_intss i0_intss a_sup_set_class f1_intss p_elint i0_intss p_vex i1_intss i0_intss a_sup_set_class f0_intss p_elint i1_intss a_sup_set_class f0_intss a_wcel i1_intss a_sup_set_class f1_intss a_wcel a_wi i1_intss a_wal i1_intss a_sup_set_class f1_intss a_wcel i0_intss a_sup_set_class i1_intss a_sup_set_class a_wcel a_wi i1_intss a_wal i1_intss a_sup_set_class f0_intss a_wcel i0_intss a_sup_set_class i1_intss a_sup_set_class a_wcel a_wi i1_intss a_wal i0_intss a_sup_set_class f1_intss a_cint a_wcel i0_intss a_sup_set_class f0_intss a_cint a_wcel p_3imtr4g i1_intss a_sup_set_class f0_intss a_wcel i1_intss a_sup_set_class f1_intss a_wcel a_wi i1_intss a_wal i0_intss a_sup_set_class f1_intss a_cint a_wcel i0_intss a_sup_set_class f0_intss a_cint a_wcel a_wi i0_intss p_alrimiv i1_intss f0_intss f1_intss p_dfss2 i0_intss f1_intss a_cint f0_intss a_cint p_dfss2 i1_intss a_sup_set_class f0_intss a_wcel i1_intss a_sup_set_class f1_intss a_wcel a_wi i1_intss a_wal i0_intss a_sup_set_class f1_intss a_cint a_wcel i0_intss a_sup_set_class f0_intss a_cint a_wcel a_wi i0_intss a_wal f0_intss f1_intss a_wss f1_intss a_cint f0_intss a_cint a_wss p_3imtr4i $.
$}

$(The intersection of a nonempty set is a subclass of its union.
       (Contributed by NM, 29-Jul-2006.) $)

${
	$v A  $.
	$d x y A  $.
	$d x y  $.
	$d y  $.
	f0_intssuni $f class A $.
	i0_intssuni $f set x $.
	i1_intssuni $f set y $.
	p_intssuni $p |- ( A =/= (/) -> |^| A C_ U. A ) $= i0_intssuni a_sup_set_class i1_intssuni a_sup_set_class a_wcel i1_intssuni f0_intssuni p_r19.2z f0_intssuni a_c0 a_wne i0_intssuni a_sup_set_class i1_intssuni a_sup_set_class a_wcel i1_intssuni f0_intssuni a_wral i0_intssuni a_sup_set_class i1_intssuni a_sup_set_class a_wcel i1_intssuni f0_intssuni a_wrex p_ex i0_intssuni p_vex i1_intssuni i0_intssuni a_sup_set_class f0_intssuni p_elint2 i1_intssuni i0_intssuni a_sup_set_class f0_intssuni p_eluni2 f0_intssuni a_c0 a_wne i0_intssuni a_sup_set_class i1_intssuni a_sup_set_class a_wcel i1_intssuni f0_intssuni a_wral i0_intssuni a_sup_set_class i1_intssuni a_sup_set_class a_wcel i1_intssuni f0_intssuni a_wrex i0_intssuni a_sup_set_class f0_intssuni a_cint a_wcel i0_intssuni a_sup_set_class f0_intssuni a_cuni a_wcel p_3imtr4g f0_intssuni a_c0 a_wne i0_intssuni f0_intssuni a_cint f0_intssuni a_cuni p_ssrdv $.
$}

$(Subclass of the intersection of a restricted class builder.
       (Contributed by NM, 30-Jan-2015.) $)

${
	$v ph x A B  $.
	$d x A  $.
	f0_ssintrab $f wff ph $.
	f1_ssintrab $f set x $.
	f2_ssintrab $f class A $.
	f3_ssintrab $f class B $.
	p_ssintrab $p |- ( A C_ |^| { x e. B | ph } <-> A. x e. B ( ph -> A C_ x ) ) $= f0_ssintrab f1_ssintrab f3_ssintrab a_df-rab f0_ssintrab f1_ssintrab f3_ssintrab a_crab f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab a_wa f1_ssintrab a_cab p_inteqi f0_ssintrab f1_ssintrab f3_ssintrab a_crab a_cint f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab a_wa f1_ssintrab a_cab a_cint f2_ssintrab p_sseq2i f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab f2_ssintrab f1_ssintrab a_sup_set_class a_wss p_impexp f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab a_wa f2_ssintrab f1_ssintrab a_sup_set_class a_wss a_wi f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab f2_ssintrab f1_ssintrab a_sup_set_class a_wss a_wi a_wi f1_ssintrab p_albii f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab a_wa f1_ssintrab f2_ssintrab p_ssintab f0_ssintrab f2_ssintrab f1_ssintrab a_sup_set_class a_wss a_wi f1_ssintrab f3_ssintrab a_df-ral f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab a_wa f2_ssintrab f1_ssintrab a_sup_set_class a_wss a_wi f1_ssintrab a_wal f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab f2_ssintrab f1_ssintrab a_sup_set_class a_wss a_wi a_wi f1_ssintrab a_wal f2_ssintrab f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab a_wa f1_ssintrab a_cab a_cint a_wss f0_ssintrab f2_ssintrab f1_ssintrab a_sup_set_class a_wss a_wi f1_ssintrab f3_ssintrab a_wral p_3bitr4i f2_ssintrab f0_ssintrab f1_ssintrab f3_ssintrab a_crab a_cint a_wss f2_ssintrab f1_ssintrab a_sup_set_class f3_ssintrab a_wcel f0_ssintrab a_wa f1_ssintrab a_cab a_cint a_wss f0_ssintrab f2_ssintrab f1_ssintrab a_sup_set_class a_wss a_wi f1_ssintrab f3_ssintrab a_wral p_bitri $.
$}

$(If the union of a class is included in its intersection, the class is
     either the empty set or a singleton ( ~ uniintsn ).  (Contributed by NM,
     30-Oct-2010.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A  $.
	f0_unissint $f class A $.
	p_unissint $p |- ( U. A C_ |^| A <-> ( A = (/) \/ U. A = |^| A ) ) $= f0_unissint a_cuni f0_unissint a_cint a_wss f0_unissint a_c0 a_wceq a_wn p_simpl f0_unissint a_c0 a_df-ne f0_unissint p_intssuni f0_unissint a_c0 a_wceq a_wn f0_unissint a_c0 a_wne f0_unissint a_cint f0_unissint a_cuni a_wss p_sylbir f0_unissint a_c0 a_wceq a_wn f0_unissint a_cint f0_unissint a_cuni a_wss f0_unissint a_cuni f0_unissint a_cint a_wss p_adantl f0_unissint a_cuni f0_unissint a_cint a_wss f0_unissint a_c0 a_wceq a_wn a_wa f0_unissint a_cuni f0_unissint a_cint p_eqssd f0_unissint a_cuni f0_unissint a_cint a_wss f0_unissint a_c0 a_wceq a_wn f0_unissint a_cuni f0_unissint a_cint a_wceq p_ex f0_unissint a_cuni f0_unissint a_cint a_wss f0_unissint a_c0 a_wceq f0_unissint a_cuni f0_unissint a_cint a_wceq p_orrd f0_unissint a_cuni p_ssv p_int0 f0_unissint a_cuni a_cvv a_c0 a_cint p_sseqtr4i f0_unissint a_c0 p_inteq f0_unissint a_c0 a_wceq a_c0 a_cint f0_unissint a_cuni f0_unissint a_cint p_syl5sseqr f0_unissint a_cuni f0_unissint a_cint p_eqimss f0_unissint a_c0 a_wceq f0_unissint a_cuni f0_unissint a_cint a_wss f0_unissint a_cuni f0_unissint a_cint a_wceq p_jaoi f0_unissint a_cuni f0_unissint a_cint a_wss f0_unissint a_c0 a_wceq f0_unissint a_cuni f0_unissint a_cint a_wceq a_wo p_impbii $.
$}

$(Subclass relationship for intersection and union.  (Contributed by NM,
     29-Jul-2006.) $)

${
	$v A B  $.
	f0_intssuni2 $f class A $.
	f1_intssuni2 $f class B $.
	p_intssuni2 $p |- ( ( A C_ B /\ A =/= (/) ) -> |^| A C_ U. B ) $= f0_intssuni2 p_intssuni f0_intssuni2 f1_intssuni2 p_uniss f0_intssuni2 a_c0 a_wne f0_intssuni2 f1_intssuni2 a_wss f0_intssuni2 a_cint f0_intssuni2 a_cuni f1_intssuni2 a_cuni p_sylan9ssr $.
$}

$(Under subset ordering, the intersection of a restricted class
       abstraction is less than or equal to any of its members.  (Contributed
       by NM, 7-Sep-2013.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_intminss $f wff ph $.
	f1_intminss $f wff ps $.
	f2_intminss $f set x $.
	f3_intminss $f class A $.
	f4_intminss $f class B $.
	e0_intminss $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_intminss $p |- ( ( A e. B /\ ps ) -> |^| { x e. B | ph } C_ A ) $= e0_intminss f0_intminss f1_intminss f2_intminss f3_intminss f4_intminss p_elrab f3_intminss f0_intminss f2_intminss f4_intminss a_crab p_intss1 f3_intminss f4_intminss a_wcel f1_intminss a_wa f3_intminss f0_intminss f2_intminss f4_intminss a_crab a_wcel f0_intminss f2_intminss f4_intminss a_crab a_cint f3_intminss a_wss p_sylbir $.
$}

$(Any set is the smallest of all sets that include it.  (Contributed by
       NM, 20-Sep-2003.) $)

${
	$v x A  $.
	$d x A  $.
	f0_intmin2 $f set x $.
	f1_intmin2 $f class A $.
	e0_intmin2 $e |- A e. _V $.
	p_intmin2 $p |- |^| { x | A C_ x } = A $= f1_intmin2 f0_intmin2 a_sup_set_class a_wss f0_intmin2 p_rabab f1_intmin2 f0_intmin2 a_sup_set_class a_wss f0_intmin2 a_cvv a_crab f1_intmin2 f0_intmin2 a_sup_set_class a_wss f0_intmin2 a_cab p_inteqi e0_intmin2 f0_intmin2 f1_intmin2 a_cvv p_intmin f1_intmin2 a_cvv a_wcel f1_intmin2 f0_intmin2 a_sup_set_class a_wss f0_intmin2 a_cvv a_crab a_cint f1_intmin2 a_wceq a_ax-mp f1_intmin2 f0_intmin2 a_sup_set_class a_wss f0_intmin2 a_cvv a_crab a_cint f1_intmin2 f0_intmin2 a_sup_set_class a_wss f0_intmin2 a_cab a_cint f1_intmin2 p_eqtr3i $.
$}

$(Under subset ordering, the intersection of a class abstraction is less
       than or equal to any of its members.  (Contributed by NM,
       3-Jul-2005.) $)

${
	$v ph ps x A V  $.
	$d x A  $.
	$d x ps  $.
	f0_intmin3 $f wff ph $.
	f1_intmin3 $f wff ps $.
	f2_intmin3 $f set x $.
	f3_intmin3 $f class A $.
	f4_intmin3 $f class V $.
	e0_intmin3 $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_intmin3 $e |- ps $.
	p_intmin3 $p |- ( A e. V -> |^| { x | ph } C_ A ) $= e1_intmin3 e0_intmin3 f0_intmin3 f1_intmin3 f2_intmin3 f3_intmin3 f4_intmin3 p_elabg f3_intmin3 f4_intmin3 a_wcel f3_intmin3 f0_intmin3 f2_intmin3 a_cab a_wcel f1_intmin3 p_mpbiri f3_intmin3 f0_intmin3 f2_intmin3 a_cab p_intss1 f3_intmin3 f4_intmin3 a_wcel f3_intmin3 f0_intmin3 f2_intmin3 a_cab a_wcel f0_intmin3 f2_intmin3 a_cab a_cint f3_intmin3 a_wss p_syl $.
$}

$(Elimination of a conjunct in a class intersection.  (Contributed by NM,
       31-Jul-2006.) $)

${
	$v ph x A  $.
	$d x y A  $.
	$d y ph  $.
	f0_intmin4 $f wff ph $.
	f1_intmin4 $f set x $.
	f2_intmin4 $f class A $.
	i0_intmin4 $f set y $.
	p_intmin4 $p |- ( A C_ |^| { x | ph } -> |^| { x | ( A C_ x /\ ph ) } = |^| { x | ph } ) $= f0_intmin4 f1_intmin4 f2_intmin4 p_ssintab f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 p_simpr f0_intmin4 f2_intmin4 f1_intmin4 a_sup_set_class a_wss p_ancr f0_intmin4 f2_intmin4 f1_intmin4 a_sup_set_class a_wss a_wi f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa f0_intmin4 p_impbid2 f0_intmin4 f2_intmin4 f1_intmin4 a_sup_set_class a_wss a_wi f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa f0_intmin4 i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel p_imbi1d f0_intmin4 f2_intmin4 f1_intmin4 a_sup_set_class a_wss a_wi f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f0_intmin4 i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi a_wb f1_intmin4 p_alimi f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f0_intmin4 i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f1_intmin4 p_albi f0_intmin4 f2_intmin4 f1_intmin4 a_sup_set_class a_wss a_wi f1_intmin4 a_wal f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f0_intmin4 i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi a_wb f1_intmin4 a_wal f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f1_intmin4 a_wal f0_intmin4 i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f1_intmin4 a_wal a_wb p_syl f2_intmin4 f0_intmin4 f1_intmin4 a_cab a_cint a_wss f0_intmin4 f2_intmin4 f1_intmin4 a_sup_set_class a_wss a_wi f1_intmin4 a_wal f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f1_intmin4 a_wal f0_intmin4 i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f1_intmin4 a_wal a_wb p_sylbi i0_intmin4 p_vex f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa f1_intmin4 i0_intmin4 a_sup_set_class p_elintab i0_intmin4 p_vex f0_intmin4 f1_intmin4 i0_intmin4 a_sup_set_class p_elintab f2_intmin4 f0_intmin4 f1_intmin4 a_cab a_cint a_wss f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f1_intmin4 a_wal f0_intmin4 i0_intmin4 a_sup_set_class f1_intmin4 a_sup_set_class a_wcel a_wi f1_intmin4 a_wal i0_intmin4 a_sup_set_class f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa f1_intmin4 a_cab a_cint a_wcel i0_intmin4 a_sup_set_class f0_intmin4 f1_intmin4 a_cab a_cint a_wcel p_3bitr4g f2_intmin4 f0_intmin4 f1_intmin4 a_cab a_cint a_wss i0_intmin4 f2_intmin4 f1_intmin4 a_sup_set_class a_wss f0_intmin4 a_wa f1_intmin4 a_cab a_cint f0_intmin4 f1_intmin4 a_cab a_cint p_eqrdv $.
$}

$(The intersection of a special case of a class abstraction. ` y ` may be
       free in ` ph ` and ` A ` , which can be thought of a ` ph ( y ) ` and
       ` A ( y ) ` .  Typically, ~ abrexex2 or ~ abexssex can be used to
       satisfy the second hypothesis.  (Contributed by NM, 28-Jul-2006.)
       (Proof shortened by Mario Carneiro, 14-Nov-2016.) $)

${
	$v ph x y A  $.
	$d x z A  $.
	$d x z ph  $.
	$d x y z  $.
	f0_intab $f wff ph $.
	f1_intab $f set x $.
	f2_intab $f set y $.
	f3_intab $f class A $.
	i0_intab $f set z $.
	e0_intab $e |- A e. _V $.
	e1_intab $e |- { x | E. y ( ph /\ x = A ) } e. _V $.
	p_intab $p |- |^| { x | A. y ( ph -> A e. x ) } = { x | E. y ( ph /\ x = A ) } $= i0_intab a_sup_set_class f1_intab a_sup_set_class f3_intab p_eqeq1 i0_intab a_sup_set_class f1_intab a_sup_set_class a_wceq i0_intab a_sup_set_class f3_intab a_wceq f1_intab a_sup_set_class f3_intab a_wceq f0_intab p_anbi2d i0_intab a_sup_set_class f1_intab a_sup_set_class a_wceq f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f0_intab f1_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab p_exbidv f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f0_intab f1_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab f1_intab p_cbvabv e1_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab f0_intab f1_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f1_intab a_cab a_cvv p_eqeltri f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab p_nfe1 f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f2_intab i0_intab p_nfab f2_intab f1_intab a_sup_set_class f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab p_nfeq2 f1_intab a_sup_set_class f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab f3_intab p_eleq2 f1_intab a_sup_set_class f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab a_wceq f3_intab f1_intab a_sup_set_class a_wcel f3_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab a_wcel f0_intab p_imbi2d f1_intab a_sup_set_class f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab a_wceq f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f0_intab f3_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab a_wcel a_wi f2_intab p_albid f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f0_intab f3_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab a_wcel a_wi f2_intab a_wal f1_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab p_elab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab p_19.8a f0_intab i0_intab a_sup_set_class f3_intab a_wceq f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex p_ex f0_intab i0_intab a_sup_set_class f3_intab a_wceq f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex a_wi i0_intab p_alrimiv e0_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab f3_intab p_sbc6 f0_intab i0_intab a_sup_set_class f3_intab a_wceq f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex a_wi i0_intab a_wal f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab f3_intab a_wsbc p_sylibr f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab f3_intab a_df-sbc f0_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab f3_intab a_wsbc f3_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab a_wcel p_sylib f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab a_cab a_wcel f0_intab f3_intab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab a_wcel a_wi f2_intab p_mpgbir f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab a_cab p_intss1 f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab a_cab a_wcel f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab a_cab a_cint f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab a_wss a_ax-mp f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab p_19.29r f0_intab i0_intab a_sup_set_class f3_intab a_wceq f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi p_simplr f0_intab f3_intab f1_intab a_sup_set_class a_wcel p_pm3.35 f0_intab f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f3_intab f1_intab a_sup_set_class a_wcel i0_intab a_sup_set_class f3_intab a_wceq p_adantlr f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi a_wa i0_intab a_sup_set_class f3_intab f1_intab a_sup_set_class p_eqeltrd f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi a_wa i0_intab a_sup_set_class f1_intab a_sup_set_class a_wcel f2_intab p_exlimiv f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal a_wa f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi a_wa f2_intab a_wex i0_intab a_sup_set_class f1_intab a_sup_set_class a_wcel p_syl f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal i0_intab a_sup_set_class f1_intab a_sup_set_class a_wcel p_ex f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal i0_intab a_sup_set_class f1_intab a_sup_set_class a_wcel a_wi f1_intab p_alrimiv i0_intab p_vex f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab i0_intab a_sup_set_class p_elintab f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal i0_intab a_sup_set_class f1_intab a_sup_set_class a_wcel a_wi f1_intab a_wal i0_intab a_sup_set_class f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab a_cab a_cint a_wcel p_sylibr f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab a_cab a_cint p_abssi f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab a_cab a_cint f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab p_eqssi i0_intab a_sup_set_class f1_intab a_sup_set_class f3_intab p_eqeq1 i0_intab a_sup_set_class f1_intab a_sup_set_class a_wceq i0_intab a_sup_set_class f3_intab a_wceq f1_intab a_sup_set_class f3_intab a_wceq f0_intab p_anbi2d i0_intab a_sup_set_class f1_intab a_sup_set_class a_wceq f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f0_intab f1_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab p_exbidv f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f0_intab f1_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab f1_intab p_cbvabv f0_intab f3_intab f1_intab a_sup_set_class a_wcel a_wi f2_intab a_wal f1_intab a_cab a_cint f0_intab i0_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex i0_intab a_cab f0_intab f1_intab a_sup_set_class f3_intab a_wceq a_wa f2_intab a_wex f1_intab a_cab p_eqtri $.
$}

$(The intersection of a class containing the empty set is empty.
     (Contributed by NM, 24-Apr-2004.) $)

${
	$v A  $.
	f0_int0el $f class A $.
	p_int0el $p |- ( (/) e. A -> |^| A = (/) ) $= a_c0 f0_int0el p_intss1 f0_int0el a_cint p_0ss a_c0 f0_int0el a_cint a_wss a_c0 f0_int0el a_wcel p_a1i a_c0 f0_int0el a_wcel f0_int0el a_cint a_c0 p_eqssd $.
$}

$(The class intersection of the union of two classes.  Theorem 78 of
       [Suppes] p. 42.  (Contributed by NM, 22-Sep-2002.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_intun $f class A $.
	f1_intun $f class B $.
	i0_intun $f set x $.
	i1_intun $f set y $.
	p_intun $p |- |^| ( A u. B ) = ( |^| A i^i |^| B ) $= i1_intun a_sup_set_class f0_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_sup_set_class f1_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun p_19.26 i1_intun a_sup_set_class f0_intun f1_intun p_elun i1_intun a_sup_set_class f0_intun f1_intun a_cun a_wcel i1_intun a_sup_set_class f0_intun a_wcel i1_intun a_sup_set_class f1_intun a_wcel a_wo i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel p_imbi1i i1_intun a_sup_set_class f0_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel i1_intun a_sup_set_class f1_intun a_wcel p_jaob i1_intun a_sup_set_class f0_intun f1_intun a_cun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_sup_set_class f0_intun a_wcel i1_intun a_sup_set_class f1_intun a_wcel a_wo i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_sup_set_class f0_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_sup_set_class f1_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi a_wa p_bitri i1_intun a_sup_set_class f0_intun f1_intun a_cun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_sup_set_class f0_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_sup_set_class f1_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi a_wa i1_intun p_albii i0_intun p_vex i1_intun i0_intun a_sup_set_class f0_intun p_elint i0_intun p_vex i1_intun i0_intun a_sup_set_class f1_intun p_elint i0_intun a_sup_set_class f0_intun a_cint a_wcel i1_intun a_sup_set_class f0_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_wal i0_intun a_sup_set_class f1_intun a_cint a_wcel i1_intun a_sup_set_class f1_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_wal p_anbi12i i1_intun a_sup_set_class f0_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_sup_set_class f1_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi a_wa i1_intun a_wal i1_intun a_sup_set_class f0_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_wal i1_intun a_sup_set_class f1_intun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_wal a_wa i1_intun a_sup_set_class f0_intun f1_intun a_cun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_wal i0_intun a_sup_set_class f0_intun a_cint a_wcel i0_intun a_sup_set_class f1_intun a_cint a_wcel a_wa p_3bitr4i i0_intun p_vex i1_intun i0_intun a_sup_set_class f0_intun f1_intun a_cun p_elint i0_intun a_sup_set_class f0_intun a_cint f1_intun a_cint p_elin i1_intun a_sup_set_class f0_intun f1_intun a_cun a_wcel i0_intun a_sup_set_class i1_intun a_sup_set_class a_wcel a_wi i1_intun a_wal i0_intun a_sup_set_class f0_intun a_cint a_wcel i0_intun a_sup_set_class f1_intun a_cint a_wcel a_wa i0_intun a_sup_set_class f0_intun f1_intun a_cun a_cint a_wcel i0_intun a_sup_set_class f0_intun a_cint f1_intun a_cint a_cin a_wcel p_3bitr4i i0_intun f0_intun f1_intun a_cun a_cint f0_intun a_cint f1_intun a_cint a_cin p_eqriv $.
$}

$(The intersection of a pair is the intersection of its members.  Theorem
       71 of [Suppes] p. 42.  (Contributed by NM, 14-Oct-1999.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_intpr $f class A $.
	f1_intpr $f class B $.
	i0_intpr $f set x $.
	i1_intpr $f set y $.
	e0_intpr $e |- A e. _V $.
	e1_intpr $e |- B e. _V $.
	p_intpr $p |- |^| { A , B } = ( A i^i B ) $= i1_intpr a_sup_set_class f0_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_sup_set_class f1_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr p_19.26 i1_intpr p_vex i1_intpr a_sup_set_class f0_intpr f1_intpr p_elpr i1_intpr a_sup_set_class f0_intpr f1_intpr a_cpr a_wcel i1_intpr a_sup_set_class f0_intpr a_wceq i1_intpr a_sup_set_class f1_intpr a_wceq a_wo i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel p_imbi1i i1_intpr a_sup_set_class f0_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel i1_intpr a_sup_set_class f1_intpr a_wceq p_jaob i1_intpr a_sup_set_class f0_intpr f1_intpr a_cpr a_wcel i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_sup_set_class f0_intpr a_wceq i1_intpr a_sup_set_class f1_intpr a_wceq a_wo i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_sup_set_class f0_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_sup_set_class f1_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi a_wa p_bitri i1_intpr a_sup_set_class f0_intpr f1_intpr a_cpr a_wcel i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_sup_set_class f0_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_sup_set_class f1_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi a_wa i1_intpr p_albii e0_intpr i1_intpr i0_intpr a_sup_set_class f0_intpr p_clel4 e1_intpr i1_intpr i0_intpr a_sup_set_class f1_intpr p_clel4 i0_intpr a_sup_set_class f0_intpr a_wcel i1_intpr a_sup_set_class f0_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_wal i0_intpr a_sup_set_class f1_intpr a_wcel i1_intpr a_sup_set_class f1_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_wal p_anbi12i i1_intpr a_sup_set_class f0_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_sup_set_class f1_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi a_wa i1_intpr a_wal i1_intpr a_sup_set_class f0_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_wal i1_intpr a_sup_set_class f1_intpr a_wceq i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_wal a_wa i1_intpr a_sup_set_class f0_intpr f1_intpr a_cpr a_wcel i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_wal i0_intpr a_sup_set_class f0_intpr a_wcel i0_intpr a_sup_set_class f1_intpr a_wcel a_wa p_3bitr4i i0_intpr p_vex i1_intpr i0_intpr a_sup_set_class f0_intpr f1_intpr a_cpr p_elint i0_intpr a_sup_set_class f0_intpr f1_intpr p_elin i1_intpr a_sup_set_class f0_intpr f1_intpr a_cpr a_wcel i0_intpr a_sup_set_class i1_intpr a_sup_set_class a_wcel a_wi i1_intpr a_wal i0_intpr a_sup_set_class f0_intpr a_wcel i0_intpr a_sup_set_class f1_intpr a_wcel a_wa i0_intpr a_sup_set_class f0_intpr f1_intpr a_cpr a_cint a_wcel i0_intpr a_sup_set_class f0_intpr f1_intpr a_cin a_wcel p_3bitr4i i0_intpr f0_intpr f1_intpr a_cpr a_cint f0_intpr f1_intpr a_cin p_eqriv $.
$}

$(The intersection of a pair is the intersection of its members.  Closed
       form of ~ intpr .  Theorem 71 of [Suppes] p. 42.  (Contributed by FL,
       27-Apr-2008.) $)

${
	$v A B V W  $.
	$d x y A  $.
	$d y B  $.
	f0_intprg $f class A $.
	f1_intprg $f class B $.
	f2_intprg $f class V $.
	f3_intprg $f class W $.
	i0_intprg $f set x $.
	i1_intprg $f set y $.
	p_intprg $p |- ( ( A e. V /\ B e. W ) -> |^| { A , B } = ( A i^i B ) ) $= i0_intprg a_sup_set_class f0_intprg i1_intprg a_sup_set_class p_preq1 i0_intprg a_sup_set_class f0_intprg a_wceq i0_intprg a_sup_set_class i1_intprg a_sup_set_class a_cpr f0_intprg i1_intprg a_sup_set_class a_cpr p_inteqd i0_intprg a_sup_set_class f0_intprg i1_intprg a_sup_set_class p_ineq1 i0_intprg a_sup_set_class f0_intprg a_wceq i0_intprg a_sup_set_class i1_intprg a_sup_set_class a_cpr a_cint f0_intprg i1_intprg a_sup_set_class a_cpr a_cint i0_intprg a_sup_set_class i1_intprg a_sup_set_class a_cin f0_intprg i1_intprg a_sup_set_class a_cin p_eqeq12d i1_intprg a_sup_set_class f1_intprg f0_intprg p_preq2 i1_intprg a_sup_set_class f1_intprg a_wceq f0_intprg i1_intprg a_sup_set_class a_cpr f0_intprg f1_intprg a_cpr p_inteqd i1_intprg a_sup_set_class f1_intprg f0_intprg p_ineq2 i1_intprg a_sup_set_class f1_intprg a_wceq f0_intprg i1_intprg a_sup_set_class a_cpr a_cint f0_intprg f1_intprg a_cpr a_cint f0_intprg i1_intprg a_sup_set_class a_cin f0_intprg f1_intprg a_cin p_eqeq12d i0_intprg p_vex i1_intprg p_vex i0_intprg a_sup_set_class i1_intprg a_sup_set_class p_intpr i0_intprg a_sup_set_class i1_intprg a_sup_set_class a_cpr a_cint i0_intprg a_sup_set_class i1_intprg a_sup_set_class a_cin a_wceq f0_intprg i1_intprg a_sup_set_class a_cpr a_cint f0_intprg i1_intprg a_sup_set_class a_cin a_wceq f0_intprg f1_intprg a_cpr a_cint f0_intprg f1_intprg a_cin a_wceq i0_intprg i1_intprg f0_intprg f1_intprg f2_intprg f3_intprg p_vtocl2g $.
$}

$(Intersection of a singleton.  (Contributed by Stefan O'Rear,
     22-Feb-2015.) $)

${
	$v A V  $.
	f0_intsng $f class A $.
	f1_intsng $f class V $.
	p_intsng $p |- ( A e. V -> |^| { A } = A ) $= f0_intsng p_dfsn2 f0_intsng a_csn f0_intsng f0_intsng a_cpr p_inteqi f0_intsng f0_intsng f1_intsng f1_intsng p_intprg f0_intsng f1_intsng a_wcel f0_intsng f0_intsng a_cpr a_cint f0_intsng f0_intsng a_cin a_wceq p_anidms f0_intsng p_inidm f0_intsng f1_intsng a_wcel f0_intsng f0_intsng a_cpr a_cint f0_intsng f0_intsng a_cin f0_intsng p_syl6eq f0_intsng f1_intsng a_wcel f0_intsng a_csn a_cint f0_intsng f0_intsng a_cpr a_cint f0_intsng p_syl5eq $.
$}

$(The intersection of a singleton is its member.  Theorem 70 of [Suppes]
       p. 41.  (Contributed by NM, 29-Sep-2002.) $)

${
	$v A  $.
	f0_intsn $f class A $.
	e0_intsn $e |- A e. _V $.
	p_intsn $p |- |^| { A } = A $= e0_intsn f0_intsn a_cvv p_intsng f0_intsn a_cvv a_wcel f0_intsn a_csn a_cint f0_intsn a_wceq a_ax-mp $.
$}

$(Two ways to express " ` A ` is a singleton."  See also ~ en1 , ~ en1b ,
       ~ card1 , and ~ eusn .  (Contributed by NM, 2-Aug-2010.) $)

${
	$v x A  $.
	$d x y A  $.
	$d y  $.
	f0_uniintsn $f set x $.
	f1_uniintsn $f class A $.
	i0_uniintsn $f set y $.
	p_uniintsn $p |- ( U. A = |^| A <-> E. x A = { x } ) $= p_vn0 f1_uniintsn a_c0 p_inteq p_int0 f1_uniintsn a_c0 a_wceq f1_uniintsn a_cint a_c0 a_cint a_cvv p_syl6eq f1_uniintsn a_c0 a_wceq f1_uniintsn a_cint a_cvv a_wceq f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq p_adantl f1_uniintsn a_c0 p_unieq p_uni0 f1_uniintsn a_c0 a_wceq f1_uniintsn a_cuni a_c0 a_cuni a_c0 p_syl6eq f1_uniintsn a_cuni f1_uniintsn a_cint a_c0 p_eqeq1 f1_uniintsn a_c0 a_wceq f1_uniintsn a_cuni a_c0 a_wceq f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f1_uniintsn a_cint a_c0 a_wceq p_syl5ib f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f1_uniintsn a_c0 a_wceq f1_uniintsn a_cint a_c0 a_wceq p_imp f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f1_uniintsn a_c0 a_wceq a_wa f1_uniintsn a_cint a_cvv a_c0 p_eqtr3d f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f1_uniintsn a_c0 a_wceq a_cvv a_c0 a_wceq p_ex f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f1_uniintsn a_c0 a_cvv a_c0 p_necon3d f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq a_cvv a_c0 a_wne f1_uniintsn a_c0 a_wne p_mpi f0_uniintsn f1_uniintsn p_n0 f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f1_uniintsn a_c0 a_wne f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn a_wex p_sylib f0_uniintsn p_vex i0_uniintsn p_vex f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class f1_uniintsn p_prss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn p_uniss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr a_cuni f1_uniintsn a_cuni a_wss f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq p_adantl f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss p_simpl f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr a_cuni f1_uniintsn a_cuni f1_uniintsn a_cint p_sseqtrd f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn p_intss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss f1_uniintsn a_cint f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr a_cint a_wss f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq p_adantl f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr a_cuni f1_uniintsn a_cint f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr a_cint p_sstrd f0_uniintsn p_vex i0_uniintsn p_vex f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class p_unipr f0_uniintsn p_vex i0_uniintsn p_vex f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class p_intpr f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr a_cuni f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr a_cint f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin p_3sstr3g f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class p_inss1 f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class p_ssun1 f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin f0_uniintsn a_sup_set_class f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun p_sstri f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin a_wss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun a_wss p_jctir f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin p_eqss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class p_uneqin f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin a_wss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun a_wss a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_wceq p_bitr3i f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin a_wss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cin f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cun a_wss a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_wceq p_sylib f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_wceq p_ex f0_uniintsn a_sup_set_class f1_uniintsn a_wcel i0_uniintsn a_sup_set_class f1_uniintsn a_wcel a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_cpr f1_uniintsn a_wss f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_wceq p_syl5bi f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class f1_uniintsn a_wcel i0_uniintsn a_sup_set_class f1_uniintsn a_wcel a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_wceq a_wi f0_uniintsn i0_uniintsn p_alrimivv f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn a_wex f0_uniintsn a_sup_set_class f1_uniintsn a_wcel i0_uniintsn a_sup_set_class f1_uniintsn a_wcel a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_wceq a_wi i0_uniintsn a_wal f0_uniintsn a_wal p_jca f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn p_euabsn f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class f1_uniintsn p_eleq1 f0_uniintsn a_sup_set_class f1_uniintsn a_wcel i0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn i0_uniintsn p_eu4 f0_uniintsn f1_uniintsn p_abid2 f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn a_cab f1_uniintsn f0_uniintsn a_sup_set_class a_csn p_eqeq1i f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn a_cab f0_uniintsn a_sup_set_class a_csn a_wceq f1_uniintsn f0_uniintsn a_sup_set_class a_csn a_wceq f0_uniintsn p_exbii f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn a_weu f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn a_cab f0_uniintsn a_sup_set_class a_csn a_wceq f0_uniintsn a_wex f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn a_wex f0_uniintsn a_sup_set_class f1_uniintsn a_wcel i0_uniintsn a_sup_set_class f1_uniintsn a_wcel a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_wceq a_wi i0_uniintsn a_wal f0_uniintsn a_wal a_wa f1_uniintsn f0_uniintsn a_sup_set_class a_csn a_wceq f0_uniintsn a_wex p_3bitr3i f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn a_sup_set_class f1_uniintsn a_wcel f0_uniintsn a_wex f0_uniintsn a_sup_set_class f1_uniintsn a_wcel i0_uniintsn a_sup_set_class f1_uniintsn a_wcel a_wa f0_uniintsn a_sup_set_class i0_uniintsn a_sup_set_class a_wceq a_wi i0_uniintsn a_wal f0_uniintsn a_wal a_wa f1_uniintsn f0_uniintsn a_sup_set_class a_csn a_wceq f0_uniintsn a_wex p_sylib f0_uniintsn p_vex f0_uniintsn a_sup_set_class p_unisn f1_uniintsn f0_uniintsn a_sup_set_class a_csn p_unieq f1_uniintsn f0_uniintsn a_sup_set_class a_csn p_inteq f0_uniintsn p_vex f0_uniintsn a_sup_set_class p_intsn f1_uniintsn f0_uniintsn a_sup_set_class a_csn a_wceq f1_uniintsn a_cint f0_uniintsn a_sup_set_class a_csn a_cint f0_uniintsn a_sup_set_class p_syl6eq f1_uniintsn f0_uniintsn a_sup_set_class a_csn a_wceq f0_uniintsn a_sup_set_class a_csn a_cuni f0_uniintsn a_sup_set_class f1_uniintsn a_cuni f1_uniintsn a_cint p_3eqtr4a f1_uniintsn f0_uniintsn a_sup_set_class a_csn a_wceq f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f0_uniintsn p_exlimiv f1_uniintsn a_cuni f1_uniintsn a_cint a_wceq f1_uniintsn f0_uniintsn a_sup_set_class a_csn a_wceq f0_uniintsn a_wex p_impbii $.
$}

$(The union and the intersection of a class abstraction are equal exactly
       when there is a unique satisfying value of ` ph ( x ) ` .  (Contributed
       by Mario Carneiro, 24-Dec-2016.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_uniintab $f wff ph $.
	f1_uniintab $f set x $.
	i0_uniintab $f set y $.
	p_uniintab $p |- ( E! x ph <-> U. { x | ph } = |^| { x | ph } ) $= f0_uniintab f1_uniintab i0_uniintab p_euabsn2 i0_uniintab f0_uniintab f1_uniintab a_cab p_uniintsn f0_uniintab f1_uniintab a_weu f0_uniintab f1_uniintab a_cab i0_uniintab a_sup_set_class a_csn a_wceq i0_uniintab a_wex f0_uniintab f1_uniintab a_cab a_cuni f0_uniintab f1_uniintab a_cab a_cint a_wceq p_bitr4i $.
$}

$(Theorem joining a singleton to an intersection.  (Contributed by NM,
       29-Sep-2002.) $)

${
	$v A B  $.
	f0_intunsn $f class A $.
	f1_intunsn $f class B $.
	e0_intunsn $e |- B e. _V $.
	p_intunsn $p |- |^| ( A u. { B } ) = ( |^| A i^i B ) $= f0_intunsn f1_intunsn a_csn p_intun e0_intunsn f1_intunsn p_intsn f1_intunsn a_csn a_cint f1_intunsn f0_intunsn a_cint p_ineq2i f0_intunsn f1_intunsn a_csn a_cun a_cint f0_intunsn a_cint f1_intunsn a_csn a_cint a_cin f0_intunsn a_cint f1_intunsn a_cin p_eqtri $.
$}

$(Relative intersection of an empty set.  (Contributed by Stefan O'Rear,
     3-Apr-2015.) $)

${
	$v A X  $.
	f0_rint0 $f class A $.
	f1_rint0 $f class X $.
	p_rint0 $p |- ( X = (/) -> ( A i^i |^| X ) = A ) $= f1_rint0 a_c0 p_inteq f1_rint0 a_c0 a_wceq f1_rint0 a_cint a_c0 a_cint f0_rint0 p_ineq2d p_int0 a_c0 a_cint a_cvv f0_rint0 p_ineq2i f0_rint0 p_inv1 f0_rint0 a_c0 a_cint a_cin f0_rint0 a_cvv a_cin f0_rint0 p_eqtri f1_rint0 a_c0 a_wceq f0_rint0 f1_rint0 a_cint a_cin f0_rint0 a_c0 a_cint a_cin f0_rint0 p_syl6eq $.
$}

$(Membership in a restricted intersection.  (Contributed by Stefan O'Rear,
       3-Apr-2015.) $)

${
	$v y A B X  $.
	$d B y  $.
	$d X y  $.
	f0_elrint $f set y $.
	f1_elrint $f class A $.
	f2_elrint $f class B $.
	f3_elrint $f class X $.
	p_elrint $p |- ( X e. ( A i^i |^| B ) <-> ( X e. A /\ A. y e. B X e. y ) ) $= f3_elrint f1_elrint f2_elrint a_cint p_elin f0_elrint f3_elrint f2_elrint f1_elrint p_elintg f3_elrint f1_elrint a_wcel f3_elrint f2_elrint a_cint a_wcel f3_elrint f0_elrint a_sup_set_class a_wcel f0_elrint f2_elrint a_wral p_pm5.32i f3_elrint f1_elrint f2_elrint a_cint a_cin a_wcel f3_elrint f1_elrint a_wcel f3_elrint f2_elrint a_cint a_wcel a_wa f3_elrint f1_elrint a_wcel f3_elrint f0_elrint a_sup_set_class a_wcel f0_elrint f2_elrint a_wral a_wa p_bitri $.
$}

$(Membership in a restricted intersection.  (Contributed by Stefan O'Rear,
       3-Apr-2015.) $)

${
	$v y A B X  $.
	$d B y  $.
	$d X y  $.
	f0_elrint2 $f set y $.
	f1_elrint2 $f class A $.
	f2_elrint2 $f class B $.
	f3_elrint2 $f class X $.
	p_elrint2 $p |- ( X e. A -> ( X e. ( A i^i |^| B ) <-> A. y e. B X e. y ) ) $= f0_elrint2 f1_elrint2 f2_elrint2 f3_elrint2 p_elrint f3_elrint2 f1_elrint2 f2_elrint2 a_cint a_cin a_wcel f3_elrint2 f1_elrint2 a_wcel f3_elrint2 f0_elrint2 a_sup_set_class a_wcel f0_elrint2 f2_elrint2 a_wral p_baib $.
$}


