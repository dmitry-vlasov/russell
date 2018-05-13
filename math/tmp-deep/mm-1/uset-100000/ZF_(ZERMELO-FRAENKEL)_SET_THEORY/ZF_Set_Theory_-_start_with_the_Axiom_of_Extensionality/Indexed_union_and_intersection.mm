$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_intersection_of_a_class.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Indexed union and intersection

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c U_ $.

$(Underlined big cup. $)

$c |^|_ $.

$(Underlined big cap. $)

$(Extend class notation to include indexed union.  Note:  Historically
     (prior to 21-Oct-2005), set.mm used the notation ` U. x e. A B ` , with
     the same union symbol as ~ cuni .  While that syntax was unambiguous, it
     did not allow for LALR parsing of the syntax constructions in set.mm.  The
     new syntax uses as distinguished symbol ` U_ ` instead of ` U. ` and does
     allow LALR parsing.  Thanks to Peter Backes for suggesting this change. $)

${
	$v x A B  $.
	f0_ciun $f set x $.
	f1_ciun $f class A $.
	f2_ciun $f class B $.
	a_ciun $a class U_ x e. A B $.
$}

$(Extend class notation to include indexed intersection.  Note:
     Historically (prior to 21-Oct-2005), set.mm used the notation
     ` |^| x e. A B ` , with the same intersection symbol as ~ cint .  Although
     that syntax was unambiguous, it did not allow for LALR parsing of the
     syntax constructions in set.mm.  The new syntax uses a distinguished
     symbol ` |^|_ ` instead of ` |^| ` and does allow LALR parsing.  Thanks to
     Peter Backes for suggesting this change. $)

${
	$v x A B  $.
	f0_ciin $f set x $.
	f1_ciin $f class A $.
	f2_ciin $f class B $.
	a_ciin $a class |^|_ x e. A B $.
$}

$(Define indexed union.  Definition indexed union in [Stoll] p. 45.  In
       most applications, ` A ` is independent of ` x ` (although this is not
       required by the definition), and ` B ` depends on ` x ` i.e. can be read
       informally as ` B ( x ) ` .  We call ` x ` the index, ` A ` the index
       set, and ` B ` the indexed set.  In most books, ` x e. A ` is written as
       a subscript or underneath a union symbol ` U. ` .  We use a special
       union symbol ` U_ ` to make it easier to distinguish from plain class
       union.  In many theorems, you will see that ` x ` and ` A ` are in the
       same distinct variable group (meaning ` A ` cannot depend on ` x ` ) and
       that ` B ` and ` x ` do not share a distinct variable group (meaning
       that can be thought of as ` B ( x ) ` i.e. can be substituted with a
       class expression containing ` x ` ).  An alternate definition tying
       indexed union to ordinary union is ~ dfiun2 .  Theorem ~ uniiun provides
       a definition of ordinary union in terms of indexed union.  Theorems
       ~ fniunfv and ~ funiunfv are useful when ` B ` is a function.
       (Contributed by NM, 27-Jun-1998.) $)

${
	$v x y A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_df-iun $f set x $.
	f1_df-iun $f set y $.
	f2_df-iun $f class A $.
	f3_df-iun $f class B $.
	a_df-iun $a |- U_ x e. A B = { y | E. x e. A y e. B } $.
$}

$(Define indexed intersection.  Definition of [Stoll] p. 45.  See the
       remarks for its sibling operation of indexed union ~ df-iun .  An
       alternate definition tying indexed intersection to ordinary intersection
       is ~ dfiin2 .  Theorem ~ intiin provides a definition of ordinary
       intersection in terms of indexed intersection.  (Contributed by NM,
       27-Jun-1998.) $)

${
	$v x y A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_df-iin $f set x $.
	f1_df-iin $f set y $.
	f2_df-iin $f class A $.
	f3_df-iin $f class B $.
	a_df-iin $a |- |^|_ x e. A B = { y | A. x e. A y e. B } $.
$}

$(Membership in indexed union.  (Contributed by NM, 3-Sep-2003.) $)

${
	$v x A B C  $.
	$d x y A  $.
	$d y B  $.
	$d y C  $.
	f0_eliun $f set x $.
	f1_eliun $f class A $.
	f2_eliun $f class B $.
	f3_eliun $f class C $.
	i0_eliun $f set y $.
	p_eliun $p |- ( A e. U_ x e. B C <-> E. x e. B A e. C ) $= f1_eliun f0_eliun f2_eliun f3_eliun a_ciun p_elex f1_eliun f3_eliun p_elex f1_eliun f3_eliun a_wcel f1_eliun a_cvv a_wcel f0_eliun f2_eliun p_rexlimivw i0_eliun a_sup_set_class f1_eliun f3_eliun p_eleq1 i0_eliun a_sup_set_class f1_eliun a_wceq i0_eliun a_sup_set_class f3_eliun a_wcel f1_eliun f3_eliun a_wcel f0_eliun f2_eliun p_rexbidv f0_eliun i0_eliun f2_eliun f3_eliun a_df-iun i0_eliun a_sup_set_class f3_eliun a_wcel f0_eliun f2_eliun a_wrex f1_eliun f3_eliun a_wcel f0_eliun f2_eliun a_wrex i0_eliun f1_eliun f0_eliun f2_eliun f3_eliun a_ciun a_cvv p_elab2g f1_eliun f0_eliun f2_eliun f3_eliun a_ciun a_wcel f1_eliun a_cvv a_wcel f1_eliun f3_eliun a_wcel f0_eliun f2_eliun a_wrex p_pm5.21nii $.
$}

$(Membership in indexed intersection.  (Contributed by NM, 3-Sep-2003.) $)

${
	$v x A B C V  $.
	$d x y A  $.
	$d y B  $.
	$d y C  $.
	f0_eliin $f set x $.
	f1_eliin $f class A $.
	f2_eliin $f class B $.
	f3_eliin $f class C $.
	f4_eliin $f class V $.
	i0_eliin $f set y $.
	p_eliin $p |- ( A e. V -> ( A e. |^|_ x e. B C <-> A. x e. B A e. C ) ) $= i0_eliin a_sup_set_class f1_eliin f3_eliin p_eleq1 i0_eliin a_sup_set_class f1_eliin a_wceq i0_eliin a_sup_set_class f3_eliin a_wcel f1_eliin f3_eliin a_wcel f0_eliin f2_eliin p_ralbidv f0_eliin i0_eliin f2_eliin f3_eliin a_df-iin i0_eliin a_sup_set_class f3_eliin a_wcel f0_eliin f2_eliin a_wral f1_eliin f3_eliin a_wcel f0_eliin f2_eliin a_wral i0_eliin f1_eliin f0_eliin f2_eliin f3_eliin a_ciin f4_eliin p_elab2g $.
$}

$(Commutation of indexed unions.  (Contributed by NM, 18-Dec-2008.) $)

${
	$v x y A B C  $.
	$d y z A  $.
	$d x z B  $.
	$d z C  $.
	$d x y  $.
	f0_iuncom $f set x $.
	f1_iuncom $f set y $.
	f2_iuncom $f class A $.
	f3_iuncom $f class B $.
	f4_iuncom $f class C $.
	i0_iuncom $f set z $.
	p_iuncom $p |- U_ x e. A U_ y e. B C = U_ y e. B U_ x e. A C $= i0_iuncom a_sup_set_class f4_iuncom a_wcel f0_iuncom f1_iuncom f2_iuncom f3_iuncom p_rexcom f1_iuncom i0_iuncom a_sup_set_class f3_iuncom f4_iuncom p_eliun i0_iuncom a_sup_set_class f1_iuncom f3_iuncom f4_iuncom a_ciun a_wcel i0_iuncom a_sup_set_class f4_iuncom a_wcel f1_iuncom f3_iuncom a_wrex f0_iuncom f2_iuncom p_rexbii f0_iuncom i0_iuncom a_sup_set_class f2_iuncom f4_iuncom p_eliun i0_iuncom a_sup_set_class f0_iuncom f2_iuncom f4_iuncom a_ciun a_wcel i0_iuncom a_sup_set_class f4_iuncom a_wcel f0_iuncom f2_iuncom a_wrex f1_iuncom f3_iuncom p_rexbii i0_iuncom a_sup_set_class f4_iuncom a_wcel f1_iuncom f3_iuncom a_wrex f0_iuncom f2_iuncom a_wrex i0_iuncom a_sup_set_class f4_iuncom a_wcel f0_iuncom f2_iuncom a_wrex f1_iuncom f3_iuncom a_wrex i0_iuncom a_sup_set_class f1_iuncom f3_iuncom f4_iuncom a_ciun a_wcel f0_iuncom f2_iuncom a_wrex i0_iuncom a_sup_set_class f0_iuncom f2_iuncom f4_iuncom a_ciun a_wcel f1_iuncom f3_iuncom a_wrex p_3bitr4i f0_iuncom i0_iuncom a_sup_set_class f2_iuncom f1_iuncom f3_iuncom f4_iuncom a_ciun p_eliun f1_iuncom i0_iuncom a_sup_set_class f3_iuncom f0_iuncom f2_iuncom f4_iuncom a_ciun p_eliun i0_iuncom a_sup_set_class f1_iuncom f3_iuncom f4_iuncom a_ciun a_wcel f0_iuncom f2_iuncom a_wrex i0_iuncom a_sup_set_class f0_iuncom f2_iuncom f4_iuncom a_ciun a_wcel f1_iuncom f3_iuncom a_wrex i0_iuncom a_sup_set_class f0_iuncom f2_iuncom f1_iuncom f3_iuncom f4_iuncom a_ciun a_ciun a_wcel i0_iuncom a_sup_set_class f1_iuncom f3_iuncom f0_iuncom f2_iuncom f4_iuncom a_ciun a_ciun a_wcel p_3bitr4i i0_iuncom f0_iuncom f2_iuncom f1_iuncom f3_iuncom f4_iuncom a_ciun a_ciun f1_iuncom f3_iuncom f0_iuncom f2_iuncom f4_iuncom a_ciun a_ciun p_eqriv $.
$}

$(Commutation of union with indexed union.  (Contributed by Mario
       Carneiro, 18-Jan-2014.) $)

${
	$v x A B  $.
	$d y z A  $.
	$d y z B  $.
	$d x y z  $.
	f0_iuncom4 $f set x $.
	f1_iuncom4 $f class A $.
	f2_iuncom4 $f class B $.
	i0_iuncom4 $f set y $.
	i1_iuncom4 $f set z $.
	p_iuncom4 $p |- U_ x e. A U. B = U. U_ x e. A B $= i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f2_iuncom4 a_df-rex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f2_iuncom4 a_wrex i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 a_wex f0_iuncom4 f1_iuncom4 p_rexbii i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa f0_iuncom4 i1_iuncom4 f1_iuncom4 p_rexcom4 i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f2_iuncom4 a_wrex f0_iuncom4 f1_iuncom4 a_wrex i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 a_wex f0_iuncom4 f1_iuncom4 a_wrex i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa f0_iuncom4 f1_iuncom4 a_wrex i1_iuncom4 a_wex p_bitri i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel f0_iuncom4 f1_iuncom4 p_r19.41v i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa f0_iuncom4 f1_iuncom4 a_wrex i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel f0_iuncom4 f1_iuncom4 a_wrex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 p_exbii i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f2_iuncom4 a_wrex f0_iuncom4 f1_iuncom4 a_wrex i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa f0_iuncom4 f1_iuncom4 a_wrex i1_iuncom4 a_wex i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel f0_iuncom4 f1_iuncom4 a_wrex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 a_wex p_bitri i1_iuncom4 i0_iuncom4 a_sup_set_class f2_iuncom4 p_eluni2 i0_iuncom4 a_sup_set_class f2_iuncom4 a_cuni a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f2_iuncom4 a_wrex f0_iuncom4 f1_iuncom4 p_rexbii i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_df-rex f0_iuncom4 i1_iuncom4 a_sup_set_class f1_iuncom4 f2_iuncom4 p_eliun i1_iuncom4 a_sup_set_class f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_wcel i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel f0_iuncom4 f1_iuncom4 a_wrex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel p_anbi1i i1_iuncom4 a_sup_set_class f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel f0_iuncom4 f1_iuncom4 a_wrex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 p_exbii i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_wrex i1_iuncom4 a_sup_set_class f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_wcel i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 a_wex i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel f0_iuncom4 f1_iuncom4 a_wrex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 a_wex p_bitri i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f2_iuncom4 a_wrex f0_iuncom4 f1_iuncom4 a_wrex i1_iuncom4 a_sup_set_class f2_iuncom4 a_wcel f0_iuncom4 f1_iuncom4 a_wrex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel a_wa i1_iuncom4 a_wex i0_iuncom4 a_sup_set_class f2_iuncom4 a_cuni a_wcel f0_iuncom4 f1_iuncom4 a_wrex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_wrex p_3bitr4i f0_iuncom4 i0_iuncom4 a_sup_set_class f1_iuncom4 f2_iuncom4 a_cuni p_eliun i1_iuncom4 i0_iuncom4 a_sup_set_class f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun p_eluni2 i0_iuncom4 a_sup_set_class f2_iuncom4 a_cuni a_wcel f0_iuncom4 f1_iuncom4 a_wrex i0_iuncom4 a_sup_set_class i1_iuncom4 a_sup_set_class a_wcel i1_iuncom4 f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_wrex i0_iuncom4 a_sup_set_class f0_iuncom4 f1_iuncom4 f2_iuncom4 a_cuni a_ciun a_wcel i0_iuncom4 a_sup_set_class f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_cuni a_wcel p_3bitr4i i0_iuncom4 f0_iuncom4 f1_iuncom4 f2_iuncom4 a_cuni a_ciun f0_iuncom4 f1_iuncom4 f2_iuncom4 a_ciun a_cuni p_eqriv $.
$}

$(Indexed union of a constant class, i.e. where ` B ` does not depend on
       ` x ` .  (Contributed by NM, 5-Sep-2004.)  (Proof shortened by Andrew
       Salmon, 25-Jul-2011.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_iunconst $f set x $.
	f1_iunconst $f class A $.
	f2_iunconst $f class B $.
	i0_iunconst $f set y $.
	p_iunconst $p |- ( A =/= (/) -> U_ x e. A B = B ) $= i0_iunconst a_sup_set_class f2_iunconst a_wcel f0_iunconst f1_iunconst p_r19.9rzv f0_iunconst i0_iunconst a_sup_set_class f1_iunconst f2_iunconst p_eliun f1_iunconst a_c0 a_wne i0_iunconst a_sup_set_class f2_iunconst a_wcel i0_iunconst a_sup_set_class f2_iunconst a_wcel f0_iunconst f1_iunconst a_wrex i0_iunconst a_sup_set_class f0_iunconst f1_iunconst f2_iunconst a_ciun a_wcel p_syl6rbbr f1_iunconst a_c0 a_wne i0_iunconst f0_iunconst f1_iunconst f2_iunconst a_ciun f2_iunconst p_eqrdv $.
$}

$(Indexed intersection of a constant class, i.e. where ` B ` does not
       depend on ` x ` .  (Contributed by Mario Carneiro, 6-Feb-2015.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_iinconst $f set x $.
	f1_iinconst $f class A $.
	f2_iinconst $f class B $.
	i0_iinconst $f set y $.
	p_iinconst $p |- ( A =/= (/) -> |^|_ x e. A B = B ) $= i0_iinconst a_sup_set_class f2_iinconst a_wcel f0_iinconst f1_iinconst p_r19.3rzv i0_iinconst p_vex f0_iinconst i0_iinconst a_sup_set_class f1_iinconst f2_iinconst a_cvv p_eliin i0_iinconst a_sup_set_class a_cvv a_wcel i0_iinconst a_sup_set_class f0_iinconst f1_iinconst f2_iinconst a_ciin a_wcel i0_iinconst a_sup_set_class f2_iinconst a_wcel f0_iinconst f1_iinconst a_wral a_wb a_ax-mp f1_iinconst a_c0 a_wne i0_iinconst a_sup_set_class f2_iinconst a_wcel i0_iinconst a_sup_set_class f2_iinconst a_wcel f0_iinconst f1_iinconst a_wral i0_iinconst a_sup_set_class f0_iinconst f1_iinconst f2_iinconst a_ciin a_wcel p_syl6rbbr f1_iinconst a_c0 a_wne i0_iinconst f0_iinconst f1_iinconst f2_iinconst a_ciin f2_iinconst p_eqrdv $.
$}

$(Law combining indexed union with indexed intersection.  Eq. 14 in
       [KuratowskiMostowski] p. 109.  This theorem also appears as the last
       example at ~ http://en.wikipedia.org/wiki/Union%5F%28set%5Ftheory%29 .
       (Contributed by NM, 17-Aug-2004.)  (Proof shortened by Andrew Salmon,
       25-Jul-2011.) $)

${
	$v x y A B C  $.
	$d x y  $.
	$d y z A  $.
	$d x z B  $.
	$d z C  $.
	f0_iuniin $f set x $.
	f1_iuniin $f set y $.
	f2_iuniin $f class A $.
	f3_iuniin $f class B $.
	f4_iuniin $f class C $.
	i0_iuniin $f set z $.
	p_iuniin $p |- U_ x e. A |^|_ y e. B C C_ |^|_ y e. B U_ x e. A C $= i0_iuniin a_sup_set_class f4_iuniin a_wcel f0_iuniin f1_iuniin f2_iuniin f3_iuniin p_r19.12 i0_iuniin p_vex f1_iuniin i0_iuniin a_sup_set_class f3_iuniin f4_iuniin a_cvv p_eliin i0_iuniin a_sup_set_class a_cvv a_wcel i0_iuniin a_sup_set_class f1_iuniin f3_iuniin f4_iuniin a_ciin a_wcel i0_iuniin a_sup_set_class f4_iuniin a_wcel f1_iuniin f3_iuniin a_wral a_wb a_ax-mp i0_iuniin a_sup_set_class f1_iuniin f3_iuniin f4_iuniin a_ciin a_wcel i0_iuniin a_sup_set_class f4_iuniin a_wcel f1_iuniin f3_iuniin a_wral f0_iuniin f2_iuniin p_rexbii f0_iuniin i0_iuniin a_sup_set_class f2_iuniin f4_iuniin p_eliun i0_iuniin a_sup_set_class f0_iuniin f2_iuniin f4_iuniin a_ciun a_wcel i0_iuniin a_sup_set_class f4_iuniin a_wcel f0_iuniin f2_iuniin a_wrex f1_iuniin f3_iuniin p_ralbii i0_iuniin a_sup_set_class f4_iuniin a_wcel f1_iuniin f3_iuniin a_wral f0_iuniin f2_iuniin a_wrex i0_iuniin a_sup_set_class f4_iuniin a_wcel f0_iuniin f2_iuniin a_wrex f1_iuniin f3_iuniin a_wral i0_iuniin a_sup_set_class f1_iuniin f3_iuniin f4_iuniin a_ciin a_wcel f0_iuniin f2_iuniin a_wrex i0_iuniin a_sup_set_class f0_iuniin f2_iuniin f4_iuniin a_ciun a_wcel f1_iuniin f3_iuniin a_wral p_3imtr4i f0_iuniin i0_iuniin a_sup_set_class f2_iuniin f1_iuniin f3_iuniin f4_iuniin a_ciin p_eliun i0_iuniin p_vex f1_iuniin i0_iuniin a_sup_set_class f3_iuniin f0_iuniin f2_iuniin f4_iuniin a_ciun a_cvv p_eliin i0_iuniin a_sup_set_class a_cvv a_wcel i0_iuniin a_sup_set_class f1_iuniin f3_iuniin f0_iuniin f2_iuniin f4_iuniin a_ciun a_ciin a_wcel i0_iuniin a_sup_set_class f0_iuniin f2_iuniin f4_iuniin a_ciun a_wcel f1_iuniin f3_iuniin a_wral a_wb a_ax-mp i0_iuniin a_sup_set_class f1_iuniin f3_iuniin f4_iuniin a_ciin a_wcel f0_iuniin f2_iuniin a_wrex i0_iuniin a_sup_set_class f0_iuniin f2_iuniin f4_iuniin a_ciun a_wcel f1_iuniin f3_iuniin a_wral i0_iuniin a_sup_set_class f0_iuniin f2_iuniin f1_iuniin f3_iuniin f4_iuniin a_ciin a_ciun a_wcel i0_iuniin a_sup_set_class f1_iuniin f3_iuniin f0_iuniin f2_iuniin f4_iuniin a_ciun a_ciin a_wcel p_3imtr4i i0_iuniin f0_iuniin f2_iuniin f1_iuniin f3_iuniin f4_iuniin a_ciin a_ciun f1_iuniin f3_iuniin f0_iuniin f2_iuniin f4_iuniin a_ciun a_ciin p_ssriv $.
$}

$(Subclass theorem for indexed union.  (Contributed by NM, 10-Dec-2004.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B C  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	f0_iunss1 $f set x $.
	f1_iunss1 $f class A $.
	f2_iunss1 $f class B $.
	f3_iunss1 $f class C $.
	i0_iunss1 $f set y $.
	p_iunss1 $p |- ( A C_ B -> U_ x e. A C C_ U_ x e. B C ) $= i0_iunss1 a_sup_set_class f3_iunss1 a_wcel f0_iunss1 f1_iunss1 f2_iunss1 p_ssrexv f0_iunss1 i0_iunss1 a_sup_set_class f1_iunss1 f3_iunss1 p_eliun f0_iunss1 i0_iunss1 a_sup_set_class f2_iunss1 f3_iunss1 p_eliun f1_iunss1 f2_iunss1 a_wss i0_iunss1 a_sup_set_class f3_iunss1 a_wcel f0_iunss1 f1_iunss1 a_wrex i0_iunss1 a_sup_set_class f3_iunss1 a_wcel f0_iunss1 f2_iunss1 a_wrex i0_iunss1 a_sup_set_class f0_iunss1 f1_iunss1 f3_iunss1 a_ciun a_wcel i0_iunss1 a_sup_set_class f0_iunss1 f2_iunss1 f3_iunss1 a_ciun a_wcel p_3imtr4g f1_iunss1 f2_iunss1 a_wss i0_iunss1 f0_iunss1 f1_iunss1 f3_iunss1 a_ciun f0_iunss1 f2_iunss1 f3_iunss1 a_ciun p_ssrdv $.
$}

$(Subclass theorem for indexed union.  (Contributed by NM,
       24-Jan-2012.) $)

${
	$v x A B C  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	f0_iinss1 $f set x $.
	f1_iinss1 $f class A $.
	f2_iinss1 $f class B $.
	f3_iinss1 $f class C $.
	i0_iinss1 $f set y $.
	p_iinss1 $p |- ( A C_ B -> |^|_ x e. B C C_ |^|_ x e. A C ) $= i0_iinss1 a_sup_set_class f3_iinss1 a_wcel f0_iinss1 f1_iinss1 f2_iinss1 p_ssralv i0_iinss1 p_vex f0_iinss1 i0_iinss1 a_sup_set_class f2_iinss1 f3_iinss1 a_cvv p_eliin i0_iinss1 a_sup_set_class a_cvv a_wcel i0_iinss1 a_sup_set_class f0_iinss1 f2_iinss1 f3_iinss1 a_ciin a_wcel i0_iinss1 a_sup_set_class f3_iinss1 a_wcel f0_iinss1 f2_iinss1 a_wral a_wb a_ax-mp i0_iinss1 p_vex f0_iinss1 i0_iinss1 a_sup_set_class f1_iinss1 f3_iinss1 a_cvv p_eliin i0_iinss1 a_sup_set_class a_cvv a_wcel i0_iinss1 a_sup_set_class f0_iinss1 f1_iinss1 f3_iinss1 a_ciin a_wcel i0_iinss1 a_sup_set_class f3_iinss1 a_wcel f0_iinss1 f1_iinss1 a_wral a_wb a_ax-mp f1_iinss1 f2_iinss1 a_wss i0_iinss1 a_sup_set_class f3_iinss1 a_wcel f0_iinss1 f2_iinss1 a_wral i0_iinss1 a_sup_set_class f3_iinss1 a_wcel f0_iinss1 f1_iinss1 a_wral i0_iinss1 a_sup_set_class f0_iinss1 f2_iinss1 f3_iinss1 a_ciin a_wcel i0_iinss1 a_sup_set_class f0_iinss1 f1_iinss1 f3_iinss1 a_ciin a_wcel p_3imtr4g f1_iinss1 f2_iinss1 a_wss i0_iinss1 f0_iinss1 f2_iinss1 f3_iinss1 a_ciin f0_iinss1 f1_iinss1 f3_iinss1 a_ciin p_ssrdv $.
$}

$(Equality theorem for indexed union.  (Contributed by NM,
       27-Jun-1998.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d x B  $.
	$d C  $.
	f0_iuneq1 $f set x $.
	f1_iuneq1 $f class A $.
	f2_iuneq1 $f class B $.
	f3_iuneq1 $f class C $.
	p_iuneq1 $p |- ( A = B -> U_ x e. A C = U_ x e. B C ) $= f0_iuneq1 f1_iuneq1 f2_iuneq1 f3_iuneq1 p_iunss1 f0_iuneq1 f2_iuneq1 f1_iuneq1 f3_iuneq1 p_iunss1 f1_iuneq1 f2_iuneq1 a_wss f0_iuneq1 f1_iuneq1 f3_iuneq1 a_ciun f0_iuneq1 f2_iuneq1 f3_iuneq1 a_ciun a_wss f2_iuneq1 f1_iuneq1 a_wss f0_iuneq1 f2_iuneq1 f3_iuneq1 a_ciun f0_iuneq1 f1_iuneq1 f3_iuneq1 a_ciun a_wss p_anim12i f1_iuneq1 f2_iuneq1 p_eqss f0_iuneq1 f1_iuneq1 f3_iuneq1 a_ciun f0_iuneq1 f2_iuneq1 f3_iuneq1 a_ciun p_eqss f1_iuneq1 f2_iuneq1 a_wss f2_iuneq1 f1_iuneq1 a_wss a_wa f0_iuneq1 f1_iuneq1 f3_iuneq1 a_ciun f0_iuneq1 f2_iuneq1 f3_iuneq1 a_ciun a_wss f0_iuneq1 f2_iuneq1 f3_iuneq1 a_ciun f0_iuneq1 f1_iuneq1 f3_iuneq1 a_ciun a_wss a_wa f1_iuneq1 f2_iuneq1 a_wceq f0_iuneq1 f1_iuneq1 f3_iuneq1 a_ciun f0_iuneq1 f2_iuneq1 f3_iuneq1 a_ciun a_wceq p_3imtr4i $.
$}

$(Equality theorem for restricted existential quantifier.  (Contributed by
       NM, 27-Jun-1998.) $)

${
	$v x A B C  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	f0_iineq1 $f set x $.
	f1_iineq1 $f class A $.
	f2_iineq1 $f class B $.
	f3_iineq1 $f class C $.
	i0_iineq1 $f set y $.
	p_iineq1 $p |- ( A = B -> |^|_ x e. A C = |^|_ x e. B C ) $= i0_iineq1 a_sup_set_class f3_iineq1 a_wcel f0_iineq1 f1_iineq1 f2_iineq1 p_raleq f1_iineq1 f2_iineq1 a_wceq i0_iineq1 a_sup_set_class f3_iineq1 a_wcel f0_iineq1 f1_iineq1 a_wral i0_iineq1 a_sup_set_class f3_iineq1 a_wcel f0_iineq1 f2_iineq1 a_wral i0_iineq1 p_abbidv f0_iineq1 i0_iineq1 f1_iineq1 f3_iineq1 a_df-iin f0_iineq1 i0_iineq1 f2_iineq1 f3_iineq1 a_df-iin f1_iineq1 f2_iineq1 a_wceq i0_iineq1 a_sup_set_class f3_iineq1 a_wcel f0_iineq1 f1_iineq1 a_wral i0_iineq1 a_cab i0_iineq1 a_sup_set_class f3_iineq1 a_wcel f0_iineq1 f2_iineq1 a_wral i0_iineq1 a_cab f0_iineq1 f1_iineq1 f3_iineq1 a_ciin f0_iineq1 f2_iineq1 f3_iineq1 a_ciin p_3eqtr4g $.
$}

$(Subclass theorem for indexed union.  (Contributed by NM, 26-Nov-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B C  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	f0_ss2iun $f set x $.
	f1_ss2iun $f class A $.
	f2_ss2iun $f class B $.
	f3_ss2iun $f class C $.
	i0_ss2iun $f set y $.
	p_ss2iun $p |- ( A. x e. A B C_ C -> U_ x e. A B C_ U_ x e. A C ) $= f2_ss2iun f3_ss2iun i0_ss2iun a_sup_set_class p_ssel f2_ss2iun f3_ss2iun a_wss i0_ss2iun a_sup_set_class f2_ss2iun a_wcel i0_ss2iun a_sup_set_class f3_ss2iun a_wcel a_wi f0_ss2iun f1_ss2iun p_ralimi i0_ss2iun a_sup_set_class f2_ss2iun a_wcel i0_ss2iun a_sup_set_class f3_ss2iun a_wcel f0_ss2iun f1_ss2iun p_rexim f2_ss2iun f3_ss2iun a_wss f0_ss2iun f1_ss2iun a_wral i0_ss2iun a_sup_set_class f2_ss2iun a_wcel i0_ss2iun a_sup_set_class f3_ss2iun a_wcel a_wi f0_ss2iun f1_ss2iun a_wral i0_ss2iun a_sup_set_class f2_ss2iun a_wcel f0_ss2iun f1_ss2iun a_wrex i0_ss2iun a_sup_set_class f3_ss2iun a_wcel f0_ss2iun f1_ss2iun a_wrex a_wi p_syl f0_ss2iun i0_ss2iun a_sup_set_class f1_ss2iun f2_ss2iun p_eliun f0_ss2iun i0_ss2iun a_sup_set_class f1_ss2iun f3_ss2iun p_eliun f2_ss2iun f3_ss2iun a_wss f0_ss2iun f1_ss2iun a_wral i0_ss2iun a_sup_set_class f2_ss2iun a_wcel f0_ss2iun f1_ss2iun a_wrex i0_ss2iun a_sup_set_class f3_ss2iun a_wcel f0_ss2iun f1_ss2iun a_wrex i0_ss2iun a_sup_set_class f0_ss2iun f1_ss2iun f2_ss2iun a_ciun a_wcel i0_ss2iun a_sup_set_class f0_ss2iun f1_ss2iun f3_ss2iun a_ciun a_wcel p_3imtr4g f2_ss2iun f3_ss2iun a_wss f0_ss2iun f1_ss2iun a_wral i0_ss2iun f0_ss2iun f1_ss2iun f2_ss2iun a_ciun f0_ss2iun f1_ss2iun f3_ss2iun a_ciun p_ssrdv $.
$}

$(Equality theorem for indexed union.  (Contributed by NM,
       22-Oct-2003.) $)

${
	$v x A B C  $.
	$d x  $.
	$d A  $.
	$d B  $.
	$d C  $.
	f0_iuneq2 $f set x $.
	f1_iuneq2 $f class A $.
	f2_iuneq2 $f class B $.
	f3_iuneq2 $f class C $.
	p_iuneq2 $p |- ( A. x e. A B = C -> U_ x e. A B = U_ x e. A C ) $= f0_iuneq2 f1_iuneq2 f2_iuneq2 f3_iuneq2 p_ss2iun f0_iuneq2 f1_iuneq2 f3_iuneq2 f2_iuneq2 p_ss2iun f2_iuneq2 f3_iuneq2 a_wss f0_iuneq2 f1_iuneq2 a_wral f0_iuneq2 f1_iuneq2 f2_iuneq2 a_ciun f0_iuneq2 f1_iuneq2 f3_iuneq2 a_ciun a_wss f3_iuneq2 f2_iuneq2 a_wss f0_iuneq2 f1_iuneq2 a_wral f0_iuneq2 f1_iuneq2 f3_iuneq2 a_ciun f0_iuneq2 f1_iuneq2 f2_iuneq2 a_ciun a_wss p_anim12i f2_iuneq2 f3_iuneq2 p_eqss f2_iuneq2 f3_iuneq2 a_wceq f2_iuneq2 f3_iuneq2 a_wss f3_iuneq2 f2_iuneq2 a_wss a_wa f0_iuneq2 f1_iuneq2 p_ralbii f2_iuneq2 f3_iuneq2 a_wss f3_iuneq2 f2_iuneq2 a_wss f0_iuneq2 f1_iuneq2 p_r19.26 f2_iuneq2 f3_iuneq2 a_wceq f0_iuneq2 f1_iuneq2 a_wral f2_iuneq2 f3_iuneq2 a_wss f3_iuneq2 f2_iuneq2 a_wss a_wa f0_iuneq2 f1_iuneq2 a_wral f2_iuneq2 f3_iuneq2 a_wss f0_iuneq2 f1_iuneq2 a_wral f3_iuneq2 f2_iuneq2 a_wss f0_iuneq2 f1_iuneq2 a_wral a_wa p_bitri f0_iuneq2 f1_iuneq2 f2_iuneq2 a_ciun f0_iuneq2 f1_iuneq2 f3_iuneq2 a_ciun p_eqss f2_iuneq2 f3_iuneq2 a_wss f0_iuneq2 f1_iuneq2 a_wral f3_iuneq2 f2_iuneq2 a_wss f0_iuneq2 f1_iuneq2 a_wral a_wa f0_iuneq2 f1_iuneq2 f2_iuneq2 a_ciun f0_iuneq2 f1_iuneq2 f3_iuneq2 a_ciun a_wss f0_iuneq2 f1_iuneq2 f3_iuneq2 a_ciun f0_iuneq2 f1_iuneq2 f2_iuneq2 a_ciun a_wss a_wa f2_iuneq2 f3_iuneq2 a_wceq f0_iuneq2 f1_iuneq2 a_wral f0_iuneq2 f1_iuneq2 f2_iuneq2 a_ciun f0_iuneq2 f1_iuneq2 f3_iuneq2 a_ciun a_wceq p_3imtr4i $.
$}

$(Equality theorem for indexed intersection.  (Contributed by NM,
       22-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B C  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	f0_iineq2 $f set x $.
	f1_iineq2 $f class A $.
	f2_iineq2 $f class B $.
	f3_iineq2 $f class C $.
	i0_iineq2 $f set y $.
	p_iineq2 $p |- ( A. x e. A B = C -> |^|_ x e. A B = |^|_ x e. A C ) $= f2_iineq2 f3_iineq2 i0_iineq2 a_sup_set_class p_eleq2 f2_iineq2 f3_iineq2 a_wceq i0_iineq2 a_sup_set_class f2_iineq2 a_wcel i0_iineq2 a_sup_set_class f3_iineq2 a_wcel a_wb f0_iineq2 f1_iineq2 p_ralimi i0_iineq2 a_sup_set_class f2_iineq2 a_wcel i0_iineq2 a_sup_set_class f3_iineq2 a_wcel f0_iineq2 f1_iineq2 p_ralbi f2_iineq2 f3_iineq2 a_wceq f0_iineq2 f1_iineq2 a_wral i0_iineq2 a_sup_set_class f2_iineq2 a_wcel i0_iineq2 a_sup_set_class f3_iineq2 a_wcel a_wb f0_iineq2 f1_iineq2 a_wral i0_iineq2 a_sup_set_class f2_iineq2 a_wcel f0_iineq2 f1_iineq2 a_wral i0_iineq2 a_sup_set_class f3_iineq2 a_wcel f0_iineq2 f1_iineq2 a_wral a_wb p_syl f2_iineq2 f3_iineq2 a_wceq f0_iineq2 f1_iineq2 a_wral i0_iineq2 a_sup_set_class f2_iineq2 a_wcel f0_iineq2 f1_iineq2 a_wral i0_iineq2 a_sup_set_class f3_iineq2 a_wcel f0_iineq2 f1_iineq2 a_wral i0_iineq2 p_abbidv f0_iineq2 i0_iineq2 f1_iineq2 f2_iineq2 a_df-iin f0_iineq2 i0_iineq2 f1_iineq2 f3_iineq2 a_df-iin f2_iineq2 f3_iineq2 a_wceq f0_iineq2 f1_iineq2 a_wral i0_iineq2 a_sup_set_class f2_iineq2 a_wcel f0_iineq2 f1_iineq2 a_wral i0_iineq2 a_cab i0_iineq2 a_sup_set_class f3_iineq2 a_wcel f0_iineq2 f1_iineq2 a_wral i0_iineq2 a_cab f0_iineq2 f1_iineq2 f2_iineq2 a_ciin f0_iineq2 f1_iineq2 f3_iineq2 a_ciin p_3eqtr4g $.
$}

$(Equality inference for indexed union.  (Contributed by NM,
       22-Oct-2003.) $)

${
	$v x A B C  $.
	f0_iuneq2i $f set x $.
	f1_iuneq2i $f class A $.
	f2_iuneq2i $f class B $.
	f3_iuneq2i $f class C $.
	e0_iuneq2i $e |- ( x e. A -> B = C ) $.
	p_iuneq2i $p |- U_ x e. A B = U_ x e. A C $= f0_iuneq2i f1_iuneq2i f2_iuneq2i f3_iuneq2i p_iuneq2 e0_iuneq2i f2_iuneq2i f3_iuneq2i a_wceq f0_iuneq2i f1_iuneq2i f2_iuneq2i a_ciun f0_iuneq2i f1_iuneq2i f3_iuneq2i a_ciun a_wceq f0_iuneq2i f1_iuneq2i p_mprg $.
$}

$(Equality inference for indexed intersection.  (Contributed by NM,
       22-Oct-2003.) $)

${
	$v x A B C  $.
	f0_iineq2i $f set x $.
	f1_iineq2i $f class A $.
	f2_iineq2i $f class B $.
	f3_iineq2i $f class C $.
	e0_iineq2i $e |- ( x e. A -> B = C ) $.
	p_iineq2i $p |- |^|_ x e. A B = |^|_ x e. A C $= f0_iineq2i f1_iineq2i f2_iineq2i f3_iineq2i p_iineq2 e0_iineq2i f2_iineq2i f3_iineq2i a_wceq f0_iineq2i f1_iineq2i f2_iineq2i a_ciin f0_iineq2i f1_iineq2i f3_iineq2i a_ciin a_wceq f0_iineq2i f1_iineq2i p_mprg $.
$}

$(Equality deduction for indexed intersection.  (Contributed by NM,
       7-Dec-2011.) $)

${
	$v ph x A B C  $.
	f0_iineq2d $f wff ph $.
	f1_iineq2d $f set x $.
	f2_iineq2d $f class A $.
	f3_iineq2d $f class B $.
	f4_iineq2d $f class C $.
	e0_iineq2d $e |- F/ x ph $.
	e1_iineq2d $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	p_iineq2d $p |- ( ph -> |^|_ x e. A B = |^|_ x e. A C ) $= e0_iineq2d e1_iineq2d f0_iineq2d f1_iineq2d a_sup_set_class f2_iineq2d a_wcel f3_iineq2d f4_iineq2d a_wceq p_ex f0_iineq2d f3_iineq2d f4_iineq2d a_wceq f1_iineq2d f2_iineq2d p_ralrimi f1_iineq2d f2_iineq2d f3_iineq2d f4_iineq2d p_iineq2 f0_iineq2d f3_iineq2d f4_iineq2d a_wceq f1_iineq2d f2_iineq2d a_wral f1_iineq2d f2_iineq2d f3_iineq2d a_ciin f1_iineq2d f2_iineq2d f4_iineq2d a_ciin a_wceq p_syl $.
$}

$(Equality deduction for indexed union.  (Contributed by NM,
       3-Aug-2004.) $)

${
	$v ph x A B C  $.
	$d x ph  $.
	f0_iuneq2dv $f wff ph $.
	f1_iuneq2dv $f set x $.
	f2_iuneq2dv $f class A $.
	f3_iuneq2dv $f class B $.
	f4_iuneq2dv $f class C $.
	e0_iuneq2dv $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	p_iuneq2dv $p |- ( ph -> U_ x e. A B = U_ x e. A C ) $= e0_iuneq2dv f0_iuneq2dv f3_iuneq2dv f4_iuneq2dv a_wceq f1_iuneq2dv f2_iuneq2dv p_ralrimiva f1_iuneq2dv f2_iuneq2dv f3_iuneq2dv f4_iuneq2dv p_iuneq2 f0_iuneq2dv f3_iuneq2dv f4_iuneq2dv a_wceq f1_iuneq2dv f2_iuneq2dv a_wral f1_iuneq2dv f2_iuneq2dv f3_iuneq2dv a_ciun f1_iuneq2dv f2_iuneq2dv f4_iuneq2dv a_ciun a_wceq p_syl $.
$}

$(Equality deduction for indexed intersection.  (Contributed by NM,
       3-Aug-2004.) $)

${
	$v ph x A B C  $.
	$d x ph  $.
	f0_iineq2dv $f wff ph $.
	f1_iineq2dv $f set x $.
	f2_iineq2dv $f class A $.
	f3_iineq2dv $f class B $.
	f4_iineq2dv $f class C $.
	e0_iineq2dv $e |- ( ( ph /\ x e. A ) -> B = C ) $.
	p_iineq2dv $p |- ( ph -> |^|_ x e. A B = |^|_ x e. A C ) $= f0_iineq2dv f1_iineq2dv p_nfv e0_iineq2dv f0_iineq2dv f1_iineq2dv f2_iineq2dv f3_iineq2dv f4_iineq2dv p_iineq2d $.
$}

$(Equality theorem for indexed union, deduction version.  (Contributed by
       Drahflow, 22-Oct-2015.) $)

${
	$v ph x A B C  $.
	$d x A  $.
	$d x B  $.
	f0_iuneq1d $f wff ph $.
	f1_iuneq1d $f set x $.
	f2_iuneq1d $f class A $.
	f3_iuneq1d $f class B $.
	f4_iuneq1d $f class C $.
	e0_iuneq1d $e |- ( ph -> A = B ) $.
	p_iuneq1d $p |- ( ph -> U_ x e. A C = U_ x e. B C ) $= e0_iuneq1d f1_iuneq1d f2_iuneq1d f3_iuneq1d f4_iuneq1d p_iuneq1 f0_iuneq1d f2_iuneq1d f3_iuneq1d a_wceq f1_iuneq1d f2_iuneq1d f4_iuneq1d a_ciun f1_iuneq1d f3_iuneq1d f4_iuneq1d a_ciun a_wceq p_syl $.
$}

$(Equality deduction for indexed union, deduction version.  (Contributed
         by Drahflow, 22-Oct-2015.) $)

${
	$v ph x A B C D  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_iuneq12d $f wff ph $.
	f1_iuneq12d $f set x $.
	f2_iuneq12d $f class A $.
	f3_iuneq12d $f class B $.
	f4_iuneq12d $f class C $.
	f5_iuneq12d $f class D $.
	e0_iuneq12d $e |- ( ph -> A = B ) $.
	e1_iuneq12d $e |- ( ph -> C = D ) $.
	p_iuneq12d $p |- ( ph -> U_ x e. A C = U_ x e. B D ) $= e0_iuneq12d f0_iuneq12d f1_iuneq12d f2_iuneq12d f3_iuneq12d f4_iuneq12d p_iuneq1d e1_iuneq12d f0_iuneq12d f4_iuneq12d f5_iuneq12d a_wceq f1_iuneq12d a_sup_set_class f3_iuneq12d a_wcel p_adantr f0_iuneq12d f1_iuneq12d f3_iuneq12d f4_iuneq12d f5_iuneq12d p_iuneq2dv f0_iuneq12d f1_iuneq12d f2_iuneq12d f4_iuneq12d a_ciun f1_iuneq12d f3_iuneq12d f4_iuneq12d a_ciun f1_iuneq12d f3_iuneq12d f5_iuneq12d a_ciun p_eqtrd $.
$}

$(Equality deduction for indexed union.  (Contributed by Drahflow,
       22-Oct-2015.) $)

${
	$v ph x A B C  $.
	$d x ph  $.
	$d x A  $.
	f0_iuneq2d $f wff ph $.
	f1_iuneq2d $f set x $.
	f2_iuneq2d $f class A $.
	f3_iuneq2d $f class B $.
	f4_iuneq2d $f class C $.
	e0_iuneq2d $e |- ( ph -> B = C ) $.
	p_iuneq2d $p |- ( ph -> U_ x e. A B = U_ x e. A C ) $= e0_iuneq2d f0_iuneq2d f3_iuneq2d f4_iuneq2d a_wceq f1_iuneq2d a_sup_set_class f2_iuneq2d a_wcel p_adantr f0_iuneq2d f1_iuneq2d f2_iuneq2d f3_iuneq2d f4_iuneq2d p_iuneq2dv $.
$}

$(Bound-variable hypothesis builder for indexed union.  (Contributed by
       Mario Carneiro, 25-Jan-2014.) $)

${
	$v x y A B  $.
	$d z A  $.
	$d z B  $.
	$d x z  $.
	$d y z  $.
	f0_nfiun $f set x $.
	f1_nfiun $f set y $.
	f2_nfiun $f class A $.
	f3_nfiun $f class B $.
	i0_nfiun $f set z $.
	e0_nfiun $e |- F/_ y A $.
	e1_nfiun $e |- F/_ y B $.
	p_nfiun $p |- F/_ y U_ x e. A B $= f0_nfiun i0_nfiun f2_nfiun f3_nfiun a_df-iun e0_nfiun e1_nfiun f1_nfiun i0_nfiun f3_nfiun p_nfcri i0_nfiun a_sup_set_class f3_nfiun a_wcel f1_nfiun f0_nfiun f2_nfiun p_nfrex i0_nfiun a_sup_set_class f3_nfiun a_wcel f0_nfiun f2_nfiun a_wrex f1_nfiun i0_nfiun p_nfab f1_nfiun f0_nfiun f2_nfiun f3_nfiun a_ciun i0_nfiun a_sup_set_class f3_nfiun a_wcel f0_nfiun f2_nfiun a_wrex i0_nfiun a_cab p_nfcxfr $.
$}

$(Bound-variable hypothesis builder for indexed intersection.
       (Contributed by Mario Carneiro, 25-Jan-2014.) $)

${
	$v x y A B  $.
	$d z A  $.
	$d z B  $.
	$d x z  $.
	$d y z  $.
	f0_nfiin $f set x $.
	f1_nfiin $f set y $.
	f2_nfiin $f class A $.
	f3_nfiin $f class B $.
	i0_nfiin $f set z $.
	e0_nfiin $e |- F/_ y A $.
	e1_nfiin $e |- F/_ y B $.
	p_nfiin $p |- F/_ y |^|_ x e. A B $= f0_nfiin i0_nfiin f2_nfiin f3_nfiin a_df-iin e0_nfiin e1_nfiin f1_nfiin i0_nfiin f3_nfiin p_nfcri i0_nfiin a_sup_set_class f3_nfiin a_wcel f1_nfiin f0_nfiin f2_nfiin p_nfral i0_nfiin a_sup_set_class f3_nfiin a_wcel f0_nfiin f2_nfiin a_wral f1_nfiin i0_nfiin p_nfab f1_nfiin f0_nfiin f2_nfiin f3_nfiin a_ciin i0_nfiin a_sup_set_class f3_nfiin a_wcel f0_nfiin f2_nfiin a_wral i0_nfiin a_cab p_nfcxfr $.
$}

$(Bound-variable hypothesis builder for indexed union.  (Contributed by
       NM, 12-Oct-2003.) $)

${
	$v x A B  $.
	$d y A  $.
	$d y B  $.
	$d x y  $.
	f0_nfiu1 $f set x $.
	f1_nfiu1 $f class A $.
	f2_nfiu1 $f class B $.
	i0_nfiu1 $f set y $.
	p_nfiu1 $p |- F/_ x U_ x e. A B $= f0_nfiu1 i0_nfiu1 f1_nfiu1 f2_nfiu1 a_df-iun i0_nfiu1 a_sup_set_class f2_nfiu1 a_wcel f0_nfiu1 f1_nfiu1 p_nfre1 i0_nfiu1 a_sup_set_class f2_nfiu1 a_wcel f0_nfiu1 f1_nfiu1 a_wrex f0_nfiu1 i0_nfiu1 p_nfab f0_nfiu1 f0_nfiu1 f1_nfiu1 f2_nfiu1 a_ciun i0_nfiu1 a_sup_set_class f2_nfiu1 a_wcel f0_nfiu1 f1_nfiu1 a_wrex i0_nfiu1 a_cab p_nfcxfr $.
$}

$(Bound-variable hypothesis builder for indexed intersection.
       (Contributed by NM, 15-Oct-2003.) $)

${
	$v x A B  $.
	$d y A  $.
	$d y B  $.
	$d x y  $.
	f0_nfii1 $f set x $.
	f1_nfii1 $f class A $.
	f2_nfii1 $f class B $.
	i0_nfii1 $f set y $.
	p_nfii1 $p |- F/_ x |^|_ x e. A B $= f0_nfii1 i0_nfii1 f1_nfii1 f2_nfii1 a_df-iin i0_nfii1 a_sup_set_class f2_nfii1 a_wcel f0_nfii1 f1_nfii1 p_nfra1 i0_nfii1 a_sup_set_class f2_nfii1 a_wcel f0_nfii1 f1_nfii1 a_wral f0_nfii1 i0_nfii1 p_nfab f0_nfii1 f0_nfii1 f1_nfii1 f2_nfii1 a_ciin i0_nfii1 a_sup_set_class f2_nfii1 a_wcel f0_nfii1 f1_nfii1 a_wral i0_nfii1 a_cab p_nfcxfr $.
$}

$(Alternate definition of indexed union when ` B ` is a set.  Definition
       15(a) of [Suppes] p. 44.  (Contributed by NM, 23-Mar-2006.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x y A B C  $.
	$d y z A  $.
	$d y z B  $.
	$d C z  $.
	$d x y z  $.
	f0_dfiun2g $f set x $.
	f1_dfiun2g $f set y $.
	f2_dfiun2g $f class A $.
	f3_dfiun2g $f class B $.
	f4_dfiun2g $f class C $.
	i0_dfiun2g $f set z $.
	p_dfiun2g $p |- ( A. x e. A B e. C -> U_ x e. A B = U. { y | E. x e. A y = B } ) $= f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g p_nfra1 f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g p_rsp f1_dfiun2g i0_dfiun2g a_sup_set_class f3_dfiun2g f4_dfiun2g p_clel3g f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wral f0_dfiun2g a_sup_set_class f2_dfiun2g a_wcel f3_dfiun2g f4_dfiun2g a_wcel i0_dfiun2g a_sup_set_class f3_dfiun2g a_wcel f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f1_dfiun2g a_wex a_wb p_syl6 f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wral f0_dfiun2g a_sup_set_class f2_dfiun2g a_wcel i0_dfiun2g a_sup_set_class f3_dfiun2g a_wcel f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f1_dfiun2g a_wex a_wb p_imp f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wral i0_dfiun2g a_sup_set_class f3_dfiun2g a_wcel f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f1_dfiun2g a_wex f0_dfiun2g f2_dfiun2g p_rexbida f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f0_dfiun2g f1_dfiun2g f2_dfiun2g p_rexcom4 f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wral i0_dfiun2g a_sup_set_class f3_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f1_dfiun2g a_wex f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_wex p_syl6bb f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel f0_dfiun2g f2_dfiun2g p_r19.41v f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f1_dfiun2g p_exbii f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel f1_dfiun2g p_exancom f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_wex f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f1_dfiun2g a_wex i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex a_wa f1_dfiun2g a_wex p_bitri f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wral i0_dfiun2g a_sup_set_class f3_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel a_wa f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_wex i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex a_wa f1_dfiun2g a_wex p_syl6bb f0_dfiun2g i0_dfiun2g a_sup_set_class f2_dfiun2g f3_dfiun2g p_eliun f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g i0_dfiun2g a_sup_set_class p_eluniab f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wral i0_dfiun2g a_sup_set_class f3_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wrex i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class a_wcel f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex a_wa f1_dfiun2g a_wex i0_dfiun2g a_sup_set_class f0_dfiun2g f2_dfiun2g f3_dfiun2g a_ciun a_wcel i0_dfiun2g a_sup_set_class f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_cab a_cuni a_wcel p_3bitr4g f3_dfiun2g f4_dfiun2g a_wcel f0_dfiun2g f2_dfiun2g a_wral i0_dfiun2g f0_dfiun2g f2_dfiun2g f3_dfiun2g a_ciun f1_dfiun2g a_sup_set_class f3_dfiun2g a_wceq f0_dfiun2g f2_dfiun2g a_wrex f1_dfiun2g a_cab a_cuni p_eqrdv $.
$}

$(Alternate definition of indexed intersection when ` B ` is a set.
       (Contributed by Jeff Hankins, 27-Aug-2009.) $)

${
	$v x y A B C  $.
	$d y z w A  $.
	$d y z w B  $.
	$d w C z  $.
	$d w x y z  $.
	f0_dfiin2g $f set x $.
	f1_dfiin2g $f set y $.
	f2_dfiin2g $f class A $.
	f3_dfiin2g $f class B $.
	f4_dfiin2g $f class C $.
	i0_dfiin2g $f set z $.
	i1_dfiin2g $f set w $.
	p_dfiin2g $p |- ( A. x e. A B e. C -> |^|_ x e. A B = |^| { y | E. x e. A y = B } ) $= i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_df-ral f3_dfiin2g f4_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_df-ral i0_dfiin2g a_sup_set_class f3_dfiin2g i1_dfiin2g a_sup_set_class p_eleq2 i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel p_biimprcd i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g p_alrimiv f3_dfiin2g p_eqid i0_dfiin2g a_sup_set_class f3_dfiin2g f3_dfiin2g p_eqeq1 i0_dfiin2g a_sup_set_class f3_dfiin2g i1_dfiin2g a_sup_set_class p_eleq2 i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f3_dfiin2g f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel p_imbi12d i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi f3_dfiin2g f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel a_wi i0_dfiin2g f3_dfiin2g f4_dfiin2g p_spcgv f3_dfiin2g f4_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal f3_dfiin2g f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel p_mpii f3_dfiin2g f4_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal p_impbid2 f3_dfiin2g f4_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wb f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel p_imim2i f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel f3_dfiin2g f4_dfiin2g a_wcel a_wi f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal p_pm5.74d f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel f3_dfiin2g f4_dfiin2g a_wcel a_wi f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel a_wi f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wi a_wb f0_dfiin2g p_alimi f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel a_wi f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wi f0_dfiin2g p_albi f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel f3_dfiin2g f4_dfiin2g a_wcel a_wi f0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel a_wi f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wi a_wb f0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel a_wi f0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wi f0_dfiin2g a_wal a_wb p_syl f3_dfiin2g f4_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_wral f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel f3_dfiin2g f4_dfiin2g a_wcel a_wi f0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel a_wi f0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wi f0_dfiin2g a_wal a_wb p_sylbi i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi f0_dfiin2g f2_dfiin2g a_df-ral i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi f0_dfiin2g f2_dfiin2g a_wral f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi a_wi f0_dfiin2g a_wal i0_dfiin2g p_albii f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi a_wi f0_dfiin2g i0_dfiin2g p_alcom i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi f0_dfiin2g f2_dfiin2g a_wral i0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi a_wi f0_dfiin2g a_wal i0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi a_wi i0_dfiin2g a_wal f0_dfiin2g a_wal p_bitr4i i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel f0_dfiin2g f2_dfiin2g p_r19.23v i0_dfiin2g p_vex f1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class f3_dfiin2g p_eqeq1 f1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wceq f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g p_rexbidv f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g i0_dfiin2g a_sup_set_class p_elab i0_dfiin2g a_sup_set_class f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel p_imbi1i i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi f0_dfiin2g f2_dfiin2g a_wral i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_sup_set_class f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_wcel i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi p_bitr4i i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi f0_dfiin2g f2_dfiin2g a_wral i0_dfiin2g a_sup_set_class f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_wcel i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g p_albii f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g p_19.21v f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi a_wi i0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wi f0_dfiin2g p_albii i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi f0_dfiin2g f2_dfiin2g a_wral i0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi a_wi i0_dfiin2g a_wal f0_dfiin2g a_wal i0_dfiin2g a_sup_set_class f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_wcel i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wi f0_dfiin2g a_wal p_3bitr3ri f3_dfiin2g f4_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_wral f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel a_wi f0_dfiin2g a_wal f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i0_dfiin2g a_sup_set_class f3_dfiin2g a_wceq i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal a_wi f0_dfiin2g a_wal i0_dfiin2g a_sup_set_class f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_wcel i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal p_syl6bb i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_wral f0_dfiin2g a_sup_set_class f2_dfiin2g a_wcel i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel a_wi f0_dfiin2g a_wal f3_dfiin2g f4_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_wral i0_dfiin2g a_sup_set_class f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_wcel i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal p_syl5bb f3_dfiin2g f4_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_wral i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_wral i0_dfiin2g a_sup_set_class f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_wcel i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal i1_dfiin2g p_abbidv f0_dfiin2g i1_dfiin2g f2_dfiin2g f3_dfiin2g a_df-iin i1_dfiin2g i0_dfiin2g f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_df-int f3_dfiin2g f4_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_wral i1_dfiin2g a_sup_set_class f3_dfiin2g a_wcel f0_dfiin2g f2_dfiin2g a_wral i1_dfiin2g a_cab i0_dfiin2g a_sup_set_class f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_wcel i1_dfiin2g a_sup_set_class i0_dfiin2g a_sup_set_class a_wcel a_wi i0_dfiin2g a_wal i1_dfiin2g a_cab f0_dfiin2g f2_dfiin2g f3_dfiin2g a_ciin f1_dfiin2g a_sup_set_class f3_dfiin2g a_wceq f0_dfiin2g f2_dfiin2g a_wrex f1_dfiin2g a_cab a_cint p_3eqtr4g $.
$}

$(Alternate definition of indexed union when ` B ` is a set.  Definition
       15(a) of [Suppes] p. 44.  (Contributed by NM, 27-Jun-1998.)  (Revised by
       David Abernethy, 19-Jun-2012.) $)

${
	$v x y A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_dfiun2 $f set x $.
	f1_dfiun2 $f set y $.
	f2_dfiun2 $f class A $.
	f3_dfiun2 $f class B $.
	e0_dfiun2 $e |- B e. _V $.
	p_dfiun2 $p |- U_ x e. A B = U. { y | E. x e. A y = B } $= f0_dfiun2 f1_dfiun2 f2_dfiun2 f3_dfiun2 a_cvv p_dfiun2g e0_dfiun2 f3_dfiun2 a_cvv a_wcel f0_dfiun2 a_sup_set_class f2_dfiun2 a_wcel p_a1i f3_dfiun2 a_cvv a_wcel f0_dfiun2 f2_dfiun2 f3_dfiun2 a_ciun f1_dfiun2 a_sup_set_class f3_dfiun2 a_wceq f0_dfiun2 f2_dfiun2 a_wrex f1_dfiun2 a_cab a_cuni a_wceq f0_dfiun2 f2_dfiun2 p_mprg $.
$}

$(Alternate definition of indexed intersection when ` B ` is a set.
       Definition 15(b) of [Suppes] p. 44.  (Contributed by NM, 28-Jun-1998.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x y A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_dfiin2 $f set x $.
	f1_dfiin2 $f set y $.
	f2_dfiin2 $f class A $.
	f3_dfiin2 $f class B $.
	e0_dfiin2 $e |- B e. _V $.
	p_dfiin2 $p |- |^|_ x e. A B = |^| { y | E. x e. A y = B } $= f0_dfiin2 f1_dfiin2 f2_dfiin2 f3_dfiin2 a_cvv p_dfiin2g e0_dfiin2 f3_dfiin2 a_cvv a_wcel f0_dfiin2 a_sup_set_class f2_dfiin2 a_wcel p_a1i f3_dfiin2 a_cvv a_wcel f0_dfiin2 f2_dfiin2 f3_dfiin2 a_ciin f1_dfiin2 a_sup_set_class f3_dfiin2 a_wceq f0_dfiin2 f2_dfiin2 a_wrex f1_dfiin2 a_cab a_cint a_wceq f0_dfiin2 f2_dfiin2 p_mprg $.
$}

$(Rule used to change the bound variables in an indexed union, with the
       substitution specified implicitly by the hypothesis.  (Contributed by
       NM, 26-Mar-2006.)  (Revised by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x y A B C  $.
	$d z y A  $.
	$d z x A  $.
	$d z B  $.
	$d z C  $.
	f0_cbviun $f set x $.
	f1_cbviun $f set y $.
	f2_cbviun $f class A $.
	f3_cbviun $f class B $.
	f4_cbviun $f class C $.
	i0_cbviun $f set z $.
	e0_cbviun $e |- F/_ y B $.
	e1_cbviun $e |- F/_ x C $.
	e2_cbviun $e |- ( x = y -> B = C ) $.
	p_cbviun $p |- U_ x e. A B = U_ y e. A C $= e0_cbviun f1_cbviun i0_cbviun f3_cbviun p_nfcri e1_cbviun f0_cbviun i0_cbviun f4_cbviun p_nfcri e2_cbviun f0_cbviun a_sup_set_class f1_cbviun a_sup_set_class a_wceq f3_cbviun f4_cbviun i0_cbviun a_sup_set_class p_eleq2d i0_cbviun a_sup_set_class f3_cbviun a_wcel i0_cbviun a_sup_set_class f4_cbviun a_wcel f0_cbviun f1_cbviun f2_cbviun p_cbvrex i0_cbviun a_sup_set_class f3_cbviun a_wcel f0_cbviun f2_cbviun a_wrex i0_cbviun a_sup_set_class f4_cbviun a_wcel f1_cbviun f2_cbviun a_wrex i0_cbviun p_abbii f0_cbviun i0_cbviun f2_cbviun f3_cbviun a_df-iun f1_cbviun i0_cbviun f2_cbviun f4_cbviun a_df-iun i0_cbviun a_sup_set_class f3_cbviun a_wcel f0_cbviun f2_cbviun a_wrex i0_cbviun a_cab i0_cbviun a_sup_set_class f4_cbviun a_wcel f1_cbviun f2_cbviun a_wrex i0_cbviun a_cab f0_cbviun f2_cbviun f3_cbviun a_ciun f1_cbviun f2_cbviun f4_cbviun a_ciun p_3eqtr4i $.
$}

$(Change bound variables in an indexed intersection.  (Contributed by Jeff
       Hankins, 26-Aug-2009.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)

${
	$v x y A B C  $.
	$d z y A  $.
	$d z x A  $.
	$d z B  $.
	$d z C  $.
	f0_cbviin $f set x $.
	f1_cbviin $f set y $.
	f2_cbviin $f class A $.
	f3_cbviin $f class B $.
	f4_cbviin $f class C $.
	i0_cbviin $f set z $.
	e0_cbviin $e |- F/_ y B $.
	e1_cbviin $e |- F/_ x C $.
	e2_cbviin $e |- ( x = y -> B = C ) $.
	p_cbviin $p |- |^|_ x e. A B = |^|_ y e. A C $= e0_cbviin f1_cbviin i0_cbviin f3_cbviin p_nfcri e1_cbviin f0_cbviin i0_cbviin f4_cbviin p_nfcri e2_cbviin f0_cbviin a_sup_set_class f1_cbviin a_sup_set_class a_wceq f3_cbviin f4_cbviin i0_cbviin a_sup_set_class p_eleq2d i0_cbviin a_sup_set_class f3_cbviin a_wcel i0_cbviin a_sup_set_class f4_cbviin a_wcel f0_cbviin f1_cbviin f2_cbviin p_cbvral i0_cbviin a_sup_set_class f3_cbviin a_wcel f0_cbviin f2_cbviin a_wral i0_cbviin a_sup_set_class f4_cbviin a_wcel f1_cbviin f2_cbviin a_wral i0_cbviin p_abbii f0_cbviin i0_cbviin f2_cbviin f3_cbviin a_df-iin f1_cbviin i0_cbviin f2_cbviin f4_cbviin a_df-iin i0_cbviin a_sup_set_class f3_cbviin a_wcel f0_cbviin f2_cbviin a_wral i0_cbviin a_cab i0_cbviin a_sup_set_class f4_cbviin a_wcel f1_cbviin f2_cbviin a_wral i0_cbviin a_cab f0_cbviin f2_cbviin f3_cbviin a_ciin f1_cbviin f2_cbviin f4_cbviin a_ciin p_3eqtr4i $.
$}

$(Rule used to change the bound variables in an indexed union, with the
       substitution specified implicitly by the hypothesis.  (Contributed by
       NM, 15-Sep-2003.) $)

${
	$v x y A B C  $.
	$d x A  $.
	$d y A  $.
	$d y B  $.
	$d x C  $.
	f0_cbviunv $f set x $.
	f1_cbviunv $f set y $.
	f2_cbviunv $f class A $.
	f3_cbviunv $f class B $.
	f4_cbviunv $f class C $.
	e0_cbviunv $e |- ( x = y -> B = C ) $.
	p_cbviunv $p |- U_ x e. A B = U_ y e. A C $= f1_cbviunv f3_cbviunv p_nfcv f0_cbviunv f4_cbviunv p_nfcv e0_cbviunv f0_cbviunv f1_cbviunv f2_cbviunv f3_cbviunv f4_cbviunv p_cbviun $.
$}

$(Change bound variables in an indexed intersection.  (Contributed by Jeff
       Hankins, 26-Aug-2009.) $)

${
	$v x y A B C  $.
	$d x A  $.
	$d y A  $.
	$d y B  $.
	$d x C  $.
	f0_cbviinv $f set x $.
	f1_cbviinv $f set y $.
	f2_cbviinv $f class A $.
	f3_cbviinv $f class B $.
	f4_cbviinv $f class C $.
	e0_cbviinv $e |- ( x = y -> B = C ) $.
	p_cbviinv $p |- |^|_ x e. A B = |^|_ y e. A C $= f1_cbviinv f3_cbviinv p_nfcv f0_cbviinv f4_cbviinv p_nfcv e0_cbviinv f0_cbviinv f1_cbviinv f2_cbviinv f3_cbviinv f4_cbviinv p_cbviin $.
$}

$(Subset theorem for an indexed union.  (Contributed by NM, 13-Sep-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B C  $.
	$d x y C  $.
	$d y A  $.
	$d y B  $.
	f0_iunss $f set x $.
	f1_iunss $f class A $.
	f2_iunss $f class B $.
	f3_iunss $f class C $.
	i0_iunss $f set y $.
	p_iunss $p |- ( U_ x e. A B C_ C <-> A. x e. A B C_ C ) $= f0_iunss i0_iunss f1_iunss f2_iunss a_df-iun f0_iunss f1_iunss f2_iunss a_ciun i0_iunss a_sup_set_class f2_iunss a_wcel f0_iunss f1_iunss a_wrex i0_iunss a_cab f3_iunss p_sseq1i i0_iunss a_sup_set_class f2_iunss a_wcel f0_iunss f1_iunss a_wrex i0_iunss f3_iunss p_abss i0_iunss f2_iunss f3_iunss p_dfss2 f2_iunss f3_iunss a_wss i0_iunss a_sup_set_class f2_iunss a_wcel i0_iunss a_sup_set_class f3_iunss a_wcel a_wi i0_iunss a_wal f0_iunss f1_iunss p_ralbii i0_iunss a_sup_set_class f2_iunss a_wcel i0_iunss a_sup_set_class f3_iunss a_wcel a_wi f0_iunss i0_iunss f1_iunss p_ralcom4 i0_iunss a_sup_set_class f2_iunss a_wcel i0_iunss a_sup_set_class f3_iunss a_wcel f0_iunss f1_iunss p_r19.23v i0_iunss a_sup_set_class f2_iunss a_wcel i0_iunss a_sup_set_class f3_iunss a_wcel a_wi f0_iunss f1_iunss a_wral i0_iunss a_sup_set_class f2_iunss a_wcel f0_iunss f1_iunss a_wrex i0_iunss a_sup_set_class f3_iunss a_wcel a_wi i0_iunss p_albii f2_iunss f3_iunss a_wss f0_iunss f1_iunss a_wral i0_iunss a_sup_set_class f2_iunss a_wcel i0_iunss a_sup_set_class f3_iunss a_wcel a_wi i0_iunss a_wal f0_iunss f1_iunss a_wral i0_iunss a_sup_set_class f2_iunss a_wcel i0_iunss a_sup_set_class f3_iunss a_wcel a_wi f0_iunss f1_iunss a_wral i0_iunss a_wal i0_iunss a_sup_set_class f2_iunss a_wcel f0_iunss f1_iunss a_wrex i0_iunss a_sup_set_class f3_iunss a_wcel a_wi i0_iunss a_wal p_3bitrri f0_iunss f1_iunss f2_iunss a_ciun f3_iunss a_wss i0_iunss a_sup_set_class f2_iunss a_wcel f0_iunss f1_iunss a_wrex i0_iunss a_cab f3_iunss a_wss i0_iunss a_sup_set_class f2_iunss a_wcel f0_iunss f1_iunss a_wrex i0_iunss a_sup_set_class f3_iunss a_wcel a_wi i0_iunss a_wal f2_iunss f3_iunss a_wss f0_iunss f1_iunss a_wral p_3bitri $.
$}

$(Subset implication for an indexed union.  (Contributed by NM,
       3-Sep-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B C  $.
	$d x y C  $.
	$d y A  $.
	$d y B  $.
	f0_ssiun $f set x $.
	f1_ssiun $f class A $.
	f2_ssiun $f class B $.
	f3_ssiun $f class C $.
	i0_ssiun $f set y $.
	p_ssiun $p |- ( E. x e. A C C_ B -> C C_ U_ x e. A B ) $= f3_ssiun f2_ssiun i0_ssiun a_sup_set_class p_ssel f3_ssiun f2_ssiun a_wss i0_ssiun a_sup_set_class f3_ssiun a_wcel i0_ssiun a_sup_set_class f2_ssiun a_wcel a_wi f0_ssiun f1_ssiun p_reximi i0_ssiun a_sup_set_class f3_ssiun a_wcel i0_ssiun a_sup_set_class f2_ssiun a_wcel f0_ssiun f1_ssiun p_r19.37av f3_ssiun f2_ssiun a_wss f0_ssiun f1_ssiun a_wrex i0_ssiun a_sup_set_class f3_ssiun a_wcel i0_ssiun a_sup_set_class f2_ssiun a_wcel a_wi f0_ssiun f1_ssiun a_wrex i0_ssiun a_sup_set_class f3_ssiun a_wcel i0_ssiun a_sup_set_class f2_ssiun a_wcel f0_ssiun f1_ssiun a_wrex a_wi p_syl f0_ssiun i0_ssiun a_sup_set_class f1_ssiun f2_ssiun p_eliun f3_ssiun f2_ssiun a_wss f0_ssiun f1_ssiun a_wrex i0_ssiun a_sup_set_class f3_ssiun a_wcel i0_ssiun a_sup_set_class f2_ssiun a_wcel f0_ssiun f1_ssiun a_wrex i0_ssiun a_sup_set_class f0_ssiun f1_ssiun f2_ssiun a_ciun a_wcel p_syl6ibr f3_ssiun f2_ssiun a_wss f0_ssiun f1_ssiun a_wrex i0_ssiun f3_ssiun f0_ssiun f1_ssiun f2_ssiun a_ciun p_ssrdv $.
$}

$(Identity law for subset of an indexed union.  (Contributed by NM,
       12-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B  $.
	$d y A  $.
	$d y B  $.
	$d x y  $.
	f0_ssiun2 $f set x $.
	f1_ssiun2 $f class A $.
	f2_ssiun2 $f class B $.
	i0_ssiun2 $f set y $.
	p_ssiun2 $p |- ( x e. A -> B C_ U_ x e. A B ) $= i0_ssiun2 a_sup_set_class f2_ssiun2 a_wcel f0_ssiun2 f1_ssiun2 p_rspe f0_ssiun2 a_sup_set_class f1_ssiun2 a_wcel i0_ssiun2 a_sup_set_class f2_ssiun2 a_wcel i0_ssiun2 a_sup_set_class f2_ssiun2 a_wcel f0_ssiun2 f1_ssiun2 a_wrex p_ex f0_ssiun2 i0_ssiun2 a_sup_set_class f1_ssiun2 f2_ssiun2 p_eliun f0_ssiun2 a_sup_set_class f1_ssiun2 a_wcel i0_ssiun2 a_sup_set_class f2_ssiun2 a_wcel i0_ssiun2 a_sup_set_class f2_ssiun2 a_wcel f0_ssiun2 f1_ssiun2 a_wrex i0_ssiun2 a_sup_set_class f0_ssiun2 f1_ssiun2 f2_ssiun2 a_ciun a_wcel p_syl6ibr f0_ssiun2 a_sup_set_class f1_ssiun2 a_wcel i0_ssiun2 f2_ssiun2 f0_ssiun2 f1_ssiun2 f2_ssiun2 a_ciun p_ssrdv $.
$}

$(Subset relationship for an indexed union.  (Contributed by NM,
       26-Oct-2003.) $)

${
	$v x A B C D  $.
	$d x A  $.
	$d x C  $.
	$d x D  $.
	f0_ssiun2s $f set x $.
	f1_ssiun2s $f class A $.
	f2_ssiun2s $f class B $.
	f3_ssiun2s $f class C $.
	f4_ssiun2s $f class D $.
	e0_ssiun2s $e |- ( x = C -> B = D ) $.
	p_ssiun2s $p |- ( C e. A -> D C_ U_ x e. A B ) $= f0_ssiun2s f3_ssiun2s p_nfcv f0_ssiun2s f4_ssiun2s p_nfcv f0_ssiun2s f1_ssiun2s f2_ssiun2s p_nfiu1 f0_ssiun2s f4_ssiun2s f0_ssiun2s f1_ssiun2s f2_ssiun2s a_ciun p_nfss e0_ssiun2s f0_ssiun2s a_sup_set_class f3_ssiun2s a_wceq f2_ssiun2s f4_ssiun2s f0_ssiun2s f1_ssiun2s f2_ssiun2s a_ciun p_sseq1d f0_ssiun2s f1_ssiun2s f2_ssiun2s p_ssiun2 f2_ssiun2s f0_ssiun2s f1_ssiun2s f2_ssiun2s a_ciun a_wss f4_ssiun2s f0_ssiun2s f1_ssiun2s f2_ssiun2s a_ciun a_wss f0_ssiun2s f3_ssiun2s f1_ssiun2s p_vtoclgaf $.
$}

$(A subclass condition on the members of two indexed classes ` C ( x ) `
       and ` D ( y ) ` that implies a subclass relation on their indexed
       unions.  Generalization of Proposition 8.6 of [TakeutiZaring] p. 59.
       Compare ~ uniss2 .  (Contributed by NM, 9-Dec-2004.) $)

${
	$v x y A B C D  $.
	$d x y  $.
	$d x B  $.
	$d y C  $.
	$d x D  $.
	f0_iunss2 $f set x $.
	f1_iunss2 $f set y $.
	f2_iunss2 $f class A $.
	f3_iunss2 $f class B $.
	f4_iunss2 $f class C $.
	f5_iunss2 $f class D $.
	p_iunss2 $p |- ( A. x e. A E. y e. B C C_ D -> U_ x e. A C C_ U_ y e. B D ) $= f1_iunss2 f3_iunss2 f5_iunss2 f4_iunss2 p_ssiun f4_iunss2 f5_iunss2 a_wss f1_iunss2 f3_iunss2 a_wrex f4_iunss2 f1_iunss2 f3_iunss2 f5_iunss2 a_ciun a_wss f0_iunss2 f2_iunss2 p_ralimi f0_iunss2 f2_iunss2 f4_iunss2 f1_iunss2 f3_iunss2 f5_iunss2 a_ciun p_iunss f4_iunss2 f5_iunss2 a_wss f1_iunss2 f3_iunss2 a_wrex f0_iunss2 f2_iunss2 a_wral f4_iunss2 f1_iunss2 f3_iunss2 f5_iunss2 a_ciun a_wss f0_iunss2 f2_iunss2 a_wral f0_iunss2 f2_iunss2 f4_iunss2 a_ciun f1_iunss2 f3_iunss2 f5_iunss2 a_ciun a_wss p_sylibr $.
$}

$(The indexed union of a class abstraction.  (Contributed by NM,
       27-Dec-2004.) $)

${
	$v ph x y A  $.
	$d y A  $.
	$d x y  $.
	$d x  $.
	f0_iunab $f wff ph $.
	f1_iunab $f set x $.
	f2_iunab $f set y $.
	f3_iunab $f class A $.
	p_iunab $p |- U_ x e. A { y | ph } = { y | E. x e. A ph } $= f2_iunab f3_iunab p_nfcv f0_iunab f2_iunab p_nfab1 f1_iunab f2_iunab f3_iunab f0_iunab f2_iunab a_cab p_nfiun f0_iunab f1_iunab f3_iunab a_wrex f2_iunab p_nfab1 f2_iunab f1_iunab f3_iunab f0_iunab f2_iunab a_cab a_ciun f0_iunab f1_iunab f3_iunab a_wrex f2_iunab a_cab p_cleqf f0_iunab f2_iunab p_abid f2_iunab a_sup_set_class f0_iunab f2_iunab a_cab a_wcel f0_iunab f1_iunab f3_iunab p_rexbii f1_iunab f2_iunab a_sup_set_class f3_iunab f0_iunab f2_iunab a_cab p_eliun f0_iunab f1_iunab f3_iunab a_wrex f2_iunab p_abid f2_iunab a_sup_set_class f0_iunab f2_iunab a_cab a_wcel f1_iunab f3_iunab a_wrex f0_iunab f1_iunab f3_iunab a_wrex f2_iunab a_sup_set_class f1_iunab f3_iunab f0_iunab f2_iunab a_cab a_ciun a_wcel f2_iunab a_sup_set_class f0_iunab f1_iunab f3_iunab a_wrex f2_iunab a_cab a_wcel p_3bitr4i f1_iunab f3_iunab f0_iunab f2_iunab a_cab a_ciun f0_iunab f1_iunab f3_iunab a_wrex f2_iunab a_cab a_wceq f2_iunab a_sup_set_class f1_iunab f3_iunab f0_iunab f2_iunab a_cab a_ciun a_wcel f2_iunab a_sup_set_class f0_iunab f1_iunab f3_iunab a_wrex f2_iunab a_cab a_wcel a_wb f2_iunab p_mpgbir $.
$}

$(The indexed union of a restricted class abstraction.  (Contributed by
       NM, 3-Jan-2004.)  (Proof shortened by Mario Carneiro, 14-Nov-2016.) $)

${
	$v ph x y A B  $.
	$d y A  $.
	$d x y  $.
	$d x B  $.
	f0_iunrab $f wff ph $.
	f1_iunrab $f set x $.
	f2_iunrab $f set y $.
	f3_iunrab $f class A $.
	f4_iunrab $f class B $.
	p_iunrab $p |- U_ x e. A { y e. B | ph } = { y e. B | E. x e. A ph } $= f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab a_wa f1_iunrab f2_iunrab f3_iunrab p_iunab f0_iunrab f2_iunrab f4_iunrab a_df-rab f0_iunrab f2_iunrab f4_iunrab a_crab f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab a_wa f2_iunrab a_cab a_wceq f1_iunrab a_sup_set_class f3_iunrab a_wcel p_a1i f1_iunrab f3_iunrab f0_iunrab f2_iunrab f4_iunrab a_crab f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab a_wa f2_iunrab a_cab p_iuneq2i f0_iunrab f1_iunrab f3_iunrab a_wrex f2_iunrab f4_iunrab a_df-rab f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab f1_iunrab f3_iunrab p_r19.42v f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab a_wa f1_iunrab f3_iunrab a_wrex f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab f1_iunrab f3_iunrab a_wrex a_wa f2_iunrab p_abbii f0_iunrab f1_iunrab f3_iunrab a_wrex f2_iunrab f4_iunrab a_crab f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab f1_iunrab f3_iunrab a_wrex a_wa f2_iunrab a_cab f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab a_wa f1_iunrab f3_iunrab a_wrex f2_iunrab a_cab p_eqtr4i f1_iunrab f3_iunrab f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab a_wa f2_iunrab a_cab a_ciun f2_iunrab a_sup_set_class f4_iunrab a_wcel f0_iunrab a_wa f1_iunrab f3_iunrab a_wrex f2_iunrab a_cab f1_iunrab f3_iunrab f0_iunrab f2_iunrab f4_iunrab a_crab a_ciun f0_iunrab f1_iunrab f3_iunrab a_wrex f2_iunrab f4_iunrab a_crab p_3eqtr4i $.
$}

$(Indexed union with a class difference as its index.  (Contributed by NM,
       10-Dec-2004.) $)

${
	$v x y A B C D  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	$d x D  $.
	f0_iunxdif2 $f set x $.
	f1_iunxdif2 $f set y $.
	f2_iunxdif2 $f class A $.
	f3_iunxdif2 $f class B $.
	f4_iunxdif2 $f class C $.
	f5_iunxdif2 $f class D $.
	e0_iunxdif2 $e |- ( x = y -> C = D ) $.
	p_iunxdif2 $p |- ( A. x e. A E. y e. ( A \ B ) C C_ D -> U_ y e. ( A \ B ) D = U_ x e. A C ) $= f0_iunxdif2 f1_iunxdif2 f2_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f4_iunxdif2 f5_iunxdif2 p_iunss2 f2_iunxdif2 f3_iunxdif2 p_difss f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f2_iunxdif2 f5_iunxdif2 p_iunss1 f2_iunxdif2 f3_iunxdif2 a_cdif f2_iunxdif2 a_wss f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f5_iunxdif2 a_ciun f1_iunxdif2 f2_iunxdif2 f5_iunxdif2 a_ciun a_wss a_ax-mp e0_iunxdif2 f0_iunxdif2 f1_iunxdif2 f2_iunxdif2 f4_iunxdif2 f5_iunxdif2 p_cbviunv f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f5_iunxdif2 a_ciun f1_iunxdif2 f2_iunxdif2 f5_iunxdif2 a_ciun f0_iunxdif2 f2_iunxdif2 f4_iunxdif2 a_ciun p_sseqtr4i f4_iunxdif2 f5_iunxdif2 a_wss f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif a_wrex f0_iunxdif2 f2_iunxdif2 a_wral f0_iunxdif2 f2_iunxdif2 f4_iunxdif2 a_ciun f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f5_iunxdif2 a_ciun a_wss f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f5_iunxdif2 a_ciun f0_iunxdif2 f2_iunxdif2 f4_iunxdif2 a_ciun a_wss p_jctil f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f5_iunxdif2 a_ciun f0_iunxdif2 f2_iunxdif2 f4_iunxdif2 a_ciun p_eqss f4_iunxdif2 f5_iunxdif2 a_wss f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif a_wrex f0_iunxdif2 f2_iunxdif2 a_wral f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f5_iunxdif2 a_ciun f0_iunxdif2 f2_iunxdif2 f4_iunxdif2 a_ciun a_wss f0_iunxdif2 f2_iunxdif2 f4_iunxdif2 a_ciun f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f5_iunxdif2 a_ciun a_wss a_wa f1_iunxdif2 f2_iunxdif2 f3_iunxdif2 a_cdif f5_iunxdif2 a_ciun f0_iunxdif2 f2_iunxdif2 f4_iunxdif2 a_ciun a_wceq p_sylibr $.
$}

$(Subset theorem for an indexed intersection.  (Contributed by FL,
       15-Oct-2012.)  (Proof shortened by Mario Carneiro, 14-Oct-2016.) $)

${
	$v x A B C  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	$d x y  $.
	f0_ssiinf $f set x $.
	f1_ssiinf $f class A $.
	f2_ssiinf $f class B $.
	f3_ssiinf $f class C $.
	i0_ssiinf $f set y $.
	e0_ssiinf $e |- F/_ x C $.
	p_ssiinf $p |- ( C C_ |^|_ x e. A B <-> A. x e. A C C_ B ) $= i0_ssiinf p_vex f0_ssiinf i0_ssiinf a_sup_set_class f1_ssiinf f2_ssiinf a_cvv p_eliin i0_ssiinf a_sup_set_class a_cvv a_wcel i0_ssiinf a_sup_set_class f0_ssiinf f1_ssiinf f2_ssiinf a_ciin a_wcel i0_ssiinf a_sup_set_class f2_ssiinf a_wcel f0_ssiinf f1_ssiinf a_wral a_wb a_ax-mp i0_ssiinf a_sup_set_class f0_ssiinf f1_ssiinf f2_ssiinf a_ciin a_wcel i0_ssiinf a_sup_set_class f2_ssiinf a_wcel f0_ssiinf f1_ssiinf a_wral i0_ssiinf f3_ssiinf p_ralbii e0_ssiinf i0_ssiinf f1_ssiinf p_nfcv i0_ssiinf a_sup_set_class f2_ssiinf a_wcel i0_ssiinf f0_ssiinf f3_ssiinf f1_ssiinf p_ralcomf i0_ssiinf a_sup_set_class f0_ssiinf f1_ssiinf f2_ssiinf a_ciin a_wcel i0_ssiinf f3_ssiinf a_wral i0_ssiinf a_sup_set_class f2_ssiinf a_wcel f0_ssiinf f1_ssiinf a_wral i0_ssiinf f3_ssiinf a_wral i0_ssiinf a_sup_set_class f2_ssiinf a_wcel i0_ssiinf f3_ssiinf a_wral f0_ssiinf f1_ssiinf a_wral p_bitri i0_ssiinf f3_ssiinf f0_ssiinf f1_ssiinf f2_ssiinf a_ciin p_dfss3 i0_ssiinf f3_ssiinf f2_ssiinf p_dfss3 f3_ssiinf f2_ssiinf a_wss i0_ssiinf a_sup_set_class f2_ssiinf a_wcel i0_ssiinf f3_ssiinf a_wral f0_ssiinf f1_ssiinf p_ralbii i0_ssiinf a_sup_set_class f0_ssiinf f1_ssiinf f2_ssiinf a_ciin a_wcel i0_ssiinf f3_ssiinf a_wral i0_ssiinf a_sup_set_class f2_ssiinf a_wcel i0_ssiinf f3_ssiinf a_wral f0_ssiinf f1_ssiinf a_wral f3_ssiinf f0_ssiinf f1_ssiinf f2_ssiinf a_ciin a_wss f3_ssiinf f2_ssiinf a_wss f0_ssiinf f1_ssiinf a_wral p_3bitr4i $.
$}

$(Subset theorem for an indexed intersection.  (Contributed by NM,
       15-Oct-2003.) $)

${
	$v x A B C  $.
	$d x C  $.
	f0_ssiin $f set x $.
	f1_ssiin $f class A $.
	f2_ssiin $f class B $.
	f3_ssiin $f class C $.
	p_ssiin $p |- ( C C_ |^|_ x e. A B <-> A. x e. A C C_ B ) $= f0_ssiin f3_ssiin p_nfcv f0_ssiin f1_ssiin f2_ssiin f3_ssiin p_ssiinf $.
$}

$(Subset implication for an indexed intersection.  (Contributed by NM,
       15-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B C  $.
	$d x y C  $.
	$d y A  $.
	$d y B  $.
	f0_iinss $f set x $.
	f1_iinss $f class A $.
	f2_iinss $f class B $.
	f3_iinss $f class C $.
	i0_iinss $f set y $.
	p_iinss $p |- ( E. x e. A B C_ C -> |^|_ x e. A B C_ C ) $= i0_iinss p_vex f0_iinss i0_iinss a_sup_set_class f1_iinss f2_iinss a_cvv p_eliin i0_iinss a_sup_set_class a_cvv a_wcel i0_iinss a_sup_set_class f0_iinss f1_iinss f2_iinss a_ciin a_wcel i0_iinss a_sup_set_class f2_iinss a_wcel f0_iinss f1_iinss a_wral a_wb a_ax-mp f2_iinss f3_iinss i0_iinss a_sup_set_class p_ssel f2_iinss f3_iinss a_wss i0_iinss a_sup_set_class f2_iinss a_wcel i0_iinss a_sup_set_class f3_iinss a_wcel a_wi f0_iinss f1_iinss p_reximi i0_iinss a_sup_set_class f2_iinss a_wcel i0_iinss a_sup_set_class f3_iinss a_wcel f0_iinss f1_iinss p_r19.36av f2_iinss f3_iinss a_wss f0_iinss f1_iinss a_wrex i0_iinss a_sup_set_class f2_iinss a_wcel i0_iinss a_sup_set_class f3_iinss a_wcel a_wi f0_iinss f1_iinss a_wrex i0_iinss a_sup_set_class f2_iinss a_wcel f0_iinss f1_iinss a_wral i0_iinss a_sup_set_class f3_iinss a_wcel a_wi p_syl i0_iinss a_sup_set_class f0_iinss f1_iinss f2_iinss a_ciin a_wcel i0_iinss a_sup_set_class f2_iinss a_wcel f0_iinss f1_iinss a_wral f2_iinss f3_iinss a_wss f0_iinss f1_iinss a_wrex i0_iinss a_sup_set_class f3_iinss a_wcel p_syl5bi f2_iinss f3_iinss a_wss f0_iinss f1_iinss a_wrex i0_iinss f0_iinss f1_iinss f2_iinss a_ciin f3_iinss p_ssrdv $.
$}

$(An indexed intersection is included in any of its members.  (Contributed
       by FL, 15-Oct-2012.) $)

${
	$v x A B  $.
	$d A y  $.
	$d B y  $.
	$d x y  $.
	f0_iinss2 $f set x $.
	f1_iinss2 $f class A $.
	f2_iinss2 $f class B $.
	i0_iinss2 $f set y $.
	p_iinss2 $p |- ( x e. A -> |^|_ x e. A B C_ B ) $= i0_iinss2 p_vex f0_iinss2 i0_iinss2 a_sup_set_class f1_iinss2 f2_iinss2 a_cvv p_eliin i0_iinss2 a_sup_set_class a_cvv a_wcel i0_iinss2 a_sup_set_class f0_iinss2 f1_iinss2 f2_iinss2 a_ciin a_wcel i0_iinss2 a_sup_set_class f2_iinss2 a_wcel f0_iinss2 f1_iinss2 a_wral a_wb a_ax-mp i0_iinss2 a_sup_set_class f2_iinss2 a_wcel f0_iinss2 f1_iinss2 p_rsp i0_iinss2 a_sup_set_class f0_iinss2 f1_iinss2 f2_iinss2 a_ciin a_wcel i0_iinss2 a_sup_set_class f2_iinss2 a_wcel f0_iinss2 f1_iinss2 a_wral f0_iinss2 a_sup_set_class f1_iinss2 a_wcel i0_iinss2 a_sup_set_class f2_iinss2 a_wcel a_wi p_sylbi i0_iinss2 a_sup_set_class f0_iinss2 f1_iinss2 f2_iinss2 a_ciin a_wcel f0_iinss2 a_sup_set_class f1_iinss2 a_wcel i0_iinss2 a_sup_set_class f2_iinss2 a_wcel p_com12 f0_iinss2 a_sup_set_class f1_iinss2 a_wcel i0_iinss2 f0_iinss2 f1_iinss2 f2_iinss2 a_ciin f2_iinss2 p_ssrdv $.
$}

$(Class union in terms of indexed union.  Definition in [Stoll] p. 43.
       (Contributed by NM, 28-Jun-1998.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_uniiun $f set x $.
	f1_uniiun $f class A $.
	i0_uniiun $f set y $.
	p_uniiun $p |- U. A = U_ x e. A x $= i0_uniiun f0_uniiun f1_uniiun p_dfuni2 f0_uniiun i0_uniiun f1_uniiun f0_uniiun a_sup_set_class a_df-iun f1_uniiun a_cuni i0_uniiun a_sup_set_class f0_uniiun a_sup_set_class a_wcel f0_uniiun f1_uniiun a_wrex i0_uniiun a_cab f0_uniiun f1_uniiun f0_uniiun a_sup_set_class a_ciun p_eqtr4i $.
$}

$(Class intersection in terms of indexed intersection.  Definition in
       [Stoll] p. 44.  (Contributed by NM, 28-Jun-1998.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_intiin $f set x $.
	f1_intiin $f class A $.
	i0_intiin $f set y $.
	p_intiin $p |- |^| A = |^|_ x e. A x $= i0_intiin f0_intiin f1_intiin p_dfint2 f0_intiin i0_intiin f1_intiin f0_intiin a_sup_set_class a_df-iin f1_intiin a_cint i0_intiin a_sup_set_class f0_intiin a_sup_set_class a_wcel f0_intiin f1_intiin a_wral i0_intiin a_cab f0_intiin f1_intiin f0_intiin a_sup_set_class a_ciin p_eqtr4i $.
$}

$(An indexed union of singletons recovers the index set.  (Contributed by
       NM, 6-Sep-2005.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_iunid $f set x $.
	f1_iunid $f class A $.
	i0_iunid $f set y $.
	p_iunid $p |- U_ x e. A { x } = A $= i0_iunid f0_iunid a_sup_set_class a_df-sn i0_iunid f0_iunid p_equcom i0_iunid a_sup_set_class f0_iunid a_sup_set_class a_wceq f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq i0_iunid p_abbii f0_iunid a_sup_set_class a_csn i0_iunid a_sup_set_class f0_iunid a_sup_set_class a_wceq i0_iunid a_cab f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq i0_iunid a_cab p_eqtri f0_iunid a_sup_set_class a_csn f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq i0_iunid a_cab a_wceq f0_iunid a_sup_set_class f1_iunid a_wcel p_a1i f0_iunid f1_iunid f0_iunid a_sup_set_class a_csn f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq i0_iunid a_cab p_iuneq2i f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq f0_iunid i0_iunid f1_iunid p_iunab f0_iunid i0_iunid a_sup_set_class f1_iunid p_risset i0_iunid a_sup_set_class f1_iunid a_wcel f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq f0_iunid f1_iunid a_wrex i0_iunid p_abbii i0_iunid f1_iunid p_abid2 f0_iunid f1_iunid f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq i0_iunid a_cab a_ciun f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq f0_iunid f1_iunid a_wrex i0_iunid a_cab i0_iunid a_sup_set_class f1_iunid a_wcel i0_iunid a_cab f1_iunid p_3eqtr2i f0_iunid f1_iunid f0_iunid a_sup_set_class a_csn a_ciun f0_iunid f1_iunid f0_iunid a_sup_set_class i0_iunid a_sup_set_class a_wceq i0_iunid a_cab a_ciun f1_iunid p_eqtri $.
$}

$(An indexed union of the empty set is empty.  (Contributed by NM,
       26-Mar-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A  $.
	$d x y  $.
	$d y A  $.
	f0_iun0 $f set x $.
	f1_iun0 $f class A $.
	i0_iun0 $f set y $.
	p_iun0 $p |- U_ x e. A (/) = (/) $= i0_iun0 a_sup_set_class p_noel i0_iun0 a_sup_set_class a_c0 a_wcel a_wn f0_iun0 a_sup_set_class f1_iun0 a_wcel p_a1i i0_iun0 a_sup_set_class a_c0 a_wcel f0_iun0 f1_iun0 p_nrex f0_iun0 i0_iun0 a_sup_set_class f1_iun0 a_c0 p_eliun i0_iun0 a_sup_set_class f0_iun0 f1_iun0 a_c0 a_ciun a_wcel i0_iun0 a_sup_set_class a_c0 a_wcel f0_iun0 f1_iun0 a_wrex p_mtbir i0_iun0 a_sup_set_class p_noel i0_iun0 a_sup_set_class f0_iun0 f1_iun0 a_c0 a_ciun a_wcel i0_iun0 a_sup_set_class a_c0 a_wcel p_2false i0_iun0 f0_iun0 f1_iun0 a_c0 a_ciun a_c0 p_eqriv $.
$}

$(An empty indexed union is empty.  (Contributed by NM, 4-Dec-2004.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A  $.
	$d x y  $.
	$d y A  $.
	f0_0iun $f set x $.
	f1_0iun $f class A $.
	i0_0iun $f set y $.
	p_0iun $p |- U_ x e. (/) A = (/) $= i0_0iun a_sup_set_class f1_0iun a_wcel f0_0iun p_rex0 f0_0iun i0_0iun a_sup_set_class a_c0 f1_0iun p_eliun i0_0iun a_sup_set_class f0_0iun a_c0 f1_0iun a_ciun a_wcel i0_0iun a_sup_set_class f1_0iun a_wcel f0_0iun a_c0 a_wrex p_mtbir i0_0iun a_sup_set_class p_noel i0_0iun a_sup_set_class f0_0iun a_c0 f1_0iun a_ciun a_wcel i0_0iun a_sup_set_class a_c0 a_wcel p_2false i0_0iun f0_0iun a_c0 f1_0iun a_ciun a_c0 p_eqriv $.
$}

$(An empty indexed intersection is the universal class.  (Contributed by
       NM, 20-Oct-2005.) $)

${
	$v x A  $.
	$d x y  $.
	$d y A  $.
	f0_0iin $f set x $.
	f1_0iin $f class A $.
	i0_0iin $f set y $.
	p_0iin $p |- |^|_ x e. (/) A = _V $= f0_0iin i0_0iin a_c0 f1_0iin a_df-iin i0_0iin p_vex i0_0iin a_sup_set_class f1_0iin a_wcel f0_0iin p_ral0 i0_0iin a_sup_set_class a_cvv a_wcel i0_0iin a_sup_set_class f1_0iin a_wcel f0_0iin a_c0 a_wral p_2th i0_0iin a_sup_set_class f1_0iin a_wcel f0_0iin a_c0 a_wral i0_0iin a_cvv p_abbi2i f0_0iin a_c0 f1_0iin a_ciin i0_0iin a_sup_set_class f1_0iin a_wcel f0_0iin a_c0 a_wral i0_0iin a_cab a_cvv p_eqtr4i $.
$}

$(Indexed intersection with a universal index class.  When ` A ` doesn't
       depend on ` x ` , this evaluates to ` A ` by ~ 19.3 and ~ abid2 .  When
       ` A = x ` , this evaluates to ` (/) ` by ~ intiin and ~ intv .
       (Contributed by NM, 11-Sep-2008.) $)

${
	$v x y A  $.
	$d x y  $.
	$d y A  $.
	f0_viin $f set x $.
	f1_viin $f set y $.
	f2_viin $f class A $.
	p_viin $p |- |^|_ x e. _V A = { y | A. x y e. A } $= f0_viin f1_viin a_cvv f2_viin a_df-iin f1_viin a_sup_set_class f2_viin a_wcel f0_viin p_ralv f1_viin a_sup_set_class f2_viin a_wcel f0_viin a_cvv a_wral f1_viin a_sup_set_class f2_viin a_wcel f0_viin a_wal f1_viin p_abbii f0_viin a_cvv f2_viin a_ciin f1_viin a_sup_set_class f2_viin a_wcel f0_viin a_cvv a_wral f1_viin a_cab f1_viin a_sup_set_class f2_viin a_wcel f0_viin a_wal f1_viin a_cab p_eqtri $.
$}

$(There is a non-empty class in an indexed collection ` B ( x ) ` iff the
       indexed union of them is non-empty.  (Contributed by NM, 15-Oct-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d y B  $.
	f0_iunn0 $f set x $.
	f1_iunn0 $f class A $.
	f2_iunn0 $f class B $.
	i0_iunn0 $f set y $.
	p_iunn0 $p |- ( E. x e. A B =/= (/) <-> U_ x e. A B =/= (/) ) $= i0_iunn0 a_sup_set_class f2_iunn0 a_wcel f0_iunn0 i0_iunn0 f1_iunn0 p_rexcom4 f0_iunn0 i0_iunn0 a_sup_set_class f1_iunn0 f2_iunn0 p_eliun i0_iunn0 a_sup_set_class f0_iunn0 f1_iunn0 f2_iunn0 a_ciun a_wcel i0_iunn0 a_sup_set_class f2_iunn0 a_wcel f0_iunn0 f1_iunn0 a_wrex i0_iunn0 p_exbii i0_iunn0 a_sup_set_class f2_iunn0 a_wcel i0_iunn0 a_wex f0_iunn0 f1_iunn0 a_wrex i0_iunn0 a_sup_set_class f2_iunn0 a_wcel f0_iunn0 f1_iunn0 a_wrex i0_iunn0 a_wex i0_iunn0 a_sup_set_class f0_iunn0 f1_iunn0 f2_iunn0 a_ciun a_wcel i0_iunn0 a_wex p_bitr4i i0_iunn0 f2_iunn0 p_n0 f2_iunn0 a_c0 a_wne i0_iunn0 a_sup_set_class f2_iunn0 a_wcel i0_iunn0 a_wex f0_iunn0 f1_iunn0 p_rexbii i0_iunn0 f0_iunn0 f1_iunn0 f2_iunn0 a_ciun p_n0 i0_iunn0 a_sup_set_class f2_iunn0 a_wcel i0_iunn0 a_wex f0_iunn0 f1_iunn0 a_wrex i0_iunn0 a_sup_set_class f0_iunn0 f1_iunn0 f2_iunn0 a_ciun a_wcel i0_iunn0 a_wex f2_iunn0 a_c0 a_wne f0_iunn0 f1_iunn0 a_wrex f0_iunn0 f1_iunn0 f2_iunn0 a_ciun a_c0 a_wne p_3bitr4i $.
$}

$(Indexed intersection of a class builder.  (Contributed by NM,
       6-Dec-2011.) $)

${
	$v ph x y A  $.
	$d y A  $.
	$d x y  $.
	f0_iinab $f wff ph $.
	f1_iinab $f set x $.
	f2_iinab $f set y $.
	f3_iinab $f class A $.
	p_iinab $p |- |^|_ x e. A { y | ph } = { y | A. x e. A ph } $= f2_iinab f3_iinab p_nfcv f0_iinab f2_iinab p_nfab1 f1_iinab f2_iinab f3_iinab f0_iinab f2_iinab a_cab p_nfiin f0_iinab f1_iinab f3_iinab a_wral f2_iinab p_nfab1 f2_iinab f1_iinab f3_iinab f0_iinab f2_iinab a_cab a_ciin f0_iinab f1_iinab f3_iinab a_wral f2_iinab a_cab p_cleqf f0_iinab f2_iinab p_abid f2_iinab a_sup_set_class f0_iinab f2_iinab a_cab a_wcel f0_iinab f1_iinab f3_iinab p_ralbii f2_iinab p_vex f1_iinab f2_iinab a_sup_set_class f3_iinab f0_iinab f2_iinab a_cab a_cvv p_eliin f2_iinab a_sup_set_class a_cvv a_wcel f2_iinab a_sup_set_class f1_iinab f3_iinab f0_iinab f2_iinab a_cab a_ciin a_wcel f2_iinab a_sup_set_class f0_iinab f2_iinab a_cab a_wcel f1_iinab f3_iinab a_wral a_wb a_ax-mp f0_iinab f1_iinab f3_iinab a_wral f2_iinab p_abid f2_iinab a_sup_set_class f0_iinab f2_iinab a_cab a_wcel f1_iinab f3_iinab a_wral f0_iinab f1_iinab f3_iinab a_wral f2_iinab a_sup_set_class f1_iinab f3_iinab f0_iinab f2_iinab a_cab a_ciin a_wcel f2_iinab a_sup_set_class f0_iinab f1_iinab f3_iinab a_wral f2_iinab a_cab a_wcel p_3bitr4i f1_iinab f3_iinab f0_iinab f2_iinab a_cab a_ciin f0_iinab f1_iinab f3_iinab a_wral f2_iinab a_cab a_wceq f2_iinab a_sup_set_class f1_iinab f3_iinab f0_iinab f2_iinab a_cab a_ciin a_wcel f2_iinab a_sup_set_class f0_iinab f1_iinab f3_iinab a_wral f2_iinab a_cab a_wcel a_wb f2_iinab p_mpgbir $.
$}

$(Indexed intersection of a restricted class builder.  (Contributed by NM,
       6-Dec-2011.) $)

${
	$v ph x y A B  $.
	$d y A  $.
	$d x y  $.
	$d x A  $.
	$d x B  $.
	f0_iinrab $f wff ph $.
	f1_iinrab $f set x $.
	f2_iinrab $f set y $.
	f3_iinrab $f class A $.
	f4_iinrab $f class B $.
	p_iinrab $p |- ( A =/= (/) -> |^|_ x e. A { y e. B | ph } = { y e. B | A. x e. A ph } ) $= f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab f1_iinrab f3_iinrab p_r19.28zv f3_iinrab a_c0 a_wne f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab a_wa f1_iinrab f3_iinrab a_wral f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab f1_iinrab f3_iinrab a_wral a_wa f2_iinrab p_abbidv f0_iinrab f2_iinrab f4_iinrab a_df-rab f0_iinrab f2_iinrab f4_iinrab a_crab f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab a_wa f2_iinrab a_cab a_wceq f1_iinrab a_sup_set_class f3_iinrab a_wcel p_a1i f1_iinrab f3_iinrab f0_iinrab f2_iinrab f4_iinrab a_crab f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab a_wa f2_iinrab a_cab p_iineq2i f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab a_wa f1_iinrab f2_iinrab f3_iinrab p_iinab f1_iinrab f3_iinrab f0_iinrab f2_iinrab f4_iinrab a_crab a_ciin f1_iinrab f3_iinrab f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab a_wa f2_iinrab a_cab a_ciin f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab a_wa f1_iinrab f3_iinrab a_wral f2_iinrab a_cab p_eqtri f0_iinrab f1_iinrab f3_iinrab a_wral f2_iinrab f4_iinrab a_df-rab f3_iinrab a_c0 a_wne f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab a_wa f1_iinrab f3_iinrab a_wral f2_iinrab a_cab f2_iinrab a_sup_set_class f4_iinrab a_wcel f0_iinrab f1_iinrab f3_iinrab a_wral a_wa f2_iinrab a_cab f1_iinrab f3_iinrab f0_iinrab f2_iinrab f4_iinrab a_crab a_ciin f0_iinrab f1_iinrab f3_iinrab a_wral f2_iinrab f4_iinrab a_crab p_3eqtr4g $.
$}

$(Indexed intersection of a restricted class builder.  (Contributed by NM,
       6-Dec-2011.) $)

${
	$v ph x y A B  $.
	$d y A  $.
	$d x y  $.
	$d x A  $.
	$d x B  $.
	$d y B  $.
	f0_iinrab2 $f wff ph $.
	f1_iinrab2 $f set x $.
	f2_iinrab2 $f set y $.
	f3_iinrab2 $f class A $.
	f4_iinrab2 $f class B $.
	p_iinrab2 $p |- ( |^|_ x e. A { y e. B | ph } i^i B ) = { y e. B | A. x e. A ph } $= f1_iinrab2 f3_iinrab2 a_c0 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab p_iineq1 f1_iinrab2 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab p_0iin f3_iinrab2 a_c0 a_wceq f1_iinrab2 f3_iinrab2 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab a_ciin f1_iinrab2 a_c0 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab a_ciin a_cvv p_syl6eq f3_iinrab2 a_c0 a_wceq f1_iinrab2 f3_iinrab2 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab a_ciin a_cvv f4_iinrab2 p_ineq1d a_cvv f4_iinrab2 p_incom f4_iinrab2 p_inv1 a_cvv f4_iinrab2 a_cin f4_iinrab2 a_cvv a_cin f4_iinrab2 p_eqtri f3_iinrab2 a_c0 a_wceq f1_iinrab2 f3_iinrab2 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab a_ciin f4_iinrab2 a_cin a_cvv f4_iinrab2 a_cin f4_iinrab2 p_syl6eq f0_iinrab2 f2_iinrab2 f4_iinrab2 a_wral f1_iinrab2 f3_iinrab2 p_rzal f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 p_rabid2 f0_iinrab2 f2_iinrab2 f1_iinrab2 f4_iinrab2 f3_iinrab2 p_ralcom f4_iinrab2 f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab a_wceq f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_wral f0_iinrab2 f2_iinrab2 f4_iinrab2 a_wral f1_iinrab2 f3_iinrab2 a_wral p_bitr2i f3_iinrab2 a_c0 a_wceq f0_iinrab2 f2_iinrab2 f4_iinrab2 a_wral f1_iinrab2 f3_iinrab2 a_wral f4_iinrab2 f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab a_wceq p_sylib f3_iinrab2 a_c0 a_wceq f1_iinrab2 f3_iinrab2 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab a_ciin f4_iinrab2 a_cin f4_iinrab2 f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab p_eqtrd f0_iinrab2 f1_iinrab2 f2_iinrab2 f3_iinrab2 f4_iinrab2 p_iinrab f3_iinrab2 a_c0 a_wne f1_iinrab2 f3_iinrab2 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab a_ciin f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab f4_iinrab2 p_ineq1d f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 p_ssrab2 f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab f4_iinrab2 p_dfss f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab f4_iinrab2 a_wss f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab f4_iinrab2 a_cin a_wceq p_mpbi f3_iinrab2 a_c0 a_wne f1_iinrab2 f3_iinrab2 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab a_ciin f4_iinrab2 a_cin f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab f4_iinrab2 a_cin f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab p_syl6eqr f1_iinrab2 f3_iinrab2 f0_iinrab2 f2_iinrab2 f4_iinrab2 a_crab a_ciin f4_iinrab2 a_cin f0_iinrab2 f1_iinrab2 f3_iinrab2 a_wral f2_iinrab2 f4_iinrab2 a_crab a_wceq f3_iinrab2 a_c0 p_pm2.61ine $.
$}

$(Indexed union of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by NM, 26-Mar-2004.) $)

${
	$v x A B C  $.
	$d y A  $.
	$d x y B  $.
	$d y C  $.
	f0_iunin2 $f set x $.
	f1_iunin2 $f class A $.
	f2_iunin2 $f class B $.
	f3_iunin2 $f class C $.
	i0_iunin2 $f set y $.
	p_iunin2 $p |- U_ x e. A ( B i^i C ) = ( B i^i U_ x e. A C ) $= i0_iunin2 a_sup_set_class f2_iunin2 a_wcel i0_iunin2 a_sup_set_class f3_iunin2 a_wcel f0_iunin2 f1_iunin2 p_r19.42v i0_iunin2 a_sup_set_class f2_iunin2 f3_iunin2 p_elin i0_iunin2 a_sup_set_class f2_iunin2 f3_iunin2 a_cin a_wcel i0_iunin2 a_sup_set_class f2_iunin2 a_wcel i0_iunin2 a_sup_set_class f3_iunin2 a_wcel a_wa f0_iunin2 f1_iunin2 p_rexbii f0_iunin2 i0_iunin2 a_sup_set_class f1_iunin2 f3_iunin2 p_eliun i0_iunin2 a_sup_set_class f0_iunin2 f1_iunin2 f3_iunin2 a_ciun a_wcel i0_iunin2 a_sup_set_class f3_iunin2 a_wcel f0_iunin2 f1_iunin2 a_wrex i0_iunin2 a_sup_set_class f2_iunin2 a_wcel p_anbi2i i0_iunin2 a_sup_set_class f2_iunin2 a_wcel i0_iunin2 a_sup_set_class f3_iunin2 a_wcel a_wa f0_iunin2 f1_iunin2 a_wrex i0_iunin2 a_sup_set_class f2_iunin2 a_wcel i0_iunin2 a_sup_set_class f3_iunin2 a_wcel f0_iunin2 f1_iunin2 a_wrex a_wa i0_iunin2 a_sup_set_class f2_iunin2 f3_iunin2 a_cin a_wcel f0_iunin2 f1_iunin2 a_wrex i0_iunin2 a_sup_set_class f2_iunin2 a_wcel i0_iunin2 a_sup_set_class f0_iunin2 f1_iunin2 f3_iunin2 a_ciun a_wcel a_wa p_3bitr4i f0_iunin2 i0_iunin2 a_sup_set_class f1_iunin2 f2_iunin2 f3_iunin2 a_cin p_eliun i0_iunin2 a_sup_set_class f2_iunin2 f0_iunin2 f1_iunin2 f3_iunin2 a_ciun p_elin i0_iunin2 a_sup_set_class f2_iunin2 f3_iunin2 a_cin a_wcel f0_iunin2 f1_iunin2 a_wrex i0_iunin2 a_sup_set_class f2_iunin2 a_wcel i0_iunin2 a_sup_set_class f0_iunin2 f1_iunin2 f3_iunin2 a_ciun a_wcel a_wa i0_iunin2 a_sup_set_class f0_iunin2 f1_iunin2 f2_iunin2 f3_iunin2 a_cin a_ciun a_wcel i0_iunin2 a_sup_set_class f2_iunin2 f0_iunin2 f1_iunin2 f3_iunin2 a_ciun a_cin a_wcel p_3bitr4i i0_iunin2 f0_iunin2 f1_iunin2 f2_iunin2 f3_iunin2 a_cin a_ciun f2_iunin2 f0_iunin2 f1_iunin2 f3_iunin2 a_ciun a_cin p_eqriv $.
$}

$(Indexed union of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 30-Aug-2015.) $)

${
	$v x A B C  $.
	$d A  $.
	$d x B  $.
	$d C  $.
	f0_iunin1 $f set x $.
	f1_iunin1 $f class A $.
	f2_iunin1 $f class B $.
	f3_iunin1 $f class C $.
	p_iunin1 $p |- U_ x e. A ( C i^i B ) = ( U_ x e. A C i^i B ) $= f0_iunin1 f1_iunin1 f2_iunin1 f3_iunin1 p_iunin2 f3_iunin1 f2_iunin1 p_incom f3_iunin1 f2_iunin1 a_cin f2_iunin1 f3_iunin1 a_cin a_wceq f0_iunin1 a_sup_set_class f1_iunin1 a_wcel p_a1i f0_iunin1 f1_iunin1 f3_iunin1 f2_iunin1 a_cin f2_iunin1 f3_iunin1 a_cin p_iuneq2i f0_iunin1 f1_iunin1 f3_iunin1 a_ciun f2_iunin1 p_incom f0_iunin1 f1_iunin1 f2_iunin1 f3_iunin1 a_cin a_ciun f2_iunin1 f0_iunin1 f1_iunin1 f3_iunin1 a_ciun a_cin f0_iunin1 f1_iunin1 f3_iunin1 f2_iunin1 a_cin a_ciun f0_iunin1 f1_iunin1 f3_iunin1 a_ciun f2_iunin1 a_cin p_3eqtr4i $.
$}

$(Indexed intersection of union.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by NM, 19-Aug-2004.) $)

${
	$v x A B C  $.
	$d y A  $.
	$d x y B  $.
	$d y C  $.
	f0_iinun2 $f set x $.
	f1_iinun2 $f class A $.
	f2_iinun2 $f class B $.
	f3_iinun2 $f class C $.
	i0_iinun2 $f set y $.
	p_iinun2 $p |- |^|_ x e. A ( B u. C ) = ( B u. |^|_ x e. A C ) $= i0_iinun2 a_sup_set_class f2_iinun2 a_wcel i0_iinun2 a_sup_set_class f3_iinun2 a_wcel f0_iinun2 f1_iinun2 p_r19.32v i0_iinun2 a_sup_set_class f2_iinun2 f3_iinun2 p_elun i0_iinun2 a_sup_set_class f2_iinun2 f3_iinun2 a_cun a_wcel i0_iinun2 a_sup_set_class f2_iinun2 a_wcel i0_iinun2 a_sup_set_class f3_iinun2 a_wcel a_wo f0_iinun2 f1_iinun2 p_ralbii i0_iinun2 p_vex f0_iinun2 i0_iinun2 a_sup_set_class f1_iinun2 f3_iinun2 a_cvv p_eliin i0_iinun2 a_sup_set_class a_cvv a_wcel i0_iinun2 a_sup_set_class f0_iinun2 f1_iinun2 f3_iinun2 a_ciin a_wcel i0_iinun2 a_sup_set_class f3_iinun2 a_wcel f0_iinun2 f1_iinun2 a_wral a_wb a_ax-mp i0_iinun2 a_sup_set_class f0_iinun2 f1_iinun2 f3_iinun2 a_ciin a_wcel i0_iinun2 a_sup_set_class f3_iinun2 a_wcel f0_iinun2 f1_iinun2 a_wral i0_iinun2 a_sup_set_class f2_iinun2 a_wcel p_orbi2i i0_iinun2 a_sup_set_class f2_iinun2 a_wcel i0_iinun2 a_sup_set_class f3_iinun2 a_wcel a_wo f0_iinun2 f1_iinun2 a_wral i0_iinun2 a_sup_set_class f2_iinun2 a_wcel i0_iinun2 a_sup_set_class f3_iinun2 a_wcel f0_iinun2 f1_iinun2 a_wral a_wo i0_iinun2 a_sup_set_class f2_iinun2 f3_iinun2 a_cun a_wcel f0_iinun2 f1_iinun2 a_wral i0_iinun2 a_sup_set_class f2_iinun2 a_wcel i0_iinun2 a_sup_set_class f0_iinun2 f1_iinun2 f3_iinun2 a_ciin a_wcel a_wo p_3bitr4i i0_iinun2 p_vex f0_iinun2 i0_iinun2 a_sup_set_class f1_iinun2 f2_iinun2 f3_iinun2 a_cun a_cvv p_eliin i0_iinun2 a_sup_set_class a_cvv a_wcel i0_iinun2 a_sup_set_class f0_iinun2 f1_iinun2 f2_iinun2 f3_iinun2 a_cun a_ciin a_wcel i0_iinun2 a_sup_set_class f2_iinun2 f3_iinun2 a_cun a_wcel f0_iinun2 f1_iinun2 a_wral a_wb a_ax-mp i0_iinun2 a_sup_set_class f2_iinun2 f0_iinun2 f1_iinun2 f3_iinun2 a_ciin p_elun i0_iinun2 a_sup_set_class f2_iinun2 f3_iinun2 a_cun a_wcel f0_iinun2 f1_iinun2 a_wral i0_iinun2 a_sup_set_class f2_iinun2 a_wcel i0_iinun2 a_sup_set_class f0_iinun2 f1_iinun2 f3_iinun2 a_ciin a_wcel a_wo i0_iinun2 a_sup_set_class f0_iinun2 f1_iinun2 f2_iinun2 f3_iinun2 a_cun a_ciin a_wcel i0_iinun2 a_sup_set_class f2_iinun2 f0_iinun2 f1_iinun2 f3_iinun2 a_ciin a_cun a_wcel p_3bitr4i i0_iinun2 f0_iinun2 f1_iinun2 f2_iinun2 f3_iinun2 a_cun a_ciin f2_iinun2 f0_iinun2 f1_iinun2 f3_iinun2 a_ciin a_cun p_eqriv $.
$}

$(Indexed union of class difference.  Generalization of half of theorem
       "De Morgan's laws" in [Enderton] p. 31.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by NM, 19-Aug-2004.) $)

${
	$v x A B C  $.
	$d y A  $.
	$d x y B  $.
	$d y C  $.
	f0_iundif2 $f set x $.
	f1_iundif2 $f class A $.
	f2_iundif2 $f class B $.
	f3_iundif2 $f class C $.
	i0_iundif2 $f set y $.
	p_iundif2 $p |- U_ x e. A ( B \ C ) = ( B \ |^|_ x e. A C ) $= i0_iundif2 a_sup_set_class f2_iundif2 f3_iundif2 p_eldif i0_iundif2 a_sup_set_class f2_iundif2 f3_iundif2 a_cdif a_wcel i0_iundif2 a_sup_set_class f2_iundif2 a_wcel i0_iundif2 a_sup_set_class f3_iundif2 a_wcel a_wn a_wa f0_iundif2 f1_iundif2 p_rexbii i0_iundif2 a_sup_set_class f2_iundif2 a_wcel i0_iundif2 a_sup_set_class f3_iundif2 a_wcel a_wn f0_iundif2 f1_iundif2 p_r19.42v i0_iundif2 a_sup_set_class f3_iundif2 a_wcel f0_iundif2 f1_iundif2 p_rexnal i0_iundif2 p_vex f0_iundif2 i0_iundif2 a_sup_set_class f1_iundif2 f3_iundif2 a_cvv p_eliin i0_iundif2 a_sup_set_class a_cvv a_wcel i0_iundif2 a_sup_set_class f0_iundif2 f1_iundif2 f3_iundif2 a_ciin a_wcel i0_iundif2 a_sup_set_class f3_iundif2 a_wcel f0_iundif2 f1_iundif2 a_wral a_wb a_ax-mp i0_iundif2 a_sup_set_class f3_iundif2 a_wcel a_wn f0_iundif2 f1_iundif2 a_wrex i0_iundif2 a_sup_set_class f3_iundif2 a_wcel f0_iundif2 f1_iundif2 a_wral i0_iundif2 a_sup_set_class f0_iundif2 f1_iundif2 f3_iundif2 a_ciin a_wcel p_xchbinxr i0_iundif2 a_sup_set_class f3_iundif2 a_wcel a_wn f0_iundif2 f1_iundif2 a_wrex i0_iundif2 a_sup_set_class f0_iundif2 f1_iundif2 f3_iundif2 a_ciin a_wcel a_wn i0_iundif2 a_sup_set_class f2_iundif2 a_wcel p_anbi2i i0_iundif2 a_sup_set_class f2_iundif2 f3_iundif2 a_cdif a_wcel f0_iundif2 f1_iundif2 a_wrex i0_iundif2 a_sup_set_class f2_iundif2 a_wcel i0_iundif2 a_sup_set_class f3_iundif2 a_wcel a_wn a_wa f0_iundif2 f1_iundif2 a_wrex i0_iundif2 a_sup_set_class f2_iundif2 a_wcel i0_iundif2 a_sup_set_class f3_iundif2 a_wcel a_wn f0_iundif2 f1_iundif2 a_wrex a_wa i0_iundif2 a_sup_set_class f2_iundif2 a_wcel i0_iundif2 a_sup_set_class f0_iundif2 f1_iundif2 f3_iundif2 a_ciin a_wcel a_wn a_wa p_3bitri f0_iundif2 i0_iundif2 a_sup_set_class f1_iundif2 f2_iundif2 f3_iundif2 a_cdif p_eliun i0_iundif2 a_sup_set_class f2_iundif2 f0_iundif2 f1_iundif2 f3_iundif2 a_ciin p_eldif i0_iundif2 a_sup_set_class f2_iundif2 f3_iundif2 a_cdif a_wcel f0_iundif2 f1_iundif2 a_wrex i0_iundif2 a_sup_set_class f2_iundif2 a_wcel i0_iundif2 a_sup_set_class f0_iundif2 f1_iundif2 f3_iundif2 a_ciin a_wcel a_wn a_wa i0_iundif2 a_sup_set_class f0_iundif2 f1_iundif2 f2_iundif2 f3_iundif2 a_cdif a_ciun a_wcel i0_iundif2 a_sup_set_class f2_iundif2 f0_iundif2 f1_iundif2 f3_iundif2 a_ciin a_cdif a_wcel p_3bitr4i i0_iundif2 f0_iundif2 f1_iundif2 f2_iundif2 f3_iundif2 a_cdif a_ciun f2_iundif2 f0_iundif2 f1_iundif2 f3_iundif2 a_ciin a_cdif p_eqriv $.
$}

$(Rearrange indexed unions over intersection.  (Contributed by NM,
       18-Dec-2008.) $)

${
	$v x y A B C D  $.
	$d x B  $.
	$d y C  $.
	$d x D  $.
	$d x y  $.
	f0_2iunin $f set x $.
	f1_2iunin $f set y $.
	f2_2iunin $f class A $.
	f3_2iunin $f class B $.
	f4_2iunin $f class C $.
	f5_2iunin $f class D $.
	p_2iunin $p |- U_ x e. A U_ y e. B ( C i^i D ) = ( U_ x e. A C i^i U_ y e. B D ) $= f1_2iunin f3_2iunin f4_2iunin f5_2iunin p_iunin2 f1_2iunin f3_2iunin f4_2iunin f5_2iunin a_cin a_ciun f4_2iunin f1_2iunin f3_2iunin f5_2iunin a_ciun a_cin a_wceq f0_2iunin a_sup_set_class f2_2iunin a_wcel p_a1i f0_2iunin f2_2iunin f1_2iunin f3_2iunin f4_2iunin f5_2iunin a_cin a_ciun f4_2iunin f1_2iunin f3_2iunin f5_2iunin a_ciun a_cin p_iuneq2i f0_2iunin f2_2iunin f1_2iunin f3_2iunin f5_2iunin a_ciun f4_2iunin p_iunin1 f0_2iunin f2_2iunin f1_2iunin f3_2iunin f4_2iunin f5_2iunin a_cin a_ciun a_ciun f0_2iunin f2_2iunin f4_2iunin f1_2iunin f3_2iunin f5_2iunin a_ciun a_cin a_ciun f0_2iunin f2_2iunin f4_2iunin a_ciun f1_2iunin f3_2iunin f5_2iunin a_ciun a_cin p_eqtri $.
$}

$(Indexed intersection of class difference.  Generalization of half of
       theorem "De Morgan's laws" in [Enderton] p. 31.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by NM, 5-Oct-2006.) $)

${
	$v x A B C  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	f0_iindif2 $f set x $.
	f1_iindif2 $f class A $.
	f2_iindif2 $f class B $.
	f3_iindif2 $f class C $.
	i0_iindif2 $f set y $.
	p_iindif2 $p |- ( A =/= (/) -> |^|_ x e. A ( B \ C ) = ( B \ U_ x e. A C ) ) $= i0_iindif2 a_sup_set_class f2_iindif2 a_wcel i0_iindif2 a_sup_set_class f3_iindif2 a_wcel a_wn f0_iindif2 f1_iindif2 p_r19.28zv i0_iindif2 a_sup_set_class f2_iindif2 f3_iindif2 p_eldif i0_iindif2 a_sup_set_class f2_iindif2 f3_iindif2 a_cdif a_wcel i0_iindif2 a_sup_set_class f2_iindif2 a_wcel i0_iindif2 a_sup_set_class f3_iindif2 a_wcel a_wn a_wa p_bicomi i0_iindif2 a_sup_set_class f2_iindif2 a_wcel i0_iindif2 a_sup_set_class f3_iindif2 a_wcel a_wn a_wa i0_iindif2 a_sup_set_class f2_iindif2 f3_iindif2 a_cdif a_wcel f0_iindif2 f1_iindif2 p_ralbii i0_iindif2 a_sup_set_class f3_iindif2 a_wcel f0_iindif2 f1_iindif2 p_ralnex f0_iindif2 i0_iindif2 a_sup_set_class f1_iindif2 f3_iindif2 p_eliun i0_iindif2 a_sup_set_class f3_iindif2 a_wcel a_wn f0_iindif2 f1_iindif2 a_wral i0_iindif2 a_sup_set_class f3_iindif2 a_wcel f0_iindif2 f1_iindif2 a_wrex i0_iindif2 a_sup_set_class f0_iindif2 f1_iindif2 f3_iindif2 a_ciun a_wcel p_xchbinxr i0_iindif2 a_sup_set_class f3_iindif2 a_wcel a_wn f0_iindif2 f1_iindif2 a_wral i0_iindif2 a_sup_set_class f0_iindif2 f1_iindif2 f3_iindif2 a_ciun a_wcel a_wn i0_iindif2 a_sup_set_class f2_iindif2 a_wcel p_anbi2i f1_iindif2 a_c0 a_wne i0_iindif2 a_sup_set_class f2_iindif2 a_wcel i0_iindif2 a_sup_set_class f3_iindif2 a_wcel a_wn a_wa f0_iindif2 f1_iindif2 a_wral i0_iindif2 a_sup_set_class f2_iindif2 a_wcel i0_iindif2 a_sup_set_class f3_iindif2 a_wcel a_wn f0_iindif2 f1_iindif2 a_wral a_wa i0_iindif2 a_sup_set_class f2_iindif2 f3_iindif2 a_cdif a_wcel f0_iindif2 f1_iindif2 a_wral i0_iindif2 a_sup_set_class f2_iindif2 a_wcel i0_iindif2 a_sup_set_class f0_iindif2 f1_iindif2 f3_iindif2 a_ciun a_wcel a_wn a_wa p_3bitr3g i0_iindif2 p_vex f0_iindif2 i0_iindif2 a_sup_set_class f1_iindif2 f2_iindif2 f3_iindif2 a_cdif a_cvv p_eliin i0_iindif2 a_sup_set_class a_cvv a_wcel i0_iindif2 a_sup_set_class f0_iindif2 f1_iindif2 f2_iindif2 f3_iindif2 a_cdif a_ciin a_wcel i0_iindif2 a_sup_set_class f2_iindif2 f3_iindif2 a_cdif a_wcel f0_iindif2 f1_iindif2 a_wral a_wb a_ax-mp i0_iindif2 a_sup_set_class f2_iindif2 f0_iindif2 f1_iindif2 f3_iindif2 a_ciun p_eldif f1_iindif2 a_c0 a_wne i0_iindif2 a_sup_set_class f2_iindif2 f3_iindif2 a_cdif a_wcel f0_iindif2 f1_iindif2 a_wral i0_iindif2 a_sup_set_class f2_iindif2 a_wcel i0_iindif2 a_sup_set_class f0_iindif2 f1_iindif2 f3_iindif2 a_ciun a_wcel a_wn a_wa i0_iindif2 a_sup_set_class f0_iindif2 f1_iindif2 f2_iindif2 f3_iindif2 a_cdif a_ciin a_wcel i0_iindif2 a_sup_set_class f2_iindif2 f0_iindif2 f1_iindif2 f3_iindif2 a_ciun a_cdif a_wcel p_3bitr4g f1_iindif2 a_c0 a_wne i0_iindif2 f0_iindif2 f1_iindif2 f2_iindif2 f3_iindif2 a_cdif a_ciin f2_iindif2 f0_iindif2 f1_iindif2 f3_iindif2 a_ciun a_cdif p_eqrdv $.
$}

$(Indexed intersection of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 19-Mar-2015.) $)

${
	$v x A B C  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	f0_iinin2 $f set x $.
	f1_iinin2 $f class A $.
	f2_iinin2 $f class B $.
	f3_iinin2 $f class C $.
	i0_iinin2 $f set y $.
	p_iinin2 $p |- ( A =/= (/) -> |^|_ x e. A ( B i^i C ) = ( B i^i |^|_ x e. A C ) ) $= i0_iinin2 a_sup_set_class f2_iinin2 a_wcel i0_iinin2 a_sup_set_class f3_iinin2 a_wcel f0_iinin2 f1_iinin2 p_r19.28zv i0_iinin2 a_sup_set_class f2_iinin2 f3_iinin2 p_elin i0_iinin2 a_sup_set_class f2_iinin2 f3_iinin2 a_cin a_wcel i0_iinin2 a_sup_set_class f2_iinin2 a_wcel i0_iinin2 a_sup_set_class f3_iinin2 a_wcel a_wa f0_iinin2 f1_iinin2 p_ralbii i0_iinin2 p_vex f0_iinin2 i0_iinin2 a_sup_set_class f1_iinin2 f3_iinin2 a_cvv p_eliin i0_iinin2 a_sup_set_class a_cvv a_wcel i0_iinin2 a_sup_set_class f0_iinin2 f1_iinin2 f3_iinin2 a_ciin a_wcel i0_iinin2 a_sup_set_class f3_iinin2 a_wcel f0_iinin2 f1_iinin2 a_wral a_wb a_ax-mp i0_iinin2 a_sup_set_class f0_iinin2 f1_iinin2 f3_iinin2 a_ciin a_wcel i0_iinin2 a_sup_set_class f3_iinin2 a_wcel f0_iinin2 f1_iinin2 a_wral i0_iinin2 a_sup_set_class f2_iinin2 a_wcel p_anbi2i f1_iinin2 a_c0 a_wne i0_iinin2 a_sup_set_class f2_iinin2 a_wcel i0_iinin2 a_sup_set_class f3_iinin2 a_wcel a_wa f0_iinin2 f1_iinin2 a_wral i0_iinin2 a_sup_set_class f2_iinin2 a_wcel i0_iinin2 a_sup_set_class f3_iinin2 a_wcel f0_iinin2 f1_iinin2 a_wral a_wa i0_iinin2 a_sup_set_class f2_iinin2 f3_iinin2 a_cin a_wcel f0_iinin2 f1_iinin2 a_wral i0_iinin2 a_sup_set_class f2_iinin2 a_wcel i0_iinin2 a_sup_set_class f0_iinin2 f1_iinin2 f3_iinin2 a_ciin a_wcel a_wa p_3bitr4g i0_iinin2 p_vex f0_iinin2 i0_iinin2 a_sup_set_class f1_iinin2 f2_iinin2 f3_iinin2 a_cin a_cvv p_eliin i0_iinin2 a_sup_set_class a_cvv a_wcel i0_iinin2 a_sup_set_class f0_iinin2 f1_iinin2 f2_iinin2 f3_iinin2 a_cin a_ciin a_wcel i0_iinin2 a_sup_set_class f2_iinin2 f3_iinin2 a_cin a_wcel f0_iinin2 f1_iinin2 a_wral a_wb a_ax-mp i0_iinin2 a_sup_set_class f2_iinin2 f0_iinin2 f1_iinin2 f3_iinin2 a_ciin p_elin f1_iinin2 a_c0 a_wne i0_iinin2 a_sup_set_class f2_iinin2 f3_iinin2 a_cin a_wcel f0_iinin2 f1_iinin2 a_wral i0_iinin2 a_sup_set_class f2_iinin2 a_wcel i0_iinin2 a_sup_set_class f0_iinin2 f1_iinin2 f3_iinin2 a_ciin a_wcel a_wa i0_iinin2 a_sup_set_class f0_iinin2 f1_iinin2 f2_iinin2 f3_iinin2 a_cin a_ciin a_wcel i0_iinin2 a_sup_set_class f2_iinin2 f0_iinin2 f1_iinin2 f3_iinin2 a_ciin a_cin a_wcel p_3bitr4g f1_iinin2 a_c0 a_wne i0_iinin2 f0_iinin2 f1_iinin2 f2_iinin2 f3_iinin2 a_cin a_ciin f2_iinin2 f0_iinin2 f1_iinin2 f3_iinin2 a_ciin a_cin p_eqrdv $.
$}

$(Indexed intersection of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 19-Mar-2015.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d x B  $.
	$d C  $.
	f0_iinin1 $f set x $.
	f1_iinin1 $f class A $.
	f2_iinin1 $f class B $.
	f3_iinin1 $f class C $.
	p_iinin1 $p |- ( A =/= (/) -> |^|_ x e. A ( C i^i B ) = ( |^|_ x e. A C i^i B ) ) $= f0_iinin1 f1_iinin1 f2_iinin1 f3_iinin1 p_iinin2 f3_iinin1 f2_iinin1 p_incom f3_iinin1 f2_iinin1 a_cin f2_iinin1 f3_iinin1 a_cin a_wceq f0_iinin1 a_sup_set_class f1_iinin1 a_wcel p_a1i f0_iinin1 f1_iinin1 f3_iinin1 f2_iinin1 a_cin f2_iinin1 f3_iinin1 a_cin p_iineq2i f0_iinin1 f1_iinin1 f3_iinin1 a_ciin f2_iinin1 p_incom f1_iinin1 a_c0 a_wne f0_iinin1 f1_iinin1 f2_iinin1 f3_iinin1 a_cin a_ciin f2_iinin1 f0_iinin1 f1_iinin1 f3_iinin1 a_ciin a_cin f0_iinin1 f1_iinin1 f3_iinin1 f2_iinin1 a_cin a_ciin f0_iinin1 f1_iinin1 f3_iinin1 a_ciin f2_iinin1 a_cin p_3eqtr4g $.
$}

$(Elementhood in a relative intersection.  (Contributed by Mario Carneiro,
       30-Dec-2016.) $)

${
	$v x A B S X  $.
	$d A x  $.
	$d X x  $.
	$d B x  $.
	f0_elriin $f set x $.
	f1_elriin $f class A $.
	f2_elriin $f class B $.
	f3_elriin $f class S $.
	f4_elriin $f class X $.
	p_elriin $p |- ( B e. ( A i^i |^|_ x e. X S ) <-> ( B e. A /\ A. x e. X B e. S ) ) $= f2_elriin f1_elriin f0_elriin f4_elriin f3_elriin a_ciin p_elin f0_elriin f2_elriin f4_elriin f3_elriin f1_elriin p_eliin f2_elriin f1_elriin a_wcel f2_elriin f0_elriin f4_elriin f3_elriin a_ciin a_wcel f2_elriin f3_elriin a_wcel f0_elriin f4_elriin a_wral p_pm5.32i f2_elriin f1_elriin f0_elriin f4_elriin f3_elriin a_ciin a_cin a_wcel f2_elriin f1_elriin a_wcel f2_elriin f0_elriin f4_elriin f3_elriin a_ciin a_wcel a_wa f2_elriin f1_elriin a_wcel f2_elriin f3_elriin a_wcel f0_elriin f4_elriin a_wral a_wa p_bitri $.
$}

$(Relative intersection of an empty family.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)

${
	$v x A S X  $.
	$d A x  $.
	$d X x  $.
	$d x  $.
	f0_riin0 $f set x $.
	f1_riin0 $f class A $.
	f2_riin0 $f class S $.
	f3_riin0 $f class X $.
	p_riin0 $p |- ( X = (/) -> ( A i^i |^|_ x e. X S ) = A ) $= f0_riin0 f3_riin0 a_c0 f2_riin0 p_iineq1 f3_riin0 a_c0 a_wceq f0_riin0 f3_riin0 f2_riin0 a_ciin f0_riin0 a_c0 f2_riin0 a_ciin f1_riin0 p_ineq2d f0_riin0 f2_riin0 p_0iin f0_riin0 a_c0 f2_riin0 a_ciin a_cvv f1_riin0 p_ineq2i f1_riin0 p_inv1 f1_riin0 f0_riin0 a_c0 f2_riin0 a_ciin a_cin f1_riin0 a_cvv a_cin f1_riin0 p_eqtri f3_riin0 a_c0 a_wceq f1_riin0 f0_riin0 f3_riin0 f2_riin0 a_ciin a_cin f1_riin0 f0_riin0 a_c0 f2_riin0 a_ciin a_cin f1_riin0 p_syl6eq $.
$}

$(Relative intersection of a nonempty family.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)

${
	$v x A S X  $.
	$d A x  $.
	$d X x  $.
	$d x  $.
	f0_riinn0 $f set x $.
	f1_riinn0 $f class A $.
	f2_riinn0 $f class S $.
	f3_riinn0 $f class X $.
	p_riinn0 $p |- ( ( A. x e. X S C_ A /\ X =/= (/) ) -> ( A i^i |^|_ x e. X S ) = |^|_ x e. X S ) $= f1_riinn0 f0_riinn0 f3_riinn0 f2_riinn0 a_ciin p_incom f2_riinn0 f1_riinn0 a_wss f0_riinn0 f3_riinn0 p_r19.2z f3_riinn0 a_c0 a_wne f2_riinn0 f1_riinn0 a_wss f0_riinn0 f3_riinn0 a_wral f2_riinn0 f1_riinn0 a_wss f0_riinn0 f3_riinn0 a_wrex p_ancoms f0_riinn0 f3_riinn0 f2_riinn0 f1_riinn0 p_iinss f2_riinn0 f1_riinn0 a_wss f0_riinn0 f3_riinn0 a_wral f3_riinn0 a_c0 a_wne a_wa f2_riinn0 f1_riinn0 a_wss f0_riinn0 f3_riinn0 a_wrex f0_riinn0 f3_riinn0 f2_riinn0 a_ciin f1_riinn0 a_wss p_syl f0_riinn0 f3_riinn0 f2_riinn0 a_ciin f1_riinn0 a_df-ss f2_riinn0 f1_riinn0 a_wss f0_riinn0 f3_riinn0 a_wral f3_riinn0 a_c0 a_wne a_wa f0_riinn0 f3_riinn0 f2_riinn0 a_ciin f1_riinn0 a_wss f0_riinn0 f3_riinn0 f2_riinn0 a_ciin f1_riinn0 a_cin f0_riinn0 f3_riinn0 f2_riinn0 a_ciin a_wceq p_sylib f2_riinn0 f1_riinn0 a_wss f0_riinn0 f3_riinn0 a_wral f3_riinn0 a_c0 a_wne a_wa f1_riinn0 f0_riinn0 f3_riinn0 f2_riinn0 a_ciin a_cin f0_riinn0 f3_riinn0 f2_riinn0 a_ciin f1_riinn0 a_cin f0_riinn0 f3_riinn0 f2_riinn0 a_ciin p_syl5eq $.
$}

$(Relative intersection of a relative abstraction.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)

${
	$v ph x y A X  $.
	$d A x y  $.
	$d X x y  $.
	$d x  $.
	f0_riinrab $f wff ph $.
	f1_riinrab $f set x $.
	f2_riinrab $f set y $.
	f3_riinrab $f class A $.
	f4_riinrab $f class X $.
	p_riinrab $p |- ( A i^i |^|_ x e. X { y e. A | ph } ) = { y e. A | A. x e. X ph } $= f1_riinrab f3_riinrab f0_riinrab f2_riinrab f3_riinrab a_crab f4_riinrab p_riin0 f0_riinrab f1_riinrab f4_riinrab p_rzal f4_riinrab a_c0 a_wceq f0_riinrab f1_riinrab f4_riinrab a_wral f2_riinrab f3_riinrab p_ralrimivw f0_riinrab f1_riinrab f4_riinrab a_wral f2_riinrab f3_riinrab p_rabid2 f4_riinrab a_c0 a_wceq f0_riinrab f1_riinrab f4_riinrab a_wral f2_riinrab f3_riinrab a_wral f3_riinrab f0_riinrab f1_riinrab f4_riinrab a_wral f2_riinrab f3_riinrab a_crab a_wceq p_sylibr f4_riinrab a_c0 a_wceq f3_riinrab f1_riinrab f4_riinrab f0_riinrab f2_riinrab f3_riinrab a_crab a_ciin a_cin f3_riinrab f0_riinrab f1_riinrab f4_riinrab a_wral f2_riinrab f3_riinrab a_crab p_eqtrd f0_riinrab f2_riinrab f3_riinrab p_ssrab2 f0_riinrab f2_riinrab f3_riinrab a_crab f3_riinrab a_wss f1_riinrab f4_riinrab p_rgenw f1_riinrab f3_riinrab f0_riinrab f2_riinrab f3_riinrab a_crab f4_riinrab p_riinn0 f0_riinrab f2_riinrab f3_riinrab a_crab f3_riinrab a_wss f1_riinrab f4_riinrab a_wral f4_riinrab a_c0 a_wne f3_riinrab f1_riinrab f4_riinrab f0_riinrab f2_riinrab f3_riinrab a_crab a_ciin a_cin f1_riinrab f4_riinrab f0_riinrab f2_riinrab f3_riinrab a_crab a_ciin a_wceq p_mpan f0_riinrab f1_riinrab f2_riinrab f4_riinrab f3_riinrab p_iinrab f4_riinrab a_c0 a_wne f3_riinrab f1_riinrab f4_riinrab f0_riinrab f2_riinrab f3_riinrab a_crab a_ciin a_cin f1_riinrab f4_riinrab f0_riinrab f2_riinrab f3_riinrab a_crab a_ciin f0_riinrab f1_riinrab f4_riinrab a_wral f2_riinrab f3_riinrab a_crab p_eqtrd f3_riinrab f1_riinrab f4_riinrab f0_riinrab f2_riinrab f3_riinrab a_crab a_ciin a_cin f0_riinrab f1_riinrab f4_riinrab a_wral f2_riinrab f3_riinrab a_crab a_wceq f4_riinrab a_c0 p_pm2.61ine $.
$}

$(A singleton index picks out an instance of an indexed intersection's
       argument.  (Contributed by NM, 15-Jan-2012.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.) $)

${
	$v x A B C V  $.
	$d x y A  $.
	$d y B  $.
	$d x y C  $.
	$d y V  $.
	f0_iinxsng $f set x $.
	f1_iinxsng $f class A $.
	f2_iinxsng $f class B $.
	f3_iinxsng $f class C $.
	f4_iinxsng $f class V $.
	i0_iinxsng $f set y $.
	e0_iinxsng $e |- ( x = A -> B = C ) $.
	p_iinxsng $p |- ( A e. V -> |^|_ x e. { A } B = C ) $= f0_iinxsng i0_iinxsng f1_iinxsng a_csn f2_iinxsng a_df-iin e0_iinxsng f0_iinxsng a_sup_set_class f1_iinxsng a_wceq f2_iinxsng f3_iinxsng i0_iinxsng a_sup_set_class p_eleq2d i0_iinxsng a_sup_set_class f2_iinxsng a_wcel i0_iinxsng a_sup_set_class f3_iinxsng a_wcel f0_iinxsng f1_iinxsng f4_iinxsng p_ralsng f1_iinxsng f4_iinxsng a_wcel i0_iinxsng a_sup_set_class f2_iinxsng a_wcel f0_iinxsng f1_iinxsng a_csn a_wral i0_iinxsng f3_iinxsng p_abbi1dv f1_iinxsng f4_iinxsng a_wcel f0_iinxsng f1_iinxsng a_csn f2_iinxsng a_ciin i0_iinxsng a_sup_set_class f2_iinxsng a_wcel f0_iinxsng f1_iinxsng a_csn a_wral i0_iinxsng a_cab f3_iinxsng p_syl5eq $.
$}

$(Indexed intersection with an unordered pair index.  (Contributed by NM,
       25-Jan-2012.) $)

${
	$v x A B C D E V W  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	$d x y D  $.
	$d x y E  $.
	$d y V  $.
	$d y W  $.
	f0_iinxprg $f set x $.
	f1_iinxprg $f class A $.
	f2_iinxprg $f class B $.
	f3_iinxprg $f class C $.
	f4_iinxprg $f class D $.
	f5_iinxprg $f class E $.
	f6_iinxprg $f class V $.
	f7_iinxprg $f class W $.
	i0_iinxprg $f set y $.
	e0_iinxprg $e |- ( x = A -> C = D ) $.
	e1_iinxprg $e |- ( x = B -> C = E ) $.
	p_iinxprg $p |- ( ( A e. V /\ B e. W ) -> |^|_ x e. { A , B } C = ( D i^i E ) ) $= e0_iinxprg f0_iinxprg a_sup_set_class f1_iinxprg a_wceq f3_iinxprg f4_iinxprg i0_iinxprg a_sup_set_class p_eleq2d e1_iinxprg f0_iinxprg a_sup_set_class f2_iinxprg a_wceq f3_iinxprg f5_iinxprg i0_iinxprg a_sup_set_class p_eleq2d i0_iinxprg a_sup_set_class f3_iinxprg a_wcel i0_iinxprg a_sup_set_class f4_iinxprg a_wcel i0_iinxprg a_sup_set_class f5_iinxprg a_wcel f0_iinxprg f1_iinxprg f2_iinxprg f6_iinxprg f7_iinxprg p_ralprg f1_iinxprg f6_iinxprg a_wcel f2_iinxprg f7_iinxprg a_wcel a_wa i0_iinxprg a_sup_set_class f3_iinxprg a_wcel f0_iinxprg f1_iinxprg f2_iinxprg a_cpr a_wral i0_iinxprg a_sup_set_class f4_iinxprg a_wcel i0_iinxprg a_sup_set_class f5_iinxprg a_wcel a_wa i0_iinxprg p_abbidv f0_iinxprg i0_iinxprg f1_iinxprg f2_iinxprg a_cpr f3_iinxprg a_df-iin i0_iinxprg f4_iinxprg f5_iinxprg a_df-in f1_iinxprg f6_iinxprg a_wcel f2_iinxprg f7_iinxprg a_wcel a_wa i0_iinxprg a_sup_set_class f3_iinxprg a_wcel f0_iinxprg f1_iinxprg f2_iinxprg a_cpr a_wral i0_iinxprg a_cab i0_iinxprg a_sup_set_class f4_iinxprg a_wcel i0_iinxprg a_sup_set_class f5_iinxprg a_wcel a_wa i0_iinxprg a_cab f0_iinxprg f1_iinxprg f2_iinxprg a_cpr f3_iinxprg a_ciin f4_iinxprg f5_iinxprg a_cin p_3eqtr4g $.
$}

$(A singleton index picks out an instance of an indexed union's argument.
       (Contributed by Mario Carneiro, 25-Jun-2016.) $)

${
	$v x A B C V  $.
	$d x y A  $.
	$d y B  $.
	$d x y C  $.
	$d y V  $.
	f0_iunxsng $f set x $.
	f1_iunxsng $f class A $.
	f2_iunxsng $f class B $.
	f3_iunxsng $f class C $.
	f4_iunxsng $f class V $.
	i0_iunxsng $f set y $.
	e0_iunxsng $e |- ( x = A -> B = C ) $.
	p_iunxsng $p |- ( A e. V -> U_ x e. { A } B = C ) $= f0_iunxsng i0_iunxsng a_sup_set_class f1_iunxsng a_csn f2_iunxsng p_eliun e0_iunxsng f0_iunxsng a_sup_set_class f1_iunxsng a_wceq f2_iunxsng f3_iunxsng i0_iunxsng a_sup_set_class p_eleq2d i0_iunxsng a_sup_set_class f2_iunxsng a_wcel i0_iunxsng a_sup_set_class f3_iunxsng a_wcel f0_iunxsng f1_iunxsng f4_iunxsng p_rexsng i0_iunxsng a_sup_set_class f0_iunxsng f1_iunxsng a_csn f2_iunxsng a_ciun a_wcel i0_iunxsng a_sup_set_class f2_iunxsng a_wcel f0_iunxsng f1_iunxsng a_csn a_wrex f1_iunxsng f4_iunxsng a_wcel i0_iunxsng a_sup_set_class f3_iunxsng a_wcel p_syl5bb f1_iunxsng f4_iunxsng a_wcel i0_iunxsng f0_iunxsng f1_iunxsng a_csn f2_iunxsng a_ciun f3_iunxsng p_eqrdv $.
$}

$(A singleton index picks out an instance of an indexed union's argument.
       (Contributed by NM, 26-Mar-2004.)  (Proof shortened by Mario Carneiro,
       25-Jun-2016.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d B  $.
	$d x C  $.
	f0_iunxsn $f set x $.
	f1_iunxsn $f class A $.
	f2_iunxsn $f class B $.
	f3_iunxsn $f class C $.
	e0_iunxsn $e |- A e. _V $.
	e1_iunxsn $e |- ( x = A -> B = C ) $.
	p_iunxsn $p |- U_ x e. { A } B = C $= e0_iunxsn e1_iunxsn f0_iunxsn f1_iunxsn f2_iunxsn f3_iunxsn a_cvv p_iunxsng f1_iunxsn a_cvv a_wcel f0_iunxsn f1_iunxsn a_csn f2_iunxsn a_ciun f3_iunxsn a_wceq a_ax-mp $.
$}

$(Separate a union in an indexed union.  (Contributed by NM,
       27-Dec-2004.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)

${
	$v x A B C  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	f0_iunun $f set x $.
	f1_iunun $f class A $.
	f2_iunun $f class B $.
	f3_iunun $f class C $.
	i0_iunun $f set y $.
	p_iunun $p |- U_ x e. A ( B u. C ) = ( U_ x e. A B u. U_ x e. A C ) $= i0_iunun a_sup_set_class f2_iunun a_wcel i0_iunun a_sup_set_class f3_iunun a_wcel f0_iunun f1_iunun p_r19.43 i0_iunun a_sup_set_class f2_iunun f3_iunun p_elun i0_iunun a_sup_set_class f2_iunun f3_iunun a_cun a_wcel i0_iunun a_sup_set_class f2_iunun a_wcel i0_iunun a_sup_set_class f3_iunun a_wcel a_wo f0_iunun f1_iunun p_rexbii f0_iunun i0_iunun a_sup_set_class f1_iunun f2_iunun p_eliun f0_iunun i0_iunun a_sup_set_class f1_iunun f3_iunun p_eliun i0_iunun a_sup_set_class f0_iunun f1_iunun f2_iunun a_ciun a_wcel i0_iunun a_sup_set_class f2_iunun a_wcel f0_iunun f1_iunun a_wrex i0_iunun a_sup_set_class f0_iunun f1_iunun f3_iunun a_ciun a_wcel i0_iunun a_sup_set_class f3_iunun a_wcel f0_iunun f1_iunun a_wrex p_orbi12i i0_iunun a_sup_set_class f2_iunun a_wcel i0_iunun a_sup_set_class f3_iunun a_wcel a_wo f0_iunun f1_iunun a_wrex i0_iunun a_sup_set_class f2_iunun a_wcel f0_iunun f1_iunun a_wrex i0_iunun a_sup_set_class f3_iunun a_wcel f0_iunun f1_iunun a_wrex a_wo i0_iunun a_sup_set_class f2_iunun f3_iunun a_cun a_wcel f0_iunun f1_iunun a_wrex i0_iunun a_sup_set_class f0_iunun f1_iunun f2_iunun a_ciun a_wcel i0_iunun a_sup_set_class f0_iunun f1_iunun f3_iunun a_ciun a_wcel a_wo p_3bitr4i f0_iunun i0_iunun a_sup_set_class f1_iunun f2_iunun f3_iunun a_cun p_eliun i0_iunun a_sup_set_class f0_iunun f1_iunun f2_iunun a_ciun f0_iunun f1_iunun f3_iunun a_ciun p_elun i0_iunun a_sup_set_class f2_iunun f3_iunun a_cun a_wcel f0_iunun f1_iunun a_wrex i0_iunun a_sup_set_class f0_iunun f1_iunun f2_iunun a_ciun a_wcel i0_iunun a_sup_set_class f0_iunun f1_iunun f3_iunun a_ciun a_wcel a_wo i0_iunun a_sup_set_class f0_iunun f1_iunun f2_iunun f3_iunun a_cun a_ciun a_wcel i0_iunun a_sup_set_class f0_iunun f1_iunun f2_iunun a_ciun f0_iunun f1_iunun f3_iunun a_ciun a_cun a_wcel p_3bitr4i i0_iunun f0_iunun f1_iunun f2_iunun f3_iunun a_cun a_ciun f0_iunun f1_iunun f2_iunun a_ciun f0_iunun f1_iunun f3_iunun a_ciun a_cun p_eqriv $.
$}

$(Separate a union in the index of an indexed union.  (Contributed by NM,
       26-Mar-2004.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)

${
	$v x A B C  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	f0_iunxun $f set x $.
	f1_iunxun $f class A $.
	f2_iunxun $f class B $.
	f3_iunxun $f class C $.
	i0_iunxun $f set y $.
	p_iunxun $p |- U_ x e. ( A u. B ) C = ( U_ x e. A C u. U_ x e. B C ) $= i0_iunxun a_sup_set_class f3_iunxun a_wcel f0_iunxun f1_iunxun f2_iunxun p_rexun f0_iunxun i0_iunxun a_sup_set_class f1_iunxun f3_iunxun p_eliun f0_iunxun i0_iunxun a_sup_set_class f2_iunxun f3_iunxun p_eliun i0_iunxun a_sup_set_class f0_iunxun f1_iunxun f3_iunxun a_ciun a_wcel i0_iunxun a_sup_set_class f3_iunxun a_wcel f0_iunxun f1_iunxun a_wrex i0_iunxun a_sup_set_class f0_iunxun f2_iunxun f3_iunxun a_ciun a_wcel i0_iunxun a_sup_set_class f3_iunxun a_wcel f0_iunxun f2_iunxun a_wrex p_orbi12i i0_iunxun a_sup_set_class f3_iunxun a_wcel f0_iunxun f1_iunxun f2_iunxun a_cun a_wrex i0_iunxun a_sup_set_class f3_iunxun a_wcel f0_iunxun f1_iunxun a_wrex i0_iunxun a_sup_set_class f3_iunxun a_wcel f0_iunxun f2_iunxun a_wrex a_wo i0_iunxun a_sup_set_class f0_iunxun f1_iunxun f3_iunxun a_ciun a_wcel i0_iunxun a_sup_set_class f0_iunxun f2_iunxun f3_iunxun a_ciun a_wcel a_wo p_bitr4i f0_iunxun i0_iunxun a_sup_set_class f1_iunxun f2_iunxun a_cun f3_iunxun p_eliun i0_iunxun a_sup_set_class f0_iunxun f1_iunxun f3_iunxun a_ciun f0_iunxun f2_iunxun f3_iunxun a_ciun p_elun i0_iunxun a_sup_set_class f3_iunxun a_wcel f0_iunxun f1_iunxun f2_iunxun a_cun a_wrex i0_iunxun a_sup_set_class f0_iunxun f1_iunxun f3_iunxun a_ciun a_wcel i0_iunxun a_sup_set_class f0_iunxun f2_iunxun f3_iunxun a_ciun a_wcel a_wo i0_iunxun a_sup_set_class f0_iunxun f1_iunxun f2_iunxun a_cun f3_iunxun a_ciun a_wcel i0_iunxun a_sup_set_class f0_iunxun f1_iunxun f3_iunxun a_ciun f0_iunxun f2_iunxun f3_iunxun a_ciun a_cun a_wcel p_3bitr4i i0_iunxun f0_iunxun f1_iunxun f2_iunxun a_cun f3_iunxun a_ciun f0_iunxun f1_iunxun f3_iunxun a_ciun f0_iunxun f2_iunxun f3_iunxun a_ciun a_cun p_eqriv $.
$}

$(Separate an indexed union in the index of an indexed union.
       (Contributed by Mario Carneiro, 5-Dec-2016.) $)

${
	$v x y A B C  $.
	$d x y z  $.
	$d x z A  $.
	$d z B  $.
	$d y z C  $.
	f0_iunxiun $f set x $.
	f1_iunxiun $f set y $.
	f2_iunxiun $f class A $.
	f3_iunxiun $f class B $.
	f4_iunxiun $f class C $.
	i0_iunxiun $f set z $.
	p_iunxiun $p |- U_ x e. U_ y e. A B C = U_ y e. A U_ x e. B C $= f1_iunxiun f0_iunxiun a_sup_set_class f2_iunxiun f3_iunxiun p_eliun f0_iunxiun a_sup_set_class f1_iunxiun f2_iunxiun f3_iunxiun a_ciun a_wcel f0_iunxiun a_sup_set_class f3_iunxiun a_wcel f1_iunxiun f2_iunxiun a_wrex i0_iunxiun a_sup_set_class f4_iunxiun a_wcel p_anbi1i f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel f1_iunxiun f2_iunxiun p_r19.41v f0_iunxiun a_sup_set_class f1_iunxiun f2_iunxiun f3_iunxiun a_ciun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_sup_set_class f3_iunxiun a_wcel f1_iunxiun f2_iunxiun a_wrex i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f1_iunxiun f2_iunxiun a_wrex p_bitr4i f0_iunxiun a_sup_set_class f1_iunxiun f2_iunxiun f3_iunxiun a_ciun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f1_iunxiun f2_iunxiun a_wrex f0_iunxiun p_exbii f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f1_iunxiun f0_iunxiun f2_iunxiun p_rexcom4 f0_iunxiun a_sup_set_class f1_iunxiun f2_iunxiun f3_iunxiun a_ciun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_wex f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f1_iunxiun f2_iunxiun a_wrex f0_iunxiun a_wex f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_wex f1_iunxiun f2_iunxiun a_wrex p_bitr4i i0_iunxiun a_sup_set_class f4_iunxiun a_wcel f0_iunxiun f1_iunxiun f2_iunxiun f3_iunxiun a_ciun a_df-rex f0_iunxiun i0_iunxiun a_sup_set_class f3_iunxiun f4_iunxiun p_eliun i0_iunxiun a_sup_set_class f4_iunxiun a_wcel f0_iunxiun f3_iunxiun a_df-rex i0_iunxiun a_sup_set_class f0_iunxiun f3_iunxiun f4_iunxiun a_ciun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel f0_iunxiun f3_iunxiun a_wrex f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_wex p_bitri i0_iunxiun a_sup_set_class f0_iunxiun f3_iunxiun f4_iunxiun a_ciun a_wcel f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_wex f1_iunxiun f2_iunxiun p_rexbii f0_iunxiun a_sup_set_class f1_iunxiun f2_iunxiun f3_iunxiun a_ciun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_wex f0_iunxiun a_sup_set_class f3_iunxiun a_wcel i0_iunxiun a_sup_set_class f4_iunxiun a_wcel a_wa f0_iunxiun a_wex f1_iunxiun f2_iunxiun a_wrex i0_iunxiun a_sup_set_class f4_iunxiun a_wcel f0_iunxiun f1_iunxiun f2_iunxiun f3_iunxiun a_ciun a_wrex i0_iunxiun a_sup_set_class f0_iunxiun f3_iunxiun f4_iunxiun a_ciun a_wcel f1_iunxiun f2_iunxiun a_wrex p_3bitr4i f0_iunxiun i0_iunxiun a_sup_set_class f1_iunxiun f2_iunxiun f3_iunxiun a_ciun f4_iunxiun p_eliun f1_iunxiun i0_iunxiun a_sup_set_class f2_iunxiun f0_iunxiun f3_iunxiun f4_iunxiun a_ciun p_eliun i0_iunxiun a_sup_set_class f4_iunxiun a_wcel f0_iunxiun f1_iunxiun f2_iunxiun f3_iunxiun a_ciun a_wrex i0_iunxiun a_sup_set_class f0_iunxiun f3_iunxiun f4_iunxiun a_ciun a_wcel f1_iunxiun f2_iunxiun a_wrex i0_iunxiun a_sup_set_class f0_iunxiun f1_iunxiun f2_iunxiun f3_iunxiun a_ciun f4_iunxiun a_ciun a_wcel i0_iunxiun a_sup_set_class f1_iunxiun f2_iunxiun f0_iunxiun f3_iunxiun f4_iunxiun a_ciun a_ciun a_wcel p_3bitr4i i0_iunxiun f0_iunxiun f1_iunxiun f2_iunxiun f3_iunxiun a_ciun f4_iunxiun a_ciun f1_iunxiun f2_iunxiun f0_iunxiun f3_iunxiun f4_iunxiun a_ciun a_ciun p_eqriv $.
$}

$(A relationship involving union and indexed intersection.  Exercise 23 of
       [Enderton] p. 33.  (Contributed by NM, 25-Nov-2003.)  (Proof shortened
       by Mario Carneiro, 17-Nov-2016.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_iinuni $f set x $.
	f1_iinuni $f class A $.
	f2_iinuni $f class B $.
	i0_iinuni $f set y $.
	p_iinuni $p |- ( A u. |^| B ) = |^|_ x e. B ( A u. x ) $= i0_iinuni a_sup_set_class f1_iinuni a_wcel i0_iinuni a_sup_set_class f0_iinuni a_sup_set_class a_wcel f0_iinuni f2_iinuni p_r19.32v i0_iinuni a_sup_set_class f1_iinuni f0_iinuni a_sup_set_class p_elun i0_iinuni a_sup_set_class f1_iinuni f0_iinuni a_sup_set_class a_cun a_wcel i0_iinuni a_sup_set_class f1_iinuni a_wcel i0_iinuni a_sup_set_class f0_iinuni a_sup_set_class a_wcel a_wo f0_iinuni f2_iinuni p_ralbii i0_iinuni p_vex f0_iinuni i0_iinuni a_sup_set_class f2_iinuni p_elint2 i0_iinuni a_sup_set_class f2_iinuni a_cint a_wcel i0_iinuni a_sup_set_class f0_iinuni a_sup_set_class a_wcel f0_iinuni f2_iinuni a_wral i0_iinuni a_sup_set_class f1_iinuni a_wcel p_orbi2i i0_iinuni a_sup_set_class f1_iinuni a_wcel i0_iinuni a_sup_set_class f0_iinuni a_sup_set_class a_wcel a_wo f0_iinuni f2_iinuni a_wral i0_iinuni a_sup_set_class f1_iinuni a_wcel i0_iinuni a_sup_set_class f0_iinuni a_sup_set_class a_wcel f0_iinuni f2_iinuni a_wral a_wo i0_iinuni a_sup_set_class f1_iinuni f0_iinuni a_sup_set_class a_cun a_wcel f0_iinuni f2_iinuni a_wral i0_iinuni a_sup_set_class f1_iinuni a_wcel i0_iinuni a_sup_set_class f2_iinuni a_cint a_wcel a_wo p_3bitr4ri i0_iinuni a_sup_set_class f1_iinuni a_wcel i0_iinuni a_sup_set_class f2_iinuni a_cint a_wcel a_wo i0_iinuni a_sup_set_class f1_iinuni f0_iinuni a_sup_set_class a_cun a_wcel f0_iinuni f2_iinuni a_wral i0_iinuni p_abbii i0_iinuni f1_iinuni f2_iinuni a_cint a_df-un f0_iinuni i0_iinuni f2_iinuni f1_iinuni f0_iinuni a_sup_set_class a_cun a_df-iin i0_iinuni a_sup_set_class f1_iinuni a_wcel i0_iinuni a_sup_set_class f2_iinuni a_cint a_wcel a_wo i0_iinuni a_cab i0_iinuni a_sup_set_class f1_iinuni f0_iinuni a_sup_set_class a_cun a_wcel f0_iinuni f2_iinuni a_wral i0_iinuni a_cab f1_iinuni f2_iinuni a_cint a_cun f0_iinuni f2_iinuni f1_iinuni f0_iinuni a_sup_set_class a_cun a_ciin p_3eqtr4i $.
$}

$(A relationship involving union and indexed union.  Exercise 25 of
       [Enderton] p. 33.  (Contributed by NM, 25-Nov-2003.)  (Proof shortened
       by Mario Carneiro, 17-Nov-2016.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_iununi $f set x $.
	f1_iununi $f class A $.
	f2_iununi $f class B $.
	p_iununi $p |- ( ( B = (/) -> A = (/) ) <-> ( A u. U. B ) = U_ x e. B ( A u. x ) ) $= f2_iununi a_c0 a_df-ne f0_iununi f2_iununi f1_iununi p_iunconst f2_iununi a_c0 a_wceq a_wn f2_iununi a_c0 a_wne f0_iununi f2_iununi f1_iununi a_ciun f1_iununi a_wceq p_sylbir f0_iununi f2_iununi p_iun0 f1_iununi a_c0 a_wceq p_id f1_iununi a_c0 a_wceq f0_iununi f2_iununi f1_iununi a_c0 p_iuneq2d f1_iununi a_c0 a_wceq p_id f1_iununi a_c0 a_wceq f0_iununi f2_iununi a_c0 a_ciun a_c0 f0_iununi f2_iununi f1_iununi a_ciun f1_iununi p_3eqtr4a f2_iununi a_c0 a_wceq f1_iununi a_c0 a_wceq f0_iununi f2_iununi f1_iununi a_ciun f1_iununi a_wceq p_ja f2_iununi a_c0 a_wceq f1_iununi a_c0 a_wceq a_wi f0_iununi f2_iununi f1_iununi a_ciun f1_iununi p_eqcomd f2_iununi a_c0 a_wceq f1_iununi a_c0 a_wceq a_wi f1_iununi f0_iununi f2_iununi f1_iununi a_ciun f0_iununi f2_iununi f0_iununi a_sup_set_class a_ciun p_uneq1d f0_iununi f2_iununi p_uniiun f2_iununi a_cuni f0_iununi f2_iununi f0_iununi a_sup_set_class a_ciun f1_iununi p_uneq2i f0_iununi f2_iununi f1_iununi f0_iununi a_sup_set_class p_iunun f2_iununi a_c0 a_wceq f1_iununi a_c0 a_wceq a_wi f1_iununi f0_iununi f2_iununi f0_iununi a_sup_set_class a_ciun a_cun f0_iununi f2_iununi f1_iununi a_ciun f0_iununi f2_iununi f0_iununi a_sup_set_class a_ciun a_cun f1_iununi f2_iununi a_cuni a_cun f0_iununi f2_iununi f1_iununi f0_iununi a_sup_set_class a_cun a_ciun p_3eqtr4g f2_iununi a_c0 p_unieq p_uni0 f2_iununi a_c0 a_wceq f2_iununi a_cuni a_c0 a_cuni a_c0 p_syl6eq f2_iununi a_c0 a_wceq f2_iununi a_cuni a_c0 f1_iununi p_uneq2d f1_iununi p_un0 f2_iununi a_c0 a_wceq f1_iununi f2_iununi a_cuni a_cun f1_iununi a_c0 a_cun f1_iununi p_syl6eq f0_iununi f2_iununi a_c0 f1_iununi f0_iununi a_sup_set_class a_cun p_iuneq1 f0_iununi f1_iununi f0_iununi a_sup_set_class a_cun p_0iun f2_iununi a_c0 a_wceq f0_iununi f2_iununi f1_iununi f0_iununi a_sup_set_class a_cun a_ciun f0_iununi a_c0 f1_iununi f0_iununi a_sup_set_class a_cun a_ciun a_c0 p_syl6eq f2_iununi a_c0 a_wceq f1_iununi f2_iununi a_cuni a_cun f1_iununi f0_iununi f2_iununi f1_iununi f0_iununi a_sup_set_class a_cun a_ciun a_c0 p_eqeq12d f2_iununi a_c0 a_wceq f1_iununi f2_iununi a_cuni a_cun f0_iununi f2_iununi f1_iununi f0_iununi a_sup_set_class a_cun a_ciun a_wceq f1_iununi a_c0 a_wceq p_biimpcd f2_iununi a_c0 a_wceq f1_iununi a_c0 a_wceq a_wi f1_iununi f2_iununi a_cuni a_cun f0_iununi f2_iununi f1_iununi f0_iununi a_sup_set_class a_cun a_ciun a_wceq p_impbii $.
$}

$(Subclass relationship for power class and union.  (Contributed by NM,
       18-Jul-2006.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_sspwuni $f class A $.
	f1_sspwuni $f class B $.
	i0_sspwuni $f set x $.
	p_sspwuni $p |- ( A C_ ~P B <-> U. A C_ B ) $= i0_sspwuni p_vex i0_sspwuni a_sup_set_class f1_sspwuni p_elpw i0_sspwuni a_sup_set_class f1_sspwuni a_cpw a_wcel i0_sspwuni a_sup_set_class f1_sspwuni a_wss i0_sspwuni f0_sspwuni p_ralbii i0_sspwuni f0_sspwuni f1_sspwuni a_cpw p_dfss3 i0_sspwuni f0_sspwuni f1_sspwuni p_unissb i0_sspwuni a_sup_set_class f1_sspwuni a_cpw a_wcel i0_sspwuni f0_sspwuni a_wral i0_sspwuni a_sup_set_class f1_sspwuni a_wss i0_sspwuni f0_sspwuni a_wral f0_sspwuni f1_sspwuni a_cpw a_wss f0_sspwuni a_cuni f1_sspwuni a_wss p_3bitr4i $.
$}

$(Two ways to express a collection of subclasses.  (Contributed by NM,
       19-Jul-2006.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_pwssb $f set x $.
	f1_pwssb $f class A $.
	f2_pwssb $f class B $.
	p_pwssb $p |- ( A C_ ~P B <-> A. x e. A x C_ B ) $= f1_pwssb f2_pwssb p_sspwuni f0_pwssb f1_pwssb f2_pwssb p_unissb f1_pwssb f2_pwssb a_cpw a_wss f1_pwssb a_cuni f2_pwssb a_wss f0_pwssb a_sup_set_class f2_pwssb a_wss f0_pwssb f1_pwssb a_wral p_bitri $.
$}

$(Relationship for power class and union.  (Contributed by NM,
     18-Jul-2006.) $)

${
	$v A B  $.
	f0_elpwuni $f class A $.
	f1_elpwuni $f class B $.
	p_elpwuni $p |- ( B e. A -> ( A C_ ~P B <-> U. A = B ) ) $= f0_elpwuni f1_elpwuni p_sspwuni f0_elpwuni f1_elpwuni p_unissel f0_elpwuni a_cuni f1_elpwuni a_wss f1_elpwuni f0_elpwuni a_wcel f0_elpwuni a_cuni f1_elpwuni a_wceq p_expcom f0_elpwuni a_cuni f1_elpwuni p_eqimss f1_elpwuni f0_elpwuni a_wcel f0_elpwuni a_cuni f1_elpwuni a_wss f0_elpwuni a_cuni f1_elpwuni a_wceq p_impbid1 f0_elpwuni f1_elpwuni a_cpw a_wss f0_elpwuni a_cuni f1_elpwuni a_wss f1_elpwuni f0_elpwuni a_wcel f0_elpwuni a_cuni f1_elpwuni a_wceq p_syl5bb $.
$}

$(The power class of an intersection in terms of indexed intersection.
       Exercise 24(a) of [Enderton] p. 33.  (Contributed by NM,
       29-Nov-2003.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_iinpw $f set x $.
	f1_iinpw $f class A $.
	i0_iinpw $f set y $.
	p_iinpw $p |- ~P |^| A = |^|_ x e. A ~P x $= f0_iinpw i0_iinpw a_sup_set_class f1_iinpw p_ssint i0_iinpw p_vex i0_iinpw a_sup_set_class f0_iinpw a_sup_set_class p_elpw i0_iinpw a_sup_set_class f0_iinpw a_sup_set_class a_cpw a_wcel i0_iinpw a_sup_set_class f0_iinpw a_sup_set_class a_wss f0_iinpw f1_iinpw p_ralbii i0_iinpw a_sup_set_class f1_iinpw a_cint a_wss i0_iinpw a_sup_set_class f0_iinpw a_sup_set_class a_wss f0_iinpw f1_iinpw a_wral i0_iinpw a_sup_set_class f0_iinpw a_sup_set_class a_cpw a_wcel f0_iinpw f1_iinpw a_wral p_bitr4i i0_iinpw p_vex i0_iinpw a_sup_set_class f1_iinpw a_cint p_elpw i0_iinpw p_vex f0_iinpw i0_iinpw a_sup_set_class f1_iinpw f0_iinpw a_sup_set_class a_cpw a_cvv p_eliin i0_iinpw a_sup_set_class a_cvv a_wcel i0_iinpw a_sup_set_class f0_iinpw f1_iinpw f0_iinpw a_sup_set_class a_cpw a_ciin a_wcel i0_iinpw a_sup_set_class f0_iinpw a_sup_set_class a_cpw a_wcel f0_iinpw f1_iinpw a_wral a_wb a_ax-mp i0_iinpw a_sup_set_class f1_iinpw a_cint a_wss i0_iinpw a_sup_set_class f0_iinpw a_sup_set_class a_cpw a_wcel f0_iinpw f1_iinpw a_wral i0_iinpw a_sup_set_class f1_iinpw a_cint a_cpw a_wcel i0_iinpw a_sup_set_class f0_iinpw f1_iinpw f0_iinpw a_sup_set_class a_cpw a_ciin a_wcel p_3bitr4i i0_iinpw f1_iinpw a_cint a_cpw f0_iinpw f1_iinpw f0_iinpw a_sup_set_class a_cpw a_ciin p_eqriv $.
$}

$(Inclusion of an indexed union of a power class in the power class of the
       union of its index.  Part of Exercise 24(b) of [Enderton] p. 33.
       (Contributed by NM, 25-Nov-2003.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_iunpwss $f set x $.
	f1_iunpwss $f class A $.
	i0_iunpwss $f set y $.
	p_iunpwss $p |- U_ x e. A ~P x C_ ~P U. A $= f0_iunpwss f1_iunpwss f0_iunpwss a_sup_set_class i0_iunpwss a_sup_set_class p_ssiun f0_iunpwss i0_iunpwss a_sup_set_class f1_iunpwss f0_iunpwss a_sup_set_class a_cpw p_eliun i0_iunpwss p_vex i0_iunpwss a_sup_set_class f0_iunpwss a_sup_set_class p_elpw i0_iunpwss a_sup_set_class f0_iunpwss a_sup_set_class a_cpw a_wcel i0_iunpwss a_sup_set_class f0_iunpwss a_sup_set_class a_wss f0_iunpwss f1_iunpwss p_rexbii i0_iunpwss a_sup_set_class f0_iunpwss f1_iunpwss f0_iunpwss a_sup_set_class a_cpw a_ciun a_wcel i0_iunpwss a_sup_set_class f0_iunpwss a_sup_set_class a_cpw a_wcel f0_iunpwss f1_iunpwss a_wrex i0_iunpwss a_sup_set_class f0_iunpwss a_sup_set_class a_wss f0_iunpwss f1_iunpwss a_wrex p_bitri i0_iunpwss p_vex i0_iunpwss a_sup_set_class f1_iunpwss a_cuni p_elpw f0_iunpwss f1_iunpwss p_uniiun f1_iunpwss a_cuni f0_iunpwss f1_iunpwss f0_iunpwss a_sup_set_class a_ciun i0_iunpwss a_sup_set_class p_sseq2i i0_iunpwss a_sup_set_class f1_iunpwss a_cuni a_cpw a_wcel i0_iunpwss a_sup_set_class f1_iunpwss a_cuni a_wss i0_iunpwss a_sup_set_class f0_iunpwss f1_iunpwss f0_iunpwss a_sup_set_class a_ciun a_wss p_bitri i0_iunpwss a_sup_set_class f0_iunpwss a_sup_set_class a_wss f0_iunpwss f1_iunpwss a_wrex i0_iunpwss a_sup_set_class f0_iunpwss f1_iunpwss f0_iunpwss a_sup_set_class a_ciun a_wss i0_iunpwss a_sup_set_class f0_iunpwss f1_iunpwss f0_iunpwss a_sup_set_class a_cpw a_ciun a_wcel i0_iunpwss a_sup_set_class f1_iunpwss a_cuni a_cpw a_wcel p_3imtr4i i0_iunpwss f0_iunpwss f1_iunpwss f0_iunpwss a_sup_set_class a_cpw a_ciun f1_iunpwss a_cuni a_cpw p_ssriv $.
$}

$(Relative intersection of a nonempty set.  (Contributed by Stefan O'Rear,
     3-Apr-2015.)  (Revised by Mario Carneiro, 5-Jun-2015.) $)

${
	$v A X  $.
	f0_rintn0 $f class A $.
	f1_rintn0 $f class X $.
	p_rintn0 $p |- ( ( X C_ ~P A /\ X =/= (/) ) -> ( A i^i |^| X ) = |^| X ) $= f0_rintn0 f1_rintn0 a_cint p_incom f1_rintn0 f0_rintn0 a_cpw p_intssuni2 f0_rintn0 a_cpw p_ssid f0_rintn0 a_cpw f0_rintn0 p_sspwuni f0_rintn0 a_cpw f0_rintn0 a_cpw a_wss f0_rintn0 a_cpw a_cuni f0_rintn0 a_wss p_mpbi f1_rintn0 f0_rintn0 a_cpw a_wss f1_rintn0 a_c0 a_wne a_wa f1_rintn0 a_cint f0_rintn0 a_cpw a_cuni f0_rintn0 p_syl6ss f1_rintn0 a_cint f0_rintn0 a_df-ss f1_rintn0 f0_rintn0 a_cpw a_wss f1_rintn0 a_c0 a_wne a_wa f1_rintn0 a_cint f0_rintn0 a_wss f1_rintn0 a_cint f0_rintn0 a_cin f1_rintn0 a_cint a_wceq p_sylib f1_rintn0 f0_rintn0 a_cpw a_wss f1_rintn0 a_c0 a_wne a_wa f0_rintn0 f1_rintn0 a_cint a_cin f1_rintn0 a_cint f0_rintn0 a_cin f1_rintn0 a_cint p_syl5eq $.
$}


