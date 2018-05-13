$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Introduce the Axiom of Power Sets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Power Sets.  An axiom of Zermelo-Fraenkel set theory.  It
       states that a set ` y ` exists that includes the power set of a given
       set ` x ` i.e. contains every subset of ` x ` .  The variant ~ axpow2
       uses explicit subset notation.  A version using class notation is
       ~ pwex .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v x y z w  $.
	$d x y z w  $.
	f0_ax-pow $f set x $.
	f1_ax-pow $f set y $.
	f2_ax-pow $f set z $.
	f3_ax-pow $f set w $.
	a_ax-pow $a |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $.
$}

$(Axiom of Power Sets expressed with the fewest number of different
       variables.  (Contributed by NM, 14-Aug-2003.) $)

${
	$v x y z  $.
	$d x y z w  $.
	f0_zfpow $f set x $.
	f1_zfpow $f set y $.
	f2_zfpow $f set z $.
	i0_zfpow $f set w $.
	p_zfpow $p |- E. x A. y ( A. x ( x e. y -> x e. z ) -> y e. x ) $= f2_zfpow f0_zfpow f1_zfpow i0_zfpow a_ax-pow i0_zfpow f0_zfpow f1_zfpow p_elequ1 i0_zfpow f0_zfpow f2_zfpow p_elequ1 i0_zfpow a_sup_set_class f0_zfpow a_sup_set_class a_wceq i0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel f0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel i0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel f0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel p_imbi12d i0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel i0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi f0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel f0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi i0_zfpow f0_zfpow p_cbvalv i0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel i0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi i0_zfpow a_wal f0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel f0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi f0_zfpow a_wal f1_zfpow a_sup_set_class f0_zfpow a_sup_set_class a_wcel p_imbi1i i0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel i0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi i0_zfpow a_wal f1_zfpow a_sup_set_class f0_zfpow a_sup_set_class a_wcel a_wi f0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel f0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi f0_zfpow a_wal f1_zfpow a_sup_set_class f0_zfpow a_sup_set_class a_wcel a_wi f1_zfpow p_albii i0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel i0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi i0_zfpow a_wal f1_zfpow a_sup_set_class f0_zfpow a_sup_set_class a_wcel a_wi f1_zfpow a_wal f0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel f0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi f0_zfpow a_wal f1_zfpow a_sup_set_class f0_zfpow a_sup_set_class a_wcel a_wi f1_zfpow a_wal f0_zfpow p_exbii i0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel i0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi i0_zfpow a_wal f1_zfpow a_sup_set_class f0_zfpow a_sup_set_class a_wcel a_wi f1_zfpow a_wal f0_zfpow a_wex f0_zfpow a_sup_set_class f1_zfpow a_sup_set_class a_wcel f0_zfpow a_sup_set_class f2_zfpow a_sup_set_class a_wcel a_wi f0_zfpow a_wal f1_zfpow a_sup_set_class f0_zfpow a_sup_set_class a_wcel a_wi f1_zfpow a_wal f0_zfpow a_wex p_mpbi $.
$}

$(A variant of the Axiom of Power Sets ~ ax-pow using subset notation.
       Problem in {BellMachover] p. 466.  (Contributed by NM, 4-Jun-2006.) $)

${
	$v x y z  $.
	$d x y z w  $.
	f0_axpow2 $f set x $.
	f1_axpow2 $f set y $.
	f2_axpow2 $f set z $.
	i0_axpow2 $f set w $.
	p_axpow2 $p |- E. y A. z ( z C_ x -> z e. y ) $= f0_axpow2 f1_axpow2 f2_axpow2 i0_axpow2 a_ax-pow i0_axpow2 f2_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class p_dfss2 f2_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class a_wss i0_axpow2 a_sup_set_class f2_axpow2 a_sup_set_class a_wcel i0_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class a_wcel a_wi i0_axpow2 a_wal f2_axpow2 a_sup_set_class f1_axpow2 a_sup_set_class a_wcel p_imbi1i f2_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class a_wss f2_axpow2 a_sup_set_class f1_axpow2 a_sup_set_class a_wcel a_wi i0_axpow2 a_sup_set_class f2_axpow2 a_sup_set_class a_wcel i0_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class a_wcel a_wi i0_axpow2 a_wal f2_axpow2 a_sup_set_class f1_axpow2 a_sup_set_class a_wcel a_wi f2_axpow2 p_albii f2_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class a_wss f2_axpow2 a_sup_set_class f1_axpow2 a_sup_set_class a_wcel a_wi f2_axpow2 a_wal i0_axpow2 a_sup_set_class f2_axpow2 a_sup_set_class a_wcel i0_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class a_wcel a_wi i0_axpow2 a_wal f2_axpow2 a_sup_set_class f1_axpow2 a_sup_set_class a_wcel a_wi f2_axpow2 a_wal f1_axpow2 p_exbii f2_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class a_wss f2_axpow2 a_sup_set_class f1_axpow2 a_sup_set_class a_wcel a_wi f2_axpow2 a_wal f1_axpow2 a_wex i0_axpow2 a_sup_set_class f2_axpow2 a_sup_set_class a_wcel i0_axpow2 a_sup_set_class f0_axpow2 a_sup_set_class a_wcel a_wi i0_axpow2 a_wal f2_axpow2 a_sup_set_class f1_axpow2 a_sup_set_class a_wcel a_wi f2_axpow2 a_wal f1_axpow2 a_wex p_mpbir $.
$}

$(A variant of the Axiom of Power Sets ~ ax-pow .  For any set ` x ` ,
       there exists a set ` y ` whose members are exactly the subsets of ` x `
       i.e. the power set of ` x ` .  Axiom Pow of [BellMachover] p. 466.
       (Contributed by NM, 4-Jun-2006.) $)

${
	$v x y z  $.
	$d x y z  $.
	f0_axpow3 $f set x $.
	f1_axpow3 $f set y $.
	f2_axpow3 $f set z $.
	p_axpow3 $p |- E. y A. z ( z C_ x <-> z e. y ) $= f0_axpow3 f1_axpow3 f2_axpow3 p_axpow2 f2_axpow3 a_sup_set_class f0_axpow3 a_sup_set_class a_wss f1_axpow3 f2_axpow3 p_bm1.3ii f2_axpow3 a_sup_set_class f0_axpow3 a_sup_set_class a_wss f2_axpow3 a_sup_set_class f1_axpow3 a_sup_set_class a_wcel p_bicom f2_axpow3 a_sup_set_class f0_axpow3 a_sup_set_class a_wss f2_axpow3 a_sup_set_class f1_axpow3 a_sup_set_class a_wcel a_wb f2_axpow3 a_sup_set_class f1_axpow3 a_sup_set_class a_wcel f2_axpow3 a_sup_set_class f0_axpow3 a_sup_set_class a_wss a_wb f2_axpow3 p_albii f2_axpow3 a_sup_set_class f0_axpow3 a_sup_set_class a_wss f2_axpow3 a_sup_set_class f1_axpow3 a_sup_set_class a_wcel a_wb f2_axpow3 a_wal f2_axpow3 a_sup_set_class f1_axpow3 a_sup_set_class a_wcel f2_axpow3 a_sup_set_class f0_axpow3 a_sup_set_class a_wss a_wb f2_axpow3 a_wal f1_axpow3 p_exbii f2_axpow3 a_sup_set_class f0_axpow3 a_sup_set_class a_wss f2_axpow3 a_sup_set_class f1_axpow3 a_sup_set_class a_wcel a_wb f2_axpow3 a_wal f1_axpow3 a_wex f2_axpow3 a_sup_set_class f1_axpow3 a_sup_set_class a_wcel f2_axpow3 a_sup_set_class f0_axpow3 a_sup_set_class a_wss a_wb f2_axpow3 a_wal f1_axpow3 a_wex p_mpbir $.
$}

$(Every set is an element of some other set.  See ~ elALT for a shorter
       proof using more axioms.  (Contributed by NM, 4-Jan-2002.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x y  $.
	$d x y z  $.
	f0_el $f set x $.
	f1_el $f set y $.
	i0_el $f set z $.
	p_el $p |- E. y x e. y $= f1_el i0_el f0_el p_zfpow i0_el f0_el f1_el a_ax-14 i0_el a_sup_set_class f0_el a_sup_set_class a_wceq f1_el a_sup_set_class i0_el a_sup_set_class a_wcel f1_el a_sup_set_class f0_el a_sup_set_class a_wcel a_wi f1_el p_alrimiv i0_el f0_el f1_el a_ax-13 i0_el a_sup_set_class f0_el a_sup_set_class a_wceq f1_el a_sup_set_class i0_el a_sup_set_class a_wcel f1_el a_sup_set_class f0_el a_sup_set_class a_wcel a_wi f1_el a_wal i0_el a_sup_set_class f1_el a_sup_set_class a_wcel f0_el a_sup_set_class f1_el a_sup_set_class a_wcel p_embantd f1_el a_sup_set_class i0_el a_sup_set_class a_wcel f1_el a_sup_set_class f0_el a_sup_set_class a_wcel a_wi f1_el a_wal i0_el a_sup_set_class f1_el a_sup_set_class a_wcel a_wi f0_el a_sup_set_class f1_el a_sup_set_class a_wcel i0_el f0_el p_spimv f1_el a_sup_set_class i0_el a_sup_set_class a_wcel f1_el a_sup_set_class f0_el a_sup_set_class a_wcel a_wi f1_el a_wal i0_el a_sup_set_class f1_el a_sup_set_class a_wcel a_wi i0_el a_wal f0_el a_sup_set_class f1_el a_sup_set_class a_wcel f1_el p_eximi f1_el a_sup_set_class i0_el a_sup_set_class a_wcel f1_el a_sup_set_class f0_el a_sup_set_class a_wcel a_wi f1_el a_wal i0_el a_sup_set_class f1_el a_sup_set_class a_wcel a_wi i0_el a_wal f1_el a_wex f0_el a_sup_set_class f1_el a_sup_set_class a_wcel f1_el a_wex a_ax-mp $.
$}

$(Power set axiom expressed in class notation.  Axiom 4 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 25-Jul-2011.) $)

${
	$v A  $.
	$d A x y z  $.
	f0_pwex $f class A $.
	i0_pwex $f set x $.
	i1_pwex $f set y $.
	i2_pwex $f set z $.
	e0_pwex $e |- A e. _V $.
	p_pwex $p |- ~P A e. _V $= e0_pwex i2_pwex a_sup_set_class f0_pwex p_pweq i2_pwex a_sup_set_class f0_pwex a_wceq i2_pwex a_sup_set_class a_cpw f0_pwex a_cpw a_cvv p_eleq1d i1_pwex i2_pwex a_sup_set_class a_df-pw i2_pwex i0_pwex i1_pwex p_axpow2 i1_pwex a_sup_set_class i2_pwex a_sup_set_class a_wss i0_pwex i1_pwex p_bm1.3ii i1_pwex a_sup_set_class i2_pwex a_sup_set_class a_wss i1_pwex i0_pwex a_sup_set_class p_abeq2 i0_pwex a_sup_set_class i1_pwex a_sup_set_class i2_pwex a_sup_set_class a_wss i1_pwex a_cab a_wceq i1_pwex a_sup_set_class i0_pwex a_sup_set_class a_wcel i1_pwex a_sup_set_class i2_pwex a_sup_set_class a_wss a_wb i1_pwex a_wal i0_pwex p_exbii i0_pwex a_sup_set_class i1_pwex a_sup_set_class i2_pwex a_sup_set_class a_wss i1_pwex a_cab a_wceq i0_pwex a_wex i1_pwex a_sup_set_class i0_pwex a_sup_set_class a_wcel i1_pwex a_sup_set_class i2_pwex a_sup_set_class a_wss a_wb i1_pwex a_wal i0_pwex a_wex p_mpbir i0_pwex i1_pwex a_sup_set_class i2_pwex a_sup_set_class a_wss i1_pwex a_cab p_issetri i2_pwex a_sup_set_class a_cpw i1_pwex a_sup_set_class i2_pwex a_sup_set_class a_wss i1_pwex a_cab a_cvv p_eqeltri i2_pwex a_sup_set_class a_cpw a_cvv a_wcel f0_pwex a_cpw a_cvv a_wcel i2_pwex f0_pwex p_vtocl $.
$}

$(Power set axiom expressed in class notation, with the sethood
       requirement as an antecedent.  Axiom 4 of [TakeutiZaring] p. 17.
       (Contributed by NM, 30-Oct-2003.) $)

${
	$v A V  $.
	$d x A  $.
	f0_pwexg $f class A $.
	f1_pwexg $f class V $.
	i0_pwexg $f set x $.
	p_pwexg $p |- ( A e. V -> ~P A e. _V ) $= i0_pwexg a_sup_set_class f0_pwexg p_pweq i0_pwexg a_sup_set_class f0_pwexg a_wceq i0_pwexg a_sup_set_class a_cpw f0_pwexg a_cpw a_cvv p_eleq1d i0_pwexg p_vex i0_pwexg a_sup_set_class p_pwex i0_pwexg a_sup_set_class a_cpw a_cvv a_wcel f0_pwexg a_cpw a_cvv a_wcel i0_pwexg f0_pwexg f1_pwexg p_vtoclg $.
$}

$(Existence of a class of subsets.  (Contributed by NM, 15-Jul-2006.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v ph x A V  $.
	$d x A  $.
	f0_abssexg $f wff ph $.
	f1_abssexg $f set x $.
	f2_abssexg $f class A $.
	f3_abssexg $f class V $.
	p_abssexg $p |- ( A e. V -> { x | ( x C_ A /\ ph ) } e. _V ) $= f2_abssexg f3_abssexg p_pwexg f1_abssexg f2_abssexg a_df-pw f2_abssexg a_cpw f1_abssexg a_sup_set_class f2_abssexg a_wss f1_abssexg a_cab a_cvv p_eleq1i f1_abssexg a_sup_set_class f2_abssexg a_wss f0_abssexg p_simpl f1_abssexg a_sup_set_class f2_abssexg a_wss f0_abssexg a_wa f1_abssexg a_sup_set_class f2_abssexg a_wss f1_abssexg p_ss2abi f1_abssexg a_sup_set_class f2_abssexg a_wss f0_abssexg a_wa f1_abssexg a_cab f1_abssexg a_sup_set_class f2_abssexg a_wss f1_abssexg a_cab a_cvv p_ssexg f1_abssexg a_sup_set_class f2_abssexg a_wss f0_abssexg a_wa f1_abssexg a_cab f1_abssexg a_sup_set_class f2_abssexg a_wss f1_abssexg a_cab a_wss f1_abssexg a_sup_set_class f2_abssexg a_wss f1_abssexg a_cab a_cvv a_wcel f1_abssexg a_sup_set_class f2_abssexg a_wss f0_abssexg a_wa f1_abssexg a_cab a_cvv a_wcel p_mpan f2_abssexg a_cpw a_cvv a_wcel f1_abssexg a_sup_set_class f2_abssexg a_wss f1_abssexg a_cab a_cvv a_wcel f1_abssexg a_sup_set_class f2_abssexg a_wss f0_abssexg a_wa f1_abssexg a_cab a_cvv a_wcel p_sylbi f2_abssexg f3_abssexg a_wcel f2_abssexg a_cpw a_cvv a_wcel f1_abssexg a_sup_set_class f2_abssexg a_wss f0_abssexg a_wa f1_abssexg a_cab a_cvv a_wcel p_syl $.
$}

$(A singleton is a set.  Theorem 7.13 of [Quine] p. 51, but proved using
       only Extensionality, Power Set, and Separation.  Unlike the proof of
       ~ zfpair , Replacement is not needed.  (Contributed by NM, 7-Aug-1994.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.)  See also ~ snex .
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v A  $.
	$d A  $.
	f0_snexALT $f class A $.
	p_snexALT $p |- { A } e. _V $= f0_snexALT p_snsspw f0_snexALT a_csn f0_snexALT a_cpw a_cvv p_ssexg f0_snexALT a_csn f0_snexALT a_cpw a_wss f0_snexALT a_cpw a_cvv a_wcel f0_snexALT a_csn a_cvv a_wcel p_mpan f0_snexALT a_cvv p_pwexg f0_snexALT a_cvv a_wcel f0_snexALT a_cpw a_cvv a_wcel p_con3i f0_snexALT p_snprc f0_snexALT a_cvv a_wcel a_wn f0_snexALT a_csn a_c0 a_wceq p_biimpi p_0ex f0_snexALT a_cvv a_wcel a_wn f0_snexALT a_csn a_c0 a_cvv p_syl6eqel f0_snexALT a_cpw a_cvv a_wcel a_wn f0_snexALT a_cvv a_wcel a_wn f0_snexALT a_csn a_cvv a_wcel p_syl f0_snexALT a_cpw a_cvv a_wcel f0_snexALT a_csn a_cvv a_wcel p_pm2.61i $.
$}

$(The power set of the empty set (the ordinal 1) is a set.  See also
     ~ p0exALT .  (Contributed by NM, 23-Dec-1993.) $)

${
	$v  $.
	p_p0ex $p |- { (/) } e. _V $= p_pw0 p_0ex a_c0 p_pwex a_c0 a_cpw a_c0 a_csn a_cvv p_eqeltrri $.
$}

$(The power set of the empty set (the ordinal 1) is a set.  Alternate proof
     which is longer and quite different from the proof of ~ p0ex if ~ snexALT
     is expanded.  (Contributed by NM, 23-Dec-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v  $.
	p_p0exALT $p |- { (/) } e. _V $= a_c0 p_snexALT $.
$}

$(The power set of the power set of the empty set (the ordinal 2) is a set.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v  $.
	p_pp0ex $p |- { (/) , { (/) } } e. _V $= p_pwpw0 p_p0ex a_c0 a_csn p_pwex a_c0 a_csn a_cpw a_c0 a_c0 a_csn a_cpr a_cvv p_eqeltrri $.
$}

$(The ordinal number 3 is a set, proved without the Axiom of Union
     ~ ax-un .  (Contributed by NM, 2-May-2009.) $)

${
	$v  $.
	p_ord3ex $p |- { (/) , { (/) } , { (/) , { (/) } } } e. _V $= a_c0 a_c0 a_csn a_c0 a_c0 a_csn a_cpr a_df-tp a_c0 a_c0 a_csn p_pwpr p_pp0ex a_c0 a_c0 a_csn a_cpr p_pwex a_c0 a_c0 a_csn a_cpr a_cpw a_c0 a_c0 a_csn a_cpr a_c0 a_csn a_csn a_c0 a_c0 a_csn a_cpr a_cpr a_cun a_cvv p_eqeltrri a_c0 a_csn a_csn a_c0 a_c0 a_csn a_cpr p_snsspr2 a_c0 a_c0 a_csn a_cpr a_csn a_c0 a_csn a_csn a_c0 a_c0 a_csn a_cpr a_cpr a_c0 a_c0 a_csn a_cpr p_unss2 a_c0 a_c0 a_csn a_cpr a_csn a_c0 a_csn a_csn a_c0 a_c0 a_csn a_cpr a_cpr a_wss a_c0 a_c0 a_csn a_cpr a_c0 a_c0 a_csn a_cpr a_csn a_cun a_c0 a_c0 a_csn a_cpr a_c0 a_csn a_csn a_c0 a_c0 a_csn a_cpr a_cpr a_cun a_wss a_ax-mp a_c0 a_c0 a_csn a_cpr a_c0 a_c0 a_csn a_cpr a_csn a_cun a_c0 a_c0 a_csn a_cpr a_c0 a_csn a_csn a_c0 a_c0 a_csn a_cpr a_cpr a_cun p_ssexi a_c0 a_c0 a_csn a_c0 a_c0 a_csn a_cpr a_ctp a_c0 a_c0 a_csn a_cpr a_c0 a_c0 a_csn a_cpr a_csn a_cun a_cvv p_eqeltri $.
$}

$(At least two sets exist (or in terms of first-order logic, the universe
       of discourse has two or more objects).  Note that we may not substitute
       the same variable for both ` x ` and ` y ` (as indicated by the distinct
       variable requirement), for otherwise we would contradict ~ stdpc6 .

       This theorem is proved directly from set theory axioms (no set theory
       definitions) and does not use ~ ax-ext or ~ ax-sep .  See ~ dtruALT for
       a shorter proof using these axioms.

       The proof makes use of dummy variables ` z ` and ` w ` which do not
       appear in the final theorem.  They must be distinct from each other and
       from ` x ` and ` y ` .  In other words, if we were to substitute ` x `
       for ` z ` throughout the proof, the proof would fail.  Although this
       requirement is made explicitly in the set.mm source file, it is implicit
       on the web page (i.e. doesn't appear in the "Distinct variable group").
       (Contributed by NM, 7-Nov-2006.) $)

${
	$v x y  $.
	$d w x y z  $.
	f0_dtru $f set x $.
	f1_dtru $f set y $.
	i0_dtru $f set z $.
	i1_dtru $f set w $.
	p_dtru $p |- -. A. x x = y $= f0_dtru i1_dtru p_el i0_dtru f0_dtru a_ax-nul f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn f0_dtru p_sp f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn f0_dtru a_wal f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn i0_dtru p_eximi f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn f0_dtru a_wal i0_dtru a_wex f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn i0_dtru a_wex a_ax-mp f0_dtru a_sup_set_class i1_dtru a_sup_set_class a_wcel f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn i1_dtru i0_dtru p_eeanv f0_dtru a_sup_set_class i1_dtru a_sup_set_class a_wcel f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn a_wa i0_dtru a_wex i1_dtru a_wex f0_dtru a_sup_set_class i1_dtru a_sup_set_class a_wcel i1_dtru a_wex f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn i0_dtru a_wex p_mpbir2an i1_dtru i0_dtru f0_dtru a_ax-14 i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq f0_dtru a_sup_set_class i1_dtru a_sup_set_class a_wcel f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel p_com12 f0_dtru a_sup_set_class i1_dtru a_sup_set_class a_wcel i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel p_con3and f0_dtru a_sup_set_class i1_dtru a_sup_set_class a_wcel f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn a_wa i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq a_wn i1_dtru i0_dtru p_2eximi f0_dtru a_sup_set_class i1_dtru a_sup_set_class a_wcel f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wcel a_wn a_wa i0_dtru a_wex i1_dtru a_wex i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq a_wn i0_dtru a_wex i1_dtru a_wex a_ax-mp i0_dtru f1_dtru i1_dtru p_equequ2 i0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq i1_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq p_notbid f0_dtru i1_dtru f1_dtru a_ax-8 f0_dtru a_sup_set_class i1_dtru a_sup_set_class a_wceq f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq i1_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq p_con3d i1_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru i1_dtru p_spimev i0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq a_wn i1_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_wex p_syl6bi f0_dtru i0_dtru f1_dtru a_ax-8 f0_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq i0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq p_con3d i0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru i0_dtru p_spimev i0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_wex i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq a_wn p_a1d i0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq a_wn f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_wex a_wi p_pm2.61i i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq a_wn f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_wex i1_dtru i0_dtru p_exlimivv i1_dtru a_sup_set_class i0_dtru a_sup_set_class a_wceq a_wn i0_dtru a_wex i1_dtru a_wex f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_wex a_ax-mp f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq f0_dtru p_exnal f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq a_wn f0_dtru a_wex f0_dtru a_sup_set_class f1_dtru a_sup_set_class a_wceq f0_dtru a_wal a_wn p_mpbi $.
$}

$(This theorem shows that axiom ~ ax-16 is redundant in the presence of
       theorem ~ dtru , which states simply that at least two things exist.
       This justifies the remark at
       ~ http://us.metamath.org/mpeuni/mmzfcnd.html#twoness (which links to
       this theorem).  (Contributed by NM, 7-Nov-2006.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_ax16b $f wff ph $.
	f1_ax16b $f set x $.
	f2_ax16b $f set y $.
	p_ax16b $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= f1_ax16b f2_ax16b p_dtru f1_ax16b a_sup_set_class f2_ax16b a_sup_set_class a_wceq f1_ax16b a_wal f0_ax16b f0_ax16b f1_ax16b a_wal a_wi p_pm2.21i $.
$}

$(Existential uniqueness implies there is a value for which the wff
       argument is false.  (Contributed by NM, 24-Oct-2010.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_eunex $f wff ph $.
	f1_eunex $f set x $.
	i0_eunex $f set y $.
	p_eunex $p |- ( E! x ph -> E. x -. ph ) $= f1_eunex i0_eunex p_dtru f0_eunex f1_eunex a_sup_set_class i0_eunex a_sup_set_class a_wceq f1_eunex p_alim f0_eunex f1_eunex a_sup_set_class i0_eunex a_sup_set_class a_wceq a_wi f1_eunex a_wal f0_eunex f1_eunex a_wal f1_eunex a_sup_set_class i0_eunex a_sup_set_class a_wceq f1_eunex a_wal p_mtoi f0_eunex f1_eunex a_sup_set_class i0_eunex a_sup_set_class a_wceq a_wi f1_eunex a_wal f0_eunex f1_eunex a_wal a_wn i0_eunex p_exlimiv f0_eunex f1_eunex a_sup_set_class i0_eunex a_sup_set_class a_wceq a_wi f1_eunex a_wal i0_eunex a_wex f0_eunex f1_eunex a_wal a_wn f0_eunex f1_eunex a_wex p_adantl f0_eunex i0_eunex p_nfv f0_eunex f1_eunex i0_eunex p_eu3 f0_eunex f1_eunex p_exnal f0_eunex f1_eunex a_wex f0_eunex f1_eunex a_sup_set_class i0_eunex a_sup_set_class a_wceq a_wi f1_eunex a_wal i0_eunex a_wex a_wa f0_eunex f1_eunex a_wal a_wn f0_eunex f1_eunex a_weu f0_eunex a_wn f1_eunex a_wex p_3imtr4i $.
$}

$(A set variable is not free from itself.  The proof relies on ~ dtru ,
       that is, it is not true in a one-element domain.  (Contributed by Mario
       Carneiro, 8-Oct-2016.) $)

${
	$v x  $.
	$d w x y z  $.
	f0_nfnid $f set x $.
	i0_nfnid $f set y $.
	i1_nfnid $f set z $.
	i2_nfnid $f set w $.
	p_nfnid $p |- -. F/_ x x $= i1_nfnid i2_nfnid p_dtru i1_nfnid i2_nfnid i0_nfnid a_ax-ext i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i0_nfnid a_wal i1_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wceq i2_nfnid p_sps i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i0_nfnid a_wal i2_nfnid a_wal i1_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wceq i1_nfnid p_alimi i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i0_nfnid a_wal i2_nfnid a_wal i1_nfnid a_wal i1_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wceq i1_nfnid a_wal p_mto f0_nfnid i0_nfnid f0_nfnid a_sup_set_class a_df-nfc i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid i1_nfnid i2_nfnid p_sbnf2 i1_nfnid f0_nfnid i0_nfnid p_elsb4 i2_nfnid f0_nfnid i0_nfnid p_elsb4 i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid i1_nfnid a_wsb i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid i2_nfnid a_wsb i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel p_bibi12i i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid i1_nfnid a_wsb i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid i2_nfnid a_wsb a_wb i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i1_nfnid i2_nfnid p_2albii i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid a_wnf i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid i1_nfnid a_wsb i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid i2_nfnid a_wsb a_wb i2_nfnid a_wal i1_nfnid a_wal i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i2_nfnid a_wal i1_nfnid a_wal p_bitri i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid a_wnf i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i2_nfnid a_wal i1_nfnid a_wal i0_nfnid p_albii i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i0_nfnid i1_nfnid i2_nfnid p_alrot3 f0_nfnid f0_nfnid a_sup_set_class a_wnfc i0_nfnid a_sup_set_class f0_nfnid a_sup_set_class a_wcel f0_nfnid a_wnf i0_nfnid a_wal i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i2_nfnid a_wal i1_nfnid a_wal i0_nfnid a_wal i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i0_nfnid a_wal i2_nfnid a_wal i1_nfnid a_wal p_3bitri f0_nfnid f0_nfnid a_sup_set_class a_wnfc i0_nfnid a_sup_set_class i1_nfnid a_sup_set_class a_wcel i0_nfnid a_sup_set_class i2_nfnid a_sup_set_class a_wcel a_wb i0_nfnid a_wal i2_nfnid a_wal i1_nfnid a_wal p_mtbir $.
$}

$(The "distinctor" expression ` -. A. x x = y ` , stating that ` x ` and
       ` y ` are not the same variable, can be written in terms of ` F/ ` in
       the obvious way.  This theorem is not true in a one-element domain,
       because then ` F/_ x y ` and ` A. x x = y ` will both be true.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)

${
	$v x y  $.
	$d x y  $.
	$d x  $.
	$d y  $.
	f0_nfcvb $f set x $.
	f1_nfcvb $f set y $.
	p_nfcvb $p |- ( F/_ x y <-> -. A. x x = y ) $= f1_nfcvb p_nfnid f0_nfcvb a_sup_set_class f1_nfcvb a_sup_set_class a_wceq f0_nfcvb a_wal f1_nfcvb a_sup_set_class p_eqidd f0_nfcvb f1_nfcvb f1_nfcvb a_sup_set_class f1_nfcvb a_sup_set_class p_drnfc1 f0_nfcvb a_sup_set_class f1_nfcvb a_sup_set_class a_wceq f0_nfcvb a_wal f0_nfcvb f1_nfcvb a_sup_set_class a_wnfc f1_nfcvb f1_nfcvb a_sup_set_class a_wnfc p_mtbiri f0_nfcvb a_sup_set_class f1_nfcvb a_sup_set_class a_wceq f0_nfcvb a_wal f0_nfcvb f1_nfcvb a_sup_set_class a_wnfc p_con2i f0_nfcvb f1_nfcvb p_nfcvf f0_nfcvb f1_nfcvb a_sup_set_class a_wnfc f0_nfcvb a_sup_set_class f1_nfcvb a_sup_set_class a_wceq f0_nfcvb a_wal a_wn p_impbii $.
$}

$(A class is a subclass of the power class of its union.  Exercise 6(b) of
       [Enderton] p. 38.  (Contributed by NM, 14-Oct-1996.) $)

${
	$v A  $.
	$d A x  $.
	f0_pwuni $f class A $.
	i0_pwuni $f set x $.
	p_pwuni $p |- A C_ ~P U. A $= i0_pwuni a_sup_set_class f0_pwuni p_elssuni i0_pwuni p_vex i0_pwuni a_sup_set_class f0_pwuni a_cuni p_elpw i0_pwuni a_sup_set_class f0_pwuni a_wcel i0_pwuni a_sup_set_class f0_pwuni a_cuni a_wss i0_pwuni a_sup_set_class f0_pwuni a_cuni a_cpw a_wcel p_sylibr i0_pwuni f0_pwuni f0_pwuni a_cuni a_cpw p_ssriv $.
$}

$(A version of ~ dtru ("two things exist") with a shorter proof that uses
       more axioms but may be easier to understand.

       Assuming that ZF set theory is consistent, we cannot prove this theorem
       unless we specify that ` x ` and ` y ` be distinct.  Specifically,
       theorem ~ spcev requires that ` x ` must not occur in the subexpression
       ` -. y = { (/) } ` in step 4 nor in the subexpression ` -. y = (/) ` in
       step 9.  The proof verifier will require that ` x ` and ` y ` be in a
       distinct variable group to ensure this.  You can check this by deleting
       the $d statement in set.mm and rerunning the verifier, which will print
       a detailed explanation of the distinct variable violation.  (Contributed
       by NM, 15-Jul-1994.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v x y  $.
	$d x y  $.
	f0_dtruALT $f set x $.
	f1_dtruALT $f set y $.
	p_dtruALT $p |- -. A. x x = y $= f1_dtruALT a_sup_set_class p_0inp0 p_p0ex f0_dtruALT a_sup_set_class a_c0 a_csn f1_dtruALT a_sup_set_class p_eqeq2 f0_dtruALT a_sup_set_class a_c0 a_csn a_wceq f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq f1_dtruALT a_sup_set_class a_c0 a_csn a_wceq p_notbid f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq a_wn f1_dtruALT a_sup_set_class a_c0 a_csn a_wceq a_wn f0_dtruALT a_c0 a_csn p_spcev f1_dtruALT a_sup_set_class a_c0 a_wceq f1_dtruALT a_sup_set_class a_c0 a_csn a_wceq a_wn f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq a_wn f0_dtruALT a_wex p_syl p_0ex f0_dtruALT a_sup_set_class a_c0 f1_dtruALT a_sup_set_class p_eqeq2 f0_dtruALT a_sup_set_class a_c0 a_wceq f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq f1_dtruALT a_sup_set_class a_c0 a_wceq p_notbid f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq a_wn f1_dtruALT a_sup_set_class a_c0 a_wceq a_wn f0_dtruALT a_c0 p_spcev f1_dtruALT a_sup_set_class a_c0 a_wceq f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq a_wn f0_dtruALT a_wex p_pm2.61i f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq f0_dtruALT p_exnal f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class p_eqcom f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq f0_dtruALT a_sup_set_class f1_dtruALT a_sup_set_class a_wceq f0_dtruALT p_albii f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq a_wn f0_dtruALT a_wex f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq f0_dtruALT a_wal f0_dtruALT a_sup_set_class f1_dtruALT a_sup_set_class a_wceq f0_dtruALT a_wal p_xchbinx f1_dtruALT a_sup_set_class f0_dtruALT a_sup_set_class a_wceq a_wn f0_dtruALT a_wex f0_dtruALT a_sup_set_class f1_dtruALT a_sup_set_class a_wceq f0_dtruALT a_wal a_wn p_mpbi $.
$}

$(Corollary of ~ dtru .  This example illustrates the danger of blindly
       trusting the standard Deduction Theorem without accounting for free
       variables: the theorem form of this deduction is not valid, as shown by
       ~ dtrucor2 .  (Contributed by NM, 27-Jun-2002.) $)

${
	$v x y  $.
	$d x y  $.
	f0_dtrucor $f set x $.
	f1_dtrucor $f set y $.
	e0_dtrucor $e |- x = y $.
	p_dtrucor $p |- x =/= y $= f0_dtrucor f1_dtrucor p_dtru f0_dtrucor a_sup_set_class f1_dtrucor a_sup_set_class a_wceq f0_dtrucor a_wal f0_dtrucor a_sup_set_class f1_dtrucor a_sup_set_class a_wne p_pm2.21i e0_dtrucor f0_dtrucor a_sup_set_class f1_dtrucor a_sup_set_class a_wceq f0_dtrucor a_sup_set_class f1_dtrucor a_sup_set_class a_wne f0_dtrucor p_mpg $.
$}

$(The theorem form of the deduction ~ dtrucor leads to a contradiction, as
       mentioned in the "Wrong!" example at
       ~ http://us.metamath.org/mpeuni/mmdeduction.html#bad .  (Contributed by
       NM, 20-Oct-2007.) $)

${
	$v ph x y  $.
	f0_dtrucor2 $f wff ph $.
	f1_dtrucor2 $f set x $.
	f2_dtrucor2 $f set y $.
	e0_dtrucor2 $e |- ( x = y -> x =/= y ) $.
	p_dtrucor2 $p |- ( ph /\ -. ph ) $= f1_dtrucor2 f2_dtrucor2 p_a9e e0_dtrucor2 f1_dtrucor2 a_sup_set_class f2_dtrucor2 a_sup_set_class a_wceq f1_dtrucor2 a_sup_set_class f2_dtrucor2 a_sup_set_class p_necon2bi f1_dtrucor2 a_sup_set_class f2_dtrucor2 a_sup_set_class a_wceq p_pm2.01 f1_dtrucor2 a_sup_set_class f2_dtrucor2 a_sup_set_class a_wceq f1_dtrucor2 a_sup_set_class f2_dtrucor2 a_sup_set_class a_wceq a_wn a_wi f1_dtrucor2 a_sup_set_class f2_dtrucor2 a_sup_set_class a_wceq a_wn a_ax-mp f1_dtrucor2 a_sup_set_class f2_dtrucor2 a_sup_set_class a_wceq f1_dtrucor2 p_nex f1_dtrucor2 a_sup_set_class f2_dtrucor2 a_sup_set_class a_wceq f1_dtrucor2 a_wex f0_dtrucor2 f0_dtrucor2 a_wn a_wa p_pm2.24ii $.
$}

$(Demonstration of a theorem (scheme) that requires (meta)variables ` x `
       and ` y ` to be distinct, but no others.  It bundles the theorem schemes
       ` E. x ( x = y -> x e. x ) ` and ` E. x ( x = y -> y e. x ) ` .  Compare
       ~ dvdemo2 .  ("Bundles" is a term introduced by Raph Levien.)
       (Contributed by NM, 1-Dec-2006.) $)

${
	$v x y z  $.
	$d x y  $.
	f0_dvdemo1 $f set x $.
	f1_dvdemo1 $f set y $.
	f2_dvdemo1 $f set z $.
	p_dvdemo1 $p |- E. x ( x = y -> z e. x ) $= f0_dvdemo1 f1_dvdemo1 p_dtru f0_dvdemo1 a_sup_set_class f1_dvdemo1 a_sup_set_class a_wceq f0_dvdemo1 p_exnal f0_dvdemo1 a_sup_set_class f1_dvdemo1 a_sup_set_class a_wceq a_wn f0_dvdemo1 a_wex f0_dvdemo1 a_sup_set_class f1_dvdemo1 a_sup_set_class a_wceq f0_dvdemo1 a_wal a_wn p_mpbir f0_dvdemo1 a_sup_set_class f1_dvdemo1 a_sup_set_class a_wceq f2_dvdemo1 a_sup_set_class f0_dvdemo1 a_sup_set_class a_wcel p_pm2.21 f0_dvdemo1 a_sup_set_class f1_dvdemo1 a_sup_set_class a_wceq a_wn f0_dvdemo1 a_sup_set_class f1_dvdemo1 a_sup_set_class a_wceq f2_dvdemo1 a_sup_set_class f0_dvdemo1 a_sup_set_class a_wcel a_wi f0_dvdemo1 p_eximi f0_dvdemo1 a_sup_set_class f1_dvdemo1 a_sup_set_class a_wceq a_wn f0_dvdemo1 a_wex f0_dvdemo1 a_sup_set_class f1_dvdemo1 a_sup_set_class a_wceq f2_dvdemo1 a_sup_set_class f0_dvdemo1 a_sup_set_class a_wcel a_wi f0_dvdemo1 a_wex a_ax-mp $.
$}

$(Demonstration of a theorem (scheme) that requires (meta)variables ` x `
       and ` z ` to be distinct, but no others.  It bundles the theorem schemes
       ` E. x ( x = x -> z e. x ) ` and ` E. x ( x = y -> y e. x ) ` .  Compare
       ~ dvdemo1 .  (Contributed by NM, 1-Dec-2006.) $)

${
	$v x y z  $.
	$d x z  $.
	f0_dvdemo2 $f set x $.
	f1_dvdemo2 $f set y $.
	f2_dvdemo2 $f set z $.
	p_dvdemo2 $p |- E. x ( x = y -> z e. x ) $= f2_dvdemo2 f0_dvdemo2 p_el f2_dvdemo2 a_sup_set_class f0_dvdemo2 a_sup_set_class a_wcel f0_dvdemo2 a_sup_set_class f1_dvdemo2 a_sup_set_class a_wceq a_ax-1 f2_dvdemo2 a_sup_set_class f0_dvdemo2 a_sup_set_class a_wcel f0_dvdemo2 a_sup_set_class f1_dvdemo2 a_sup_set_class a_wceq f2_dvdemo2 a_sup_set_class f0_dvdemo2 a_sup_set_class a_wcel a_wi f0_dvdemo2 p_eximi f2_dvdemo2 a_sup_set_class f0_dvdemo2 a_sup_set_class a_wcel f0_dvdemo2 a_wex f0_dvdemo2 a_sup_set_class f1_dvdemo2 a_sup_set_class a_wceq f2_dvdemo2 a_sup_set_class f0_dvdemo2 a_sup_set_class a_wcel a_wi f0_dvdemo2 a_wex a_ax-mp $.
$}


