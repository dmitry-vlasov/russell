$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Introduce_the_Axiom_of_Power_Sets.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Derive the Axiom of Pairing

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(The Axiom of Pairing of Zermelo-Fraenkel set theory.  Axiom 2 of
       [TakeutiZaring] p. 15.  In some textbooks this is stated as a separate
       axiom; here we show it is redundant since it can be derived from the
       other axioms.

       This theorem should not be referenced by any proof other than ~ axpr .
       Instead, use ~ zfpair2 below so that the uses of the Axiom of Pairing
       can be more easily identified.  (Contributed by NM, 18-Oct-1995.)
       (New usage is discouraged.) $)

${
	$v x y  $.
	$d x z w v  $.
	$d y z w v  $.
	f0_zfpair $f set x $.
	f1_zfpair $f set y $.
	i0_zfpair $f set z $.
	i1_zfpair $f set w $.
	i2_zfpair $f set v $.
	p_zfpair $p |- { x , y } e. _V $= i1_zfpair f0_zfpair a_sup_set_class f1_zfpair a_sup_set_class p_dfpr2 i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa i0_zfpair p_19.43 i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq p_prlem2 i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq a_wo i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo a_wa i0_zfpair p_exbii p_0ex i0_zfpair a_c0 p_isseti i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i0_zfpair p_19.41v i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_wex i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_wex i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq p_mpbiran p_p0ex i0_zfpair a_c0 a_csn p_isseti i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq i0_zfpair p_19.41v i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_wex i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i0_zfpair a_wex i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq p_mpbiran i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_wex i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_wex i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq p_orbi12i i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i0_zfpair a_wex i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_wex i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_wex a_wo i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq a_wo i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo a_wa i0_zfpair a_wex i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wo p_3bitr3ri i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wo i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq a_wo i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo a_wa i0_zfpair a_wex i1_zfpair p_abbii i0_zfpair a_c0 a_c0 a_csn p_dfpr2 p_pp0ex a_c0 a_c0 a_csn a_cpr i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq a_wo i0_zfpair a_cab a_cvv p_eqeltrri i2_zfpair f0_zfpair i1_zfpair p_equequ2 i0_zfpair a_sup_set_class p_0inp0 i2_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq i1_zfpair a_sup_set_class i2_zfpair a_sup_set_class a_wceq p_prlem1 i2_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i1_zfpair a_sup_set_class i2_zfpair a_sup_set_class a_wceq a_wi i1_zfpair p_alrimdv i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i1_zfpair a_sup_set_class i2_zfpair a_sup_set_class a_wceq a_wi i1_zfpair a_wal i2_zfpair f0_zfpair p_spimev i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa p_orcom i2_zfpair f1_zfpair i1_zfpair p_equequ2 i0_zfpair a_sup_set_class p_0inp0 i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq p_con2i i2_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i1_zfpair a_sup_set_class i2_zfpair a_sup_set_class a_wceq p_prlem1 i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa a_wo i2_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class i2_zfpair a_sup_set_class a_wceq p_syl7bi i2_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i1_zfpair a_sup_set_class i2_zfpair a_sup_set_class a_wceq a_wi i1_zfpair p_alrimdv i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i1_zfpair a_sup_set_class i2_zfpair a_sup_set_class a_wceq a_wi i1_zfpair a_wal i2_zfpair f1_zfpair p_spimev i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i1_zfpair a_sup_set_class i2_zfpair a_sup_set_class a_wceq a_wi i1_zfpair a_wal i2_zfpair a_wex i0_zfpair a_sup_set_class a_c0 a_csn a_wceq p_jaoi i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq a_wo i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo i0_zfpair i1_zfpair i2_zfpair p_zfrep4 i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wo i1_zfpair a_cab i0_zfpair a_sup_set_class a_c0 a_wceq i0_zfpair a_sup_set_class a_c0 a_csn a_wceq a_wo i0_zfpair a_sup_set_class a_c0 a_wceq i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq a_wa i0_zfpair a_sup_set_class a_c0 a_csn a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wa a_wo a_wa i0_zfpair a_wex i1_zfpair a_cab a_cvv p_eqeltri f0_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_cpr i1_zfpair a_sup_set_class f0_zfpair a_sup_set_class a_wceq i1_zfpair a_sup_set_class f1_zfpair a_sup_set_class a_wceq a_wo i1_zfpair a_cab a_cvv p_eqeltri $.
$}

$(Unabbreviated version of the Axiom of Pairing of ZF set theory, derived
       as a theorem from the other axioms.

       This theorem should not be referenced by any proof.  Instead, use
       ~ ax-pr below so that the uses of the Axiom of Pairing can be more
       easily identified.  (Contributed by NM, 14-Nov-2006.)
       (New usage is discouraged.) $)

${
	$v x y z w  $.
	$d x z w  $.
	$d y z w  $.
	f0_axpr $f set x $.
	f1_axpr $f set y $.
	f2_axpr $f set z $.
	f3_axpr $f set w $.
	p_axpr $p |- E. z A. w ( ( w = x \/ w = y ) -> w e. z ) $= f0_axpr f1_axpr p_zfpair f2_axpr f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr p_isseti f3_axpr f2_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr p_dfcleq f3_axpr p_vex f3_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class p_elpr f3_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr a_wcel f3_axpr a_sup_set_class f0_axpr a_sup_set_class a_wceq f3_axpr a_sup_set_class f1_axpr a_sup_set_class a_wceq a_wo f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel p_bibi2i f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel f3_axpr a_sup_set_class f0_axpr a_sup_set_class a_wceq f3_axpr a_sup_set_class f1_axpr a_sup_set_class a_wceq a_wo p_bi2 f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel f3_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr a_wcel a_wb f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel f3_axpr a_sup_set_class f0_axpr a_sup_set_class a_wceq f3_axpr a_sup_set_class f1_axpr a_sup_set_class a_wceq a_wo a_wb f3_axpr a_sup_set_class f0_axpr a_sup_set_class a_wceq f3_axpr a_sup_set_class f1_axpr a_sup_set_class a_wceq a_wo f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel a_wi p_sylbi f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel f3_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr a_wcel a_wb f3_axpr a_sup_set_class f0_axpr a_sup_set_class a_wceq f3_axpr a_sup_set_class f1_axpr a_sup_set_class a_wceq a_wo f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel a_wi f3_axpr p_alimi f2_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr a_wceq f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel f3_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr a_wcel a_wb f3_axpr a_wal f3_axpr a_sup_set_class f0_axpr a_sup_set_class a_wceq f3_axpr a_sup_set_class f1_axpr a_sup_set_class a_wceq a_wo f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel a_wi f3_axpr a_wal p_sylbi f2_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr a_wceq f3_axpr a_sup_set_class f0_axpr a_sup_set_class a_wceq f3_axpr a_sup_set_class f1_axpr a_sup_set_class a_wceq a_wo f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel a_wi f3_axpr a_wal f2_axpr p_eximi f2_axpr a_sup_set_class f0_axpr a_sup_set_class f1_axpr a_sup_set_class a_cpr a_wceq f2_axpr a_wex f3_axpr a_sup_set_class f0_axpr a_sup_set_class a_wceq f3_axpr a_sup_set_class f1_axpr a_sup_set_class a_wceq a_wo f3_axpr a_sup_set_class f2_axpr a_sup_set_class a_wcel a_wi f3_axpr a_wal f2_axpr a_wex a_ax-mp $.
$}

$(The Axiom of Pairing of ZF set theory.  It was derived as theorem ~ axpr
       above and is therefore redundant, but we state it as a separate axiom
       here so that its uses can be identified more easily.  (Contributed by
       NM, 14-Nov-2006.) $)

${
	$v x y z w  $.
	$d x z w  $.
	$d y z w  $.
	f0_ax-pr $f set x $.
	f1_ax-pr $f set y $.
	f2_ax-pr $f set z $.
	f3_ax-pr $f set w $.
	a_ax-pr $a |- E. z A. w ( ( w = x \/ w = y ) -> w e. z ) $.
$}

$(Derive the abbreviated version of the Axiom of Pairing from ~ ax-pr .
       See ~ zfpair for its derivation from the other axioms.  (Contributed by
       NM, 14-Nov-2006.) $)

${
	$v x y  $.
	$d x z w  $.
	$d y z w  $.
	f0_zfpair2 $f set x $.
	f1_zfpair2 $f set y $.
	i0_zfpair2 $f set z $.
	i1_zfpair2 $f set w $.
	p_zfpair2 $p |- { x , y } e. _V $= f0_zfpair2 f1_zfpair2 i0_zfpair2 i1_zfpair2 a_ax-pr i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class a_wceq i1_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_wceq a_wo i0_zfpair2 i1_zfpair2 p_bm1.3ii i1_zfpair2 i0_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_cpr p_dfcleq i1_zfpair2 p_vex i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class p_elpr i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_cpr a_wcel i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class a_wceq i1_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_wceq a_wo i1_zfpair2 a_sup_set_class i0_zfpair2 a_sup_set_class a_wcel p_bibi2i i1_zfpair2 a_sup_set_class i0_zfpair2 a_sup_set_class a_wcel i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_cpr a_wcel a_wb i1_zfpair2 a_sup_set_class i0_zfpair2 a_sup_set_class a_wcel i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class a_wceq i1_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_wceq a_wo a_wb i1_zfpair2 p_albii i0_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_cpr a_wceq i1_zfpair2 a_sup_set_class i0_zfpair2 a_sup_set_class a_wcel i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_cpr a_wcel a_wb i1_zfpair2 a_wal i1_zfpair2 a_sup_set_class i0_zfpair2 a_sup_set_class a_wcel i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class a_wceq i1_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_wceq a_wo a_wb i1_zfpair2 a_wal p_bitri i0_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_cpr a_wceq i1_zfpair2 a_sup_set_class i0_zfpair2 a_sup_set_class a_wcel i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class a_wceq i1_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_wceq a_wo a_wb i1_zfpair2 a_wal i0_zfpair2 p_exbii i0_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_cpr a_wceq i0_zfpair2 a_wex i1_zfpair2 a_sup_set_class i0_zfpair2 a_sup_set_class a_wcel i1_zfpair2 a_sup_set_class f0_zfpair2 a_sup_set_class a_wceq i1_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_wceq a_wo a_wb i1_zfpair2 a_wal i0_zfpair2 a_wex p_mpbir i0_zfpair2 f0_zfpair2 a_sup_set_class f1_zfpair2 a_sup_set_class a_cpr p_issetri $.
$}

$(A singleton is a set.  Theorem 7.13 of [Quine] p. 51, proved using
       Extensionality, Separation, and Pairing.  See also ~ snexALT .
       (Contributed by NM, 7-Aug-1994.)  (Revised by Mario Carneiro,
       19-May-2013.)  (Proof modification is discouraged.) $)

${
	$v A  $.
	$d x A  $.
	f0_snex $f class A $.
	i0_snex $f set x $.
	p_snex $p |- { A } e. _V $= f0_snex p_dfsn2 i0_snex a_sup_set_class i0_snex a_sup_set_class f0_snex f0_snex p_preq12 i0_snex a_sup_set_class f0_snex a_wceq i0_snex a_sup_set_class i0_snex a_sup_set_class a_cpr f0_snex f0_snex a_cpr a_wceq p_anidms i0_snex a_sup_set_class f0_snex a_wceq i0_snex a_sup_set_class i0_snex a_sup_set_class a_cpr f0_snex f0_snex a_cpr a_cvv p_eleq1d i0_snex i0_snex p_zfpair2 i0_snex a_sup_set_class i0_snex a_sup_set_class a_cpr a_cvv a_wcel f0_snex f0_snex a_cpr a_cvv a_wcel i0_snex f0_snex a_cvv p_vtoclg f0_snex a_cvv a_wcel f0_snex a_csn f0_snex f0_snex a_cpr a_cvv p_syl5eqel f0_snex p_snprc f0_snex a_cvv a_wcel a_wn f0_snex a_csn a_c0 a_wceq p_biimpi p_0ex f0_snex a_cvv a_wcel a_wn f0_snex a_csn a_c0 a_cvv p_syl6eqel f0_snex a_cvv a_wcel f0_snex a_csn a_cvv a_wcel p_pm2.61i $.
$}

$(The Axiom of Pairing using class variables.  Theorem 7.13 of [Quine]
       p. 51.  By virtue of its definition, an unordered pair remains a set
       (even though no longer a pair) even when its components are proper
       classes (see ~ prprc ), so we can dispense with hypotheses requiring
       them to be sets.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_prex $f class A $.
	f1_prex $f class B $.
	i0_prex $f set x $.
	i1_prex $f set y $.
	p_prex $p |- { A , B } e. _V $= i1_prex a_sup_set_class f1_prex i0_prex a_sup_set_class p_preq2 i1_prex a_sup_set_class f1_prex a_wceq i0_prex a_sup_set_class i1_prex a_sup_set_class a_cpr i0_prex a_sup_set_class f1_prex a_cpr a_cvv p_eleq1d i0_prex i1_prex p_zfpair2 i0_prex a_sup_set_class i1_prex a_sup_set_class a_cpr a_cvv a_wcel i0_prex a_sup_set_class f1_prex a_cpr a_cvv a_wcel i1_prex f1_prex a_cvv p_vtoclg i0_prex a_sup_set_class f0_prex f1_prex p_preq1 i0_prex a_sup_set_class f0_prex a_wceq i0_prex a_sup_set_class f1_prex a_cpr f0_prex f1_prex a_cpr a_cvv p_eleq1d f1_prex a_cvv a_wcel i0_prex a_sup_set_class f1_prex a_cpr a_cvv a_wcel i0_prex a_sup_set_class f0_prex a_wceq f0_prex f1_prex a_cpr a_cvv a_wcel p_syl5ib f1_prex a_cvv a_wcel f0_prex f1_prex a_cpr a_cvv a_wcel a_wi i0_prex f0_prex a_cvv p_vtocleg f0_prex f1_prex p_prprc1 f1_prex p_snex f0_prex a_cvv a_wcel a_wn f0_prex f1_prex a_cpr f1_prex a_csn a_cvv p_syl6eqel f0_prex f1_prex p_prprc2 f0_prex p_snex f1_prex a_cvv a_wcel a_wn f0_prex f1_prex a_cpr f0_prex a_csn a_cvv p_syl6eqel f0_prex a_cvv a_wcel f1_prex a_cvv a_wcel f0_prex f1_prex a_cpr a_cvv a_wcel p_pm2.61nii $.
$}

$(Every set is an element of some other set.  This has a shorter proof
       than ~ el but uses more axioms.  (Contributed by NM, 4-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v x y  $.
	$d x y  $.
	f0_elALT $f set x $.
	f1_elALT $f set y $.
	p_elALT $p |- E. y x e. y $= f0_elALT p_vex f0_elALT a_sup_set_class p_snid f0_elALT a_sup_set_class p_snex f1_elALT a_sup_set_class f0_elALT a_sup_set_class a_csn f0_elALT a_sup_set_class p_eleq2 f0_elALT a_sup_set_class f1_elALT a_sup_set_class a_wcel f0_elALT a_sup_set_class f0_elALT a_sup_set_class a_csn a_wcel f1_elALT f0_elALT a_sup_set_class a_csn p_spcev f0_elALT a_sup_set_class f0_elALT a_sup_set_class a_csn a_wcel f0_elALT a_sup_set_class f1_elALT a_sup_set_class a_wcel f1_elALT a_wex a_ax-mp $.
$}

$(An alternative proof of ~ dtru ("two things exist") using ~ ax-pr
       instead of ~ ax-pow .  (Contributed by Mario Carneiro, 31-Aug-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v x y  $.
	$d x y  $.
	f0_dtruALT2 $f set x $.
	f1_dtruALT2 $f set y $.
	p_dtruALT2 $p |- -. A. x x = y $= f1_dtruALT2 a_sup_set_class p_0inp0 a_c0 p_snex f0_dtruALT2 a_sup_set_class a_c0 a_csn f1_dtruALT2 a_sup_set_class p_eqeq2 f0_dtruALT2 a_sup_set_class a_c0 a_csn a_wceq f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq f1_dtruALT2 a_sup_set_class a_c0 a_csn a_wceq p_notbid f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq a_wn f1_dtruALT2 a_sup_set_class a_c0 a_csn a_wceq a_wn f0_dtruALT2 a_c0 a_csn p_spcev f1_dtruALT2 a_sup_set_class a_c0 a_wceq f1_dtruALT2 a_sup_set_class a_c0 a_csn a_wceq a_wn f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq a_wn f0_dtruALT2 a_wex p_syl p_0ex f0_dtruALT2 a_sup_set_class a_c0 f1_dtruALT2 a_sup_set_class p_eqeq2 f0_dtruALT2 a_sup_set_class a_c0 a_wceq f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq f1_dtruALT2 a_sup_set_class a_c0 a_wceq p_notbid f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq a_wn f1_dtruALT2 a_sup_set_class a_c0 a_wceq a_wn f0_dtruALT2 a_c0 p_spcev f1_dtruALT2 a_sup_set_class a_c0 a_wceq f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq a_wn f0_dtruALT2 a_wex p_pm2.61i f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq f0_dtruALT2 p_exnal f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class p_eqcom f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq f0_dtruALT2 a_sup_set_class f1_dtruALT2 a_sup_set_class a_wceq f0_dtruALT2 p_albii f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq a_wn f0_dtruALT2 a_wex f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq f0_dtruALT2 a_wal f0_dtruALT2 a_sup_set_class f1_dtruALT2 a_sup_set_class a_wceq f0_dtruALT2 a_wal p_xchbinx f1_dtruALT2 a_sup_set_class f0_dtruALT2 a_sup_set_class a_wceq a_wn f0_dtruALT2 a_wex f0_dtruALT2 a_sup_set_class f1_dtruALT2 a_sup_set_class a_wceq f0_dtruALT2 a_wal a_wn p_mpbi $.
$}

$(A singleton of a set belongs to the power class of a class containing
       the set.  (Contributed by Alan Sare, 25-Aug-2011.) $)

${
	$v A B  $.
	f0_snelpwi $f class A $.
	f1_snelpwi $f class B $.
	p_snelpwi $p |- ( A e. B -> { A } e. ~P B ) $= f0_snelpwi f1_snelpwi p_snssi f0_snelpwi p_snex f0_snelpwi a_csn f1_snelpwi p_elpw f0_snelpwi f1_snelpwi a_wcel f0_snelpwi a_csn f1_snelpwi a_wss f0_snelpwi a_csn f1_snelpwi a_cpw a_wcel p_sylibr $.
$}

$(A singleton of a set belongs to the power class of a class containing
       the set.  (Contributed by NM, 1-Apr-1998.) $)

${
	$v A B  $.
	f0_snelpw $f class A $.
	f1_snelpw $f class B $.
	e0_snelpw $e |- A e. _V $.
	p_snelpw $p |- ( A e. B <-> { A } e. ~P B ) $= e0_snelpw f0_snelpw f1_snelpw p_snss f0_snelpw p_snex f0_snelpw a_csn f1_snelpw p_elpw f0_snelpw f1_snelpw a_wcel f0_snelpw a_csn f1_snelpw a_wss f0_snelpw a_csn f1_snelpw a_cpw a_wcel p_bitr4i $.
$}

$(A theorem similar to extensionality, requiring the existence of a
       singleton.  Exercise 8 of [TakeutiZaring] p. 16.  (Contributed by NM,
       10-Aug-1993.) $)

${
	$v x y z  $.
	$d x y z  $.
	f0_rext $f set x $.
	f1_rext $f set y $.
	f2_rext $f set z $.
	p_rext $p |- ( A. z ( x e. z -> y e. z ) -> x = y ) $= f0_rext p_vex f0_rext a_sup_set_class p_snid f0_rext a_sup_set_class p_snex f2_rext a_sup_set_class f0_rext a_sup_set_class a_csn f0_rext a_sup_set_class p_eleq2 f2_rext a_sup_set_class f0_rext a_sup_set_class a_csn f1_rext a_sup_set_class p_eleq2 f2_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wceq f0_rext a_sup_set_class f2_rext a_sup_set_class a_wcel f0_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wcel f1_rext a_sup_set_class f2_rext a_sup_set_class a_wcel f1_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wcel p_imbi12d f0_rext a_sup_set_class f2_rext a_sup_set_class a_wcel f1_rext a_sup_set_class f2_rext a_sup_set_class a_wcel a_wi f0_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wcel f1_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wcel a_wi f2_rext f0_rext a_sup_set_class a_csn p_spcv f0_rext a_sup_set_class f2_rext a_sup_set_class a_wcel f1_rext a_sup_set_class f2_rext a_sup_set_class a_wcel a_wi f2_rext a_wal f0_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wcel f1_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wcel p_mpi f1_rext f0_rext a_sup_set_class p_elsn f1_rext f0_rext p_equcomi f1_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wcel f1_rext a_sup_set_class f0_rext a_sup_set_class a_wceq f0_rext a_sup_set_class f1_rext a_sup_set_class a_wceq p_sylbi f0_rext a_sup_set_class f2_rext a_sup_set_class a_wcel f1_rext a_sup_set_class f2_rext a_sup_set_class a_wcel a_wi f2_rext a_wal f1_rext a_sup_set_class f0_rext a_sup_set_class a_csn a_wcel f0_rext a_sup_set_class f1_rext a_sup_set_class a_wceq p_syl $.
$}

$(Classes are subclasses if and only if their power classes are
       subclasses.  Exercise 18 of [TakeutiZaring] p. 18.  (Contributed by NM,
       13-Oct-1996.) $)

${
	$v A B  $.
	$d A x  $.
	$d B x  $.
	f0_sspwb $f class A $.
	f1_sspwb $f class B $.
	i0_sspwb $f set x $.
	p_sspwb $p |- ( A C_ B <-> ~P A C_ ~P B ) $= i0_sspwb a_sup_set_class f0_sspwb f1_sspwb p_sstr2 i0_sspwb a_sup_set_class f0_sspwb a_wss f0_sspwb f1_sspwb a_wss i0_sspwb a_sup_set_class f1_sspwb a_wss p_com12 i0_sspwb p_vex i0_sspwb a_sup_set_class f0_sspwb p_elpw i0_sspwb p_vex i0_sspwb a_sup_set_class f1_sspwb p_elpw f0_sspwb f1_sspwb a_wss i0_sspwb a_sup_set_class f0_sspwb a_wss i0_sspwb a_sup_set_class f1_sspwb a_wss i0_sspwb a_sup_set_class f0_sspwb a_cpw a_wcel i0_sspwb a_sup_set_class f1_sspwb a_cpw a_wcel p_3imtr4g f0_sspwb f1_sspwb a_wss i0_sspwb f0_sspwb a_cpw f1_sspwb a_cpw p_ssrdv f0_sspwb a_cpw f1_sspwb a_cpw i0_sspwb a_sup_set_class a_csn p_ssel i0_sspwb a_sup_set_class p_snex i0_sspwb a_sup_set_class a_csn f0_sspwb p_elpw i0_sspwb p_vex i0_sspwb a_sup_set_class f0_sspwb p_snss i0_sspwb a_sup_set_class a_csn f0_sspwb a_cpw a_wcel i0_sspwb a_sup_set_class a_csn f0_sspwb a_wss i0_sspwb a_sup_set_class f0_sspwb a_wcel p_bitr4i i0_sspwb a_sup_set_class p_snex i0_sspwb a_sup_set_class a_csn f1_sspwb p_elpw i0_sspwb p_vex i0_sspwb a_sup_set_class f1_sspwb p_snss i0_sspwb a_sup_set_class a_csn f1_sspwb a_cpw a_wcel i0_sspwb a_sup_set_class a_csn f1_sspwb a_wss i0_sspwb a_sup_set_class f1_sspwb a_wcel p_bitr4i f0_sspwb a_cpw f1_sspwb a_cpw a_wss i0_sspwb a_sup_set_class a_csn f0_sspwb a_cpw a_wcel i0_sspwb a_sup_set_class a_csn f1_sspwb a_cpw a_wcel i0_sspwb a_sup_set_class f0_sspwb a_wcel i0_sspwb a_sup_set_class f1_sspwb a_wcel p_3imtr3g f0_sspwb a_cpw f1_sspwb a_cpw a_wss i0_sspwb f0_sspwb f1_sspwb p_ssrdv f0_sspwb f1_sspwb a_wss f0_sspwb a_cpw f1_sspwb a_cpw a_wss p_impbii $.
$}

$(A class equals the union of its power class.  Exercise 6(a) of
       [Enderton] p. 38.  (Contributed by NM, 14-Oct-1996.)  (Proof shortened
       by Alan Sare, 28-Dec-2008.) $)

${
	$v A  $.
	$d A x y  $.
	f0_unipw $f class A $.
	i0_unipw $f set x $.
	i1_unipw $f set y $.
	p_unipw $p |- U. ~P A = A $= i1_unipw i0_unipw a_sup_set_class f0_unipw a_cpw p_eluni i0_unipw a_sup_set_class i1_unipw a_sup_set_class f0_unipw p_elelpwi i0_unipw a_sup_set_class i1_unipw a_sup_set_class a_wcel i1_unipw a_sup_set_class f0_unipw a_cpw a_wcel a_wa i0_unipw a_sup_set_class f0_unipw a_wcel i1_unipw p_exlimiv i0_unipw a_sup_set_class f0_unipw a_cpw a_cuni a_wcel i0_unipw a_sup_set_class i1_unipw a_sup_set_class a_wcel i1_unipw a_sup_set_class f0_unipw a_cpw a_wcel a_wa i1_unipw a_wex i0_unipw a_sup_set_class f0_unipw a_wcel p_sylbi i0_unipw p_vex i0_unipw a_sup_set_class p_snid i0_unipw a_sup_set_class f0_unipw p_snelpwi i0_unipw a_sup_set_class i0_unipw a_sup_set_class a_csn f0_unipw a_cpw p_elunii i0_unipw a_sup_set_class f0_unipw a_wcel i0_unipw a_sup_set_class i0_unipw a_sup_set_class a_csn a_wcel i0_unipw a_sup_set_class a_csn f0_unipw a_cpw a_wcel i0_unipw a_sup_set_class f0_unipw a_cpw a_cuni a_wcel p_sylancr i0_unipw a_sup_set_class f0_unipw a_cpw a_cuni a_wcel i0_unipw a_sup_set_class f0_unipw a_wcel p_impbii i0_unipw f0_unipw a_cpw a_cuni f0_unipw p_eqriv $.
$}

$(Membership of a power class.  Exercise 10 of [Enderton] p. 26.
     (Contributed by NM, 13-Jan-2007.) $)

${
	$v A B  $.
	f0_pwel $f class A $.
	f1_pwel $f class B $.
	p_pwel $p |- ( A e. B -> ~P A e. ~P ~P U. B ) $= f0_pwel f1_pwel p_elssuni f0_pwel f1_pwel a_cuni p_sspwb f0_pwel f1_pwel a_wcel f0_pwel f1_pwel a_cuni a_wss f0_pwel a_cpw f1_pwel a_cuni a_cpw a_wss p_sylib f0_pwel f1_pwel p_pwexg f0_pwel a_cpw f1_pwel a_cuni a_cpw a_cvv p_elpwg f0_pwel f1_pwel a_wcel f0_pwel a_cpw a_cvv a_wcel f0_pwel a_cpw f1_pwel a_cuni a_cpw a_cpw a_wcel f0_pwel a_cpw f1_pwel a_cuni a_cpw a_wss a_wb p_syl f0_pwel f1_pwel a_wcel f0_pwel a_cpw f1_pwel a_cuni a_cpw a_cpw a_wcel f0_pwel a_cpw f1_pwel a_cuni a_cpw a_wss p_mpbird $.
$}

$(A class is transitive iff its power class is transitive.  (Contributed by
     Alan Sare, 25-Aug-2011.)  (Revised by Mario Carneiro, 15-Jun-2014.) $)

${
	$v A  $.
	f0_pwtr $f class A $.
	p_pwtr $p |- ( Tr A <-> Tr ~P A ) $= f0_pwtr p_unipw f0_pwtr a_cpw a_cuni f0_pwtr f0_pwtr a_cpw p_sseq1i f0_pwtr a_cpw a_df-tr f0_pwtr p_dftr4 f0_pwtr a_cpw a_cuni f0_pwtr a_cpw a_wss f0_pwtr f0_pwtr a_cpw a_wss f0_pwtr a_cpw a_wtr f0_pwtr a_wtr p_3bitr4ri $.
$}

$(An extensionality-like principle defining subclass in terms of subsets.
       (Contributed by NM, 30-Jun-2004.) $)

${
	$v x A B  $.
	$d A x  $.
	$d B x  $.
	f0_ssextss $f set x $.
	f1_ssextss $f class A $.
	f2_ssextss $f class B $.
	p_ssextss $p |- ( A C_ B <-> A. x ( x C_ A -> x C_ B ) ) $= f1_ssextss f2_ssextss p_sspwb f0_ssextss f1_ssextss a_cpw f2_ssextss a_cpw p_dfss2 f0_ssextss p_vex f0_ssextss a_sup_set_class f1_ssextss p_elpw f0_ssextss p_vex f0_ssextss a_sup_set_class f2_ssextss p_elpw f0_ssextss a_sup_set_class f1_ssextss a_cpw a_wcel f0_ssextss a_sup_set_class f1_ssextss a_wss f0_ssextss a_sup_set_class f2_ssextss a_cpw a_wcel f0_ssextss a_sup_set_class f2_ssextss a_wss p_imbi12i f0_ssextss a_sup_set_class f1_ssextss a_cpw a_wcel f0_ssextss a_sup_set_class f2_ssextss a_cpw a_wcel a_wi f0_ssextss a_sup_set_class f1_ssextss a_wss f0_ssextss a_sup_set_class f2_ssextss a_wss a_wi f0_ssextss p_albii f1_ssextss f2_ssextss a_wss f1_ssextss a_cpw f2_ssextss a_cpw a_wss f0_ssextss a_sup_set_class f1_ssextss a_cpw a_wcel f0_ssextss a_sup_set_class f2_ssextss a_cpw a_wcel a_wi f0_ssextss a_wal f0_ssextss a_sup_set_class f1_ssextss a_wss f0_ssextss a_sup_set_class f2_ssextss a_wss a_wi f0_ssextss a_wal p_3bitri $.
$}

$(An extensionality-like principle that uses the subset instead of the
       membership relation: two classes are equal iff they have the same
       subsets.  (Contributed by NM, 30-Jun-2004.) $)

${
	$v x A B  $.
	$d A x  $.
	$d B x  $.
	f0_ssext $f set x $.
	f1_ssext $f class A $.
	f2_ssext $f class B $.
	p_ssext $p |- ( A = B <-> A. x ( x C_ A <-> x C_ B ) ) $= f0_ssext f1_ssext f2_ssext p_ssextss f0_ssext f2_ssext f1_ssext p_ssextss f1_ssext f2_ssext a_wss f0_ssext a_sup_set_class f1_ssext a_wss f0_ssext a_sup_set_class f2_ssext a_wss a_wi f0_ssext a_wal f2_ssext f1_ssext a_wss f0_ssext a_sup_set_class f2_ssext a_wss f0_ssext a_sup_set_class f1_ssext a_wss a_wi f0_ssext a_wal p_anbi12i f1_ssext f2_ssext p_eqss f0_ssext a_sup_set_class f1_ssext a_wss f0_ssext a_sup_set_class f2_ssext a_wss f0_ssext p_albiim f1_ssext f2_ssext a_wss f2_ssext f1_ssext a_wss a_wa f0_ssext a_sup_set_class f1_ssext a_wss f0_ssext a_sup_set_class f2_ssext a_wss a_wi f0_ssext a_wal f0_ssext a_sup_set_class f2_ssext a_wss f0_ssext a_sup_set_class f1_ssext a_wss a_wi f0_ssext a_wal a_wa f1_ssext f2_ssext a_wceq f0_ssext a_sup_set_class f1_ssext a_wss f0_ssext a_sup_set_class f2_ssext a_wss a_wb f0_ssext a_wal p_3bitr4i $.
$}

$(Negation of subclass relationship.  Compare ~ nss .  (Contributed by NM,
       30-Jun-2004.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v x A B  $.
	$d A x  $.
	$d B x  $.
	f0_nssss $f set x $.
	f1_nssss $f class A $.
	f2_nssss $f class B $.
	p_nssss $p |- ( -. A C_ B <-> E. x ( x C_ A /\ -. x C_ B ) ) $= f0_nssss a_sup_set_class f1_nssss a_wss f0_nssss a_sup_set_class f2_nssss a_wss f0_nssss p_exanali f0_nssss f1_nssss f2_nssss p_ssextss f0_nssss a_sup_set_class f1_nssss a_wss f0_nssss a_sup_set_class f2_nssss a_wss a_wn a_wa f0_nssss a_wex f0_nssss a_sup_set_class f1_nssss a_wss f0_nssss a_sup_set_class f2_nssss a_wss a_wi f0_nssss a_wal f1_nssss f2_nssss a_wss p_xchbinxr f0_nssss a_sup_set_class f1_nssss a_wss f0_nssss a_sup_set_class f2_nssss a_wss a_wn a_wa f0_nssss a_wex f1_nssss f2_nssss a_wss a_wn p_bicomi $.
$}

$(Classes are equal if and only if their power classes are equal.  Exercise
     19 of [TakeutiZaring] p. 18.  (Contributed by NM, 13-Oct-1996.) $)

${
	$v A B  $.
	f0_pweqb $f class A $.
	f1_pweqb $f class B $.
	p_pweqb $p |- ( A = B <-> ~P A = ~P B ) $= f0_pweqb f1_pweqb p_sspwb f1_pweqb f0_pweqb p_sspwb f0_pweqb f1_pweqb a_wss f0_pweqb a_cpw f1_pweqb a_cpw a_wss f1_pweqb f0_pweqb a_wss f1_pweqb a_cpw f0_pweqb a_cpw a_wss p_anbi12i f0_pweqb f1_pweqb p_eqss f0_pweqb a_cpw f1_pweqb a_cpw p_eqss f0_pweqb f1_pweqb a_wss f1_pweqb f0_pweqb a_wss a_wa f0_pweqb a_cpw f1_pweqb a_cpw a_wss f1_pweqb a_cpw f0_pweqb a_cpw a_wss a_wa f0_pweqb f1_pweqb a_wceq f0_pweqb a_cpw f1_pweqb a_cpw a_wceq p_3bitr4i $.
$}

$(The intersection of all sets to which a set belongs is the singleton of
       that set.  (Contributed by NM, 5-Jun-2009.) $)

${
	$v x A  $.
	$d x A  $.
	f0_intid $f set x $.
	f1_intid $f class A $.
	e0_intid $e |- A e. _V $.
	p_intid $p |- |^| { x | A e. x } = { A } $= f1_intid p_snex f0_intid a_sup_set_class f1_intid a_csn f1_intid p_eleq2 e0_intid f1_intid p_snid f1_intid f0_intid a_sup_set_class a_wcel f1_intid f1_intid a_csn a_wcel f0_intid f1_intid a_csn a_cvv p_intmin3 f1_intid a_csn a_cvv a_wcel f1_intid f0_intid a_sup_set_class a_wcel f0_intid a_cab a_cint f1_intid a_csn a_wss a_ax-mp e0_intid f1_intid f0_intid a_sup_set_class a_wcel f0_intid f1_intid p_elintab f1_intid f0_intid a_sup_set_class a_wcel p_id f1_intid f1_intid f0_intid a_sup_set_class a_wcel f0_intid a_cab a_cint a_wcel f1_intid f0_intid a_sup_set_class a_wcel f1_intid f0_intid a_sup_set_class a_wcel a_wi f0_intid p_mpgbir f1_intid f1_intid f0_intid a_sup_set_class a_wcel f0_intid a_cab a_cint p_snssi f1_intid f1_intid f0_intid a_sup_set_class a_wcel f0_intid a_cab a_cint a_wcel f1_intid a_csn f1_intid f0_intid a_sup_set_class a_wcel f0_intid a_cab a_cint a_wss a_ax-mp f1_intid f0_intid a_sup_set_class a_wcel f0_intid a_cab a_cint f1_intid a_csn p_eqssi $.
$}

$("At most one" existence implies a class abstraction exists.
       (Contributed by NM, 30-Dec-1996.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_moabex $f wff ph $.
	f1_moabex $f set x $.
	i0_moabex $f set y $.
	p_moabex $p |- ( E* x ph -> { x | ph } e. _V ) $= f0_moabex i0_moabex p_nfv f0_moabex f1_moabex i0_moabex p_mo2 f0_moabex f1_moabex i0_moabex a_sup_set_class a_csn p_abss f1_moabex i0_moabex a_sup_set_class p_elsn f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_csn a_wcel f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_wceq f0_moabex p_imbi2i f0_moabex f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_csn a_wcel a_wi f0_moabex f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_wceq a_wi f1_moabex p_albii f0_moabex f1_moabex a_cab i0_moabex a_sup_set_class a_csn a_wss f0_moabex f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_csn a_wcel a_wi f1_moabex a_wal f0_moabex f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_wceq a_wi f1_moabex a_wal p_bitri i0_moabex a_sup_set_class p_snex f0_moabex f1_moabex a_cab i0_moabex a_sup_set_class a_csn p_ssex f0_moabex f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_wceq a_wi f1_moabex a_wal f0_moabex f1_moabex a_cab i0_moabex a_sup_set_class a_csn a_wss f0_moabex f1_moabex a_cab a_cvv a_wcel p_sylbir f0_moabex f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_wceq a_wi f1_moabex a_wal f0_moabex f1_moabex a_cab a_cvv a_wcel i0_moabex p_exlimiv f0_moabex f1_moabex a_wmo f0_moabex f1_moabex a_sup_set_class i0_moabex a_sup_set_class a_wceq a_wi f1_moabex a_wal i0_moabex a_wex f0_moabex f1_moabex a_cab a_cvv a_wcel p_sylbi $.
$}

$(Restricted "at most one" existence implies a restricted class abstraction
     exists.  (Contributed by NM, 17-Jun-2017.) $)

${
	$v ph x A  $.
	f0_rmorabex $f wff ph $.
	f1_rmorabex $f set x $.
	f2_rmorabex $f class A $.
	p_rmorabex $p |- ( E* x e. A ph -> { x e. A | ph } e. _V ) $= f1_rmorabex a_sup_set_class f2_rmorabex a_wcel f0_rmorabex a_wa f1_rmorabex p_moabex f0_rmorabex f1_rmorabex f2_rmorabex a_df-rmo f0_rmorabex f1_rmorabex f2_rmorabex a_df-rab f0_rmorabex f1_rmorabex f2_rmorabex a_crab f1_rmorabex a_sup_set_class f2_rmorabex a_wcel f0_rmorabex a_wa f1_rmorabex a_cab a_cvv p_eleq1i f1_rmorabex a_sup_set_class f2_rmorabex a_wcel f0_rmorabex a_wa f1_rmorabex a_wmo f1_rmorabex a_sup_set_class f2_rmorabex a_wcel f0_rmorabex a_wa f1_rmorabex a_cab a_cvv a_wcel f0_rmorabex f1_rmorabex f2_rmorabex a_wrmo f0_rmorabex f1_rmorabex f2_rmorabex a_crab a_cvv a_wcel p_3imtr4i $.
$}

$(The abstraction of a wff with existential uniqueness exists.  (Contributed
     by NM, 25-Nov-1994.) $)

${
	$v ph x  $.
	f0_euabex $f wff ph $.
	f1_euabex $f set x $.
	p_euabex $p |- ( E! x ph -> { x | ph } e. _V ) $= f0_euabex f1_euabex p_eumo f0_euabex f1_euabex p_moabex f0_euabex f1_euabex a_weu f0_euabex f1_euabex a_wmo f0_euabex f1_euabex a_cab a_cvv a_wcel p_syl $.
$}

$(A non-empty class (even if proper) has a non-empty subset.  (Contributed
       by NM, 23-Aug-2003.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_nnullss $f set x $.
	f1_nnullss $f class A $.
	i0_nnullss $f set y $.
	p_nnullss $p |- ( A =/= (/) -> E. x ( x C_ A /\ x =/= (/) ) ) $= i0_nnullss f1_nnullss p_n0 i0_nnullss p_vex i0_nnullss a_sup_set_class f1_nnullss p_snss i0_nnullss p_vex i0_nnullss a_sup_set_class p_snnz i0_nnullss a_sup_set_class p_snex f0_nnullss a_sup_set_class i0_nnullss a_sup_set_class a_csn f1_nnullss p_sseq1 f0_nnullss a_sup_set_class i0_nnullss a_sup_set_class a_csn a_c0 p_neeq1 f0_nnullss a_sup_set_class i0_nnullss a_sup_set_class a_csn a_wceq f0_nnullss a_sup_set_class f1_nnullss a_wss i0_nnullss a_sup_set_class a_csn f1_nnullss a_wss f0_nnullss a_sup_set_class a_c0 a_wne i0_nnullss a_sup_set_class a_csn a_c0 a_wne p_anbi12d f0_nnullss a_sup_set_class f1_nnullss a_wss f0_nnullss a_sup_set_class a_c0 a_wne a_wa i0_nnullss a_sup_set_class a_csn f1_nnullss a_wss i0_nnullss a_sup_set_class a_csn a_c0 a_wne a_wa f0_nnullss i0_nnullss a_sup_set_class a_csn p_spcev i0_nnullss a_sup_set_class a_csn f1_nnullss a_wss i0_nnullss a_sup_set_class a_csn a_c0 a_wne f0_nnullss a_sup_set_class f1_nnullss a_wss f0_nnullss a_sup_set_class a_c0 a_wne a_wa f0_nnullss a_wex p_mpan2 i0_nnullss a_sup_set_class f1_nnullss a_wcel i0_nnullss a_sup_set_class a_csn f1_nnullss a_wss f0_nnullss a_sup_set_class f1_nnullss a_wss f0_nnullss a_sup_set_class a_c0 a_wne a_wa f0_nnullss a_wex p_sylbi i0_nnullss a_sup_set_class f1_nnullss a_wcel f0_nnullss a_sup_set_class f1_nnullss a_wss f0_nnullss a_sup_set_class a_c0 a_wne a_wa f0_nnullss a_wex i0_nnullss p_exlimiv f1_nnullss a_c0 a_wne i0_nnullss a_sup_set_class f1_nnullss a_wcel i0_nnullss a_wex f0_nnullss a_sup_set_class f1_nnullss a_wss f0_nnullss a_sup_set_class a_c0 a_wne a_wa f0_nnullss a_wex p_sylbi $.
$}

$(Restricted existence in a class (even if proper) implies restricted
       existence in a subset.  (Contributed by NM, 23-Aug-2003.) $)

${
	$v ph x y A  $.
	$d x y z A  $.
	$d y z ph  $.
	f0_exss $f wff ph $.
	f1_exss $f set x $.
	f2_exss $f set y $.
	f3_exss $f class A $.
	i0_exss $f set z $.
	p_exss $p |- ( E. x e. A ph -> E. y ( y C_ A /\ E. x e. y ph ) ) $= f0_exss f1_exss f3_exss a_df-rab f0_exss f1_exss f3_exss a_crab f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_c0 p_neeq1i f0_exss f1_exss f3_exss p_rabn0 i0_exss f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab p_n0 f0_exss f1_exss f3_exss a_crab a_c0 a_wne f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_c0 a_wne f0_exss f1_exss f3_exss a_wrex i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel i0_exss a_wex p_3bitr3i i0_exss p_vex i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab p_snss f0_exss f1_exss f3_exss p_ssab2 i0_exss a_sup_set_class a_csn f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab f3_exss p_sstr2 i0_exss a_sup_set_class a_csn f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wss f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab f3_exss a_wss i0_exss a_sup_set_class a_csn f3_exss a_wss p_mpi i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel i0_exss a_sup_set_class a_csn f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wss i0_exss a_sup_set_class a_csn f3_exss a_wss p_sylbi f1_exss a_sup_set_class f3_exss a_wcel f1_exss i0_exss a_wsb f0_exss f1_exss i0_exss a_wsb p_simpr f1_exss i0_exss p_equsb1 f1_exss i0_exss a_sup_set_class p_elsn f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f1_exss a_sup_set_class i0_exss a_sup_set_class a_wceq f1_exss i0_exss p_sbbii f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f1_exss i0_exss a_wsb f1_exss a_sup_set_class i0_exss a_sup_set_class a_wceq f1_exss i0_exss a_wsb p_mpbir f1_exss a_sup_set_class f3_exss a_wcel f1_exss i0_exss a_wsb f0_exss f1_exss i0_exss a_wsb a_wa f0_exss f1_exss i0_exss a_wsb f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f1_exss i0_exss a_wsb p_jctil f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa i0_exss f1_exss a_df-clab f1_exss a_sup_set_class f3_exss a_wcel f0_exss f1_exss i0_exss p_sban i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss i0_exss a_wsb f1_exss a_sup_set_class f3_exss a_wcel f1_exss i0_exss a_wsb f0_exss f1_exss i0_exss a_wsb a_wa p_bitri f0_exss f1_exss i0_exss a_sup_set_class a_csn a_df-rab f0_exss f1_exss i0_exss a_sup_set_class a_csn a_crab f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f0_exss a_wa f1_exss a_cab i0_exss a_sup_set_class p_eleq2i f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f0_exss a_wa i0_exss f1_exss a_df-clab f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f0_exss f1_exss i0_exss p_sban i0_exss a_sup_set_class f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f0_exss a_wa f1_exss a_cab a_wcel f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f0_exss a_wa f1_exss i0_exss a_wsb f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f1_exss i0_exss a_wsb f0_exss f1_exss i0_exss a_wsb a_wa p_bitri i0_exss a_sup_set_class f0_exss f1_exss i0_exss a_sup_set_class a_csn a_crab a_wcel i0_exss a_sup_set_class f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f0_exss a_wa f1_exss a_cab a_wcel f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f1_exss i0_exss a_wsb f0_exss f1_exss i0_exss a_wsb a_wa p_bitri f1_exss a_sup_set_class f3_exss a_wcel f1_exss i0_exss a_wsb f0_exss f1_exss i0_exss a_wsb a_wa f1_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wcel f1_exss i0_exss a_wsb f0_exss f1_exss i0_exss a_wsb a_wa i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel i0_exss a_sup_set_class f0_exss f1_exss i0_exss a_sup_set_class a_csn a_crab a_wcel p_3imtr4i f0_exss f1_exss i0_exss a_sup_set_class a_csn a_crab i0_exss a_sup_set_class p_ne0i i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel i0_exss a_sup_set_class f0_exss f1_exss i0_exss a_sup_set_class a_csn a_crab a_wcel f0_exss f1_exss i0_exss a_sup_set_class a_csn a_crab a_c0 a_wne p_syl f0_exss f1_exss i0_exss a_sup_set_class a_csn p_rabn0 i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel f0_exss f1_exss i0_exss a_sup_set_class a_csn a_crab a_c0 a_wne f0_exss f1_exss i0_exss a_sup_set_class a_csn a_wrex p_sylib i0_exss a_sup_set_class p_snex f2_exss a_sup_set_class i0_exss a_sup_set_class a_csn f3_exss p_sseq1 f0_exss f1_exss f2_exss a_sup_set_class i0_exss a_sup_set_class a_csn p_rexeq f2_exss a_sup_set_class i0_exss a_sup_set_class a_csn a_wceq f2_exss a_sup_set_class f3_exss a_wss i0_exss a_sup_set_class a_csn f3_exss a_wss f0_exss f1_exss f2_exss a_sup_set_class a_wrex f0_exss f1_exss i0_exss a_sup_set_class a_csn a_wrex p_anbi12d f2_exss a_sup_set_class f3_exss a_wss f0_exss f1_exss f2_exss a_sup_set_class a_wrex a_wa i0_exss a_sup_set_class a_csn f3_exss a_wss f0_exss f1_exss i0_exss a_sup_set_class a_csn a_wrex a_wa f2_exss i0_exss a_sup_set_class a_csn p_spcev i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel i0_exss a_sup_set_class a_csn f3_exss a_wss f0_exss f1_exss i0_exss a_sup_set_class a_csn a_wrex f2_exss a_sup_set_class f3_exss a_wss f0_exss f1_exss f2_exss a_sup_set_class a_wrex a_wa f2_exss a_wex p_syl2anc i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel f2_exss a_sup_set_class f3_exss a_wss f0_exss f1_exss f2_exss a_sup_set_class a_wrex a_wa f2_exss a_wex i0_exss p_exlimiv f0_exss f1_exss f3_exss a_wrex i0_exss a_sup_set_class f1_exss a_sup_set_class f3_exss a_wcel f0_exss a_wa f1_exss a_cab a_wcel i0_exss a_wex f2_exss a_sup_set_class f3_exss a_wss f0_exss f1_exss f2_exss a_sup_set_class a_wrex a_wa f2_exss a_wex p_sylbi $.
$}

$(An ordered pair of classes is a set.  Exercise 7 of [TakeutiZaring]
     p. 16.  (Contributed by NM, 18-Aug-1993.)  (Revised by Mario Carneiro,
     26-Apr-2015.) $)

${
	$v A B  $.
	f0_opex $f class A $.
	f1_opex $f class B $.
	p_opex $p |- <. A , B >. e. _V $= f0_opex f1_opex p_dfopif f0_opex a_csn f0_opex f1_opex a_cpr p_prex p_0ex f0_opex a_cvv a_wcel f1_opex a_cvv a_wcel a_wa f0_opex a_csn f0_opex f1_opex a_cpr a_cpr a_c0 p_ifex f0_opex f1_opex a_cop f0_opex a_cvv a_wcel f1_opex a_cvv a_wcel a_wa f0_opex a_csn f0_opex f1_opex a_cpr a_cpr a_c0 a_cif a_cvv p_eqeltri $.
$}

$(An ordered triple of classes is a set.  (Contributed by NM,
     3-Apr-2015.) $)

${
	$v A B C  $.
	f0_otex $f class A $.
	f1_otex $f class B $.
	f2_otex $f class C $.
	p_otex $p |- <. A , B , C >. e. _V $= f0_otex f1_otex f2_otex a_df-ot f0_otex f1_otex a_cop f2_otex p_opex f0_otex f1_otex f2_otex a_cotp f0_otex f1_otex a_cop f2_otex a_cop a_cvv p_eqeltri $.
$}

$(An ordered pair has two elements.  Exercise 3 of [TakeutiZaring] p. 15.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)

${
	$v A B C  $.
	f0_elop $f class A $.
	f1_elop $f class B $.
	f2_elop $f class C $.
	e0_elop $e |- A e. _V $.
	e1_elop $e |- B e. _V $.
	e2_elop $e |- C e. _V $.
	p_elop $p |- ( A e. <. B , C >. <-> ( A = { B } \/ A = { B , C } ) ) $= e1_elop e2_elop f1_elop f2_elop p_dfop f1_elop f2_elop a_cop f1_elop a_csn f1_elop f2_elop a_cpr a_cpr f0_elop p_eleq2i e0_elop f0_elop f1_elop a_csn f1_elop f2_elop a_cpr p_elpr f0_elop f1_elop f2_elop a_cop a_wcel f0_elop f1_elop a_csn f1_elop f2_elop a_cpr a_cpr a_wcel f0_elop f1_elop a_csn a_wceq f0_elop f1_elop f2_elop a_cpr a_wceq a_wo p_bitri $.
$}

$(One of the two elements in an ordered pair.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B  $.
	f0_opi1 $f class A $.
	f1_opi1 $f class B $.
	e0_opi1 $e |- A e. _V $.
	e1_opi1 $e |- B e. _V $.
	p_opi1 $p |- { A } e. <. A , B >. $= f0_opi1 p_snex f0_opi1 a_csn f0_opi1 f1_opi1 a_cpr p_prid1 e0_opi1 e1_opi1 f0_opi1 f1_opi1 p_dfop f0_opi1 a_csn f0_opi1 a_csn f0_opi1 f1_opi1 a_cpr a_cpr f0_opi1 f1_opi1 a_cop p_eleqtrri $.
$}

$(One of the two elements of an ordered pair.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B  $.
	f0_opi2 $f class A $.
	f1_opi2 $f class B $.
	e0_opi2 $e |- A e. _V $.
	e1_opi2 $e |- B e. _V $.
	p_opi2 $p |- { A , B } e. <. A , B >. $= f0_opi2 f1_opi2 p_prex f0_opi2 a_csn f0_opi2 f1_opi2 a_cpr p_prid2 e0_opi2 e1_opi2 f0_opi2 f1_opi2 p_dfop f0_opi2 f1_opi2 a_cpr f0_opi2 a_csn f0_opi2 f1_opi2 a_cpr a_cpr f0_opi2 f1_opi2 a_cop p_eleqtrri $.
$}


