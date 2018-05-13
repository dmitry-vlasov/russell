$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Peano_s_postulates.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Finite induction (for finite ordinals)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(The Principle of Finite Induction (mathematical induction).  Corollary
       7.31 of [TakeutiZaring] p. 43.  The simpler hypothesis shown here was
       suggested in an email from "Colin" on 1-Oct-2001.  The hypothesis states
       that ` A ` is a set of natural numbers, zero belongs to ` A ` , and
       given any member of ` A ` the member's successor also belongs to
       ` A ` .  The conclusion is that every natural number is in ` A ` .
       (Contributed by NM, 22-Feb-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)

${
	$v x A  $.
	$d x A  $.
	f0_find $f set x $.
	f1_find $f class A $.
	e0_find $e |- ( A C_ om /\ (/) e. A /\ A. x e. A suc x e. A ) $.
	p_find $p |- A = om $= e0_find f1_find a_com a_wss a_c0 f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel f0_find f1_find a_wral p_simp1i e0_find f1_find a_com a_wss a_c0 f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel f0_find f1_find a_wral p_3simpc f1_find a_com a_wss a_c0 f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel f0_find f1_find a_wral a_w3a a_c0 f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel f0_find f1_find a_wral a_wa a_ax-mp f0_find a_sup_set_class a_csuc f1_find a_wcel f0_find f1_find a_df-ral f0_find a_sup_set_class f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel a_wi f0_find a_com p_alral f0_find a_sup_set_class a_csuc f1_find a_wcel f0_find f1_find a_wral f0_find a_sup_set_class f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel a_wi f0_find a_wal f0_find a_sup_set_class f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel a_wi f0_find a_com a_wral p_sylbi f0_find a_sup_set_class a_csuc f1_find a_wcel f0_find f1_find a_wral f0_find a_sup_set_class f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel a_wi f0_find a_com a_wral a_c0 f1_find a_wcel p_anim2i a_c0 f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel f0_find f1_find a_wral a_wa a_c0 f1_find a_wcel f0_find a_sup_set_class f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel a_wi f0_find a_com a_wral a_wa a_ax-mp f0_find f1_find p_peano5 a_c0 f1_find a_wcel f0_find a_sup_set_class f1_find a_wcel f0_find a_sup_set_class a_csuc f1_find a_wcel a_wi f0_find a_com a_wral a_wa a_com f1_find a_wss a_ax-mp f1_find a_com p_eqssi $.
$}

$(Substitutions. $)

$(Basis. $)

$(Induction hypothesis. $)

$(Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last two are the basis and the induction hypothesis.  Theorem
       Schema 22 of [Suppes] p. 136.  (Contributed by NM, 14-Apr-1995.) $)

${
	$v ph ps ch th ta x y A  $.
	$d x y  $.
	$d x A  $.
	$d x ps  $.
	$d x ch  $.
	$d x th  $.
	$d x ta  $.
	$d y ph  $.
	f0_finds $f wff ph $.
	f1_finds $f wff ps $.
	f2_finds $f wff ch $.
	f3_finds $f wff th $.
	f4_finds $f wff ta $.
	f5_finds $f set x $.
	f6_finds $f set y $.
	f7_finds $f class A $.
	e0_finds $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	e1_finds $e |- ( x = y -> ( ph <-> ch ) ) $.
	e2_finds $e |- ( x = suc y -> ( ph <-> th ) ) $.
	e3_finds $e |- ( x = A -> ( ph <-> ta ) ) $.
	e4_finds $e |- ps $.
	e5_finds $e |- ( y e. om -> ( ch -> th ) ) $.
	p_finds $p |- ( A e. om -> ta ) $= e4_finds p_0ex e0_finds f0_finds f1_finds f5_finds a_c0 p_elab a_c0 f0_finds f5_finds a_cab a_wcel f1_finds p_mpbir e5_finds f6_finds p_vex e1_finds f0_finds f2_finds f5_finds f6_finds a_sup_set_class p_elab f6_finds p_vex f6_finds a_sup_set_class p_sucex e2_finds f0_finds f3_finds f5_finds f6_finds a_sup_set_class a_csuc p_elab f6_finds a_sup_set_class a_com a_wcel f2_finds f3_finds f6_finds a_sup_set_class f0_finds f5_finds a_cab a_wcel f6_finds a_sup_set_class a_csuc f0_finds f5_finds a_cab a_wcel p_3imtr4g f6_finds a_sup_set_class f0_finds f5_finds a_cab a_wcel f6_finds a_sup_set_class a_csuc f0_finds f5_finds a_cab a_wcel a_wi f6_finds a_com p_rgen f6_finds f0_finds f5_finds a_cab p_peano5 a_c0 f0_finds f5_finds a_cab a_wcel f6_finds a_sup_set_class f0_finds f5_finds a_cab a_wcel f6_finds a_sup_set_class a_csuc f0_finds f5_finds a_cab a_wcel a_wi f6_finds a_com a_wral a_com f0_finds f5_finds a_cab a_wss p_mp2an a_com f0_finds f5_finds a_cab f7_finds p_sseli e3_finds f0_finds f4_finds f5_finds f7_finds a_com p_elabg f7_finds a_com a_wcel f7_finds f0_finds f5_finds a_cab a_wcel f4_finds p_mpbid $.
$}

$(Substitutions. $)

$(Basis. $)

$(Induction hypothesis. $)

$(Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last two are the basis and the induction hypothesis.  The
       basis of this version is an arbitrary natural number ` B ` instead of
       zero.  (Contributed by NM, 16-Sep-1995.) $)

${
	$v ph ps ch th ta x y A B  $.
	$d x A  $.
	$d x y B  $.
	$d x ps  $.
	$d x ch  $.
	$d x th  $.
	$d x ta  $.
	$d y ph  $.
	f0_findsg $f wff ph $.
	f1_findsg $f wff ps $.
	f2_findsg $f wff ch $.
	f3_findsg $f wff th $.
	f4_findsg $f wff ta $.
	f5_findsg $f set x $.
	f6_findsg $f set y $.
	f7_findsg $f class A $.
	f8_findsg $f class B $.
	e0_findsg $e |- ( x = B -> ( ph <-> ps ) ) $.
	e1_findsg $e |- ( x = y -> ( ph <-> ch ) ) $.
	e2_findsg $e |- ( x = suc y -> ( ph <-> th ) ) $.
	e3_findsg $e |- ( x = A -> ( ph <-> ta ) ) $.
	e4_findsg $e |- ( B e. om -> ps ) $.
	e5_findsg $e |- ( ( ( y e. om /\ B e. om ) /\ B C_ y ) -> ( ch -> th ) ) $.
	p_findsg $p |- ( ( ( A e. om /\ B e. om ) /\ B C_ A ) -> ta ) $= f5_findsg a_sup_set_class a_c0 f8_findsg p_sseq2 f5_findsg a_sup_set_class a_c0 a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f8_findsg a_c0 a_wss a_wb f8_findsg a_c0 a_wceq p_adantl f8_findsg a_c0 f5_findsg a_sup_set_class p_eqeq2 e0_findsg f8_findsg a_c0 a_wceq f5_findsg a_sup_set_class a_c0 a_wceq f5_findsg a_sup_set_class f8_findsg a_wceq f0_findsg f1_findsg a_wb p_syl6bir f8_findsg a_c0 a_wceq f5_findsg a_sup_set_class a_c0 a_wceq f0_findsg f1_findsg a_wb p_imp f8_findsg a_c0 a_wceq f5_findsg a_sup_set_class a_c0 a_wceq a_wa f8_findsg f5_findsg a_sup_set_class a_wss f8_findsg a_c0 a_wss f0_findsg f1_findsg p_imbi12d f5_findsg a_sup_set_class a_c0 f8_findsg p_sseq2 f5_findsg a_sup_set_class a_c0 a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f8_findsg a_c0 a_wss f0_findsg p_imbi1d f8_findsg p_ss0 f8_findsg a_c0 a_wss f8_findsg a_c0 a_wceq p_con3i f8_findsg a_c0 a_wceq a_wn f8_findsg a_c0 a_wss f0_findsg f1_findsg a_wb p_pm2.21d f8_findsg a_c0 a_wceq a_wn f8_findsg a_c0 a_wss f0_findsg f1_findsg p_pm5.74d f5_findsg a_sup_set_class a_c0 a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f0_findsg a_wi f8_findsg a_c0 a_wss f0_findsg a_wi f8_findsg a_c0 a_wceq a_wn f8_findsg a_c0 a_wss f1_findsg a_wi p_sylan9bbr f8_findsg a_c0 a_wceq f5_findsg a_sup_set_class a_c0 a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f0_findsg a_wi f8_findsg a_c0 a_wss f1_findsg a_wi a_wb p_pm2.61ian f5_findsg a_sup_set_class a_c0 a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f0_findsg a_wi f8_findsg a_c0 a_wss f1_findsg a_wi f8_findsg a_com a_wcel p_imbi2d f5_findsg a_sup_set_class f6_findsg a_sup_set_class f8_findsg p_sseq2 e1_findsg f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f8_findsg f6_findsg a_sup_set_class a_wss f0_findsg f2_findsg p_imbi12d f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f0_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg a_com a_wcel p_imbi2d f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_csuc f8_findsg p_sseq2 e2_findsg f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_csuc a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f0_findsg f3_findsg p_imbi12d f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_csuc a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f0_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi f8_findsg a_com a_wcel p_imbi2d f5_findsg a_sup_set_class f7_findsg f8_findsg p_sseq2 e3_findsg f5_findsg a_sup_set_class f7_findsg a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f8_findsg f7_findsg a_wss f0_findsg f4_findsg p_imbi12d f5_findsg a_sup_set_class f7_findsg a_wceq f8_findsg f5_findsg a_sup_set_class a_wss f0_findsg a_wi f8_findsg f7_findsg a_wss f4_findsg a_wi f8_findsg a_com a_wcel p_imbi2d e4_findsg f8_findsg a_com a_wcel f1_findsg f8_findsg a_c0 a_wss p_a1d f6_findsg p_vex f6_findsg a_sup_set_class p_sucex f5_findsg f6_findsg a_sup_set_class a_csuc f8_findsg p_eqvinc e4_findsg e0_findsg f8_findsg a_com a_wcel f0_findsg f5_findsg a_sup_set_class f8_findsg a_wceq f1_findsg p_syl5ibr e2_findsg f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_csuc a_wceq f0_findsg f3_findsg p_biimpd f5_findsg a_sup_set_class f8_findsg a_wceq f8_findsg a_com a_wcel f0_findsg f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_csuc a_wceq f3_findsg p_sylan9r f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_csuc a_wceq f5_findsg a_sup_set_class f8_findsg a_wceq a_wa f8_findsg a_com a_wcel f3_findsg a_wi f5_findsg p_exlimiv f6_findsg a_sup_set_class a_csuc f8_findsg a_wceq f5_findsg a_sup_set_class f6_findsg a_sup_set_class a_csuc a_wceq f5_findsg a_sup_set_class f8_findsg a_wceq a_wa f5_findsg a_wex f8_findsg a_com a_wcel f3_findsg a_wi p_sylbi f8_findsg a_com a_wcel f3_findsg a_wi f6_findsg a_sup_set_class a_csuc f8_findsg p_eqcoms f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq f8_findsg a_com a_wcel f3_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss p_imim2i f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg a_com a_wcel f3_findsg a_wi a_wi f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi p_a1d f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq a_wi f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg a_com a_wcel f3_findsg p_com4r f8_findsg a_com a_wcel f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq a_wi f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi a_wi a_wi f6_findsg a_sup_set_class a_com a_wcel p_adantl f8_findsg f6_findsg a_sup_set_class a_csuc a_df-ne f8_findsg f6_findsg a_sup_set_class a_csuc a_wne f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq a_wn f8_findsg f6_findsg a_sup_set_class a_csuc a_wss p_anbi2i f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq p_annim f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wne a_wa f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq a_wn a_wa f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq a_wi a_wn p_bitri f8_findsg p_nnon f6_findsg a_sup_set_class p_nnon f8_findsg f6_findsg a_sup_set_class p_onsssuc f6_findsg a_sup_set_class p_suceloni f8_findsg f6_findsg a_sup_set_class a_csuc p_onelpss f6_findsg a_sup_set_class a_con0 a_wcel f8_findsg a_con0 a_wcel f6_findsg a_sup_set_class a_csuc a_con0 a_wcel f8_findsg f6_findsg a_sup_set_class a_csuc a_wcel f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wne a_wa a_wb p_sylan2 f8_findsg a_con0 a_wcel f6_findsg a_sup_set_class a_con0 a_wcel a_wa f8_findsg f6_findsg a_sup_set_class a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wcel f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wne a_wa p_bitrd f8_findsg a_com a_wcel f8_findsg a_con0 a_wcel f6_findsg a_sup_set_class a_con0 a_wcel f8_findsg f6_findsg a_sup_set_class a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wne a_wa a_wb f6_findsg a_sup_set_class a_com a_wcel p_syl2anr e5_findsg f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel a_wa f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg f3_findsg a_wi p_ex f3_findsg f8_findsg f6_findsg a_sup_set_class a_csuc a_wss a_ax-1 f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel a_wa f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg f3_findsg f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi p_syl8 f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel a_wa f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi p_a2d f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel a_wa f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi p_com23 f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel a_wa f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wne a_wa f8_findsg f6_findsg a_sup_set_class a_wss f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi a_wi p_sylbird f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq a_wi a_wn f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wne a_wa f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel a_wa f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi a_wi p_syl5bir f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel a_wa f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f8_findsg f6_findsg a_sup_set_class a_csuc a_wceq a_wi f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi a_wi p_pm2.61d f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi a_wi p_ex f6_findsg a_sup_set_class a_com a_wcel f8_findsg a_com a_wcel f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi p_a2d f8_findsg a_com a_wcel f8_findsg f5_findsg a_sup_set_class a_wss f0_findsg a_wi a_wi f8_findsg a_com a_wcel f8_findsg a_c0 a_wss f1_findsg a_wi a_wi f8_findsg a_com a_wcel f8_findsg f6_findsg a_sup_set_class a_wss f2_findsg a_wi a_wi f8_findsg a_com a_wcel f8_findsg f6_findsg a_sup_set_class a_csuc a_wss f3_findsg a_wi a_wi f8_findsg a_com a_wcel f8_findsg f7_findsg a_wss f4_findsg a_wi a_wi f5_findsg f6_findsg f7_findsg p_finds f7_findsg a_com a_wcel f8_findsg a_com a_wcel f8_findsg f7_findsg a_wss f4_findsg p_imp31 $.
$}

$(Substitutions. $)

$(Basis. $)

$(Induction hypothesis. $)

$(Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first three hypotheses establish the substitutions
       we need.  The last two are the basis and the induction hypothesis.
       Theorem Schema 22 of [Suppes] p. 136.  (Contributed by NM,
       29-Nov-2002.) $)

${
	$v ph ps ch th ta x y  $.
	$d x y ta  $.
	$d x ps  $.
	$d x ch  $.
	$d x th  $.
	$d y ph  $.
	f0_finds2 $f wff ph $.
	f1_finds2 $f wff ps $.
	f2_finds2 $f wff ch $.
	f3_finds2 $f wff th $.
	f4_finds2 $f wff ta $.
	f5_finds2 $f set x $.
	f6_finds2 $f set y $.
	e0_finds2 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	e1_finds2 $e |- ( x = y -> ( ph <-> ch ) ) $.
	e2_finds2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	e3_finds2 $e |- ( ta -> ps ) $.
	e4_finds2 $e |- ( y e. om -> ( ta -> ( ch -> th ) ) ) $.
	p_finds2 $p |- ( x e. om -> ( ta -> ph ) ) $= e3_finds2 p_0ex e0_finds2 f5_finds2 a_sup_set_class a_c0 a_wceq f0_finds2 f1_finds2 f4_finds2 p_imbi2d f4_finds2 f0_finds2 a_wi f4_finds2 f1_finds2 a_wi f5_finds2 a_c0 p_elab a_c0 f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel f4_finds2 f1_finds2 a_wi p_mpbir e4_finds2 f6_finds2 a_sup_set_class a_com a_wcel f4_finds2 f2_finds2 f3_finds2 p_a2d f6_finds2 p_vex e1_finds2 f5_finds2 a_sup_set_class f6_finds2 a_sup_set_class a_wceq f0_finds2 f2_finds2 f4_finds2 p_imbi2d f4_finds2 f0_finds2 a_wi f4_finds2 f2_finds2 a_wi f5_finds2 f6_finds2 a_sup_set_class p_elab f6_finds2 p_vex f6_finds2 a_sup_set_class p_sucex e2_finds2 f5_finds2 a_sup_set_class f6_finds2 a_sup_set_class a_csuc a_wceq f0_finds2 f3_finds2 f4_finds2 p_imbi2d f4_finds2 f0_finds2 a_wi f4_finds2 f3_finds2 a_wi f5_finds2 f6_finds2 a_sup_set_class a_csuc p_elab f6_finds2 a_sup_set_class a_com a_wcel f4_finds2 f2_finds2 a_wi f4_finds2 f3_finds2 a_wi f6_finds2 a_sup_set_class f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel f6_finds2 a_sup_set_class a_csuc f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel p_3imtr4g f6_finds2 a_sup_set_class f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel f6_finds2 a_sup_set_class a_csuc f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel a_wi f6_finds2 a_com p_rgen f6_finds2 f4_finds2 f0_finds2 a_wi f5_finds2 a_cab p_peano5 a_c0 f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel f6_finds2 a_sup_set_class f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel f6_finds2 a_sup_set_class a_csuc f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel a_wi f6_finds2 a_com a_wral a_com f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wss p_mp2an a_com f4_finds2 f0_finds2 a_wi f5_finds2 a_cab f5_finds2 a_sup_set_class p_sseli f4_finds2 f0_finds2 a_wi f5_finds2 p_abid f5_finds2 a_sup_set_class a_com a_wcel f5_finds2 a_sup_set_class f4_finds2 f0_finds2 a_wi f5_finds2 a_cab a_wcel f4_finds2 f0_finds2 a_wi p_sylib $.
$}

$(Substitutions. $)

$(Basis. $)

$(Induction hypothesis. $)

$(Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first three hypotheses establish the substitutions
       we need.  The last two are the basis and the induction hypothesis.
       Theorem Schema 22 of [Suppes] p. 136.  (Contributed by NM,
       22-Mar-2006.) $)

${
	$v ph ps ch th x y  $.
	$d x y  $.
	$d x ps  $.
	$d x ch  $.
	$d x th  $.
	$d y ph  $.
	f0_finds1 $f wff ph $.
	f1_finds1 $f wff ps $.
	f2_finds1 $f wff ch $.
	f3_finds1 $f wff th $.
	f4_finds1 $f set x $.
	f5_finds1 $f set y $.
	e0_finds1 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	e1_finds1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	e2_finds1 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	e3_finds1 $e |- ps $.
	e4_finds1 $e |- ( y e. om -> ( ch -> th ) ) $.
	p_finds1 $p |- ( x e. om -> ph ) $= a_c0 p_eqid e0_finds1 e1_finds1 e2_finds1 e3_finds1 f1_finds1 a_c0 a_c0 a_wceq p_a1i e4_finds1 f5_finds1 a_sup_set_class a_com a_wcel f2_finds1 f3_finds1 a_wi a_c0 a_c0 a_wceq p_a1d f0_finds1 f1_finds1 f2_finds1 f3_finds1 a_c0 a_c0 a_wceq f4_finds1 f5_finds1 p_finds2 f4_finds1 a_sup_set_class a_com a_wcel a_c0 a_c0 a_wceq f0_finds1 p_mpi $.
$}

$(Finite induction with explicit substitution.  The first hypothesis is
       the basis and the second is the induction hypothesis.  Theorem Schema 22
       of [Suppes] p. 136.  See ~ tfindes for the transfinite version.
       (Contributed by Raph Levien, 9-Jul-2003.) $)

${
	$v ph x  $.
	$d x y z  $.
	$d y z ph  $.
	f0_findes $f wff ph $.
	f1_findes $f set x $.
	i0_findes $f set y $.
	i1_findes $f set z $.
	e0_findes $e |- [. (/) / x ]. ph $.
	e1_findes $e |- ( x e. om -> ( ph -> [. suc x / x ]. ph ) ) $.
	p_findes $p |- ( x e. om -> ph ) $= f0_findes f1_findes i1_findes a_c0 p_dfsbcq2 f0_findes i1_findes i0_findes f1_findes p_sbequ f0_findes f1_findes i1_findes i0_findes a_sup_set_class a_csuc p_dfsbcq2 f0_findes i1_findes f1_findes p_sbequ12r e0_findes i0_findes a_sup_set_class a_com a_wcel f1_findes p_nfv f0_findes f1_findes i0_findes p_nfs1v f0_findes f1_findes i0_findes a_sup_set_class a_csuc p_nfsbc1v f0_findes f1_findes i0_findes a_wsb f0_findes f1_findes i0_findes a_sup_set_class a_csuc a_wsbc f1_findes p_nfim i0_findes a_sup_set_class a_com a_wcel f0_findes f1_findes i0_findes a_wsb f0_findes f1_findes i0_findes a_sup_set_class a_csuc a_wsbc a_wi f1_findes p_nfim f1_findes a_sup_set_class i0_findes a_sup_set_class a_com p_eleq1 f0_findes f1_findes i0_findes p_sbequ12 f1_findes a_sup_set_class i0_findes a_sup_set_class p_suceq f0_findes f1_findes f1_findes a_sup_set_class a_csuc i0_findes a_sup_set_class a_csuc p_dfsbcq f1_findes a_sup_set_class i0_findes a_sup_set_class a_wceq f1_findes a_sup_set_class a_csuc i0_findes a_sup_set_class a_csuc a_wceq f0_findes f1_findes f1_findes a_sup_set_class a_csuc a_wsbc f0_findes f1_findes i0_findes a_sup_set_class a_csuc a_wsbc a_wb p_syl f1_findes a_sup_set_class i0_findes a_sup_set_class a_wceq f0_findes f0_findes f1_findes i0_findes a_wsb f0_findes f1_findes f1_findes a_sup_set_class a_csuc a_wsbc f0_findes f1_findes i0_findes a_sup_set_class a_csuc a_wsbc p_imbi12d f1_findes a_sup_set_class i0_findes a_sup_set_class a_wceq f1_findes a_sup_set_class a_com a_wcel i0_findes a_sup_set_class a_com a_wcel f0_findes f0_findes f1_findes f1_findes a_sup_set_class a_csuc a_wsbc a_wi f0_findes f1_findes i0_findes a_wsb f0_findes f1_findes i0_findes a_sup_set_class a_csuc a_wsbc a_wi p_imbi12d e1_findes f1_findes a_sup_set_class a_com a_wcel f0_findes f0_findes f1_findes f1_findes a_sup_set_class a_csuc a_wsbc a_wi a_wi i0_findes a_sup_set_class a_com a_wcel f0_findes f1_findes i0_findes a_wsb f0_findes f1_findes i0_findes a_sup_set_class a_csuc a_wsbc a_wi a_wi f1_findes i0_findes p_chvar f0_findes f1_findes i1_findes a_wsb f0_findes f1_findes a_c0 a_wsbc f0_findes f1_findes i0_findes a_wsb f0_findes f1_findes i0_findes a_sup_set_class a_csuc a_wsbc f0_findes i1_findes i0_findes f1_findes a_sup_set_class p_finds $.
$}


