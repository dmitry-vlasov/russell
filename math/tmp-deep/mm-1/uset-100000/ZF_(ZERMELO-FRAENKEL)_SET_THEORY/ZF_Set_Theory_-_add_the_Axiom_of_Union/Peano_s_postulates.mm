$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/The_natural_numbers_(i_e__finite_ordinals).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Peano's postulates

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Zero is a natural number.  One of Peano's 5 postulates for arithmetic.
     Proposition 7.30(1) of [TakeutiZaring] p. 42.  Note:  Unlike most
     textbooks, our proofs of ~ peano1 through ~ peano5 do not use the Axiom of
     Infinity.  Unlike Takeuti and Zaring, they also do not use the Axiom of
     Regularity.  (Contributed by NM, 15-May-1994.) $)

${
	$v  $.
	p_peano1 $p |- (/) e. om $= p_limom a_com p_0ellim a_com a_wlim a_c0 a_com a_wcel a_ax-mp $.
$}

$(The successor of any natural number is a natural number.  One of Peano's 5
     postulates for arithmetic.  Proposition 7.30(2) of [TakeutiZaring] p. 42.
     (Contributed by NM, 3-Sep-2003.) $)

${
	$v A  $.
	f0_peano2 $f class A $.
	p_peano2 $p |- ( A e. om -> suc A e. om ) $= f0_peano2 p_peano2b f0_peano2 a_com a_wcel f0_peano2 a_csuc a_com a_wcel p_biimpi $.
$}

$(The successor of any natural number is not zero.  One of Peano's 5
     postulates for arithmetic.  Proposition 7.30(3) of [TakeutiZaring] p. 42.
     (Contributed by NM, 3-Sep-2003.) $)

${
	$v A  $.
	f0_peano3 $f class A $.
	p_peano3 $p |- ( A e. om -> suc A =/= (/) ) $= f0_peano3 p_nsuceq0 f0_peano3 a_csuc a_c0 a_wne f0_peano3 a_com a_wcel p_a1i $.
$}

$(Two natural numbers are equal iff their successors are equal, i.e. the
     successor function is one-to-one.  One of Peano's 5 postulates for
     arithmetic.  Proposition 7.30(4) of [TakeutiZaring] p. 43.  (Contributed
     by NM, 3-Sep-2003.) $)

${
	$v A B  $.
	f0_peano4 $f class A $.
	f1_peano4 $f class B $.
	p_peano4 $p |- ( ( A e. om /\ B e. om ) -> ( suc A = suc B <-> A = B ) ) $= f0_peano4 p_nnon f1_peano4 p_nnon f0_peano4 f1_peano4 p_suc11 f0_peano4 a_com a_wcel f0_peano4 a_con0 a_wcel f1_peano4 a_con0 a_wcel f0_peano4 a_csuc f1_peano4 a_csuc a_wceq f0_peano4 f1_peano4 a_wceq a_wb f1_peano4 a_com a_wcel p_syl2an $.
$}

$(The induction postulate: any class containing zero and closed under the
       successor operation contains all natural numbers.  One of Peano's 5
       postulates for arithmetic.  Proposition 7.30(5) of [TakeutiZaring]
       p. 43, except our proof does not require the Axiom of Infinity.  The
       more traditional statement of mathematical induction as a theorem
       schema, with a basis and an induction hypothesis, is derived from this
       theorem as theorem ~ findes .  (Contributed by NM, 18-Feb-2004.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_peano5 $f set x $.
	f1_peano5 $f class A $.
	i0_peano5 $f set y $.
	p_peano5 $p |- ( ( (/) e. A /\ A. x e. om ( x e. A -> suc x e. A ) ) -> om C_ A ) $= i0_peano5 a_sup_set_class a_com f1_peano5 p_eldifn i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel i0_peano5 a_sup_set_class f1_peano5 a_wcel a_wn a_c0 f1_peano5 a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral a_wa p_adantl i0_peano5 a_sup_set_class a_com f1_peano5 p_eldifi i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel i0_peano5 a_sup_set_class a_com a_wcel a_c0 f1_peano5 a_wcel p_adantl a_c0 f1_peano5 a_com p_elndif i0_peano5 a_sup_set_class a_c0 a_com f1_peano5 a_cdif p_eleq1 i0_peano5 a_sup_set_class a_c0 a_wceq i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_c0 a_com f1_peano5 a_cdif a_wcel p_biimpcd i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_c0 a_com f1_peano5 a_cdif a_wcel i0_peano5 a_sup_set_class a_c0 p_necon3bd a_c0 f1_peano5 a_wcel a_c0 a_com f1_peano5 a_cdif a_wcel a_wn i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel i0_peano5 a_sup_set_class a_c0 a_wne p_mpan9 f0_peano5 i0_peano5 a_sup_set_class p_nnsuc a_c0 f1_peano5 a_wcel i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_wa i0_peano5 a_sup_set_class a_com a_wcel i0_peano5 a_sup_set_class a_c0 a_wne i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_com a_wrex p_syl2anc a_c0 f1_peano5 a_wcel i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_com a_wrex f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral p_adantlr a_c0 f1_peano5 a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral a_wa i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_wa i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_com a_wrex a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq p_adantr f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com p_nfra1 i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq a_wa f0_peano5 p_nfv f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq a_wa f0_peano5 p_nfan i0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 p_nfv f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com p_rsp i0_peano5 a_sup_set_class a_com f1_peano5 p_eldifi f0_peano5 p_vex f0_peano5 a_sup_set_class p_sucid i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc f0_peano5 a_sup_set_class p_eleq2 i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_sup_set_class i0_peano5 a_sup_set_class a_wcel f0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wcel p_mpbiri i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_com p_eleq1 f0_peano5 a_sup_set_class p_peano2b i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq i0_peano5 a_sup_set_class a_com a_wcel f0_peano5 a_sup_set_class a_csuc a_com a_wcel f0_peano5 a_sup_set_class a_com a_wcel p_syl6bbr f0_peano5 a_sup_set_class i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif p_minel f0_peano5 a_sup_set_class a_com f1_peano5 p_neldif f0_peano5 a_sup_set_class i0_peano5 a_sup_set_class a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq a_wa f0_peano5 a_sup_set_class a_com a_wcel f0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_wn f0_peano5 a_sup_set_class f1_peano5 a_wcel p_sylan2 f0_peano5 a_sup_set_class a_com a_wcel f0_peano5 a_sup_set_class i0_peano5 a_sup_set_class a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq f0_peano5 a_sup_set_class f1_peano5 a_wcel p_exp32 i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq i0_peano5 a_sup_set_class a_com a_wcel f0_peano5 a_sup_set_class a_com a_wcel f0_peano5 a_sup_set_class i0_peano5 a_sup_set_class a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq f0_peano5 a_sup_set_class f1_peano5 a_wcel a_wi a_wi p_syl6bi i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq i0_peano5 a_sup_set_class a_com a_wcel f0_peano5 a_sup_set_class i0_peano5 a_sup_set_class a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq f0_peano5 a_sup_set_class f1_peano5 a_wcel a_wi p_mpid i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel i0_peano5 a_sup_set_class a_com a_wcel i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq f0_peano5 a_sup_set_class f1_peano5 a_wcel a_wi p_syl5 i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq f0_peano5 a_sup_set_class f1_peano5 a_wcel p_imp3a f0_peano5 a_sup_set_class a_csuc f1_peano5 i0_peano5 a_sup_set_class p_eleq1a f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq i0_peano5 a_sup_set_class f1_peano5 a_wcel p_com12 i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq a_wa f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel i0_peano5 a_sup_set_class f1_peano5 a_wcel p_imim12d i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq a_wa i0_peano5 a_sup_set_class f1_peano5 a_wcel p_com13 f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral f0_peano5 a_sup_set_class a_com a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq a_wa i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq i0_peano5 a_sup_set_class f1_peano5 a_wcel a_wi p_sylan9 f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq a_wa a_wa i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq i0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_com p_rexlimd f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_com a_wrex i0_peano5 a_sup_set_class f1_peano5 a_wcel a_wi p_exp32 f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_com a_wrex i0_peano5 a_sup_set_class f1_peano5 a_wcel a_wi a_wi a_wi a_wi a_c0 f1_peano5 a_wcel p_a1i a_c0 f1_peano5 a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_com a_wrex i0_peano5 a_sup_set_class f1_peano5 a_wcel a_wi p_imp41 a_c0 f1_peano5 a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral a_wa i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_wa a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq a_wa i0_peano5 a_sup_set_class f0_peano5 a_sup_set_class a_csuc a_wceq f0_peano5 a_com a_wrex i0_peano5 a_sup_set_class f1_peano5 a_wcel p_mpd a_c0 f1_peano5 a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral a_wa i0_peano5 a_sup_set_class a_com f1_peano5 a_cdif a_wcel a_wa a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq i0_peano5 a_sup_set_class f1_peano5 a_wcel p_mtand a_c0 f1_peano5 a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral a_wa a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq i0_peano5 a_com f1_peano5 a_cdif p_nrexdv p_ordom a_com f1_peano5 p_difss i0_peano5 a_com a_com f1_peano5 a_cdif p_tz7.5 a_com a_word a_com f1_peano5 a_cdif a_com a_wss a_com f1_peano5 a_cdif a_c0 a_wne a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq i0_peano5 a_com f1_peano5 a_cdif a_wrex p_mp3an12 a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq i0_peano5 a_com f1_peano5 a_cdif a_wrex a_com f1_peano5 a_cdif a_c0 p_necon1bi a_c0 f1_peano5 a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral a_wa a_com f1_peano5 a_cdif i0_peano5 a_sup_set_class a_cin a_c0 a_wceq i0_peano5 a_com f1_peano5 a_cdif a_wrex a_wn a_com f1_peano5 a_cdif a_c0 a_wceq p_syl a_com f1_peano5 p_ssdif0 a_c0 f1_peano5 a_wcel f0_peano5 a_sup_set_class f1_peano5 a_wcel f0_peano5 a_sup_set_class a_csuc f1_peano5 a_wcel a_wi f0_peano5 a_com a_wral a_wa a_com f1_peano5 a_cdif a_c0 a_wceq a_com f1_peano5 a_wss p_sylibr $.
$}

$(A natural number is either 0 or a successor.  (Contributed by NM,
       27-May-1998.) $)

${
	$v x A  $.
	$d x A  $.
	f0_nn0suc $f set x $.
	f1_nn0suc $f class A $.
	p_nn0suc $p |- ( A e. om -> ( A = (/) \/ E. x e. om A = suc x ) ) $= f1_nn0suc a_c0 a_df-ne f0_nn0suc f1_nn0suc p_nnsuc f1_nn0suc a_c0 a_wceq a_wn f1_nn0suc a_com a_wcel f1_nn0suc a_c0 a_wne f1_nn0suc f0_nn0suc a_sup_set_class a_csuc a_wceq f0_nn0suc a_com a_wrex p_sylan2br f1_nn0suc a_com a_wcel f1_nn0suc a_c0 a_wceq a_wn f1_nn0suc f0_nn0suc a_sup_set_class a_csuc a_wceq f0_nn0suc a_com a_wrex p_ex f1_nn0suc a_com a_wcel f1_nn0suc a_c0 a_wceq f1_nn0suc f0_nn0suc a_sup_set_class a_csuc a_wceq f0_nn0suc a_com a_wrex p_orrd $.
$}


