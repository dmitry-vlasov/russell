$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Transfinite_induction.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The natural numbers (i.e. finite ordinals)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare new symbol. $)

$c om $.

$(Greek letter omega $)

$(Extend class notation to include the class of natural numbers. $)

${
	$v  $.
	a_com $a class om $.
$}

$(Define the class of natural numbers, which are all ordinal numbers that
       are less than every limit ordinal, i.e. all finite ordinals.  Our
       definition is a variant of the Definition of N of [BellMachover]
       p. 471.  See ~ dfom2 for an alternate definition.  Later, when we assume
       the Axiom of Infinity, we show ` om ` is a set in ~ omex , and ` om `
       can then be defined per ~ dfom3 (the smallest inductive set) and
       ~ dfom4 .

       _Note_: the natural numbers ` om ` are a subset of the ordinal numbers
       ~ df-on .  They are completely different from the natural numbers ` NN `
       ( ~ df-nn ) that are a subset of the complex numbers defined much later
       in our development, although the two sets have analogous properties and
       operations defined on them.  (Contributed by NM, 15-May-1994.) $)

${
	$v x y  $.
	$d x y  $.
	f0_df-om $f set x $.
	f1_df-om $f set y $.
	a_df-om $a |- om = { x e. On | A. y ( Lim y -> x e. y ) } $.
$}

$(An alternate definition of the set of natural numbers ` om ` .
       Definition 7.28 of [TakeutiZaring] p. 42, who use the symbol K_I for the
       inner class builder of non-limit ordinal numbers (see ~ nlimon ).
       (Contributed by NM, 1-Nov-2004.) $)

${
	$v x y  $.
	$d x z  $.
	$d y z  $.
	f0_dfom2 $f set x $.
	f1_dfom2 $f set y $.
	i0_dfom2 $f set z $.
	p_dfom2 $p |- om = { x e. On | suc x C_ { y e. On | -. Lim y } } $= f0_dfom2 i0_dfom2 a_df-om i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class p_onsssuc i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class p_ontri1 i0_dfom2 a_sup_set_class a_con0 a_wcel f0_dfom2 a_sup_set_class a_con0 a_wcel a_wa i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_wss i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn p_bitr3d i0_dfom2 a_sup_set_class a_con0 a_wcel f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn a_wb p_ancoms f1_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class p_limeq f1_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wceq f1_dfom2 a_sup_set_class a_wlim i0_dfom2 a_sup_set_class a_wlim p_notbid f1_dfom2 a_sup_set_class a_wlim a_wn i0_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 i0_dfom2 a_sup_set_class a_con0 p_elrab i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn a_wa a_wb f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel a_wa p_a1i f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel a_wa i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn a_wa p_imbi12d f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn a_wa a_wi p_pm5.74da i0_dfom2 p_vex i0_dfom2 a_sup_set_class a_cvv p_limelon i0_dfom2 a_sup_set_class a_cvv a_wcel i0_dfom2 a_sup_set_class a_wlim i0_dfom2 a_sup_set_class a_con0 a_wcel p_mpan i0_dfom2 a_sup_set_class a_wlim i0_dfom2 a_sup_set_class a_con0 a_wcel p_pm4.71ri i0_dfom2 a_sup_set_class a_wlim i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wa f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel p_imbi1i i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel p_impexp i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel p_con34b i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn p_ibar i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn a_wa f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn p_imbi2d i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn i0_dfom2 a_sup_set_class a_wlim a_wn a_wi i0_dfom2 a_sup_set_class a_con0 a_wcel f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn a_wa a_wi p_syl5bb i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn a_wa a_wi p_pm5.74i i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wa f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi a_wi i0_dfom2 a_sup_set_class a_con0 a_wcel f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn a_wa a_wi a_wi p_3bitri f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi a_wi i0_dfom2 a_sup_set_class a_con0 a_wcel f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wn i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim a_wn a_wa a_wi a_wi i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi p_syl6rbbr i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel p_impexp i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel p_simpr f0_dfom2 a_sup_set_class p_suceloni f0_dfom2 a_sup_set_class a_csuc i0_dfom2 a_sup_set_class p_onelon f0_dfom2 a_sup_set_class a_csuc a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel p_ex f0_dfom2 a_sup_set_class a_con0 a_wcel f0_dfom2 a_sup_set_class a_csuc a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel a_wi p_syl f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel p_ancrd f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel a_wa i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel p_impbid2 f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel a_wa i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel p_imbi1d i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi a_wi i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel a_wa i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi p_syl5bbr f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi i0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi a_wi i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi p_bitrd f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi i0_dfom2 p_albidv i0_dfom2 f0_dfom2 a_sup_set_class a_csuc f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab p_dfss2 f0_dfom2 a_sup_set_class a_con0 a_wcel i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi i0_dfom2 a_wal i0_dfom2 a_sup_set_class f0_dfom2 a_sup_set_class a_csuc a_wcel i0_dfom2 a_sup_set_class f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wcel a_wi i0_dfom2 a_wal f0_dfom2 a_sup_set_class a_csuc f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wss p_syl6bbr i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi i0_dfom2 a_wal f0_dfom2 a_sup_set_class a_csuc f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wss f0_dfom2 a_con0 p_rabbiia a_com i0_dfom2 a_sup_set_class a_wlim f0_dfom2 a_sup_set_class i0_dfom2 a_sup_set_class a_wcel a_wi i0_dfom2 a_wal f0_dfom2 a_con0 a_crab f0_dfom2 a_sup_set_class a_csuc f1_dfom2 a_sup_set_class a_wlim a_wn f1_dfom2 a_con0 a_crab a_wss f0_dfom2 a_con0 a_crab p_eqtri $.
$}

$(Membership in omega.  The left conjunct can be eliminated if we assume
       the Axiom of Infinity; see ~ elom3 .  (Contributed by NM,
       15-May-1994.) $)

${
	$v x A  $.
	$d A x y  $.
	f0_elom $f set x $.
	f1_elom $f class A $.
	i0_elom $f set y $.
	p_elom $p |- ( A e. om <-> ( A e. On /\ A. x ( Lim x -> A e. x ) ) ) $= i0_elom a_sup_set_class f1_elom f0_elom a_sup_set_class p_eleq1 i0_elom a_sup_set_class f1_elom a_wceq i0_elom a_sup_set_class f0_elom a_sup_set_class a_wcel f1_elom f0_elom a_sup_set_class a_wcel f0_elom a_sup_set_class a_wlim p_imbi2d i0_elom a_sup_set_class f1_elom a_wceq f0_elom a_sup_set_class a_wlim i0_elom a_sup_set_class f0_elom a_sup_set_class a_wcel a_wi f0_elom a_sup_set_class a_wlim f1_elom f0_elom a_sup_set_class a_wcel a_wi f0_elom p_albidv i0_elom f0_elom a_df-om f0_elom a_sup_set_class a_wlim i0_elom a_sup_set_class f0_elom a_sup_set_class a_wcel a_wi f0_elom a_wal f0_elom a_sup_set_class a_wlim f1_elom f0_elom a_sup_set_class a_wcel a_wi f0_elom a_wal i0_elom f1_elom a_con0 a_com p_elrab2 $.
$}

$(Omega is a subset of ` On ` .  (Contributed by NM, 13-Jun-1994.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)

${
	$v  $.
	$d x y  $.
	i0_omsson $f set x $.
	i1_omsson $f set y $.
	p_omsson $p |- om C_ On $= i0_omsson i1_omsson p_dfom2 i0_omsson a_sup_set_class a_csuc i1_omsson a_sup_set_class a_wlim a_wn i1_omsson a_con0 a_crab a_wss i0_omsson a_con0 p_ssrab2 a_com i0_omsson a_sup_set_class a_csuc i1_omsson a_sup_set_class a_wlim a_wn i1_omsson a_con0 a_crab a_wss i0_omsson a_con0 a_crab a_con0 p_eqsstri $.
$}

$(The class of natural numbers is a subclass of any (infinite) limit
       ordinal.  Exercise 1 of [TakeutiZaring] p. 44.  Remarkably, our proof
       does not require the Axiom of Infinity.  (Contributed by NM,
       30-Oct-2003.) $)

${
	$v A  $.
	$d x y A  $.
	f0_limomss $f class A $.
	i0_limomss $f set x $.
	i1_limomss $f set y $.
	p_limomss $p |- ( Lim A -> om C_ A ) $= f0_limomss p_limord f0_limomss p_ordeleqon i1_limomss i0_limomss a_sup_set_class p_elom i0_limomss a_sup_set_class a_com a_wcel i0_limomss a_sup_set_class a_con0 a_wcel i1_limomss a_sup_set_class a_wlim i0_limomss a_sup_set_class i1_limomss a_sup_set_class a_wcel a_wi i1_limomss a_wal p_simprbi i1_limomss a_sup_set_class f0_limomss p_limeq i1_limomss a_sup_set_class f0_limomss i0_limomss a_sup_set_class p_eleq2 i1_limomss a_sup_set_class f0_limomss a_wceq i1_limomss a_sup_set_class a_wlim f0_limomss a_wlim i0_limomss a_sup_set_class i1_limomss a_sup_set_class a_wcel i0_limomss a_sup_set_class f0_limomss a_wcel p_imbi12d i1_limomss a_sup_set_class a_wlim i0_limomss a_sup_set_class i1_limomss a_sup_set_class a_wcel a_wi f0_limomss a_wlim i0_limomss a_sup_set_class f0_limomss a_wcel a_wi i1_limomss f0_limomss a_con0 p_spcgv i0_limomss a_sup_set_class a_com a_wcel i1_limomss a_sup_set_class a_wlim i0_limomss a_sup_set_class i1_limomss a_sup_set_class a_wcel a_wi i1_limomss a_wal f0_limomss a_con0 a_wcel f0_limomss a_wlim i0_limomss a_sup_set_class f0_limomss a_wcel a_wi p_syl5 f0_limomss a_con0 a_wcel i0_limomss a_sup_set_class a_com a_wcel f0_limomss a_wlim i0_limomss a_sup_set_class f0_limomss a_wcel p_com23 f0_limomss a_con0 a_wcel f0_limomss a_wlim i0_limomss a_sup_set_class a_com a_wcel i0_limomss a_sup_set_class f0_limomss a_wcel a_wi p_imp f0_limomss a_con0 a_wcel f0_limomss a_wlim a_wa i0_limomss a_com f0_limomss p_ssrdv f0_limomss a_con0 a_wcel f0_limomss a_wlim a_com f0_limomss a_wss p_ex p_omsson f0_limomss a_con0 a_com p_sseq2 f0_limomss a_con0 a_wceq a_com f0_limomss a_wss a_com a_con0 a_wss p_mpbiri f0_limomss a_con0 a_wceq a_com f0_limomss a_wss f0_limomss a_wlim p_a1d f0_limomss a_con0 a_wcel f0_limomss a_wlim a_com f0_limomss a_wss a_wi f0_limomss a_con0 a_wceq p_jaoi f0_limomss a_word f0_limomss a_con0 a_wcel f0_limomss a_con0 a_wceq a_wo f0_limomss a_wlim a_com f0_limomss a_wss a_wi p_sylbi f0_limomss a_word f0_limomss a_wlim a_com f0_limomss a_wss p_mpcom $.
$}

$(A natural number is an ordinal number.  (Contributed by NM,
     27-Jun-1994.) $)

${
	$v A  $.
	f0_nnon $f class A $.
	p_nnon $p |- ( A e. om -> A e. On ) $= p_omsson a_com a_con0 f0_nnon p_sseli $.
$}

$(A natural number is an ordinal number.  (Contributed by NM,
       27-Jun-1994.) $)

${
	$v A  $.
	f0_nnoni $f class A $.
	e0_nnoni $e |- A e. om $.
	p_nnoni $p |- A e. On $= e0_nnoni f0_nnoni p_nnon f0_nnoni a_com a_wcel f0_nnoni a_con0 a_wcel a_ax-mp $.
$}

$(A natural number is ordinal.  (Contributed by NM, 17-Oct-1995.) $)

${
	$v A  $.
	f0_nnord $f class A $.
	p_nnord $p |- ( A e. om -> Ord A ) $= f0_nnord p_nnon f0_nnord p_eloni f0_nnord a_com a_wcel f0_nnord a_con0 a_wcel f0_nnord a_word p_syl $.
$}

$(Omega is ordinal.  Theorem 7.32 of [TakeutiZaring] p. 43.  (Contributed
       by NM, 18-Oct-1995.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)

${
	$v  $.
	$d x y z  $.
	i0_ordom $f set x $.
	i1_ordom $f set y $.
	i2_ordom $f set z $.
	p_ordom $p |- Ord om $= i1_ordom i0_ordom a_com p_dftr2 i0_ordom a_sup_set_class i1_ordom a_sup_set_class p_onelon i0_ordom a_sup_set_class a_con0 a_wcel i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i1_ordom a_sup_set_class a_con0 a_wcel p_expcom i2_ordom a_sup_set_class p_limord i2_ordom a_sup_set_class p_ordtr i2_ordom a_sup_set_class i1_ordom a_sup_set_class i0_ordom a_sup_set_class p_trel i2_ordom a_sup_set_class a_wlim i2_ordom a_sup_set_class a_word i2_ordom a_sup_set_class a_wtr i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i0_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wa i1_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wi p_3syl i2_ordom a_sup_set_class a_wlim i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i0_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel i1_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel p_exp3a i2_ordom a_sup_set_class a_wlim i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i0_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel i1_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wi p_com12 i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i2_ordom a_sup_set_class a_wlim i0_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel i1_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel p_a2d i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i2_ordom a_sup_set_class a_wlim i0_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wi i2_ordom a_sup_set_class a_wlim i1_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wi i2_ordom p_alimdv i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i0_ordom a_sup_set_class a_con0 a_wcel i1_ordom a_sup_set_class a_con0 a_wcel i2_ordom a_sup_set_class a_wlim i0_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wi i2_ordom a_wal i2_ordom a_sup_set_class a_wlim i1_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wi i2_ordom a_wal p_anim12d i2_ordom i0_ordom a_sup_set_class p_elom i2_ordom i1_ordom a_sup_set_class p_elom i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i0_ordom a_sup_set_class a_con0 a_wcel i2_ordom a_sup_set_class a_wlim i0_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wi i2_ordom a_wal a_wa i1_ordom a_sup_set_class a_con0 a_wcel i2_ordom a_sup_set_class a_wlim i1_ordom a_sup_set_class i2_ordom a_sup_set_class a_wcel a_wi i2_ordom a_wal a_wa i0_ordom a_sup_set_class a_com a_wcel i1_ordom a_sup_set_class a_com a_wcel p_3imtr4g i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i0_ordom a_sup_set_class a_com a_wcel i1_ordom a_sup_set_class a_com a_wcel p_imp i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i0_ordom a_sup_set_class a_com a_wcel a_wa i1_ordom a_sup_set_class a_com a_wcel a_wi i0_ordom a_ax-gen a_com a_wtr i1_ordom a_sup_set_class i0_ordom a_sup_set_class a_wcel i0_ordom a_sup_set_class a_com a_wcel a_wa i1_ordom a_sup_set_class a_com a_wcel a_wi i0_ordom a_wal i1_ordom p_mpgbir p_omsson p_ordon a_com a_con0 p_trssord a_com a_wtr a_com a_con0 a_wss a_con0 a_word a_com a_word p_mp3an $.
$}

$(A member of a natural number is a natural number.  (Contributed by NM,
     21-Jun-1998.) $)

${
	$v A B  $.
	f0_elnn $f class A $.
	f1_elnn $f class B $.
	p_elnn $p |- ( ( A e. B /\ B e. om ) -> A e. om ) $= p_ordom a_com p_ordtr a_com f0_elnn f1_elnn p_trel a_com a_word a_com a_wtr f0_elnn f1_elnn a_wcel f1_elnn a_com a_wcel a_wa f0_elnn a_com a_wcel a_wi p_mp2b $.
$}

$(The class of natural numbers ` om ` is either an ordinal number (if we
     accept the Axiom of Infinity) or the proper class of all ordinal numbers
     (if we deny the Axiom of Infinity).  Remark in [TakeutiZaring] p. 43.
     (Contributed by NM, 10-May-1998.) $)

${
	$v  $.
	p_omon $p |- ( om e. On \/ om = On ) $= p_ordom a_com p_ordeleqon a_com a_word a_com a_con0 a_wcel a_com a_con0 a_wceq a_wo p_mpbi $.
$}

$(Omega is an ordinal number.  (Contributed by Mario Carneiro,
       30-Jan-2013.) $)

${
	$v  $.
	p_omelon2 $p |- ( om e. _V -> om e. On ) $= p_omon a_com a_con0 a_wcel a_com a_con0 a_wceq p_ori p_onprc a_com a_con0 a_cvv p_eleq1 a_com a_con0 a_wceq a_com a_cvv a_wcel a_con0 a_cvv a_wcel p_mtbiri a_com a_con0 a_wcel a_wn a_com a_con0 a_wceq a_com a_cvv a_wcel a_wn p_syl a_com a_con0 a_wcel a_com a_cvv a_wcel p_con4i $.
$}

$(A natural number is not a limit ordinal.  (Contributed by NM,
       18-Oct-1995.) $)

${
	$v A  $.
	$d x A  $.
	f0_nnlim $f class A $.
	i0_nnlim $f set x $.
	p_nnlim $p |- ( A e. om -> -. Lim A ) $= f0_nnlim p_nnord f0_nnlim p_ordirr f0_nnlim a_com a_wcel f0_nnlim a_word f0_nnlim f0_nnlim a_wcel a_wn p_syl i0_nnlim f0_nnlim p_elom f0_nnlim a_com a_wcel f0_nnlim a_con0 a_wcel i0_nnlim a_sup_set_class a_wlim f0_nnlim i0_nnlim a_sup_set_class a_wcel a_wi i0_nnlim a_wal p_simprbi i0_nnlim a_sup_set_class f0_nnlim p_limeq i0_nnlim a_sup_set_class f0_nnlim f0_nnlim p_eleq2 i0_nnlim a_sup_set_class f0_nnlim a_wceq i0_nnlim a_sup_set_class a_wlim f0_nnlim a_wlim f0_nnlim i0_nnlim a_sup_set_class a_wcel f0_nnlim f0_nnlim a_wcel p_imbi12d i0_nnlim a_sup_set_class a_wlim f0_nnlim i0_nnlim a_sup_set_class a_wcel a_wi f0_nnlim a_wlim f0_nnlim f0_nnlim a_wcel a_wi i0_nnlim f0_nnlim a_com p_spcgv f0_nnlim a_com a_wcel i0_nnlim a_sup_set_class a_wlim f0_nnlim i0_nnlim a_sup_set_class a_wcel a_wi i0_nnlim a_wal f0_nnlim a_wlim f0_nnlim f0_nnlim a_wcel a_wi p_mpd f0_nnlim a_com a_wcel f0_nnlim a_wlim f0_nnlim f0_nnlim a_wcel p_mtod $.
$}

$(The class of natural numbers is a subclass of the class of non-limit
       ordinal numbers.  Exercise 4 of [TakeutiZaring] p. 42.  (Contributed by
       NM, 2-Nov-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)

${
	$v x  $.
	$d x  $.
	f0_omssnlim $f set x $.
	p_omssnlim $p |- om C_ { x e. On | -. Lim x } $= p_omsson f0_omssnlim a_sup_set_class p_nnlim f0_omssnlim a_sup_set_class a_wlim a_wn f0_omssnlim a_com p_rgen f0_omssnlim a_sup_set_class a_wlim a_wn f0_omssnlim a_con0 a_com p_ssrab a_com f0_omssnlim a_sup_set_class a_wlim a_wn f0_omssnlim a_con0 a_crab a_wss a_com a_con0 a_wss f0_omssnlim a_sup_set_class a_wlim a_wn f0_omssnlim a_com a_wral p_mpbir2an $.
$}

$(Omega is a limit ordinal.  Theorem 2.8 of [BellMachover] p. 473.  Our
     proof, however, does not require the Axiom of Infinity.  (Contributed by
     NM, 26-Mar-1995.)  (Proof shortened by Mario Carneiro, 2-Sep-2015.) $)

${
	$v  $.
	i0_limom $f set x $.
	p_limom $p |- Lim om $= p_ordom a_com p_ordeleqon p_ordom a_com p_ordirr a_com a_word a_com a_com a_wcel a_wn a_ax-mp i0_limom a_com p_elom a_com a_com a_wcel a_com a_con0 a_wcel i0_limom a_sup_set_class a_wlim a_com i0_limom a_sup_set_class a_wcel a_wi i0_limom a_wal p_baib a_com a_con0 a_wcel a_com a_com a_wcel i0_limom a_sup_set_class a_wlim a_com i0_limom a_sup_set_class a_wcel a_wi i0_limom a_wal p_mtbii i0_limom a_sup_set_class p_limomss p_ordom i0_limom a_sup_set_class p_limord a_com i0_limom a_sup_set_class p_ordsseleq i0_limom a_sup_set_class a_wlim a_com a_word i0_limom a_sup_set_class a_word a_com i0_limom a_sup_set_class a_wss a_com i0_limom a_sup_set_class a_wcel a_com i0_limom a_sup_set_class a_wceq a_wo a_wb p_sylancr i0_limom a_sup_set_class a_wlim a_com i0_limom a_sup_set_class a_wss a_com i0_limom a_sup_set_class a_wcel a_com i0_limom a_sup_set_class a_wceq a_wo p_mpbid i0_limom a_sup_set_class a_wlim a_com i0_limom a_sup_set_class a_wcel a_com i0_limom a_sup_set_class a_wceq p_ord a_com i0_limom a_sup_set_class p_limeq a_com i0_limom a_sup_set_class a_wceq a_com a_wlim i0_limom a_sup_set_class a_wlim p_biimprcd i0_limom a_sup_set_class a_wlim a_com i0_limom a_sup_set_class a_wcel a_wn a_com i0_limom a_sup_set_class a_wceq a_com a_wlim p_syld i0_limom a_sup_set_class a_wlim a_com i0_limom a_sup_set_class a_wcel a_com a_wlim p_con1d i0_limom a_sup_set_class a_wlim a_com a_wlim a_wn a_com i0_limom a_sup_set_class a_wcel p_com12 a_com a_wlim a_wn i0_limom a_sup_set_class a_wlim a_com i0_limom a_sup_set_class a_wcel a_wi i0_limom p_alrimiv a_com a_con0 a_wcel i0_limom a_sup_set_class a_wlim a_com i0_limom a_sup_set_class a_wcel a_wi i0_limom a_wal a_com a_wlim p_nsyl2 p_limon a_com a_con0 p_limeq a_com a_con0 a_wceq a_com a_wlim a_con0 a_wlim p_mpbiri a_com a_con0 a_wcel a_com a_wlim a_com a_con0 a_wceq p_jaoi a_com a_word a_com a_con0 a_wcel a_com a_con0 a_wceq a_wo a_com a_wlim p_sylbi a_com a_word a_com a_wlim a_ax-mp $.
$}

$(A class belongs to omega iff its successor does.  (Contributed by NM,
     3-Dec-1995.) $)

${
	$v A  $.
	f0_peano2b $f class A $.
	p_peano2b $p |- ( A e. om <-> suc A e. om ) $= p_limom a_com f0_peano2b p_limsuc a_com a_wlim f0_peano2b a_com a_wcel f0_peano2b a_csuc a_com a_wcel a_wb a_ax-mp $.
$}

$(A nonzero natural number is a successor.  (Contributed by NM,
       18-Feb-2004.) $)

${
	$v x A  $.
	$d x A  $.
	f0_nnsuc $f set x $.
	f1_nnsuc $f class A $.
	p_nnsuc $p |- ( ( A e. om /\ A =/= (/) ) -> E. x e. om A = suc x ) $= f1_nnsuc p_nnlim f1_nnsuc a_com a_wcel f1_nnsuc a_wlim a_wn f1_nnsuc a_c0 a_wne p_adantr f1_nnsuc p_nnord f0_nnsuc f1_nnsuc p_orduninsuc f1_nnsuc a_word f1_nnsuc f1_nnsuc a_cuni a_wceq f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_con0 a_wrex a_wn a_wb f1_nnsuc a_c0 a_wne p_adantr f1_nnsuc a_df-lim f1_nnsuc a_wlim f1_nnsuc a_word f1_nnsuc a_c0 a_wne f1_nnsuc f1_nnsuc a_cuni a_wceq a_w3a p_biimpri f1_nnsuc a_word f1_nnsuc a_c0 a_wne f1_nnsuc f1_nnsuc a_cuni a_wceq f1_nnsuc a_wlim p_3expia f1_nnsuc a_word f1_nnsuc a_c0 a_wne a_wa f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_con0 a_wrex a_wn f1_nnsuc f1_nnsuc a_cuni a_wceq f1_nnsuc a_wlim p_sylbird f1_nnsuc a_com a_wcel f1_nnsuc a_word f1_nnsuc a_c0 a_wne f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_con0 a_wrex a_wn f1_nnsuc a_wlim a_wi p_sylan f1_nnsuc a_com a_wcel f1_nnsuc a_c0 a_wne a_wa f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_con0 a_wrex f1_nnsuc a_wlim p_mt3d f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_com p_eleq1 f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f1_nnsuc a_com a_wcel f0_nnsuc a_sup_set_class a_csuc a_com a_wcel p_biimpcd f0_nnsuc a_sup_set_class p_peano2b f1_nnsuc a_com a_wcel f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_sup_set_class a_csuc a_com a_wcel f0_nnsuc a_sup_set_class a_com a_wcel p_syl6ibr f1_nnsuc a_com a_wcel f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_sup_set_class a_com a_wcel p_ancrd f1_nnsuc a_com a_wcel f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_sup_set_class a_com a_wcel f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq a_wa f0_nnsuc a_sup_set_class a_con0 a_wcel p_adantld f1_nnsuc a_com a_wcel f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_con0 a_com p_reximdv2 f1_nnsuc a_com a_wcel f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_con0 a_wrex f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_com a_wrex a_wi f1_nnsuc a_c0 a_wne p_adantr f1_nnsuc a_com a_wcel f1_nnsuc a_c0 a_wne a_wa f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_con0 a_wrex f1_nnsuc f0_nnsuc a_sup_set_class a_csuc a_wceq f0_nnsuc a_com a_wrex p_mpd $.
$}

$(An ordinal subclass of non-limit ordinals is a class of natural
       numbers.  Exercise 7 of [TakeutiZaring] p. 42.  (Contributed by NM,
       2-Nov-2004.) $)

${
	$v x A  $.
	$d x A  $.
	f0_ssnlim $f set x $.
	f1_ssnlim $f class A $.
	p_ssnlim $p |- ( ( Ord A /\ A C_ { x e. On | -. Lim x } ) -> A C_ om ) $= p_limom f1_ssnlim f0_ssnlim a_sup_set_class a_wlim a_wn f0_ssnlim a_con0 a_crab a_com p_ssel f0_ssnlim a_sup_set_class a_com p_limeq f0_ssnlim a_sup_set_class a_com a_wceq f0_ssnlim a_sup_set_class a_wlim a_com a_wlim p_notbid f0_ssnlim a_sup_set_class a_wlim a_wn a_com a_wlim a_wn f0_ssnlim a_com a_con0 p_elrab a_com f0_ssnlim a_sup_set_class a_wlim a_wn f0_ssnlim a_con0 a_crab a_wcel a_com a_con0 a_wcel a_com a_wlim a_wn p_simprbi f1_ssnlim f0_ssnlim a_sup_set_class a_wlim a_wn f0_ssnlim a_con0 a_crab a_wss a_com f1_ssnlim a_wcel a_com f0_ssnlim a_sup_set_class a_wlim a_wn f0_ssnlim a_con0 a_crab a_wcel a_com a_wlim a_wn p_syl6 f1_ssnlim f0_ssnlim a_sup_set_class a_wlim a_wn f0_ssnlim a_con0 a_crab a_wss a_com f1_ssnlim a_wcel a_com a_wlim p_mt2i f1_ssnlim f0_ssnlim a_sup_set_class a_wlim a_wn f0_ssnlim a_con0 a_crab a_wss a_com f1_ssnlim a_wcel a_wn f1_ssnlim a_word p_adantl p_ordom f1_ssnlim a_com p_ordtri1 f1_ssnlim a_word a_com a_word f1_ssnlim a_com a_wss a_com f1_ssnlim a_wcel a_wn a_wb p_mpan2 f1_ssnlim a_word f1_ssnlim a_com a_wss a_com f1_ssnlim a_wcel a_wn a_wb f1_ssnlim f0_ssnlim a_sup_set_class a_wlim a_wn f0_ssnlim a_con0 a_crab a_wss p_adantr f1_ssnlim a_word f1_ssnlim f0_ssnlim a_sup_set_class a_wlim a_wn f0_ssnlim a_con0 a_crab a_wss a_wa f1_ssnlim a_com a_wss a_com f1_ssnlim a_wcel a_wn p_mpbird $.
$}


