$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Derive_the_Null_Set_Axiom.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Theorems requiring subset and intersection existence

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(No set contains all sets.  Theorem 41 of [Suppes] p. 30.  (Contributed
       by NM, 23-Aug-1993.) $)

${
	$v x y  $.
	$d x y z  $.
	f0_nalset $f set x $.
	f1_nalset $f set y $.
	i0_nalset $f set z $.
	p_nalset $p |- -. E. x A. y y e. x $= f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel f0_nalset f1_nalset p_alexn i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel a_wn i0_nalset f1_nalset f0_nalset a_ax-sep i0_nalset f1_nalset f1_nalset p_elequ1 i0_nalset f1_nalset f0_nalset p_elequ1 i0_nalset f1_nalset i0_nalset p_elequ1 i0_nalset f1_nalset f1_nalset p_elequ2 i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wceq i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel p_bitrd i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wceq i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel p_notbid i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wceq i0_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel a_wn f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel a_wn p_anbi12d i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wceq i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel a_wn a_wa f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel a_wn a_wa p_bibi12d i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel a_wn a_wa a_wb f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel a_wn a_wa a_wb i0_nalset f1_nalset p_spv f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel p_pclem6 i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel a_wn a_wa a_wb i0_nalset a_wal f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel f1_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel a_wn a_wa a_wb f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel a_wn p_syl i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel a_wn a_wa a_wb i0_nalset a_wal f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel a_wn f1_nalset p_eximi i0_nalset a_sup_set_class f1_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel i0_nalset a_sup_set_class i0_nalset a_sup_set_class a_wcel a_wn a_wa a_wb i0_nalset a_wal f1_nalset a_wex f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel a_wn f1_nalset a_wex a_ax-mp f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel a_wn f1_nalset a_wex f1_nalset a_sup_set_class f0_nalset a_sup_set_class a_wcel f1_nalset a_wal f0_nalset a_wex a_wn f0_nalset p_mpgbi $.
$}

$(The universal class is not a member of itself (and thus is not a set).
       Proposition 5.21 of [TakeutiZaring] p. 21; our proof, however, does not
       depend on the Axiom of Regularity.  (Contributed by NM, 23-Aug-1993.) $)

${
	$v  $.
	$d x y  $.
	i0_vprc $f set x $.
	i1_vprc $f set y $.
	p_vprc $p |- -. _V e. _V $= i0_vprc i1_vprc p_nalset i1_vprc p_vex i1_vprc a_sup_set_class a_cvv a_wcel i1_vprc a_sup_set_class i0_vprc a_sup_set_class a_wcel p_tbt i1_vprc a_sup_set_class i0_vprc a_sup_set_class a_wcel i1_vprc a_sup_set_class i0_vprc a_sup_set_class a_wcel i1_vprc a_sup_set_class a_cvv a_wcel a_wb i1_vprc p_albii i1_vprc i0_vprc a_sup_set_class a_cvv p_dfcleq i1_vprc a_sup_set_class i0_vprc a_sup_set_class a_wcel i1_vprc a_wal i1_vprc a_sup_set_class i0_vprc a_sup_set_class a_wcel i1_vprc a_sup_set_class a_cvv a_wcel a_wb i1_vprc a_wal i0_vprc a_sup_set_class a_cvv a_wceq p_bitr4i i1_vprc a_sup_set_class i0_vprc a_sup_set_class a_wcel i1_vprc a_wal i0_vprc a_sup_set_class a_cvv a_wceq i0_vprc p_exbii i1_vprc a_sup_set_class i0_vprc a_sup_set_class a_wcel i1_vprc a_wal i0_vprc a_wex i0_vprc a_sup_set_class a_cvv a_wceq i0_vprc a_wex p_mtbi i0_vprc a_cvv p_isset a_cvv a_cvv a_wcel i0_vprc a_sup_set_class a_cvv a_wceq i0_vprc a_wex p_mtbir $.
$}

$(The universal class doesn't belong to any class.  (Contributed by FL,
     31-Dec-2006.) $)

${
	$v A  $.
	f0_nvel $f class A $.
	p_nvel $p |- -. _V e. A $= p_vprc a_cvv f0_nvel p_elex a_cvv f0_nvel a_wcel a_cvv a_cvv a_wcel p_mto $.
$}

$(The universal class does not exist.  (Contributed by NM, 4-Jul-2005.) $)

${
	$v x  $.
	f0_vnex $f set x $.
	p_vnex $p |- -. E. x x = _V $= p_vprc f0_vnex a_cvv p_isset a_cvv a_cvv a_wcel f0_vnex a_sup_set_class a_cvv a_wceq f0_vnex a_wex p_mtbi $.
$}

$(Separation Scheme (Aussonderung) using class notation.  Compare Exercise
       4 of [TakeutiZaring] p. 22.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d A x y  $.
	$d B x y  $.
	f0_inex1 $f class A $.
	f1_inex1 $f class B $.
	i0_inex1 $f set x $.
	i1_inex1 $f set y $.
	e0_inex1 $e |- A e. _V $.
	p_inex1 $p |- ( A i^i B ) e. _V $= e0_inex1 i1_inex1 a_sup_set_class f1_inex1 a_wcel i1_inex1 i0_inex1 f0_inex1 p_zfauscl i1_inex1 i0_inex1 a_sup_set_class f0_inex1 f1_inex1 a_cin p_dfcleq i1_inex1 a_sup_set_class f0_inex1 f1_inex1 p_elin i1_inex1 a_sup_set_class f0_inex1 f1_inex1 a_cin a_wcel i1_inex1 a_sup_set_class f0_inex1 a_wcel i1_inex1 a_sup_set_class f1_inex1 a_wcel a_wa i1_inex1 a_sup_set_class i0_inex1 a_sup_set_class a_wcel p_bibi2i i1_inex1 a_sup_set_class i0_inex1 a_sup_set_class a_wcel i1_inex1 a_sup_set_class f0_inex1 f1_inex1 a_cin a_wcel a_wb i1_inex1 a_sup_set_class i0_inex1 a_sup_set_class a_wcel i1_inex1 a_sup_set_class f0_inex1 a_wcel i1_inex1 a_sup_set_class f1_inex1 a_wcel a_wa a_wb i1_inex1 p_albii i0_inex1 a_sup_set_class f0_inex1 f1_inex1 a_cin a_wceq i1_inex1 a_sup_set_class i0_inex1 a_sup_set_class a_wcel i1_inex1 a_sup_set_class f0_inex1 f1_inex1 a_cin a_wcel a_wb i1_inex1 a_wal i1_inex1 a_sup_set_class i0_inex1 a_sup_set_class a_wcel i1_inex1 a_sup_set_class f0_inex1 a_wcel i1_inex1 a_sup_set_class f1_inex1 a_wcel a_wa a_wb i1_inex1 a_wal p_bitri i0_inex1 a_sup_set_class f0_inex1 f1_inex1 a_cin a_wceq i1_inex1 a_sup_set_class i0_inex1 a_sup_set_class a_wcel i1_inex1 a_sup_set_class f0_inex1 a_wcel i1_inex1 a_sup_set_class f1_inex1 a_wcel a_wa a_wb i1_inex1 a_wal i0_inex1 p_exbii i0_inex1 a_sup_set_class f0_inex1 f1_inex1 a_cin a_wceq i0_inex1 a_wex i1_inex1 a_sup_set_class i0_inex1 a_sup_set_class a_wcel i1_inex1 a_sup_set_class f0_inex1 a_wcel i1_inex1 a_sup_set_class f1_inex1 a_wcel a_wa a_wb i1_inex1 a_wal i0_inex1 a_wex p_mpbir i0_inex1 f0_inex1 f1_inex1 a_cin p_issetri $.
$}

$(Separation Scheme (Aussonderung) using class notation.  (Contributed by
       NM, 27-Apr-1994.) $)

${
	$v A B  $.
	f0_inex2 $f class A $.
	f1_inex2 $f class B $.
	e0_inex2 $e |- A e. _V $.
	p_inex2 $p |- ( B i^i A ) e. _V $= f1_inex2 f0_inex2 p_incom e0_inex2 f0_inex2 f1_inex2 p_inex1 f1_inex2 f0_inex2 a_cin f0_inex2 f1_inex2 a_cin a_cvv p_eqeltri $.
$}

$(Closed-form, generalized Separation Scheme.  (Contributed by NM,
       7-Apr-1995.) $)

${
	$v A B V  $.
	$d x A  $.
	$d x B  $.
	f0_inex1g $f class A $.
	f1_inex1g $f class B $.
	f2_inex1g $f class V $.
	i0_inex1g $f set x $.
	p_inex1g $p |- ( A e. V -> ( A i^i B ) e. _V ) $= i0_inex1g a_sup_set_class f0_inex1g f1_inex1g p_ineq1 i0_inex1g a_sup_set_class f0_inex1g a_wceq i0_inex1g a_sup_set_class f1_inex1g a_cin f0_inex1g f1_inex1g a_cin a_cvv p_eleq1d i0_inex1g p_vex i0_inex1g a_sup_set_class f1_inex1g p_inex1 i0_inex1g a_sup_set_class f1_inex1g a_cin a_cvv a_wcel f0_inex1g f1_inex1g a_cin a_cvv a_wcel i0_inex1g f0_inex1g f2_inex1g p_vtoclg $.
$}

$(The subset of a set is also a set.  Exercise 3 of [TakeutiZaring]
       p. 22.  This is one way to express the Axiom of Separation ~ ax-sep
       (a.k.a.  Subset Axiom).  (Contributed by NM, 27-Apr-1994.) $)

${
	$v A B  $.
	f0_ssex $f class A $.
	f1_ssex $f class B $.
	e0_ssex $e |- B e. _V $.
	p_ssex $p |- ( A C_ B -> A e. _V ) $= f0_ssex f1_ssex a_df-ss e0_ssex f1_ssex f0_ssex p_inex2 f0_ssex f1_ssex a_cin f0_ssex a_cvv p_eleq1 f0_ssex f1_ssex a_cin f0_ssex a_wceq f0_ssex f1_ssex a_cin a_cvv a_wcel f0_ssex a_cvv a_wcel p_mpbii f0_ssex f1_ssex a_wss f0_ssex f1_ssex a_cin f0_ssex a_wceq f0_ssex a_cvv a_wcel p_sylbi $.
$}

$(The subset of a set is also a set.  (Contributed by NM, 9-Sep-1993.) $)

${
	$v A B  $.
	f0_ssexi $f class A $.
	f1_ssexi $f class B $.
	e0_ssexi $e |- B e. _V $.
	e1_ssexi $e |- A C_ B $.
	p_ssexi $p |- A e. _V $= e1_ssexi e0_ssexi f0_ssexi f1_ssexi p_ssex f0_ssexi f1_ssexi a_wss f0_ssexi a_cvv a_wcel a_ax-mp $.
$}

$(The subset of a set is also a set.  Exercise 3 of [TakeutiZaring] p. 22
       (generalized).  (Contributed by NM, 14-Aug-1994.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	f0_ssexg $f class A $.
	f1_ssexg $f class B $.
	f2_ssexg $f class C $.
	i0_ssexg $f set x $.
	p_ssexg $p |- ( ( A C_ B /\ B e. C ) -> A e. _V ) $= i0_ssexg a_sup_set_class f1_ssexg f0_ssexg p_sseq2 i0_ssexg a_sup_set_class f1_ssexg a_wceq f0_ssexg i0_ssexg a_sup_set_class a_wss f0_ssexg f1_ssexg a_wss f0_ssexg a_cvv a_wcel p_imbi1d i0_ssexg p_vex f0_ssexg i0_ssexg a_sup_set_class p_ssex f0_ssexg i0_ssexg a_sup_set_class a_wss f0_ssexg a_cvv a_wcel a_wi f0_ssexg f1_ssexg a_wss f0_ssexg a_cvv a_wcel a_wi i0_ssexg f1_ssexg f2_ssexg p_vtoclg f1_ssexg f2_ssexg a_wcel f0_ssexg f1_ssexg a_wss f0_ssexg a_cvv a_wcel p_impcom $.
$}

$(A subclass of a set is a set.  Deduction form of ~ ssexg .  (Contributed
       by David Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_ssexd $f wff ph $.
	f1_ssexd $f class A $.
	f2_ssexd $f class B $.
	f3_ssexd $f class C $.
	e0_ssexd $e |- ( ph -> B e. C ) $.
	e1_ssexd $e |- ( ph -> A C_ B ) $.
	p_ssexd $p |- ( ph -> A e. _V ) $= e1_ssexd e0_ssexd f1_ssexd f2_ssexd f3_ssexd p_ssexg f0_ssexd f1_ssexd f2_ssexd a_wss f2_ssexd f3_ssexd a_wcel f1_ssexd a_cvv a_wcel p_syl2anc $.
$}

$(Existence of a difference.  (Contributed by NM, 26-May-1998.) $)

${
	$v A B V  $.
	f0_difexg $f class A $.
	f1_difexg $f class B $.
	f2_difexg $f class V $.
	p_difexg $p |- ( A e. V -> ( A \ B ) e. _V ) $= f0_difexg f1_difexg p_difss f0_difexg f1_difexg a_cdif f0_difexg f2_difexg p_ssexg f0_difexg f1_difexg a_cdif f0_difexg a_wss f0_difexg f2_difexg a_wcel f0_difexg f1_difexg a_cdif a_cvv a_wcel p_mpan $.
$}

$(Separation Scheme (Aussonderung) in terms of a class abstraction.
       (Contributed by NM, 8-Jun-1994.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d ph  $.
	f0_zfausab $f wff ph $.
	f1_zfausab $f set x $.
	f2_zfausab $f class A $.
	e0_zfausab $e |- A e. _V $.
	p_zfausab $p |- { x | ( x e. A /\ ph ) } e. _V $= e0_zfausab f0_zfausab f1_zfausab f2_zfausab p_ssab2 f1_zfausab a_sup_set_class f2_zfausab a_wcel f0_zfausab a_wa f1_zfausab a_cab f2_zfausab p_ssexi $.
$}

$(Separation Scheme in terms of a restricted class abstraction.
       (Contributed by NM, 23-Oct-1999.) $)

${
	$v ph x A V  $.
	$d x A  $.
	f0_rabexg $f wff ph $.
	f1_rabexg $f set x $.
	f2_rabexg $f class A $.
	f3_rabexg $f class V $.
	p_rabexg $p |- ( A e. V -> { x e. A | ph } e. _V ) $= f0_rabexg f1_rabexg f2_rabexg p_ssrab2 f0_rabexg f1_rabexg f2_rabexg a_crab f2_rabexg f3_rabexg p_ssexg f0_rabexg f1_rabexg f2_rabexg a_crab f2_rabexg a_wss f2_rabexg f3_rabexg a_wcel f0_rabexg f1_rabexg f2_rabexg a_crab a_cvv a_wcel p_mpan $.
$}

$(Separation Scheme in terms of a restricted class abstraction.
       (Contributed by NM, 19-Jul-1996.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_rabex $f wff ph $.
	f1_rabex $f set x $.
	f2_rabex $f class A $.
	e0_rabex $e |- A e. _V $.
	p_rabex $p |- { x e. A | ph } e. _V $= e0_rabex f0_rabex f1_rabex f2_rabex a_cvv p_rabexg f2_rabex a_cvv a_wcel f0_rabex f1_rabex f2_rabex a_crab a_cvv a_wcel a_ax-mp $.
$}

$(Membership in a class abstraction involving a subset.  Unlike ~ elabg ,
       ` A ` does not have to be a set.  (Contributed by NM, 29-Aug-2006.) $)

${
	$v ph ps x A B V  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_elssabg $f wff ph $.
	f1_elssabg $f wff ps $.
	f2_elssabg $f set x $.
	f3_elssabg $f class A $.
	f4_elssabg $f class B $.
	f5_elssabg $f class V $.
	e0_elssabg $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_elssabg $p |- ( B e. V -> ( A e. { x | ( x C_ B /\ ph ) } <-> ( A C_ B /\ ps ) ) ) $= f3_elssabg f4_elssabg f5_elssabg p_ssexg f3_elssabg f4_elssabg a_wss f4_elssabg f5_elssabg a_wcel f3_elssabg a_cvv a_wcel p_expcom f4_elssabg f5_elssabg a_wcel f3_elssabg f4_elssabg a_wss f3_elssabg a_cvv a_wcel f1_elssabg p_adantrd f2_elssabg a_sup_set_class f3_elssabg f4_elssabg p_sseq1 e0_elssabg f2_elssabg a_sup_set_class f3_elssabg a_wceq f2_elssabg a_sup_set_class f4_elssabg a_wss f3_elssabg f4_elssabg a_wss f0_elssabg f1_elssabg p_anbi12d f2_elssabg a_sup_set_class f4_elssabg a_wss f0_elssabg a_wa f3_elssabg f4_elssabg a_wss f1_elssabg a_wa f2_elssabg f3_elssabg a_cvv p_elab3g f4_elssabg f5_elssabg a_wcel f3_elssabg f4_elssabg a_wss f1_elssabg a_wa f3_elssabg a_cvv a_wcel a_wi f3_elssabg f2_elssabg a_sup_set_class f4_elssabg a_wss f0_elssabg a_wa f2_elssabg a_cab a_wcel f3_elssabg f4_elssabg a_wss f1_elssabg a_wa a_wb p_syl $.
$}

$(The intersection of a non-empty class exists.  Exercise 5 of
       [TakeutiZaring] p. 44 and its converse.  (Contributed by NM,
       13-Aug-2002.) $)

${
	$v A  $.
	$d x A  $.
	f0_intex $f class A $.
	i0_intex $f set x $.
	p_intex $p |- ( A =/= (/) <-> |^| A e. _V ) $= i0_intex f0_intex p_n0 i0_intex a_sup_set_class f0_intex p_intss1 i0_intex p_vex f0_intex a_cint i0_intex a_sup_set_class p_ssex i0_intex a_sup_set_class f0_intex a_wcel f0_intex a_cint i0_intex a_sup_set_class a_wss f0_intex a_cint a_cvv a_wcel p_syl i0_intex a_sup_set_class f0_intex a_wcel f0_intex a_cint a_cvv a_wcel i0_intex p_exlimiv f0_intex a_c0 a_wne i0_intex a_sup_set_class f0_intex a_wcel i0_intex a_wex f0_intex a_cint a_cvv a_wcel p_sylbi p_vprc f0_intex a_c0 p_inteq p_int0 f0_intex a_c0 a_wceq f0_intex a_cint a_c0 a_cint a_cvv p_syl6eq f0_intex a_c0 a_wceq f0_intex a_cint a_cvv a_cvv p_eleq1d f0_intex a_c0 a_wceq f0_intex a_cint a_cvv a_wcel a_cvv a_cvv a_wcel p_mtbiri f0_intex a_cint a_cvv a_wcel f0_intex a_c0 p_necon2ai f0_intex a_c0 a_wne f0_intex a_cint a_cvv a_wcel p_impbii $.
$}

$(If a class intersection is not a set, it must be the universe.
     (Contributed by NM, 3-Jul-2005.) $)

${
	$v A  $.
	f0_intnex $f class A $.
	p_intnex $p |- ( -. |^| A e. _V <-> |^| A = _V ) $= f0_intnex p_intex f0_intnex a_cint a_cvv a_wcel f0_intnex a_c0 p_necon1bbii f0_intnex a_c0 p_inteq p_int0 f0_intnex a_c0 a_wceq f0_intnex a_cint a_c0 a_cint a_cvv p_syl6eq f0_intnex a_cint a_cvv a_wcel a_wn f0_intnex a_c0 a_wceq f0_intnex a_cint a_cvv a_wceq p_sylbi p_vprc f0_intnex a_cint a_cvv a_cvv p_eleq1 f0_intnex a_cint a_cvv a_wceq f0_intnex a_cint a_cvv a_wcel a_cvv a_cvv a_wcel p_mtbiri f0_intnex a_cint a_cvv a_wcel a_wn f0_intnex a_cint a_cvv a_wceq p_impbii $.
$}

$(The intersection of a non-empty class abstraction exists.  (Contributed
       by NM, 21-Oct-2003.) $)

${
	$v ph x  $.
	$d x  $.
	$d ph  $.
	f0_intexab $f wff ph $.
	f1_intexab $f set x $.
	p_intexab $p |- ( E. x ph <-> |^| { x | ph } e. _V ) $= f0_intexab f1_intexab p_abn0 f0_intexab f1_intexab a_cab p_intex f0_intexab f1_intexab a_wex f0_intexab f1_intexab a_cab a_c0 a_wne f0_intexab f1_intexab a_cab a_cint a_cvv a_wcel p_bitr3i $.
$}

$(The intersection of a non-empty restricted class abstraction exists.
     (Contributed by NM, 21-Oct-2003.) $)

${
	$v ph x A  $.
	f0_intexrab $f wff ph $.
	f1_intexrab $f set x $.
	f2_intexrab $f class A $.
	p_intexrab $p |- ( E. x e. A ph <-> |^| { x e. A | ph } e. _V ) $= f1_intexrab a_sup_set_class f2_intexrab a_wcel f0_intexrab a_wa f1_intexrab p_intexab f0_intexrab f1_intexrab f2_intexrab a_df-rex f0_intexrab f1_intexrab f2_intexrab a_df-rab f0_intexrab f1_intexrab f2_intexrab a_crab f1_intexrab a_sup_set_class f2_intexrab a_wcel f0_intexrab a_wa f1_intexrab a_cab p_inteqi f0_intexrab f1_intexrab f2_intexrab a_crab a_cint f1_intexrab a_sup_set_class f2_intexrab a_wcel f0_intexrab a_wa f1_intexrab a_cab a_cint a_cvv p_eleq1i f1_intexrab a_sup_set_class f2_intexrab a_wcel f0_intexrab a_wa f1_intexrab a_wex f1_intexrab a_sup_set_class f2_intexrab a_wcel f0_intexrab a_wa f1_intexrab a_cab a_cint a_cvv a_wcel f0_intexrab f1_intexrab f2_intexrab a_wrex f0_intexrab f1_intexrab f2_intexrab a_crab a_cint a_cvv a_wcel p_3bitr4i $.
$}

$(The existence of an indexed union. ` x ` is normally a free-variable
       parameter in ` B ` , which should be read ` B ( x ) ` .  (Contributed by
       FL, 19-Sep-2011.) $)

${
	$v x A B C  $.
	$d A x y  $.
	$d B y  $.
	f0_iinexg $f set x $.
	f1_iinexg $f class A $.
	f2_iinexg $f class B $.
	f3_iinexg $f class C $.
	i0_iinexg $f set y $.
	p_iinexg $p |- ( ( A =/= (/) /\ A. x e. A B e. C ) -> |^|_ x e. A B e. _V ) $= f0_iinexg i0_iinexg f1_iinexg f2_iinexg f3_iinexg p_dfiin2g f2_iinexg f3_iinexg a_wcel f0_iinexg f1_iinexg a_wral f0_iinexg f1_iinexg f2_iinexg a_ciin i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg a_cab a_cint a_wceq f1_iinexg a_c0 a_wne p_adantl i0_iinexg f2_iinexg f3_iinexg p_elisset f2_iinexg f3_iinexg a_wcel i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex a_wi f0_iinexg f1_iinexg p_rgenw f2_iinexg f3_iinexg a_wcel i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex a_wi f0_iinexg f1_iinexg p_r19.2z f1_iinexg a_c0 a_wne f2_iinexg f3_iinexg a_wcel i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex a_wi f0_iinexg f1_iinexg a_wral f2_iinexg f3_iinexg a_wcel i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex a_wi f0_iinexg f1_iinexg a_wrex p_mpan2 f2_iinexg f3_iinexg a_wcel i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex f0_iinexg f1_iinexg p_r19.35 f1_iinexg a_c0 a_wne f2_iinexg f3_iinexg a_wcel i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex a_wi f0_iinexg f1_iinexg a_wrex f2_iinexg f3_iinexg a_wcel f0_iinexg f1_iinexg a_wral i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex f0_iinexg f1_iinexg a_wrex a_wi p_sylib f1_iinexg a_c0 a_wne f2_iinexg f3_iinexg a_wcel f0_iinexg f1_iinexg a_wral i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex f0_iinexg f1_iinexg a_wrex p_imp i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg i0_iinexg f1_iinexg p_rexcom4 f1_iinexg a_c0 a_wne f2_iinexg f3_iinexg a_wcel f0_iinexg f1_iinexg a_wral a_wa i0_iinexg a_sup_set_class f2_iinexg a_wceq i0_iinexg a_wex f0_iinexg f1_iinexg a_wrex i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg a_wex p_sylib i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg p_abn0 f1_iinexg a_c0 a_wne f2_iinexg f3_iinexg a_wcel f0_iinexg f1_iinexg a_wral a_wa i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg a_wex i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg a_cab a_c0 a_wne p_sylibr i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg a_cab p_intex f1_iinexg a_c0 a_wne f2_iinexg f3_iinexg a_wcel f0_iinexg f1_iinexg a_wral a_wa i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg a_cab a_c0 a_wne i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg a_cab a_cint a_cvv a_wcel p_sylib f1_iinexg a_c0 a_wne f2_iinexg f3_iinexg a_wcel f0_iinexg f1_iinexg a_wral a_wa f0_iinexg f1_iinexg f2_iinexg a_ciin i0_iinexg a_sup_set_class f2_iinexg a_wceq f0_iinexg f1_iinexg a_wrex i0_iinexg a_cab a_cint a_cvv p_eqeltrd $.
$}

$(Absorption of a redundant conjunct in the intersection of a class
       abstraction.  (Contributed by NM, 3-Jul-2005.) $)

${
	$v ph ps ch x y A  $.
	$d x y  $.
	$d x A  $.
	$d y ph  $.
	$d x ps  $.
	$d x ch  $.
	f0_intabs $f wff ph $.
	f1_intabs $f wff ps $.
	f2_intabs $f wff ch $.
	f3_intabs $f set x $.
	f4_intabs $f set y $.
	f5_intabs $f class A $.
	e0_intabs $e |- ( x = y -> ( ph <-> ps ) ) $.
	e1_intabs $e |- ( x = |^| { y | ps } -> ( ph <-> ch ) ) $.
	e2_intabs $e |- ( |^| { y | ps } C_ A /\ ch ) $.
	p_intabs $p |- |^| { x | ( x C_ A /\ ph ) } = |^| { x | ph } $= f3_intabs a_sup_set_class f1_intabs f4_intabs a_cab a_cint f5_intabs p_sseq1 e1_intabs f3_intabs a_sup_set_class f1_intabs f4_intabs a_cab a_cint a_wceq f3_intabs a_sup_set_class f5_intabs a_wss f1_intabs f4_intabs a_cab a_cint f5_intabs a_wss f0_intabs f2_intabs p_anbi12d e2_intabs f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f1_intabs f4_intabs a_cab a_cint f5_intabs a_wss f2_intabs a_wa f3_intabs f1_intabs f4_intabs a_cab a_cint a_cvv p_intmin3 f1_intabs f4_intabs a_cab p_intnex f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint p_ssv f1_intabs f4_intabs a_cab a_cint a_cvv f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint p_sseq2 f1_intabs f4_intabs a_cab a_cint a_cvv a_wceq f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint f1_intabs f4_intabs a_cab a_cint a_wss f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint a_cvv a_wss p_mpbiri f1_intabs f4_intabs a_cab a_cint a_cvv a_wcel a_wn f1_intabs f4_intabs a_cab a_cint a_cvv a_wceq f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint f1_intabs f4_intabs a_cab a_cint a_wss p_sylbi f1_intabs f4_intabs a_cab a_cint a_cvv a_wcel f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint f1_intabs f4_intabs a_cab a_cint a_wss p_pm2.61i e0_intabs f0_intabs f1_intabs f3_intabs f4_intabs p_cbvabv f0_intabs f3_intabs a_cab f1_intabs f4_intabs a_cab p_inteqi f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint f1_intabs f4_intabs a_cab a_cint f0_intabs f3_intabs a_cab a_cint p_sseqtr4i f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs p_simpr f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f0_intabs f3_intabs p_ss2abi f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab f0_intabs f3_intabs a_cab p_intss f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab f0_intabs f3_intabs a_cab a_wss f0_intabs f3_intabs a_cab a_cint f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint a_wss a_ax-mp f3_intabs a_sup_set_class f5_intabs a_wss f0_intabs a_wa f3_intabs a_cab a_cint f0_intabs f3_intabs a_cab a_cint p_eqssi $.
$}

$(The intersection of a union ` U. A ` with a class ` B ` is equal to the
       union of the intersections of each element of ` A ` with ` B ` .
       (Contributed by FL, 24-Mar-2007.) $)

${
	$v x y A B  $.
	$d A x y z  $.
	$d B x y z  $.
	f0_inuni $f set x $.
	f1_inuni $f set y $.
	f2_inuni $f class A $.
	f3_inuni $f class B $.
	i0_inuni $f set z $.
	p_inuni $p |- ( U. A i^i B ) = U. { x | E. y e. A x = ( y i^i B ) } $= f1_inuni i0_inuni a_sup_set_class f2_inuni p_eluni2 i0_inuni a_sup_set_class f2_inuni a_cuni a_wcel i0_inuni a_sup_set_class f1_inuni a_sup_set_class a_wcel f1_inuni f2_inuni a_wrex i0_inuni a_sup_set_class f3_inuni a_wcel p_anbi1i i0_inuni a_sup_set_class f2_inuni a_cuni f3_inuni p_elin i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex p_ancom f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel f1_inuni f2_inuni p_r19.41v i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex a_wa f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f1_inuni f2_inuni a_wrex p_bitr4i i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex a_wa f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f1_inuni f2_inuni a_wrex f0_inuni p_exbii f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f1_inuni f0_inuni f2_inuni p_rexcom4 i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex a_wa f0_inuni a_wex f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f1_inuni f2_inuni a_wrex f0_inuni a_wex f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f0_inuni a_wex f1_inuni f2_inuni a_wrex p_bitr4i f1_inuni p_vex f1_inuni a_sup_set_class f3_inuni p_inex1 f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin i0_inuni a_sup_set_class p_eleq2 i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel i0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wcel f0_inuni f1_inuni a_sup_set_class f3_inuni a_cin p_ceqsexv i0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni p_elin f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f0_inuni a_wex i0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wcel i0_inuni a_sup_set_class f1_inuni a_sup_set_class a_wcel i0_inuni a_sup_set_class f3_inuni a_wcel a_wa p_bitri f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f0_inuni a_wex i0_inuni a_sup_set_class f1_inuni a_sup_set_class a_wcel i0_inuni a_sup_set_class f3_inuni a_wcel a_wa f1_inuni f2_inuni p_rexbii i0_inuni a_sup_set_class f1_inuni a_sup_set_class a_wcel i0_inuni a_sup_set_class f3_inuni a_wcel f1_inuni f2_inuni p_r19.41v f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f0_inuni a_wex f1_inuni f2_inuni a_wrex i0_inuni a_sup_set_class f1_inuni a_sup_set_class a_wcel i0_inuni a_sup_set_class f3_inuni a_wcel a_wa f1_inuni f2_inuni a_wrex i0_inuni a_sup_set_class f1_inuni a_sup_set_class a_wcel f1_inuni f2_inuni a_wrex i0_inuni a_sup_set_class f3_inuni a_wcel a_wa p_bitri i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex a_wa f0_inuni a_wex f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel a_wa f0_inuni a_wex f1_inuni f2_inuni a_wrex i0_inuni a_sup_set_class f1_inuni a_sup_set_class a_wcel f1_inuni f2_inuni a_wrex i0_inuni a_sup_set_class f3_inuni a_wcel a_wa p_bitri i0_inuni a_sup_set_class f2_inuni a_cuni a_wcel i0_inuni a_sup_set_class f3_inuni a_wcel a_wa i0_inuni a_sup_set_class f1_inuni a_sup_set_class a_wcel f1_inuni f2_inuni a_wrex i0_inuni a_sup_set_class f3_inuni a_wcel a_wa i0_inuni a_sup_set_class f2_inuni a_cuni f3_inuni a_cin a_wcel i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex a_wa f0_inuni a_wex p_3bitr4i f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex f0_inuni i0_inuni a_sup_set_class p_eluniab i0_inuni a_sup_set_class f2_inuni a_cuni f3_inuni a_cin a_wcel i0_inuni a_sup_set_class f0_inuni a_sup_set_class a_wcel f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex a_wa f0_inuni a_wex i0_inuni a_sup_set_class f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex f0_inuni a_cab a_cuni a_wcel p_bitr4i i0_inuni f2_inuni a_cuni f3_inuni a_cin f0_inuni a_sup_set_class f1_inuni a_sup_set_class f3_inuni a_cin a_wceq f1_inuni f2_inuni a_wrex f0_inuni a_cab a_cuni p_eqriv $.
$}

$(Membership in a power class.  Theorem 86 of [Suppes] p. 47.  (Contributed
     by NM, 7-Aug-2000.) $)

${
	$v A B V  $.
	f0_elpw2g $f class A $.
	f1_elpw2g $f class B $.
	f2_elpw2g $f class V $.
	p_elpw2g $p |- ( B e. V -> ( A e. ~P B <-> A C_ B ) ) $= f0_elpw2g f1_elpw2g p_elpwi f0_elpw2g f1_elpw2g f2_elpw2g p_ssexg f0_elpw2g f1_elpw2g a_cvv p_elpwg f0_elpw2g a_cvv a_wcel f0_elpw2g f1_elpw2g a_cpw a_wcel f0_elpw2g f1_elpw2g a_wss p_biimparc f0_elpw2g f1_elpw2g a_wss f1_elpw2g f2_elpw2g a_wcel f0_elpw2g a_cvv a_wcel f0_elpw2g f1_elpw2g a_cpw a_wcel p_syldan f0_elpw2g f1_elpw2g a_wss f1_elpw2g f2_elpw2g a_wcel f0_elpw2g f1_elpw2g a_cpw a_wcel p_expcom f1_elpw2g f2_elpw2g a_wcel f0_elpw2g f1_elpw2g a_cpw a_wcel f0_elpw2g f1_elpw2g a_wss p_impbid2 $.
$}

$(Membership in a power class.  Theorem 86 of [Suppes] p. 47.
       (Contributed by NM, 11-Oct-2007.) $)

${
	$v A B  $.
	f0_elpw2 $f class A $.
	f1_elpw2 $f class B $.
	e0_elpw2 $e |- B e. _V $.
	p_elpw2 $p |- ( A e. ~P B <-> A C_ B ) $= e0_elpw2 f0_elpw2 f1_elpw2 a_cvv p_elpw2g f1_elpw2 a_cvv a_wcel f0_elpw2 f1_elpw2 a_cpw a_wcel f0_elpw2 f1_elpw2 a_wss a_wb a_ax-mp $.
$}

$(The power set of a set is never a subset.  (Contributed by Stefan
       O'Rear, 22-Feb-2015.) $)

${
	$v A V  $.
	$d A x y  $.
	$d V x y  $.
	f0_pwnss $f class A $.
	f1_pwnss $f class V $.
	i0_pwnss $f set x $.
	i1_pwnss $f set y $.
	p_pwnss $p |- ( A e. V -> -. ~P A C_ A ) $= i1_pwnss a_sup_set_class i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab i1_pwnss a_sup_set_class i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab p_eleq12 i1_pwnss a_sup_set_class i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab a_wceq i1_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wcel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab a_wcel a_wb p_anidms i1_pwnss a_sup_set_class i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab a_wceq i1_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wcel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab a_wcel p_notbid i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_df-nel i0_pwnss a_sup_set_class i1_pwnss a_sup_set_class i0_pwnss a_sup_set_class i1_pwnss a_sup_set_class p_eleq12 i0_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wceq i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wcel i1_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wcel a_wb p_anidms i0_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wceq i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wcel i1_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wcel p_notbid i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wcel a_wn i0_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wceq i1_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wcel a_wn p_syl5bb i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i1_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wcel a_wn i0_pwnss i1_pwnss f0_pwnss p_cbvrabv i1_pwnss a_sup_set_class i1_pwnss a_sup_set_class a_wcel a_wn i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab a_wcel a_wn i1_pwnss i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab p_elrab2 i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab a_wcel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss a_wcel p_pclem6 i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab a_wcel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss a_wcel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab a_wcel a_wn a_wa a_wb i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss a_wcel a_wn a_ax-mp f0_pwnss a_cpw f0_pwnss i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab p_ssel f0_pwnss a_cpw f0_pwnss a_wss i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss a_cpw a_wcel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss a_wcel p_mtoi i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss p_ssrab2 i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss f1_pwnss p_elpw2g f0_pwnss f1_pwnss a_wcel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss a_cpw a_wcel i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss a_wss p_mpbiri f0_pwnss a_cpw f0_pwnss a_wss i0_pwnss a_sup_set_class i0_pwnss a_sup_set_class a_wnel i0_pwnss f0_pwnss a_crab f0_pwnss a_cpw a_wcel f0_pwnss f1_pwnss a_wcel p_nsyl3 $.
$}

$(No set equals its power set.  The sethood antecedent is necessary; compare
     ~ pwv .  (Contributed by NM, 17-Nov-2008.)  (Proof shortened by Mario
     Carneiro, 23-Dec-2016.) $)

${
	$v A V  $.
	f0_pwne $f class A $.
	f1_pwne $f class V $.
	p_pwne $p |- ( A e. V -> ~P A =/= A ) $= f0_pwne f1_pwne p_pwnss f0_pwne a_cpw f0_pwne p_eqimss f0_pwne a_cpw f0_pwne a_wss f0_pwne a_cpw f0_pwne p_necon3bi f0_pwne f1_pwne a_wcel f0_pwne a_cpw f0_pwne a_wss a_wn f0_pwne a_cpw f0_pwne a_wne p_syl $.
$}


