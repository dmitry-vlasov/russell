$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Introduce_the_Axiom_of_Union.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Ordinals (continued)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(The class of all ordinal numbers is ordinal.  Proposition 7.12 of
       [TakeutiZaring] p. 38, but without using the Axiom of Regularity.
       (Contributed by NM, 17-May-1994.) $)

${
	$v  $.
	$d x y  $.
	i0_ordon $f set x $.
	i1_ordon $f set y $.
	p_ordon $p |- Ord On $= p_tron p_onfr i0_ordon a_sup_set_class p_eloni i1_ordon a_sup_set_class p_eloni i0_ordon a_sup_set_class i1_ordon a_sup_set_class p_ordtri3or i0_ordon i1_ordon p_epel i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wceq p_biid i1_ordon i0_ordon p_epel i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_cep a_wbr i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wcel i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wceq i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wceq i1_ordon a_sup_set_class i0_ordon a_sup_set_class a_cep a_wbr i1_ordon a_sup_set_class i0_ordon a_sup_set_class a_wcel p_3orbi123i i0_ordon a_sup_set_class a_word i1_ordon a_sup_set_class a_word a_wa i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wcel i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wceq i1_ordon a_sup_set_class i0_ordon a_sup_set_class a_wcel a_w3o i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_cep a_wbr i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wceq i1_ordon a_sup_set_class i0_ordon a_sup_set_class a_cep a_wbr a_w3o p_sylibr i0_ordon a_sup_set_class a_con0 a_wcel i0_ordon a_sup_set_class a_word i1_ordon a_sup_set_class a_word i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_cep a_wbr i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wceq i1_ordon a_sup_set_class i0_ordon a_sup_set_class a_cep a_wbr a_w3o i1_ordon a_sup_set_class a_con0 a_wcel p_syl2an i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_cep a_wbr i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wceq i1_ordon a_sup_set_class i0_ordon a_sup_set_class a_cep a_wbr a_w3o i0_ordon i1_ordon a_con0 p_rgen2a i0_ordon i1_ordon a_con0 a_cep p_dfwe2 a_con0 a_cep a_wwe a_con0 a_cep a_wfr i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_cep a_wbr i0_ordon a_sup_set_class i1_ordon a_sup_set_class a_wceq i1_ordon a_sup_set_class i0_ordon a_sup_set_class a_cep a_wbr a_w3o i1_ordon a_con0 a_wral i0_ordon a_con0 a_wral p_mpbir2an a_con0 a_df-ord a_con0 a_word a_con0 a_wtr a_con0 a_cep a_wwe p_mpbir2an $.
$}

$(The epsilon relation well-orders the class of ordinal numbers.
     Proposition 4.8(g) of [Mendelson] p. 244.  (Contributed by NM,
     1-Nov-2003.) $)

${
	$v  $.
	p_epweon $p |- _E We On $= p_ordon a_con0 p_ordwe a_con0 a_word a_con0 a_cep a_wwe a_ax-mp $.
$}

$(No set contains all ordinal numbers.  Proposition 7.13 of [TakeutiZaring]
     p. 38, but without using the Axiom of Regularity.  This is also known as
     the Burali-Forti paradox (remark in [Enderton] p. 194).  In 1897, Cesare
     Burali-Forti noticed that since the "set" of all ordinal numbers is an
     ordinal class ( ~ ordon ), it must be both an element of the set of all
     ordinal numbers yet greater than every such element.  ZF set theory
     resolves this paradox by not allowing the class of all ordinal numbers to
     be a set (so instead it is a proper class).  Here we prove the denial of
     its existence.  (Contributed by NM, 18-May-1994.) $)

${
	$v  $.
	p_onprc $p |- -. On e. _V $= p_ordon a_con0 p_ordirr a_con0 a_word a_con0 a_con0 a_wcel a_wn a_ax-mp p_ordon a_con0 a_cvv p_elong a_con0 a_cvv a_wcel a_con0 a_con0 a_wcel a_con0 a_word p_mpbiri a_con0 a_cvv a_wcel a_con0 a_con0 a_wcel p_mto $.
$}

$(The union of a class of ordinal numbers is ordinal.  Proposition 7.19 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 30-May-1994.)  (Proof
       shortened by Andrew Salmon, 12-Aug-2011.) $)

${
	$v A  $.
	$d x y A  $.
	f0_ssorduni $f class A $.
	i0_ssorduni $f set x $.
	i1_ssorduni $f set y $.
	p_ssorduni $p |- ( A C_ On -> Ord U. A ) $= i1_ssorduni i0_ssorduni a_sup_set_class f0_ssorduni p_eluni2 f0_ssorduni a_con0 i1_ssorduni a_sup_set_class p_ssel i1_ssorduni a_sup_set_class i0_ssorduni a_sup_set_class p_onelss f0_ssorduni a_con0 a_wss i1_ssorduni a_sup_set_class f0_ssorduni a_wcel i1_ssorduni a_sup_set_class a_con0 a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wss a_wi p_syl6 i1_ssorduni a_sup_set_class f0_ssorduni a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wss p_anc2r f0_ssorduni a_con0 a_wss i1_ssorduni a_sup_set_class f0_ssorduni a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wss a_wi a_wi i1_ssorduni a_sup_set_class f0_ssorduni a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wss i1_ssorduni a_sup_set_class f0_ssorduni a_wcel a_wa a_wi a_wi p_syl i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class f0_ssorduni p_ssuni f0_ssorduni a_con0 a_wss i1_ssorduni a_sup_set_class f0_ssorduni a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wss i1_ssorduni a_sup_set_class f0_ssorduni a_wcel a_wa i0_ssorduni a_sup_set_class f0_ssorduni a_cuni a_wss p_syl8 f0_ssorduni a_con0 a_wss i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class f0_ssorduni a_cuni a_wss i1_ssorduni f0_ssorduni p_rexlimdv i0_ssorduni a_sup_set_class f0_ssorduni a_cuni a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i1_ssorduni f0_ssorduni a_wrex f0_ssorduni a_con0 a_wss i0_ssorduni a_sup_set_class f0_ssorduni a_cuni a_wss p_syl5bi f0_ssorduni a_con0 a_wss i0_ssorduni a_sup_set_class f0_ssorduni a_cuni a_wss i0_ssorduni f0_ssorduni a_cuni p_ralrimiv i0_ssorduni f0_ssorduni a_cuni p_dftr3 f0_ssorduni a_con0 a_wss i0_ssorduni a_sup_set_class f0_ssorduni a_cuni a_wss i0_ssorduni f0_ssorduni a_cuni a_wral f0_ssorduni a_cuni a_wtr p_sylibr i1_ssorduni i0_ssorduni a_sup_set_class f0_ssorduni p_eluni2 f0_ssorduni a_con0 i1_ssorduni a_sup_set_class p_ssel i1_ssorduni a_sup_set_class i0_ssorduni a_sup_set_class p_onelon i1_ssorduni a_sup_set_class a_con0 a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class a_con0 a_wcel p_ex f0_ssorduni a_con0 a_wss i1_ssorduni a_sup_set_class f0_ssorduni a_wcel i1_ssorduni a_sup_set_class a_con0 a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class a_con0 a_wcel a_wi p_syl6 f0_ssorduni a_con0 a_wss i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i0_ssorduni a_sup_set_class a_con0 a_wcel i1_ssorduni f0_ssorduni p_rexlimdv i0_ssorduni a_sup_set_class f0_ssorduni a_cuni a_wcel i0_ssorduni a_sup_set_class i1_ssorduni a_sup_set_class a_wcel i1_ssorduni f0_ssorduni a_wrex f0_ssorduni a_con0 a_wss i0_ssorduni a_sup_set_class a_con0 a_wcel p_syl5bi f0_ssorduni a_con0 a_wss i0_ssorduni f0_ssorduni a_cuni a_con0 p_ssrdv p_ordon f0_ssorduni a_cuni a_con0 p_trssord f0_ssorduni a_cuni a_wtr f0_ssorduni a_cuni a_con0 a_wss a_con0 a_word f0_ssorduni a_cuni a_word p_3exp f0_ssorduni a_cuni a_wtr f0_ssorduni a_cuni a_con0 a_wss a_con0 a_word f0_ssorduni a_cuni a_word p_mpii f0_ssorduni a_con0 a_wss f0_ssorduni a_cuni a_wtr f0_ssorduni a_cuni a_con0 a_wss f0_ssorduni a_cuni a_word p_sylc $.
$}

$(The union of a set of ordinal numbers is an ordinal number.  Theorem 9 of
     [Suppes] p. 132.  (Contributed by NM, 1-Nov-2003.) $)

${
	$v A V  $.
	f0_ssonuni $f class A $.
	f1_ssonuni $f class V $.
	p_ssonuni $p |- ( A e. V -> ( A C_ On -> U. A e. On ) ) $= f0_ssonuni p_ssorduni f0_ssonuni f1_ssonuni p_uniexg f0_ssonuni a_cuni a_cvv p_elong f0_ssonuni f1_ssonuni a_wcel f0_ssonuni a_cuni a_cvv a_wcel f0_ssonuni a_cuni a_con0 a_wcel f0_ssonuni a_cuni a_word a_wb p_syl f0_ssonuni a_con0 a_wss f0_ssonuni a_cuni a_con0 a_wcel f0_ssonuni f1_ssonuni a_wcel f0_ssonuni a_cuni a_word p_syl5ibr $.
$}

$(The union of a set of ordinal numbers is an ordinal number.  Corollary
       7N(d) of [Enderton] p. 193.  (Contributed by NM, 20-Sep-2003.) $)

${
	$v A  $.
	f0_ssonunii $f class A $.
	e0_ssonunii $e |- A e. _V $.
	p_ssonunii $p |- ( A C_ On -> U. A e. On ) $= e0_ssonunii f0_ssonunii a_cvv p_ssonuni f0_ssonunii a_cvv a_wcel f0_ssonunii a_con0 a_wss f0_ssonunii a_cuni a_con0 a_wcel a_wi a_ax-mp $.
$}

$(A way to express the ordinal property of a class in terms of the class of
     ordinal numbers.  Corollary 7.14 of [TakeutiZaring] p. 38 and its
     converse.  (Contributed by NM, 1-Jun-2003.) $)

${
	$v A  $.
	f0_ordeleqon $f class A $.
	p_ordeleqon $p |- ( Ord A <-> ( A e. On \/ A = On ) ) $= p_onprc a_con0 f0_ordeleqon p_elex a_con0 f0_ordeleqon a_wcel a_con0 a_cvv a_wcel p_mto p_ordon f0_ordeleqon a_con0 p_ordtri3or f0_ordeleqon a_word a_con0 a_word f0_ordeleqon a_con0 a_wcel f0_ordeleqon a_con0 a_wceq a_con0 f0_ordeleqon a_wcel a_w3o p_mpan2 f0_ordeleqon a_con0 a_wcel f0_ordeleqon a_con0 a_wceq a_con0 f0_ordeleqon a_wcel a_df-3or f0_ordeleqon a_word f0_ordeleqon a_con0 a_wcel f0_ordeleqon a_con0 a_wceq a_con0 f0_ordeleqon a_wcel a_w3o f0_ordeleqon a_con0 a_wcel f0_ordeleqon a_con0 a_wceq a_wo a_con0 f0_ordeleqon a_wcel a_wo p_sylib f0_ordeleqon a_word f0_ordeleqon a_con0 a_wcel f0_ordeleqon a_con0 a_wceq a_wo a_con0 f0_ordeleqon a_wcel p_ord f0_ordeleqon a_word f0_ordeleqon a_con0 a_wcel f0_ordeleqon a_con0 a_wceq a_wo a_con0 f0_ordeleqon a_wcel p_mt3i f0_ordeleqon p_eloni p_ordon f0_ordeleqon a_con0 p_ordeq f0_ordeleqon a_con0 a_wceq f0_ordeleqon a_word a_con0 a_word p_mpbiri f0_ordeleqon a_con0 a_wcel f0_ordeleqon a_word f0_ordeleqon a_con0 a_wceq p_jaoi f0_ordeleqon a_word f0_ordeleqon a_con0 a_wcel f0_ordeleqon a_con0 a_wceq a_wo p_impbii $.
$}

$(Any ordinal class is a subclass of the class of ordinal numbers.
     Corollary 7.15 of [TakeutiZaring] p. 38.  (Contributed by NM,
     18-May-1994.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.) $)

${
	$v A  $.
	f0_ordsson $f class A $.
	p_ordsson $p |- ( Ord A -> A C_ On ) $= p_ordon f0_ordsson p_ordeleqon f0_ordsson a_word f0_ordsson a_con0 a_wcel f0_ordsson a_con0 a_wceq a_wo p_biimpi f0_ordsson a_word f0_ordsson a_con0 a_wcel f0_ordsson a_con0 a_wceq a_wo a_con0 a_word p_adantr f0_ordsson a_con0 p_ordsseleq f0_ordsson a_word a_con0 a_word a_wa f0_ordsson a_con0 a_wss f0_ordsson a_con0 a_wcel f0_ordsson a_con0 a_wceq a_wo p_mpbird f0_ordsson a_word a_con0 a_word f0_ordsson a_con0 a_wss p_mpan2 $.
$}

$(An ordinal number is a subset of the class of ordinal numbers.
     (Contributed by NM, 5-Jun-1994.) $)

${
	$v A  $.
	f0_onss $f class A $.
	p_onss $p |- ( A e. On -> A C_ On ) $= f0_onss p_eloni f0_onss p_ordsson f0_onss a_con0 a_wcel f0_onss a_word f0_onss a_con0 a_wss p_syl $.
$}

$(Two ways of saying a class of ordinals is unbounded.  (Contributed by
     Mario Carneiro, 8-Jun-2013.) $)

${
	$v A  $.
	f0_ssonprc $f class A $.
	p_ssonprc $p |- ( A C_ On -> ( A e/ _V <-> U. A = On ) ) $= f0_ssonprc a_cvv a_df-nel f0_ssonprc p_ssorduni f0_ssonprc a_cuni p_ordeleqon f0_ssonprc a_con0 a_wss f0_ssonprc a_cuni a_word f0_ssonprc a_cuni a_con0 a_wcel f0_ssonprc a_cuni a_con0 a_wceq a_wo p_sylib f0_ssonprc a_con0 a_wss f0_ssonprc a_cuni a_con0 a_wcel f0_ssonprc a_cuni a_con0 a_wceq p_orcomd f0_ssonprc a_con0 a_wss f0_ssonprc a_cuni a_con0 a_wceq f0_ssonprc a_cuni a_con0 a_wcel p_ord f0_ssonprc a_cuni a_con0 p_elex f0_ssonprc p_uniexb f0_ssonprc a_cuni a_con0 a_wcel f0_ssonprc a_cuni a_cvv a_wcel f0_ssonprc a_cvv a_wcel p_sylibr f0_ssonprc a_con0 a_wss f0_ssonprc a_cuni a_con0 a_wceq a_wn f0_ssonprc a_cuni a_con0 a_wcel f0_ssonprc a_cvv a_wcel p_syl6 f0_ssonprc a_con0 a_wss f0_ssonprc a_cuni a_con0 a_wceq f0_ssonprc a_cvv a_wcel p_con1d p_onprc f0_ssonprc a_cvv p_uniexg f0_ssonprc a_cuni a_con0 a_cvv p_eleq1 f0_ssonprc a_cvv a_wcel f0_ssonprc a_cuni a_cvv a_wcel f0_ssonprc a_cuni a_con0 a_wceq a_con0 a_cvv a_wcel p_syl5ib f0_ssonprc a_cuni a_con0 a_wceq f0_ssonprc a_cvv a_wcel a_con0 a_cvv a_wcel p_mtoi f0_ssonprc a_con0 a_wss f0_ssonprc a_cvv a_wcel a_wn f0_ssonprc a_cuni a_con0 a_wceq p_impbid1 f0_ssonprc a_cvv a_wnel f0_ssonprc a_cvv a_wcel a_wn f0_ssonprc a_con0 a_wss f0_ssonprc a_cuni a_con0 a_wceq p_syl5bb $.
$}

$(The union of an ordinal number is an ordinal number.  (Contributed by NM,
     29-Sep-2006.) $)

${
	$v A  $.
	f0_onuni $f class A $.
	p_onuni $p |- ( A e. On -> U. A e. On ) $= f0_onuni p_onss f0_onuni a_con0 p_ssonuni f0_onuni a_con0 a_wcel f0_onuni a_con0 a_wss f0_onuni a_cuni a_con0 a_wcel p_mpd $.
$}

$(The union of an ordinal class is ordinal.  (Contributed by NM,
     12-Sep-2003.) $)

${
	$v A  $.
	f0_orduni $f class A $.
	p_orduni $p |- ( Ord A -> Ord U. A ) $= f0_orduni p_ordsson f0_orduni p_ssorduni f0_orduni a_word f0_orduni a_con0 a_wss f0_orduni a_cuni a_word p_syl $.
$}

$(The intersection (infimum) of a non-empty class of ordinal numbers
       belongs to the class.  Compare Exercise 4 of [TakeutiZaring] p. 45.
       (Contributed by NM, 31-Jan-1997.) $)

${
	$v A  $.
	$d x y z A  $.
	f0_onint $f class A $.
	i0_onint $f set x $.
	i1_onint $f set y $.
	i2_onint $f set z $.
	p_onint $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. A ) $= p_ordon i0_onint a_con0 f0_onint p_tz7.5 a_con0 a_word f0_onint a_con0 a_wss f0_onint a_c0 a_wne f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i0_onint f0_onint a_wrex p_mp3an1 f0_onint a_con0 i0_onint a_sup_set_class p_ssel f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel i0_onint a_sup_set_class a_con0 a_wcel p_imdistani f0_onint a_con0 i2_onint a_sup_set_class p_ssel i0_onint a_sup_set_class i2_onint a_sup_set_class p_ontri1 i0_onint a_sup_set_class i2_onint a_sup_set_class i1_onint a_sup_set_class p_ssel i0_onint a_sup_set_class a_con0 a_wcel i2_onint a_sup_set_class a_con0 a_wcel a_wa i2_onint a_sup_set_class i0_onint a_sup_set_class a_wcel a_wn i0_onint a_sup_set_class i2_onint a_sup_set_class a_wss i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel i1_onint a_sup_set_class i2_onint a_sup_set_class a_wcel a_wi p_syl6bir i0_onint a_sup_set_class a_con0 a_wcel i2_onint a_sup_set_class a_con0 a_wcel i2_onint a_sup_set_class i0_onint a_sup_set_class a_wcel a_wn i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel i1_onint a_sup_set_class i2_onint a_sup_set_class a_wcel a_wi a_wi p_ex f0_onint a_con0 a_wss i2_onint a_sup_set_class f0_onint a_wcel i2_onint a_sup_set_class a_con0 a_wcel i0_onint a_sup_set_class a_con0 a_wcel i2_onint a_sup_set_class i0_onint a_sup_set_class a_wcel a_wn i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel i1_onint a_sup_set_class i2_onint a_sup_set_class a_wcel a_wi a_wi p_sylan9 f0_onint a_con0 a_wss i0_onint a_sup_set_class a_con0 a_wcel a_wa i2_onint a_sup_set_class f0_onint a_wcel i2_onint a_sup_set_class i0_onint a_sup_set_class a_wcel a_wn i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel i1_onint a_sup_set_class i2_onint a_sup_set_class a_wcel p_com4r i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel f0_onint a_con0 a_wss i0_onint a_sup_set_class a_con0 a_wcel a_wa i2_onint a_sup_set_class f0_onint a_wcel i2_onint a_sup_set_class i0_onint a_sup_set_class a_wcel a_wn i1_onint a_sup_set_class i2_onint a_sup_set_class a_wcel a_wi p_imp31 i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel f0_onint a_con0 a_wss i0_onint a_sup_set_class a_con0 a_wcel a_wa a_wa i2_onint a_sup_set_class i0_onint a_sup_set_class a_wcel a_wn i1_onint a_sup_set_class i2_onint a_sup_set_class a_wcel i2_onint f0_onint p_ralimdva i2_onint f0_onint i0_onint a_sup_set_class p_disj i1_onint p_vex i2_onint i1_onint a_sup_set_class f0_onint p_elint2 i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel f0_onint a_con0 a_wss i0_onint a_sup_set_class a_con0 a_wcel a_wa a_wa i2_onint a_sup_set_class i0_onint a_sup_set_class a_wcel a_wn i2_onint f0_onint a_wral i1_onint a_sup_set_class i2_onint a_sup_set_class a_wcel i2_onint f0_onint a_wral f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i1_onint a_sup_set_class f0_onint a_cint a_wcel p_3imtr4g f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel a_wa i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel f0_onint a_con0 a_wss i0_onint a_sup_set_class a_con0 a_wcel a_wa f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i1_onint a_sup_set_class f0_onint a_cint a_wcel a_wi p_sylan2 i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i1_onint a_sup_set_class f0_onint a_cint a_wcel a_wi p_exp32 i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i1_onint a_sup_set_class f0_onint a_cint a_wcel p_com4l f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i1_onint a_sup_set_class i0_onint a_sup_set_class a_wcel i1_onint a_sup_set_class f0_onint a_cint a_wcel a_wi p_imp32 f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq a_wa a_wa i1_onint i0_onint a_sup_set_class f0_onint a_cint p_ssrdv i0_onint a_sup_set_class f0_onint p_intss1 i0_onint a_sup_set_class f0_onint a_wcel f0_onint a_cint i0_onint a_sup_set_class a_wss f0_onint a_con0 a_wss f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq p_ad2antrl f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq a_wa a_wa i0_onint a_sup_set_class f0_onint a_cint p_eqssd f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq a_wa a_wa i0_onint a_sup_set_class f0_onint a_cint f0_onint p_eleq1d f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq a_wa a_wa i0_onint a_sup_set_class f0_onint a_wcel f0_onint a_cint f0_onint a_wcel p_biimpd f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i0_onint a_sup_set_class f0_onint a_wcel f0_onint a_cint f0_onint a_wcel a_wi p_exp32 f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i0_onint a_sup_set_class f0_onint a_wcel f0_onint a_cint f0_onint a_wcel p_com34 f0_onint a_con0 a_wss i0_onint a_sup_set_class f0_onint a_wcel f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq f0_onint a_cint f0_onint a_wcel a_wi p_pm2.43d f0_onint a_con0 a_wss f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq f0_onint a_cint f0_onint a_wcel i0_onint f0_onint p_rexlimdv f0_onint a_con0 a_wss f0_onint a_c0 a_wne a_wa f0_onint i0_onint a_sup_set_class a_cin a_c0 a_wceq i0_onint f0_onint a_wrex f0_onint a_con0 a_wss f0_onint a_cint f0_onint a_wcel p_syl5 f0_onint a_con0 a_wss f0_onint a_c0 a_wne f0_onint a_cint f0_onint a_wcel p_anabsi5 $.
$}

$(The intersection of a class of ordinal numbers is zero iff the class
     contains zero.  (Contributed by NM, 24-Apr-2004.) $)

${
	$v A  $.
	f0_onint0 $f class A $.
	p_onint0 $p |- ( A C_ On -> ( |^| A = (/) <-> (/) e. A ) ) $= p_0ex f0_onint0 a_cint a_c0 a_cvv p_eleq1 f0_onint0 a_cint a_c0 a_wceq f0_onint0 a_cint a_cvv a_wcel a_c0 a_cvv a_wcel p_mpbiri f0_onint0 p_intex f0_onint0 a_cint a_c0 a_wceq f0_onint0 a_cint a_cvv a_wcel f0_onint0 a_c0 a_wne p_sylibr f0_onint0 p_onint f0_onint0 a_cint a_c0 a_wceq f0_onint0 a_con0 a_wss f0_onint0 a_c0 a_wne f0_onint0 a_cint f0_onint0 a_wcel p_sylan2 f0_onint0 a_cint a_c0 f0_onint0 p_eleq1 f0_onint0 a_cint a_c0 a_wceq f0_onint0 a_cint f0_onint0 a_wcel a_c0 f0_onint0 a_wcel a_wb f0_onint0 a_con0 a_wss p_adantl f0_onint0 a_con0 a_wss f0_onint0 a_cint a_c0 a_wceq a_wa f0_onint0 a_cint f0_onint0 a_wcel a_c0 f0_onint0 a_wcel p_mpbid f0_onint0 a_con0 a_wss f0_onint0 a_cint a_c0 a_wceq a_c0 f0_onint0 a_wcel p_ex f0_onint0 p_int0el f0_onint0 a_con0 a_wss f0_onint0 a_cint a_c0 a_wceq a_c0 f0_onint0 a_wcel p_impbid1 $.
$}

$(A non-empty class of ordinal numbers has the smallest member.  Exercise
       9 of [TakeutiZaring] p. 40.  (Contributed by NM, 3-Oct-2003.) $)

${
	$v x y A  $.
	$d x y A  $.
	f0_onssmin $f set x $.
	f1_onssmin $f set y $.
	f2_onssmin $f class A $.
	p_onssmin $p |- ( ( A C_ On /\ A =/= (/) ) -> E. x e. A A. y e. A x C_ y ) $= f2_onssmin p_onint f1_onssmin a_sup_set_class f2_onssmin p_intss1 f2_onssmin a_cint f1_onssmin a_sup_set_class a_wss f1_onssmin f2_onssmin p_rgen f0_onssmin a_sup_set_class f2_onssmin a_cint f1_onssmin a_sup_set_class p_sseq1 f0_onssmin a_sup_set_class f2_onssmin a_cint a_wceq f0_onssmin a_sup_set_class f1_onssmin a_sup_set_class a_wss f2_onssmin a_cint f1_onssmin a_sup_set_class a_wss f1_onssmin f2_onssmin p_ralbidv f0_onssmin a_sup_set_class f1_onssmin a_sup_set_class a_wss f1_onssmin f2_onssmin a_wral f2_onssmin a_cint f1_onssmin a_sup_set_class a_wss f1_onssmin f2_onssmin a_wral f0_onssmin f2_onssmin a_cint f2_onssmin p_rspcev f2_onssmin a_con0 a_wss f2_onssmin a_c0 a_wne a_wa f2_onssmin a_cint f2_onssmin a_wcel f2_onssmin a_cint f1_onssmin a_sup_set_class a_wss f1_onssmin f2_onssmin a_wral f0_onssmin a_sup_set_class f1_onssmin a_sup_set_class a_wss f1_onssmin f2_onssmin a_wral f0_onssmin f2_onssmin a_wrex p_sylancl $.
$}

$(If a property is true for some ordinal number, it is true for a minimal
       ordinal number.  This version uses explicit substitution.  Theorem
       Schema 62 of [Suppes] p. 228.  (Contributed by NM, 29-Sep-2003.) $)

${
	$v ph x  $.
	$d x  $.
	f0_onminesb $f wff ph $.
	f1_onminesb $f set x $.
	p_onminesb $p |- ( E. x e. On ph -> [. |^| { x e. On | ph } / x ]. ph ) $= f0_onminesb f1_onminesb a_con0 p_rabn0 f0_onminesb f1_onminesb a_con0 p_ssrab2 f0_onminesb f1_onminesb a_con0 a_crab p_onint f0_onminesb f1_onminesb a_con0 a_crab a_con0 a_wss f0_onminesb f1_onminesb a_con0 a_crab a_c0 a_wne f0_onminesb f1_onminesb a_con0 a_crab a_cint f0_onminesb f1_onminesb a_con0 a_crab a_wcel p_mpan f0_onminesb f1_onminesb a_con0 a_wrex f0_onminesb f1_onminesb a_con0 a_crab a_c0 a_wne f0_onminesb f1_onminesb a_con0 a_crab a_cint f0_onminesb f1_onminesb a_con0 a_crab a_wcel p_sylbir f1_onminesb a_con0 p_nfcv f0_onminesb f1_onminesb f0_onminesb f1_onminesb a_con0 a_crab a_cint a_con0 p_elrabsf f0_onminesb f1_onminesb a_con0 a_crab a_cint f0_onminesb f1_onminesb a_con0 a_crab a_wcel f0_onminesb f1_onminesb a_con0 a_crab a_cint a_con0 a_wcel f0_onminesb f1_onminesb f0_onminesb f1_onminesb a_con0 a_crab a_cint a_wsbc p_simprbi f0_onminesb f1_onminesb a_con0 a_wrex f0_onminesb f1_onminesb a_con0 a_crab a_cint f0_onminesb f1_onminesb a_con0 a_crab a_wcel f0_onminesb f1_onminesb f0_onminesb f1_onminesb a_con0 a_crab a_cint a_wsbc p_syl $.
$}

$(If a property is true for some ordinal number, it is true for a minimal
       ordinal number.  This version uses implicit substitution.  Theorem
       Schema 62 of [Suppes] p. 228.  (Contributed by NM, 3-Oct-2003.) $)

${
	$v ph ps x  $.
	$d x  $.
	$d ph  $.
	f0_onminsb $f wff ph $.
	f1_onminsb $f wff ps $.
	f2_onminsb $f set x $.
	e0_onminsb $e |- F/ x ps $.
	e1_onminsb $e |- ( x = |^| { x e. On | ph } -> ( ph <-> ps ) ) $.
	p_onminsb $p |- ( E. x e. On ph -> ps ) $= f0_onminsb f2_onminsb a_con0 p_rabn0 f0_onminsb f2_onminsb a_con0 p_ssrab2 f0_onminsb f2_onminsb a_con0 a_crab p_onint f0_onminsb f2_onminsb a_con0 a_crab a_con0 a_wss f0_onminsb f2_onminsb a_con0 a_crab a_c0 a_wne f0_onminsb f2_onminsb a_con0 a_crab a_cint f0_onminsb f2_onminsb a_con0 a_crab a_wcel p_mpan f0_onminsb f2_onminsb a_con0 a_wrex f0_onminsb f2_onminsb a_con0 a_crab a_c0 a_wne f0_onminsb f2_onminsb a_con0 a_crab a_cint f0_onminsb f2_onminsb a_con0 a_crab a_wcel p_sylbir f0_onminsb f2_onminsb a_con0 p_nfrab1 f2_onminsb f0_onminsb f2_onminsb a_con0 a_crab p_nfint f2_onminsb a_con0 p_nfcv e0_onminsb e1_onminsb f0_onminsb f1_onminsb f2_onminsb f0_onminsb f2_onminsb a_con0 a_crab a_cint a_con0 p_elrabf f0_onminsb f2_onminsb a_con0 a_crab a_cint f0_onminsb f2_onminsb a_con0 a_crab a_wcel f0_onminsb f2_onminsb a_con0 a_crab a_cint a_con0 a_wcel f1_onminsb p_simprbi f0_onminsb f2_onminsb a_con0 a_wrex f0_onminsb f2_onminsb a_con0 a_crab a_cint f0_onminsb f2_onminsb a_con0 a_crab a_wcel f1_onminsb p_syl $.
$}

$(The intersection of a non-empty collection of ordinal numbers is an
     ordinal number.  Compare Exercise 6 of [TakeutiZaring] p. 44.
     (Contributed by NM, 29-Jan-1997.) $)

${
	$v A  $.
	f0_oninton $f class A $.
	p_oninton $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. On ) $= f0_oninton p_onint f0_oninton a_con0 a_wss f0_oninton a_c0 a_wne f0_oninton a_cint f0_oninton a_wcel p_ex f0_oninton a_con0 f0_oninton a_cint p_ssel f0_oninton a_con0 a_wss f0_oninton a_c0 a_wne f0_oninton a_cint f0_oninton a_wcel f0_oninton a_cint a_con0 a_wcel p_syld f0_oninton a_con0 a_wss f0_oninton a_c0 a_wne f0_oninton a_cint a_con0 a_wcel p_imp $.
$}

$(The intersection of a class of ordinal numbers exists iff it is an ordinal
     number.  (Contributed by NM, 6-Nov-2003.) $)

${
	$v ph x  $.
	f0_onintrab $f wff ph $.
	f1_onintrab $f set x $.
	p_onintrab $p |- ( |^| { x e. On | ph } e. _V <-> |^| { x e. On | ph } e. On ) $= f0_onintrab f1_onintrab a_con0 a_crab p_intex f0_onintrab f1_onintrab a_con0 p_ssrab2 f0_onintrab f1_onintrab a_con0 a_crab p_oninton f0_onintrab f1_onintrab a_con0 a_crab a_con0 a_wss f0_onintrab f1_onintrab a_con0 a_crab a_c0 a_wne f0_onintrab f1_onintrab a_con0 a_crab a_cint a_con0 a_wcel p_mpan f0_onintrab f1_onintrab a_con0 a_crab a_cint a_cvv a_wcel f0_onintrab f1_onintrab a_con0 a_crab a_c0 a_wne f0_onintrab f1_onintrab a_con0 a_crab a_cint a_con0 a_wcel p_sylbir f0_onintrab f1_onintrab a_con0 a_crab a_cint a_con0 p_elex f0_onintrab f1_onintrab a_con0 a_crab a_cint a_cvv a_wcel f0_onintrab f1_onintrab a_con0 a_crab a_cint a_con0 a_wcel p_impbii $.
$}

$(An existence condition equivalent to an intersection's being an ordinal
     number.  (Contributed by NM, 6-Nov-2003.) $)

${
	$v ph x  $.
	f0_onintrab2 $f wff ph $.
	f1_onintrab2 $f set x $.
	p_onintrab2 $p |- ( E. x e. On ph <-> |^| { x e. On | ph } e. On ) $= f0_onintrab2 f1_onintrab2 a_con0 p_intexrab f0_onintrab2 f1_onintrab2 p_onintrab f0_onintrab2 f1_onintrab2 a_con0 a_wrex f0_onintrab2 f1_onintrab2 a_con0 a_crab a_cint a_cvv a_wcel f0_onintrab2 f1_onintrab2 a_con0 a_crab a_cint a_con0 a_wcel p_bitri $.
$}

$(No member of a set of ordinal numbers belongs to its minimum.
     (Contributed by NM, 2-Feb-1997.) $)

${
	$v A B  $.
	f0_onnmin $f class A $.
	f1_onnmin $f class B $.
	p_onnmin $p |- ( ( A C_ On /\ B e. A ) -> -. B e. |^| A ) $= f1_onnmin f0_onnmin p_intss1 f1_onnmin f0_onnmin a_wcel f0_onnmin a_cint f1_onnmin a_wss f0_onnmin a_con0 a_wss p_adantl f0_onnmin f1_onnmin p_ne0i f0_onnmin p_oninton f1_onnmin f0_onnmin a_wcel f0_onnmin a_con0 a_wss f0_onnmin a_c0 a_wne f0_onnmin a_cint a_con0 a_wcel p_sylan2 f0_onnmin a_con0 f1_onnmin p_ssel2 f0_onnmin a_cint f1_onnmin p_ontri1 f0_onnmin a_con0 a_wss f1_onnmin f0_onnmin a_wcel a_wa f0_onnmin a_cint a_con0 a_wcel f1_onnmin a_con0 a_wcel f0_onnmin a_cint f1_onnmin a_wss f1_onnmin f0_onnmin a_cint a_wcel a_wn a_wb p_syl2anc f0_onnmin a_con0 a_wss f1_onnmin f0_onnmin a_wcel a_wa f0_onnmin a_cint f1_onnmin a_wss f1_onnmin f0_onnmin a_cint a_wcel a_wn p_mpbid $.
$}

$(An ordinal number smaller than the minimum of a set of ordinal numbers
       does not have the property determining that set. ` ps ` is the wff
       resulting from the substitution of ` A ` for ` x ` in wff ` ph ` .
       (Contributed by NM, 9-Nov-2003.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_onnminsb $f wff ph $.
	f1_onnminsb $f wff ps $.
	f2_onnminsb $f set x $.
	f3_onnminsb $f class A $.
	e0_onnminsb $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_onnminsb $p |- ( A e. On -> ( A e. |^| { x e. On | ph } -> -. ps ) ) $= e0_onnminsb f0_onnminsb f1_onnminsb f2_onnminsb f3_onnminsb a_con0 p_elrab f0_onnminsb f2_onnminsb a_con0 p_ssrab2 f0_onnminsb f2_onnminsb a_con0 a_crab f3_onnminsb p_onnmin f0_onnminsb f2_onnminsb a_con0 a_crab a_con0 a_wss f3_onnminsb f0_onnminsb f2_onnminsb a_con0 a_crab a_wcel f3_onnminsb f0_onnminsb f2_onnminsb a_con0 a_crab a_cint a_wcel a_wn p_mpan f3_onnminsb a_con0 a_wcel f1_onnminsb a_wa f3_onnminsb f0_onnminsb f2_onnminsb a_con0 a_crab a_wcel f3_onnminsb f0_onnminsb f2_onnminsb a_con0 a_crab a_cint a_wcel a_wn p_sylbir f3_onnminsb a_con0 a_wcel f1_onnminsb f3_onnminsb f0_onnminsb f2_onnminsb a_con0 a_crab a_cint a_wcel a_wn p_ex f3_onnminsb a_con0 a_wcel f1_onnminsb f3_onnminsb f0_onnminsb f2_onnminsb a_con0 a_crab a_cint a_wcel p_con2d $.
$}

$(A way to show that an ordinal number equals the minimum of a non-empty
       collection of ordinal numbers: it must be in the collection, and it must
       not be larger than any member of the collection.  (Contributed by NM,
       14-Nov-2003.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_oneqmin $f set x $.
	f1_oneqmin $f class A $.
	f2_oneqmin $f class B $.
	p_oneqmin $p |- ( ( B C_ On /\ B =/= (/) ) -> ( A = |^| B <-> ( A e. B /\ A. x e. A -. x e. B ) ) ) $= f2_oneqmin p_onint f1_oneqmin f2_oneqmin a_cint f2_oneqmin p_eleq1 f2_oneqmin a_con0 a_wss f2_oneqmin a_c0 a_wne a_wa f1_oneqmin f2_oneqmin a_wcel f1_oneqmin f2_oneqmin a_cint a_wceq f2_oneqmin a_cint f2_oneqmin a_wcel p_syl5ibrcom f1_oneqmin f2_oneqmin a_cint f0_oneqmin a_sup_set_class p_eleq2 f1_oneqmin f2_oneqmin a_cint a_wceq f0_oneqmin a_sup_set_class f1_oneqmin a_wcel f0_oneqmin a_sup_set_class f2_oneqmin a_cint a_wcel p_biimpd f2_oneqmin f0_oneqmin a_sup_set_class p_onnmin f2_oneqmin a_con0 a_wss f0_oneqmin a_sup_set_class f2_oneqmin a_wcel f0_oneqmin a_sup_set_class f2_oneqmin a_cint a_wcel a_wn p_ex f2_oneqmin a_con0 a_wss f0_oneqmin a_sup_set_class f2_oneqmin a_wcel f0_oneqmin a_sup_set_class f2_oneqmin a_cint a_wcel p_con2d f1_oneqmin f2_oneqmin a_cint a_wceq f0_oneqmin a_sup_set_class f1_oneqmin a_wcel f0_oneqmin a_sup_set_class f2_oneqmin a_cint a_wcel f2_oneqmin a_con0 a_wss f0_oneqmin a_sup_set_class f2_oneqmin a_wcel a_wn p_syl9r f2_oneqmin a_con0 a_wss f1_oneqmin f2_oneqmin a_cint a_wceq f0_oneqmin a_sup_set_class f2_oneqmin a_wcel a_wn f0_oneqmin f1_oneqmin p_ralrimdv f2_oneqmin a_con0 a_wss f1_oneqmin f2_oneqmin a_cint a_wceq f0_oneqmin a_sup_set_class f2_oneqmin a_wcel a_wn f0_oneqmin f1_oneqmin a_wral a_wi f2_oneqmin a_c0 a_wne p_adantr f2_oneqmin a_con0 a_wss f2_oneqmin a_c0 a_wne a_wa f1_oneqmin f2_oneqmin a_cint a_wceq f1_oneqmin f2_oneqmin a_wcel f0_oneqmin a_sup_set_class f2_oneqmin a_wcel a_wn f0_oneqmin f1_oneqmin a_wral p_jcad f0_oneqmin f1_oneqmin f2_oneqmin p_oneqmini f2_oneqmin a_con0 a_wss f1_oneqmin f2_oneqmin a_wcel f0_oneqmin a_sup_set_class f2_oneqmin a_wcel a_wn f0_oneqmin f1_oneqmin a_wral a_wa f1_oneqmin f2_oneqmin a_cint a_wceq a_wi f2_oneqmin a_c0 a_wne p_adantr f2_oneqmin a_con0 a_wss f2_oneqmin a_c0 a_wne a_wa f1_oneqmin f2_oneqmin a_cint a_wceq f1_oneqmin f2_oneqmin a_wcel f0_oneqmin a_sup_set_class f2_oneqmin a_wcel a_wn f0_oneqmin f1_oneqmin a_wral a_wa p_impbid $.
$}

$(Problem 2.5(ii) of [BellMachover] p. 471.  (Contributed by NM,
       20-Sep-2003.) $)

${
	$v x y A  $.
	$d x y A  $.
	f0_bm2.5ii $f set x $.
	f1_bm2.5ii $f set y $.
	f2_bm2.5ii $f class A $.
	e0_bm2.5ii $e |- A e. _V $.
	p_bm2.5ii $p |- ( A C_ On -> U. A = |^| { x e. On | A. y e. A y C_ x } ) $= e0_bm2.5ii f2_bm2.5ii p_ssonunii f1_bm2.5ii f2_bm2.5ii f0_bm2.5ii a_sup_set_class p_unissb f2_bm2.5ii a_cuni f0_bm2.5ii a_sup_set_class a_wss f1_bm2.5ii a_sup_set_class f0_bm2.5ii a_sup_set_class a_wss f1_bm2.5ii f2_bm2.5ii a_wral a_wb f0_bm2.5ii a_sup_set_class a_con0 a_wcel p_a1i f2_bm2.5ii a_cuni f0_bm2.5ii a_sup_set_class a_wss f1_bm2.5ii a_sup_set_class f0_bm2.5ii a_sup_set_class a_wss f1_bm2.5ii f2_bm2.5ii a_wral f0_bm2.5ii a_con0 p_rabbiia f2_bm2.5ii a_cuni f0_bm2.5ii a_sup_set_class a_wss f0_bm2.5ii a_con0 a_crab f1_bm2.5ii a_sup_set_class f0_bm2.5ii a_sup_set_class a_wss f1_bm2.5ii f2_bm2.5ii a_wral f0_bm2.5ii a_con0 a_crab p_inteqi f0_bm2.5ii f2_bm2.5ii a_cuni a_con0 p_intmin f2_bm2.5ii a_cuni a_con0 a_wcel f1_bm2.5ii a_sup_set_class f0_bm2.5ii a_sup_set_class a_wss f1_bm2.5ii f2_bm2.5ii a_wral f0_bm2.5ii a_con0 a_crab a_cint f2_bm2.5ii a_cuni f0_bm2.5ii a_sup_set_class a_wss f0_bm2.5ii a_con0 a_crab a_cint f2_bm2.5ii a_cuni p_syl5reqr f2_bm2.5ii a_con0 a_wss f2_bm2.5ii a_cuni a_con0 a_wcel f2_bm2.5ii a_cuni f1_bm2.5ii a_sup_set_class f0_bm2.5ii a_sup_set_class a_wss f1_bm2.5ii f2_bm2.5ii a_wral f0_bm2.5ii a_con0 a_crab a_cint a_wceq p_syl $.
$}

$(If a wff is true for an ordinal number, there is the smallest ordinal
       number for which it is true.  (Contributed by NM, 2-Feb-1997.)  (Proof
       shortened by Mario Carneiro, 20-Nov-2016.) $)

${
	$v ph ps x y  $.
	$d x y z  $.
	$d y z ph  $.
	$d x z ps  $.
	f0_onminex $f wff ph $.
	f1_onminex $f wff ps $.
	f2_onminex $f set x $.
	f3_onminex $f set y $.
	i0_onminex $f set z $.
	e0_onminex $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_onminex $p |- ( E. x e. On ph -> E. x e. On ( ph /\ A. y e. x -. ps ) ) $= f0_onminex f2_onminex a_con0 p_ssrab2 f0_onminex f2_onminex a_con0 p_rabn0 f0_onminex f2_onminex a_con0 a_crab a_c0 a_wne f0_onminex f2_onminex a_con0 a_wrex p_biimpri f0_onminex f2_onminex a_con0 a_crab p_oninton f0_onminex f2_onminex a_con0 a_wrex f0_onminex f2_onminex a_con0 a_crab a_con0 a_wss f0_onminex f2_onminex a_con0 a_crab a_c0 a_wne f0_onminex f2_onminex a_con0 a_crab a_cint a_con0 a_wcel p_sylancr f0_onminex f2_onminex p_onminesb f0_onminex f2_onminex a_con0 p_ssrab2 f0_onminex f2_onminex a_con0 p_rabn0 f0_onminex f2_onminex a_con0 a_crab a_c0 a_wne f0_onminex f2_onminex a_con0 a_wrex p_biimpri f0_onminex f2_onminex a_con0 a_crab p_oninton f0_onminex f2_onminex a_con0 a_wrex f0_onminex f2_onminex a_con0 a_crab a_con0 a_wss f0_onminex f2_onminex a_con0 a_crab a_c0 a_wne f0_onminex f2_onminex a_con0 a_crab a_cint a_con0 a_wcel p_sylancr f0_onminex f2_onminex a_con0 a_crab a_cint p_onss f0_onminex f2_onminex a_con0 a_wrex f0_onminex f2_onminex a_con0 a_crab a_cint a_con0 a_wcel f0_onminex f2_onminex a_con0 a_crab a_cint a_con0 a_wss p_syl f0_onminex f2_onminex a_con0 a_wrex f0_onminex f2_onminex a_con0 a_crab a_cint a_con0 f3_onminex a_sup_set_class p_sseld e0_onminex f0_onminex f1_onminex f2_onminex f3_onminex a_sup_set_class p_onnminsb f3_onminex a_sup_set_class f0_onminex f2_onminex a_con0 a_crab a_cint a_wcel f0_onminex f2_onminex a_con0 a_wrex f3_onminex a_sup_set_class a_con0 a_wcel f1_onminex a_wn p_syli f0_onminex f2_onminex a_con0 a_wrex f1_onminex a_wn f3_onminex f0_onminex f2_onminex a_con0 a_crab a_cint p_ralrimiv f0_onminex f2_onminex i0_onminex f0_onminex f2_onminex a_con0 a_crab a_cint p_dfsbcq2 f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class f0_onminex f2_onminex a_con0 a_crab a_cint p_raleq i0_onminex a_sup_set_class f0_onminex f2_onminex a_con0 a_crab a_cint a_wceq f0_onminex f2_onminex i0_onminex a_wsb f0_onminex f2_onminex f0_onminex f2_onminex a_con0 a_crab a_cint a_wsbc f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class a_wral f1_onminex a_wn f3_onminex f0_onminex f2_onminex a_con0 a_crab a_cint a_wral p_anbi12d f0_onminex f2_onminex i0_onminex a_wsb f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class a_wral a_wa f0_onminex f2_onminex f0_onminex f2_onminex a_con0 a_crab a_cint a_wsbc f1_onminex a_wn f3_onminex f0_onminex f2_onminex a_con0 a_crab a_cint a_wral a_wa i0_onminex f0_onminex f2_onminex a_con0 a_crab a_cint a_con0 p_rspcev f0_onminex f2_onminex a_con0 a_wrex f0_onminex f2_onminex a_con0 a_crab a_cint a_con0 a_wcel f0_onminex f2_onminex f0_onminex f2_onminex a_con0 a_crab a_cint a_wsbc f1_onminex a_wn f3_onminex f0_onminex f2_onminex a_con0 a_crab a_cint a_wral f0_onminex f2_onminex i0_onminex a_wsb f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class a_wral a_wa i0_onminex a_con0 a_wrex p_syl12anc f0_onminex f1_onminex a_wn f3_onminex f2_onminex a_sup_set_class a_wral a_wa i0_onminex p_nfv f0_onminex f2_onminex i0_onminex p_nfs1v f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class a_wral f2_onminex p_nfv f0_onminex f2_onminex i0_onminex a_wsb f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class a_wral f2_onminex p_nfan f0_onminex f2_onminex i0_onminex p_sbequ12 f1_onminex a_wn f3_onminex f2_onminex a_sup_set_class i0_onminex a_sup_set_class p_raleq f2_onminex a_sup_set_class i0_onminex a_sup_set_class a_wceq f0_onminex f0_onminex f2_onminex i0_onminex a_wsb f1_onminex a_wn f3_onminex f2_onminex a_sup_set_class a_wral f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class a_wral p_anbi12d f0_onminex f1_onminex a_wn f3_onminex f2_onminex a_sup_set_class a_wral a_wa f0_onminex f2_onminex i0_onminex a_wsb f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class a_wral a_wa f2_onminex i0_onminex a_con0 p_cbvrex f0_onminex f2_onminex a_con0 a_wrex f0_onminex f2_onminex i0_onminex a_wsb f1_onminex a_wn f3_onminex i0_onminex a_sup_set_class a_wral a_wa i0_onminex a_con0 a_wrex f0_onminex f1_onminex a_wn f3_onminex f2_onminex a_sup_set_class a_wral a_wa f2_onminex a_con0 a_wrex p_sylibr $.
$}

$(The class of all ordinal numbers is its own successor.  (Contributed by
     NM, 12-Sep-2003.) $)

${
	$v  $.
	p_sucon $p |- suc On = On $= p_onprc a_con0 p_sucprc a_con0 a_cvv a_wcel a_wn a_con0 a_csuc a_con0 a_wceq a_ax-mp $.
$}

$(A successor exists iff its class argument exists.  (Contributed by NM,
     22-Jun-1998.) $)

${
	$v A  $.
	f0_sucexb $f class A $.
	p_sucexb $p |- ( A e. _V <-> suc A e. _V ) $= f0_sucexb f0_sucexb a_csn p_unexb f0_sucexb p_snex f0_sucexb a_csn a_cvv a_wcel f0_sucexb a_cvv a_wcel p_biantru f0_sucexb a_df-suc f0_sucexb a_csuc f0_sucexb f0_sucexb a_csn a_cun a_cvv p_eleq1i f0_sucexb a_cvv a_wcel f0_sucexb a_csn a_cvv a_wcel a_wa f0_sucexb f0_sucexb a_csn a_cun a_cvv a_wcel f0_sucexb a_cvv a_wcel f0_sucexb a_csuc a_cvv a_wcel p_3bitr4i $.
$}

$(The successor of a set is a set (generalization).  (Contributed by NM,
     5-Jun-1994.) $)

${
	$v A V  $.
	f0_sucexg $f class A $.
	f1_sucexg $f class V $.
	p_sucexg $p |- ( A e. V -> suc A e. _V ) $= f0_sucexg f1_sucexg p_elex f0_sucexg p_sucexb f0_sucexg f1_sucexg a_wcel f0_sucexg a_cvv a_wcel f0_sucexg a_csuc a_cvv a_wcel p_sylib $.
$}

$(The successor of a set is a set.  (Contributed by NM, 30-Aug-1993.) $)

${
	$v A  $.
	f0_sucex $f class A $.
	e0_sucex $e |- A e. _V $.
	p_sucex $p |- suc A e. _V $= e0_sucex f0_sucex a_cvv p_sucexg f0_sucex a_cvv a_wcel f0_sucex a_csuc a_cvv a_wcel a_ax-mp $.
$}

$(The minimum of a class of ordinal numbers is less than the minimum of
       that class with its minimum removed.  (Contributed by NM,
       20-Nov-2003.) $)

${
	$v A  $.
	$d x A  $.
	f0_onmindif2 $f class A $.
	i0_onmindif2 $f set x $.
	p_onmindif2 $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. |^| ( A \ { |^| A } ) ) $= i0_onmindif2 a_sup_set_class f0_onmindif2 f0_onmindif2 a_cint p_eldifsn f0_onmindif2 i0_onmindif2 a_sup_set_class p_onnmin f0_onmindif2 a_con0 a_wss i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel i0_onmindif2 a_sup_set_class f0_onmindif2 a_cint a_wcel a_wn f0_onmindif2 a_c0 a_wne p_adantlr f0_onmindif2 p_oninton f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa f0_onmindif2 a_cint a_con0 a_wcel i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel p_adantr f0_onmindif2 a_con0 i0_onmindif2 a_sup_set_class p_ssel2 f0_onmindif2 a_con0 a_wss i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel i0_onmindif2 a_sup_set_class a_con0 a_wcel f0_onmindif2 a_c0 a_wne p_adantlr f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class p_ontri1 f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class p_onsseleq f0_onmindif2 a_cint a_con0 a_wcel i0_onmindif2 a_sup_set_class a_con0 a_wcel a_wa f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wss i0_onmindif2 a_sup_set_class f0_onmindif2 a_cint a_wcel a_wn f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wceq a_wo p_bitr3d f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel a_wa f0_onmindif2 a_cint a_con0 a_wcel i0_onmindif2 a_sup_set_class a_con0 a_wcel i0_onmindif2 a_sup_set_class f0_onmindif2 a_cint a_wcel a_wn f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wceq a_wo a_wb p_syl2anc f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel a_wa i0_onmindif2 a_sup_set_class f0_onmindif2 a_cint a_wcel a_wn f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wceq a_wo p_mpbid f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel a_wa f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wceq p_ord f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class p_eqcom f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel a_wa f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel a_wn f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wceq i0_onmindif2 a_sup_set_class f0_onmindif2 a_cint a_wceq p_syl6ib f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel a_wa f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel i0_onmindif2 a_sup_set_class f0_onmindif2 a_cint p_necon1ad f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel i0_onmindif2 a_sup_set_class f0_onmindif2 a_cint a_wne f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel p_expimpd i0_onmindif2 a_sup_set_class f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif a_wcel i0_onmindif2 a_sup_set_class f0_onmindif2 a_wcel i0_onmindif2 a_sup_set_class f0_onmindif2 a_cint a_wne a_wa f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel p_syl5bi f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel i0_onmindif2 f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif p_ralrimiv f0_onmindif2 p_intex i0_onmindif2 f0_onmindif2 a_cint f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif a_cvv p_elintg f0_onmindif2 a_c0 a_wne f0_onmindif2 a_cint a_cvv a_wcel f0_onmindif2 a_cint f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif a_cint a_wcel f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel i0_onmindif2 f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif a_wral a_wb p_sylbi f0_onmindif2 a_c0 a_wne f0_onmindif2 a_cint f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif a_cint a_wcel f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel i0_onmindif2 f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif a_wral a_wb f0_onmindif2 a_con0 a_wss p_adantl f0_onmindif2 a_con0 a_wss f0_onmindif2 a_c0 a_wne a_wa f0_onmindif2 a_cint f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif a_cint a_wcel f0_onmindif2 a_cint i0_onmindif2 a_sup_set_class a_wcel i0_onmindif2 f0_onmindif2 f0_onmindif2 a_cint a_csn a_cdif a_wral p_mpbird $.
$}

$(The successor of an ordinal number is an ordinal number.  Proposition
       7.24 of [TakeutiZaring] p. 41.  (Contributed by NM, 6-Jun-1994.) $)

${
	$v A  $.
	$d x A  $.
	f0_suceloni $f class A $.
	i0_suceloni $f set x $.
	p_suceloni $p |- ( A e. On -> suc A e. On ) $= f0_suceloni i0_suceloni a_sup_set_class p_onelss i0_suceloni f0_suceloni p_elsn i0_suceloni a_sup_set_class f0_suceloni p_eqimss i0_suceloni a_sup_set_class f0_suceloni a_csn a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wceq i0_suceloni a_sup_set_class f0_suceloni a_wss p_sylbi i0_suceloni a_sup_set_class f0_suceloni a_csn a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wss a_wi f0_suceloni a_con0 a_wcel p_a1i f0_suceloni a_con0 a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wss i0_suceloni a_sup_set_class f0_suceloni a_csn a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wss p_orim12d f0_suceloni a_df-suc f0_suceloni a_csuc f0_suceloni f0_suceloni a_csn a_cun i0_suceloni a_sup_set_class p_eleq2i i0_suceloni a_sup_set_class f0_suceloni f0_suceloni a_csn p_elun i0_suceloni a_sup_set_class f0_suceloni a_csuc a_wcel i0_suceloni a_sup_set_class f0_suceloni f0_suceloni a_csn a_cun a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wcel i0_suceloni a_sup_set_class f0_suceloni a_csn a_wcel a_wo p_bitr2i i0_suceloni a_sup_set_class f0_suceloni a_wss p_oridm f0_suceloni a_con0 a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wcel i0_suceloni a_sup_set_class f0_suceloni a_csn a_wcel a_wo i0_suceloni a_sup_set_class f0_suceloni a_wss i0_suceloni a_sup_set_class f0_suceloni a_wss a_wo i0_suceloni a_sup_set_class f0_suceloni a_csuc a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wss p_3imtr3g f0_suceloni p_sssucid i0_suceloni a_sup_set_class f0_suceloni f0_suceloni a_csuc p_sstr2 f0_suceloni a_con0 a_wcel i0_suceloni a_sup_set_class f0_suceloni a_csuc a_wcel i0_suceloni a_sup_set_class f0_suceloni a_wss f0_suceloni f0_suceloni a_csuc a_wss i0_suceloni a_sup_set_class f0_suceloni a_csuc a_wss p_syl6mpi f0_suceloni a_con0 a_wcel i0_suceloni a_sup_set_class f0_suceloni a_csuc a_wss i0_suceloni f0_suceloni a_csuc p_ralrimiv i0_suceloni f0_suceloni a_csuc p_dftr3 f0_suceloni a_con0 a_wcel i0_suceloni a_sup_set_class f0_suceloni a_csuc a_wss i0_suceloni f0_suceloni a_csuc a_wral f0_suceloni a_csuc a_wtr p_sylibr f0_suceloni a_df-suc f0_suceloni p_onss f0_suceloni a_con0 p_snssi f0_suceloni a_con0 a_wcel f0_suceloni f0_suceloni a_csn a_con0 p_unssd f0_suceloni a_con0 a_wcel f0_suceloni a_csuc f0_suceloni f0_suceloni a_csn a_cun a_con0 p_syl5eqss p_ordon f0_suceloni a_csuc a_con0 p_trssord f0_suceloni a_csuc a_wtr f0_suceloni a_csuc a_con0 a_wss a_con0 a_word f0_suceloni a_csuc a_word p_3exp f0_suceloni a_csuc a_wtr f0_suceloni a_csuc a_con0 a_wss a_con0 a_word f0_suceloni a_csuc a_word p_mpii f0_suceloni a_con0 a_wcel f0_suceloni a_csuc a_wtr f0_suceloni a_csuc a_con0 a_wss f0_suceloni a_csuc a_word p_sylc f0_suceloni a_con0 p_sucexg f0_suceloni a_csuc a_cvv p_elong f0_suceloni a_con0 a_wcel f0_suceloni a_csuc a_cvv a_wcel f0_suceloni a_csuc a_con0 a_wcel f0_suceloni a_csuc a_word a_wb p_syl f0_suceloni a_con0 a_wcel f0_suceloni a_csuc a_con0 a_wcel f0_suceloni a_csuc a_word p_mpbird $.
$}

$(The successor of an ordinal class is ordinal.  (Contributed by NM,
     3-Apr-1995.) $)

${
	$v A  $.
	f0_ordsuc $f class A $.
	p_ordsuc $p |- ( Ord A <-> Ord suc A ) $= f0_ordsuc a_cvv p_elong f0_ordsuc p_suceloni f0_ordsuc a_csuc p_eloni f0_ordsuc a_con0 a_wcel f0_ordsuc a_csuc a_con0 a_wcel f0_ordsuc a_csuc a_word p_syl f0_ordsuc a_cvv a_wcel f0_ordsuc a_word f0_ordsuc a_con0 a_wcel f0_ordsuc a_csuc a_word p_syl6bir f0_ordsuc a_cvv p_sucidg f0_ordsuc a_csuc f0_ordsuc p_ordelord f0_ordsuc a_csuc a_word f0_ordsuc f0_ordsuc a_csuc a_wcel f0_ordsuc a_word p_ex f0_ordsuc a_cvv a_wcel f0_ordsuc f0_ordsuc a_csuc a_wcel f0_ordsuc a_csuc a_word f0_ordsuc a_word p_syl5com f0_ordsuc a_cvv a_wcel f0_ordsuc a_word f0_ordsuc a_csuc a_word p_impbid f0_ordsuc p_sucprc f0_ordsuc a_cvv a_wcel a_wn f0_ordsuc a_csuc f0_ordsuc p_eqcomd f0_ordsuc f0_ordsuc a_csuc p_ordeq f0_ordsuc a_cvv a_wcel a_wn f0_ordsuc f0_ordsuc a_csuc a_wceq f0_ordsuc a_word f0_ordsuc a_csuc a_word a_wb p_syl f0_ordsuc a_cvv a_wcel f0_ordsuc a_word f0_ordsuc a_csuc a_word a_wb p_pm2.61i $.
$}

$(The collection of ordinals in the power class of an ordinal is its
       successor.  (Contributed by NM, 30-Jan-2005.) $)

${
	$v A  $.
	$d x A  $.
	f0_ordpwsuc $f class A $.
	i0_ordpwsuc $f set x $.
	p_ordpwsuc $p |- ( Ord A -> ( ~P A i^i On ) = suc A ) $= i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_cpw a_con0 p_elin i0_ordpwsuc p_vex i0_ordpwsuc a_sup_set_class f0_ordpwsuc p_elpw i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_cpw a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_wss i0_ordpwsuc a_sup_set_class a_con0 a_wcel p_anbi2ci i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_cpw a_con0 a_cin a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_cpw a_wcel i0_ordpwsuc a_sup_set_class a_con0 a_wcel a_wa i0_ordpwsuc a_sup_set_class a_con0 a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_wss a_wa p_bitri i0_ordpwsuc a_sup_set_class f0_ordpwsuc p_ordsssuc i0_ordpwsuc a_sup_set_class a_con0 a_wcel f0_ordpwsuc a_word i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_wss i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel a_wb p_expcom f0_ordpwsuc a_word i0_ordpwsuc a_sup_set_class a_con0 a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_wss i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel p_pm5.32d i0_ordpwsuc a_sup_set_class a_con0 a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel p_simpr f0_ordpwsuc p_ordsuc f0_ordpwsuc a_csuc i0_ordpwsuc a_sup_set_class p_ordelon f0_ordpwsuc a_csuc a_word i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel i0_ordpwsuc a_sup_set_class a_con0 a_wcel p_ex f0_ordpwsuc a_word f0_ordpwsuc a_csuc a_word i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel i0_ordpwsuc a_sup_set_class a_con0 a_wcel a_wi p_sylbi f0_ordpwsuc a_word i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel i0_ordpwsuc a_sup_set_class a_con0 a_wcel p_ancrd f0_ordpwsuc a_word i0_ordpwsuc a_sup_set_class a_con0 a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel a_wa i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel p_impbid2 f0_ordpwsuc a_word i0_ordpwsuc a_sup_set_class a_con0 a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_wss a_wa i0_ordpwsuc a_sup_set_class a_con0 a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel a_wa i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel p_bitrd i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_cpw a_con0 a_cin a_wcel i0_ordpwsuc a_sup_set_class a_con0 a_wcel i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_wss a_wa f0_ordpwsuc a_word i0_ordpwsuc a_sup_set_class f0_ordpwsuc a_csuc a_wcel p_syl5bb f0_ordpwsuc a_word i0_ordpwsuc f0_ordpwsuc a_cpw a_con0 a_cin f0_ordpwsuc a_csuc p_eqrdv $.
$}

$(The collection of ordinal numbers in the power set of an ordinal number
       is its successor.  (Contributed by NM, 19-Oct-2004.) $)

${
	$v A  $.
	$d A  $.
	f0_onpwsuc $f class A $.
	p_onpwsuc $p |- ( A e. On -> ( ~P A i^i On ) = suc A ) $= f0_onpwsuc p_eloni f0_onpwsuc p_ordpwsuc f0_onpwsuc a_con0 a_wcel f0_onpwsuc a_word f0_onpwsuc a_cpw a_con0 a_cin f0_onpwsuc a_csuc a_wceq p_syl $.
$}

$(The successor of an ordinal number is an ordinal number.  (Contributed by
     NM, 9-Sep-2003.) $)

${
	$v A  $.
	f0_sucelon $f class A $.
	p_sucelon $p |- ( A e. On <-> suc A e. On ) $= f0_sucelon p_ordsuc f0_sucelon p_sucexb f0_sucelon a_word f0_sucelon a_csuc a_word f0_sucelon a_cvv a_wcel f0_sucelon a_csuc a_cvv a_wcel p_anbi12i f0_sucelon p_elon2 f0_sucelon a_csuc p_elon2 f0_sucelon a_word f0_sucelon a_cvv a_wcel a_wa f0_sucelon a_csuc a_word f0_sucelon a_csuc a_cvv a_wcel a_wa f0_sucelon a_con0 a_wcel f0_sucelon a_csuc a_con0 a_wcel p_3bitr4i $.
$}

$(The successor of an element of an ordinal class is a subset of it.
     (Contributed by NM, 21-Jun-1998.) $)

${
	$v A B  $.
	f0_ordsucss $f class A $.
	f1_ordsucss $f class B $.
	p_ordsucss $p |- ( Ord B -> ( A e. B -> suc A C_ B ) ) $= f1_ordsucss f0_ordsucss p_ordelord f0_ordsucss f1_ordsucss p_ordnbtwn f0_ordsucss f1_ordsucss a_wcel f1_ordsucss f0_ordsucss a_csuc a_wcel p_imnan f0_ordsucss a_word f0_ordsucss f1_ordsucss a_wcel f1_ordsucss f0_ordsucss a_csuc a_wcel a_wa a_wn f0_ordsucss f1_ordsucss a_wcel f1_ordsucss f0_ordsucss a_csuc a_wcel a_wn a_wi p_sylibr f0_ordsucss a_word f0_ordsucss f1_ordsucss a_wcel f1_ordsucss f0_ordsucss a_csuc a_wcel a_wn a_wi f1_ordsucss a_word p_adantr f0_ordsucss p_ordsuc f0_ordsucss a_csuc f1_ordsucss p_ordtri1 f0_ordsucss a_word f0_ordsucss a_csuc a_word f1_ordsucss a_word f0_ordsucss a_csuc f1_ordsucss a_wss f1_ordsucss f0_ordsucss a_csuc a_wcel a_wn a_wb p_sylanb f0_ordsucss a_word f1_ordsucss a_word a_wa f0_ordsucss f1_ordsucss a_wcel f1_ordsucss f0_ordsucss a_csuc a_wcel a_wn f0_ordsucss a_csuc f1_ordsucss a_wss p_sylibrd f1_ordsucss a_word f0_ordsucss f1_ordsucss a_wcel a_wa f0_ordsucss a_word f1_ordsucss a_word f0_ordsucss f1_ordsucss a_wcel f0_ordsucss a_csuc f1_ordsucss a_wss a_wi p_sylan f1_ordsucss a_word f0_ordsucss f1_ordsucss a_wcel f1_ordsucss a_word f0_ordsucss f1_ordsucss a_wcel f0_ordsucss a_csuc f1_ordsucss a_wss a_wi p_exp31 f0_ordsucss f1_ordsucss a_wcel f1_ordsucss a_word f0_ordsucss f1_ordsucss a_wcel f0_ordsucss a_csuc f1_ordsucss a_wss a_wi p_pm2.43b f1_ordsucss a_word f0_ordsucss f1_ordsucss a_wcel f0_ordsucss a_csuc f1_ordsucss a_wss p_pm2.43b $.
$}

$(An ordinal number is a proper subset of its successor.  (Contributed by
     Stefan O'Rear, 18-Nov-2014.) $)

${
	$v A  $.
	f0_onpsssuc $f class A $.
	p_onpsssuc $p |- ( A e. On -> A C. suc A ) $= f0_onpsssuc a_con0 p_sucidg f0_onpsssuc p_eloni f0_onpsssuc p_eloni f0_onpsssuc p_ordsuc f0_onpsssuc a_con0 a_wcel f0_onpsssuc a_word f0_onpsssuc a_csuc a_word p_sylib f0_onpsssuc f0_onpsssuc a_csuc p_ordelpss f0_onpsssuc a_con0 a_wcel f0_onpsssuc a_word f0_onpsssuc a_csuc a_word f0_onpsssuc f0_onpsssuc a_csuc a_wcel f0_onpsssuc f0_onpsssuc a_csuc a_wpss a_wb p_syl2anc f0_onpsssuc a_con0 a_wcel f0_onpsssuc f0_onpsssuc a_csuc a_wcel f0_onpsssuc f0_onpsssuc a_csuc a_wpss p_mpbid $.
$}

$(A set belongs to an ordinal iff its successor is a subset of the ordinal.
     Exercise 8 of [TakeutiZaring] p. 42 and its converse.  (Contributed by NM,
     29-Nov-2003.) $)

${
	$v A B C  $.
	f0_ordelsuc $f class A $.
	f1_ordelsuc $f class B $.
	f2_ordelsuc $f class C $.
	p_ordelsuc $p |- ( ( A e. C /\ Ord B ) -> ( A e. B <-> suc A C_ B ) ) $= f0_ordelsuc f1_ordelsuc p_ordsucss f1_ordelsuc a_word f0_ordelsuc f1_ordelsuc a_wcel f0_ordelsuc a_csuc f1_ordelsuc a_wss a_wi f0_ordelsuc f2_ordelsuc a_wcel p_adantl f0_ordelsuc f1_ordelsuc f2_ordelsuc p_sucssel f0_ordelsuc f2_ordelsuc a_wcel f0_ordelsuc a_csuc f1_ordelsuc a_wss f0_ordelsuc f1_ordelsuc a_wcel a_wi f1_ordelsuc a_word p_adantr f0_ordelsuc f2_ordelsuc a_wcel f1_ordelsuc a_word a_wa f0_ordelsuc f1_ordelsuc a_wcel f0_ordelsuc a_csuc f1_ordelsuc a_wss p_impbid $.
$}

$(The successor of an ordinal number is the smallest larger ordinal
       number.  (Contributed by NM, 28-Nov-2003.) $)

${
	$v x A  $.
	$d x A  $.
	f0_onsucmin $f set x $.
	f1_onsucmin $f class A $.
	p_onsucmin $p |- ( A e. On -> suc A = |^| { x e. On | A e. x } ) $= f0_onsucmin a_sup_set_class p_eloni f1_onsucmin f0_onsucmin a_sup_set_class a_con0 p_ordelsuc f0_onsucmin a_sup_set_class a_con0 a_wcel f1_onsucmin a_con0 a_wcel f0_onsucmin a_sup_set_class a_word f1_onsucmin f0_onsucmin a_sup_set_class a_wcel f1_onsucmin a_csuc f0_onsucmin a_sup_set_class a_wss a_wb p_sylan2 f1_onsucmin a_con0 a_wcel f1_onsucmin f0_onsucmin a_sup_set_class a_wcel f1_onsucmin a_csuc f0_onsucmin a_sup_set_class a_wss f0_onsucmin a_con0 p_rabbidva f1_onsucmin a_con0 a_wcel f1_onsucmin f0_onsucmin a_sup_set_class a_wcel f0_onsucmin a_con0 a_crab f1_onsucmin a_csuc f0_onsucmin a_sup_set_class a_wss f0_onsucmin a_con0 a_crab p_inteqd f1_onsucmin p_sucelon f0_onsucmin f1_onsucmin a_csuc a_con0 p_intmin f1_onsucmin a_con0 a_wcel f1_onsucmin a_csuc a_con0 a_wcel f1_onsucmin a_csuc f0_onsucmin a_sup_set_class a_wss f0_onsucmin a_con0 a_crab a_cint f1_onsucmin a_csuc a_wceq p_sylbi f1_onsucmin a_con0 a_wcel f1_onsucmin f0_onsucmin a_sup_set_class a_wcel f0_onsucmin a_con0 a_crab a_cint f1_onsucmin a_csuc f0_onsucmin a_sup_set_class a_wss f0_onsucmin a_con0 a_crab a_cint f1_onsucmin a_csuc p_eqtr2d $.
$}

$(Membership is inherited by successors.  Generalization of Exercise 9 of
     [TakeutiZaring] p. 42.  (Contributed by NM, 22-Jun-1998.)  (Proof
     shortened by Andrew Salmon, 12-Aug-2011.) $)

${
	$v A B  $.
	f0_ordsucelsuc $f class A $.
	f1_ordsucelsuc $f class B $.
	p_ordsucelsuc $p |- ( Ord B -> ( A e. B <-> suc A e. suc B ) ) $= f1_ordsucelsuc a_word f0_ordsucelsuc f1_ordsucelsuc a_wcel p_simpl f1_ordsucelsuc f0_ordsucelsuc p_ordelord f1_ordsucelsuc a_word f0_ordsucelsuc f1_ordsucelsuc a_wcel a_wa f1_ordsucelsuc a_word f0_ordsucelsuc a_word p_jca f1_ordsucelsuc a_word f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel p_simpl f1_ordsucelsuc p_ordsuc f1_ordsucelsuc a_csuc f0_ordsucelsuc a_csuc p_ordelord f0_ordsucelsuc p_ordsuc f1_ordsucelsuc a_csuc a_word f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel a_wa f0_ordsucelsuc a_csuc a_word f0_ordsucelsuc a_word p_sylibr f1_ordsucelsuc a_word f1_ordsucelsuc a_csuc a_word f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel f0_ordsucelsuc a_word p_sylanb f1_ordsucelsuc a_word f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel a_wa f1_ordsucelsuc a_word f0_ordsucelsuc a_word p_jca f0_ordsucelsuc p_ordsuc f0_ordsucelsuc a_csuc f1_ordsucelsuc p_ordsseleq f0_ordsucelsuc a_word f0_ordsucelsuc a_csuc a_word f1_ordsucelsuc a_word f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wss f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wceq a_wo a_wb p_sylanb f0_ordsucelsuc a_word f1_ordsucelsuc a_word f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wss f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wceq a_wo a_wb p_ancoms f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wss f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wceq a_wo a_wb f0_ordsucelsuc a_cvv a_wcel p_adantl f0_ordsucelsuc f1_ordsucelsuc p_ordsucss f1_ordsucelsuc a_word f0_ordsucelsuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wss a_wi f0_ordsucelsuc a_cvv a_wcel f0_ordsucelsuc a_word p_ad2antrl f0_ordsucelsuc f1_ordsucelsuc a_cvv p_sucssel f0_ordsucelsuc a_cvv a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wss f0_ordsucelsuc f1_ordsucelsuc a_wcel a_wi f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa p_adantr f0_ordsucelsuc a_cvv a_wcel f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa a_wa f0_ordsucelsuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wss p_impbid f0_ordsucelsuc p_sucexb f0_ordsucelsuc a_csuc f1_ordsucelsuc a_cvv p_elsucg f0_ordsucelsuc a_cvv a_wcel f0_ordsucelsuc a_csuc a_cvv a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wceq a_wo a_wb p_sylbi f0_ordsucelsuc a_cvv a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wceq a_wo a_wb f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa p_adantr f0_ordsucelsuc a_cvv a_wcel f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa a_wa f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wss f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_wceq a_wo f0_ordsucelsuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel p_3bitr4d f0_ordsucelsuc a_cvv a_wcel f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa f0_ordsucelsuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel a_wb p_ex f0_ordsucelsuc f1_ordsucelsuc p_elex f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc p_elex f0_ordsucelsuc p_sucexb f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel f0_ordsucelsuc a_csuc a_cvv a_wcel f0_ordsucelsuc a_cvv a_wcel p_sylibr f0_ordsucelsuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_cvv a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel p_pm5.21ni f0_ordsucelsuc a_cvv a_wcel a_wn f0_ordsucelsuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel a_wb f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa p_a1d f0_ordsucelsuc a_cvv a_wcel f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa f0_ordsucelsuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel a_wb a_wi p_pm2.61i f1_ordsucelsuc a_word f0_ordsucelsuc f1_ordsucelsuc a_wcel f0_ordsucelsuc a_csuc f1_ordsucelsuc a_csuc a_wcel f1_ordsucelsuc a_word f0_ordsucelsuc a_word a_wa p_pm5.21nd $.
$}

$(The subclass relationship between two ordinal classes is inherited by
     their successors.  (Contributed by NM, 4-Oct-2003.) $)

${
	$v A B  $.
	f0_ordsucsssuc $f class A $.
	f1_ordsucsssuc $f class B $.
	p_ordsucsssuc $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> suc A C_ suc B ) ) $= f1_ordsucsssuc f0_ordsucsssuc p_ordsucelsuc f0_ordsucsssuc a_word f1_ordsucsssuc f0_ordsucsssuc a_wcel f1_ordsucsssuc a_csuc f0_ordsucsssuc a_csuc a_wcel p_notbid f0_ordsucsssuc a_word f1_ordsucsssuc f0_ordsucsssuc a_wcel a_wn f1_ordsucsssuc a_csuc f0_ordsucsssuc a_csuc a_wcel a_wn a_wb f1_ordsucsssuc a_word p_adantr f0_ordsucsssuc f1_ordsucsssuc p_ordtri1 f0_ordsucsssuc p_ordsuc f1_ordsucsssuc p_ordsuc f0_ordsucsssuc a_csuc f1_ordsucsssuc a_csuc p_ordtri1 f0_ordsucsssuc a_word f0_ordsucsssuc a_csuc a_word f1_ordsucsssuc a_csuc a_word f0_ordsucsssuc a_csuc f1_ordsucsssuc a_csuc a_wss f1_ordsucsssuc a_csuc f0_ordsucsssuc a_csuc a_wcel a_wn a_wb f1_ordsucsssuc a_word p_syl2anb f0_ordsucsssuc a_word f1_ordsucsssuc a_word a_wa f1_ordsucsssuc f0_ordsucsssuc a_wcel a_wn f1_ordsucsssuc a_csuc f0_ordsucsssuc a_csuc a_wcel a_wn f0_ordsucsssuc f1_ordsucsssuc a_wss f0_ordsucsssuc a_csuc f1_ordsucsssuc a_csuc a_wss p_3bitr4d $.
$}

$(Given an element ` A ` of the union of an ordinal ` B ` , ` suc A ` is an
     element of ` B ` itself.  (Contributed by Scott Fenton, 28-Mar-2012.)
     (Proof shortened by Mario Carneiro, 29-May-2015.) $)

${
	$v A B  $.
	f0_ordsucuniel $f class A $.
	f1_ordsucuniel $f class B $.
	p_ordsucuniel $p |- ( Ord B -> ( A e. U. B <-> suc A e. B ) ) $= f1_ordsucuniel p_orduni f1_ordsucuniel a_cuni f0_ordsucuniel p_ordelord f1_ordsucuniel a_cuni a_word f0_ordsucuniel f1_ordsucuniel a_cuni a_wcel f0_ordsucuniel a_word p_ex f1_ordsucuniel a_word f1_ordsucuniel a_cuni a_word f0_ordsucuniel f1_ordsucuniel a_cuni a_wcel f0_ordsucuniel a_word a_wi p_syl f1_ordsucuniel f0_ordsucuniel a_csuc p_ordelord f0_ordsucuniel p_ordsuc f1_ordsucuniel a_word f0_ordsucuniel a_csuc f1_ordsucuniel a_wcel a_wa f0_ordsucuniel a_csuc a_word f0_ordsucuniel a_word p_sylibr f1_ordsucuniel a_word f0_ordsucuniel a_csuc f1_ordsucuniel a_wcel f0_ordsucuniel a_word p_ex f1_ordsucuniel p_ordsson f1_ordsucuniel f0_ordsucuniel p_ordunisssuc f1_ordsucuniel a_word f1_ordsucuniel a_con0 a_wss f0_ordsucuniel a_word f1_ordsucuniel a_cuni f0_ordsucuniel a_wss f1_ordsucuniel f0_ordsucuniel a_csuc a_wss a_wb p_sylan f1_ordsucuniel p_orduni f1_ordsucuniel a_cuni f0_ordsucuniel p_ordtri1 f1_ordsucuniel a_word f1_ordsucuniel a_cuni a_word f0_ordsucuniel a_word f1_ordsucuniel a_cuni f0_ordsucuniel a_wss f0_ordsucuniel f1_ordsucuniel a_cuni a_wcel a_wn a_wb p_sylan f0_ordsucuniel p_ordsuc f1_ordsucuniel f0_ordsucuniel a_csuc p_ordtri1 f0_ordsucuniel a_word f1_ordsucuniel a_word f0_ordsucuniel a_csuc a_word f1_ordsucuniel f0_ordsucuniel a_csuc a_wss f0_ordsucuniel a_csuc f1_ordsucuniel a_wcel a_wn a_wb p_sylan2b f1_ordsucuniel a_word f0_ordsucuniel a_word a_wa f1_ordsucuniel a_cuni f0_ordsucuniel a_wss f1_ordsucuniel f0_ordsucuniel a_csuc a_wss f0_ordsucuniel f1_ordsucuniel a_cuni a_wcel a_wn f0_ordsucuniel a_csuc f1_ordsucuniel a_wcel a_wn p_3bitr3d f1_ordsucuniel a_word f0_ordsucuniel a_word a_wa f0_ordsucuniel f1_ordsucuniel a_cuni a_wcel f0_ordsucuniel a_csuc f1_ordsucuniel a_wcel p_con4bid f1_ordsucuniel a_word f0_ordsucuniel a_word f0_ordsucuniel f1_ordsucuniel a_cuni a_wcel f0_ordsucuniel a_csuc f1_ordsucuniel a_wcel a_wb p_ex f1_ordsucuniel a_word f0_ordsucuniel a_word f0_ordsucuniel f1_ordsucuniel a_cuni a_wcel f0_ordsucuniel a_csuc f1_ordsucuniel a_wcel p_pm5.21ndd $.
$}

$(The successor of the maximum (i.e. union) of two ordinals is the maximum
       of their successors.  (Contributed by NM, 28-Nov-2003.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_ordsucun $f class A $.
	f1_ordsucun $f class B $.
	i0_ordsucun $f set x $.
	p_ordsucun $p |- ( ( Ord A /\ Ord B ) -> suc ( A u. B ) = ( suc A u. suc B ) ) $= f0_ordsucun f1_ordsucun p_ordun f0_ordsucun f1_ordsucun a_cun p_ordsuc f0_ordsucun f1_ordsucun a_cun a_csuc i0_ordsucun a_sup_set_class p_ordelon f0_ordsucun f1_ordsucun a_cun a_csuc a_word i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_csuc a_wcel i0_ordsucun a_sup_set_class a_con0 a_wcel p_ex f0_ordsucun f1_ordsucun a_cun a_word f0_ordsucun f1_ordsucun a_cun a_csuc a_word i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_csuc a_wcel i0_ordsucun a_sup_set_class a_con0 a_wcel a_wi p_sylbi f0_ordsucun a_word f1_ordsucun a_word a_wa f0_ordsucun f1_ordsucun a_cun a_word i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_csuc a_wcel i0_ordsucun a_sup_set_class a_con0 a_wcel a_wi p_syl f0_ordsucun p_ordsuc f1_ordsucun p_ordsuc f0_ordsucun a_csuc f1_ordsucun a_csuc p_ordun f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun i0_ordsucun a_sup_set_class p_ordelon f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun a_word i0_ordsucun a_sup_set_class f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun a_wcel i0_ordsucun a_sup_set_class a_con0 a_wcel p_ex f0_ordsucun a_csuc a_word f1_ordsucun a_csuc a_word a_wa f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun a_word i0_ordsucun a_sup_set_class f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun a_wcel i0_ordsucun a_sup_set_class a_con0 a_wcel a_wi p_syl f0_ordsucun a_word f0_ordsucun a_csuc a_word f1_ordsucun a_csuc a_word i0_ordsucun a_sup_set_class f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun a_wcel i0_ordsucun a_sup_set_class a_con0 a_wcel a_wi f1_ordsucun a_word p_syl2anb i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun p_ordssun f0_ordsucun a_word f1_ordsucun a_word a_wa i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_wss i0_ordsucun a_sup_set_class f0_ordsucun a_wss i0_ordsucun a_sup_set_class f1_ordsucun a_wss a_wo a_wb i0_ordsucun a_sup_set_class a_con0 a_wcel p_adantl f0_ordsucun f1_ordsucun p_ordun i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun p_ordsssuc f0_ordsucun a_word f1_ordsucun a_word a_wa i0_ordsucun a_sup_set_class a_con0 a_wcel f0_ordsucun f1_ordsucun a_cun a_word i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_wss i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_csuc a_wcel a_wb p_sylan2 i0_ordsucun a_sup_set_class f0_ordsucun p_ordsssuc i0_ordsucun a_sup_set_class a_con0 a_wcel f0_ordsucun a_word i0_ordsucun a_sup_set_class f0_ordsucun a_wss i0_ordsucun a_sup_set_class f0_ordsucun a_csuc a_wcel a_wb f1_ordsucun a_word p_adantrr i0_ordsucun a_sup_set_class f1_ordsucun p_ordsssuc i0_ordsucun a_sup_set_class a_con0 a_wcel f1_ordsucun a_word i0_ordsucun a_sup_set_class f1_ordsucun a_wss i0_ordsucun a_sup_set_class f1_ordsucun a_csuc a_wcel a_wb f0_ordsucun a_word p_adantrl i0_ordsucun a_sup_set_class a_con0 a_wcel f0_ordsucun a_word f1_ordsucun a_word a_wa a_wa i0_ordsucun a_sup_set_class f0_ordsucun a_wss i0_ordsucun a_sup_set_class f0_ordsucun a_csuc a_wcel i0_ordsucun a_sup_set_class f1_ordsucun a_wss i0_ordsucun a_sup_set_class f1_ordsucun a_csuc a_wcel p_orbi12d i0_ordsucun a_sup_set_class a_con0 a_wcel f0_ordsucun a_word f1_ordsucun a_word a_wa a_wa i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_wss i0_ordsucun a_sup_set_class f0_ordsucun a_wss i0_ordsucun a_sup_set_class f1_ordsucun a_wss a_wo i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_csuc a_wcel i0_ordsucun a_sup_set_class f0_ordsucun a_csuc a_wcel i0_ordsucun a_sup_set_class f1_ordsucun a_csuc a_wcel a_wo p_3bitr3d i0_ordsucun a_sup_set_class f0_ordsucun a_csuc f1_ordsucun a_csuc p_elun i0_ordsucun a_sup_set_class a_con0 a_wcel f0_ordsucun a_word f1_ordsucun a_word a_wa a_wa i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_csuc a_wcel i0_ordsucun a_sup_set_class f0_ordsucun a_csuc a_wcel i0_ordsucun a_sup_set_class f1_ordsucun a_csuc a_wcel a_wo i0_ordsucun a_sup_set_class f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun a_wcel p_syl6bbr i0_ordsucun a_sup_set_class a_con0 a_wcel f0_ordsucun a_word f1_ordsucun a_word a_wa i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_csuc a_wcel i0_ordsucun a_sup_set_class f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun a_wcel a_wb p_expcom f0_ordsucun a_word f1_ordsucun a_word a_wa i0_ordsucun a_sup_set_class a_con0 a_wcel i0_ordsucun a_sup_set_class f0_ordsucun f1_ordsucun a_cun a_csuc a_wcel i0_ordsucun a_sup_set_class f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun a_wcel p_pm5.21ndd f0_ordsucun a_word f1_ordsucun a_word a_wa i0_ordsucun f0_ordsucun f1_ordsucun a_cun a_csuc f0_ordsucun a_csuc f1_ordsucun a_csuc a_cun p_eqrdv $.
$}

$(The maximum of two ordinals is equal to one of them.  (Contributed by
     Mario Carneiro, 25-Jun-2015.) $)

${
	$v B C  $.
	f0_ordunpr $f class B $.
	f1_ordunpr $f class C $.
	p_ordunpr $p |- ( ( B e. On /\ C e. On ) -> ( B u. C ) e. { B , C } ) $= f0_ordunpr p_eloni f1_ordunpr p_eloni f0_ordunpr f1_ordunpr p_ordtri2or2 f0_ordunpr a_con0 a_wcel f0_ordunpr a_word f1_ordunpr a_word f0_ordunpr f1_ordunpr a_wss f1_ordunpr f0_ordunpr a_wss a_wo f1_ordunpr a_con0 a_wcel p_syl2an f0_ordunpr a_con0 a_wcel f1_ordunpr a_con0 a_wcel a_wa f0_ordunpr f1_ordunpr a_wss f1_ordunpr f0_ordunpr a_wss p_orcomd f1_ordunpr f0_ordunpr p_ssequn2 f0_ordunpr f1_ordunpr p_ssequn1 f1_ordunpr f0_ordunpr a_wss f0_ordunpr f1_ordunpr a_cun f0_ordunpr a_wceq f0_ordunpr f1_ordunpr a_wss f0_ordunpr f1_ordunpr a_cun f1_ordunpr a_wceq p_orbi12i f0_ordunpr a_con0 a_wcel f1_ordunpr a_con0 a_wcel a_wa f1_ordunpr f0_ordunpr a_wss f0_ordunpr f1_ordunpr a_wss a_wo f0_ordunpr f1_ordunpr a_cun f0_ordunpr a_wceq f0_ordunpr f1_ordunpr a_cun f1_ordunpr a_wceq a_wo p_sylib f0_ordunpr f1_ordunpr a_con0 a_con0 p_unexg f0_ordunpr f1_ordunpr a_cun f0_ordunpr f1_ordunpr a_cvv p_elprg f0_ordunpr a_con0 a_wcel f1_ordunpr a_con0 a_wcel a_wa f0_ordunpr f1_ordunpr a_cun a_cvv a_wcel f0_ordunpr f1_ordunpr a_cun f0_ordunpr f1_ordunpr a_cpr a_wcel f0_ordunpr f1_ordunpr a_cun f0_ordunpr a_wceq f0_ordunpr f1_ordunpr a_cun f1_ordunpr a_wceq a_wo a_wb p_syl f0_ordunpr a_con0 a_wcel f1_ordunpr a_con0 a_wcel a_wa f0_ordunpr f1_ordunpr a_cun f0_ordunpr f1_ordunpr a_cpr a_wcel f0_ordunpr f1_ordunpr a_cun f0_ordunpr a_wceq f0_ordunpr f1_ordunpr a_cun f1_ordunpr a_wceq a_wo p_mpbird $.
$}

$(The maximum of two ordinals belongs to a third if each of them do.
     (Contributed by NM, 18-Sep-2006.)  (Revised by Mario Carneiro,
     25-Jun-2015.) $)

${
	$v A B C  $.
	f0_ordunel $f class A $.
	f1_ordunel $f class B $.
	f2_ordunel $f class C $.
	p_ordunel $p |- ( ( Ord A /\ B e. A /\ C e. A ) -> ( B u. C ) e. A ) $= f1_ordunel f2_ordunel f0_ordunel p_prssi f1_ordunel f0_ordunel a_wcel f2_ordunel f0_ordunel a_wcel f1_ordunel f2_ordunel a_cpr f0_ordunel a_wss f0_ordunel a_word p_3adant1 f0_ordunel f1_ordunel p_ordelon f0_ordunel a_word f1_ordunel f0_ordunel a_wcel f1_ordunel a_con0 a_wcel f2_ordunel f0_ordunel a_wcel p_3adant3 f0_ordunel f2_ordunel p_ordelon f0_ordunel a_word f2_ordunel f0_ordunel a_wcel f2_ordunel a_con0 a_wcel f1_ordunel f0_ordunel a_wcel p_3adant2 f1_ordunel f2_ordunel p_ordunpr f0_ordunel a_word f1_ordunel f0_ordunel a_wcel f2_ordunel f0_ordunel a_wcel a_w3a f1_ordunel a_con0 a_wcel f2_ordunel a_con0 a_wcel f1_ordunel f2_ordunel a_cun f1_ordunel f2_ordunel a_cpr a_wcel p_syl2anc f0_ordunel a_word f1_ordunel f0_ordunel a_wcel f2_ordunel f0_ordunel a_wcel a_w3a f1_ordunel f2_ordunel a_cpr f0_ordunel f1_ordunel f2_ordunel a_cun p_sseldd $.
$}

$(A class of ordinal numbers is a subclass of the successor of its union.
     Similar to Proposition 7.26 of [TakeutiZaring] p. 41.  (Contributed by NM,
     19-Sep-2003.) $)

${
	$v A  $.
	f0_onsucuni $f class A $.
	p_onsucuni $p |- ( A C_ On -> A C_ suc U. A ) $= f0_onsucuni p_ssorduni f0_onsucuni a_cuni p_ssid f0_onsucuni f0_onsucuni a_cuni p_ordunisssuc f0_onsucuni a_con0 a_wss f0_onsucuni a_cuni a_word a_wa f0_onsucuni a_cuni f0_onsucuni a_cuni a_wss f0_onsucuni f0_onsucuni a_cuni a_csuc a_wss p_mpbii f0_onsucuni a_con0 a_wss f0_onsucuni a_cuni a_word f0_onsucuni f0_onsucuni a_cuni a_csuc a_wss p_mpdan $.
$}

$(An ordinal class is a subclass of the successor of its union.
     (Contributed by NM, 12-Sep-2003.) $)

${
	$v A  $.
	f0_ordsucuni $f class A $.
	p_ordsucuni $p |- ( Ord A -> A C_ suc U. A ) $= f0_ordsucuni p_ordsson f0_ordsucuni p_onsucuni f0_ordsucuni a_word f0_ordsucuni a_con0 a_wss f0_ordsucuni f0_ordsucuni a_cuni a_csuc a_wss p_syl $.
$}

$(An ordinal class is either its union or the successor of its union.  If we
     adopt the view that zero is a limit ordinal, this means every ordinal
     class is either a limit or a successor.  (Contributed by NM,
     13-Sep-2003.) $)

${
	$v A  $.
	f0_orduniorsuc $f class A $.
	p_orduniorsuc $p |- ( Ord A -> ( A = U. A \/ A = suc U. A ) ) $= f0_orduniorsuc p_orduniss f0_orduniorsuc p_orduni f0_orduniorsuc a_cuni f0_orduniorsuc p_ordelssne f0_orduniorsuc a_cuni a_word f0_orduniorsuc a_word f0_orduniorsuc a_cuni f0_orduniorsuc a_wcel f0_orduniorsuc a_cuni f0_orduniorsuc a_wss f0_orduniorsuc a_cuni f0_orduniorsuc a_wne a_wa a_wb p_mpancom f0_orduniorsuc a_word f0_orduniorsuc a_cuni f0_orduniorsuc a_wcel f0_orduniorsuc a_cuni f0_orduniorsuc a_wss f0_orduniorsuc a_cuni f0_orduniorsuc a_wne a_wa p_biimprd f0_orduniorsuc a_word f0_orduniorsuc a_cuni f0_orduniorsuc a_wss f0_orduniorsuc a_cuni f0_orduniorsuc a_wne f0_orduniorsuc a_cuni f0_orduniorsuc a_wcel p_mpand f0_orduniorsuc a_cuni f0_orduniorsuc p_ordsucss f0_orduniorsuc a_word f0_orduniorsuc a_cuni f0_orduniorsuc a_wne f0_orduniorsuc a_cuni f0_orduniorsuc a_wcel f0_orduniorsuc a_cuni a_csuc f0_orduniorsuc a_wss p_syld f0_orduniorsuc p_ordsucuni f0_orduniorsuc a_word f0_orduniorsuc a_cuni f0_orduniorsuc a_wne f0_orduniorsuc a_cuni a_csuc f0_orduniorsuc a_wss f0_orduniorsuc f0_orduniorsuc a_cuni a_csuc a_wss p_jctild f0_orduniorsuc f0_orduniorsuc a_cuni a_df-ne f0_orduniorsuc f0_orduniorsuc a_cuni p_necom f0_orduniorsuc f0_orduniorsuc a_cuni a_wceq a_wn f0_orduniorsuc f0_orduniorsuc a_cuni a_wne f0_orduniorsuc a_cuni f0_orduniorsuc a_wne p_bitr3i f0_orduniorsuc f0_orduniorsuc a_cuni a_csuc p_eqss f0_orduniorsuc a_word f0_orduniorsuc a_cuni f0_orduniorsuc a_wne f0_orduniorsuc f0_orduniorsuc a_cuni a_csuc a_wss f0_orduniorsuc a_cuni a_csuc f0_orduniorsuc a_wss a_wa f0_orduniorsuc f0_orduniorsuc a_cuni a_wceq a_wn f0_orduniorsuc f0_orduniorsuc a_cuni a_csuc a_wceq p_3imtr4g f0_orduniorsuc a_word f0_orduniorsuc f0_orduniorsuc a_cuni a_wceq f0_orduniorsuc f0_orduniorsuc a_cuni a_csuc a_wceq p_orrd $.
$}

$(The class of all ordinal numbers is its own union.  Exercise 11 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 12-Nov-2003.) $)

${
	$v  $.
	$d x y  $.
	i0_unon $f set x $.
	i1_unon $f set y $.
	p_unon $p |- U. On = On $= i1_unon i0_unon a_sup_set_class a_con0 p_eluni2 i1_unon a_sup_set_class i0_unon a_sup_set_class p_onelon i0_unon a_sup_set_class i1_unon a_sup_set_class a_wcel i0_unon a_sup_set_class a_con0 a_wcel i1_unon a_con0 p_rexlimiva i0_unon a_sup_set_class a_con0 a_cuni a_wcel i0_unon a_sup_set_class i1_unon a_sup_set_class a_wcel i1_unon a_con0 a_wrex i0_unon a_sup_set_class a_con0 a_wcel p_sylbi i0_unon p_vex i0_unon a_sup_set_class p_sucid i0_unon a_sup_set_class p_suceloni i0_unon a_sup_set_class i0_unon a_sup_set_class a_csuc a_con0 p_elunii i0_unon a_sup_set_class a_con0 a_wcel i0_unon a_sup_set_class i0_unon a_sup_set_class a_csuc a_wcel i0_unon a_sup_set_class a_csuc a_con0 a_wcel i0_unon a_sup_set_class a_con0 a_cuni a_wcel p_sylancr i0_unon a_sup_set_class a_con0 a_cuni a_wcel i0_unon a_sup_set_class a_con0 a_wcel p_impbii i0_unon a_con0 a_cuni a_con0 p_eqriv $.
$}

$(An ordinal class is equal to the union of its successor.  (Contributed
       by NM, 10-Dec-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)

${
	$v A  $.
	$d x A  $.
	f0_ordunisuc $f class A $.
	i0_ordunisuc $f set x $.
	p_ordunisuc $p |- ( Ord A -> U. suc A = A ) $= f0_ordunisuc p_ordeleqon i0_ordunisuc a_sup_set_class f0_ordunisuc p_suceq i0_ordunisuc a_sup_set_class f0_ordunisuc a_wceq i0_ordunisuc a_sup_set_class a_csuc f0_ordunisuc a_csuc p_unieqd i0_ordunisuc a_sup_set_class f0_ordunisuc a_wceq p_id i0_ordunisuc a_sup_set_class f0_ordunisuc a_wceq i0_ordunisuc a_sup_set_class a_csuc a_cuni f0_ordunisuc a_csuc a_cuni i0_ordunisuc a_sup_set_class f0_ordunisuc p_eqeq12d i0_ordunisuc a_sup_set_class p_eloni i0_ordunisuc a_sup_set_class p_ordtr i0_ordunisuc a_sup_set_class a_con0 a_wcel i0_ordunisuc a_sup_set_class a_word i0_ordunisuc a_sup_set_class a_wtr p_syl i0_ordunisuc p_vex i0_ordunisuc a_sup_set_class p_unisuc i0_ordunisuc a_sup_set_class a_con0 a_wcel i0_ordunisuc a_sup_set_class a_wtr i0_ordunisuc a_sup_set_class a_csuc a_cuni i0_ordunisuc a_sup_set_class a_wceq p_sylib i0_ordunisuc a_sup_set_class a_csuc a_cuni i0_ordunisuc a_sup_set_class a_wceq f0_ordunisuc a_csuc a_cuni f0_ordunisuc a_wceq i0_ordunisuc f0_ordunisuc a_con0 p_vtoclga p_sucon a_con0 a_csuc a_con0 p_unieqi p_unon a_con0 a_csuc a_cuni a_con0 a_cuni a_con0 p_eqtri f0_ordunisuc a_con0 p_suceq f0_ordunisuc a_con0 a_wceq f0_ordunisuc a_csuc a_con0 a_csuc p_unieqd f0_ordunisuc a_con0 a_wceq p_id f0_ordunisuc a_con0 a_wceq a_con0 a_csuc a_cuni a_con0 f0_ordunisuc a_csuc a_cuni f0_ordunisuc p_3eqtr4a f0_ordunisuc a_con0 a_wcel f0_ordunisuc a_csuc a_cuni f0_ordunisuc a_wceq f0_ordunisuc a_con0 a_wceq p_jaoi f0_ordunisuc a_word f0_ordunisuc a_con0 a_wcel f0_ordunisuc a_con0 a_wceq a_wo f0_ordunisuc a_csuc a_cuni f0_ordunisuc a_wceq p_sylbi $.
$}

$(The union of the ordinal subsets of an ordinal number is that number.
       (Contributed by NM, 30-Jan-2005.) $)

${
	$v x A  $.
	$d x A  $.
	f0_orduniss2 $f set x $.
	f1_orduniss2 $f class A $.
	p_orduniss2 $p |- ( Ord A -> U. { x e. On | x C_ A } = A ) $= f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_con0 a_df-rab f0_orduniss2 a_sup_set_class a_con0 a_wcel f0_orduniss2 a_cab f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_cab p_incom f0_orduniss2 a_sup_set_class a_con0 a_wcel f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 p_inab f0_orduniss2 f1_orduniss2 a_df-pw f1_orduniss2 a_cpw f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_cab p_eqcomi f0_orduniss2 a_con0 p_abid2 f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_cab f1_orduniss2 a_cpw f0_orduniss2 a_sup_set_class a_con0 a_wcel f0_orduniss2 a_cab a_con0 p_ineq12i f0_orduniss2 a_sup_set_class a_con0 a_wcel f0_orduniss2 a_cab f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_cab a_cin f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_cab f0_orduniss2 a_sup_set_class a_con0 a_wcel f0_orduniss2 a_cab a_cin f0_orduniss2 a_sup_set_class a_con0 a_wcel f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss a_wa f0_orduniss2 a_cab f1_orduniss2 a_cpw a_con0 a_cin p_3eqtr3i f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_con0 a_crab f0_orduniss2 a_sup_set_class a_con0 a_wcel f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss a_wa f0_orduniss2 a_cab f1_orduniss2 a_cpw a_con0 a_cin p_eqtri f1_orduniss2 p_ordpwsuc f1_orduniss2 a_word f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_con0 a_crab f1_orduniss2 a_cpw a_con0 a_cin f1_orduniss2 a_csuc p_syl5eq f1_orduniss2 a_word f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_con0 a_crab f1_orduniss2 a_csuc p_unieqd f1_orduniss2 p_ordunisuc f1_orduniss2 a_word f0_orduniss2 a_sup_set_class f1_orduniss2 a_wss f0_orduniss2 a_con0 a_crab a_cuni f1_orduniss2 a_csuc a_cuni f1_orduniss2 p_eqtrd $.
$}

$(A successor ordinal is the successor of its union.  (Contributed by NM,
     10-Dec-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)

${
	$v A B  $.
	f0_onsucuni2 $f class A $.
	f1_onsucuni2 $f class B $.
	p_onsucuni2 $p |- ( ( A e. On /\ A = suc B ) -> suc U. A = A ) $= f0_onsucuni2 f1_onsucuni2 a_csuc a_con0 p_eleq1 f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq f0_onsucuni2 a_con0 a_wcel f1_onsucuni2 a_csuc a_con0 a_wcel p_biimpac f1_onsucuni2 a_csuc p_eloni f1_onsucuni2 p_ordsuc f1_onsucuni2 p_ordunisuc f1_onsucuni2 a_csuc a_word f1_onsucuni2 a_word f1_onsucuni2 a_csuc a_cuni f1_onsucuni2 a_wceq p_sylbir f1_onsucuni2 a_csuc a_cuni f1_onsucuni2 p_suceq f1_onsucuni2 a_csuc a_word f1_onsucuni2 a_csuc a_cuni f1_onsucuni2 a_wceq f1_onsucuni2 a_csuc a_cuni a_csuc f1_onsucuni2 a_csuc a_wceq p_syl f1_onsucuni2 a_csuc p_ordunisuc f1_onsucuni2 a_csuc a_word f1_onsucuni2 a_csuc a_cuni a_csuc f1_onsucuni2 a_csuc f1_onsucuni2 a_csuc a_csuc a_cuni p_eqtr4d f0_onsucuni2 a_con0 a_wcel f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq a_wa f1_onsucuni2 a_csuc a_con0 a_wcel f1_onsucuni2 a_csuc a_word f1_onsucuni2 a_csuc a_cuni a_csuc f1_onsucuni2 a_csuc a_csuc a_cuni a_wceq p_3syl f0_onsucuni2 f1_onsucuni2 a_csuc p_unieq f0_onsucuni2 a_cuni f1_onsucuni2 a_csuc a_cuni p_suceq f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq f0_onsucuni2 a_cuni f1_onsucuni2 a_csuc a_cuni a_wceq f0_onsucuni2 a_cuni a_csuc f1_onsucuni2 a_csuc a_cuni a_csuc a_wceq p_syl f0_onsucuni2 f1_onsucuni2 a_csuc p_suceq f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq f0_onsucuni2 a_csuc f1_onsucuni2 a_csuc a_csuc p_unieqd f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq f0_onsucuni2 a_cuni a_csuc f1_onsucuni2 a_csuc a_cuni a_csuc f0_onsucuni2 a_csuc a_cuni f1_onsucuni2 a_csuc a_csuc a_cuni p_eqeq12d f0_onsucuni2 a_con0 a_wcel f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq a_wa f0_onsucuni2 a_cuni a_csuc f0_onsucuni2 a_csuc a_cuni a_wceq f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq f1_onsucuni2 a_csuc a_cuni a_csuc f1_onsucuni2 a_csuc a_csuc a_cuni a_wceq p_syl5ibr f0_onsucuni2 a_con0 a_wcel f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq f0_onsucuni2 a_cuni a_csuc f0_onsucuni2 a_csuc a_cuni a_wceq p_anabsi7 f0_onsucuni2 p_eloni f0_onsucuni2 p_ordunisuc f0_onsucuni2 a_con0 a_wcel f0_onsucuni2 a_word f0_onsucuni2 a_csuc a_cuni f0_onsucuni2 a_wceq p_syl f0_onsucuni2 a_con0 a_wcel f0_onsucuni2 a_csuc a_cuni f0_onsucuni2 a_wceq f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq p_adantr f0_onsucuni2 a_con0 a_wcel f0_onsucuni2 f1_onsucuni2 a_csuc a_wceq a_wa f0_onsucuni2 a_cuni a_csuc f0_onsucuni2 a_csuc a_cuni f0_onsucuni2 p_eqtrd $.
$}

$(The successor of an ordinal class contains the empty set.  (Contributed by
     NM, 4-Apr-1995.) $)

${
	$v A  $.
	f0_0elsuc $f class A $.
	p_0elsuc $p |- ( Ord A -> (/) e. suc A ) $= f0_0elsuc p_ordsuc f0_0elsuc p_nsuceq0 f0_0elsuc a_csuc p_ord0eln0 f0_0elsuc a_csuc a_word a_c0 f0_0elsuc a_csuc a_wcel f0_0elsuc a_csuc a_c0 a_wne p_mpbiri f0_0elsuc a_word f0_0elsuc a_csuc a_word a_c0 f0_0elsuc a_csuc a_wcel p_sylbi $.
$}

$(The class of ordinal numbers is a limit ordinal.  (Contributed by NM,
     24-Mar-1995.) $)

${
	$v  $.
	p_limon $p |- Lim On $= p_ordon p_onn0 p_unon a_con0 a_cuni a_con0 p_eqcomi a_con0 a_df-lim a_con0 a_wlim a_con0 a_word a_con0 a_c0 a_wne a_con0 a_con0 a_cuni a_wceq p_mpbir3an $.
$}

$(An ordinal number is a subset of ` On ` .  (Contributed by NM,
       11-Aug-1994.) $)

${
	$v A  $.
	f0_onssi $f class A $.
	e0_onssi $e |- A e. On $.
	p_onssi $p |- A C_ On $= e0_onssi f0_onssi p_onss f0_onssi a_con0 a_wcel f0_onssi a_con0 a_wss a_ax-mp $.
$}

$(The successor of an ordinal number is an ordinal number.  Corollary
       7N(c) of [Enderton] p. 193.  (Contributed by NM, 12-Jun-1994.) $)

${
	$v A  $.
	f0_onsuci $f class A $.
	e0_onsuci $e |- A e. On $.
	p_onsuci $p |- suc A e. On $= e0_onsuci f0_onsuci p_suceloni f0_onsuci a_con0 a_wcel f0_onsuci a_csuc a_con0 a_wcel a_ax-mp $.
$}

$(An ordinal number is either its own union (if zero or a limit ordinal)
       or the successor of its union.  (Contributed by NM, 13-Jun-1994.) $)

${
	$v A  $.
	f0_onuniorsuci $f class A $.
	e0_onuniorsuci $e |- A e. On $.
	p_onuniorsuci $p |- ( A = U. A \/ A = suc U. A ) $= e0_onuniorsuci f0_onuniorsuci p_onordi f0_onuniorsuci p_orduniorsuc f0_onuniorsuci a_word f0_onuniorsuci f0_onuniorsuci a_cuni a_wceq f0_onuniorsuci f0_onuniorsuci a_cuni a_csuc a_wceq a_wo a_ax-mp $.
$}

$(A limit ordinal is not a successor ordinal.  (Contributed by NM,
         18-Feb-2004.) $)

${
	$v x A  $.
	$d x A  $.
	f0_onuninsuci $f set x $.
	f1_onuninsuci $f class A $.
	e0_onuninsuci $e |- A e. On $.
	p_onuninsuci $p |- ( A = U. A <-> -. E. x e. On A = suc x ) $= e0_onuninsuci f1_onuninsuci p_onirri f1_onuninsuci f1_onuninsuci a_cuni a_wceq p_id f0_onuninsuci a_sup_set_class a_df-suc f0_onuninsuci a_sup_set_class a_csuc f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_csn a_cun f1_onuninsuci p_eqeq2i f1_onuninsuci f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_csn a_cun p_unieq f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_csn a_cun a_wceq f1_onuninsuci a_cuni f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_csn a_cun a_cuni a_wceq p_sylbi f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_csn p_uniun f0_onuninsuci p_vex f0_onuninsuci a_sup_set_class p_unisn f0_onuninsuci a_sup_set_class a_csn a_cuni f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_cuni p_uneq2i f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_csn a_cun a_cuni f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class a_csn a_cuni a_cun f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class a_cun p_eqtri f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci a_cuni f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_csn a_cun a_cuni f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class a_cun p_syl6eq p_tron e0_onuninsuci f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_con0 p_eleq1 f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci a_con0 a_wcel f0_onuninsuci a_sup_set_class a_csuc a_con0 a_wcel p_mpbii a_con0 f0_onuninsuci a_sup_set_class p_trsuc f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq a_con0 a_wtr f0_onuninsuci a_sup_set_class a_csuc a_con0 a_wcel f0_onuninsuci a_sup_set_class a_con0 a_wcel p_sylancr f0_onuninsuci a_sup_set_class p_eloni f0_onuninsuci a_sup_set_class p_ordtr f0_onuninsuci a_sup_set_class a_con0 a_wcel f0_onuninsuci a_sup_set_class a_word f0_onuninsuci a_sup_set_class a_wtr p_syl f0_onuninsuci a_sup_set_class a_df-tr f0_onuninsuci a_sup_set_class a_con0 a_wcel f0_onuninsuci a_sup_set_class a_wtr f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class a_wss p_sylib f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f0_onuninsuci a_sup_set_class a_con0 a_wcel f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class a_wss p_syl f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class p_ssequn1 f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class a_wss f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class a_cun f0_onuninsuci a_sup_set_class a_wceq p_sylib f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci a_cuni f0_onuninsuci a_sup_set_class a_cuni f0_onuninsuci a_sup_set_class a_cun f0_onuninsuci a_sup_set_class p_eqtrd f1_onuninsuci f1_onuninsuci a_cuni a_wceq f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci f1_onuninsuci a_cuni f0_onuninsuci a_sup_set_class p_sylan9eqr f0_onuninsuci p_vex f0_onuninsuci a_sup_set_class p_sucid f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc f0_onuninsuci a_sup_set_class p_eleq2 f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f0_onuninsuci a_sup_set_class f1_onuninsuci a_wcel f0_onuninsuci a_sup_set_class f0_onuninsuci a_sup_set_class a_csuc a_wcel p_mpbiri f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f0_onuninsuci a_sup_set_class f1_onuninsuci a_wcel f1_onuninsuci f1_onuninsuci a_cuni a_wceq p_adantr f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci f1_onuninsuci a_cuni a_wceq a_wa f1_onuninsuci f0_onuninsuci a_sup_set_class f1_onuninsuci p_eqeltrd f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci f1_onuninsuci a_cuni a_wceq a_wa f1_onuninsuci f1_onuninsuci a_wcel p_mto f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci f1_onuninsuci a_cuni a_wceq p_imnani f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci f1_onuninsuci a_cuni a_wceq a_wn f0_onuninsuci a_con0 p_rexlimivw e0_onuninsuci f1_onuninsuci p_onuni f1_onuninsuci a_con0 a_wcel f1_onuninsuci a_cuni a_con0 a_wcel a_ax-mp e0_onuninsuci f1_onuninsuci p_onuniorsuci f1_onuninsuci f1_onuninsuci a_cuni a_wceq f1_onuninsuci f1_onuninsuci a_cuni a_csuc a_wceq p_ori f0_onuninsuci a_sup_set_class f1_onuninsuci a_cuni p_suceq f0_onuninsuci a_sup_set_class f1_onuninsuci a_cuni a_wceq f0_onuninsuci a_sup_set_class a_csuc f1_onuninsuci a_cuni a_csuc f1_onuninsuci p_eqeq2d f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f1_onuninsuci f1_onuninsuci a_cuni a_csuc a_wceq f0_onuninsuci f1_onuninsuci a_cuni a_con0 p_rspcev f1_onuninsuci f1_onuninsuci a_cuni a_wceq a_wn f1_onuninsuci a_cuni a_con0 a_wcel f1_onuninsuci f1_onuninsuci a_cuni a_csuc a_wceq f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f0_onuninsuci a_con0 a_wrex p_sylancr f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f0_onuninsuci a_con0 a_wrex f1_onuninsuci f1_onuninsuci a_cuni a_wceq a_wn p_impbii f1_onuninsuci f0_onuninsuci a_sup_set_class a_csuc a_wceq f0_onuninsuci a_con0 a_wrex f1_onuninsuci f1_onuninsuci a_cuni a_wceq p_con2bii $.
$}

$(A set belongs to an ordinal number iff its successor is a subset of
         the ordinal number.  Exercise 8 of [TakeutiZaring] p. 42 and its
         converse.  (Contributed by NM, 16-Sep-1995.) $)

${
	$v A B  $.
	f0_onsucssi $f class A $.
	f1_onsucssi $f class B $.
	e0_onsucssi $e |- A e. On $.
	e1_onsucssi $e |- B e. On $.
	p_onsucssi $p |- ( A e. B <-> suc A C_ B ) $= e0_onsucssi e1_onsucssi f1_onsucssi p_onordi f0_onsucssi f1_onsucssi a_con0 p_ordelsuc f0_onsucssi a_con0 a_wcel f1_onsucssi a_word f0_onsucssi f1_onsucssi a_wcel f0_onsucssi a_csuc f1_onsucssi a_wss a_wb p_mp2an $.
$}

$(A successor is not a limit ordinal.  (Contributed by NM, 25-Mar-1995.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)

${
	$v A V  $.
	f0_nlimsucg $f class A $.
	f1_nlimsucg $f class V $.
	p_nlimsucg $p |- ( A e. V -> -. Lim suc A ) $= f0_nlimsucg a_csuc p_limord f0_nlimsucg p_ordsuc f0_nlimsucg a_csuc a_wlim f0_nlimsucg a_csuc a_word f0_nlimsucg a_word p_sylibr f0_nlimsucg a_csuc p_limuni f0_nlimsucg p_ordunisuc f0_nlimsucg a_word f0_nlimsucg a_csuc a_cuni f0_nlimsucg f0_nlimsucg a_csuc p_eqeq2d f0_nlimsucg p_ordirr f0_nlimsucg a_csuc f0_nlimsucg f0_nlimsucg p_eleq2 f0_nlimsucg a_csuc f0_nlimsucg a_wceq f0_nlimsucg f0_nlimsucg a_csuc a_wcel f0_nlimsucg f0_nlimsucg a_wcel p_notbid f0_nlimsucg a_word f0_nlimsucg f0_nlimsucg a_csuc a_wcel a_wn f0_nlimsucg a_csuc f0_nlimsucg a_wceq f0_nlimsucg f0_nlimsucg a_wcel a_wn p_syl5ibrcom f0_nlimsucg f1_nlimsucg p_sucidg f0_nlimsucg f1_nlimsucg a_wcel f0_nlimsucg f0_nlimsucg a_csuc a_wcel p_con3i f0_nlimsucg a_word f0_nlimsucg a_csuc f0_nlimsucg a_wceq f0_nlimsucg f0_nlimsucg a_csuc a_wcel a_wn f0_nlimsucg f1_nlimsucg a_wcel a_wn p_syl6 f0_nlimsucg a_word f0_nlimsucg a_csuc f0_nlimsucg a_csuc a_cuni a_wceq f0_nlimsucg a_csuc f0_nlimsucg a_wceq f0_nlimsucg f1_nlimsucg a_wcel a_wn p_sylbid f0_nlimsucg a_csuc a_wlim f0_nlimsucg a_word f0_nlimsucg a_csuc f0_nlimsucg a_csuc a_cuni a_wceq f0_nlimsucg f1_nlimsucg a_wcel a_wn p_sylc f0_nlimsucg a_csuc a_wlim f0_nlimsucg f1_nlimsucg a_wcel p_con2i $.
$}

$(An ordinal equal to its union is not a successor.  (Contributed by NM,
       18-Feb-2004.) $)

${
	$v x A  $.
	$d x A  $.
	f0_orduninsuc $f set x $.
	f1_orduninsuc $f class A $.
	p_orduninsuc $p |- ( Ord A -> ( A = U. A <-> -. E. x e. On A = suc x ) ) $= f1_orduninsuc p_ordeleqon f1_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif a_wceq p_id f1_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif p_unieq f1_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif a_wceq f1_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif f1_orduninsuc a_cuni f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif a_cuni p_eqeq12d f1_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif f0_orduninsuc a_sup_set_class a_csuc p_eqeq1 f1_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 p_rexbidv f1_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex p_notbid f1_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif a_wceq f1_orduninsuc f1_orduninsuc a_cuni a_wceq f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif a_cuni a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn p_bibi12d p_0elon f1_orduninsuc a_c0 a_con0 p_elimel f0_orduninsuc f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif p_onuninsuci f1_orduninsuc a_con0 a_wcel f1_orduninsuc f1_orduninsuc a_cuni a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn a_wb f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif a_cuni a_wceq f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_c0 a_cif f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn a_wb f1_orduninsuc a_c0 p_dedth p_unon a_con0 a_cuni a_con0 p_eqcomi p_onprc f0_orduninsuc p_vex f0_orduninsuc a_sup_set_class p_sucex a_con0 f0_orduninsuc a_sup_set_class a_csuc a_cvv p_eleq1 a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq a_con0 a_cvv a_wcel f0_orduninsuc a_sup_set_class a_csuc a_cvv a_wcel p_mpbiri a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq a_con0 a_cvv a_wcel p_mto a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq a_wn f0_orduninsuc a_sup_set_class a_con0 a_wcel p_a1i a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 p_nrex a_con0 a_con0 a_cuni a_wceq a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn p_2th f1_orduninsuc a_con0 a_wceq p_id f1_orduninsuc a_con0 p_unieq f1_orduninsuc a_con0 a_wceq f1_orduninsuc a_con0 f1_orduninsuc a_cuni a_con0 a_cuni p_eqeq12d f1_orduninsuc a_con0 f0_orduninsuc a_sup_set_class a_csuc p_eqeq1 f1_orduninsuc a_con0 a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 p_rexbidv f1_orduninsuc a_con0 a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex p_notbid f1_orduninsuc a_con0 a_wceq f1_orduninsuc f1_orduninsuc a_cuni a_wceq a_con0 a_con0 a_cuni a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn p_bibi12d f1_orduninsuc a_con0 a_wceq f1_orduninsuc f1_orduninsuc a_cuni a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn a_wb a_con0 a_con0 a_cuni a_wceq a_con0 f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn a_wb p_mpbiri f1_orduninsuc a_con0 a_wcel f1_orduninsuc f1_orduninsuc a_cuni a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn a_wb f1_orduninsuc a_con0 a_wceq p_jaoi f1_orduninsuc a_word f1_orduninsuc a_con0 a_wcel f1_orduninsuc a_con0 a_wceq a_wo f1_orduninsuc f1_orduninsuc a_cuni a_wceq f1_orduninsuc f0_orduninsuc a_sup_set_class a_csuc a_wceq f0_orduninsuc a_con0 a_wrex a_wn a_wb p_sylbi $.
$}

$(An ordinal equal to its union contains the successor of each of its
       members.  (Contributed by NM, 1-Feb-2005.) $)

${
	$v x A  $.
	$d x A  $.
	f0_ordunisuc2 $f set x $.
	f1_ordunisuc2 $f class A $.
	p_ordunisuc2 $p |- ( Ord A -> ( A = U. A <-> A. x e. A suc x e. A ) ) $= f0_ordunisuc2 f1_ordunisuc2 p_orduninsuc f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq f0_ordunisuc2 a_con0 p_ralnex f0_ordunisuc2 a_sup_set_class p_suceloni f0_ordunisuc2 a_sup_set_class a_csuc p_eloni f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc a_con0 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc a_word p_syl f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc p_ordtri3 f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_csuc a_word f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wo a_wn a_wb p_sylan2 f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wo p_con2bid f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 p_onnbtwn f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel p_imnan f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel a_wa a_wn f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel a_wn a_wi p_sylibr f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel p_con2d f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel p_pm2.21 f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel a_wn f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_syl6 f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi a_wi f1_ordunisuc2 a_word p_adantl f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel a_ax-1 f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi a_wi f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa p_a1i f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel p_jaod f0_ordunisuc2 a_sup_set_class p_eloni f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 p_ordtri2or f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class a_word f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_wss a_wo p_sylan f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_wss a_wo p_ancoms f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_wss p_orcomd f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_wss f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel a_wo f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_adantr f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class p_ordsssuc2 f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_wss f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel p_biimpd f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_wss f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel a_wi f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_adantr f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_simpr f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_wss f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel p_orim12d f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_wss f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel a_wo f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wo p_mpd f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wo p_ex f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wo f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_impbid f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel a_wa f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wo f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq a_wn f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_bitr3d f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq a_wn f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_pm5.74da f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel p_impexp f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel p_simpr f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class p_ordelon f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_con0 a_wcel p_ex f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_con0 a_wcel p_ancrd f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel a_wa f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel p_impbid2 f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel a_wa f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel p_imbi1d f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi a_wi f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel a_wa f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_syl5bbr f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq a_wn a_wi f0_ordunisuc2 a_sup_set_class a_con0 a_wcel f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi a_wi f0_ordunisuc2 a_sup_set_class f1_ordunisuc2 a_wcel f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel a_wi p_bitrd f1_ordunisuc2 a_word f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq a_wn f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel f0_ordunisuc2 a_con0 f1_ordunisuc2 p_ralbidv2 f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq f0_ordunisuc2 a_con0 a_wrex a_wn f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq a_wn f0_ordunisuc2 a_con0 a_wral f1_ordunisuc2 a_word f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel f0_ordunisuc2 f1_ordunisuc2 a_wral p_syl5bbr f1_ordunisuc2 a_word f1_ordunisuc2 f1_ordunisuc2 a_cuni a_wceq f1_ordunisuc2 f0_ordunisuc2 a_sup_set_class a_csuc a_wceq f0_ordunisuc2 a_con0 a_wrex a_wn f0_ordunisuc2 a_sup_set_class a_csuc f1_ordunisuc2 a_wcel f0_ordunisuc2 f1_ordunisuc2 a_wral p_bitrd $.
$}

$(An ordinal is zero, a successor ordinal, or a limit ordinal.
       (Contributed by NM, 1-Oct-2003.) $)

${
	$v x A  $.
	$d x A  $.
	f0_ordzsl $f set x $.
	f1_ordzsl $f class A $.
	p_ordzsl $p |- ( Ord A <-> ( A = (/) \/ E. x e. On A = suc x \/ Lim A ) ) $= f0_ordzsl f1_ordzsl p_orduninsuc f1_ordzsl a_word f1_ordzsl f1_ordzsl a_cuni a_wceq f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex a_wn p_biimprd f1_ordzsl p_unizlim f1_ordzsl a_word f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex a_wn f1_ordzsl f1_ordzsl a_cuni a_wceq f1_ordzsl a_c0 a_wceq f1_ordzsl a_wlim a_wo p_sylibd f1_ordzsl a_word f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_c0 a_wceq f1_ordzsl a_wlim a_wo p_orrd f1_ordzsl a_c0 a_wceq f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_wlim p_3orass f1_ordzsl a_c0 a_wceq f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_wlim p_or12 f1_ordzsl a_c0 a_wceq f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_wlim a_w3o f1_ordzsl a_c0 a_wceq f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_wlim a_wo a_wo f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_c0 a_wceq f1_ordzsl a_wlim a_wo a_wo p_bitri f1_ordzsl a_word f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_c0 a_wceq f1_ordzsl a_wlim a_wo a_wo f1_ordzsl a_c0 a_wceq f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_wlim a_w3o p_sylibr p_ord0 f1_ordzsl a_c0 p_ordeq f1_ordzsl a_c0 a_wceq f1_ordzsl a_word a_c0 a_word p_mpbiri f0_ordzsl a_sup_set_class p_suceloni f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_con0 p_eleq1 f0_ordzsl a_sup_set_class a_con0 a_wcel f1_ordzsl a_con0 a_wcel f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_sup_set_class a_csuc a_con0 a_wcel p_syl5ibr f1_ordzsl p_eloni f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_sup_set_class a_con0 a_wcel f1_ordzsl a_con0 a_wcel f1_ordzsl a_word p_syl6com f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f1_ordzsl a_word f0_ordzsl a_con0 p_rexlimiv f1_ordzsl p_limord f1_ordzsl a_c0 a_wceq f1_ordzsl a_word f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_wlim p_3jaoi f1_ordzsl a_word f1_ordzsl a_c0 a_wceq f1_ordzsl f0_ordzsl a_sup_set_class a_csuc a_wceq f0_ordzsl a_con0 a_wrex f1_ordzsl a_wlim a_w3o p_impbii $.
$}

$(An ordinal number is zero, a successor ordinal, or a limit ordinal
       number.  (Contributed by NM, 1-Oct-2003.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)

${
	$v x A  $.
	$d x A  $.
	f0_onzsl $f set x $.
	f1_onzsl $f class A $.
	p_onzsl $p |- ( A e. On <-> ( A = (/) \/ E. x e. On A = suc x \/ ( A e. _V /\ Lim A ) ) ) $= f1_onzsl a_con0 p_elex f1_onzsl p_eloni f0_onzsl f1_onzsl p_ordzsl f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa p_3mix1 f1_onzsl a_c0 a_wceq f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa a_w3o f1_onzsl a_cvv a_wcel p_adantl f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_c0 a_wceq f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa p_3mix2 f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa a_w3o f1_onzsl a_cvv a_wcel p_adantl f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex p_3mix3 f1_onzsl a_cvv a_wcel f1_onzsl a_c0 a_wceq f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa a_w3o f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_wlim p_3jaodan f1_onzsl a_word f1_onzsl a_cvv a_wcel f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_wlim a_w3o f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa a_w3o p_sylan2b f1_onzsl a_con0 a_wcel f1_onzsl a_cvv a_wcel f1_onzsl a_word f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa a_w3o p_syl2anc p_0elon f1_onzsl a_c0 a_con0 p_eleq1 f1_onzsl a_c0 a_wceq f1_onzsl a_con0 a_wcel a_c0 a_con0 a_wcel p_mpbiri f0_onzsl a_sup_set_class p_suceloni f1_onzsl f0_onzsl a_sup_set_class a_csuc a_con0 p_eleq1 f0_onzsl a_sup_set_class a_con0 a_wcel f1_onzsl a_con0 a_wcel f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_sup_set_class a_csuc a_con0 a_wcel p_syl5ibrcom f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f1_onzsl a_con0 a_wcel f0_onzsl a_con0 p_rexlimiv f1_onzsl a_cvv p_limelon f1_onzsl a_c0 a_wceq f1_onzsl a_con0 a_wcel f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa p_3jaoi f1_onzsl a_con0 a_wcel f1_onzsl a_c0 a_wceq f1_onzsl f0_onzsl a_sup_set_class a_csuc a_wceq f0_onzsl a_con0 a_wrex f1_onzsl a_cvv a_wcel f1_onzsl a_wlim a_wa a_w3o p_impbii $.
$}

$(An alternate definition of a limit ordinal, which is any ordinal that is
       neither zero nor a successor.  (Contributed by NM, 1-Nov-2004.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)

${
	$v x A  $.
	$d x A  $.
	f0_dflim3 $f set x $.
	f1_dflim3 $f class A $.
	p_dflim3 $p |- ( Lim A <-> ( Ord A /\ -. ( A = (/) \/ E. x e. On A = suc x ) ) ) $= f1_dflim3 a_df-lim f1_dflim3 a_word f1_dflim3 a_c0 a_wne f1_dflim3 f1_dflim3 a_cuni a_wceq p_3anass f1_dflim3 a_c0 a_df-ne f1_dflim3 a_c0 a_wne f1_dflim3 a_c0 a_wceq a_wn a_wb f1_dflim3 a_word p_a1i f0_dflim3 f1_dflim3 p_orduninsuc f1_dflim3 a_word f1_dflim3 a_c0 a_wne f1_dflim3 a_c0 a_wceq a_wn f1_dflim3 f1_dflim3 a_cuni a_wceq f1_dflim3 f0_dflim3 a_sup_set_class a_csuc a_wceq f0_dflim3 a_con0 a_wrex a_wn p_anbi12d f1_dflim3 a_c0 a_wceq f1_dflim3 f0_dflim3 a_sup_set_class a_csuc a_wceq f0_dflim3 a_con0 a_wrex p_ioran f1_dflim3 a_word f1_dflim3 a_c0 a_wne f1_dflim3 f1_dflim3 a_cuni a_wceq a_wa f1_dflim3 a_c0 a_wceq a_wn f1_dflim3 f0_dflim3 a_sup_set_class a_csuc a_wceq f0_dflim3 a_con0 a_wrex a_wn a_wa f1_dflim3 a_c0 a_wceq f1_dflim3 f0_dflim3 a_sup_set_class a_csuc a_wceq f0_dflim3 a_con0 a_wrex a_wo a_wn p_syl6bbr f1_dflim3 a_word f1_dflim3 a_c0 a_wne f1_dflim3 f1_dflim3 a_cuni a_wceq a_wa f1_dflim3 a_c0 a_wceq f1_dflim3 f0_dflim3 a_sup_set_class a_csuc a_wceq f0_dflim3 a_con0 a_wrex a_wo a_wn p_pm5.32i f1_dflim3 a_wlim f1_dflim3 a_word f1_dflim3 a_c0 a_wne f1_dflim3 f1_dflim3 a_cuni a_wceq a_w3a f1_dflim3 a_word f1_dflim3 a_c0 a_wne f1_dflim3 f1_dflim3 a_cuni a_wceq a_wa a_wa f1_dflim3 a_word f1_dflim3 a_c0 a_wceq f1_dflim3 f0_dflim3 a_sup_set_class a_csuc a_wceq f0_dflim3 a_con0 a_wrex a_wo a_wn a_wa p_3bitri $.
$}

$(An alternate definition of a limit ordinal.  (Contributed by NM,
       1-Feb-2005.) $)

${
	$v x A  $.
	$d x A  $.
	f0_dflim4 $f set x $.
	f1_dflim4 $f class A $.
	p_dflim4 $p |- ( Lim A <-> ( Ord A /\ (/) e. A /\ A. x e. A suc x e. A ) ) $= f1_dflim4 p_dflim2 f0_dflim4 f1_dflim4 p_ordunisuc2 f1_dflim4 a_word f1_dflim4 f1_dflim4 a_cuni a_wceq f0_dflim4 a_sup_set_class a_csuc f1_dflim4 a_wcel f0_dflim4 f1_dflim4 a_wral a_c0 f1_dflim4 a_wcel p_anbi2d f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f1_dflim4 f1_dflim4 a_cuni a_wceq a_wa a_c0 f1_dflim4 a_wcel f0_dflim4 a_sup_set_class a_csuc f1_dflim4 a_wcel f0_dflim4 f1_dflim4 a_wral a_wa p_pm5.32i f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f1_dflim4 f1_dflim4 a_cuni a_wceq p_3anass f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f0_dflim4 a_sup_set_class a_csuc f1_dflim4 a_wcel f0_dflim4 f1_dflim4 a_wral p_3anass f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f1_dflim4 f1_dflim4 a_cuni a_wceq a_wa a_wa f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f0_dflim4 a_sup_set_class a_csuc f1_dflim4 a_wcel f0_dflim4 f1_dflim4 a_wral a_wa a_wa f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f1_dflim4 f1_dflim4 a_cuni a_wceq a_w3a f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f0_dflim4 a_sup_set_class a_csuc f1_dflim4 a_wcel f0_dflim4 f1_dflim4 a_wral a_w3a p_3bitr4i f1_dflim4 a_wlim f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f1_dflim4 f1_dflim4 a_cuni a_wceq a_w3a f1_dflim4 a_word a_c0 f1_dflim4 a_wcel f0_dflim4 a_sup_set_class a_csuc f1_dflim4 a_wcel f0_dflim4 f1_dflim4 a_wral a_w3a p_bitri $.
$}

$(The successor of a member of a limit ordinal is also a member.
       (Contributed by NM, 3-Sep-2003.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_limsuc $f class A $.
	f1_limsuc $f class B $.
	i0_limsuc $f set x $.
	p_limsuc $p |- ( Lim A -> ( B e. A <-> suc B e. A ) ) $= i0_limsuc f0_limsuc p_dflim4 i0_limsuc a_sup_set_class f1_limsuc p_suceq i0_limsuc a_sup_set_class f1_limsuc a_wceq i0_limsuc a_sup_set_class a_csuc f1_limsuc a_csuc f0_limsuc p_eleq1d i0_limsuc a_sup_set_class a_csuc f0_limsuc a_wcel f1_limsuc a_csuc f0_limsuc a_wcel i0_limsuc f1_limsuc f0_limsuc p_rspccv i0_limsuc a_sup_set_class a_csuc f0_limsuc a_wcel i0_limsuc f0_limsuc a_wral f0_limsuc a_word f1_limsuc f0_limsuc a_wcel f1_limsuc a_csuc f0_limsuc a_wcel a_wi a_c0 f0_limsuc a_wcel p_3ad2ant3 f0_limsuc a_wlim f0_limsuc a_word a_c0 f0_limsuc a_wcel i0_limsuc a_sup_set_class a_csuc f0_limsuc a_wcel i0_limsuc f0_limsuc a_wral a_w3a f1_limsuc f0_limsuc a_wcel f1_limsuc a_csuc f0_limsuc a_wcel a_wi p_sylbi f0_limsuc p_limord f0_limsuc p_ordtr f0_limsuc f1_limsuc p_trsuc f0_limsuc a_wtr f1_limsuc a_csuc f0_limsuc a_wcel f1_limsuc f0_limsuc a_wcel p_ex f0_limsuc a_wlim f0_limsuc a_word f0_limsuc a_wtr f1_limsuc a_csuc f0_limsuc a_wcel f1_limsuc f0_limsuc a_wcel a_wi p_3syl f0_limsuc a_wlim f1_limsuc f0_limsuc a_wcel f1_limsuc a_csuc f0_limsuc a_wcel p_impbid $.
$}

$(A class includes a limit ordinal iff the successor of the class includes
       it.  (Contributed by NM, 30-Oct-2003.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_limsssuc $f class A $.
	f1_limsssuc $f class B $.
	i0_limsssuc $f set x $.
	p_limsssuc $p |- ( Lim A -> ( A C_ B <-> A C_ suc B ) ) $= f1_limsssuc p_sssucid f0_limsssuc f1_limsssuc f1_limsssuc a_csuc p_sstr2 f0_limsssuc f1_limsssuc a_wss f1_limsssuc f1_limsssuc a_csuc a_wss f0_limsssuc f1_limsssuc a_csuc a_wss p_mpi i0_limsssuc a_sup_set_class f1_limsssuc f0_limsssuc p_eleq1 i0_limsssuc a_sup_set_class f1_limsssuc a_wceq i0_limsssuc a_sup_set_class f0_limsssuc a_wcel f1_limsssuc f0_limsssuc a_wcel p_biimpcd f0_limsssuc f1_limsssuc p_limsuc f0_limsssuc a_wlim f1_limsssuc f0_limsssuc a_wcel f1_limsssuc a_csuc f0_limsssuc a_wcel p_biimpa f0_limsssuc p_limord f0_limsssuc a_wlim f0_limsssuc a_word f1_limsssuc f0_limsssuc a_wcel p_adantr f0_limsssuc p_limord f0_limsssuc f1_limsssuc p_ordelord f0_limsssuc a_wlim f0_limsssuc a_word f1_limsssuc f0_limsssuc a_wcel f1_limsssuc a_word p_sylan f1_limsssuc p_ordsuc f0_limsssuc a_wlim f1_limsssuc f0_limsssuc a_wcel a_wa f1_limsssuc a_word f1_limsssuc a_csuc a_word p_sylib f0_limsssuc f1_limsssuc a_csuc p_ordtri1 f0_limsssuc a_wlim f1_limsssuc f0_limsssuc a_wcel a_wa f0_limsssuc a_word f1_limsssuc a_csuc a_word f0_limsssuc f1_limsssuc a_csuc a_wss f1_limsssuc a_csuc f0_limsssuc a_wcel a_wn a_wb p_syl2anc f0_limsssuc a_wlim f1_limsssuc f0_limsssuc a_wcel a_wa f0_limsssuc f1_limsssuc a_csuc a_wss f1_limsssuc a_csuc f0_limsssuc a_wcel p_con2bid f0_limsssuc a_wlim f1_limsssuc f0_limsssuc a_wcel a_wa f1_limsssuc a_csuc f0_limsssuc a_wcel f0_limsssuc f1_limsssuc a_csuc a_wss a_wn p_mpbid f0_limsssuc a_wlim f1_limsssuc f0_limsssuc a_wcel f0_limsssuc f1_limsssuc a_csuc a_wss a_wn p_ex i0_limsssuc a_sup_set_class f0_limsssuc a_wcel i0_limsssuc a_sup_set_class f1_limsssuc a_wceq f1_limsssuc f0_limsssuc a_wcel f0_limsssuc a_wlim f0_limsssuc f1_limsssuc a_csuc a_wss a_wn p_sylan9r f0_limsssuc a_wlim i0_limsssuc a_sup_set_class f0_limsssuc a_wcel a_wa i0_limsssuc a_sup_set_class f1_limsssuc a_wceq f0_limsssuc f1_limsssuc a_csuc a_wss p_con2d f0_limsssuc a_wlim i0_limsssuc a_sup_set_class f0_limsssuc a_wcel f0_limsssuc f1_limsssuc a_csuc a_wss i0_limsssuc a_sup_set_class f1_limsssuc a_wceq a_wn a_wi p_ex f0_limsssuc a_wlim i0_limsssuc a_sup_set_class f0_limsssuc a_wcel f0_limsssuc f1_limsssuc a_csuc a_wss i0_limsssuc a_sup_set_class f1_limsssuc a_wceq a_wn p_com23 f0_limsssuc a_wlim f0_limsssuc f1_limsssuc a_csuc a_wss i0_limsssuc a_sup_set_class f0_limsssuc a_wcel i0_limsssuc a_sup_set_class f1_limsssuc a_wceq a_wn p_imp31 f0_limsssuc f1_limsssuc a_csuc i0_limsssuc a_sup_set_class p_ssel2 i0_limsssuc p_vex i0_limsssuc a_sup_set_class f1_limsssuc p_elsuc f0_limsssuc f1_limsssuc a_csuc a_wss i0_limsssuc a_sup_set_class f0_limsssuc a_wcel a_wa i0_limsssuc a_sup_set_class f1_limsssuc a_csuc a_wcel i0_limsssuc a_sup_set_class f1_limsssuc a_wcel i0_limsssuc a_sup_set_class f1_limsssuc a_wceq a_wo p_sylib f0_limsssuc f1_limsssuc a_csuc a_wss i0_limsssuc a_sup_set_class f0_limsssuc a_wcel a_wa i0_limsssuc a_sup_set_class f1_limsssuc a_wcel i0_limsssuc a_sup_set_class f1_limsssuc a_wceq p_ord f0_limsssuc f1_limsssuc a_csuc a_wss i0_limsssuc a_sup_set_class f0_limsssuc a_wcel a_wa i0_limsssuc a_sup_set_class f1_limsssuc a_wcel i0_limsssuc a_sup_set_class f1_limsssuc a_wceq p_con1d f0_limsssuc f1_limsssuc a_csuc a_wss i0_limsssuc a_sup_set_class f0_limsssuc a_wcel i0_limsssuc a_sup_set_class f1_limsssuc a_wceq a_wn i0_limsssuc a_sup_set_class f1_limsssuc a_wcel a_wi f0_limsssuc a_wlim p_adantll f0_limsssuc a_wlim f0_limsssuc f1_limsssuc a_csuc a_wss a_wa i0_limsssuc a_sup_set_class f0_limsssuc a_wcel a_wa i0_limsssuc a_sup_set_class f1_limsssuc a_wceq a_wn i0_limsssuc a_sup_set_class f1_limsssuc a_wcel p_mpd f0_limsssuc a_wlim f0_limsssuc f1_limsssuc a_csuc a_wss a_wa i0_limsssuc a_sup_set_class f0_limsssuc a_wcel i0_limsssuc a_sup_set_class f1_limsssuc a_wcel p_ex f0_limsssuc a_wlim f0_limsssuc f1_limsssuc a_csuc a_wss a_wa i0_limsssuc f0_limsssuc f1_limsssuc p_ssrdv f0_limsssuc a_wlim f0_limsssuc f1_limsssuc a_csuc a_wss f0_limsssuc f1_limsssuc a_wss p_ex f0_limsssuc a_wlim f0_limsssuc f1_limsssuc a_wss f0_limsssuc f1_limsssuc a_csuc a_wss p_impbid2 $.
$}

$(Two ways to express the class of non-limit ordinal numbers.  Part of
       Definition 7.27 of [TakeutiZaring] p. 42, who use the symbol K_I for
       this class.  (Contributed by NM, 1-Nov-2004.) $)

${
	$v x y  $.
	$d x y  $.
	f0_nlimon $f set x $.
	f1_nlimon $f set y $.
	p_nlimon $p |- { x e. On | ( x = (/) \/ E. y e. On x = suc y ) } = { x e. On | -. Lim x } $= f0_nlimon a_sup_set_class p_eloni f1_nlimon f0_nlimon a_sup_set_class p_dflim3 f0_nlimon a_sup_set_class a_wlim f0_nlimon a_sup_set_class a_word f0_nlimon a_sup_set_class a_c0 a_wceq f0_nlimon a_sup_set_class f1_nlimon a_sup_set_class a_csuc a_wceq f1_nlimon a_con0 a_wrex a_wo a_wn p_baib f0_nlimon a_sup_set_class a_word f0_nlimon a_sup_set_class a_wlim f0_nlimon a_sup_set_class a_c0 a_wceq f0_nlimon a_sup_set_class f1_nlimon a_sup_set_class a_csuc a_wceq f1_nlimon a_con0 a_wrex a_wo p_con2bid f0_nlimon a_sup_set_class a_con0 a_wcel f0_nlimon a_sup_set_class a_word f0_nlimon a_sup_set_class a_c0 a_wceq f0_nlimon a_sup_set_class f1_nlimon a_sup_set_class a_csuc a_wceq f1_nlimon a_con0 a_wrex a_wo f0_nlimon a_sup_set_class a_wlim a_wn a_wb p_syl f0_nlimon a_sup_set_class a_c0 a_wceq f0_nlimon a_sup_set_class f1_nlimon a_sup_set_class a_csuc a_wceq f1_nlimon a_con0 a_wrex a_wo f0_nlimon a_sup_set_class a_wlim a_wn f0_nlimon a_con0 p_rabbiia $.
$}

$(The union of a nonempty class of limit ordinals is a limit ordinal.
       (Contributed by NM, 1-Feb-2005.) $)

${
	$v x A  $.
	$d x y z A  $.
	f0_limuni3 $f set x $.
	f1_limuni3 $f class A $.
	i0_limuni3 $f set y $.
	i1_limuni3 $f set z $.
	p_limuni3 $p |- ( ( A =/= (/) /\ A. x e. A Lim x ) -> Lim U. A ) $= f0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class p_limeq f0_limuni3 a_sup_set_class a_wlim i1_limuni3 a_sup_set_class a_wlim f0_limuni3 i1_limuni3 a_sup_set_class f1_limuni3 p_rspcv i1_limuni3 p_vex i1_limuni3 a_sup_set_class a_cvv p_limelon i1_limuni3 a_sup_set_class a_cvv a_wcel i1_limuni3 a_sup_set_class a_wlim i1_limuni3 a_sup_set_class a_con0 a_wcel p_mpan i1_limuni3 a_sup_set_class f1_limuni3 a_wcel f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral i1_limuni3 a_sup_set_class a_wlim i1_limuni3 a_sup_set_class a_con0 a_wcel p_syl6com f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral i1_limuni3 f1_limuni3 a_con0 p_ssrdv f1_limuni3 p_ssorduni f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral f1_limuni3 a_con0 a_wss f1_limuni3 a_cuni a_word p_syl f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral f1_limuni3 a_cuni a_word f1_limuni3 a_c0 a_wne p_adantl i1_limuni3 f1_limuni3 p_n0 f0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class p_limeq f0_limuni3 a_sup_set_class a_wlim i1_limuni3 a_sup_set_class a_wlim f0_limuni3 i1_limuni3 a_sup_set_class f1_limuni3 p_rspcv i1_limuni3 a_sup_set_class p_0ellim a_c0 i1_limuni3 a_sup_set_class f1_limuni3 p_elunii a_c0 i1_limuni3 a_sup_set_class a_wcel i1_limuni3 a_sup_set_class f1_limuni3 a_wcel a_c0 f1_limuni3 a_cuni a_wcel p_expcom i1_limuni3 a_sup_set_class a_wlim a_c0 i1_limuni3 a_sup_set_class a_wcel i1_limuni3 a_sup_set_class f1_limuni3 a_wcel a_c0 f1_limuni3 a_cuni a_wcel p_syl5 i1_limuni3 a_sup_set_class f1_limuni3 a_wcel f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral i1_limuni3 a_sup_set_class a_wlim a_c0 f1_limuni3 a_cuni a_wcel p_syld i1_limuni3 a_sup_set_class f1_limuni3 a_wcel f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral a_c0 f1_limuni3 a_cuni a_wcel a_wi i1_limuni3 p_exlimiv f1_limuni3 a_c0 a_wne i1_limuni3 a_sup_set_class f1_limuni3 a_wcel i1_limuni3 a_wex f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral a_c0 f1_limuni3 a_cuni a_wcel a_wi p_sylbi f1_limuni3 a_c0 a_wne f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral a_c0 f1_limuni3 a_cuni a_wcel p_imp i1_limuni3 i0_limuni3 a_sup_set_class f1_limuni3 p_eluni2 f0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class p_limeq f0_limuni3 a_sup_set_class a_wlim i1_limuni3 a_sup_set_class a_wlim f0_limuni3 i1_limuni3 a_sup_set_class f1_limuni3 p_rspccv i1_limuni3 a_sup_set_class i0_limuni3 a_sup_set_class p_limsuc i1_limuni3 a_sup_set_class a_wlim i0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class a_wcel i0_limuni3 a_sup_set_class a_csuc i1_limuni3 a_sup_set_class a_wcel i1_limuni3 a_sup_set_class f1_limuni3 a_wcel p_anbi1d i0_limuni3 a_sup_set_class a_csuc i1_limuni3 a_sup_set_class f1_limuni3 p_elunii i1_limuni3 a_sup_set_class a_wlim i0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class a_wcel i1_limuni3 a_sup_set_class f1_limuni3 a_wcel a_wa i0_limuni3 a_sup_set_class a_csuc i1_limuni3 a_sup_set_class a_wcel i1_limuni3 a_sup_set_class f1_limuni3 a_wcel a_wa i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel p_syl6bi i1_limuni3 a_sup_set_class a_wlim i0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class a_wcel i1_limuni3 a_sup_set_class f1_limuni3 a_wcel i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel p_exp3a i1_limuni3 a_sup_set_class a_wlim i0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class a_wcel i1_limuni3 a_sup_set_class f1_limuni3 a_wcel i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel p_com3r f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral i1_limuni3 a_sup_set_class f1_limuni3 a_wcel i1_limuni3 a_sup_set_class a_wlim i0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class a_wcel i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel a_wi p_sylcom f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral i0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class a_wcel i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel i1_limuni3 f1_limuni3 p_rexlimdv i0_limuni3 a_sup_set_class f1_limuni3 a_cuni a_wcel i0_limuni3 a_sup_set_class i1_limuni3 a_sup_set_class a_wcel i1_limuni3 f1_limuni3 a_wrex f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel p_syl5bi f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel i0_limuni3 f1_limuni3 a_cuni p_ralrimiv f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel i0_limuni3 f1_limuni3 a_cuni a_wral f1_limuni3 a_c0 a_wne p_adantl i0_limuni3 f1_limuni3 a_cuni p_dflim4 f1_limuni3 a_c0 a_wne f0_limuni3 a_sup_set_class a_wlim f0_limuni3 f1_limuni3 a_wral a_wa f1_limuni3 a_cuni a_word a_c0 f1_limuni3 a_cuni a_wcel i0_limuni3 a_sup_set_class a_csuc f1_limuni3 a_cuni a_wcel i0_limuni3 f1_limuni3 a_cuni a_wral f1_limuni3 a_cuni a_wlim p_syl3anbrc $.
$}


