$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Ordered-pair_class_abstractions_(class_builders).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Transitive classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare a new symbol. $)

$c Tr $.

$(Transitive predicate (read:  "the following class is
              transitive") $)

$(Extend wff notation to include transitive classes.  Notation from
     [TakeutiZaring] p. 35. $)

${
	$v A  $.
	f0_wtr $f class A $.
	a_wtr $a wff Tr A $.
$}

$(Define the transitive class predicate.  Not to be confused with a
     transitive relation (see ~ cotr ).  Definition of [Enderton] p. 71
     extended to arbitrary classes.  For alternate definitions, see ~ dftr2
     (which is suggestive of the word "transitive"), ~ dftr3 , ~ dftr4 ,
     ~ dftr5 , and (when ` A ` is a set) ~ unisuc .  The term "complete" is
     used instead of "transitive" in Definition 3 of [Suppes] p. 130.
     (Contributed by NM, 29-Aug-1993.) $)

${
	$v A  $.
	f0_df-tr $f class A $.
	a_df-tr $a |- ( Tr A <-> U. A C_ A ) $.
$}

$(An alternate way of defining a transitive class.  Exercise 7 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 24-Apr-1994.) $)

${
	$v x y A  $.
	$d x y A  $.
	f0_dftr2 $f set x $.
	f1_dftr2 $f set y $.
	f2_dftr2 $f class A $.
	p_dftr2 $p |- ( Tr A <-> A. x A. y ( ( x e. y /\ y e. A ) -> x e. A ) ) $= f0_dftr2 f2_dftr2 a_cuni f2_dftr2 p_dfss2 f2_dftr2 a_df-tr f0_dftr2 a_sup_set_class f1_dftr2 a_sup_set_class a_wcel f1_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wa f0_dftr2 a_sup_set_class f2_dftr2 a_wcel f1_dftr2 p_19.23v f1_dftr2 f0_dftr2 a_sup_set_class f2_dftr2 p_eluni f0_dftr2 a_sup_set_class f2_dftr2 a_cuni a_wcel f0_dftr2 a_sup_set_class f1_dftr2 a_sup_set_class a_wcel f1_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wa f1_dftr2 a_wex f0_dftr2 a_sup_set_class f2_dftr2 a_wcel p_imbi1i f0_dftr2 a_sup_set_class f1_dftr2 a_sup_set_class a_wcel f1_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wa f0_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wi f1_dftr2 a_wal f0_dftr2 a_sup_set_class f1_dftr2 a_sup_set_class a_wcel f1_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wa f1_dftr2 a_wex f0_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wi f0_dftr2 a_sup_set_class f2_dftr2 a_cuni a_wcel f0_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wi p_bitr4i f0_dftr2 a_sup_set_class f1_dftr2 a_sup_set_class a_wcel f1_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wa f0_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wi f1_dftr2 a_wal f0_dftr2 a_sup_set_class f2_dftr2 a_cuni a_wcel f0_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wi f0_dftr2 p_albii f2_dftr2 a_cuni f2_dftr2 a_wss f0_dftr2 a_sup_set_class f2_dftr2 a_cuni a_wcel f0_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wi f0_dftr2 a_wal f2_dftr2 a_wtr f0_dftr2 a_sup_set_class f1_dftr2 a_sup_set_class a_wcel f1_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wa f0_dftr2 a_sup_set_class f2_dftr2 a_wcel a_wi f1_dftr2 a_wal f0_dftr2 a_wal p_3bitr4i $.
$}

$(An alternate way of defining a transitive class.  (Contributed by NM,
       20-Mar-2004.) $)

${
	$v x y A  $.
	$d x y A  $.
	f0_dftr5 $f set x $.
	f1_dftr5 $f set y $.
	f2_dftr5 $f class A $.
	p_dftr5 $p |- ( Tr A <-> A. x e. A A. y e. x y e. A ) $= f1_dftr5 f0_dftr5 f2_dftr5 p_dftr2 f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 f0_dftr5 p_alcom f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel p_impexp f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi a_wi f1_dftr5 p_albii f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 f0_dftr5 a_sup_set_class a_df-ral f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 a_wal f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi a_wi f1_dftr5 a_wal f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 f0_dftr5 a_sup_set_class a_wral p_bitr4i f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 f0_dftr5 a_sup_set_class p_r19.21v f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 a_wal f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 f0_dftr5 a_sup_set_class a_wral f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 f0_dftr5 a_sup_set_class a_wral a_wi p_bitri f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 a_wal f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 f0_dftr5 a_sup_set_class a_wral a_wi f0_dftr5 p_albii f1_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 f0_dftr5 a_sup_set_class a_wral f0_dftr5 f2_dftr5 a_df-ral f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 a_wal f0_dftr5 a_wal f0_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 f0_dftr5 a_sup_set_class a_wral a_wi f0_dftr5 a_wal f1_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 f0_dftr5 a_sup_set_class a_wral f0_dftr5 f2_dftr5 a_wral p_bitr4i f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f0_dftr5 a_wal f1_dftr5 a_wal f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f1_dftr5 a_wal f0_dftr5 a_wal f1_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 f0_dftr5 a_sup_set_class a_wral f0_dftr5 f2_dftr5 a_wral p_bitri f2_dftr5 a_wtr f1_dftr5 a_sup_set_class f0_dftr5 a_sup_set_class a_wcel f0_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wa f1_dftr5 a_sup_set_class f2_dftr5 a_wcel a_wi f0_dftr5 a_wal f1_dftr5 a_wal f1_dftr5 a_sup_set_class f2_dftr5 a_wcel f1_dftr5 f0_dftr5 a_sup_set_class a_wral f0_dftr5 f2_dftr5 a_wral p_bitri $.
$}

$(An alternate way of defining a transitive class.  Definition 7.1 of
       [TakeutiZaring] p. 35.  (Contributed by NM, 29-Aug-1993.) $)

${
	$v x A  $.
	$d x y A  $.
	f0_dftr3 $f set x $.
	f1_dftr3 $f class A $.
	i0_dftr3 $f set y $.
	p_dftr3 $p |- ( Tr A <-> A. x e. A x C_ A ) $= f0_dftr3 i0_dftr3 f1_dftr3 p_dftr5 i0_dftr3 f0_dftr3 a_sup_set_class f1_dftr3 p_dfss3 f0_dftr3 a_sup_set_class f1_dftr3 a_wss i0_dftr3 a_sup_set_class f1_dftr3 a_wcel i0_dftr3 f0_dftr3 a_sup_set_class a_wral f0_dftr3 f1_dftr3 p_ralbii f1_dftr3 a_wtr i0_dftr3 a_sup_set_class f1_dftr3 a_wcel i0_dftr3 f0_dftr3 a_sup_set_class a_wral f0_dftr3 f1_dftr3 a_wral f0_dftr3 a_sup_set_class f1_dftr3 a_wss f0_dftr3 f1_dftr3 a_wral p_bitr4i $.
$}

$(An alternate way of defining a transitive class.  Definition of [Enderton]
     p. 71.  (Contributed by NM, 29-Aug-1993.) $)

${
	$v A  $.
	f0_dftr4 $f class A $.
	p_dftr4 $p |- ( Tr A <-> A C_ ~P A ) $= f0_dftr4 a_df-tr f0_dftr4 f0_dftr4 p_sspwuni f0_dftr4 a_wtr f0_dftr4 a_cuni f0_dftr4 a_wss f0_dftr4 f0_dftr4 a_cpw a_wss p_bitr4i $.
$}

$(Equality theorem for the transitive class predicate.  (Contributed by NM,
     17-Sep-1993.) $)

${
	$v A B  $.
	f0_treq $f class A $.
	f1_treq $f class B $.
	p_treq $p |- ( A = B -> ( Tr A <-> Tr B ) ) $= f0_treq f1_treq p_unieq f0_treq f1_treq a_wceq f0_treq a_cuni f1_treq a_cuni f0_treq p_sseq1d f0_treq f1_treq f1_treq a_cuni p_sseq2 f0_treq f1_treq a_wceq f0_treq a_cuni f0_treq a_wss f1_treq a_cuni f0_treq a_wss f1_treq a_cuni f1_treq a_wss p_bitrd f0_treq a_df-tr f1_treq a_df-tr f0_treq f1_treq a_wceq f0_treq a_cuni f0_treq a_wss f1_treq a_cuni f1_treq a_wss f0_treq a_wtr f1_treq a_wtr p_3bitr4g $.
$}

$(In a transitive class, the membership relation is transitive.
       (Contributed by NM, 19-Apr-1994.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)

${
	$v A B C  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	f0_trel $f class A $.
	f1_trel $f class B $.
	f2_trel $f class C $.
	i0_trel $f set x $.
	i1_trel $f set y $.
	p_trel $p |- ( Tr A -> ( ( B e. C /\ C e. A ) -> B e. A ) ) $= i1_trel i0_trel f0_trel p_dftr2 i1_trel a_sup_set_class f1_trel i0_trel a_sup_set_class f2_trel p_eleq12 i0_trel a_sup_set_class f2_trel f0_trel p_eleq1 i0_trel a_sup_set_class f2_trel a_wceq i0_trel a_sup_set_class f0_trel a_wcel f2_trel f0_trel a_wcel a_wb i1_trel a_sup_set_class f1_trel a_wceq p_adantl i1_trel a_sup_set_class f1_trel a_wceq i0_trel a_sup_set_class f2_trel a_wceq a_wa i1_trel a_sup_set_class i0_trel a_sup_set_class a_wcel f1_trel f2_trel a_wcel i0_trel a_sup_set_class f0_trel a_wcel f2_trel f0_trel a_wcel p_anbi12d i1_trel a_sup_set_class f1_trel f0_trel p_eleq1 i1_trel a_sup_set_class f1_trel a_wceq i1_trel a_sup_set_class f0_trel a_wcel f1_trel f0_trel a_wcel a_wb i0_trel a_sup_set_class f2_trel a_wceq p_adantr i1_trel a_sup_set_class f1_trel a_wceq i0_trel a_sup_set_class f2_trel a_wceq a_wa i1_trel a_sup_set_class i0_trel a_sup_set_class a_wcel i0_trel a_sup_set_class f0_trel a_wcel a_wa f1_trel f2_trel a_wcel f2_trel f0_trel a_wcel a_wa i1_trel a_sup_set_class f0_trel a_wcel f1_trel f0_trel a_wcel p_imbi12d i1_trel a_sup_set_class i0_trel a_sup_set_class a_wcel i0_trel a_sup_set_class f0_trel a_wcel a_wa i1_trel a_sup_set_class f0_trel a_wcel a_wi f1_trel f2_trel a_wcel f2_trel f0_trel a_wcel a_wa f1_trel f0_trel a_wcel a_wi i1_trel i0_trel f1_trel f2_trel f2_trel f0_trel p_spc2gv i1_trel a_sup_set_class i0_trel a_sup_set_class a_wcel i0_trel a_sup_set_class f0_trel a_wcel a_wa i1_trel a_sup_set_class f0_trel a_wcel a_wi i0_trel a_wal i1_trel a_wal f1_trel f2_trel a_wcel f2_trel f0_trel a_wcel a_wa f1_trel f0_trel a_wcel p_pm2.43b f0_trel a_wtr i1_trel a_sup_set_class i0_trel a_sup_set_class a_wcel i0_trel a_sup_set_class f0_trel a_wcel a_wa i1_trel a_sup_set_class f0_trel a_wcel a_wi i0_trel a_wal i1_trel a_wal f1_trel f2_trel a_wcel f2_trel f0_trel a_wcel a_wa f1_trel f0_trel a_wcel a_wi p_sylbi $.
$}

$(In a transitive class, the membership relation is transitive.
     (Contributed by NM, 19-Apr-1994.) $)

${
	$v A B C D  $.
	f0_trel3 $f class A $.
	f1_trel3 $f class B $.
	f2_trel3 $f class C $.
	f3_trel3 $f class D $.
	p_trel3 $p |- ( Tr A -> ( ( B e. C /\ C e. D /\ D e. A ) -> B e. A ) ) $= f1_trel3 f2_trel3 a_wcel f2_trel3 f3_trel3 a_wcel f3_trel3 f0_trel3 a_wcel p_3anass f0_trel3 f2_trel3 f3_trel3 p_trel f0_trel3 a_wtr f2_trel3 f3_trel3 a_wcel f3_trel3 f0_trel3 a_wcel a_wa f2_trel3 f0_trel3 a_wcel f1_trel3 f2_trel3 a_wcel p_anim2d f1_trel3 f2_trel3 a_wcel f2_trel3 f3_trel3 a_wcel f3_trel3 f0_trel3 a_wcel a_w3a f1_trel3 f2_trel3 a_wcel f2_trel3 f3_trel3 a_wcel f3_trel3 f0_trel3 a_wcel a_wa a_wa f0_trel3 a_wtr f1_trel3 f2_trel3 a_wcel f2_trel3 f0_trel3 a_wcel a_wa p_syl5bi f0_trel3 f1_trel3 f2_trel3 p_trel f0_trel3 a_wtr f1_trel3 f2_trel3 a_wcel f2_trel3 f3_trel3 a_wcel f3_trel3 f0_trel3 a_wcel a_w3a f1_trel3 f2_trel3 a_wcel f2_trel3 f0_trel3 a_wcel a_wa f1_trel3 f0_trel3 a_wcel p_syld $.
$}

$(An element of a transitive class is a subset of the class.  (Contributed
       by NM, 7-Aug-1994.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_trss $f class A $.
	f1_trss $f class B $.
	i0_trss $f set x $.
	p_trss $p |- ( Tr A -> ( B e. A -> B C_ A ) ) $= i0_trss a_sup_set_class f1_trss f0_trss p_eleq1 i0_trss a_sup_set_class f1_trss f0_trss p_sseq1 i0_trss a_sup_set_class f1_trss a_wceq i0_trss a_sup_set_class f0_trss a_wcel f1_trss f0_trss a_wcel i0_trss a_sup_set_class f0_trss a_wss f1_trss f0_trss a_wss p_imbi12d i0_trss a_sup_set_class f1_trss a_wceq i0_trss a_sup_set_class f0_trss a_wcel i0_trss a_sup_set_class f0_trss a_wss a_wi f1_trss f0_trss a_wcel f1_trss f0_trss a_wss a_wi f0_trss a_wtr p_imbi2d i0_trss f0_trss p_dftr3 i0_trss a_sup_set_class f0_trss a_wss i0_trss f0_trss p_rsp f0_trss a_wtr i0_trss a_sup_set_class f0_trss a_wss i0_trss f0_trss a_wral i0_trss a_sup_set_class f0_trss a_wcel i0_trss a_sup_set_class f0_trss a_wss a_wi p_sylbi f0_trss a_wtr i0_trss a_sup_set_class f0_trss a_wcel i0_trss a_sup_set_class f0_trss a_wss a_wi a_wi f0_trss a_wtr f1_trss f0_trss a_wcel f1_trss f0_trss a_wss a_wi a_wi i0_trss f1_trss f0_trss p_vtoclg f0_trss a_wtr f1_trss f0_trss a_wcel f1_trss f0_trss a_wss p_pm2.43b $.
$}

$(The intersection of transitive classes is transitive.  (Contributed by
       NM, 9-May-1994.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_trin $f class A $.
	f1_trin $f class B $.
	i0_trin $f set x $.
	p_trin $p |- ( ( Tr A /\ Tr B ) -> Tr ( A i^i B ) ) $= i0_trin a_sup_set_class f0_trin f1_trin p_elin f0_trin i0_trin a_sup_set_class p_trss f1_trin i0_trin a_sup_set_class p_trss f0_trin a_wtr i0_trin a_sup_set_class f0_trin a_wcel i0_trin a_sup_set_class f0_trin a_wss f1_trin a_wtr i0_trin a_sup_set_class f1_trin a_wcel i0_trin a_sup_set_class f1_trin a_wss p_im2anan9 i0_trin a_sup_set_class f0_trin f1_trin a_cin a_wcel i0_trin a_sup_set_class f0_trin a_wcel i0_trin a_sup_set_class f1_trin a_wcel a_wa f0_trin a_wtr f1_trin a_wtr a_wa i0_trin a_sup_set_class f0_trin a_wss i0_trin a_sup_set_class f1_trin a_wss a_wa p_syl5bi i0_trin a_sup_set_class f0_trin f1_trin p_ssin f0_trin a_wtr f1_trin a_wtr a_wa i0_trin a_sup_set_class f0_trin f1_trin a_cin a_wcel i0_trin a_sup_set_class f0_trin a_wss i0_trin a_sup_set_class f1_trin a_wss a_wa i0_trin a_sup_set_class f0_trin f1_trin a_cin a_wss p_syl6ib f0_trin a_wtr f1_trin a_wtr a_wa i0_trin a_sup_set_class f0_trin f1_trin a_cin a_wss i0_trin f0_trin f1_trin a_cin p_ralrimiv i0_trin f0_trin f1_trin a_cin p_dftr3 f0_trin a_wtr f1_trin a_wtr a_wa i0_trin a_sup_set_class f0_trin f1_trin a_cin a_wss i0_trin f0_trin f1_trin a_cin a_wral f0_trin f1_trin a_cin a_wtr p_sylibr $.
$}

$(The empty set is transitive.  (Contributed by NM, 16-Sep-1993.) $)

${
	$v  $.
	p_tr0 $p |- Tr (/) $= a_c0 a_cpw p_0ss a_c0 p_dftr4 a_c0 a_wtr a_c0 a_c0 a_cpw a_wss p_mpbir $.
$}

$(The universe is transitive.  (Contributed by NM, 14-Sep-2003.) $)

${
	$v  $.
	p_trv $p |- Tr _V $= a_cvv a_cuni p_ssv a_cvv a_df-tr a_cvv a_wtr a_cvv a_cuni a_cvv a_wss p_mpbir $.
$}

$(The indexed union of a class of transitive sets is transitive.
       (Contributed by Mario Carneiro, 16-Nov-2014.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d y B  $.
	f0_triun $f set x $.
	f1_triun $f class A $.
	f2_triun $f class B $.
	i0_triun $f set y $.
	p_triun $p |- ( A. x e. A Tr B -> Tr U_ x e. A B ) $= f0_triun i0_triun a_sup_set_class f1_triun f2_triun p_eliun f2_triun a_wtr i0_triun a_sup_set_class f2_triun a_wcel f0_triun f1_triun p_r19.29 f0_triun i0_triun a_sup_set_class p_nfcv f0_triun f1_triun f2_triun p_nfiu1 f0_triun i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun p_nfss f2_triun i0_triun a_sup_set_class p_trss f2_triun a_wtr i0_triun a_sup_set_class f2_triun a_wcel i0_triun a_sup_set_class f2_triun a_wss p_imp f0_triun f1_triun f2_triun p_ssiun2 i0_triun a_sup_set_class f2_triun f0_triun f1_triun f2_triun a_ciun p_sstr2 f0_triun a_sup_set_class f1_triun a_wcel f2_triun f0_triun f1_triun f2_triun a_ciun a_wss i0_triun a_sup_set_class f2_triun a_wss i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun a_wss p_syl5com f2_triun a_wtr i0_triun a_sup_set_class f2_triun a_wcel a_wa i0_triun a_sup_set_class f2_triun a_wss f0_triun a_sup_set_class f1_triun a_wcel i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun a_wss p_syl5 f2_triun a_wtr i0_triun a_sup_set_class f2_triun a_wcel a_wa i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun a_wss f0_triun f1_triun p_rexlimi f2_triun a_wtr f0_triun f1_triun a_wral i0_triun a_sup_set_class f2_triun a_wcel f0_triun f1_triun a_wrex a_wa f2_triun a_wtr i0_triun a_sup_set_class f2_triun a_wcel a_wa f0_triun f1_triun a_wrex i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun a_wss p_syl i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun a_wcel f2_triun a_wtr f0_triun f1_triun a_wral i0_triun a_sup_set_class f2_triun a_wcel f0_triun f1_triun a_wrex i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun a_wss p_sylan2b f2_triun a_wtr f0_triun f1_triun a_wral i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun a_wss i0_triun f0_triun f1_triun f2_triun a_ciun p_ralrimiva i0_triun f0_triun f1_triun f2_triun a_ciun p_dftr3 f2_triun a_wtr f0_triun f1_triun a_wral i0_triun a_sup_set_class f0_triun f1_triun f2_triun a_ciun a_wss i0_triun f0_triun f1_triun f2_triun a_ciun a_wral f0_triun f1_triun f2_triun a_ciun a_wtr p_sylibr $.
$}

$(The union of a class of transitive sets is transitive.  Exercise 5(a) of
       [Enderton] p. 73.  (Contributed by Scott Fenton, 21-Feb-2011.)  (Proof
       shortened by Mario Carneiro, 26-Apr-2014.) $)

${
	$v x A  $.
	$d x A  $.
	f0_truni $f set x $.
	f1_truni $f class A $.
	p_truni $p |- ( A. x e. A Tr x -> Tr U. A ) $= f0_truni f1_truni f0_truni a_sup_set_class p_triun f0_truni f1_truni p_uniiun f1_truni a_cuni f0_truni f1_truni f0_truni a_sup_set_class a_ciun p_treq f1_truni a_cuni f0_truni f1_truni f0_truni a_sup_set_class a_ciun a_wceq f1_truni a_cuni a_wtr f0_truni f1_truni f0_truni a_sup_set_class a_ciun a_wtr a_wb a_ax-mp f0_truni a_sup_set_class a_wtr f0_truni f1_truni a_wral f0_truni f1_truni f0_truni a_sup_set_class a_ciun a_wtr f1_truni a_cuni a_wtr p_sylibr $.
$}

$(The intersection of a class of transitive sets is transitive.  Exercise
       5(b) of [Enderton] p. 73.  (Contributed by Scott Fenton,
       25-Feb-2011.) $)

${
	$v x A  $.
	$d x y A  $.
	$d y  $.
	f0_trint $f set x $.
	f1_trint $f class A $.
	i0_trint $f set y $.
	p_trint $p |- ( A. x e. A Tr x -> Tr |^| A ) $= i0_trint f0_trint a_sup_set_class p_dftr3 f0_trint a_sup_set_class a_wtr i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss i0_trint f0_trint a_sup_set_class a_wral f0_trint f1_trint p_ralbii f0_trint a_sup_set_class a_wtr f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss i0_trint f0_trint a_sup_set_class a_wral f0_trint f1_trint a_wral p_biimpi i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss i0_trint f0_trint a_sup_set_class a_df-ral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss i0_trint f0_trint a_sup_set_class a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss a_wi i0_trint a_wal f0_trint f1_trint p_ralbii i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss a_wi f0_trint i0_trint f1_trint p_ralcom4 i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss i0_trint f0_trint a_sup_set_class a_wral f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss a_wi i0_trint a_wal f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss a_wi f0_trint f1_trint a_wral i0_trint a_wal p_bitri f0_trint a_sup_set_class a_wtr f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss i0_trint f0_trint a_sup_set_class a_wral f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss a_wi f0_trint f1_trint a_wral i0_trint a_wal p_sylib i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss f0_trint f1_trint p_ralim i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss a_wi f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss f0_trint f1_trint a_wral a_wi i0_trint p_alimi f0_trint a_sup_set_class a_wtr f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss a_wi f0_trint f1_trint a_wral i0_trint a_wal i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss f0_trint f1_trint a_wral a_wi i0_trint a_wal p_syl i0_trint f1_trint a_cint p_dftr3 i0_trint a_sup_set_class f1_trint a_cint a_wss i0_trint f1_trint a_cint a_df-ral i0_trint p_vex f0_trint i0_trint a_sup_set_class f1_trint p_elint2 f0_trint i0_trint a_sup_set_class f1_trint p_ssint i0_trint a_sup_set_class f1_trint a_cint a_wcel i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel f0_trint f1_trint a_wral i0_trint a_sup_set_class f1_trint a_cint a_wss i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss f0_trint f1_trint a_wral p_imbi12i i0_trint a_sup_set_class f1_trint a_cint a_wcel i0_trint a_sup_set_class f1_trint a_cint a_wss a_wi i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss f0_trint f1_trint a_wral a_wi i0_trint p_albii i0_trint a_sup_set_class f1_trint a_cint a_wss i0_trint f1_trint a_cint a_wral i0_trint a_sup_set_class f1_trint a_cint a_wcel i0_trint a_sup_set_class f1_trint a_cint a_wss a_wi i0_trint a_wal i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss f0_trint f1_trint a_wral a_wi i0_trint a_wal p_bitri f1_trint a_cint a_wtr i0_trint a_sup_set_class f1_trint a_cint a_wss i0_trint f1_trint a_cint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss f0_trint f1_trint a_wral a_wi i0_trint a_wal p_bitri f0_trint a_sup_set_class a_wtr f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wcel f0_trint f1_trint a_wral i0_trint a_sup_set_class f0_trint a_sup_set_class a_wss f0_trint f1_trint a_wral a_wi i0_trint a_wal f1_trint a_cint a_wtr p_sylibr $.
$}

$(If ` A ` is transitive and non-null, then ` |^| A ` is a subset of
       ` A ` .  (Contributed by Scott Fenton, 3-Mar-2011.) $)

${
	$v A  $.
	$d x y A  $.
	$d y  $.
	f0_trintss $f class A $.
	i0_trintss $f set x $.
	i1_trintss $f set y $.
	p_trintss $p |- ( ( A =/= (/) /\ Tr A ) -> |^| A C_ A ) $= i1_trintss p_vex i0_trintss i1_trintss a_sup_set_class f0_trintss p_elint2 i1_trintss a_sup_set_class i0_trintss a_sup_set_class a_wcel i0_trintss f0_trintss p_r19.2z f0_trintss a_c0 a_wne i1_trintss a_sup_set_class i0_trintss a_sup_set_class a_wcel i0_trintss f0_trintss a_wral i1_trintss a_sup_set_class i0_trintss a_sup_set_class a_wcel i0_trintss f0_trintss a_wrex p_ex f0_trintss i1_trintss a_sup_set_class i0_trintss a_sup_set_class p_trel f0_trintss a_wtr i1_trintss a_sup_set_class i0_trintss a_sup_set_class a_wcel i0_trintss a_sup_set_class f0_trintss a_wcel i1_trintss a_sup_set_class f0_trintss a_wcel p_exp3acom23 f0_trintss a_wtr i1_trintss a_sup_set_class i0_trintss a_sup_set_class a_wcel i1_trintss a_sup_set_class f0_trintss a_wcel i0_trintss f0_trintss p_rexlimdv f0_trintss a_c0 a_wne i1_trintss a_sup_set_class i0_trintss a_sup_set_class a_wcel i0_trintss f0_trintss a_wral i1_trintss a_sup_set_class i0_trintss a_sup_set_class a_wcel i0_trintss f0_trintss a_wrex f0_trintss a_wtr i1_trintss a_sup_set_class f0_trintss a_wcel p_sylan9 i1_trintss a_sup_set_class f0_trintss a_cint a_wcel i1_trintss a_sup_set_class i0_trintss a_sup_set_class a_wcel i0_trintss f0_trintss a_wral f0_trintss a_c0 a_wne f0_trintss a_wtr a_wa i1_trintss a_sup_set_class f0_trintss a_wcel p_syl5bi f0_trintss a_c0 a_wne f0_trintss a_wtr a_wa i1_trintss f0_trintss a_cint f0_trintss p_ssrdv $.
$}

$(Any non-empty transitive class includes its intersection.  Exercise 2 in
       [TakeutiZaring] p. 44.  (Contributed by Andrew Salmon, 14-Nov-2011.) $)

${
	$v A  $.
	$d x A  $.
	f0_trint0 $f class A $.
	i0_trint0 $f set x $.
	p_trint0 $p |- ( ( Tr A /\ A =/= (/) ) -> |^| A C_ A ) $= i0_trint0 f0_trint0 p_n0 i0_trint0 a_sup_set_class f0_trint0 p_intss1 f0_trint0 i0_trint0 a_sup_set_class p_trss f0_trint0 a_wtr i0_trint0 a_sup_set_class f0_trint0 a_wcel i0_trint0 a_sup_set_class f0_trint0 a_wss p_com12 f0_trint0 a_cint i0_trint0 a_sup_set_class f0_trint0 p_sstr2 i0_trint0 a_sup_set_class f0_trint0 a_wcel f0_trint0 a_cint i0_trint0 a_sup_set_class a_wss f0_trint0 a_wtr i0_trint0 a_sup_set_class f0_trint0 a_wss f0_trint0 a_cint f0_trint0 a_wss p_sylsyld i0_trint0 a_sup_set_class f0_trint0 a_wcel f0_trint0 a_wtr f0_trint0 a_cint f0_trint0 a_wss a_wi i0_trint0 p_exlimiv f0_trint0 a_c0 a_wne i0_trint0 a_sup_set_class f0_trint0 a_wcel i0_trint0 a_wex f0_trint0 a_wtr f0_trint0 a_cint f0_trint0 a_wss a_wi p_sylbi f0_trint0 a_c0 a_wne f0_trint0 a_wtr f0_trint0 a_cint f0_trint0 a_wss p_impcom $.
$}


