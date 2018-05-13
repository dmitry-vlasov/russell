$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Founded_and_well-ordering_relations.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Ordinals

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Introduce new constant symbols. $)

$c Ord $.

$(Ordinal predicate $)

$c On $.

$(The class of ordinal numbers $)

$c Lim $.

$(Limit ordinal predicate $)

$c suc $.

$(Successor function (read:  'successor of') $)

$(Extend the definition of a wff to include the ordinal predicate. $)

${
	$v A  $.
	f0_word $f class A $.
	a_word $a wff Ord A $.
$}

$(Extend the definition of a class to include the class of all ordinal
     numbers.  (The 0 in the name prevents creating a file called con.html,
     which causes problems in Windows.) $)

${
	$v  $.
	a_con0 $a class On $.
$}

$(Extend the definition of a wff to include the limit ordinal predicate. $)

${
	$v A  $.
	f0_wlim $f class A $.
	a_wlim $a wff Lim A $.
$}

$(Extend class notation to include the successor function. $)

${
	$v A  $.
	f0_csuc $f class A $.
	a_csuc $a class suc A $.
$}

$(Define the ordinal predicate, which is true for a class that is transitive
     and is well-ordered by the epsilon relation.  Variant of definition of
     [BellMachover] p. 468.  (Contributed by NM, 17-Sep-1993.) $)

${
	$v A  $.
	f0_df-ord $f class A $.
	a_df-ord $a |- ( Ord A <-> ( Tr A /\ _E We A ) ) $.
$}

$(Define the class of all ordinal numbers.  Definition 7.11 of
     [TakeutiZaring] p. 38.  (Contributed by NM, 5-Jun-1994.) $)

${
	$v x  $.
	f0_df-on $f set x $.
	a_df-on $a |- On = { x | Ord x } $.
$}

$(Define the limit ordinal predicate, which is true for a non-empty ordinal
     that is not a successor (i.e. that is the union of itself).  Our
     definition combines the definition of Lim of [BellMachover] p. 471 and
     Exercise 1 of [TakeutiZaring] p. 42.  See ~ dflim2 , ~ dflim3 , and dflim4
     for alternate definitions.  (Contributed by NM, 22-Apr-1994.) $)

${
	$v A  $.
	f0_df-lim $f class A $.
	a_df-lim $a |- ( Lim A <-> ( Ord A /\ A =/= (/) /\ A = U. A ) ) $.
$}

$(Define the successor of a class.  When applied to an ordinal number, the
     successor means the same thing as "plus 1" (see ~ oa1suc ).  Definition
     7.22 of [TakeutiZaring] p. 41, who use "+ 1" to denote this function.  Our
     definition is a generalization to classes.  Although it is not
     conventional to use it with proper classes, it has no effect on a proper
     class ( ~ sucprc ), so that the successor of any ordinal class is still an
     ordinal class ( ~ ordsuc ), simplifying certain proofs.  Some authors
     denote the successor operation with a prime (apostrophe-like) symbol, such
     as Definition 6 of [Suppes] p. 134 and the definition of successor in
     [Mendelson] p. 246 (who uses the symbol "Suc" as a predicate to mean "is a
     successor ordinal").  The definition of successor of [Enderton] p. 68
     denotes the operation with a plus-sign superscript.  (Contributed by NM,
     30-Aug-1993.) $)

${
	$v A  $.
	f0_df-suc $f class A $.
	a_df-suc $a |- suc A = ( A u. { A } ) $.
$}

$(Equality theorem for the ordinal predicate.  (Contributed by NM,
     17-Sep-1993.) $)

${
	$v A B  $.
	f0_ordeq $f class A $.
	f1_ordeq $f class B $.
	p_ordeq $p |- ( A = B -> ( Ord A <-> Ord B ) ) $= f0_ordeq f1_ordeq p_treq f0_ordeq f1_ordeq a_cep p_weeq2 f0_ordeq f1_ordeq a_wceq f0_ordeq a_wtr f1_ordeq a_wtr f0_ordeq a_cep a_wwe f1_ordeq a_cep a_wwe p_anbi12d f0_ordeq a_df-ord f1_ordeq a_df-ord f0_ordeq f1_ordeq a_wceq f0_ordeq a_wtr f0_ordeq a_cep a_wwe a_wa f1_ordeq a_wtr f1_ordeq a_cep a_wwe a_wa f0_ordeq a_word f1_ordeq a_word p_3bitr4g $.
$}

$(An ordinal number is an ordinal set.  (Contributed by NM,
       5-Jun-1994.) $)

${
	$v A V  $.
	$d x A  $.
	f0_elong $f class A $.
	f1_elong $f class V $.
	i0_elong $f set x $.
	p_elong $p |- ( A e. V -> ( A e. On <-> Ord A ) ) $= i0_elong a_sup_set_class f0_elong p_ordeq i0_elong a_df-on i0_elong a_sup_set_class a_word f0_elong a_word i0_elong f0_elong a_con0 f1_elong p_elab2g $.
$}

$(An ordinal number is an ordinal set.  (Contributed by NM,
       5-Jun-1994.) $)

${
	$v A  $.
	f0_elon $f class A $.
	e0_elon $e |- A e. _V $.
	p_elon $p |- ( A e. On <-> Ord A ) $= e0_elon f0_elon a_cvv p_elong f0_elon a_cvv a_wcel f0_elon a_con0 a_wcel f0_elon a_word a_wb a_ax-mp $.
$}

$(An ordinal number has the ordinal property.  (Contributed by NM,
     5-Jun-1994.) $)

${
	$v A  $.
	f0_eloni $f class A $.
	p_eloni $p |- ( A e. On -> Ord A ) $= f0_eloni a_con0 p_elong f0_eloni a_con0 a_wcel f0_eloni a_word p_ibi $.
$}

$(An ordinal number is an ordinal set.  (Contributed by NM, 8-Feb-2004.) $)

${
	$v A  $.
	f0_elon2 $f class A $.
	p_elon2 $p |- ( A e. On <-> ( Ord A /\ A e. _V ) ) $= f0_elon2 p_eloni f0_elon2 a_con0 p_elex f0_elon2 a_con0 a_wcel f0_elon2 a_word f0_elon2 a_cvv a_wcel p_jca f0_elon2 a_cvv p_elong f0_elon2 a_cvv a_wcel f0_elon2 a_con0 a_wcel f0_elon2 a_word p_biimparc f0_elon2 a_con0 a_wcel f0_elon2 a_word f0_elon2 a_cvv a_wcel a_wa p_impbii $.
$}

$(Equality theorem for the limit predicate.  (Contributed by NM,
     22-Apr-1994.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B  $.
	f0_limeq $f class A $.
	f1_limeq $f class B $.
	p_limeq $p |- ( A = B -> ( Lim A <-> Lim B ) ) $= f0_limeq f1_limeq p_ordeq f0_limeq f1_limeq a_c0 p_neeq1 f0_limeq f1_limeq a_wceq p_id f0_limeq f1_limeq p_unieq f0_limeq f1_limeq a_wceq f0_limeq f1_limeq f0_limeq a_cuni f1_limeq a_cuni p_eqeq12d f0_limeq f1_limeq a_wceq f0_limeq a_word f1_limeq a_word f0_limeq a_c0 a_wne f1_limeq a_c0 a_wne f0_limeq f0_limeq a_cuni a_wceq f1_limeq f1_limeq a_cuni a_wceq p_3anbi123d f0_limeq a_df-lim f1_limeq a_df-lim f0_limeq f1_limeq a_wceq f0_limeq a_word f0_limeq a_c0 a_wne f0_limeq f0_limeq a_cuni a_wceq a_w3a f1_limeq a_word f1_limeq a_c0 a_wne f1_limeq f1_limeq a_cuni a_wceq a_w3a f0_limeq a_wlim f1_limeq a_wlim p_3bitr4g $.
$}

$(Epsilon well-orders every ordinal.  Proposition 7.4 of [TakeutiZaring]
     p. 36.  (Contributed by NM, 3-Apr-1994.) $)

${
	$v A  $.
	f0_ordwe $f class A $.
	p_ordwe $p |- ( Ord A -> _E We A ) $= f0_ordwe a_df-ord f0_ordwe a_word f0_ordwe a_wtr f0_ordwe a_cep a_wwe p_simprbi $.
$}

$(An ordinal class is transitive.  (Contributed by NM, 3-Apr-1994.) $)

${
	$v A  $.
	f0_ordtr $f class A $.
	p_ordtr $p |- ( Ord A -> Tr A ) $= f0_ordtr a_df-ord f0_ordtr a_word f0_ordtr a_wtr f0_ordtr a_cep a_wwe p_simplbi $.
$}

$(Epsilon is well-founded on an ordinal class.  (Contributed by NM,
     22-Apr-1994.) $)

${
	$v A  $.
	f0_ordfr $f class A $.
	p_ordfr $p |- ( Ord A -> _E Fr A ) $= f0_ordfr p_ordwe f0_ordfr a_cep p_wefr f0_ordfr a_word f0_ordfr a_cep a_wwe f0_ordfr a_cep a_wfr p_syl $.
$}

$(An element of an ordinal class is a subset of it.  (Contributed by NM,
     30-May-1994.) $)

${
	$v A B  $.
	f0_ordelss $f class A $.
	f1_ordelss $f class B $.
	p_ordelss $p |- ( ( Ord A /\ B e. A ) -> B C_ A ) $= f0_ordelss p_ordtr f0_ordelss f1_ordelss p_trss f0_ordelss a_wtr f1_ordelss f0_ordelss a_wcel f1_ordelss f0_ordelss a_wss p_imp f0_ordelss a_word f0_ordelss a_wtr f1_ordelss f0_ordelss a_wcel f1_ordelss f0_ordelss a_wss p_sylan $.
$}

$(A transitive subclass of an ordinal class is ordinal.  (Contributed by NM,
     29-May-1994.) $)

${
	$v A B  $.
	f0_trssord $f class A $.
	f1_trssord $f class B $.
	p_trssord $p |- ( ( Tr A /\ A C_ B /\ Ord B ) -> Ord A ) $= f1_trssord p_ordwe f0_trssord f1_trssord a_cep p_wess f0_trssord f1_trssord a_wss f1_trssord a_cep a_wwe f0_trssord a_cep a_wwe p_imp f1_trssord a_word f0_trssord f1_trssord a_wss f1_trssord a_cep a_wwe f0_trssord a_cep a_wwe p_sylan2 f0_trssord f1_trssord a_wss f1_trssord a_word a_wa f0_trssord a_cep a_wwe f0_trssord a_wtr p_anim2i f0_trssord a_wtr f0_trssord f1_trssord a_wss f1_trssord a_word f0_trssord a_wtr f0_trssord a_cep a_wwe a_wa p_3impb f0_trssord a_df-ord f0_trssord a_wtr f0_trssord f1_trssord a_wss f1_trssord a_word a_w3a f0_trssord a_wtr f0_trssord a_cep a_wwe a_wa f0_trssord a_word p_sylibr $.
$}

$(Epsilon irreflexivity of ordinals: no ordinal class is a member of
     itself.  Theorem 2.2(i) of [BellMachover] p. 469, generalized to classes.
     We prove this without invoking the Axiom of Regularity.  (Contributed by
     NM, 2-Jan-1994.) $)

${
	$v A  $.
	f0_ordirr $f class A $.
	p_ordirr $p |- ( Ord A -> -. A e. A ) $= f0_ordirr p_ordfr f0_ordirr p_efrirr f0_ordirr a_word f0_ordirr a_cep a_wfr f0_ordirr f0_ordirr a_wcel a_wn p_syl $.
$}

$(A member of an ordinal class is not equal to it.  (Contributed by NM,
     25-May-1998.) $)

${
	$v A B  $.
	f0_nordeq $f class A $.
	f1_nordeq $f class B $.
	p_nordeq $p |- ( ( Ord A /\ B e. A ) -> A =/= B ) $= f0_nordeq p_ordirr f0_nordeq f1_nordeq f0_nordeq p_eleq1 f0_nordeq f1_nordeq a_wceq f0_nordeq f0_nordeq a_wcel f1_nordeq f0_nordeq a_wcel p_notbid f0_nordeq a_word f0_nordeq f0_nordeq a_wcel a_wn f0_nordeq f1_nordeq a_wceq f1_nordeq f0_nordeq a_wcel a_wn p_syl5ibcom f0_nordeq a_word f1_nordeq f0_nordeq a_wcel f0_nordeq f1_nordeq p_necon2ad f0_nordeq a_word f1_nordeq f0_nordeq a_wcel f0_nordeq f1_nordeq a_wne p_imp $.
$}

$(An ordinal class cannot an element of one of its members.  Variant of
     first part of Theorem 2.2(vii) of [BellMachover] p. 469.  (Contributed by
     NM, 3-Apr-1994.) $)

${
	$v A B  $.
	f0_ordn2lp $f class A $.
	f1_ordn2lp $f class B $.
	p_ordn2lp $p |- ( Ord A -> -. ( A e. B /\ B e. A ) ) $= f0_ordn2lp p_ordirr f0_ordn2lp p_ordtr f0_ordn2lp f0_ordn2lp f1_ordn2lp p_trel f0_ordn2lp a_word f0_ordn2lp a_wtr f0_ordn2lp f1_ordn2lp a_wcel f1_ordn2lp f0_ordn2lp a_wcel a_wa f0_ordn2lp f0_ordn2lp a_wcel a_wi p_syl f0_ordn2lp a_word f0_ordn2lp f1_ordn2lp a_wcel f1_ordn2lp f0_ordn2lp a_wcel a_wa f0_ordn2lp f0_ordn2lp a_wcel p_mtod $.
$}

$(A subclass (possibly proper) of an ordinal class has a minimal element.
       Proposition 7.5 of [TakeutiZaring] p. 36.  (Contributed by NM,
       18-Feb-2004.)  (Revised by David Abernethy, 16-Mar-2011.) $)

${
	$v x A B  $.
	$d x B  $.
	f0_tz7.5 $f set x $.
	f1_tz7.5 $f class A $.
	f2_tz7.5 $f class B $.
	p_tz7.5 $p |- ( ( Ord A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) ) $= f1_tz7.5 p_ordwe f0_tz7.5 f1_tz7.5 f2_tz7.5 p_wefrc f1_tz7.5 a_word f1_tz7.5 a_cep a_wwe f2_tz7.5 f1_tz7.5 a_wss f2_tz7.5 a_c0 a_wne f2_tz7.5 f0_tz7.5 a_sup_set_class a_cin a_c0 a_wceq f0_tz7.5 f2_tz7.5 a_wrex p_syl3an1 $.
$}

$(An element of an ordinal class is ordinal.  Proposition 7.6 of
       [TakeutiZaring] p. 36.  (Contributed by NM, 23-Apr-1994.) $)

${
	$v A B  $.
	$d x y z A  $.
	$d x y z B  $.
	f0_ordelord $f class A $.
	f1_ordelord $f class B $.
	i0_ordelord $f set x $.
	i1_ordelord $f set y $.
	i2_ordelord $f set z $.
	p_ordelord $p |- ( ( Ord A /\ B e. A ) -> Ord B ) $= i0_ordelord a_sup_set_class f1_ordelord f0_ordelord p_eleq1 i0_ordelord a_sup_set_class f1_ordelord a_wceq i0_ordelord a_sup_set_class f0_ordelord a_wcel f1_ordelord f0_ordelord a_wcel f0_ordelord a_word p_anbi2d i0_ordelord a_sup_set_class f1_ordelord p_ordeq i0_ordelord a_sup_set_class f1_ordelord a_wceq f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa f0_ordelord a_word f1_ordelord f0_ordelord a_wcel a_wa i0_ordelord a_sup_set_class a_word f1_ordelord a_word p_imbi12d f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa p_simpll i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel p_3anrot i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel p_3anass i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wcel a_w3a i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_w3a i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa a_wa p_bitr3i f0_ordelord p_ordtr f0_ordelord i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class p_trel3 f0_ordelord a_word f0_ordelord a_wtr i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wcel a_w3a i2_ordelord a_sup_set_class f0_ordelord a_wcel a_wi p_syl i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa a_wa i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wcel a_w3a f0_ordelord a_word i2_ordelord a_sup_set_class f0_ordelord a_wcel p_syl5bir f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa i2_ordelord a_sup_set_class f0_ordelord a_wcel p_impl f0_ordelord p_ordtr f0_ordelord i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class p_trel f0_ordelord a_word f0_ordelord a_wtr i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i1_ordelord a_sup_set_class f0_ordelord a_wcel a_wi p_syl f0_ordelord a_word i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wcel i1_ordelord a_sup_set_class f0_ordelord a_wcel p_exp3acom23 f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class f0_ordelord a_wcel p_imp31 f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel p_adantrl f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa p_simplr f0_ordelord p_ordwe i2_ordelord i1_ordelord i0_ordelord f0_ordelord p_wetrep f0_ordelord a_word f0_ordelord a_cep a_wwe i2_ordelord a_sup_set_class f0_ordelord a_wcel i1_ordelord a_sup_set_class f0_ordelord a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wcel a_w3a i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa i2_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wi p_sylan f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa a_wa f0_ordelord a_word i2_ordelord a_sup_set_class f0_ordelord a_wcel i1_ordelord a_sup_set_class f0_ordelord a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wcel i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa i2_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wi p_syl13anc f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa i2_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wi p_ex f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa i2_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel p_pm2.43d f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa i2_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wi i2_ordelord i1_ordelord p_alrimivv i2_ordelord i1_ordelord i0_ordelord a_sup_set_class p_dftr2 f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i2_ordelord a_sup_set_class i1_ordelord a_sup_set_class a_wcel i1_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wa i2_ordelord a_sup_set_class i0_ordelord a_sup_set_class a_wcel a_wi i1_ordelord a_wal i2_ordelord a_wal i0_ordelord a_sup_set_class a_wtr p_sylibr f0_ordelord p_ordtr f0_ordelord i0_ordelord a_sup_set_class p_trss f0_ordelord a_word f0_ordelord a_wtr i0_ordelord a_sup_set_class f0_ordelord a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wss a_wi p_syl f0_ordelord p_ordwe i0_ordelord a_sup_set_class f0_ordelord a_cep p_wess f0_ordelord a_word f0_ordelord a_cep a_wwe i0_ordelord a_sup_set_class f0_ordelord a_wss i0_ordelord a_sup_set_class a_cep a_wwe p_syl5com f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel i0_ordelord a_sup_set_class f0_ordelord a_wss i0_ordelord a_sup_set_class a_cep a_wwe p_syld f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel i0_ordelord a_sup_set_class a_cep a_wwe p_imp i0_ordelord a_sup_set_class a_df-ord f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i0_ordelord a_sup_set_class a_wtr i0_ordelord a_sup_set_class a_cep a_wwe i0_ordelord a_sup_set_class a_word p_sylanbrc f0_ordelord a_word i0_ordelord a_sup_set_class f0_ordelord a_wcel a_wa i0_ordelord a_sup_set_class a_word a_wi f0_ordelord a_word f1_ordelord f0_ordelord a_wcel a_wa f1_ordelord a_word a_wi i0_ordelord f1_ordelord f0_ordelord p_vtoclg f0_ordelord a_word f1_ordelord f0_ordelord a_wcel f1_ordelord a_word p_anabsi7 $.
$}

$(The class of all ordinal numbers is transitive.  (Contributed by NM,
       4-May-2009.) $)

${
	$v  $.
	$d x y  $.
	i0_tron $f set x $.
	i1_tron $f set y $.
	p_tron $p |- Tr On $= i0_tron a_con0 p_dftr3 i0_tron p_vex i0_tron a_sup_set_class p_elon i0_tron a_sup_set_class i1_tron a_sup_set_class p_ordelord i0_tron a_sup_set_class a_con0 a_wcel i0_tron a_sup_set_class a_word i1_tron a_sup_set_class i0_tron a_sup_set_class a_wcel i1_tron a_sup_set_class a_word p_sylanb i0_tron a_sup_set_class a_con0 a_wcel i1_tron a_sup_set_class i0_tron a_sup_set_class a_wcel i1_tron a_sup_set_class a_word p_ex i1_tron p_vex i1_tron a_sup_set_class p_elon i0_tron a_sup_set_class a_con0 a_wcel i1_tron a_sup_set_class i0_tron a_sup_set_class a_wcel i1_tron a_sup_set_class a_word i1_tron a_sup_set_class a_con0 a_wcel p_syl6ibr i0_tron a_sup_set_class a_con0 a_wcel i1_tron i0_tron a_sup_set_class a_con0 p_ssrdv a_con0 a_wtr i0_tron a_sup_set_class a_con0 a_wss i0_tron a_con0 p_mprgbir $.
$}

$(An element of an ordinal class is an ordinal number.  (Contributed by NM,
     26-Oct-2003.) $)

${
	$v A B  $.
	f0_ordelon $f class A $.
	f1_ordelon $f class B $.
	p_ordelon $p |- ( ( Ord A /\ B e. A ) -> B e. On ) $= f0_ordelon f1_ordelon p_ordelord f1_ordelon f0_ordelon p_elong f1_ordelon f0_ordelon a_wcel f1_ordelon a_con0 a_wcel f1_ordelon a_word a_wb f0_ordelon a_word p_adantl f0_ordelon a_word f1_ordelon f0_ordelon a_wcel a_wa f1_ordelon a_con0 a_wcel f1_ordelon a_word p_mpbird $.
$}

$(An element of an ordinal number is an ordinal number.  Theorem 2.2(iii) of
     [BellMachover] p. 469.  (Contributed by NM, 26-Oct-2003.) $)

${
	$v A B  $.
	f0_onelon $f class A $.
	f1_onelon $f class B $.
	p_onelon $p |- ( ( A e. On /\ B e. A ) -> B e. On ) $= f0_onelon p_eloni f0_onelon f1_onelon p_ordelon f0_onelon a_con0 a_wcel f0_onelon a_word f1_onelon f0_onelon a_wcel f1_onelon a_con0 a_wcel p_sylan $.
$}

$(Proposition 7.7 of [TakeutiZaring] p. 37.  (Contributed by NM,
       5-May-1994.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_tz7.7 $f class A $.
	f1_tz7.7 $f class B $.
	i0_tz7.7 $f set x $.
	i1_tz7.7 $f set y $.
	p_tz7.7 $p |- ( ( Ord A /\ Tr B ) -> ( B e. A <-> ( B C_ A /\ B =/= A ) ) ) $= f0_tz7.7 p_ordtr f0_tz7.7 p_ordfr f0_tz7.7 f1_tz7.7 p_tz7.2 f0_tz7.7 a_wtr f0_tz7.7 a_cep a_wfr f1_tz7.7 f0_tz7.7 a_wcel f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wne a_wa p_3exp f0_tz7.7 a_word f0_tz7.7 a_wtr f0_tz7.7 a_cep a_wfr f1_tz7.7 f0_tz7.7 a_wcel f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wne a_wa a_wi p_sylc f0_tz7.7 a_word f1_tz7.7 f0_tz7.7 a_wcel f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wne a_wa a_wi f1_tz7.7 a_wtr p_adantr f1_tz7.7 f0_tz7.7 p_pssdifn0 f0_tz7.7 f1_tz7.7 p_difss i0_tz7.7 f0_tz7.7 f0_tz7.7 f1_tz7.7 a_cdif p_tz7.5 f0_tz7.7 a_word f0_tz7.7 f1_tz7.7 a_cdif f0_tz7.7 a_wss f0_tz7.7 f1_tz7.7 a_cdif a_c0 a_wne f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq i0_tz7.7 f0_tz7.7 f1_tz7.7 a_cdif a_wrex p_mp3an2 f0_tz7.7 p_ordtr i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 p_eldifi f0_tz7.7 i0_tz7.7 a_sup_set_class p_trss f0_tz7.7 f1_tz7.7 i0_tz7.7 a_sup_set_class p_difin0ss f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq i0_tz7.7 a_sup_set_class f0_tz7.7 a_wss i0_tz7.7 a_sup_set_class f1_tz7.7 a_wss p_com12 i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 a_wcel f0_tz7.7 a_wtr i0_tz7.7 a_sup_set_class f0_tz7.7 a_wss f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq i0_tz7.7 a_sup_set_class f1_tz7.7 a_wss a_wi p_syl56 f0_tz7.7 a_word f0_tz7.7 a_wtr i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq i0_tz7.7 a_sup_set_class f1_tz7.7 a_wss a_wi a_wi p_syl f0_tz7.7 a_word i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq i0_tz7.7 a_sup_set_class f1_tz7.7 a_wss a_wi a_wi f1_tz7.7 a_wtr f1_tz7.7 f0_tz7.7 a_wss p_ad2antrr f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq i0_tz7.7 a_sup_set_class f1_tz7.7 a_wss p_imp32 i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class f1_tz7.7 p_eleq1 i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wceq i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f1_tz7.7 a_wcel p_biimpcd i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 p_eldifn i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wceq i0_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel p_nsyli i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wceq a_wn p_imp i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wceq a_wn f1_tz7.7 f0_tz7.7 a_wss p_adantll f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel a_wa i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wceq a_wn f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa p_adantl f1_tz7.7 i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class p_trel f1_tz7.7 a_wtr i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f1_tz7.7 a_wcel p_exp3acom23 f1_tz7.7 a_wtr i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel i0_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wi p_imp i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 p_eldifn f1_tz7.7 a_wtr i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wa i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel i0_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel p_nsyli f1_tz7.7 a_wtr i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel a_wn a_wi p_ex f1_tz7.7 a_wtr i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel a_wn a_wi f1_tz7.7 f0_tz7.7 a_wss p_adantld f1_tz7.7 a_wtr f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel a_wn p_imp32 f1_tz7.7 a_wtr f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel a_wa i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel a_wn f0_tz7.7 a_word p_adantll f0_tz7.7 p_ordwe f1_tz7.7 f0_tz7.7 i1_tz7.7 a_sup_set_class p_ssel2 i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 p_eldifi f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wa i1_tz7.7 a_sup_set_class f0_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 a_wcel p_anim12i i1_tz7.7 i0_tz7.7 f0_tz7.7 p_wecmpep f0_tz7.7 a_word f0_tz7.7 a_cep a_wwe i1_tz7.7 a_sup_set_class f0_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 a_wcel a_wa i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wceq i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel a_w3o f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel a_wa p_syl2an f0_tz7.7 a_word f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel a_wa i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wceq i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel a_w3o f1_tz7.7 a_wtr p_adantlr f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel a_wa a_wa i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wceq i0_tz7.7 a_sup_set_class i1_tz7.7 a_sup_set_class a_wcel p_ecase23d f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wcel p_exp44 f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wcel p_com34 f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i1_tz7.7 a_sup_set_class f1_tz7.7 a_wcel i1_tz7.7 a_sup_set_class i0_tz7.7 a_sup_set_class a_wcel a_wi p_imp31 f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel a_wa i1_tz7.7 f1_tz7.7 i0_tz7.7 a_sup_set_class p_ssrdv f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel f1_tz7.7 i0_tz7.7 a_sup_set_class a_wss f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq p_adantrr f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq a_wa a_wa i0_tz7.7 a_sup_set_class f1_tz7.7 p_eqssd i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 p_eldifi i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel i0_tz7.7 a_sup_set_class f0_tz7.7 a_wcel f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq p_ad2antrl f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq a_wa a_wa i0_tz7.7 a_sup_set_class f1_tz7.7 f0_tz7.7 p_eqeltrrd f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa i0_tz7.7 a_sup_set_class f0_tz7.7 f1_tz7.7 a_cdif a_wcel f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq f1_tz7.7 f0_tz7.7 a_wcel p_exp32 f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq f1_tz7.7 f0_tz7.7 a_wcel i0_tz7.7 f0_tz7.7 f1_tz7.7 a_cdif p_rexlimdv f0_tz7.7 a_word f0_tz7.7 f1_tz7.7 a_cdif a_c0 a_wne a_wa f0_tz7.7 f1_tz7.7 a_cdif i0_tz7.7 a_sup_set_class a_cin a_c0 a_wceq i0_tz7.7 f0_tz7.7 f1_tz7.7 a_cdif a_wrex f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss a_wa f1_tz7.7 f0_tz7.7 a_wcel p_syl5 f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss f0_tz7.7 a_word f0_tz7.7 f1_tz7.7 a_cdif a_c0 a_wne f1_tz7.7 f0_tz7.7 a_wcel p_exp4b f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss f0_tz7.7 a_word f0_tz7.7 f1_tz7.7 a_cdif a_c0 a_wne f1_tz7.7 f0_tz7.7 a_wcel a_wi p_com23 f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f0_tz7.7 a_word f1_tz7.7 f0_tz7.7 a_wss f0_tz7.7 f1_tz7.7 a_cdif a_c0 a_wne f1_tz7.7 f0_tz7.7 a_wcel a_wi a_wi f1_tz7.7 a_wtr p_adantrd f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss f0_tz7.7 f1_tz7.7 a_cdif a_c0 a_wne f1_tz7.7 f0_tz7.7 a_wcel a_wi a_wi p_pm2.43i f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wne a_wa f0_tz7.7 f1_tz7.7 a_cdif a_c0 a_wne f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wcel p_syl7 f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wne f1_tz7.7 f0_tz7.7 a_wcel p_exp4a f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wne f1_tz7.7 f0_tz7.7 a_wcel a_wi p_pm2.43d f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wne f1_tz7.7 f0_tz7.7 a_wcel p_imp3a f0_tz7.7 a_word f1_tz7.7 a_wtr a_wa f1_tz7.7 f0_tz7.7 a_wcel f1_tz7.7 f0_tz7.7 a_wss f1_tz7.7 f0_tz7.7 a_wne a_wa p_impbid $.
$}

$(Corollary 7.8 of [TakeutiZaring] p. 37.  (Contributed by NM,
     25-Nov-1995.) $)

${
	$v A B  $.
	f0_ordelssne $f class A $.
	f1_ordelssne $f class B $.
	p_ordelssne $p |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> ( A C_ B /\ A =/= B ) ) ) $= f0_ordelssne p_ordtr f1_ordelssne f0_ordelssne p_tz7.7 f0_ordelssne a_word f1_ordelssne a_word f0_ordelssne a_wtr f0_ordelssne f1_ordelssne a_wcel f0_ordelssne f1_ordelssne a_wss f0_ordelssne f1_ordelssne a_wne a_wa a_wb p_sylan2 f1_ordelssne a_word f0_ordelssne a_word f0_ordelssne f1_ordelssne a_wcel f0_ordelssne f1_ordelssne a_wss f0_ordelssne f1_ordelssne a_wne a_wa a_wb p_ancoms $.
$}

$(Corollary 7.8 of [TakeutiZaring] p. 37.  (Contributed by NM,
     17-Jun-1998.) $)

${
	$v A B  $.
	f0_ordelpss $f class A $.
	f1_ordelpss $f class B $.
	p_ordelpss $p |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> A C. B ) ) $= f0_ordelpss f1_ordelpss p_ordelssne f0_ordelpss f1_ordelpss a_df-pss f0_ordelpss a_word f1_ordelpss a_word a_wa f0_ordelpss f1_ordelpss a_wcel f0_ordelpss f1_ordelpss a_wss f0_ordelpss f1_ordelpss a_wne a_wa f0_ordelpss f1_ordelpss a_wpss p_syl6bbr $.
$}

$(For ordinal classes, subclass is equivalent to membership or equality.
     (Contributed by NM, 25-Nov-1995.)  (Proof shortened by Andrew Salmon,
     25-Jul-2011.) $)

${
	$v A B  $.
	f0_ordsseleq $f class A $.
	f1_ordsseleq $f class B $.
	p_ordsseleq $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> ( A e. B \/ A = B ) ) ) $= f0_ordsseleq f1_ordsseleq p_ordelpss f0_ordsseleq a_word f1_ordsseleq a_word a_wa f0_ordsseleq f1_ordsseleq a_wcel f0_ordsseleq f1_ordsseleq a_wpss f0_ordsseleq f1_ordsseleq a_wceq p_orbi1d f0_ordsseleq f1_ordsseleq p_sspss f0_ordsseleq a_word f1_ordsseleq a_word a_wa f0_ordsseleq f1_ordsseleq a_wcel f0_ordsseleq f1_ordsseleq a_wceq a_wo f0_ordsseleq f1_ordsseleq a_wpss f0_ordsseleq f1_ordsseleq a_wceq a_wo f0_ordsseleq f1_ordsseleq a_wss p_syl6rbbr $.
$}

$(The intersection of two ordinal classes is ordinal.  Proposition 7.9 of
     [TakeutiZaring] p. 37.  (Contributed by NM, 9-May-1994.) $)

${
	$v A B  $.
	f0_ordin $f class A $.
	f1_ordin $f class B $.
	p_ordin $p |- ( ( Ord A /\ Ord B ) -> Ord ( A i^i B ) ) $= f0_ordin p_ordtr f1_ordin p_ordtr f0_ordin f1_ordin p_trin f0_ordin a_word f0_ordin a_wtr f1_ordin a_wtr f0_ordin f1_ordin a_cin a_wtr f1_ordin a_word p_syl2an f0_ordin f1_ordin p_inss2 f0_ordin f1_ordin a_cin f1_ordin p_trssord f0_ordin f1_ordin a_cin a_wtr f0_ordin f1_ordin a_cin f1_ordin a_wss f1_ordin a_word f0_ordin f1_ordin a_cin a_word p_mp3an2 f0_ordin a_word f1_ordin a_word f0_ordin f1_ordin a_cin a_wtr f0_ordin f1_ordin a_cin a_word p_sylancom $.
$}

$(The intersection of two ordinal numbers is an ordinal number.
       (Contributed by NM, 7-Apr-1995.) $)

${
	$v A B  $.
	$d A  $.
	$d B  $.
	f0_onin $f class A $.
	f1_onin $f class B $.
	p_onin $p |- ( ( A e. On /\ B e. On ) -> ( A i^i B ) e. On ) $= f0_onin p_eloni f1_onin p_eloni f0_onin f1_onin p_ordin f0_onin a_con0 a_wcel f0_onin a_word f1_onin a_word f0_onin f1_onin a_cin a_word f1_onin a_con0 a_wcel p_syl2an f0_onin a_con0 a_wcel f1_onin a_con0 a_wcel p_simpl f0_onin f1_onin a_con0 p_inex1g f0_onin f1_onin a_cin a_cvv p_elong f0_onin a_con0 a_wcel f1_onin a_con0 a_wcel a_wa f0_onin a_con0 a_wcel f0_onin f1_onin a_cin a_cvv a_wcel f0_onin f1_onin a_cin a_con0 a_wcel f0_onin f1_onin a_cin a_word a_wb p_3syl f0_onin a_con0 a_wcel f1_onin a_con0 a_wcel a_wa f0_onin f1_onin a_cin a_con0 a_wcel f0_onin f1_onin a_cin a_word p_mpbird $.
$}

$(A trichotomy law for ordinals.  Proposition 7.10 of [TakeutiZaring]
     p. 38.  (Contributed by NM, 10-May-1994.)  (Proof shortened by Andrew
     Salmon, 25-Jul-2011.) $)

${
	$v A B  $.
	f0_ordtri3or $f class A $.
	f1_ordtri3or $f class B $.
	p_ordtri3or $p |- ( ( Ord A /\ Ord B ) -> ( A e. B \/ A = B \/ B e. A ) ) $= f0_ordtri3or f1_ordtri3or p_ordin f0_ordtri3or f1_ordtri3or a_cin p_ordirr f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_cin a_word f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or f1_ordtri3or a_cin a_wcel a_wn p_syl f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel p_ianor f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or f1_ordtri3or p_elin f0_ordtri3or f1_ordtri3or p_incom f0_ordtri3or f1_ordtri3or a_cin f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or p_eleq1i f0_ordtri3or f1_ordtri3or a_cin f1_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel p_anbi2i f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or f1_ordtri3or a_cin a_wcel f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel f0_ordtri3or f1_ordtri3or a_cin f1_ordtri3or a_wcel a_wa f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel a_wa p_bitri f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel a_wa f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel a_wn f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel a_wn a_wo f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or f1_ordtri3or a_cin a_wcel p_xchnxbir f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or f1_ordtri3or a_cin a_wcel a_wn f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel a_wn f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel a_wn a_wo p_sylib f0_ordtri3or f1_ordtri3or p_ordin f0_ordtri3or f1_ordtri3or p_inss1 f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or p_ordsseleq f0_ordtri3or f1_ordtri3or a_cin a_word f0_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wss f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wceq a_wo p_mpbii f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_cin a_word f0_ordtri3or a_word f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wceq a_wo p_sylan f0_ordtri3or a_word f1_ordtri3or a_word f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wceq a_wo p_anabss1 f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wceq p_ord f0_ordtri3or f1_ordtri3or a_df-ss f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel a_wn f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wceq f0_ordtri3or f1_ordtri3or a_wss p_syl6ibr f1_ordtri3or f0_ordtri3or p_ordin f1_ordtri3or f0_ordtri3or p_inss1 f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or p_ordsseleq f1_ordtri3or f0_ordtri3or a_cin a_word f1_ordtri3or a_word a_wa f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wss f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wceq a_wo p_mpbii f1_ordtri3or a_word f0_ordtri3or a_word a_wa f1_ordtri3or f0_ordtri3or a_cin a_word f1_ordtri3or a_word f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wceq a_wo p_sylan f0_ordtri3or a_word f1_ordtri3or a_word f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wceq a_wo p_anabss4 f0_ordtri3or a_word f1_ordtri3or a_word a_wa f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wceq p_ord f1_ordtri3or f0_ordtri3or a_df-ss f0_ordtri3or a_word f1_ordtri3or a_word a_wa f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel a_wn f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wceq f1_ordtri3or f0_ordtri3or a_wss p_syl6ibr f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel a_wn f0_ordtri3or f1_ordtri3or a_wss f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel a_wn f1_ordtri3or f0_ordtri3or a_wss p_orim12d f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_cin f0_ordtri3or a_wcel a_wn f1_ordtri3or f0_ordtri3or a_cin f1_ordtri3or a_wcel a_wn a_wo f0_ordtri3or f1_ordtri3or a_wss f1_ordtri3or f0_ordtri3or a_wss a_wo p_mpd f0_ordtri3or f1_ordtri3or p_sspsstri f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_wss f1_ordtri3or f0_ordtri3or a_wss a_wo f0_ordtri3or f1_ordtri3or a_wpss f0_ordtri3or f1_ordtri3or a_wceq f1_ordtri3or f0_ordtri3or a_wpss a_w3o p_sylib f0_ordtri3or f1_ordtri3or p_ordelpss f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_wceq p_biidd f1_ordtri3or f0_ordtri3or p_ordelpss f1_ordtri3or a_word f0_ordtri3or a_word f1_ordtri3or f0_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_wpss a_wb p_ancoms f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_wcel f0_ordtri3or f1_ordtri3or a_wpss f0_ordtri3or f1_ordtri3or a_wceq f0_ordtri3or f1_ordtri3or a_wceq f1_ordtri3or f0_ordtri3or a_wcel f1_ordtri3or f0_ordtri3or a_wpss p_3orbi123d f0_ordtri3or a_word f1_ordtri3or a_word a_wa f0_ordtri3or f1_ordtri3or a_wcel f0_ordtri3or f1_ordtri3or a_wceq f1_ordtri3or f0_ordtri3or a_wcel a_w3o f0_ordtri3or f1_ordtri3or a_wpss f0_ordtri3or f1_ordtri3or a_wceq f1_ordtri3or f0_ordtri3or a_wpss a_w3o p_mpbird $.
$}

$(A trichotomy law for ordinals.  (Contributed by NM, 25-Mar-1995.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B  $.
	f0_ordtri1 $f class A $.
	f1_ordtri1 $f class B $.
	p_ordtri1 $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> -. B e. A ) ) $= f0_ordtri1 f1_ordtri1 p_ordsseleq f0_ordtri1 f1_ordtri1 p_ordn2lp f0_ordtri1 f1_ordtri1 a_wcel f1_ordtri1 f0_ordtri1 a_wcel p_imnan f0_ordtri1 a_word f0_ordtri1 f1_ordtri1 a_wcel f1_ordtri1 f0_ordtri1 a_wcel a_wa a_wn f0_ordtri1 f1_ordtri1 a_wcel f1_ordtri1 f0_ordtri1 a_wcel a_wn a_wi p_sylibr f1_ordtri1 p_ordirr f0_ordtri1 f1_ordtri1 f1_ordtri1 p_eleq2 f0_ordtri1 f1_ordtri1 a_wceq f1_ordtri1 f0_ordtri1 a_wcel f1_ordtri1 f1_ordtri1 a_wcel p_notbid f1_ordtri1 a_word f1_ordtri1 f0_ordtri1 a_wcel a_wn f0_ordtri1 f1_ordtri1 a_wceq f1_ordtri1 f1_ordtri1 a_wcel a_wn p_syl5ibrcom f0_ordtri1 a_word f0_ordtri1 f1_ordtri1 a_wcel f1_ordtri1 f0_ordtri1 a_wcel a_wn f1_ordtri1 a_word f0_ordtri1 f1_ordtri1 a_wceq p_jaao f0_ordtri1 f1_ordtri1 p_ordtri3or f0_ordtri1 f1_ordtri1 a_wcel f0_ordtri1 f1_ordtri1 a_wceq f1_ordtri1 f0_ordtri1 a_wcel a_df-3or f0_ordtri1 a_word f1_ordtri1 a_word a_wa f0_ordtri1 f1_ordtri1 a_wcel f0_ordtri1 f1_ordtri1 a_wceq f1_ordtri1 f0_ordtri1 a_wcel a_w3o f0_ordtri1 f1_ordtri1 a_wcel f0_ordtri1 f1_ordtri1 a_wceq a_wo f1_ordtri1 f0_ordtri1 a_wcel a_wo p_sylib f0_ordtri1 a_word f1_ordtri1 a_word a_wa f0_ordtri1 f1_ordtri1 a_wcel f0_ordtri1 f1_ordtri1 a_wceq a_wo f1_ordtri1 f0_ordtri1 a_wcel p_orcomd f0_ordtri1 a_word f1_ordtri1 a_word a_wa f1_ordtri1 f0_ordtri1 a_wcel f0_ordtri1 f1_ordtri1 a_wcel f0_ordtri1 f1_ordtri1 a_wceq a_wo p_ord f0_ordtri1 a_word f1_ordtri1 a_word a_wa f0_ordtri1 f1_ordtri1 a_wcel f0_ordtri1 f1_ordtri1 a_wceq a_wo f1_ordtri1 f0_ordtri1 a_wcel a_wn p_impbid f0_ordtri1 a_word f1_ordtri1 a_word a_wa f0_ordtri1 f1_ordtri1 a_wss f0_ordtri1 f1_ordtri1 a_wcel f0_ordtri1 f1_ordtri1 a_wceq a_wo f1_ordtri1 f0_ordtri1 a_wcel a_wn p_bitrd $.
$}

$(A trichotomy law for ordinal numbers.  (Contributed by NM, 6-Nov-2003.) $)

${
	$v A B  $.
	f0_ontri1 $f class A $.
	f1_ontri1 $f class B $.
	p_ontri1 $p |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> -. B e. A ) ) $= f0_ontri1 p_eloni f1_ontri1 p_eloni f0_ontri1 f1_ontri1 p_ordtri1 f0_ontri1 a_con0 a_wcel f0_ontri1 a_word f1_ontri1 a_word f0_ontri1 f1_ontri1 a_wss f1_ontri1 f0_ontri1 a_wcel a_wn a_wb f1_ontri1 a_con0 a_wcel p_syl2an $.
$}

$(A trichotomy law for ordinals.  (Contributed by NM, 25-Nov-1995.) $)

${
	$v A B  $.
	f0_ordtri2 $f class A $.
	f1_ordtri2 $f class B $.
	p_ordtri2 $p |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> -. ( A = B \/ B e. A ) ) ) $= f1_ordtri2 f0_ordtri2 p_ordsseleq f1_ordtri2 f0_ordtri2 p_eqcom f1_ordtri2 f0_ordtri2 a_wceq f0_ordtri2 f1_ordtri2 a_wceq f1_ordtri2 f0_ordtri2 a_wcel p_orbi2i f1_ordtri2 f0_ordtri2 a_wcel f0_ordtri2 f1_ordtri2 a_wceq p_orcom f1_ordtri2 f0_ordtri2 a_wcel f1_ordtri2 f0_ordtri2 a_wceq a_wo f1_ordtri2 f0_ordtri2 a_wcel f0_ordtri2 f1_ordtri2 a_wceq a_wo f0_ordtri2 f1_ordtri2 a_wceq f1_ordtri2 f0_ordtri2 a_wcel a_wo p_bitri f1_ordtri2 a_word f0_ordtri2 a_word a_wa f1_ordtri2 f0_ordtri2 a_wss f1_ordtri2 f0_ordtri2 a_wcel f1_ordtri2 f0_ordtri2 a_wceq a_wo f0_ordtri2 f1_ordtri2 a_wceq f1_ordtri2 f0_ordtri2 a_wcel a_wo p_syl6bb f1_ordtri2 f0_ordtri2 p_ordtri1 f1_ordtri2 a_word f0_ordtri2 a_word a_wa f1_ordtri2 f0_ordtri2 a_wss f0_ordtri2 f1_ordtri2 a_wceq f1_ordtri2 f0_ordtri2 a_wcel a_wo f0_ordtri2 f1_ordtri2 a_wcel a_wn p_bitr3d f1_ordtri2 a_word f0_ordtri2 a_word f0_ordtri2 f1_ordtri2 a_wceq f1_ordtri2 f0_ordtri2 a_wcel a_wo f0_ordtri2 f1_ordtri2 a_wcel a_wn a_wb p_ancoms f0_ordtri2 a_word f1_ordtri2 a_word a_wa f0_ordtri2 f1_ordtri2 a_wceq f1_ordtri2 f0_ordtri2 a_wcel a_wo f0_ordtri2 f1_ordtri2 a_wcel p_con2bid $.
$}

$(A trichotomy law for ordinals.  (Contributed by NM, 18-Oct-1995.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B  $.
	f0_ordtri3 $f class A $.
	f1_ordtri3 $f class B $.
	p_ordtri3 $p |- ( ( Ord A /\ Ord B ) -> ( A = B <-> -. ( A e. B \/ B e. A ) ) ) $= f0_ordtri3 p_ordirr f0_ordtri3 f1_ordtri3 f0_ordtri3 p_eleq2 f0_ordtri3 f1_ordtri3 a_wceq f0_ordtri3 f0_ordtri3 a_wcel f0_ordtri3 f1_ordtri3 a_wcel p_notbid f0_ordtri3 a_word f0_ordtri3 f0_ordtri3 a_wcel a_wn f0_ordtri3 f1_ordtri3 a_wceq f0_ordtri3 f1_ordtri3 a_wcel a_wn p_syl5ib f1_ordtri3 p_ordirr f0_ordtri3 f1_ordtri3 f1_ordtri3 p_eleq2 f0_ordtri3 f1_ordtri3 a_wceq f1_ordtri3 f0_ordtri3 a_wcel f1_ordtri3 f1_ordtri3 a_wcel p_notbid f1_ordtri3 a_word f1_ordtri3 f0_ordtri3 a_wcel a_wn f0_ordtri3 f1_ordtri3 a_wceq f1_ordtri3 f1_ordtri3 a_wcel a_wn p_syl5ibr f0_ordtri3 f1_ordtri3 a_wceq f0_ordtri3 a_word f0_ordtri3 f1_ordtri3 a_wcel a_wn f1_ordtri3 a_word f1_ordtri3 f0_ordtri3 a_wcel a_wn p_anim12d f0_ordtri3 f1_ordtri3 a_wceq f0_ordtri3 a_word f1_ordtri3 a_word a_wa f0_ordtri3 f1_ordtri3 a_wcel a_wn f1_ordtri3 f0_ordtri3 a_wcel a_wn a_wa p_com12 f0_ordtri3 f1_ordtri3 a_wcel f1_ordtri3 f0_ordtri3 a_wcel p_pm4.56 f0_ordtri3 a_word f1_ordtri3 a_word a_wa f0_ordtri3 f1_ordtri3 a_wceq f0_ordtri3 f1_ordtri3 a_wcel a_wn f1_ordtri3 f0_ordtri3 a_wcel a_wn a_wa f0_ordtri3 f1_ordtri3 a_wcel f1_ordtri3 f0_ordtri3 a_wcel a_wo a_wn p_syl6ib f0_ordtri3 f1_ordtri3 p_ordtri3or f0_ordtri3 f1_ordtri3 a_wcel f0_ordtri3 f1_ordtri3 a_wceq f1_ordtri3 f0_ordtri3 a_wcel a_df-3or f0_ordtri3 a_word f1_ordtri3 a_word a_wa f0_ordtri3 f1_ordtri3 a_wcel f0_ordtri3 f1_ordtri3 a_wceq f1_ordtri3 f0_ordtri3 a_wcel a_w3o f0_ordtri3 f1_ordtri3 a_wcel f0_ordtri3 f1_ordtri3 a_wceq a_wo f1_ordtri3 f0_ordtri3 a_wcel a_wo p_sylib f0_ordtri3 f1_ordtri3 a_wcel f0_ordtri3 f1_ordtri3 a_wceq f1_ordtri3 f0_ordtri3 a_wcel p_or32 f0_ordtri3 a_word f1_ordtri3 a_word a_wa f0_ordtri3 f1_ordtri3 a_wcel f0_ordtri3 f1_ordtri3 a_wceq a_wo f1_ordtri3 f0_ordtri3 a_wcel a_wo f0_ordtri3 f1_ordtri3 a_wcel f1_ordtri3 f0_ordtri3 a_wcel a_wo f0_ordtri3 f1_ordtri3 a_wceq a_wo p_sylib f0_ordtri3 a_word f1_ordtri3 a_word a_wa f0_ordtri3 f1_ordtri3 a_wcel f1_ordtri3 f0_ordtri3 a_wcel a_wo f0_ordtri3 f1_ordtri3 a_wceq p_ord f0_ordtri3 a_word f1_ordtri3 a_word a_wa f0_ordtri3 f1_ordtri3 a_wceq f0_ordtri3 f1_ordtri3 a_wcel f1_ordtri3 f0_ordtri3 a_wcel a_wo a_wn p_impbid $.
$}

$(A trichotomy law for ordinals.  (Contributed by NM, 1-Nov-2003.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B  $.
	f0_ordtri4 $f class A $.
	f1_ordtri4 $f class B $.
	p_ordtri4 $p |- ( ( Ord A /\ Ord B ) -> ( A = B <-> ( A C_ B /\ -. A e. B ) ) ) $= f0_ordtri4 f1_ordtri4 p_eqss f1_ordtri4 f0_ordtri4 p_ordtri1 f1_ordtri4 a_word f0_ordtri4 a_word f1_ordtri4 f0_ordtri4 a_wss f0_ordtri4 f1_ordtri4 a_wcel a_wn a_wb p_ancoms f0_ordtri4 a_word f1_ordtri4 a_word a_wa f1_ordtri4 f0_ordtri4 a_wss f0_ordtri4 f1_ordtri4 a_wcel a_wn f0_ordtri4 f1_ordtri4 a_wss p_anbi2d f0_ordtri4 f1_ordtri4 a_wceq f0_ordtri4 f1_ordtri4 a_wss f1_ordtri4 f0_ordtri4 a_wss a_wa f0_ordtri4 a_word f1_ordtri4 a_word a_wa f0_ordtri4 f1_ordtri4 a_wss f0_ordtri4 f1_ordtri4 a_wcel a_wn a_wa p_syl5bb $.
$}

$(An ordinal class and its singleton are disjoint.  (Contributed by NM,
     19-May-1998.) $)

${
	$v A  $.
	f0_orddisj $f class A $.
	p_orddisj $p |- ( Ord A -> ( A i^i { A } ) = (/) ) $= f0_orddisj p_ordirr f0_orddisj f0_orddisj p_disjsn f0_orddisj a_word f0_orddisj f0_orddisj a_wcel a_wn f0_orddisj f0_orddisj a_csn a_cin a_c0 a_wceq p_sylibr $.
$}

$(The ordinal class is well-founded.  This lemma is needed for ~ ordon in
       order to eliminate the need for the Axiom of Regularity.  (Contributed
       by NM, 17-May-1994.) $)

${
	$v  $.
	$d x y z  $.
	i0_onfr $f set x $.
	i1_onfr $f set y $.
	i2_onfr $f set z $.
	p_onfr $p |- _E Fr On $= i0_onfr i2_onfr a_con0 p_dfepfr i1_onfr i0_onfr a_sup_set_class p_n0 i2_onfr a_sup_set_class i1_onfr a_sup_set_class i0_onfr a_sup_set_class p_ineq2 i2_onfr a_sup_set_class i1_onfr a_sup_set_class a_wceq i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 p_eqeq1d i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i1_onfr a_sup_set_class i0_onfr a_sup_set_class p_rspcev i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 a_wceq i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex i0_onfr a_sup_set_class a_con0 a_wss p_adantll i0_onfr a_sup_set_class a_con0 i1_onfr a_sup_set_class p_ssel2 i1_onfr a_sup_set_class p_eloni i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i1_onfr a_sup_set_class a_con0 a_wcel i1_onfr a_sup_set_class a_word p_syl i1_onfr a_sup_set_class p_ordfr i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i1_onfr a_sup_set_class a_word i1_onfr a_sup_set_class a_cep a_wfr p_syl i0_onfr a_sup_set_class i1_onfr a_sup_set_class p_inss2 i0_onfr p_vex i0_onfr a_sup_set_class i1_onfr a_sup_set_class p_inex1 i2_onfr i1_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin p_epfrc i1_onfr a_sup_set_class a_cep a_wfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i1_onfr a_sup_set_class a_wss i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 a_wne i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wrex p_mp3an2 i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i1_onfr a_sup_set_class a_cep a_wfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 a_wne i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wrex p_sylan i0_onfr a_sup_set_class i1_onfr a_sup_set_class i2_onfr a_sup_set_class p_inass i0_onfr a_sup_set_class a_con0 i1_onfr a_sup_set_class p_ssel2 i1_onfr a_sup_set_class p_eloni i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i1_onfr a_sup_set_class a_con0 a_wcel i1_onfr a_sup_set_class a_word p_syl i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i1_onfr a_sup_set_class a_word i2_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wcel p_adantr i0_onfr a_sup_set_class i1_onfr a_sup_set_class p_inss2 i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i2_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wcel p_simpr i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i2_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wcel a_wa i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i1_onfr a_sup_set_class i2_onfr a_sup_set_class p_sseldi i1_onfr a_sup_set_class i2_onfr a_sup_set_class p_ordelss i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i2_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wcel a_wa i1_onfr a_sup_set_class a_word i2_onfr a_sup_set_class i1_onfr a_sup_set_class a_wcel i2_onfr a_sup_set_class i1_onfr a_sup_set_class a_wss p_syl2anc i2_onfr a_sup_set_class i1_onfr a_sup_set_class p_dfss1 i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i2_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wcel a_wa i2_onfr a_sup_set_class i1_onfr a_sup_set_class a_wss i1_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class a_wceq p_sylib i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i2_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wcel a_wa i1_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class i0_onfr a_sup_set_class p_ineq2d i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i2_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wcel a_wa i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class a_cin i0_onfr a_sup_set_class i1_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_cin i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin p_syl5eq i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i2_onfr a_sup_set_class i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wcel a_wa i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class a_cin i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 p_eqeq1d i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class a_cin a_c0 a_wceq i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin p_rexbidva i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wrex i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wrex a_wb i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 a_wne p_adantr i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 a_wne a_wa i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wrex i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wrex p_mpbid i0_onfr a_sup_set_class i1_onfr a_sup_set_class p_inss1 i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i0_onfr a_sup_set_class p_ssrexv i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin i0_onfr a_sup_set_class a_wss i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wrex i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex a_wi a_ax-mp i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 a_wne a_wa i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_wrex i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex p_syl i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel a_wa i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex i0_onfr a_sup_set_class i1_onfr a_sup_set_class a_cin a_c0 p_pm2.61dane i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex p_ex i0_onfr a_sup_set_class a_con0 a_wss i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex i1_onfr p_exlimdv i0_onfr a_sup_set_class a_c0 a_wne i1_onfr a_sup_set_class i0_onfr a_sup_set_class a_wcel i1_onfr a_wex i0_onfr a_sup_set_class a_con0 a_wss i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex p_syl5bi i0_onfr a_sup_set_class a_con0 a_wss i0_onfr a_sup_set_class a_c0 a_wne i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex p_imp a_con0 a_cep a_wfr i0_onfr a_sup_set_class a_con0 a_wss i0_onfr a_sup_set_class a_c0 a_wne a_wa i0_onfr a_sup_set_class i2_onfr a_sup_set_class a_cin a_c0 a_wceq i2_onfr i0_onfr a_sup_set_class a_wrex a_wi i0_onfr p_mpgbir $.
$}

$(Relationship between membership and proper subset of an ordinal number.
     (Contributed by NM, 15-Sep-1995.) $)

${
	$v A B  $.
	f0_onelpss $f class A $.
	f1_onelpss $f class B $.
	p_onelpss $p |- ( ( A e. On /\ B e. On ) -> ( A e. B <-> ( A C_ B /\ A =/= B ) ) ) $= f0_onelpss p_eloni f1_onelpss p_eloni f0_onelpss f1_onelpss p_ordelssne f0_onelpss a_con0 a_wcel f0_onelpss a_word f1_onelpss a_word f0_onelpss f1_onelpss a_wcel f0_onelpss f1_onelpss a_wss f0_onelpss f1_onelpss a_wne a_wa a_wb f1_onelpss a_con0 a_wcel p_syl2an $.
$}

$(Relationship between subset and membership of an ordinal number.
     (Contributed by NM, 15-Sep-1995.) $)

${
	$v A B  $.
	f0_onsseleq $f class A $.
	f1_onsseleq $f class B $.
	p_onsseleq $p |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> ( A e. B \/ A = B ) ) ) $= f0_onsseleq p_eloni f1_onsseleq p_eloni f0_onsseleq f1_onsseleq p_ordsseleq f0_onsseleq a_con0 a_wcel f0_onsseleq a_word f1_onsseleq a_word f0_onsseleq f1_onsseleq a_wss f0_onsseleq f1_onsseleq a_wcel f0_onsseleq f1_onsseleq a_wceq a_wo a_wb f1_onsseleq a_con0 a_wcel p_syl2an $.
$}

$(An element of an ordinal number is a subset of the number.  (Contributed
     by NM, 5-Jun-1994.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B  $.
	f0_onelss $f class A $.
	f1_onelss $f class B $.
	p_onelss $p |- ( A e. On -> ( B e. A -> B C_ A ) ) $= f0_onelss p_eloni f0_onelss f1_onelss p_ordelss f0_onelss a_word f1_onelss f0_onelss a_wcel f1_onelss f0_onelss a_wss p_ex f0_onelss a_con0 a_wcel f0_onelss a_word f1_onelss f0_onelss a_wcel f1_onelss f0_onelss a_wss a_wi p_syl $.
$}

$(Transitive law for ordinal classes.  (Contributed by NM, 12-Dec-2004.) $)

${
	$v A B C  $.
	f0_ordtr1 $f class A $.
	f1_ordtr1 $f class B $.
	f2_ordtr1 $f class C $.
	p_ordtr1 $p |- ( Ord C -> ( ( A e. B /\ B e. C ) -> A e. C ) ) $= f2_ordtr1 p_ordtr f2_ordtr1 f0_ordtr1 f1_ordtr1 p_trel f2_ordtr1 a_word f2_ordtr1 a_wtr f0_ordtr1 f1_ordtr1 a_wcel f1_ordtr1 f2_ordtr1 a_wcel a_wa f0_ordtr1 f2_ordtr1 a_wcel a_wi p_syl $.
$}

$(Transitive law for ordinal classes.  (Contributed by NM, 12-Dec-2004.)
     (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B C  $.
	f0_ordtr2 $f class A $.
	f1_ordtr2 $f class B $.
	f2_ordtr2 $f class C $.
	p_ordtr2 $p |- ( ( Ord A /\ Ord C ) -> ( ( A C_ B /\ B e. C ) -> A e. C ) ) $= f2_ordtr2 f1_ordtr2 p_ordelord f2_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 a_word p_ex f2_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 a_word p_ancld f2_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 a_word a_wa p_anc2li f1_ordtr2 f2_ordtr2 p_ordelpss f1_ordtr2 a_word f2_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 f2_ordtr2 a_wpss a_wb p_ancoms f0_ordtr2 f1_ordtr2 f2_ordtr2 p_sspsstr f0_ordtr2 f1_ordtr2 a_wss f1_ordtr2 f2_ordtr2 a_wpss f0_ordtr2 f2_ordtr2 a_wpss p_expcom f2_ordtr2 a_word f1_ordtr2 a_word a_wa f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 f2_ordtr2 a_wpss f0_ordtr2 f1_ordtr2 a_wss f0_ordtr2 f2_ordtr2 a_wpss a_wi p_syl6bi f2_ordtr2 a_word f1_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f0_ordtr2 f1_ordtr2 a_wss f0_ordtr2 f2_ordtr2 a_wpss a_wi a_wi p_ex f2_ordtr2 a_word f1_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f0_ordtr2 f1_ordtr2 a_wss f0_ordtr2 f2_ordtr2 a_wpss a_wi p_com23 f2_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 a_word f0_ordtr2 f1_ordtr2 a_wss f0_ordtr2 f2_ordtr2 a_wpss a_wi p_imp32 f2_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 a_word a_wa a_wa f0_ordtr2 f1_ordtr2 a_wss f0_ordtr2 f2_ordtr2 a_wpss p_com12 f2_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f2_ordtr2 a_word f1_ordtr2 f2_ordtr2 a_wcel f1_ordtr2 a_word a_wa a_wa f0_ordtr2 f1_ordtr2 a_wss f0_ordtr2 f2_ordtr2 a_wpss p_syl9 f2_ordtr2 a_word f0_ordtr2 f1_ordtr2 a_wss f1_ordtr2 f2_ordtr2 a_wcel f0_ordtr2 f2_ordtr2 a_wpss p_imp3a f2_ordtr2 a_word f0_ordtr2 f1_ordtr2 a_wss f1_ordtr2 f2_ordtr2 a_wcel a_wa f0_ordtr2 f2_ordtr2 a_wpss a_wi f0_ordtr2 a_word p_adantl f0_ordtr2 f2_ordtr2 p_ordelpss f0_ordtr2 a_word f2_ordtr2 a_word a_wa f0_ordtr2 f1_ordtr2 a_wss f1_ordtr2 f2_ordtr2 a_wcel a_wa f0_ordtr2 f2_ordtr2 a_wpss f0_ordtr2 f2_ordtr2 a_wcel p_sylibrd $.
$}

$(Transitive law for ordinal classes.  (Contributed by Mario Carneiro,
     30-Dec-2014.) $)

${
	$v A B C  $.
	f0_ordtr3 $f class A $.
	f1_ordtr3 $f class B $.
	f2_ordtr3 $f class C $.
	p_ordtr3 $p |- ( ( Ord B /\ Ord C ) -> ( A e. B -> ( A e. C \/ C e. B ) ) ) $= f1_ordtr3 a_word f2_ordtr3 a_word f0_ordtr3 f1_ordtr3 a_wcel p_simplr f1_ordtr3 f0_ordtr3 p_ordelord f1_ordtr3 a_word f0_ordtr3 f1_ordtr3 a_wcel f0_ordtr3 a_word f2_ordtr3 a_word p_adantlr f2_ordtr3 f0_ordtr3 p_ordtri1 f1_ordtr3 a_word f2_ordtr3 a_word a_wa f0_ordtr3 f1_ordtr3 a_wcel a_wa f2_ordtr3 a_word f0_ordtr3 a_word f2_ordtr3 f0_ordtr3 a_wss f0_ordtr3 f2_ordtr3 a_wcel a_wn a_wb p_syl2anc f2_ordtr3 f0_ordtr3 f1_ordtr3 p_ordtr2 f2_ordtr3 a_word f1_ordtr3 a_word f2_ordtr3 f0_ordtr3 a_wss f0_ordtr3 f1_ordtr3 a_wcel a_wa f2_ordtr3 f1_ordtr3 a_wcel a_wi p_ancoms f1_ordtr3 a_word f2_ordtr3 a_word a_wa f2_ordtr3 f0_ordtr3 a_wss f0_ordtr3 f1_ordtr3 a_wcel f2_ordtr3 f1_ordtr3 a_wcel p_ancomsd f1_ordtr3 a_word f2_ordtr3 a_word a_wa f0_ordtr3 f1_ordtr3 a_wcel f2_ordtr3 f0_ordtr3 a_wss f2_ordtr3 f1_ordtr3 a_wcel p_expdimp f1_ordtr3 a_word f2_ordtr3 a_word a_wa f0_ordtr3 f1_ordtr3 a_wcel a_wa f0_ordtr3 f2_ordtr3 a_wcel a_wn f2_ordtr3 f0_ordtr3 a_wss f2_ordtr3 f1_ordtr3 a_wcel p_sylbird f1_ordtr3 a_word f2_ordtr3 a_word a_wa f0_ordtr3 f1_ordtr3 a_wcel a_wa f0_ordtr3 f2_ordtr3 a_wcel f2_ordtr3 f1_ordtr3 a_wcel p_orrd f1_ordtr3 a_word f2_ordtr3 a_word a_wa f0_ordtr3 f1_ordtr3 a_wcel f0_ordtr3 f2_ordtr3 a_wcel f2_ordtr3 f1_ordtr3 a_wcel a_wo p_ex $.
$}

$(Transitive law for ordinal numbers.  Theorem 7M(b) of [Enderton] p. 192.
     (Contributed by NM, 11-Aug-1994.) $)

${
	$v A B C  $.
	f0_ontr1 $f class A $.
	f1_ontr1 $f class B $.
	f2_ontr1 $f class C $.
	p_ontr1 $p |- ( C e. On -> ( ( A e. B /\ B e. C ) -> A e. C ) ) $= f2_ontr1 p_eloni f0_ontr1 f1_ontr1 f2_ontr1 p_ordtr1 f2_ontr1 a_con0 a_wcel f2_ontr1 a_word f0_ontr1 f1_ontr1 a_wcel f1_ontr1 f2_ontr1 a_wcel a_wa f0_ontr1 f2_ontr1 a_wcel a_wi p_syl $.
$}

$(Transitive law for ordinal numbers.  Exercise 3 of [TakeutiZaring] p. 40.
     (Contributed by NM, 6-Nov-2003.) $)

${
	$v A B C  $.
	f0_ontr2 $f class A $.
	f1_ontr2 $f class B $.
	f2_ontr2 $f class C $.
	p_ontr2 $p |- ( ( A e. On /\ C e. On ) -> ( ( A C_ B /\ B e. C ) -> A e. C ) ) $= f0_ontr2 p_eloni f2_ontr2 p_eloni f0_ontr2 f1_ontr2 f2_ontr2 p_ordtr2 f0_ontr2 a_con0 a_wcel f0_ontr2 a_word f2_ontr2 a_word f0_ontr2 f1_ontr2 a_wss f1_ontr2 f2_ontr2 a_wcel a_wa f0_ontr2 f2_ontr2 a_wcel a_wi f2_ontr2 a_con0 a_wcel p_syl2an $.
$}

$(The union of an ordinal stays the same if a subset equal to one of its
       elements is removed.  (Contributed by NM, 10-Dec-2004.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_ordunidif $f class A $.
	f1_ordunidif $f class B $.
	i0_ordunidif $f set x $.
	i1_ordunidif $f set y $.
	p_ordunidif $p |- ( ( Ord A /\ B e. A ) -> U. ( A \ B ) = U. A ) $= f0_ordunidif f1_ordunidif p_ordelon f1_ordunidif i0_ordunidif a_sup_set_class p_onelss f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa f1_ordunidif a_con0 a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wss a_wi p_syl f0_ordunidif f1_ordunidif p_ordelon f1_ordunidif p_eloni f1_ordunidif p_ordirr f1_ordunidif a_con0 a_wcel f1_ordunidif a_word f1_ordunidif f1_ordunidif a_wcel a_wn p_syl f1_ordunidif f0_ordunidif f1_ordunidif p_eldif f1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wcel f1_ordunidif f0_ordunidif a_wcel f1_ordunidif f1_ordunidif a_wcel a_wn p_simplbi2 f1_ordunidif a_con0 a_wcel f1_ordunidif f1_ordunidif a_wcel a_wn f1_ordunidif f0_ordunidif a_wcel f1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wcel p_syl5 f1_ordunidif f0_ordunidif a_wcel f1_ordunidif a_con0 a_wcel f1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wcel a_wi f0_ordunidif a_word p_adantl f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa f1_ordunidif a_con0 a_wcel f1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wcel p_mpd f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa i0_ordunidif a_sup_set_class f1_ordunidif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wss f1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wcel p_jctild f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa i0_ordunidif a_sup_set_class f1_ordunidif a_wcel f1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wss a_wa a_wi i0_ordunidif a_sup_set_class f0_ordunidif a_wcel p_adantr i1_ordunidif a_sup_set_class f1_ordunidif i0_ordunidif a_sup_set_class p_sseq2 i0_ordunidif a_sup_set_class i1_ordunidif a_sup_set_class a_wss i0_ordunidif a_sup_set_class f1_ordunidif a_wss i1_ordunidif f1_ordunidif f0_ordunidif f1_ordunidif a_cdif p_rspcev f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa i0_ordunidif a_sup_set_class f0_ordunidif a_wcel a_wa i0_ordunidif a_sup_set_class f1_ordunidif a_wcel f1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wss a_wa i0_ordunidif a_sup_set_class i1_ordunidif a_sup_set_class a_wss i1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wrex p_syl6 i0_ordunidif a_sup_set_class f0_ordunidif f1_ordunidif p_eldif i0_ordunidif a_sup_set_class f0_ordunidif f1_ordunidif a_cdif a_wcel i0_ordunidif a_sup_set_class f0_ordunidif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wcel a_wn a_wa p_biimpri i0_ordunidif a_sup_set_class p_ssid i0_ordunidif a_sup_set_class f0_ordunidif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wcel a_wn a_wa i0_ordunidif a_sup_set_class f0_ordunidif f1_ordunidif a_cdif a_wcel i0_ordunidif a_sup_set_class i0_ordunidif a_sup_set_class a_wss p_jctir i0_ordunidif a_sup_set_class f0_ordunidif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wcel a_wn i0_ordunidif a_sup_set_class f0_ordunidif f1_ordunidif a_cdif a_wcel i0_ordunidif a_sup_set_class i0_ordunidif a_sup_set_class a_wss a_wa p_ex i1_ordunidif a_sup_set_class i0_ordunidif a_sup_set_class i0_ordunidif a_sup_set_class p_sseq2 i0_ordunidif a_sup_set_class i1_ordunidif a_sup_set_class a_wss i0_ordunidif a_sup_set_class i0_ordunidif a_sup_set_class a_wss i1_ordunidif i0_ordunidif a_sup_set_class f0_ordunidif f1_ordunidif a_cdif p_rspcev i0_ordunidif a_sup_set_class f0_ordunidif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wcel a_wn i0_ordunidif a_sup_set_class f0_ordunidif f1_ordunidif a_cdif a_wcel i0_ordunidif a_sup_set_class i0_ordunidif a_sup_set_class a_wss a_wa i0_ordunidif a_sup_set_class i1_ordunidif a_sup_set_class a_wss i1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wrex p_syl6 i0_ordunidif a_sup_set_class f0_ordunidif a_wcel i0_ordunidif a_sup_set_class f1_ordunidif a_wcel a_wn i0_ordunidif a_sup_set_class i1_ordunidif a_sup_set_class a_wss i1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wrex a_wi f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa p_adantl f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa i0_ordunidif a_sup_set_class f0_ordunidif a_wcel a_wa i0_ordunidif a_sup_set_class f1_ordunidif a_wcel i0_ordunidif a_sup_set_class i1_ordunidif a_sup_set_class a_wss i1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wrex p_pm2.61d f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa i0_ordunidif a_sup_set_class i1_ordunidif a_sup_set_class a_wss i1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wrex i0_ordunidif f0_ordunidif p_ralrimiva i0_ordunidif i1_ordunidif f0_ordunidif f1_ordunidif p_unidif f0_ordunidif a_word f1_ordunidif f0_ordunidif a_wcel a_wa i0_ordunidif a_sup_set_class i1_ordunidif a_sup_set_class a_wss i1_ordunidif f0_ordunidif f1_ordunidif a_cdif a_wrex i0_ordunidif f0_ordunidif a_wral f0_ordunidif f1_ordunidif a_cdif a_cuni f0_ordunidif a_cuni a_wceq p_syl $.
$}

$(If ` B ` is smaller than ` A ` , then it equals the intersection of the
       difference.  Exercise 11 in [TakeutiZaring] p. 44.  (Contributed by
       Andrew Salmon, 14-Nov-2011.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_ordintdif $f class A $.
	f1_ordintdif $f class B $.
	i0_ordintdif $f set x $.
	p_ordintdif $p |- ( ( Ord A /\ Ord B /\ ( A \ B ) =/= (/) ) -> B = |^| ( A \ B ) ) $= f0_ordintdif f1_ordintdif p_ssdif0 f0_ordintdif f1_ordintdif a_wss f0_ordintdif f1_ordintdif a_cdif a_c0 p_necon3bbii i0_ordintdif f0_ordintdif f1_ordintdif p_dfdif2 f0_ordintdif f1_ordintdif a_cdif i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn i0_ordintdif f0_ordintdif a_crab p_inteqi f0_ordintdif f1_ordintdif p_ordtri1 f0_ordintdif a_word f1_ordintdif a_word a_wa f0_ordintdif f1_ordintdif a_wss f1_ordintdif f0_ordintdif a_wcel p_con2bid f0_ordintdif i0_ordintdif a_sup_set_class p_ordelord f1_ordintdif i0_ordintdif a_sup_set_class p_ordtri1 f1_ordintdif a_word i0_ordintdif a_sup_set_class a_word f1_ordintdif i0_ordintdif a_sup_set_class a_wss i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn a_wb p_ancoms f0_ordintdif a_word i0_ordintdif a_sup_set_class f0_ordintdif a_wcel a_wa i0_ordintdif a_sup_set_class a_word f1_ordintdif a_word f1_ordintdif i0_ordintdif a_sup_set_class a_wss i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn a_wb p_sylan f0_ordintdif a_word i0_ordintdif a_sup_set_class f0_ordintdif a_wcel f1_ordintdif a_word f1_ordintdif i0_ordintdif a_sup_set_class a_wss i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn a_wb p_an32s f0_ordintdif a_word f1_ordintdif a_word a_wa i0_ordintdif a_sup_set_class f0_ordintdif a_wcel a_wa f1_ordintdif i0_ordintdif a_sup_set_class a_wss i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn p_bicomd f0_ordintdif a_word f1_ordintdif a_word a_wa i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn f1_ordintdif i0_ordintdif a_sup_set_class a_wss i0_ordintdif f0_ordintdif p_rabbidva f0_ordintdif a_word f1_ordintdif a_word a_wa i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn i0_ordintdif f0_ordintdif a_crab f1_ordintdif i0_ordintdif a_sup_set_class a_wss i0_ordintdif f0_ordintdif a_crab p_inteqd i0_ordintdif f1_ordintdif f0_ordintdif p_intmin f0_ordintdif a_word f1_ordintdif a_word a_wa f1_ordintdif f0_ordintdif a_wcel i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn i0_ordintdif f0_ordintdif a_crab a_cint f1_ordintdif i0_ordintdif a_sup_set_class a_wss i0_ordintdif f0_ordintdif a_crab a_cint f1_ordintdif p_sylan9eq f0_ordintdif a_word f1_ordintdif a_word a_wa f1_ordintdif f0_ordintdif a_wcel i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn i0_ordintdif f0_ordintdif a_crab a_cint f1_ordintdif a_wceq p_ex f0_ordintdif a_word f1_ordintdif a_word a_wa f0_ordintdif f1_ordintdif a_wss a_wn f1_ordintdif f0_ordintdif a_wcel i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn i0_ordintdif f0_ordintdif a_crab a_cint f1_ordintdif a_wceq p_sylbird f0_ordintdif a_word f1_ordintdif a_word f0_ordintdif f1_ordintdif a_wss a_wn i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn i0_ordintdif f0_ordintdif a_crab a_cint f1_ordintdif a_wceq p_3impia f0_ordintdif a_word f1_ordintdif a_word f0_ordintdif f1_ordintdif a_wss a_wn a_w3a f0_ordintdif f1_ordintdif a_cdif a_cint i0_ordintdif a_sup_set_class f1_ordintdif a_wcel a_wn i0_ordintdif f0_ordintdif a_crab a_cint f1_ordintdif p_syl5req f0_ordintdif f1_ordintdif a_cdif a_c0 a_wne f0_ordintdif a_word f1_ordintdif a_word f0_ordintdif f1_ordintdif a_wss a_wn f1_ordintdif f0_ordintdif f1_ordintdif a_cdif a_cint a_wceq p_syl3an3br $.
$}

$(If a property is true for an ordinal number, then the minimum ordinal
       number for which it is true is smaller or equal.  Theorem Schema 61 of
       [Suppes] p. 228.  (Contributed by NM, 3-Oct-2003.) $)

${
	$v ph ps x A  $.
	$d x ps  $.
	$d x A  $.
	f0_onintss $f wff ph $.
	f1_onintss $f wff ps $.
	f2_onintss $f set x $.
	f3_onintss $f class A $.
	e0_onintss $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_onintss $p |- ( A e. On -> ( ps -> |^| { x e. On | ph } C_ A ) ) $= e0_onintss f0_onintss f1_onintss f2_onintss f3_onintss a_con0 p_intminss f3_onintss a_con0 a_wcel f1_onintss f0_onintss f2_onintss a_con0 a_crab a_cint f3_onintss a_wss p_ex $.
$}

$(A way to show that an ordinal number equals the minimum of a collection
       of ordinal numbers: it must be in the collection, and it must not be
       larger than any member of the collection.  (Contributed by NM,
       14-Nov-2003.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_oneqmini $f set x $.
	f1_oneqmini $f class A $.
	f2_oneqmini $f class B $.
	p_oneqmini $p |- ( B C_ On -> ( ( A e. B /\ A. x e. A -. x e. B ) -> A = |^| B ) ) $= f0_oneqmini f1_oneqmini f2_oneqmini p_ssint f2_oneqmini a_con0 f1_oneqmini p_ssel f2_oneqmini a_con0 f0_oneqmini a_sup_set_class p_ssel f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel f1_oneqmini a_con0 a_wcel f0_oneqmini a_sup_set_class f2_oneqmini a_wcel f0_oneqmini a_sup_set_class a_con0 a_wcel p_anim12d f1_oneqmini f0_oneqmini a_sup_set_class p_ontri1 f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wa f1_oneqmini a_con0 a_wcel f0_oneqmini a_sup_set_class a_con0 a_wcel a_wa f1_oneqmini f0_oneqmini a_sup_set_class a_wss f0_oneqmini a_sup_set_class f1_oneqmini a_wcel a_wn a_wb p_syl6 f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel f0_oneqmini a_sup_set_class f2_oneqmini a_wcel f1_oneqmini f0_oneqmini a_sup_set_class a_wss f0_oneqmini a_sup_set_class f1_oneqmini a_wcel a_wn a_wb p_expdimp f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel a_wa f0_oneqmini a_sup_set_class f2_oneqmini a_wcel f1_oneqmini f0_oneqmini a_sup_set_class a_wss f0_oneqmini a_sup_set_class f1_oneqmini a_wcel a_wn p_pm5.74d f0_oneqmini a_sup_set_class f2_oneqmini a_wcel f0_oneqmini a_sup_set_class f1_oneqmini a_wcel p_con2b f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel a_wa f0_oneqmini a_sup_set_class f2_oneqmini a_wcel f1_oneqmini f0_oneqmini a_sup_set_class a_wss a_wi f0_oneqmini a_sup_set_class f2_oneqmini a_wcel f0_oneqmini a_sup_set_class f1_oneqmini a_wcel a_wn a_wi f0_oneqmini a_sup_set_class f1_oneqmini a_wcel f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wn a_wi p_syl6bb f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel a_wa f1_oneqmini f0_oneqmini a_sup_set_class a_wss f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wn f0_oneqmini f2_oneqmini f1_oneqmini p_ralbidv2 f1_oneqmini f2_oneqmini a_cint a_wss f1_oneqmini f0_oneqmini a_sup_set_class a_wss f0_oneqmini f2_oneqmini a_wral f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel a_wa f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wn f0_oneqmini f1_oneqmini a_wral p_syl5bb f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel a_wa f1_oneqmini f2_oneqmini a_cint a_wss f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wn f0_oneqmini f1_oneqmini a_wral p_biimprd f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wn f0_oneqmini f1_oneqmini a_wral f1_oneqmini f2_oneqmini a_cint a_wss p_expimpd f1_oneqmini f2_oneqmini p_intss1 f1_oneqmini f2_oneqmini a_wcel f2_oneqmini a_cint f1_oneqmini a_wss a_wi f2_oneqmini a_con0 a_wss p_a1i f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel f2_oneqmini a_cint f1_oneqmini a_wss f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wn f0_oneqmini f1_oneqmini a_wral p_adantrd f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wn f0_oneqmini f1_oneqmini a_wral a_wa f1_oneqmini f2_oneqmini a_cint a_wss f2_oneqmini a_cint f1_oneqmini a_wss p_jcad f1_oneqmini f2_oneqmini a_cint p_eqss f2_oneqmini a_con0 a_wss f1_oneqmini f2_oneqmini a_wcel f0_oneqmini a_sup_set_class f2_oneqmini a_wcel a_wn f0_oneqmini f1_oneqmini a_wral a_wa f1_oneqmini f2_oneqmini a_cint a_wss f2_oneqmini a_cint f1_oneqmini a_wss a_wa f1_oneqmini f2_oneqmini a_cint a_wceq p_syl6ibr $.
$}

$(The empty set is an ordinal class.  (Contributed by NM, 11-May-1994.) $)

${
	$v  $.
	p_ord0 $p |- Ord (/) $= p_tr0 a_cep p_we0 a_c0 a_df-ord a_c0 a_word a_c0 a_wtr a_c0 a_cep a_wwe p_mpbir2an $.
$}

$(The empty set is an ordinal number.  Corollary 7N(b) of [Enderton]
     p. 193.  (Contributed by NM, 17-Sep-1993.) $)

${
	$v  $.
	p_0elon $p |- (/) e. On $= p_ord0 p_0ex a_c0 p_elon a_c0 a_con0 a_wcel a_c0 a_word p_mpbir $.
$}

$(A non-empty ordinal contains the empty set.  (Contributed by NM,
     25-Nov-1995.) $)

${
	$v A  $.
	f0_ord0eln0 $f class A $.
	p_ord0eln0 $p |- ( Ord A -> ( (/) e. A <-> A =/= (/) ) ) $= f0_ord0eln0 a_c0 p_ne0i f0_ord0eln0 a_c0 a_df-ne p_ord0 f0_ord0eln0 p_noel f0_ord0eln0 a_c0 p_ordtri2 f0_ord0eln0 a_word a_c0 a_word a_wa f0_ord0eln0 a_c0 a_wcel f0_ord0eln0 a_c0 a_wceq a_c0 f0_ord0eln0 a_wcel a_wo p_con2bid f0_ord0eln0 a_word a_c0 a_word a_wa f0_ord0eln0 a_c0 a_wceq a_c0 f0_ord0eln0 a_wcel a_wo f0_ord0eln0 a_c0 a_wcel a_wn p_mpbiri f0_ord0eln0 a_word a_c0 a_word f0_ord0eln0 a_c0 a_wceq a_c0 f0_ord0eln0 a_wcel a_wo p_mpan2 f0_ord0eln0 a_word f0_ord0eln0 a_c0 a_wceq a_c0 f0_ord0eln0 a_wcel p_ord f0_ord0eln0 a_c0 a_wne f0_ord0eln0 a_c0 a_wceq a_wn f0_ord0eln0 a_word a_c0 f0_ord0eln0 a_wcel p_syl5bi f0_ord0eln0 a_word a_c0 f0_ord0eln0 a_wcel f0_ord0eln0 a_c0 a_wne p_impbid2 $.
$}

$(An ordinal number contains zero iff it is nonzero.  (Contributed by NM,
     6-Dec-2004.) $)

${
	$v A  $.
	f0_on0eln0 $f class A $.
	p_on0eln0 $p |- ( A e. On -> ( (/) e. A <-> A =/= (/) ) ) $= f0_on0eln0 p_eloni f0_on0eln0 p_ord0eln0 f0_on0eln0 a_con0 a_wcel f0_on0eln0 a_word a_c0 f0_on0eln0 a_wcel f0_on0eln0 a_c0 a_wne a_wb p_syl $.
$}

$(An alternate definition of a limit ordinal.  (Contributed by NM,
     4-Nov-2004.) $)

${
	$v A  $.
	f0_dflim2 $f class A $.
	p_dflim2 $p |- ( Lim A <-> ( Ord A /\ (/) e. A /\ A = U. A ) ) $= f0_dflim2 a_df-lim f0_dflim2 p_ord0eln0 f0_dflim2 a_word a_c0 f0_dflim2 a_wcel f0_dflim2 a_c0 a_wne f0_dflim2 f0_dflim2 a_cuni a_wceq p_anbi1d f0_dflim2 a_word a_c0 f0_dflim2 a_wcel f0_dflim2 f0_dflim2 a_cuni a_wceq a_wa f0_dflim2 a_c0 a_wne f0_dflim2 f0_dflim2 a_cuni a_wceq a_wa p_pm5.32i f0_dflim2 a_word a_c0 f0_dflim2 a_wcel f0_dflim2 f0_dflim2 a_cuni a_wceq p_3anass f0_dflim2 a_word f0_dflim2 a_c0 a_wne f0_dflim2 f0_dflim2 a_cuni a_wceq p_3anass f0_dflim2 a_word a_c0 f0_dflim2 a_wcel f0_dflim2 f0_dflim2 a_cuni a_wceq a_wa a_wa f0_dflim2 a_word f0_dflim2 a_c0 a_wne f0_dflim2 f0_dflim2 a_cuni a_wceq a_wa a_wa f0_dflim2 a_word a_c0 f0_dflim2 a_wcel f0_dflim2 f0_dflim2 a_cuni a_wceq a_w3a f0_dflim2 a_word f0_dflim2 a_c0 a_wne f0_dflim2 f0_dflim2 a_cuni a_wceq a_w3a p_3bitr4i f0_dflim2 a_wlim f0_dflim2 a_word f0_dflim2 a_c0 a_wne f0_dflim2 f0_dflim2 a_cuni a_wceq a_w3a f0_dflim2 a_word a_c0 f0_dflim2 a_wcel f0_dflim2 f0_dflim2 a_cuni a_wceq a_w3a p_bitr4i $.
$}

$(The intersection of the class of ordinal numbers is the empty set.
     (Contributed by NM, 20-Oct-2003.) $)

${
	$v  $.
	p_inton $p |- |^| On = (/) $= p_0elon a_con0 p_int0el a_c0 a_con0 a_wcel a_con0 a_cint a_c0 a_wceq a_ax-mp $.
$}

$(The empty set is not a limit ordinal.  (Contributed by NM, 24-Mar-1995.)
     (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v  $.
	p_nlim0 $p |- -. Lim (/) $= a_c0 p_noel a_c0 a_word a_c0 a_c0 a_wcel a_c0 a_c0 a_cuni a_wceq p_simp2 a_c0 a_word a_c0 a_c0 a_wcel a_c0 a_c0 a_cuni a_wceq a_w3a a_c0 a_c0 a_wcel p_mto a_c0 p_dflim2 a_c0 a_wlim a_c0 a_word a_c0 a_c0 a_wcel a_c0 a_c0 a_cuni a_wceq a_w3a p_mtbir $.
$}

$(A limit ordinal is ordinal.  (Contributed by NM, 4-May-1995.) $)

${
	$v A  $.
	f0_limord $f class A $.
	p_limord $p |- ( Lim A -> Ord A ) $= f0_limord a_df-lim f0_limord a_wlim f0_limord a_word f0_limord a_c0 a_wne f0_limord f0_limord a_cuni a_wceq p_simp1bi $.
$}

$(A limit ordinal is its own supremum (union).  (Contributed by NM,
     4-May-1995.) $)

${
	$v A  $.
	f0_limuni $f class A $.
	p_limuni $p |- ( Lim A -> A = U. A ) $= f0_limuni a_df-lim f0_limuni a_wlim f0_limuni a_word f0_limuni a_c0 a_wne f0_limuni f0_limuni a_cuni a_wceq p_simp3bi $.
$}

$(The union of a limit ordinal is a limit ordinal.  (Contributed by NM,
     19-Sep-2006.) $)

${
	$v A  $.
	f0_limuni2 $f class A $.
	p_limuni2 $p |- ( Lim A -> Lim U. A ) $= f0_limuni2 p_limuni f0_limuni2 f0_limuni2 a_cuni p_limeq f0_limuni2 a_wlim f0_limuni2 f0_limuni2 a_cuni a_wceq f0_limuni2 a_wlim f0_limuni2 a_cuni a_wlim a_wb p_syl f0_limuni2 a_wlim f0_limuni2 a_cuni a_wlim p_ibi $.
$}

$(A limit ordinal contains the empty set.  (Contributed by NM,
     15-May-1994.) $)

${
	$v A  $.
	f0_0ellim $f class A $.
	p_0ellim $p |- ( Lim A -> (/) e. A ) $= p_nlim0 f0_0ellim a_c0 p_limeq f0_0ellim a_c0 a_wceq f0_0ellim a_wlim a_c0 a_wlim p_mtbiri f0_0ellim a_wlim f0_0ellim a_c0 p_necon2ai f0_0ellim p_limord f0_0ellim p_ord0eln0 f0_0ellim a_wlim f0_0ellim a_word a_c0 f0_0ellim a_wcel f0_0ellim a_c0 a_wne a_wb p_syl f0_0ellim a_wlim a_c0 f0_0ellim a_wcel f0_0ellim a_c0 a_wne p_mpbird $.
$}

$(A limit ordinal class that is also a set is an ordinal number.
     (Contributed by NM, 26-Apr-2004.) $)

${
	$v A B  $.
	f0_limelon $f class A $.
	f1_limelon $f class B $.
	p_limelon $p |- ( ( A e. B /\ Lim A ) -> A e. On ) $= f0_limelon p_limord f0_limelon f1_limelon p_elong f0_limelon a_wlim f0_limelon a_con0 a_wcel f0_limelon f1_limelon a_wcel f0_limelon a_word p_syl5ibr f0_limelon f1_limelon a_wcel f0_limelon a_wlim f0_limelon a_con0 a_wcel p_imp $.
$}

$(The class of all ordinal numbers in not empty.  (Contributed by NM,
     17-Sep-1995.) $)

${
	$v  $.
	p_onn0 $p |- On =/= (/) $= p_0elon a_con0 a_c0 p_ne0i a_c0 a_con0 a_wcel a_con0 a_c0 a_wne a_ax-mp $.
$}

$(Equality of successors.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B  $.
	f0_suceq $f class A $.
	f1_suceq $f class B $.
	p_suceq $p |- ( A = B -> suc A = suc B ) $= f0_suceq f1_suceq a_wceq p_id f0_suceq f1_suceq p_sneq f0_suceq f1_suceq a_wceq f0_suceq f1_suceq f0_suceq a_csn f1_suceq a_csn p_uneq12d f0_suceq a_df-suc f1_suceq a_df-suc f0_suceq f1_suceq a_wceq f0_suceq f0_suceq a_csn a_cun f1_suceq f1_suceq a_csn a_cun f0_suceq a_csuc f1_suceq a_csuc p_3eqtr4g $.
$}

$(Membership in a successor.  This one-way implication does not require that
     either ` A ` or ` B ` be sets.  (Contributed by NM, 6-Jun-1994.) $)

${
	$v A B  $.
	f0_elsuci $f class A $.
	f1_elsuci $f class B $.
	p_elsuci $p |- ( A e. suc B -> ( A e. B \/ A = B ) ) $= f1_elsuci a_df-suc f1_elsuci a_csuc f1_elsuci f1_elsuci a_csn a_cun f0_elsuci p_eleq2i f0_elsuci f1_elsuci f1_elsuci a_csn p_elun f0_elsuci f1_elsuci a_csuc a_wcel f0_elsuci f1_elsuci f1_elsuci a_csn a_cun a_wcel f0_elsuci f1_elsuci a_wcel f0_elsuci f1_elsuci a_csn a_wcel a_wo p_bitri f0_elsuci f1_elsuci p_elsni f0_elsuci f1_elsuci a_csn a_wcel f0_elsuci f1_elsuci a_wceq f0_elsuci f1_elsuci a_wcel p_orim2i f0_elsuci f1_elsuci a_csuc a_wcel f0_elsuci f1_elsuci a_wcel f0_elsuci f1_elsuci a_csn a_wcel a_wo f0_elsuci f1_elsuci a_wcel f0_elsuci f1_elsuci a_wceq a_wo p_sylbi $.
$}

$(Membership in a successor.  Exercise 5 of [TakeutiZaring] p. 17.
     (Contributed by NM, 15-Sep-1995.) $)

${
	$v A B V  $.
	f0_elsucg $f class A $.
	f1_elsucg $f class B $.
	f2_elsucg $f class V $.
	p_elsucg $p |- ( A e. V -> ( A e. suc B <-> ( A e. B \/ A = B ) ) ) $= f1_elsucg a_df-suc f1_elsucg a_csuc f1_elsucg f1_elsucg a_csn a_cun f0_elsucg p_eleq2i f0_elsucg f1_elsucg f1_elsucg a_csn p_elun f0_elsucg f1_elsucg a_csuc a_wcel f0_elsucg f1_elsucg f1_elsucg a_csn a_cun a_wcel f0_elsucg f1_elsucg a_wcel f0_elsucg f1_elsucg a_csn a_wcel a_wo p_bitri f0_elsucg f1_elsucg f2_elsucg p_elsncg f0_elsucg f2_elsucg a_wcel f0_elsucg f1_elsucg a_csn a_wcel f0_elsucg f1_elsucg a_wceq f0_elsucg f1_elsucg a_wcel p_orbi2d f0_elsucg f1_elsucg a_csuc a_wcel f0_elsucg f1_elsucg a_wcel f0_elsucg f1_elsucg a_csn a_wcel a_wo f0_elsucg f2_elsucg a_wcel f0_elsucg f1_elsucg a_wcel f0_elsucg f1_elsucg a_wceq a_wo p_syl5bb $.
$}

$(Variant of membership in a successor, requiring that ` B ` rather than
     ` A ` be a set.  (Contributed by NM, 28-Oct-2003.) $)

${
	$v A B V  $.
	f0_elsuc2g $f class A $.
	f1_elsuc2g $f class B $.
	f2_elsuc2g $f class V $.
	p_elsuc2g $p |- ( B e. V -> ( A e. suc B <-> ( A e. B \/ A = B ) ) ) $= f1_elsuc2g a_df-suc f1_elsuc2g a_csuc f1_elsuc2g f1_elsuc2g a_csn a_cun f0_elsuc2g p_eleq2i f0_elsuc2g f1_elsuc2g f1_elsuc2g a_csn p_elun f0_elsuc2g f1_elsuc2g f2_elsuc2g p_elsnc2g f1_elsuc2g f2_elsuc2g a_wcel f0_elsuc2g f1_elsuc2g a_csn a_wcel f0_elsuc2g f1_elsuc2g a_wceq f0_elsuc2g f1_elsuc2g a_wcel p_orbi2d f0_elsuc2g f1_elsuc2g f1_elsuc2g a_csn a_cun a_wcel f0_elsuc2g f1_elsuc2g a_wcel f0_elsuc2g f1_elsuc2g a_csn a_wcel a_wo f1_elsuc2g f2_elsuc2g a_wcel f0_elsuc2g f1_elsuc2g a_wcel f0_elsuc2g f1_elsuc2g a_wceq a_wo p_syl5bb f0_elsuc2g f1_elsuc2g a_csuc a_wcel f0_elsuc2g f1_elsuc2g f1_elsuc2g a_csn a_cun a_wcel f1_elsuc2g f2_elsuc2g a_wcel f0_elsuc2g f1_elsuc2g a_wcel f0_elsuc2g f1_elsuc2g a_wceq a_wo p_syl5bb $.
$}

$(Membership in a successor.  Exercise 5 of [TakeutiZaring] p. 17.
       (Contributed by NM, 15-Sep-2003.) $)

${
	$v A B  $.
	f0_elsuc $f class A $.
	f1_elsuc $f class B $.
	e0_elsuc $e |- A e. _V $.
	p_elsuc $p |- ( A e. suc B <-> ( A e. B \/ A = B ) ) $= e0_elsuc f0_elsuc f1_elsuc a_cvv p_elsucg f0_elsuc a_cvv a_wcel f0_elsuc f1_elsuc a_csuc a_wcel f0_elsuc f1_elsuc a_wcel f0_elsuc f1_elsuc a_wceq a_wo a_wb a_ax-mp $.
$}

$(Membership in a successor.  (Contributed by NM, 15-Sep-2003.) $)

${
	$v A B  $.
	f0_elsuc2 $f class A $.
	f1_elsuc2 $f class B $.
	e0_elsuc2 $e |- A e. _V $.
	p_elsuc2 $p |- ( B e. suc A <-> ( B e. A \/ B = A ) ) $= e0_elsuc2 f1_elsuc2 f0_elsuc2 a_cvv p_elsuc2g f0_elsuc2 a_cvv a_wcel f1_elsuc2 f0_elsuc2 a_csuc a_wcel f1_elsuc2 f0_elsuc2 a_wcel f1_elsuc2 f0_elsuc2 a_wceq a_wo a_wb a_ax-mp $.
$}

$(Bound-variable hypothesis builder for successor.  (Contributed by NM,
       15-Sep-2003.) $)

${
	$v x A  $.
	$d A  $.
	$d x  $.
	f0_nfsuc $f set x $.
	f1_nfsuc $f class A $.
	e0_nfsuc $e |- F/_ x A $.
	p_nfsuc $p |- F/_ x suc A $= f1_nfsuc a_df-suc e0_nfsuc e0_nfsuc f0_nfsuc f1_nfsuc p_nfsn f0_nfsuc f1_nfsuc f1_nfsuc a_csn p_nfun f0_nfsuc f1_nfsuc a_csuc f1_nfsuc f1_nfsuc a_csn a_cun p_nfcxfr $.
$}

$(Membership in a successor.  (Contributed by NM, 20-Jun-1998.) $)

${
	$v A B  $.
	f0_elelsuc $f class A $.
	f1_elelsuc $f class B $.
	p_elelsuc $p |- ( A e. B -> A e. suc B ) $= f0_elelsuc f1_elelsuc a_wcel f0_elelsuc f1_elelsuc a_wceq p_orc f0_elelsuc f1_elelsuc f1_elelsuc p_elsucg f0_elelsuc f1_elelsuc a_wcel f0_elelsuc f1_elelsuc a_csuc a_wcel f0_elelsuc f1_elelsuc a_wcel f0_elelsuc f1_elelsuc a_wceq a_wo p_mpbird $.
$}

$(Membership of a successor in another class.  (Contributed by NM,
       29-Jun-2004.) $)

${
	$v x y A B  $.
	$d x y A  $.
	$d x B  $.
	f0_sucel $f set x $.
	f1_sucel $f set y $.
	f2_sucel $f class A $.
	f3_sucel $f class B $.
	p_sucel $p |- ( suc A e. B <-> E. x e. B A. y ( y e. x <-> ( y e. A \/ y = A ) ) ) $= f0_sucel f2_sucel a_csuc f3_sucel p_risset f1_sucel f0_sucel a_sup_set_class f2_sucel a_csuc p_dfcleq f1_sucel p_vex f1_sucel a_sup_set_class f2_sucel p_elsuc f1_sucel a_sup_set_class f2_sucel a_csuc a_wcel f1_sucel a_sup_set_class f2_sucel a_wcel f1_sucel a_sup_set_class f2_sucel a_wceq a_wo f1_sucel a_sup_set_class f0_sucel a_sup_set_class a_wcel p_bibi2i f1_sucel a_sup_set_class f0_sucel a_sup_set_class a_wcel f1_sucel a_sup_set_class f2_sucel a_csuc a_wcel a_wb f1_sucel a_sup_set_class f0_sucel a_sup_set_class a_wcel f1_sucel a_sup_set_class f2_sucel a_wcel f1_sucel a_sup_set_class f2_sucel a_wceq a_wo a_wb f1_sucel p_albii f0_sucel a_sup_set_class f2_sucel a_csuc a_wceq f1_sucel a_sup_set_class f0_sucel a_sup_set_class a_wcel f1_sucel a_sup_set_class f2_sucel a_csuc a_wcel a_wb f1_sucel a_wal f1_sucel a_sup_set_class f0_sucel a_sup_set_class a_wcel f1_sucel a_sup_set_class f2_sucel a_wcel f1_sucel a_sup_set_class f2_sucel a_wceq a_wo a_wb f1_sucel a_wal p_bitri f0_sucel a_sup_set_class f2_sucel a_csuc a_wceq f1_sucel a_sup_set_class f0_sucel a_sup_set_class a_wcel f1_sucel a_sup_set_class f2_sucel a_wcel f1_sucel a_sup_set_class f2_sucel a_wceq a_wo a_wb f1_sucel a_wal f0_sucel f3_sucel p_rexbii f2_sucel a_csuc f3_sucel a_wcel f0_sucel a_sup_set_class f2_sucel a_csuc a_wceq f0_sucel f3_sucel a_wrex f1_sucel a_sup_set_class f0_sucel a_sup_set_class a_wcel f1_sucel a_sup_set_class f2_sucel a_wcel f1_sucel a_sup_set_class f2_sucel a_wceq a_wo a_wb f1_sucel a_wal f0_sucel f3_sucel a_wrex p_bitri $.
$}

$(The successor of the empty set.  (Contributed by NM, 1-Feb-2005.) $)

${
	$v  $.
	p_suc0 $p |- suc (/) = { (/) } $= a_c0 a_df-suc a_c0 a_c0 a_csn p_uncom a_c0 a_csn p_un0 a_c0 a_csuc a_c0 a_c0 a_csn a_cun a_c0 a_csn a_c0 a_cun a_c0 a_csn p_3eqtri $.
$}

$(A proper class is its own successor.  (Contributed by NM, 3-Apr-1995.) $)

${
	$v A  $.
	f0_sucprc $f class A $.
	p_sucprc $p |- ( -. A e. _V -> suc A = A ) $= f0_sucprc a_df-suc f0_sucprc p_snprc f0_sucprc a_csn a_c0 f0_sucprc p_uneq2 f0_sucprc a_cvv a_wcel a_wn f0_sucprc a_csn a_c0 a_wceq f0_sucprc f0_sucprc a_csn a_cun f0_sucprc a_c0 a_cun a_wceq p_sylbi f0_sucprc a_cvv a_wcel a_wn f0_sucprc a_csuc f0_sucprc f0_sucprc a_csn a_cun f0_sucprc a_c0 a_cun p_syl5eq f0_sucprc p_un0 f0_sucprc a_cvv a_wcel a_wn f0_sucprc a_csuc f0_sucprc a_c0 a_cun f0_sucprc p_syl6eq $.
$}

$(A transitive class is equal to the union of its successor.  Combines
       Theorem 4E of [Enderton] p. 72 and Exercise 6 of [Enderton] p. 73.
       (Contributed by NM, 30-Aug-1993.) $)

${
	$v A  $.
	f0_unisuc $f class A $.
	e0_unisuc $e |- A e. _V $.
	p_unisuc $p |- ( Tr A <-> U. suc A = A ) $= f0_unisuc a_cuni f0_unisuc p_ssequn1 f0_unisuc a_df-tr f0_unisuc a_df-suc f0_unisuc a_csuc f0_unisuc f0_unisuc a_csn a_cun p_unieqi f0_unisuc f0_unisuc a_csn p_uniun e0_unisuc f0_unisuc p_unisn f0_unisuc a_csn a_cuni f0_unisuc f0_unisuc a_cuni p_uneq2i f0_unisuc a_csuc a_cuni f0_unisuc f0_unisuc a_csn a_cun a_cuni f0_unisuc a_cuni f0_unisuc a_csn a_cuni a_cun f0_unisuc a_cuni f0_unisuc a_cun p_3eqtri f0_unisuc a_csuc a_cuni f0_unisuc a_cuni f0_unisuc a_cun f0_unisuc p_eqeq1i f0_unisuc a_cuni f0_unisuc a_wss f0_unisuc a_cuni f0_unisuc a_cun f0_unisuc a_wceq f0_unisuc a_wtr f0_unisuc a_csuc a_cuni f0_unisuc a_wceq p_3bitr4i $.
$}

$(A class is included in its own successor.  Part of Proposition 7.23 of
     [TakeutiZaring] p. 41 (generalized to arbitrary classes).  (Contributed by
     NM, 31-May-1994.) $)

${
	$v A  $.
	f0_sssucid $f class A $.
	p_sssucid $p |- A C_ suc A $= f0_sssucid f0_sssucid a_csn p_ssun1 f0_sssucid a_df-suc f0_sssucid f0_sssucid f0_sssucid a_csn a_cun f0_sssucid a_csuc p_sseqtr4i $.
$}

$(Part of Proposition 7.23 of [TakeutiZaring] p. 41 (generalized).
     (Contributed by NM, 25-Mar-1995.)  (Proof shortened by Scott Fenton,
     20-Feb-2012.) $)

${
	$v A V  $.
	f0_sucidg $f class A $.
	f1_sucidg $f class V $.
	p_sucidg $p |- ( A e. V -> A e. suc A ) $= f0_sucidg p_eqid f0_sucidg f0_sucidg a_wceq f0_sucidg f0_sucidg a_wcel p_olci f0_sucidg f0_sucidg f1_sucidg p_elsucg f0_sucidg f1_sucidg a_wcel f0_sucidg f0_sucidg a_csuc a_wcel f0_sucidg f0_sucidg a_wcel f0_sucidg f0_sucidg a_wceq a_wo p_mpbiri $.
$}

$(A set belongs to its successor.  (Contributed by NM, 22-Jun-1994.)
       (Proof shortened by Alan Sare, 18-Feb-2012.)  (Proof shortened by Scott
       Fenton, 20-Feb-2012.) $)

${
	$v A  $.
	f0_sucid $f class A $.
	e0_sucid $e |- A e. _V $.
	p_sucid $p |- A e. suc A $= e0_sucid f0_sucid a_cvv p_sucidg f0_sucid a_cvv a_wcel f0_sucid f0_sucid a_csuc a_wcel a_ax-mp $.
$}

$(No successor is empty.  (Contributed by NM, 3-Apr-1995.) $)

${
	$v A  $.
	f0_nsuceq0 $f class A $.
	p_nsuceq0 $p |- suc A =/= (/) $= f0_nsuceq0 p_noel f0_nsuceq0 a_cvv p_sucidg f0_nsuceq0 a_csuc a_c0 f0_nsuceq0 p_eleq2 f0_nsuceq0 a_cvv a_wcel f0_nsuceq0 f0_nsuceq0 a_csuc a_wcel f0_nsuceq0 a_csuc a_c0 a_wceq f0_nsuceq0 a_c0 a_wcel p_syl5ibcom f0_nsuceq0 a_cvv a_wcel f0_nsuceq0 a_csuc a_c0 a_wceq f0_nsuceq0 a_c0 a_wcel p_mtoi f0_nsuceq0 p_sucprc f0_nsuceq0 a_cvv a_wcel a_wn f0_nsuceq0 a_csuc f0_nsuceq0 a_c0 p_eqeq1d p_0ex f0_nsuceq0 a_c0 a_cvv p_eleq1 f0_nsuceq0 a_c0 a_wceq f0_nsuceq0 a_cvv a_wcel a_c0 a_cvv a_wcel p_mpbiri f0_nsuceq0 a_cvv a_wcel a_wn f0_nsuceq0 a_csuc a_c0 a_wceq f0_nsuceq0 a_c0 a_wceq f0_nsuceq0 a_cvv a_wcel p_syl6bi f0_nsuceq0 a_cvv a_wcel a_wn f0_nsuceq0 a_csuc a_c0 a_wceq f0_nsuceq0 a_cvv a_wcel p_con3d f0_nsuceq0 a_cvv a_wcel a_wn f0_nsuceq0 a_csuc a_c0 a_wceq a_wn p_pm2.43i f0_nsuceq0 a_cvv a_wcel f0_nsuceq0 a_csuc a_c0 a_wceq a_wn p_pm2.61i f0_nsuceq0 a_csuc a_c0 a_df-ne f0_nsuceq0 a_csuc a_c0 a_wne f0_nsuceq0 a_csuc a_c0 a_wceq a_wn p_mpbir $.
$}

$(A set belongs to the successor of an equal set.  (Contributed by NM,
       18-Aug-1994.) $)

${
	$v A B  $.
	f0_eqelsuc $f class A $.
	f1_eqelsuc $f class B $.
	e0_eqelsuc $e |- A e. _V $.
	p_eqelsuc $p |- ( A = B -> A e. suc B ) $= e0_eqelsuc f0_eqelsuc p_sucid f0_eqelsuc f1_eqelsuc p_suceq f0_eqelsuc f1_eqelsuc a_wceq f0_eqelsuc f0_eqelsuc a_csuc f1_eqelsuc a_csuc p_syl5eleq $.
$}

$(Inductive definition for the indexed union at a successor.  (Contributed
       by Mario Carneiro, 4-Feb-2013.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)

${
	$v x A B C  $.
	$d A x  $.
	$d B  $.
	$d C x  $.
	f0_iunsuc $f set x $.
	f1_iunsuc $f class A $.
	f2_iunsuc $f class B $.
	f3_iunsuc $f class C $.
	e0_iunsuc $e |- A e. _V $.
	e1_iunsuc $e |- ( x = A -> B = C ) $.
	p_iunsuc $p |- U_ x e. suc A B = ( U_ x e. A B u. C ) $= f1_iunsuc a_df-suc f0_iunsuc f1_iunsuc a_csuc f1_iunsuc f1_iunsuc a_csn a_cun f2_iunsuc p_iuneq1 f1_iunsuc a_csuc f1_iunsuc f1_iunsuc a_csn a_cun a_wceq f0_iunsuc f1_iunsuc a_csuc f2_iunsuc a_ciun f0_iunsuc f1_iunsuc f1_iunsuc a_csn a_cun f2_iunsuc a_ciun a_wceq a_ax-mp f0_iunsuc f1_iunsuc f1_iunsuc a_csn f2_iunsuc p_iunxun e0_iunsuc e1_iunsuc f0_iunsuc f1_iunsuc f2_iunsuc f3_iunsuc p_iunxsn f0_iunsuc f1_iunsuc a_csn f2_iunsuc a_ciun f3_iunsuc f0_iunsuc f1_iunsuc f2_iunsuc a_ciun p_uneq2i f0_iunsuc f1_iunsuc a_csuc f2_iunsuc a_ciun f0_iunsuc f1_iunsuc f1_iunsuc a_csn a_cun f2_iunsuc a_ciun f0_iunsuc f1_iunsuc f2_iunsuc a_ciun f0_iunsuc f1_iunsuc a_csn f2_iunsuc a_ciun a_cun f0_iunsuc f1_iunsuc f2_iunsuc a_ciun f3_iunsuc a_cun p_3eqtri $.
$}

$(The successor of a transtive class is transitive.  (Contributed by Alan
       Sare, 11-Apr-2009.) $)

${
	$v A  $.
	$d z y A  $.
	f0_suctr $f class A $.
	i0_suctr $f set y $.
	i1_suctr $f set z $.
	p_suctr $p |- ( Tr A -> Tr suc A ) $= i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel p_simpr i0_suctr p_vex i0_suctr a_sup_set_class f0_suctr p_elsuc i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel i0_suctr a_sup_set_class f0_suctr a_wcel i0_suctr a_sup_set_class f0_suctr a_wceq a_wo p_sylib i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel p_simpl i0_suctr a_sup_set_class f0_suctr i1_suctr a_sup_set_class p_eleq2 i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_wceq i1_suctr a_sup_set_class f0_suctr a_wcel p_syl5ibcom i1_suctr a_sup_set_class f0_suctr p_elelsuc i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i0_suctr a_sup_set_class f0_suctr a_wceq i1_suctr a_sup_set_class f0_suctr a_wcel i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel p_syl6 f0_suctr i1_suctr a_sup_set_class i0_suctr a_sup_set_class p_trel f0_suctr a_wtr i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_wcel i1_suctr a_sup_set_class f0_suctr a_wcel p_exp3a f0_suctr a_wtr i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_wcel i1_suctr a_sup_set_class f0_suctr a_wcel a_wi i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel p_adantrd i1_suctr a_sup_set_class f0_suctr p_elelsuc f0_suctr a_wtr i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i0_suctr a_sup_set_class f0_suctr a_wcel i1_suctr a_sup_set_class f0_suctr a_wcel i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel p_syl8 i0_suctr a_sup_set_class f0_suctr a_wcel i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel i0_suctr a_sup_set_class f0_suctr a_wceq p_jao f0_suctr a_wtr i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i0_suctr a_sup_set_class f0_suctr a_wcel i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wi i0_suctr a_sup_set_class f0_suctr a_wceq i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wi i0_suctr a_sup_set_class f0_suctr a_wcel i0_suctr a_sup_set_class f0_suctr a_wceq a_wo i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wi a_wi p_syl6 f0_suctr a_wtr i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i0_suctr a_sup_set_class f0_suctr a_wceq i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wi i0_suctr a_sup_set_class f0_suctr a_wcel i0_suctr a_sup_set_class f0_suctr a_wceq a_wo i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wi p_mpdi f0_suctr a_wtr i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i0_suctr a_sup_set_class f0_suctr a_wcel i0_suctr a_sup_set_class f0_suctr a_wceq a_wo i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel p_mpdi f0_suctr a_wtr i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wi i1_suctr i0_suctr p_alrimivv i1_suctr i0_suctr f0_suctr a_csuc p_dftr2 f0_suctr a_wtr i1_suctr a_sup_set_class i0_suctr a_sup_set_class a_wcel i0_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wa i1_suctr a_sup_set_class f0_suctr a_csuc a_wcel a_wi i0_suctr a_wal i1_suctr a_wal f0_suctr a_csuc a_wtr p_sylibr $.
$}

$(A set whose successor belongs to a transitive class also belongs.
     (Contributed by NM, 5-Sep-2003.)  (Proof shortened by Andrew Salmon,
     12-Aug-2011.) $)

${
	$v A B  $.
	f0_trsuc $f class A $.
	f1_trsuc $f class B $.
	p_trsuc $p |- ( ( Tr A /\ suc B e. A ) -> B e. A ) $= f1_trsuc p_sssucid f1_trsuc f1_trsuc a_csuc f0_trsuc p_ssexg f1_trsuc f1_trsuc a_csuc a_wss f1_trsuc a_csuc f0_trsuc a_wcel f1_trsuc a_cvv a_wcel p_mpan f1_trsuc a_cvv p_sucidg f1_trsuc a_csuc f0_trsuc a_wcel f1_trsuc a_cvv a_wcel f1_trsuc f1_trsuc a_csuc a_wcel p_syl f1_trsuc a_csuc f0_trsuc a_wcel f1_trsuc f1_trsuc a_csuc a_wcel p_ancri f0_trsuc f1_trsuc f1_trsuc a_csuc p_trel f1_trsuc a_csuc f0_trsuc a_wcel f1_trsuc f1_trsuc a_csuc a_wcel f1_trsuc a_csuc f0_trsuc a_wcel a_wa f0_trsuc a_wtr f1_trsuc f0_trsuc a_wcel p_syl5 f0_trsuc a_wtr f1_trsuc a_csuc f0_trsuc a_wcel f1_trsuc f0_trsuc a_wcel p_imp $.
$}

$(Obsolete proof of ~ suctr as of 5-Apr-2016.  The successor of a
       transitive set is transitive.  (Contributed by Scott Fenton,
       21-Feb-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v A  $.
	$d x y A  $.
	f0_trsuc2OLD $f class A $.
	i0_trsuc2OLD $f set x $.
	i1_trsuc2OLD $f set y $.
	p_trsuc2OLD $p |- ( Tr A -> Tr suc A ) $= i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel p_andi i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD i0_trsuc2OLD a_sup_set_class p_eleq2 i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel p_biimpac i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa p_orim2i f0_trsuc2OLD i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class p_trel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq p_orc f0_trsuc2OLD a_wtr i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wo p_syl6 i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq p_orc i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wo a_wi f0_trsuc2OLD a_wtr p_a1i f0_trsuc2OLD a_wtr i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wo i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel p_jaod i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wa a_wo i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wo f0_trsuc2OLD a_wtr i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wo p_syl5 i1_trsuc2OLD f0_trsuc2OLD p_elsn i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel p_anbi2i i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wa i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wa i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa p_orbi2i i0_trsuc2OLD f0_trsuc2OLD p_elsn i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel p_orbi2i f0_trsuc2OLD a_wtr i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wa a_wo i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wceq a_wo i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wa a_wo i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo p_3imtr4g i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wa i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel a_wa i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wa a_wo f0_trsuc2OLD a_wtr i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo p_syl5bi f0_trsuc2OLD a_wtr i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wi i0_trsuc2OLD i1_trsuc2OLD p_alrimivv f0_trsuc2OLD a_df-suc f0_trsuc2OLD a_csuc f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun p_treq f0_trsuc2OLD a_csuc f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wceq f0_trsuc2OLD a_csuc a_wtr f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wtr a_wb a_ax-mp i0_trsuc2OLD i1_trsuc2OLD f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun p_dftr2 i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn p_elun i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel p_anbi2i i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn p_elun i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wcel a_wa i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo p_imbi12i i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wcel a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wcel a_wi i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wi i0_trsuc2OLD i1_trsuc2OLD p_2albii f0_trsuc2OLD a_csuc a_wtr f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wtr i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wcel a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD f0_trsuc2OLD a_csn a_cun a_wcel a_wi i1_trsuc2OLD a_wal i0_trsuc2OLD a_wal i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wi i1_trsuc2OLD a_wal i0_trsuc2OLD a_wal p_3bitri f0_trsuc2OLD a_wtr i0_trsuc2OLD a_sup_set_class i1_trsuc2OLD a_sup_set_class a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i1_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wa i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_wcel i0_trsuc2OLD a_sup_set_class f0_trsuc2OLD a_csn a_wcel a_wo a_wi i1_trsuc2OLD a_wal i0_trsuc2OLD a_wal f0_trsuc2OLD a_csuc a_wtr p_sylibr $.
$}

$(A member of the successor of a transitive class is a subclass of it.
     (Contributed by NM, 4-Oct-2003.) $)

${
	$v A B  $.
	f0_trsucss $f class A $.
	f1_trsucss $f class B $.
	p_trsucss $p |- ( Tr A -> ( B e. suc A -> B C_ A ) ) $= f1_trsucss f0_trsucss p_elsuci f0_trsucss f1_trsucss p_trss f1_trsucss f0_trsucss p_eqimss f1_trsucss f0_trsucss a_wceq f1_trsucss f0_trsucss a_wss a_wi f0_trsucss a_wtr p_a1i f0_trsucss a_wtr f1_trsucss f0_trsucss a_wcel f1_trsucss f0_trsucss a_wss f1_trsucss f0_trsucss a_wceq p_jaod f1_trsucss f0_trsucss a_csuc a_wcel f1_trsucss f0_trsucss a_wcel f1_trsucss f0_trsucss a_wceq a_wo f0_trsucss a_wtr f1_trsucss f0_trsucss a_wss p_syl5 $.
$}

$(A subset of an ordinal belongs to its successor.  (Contributed by NM,
     28-Nov-2003.) $)

${
	$v A B  $.
	f0_ordsssuc $f class A $.
	f1_ordsssuc $f class B $.
	p_ordsssuc $p |- ( ( A e. On /\ Ord B ) -> ( A C_ B <-> A e. suc B ) ) $= f0_ordsssuc p_eloni f0_ordsssuc f1_ordsssuc p_ordsseleq f0_ordsssuc a_con0 a_wcel f0_ordsssuc a_word f1_ordsssuc a_word f0_ordsssuc f1_ordsssuc a_wss f0_ordsssuc f1_ordsssuc a_wcel f0_ordsssuc f1_ordsssuc a_wceq a_wo a_wb p_sylan f0_ordsssuc f1_ordsssuc a_con0 p_elsucg f0_ordsssuc a_con0 a_wcel f0_ordsssuc f1_ordsssuc a_csuc a_wcel f0_ordsssuc f1_ordsssuc a_wcel f0_ordsssuc f1_ordsssuc a_wceq a_wo a_wb f1_ordsssuc a_word p_adantr f0_ordsssuc a_con0 a_wcel f1_ordsssuc a_word a_wa f0_ordsssuc f1_ordsssuc a_wss f0_ordsssuc f1_ordsssuc a_wcel f0_ordsssuc f1_ordsssuc a_wceq a_wo f0_ordsssuc f1_ordsssuc a_csuc a_wcel p_bitr4d $.
$}

$(A subset of an ordinal number belongs to its successor.  (Contributed by
     NM, 15-Sep-1995.) $)

${
	$v A B  $.
	f0_onsssuc $f class A $.
	f1_onsssuc $f class B $.
	p_onsssuc $p |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> A e. suc B ) ) $= f1_onsssuc p_eloni f0_onsssuc f1_onsssuc p_ordsssuc f1_onsssuc a_con0 a_wcel f0_onsssuc a_con0 a_wcel f1_onsssuc a_word f0_onsssuc f1_onsssuc a_wss f0_onsssuc f1_onsssuc a_csuc a_wcel a_wb p_sylan2 $.
$}

$(An ordinal subset of an ordinal number belongs to its successor.
     (Contributed by NM, 1-Feb-2005.)  (Proof shortened by Andrew Salmon,
     12-Aug-2011.) $)

${
	$v A B  $.
	f0_ordsssuc2 $f class A $.
	f1_ordsssuc2 $f class B $.
	p_ordsssuc2 $p |- ( ( Ord A /\ B e. On ) -> ( A C_ B <-> A e. suc B ) ) $= f0_ordsssuc2 a_cvv p_elong f0_ordsssuc2 a_cvv a_wcel f0_ordsssuc2 a_con0 a_wcel f0_ordsssuc2 a_word p_biimprd f0_ordsssuc2 a_cvv a_wcel f0_ordsssuc2 a_word f0_ordsssuc2 a_con0 a_wcel f1_ordsssuc2 a_con0 a_wcel p_anim1d f0_ordsssuc2 f1_ordsssuc2 p_onsssuc f0_ordsssuc2 a_cvv a_wcel f0_ordsssuc2 a_word f1_ordsssuc2 a_con0 a_wcel a_wa f0_ordsssuc2 a_con0 a_wcel f1_ordsssuc2 a_con0 a_wcel a_wa f0_ordsssuc2 f1_ordsssuc2 a_wss f0_ordsssuc2 f1_ordsssuc2 a_csuc a_wcel a_wb p_syl6 f1_ordsssuc2 a_con0 a_wcel f0_ordsssuc2 a_cvv a_wcel p_annim f0_ordsssuc2 f1_ordsssuc2 a_con0 p_ssexg f0_ordsssuc2 f1_ordsssuc2 a_wss f1_ordsssuc2 a_con0 a_wcel f0_ordsssuc2 a_cvv a_wcel p_ex f0_ordsssuc2 f1_ordsssuc2 a_csuc p_elex f0_ordsssuc2 f1_ordsssuc2 a_csuc a_wcel f0_ordsssuc2 a_cvv a_wcel f1_ordsssuc2 a_con0 a_wcel p_a1d f0_ordsssuc2 f1_ordsssuc2 a_wss f1_ordsssuc2 a_con0 a_wcel f0_ordsssuc2 a_cvv a_wcel a_wi f0_ordsssuc2 f1_ordsssuc2 a_csuc a_wcel p_pm5.21ni f1_ordsssuc2 a_con0 a_wcel f0_ordsssuc2 a_cvv a_wcel a_wn a_wa f1_ordsssuc2 a_con0 a_wcel f0_ordsssuc2 a_cvv a_wcel a_wi a_wn f0_ordsssuc2 f1_ordsssuc2 a_wss f0_ordsssuc2 f1_ordsssuc2 a_csuc a_wcel a_wb p_sylbi f1_ordsssuc2 a_con0 a_wcel f0_ordsssuc2 a_cvv a_wcel a_wn f0_ordsssuc2 f1_ordsssuc2 a_wss f0_ordsssuc2 f1_ordsssuc2 a_csuc a_wcel a_wb p_expcom f0_ordsssuc2 a_cvv a_wcel a_wn f1_ordsssuc2 a_con0 a_wcel f0_ordsssuc2 f1_ordsssuc2 a_wss f0_ordsssuc2 f1_ordsssuc2 a_csuc a_wcel a_wb f0_ordsssuc2 a_word p_adantld f0_ordsssuc2 a_cvv a_wcel f0_ordsssuc2 a_word f1_ordsssuc2 a_con0 a_wcel a_wa f0_ordsssuc2 f1_ordsssuc2 a_wss f0_ordsssuc2 f1_ordsssuc2 a_csuc a_wcel a_wb a_wi p_pm2.61i $.
$}

$(When its successor is subtracted from a class of ordinal numbers, an
       ordinal number is less than the minimum of the resulting subclass.
       (Contributed by NM, 1-Dec-2003.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_onmindif $f class A $.
	f1_onmindif $f class B $.
	i0_onmindif $f set x $.
	p_onmindif $p |- ( ( A C_ On /\ B e. On ) -> B e. |^| ( A \ suc B ) ) $= i0_onmindif a_sup_set_class f0_onmindif f1_onmindif a_csuc p_eldif f0_onmindif a_con0 i0_onmindif a_sup_set_class p_ssel2 i0_onmindif a_sup_set_class f1_onmindif p_ontri1 i0_onmindif a_sup_set_class f1_onmindif p_onsssuc i0_onmindif a_sup_set_class a_con0 a_wcel f1_onmindif a_con0 a_wcel a_wa i0_onmindif a_sup_set_class f1_onmindif a_wss f1_onmindif i0_onmindif a_sup_set_class a_wcel a_wn i0_onmindif a_sup_set_class f1_onmindif a_csuc a_wcel p_bitr3d i0_onmindif a_sup_set_class a_con0 a_wcel f1_onmindif a_con0 a_wcel a_wa f1_onmindif i0_onmindif a_sup_set_class a_wcel i0_onmindif a_sup_set_class f1_onmindif a_csuc a_wcel p_con1bid f0_onmindif a_con0 a_wss i0_onmindif a_sup_set_class f0_onmindif a_wcel a_wa i0_onmindif a_sup_set_class a_con0 a_wcel f1_onmindif a_con0 a_wcel i0_onmindif a_sup_set_class f1_onmindif a_csuc a_wcel a_wn f1_onmindif i0_onmindif a_sup_set_class a_wcel a_wb p_sylan f0_onmindif a_con0 a_wss i0_onmindif a_sup_set_class f0_onmindif a_wcel a_wa f1_onmindif a_con0 a_wcel a_wa i0_onmindif a_sup_set_class f1_onmindif a_csuc a_wcel a_wn f1_onmindif i0_onmindif a_sup_set_class a_wcel p_biimpd f0_onmindif a_con0 a_wss i0_onmindif a_sup_set_class f0_onmindif a_wcel f1_onmindif a_con0 a_wcel i0_onmindif a_sup_set_class f1_onmindif a_csuc a_wcel a_wn f1_onmindif i0_onmindif a_sup_set_class a_wcel a_wi p_exp31 f0_onmindif a_con0 a_wss i0_onmindif a_sup_set_class f0_onmindif a_wcel f1_onmindif a_con0 a_wcel i0_onmindif a_sup_set_class f1_onmindif a_csuc a_wcel a_wn f1_onmindif i0_onmindif a_sup_set_class a_wcel a_wi p_com23 f0_onmindif a_con0 a_wss f1_onmindif a_con0 a_wcel i0_onmindif a_sup_set_class f0_onmindif a_wcel i0_onmindif a_sup_set_class f1_onmindif a_csuc a_wcel a_wn f1_onmindif i0_onmindif a_sup_set_class a_wcel p_imp4b i0_onmindif a_sup_set_class f0_onmindif f1_onmindif a_csuc a_cdif a_wcel i0_onmindif a_sup_set_class f0_onmindif a_wcel i0_onmindif a_sup_set_class f1_onmindif a_csuc a_wcel a_wn a_wa f0_onmindif a_con0 a_wss f1_onmindif a_con0 a_wcel a_wa f1_onmindif i0_onmindif a_sup_set_class a_wcel p_syl5bi f0_onmindif a_con0 a_wss f1_onmindif a_con0 a_wcel a_wa f1_onmindif i0_onmindif a_sup_set_class a_wcel i0_onmindif f0_onmindif f1_onmindif a_csuc a_cdif p_ralrimiv i0_onmindif f1_onmindif f0_onmindif f1_onmindif a_csuc a_cdif a_con0 p_elintg f1_onmindif a_con0 a_wcel f1_onmindif f0_onmindif f1_onmindif a_csuc a_cdif a_cint a_wcel f1_onmindif i0_onmindif a_sup_set_class a_wcel i0_onmindif f0_onmindif f1_onmindif a_csuc a_cdif a_wral a_wb f0_onmindif a_con0 a_wss p_adantl f0_onmindif a_con0 a_wss f1_onmindif a_con0 a_wcel a_wa f1_onmindif f0_onmindif f1_onmindif a_csuc a_cdif a_cint a_wcel f1_onmindif i0_onmindif a_sup_set_class a_wcel i0_onmindif f0_onmindif f1_onmindif a_csuc a_cdif a_wral p_mpbird $.
$}

$(There is no set between an ordinal class and its successor.  Generalized
     Proposition 7.25 of [TakeutiZaring] p. 41.  (Contributed by NM,
     21-Jun-1998.) $)

${
	$v A B  $.
	f0_ordnbtwn $f class A $.
	f1_ordnbtwn $f class B $.
	p_ordnbtwn $p |- ( Ord A -> -. ( A e. B /\ B e. suc A ) ) $= f0_ordnbtwn f1_ordnbtwn p_ordn2lp f0_ordnbtwn p_ordirr f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel a_wa f0_ordnbtwn f0_ordnbtwn a_wcel p_ioran f0_ordnbtwn a_word f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel a_wa a_wn f0_ordnbtwn f0_ordnbtwn a_wcel a_wn f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel a_wa f0_ordnbtwn f0_ordnbtwn a_wcel a_wo a_wn p_sylanbrc f1_ordnbtwn f0_ordnbtwn p_elsuci f1_ordnbtwn f0_ordnbtwn a_csuc a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wceq a_wo f0_ordnbtwn f1_ordnbtwn a_wcel p_anim2i f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wceq p_andi f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_csuc a_wcel a_wa f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wceq a_wo a_wa f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel a_wa f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wceq a_wa a_wo p_sylib f1_ordnbtwn f0_ordnbtwn f0_ordnbtwn p_eleq2 f1_ordnbtwn f0_ordnbtwn a_wceq f0_ordnbtwn f1_ordnbtwn a_wcel f0_ordnbtwn f0_ordnbtwn a_wcel p_biimpac f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wceq a_wa f0_ordnbtwn f0_ordnbtwn a_wcel f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel a_wa p_orim2i f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_csuc a_wcel a_wa f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel a_wa f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wceq a_wa a_wo f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel a_wa f0_ordnbtwn f0_ordnbtwn a_wcel a_wo p_syl f0_ordnbtwn a_word f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_wcel a_wa f0_ordnbtwn f0_ordnbtwn a_wcel a_wo f0_ordnbtwn f1_ordnbtwn a_wcel f1_ordnbtwn f0_ordnbtwn a_csuc a_wcel a_wa p_nsyl $.
$}

$(There is no set between an ordinal number and its successor.  Proposition
     7.25 of [TakeutiZaring] p. 41.  (Contributed by NM, 9-Jun-1994.) $)

${
	$v A B  $.
	f0_onnbtwn $f class A $.
	f1_onnbtwn $f class B $.
	p_onnbtwn $p |- ( A e. On -> -. ( A e. B /\ B e. suc A ) ) $= f0_onnbtwn p_eloni f0_onnbtwn f1_onnbtwn p_ordnbtwn f0_onnbtwn a_con0 a_wcel f0_onnbtwn a_word f0_onnbtwn f1_onnbtwn a_wcel f1_onnbtwn f0_onnbtwn a_csuc a_wcel a_wa a_wn p_syl $.
$}

$(A set whose successor is a subset of another class is a member of that
     class.  (Contributed by NM, 16-Sep-1995.) $)

${
	$v A B V  $.
	f0_sucssel $f class A $.
	f1_sucssel $f class B $.
	f2_sucssel $f class V $.
	p_sucssel $p |- ( A e. V -> ( suc A C_ B -> A e. B ) ) $= f0_sucssel f2_sucssel p_sucidg f0_sucssel a_csuc f1_sucssel f0_sucssel p_ssel f0_sucssel f2_sucssel a_wcel f0_sucssel f0_sucssel a_csuc a_wcel f0_sucssel a_csuc f1_sucssel a_wss f0_sucssel f1_sucssel a_wcel p_syl5com $.
$}

$(Ordinal derived from its successor.  (Contributed by NM, 20-May-1998.) $)

${
	$v A  $.
	f0_orddif $f class A $.
	p_orddif $p |- ( Ord A -> A = ( suc A \ { A } ) ) $= f0_orddif p_orddisj f0_orddif f0_orddif a_csn p_disj3 f0_orddif a_df-suc f0_orddif a_csuc f0_orddif f0_orddif a_csn a_cun f0_orddif a_csn p_difeq1i f0_orddif f0_orddif a_csn p_difun2 f0_orddif a_csuc f0_orddif a_csn a_cdif f0_orddif f0_orddif a_csn a_cun f0_orddif a_csn a_cdif f0_orddif f0_orddif a_csn a_cdif p_eqtri f0_orddif a_csuc f0_orddif a_csn a_cdif f0_orddif f0_orddif a_csn a_cdif f0_orddif p_eqeq2i f0_orddif f0_orddif a_csn a_cin a_c0 a_wceq f0_orddif f0_orddif f0_orddif a_csn a_cdif a_wceq f0_orddif f0_orddif a_csuc f0_orddif a_csn a_cdif a_wceq p_bitr4i f0_orddif a_word f0_orddif f0_orddif a_csn a_cin a_c0 a_wceq f0_orddif f0_orddif a_csuc f0_orddif a_csn a_cdif a_wceq p_sylib $.
$}

$(An ordinal class includes its union.  (Contributed by NM, 13-Sep-2003.) $)

${
	$v A  $.
	f0_orduniss $f class A $.
	p_orduniss $p |- ( Ord A -> U. A C_ A ) $= f0_orduniss p_ordtr f0_orduniss a_df-tr f0_orduniss a_word f0_orduniss a_wtr f0_orduniss a_cuni f0_orduniss a_wss p_sylib $.
$}

$(A trichotomy law for ordinal classes.  (Contributed by NM, 13-Sep-2003.)
     (Proof shortened by Andrew Salmon, 12-Aug-2011.) $)

${
	$v A B  $.
	f0_ordtri2or $f class A $.
	f1_ordtri2or $f class B $.
	p_ordtri2or $p |- ( ( Ord A /\ Ord B ) -> ( A e. B \/ B C_ A ) ) $= f1_ordtri2or f0_ordtri2or p_ordtri1 f1_ordtri2or a_word f0_ordtri2or a_word f1_ordtri2or f0_ordtri2or a_wss f0_ordtri2or f1_ordtri2or a_wcel a_wn a_wb p_ancoms f0_ordtri2or a_word f1_ordtri2or a_word a_wa f1_ordtri2or f0_ordtri2or a_wss f0_ordtri2or f1_ordtri2or a_wcel a_wn p_biimprd f0_ordtri2or a_word f1_ordtri2or a_word a_wa f0_ordtri2or f1_ordtri2or a_wcel f1_ordtri2or f0_ordtri2or a_wss p_orrd $.
$}

$(A trichotomy law for ordinal classes.  (Contributed by NM, 2-Nov-2003.) $)

${
	$v A B  $.
	f0_ordtri2or2 $f class A $.
	f1_ordtri2or2 $f class B $.
	p_ordtri2or2 $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B \/ B C_ A ) ) $= f0_ordtri2or2 f1_ordtri2or2 p_ordtri2or f1_ordtri2or2 f0_ordtri2or2 p_ordelss f1_ordtri2or2 a_word f0_ordtri2or2 f1_ordtri2or2 a_wcel f0_ordtri2or2 f1_ordtri2or2 a_wss p_ex f1_ordtri2or2 a_word f0_ordtri2or2 f1_ordtri2or2 a_wcel f0_ordtri2or2 f1_ordtri2or2 a_wss f1_ordtri2or2 f0_ordtri2or2 a_wss p_orim1d f1_ordtri2or2 a_word f0_ordtri2or2 f1_ordtri2or2 a_wcel f1_ordtri2or2 f0_ordtri2or2 a_wss a_wo f0_ordtri2or2 f1_ordtri2or2 a_wss f1_ordtri2or2 f0_ordtri2or2 a_wss a_wo a_wi f0_ordtri2or2 a_word p_adantl f0_ordtri2or2 a_word f1_ordtri2or2 a_word a_wa f0_ordtri2or2 f1_ordtri2or2 a_wcel f1_ordtri2or2 f0_ordtri2or2 a_wss a_wo f0_ordtri2or2 f1_ordtri2or2 a_wss f1_ordtri2or2 f0_ordtri2or2 a_wss a_wo p_mpd $.
$}

$(A consequence of total ordering for ordinal classes.  Similar to
     ~ ordtri2or2 .  (Contributed by David Moews, 1-May-2017.) $)

${
	$v A B  $.
	f0_ordtri2or3 $f class A $.
	f1_ordtri2or3 $f class B $.
	p_ordtri2or3 $p |- ( ( Ord A /\ Ord B ) -> ( A = ( A i^i B ) \/ B = ( A i^i B ) ) ) $= f0_ordtri2or3 f1_ordtri2or3 p_ordtri2or2 f0_ordtri2or3 f1_ordtri2or3 p_dfss f1_ordtri2or3 f0_ordtri2or3 p_dfss5 f0_ordtri2or3 f1_ordtri2or3 a_wss f0_ordtri2or3 f0_ordtri2or3 f1_ordtri2or3 a_cin a_wceq f1_ordtri2or3 f0_ordtri2or3 a_wss f1_ordtri2or3 f0_ordtri2or3 f1_ordtri2or3 a_cin a_wceq p_orbi12i f0_ordtri2or3 a_word f1_ordtri2or3 a_word a_wa f0_ordtri2or3 f1_ordtri2or3 a_wss f1_ordtri2or3 f0_ordtri2or3 a_wss a_wo f0_ordtri2or3 f0_ordtri2or3 f1_ordtri2or3 a_cin a_wceq f1_ordtri2or3 f0_ordtri2or3 f1_ordtri2or3 a_cin a_wceq a_wo p_sylib $.
$}

$(The intersection of two ordinal classes is an element of a third if and
     only if either one of them is.  (Contributed by David Moews,
     1-May-2017.) $)

${
	$v A B C  $.
	f0_ordelinel $f class A $.
	f1_ordelinel $f class B $.
	f2_ordelinel $f class C $.
	p_ordelinel $p |- ( ( Ord A /\ Ord B /\ Ord C ) -> ( ( A i^i B ) e. C <-> ( A e. C \/ B e. C ) ) ) $= f0_ordelinel f1_ordelinel p_ordtri2or3 f0_ordelinel a_word f1_ordelinel a_word f0_ordelinel f0_ordelinel f1_ordelinel a_cin a_wceq f1_ordelinel f0_ordelinel f1_ordelinel a_cin a_wceq a_wo f2_ordelinel a_word p_3adant3 f0_ordelinel f0_ordelinel f1_ordelinel a_cin f2_ordelinel p_eleq1 f0_ordelinel f2_ordelinel a_wcel f1_ordelinel f2_ordelinel a_wcel p_orc f0_ordelinel f0_ordelinel f1_ordelinel a_cin a_wceq f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel f0_ordelinel f2_ordelinel a_wcel f0_ordelinel f2_ordelinel a_wcel f1_ordelinel f2_ordelinel a_wcel a_wo p_syl6bir f1_ordelinel f0_ordelinel f1_ordelinel a_cin f2_ordelinel p_eleq1 f1_ordelinel f2_ordelinel a_wcel f0_ordelinel f2_ordelinel a_wcel p_olc f1_ordelinel f0_ordelinel f1_ordelinel a_cin a_wceq f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel f1_ordelinel f2_ordelinel a_wcel f0_ordelinel f2_ordelinel a_wcel f1_ordelinel f2_ordelinel a_wcel a_wo p_syl6bir f0_ordelinel f0_ordelinel f1_ordelinel a_cin a_wceq f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel f0_ordelinel f2_ordelinel a_wcel f1_ordelinel f2_ordelinel a_wcel a_wo a_wi f1_ordelinel f0_ordelinel f1_ordelinel a_cin a_wceq p_jaoi f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word a_w3a f0_ordelinel f0_ordelinel f1_ordelinel a_cin a_wceq f1_ordelinel f0_ordelinel f1_ordelinel a_cin a_wceq a_wo f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel f0_ordelinel f2_ordelinel a_wcel f1_ordelinel f2_ordelinel a_wcel a_wo a_wi p_syl f0_ordelinel f1_ordelinel p_inss1 f0_ordelinel f1_ordelinel p_ordin f0_ordelinel a_word f1_ordelinel a_word a_wa f0_ordelinel f1_ordelinel a_cin a_word f2_ordelinel a_word p_anim1i f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word f0_ordelinel f1_ordelinel a_cin a_word f2_ordelinel a_word a_wa p_3impa f0_ordelinel f1_ordelinel a_cin f0_ordelinel f2_ordelinel p_ordtr2 f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word a_w3a f0_ordelinel f1_ordelinel a_cin a_word f2_ordelinel a_word a_wa f0_ordelinel f1_ordelinel a_cin f0_ordelinel a_wss f0_ordelinel f2_ordelinel a_wcel a_wa f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel a_wi p_syl f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word a_w3a f0_ordelinel f1_ordelinel a_cin f0_ordelinel a_wss f0_ordelinel f2_ordelinel a_wcel f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel p_mpani f0_ordelinel f1_ordelinel p_inss2 f0_ordelinel f1_ordelinel p_ordin f0_ordelinel a_word f1_ordelinel a_word a_wa f0_ordelinel f1_ordelinel a_cin a_word f2_ordelinel a_word p_anim1i f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word f0_ordelinel f1_ordelinel a_cin a_word f2_ordelinel a_word a_wa p_3impa f0_ordelinel f1_ordelinel a_cin f1_ordelinel f2_ordelinel p_ordtr2 f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word a_w3a f0_ordelinel f1_ordelinel a_cin a_word f2_ordelinel a_word a_wa f0_ordelinel f1_ordelinel a_cin f1_ordelinel a_wss f1_ordelinel f2_ordelinel a_wcel a_wa f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel a_wi p_syl f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word a_w3a f0_ordelinel f1_ordelinel a_cin f1_ordelinel a_wss f1_ordelinel f2_ordelinel a_wcel f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel p_mpani f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word a_w3a f0_ordelinel f2_ordelinel a_wcel f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel f1_ordelinel f2_ordelinel a_wcel p_jaod f0_ordelinel a_word f1_ordelinel a_word f2_ordelinel a_word a_w3a f0_ordelinel f1_ordelinel a_cin f2_ordelinel a_wcel f0_ordelinel f2_ordelinel a_wcel f1_ordelinel f2_ordelinel a_wcel a_wo p_impbid $.
$}

$(Property of a subclass of the maximum (i.e. union) of two ordinals.
     (Contributed by NM, 28-Nov-2003.) $)

${
	$v A B C  $.
	f0_ordssun $f class A $.
	f1_ordssun $f class B $.
	f2_ordssun $f class C $.
	p_ordssun $p |- ( ( Ord B /\ Ord C ) -> ( A C_ ( B u. C ) <-> ( A C_ B \/ A C_ C ) ) ) $= f1_ordssun f2_ordssun p_ordtri2or2 f1_ordssun f2_ordssun p_ssequn1 f1_ordssun f2_ordssun a_cun f2_ordssun f0_ordssun p_sseq2 f1_ordssun f2_ordssun a_wss f1_ordssun f2_ordssun a_cun f2_ordssun a_wceq f0_ordssun f1_ordssun f2_ordssun a_cun a_wss f0_ordssun f2_ordssun a_wss a_wb p_sylbi f0_ordssun f2_ordssun a_wss f0_ordssun f1_ordssun a_wss p_olc f1_ordssun f2_ordssun a_wss f0_ordssun f1_ordssun f2_ordssun a_cun a_wss f0_ordssun f2_ordssun a_wss f0_ordssun f1_ordssun a_wss f0_ordssun f2_ordssun a_wss a_wo p_syl6bi f2_ordssun f1_ordssun p_ssequn2 f1_ordssun f2_ordssun a_cun f1_ordssun f0_ordssun p_sseq2 f2_ordssun f1_ordssun a_wss f1_ordssun f2_ordssun a_cun f1_ordssun a_wceq f0_ordssun f1_ordssun f2_ordssun a_cun a_wss f0_ordssun f1_ordssun a_wss a_wb p_sylbi f0_ordssun f1_ordssun a_wss f0_ordssun f2_ordssun a_wss p_orc f2_ordssun f1_ordssun a_wss f0_ordssun f1_ordssun f2_ordssun a_cun a_wss f0_ordssun f1_ordssun a_wss f0_ordssun f1_ordssun a_wss f0_ordssun f2_ordssun a_wss a_wo p_syl6bi f1_ordssun f2_ordssun a_wss f0_ordssun f1_ordssun f2_ordssun a_cun a_wss f0_ordssun f1_ordssun a_wss f0_ordssun f2_ordssun a_wss a_wo a_wi f2_ordssun f1_ordssun a_wss p_jaoi f1_ordssun a_word f2_ordssun a_word a_wa f1_ordssun f2_ordssun a_wss f2_ordssun f1_ordssun a_wss a_wo f0_ordssun f1_ordssun f2_ordssun a_cun a_wss f0_ordssun f1_ordssun a_wss f0_ordssun f2_ordssun a_wss a_wo a_wi p_syl f0_ordssun f1_ordssun f2_ordssun p_ssun f1_ordssun a_word f2_ordssun a_word a_wa f0_ordssun f1_ordssun f2_ordssun a_cun a_wss f0_ordssun f1_ordssun a_wss f0_ordssun f2_ordssun a_wss a_wo p_impbid1 $.
$}

$(The maximum (i.e. union) of two ordinals is either one or the other.
     Similar to Exercise 14 of [TakeutiZaring] p. 40.  (Contributed by NM,
     28-Nov-2003.) $)

${
	$v A B C  $.
	f0_ordequn $f class A $.
	f1_ordequn $f class B $.
	f2_ordequn $f class C $.
	p_ordequn $p |- ( ( Ord B /\ Ord C ) -> ( A = ( B u. C ) -> ( A = B \/ A = C ) ) ) $= f1_ordequn f2_ordequn p_ordtri2or2 f1_ordequn f2_ordequn p_ssequn1 f1_ordequn f2_ordequn a_cun f2_ordequn f0_ordequn p_eqeq2 f1_ordequn f2_ordequn a_wss f1_ordequn f2_ordequn a_cun f2_ordequn a_wceq f0_ordequn f1_ordequn f2_ordequn a_cun a_wceq f0_ordequn f2_ordequn a_wceq a_wb p_sylbi f0_ordequn f2_ordequn a_wceq f0_ordequn f1_ordequn a_wceq p_olc f1_ordequn f2_ordequn a_wss f0_ordequn f1_ordequn f2_ordequn a_cun a_wceq f0_ordequn f2_ordequn a_wceq f0_ordequn f1_ordequn a_wceq f0_ordequn f2_ordequn a_wceq a_wo p_syl6bi f2_ordequn f1_ordequn p_ssequn2 f1_ordequn f2_ordequn a_cun f1_ordequn f0_ordequn p_eqeq2 f2_ordequn f1_ordequn a_wss f1_ordequn f2_ordequn a_cun f1_ordequn a_wceq f0_ordequn f1_ordequn f2_ordequn a_cun a_wceq f0_ordequn f1_ordequn a_wceq a_wb p_sylbi f0_ordequn f1_ordequn a_wceq f0_ordequn f2_ordequn a_wceq p_orc f2_ordequn f1_ordequn a_wss f0_ordequn f1_ordequn f2_ordequn a_cun a_wceq f0_ordequn f1_ordequn a_wceq f0_ordequn f1_ordequn a_wceq f0_ordequn f2_ordequn a_wceq a_wo p_syl6bi f1_ordequn f2_ordequn a_wss f0_ordequn f1_ordequn f2_ordequn a_cun a_wceq f0_ordequn f1_ordequn a_wceq f0_ordequn f2_ordequn a_wceq a_wo a_wi f2_ordequn f1_ordequn a_wss p_jaoi f1_ordequn a_word f2_ordequn a_word a_wa f1_ordequn f2_ordequn a_wss f2_ordequn f1_ordequn a_wss a_wo f0_ordequn f1_ordequn f2_ordequn a_cun a_wceq f0_ordequn f1_ordequn a_wceq f0_ordequn f2_ordequn a_wceq a_wo a_wi p_syl $.
$}

$(The maximum (i.e. union) of two ordinals is ordinal.  Exercise 12 of
     [TakeutiZaring] p. 40.  (Contributed by NM, 28-Nov-2003.) $)

${
	$v A B  $.
	f0_ordun $f class A $.
	f1_ordun $f class B $.
	p_ordun $p |- ( ( Ord A /\ Ord B ) -> Ord ( A u. B ) ) $= f0_ordun f1_ordun a_cun p_eqid f0_ordun f1_ordun a_cun f0_ordun f1_ordun p_ordequn f0_ordun a_word f1_ordun a_word a_wa f0_ordun f1_ordun a_cun f0_ordun f1_ordun a_cun a_wceq f0_ordun f1_ordun a_cun f0_ordun a_wceq f0_ordun f1_ordun a_cun f1_ordun a_wceq a_wo p_mpi f0_ordun f1_ordun a_cun f0_ordun p_ordeq f0_ordun f1_ordun a_cun f0_ordun a_wceq f0_ordun f1_ordun a_cun a_word f0_ordun a_word p_biimprcd f0_ordun f1_ordun a_cun f1_ordun p_ordeq f0_ordun f1_ordun a_cun f1_ordun a_wceq f0_ordun f1_ordun a_cun a_word f1_ordun a_word p_biimprcd f0_ordun a_word f0_ordun f1_ordun a_cun f0_ordun a_wceq f0_ordun f1_ordun a_cun a_word f1_ordun a_word f0_ordun f1_ordun a_cun f1_ordun a_wceq p_jaao f0_ordun a_word f1_ordun a_word a_wa f0_ordun f1_ordun a_cun f0_ordun a_wceq f0_ordun f1_ordun a_cun f1_ordun a_wceq a_wo f0_ordun f1_ordun a_cun a_word p_mpd $.
$}

$(A subclass relationship for union and successor of ordinal classes.
       (Contributed by NM, 28-Nov-2003.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_ordunisssuc $f class A $.
	f1_ordunisssuc $f class B $.
	i0_ordunisssuc $f set x $.
	p_ordunisssuc $p |- ( ( A C_ On /\ Ord B ) -> ( U. A C_ B <-> A C_ suc B ) ) $= f0_ordunisssuc a_con0 i0_ordunisssuc a_sup_set_class p_ssel2 i0_ordunisssuc a_sup_set_class f1_ordunisssuc p_ordsssuc f0_ordunisssuc a_con0 a_wss i0_ordunisssuc a_sup_set_class f0_ordunisssuc a_wcel a_wa i0_ordunisssuc a_sup_set_class a_con0 a_wcel f1_ordunisssuc a_word i0_ordunisssuc a_sup_set_class f1_ordunisssuc a_wss i0_ordunisssuc a_sup_set_class f1_ordunisssuc a_csuc a_wcel a_wb p_sylan f0_ordunisssuc a_con0 a_wss i0_ordunisssuc a_sup_set_class f0_ordunisssuc a_wcel f1_ordunisssuc a_word i0_ordunisssuc a_sup_set_class f1_ordunisssuc a_wss i0_ordunisssuc a_sup_set_class f1_ordunisssuc a_csuc a_wcel a_wb p_an32s f0_ordunisssuc a_con0 a_wss f1_ordunisssuc a_word a_wa i0_ordunisssuc a_sup_set_class f1_ordunisssuc a_wss i0_ordunisssuc a_sup_set_class f1_ordunisssuc a_csuc a_wcel i0_ordunisssuc f0_ordunisssuc p_ralbidva i0_ordunisssuc f0_ordunisssuc f1_ordunisssuc p_unissb i0_ordunisssuc f0_ordunisssuc f1_ordunisssuc a_csuc p_dfss3 f0_ordunisssuc a_con0 a_wss f1_ordunisssuc a_word a_wa i0_ordunisssuc a_sup_set_class f1_ordunisssuc a_wss i0_ordunisssuc f0_ordunisssuc a_wral i0_ordunisssuc a_sup_set_class f1_ordunisssuc a_csuc a_wcel i0_ordunisssuc f0_ordunisssuc a_wral f0_ordunisssuc a_cuni f1_ordunisssuc a_wss f0_ordunisssuc f1_ordunisssuc a_csuc a_wss p_3bitr4g $.
$}

$(The successor operation behaves like a one-to-one function.  Compare
     Exercise 16 of [Enderton] p. 194.  (Contributed by NM, 3-Sep-2003.) $)

${
	$v A B  $.
	f0_suc11 $f class A $.
	f1_suc11 $f class B $.
	p_suc11 $p |- ( ( A e. On /\ B e. On ) -> ( suc A = suc B <-> A = B ) ) $= f0_suc11 p_eloni f0_suc11 f1_suc11 p_ordn2lp f0_suc11 f1_suc11 a_wcel f1_suc11 f0_suc11 a_wcel p_ianor f0_suc11 a_word f0_suc11 f1_suc11 a_wcel f1_suc11 f0_suc11 a_wcel a_wa a_wn f0_suc11 f1_suc11 a_wcel a_wn f1_suc11 f0_suc11 a_wcel a_wn a_wo p_sylib f0_suc11 a_con0 a_wcel f0_suc11 a_word f0_suc11 f1_suc11 a_wcel a_wn f1_suc11 f0_suc11 a_wcel a_wn a_wo p_syl f0_suc11 a_con0 a_wcel f0_suc11 f1_suc11 a_wcel a_wn f1_suc11 f0_suc11 a_wcel a_wn a_wo f1_suc11 a_con0 a_wcel p_adantr f0_suc11 a_csuc f1_suc11 a_csuc p_eqimss f0_suc11 f1_suc11 a_csuc a_con0 p_sucssel f0_suc11 a_csuc f1_suc11 a_csuc a_wceq f0_suc11 a_csuc f1_suc11 a_csuc a_wss f0_suc11 a_con0 a_wcel f0_suc11 f1_suc11 a_csuc a_wcel p_syl5 f0_suc11 f1_suc11 p_elsuci f0_suc11 f1_suc11 a_csuc a_wcel f0_suc11 f1_suc11 a_wcel f0_suc11 f1_suc11 a_wceq p_ord f0_suc11 f1_suc11 a_csuc a_wcel f0_suc11 f1_suc11 a_wcel a_wn f0_suc11 f1_suc11 a_wceq p_com12 f0_suc11 a_con0 a_wcel f0_suc11 a_csuc f1_suc11 a_csuc a_wceq f0_suc11 f1_suc11 a_csuc a_wcel f0_suc11 f1_suc11 a_wcel a_wn f0_suc11 f1_suc11 a_wceq p_syl9 f1_suc11 a_csuc f0_suc11 a_csuc p_eqimss2 f1_suc11 f0_suc11 a_csuc a_con0 p_sucssel f0_suc11 a_csuc f1_suc11 a_csuc a_wceq f1_suc11 a_csuc f0_suc11 a_csuc a_wss f1_suc11 a_con0 a_wcel f1_suc11 f0_suc11 a_csuc a_wcel p_syl5 f1_suc11 f0_suc11 p_elsuci f1_suc11 f0_suc11 a_csuc a_wcel f1_suc11 f0_suc11 a_wcel f1_suc11 f0_suc11 a_wceq p_ord f1_suc11 f0_suc11 a_csuc a_wcel f1_suc11 f0_suc11 a_wcel a_wn f1_suc11 f0_suc11 a_wceq p_com12 f1_suc11 f0_suc11 p_eqcom f1_suc11 f0_suc11 a_wcel a_wn f1_suc11 f0_suc11 a_csuc a_wcel f1_suc11 f0_suc11 a_wceq f0_suc11 f1_suc11 a_wceq p_syl6ib f1_suc11 a_con0 a_wcel f0_suc11 a_csuc f1_suc11 a_csuc a_wceq f1_suc11 f0_suc11 a_csuc a_wcel f1_suc11 f0_suc11 a_wcel a_wn f0_suc11 f1_suc11 a_wceq p_syl9 f0_suc11 a_con0 a_wcel f0_suc11 f1_suc11 a_wcel a_wn f0_suc11 a_csuc f1_suc11 a_csuc a_wceq f0_suc11 f1_suc11 a_wceq a_wi f1_suc11 a_con0 a_wcel f1_suc11 f0_suc11 a_wcel a_wn p_jaao f0_suc11 a_con0 a_wcel f1_suc11 a_con0 a_wcel a_wa f0_suc11 f1_suc11 a_wcel a_wn f1_suc11 f0_suc11 a_wcel a_wn a_wo f0_suc11 a_csuc f1_suc11 a_csuc a_wceq f0_suc11 f1_suc11 a_wceq a_wi p_mpd f0_suc11 f1_suc11 p_suceq f0_suc11 a_con0 a_wcel f1_suc11 a_con0 a_wcel a_wa f0_suc11 a_csuc f1_suc11 a_csuc a_wceq f0_suc11 f1_suc11 a_wceq p_impbid1 $.
$}

$(An ordinal number is an ordinal class.  (Contributed by NM,
       11-Jun-1994.) $)

${
	$v A  $.
	f0_onordi $f class A $.
	e0_onordi $e |- A e. On $.
	p_onordi $p |- Ord A $= e0_onordi f0_onordi p_eloni f0_onordi a_con0 a_wcel f0_onordi a_word a_ax-mp $.
$}

$(An ordinal number is a transitive class.  (Contributed by NM,
       11-Jun-1994.) $)

${
	$v A  $.
	f0_ontrci $f class A $.
	e0_ontrci $e |- A e. On $.
	p_ontrci $p |- Tr A $= e0_ontrci f0_ontrci p_onordi f0_ontrci p_ordtr f0_ontrci a_word f0_ontrci a_wtr a_ax-mp $.
$}

$(An ordinal number is not a member of itself.  Theorem 7M(c) of
       [Enderton] p. 192.  (Contributed by NM, 11-Jun-1994.) $)

${
	$v A  $.
	f0_onirri $f class A $.
	e0_onirri $e |- A e. On $.
	p_onirri $p |- -. A e. A $= e0_onirri f0_onirri p_onordi f0_onirri p_ordirr f0_onirri a_word f0_onirri f0_onirri a_wcel a_wn a_ax-mp $.
$}

$(A member of an ordinal number is an ordinal number.  Theorem 7M(a) of
       [Enderton] p. 192.  (Contributed by NM, 11-Jun-1994.) $)

${
	$v A B  $.
	f0_oneli $f class A $.
	f1_oneli $f class B $.
	e0_oneli $e |- A e. On $.
	p_oneli $p |- ( B e. A -> B e. On ) $= e0_oneli f0_oneli f1_oneli p_onelon f0_oneli a_con0 a_wcel f1_oneli f0_oneli a_wcel f1_oneli a_con0 a_wcel p_mpan $.
$}

$(A member of an ordinal number is a subset of it.  (Contributed by NM,
       11-Aug-1994.) $)

${
	$v A B  $.
	f0_onelssi $f class A $.
	f1_onelssi $f class B $.
	e0_onelssi $e |- A e. On $.
	p_onelssi $p |- ( B e. A -> B C_ A ) $= e0_onelssi f0_onelssi f1_onelssi p_onelss f0_onelssi a_con0 a_wcel f1_onelssi f0_onelssi a_wcel f1_onelssi f0_onelssi a_wss a_wi a_ax-mp $.
$}

$(An ordering law for ordinal numbers.  (Contributed by NM,
       13-Jun-1994.) $)

${
	$v A B  $.
	f0_onssneli $f class A $.
	f1_onssneli $f class B $.
	e0_onssneli $e |- A e. On $.
	p_onssneli $p |- ( A C_ B -> -. B e. A ) $= e0_onssneli f0_onssneli f1_onssneli p_oneli f1_onssneli p_eloni f1_onssneli p_ordirr f1_onssneli f0_onssneli a_wcel f1_onssneli a_con0 a_wcel f1_onssneli a_word f1_onssneli f1_onssneli a_wcel a_wn p_3syl f0_onssneli f1_onssneli f1_onssneli p_ssel f0_onssneli f1_onssneli a_wss f1_onssneli f0_onssneli a_wcel f1_onssneli f1_onssneli a_wcel p_com12 f1_onssneli f0_onssneli a_wcel f0_onssneli f1_onssneli a_wss f1_onssneli f1_onssneli a_wcel p_mtod f1_onssneli f0_onssneli a_wcel f0_onssneli f1_onssneli a_wss p_con2i $.
$}

$(An ordering law for ordinal numbers.  (Contributed by NM,
       13-Jun-1994.) $)

${
	$v A B  $.
	f0_onssnel2i $f class A $.
	f1_onssnel2i $f class B $.
	e0_onssnel2i $e |- A e. On $.
	p_onssnel2i $p |- ( B C_ A -> -. A e. B ) $= e0_onssnel2i f0_onssnel2i p_onirri f1_onssnel2i f0_onssnel2i f0_onssnel2i p_ssel f1_onssnel2i f0_onssnel2i a_wss f0_onssnel2i f1_onssnel2i a_wcel f0_onssnel2i f0_onssnel2i a_wcel p_mtoi $.
$}

$(An element of an ordinal number equals the intersection with it.
       (Contributed by NM, 11-Jun-1994.) $)

${
	$v A B  $.
	f0_onelini $f class A $.
	f1_onelini $f class B $.
	e0_onelini $e |- A e. On $.
	p_onelini $p |- ( B e. A -> B = ( B i^i A ) ) $= e0_onelini f0_onelini f1_onelini p_onelssi f1_onelini f0_onelini p_dfss f1_onelini f0_onelini a_wcel f1_onelini f0_onelini a_wss f1_onelini f1_onelini f0_onelini a_cin a_wceq p_sylib $.
$}

$(An ordinal number equals its union with any element.  (Contributed by
       NM, 13-Jun-1994.) $)

${
	$v A B  $.
	f0_oneluni $f class A $.
	f1_oneluni $f class B $.
	e0_oneluni $e |- A e. On $.
	p_oneluni $p |- ( B e. A -> ( A u. B ) = A ) $= e0_oneluni f0_oneluni f1_oneluni p_onelssi f1_oneluni f0_oneluni p_ssequn2 f1_oneluni f0_oneluni a_wcel f1_oneluni f0_oneluni a_wss f0_oneluni f1_oneluni a_cun f0_oneluni a_wceq p_sylib $.
$}

$(An ordinal number is equal to the union of its successor.  (Contributed
       by NM, 12-Jun-1994.) $)

${
	$v A  $.
	f0_onunisuci $f class A $.
	e0_onunisuci $e |- A e. On $.
	p_onunisuci $p |- U. suc A = A $= e0_onunisuci f0_onunisuci p_ontrci e0_onunisuci f0_onunisuci a_con0 p_elexi f0_onunisuci p_unisuc f0_onunisuci a_wtr f0_onunisuci a_csuc a_cuni f0_onunisuci a_wceq p_mpbi $.
$}

$(Subset is equivalent to membership or equality for ordinal numbers.
         (Contributed by NM, 15-Sep-1995.) $)

${
	$v A B  $.
	f0_onsseli $f class A $.
	f1_onsseli $f class B $.
	e0_onsseli $e |- A e. On $.
	e1_onsseli $e |- B e. On $.
	p_onsseli $p |- ( A C_ B <-> ( A e. B \/ A = B ) ) $= e0_onsseli e1_onsseli f0_onsseli f1_onsseli p_onsseleq f0_onsseli a_con0 a_wcel f1_onsseli a_con0 a_wcel f0_onsseli f1_onsseli a_wss f0_onsseli f1_onsseli a_wcel f0_onsseli f1_onsseli a_wceq a_wo a_wb p_mp2an $.
$}

$(The union of two ordinal numbers is an ordinal number.  (Contributed
         by NM, 13-Jun-1994.) $)

${
	$v A B  $.
	f0_onun2i $f class A $.
	f1_onun2i $f class B $.
	e0_onun2i $e |- A e. On $.
	e1_onun2i $e |- B e. On $.
	p_onun2i $p |- ( A u. B ) e. On $= e1_onun2i f1_onun2i p_onordi e0_onun2i f0_onun2i p_onordi f1_onun2i f0_onun2i p_ordtri2or f1_onun2i a_word f0_onun2i a_word f1_onun2i f0_onun2i a_wcel f0_onun2i f1_onun2i a_wss a_wo p_mp2an e0_onun2i f0_onun2i f1_onun2i p_oneluni e0_onun2i f1_onun2i f0_onun2i a_wcel f0_onun2i f1_onun2i a_cun f0_onun2i a_con0 p_syl6eqel f0_onun2i f1_onun2i p_ssequn1 e1_onun2i f0_onun2i f1_onun2i a_cun f1_onun2i a_con0 p_eleq1 f0_onun2i f1_onun2i a_cun f1_onun2i a_wceq f0_onun2i f1_onun2i a_cun a_con0 a_wcel f1_onun2i a_con0 a_wcel p_mpbiri f0_onun2i f1_onun2i a_wss f0_onun2i f1_onun2i a_cun f1_onun2i a_wceq f0_onun2i f1_onun2i a_cun a_con0 a_wcel p_sylbi f1_onun2i f0_onun2i a_wcel f0_onun2i f1_onun2i a_cun a_con0 a_wcel f0_onun2i f1_onun2i a_wss p_jaoi f1_onun2i f0_onun2i a_wcel f0_onun2i f1_onun2i a_wss a_wo f0_onun2i f1_onun2i a_cun a_con0 a_wcel a_ax-mp $.
$}

$(An ordinal equal to its own union is either zero or a limit ordinal.
     (Contributed by NM, 1-Oct-2003.) $)

${
	$v A  $.
	f0_unizlim $f class A $.
	p_unizlim $p |- ( Ord A -> ( A = U. A <-> ( A = (/) \/ Lim A ) ) ) $= f0_unizlim a_c0 a_df-ne f0_unizlim a_df-lim f0_unizlim a_wlim f0_unizlim a_word f0_unizlim a_c0 a_wne f0_unizlim f0_unizlim a_cuni a_wceq a_w3a p_biimpri f0_unizlim a_word f0_unizlim a_c0 a_wne f0_unizlim f0_unizlim a_cuni a_wceq f0_unizlim a_wlim p_3exp f0_unizlim a_c0 a_wceq a_wn f0_unizlim a_c0 a_wne f0_unizlim a_word f0_unizlim f0_unizlim a_cuni a_wceq f0_unizlim a_wlim a_wi p_syl5bir f0_unizlim a_word f0_unizlim a_c0 a_wceq a_wn f0_unizlim f0_unizlim a_cuni a_wceq f0_unizlim a_wlim p_com23 f0_unizlim a_word f0_unizlim f0_unizlim a_cuni a_wceq f0_unizlim a_c0 a_wceq a_wn f0_unizlim a_wlim a_wi p_imp f0_unizlim a_word f0_unizlim f0_unizlim a_cuni a_wceq a_wa f0_unizlim a_c0 a_wceq f0_unizlim a_wlim p_orrd f0_unizlim a_word f0_unizlim f0_unizlim a_cuni a_wceq f0_unizlim a_c0 a_wceq f0_unizlim a_wlim a_wo p_ex p_uni0 a_c0 a_cuni a_c0 p_eqcomi f0_unizlim a_c0 a_wceq p_id f0_unizlim a_c0 p_unieq f0_unizlim a_c0 a_wceq a_c0 a_c0 a_cuni f0_unizlim f0_unizlim a_cuni p_3eqtr4a f0_unizlim p_limuni f0_unizlim a_c0 a_wceq f0_unizlim f0_unizlim a_cuni a_wceq f0_unizlim a_wlim p_jaoi f0_unizlim a_word f0_unizlim f0_unizlim a_cuni a_wceq f0_unizlim a_c0 a_wceq f0_unizlim a_wlim a_wo p_impbid1 $.
$}

$(An ordinal number either equals zero or contains zero.  (Contributed by
     NM, 1-Jun-2004.) $)

${
	$v A  $.
	f0_on0eqel $f class A $.
	p_on0eqel $p |- ( A e. On -> ( A = (/) \/ (/) e. A ) ) $= f0_on0eqel p_0ss p_0elon a_c0 f0_on0eqel p_onsseleq a_c0 a_con0 a_wcel f0_on0eqel a_con0 a_wcel a_c0 f0_on0eqel a_wss a_c0 f0_on0eqel a_wcel a_c0 f0_on0eqel a_wceq a_wo a_wb p_mpan f0_on0eqel a_con0 a_wcel a_c0 f0_on0eqel a_wss a_c0 f0_on0eqel a_wcel a_c0 f0_on0eqel a_wceq a_wo p_mpbii a_c0 f0_on0eqel p_eqcom a_c0 f0_on0eqel a_wceq f0_on0eqel a_c0 a_wceq a_c0 f0_on0eqel a_wcel p_orbi2i a_c0 f0_on0eqel a_wcel f0_on0eqel a_c0 a_wceq p_orcom a_c0 f0_on0eqel a_wcel a_c0 f0_on0eqel a_wceq a_wo a_c0 f0_on0eqel a_wcel f0_on0eqel a_c0 a_wceq a_wo f0_on0eqel a_c0 a_wceq a_c0 f0_on0eqel a_wcel a_wo p_bitri f0_on0eqel a_con0 a_wcel a_c0 f0_on0eqel a_wcel a_c0 f0_on0eqel a_wceq a_wo f0_on0eqel a_c0 a_wceq a_c0 f0_on0eqel a_wcel a_wo p_sylib $.
$}

$(The singleton of the singleton of the empty set is not an ordinal (nor a
     natural number by ~ omsson ).  It can be used to represent an "undefined"
     value for a partial operation on natural or ordinal numbers.  See also
     ~ onxpdisj .  (Contributed by NM, 21-May-2004.)  (Proof shortened by
     Andrew Salmon, 12-Aug-2011.) $)

${
	$v  $.
	p_snsn0non $p |- -. { { (/) } } e. On $= p_p0ex a_c0 a_csn p_snid a_c0 a_csn a_csn a_c0 a_csn p_n0i a_c0 a_csn a_c0 a_csn a_csn a_wcel a_c0 a_csn a_csn a_c0 a_wceq a_wn a_ax-mp p_0ex a_c0 p_snid a_c0 a_csn a_c0 p_n0i a_c0 a_c0 a_csn a_wcel a_c0 a_csn a_c0 a_wceq a_wn a_ax-mp a_c0 a_c0 a_csn p_eqcom a_c0 a_c0 a_csn a_wceq a_c0 a_csn a_c0 a_wceq p_mtbir p_0ex a_c0 a_c0 a_csn p_elsnc a_c0 a_c0 a_csn a_csn a_wcel a_c0 a_c0 a_csn a_wceq p_mtbir a_c0 a_csn a_csn a_c0 a_wceq a_c0 a_c0 a_csn a_csn a_wcel p_pm3.2ni a_c0 a_csn a_csn p_on0eqel a_c0 a_csn a_csn a_con0 a_wcel a_c0 a_csn a_csn a_c0 a_wceq a_c0 a_c0 a_csn a_csn a_wcel a_wo p_mto $.
$}


