$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_disjunction_and_conjunction.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Miscellaneous theorems of propositional calculus

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Eliminate an antecedent implied by each side of a biconditional.
       (Contributed by NM, 20-Nov-2005.)  (Proof shortened by Wolf Lammen,
       4-Nov-2013.) $)

${
	$v ph ps ch th  $.
	f0_pm5.21nd $f wff ph $.
	f1_pm5.21nd $f wff ps $.
	f2_pm5.21nd $f wff ch $.
	f3_pm5.21nd $f wff th $.
	e0_pm5.21nd $e |- ( ( ph /\ ps ) -> th ) $.
	e1_pm5.21nd $e |- ( ( ph /\ ch ) -> th ) $.
	e2_pm5.21nd $e |- ( th -> ( ps <-> ch ) ) $.
	p_pm5.21nd $p |- ( ph -> ( ps <-> ch ) ) $= e0_pm5.21nd f0_pm5.21nd f1_pm5.21nd f3_pm5.21nd p_ex e1_pm5.21nd f0_pm5.21nd f2_pm5.21nd f3_pm5.21nd p_ex e2_pm5.21nd f3_pm5.21nd f1_pm5.21nd f2_pm5.21nd a_wb a_wi f0_pm5.21nd p_a1i f0_pm5.21nd f3_pm5.21nd f1_pm5.21nd f2_pm5.21nd p_pm5.21ndd $.
$}

$(Theorem *5.35 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm5.35 $f wff ph $.
	f1_pm5.35 $f wff ps $.
	f2_pm5.35 $f wff ch $.
	p_pm5.35 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) -> ( ph -> ( ps <-> ch ) ) ) $= f0_pm5.35 f1_pm5.35 a_wi f0_pm5.35 f2_pm5.35 a_wi p_pm5.1 f0_pm5.35 f1_pm5.35 a_wi f0_pm5.35 f2_pm5.35 a_wi a_wa f0_pm5.35 f1_pm5.35 f2_pm5.35 p_pm5.74rd $.
$}

$(Theorem *5.54 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 7-Nov-2013.) $)

${
	$v ph ps  $.
	f0_pm5.54 $f wff ph $.
	f1_pm5.54 $f wff ps $.
	p_pm5.54 $p |- ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) ) $= f1_pm5.54 f0_pm5.54 p_iba f1_pm5.54 f0_pm5.54 f0_pm5.54 f1_pm5.54 a_wa p_bicomd f1_pm5.54 f0_pm5.54 f1_pm5.54 a_wa f0_pm5.54 a_wb f0_pm5.54 p_adantl f1_pm5.54 f0_pm5.54 p_iba f1_pm5.54 f0_pm5.54 f0_pm5.54 f1_pm5.54 a_wa p_bicomd f0_pm5.54 f1_pm5.54 a_wa f0_pm5.54 f1_pm5.54 a_wa f0_pm5.54 a_wb f1_pm5.54 p_pm5.21ni f0_pm5.54 f1_pm5.54 a_wa f0_pm5.54 a_wb f0_pm5.54 f1_pm5.54 a_wa f1_pm5.54 a_wb p_orri $.
$}

$(Move conjunction outside of biconditional.  (Contributed by NM,
       13-May-1999.) $)

${
	$v ph ps ch  $.
	f0_baib $f wff ph $.
	f1_baib $f wff ps $.
	f2_baib $f wff ch $.
	e0_baib $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_baib $p |- ( ps -> ( ph <-> ch ) ) $= f1_baib f2_baib p_ibar e0_baib f1_baib f2_baib f1_baib f2_baib a_wa f0_baib p_syl6rbbr $.
$}

$(Move conjunction outside of biconditional.  (Contributed by NM,
       11-Jul-1994.) $)

${
	$v ph ps ch  $.
	f0_baibr $f wff ph $.
	f1_baibr $f wff ps $.
	f2_baibr $f wff ch $.
	e0_baibr $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_baibr $p |- ( ps -> ( ch <-> ph ) ) $= e0_baibr f0_baibr f1_baibr f2_baibr p_baib f1_baibr f0_baibr f2_baibr p_bicomd $.
$}

$(Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)

${
	$v ph ps ch  $.
	f0_rbaib $f wff ph $.
	f1_rbaib $f wff ps $.
	f2_rbaib $f wff ch $.
	e0_rbaib $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_rbaib $p |- ( ch -> ( ph <-> ps ) ) $= e0_rbaib f1_rbaib f2_rbaib p_ancom f0_rbaib f1_rbaib f2_rbaib a_wa f2_rbaib f1_rbaib a_wa p_bitri f0_rbaib f2_rbaib f1_rbaib p_baib $.
$}

$(Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)

${
	$v ph ps ch  $.
	f0_rbaibr $f wff ph $.
	f1_rbaibr $f wff ps $.
	f2_rbaibr $f wff ch $.
	e0_rbaibr $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_rbaibr $p |- ( ch -> ( ps <-> ph ) ) $= e0_rbaibr f1_rbaibr f2_rbaibr p_ancom f0_rbaibr f1_rbaibr f2_rbaibr a_wa f2_rbaibr f1_rbaibr a_wa p_bitri f0_rbaibr f2_rbaibr f1_rbaibr p_baibr $.
$}

$(Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)

${
	$v ph ps ch th  $.
	f0_baibd $f wff ph $.
	f1_baibd $f wff ps $.
	f2_baibd $f wff ch $.
	f3_baibd $f wff th $.
	e0_baibd $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	p_baibd $p |- ( ( ph /\ ch ) -> ( ps <-> th ) ) $= e0_baibd f2_baibd f3_baibd p_ibar f2_baibd f3_baibd f2_baibd f3_baibd a_wa p_bicomd f0_baibd f1_baibd f2_baibd f3_baibd a_wa f2_baibd f3_baibd p_sylan9bb $.
$}

$(Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)

${
	$v ph ps ch th  $.
	f0_rbaibd $f wff ph $.
	f1_rbaibd $f wff ps $.
	f2_rbaibd $f wff ch $.
	f3_rbaibd $f wff th $.
	e0_rbaibd $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	p_rbaibd $p |- ( ( ph /\ th ) -> ( ps <-> ch ) ) $= e0_rbaibd f3_rbaibd f2_rbaibd p_iba f3_rbaibd f2_rbaibd f2_rbaibd f3_rbaibd a_wa p_bicomd f0_rbaibd f1_rbaibd f2_rbaibd f3_rbaibd a_wa f3_rbaibd f2_rbaibd p_sylan9bb $.
$}

$(Theorem *5.44 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm5.44 $f wff ph $.
	f1_pm5.44 $f wff ps $.
	f2_pm5.44 $f wff ch $.
	p_pm5.44 $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) <-> ( ph -> ( ps /\ ch ) ) ) ) $= f0_pm5.44 f1_pm5.44 f2_pm5.44 p_jcab f0_pm5.44 f1_pm5.44 f2_pm5.44 a_wa a_wi f0_pm5.44 f1_pm5.44 a_wi f0_pm5.44 f2_pm5.44 a_wi p_baibr $.
$}

$(Conjunction in antecedent versus disjunction in consequent.  Theorem *5.6
     of [WhiteheadRussell] p. 125.  (Contributed by NM, 8-Jun-1994.) $)

${
	$v ph ps ch  $.
	f0_pm5.6 $f wff ph $.
	f1_pm5.6 $f wff ps $.
	f2_pm5.6 $f wff ch $.
	p_pm5.6 $p |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ) $= f0_pm5.6 f1_pm5.6 a_wn f2_pm5.6 p_impexp f1_pm5.6 f2_pm5.6 a_df-or f1_pm5.6 f2_pm5.6 a_wo f1_pm5.6 a_wn f2_pm5.6 a_wi f0_pm5.6 p_imbi2i f0_pm5.6 f1_pm5.6 a_wn a_wa f2_pm5.6 a_wi f0_pm5.6 f1_pm5.6 a_wn f2_pm5.6 a_wi a_wi f0_pm5.6 f1_pm5.6 f2_pm5.6 a_wo a_wi p_bitr4i $.
$}

$(Change disjunction in consequent to conjunction in antecedent.
       (Contributed by NM, 8-Jun-1994.) $)

${
	$v ph ps ch  $.
	f0_orcanai $f wff ph $.
	f1_orcanai $f wff ps $.
	f2_orcanai $f wff ch $.
	e0_orcanai $e |- ( ph -> ( ps \/ ch ) ) $.
	p_orcanai $p |- ( ( ph /\ -. ps ) -> ch ) $= e0_orcanai f0_orcanai f1_orcanai f2_orcanai p_ord f0_orcanai f1_orcanai a_wn f2_orcanai p_imp $.
$}

$(Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       16-Sep-1993.) $)

${
	$v ph ps  $.
	f0_intnan $f wff ph $.
	f1_intnan $f wff ps $.
	e0_intnan $e |- -. ph $.
	p_intnan $p |- -. ( ps /\ ph ) $= e0_intnan f1_intnan f0_intnan p_simpr f1_intnan f0_intnan a_wa f0_intnan p_mto $.
$}

$(Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       3-Apr-1995.) $)

${
	$v ph ps  $.
	f0_intnanr $f wff ph $.
	f1_intnanr $f wff ps $.
	e0_intnanr $e |- -. ph $.
	p_intnanr $p |- -. ( ph /\ ps ) $= e0_intnanr f0_intnanr f1_intnanr p_simpl f0_intnanr f1_intnanr a_wa f0_intnanr p_mto $.
$}

$(Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) $)

${
	$v ph ps ch  $.
	f0_intnand $f wff ph $.
	f1_intnand $f wff ps $.
	f2_intnand $f wff ch $.
	e0_intnand $e |- ( ph -> -. ps ) $.
	p_intnand $p |- ( ph -> -. ( ch /\ ps ) ) $= e0_intnand f2_intnand f1_intnand p_simpr f0_intnand f1_intnand f2_intnand f1_intnand a_wa p_nsyl $.
$}

$(Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) $)

${
	$v ph ps ch  $.
	f0_intnanrd $f wff ph $.
	f1_intnanrd $f wff ps $.
	f2_intnanrd $f wff ch $.
	e0_intnanrd $e |- ( ph -> -. ps ) $.
	p_intnanrd $p |- ( ph -> -. ( ps /\ ch ) ) $= e0_intnanrd f1_intnanrd f2_intnanrd p_simpl f0_intnanrd f1_intnanrd f1_intnanrd f2_intnanrd a_wa p_nsyl $.
$}

$(Detach truth from conjunction in biconditional.  (Contributed by NM,
       27-Feb-1996.) $)

${
	$v ph ps ch  $.
	f0_mpbiran $f wff ph $.
	f1_mpbiran $f wff ps $.
	f2_mpbiran $f wff ch $.
	e0_mpbiran $e |- ps $.
	e1_mpbiran $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_mpbiran $p |- ( ph <-> ch ) $= e1_mpbiran e0_mpbiran f1_mpbiran f2_mpbiran p_biantrur f0_mpbiran f1_mpbiran f2_mpbiran a_wa f2_mpbiran p_bitr4i $.
$}

$(Detach truth from conjunction in biconditional.  (Contributed by NM,
       22-Feb-1996.) $)

${
	$v ph ps ch  $.
	f0_mpbiran2 $f wff ph $.
	f1_mpbiran2 $f wff ps $.
	f2_mpbiran2 $f wff ch $.
	e0_mpbiran2 $e |- ch $.
	e1_mpbiran2 $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_mpbiran2 $p |- ( ph <-> ps ) $= e1_mpbiran2 e0_mpbiran2 f2_mpbiran2 f1_mpbiran2 p_biantru f0_mpbiran2 f1_mpbiran2 f2_mpbiran2 a_wa f1_mpbiran2 p_bitr4i $.
$}

$(Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       10-May-2005.) $)

${
	$v ph ps ch  $.
	f0_mpbir2an $f wff ph $.
	f1_mpbir2an $f wff ps $.
	f2_mpbir2an $f wff ch $.
	e0_mpbir2an $e |- ps $.
	e1_mpbir2an $e |- ch $.
	e2_mpbir2an $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_mpbir2an $p |- ph $= e1_mpbir2an e0_mpbir2an e2_mpbir2an f0_mpbir2an f1_mpbir2an f2_mpbir2an p_mpbiran f0_mpbir2an f2_mpbir2an p_mpbir $.
$}

$(Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       6-Nov-2011.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_mpbi2and $f wff ph $.
	f1_mpbi2and $f wff ps $.
	f2_mpbi2and $f wff ch $.
	f3_mpbi2and $f wff th $.
	e0_mpbi2and $e |- ( ph -> ps ) $.
	e1_mpbi2and $e |- ( ph -> ch ) $.
	e2_mpbi2and $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
	p_mpbi2and $p |- ( ph -> th ) $= e0_mpbi2and e1_mpbi2and f0_mpbi2and f1_mpbi2and f2_mpbi2and p_jca e2_mpbi2and f0_mpbi2and f1_mpbi2and f2_mpbi2and a_wa f3_mpbi2and p_mpbid $.
$}

$(Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       6-Nov-2011.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_mpbir2and $f wff ph $.
	f1_mpbir2and $f wff ps $.
	f2_mpbir2and $f wff ch $.
	f3_mpbir2and $f wff th $.
	e0_mpbir2and $e |- ( ph -> ch ) $.
	e1_mpbir2and $e |- ( ph -> th ) $.
	e2_mpbir2and $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	p_mpbir2and $p |- ( ph -> ps ) $= e0_mpbir2and e1_mpbir2and f0_mpbir2and f2_mpbir2and f3_mpbir2and p_jca e2_mpbir2and f0_mpbir2and f1_mpbir2and f2_mpbir2and f3_mpbir2and a_wa p_mpbird $.
$}

$(Theorem *5.62 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)

${
	$v ph ps  $.
	f0_pm5.62 $f wff ph $.
	f1_pm5.62 $f wff ps $.
	p_pm5.62 $p |- ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) ) $= f1_pm5.62 p_exmid f0_pm5.62 f1_pm5.62 f1_pm5.62 a_wn p_ordir f0_pm5.62 f1_pm5.62 a_wa f1_pm5.62 a_wn a_wo f0_pm5.62 f1_pm5.62 a_wn a_wo f1_pm5.62 f1_pm5.62 a_wn a_wo p_mpbiran2 $.
$}

$(Theorem *5.63 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 25-Dec-2012.) $)

${
	$v ph ps  $.
	f0_pm5.63 $f wff ph $.
	f1_pm5.63 $f wff ps $.
	p_pm5.63 $p |- ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) ) $= f0_pm5.63 p_exmid f0_pm5.63 f0_pm5.63 a_wn f1_pm5.63 p_ordi f0_pm5.63 f0_pm5.63 a_wn f1_pm5.63 a_wa a_wo f0_pm5.63 f0_pm5.63 a_wn a_wo f0_pm5.63 f1_pm5.63 a_wo p_mpbiran f0_pm5.63 f0_pm5.63 a_wn f1_pm5.63 a_wa a_wo f0_pm5.63 f1_pm5.63 a_wo p_bicomi $.
$}

$(A wff conjoined with falsehood is false.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)

${
	$v ph ps  $.
	f0_bianfi $f wff ph $.
	f1_bianfi $f wff ps $.
	e0_bianfi $e |- -. ph $.
	p_bianfi $p |- ( ph <-> ( ps /\ ph ) ) $= e0_bianfi e0_bianfi f0_bianfi f1_bianfi p_intnan f0_bianfi f1_bianfi f0_bianfi a_wa p_2false $.
$}

$(A wff conjoined with falsehood is false.  (Contributed by NM,
       27-Mar-1995.)  (Proof shortened by Wolf Lammen, 5-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_bianfd $f wff ph $.
	f1_bianfd $f wff ps $.
	f2_bianfd $f wff ch $.
	e0_bianfd $e |- ( ph -> -. ps ) $.
	p_bianfd $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $= e0_bianfd e0_bianfd f0_bianfd f1_bianfd f2_bianfd p_intnanrd f0_bianfd f1_bianfd f1_bianfd f2_bianfd a_wa p_2falsed $.
$}

$(Theorem *4.43 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)

${
	$v ph ps  $.
	f0_pm4.43 $f wff ph $.
	f1_pm4.43 $f wff ps $.
	p_pm4.43 $p |- ( ph <-> ( ( ph \/ ps ) /\ ( ph \/ -. ps ) ) ) $= f1_pm4.43 p_pm3.24 f1_pm4.43 f1_pm4.43 a_wn a_wa f0_pm4.43 p_biorfi f0_pm4.43 f1_pm4.43 f1_pm4.43 a_wn p_ordi f0_pm4.43 f0_pm4.43 f1_pm4.43 f1_pm4.43 a_wn a_wa a_wo f0_pm4.43 f1_pm4.43 a_wo f0_pm4.43 f1_pm4.43 a_wn a_wo a_wa p_bitri $.
$}

$(Theorem *4.82 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.82 $f wff ph $.
	f1_pm4.82 $f wff ps $.
	p_pm4.82 $p |- ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph ) $= f0_pm4.82 f1_pm4.82 p_pm2.65 f0_pm4.82 f1_pm4.82 a_wi f0_pm4.82 f1_pm4.82 a_wn a_wi f0_pm4.82 a_wn p_imp f0_pm4.82 f1_pm4.82 p_pm2.21 f0_pm4.82 f1_pm4.82 a_wn p_pm2.21 f0_pm4.82 a_wn f0_pm4.82 f1_pm4.82 a_wi f0_pm4.82 f1_pm4.82 a_wn a_wi p_jca f0_pm4.82 f1_pm4.82 a_wi f0_pm4.82 f1_pm4.82 a_wn a_wi a_wa f0_pm4.82 a_wn p_impbii $.
$}

$(Theorem *4.83 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.83 $f wff ph $.
	f1_pm4.83 $f wff ps $.
	p_pm4.83 $p |- ( ( ( ph -> ps ) /\ ( -. ph -> ps ) ) <-> ps ) $= f0_pm4.83 p_exmid f0_pm4.83 f0_pm4.83 a_wn a_wo f1_pm4.83 p_a1bi f0_pm4.83 f1_pm4.83 f0_pm4.83 a_wn p_jaob f1_pm4.83 f0_pm4.83 f0_pm4.83 a_wn a_wo f1_pm4.83 a_wi f0_pm4.83 f1_pm4.83 a_wi f0_pm4.83 a_wn f1_pm4.83 a_wi a_wa p_bitr2i $.
$}

$(Negation inferred from embedded conjunct.  (Contributed by NM,
     20-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-Nov-2012.) $)

${
	$v ph ps  $.
	f0_pclem6 $f wff ph $.
	f1_pclem6 $f wff ps $.
	p_pclem6 $p |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps ) $= f1_pclem6 f0_pclem6 a_wn p_ibar f0_pclem6 f1_pclem6 f0_pclem6 a_wn a_wa p_nbbn f1_pclem6 f0_pclem6 a_wn f1_pclem6 f0_pclem6 a_wn a_wa a_wb f0_pclem6 f1_pclem6 f0_pclem6 a_wn a_wa a_wb a_wn p_sylib f1_pclem6 f0_pclem6 f1_pclem6 f0_pclem6 a_wn a_wa a_wb p_con2i $.
$}

$(A transitive law of equivalence.  Compare Theorem *4.22 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 18-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_biantr $f wff ph $.
	f1_biantr $f wff ps $.
	f2_biantr $f wff ch $.
	p_biantr $p |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ) $= f2_biantr f1_biantr a_wb p_id f2_biantr f1_biantr a_wb f2_biantr f1_biantr f0_biantr p_bibi2d f2_biantr f1_biantr a_wb f0_biantr f2_biantr a_wb f0_biantr f1_biantr a_wb p_biimparc $.
$}

$(Disjunction distributes over the biconditional.  An axiom of system DS in
     Vladimir Lifschitz, "On calculational proofs" (1998),
     ~ http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.3384 .
     (Contributed by NM, 8-Jan-2005.)  (Proof shortened by Wolf Lammen,
     4-Feb-2013.) $)

${
	$v ph ps ch  $.
	f0_orbidi $f wff ph $.
	f1_orbidi $f wff ps $.
	f2_orbidi $f wff ch $.
	p_orbidi $p |- ( ( ph \/ ( ps <-> ch ) ) <-> ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ) $= f0_orbidi a_wn f1_orbidi f2_orbidi p_pm5.74 f0_orbidi f1_orbidi f2_orbidi a_wb a_df-or f0_orbidi f1_orbidi a_df-or f0_orbidi f2_orbidi a_df-or f0_orbidi f1_orbidi a_wo f0_orbidi a_wn f1_orbidi a_wi f0_orbidi f2_orbidi a_wo f0_orbidi a_wn f2_orbidi a_wi p_bibi12i f0_orbidi a_wn f1_orbidi f2_orbidi a_wb a_wi f0_orbidi a_wn f1_orbidi a_wi f0_orbidi a_wn f2_orbidi a_wi a_wb f0_orbidi f1_orbidi f2_orbidi a_wb a_wo f0_orbidi f1_orbidi a_wo f0_orbidi f2_orbidi a_wo a_wb p_3bitr4i $.
$}

$(Lukasiewicz's shortest axiom for equivalential calculus.  Storrs McCall,
     ed., _Polish Logic 1920-1939_ (Oxford, 1967), p. 96.  (Contributed by NM,
     10-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_biluk $f wff ph $.
	f1_biluk $f wff ps $.
	f2_biluk $f wff ch $.
	p_biluk $p |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) $= f0_biluk f1_biluk p_bicom f0_biluk f1_biluk a_wb f1_biluk f0_biluk a_wb f2_biluk p_bibi1i f1_biluk f0_biluk f2_biluk p_biass f0_biluk f1_biluk a_wb f2_biluk a_wb f1_biluk f0_biluk a_wb f2_biluk a_wb f1_biluk f0_biluk f2_biluk a_wb a_wb p_bitri f0_biluk f1_biluk a_wb f2_biluk f1_biluk f0_biluk f2_biluk a_wb a_wb p_biass f0_biluk f1_biluk a_wb f2_biluk a_wb f1_biluk f0_biluk f2_biluk a_wb a_wb a_wb f0_biluk f1_biluk a_wb f2_biluk f1_biluk f0_biluk f2_biluk a_wb a_wb a_wb a_wb p_mpbi f2_biluk f1_biluk f0_biluk f2_biluk a_wb p_biass f0_biluk f1_biluk a_wb f2_biluk f1_biluk f0_biluk f2_biluk a_wb a_wb a_wb f2_biluk f1_biluk a_wb f0_biluk f2_biluk a_wb a_wb p_bitr4i $.
$}

$(Disjunction distributes over the biconditional.  Theorem *5.7 of
     [WhiteheadRussell] p. 125.  This theorem is similar to ~ orbidi .
     (Contributed by Roy F. Longton, 21-Jun-2005.) $)

${
	$v ph ps ch  $.
	f0_pm5.7 $f wff ph $.
	f1_pm5.7 $f wff ps $.
	f2_pm5.7 $f wff ch $.
	p_pm5.7 $p |- ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <-> ( ch \/ ( ph <-> ps ) ) ) $= f2_pm5.7 f0_pm5.7 f1_pm5.7 p_orbidi f2_pm5.7 f0_pm5.7 p_orcom f2_pm5.7 f1_pm5.7 p_orcom f2_pm5.7 f0_pm5.7 a_wo f0_pm5.7 f2_pm5.7 a_wo f2_pm5.7 f1_pm5.7 a_wo f1_pm5.7 f2_pm5.7 a_wo p_bibi12i f2_pm5.7 f0_pm5.7 f1_pm5.7 a_wb a_wo f2_pm5.7 f0_pm5.7 a_wo f2_pm5.7 f1_pm5.7 a_wo a_wb f0_pm5.7 f2_pm5.7 a_wo f1_pm5.7 f2_pm5.7 a_wo a_wb p_bitr2i $.
$}

$(Dijkstra-Scholten's Golden Rule for calculational proofs.  (Contributed by
     NM, 10-Jan-2005.) $)

${
	$v ph ps  $.
	f0_bigolden $f wff ph $.
	f1_bigolden $f wff ps $.
	p_bigolden $p |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) ) $= f0_bigolden f1_bigolden p_pm4.71 f0_bigolden f1_bigolden p_pm4.72 f0_bigolden f0_bigolden f1_bigolden a_wa p_bicom f0_bigolden f1_bigolden a_wi f0_bigolden f0_bigolden f1_bigolden a_wa a_wb f1_bigolden f0_bigolden f1_bigolden a_wo a_wb f0_bigolden f1_bigolden a_wa f0_bigolden a_wb p_3bitr3ri $.
$}

$(Theorem *5.71 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 23-Jun-2005.) $)

${
	$v ph ps ch  $.
	f0_pm5.71 $f wff ph $.
	f1_pm5.71 $f wff ps $.
	f2_pm5.71 $f wff ch $.
	p_pm5.71 $p |- ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <-> ( ph /\ ch ) ) ) $= f1_pm5.71 f0_pm5.71 p_orel2 f0_pm5.71 f1_pm5.71 p_orc f1_pm5.71 a_wn f0_pm5.71 f1_pm5.71 a_wo f0_pm5.71 p_impbid1 f1_pm5.71 a_wn f0_pm5.71 f1_pm5.71 a_wo f0_pm5.71 f2_pm5.71 p_anbi1d f2_pm5.71 f0_pm5.71 f1_pm5.71 a_wo f0_pm5.71 a_wb p_pm2.21 f2_pm5.71 a_wn f2_pm5.71 f0_pm5.71 f1_pm5.71 a_wo f0_pm5.71 p_pm5.32rd f1_pm5.71 f2_pm5.71 a_wn f0_pm5.71 f1_pm5.71 a_wo f2_pm5.71 a_wa f0_pm5.71 f2_pm5.71 a_wa a_wb p_ja $.
$}

$(Theorem *5.75 of [WhiteheadRussell] p. 126.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 23-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_pm5.75 $f wff ph $.
	f1_pm5.75 $f wff ps $.
	f2_pm5.75 $f wff ch $.
	p_pm5.75 $p |- ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) -> ( ( ph /\ -. ps ) <-> ch ) ) $= f0_pm5.75 f1_pm5.75 f2_pm5.75 a_wo f1_pm5.75 a_wn p_anbi1 f1_pm5.75 f2_pm5.75 p_orcom f1_pm5.75 f2_pm5.75 a_wo f2_pm5.75 f1_pm5.75 a_wo f1_pm5.75 a_wn p_anbi1i f2_pm5.75 f1_pm5.75 p_pm5.61 f1_pm5.75 f2_pm5.75 a_wo f1_pm5.75 a_wn a_wa f2_pm5.75 f1_pm5.75 a_wo f1_pm5.75 a_wn a_wa f2_pm5.75 f1_pm5.75 a_wn a_wa p_bitri f0_pm5.75 f1_pm5.75 f2_pm5.75 a_wo a_wb f0_pm5.75 f1_pm5.75 a_wn a_wa f1_pm5.75 f2_pm5.75 a_wo f1_pm5.75 a_wn a_wa f2_pm5.75 f1_pm5.75 a_wn a_wa p_syl6bb f2_pm5.75 f1_pm5.75 a_wn p_pm4.71 f2_pm5.75 f1_pm5.75 a_wn a_wi f2_pm5.75 f2_pm5.75 f1_pm5.75 a_wn a_wa a_wb p_biimpi f2_pm5.75 f1_pm5.75 a_wn a_wi f2_pm5.75 f2_pm5.75 f1_pm5.75 a_wn a_wa p_bicomd f0_pm5.75 f1_pm5.75 f2_pm5.75 a_wo a_wb f0_pm5.75 f1_pm5.75 a_wn a_wa f2_pm5.75 f1_pm5.75 a_wn a_wa f2_pm5.75 f1_pm5.75 a_wn a_wi f2_pm5.75 p_sylan9bbr $.
$}

$(Removal of conjunct from one side of an equivalence.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_bimsc1 $f wff ph $.
	f1_bimsc1 $f wff ps $.
	f2_bimsc1 $f wff ch $.
	p_bimsc1 $p |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) ) -> ( ch <-> ph ) ) $= f1_bimsc1 f0_bimsc1 p_simpr f0_bimsc1 f1_bimsc1 p_ancr f0_bimsc1 f1_bimsc1 a_wi f1_bimsc1 f0_bimsc1 a_wa f0_bimsc1 p_impbid2 f0_bimsc1 f1_bimsc1 a_wi f1_bimsc1 f0_bimsc1 a_wa f0_bimsc1 f2_bimsc1 p_bibi2d f0_bimsc1 f1_bimsc1 a_wi f2_bimsc1 f1_bimsc1 f0_bimsc1 a_wa a_wb f2_bimsc1 f0_bimsc1 a_wb p_biimpa $.
$}

$(The disjunction of the four possible combinations of two wffs and their
     negations is always true.  (Contributed by David Abernethy,
     28-Jan-2014.) $)

${
	$v ph ps  $.
	f0_4exmid $f wff ph $.
	f1_4exmid $f wff ps $.
	p_4exmid $p |- ( ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) \/ ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $= f0_4exmid f1_4exmid a_wb p_exmid f0_4exmid f1_4exmid p_dfbi3 f0_4exmid f1_4exmid p_xor f0_4exmid f1_4exmid a_wb f0_4exmid f1_4exmid a_wa f0_4exmid a_wn f1_4exmid a_wn a_wa a_wo f0_4exmid f1_4exmid a_wb a_wn f0_4exmid f1_4exmid a_wn a_wa f1_4exmid f0_4exmid a_wn a_wa a_wo p_orbi12i f0_4exmid f1_4exmid a_wb f0_4exmid f1_4exmid a_wb a_wn a_wo f0_4exmid f1_4exmid a_wa f0_4exmid a_wn f1_4exmid a_wn a_wa a_wo f0_4exmid f1_4exmid a_wn a_wa f1_4exmid f0_4exmid a_wn a_wa a_wo a_wo p_mpbi $.
$}

$(Deduction for elimination by cases.  (Contributed by NM, 21-Apr-1994.)
       (Proof shortened by Wolf Lammen, 22-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_ecase2d $f wff ph $.
	f1_ecase2d $f wff ps $.
	f2_ecase2d $f wff ch $.
	f3_ecase2d $f wff th $.
	f4_ecase2d $f wff ta $.
	e0_ecase2d $e |- ( ph -> ps ) $.
	e1_ecase2d $e |- ( ph -> -. ( ps /\ ch ) ) $.
	e2_ecase2d $e |- ( ph -> -. ( ps /\ th ) ) $.
	e3_ecase2d $e |- ( ph -> ( ta \/ ( ch \/ th ) ) ) $.
	p_ecase2d $p |- ( ph -> ta ) $= f0_ecase2d f4_ecase2d p_idd e0_ecase2d e1_ecase2d f0_ecase2d f1_ecase2d f2_ecase2d a_wa f4_ecase2d p_pm2.21d f0_ecase2d f1_ecase2d f2_ecase2d f4_ecase2d p_mpand e0_ecase2d e2_ecase2d f0_ecase2d f1_ecase2d f3_ecase2d a_wa f4_ecase2d p_pm2.21d f0_ecase2d f1_ecase2d f3_ecase2d f4_ecase2d p_mpand f0_ecase2d f2_ecase2d f4_ecase2d f3_ecase2d p_jaod e3_ecase2d f0_ecase2d f4_ecase2d f4_ecase2d f2_ecase2d f3_ecase2d a_wo p_mpjaod $.
$}

$(Inference for elimination by cases.  (Contributed by NM, 23-Mar-1995.)
       (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_ecase3 $f wff ph $.
	f1_ecase3 $f wff ps $.
	f2_ecase3 $f wff ch $.
	e0_ecase3 $e |- ( ph -> ch ) $.
	e1_ecase3 $e |- ( ps -> ch ) $.
	e2_ecase3 $e |- ( -. ( ph \/ ps ) -> ch ) $.
	p_ecase3 $p |- ch $= e0_ecase3 e1_ecase3 f0_ecase3 f2_ecase3 f1_ecase3 p_jaoi e2_ecase3 f0_ecase3 f1_ecase3 a_wo f2_ecase3 p_pm2.61i $.
$}

$(Inference for elimination by cases.  (Contributed by NM,
       13-Jul-2005.) $)

${
	$v ph ps ch  $.
	f0_ecase $f wff ph $.
	f1_ecase $f wff ps $.
	f2_ecase $f wff ch $.
	e0_ecase $e |- ( -. ph -> ch ) $.
	e1_ecase $e |- ( -. ps -> ch ) $.
	e2_ecase $e |- ( ( ph /\ ps ) -> ch ) $.
	p_ecase $p |- ch $= e2_ecase f0_ecase f1_ecase f2_ecase p_ex e0_ecase e1_ecase f0_ecase f1_ecase f2_ecase p_pm2.61nii $.
$}

$(Deduction for elimination by cases.  (Contributed by NM, 2-May-1996.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch th  $.
	f0_ecase3d $f wff ph $.
	f1_ecase3d $f wff ps $.
	f2_ecase3d $f wff ch $.
	f3_ecase3d $f wff th $.
	e0_ecase3d $e |- ( ph -> ( ps -> th ) ) $.
	e1_ecase3d $e |- ( ph -> ( ch -> th ) ) $.
	e2_ecase3d $e |- ( ph -> ( -. ( ps \/ ch ) -> th ) ) $.
	p_ecase3d $p |- ( ph -> th ) $= e0_ecase3d e1_ecase3d f0_ecase3d f1_ecase3d f3_ecase3d f2_ecase3d p_jaod e2_ecase3d f0_ecase3d f1_ecase3d f2_ecase3d a_wo f3_ecase3d p_pm2.61d $.
$}

$(Deduction for elimination by cases.  (Contributed by NM, 8-Oct-2012.) $)

${
	$v ph ps ch th  $.
	f0_ecased $f wff ph $.
	f1_ecased $f wff ps $.
	f2_ecased $f wff ch $.
	f3_ecased $f wff th $.
	e0_ecased $e |- ( ph -> ( -. ps -> th ) ) $.
	e1_ecased $e |- ( ph -> ( -. ch -> th ) ) $.
	e2_ecased $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_ecased $p |- ( ph -> th ) $= e0_ecased e1_ecased f1_ecased f2_ecased p_pm3.11 e2_ecased f1_ecased a_wn f2_ecased a_wn a_wo a_wn f1_ecased f2_ecased a_wa f0_ecased f3_ecased p_syl5 f0_ecased f1_ecased a_wn f2_ecased a_wn f3_ecased p_ecase3d $.
$}

$(Deduction for elimination by cases.  (Contributed by NM,
       24-May-2013.) $)

${
	$v ph ps ch th  $.
	f0_ecase3ad $f wff ph $.
	f1_ecase3ad $f wff ps $.
	f2_ecase3ad $f wff ch $.
	f3_ecase3ad $f wff th $.
	e0_ecase3ad $e |- ( ph -> ( ps -> th ) ) $.
	e1_ecase3ad $e |- ( ph -> ( ch -> th ) ) $.
	e2_ecase3ad $e |- ( ph -> ( ( -. ps /\ -. ch ) -> th ) ) $.
	p_ecase3ad $p |- ( ph -> th ) $= f1_ecase3ad p_notnot2 e0_ecase3ad f1_ecase3ad a_wn a_wn f1_ecase3ad f0_ecase3ad f3_ecase3ad p_syl5 f2_ecase3ad p_notnot2 e1_ecase3ad f2_ecase3ad a_wn a_wn f2_ecase3ad f0_ecase3ad f3_ecase3ad p_syl5 e2_ecase3ad f0_ecase3ad f1_ecase3ad a_wn f2_ecase3ad a_wn f3_ecase3ad p_ecased $.
$}

$(Inference for combining cases.  (Contributed by NM, 29-Jul-1999.)
       (Proof shortened by Wolf Lammen, 6-Jan-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_ccase $f wff ph $.
	f1_ccase $f wff ps $.
	f2_ccase $f wff ch $.
	f3_ccase $f wff th $.
	f4_ccase $f wff ta $.
	e0_ccase $e |- ( ( ph /\ ps ) -> ta ) $.
	e1_ccase $e |- ( ( ch /\ ps ) -> ta ) $.
	e2_ccase $e |- ( ( ph /\ th ) -> ta ) $.
	e3_ccase $e |- ( ( ch /\ th ) -> ta ) $.
	p_ccase $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $= e0_ccase e1_ccase f0_ccase f1_ccase f4_ccase f2_ccase p_jaoian e2_ccase e3_ccase f0_ccase f3_ccase f4_ccase f2_ccase p_jaoian f0_ccase f2_ccase a_wo f1_ccase f4_ccase f3_ccase p_jaodan $.
$}

$(Deduction for combining cases.  (Contributed by NM, 9-May-2004.) $)

${
	$v ph ps ch th ta et  $.
	f0_ccased $f wff ph $.
	f1_ccased $f wff ps $.
	f2_ccased $f wff ch $.
	f3_ccased $f wff th $.
	f4_ccased $f wff ta $.
	f5_ccased $f wff et $.
	e0_ccased $e |- ( ph -> ( ( ps /\ ch ) -> et ) ) $.
	e1_ccased $e |- ( ph -> ( ( th /\ ch ) -> et ) ) $.
	e2_ccased $e |- ( ph -> ( ( ps /\ ta ) -> et ) ) $.
	e3_ccased $e |- ( ph -> ( ( th /\ ta ) -> et ) ) $.
	p_ccased $p |- ( ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ) ) $= e0_ccased f0_ccased f1_ccased f2_ccased a_wa f5_ccased p_com12 e1_ccased f0_ccased f3_ccased f2_ccased a_wa f5_ccased p_com12 e2_ccased f0_ccased f1_ccased f4_ccased a_wa f5_ccased p_com12 e3_ccased f0_ccased f3_ccased f4_ccased a_wa f5_ccased p_com12 f1_ccased f2_ccased f3_ccased f4_ccased f0_ccased f5_ccased a_wi p_ccase f1_ccased f3_ccased a_wo f2_ccased f4_ccased a_wo a_wa f0_ccased f5_ccased p_com12 $.
$}

$(Inference for combining cases.  (Contributed by NM, 29-Jul-1999.) $)

${
	$v ph ps ch th ta  $.
	f0_ccase2 $f wff ph $.
	f1_ccase2 $f wff ps $.
	f2_ccase2 $f wff ch $.
	f3_ccase2 $f wff th $.
	f4_ccase2 $f wff ta $.
	e0_ccase2 $e |- ( ( ph /\ ps ) -> ta ) $.
	e1_ccase2 $e |- ( ch -> ta ) $.
	e2_ccase2 $e |- ( th -> ta ) $.
	p_ccase2 $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $= e0_ccase2 e1_ccase2 f2_ccase2 f4_ccase2 f1_ccase2 p_adantr e2_ccase2 f3_ccase2 f4_ccase2 f0_ccase2 p_adantl e2_ccase2 f3_ccase2 f4_ccase2 f2_ccase2 p_adantl f0_ccase2 f1_ccase2 f2_ccase2 f3_ccase2 f4_ccase2 p_ccase $.
$}

$(Inference eliminating two antecedents from the four possible cases that
       result from their true/false combinations.  (Contributed by NM,
       25-Oct-2003.) $)

${
	$v ph ps ch  $.
	f0_4cases $f wff ph $.
	f1_4cases $f wff ps $.
	f2_4cases $f wff ch $.
	e0_4cases $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_4cases $e |- ( ( ph /\ -. ps ) -> ch ) $.
	e2_4cases $e |- ( ( -. ph /\ ps ) -> ch ) $.
	e3_4cases $e |- ( ( -. ph /\ -. ps ) -> ch ) $.
	p_4cases $p |- ch $= e0_4cases e2_4cases f0_4cases f1_4cases f2_4cases p_pm2.61ian e1_4cases e3_4cases f0_4cases f1_4cases a_wn f2_4cases p_pm2.61ian f1_4cases f2_4cases p_pm2.61i $.
$}

$(Deduction eliminating two antecedents from the four possible cases that
       result from their true/false combinations.  (Contributed by NM,
       19-Mar-2013.) $)

${
	$v ph ps ch th  $.
	f0_4casesdan $f wff ph $.
	f1_4casesdan $f wff ps $.
	f2_4casesdan $f wff ch $.
	f3_4casesdan $f wff th $.
	e0_4casesdan $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	e1_4casesdan $e |- ( ( ph /\ ( ps /\ -. ch ) ) -> th ) $.
	e2_4casesdan $e |- ( ( ph /\ ( -. ps /\ ch ) ) -> th ) $.
	e3_4casesdan $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
	p_4casesdan $p |- ( ph -> th ) $= e0_4casesdan f0_4casesdan f1_4casesdan f2_4casesdan a_wa f3_4casesdan p_expcom e1_4casesdan f0_4casesdan f1_4casesdan f2_4casesdan a_wn a_wa f3_4casesdan p_expcom e2_4casesdan f0_4casesdan f1_4casesdan a_wn f2_4casesdan a_wa f3_4casesdan p_expcom e3_4casesdan f0_4casesdan f1_4casesdan a_wn f2_4casesdan a_wn a_wa f3_4casesdan p_expcom f1_4casesdan f2_4casesdan f0_4casesdan f3_4casesdan a_wi p_4cases $.
$}

$(Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) $)

${
	$v ph ps ch  $.
	f0_niabn $f wff ph $.
	f1_niabn $f wff ps $.
	f2_niabn $f wff ch $.
	e0_niabn $e |- ph $.
	p_niabn $p |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) ) $= f2_niabn f1_niabn p_simpr e0_niabn f0_niabn f1_niabn p_pm2.24i f2_niabn f1_niabn a_wa f1_niabn f0_niabn a_wn p_pm5.21ni $.
$}

$(Lemma for an alternate version of weak deduction theorem.  (Contributed by
     NM, 2-Apr-1994.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 4-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_dedlem0a $f wff ph $.
	f1_dedlem0a $f wff ps $.
	f2_dedlem0a $f wff ch $.
	p_dedlem0a $p |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) ) $= f0_dedlem0a f1_dedlem0a p_iba f0_dedlem0a f2_dedlem0a a_ax-1 f2_dedlem0a f0_dedlem0a a_wi f1_dedlem0a f0_dedlem0a a_wa p_biimt f0_dedlem0a f2_dedlem0a f0_dedlem0a a_wi f1_dedlem0a f0_dedlem0a a_wa f2_dedlem0a f0_dedlem0a a_wi f1_dedlem0a f0_dedlem0a a_wa a_wi a_wb p_syl f0_dedlem0a f1_dedlem0a f1_dedlem0a f0_dedlem0a a_wa f2_dedlem0a f0_dedlem0a a_wi f1_dedlem0a f0_dedlem0a a_wa a_wi p_bitrd $.
$}

$(Lemma for an alternate version of weak deduction theorem.  (Contributed by
     NM, 2-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_dedlem0b $f wff ph $.
	f1_dedlem0b $f wff ps $.
	f2_dedlem0b $f wff ch $.
	p_dedlem0b $p |- ( -. ph -> ( ps <-> ( ( ps -> ph ) -> ( ch /\ ph ) ) ) ) $= f0_dedlem0b f2_dedlem0b f0_dedlem0b a_wa p_pm2.21 f0_dedlem0b a_wn f0_dedlem0b f2_dedlem0b f0_dedlem0b a_wa f1_dedlem0b p_imim2d f0_dedlem0b a_wn f1_dedlem0b f0_dedlem0b a_wi f1_dedlem0b f2_dedlem0b f0_dedlem0b a_wa p_com23 f1_dedlem0b f0_dedlem0b p_pm2.21 f2_dedlem0b f0_dedlem0b p_simpr f1_dedlem0b a_wn f1_dedlem0b f0_dedlem0b a_wi f2_dedlem0b f0_dedlem0b a_wa f0_dedlem0b p_imim12i f1_dedlem0b f0_dedlem0b a_wi f2_dedlem0b f0_dedlem0b a_wa a_wi f1_dedlem0b f0_dedlem0b p_con1d f1_dedlem0b f0_dedlem0b a_wi f2_dedlem0b f0_dedlem0b a_wa a_wi f0_dedlem0b a_wn f1_dedlem0b p_com12 f0_dedlem0b a_wn f1_dedlem0b f1_dedlem0b f0_dedlem0b a_wi f2_dedlem0b f0_dedlem0b a_wa a_wi p_impbid $.
$}

$(Lemma for weak deduction theorem.  (Contributed by NM, 26-Jun-2002.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch  $.
	f0_dedlema $f wff ph $.
	f1_dedlema $f wff ps $.
	f2_dedlema $f wff ch $.
	p_dedlema $p |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $= f1_dedlema f0_dedlema a_wa f2_dedlema f0_dedlema a_wn a_wa p_orc f1_dedlema f0_dedlema f1_dedlema f0_dedlema a_wa f2_dedlema f0_dedlema a_wn a_wa a_wo p_expcom f1_dedlema f0_dedlema p_simpl f1_dedlema f0_dedlema a_wa f1_dedlema a_wi f0_dedlema p_a1i f0_dedlema f1_dedlema p_pm2.24 f0_dedlema f0_dedlema a_wn f1_dedlema f2_dedlema p_adantld f0_dedlema f1_dedlema f0_dedlema a_wa f1_dedlema f2_dedlema f0_dedlema a_wn a_wa p_jaod f0_dedlema f1_dedlema f1_dedlema f0_dedlema a_wa f2_dedlema f0_dedlema a_wn a_wa a_wo p_impbid $.
$}

$(Lemma for weak deduction theorem.  (Contributed by NM, 15-May-1999.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch  $.
	f0_dedlemb $f wff ph $.
	f1_dedlemb $f wff ps $.
	f2_dedlemb $f wff ch $.
	p_dedlemb $p |- ( -. ph -> ( ch <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $= f2_dedlemb f0_dedlemb a_wn a_wa f1_dedlemb f0_dedlemb a_wa p_olc f2_dedlemb f0_dedlemb a_wn f1_dedlemb f0_dedlemb a_wa f2_dedlemb f0_dedlemb a_wn a_wa a_wo p_expcom f0_dedlemb f2_dedlemb p_pm2.21 f0_dedlemb a_wn f0_dedlemb f2_dedlemb f1_dedlemb p_adantld f2_dedlemb f0_dedlemb a_wn p_simpl f2_dedlemb f0_dedlemb a_wn a_wa f2_dedlemb a_wi f0_dedlemb a_wn p_a1i f0_dedlemb a_wn f1_dedlemb f0_dedlemb a_wa f2_dedlemb f2_dedlemb f0_dedlemb a_wn a_wa p_jaod f0_dedlemb a_wn f2_dedlemb f1_dedlemb f0_dedlemb a_wa f2_dedlemb f0_dedlemb a_wn a_wa a_wo p_impbid $.
$}

$(Hypothesis builder for weak deduction theorem.  For more information,
       see the Deduction Theorem link on the Metamath Proof Explorer home
       page.  (Contributed by NM, 26-Jun-2002.) $)

${
	$v ph ps ch th ta  $.
	f0_elimh $f wff ph $.
	f1_elimh $f wff ps $.
	f2_elimh $f wff ch $.
	f3_elimh $f wff th $.
	f4_elimh $f wff ta $.
	e0_elimh $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) ) -> ( ch <-> ta ) ) $.
	e1_elimh $e |- ( ( ps <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) ) -> ( th <-> ta ) ) $.
	e2_elimh $e |- th $.
	p_elimh $p |- ta $= f2_elimh f0_elimh f1_elimh p_dedlema e0_elimh f2_elimh f0_elimh f0_elimh f2_elimh a_wa f1_elimh f2_elimh a_wn a_wa a_wo a_wb f2_elimh f4_elimh a_wb p_syl f2_elimh f4_elimh p_ibi e2_elimh f2_elimh f0_elimh f1_elimh p_dedlemb e1_elimh f2_elimh a_wn f1_elimh f0_elimh f2_elimh a_wa f1_elimh f2_elimh a_wn a_wa a_wo a_wb f3_elimh f4_elimh a_wb p_syl f2_elimh a_wn f3_elimh f4_elimh p_mpbii f2_elimh f4_elimh p_pm2.61i $.
$}

$(The weak deduction theorem.  For more information, see the Deduction
       Theorem link on the Metamath Proof Explorer home page.  (Contributed by
       NM, 26-Jun-2002.) $)

${
	$v ph ps ch th ta  $.
	f0_dedt $f wff ph $.
	f1_dedt $f wff ps $.
	f2_dedt $f wff ch $.
	f3_dedt $f wff th $.
	f4_dedt $f wff ta $.
	e0_dedt $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) ) -> ( th <-> ta ) ) $.
	e1_dedt $e |- ta $.
	p_dedt $p |- ( ch -> th ) $= f2_dedt f0_dedt f1_dedt p_dedlema e1_dedt e0_dedt f0_dedt f0_dedt f2_dedt a_wa f1_dedt f2_dedt a_wn a_wa a_wo a_wb f3_dedt f4_dedt p_mpbiri f2_dedt f0_dedt f0_dedt f2_dedt a_wa f1_dedt f2_dedt a_wn a_wa a_wo a_wb f3_dedt p_syl $.
$}

$(Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This version
     of ~ con3 demonstrates the use of the weak deduction theorem ~ dedt to
     derive it from ~ con3i .  (Contributed by NM, 27-Jun-2002.)
     (Proof modification is discouraged.) $)

${
	$v ph ps  $.
	f0_con3th $f wff ph $.
	f1_con3th $f wff ps $.
	p_con3th $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $= f1_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wb p_id f1_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wb f1_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo p_notbid f1_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wb f1_con3th a_wn f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wn f0_con3th a_wn p_imbi1d f1_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wb p_id f1_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wb f1_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo f0_con3th p_imbi2d f0_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wb p_id f0_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wb f0_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo f0_con3th p_imbi2d f0_con3th p_id f1_con3th f0_con3th f0_con3th f1_con3th a_wi f0_con3th f0_con3th a_wi f0_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wi p_elimh f0_con3th f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo p_con3i f1_con3th f0_con3th f0_con3th f1_con3th a_wi f1_con3th a_wn f0_con3th a_wn a_wi f1_con3th f0_con3th f1_con3th a_wi a_wa f0_con3th f0_con3th f1_con3th a_wi a_wn a_wa a_wo a_wn f0_con3th a_wn a_wi p_dedt $.
$}

$(The consensus theorem.  This theorem and its dual (with ` \/ ` and ` /\ `
     interchanged) are commonly used in computer logic design to eliminate
     redundant terms from Boolean expressions.  Specifically, we prove that the
     term ` ( ps /\ ch ) ` on the left-hand side is redundant.  (Contributed by
     NM, 16-May-2003.)  (Proof shortened by Andrew Salmon, 13-May-2011.)
     (Proof shortened by Wolf Lammen, 20-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_consensus $f wff ph $.
	f1_consensus $f wff ps $.
	f2_consensus $f wff ch $.
	p_consensus $p |- ( ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) \/ ( ps /\ ch ) ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) ) $= f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo p_id f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa p_orc f0_consensus f1_consensus f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo f2_consensus p_adantrr f0_consensus a_wn f2_consensus a_wa f0_consensus f1_consensus a_wa p_olc f0_consensus a_wn f2_consensus f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo f1_consensus p_adantrl f0_consensus f1_consensus f2_consensus a_wa f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo p_pm2.61ian f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo f1_consensus f2_consensus a_wa p_jaoi f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo f1_consensus f2_consensus a_wa p_orc f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo f1_consensus f2_consensus a_wa a_wo f0_consensus f1_consensus a_wa f0_consensus a_wn f2_consensus a_wa a_wo p_impbii $.
$}

$(Theorem *4.42 of [WhiteheadRussell] p. 119.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)

${
	$v ph ps  $.
	f0_pm4.42 $f wff ph $.
	f1_pm4.42 $f wff ps $.
	p_pm4.42 $p |- ( ph <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) ) $= f1_pm4.42 f0_pm4.42 f0_pm4.42 p_dedlema f1_pm4.42 f0_pm4.42 f0_pm4.42 p_dedlemb f1_pm4.42 f0_pm4.42 f0_pm4.42 f1_pm4.42 a_wa f0_pm4.42 f1_pm4.42 a_wn a_wa a_wo a_wb p_pm2.61i $.
$}

$(Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) $)

${
	$v ph ps ch  $.
	f0_ninba $f wff ph $.
	f1_ninba $f wff ps $.
	f2_ninba $f wff ch $.
	e0_ninba $e |- ph $.
	p_ninba $p |- ( -. ps -> ( -. ph <-> ( ch /\ ps ) ) ) $= e0_ninba f0_ninba f1_ninba f2_ninba p_niabn f1_ninba a_wn f2_ninba f1_ninba a_wa f0_ninba a_wn p_bicomd $.
$}

$(A specialized lemma for set theory (to derive the Axiom of Pairing).
       (Contributed by NM, 18-Oct-1995.)  (Proof shortened by Andrew Salmon,
       13-May-2011.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)

${
	$v ph ps ch th ta et  $.
	f0_prlem1 $f wff ph $.
	f1_prlem1 $f wff ps $.
	f2_prlem1 $f wff ch $.
	f3_prlem1 $f wff th $.
	f4_prlem1 $f wff ta $.
	f5_prlem1 $f wff et $.
	e0_prlem1 $e |- ( ph -> ( et <-> ch ) ) $.
	e1_prlem1 $e |- ( ps -> -. th ) $.
	p_prlem1 $p |- ( ph -> ( ps -> ( ( ( ps /\ ch ) \/ ( th /\ ta ) ) -> et ) ) ) $= e0_prlem1 f0_prlem1 f5_prlem1 f2_prlem1 p_biimprd f0_prlem1 f2_prlem1 f5_prlem1 f1_prlem1 p_adantld e1_prlem1 f1_prlem1 f3_prlem1 f5_prlem1 p_pm2.21d f1_prlem1 f3_prlem1 f5_prlem1 f4_prlem1 p_adantrd f0_prlem1 f1_prlem1 f2_prlem1 a_wa f5_prlem1 f1_prlem1 f3_prlem1 f4_prlem1 a_wa p_jaao f0_prlem1 f1_prlem1 f1_prlem1 f2_prlem1 a_wa f3_prlem1 f4_prlem1 a_wa a_wo f5_prlem1 a_wi p_ex $.
$}

$(A specialized lemma for set theory (to derive the Axiom of Pairing).
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
     13-May-2011.)  (Proof shortened by Wolf Lammen, 9-Dec-2012.) $)

${
	$v ph ps ch th  $.
	f0_prlem2 $f wff ph $.
	f1_prlem2 $f wff ps $.
	f2_prlem2 $f wff ch $.
	f3_prlem2 $f wff th $.
	p_prlem2 $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <-> ( ( ph \/ ch ) /\ ( ( ph /\ ps ) \/ ( ch /\ th ) ) ) ) $= f0_prlem2 f1_prlem2 p_simpl f2_prlem2 f3_prlem2 p_simpl f0_prlem2 f1_prlem2 a_wa f0_prlem2 f2_prlem2 f3_prlem2 a_wa f2_prlem2 p_orim12i f0_prlem2 f1_prlem2 a_wa f2_prlem2 f3_prlem2 a_wa a_wo f0_prlem2 f2_prlem2 a_wo p_pm4.71ri $.
$}

$(A specialized lemma for set theory (ordered pair theorem).  (Contributed
       by NM, 18-Oct-1995.)  (Proof shortened by Wolf Lammen, 8-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_oplem1 $f wff ph $.
	f1_oplem1 $f wff ps $.
	f2_oplem1 $f wff ch $.
	f3_oplem1 $f wff th $.
	f4_oplem1 $f wff ta $.
	e0_oplem1 $e |- ( ph -> ( ps \/ ch ) ) $.
	e1_oplem1 $e |- ( ph -> ( th \/ ta ) ) $.
	e2_oplem1 $e |- ( ps <-> th ) $.
	e3_oplem1 $e |- ( ch -> ( th <-> ta ) ) $.
	p_oplem1 $p |- ( ph -> ps ) $= e2_oplem1 f1_oplem1 f3_oplem1 p_notbii e0_oplem1 f0_oplem1 f1_oplem1 f2_oplem1 p_ord f3_oplem1 a_wn f1_oplem1 a_wn f0_oplem1 f2_oplem1 p_syl5bir e1_oplem1 f0_oplem1 f3_oplem1 f4_oplem1 p_ord f0_oplem1 f3_oplem1 a_wn f2_oplem1 f4_oplem1 p_jcad e3_oplem1 f2_oplem1 f3_oplem1 f4_oplem1 p_biimpar f0_oplem1 f3_oplem1 a_wn f2_oplem1 f4_oplem1 a_wa f3_oplem1 p_syl6 f0_oplem1 f3_oplem1 p_pm2.18d e2_oplem1 f0_oplem1 f3_oplem1 f1_oplem1 p_sylibr $.
$}

$(Lemma used in construction of real numbers.  (Contributed by NM,
     4-Sep-1995.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph ps ch th  $.
	f0_rnlem $f wff ph $.
	f1_rnlem $f wff ps $.
	f2_rnlem $f wff ch $.
	f3_rnlem $f wff th $.
	p_rnlem $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) /\ ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) ) $= f0_rnlem f1_rnlem f2_rnlem f3_rnlem p_an4 f0_rnlem f1_rnlem a_wa f2_rnlem f3_rnlem a_wa a_wa f0_rnlem f2_rnlem a_wa f1_rnlem f3_rnlem a_wa a_wa p_biimpi f0_rnlem f3_rnlem f1_rnlem f2_rnlem p_an42 f0_rnlem f3_rnlem a_wa f1_rnlem f2_rnlem a_wa a_wa f0_rnlem f1_rnlem a_wa f2_rnlem f3_rnlem a_wa a_wa p_biimpri f0_rnlem f1_rnlem a_wa f2_rnlem f3_rnlem a_wa a_wa f0_rnlem f2_rnlem a_wa f1_rnlem f3_rnlem a_wa a_wa f0_rnlem f3_rnlem a_wa f1_rnlem f2_rnlem a_wa a_wa p_jca f0_rnlem f3_rnlem f1_rnlem f2_rnlem p_an42 f0_rnlem f3_rnlem a_wa f1_rnlem f2_rnlem a_wa a_wa f0_rnlem f1_rnlem a_wa f2_rnlem f3_rnlem a_wa a_wa p_biimpi f0_rnlem f3_rnlem a_wa f1_rnlem f2_rnlem a_wa a_wa f0_rnlem f1_rnlem a_wa f2_rnlem f3_rnlem a_wa a_wa f0_rnlem f2_rnlem a_wa f1_rnlem f3_rnlem a_wa a_wa p_adantl f0_rnlem f1_rnlem a_wa f2_rnlem f3_rnlem a_wa a_wa f0_rnlem f2_rnlem a_wa f1_rnlem f3_rnlem a_wa a_wa f0_rnlem f3_rnlem a_wa f1_rnlem f2_rnlem a_wa a_wa a_wa p_impbii $.
$}

$(A single axiom for Boolean algebra known as DN_1.  See
     ~ http://www-unix.mcs.anl.gov/~~mccune/papers/basax/v12.pdf .
     (Contributed by Jeffrey Hankins, 3-Jul-2009.)  (Proof shortened by Andrew
     Salmon, 13-May-2011.)  (Proof shortened by Wolf Lammen, 6-Jan-2013.) $)

${
	$v ph ps ch th  $.
	f0_dn1 $f wff ph $.
	f1_dn1 $f wff ps $.
	f2_dn1 $f wff ch $.
	f3_dn1 $f wff th $.
	p_dn1 $p |- ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/ -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch ) $= f0_dn1 f1_dn1 p_pm2.45 f0_dn1 f1_dn1 a_wo a_wn f0_dn1 p_imnan f0_dn1 f1_dn1 a_wo a_wn f0_dn1 a_wn a_wi f0_dn1 f1_dn1 a_wo a_wn f0_dn1 a_wa a_wn p_mpbi f0_dn1 f1_dn1 a_wo a_wn f0_dn1 a_wa f2_dn1 p_biorfi f2_dn1 f0_dn1 f1_dn1 a_wo a_wn f0_dn1 a_wa p_orcom f0_dn1 f1_dn1 a_wo a_wn f0_dn1 f2_dn1 p_ordir f2_dn1 f0_dn1 f1_dn1 a_wo a_wn f0_dn1 a_wa a_wo f0_dn1 f1_dn1 a_wo a_wn f0_dn1 a_wa f2_dn1 a_wo f0_dn1 f1_dn1 a_wo a_wn f2_dn1 a_wo f0_dn1 f2_dn1 a_wo a_wa p_bitri f2_dn1 f2_dn1 f0_dn1 f1_dn1 a_wo a_wn f0_dn1 a_wa a_wo f0_dn1 f1_dn1 a_wo a_wn f2_dn1 a_wo f0_dn1 f2_dn1 a_wo a_wa p_bitri f2_dn1 f3_dn1 p_pm4.45 f2_dn1 f2_dn1 f3_dn1 a_wo p_anor f2_dn1 f2_dn1 f2_dn1 f3_dn1 a_wo a_wa f2_dn1 a_wn f2_dn1 f3_dn1 a_wo a_wn a_wo a_wn p_bitri f2_dn1 f2_dn1 a_wn f2_dn1 f3_dn1 a_wo a_wn a_wo a_wn f0_dn1 p_orbi2i f0_dn1 f2_dn1 a_wo f0_dn1 f2_dn1 a_wn f2_dn1 f3_dn1 a_wo a_wn a_wo a_wn a_wo f0_dn1 f1_dn1 a_wo a_wn f2_dn1 a_wo p_anbi2i f0_dn1 f1_dn1 a_wo a_wn f2_dn1 a_wo f0_dn1 f2_dn1 a_wn f2_dn1 f3_dn1 a_wo a_wn a_wo a_wn a_wo p_anor f2_dn1 f0_dn1 f1_dn1 a_wo a_wn f2_dn1 a_wo f0_dn1 f2_dn1 a_wo a_wa f0_dn1 f1_dn1 a_wo a_wn f2_dn1 a_wo f0_dn1 f2_dn1 a_wn f2_dn1 f3_dn1 a_wo a_wn a_wo a_wn a_wo a_wa f0_dn1 f1_dn1 a_wo a_wn f2_dn1 a_wo a_wn f0_dn1 f2_dn1 a_wn f2_dn1 f3_dn1 a_wo a_wn a_wo a_wn a_wo a_wn a_wo a_wn p_3bitrri $.
$}


