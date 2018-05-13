$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Miscellaneous_theorems_of_propositional_calculus.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Abbreviated conjunction and disjunction of three wff's

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Extend wff definition to include 3-way disjunction ('or'). $)

${
	$v ph ps ch  $.
	f0_w3o $f wff ph $.
	f1_w3o $f wff ps $.
	f2_w3o $f wff ch $.
	a_w3o $a wff ( ph \/ ps \/ ch ) $.
$}

$(Extend wff definition to include 3-way conjunction ('and'). $)

${
	$v ph ps ch  $.
	f0_w3a $f wff ph $.
	f1_w3a $f wff ps $.
	f2_w3a $f wff ch $.
	a_w3a $a wff ( ph /\ ps /\ ch ) $.
$}

$(These abbreviations help eliminate parentheses to aid readability. $)

$(Define disjunction ('or') of three wff's.  Definition *2.33 of
     [WhiteheadRussell] p. 105.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ orass .  (Contributed by NM,
     8-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_df-3or $f wff ph $.
	f1_df-3or $f wff ps $.
	f2_df-3or $f wff ch $.
	a_df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.
$}

$(Define conjunction ('and') of three wff's.  Definition *4.34 of
     [WhiteheadRussell] p. 118.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ anass .  (Contributed by NM,
     8-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_df-3an $f wff ph $.
	f1_df-3an $f wff ps $.
	f2_df-3an $f wff ch $.
	a_df-3an $a |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) ) $.
$}

$(Associative law for triple disjunction.  (Contributed by NM,
     8-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_3orass $f wff ph $.
	f1_3orass $f wff ps $.
	f2_3orass $f wff ch $.
	p_3orass $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $= f0_3orass f1_3orass f2_3orass a_df-3or f0_3orass f1_3orass f2_3orass p_orass f0_3orass f1_3orass f2_3orass a_w3o f0_3orass f1_3orass a_wo f2_3orass a_wo f0_3orass f1_3orass f2_3orass a_wo a_wo p_bitri $.
$}

$(Associative law for triple conjunction.  (Contributed by NM,
     8-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_3anass $f wff ph $.
	f1_3anass $f wff ps $.
	f2_3anass $f wff ch $.
	p_3anass $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $= f0_3anass f1_3anass f2_3anass a_df-3an f0_3anass f1_3anass f2_3anass p_anass f0_3anass f1_3anass f2_3anass a_w3a f0_3anass f1_3anass a_wa f2_3anass a_wa f0_3anass f1_3anass f2_3anass a_wa a_wa p_bitri $.
$}

$(Rotation law for triple conjunction.  (Contributed by NM, 8-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_3anrot $f wff ph $.
	f1_3anrot $f wff ps $.
	f2_3anrot $f wff ch $.
	p_3anrot $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ch /\ ph ) ) $= f0_3anrot f1_3anrot f2_3anrot a_wa p_ancom f0_3anrot f1_3anrot f2_3anrot p_3anass f1_3anrot f2_3anrot f0_3anrot a_df-3an f0_3anrot f1_3anrot f2_3anrot a_wa a_wa f1_3anrot f2_3anrot a_wa f0_3anrot a_wa f0_3anrot f1_3anrot f2_3anrot a_w3a f1_3anrot f2_3anrot f0_3anrot a_w3a p_3bitr4i $.
$}

$(Rotation law for triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)

${
	$v ph ps ch  $.
	f0_3orrot $f wff ph $.
	f1_3orrot $f wff ps $.
	f2_3orrot $f wff ch $.
	p_3orrot $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) ) $= f0_3orrot f1_3orrot f2_3orrot a_wo p_orcom f0_3orrot f1_3orrot f2_3orrot p_3orass f1_3orrot f2_3orrot f0_3orrot a_df-3or f0_3orrot f1_3orrot f2_3orrot a_wo a_wo f1_3orrot f2_3orrot a_wo f0_3orrot a_wo f0_3orrot f1_3orrot f2_3orrot a_w3o f1_3orrot f2_3orrot f0_3orrot a_w3o p_3bitr4i $.
$}

$(Commutation law for triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_3ancoma $f wff ph $.
	f1_3ancoma $f wff ps $.
	f2_3ancoma $f wff ch $.
	p_3ancoma $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ph /\ ch ) ) $= f0_3ancoma f1_3ancoma p_ancom f0_3ancoma f1_3ancoma a_wa f1_3ancoma f0_3ancoma a_wa f2_3ancoma p_anbi1i f0_3ancoma f1_3ancoma f2_3ancoma a_df-3an f1_3ancoma f0_3ancoma f2_3ancoma a_df-3an f0_3ancoma f1_3ancoma a_wa f2_3ancoma a_wa f1_3ancoma f0_3ancoma a_wa f2_3ancoma a_wa f0_3ancoma f1_3ancoma f2_3ancoma a_w3a f1_3ancoma f0_3ancoma f2_3ancoma a_w3a p_3bitr4i $.
$}

$(Commutation law for triple disjunction.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_3orcoma $f wff ph $.
	f1_3orcoma $f wff ps $.
	f2_3orcoma $f wff ch $.
	p_3orcoma $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ph \/ ch ) ) $= f0_3orcoma f1_3orcoma f2_3orcoma p_or12 f0_3orcoma f1_3orcoma f2_3orcoma p_3orass f1_3orcoma f0_3orcoma f2_3orcoma p_3orass f0_3orcoma f1_3orcoma f2_3orcoma a_wo a_wo f1_3orcoma f0_3orcoma f2_3orcoma a_wo a_wo f0_3orcoma f1_3orcoma f2_3orcoma a_w3o f1_3orcoma f0_3orcoma f2_3orcoma a_w3o p_3bitr4i $.
$}

$(Commutation law for triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_3ancomb $f wff ph $.
	f1_3ancomb $f wff ps $.
	f2_3ancomb $f wff ch $.
	p_3ancomb $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ch /\ ps ) ) $= f0_3ancomb f1_3ancomb f2_3ancomb p_3ancoma f1_3ancomb f0_3ancomb f2_3ancomb p_3anrot f0_3ancomb f1_3ancomb f2_3ancomb a_w3a f1_3ancomb f0_3ancomb f2_3ancomb a_w3a f0_3ancomb f2_3ancomb f1_3ancomb a_w3a p_bitri $.
$}

$(Commutation law for triple disjunction.  (Contributed by Scott Fenton,
     20-Apr-2011.) $)

${
	$v ph ps ch  $.
	f0_3orcomb $f wff ph $.
	f1_3orcomb $f wff ps $.
	f2_3orcomb $f wff ch $.
	p_3orcomb $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) ) $= f1_3orcomb f2_3orcomb p_orcom f1_3orcomb f2_3orcomb a_wo f2_3orcomb f1_3orcomb a_wo f0_3orcomb p_orbi2i f0_3orcomb f1_3orcomb f2_3orcomb p_3orass f0_3orcomb f2_3orcomb f1_3orcomb p_3orass f0_3orcomb f1_3orcomb f2_3orcomb a_wo a_wo f0_3orcomb f2_3orcomb f1_3orcomb a_wo a_wo f0_3orcomb f1_3orcomb f2_3orcomb a_w3o f0_3orcomb f2_3orcomb f1_3orcomb a_w3o p_3bitr4i $.
$}

$(Reversal law for triple conjunction.  (Contributed by NM, 21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_3anrev $f wff ph $.
	f1_3anrev $f wff ps $.
	f2_3anrev $f wff ch $.
	p_3anrev $p |- ( ( ph /\ ps /\ ch ) <-> ( ch /\ ps /\ ph ) ) $= f0_3anrev f1_3anrev f2_3anrev p_3ancoma f2_3anrev f1_3anrev f0_3anrev p_3anrot f0_3anrev f1_3anrev f2_3anrev a_w3a f1_3anrev f0_3anrev f2_3anrev a_w3a f2_3anrev f1_3anrev f0_3anrev a_w3a p_bitr4i $.
$}

$(Convert triple conjunction to conjunction, then commute.  (Contributed by
     Jonathan Ben-Naim, 3-Jun-2011.) $)

${
	$v ph ps ch  $.
	f0_3anan32 $f wff ph $.
	f1_3anan32 $f wff ps $.
	f2_3anan32 $f wff ch $.
	p_3anan32 $p |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $= f0_3anan32 f1_3anan32 f2_3anan32 a_df-3an f0_3anan32 f1_3anan32 f2_3anan32 p_an32 f0_3anan32 f1_3anan32 f2_3anan32 a_w3a f0_3anan32 f1_3anan32 a_wa f2_3anan32 a_wa f0_3anan32 f2_3anan32 a_wa f1_3anan32 a_wa p_bitri $.
$}

$(Convert triple conjunction to conjunction, then commute.  (Contributed by
     Jonathan Ben-Naim, 3-Jun-2011.)  (Proof shortened by Andrew Salmon,
     14-Jun-2011.) $)

${
	$v ph ps ch  $.
	f0_3anan12 $f wff ph $.
	f1_3anan12 $f wff ps $.
	f2_3anan12 $f wff ch $.
	p_3anan12 $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ( ph /\ ch ) ) ) $= f0_3anan12 f1_3anan12 f2_3anan12 p_3ancoma f1_3anan12 f0_3anan12 f2_3anan12 p_3anass f0_3anan12 f1_3anan12 f2_3anan12 a_w3a f1_3anan12 f0_3anan12 f2_3anan12 a_w3a f1_3anan12 f0_3anan12 f2_3anan12 a_wa a_wa p_bitri $.
$}

$(Triple conjunction expressed in terms of triple disjunction.  (Contributed
     by Jeff Hankins, 15-Aug-2009.) $)

${
	$v ph ps ch  $.
	f0_3anor $f wff ph $.
	f1_3anor $f wff ps $.
	f2_3anor $f wff ch $.
	p_3anor $p |- ( ( ph /\ ps /\ ch ) <-> -. ( -. ph \/ -. ps \/ -. ch ) ) $= f0_3anor f1_3anor f2_3anor a_df-3an f0_3anor f1_3anor a_wa f2_3anor p_anor f0_3anor f1_3anor p_ianor f0_3anor f1_3anor a_wa a_wn f0_3anor a_wn f1_3anor a_wn a_wo f2_3anor a_wn p_orbi1i f0_3anor f1_3anor a_wa f2_3anor a_wa f0_3anor f1_3anor a_wa a_wn f2_3anor a_wn a_wo f0_3anor a_wn f1_3anor a_wn a_wo f2_3anor a_wn a_wo p_xchbinx f0_3anor a_wn f1_3anor a_wn f2_3anor a_wn a_df-3or f0_3anor f1_3anor a_wa f2_3anor a_wa f0_3anor a_wn f1_3anor a_wn a_wo f2_3anor a_wn a_wo f0_3anor a_wn f1_3anor a_wn f2_3anor a_wn a_w3o p_xchbinxr f0_3anor f1_3anor f2_3anor a_w3a f0_3anor f1_3anor a_wa f2_3anor a_wa f0_3anor a_wn f1_3anor a_wn f2_3anor a_wn a_w3o a_wn p_bitri $.
$}

$(Negated triple conjunction expressed in terms of triple disjunction.
     (Contributed by Jeff Hankins, 15-Aug-2009.)  (Proof shortened by Andrew
     Salmon, 13-May-2011.) $)

${
	$v ph ps ch  $.
	f0_3ianor $f wff ph $.
	f1_3ianor $f wff ps $.
	f2_3ianor $f wff ch $.
	p_3ianor $p |- ( -. ( ph /\ ps /\ ch ) <-> ( -. ph \/ -. ps \/ -. ch ) ) $= f0_3ianor f1_3ianor f2_3ianor p_3anor f0_3ianor f1_3ianor f2_3ianor a_w3a f0_3ianor a_wn f1_3ianor a_wn f2_3ianor a_wn a_w3o p_con2bii f0_3ianor a_wn f1_3ianor a_wn f2_3ianor a_wn a_w3o f0_3ianor f1_3ianor f2_3ianor a_w3a a_wn p_bicomi $.
$}

$(Negated triple disjunction as triple conjunction.  (Contributed by Scott
     Fenton, 19-Apr-2011.) $)

${
	$v ph ps ch  $.
	f0_3ioran $f wff ph $.
	f1_3ioran $f wff ps $.
	f2_3ioran $f wff ch $.
	p_3ioran $p |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) ) $= f0_3ioran f1_3ioran p_ioran f0_3ioran f1_3ioran a_wo a_wn f0_3ioran a_wn f1_3ioran a_wn a_wa f2_3ioran a_wn p_anbi1i f0_3ioran f1_3ioran a_wo f2_3ioran p_ioran f0_3ioran f1_3ioran f2_3ioran a_df-3or f0_3ioran f1_3ioran a_wo f2_3ioran a_wo f0_3ioran f1_3ioran a_wo a_wn f2_3ioran a_wn a_wa f0_3ioran f1_3ioran f2_3ioran a_w3o p_xchnxbir f0_3ioran a_wn f1_3ioran a_wn f2_3ioran a_wn a_df-3an f0_3ioran f1_3ioran a_wo a_wn f2_3ioran a_wn a_wa f0_3ioran a_wn f1_3ioran a_wn a_wa f2_3ioran a_wn a_wa f0_3ioran f1_3ioran f2_3ioran a_w3o a_wn f0_3ioran a_wn f1_3ioran a_wn f2_3ioran a_wn a_w3a p_3bitr4i $.
$}

$(Triple disjunction in terms of triple conjunction.  (Contributed by NM,
     8-Oct-2012.) $)

${
	$v ph ps ch  $.
	f0_3oran $f wff ph $.
	f1_3oran $f wff ps $.
	f2_3oran $f wff ch $.
	p_3oran $p |- ( ( ph \/ ps \/ ch ) <-> -. ( -. ph /\ -. ps /\ -. ch ) ) $= f0_3oran f1_3oran f2_3oran p_3ioran f0_3oran f1_3oran f2_3oran a_w3o f0_3oran a_wn f1_3oran a_wn f2_3oran a_wn a_w3a p_con1bii f0_3oran a_wn f1_3oran a_wn f2_3oran a_wn a_w3a a_wn f0_3oran f1_3oran f2_3oran a_w3o p_bicomi $.
$}

$(Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_3simpa $f wff ph $.
	f1_3simpa $f wff ps $.
	f2_3simpa $f wff ch $.
	p_3simpa $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ps ) ) $= f0_3simpa f1_3simpa f2_3simpa a_df-3an f0_3simpa f1_3simpa f2_3simpa a_w3a f0_3simpa f1_3simpa a_wa f2_3simpa p_simplbi $.
$}

$(Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_3simpb $f wff ph $.
	f1_3simpb $f wff ps $.
	f2_3simpb $f wff ch $.
	p_3simpb $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ch ) ) $= f0_3simpb f1_3simpb f2_3simpb p_3ancomb f0_3simpb f2_3simpb f1_3simpb p_3simpa f0_3simpb f1_3simpb f2_3simpb a_w3a f0_3simpb f2_3simpb f1_3simpb a_w3a f0_3simpb f2_3simpb a_wa p_sylbi $.
$}

$(Simplification of triple conjunction.  (Contributed by NM, 21-Apr-1994.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v ph ps ch  $.
	f0_3simpc $f wff ph $.
	f1_3simpc $f wff ps $.
	f2_3simpc $f wff ch $.
	p_3simpc $p |- ( ( ph /\ ps /\ ch ) -> ( ps /\ ch ) ) $= f0_3simpc f1_3simpc f2_3simpc p_3anrot f1_3simpc f2_3simpc f0_3simpc p_3simpa f0_3simpc f1_3simpc f2_3simpc a_w3a f1_3simpc f2_3simpc f0_3simpc a_w3a f1_3simpc f2_3simpc a_wa p_sylbi $.
$}

$(Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_simp1 $f wff ph $.
	f1_simp1 $f wff ps $.
	f2_simp1 $f wff ch $.
	p_simp1 $p |- ( ( ph /\ ps /\ ch ) -> ph ) $= f0_simp1 f1_simp1 f2_simp1 p_3simpa f0_simp1 f1_simp1 f2_simp1 a_w3a f0_simp1 f1_simp1 p_simpld $.
$}

$(Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_simp2 $f wff ph $.
	f1_simp2 $f wff ps $.
	f2_simp2 $f wff ch $.
	p_simp2 $p |- ( ( ph /\ ps /\ ch ) -> ps ) $= f0_simp2 f1_simp2 f2_simp2 p_3simpa f0_simp2 f1_simp2 f2_simp2 a_w3a f0_simp2 f1_simp2 p_simprd $.
$}

$(Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_simp3 $f wff ph $.
	f1_simp3 $f wff ps $.
	f2_simp3 $f wff ch $.
	p_simp3 $p |- ( ( ph /\ ps /\ ch ) -> ch ) $= f0_simp3 f1_simp3 f2_simp3 p_3simpc f0_simp3 f1_simp3 f2_simp3 a_w3a f1_simp3 f2_simp3 p_simprd $.
$}

$(Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)

${
	$v ph ps ch th  $.
	f0_simpl1 $f wff ph $.
	f1_simpl1 $f wff ps $.
	f2_simpl1 $f wff ch $.
	f3_simpl1 $f wff th $.
	p_simpl1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ph ) $= f0_simpl1 f1_simpl1 f2_simpl1 p_simp1 f0_simpl1 f1_simpl1 f2_simpl1 a_w3a f0_simpl1 f3_simpl1 p_adantr $.
$}

$(Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)

${
	$v ph ps ch th  $.
	f0_simpl2 $f wff ph $.
	f1_simpl2 $f wff ps $.
	f2_simpl2 $f wff ch $.
	f3_simpl2 $f wff th $.
	p_simpl2 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ps ) $= f0_simpl2 f1_simpl2 f2_simpl2 p_simp2 f0_simpl2 f1_simpl2 f2_simpl2 a_w3a f1_simpl2 f3_simpl2 p_adantr $.
$}

$(Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)

${
	$v ph ps ch th  $.
	f0_simpl3 $f wff ph $.
	f1_simpl3 $f wff ps $.
	f2_simpl3 $f wff ch $.
	f3_simpl3 $f wff th $.
	p_simpl3 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ch ) $= f0_simpl3 f1_simpl3 f2_simpl3 p_simp3 f0_simpl3 f1_simpl3 f2_simpl3 a_w3a f2_simpl3 f3_simpl3 p_adantr $.
$}

$(Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)

${
	$v ph ps ch th  $.
	f0_simpr1 $f wff ph $.
	f1_simpr1 $f wff ps $.
	f2_simpr1 $f wff ch $.
	f3_simpr1 $f wff th $.
	p_simpr1 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ps ) $= f1_simpr1 f2_simpr1 f3_simpr1 p_simp1 f1_simpr1 f2_simpr1 f3_simpr1 a_w3a f1_simpr1 f0_simpr1 p_adantl $.
$}

$(Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)

${
	$v ph ps ch th  $.
	f0_simpr2 $f wff ph $.
	f1_simpr2 $f wff ps $.
	f2_simpr2 $f wff ch $.
	f3_simpr2 $f wff th $.
	p_simpr2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ch ) $= f1_simpr2 f2_simpr2 f3_simpr2 p_simp2 f1_simpr2 f2_simpr2 f3_simpr2 a_w3a f2_simpr2 f0_simpr2 p_adantl $.
$}

$(Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)

${
	$v ph ps ch th  $.
	f0_simpr3 $f wff ph $.
	f1_simpr3 $f wff ps $.
	f2_simpr3 $f wff ch $.
	f3_simpr3 $f wff th $.
	p_simpr3 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> th ) $= f1_simpr3 f2_simpr3 f3_simpr3 p_simp3 f1_simpr3 f2_simpr3 f3_simpr3 a_w3a f3_simpr3 f0_simpr3 p_adantl $.
$}

$(Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)

${
	$v ph ps ch  $.
	f0_simp1i $f wff ph $.
	f1_simp1i $f wff ps $.
	f2_simp1i $f wff ch $.
	e0_simp1i $e |- ( ph /\ ps /\ ch ) $.
	p_simp1i $p |- ph $= e0_simp1i f0_simp1i f1_simp1i f2_simp1i p_simp1 f0_simp1i f1_simp1i f2_simp1i a_w3a f0_simp1i a_ax-mp $.
$}

$(Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)

${
	$v ph ps ch  $.
	f0_simp2i $f wff ph $.
	f1_simp2i $f wff ps $.
	f2_simp2i $f wff ch $.
	e0_simp2i $e |- ( ph /\ ps /\ ch ) $.
	p_simp2i $p |- ps $= e0_simp2i f0_simp2i f1_simp2i f2_simp2i p_simp2 f0_simp2i f1_simp2i f2_simp2i a_w3a f1_simp2i a_ax-mp $.
$}

$(Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)

${
	$v ph ps ch  $.
	f0_simp3i $f wff ph $.
	f1_simp3i $f wff ps $.
	f2_simp3i $f wff ch $.
	e0_simp3i $e |- ( ph /\ ps /\ ch ) $.
	p_simp3i $p |- ch $= e0_simp3i f0_simp3i f1_simp3i f2_simp3i p_simp3 f0_simp3i f1_simp3i f2_simp3i a_w3a f2_simp3i a_ax-mp $.
$}

$(Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)

${
	$v ph ps ch th  $.
	f0_simp1d $f wff ph $.
	f1_simp1d $f wff ps $.
	f2_simp1d $f wff ch $.
	f3_simp1d $f wff th $.
	e0_simp1d $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
	p_simp1d $p |- ( ph -> ps ) $= e0_simp1d f1_simp1d f2_simp1d f3_simp1d p_simp1 f0_simp1d f1_simp1d f2_simp1d f3_simp1d a_w3a f1_simp1d p_syl $.
$}

$(Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)

${
	$v ph ps ch th  $.
	f0_simp2d $f wff ph $.
	f1_simp2d $f wff ps $.
	f2_simp2d $f wff ch $.
	f3_simp2d $f wff th $.
	e0_simp2d $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
	p_simp2d $p |- ( ph -> ch ) $= e0_simp2d f1_simp2d f2_simp2d f3_simp2d p_simp2 f0_simp2d f1_simp2d f2_simp2d f3_simp2d a_w3a f2_simp2d p_syl $.
$}

$(Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)

${
	$v ph ps ch th  $.
	f0_simp3d $f wff ph $.
	f1_simp3d $f wff ps $.
	f2_simp3d $f wff ch $.
	f3_simp3d $f wff th $.
	e0_simp3d $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
	p_simp3d $p |- ( ph -> th ) $= e0_simp3d f1_simp3d f2_simp3d f3_simp3d p_simp3 f0_simp3d f1_simp3d f2_simp3d f3_simp3d a_w3a f3_simp3d p_syl $.
$}

$(Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp1bi $f wff ph $.
	f1_simp1bi $f wff ps $.
	f2_simp1bi $f wff ch $.
	f3_simp1bi $f wff th $.
	e0_simp1bi $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
	p_simp1bi $p |- ( ph -> ps ) $= e0_simp1bi f0_simp1bi f1_simp1bi f2_simp1bi f3_simp1bi a_w3a p_biimpi f0_simp1bi f1_simp1bi f2_simp1bi f3_simp1bi p_simp1d $.
$}

$(Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp2bi $f wff ph $.
	f1_simp2bi $f wff ps $.
	f2_simp2bi $f wff ch $.
	f3_simp2bi $f wff th $.
	e0_simp2bi $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
	p_simp2bi $p |- ( ph -> ch ) $= e0_simp2bi f0_simp2bi f1_simp2bi f2_simp2bi f3_simp2bi a_w3a p_biimpi f0_simp2bi f1_simp2bi f2_simp2bi f3_simp2bi p_simp2d $.
$}

$(Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp3bi $f wff ph $.
	f1_simp3bi $f wff ps $.
	f2_simp3bi $f wff ch $.
	f3_simp3bi $f wff th $.
	e0_simp3bi $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
	p_simp3bi $p |- ( ph -> th ) $= e0_simp3bi f0_simp3bi f1_simp3bi f2_simp3bi f3_simp3bi a_w3a p_biimpi f0_simp3bi f1_simp3bi f2_simp3bi f3_simp3bi p_simp3d $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)

${
	$v ph ps ch th  $.
	f0_3adant1 $f wff ph $.
	f1_3adant1 $f wff ps $.
	f2_3adant1 $f wff ch $.
	f3_3adant1 $f wff th $.
	e0_3adant1 $e |- ( ( ph /\ ps ) -> ch ) $.
	p_3adant1 $p |- ( ( th /\ ph /\ ps ) -> ch ) $= f3_3adant1 f0_3adant1 f1_3adant1 p_3simpc e0_3adant1 f3_3adant1 f0_3adant1 f1_3adant1 a_w3a f0_3adant1 f1_3adant1 a_wa f2_3adant1 p_syl $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)

${
	$v ph ps ch th  $.
	f0_3adant2 $f wff ph $.
	f1_3adant2 $f wff ps $.
	f2_3adant2 $f wff ch $.
	f3_3adant2 $f wff th $.
	e0_3adant2 $e |- ( ( ph /\ ps ) -> ch ) $.
	p_3adant2 $p |- ( ( ph /\ th /\ ps ) -> ch ) $= f0_3adant2 f3_3adant2 f1_3adant2 p_3simpb e0_3adant2 f0_3adant2 f3_3adant2 f1_3adant2 a_w3a f0_3adant2 f1_3adant2 a_wa f2_3adant2 p_syl $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)

${
	$v ph ps ch th  $.
	f0_3adant3 $f wff ph $.
	f1_3adant3 $f wff ps $.
	f2_3adant3 $f wff ch $.
	f3_3adant3 $f wff th $.
	e0_3adant3 $e |- ( ( ph /\ ps ) -> ch ) $.
	p_3adant3 $p |- ( ( ph /\ ps /\ th ) -> ch ) $= f0_3adant3 f1_3adant3 f3_3adant3 p_3simpa e0_3adant3 f0_3adant3 f1_3adant3 f3_3adant3 a_w3a f0_3adant3 f1_3adant3 a_wa f2_3adant3 p_syl $.
$}

$(Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)

${
	$v ph ps ch th  $.
	f0_3ad2ant1 $f wff ph $.
	f1_3ad2ant1 $f wff ps $.
	f2_3ad2ant1 $f wff ch $.
	f3_3ad2ant1 $f wff th $.
	e0_3ad2ant1 $e |- ( ph -> ch ) $.
	p_3ad2ant1 $p |- ( ( ph /\ ps /\ th ) -> ch ) $= e0_3ad2ant1 f0_3ad2ant1 f2_3ad2ant1 f3_3ad2ant1 p_adantr f0_3ad2ant1 f3_3ad2ant1 f2_3ad2ant1 f1_3ad2ant1 p_3adant2 $.
$}

$(Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)

${
	$v ph ps ch th  $.
	f0_3ad2ant2 $f wff ph $.
	f1_3ad2ant2 $f wff ps $.
	f2_3ad2ant2 $f wff ch $.
	f3_3ad2ant2 $f wff th $.
	e0_3ad2ant2 $e |- ( ph -> ch ) $.
	p_3ad2ant2 $p |- ( ( ps /\ ph /\ th ) -> ch ) $= e0_3ad2ant2 f0_3ad2ant2 f2_3ad2ant2 f3_3ad2ant2 p_adantr f0_3ad2ant2 f3_3ad2ant2 f2_3ad2ant2 f1_3ad2ant2 p_3adant1 $.
$}

$(Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)

${
	$v ph ps ch th  $.
	f0_3ad2ant3 $f wff ph $.
	f1_3ad2ant3 $f wff ps $.
	f2_3ad2ant3 $f wff ch $.
	f3_3ad2ant3 $f wff th $.
	e0_3ad2ant3 $e |- ( ph -> ch ) $.
	p_3ad2ant3 $p |- ( ( ps /\ th /\ ph ) -> ch ) $= e0_3ad2ant3 f0_3ad2ant3 f2_3ad2ant3 f3_3ad2ant3 p_adantl f3_3ad2ant3 f0_3ad2ant3 f2_3ad2ant3 f1_3ad2ant3 p_3adant1 $.
$}

$(Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp1l $f wff ph $.
	f1_simp1l $f wff ps $.
	f2_simp1l $f wff ch $.
	f3_simp1l $f wff th $.
	p_simp1l $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ph ) $= f0_simp1l f1_simp1l p_simpl f0_simp1l f1_simp1l a_wa f2_simp1l f0_simp1l f3_simp1l p_3ad2ant1 $.
$}

$(Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp1r $f wff ph $.
	f1_simp1r $f wff ps $.
	f2_simp1r $f wff ch $.
	f3_simp1r $f wff th $.
	p_simp1r $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ps ) $= f0_simp1r f1_simp1r p_simpr f0_simp1r f1_simp1r a_wa f2_simp1r f1_simp1r f3_simp1r p_3ad2ant1 $.
$}

$(Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp2l $f wff ph $.
	f1_simp2l $f wff ps $.
	f2_simp2l $f wff ch $.
	f3_simp2l $f wff th $.
	p_simp2l $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ps ) $= f1_simp2l f2_simp2l p_simpl f1_simp2l f2_simp2l a_wa f0_simp2l f1_simp2l f3_simp2l p_3ad2ant2 $.
$}

$(Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp2r $f wff ph $.
	f1_simp2r $f wff ps $.
	f2_simp2r $f wff ch $.
	f3_simp2r $f wff th $.
	p_simp2r $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ch ) $= f1_simp2r f2_simp2r p_simpr f1_simp2r f2_simp2r a_wa f0_simp2r f2_simp2r f3_simp2r p_3ad2ant2 $.
$}

$(Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp3l $f wff ph $.
	f1_simp3l $f wff ps $.
	f2_simp3l $f wff ch $.
	f3_simp3l $f wff th $.
	p_simp3l $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> ch ) $= f2_simp3l f3_simp3l p_simpl f2_simp3l f3_simp3l a_wa f0_simp3l f2_simp3l f1_simp3l p_3ad2ant3 $.
$}

$(Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)

${
	$v ph ps ch th  $.
	f0_simp3r $f wff ph $.
	f1_simp3r $f wff ps $.
	f2_simp3r $f wff ch $.
	f3_simp3r $f wff th $.
	p_simp3r $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> th ) $= f2_simp3r f3_simp3r p_simpr f2_simp3r f3_simp3r a_wa f0_simp3r f3_simp3r f1_simp3r p_3ad2ant3 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp11 $f wff ph $.
	f1_simp11 $f wff ps $.
	f2_simp11 $f wff ch $.
	f3_simp11 $f wff th $.
	f4_simp11 $f wff ta $.
	p_simp11 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ph ) $= f0_simp11 f1_simp11 f2_simp11 p_simp1 f0_simp11 f1_simp11 f2_simp11 a_w3a f3_simp11 f0_simp11 f4_simp11 p_3ad2ant1 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp12 $f wff ph $.
	f1_simp12 $f wff ps $.
	f2_simp12 $f wff ch $.
	f3_simp12 $f wff th $.
	f4_simp12 $f wff ta $.
	p_simp12 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ps ) $= f0_simp12 f1_simp12 f2_simp12 p_simp2 f0_simp12 f1_simp12 f2_simp12 a_w3a f3_simp12 f1_simp12 f4_simp12 p_3ad2ant1 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp13 $f wff ph $.
	f1_simp13 $f wff ps $.
	f2_simp13 $f wff ch $.
	f3_simp13 $f wff th $.
	f4_simp13 $f wff ta $.
	p_simp13 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ch ) $= f0_simp13 f1_simp13 f2_simp13 p_simp3 f0_simp13 f1_simp13 f2_simp13 a_w3a f3_simp13 f2_simp13 f4_simp13 p_3ad2ant1 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp21 $f wff ph $.
	f1_simp21 $f wff ps $.
	f2_simp21 $f wff ch $.
	f3_simp21 $f wff th $.
	f4_simp21 $f wff ta $.
	p_simp21 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ps ) $= f1_simp21 f2_simp21 f3_simp21 p_simp1 f1_simp21 f2_simp21 f3_simp21 a_w3a f0_simp21 f1_simp21 f4_simp21 p_3ad2ant2 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp22 $f wff ph $.
	f1_simp22 $f wff ps $.
	f2_simp22 $f wff ch $.
	f3_simp22 $f wff th $.
	f4_simp22 $f wff ta $.
	p_simp22 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ch ) $= f1_simp22 f2_simp22 f3_simp22 p_simp2 f1_simp22 f2_simp22 f3_simp22 a_w3a f0_simp22 f2_simp22 f4_simp22 p_3ad2ant2 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp23 $f wff ph $.
	f1_simp23 $f wff ps $.
	f2_simp23 $f wff ch $.
	f3_simp23 $f wff th $.
	f4_simp23 $f wff ta $.
	p_simp23 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> th ) $= f1_simp23 f2_simp23 f3_simp23 p_simp3 f1_simp23 f2_simp23 f3_simp23 a_w3a f0_simp23 f3_simp23 f4_simp23 p_3ad2ant2 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp31 $f wff ph $.
	f1_simp31 $f wff ps $.
	f2_simp31 $f wff ch $.
	f3_simp31 $f wff th $.
	f4_simp31 $f wff ta $.
	p_simp31 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ch ) $= f2_simp31 f3_simp31 f4_simp31 p_simp1 f2_simp31 f3_simp31 f4_simp31 a_w3a f0_simp31 f2_simp31 f1_simp31 p_3ad2ant3 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp32 $f wff ph $.
	f1_simp32 $f wff ps $.
	f2_simp32 $f wff ch $.
	f3_simp32 $f wff th $.
	f4_simp32 $f wff ta $.
	p_simp32 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> th ) $= f2_simp32 f3_simp32 f4_simp32 p_simp2 f2_simp32 f3_simp32 f4_simp32 a_w3a f0_simp32 f3_simp32 f1_simp32 p_3ad2ant3 $.
$}

$(Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_simp33 $f wff ph $.
	f1_simp33 $f wff ps $.
	f2_simp33 $f wff ch $.
	f3_simp33 $f wff th $.
	f4_simp33 $f wff ta $.
	p_simp33 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ta ) $= f2_simp33 f3_simp33 f4_simp33 p_simp3 f2_simp33 f3_simp33 f4_simp33 a_w3a f0_simp33 f4_simp33 f1_simp33 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpll1 $f wff ph $.
	f1_simpll1 $f wff ps $.
	f2_simpll1 $f wff ch $.
	f3_simpll1 $f wff th $.
	f4_simpll1 $f wff ta $.
	p_simpll1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ph ) $= f0_simpll1 f1_simpll1 f2_simpll1 f3_simpll1 p_simpl1 f0_simpll1 f1_simpll1 f2_simpll1 a_w3a f3_simpll1 a_wa f0_simpll1 f4_simpll1 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpll2 $f wff ph $.
	f1_simpll2 $f wff ps $.
	f2_simpll2 $f wff ch $.
	f3_simpll2 $f wff th $.
	f4_simpll2 $f wff ta $.
	p_simpll2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ps ) $= f0_simpll2 f1_simpll2 f2_simpll2 f3_simpll2 p_simpl2 f0_simpll2 f1_simpll2 f2_simpll2 a_w3a f3_simpll2 a_wa f1_simpll2 f4_simpll2 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpll3 $f wff ph $.
	f1_simpll3 $f wff ps $.
	f2_simpll3 $f wff ch $.
	f3_simpll3 $f wff th $.
	f4_simpll3 $f wff ta $.
	p_simpll3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ch ) $= f0_simpll3 f1_simpll3 f2_simpll3 f3_simpll3 p_simpl3 f0_simpll3 f1_simpll3 f2_simpll3 a_w3a f3_simpll3 a_wa f2_simpll3 f4_simpll3 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simplr1 $f wff ph $.
	f1_simplr1 $f wff ps $.
	f2_simplr1 $f wff ch $.
	f3_simplr1 $f wff th $.
	f4_simplr1 $f wff ta $.
	p_simplr1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ph ) $= f3_simplr1 f0_simplr1 f1_simplr1 f2_simplr1 p_simpr1 f3_simplr1 f0_simplr1 f1_simplr1 f2_simplr1 a_w3a a_wa f0_simplr1 f4_simplr1 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simplr2 $f wff ph $.
	f1_simplr2 $f wff ps $.
	f2_simplr2 $f wff ch $.
	f3_simplr2 $f wff th $.
	f4_simplr2 $f wff ta $.
	p_simplr2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ps ) $= f3_simplr2 f0_simplr2 f1_simplr2 f2_simplr2 p_simpr2 f3_simplr2 f0_simplr2 f1_simplr2 f2_simplr2 a_w3a a_wa f1_simplr2 f4_simplr2 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simplr3 $f wff ph $.
	f1_simplr3 $f wff ps $.
	f2_simplr3 $f wff ch $.
	f3_simplr3 $f wff th $.
	f4_simplr3 $f wff ta $.
	p_simplr3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ch ) $= f3_simplr3 f0_simplr3 f1_simplr3 f2_simplr3 p_simpr3 f3_simplr3 f0_simplr3 f1_simplr3 f2_simplr3 a_w3a a_wa f2_simplr3 f4_simplr3 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simprl1 $f wff ph $.
	f1_simprl1 $f wff ps $.
	f2_simprl1 $f wff ch $.
	f3_simprl1 $f wff th $.
	f4_simprl1 $f wff ta $.
	p_simprl1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $= f0_simprl1 f1_simprl1 f2_simprl1 f3_simprl1 p_simpl1 f0_simprl1 f1_simprl1 f2_simprl1 a_w3a f3_simprl1 a_wa f0_simprl1 f4_simprl1 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simprl2 $f wff ph $.
	f1_simprl2 $f wff ps $.
	f2_simprl2 $f wff ch $.
	f3_simprl2 $f wff th $.
	f4_simprl2 $f wff ta $.
	p_simprl2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $= f0_simprl2 f1_simprl2 f2_simprl2 f3_simprl2 p_simpl2 f0_simprl2 f1_simprl2 f2_simprl2 a_w3a f3_simprl2 a_wa f1_simprl2 f4_simprl2 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simprl3 $f wff ph $.
	f1_simprl3 $f wff ps $.
	f2_simprl3 $f wff ch $.
	f3_simprl3 $f wff th $.
	f4_simprl3 $f wff ta $.
	p_simprl3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $= f0_simprl3 f1_simprl3 f2_simprl3 f3_simprl3 p_simpl3 f0_simprl3 f1_simprl3 f2_simprl3 a_w3a f3_simprl3 a_wa f2_simprl3 f4_simprl3 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simprr1 $f wff ph $.
	f1_simprr1 $f wff ps $.
	f2_simprr1 $f wff ch $.
	f3_simprr1 $f wff th $.
	f4_simprr1 $f wff ta $.
	p_simprr1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $= f3_simprr1 f0_simprr1 f1_simprr1 f2_simprr1 p_simpr1 f3_simprr1 f0_simprr1 f1_simprr1 f2_simprr1 a_w3a a_wa f0_simprr1 f4_simprr1 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simprr2 $f wff ph $.
	f1_simprr2 $f wff ps $.
	f2_simprr2 $f wff ch $.
	f3_simprr2 $f wff th $.
	f4_simprr2 $f wff ta $.
	p_simprr2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $= f3_simprr2 f0_simprr2 f1_simprr2 f2_simprr2 p_simpr2 f3_simprr2 f0_simprr2 f1_simprr2 f2_simprr2 a_w3a a_wa f1_simprr2 f4_simprr2 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simprr3 $f wff ph $.
	f1_simprr3 $f wff ps $.
	f2_simprr3 $f wff ch $.
	f3_simprr3 $f wff th $.
	f4_simprr3 $f wff ta $.
	p_simprr3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $= f3_simprr3 f0_simprr3 f1_simprr3 f2_simprr3 p_simpr3 f3_simprr3 f0_simprr3 f1_simprr3 f2_simprr3 a_w3a a_wa f2_simprr3 f4_simprr3 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpl1l $f wff ph $.
	f1_simpl1l $f wff ps $.
	f2_simpl1l $f wff ch $.
	f3_simpl1l $f wff th $.
	f4_simpl1l $f wff ta $.
	p_simpl1l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ph ) $= f0_simpl1l f1_simpl1l f2_simpl1l f3_simpl1l p_simp1l f0_simpl1l f1_simpl1l a_wa f2_simpl1l f3_simpl1l a_w3a f0_simpl1l f4_simpl1l p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpl1r $f wff ph $.
	f1_simpl1r $f wff ps $.
	f2_simpl1r $f wff ch $.
	f3_simpl1r $f wff th $.
	f4_simpl1r $f wff ta $.
	p_simpl1r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ps ) $= f0_simpl1r f1_simpl1r f2_simpl1r f3_simpl1r p_simp1r f0_simpl1r f1_simpl1r a_wa f2_simpl1r f3_simpl1r a_w3a f1_simpl1r f4_simpl1r p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpl2l $f wff ph $.
	f1_simpl2l $f wff ps $.
	f2_simpl2l $f wff ch $.
	f3_simpl2l $f wff th $.
	f4_simpl2l $f wff ta $.
	p_simpl2l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ph ) $= f2_simpl2l f0_simpl2l f1_simpl2l f3_simpl2l p_simp2l f2_simpl2l f0_simpl2l f1_simpl2l a_wa f3_simpl2l a_w3a f0_simpl2l f4_simpl2l p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpl2r $f wff ph $.
	f1_simpl2r $f wff ps $.
	f2_simpl2r $f wff ch $.
	f3_simpl2r $f wff th $.
	f4_simpl2r $f wff ta $.
	p_simpl2r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ps ) $= f2_simpl2r f0_simpl2r f1_simpl2r f3_simpl2r p_simp2r f2_simpl2r f0_simpl2r f1_simpl2r a_wa f3_simpl2r a_w3a f1_simpl2r f4_simpl2r p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpl3l $f wff ph $.
	f1_simpl3l $f wff ps $.
	f2_simpl3l $f wff ch $.
	f3_simpl3l $f wff th $.
	f4_simpl3l $f wff ta $.
	p_simpl3l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $= f2_simpl3l f3_simpl3l f0_simpl3l f1_simpl3l p_simp3l f2_simpl3l f3_simpl3l f0_simpl3l f1_simpl3l a_wa a_w3a f0_simpl3l f4_simpl3l p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpl3r $f wff ph $.
	f1_simpl3r $f wff ps $.
	f2_simpl3r $f wff ch $.
	f3_simpl3r $f wff th $.
	f4_simpl3r $f wff ta $.
	p_simpl3r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $= f2_simpl3r f3_simpl3r f0_simpl3r f1_simpl3r p_simp3r f2_simpl3r f3_simpl3r f0_simpl3r f1_simpl3r a_wa a_w3a f1_simpl3r f4_simpl3r p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpr1l $f wff ph $.
	f1_simpr1l $f wff ps $.
	f2_simpr1l $f wff ch $.
	f3_simpr1l $f wff th $.
	f4_simpr1l $f wff ta $.
	p_simpr1l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $= f0_simpr1l f1_simpr1l f2_simpr1l f3_simpr1l p_simp1l f0_simpr1l f1_simpr1l a_wa f2_simpr1l f3_simpr1l a_w3a f0_simpr1l f4_simpr1l p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpr1r $f wff ph $.
	f1_simpr1r $f wff ps $.
	f2_simpr1r $f wff ch $.
	f3_simpr1r $f wff th $.
	f4_simpr1r $f wff ta $.
	p_simpr1r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $= f0_simpr1r f1_simpr1r f2_simpr1r f3_simpr1r p_simp1r f0_simpr1r f1_simpr1r a_wa f2_simpr1r f3_simpr1r a_w3a f1_simpr1r f4_simpr1r p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpr2l $f wff ph $.
	f1_simpr2l $f wff ps $.
	f2_simpr2l $f wff ch $.
	f3_simpr2l $f wff th $.
	f4_simpr2l $f wff ta $.
	p_simpr2l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $= f2_simpr2l f0_simpr2l f1_simpr2l f3_simpr2l p_simp2l f2_simpr2l f0_simpr2l f1_simpr2l a_wa f3_simpr2l a_w3a f0_simpr2l f4_simpr2l p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpr2r $f wff ph $.
	f1_simpr2r $f wff ps $.
	f2_simpr2r $f wff ch $.
	f3_simpr2r $f wff th $.
	f4_simpr2r $f wff ta $.
	p_simpr2r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $= f2_simpr2r f0_simpr2r f1_simpr2r f3_simpr2r p_simp2r f2_simpr2r f0_simpr2r f1_simpr2r a_wa f3_simpr2r a_w3a f1_simpr2r f4_simpr2r p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpr3l $f wff ph $.
	f1_simpr3l $f wff ps $.
	f2_simpr3l $f wff ch $.
	f3_simpr3l $f wff th $.
	f4_simpr3l $f wff ta $.
	p_simpr3l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $= f2_simpr3l f3_simpr3l f0_simpr3l f1_simpr3l p_simp3l f2_simpr3l f3_simpr3l f0_simpr3l f1_simpr3l a_wa a_w3a f0_simpr3l f4_simpr3l p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simpr3r $f wff ph $.
	f1_simpr3r $f wff ps $.
	f2_simpr3r $f wff ch $.
	f3_simpr3r $f wff th $.
	f4_simpr3r $f wff ta $.
	p_simpr3r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $= f2_simpr3r f3_simpr3r f0_simpr3r f1_simpr3r p_simp3r f2_simpr3r f3_simpr3r f0_simpr3r f1_simpr3r a_wa a_w3a f1_simpr3r f4_simpr3r p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp1ll $f wff ph $.
	f1_simp1ll $f wff ps $.
	f2_simp1ll $f wff ch $.
	f3_simp1ll $f wff th $.
	f4_simp1ll $f wff ta $.
	p_simp1ll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ph ) $= f0_simp1ll f1_simp1ll f2_simp1ll p_simpll f0_simp1ll f1_simp1ll a_wa f2_simp1ll a_wa f3_simp1ll f0_simp1ll f4_simp1ll p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp1lr $f wff ph $.
	f1_simp1lr $f wff ps $.
	f2_simp1lr $f wff ch $.
	f3_simp1lr $f wff th $.
	f4_simp1lr $f wff ta $.
	p_simp1lr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ps ) $= f0_simp1lr f1_simp1lr f2_simp1lr p_simplr f0_simp1lr f1_simp1lr a_wa f2_simp1lr a_wa f3_simp1lr f1_simp1lr f4_simp1lr p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp1rl $f wff ph $.
	f1_simp1rl $f wff ps $.
	f2_simp1rl $f wff ch $.
	f3_simp1rl $f wff th $.
	f4_simp1rl $f wff ta $.
	p_simp1rl $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ph ) $= f2_simp1rl f0_simp1rl f1_simp1rl p_simprl f2_simp1rl f0_simp1rl f1_simp1rl a_wa a_wa f3_simp1rl f0_simp1rl f4_simp1rl p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp1rr $f wff ph $.
	f1_simp1rr $f wff ps $.
	f2_simp1rr $f wff ch $.
	f3_simp1rr $f wff th $.
	f4_simp1rr $f wff ta $.
	p_simp1rr $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ps ) $= f2_simp1rr f0_simp1rr f1_simp1rr p_simprr f2_simp1rr f0_simp1rr f1_simp1rr a_wa a_wa f3_simp1rr f1_simp1rr f4_simp1rr p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp2ll $f wff ph $.
	f1_simp2ll $f wff ps $.
	f2_simp2ll $f wff ch $.
	f3_simp2ll $f wff th $.
	f4_simp2ll $f wff ta $.
	p_simp2ll $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ph ) $= f0_simp2ll f1_simp2ll f2_simp2ll p_simpll f0_simp2ll f1_simp2ll a_wa f2_simp2ll a_wa f3_simp2ll f0_simp2ll f4_simp2ll p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp2lr $f wff ph $.
	f1_simp2lr $f wff ps $.
	f2_simp2lr $f wff ch $.
	f3_simp2lr $f wff th $.
	f4_simp2lr $f wff ta $.
	p_simp2lr $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ps ) $= f0_simp2lr f1_simp2lr f2_simp2lr p_simplr f0_simp2lr f1_simp2lr a_wa f2_simp2lr a_wa f3_simp2lr f1_simp2lr f4_simp2lr p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp2rl $f wff ph $.
	f1_simp2rl $f wff ps $.
	f2_simp2rl $f wff ch $.
	f3_simp2rl $f wff th $.
	f4_simp2rl $f wff ta $.
	p_simp2rl $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $= f2_simp2rl f0_simp2rl f1_simp2rl p_simprl f2_simp2rl f0_simp2rl f1_simp2rl a_wa a_wa f3_simp2rl f0_simp2rl f4_simp2rl p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp2rr $f wff ph $.
	f1_simp2rr $f wff ps $.
	f2_simp2rr $f wff ch $.
	f3_simp2rr $f wff th $.
	f4_simp2rr $f wff ta $.
	p_simp2rr $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $= f2_simp2rr f0_simp2rr f1_simp2rr p_simprr f2_simp2rr f0_simp2rr f1_simp2rr a_wa a_wa f3_simp2rr f1_simp2rr f4_simp2rr p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp3ll $f wff ph $.
	f1_simp3ll $f wff ps $.
	f2_simp3ll $f wff ch $.
	f3_simp3ll $f wff th $.
	f4_simp3ll $f wff ta $.
	p_simp3ll $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ph ) $= f0_simp3ll f1_simp3ll f2_simp3ll p_simpll f0_simp3ll f1_simp3ll a_wa f2_simp3ll a_wa f3_simp3ll f0_simp3ll f4_simp3ll p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp3lr $f wff ph $.
	f1_simp3lr $f wff ps $.
	f2_simp3lr $f wff ch $.
	f3_simp3lr $f wff th $.
	f4_simp3lr $f wff ta $.
	p_simp3lr $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ps ) $= f0_simp3lr f1_simp3lr f2_simp3lr p_simplr f0_simp3lr f1_simp3lr a_wa f2_simp3lr a_wa f3_simp3lr f1_simp3lr f4_simp3lr p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp3rl $f wff ph $.
	f1_simp3rl $f wff ps $.
	f2_simp3rl $f wff ch $.
	f3_simp3rl $f wff th $.
	f4_simp3rl $f wff ta $.
	p_simp3rl $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ph ) $= f2_simp3rl f0_simp3rl f1_simp3rl p_simprl f2_simp3rl f0_simp3rl f1_simp3rl a_wa a_wa f3_simp3rl f0_simp3rl f4_simp3rl p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_simp3rr $f wff ph $.
	f1_simp3rr $f wff ps $.
	f2_simp3rr $f wff ch $.
	f3_simp3rr $f wff th $.
	f4_simp3rr $f wff ta $.
	p_simp3rr $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ps ) $= f2_simp3rr f0_simp3rr f1_simp3rr p_simprr f2_simp3rr f0_simp3rr f1_simp3rr a_wa a_wa f3_simp3rr f1_simp3rr f4_simp3rr p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl11 $f wff ph $.
	f1_simpl11 $f wff ps $.
	f2_simpl11 $f wff ch $.
	f3_simpl11 $f wff th $.
	f4_simpl11 $f wff ta $.
	f5_simpl11 $f wff et $.
	p_simpl11 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ph ) $= f0_simpl11 f1_simpl11 f2_simpl11 f3_simpl11 f4_simpl11 p_simp11 f0_simpl11 f1_simpl11 f2_simpl11 a_w3a f3_simpl11 f4_simpl11 a_w3a f0_simpl11 f5_simpl11 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl12 $f wff ph $.
	f1_simpl12 $f wff ps $.
	f2_simpl12 $f wff ch $.
	f3_simpl12 $f wff th $.
	f4_simpl12 $f wff ta $.
	f5_simpl12 $f wff et $.
	p_simpl12 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ps ) $= f0_simpl12 f1_simpl12 f2_simpl12 f3_simpl12 f4_simpl12 p_simp12 f0_simpl12 f1_simpl12 f2_simpl12 a_w3a f3_simpl12 f4_simpl12 a_w3a f1_simpl12 f5_simpl12 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl13 $f wff ph $.
	f1_simpl13 $f wff ps $.
	f2_simpl13 $f wff ch $.
	f3_simpl13 $f wff th $.
	f4_simpl13 $f wff ta $.
	f5_simpl13 $f wff et $.
	p_simpl13 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ch ) $= f0_simpl13 f1_simpl13 f2_simpl13 f3_simpl13 f4_simpl13 p_simp13 f0_simpl13 f1_simpl13 f2_simpl13 a_w3a f3_simpl13 f4_simpl13 a_w3a f2_simpl13 f5_simpl13 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl21 $f wff ph $.
	f1_simpl21 $f wff ps $.
	f2_simpl21 $f wff ch $.
	f3_simpl21 $f wff th $.
	f4_simpl21 $f wff ta $.
	f5_simpl21 $f wff et $.
	p_simpl21 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ph ) $= f3_simpl21 f0_simpl21 f1_simpl21 f2_simpl21 f4_simpl21 p_simp21 f3_simpl21 f0_simpl21 f1_simpl21 f2_simpl21 a_w3a f4_simpl21 a_w3a f0_simpl21 f5_simpl21 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl22 $f wff ph $.
	f1_simpl22 $f wff ps $.
	f2_simpl22 $f wff ch $.
	f3_simpl22 $f wff th $.
	f4_simpl22 $f wff ta $.
	f5_simpl22 $f wff et $.
	p_simpl22 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ps ) $= f3_simpl22 f0_simpl22 f1_simpl22 f2_simpl22 f4_simpl22 p_simp22 f3_simpl22 f0_simpl22 f1_simpl22 f2_simpl22 a_w3a f4_simpl22 a_w3a f1_simpl22 f5_simpl22 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl23 $f wff ph $.
	f1_simpl23 $f wff ps $.
	f2_simpl23 $f wff ch $.
	f3_simpl23 $f wff th $.
	f4_simpl23 $f wff ta $.
	f5_simpl23 $f wff et $.
	p_simpl23 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ch ) $= f3_simpl23 f0_simpl23 f1_simpl23 f2_simpl23 f4_simpl23 p_simp23 f3_simpl23 f0_simpl23 f1_simpl23 f2_simpl23 a_w3a f4_simpl23 a_w3a f2_simpl23 f5_simpl23 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl31 $f wff ph $.
	f1_simpl31 $f wff ps $.
	f2_simpl31 $f wff ch $.
	f3_simpl31 $f wff th $.
	f4_simpl31 $f wff ta $.
	f5_simpl31 $f wff et $.
	p_simpl31 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $= f3_simpl31 f4_simpl31 f0_simpl31 f1_simpl31 f2_simpl31 p_simp31 f3_simpl31 f4_simpl31 f0_simpl31 f1_simpl31 f2_simpl31 a_w3a a_w3a f0_simpl31 f5_simpl31 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl32 $f wff ph $.
	f1_simpl32 $f wff ps $.
	f2_simpl32 $f wff ch $.
	f3_simpl32 $f wff th $.
	f4_simpl32 $f wff ta $.
	f5_simpl32 $f wff et $.
	p_simpl32 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $= f3_simpl32 f4_simpl32 f0_simpl32 f1_simpl32 f2_simpl32 p_simp32 f3_simpl32 f4_simpl32 f0_simpl32 f1_simpl32 f2_simpl32 a_w3a a_w3a f1_simpl32 f5_simpl32 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpl33 $f wff ph $.
	f1_simpl33 $f wff ps $.
	f2_simpl33 $f wff ch $.
	f3_simpl33 $f wff th $.
	f4_simpl33 $f wff ta $.
	f5_simpl33 $f wff et $.
	p_simpl33 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $= f3_simpl33 f4_simpl33 f0_simpl33 f1_simpl33 f2_simpl33 p_simp33 f3_simpl33 f4_simpl33 f0_simpl33 f1_simpl33 f2_simpl33 a_w3a a_w3a f2_simpl33 f5_simpl33 p_adantr $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr11 $f wff ph $.
	f1_simpr11 $f wff ps $.
	f2_simpr11 $f wff ch $.
	f3_simpr11 $f wff th $.
	f4_simpr11 $f wff ta $.
	f5_simpr11 $f wff et $.
	p_simpr11 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $= f0_simpr11 f1_simpr11 f2_simpr11 f3_simpr11 f4_simpr11 p_simp11 f0_simpr11 f1_simpr11 f2_simpr11 a_w3a f3_simpr11 f4_simpr11 a_w3a f0_simpr11 f5_simpr11 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr12 $f wff ph $.
	f1_simpr12 $f wff ps $.
	f2_simpr12 $f wff ch $.
	f3_simpr12 $f wff th $.
	f4_simpr12 $f wff ta $.
	f5_simpr12 $f wff et $.
	p_simpr12 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $= f0_simpr12 f1_simpr12 f2_simpr12 f3_simpr12 f4_simpr12 p_simp12 f0_simpr12 f1_simpr12 f2_simpr12 a_w3a f3_simpr12 f4_simpr12 a_w3a f1_simpr12 f5_simpr12 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr13 $f wff ph $.
	f1_simpr13 $f wff ps $.
	f2_simpr13 $f wff ch $.
	f3_simpr13 $f wff th $.
	f4_simpr13 $f wff ta $.
	f5_simpr13 $f wff et $.
	p_simpr13 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $= f0_simpr13 f1_simpr13 f2_simpr13 f3_simpr13 f4_simpr13 p_simp13 f0_simpr13 f1_simpr13 f2_simpr13 a_w3a f3_simpr13 f4_simpr13 a_w3a f2_simpr13 f5_simpr13 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr21 $f wff ph $.
	f1_simpr21 $f wff ps $.
	f2_simpr21 $f wff ch $.
	f3_simpr21 $f wff th $.
	f4_simpr21 $f wff ta $.
	f5_simpr21 $f wff et $.
	p_simpr21 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $= f3_simpr21 f0_simpr21 f1_simpr21 f2_simpr21 f4_simpr21 p_simp21 f3_simpr21 f0_simpr21 f1_simpr21 f2_simpr21 a_w3a f4_simpr21 a_w3a f0_simpr21 f5_simpr21 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr22 $f wff ph $.
	f1_simpr22 $f wff ps $.
	f2_simpr22 $f wff ch $.
	f3_simpr22 $f wff th $.
	f4_simpr22 $f wff ta $.
	f5_simpr22 $f wff et $.
	p_simpr22 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $= f3_simpr22 f0_simpr22 f1_simpr22 f2_simpr22 f4_simpr22 p_simp22 f3_simpr22 f0_simpr22 f1_simpr22 f2_simpr22 a_w3a f4_simpr22 a_w3a f1_simpr22 f5_simpr22 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr23 $f wff ph $.
	f1_simpr23 $f wff ps $.
	f2_simpr23 $f wff ch $.
	f3_simpr23 $f wff th $.
	f4_simpr23 $f wff ta $.
	f5_simpr23 $f wff et $.
	p_simpr23 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $= f3_simpr23 f0_simpr23 f1_simpr23 f2_simpr23 f4_simpr23 p_simp23 f3_simpr23 f0_simpr23 f1_simpr23 f2_simpr23 a_w3a f4_simpr23 a_w3a f2_simpr23 f5_simpr23 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr31 $f wff ph $.
	f1_simpr31 $f wff ps $.
	f2_simpr31 $f wff ch $.
	f3_simpr31 $f wff th $.
	f4_simpr31 $f wff ta $.
	f5_simpr31 $f wff et $.
	p_simpr31 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $= f3_simpr31 f4_simpr31 f0_simpr31 f1_simpr31 f2_simpr31 p_simp31 f3_simpr31 f4_simpr31 f0_simpr31 f1_simpr31 f2_simpr31 a_w3a a_w3a f0_simpr31 f5_simpr31 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr32 $f wff ph $.
	f1_simpr32 $f wff ps $.
	f2_simpr32 $f wff ch $.
	f3_simpr32 $f wff th $.
	f4_simpr32 $f wff ta $.
	f5_simpr32 $f wff et $.
	p_simpr32 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $= f3_simpr32 f4_simpr32 f0_simpr32 f1_simpr32 f2_simpr32 p_simp32 f3_simpr32 f4_simpr32 f0_simpr32 f1_simpr32 f2_simpr32 a_w3a a_w3a f1_simpr32 f5_simpr32 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simpr33 $f wff ph $.
	f1_simpr33 $f wff ps $.
	f2_simpr33 $f wff ch $.
	f3_simpr33 $f wff th $.
	f4_simpr33 $f wff ta $.
	f5_simpr33 $f wff et $.
	p_simpr33 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $= f3_simpr33 f4_simpr33 f0_simpr33 f1_simpr33 f2_simpr33 p_simp33 f3_simpr33 f4_simpr33 f0_simpr33 f1_simpr33 f2_simpr33 a_w3a a_w3a f2_simpr33 f5_simpr33 p_adantl $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp1l1 $f wff ph $.
	f1_simp1l1 $f wff ps $.
	f2_simp1l1 $f wff ch $.
	f3_simp1l1 $f wff th $.
	f4_simp1l1 $f wff ta $.
	f5_simp1l1 $f wff et $.
	p_simp1l1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ph ) $= f0_simp1l1 f1_simp1l1 f2_simp1l1 f3_simp1l1 p_simpl1 f0_simp1l1 f1_simp1l1 f2_simp1l1 a_w3a f3_simp1l1 a_wa f4_simp1l1 f0_simp1l1 f5_simp1l1 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp1l2 $f wff ph $.
	f1_simp1l2 $f wff ps $.
	f2_simp1l2 $f wff ch $.
	f3_simp1l2 $f wff th $.
	f4_simp1l2 $f wff ta $.
	f5_simp1l2 $f wff et $.
	p_simp1l2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ps ) $= f0_simp1l2 f1_simp1l2 f2_simp1l2 f3_simp1l2 p_simpl2 f0_simp1l2 f1_simp1l2 f2_simp1l2 a_w3a f3_simp1l2 a_wa f4_simp1l2 f1_simp1l2 f5_simp1l2 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp1l3 $f wff ph $.
	f1_simp1l3 $f wff ps $.
	f2_simp1l3 $f wff ch $.
	f3_simp1l3 $f wff th $.
	f4_simp1l3 $f wff ta $.
	f5_simp1l3 $f wff et $.
	p_simp1l3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ch ) $= f0_simp1l3 f1_simp1l3 f2_simp1l3 f3_simp1l3 p_simpl3 f0_simp1l3 f1_simp1l3 f2_simp1l3 a_w3a f3_simp1l3 a_wa f4_simp1l3 f2_simp1l3 f5_simp1l3 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp1r1 $f wff ph $.
	f1_simp1r1 $f wff ps $.
	f2_simp1r1 $f wff ch $.
	f3_simp1r1 $f wff th $.
	f4_simp1r1 $f wff ta $.
	f5_simp1r1 $f wff et $.
	p_simp1r1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ph ) $= f3_simp1r1 f0_simp1r1 f1_simp1r1 f2_simp1r1 p_simpr1 f3_simp1r1 f0_simp1r1 f1_simp1r1 f2_simp1r1 a_w3a a_wa f4_simp1r1 f0_simp1r1 f5_simp1r1 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp1r2 $f wff ph $.
	f1_simp1r2 $f wff ps $.
	f2_simp1r2 $f wff ch $.
	f3_simp1r2 $f wff th $.
	f4_simp1r2 $f wff ta $.
	f5_simp1r2 $f wff et $.
	p_simp1r2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ps ) $= f3_simp1r2 f0_simp1r2 f1_simp1r2 f2_simp1r2 p_simpr2 f3_simp1r2 f0_simp1r2 f1_simp1r2 f2_simp1r2 a_w3a a_wa f4_simp1r2 f1_simp1r2 f5_simp1r2 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp1r3 $f wff ph $.
	f1_simp1r3 $f wff ps $.
	f2_simp1r3 $f wff ch $.
	f3_simp1r3 $f wff th $.
	f4_simp1r3 $f wff ta $.
	f5_simp1r3 $f wff et $.
	p_simp1r3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ch ) $= f3_simp1r3 f0_simp1r3 f1_simp1r3 f2_simp1r3 p_simpr3 f3_simp1r3 f0_simp1r3 f1_simp1r3 f2_simp1r3 a_w3a a_wa f4_simp1r3 f2_simp1r3 f5_simp1r3 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp2l1 $f wff ph $.
	f1_simp2l1 $f wff ps $.
	f2_simp2l1 $f wff ch $.
	f3_simp2l1 $f wff th $.
	f4_simp2l1 $f wff ta $.
	f5_simp2l1 $f wff et $.
	p_simp2l1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ph ) $= f0_simp2l1 f1_simp2l1 f2_simp2l1 f3_simp2l1 p_simpl1 f0_simp2l1 f1_simp2l1 f2_simp2l1 a_w3a f3_simp2l1 a_wa f4_simp2l1 f0_simp2l1 f5_simp2l1 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp2l2 $f wff ph $.
	f1_simp2l2 $f wff ps $.
	f2_simp2l2 $f wff ch $.
	f3_simp2l2 $f wff th $.
	f4_simp2l2 $f wff ta $.
	f5_simp2l2 $f wff et $.
	p_simp2l2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ps ) $= f0_simp2l2 f1_simp2l2 f2_simp2l2 f3_simp2l2 p_simpl2 f0_simp2l2 f1_simp2l2 f2_simp2l2 a_w3a f3_simp2l2 a_wa f4_simp2l2 f1_simp2l2 f5_simp2l2 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp2l3 $f wff ph $.
	f1_simp2l3 $f wff ps $.
	f2_simp2l3 $f wff ch $.
	f3_simp2l3 $f wff th $.
	f4_simp2l3 $f wff ta $.
	f5_simp2l3 $f wff et $.
	p_simp2l3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ch ) $= f0_simp2l3 f1_simp2l3 f2_simp2l3 f3_simp2l3 p_simpl3 f0_simp2l3 f1_simp2l3 f2_simp2l3 a_w3a f3_simp2l3 a_wa f4_simp2l3 f2_simp2l3 f5_simp2l3 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp2r1 $f wff ph $.
	f1_simp2r1 $f wff ps $.
	f2_simp2r1 $f wff ch $.
	f3_simp2r1 $f wff th $.
	f4_simp2r1 $f wff ta $.
	f5_simp2r1 $f wff et $.
	p_simp2r1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $= f3_simp2r1 f0_simp2r1 f1_simp2r1 f2_simp2r1 p_simpr1 f3_simp2r1 f0_simp2r1 f1_simp2r1 f2_simp2r1 a_w3a a_wa f4_simp2r1 f0_simp2r1 f5_simp2r1 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp2r2 $f wff ph $.
	f1_simp2r2 $f wff ps $.
	f2_simp2r2 $f wff ch $.
	f3_simp2r2 $f wff th $.
	f4_simp2r2 $f wff ta $.
	f5_simp2r2 $f wff et $.
	p_simp2r2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $= f3_simp2r2 f0_simp2r2 f1_simp2r2 f2_simp2r2 p_simpr2 f3_simp2r2 f0_simp2r2 f1_simp2r2 f2_simp2r2 a_w3a a_wa f4_simp2r2 f1_simp2r2 f5_simp2r2 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp2r3 $f wff ph $.
	f1_simp2r3 $f wff ps $.
	f2_simp2r3 $f wff ch $.
	f3_simp2r3 $f wff th $.
	f4_simp2r3 $f wff ta $.
	f5_simp2r3 $f wff et $.
	p_simp2r3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $= f3_simp2r3 f0_simp2r3 f1_simp2r3 f2_simp2r3 p_simpr3 f3_simp2r3 f0_simp2r3 f1_simp2r3 f2_simp2r3 a_w3a a_wa f4_simp2r3 f2_simp2r3 f5_simp2r3 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp3l1 $f wff ph $.
	f1_simp3l1 $f wff ps $.
	f2_simp3l1 $f wff ch $.
	f3_simp3l1 $f wff th $.
	f4_simp3l1 $f wff ta $.
	f5_simp3l1 $f wff et $.
	p_simp3l1 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $= f0_simp3l1 f1_simp3l1 f2_simp3l1 f3_simp3l1 p_simpl1 f0_simp3l1 f1_simp3l1 f2_simp3l1 a_w3a f3_simp3l1 a_wa f4_simp3l1 f0_simp3l1 f5_simp3l1 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp3l2 $f wff ph $.
	f1_simp3l2 $f wff ps $.
	f2_simp3l2 $f wff ch $.
	f3_simp3l2 $f wff th $.
	f4_simp3l2 $f wff ta $.
	f5_simp3l2 $f wff et $.
	p_simp3l2 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $= f0_simp3l2 f1_simp3l2 f2_simp3l2 f3_simp3l2 p_simpl2 f0_simp3l2 f1_simp3l2 f2_simp3l2 a_w3a f3_simp3l2 a_wa f4_simp3l2 f1_simp3l2 f5_simp3l2 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp3l3 $f wff ph $.
	f1_simp3l3 $f wff ps $.
	f2_simp3l3 $f wff ch $.
	f3_simp3l3 $f wff th $.
	f4_simp3l3 $f wff ta $.
	f5_simp3l3 $f wff et $.
	p_simp3l3 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $= f0_simp3l3 f1_simp3l3 f2_simp3l3 f3_simp3l3 p_simpl3 f0_simp3l3 f1_simp3l3 f2_simp3l3 a_w3a f3_simp3l3 a_wa f4_simp3l3 f2_simp3l3 f5_simp3l3 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp3r1 $f wff ph $.
	f1_simp3r1 $f wff ps $.
	f2_simp3r1 $f wff ch $.
	f3_simp3r1 $f wff th $.
	f4_simp3r1 $f wff ta $.
	f5_simp3r1 $f wff et $.
	p_simp3r1 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $= f3_simp3r1 f0_simp3r1 f1_simp3r1 f2_simp3r1 p_simpr1 f3_simp3r1 f0_simp3r1 f1_simp3r1 f2_simp3r1 a_w3a a_wa f4_simp3r1 f0_simp3r1 f5_simp3r1 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp3r2 $f wff ph $.
	f1_simp3r2 $f wff ps $.
	f2_simp3r2 $f wff ch $.
	f3_simp3r2 $f wff th $.
	f4_simp3r2 $f wff ta $.
	f5_simp3r2 $f wff et $.
	p_simp3r2 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $= f3_simp3r2 f0_simp3r2 f1_simp3r2 f2_simp3r2 p_simpr2 f3_simp3r2 f0_simp3r2 f1_simp3r2 f2_simp3r2 a_w3a a_wa f4_simp3r2 f1_simp3r2 f5_simp3r2 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp3r3 $f wff ph $.
	f1_simp3r3 $f wff ps $.
	f2_simp3r3 $f wff ch $.
	f3_simp3r3 $f wff th $.
	f4_simp3r3 $f wff ta $.
	f5_simp3r3 $f wff et $.
	p_simp3r3 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $= f3_simp3r3 f0_simp3r3 f1_simp3r3 f2_simp3r3 p_simpr3 f3_simp3r3 f0_simp3r3 f1_simp3r3 f2_simp3r3 a_w3a a_wa f4_simp3r3 f2_simp3r3 f5_simp3r3 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp11l $f wff ph $.
	f1_simp11l $f wff ps $.
	f2_simp11l $f wff ch $.
	f3_simp11l $f wff th $.
	f4_simp11l $f wff ta $.
	f5_simp11l $f wff et $.
	p_simp11l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ph ) $= f0_simp11l f1_simp11l f2_simp11l f3_simp11l p_simp1l f0_simp11l f1_simp11l a_wa f2_simp11l f3_simp11l a_w3a f4_simp11l f0_simp11l f5_simp11l p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp11r $f wff ph $.
	f1_simp11r $f wff ps $.
	f2_simp11r $f wff ch $.
	f3_simp11r $f wff th $.
	f4_simp11r $f wff ta $.
	f5_simp11r $f wff et $.
	p_simp11r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ps ) $= f0_simp11r f1_simp11r f2_simp11r f3_simp11r p_simp1r f0_simp11r f1_simp11r a_wa f2_simp11r f3_simp11r a_w3a f4_simp11r f1_simp11r f5_simp11r p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp12l $f wff ph $.
	f1_simp12l $f wff ps $.
	f2_simp12l $f wff ch $.
	f3_simp12l $f wff th $.
	f4_simp12l $f wff ta $.
	f5_simp12l $f wff et $.
	p_simp12l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ph ) $= f2_simp12l f0_simp12l f1_simp12l f3_simp12l p_simp2l f2_simp12l f0_simp12l f1_simp12l a_wa f3_simp12l a_w3a f4_simp12l f0_simp12l f5_simp12l p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp12r $f wff ph $.
	f1_simp12r $f wff ps $.
	f2_simp12r $f wff ch $.
	f3_simp12r $f wff th $.
	f4_simp12r $f wff ta $.
	f5_simp12r $f wff et $.
	p_simp12r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ps ) $= f2_simp12r f0_simp12r f1_simp12r f3_simp12r p_simp2r f2_simp12r f0_simp12r f1_simp12r a_wa f3_simp12r a_w3a f4_simp12r f1_simp12r f5_simp12r p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp13l $f wff ph $.
	f1_simp13l $f wff ps $.
	f2_simp13l $f wff ch $.
	f3_simp13l $f wff th $.
	f4_simp13l $f wff ta $.
	f5_simp13l $f wff et $.
	p_simp13l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ph ) $= f2_simp13l f3_simp13l f0_simp13l f1_simp13l p_simp3l f2_simp13l f3_simp13l f0_simp13l f1_simp13l a_wa a_w3a f4_simp13l f0_simp13l f5_simp13l p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp13r $f wff ph $.
	f1_simp13r $f wff ps $.
	f2_simp13r $f wff ch $.
	f3_simp13r $f wff th $.
	f4_simp13r $f wff ta $.
	f5_simp13r $f wff et $.
	p_simp13r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ps ) $= f2_simp13r f3_simp13r f0_simp13r f1_simp13r p_simp3r f2_simp13r f3_simp13r f0_simp13r f1_simp13r a_wa a_w3a f4_simp13r f1_simp13r f5_simp13r p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp21l $f wff ph $.
	f1_simp21l $f wff ps $.
	f2_simp21l $f wff ch $.
	f3_simp21l $f wff th $.
	f4_simp21l $f wff ta $.
	f5_simp21l $f wff et $.
	p_simp21l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ph ) $= f0_simp21l f1_simp21l f2_simp21l f3_simp21l p_simp1l f0_simp21l f1_simp21l a_wa f2_simp21l f3_simp21l a_w3a f4_simp21l f0_simp21l f5_simp21l p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp21r $f wff ph $.
	f1_simp21r $f wff ps $.
	f2_simp21r $f wff ch $.
	f3_simp21r $f wff th $.
	f4_simp21r $f wff ta $.
	f5_simp21r $f wff et $.
	p_simp21r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ps ) $= f0_simp21r f1_simp21r f2_simp21r f3_simp21r p_simp1r f0_simp21r f1_simp21r a_wa f2_simp21r f3_simp21r a_w3a f4_simp21r f1_simp21r f5_simp21r p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp22l $f wff ph $.
	f1_simp22l $f wff ps $.
	f2_simp22l $f wff ch $.
	f3_simp22l $f wff th $.
	f4_simp22l $f wff ta $.
	f5_simp22l $f wff et $.
	p_simp22l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ph ) $= f2_simp22l f0_simp22l f1_simp22l f3_simp22l p_simp2l f2_simp22l f0_simp22l f1_simp22l a_wa f3_simp22l a_w3a f4_simp22l f0_simp22l f5_simp22l p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp22r $f wff ph $.
	f1_simp22r $f wff ps $.
	f2_simp22r $f wff ch $.
	f3_simp22r $f wff th $.
	f4_simp22r $f wff ta $.
	f5_simp22r $f wff et $.
	p_simp22r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ps ) $= f2_simp22r f0_simp22r f1_simp22r f3_simp22r p_simp2r f2_simp22r f0_simp22r f1_simp22r a_wa f3_simp22r a_w3a f4_simp22r f1_simp22r f5_simp22r p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp23l $f wff ph $.
	f1_simp23l $f wff ps $.
	f2_simp23l $f wff ch $.
	f3_simp23l $f wff th $.
	f4_simp23l $f wff ta $.
	f5_simp23l $f wff et $.
	p_simp23l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ph ) $= f2_simp23l f3_simp23l f0_simp23l f1_simp23l p_simp3l f2_simp23l f3_simp23l f0_simp23l f1_simp23l a_wa a_w3a f4_simp23l f0_simp23l f5_simp23l p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp23r $f wff ph $.
	f1_simp23r $f wff ps $.
	f2_simp23r $f wff ch $.
	f3_simp23r $f wff th $.
	f4_simp23r $f wff ta $.
	f5_simp23r $f wff et $.
	p_simp23r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ps ) $= f2_simp23r f3_simp23r f0_simp23r f1_simp23r p_simp3r f2_simp23r f3_simp23r f0_simp23r f1_simp23r a_wa a_w3a f4_simp23r f1_simp23r f5_simp23r p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp31l $f wff ph $.
	f1_simp31l $f wff ps $.
	f2_simp31l $f wff ch $.
	f3_simp31l $f wff th $.
	f4_simp31l $f wff ta $.
	f5_simp31l $f wff et $.
	p_simp31l $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $= f0_simp31l f1_simp31l f2_simp31l f3_simp31l p_simp1l f0_simp31l f1_simp31l a_wa f2_simp31l f3_simp31l a_w3a f4_simp31l f0_simp31l f5_simp31l p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp31r $f wff ph $.
	f1_simp31r $f wff ps $.
	f2_simp31r $f wff ch $.
	f3_simp31r $f wff th $.
	f4_simp31r $f wff ta $.
	f5_simp31r $f wff et $.
	p_simp31r $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $= f0_simp31r f1_simp31r f2_simp31r f3_simp31r p_simp1r f0_simp31r f1_simp31r a_wa f2_simp31r f3_simp31r a_w3a f4_simp31r f1_simp31r f5_simp31r p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp32l $f wff ph $.
	f1_simp32l $f wff ps $.
	f2_simp32l $f wff ch $.
	f3_simp32l $f wff th $.
	f4_simp32l $f wff ta $.
	f5_simp32l $f wff et $.
	p_simp32l $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $= f2_simp32l f0_simp32l f1_simp32l f3_simp32l p_simp2l f2_simp32l f0_simp32l f1_simp32l a_wa f3_simp32l a_w3a f4_simp32l f0_simp32l f5_simp32l p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp32r $f wff ph $.
	f1_simp32r $f wff ps $.
	f2_simp32r $f wff ch $.
	f3_simp32r $f wff th $.
	f4_simp32r $f wff ta $.
	f5_simp32r $f wff et $.
	p_simp32r $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $= f2_simp32r f0_simp32r f1_simp32r f3_simp32r p_simp2r f2_simp32r f0_simp32r f1_simp32r a_wa f3_simp32r a_w3a f4_simp32r f1_simp32r f5_simp32r p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp33l $f wff ph $.
	f1_simp33l $f wff ps $.
	f2_simp33l $f wff ch $.
	f3_simp33l $f wff th $.
	f4_simp33l $f wff ta $.
	f5_simp33l $f wff et $.
	p_simp33l $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $= f2_simp33l f3_simp33l f0_simp33l f1_simp33l p_simp3l f2_simp33l f3_simp33l f0_simp33l f1_simp33l a_wa a_w3a f4_simp33l f0_simp33l f5_simp33l p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp33r $f wff ph $.
	f1_simp33r $f wff ps $.
	f2_simp33r $f wff ch $.
	f3_simp33r $f wff th $.
	f4_simp33r $f wff ta $.
	f5_simp33r $f wff et $.
	p_simp33r $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $= f2_simp33r f3_simp33r f0_simp33r f1_simp33r p_simp3r f2_simp33r f3_simp33r f0_simp33r f1_simp33r a_wa a_w3a f4_simp33r f1_simp33r f5_simp33r p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp111 $f wff ph $.
	f1_simp111 $f wff ps $.
	f2_simp111 $f wff ch $.
	f3_simp111 $f wff th $.
	f4_simp111 $f wff ta $.
	f5_simp111 $f wff et $.
	f6_simp111 $f wff ze $.
	p_simp111 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ph ) $= f0_simp111 f1_simp111 f2_simp111 f3_simp111 f4_simp111 p_simp11 f0_simp111 f1_simp111 f2_simp111 a_w3a f3_simp111 f4_simp111 a_w3a f5_simp111 f0_simp111 f6_simp111 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp112 $f wff ph $.
	f1_simp112 $f wff ps $.
	f2_simp112 $f wff ch $.
	f3_simp112 $f wff th $.
	f4_simp112 $f wff ta $.
	f5_simp112 $f wff et $.
	f6_simp112 $f wff ze $.
	p_simp112 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ps ) $= f0_simp112 f1_simp112 f2_simp112 f3_simp112 f4_simp112 p_simp12 f0_simp112 f1_simp112 f2_simp112 a_w3a f3_simp112 f4_simp112 a_w3a f5_simp112 f1_simp112 f6_simp112 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp113 $f wff ph $.
	f1_simp113 $f wff ps $.
	f2_simp113 $f wff ch $.
	f3_simp113 $f wff th $.
	f4_simp113 $f wff ta $.
	f5_simp113 $f wff et $.
	f6_simp113 $f wff ze $.
	p_simp113 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ch ) $= f0_simp113 f1_simp113 f2_simp113 f3_simp113 f4_simp113 p_simp13 f0_simp113 f1_simp113 f2_simp113 a_w3a f3_simp113 f4_simp113 a_w3a f5_simp113 f2_simp113 f6_simp113 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp121 $f wff ph $.
	f1_simp121 $f wff ps $.
	f2_simp121 $f wff ch $.
	f3_simp121 $f wff th $.
	f4_simp121 $f wff ta $.
	f5_simp121 $f wff et $.
	f6_simp121 $f wff ze $.
	p_simp121 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ph ) $= f3_simp121 f0_simp121 f1_simp121 f2_simp121 f4_simp121 p_simp21 f3_simp121 f0_simp121 f1_simp121 f2_simp121 a_w3a f4_simp121 a_w3a f5_simp121 f0_simp121 f6_simp121 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp122 $f wff ph $.
	f1_simp122 $f wff ps $.
	f2_simp122 $f wff ch $.
	f3_simp122 $f wff th $.
	f4_simp122 $f wff ta $.
	f5_simp122 $f wff et $.
	f6_simp122 $f wff ze $.
	p_simp122 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ps ) $= f3_simp122 f0_simp122 f1_simp122 f2_simp122 f4_simp122 p_simp22 f3_simp122 f0_simp122 f1_simp122 f2_simp122 a_w3a f4_simp122 a_w3a f5_simp122 f1_simp122 f6_simp122 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp123 $f wff ph $.
	f1_simp123 $f wff ps $.
	f2_simp123 $f wff ch $.
	f3_simp123 $f wff th $.
	f4_simp123 $f wff ta $.
	f5_simp123 $f wff et $.
	f6_simp123 $f wff ze $.
	p_simp123 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ch ) $= f3_simp123 f0_simp123 f1_simp123 f2_simp123 f4_simp123 p_simp23 f3_simp123 f0_simp123 f1_simp123 f2_simp123 a_w3a f4_simp123 a_w3a f5_simp123 f2_simp123 f6_simp123 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp131 $f wff ph $.
	f1_simp131 $f wff ps $.
	f2_simp131 $f wff ch $.
	f3_simp131 $f wff th $.
	f4_simp131 $f wff ta $.
	f5_simp131 $f wff et $.
	f6_simp131 $f wff ze $.
	p_simp131 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ph ) $= f3_simp131 f4_simp131 f0_simp131 f1_simp131 f2_simp131 p_simp31 f3_simp131 f4_simp131 f0_simp131 f1_simp131 f2_simp131 a_w3a a_w3a f5_simp131 f0_simp131 f6_simp131 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp132 $f wff ph $.
	f1_simp132 $f wff ps $.
	f2_simp132 $f wff ch $.
	f3_simp132 $f wff th $.
	f4_simp132 $f wff ta $.
	f5_simp132 $f wff et $.
	f6_simp132 $f wff ze $.
	p_simp132 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ps ) $= f3_simp132 f4_simp132 f0_simp132 f1_simp132 f2_simp132 p_simp32 f3_simp132 f4_simp132 f0_simp132 f1_simp132 f2_simp132 a_w3a a_w3a f5_simp132 f1_simp132 f6_simp132 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp133 $f wff ph $.
	f1_simp133 $f wff ps $.
	f2_simp133 $f wff ch $.
	f3_simp133 $f wff th $.
	f4_simp133 $f wff ta $.
	f5_simp133 $f wff et $.
	f6_simp133 $f wff ze $.
	p_simp133 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ch ) $= f3_simp133 f4_simp133 f0_simp133 f1_simp133 f2_simp133 p_simp33 f3_simp133 f4_simp133 f0_simp133 f1_simp133 f2_simp133 a_w3a a_w3a f5_simp133 f2_simp133 f6_simp133 p_3ad2ant1 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp211 $f wff ph $.
	f1_simp211 $f wff ps $.
	f2_simp211 $f wff ch $.
	f3_simp211 $f wff th $.
	f4_simp211 $f wff ta $.
	f5_simp211 $f wff et $.
	f6_simp211 $f wff ze $.
	p_simp211 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ph ) $= f0_simp211 f1_simp211 f2_simp211 f3_simp211 f4_simp211 p_simp11 f0_simp211 f1_simp211 f2_simp211 a_w3a f3_simp211 f4_simp211 a_w3a f5_simp211 f0_simp211 f6_simp211 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp212 $f wff ph $.
	f1_simp212 $f wff ps $.
	f2_simp212 $f wff ch $.
	f3_simp212 $f wff th $.
	f4_simp212 $f wff ta $.
	f5_simp212 $f wff et $.
	f6_simp212 $f wff ze $.
	p_simp212 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ps ) $= f0_simp212 f1_simp212 f2_simp212 f3_simp212 f4_simp212 p_simp12 f0_simp212 f1_simp212 f2_simp212 a_w3a f3_simp212 f4_simp212 a_w3a f5_simp212 f1_simp212 f6_simp212 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp213 $f wff ph $.
	f1_simp213 $f wff ps $.
	f2_simp213 $f wff ch $.
	f3_simp213 $f wff th $.
	f4_simp213 $f wff ta $.
	f5_simp213 $f wff et $.
	f6_simp213 $f wff ze $.
	p_simp213 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ch ) $= f0_simp213 f1_simp213 f2_simp213 f3_simp213 f4_simp213 p_simp13 f0_simp213 f1_simp213 f2_simp213 a_w3a f3_simp213 f4_simp213 a_w3a f5_simp213 f2_simp213 f6_simp213 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp221 $f wff ph $.
	f1_simp221 $f wff ps $.
	f2_simp221 $f wff ch $.
	f3_simp221 $f wff th $.
	f4_simp221 $f wff ta $.
	f5_simp221 $f wff et $.
	f6_simp221 $f wff ze $.
	p_simp221 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ph ) $= f3_simp221 f0_simp221 f1_simp221 f2_simp221 f4_simp221 p_simp21 f3_simp221 f0_simp221 f1_simp221 f2_simp221 a_w3a f4_simp221 a_w3a f5_simp221 f0_simp221 f6_simp221 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp222 $f wff ph $.
	f1_simp222 $f wff ps $.
	f2_simp222 $f wff ch $.
	f3_simp222 $f wff th $.
	f4_simp222 $f wff ta $.
	f5_simp222 $f wff et $.
	f6_simp222 $f wff ze $.
	p_simp222 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ps ) $= f3_simp222 f0_simp222 f1_simp222 f2_simp222 f4_simp222 p_simp22 f3_simp222 f0_simp222 f1_simp222 f2_simp222 a_w3a f4_simp222 a_w3a f5_simp222 f1_simp222 f6_simp222 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp223 $f wff ph $.
	f1_simp223 $f wff ps $.
	f2_simp223 $f wff ch $.
	f3_simp223 $f wff th $.
	f4_simp223 $f wff ta $.
	f5_simp223 $f wff et $.
	f6_simp223 $f wff ze $.
	p_simp223 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ch ) $= f3_simp223 f0_simp223 f1_simp223 f2_simp223 f4_simp223 p_simp23 f3_simp223 f0_simp223 f1_simp223 f2_simp223 a_w3a f4_simp223 a_w3a f5_simp223 f2_simp223 f6_simp223 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp231 $f wff ph $.
	f1_simp231 $f wff ps $.
	f2_simp231 $f wff ch $.
	f3_simp231 $f wff th $.
	f4_simp231 $f wff ta $.
	f5_simp231 $f wff et $.
	f6_simp231 $f wff ze $.
	p_simp231 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ph ) $= f3_simp231 f4_simp231 f0_simp231 f1_simp231 f2_simp231 p_simp31 f3_simp231 f4_simp231 f0_simp231 f1_simp231 f2_simp231 a_w3a a_w3a f5_simp231 f0_simp231 f6_simp231 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp232 $f wff ph $.
	f1_simp232 $f wff ps $.
	f2_simp232 $f wff ch $.
	f3_simp232 $f wff th $.
	f4_simp232 $f wff ta $.
	f5_simp232 $f wff et $.
	f6_simp232 $f wff ze $.
	p_simp232 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ps ) $= f3_simp232 f4_simp232 f0_simp232 f1_simp232 f2_simp232 p_simp32 f3_simp232 f4_simp232 f0_simp232 f1_simp232 f2_simp232 a_w3a a_w3a f5_simp232 f1_simp232 f6_simp232 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp233 $f wff ph $.
	f1_simp233 $f wff ps $.
	f2_simp233 $f wff ch $.
	f3_simp233 $f wff th $.
	f4_simp233 $f wff ta $.
	f5_simp233 $f wff et $.
	f6_simp233 $f wff ze $.
	p_simp233 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ch ) $= f3_simp233 f4_simp233 f0_simp233 f1_simp233 f2_simp233 p_simp33 f3_simp233 f4_simp233 f0_simp233 f1_simp233 f2_simp233 a_w3a a_w3a f5_simp233 f2_simp233 f6_simp233 p_3ad2ant2 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp311 $f wff ph $.
	f1_simp311 $f wff ps $.
	f2_simp311 $f wff ch $.
	f3_simp311 $f wff th $.
	f4_simp311 $f wff ta $.
	f5_simp311 $f wff et $.
	f6_simp311 $f wff ze $.
	p_simp311 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $= f0_simp311 f1_simp311 f2_simp311 f3_simp311 f4_simp311 p_simp11 f0_simp311 f1_simp311 f2_simp311 a_w3a f3_simp311 f4_simp311 a_w3a f5_simp311 f0_simp311 f6_simp311 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp312 $f wff ph $.
	f1_simp312 $f wff ps $.
	f2_simp312 $f wff ch $.
	f3_simp312 $f wff th $.
	f4_simp312 $f wff ta $.
	f5_simp312 $f wff et $.
	f6_simp312 $f wff ze $.
	p_simp312 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $= f0_simp312 f1_simp312 f2_simp312 f3_simp312 f4_simp312 p_simp12 f0_simp312 f1_simp312 f2_simp312 a_w3a f3_simp312 f4_simp312 a_w3a f5_simp312 f1_simp312 f6_simp312 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp313 $f wff ph $.
	f1_simp313 $f wff ps $.
	f2_simp313 $f wff ch $.
	f3_simp313 $f wff th $.
	f4_simp313 $f wff ta $.
	f5_simp313 $f wff et $.
	f6_simp313 $f wff ze $.
	p_simp313 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $= f0_simp313 f1_simp313 f2_simp313 f3_simp313 f4_simp313 p_simp13 f0_simp313 f1_simp313 f2_simp313 a_w3a f3_simp313 f4_simp313 a_w3a f5_simp313 f2_simp313 f6_simp313 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp321 $f wff ph $.
	f1_simp321 $f wff ps $.
	f2_simp321 $f wff ch $.
	f3_simp321 $f wff th $.
	f4_simp321 $f wff ta $.
	f5_simp321 $f wff et $.
	f6_simp321 $f wff ze $.
	p_simp321 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $= f3_simp321 f0_simp321 f1_simp321 f2_simp321 f4_simp321 p_simp21 f3_simp321 f0_simp321 f1_simp321 f2_simp321 a_w3a f4_simp321 a_w3a f5_simp321 f0_simp321 f6_simp321 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp322 $f wff ph $.
	f1_simp322 $f wff ps $.
	f2_simp322 $f wff ch $.
	f3_simp322 $f wff th $.
	f4_simp322 $f wff ta $.
	f5_simp322 $f wff et $.
	f6_simp322 $f wff ze $.
	p_simp322 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $= f3_simp322 f0_simp322 f1_simp322 f2_simp322 f4_simp322 p_simp22 f3_simp322 f0_simp322 f1_simp322 f2_simp322 a_w3a f4_simp322 a_w3a f5_simp322 f1_simp322 f6_simp322 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp323 $f wff ph $.
	f1_simp323 $f wff ps $.
	f2_simp323 $f wff ch $.
	f3_simp323 $f wff th $.
	f4_simp323 $f wff ta $.
	f5_simp323 $f wff et $.
	f6_simp323 $f wff ze $.
	p_simp323 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $= f3_simp323 f0_simp323 f1_simp323 f2_simp323 f4_simp323 p_simp23 f3_simp323 f0_simp323 f1_simp323 f2_simp323 a_w3a f4_simp323 a_w3a f5_simp323 f2_simp323 f6_simp323 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp331 $f wff ph $.
	f1_simp331 $f wff ps $.
	f2_simp331 $f wff ch $.
	f3_simp331 $f wff th $.
	f4_simp331 $f wff ta $.
	f5_simp331 $f wff et $.
	f6_simp331 $f wff ze $.
	p_simp331 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $= f3_simp331 f4_simp331 f0_simp331 f1_simp331 f2_simp331 p_simp31 f3_simp331 f4_simp331 f0_simp331 f1_simp331 f2_simp331 a_w3a a_w3a f5_simp331 f0_simp331 f6_simp331 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp332 $f wff ph $.
	f1_simp332 $f wff ps $.
	f2_simp332 $f wff ch $.
	f3_simp332 $f wff th $.
	f4_simp332 $f wff ta $.
	f5_simp332 $f wff et $.
	f6_simp332 $f wff ze $.
	p_simp332 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $= f3_simp332 f4_simp332 f0_simp332 f1_simp332 f2_simp332 p_simp32 f3_simp332 f4_simp332 f0_simp332 f1_simp332 f2_simp332 a_w3a a_w3a f5_simp332 f1_simp332 f6_simp332 p_3ad2ant3 $.
$}

$(Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp333 $f wff ph $.
	f1_simp333 $f wff ps $.
	f2_simp333 $f wff ch $.
	f3_simp333 $f wff th $.
	f4_simp333 $f wff ta $.
	f5_simp333 $f wff et $.
	f6_simp333 $f wff ze $.
	p_simp333 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $= f3_simp333 f4_simp333 f0_simp333 f1_simp333 f2_simp333 p_simp33 f3_simp333 f4_simp333 f0_simp333 f1_simp333 f2_simp333 a_w3a a_w3a f5_simp333 f2_simp333 f6_simp333 p_3ad2ant3 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3adantl1 $f wff ph $.
	f1_3adantl1 $f wff ps $.
	f2_3adantl1 $f wff ch $.
	f3_3adantl1 $f wff th $.
	f4_3adantl1 $f wff ta $.
	e0_3adantl1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_3adantl1 $p |- ( ( ( ta /\ ph /\ ps ) /\ ch ) -> th ) $= f4_3adantl1 f0_3adantl1 f1_3adantl1 p_3simpc e0_3adantl1 f4_3adantl1 f0_3adantl1 f1_3adantl1 a_w3a f0_3adantl1 f1_3adantl1 a_wa f2_3adantl1 f3_3adantl1 p_sylan $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3adantl2 $f wff ph $.
	f1_3adantl2 $f wff ps $.
	f2_3adantl2 $f wff ch $.
	f3_3adantl2 $f wff th $.
	f4_3adantl2 $f wff ta $.
	e0_3adantl2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_3adantl2 $p |- ( ( ( ph /\ ta /\ ps ) /\ ch ) -> th ) $= f0_3adantl2 f4_3adantl2 f1_3adantl2 p_3simpb e0_3adantl2 f0_3adantl2 f4_3adantl2 f1_3adantl2 a_w3a f0_3adantl2 f1_3adantl2 a_wa f2_3adantl2 f3_3adantl2 p_sylan $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3adantl3 $f wff ph $.
	f1_3adantl3 $f wff ps $.
	f2_3adantl3 $f wff ch $.
	f3_3adantl3 $f wff th $.
	f4_3adantl3 $f wff ta $.
	e0_3adantl3 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_3adantl3 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $= f0_3adantl3 f1_3adantl3 f4_3adantl3 p_3simpa e0_3adantl3 f0_3adantl3 f1_3adantl3 f4_3adantl3 a_w3a f0_3adantl3 f1_3adantl3 a_wa f2_3adantl3 f3_3adantl3 p_sylan $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3adantr1 $f wff ph $.
	f1_3adantr1 $f wff ps $.
	f2_3adantr1 $f wff ch $.
	f3_3adantr1 $f wff th $.
	f4_3adantr1 $f wff ta $.
	e0_3adantr1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_3adantr1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $= f4_3adantr1 f1_3adantr1 f2_3adantr1 p_3simpc e0_3adantr1 f4_3adantr1 f1_3adantr1 f2_3adantr1 a_w3a f0_3adantr1 f1_3adantr1 f2_3adantr1 a_wa f3_3adantr1 p_sylan2 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3adantr2 $f wff ph $.
	f1_3adantr2 $f wff ps $.
	f2_3adantr2 $f wff ch $.
	f3_3adantr2 $f wff th $.
	f4_3adantr2 $f wff ta $.
	e0_3adantr2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_3adantr2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $= f1_3adantr2 f4_3adantr2 f2_3adantr2 p_3simpb e0_3adantr2 f1_3adantr2 f4_3adantr2 f2_3adantr2 a_w3a f0_3adantr2 f1_3adantr2 f2_3adantr2 a_wa f3_3adantr2 p_sylan2 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3adantr3 $f wff ph $.
	f1_3adantr3 $f wff ps $.
	f2_3adantr3 $f wff ch $.
	f3_3adantr3 $f wff th $.
	f4_3adantr3 $f wff ta $.
	e0_3adantr3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_3adantr3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $= f1_3adantr3 f2_3adantr3 f4_3adantr3 p_3simpa e0_3adantr3 f1_3adantr3 f2_3adantr3 f4_3adantr3 a_w3a f0_3adantr3 f1_3adantr3 f2_3adantr3 a_wa f3_3adantr3 p_sylan2 $.
$}

$(Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_3ad2antl1 $f wff ph $.
	f1_3ad2antl1 $f wff ps $.
	f2_3ad2antl1 $f wff ch $.
	f3_3ad2antl1 $f wff th $.
	f4_3ad2antl1 $f wff ta $.
	e0_3ad2antl1 $e |- ( ( ph /\ ch ) -> th ) $.
	p_3ad2antl1 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $= e0_3ad2antl1 f0_3ad2antl1 f2_3ad2antl1 f3_3ad2antl1 f4_3ad2antl1 p_adantlr f0_3ad2antl1 f4_3ad2antl1 f2_3ad2antl1 f3_3ad2antl1 f1_3ad2antl1 p_3adantl2 $.
$}

$(Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_3ad2antl2 $f wff ph $.
	f1_3ad2antl2 $f wff ps $.
	f2_3ad2antl2 $f wff ch $.
	f3_3ad2antl2 $f wff th $.
	f4_3ad2antl2 $f wff ta $.
	e0_3ad2antl2 $e |- ( ( ph /\ ch ) -> th ) $.
	p_3ad2antl2 $p |- ( ( ( ps /\ ph /\ ta ) /\ ch ) -> th ) $= e0_3ad2antl2 f0_3ad2antl2 f2_3ad2antl2 f3_3ad2antl2 f4_3ad2antl2 p_adantlr f0_3ad2antl2 f4_3ad2antl2 f2_3ad2antl2 f3_3ad2antl2 f1_3ad2antl2 p_3adantl1 $.
$}

$(Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_3ad2antl3 $f wff ph $.
	f1_3ad2antl3 $f wff ps $.
	f2_3ad2antl3 $f wff ch $.
	f3_3ad2antl3 $f wff th $.
	f4_3ad2antl3 $f wff ta $.
	e0_3ad2antl3 $e |- ( ( ph /\ ch ) -> th ) $.
	p_3ad2antl3 $p |- ( ( ( ps /\ ta /\ ph ) /\ ch ) -> th ) $= e0_3ad2antl3 f0_3ad2antl3 f2_3ad2antl3 f3_3ad2antl3 f4_3ad2antl3 p_adantll f4_3ad2antl3 f0_3ad2antl3 f2_3ad2antl3 f3_3ad2antl3 f1_3ad2antl3 p_3adantl1 $.
$}

$(Deduction adding conjuncts to antecedent.  (Contributed by NM,
       25-Dec-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_3ad2antr1 $f wff ph $.
	f1_3ad2antr1 $f wff ps $.
	f2_3ad2antr1 $f wff ch $.
	f3_3ad2antr1 $f wff th $.
	f4_3ad2antr1 $f wff ta $.
	e0_3ad2antr1 $e |- ( ( ph /\ ch ) -> th ) $.
	p_3ad2antr1 $p |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th ) $= e0_3ad2antr1 f0_3ad2antr1 f2_3ad2antr1 f3_3ad2antr1 f1_3ad2antr1 p_adantrr f0_3ad2antr1 f2_3ad2antr1 f1_3ad2antr1 f3_3ad2antr1 f4_3ad2antr1 p_3adantr3 $.
$}

$(Deduction adding conjuncts to antecedent.  (Contributed by NM,
       27-Dec-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_3ad2antr2 $f wff ph $.
	f1_3ad2antr2 $f wff ps $.
	f2_3ad2antr2 $f wff ch $.
	f3_3ad2antr2 $f wff th $.
	f4_3ad2antr2 $f wff ta $.
	e0_3ad2antr2 $e |- ( ( ph /\ ch ) -> th ) $.
	p_3ad2antr2 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $= e0_3ad2antr2 f0_3ad2antr2 f2_3ad2antr2 f3_3ad2antr2 f1_3ad2antr2 p_adantrl f0_3ad2antr2 f1_3ad2antr2 f2_3ad2antr2 f3_3ad2antr2 f4_3ad2antr2 p_3adantr3 $.
$}

$(Deduction adding conjuncts to antecedent.  (Contributed by NM,
       30-Dec-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_3ad2antr3 $f wff ph $.
	f1_3ad2antr3 $f wff ps $.
	f2_3ad2antr3 $f wff ch $.
	f3_3ad2antr3 $f wff th $.
	f4_3ad2antr3 $f wff ta $.
	e0_3ad2antr3 $e |- ( ( ph /\ ch ) -> th ) $.
	p_3ad2antr3 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $= e0_3ad2antr3 f0_3ad2antr3 f2_3ad2antr3 f3_3ad2antr3 f4_3ad2antr3 p_adantrl f0_3ad2antr3 f4_3ad2antr3 f2_3ad2antr3 f3_3ad2antr3 f1_3ad2antr3 p_3adantr1 $.
$}

$(Remove a hypothesis from the second member of a biimplication.
       (Contributed by FL, 22-Jul-2008.) $)

${
	$v ph ps ch th ta  $.
	f0_3anibar $f wff ph $.
	f1_3anibar $f wff ps $.
	f2_3anibar $f wff ch $.
	f3_3anibar $f wff th $.
	f4_3anibar $f wff ta $.
	e0_3anibar $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ( ch /\ ta ) ) ) $.
	p_3anibar $p |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $= e0_3anibar f0_3anibar f1_3anibar f2_3anibar p_simp3 f0_3anibar f1_3anibar f2_3anibar a_w3a f2_3anibar f4_3anibar p_biantrurd f0_3anibar f1_3anibar f2_3anibar a_w3a f3_3anibar f2_3anibar f4_3anibar a_wa f4_3anibar p_bitr4d $.
$}

$(Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)

${
	$v ph ps ch  $.
	f0_3mix1 $f wff ph $.
	f1_3mix1 $f wff ps $.
	f2_3mix1 $f wff ch $.
	p_3mix1 $p |- ( ph -> ( ph \/ ps \/ ch ) ) $= f0_3mix1 f1_3mix1 f2_3mix1 a_wo p_orc f0_3mix1 f1_3mix1 f2_3mix1 p_3orass f0_3mix1 f0_3mix1 f1_3mix1 f2_3mix1 a_wo a_wo f0_3mix1 f1_3mix1 f2_3mix1 a_w3o p_sylibr $.
$}

$(Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)

${
	$v ph ps ch  $.
	f0_3mix2 $f wff ph $.
	f1_3mix2 $f wff ps $.
	f2_3mix2 $f wff ch $.
	p_3mix2 $p |- ( ph -> ( ps \/ ph \/ ch ) ) $= f0_3mix2 f2_3mix2 f1_3mix2 p_3mix1 f1_3mix2 f0_3mix2 f2_3mix2 p_3orrot f0_3mix2 f0_3mix2 f2_3mix2 f1_3mix2 a_w3o f1_3mix2 f0_3mix2 f2_3mix2 a_w3o p_sylibr $.
$}

$(Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)

${
	$v ph ps ch  $.
	f0_3mix3 $f wff ph $.
	f1_3mix3 $f wff ps $.
	f2_3mix3 $f wff ch $.
	p_3mix3 $p |- ( ph -> ( ps \/ ch \/ ph ) ) $= f0_3mix3 f1_3mix3 f2_3mix3 p_3mix1 f0_3mix3 f1_3mix3 f2_3mix3 p_3orrot f0_3mix3 f0_3mix3 f1_3mix3 f2_3mix3 a_w3o f1_3mix3 f2_3mix3 f0_3mix3 a_w3o p_sylib $.
$}

$(Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)

${
	$v ph ps ch  $.
	f0_3mix1i $f wff ph $.
	f1_3mix1i $f wff ps $.
	f2_3mix1i $f wff ch $.
	e0_3mix1i $e |- ph $.
	p_3mix1i $p |- ( ph \/ ps \/ ch ) $= e0_3mix1i f0_3mix1i f1_3mix1i f2_3mix1i p_3mix1 f0_3mix1i f0_3mix1i f1_3mix1i f2_3mix1i a_w3o a_ax-mp $.
$}

$(Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)

${
	$v ph ps ch  $.
	f0_3mix2i $f wff ph $.
	f1_3mix2i $f wff ps $.
	f2_3mix2i $f wff ch $.
	e0_3mix2i $e |- ph $.
	p_3mix2i $p |- ( ps \/ ph \/ ch ) $= e0_3mix2i f0_3mix2i f1_3mix2i f2_3mix2i p_3mix2 f0_3mix2i f1_3mix2i f0_3mix2i f2_3mix2i a_w3o a_ax-mp $.
$}

$(Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)

${
	$v ph ps ch  $.
	f0_3mix3i $f wff ph $.
	f1_3mix3i $f wff ps $.
	f2_3mix3i $f wff ch $.
	e0_3mix3i $e |- ph $.
	p_3mix3i $p |- ( ps \/ ch \/ ph ) $= e0_3mix3i f0_3mix3i f1_3mix3i f2_3mix3i p_3mix3 f0_3mix3i f1_3mix3i f2_3mix3i f0_3mix3i a_w3o a_ax-mp $.
$}

$(Infer conjunction of premises.  (Contributed by NM, 10-Feb-1995.) $)

${
	$v ph ps ch  $.
	f0_3pm3.2i $f wff ph $.
	f1_3pm3.2i $f wff ps $.
	f2_3pm3.2i $f wff ch $.
	e0_3pm3.2i $e |- ph $.
	e1_3pm3.2i $e |- ps $.
	e2_3pm3.2i $e |- ch $.
	p_3pm3.2i $p |- ( ph /\ ps /\ ch ) $= e0_3pm3.2i e1_3pm3.2i f0_3pm3.2i f1_3pm3.2i p_pm3.2i e2_3pm3.2i f0_3pm3.2i f1_3pm3.2i f2_3pm3.2i a_df-3an f0_3pm3.2i f1_3pm3.2i f2_3pm3.2i a_w3a f0_3pm3.2i f1_3pm3.2i a_wa f2_3pm3.2i p_mpbir2an $.
$}

$(~ pm3.2 for a triple conjunction.  (Contributed by Alan Sare,
       24-Oct-2011.) $)

${
	$v ph ps ch  $.
	f0_pm3.2an3 $f wff ph $.
	f1_pm3.2an3 $f wff ps $.
	f2_pm3.2an3 $f wff ch $.
	p_pm3.2an3 $p |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) ) $= f0_pm3.2an3 f1_pm3.2an3 a_wa f2_pm3.2an3 p_pm3.2 f0_pm3.2an3 f1_pm3.2an3 f2_pm3.2an3 f0_pm3.2an3 f1_pm3.2an3 a_wa f2_pm3.2an3 a_wa a_wi p_ex f0_pm3.2an3 f1_pm3.2an3 f2_pm3.2an3 a_df-3an f0_pm3.2an3 f1_pm3.2an3 f2_pm3.2an3 a_w3a f0_pm3.2an3 f1_pm3.2an3 a_wa f2_pm3.2an3 a_wa p_bicomi f0_pm3.2an3 f1_pm3.2an3 f2_pm3.2an3 f0_pm3.2an3 f1_pm3.2an3 a_wa f2_pm3.2an3 a_wa f0_pm3.2an3 f1_pm3.2an3 f2_pm3.2an3 a_w3a p_syl8ib $.
$}

$(Join consequents with conjunction.  (Contributed by NM, 9-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_3jca $f wff ph $.
	f1_3jca $f wff ps $.
	f2_3jca $f wff ch $.
	f3_3jca $f wff th $.
	e0_3jca $e |- ( ph -> ps ) $.
	e1_3jca $e |- ( ph -> ch ) $.
	e2_3jca $e |- ( ph -> th ) $.
	p_3jca $p |- ( ph -> ( ps /\ ch /\ th ) ) $= e0_3jca e1_3jca e2_3jca f0_3jca f1_3jca f2_3jca f3_3jca p_jca31 f1_3jca f2_3jca f3_3jca a_df-3an f0_3jca f1_3jca f2_3jca a_wa f3_3jca a_wa f1_3jca f2_3jca f3_3jca a_w3a p_sylibr $.
$}

$(Deduction conjoining the consequents of three implications.
       (Contributed by NM, 25-Sep-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3jcad $f wff ph $.
	f1_3jcad $f wff ps $.
	f2_3jcad $f wff ch $.
	f3_3jcad $f wff th $.
	f4_3jcad $f wff ta $.
	e0_3jcad $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3jcad $e |- ( ph -> ( ps -> th ) ) $.
	e2_3jcad $e |- ( ph -> ( ps -> ta ) ) $.
	p_3jcad $p |- ( ph -> ( ps -> ( ch /\ th /\ ta ) ) ) $= e0_3jcad f0_3jcad f1_3jcad f2_3jcad p_imp e1_3jcad f0_3jcad f1_3jcad f3_3jcad p_imp e2_3jcad f0_3jcad f1_3jcad f4_3jcad p_imp f0_3jcad f1_3jcad a_wa f2_3jcad f3_3jcad f4_3jcad p_3jca f0_3jcad f1_3jcad f2_3jcad f3_3jcad f4_3jcad a_w3a p_ex $.
$}

$(Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       16-Sep-2011.) $)

${
	$v ph ps ch th  $.
	f0_mpbir3an $f wff ph $.
	f1_mpbir3an $f wff ps $.
	f2_mpbir3an $f wff ch $.
	f3_mpbir3an $f wff th $.
	e0_mpbir3an $e |- ps $.
	e1_mpbir3an $e |- ch $.
	e2_mpbir3an $e |- th $.
	e3_mpbir3an $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
	p_mpbir3an $p |- ph $= e0_mpbir3an e1_mpbir3an e2_mpbir3an f1_mpbir3an f2_mpbir3an f3_mpbir3an p_3pm3.2i e3_mpbir3an f0_mpbir3an f1_mpbir3an f2_mpbir3an f3_mpbir3an a_w3a p_mpbir $.
$}

$(Detach a conjunction of truths in a biconditional.  (Contributed by
       Mario Carneiro, 11-May-2014.)  (Revised by Mario Carneiro,
       9-Jan-2015.) $)

${
	$v ph ps ch th ta  $.
	f0_mpbir3and $f wff ph $.
	f1_mpbir3and $f wff ps $.
	f2_mpbir3and $f wff ch $.
	f3_mpbir3and $f wff th $.
	f4_mpbir3and $f wff ta $.
	e0_mpbir3and $e |- ( ph -> ch ) $.
	e1_mpbir3and $e |- ( ph -> th ) $.
	e2_mpbir3and $e |- ( ph -> ta ) $.
	e3_mpbir3and $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
	p_mpbir3and $p |- ( ph -> ps ) $= e0_mpbir3and e1_mpbir3and e2_mpbir3and f0_mpbir3and f2_mpbir3and f3_mpbir3and f4_mpbir3and p_3jca e3_mpbir3and f0_mpbir3and f1_mpbir3and f2_mpbir3and f3_mpbir3and f4_mpbir3and a_w3a p_mpbird $.
$}

$(Syllogism inference.  (Contributed by Mario Carneiro, 11-May-2014.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3anbrc $f wff ph $.
	f1_syl3anbrc $f wff ps $.
	f2_syl3anbrc $f wff ch $.
	f3_syl3anbrc $f wff th $.
	f4_syl3anbrc $f wff ta $.
	e0_syl3anbrc $e |- ( ph -> ps ) $.
	e1_syl3anbrc $e |- ( ph -> ch ) $.
	e2_syl3anbrc $e |- ( ph -> th ) $.
	e3_syl3anbrc $e |- ( ta <-> ( ps /\ ch /\ th ) ) $.
	p_syl3anbrc $p |- ( ph -> ta ) $= e0_syl3anbrc e1_syl3anbrc e2_syl3anbrc f0_syl3anbrc f1_syl3anbrc f2_syl3anbrc f3_syl3anbrc p_3jca e3_syl3anbrc f0_syl3anbrc f1_syl3anbrc f2_syl3anbrc f3_syl3anbrc a_w3a f4_syl3anbrc p_sylibr $.
$}

$(Join antecedents and consequents with conjunction.  (Contributed by NM,
       8-Apr-1994.) $)

${
	$v ph ps ch th ta et  $.
	f0_3anim123i $f wff ph $.
	f1_3anim123i $f wff ps $.
	f2_3anim123i $f wff ch $.
	f3_3anim123i $f wff th $.
	f4_3anim123i $f wff ta $.
	f5_3anim123i $f wff et $.
	e0_3anim123i $e |- ( ph -> ps ) $.
	e1_3anim123i $e |- ( ch -> th ) $.
	e2_3anim123i $e |- ( ta -> et ) $.
	p_3anim123i $p |- ( ( ph /\ ch /\ ta ) -> ( ps /\ th /\ et ) ) $= e0_3anim123i f0_3anim123i f2_3anim123i f1_3anim123i f4_3anim123i p_3ad2ant1 e1_3anim123i f2_3anim123i f0_3anim123i f3_3anim123i f4_3anim123i p_3ad2ant2 e2_3anim123i f4_3anim123i f0_3anim123i f5_3anim123i f2_3anim123i p_3ad2ant3 f0_3anim123i f2_3anim123i f4_3anim123i a_w3a f1_3anim123i f3_3anim123i f5_3anim123i p_3jca $.
$}

$(Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 16-Aug-2009.) $)

${
	$v ph ps ch th  $.
	f0_3anim1i $f wff ph $.
	f1_3anim1i $f wff ps $.
	f2_3anim1i $f wff ch $.
	f3_3anim1i $f wff th $.
	e0_3anim1i $e |- ( ph -> ps ) $.
	p_3anim1i $p |- ( ( ph /\ ch /\ th ) -> ( ps /\ ch /\ th ) ) $= e0_3anim1i f2_3anim1i p_id f3_3anim1i p_id f0_3anim1i f1_3anim1i f2_3anim1i f2_3anim1i f3_3anim1i f3_3anim1i p_3anim123i $.
$}

$(Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 19-Aug-2009.) $)

${
	$v ph ps ch th  $.
	f0_3anim3i $f wff ph $.
	f1_3anim3i $f wff ps $.
	f2_3anim3i $f wff ch $.
	f3_3anim3i $f wff th $.
	e0_3anim3i $e |- ( ph -> ps ) $.
	p_3anim3i $p |- ( ( ch /\ th /\ ph ) -> ( ch /\ th /\ ps ) ) $= f2_3anim3i p_id f3_3anim3i p_id e0_3anim3i f2_3anim3i f2_3anim3i f3_3anim3i f3_3anim3i f0_3anim3i f1_3anim3i p_3anim123i $.
$}

$(Join 3 biconditionals with conjunction.  (Contributed by NM,
       21-Apr-1994.) $)

${
	$v ph ps ch th ta et  $.
	f0_3anbi123i $f wff ph $.
	f1_3anbi123i $f wff ps $.
	f2_3anbi123i $f wff ch $.
	f3_3anbi123i $f wff th $.
	f4_3anbi123i $f wff ta $.
	f5_3anbi123i $f wff et $.
	e0_3anbi123i $e |- ( ph <-> ps ) $.
	e1_3anbi123i $e |- ( ch <-> th ) $.
	e2_3anbi123i $e |- ( ta <-> et ) $.
	p_3anbi123i $p |- ( ( ph /\ ch /\ ta ) <-> ( ps /\ th /\ et ) ) $= e0_3anbi123i e1_3anbi123i f0_3anbi123i f1_3anbi123i f2_3anbi123i f3_3anbi123i p_anbi12i e2_3anbi123i f0_3anbi123i f2_3anbi123i a_wa f1_3anbi123i f3_3anbi123i a_wa f4_3anbi123i f5_3anbi123i p_anbi12i f0_3anbi123i f2_3anbi123i f4_3anbi123i a_df-3an f1_3anbi123i f3_3anbi123i f5_3anbi123i a_df-3an f0_3anbi123i f2_3anbi123i a_wa f4_3anbi123i a_wa f1_3anbi123i f3_3anbi123i a_wa f5_3anbi123i a_wa f0_3anbi123i f2_3anbi123i f4_3anbi123i a_w3a f1_3anbi123i f3_3anbi123i f5_3anbi123i a_w3a p_3bitr4i $.
$}

$(Join 3 biconditionals with disjunction.  (Contributed by NM,
       17-May-1994.) $)

${
	$v ph ps ch th ta et  $.
	f0_3orbi123i $f wff ph $.
	f1_3orbi123i $f wff ps $.
	f2_3orbi123i $f wff ch $.
	f3_3orbi123i $f wff th $.
	f4_3orbi123i $f wff ta $.
	f5_3orbi123i $f wff et $.
	e0_3orbi123i $e |- ( ph <-> ps ) $.
	e1_3orbi123i $e |- ( ch <-> th ) $.
	e2_3orbi123i $e |- ( ta <-> et ) $.
	p_3orbi123i $p |- ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) $= e0_3orbi123i e1_3orbi123i f0_3orbi123i f1_3orbi123i f2_3orbi123i f3_3orbi123i p_orbi12i e2_3orbi123i f0_3orbi123i f2_3orbi123i a_wo f1_3orbi123i f3_3orbi123i a_wo f4_3orbi123i f5_3orbi123i p_orbi12i f0_3orbi123i f2_3orbi123i f4_3orbi123i a_df-3or f1_3orbi123i f3_3orbi123i f5_3orbi123i a_df-3or f0_3orbi123i f2_3orbi123i a_wo f4_3orbi123i a_wo f1_3orbi123i f3_3orbi123i a_wo f5_3orbi123i a_wo f0_3orbi123i f2_3orbi123i f4_3orbi123i a_w3o f1_3orbi123i f3_3orbi123i f5_3orbi123i a_w3o p_3bitr4i $.
$}

$(Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)

${
	$v ph ps ch th  $.
	f0_3anbi1i $f wff ph $.
	f1_3anbi1i $f wff ps $.
	f2_3anbi1i $f wff ch $.
	f3_3anbi1i $f wff th $.
	e0_3anbi1i $e |- ( ph <-> ps ) $.
	p_3anbi1i $p |- ( ( ph /\ ch /\ th ) <-> ( ps /\ ch /\ th ) ) $= e0_3anbi1i f2_3anbi1i p_biid f3_3anbi1i p_biid f0_3anbi1i f1_3anbi1i f2_3anbi1i f2_3anbi1i f3_3anbi1i f3_3anbi1i p_3anbi123i $.
$}

$(Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)

${
	$v ph ps ch th  $.
	f0_3anbi2i $f wff ph $.
	f1_3anbi2i $f wff ps $.
	f2_3anbi2i $f wff ch $.
	f3_3anbi2i $f wff th $.
	e0_3anbi2i $e |- ( ph <-> ps ) $.
	p_3anbi2i $p |- ( ( ch /\ ph /\ th ) <-> ( ch /\ ps /\ th ) ) $= f2_3anbi2i p_biid e0_3anbi2i f3_3anbi2i p_biid f2_3anbi2i f2_3anbi2i f0_3anbi2i f1_3anbi2i f3_3anbi2i f3_3anbi2i p_3anbi123i $.
$}

$(Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)

${
	$v ph ps ch th  $.
	f0_3anbi3i $f wff ph $.
	f1_3anbi3i $f wff ps $.
	f2_3anbi3i $f wff ch $.
	f3_3anbi3i $f wff th $.
	e0_3anbi3i $e |- ( ph <-> ps ) $.
	p_3anbi3i $p |- ( ( ch /\ th /\ ph ) <-> ( ch /\ th /\ ps ) ) $= f2_3anbi3i p_biid f3_3anbi3i p_biid e0_3anbi3i f2_3anbi3i f2_3anbi3i f3_3anbi3i f3_3anbi3i f0_3anbi3i f1_3anbi3i p_3anbi123i $.
$}

$(Importation inference.  (Contributed by NM, 8-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_3imp $f wff ph $.
	f1_3imp $f wff ps $.
	f2_3imp $f wff ch $.
	f3_3imp $f wff th $.
	e0_3imp $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_3imp $p |- ( ( ph /\ ps /\ ch ) -> th ) $= f0_3imp f1_3imp f2_3imp a_df-3an e0_3imp f0_3imp f1_3imp f2_3imp f3_3imp p_imp31 f0_3imp f1_3imp f2_3imp a_w3a f0_3imp f1_3imp a_wa f2_3imp a_wa f3_3imp p_sylbi $.
$}

$(Importation from double to triple conjunction.  (Contributed by NM,
       20-Aug-1995.) $)

${
	$v ph ps ch th  $.
	f0_3impa $f wff ph $.
	f1_3impa $f wff ps $.
	f2_3impa $f wff ch $.
	f3_3impa $f wff th $.
	e0_3impa $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_3impa $p |- ( ( ph /\ ps /\ ch ) -> th ) $= e0_3impa f0_3impa f1_3impa f2_3impa f3_3impa p_exp31 f0_3impa f1_3impa f2_3impa f3_3impa p_3imp $.
$}

$(Importation from double to triple conjunction.  (Contributed by NM,
       20-Aug-1995.) $)

${
	$v ph ps ch th  $.
	f0_3impb $f wff ph $.
	f1_3impb $f wff ps $.
	f2_3impb $f wff ch $.
	f3_3impb $f wff th $.
	e0_3impb $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_3impb $p |- ( ( ph /\ ps /\ ch ) -> th ) $= e0_3impb f0_3impb f1_3impb f2_3impb f3_3impb p_exp32 f0_3impb f1_3impb f2_3impb f3_3impb p_3imp $.
$}

$(Importation to triple conjunction.  (Contributed by NM, 13-Jun-2006.) $)

${
	$v ph ps ch th  $.
	f0_3impia $f wff ph $.
	f1_3impia $f wff ps $.
	f2_3impia $f wff ch $.
	f3_3impia $f wff th $.
	e0_3impia $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	p_3impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $= e0_3impia f0_3impia f1_3impia f2_3impia f3_3impia a_wi p_ex f0_3impia f1_3impia f2_3impia f3_3impia p_3imp $.
$}

$(Importation to triple conjunction.  (Contributed by NM, 13-Jun-2006.) $)

${
	$v ph ps ch th  $.
	f0_3impib $f wff ph $.
	f1_3impib $f wff ps $.
	f2_3impib $f wff ch $.
	f3_3impib $f wff th $.
	e0_3impib $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_3impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $= e0_3impib f0_3impib f1_3impib f2_3impib f3_3impib p_exp3a f0_3impib f1_3impib f2_3impib f3_3impib p_3imp $.
$}

$(Exportation inference.  (Contributed by NM, 30-May-1994.) $)

${
	$v ph ps ch th  $.
	f0_3exp $f wff ph $.
	f1_3exp $f wff ps $.
	f2_3exp $f wff ch $.
	f3_3exp $f wff th $.
	e0_3exp $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3exp $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= f0_3exp f1_3exp f2_3exp p_pm3.2an3 e0_3exp f0_3exp f1_3exp f2_3exp f0_3exp f1_3exp f2_3exp a_w3a f3_3exp p_syl8 $.
$}

$(Exportation from triple to double conjunction.  (Contributed by NM,
       20-Aug-1995.) $)

${
	$v ph ps ch th  $.
	f0_3expa $f wff ph $.
	f1_3expa $f wff ps $.
	f2_3expa $f wff ch $.
	f3_3expa $f wff th $.
	e0_3expa $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3expa $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $= e0_3expa f0_3expa f1_3expa f2_3expa f3_3expa p_3exp f0_3expa f1_3expa f2_3expa f3_3expa p_imp31 $.
$}

$(Exportation from triple to double conjunction.  (Contributed by NM,
       20-Aug-1995.) $)

${
	$v ph ps ch th  $.
	f0_3expb $f wff ph $.
	f1_3expb $f wff ps $.
	f2_3expb $f wff ch $.
	f3_3expb $f wff th $.
	e0_3expb $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3expb $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $= e0_3expb f0_3expb f1_3expb f2_3expb f3_3expb p_3exp f0_3expb f1_3expb f2_3expb f3_3expb p_imp32 $.
$}

$(Exportation from triple conjunction.  (Contributed by NM,
       19-May-2007.) $)

${
	$v ph ps ch th  $.
	f0_3expia $f wff ph $.
	f1_3expia $f wff ps $.
	f2_3expia $f wff ch $.
	f3_3expia $f wff th $.
	e0_3expia $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3expia $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $= e0_3expia f0_3expia f1_3expia f2_3expia f3_3expia p_3exp f0_3expia f1_3expia f2_3expia f3_3expia a_wi p_imp $.
$}

$(Exportation from triple conjunction.  (Contributed by NM,
       19-May-2007.) $)

${
	$v ph ps ch th  $.
	f0_3expib $f wff ph $.
	f1_3expib $f wff ps $.
	f2_3expib $f wff ch $.
	f3_3expib $f wff th $.
	e0_3expib $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3expib $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= e0_3expib f0_3expib f1_3expib f2_3expib f3_3expib p_3exp f0_3expib f1_3expib f2_3expib f3_3expib p_imp3a $.
$}

$(Commutation in antecedent.  Swap 1st and 3rd.  (Contributed by NM,
       28-Jan-1996.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v ph ps ch th  $.
	f0_3com12 $f wff ph $.
	f1_3com12 $f wff ps $.
	f2_3com12 $f wff ch $.
	f3_3com12 $f wff th $.
	e0_3com12 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3com12 $p |- ( ( ps /\ ph /\ ch ) -> th ) $= f1_3com12 f0_3com12 f2_3com12 p_3ancoma e0_3com12 f1_3com12 f0_3com12 f2_3com12 a_w3a f0_3com12 f1_3com12 f2_3com12 a_w3a f3_3com12 p_sylbi $.
$}

$(Commutation in antecedent.  Swap 1st and 3rd.  (Contributed by NM,
       28-Jan-1996.) $)

${
	$v ph ps ch th  $.
	f0_3com13 $f wff ph $.
	f1_3com13 $f wff ps $.
	f2_3com13 $f wff ch $.
	f3_3com13 $f wff th $.
	e0_3com13 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3com13 $p |- ( ( ch /\ ps /\ ph ) -> th ) $= f2_3com13 f1_3com13 f0_3com13 p_3anrev e0_3com13 f2_3com13 f1_3com13 f0_3com13 a_w3a f0_3com13 f1_3com13 f2_3com13 a_w3a f3_3com13 p_sylbi $.
$}

$(Commutation in antecedent.  Swap 2nd and 3rd.  (Contributed by NM,
       28-Jan-1996.) $)

${
	$v ph ps ch th  $.
	f0_3com23 $f wff ph $.
	f1_3com23 $f wff ps $.
	f2_3com23 $f wff ch $.
	f3_3com23 $f wff th $.
	e0_3com23 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3com23 $p |- ( ( ph /\ ch /\ ps ) -> th ) $= e0_3com23 f0_3com23 f1_3com23 f2_3com23 f3_3com23 p_3exp f0_3com23 f1_3com23 f2_3com23 f3_3com23 p_com23 f0_3com23 f2_3com23 f1_3com23 f3_3com23 p_3imp $.
$}

$(Commutation in antecedent.  Rotate left.  (Contributed by NM,
       28-Jan-1996.) $)

${
	$v ph ps ch th  $.
	f0_3coml $f wff ph $.
	f1_3coml $f wff ps $.
	f2_3coml $f wff ch $.
	f3_3coml $f wff th $.
	e0_3coml $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3coml $p |- ( ( ps /\ ch /\ ph ) -> th ) $= e0_3coml f0_3coml f1_3coml f2_3coml f3_3coml p_3com23 f0_3coml f2_3coml f1_3coml f3_3coml p_3com13 $.
$}

$(Commutation in antecedent.  Rotate right.  (Contributed by NM,
       28-Jan-1996.) $)

${
	$v ph ps ch th  $.
	f0_3comr $f wff ph $.
	f1_3comr $f wff ps $.
	f2_3comr $f wff ch $.
	f3_3comr $f wff th $.
	e0_3comr $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3comr $p |- ( ( ch /\ ph /\ ps ) -> th ) $= e0_3comr f0_3comr f1_3comr f2_3comr f3_3comr p_3coml f1_3comr f2_3comr f0_3comr f3_3comr p_3coml $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Feb-2008.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant3r1 $f wff ph $.
	f1_3adant3r1 $f wff ps $.
	f2_3adant3r1 $f wff ch $.
	f3_3adant3r1 $f wff th $.
	f4_3adant3r1 $f wff ta $.
	e0_3adant3r1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant3r1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $= e0_3adant3r1 f0_3adant3r1 f1_3adant3r1 f2_3adant3r1 f3_3adant3r1 p_3expb f0_3adant3r1 f1_3adant3r1 f2_3adant3r1 f3_3adant3r1 f4_3adant3r1 p_3adantr1 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       17-Feb-2008.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant3r2 $f wff ph $.
	f1_3adant3r2 $f wff ps $.
	f2_3adant3r2 $f wff ch $.
	f3_3adant3r2 $f wff th $.
	f4_3adant3r2 $f wff ta $.
	e0_3adant3r2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant3r2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $= e0_3adant3r2 f0_3adant3r2 f1_3adant3r2 f2_3adant3r2 f3_3adant3r2 p_3expb f0_3adant3r2 f1_3adant3r2 f2_3adant3r2 f3_3adant3r2 f4_3adant3r2 p_3adantr2 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       18-Feb-2008.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant3r3 $f wff ph $.
	f1_3adant3r3 $f wff ps $.
	f2_3adant3r3 $f wff ch $.
	f3_3adant3r3 $f wff th $.
	f4_3adant3r3 $f wff ta $.
	e0_3adant3r3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant3r3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $= e0_3adant3r3 f0_3adant3r3 f1_3adant3r3 f2_3adant3r3 f3_3adant3r3 p_3expb f0_3adant3r3 f1_3adant3r3 f2_3adant3r3 f3_3adant3r3 f4_3adant3r3 p_3adantr3 $.
$}

$(Swap conjuncts.  (Contributed by NM, 16-Dec-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_3an1rs $f wff ph $.
	f1_3an1rs $f wff ps $.
	f2_3an1rs $f wff ch $.
	f3_3an1rs $f wff th $.
	f4_3an1rs $f wff ta $.
	e0_3an1rs $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	p_3an1rs $p |- ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta ) $= e0_3an1rs f0_3an1rs f1_3an1rs f2_3an1rs a_w3a f3_3an1rs f4_3an1rs p_ex f0_3an1rs f1_3an1rs f2_3an1rs f3_3an1rs f4_3an1rs a_wi p_3exp f0_3an1rs f1_3an1rs f2_3an1rs f3_3an1rs f4_3an1rs p_com34 f0_3an1rs f1_3an1rs f3_3an1rs f2_3an1rs f4_3an1rs a_wi p_3imp f0_3an1rs f1_3an1rs f3_3an1rs a_w3a f2_3an1rs f4_3an1rs p_imp $.
$}

$(Importation to left triple conjunction.  (Contributed by NM,
       24-Feb-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3imp1 $f wff ph $.
	f1_3imp1 $f wff ps $.
	f2_3imp1 $f wff ch $.
	f3_3imp1 $f wff th $.
	f4_3imp1 $f wff ta $.
	e0_3imp1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_3imp1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $= e0_3imp1 f0_3imp1 f1_3imp1 f2_3imp1 f3_3imp1 f4_3imp1 a_wi p_3imp f0_3imp1 f1_3imp1 f2_3imp1 a_w3a f3_3imp1 f4_3imp1 p_imp $.
$}

$(Importation deduction for triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3impd $f wff ph $.
	f1_3impd $f wff ps $.
	f2_3impd $f wff ch $.
	f3_3impd $f wff th $.
	f4_3impd $f wff ta $.
	e0_3impd $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_3impd $p |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $= e0_3impd f0_3impd f1_3impd f2_3impd f3_3impd f4_3impd p_com4l f1_3impd f2_3impd f3_3impd f0_3impd f4_3impd a_wi p_3imp f1_3impd f2_3impd f3_3impd a_w3a f0_3impd f4_3impd p_com12 $.
$}

$(Importation to right triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3imp2 $f wff ph $.
	f1_3imp2 $f wff ps $.
	f2_3imp2 $f wff ch $.
	f3_3imp2 $f wff th $.
	f4_3imp2 $f wff ta $.
	e0_3imp2 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_3imp2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $= e0_3imp2 f0_3imp2 f1_3imp2 f2_3imp2 f3_3imp2 f4_3imp2 p_3impd f0_3imp2 f1_3imp2 f2_3imp2 f3_3imp2 a_w3a f4_3imp2 p_imp $.
$}

$(Exportation from left triple conjunction.  (Contributed by NM,
       24-Feb-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3exp1 $f wff ph $.
	f1_3exp1 $f wff ps $.
	f2_3exp1 $f wff ch $.
	f3_3exp1 $f wff th $.
	f4_3exp1 $f wff ta $.
	e0_3exp1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	p_3exp1 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_3exp1 f0_3exp1 f1_3exp1 f2_3exp1 a_w3a f3_3exp1 f4_3exp1 p_ex f0_3exp1 f1_3exp1 f2_3exp1 f3_3exp1 f4_3exp1 a_wi p_3exp $.
$}

$(Exportation deduction for triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3expd $f wff ph $.
	f1_3expd $f wff ps $.
	f2_3expd $f wff ch $.
	f3_3expd $f wff th $.
	f4_3expd $f wff ta $.
	e0_3expd $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
	p_3expd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_3expd f0_3expd f1_3expd f2_3expd f3_3expd a_w3a f4_3expd p_com12 f1_3expd f2_3expd f3_3expd f0_3expd f4_3expd a_wi p_3exp f1_3expd f2_3expd f3_3expd f0_3expd f4_3expd p_com4r $.
$}

$(Exportation from right triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3exp2 $f wff ph $.
	f1_3exp2 $f wff ps $.
	f2_3exp2 $f wff ch $.
	f3_3exp2 $f wff th $.
	f4_3exp2 $f wff ta $.
	e0_3exp2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	p_3exp2 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_3exp2 f0_3exp2 f1_3exp2 f2_3exp2 f3_3exp2 a_w3a f4_3exp2 p_ex f0_3exp2 f1_3exp2 f2_3exp2 f3_3exp2 f4_3exp2 p_3expd $.
$}

$(A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_exp5o $f wff ph $.
	f1_exp5o $f wff ps $.
	f2_exp5o $f wff ch $.
	f3_exp5o $f wff th $.
	f4_exp5o $f wff ta $.
	f5_exp5o $f wff et $.
	e0_exp5o $e |- ( ( ph /\ ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) $.
	p_exp5o $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= e0_exp5o f0_exp5o f1_exp5o f2_exp5o a_w3a f3_exp5o f4_exp5o f5_exp5o p_exp3a f0_exp5o f1_exp5o f2_exp5o f3_exp5o f4_exp5o f5_exp5o a_wi a_wi p_3exp $.
$}

$(A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_exp516 $f wff ph $.
	f1_exp516 $f wff ps $.
	f2_exp516 $f wff ch $.
	f3_exp516 $f wff th $.
	f4_exp516 $f wff ta $.
	f5_exp516 $f wff et $.
	e0_exp516 $e |- ( ( ( ph /\ ( ps /\ ch /\ th ) ) /\ ta ) -> et ) $.
	p_exp516 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= e0_exp516 f0_exp516 f1_exp516 f2_exp516 f3_exp516 a_w3a f4_exp516 f5_exp516 p_exp31 f0_exp516 f1_exp516 f2_exp516 f3_exp516 f4_exp516 f5_exp516 a_wi p_3expd $.
$}

$(A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_exp520 $f wff ph $.
	f1_exp520 $f wff ps $.
	f2_exp520 $f wff ch $.
	f3_exp520 $f wff th $.
	f4_exp520 $f wff ta $.
	f5_exp520 $f wff et $.
	e0_exp520 $e |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
	p_exp520 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= e0_exp520 f0_exp520 f1_exp520 f2_exp520 a_w3a f3_exp520 f4_exp520 a_wa f5_exp520 p_ex f0_exp520 f1_exp520 f2_exp520 f3_exp520 f4_exp520 f5_exp520 p_exp5o $.
$}

$(Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch th ta  $.
	f0_3anassrs $f wff ph $.
	f1_3anassrs $f wff ps $.
	f2_3anassrs $f wff ch $.
	f3_3anassrs $f wff th $.
	f4_3anassrs $f wff ta $.
	e0_3anassrs $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	p_3anassrs $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $= e0_3anassrs f0_3anassrs f1_3anassrs f2_3anassrs f3_3anassrs f4_3anassrs p_3exp2 f0_3anassrs f1_3anassrs f2_3anassrs f3_3anassrs f4_3anassrs p_imp41 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant1l $f wff ph $.
	f1_3adant1l $f wff ps $.
	f2_3adant1l $f wff ch $.
	f3_3adant1l $f wff th $.
	f4_3adant1l $f wff ta $.
	e0_3adant1l $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant1l $p |- ( ( ( ta /\ ph ) /\ ps /\ ch ) -> th ) $= e0_3adant1l f0_3adant1l f1_3adant1l f2_3adant1l f3_3adant1l p_3expb f0_3adant1l f1_3adant1l f2_3adant1l a_wa f3_3adant1l f4_3adant1l p_adantll f4_3adant1l f0_3adant1l a_wa f1_3adant1l f2_3adant1l f3_3adant1l p_3impb $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant1r $f wff ph $.
	f1_3adant1r $f wff ps $.
	f2_3adant1r $f wff ch $.
	f3_3adant1r $f wff th $.
	f4_3adant1r $f wff ta $.
	e0_3adant1r $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant1r $p |- ( ( ( ph /\ ta ) /\ ps /\ ch ) -> th ) $= e0_3adant1r f0_3adant1r f1_3adant1r f2_3adant1r f3_3adant1r p_3expb f0_3adant1r f1_3adant1r f2_3adant1r a_wa f3_3adant1r f4_3adant1r p_adantlr f0_3adant1r f4_3adant1r a_wa f1_3adant1r f2_3adant1r f3_3adant1r p_3impb $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant2l $f wff ph $.
	f1_3adant2l $f wff ps $.
	f2_3adant2l $f wff ch $.
	f3_3adant2l $f wff th $.
	f4_3adant2l $f wff ta $.
	e0_3adant2l $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant2l $p |- ( ( ph /\ ( ta /\ ps ) /\ ch ) -> th ) $= e0_3adant2l f0_3adant2l f1_3adant2l f2_3adant2l f3_3adant2l p_3com12 f1_3adant2l f0_3adant2l f2_3adant2l f3_3adant2l f4_3adant2l p_3adant1l f4_3adant2l f1_3adant2l a_wa f0_3adant2l f2_3adant2l f3_3adant2l p_3com12 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant2r $f wff ph $.
	f1_3adant2r $f wff ps $.
	f2_3adant2r $f wff ch $.
	f3_3adant2r $f wff th $.
	f4_3adant2r $f wff ta $.
	e0_3adant2r $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant2r $p |- ( ( ph /\ ( ps /\ ta ) /\ ch ) -> th ) $= e0_3adant2r f0_3adant2r f1_3adant2r f2_3adant2r f3_3adant2r p_3com12 f1_3adant2r f0_3adant2r f2_3adant2r f3_3adant2r f4_3adant2r p_3adant1r f1_3adant2r f4_3adant2r a_wa f0_3adant2r f2_3adant2r f3_3adant2r p_3com12 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant3l $f wff ph $.
	f1_3adant3l $f wff ps $.
	f2_3adant3l $f wff ch $.
	f3_3adant3l $f wff th $.
	f4_3adant3l $f wff ta $.
	e0_3adant3l $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant3l $p |- ( ( ph /\ ps /\ ( ta /\ ch ) ) -> th ) $= e0_3adant3l f0_3adant3l f1_3adant3l f2_3adant3l f3_3adant3l p_3com13 f2_3adant3l f1_3adant3l f0_3adant3l f3_3adant3l f4_3adant3l p_3adant1l f4_3adant3l f2_3adant3l a_wa f1_3adant3l f0_3adant3l f3_3adant3l p_3com13 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3adant3r $f wff ph $.
	f1_3adant3r $f wff ps $.
	f2_3adant3r $f wff ch $.
	f3_3adant3r $f wff th $.
	f4_3adant3r $f wff ta $.
	e0_3adant3r $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3adant3r $p |- ( ( ph /\ ps /\ ( ch /\ ta ) ) -> th ) $= e0_3adant3r f0_3adant3r f1_3adant3r f2_3adant3r f3_3adant3r p_3com13 f2_3adant3r f1_3adant3r f0_3adant3r f3_3adant3r f4_3adant3r p_3adant1r f2_3adant3r f4_3adant3r a_wa f1_3adant3r f0_3adant3r f3_3adant3r p_3com13 $.
$}

$(Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)

${
	$v ph ps ch th ta  $.
	f0_syl12anc $f wff ph $.
	f1_syl12anc $f wff ps $.
	f2_syl12anc $f wff ch $.
	f3_syl12anc $f wff th $.
	f4_syl12anc $f wff ta $.
	e0_syl12anc $e |- ( ph -> ps ) $.
	e1_syl12anc $e |- ( ph -> ch ) $.
	e2_syl12anc $e |- ( ph -> th ) $.
	e3_syl12anc $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
	p_syl12anc $p |- ( ph -> ta ) $= e0_syl12anc e1_syl12anc e2_syl12anc f0_syl12anc f1_syl12anc f2_syl12anc f3_syl12anc p_jca32 e3_syl12anc f0_syl12anc f1_syl12anc f2_syl12anc f3_syl12anc a_wa a_wa f4_syl12anc p_syl $.
$}

$(Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)

${
	$v ph ps ch th ta  $.
	f0_syl21anc $f wff ph $.
	f1_syl21anc $f wff ps $.
	f2_syl21anc $f wff ch $.
	f3_syl21anc $f wff th $.
	f4_syl21anc $f wff ta $.
	e0_syl21anc $e |- ( ph -> ps ) $.
	e1_syl21anc $e |- ( ph -> ch ) $.
	e2_syl21anc $e |- ( ph -> th ) $.
	e3_syl21anc $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
	p_syl21anc $p |- ( ph -> ta ) $= e0_syl21anc e1_syl21anc e2_syl21anc f0_syl21anc f1_syl21anc f2_syl21anc f3_syl21anc p_jca31 e3_syl21anc f0_syl21anc f1_syl21anc f2_syl21anc a_wa f3_syl21anc a_wa f4_syl21anc p_syl $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3anc $f wff ph $.
	f1_syl3anc $f wff ps $.
	f2_syl3anc $f wff ch $.
	f3_syl3anc $f wff th $.
	f4_syl3anc $f wff ta $.
	e0_syl3anc $e |- ( ph -> ps ) $.
	e1_syl3anc $e |- ( ph -> ch ) $.
	e2_syl3anc $e |- ( ph -> th ) $.
	e3_syl3anc $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3anc $p |- ( ph -> ta ) $= e0_syl3anc e1_syl3anc e2_syl3anc f0_syl3anc f1_syl3anc f2_syl3anc f3_syl3anc p_3jca e3_syl3anc f0_syl3anc f1_syl3anc f2_syl3anc f3_syl3anc a_w3a f4_syl3anc p_syl $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl22anc $f wff ph $.
	f1_syl22anc $f wff ps $.
	f2_syl22anc $f wff ch $.
	f3_syl22anc $f wff th $.
	f4_syl22anc $f wff ta $.
	f5_syl22anc $f wff et $.
	e0_syl22anc $e |- ( ph -> ps ) $.
	e1_syl22anc $e |- ( ph -> ch ) $.
	e2_syl22anc $e |- ( ph -> th ) $.
	e3_syl22anc $e |- ( ph -> ta ) $.
	e4_syl22anc $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
	p_syl22anc $p |- ( ph -> et ) $= e0_syl22anc e1_syl22anc f0_syl22anc f1_syl22anc f2_syl22anc p_jca e2_syl22anc e3_syl22anc e4_syl22anc f0_syl22anc f1_syl22anc f2_syl22anc a_wa f3_syl22anc f4_syl22anc f5_syl22anc p_syl12anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl13anc $f wff ph $.
	f1_syl13anc $f wff ps $.
	f2_syl13anc $f wff ch $.
	f3_syl13anc $f wff th $.
	f4_syl13anc $f wff ta $.
	f5_syl13anc $f wff et $.
	e0_syl13anc $e |- ( ph -> ps ) $.
	e1_syl13anc $e |- ( ph -> ch ) $.
	e2_syl13anc $e |- ( ph -> th ) $.
	e3_syl13anc $e |- ( ph -> ta ) $.
	e4_syl13anc $e |- ( ( ps /\ ( ch /\ th /\ ta ) ) -> et ) $.
	p_syl13anc $p |- ( ph -> et ) $= e0_syl13anc e1_syl13anc e2_syl13anc e3_syl13anc f0_syl13anc f2_syl13anc f3_syl13anc f4_syl13anc p_3jca e4_syl13anc f0_syl13anc f1_syl13anc f2_syl13anc f3_syl13anc f4_syl13anc a_w3a f5_syl13anc p_syl2anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl31anc $f wff ph $.
	f1_syl31anc $f wff ps $.
	f2_syl31anc $f wff ch $.
	f3_syl31anc $f wff th $.
	f4_syl31anc $f wff ta $.
	f5_syl31anc $f wff et $.
	e0_syl31anc $e |- ( ph -> ps ) $.
	e1_syl31anc $e |- ( ph -> ch ) $.
	e2_syl31anc $e |- ( ph -> th ) $.
	e3_syl31anc $e |- ( ph -> ta ) $.
	e4_syl31anc $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
	p_syl31anc $p |- ( ph -> et ) $= e0_syl31anc e1_syl31anc e2_syl31anc f0_syl31anc f1_syl31anc f2_syl31anc f3_syl31anc p_3jca e3_syl31anc e4_syl31anc f0_syl31anc f1_syl31anc f2_syl31anc f3_syl31anc a_w3a f4_syl31anc f5_syl31anc p_syl2anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl112anc $f wff ph $.
	f1_syl112anc $f wff ps $.
	f2_syl112anc $f wff ch $.
	f3_syl112anc $f wff th $.
	f4_syl112anc $f wff ta $.
	f5_syl112anc $f wff et $.
	e0_syl112anc $e |- ( ph -> ps ) $.
	e1_syl112anc $e |- ( ph -> ch ) $.
	e2_syl112anc $e |- ( ph -> th ) $.
	e3_syl112anc $e |- ( ph -> ta ) $.
	e4_syl112anc $e |- ( ( ps /\ ch /\ ( th /\ ta ) ) -> et ) $.
	p_syl112anc $p |- ( ph -> et ) $= e0_syl112anc e1_syl112anc e2_syl112anc e3_syl112anc f0_syl112anc f3_syl112anc f4_syl112anc p_jca e4_syl112anc f0_syl112anc f1_syl112anc f2_syl112anc f3_syl112anc f4_syl112anc a_wa f5_syl112anc p_syl3anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl121anc $f wff ph $.
	f1_syl121anc $f wff ps $.
	f2_syl121anc $f wff ch $.
	f3_syl121anc $f wff th $.
	f4_syl121anc $f wff ta $.
	f5_syl121anc $f wff et $.
	e0_syl121anc $e |- ( ph -> ps ) $.
	e1_syl121anc $e |- ( ph -> ch ) $.
	e2_syl121anc $e |- ( ph -> th ) $.
	e3_syl121anc $e |- ( ph -> ta ) $.
	e4_syl121anc $e |- ( ( ps /\ ( ch /\ th ) /\ ta ) -> et ) $.
	p_syl121anc $p |- ( ph -> et ) $= e0_syl121anc e1_syl121anc e2_syl121anc f0_syl121anc f2_syl121anc f3_syl121anc p_jca e3_syl121anc e4_syl121anc f0_syl121anc f1_syl121anc f2_syl121anc f3_syl121anc a_wa f4_syl121anc f5_syl121anc p_syl3anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl211anc $f wff ph $.
	f1_syl211anc $f wff ps $.
	f2_syl211anc $f wff ch $.
	f3_syl211anc $f wff th $.
	f4_syl211anc $f wff ta $.
	f5_syl211anc $f wff et $.
	e0_syl211anc $e |- ( ph -> ps ) $.
	e1_syl211anc $e |- ( ph -> ch ) $.
	e2_syl211anc $e |- ( ph -> th ) $.
	e3_syl211anc $e |- ( ph -> ta ) $.
	e4_syl211anc $e |- ( ( ( ps /\ ch ) /\ th /\ ta ) -> et ) $.
	p_syl211anc $p |- ( ph -> et ) $= e0_syl211anc e1_syl211anc f0_syl211anc f1_syl211anc f2_syl211anc p_jca e2_syl211anc e3_syl211anc e4_syl211anc f0_syl211anc f1_syl211anc f2_syl211anc a_wa f3_syl211anc f4_syl211anc f5_syl211anc p_syl3anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl23anc $f wff ph $.
	f1_syl23anc $f wff ps $.
	f2_syl23anc $f wff ch $.
	f3_syl23anc $f wff th $.
	f4_syl23anc $f wff ta $.
	f5_syl23anc $f wff et $.
	f6_syl23anc $f wff ze $.
	e0_syl23anc $e |- ( ph -> ps ) $.
	e1_syl23anc $e |- ( ph -> ch ) $.
	e2_syl23anc $e |- ( ph -> th ) $.
	e3_syl23anc $e |- ( ph -> ta ) $.
	e4_syl23anc $e |- ( ph -> et ) $.
	e5_syl23anc $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) ) -> ze ) $.
	p_syl23anc $p |- ( ph -> ze ) $= e0_syl23anc e1_syl23anc f0_syl23anc f1_syl23anc f2_syl23anc p_jca e2_syl23anc e3_syl23anc e4_syl23anc e5_syl23anc f0_syl23anc f1_syl23anc f2_syl23anc a_wa f3_syl23anc f4_syl23anc f5_syl23anc f6_syl23anc p_syl13anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl32anc $f wff ph $.
	f1_syl32anc $f wff ps $.
	f2_syl32anc $f wff ch $.
	f3_syl32anc $f wff th $.
	f4_syl32anc $f wff ta $.
	f5_syl32anc $f wff et $.
	f6_syl32anc $f wff ze $.
	e0_syl32anc $e |- ( ph -> ps ) $.
	e1_syl32anc $e |- ( ph -> ch ) $.
	e2_syl32anc $e |- ( ph -> th ) $.
	e3_syl32anc $e |- ( ph -> ta ) $.
	e4_syl32anc $e |- ( ph -> et ) $.
	e5_syl32anc $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
	p_syl32anc $p |- ( ph -> ze ) $= e0_syl32anc e1_syl32anc e2_syl32anc e3_syl32anc e4_syl32anc f0_syl32anc f4_syl32anc f5_syl32anc p_jca e5_syl32anc f0_syl32anc f1_syl32anc f2_syl32anc f3_syl32anc f4_syl32anc f5_syl32anc a_wa f6_syl32anc p_syl31anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl122anc $f wff ph $.
	f1_syl122anc $f wff ps $.
	f2_syl122anc $f wff ch $.
	f3_syl122anc $f wff th $.
	f4_syl122anc $f wff ta $.
	f5_syl122anc $f wff et $.
	f6_syl122anc $f wff ze $.
	e0_syl122anc $e |- ( ph -> ps ) $.
	e1_syl122anc $e |- ( ph -> ch ) $.
	e2_syl122anc $e |- ( ph -> th ) $.
	e3_syl122anc $e |- ( ph -> ta ) $.
	e4_syl122anc $e |- ( ph -> et ) $.
	e5_syl122anc $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
	p_syl122anc $p |- ( ph -> ze ) $= e0_syl122anc e1_syl122anc e2_syl122anc e3_syl122anc e4_syl122anc f0_syl122anc f4_syl122anc f5_syl122anc p_jca e5_syl122anc f0_syl122anc f1_syl122anc f2_syl122anc f3_syl122anc f4_syl122anc f5_syl122anc a_wa f6_syl122anc p_syl121anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl212anc $f wff ph $.
	f1_syl212anc $f wff ps $.
	f2_syl212anc $f wff ch $.
	f3_syl212anc $f wff th $.
	f4_syl212anc $f wff ta $.
	f5_syl212anc $f wff et $.
	f6_syl212anc $f wff ze $.
	e0_syl212anc $e |- ( ph -> ps ) $.
	e1_syl212anc $e |- ( ph -> ch ) $.
	e2_syl212anc $e |- ( ph -> th ) $.
	e3_syl212anc $e |- ( ph -> ta ) $.
	e4_syl212anc $e |- ( ph -> et ) $.
	e5_syl212anc $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et ) ) -> ze ) $.
	p_syl212anc $p |- ( ph -> ze ) $= e0_syl212anc e1_syl212anc e2_syl212anc e3_syl212anc e4_syl212anc f0_syl212anc f4_syl212anc f5_syl212anc p_jca e5_syl212anc f0_syl212anc f1_syl212anc f2_syl212anc f3_syl212anc f4_syl212anc f5_syl212anc a_wa f6_syl212anc p_syl211anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl221anc $f wff ph $.
	f1_syl221anc $f wff ps $.
	f2_syl221anc $f wff ch $.
	f3_syl221anc $f wff th $.
	f4_syl221anc $f wff ta $.
	f5_syl221anc $f wff et $.
	f6_syl221anc $f wff ze $.
	e0_syl221anc $e |- ( ph -> ps ) $.
	e1_syl221anc $e |- ( ph -> ch ) $.
	e2_syl221anc $e |- ( ph -> th ) $.
	e3_syl221anc $e |- ( ph -> ta ) $.
	e4_syl221anc $e |- ( ph -> et ) $.
	e5_syl221anc $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ et ) -> ze ) $.
	p_syl221anc $p |- ( ph -> ze ) $= e0_syl221anc e1_syl221anc e2_syl221anc e3_syl221anc f0_syl221anc f3_syl221anc f4_syl221anc p_jca e4_syl221anc e5_syl221anc f0_syl221anc f1_syl221anc f2_syl221anc f3_syl221anc f4_syl221anc a_wa f5_syl221anc f6_syl221anc p_syl211anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl113anc $f wff ph $.
	f1_syl113anc $f wff ps $.
	f2_syl113anc $f wff ch $.
	f3_syl113anc $f wff th $.
	f4_syl113anc $f wff ta $.
	f5_syl113anc $f wff et $.
	f6_syl113anc $f wff ze $.
	e0_syl113anc $e |- ( ph -> ps ) $.
	e1_syl113anc $e |- ( ph -> ch ) $.
	e2_syl113anc $e |- ( ph -> th ) $.
	e3_syl113anc $e |- ( ph -> ta ) $.
	e4_syl113anc $e |- ( ph -> et ) $.
	e5_syl113anc $e |- ( ( ps /\ ch /\ ( th /\ ta /\ et ) ) -> ze ) $.
	p_syl113anc $p |- ( ph -> ze ) $= e0_syl113anc e1_syl113anc e2_syl113anc e3_syl113anc e4_syl113anc f0_syl113anc f3_syl113anc f4_syl113anc f5_syl113anc p_3jca e5_syl113anc f0_syl113anc f1_syl113anc f2_syl113anc f3_syl113anc f4_syl113anc f5_syl113anc a_w3a f6_syl113anc p_syl3anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl131anc $f wff ph $.
	f1_syl131anc $f wff ps $.
	f2_syl131anc $f wff ch $.
	f3_syl131anc $f wff th $.
	f4_syl131anc $f wff ta $.
	f5_syl131anc $f wff et $.
	f6_syl131anc $f wff ze $.
	e0_syl131anc $e |- ( ph -> ps ) $.
	e1_syl131anc $e |- ( ph -> ch ) $.
	e2_syl131anc $e |- ( ph -> th ) $.
	e3_syl131anc $e |- ( ph -> ta ) $.
	e4_syl131anc $e |- ( ph -> et ) $.
	e5_syl131anc $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ et ) -> ze ) $.
	p_syl131anc $p |- ( ph -> ze ) $= e0_syl131anc e1_syl131anc e2_syl131anc e3_syl131anc f0_syl131anc f2_syl131anc f3_syl131anc f4_syl131anc p_3jca e4_syl131anc e5_syl131anc f0_syl131anc f1_syl131anc f2_syl131anc f3_syl131anc f4_syl131anc a_w3a f5_syl131anc f6_syl131anc p_syl3anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl311anc $f wff ph $.
	f1_syl311anc $f wff ps $.
	f2_syl311anc $f wff ch $.
	f3_syl311anc $f wff th $.
	f4_syl311anc $f wff ta $.
	f5_syl311anc $f wff et $.
	f6_syl311anc $f wff ze $.
	e0_syl311anc $e |- ( ph -> ps ) $.
	e1_syl311anc $e |- ( ph -> ch ) $.
	e2_syl311anc $e |- ( ph -> th ) $.
	e3_syl311anc $e |- ( ph -> ta ) $.
	e4_syl311anc $e |- ( ph -> et ) $.
	e5_syl311anc $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ et ) -> ze ) $.
	p_syl311anc $p |- ( ph -> ze ) $= e0_syl311anc e1_syl311anc e2_syl311anc f0_syl311anc f1_syl311anc f2_syl311anc f3_syl311anc p_3jca e3_syl311anc e4_syl311anc e5_syl311anc f0_syl311anc f1_syl311anc f2_syl311anc f3_syl311anc a_w3a f4_syl311anc f5_syl311anc f6_syl311anc p_syl3anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl33anc $f wff ph $.
	f1_syl33anc $f wff ps $.
	f2_syl33anc $f wff ch $.
	f3_syl33anc $f wff th $.
	f4_syl33anc $f wff ta $.
	f5_syl33anc $f wff et $.
	f6_syl33anc $f wff ze $.
	f7_syl33anc $f wff si $.
	e0_syl33anc $e |- ( ph -> ps ) $.
	e1_syl33anc $e |- ( ph -> ch ) $.
	e2_syl33anc $e |- ( ph -> th ) $.
	e3_syl33anc $e |- ( ph -> ta ) $.
	e4_syl33anc $e |- ( ph -> et ) $.
	e5_syl33anc $e |- ( ph -> ze ) $.
	e6_syl33anc $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si ) $.
	p_syl33anc $p |- ( ph -> si ) $= e0_syl33anc e1_syl33anc e2_syl33anc f0_syl33anc f1_syl33anc f2_syl33anc f3_syl33anc p_3jca e3_syl33anc e4_syl33anc e5_syl33anc e6_syl33anc f0_syl33anc f1_syl33anc f2_syl33anc f3_syl33anc a_w3a f4_syl33anc f5_syl33anc f6_syl33anc f7_syl33anc p_syl13anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl222anc $f wff ph $.
	f1_syl222anc $f wff ps $.
	f2_syl222anc $f wff ch $.
	f3_syl222anc $f wff th $.
	f4_syl222anc $f wff ta $.
	f5_syl222anc $f wff et $.
	f6_syl222anc $f wff ze $.
	f7_syl222anc $f wff si $.
	e0_syl222anc $e |- ( ph -> ps ) $.
	e1_syl222anc $e |- ( ph -> ch ) $.
	e2_syl222anc $e |- ( ph -> th ) $.
	e3_syl222anc $e |- ( ph -> ta ) $.
	e4_syl222anc $e |- ( ph -> et ) $.
	e5_syl222anc $e |- ( ph -> ze ) $.
	e6_syl222anc $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze ) ) -> si ) $.
	p_syl222anc $p |- ( ph -> si ) $= e0_syl222anc e1_syl222anc e2_syl222anc e3_syl222anc e4_syl222anc e5_syl222anc f0_syl222anc f5_syl222anc f6_syl222anc p_jca e6_syl222anc f0_syl222anc f1_syl222anc f2_syl222anc f3_syl222anc f4_syl222anc f5_syl222anc f6_syl222anc a_wa f7_syl222anc p_syl221anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl123anc $f wff ph $.
	f1_syl123anc $f wff ps $.
	f2_syl123anc $f wff ch $.
	f3_syl123anc $f wff th $.
	f4_syl123anc $f wff ta $.
	f5_syl123anc $f wff et $.
	f6_syl123anc $f wff ze $.
	f7_syl123anc $f wff si $.
	e0_syl123anc $e |- ( ph -> ps ) $.
	e1_syl123anc $e |- ( ph -> ch ) $.
	e2_syl123anc $e |- ( ph -> th ) $.
	e3_syl123anc $e |- ( ph -> ta ) $.
	e4_syl123anc $e |- ( ph -> et ) $.
	e5_syl123anc $e |- ( ph -> ze ) $.
	e6_syl123anc $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si ) $.
	p_syl123anc $p |- ( ph -> si ) $= e0_syl123anc e1_syl123anc e2_syl123anc f0_syl123anc f2_syl123anc f3_syl123anc p_jca e3_syl123anc e4_syl123anc e5_syl123anc e6_syl123anc f0_syl123anc f1_syl123anc f2_syl123anc f3_syl123anc a_wa f4_syl123anc f5_syl123anc f6_syl123anc f7_syl123anc p_syl113anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl132anc $f wff ph $.
	f1_syl132anc $f wff ps $.
	f2_syl132anc $f wff ch $.
	f3_syl132anc $f wff th $.
	f4_syl132anc $f wff ta $.
	f5_syl132anc $f wff et $.
	f6_syl132anc $f wff ze $.
	f7_syl132anc $f wff si $.
	e0_syl132anc $e |- ( ph -> ps ) $.
	e1_syl132anc $e |- ( ph -> ch ) $.
	e2_syl132anc $e |- ( ph -> th ) $.
	e3_syl132anc $e |- ( ph -> ta ) $.
	e4_syl132anc $e |- ( ph -> et ) $.
	e5_syl132anc $e |- ( ph -> ze ) $.
	e6_syl132anc $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze ) ) -> si ) $.
	p_syl132anc $p |- ( ph -> si ) $= e0_syl132anc e1_syl132anc e2_syl132anc e3_syl132anc e4_syl132anc e5_syl132anc f0_syl132anc f5_syl132anc f6_syl132anc p_jca e6_syl132anc f0_syl132anc f1_syl132anc f2_syl132anc f3_syl132anc f4_syl132anc f5_syl132anc f6_syl132anc a_wa f7_syl132anc p_syl131anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl213anc $f wff ph $.
	f1_syl213anc $f wff ps $.
	f2_syl213anc $f wff ch $.
	f3_syl213anc $f wff th $.
	f4_syl213anc $f wff ta $.
	f5_syl213anc $f wff et $.
	f6_syl213anc $f wff ze $.
	f7_syl213anc $f wff si $.
	e0_syl213anc $e |- ( ph -> ps ) $.
	e1_syl213anc $e |- ( ph -> ch ) $.
	e2_syl213anc $e |- ( ph -> th ) $.
	e3_syl213anc $e |- ( ph -> ta ) $.
	e4_syl213anc $e |- ( ph -> et ) $.
	e5_syl213anc $e |- ( ph -> ze ) $.
	e6_syl213anc $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et /\ ze ) ) -> si ) $.
	p_syl213anc $p |- ( ph -> si ) $= e0_syl213anc e1_syl213anc f0_syl213anc f1_syl213anc f2_syl213anc p_jca e2_syl213anc e3_syl213anc e4_syl213anc e5_syl213anc e6_syl213anc f0_syl213anc f1_syl213anc f2_syl213anc a_wa f3_syl213anc f4_syl213anc f5_syl213anc f6_syl213anc f7_syl213anc p_syl113anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl231anc $f wff ph $.
	f1_syl231anc $f wff ps $.
	f2_syl231anc $f wff ch $.
	f3_syl231anc $f wff th $.
	f4_syl231anc $f wff ta $.
	f5_syl231anc $f wff et $.
	f6_syl231anc $f wff ze $.
	f7_syl231anc $f wff si $.
	e0_syl231anc $e |- ( ph -> ps ) $.
	e1_syl231anc $e |- ( ph -> ch ) $.
	e2_syl231anc $e |- ( ph -> th ) $.
	e3_syl231anc $e |- ( ph -> ta ) $.
	e4_syl231anc $e |- ( ph -> et ) $.
	e5_syl231anc $e |- ( ph -> ze ) $.
	e6_syl231anc $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze ) -> si ) $.
	p_syl231anc $p |- ( ph -> si ) $= e0_syl231anc e1_syl231anc f0_syl231anc f1_syl231anc f2_syl231anc p_jca e2_syl231anc e3_syl231anc e4_syl231anc e5_syl231anc e6_syl231anc f0_syl231anc f1_syl231anc f2_syl231anc a_wa f3_syl231anc f4_syl231anc f5_syl231anc f6_syl231anc f7_syl231anc p_syl131anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl312anc $f wff ph $.
	f1_syl312anc $f wff ps $.
	f2_syl312anc $f wff ch $.
	f3_syl312anc $f wff th $.
	f4_syl312anc $f wff ta $.
	f5_syl312anc $f wff et $.
	f6_syl312anc $f wff ze $.
	f7_syl312anc $f wff si $.
	e0_syl312anc $e |- ( ph -> ps ) $.
	e1_syl312anc $e |- ( ph -> ch ) $.
	e2_syl312anc $e |- ( ph -> th ) $.
	e3_syl312anc $e |- ( ph -> ta ) $.
	e4_syl312anc $e |- ( ph -> et ) $.
	e5_syl312anc $e |- ( ph -> ze ) $.
	e6_syl312anc $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze ) ) -> si ) $.
	p_syl312anc $p |- ( ph -> si ) $= e0_syl312anc e1_syl312anc e2_syl312anc e3_syl312anc e4_syl312anc e5_syl312anc f0_syl312anc f5_syl312anc f6_syl312anc p_jca e6_syl312anc f0_syl312anc f1_syl312anc f2_syl312anc f3_syl312anc f4_syl312anc f5_syl312anc f6_syl312anc a_wa f7_syl312anc p_syl311anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl321anc $f wff ph $.
	f1_syl321anc $f wff ps $.
	f2_syl321anc $f wff ch $.
	f3_syl321anc $f wff th $.
	f4_syl321anc $f wff ta $.
	f5_syl321anc $f wff et $.
	f6_syl321anc $f wff ze $.
	f7_syl321anc $f wff si $.
	e0_syl321anc $e |- ( ph -> ps ) $.
	e1_syl321anc $e |- ( ph -> ch ) $.
	e2_syl321anc $e |- ( ph -> th ) $.
	e3_syl321anc $e |- ( ph -> ta ) $.
	e4_syl321anc $e |- ( ph -> et ) $.
	e5_syl321anc $e |- ( ph -> ze ) $.
	e6_syl321anc $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze ) -> si ) $.
	p_syl321anc $p |- ( ph -> si ) $= e0_syl321anc e1_syl321anc e2_syl321anc e3_syl321anc e4_syl321anc f0_syl321anc f4_syl321anc f5_syl321anc p_jca e5_syl321anc e6_syl321anc f0_syl321anc f1_syl321anc f2_syl321anc f3_syl321anc f4_syl321anc f5_syl321anc a_wa f6_syl321anc f7_syl321anc p_syl311anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_syl133anc $f wff ph $.
	f1_syl133anc $f wff ps $.
	f2_syl133anc $f wff ch $.
	f3_syl133anc $f wff th $.
	f4_syl133anc $f wff ta $.
	f5_syl133anc $f wff et $.
	f6_syl133anc $f wff ze $.
	f7_syl133anc $f wff si $.
	f8_syl133anc $f wff rh $.
	e0_syl133anc $e |- ( ph -> ps ) $.
	e1_syl133anc $e |- ( ph -> ch ) $.
	e2_syl133anc $e |- ( ph -> th ) $.
	e3_syl133anc $e |- ( ph -> ta ) $.
	e4_syl133anc $e |- ( ph -> et ) $.
	e5_syl133anc $e |- ( ph -> ze ) $.
	e6_syl133anc $e |- ( ph -> si ) $.
	e7_syl133anc $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze /\ si ) ) -> rh ) $.
	p_syl133anc $p |- ( ph -> rh ) $= e0_syl133anc e1_syl133anc e2_syl133anc e3_syl133anc e4_syl133anc e5_syl133anc e6_syl133anc f0_syl133anc f5_syl133anc f6_syl133anc f7_syl133anc p_3jca e7_syl133anc f0_syl133anc f1_syl133anc f2_syl133anc f3_syl133anc f4_syl133anc f5_syl133anc f6_syl133anc f7_syl133anc a_w3a f8_syl133anc p_syl131anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_syl313anc $f wff ph $.
	f1_syl313anc $f wff ps $.
	f2_syl313anc $f wff ch $.
	f3_syl313anc $f wff th $.
	f4_syl313anc $f wff ta $.
	f5_syl313anc $f wff et $.
	f6_syl313anc $f wff ze $.
	f7_syl313anc $f wff si $.
	f8_syl313anc $f wff rh $.
	e0_syl313anc $e |- ( ph -> ps ) $.
	e1_syl313anc $e |- ( ph -> ch ) $.
	e2_syl313anc $e |- ( ph -> th ) $.
	e3_syl313anc $e |- ( ph -> ta ) $.
	e4_syl313anc $e |- ( ph -> et ) $.
	e5_syl313anc $e |- ( ph -> ze ) $.
	e6_syl313anc $e |- ( ph -> si ) $.
	e7_syl313anc $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze /\ si ) ) -> rh ) $.
	p_syl313anc $p |- ( ph -> rh ) $= e0_syl313anc e1_syl313anc e2_syl313anc e3_syl313anc e4_syl313anc e5_syl313anc e6_syl313anc f0_syl313anc f5_syl313anc f6_syl313anc f7_syl313anc p_3jca e7_syl313anc f0_syl313anc f1_syl313anc f2_syl313anc f3_syl313anc f4_syl313anc f5_syl313anc f6_syl313anc f7_syl313anc a_w3a f8_syl313anc p_syl311anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_syl331anc $f wff ph $.
	f1_syl331anc $f wff ps $.
	f2_syl331anc $f wff ch $.
	f3_syl331anc $f wff th $.
	f4_syl331anc $f wff ta $.
	f5_syl331anc $f wff et $.
	f6_syl331anc $f wff ze $.
	f7_syl331anc $f wff si $.
	f8_syl331anc $f wff rh $.
	e0_syl331anc $e |- ( ph -> ps ) $.
	e1_syl331anc $e |- ( ph -> ch ) $.
	e2_syl331anc $e |- ( ph -> th ) $.
	e3_syl331anc $e |- ( ph -> ta ) $.
	e4_syl331anc $e |- ( ph -> et ) $.
	e5_syl331anc $e |- ( ph -> ze ) $.
	e6_syl331anc $e |- ( ph -> si ) $.
	e7_syl331anc $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ si ) -> rh ) $.
	p_syl331anc $p |- ( ph -> rh ) $= e0_syl331anc e1_syl331anc e2_syl331anc e3_syl331anc e4_syl331anc e5_syl331anc f0_syl331anc f4_syl331anc f5_syl331anc f6_syl331anc p_3jca e6_syl331anc e7_syl331anc f0_syl331anc f1_syl331anc f2_syl331anc f3_syl331anc f4_syl331anc f5_syl331anc f6_syl331anc a_w3a f7_syl331anc f8_syl331anc p_syl311anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_syl223anc $f wff ph $.
	f1_syl223anc $f wff ps $.
	f2_syl223anc $f wff ch $.
	f3_syl223anc $f wff th $.
	f4_syl223anc $f wff ta $.
	f5_syl223anc $f wff et $.
	f6_syl223anc $f wff ze $.
	f7_syl223anc $f wff si $.
	f8_syl223anc $f wff rh $.
	e0_syl223anc $e |- ( ph -> ps ) $.
	e1_syl223anc $e |- ( ph -> ch ) $.
	e2_syl223anc $e |- ( ph -> th ) $.
	e3_syl223anc $e |- ( ph -> ta ) $.
	e4_syl223anc $e |- ( ph -> et ) $.
	e5_syl223anc $e |- ( ph -> ze ) $.
	e6_syl223anc $e |- ( ph -> si ) $.
	e7_syl223anc $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze /\ si ) ) -> rh ) $.
	p_syl223anc $p |- ( ph -> rh ) $= e0_syl223anc e1_syl223anc e2_syl223anc e3_syl223anc f0_syl223anc f3_syl223anc f4_syl223anc p_jca e4_syl223anc e5_syl223anc e6_syl223anc e7_syl223anc f0_syl223anc f1_syl223anc f2_syl223anc f3_syl223anc f4_syl223anc a_wa f5_syl223anc f6_syl223anc f7_syl223anc f8_syl223anc p_syl213anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_syl232anc $f wff ph $.
	f1_syl232anc $f wff ps $.
	f2_syl232anc $f wff ch $.
	f3_syl232anc $f wff th $.
	f4_syl232anc $f wff ta $.
	f5_syl232anc $f wff et $.
	f6_syl232anc $f wff ze $.
	f7_syl232anc $f wff si $.
	f8_syl232anc $f wff rh $.
	e0_syl232anc $e |- ( ph -> ps ) $.
	e1_syl232anc $e |- ( ph -> ch ) $.
	e2_syl232anc $e |- ( ph -> th ) $.
	e3_syl232anc $e |- ( ph -> ta ) $.
	e4_syl232anc $e |- ( ph -> et ) $.
	e5_syl232anc $e |- ( ph -> ze ) $.
	e6_syl232anc $e |- ( ph -> si ) $.
	e7_syl232anc $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si ) ) -> rh ) $.
	p_syl232anc $p |- ( ph -> rh ) $= e0_syl232anc e1_syl232anc e2_syl232anc e3_syl232anc e4_syl232anc e5_syl232anc e6_syl232anc f0_syl232anc f6_syl232anc f7_syl232anc p_jca e7_syl232anc f0_syl232anc f1_syl232anc f2_syl232anc f3_syl232anc f4_syl232anc f5_syl232anc f6_syl232anc f7_syl232anc a_wa f8_syl232anc p_syl231anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_syl322anc $f wff ph $.
	f1_syl322anc $f wff ps $.
	f2_syl322anc $f wff ch $.
	f3_syl322anc $f wff th $.
	f4_syl322anc $f wff ta $.
	f5_syl322anc $f wff et $.
	f6_syl322anc $f wff ze $.
	f7_syl322anc $f wff si $.
	f8_syl322anc $f wff rh $.
	e0_syl322anc $e |- ( ph -> ps ) $.
	e1_syl322anc $e |- ( ph -> ch ) $.
	e2_syl322anc $e |- ( ph -> th ) $.
	e3_syl322anc $e |- ( ph -> ta ) $.
	e4_syl322anc $e |- ( ph -> et ) $.
	e5_syl322anc $e |- ( ph -> ze ) $.
	e6_syl322anc $e |- ( ph -> si ) $.
	e7_syl322anc $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si ) ) -> rh ) $.
	p_syl322anc $p |- ( ph -> rh ) $= e0_syl322anc e1_syl322anc e2_syl322anc e3_syl322anc e4_syl322anc e5_syl322anc e6_syl322anc f0_syl322anc f6_syl322anc f7_syl322anc p_jca e7_syl322anc f0_syl322anc f1_syl322anc f2_syl322anc f3_syl322anc f4_syl322anc f5_syl322anc f6_syl322anc f7_syl322anc a_wa f8_syl322anc p_syl321anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh mu  $.
	f0_syl233anc $f wff ph $.
	f1_syl233anc $f wff ps $.
	f2_syl233anc $f wff ch $.
	f3_syl233anc $f wff th $.
	f4_syl233anc $f wff ta $.
	f5_syl233anc $f wff et $.
	f6_syl233anc $f wff ze $.
	f7_syl233anc $f wff si $.
	f8_syl233anc $f wff rh $.
	f9_syl233anc $f wff mu $.
	e0_syl233anc $e |- ( ph -> ps ) $.
	e1_syl233anc $e |- ( ph -> ch ) $.
	e2_syl233anc $e |- ( ph -> th ) $.
	e3_syl233anc $e |- ( ph -> ta ) $.
	e4_syl233anc $e |- ( ph -> et ) $.
	e5_syl233anc $e |- ( ph -> ze ) $.
	e6_syl233anc $e |- ( ph -> si ) $.
	e7_syl233anc $e |- ( ph -> rh ) $.
	e8_syl233anc $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\ rh ) ) -> mu ) $.
	p_syl233anc $p |- ( ph -> mu ) $= e0_syl233anc e1_syl233anc f0_syl233anc f1_syl233anc f2_syl233anc p_jca e2_syl233anc e3_syl233anc e4_syl233anc e5_syl233anc e6_syl233anc e7_syl233anc e8_syl233anc f0_syl233anc f1_syl233anc f2_syl233anc a_wa f3_syl233anc f4_syl233anc f5_syl233anc f6_syl233anc f7_syl233anc f8_syl233anc f9_syl233anc p_syl133anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh mu  $.
	f0_syl323anc $f wff ph $.
	f1_syl323anc $f wff ps $.
	f2_syl323anc $f wff ch $.
	f3_syl323anc $f wff th $.
	f4_syl323anc $f wff ta $.
	f5_syl323anc $f wff et $.
	f6_syl323anc $f wff ze $.
	f7_syl323anc $f wff si $.
	f8_syl323anc $f wff rh $.
	f9_syl323anc $f wff mu $.
	e0_syl323anc $e |- ( ph -> ps ) $.
	e1_syl323anc $e |- ( ph -> ch ) $.
	e2_syl323anc $e |- ( ph -> th ) $.
	e3_syl323anc $e |- ( ph -> ta ) $.
	e4_syl323anc $e |- ( ph -> et ) $.
	e5_syl323anc $e |- ( ph -> ze ) $.
	e6_syl323anc $e |- ( ph -> si ) $.
	e7_syl323anc $e |- ( ph -> rh ) $.
	e8_syl323anc $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si /\ rh ) ) -> mu ) $.
	p_syl323anc $p |- ( ph -> mu ) $= e0_syl323anc e1_syl323anc e2_syl323anc e3_syl323anc e4_syl323anc f0_syl323anc f4_syl323anc f5_syl323anc p_jca e5_syl323anc e6_syl323anc e7_syl323anc e8_syl323anc f0_syl323anc f1_syl323anc f2_syl323anc f3_syl323anc f4_syl323anc f5_syl323anc a_wa f6_syl323anc f7_syl323anc f8_syl323anc f9_syl323anc p_syl313anc $.
$}

$(Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh mu  $.
	f0_syl332anc $f wff ph $.
	f1_syl332anc $f wff ps $.
	f2_syl332anc $f wff ch $.
	f3_syl332anc $f wff th $.
	f4_syl332anc $f wff ta $.
	f5_syl332anc $f wff et $.
	f6_syl332anc $f wff ze $.
	f7_syl332anc $f wff si $.
	f8_syl332anc $f wff rh $.
	f9_syl332anc $f wff mu $.
	e0_syl332anc $e |- ( ph -> ps ) $.
	e1_syl332anc $e |- ( ph -> ch ) $.
	e2_syl332anc $e |- ( ph -> th ) $.
	e3_syl332anc $e |- ( ph -> ta ) $.
	e4_syl332anc $e |- ( ph -> et ) $.
	e5_syl332anc $e |- ( ph -> ze ) $.
	e6_syl332anc $e |- ( ph -> si ) $.
	e7_syl332anc $e |- ( ph -> rh ) $.
	e8_syl332anc $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh ) ) -> mu ) $.
	p_syl332anc $p |- ( ph -> mu ) $= e0_syl332anc e1_syl332anc e2_syl332anc e3_syl332anc e4_syl332anc e5_syl332anc e6_syl332anc e7_syl332anc f0_syl332anc f7_syl332anc f8_syl332anc p_jca e8_syl332anc f0_syl332anc f1_syl332anc f2_syl332anc f3_syl332anc f4_syl332anc f5_syl332anc f6_syl332anc f7_syl332anc f8_syl332anc a_wa f9_syl332anc p_syl331anc $.
$}

$(A syllogism inference combined with contraction.  (Contributed by NM,
         10-Mar-2012.) $)

${
	$v ph ps ch th ta et ze si rh mu la  $.
	f0_syl333anc $f wff ph $.
	f1_syl333anc $f wff ps $.
	f2_syl333anc $f wff ch $.
	f3_syl333anc $f wff th $.
	f4_syl333anc $f wff ta $.
	f5_syl333anc $f wff et $.
	f6_syl333anc $f wff ze $.
	f7_syl333anc $f wff si $.
	f8_syl333anc $f wff rh $.
	f9_syl333anc $f wff mu $.
	f10_syl333anc $f wff la $.
	e0_syl333anc $e |- ( ph -> ps ) $.
	e1_syl333anc $e |- ( ph -> ch ) $.
	e2_syl333anc $e |- ( ph -> th ) $.
	e3_syl333anc $e |- ( ph -> ta ) $.
	e4_syl333anc $e |- ( ph -> et ) $.
	e5_syl333anc $e |- ( ph -> ze ) $.
	e6_syl333anc $e |- ( ph -> si ) $.
	e7_syl333anc $e |- ( ph -> rh ) $.
	e8_syl333anc $e |- ( ph -> mu ) $.
	e9_syl333anc $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh /\ mu ) ) -> la ) $.
	p_syl333anc $p |- ( ph -> la ) $= e0_syl333anc e1_syl333anc e2_syl333anc e3_syl333anc e4_syl333anc e5_syl333anc e6_syl333anc e7_syl333anc e8_syl333anc f0_syl333anc f7_syl333anc f8_syl333anc f9_syl333anc p_3jca e9_syl333anc f0_syl333anc f1_syl333anc f2_syl333anc f3_syl333anc f4_syl333anc f5_syl333anc f6_syl333anc f7_syl333anc f8_syl333anc f9_syl333anc a_w3a f10_syl333anc p_syl331anc $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an1 $f wff ph $.
	f1_syl3an1 $f wff ps $.
	f2_syl3an1 $f wff ch $.
	f3_syl3an1 $f wff th $.
	f4_syl3an1 $f wff ta $.
	e0_syl3an1 $e |- ( ph -> ps ) $.
	e1_syl3an1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an1 $p |- ( ( ph /\ ch /\ th ) -> ta ) $= e0_syl3an1 f0_syl3an1 f1_syl3an1 f2_syl3an1 f3_syl3an1 p_3anim1i e1_syl3an1 f0_syl3an1 f2_syl3an1 f3_syl3an1 a_w3a f1_syl3an1 f2_syl3an1 f3_syl3an1 a_w3a f4_syl3an1 p_syl $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an2 $f wff ph $.
	f1_syl3an2 $f wff ps $.
	f2_syl3an2 $f wff ch $.
	f3_syl3an2 $f wff th $.
	f4_syl3an2 $f wff ta $.
	e0_syl3an2 $e |- ( ph -> ch ) $.
	e1_syl3an2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an2 $p |- ( ( ps /\ ph /\ th ) -> ta ) $= e0_syl3an2 e1_syl3an2 f1_syl3an2 f2_syl3an2 f3_syl3an2 f4_syl3an2 p_3exp f0_syl3an2 f2_syl3an2 f1_syl3an2 f3_syl3an2 f4_syl3an2 a_wi p_syl5 f1_syl3an2 f0_syl3an2 f3_syl3an2 f4_syl3an2 p_3imp $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an3 $f wff ph $.
	f1_syl3an3 $f wff ps $.
	f2_syl3an3 $f wff ch $.
	f3_syl3an3 $f wff th $.
	f4_syl3an3 $f wff ta $.
	e0_syl3an3 $e |- ( ph -> th ) $.
	e1_syl3an3 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an3 $p |- ( ( ps /\ ch /\ ph ) -> ta ) $= e0_syl3an3 e1_syl3an3 f1_syl3an3 f2_syl3an3 f3_syl3an3 f4_syl3an3 p_3exp f0_syl3an3 f3_syl3an3 f1_syl3an3 f2_syl3an3 f4_syl3an3 p_syl7 f1_syl3an3 f2_syl3an3 f0_syl3an3 f4_syl3an3 p_3imp $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an1b $f wff ph $.
	f1_syl3an1b $f wff ps $.
	f2_syl3an1b $f wff ch $.
	f3_syl3an1b $f wff th $.
	f4_syl3an1b $f wff ta $.
	e0_syl3an1b $e |- ( ph <-> ps ) $.
	e1_syl3an1b $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an1b $p |- ( ( ph /\ ch /\ th ) -> ta ) $= e0_syl3an1b f0_syl3an1b f1_syl3an1b p_biimpi e1_syl3an1b f0_syl3an1b f1_syl3an1b f2_syl3an1b f3_syl3an1b f4_syl3an1b p_syl3an1 $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an2b $f wff ph $.
	f1_syl3an2b $f wff ps $.
	f2_syl3an2b $f wff ch $.
	f3_syl3an2b $f wff th $.
	f4_syl3an2b $f wff ta $.
	e0_syl3an2b $e |- ( ph <-> ch ) $.
	e1_syl3an2b $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an2b $p |- ( ( ps /\ ph /\ th ) -> ta ) $= e0_syl3an2b f0_syl3an2b f2_syl3an2b p_biimpi e1_syl3an2b f0_syl3an2b f1_syl3an2b f2_syl3an2b f3_syl3an2b f4_syl3an2b p_syl3an2 $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an3b $f wff ph $.
	f1_syl3an3b $f wff ps $.
	f2_syl3an3b $f wff ch $.
	f3_syl3an3b $f wff th $.
	f4_syl3an3b $f wff ta $.
	e0_syl3an3b $e |- ( ph <-> th ) $.
	e1_syl3an3b $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an3b $p |- ( ( ps /\ ch /\ ph ) -> ta ) $= e0_syl3an3b f0_syl3an3b f3_syl3an3b p_biimpi e1_syl3an3b f0_syl3an3b f1_syl3an3b f2_syl3an3b f3_syl3an3b f4_syl3an3b p_syl3an3 $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an1br $f wff ph $.
	f1_syl3an1br $f wff ps $.
	f2_syl3an1br $f wff ch $.
	f3_syl3an1br $f wff th $.
	f4_syl3an1br $f wff ta $.
	e0_syl3an1br $e |- ( ps <-> ph ) $.
	e1_syl3an1br $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an1br $p |- ( ( ph /\ ch /\ th ) -> ta ) $= e0_syl3an1br f1_syl3an1br f0_syl3an1br p_biimpri e1_syl3an1br f0_syl3an1br f1_syl3an1br f2_syl3an1br f3_syl3an1br f4_syl3an1br p_syl3an1 $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an2br $f wff ph $.
	f1_syl3an2br $f wff ps $.
	f2_syl3an2br $f wff ch $.
	f3_syl3an2br $f wff th $.
	f4_syl3an2br $f wff ta $.
	e0_syl3an2br $e |- ( ch <-> ph ) $.
	e1_syl3an2br $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an2br $p |- ( ( ps /\ ph /\ th ) -> ta ) $= e0_syl3an2br f2_syl3an2br f0_syl3an2br p_biimpri e1_syl3an2br f0_syl3an2br f1_syl3an2br f2_syl3an2br f3_syl3an2br f4_syl3an2br p_syl3an2 $.
$}

$(A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3an3br $f wff ph $.
	f1_syl3an3br $f wff ps $.
	f2_syl3an3br $f wff ch $.
	f3_syl3an3br $f wff th $.
	f4_syl3an3br $f wff ta $.
	e0_syl3an3br $e |- ( th <-> ph ) $.
	e1_syl3an3br $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	p_syl3an3br $p |- ( ( ps /\ ch /\ ph ) -> ta ) $= e0_syl3an3br f3_syl3an3br f0_syl3an3br p_biimpri e1_syl3an3br f0_syl3an3br f1_syl3an3br f2_syl3an3br f3_syl3an3br f4_syl3an3br p_syl3an3 $.
$}

$(A triple syllogism inference.  (Contributed by NM, 13-May-2004.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl3an $f wff ph $.
	f1_syl3an $f wff ps $.
	f2_syl3an $f wff ch $.
	f3_syl3an $f wff th $.
	f4_syl3an $f wff ta $.
	f5_syl3an $f wff et $.
	f6_syl3an $f wff ze $.
	e0_syl3an $e |- ( ph -> ps ) $.
	e1_syl3an $e |- ( ch -> th ) $.
	e2_syl3an $e |- ( ta -> et ) $.
	e3_syl3an $e |- ( ( ps /\ th /\ et ) -> ze ) $.
	p_syl3an $p |- ( ( ph /\ ch /\ ta ) -> ze ) $= e0_syl3an e1_syl3an e2_syl3an f0_syl3an f1_syl3an f2_syl3an f3_syl3an f4_syl3an f5_syl3an p_3anim123i e3_syl3an f0_syl3an f2_syl3an f4_syl3an a_w3a f1_syl3an f3_syl3an f5_syl3an a_w3a f6_syl3an p_syl $.
$}

$(A triple syllogism inference.  (Contributed by NM, 15-Oct-2005.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl3anb $f wff ph $.
	f1_syl3anb $f wff ps $.
	f2_syl3anb $f wff ch $.
	f3_syl3anb $f wff th $.
	f4_syl3anb $f wff ta $.
	f5_syl3anb $f wff et $.
	f6_syl3anb $f wff ze $.
	e0_syl3anb $e |- ( ph <-> ps ) $.
	e1_syl3anb $e |- ( ch <-> th ) $.
	e2_syl3anb $e |- ( ta <-> et ) $.
	e3_syl3anb $e |- ( ( ps /\ th /\ et ) -> ze ) $.
	p_syl3anb $p |- ( ( ph /\ ch /\ ta ) -> ze ) $= e0_syl3anb e1_syl3anb e2_syl3anb f0_syl3anb f1_syl3anb f2_syl3anb f3_syl3anb f4_syl3anb f5_syl3anb p_3anbi123i e3_syl3anb f0_syl3anb f2_syl3anb f4_syl3anb a_w3a f1_syl3anb f3_syl3anb f5_syl3anb a_w3a f6_syl3anb p_sylbi $.
$}

$(A triple syllogism inference.  (Contributed by NM, 29-Dec-2011.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl3anbr $f wff ph $.
	f1_syl3anbr $f wff ps $.
	f2_syl3anbr $f wff ch $.
	f3_syl3anbr $f wff th $.
	f4_syl3anbr $f wff ta $.
	f5_syl3anbr $f wff et $.
	f6_syl3anbr $f wff ze $.
	e0_syl3anbr $e |- ( ps <-> ph ) $.
	e1_syl3anbr $e |- ( th <-> ch ) $.
	e2_syl3anbr $e |- ( et <-> ta ) $.
	e3_syl3anbr $e |- ( ( ps /\ th /\ et ) -> ze ) $.
	p_syl3anbr $p |- ( ( ph /\ ch /\ ta ) -> ze ) $= e0_syl3anbr f1_syl3anbr f0_syl3anbr p_bicomi e1_syl3anbr f3_syl3anbr f2_syl3anbr p_bicomi e2_syl3anbr f5_syl3anbr f4_syl3anbr p_bicomi e3_syl3anbr f0_syl3anbr f1_syl3anbr f2_syl3anbr f3_syl3anbr f4_syl3anbr f5_syl3anbr f6_syl3anbr p_syl3anb $.
$}

$(A syllogism inference.  (Contributed by NM, 20-May-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_syld3an3 $f wff ph $.
	f1_syld3an3 $f wff ps $.
	f2_syld3an3 $f wff ch $.
	f3_syld3an3 $f wff th $.
	f4_syld3an3 $f wff ta $.
	e0_syld3an3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	e1_syld3an3 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
	p_syld3an3 $p |- ( ( ph /\ ps /\ ch ) -> ta ) $= f0_syld3an3 f1_syld3an3 f2_syld3an3 p_simp1 f0_syld3an3 f1_syld3an3 f2_syld3an3 p_simp2 e0_syld3an3 e1_syld3an3 f0_syld3an3 f1_syld3an3 f2_syld3an3 a_w3a f0_syld3an3 f1_syld3an3 f3_syld3an3 f4_syld3an3 p_syl3anc $.
$}

$(A syllogism inference.  (Contributed by NM, 7-Jul-2008.) $)

${
	$v ph ps ch th ta  $.
	f0_syld3an1 $f wff ph $.
	f1_syld3an1 $f wff ps $.
	f2_syld3an1 $f wff ch $.
	f3_syld3an1 $f wff th $.
	f4_syld3an1 $f wff ta $.
	e0_syld3an1 $e |- ( ( ch /\ ps /\ th ) -> ph ) $.
	e1_syld3an1 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
	p_syld3an1 $p |- ( ( ch /\ ps /\ th ) -> ta ) $= e0_syld3an1 f2_syld3an1 f1_syld3an1 f3_syld3an1 f0_syld3an1 p_3com13 e1_syld3an1 f0_syld3an1 f1_syld3an1 f3_syld3an1 f4_syld3an1 p_3com13 f3_syld3an1 f1_syld3an1 f2_syld3an1 f0_syld3an1 f4_syld3an1 p_syld3an3 f3_syld3an1 f1_syld3an1 f2_syld3an1 f4_syld3an1 p_3com13 $.
$}

$(A syllogism inference.  (Contributed by NM, 20-May-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_syld3an2 $f wff ph $.
	f1_syld3an2 $f wff ps $.
	f2_syld3an2 $f wff ch $.
	f3_syld3an2 $f wff th $.
	f4_syld3an2 $f wff ta $.
	e0_syld3an2 $e |- ( ( ph /\ ch /\ th ) -> ps ) $.
	e1_syld3an2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
	p_syld3an2 $p |- ( ( ph /\ ch /\ th ) -> ta ) $= e0_syld3an2 f0_syld3an2 f2_syld3an2 f3_syld3an2 f1_syld3an2 p_3com23 e1_syld3an2 f0_syld3an2 f1_syld3an2 f3_syld3an2 f4_syld3an2 p_3com23 f0_syld3an2 f3_syld3an2 f2_syld3an2 f1_syld3an2 f4_syld3an2 p_syld3an3 f0_syld3an2 f3_syld3an2 f2_syld3an2 f4_syld3an2 p_3com23 $.
$}

$(A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl3anl1 $f wff ph $.
	f1_syl3anl1 $f wff ps $.
	f2_syl3anl1 $f wff ch $.
	f3_syl3anl1 $f wff th $.
	f4_syl3anl1 $f wff ta $.
	f5_syl3anl1 $f wff et $.
	e0_syl3anl1 $e |- ( ph -> ps ) $.
	e1_syl3anl1 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
	p_syl3anl1 $p |- ( ( ( ph /\ ch /\ th ) /\ ta ) -> et ) $= e0_syl3anl1 f0_syl3anl1 f1_syl3anl1 f2_syl3anl1 f3_syl3anl1 p_3anim1i e1_syl3anl1 f0_syl3anl1 f2_syl3anl1 f3_syl3anl1 a_w3a f1_syl3anl1 f2_syl3anl1 f3_syl3anl1 a_w3a f4_syl3anl1 f5_syl3anl1 p_sylan $.
$}

$(A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl3anl2 $f wff ph $.
	f1_syl3anl2 $f wff ps $.
	f2_syl3anl2 $f wff ch $.
	f3_syl3anl2 $f wff th $.
	f4_syl3anl2 $f wff ta $.
	f5_syl3anl2 $f wff et $.
	e0_syl3anl2 $e |- ( ph -> ch ) $.
	e1_syl3anl2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
	p_syl3anl2 $p |- ( ( ( ps /\ ph /\ th ) /\ ta ) -> et ) $= e0_syl3anl2 e1_syl3anl2 f1_syl3anl2 f2_syl3anl2 f3_syl3anl2 a_w3a f4_syl3anl2 f5_syl3anl2 p_ex f0_syl3anl2 f1_syl3anl2 f2_syl3anl2 f3_syl3anl2 f4_syl3anl2 f5_syl3anl2 a_wi p_syl3an2 f1_syl3anl2 f0_syl3anl2 f3_syl3anl2 a_w3a f4_syl3anl2 f5_syl3anl2 p_imp $.
$}

$(A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl3anl3 $f wff ph $.
	f1_syl3anl3 $f wff ps $.
	f2_syl3anl3 $f wff ch $.
	f3_syl3anl3 $f wff th $.
	f4_syl3anl3 $f wff ta $.
	f5_syl3anl3 $f wff et $.
	e0_syl3anl3 $e |- ( ph -> th ) $.
	e1_syl3anl3 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
	p_syl3anl3 $p |- ( ( ( ps /\ ch /\ ph ) /\ ta ) -> et ) $= e0_syl3anl3 f0_syl3anl3 f3_syl3anl3 f1_syl3anl3 f2_syl3anl3 p_3anim3i e1_syl3anl3 f1_syl3anl3 f2_syl3anl3 f0_syl3anl3 a_w3a f1_syl3anl3 f2_syl3anl3 f3_syl3anl3 a_w3a f4_syl3anl3 f5_syl3anl3 p_sylan $.
$}

$(A triple syllogism inference.  (Contributed by NM, 24-Dec-2006.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_syl3anl $f wff ph $.
	f1_syl3anl $f wff ps $.
	f2_syl3anl $f wff ch $.
	f3_syl3anl $f wff th $.
	f4_syl3anl $f wff ta $.
	f5_syl3anl $f wff et $.
	f6_syl3anl $f wff ze $.
	f7_syl3anl $f wff si $.
	e0_syl3anl $e |- ( ph -> ps ) $.
	e1_syl3anl $e |- ( ch -> th ) $.
	e2_syl3anl $e |- ( ta -> et ) $.
	e3_syl3anl $e |- ( ( ( ps /\ th /\ et ) /\ ze ) -> si ) $.
	p_syl3anl $p |- ( ( ( ph /\ ch /\ ta ) /\ ze ) -> si ) $= e0_syl3anl e1_syl3anl e2_syl3anl f0_syl3anl f1_syl3anl f2_syl3anl f3_syl3anl f4_syl3anl f5_syl3anl p_3anim123i e3_syl3anl f0_syl3anl f2_syl3anl f4_syl3anl a_w3a f1_syl3anl f3_syl3anl f5_syl3anl a_w3a f6_syl3anl f7_syl3anl p_sylan $.
$}

$(A syllogism inference.  (Contributed by NM, 31-Jul-2007.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl3anr1 $f wff ph $.
	f1_syl3anr1 $f wff ps $.
	f2_syl3anr1 $f wff ch $.
	f3_syl3anr1 $f wff th $.
	f4_syl3anr1 $f wff ta $.
	f5_syl3anr1 $f wff et $.
	e0_syl3anr1 $e |- ( ph -> ps ) $.
	e1_syl3anr1 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
	p_syl3anr1 $p |- ( ( ch /\ ( ph /\ th /\ ta ) ) -> et ) $= e0_syl3anr1 f0_syl3anr1 f1_syl3anr1 f3_syl3anr1 f4_syl3anr1 p_3anim1i e1_syl3anr1 f0_syl3anr1 f3_syl3anr1 f4_syl3anr1 a_w3a f2_syl3anr1 f1_syl3anr1 f3_syl3anr1 f4_syl3anr1 a_w3a f5_syl3anr1 p_sylan2 $.
$}

$(A syllogism inference.  (Contributed by NM, 1-Aug-2007.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl3anr2 $f wff ph $.
	f1_syl3anr2 $f wff ps $.
	f2_syl3anr2 $f wff ch $.
	f3_syl3anr2 $f wff th $.
	f4_syl3anr2 $f wff ta $.
	f5_syl3anr2 $f wff et $.
	e0_syl3anr2 $e |- ( ph -> th ) $.
	e1_syl3anr2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
	p_syl3anr2 $p |- ( ( ch /\ ( ps /\ ph /\ ta ) ) -> et ) $= e0_syl3anr2 e1_syl3anr2 f2_syl3anr2 f1_syl3anr2 f3_syl3anr2 f4_syl3anr2 a_w3a f5_syl3anr2 p_ancoms f0_syl3anr2 f1_syl3anr2 f3_syl3anr2 f4_syl3anr2 f2_syl3anr2 f5_syl3anr2 p_syl3anl2 f1_syl3anr2 f0_syl3anr2 f4_syl3anr2 a_w3a f2_syl3anr2 f5_syl3anr2 p_ancoms $.
$}

$(A syllogism inference.  (Contributed by NM, 23-Aug-2007.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl3anr3 $f wff ph $.
	f1_syl3anr3 $f wff ps $.
	f2_syl3anr3 $f wff ch $.
	f3_syl3anr3 $f wff th $.
	f4_syl3anr3 $f wff ta $.
	f5_syl3anr3 $f wff et $.
	e0_syl3anr3 $e |- ( ph -> ta ) $.
	e1_syl3anr3 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
	p_syl3anr3 $p |- ( ( ch /\ ( ps /\ th /\ ph ) ) -> et ) $= e0_syl3anr3 f0_syl3anr3 f4_syl3anr3 f1_syl3anr3 f3_syl3anr3 p_3anim3i e1_syl3anr3 f1_syl3anr3 f3_syl3anr3 f0_syl3anr3 a_w3a f2_syl3anr3 f1_syl3anr3 f3_syl3anr3 f4_syl3anr3 a_w3a f5_syl3anr3 p_sylan2 $.
$}

$(Importation inference (undistribute conjunction).  (Contributed by NM,
       14-Aug-1995.) $)

${
	$v ph ps ch th  $.
	f0_3impdi $f wff ph $.
	f1_3impdi $f wff ps $.
	f2_3impdi $f wff ch $.
	f3_3impdi $f wff th $.
	e0_3impdi $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th ) $.
	p_3impdi $p |- ( ( ph /\ ps /\ ch ) -> th ) $= e0_3impdi f0_3impdi f1_3impdi f2_3impdi f3_3impdi p_anandis f0_3impdi f1_3impdi f2_3impdi f3_3impdi p_3impb $.
$}

$(Importation inference (undistribute conjunction).  (Contributed by NM,
       20-Aug-1995.) $)

${
	$v ph ps ch th  $.
	f0_3impdir $f wff ph $.
	f1_3impdir $f wff ps $.
	f2_3impdir $f wff ch $.
	f3_3impdir $f wff th $.
	e0_3impdir $e |- ( ( ( ph /\ ps ) /\ ( ch /\ ps ) ) -> th ) $.
	p_3impdir $p |- ( ( ph /\ ch /\ ps ) -> th ) $= e0_3impdir f0_3impdir f2_3impdir f1_3impdir f3_3impdir p_anandirs f0_3impdir f2_3impdir f1_3impdir f3_3impdir p_3impa $.
$}

$(Inference from idempotent law for conjunction.  (Contributed by NM,
       7-Mar-2008.) $)

${
	$v ph ps ch  $.
	f0_3anidm12 $f wff ph $.
	f1_3anidm12 $f wff ps $.
	f2_3anidm12 $f wff ch $.
	e0_3anidm12 $e |- ( ( ph /\ ph /\ ps ) -> ch ) $.
	p_3anidm12 $p |- ( ( ph /\ ps ) -> ch ) $= e0_3anidm12 f0_3anidm12 f0_3anidm12 f1_3anidm12 f2_3anidm12 p_3expib f0_3anidm12 f1_3anidm12 f2_3anidm12 p_anabsi5 $.
$}

$(Inference from idempotent law for conjunction.  (Contributed by NM,
       7-Mar-2008.) $)

${
	$v ph ps ch  $.
	f0_3anidm13 $f wff ph $.
	f1_3anidm13 $f wff ps $.
	f2_3anidm13 $f wff ch $.
	e0_3anidm13 $e |- ( ( ph /\ ps /\ ph ) -> ch ) $.
	p_3anidm13 $p |- ( ( ph /\ ps ) -> ch ) $= e0_3anidm13 f0_3anidm13 f1_3anidm13 f0_3anidm13 f2_3anidm13 p_3com23 f0_3anidm13 f1_3anidm13 f2_3anidm13 p_3anidm12 $.
$}

$(Inference from idempotent law for conjunction.  (Contributed by NM,
       1-Feb-2007.) $)

${
	$v ph ps ch  $.
	f0_3anidm23 $f wff ph $.
	f1_3anidm23 $f wff ps $.
	f2_3anidm23 $f wff ch $.
	e0_3anidm23 $e |- ( ( ph /\ ps /\ ps ) -> ch ) $.
	p_3anidm23 $p |- ( ( ph /\ ps ) -> ch ) $= e0_3anidm23 f0_3anidm23 f1_3anidm23 f1_3anidm23 f2_3anidm23 p_3expa f0_3anidm23 f1_3anidm23 f2_3anidm23 p_anabss3 $.
$}

$(Infer implication from triple disjunction.  (Contributed by NM,
       26-Sep-2006.) $)

${
	$v ph ps ch  $.
	f0_3ori $f wff ph $.
	f1_3ori $f wff ps $.
	f2_3ori $f wff ch $.
	e0_3ori $e |- ( ph \/ ps \/ ch ) $.
	p_3ori $p |- ( ( -. ph /\ -. ps ) -> ch ) $= f0_3ori f1_3ori p_ioran e0_3ori f0_3ori f1_3ori f2_3ori a_df-3or f0_3ori f1_3ori f2_3ori a_w3o f0_3ori f1_3ori a_wo f2_3ori a_wo p_mpbi f0_3ori f1_3ori a_wo f2_3ori p_ori f0_3ori a_wn f1_3ori a_wn a_wa f0_3ori f1_3ori a_wo a_wn f2_3ori p_sylbir $.
$}

$(Disjunction of 3 antecedents.  (Contributed by NM, 8-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_3jao $f wff ph $.
	f1_3jao $f wff ps $.
	f2_3jao $f wff ch $.
	f3_3jao $f wff th $.
	p_3jao $p |- ( ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) -> ( ( ph \/ ch \/ th ) -> ps ) ) $= f0_3jao f2_3jao f3_3jao a_df-3or f0_3jao f1_3jao f2_3jao p_jao f0_3jao f2_3jao a_wo f1_3jao f3_3jao p_jao f0_3jao f1_3jao a_wi f2_3jao f1_3jao a_wi f0_3jao f2_3jao a_wo f1_3jao a_wi f3_3jao f1_3jao a_wi f0_3jao f2_3jao a_wo f3_3jao a_wo f1_3jao a_wi a_wi p_syl6 f0_3jao f1_3jao a_wi f2_3jao f1_3jao a_wi f3_3jao f1_3jao a_wi f0_3jao f2_3jao a_wo f3_3jao a_wo f1_3jao a_wi p_3imp f0_3jao f2_3jao f3_3jao a_w3o f0_3jao f2_3jao a_wo f3_3jao a_wo f0_3jao f1_3jao a_wi f2_3jao f1_3jao a_wi f3_3jao f1_3jao a_wi a_w3a f1_3jao p_syl5bi $.
$}

$(Disjunction of 3 antecedents.  (Contributed by NM, 13-Sep-2011.) $)

${
	$v ph ps ch th  $.
	f0_3jaob $f wff ph $.
	f1_3jaob $f wff ps $.
	f2_3jaob $f wff ch $.
	f3_3jaob $f wff th $.
	p_3jaob $p |- ( ( ( ph \/ ch \/ th ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ) $= f0_3jaob f2_3jaob f3_3jaob p_3mix1 f0_3jaob f0_3jaob f2_3jaob f3_3jaob a_w3o f1_3jaob p_imim1i f2_3jaob f0_3jaob f3_3jaob p_3mix2 f2_3jaob f0_3jaob f2_3jaob f3_3jaob a_w3o f1_3jaob p_imim1i f3_3jaob f0_3jaob f2_3jaob p_3mix3 f3_3jaob f0_3jaob f2_3jaob f3_3jaob a_w3o f1_3jaob p_imim1i f0_3jaob f2_3jaob f3_3jaob a_w3o f1_3jaob a_wi f0_3jaob f1_3jaob a_wi f2_3jaob f1_3jaob a_wi f3_3jaob f1_3jaob a_wi p_3jca f0_3jaob f1_3jaob f2_3jaob f3_3jaob p_3jao f0_3jaob f2_3jaob f3_3jaob a_w3o f1_3jaob a_wi f0_3jaob f1_3jaob a_wi f2_3jaob f1_3jaob a_wi f3_3jaob f1_3jaob a_wi a_w3a p_impbii $.
$}

$(Disjunction of 3 antecedents (inference).  (Contributed by NM,
       12-Sep-1995.) $)

${
	$v ph ps ch th  $.
	f0_3jaoi $f wff ph $.
	f1_3jaoi $f wff ps $.
	f2_3jaoi $f wff ch $.
	f3_3jaoi $f wff th $.
	e0_3jaoi $e |- ( ph -> ps ) $.
	e1_3jaoi $e |- ( ch -> ps ) $.
	e2_3jaoi $e |- ( th -> ps ) $.
	p_3jaoi $p |- ( ( ph \/ ch \/ th ) -> ps ) $= e0_3jaoi e1_3jaoi e2_3jaoi f0_3jaoi f1_3jaoi a_wi f2_3jaoi f1_3jaoi a_wi f3_3jaoi f1_3jaoi a_wi p_3pm3.2i f0_3jaoi f1_3jaoi f2_3jaoi f3_3jaoi p_3jao f0_3jaoi f1_3jaoi a_wi f2_3jaoi f1_3jaoi a_wi f3_3jaoi f1_3jaoi a_wi a_w3a f0_3jaoi f2_3jaoi f3_3jaoi a_w3o f1_3jaoi a_wi a_ax-mp $.
$}

$(Disjunction of 3 antecedents (deduction).  (Contributed by NM,
       14-Oct-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3jaod $f wff ph $.
	f1_3jaod $f wff ps $.
	f2_3jaod $f wff ch $.
	f3_3jaod $f wff th $.
	f4_3jaod $f wff ta $.
	e0_3jaod $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3jaod $e |- ( ph -> ( th -> ch ) ) $.
	e2_3jaod $e |- ( ph -> ( ta -> ch ) ) $.
	p_3jaod $p |- ( ph -> ( ( ps \/ th \/ ta ) -> ch ) ) $= e0_3jaod e1_3jaod e2_3jaod f1_3jaod f2_3jaod f3_3jaod f4_3jaod p_3jao f0_3jaod f1_3jaod f2_3jaod a_wi f3_3jaod f2_3jaod a_wi f4_3jaod f2_3jaod a_wi f1_3jaod f3_3jaod f4_3jaod a_w3o f2_3jaod a_wi p_syl3anc $.
$}

$(Disjunction of 3 antecedents (inference).  (Contributed by NM,
       14-Oct-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3jaoian $f wff ph $.
	f1_3jaoian $f wff ps $.
	f2_3jaoian $f wff ch $.
	f3_3jaoian $f wff th $.
	f4_3jaoian $f wff ta $.
	e0_3jaoian $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_3jaoian $e |- ( ( th /\ ps ) -> ch ) $.
	e2_3jaoian $e |- ( ( ta /\ ps ) -> ch ) $.
	p_3jaoian $p |- ( ( ( ph \/ th \/ ta ) /\ ps ) -> ch ) $= e0_3jaoian f0_3jaoian f1_3jaoian f2_3jaoian p_ex e1_3jaoian f3_3jaoian f1_3jaoian f2_3jaoian p_ex e2_3jaoian f4_3jaoian f1_3jaoian f2_3jaoian p_ex f0_3jaoian f1_3jaoian f2_3jaoian a_wi f3_3jaoian f4_3jaoian p_3jaoi f0_3jaoian f3_3jaoian f4_3jaoian a_w3o f1_3jaoian f2_3jaoian p_imp $.
$}

$(Disjunction of 3 antecedents (deduction).  (Contributed by NM,
       14-Oct-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_3jaodan $f wff ph $.
	f1_3jaodan $f wff ps $.
	f2_3jaodan $f wff ch $.
	f3_3jaodan $f wff th $.
	f4_3jaodan $f wff ta $.
	e0_3jaodan $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_3jaodan $e |- ( ( ph /\ th ) -> ch ) $.
	e2_3jaodan $e |- ( ( ph /\ ta ) -> ch ) $.
	p_3jaodan $p |- ( ( ph /\ ( ps \/ th \/ ta ) ) -> ch ) $= e0_3jaodan f0_3jaodan f1_3jaodan f2_3jaodan p_ex e1_3jaodan f0_3jaodan f3_3jaodan f2_3jaodan p_ex e2_3jaodan f0_3jaodan f4_3jaodan f2_3jaodan p_ex f0_3jaodan f1_3jaodan f2_3jaodan f3_3jaodan f4_3jaodan p_3jaod f0_3jaodan f1_3jaodan f3_3jaodan f4_3jaodan a_w3o f2_3jaodan p_imp $.
$}

$(Inference conjoining and disjoining the antecedents of three
       implications.  (Contributed by Jeff Hankins, 15-Aug-2009.)  (Proof
       shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_3jaao $f wff ph $.
	f1_3jaao $f wff ps $.
	f2_3jaao $f wff ch $.
	f3_3jaao $f wff th $.
	f4_3jaao $f wff ta $.
	f5_3jaao $f wff et $.
	f6_3jaao $f wff ze $.
	e0_3jaao $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3jaao $e |- ( th -> ( ta -> ch ) ) $.
	e2_3jaao $e |- ( et -> ( ze -> ch ) ) $.
	p_3jaao $p |- ( ( ph /\ th /\ et ) -> ( ( ps \/ ta \/ ze ) -> ch ) ) $= e0_3jaao f0_3jaao f3_3jaao f1_3jaao f2_3jaao a_wi f5_3jaao p_3ad2ant1 e1_3jaao f3_3jaao f0_3jaao f4_3jaao f2_3jaao a_wi f5_3jaao p_3ad2ant2 e2_3jaao f5_3jaao f0_3jaao f6_3jaao f2_3jaao a_wi f3_3jaao p_3ad2ant3 f0_3jaao f3_3jaao f5_3jaao a_w3a f1_3jaao f2_3jaao f4_3jaao f6_3jaao p_3jaod $.
$}

$(Nested syllogism inference conjoining 3 dissimilar antecedents.
       (Contributed by NM, 1-May-1995.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_syl3an9b $f wff ph $.
	f1_syl3an9b $f wff ps $.
	f2_syl3an9b $f wff ch $.
	f3_syl3an9b $f wff th $.
	f4_syl3an9b $f wff ta $.
	f5_syl3an9b $f wff et $.
	f6_syl3an9b $f wff ze $.
	e0_syl3an9b $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_syl3an9b $e |- ( th -> ( ch <-> ta ) ) $.
	e2_syl3an9b $e |- ( et -> ( ta <-> ze ) ) $.
	p_syl3an9b $p |- ( ( ph /\ th /\ et ) -> ( ps <-> ze ) ) $= e0_syl3an9b e1_syl3an9b f0_syl3an9b f1_syl3an9b f2_syl3an9b f3_syl3an9b f4_syl3an9b p_sylan9bb e2_syl3an9b f0_syl3an9b f3_syl3an9b a_wa f1_syl3an9b f4_syl3an9b f5_syl3an9b f6_syl3an9b p_sylan9bb f0_syl3an9b f3_syl3an9b f5_syl3an9b f1_syl3an9b f6_syl3an9b a_wb p_3impa $.
$}

$(Deduction joining 3 equivalences to form equivalence of disjunctions.
       (Contributed by NM, 20-Apr-1994.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_3orbi123d $f wff ph $.
	f1_3orbi123d $f wff ps $.
	f2_3orbi123d $f wff ch $.
	f3_3orbi123d $f wff th $.
	f4_3orbi123d $f wff ta $.
	f5_3orbi123d $f wff et $.
	f6_3orbi123d $f wff ze $.
	e0_3orbi123d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3orbi123d $e |- ( ph -> ( th <-> ta ) ) $.
	e2_3orbi123d $e |- ( ph -> ( et <-> ze ) ) $.
	p_3orbi123d $p |- ( ph -> ( ( ps \/ th \/ et ) <-> ( ch \/ ta \/ ze ) ) ) $= e0_3orbi123d e1_3orbi123d f0_3orbi123d f1_3orbi123d f2_3orbi123d f3_3orbi123d f4_3orbi123d p_orbi12d e2_3orbi123d f0_3orbi123d f1_3orbi123d f3_3orbi123d a_wo f2_3orbi123d f4_3orbi123d a_wo f5_3orbi123d f6_3orbi123d p_orbi12d f1_3orbi123d f3_3orbi123d f5_3orbi123d a_df-3or f2_3orbi123d f4_3orbi123d f6_3orbi123d a_df-3or f0_3orbi123d f1_3orbi123d f3_3orbi123d a_wo f5_3orbi123d a_wo f2_3orbi123d f4_3orbi123d a_wo f6_3orbi123d a_wo f1_3orbi123d f3_3orbi123d f5_3orbi123d a_w3o f2_3orbi123d f4_3orbi123d f6_3orbi123d a_w3o p_3bitr4g $.
$}

$(Deduction joining 3 equivalences to form equivalence of conjunctions.
       (Contributed by NM, 22-Apr-1994.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_3anbi123d $f wff ph $.
	f1_3anbi123d $f wff ps $.
	f2_3anbi123d $f wff ch $.
	f3_3anbi123d $f wff th $.
	f4_3anbi123d $f wff ta $.
	f5_3anbi123d $f wff et $.
	f6_3anbi123d $f wff ze $.
	e0_3anbi123d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3anbi123d $e |- ( ph -> ( th <-> ta ) ) $.
	e2_3anbi123d $e |- ( ph -> ( et <-> ze ) ) $.
	p_3anbi123d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ ze ) ) ) $= e0_3anbi123d e1_3anbi123d f0_3anbi123d f1_3anbi123d f2_3anbi123d f3_3anbi123d f4_3anbi123d p_anbi12d e2_3anbi123d f0_3anbi123d f1_3anbi123d f3_3anbi123d a_wa f2_3anbi123d f4_3anbi123d a_wa f5_3anbi123d f6_3anbi123d p_anbi12d f1_3anbi123d f3_3anbi123d f5_3anbi123d a_df-3an f2_3anbi123d f4_3anbi123d f6_3anbi123d a_df-3an f0_3anbi123d f1_3anbi123d f3_3anbi123d a_wa f5_3anbi123d a_wa f2_3anbi123d f4_3anbi123d a_wa f6_3anbi123d a_wa f1_3anbi123d f3_3anbi123d f5_3anbi123d a_w3a f2_3anbi123d f4_3anbi123d f6_3anbi123d a_w3a p_3bitr4g $.
$}

$(Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)

${
	$v ph ps ch th ta et  $.
	f0_3anbi12d $f wff ph $.
	f1_3anbi12d $f wff ps $.
	f2_3anbi12d $f wff ch $.
	f3_3anbi12d $f wff th $.
	f4_3anbi12d $f wff ta $.
	f5_3anbi12d $f wff et $.
	e0_3anbi12d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3anbi12d $e |- ( ph -> ( th <-> ta ) ) $.
	p_3anbi12d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ et ) ) ) $= e0_3anbi12d e1_3anbi12d f0_3anbi12d f5_3anbi12d p_biidd f0_3anbi12d f1_3anbi12d f2_3anbi12d f3_3anbi12d f4_3anbi12d f5_3anbi12d f5_3anbi12d p_3anbi123d $.
$}

$(Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)

${
	$v ph ps ch th ta et  $.
	f0_3anbi13d $f wff ph $.
	f1_3anbi13d $f wff ps $.
	f2_3anbi13d $f wff ch $.
	f3_3anbi13d $f wff th $.
	f4_3anbi13d $f wff ta $.
	f5_3anbi13d $f wff et $.
	e0_3anbi13d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3anbi13d $e |- ( ph -> ( th <-> ta ) ) $.
	p_3anbi13d $p |- ( ph -> ( ( ps /\ et /\ th ) <-> ( ch /\ et /\ ta ) ) ) $= e0_3anbi13d f0_3anbi13d f5_3anbi13d p_biidd e1_3anbi13d f0_3anbi13d f1_3anbi13d f2_3anbi13d f5_3anbi13d f5_3anbi13d f3_3anbi13d f4_3anbi13d p_3anbi123d $.
$}

$(Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)

${
	$v ph ps ch th ta et  $.
	f0_3anbi23d $f wff ph $.
	f1_3anbi23d $f wff ps $.
	f2_3anbi23d $f wff ch $.
	f3_3anbi23d $f wff th $.
	f4_3anbi23d $f wff ta $.
	f5_3anbi23d $f wff et $.
	e0_3anbi23d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3anbi23d $e |- ( ph -> ( th <-> ta ) ) $.
	p_3anbi23d $p |- ( ph -> ( ( et /\ ps /\ th ) <-> ( et /\ ch /\ ta ) ) ) $= f0_3anbi23d f5_3anbi23d p_biidd e0_3anbi23d e1_3anbi23d f0_3anbi23d f5_3anbi23d f5_3anbi23d f1_3anbi23d f2_3anbi23d f3_3anbi23d f4_3anbi23d p_3anbi123d $.
$}

$(Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3anbi1d $f wff ph $.
	f1_3anbi1d $f wff ps $.
	f2_3anbi1d $f wff ch $.
	f3_3anbi1d $f wff th $.
	f4_3anbi1d $f wff ta $.
	e0_3anbi1d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_3anbi1d $p |- ( ph -> ( ( ps /\ th /\ ta ) <-> ( ch /\ th /\ ta ) ) ) $= e0_3anbi1d f0_3anbi1d f3_3anbi1d p_biidd f0_3anbi1d f1_3anbi1d f2_3anbi1d f3_3anbi1d f3_3anbi1d f4_3anbi1d p_3anbi12d $.
$}

$(Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3anbi2d $f wff ph $.
	f1_3anbi2d $f wff ps $.
	f2_3anbi2d $f wff ch $.
	f3_3anbi2d $f wff th $.
	f4_3anbi2d $f wff ta $.
	e0_3anbi2d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_3anbi2d $p |- ( ph -> ( ( th /\ ps /\ ta ) <-> ( th /\ ch /\ ta ) ) ) $= f0_3anbi2d f3_3anbi2d p_biidd e0_3anbi2d f0_3anbi2d f3_3anbi2d f3_3anbi2d f1_3anbi2d f2_3anbi2d f4_3anbi2d p_3anbi12d $.
$}

$(Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3anbi3d $f wff ph $.
	f1_3anbi3d $f wff ps $.
	f2_3anbi3d $f wff ch $.
	f3_3anbi3d $f wff th $.
	f4_3anbi3d $f wff ta $.
	e0_3anbi3d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_3anbi3d $p |- ( ph -> ( ( th /\ ta /\ ps ) <-> ( th /\ ta /\ ch ) ) ) $= f0_3anbi3d f3_3anbi3d p_biidd e0_3anbi3d f0_3anbi3d f3_3anbi3d f3_3anbi3d f1_3anbi3d f2_3anbi3d f4_3anbi3d p_3anbi13d $.
$}

$(Deduction joining 3 implications to form implication of conjunctions.
       (Contributed by NM, 24-Feb-2005.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_3anim123d $f wff ph $.
	f1_3anim123d $f wff ps $.
	f2_3anim123d $f wff ch $.
	f3_3anim123d $f wff th $.
	f4_3anim123d $f wff ta $.
	f5_3anim123d $f wff et $.
	f6_3anim123d $f wff ze $.
	e0_3anim123d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3anim123d $e |- ( ph -> ( th -> ta ) ) $.
	e2_3anim123d $e |- ( ph -> ( et -> ze ) ) $.
	p_3anim123d $p |- ( ph -> ( ( ps /\ th /\ et ) -> ( ch /\ ta /\ ze ) ) ) $= e0_3anim123d e1_3anim123d f0_3anim123d f1_3anim123d f2_3anim123d f3_3anim123d f4_3anim123d p_anim12d e2_3anim123d f0_3anim123d f1_3anim123d f3_3anim123d a_wa f2_3anim123d f4_3anim123d a_wa f5_3anim123d f6_3anim123d p_anim12d f1_3anim123d f3_3anim123d f5_3anim123d a_df-3an f2_3anim123d f4_3anim123d f6_3anim123d a_df-3an f0_3anim123d f1_3anim123d f3_3anim123d a_wa f5_3anim123d a_wa f2_3anim123d f4_3anim123d a_wa f6_3anim123d a_wa f1_3anim123d f3_3anim123d f5_3anim123d a_w3a f2_3anim123d f4_3anim123d f6_3anim123d a_w3a p_3imtr4g $.
$}

$(Deduction joining 3 implications to form implication of disjunctions.
       (Contributed by NM, 4-Apr-1997.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_3orim123d $f wff ph $.
	f1_3orim123d $f wff ps $.
	f2_3orim123d $f wff ch $.
	f3_3orim123d $f wff th $.
	f4_3orim123d $f wff ta $.
	f5_3orim123d $f wff et $.
	f6_3orim123d $f wff ze $.
	e0_3orim123d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3orim123d $e |- ( ph -> ( th -> ta ) ) $.
	e2_3orim123d $e |- ( ph -> ( et -> ze ) ) $.
	p_3orim123d $p |- ( ph -> ( ( ps \/ th \/ et ) -> ( ch \/ ta \/ ze ) ) ) $= e0_3orim123d e1_3orim123d f0_3orim123d f1_3orim123d f2_3orim123d f3_3orim123d f4_3orim123d p_orim12d e2_3orim123d f0_3orim123d f1_3orim123d f3_3orim123d a_wo f2_3orim123d f4_3orim123d a_wo f5_3orim123d f6_3orim123d p_orim12d f1_3orim123d f3_3orim123d f5_3orim123d a_df-3or f2_3orim123d f4_3orim123d f6_3orim123d a_df-3or f0_3orim123d f1_3orim123d f3_3orim123d a_wo f5_3orim123d a_wo f2_3orim123d f4_3orim123d a_wo f6_3orim123d a_wo f1_3orim123d f3_3orim123d f5_3orim123d a_w3o f2_3orim123d f4_3orim123d f6_3orim123d a_w3o p_3imtr4g $.
$}

$(Rearrangement of 6 conjuncts.  (Contributed by NM, 13-Mar-1995.) $)

${
	$v ph ps ch th ta et  $.
	f0_an6 $f wff ph $.
	f1_an6 $f wff ps $.
	f2_an6 $f wff ch $.
	f3_an6 $f wff th $.
	f4_an6 $f wff ta $.
	f5_an6 $f wff et $.
	p_an6 $p |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) ) <-> ( ( ph /\ th ) /\ ( ps /\ ta ) /\ ( ch /\ et ) ) ) $= f0_an6 f1_an6 a_wa f2_an6 f3_an6 f4_an6 a_wa f5_an6 p_an4 f0_an6 f1_an6 f3_an6 f4_an6 p_an4 f0_an6 f1_an6 a_wa f3_an6 f4_an6 a_wa a_wa f0_an6 f3_an6 a_wa f1_an6 f4_an6 a_wa a_wa f2_an6 f5_an6 a_wa p_anbi1i f0_an6 f1_an6 a_wa f2_an6 a_wa f3_an6 f4_an6 a_wa f5_an6 a_wa a_wa f0_an6 f1_an6 a_wa f3_an6 f4_an6 a_wa a_wa f2_an6 f5_an6 a_wa a_wa f0_an6 f3_an6 a_wa f1_an6 f4_an6 a_wa a_wa f2_an6 f5_an6 a_wa a_wa p_bitri f0_an6 f1_an6 f2_an6 a_df-3an f3_an6 f4_an6 f5_an6 a_df-3an f0_an6 f1_an6 f2_an6 a_w3a f0_an6 f1_an6 a_wa f2_an6 a_wa f3_an6 f4_an6 f5_an6 a_w3a f3_an6 f4_an6 a_wa f5_an6 a_wa p_anbi12i f0_an6 f3_an6 a_wa f1_an6 f4_an6 a_wa f2_an6 f5_an6 a_wa a_df-3an f0_an6 f1_an6 a_wa f2_an6 a_wa f3_an6 f4_an6 a_wa f5_an6 a_wa a_wa f0_an6 f3_an6 a_wa f1_an6 f4_an6 a_wa a_wa f2_an6 f5_an6 a_wa a_wa f0_an6 f1_an6 f2_an6 a_w3a f3_an6 f4_an6 f5_an6 a_w3a a_wa f0_an6 f3_an6 a_wa f1_an6 f4_an6 a_wa f2_an6 f5_an6 a_wa a_w3a p_3bitr4i $.
$}

$(Analog of ~ an4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps ch th ta et  $.
	f0_3an6 $f wff ph $.
	f1_3an6 $f wff ps $.
	f2_3an6 $f wff ch $.
	f3_3an6 $f wff th $.
	f4_3an6 $f wff ta $.
	f5_3an6 $f wff et $.
	p_3an6 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) /\ ( ta /\ et ) ) <-> ( ( ph /\ ch /\ ta ) /\ ( ps /\ th /\ et ) ) ) $= f0_3an6 f2_3an6 f4_3an6 f1_3an6 f3_3an6 f5_3an6 p_an6 f0_3an6 f2_3an6 f4_3an6 a_w3a f1_3an6 f3_3an6 f5_3an6 a_w3a a_wa f0_3an6 f1_3an6 a_wa f2_3an6 f3_3an6 a_wa f4_3an6 f5_3an6 a_wa a_w3a p_bicomi $.
$}

$(Analog of ~ or4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.) $)

${
	$v ph ps ch th ta et  $.
	f0_3or6 $f wff ph $.
	f1_3or6 $f wff ps $.
	f2_3or6 $f wff ch $.
	f3_3or6 $f wff th $.
	f4_3or6 $f wff ta $.
	f5_3or6 $f wff et $.
	p_3or6 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) \/ ( ta \/ et ) ) <-> ( ( ph \/ ch \/ ta ) \/ ( ps \/ th \/ et ) ) ) $= f0_3or6 f2_3or6 a_wo f4_3or6 f1_3or6 f3_3or6 a_wo f5_3or6 p_or4 f0_3or6 f2_3or6 f1_3or6 f3_3or6 p_or4 f0_3or6 f2_3or6 a_wo f1_3or6 f3_3or6 a_wo a_wo f0_3or6 f1_3or6 a_wo f2_3or6 f3_3or6 a_wo a_wo f4_3or6 f5_3or6 a_wo p_orbi1i f0_3or6 f2_3or6 a_wo f4_3or6 a_wo f1_3or6 f3_3or6 a_wo f5_3or6 a_wo a_wo f0_3or6 f2_3or6 a_wo f1_3or6 f3_3or6 a_wo a_wo f4_3or6 f5_3or6 a_wo a_wo f0_3or6 f1_3or6 a_wo f2_3or6 f3_3or6 a_wo a_wo f4_3or6 f5_3or6 a_wo a_wo p_bitr2i f0_3or6 f1_3or6 a_wo f2_3or6 f3_3or6 a_wo f4_3or6 f5_3or6 a_wo a_df-3or f0_3or6 f2_3or6 f4_3or6 a_df-3or f1_3or6 f3_3or6 f5_3or6 a_df-3or f0_3or6 f2_3or6 f4_3or6 a_w3o f0_3or6 f2_3or6 a_wo f4_3or6 a_wo f1_3or6 f3_3or6 f5_3or6 a_w3o f1_3or6 f3_3or6 a_wo f5_3or6 a_wo p_orbi12i f0_3or6 f1_3or6 a_wo f2_3or6 f3_3or6 a_wo a_wo f4_3or6 f5_3or6 a_wo a_wo f0_3or6 f2_3or6 a_wo f4_3or6 a_wo f1_3or6 f3_3or6 a_wo f5_3or6 a_wo a_wo f0_3or6 f1_3or6 a_wo f2_3or6 f3_3or6 a_wo f4_3or6 f5_3or6 a_wo a_w3o f0_3or6 f2_3or6 f4_3or6 a_w3o f1_3or6 f3_3or6 f5_3or6 a_w3o a_wo p_3bitr4i $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)

${
	$v ph ps ch th  $.
	f0_mp3an1 $f wff ph $.
	f1_mp3an1 $f wff ps $.
	f2_mp3an1 $f wff ch $.
	f3_mp3an1 $f wff th $.
	e0_mp3an1 $e |- ph $.
	e1_mp3an1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mp3an1 $p |- ( ( ps /\ ch ) -> th ) $= e0_mp3an1 e1_mp3an1 f0_mp3an1 f1_mp3an1 f2_mp3an1 f3_mp3an1 p_3expb f0_mp3an1 f1_mp3an1 f2_mp3an1 a_wa f3_mp3an1 p_mpan $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)

${
	$v ph ps ch th  $.
	f0_mp3an2 $f wff ph $.
	f1_mp3an2 $f wff ps $.
	f2_mp3an2 $f wff ch $.
	f3_mp3an2 $f wff th $.
	e0_mp3an2 $e |- ps $.
	e1_mp3an2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mp3an2 $p |- ( ( ph /\ ch ) -> th ) $= e0_mp3an2 e1_mp3an2 f0_mp3an2 f1_mp3an2 f2_mp3an2 f3_mp3an2 p_3expa f0_mp3an2 f1_mp3an2 f2_mp3an2 f3_mp3an2 p_mpanl2 $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)

${
	$v ph ps ch th  $.
	f0_mp3an3 $f wff ph $.
	f1_mp3an3 $f wff ps $.
	f2_mp3an3 $f wff ch $.
	f3_mp3an3 $f wff th $.
	e0_mp3an3 $e |- ch $.
	e1_mp3an3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mp3an3 $p |- ( ( ph /\ ps ) -> th ) $= e0_mp3an3 e1_mp3an3 f0_mp3an3 f1_mp3an3 f2_mp3an3 f3_mp3an3 p_3expia f0_mp3an3 f1_mp3an3 a_wa f2_mp3an3 f3_mp3an3 p_mpi $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       13-Jul-2005.) $)

${
	$v ph ps ch th  $.
	f0_mp3an12 $f wff ph $.
	f1_mp3an12 $f wff ps $.
	f2_mp3an12 $f wff ch $.
	f3_mp3an12 $f wff th $.
	e0_mp3an12 $e |- ph $.
	e1_mp3an12 $e |- ps $.
	e2_mp3an12 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mp3an12 $p |- ( ch -> th ) $= e1_mp3an12 e0_mp3an12 e2_mp3an12 f0_mp3an12 f1_mp3an12 f2_mp3an12 f3_mp3an12 p_mp3an1 f1_mp3an12 f2_mp3an12 f3_mp3an12 p_mpan $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       14-Jul-2005.) $)

${
	$v ph ps ch th  $.
	f0_mp3an13 $f wff ph $.
	f1_mp3an13 $f wff ps $.
	f2_mp3an13 $f wff ch $.
	f3_mp3an13 $f wff th $.
	e0_mp3an13 $e |- ph $.
	e1_mp3an13 $e |- ch $.
	e2_mp3an13 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mp3an13 $p |- ( ps -> th ) $= e0_mp3an13 e1_mp3an13 e2_mp3an13 f0_mp3an13 f1_mp3an13 f2_mp3an13 f3_mp3an13 p_mp3an3 f0_mp3an13 f1_mp3an13 f3_mp3an13 p_mpan $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       14-Jul-2005.) $)

${
	$v ph ps ch th  $.
	f0_mp3an23 $f wff ph $.
	f1_mp3an23 $f wff ps $.
	f2_mp3an23 $f wff ch $.
	f3_mp3an23 $f wff th $.
	e0_mp3an23 $e |- ps $.
	e1_mp3an23 $e |- ch $.
	e2_mp3an23 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mp3an23 $p |- ( ph -> th ) $= e0_mp3an23 e1_mp3an23 e2_mp3an23 f0_mp3an23 f1_mp3an23 f2_mp3an23 f3_mp3an23 p_mp3an3 f0_mp3an23 f1_mp3an23 f3_mp3an23 p_mpan2 $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 5-Jul-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_mp3an1i $f wff ph $.
	f1_mp3an1i $f wff ps $.
	f2_mp3an1i $f wff ch $.
	f3_mp3an1i $f wff th $.
	f4_mp3an1i $f wff ta $.
	e0_mp3an1i $e |- ps $.
	e1_mp3an1i $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
	p_mp3an1i $p |- ( ph -> ( ( ch /\ th ) -> ta ) ) $= e0_mp3an1i e1_mp3an1i f0_mp3an1i f1_mp3an1i f2_mp3an1i f3_mp3an1i a_w3a f4_mp3an1i p_com12 f1_mp3an1i f2_mp3an1i f3_mp3an1i f0_mp3an1i f4_mp3an1i a_wi p_mp3an1 f2_mp3an1i f3_mp3an1i a_wa f0_mp3an1i f4_mp3an1i p_com12 $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_mp3anl1 $f wff ph $.
	f1_mp3anl1 $f wff ps $.
	f2_mp3anl1 $f wff ch $.
	f3_mp3anl1 $f wff th $.
	f4_mp3anl1 $f wff ta $.
	e0_mp3anl1 $e |- ph $.
	e1_mp3anl1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	p_mp3anl1 $p |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $= e0_mp3anl1 e1_mp3anl1 f0_mp3anl1 f1_mp3anl1 f2_mp3anl1 a_w3a f3_mp3anl1 f4_mp3anl1 p_ex f0_mp3anl1 f1_mp3anl1 f2_mp3anl1 f3_mp3anl1 f4_mp3anl1 a_wi p_mp3an1 f1_mp3anl1 f2_mp3anl1 a_wa f3_mp3anl1 f4_mp3anl1 p_imp $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_mp3anl2 $f wff ph $.
	f1_mp3anl2 $f wff ps $.
	f2_mp3anl2 $f wff ch $.
	f3_mp3anl2 $f wff th $.
	f4_mp3anl2 $f wff ta $.
	e0_mp3anl2 $e |- ps $.
	e1_mp3anl2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	p_mp3anl2 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $= e0_mp3anl2 e1_mp3anl2 f0_mp3anl2 f1_mp3anl2 f2_mp3anl2 a_w3a f3_mp3anl2 f4_mp3anl2 p_ex f0_mp3anl2 f1_mp3anl2 f2_mp3anl2 f3_mp3anl2 f4_mp3anl2 a_wi p_mp3an2 f0_mp3anl2 f2_mp3anl2 a_wa f3_mp3anl2 f4_mp3anl2 p_imp $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_mp3anl3 $f wff ph $.
	f1_mp3anl3 $f wff ps $.
	f2_mp3anl3 $f wff ch $.
	f3_mp3anl3 $f wff th $.
	f4_mp3anl3 $f wff ta $.
	e0_mp3anl3 $e |- ch $.
	e1_mp3anl3 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	p_mp3anl3 $p |- ( ( ( ph /\ ps ) /\ th ) -> ta ) $= e0_mp3anl3 e1_mp3anl3 f0_mp3anl3 f1_mp3anl3 f2_mp3anl3 a_w3a f3_mp3anl3 f4_mp3anl3 p_ex f0_mp3anl3 f1_mp3anl3 f2_mp3anl3 f3_mp3anl3 f4_mp3anl3 a_wi p_mp3an3 f0_mp3anl3 f1_mp3anl3 a_wa f3_mp3anl3 f4_mp3anl3 p_imp $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 4-Nov-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_mp3anr1 $f wff ph $.
	f1_mp3anr1 $f wff ps $.
	f2_mp3anr1 $f wff ch $.
	f3_mp3anr1 $f wff th $.
	f4_mp3anr1 $f wff ta $.
	e0_mp3anr1 $e |- ps $.
	e1_mp3anr1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	p_mp3anr1 $p |- ( ( ph /\ ( ch /\ th ) ) -> ta ) $= e0_mp3anr1 e1_mp3anr1 f0_mp3anr1 f1_mp3anr1 f2_mp3anr1 f3_mp3anr1 a_w3a f4_mp3anr1 p_ancoms f1_mp3anr1 f2_mp3anr1 f3_mp3anr1 f0_mp3anr1 f4_mp3anr1 p_mp3anl1 f2_mp3anr1 f3_mp3anr1 a_wa f0_mp3anr1 f4_mp3anr1 p_ancoms $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       24-Nov-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_mp3anr2 $f wff ph $.
	f1_mp3anr2 $f wff ps $.
	f2_mp3anr2 $f wff ch $.
	f3_mp3anr2 $f wff th $.
	f4_mp3anr2 $f wff ta $.
	e0_mp3anr2 $e |- ch $.
	e1_mp3anr2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	p_mp3anr2 $p |- ( ( ph /\ ( ps /\ th ) ) -> ta ) $= e0_mp3anr2 e1_mp3anr2 f0_mp3anr2 f1_mp3anr2 f2_mp3anr2 f3_mp3anr2 a_w3a f4_mp3anr2 p_ancoms f1_mp3anr2 f2_mp3anr2 f3_mp3anr2 f0_mp3anr2 f4_mp3anr2 p_mp3anl2 f1_mp3anr2 f3_mp3anr2 a_wa f0_mp3anr2 f4_mp3anr2 p_ancoms $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       19-Oct-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_mp3anr3 $f wff ph $.
	f1_mp3anr3 $f wff ps $.
	f2_mp3anr3 $f wff ch $.
	f3_mp3anr3 $f wff th $.
	f4_mp3anr3 $f wff ta $.
	e0_mp3anr3 $e |- th $.
	e1_mp3anr3 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	p_mp3anr3 $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $= e0_mp3anr3 e1_mp3anr3 f0_mp3anr3 f1_mp3anr3 f2_mp3anr3 f3_mp3anr3 a_w3a f4_mp3anr3 p_ancoms f1_mp3anr3 f2_mp3anr3 f3_mp3anr3 f0_mp3anr3 f4_mp3anr3 p_mp3anl3 f1_mp3anr3 f2_mp3anr3 a_wa f0_mp3anr3 f4_mp3anr3 p_ancoms $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       14-May-1999.) $)

${
	$v ph ps ch th  $.
	f0_mp3an $f wff ph $.
	f1_mp3an $f wff ps $.
	f2_mp3an $f wff ch $.
	f3_mp3an $f wff th $.
	e0_mp3an $e |- ph $.
	e1_mp3an $e |- ps $.
	e2_mp3an $e |- ch $.
	e3_mp3an $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mp3an $p |- th $= e1_mp3an e2_mp3an e0_mp3an e3_mp3an f0_mp3an f1_mp3an f2_mp3an f3_mp3an p_mp3an1 f1_mp3an f2_mp3an f3_mp3an p_mp2an $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 8-Nov-2007.) $)

${
	$v ph ps ch th  $.
	f0_mpd3an3 $f wff ph $.
	f1_mpd3an3 $f wff ps $.
	f2_mpd3an3 $f wff ch $.
	f3_mpd3an3 $f wff th $.
	e0_mpd3an3 $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_mpd3an3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mpd3an3 $p |- ( ( ph /\ ps ) -> th ) $= e0_mpd3an3 e1_mpd3an3 f0_mpd3an3 f1_mpd3an3 f2_mpd3an3 f3_mpd3an3 p_3expa f0_mpd3an3 f1_mpd3an3 a_wa f2_mpd3an3 f3_mpd3an3 p_mpdan $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 4-Dec-2006.) $)

${
	$v ph ps ch th  $.
	f0_mpd3an23 $f wff ph $.
	f1_mpd3an23 $f wff ps $.
	f2_mpd3an23 $f wff ch $.
	f3_mpd3an23 $f wff th $.
	e0_mpd3an23 $e |- ( ph -> ps ) $.
	e1_mpd3an23 $e |- ( ph -> ch ) $.
	e2_mpd3an23 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_mpd3an23 $p |- ( ph -> th ) $= f0_mpd3an23 p_id e0_mpd3an23 e1_mpd3an23 e2_mpd3an23 f0_mpd3an23 f0_mpd3an23 f1_mpd3an23 f2_mpd3an23 f3_mpd3an23 p_syl3anc $.
$}

$(A deduction based on modus ponens.  (Contributed by Mario Carneiro,
       24-Dec-2016.) $)

${
	$v ph ps ch th ta  $.
	f0_mp3and $f wff ph $.
	f1_mp3and $f wff ps $.
	f2_mp3and $f wff ch $.
	f3_mp3and $f wff th $.
	f4_mp3and $f wff ta $.
	e0_mp3and $e |- ( ph -> ps ) $.
	e1_mp3and $e |- ( ph -> ch ) $.
	e2_mp3and $e |- ( ph -> th ) $.
	e3_mp3and $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
	p_mp3and $p |- ( ph -> ta ) $= e0_mp3and e1_mp3and e2_mp3and f0_mp3and f1_mp3and f2_mp3and f3_mp3and p_3jca e3_mp3and f0_mp3and f1_mp3and f2_mp3and f3_mp3and a_w3a f4_mp3and p_mpd $.
$}

$(Infer implication from a logical equivalence.  Similar to ~ biimpa .
       (Contributed by NM, 4-Sep-2005.) $)

${
	$v ph ps ch th  $.
	f0_biimp3a $f wff ph $.
	f1_biimp3a $f wff ps $.
	f2_biimp3a $f wff ch $.
	f3_biimp3a $f wff th $.
	e0_biimp3a $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	p_biimp3a $p |- ( ( ph /\ ps /\ ch ) -> th ) $= e0_biimp3a f0_biimp3a f1_biimp3a a_wa f2_biimp3a f3_biimp3a p_biimpa f0_biimp3a f1_biimp3a f2_biimp3a f3_biimp3a p_3impa $.
$}

$(Infer implication from a logical equivalence.  Similar to ~ biimpar .
       (Contributed by NM, 2-Jan-2009.) $)

${
	$v ph ps ch th  $.
	f0_biimp3ar $f wff ph $.
	f1_biimp3ar $f wff ps $.
	f2_biimp3ar $f wff ch $.
	f3_biimp3ar $f wff th $.
	e0_biimp3ar $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	p_biimp3ar $p |- ( ( ph /\ ps /\ th ) -> ch ) $= e0_biimp3ar f0_biimp3ar f1_biimp3ar f2_biimp3ar f3_biimp3ar p_exbiri f0_biimp3ar f1_biimp3ar f3_biimp3ar f2_biimp3ar p_3imp $.
$}

$(Inference that undistributes a triple conjunction in the antecedent.
       (Contributed by NM, 18-Apr-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_3anandis $f wff ph $.
	f1_3anandis $f wff ps $.
	f2_3anandis $f wff ch $.
	f3_3anandis $f wff th $.
	f4_3anandis $f wff ta $.
	e0_3anandis $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) ) -> ta ) $.
	p_3anandis $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $= f0_3anandis f1_3anandis f2_3anandis f3_3anandis a_w3a p_simpl f0_3anandis f1_3anandis f2_3anandis f3_3anandis p_simpr1 f0_3anandis f1_3anandis f2_3anandis f3_3anandis a_w3a p_simpl f0_3anandis f1_3anandis f2_3anandis f3_3anandis p_simpr2 f0_3anandis f1_3anandis f2_3anandis f3_3anandis a_w3a p_simpl f0_3anandis f1_3anandis f2_3anandis f3_3anandis p_simpr3 e0_3anandis f0_3anandis f1_3anandis f2_3anandis f3_3anandis a_w3a a_wa f0_3anandis f1_3anandis f0_3anandis f2_3anandis f0_3anandis f3_3anandis f4_3anandis p_syl222anc $.
$}

$(Inference that undistributes a triple conjunction in the antecedent.
       (Contributed by NM, 25-Jul-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3anandirs $f wff ph $.
	f1_3anandirs $f wff ps $.
	f2_3anandirs $f wff ch $.
	f3_3anandirs $f wff th $.
	f4_3anandirs $f wff ta $.
	e0_3anandirs $e |- ( ( ( ph /\ th ) /\ ( ps /\ th ) /\ ( ch /\ th ) ) -> ta ) $.
	p_3anandirs $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $= f0_3anandirs f1_3anandirs f2_3anandirs f3_3anandirs p_simpl1 f0_3anandirs f1_3anandirs f2_3anandirs a_w3a f3_3anandirs p_simpr f0_3anandirs f1_3anandirs f2_3anandirs f3_3anandirs p_simpl2 f0_3anandirs f1_3anandirs f2_3anandirs a_w3a f3_3anandirs p_simpr f0_3anandirs f1_3anandirs f2_3anandirs f3_3anandirs p_simpl3 f0_3anandirs f1_3anandirs f2_3anandirs a_w3a f3_3anandirs p_simpr e0_3anandirs f0_3anandirs f1_3anandirs f2_3anandirs a_w3a f3_3anandirs a_wa f0_3anandirs f3_3anandirs f1_3anandirs f3_3anandirs f2_3anandirs f3_3anandirs f4_3anandirs p_syl222anc $.
$}

$(Deduction for elimination by cases.  (Contributed by NM,
       22-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_ecase23d $f wff ph $.
	f1_ecase23d $f wff ps $.
	f2_ecase23d $f wff ch $.
	f3_ecase23d $f wff th $.
	e0_ecase23d $e |- ( ph -> -. ch ) $.
	e1_ecase23d $e |- ( ph -> -. th ) $.
	e2_ecase23d $e |- ( ph -> ( ps \/ ch \/ th ) ) $.
	p_ecase23d $p |- ( ph -> ps ) $= e0_ecase23d e1_ecase23d f2_ecase23d f3_ecase23d p_ioran f0_ecase23d f2_ecase23d a_wn f3_ecase23d a_wn f2_ecase23d f3_ecase23d a_wo a_wn p_sylanbrc e2_ecase23d f1_ecase23d f2_ecase23d f3_ecase23d p_3orass f0_ecase23d f1_ecase23d f2_ecase23d f3_ecase23d a_w3o f1_ecase23d f2_ecase23d f3_ecase23d a_wo a_wo p_sylib f0_ecase23d f1_ecase23d f2_ecase23d f3_ecase23d a_wo p_ord f0_ecase23d f1_ecase23d f2_ecase23d f3_ecase23d a_wo p_mt3d $.
$}

$(Inference for elimination by cases.  (Contributed by NM,
       13-Jul-2005.) $)

${
	$v ph ps ch th  $.
	f0_3ecase $f wff ph $.
	f1_3ecase $f wff ps $.
	f2_3ecase $f wff ch $.
	f3_3ecase $f wff th $.
	e0_3ecase $e |- ( -. ph -> th ) $.
	e1_3ecase $e |- ( -. ps -> th ) $.
	e2_3ecase $e |- ( -. ch -> th ) $.
	e3_3ecase $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	p_3ecase $p |- th $= e3_3ecase f0_3ecase f1_3ecase f2_3ecase f3_3ecase p_3exp e0_3ecase f0_3ecase a_wn f3_3ecase f2_3ecase p_a1d f0_3ecase a_wn f2_3ecase f3_3ecase a_wi f1_3ecase p_a1d f0_3ecase f1_3ecase f2_3ecase f3_3ecase a_wi a_wi p_pm2.61i e1_3ecase e2_3ecase f1_3ecase f2_3ecase f3_3ecase p_pm2.61nii $.
$}


