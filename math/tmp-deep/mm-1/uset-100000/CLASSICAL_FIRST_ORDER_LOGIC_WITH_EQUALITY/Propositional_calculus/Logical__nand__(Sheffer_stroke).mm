$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Abbreviated_conjunction_and_disjunction_of_three_wff_s.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'nand' (Sheffer stroke)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare connective for alternative denial ('nand'). $)

$c -/\ $.

$(Overlined 'wedge' (read:  'nand') $)

$(Extend wff definition to include alternative denial ('nand'). $)

${
	$v ph ps  $.
	f0_wnan $f wff ph $.
	f1_wnan $f wff ps $.
	a_wnan $a wff ( ph -/\ ps ) $.
$}

$(Define incompatibility, or alternative denial ('not-and' or 'nand').  This
     is also called the Sheffer stroke, represented by a vertical bar, but we
     use a different symbol to avoid ambiguity with other uses of the vertical
     bar.  In the second edition of Principia Mathematica (1927), Russell and
     Whitehead used the Sheffer stroke and suggested it as a replacement for
     the "or" and "not" operations of the first edition.  However, in practice,
     "or" and "not" are more widely used.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. -/\ T. ) <-> F. ) `
     ( ~ trunantru ), ` ( ( T. -/\ F. ) <-> T. ) ` ( ~ trunanfal ),
     ` ( ( F. -/\ T. ) <-> T. ) ` ( ~ falnantru ), and
     ` ( ( F. -/\ F. ) <-> T. ) ` ( ~ falnanfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` \/_ `
     ( ~ df-xor ) .  (Contributed by Jeff Hoffman, 19-Nov-2007.) $)

${
	$v ph ps  $.
	f0_df-nan $f wff ph $.
	f1_df-nan $f wff ps $.
	a_df-nan $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.
$}

$(Write 'and' in terms of 'nand'.  (Contributed by Mario Carneiro,
     9-May-2015.) $)

${
	$v ph ps  $.
	f0_nanan $f wff ph $.
	f1_nanan $f wff ps $.
	p_nanan $p |- ( ( ph /\ ps ) <-> -. ( ph -/\ ps ) ) $= f0_nanan f1_nanan a_df-nan f0_nanan f1_nanan a_wnan f0_nanan f1_nanan a_wa p_con2bii $.
$}

$(The 'nand' operator commutes.  (Contributed by Mario Carneiro,
     9-May-2015.) $)

${
	$v ph ps  $.
	f0_nancom $f wff ph $.
	f1_nancom $f wff ps $.
	p_nancom $p |- ( ( ph -/\ ps ) <-> ( ps -/\ ph ) ) $= f0_nancom f1_nancom p_ancom f0_nancom f1_nancom a_wa f1_nancom f0_nancom a_wa p_notbii f0_nancom f1_nancom a_df-nan f1_nancom f0_nancom a_df-nan f0_nancom f1_nancom a_wa a_wn f1_nancom f0_nancom a_wa a_wn f0_nancom f1_nancom a_wnan f1_nancom f0_nancom a_wnan p_3bitr4i $.
$}

$(Lemma for handling nested 'nand's.  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)

${
	$v ph ps ch  $.
	f0_nannan $f wff ph $.
	f1_nannan $f wff ps $.
	f2_nannan $f wff ch $.
	p_nannan $p |- ( ( ph -/\ ( ch -/\ ps ) ) <-> ( ph -> ( ch /\ ps ) ) ) $= f0_nannan f2_nannan f1_nannan a_wnan a_df-nan f2_nannan f1_nannan a_df-nan f2_nannan f1_nannan a_wnan f2_nannan f1_nannan a_wa a_wn f0_nannan p_anbi2i f0_nannan f2_nannan f1_nannan a_wnan a_wnan f0_nannan f2_nannan f1_nannan a_wnan a_wa f0_nannan f2_nannan f1_nannan a_wa a_wn a_wa p_xchbinx f0_nannan f2_nannan f1_nannan a_wa p_iman f0_nannan f2_nannan f1_nannan a_wnan a_wnan f0_nannan f2_nannan f1_nannan a_wa a_wn a_wa a_wn f0_nannan f2_nannan f1_nannan a_wa a_wi p_bitr4i $.
$}

$(Show equivalence between implication and the Nicod version.  To derive
     ~ nic-dfim , apply ~ nanbi .  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)

${
	$v ph ps  $.
	f0_nanim $f wff ph $.
	f1_nanim $f wff ps $.
	p_nanim $p |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) ) $= f0_nanim f1_nanim f1_nanim p_nannan f0_nanim f1_nanim p_anidmdbi f0_nanim f1_nanim f1_nanim a_wnan a_wnan f0_nanim f1_nanim f1_nanim a_wa a_wi f0_nanim f1_nanim a_wi p_bitr2i $.
$}

$(Show equivalence between negation and the Nicod version.  To derive
     ~ nic-dfneg , apply ~ nanbi .  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)

${
	$v ps  $.
	f0_nannot $f wff ps $.
	p_nannot $p |- ( -. ps <-> ( ps -/\ ps ) ) $= f0_nannot f0_nannot a_df-nan f0_nannot p_anidm f0_nannot f0_nannot a_wnan f0_nannot f0_nannot a_wa f0_nannot p_xchbinx f0_nannot f0_nannot a_wnan f0_nannot a_wn p_bicomi $.
$}

$(Show equivalence between the bidirectional and the Nicod version.
     (Contributed by Jeff Hoffman, 19-Nov-2007.) $)

${
	$v ph ps  $.
	f0_nanbi $f wff ph $.
	f1_nanbi $f wff ps $.
	p_nanbi $p |- ( ( ph <-> ps ) <-> ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) $= f0_nanbi f1_nanbi a_wa f0_nanbi a_wn f1_nanbi a_wn a_wa p_pm4.57 f0_nanbi f1_nanbi a_wnan f0_nanbi f0_nanbi a_wnan f1_nanbi f1_nanbi a_wnan a_wnan a_df-nan f0_nanbi f1_nanbi a_df-nan f0_nanbi f0_nanbi a_wnan f1_nanbi f1_nanbi a_wnan a_df-nan f0_nanbi p_nannot f1_nanbi p_nannot f0_nanbi a_wn f0_nanbi f0_nanbi a_wnan f1_nanbi a_wn f1_nanbi f1_nanbi a_wnan p_anbi12i f0_nanbi f0_nanbi a_wnan f1_nanbi f1_nanbi a_wnan a_wnan f0_nanbi f0_nanbi a_wnan f1_nanbi f1_nanbi a_wnan a_wa f0_nanbi a_wn f1_nanbi a_wn a_wa p_xchbinxr f0_nanbi f1_nanbi a_wnan f0_nanbi f1_nanbi a_wa a_wn f0_nanbi f0_nanbi a_wnan f1_nanbi f1_nanbi a_wnan a_wnan f0_nanbi a_wn f1_nanbi a_wn a_wa a_wn p_anbi12i f0_nanbi f1_nanbi a_wnan f0_nanbi f0_nanbi a_wnan f1_nanbi f1_nanbi a_wnan a_wnan a_wnan f0_nanbi f1_nanbi a_wnan f0_nanbi f0_nanbi a_wnan f1_nanbi f1_nanbi a_wnan a_wnan a_wa f0_nanbi f1_nanbi a_wa a_wn f0_nanbi a_wn f1_nanbi a_wn a_wa a_wn a_wa p_xchbinx f0_nanbi f1_nanbi p_dfbi3 f0_nanbi f1_nanbi a_wa a_wn f0_nanbi a_wn f1_nanbi a_wn a_wa a_wn a_wa a_wn f0_nanbi f1_nanbi a_wa f0_nanbi a_wn f1_nanbi a_wn a_wa a_wo f0_nanbi f1_nanbi a_wnan f0_nanbi f0_nanbi a_wnan f1_nanbi f1_nanbi a_wnan a_wnan a_wnan f0_nanbi f1_nanbi a_wb p_3bitr4ri $.
$}


