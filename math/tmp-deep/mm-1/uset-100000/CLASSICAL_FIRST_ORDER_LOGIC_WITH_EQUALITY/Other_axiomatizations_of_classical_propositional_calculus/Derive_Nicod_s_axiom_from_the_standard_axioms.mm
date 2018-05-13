$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_standard_axioms_from_the_Lukasiewicz_axioms.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Derive Nicod's axiom from the standard axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Prove Nicod's axiom and implication and negation definitions.

$)

$(Define implication in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ( ps -/\ ps ) ) <-> ( ph -> ps ) ) ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     a definition ($a statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_nic-dfim $f wff ph $.
	f1_nic-dfim $f wff ps $.
	p_nic-dfim $p |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\ ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) ) -/\ ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) ) $= f0_nic-dfim f1_nic-dfim p_nanim f0_nic-dfim f1_nic-dfim a_wi f0_nic-dfim f1_nic-dfim f1_nic-dfim a_wnan a_wnan p_bicomi f0_nic-dfim f1_nic-dfim f1_nic-dfim a_wnan a_wnan f0_nic-dfim f1_nic-dfim a_wi p_nanbi f0_nic-dfim f1_nic-dfim f1_nic-dfim a_wnan a_wnan f0_nic-dfim f1_nic-dfim a_wi a_wb f0_nic-dfim f1_nic-dfim f1_nic-dfim a_wnan a_wnan f0_nic-dfim f1_nic-dfim a_wi a_wnan f0_nic-dfim f1_nic-dfim f1_nic-dfim a_wnan a_wnan f0_nic-dfim f1_nic-dfim f1_nic-dfim a_wnan a_wnan a_wnan f0_nic-dfim f1_nic-dfim a_wi f0_nic-dfim f1_nic-dfim a_wi a_wnan a_wnan a_wnan p_mpbi $.
$}

$(Define negation in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ph ) <-> -. ph ) ` .  In a pure (standalone) treatment of
     Nicod's axiom, this theorem would be changed to a definition ($a
     statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph  $.
	f0_nic-dfneg $f wff ph $.
	p_nic-dfneg $p |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\ ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\ ( -. ph -/\ -. ph ) ) ) $= f0_nic-dfneg p_nannot f0_nic-dfneg a_wn f0_nic-dfneg f0_nic-dfneg a_wnan p_bicomi f0_nic-dfneg f0_nic-dfneg a_wnan f0_nic-dfneg a_wn p_nanbi f0_nic-dfneg f0_nic-dfneg a_wnan f0_nic-dfneg a_wn a_wb f0_nic-dfneg f0_nic-dfneg a_wnan f0_nic-dfneg a_wn a_wnan f0_nic-dfneg f0_nic-dfneg a_wnan f0_nic-dfneg f0_nic-dfneg a_wnan a_wnan f0_nic-dfneg a_wn f0_nic-dfneg a_wn a_wnan a_wnan a_wnan p_mpbi $.
$}

$(Minor premise. $)

$(Major premise. $)

$(Derive Nicod's rule of modus ponens using 'nand', from the standard
       one.  Although the major and minor premise together also imply ` ch ` ,
       this form is necessary for useful derivations from ~ nic-ax .  In a pure
       (standalone) treatment of Nicod's axiom, this theorem would be changed
       to an axiom ($a statement).  (Contributed by Jeff Hoffman,
       19-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_nic-mp $f wff ph $.
	f1_nic-mp $f wff ps $.
	f2_nic-mp $f wff ch $.
	e0_nic-mp $e |- ph $.
	e1_nic-mp $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	p_nic-mp $p |- ps $= e0_nic-mp e1_nic-mp f0_nic-mp f1_nic-mp f2_nic-mp p_nannan f0_nic-mp f2_nic-mp f1_nic-mp a_wnan a_wnan f0_nic-mp f2_nic-mp f1_nic-mp a_wa a_wi p_mpbi f0_nic-mp f2_nic-mp f1_nic-mp p_simprd f0_nic-mp f1_nic-mp a_ax-mp $.
$}

$(A direct proof of ~ nic-mp .  (Contributed by NM, 30-Dec-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_nic-mpALT $f wff ph $.
	f1_nic-mpALT $f wff ps $.
	f2_nic-mpALT $f wff ch $.
	e0_nic-mpALT $e |- ph $.
	e1_nic-mpALT $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	p_nic-mpALT $p |- ps $= e0_nic-mpALT e1_nic-mpALT f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wnan a_df-nan f2_nic-mpALT f1_nic-mpALT a_df-nan f2_nic-mpALT f1_nic-mpALT a_wnan f2_nic-mpALT f1_nic-mpALT a_wa a_wn f0_nic-mpALT p_anbi2i f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wnan a_wnan f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wnan a_wa f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wa a_wn a_wa p_xchbinx f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wnan a_wnan f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wa a_wn a_wa a_wn p_mpbi f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wa p_iman f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wa a_wi f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT a_wa a_wn a_wa a_wn p_mpbir f0_nic-mpALT f2_nic-mpALT f1_nic-mpALT p_simprd f0_nic-mpALT f1_nic-mpALT a_ax-mp $.
$}

$(Nicod's axiom derived from the standard ones.  See _Intro. to Math.
     Phil._ by B. Russell, p. 152.  Like ~ meredith , the usual axioms can be
     derived from this and vice versa.  Unlike ~ meredith , Nicod uses a
     different connective ('nand'), so another form of modus ponens must be
     used in proofs, e.g. ` { ` ~ nic-ax , ~ nic-mp ` } ` is equivalent to
     ` { ` ~ luk-1 , ~ luk-2 , ~ luk-3 , ~ ax-mp ` } ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     an axiom ($a statement).  (Contributed by Jeff Hoffman, 19-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch th ta  $.
	f0_nic-ax $f wff ph $.
	f1_nic-ax $f wff ps $.
	f2_nic-ax $f wff ch $.
	f3_nic-ax $f wff th $.
	f4_nic-ax $f wff ta $.
	p_nic-ax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $= f0_nic-ax f1_nic-ax f2_nic-ax p_nannan f0_nic-ax f2_nic-ax f1_nic-ax a_wnan a_wnan f0_nic-ax f2_nic-ax f1_nic-ax a_wa a_wi p_biimpi f2_nic-ax f1_nic-ax p_simpl f2_nic-ax f1_nic-ax a_wa f2_nic-ax f0_nic-ax p_imim2i f3_nic-ax f2_nic-ax p_imnan f3_nic-ax f2_nic-ax a_df-nan f3_nic-ax f2_nic-ax a_wn a_wi f3_nic-ax f2_nic-ax a_wa a_wn f3_nic-ax f2_nic-ax a_wnan p_bitr4i f0_nic-ax f2_nic-ax p_con3 f0_nic-ax f2_nic-ax a_wi f2_nic-ax a_wn f0_nic-ax a_wn f3_nic-ax p_imim2d f0_nic-ax f3_nic-ax p_imnan f3_nic-ax f0_nic-ax p_con2b f0_nic-ax f3_nic-ax a_df-nan f0_nic-ax f3_nic-ax a_wn a_wi f0_nic-ax f3_nic-ax a_wa a_wn f3_nic-ax f0_nic-ax a_wn a_wi f0_nic-ax f3_nic-ax a_wnan p_3bitr4ri f0_nic-ax f2_nic-ax a_wi f3_nic-ax f2_nic-ax a_wn a_wi f3_nic-ax f0_nic-ax a_wn a_wi f0_nic-ax f3_nic-ax a_wnan p_syl6ibr f3_nic-ax f2_nic-ax a_wnan f3_nic-ax f2_nic-ax a_wn a_wi f0_nic-ax f2_nic-ax a_wi f0_nic-ax f3_nic-ax a_wnan p_syl5bir f3_nic-ax f2_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan p_nanim f0_nic-ax f2_nic-ax a_wi f3_nic-ax f2_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan a_wi f3_nic-ax f2_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan a_wnan a_wnan p_sylib f0_nic-ax f2_nic-ax f1_nic-ax a_wnan a_wnan f0_nic-ax f2_nic-ax f1_nic-ax a_wa a_wi f0_nic-ax f2_nic-ax a_wi f3_nic-ax f2_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan a_wnan a_wnan p_3syl f4_nic-ax p_pm4.24 f4_nic-ax f4_nic-ax f4_nic-ax a_wa p_biimpi f4_nic-ax f4_nic-ax f4_nic-ax p_nannan f4_nic-ax f4_nic-ax f4_nic-ax a_wnan a_wnan f4_nic-ax f4_nic-ax f4_nic-ax a_wa a_wi p_mpbir f0_nic-ax f2_nic-ax f1_nic-ax a_wnan a_wnan f3_nic-ax f2_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan a_wnan a_wnan f4_nic-ax f4_nic-ax f4_nic-ax a_wnan a_wnan p_jctil f0_nic-ax f2_nic-ax f1_nic-ax a_wnan a_wnan f3_nic-ax f2_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan a_wnan a_wnan f4_nic-ax f4_nic-ax f4_nic-ax a_wnan a_wnan p_nannan f0_nic-ax f2_nic-ax f1_nic-ax a_wnan a_wnan f4_nic-ax f4_nic-ax f4_nic-ax a_wnan a_wnan f3_nic-ax f2_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan a_wnan a_wnan a_wnan a_wnan f0_nic-ax f2_nic-ax f1_nic-ax a_wnan a_wnan f4_nic-ax f4_nic-ax f4_nic-ax a_wnan a_wnan f3_nic-ax f2_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan f0_nic-ax f3_nic-ax a_wnan a_wnan a_wnan a_wa a_wi p_mpbir $.
$}

$(A direct proof of ~ nic-ax .  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch th ta  $.
	f0_nic-axALT $f wff ph $.
	f1_nic-axALT $f wff ps $.
	f2_nic-axALT $f wff ch $.
	f3_nic-axALT $f wff th $.
	f4_nic-axALT $f wff ta $.
	p_nic-axALT $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $= f2_nic-axALT f1_nic-axALT p_simpl f2_nic-axALT f1_nic-axALT a_wa f2_nic-axALT f0_nic-axALT p_imim2i f0_nic-axALT f2_nic-axALT p_con3 f0_nic-axALT f2_nic-axALT a_wi f2_nic-axALT a_wn f0_nic-axALT a_wn f3_nic-axALT p_imim2d f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi f0_nic-axALT f2_nic-axALT a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi p_syl f4_nic-axALT p_anidm f4_nic-axALT f4_nic-axALT a_wa f4_nic-axALT p_biimpri f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi p_jctil f2_nic-axALT f1_nic-axALT a_df-nan f2_nic-axALT f1_nic-axALT a_wnan f2_nic-axALT f1_nic-axALT a_wa a_wn f0_nic-axALT p_anbi2i f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wa f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wn a_wa p_notbii f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_df-nan f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa p_iman f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wa a_wn f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wn a_wa a_wn f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wnan f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi p_3bitr4i f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_df-nan f4_nic-axALT f4_nic-axALT a_df-nan f4_nic-axALT f4_nic-axALT a_wnan f4_nic-axALT f4_nic-axALT a_wa a_wn f4_nic-axALT p_anbi2i f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wa f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wn a_wa p_notbii f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_df-nan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa p_iman f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wa a_wn f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wn a_wa a_wn f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi p_3bitr4i f3_nic-axALT f2_nic-axALT a_df-nan f3_nic-axALT f2_nic-axALT p_imnan f3_nic-axALT f2_nic-axALT a_wnan f3_nic-axALT f2_nic-axALT a_wa a_wn f3_nic-axALT f2_nic-axALT a_wn a_wi p_bitr4i f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_df-nan f0_nic-axALT f3_nic-axALT a_wnan p_anidm f0_nic-axALT f3_nic-axALT a_df-nan f0_nic-axALT f3_nic-axALT p_imnan f0_nic-axALT f3_nic-axALT p_con2b f0_nic-axALT f3_nic-axALT a_wa a_wn f0_nic-axALT f3_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi p_bitr3i f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wa f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wa a_wn f3_nic-axALT f0_nic-axALT a_wn a_wi p_3bitri f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wa f3_nic-axALT f0_nic-axALT a_wn a_wi p_xchbinx f3_nic-axALT f2_nic-axALT a_wnan f3_nic-axALT f2_nic-axALT a_wn a_wi f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan f3_nic-axALT f0_nic-axALT a_wn a_wi a_wn p_anbi12i f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wa f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wn a_wa p_notbii f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_df-nan f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi p_iman f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wa a_wn f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wn a_wa a_wn f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi p_3bitr4i f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi p_anbi12i f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wa f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi a_wa p_xchbinx f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wnan f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi a_wa a_wn p_anbi12i f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wnan a_wa f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi a_wa a_wn a_wa p_notbii f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi a_wa p_iman f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wnan a_wa a_wn f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi a_wa a_wn a_wa a_wn f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi a_wa a_wi p_bitr4i f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wnan a_wa a_wn f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wa a_wi f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wa a_wi f3_nic-axALT f2_nic-axALT a_wn a_wi f3_nic-axALT f0_nic-axALT a_wn a_wi a_wi a_wa a_wi p_mpbir f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wnan a_df-nan f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wnan a_wnan f0_nic-axALT f2_nic-axALT f1_nic-axALT a_wnan a_wnan f4_nic-axALT f4_nic-axALT f4_nic-axALT a_wnan a_wnan f3_nic-axALT f2_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan f0_nic-axALT f3_nic-axALT a_wnan a_wnan a_wnan a_wnan a_wa a_wn p_mpbir $.
$}


