$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_standard_axioms_from_the_Lukasiewicz_axioms.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Derive Nicod's axiom from the standard axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Prove Nicod's axiom and implication and negation definitions.

$)
$( Define implication in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ( ps -/\ ps ) ) <-> ( ph -> ps ) ) ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     a definition ($a statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fnic-dfim_0 $f wff ph $.
	fnic-dfim_1 $f wff ps $.
	nic-dfim $p |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\ ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) ) -/\ ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) ) $= fnic-dfim_0 fnic-dfim_1 fnic-dfim_1 wnan wnan fnic-dfim_0 fnic-dfim_1 wi wb fnic-dfim_0 fnic-dfim_1 fnic-dfim_1 wnan wnan fnic-dfim_0 fnic-dfim_1 wi wnan fnic-dfim_0 fnic-dfim_1 fnic-dfim_1 wnan wnan fnic-dfim_0 fnic-dfim_1 fnic-dfim_1 wnan wnan wnan fnic-dfim_0 fnic-dfim_1 wi fnic-dfim_0 fnic-dfim_1 wi wnan wnan wnan fnic-dfim_0 fnic-dfim_1 wi fnic-dfim_0 fnic-dfim_1 fnic-dfim_1 wnan wnan fnic-dfim_0 fnic-dfim_1 nanim bicomi fnic-dfim_0 fnic-dfim_1 fnic-dfim_1 wnan wnan fnic-dfim_0 fnic-dfim_1 wi nanbi mpbi $.
$}
$( Define negation in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ph ) <-> -. ph ) ` .  In a pure (standalone) treatment of
     Nicod's axiom, this theorem would be changed to a definition ($a
     statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	fnic-dfneg_0 $f wff ph $.
	nic-dfneg $p |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\ ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\ ( -. ph -/\ -. ph ) ) ) $= fnic-dfneg_0 fnic-dfneg_0 wnan fnic-dfneg_0 wn wb fnic-dfneg_0 fnic-dfneg_0 wnan fnic-dfneg_0 wn wnan fnic-dfneg_0 fnic-dfneg_0 wnan fnic-dfneg_0 fnic-dfneg_0 wnan wnan fnic-dfneg_0 wn fnic-dfneg_0 wn wnan wnan wnan fnic-dfneg_0 wn fnic-dfneg_0 fnic-dfneg_0 wnan fnic-dfneg_0 nannot bicomi fnic-dfneg_0 fnic-dfneg_0 wnan fnic-dfneg_0 wn nanbi mpbi $.
$}
$( Minor premise. $)
$( Major premise. $)
$( Derive Nicod's rule of modus ponens using 'nand', from the standard
       one.  Although the major and minor premise together also imply ` ch ` ,
       this form is necessary for useful derivations from ~ nic-ax .  In a pure
       (standalone) treatment of Nicod's axiom, this theorem would be changed
       to an axiom ($a statement).  (Contributed by Jeff Hoffman,
       19-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnic-mp_0 $f wff ph $.
	fnic-mp_1 $f wff ps $.
	fnic-mp_2 $f wff ch $.
	enic-mp_0 $e |- ph $.
	enic-mp_1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	nic-mp $p |- ps $= fnic-mp_0 fnic-mp_1 enic-mp_0 fnic-mp_0 fnic-mp_2 fnic-mp_1 fnic-mp_0 fnic-mp_2 fnic-mp_1 wnan wnan fnic-mp_0 fnic-mp_2 fnic-mp_1 wa wi enic-mp_1 fnic-mp_0 fnic-mp_1 fnic-mp_2 nannan mpbi simprd ax-mp $.
$}
$( A direct proof of ~ nic-mp .  (Contributed by NM, 30-Dec-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnic-mpALT_0 $f wff ph $.
	fnic-mpALT_1 $f wff ps $.
	fnic-mpALT_2 $f wff ch $.
	enic-mpALT_0 $e |- ph $.
	enic-mpALT_1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	nic-mpALT $p |- ps $= fnic-mpALT_0 fnic-mpALT_1 enic-mpALT_0 fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wa wi fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wa wn wa wn fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wnan wnan fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wa wn wa wn enic-mpALT_1 fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wnan wnan fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wnan wa fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wa wn wa fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wnan df-nan fnic-mpALT_2 fnic-mpALT_1 wnan fnic-mpALT_2 fnic-mpALT_1 wa wn fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 df-nan anbi2i xchbinx mpbi fnic-mpALT_0 fnic-mpALT_2 fnic-mpALT_1 wa iman mpbir simprd ax-mp $.
$}
$( Nicod's axiom derived from the standard ones.  See _Intro. to Math.
     Phil._ by B. Russell, p. 152.  Like ~ meredith , the usual axioms can be
     derived from this and vice versa.  Unlike ~ meredith , Nicod uses a
     different connective ('nand'), so another form of modus ponens must be
     used in proofs, e.g. ` { ` ~ nic-ax , ~ nic-mp ` } ` is equivalent to
     ` { ` ~ luk-1 , ~ luk-2 , ~ luk-3 , ~ ax-mp ` } ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     an axiom ($a statement).  (Contributed by Jeff Hoffman, 19-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fnic-ax_0 $f wff ph $.
	fnic-ax_1 $f wff ps $.
	fnic-ax_2 $f wff ch $.
	fnic-ax_3 $f wff th $.
	fnic-ax_4 $f wff ta $.
	nic-ax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $= fnic-ax_0 fnic-ax_2 fnic-ax_1 wnan wnan fnic-ax_4 fnic-ax_4 fnic-ax_4 wnan wnan fnic-ax_3 fnic-ax_2 wnan fnic-ax_0 fnic-ax_3 wnan fnic-ax_0 fnic-ax_3 wnan wnan wnan wnan wnan fnic-ax_0 fnic-ax_2 fnic-ax_1 wnan wnan fnic-ax_4 fnic-ax_4 fnic-ax_4 wnan wnan fnic-ax_3 fnic-ax_2 wnan fnic-ax_0 fnic-ax_3 wnan fnic-ax_0 fnic-ax_3 wnan wnan wnan wa wi fnic-ax_0 fnic-ax_2 fnic-ax_1 wnan wnan fnic-ax_3 fnic-ax_2 wnan fnic-ax_0 fnic-ax_3 wnan fnic-ax_0 fnic-ax_3 wnan wnan wnan fnic-ax_4 fnic-ax_4 fnic-ax_4 wnan wnan fnic-ax_0 fnic-ax_2 fnic-ax_1 wnan wnan fnic-ax_0 fnic-ax_2 fnic-ax_1 wa wi fnic-ax_0 fnic-ax_2 wi fnic-ax_3 fnic-ax_2 wnan fnic-ax_0 fnic-ax_3 wnan fnic-ax_0 fnic-ax_3 wnan wnan wnan fnic-ax_0 fnic-ax_2 fnic-ax_1 wnan wnan fnic-ax_0 fnic-ax_2 fnic-ax_1 wa wi fnic-ax_0 fnic-ax_1 fnic-ax_2 nannan biimpi fnic-ax_2 fnic-ax_1 wa fnic-ax_2 fnic-ax_0 fnic-ax_2 fnic-ax_1 simpl imim2i fnic-ax_0 fnic-ax_2 wi fnic-ax_3 fnic-ax_2 wnan fnic-ax_0 fnic-ax_3 wnan wi fnic-ax_3 fnic-ax_2 wnan fnic-ax_0 fnic-ax_3 wnan fnic-ax_0 fnic-ax_3 wnan wnan wnan fnic-ax_3 fnic-ax_2 wnan fnic-ax_3 fnic-ax_2 wn wi fnic-ax_0 fnic-ax_2 wi fnic-ax_0 fnic-ax_3 wnan fnic-ax_3 fnic-ax_2 wn wi fnic-ax_3 fnic-ax_2 wa wn fnic-ax_3 fnic-ax_2 wnan fnic-ax_3 fnic-ax_2 imnan fnic-ax_3 fnic-ax_2 df-nan bitr4i fnic-ax_0 fnic-ax_2 wi fnic-ax_3 fnic-ax_2 wn wi fnic-ax_3 fnic-ax_0 wn wi fnic-ax_0 fnic-ax_3 wnan fnic-ax_0 fnic-ax_2 wi fnic-ax_2 wn fnic-ax_0 wn fnic-ax_3 fnic-ax_0 fnic-ax_2 con3 imim2d fnic-ax_0 fnic-ax_3 wn wi fnic-ax_0 fnic-ax_3 wa wn fnic-ax_3 fnic-ax_0 wn wi fnic-ax_0 fnic-ax_3 wnan fnic-ax_0 fnic-ax_3 imnan fnic-ax_3 fnic-ax_0 con2b fnic-ax_0 fnic-ax_3 df-nan 3bitr4ri syl6ibr syl5bir fnic-ax_3 fnic-ax_2 wnan fnic-ax_0 fnic-ax_3 wnan nanim sylib 3syl fnic-ax_4 fnic-ax_4 fnic-ax_4 wnan wnan fnic-ax_4 fnic-ax_4 fnic-ax_4 wa wi fnic-ax_4 fnic-ax_4 fnic-ax_4 wa fnic-ax_4 pm4.24 biimpi fnic-ax_4 fnic-ax_4 fnic-ax_4 nannan mpbir jctil fnic-ax_0 fnic-ax_2 fnic-ax_1 wnan wnan fnic-ax_3 fnic-ax_2 wnan fnic-ax_0 fnic-ax_3 wnan fnic-ax_0 fnic-ax_3 wnan wnan wnan fnic-ax_4 fnic-ax_4 fnic-ax_4 wnan wnan nannan mpbir $.
$}
$( A direct proof of ~ nic-ax .  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fnic-axALT_0 $f wff ph $.
	fnic-axALT_1 $f wff ps $.
	fnic-axALT_2 $f wff ch $.
	fnic-axALT_3 $f wff th $.
	fnic-axALT_4 $f wff ta $.
	nic-axALT $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $= fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wnan wnan fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wnan wa wn fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wnan wa wn fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi wa wi fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_0 fnic-axALT_2 wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi fnic-axALT_2 fnic-axALT_1 wa fnic-axALT_2 fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 simpl imim2i fnic-axALT_0 fnic-axALT_2 wi fnic-axALT_2 wn fnic-axALT_0 wn fnic-axALT_3 fnic-axALT_0 fnic-axALT_2 con3 imim2d syl fnic-axALT_4 fnic-axALT_4 wa fnic-axALT_4 fnic-axALT_4 anidm biimpri jctil fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wnan wa wn fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi wa wn wa wn fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi wa wi fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wnan wa fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi wa wn wa fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wnan fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi wa wn fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wa wn fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wn wa wn fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wnan fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wa fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wn wa fnic-axALT_2 fnic-axALT_1 wnan fnic-axALT_2 fnic-axALT_1 wa wn fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 df-nan anbi2i notbii fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan df-nan fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa iman 3bitr4i fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wa fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi wa fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan df-nan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wa wn fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wn wa wn fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wa fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wn wa fnic-axALT_4 fnic-axALT_4 wnan fnic-axALT_4 fnic-axALT_4 wa wn fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 df-nan anbi2i notbii fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan df-nan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa iman 3bitr4i fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wa wn fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wn wa wn fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wa fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wn wa fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan fnic-axALT_3 fnic-axALT_0 wn wi wn fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_3 fnic-axALT_2 wa wn fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_2 df-nan fnic-axALT_3 fnic-axALT_2 imnan bitr4i fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wa fnic-axALT_3 fnic-axALT_0 wn wi fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan df-nan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wa fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wa wn fnic-axALT_3 fnic-axALT_0 wn wi fnic-axALT_0 fnic-axALT_3 wnan anidm fnic-axALT_0 fnic-axALT_3 df-nan fnic-axALT_0 fnic-axALT_3 wa wn fnic-axALT_0 fnic-axALT_3 wn wi fnic-axALT_3 fnic-axALT_0 wn wi fnic-axALT_0 fnic-axALT_3 imnan fnic-axALT_0 fnic-axALT_3 con2b bitr3i 3bitri xchbinx anbi12i notbii fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan df-nan fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi iman 3bitr4i anbi12i xchbinx anbi12i notbii fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wa wi fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wa wi fnic-axALT_3 fnic-axALT_2 wn wi fnic-axALT_3 fnic-axALT_0 wn wi wi wa iman bitr4i mpbir fnic-axALT_0 fnic-axALT_2 fnic-axALT_1 wnan wnan fnic-axALT_4 fnic-axALT_4 fnic-axALT_4 wnan wnan fnic-axALT_3 fnic-axALT_2 wnan fnic-axALT_0 fnic-axALT_3 wnan fnic-axALT_0 fnic-axALT_3 wnan wnan wnan wnan df-nan mpbir $.
$}

