$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz axioms from Meredith's sole axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Carew Meredith's sole axiom for propositional calculus.  This amazing
     formula is thought to be the shortest possible single axiom for
     propositional calculus with inference rule ~ ax-mp , where negation and
     implication are primitive.  Here we prove Meredith's axiom from ~ ax-1 ,
     ~ ax-2 , and ~ ax-3 .  Then from it we derive the Lukasiewicz axioms
     ~ luk-1 , ~ luk-2 , and ~ luk-3 .  Using these we finally re-derive our
     axioms as ~ ax1 , ~ ax2 , and ~ ax3 , thus proving the equivalence of all
     three systems.  C. A. Meredith, "Single Axioms for the Systems (C,N),
     (C,O) and (A,N) of the Two-Valued Propositional Calculus," _The Journal of
     Computing Systems_ vol. 1 (1953), pp. 155-164.  Meredith claimed to be
     close to a proof that this axiom is the shortest possible, but the proof
     was apparently never completed.

     An obscure Irish lecturer, Meredith (1904-1976) became enamored with logic
     somewhat late in life after attending talks by Lukasiewicz and produced
     many remarkable results such as this axiom.  From his obituary:  "He did
     logic whenever time and opportunity presented themselves, and he did it on
     whatever materials came to hand: in a pub, his favored pint of porter
     within reach, he would use the inside of cigarette packs to write proofs
     for logical colleagues."  (Contributed by NM, 14-Dec-2002.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.)  (Proof shortened by Wolf
     Lammen, 28-May-2013.) $)
${
	fmeredith_0 $f wff ph $.
	fmeredith_1 $f wff ps $.
	fmeredith_2 $f wff ch $.
	fmeredith_3 $f wff th $.
	fmeredith_4 $f wff ta $.
	meredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $= fmeredith_0 fmeredith_1 wi fmeredith_2 wn fmeredith_3 wn wi wi fmeredith_2 wi fmeredith_4 fmeredith_4 fmeredith_0 wi fmeredith_3 fmeredith_0 wi wi fmeredith_0 fmeredith_1 wi fmeredith_2 wn fmeredith_3 wn wi wi fmeredith_2 wi wn fmeredith_3 fmeredith_0 wi fmeredith_4 fmeredith_0 wi fmeredith_3 fmeredith_0 fmeredith_1 wi fmeredith_2 wn fmeredith_3 wn wi wi fmeredith_2 wi wn fmeredith_0 fmeredith_3 fmeredith_0 fmeredith_0 fmeredith_1 wi fmeredith_2 wn fmeredith_3 wn wi wi fmeredith_2 wi fmeredith_0 fmeredith_1 wi fmeredith_2 wn fmeredith_3 wn wi wi fmeredith_0 wn fmeredith_3 fmeredith_2 fmeredith_0 wn fmeredith_0 fmeredith_1 wi fmeredith_2 wn fmeredith_3 wn wi fmeredith_3 fmeredith_2 wi fmeredith_0 fmeredith_1 pm2.21 fmeredith_2 fmeredith_3 ax-3 imim12i com13 con1d com12 a1d fmeredith_4 fmeredith_3 fmeredith_4 fmeredith_0 fmeredith_4 fmeredith_3 ax-1 imim1d ja $.
$}
$( Alias for ~ meredith which "verify markup *" will match to
     ~ ax-meredith .  (Contributed by NM, 21-Aug-2017.)
     (New usage is discouraged.) $)
${
	faxmeredith_0 $f wff ph $.
	faxmeredith_1 $f wff ps $.
	faxmeredith_2 $f wff ch $.
	faxmeredith_3 $f wff th $.
	faxmeredith_4 $f wff ta $.
	axmeredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $= faxmeredith_0 faxmeredith_1 faxmeredith_2 faxmeredith_3 faxmeredith_4 meredith $.
$}
$( Theorem ~ meredith restated as an axiom.  This will allow us to ensure
     that the rederivation of ~ ax1 , ~ ax2 , and ~ ax3 below depend only on
     Meredith's sole axiom and not accidentally on a previous theorem above.
     Outside of this section, we will not make use of this axiom.  (Contributed
     by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fax-meredith_0 $f wff ph $.
	fax-meredith_1 $f wff ps $.
	fax-meredith_2 $f wff ch $.
	fax-meredith_3 $f wff th $.
	fax-meredith_4 $f wff ta $.
	ax-meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.
$}
$( Step 3 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (The step numbers refer to Meredith's original paper.)  (Contributed by
     NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem1_0 $f wff ph $.
	fmerlem1_1 $f wff ps $.
	fmerlem1_2 $f wff ch $.
	fmerlem1_3 $f wff ta $.
	merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $= fmerlem1_3 fmerlem1_0 wn wi fmerlem1_0 wn fmerlem1_1 wi wn fmerlem1_0 wn wi wi fmerlem1_0 wn fmerlem1_1 wi wi fmerlem1_2 fmerlem1_0 wn fmerlem1_1 wi wi wi fmerlem1_2 fmerlem1_0 wn fmerlem1_1 wi wi fmerlem1_3 wi fmerlem1_0 fmerlem1_3 wi wi fmerlem1_0 wn fmerlem1_1 wi fmerlem1_3 wn fmerlem1_2 wn wi wn fmerlem1_0 wn fmerlem1_1 wi wn wn wi wi fmerlem1_3 wn fmerlem1_2 wn wi wi fmerlem1_3 wi fmerlem1_3 fmerlem1_0 wn wi fmerlem1_0 wn fmerlem1_1 wi wn fmerlem1_0 wn wi wi wi fmerlem1_3 fmerlem1_0 wn wi fmerlem1_0 wn fmerlem1_1 wi wn fmerlem1_0 wn wi wi fmerlem1_0 wn fmerlem1_1 wi wi fmerlem1_2 fmerlem1_0 wn fmerlem1_1 wi wi wi fmerlem1_0 wn fmerlem1_1 fmerlem1_3 wn fmerlem1_2 wn wi fmerlem1_0 wn fmerlem1_1 wi wn fmerlem1_3 ax-meredith fmerlem1_0 wn fmerlem1_1 wi fmerlem1_3 wn fmerlem1_2 wn wi wn fmerlem1_0 wn fmerlem1_1 wi wn wn wi fmerlem1_3 fmerlem1_2 fmerlem1_3 fmerlem1_0 wn wi fmerlem1_0 wn fmerlem1_1 wi wn fmerlem1_0 wn wi wi ax-meredith ax-mp fmerlem1_3 fmerlem1_0 wn fmerlem1_0 wn fmerlem1_1 wi fmerlem1_0 fmerlem1_2 fmerlem1_0 wn fmerlem1_1 wi wi ax-meredith ax-mp $.
$}
$( Step 4 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem2_0 $f wff ph $.
	fmerlem2_1 $f wff ch $.
	fmerlem2_2 $f wff th $.
	merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $= fmerlem2_1 fmerlem2_1 wi fmerlem2_0 wn fmerlem2_2 wn wi wi fmerlem2_0 wi fmerlem2_0 fmerlem2_0 wi wi fmerlem2_0 fmerlem2_0 wi fmerlem2_1 wi fmerlem2_2 fmerlem2_1 wi wi fmerlem2_0 fmerlem2_2 wn fmerlem2_1 fmerlem2_1 wi fmerlem2_0 merlem1 fmerlem2_1 fmerlem2_1 fmerlem2_0 fmerlem2_2 fmerlem2_0 fmerlem2_0 wi ax-meredith ax-mp $.
$}
$( Step 7 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem3_0 $f wff ph $.
	fmerlem3_1 $f wff ps $.
	fmerlem3_2 $f wff ch $.
	merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $= fmerlem3_0 fmerlem3_0 wi fmerlem3_2 wn fmerlem3_2 wn wi wi fmerlem3_2 wi fmerlem3_1 fmerlem3_2 wi wi fmerlem3_1 fmerlem3_2 wi fmerlem3_0 wi fmerlem3_2 fmerlem3_0 wi wi fmerlem3_2 fmerlem3_0 wi fmerlem3_1 wn fmerlem3_1 wn wi wi fmerlem3_1 wi fmerlem3_0 fmerlem3_0 wi fmerlem3_2 wn fmerlem3_2 wn wi wi wi fmerlem3_0 fmerlem3_0 wi fmerlem3_2 wn fmerlem3_2 wn wi wi fmerlem3_2 wi fmerlem3_1 fmerlem3_2 wi wi fmerlem3_2 wn fmerlem3_2 wn wi fmerlem3_2 wn fmerlem3_2 wn wi wi fmerlem3_0 fmerlem3_0 wi fmerlem3_2 wn fmerlem3_2 wn wi wi wi fmerlem3_2 fmerlem3_0 wi fmerlem3_1 wn fmerlem3_1 wn wi wi fmerlem3_1 wi fmerlem3_0 fmerlem3_0 wi fmerlem3_2 wn fmerlem3_2 wn wi wi wi fmerlem3_2 wn fmerlem3_2 wn fmerlem3_2 wn wi fmerlem3_0 fmerlem3_0 wi merlem2 fmerlem3_2 wn fmerlem3_2 wn wi fmerlem3_0 fmerlem3_0 wi fmerlem3_2 wn fmerlem3_2 wn wi wi fmerlem3_2 fmerlem3_0 wi fmerlem3_1 wn fmerlem3_1 wn wi wi fmerlem3_1 wi merlem2 ax-mp fmerlem3_2 fmerlem3_0 fmerlem3_1 fmerlem3_1 fmerlem3_0 fmerlem3_0 wi fmerlem3_2 wn fmerlem3_2 wn wi wi ax-meredith ax-mp fmerlem3_0 fmerlem3_0 fmerlem3_2 fmerlem3_2 fmerlem3_1 fmerlem3_2 wi ax-meredith ax-mp $.
$}
$( Step 8 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem4_0 $f wff ph $.
	fmerlem4_1 $f wff th $.
	fmerlem4_2 $f wff ta $.
	merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $= fmerlem4_0 fmerlem4_0 wi fmerlem4_1 wn fmerlem4_1 wn wi wi fmerlem4_1 wi fmerlem4_2 wi fmerlem4_2 fmerlem4_0 wi fmerlem4_1 fmerlem4_0 wi wi wi fmerlem4_2 fmerlem4_2 fmerlem4_0 wi fmerlem4_1 fmerlem4_0 wi wi wi fmerlem4_0 fmerlem4_0 fmerlem4_1 fmerlem4_1 fmerlem4_2 ax-meredith fmerlem4_2 fmerlem4_0 wi fmerlem4_1 fmerlem4_0 wi wi fmerlem4_0 fmerlem4_0 wi fmerlem4_1 wn fmerlem4_1 wn wi wi fmerlem4_1 wi fmerlem4_2 merlem3 ax-mp $.
$}
$( Step 11 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem5_0 $f wff ph $.
	fmerlem5_1 $f wff ps $.
	merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $= fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi fmerlem5_1 fmerlem5_1 fmerlem5_1 fmerlem5_1 fmerlem5_1 ax-meredith fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_0 wn wn wn wi wi fmerlem5_1 wi fmerlem5_0 wi fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi wi fmerlem5_1 fmerlem5_1 fmerlem5_1 fmerlem5_0 wn wn fmerlem5_0 ax-meredith fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn wi fmerlem5_0 wn fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn wi wi fmerlem5_0 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_0 wn wn wn wi wi fmerlem5_1 wi fmerlem5_0 wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_0 wn wn wn wi wi fmerlem5_1 wi fmerlem5_0 wi fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi wi wi fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn wi fmerlem5_0 wn fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn wi wi fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn wi fmerlem5_0 wn fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn wi wi fmerlem5_0 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_0 wn wn wn wi wi fmerlem5_1 wi fmerlem5_0 wi wi fmerlem5_0 wn fmerlem5_1 fmerlem5_0 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn merlem1 fmerlem5_0 fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_0 wn wn wn wi wi fmerlem5_1 wi fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn wi fmerlem5_0 wn fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn wi wi merlem4 ax-mp fmerlem5_0 fmerlem5_1 wi fmerlem5_0 wn wn fmerlem5_1 wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi wn fmerlem5_0 fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_1 wn wi wi fmerlem5_1 wi fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 fmerlem5_1 wi wi wi fmerlem5_1 fmerlem5_1 wi fmerlem5_1 wn fmerlem5_0 wn wn wn wi wi fmerlem5_1 wi fmerlem5_0 wi ax-meredith ax-mp ax-mp ax-mp $.
$}
$( Step 12 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem6_0 $f wff ph $.
	fmerlem6_1 $f wff ps $.
	fmerlem6_2 $f wff ch $.
	fmerlem6_3 $f wff th $.
	merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $= fmerlem6_1 fmerlem6_2 wi fmerlem6_1 fmerlem6_2 wi fmerlem6_0 wi fmerlem6_3 fmerlem6_0 wi wi wi fmerlem6_2 fmerlem6_1 fmerlem6_2 wi fmerlem6_0 wi fmerlem6_3 fmerlem6_0 wi wi wi fmerlem6_0 fmerlem6_3 fmerlem6_1 fmerlem6_2 wi merlem4 fmerlem6_1 fmerlem6_2 wi fmerlem6_0 wi fmerlem6_3 fmerlem6_0 wi wi fmerlem6_1 fmerlem6_2 merlem3 ax-mp $.
$}
$( Between steps 14 and 15 of Meredith's proof of Lukasiewicz axioms from his
     sole axiom.  (Contributed by NM, 22-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fmerlem7_0 $f wff ph $.
	fmerlem7_1 $f wff ps $.
	fmerlem7_2 $f wff ch $.
	fmerlem7_3 $f wff th $.
	fmerlem7_4 $f wff ta $.
	merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) -> ( -. th -> -. ps ) ) -> th ) ) ) $= fmerlem7_1 fmerlem7_2 wi fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi wi fmerlem7_0 fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi wi fmerlem7_3 fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_1 fmerlem7_2 wi merlem4 fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi fmerlem7_0 wn wi fmerlem7_2 wn fmerlem7_0 wn wi wi fmerlem7_2 wi fmerlem7_1 fmerlem7_2 wi wi fmerlem7_1 fmerlem7_2 wi fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi wi fmerlem7_0 fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi wi wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi fmerlem7_0 wn wi fmerlem7_2 wn fmerlem7_0 wn wi wi wi fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi fmerlem7_0 wn wi fmerlem7_2 wn fmerlem7_0 wn wi wi fmerlem7_2 wi fmerlem7_1 fmerlem7_2 wi wi fmerlem7_0 wn fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi fmerlem7_2 wn merlem6 fmerlem7_2 fmerlem7_4 fmerlem7_3 fmerlem7_1 fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi fmerlem7_0 wn wi fmerlem7_2 wn fmerlem7_0 wn wi wi ax-meredith ax-mp fmerlem7_1 fmerlem7_2 wi fmerlem7_3 wi fmerlem7_2 fmerlem7_4 wi fmerlem7_3 wn fmerlem7_1 wn wi wi fmerlem7_3 wi wi fmerlem7_0 wn fmerlem7_2 fmerlem7_0 fmerlem7_1 fmerlem7_2 wi ax-meredith ax-mp ax-mp $.
$}
$( Step 15 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	imerlem8_0 $f wff ph $.
	fmerlem8_0 $f wff ps $.
	fmerlem8_1 $f wff ch $.
	fmerlem8_2 $f wff th $.
	fmerlem8_3 $f wff ta $.
	merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) -> ( -. th -> -. ps ) ) -> th ) ) $= imerlem8_0 imerlem8_0 wi imerlem8_0 wn imerlem8_0 wn wi wi imerlem8_0 wi imerlem8_0 wi imerlem8_0 imerlem8_0 wi imerlem8_0 imerlem8_0 wi wi wi fmerlem8_0 fmerlem8_1 wi fmerlem8_2 wi fmerlem8_1 fmerlem8_3 wi fmerlem8_2 wn fmerlem8_0 wn wi wi fmerlem8_2 wi wi imerlem8_0 imerlem8_0 imerlem8_0 imerlem8_0 imerlem8_0 ax-meredith imerlem8_0 imerlem8_0 wi imerlem8_0 wn imerlem8_0 wn wi wi imerlem8_0 wi imerlem8_0 wi imerlem8_0 imerlem8_0 wi imerlem8_0 imerlem8_0 wi wi wi fmerlem8_0 fmerlem8_1 fmerlem8_2 fmerlem8_3 merlem7 ax-mp $.
$}
$( Step 18 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem9_0 $f wff ph $.
	fmerlem9_1 $f wff ps $.
	fmerlem9_2 $f wff ch $.
	fmerlem9_3 $f wff th $.
	fmerlem9_4 $f wff ta $.
	fmerlem9_5 $f wff et $.
	merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) -> ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $= fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi fmerlem9_1 wi fmerlem9_0 fmerlem9_1 wi wi fmerlem9_0 fmerlem9_1 wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi wi fmerlem9_5 fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi wi wi fmerlem9_1 fmerlem9_4 wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wn fmerlem9_3 wn wi wn fmerlem9_0 wn wi wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wn fmerlem9_3 wn wi wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi fmerlem9_1 wi fmerlem9_0 fmerlem9_1 wi wi fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wi fmerlem9_1 fmerlem9_4 wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wn fmerlem9_3 wn wi wn fmerlem9_0 wn wi wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wn fmerlem9_3 wn wi wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wi fmerlem9_5 wn fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi fmerlem9_1 wn merlem6 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wn fmerlem9_3 wn wi wn fmerlem9_0 wn wi merlem8 ax-mp fmerlem9_1 fmerlem9_4 fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi wn fmerlem9_3 wn wi fmerlem9_0 fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn wi fmerlem9_1 wn fmerlem9_5 wn wi wi ax-meredith ax-mp fmerlem9_2 fmerlem9_3 fmerlem9_1 fmerlem9_4 wi wi wi fmerlem9_5 wn fmerlem9_1 fmerlem9_5 fmerlem9_0 fmerlem9_1 wi ax-meredith ax-mp $.
$}
$( Step 19 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem10_0 $f wff ph $.
	fmerlem10_1 $f wff ps $.
	fmerlem10_2 $f wff th $.
	merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $= fmerlem10_0 fmerlem10_0 wi fmerlem10_0 wn fmerlem10_0 wn wi wi fmerlem10_0 wi fmerlem10_0 wi fmerlem10_0 fmerlem10_0 wi fmerlem10_0 fmerlem10_0 wi wi wi fmerlem10_0 fmerlem10_0 fmerlem10_1 wi wi fmerlem10_2 fmerlem10_0 fmerlem10_1 wi wi wi fmerlem10_0 fmerlem10_0 fmerlem10_0 fmerlem10_0 fmerlem10_0 ax-meredith fmerlem10_0 fmerlem10_1 wi fmerlem10_0 wi fmerlem10_0 wn fmerlem10_2 wn wi wi fmerlem10_0 wi fmerlem10_0 wi fmerlem10_0 fmerlem10_0 fmerlem10_1 wi wi fmerlem10_2 fmerlem10_0 fmerlem10_1 wi wi wi wi fmerlem10_0 fmerlem10_0 wi fmerlem10_0 wn fmerlem10_0 wn wi wi fmerlem10_0 wi fmerlem10_0 wi fmerlem10_0 fmerlem10_0 wi fmerlem10_0 fmerlem10_0 wi wi wi fmerlem10_0 fmerlem10_0 fmerlem10_1 wi wi fmerlem10_2 fmerlem10_0 fmerlem10_1 wi wi wi wi fmerlem10_0 fmerlem10_1 wi fmerlem10_0 fmerlem10_0 fmerlem10_2 fmerlem10_0 ax-meredith fmerlem10_0 fmerlem10_1 wi fmerlem10_0 wi fmerlem10_0 wn fmerlem10_2 wn wi wi fmerlem10_0 wi fmerlem10_0 fmerlem10_0 fmerlem10_0 fmerlem10_1 wi wi fmerlem10_2 fmerlem10_1 fmerlem10_0 fmerlem10_0 wi fmerlem10_0 wn fmerlem10_0 wn wi wi fmerlem10_0 wi fmerlem10_0 wi fmerlem10_0 fmerlem10_0 wi fmerlem10_0 fmerlem10_0 wi wi wi merlem9 ax-mp ax-mp $.
$}
$( Step 20 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem11_0 $f wff ph $.
	fmerlem11_1 $f wff ps $.
	merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $= fmerlem11_0 fmerlem11_0 wi fmerlem11_0 wn fmerlem11_0 wn wi wi fmerlem11_0 wi fmerlem11_0 wi fmerlem11_0 fmerlem11_0 wi fmerlem11_0 fmerlem11_0 wi wi wi fmerlem11_0 fmerlem11_0 fmerlem11_1 wi wi fmerlem11_0 fmerlem11_1 wi wi fmerlem11_0 fmerlem11_0 fmerlem11_0 fmerlem11_0 fmerlem11_0 ax-meredith fmerlem11_0 fmerlem11_0 fmerlem11_1 wi wi fmerlem11_0 fmerlem11_0 fmerlem11_1 wi wi fmerlem11_0 fmerlem11_1 wi wi wi fmerlem11_0 fmerlem11_0 wi fmerlem11_0 wn fmerlem11_0 wn wi wi fmerlem11_0 wi fmerlem11_0 wi fmerlem11_0 fmerlem11_0 wi fmerlem11_0 fmerlem11_0 wi wi wi fmerlem11_0 fmerlem11_0 fmerlem11_1 wi wi fmerlem11_0 fmerlem11_1 wi wi wi fmerlem11_0 fmerlem11_1 fmerlem11_0 fmerlem11_0 fmerlem11_1 wi wi merlem10 fmerlem11_0 fmerlem11_0 fmerlem11_1 wi wi fmerlem11_0 fmerlem11_1 wi fmerlem11_0 fmerlem11_0 wi fmerlem11_0 wn fmerlem11_0 wn wi wi fmerlem11_0 wi fmerlem11_0 wi fmerlem11_0 fmerlem11_0 wi fmerlem11_0 fmerlem11_0 wi wi wi merlem10 ax-mp ax-mp $.
$}
$( Step 28 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem12_0 $f wff ph $.
	fmerlem12_1 $f wff ch $.
	fmerlem12_2 $f wff th $.
	merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $= fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_0 wi fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_0 wi fmerlem12_0 wi wi fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_0 wi fmerlem12_0 wi fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_0 wi fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_0 wi fmerlem12_0 wi wi fmerlem12_1 fmerlem12_1 wi fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_1 fmerlem12_1 merlem5 fmerlem12_1 fmerlem12_1 wn wn fmerlem12_1 wi fmerlem12_2 merlem2 ax-mp fmerlem12_0 fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_0 wi fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi merlem4 ax-mp fmerlem12_2 fmerlem12_1 wn wn fmerlem12_1 wi wi fmerlem12_0 wi fmerlem12_0 merlem11 ax-mp $.
$}
$( Step 35 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fmerlem13_0 $f wff ph $.
	fmerlem13_1 $f wff ps $.
	fmerlem13_2 $f wff ch $.
	fmerlem13_3 $f wff th $.
	merlem13 $p |- ( ( ph -> ps ) -> ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $= fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_0 wi fmerlem13_0 wi fmerlem13_0 fmerlem13_1 wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi fmerlem13_1 wi wi fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_0 wi fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_0 wi fmerlem13_0 wi wi fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_0 wi fmerlem13_0 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_0 wi fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_0 wi fmerlem13_0 wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn fmerlem13_2 fmerlem13_3 merlem12 fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn fmerlem13_1 wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wn fmerlem13_0 wn wn wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wn fmerlem13_0 wn wn wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn fmerlem13_1 wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wn fmerlem13_0 wn wn wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi fmerlem13_0 wn wn wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wn fmerlem13_0 wn wn wi fmerlem13_0 wn wn fmerlem13_2 fmerlem13_3 merlem12 fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi fmerlem13_0 wn wn merlem5 ax-mp fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn fmerlem13_1 wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wn fmerlem13_0 wn wn wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi merlem6 ax-mp fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn fmerlem13_1 fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi ax-meredith ax-mp ax-mp fmerlem13_0 fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_0 wi merlem6 ax-mp fmerlem13_1 fmerlem13_1 wi fmerlem13_0 wn fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi wn wi wi fmerlem13_0 wi fmerlem13_0 merlem11 ax-mp fmerlem13_1 fmerlem13_1 fmerlem13_0 fmerlem13_3 fmerlem13_2 wn wn fmerlem13_2 wi wi fmerlem13_0 wn wn wi fmerlem13_0 ax-meredith ax-mp $.
$}
$( 1 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fluk-1_0 $f wff ph $.
	fluk-1_1 $f wff ps $.
	fluk-1_2 $f wff ch $.
	luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= fluk-1_2 fluk-1_2 wi fluk-1_0 wn wn wn fluk-1_0 wn wi wi fluk-1_0 wn wn wi fluk-1_1 wi fluk-1_1 fluk-1_2 wi fluk-1_0 fluk-1_2 wi wi wi fluk-1_0 fluk-1_1 wi fluk-1_1 fluk-1_2 wi fluk-1_0 fluk-1_2 wi wi wi fluk-1_2 fluk-1_2 fluk-1_0 wn wn fluk-1_0 fluk-1_1 ax-meredith fluk-1_1 fluk-1_2 wi fluk-1_0 fluk-1_2 wi wi fluk-1_0 wi fluk-1_0 fluk-1_1 wi wn wn wn fluk-1_0 fluk-1_1 wi wn wi wi fluk-1_0 fluk-1_1 wi wn wn wi fluk-1_2 fluk-1_2 wi fluk-1_0 wn wn wn fluk-1_0 wn wi wi fluk-1_0 wn wn wi fluk-1_1 wi wi fluk-1_2 fluk-1_2 wi fluk-1_0 wn wn wn fluk-1_0 wn wi wi fluk-1_0 wn wn wi fluk-1_1 wi fluk-1_1 fluk-1_2 wi fluk-1_0 fluk-1_2 wi wi wi fluk-1_0 fluk-1_1 wi fluk-1_1 fluk-1_2 wi fluk-1_0 fluk-1_2 wi wi wi wi fluk-1_0 fluk-1_1 wi fluk-1_2 fluk-1_2 wi fluk-1_0 wn wn wn fluk-1_0 wn wi wi fluk-1_0 wn wn wi fluk-1_1 wi wi fluk-1_1 fluk-1_2 wi fluk-1_0 fluk-1_2 wi wi fluk-1_0 wi fluk-1_0 fluk-1_1 wi wn wn wn fluk-1_0 fluk-1_1 wi wn wi wi fluk-1_0 fluk-1_1 wi wn wn wi fluk-1_2 fluk-1_2 wi fluk-1_0 wn wn wn fluk-1_0 wn wi wi fluk-1_0 wn wn wi fluk-1_1 wi wi fluk-1_0 fluk-1_1 fluk-1_0 wn fluk-1_2 fluk-1_2 wi merlem13 fluk-1_0 fluk-1_1 wi fluk-1_2 fluk-1_2 wi fluk-1_0 wn wn wn fluk-1_0 wn wi wi fluk-1_0 wn wn wi fluk-1_1 wi fluk-1_0 fluk-1_1 wi wn fluk-1_1 fluk-1_2 wi fluk-1_0 fluk-1_2 wi wi fluk-1_0 wi merlem13 ax-mp fluk-1_1 fluk-1_2 wi fluk-1_0 fluk-1_2 wi wi fluk-1_0 fluk-1_0 fluk-1_1 wi wn wn fluk-1_0 fluk-1_1 wi fluk-1_2 fluk-1_2 wi fluk-1_0 wn wn wn fluk-1_0 wn wi wi fluk-1_0 wn wn wi fluk-1_1 wi ax-meredith ax-mp ax-mp $.
$}
$( 2 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fluk-2_0 $f wff ph $.
	luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $= fluk-2_0 wn fluk-2_0 wi fluk-2_0 wn fluk-2_0 wi fluk-2_0 wi wi fluk-2_0 wn fluk-2_0 wi fluk-2_0 wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 wn wi fluk-2_0 wn wi fluk-2_0 wn fluk-2_0 wi fluk-2_0 wn fluk-2_0 wi fluk-2_0 wi wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 wn wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 wn wi fluk-2_0 wn wi wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 wn wi fluk-2_0 wn wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 wn wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 wn wi fluk-2_0 wn wi wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn merlem5 fluk-2_0 wn fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 wn wi fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi merlem4 ax-mp fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn wi fluk-2_0 wn wn fluk-2_0 wn fluk-2_0 wi wn wi wi fluk-2_0 wn wi fluk-2_0 wn merlem11 ax-mp fluk-2_0 fluk-2_0 wn fluk-2_0 wi wn fluk-2_0 wn fluk-2_0 wn fluk-2_0 wi fluk-2_0 wn ax-meredith ax-mp fluk-2_0 wn fluk-2_0 wi fluk-2_0 merlem11 ax-mp $.
$}
$( 3 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fluk-3_0 $f wff ph $.
	fluk-3_1 $f wff ps $.
	luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $= fluk-3_0 wn fluk-3_0 wn fluk-3_1 wi wi fluk-3_0 wn fluk-3_1 wi wi fluk-3_0 fluk-3_0 wn fluk-3_1 wi wi fluk-3_0 wn fluk-3_1 merlem11 fluk-3_0 fluk-3_1 fluk-3_0 wn fluk-3_0 wn fluk-3_1 wi merlem1 ax-mp $.
$}

