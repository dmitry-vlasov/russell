$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz axioms from Meredith's sole axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Carew Meredith's sole axiom for propositional calculus.  This amazing
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
	$v ph ps ch th ta  $.
	f0_meredith $f wff ph $.
	f1_meredith $f wff ps $.
	f2_meredith $f wff ch $.
	f3_meredith $f wff th $.
	f4_meredith $f wff ta $.
	p_meredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $= f0_meredith f1_meredith p_pm2.21 f2_meredith f3_meredith a_ax-3 f0_meredith a_wn f0_meredith f1_meredith a_wi f2_meredith a_wn f3_meredith a_wn a_wi f3_meredith f2_meredith a_wi p_imim12i f0_meredith f1_meredith a_wi f2_meredith a_wn f3_meredith a_wn a_wi a_wi f0_meredith a_wn f3_meredith f2_meredith p_com13 f3_meredith f0_meredith f0_meredith f1_meredith a_wi f2_meredith a_wn f3_meredith a_wn a_wi a_wi f2_meredith a_wi p_con1d f3_meredith f0_meredith f1_meredith a_wi f2_meredith a_wn f3_meredith a_wn a_wi a_wi f2_meredith a_wi a_wn f0_meredith p_com12 f0_meredith f1_meredith a_wi f2_meredith a_wn f3_meredith a_wn a_wi a_wi f2_meredith a_wi a_wn f3_meredith f0_meredith a_wi f4_meredith f0_meredith a_wi p_a1d f4_meredith f3_meredith a_ax-1 f4_meredith f3_meredith f4_meredith f0_meredith p_imim1d f0_meredith f1_meredith a_wi f2_meredith a_wn f3_meredith a_wn a_wi a_wi f2_meredith a_wi f4_meredith f4_meredith f0_meredith a_wi f3_meredith f0_meredith a_wi a_wi p_ja $.
$}

$(Alias for ~ meredith which "verify markup *" will match to
     ~ ax-meredith .  (Contributed by NM, 21-Aug-2017.)
     (New usage is discouraged.) $)

${
	$v ph ps ch th ta  $.
	f0_axmeredith $f wff ph $.
	f1_axmeredith $f wff ps $.
	f2_axmeredith $f wff ch $.
	f3_axmeredith $f wff th $.
	f4_axmeredith $f wff ta $.
	p_axmeredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $= f0_axmeredith f1_axmeredith f2_axmeredith f3_axmeredith f4_axmeredith p_meredith $.
$}

$(Theorem ~ meredith restated as an axiom.  This will allow us to ensure
     that the rederivation of ~ ax1 , ~ ax2 , and ~ ax3 below depend only on
     Meredith's sole axiom and not accidentally on a previous theorem above.
     Outside of this section, we will not make use of this axiom.  (Contributed
     by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch th ta  $.
	f0_ax-meredith $f wff ph $.
	f1_ax-meredith $f wff ps $.
	f2_ax-meredith $f wff ch $.
	f3_ax-meredith $f wff th $.
	f4_ax-meredith $f wff ta $.
	a_ax-meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.
$}

$(Step 3 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (The step numbers refer to Meredith's original paper.)  (Contributed by
     NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch ta  $.
	f0_merlem1 $f wff ph $.
	f1_merlem1 $f wff ps $.
	f2_merlem1 $f wff ch $.
	f3_merlem1 $f wff ta $.
	p_merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $= f0_merlem1 a_wn f1_merlem1 f3_merlem1 a_wn f2_merlem1 a_wn a_wi f0_merlem1 a_wn f1_merlem1 a_wi a_wn f3_merlem1 a_ax-meredith f0_merlem1 a_wn f1_merlem1 a_wi f3_merlem1 a_wn f2_merlem1 a_wn a_wi a_wn f0_merlem1 a_wn f1_merlem1 a_wi a_wn a_wn a_wi f3_merlem1 f2_merlem1 f3_merlem1 f0_merlem1 a_wn a_wi f0_merlem1 a_wn f1_merlem1 a_wi a_wn f0_merlem1 a_wn a_wi a_wi a_ax-meredith f0_merlem1 a_wn f1_merlem1 a_wi f3_merlem1 a_wn f2_merlem1 a_wn a_wi a_wn f0_merlem1 a_wn f1_merlem1 a_wi a_wn a_wn a_wi a_wi f3_merlem1 a_wn f2_merlem1 a_wn a_wi a_wi f3_merlem1 a_wi f3_merlem1 f0_merlem1 a_wn a_wi f0_merlem1 a_wn f1_merlem1 a_wi a_wn f0_merlem1 a_wn a_wi a_wi a_wi f3_merlem1 f0_merlem1 a_wn a_wi f0_merlem1 a_wn f1_merlem1 a_wi a_wn f0_merlem1 a_wn a_wi a_wi f0_merlem1 a_wn f1_merlem1 a_wi a_wi f2_merlem1 f0_merlem1 a_wn f1_merlem1 a_wi a_wi a_wi a_ax-mp f3_merlem1 f0_merlem1 a_wn f0_merlem1 a_wn f1_merlem1 a_wi f0_merlem1 f2_merlem1 f0_merlem1 a_wn f1_merlem1 a_wi a_wi a_ax-meredith f3_merlem1 f0_merlem1 a_wn a_wi f0_merlem1 a_wn f1_merlem1 a_wi a_wn f0_merlem1 a_wn a_wi a_wi f0_merlem1 a_wn f1_merlem1 a_wi a_wi f2_merlem1 f0_merlem1 a_wn f1_merlem1 a_wi a_wi a_wi f2_merlem1 f0_merlem1 a_wn f1_merlem1 a_wi a_wi f3_merlem1 a_wi f0_merlem1 f3_merlem1 a_wi a_wi a_ax-mp $.
$}

$(Step 4 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ch th  $.
	f0_merlem2 $f wff ph $.
	f1_merlem2 $f wff ch $.
	f2_merlem2 $f wff th $.
	p_merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $= f0_merlem2 f2_merlem2 a_wn f1_merlem2 f1_merlem2 a_wi f0_merlem2 p_merlem1 f1_merlem2 f1_merlem2 f0_merlem2 f2_merlem2 f0_merlem2 f0_merlem2 a_wi a_ax-meredith f1_merlem2 f1_merlem2 a_wi f0_merlem2 a_wn f2_merlem2 a_wn a_wi a_wi f0_merlem2 a_wi f0_merlem2 f0_merlem2 a_wi a_wi f0_merlem2 f0_merlem2 a_wi f1_merlem2 a_wi f2_merlem2 f1_merlem2 a_wi a_wi a_ax-mp $.
$}

$(Step 7 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_merlem3 $f wff ph $.
	f1_merlem3 $f wff ps $.
	f2_merlem3 $f wff ch $.
	p_merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $= f2_merlem3 a_wn f2_merlem3 a_wn f2_merlem3 a_wn a_wi f0_merlem3 f0_merlem3 a_wi p_merlem2 f2_merlem3 a_wn f2_merlem3 a_wn a_wi f0_merlem3 f0_merlem3 a_wi f2_merlem3 a_wn f2_merlem3 a_wn a_wi a_wi f2_merlem3 f0_merlem3 a_wi f1_merlem3 a_wn f1_merlem3 a_wn a_wi a_wi f1_merlem3 a_wi p_merlem2 f2_merlem3 a_wn f2_merlem3 a_wn a_wi f2_merlem3 a_wn f2_merlem3 a_wn a_wi a_wi f0_merlem3 f0_merlem3 a_wi f2_merlem3 a_wn f2_merlem3 a_wn a_wi a_wi a_wi f2_merlem3 f0_merlem3 a_wi f1_merlem3 a_wn f1_merlem3 a_wn a_wi a_wi f1_merlem3 a_wi f0_merlem3 f0_merlem3 a_wi f2_merlem3 a_wn f2_merlem3 a_wn a_wi a_wi a_wi a_ax-mp f2_merlem3 f0_merlem3 f1_merlem3 f1_merlem3 f0_merlem3 f0_merlem3 a_wi f2_merlem3 a_wn f2_merlem3 a_wn a_wi a_wi a_ax-meredith f2_merlem3 f0_merlem3 a_wi f1_merlem3 a_wn f1_merlem3 a_wn a_wi a_wi f1_merlem3 a_wi f0_merlem3 f0_merlem3 a_wi f2_merlem3 a_wn f2_merlem3 a_wn a_wi a_wi a_wi f0_merlem3 f0_merlem3 a_wi f2_merlem3 a_wn f2_merlem3 a_wn a_wi a_wi f2_merlem3 a_wi f1_merlem3 f2_merlem3 a_wi a_wi a_ax-mp f0_merlem3 f0_merlem3 f2_merlem3 f2_merlem3 f1_merlem3 f2_merlem3 a_wi a_ax-meredith f0_merlem3 f0_merlem3 a_wi f2_merlem3 a_wn f2_merlem3 a_wn a_wi a_wi f2_merlem3 a_wi f1_merlem3 f2_merlem3 a_wi a_wi f1_merlem3 f2_merlem3 a_wi f0_merlem3 a_wi f2_merlem3 f0_merlem3 a_wi a_wi a_ax-mp $.
$}

$(Step 8 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph th ta  $.
	f0_merlem4 $f wff ph $.
	f1_merlem4 $f wff th $.
	f2_merlem4 $f wff ta $.
	p_merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $= f0_merlem4 f0_merlem4 f1_merlem4 f1_merlem4 f2_merlem4 a_ax-meredith f2_merlem4 f0_merlem4 a_wi f1_merlem4 f0_merlem4 a_wi a_wi f0_merlem4 f0_merlem4 a_wi f1_merlem4 a_wn f1_merlem4 a_wn a_wi a_wi f1_merlem4 a_wi f2_merlem4 p_merlem3 f0_merlem4 f0_merlem4 a_wi f1_merlem4 a_wn f1_merlem4 a_wn a_wi a_wi f1_merlem4 a_wi f2_merlem4 a_wi f2_merlem4 f0_merlem4 a_wi f1_merlem4 f0_merlem4 a_wi a_wi a_wi f2_merlem4 f2_merlem4 f0_merlem4 a_wi f1_merlem4 f0_merlem4 a_wi a_wi a_wi a_ax-mp $.
$}

$(Step 11 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_merlem5 $f wff ph $.
	f1_merlem5 $f wff ps $.
	p_merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $= f1_merlem5 f1_merlem5 f1_merlem5 f1_merlem5 f1_merlem5 a_ax-meredith f1_merlem5 f1_merlem5 f1_merlem5 f0_merlem5 a_wn a_wn f0_merlem5 a_ax-meredith f0_merlem5 a_wn f1_merlem5 f0_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn p_merlem1 f0_merlem5 f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f0_merlem5 a_wn a_wn a_wn a_wi a_wi f1_merlem5 a_wi f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn a_wi f0_merlem5 a_wn f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn a_wi a_wi p_merlem4 f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn a_wi f0_merlem5 a_wn f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn a_wi a_wi f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn a_wi f0_merlem5 a_wn f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn a_wi a_wi f0_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f0_merlem5 a_wn a_wn a_wn a_wi a_wi f1_merlem5 a_wi f0_merlem5 a_wi a_wi a_ax-mp f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn f0_merlem5 f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f0_merlem5 a_wn a_wn a_wn a_wi a_wi f1_merlem5 a_wi f0_merlem5 a_wi a_ax-meredith f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn a_wi f0_merlem5 a_wn f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi a_wn a_wi a_wi f0_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f0_merlem5 a_wn a_wn a_wn a_wi a_wi f1_merlem5 a_wi f0_merlem5 a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f0_merlem5 a_wn a_wn a_wn a_wi a_wi f1_merlem5 a_wi f0_merlem5 a_wi f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi a_wi a_wi a_ax-mp f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f0_merlem5 a_wn a_wn a_wn a_wi a_wi f1_merlem5 a_wi f0_merlem5 a_wi f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi a_wi a_ax-mp f1_merlem5 f1_merlem5 a_wi f1_merlem5 a_wn f1_merlem5 a_wn a_wi a_wi f1_merlem5 a_wi f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi f1_merlem5 f1_merlem5 a_wi a_wi a_wi f0_merlem5 f1_merlem5 a_wi f0_merlem5 a_wn a_wn f1_merlem5 a_wi a_wi a_ax-mp $.
$}

$(Step 12 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_merlem6 $f wff ph $.
	f1_merlem6 $f wff ps $.
	f2_merlem6 $f wff ch $.
	f3_merlem6 $f wff th $.
	p_merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $= f0_merlem6 f3_merlem6 f1_merlem6 f2_merlem6 a_wi p_merlem4 f1_merlem6 f2_merlem6 a_wi f0_merlem6 a_wi f3_merlem6 f0_merlem6 a_wi a_wi f1_merlem6 f2_merlem6 p_merlem3 f1_merlem6 f2_merlem6 a_wi f1_merlem6 f2_merlem6 a_wi f0_merlem6 a_wi f3_merlem6 f0_merlem6 a_wi a_wi a_wi f2_merlem6 f1_merlem6 f2_merlem6 a_wi f0_merlem6 a_wi f3_merlem6 f0_merlem6 a_wi a_wi a_wi a_ax-mp $.
$}

$(Between steps 14 and 15 of Meredith's proof of Lukasiewicz axioms from his
     sole axiom.  (Contributed by NM, 22-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch th ta  $.
	f0_merlem7 $f wff ph $.
	f1_merlem7 $f wff ps $.
	f2_merlem7 $f wff ch $.
	f3_merlem7 $f wff th $.
	f4_merlem7 $f wff ta $.
	p_merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) -> ( -. th -> -. ps ) ) -> th ) ) ) $= f3_merlem7 f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f1_merlem7 f2_merlem7 a_wi p_merlem4 f0_merlem7 a_wn f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi f2_merlem7 a_wn p_merlem6 f2_merlem7 f4_merlem7 f3_merlem7 f1_merlem7 f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi f0_merlem7 a_wn a_wi f2_merlem7 a_wn f0_merlem7 a_wn a_wi a_wi a_ax-meredith f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi f0_merlem7 a_wn a_wi f2_merlem7 a_wn f0_merlem7 a_wn a_wi a_wi a_wi f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi f0_merlem7 a_wn a_wi f2_merlem7 a_wn f0_merlem7 a_wn a_wi a_wi f2_merlem7 a_wi f1_merlem7 f2_merlem7 a_wi a_wi a_ax-mp f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi f0_merlem7 a_wn f2_merlem7 f0_merlem7 f1_merlem7 f2_merlem7 a_wi a_ax-meredith f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi f0_merlem7 a_wn a_wi f2_merlem7 a_wn f0_merlem7 a_wn a_wi a_wi f2_merlem7 a_wi f1_merlem7 f2_merlem7 a_wi a_wi f1_merlem7 f2_merlem7 a_wi f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi a_wi f0_merlem7 f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi a_wi a_wi a_ax-mp f1_merlem7 f2_merlem7 a_wi f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi a_wi f0_merlem7 f1_merlem7 f2_merlem7 a_wi f3_merlem7 a_wi f2_merlem7 f4_merlem7 a_wi f3_merlem7 a_wn f1_merlem7 a_wn a_wi a_wi f3_merlem7 a_wi a_wi a_wi a_ax-mp $.
$}

$(Step 15 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ps ch th ta  $.
	f0_merlem8 $f wff ps $.
	f1_merlem8 $f wff ch $.
	f2_merlem8 $f wff th $.
	f3_merlem8 $f wff ta $.
	i0_merlem8 $f wff ph $.
	p_merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) -> ( -. th -> -. ps ) ) -> th ) ) $= i0_merlem8 i0_merlem8 i0_merlem8 i0_merlem8 i0_merlem8 a_ax-meredith i0_merlem8 i0_merlem8 a_wi i0_merlem8 a_wn i0_merlem8 a_wn a_wi a_wi i0_merlem8 a_wi i0_merlem8 a_wi i0_merlem8 i0_merlem8 a_wi i0_merlem8 i0_merlem8 a_wi a_wi a_wi f0_merlem8 f1_merlem8 f2_merlem8 f3_merlem8 p_merlem7 i0_merlem8 i0_merlem8 a_wi i0_merlem8 a_wn i0_merlem8 a_wn a_wi a_wi i0_merlem8 a_wi i0_merlem8 a_wi i0_merlem8 i0_merlem8 a_wi i0_merlem8 i0_merlem8 a_wi a_wi a_wi f0_merlem8 f1_merlem8 a_wi f2_merlem8 a_wi f1_merlem8 f3_merlem8 a_wi f2_merlem8 a_wn f0_merlem8 a_wn a_wi a_wi f2_merlem8 a_wi a_wi a_ax-mp $.
$}

$(Step 18 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch th ta et  $.
	f0_merlem9 $f wff ph $.
	f1_merlem9 $f wff ps $.
	f2_merlem9 $f wff ch $.
	f3_merlem9 $f wff th $.
	f4_merlem9 $f wff ta $.
	f5_merlem9 $f wff et $.
	p_merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) -> ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $= f5_merlem9 a_wn f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi f1_merlem9 a_wn p_merlem6 f3_merlem9 f1_merlem9 f4_merlem9 a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wn f3_merlem9 a_wn a_wi a_wn f0_merlem9 a_wn a_wi p_merlem8 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wi f1_merlem9 f4_merlem9 a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wn f3_merlem9 a_wn a_wi a_wn f0_merlem9 a_wn a_wi a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wn f3_merlem9 a_wn a_wi a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wi a_ax-mp f1_merlem9 f4_merlem9 f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wn f3_merlem9 a_wn a_wi f0_merlem9 f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_ax-meredith f1_merlem9 f4_merlem9 a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wn f3_merlem9 a_wn a_wi a_wn f0_merlem9 a_wn a_wi a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wn f3_merlem9 a_wn a_wi a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi f1_merlem9 a_wi f0_merlem9 f1_merlem9 a_wi a_wi a_ax-mp f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn f1_merlem9 f5_merlem9 f0_merlem9 f1_merlem9 a_wi a_ax-meredith f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi f5_merlem9 a_wn a_wi f1_merlem9 a_wn f5_merlem9 a_wn a_wi a_wi f1_merlem9 a_wi f0_merlem9 f1_merlem9 a_wi a_wi f0_merlem9 f1_merlem9 a_wi f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi a_wi f5_merlem9 f2_merlem9 f3_merlem9 f1_merlem9 f4_merlem9 a_wi a_wi a_wi a_wi a_wi a_ax-mp $.
$}

$(Step 19 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps th  $.
	f0_merlem10 $f wff ph $.
	f1_merlem10 $f wff ps $.
	f2_merlem10 $f wff th $.
	p_merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $= f0_merlem10 f0_merlem10 f0_merlem10 f0_merlem10 f0_merlem10 a_ax-meredith f0_merlem10 f1_merlem10 a_wi f0_merlem10 f0_merlem10 f2_merlem10 f0_merlem10 a_ax-meredith f0_merlem10 f1_merlem10 a_wi f0_merlem10 a_wi f0_merlem10 a_wn f2_merlem10 a_wn a_wi a_wi f0_merlem10 a_wi f0_merlem10 f0_merlem10 f0_merlem10 f1_merlem10 a_wi a_wi f2_merlem10 f1_merlem10 f0_merlem10 f0_merlem10 a_wi f0_merlem10 a_wn f0_merlem10 a_wn a_wi a_wi f0_merlem10 a_wi f0_merlem10 a_wi f0_merlem10 f0_merlem10 a_wi f0_merlem10 f0_merlem10 a_wi a_wi a_wi p_merlem9 f0_merlem10 f1_merlem10 a_wi f0_merlem10 a_wi f0_merlem10 a_wn f2_merlem10 a_wn a_wi a_wi f0_merlem10 a_wi f0_merlem10 a_wi f0_merlem10 f0_merlem10 f1_merlem10 a_wi a_wi f2_merlem10 f0_merlem10 f1_merlem10 a_wi a_wi a_wi a_wi f0_merlem10 f0_merlem10 a_wi f0_merlem10 a_wn f0_merlem10 a_wn a_wi a_wi f0_merlem10 a_wi f0_merlem10 a_wi f0_merlem10 f0_merlem10 a_wi f0_merlem10 f0_merlem10 a_wi a_wi a_wi f0_merlem10 f0_merlem10 f1_merlem10 a_wi a_wi f2_merlem10 f0_merlem10 f1_merlem10 a_wi a_wi a_wi a_wi a_ax-mp f0_merlem10 f0_merlem10 a_wi f0_merlem10 a_wn f0_merlem10 a_wn a_wi a_wi f0_merlem10 a_wi f0_merlem10 a_wi f0_merlem10 f0_merlem10 a_wi f0_merlem10 f0_merlem10 a_wi a_wi a_wi f0_merlem10 f0_merlem10 f1_merlem10 a_wi a_wi f2_merlem10 f0_merlem10 f1_merlem10 a_wi a_wi a_wi a_ax-mp $.
$}

$(Step 20 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_merlem11 $f wff ph $.
	f1_merlem11 $f wff ps $.
	p_merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $= f0_merlem11 f0_merlem11 f0_merlem11 f0_merlem11 f0_merlem11 a_ax-meredith f0_merlem11 f1_merlem11 f0_merlem11 f0_merlem11 f1_merlem11 a_wi a_wi p_merlem10 f0_merlem11 f0_merlem11 f1_merlem11 a_wi a_wi f0_merlem11 f1_merlem11 a_wi f0_merlem11 f0_merlem11 a_wi f0_merlem11 a_wn f0_merlem11 a_wn a_wi a_wi f0_merlem11 a_wi f0_merlem11 a_wi f0_merlem11 f0_merlem11 a_wi f0_merlem11 f0_merlem11 a_wi a_wi a_wi p_merlem10 f0_merlem11 f0_merlem11 f1_merlem11 a_wi a_wi f0_merlem11 f0_merlem11 f1_merlem11 a_wi a_wi f0_merlem11 f1_merlem11 a_wi a_wi a_wi f0_merlem11 f0_merlem11 a_wi f0_merlem11 a_wn f0_merlem11 a_wn a_wi a_wi f0_merlem11 a_wi f0_merlem11 a_wi f0_merlem11 f0_merlem11 a_wi f0_merlem11 f0_merlem11 a_wi a_wi a_wi f0_merlem11 f0_merlem11 f1_merlem11 a_wi a_wi f0_merlem11 f1_merlem11 a_wi a_wi a_wi a_ax-mp f0_merlem11 f0_merlem11 a_wi f0_merlem11 a_wn f0_merlem11 a_wn a_wi a_wi f0_merlem11 a_wi f0_merlem11 a_wi f0_merlem11 f0_merlem11 a_wi f0_merlem11 f0_merlem11 a_wi a_wi a_wi f0_merlem11 f0_merlem11 f1_merlem11 a_wi a_wi f0_merlem11 f1_merlem11 a_wi a_wi a_ax-mp $.
$}

$(Step 28 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ch th  $.
	f0_merlem12 $f wff ph $.
	f1_merlem12 $f wff ch $.
	f2_merlem12 $f wff th $.
	p_merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $= f1_merlem12 f1_merlem12 p_merlem5 f1_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi f2_merlem12 p_merlem2 f1_merlem12 f1_merlem12 a_wi f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi a_ax-mp f0_merlem12 f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f0_merlem12 a_wi f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi p_merlem4 f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f0_merlem12 a_wi f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f0_merlem12 a_wi f0_merlem12 a_wi a_wi a_ax-mp f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f0_merlem12 a_wi f0_merlem12 p_merlem11 f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f0_merlem12 a_wi f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f0_merlem12 a_wi f0_merlem12 a_wi a_wi f2_merlem12 f1_merlem12 a_wn a_wn f1_merlem12 a_wi a_wi f0_merlem12 a_wi f0_merlem12 a_wi a_ax-mp $.
$}

$(Step 35 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_merlem13 $f wff ph $.
	f1_merlem13 $f wff ps $.
	f2_merlem13 $f wff ch $.
	f3_merlem13 $f wff th $.
	p_merlem13 $p |- ( ( ph -> ps ) -> ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $= f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn f2_merlem13 f3_merlem13 p_merlem12 f0_merlem13 a_wn a_wn f2_merlem13 f3_merlem13 p_merlem12 f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi f0_merlem13 a_wn a_wn p_merlem5 f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi f0_merlem13 a_wn a_wn a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wn f0_merlem13 a_wn a_wn a_wi a_ax-mp f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn f1_merlem13 a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wn f0_merlem13 a_wn a_wn a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi p_merlem6 f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wn f0_merlem13 a_wn a_wn a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn f1_merlem13 a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wn f0_merlem13 a_wn a_wn a_wi a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi a_ax-mp f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn f1_merlem13 f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_ax-meredith f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn f1_merlem13 a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wn f0_merlem13 a_wn a_wn a_wi a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi a_ax-mp f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_ax-mp f0_merlem13 f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f0_merlem13 a_wi p_merlem6 f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f0_merlem13 a_wi f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f0_merlem13 a_wi f0_merlem13 a_wi a_wi a_ax-mp f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f0_merlem13 a_wi f0_merlem13 p_merlem11 f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f0_merlem13 a_wi f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f0_merlem13 a_wi f0_merlem13 a_wi a_wi f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f0_merlem13 a_wi f0_merlem13 a_wi a_ax-mp f1_merlem13 f1_merlem13 f0_merlem13 f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi f0_merlem13 a_ax-meredith f1_merlem13 f1_merlem13 a_wi f0_merlem13 a_wn f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi a_wn a_wi a_wi f0_merlem13 a_wi f0_merlem13 a_wi f0_merlem13 f1_merlem13 a_wi f3_merlem13 f2_merlem13 a_wn a_wn f2_merlem13 a_wi a_wi f0_merlem13 a_wn a_wn a_wi f1_merlem13 a_wi a_wi a_ax-mp $.
$}

$(1 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_luk-1 $f wff ph $.
	f1_luk-1 $f wff ps $.
	f2_luk-1 $f wff ch $.
	p_luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= f2_luk-1 f2_luk-1 f0_luk-1 a_wn a_wn f0_luk-1 f1_luk-1 a_ax-meredith f0_luk-1 f1_luk-1 f0_luk-1 a_wn f2_luk-1 f2_luk-1 a_wi p_merlem13 f0_luk-1 f1_luk-1 a_wi f2_luk-1 f2_luk-1 a_wi f0_luk-1 a_wn a_wn a_wn f0_luk-1 a_wn a_wi a_wi f0_luk-1 a_wn a_wn a_wi f1_luk-1 a_wi f0_luk-1 f1_luk-1 a_wi a_wn f1_luk-1 f2_luk-1 a_wi f0_luk-1 f2_luk-1 a_wi a_wi f0_luk-1 a_wi p_merlem13 f0_luk-1 f1_luk-1 a_wi f2_luk-1 f2_luk-1 a_wi f0_luk-1 a_wn a_wn a_wn f0_luk-1 a_wn a_wi a_wi f0_luk-1 a_wn a_wn a_wi f1_luk-1 a_wi a_wi f1_luk-1 f2_luk-1 a_wi f0_luk-1 f2_luk-1 a_wi a_wi f0_luk-1 a_wi f0_luk-1 f1_luk-1 a_wi a_wn a_wn a_wn f0_luk-1 f1_luk-1 a_wi a_wn a_wi a_wi f0_luk-1 f1_luk-1 a_wi a_wn a_wn a_wi f2_luk-1 f2_luk-1 a_wi f0_luk-1 a_wn a_wn a_wn f0_luk-1 a_wn a_wi a_wi f0_luk-1 a_wn a_wn a_wi f1_luk-1 a_wi a_wi a_ax-mp f1_luk-1 f2_luk-1 a_wi f0_luk-1 f2_luk-1 a_wi a_wi f0_luk-1 f0_luk-1 f1_luk-1 a_wi a_wn a_wn f0_luk-1 f1_luk-1 a_wi f2_luk-1 f2_luk-1 a_wi f0_luk-1 a_wn a_wn a_wn f0_luk-1 a_wn a_wi a_wi f0_luk-1 a_wn a_wn a_wi f1_luk-1 a_wi a_ax-meredith f1_luk-1 f2_luk-1 a_wi f0_luk-1 f2_luk-1 a_wi a_wi f0_luk-1 a_wi f0_luk-1 f1_luk-1 a_wi a_wn a_wn a_wn f0_luk-1 f1_luk-1 a_wi a_wn a_wi a_wi f0_luk-1 f1_luk-1 a_wi a_wn a_wn a_wi f2_luk-1 f2_luk-1 a_wi f0_luk-1 a_wn a_wn a_wn f0_luk-1 a_wn a_wi a_wi f0_luk-1 a_wn a_wn a_wi f1_luk-1 a_wi a_wi f2_luk-1 f2_luk-1 a_wi f0_luk-1 a_wn a_wn a_wn f0_luk-1 a_wn a_wi a_wi f0_luk-1 a_wn a_wn a_wi f1_luk-1 a_wi f1_luk-1 f2_luk-1 a_wi f0_luk-1 f2_luk-1 a_wi a_wi a_wi f0_luk-1 f1_luk-1 a_wi f1_luk-1 f2_luk-1 a_wi f0_luk-1 f2_luk-1 a_wi a_wi a_wi a_wi a_ax-mp f2_luk-1 f2_luk-1 a_wi f0_luk-1 a_wn a_wn a_wn f0_luk-1 a_wn a_wi a_wi f0_luk-1 a_wn a_wn a_wi f1_luk-1 a_wi f1_luk-1 f2_luk-1 a_wi f0_luk-1 f2_luk-1 a_wi a_wi a_wi f0_luk-1 f1_luk-1 a_wi f1_luk-1 f2_luk-1 a_wi f0_luk-1 f2_luk-1 a_wi a_wi a_wi a_ax-mp $.
$}

$(2 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph  $.
	f0_luk-2 $f wff ph $.
	p_luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $= f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn p_merlem5 f0_luk-2 a_wn f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 a_wn a_wi f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi p_merlem4 f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 a_wn a_wi f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 a_wn a_wi f0_luk-2 a_wn a_wi a_wi a_ax-mp f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 a_wn a_wi f0_luk-2 a_wn p_merlem11 f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 a_wn a_wi f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 a_wn a_wi f0_luk-2 a_wn a_wi a_wi f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 a_wn a_wi f0_luk-2 a_wn a_wi a_ax-mp f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn f0_luk-2 a_wn f0_luk-2 a_wn f0_luk-2 a_wi f0_luk-2 a_wn a_ax-meredith f0_luk-2 f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi f0_luk-2 a_wn a_wn f0_luk-2 a_wn f0_luk-2 a_wi a_wn a_wi a_wi f0_luk-2 a_wn a_wi f0_luk-2 a_wn a_wi f0_luk-2 a_wn f0_luk-2 a_wi f0_luk-2 a_wn f0_luk-2 a_wi f0_luk-2 a_wi a_wi a_ax-mp f0_luk-2 a_wn f0_luk-2 a_wi f0_luk-2 p_merlem11 f0_luk-2 a_wn f0_luk-2 a_wi f0_luk-2 a_wn f0_luk-2 a_wi f0_luk-2 a_wi a_wi f0_luk-2 a_wn f0_luk-2 a_wi f0_luk-2 a_wi a_ax-mp $.
$}

$(3 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_luk-3 $f wff ph $.
	f1_luk-3 $f wff ps $.
	p_luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $= f0_luk-3 a_wn f1_luk-3 p_merlem11 f0_luk-3 f1_luk-3 f0_luk-3 a_wn f0_luk-3 a_wn f1_luk-3 a_wi p_merlem1 f0_luk-3 a_wn f0_luk-3 a_wn f1_luk-3 a_wi a_wi f0_luk-3 a_wn f1_luk-3 a_wi a_wi f0_luk-3 f0_luk-3 a_wn f1_luk-3 a_wi a_wi a_ax-mp $.
$}


