$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Introduce the Axiom of Power Sets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Power Sets.  An axiom of Zermelo-Fraenkel set theory.  It
       states that a set ` y ` exists that includes the power set of a given
       set ` x ` i.e. contains every subset of ` x ` .  The variant ~ axpow2
       uses explicit subset notation.  A version using class notation is
       ~ pwex .  (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z w $.
	fax-pow_0 $f set x $.
	fax-pow_1 $f set y $.
	fax-pow_2 $f set z $.
	fax-pow_3 $f set w $.
	ax-pow $a |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $.
$}
$( Axiom of Power Sets expressed with the fewest number of different
       variables.  (Contributed by NM, 14-Aug-2003.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z w $.
	izfpow_0 $f set w $.
	fzfpow_0 $f set x $.
	fzfpow_1 $f set y $.
	fzfpow_2 $f set z $.
	zfpow $p |- E. x A. y ( A. x ( x e. y -> x e. z ) -> y e. x ) $= izfpow_0 cv fzfpow_1 cv wcel izfpow_0 cv fzfpow_2 cv wcel wi izfpow_0 wal fzfpow_1 cv fzfpow_0 cv wcel wi fzfpow_1 wal fzfpow_0 wex fzfpow_0 cv fzfpow_1 cv wcel fzfpow_0 cv fzfpow_2 cv wcel wi fzfpow_0 wal fzfpow_1 cv fzfpow_0 cv wcel wi fzfpow_1 wal fzfpow_0 wex fzfpow_2 fzfpow_0 fzfpow_1 izfpow_0 ax-pow izfpow_0 cv fzfpow_1 cv wcel izfpow_0 cv fzfpow_2 cv wcel wi izfpow_0 wal fzfpow_1 cv fzfpow_0 cv wcel wi fzfpow_1 wal fzfpow_0 cv fzfpow_1 cv wcel fzfpow_0 cv fzfpow_2 cv wcel wi fzfpow_0 wal fzfpow_1 cv fzfpow_0 cv wcel wi fzfpow_1 wal fzfpow_0 izfpow_0 cv fzfpow_1 cv wcel izfpow_0 cv fzfpow_2 cv wcel wi izfpow_0 wal fzfpow_1 cv fzfpow_0 cv wcel wi fzfpow_0 cv fzfpow_1 cv wcel fzfpow_0 cv fzfpow_2 cv wcel wi fzfpow_0 wal fzfpow_1 cv fzfpow_0 cv wcel wi fzfpow_1 izfpow_0 cv fzfpow_1 cv wcel izfpow_0 cv fzfpow_2 cv wcel wi izfpow_0 wal fzfpow_0 cv fzfpow_1 cv wcel fzfpow_0 cv fzfpow_2 cv wcel wi fzfpow_0 wal fzfpow_1 cv fzfpow_0 cv wcel izfpow_0 cv fzfpow_1 cv wcel izfpow_0 cv fzfpow_2 cv wcel wi fzfpow_0 cv fzfpow_1 cv wcel fzfpow_0 cv fzfpow_2 cv wcel wi izfpow_0 fzfpow_0 izfpow_0 cv fzfpow_0 cv wceq izfpow_0 cv fzfpow_1 cv wcel fzfpow_0 cv fzfpow_1 cv wcel izfpow_0 cv fzfpow_2 cv wcel fzfpow_0 cv fzfpow_2 cv wcel izfpow_0 fzfpow_0 fzfpow_1 elequ1 izfpow_0 fzfpow_0 fzfpow_2 elequ1 imbi12d cbvalv imbi1i albii exbii mpbi $.
$}
$( A variant of the Axiom of Power Sets ~ ax-pow using subset notation.
       Problem in {BellMachover] p. 466.  (Contributed by NM, 4-Jun-2006.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z w $.
	iaxpow2_0 $f set w $.
	faxpow2_0 $f set x $.
	faxpow2_1 $f set y $.
	faxpow2_2 $f set z $.
	axpow2 $p |- E. y A. z ( z C_ x -> z e. y ) $= faxpow2_2 cv faxpow2_0 cv wss faxpow2_2 cv faxpow2_1 cv wcel wi faxpow2_2 wal faxpow2_1 wex iaxpow2_0 cv faxpow2_2 cv wcel iaxpow2_0 cv faxpow2_0 cv wcel wi iaxpow2_0 wal faxpow2_2 cv faxpow2_1 cv wcel wi faxpow2_2 wal faxpow2_1 wex faxpow2_0 faxpow2_1 faxpow2_2 iaxpow2_0 ax-pow faxpow2_2 cv faxpow2_0 cv wss faxpow2_2 cv faxpow2_1 cv wcel wi faxpow2_2 wal iaxpow2_0 cv faxpow2_2 cv wcel iaxpow2_0 cv faxpow2_0 cv wcel wi iaxpow2_0 wal faxpow2_2 cv faxpow2_1 cv wcel wi faxpow2_2 wal faxpow2_1 faxpow2_2 cv faxpow2_0 cv wss faxpow2_2 cv faxpow2_1 cv wcel wi iaxpow2_0 cv faxpow2_2 cv wcel iaxpow2_0 cv faxpow2_0 cv wcel wi iaxpow2_0 wal faxpow2_2 cv faxpow2_1 cv wcel wi faxpow2_2 faxpow2_2 cv faxpow2_0 cv wss iaxpow2_0 cv faxpow2_2 cv wcel iaxpow2_0 cv faxpow2_0 cv wcel wi iaxpow2_0 wal faxpow2_2 cv faxpow2_1 cv wcel iaxpow2_0 faxpow2_2 cv faxpow2_0 cv dfss2 imbi1i albii exbii mpbir $.
$}
$( A variant of the Axiom of Power Sets ~ ax-pow .  For any set ` x ` ,
       there exists a set ` y ` whose members are exactly the subsets of ` x `
       i.e. the power set of ` x ` .  Axiom Pow of [BellMachover] p. 466.
       (Contributed by NM, 4-Jun-2006.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	faxpow3_0 $f set x $.
	faxpow3_1 $f set y $.
	faxpow3_2 $f set z $.
	axpow3 $p |- E. y A. z ( z C_ x <-> z e. y ) $= faxpow3_2 cv faxpow3_0 cv wss faxpow3_2 cv faxpow3_1 cv wcel wb faxpow3_2 wal faxpow3_1 wex faxpow3_2 cv faxpow3_1 cv wcel faxpow3_2 cv faxpow3_0 cv wss wb faxpow3_2 wal faxpow3_1 wex faxpow3_2 cv faxpow3_0 cv wss faxpow3_1 faxpow3_2 faxpow3_0 faxpow3_1 faxpow3_2 axpow2 bm1.3ii faxpow3_2 cv faxpow3_0 cv wss faxpow3_2 cv faxpow3_1 cv wcel wb faxpow3_2 wal faxpow3_2 cv faxpow3_1 cv wcel faxpow3_2 cv faxpow3_0 cv wss wb faxpow3_2 wal faxpow3_1 faxpow3_2 cv faxpow3_0 cv wss faxpow3_2 cv faxpow3_1 cv wcel wb faxpow3_2 cv faxpow3_1 cv wcel faxpow3_2 cv faxpow3_0 cv wss wb faxpow3_2 faxpow3_2 cv faxpow3_0 cv wss faxpow3_2 cv faxpow3_1 cv wcel bicom albii exbii mpbir $.
$}
$( Every set is an element of some other set.  See ~ elALT for a shorter
       proof using more axioms.  (Contributed by NM, 4-Jan-2002.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	iel_0 $f set z $.
	fel_0 $f set x $.
	fel_1 $f set y $.
	el $p |- E. y x e. y $= fel_1 cv iel_0 cv wcel fel_1 cv fel_0 cv wcel wi fel_1 wal iel_0 cv fel_1 cv wcel wi iel_0 wal fel_1 wex fel_0 cv fel_1 cv wcel fel_1 wex fel_1 iel_0 fel_0 zfpow fel_1 cv iel_0 cv wcel fel_1 cv fel_0 cv wcel wi fel_1 wal iel_0 cv fel_1 cv wcel wi iel_0 wal fel_0 cv fel_1 cv wcel fel_1 fel_1 cv iel_0 cv wcel fel_1 cv fel_0 cv wcel wi fel_1 wal iel_0 cv fel_1 cv wcel wi fel_0 cv fel_1 cv wcel iel_0 fel_0 iel_0 cv fel_0 cv wceq fel_1 cv iel_0 cv wcel fel_1 cv fel_0 cv wcel wi fel_1 wal iel_0 cv fel_1 cv wcel fel_0 cv fel_1 cv wcel iel_0 cv fel_0 cv wceq fel_1 cv iel_0 cv wcel fel_1 cv fel_0 cv wcel wi fel_1 iel_0 fel_0 fel_1 ax-14 alrimiv iel_0 fel_0 fel_1 ax-13 embantd spimv eximi ax-mp $.
$}
$( Power set axiom expressed in class notation.  Axiom 4 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 25-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$d A x y z $.
	ipwex_0 $f set x $.
	ipwex_1 $f set y $.
	ipwex_2 $f set z $.
	fpwex_0 $f class A $.
	epwex_0 $e |- A e. _V $.
	pwex $p |- ~P A e. _V $= ipwex_2 cv cpw cvv wcel fpwex_0 cpw cvv wcel ipwex_2 fpwex_0 epwex_0 ipwex_2 cv fpwex_0 wceq ipwex_2 cv cpw fpwex_0 cpw cvv ipwex_2 cv fpwex_0 pweq eleq1d ipwex_2 cv cpw ipwex_1 cv ipwex_2 cv wss ipwex_1 cab cvv ipwex_1 ipwex_2 cv df-pw ipwex_0 ipwex_1 cv ipwex_2 cv wss ipwex_1 cab ipwex_0 cv ipwex_1 cv ipwex_2 cv wss ipwex_1 cab wceq ipwex_0 wex ipwex_1 cv ipwex_0 cv wcel ipwex_1 cv ipwex_2 cv wss wb ipwex_1 wal ipwex_0 wex ipwex_1 cv ipwex_2 cv wss ipwex_0 ipwex_1 ipwex_2 ipwex_0 ipwex_1 axpow2 bm1.3ii ipwex_0 cv ipwex_1 cv ipwex_2 cv wss ipwex_1 cab wceq ipwex_1 cv ipwex_0 cv wcel ipwex_1 cv ipwex_2 cv wss wb ipwex_1 wal ipwex_0 ipwex_1 cv ipwex_2 cv wss ipwex_1 ipwex_0 cv abeq2 exbii mpbir issetri eqeltri vtocl $.
$}
$( Power set axiom expressed in class notation, with the sethood
       requirement as an antecedent.  Axiom 4 of [TakeutiZaring] p. 17.
       (Contributed by NM, 30-Oct-2003.) $)
${
	$v x $.
	$v A $.
	$v V $.
	$d x A $.
	ipwexg_0 $f set x $.
	fpwexg_0 $f class A $.
	fpwexg_1 $f class V $.
	pwexg $p |- ( A e. V -> ~P A e. _V ) $= ipwexg_0 cv cpw cvv wcel fpwexg_0 cpw cvv wcel ipwexg_0 fpwexg_0 fpwexg_1 ipwexg_0 cv fpwexg_0 wceq ipwexg_0 cv cpw fpwexg_0 cpw cvv ipwexg_0 cv fpwexg_0 pweq eleq1d ipwexg_0 cv ipwexg_0 vex pwex vtoclg $.
$}
$( Existence of a class of subsets.  (Contributed by NM, 15-Jul-2006.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v V $.
	$d x A $.
	fabssexg_0 $f wff ph $.
	fabssexg_1 $f set x $.
	fabssexg_2 $f class A $.
	fabssexg_3 $f class V $.
	abssexg $p |- ( A e. V -> { x | ( x C_ A /\ ph ) } e. _V ) $= fabssexg_2 fabssexg_3 wcel fabssexg_2 cpw cvv wcel fabssexg_1 cv fabssexg_2 wss fabssexg_0 wa fabssexg_1 cab cvv wcel fabssexg_2 fabssexg_3 pwexg fabssexg_2 cpw cvv wcel fabssexg_1 cv fabssexg_2 wss fabssexg_1 cab cvv wcel fabssexg_1 cv fabssexg_2 wss fabssexg_0 wa fabssexg_1 cab cvv wcel fabssexg_2 cpw fabssexg_1 cv fabssexg_2 wss fabssexg_1 cab cvv fabssexg_1 fabssexg_2 df-pw eleq1i fabssexg_1 cv fabssexg_2 wss fabssexg_0 wa fabssexg_1 cab fabssexg_1 cv fabssexg_2 wss fabssexg_1 cab wss fabssexg_1 cv fabssexg_2 wss fabssexg_1 cab cvv wcel fabssexg_1 cv fabssexg_2 wss fabssexg_0 wa fabssexg_1 cab cvv wcel fabssexg_1 cv fabssexg_2 wss fabssexg_0 wa fabssexg_1 cv fabssexg_2 wss fabssexg_1 fabssexg_1 cv fabssexg_2 wss fabssexg_0 simpl ss2abi fabssexg_1 cv fabssexg_2 wss fabssexg_0 wa fabssexg_1 cab fabssexg_1 cv fabssexg_2 wss fabssexg_1 cab cvv ssexg mpan sylbi syl $.
$}
$( A singleton is a set.  Theorem 7.13 of [Quine] p. 51, but proved using
       only Extensionality, Power Set, and Separation.  Unlike the proof of
       ~ zfpair , Replacement is not needed.  (Contributed by NM, 7-Aug-1994.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.)  See also ~ snex .
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v A $.
	fsnexALT_0 $f class A $.
	snexALT $p |- { A } e. _V $= fsnexALT_0 cpw cvv wcel fsnexALT_0 csn cvv wcel fsnexALT_0 csn fsnexALT_0 cpw wss fsnexALT_0 cpw cvv wcel fsnexALT_0 csn cvv wcel fsnexALT_0 snsspw fsnexALT_0 csn fsnexALT_0 cpw cvv ssexg mpan fsnexALT_0 cpw cvv wcel wn fsnexALT_0 cvv wcel wn fsnexALT_0 csn cvv wcel fsnexALT_0 cvv wcel fsnexALT_0 cpw cvv wcel fsnexALT_0 cvv pwexg con3i fsnexALT_0 cvv wcel wn fsnexALT_0 csn c0 cvv fsnexALT_0 cvv wcel wn fsnexALT_0 csn c0 wceq fsnexALT_0 snprc biimpi 0ex syl6eqel syl pm2.61i $.
$}
$( The power set of the empty set (the ordinal 1) is a set.  See also
     ~ p0exALT .  (Contributed by NM, 23-Dec-1993.) $)
${
	p0ex $p |- { (/) } e. _V $= c0 cpw c0 csn cvv pw0 c0 0ex pwex eqeltrri $.
$}
$( The power set of the empty set (the ordinal 1) is a set.  Alternate proof
     which is longer and quite different from the proof of ~ p0ex if ~ snexALT
     is expanded.  (Contributed by NM, 23-Dec-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	p0exALT $p |- { (/) } e. _V $= c0 snexALT $.
$}
$( The power set of the power set of the empty set (the ordinal 2) is a set.
     (Contributed by NM, 5-Aug-1993.) $)
${
	pp0ex $p |- { (/) , { (/) } } e. _V $= c0 csn cpw c0 c0 csn cpr cvv pwpw0 c0 csn p0ex pwex eqeltrri $.
$}
$( The ordinal number 3 is a set, proved without the Axiom of Union
     ~ ax-un .  (Contributed by NM, 2-May-2009.) $)
${
	ord3ex $p |- { (/) , { (/) } , { (/) , { (/) } } } e. _V $= c0 c0 csn c0 c0 csn cpr ctp c0 c0 csn cpr c0 c0 csn cpr csn cun cvv c0 c0 csn c0 c0 csn cpr df-tp c0 c0 csn cpr c0 c0 csn cpr csn cun c0 c0 csn cpr c0 csn csn c0 c0 csn cpr cpr cun c0 c0 csn cpr cpw c0 c0 csn cpr c0 csn csn c0 c0 csn cpr cpr cun cvv c0 c0 csn pwpr c0 c0 csn cpr pp0ex pwex eqeltrri c0 c0 csn cpr csn c0 csn csn c0 c0 csn cpr cpr wss c0 c0 csn cpr c0 c0 csn cpr csn cun c0 c0 csn cpr c0 csn csn c0 c0 csn cpr cpr cun wss c0 csn csn c0 c0 csn cpr snsspr2 c0 c0 csn cpr csn c0 csn csn c0 c0 csn cpr cpr c0 c0 csn cpr unss2 ax-mp ssexi eqeltri $.
$}
$( At least two sets exist (or in terms of first-order logic, the universe
       of discourse has two or more objects).  Note that we may not substitute
       the same variable for both ` x ` and ` y ` (as indicated by the distinct
       variable requirement), for otherwise we would contradict ~ stdpc6 .

       This theorem is proved directly from set theory axioms (no set theory
       definitions) and does not use ~ ax-ext or ~ ax-sep .  See ~ dtruALT for
       a shorter proof using these axioms.

       The proof makes use of dummy variables ` z ` and ` w ` which do not
       appear in the final theorem.  They must be distinct from each other and
       from ` x ` and ` y ` .  In other words, if we were to substitute ` x `
       for ` z ` throughout the proof, the proof would fail.  Although this
       requirement is made explicitly in the set.mm source file, it is implicit
       on the web page (i.e. doesn't appear in the "Distinct variable group").
       (Contributed by NM, 7-Nov-2006.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y z $.
	idtru_0 $f set z $.
	idtru_1 $f set w $.
	fdtru_0 $f set x $.
	fdtru_1 $f set y $.
	dtru $p |- -. A. x x = y $= fdtru_0 cv fdtru_1 cv wceq wn fdtru_0 wex fdtru_0 cv fdtru_1 cv wceq fdtru_0 wal wn idtru_1 cv idtru_0 cv wceq wn idtru_0 wex idtru_1 wex fdtru_0 cv fdtru_1 cv wceq wn fdtru_0 wex fdtru_0 cv idtru_1 cv wcel fdtru_0 cv idtru_0 cv wcel wn wa idtru_0 wex idtru_1 wex idtru_1 cv idtru_0 cv wceq wn idtru_0 wex idtru_1 wex fdtru_0 cv idtru_1 cv wcel fdtru_0 cv idtru_0 cv wcel wn wa idtru_0 wex idtru_1 wex fdtru_0 cv idtru_1 cv wcel idtru_1 wex fdtru_0 cv idtru_0 cv wcel wn idtru_0 wex fdtru_0 idtru_1 el fdtru_0 cv idtru_0 cv wcel wn fdtru_0 wal idtru_0 wex fdtru_0 cv idtru_0 cv wcel wn idtru_0 wex idtru_0 fdtru_0 ax-nul fdtru_0 cv idtru_0 cv wcel wn fdtru_0 wal fdtru_0 cv idtru_0 cv wcel wn idtru_0 fdtru_0 cv idtru_0 cv wcel wn fdtru_0 sp eximi ax-mp fdtru_0 cv idtru_1 cv wcel fdtru_0 cv idtru_0 cv wcel wn idtru_1 idtru_0 eeanv mpbir2an fdtru_0 cv idtru_1 cv wcel fdtru_0 cv idtru_0 cv wcel wn wa idtru_1 cv idtru_0 cv wceq wn idtru_1 idtru_0 fdtru_0 cv idtru_1 cv wcel idtru_1 cv idtru_0 cv wceq fdtru_0 cv idtru_0 cv wcel idtru_1 cv idtru_0 cv wceq fdtru_0 cv idtru_1 cv wcel fdtru_0 cv idtru_0 cv wcel idtru_1 idtru_0 fdtru_0 ax-14 com12 con3and 2eximi ax-mp idtru_1 cv idtru_0 cv wceq wn fdtru_0 cv fdtru_1 cv wceq wn fdtru_0 wex idtru_1 idtru_0 idtru_0 cv fdtru_1 cv wceq idtru_1 cv idtru_0 cv wceq wn fdtru_0 cv fdtru_1 cv wceq wn fdtru_0 wex wi idtru_0 cv fdtru_1 cv wceq idtru_1 cv idtru_0 cv wceq wn idtru_1 cv fdtru_1 cv wceq wn fdtru_0 cv fdtru_1 cv wceq wn fdtru_0 wex idtru_0 cv fdtru_1 cv wceq idtru_1 cv idtru_0 cv wceq idtru_1 cv fdtru_1 cv wceq idtru_0 fdtru_1 idtru_1 equequ2 notbid idtru_1 cv fdtru_1 cv wceq wn fdtru_0 cv fdtru_1 cv wceq wn fdtru_0 idtru_1 fdtru_0 cv idtru_1 cv wceq fdtru_0 cv fdtru_1 cv wceq idtru_1 cv fdtru_1 cv wceq fdtru_0 idtru_1 fdtru_1 ax-8 con3d spimev syl6bi idtru_0 cv fdtru_1 cv wceq wn fdtru_0 cv fdtru_1 cv wceq wn fdtru_0 wex idtru_1 cv idtru_0 cv wceq wn idtru_0 cv fdtru_1 cv wceq wn fdtru_0 cv fdtru_1 cv wceq wn fdtru_0 idtru_0 fdtru_0 cv idtru_0 cv wceq fdtru_0 cv fdtru_1 cv wceq idtru_0 cv fdtru_1 cv wceq fdtru_0 idtru_0 fdtru_1 ax-8 con3d spimev a1d pm2.61i exlimivv ax-mp fdtru_0 cv fdtru_1 cv wceq fdtru_0 exnal mpbi $.
$}
$( This theorem shows that axiom ~ ax-16 is redundant in the presence of
       theorem ~ dtru , which states simply that at least two things exist.
       This justifies the remark at
       ~ http://us.metamath.org/mpeuni/mmzfcnd.html#twoness (which links to
       this theorem).  (Contributed by NM, 7-Nov-2006.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fax16b_0 $f wff ph $.
	fax16b_1 $f set x $.
	fax16b_2 $f set y $.
	ax16b $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $= fax16b_1 cv fax16b_2 cv wceq fax16b_1 wal fax16b_0 fax16b_0 fax16b_1 wal wi fax16b_1 fax16b_2 dtru pm2.21i $.
$}
$( Existential uniqueness implies there is a value for which the wff
       argument is false.  (Contributed by NM, 24-Oct-2010.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	$d y ph $.
	ieunex_0 $f set y $.
	feunex_0 $f wff ph $.
	feunex_1 $f set x $.
	eunex $p |- ( E! x ph -> E. x -. ph ) $= feunex_0 feunex_1 wex feunex_0 feunex_1 cv ieunex_0 cv wceq wi feunex_1 wal ieunex_0 wex wa feunex_0 feunex_1 wal wn feunex_0 feunex_1 weu feunex_0 wn feunex_1 wex feunex_0 feunex_1 cv ieunex_0 cv wceq wi feunex_1 wal ieunex_0 wex feunex_0 feunex_1 wal wn feunex_0 feunex_1 wex feunex_0 feunex_1 cv ieunex_0 cv wceq wi feunex_1 wal feunex_0 feunex_1 wal wn ieunex_0 feunex_0 feunex_1 cv ieunex_0 cv wceq wi feunex_1 wal feunex_0 feunex_1 wal feunex_1 cv ieunex_0 cv wceq feunex_1 wal feunex_1 ieunex_0 dtru feunex_0 feunex_1 cv ieunex_0 cv wceq feunex_1 alim mtoi exlimiv adantl feunex_0 feunex_1 ieunex_0 feunex_0 ieunex_0 nfv eu3 feunex_0 feunex_1 exnal 3imtr4i $.
$}
$( A set variable is not free from itself.  The proof relies on ~ dtru ,
       that is, it is not true in a one-element domain.  (Contributed by Mario
       Carneiro, 8-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y z $.
	infnid_0 $f set y $.
	infnid_1 $f set z $.
	infnid_2 $f set w $.
	fnfnid_0 $f set x $.
	nfnid $p |- -. F/_ x x $= fnfnid_0 fnfnid_0 cv wnfc infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_0 wal infnid_2 wal infnid_1 wal infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_0 wal infnid_2 wal infnid_1 wal infnid_1 cv infnid_2 cv wceq infnid_1 wal infnid_1 infnid_2 dtru infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_0 wal infnid_2 wal infnid_1 cv infnid_2 cv wceq infnid_1 infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_0 wal infnid_1 cv infnid_2 cv wceq infnid_2 infnid_1 infnid_2 infnid_0 ax-ext sps alimi mto fnfnid_0 fnfnid_0 cv wnfc infnid_0 cv fnfnid_0 cv wcel fnfnid_0 wnf infnid_0 wal infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_2 wal infnid_1 wal infnid_0 wal infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_0 wal infnid_2 wal infnid_1 wal fnfnid_0 infnid_0 fnfnid_0 cv df-nfc infnid_0 cv fnfnid_0 cv wcel fnfnid_0 wnf infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_2 wal infnid_1 wal infnid_0 infnid_0 cv fnfnid_0 cv wcel fnfnid_0 wnf infnid_0 cv fnfnid_0 cv wcel fnfnid_0 infnid_1 wsb infnid_0 cv fnfnid_0 cv wcel fnfnid_0 infnid_2 wsb wb infnid_2 wal infnid_1 wal infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_2 wal infnid_1 wal infnid_0 cv fnfnid_0 cv wcel fnfnid_0 infnid_1 infnid_2 sbnf2 infnid_0 cv fnfnid_0 cv wcel fnfnid_0 infnid_1 wsb infnid_0 cv fnfnid_0 cv wcel fnfnid_0 infnid_2 wsb wb infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_1 infnid_2 infnid_0 cv fnfnid_0 cv wcel fnfnid_0 infnid_1 wsb infnid_0 cv infnid_1 cv wcel infnid_0 cv fnfnid_0 cv wcel fnfnid_0 infnid_2 wsb infnid_0 cv infnid_2 cv wcel infnid_1 fnfnid_0 infnid_0 elsb4 infnid_2 fnfnid_0 infnid_0 elsb4 bibi12i 2albii bitri albii infnid_0 cv infnid_1 cv wcel infnid_0 cv infnid_2 cv wcel wb infnid_0 infnid_1 infnid_2 alrot3 3bitri mtbir $.
$}
$( The "distinctor" expression ` -. A. x x = y ` , stating that ` x ` and
       ` y ` are not the same variable, can be written in terms of ` F/ ` in
       the obvious way.  This theorem is not true in a one-element domain,
       because then ` F/_ x y ` and ` A. x x = y ` will both be true.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	fnfcvb_0 $f set x $.
	fnfcvb_1 $f set y $.
	nfcvb $p |- ( F/_ x y <-> -. A. x x = y ) $= fnfcvb_0 fnfcvb_1 cv wnfc fnfcvb_0 cv fnfcvb_1 cv wceq fnfcvb_0 wal wn fnfcvb_0 cv fnfcvb_1 cv wceq fnfcvb_0 wal fnfcvb_0 fnfcvb_1 cv wnfc fnfcvb_0 cv fnfcvb_1 cv wceq fnfcvb_0 wal fnfcvb_0 fnfcvb_1 cv wnfc fnfcvb_1 fnfcvb_1 cv wnfc fnfcvb_1 nfnid fnfcvb_0 fnfcvb_1 fnfcvb_1 cv fnfcvb_1 cv fnfcvb_0 cv fnfcvb_1 cv wceq fnfcvb_0 wal fnfcvb_1 cv eqidd drnfc1 mtbiri con2i fnfcvb_0 fnfcvb_1 nfcvf impbii $.
$}
$( A class is a subclass of the power class of its union.  Exercise 6(b) of
       [Enderton] p. 38.  (Contributed by NM, 14-Oct-1996.) $)
${
	$v x $.
	$v A $.
	$d A x $.
	ipwuni_0 $f set x $.
	fpwuni_0 $f class A $.
	pwuni $p |- A C_ ~P U. A $= ipwuni_0 fpwuni_0 fpwuni_0 cuni cpw ipwuni_0 cv fpwuni_0 wcel ipwuni_0 cv fpwuni_0 cuni wss ipwuni_0 cv fpwuni_0 cuni cpw wcel ipwuni_0 cv fpwuni_0 elssuni ipwuni_0 cv fpwuni_0 cuni ipwuni_0 vex elpw sylibr ssriv $.
$}
$( A version of ~ dtru ("two things exist") with a shorter proof that uses
       more axioms but may be easier to understand.

       Assuming that ZF set theory is consistent, we cannot prove this theorem
       unless we specify that ` x ` and ` y ` be distinct.  Specifically,
       theorem ~ spcev requires that ` x ` must not occur in the subexpression
       ` -. y = { (/) } ` in step 4 nor in the subexpression ` -. y = (/) ` in
       step 9.  The proof verifier will require that ` x ` and ` y ` be in a
       distinct variable group to ensure this.  You can check this by deleting
       the $d statement in set.mm and rerunning the verifier, which will print
       a detailed explanation of the distinct variable violation.  (Contributed
       by NM, 15-Jul-1994.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	fdtruALT_0 $f set x $.
	fdtruALT_1 $f set y $.
	dtruALT $p |- -. A. x x = y $= fdtruALT_1 cv fdtruALT_0 cv wceq wn fdtruALT_0 wex fdtruALT_0 cv fdtruALT_1 cv wceq fdtruALT_0 wal wn fdtruALT_1 cv c0 wceq fdtruALT_1 cv fdtruALT_0 cv wceq wn fdtruALT_0 wex fdtruALT_1 cv c0 wceq fdtruALT_1 cv c0 csn wceq wn fdtruALT_1 cv fdtruALT_0 cv wceq wn fdtruALT_0 wex fdtruALT_1 cv 0inp0 fdtruALT_1 cv fdtruALT_0 cv wceq wn fdtruALT_1 cv c0 csn wceq wn fdtruALT_0 c0 csn p0ex fdtruALT_0 cv c0 csn wceq fdtruALT_1 cv fdtruALT_0 cv wceq fdtruALT_1 cv c0 csn wceq fdtruALT_0 cv c0 csn fdtruALT_1 cv eqeq2 notbid spcev syl fdtruALT_1 cv fdtruALT_0 cv wceq wn fdtruALT_1 cv c0 wceq wn fdtruALT_0 c0 0ex fdtruALT_0 cv c0 wceq fdtruALT_1 cv fdtruALT_0 cv wceq fdtruALT_1 cv c0 wceq fdtruALT_0 cv c0 fdtruALT_1 cv eqeq2 notbid spcev pm2.61i fdtruALT_1 cv fdtruALT_0 cv wceq wn fdtruALT_0 wex fdtruALT_1 cv fdtruALT_0 cv wceq fdtruALT_0 wal fdtruALT_0 cv fdtruALT_1 cv wceq fdtruALT_0 wal fdtruALT_1 cv fdtruALT_0 cv wceq fdtruALT_0 exnal fdtruALT_1 cv fdtruALT_0 cv wceq fdtruALT_0 cv fdtruALT_1 cv wceq fdtruALT_0 fdtruALT_1 cv fdtruALT_0 cv eqcom albii xchbinx mpbi $.
$}
$( Corollary of ~ dtru .  This example illustrates the danger of blindly
       trusting the standard Deduction Theorem without accounting for free
       variables: the theorem form of this deduction is not valid, as shown by
       ~ dtrucor2 .  (Contributed by NM, 27-Jun-2002.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	fdtrucor_0 $f set x $.
	fdtrucor_1 $f set y $.
	edtrucor_0 $e |- x = y $.
	dtrucor $p |- x =/= y $= fdtrucor_0 cv fdtrucor_1 cv wceq fdtrucor_0 cv fdtrucor_1 cv wne fdtrucor_0 fdtrucor_0 cv fdtrucor_1 cv wceq fdtrucor_0 wal fdtrucor_0 cv fdtrucor_1 cv wne fdtrucor_0 fdtrucor_1 dtru pm2.21i edtrucor_0 mpg $.
$}
$( The theorem form of the deduction ~ dtrucor leads to a contradiction, as
       mentioned in the "Wrong!" example at
       ~ http://us.metamath.org/mpeuni/mmdeduction.html#bad .  (Contributed by
       NM, 20-Oct-2007.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fdtrucor2_0 $f wff ph $.
	fdtrucor2_1 $f set x $.
	fdtrucor2_2 $f set y $.
	edtrucor2_0 $e |- ( x = y -> x =/= y ) $.
	dtrucor2 $p |- ( ph /\ -. ph ) $= fdtrucor2_1 cv fdtrucor2_2 cv wceq fdtrucor2_1 wex fdtrucor2_0 fdtrucor2_0 wn wa fdtrucor2_1 fdtrucor2_2 a9e fdtrucor2_1 cv fdtrucor2_2 cv wceq fdtrucor2_1 fdtrucor2_1 cv fdtrucor2_2 cv wceq fdtrucor2_1 cv fdtrucor2_2 cv wceq wn wi fdtrucor2_1 cv fdtrucor2_2 cv wceq wn fdtrucor2_1 cv fdtrucor2_2 cv wceq fdtrucor2_1 cv fdtrucor2_2 cv edtrucor2_0 necon2bi fdtrucor2_1 cv fdtrucor2_2 cv wceq pm2.01 ax-mp nex pm2.24ii $.
$}
$( Demonstration of a theorem (scheme) that requires (meta)variables ` x `
       and ` y ` to be distinct, but no others.  It bundles the theorem schemes
       ` E. x ( x = y -> x e. x ) ` and ` E. x ( x = y -> y e. x ) ` .  Compare
       ~ dvdemo2 .  ("Bundles" is a term introduced by Raph Levien.)
       (Contributed by NM, 1-Dec-2006.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	fdvdemo1_0 $f set x $.
	fdvdemo1_1 $f set y $.
	fdvdemo1_2 $f set z $.
	dvdemo1 $p |- E. x ( x = y -> z e. x ) $= fdvdemo1_0 cv fdvdemo1_1 cv wceq wn fdvdemo1_0 wex fdvdemo1_0 cv fdvdemo1_1 cv wceq fdvdemo1_2 cv fdvdemo1_0 cv wcel wi fdvdemo1_0 wex fdvdemo1_0 cv fdvdemo1_1 cv wceq wn fdvdemo1_0 wex fdvdemo1_0 cv fdvdemo1_1 cv wceq fdvdemo1_0 wal wn fdvdemo1_0 fdvdemo1_1 dtru fdvdemo1_0 cv fdvdemo1_1 cv wceq fdvdemo1_0 exnal mpbir fdvdemo1_0 cv fdvdemo1_1 cv wceq wn fdvdemo1_0 cv fdvdemo1_1 cv wceq fdvdemo1_2 cv fdvdemo1_0 cv wcel wi fdvdemo1_0 fdvdemo1_0 cv fdvdemo1_1 cv wceq fdvdemo1_2 cv fdvdemo1_0 cv wcel pm2.21 eximi ax-mp $.
$}
$( Demonstration of a theorem (scheme) that requires (meta)variables ` x `
       and ` z ` to be distinct, but no others.  It bundles the theorem schemes
       ` E. x ( x = x -> z e. x ) ` and ` E. x ( x = y -> y e. x ) ` .  Compare
       ~ dvdemo1 .  (Contributed by NM, 1-Dec-2006.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	fdvdemo2_0 $f set x $.
	fdvdemo2_1 $f set y $.
	fdvdemo2_2 $f set z $.
	dvdemo2 $p |- E. x ( x = y -> z e. x ) $= fdvdemo2_2 cv fdvdemo2_0 cv wcel fdvdemo2_0 wex fdvdemo2_0 cv fdvdemo2_1 cv wceq fdvdemo2_2 cv fdvdemo2_0 cv wcel wi fdvdemo2_0 wex fdvdemo2_2 fdvdemo2_0 el fdvdemo2_2 cv fdvdemo2_0 cv wcel fdvdemo2_0 cv fdvdemo2_1 cv wceq fdvdemo2_2 cv fdvdemo2_0 cv wcel wi fdvdemo2_0 fdvdemo2_2 cv fdvdemo2_0 cv wcel fdvdemo2_0 cv fdvdemo2_1 cv wceq ax-1 eximi ax-mp $.
$}

