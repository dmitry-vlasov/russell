$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Introduce_the_Axiom_of_Power_Sets.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Derive the Axiom of Pairing

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( The Axiom of Pairing of Zermelo-Fraenkel set theory.  Axiom 2 of
       [TakeutiZaring] p. 15.  In some textbooks this is stated as a separate
       axiom; here we show it is redundant since it can be derived from the
       other axioms.

       This theorem should not be referenced by any proof other than ~ axpr .
       Instead, use ~ zfpair2 below so that the uses of the Axiom of Pairing
       can be more easily identified.  (Contributed by NM, 18-Oct-1995.)
       (New usage is discouraged.) $)
${
	$d x z w v $.
	$d y z w v $.
	izfpair_0 $f set z $.
	izfpair_1 $f set w $.
	izfpair_2 $f set v $.
	fzfpair_0 $f set x $.
	fzfpair_1 $f set y $.
	zfpair $p |- { x , y } e. _V $= fzfpair_0 sup_set_class fzfpair_1 sup_set_class cpr izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wo izfpair_1 cab cvv izfpair_1 fzfpair_0 sup_set_class fzfpair_1 sup_set_class dfpr2 izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wo izfpair_1 cab izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 csn wceq wo izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo wa izfpair_0 wex izfpair_1 cab cvv izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wo izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 csn wceq wo izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo wa izfpair_0 wex izfpair_1 izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_0 wex izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 wex izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa izfpair_0 wex wo izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 csn wceq wo izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo wa izfpair_0 wex izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wo izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa izfpair_0 19.43 izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 csn wceq wo izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo wa izfpair_0 izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq prlem2 exbii izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 wex izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa izfpair_0 wex izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 wex izfpair_0 sup_set_class c0 wceq izfpair_0 wex izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_0 c0 0ex isseti izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_0 19.41v mpbiran izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa izfpair_0 wex izfpair_0 sup_set_class c0 csn wceq izfpair_0 wex izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq izfpair_0 c0 csn p0ex isseti izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq izfpair_0 19.41v mpbiran orbi12i 3bitr3ri abbii izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 csn wceq wo izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_0 izfpair_1 izfpair_2 c0 c0 csn cpr izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 csn wceq wo izfpair_0 cab cvv izfpair_0 c0 c0 csn dfpr2 pp0ex eqeltrri izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_1 sup_set_class izfpair_2 sup_set_class wceq wi izfpair_1 wal izfpair_2 wex izfpair_0 sup_set_class c0 csn wceq izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_1 sup_set_class izfpair_2 sup_set_class wceq wi izfpair_1 wal izfpair_2 fzfpair_0 izfpair_2 sup_set_class fzfpair_0 sup_set_class wceq izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_1 sup_set_class izfpair_2 sup_set_class wceq wi izfpair_1 izfpair_2 sup_set_class fzfpair_0 sup_set_class wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq izfpair_1 sup_set_class izfpair_2 sup_set_class wceq izfpair_2 fzfpair_0 izfpair_1 equequ2 izfpair_0 sup_set_class 0inp0 prlem1 alrimdv spimev izfpair_0 sup_set_class c0 csn wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_1 sup_set_class izfpair_2 sup_set_class wceq wi izfpair_1 wal izfpair_2 fzfpair_1 izfpair_2 sup_set_class fzfpair_1 sup_set_class wceq izfpair_0 sup_set_class c0 csn wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_1 sup_set_class izfpair_2 sup_set_class wceq wi izfpair_1 izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa wo izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa wo izfpair_2 sup_set_class fzfpair_1 sup_set_class wceq izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class izfpair_2 sup_set_class wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq wa izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq wa orcom izfpair_2 sup_set_class fzfpair_1 sup_set_class wceq izfpair_0 sup_set_class c0 csn wceq izfpair_1 sup_set_class fzfpair_1 sup_set_class wceq izfpair_0 sup_set_class c0 wceq izfpair_1 sup_set_class fzfpair_0 sup_set_class wceq izfpair_1 sup_set_class izfpair_2 sup_set_class wceq izfpair_2 fzfpair_1 izfpair_1 equequ2 izfpair_0 sup_set_class c0 wceq izfpair_0 sup_set_class c0 csn wceq izfpair_0 sup_set_class 0inp0 con2i prlem1 syl7bi alrimdv spimev jaoi zfrep4 eqeltri eqeltri $.
$}
$( Unabbreviated version of the Axiom of Pairing of ZF set theory, derived
       as a theorem from the other axioms.

       This theorem should not be referenced by any proof.  Instead, use
       ~ ax-pr below so that the uses of the Axiom of Pairing can be more
       easily identified.  (Contributed by NM, 14-Nov-2006.)
       (New usage is discouraged.) $)
${
	$d x z w $.
	$d y z w $.
	faxpr_0 $f set x $.
	faxpr_1 $f set y $.
	faxpr_2 $f set z $.
	faxpr_3 $f set w $.
	axpr $p |- E. z A. w ( ( w = x \/ w = y ) -> w e. z ) $= faxpr_2 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class cpr wceq faxpr_2 wex faxpr_3 sup_set_class faxpr_0 sup_set_class wceq faxpr_3 sup_set_class faxpr_1 sup_set_class wceq wo faxpr_3 sup_set_class faxpr_2 sup_set_class wcel wi faxpr_3 wal faxpr_2 wex faxpr_2 faxpr_0 sup_set_class faxpr_1 sup_set_class cpr faxpr_0 faxpr_1 zfpair isseti faxpr_2 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class cpr wceq faxpr_3 sup_set_class faxpr_0 sup_set_class wceq faxpr_3 sup_set_class faxpr_1 sup_set_class wceq wo faxpr_3 sup_set_class faxpr_2 sup_set_class wcel wi faxpr_3 wal faxpr_2 faxpr_2 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class cpr wceq faxpr_3 sup_set_class faxpr_2 sup_set_class wcel faxpr_3 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class cpr wcel wb faxpr_3 wal faxpr_3 sup_set_class faxpr_0 sup_set_class wceq faxpr_3 sup_set_class faxpr_1 sup_set_class wceq wo faxpr_3 sup_set_class faxpr_2 sup_set_class wcel wi faxpr_3 wal faxpr_3 faxpr_2 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class cpr dfcleq faxpr_3 sup_set_class faxpr_2 sup_set_class wcel faxpr_3 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class cpr wcel wb faxpr_3 sup_set_class faxpr_0 sup_set_class wceq faxpr_3 sup_set_class faxpr_1 sup_set_class wceq wo faxpr_3 sup_set_class faxpr_2 sup_set_class wcel wi faxpr_3 faxpr_3 sup_set_class faxpr_2 sup_set_class wcel faxpr_3 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class cpr wcel wb faxpr_3 sup_set_class faxpr_2 sup_set_class wcel faxpr_3 sup_set_class faxpr_0 sup_set_class wceq faxpr_3 sup_set_class faxpr_1 sup_set_class wceq wo wb faxpr_3 sup_set_class faxpr_0 sup_set_class wceq faxpr_3 sup_set_class faxpr_1 sup_set_class wceq wo faxpr_3 sup_set_class faxpr_2 sup_set_class wcel wi faxpr_3 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class cpr wcel faxpr_3 sup_set_class faxpr_0 sup_set_class wceq faxpr_3 sup_set_class faxpr_1 sup_set_class wceq wo faxpr_3 sup_set_class faxpr_2 sup_set_class wcel faxpr_3 sup_set_class faxpr_0 sup_set_class faxpr_1 sup_set_class faxpr_3 vex elpr bibi2i faxpr_3 sup_set_class faxpr_2 sup_set_class wcel faxpr_3 sup_set_class faxpr_0 sup_set_class wceq faxpr_3 sup_set_class faxpr_1 sup_set_class wceq wo bi2 sylbi alimi sylbi eximi ax-mp $.
$}
$( The Axiom of Pairing of ZF set theory.  It was derived as theorem ~ axpr
       above and is therefore redundant, but we state it as a separate axiom
       here so that its uses can be identified more easily.  (Contributed by
       NM, 14-Nov-2006.) $)
${
	$d x z w $.
	$d y z w $.
	fax-pr_0 $f set x $.
	fax-pr_1 $f set y $.
	fax-pr_2 $f set z $.
	fax-pr_3 $f set w $.
	ax-pr $a |- E. z A. w ( ( w = x \/ w = y ) -> w e. z ) $.
$}
$( Derive the abbreviated version of the Axiom of Pairing from ~ ax-pr .
       See ~ zfpair for its derivation from the other axioms.  (Contributed by
       NM, 14-Nov-2006.) $)
${
	$d x z w $.
	$d y z w $.
	izfpair2_0 $f set z $.
	izfpair2_1 $f set w $.
	fzfpair2_0 $f set x $.
	fzfpair2_1 $f set y $.
	zfpair2 $p |- { x , y } e. _V $= izfpair2_0 fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class cpr izfpair2_0 sup_set_class fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class cpr wceq izfpair2_0 wex izfpair2_1 sup_set_class izfpair2_0 sup_set_class wcel izfpair2_1 sup_set_class fzfpair2_0 sup_set_class wceq izfpair2_1 sup_set_class fzfpair2_1 sup_set_class wceq wo wb izfpair2_1 wal izfpair2_0 wex izfpair2_1 sup_set_class fzfpair2_0 sup_set_class wceq izfpair2_1 sup_set_class fzfpair2_1 sup_set_class wceq wo izfpair2_0 izfpair2_1 fzfpair2_0 fzfpair2_1 izfpair2_0 izfpair2_1 ax-pr bm1.3ii izfpair2_0 sup_set_class fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class cpr wceq izfpair2_1 sup_set_class izfpair2_0 sup_set_class wcel izfpair2_1 sup_set_class fzfpair2_0 sup_set_class wceq izfpair2_1 sup_set_class fzfpair2_1 sup_set_class wceq wo wb izfpair2_1 wal izfpair2_0 izfpair2_0 sup_set_class fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class cpr wceq izfpair2_1 sup_set_class izfpair2_0 sup_set_class wcel izfpair2_1 sup_set_class fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class cpr wcel wb izfpair2_1 wal izfpair2_1 sup_set_class izfpair2_0 sup_set_class wcel izfpair2_1 sup_set_class fzfpair2_0 sup_set_class wceq izfpair2_1 sup_set_class fzfpair2_1 sup_set_class wceq wo wb izfpair2_1 wal izfpair2_1 izfpair2_0 sup_set_class fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class cpr dfcleq izfpair2_1 sup_set_class izfpair2_0 sup_set_class wcel izfpair2_1 sup_set_class fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class cpr wcel wb izfpair2_1 sup_set_class izfpair2_0 sup_set_class wcel izfpair2_1 sup_set_class fzfpair2_0 sup_set_class wceq izfpair2_1 sup_set_class fzfpair2_1 sup_set_class wceq wo wb izfpair2_1 izfpair2_1 sup_set_class fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class cpr wcel izfpair2_1 sup_set_class fzfpair2_0 sup_set_class wceq izfpair2_1 sup_set_class fzfpair2_1 sup_set_class wceq wo izfpair2_1 sup_set_class izfpair2_0 sup_set_class wcel izfpair2_1 sup_set_class fzfpair2_0 sup_set_class fzfpair2_1 sup_set_class izfpair2_1 vex elpr bibi2i albii bitri exbii mpbir issetri $.
$}
$( A singleton is a set.  Theorem 7.13 of [Quine] p. 51, proved using
       Extensionality, Separation, and Pairing.  See also ~ snexALT .
       (Contributed by NM, 7-Aug-1994.)  (Revised by Mario Carneiro,
       19-May-2013.)  (Proof modification is discouraged.) $)
${
	$d x A $.
	isnex_0 $f set x $.
	fsnex_0 $f class A $.
	snex $p |- { A } e. _V $= fsnex_0 cvv wcel fsnex_0 csn cvv wcel fsnex_0 cvv wcel fsnex_0 csn fsnex_0 fsnex_0 cpr cvv fsnex_0 dfsn2 isnex_0 sup_set_class isnex_0 sup_set_class cpr cvv wcel fsnex_0 fsnex_0 cpr cvv wcel isnex_0 fsnex_0 cvv isnex_0 sup_set_class fsnex_0 wceq isnex_0 sup_set_class isnex_0 sup_set_class cpr fsnex_0 fsnex_0 cpr cvv isnex_0 sup_set_class fsnex_0 wceq isnex_0 sup_set_class isnex_0 sup_set_class cpr fsnex_0 fsnex_0 cpr wceq isnex_0 sup_set_class isnex_0 sup_set_class fsnex_0 fsnex_0 preq12 anidms eleq1d isnex_0 isnex_0 zfpair2 vtoclg syl5eqel fsnex_0 cvv wcel wn fsnex_0 csn c0 cvv fsnex_0 cvv wcel wn fsnex_0 csn c0 wceq fsnex_0 snprc biimpi 0ex syl6eqel pm2.61i $.
$}
$( The Axiom of Pairing using class variables.  Theorem 7.13 of [Quine]
       p. 51.  By virtue of its definition, an unordered pair remains a set
       (even though no longer a pair) even when its components are proper
       classes (see ~ prprc ), so we can dispense with hypotheses requiring
       them to be sets.  (Contributed by NM, 5-Aug-1993.) $)
${
	$d x y A $.
	$d x y B $.
	iprex_0 $f set x $.
	iprex_1 $f set y $.
	fprex_0 $f class A $.
	fprex_1 $f class B $.
	prex $p |- { A , B } e. _V $= fprex_0 cvv wcel fprex_1 cvv wcel fprex_0 fprex_1 cpr cvv wcel fprex_1 cvv wcel fprex_0 fprex_1 cpr cvv wcel wi iprex_0 fprex_0 cvv fprex_1 cvv wcel iprex_0 sup_set_class fprex_1 cpr cvv wcel iprex_0 sup_set_class fprex_0 wceq fprex_0 fprex_1 cpr cvv wcel iprex_0 sup_set_class iprex_1 sup_set_class cpr cvv wcel iprex_0 sup_set_class fprex_1 cpr cvv wcel iprex_1 fprex_1 cvv iprex_1 sup_set_class fprex_1 wceq iprex_0 sup_set_class iprex_1 sup_set_class cpr iprex_0 sup_set_class fprex_1 cpr cvv iprex_1 sup_set_class fprex_1 iprex_0 sup_set_class preq2 eleq1d iprex_0 iprex_1 zfpair2 vtoclg iprex_0 sup_set_class fprex_0 wceq iprex_0 sup_set_class fprex_1 cpr fprex_0 fprex_1 cpr cvv iprex_0 sup_set_class fprex_0 fprex_1 preq1 eleq1d syl5ib vtocleg fprex_0 cvv wcel wn fprex_0 fprex_1 cpr fprex_1 csn cvv fprex_0 fprex_1 prprc1 fprex_1 snex syl6eqel fprex_1 cvv wcel wn fprex_0 fprex_1 cpr fprex_0 csn cvv fprex_0 fprex_1 prprc2 fprex_0 snex syl6eqel pm2.61nii $.
$}
$( Every set is an element of some other set.  This has a shorter proof
       than ~ el but uses more axioms.  (Contributed by NM, 4-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d x y $.
	felALT_0 $f set x $.
	felALT_1 $f set y $.
	elALT $p |- E. y x e. y $= felALT_0 sup_set_class felALT_0 sup_set_class csn wcel felALT_0 sup_set_class felALT_1 sup_set_class wcel felALT_1 wex felALT_0 sup_set_class felALT_0 vex snid felALT_0 sup_set_class felALT_1 sup_set_class wcel felALT_0 sup_set_class felALT_0 sup_set_class csn wcel felALT_1 felALT_0 sup_set_class csn felALT_0 sup_set_class snex felALT_1 sup_set_class felALT_0 sup_set_class csn felALT_0 sup_set_class eleq2 spcev ax-mp $.
$}
$( An alternative proof of ~ dtru ("two things exist") using ~ ax-pr
       instead of ~ ax-pow .  (Contributed by Mario Carneiro, 31-Aug-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d x y $.
	fdtruALT2_0 $f set x $.
	fdtruALT2_1 $f set y $.
	dtruALT2 $p |- -. A. x x = y $= fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq wn fdtruALT2_0 wex fdtruALT2_0 sup_set_class fdtruALT2_1 sup_set_class wceq fdtruALT2_0 wal wn fdtruALT2_1 sup_set_class c0 wceq fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq wn fdtruALT2_0 wex fdtruALT2_1 sup_set_class c0 wceq fdtruALT2_1 sup_set_class c0 csn wceq wn fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq wn fdtruALT2_0 wex fdtruALT2_1 sup_set_class 0inp0 fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq wn fdtruALT2_1 sup_set_class c0 csn wceq wn fdtruALT2_0 c0 csn c0 snex fdtruALT2_0 sup_set_class c0 csn wceq fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq fdtruALT2_1 sup_set_class c0 csn wceq fdtruALT2_0 sup_set_class c0 csn fdtruALT2_1 sup_set_class eqeq2 notbid spcev syl fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq wn fdtruALT2_1 sup_set_class c0 wceq wn fdtruALT2_0 c0 0ex fdtruALT2_0 sup_set_class c0 wceq fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq fdtruALT2_1 sup_set_class c0 wceq fdtruALT2_0 sup_set_class c0 fdtruALT2_1 sup_set_class eqeq2 notbid spcev pm2.61i fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq wn fdtruALT2_0 wex fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq fdtruALT2_0 wal fdtruALT2_0 sup_set_class fdtruALT2_1 sup_set_class wceq fdtruALT2_0 wal fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq fdtruALT2_0 exnal fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class wceq fdtruALT2_0 sup_set_class fdtruALT2_1 sup_set_class wceq fdtruALT2_0 fdtruALT2_1 sup_set_class fdtruALT2_0 sup_set_class eqcom albii xchbinx mpbi $.
$}
$( A singleton of a set belongs to the power class of a class containing
       the set.  (Contributed by Alan Sare, 25-Aug-2011.) $)
${
	fsnelpwi_0 $f class A $.
	fsnelpwi_1 $f class B $.
	snelpwi $p |- ( A e. B -> { A } e. ~P B ) $= fsnelpwi_0 fsnelpwi_1 wcel fsnelpwi_0 csn fsnelpwi_1 wss fsnelpwi_0 csn fsnelpwi_1 cpw wcel fsnelpwi_0 fsnelpwi_1 snssi fsnelpwi_0 csn fsnelpwi_1 fsnelpwi_0 snex elpw sylibr $.
$}
$( A singleton of a set belongs to the power class of a class containing
       the set.  (Contributed by NM, 1-Apr-1998.) $)
${
	fsnelpw_0 $f class A $.
	fsnelpw_1 $f class B $.
	esnelpw_0 $e |- A e. _V $.
	snelpw $p |- ( A e. B <-> { A } e. ~P B ) $= fsnelpw_0 fsnelpw_1 wcel fsnelpw_0 csn fsnelpw_1 wss fsnelpw_0 csn fsnelpw_1 cpw wcel fsnelpw_0 fsnelpw_1 esnelpw_0 snss fsnelpw_0 csn fsnelpw_1 fsnelpw_0 snex elpw bitr4i $.
$}
$( A theorem similar to extensionality, requiring the existence of a
       singleton.  Exercise 8 of [TakeutiZaring] p. 16.  (Contributed by NM,
       10-Aug-1993.) $)
${
	$d x y z $.
	frext_0 $f set x $.
	frext_1 $f set y $.
	frext_2 $f set z $.
	rext $p |- ( A. z ( x e. z -> y e. z ) -> x = y ) $= frext_0 sup_set_class frext_2 sup_set_class wcel frext_1 sup_set_class frext_2 sup_set_class wcel wi frext_2 wal frext_1 sup_set_class frext_0 sup_set_class csn wcel frext_0 sup_set_class frext_1 sup_set_class wceq frext_0 sup_set_class frext_2 sup_set_class wcel frext_1 sup_set_class frext_2 sup_set_class wcel wi frext_2 wal frext_0 sup_set_class frext_0 sup_set_class csn wcel frext_1 sup_set_class frext_0 sup_set_class csn wcel frext_0 sup_set_class frext_0 vex snid frext_0 sup_set_class frext_2 sup_set_class wcel frext_1 sup_set_class frext_2 sup_set_class wcel wi frext_0 sup_set_class frext_0 sup_set_class csn wcel frext_1 sup_set_class frext_0 sup_set_class csn wcel wi frext_2 frext_0 sup_set_class csn frext_0 sup_set_class snex frext_2 sup_set_class frext_0 sup_set_class csn wceq frext_0 sup_set_class frext_2 sup_set_class wcel frext_0 sup_set_class frext_0 sup_set_class csn wcel frext_1 sup_set_class frext_2 sup_set_class wcel frext_1 sup_set_class frext_0 sup_set_class csn wcel frext_2 sup_set_class frext_0 sup_set_class csn frext_0 sup_set_class eleq2 frext_2 sup_set_class frext_0 sup_set_class csn frext_1 sup_set_class eleq2 imbi12d spcv mpi frext_1 sup_set_class frext_0 sup_set_class csn wcel frext_1 sup_set_class frext_0 sup_set_class wceq frext_0 sup_set_class frext_1 sup_set_class wceq frext_1 frext_0 sup_set_class elsn frext_1 frext_0 equcomi sylbi syl $.
$}
$( Classes are subclasses if and only if their power classes are
       subclasses.  Exercise 18 of [TakeutiZaring] p. 18.  (Contributed by NM,
       13-Oct-1996.) $)
${
	$d A x $.
	$d B x $.
	isspwb_0 $f set x $.
	fsspwb_0 $f class A $.
	fsspwb_1 $f class B $.
	sspwb $p |- ( A C_ B <-> ~P A C_ ~P B ) $= fsspwb_0 fsspwb_1 wss fsspwb_0 cpw fsspwb_1 cpw wss fsspwb_0 fsspwb_1 wss isspwb_0 fsspwb_0 cpw fsspwb_1 cpw fsspwb_0 fsspwb_1 wss isspwb_0 sup_set_class fsspwb_0 wss isspwb_0 sup_set_class fsspwb_1 wss isspwb_0 sup_set_class fsspwb_0 cpw wcel isspwb_0 sup_set_class fsspwb_1 cpw wcel isspwb_0 sup_set_class fsspwb_0 wss fsspwb_0 fsspwb_1 wss isspwb_0 sup_set_class fsspwb_1 wss isspwb_0 sup_set_class fsspwb_0 fsspwb_1 sstr2 com12 isspwb_0 sup_set_class fsspwb_0 isspwb_0 vex elpw isspwb_0 sup_set_class fsspwb_1 isspwb_0 vex elpw 3imtr4g ssrdv fsspwb_0 cpw fsspwb_1 cpw wss isspwb_0 fsspwb_0 fsspwb_1 fsspwb_0 cpw fsspwb_1 cpw wss isspwb_0 sup_set_class csn fsspwb_0 cpw wcel isspwb_0 sup_set_class csn fsspwb_1 cpw wcel isspwb_0 sup_set_class fsspwb_0 wcel isspwb_0 sup_set_class fsspwb_1 wcel fsspwb_0 cpw fsspwb_1 cpw isspwb_0 sup_set_class csn ssel isspwb_0 sup_set_class csn fsspwb_0 cpw wcel isspwb_0 sup_set_class csn fsspwb_0 wss isspwb_0 sup_set_class fsspwb_0 wcel isspwb_0 sup_set_class csn fsspwb_0 isspwb_0 sup_set_class snex elpw isspwb_0 sup_set_class fsspwb_0 isspwb_0 vex snss bitr4i isspwb_0 sup_set_class csn fsspwb_1 cpw wcel isspwb_0 sup_set_class csn fsspwb_1 wss isspwb_0 sup_set_class fsspwb_1 wcel isspwb_0 sup_set_class csn fsspwb_1 isspwb_0 sup_set_class snex elpw isspwb_0 sup_set_class fsspwb_1 isspwb_0 vex snss bitr4i 3imtr3g ssrdv impbii $.
$}
$( A class equals the union of its power class.  Exercise 6(a) of
       [Enderton] p. 38.  (Contributed by NM, 14-Oct-1996.)  (Proof shortened
       by Alan Sare, 28-Dec-2008.) $)
${
	$d A x y $.
	iunipw_0 $f set x $.
	iunipw_1 $f set y $.
	funipw_0 $f class A $.
	unipw $p |- U. ~P A = A $= iunipw_0 funipw_0 cpw cuni funipw_0 iunipw_0 sup_set_class funipw_0 cpw cuni wcel iunipw_0 sup_set_class funipw_0 wcel iunipw_0 sup_set_class funipw_0 cpw cuni wcel iunipw_0 sup_set_class iunipw_1 sup_set_class wcel iunipw_1 sup_set_class funipw_0 cpw wcel wa iunipw_1 wex iunipw_0 sup_set_class funipw_0 wcel iunipw_1 iunipw_0 sup_set_class funipw_0 cpw eluni iunipw_0 sup_set_class iunipw_1 sup_set_class wcel iunipw_1 sup_set_class funipw_0 cpw wcel wa iunipw_0 sup_set_class funipw_0 wcel iunipw_1 iunipw_0 sup_set_class iunipw_1 sup_set_class funipw_0 elelpwi exlimiv sylbi iunipw_0 sup_set_class funipw_0 wcel iunipw_0 sup_set_class iunipw_0 sup_set_class csn wcel iunipw_0 sup_set_class csn funipw_0 cpw wcel iunipw_0 sup_set_class funipw_0 cpw cuni wcel iunipw_0 sup_set_class iunipw_0 vex snid iunipw_0 sup_set_class funipw_0 snelpwi iunipw_0 sup_set_class iunipw_0 sup_set_class csn funipw_0 cpw elunii sylancr impbii eqriv $.
$}
$( Membership of a power class.  Exercise 10 of [Enderton] p. 26.
     (Contributed by NM, 13-Jan-2007.) $)
${
	fpwel_0 $f class A $.
	fpwel_1 $f class B $.
	pwel $p |- ( A e. B -> ~P A e. ~P ~P U. B ) $= fpwel_0 fpwel_1 wcel fpwel_0 cpw fpwel_1 cuni cpw cpw wcel fpwel_0 cpw fpwel_1 cuni cpw wss fpwel_0 fpwel_1 wcel fpwel_0 fpwel_1 cuni wss fpwel_0 cpw fpwel_1 cuni cpw wss fpwel_0 fpwel_1 elssuni fpwel_0 fpwel_1 cuni sspwb sylib fpwel_0 fpwel_1 wcel fpwel_0 cpw cvv wcel fpwel_0 cpw fpwel_1 cuni cpw cpw wcel fpwel_0 cpw fpwel_1 cuni cpw wss wb fpwel_0 fpwel_1 pwexg fpwel_0 cpw fpwel_1 cuni cpw cvv elpwg syl mpbird $.
$}
$( A class is transitive iff its power class is transitive.  (Contributed by
     Alan Sare, 25-Aug-2011.)  (Revised by Mario Carneiro, 15-Jun-2014.) $)
${
	fpwtr_0 $f class A $.
	pwtr $p |- ( Tr A <-> Tr ~P A ) $= fpwtr_0 cpw cuni fpwtr_0 cpw wss fpwtr_0 fpwtr_0 cpw wss fpwtr_0 cpw wtr fpwtr_0 wtr fpwtr_0 cpw cuni fpwtr_0 fpwtr_0 cpw fpwtr_0 unipw sseq1i fpwtr_0 cpw df-tr fpwtr_0 dftr4 3bitr4ri $.
$}
$( An extensionality-like principle defining subclass in terms of subsets.
       (Contributed by NM, 30-Jun-2004.) $)
${
	$d A x $.
	$d B x $.
	fssextss_0 $f set x $.
	fssextss_1 $f class A $.
	fssextss_2 $f class B $.
	ssextss $p |- ( A C_ B <-> A. x ( x C_ A -> x C_ B ) ) $= fssextss_1 fssextss_2 wss fssextss_1 cpw fssextss_2 cpw wss fssextss_0 sup_set_class fssextss_1 cpw wcel fssextss_0 sup_set_class fssextss_2 cpw wcel wi fssextss_0 wal fssextss_0 sup_set_class fssextss_1 wss fssextss_0 sup_set_class fssextss_2 wss wi fssextss_0 wal fssextss_1 fssextss_2 sspwb fssextss_0 fssextss_1 cpw fssextss_2 cpw dfss2 fssextss_0 sup_set_class fssextss_1 cpw wcel fssextss_0 sup_set_class fssextss_2 cpw wcel wi fssextss_0 sup_set_class fssextss_1 wss fssextss_0 sup_set_class fssextss_2 wss wi fssextss_0 fssextss_0 sup_set_class fssextss_1 cpw wcel fssextss_0 sup_set_class fssextss_1 wss fssextss_0 sup_set_class fssextss_2 cpw wcel fssextss_0 sup_set_class fssextss_2 wss fssextss_0 sup_set_class fssextss_1 fssextss_0 vex elpw fssextss_0 sup_set_class fssextss_2 fssextss_0 vex elpw imbi12i albii 3bitri $.
$}
$( An extensionality-like principle that uses the subset instead of the
       membership relation: two classes are equal iff they have the same
       subsets.  (Contributed by NM, 30-Jun-2004.) $)
${
	$d A x $.
	$d B x $.
	fssext_0 $f set x $.
	fssext_1 $f class A $.
	fssext_2 $f class B $.
	ssext $p |- ( A = B <-> A. x ( x C_ A <-> x C_ B ) ) $= fssext_1 fssext_2 wss fssext_2 fssext_1 wss wa fssext_0 sup_set_class fssext_1 wss fssext_0 sup_set_class fssext_2 wss wi fssext_0 wal fssext_0 sup_set_class fssext_2 wss fssext_0 sup_set_class fssext_1 wss wi fssext_0 wal wa fssext_1 fssext_2 wceq fssext_0 sup_set_class fssext_1 wss fssext_0 sup_set_class fssext_2 wss wb fssext_0 wal fssext_1 fssext_2 wss fssext_0 sup_set_class fssext_1 wss fssext_0 sup_set_class fssext_2 wss wi fssext_0 wal fssext_2 fssext_1 wss fssext_0 sup_set_class fssext_2 wss fssext_0 sup_set_class fssext_1 wss wi fssext_0 wal fssext_0 fssext_1 fssext_2 ssextss fssext_0 fssext_2 fssext_1 ssextss anbi12i fssext_1 fssext_2 eqss fssext_0 sup_set_class fssext_1 wss fssext_0 sup_set_class fssext_2 wss fssext_0 albiim 3bitr4i $.
$}
$( Negation of subclass relationship.  Compare ~ nss .  (Contributed by NM,
       30-Jun-2004.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$d A x $.
	$d B x $.
	fnssss_0 $f set x $.
	fnssss_1 $f class A $.
	fnssss_2 $f class B $.
	nssss $p |- ( -. A C_ B <-> E. x ( x C_ A /\ -. x C_ B ) ) $= fnssss_0 sup_set_class fnssss_1 wss fnssss_0 sup_set_class fnssss_2 wss wn wa fnssss_0 wex fnssss_1 fnssss_2 wss wn fnssss_0 sup_set_class fnssss_1 wss fnssss_0 sup_set_class fnssss_2 wss wn wa fnssss_0 wex fnssss_0 sup_set_class fnssss_1 wss fnssss_0 sup_set_class fnssss_2 wss wi fnssss_0 wal fnssss_1 fnssss_2 wss fnssss_0 sup_set_class fnssss_1 wss fnssss_0 sup_set_class fnssss_2 wss fnssss_0 exanali fnssss_0 fnssss_1 fnssss_2 ssextss xchbinxr bicomi $.
$}
$( Classes are equal if and only if their power classes are equal.  Exercise
     19 of [TakeutiZaring] p. 18.  (Contributed by NM, 13-Oct-1996.) $)
${
	fpweqb_0 $f class A $.
	fpweqb_1 $f class B $.
	pweqb $p |- ( A = B <-> ~P A = ~P B ) $= fpweqb_0 fpweqb_1 wss fpweqb_1 fpweqb_0 wss wa fpweqb_0 cpw fpweqb_1 cpw wss fpweqb_1 cpw fpweqb_0 cpw wss wa fpweqb_0 fpweqb_1 wceq fpweqb_0 cpw fpweqb_1 cpw wceq fpweqb_0 fpweqb_1 wss fpweqb_0 cpw fpweqb_1 cpw wss fpweqb_1 fpweqb_0 wss fpweqb_1 cpw fpweqb_0 cpw wss fpweqb_0 fpweqb_1 sspwb fpweqb_1 fpweqb_0 sspwb anbi12i fpweqb_0 fpweqb_1 eqss fpweqb_0 cpw fpweqb_1 cpw eqss 3bitr4i $.
$}
$( The intersection of all sets to which a set belongs is the singleton of
       that set.  (Contributed by NM, 5-Jun-2009.) $)
${
	$d x A $.
	fintid_0 $f set x $.
	fintid_1 $f class A $.
	eintid_0 $e |- A e. _V $.
	intid $p |- |^| { x | A e. x } = { A } $= fintid_1 fintid_0 sup_set_class wcel fintid_0 cab cint fintid_1 csn fintid_1 csn cvv wcel fintid_1 fintid_0 sup_set_class wcel fintid_0 cab cint fintid_1 csn wss fintid_1 snex fintid_1 fintid_0 sup_set_class wcel fintid_1 fintid_1 csn wcel fintid_0 fintid_1 csn cvv fintid_0 sup_set_class fintid_1 csn fintid_1 eleq2 fintid_1 eintid_0 snid intmin3 ax-mp fintid_1 fintid_1 fintid_0 sup_set_class wcel fintid_0 cab cint wcel fintid_1 csn fintid_1 fintid_0 sup_set_class wcel fintid_0 cab cint wss fintid_1 fintid_1 fintid_0 sup_set_class wcel fintid_0 cab cint wcel fintid_1 fintid_0 sup_set_class wcel fintid_1 fintid_0 sup_set_class wcel wi fintid_0 fintid_1 fintid_0 sup_set_class wcel fintid_0 fintid_1 eintid_0 elintab fintid_1 fintid_0 sup_set_class wcel id mpgbir fintid_1 fintid_1 fintid_0 sup_set_class wcel fintid_0 cab cint snssi ax-mp eqssi $.
$}
$( "At most one" existence implies a class abstraction exists.
       (Contributed by NM, 30-Dec-1996.) $)
${
	$d x y $.
	$d y ph $.
	imoabex_0 $f set y $.
	fmoabex_0 $f wff ph $.
	fmoabex_1 $f set x $.
	moabex $p |- ( E* x ph -> { x | ph } e. _V ) $= fmoabex_0 fmoabex_1 wmo fmoabex_0 fmoabex_1 sup_set_class imoabex_0 sup_set_class wceq wi fmoabex_1 wal imoabex_0 wex fmoabex_0 fmoabex_1 cab cvv wcel fmoabex_0 fmoabex_1 imoabex_0 fmoabex_0 imoabex_0 nfv mo2 fmoabex_0 fmoabex_1 sup_set_class imoabex_0 sup_set_class wceq wi fmoabex_1 wal fmoabex_0 fmoabex_1 cab cvv wcel imoabex_0 fmoabex_0 fmoabex_1 sup_set_class imoabex_0 sup_set_class wceq wi fmoabex_1 wal fmoabex_0 fmoabex_1 cab imoabex_0 sup_set_class csn wss fmoabex_0 fmoabex_1 cab cvv wcel fmoabex_0 fmoabex_1 cab imoabex_0 sup_set_class csn wss fmoabex_0 fmoabex_1 sup_set_class imoabex_0 sup_set_class csn wcel wi fmoabex_1 wal fmoabex_0 fmoabex_1 sup_set_class imoabex_0 sup_set_class wceq wi fmoabex_1 wal fmoabex_0 fmoabex_1 imoabex_0 sup_set_class csn abss fmoabex_0 fmoabex_1 sup_set_class imoabex_0 sup_set_class csn wcel wi fmoabex_0 fmoabex_1 sup_set_class imoabex_0 sup_set_class wceq wi fmoabex_1 fmoabex_1 sup_set_class imoabex_0 sup_set_class csn wcel fmoabex_1 sup_set_class imoabex_0 sup_set_class wceq fmoabex_0 fmoabex_1 imoabex_0 sup_set_class elsn imbi2i albii bitri fmoabex_0 fmoabex_1 cab imoabex_0 sup_set_class csn imoabex_0 sup_set_class snex ssex sylbir exlimiv sylbi $.
$}
$( Restricted "at most one" existence implies a restricted class abstraction
     exists.  (Contributed by NM, 17-Jun-2017.) $)
${
	frmorabex_0 $f wff ph $.
	frmorabex_1 $f set x $.
	frmorabex_2 $f class A $.
	rmorabex $p |- ( E* x e. A ph -> { x e. A | ph } e. _V ) $= frmorabex_1 sup_set_class frmorabex_2 wcel frmorabex_0 wa frmorabex_1 wmo frmorabex_1 sup_set_class frmorabex_2 wcel frmorabex_0 wa frmorabex_1 cab cvv wcel frmorabex_0 frmorabex_1 frmorabex_2 wrmo frmorabex_0 frmorabex_1 frmorabex_2 crab cvv wcel frmorabex_1 sup_set_class frmorabex_2 wcel frmorabex_0 wa frmorabex_1 moabex frmorabex_0 frmorabex_1 frmorabex_2 df-rmo frmorabex_0 frmorabex_1 frmorabex_2 crab frmorabex_1 sup_set_class frmorabex_2 wcel frmorabex_0 wa frmorabex_1 cab cvv frmorabex_0 frmorabex_1 frmorabex_2 df-rab eleq1i 3imtr4i $.
$}
$( The abstraction of a wff with existential uniqueness exists.  (Contributed
     by NM, 25-Nov-1994.) $)
${
	feuabex_0 $f wff ph $.
	feuabex_1 $f set x $.
	euabex $p |- ( E! x ph -> { x | ph } e. _V ) $= feuabex_0 feuabex_1 weu feuabex_0 feuabex_1 wmo feuabex_0 feuabex_1 cab cvv wcel feuabex_0 feuabex_1 eumo feuabex_0 feuabex_1 moabex syl $.
$}
$( A non-empty class (even if proper) has a non-empty subset.  (Contributed
       by NM, 23-Aug-2003.) $)
${
	$d x y A $.
	innullss_0 $f set y $.
	fnnullss_0 $f set x $.
	fnnullss_1 $f class A $.
	nnullss $p |- ( A =/= (/) -> E. x ( x C_ A /\ x =/= (/) ) ) $= fnnullss_1 c0 wne innullss_0 sup_set_class fnnullss_1 wcel innullss_0 wex fnnullss_0 sup_set_class fnnullss_1 wss fnnullss_0 sup_set_class c0 wne wa fnnullss_0 wex innullss_0 fnnullss_1 n0 innullss_0 sup_set_class fnnullss_1 wcel fnnullss_0 sup_set_class fnnullss_1 wss fnnullss_0 sup_set_class c0 wne wa fnnullss_0 wex innullss_0 innullss_0 sup_set_class fnnullss_1 wcel innullss_0 sup_set_class csn fnnullss_1 wss fnnullss_0 sup_set_class fnnullss_1 wss fnnullss_0 sup_set_class c0 wne wa fnnullss_0 wex innullss_0 sup_set_class fnnullss_1 innullss_0 vex snss innullss_0 sup_set_class csn fnnullss_1 wss innullss_0 sup_set_class csn c0 wne fnnullss_0 sup_set_class fnnullss_1 wss fnnullss_0 sup_set_class c0 wne wa fnnullss_0 wex innullss_0 sup_set_class innullss_0 vex snnz fnnullss_0 sup_set_class fnnullss_1 wss fnnullss_0 sup_set_class c0 wne wa innullss_0 sup_set_class csn fnnullss_1 wss innullss_0 sup_set_class csn c0 wne wa fnnullss_0 innullss_0 sup_set_class csn innullss_0 sup_set_class snex fnnullss_0 sup_set_class innullss_0 sup_set_class csn wceq fnnullss_0 sup_set_class fnnullss_1 wss innullss_0 sup_set_class csn fnnullss_1 wss fnnullss_0 sup_set_class c0 wne innullss_0 sup_set_class csn c0 wne fnnullss_0 sup_set_class innullss_0 sup_set_class csn fnnullss_1 sseq1 fnnullss_0 sup_set_class innullss_0 sup_set_class csn c0 neeq1 anbi12d spcev mpan2 sylbi exlimiv sylbi $.
$}
$( Restricted existence in a class (even if proper) implies restricted
       existence in a subset.  (Contributed by NM, 23-Aug-2003.) $)
${
	$d x y z A $.
	$d y z ph $.
	iexss_0 $f set z $.
	fexss_0 $f wff ph $.
	fexss_1 $f set x $.
	fexss_2 $f set y $.
	fexss_3 $f class A $.
	exss $p |- ( E. x e. A ph -> E. y ( y C_ A /\ E. x e. y ph ) ) $= fexss_0 fexss_1 fexss_3 wrex iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel iexss_0 wex fexss_2 sup_set_class fexss_3 wss fexss_0 fexss_1 fexss_2 sup_set_class wrex wa fexss_2 wex fexss_0 fexss_1 fexss_3 crab c0 wne fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab c0 wne fexss_0 fexss_1 fexss_3 wrex iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel iexss_0 wex fexss_0 fexss_1 fexss_3 crab fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab c0 fexss_0 fexss_1 fexss_3 df-rab neeq1i fexss_0 fexss_1 fexss_3 rabn0 iexss_0 fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab n0 3bitr3i iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel fexss_2 sup_set_class fexss_3 wss fexss_0 fexss_1 fexss_2 sup_set_class wrex wa fexss_2 wex iexss_0 iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel iexss_0 sup_set_class csn fexss_3 wss fexss_0 fexss_1 iexss_0 sup_set_class csn wrex fexss_2 sup_set_class fexss_3 wss fexss_0 fexss_1 fexss_2 sup_set_class wrex wa fexss_2 wex iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel iexss_0 sup_set_class csn fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wss iexss_0 sup_set_class csn fexss_3 wss iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab iexss_0 vex snss iexss_0 sup_set_class csn fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wss fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab fexss_3 wss iexss_0 sup_set_class csn fexss_3 wss fexss_0 fexss_1 fexss_3 ssab2 iexss_0 sup_set_class csn fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab fexss_3 sstr2 mpi sylbi iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel fexss_0 fexss_1 iexss_0 sup_set_class csn crab c0 wne fexss_0 fexss_1 iexss_0 sup_set_class csn wrex iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel iexss_0 sup_set_class fexss_0 fexss_1 iexss_0 sup_set_class csn crab wcel fexss_0 fexss_1 iexss_0 sup_set_class csn crab c0 wne fexss_1 sup_set_class fexss_3 wcel fexss_1 iexss_0 wsb fexss_0 fexss_1 iexss_0 wsb wa fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_1 iexss_0 wsb fexss_0 fexss_1 iexss_0 wsb wa iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel iexss_0 sup_set_class fexss_0 fexss_1 iexss_0 sup_set_class csn crab wcel fexss_1 sup_set_class fexss_3 wcel fexss_1 iexss_0 wsb fexss_0 fexss_1 iexss_0 wsb wa fexss_0 fexss_1 iexss_0 wsb fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_1 iexss_0 wsb fexss_1 sup_set_class fexss_3 wcel fexss_1 iexss_0 wsb fexss_0 fexss_1 iexss_0 wsb simpr fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_1 iexss_0 wsb fexss_1 sup_set_class iexss_0 sup_set_class wceq fexss_1 iexss_0 wsb fexss_1 iexss_0 equsb1 fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_1 sup_set_class iexss_0 sup_set_class wceq fexss_1 iexss_0 fexss_1 iexss_0 sup_set_class elsn sbbii mpbir jctil iexss_0 sup_set_class fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 cab wcel fexss_1 sup_set_class fexss_3 wcel fexss_0 wa fexss_1 iexss_0 wsb fexss_1 sup_set_class fexss_3 wcel fexss_1 iexss_0 wsb fexss_0 fexss_1 iexss_0 wsb wa fexss_1 sup_set_class fexss_3 wcel fexss_0 wa iexss_0 fexss_1 df-clab fexss_1 sup_set_class fexss_3 wcel fexss_0 fexss_1 iexss_0 sban bitri iexss_0 sup_set_class fexss_0 fexss_1 iexss_0 sup_set_class csn crab wcel iexss_0 sup_set_class fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_0 wa fexss_1 cab wcel fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_1 iexss_0 wsb fexss_0 fexss_1 iexss_0 wsb wa fexss_0 fexss_1 iexss_0 sup_set_class csn crab fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_0 wa fexss_1 cab iexss_0 sup_set_class fexss_0 fexss_1 iexss_0 sup_set_class csn df-rab eleq2i iexss_0 sup_set_class fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_0 wa fexss_1 cab wcel fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_0 wa fexss_1 iexss_0 wsb fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_1 iexss_0 wsb fexss_0 fexss_1 iexss_0 wsb wa fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_0 wa iexss_0 fexss_1 df-clab fexss_1 sup_set_class iexss_0 sup_set_class csn wcel fexss_0 fexss_1 iexss_0 sban bitri bitri 3imtr4i fexss_0 fexss_1 iexss_0 sup_set_class csn crab iexss_0 sup_set_class ne0i syl fexss_0 fexss_1 iexss_0 sup_set_class csn rabn0 sylib fexss_2 sup_set_class fexss_3 wss fexss_0 fexss_1 fexss_2 sup_set_class wrex wa iexss_0 sup_set_class csn fexss_3 wss fexss_0 fexss_1 iexss_0 sup_set_class csn wrex wa fexss_2 iexss_0 sup_set_class csn iexss_0 sup_set_class snex fexss_2 sup_set_class iexss_0 sup_set_class csn wceq fexss_2 sup_set_class fexss_3 wss iexss_0 sup_set_class csn fexss_3 wss fexss_0 fexss_1 fexss_2 sup_set_class wrex fexss_0 fexss_1 iexss_0 sup_set_class csn wrex fexss_2 sup_set_class iexss_0 sup_set_class csn fexss_3 sseq1 fexss_0 fexss_1 fexss_2 sup_set_class iexss_0 sup_set_class csn rexeq anbi12d spcev syl2anc exlimiv sylbi $.
$}
$( An ordered pair of classes is a set.  Exercise 7 of [TakeutiZaring]
     p. 16.  (Contributed by NM, 18-Aug-1993.)  (Revised by Mario Carneiro,
     26-Apr-2015.) $)
${
	fopex_0 $f class A $.
	fopex_1 $f class B $.
	opex $p |- <. A , B >. e. _V $= fopex_0 fopex_1 cop fopex_0 cvv wcel fopex_1 cvv wcel wa fopex_0 csn fopex_0 fopex_1 cpr cpr c0 cif cvv fopex_0 fopex_1 dfopif fopex_0 cvv wcel fopex_1 cvv wcel wa fopex_0 csn fopex_0 fopex_1 cpr cpr c0 fopex_0 csn fopex_0 fopex_1 cpr prex 0ex ifex eqeltri $.
$}
$( An ordered triple of classes is a set.  (Contributed by NM,
     3-Apr-2015.) $)
${
	fotex_0 $f class A $.
	fotex_1 $f class B $.
	fotex_2 $f class C $.
	otex $p |- <. A , B , C >. e. _V $= fotex_0 fotex_1 fotex_2 cotp fotex_0 fotex_1 cop fotex_2 cop cvv fotex_0 fotex_1 fotex_2 df-ot fotex_0 fotex_1 cop fotex_2 opex eqeltri $.
$}
$( An ordered pair has two elements.  Exercise 3 of [TakeutiZaring] p. 15.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
${
	felop_0 $f class A $.
	felop_1 $f class B $.
	felop_2 $f class C $.
	eelop_0 $e |- A e. _V $.
	eelop_1 $e |- B e. _V $.
	eelop_2 $e |- C e. _V $.
	elop $p |- ( A e. <. B , C >. <-> ( A = { B } \/ A = { B , C } ) ) $= felop_0 felop_1 felop_2 cop wcel felop_0 felop_1 csn felop_1 felop_2 cpr cpr wcel felop_0 felop_1 csn wceq felop_0 felop_1 felop_2 cpr wceq wo felop_1 felop_2 cop felop_1 csn felop_1 felop_2 cpr cpr felop_0 felop_1 felop_2 eelop_1 eelop_2 dfop eleq2i felop_0 felop_1 csn felop_1 felop_2 cpr eelop_0 elpr bitri $.
$}
$( One of the two elements in an ordered pair.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	fopi1_0 $f class A $.
	fopi1_1 $f class B $.
	eopi1_0 $e |- A e. _V $.
	eopi1_1 $e |- B e. _V $.
	opi1 $p |- { A } e. <. A , B >. $= fopi1_0 csn fopi1_0 csn fopi1_0 fopi1_1 cpr cpr fopi1_0 fopi1_1 cop fopi1_0 csn fopi1_0 fopi1_1 cpr fopi1_0 snex prid1 fopi1_0 fopi1_1 eopi1_0 eopi1_1 dfop eleqtrri $.
$}
$( One of the two elements of an ordered pair.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	fopi2_0 $f class A $.
	fopi2_1 $f class B $.
	eopi2_0 $e |- A e. _V $.
	eopi2_1 $e |- B e. _V $.
	opi2 $p |- { A , B } e. <. A , B >. $= fopi2_0 fopi2_1 cpr fopi2_0 csn fopi2_0 fopi2_1 cpr cpr fopi2_0 fopi2_1 cop fopi2_0 csn fopi2_0 fopi2_1 cpr fopi2_0 fopi2_1 prex prid2 fopi2_0 fopi2_1 eopi2_0 eopi2_1 dfop eleqtrri $.
$}

