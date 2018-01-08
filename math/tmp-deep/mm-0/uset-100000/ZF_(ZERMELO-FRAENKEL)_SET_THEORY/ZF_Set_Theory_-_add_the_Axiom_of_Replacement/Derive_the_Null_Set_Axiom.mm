$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Derive_the_Axiom_of_Separation.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Derive the Null Set Axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Show the uniqueness of the empty set (using the Axiom of Extensionality
       via ~ bm1.1 to strengthen the hypothesis in the form of ~ axnul ).
       (Contributed by NM, 22-Dec-2007.) $)
${
	$d x y $.
	fzfnuleu_0 $f set x $.
	fzfnuleu_1 $f set y $.
	ezfnuleu_0 $e |- E. x A. y -. y e. x $.
	zfnuleu $p |- E! x A. y -. y e. x $= fzfnuleu_1 cv fzfnuleu_0 cv wcel wn fzfnuleu_1 wal fzfnuleu_0 weu fzfnuleu_1 cv fzfnuleu_0 cv wcel wfal wb fzfnuleu_1 wal fzfnuleu_0 weu fzfnuleu_1 cv fzfnuleu_0 cv wcel wfal wb fzfnuleu_1 wal fzfnuleu_0 wex fzfnuleu_1 cv fzfnuleu_0 cv wcel wfal wb fzfnuleu_1 wal fzfnuleu_0 weu fzfnuleu_1 cv fzfnuleu_0 cv wcel wn fzfnuleu_1 wal fzfnuleu_0 wex fzfnuleu_1 cv fzfnuleu_0 cv wcel wfal wb fzfnuleu_1 wal fzfnuleu_0 wex ezfnuleu_0 fzfnuleu_1 cv fzfnuleu_0 cv wcel wn fzfnuleu_1 wal fzfnuleu_1 cv fzfnuleu_0 cv wcel wfal wb fzfnuleu_1 wal fzfnuleu_0 fzfnuleu_1 cv fzfnuleu_0 cv wcel wn fzfnuleu_1 cv fzfnuleu_0 cv wcel wfal wb fzfnuleu_1 fzfnuleu_1 cv fzfnuleu_0 cv wcel nbfal albii exbii mpbi wfal fzfnuleu_0 fzfnuleu_1 wfal fzfnuleu_0 nfv bm1.1 ax-mp fzfnuleu_1 cv fzfnuleu_0 cv wcel wn fzfnuleu_1 wal fzfnuleu_1 cv fzfnuleu_0 cv wcel wfal wb fzfnuleu_1 wal fzfnuleu_0 fzfnuleu_1 cv fzfnuleu_0 cv wcel wn fzfnuleu_1 cv fzfnuleu_0 cv wcel wfal wb fzfnuleu_1 fzfnuleu_1 cv fzfnuleu_0 cv wcel nbfal albii eubii mpbir $.
$}
$( Prove ~ axnul directly from ~ ax-rep using none of the equality axioms
       ~ ax-8 through ~ ax-15 provided we accept ~ sp as an axiom.  Replace
       ~ sp with the obsolete ~ ax-4 to see this in 'show trace_back'.
       (Contributed by Jeff Hoffman, 3-Feb-2008.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d x y z w $.
	iaxnulALT_0 $f set z $.
	iaxnulALT_1 $f set w $.
	faxnulALT_0 $f set x $.
	faxnulALT_1 $f set y $.
	axnulALT $p |- E. x A. y -. y e. x $= faxnulALT_1 cv faxnulALT_0 cv wcel wn faxnulALT_1 wal faxnulALT_0 wex faxnulALT_1 cv faxnulALT_0 cv wcel iaxnulALT_1 cv iaxnulALT_0 cv wcel wfal faxnulALT_0 wal wa iaxnulALT_1 wex wb faxnulALT_1 wal faxnulALT_0 wex wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal faxnulALT_0 wex faxnulALT_1 cv faxnulALT_0 cv wcel iaxnulALT_1 cv iaxnulALT_0 cv wcel wfal faxnulALT_0 wal wa iaxnulALT_1 wex wb faxnulALT_1 wal faxnulALT_0 wex iaxnulALT_1 wfal iaxnulALT_0 faxnulALT_0 faxnulALT_1 iaxnulALT_1 ax-rep wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal faxnulALT_0 wex faxnulALT_1 wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal wn faxnulALT_0 wal wn wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal faxnulALT_0 wex wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal wn faxnulALT_0 wal wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal wn faxnulALT_0 sp con2i wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wi faxnulALT_1 wal faxnulALT_0 df-ex sylibr wfal faxnulALT_0 wal faxnulALT_1 cv faxnulALT_0 cv wceq wfal faxnulALT_0 wal wfal fal wfal faxnulALT_0 sp mto pm2.21i mpg mpg faxnulALT_1 cv faxnulALT_0 cv wcel wn faxnulALT_1 wal faxnulALT_1 cv faxnulALT_0 cv wcel iaxnulALT_1 cv iaxnulALT_0 cv wcel wfal faxnulALT_0 wal wa iaxnulALT_1 wex wb faxnulALT_1 wal faxnulALT_0 faxnulALT_1 cv faxnulALT_0 cv wcel wn faxnulALT_1 cv faxnulALT_0 cv wcel iaxnulALT_1 cv iaxnulALT_0 cv wcel wfal faxnulALT_0 wal wa iaxnulALT_1 wex wb faxnulALT_1 iaxnulALT_1 cv iaxnulALT_0 cv wcel wfal faxnulALT_0 wal wa iaxnulALT_1 wex faxnulALT_1 cv faxnulALT_0 cv wcel iaxnulALT_1 cv iaxnulALT_0 cv wcel wfal faxnulALT_0 wal wa iaxnulALT_1 wfal faxnulALT_0 wal iaxnulALT_1 cv iaxnulALT_0 cv wcel wfal faxnulALT_0 wal wfal fal wfal faxnulALT_0 sp mto intnan nex nbn albii exbii mpbir $.
$}
$( The Null Set Axiom of ZF set theory: there exists a set with no
       elements.  Axiom of Empty Set of [Enderton] p. 18.  In some textbooks,
       this is presented as a separate axiom; here we show it can be derived
       from Separation ~ ax-sep .  This version of the Null Set Axiom tells us
       that at least one empty set exists, but does not tell us that it is
       unique - we need the Axiom of Extensionality to do that (see
       ~ zfnuleu ).

       This proof, suggested by Jeff Hoffman, uses only ~ ax-5 and ~ ax-gen
       from predicate calculus, which are valid in "free logic" i.e. logic
       holding in an empty domain (see Axiom A5 and Rule R2 of [LeBlanc]
       p. 277).  Thus, our ~ ax-sep implies the existence of at least one set.
       Note that Kunen's version of ~ ax-sep (Axiom 3 of [Kunen] p. 11) does
       not imply the existence of a set because his is universally closed i.e.
       prefixed with universal quantifiers to eliminate all free variables.
       His existence is provided by a separate axiom stating ` E. x x = x `
       (Axiom 0 of [Kunen] p. 10).

       See ~ axnulALT for a proof directly from ~ ax-rep .

       This theorem should not be referenced by any proof.  Instead, use
       ~ ax-nul below so that the uses of the Null Set Axiom can be more easily
       identified.  (Contributed by Jeff Hoffman, 3-Feb-2008.)  (Revised by NM,
       4-Feb-2008.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
${
	$d x y z $.
	iaxnul_0 $f set z $.
	faxnul_0 $f set x $.
	faxnul_1 $f set y $.
	axnul $p |- E. x A. y -. y e. x $= faxnul_1 cv faxnul_0 cv wcel faxnul_1 cv iaxnul_0 cv wcel faxnul_1 cv faxnul_1 cv wcel faxnul_1 cv faxnul_1 cv wcel wn wa wa wb faxnul_1 wal faxnul_0 wex faxnul_1 cv faxnul_0 cv wcel wn faxnul_1 wal faxnul_0 wex faxnul_1 cv faxnul_1 cv wcel faxnul_1 cv faxnul_1 cv wcel wn wa faxnul_1 faxnul_0 iaxnul_0 ax-sep faxnul_1 cv faxnul_0 cv wcel faxnul_1 cv iaxnul_0 cv wcel faxnul_1 cv faxnul_1 cv wcel faxnul_1 cv faxnul_1 cv wcel wn wa wa wb faxnul_1 wal faxnul_1 cv faxnul_0 cv wcel wn faxnul_1 wal faxnul_0 faxnul_1 cv faxnul_0 cv wcel faxnul_1 cv iaxnul_0 cv wcel faxnul_1 cv faxnul_1 cv wcel faxnul_1 cv faxnul_1 cv wcel wn wa wa wb faxnul_1 cv faxnul_0 cv wcel wn faxnul_1 faxnul_1 cv faxnul_0 cv wcel faxnul_1 cv iaxnul_0 cv wcel faxnul_1 cv faxnul_1 cv wcel faxnul_1 cv faxnul_1 cv wcel wn wa wa wb faxnul_1 cv faxnul_0 cv wcel faxnul_1 cv iaxnul_0 cv wcel faxnul_1 cv faxnul_1 cv wcel faxnul_1 cv faxnul_1 cv wcel wn wa wa faxnul_1 cv faxnul_1 cv wcel faxnul_1 cv faxnul_1 cv wcel wn wa faxnul_1 cv iaxnul_0 cv wcel faxnul_1 cv faxnul_1 cv wcel pm3.24 intnan faxnul_1 cv faxnul_0 cv wcel faxnul_1 cv iaxnul_0 cv wcel faxnul_1 cv faxnul_1 cv wcel faxnul_1 cv faxnul_1 cv wcel wn wa wa wb id mtbiri alimi eximi ax-mp $.
$}
$( The Null Set Axiom of ZF set theory.  It was derived as ~ axnul above
       and is therefore redundant, but we state it as a separate axiom here so
       that its uses can be identified more easily.  (Contributed by NM,
       7-Aug-2003.) $)
${
	$d x y $.
	fax-nul_0 $f set x $.
	fax-nul_1 $f set y $.
	ax-nul $a |- E. x A. y -. y e. x $.
$}
$( The Null Set Axiom of ZF set theory: the empty set exists.  Corollary
       5.16 of [TakeutiZaring] p. 20.  For the unabbreviated version, see
       ~ ax-nul .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 9-Jul-2011.) $)
${
	$d x y $.
	i0ex_0 $f set x $.
	i0ex_1 $f set y $.
	0ex $p |- (/) e. _V $= i0ex_0 c0 i0ex_0 cv c0 wceq i0ex_0 wex i0ex_1 cv i0ex_0 cv wcel wn i0ex_1 wal i0ex_0 wex i0ex_0 i0ex_1 ax-nul i0ex_0 cv c0 wceq i0ex_1 cv i0ex_0 cv wcel wn i0ex_1 wal i0ex_0 i0ex_1 i0ex_0 cv eq0 exbii mpbir issetri $.
$}

