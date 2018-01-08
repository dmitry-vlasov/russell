
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Derive_the_Axiom_of_Separation.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Derive the Null Set Axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    zfnuleu.1 $e |- E. x A. y -. y e. x $.
    $( Show the uniqueness of the empty set (using the Axiom of Extensionality
       via ~ bm1.1 to strengthen the hypothesis in the form of ~ axnul ).
       (Contributed by NM, 22-Dec-2007.) $)
    zfnuleu $p |- E! x A. y -. y e. x $=
      vy cv vx cv wcel wn vy wal vx weu vy cv vx cv wcel wfal wb vy wal vx weu
      vy cv vx cv wcel wfal wb vy wal vx wex vy cv vx cv wcel wfal wb vy wal vx
      weu vy cv vx cv wcel wn vy wal vx wex vy cv vx cv wcel wfal wb vy wal vx
      wex zfnuleu.1 vy cv vx cv wcel wn vy wal vy cv vx cv wcel wfal wb vy wal
      vx vy cv vx cv wcel wn vy cv vx cv wcel wfal wb vy vy cv vx cv wcel nbfal
      albii exbii mpbi wfal vx vy wfal vx nfv bm1.1 ax-mp vy cv vx cv wcel wn
      vy wal vy cv vx cv wcel wfal wb vy wal vx vy cv vx cv wcel wn vy cv vx cv
      wcel wfal wb vy vy cv vx cv wcel nbfal albii eubii mpbir $.
  $}

  ${
    $d x y z w $.
    $( Prove ~ axnul directly from ~ ax-rep using none of the equality axioms
       ~ ax-8 through ~ ax-15 provided we accept ~ sp as an axiom.  Replace
       ~ sp with the obsolete ~ ax-4 to see this in 'show trace_back'.
       (Contributed by Jeff Hoffman, 3-Feb-2008.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axnulALT $p |- E. x A. y -. y e. x $=
      vy cv vx cv wcel wn vy wal vx wex vy cv vx cv wcel vw cv vz cv wcel wfal
      vx wal wa vw wex wb vy wal vx wex wfal vx wal vy cv vx cv wceq wi vy wal
      vx wex vy cv vx cv wcel vw cv vz cv wcel wfal vx wal wa vw wex wb vy wal
      vx wex vw wfal vz vx vy vw ax-rep wfal vx wal vy cv vx cv wceq wi wfal vx
      wal vy cv vx cv wceq wi vy wal vx wex vy wfal vx wal vy cv vx cv wceq wi
      vy wal wfal vx wal vy cv vx cv wceq wi vy wal wn vx wal wn wfal vx wal vy
      cv vx cv wceq wi vy wal vx wex wfal vx wal vy cv vx cv wceq wi vy wal wn
      vx wal wfal vx wal vy cv vx cv wceq wi vy wal wfal vx wal vy cv vx cv
      wceq wi vy wal wn vx sp con2i wfal vx wal vy cv vx cv wceq wi vy wal vx
      df-ex sylibr wfal vx wal vy cv vx cv wceq wfal vx wal wfal fal wfal vx sp
      mto pm2.21i mpg mpg vy cv vx cv wcel wn vy wal vy cv vx cv wcel vw cv vz
      cv wcel wfal vx wal wa vw wex wb vy wal vx vy cv vx cv wcel wn vy cv vx
      cv wcel vw cv vz cv wcel wfal vx wal wa vw wex wb vy vw cv vz cv wcel
      wfal vx wal wa vw wex vy cv vx cv wcel vw cv vz cv wcel wfal vx wal wa vw
      wfal vx wal vw cv vz cv wcel wfal vx wal wfal fal wfal vx sp mto intnan
      nex nbn albii exbii mpbir $.

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
    axnul $p |- E. x A. y -. y e. x $=
      vy cv vx cv wcel vy cv vz cv wcel vy cv vy cv wcel vy cv vy cv wcel wn wa
      wa wb vy wal vx wex vy cv vx cv wcel wn vy wal vx wex vy cv vy cv wcel vy
      cv vy cv wcel wn wa vy vx vz ax-sep vy cv vx cv wcel vy cv vz cv wcel vy
      cv vy cv wcel vy cv vy cv wcel wn wa wa wb vy wal vy cv vx cv wcel wn vy
      wal vx vy cv vx cv wcel vy cv vz cv wcel vy cv vy cv wcel vy cv vy cv
      wcel wn wa wa wb vy cv vx cv wcel wn vy vy cv vx cv wcel vy cv vz cv wcel
      vy cv vy cv wcel vy cv vy cv wcel wn wa wa wb vy cv vx cv wcel vy cv vz
      cv wcel vy cv vy cv wcel vy cv vy cv wcel wn wa wa vy cv vy cv wcel vy cv
      vy cv wcel wn wa vy cv vz cv wcel vy cv vy cv wcel pm3.24 intnan vy cv vx
      cv wcel vy cv vz cv wcel vy cv vy cv wcel vy cv vy cv wcel wn wa wa wb id
      mtbiri alimi eximi ax-mp $.

    $( The Null Set Axiom of ZF set theory.  It was derived as ~ axnul above
       and is therefore redundant, but we state it as a separate axiom here so
       that its uses can be identified more easily.  (Contributed by NM,
       7-Aug-2003.) $)
    ax-nul $a |- E. x A. y -. y e. x $.

    $( The Null Set Axiom of ZF set theory: the empty set exists.  Corollary
       5.16 of [TakeutiZaring] p. 20.  For the unabbreviated version, see
       ~ ax-nul .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 9-Jul-2011.) $)
    0ex $p |- (/) e. _V $=
      vx c0 vx cv c0 wceq vx wex vy cv vx cv wcel wn vy wal vx wex vx vy ax-nul
      vx cv c0 wceq vy cv vx cv wcel wn vy wal vx vy vx cv eq0 exbii mpbir
      issetri $.
  $}



