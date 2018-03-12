
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Introduce the Axiom of Extensionality

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d x y z $.
    $( Axiom of Extensionality.  An axiom of Zermelo-Fraenkel set theory.  It
       states that two sets are identical if they contain the same elements.
       Axiom Ext of [BellMachover] p. 461.

       Set theory can also be formulated with a _single_ primitive predicate
       ` e. ` on top of traditional predicate calculus _without_ equality.  In
       that case the Axiom of Extensionality becomes
       ` ( A. w ( w e. x <-> w e. y ) -> ( x e. z -> y e. z ) ) ` , and
       equality ` x = y ` is _defined_ as ` A. w ( w e. x <-> w e. y ) ` .  All
       of the usual axioms of equality then become theorems of set theory.
       See, for example, Axiom 1 of [TakeutiZaring] p. 8.

       To use the above "equality-free" version of Extensionality with
       Metamath's logical axioms, we would rewrite ~ ax-8 through ~ ax-16 with
       equality expanded according to the above definition.  Some of those
       axioms could be proved from set theory and would be redundant.  Not all
       of them are redundant, since our axioms of predicate calculus make
       essential use of equality for the proper substitution that is a
       primitive notion in traditional predicate calculus.  A study of such an
       axiomatization would be an interesting project for someone exploring the
       foundations of logic.

       _General remarks_:  Our set theory axioms are presented using defined
       connectives ( ` <-> ` , ` E. ` , etc.) for convenience.  However, it is
       implicitly understood that the actual axioms use only the primitive
       connectives ` -> ` , ` -. ` , ` A. ` , ` = ` , and ` e. ` .  It is
       straightforward to establish the equivalence between the actual axioms
       and the ones we display, and we will not do so.

       It is important to understand that strictly speaking, all of our set
       theory axioms are really schemes that represent an infinite number of
       actual axioms.  This is inherent in the design of Metamath
       ("metavariable math"), which manipulates only metavariables.  For
       example, the metavariable ` x ` in ~ ax-ext can represent any actual
       variable _v1_, _v2_, _v3_,... .  Distinct variable restrictions ($d)
       prevent us from substituting say _v1_ for both ` x ` and ` z ` .  This
       is in contrast to typical textbook presentations that present actual
       axioms (except for Replacement ~ ax-rep , which involves a wff
       metavariable).  In practice, though, the theorems and proofs are
       essentially the same.  The $d restrictions make each of the infinite
       axioms generated by the ~ ax-ext scheme exactly logically equivalent to
       each other and in particular to the actual axiom of the textbook
       version.  (Contributed by NM, 5-Aug-1993.) $)
    ax-ext $a |- ( A. z ( z e. x <-> z e. y ) -> x = y ) $.

    $( The Axiom of Extensionality ( ~ ax-ext ) restated so that it postulates
       the existence of a set ` z ` given two arbitrary sets ` x ` and ` y ` .
       This way to express it follows the general idea of the other ZFC axioms,
       which is to postulate the existence of sets given other sets.
       (Contributed by NM, 28-Sep-2003.) $)
    axext2 $p |- E. z ( ( z e. x <-> z e. y ) -> x = y ) $=
      vz cv vx cv wcel vz cv vy cv wcel wb vx cv vy cv wceq wi vz wex vz cv vx
      cv wcel vz cv vy cv wcel wb vz wal vx cv vy cv wceq wi vx vy vz ax-ext vz
      cv vx cv wcel vz cv vy cv wcel wb vx cv vy cv wceq vz 19.36v mpbir $.
  $}

  ${
    $d z x w $.  $d z y w $.
    $( A generalization of the Axiom of Extensionality in which ` x ` and ` y `
       need not be distinct.  (Contributed by NM, 15-Sep-1993.)  (Proof
       shortened by Andrew Salmon, 12-Aug-2011.) $)
    axext3 $p |- ( A. z ( z e. x <-> z e. y ) -> x = y ) $=
      vz cv vw cv wcel vz cv vy cv wcel wb vz wal vw cv vy cv wceq wi vz cv vx
      cv wcel vz cv vy cv wcel wb vz wal vx cv vy cv wceq wi vw vx vw cv vx cv
      wceq vz cv vw cv wcel vz cv vy cv wcel wb vz wal vz cv vx cv wcel vz cv
      vy cv wcel wb vz wal vw cv vy cv wceq vx cv vy cv wceq vw cv vx cv wceq
      vz cv vw cv wcel vz cv vy cv wcel wb vz cv vx cv wcel vz cv vy cv wcel wb
      vz vw cv vx cv wceq vz cv vw cv wcel vz cv vx cv wcel vz cv vy cv wcel vw
      vx vz elequ2 bibi1d albidv vw vx vy equequ1 imbi12d vw vy vz ax-ext
      chvarv $.

    $( A bidirectional version of Extensionality.  Although this theorem
       "looks" like it is just a definition of equality, it requires the Axiom
       of Extensionality for its proof under our axiomatization.  See the
       comments for ~ ax-ext and ~ df-cleq .  (Contributed by NM,
       14-Nov-2008.) $)
    axext4 $p |- ( x = y <-> A. z ( z e. x <-> z e. y ) ) $=
      vx cv vy cv wceq vz cv vx cv wcel vz cv vy cv wcel wb vz wal vx cv vy cv
      wceq vz cv vx cv wcel vz cv vy cv wcel wb vz vx vy vz elequ2 alrimiv vx
      vy vz axext3 impbii $.
  $}

  ${
    $d x y z $.  $d ph z $.
    bm1.1.1 $e |- F/ x ph $.
    $( Any set defined by a property is the only set defined by that property.
       Theorem 1.1 of [BellMachover] p. 462.  (Contributed by NM,
       30-Jun-1994.) $)
    bm1.1 $p |- ( E. x A. y ( y e. x <-> ph ) ->
                  E! x A. y ( y e. x <-> ph ) ) $=
      vy cv vx cv wcel wph wb vy wal vx wex vy cv vx cv wcel wph wb vy wal vx
      wex vy cv vx cv wcel wph wb vy wal vy cv vx cv wcel wph wb vy wal vx vz
      wsb wa vx cv vz cv wceq wi vz wal vx wal wa vy cv vx cv wcel wph wb vy
      wal vx weu vy cv vx cv wcel wph wb vy wal vx wex vy cv vx cv wcel wph wb
      vy wal vy cv vx cv wcel wph wb vy wal vx vz wsb wa vx cv vz cv wceq wi vz
      wal vx wal vy cv vx cv wcel wph wb vy wal vy cv vx cv wcel wph wb vy wal
      vx vz wsb wa vx cv vz cv wceq wi vx vz vy cv vx cv wcel wph wb vy wal vx
      vz wsb vy cv vx cv wcel wph wb vy wal vy cv vz cv wcel wph wb vy wal vx
      cv vz cv wceq vy cv vx cv wcel wph wb vy wal vy cv vz cv wcel wph wb vy
      wal vx vz vy cv vz cv wcel wph wb vx vy vy cv vz cv wcel wph vx vy cv vz
      cv wcel vx nfv bm1.1.1 nfbi nfal vx cv vz cv wceq vy cv vx cv wcel wph wb
      vy cv vz cv wcel wph wb vy vx cv vz cv wceq vy cv vx cv wcel vy cv vz cv
      wcel wph vx vz vy elequ2 bibi1d albidv sbie vy cv vx cv wcel wph wb vy
      wal vy cv vz cv wcel wph wb vy wal wa vy cv vx cv wcel wph wb vy cv vz cv
      wcel wph wb wa vy wal vx cv vz cv wceq vy cv vx cv wcel wph wb vy cv vz
      cv wcel wph wb vy 19.26 vy cv vx cv wcel wph wb vy cv vz cv wcel wph wb
      wa vy wal vy cv vx cv wcel vy cv vz cv wcel wb vy wal vx cv vz cv wceq vy
      cv vx cv wcel wph wb vy cv vz cv wcel wph wb wa vy cv vx cv wcel vy cv vz
      cv wcel wb vy vy cv vx cv wcel wph vy cv vz cv wcel biantr alimi vx vz vy
      ax-ext syl sylbir sylan2b gen2 jctr vy cv vx cv wcel wph wb vy wal vx vz
      vy cv vx cv wcel wph wb vy wal vz nfv eu2 sylibr $.
  $}


