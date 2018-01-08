
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Introduce the Axiom of Power Sets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z w $.
    $( Axiom of Power Sets.  An axiom of Zermelo-Fraenkel set theory.  It
       states that a set ` y ` exists that includes the power set of a given
       set ` x ` i.e. contains every subset of ` x ` .  The variant ~ axpow2
       uses explicit subset notation.  A version using class notation is
       ~ pwex .  (Contributed by NM, 5-Aug-1993.) $)
    ax-pow $a |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $.

    $( Axiom of Power Sets expressed with the fewest number of different
       variables.  (Contributed by NM, 14-Aug-2003.) $)
    zfpow $p |- E. x A. y ( A. x ( x e. y -> x e. z ) -> y e. x ) $=
      vw cv vy cv wcel vw cv vz cv wcel wi vw wal vy cv vx cv wcel wi vy wal vx
      wex vx cv vy cv wcel vx cv vz cv wcel wi vx wal vy cv vx cv wcel wi vy
      wal vx wex vz vx vy vw ax-pow vw cv vy cv wcel vw cv vz cv wcel wi vw wal
      vy cv vx cv wcel wi vy wal vx cv vy cv wcel vx cv vz cv wcel wi vx wal vy
      cv vx cv wcel wi vy wal vx vw cv vy cv wcel vw cv vz cv wcel wi vw wal vy
      cv vx cv wcel wi vx cv vy cv wcel vx cv vz cv wcel wi vx wal vy cv vx cv
      wcel wi vy vw cv vy cv wcel vw cv vz cv wcel wi vw wal vx cv vy cv wcel
      vx cv vz cv wcel wi vx wal vy cv vx cv wcel vw cv vy cv wcel vw cv vz cv
      wcel wi vx cv vy cv wcel vx cv vz cv wcel wi vw vx vw cv vx cv wceq vw cv
      vy cv wcel vx cv vy cv wcel vw cv vz cv wcel vx cv vz cv wcel vw vx vy
      elequ1 vw vx vz elequ1 imbi12d cbvalv imbi1i albii exbii mpbi $.

    $( A variant of the Axiom of Power Sets ~ ax-pow using subset notation.
       Problem in {BellMachover] p. 466.  (Contributed by NM, 4-Jun-2006.) $)
    axpow2 $p |- E. y A. z ( z C_ x -> z e. y ) $=
      vz cv vx cv wss vz cv vy cv wcel wi vz wal vy wex vw cv vz cv wcel vw cv
      vx cv wcel wi vw wal vz cv vy cv wcel wi vz wal vy wex vx vy vz vw ax-pow
      vz cv vx cv wss vz cv vy cv wcel wi vz wal vw cv vz cv wcel vw cv vx cv
      wcel wi vw wal vz cv vy cv wcel wi vz wal vy vz cv vx cv wss vz cv vy cv
      wcel wi vw cv vz cv wcel vw cv vx cv wcel wi vw wal vz cv vy cv wcel wi
      vz vz cv vx cv wss vw cv vz cv wcel vw cv vx cv wcel wi vw wal vz cv vy
      cv wcel vw vz cv vx cv dfss2 imbi1i albii exbii mpbir $.

    $( A variant of the Axiom of Power Sets ~ ax-pow .  For any set ` x ` ,
       there exists a set ` y ` whose members are exactly the subsets of ` x `
       i.e. the power set of ` x ` .  Axiom Pow of [BellMachover] p. 466.
       (Contributed by NM, 4-Jun-2006.) $)
    axpow3 $p |- E. y A. z ( z C_ x <-> z e. y ) $=
      vz cv vx cv wss vz cv vy cv wcel wb vz wal vy wex vz cv vy cv wcel vz cv
      vx cv wss wb vz wal vy wex vz cv vx cv wss vy vz vx vy vz axpow2 bm1.3ii
      vz cv vx cv wss vz cv vy cv wcel wb vz wal vz cv vy cv wcel vz cv vx cv
      wss wb vz wal vy vz cv vx cv wss vz cv vy cv wcel wb vz cv vy cv wcel vz
      cv vx cv wss wb vz vz cv vx cv wss vz cv vy cv wcel bicom albii exbii
      mpbir $.
  $}

  ${
    $d w x y z $.
    $( Every set is an element of some other set.  See ~ elALT for a shorter
       proof using more axioms.  (Contributed by NM, 4-Jan-2002.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)
    el $p |- E. y x e. y $=
      vy cv vz cv wcel vy cv vx cv wcel wi vy wal vz cv vy cv wcel wi vz wal vy
      wex vx cv vy cv wcel vy wex vy vz vx zfpow vy cv vz cv wcel vy cv vx cv
      wcel wi vy wal vz cv vy cv wcel wi vz wal vx cv vy cv wcel vy vy cv vz cv
      wcel vy cv vx cv wcel wi vy wal vz cv vy cv wcel wi vx cv vy cv wcel vz
      vx vz cv vx cv wceq vy cv vz cv wcel vy cv vx cv wcel wi vy wal vz cv vy
      cv wcel vx cv vy cv wcel vz cv vx cv wceq vy cv vz cv wcel vy cv vx cv
      wcel wi vy vz vx vy ax-14 alrimiv vz vx vy ax-13 embantd spimv eximi
      ax-mp $.
  $}

  ${
    $d A x y z $.
    zfpowcl.1 $e |- A e. _V $.
    $( Power set axiom expressed in class notation.  Axiom 4 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 25-Jul-2011.) $)
    pwex $p |- ~P A e. _V $=
      vz cv cpw cvv wcel cA cpw cvv wcel vz cA zfpowcl.1 vz cv cA wceq vz cv
      cpw cA cpw cvv vz cv cA pweq eleq1d vz cv cpw vy cv vz cv wss vy cab cvv
      vy vz cv df-pw vx vy cv vz cv wss vy cab vx cv vy cv vz cv wss vy cab
      wceq vx wex vy cv vx cv wcel vy cv vz cv wss wb vy wal vx wex vy cv vz cv
      wss vx vy vz vx vy axpow2 bm1.3ii vx cv vy cv vz cv wss vy cab wceq vy cv
      vx cv wcel vy cv vz cv wss wb vy wal vx vy cv vz cv wss vy vx cv abeq2
      exbii mpbir issetri eqeltri vtocl $.
  $}

  ${
    $d x A $.
    $( Power set axiom expressed in class notation, with the sethood
       requirement as an antecedent.  Axiom 4 of [TakeutiZaring] p. 17.
       (Contributed by NM, 30-Oct-2003.) $)
    pwexg $p |- ( A e. V -> ~P A e. _V ) $=
      vx cv cpw cvv wcel cA cpw cvv wcel vx cA cV vx cv cA wceq vx cv cpw cA
      cpw cvv vx cv cA pweq eleq1d vx cv vx vex pwex vtoclg $.

    $( Existence of a class of subsets.  (Contributed by NM, 15-Jul-2006.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    abssexg $p |- ( A e. V -> { x | ( x C_ A /\ ph ) } e. _V ) $=
      cA cV wcel cA cpw cvv wcel vx cv cA wss wph wa vx cab cvv wcel cA cV
      pwexg cA cpw cvv wcel vx cv cA wss vx cab cvv wcel vx cv cA wss wph wa vx
      cab cvv wcel cA cpw vx cv cA wss vx cab cvv vx cA df-pw eleq1i vx cv cA
      wss wph wa vx cab vx cv cA wss vx cab wss vx cv cA wss vx cab cvv wcel vx
      cv cA wss wph wa vx cab cvv wcel vx cv cA wss wph wa vx cv cA wss vx vx
      cv cA wss wph simpl ss2abi vx cv cA wss wph wa vx cab vx cv cA wss vx cab
      cvv ssexg mpan sylbi syl $.
  $}

  ${
    $d x y A $.
    $( A singleton is a set.  Theorem 7.13 of [Quine] p. 51, but proved using
       only Extensionality, Power Set, and Separation.  Unlike the proof of
       ~ zfpair , Replacement is not needed.  (Contributed by NM, 7-Aug-1994.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.)  See also ~ snex .
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    snexALT $p |- { A } e. _V $=
      cA cpw cvv wcel cA csn cvv wcel cA csn cA cpw wss cA cpw cvv wcel cA csn
      cvv wcel cA snsspw cA csn cA cpw cvv ssexg mpan cA cpw cvv wcel wn cA cvv
      wcel wn cA csn cvv wcel cA cvv wcel cA cpw cvv wcel cA cvv pwexg con3i cA
      cvv wcel wn cA csn c0 cvv cA cvv wcel wn cA csn c0 wceq cA snprc biimpi
      0ex syl6eqel syl pm2.61i $.
  $}

  $( The power set of the empty set (the ordinal 1) is a set.  See also
     ~ p0exALT .  (Contributed by NM, 23-Dec-1993.) $)
  p0ex $p |- { (/) } e. _V $=
    c0 cpw c0 csn cvv pw0 c0 0ex pwex eqeltrri $.

  $( The power set of the empty set (the ordinal 1) is a set.  Alternate proof
     which is longer and quite different from the proof of ~ p0ex if ~ snexALT
     is expanded.  (Contributed by NM, 23-Dec-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  p0exALT $p |- { (/) } e. _V $=
    c0 snexALT $.

  $( The power set of the power set of the empty set (the ordinal 2) is a set.
     (Contributed by NM, 5-Aug-1993.) $)
  pp0ex $p |- { (/) , { (/) } } e. _V $=
    c0 csn cpw c0 c0 csn cpr cvv pwpw0 c0 csn p0ex pwex eqeltrri $.

  $( The ordinal number 3 is a set, proved without the Axiom of Union
     ~ ax-un .  (Contributed by NM, 2-May-2009.) $)
  ord3ex $p |- { (/) , { (/) } , { (/) , { (/) } } } e. _V $=
    c0 c0 csn c0 c0 csn cpr ctp c0 c0 csn cpr c0 c0 csn cpr csn cun cvv c0 c0
    csn c0 c0 csn cpr df-tp c0 c0 csn cpr c0 c0 csn cpr csn cun c0 c0 csn cpr
    c0 csn csn c0 c0 csn cpr cpr cun c0 c0 csn cpr cpw c0 c0 csn cpr c0 csn csn
    c0 c0 csn cpr cpr cun cvv c0 c0 csn pwpr c0 c0 csn cpr pp0ex pwex eqeltrri
    c0 c0 csn cpr csn c0 csn csn c0 c0 csn cpr cpr wss c0 c0 csn cpr c0 c0 csn
    cpr csn cun c0 c0 csn cpr c0 csn csn c0 c0 csn cpr cpr cun wss c0 csn csn
    c0 c0 csn cpr snsspr2 c0 c0 csn cpr csn c0 csn csn c0 c0 csn cpr cpr c0 c0
    csn cpr unss2 ax-mp ssexi eqeltri $.

  ${
    $d w x y z $.
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
    dtru $p |- -. A. x x = y $=
      vx cv vy cv wceq wn vx wex vx cv vy cv wceq vx wal wn vw cv vz cv wceq wn
      vz wex vw wex vx cv vy cv wceq wn vx wex vx cv vw cv wcel vx cv vz cv
      wcel wn wa vz wex vw wex vw cv vz cv wceq wn vz wex vw wex vx cv vw cv
      wcel vx cv vz cv wcel wn wa vz wex vw wex vx cv vw cv wcel vw wex vx cv
      vz cv wcel wn vz wex vx vw el vx cv vz cv wcel wn vx wal vz wex vx cv vz
      cv wcel wn vz wex vz vx ax-nul vx cv vz cv wcel wn vx wal vx cv vz cv
      wcel wn vz vx cv vz cv wcel wn vx sp eximi ax-mp vx cv vw cv wcel vx cv
      vz cv wcel wn vw vz eeanv mpbir2an vx cv vw cv wcel vx cv vz cv wcel wn
      wa vw cv vz cv wceq wn vw vz vx cv vw cv wcel vw cv vz cv wceq vx cv vz
      cv wcel vw cv vz cv wceq vx cv vw cv wcel vx cv vz cv wcel vw vz vx ax-14
      com12 con3and 2eximi ax-mp vw cv vz cv wceq wn vx cv vy cv wceq wn vx wex
      vw vz vz cv vy cv wceq vw cv vz cv wceq wn vx cv vy cv wceq wn vx wex wi
      vz cv vy cv wceq vw cv vz cv wceq wn vw cv vy cv wceq wn vx cv vy cv wceq
      wn vx wex vz cv vy cv wceq vw cv vz cv wceq vw cv vy cv wceq vz vy vw
      equequ2 notbid vw cv vy cv wceq wn vx cv vy cv wceq wn vx vw vx cv vw cv
      wceq vx cv vy cv wceq vw cv vy cv wceq vx vw vy ax-8 con3d spimev syl6bi
      vz cv vy cv wceq wn vx cv vy cv wceq wn vx wex vw cv vz cv wceq wn vz cv
      vy cv wceq wn vx cv vy cv wceq wn vx vz vx cv vz cv wceq vx cv vy cv wceq
      vz cv vy cv wceq vx vz vy ax-8 con3d spimev a1d pm2.61i exlimivv ax-mp vx
      cv vy cv wceq vx exnal mpbi $.
  $}

  ${
    $d x y $.
    $( This theorem shows that axiom ~ ax-16 is redundant in the presence of
       theorem ~ dtru , which states simply that at least two things exist.
       This justifies the remark at
       ~ http://us.metamath.org/mpeuni/mmzfcnd.html#twoness (which links to
       this theorem).  (Contributed by NM, 7-Nov-2006.) $)
    ax16b $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      vx cv vy cv wceq vx wal wph wph vx wal wi vx vy dtru pm2.21i $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Existential uniqueness implies there is a value for which the wff
       argument is false.  (Contributed by NM, 24-Oct-2010.) $)
    eunex $p |- ( E! x ph -> E. x -. ph ) $=
      wph vx wex wph vx cv vy cv wceq wi vx wal vy wex wa wph vx wal wn wph vx
      weu wph wn vx wex wph vx cv vy cv wceq wi vx wal vy wex wph vx wal wn wph
      vx wex wph vx cv vy cv wceq wi vx wal wph vx wal wn vy wph vx cv vy cv
      wceq wi vx wal wph vx wal vx cv vy cv wceq vx wal vx vy dtru wph vx cv vy
      cv wceq vx alim mtoi exlimiv adantl wph vx vy wph vy nfv eu3 wph vx exnal
      3imtr4i $.
  $}

  ${
    $d w x y z $.
    $( A set variable is not free from itself.  The proof relies on ~ dtru ,
       that is, it is not true in a one-element domain.  (Contributed by Mario
       Carneiro, 8-Oct-2016.) $)
    nfnid $p |- -. F/_ x x $=
      vx vx cv wnfc vy cv vz cv wcel vy cv vw cv wcel wb vy wal vw wal vz wal
      vy cv vz cv wcel vy cv vw cv wcel wb vy wal vw wal vz wal vz cv vw cv
      wceq vz wal vz vw dtru vy cv vz cv wcel vy cv vw cv wcel wb vy wal vw wal
      vz cv vw cv wceq vz vy cv vz cv wcel vy cv vw cv wcel wb vy wal vz cv vw
      cv wceq vw vz vw vy ax-ext sps alimi mto vx vx cv wnfc vy cv vx cv wcel
      vx wnf vy wal vy cv vz cv wcel vy cv vw cv wcel wb vw wal vz wal vy wal
      vy cv vz cv wcel vy cv vw cv wcel wb vy wal vw wal vz wal vx vy vx cv
      df-nfc vy cv vx cv wcel vx wnf vy cv vz cv wcel vy cv vw cv wcel wb vw
      wal vz wal vy vy cv vx cv wcel vx wnf vy cv vx cv wcel vx vz wsb vy cv vx
      cv wcel vx vw wsb wb vw wal vz wal vy cv vz cv wcel vy cv vw cv wcel wb
      vw wal vz wal vy cv vx cv wcel vx vz vw sbnf2 vy cv vx cv wcel vx vz wsb
      vy cv vx cv wcel vx vw wsb wb vy cv vz cv wcel vy cv vw cv wcel wb vz vw
      vy cv vx cv wcel vx vz wsb vy cv vz cv wcel vy cv vx cv wcel vx vw wsb vy
      cv vw cv wcel vz vx vy elsb4 vw vx vy elsb4 bibi12i 2albii bitri albii vy
      cv vz cv wcel vy cv vw cv wcel wb vy vz vw alrot3 3bitri mtbir $.

    $d x z $.  $d y z $.
    $( The "distinctor" expression ` -. A. x x = y ` , stating that ` x ` and
       ` y ` are not the same variable, can be written in terms of ` F/ ` in
       the obvious way.  This theorem is not true in a one-element domain,
       because then ` F/_ x y ` and ` A. x x = y ` will both be true.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)
    nfcvb $p |- ( F/_ x y <-> -. A. x x = y ) $=
      vx vy cv wnfc vx cv vy cv wceq vx wal wn vx cv vy cv wceq vx wal vx vy cv
      wnfc vx cv vy cv wceq vx wal vx vy cv wnfc vy vy cv wnfc vy nfnid vx vy
      vy cv vy cv vx cv vy cv wceq vx wal vy cv eqidd drnfc1 mtbiri con2i vx vy
      nfcvf impbii $.
  $}

  ${
    $d A x $.
    $( A class is a subclass of the power class of its union.  Exercise 6(b) of
       [Enderton] p. 38.  (Contributed by NM, 14-Oct-1996.) $)
    pwuni $p |- A C_ ~P U. A $=
      vx cA cA cuni cpw vx cv cA wcel vx cv cA cuni wss vx cv cA cuni cpw wcel
      vx cv cA elssuni vx cv cA cuni vx vex elpw sylibr ssriv $.
  $}

  ${
    $d x y $.
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
    dtruALT $p |- -. A. x x = y $=
      vy cv vx cv wceq wn vx wex vx cv vy cv wceq vx wal wn vy cv c0 wceq vy cv
      vx cv wceq wn vx wex vy cv c0 wceq vy cv c0 csn wceq wn vy cv vx cv wceq
      wn vx wex vy cv 0inp0 vy cv vx cv wceq wn vy cv c0 csn wceq wn vx c0 csn
      p0ex vx cv c0 csn wceq vy cv vx cv wceq vy cv c0 csn wceq vx cv c0 csn vy
      cv eqeq2 notbid spcev syl vy cv vx cv wceq wn vy cv c0 wceq wn vx c0 0ex
      vx cv c0 wceq vy cv vx cv wceq vy cv c0 wceq vx cv c0 vy cv eqeq2 notbid
      spcev pm2.61i vy cv vx cv wceq wn vx wex vy cv vx cv wceq vx wal vx cv vy
      cv wceq vx wal vy cv vx cv wceq vx exnal vy cv vx cv wceq vx cv vy cv
      wceq vx vy cv vx cv eqcom albii xchbinx mpbi $.
  $}

  ${
    $d x y $.
    dtrucor.1 $e |- x = y $.
    $( Corollary of ~ dtru .  This example illustrates the danger of blindly
       trusting the standard Deduction Theorem without accounting for free
       variables: the theorem form of this deduction is not valid, as shown by
       ~ dtrucor2 .  (Contributed by NM, 27-Jun-2002.) $)
    dtrucor $p |- x =/= y $=
      vx cv vy cv wceq vx cv vy cv wne vx vx cv vy cv wceq vx wal vx cv vy cv
      wne vx vy dtru pm2.21i dtrucor.1 mpg $.
  $}

  ${
    dtrucor2.1 $e |- ( x = y -> x =/= y ) $.
    $( The theorem form of the deduction ~ dtrucor leads to a contradiction, as
       mentioned in the "Wrong!" example at
       ~ http://us.metamath.org/mpeuni/mmdeduction.html#bad .  (Contributed by
       NM, 20-Oct-2007.) $)
    dtrucor2 $p |- ( ph /\ -. ph ) $=
      vx cv vy cv wceq vx wex wph wph wn wa vx vy a9e vx cv vy cv wceq vx vx cv
      vy cv wceq vx cv vy cv wceq wn wi vx cv vy cv wceq wn vx cv vy cv wceq vx
      cv vy cv dtrucor2.1 necon2bi vx cv vy cv wceq pm2.01 ax-mp nex pm2.24ii
      $.
  $}


  ${
    $d x y $.
    $( Demonstration of a theorem (scheme) that requires (meta)variables ` x `
       and ` y ` to be distinct, but no others.  It bundles the theorem schemes
       ` E. x ( x = y -> x e. x ) ` and ` E. x ( x = y -> y e. x ) ` .  Compare
       ~ dvdemo2 .  ("Bundles" is a term introduced by Raph Levien.)
       (Contributed by NM, 1-Dec-2006.) $)
    dvdemo1 $p |- E. x ( x = y -> z e. x ) $=
      vx cv vy cv wceq wn vx wex vx cv vy cv wceq vz cv vx cv wcel wi vx wex vx
      cv vy cv wceq wn vx wex vx cv vy cv wceq vx wal wn vx vy dtru vx cv vy cv
      wceq vx exnal mpbir vx cv vy cv wceq wn vx cv vy cv wceq vz cv vx cv wcel
      wi vx vx cv vy cv wceq vz cv vx cv wcel pm2.21 eximi ax-mp $.
  $}

  ${
    $d x z $.
    $( Demonstration of a theorem (scheme) that requires (meta)variables ` x `
       and ` z ` to be distinct, but no others.  It bundles the theorem schemes
       ` E. x ( x = x -> z e. x ) ` and ` E. x ( x = y -> y e. x ) ` .  Compare
       ~ dvdemo1 .  (Contributed by NM, 1-Dec-2006.) $)
    dvdemo2 $p |- E. x ( x = y -> z e. x ) $=
      vz cv vx cv wcel vx wex vx cv vy cv wceq vz cv vx cv wcel wi vx wex vz vx
      el vz cv vx cv wcel vx cv vy cv wceq vz cv vx cv wcel wi vx vz cv vx cv
      wcel vx cv vy cv wceq ax-1 eximi ax-mp $.
  $}


