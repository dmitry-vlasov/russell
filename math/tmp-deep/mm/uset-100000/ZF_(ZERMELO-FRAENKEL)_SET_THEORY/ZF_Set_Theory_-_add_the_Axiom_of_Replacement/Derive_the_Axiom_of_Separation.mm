
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Introduce_the_Axiom_of_Replacement.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    Derive the Axiom of Separation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z w $.  $d y z ph w $.
    $( Separation Scheme, which is an axiom scheme of Zermelo's original
       theory.  Scheme Sep of [BellMachover] p. 463.  As we show here, it is
       redundant if we assume Replacement in the form of ~ ax-rep .  Some
       textbooks present Separation as a separate axiom scheme in order to show
       that much of set theory can be derived without the stronger
       Replacement.  The Separation Scheme is a weak form of Frege's Axiom of
       Comprehension, conditioning it (with ` x e. z ` ) so that it asserts the
       existence of a collection only if it is smaller than some other
       collection ` z ` that already exists.  This prevents Russell's paradox
       ~ ru .  In some texts, this scheme is called "Aussonderung" or the
       Subset Axiom.

       The variable ` x ` can appear free in the wff ` ph ` , which in
       textbooks is often written ` ph ( x ) ` .  To specify this in the
       Metamath language, we _omit_ the distinct variable requirement ($d) that
       ` x ` not appear in ` ph ` .

       For a version using a class variable, see ~ zfauscl , which requires the
       Axiom of Extensionality as well as Separation for its derivation.

       If we omit the requirement that ` y ` not occur in ` ph ` , we can
       derive a contradiction, as ~ notzfaus shows (contradicting ~ zfauscl ).
       However, as ~ axsep2 shows, we can eliminate the restriction that ` z `
       not occur in ` ph ` .

       Note: the distinct variable restriction that ` z ` not occur in ` ph `
       is actually redundant in this particular proof, but we keep it since its
       purpose is to demonstrate the derivation of the exact ~ ax-sep from
       ~ ax-rep .

       This theorem should not be referenced by any proof.  Instead, use
       ~ ax-sep below so that the uses of the Axiom of Separation can be more
       easily identified.  (Contributed by NM, 11-Sep-2006.)
       (New usage is discouraged.) $)
    axsep $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $=
      vx cv vy cv wcel vw cv vz cv wcel vw cv vx cv wceq wph wa wa vw wex wb vx
      wal vy wex vx cv vy cv wcel vx cv vz cv wcel wph wa wb vx wal vy wex vw
      cv vz cv wcel vw cv vx cv wceq wph wa vx cv vy cv wceq wi vx wal vy wex
      wi vx cv vy cv wcel vw cv vz cv wcel vw cv vx cv wceq wph wa wa vw wex wb
      vx wal vy wex vw vw cv vx cv wceq wph wa vw vx vy vz vw cv vx cv wceq wph
      wa vy nfv axrep5 vw cv vz cv wcel vw cv vx cv wceq wph wa vx cv vy cv
      wceq wi vx wal vy vw vy cv vw cv wceq vw cv vx cv wceq wph wa vx cv vy cv
      wceq wi vx wal vw cv vz cv wcel vy cv vw cv wceq vw cv vx cv wceq wph wa
      vx cv vy cv wceq wi vx vy cv vw cv wceq vw cv vx cv wceq vx cv vy cv wceq
      wph vy cv vw cv wceq vw cv vx cv wceq vy cv vx cv wceq vx cv vy cv wceq
      vy vw vx equtr vy vx equcomi syl6 adantrd alrimiv a1d spimev mpg vx cv vy
      cv wcel vw cv vz cv wcel vw cv vx cv wceq wph wa wa vw wex wb vx wal vx
      cv vy cv wcel vx cv vz cv wcel wph wa wb vx wal vy vx cv vy cv wcel vw cv
      vz cv wcel vw cv vx cv wceq wph wa wa vw wex wb vx cv vy cv wcel vx cv vz
      cv wcel wph wa wb vx vw cv vz cv wcel vw cv vx cv wceq wph wa wa vw wex
      vx cv vz cv wcel wph wa vx cv vy cv wcel vw cv vz cv wcel vw cv vx cv
      wceq wph wa wa vw wex vw cv vx cv wceq vw cv vz cv wcel wph wa wa vw wex
      vx cv vz cv wcel wph wa vw cv vx cv wceq vw cv vz cv wcel wph wa wa vw cv
      vz cv wcel vw cv vx cv wceq wph wa wa vw vw cv vx cv wceq vw cv vz cv
      wcel wph an12 exbii vw cv vz cv wcel wph wa vx cv vz cv wcel wph wa vw vx
      vx cv vz cv wcel wph wa vw nfv vw cv vx cv wceq vw cv vz cv wcel vx cv vz
      cv wcel wph vw vx vz elequ1 anbi1d equsex bitr3i bibi2i albii exbii mpbi
      $.

    $( The Axiom of Separation of ZF set theory.  See ~ axsep for more
       information.  It was derived as ~ axsep above and is therefore
       redundant, but we state it as a separate axiom here so that its uses can
       be identified more easily.  (Contributed by NM, 11-Sep-2006.) $)
    ax-sep $a |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $.
  $}

  ${
    $d x y z w $.  $d y ph w $.  $d z w $.
    $( A less restrictive version of the Separation Scheme ~ axsep , where
       variables ` x ` and ` z ` can both appear free in the wff ` ph ` , which
       can therefore be thought of as ` ph ( x , z ) ` .  This version was
       derived from the more restrictive ~ ax-sep with no additional set theory
       axioms.  (Contributed by NM, 10-Dec-2006.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.) $)
    axsep2 $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $=
      vx cv vy cv wcel vx cv vw cv wcel vx cv vz cv wcel wph wa wa wb vx wal vy
      wex vx cv vy cv wcel vx cv vz cv wcel wph wa wb vx wal vy wex vw vz vw cv
      vz cv wceq vx cv vy cv wcel vx cv vw cv wcel vx cv vz cv wcel wph wa wa
      wb vx wal vx cv vy cv wcel vx cv vz cv wcel wph wa wb vx wal vy vw cv vz
      cv wceq vx cv vy cv wcel vx cv vw cv wcel vx cv vz cv wcel wph wa wa wb
      vx cv vy cv wcel vx cv vz cv wcel wph wa wb vx vw cv vz cv wceq vx cv vw
      cv wcel vx cv vz cv wcel wph wa wa vx cv vz cv wcel wph wa vx cv vy cv
      wcel vw cv vz cv wceq vx cv vw cv wcel vx cv vz cv wcel wph wa wa vx cv
      vz cv wcel vx cv vz cv wcel wph wa wa vx cv vz cv wcel wph wa vw cv vz cv
      wceq vx cv vw cv wcel vx cv vz cv wcel vx cv vz cv wcel wph wa vw cv vz
      cv vx cv eleq2 anbi1d vx cv vz cv wcel wph anabs5 syl6bb bibi2d albidv
      exbidv vx cv vz cv wcel wph wa vx vy vw ax-sep chvarv $.
  $}

  ${
    $d x y A z $.  $d y ph z $.
    zfauscl.1 $e |- A e. _V $.
    $( Separation Scheme (Aussonderung) using a class variable.  To derive this
       from ~ ax-sep , we invoke the Axiom of Extensionality (indirectly via
       ~ vtocl ), which is needed for the justification of class variable
       notation.

       If we omit the requirement that ` y ` not occur in ` ph ` , we can
       derive a contradiction, as ~ notzfaus shows.  (Contributed by NM,
       5-Aug-1993.) $)
    zfauscl $p |- E. y A. x ( x e. y <-> ( x e. A /\ ph ) ) $=
      vx cv vy cv wcel vx cv vz cv wcel wph wa wb vx wal vy wex vx cv vy cv
      wcel vx cv cA wcel wph wa wb vx wal vy wex vz cA zfauscl.1 vz cv cA wceq
      vx cv vy cv wcel vx cv vz cv wcel wph wa wb vx wal vx cv vy cv wcel vx cv
      cA wcel wph wa wb vx wal vy vz cv cA wceq vx cv vy cv wcel vx cv vz cv
      wcel wph wa wb vx cv vy cv wcel vx cv cA wcel wph wa wb vx vz cv cA wceq
      vx cv vz cv wcel wph wa vx cv cA wcel wph wa vx cv vy cv wcel vz cv cA
      wceq vx cv vz cv wcel vx cv cA wcel wph vz cv cA vx cv eleq2 anbi1d
      bibi2d albidv exbidv wph vx vy vz ax-sep vtocl $.
  $}

  ${
    $d x ph z $.  $d x y z $.
    bm1.3ii.1 $e |- E. x A. y ( ph -> y e. x ) $.
    $( Convert implication to equivalence using the Separation Scheme
       (Aussonderung) ~ ax-sep .  Similar to Theorem 1.3ii of [BellMachover]
       p. 463.  (Contributed by NM, 5-Aug-1993.) $)
    bm1.3ii $p |- E. x A. y ( y e. x <-> ph ) $=
      wph vy cv vz cv wcel wi vy wal vy cv vx cv wcel vy cv vz cv wcel wph wa
      wb vy wal vx wex wa vz wex vy cv vx cv wcel wph wb vy wal vx wex wph vy
      cv vz cv wcel wi vy wal vy cv vx cv wcel vy cv vz cv wcel wph wa wb vy
      wal vx wex vz wph vy cv vz cv wcel wi vy wal vz wex vy cv vx cv wcel vy
      cv vz cv wcel wph wa wb vy wal vx wex wph vy cv vx cv wcel wi vy wal vx
      wex wph vy cv vz cv wcel wi vy wal vz wex bm1.3ii.1 wph vy cv vx cv wcel
      wi vy wal wph vy cv vz cv wcel wi vy wal vx vz vx cv vz cv wceq wph vy cv
      vx cv wcel wi wph vy cv vz cv wcel wi vy vx cv vz cv wceq vy cv vx cv
      wcel vy cv vz cv wcel wph vx vz vy elequ2 imbi2d albidv cbvexv mpbi wph
      vy vx vz ax-sep pm3.2i exan wph vy cv vz cv wcel wi vy wal vy cv vx cv
      wcel vy cv vz cv wcel wph wa wb vy wal vx wex wa vy cv vx cv wcel wph wb
      vy wal vx wex vz wph vy cv vz cv wcel wi vy wal vy cv vx cv wcel vy cv vz
      cv wcel wph wa wb vy wal vx wex wa wph vy cv vz cv wcel wi vy wal vy cv
      vx cv wcel vy cv vz cv wcel wph wa wb vy wal wa vx wex vy cv vx cv wcel
      wph wb vy wal vx wex wph vy cv vz cv wcel wi vy wal vy cv vx cv wcel vy
      cv vz cv wcel wph wa wb vy wal vx 19.42v wph vy cv vz cv wcel wi vy wal
      vy cv vx cv wcel vy cv vz cv wcel wph wa wb vy wal wa vy cv vx cv wcel
      wph wb vy wal vx wph vy cv vz cv wcel wi vy cv vx cv wcel vy cv vz cv
      wcel wph wa wb vy cv vx cv wcel wph wb vy wph vy cv vz cv wcel vy cv vx
      cv wcel bimsc1 alanimi eximi sylbir exlimiv ax-mp $.
  $}

  ${
    $d x y z $.
    $( Derive a weakened version of ~ ax9 ( i.e. ~ ax9v ), where ` x ` and
       ` y ` must be distinct, from Separation ~ ax-sep and Extensionality
       ~ ax-ext .  See ~ ax9 for the derivation of ~ ax9 from ~ ax9v .
       (Contributed by NM, 12-Nov-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax9vsep $p |- -. A. x -. x = y $=
      vx cv vy cv wceq vx wex vx cv vy cv wceq wn vx wal wn vz cv vx cv wcel vz
      cv vy cv wcel vz cv vz cv wceq vz cv vz cv wceq wi wa wb vz wal vx wex vx
      cv vy cv wceq vx wex vz cv vz cv wceq vz cv vz cv wceq wi vz vx vy ax-sep
      vz cv vx cv wcel vz cv vy cv wcel vz cv vz cv wceq vz cv vz cv wceq wi wa
      wb vz wal vx cv vy cv wceq vx vz cv vx cv wcel vz cv vy cv wcel vz cv vz
      cv wceq vz cv vz cv wceq wi wa wb vz wal vz cv vx cv wcel vz cv vy cv
      wcel wb vz wal vx cv vy cv wceq vz cv vx cv wcel vz cv vy cv wcel vz cv
      vz cv wceq vz cv vz cv wceq wi wa wb vz cv vx cv wcel vz cv vy cv wcel wb
      vz vz cv vx cv wcel vz cv vy cv wcel wb vz cv vx cv wcel vz cv vy cv wcel
      vz cv vz cv wceq vz cv vz cv wceq wi wa wb vz cv vy cv wcel vz cv vy cv
      wcel vz cv vz cv wceq vz cv vz cv wceq wi wa vz cv vx cv wcel vz cv vz cv
      wceq vz cv vz cv wceq wi vz cv vy cv wcel vz cv vz cv wceq id biantru
      bibi2i biimpri alimi vx vy vz ax-ext syl eximi ax-mp vx cv vy cv wceq vx
      df-ex mpbi $.
  $}


