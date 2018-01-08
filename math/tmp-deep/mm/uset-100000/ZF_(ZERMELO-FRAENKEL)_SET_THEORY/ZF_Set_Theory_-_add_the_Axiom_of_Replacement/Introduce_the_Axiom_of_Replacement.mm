
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Introduce the Axiom of Replacement

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z w $.
    $( Axiom of Replacement.  An axiom scheme of Zermelo-Fraenkel set theory.
       Axiom 5 of [TakeutiZaring] p. 19.  It tells us that the image of any set
       under a function is also a set (see the variant ~ funimaex ).  Although
       ` ph ` may be any wff whatsoever, this axiom is useful (i.e. its
       antecedent is satisfied) when we are given some function and ` ph `
       encodes the predicate "the value of the function at ` w ` is ` z ` ."
       Thus, ` ph ` will ordinarily have free variables ` w ` and ` z ` - think
       of it informally as ` ph ( w , z ) ` .  We prefix ` ph ` with the
       quantifier ` A. y ` in order to "protect" the axiom from any ` ph `
       containing ` y ` , thus allowing us to eliminate any restrictions on
       ` ph ` .  This makes the axiom usable in a formalization that omits the
       logically redundant axiom ~ ax-17 .  Another common variant is derived
       as ~ axrep5 , where you can find some further remarks.  A slightly more
       compact version is shown as ~ axrep2 .  A quite different variant is
       ~ zfrep6 , which if used in place of ~ ax-rep would also require that
       the Separation Scheme ~ axsep be stated as a separate axiom.

       There is very a strong generalization of Replacement that doesn't demand
       function-like behavior of ` ph ` .  Two versions of this generalization
       are called the Collection Principle ~ cp and the Boundedness Axiom
       ~ bnd .

       Many developments of set theory distinguish the uses of Replacement from
       uses the weaker axioms of Separation ~ axsep , Null Set ~ axnul , and
       Pairing ~ axpr , all of which we derive from Replacement.  In order to
       make it easier to identify the uses of those redundant axioms, we
       restate them as axioms ~ ax-sep , ~ ax-nul , and ~ ax-pr below the
       theorems that prove them.  (Contributed by NM, 23-Dec-1993.) $)
    ax-rep $a |- ( A. w E. y A. z ( A. y ph -> z = y ) ->
                     E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) ) $.
  $}

  ${
    $d w y ph $.  $d w x y z $.
    $( The version of the Axiom of Replacement used in the Metamath Solitaire
       applet ~ http://us.metamath.org/mmsolitaire/mms.html .  Equivalence is
       shown via the path ~ ax-rep ` -> ` ~ axrep1 ` -> ` ~ axrep2 ` -> `
       ~ axrepnd ` -> ` ~ zfcndrep = ~ ax-rep .  (Contributed by NM,
       19-Nov-2005.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)
    axrep1 $p |- E. x ( E. y A. z ( ph -> z = y ) ->
                 A. z ( z e. x <-> E. x ( x e. y /\ ph ) ) ) $=
      wph vz cv vy cv wceq wi vz wal vy wex vz cv vx cv wcel vx cv vy cv wcel
      wph wa vx wex wb vz wal vx wph vz cv vy cv wceq wi vz wal vy wex vx wal
      vz cv vx cv wcel vx cv vw cv wcel wph wa vx wex wb vz wal vx wex wi wph
      vz cv vy cv wceq wi vz wal vy wex vx wal vz cv vx cv wcel vx cv vy cv
      wcel wph wa vx wex wb vz wal vx wex wi vw vy vw cv vy cv wceq vz cv vx cv
      wcel vx cv vw cv wcel wph wa vx wex wb vz wal vx wex vz cv vx cv wcel vx
      cv vy cv wcel wph wa vx wex wb vz wal vx wex wph vz cv vy cv wceq wi vz
      wal vy wex vx wal vw cv vy cv wceq vz cv vx cv wcel vx cv vw cv wcel wph
      wa vx wex wb vz wal vz cv vx cv wcel vx cv vy cv wcel wph wa vx wex wb vz
      wal vx vw cv vy cv wceq vz cv vx cv wcel vx cv vw cv wcel wph wa vx wex
      wb vz cv vx cv wcel vx cv vy cv wcel wph wa vx wex wb vz vw cv vy cv wceq
      vx cv vw cv wcel wph wa vx wex vx cv vy cv wcel wph wa vx wex vz cv vx cv
      wcel vw cv vy cv wceq vx cv vw cv wcel wph wa vx cv vy cv wcel wph wa vx
      vw cv vy cv wceq vx cv vw cv wcel vx cv vy cv wcel wph vw cv vy cv vx cv
      eleq2 anbi1d exbidv bibi2d albidv exbidv imbi2d wph vy wal vz cv vy cv
      wceq wi vz wal vy wex vx wal vz cv vy cv wcel vx cv vw cv wcel wph vy wal
      wa vx wex wb vz wal vy wex wph vz cv vy cv wceq wi vz wal vy wex vx wal
      vz cv vx cv wcel vx cv vw cv wcel wph wa vx wex wb vz wal vx wex wph vw
      vy vz vx ax-rep wph vy wal vz cv vy cv wceq wi vz wal vy wex wph vz cv vy
      cv wceq wi vz wal vy wex vx wph vy wal vz cv vy cv wceq wi vz wal wph vz
      cv vy cv wceq wi vz wal vy wph vy wal vz cv vy cv wceq wi wph vz cv vy cv
      wceq wi vz wph vy wal wph vz cv vy cv wceq wph vy wph vy nfv 19.3 imbi1i
      albii exbii albii vz cv vy cv wcel vx cv vw cv wcel wph vy wal wa vx wex
      wb vz wal vz cv vx cv wcel vx cv vw cv wcel wph wa vx wex wb vz wal vy vx
      vz cv vy cv wcel vx cv vw cv wcel wph vy wal wa vx wex wb vx vz vz cv vy
      cv wcel vx cv vw cv wcel wph vy wal wa vx wex vx vz cv vy cv wcel vx nfv
      vx cv vw cv wcel wph vy wal wa vx nfe1 nfbi nfal vz cv vx cv wcel vx cv
      vw cv wcel wph wa vx wex wb vz wal vy nfv vy cv vx cv wceq vz cv vy cv
      wcel vx cv vw cv wcel wph vy wal wa vx wex wb vz cv vx cv wcel vx cv vw
      cv wcel wph wa vx wex wb vz vy cv vx cv wceq vz cv vy cv wcel vz cv vx cv
      wcel vx cv vw cv wcel wph vy wal wa vx wex vx cv vw cv wcel wph wa vx wex
      vy vx vz elequ2 vx cv vw cv wcel wph vy wal wa vx wex vx cv vw cv wcel
      wph wa vx wex wb vy cv vx cv wceq vx cv vw cv wcel wph vy wal wa vx cv vw
      cv wcel wph wa vx wph vy wal wph vx cv vw cv wcel wph vy wph vy nfv 19.3
      anbi2i exbii a1i bibi12d albidv cbvex 3imtr3i chvarv 19.35ri $.
  $}

  ${
    $d w ph $.  $d w x y z $.
    $( Axiom of Replacement expressed with the fewest number of different
       variables and without any restrictions on ` ph ` .  (Contributed by NM,
       15-Aug-2003.) $)
    axrep2 $p |- E. x ( E. y A. z ( ph -> z = y ) ->
                        A. z ( z e. x <-> E. x ( x e. y /\ A. y ph ) ) ) $=
      wph vy wal vz cv vw cv wceq wi vz wal vw wex vz cv vx cv wcel vx cv vy cv
      wcel wph vy wal wa vx wex wb vz wal wi vx wex wph vz cv vy cv wceq wi vz
      wal vy wex vz cv vx cv wcel vx cv vy cv wcel wph vy wal wa vx wex wb vz
      wal wi vx wex wph vy wal vz cv vw cv wceq wi vz wal vw wex vz cv vx cv
      wcel vx cv vw cv wcel wph vy wal wa vx wex wb vz wal wi vx wex wph vy wal
      vz cv vw cv wceq wi vz wal vw wex vz cv vx cv wcel vx cv vy cv wcel wph
      vy wal wa vx wex wb vz wal wi vx wex vw vy wph vy wal vz cv vw cv wceq wi
      vz wal vw wex vz cv vx cv wcel vx cv vy cv wcel wph vy wal wa vx wex wb
      vz wal wi vw vx wph vy wal vz cv vw cv wceq wi vz wal vw wex vz cv vx cv
      wcel vx cv vy cv wcel wph vy wal wa vx wex wb vz wal vw wph vy wal vz cv
      vw cv wceq wi vz wal vw nfe1 vz cv vx cv wcel vx cv vy cv wcel wph vy wal
      wa vx wex wb vz wal vw nfv nfim nfex vw cv vy cv wceq wph vy wal vz cv vw
      cv wceq wi vz wal vw wex vz cv vx cv wcel vx cv vw cv wcel wph vy wal wa
      vx wex wb vz wal wi wph vy wal vz cv vw cv wceq wi vz wal vw wex vz cv vx
      cv wcel vx cv vy cv wcel wph vy wal wa vx wex wb vz wal wi vx vw cv vy cv
      wceq vz cv vx cv wcel vx cv vw cv wcel wph vy wal wa vx wex wb vz wal vz
      cv vx cv wcel vx cv vy cv wcel wph vy wal wa vx wex wb vz wal wph vy wal
      vz cv vw cv wceq wi vz wal vw wex vw cv vy cv wceq vz cv vx cv wcel vx cv
      vw cv wcel wph vy wal wa vx wex wb vz cv vx cv wcel vx cv vy cv wcel wph
      vy wal wa vx wex wb vz vw cv vy cv wceq vx cv vw cv wcel wph vy wal wa vx
      wex vx cv vy cv wcel wph vy wal wa vx wex vz cv vx cv wcel vw cv vy cv
      wceq vx cv vw cv wcel wph vy wal wa vx cv vy cv wcel wph vy wal wa vx vw
      cv vy cv wceq vx cv vw cv wcel vx cv vy cv wcel wph vy wal vw vy vx
      elequ2 anbi1d exbidv bibi2d albidv imbi2d exbidv wph vy wal vx vw vz
      axrep1 chvar wph vy wal vz cv vw cv wceq wi vz wal vw wex vz cv vx cv
      wcel vx cv vy cv wcel wph vy wal wa vx wex wb vz wal wi wph vz cv vy cv
      wceq wi vz wal vy wex vz cv vx cv wcel vx cv vy cv wcel wph vy wal wa vx
      wex wb vz wal wi vx wph vz cv vy cv wceq wi vz wal vy wex wph vy wal vz
      cv vw cv wceq wi vz wal vw wex vz cv vx cv wcel vx cv vy cv wcel wph vy
      wal wa vx wex wb vz wal wph vz cv vy cv wceq wi vz wal vy wex wph vy wal
      vz cv vy cv wceq wi vz wal vy wex wph vy wal vz cv vw cv wceq wi vz wal
      vw wex wph vz cv vy cv wceq wi vz wal wph vy wal vz cv vy cv wceq wi vz
      wal vy wph vz cv vy cv wceq wi wph vy wal vz cv vy cv wceq wi vz wph vy
      wal wph vz cv vy cv wceq wph vy sp imim1i alimi eximi wph vy wal vz cv vy
      cv wceq wi vz wal wph vy wal vz cv vw cv wceq wi vz wal vy vw wph vy wal
      vz cv vy cv wceq wi vz wal vw nfv wph vy wal vz cv vw cv wceq wi vy vz
      wph vy wal vz cv vw cv wceq vy wph vy nfa1 vz cv vw cv wceq vy nfv nfim
      nfal vy cv vw cv wceq wph vy wal vz cv vy cv wceq wi wph vy wal vz cv vw
      cv wceq wi vz vy cv vw cv wceq vz cv vy cv wceq vz cv vw cv wceq wph vy
      wal vy vw vz equequ2 imbi2d albidv cbvex sylib imim1i eximi ax-mp $.
  $}

  ${
    $d w x y z $.
    $( Axiom of Replacement slightly strengthened from ~ axrep2 ; ` w ` may
       occur free in ` ph ` .  (Contributed by NM, 2-Jan-1997.) $)
    axrep3 $p |- E. x ( E. y A. z ( ph -> z = y ) ->
                 A. z ( z e. x <-> E. x ( x e. w /\ A. y ph ) ) ) $=
      wph vz cv vy cv wceq wi vz wal vy wex vz cv vx cv wcel vx cv vy cv wcel
      wph vy wal wa vx wex wb vz wal wi vx wex wph vz cv vy cv wceq wi vz wal
      vy wex vz cv vx cv wcel vx cv vw cv wcel wph vy wal wa vx wex wb vz wal
      wi vx wex vy vw wph vz cv vy cv wceq wi vz wal vy wex vz cv vx cv wcel vx
      cv vw cv wcel wph vy wal wa vx wex wb vz wal wi vy vx wph vz cv vy cv
      wceq wi vz wal vy wex vz cv vx cv wcel vx cv vw cv wcel wph vy wal wa vx
      wex wb vz wal vy wph vz cv vy cv wceq wi vz wal vy nfe1 vz cv vx cv wcel
      vx cv vw cv wcel wph vy wal wa vx wex wb vy vz vz cv vx cv wcel vx cv vw
      cv wcel wph vy wal wa vx wex vy vz cv vx cv wcel vy nfv vx cv vw cv wcel
      wph vy wal wa vy vx vx cv vw cv wcel wph vy wal vy vx cv vw cv wcel vy
      nfv wph vy nfa1 nfan nfex nfbi nfal nfim nfex vy cv vw cv wceq wph vz cv
      vy cv wceq wi vz wal vy wex vz cv vx cv wcel vx cv vy cv wcel wph vy wal
      wa vx wex wb vz wal wi wph vz cv vy cv wceq wi vz wal vy wex vz cv vx cv
      wcel vx cv vw cv wcel wph vy wal wa vx wex wb vz wal wi vx vy cv vw cv
      wceq vz cv vx cv wcel vx cv vy cv wcel wph vy wal wa vx wex wb vz wal vz
      cv vx cv wcel vx cv vw cv wcel wph vy wal wa vx wex wb vz wal wph vz cv
      vy cv wceq wi vz wal vy wex vy cv vw cv wceq vz cv vx cv wcel vx cv vy cv
      wcel wph vy wal wa vx wex wb vz cv vx cv wcel vx cv vw cv wcel wph vy wal
      wa vx wex wb vz vy cv vw cv wceq vx cv vy cv wcel wph vy wal wa vx wex vx
      cv vw cv wcel wph vy wal wa vx wex vz cv vx cv wcel vy cv vw cv wceq vx
      cv vy cv wcel wph vy wal wa vx cv vw cv wcel wph vy wal wa vx vy cv vw cv
      wceq vx cv vy cv wcel vx cv vw cv wcel wph vy wal vy vw vx elequ2 anbi1d
      exbidv bibi2d albidv imbi2d exbidv wph vx vy vz axrep2 chvar $.
  $}

  ${
    $d x y z w $.
    axrep4.1 $e |- F/ z ph $.
    $( A more traditional version of the Axiom of Replacement.  (Contributed by
       NM, 14-Aug-1994.) $)
    axrep4 $p |- ( A. x E. z A. y ( ph -> y = z ) ->
                E. z A. y ( y e. z <-> E. x ( x e. w /\ ph ) ) ) $=
      wph vy cv vz cv wceq wi vy wal vz wex vx wal vy cv vx cv wcel vx cv vw cv
      wcel wph vz wal wa vx wex wb vy wal vx wex vy cv vz cv wcel vx cv vw cv
      wcel wph wa vx wex wb vy wal vz wex wph vy cv vz cv wceq wi vy wal vz wex
      vy cv vx cv wcel vx cv vw cv wcel wph vz wal wa vx wex wb vy wal vx wph
      vx vz vy vw axrep3 19.35i vy cv vx cv wcel vx cv vw cv wcel wph vz wal wa
      vx wex wb vy wal vy cv vz cv wcel vx cv vw cv wcel wph wa vx wex wb vy
      wal vx vz vy cv vx cv wcel vx cv vw cv wcel wph vz wal wa vx wex wb vz vy
      vy cv vx cv wcel vx cv vw cv wcel wph vz wal wa vx wex vz vy cv vx cv
      wcel vz nfv vx cv vw cv wcel wph vz wal wa vz vx vx cv vw cv wcel wph vz
      wal vz vx cv vw cv wcel vz nfv wph vz nfa1 nfan nfex nfbi nfal vy cv vz
      cv wcel vx cv vw cv wcel wph wa vx wex wb vx vy vy cv vz cv wcel vx cv vw
      cv wcel wph wa vx wex vx vy cv vz cv wcel vx nfv vx cv vw cv wcel wph wa
      vx nfe1 nfbi nfal vx cv vz cv wceq vy cv vx cv wcel vx cv vw cv wcel wph
      vz wal wa vx wex wb vy cv vz cv wcel vx cv vw cv wcel wph wa vx wex wb vy
      vx cv vz cv wceq vy cv vx cv wcel vy cv vz cv wcel vx cv vw cv wcel wph
      vz wal wa vx wex vx cv vw cv wcel wph wa vx wex vx vz vy elequ2 vx cv vw
      cv wcel wph vz wal wa vx wex vx cv vw cv wcel wph wa vx wex wb vx cv vz
      cv wceq vx cv vw cv wcel wph vz wal wa vx cv vw cv wcel wph wa vx wph vz
      wal wph vx cv vw cv wcel wph vz axrep4.1 19.3 anbi2i exbii a1i bibi12d
      albidv cbvex sylib $.
  $}

  ${
    $d x y z w $.
    axrep5.1 $e |- F/ z ph $.
    $( Axiom of Replacement (similar to Axiom Rep of [BellMachover] p. 463).
       The antecedent tells us ` ph ` is analogous to a "function" from ` x `
       to ` y ` (although it is not really a function since it is a wff and not
       a class).  In the consequent we postulate the existence of a set ` z `
       that corresponds to the "image" of ` ph ` restricted to some other set
       ` w ` .  The hypothesis says ` z ` must not be free in ` ph ` .
       (Contributed by NM, 26-Nov-1995.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
    axrep5 $p |- ( A. x ( x e. w -> E. z A. y ( ph -> y = z ) ) ->
                E. z A. y ( y e. z <-> E. x ( x e. w /\ ph ) ) ) $=
      vx cv vw cv wcel wph vy cv vz cv wceq wi vy wal vz wex wi vx wal vy cv vz
      cv wcel vx cv vw cv wcel vx cv vw cv wcel wph wa wa vx wex wb vy wal vz
      wex vy cv vz cv wcel vx cv vw cv wcel wph wa vx wex wb vy wal vz wex vx
      cv vw cv wcel wph vy cv vz cv wceq wi vy wal vz wex wi vx wal vx cv vw cv
      wcel wph wa vy cv vz cv wceq wi vy wal vz wex vx wal vy cv vz cv wcel vx
      cv vw cv wcel vx cv vw cv wcel wph wa wa vx wex wb vy wal vz wex vx cv vw
      cv wcel wph vy cv vz cv wceq wi vy wal vz wex wi vx cv vw cv wcel wph wa
      vy cv vz cv wceq wi vy wal vz wex vx vx cv vw cv wcel wph vy cv vz cv
      wceq wi vy wal vz wex wi vx cv vw cv wcel wph vy cv vz cv wceq wi vy wal
      wi vz wex vx cv vw cv wcel wph wa vy cv vz cv wceq wi vy wal vz wex vx cv
      vw cv wcel wph vy cv vz cv wceq wi vy wal vz 19.37v vx cv vw cv wcel wph
      vy cv vz cv wceq wi vy wal wi vx cv vw cv wcel wph wa vy cv vz cv wceq wi
      vy wal vz vx cv vw cv wcel wph wa vy cv vz cv wceq wi vy wal vx cv vw cv
      wcel wph vy cv vz cv wceq wi wi vy wal vx cv vw cv wcel wph vy cv vz cv
      wceq wi vy wal wi vx cv vw cv wcel wph wa vy cv vz cv wceq wi vx cv vw cv
      wcel wph vy cv vz cv wceq wi wi vy vx cv vw cv wcel wph vy cv vz cv wceq
      impexp albii vx cv vw cv wcel wph vy cv vz cv wceq wi vy 19.21v bitr2i
      exbii bitr3i albii vx cv vw cv wcel wph wa vx vy vz vw vx cv vw cv wcel
      wph vz vx cv vw cv wcel vz nfv axrep5.1 nfan axrep4 sylbi vy cv vz cv
      wcel vx cv vw cv wcel vx cv vw cv wcel wph wa wa vx wex wb vy wal vy cv
      vz cv wcel vx cv vw cv wcel wph wa vx wex wb vy wal vz vy cv vz cv wcel
      vx cv vw cv wcel vx cv vw cv wcel wph wa wa vx wex wb vy cv vz cv wcel vx
      cv vw cv wcel wph wa vx wex wb vy vx cv vw cv wcel vx cv vw cv wcel wph
      wa wa vx wex vx cv vw cv wcel wph wa vx wex vy cv vz cv wcel vx cv vw cv
      wcel vx cv vw cv wcel wph wa wa vx cv vw cv wcel wph wa vx vx cv vw cv
      wcel wph anabs5 exbii bibi2i albii exbii sylib $.
  $}

  ${
    $d y z A v $.  $d z ph v $.  $d A w v $.  $d x y z v $.  $d x w v $.
    zfrepclf.1 $e |- F/_ x A $.
    zfrepclf.2 $e |- A e. _V $.
    zfrepclf.3 $e |- ( x e. A -> E. z A. y ( ph -> y = z ) ) $.
    $( An inference rule based on the Axiom of Replacement.  Typically, ` ph `
       defines a function from ` x ` to ` y ` .  (Contributed by NM,
       26-Nov-1995.) $)
    zfrepclf $p |- E. z A. y ( y e. z <-> E. x ( x e. A /\ ph ) ) $=
      vy cv vz cv wcel vx cv cA wcel wph wa vx wex wb vy wal vz wex vv cA
      zfrepclf.2 vv cv cA wceq vy cv vz cv wcel vx cv vv cv wcel wph wa vx wex
      wb vy wal vz wex vy cv vz cv wcel vx cv cA wcel wph wa vx wex wb vy wal
      vz wex vv cv cA wceq vx cv vv cv wcel wph vy cv vz cv wceq wi vy wal vz
      wex wi vx wal vy cv vz cv wcel vx cv vv cv wcel wph wa vx wex wb vy wal
      vz wex vv cv cA wceq vx cv vv cv wcel wph vy cv vz cv wceq wi vy wal vz
      wex wi vx vx vv cv cA zfrepclf.1 nfeq2 vv cv cA wceq vx cv vv cv wcel vx
      cv cA wcel wph vy cv vz cv wceq wi vy wal vz wex vv cv cA vx cv eleq2
      zfrepclf.3 syl6bi alrimi wph vx vy vz vv wph vz nfv axrep5 syl vv cv cA
      wceq vy cv vz cv wcel vx cv vv cv wcel wph wa vx wex wb vy wal vy cv vz
      cv wcel vx cv cA wcel wph wa vx wex wb vy wal vz vv cv cA wceq vy cv vz
      cv wcel vx cv vv cv wcel wph wa vx wex wb vy cv vz cv wcel vx cv cA wcel
      wph wa vx wex wb vy vv cv cA wceq vx cv vv cv wcel wph wa vx wex vx cv cA
      wcel wph wa vx wex vy cv vz cv wcel vv cv cA wceq vx cv vv cv wcel wph wa
      vx cv cA wcel wph wa vx vx vv cv cA zfrepclf.1 nfeq2 vv cv cA wceq vx cv
      vv cv wcel vx cv cA wcel wph vv cv cA vx cv eleq2 anbi1d exbid bibi2d
      albidv exbidv mpbid vtocle $.
  $}

  ${
    $d x y z A $.  $d z ph $.
    zfrep3cl.1 $e |- A e. _V $.
    zfrep3cl.2 $e |- ( x e. A -> E. z A. y ( ph -> y = z ) ) $.
    $( An inference rule based on the Axiom of Replacement.  Typically, ` ph `
       defines a function from ` x ` to ` y ` .  (Contributed by NM,
       26-Nov-1995.) $)
    zfrep3cl $p |- E. z A. y ( y e. z <-> E. x ( x e. A /\ ph ) ) $=
      wph vx vy vz cA vx cA nfcv zfrep3cl.1 zfrep3cl.2 zfrepclf $.
  $}

  ${
    $d ph y z $.  $d ps z $.  $d x y z $.
    zfrep4.1 $e |- { x | ph } e. _V $.
    zfrep4.2 $e |- ( ph -> E. z A. y ( ps -> y = z ) ) $.
    $( A version of Replacement using class abstractions.  (Contributed by NM,
       26-Nov-1995.) $)
    zfrep4 $p |- { y | E. x ( ph /\ ps ) } e. _V $=
      vx cv wph vx cab wcel wps wa vx wex vy cab wph wps wa vx wex vy cab cvv
      vx cv wph vx cab wcel wps wa vx wex wph wps wa vx wex vy vx cv wph vx cab
      wcel wps wa wph wps wa vx vx cv wph vx cab wcel wph wps wph vx abid
      anbi1i exbii abbii vz vx cv wph vx cab wcel wps wa vx wex vy cab vz cv vx
      cv wph vx cab wcel wps wa vx wex vy cab wceq vz wex vy cv vz cv wcel vx
      cv wph vx cab wcel wps wa vx wex wb vy wal vz wex wps vx vy vz wph vx cab
      wph vx nfab1 zfrep4.1 vx cv wph vx cab wcel wph wps vy cv vz cv wceq wi
      vy wal vz wex wph vx abid zfrep4.2 sylbi zfrepclf vz cv vx cv wph vx cab
      wcel wps wa vx wex vy cab wceq vy cv vz cv wcel vx cv wph vx cab wcel wps
      wa vx wex wb vy wal vz vx cv wph vx cab wcel wps wa vx wex vy vz cv abeq2
      exbii mpbir issetri eqeltrri $.
  $}



