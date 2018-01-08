
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes).mm $]

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
               Existential uniqueness

#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare new symbols needed for uniqueness notation. $)
  $c E! $.  $( Backwards E exclamation point. $)
  $c E* $.  $( Backwards E superscript *. $)

  $( Extend wff definition to include existential uniqueness ("there exists a
     unique ` x ` such that ` ph ` "). $)
  weu $a wff E! x ph $.

  $( Extend wff definition to include uniqueness ("there exists at most one
     ` x ` such that ` ph ` "). $)
  wmo $a wff E* x ph $.

  ${
    $d w x y $.  $d x z $.  $d y ph $.  $d w z ph $.
    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  See
       ~ eujustALT for a proof that provides an example of how it can be
       achieved through the use of ~ dvelim .  (Contributed by NM,
       11-Mar-2010.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    eujust $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      wph vx cv vy cv wceq wb vx wal vy wex wph vx cv vw cv wceq wb vx wal vw
      wex wph vx cv vz cv wceq wb vx wal vz wex wph vx cv vy cv wceq wb vx wal
      wph vx cv vw cv wceq wb vx wal vy vw vy cv vw cv wceq wph vx cv vy cv
      wceq wb wph vx cv vw cv wceq wb vx vy cv vw cv wceq vx cv vy cv wceq vx
      cv vw cv wceq wph vy vw vx equequ2 bibi2d albidv cbvexv wph vx cv vw cv
      wceq wb vx wal wph vx cv vz cv wceq wb vx wal vw vz vw cv vz cv wceq wph
      vx cv vw cv wceq wb wph vx cv vz cv wceq wb vx vw cv vz cv wceq vx cv vw
      cv wceq vx cv vz cv wceq wph vw vz vx equequ2 bibi2d albidv cbvexv bitri
      $.

    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  While this
       isn't strictly necessary for soundness, the proof provides an example of
       how it can be achieved through the use of ~ dvelim .  (Contributed by
       NM, 11-Mar-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eujustALT $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      vy vz weq vy wal wph vx vy weq wb vx wal vy wex wph vx vz weq wb vx wal
      vz wex wb wph vx vy weq wb vx wal wph vx vz weq wb vx wal vy vz vy vz weq
      wph vx vy weq wb vx wal wph vx vz weq wb vx wal wb vy vy vz weq wph vx vy
      weq wb wph vx vz weq wb vx vy vz weq vx vy weq vx vz weq wph vy vz vx
      equequ2 bibi2d albidv sps drex1 vy vz weq vy wal wn wph vx vy weq wb vx
      wal wn vy wal wn wph vx vz weq wb vx wal wn vz wal wn wph vx vy weq wb vx
      wal vy wex wph vx vz weq wb vx wal vz wex vy vz weq vy wal wn wph vx vy
      weq wb vx wal wn vy wal wph vx vz weq wb vx wal wn vz wal vy vz weq vy
      wal wn vy vz weq vy wal wn vz wal vy wal wph vx vy weq wb vx wal wn vy
      wal wph vx vz weq wb vx wal wn vz wal wb vy vz weq vy wal wn vy vz weq vy
      wal wn vz wal vy vy vz vy hbnae vy vz vz hbnae alrimih vy vz weq vy wal
      wn wph vx vy weq wb vx wal wn wph vx vz weq wb vx wal wn vy vz wph vx vy
      weq wb vx wal wn wph vx vy weq wb vx wal wn vz wal wi vz vy wph vx vw weq
      wb vx wal wn wph vx vy weq wb vx wal wn vz vy vw wph vx vw weq wb vx wal
      wn vz ax-17 vw vy weq wph vx vw weq wb vx wal wph vx vy weq wb vx wal vw
      vy weq wph vx vw weq wb wph vx vy weq wb vx vw vy weq vx vw weq vx vy weq
      wph vw vy vx equequ2 bibi2d albidv notbid dvelim naecoms wph vx vw weq wb
      vx wal wn wph vx vz weq wb vx wal wn vy vz vw wph vx vw weq wb vx wal wn
      vy ax-17 vw vz weq wph vx vw weq wb vx wal wph vx vz weq wb vx wal vw vz
      weq wph vx vw weq wb wph vx vz weq wb vx vw vz weq vx vw weq vx vz weq
      wph vw vz vx equequ2 bibi2d albidv notbid dvelim vy vz weq wph vx vy weq
      wb vx wal wn wph vx vz weq wb vx wal wn wb wi vy vz weq vy wal wn vy vz
      weq wph vx vy weq wb vx wal wph vx vz weq wb vx wal vy vz weq wph vx vy
      weq wb wph vx vz weq wb vx vy vz weq vx vy weq vx vz weq wph vy vz vx
      equequ2 bibi2d albidv notbid a1i cbv2h syl notbid wph vx vy weq wb vx wal
      vy df-ex wph vx vz weq wb vx wal vz df-ex 3bitr4g pm2.61i $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Define existential uniqueness, i.e.  "there exists exactly one ` x `
       such that ` ph ` ."  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3 , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean "exactly one ` x ` and one
       ` y ` " (see ~ 2eu4 ).  (Contributed by NM, 12-Aug-1993.) $)
    df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
  $}

  $( Define "there exists at most one ` x ` such that ` ph ` ."  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For other possible definitions see
     ~ mo2 and ~ mo4 .  (Contributed by NM, 8-Mar-1995.) $)
  df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.

  ${
    $d x y z $.  $d ph z $.
    euf.1 $e |- F/ y ph $.
    $( A version of the existential uniqueness definition with a hypothesis
       instead of a distinct variable condition.  (Contributed by NM,
       12-Aug-1993.) $)
    euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      wph vx weu wph vx cv vz cv wceq wb vx wal vz wex wph vx cv vy cv wceq wb
      vx wal vy wex wph vx vz df-eu wph vx cv vz cv wceq wb vx wal wph vx cv vy
      cv wceq wb vx wal vz vy wph vx cv vz cv wceq wb vy vx wph vx cv vz cv
      wceq vy euf.1 vx cv vz cv wceq vy nfv nfbi nfal wph vx cv vy cv wceq wb
      vz vx wph vx cv vy cv wceq vz wph vz nfv vx cv vy cv wceq vz nfv nfbi
      nfal vz cv vy cv wceq wph vx cv vz cv wceq wb wph vx cv vy cv wceq wb vx
      vz cv vy cv wceq vx cv vz cv wceq vx cv vy cv wceq wph vz vy vx equequ2
      bibi2d albidv cbvex bitri $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.  $d y ch $.
    eubid.1 $e |- F/ x ph $.
    eubid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)
    eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      wph wps vx cv vy cv wceq wb vx wal vy wex wch vx cv vy cv wceq wb vx wal
      vy wex wps vx weu wch vx weu wph wps vx cv vy cv wceq wb vx wal wch vx cv
      vy cv wceq wb vx wal vy wph wps vx cv vy cv wceq wb wch vx cv vy cv wceq
      wb vx eubid.1 wph wps wch vx cv vy cv wceq eubid.2 bibi1d albid exbidv
      wps vx vy df-eu wch vx vy df-eu 3bitr4g $.
  $}

  ${
    $d x ph $.
    eubidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)
    eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      wph wps wch vx wph vx nfv eubidv.1 eubid $.
  $}

  ${
    eubii.1 $e |- ( ph <-> ps ) $.
    $( Introduce uniqueness quantifier to both sides of an equivalence.
       (Contributed by NM, 9-Jul-1994.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
    eubii $p |- ( E! x ph <-> E! x ps ) $=
      wph vx weu wps vx weu wb wtru wph wps vx wph wps wb wtru eubii.1 a1i
      eubidv trud $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by NM,
       9-Jul-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfeu1 $p |- F/ x E! x ph $=
      wph vx weu wph vx cv vy cv wceq wb vx wal vy wex vx wph vx vy df-eu wph
      vx cv vy cv wceq wb vx wal vx vy wph vx cv vy cv wceq wb vx nfa1 nfex
      nfxfr $.
  $}

  $( Bound-variable hypothesis builder for "at most one."  (Contributed by NM,
     8-Mar-1995.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
  nfmo1 $p |- F/ x E* x ph $=
    wph vx wmo wph vx wex wph vx weu wi vx wph vx df-mo wph vx wex wph vx weu
    vx wph vx nfe1 wph vx nfeu1 nfim nfxfr $.

  ${
    $d y z $.  $d z ph $.  $d z ps $.
    nfeud2.1 $e |- F/ y ph $.
    nfeud2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    nfeud2 $p |- ( ph -> F/ x E! y ps ) $=
      wps vy weu wps vy cv vz cv wceq wb vy wal vz wex wph vx wps vy vz df-eu
      wph wps vy cv vz cv wceq wb vy wal vx vz wph vz nfv wph vx cv vz cv wceq
      vx wal wn wa wps vy cv vz cv wceq wb vx vy wph vx cv vz cv wceq vx wal wn
      vy nfeud2.1 vx vz vy nfnae nfan wph vx cv vz cv wceq vx wal wn wa vx cv
      vy cv wceq vx wal wn wa wps vy cv vz cv wceq vx wph vx cv vy cv wceq vx
      wal wn wps vx wnf vx cv vz cv wceq vx wal wn nfeud2.2 adantlr vx cv vz cv
      wceq vx wal wn vx cv vy cv wceq vx wal wn vy cv vz cv wceq vx wnf wph vx
      cv vy cv wceq vx wal wn vx cv vz cv wceq vx wal wn vy cv vz cv wceq vx
      wnf vy vz vx nfeqf ancoms adantll nfbid nfald2 nfexd2 nfxfrd $.

    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    nfmod2 $p |- ( ph -> F/ x E* y ps ) $=
      wps vy wmo wps vy wex wps vy weu wi wph vx wps vy df-mo wph wps vy wex
      wps vy weu vx wph wps vx vy nfeud2.1 nfeud2.2 nfexd2 wph wps vx vy
      nfeud2.1 nfeud2.2 nfeud2 nfimd nfxfrd $.
  $}

  ${
    nfeud.1 $e |- F/ y ph $.
    nfeud.2 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfeu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfeud $p |- ( ph -> F/ x E! y ps ) $=
      wph wps vx vy nfeud.1 wph wps vx wnf vx cv vy cv wceq vx wal wn nfeud.2
      adantr nfeud2 $.

    $( Bound-variable hypothesis builder for "at most one."  (Contributed by
       Mario Carneiro, 14-Nov-2016.) $)
    nfmod $p |- ( ph -> F/ x E* y ps ) $=
      wph wps vx vy nfeud.1 wph wps vx wnf vx cv vy cv wceq vx wal wn nfeud.2
      adantr nfmod2 $.
  $}

  ${
    $d y z $.  $d x z $.  $d z ph $.
    nfeu.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for "at most one."  Note that ` x `
       and ` y ` needn't be distinct (this makes the proof more difficult).
       (Contributed by NM, 8-Mar-1995.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    nfeu $p |- F/ x E! y ph $=
      wph vy weu vx wnf wtru wph vx vy vy nftru wph vx wnf wtru nfeu.1 a1i
      nfeud trud $.

    $( Bound-variable hypothesis builder for "at most one."  (Contributed by
       NM, 9-Mar-1995.) $)
    nfmo $p |- F/ x E* y ph $=
      wph vy wmo vx wnf wtru wph vx vy vy nftru wph vx wnf wtru nfeu.1 a1i
      nfmod trud $.
  $}

  ${
    $d w y z $.  $d ph z w $.  $d w x z $.
    sb8eu.1 $e |- F/ y ph $.
    $( Variable substitution in uniqueness quantifier.  (Contributed by NM,
       7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      wph vx cv vz cv wceq wb vx wal vz wex wph vx vy wsb vy cv vz cv wceq wb
      vy wal vz wex wph vx weu wph vx vy wsb vy weu wph vx cv vz cv wceq wb vx
      wal wph vx vy wsb vy cv vz cv wceq wb vy wal vz wph vx cv vz cv wceq wb
      vx wal wph vx cv vz cv wceq wb vx vw wsb vw wal wph vx cv vz cv wceq wb
      vx vy wsb vy wal wph vx vy wsb vy cv vz cv wceq wb vy wal wph vx cv vz cv
      wceq wb vx vw wph vx cv vz cv wceq wb vw nfv sb8 wph vx cv vz cv wceq wb
      vx vw wsb wph vx cv vz cv wceq wb vx vy wsb vw vy wph vx cv vz cv wceq wb
      vx vw wsb wph vx vw wsb vx cv vz cv wceq vx vw wsb wb vy wph vx cv vz cv
      wceq vx vw sbbi wph vx vw wsb vx cv vz cv wceq vx vw wsb vy wph vx vw vy
      sb8eu.1 nfsb vx cv vz cv wceq vx vw wsb vw cv vz cv wceq vy vw vx vz
      equsb3 vw cv vz cv wceq vy nfv nfxfr nfbi nfxfr wph vx cv vz cv wceq wb
      vx vy wsb vw nfv wph vx cv vz cv wceq wb vw vy vx sbequ cbval wph vx cv
      vz cv wceq wb vx vy wsb wph vx vy wsb vy cv vz cv wceq wb vy vx cv vz cv
      wceq vy cv vz cv wceq wph vx vy vy vx vz equsb3 sblbis albii 3bitri exbii
      wph vx vz df-eu wph vx vy wsb vy vz df-eu 3bitr4i $.

    $( Variable substitution in uniqueness quantifier.  (Contributed by
       Alexander van der Vekens, 17-Jun-2017.) $)
    sb8mo $p |- ( E* x ph <-> E* y [ y / x ] ph ) $=
      wph vx wex wph vx weu wi wph vx vy wsb vy wex wph vx vy wsb vy weu wi wph
      vx wmo wph vx vy wsb vy wmo wph vx wex wph vx vy wsb vy wex wph vx weu
      wph vx vy wsb vy weu wph vx vy sb8eu.1 sb8e wph vx vy sb8eu.1 sb8eu
      imbi12i wph vx df-mo wph vx vy wsb vy df-mo 3bitr4i $.
  $}

  ${
    cbveu.1 $e |- F/ y ph $.
    cbveu.2 $e |- F/ x ps $.
    cbveu.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 25-Nov-1994.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    cbveu $p |- ( E! x ph <-> E! y ps ) $=
      wph vx weu wph vx vy wsb vy weu wps vy weu wph vx vy cbveu.1 sb8eu wph vx
      vy wsb wps vy wph wps vx vy cbveu.2 cbveu.3 sbie eubii bitri $.
  $}

  ${
    $d x y $.
    eu1.1 $e |- F/ y ph $.
    $( An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110.  (Contributed by NM, 20-Aug-1993.)  (Revised
       by Mario Carneiro, 7-Oct-2016.) $)
    eu1 $p |- ( E! x ph <->
                E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $=
      wph vx vy wsb vy weu wph vx vy wsb vy cv vx cv wceq wb vy wal vx wex wph
      vx weu wph wph vx vy wsb vx cv vy cv wceq wi vy wal wa vx wex wph vx vy
      wsb vy vx wph vx vy nfs1v euf wph vx vy eu1.1 sb8eu wph wph vx vy wsb vx
      cv vy cv wceq wi vy wal wa wph vx vy wsb vy cv vx cv wceq wb vy wal vx
      wph vx vy wsb vx cv vy cv wceq wi vy wal wph wa wph vx vy wsb vy cv vx cv
      wceq wi vy wal vy cv vx cv wceq wph vx vy wsb wi vy wal wa wph wph vx vy
      wsb vx cv vy cv wceq wi vy wal wa wph vx vy wsb vy cv vx cv wceq wb vy
      wal wph vx vy wsb vx cv vy cv wceq wi vy wal wph vx vy wsb vy cv vx cv
      wceq wi vy wal wph vy cv vx cv wceq wph vx vy wsb wi vy wal wph vx vy wsb
      vx cv vy cv wceq wi wph vx vy wsb vy cv vx cv wceq wi vy vx cv vy cv wceq
      vy cv vx cv wceq wph vx vy wsb vx vy equcom imbi2i albii wph vx vy eu1.1
      sb6rf anbi12i wph wph vx vy wsb vx cv vy cv wceq wi vy wal ancom wph vx
      vy wsb vy cv vx cv wceq vy albiim 3bitr4i exbii 3bitr4i $.
  $}

  ${
    $d x y z $.  $d ph z $.
    mo.1 $e |- F/ y ph $.
    $( Equivalent definitions of "there exists at most one."  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    mo $p |- ( E. y A. x ( ph -> x = y ) <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      wph vx cv vy cv wceq wi vx wal vy wex wph wph vx vy wsb wa vx cv vy cv
      wceq wi vy wal vx wal wph vx cv vy cv wceq wi vx wal vy wex wph vx cv vz
      cv wceq wi vx wal vz wex wph wph vx vy wsb wa vx cv vy cv wceq wi vy wal
      vx wal wph vx cv vz cv wceq wi vx wal wph vx cv vy cv wceq wi vx wal vz
      vy wph vx cv vz cv wceq wi vy vx wph vx cv vz cv wceq vy mo.1 vx cv vz cv
      wceq vy nfv nfim nfal wph vx cv vy cv wceq wi vx wal vz nfv vz cv vy cv
      wceq wph vx cv vz cv wceq wi wph vx cv vy cv wceq wi vx vz cv vy cv wceq
      vx cv vz cv wceq vx cv vy cv wceq wph vz vy vx equequ2 imbi2d albidv
      cbvex wph vx cv vz cv wceq wi vx wal wph wph vx vy wsb wa vx cv vy cv
      wceq wi vy wal vx wal vz wph vx cv vz cv wceq wi vx wal wph vx cv vz cv
      wceq wi wph vx vy wsb vy cv vz cv wceq wi wa vy wal vx wal wph wph vx vy
      wsb wa vx cv vy cv wceq wi vy wal vx wal wph vx cv vz cv wceq wi vx wal
      wph vx cv vz cv wceq wi vx wal wph vx vy wsb vy cv vz cv wceq wi vy wal
      wa wph vx cv vz cv wceq wi wph vx vy wsb vy cv vz cv wceq wi wa vy wal vx
      wal wph vx cv vz cv wceq wi vx wal wph vx vy wsb vy cv vz cv wceq wi vy
      wal wph vx cv vz cv wceq wi wph vx vy wsb vy cv vz cv wceq wi vx vy wph
      vx cv vz cv wceq vy mo.1 vx cv vz cv wceq vy nfv nfim wph vx vy wsb vy cv
      vz cv wceq vx wph vx vy mo.1 nfs1 vy cv vz cv wceq vx nfv nfim vx cv vy
      cv wceq wph vx vy wsb wph vx cv vz cv wceq vy cv vz cv wceq wph vx vy
      sbequ2 vx vy vz ax-8 imim12d cbv3 ancli wph vx cv vz cv wceq wi wph vx vy
      wsb vy cv vz cv wceq wi vx vy wph vx cv vz cv wceq vy mo.1 vx cv vz cv
      wceq vy nfv nfim wph vx vy wsb vy cv vz cv wceq vx wph vx vy mo.1 nfs1 vy
      cv vz cv wceq vx nfv nfim aaan sylibr wph vx cv vz cv wceq wi wph vx vy
      wsb vy cv vz cv wceq wi wa wph wph vx vy wsb wa vx cv vy cv wceq wi vx vy
      wph vx cv vz cv wceq wi wph vx vy wsb vy cv vz cv wceq wi wa wph wph vx
      vy wsb wa vx cv vz cv wceq vy cv vz cv wceq wa vx cv vy cv wceq wph vx cv
      vz cv wceq wph vx vy wsb vy cv vz cv wceq prth vx vy vz equtr2 syl6
      2alimi syl exlimiv sylbir wph wph vx vy wsb wa vx cv vy cv wceq wi vy wal
      vx wal wph vx vy wsb vy wex wph vx cv vy cv wceq wi vx wal vy wex wph wph
      vx vy wsb wa vx cv vy cv wceq wi vy wal vx wal wph vx vy wsb wph vx cv vy
      cv wceq wi vx wal vy wph wph vx vy wsb wa vx cv vy cv wceq wi vy vx nfa2
      wph vx vy wsb wph wph vx vy wsb wa vx cv vy cv wceq wi vy wal vx wal wph
      vx cv vy cv wceq wi vx wal wph vx vy wsb wph wph vx vy wsb wa vx cv vy cv
      wceq wi vy wal wph vx cv vy cv wceq wi vx wph vx vy mo.1 nfs1 wph wph vx
      vy wsb wa vx cv vy cv wceq wi vy wal wph wph vx vy wsb vx cv vy cv wceq
      wph wph vx vy wsb wa vx cv vy cv wceq wi vy wal wph wph vx vy wsb vx cv
      vy cv wceq wph wph vx vy wsb wa vx cv vy cv wceq wi vy sp exp3a com3r
      alimd com12 eximd wph vx vy wsb vy wex wn wph vx vy wsb wn vy wal wph vx
      cv vy cv wceq wi vx wal vy wex wph vx vy wsb vy alnex wph vx vy wsb wn vy
      wal wph wn vx wal wph vx cv vy cv wceq wi vx wal wph vx cv vy cv wceq wi
      vx wal vy wex wph vx vy wsb wn wph wn vy vx wph vx vy wsb vx wph vx vy
      mo.1 nfs1 nfn wph vy mo.1 nfn vy cv vx cv wceq wph wph vx vy wsb wph wph
      vx vy wsb wi vx vy wph vx vy sbequ1 equcoms con3d cbv3 wph wn wph vx cv
      vy cv wceq wi vx wph vx cv vy cv wceq pm2.21 alimi wph vx cv vy cv wceq
      wi vx wal vy 19.8a 3syl sylbir pm2.61d1 impbii $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Existential uniqueness implies existence.  (Contributed by NM,
       15-Sep-1993.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    euex $p |- ( E! x ph -> E. x ph ) $=
      wph vx weu wph wph vx vy wsb vx cv vy cv wceq wi vy wal wa vx wex wph vx
      wex wph vx vy wph vy nfv eu1 wph wph vx vy wsb vx cv vy cv wceq wi vy wal
      vx exsimpl sylbi $.
  $}

  ${
    $d x y $.
    eumo0.1 $e |- F/ y ph $.
    $( Existential uniqueness implies "at most one."  (Contributed by NM,
       8-Jul-1994.) $)
    eumo0 $p |- ( E! x ph -> E. y A. x ( ph -> x = y ) ) $=
      wph vx weu wph vx vy weq wb vx wal vy wex wph vx vy weq wi vx wal vy wex
      wph vx vy eumo0.1 euf wph vx vy weq wb vx wal wph vx vy weq wi vx wal vy
      wph vx vy weq wb wph vx vy weq wi vx wph vx vy weq bi1 alimi eximi sylbi
      $.
  $}

  ${
    $d x y $.
    eu2.1 $e |- F/ y ph $.
    $( An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26.  (Contributed by NM, 8-Jul-1994.) $)
    eu2 $p |- ( E! x ph <->
    ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      wph vx weu wph vx wex wph wph vx vy wsb wa vx vy weq wi vy wal vx wal wa
      wph vx weu wph vx wex wph wph vx vy wsb wa vx vy weq wi vy wal vx wal wph
      vx euex wph vx weu wph vx vy weq wi vx wal vy wex wph wph vx vy wsb wa vx
      vy weq wi vy wal vx wal wph vx vy eu2.1 eumo0 wph vx vy eu2.1 mo sylib
      jca wph vx wex wph wph vx vy wsb wa vx vy weq wi vy wal vx wal wa wph wph
      vx vy wsb vx vy weq wi vy wal wa vx wex wph vx weu wph vx wex wph wph vx
      vy wsb wa vx vy weq wi vy wal vx wal wa wph wph wph vx vy wsb wa vx vy
      weq wi vy wal wa vx wex wph wph vx vy wsb vx vy weq wi vy wal wa vx wex
      wph wph wph vx vy wsb wa vx vy weq wi vy wal vx 19.29r wph wph wph vx vy
      wsb wa vx vy weq wi vy wal wa wph wph vx vy wsb vx vy weq wi vy wal wa vx
      wph wph wph vx vy wsb wa vx vy weq wi vy wal wa wph wph wph vx vy wsb vx
      vy weq wi vy wal wi wa wph wph vx vy wsb vx vy weq wi vy wal wa wph wph
      vx vy wsb wa vx vy weq wi vy wal wph wph vx vy wsb vx vy weq wi vy wal wi
      wph wph wph vx vy wsb wa vx vy weq wi vy wal wph wph vx vy wsb vx vy weq
      wi wi vy wal wph wph vx vy wsb vx vy weq wi vy wal wi wph wph vx vy wsb
      wa vx vy weq wi wph wph vx vy wsb vx vy weq wi wi vy wph wph vx vy wsb vx
      vy weq impexp albii wph wph vx vy wsb vx vy weq wi vy eu2.1 19.21 bitri
      anbi2i wph wph vx vy wsb vx vy weq wi vy wal abai bitr4i exbii sylib wph
      vx vy eu2.1 eu1 sylibr impbii $.
  $}

  ${
    $d x y $.
    eu3.1 $e |- F/ y ph $.
    $( An alternate way to express existential uniqueness.  (Contributed by NM,
       8-Jul-1994.) $)
    eu3 $p |- ( E! x ph <->
                ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      wph vx weu wph vx wex wph wph vx vy wsb wa vx vy weq wi vy wal vx wal wa
      wph vx wex wph vx vy weq wi vx wal vy wex wa wph vx vy eu3.1 eu2 wph vx
      vy weq wi vx wal vy wex wph wph vx vy wsb wa vx vy weq wi vy wal vx wal
      wph vx wex wph vx vy eu3.1 mo anbi2i bitr4i $.
  $}

  ${
    euor.1 $e |- F/ x ph $.
    $( Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       21-Oct-2005.) $)
    euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      wph wn wps vx weu wph wps wo vx weu wph wn wps wph wps wo vx wph vx
      euor.1 nfn wph wps biorf eubid biimpa $.
  $}

  ${
    $d x ph $.
    $( Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       23-Mar-1995.) $)
    euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      wph wps vx wph vx nfv euor $.
  $}

  ${
    $d x y $.
    mo2.1 $e |- F/ y ph $.
    $( Alternate definition of "at most one."  (Contributed by NM,
       8-Mar-1995.) $)
    mo2 $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      wph vx wmo wph vx wex wph vx weu wi wph vx vy weq wi vx wal vy wex wph vx
      df-mo wph vx wex wph vx weu wi wph vx vy weq wi vx wal vy wex wph vx wex
      wph vx weu wph vx vy weq wi vx wal vy wex wph vx wex wn wph wn vx wal wph
      vx vy weq wi vx wal vy wex wph vx alnex wph wn vx wal wph vx vy weq wi vx
      wal wph vx vy weq wi vx wal vy wex wph wn wph vx vy weq wi vx wph vx vy
      weq pm2.21 alimi wph vx vy weq wi vx wal vy 19.8a syl sylbir wph vx vy
      mo2.1 eumo0 ja wph vx weu wph vx wex wph vx vy weq wi vx wal vy wex wph
      vx vy mo2.1 eu3 simplbi2com impbii bitri $.
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    $( Substitution into "at most one".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $=
      wph vz cv vw cv wceq wi vz wal vw wex vx vy wsb wph vx vy wsb vz cv vw cv
      wceq wi vz wal vw wex wph vz wmo vx vy wsb wph vx vy wsb vz wmo wph vz cv
      vw cv wceq wi vz wal vw wex vx vy wsb wph vz cv vw cv wceq wi vz wal vx
      vy wsb vw wex wph vx vy wsb vz cv vw cv wceq wi vz wal vw wex wph vz cv
      vw cv wceq wi vz wal vw vx vy sbex wph vz cv vw cv wceq wi vz wal vx vy
      wsb wph vx vy wsb vz cv vw cv wceq wi vz wal vw wph vz cv vw cv wceq wi
      wph vx vy wsb vz cv vw cv wceq wi vx vy vz wph vz cv vw cv wceq vx vy vz
      cv vw cv wceq vx nfv sblim sbalv exbii bitri wph vz wmo wph vz cv vw cv
      wceq wi vz wal vw wex vx vy wph vz vw wph vw nfv mo2 sbbii wph vx vy wsb
      vz vw wph vx vy wsb vw nfv mo2 3bitr4i $.
  $}

  ${
    $d x y $.
    mo3.1 $e |- F/ y ph $.
    $( Alternate definition of "at most one."  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis.  (Contributed by NM,
       8-Mar-1995.) $)
    mo3 $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      wph vx wmo wph vx vy weq wi vx wal vy wex wph wph vx vy wsb wa vx vy weq
      wi vy wal vx wal wph vx vy mo3.1 mo2 wph vx vy mo3.1 mo bitri $.
  $}

  ${
    $d x y $.  $d y ph $.
    mo4f.1 $e |- F/ x ps $.
    mo4f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution.  (Contributed by
       NM, 10-Apr-2004.) $)
    mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      wph vx wmo wph wph vx vy wsb wa vx vy weq wi vy wal vx wal wph wps wa vx
      vy weq wi vy wal vx wal wph vx vy wph vy nfv mo3 wph wph vx vy wsb wa vx
      vy weq wi wph wps wa vx vy weq wi vx vy wph wph vx vy wsb wa wph wps wa
      vx vy weq wph vx vy wsb wps wph wph wps vx vy mo4f.1 mo4f.2 sbie anbi2i
      imbi1i 2albii bitri $.
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    mo4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution.  (Contributed by
       NM, 26-Jul-1995.) $)
    mo4 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      wph wps vx vy wps vx nfv mo4.1 mo4f $.
  $}

  ${
    mobid.1 $e |- F/ x ph $.
    mobid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction rule).
       (Contributed by NM, 8-Mar-1995.) $)
    mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      wph wps vx wex wps vx weu wi wch vx wex wch vx weu wi wps vx wmo wch vx
      wmo wph wps vx wex wch vx wex wps vx weu wch vx weu wph wps wch vx
      mobid.1 mobid.2 exbid wph wps wch vx mobid.1 mobid.2 eubid imbi12d wps vx
      df-mo wch vx df-mo 3bitr4g $.
  $}

  ${
    $d x ph $.
    mobidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction rule).
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    mobidv $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      wph wps wch vx wph vx nfv mobidv.1 mobid $.
  $}

  ${
    mobii.1 $e |- ( ps <-> ch ) $.
    $( Formula-building rule for "at most one" quantifier (inference rule).
       (Contributed by NM, 9-Mar-1995.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
    mobii $p |- ( E* x ps <-> E* x ch ) $=
      wps vx wmo wch vx wmo wb wtru wps wch vx wps wch wb wtru mobii.1 a1i
      mobidv trud $.
  $}

  ${
    cbvmo.1 $e |- F/ y ph $.
    cbvmo.2 $e |- F/ x ps $.
    cbvmo.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 9-Mar-1995.)  (Revised by Andrew Salmon,
       8-Jun-2011.) $)
    cbvmo $p |- ( E* x ph <-> E* y ps ) $=
      wph vx wex wph vx weu wi wps vy wex wps vy weu wi wph vx wmo wps vy wmo
      wph vx wex wps vy wex wph vx weu wps vy weu wph wps vx vy cbvmo.1 cbvmo.2
      cbvmo.3 cbvex wph wps vx vy cbvmo.1 cbvmo.2 cbvmo.3 cbveu imbi12i wph vx
      df-mo wps vy df-mo 3bitr4i $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Uniqueness in terms of "at most one."  (Contributed by NM,
       23-Mar-1995.) $)
    eu5 $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $=
      wph vx weu wph vx wex wph vx cv vy cv wceq wi vx wal vy wex wa wph vx wex
      wph vx wmo wa wph vx vy wph vy nfv eu3 wph vx wmo wph vx cv vy cv wceq wi
      vx wal vy wex wph vx wex wph vx vy wph vy nfv mo2 anbi2i bitr4i $.
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    eu4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Uniqueness using implicit substitution.  (Contributed by NM,
       26-Jul-1995.) $)
    eu4 $p |- ( E! x ph <-> ( E. x ph /\
             A. x A. y ( ( ph /\ ps ) -> x = y ) ) ) $=
      wph vx weu wph vx wex wph vx wmo wa wph vx wex wph wps wa vx vy weq wi vy
      wal vx wal wa wph vx eu5 wph vx wmo wph wps wa vx vy weq wi vy wal vx wal
      wph vx wex wph wps vx vy eu4.1 mo4 anbi2i bitri $.
  $}

  $( Existential uniqueness implies "at most one."  (Contributed by NM,
     23-Mar-1995.) $)
  eumo $p |- ( E! x ph -> E* x ph ) $=
    wph vx weu wph vx wex wph vx wmo wph vx eu5 simprbi $.

  ${
    eumoi.1 $e |- E! x ph $.
    $( "At most one" inferred from existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)
    eumoi $p |- E* x ph $=
      wph vx weu wph vx wmo eumoi.1 wph vx eumo ax-mp $.
  $}

  $( Existence in terms of "at most one" and uniqueness.  (Contributed by NM,
     5-Apr-2004.) $)
  exmoeu $p |- ( E. x ph <-> ( E* x ph -> E! x ph ) ) $=
    wph vx wex wph vx wmo wph vx weu wi wph vx wmo wph vx wex wph vx weu wph vx
    wmo wph vx wex wph vx weu wi wph vx df-mo biimpi com12 wph vx wmo wph vx
    weu wi wph vx wex wph vx weu wi wph vx wex wi wph vx wex wph vx wex wph vx
    weu wi wph vx wmo wph vx weu wph vx wex wph vx wmo wph vx wex wph vx weu wi
    wph vx df-mo biimpri wph vx euex imim12i wph vx wex wph vx weu peirce syl
    impbii $.

  $( Existence implies "at most one" is equivalent to uniqueness.  (Contributed
     by NM, 5-Apr-2004.) $)
  exmoeu2 $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $=
    wph vx weu wph vx wex wph vx wmo wph vx eu5 baibr $.

  $( Absorption of existence condition by "at most one."  (Contributed by NM,
     4-Nov-2002.) $)
  moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $=
    wph vx wex wph vx wex wph vx weu wi wi wph vx wex wph vx weu wi wph vx wex
    wph vx wmo wi wph vx wmo wph vx wex wph vx weu pm5.4 wph vx wmo wph vx wex
    wph vx weu wi wph vx wex wph vx df-mo imbi2i wph vx df-mo 3bitr4ri $.

  $( Something exists or at most one exists.  (Contributed by NM,
     8-Mar-1995.) $)
  exmo $p |- ( E. x ph \/ E* x ph ) $=
    wph vx wex wph vx wmo wph vx wex wn wph vx wex wph vx weu wi wph vx wmo wph
    vx wex wph vx weu pm2.21 wph vx df-mo sylibr orri $.

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 22-Apr-1995.) $)
    moim $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $=
      wph wps wi vx wal wps vx cv vy cv wceq wi vx wal vy wex wph vx cv vy cv
      wceq wi vx wal vy wex wps vx wmo wph vx wmo wph wps wi vx wal wps vx cv
      vy cv wceq wi vx wal wph vx cv vy cv wceq wi vx wal vy wph wps wi wps vx
      cv vy cv wceq wi wph vx cv vy cv wceq wi vx wph wps vx cv vy cv wceq
      imim1 al2imi eximdv wps vx vy wps vy nfv mo2 wph vx vy wph vy nfv mo2
      3imtr4g $.
  $}

  ${
    immoi.1 $e |- ( ph -> ps ) $.
    $( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 15-Feb-2006.) $)
    moimi $p |- ( E* x ps -> E* x ph ) $=
      wph wps wi wps vx wmo wph vx wmo wi vx wph wps vx moim immoi.1 mpg $.
  $}

  ${
    $d x y $.  $d x y ph $.  $d y ps $.
    $( Move antecedent outside of "at most one."  (Contributed by NM,
       28-Jul-1995.) $)
    morimv $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $=
      wph wph wps wi vx wmo wps vx wmo wph wph wps wi vx cv vy cv wceq wi vx
      wal vy wex wps vx cv vy cv wceq wi vx wal vy wex wph wps wi vx wmo wps vx
      wmo wph wph wps wi vx cv vy cv wceq wi vx wal wps vx cv vy cv wceq wi vx
      wal vy wph wph wps wi vx cv vy cv wceq wi wps vx cv vy cv wceq wi vx wph
      wps wph wps wi vx cv vy cv wceq wps wph wps wi wi wph wps wph ax-1 a1i
      imim1d alimdv eximdv wph wps wi vx vy wph wps wi vy nfv mo2 wps vx vy wps
      vy nfv mo2 3imtr4g com12 $.
  $}

  $( Uniqueness implies "at most one" through implication.  (Contributed by NM,
     22-Apr-1995.) $)
  euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $=
    wps vx weu wps vx wmo wph wps wi vx wal wph vx wmo wps vx eumo wph wps vx
    moim syl5 $.

  $( Add existential uniqueness quantifiers to an implication.  Note the
     reversed implication in the antecedent.  (Contributed by NM,
     19-Oct-2005.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
  euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $=
    wph vx wex wph wps wi vx wal wa wps vx weu wph vx wex wph vx wmo wa wph vx
    weu wph vx wex wps vx weu wph vx wex wph wps wi vx wal wph vx wmo wph vx
    wex wps vx weu ax-1 wph wps vx euimmo anim12ii wph vx eu5 syl6ibr $.

  $( "At most one" is still the case when a conjunct is added.  (Contributed by
     NM, 22-Apr-1995.) $)
  moan $p |- ( E* x ph -> E* x ( ps /\ ph ) ) $=
    wps wph wa wph vx wps wph simpr moimi $.

  ${
    moani.1 $e |- E* x ph $.
    $( "At most one" is still true when a conjunct is added.  (Contributed by
       NM, 9-Mar-1995.) $)
    moani $p |- E* x ( ps /\ ph ) $=
      wph vx wmo wps wph wa vx wmo moani.1 wph wps vx moan ax-mp $.
  $}

  $( "At most one" is still the case when a disjunct is removed.  (Contributed
     by NM, 5-Apr-2004.) $)
  moor $p |- ( E* x ( ph \/ ps ) -> E* x ph ) $=
    wph wph wps wo vx wph wps orc moimi $.

  $( "At most one" imports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran1 $p |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) ) $=
    wph vx wmo wph wps wa vx wmo wps vx wmo wph wps wa wph vx wph wps simpl
    moimi wps wph vx moan jaoi $.

  $( "At most one" exports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran2 $p |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) ) $=
    wph wps wo vx wmo wph vx wmo wps vx wmo wph wps vx moor wps wph wps wo vx
    wps wph olc moimi jca $.

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    moanim.1 $e |- F/ x ph $.
    $( Introduction of a conjunct into "at most one" quantifier.  (Contributed
       by NM, 3-Dec-2001.) $)
    moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      wph wps wa vx vy weq wi vx wal vy wex wph wps vx vy weq wi vx wal wi vy
      wex wph wps wa vx wmo wph wps vx wmo wi wph wps wa vx vy weq wi vx wal
      wph wps vx vy weq wi vx wal wi vy wph wps wa vx vy weq wi vx wal wph wps
      vx vy weq wi wi vx wal wph wps vx vy weq wi vx wal wi wph wps wa vx vy
      weq wi wph wps vx vy weq wi wi vx wph wps vx vy weq impexp albii wph wps
      vx vy weq wi vx moanim.1 19.21 bitri exbii wph wps wa vx vy wph wps wa vy
      nfv mo2 wph wps vx wmo wi wph wps vx vy weq wi vx wal vy wex wi wph wps
      vx vy weq wi vx wal wi vy wex wps vx wmo wps vx vy weq wi vx wal vy wex
      wph wps vx vy wps vy nfv mo2 imbi2i wph wps vx vy weq wi vx wal vy 19.37v
      bitr4i 3bitr4i $.

    $( Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 19-Feb-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      wph wps wa vx weu wph wps vx weu wa wph wps wa vx wex wph wps wa vx wmo
      wa wph wps vx wex wps vx wmo wa wa wph wps wa vx weu wph wps vx weu wa
      wph wps wa vx wex wph wps wa vx wmo wa wph wps vx wex wps vx wmo wph wps
      wa vx wex wph wph wps wa vx wmo wph wps wa wph vx moanim.1 wph wps simpl
      exlimi adantr wph wps wa vx wex wps vx wex wph wps wa vx wmo wph wps wa
      wps vx wph wps simpr eximi adantr wph wps wa vx wex wph wps wa vx wmo wps
      vx wmo wph wps wa vx wex wph wps wa wps vx wph wps wa vx nfe1 wph wps wa
      vx wex wph wps wa wps wph wps simpr wph wps wa vx wex wps wph wph wps wa
      vx wex wph wps wph wps wa wph vx moanim.1 wph wps simpl exlimi a1d ancrd
      impbid2 mobid biimpa jca32 wph wps wa vx eu5 wps vx weu wps vx wex wps vx
      wmo wa wph wps vx eu5 anbi2i 3imtr4i wph wps vx weu wph wps wa vx weu wph
      wps wph wps wa vx moanim.1 wph wps ibar eubid biimpa impbii $.
  $}

  ${
    $d x y ph $.  $d y ps $.
    $( Introduction of a conjunct into "at most one" quantifier.  (Contributed
       by NM, 23-Mar-1995.) $)
    moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      wph wps vx wph vx nfv moanim $.
  $}

  $( Nested "at most one" and uniqueness quantifiers.  (Contributed by NM,
     25-Jan-2006.) $)
  moaneu $p |- E* x ( ph /\ E! x ph ) $=
    wph wph vx weu wa vx wmo wph vx weu wph wa vx wmo wph vx weu wph wa vx wmo
    wph vx weu wph vx wmo wi wph vx eumo wph vx weu wph vx wph vx nfeu1 moanim
    mpbir wph wph vx weu wa wph vx weu wph wa vx wph wph vx weu ancom mobii
    mpbir $.

  $( Nested "at most one" quantifiers.  (Contributed by NM, 25-Jan-2006.) $)
  moanmo $p |- E* x ( ph /\ E* x ph ) $=
    wph wph vx wmo wa vx wmo wph vx wmo wph wa vx wmo wph vx wmo wph wa vx wmo
    wph vx wmo wph vx wmo wi wph vx wmo id wph vx wmo wph vx wph vx nfmo1
    moanim mpbir wph wph vx wmo wa wph vx wmo wph wa vx wph wph vx wmo ancom
    mobii mpbir $.

  ${
    $d x ph $.
    $( Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 23-Mar-1995.) $)
    euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      wph wps vx wph vx nfv euan $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" picks a variable value, eliminating an existential
       quantifier.  (Contributed by NM, 27-Jan-1997.) $)
    mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
      wph wps wa vx wex wph vx wmo wph wps wi wph wps wa vx wex wph vx vy wsb
      wps vx vy wsb wa vy wex wph vx wmo wph wps wi wi wph wps wa wph vx vy wsb
      wps vx vy wsb wa vx vy wph wps wa vy nfv wph vx vy wsb wps vx vy wsb vx
      wph vx vy nfs1v wps vx vy nfs1v nfan vx cv vy cv wceq wph wph vx vy wsb
      wps wps vx vy wsb wph vx vy sbequ12 wps vx vy sbequ12 anbi12d cbvex wph
      vx vy wsb wps vx vy wsb wa wph vx wmo wph wps wi wi vy wph vx wmo wph wph
      vx vy wsb wa vx cv vy cv wceq wi wph vx vy wsb wps vx vy wsb wa wph wps
      wi wph vx wmo wph wph vx vy wsb wa vx cv vy cv wceq wi vy wal vx wal wph
      wph vx vy wsb wa vx cv vy cv wceq wi wph vx vy wph vy nfv mo3 wph wph vx
      vy wsb wa vx cv vy cv wceq wi vy wal wph wph vx vy wsb wa vx cv vy cv
      wceq wi vx wph wph vx vy wsb wa vx cv vy cv wceq wi vy sp sps sylbi wph
      vx vy wsb wps vx vy wsb wph wph vx vy wsb wa vx cv vy cv wceq wi wph wps
      wi wi wph wph vx vy wsb wa vx cv vy cv wceq wi wph wph vx vy wsb wps vx
      vy wsb wps wph wph vx vy wsb wa vx cv vy cv wceq wi wph wph vx vy wsb wps
      vx vy wsb wps wi vx cv vy cv wceq wps vx vy wsb wps wi wph wph vx vy wsb
      wa wps vx vy sbequ2 imim2i exp3a com4t imp syl5 exlimiv sylbi impcom $.
  $}

  $( Existential uniqueness "picks" a variable value for which another wff is
     true.  If there is only one thing ` x ` such that ` ph ` is true, and
     there is also an ` x ` (actually the same one) such that ` ph ` and ` ps `
     are both true, then ` ph ` implies ` ps ` regardless of ` x ` .  This
     theorem can be useful for eliminating existential quantifiers in a
     hypothesis.  Compare Theorem *14.26 in [WhiteheadRussell] p. 192.
     (Contributed by NM, 10-Jul-1994.) $)
  eupick $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
    wph vx weu wph vx wmo wph wps wa vx wex wph wps wi wph vx eumo wph wps vx
    mopick sylan $.

  $( Version of ~ eupick with closed formulas.  (Contributed by NM,
     6-Sep-2008.) $)
  eupicka $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) ) $=
    wph vx weu wph wps wa vx wex wa wph wps wi vx wph vx weu wph wps wa vx wex
    vx wph vx nfeu1 wph wps wa vx nfe1 nfan wph wps vx eupick alrimi $.

  $( Existential uniqueness "pick" showing wff equivalence.  (Contributed by
     NM, 25-Nov-1994.) $)
  eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) ->
               ( ph <-> ps ) ) $=
    wph vx weu wps vx weu wph wps wa vx wex w3a wph wps wph vx weu wph wps wa
    vx wex wph wps wi wps vx weu wph wps vx eupick 3adant2 wph vx weu wps vx
    weu wph wps wa vx wex w3a wps vx weu wph wps wa vx wex wa wps vx weu wps
    wph wa vx wex wa wps wph wi wph vx weu wps vx weu wph wps wa vx wex 3simpc
    wph wps wa vx wex wps wph wa vx wex wps vx weu wph wps wa wps wph wa vx wph
    wps pm3.22 eximi anim2i wps wph vx eupick 3syl impbid $.

  $( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)
  eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $=
    wph vx weu wph wps wa vx wex wph wps wi vx wal wph vx weu wph wps wa vx wex
    wph wps wi vx wal wph wps vx eupicka ex wph wps wi vx wal wph vx weu wph
    wps wa vx wex wph wps wi vx wal wph vx weu wph wps wa vx weu wph wps wa vx
    wex wph wps wi vx wal wph wph wps wa vx wph wps wi vx nfa1 wph wps wi wph
    wph wps wa wb vx wph wps wi wph wph wps wa wph wps ancl wph wps simpl
    impbid1 sps eubid wph wps wa vx euex syl6bi com12 impbid $.

  $( "At most one" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) ->
                E. x ( ph /\ ps /\ ch ) ) $=
    wph vx wmo wph wps wa vx wex wph wch wa vx wex wph wps wch w3a vx wex wph
    vx wmo wph wps wa vx wex wa wph wch wa wph wps wch w3a vx wph vx wmo wph
    wps wa vx wex vx wph vx nfmo1 wph wps wa vx nfe1 nfan wph vx wmo wph wps wa
    vx wex wa wph wch wa wph wps wa wch wa wph wps wch w3a wph vx wmo wph wps
    wa vx wex wa wph wph wps wa wch wph vx wmo wph wps wa vx wex wa wph wps wph
    wps vx mopick ancld anim1d wph wps wch df-3an syl6ibr eximd 3impia $.

  $( Introduce or eliminate a disjunct in a uniqueness quantifier.
     (Contributed by NM, 21-Oct-2005.)  (Proof shortened by Andrew Salmon,
     9-Jul-2011.) $)
  euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $=
    wph vx wex wn wph wps wo wps vx wph vx wex vx wph vx nfe1 nfn wph vx wex wn
    wph wn wph wps wo wps wb wph wph vx wex wph vx 19.8a con3i wph wn wph wps
    wo wps wph wps orel1 wps wph olc impbid1 syl eubid $.

  ${
    moexex.1 $e |- F/ y ph $.
    $( "At most one" double quantification.  (Contributed by NM,
       3-Dec-2001.) $)
    moexex $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      wph vx wmo wps vy wmo vx wal wph wps wa vx wex vy wmo wph vx wex wph vx
      wmo wps vy wmo vx wal wph wps wa vx wex vy wmo wi wi wph wph vx wmo wps
      vy wmo vx wal wph wps wa vx wex vy wmo wi wi vx wph vx wmo wps vy wmo vx
      wal wph wps wa vx wex vy wmo wi vx wph vx nfmo1 wps vy wmo vx wal wph wps
      wa vx wex vy wmo vx wps vy wmo vx nfa1 wph wps wa vx wex vx vy wph wps wa
      vx nfe1 nfmo nfim nfim wph wph vx wmo wph wps wa vx wex wps wi vy wal wps
      vy wmo vx wal wph wps wa vx wex vy wmo wi wph wph vx wmo wph wps wa vx
      wex wps wi vy moexex.1 wph vy vx moexex.1 nfmo wph vx wmo wph wps wa vx
      wex wph wps wph vx wmo wph wps wa vx wex wph wps wi wph wps vx mopick ex
      com3r alrimd wph wps wa vx wex wps wi vy wal wps vy wmo wph wps wa vx wex
      vy wmo vx wph wps wa vx wex wps vy moim spsd syl6 exlimi wph vx wex wn
      wps vy wmo vx wal wph wps wa vx wex vy wmo wi wph vx wmo wph vx wex wn
      wph wps wa vx wex vy wmo wps vy wmo vx wal wph vx wex wn wph wps wa vx
      wex vy wex wn wph wps wa vx wex vy wmo wph wps wa vx wex vy wex wph vx
      wex wph wps wa vx wex wph vx wex vy wph vy vx moexex.1 nfex wph wps vx
      exsimpl exlimi con3i wph wps wa vx wex vy wex wph wps wa vx wex vy wmo
      wph wps wa vx wex vy exmo ori syl a1d a1d pm2.61i imp $.
  $}

  ${
    $d y ph $.
    $( "At most one" double quantification.  (Contributed by NM,
       26-Jan-1997.) $)
    moexexv $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      wph wps vx vy wph vy nfv moexex $.
  $}

  $( Double quantification with "at most one."  (Contributed by NM,
     3-Dec-2001.) $)
  2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $=
    wph vy wex vx wmo wph vx wmo vy wph vy wex vy vx wph vy nfe1 nfmo wph wph
    vy wex vx wph vy 19.8a moimi alrimi $.

  $( Double quantification with existential uniqueness.  (Contributed by NM,
     3-Dec-2001.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $=
    wph vy wex vx weu wph vy wex vx wex wph vy wex vx wmo wa wph vx weu vy wex
    wph vy wex vx eu5 wph vy wex vx wmo wph vy wex vx wex wph vx weu vy wex wph
    vy wex vx wex wph vx wex vy wex wph vy wex vx wmo wph vx weu vy wex wph vx
    vy excom wph vy wex vx wmo wph vx wex wph vx weu vy wph vy wex vy vx wph vy
    nfe1 nfmo wph vy wex vx wmo wph vx wmo wph vx wex wph vx weu wi wph wph vy
    wex vx wph vy 19.8a moimi wph vx df-mo sylib eximd syl5bi impcom sylbi $.

  $( Double quantification with existential uniqueness and "at most one."
     (Contributed by NM, 3-Dec-2001.) $)
  2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $=
    wph vy weu wph vy wmo wi wph vy wmo vx weu wph vy weu vx wmo wi vx wph vy
    weu wph vy wmo vx euimmo wph vy eumo mpg $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $=
    wph vy weu vx weu wph vy weu vx wex wph vy wex vx wex wph vy weu vx euex
    wph vy weu wph vy wex vx wph vy euex eximi syl $.

  $( A condition allowing swap of "at most one" and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)
  2moswap $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $=
    wph vy wmo vx wal wph vy wex vx wmo wph vy wex wph wa vx wex vy wmo wph vx
    wex vy wmo wph vy wex vx wmo wph vy wmo vx wal wph vy wex wph wa vx wex vy
    wmo wph vy wex wph vx vy wph vy nfe1 moexex expcom wph vx wex wph vy wex
    wph wa vx wex vy wph wph vy wex wph wa vx wph wph vy wex wph vy 19.8a
    pm4.71ri exbii mobii syl6ibr $.

  $( A condition allowing swap of uniqueness and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)
  2euswap $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $=
    wph vy wmo vx wal wph vy wex vx wex wph vy wex vx wmo wa wph vx wex vy wex
    wph vx wex vy wmo wa wph vy wex vx weu wph vx wex vy weu wph vy wmo vx wal
    wph vy wex vx wex wph vx wex vy wex wph vy wex vx wmo wph vx wex vy wmo wph
    vy wex vx wex wph vx wex vy wex wi wph vy wmo vx wal wph vx vy excomim a1i
    wph vx vy 2moswap anim12d wph vy wex vx eu5 wph vx wex vy eu5 3imtr4g $.

  $( Double existential uniqueness implies double uniqueness quantification.
     (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Mario Carneiro,
     22-Dec-2016.) $)
  2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $=
    wph vy wex vx weu wph vx wex vy weu wa wph vy weu vx wex wph vy weu vx wmo
    wa wph vy weu vx weu wph vy wex vx weu wph vy weu vx wmo wph vx wex vy weu
    wph vy weu vx wex wph vy wex vx weu wph vy wex vx wmo wph vy weu vx wmo wph
    vy wex vx eumo wph vy weu wph vy wex vx wph vy euex moimi syl wph vy vx
    2euex anim12ci wph vy weu vx eu5 sylibr $.

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Two equivalent expressions for double "at most one."  (Contributed by
       NM, 2-Feb-2005.)  (Revised by Mario Carneiro, 17-Oct-2016.) $)
    2mo $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
              A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) ->
                   ( x = z /\ y = w ) ) ) $=
      wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal vw wex vz wex
      wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi vw
      wal vz wal vy wal vx wal wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy
      wal vx wal vw wex vz wex wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy
      wal vx wal vu wex vv wex wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq
      vy cv vw cv wceq wa wi vw wal vz wal vy wal vx wal wph vx cv vv cv wceq
      vy cv vu cv wceq wa wi vy wal vx wal wph vx cv vz cv wceq vy cv vw cv
      wceq wa wi vy wal vx wal vv vu vz vw vv cv vz cv wceq vu cv vw cv wceq wa
      wph vx cv vv cv wceq vy cv vu cv wceq wa wi wph vx cv vz cv wceq vy cv vw
      cv wceq wa wi vx vy vv cv vz cv wceq vu cv vw cv wceq wa vx cv vv cv wceq
      vy cv vu cv wceq wa vx cv vz cv wceq vy cv vw cv wceq wa wph vv cv vz cv
      wceq vx cv vv cv wceq vx cv vz cv wceq vu cv vw cv wceq vy cv vu cv wceq
      vy cv vw cv wceq vv vz vx equequ2 vu vw vy equequ2 bi2anan9 imbi2d
      2albidv cbvex2v wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy wal vx wal
      wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi vw
      wal vz wal vy wal vx wal vv vu wph vx cv vv cv wceq vy cv vu cv wceq wa
      wi vy wal vx wal wph vx cv vv cv wceq vy cv vu cv wceq wa wi wph vy vw
      wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi wa vw wal vz wal vy
      wal vx wal wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv
      wceq wa wi vw wal vz wal vy wal vx wal wph vx cv vv cv wceq vy cv vu cv
      wceq wa wi vy wal vx wal wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy
      wal vx wal wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa
      wi vw wal vz wal wa wph vx cv vv cv wceq vy cv vu cv wceq wa wi wph vy vw
      wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi wa vw wal vz wal vy
      wal vx wal wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy wal vx wal wph
      vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vw wal vz wal
      wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy wal vx wal wph vy vw wsb
      vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vw wal vz wal wph vx cv
      vv cv wceq vy cv vu cv wceq wa wi wph vy vw wsb vx vz wsb vz cv vv cv
      wceq vw cv vu cv wceq wa wi vx vy vz vw wph vx cv vv cv wceq vy cv vu cv
      wceq wa wi vz nfv wph vx cv vv cv wceq vy cv vu cv wceq wa wi vw nfv wph
      vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa vx wph vy vw wsb
      vx vz nfs1v vz cv vv cv wceq vw cv vu cv wceq wa vx nfv nfim wph vy vw
      wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa vy wph vy vw wsb vx vz
      vy wph vy vw nfs1v nfsb vz cv vv cv wceq vw cv vu cv wceq wa vy nfv nfim
      vx cv vz cv wceq vy cv vw cv wceq wa wph wph vy vw wsb vx vz wsb vx cv vv
      cv wceq vy cv vu cv wceq wa vz cv vv cv wceq vw cv vu cv wceq wa vy cv vw
      cv wceq wph wph vy vw wsb vx cv vz cv wceq wph vy vw wsb vx vz wsb wph vy
      vw sbequ12 wph vy vw wsb vx vz sbequ12 sylan9bbr vx cv vz cv wceq vx cv
      vv cv wceq vz cv vv cv wceq vy cv vw cv wceq vy cv vu cv wceq vw cv vu cv
      wceq vx vz vv equequ1 vy vw vu equequ1 bi2anan9 imbi12d cbval2 biimpi
      ancli wph vx cv vv cv wceq vy cv vu cv wceq wa wi wph vy vw wsb vx vz wsb
      vz cv vv cv wceq vw cv vu cv wceq wa wi wa vw wal vz wal vy wal vx wal
      wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy wal wph vy vw wsb vx vz
      wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vw wal wa vz wal vx wal wph
      vx cv vv cv wceq vy cv vu cv wceq wa wi vy wal vx wal wph vy vw wsb vx vz
      wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vw wal vz wal wa wph vx cv vv
      cv wceq vy cv vu cv wceq wa wi wph vy vw wsb vx vz wsb vz cv vv cv wceq
      vw cv vu cv wceq wa wi wa vw wal vz wal vy wal wph vx cv vv cv wceq vy cv
      vu cv wceq wa wi vy wal wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu
      cv wceq wa wi vw wal wa vz wal vx wph vx cv vv cv wceq vy cv vu cv wceq
      wa wi wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi wa
      vw wal vz wal vy wal wph vx cv vv cv wceq vy cv vu cv wceq wa wi wph vy
      vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi wa vw wal vy wal
      vz wal wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy wal wph vy vw wsb
      vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vw wal wa vz wal wph vx
      cv vv cv wceq vy cv vu cv wceq wa wi wph vy vw wsb vx vz wsb vz cv vv cv
      wceq vw cv vu cv wceq wa wi wa vw wal vy vz alcom wph vx cv vv cv wceq vy
      cv vu cv wceq wa wi wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv
      wceq wa wi wa vw wal vy wal wph vx cv vv cv wceq vy cv vu cv wceq wa wi
      vy wal wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vw
      wal wa vz wph vx cv vv cv wceq vy cv vu cv wceq wa wi wph vy vw wsb vx vz
      wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vy vw wph vx cv vv cv wceq vy
      cv vu cv wceq wa wi vw nfv wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv
      vu cv wceq wa vy wph vy vw wsb vx vz vy wph vy vw nfs1v nfsb vz cv vv cv
      wceq vw cv vu cv wceq wa vy nfv nfim aaan albii bitri albii wph vx cv vv
      cv wceq vy cv vu cv wceq wa wi vy wal wph vy vw wsb vx vz wsb vz cv vv cv
      wceq vw cv vu cv wceq wa wi vw wal vx vz wph vx cv vv cv wceq vy cv vu cv
      wceq wa wi vy wal vz nfv wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv
      vu cv wceq wa wi vx vw wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu
      cv wceq wa vx wph vy vw wsb vx vz nfs1v vz cv vv cv wceq vw cv vu cv wceq
      wa vx nfv nfim nfal aaan bitri sylibr wph vx cv vv cv wceq vy cv vu cv
      wceq wa wi wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa
      wi wa vw wal vz wal wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv
      vw cv wceq wa wi vw wal vz wal vx vy wph vx cv vv cv wceq vy cv vu cv
      wceq wa wi wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa
      wi wa wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa
      wi vz vw wph vx cv vv cv wceq vy cv vu cv wceq wa wi wph vy vw wsb vx vz
      wsb vz cv vv cv wceq vw cv vu cv wceq wa wi wa wph wph vy vw wsb vx vz
      wsb wa vx cv vv cv wceq vy cv vu cv wceq wa vz cv vv cv wceq vw cv vu cv
      wceq wa wa vx cv vz cv wceq vy cv vw cv wceq wa wph vx cv vv cv wceq vy
      cv vu cv wceq wa wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv
      wceq wa prth vx cv vv cv wceq vz cv vv cv wceq vy cv vu cv wceq vw cv vu
      cv wceq vx cv vz cv wceq vy cv vw cv wceq wa vx cv vv cv wceq vz cv vv cv
      wceq wa vx cv vz cv wceq vy cv vu cv wceq vw cv vu cv wceq wa vy cv vw cv
      wceq vx vz vv equtr2 vy vw vu equtr2 anim12i an4s syl6 2alimi 2alimi syl
      exlimivv sylbir wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw
      cv wceq wa wi vw wal vz wal vy wal vx wal wph vy vw wsb vx vz wsb vw wex
      vz wex wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal vw wex
      vz wex wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq
      wa wi vw wal vz wal vy wal vx wal wph vy vw wsb vx vz wsb vw wex wph vx
      cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal vw wex wi vz wal wph
      vy vw wsb vx vz wsb vw wex vz wex wph vx cv vz cv wceq vy cv vw cv wceq
      wa wi vy wal vx wal vw wex vz wex wi wph wph vy vw wsb vx vz wsb wa vx cv
      vz cv wceq vy cv vw cv wceq wa wi vw wal vz wal vy wal vx wal wph wph vy
      vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal
      vw wal vz wal wph vy vw wsb vx vz wsb vw wex wph vx cv vz cv wceq vy cv
      vw cv wceq wa wi vy wal vx wal vw wex wi vz wal wph wph vy vw wsb vx vz
      wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi vx vy vz vw alrot4 wph wph
      vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx
      wal vw wal wph vy vw wsb vx vz wsb vw wex wph vx cv vz cv wceq vy cv vw
      cv wceq wa wi vy wal vx wal vw wex wi vz wph wph vy vw wsb vx vz wsb wa
      vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal vw wal wph vy vw
      wsb vx vz wsb wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal
      wi vw wal wph vy vw wsb vx vz wsb vw wex wph vx cv vz cv wceq vy cv vw cv
      wceq wa wi vy wal vx wal vw wex wi wph wph vy vw wsb vx vz wsb wa vx cv
      vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wph vy vw wsb vx vz wsb
      wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wi vw wph vy vw
      wsb vx vz wsb wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv
      wceq wa wi vy wal vx wal wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy
      wal vx wal wph vy vw wsb vx vz wsb wph wph vy vw wsb vx vz wsb wa vx cv
      vz cv wceq vy cv vw cv wceq wa wi vy wal wph vx cv vz cv wceq vy cv vw cv
      wceq wa wi vy wal vx wph vy vw wsb vx vz nfs1v wph vy vw wsb vx vz wsb
      wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi
      wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wph vy vw wsb vx vz vy wph
      vy vw nfs1v nfsb wph vy vw wsb vx vz wsb wph wph wph vy vw wsb vx vz wsb
      wa vx cv vz cv wceq vy cv vw cv wceq wa wph vy vw wsb vx vz wsb wph
      pm3.21 imim1d alimd alimd com12 alimi wph vy vw wsb vx vz wsb wph vx cv
      vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal vw exim syl alimi sylbi
      wph vy vw wsb vx vz wsb vw wex wph vx cv vz cv wceq vy cv vw cv wceq wa
      wi vy wal vx wal vw wex vz exim syl wph vy vw wsb vx vz wsb vw wex vz wex
      wn wph vy vw wsb vx vz wsb wn vw wal vz wal wph vx cv vz cv wceq vy cv vw
      cv wceq wa wi vy wal vx wal vw wex vz wex wph vy vw wsb vx vz wsb wn vw
      wal vz wal wph vy vw wsb vx vz wsb vw wex wn vz wal wph vy vw wsb vx vz
      wsb vw wex vz wex wn wph vy vw wsb vx vz wsb wn vw wal wph vy vw wsb vx
      vz wsb vw wex wn vz wph vy vw wsb vx vz wsb vw alnex albii wph vy vw wsb
      vx vz wsb vw wex vz alnex bitri wph vy vw wsb vx vz wsb wn vw wal vz wal
      wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wph vx cv vz cv
      wceq vy cv vw cv wceq wa wi vy wal vx wal vw wex vz wex wph vy vw wsb vx
      vz wsb wn vw wal vz wal wph wn vy wal vx wal wph vx cv vz cv wceq vy cv
      vw cv wceq wa wi vy wal vx wal wph wn wph vy vw wsb vx vz wsb wn vx vy vz
      vw wph wn vz nfv wph wn vw nfv wph vy vw wsb vx vz wsb vx wph vy vw wsb
      vx vz nfs1v nfn wph vy vw wsb vx vz wsb vy wph vy vw wsb vx vz vy wph vy
      vw nfs1v nfsb nfn vx cv vz cv wceq vy cv vw cv wceq wa wph wph vy vw wsb
      vx vz wsb vy cv vw cv wceq wph wph vy vw wsb vx cv vz cv wceq wph vy vw
      wsb vx vz wsb wph vy vw sbequ12 wph vy vw wsb vx vz sbequ12 sylan9bbr
      notbid cbval2 wph wn wph vx cv vz cv wceq vy cv vw cv wceq wa wi vx vy
      wph vx cv vz cv wceq vy cv vw cv wceq wa pm2.21 2alimi sylbir wph vx cv
      vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wph vx cv vz cv wceq vy
      cv vw cv wceq wa wi vy wal vx wal vw wex vz wex vw wph vx cv vz cv wceq
      vy cv vw cv wceq wa wi vy wal vx wal vw wex vz 19.8a 19.23bi syl sylbir
      pm2.61d1 impbii $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x y z w $.
    2mos.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Double "exists at most one", using implicit substitution.  (Contributed
       by NM, 10-Feb-2005.) $)
    2mos $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
             A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) ) $=
      wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal vw wex vz wex
      wph wph vy vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi vw
      wal vz wal vy wal vx wal wph wps wa vx cv vz cv wceq vy cv vw cv wceq wa
      wi vw wal vz wal vy wal vx wal wph vx vy vz vw 2mo wph wph vy vw wsb vx
      vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi vw wal vz wal wph wps
      wa vx cv vz cv wceq vy cv vw cv wceq wa wi vw wal vz wal vx vy wph wph vy
      vw wsb vx vz wsb wa vx cv vz cv wceq vy cv vw cv wceq wa wi wph wps wa vx
      cv vz cv wceq vy cv vw cv wceq wa wi vz vw wph wph vy vw wsb vx vz wsb wa
      wph wps wa vx cv vz cv wceq vy cv vw cv wceq wa wph vy vw wsb vx vz wsb
      wps wph wph vy vw wsb wps vx vz wps vx nfv vx cv vz cv wceq wph vy vw wsb
      wps vx cv vz cv wceq wph vy vw wsb wi vx cv vz cv wceq wph wi vy vw wsb
      vx cv vz cv wceq wps wi vx cv vz cv wceq wph vy vw vx cv vz cv wceq vy
      nfv sbrim vx cv vz cv wceq wph wi vx cv vz cv wceq wps wi vy vw vx cv vz
      cv wceq wps wi vy nfv vy cv vw cv wceq vx cv vz cv wceq wph wps vx cv vz
      cv wceq vy cv vw cv wceq wph wps wb 2mos.1 expcom pm5.74d sbie bitr3i
      pm5.74ri sbie anbi2i imbi1i 2albii 2albii bitri $.
  $}

  $( Double existential uniqueness.  This theorem shows a condition under which
     a "naive" definition matches the correct one.  (Contributed by NM,
     3-Dec-2001.) $)
  2eu1 $p |- ( A. x E* y ph ->
        ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    wph vy wmo vx wal wph vy weu vx weu wph vy wex vx weu wph vx wex vy weu wa
    wph vy weu vx weu wph vy wmo vx wal wph vy wex vx weu wph vx wex vy weu wa
    wph vy weu vx weu wph vy wmo vx wal wph vy wex vx wex wph vx wex vy wex wa
    wph vy wex vx wmo wph vx wex vy wmo wa wa wph vy wex vx weu wph vx wex vy
    weu wa wph vy weu vx weu wph vy wmo vx wal wph vy wex vx wmo wph vx wex vy
    wmo wa wph vy wex vx wex wph vx wex vy wex wa wph vy weu vx weu wph vy wex
    wph vy wmo wa vx wmo wph vy wmo vx wal wph vy wex vx wmo wph vx wex vy wmo
    wa wi wph vy weu vx weu wph vy wex wph vy wmo wa vx wex wph vy wex wph vy
    wmo wa vx wmo wph vy weu vx weu wph vy weu vx wex wph vy weu vx wmo wa wph
    vy wex wph vy wmo wa vx wex wph vy wex wph vy wmo wa vx wmo wa wph vy weu
    vx eu5 wph vy weu vx wex wph vy wex wph vy wmo wa vx wex wph vy weu vx wmo
    wph vy wex wph vy wmo wa vx wmo wph vy weu wph vy wex wph vy wmo wa vx wph
    vy eu5 exbii wph vy weu wph vy wex wph vy wmo wa vx wph vy eu5 mobii
    anbi12i bitri simprbi wph vy wex wph vy wmo wa vx wmo wph vy wmo vx wal wph
    vy wex vx wmo wph vy wmo vx wal wa wph vy wex vx wmo wph vx wex vy wmo wa
    wph vy wex wph vy wmo wa vx wmo wph vy wmo vx wal wph vy wex vx wmo wph vy
    wex wph vy wmo wa vx wmo wph vy wmo vx wal wph vy wex wa vx wmo wph vy wmo
    vx wal wph vy wex vx wmo wi wph vy wmo vx wal wph vy wex wa wph vy wex wph
    vy wmo wa vx wph vy wex wph vy wmo vx wal wph vy wex wph vy wmo wa wph vy
    wmo vx wal wph vy wmo wph vy wex wph vy wmo vx sp anim2i ancoms moimi wph
    vy wmo vx wal wph vy wex vx wph vy wmo vx nfa1 moanim sylib ancrd wph vy
    wex vx wmo wph vy wmo vx wal wph vx wex vy wmo wph vy wmo vx wal wph vy wex
    vx wmo wph vx wex vy wmo wph vx vy 2moswap com12 imdistani syl6 syl wph vy
    weu vx weu wph vy wex vx wex wph vx wex vy wex wph vx vy 2eu2ex wph vy weu
    vx weu wph vy wex vx wex wph vx wex vy wex wph vx vy 2eu2ex wph vx vy excom
    sylib jca jctild wph vy wex vx weu wph vx wex vy weu wa wph vy wex vx wex
    wph vy wex vx wmo wa wph vx wex vy wex wph vx wex vy wmo wa wa wph vy wex
    vx wex wph vx wex vy wex wa wph vy wex vx wmo wph vx wex vy wmo wa wa wph
    vy wex vx weu wph vy wex vx wex wph vy wex vx wmo wa wph vx wex vy weu wph
    vx wex vy wex wph vx wex vy wmo wa wph vy wex vx eu5 wph vx wex vy eu5
    anbi12i wph vy wex vx wex wph vy wex vx wmo wph vx wex vy wex wph vx wex vy
    wmo an4 bitri syl6ibr com12 wph vx vy 2exeu impbid1 $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu2 $p |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) ) $=
    wph vx wex vy weu wph vy weu vx weu wph vy wex vx weu wph vx wex vy weu wph
    vx wex vy wmo wph vy wmo vx wal wph vy weu vx weu wph vy wex vx weu wi wph
    vx wex vy eumo wph vy vx 2moex wph vy wmo vx wal wph vy weu vx weu wph vy
    wex vx weu wph vx wex vy weu wa wph vy wex vx weu wph vx vy 2eu1 wph vy wex
    vx weu wph vx wex vy weu simpl syl6bi 3syl wph vy wex vx weu wph vx wex vy
    weu wph vy weu vx weu wph vx vy 2exeu expcom impbid $.


  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu3 $p |- ( A. x A. y ( E* x ph \/ E* y ph ) ->
 ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    wph vx wmo wph vy wmo wo vy wal vx wal wph vx wmo vy wal wph vy wmo vx wal
    wo wph vy weu vx weu wph vx weu vy weu wa wph vy wex vx weu wph vx wex vy
    weu wa wb wph vx wmo wph vy wmo wo vy wal vx wal wph vx wmo vy wal wph vy
    wmo wo vx wal wph vx wmo vy wal wph vy wmo vx wal wo wph vx wmo wph vy wmo
    wo vy wal wph vx wmo vy wal wph vy wmo wo vx wph vx wmo wph vy wmo vy wph
    vy nfmo1 19.31 albii wph vx wmo vy wal wph vy wmo vx wph vx wmo vx vy wph
    vx nfmo1 nfal 19.32 bitri wph vx wmo vy wal wph vy wmo vx wal wo wph vy weu
    vx weu wph vx weu vy weu wa wph vy wex vx weu wph vx wex vy weu wa wph vx
    wmo vy wal wph vy weu vx weu wph vx weu vy weu wa wph vy wex vx weu wph vx
    wex vy weu wa wi wph vy wmo vx wal wph vx wmo vy wal wph vx weu vy weu wph
    vy wex vx weu wph vx wex vy weu wa wph vy weu vx weu wph vx wmo vy wal wph
    vx weu vy weu wph vx wex vy weu wph vy wex vx weu wa wph vy wex vx weu wph
    vx wex vy weu wa wph vx wmo vy wal wph vx weu vy weu wph vx wex vy weu wph
    vy wex vx weu wa wph vy vx 2eu1 biimpd wph vx wex vy weu wph vy wex vx weu
    ancom syl6ib adantld wph vy wmo vx wal wph vy weu vx weu wph vy wex vx weu
    wph vx wex vy weu wa wph vx weu vy weu wph vy wmo vx wal wph vy weu vx weu
    wph vy wex vx weu wph vx wex vy weu wa wph vx vy 2eu1 biimpd adantrd jaoi
    wph vy wex vx weu wph vx wex vy weu wa wph vy weu vx weu wph vx weu vy weu
    wph vx vy 2exeu wph vx wex vy weu wph vy wex vx weu wph vx weu vy weu wph
    vy vx 2exeu ancoms jca impbid1 sylbi $.

  ${
    $d x y z w $.  $d z w ph $.
    $( This theorem provides us with a definition of double existential
       uniqueness ("exactly one ` x ` and exactly one ` y ` ").  Naively one
       might think (incorrectly) that it could be defined by
       ` E! x E! y ph ` .  See ~ 2eu1 for a condition under which the naive
       definition holds and ~ 2exeu for a one-way implication.  See ~ 2eu5 and
       ~ 2eu8 for alternate definitions.  (Contributed by NM, 3-Dec-2001.) $)
    2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      wph vy wex vx weu wph vx wex vy weu wa wph vy wex vx wex wph vy wex vx cv
      vz cv wceq wi vx wal vz wex wa wph vx wex vy wex wph vx wex vy cv vw cv
      wceq wi vy wal vw wex wa wa wph vy wex vx wex wph vx wex vy wex wa wph vy
      wex vx cv vz cv wceq wi vx wal vz wex wph vx wex vy cv vw cv wceq wi vy
      wal vw wex wa wa wph vy wex vx wex wph vx cv vz cv wceq vy cv vw cv wceq
      wa wi vy wal vx wal vw wex vz wex wa wph vy wex vx weu wph vy wex vx wex
      wph vy wex vx cv vz cv wceq wi vx wal vz wex wa wph vx wex vy weu wph vx
      wex vy wex wph vx wex vy cv vw cv wceq wi vy wal vw wex wa wph vy wex vx
      vz wph vy wex vz nfv eu3 wph vx wex vy vw wph vx wex vw nfv eu3 anbi12i
      wph vy wex vx wex wph vy wex vx cv vz cv wceq wi vx wal vz wex wph vx wex
      vy wex wph vx wex vy cv vw cv wceq wi vy wal vw wex an4 wph vy wex vx wex
      wph vx wex vy wex wa wph vy wex vx wex wph vy wex vx cv vz cv wceq wi vx
      wal vz wex wph vx wex vy cv vw cv wceq wi vy wal vw wex wa wph vx cv vz
      cv wceq vy cv vw cv wceq wa wi vy wal vx wal vw wex vz wex wph vy wex vx
      wex wph vx wex vy wex wa wph vy wex vx wex wph vy wex vx wex wa wph vy
      wex vx wex wph vx wex vy wex wph vy wex vx wex wph vy wex vx wex wph vy
      vx excom anbi2i wph vy wex vx wex anidm bitri wph vx cv vz cv wceq vy cv
      vw cv wceq wa wi vy wal vx wal vw wex vz wex wph vy wex vx cv vz cv wceq
      wi vx wal wph vx wex vy cv vw cv wceq wi vy wal wa vw wex vz wex wph vy
      wex vx cv vz cv wceq wi vx wal vz wex wph vx wex vy cv vw cv wceq wi vy
      wal vw wex wa wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal
      wph vy wex vx cv vz cv wceq wi vx wal wph vx wex vy cv vw cv wceq wi vy
      wal wa vz vw wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal
      wph vx cv vz cv wceq wi vy wal wph vy cv vw cv wceq wi vx wal wa vy wal
      vx wal wph vy wex vx cv vz cv wceq wi wph vx wex vy cv vw cv wceq wi wa
      vy wal vx wal wph vy wex vx cv vz cv wceq wi vx wal wph vx wex vy cv vw
      cv wceq wi vy wal wa wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal
      vx wal wph vx cv vz cv wceq wi vy wal wph vy cv vw cv wceq wi vy wal vx
      wal wa vx wal wph vx cv vz cv wceq wi vy wal wph vy cv vw cv wceq wi vx
      wal wa vy wal vx wal wph vx cv vz cv wceq wi vy wal wph vy cv vw cv wceq
      wi vy wal vx wal wa vx wal wph vx cv vz cv wceq wi vy wal vx wal wph vy
      cv vw cv wceq wi vy wal vx wal vx wal wa wph vx cv vz cv wceq vy cv vw cv
      wceq wa wi vy wal vx wal wph vx cv vz cv wceq wi vy wal wph vy cv vw cv
      wceq wi vy wal vx wal vx 19.26 wph vx cv vz cv wceq wi vy wal vx wal wph
      vy cv vw cv wceq wi vy wal vx wal vx wal wa wph vx cv vz cv wceq wi vy
      wal vx wal wph vy cv vw cv wceq wi vy wal vx wal wa wph vx cv vz cv wceq
      vy cv vw cv wceq wa wi vy wal vx wal wph vy cv vw cv wceq wi vy wal vx
      wal vx wal wph vy cv vw cv wceq wi vy wal vx wal wph vx cv vz cv wceq wi
      vy wal vx wal wph vy cv vw cv wceq wi vy wal vx wal vx wph vy cv vw cv
      wceq wi vy wal vx nfa1 19.3 anbi2i wph vx cv vz cv wceq vy cv vw cv wceq
      wa wi vy wal vx wal wph vx cv vz cv wceq wi vy wal wph vy cv vw cv wceq
      wi vy wal wa vx wal wph vx cv vz cv wceq wi vy wal vx wal wph vy cv vw cv
      wceq wi vy wal vx wal wa wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy
      wal wph vx cv vz cv wceq wi vy wal wph vy cv vw cv wceq wi vy wal wa vx
      wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal wph vx cv vz cv wceq
      wi wph vy cv vw cv wceq wi wa vy wal wph vx cv vz cv wceq wi vy wal wph
      vy cv vw cv wceq wi vy wal wa wph vx cv vz cv wceq vy cv vw cv wceq wa wi
      wph vx cv vz cv wceq wi wph vy cv vw cv wceq wi wa vy wph vx cv vz cv
      wceq vy cv vw cv wceq jcab albii wph vx cv vz cv wceq wi wph vy cv vw cv
      wceq wi vy 19.26 bitri albii wph vx cv vz cv wceq wi vy wal wph vy cv vw
      cv wceq wi vy wal vx 19.26 bitri bitr4i bitr2i wph vx cv vz cv wceq wi vy
      wal wph vy cv vw cv wceq wi vx wal wa vy wal wph vx cv vz cv wceq wi vy
      wal wph vy cv vw cv wceq wi vy wal vx wal wa vx wph vx cv vz cv wceq wi
      vy wal wph vy cv vw cv wceq wi vx wal wa vy wal wph vx cv vz cv wceq wi
      vy wal vy wal wph vy cv vw cv wceq wi vx wal vy wal wa wph vx cv vz cv
      wceq wi vy wal wph vy cv vw cv wceq wi vy wal vx wal wa wph vx cv vz cv
      wceq wi vy wal wph vy cv vw cv wceq wi vx wal vy 19.26 wph vx cv vz cv
      wceq wi vy wal vy wal wph vx cv vz cv wceq wi vy wal wph vy cv vw cv wceq
      wi vx wal vy wal wph vy cv vw cv wceq wi vy wal vx wal wph vx cv vz cv
      wceq wi vy wal vy wph vx cv vz cv wceq wi vy nfa1 19.3 wph vy cv vw cv
      wceq wi vy vx alcom anbi12i bitri albii bitr4i wph vx cv vz cv wceq wi vy
      wal wph vy cv vw cv wceq wi vx wal wa wph vy wex vx cv vz cv wceq wi wph
      vx wex vy cv vw cv wceq wi wa vx vy wph vx cv vz cv wceq wi vy wal wph vy
      wex vx cv vz cv wceq wi wph vy cv vw cv wceq wi vx wal wph vx wex vy cv
      vw cv wceq wi wph vx cv vz cv wceq vy 19.23v wph vy cv vw cv wceq vx
      19.23v anbi12i 2albii wph vy wex vx cv vz cv wceq wi wph vx wex vy cv vw
      cv wceq wi vx vy wph vy wex vx cv vz cv wceq vy wph vy nfe1 vx cv vz cv
      wceq vy nfv nfim wph vx wex vy cv vw cv wceq vx wph vx nfe1 vy cv vw cv
      wceq vx nfv nfim aaan 3bitri 2exbii wph vy wex vx cv vz cv wceq wi vx wal
      wph vx wex vy cv vw cv wceq wi vy wal vz vw eeanv bitr2i anbi12i 3bitri
      $.

    $( An alternate definition of double existential uniqueness (see ~ 2eu4 ).
       A mistake sometimes made in the literature is to use ` E! x E! y ` to
       mean "exactly one ` x ` and exactly one ` y ` ."  (For example, see
       Proposition 7.53 of [TakeutiZaring] p. 53.)  It turns out that this is
       actually a weaker assertion, as can be seen by expanding out the formal
       definitions.  This theorem shows that the erroneous definition can be
       repaired by conjoining ` A. x E* y ph ` as an additional condition.  The
       correct definition apparently has never been published.  ( ` E* ` means
       "exists at most one.") (Contributed by NM, 26-Oct-2003.) $)
    2eu5 $p |- ( ( E! x E! y ph /\ A. x E* y ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      wph vy weu vx weu wph vy wmo vx wal wa wph vy wex vx weu wph vx wex vy
      weu wa wph vy wmo vx wal wa wph vy wex vx weu wph vx wex vy weu wa wph vy
      wex vx wex wph vx vz weq vy vw weq wa wi vy wal vx wal vw wex vz wex wa
      wph vy wmo vx wal wph vy weu vx weu wph vy wex vx weu wph vx wex vy weu
      wa wph vx vy 2eu1 pm5.32ri wph vy wex vx weu wph vx wex vy weu wa wph vy
      wmo vx wal wph vy wex vx weu wph vx wex vy weu wa wph vx wex vy wmo wph
      vy wmo vx wal wph vx wex vy weu wph vx wex vy wmo wph vy wex vx weu wph
      vx wex vy eumo adantl wph vy vx 2moex syl pm4.71i wph vx vy vz vw 2eu4
      3bitr2i $.
  $}

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Two equivalent expressions for double existential uniqueness.
       (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
    2eu6 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
               E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $=
      wph vy wex vx weu wph vx wex vy weu wa wph vy wex vx wex wph vx cv vz cv
      wceq vy cv vw cv wceq wa wi vy wal vx wal vw wex vz wex wa wph vx cv vz
      cv wceq vy cv vw cv wceq wa wb vy wal vx wal vw wex vz wex wph vx vy vz
      vw 2eu4 wph vy wex vx wex wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy
      wal vx wal vw wex vz wex wa wph vx cv vz cv wceq vy cv vw cv wceq wa wb
      vy wal vx wal vw wex vz wex wph vy wex vx wex wph vx cv vz cv wceq vy cv
      vw cv wceq wa wi vy wal vx wal vw wex vz wex wa wph vy vw wsb vx vz wsb
      wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb wa vz
      cv vv cv wceq vw cv vu cv wceq wa wi vu wal vv wal wa vw wex vz wex wph
      vx cv vz cv wceq vy cv vw cv wceq wa wb vy wal vx wal vw wex vz wex wph
      vy wex vx wex wph vy vw wsb vx vz wsb vw wex vz wex wph vy vw wsb vx vz
      wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv
      vu cv wceq wa wi vu wal vv wal vw wal vz wal wph vy vw wsb vx vz wsb wph
      vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb wa vz cv
      vv cv wceq vw cv vu cv wceq wa wi vu wal vv wal wa vw wex vz wex wph vx
      cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal vw wex vz wex wph wph
      vy vw wsb vx vz wsb vx vy vz vw wph vz nfv wph vw nfv wph vy vw wsb vx vz
      nfs1v wph vy vw wsb vx vz vy wph vy vw nfs1v nfsb vy cv vw cv wceq wph
      wph vy vw wsb vx cv vz cv wceq wph vy vw wsb vx vz wsb wph vy vw sbequ12
      wph vy vw wsb vx vz sbequ12 sylan9bbr cbvex2 wph vx cv vz cv wceq vy cv
      vw cv wceq wa wi vy wal vx wal vw wex vz wex wph vx cv vv cv wceq vy cv
      vu cv wceq wa wi vy wal vx wal vu wex vv wex wph vy vw wsb vx vz wsb wph
      vy vw wsb vx vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv
      wceq wa wi vu wal vv wal vw wal vz wal wph vx cv vz cv wceq vy cv vw cv
      wceq wa wi vy wal vx wal wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy
      wal vx wal vz vw vv vu vz cv vv cv wceq vw cv vu cv wceq wa wph vx cv vz
      cv wceq vy cv vw cv wceq wa wi wph vx cv vv cv wceq vy cv vu cv wceq wa
      wi vx vy vz cv vv cv wceq vw cv vu cv wceq wa vx cv vz cv wceq vy cv vw
      cv wceq wa vx cv vv cv wceq vy cv vu cv wceq wa wph vz cv vv cv wceq vx
      cv vz cv wceq vx cv vv cv wceq vw cv vu cv wceq vy cv vw cv wceq vy cv vu
      cv wceq vz vv vx equequ2 vw vu vy equequ2 bi2anan9 imbi2d 2albidv cbvex2v
      wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy wal vx wal vu wex vv wex
      wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vw wal vz
      wal vu wex vv wex wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu
      wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa wi vu wal vv wal vw
      wal vz wal wph vx cv vv cv wceq vy cv vu cv wceq wa wi vy wal vx wal wph
      vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa wi vw wal vz wal
      vv vu wph vx cv vv cv wceq vy cv vu cv wceq wa wi wph vy vw wsb vx vz wsb
      vz cv vv cv wceq vw cv vu cv wceq wa wi vx vy vz vw wph vx cv vv cv wceq
      vy cv vu cv wceq wa wi vz nfv wph vx cv vv cv wceq vy cv vu cv wceq wa wi
      vw nfv wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa vx
      wph vy vw wsb vx vz nfs1v vz cv vv cv wceq vw cv vu cv wceq wa vx nfv
      nfim wph vy vw wsb vx vz wsb vz cv vv cv wceq vw cv vu cv wceq wa vy wph
      vy vw wsb vx vz vy wph vy vw nfs1v nfsb vz cv vv cv wceq vw cv vu cv wceq
      wa vy nfv nfim vx cv vz cv wceq vy cv vw cv wceq wa wph wph vy vw wsb vx
      vz wsb vx cv vv cv wceq vy cv vu cv wceq wa vz cv vv cv wceq vw cv vu cv
      wceq wa vy cv vw cv wceq wph wph vy vw wsb vx cv vz cv wceq wph vy vw wsb
      vx vz wsb wph vy vw sbequ12 wph vy vw wsb vx vz sbequ12 sylan9bbr vx cv
      vz cv wceq vx cv vv cv wceq vz cv vv cv wceq vy cv vw cv wceq vy cv vu cv
      wceq vw cv vu cv wceq vx vz vv equequ1 vy vw vu equequ1 bi2anan9 imbi12d
      cbval2 2exbii wph vy vw wsb vx vz wsb vz vw vv vu 2mo bitri bitri wph vy
      vw wsb vx vz wsb wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu
      wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa wi vu wal vv wal vz
      vw 19.29r2 syl2anb wph vx cv vz cv wceq vy cv vw cv wceq wa wb vy wal vx
      wal vw wex vz wex vx cv vz cv wceq vy cv vw cv wceq wa wph wi vy wal vx
      wal wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wa vw wex
      vz wex wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb wph vy vw wsb vx
      vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa wi vu
      wal vv wal wa vw wex vz wex wph vx cv vz cv wceq vy cv vw cv wceq wa wb
      vy wal vx wal vx cv vz cv wceq vy cv vw cv wceq wa wph wi vy wal vx wal
      wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wa vz vw wph vx
      cv vz cv wceq vy cv vw cv wceq wa wb vy wal vx wal wph vx cv vz cv wceq
      vy cv vw cv wceq wa wi vy wal vx wal vx cv vz cv wceq vy cv vw cv wceq wa
      wph wi vy wal vx wal wa vx cv vz cv wceq vy cv vw cv wceq wa wph wi vy
      wal vx wal wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wa
      wph vx cv vz cv wceq vy cv vw cv wceq wa vx vy 2albiim wph vx cv vz cv
      wceq vy cv vw cv wceq wa wi vy wal vx wal vx cv vz cv wceq vy cv vw cv
      wceq wa wph wi vy wal vx wal ancom bitri 2exbii wph vy vw wsb vx vz wsb
      wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb wa vz
      cv vv cv wceq vw cv vu cv wceq wa wi vu wal vv wal wa vx cv vz cv wceq vy
      cv vw cv wceq wa wph wi vy wal vx wal wph vx cv vz cv wceq vy cv vw cv
      wceq wa wi vy wal vx wal wa vz vw wph vy vw wsb vx vz wsb wph vy vw wsb
      vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq
      vw cv vu cv wceq wa wi vu wal vv wal wa wph vy vw wsb vx vz wsb wph vx cv
      vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wa vx cv vz cv wceq vy cv
      vw cv wceq wa wph wi vy wal vx wal wph vx cv vz cv wceq vy cv vw cv wceq
      wa wi vy wal vx wal wa wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb
      wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv vu
      cv wceq wa wi vu wal vv wal wa wph vy vw wsb vx vz wsb wph vy vw wsb vx
      vz wsb wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wi wa
      wph vy vw wsb vx vz wsb wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy
      wal vx wal wa wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb
      vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa wi vu wal vv wal wph vy
      vw wsb vx vz wsb wph vx cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx
      wal wi wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb wph vy vw wsb vx
      vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa wi vu
      wal vv wal wph vy vw wsb vx vz wsb wph vx cv vz cv wceq vy cv vw cv wceq
      wa wi wi vy wal vx wal wph vy vw wsb vx vz wsb wph vx cv vz cv wceq vy cv
      vw cv wceq wa wi vy wal vx wal wi wph vy vw wsb vx vz wsb wph vy vw wsb
      vx vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa wi
      vu wal vv wal wph vy vw wsb vx vz wsb wph wa vz cv vx cv wceq vw cv vy cv
      wceq wa wi vy wal vx wal wph vy vw wsb vx vz wsb wph vx cv vz cv wceq vy
      cv vw cv wceq wa wi wi vy wal vx wal wph vy vw wsb vx vz wsb wph wa vz cv
      vx cv wceq vw cv vy cv wceq wa wi wph vy vw wsb vx vz wsb wph vy vw wsb
      vx vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa wi
      vx vy vv vu wph vy vw wsb vx vz wsb wph wa vz cv vx cv wceq vw cv vy cv
      wceq wa wi vv nfv wph vy vw wsb vx vz wsb wph wa vz cv vx cv wceq vw cv
      vy cv wceq wa wi vu nfv wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb
      vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa vx wph vy vw
      wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb vx wph vy vw
      wsb vx vz nfs1v wph vy vw wsb vx vz wsb vw vu wsb vz vv vx wph vy vw wsb
      vx vz wsb vw vu vx wph vy vw wsb vx vz nfs1v nfsb nfsb nfan vz cv vv cv
      wceq vw cv vu cv wceq wa vx nfv nfim wph vy vw wsb vx vz wsb wph vy vw
      wsb vx vz wsb vw vu wsb vz vv wsb wa vz cv vv cv wceq vw cv vu cv wceq wa
      vy wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb vy
      wph vy vw wsb vx vz vy wph vy vw nfs1v nfsb wph vy vw wsb vx vz wsb vw vu
      wsb vz vv vy wph vy vw wsb vx vz wsb vw vu vy wph vy vw wsb vx vz vy wph
      vy vw nfs1v nfsb nfsb nfsb nfan vz cv vv cv wceq vw cv vu cv wceq wa vy
      nfv nfim vx cv vv cv wceq vy cv vu cv wceq wa wph vy vw wsb vx vz wsb wph
      wa wph vy vw wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb wa
      vz cv vx cv wceq vw cv vy cv wceq wa vz cv vv cv wceq vw cv vu cv wceq wa
      vx cv vv cv wceq vy cv vu cv wceq wa wph wph vy vw wsb vx vz wsb vw vu
      wsb vz vv wsb wph vy vw wsb vx vz wsb vx cv vv cv wceq vy cv vu cv wceq
      wa wph wph vy vu wsb vx vv wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv
      wsb vy cv vu cv wceq wph wph vy vu wsb vx cv vv cv wceq wph vy vu wsb vx
      vv wsb wph vy vu sbequ12 wph vy vu wsb vx vv sbequ12 sylan9bbr wph vy vu
      wsb vx vv wsb wph vy vw wsb vw vu wsb vx vv wsb wph vy vw wsb vx vz wsb
      vw vu wsb vz vv wsb wph vy vw wsb vw vu wsb wph vy vu wsb vx vv wph vy vu
      vw wph vw nfv sbco2 sbbii wph vy vw wsb vw vu wsb vx vv wsb wph vy vw wsb
      vw vu wsb vx vz wsb vz vv wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wsb
      wph vy vw wsb vw vu wsb vx vv vz wph vy vw wsb vw vu wsb vz nfv sbco2 wph
      vy vw wsb vw vu wsb vx vz wsb wph vy vw wsb vx vz wsb vw vu wsb vz vv wph
      vy vw wsb vw vu vx vz sbcom2 sbbii bitr3i bitr3i syl6bb anbi2d vx cv vv
      cv wceq vz cv vx cv wceq vz cv vv cv wceq vy cv vu cv wceq vw cv vy cv
      wceq vw cv vu cv wceq vx vv vz equequ2 vy vu vw equequ2 bi2anan9 imbi12d
      cbval2 wph vy vw wsb vx vz wsb wph wa vz cv vx cv wceq vw cv vy cv wceq
      wa wi wph vy vw wsb vx vz wsb wph vx cv vz cv wceq vy cv vw cv wceq wa wi
      wi vx vy wph vy vw wsb vx vz wsb wph wa vz cv vx cv wceq vw cv vy cv wceq
      wa wi wph vy vw wsb vx vz wsb wph wa vx cv vz cv wceq vy cv vw cv wceq wa
      wi wph vy vw wsb vx vz wsb wph vx cv vz cv wceq vy cv vw cv wceq wa wi wi
      vz cv vx cv wceq vw cv vy cv wceq wa vx cv vz cv wceq vy cv vw cv wceq wa
      wph vy vw wsb vx vz wsb wph wa vz cv vx cv wceq vx cv vz cv wceq vw cv vy
      cv wceq vy cv vw cv wceq vz vx equcom vw vy equcom anbi12i imbi2i wph vy
      vw wsb vx vz wsb wph vx cv vz cv wceq vy cv vw cv wceq wa impexp bitri
      2albii bitr3i wph vy vw wsb vx vz wsb wph vx cv vz cv wceq vy cv vw cv
      wceq wa wi vx vy wph vy vw wsb vx vz nfs1v wph vy vw wsb vx vz vy wph vy
      vw nfs1v nfsb 19.21-2 bitri anbi2i wph vy vw wsb vx vz wsb wph vx cv vz
      cv wceq vy cv vw cv wceq wa wi vy wal vx wal abai bitr4i wph vy vw wsb vx
      vz wsb vx cv vz cv wceq vy cv vw cv wceq wa wph wi vy wal vx wal wph vx
      cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal wph vx vy vz vw 2sb6
      anbi1i bitri 2exbii bitr4i sylibr wph vx cv vz cv wceq vy cv vw cv wceq
      wa wb vy wal vx wal vw wex vz wex wph vy wex vx wex wph vx cv vz cv wceq
      vy cv vw cv wceq wa wi vy wal vx wal vw wex vz wex wph vx cv vz cv wceq
      vy cv vw cv wceq wa wb vy wal vx wal vw wex vz wex vx cv vz cv wceq vy cv
      vw cv wceq wa wph wi vy wal vx wal vw wex vz wex wph vy wex vx wex wph vx
      cv vz cv wceq vy cv vw cv wceq wa wb vy wal vx wal vx cv vz cv wceq vy cv
      vw cv wceq wa wph wi vy wal vx wal vz vw wph vx cv vz cv wceq vy cv vw cv
      wceq wa wb vx cv vz cv wceq vy cv vw cv wceq wa wph wi vx vy wph vx cv vz
      cv wceq vy cv vw cv wceq wa bi2 2alimi 2eximi wph vx vy vz vw 2exsb
      sylibr wph vx cv vz cv wceq vy cv vw cv wceq wa wb vy wal vx wal wph vx
      cv vz cv wceq vy cv vw cv wceq wa wi vy wal vx wal vz vw wph vx cv vz cv
      wceq vy cv vw cv wceq wa wb wph vx cv vz cv wceq vy cv vw cv wceq wa wi
      vx vy wph vx cv vz cv wceq vy cv vw cv wceq wa bi1 2alimi 2eximi jca
      impbii bitri $.
  $}

  $( Two equivalent expressions for double existential uniqueness.
     (Contributed by NM, 19-Feb-2005.) $)
  2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
             E! x E! y ( E. x ph /\ E. y ph ) ) $=
    wph vx wex vy weu wph vy wex wa vx weu wph vx wex vy weu wph vy wex vx weu
    wa wph vx wex wph vy wex wa vy weu vx weu wph vy wex vx weu wph vx wex vy
    weu wa wph vx wex vy weu wph vy wex vx wph vx wex vx vy wph vx nfe1 nfeu
    euan wph vx wex wph vy wex wa vy weu wph vx wex vy weu wph vy wex wa vx wph
    vx wex wph vy wex wa vy weu wph vy wex wph vx wex wa vy weu wph vy wex wph
    vx wex vy weu wa wph vx wex vy weu wph vy wex wa wph vx wex wph vy wex wa
    wph vy wex wph vx wex wa vy wph vx wex wph vy wex ancom eubii wph vy wex
    wph vx wex vy wph vy nfe1 euan wph vy wex wph vx wex vy weu ancom 3bitri
    eubii wph vy wex vx weu wph vx wex vy weu ancom 3bitr4ri $.

  $( Two equivalent expressions for double existential uniqueness.  Curiously,
     we can put ` E! ` on either of the internal conjuncts but not both.  We
     can also commute ` E! x E! y ` using ~ 2eu7 .  (Contributed by NM,
     20-Feb-2005.) $)
  2eu8 $p |- ( E! x E! y ( E. x ph /\ E. y ph ) <->
                E! x E! y ( E! x ph /\ E. y ph ) ) $=
    wph vy wex vx weu wph vx weu vy weu wa wph vy wex vx weu wph vx wex vy weu
    wa wph vx weu wph vy wex wa vy weu vx weu wph vx wex wph vy wex wa vy weu
    vx weu wph vy wex vx weu wph vx weu vy weu wph vx wex vy weu wph vy vx 2eu2
    pm5.32i wph vx weu vy weu wph vy wex wa vx weu wph vx weu vy weu wph vy wex
    vx weu wa wph vx weu wph vy wex wa vy weu vx weu wph vy wex vx weu wph vx
    weu vy weu wa wph vx weu vy weu wph vy wex vx wph vx weu vx vy wph vx nfeu1
    nfeu euan wph vx weu wph vy wex wa vy weu wph vx weu vy weu wph vy wex wa
    vx wph vx weu wph vy wex wa vy weu wph vy wex wph vx weu wa vy weu wph vy
    wex wph vx weu vy weu wa wph vx weu vy weu wph vy wex wa wph vx weu wph vy
    wex wa wph vy wex wph vx weu wa vy wph vx weu wph vy wex ancom eubii wph vy
    wex wph vx weu vy wph vy nfe1 euan wph vy wex wph vx weu vy weu ancom
    3bitri eubii wph vy wex vx weu wph vx weu vy weu ancom 3bitr4ri wph vx vy
    2eu7 3bitr3ri $.

  ${
    $d x y z $.
    $( Equality has existential uniqueness.  Special case of ~ eueq1 proved
       using only predicate calculus.  (Contributed by Stefan Allan,
       4-Dec-2008.) $)
    euequ1 $p |- E! x x = y $=
      vx vy weq vx weu vx vy weq vx wex vx vy weq vz vy weq wa vx vz weq wi vz
      wal vx wal vx vy a9ev vx vy weq vz vy weq wa vx vz weq wi vx vz vx vz vy
      equtr2 gen2 vx vy weq vz vy weq vx vz vx vz vy equequ1 eu4 mpbir2an $.
  $}

  ${
    $d x y $.
    $( Two ways to express "only one thing exists."  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory; see theorem ~ dtru .  (Contributed by NM, 5-Apr-2004.) $)
    exists1 $p |- ( E! x x = x <-> A. x x = y ) $=
      vx cv vx cv wceq vx weu vx cv vx cv wceq vx cv vy cv wceq wb vx wal vy
      wex vx cv vy cv wceq vx wal vy wex vx cv vy cv wceq vx wal vx cv vx cv
      wceq vx vy df-eu vx cv vy cv wceq vx wal vx cv vx cv wceq vx cv vy cv
      wceq wb vx wal vy vx cv vy cv wceq vx cv vx cv wceq vx cv vy cv wceq wb
      vx vx cv vy cv wceq vx cv vy cv wceq vx cv vx cv wceq wb vx cv vx cv wceq
      vx cv vy cv wceq wb vx cv vx cv wceq vx cv vy cv wceq vx equid tbt vx cv
      vy cv wceq vx cv vx cv wceq bicom bitri albii exbii vx cv vy cv wceq vx
      wal vy vx vy vy nfae 19.9 3bitr2i $.

    $( A condition implying that at least two things exist.  (Contributed by
       NM, 10-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $=
      wph vx wex wph wn vx wex vx cv vx cv wceq vx weu wn wph vx wex vx cv vx
      cv wceq vx weu wph wn vx wex wph vx wex vx cv vx cv wceq vx weu wph vx
      wal wph wn vx wex wn vx cv vx cv wceq vx weu wph vx wex wph vx wal vx cv
      vx cv wceq vx weu wph wph vx wal vx vx cv vx cv wceq vx nfeu1 wph vx nfa1
      vx cv vx cv wceq vx weu vx cv vy cv wceq vx wal wph wph vx wal wi vx vy
      exists1 wph vx vy ax16 sylbi exlimd com12 wph vx alex syl6ib con2d imp $.
  $}


