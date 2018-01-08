
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-5_(Quantified_Implication).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-17 (Distinctness) - first use of $d

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    $( Axiom of Distinctness.  This axiom quantifies a variable over a formula
       in which it does not occur.  Axiom C5 in [Megill] p. 444 (p. 11 of the
       preprint).  Also appears as Axiom B6 (p. 75) of system S2 of [Tarski]
       p. 77 and Axiom C5-1 of [Monk2] p. 113.

       (See comments in ~ ax17o about the logical redundancy of ~ ax-17 in the
       presence of our obsolete axioms.)

       This axiom essentially says that if ` x ` does not occur in ` ph ` ,
       i.e. ` ph ` does not depend on ` x ` in any way, then we can add the
       quantifier ` A. x ` to ` ph ` with no further assumptions.  By ~ sp , we
       can also remove the quantifier (unconditionally).  (Contributed by NM,
       5-Aug-1993.) $)
    ax-17 $a |- ( ph -> A. x ph ) $.
  $}

  ${
    $d x ps $.
    $( ~ ax-17 with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders.  (Contributed by NM, 1-Mar-2013.) $)
    a17d $p |- ( ph -> ( ps -> A. x ps ) ) $=
      wps wps vx wal wi wph wps vx ax-17 a1i $.
  $}

  ${
    $d x ph $.
    $( If ` x ` is not present in ` ph ` , then ` x ` is not free in ` ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfv $p |- F/ x ph $=
      wph vx wph vx ax-17 nfi $.
  $}

  ${
    $d x ps $.
    $( ~ nfv with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders such as ~ nfimd .  (Contributed by
       Mario Carneiro, 6-Oct-2016.) $)
    nfvd $p |- ( ph -> F/ x ps ) $=
      wps vx wnf wph wps vx nfv a1i $.
  $}

  ${
    $d x ph $.
    alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM,
       3-Apr-1994.) $)
    alimdv $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      wph wps wch vx wph vx ax-17 alimdv.1 alimdh $.

    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-1994.) $)
    eximdv $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      wph wps wch vx wph vx ax-17 alimdv.1 eximdh $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-2004.) $)
    2alimdv $p |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) ) $=
      wph wps vy wal wch vy wal vx wph wps wch vy 2alimdv.1 alimdv alimdv $.

    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       3-Aug-1995.) $)
    2eximdv $p |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) ) $=
      wph wps vy wex wch vy wex vx wph wps wch vy 2alimdv.1 eximdv eximdv $.
  $}

  ${
    $d x ph $.
    albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
    albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      wph wps wch vx wph vx ax-17 albidv.1 albidh $.

    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
    exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      wph wps wch vx wph vx ax-17 albidv.1 exbidh $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 2 universal quantifiers (deduction rule).
       (Contributed by NM, 4-Mar-1997.) $)
    2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $=
      wph wps vy wal wch vy wal vx wph wps wch vy 2albidv.1 albidv albidv $.

    $( Formula-building rule for 2 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)
    2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $=
      wph wps vy wex wch vy wex vx wph wps wch vy 2albidv.1 exbidv exbidv $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    3exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 3 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)
    3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $=
      wph wps vz wex wch vz wex vx vy wph wps wch vz 3exbidv.1 exbidv 2exbidv
      $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.  $d w ph $.
    4exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 4 existential quantifiers (deduction rule).
       (Contributed by NM, 3-Aug-1995.) $)
    4exbidv $p |- ( ph ->
                     ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $=
      wph wps vw wex vz wex wch vw wex vz wex vx vy wph wps wch vz vw 4exbidv.1
      2exbidv 2exbidv $.
  $}

  ${
    $d x ph $.
    alrimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    alrimiv $p |- ( ph -> A. x ps ) $=
      wph wps vx wph vx ax-17 alrimiv.1 alrimih $.
  $}

  ${
    $d x ph $.  $d y ph $.
    alrimivv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       31-Jul-1995.) $)
    alrimivv $p |- ( ph -> A. x A. y ps ) $=
      wph wps vy wal vx wph wps vy alrimivv.1 alrimiv alrimiv $.
  $}

  ${
    $d x ph $.  $d x ps $.
    alrimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       10-Feb-1997.) $)
    alrimdv $p |- ( ph -> ( ps -> A. x ch ) ) $=
      wph wps wch vx wph vx ax-17 wps vx ax-17 alrimdv.1 alrimdh $.
  $}

  ${
    $d x ph $.
    nfdv.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Apply the definition of not-free in a context.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfdv $p |- ( ph -> F/ x ps ) $=
      wph wps wps vx wal wi vx wal wps vx wnf wph wps wps vx wal wi vx nfdv.1
      alrimiv wps vx df-nf sylibr $.
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Quantification of two variables over a formula in which they do not
       occur.  (Contributed by Alan Sare, 12-Apr-2011.) $)
    2ax17 $p |- ( ph -> A. x A. y ph ) $=
      wph wph vx vy wph id alrimivv $.
  $}


