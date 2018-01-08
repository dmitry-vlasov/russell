
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-9_(Existence).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Axiom scheme ax-8 (Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  This is similar to, but not quite, a
     transitive law for equality (proved later as ~ equtr ).  This axiom scheme
     is a sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom C7 of [Monk2] p. 105 and Axiom Scheme C8' in [Megill] p. 448 (p. 16
     of the preprint).

     The equality symbol was invented in 1527 by Robert Recorde.  He chose a
     pair of parallel lines of the same length because "noe .2. thynges, can be
     moare equalle."

     Note that this axiom is still valid even when any two or all three of
     ` x ` , ` y ` , and ` z ` are replaced with the same variable since they
     do not have any distinct variable (Metamath's $d) restrictions.  Because
     of this, we say that these three variables are "bundled" (a term coined by
     Raph Levien).  (Contributed by NM, 5-Aug-1993.) $)
  ax-8 $a |- ( x = y -> ( x = z -> y = z ) ) $.

  ${
    $d x y $.
    $( Identity law for equality.  Lemma 2 of [KalishMontague] p. 85.  See also
       Lemma 6 of [Tarski] p. 68.  (Contributed by NM, 1-Apr-2005.)  (Revised
       by NM, 9-Apr-2017.) $)
    equid $p |- x = x $=
      vx vx weq vx vx weq wn vy wal vx vx weq wn vy wal vy vx weq wn vy wal vy
      vx ax9v vx vx weq wn vy vx weq wn vy vy vx weq vx vx weq vy vx weq vx vx
      weq vy vx vx ax-8 pm2.43i con3i alimi mto vx vx weq wn vy ax-17 mt3 $.
  $}

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (Contributed by NM,
     13-Jan-2011.)  (Revised by NM, 21-Aug-2017.) $)
  nfequid $p |- F/ y x = x $=
    vx vx weq vy vx equid nfth $.

  ${
    $d x w $.
    $( Commutative law for equality.  Lemma 3 of [KalishMontague] p. 85.  See
       also Lemma 7 of [Tarski] p. 69.  (Contributed by NM, 5-Aug-1993.)
       (Revised by NM, 9-Apr-2017.) $)
    equcomi $p |- ( x = y -> y = x ) $=
      vx vy weq vx vx weq vy vx weq vx equid vx vy vx ax-8 mpi $.
  $}

  $( Commutative law for equality.  (Contributed by NM, 20-Aug-1993.) $)
  equcom $p |- ( x = y <-> y = x ) $=
    vx vy weq vy vx weq vx vy equcomi vy vx equcomi impbii $.

  ${
    equcoms.1 $e |- ( x = y -> ph ) $.
    $( An inference commuting equality in antecedent.  Used to eliminate the
       need for a syllogism.  (Contributed by NM, 5-Aug-1993.) $)
    equcoms $p |- ( y = x -> ph ) $=
      vy vx weq vx vy weq wph vy vx equcomi equcoms.1 syl $.
  $}

  $( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2017.) $)
  equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    vx vy weq vx vz weq vy vz weq vx vy vz ax-8 vy vz weq vx vz weq wi vy vx vy
    vx vz ax-8 equcoms impbid $.

  $( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  equequ1OLD $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    vx vy weq vx vz weq vy vz weq vx vy vz ax-8 vx vy weq vy vx weq vy vz weq
    vx vz weq wi vx vy equcomi vy vx vz ax-8 syl impbid $.

  $( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 4-Aug-2017.) $)
  equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
    vx vy weq vx vz weq vy vz weq vz vx weq vz vy weq vx vy vz equequ1 vx vz
    equcom vy vz equcom 3bitr3g $.

  $( One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain).  (Contributed by NM, 16-Feb-2005.) $)
  stdpc6 $p |- A. x x = x $=
    vx vx weq vx vx equid ax-gen $.

  $( A transitive law for equality.  (Contributed by NM, 23-Aug-1993.) $)
  equtr $p |- ( x = y -> ( y = z -> x = z ) ) $=
    vy vz weq vx vz weq wi vy vx vy vx vz ax-8 equcoms $.

  $( A transitive law for equality.  Lemma L17 in [Megill] p. 446 (p. 14 of the
     preprint).  (Contributed by NM, 23-Aug-1993.) $)
  equtrr $p |- ( x = y -> ( z = x -> z = y ) ) $=
    vz vx weq vx vy weq vz vy weq vz vx vy equtr com12 $.

  $( A transitive law for equality.  (Contributed by NM, 12-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $=
    vy vz weq vx vz weq vx vy weq vx vz weq vx vy weq wi vz vy vz vy vx equtrr
    equcoms impcom $.

  $( Two equivalent ways of expressing ~ ax-12 .  See the comment for
     ~ ax-12 .  (Contributed by NM, 2-May-2017.)  (Proof shortened by Wolf
     Lammen, 12-Aug-2017.) $)
  ax12b $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) )
     <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $=
    vx vy weq wn vy vz weq vy vz weq vx wal wi wi vx vy weq wn vx vz weq wn vy
    vz weq vy vz weq vx wal wi wi wi vx vy weq wn vy vz weq vy vz weq vx wal wi
    wi vx vy weq wn vy vz weq vy vz weq vx wal wi vx vz weq wn vx vy weq wn vy
    vz weq vy vz weq vx wal wi wi id a1dd vx vy weq wn vy vz weq vx vy weq wn
    vx vz weq wn vy vz weq vy vz weq vx wal wi wi wi vy vz weq vx wal vx vy weq
    wn vy vz weq vx vz weq wn vx vy weq wn vx vz weq wn vy vz weq vy vz weq vx
    wal wi wi wi vy vz weq vx wal wi vy vz weq vx vz weq vx vy weq vx vz weq vx
    vy weq wi vz vy vz vy vx equtrr equcoms con3rr3 vx vy weq wn vx vz weq wn
    vy vz weq vx vy weq wn vx vz weq wn vy vz weq vy vz weq vx wal wi wi wi vy
    vz weq vx wal wi vx vy weq wn vx vz weq wn vy vz weq vy vz weq vx wal wi wi
    wi vx vy weq wn vx vz weq wn vy vz weq vy vz weq vx wal vx vy weq wn vx vz
    weq wn vy vz weq vy vz weq vx wal wi wi wi id com4l com23 mpdd com3r impbii
    $.

  $( Obsolete version of ~ ax12b as of 12-Aug-2017.  (Contributed by NM,
     2-May-2017.)  (New usage is discouraged.) $)
  ax12bOLD $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) )
     <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $=
    vx vy weq wn vy vz weq vy vz weq vx wal wi wi vx vy weq wn vx vz weq wn wa
    vy vz weq vy vz weq vx wal wi wi vx vy weq wn vx vz weq wn vy vz weq vy vz
    weq vx wal wi wi wi vx vy weq wn vy vz weq vy vz weq vx wal wi wi vy vz weq
    vx vy weq wn vx vz weq wn wa vy vz weq vx wal wi wi vx vy weq wn vx vz weq
    wn wa vy vz weq vy vz weq vx wal wi wi vx vy weq wn vy vz weq vy vz weq vx
    wal wi wi vy vz weq vx vy weq wn vy vz weq vx wal wi wi vy vz weq vx vy weq
    wn vx vz weq wn wa vy vz weq vx wal wi wi vx vy weq wn vy vz weq vy vz weq
    vx wal bi2.04 vy vz weq vx vy weq wn vy vz weq vx wal wi vx vy weq wn vx vz
    weq wn wa vy vz weq vx wal wi vy vz weq vx vy weq wn vx vy weq wn vx vz weq
    wn wa vy vz weq vx wal vy vz weq vx vy weq wn vx vz weq wn vy vz weq vx vz
    weq vx vy weq vx vz weq vx vy weq wi vz vy vz vy vx equtrr equcoms con3d
    pm4.71d imbi1d pm5.74i bitri vy vz weq vx vy weq wn vx vz weq wn wa vy vz
    weq vx wal bi2.04 bitri vx vy weq wn vx vz weq wn vy vz weq vy vz weq vx
    wal wi impexp bitri $.

  ${
    $d x y $.
    spfw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spfw.2 $e |- ( A. x ph -> A. y A. x ph ) $.
    spfw.3 $e |- ( -. ph -> A. y -. ph ) $.
    spfw.4 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Lemma 9
       of [KalishMontague] p. 87.  This may be the best we can do with minimal
       distinct variable conditions.  TO DO:  Do we need this theorem?  If not,
       maybe it should be deleted.  (Contributed by NM, 19-Apr-2017.) $)
    spfw $p |- ( A. x ph -> ph ) $=
      wph vx wal wps wi wph vx wal wph wi vy wph vx wal wph vx wal vy wal wph
      vx wal wps wi vy wal wps vy wal wph spfw.2 wph vx wal wps vy ax-5 wps wph
      vy vx spfw.3 wps wph wi vx vy vx vy weq wph wps spfw.4 biimprd equcoms
      spimw syl56 wph wps vx vy spfw.1 vx vy weq wph wps spfw.4 biimpd spimw
      mpg $.
  $}

  ${
    $d x y $.  $d y ph $.
    spnfw.3 $e |- ( -. ph -> A. x -. ph ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Obsolete
       version of ~ spnfw as of 13-Aug-2017.  (Contributed by NM, 1-Aug-2017.)
       (New usage is discouraged.) $)
    spnfwOLD $p |- ( A. x ph -> ph ) $=
      wph wph vx vy spnfw.3 wph vx wal vy ax-17 wph wn vy ax-17 vx vy weq wph
      biidd spfw $.
  $}

  ${
    19.8w.1 $e |- ( ph -> A. x ph ) $.
    $( Weak version of ~ 19.8a .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.) $)
    19.8w $p |- ( ph -> E. x ph ) $=
      wph wph wn vx wal wn wph vx wex wph wn vx wal wph wph wn vx wph wph vx
      wal wph wn wn wph wn wn vx wal 19.8w.1 wph notnot wph wph wn wn vx wph
      notnot albii 3imtr3i spnfw con2i wph vx df-ex sylibr $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    spw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of specialization scheme ~ sp .  Lemma 9 of
       [KalishMontague] p. 87.  While it appears that ~ sp in its general form
       does not follow from Tarski's FOL axiom schemes, from this theorem we
       can prove any instance of ~ sp having no wff metavariables and mutually
       distinct set variables (see ~ ax11wdemo for an example of the procedure
       to eliminate the hypothesis).  Other approximations of ~ sp are ~ spfw
       (minimal distinct variable requirements), ~ spnfw (when ` x ` is not
       free in ` -. ph ` ), ~ spvw (when ` x ` does not appear in ` ph ` ),
       ~ sptruw (when ` ph ` is true), and ~ spfalw (when ` ph ` is false).
       (Contributed by NM, 9-Apr-2017.) $)
    spw $p |- ( A. x ph -> ph ) $=
      wph vx wal wps wi wph vx wal wph wi vy wph vx wal wph vx wal vy wal wph
      vx wal wps wi vy wal wps vy wal wph wph vx wal vy ax-17 wph vx wal wps vy
      ax-5 wps wph vy vx wps wph wi vx vy vx vy weq wph wps spw.1 biimprd
      equcoms spimvw syl56 wph wps vx vy vx vy weq wph wps spw.1 biimpd spimvw
      mpg $.
  $}

  ${
    $d x y ph $.
    $( Version of ~ sp when ` x ` does not occur in ` ph ` .  This provides the
       other direction of ~ ax-17 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.) $)
    spvw $p |- ( A. x ph -> ph ) $=
      wph wph vx vy vx vy weq wph biidd spw $.

    $( Special case of Theorem 19.3 of [Margaris] p. 89.  (Contributed by NM,
       1-Aug-2017.) $)
    19.3v $p |- ( A. x ph <-> ph ) $=
      wph vx wal wph wph vx spvw wph vx ax-17 impbii $.

    $( Special case of Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       28-May-1995.)  (Revised by NM, 1-Aug-2017.) $)
    19.9v $p |- ( E. x ph <-> ph ) $=
      wph vx wex wph wn vx wal wn wph wph vx df-ex wph wn vx wal wph wph wn vx
      19.3v con2bii bitr4i $.
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-1994.) $)
    exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $=
      wph wps vx wex wch vx wex wch wph wps wch vx exlimdv.1 eximdv wch vx
      19.9v syl6ib $.
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimddv.1 $e |- ( ph -> E. x ps ) $.
    exlimddv.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 15-Jun-2016.) $)
    exlimddv $p |- ( ph -> ch ) $=
      wph wps vx wex wch exlimddv.1 wph wps wch vx wph wps wch exlimddv.2 ex
      exlimdv mpd $.
  $}

  ${
    $d x ps $.
    exlimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.

       This inference, along with our many variants such as ~ rexlimdv , is
       used to implement a metatheorem called "Rule C" that is given in many
       logic textbooks.  See, for example, Rule C in [Mendelson] p. 81, Rule C
       in [Margaris] p. 40, or Rule C in Hirst and Hirst's _A Primer for Logic
       and Proof_ p. 59 (PDF p. 65) at
       ~ http://www.mathsci.appstate.edu/~~hirstjl/primer/hirst.pdf .

       In informal proofs, the statement "Let ` C ` be an element such that..."
       almost always means an implicit application of Rule C.

       In essence, Rule C states that if we can prove that some element ` x `
       exists satisfying a wff, i.e. ` E. x ph ( x ) ` where ` ph ( x ) ` has
       ` x ` free, then we can use ` ph ( C ) ` as a hypothesis for the proof
       where ` C ` is a new (ficticious) constant not appearing previously in
       the proof, nor in any axioms used, nor in the theorem to be proved.  The
       purpose of Rule C is to get rid of the existential quantifier.

       We cannot do this in Metamath directly.  Instead, we use the original
       ` ph ` (containing ` x ` ) as an antecedent for the main part of the
       proof.  We eventually arrive at ` ( ph -> ps ) ` where ` ps ` is the
       theorem to be proved and does not contain ` x ` .  Then we apply
       ~ exlimiv to arrive at ` ( E. x ph -> ps ) ` .  Finally, we separately
       prove ` E. x ph ` and detach it with modus ponens ~ ax-mp to arrive at
       the final theorem ` ps ` .  (Contributed by NM, 5-Aug-1993.) $)
    exlimiv $p |- ( E. x ph -> ps ) $=
      wph vx wex wps vx wex wps wph wps vx exlimiv.1 eximi wps vx 19.9v sylib
      $.
  $}

  ${
    $d x ps $.  $d y ps $.
    exlimivv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       1-Aug-1995.) $)
    exlimivv $p |- ( E. x E. y ph -> ps ) $=
      wph vy wex wps vx wph wps vy exlimivv.1 exlimiv exlimiv $.
  $}

  ${
    $d x ch $.  $d x ph $.  $d y ch $.  $d y ph $.
    exlimdvv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       31-Jul-1995.) $)
    exlimdvv $p |- ( ph -> ( E. x E. y ps -> ch ) ) $=
      wph wps vy wex wch vx wph wps wch vy exlimdvv.1 exlimdv exlimdv $.
  $}

  ${
    sptruw.1 $e |- ph $.
    $( Version of ~ sp when ` ph ` is true.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-1017.) $)
    sptruw $p |- ( A. x ph -> ph ) $=
      wph wph vx wal sptruw.1 a1i $.
  $}

  ${
    $d x y $.  $d y ph $.
    spfalw.1 $e |- -. ph $.
    $( Version of ~ sp when ` ph ` is false.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-1017.) $)
    spfalw $p |- ( A. x ph -> ph ) $=
      wph wfal vx vy wph wfal wb vx vy weq wph spfalw.1 bifal a1i spw $.
  $}

  $( Theorem 19.2 of [Margaris] p. 89.  Note:  This proof is very different
     from Margaris' because we only have Tarski's FOL axiom schemes available
     at this point.  See the later ~ 19.2g for a more conventional proof.
     (Contributed by NM, 2-Aug-2017.) $)
  19.2 $p |- ( A. x ph -> E. x ph ) $=
    vx vx weq wn vx wal wn wph vx wal wph vx wex wi vx vx weq wn vx wal vx vx
    weq vx equid vx vx weq wn vx vx vx weq vx equid notnoti spfalw mt2 wph wph
    vx vx vx vx weq wph idd speimfw ax-mp $.

  $( Theorem 19.39 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $=
    wph vx wex wps vx wex wi wph vx wal wps vx wex wi wph wps wi vx wex wph vx
    wal wph vx wex wps vx wex wph vx 19.2 imim1i wph wps vx 19.35 sylibr $.

  $( Theorem 19.24 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $=
    wph vx wal wps vx wal wi wph vx wal wps vx wex wi wph wps wi vx wex wps vx
    wal wps vx wex wph vx wal wps vx 19.2 imim2i wph wps vx 19.35 sylibr $.

  $( Theorem 19.34 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $=
    wph vx wal wps vx wex wo wph vx wex wps vx wex wo wph wps wo vx wex wph vx
    wal wph vx wex wps vx wex wph vx 19.2 orim1i wph wps vx 19.43 sylibr $.

  ${
    $d x y $.
    cbvalw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    cbvalw.2 $e |- ( -. ps -> A. x -. ps ) $.
    cbvalw.3 $e |- ( A. y ps -> A. x A. y ps ) $.
    cbvalw.4 $e |- ( -. ph -> A. y -. ph ) $.
    cbvalw.5 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    cbvalw $p |- ( A. x ph <-> A. y ps ) $=
      wph vx wal wps vy wal wph wps vx vy cbvalw.1 cbvalw.2 vx vy weq wph wps
      cbvalw.5 biimpd cbvaliw wps wph vy vx cbvalw.3 cbvalw.4 wps wph wi vx vy
      vx vy weq wph wps cbvalw.5 biimprd equcoms cbvaliw impbii $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbvalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    cbvalvw $p |- ( A. x ph <-> A. y ps ) $=
      wph vx wal wps vy wal wph wps vx vy vx vy weq wph wps cbvalvw.1 biimpd
      cbvalivw wps wph vy vx wps wph wi vx vy vx vy weq wph wps cbvalvw.1
      biimprd equcoms cbvalivw impbii $.

    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 19-Apr-2017.) $)
    cbvexvw $p |- ( E. x ph <-> E. y ps ) $=
      wph wn vx wal wn wps wn vy wal wn wph vx wex wps vy wex wph wn vx wal wps
      wn vy wal wph wn wps wn vx vy vx vy weq wph wps cbvalvw.1 notbid cbvalvw
      notbii wph vx df-ex wps vy df-ex 3bitr4i $.
  $}

  ${
    $d y z $.  $d x y $.  $d z ph $.  $d y ps $.
    alcomiw.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ alcom .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.) $)
    alcomiw $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      wph vy wal vx wal wps vz wal vx wal wps vz wal vx wal vy wal wph vx wal
      vy wal wph vy wal wps vz wal vx wph wps vy vz vy vz weq wph wps alcomiw.1
      biimpd cbvalivw alimi wps vz wal vx wal vy ax-17 wps vz wal vx wal wph vx
      wal vy wps vz wal wph vx wps wph vz vy wps wph wi vy vz vy vz weq wph wps
      alcomiw.1 biimprd equcoms spimvw alimi alimi 3syl $.
  $}

  ${
    $d x y $.
    hbn1fw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    hbn1fw.2 $e |- ( -. ps -> A. x -. ps ) $.
    hbn1fw.3 $e |- ( A. y ps -> A. x A. y ps ) $.
    hbn1fw.4 $e |- ( -. ph -> A. y -. ph ) $.
    hbn1fw.5 $e |- ( -. A. y ps -> A. x -. A. y ps ) $.
    hbn1fw.6 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-6 from which we can prove any ~ ax-6 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 19-Apr-2017.) $)
    hbn1fw $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      wph vx wal wn wps vy wal wn wps vy wal wn vx wal wph vx wal wn vx wal wps
      vy wal wph vx wal wph vx wal wps vy wal wph wps vx vy hbn1fw.1 hbn1fw.2
      hbn1fw.3 hbn1fw.4 hbn1fw.6 cbvalw biimpri con3i hbn1fw.5 wps vy wal wn
      wph vx wal wn vx wph vx wal wps vy wal wph vx wal wps vy wal wph wps vx
      vy hbn1fw.1 hbn1fw.2 hbn1fw.3 hbn1fw.4 hbn1fw.6 cbvalw biimpi con3i alimi
      3syl $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    hbn1w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ hbn1 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    hbn1w $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      wph wps vx vy wph vx wal vy ax-17 wps wn vx ax-17 wps vy wal vx ax-17 wph
      wn vy ax-17 wps vy wal wn vx ax-17 hbn1w.1 hbn1fw $.

    $( Weak version of ~ hba1 .  See comments for ~ ax6w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)
    hba1w $p |- ( A. x ph -> A. x A. x ph ) $=
      wph vx wal wph vx wal wn vx wal wn wph vx wal wn vx wal wn vx wal wph vx
      wal vx wal wph vx wal wn vx wal wph vx wal wph vx wal wn wps vy wal wn vx
      vy vx vy weq wph vx wal wps vy wal wph vx wal wps vy wal wb vx vy weq wph
      wps vx vy hbn1w.1 cbvalvw a1i notbid spw con2i wph vx wal wn wps vy wal
      wn vx vy vx vy weq wph vx wal wps vy wal wph vx wal wps vy wal wb vx vy
      weq wph wps vx vy hbn1w.1 cbvalvw a1i notbid hbn1w wph vx wal wn vx wal
      wn wph vx wal vx wph vx wal wph vx wal wn vx wal wph wps vx vy hbn1w.1
      hbn1w con1i alimi 3syl $.

    $( Weak version of ~ hbe1 .  See comments for ~ ax6w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.) $)
    hbe1w $p |- ( E. x ph -> A. x E. x ph ) $=
      wph vx wex wph wn vx wal wn vx wph vx df-ex wph wn wps wn vx vy vx vy weq
      wph wps hbn1w.1 notbid hbn1w hbxfrbi $.
  $}

  ${
    $d x z $.  $d x y $.  $d z ph $.  $d x ps $.
    hbalw.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    hbalw.2 $e |- ( ph -> A. x ph ) $.
    $( Weak version of ~ hbal .  Uses only Tarski's FOL axiom schemes.  Unlike
       ~ hbal , this theorem requires that ` x ` and ` y ` be distinct i.e. are
       not bundled.  (Contributed by NM, 19-Apr-2017.) $)
    hbalw $p |- ( A. y ph -> A. x A. y ph ) $=
      wph vy wal wph vx wal vy wal wph vy wal vx wal wph wph vx wal vy hbalw.2
      alimi wph wps vy vx vz hbalw.1 alcomiw syl $.
  $}


