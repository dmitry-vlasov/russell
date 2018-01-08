
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Rule_scheme_ax-gen_(Generalization).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
         Axiom scheme ax-5 (Quantified Implication)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105.
     (Contributed by NM, 5-Aug-1993.) $)
  ax-5 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by O'Cat, 30-Mar-2008.) $)
  alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    wph wps vx ax-5 $.

  ${
    alimi.1 $e |- ( ph -> ps ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 5-Aug-1993.) $)
    alimi $p |- ( A. x ph -> A. x ps ) $=
      wph wps wi wph vx wal wps vx wal wi vx wph wps vx ax-5 alimi.1 mpg $.

    $( Inference doubly quantifying both antecedent and consequent.
       (Contributed by NM, 3-Feb-2005.) $)
    2alimi $p |- ( A. x A. y ph -> A. x A. y ps ) $=
      wph vy wal wps vy wal vx wph wps vy alimi.1 alimi alimi $.
  $}

  ${
    al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference quantifying antecedent, nested antecedent, and consequent.
       (Contributed by NM, 5-Aug-1993.) $)
    al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $=
      wph vx wal wps wch wi vx wal wps vx wal wch vx wal wi wph wps wch wi vx
      al2imi.1 alimi wps wch vx alim syl $.
  $}

  ${
    alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Variant of ~ al2imi with conjunctive antecedent.  (Contributed by Andrew
       Salmon, 8-Jun-2011.) $)
    alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $=
      wph vx wal wps vx wal wch vx wal wph wps wch vx wph wps wch alanimi.1 ex
      al2imi imp $.
  $}

  ${
    alimdh.1 $e |- ( ph -> A. x ph ) $.
    alimdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM,
       4-Jan-2002.) $)
    alimdh $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      wph wph vx wal wps vx wal wch vx wal wi alimdh.1 wph wps wch vx alimdh.2
      al2imi syl $.
  $}

  $( Theorem 19.15 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $=
    wph wps wb vx wal wph vx wal wps vx wal wph wps wb wph wps vx wph wps bi1
    al2imi wph wps wb wps wph vx wph wps bi2 al2imi impbid $.

  ${
    alrimih.1 $e |- ( ph -> A. x ph ) $.
    alrimih.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    alrimih $p |- ( ph -> A. x ps ) $=
      wph wph vx wal wps vx wal alrimih.1 wph wps vx alrimih.2 alimi syl $.
  $}

  ${
    albii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding universal quantifier to both sides of an equivalence.
       (Contributed by NM, 7-Aug-1994.) $)
    albii $p |- ( A. x ph <-> A. x ps ) $=
      wph wps wb wph vx wal wps vx wal wb vx wph wps vx albi albii.1 mpg $.

    $( Theorem albii is the congruence law for universal quantification. $)
    $( $j congruence 'albii'; $)

    $( Inference adding two universal quantifiers to both sides of an
       equivalence.  (Contributed by NM, 9-Mar-1997.) $)
    2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $=
      wph vy wal wps vy wal vx wph wps vy albii.1 albii albii $.
  $}

  ${
    hbxfrbi.1 $e |- ( ph <-> ps ) $.
    hbxfrbi.2 $e |- ( ps -> A. x ps ) $.
    $( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfreq for equality version.  (Contributed by
       Jonathan Ben-Naim, 3-Jun-2011.) $)
    hbxfrbi $p |- ( ph -> A. x ph ) $=
      wps wps vx wal wph wph vx wal hbxfrbi.2 hbxfrbi.1 wph wps vx hbxfrbi.1
      albii 3imtr4i $.
  $}

  ${
    nfbii.1 $e |- ( ph <-> ps ) $.
    $( Equality theorem for not-free.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfbii $p |- ( F/ x ph <-> F/ x ps ) $=
      wph wph vx wal wi vx wal wps wps vx wal wi vx wal wph vx wnf wps vx wnf
      wph wph vx wal wi wps wps vx wal wi vx wph wps wph vx wal wps vx wal
      nfbii.1 wph wps vx nfbii.1 albii imbi12i albii wph vx df-nf wps vx df-nf
      3bitr4i $.

    ${
      nfxfr.2 $e |- F/ x ps $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
      nfxfr $p |- F/ x ph $=
        wph vx wnf wps vx wnf nfxfr.2 wph wps vx nfbii.1 nfbii mpbir $.
    $}

    ${
      nfxfrd.2 $e |- ( ch -> F/ x ps ) $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
      nfxfrd $p |- ( ch -> F/ x ph ) $=
        wch wps vx wnf wph vx wnf nfxfrd.2 wph wps vx nfbii.1 nfbii sylibr $.
    $}
  $}

  $( Theorem 19.6 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  alex $p |- ( A. x ph <-> -. E. x -. ph ) $=
    wph vx wal wph wn wn vx wal wph wn vx wex wn wph wph wn wn vx wph notnot
    albii wph wn vx alnex bitri $.

  $( Part of theorem *11.5 in [WhiteheadRussell] p. 164.  (Contributed by
     Andrew Salmon, 24-May-2011.) $)
  2nalexn $p |- ( -. A. x A. y ph <-> E. x E. y -. ph ) $=
    wph wn vy wex vx wex wph vy wal vx wal wn wph wn vy wex vx wex wph wn vy
    wex wn vx wal wph vy wal vx wal wph wn vy wex vx df-ex wph vy wal wph wn vy
    wex wn vx wph vy alex albii xchbinxr bicomi $.

  $( Theorem 19.14 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  exnal $p |- ( E. x -. ph <-> -. A. x ph ) $=
    wph vx wal wph wn vx wex wph vx alex con2bii $.

  $( Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 4-Jul-2014.) $)
  exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    wph wps wi vx wal wps vx wex wph vx wex wph wps wi vx wal wps wn vx wal wph
    wn vx wal wps vx wex wn wph vx wex wn wph wps wi wps wn wph wn vx wph wps
    con3 al2imi wps vx alnex wph vx alnex 3imtr3g con4d $.

  ${
    eximi.1 $e |- ( ph -> ps ) $.
    $( Inference adding existential quantifier to antecedent and consequent.
       (Contributed by NM, 5-Aug-1993.) $)
    eximi $p |- ( E. x ph -> E. x ps ) $=
      wph wps wi wph vx wex wps vx wex wi vx wph wps vx exim eximi.1 mpg $.

    $( Inference adding two existential quantifiers to antecedent and
       consequent.  (Contributed by NM, 3-Feb-2005.) $)
    2eximi $p |- ( E. x E. y ph -> E. x E. y ps ) $=
      wph vy wex wps vy wex vx wph wps vy eximi.1 eximi eximi $.
  $}

  $( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 19-Aug-1993.) $)
  alinexa $p |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) ) $=
    wph wps wn wi vx wal wph wps wa wn vx wal wph wps wa vx wex wn wph wps wn
    wi wph wps wa wn vx wph wps imnan albii wph wps wa vx alnex bitri $.

  $( A relationship between two quantifiers and negation.  (Contributed by NM,
     18-Aug-1993.) $)
  alexn $p |- ( A. x E. y -. ph <-> -. E. x A. y ph ) $=
    wph wn vy wex vx wal wph vy wal wn vx wal wph vy wal vx wex wn wph wn vy
    wex wph vy wal wn vx wph vy exnal albii wph vy wal vx alnex bitri $.

  $( Theorem *11.51 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.)  (Proof shortened by Wolf Lammen, 25-Sep-2014.) $)
  2exnexn $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $=
    wph wn vy wex vx wal wph vy wal vx wex wph vx vy alexn con2bii $.

  $( Theorem 19.18 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $=
    wph wps wb vx wal wph vx wex wps vx wex wph wps wb vx wal wph wps wi vx wal
    wph vx wex wps vx wex wi wph wps wb wph wps wi vx wph wps bi1 alimi wph wps
    vx exim syl wph wps wb vx wal wps wph wi vx wal wps vx wex wph vx wex wi
    wph wps wb wps wph wi vx wph wps bi2 alimi wps wph vx exim syl impbid $.

  ${
    exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 24-May-1994.) $)
    exbii $p |- ( E. x ph <-> E. x ps ) $=
      wph wps wb wph vx wex wps vx wex wb vx wph wps vx exbi exbii.1 mpg $.
  $}

  ${
    2exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 16-Mar-1995.) $)
    2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $=
      wph vy wex wps vy wex vx wph wps vy 2exbii.1 exbii exbii $.
  $}

  ${
    3exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding 3 existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 2-May-1995.) $)
    3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $=
      wph vz wex wps vz wex vx vy wph wps vz 3exbii.1 exbii 2exbii $.
  $}

  $( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 25-Mar-1996.)  (Proof shortened by Wolf Lammen, 4-Sep-2014.) $)
  exanali $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $=
    wph wps wn wa vx wex wph wps wi wn vx wex wph wps wi vx wal wn wph wps wn
    wa wph wps wi wn vx wph wps annim exbii wph wps wi vx exnal bitri $.

  $( Commutation of conjunction inside an existential quantifier.  (Contributed
     by NM, 18-Aug-1993.) $)
  exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $=
    wph wps wa wps wph wa vx wph wps ancom exbii $.

  ${
    alrimdh.1 $e |- ( ph -> A. x ph ) $.
    alrimdh.2 $e |- ( ps -> A. x ps ) $.
    alrimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    alrimdh $p |- ( ph -> ( ps -> A. x ch ) ) $=
      wps wps vx wal wph wch vx wal alrimdh.2 wph wps wch vx alrimdh.1
      alrimdh.3 alimdh syl5 $.
  $}

  ${
    eximdh.1 $e |- ( ph -> A. x ph ) $.
    eximdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       20-May-1996.) $)
    eximdh $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      wph wps wch wi vx wal wps vx wex wch vx wex wi wph wps wch wi vx eximdh.1
      eximdh.2 alrimih wps wch vx exim syl $.
  $}

  ${
    nexdh.1 $e |- ( ph -> A. x ph ) $.
    nexdh.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       2-Jan-2002.) $)
    nexdh $p |- ( ph -> -. E. x ps ) $=
      wph wps wn vx wal wps vx wex wn wph wps wn vx nexdh.1 nexdh.2 alrimih wps
      vx alnex sylib $.
  $}

  ${
    albidh.1 $e |- ( ph -> A. x ph ) $.
    albidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
    albidh $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      wph wps wch wb vx wal wps vx wal wch vx wal wb wph wps wch wb vx albidh.1
      albidh.2 alrimih wps wch vx albi syl $.
  $}

  ${
    exbidh.1 $e |- ( ph -> A. x ph ) $.
    exbidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
    exbidh $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      wph wps wch wb vx wal wps vx wex wch vx wex wb wph wps wch wb vx exbidh.1
      exbidh.2 alrimih wps wch vx exbi syl $.
  $}

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
  exsimpl $p |- ( E. x ( ph /\ ps ) -> E. x ph ) $=
    wph wps wa wph vx wph wps simpl eximi $.

  $( Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 147.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 4-Jul-2014.) $)
  19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    wph wps wa vx wal wph vx wal wps vx wal wa wph wps wa vx wal wph vx wal wps
    vx wal wph wps wa wph vx wph wps simpl alimi wph wps wa wps vx wph wps
    simpr alimi jca wph wps wph wps wa vx wph wps wa id alanimi impbii $.

  $( Theorem 19.26 of [Margaris] p. 90 with two quantifiers.  (Contributed by
     NM, 3-Feb-2005.) $)
  19.26-2 $p |- ( A. x A. y ( ph /\ ps ) <->
                ( A. x A. y ph /\ A. x A. y ps ) ) $=
    wph wps wa vy wal vx wal wph vy wal wps vy wal wa vx wal wph vy wal vx wal
    wps vy wal vx wal wa wph wps wa vy wal wph vy wal wps vy wal wa vx wph wps
    vy 19.26 albii wph vy wal wps vy wal vx 19.26 bitri $.

  $( Theorem 19.26 of [Margaris] p. 90 with triple conjunction.  (Contributed
     by NM, 13-Sep-2011.) $)
  19.26-3an $p |- ( A. x ( ph /\ ps /\ ch )
                   <-> ( A. x ph /\ A. x ps /\ A. x ch ) ) $=
    wph wps wa wch wa vx wal wph vx wal wps vx wal wa wch vx wal wa wph wps wch
    w3a vx wal wph vx wal wps vx wal wch vx wal w3a wph wps wa wch wa vx wal
    wph wps wa vx wal wch vx wal wa wph vx wal wps vx wal wa wch vx wal wa wph
    wps wa wch vx 19.26 wph wps wa vx wal wph vx wal wps vx wal wa wch vx wal
    wph wps vx 19.26 anbi1i bitri wph wps wch w3a wph wps wa wch wa vx wph wps
    wch df-3an albii wph vx wal wps vx wal wch vx wal df-3an 3bitr4i $.

  $( Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $=
    wph vx wal wps vx wex wph wps wa vx wex wph vx wal wps wph wps wa wi vx wal
    wps vx wex wph wps wa vx wex wi wph wps wph wps wa wi vx wph wps pm3.2
    alimi wps wph wps wa vx exim syl imp $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM,
     18-Aug-1993.) $)
  19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $=
    wph vx wex wps vx wal wa wps wph wa vx wex wph wps wa vx wex wps vx wal wph
    vx wex wps wph wa vx wex wps wph vx 19.29 ancoms wph wps vx exancom sylibr
    $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with double
     quantification.  (Contributed by NM, 3-Feb-2005.) $)
  19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    wph vy wex vx wex wps vy wal vx wal wa wph vy wex wps vy wal wa vx wex wph
    wps wa vy wex vx wex wph vy wex wps vy wal vx 19.29r wph vy wex wps vy wal
    wa wph wps wa vy wex vx wph wps vy 19.29r eximi syl $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with mixed quantification.
     (Contributed by NM, 11-Feb-2005.) $)
  19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    wph vy wal vx wex wps vy wex vx wal wa wph vy wal wps vy wex wa vx wex wph
    wps wa vy wex vx wex wph vy wal wps vy wex vx 19.29r wph vy wal wps vy wex
    wa wph wps wa vy wex vx wph wps vy 19.29 eximi syl $.

  $( Theorem 19.35 of [Margaris] p. 90.  This theorem is useful for moving an
     implication (in the form of the right-hand side) into the scope of a
     single existential quantifier.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 27-Jun-2014.) $)
  19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    wph wps wi vx wex wph vx wal wps vx wex wi wph wps wi wn vx wal wph vx wal
    wps vx wex wn wa wph wps wi vx wex wn wph vx wal wps vx wex wi wn wph wps
    wn wa vx wal wph vx wal wps wn vx wal wa wph wps wi wn vx wal wph vx wal
    wps vx wex wn wa wph wps wn vx 19.26 wph wps wn wa wph wps wi wn vx wph wps
    annim albii wps wn vx wal wps vx wex wn wph vx wal wps vx alnex anbi2i
    3bitr3i wph wps wi vx alnex wph vx wal wps vx wex annim 3bitr3i con4bii $.

  ${
    19.35i.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.35i $p |- ( A. x ph -> E. x ps ) $=
      wph wps wi vx wex wph vx wal wps vx wex wi 19.35i.1 wph wps vx 19.35 mpbi
      $.
  $}

  ${
    19.35ri.1 $e |- ( A. x ph -> E. x ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.35ri $p |- E. x ( ph -> ps ) $=
      wph wps wi vx wex wph vx wal wps vx wex wi 19.35ri.1 wph wps vx 19.35
      mpbir $.
  $}

  $( Theorem 19.25 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.25 $p |- ( A. y E. x ( ph -> ps ) ->
              ( E. y A. x ph -> E. y E. x ps ) ) $=
    wph wps wi vx wex vy wal wph vx wal wps vx wex wi vy wal wph vx wal vy wex
    wps vx wex vy wex wi wph wps wi vx wex wph vx wal wps vx wex wi vy wph wps
    wi vx wex wph vx wal wps vx wex wi wph wps vx 19.35 biimpi alimi wph vx wal
    wps vx wex vy exim syl $.

  $( Theorem 19.30 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  19.30 $p |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) $=
    wph wn wps wi vx wal wph vx wal wn wps vx wex wi wph wps wo vx wal wph vx
    wal wps vx wex wo wph vx wal wn wph wn vx wex wph wn wps wi vx wal wps vx
    wex wph vx exnal wph wn wps vx exim syl5bir wph wps wo wph wn wps wi vx wph
    wps df-or albii wph vx wal wps vx wex df-or 3imtr4i $.

  $( Theorem 19.43 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 27-Jun-2014.) $)
  19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    wph wps wo vx wex wph vx wex wn wps vx wex wi wph vx wex wps vx wex wo wph
    wps wo vx wex wph wn wps wi vx wex wph wn vx wal wps vx wex wi wph vx wex
    wn wps vx wex wi wph wps wo wph wn wps wi vx wph wps df-or exbii wph wn wps
    vx 19.35 wph wn vx wal wph vx wex wn wps vx wex wph vx alnex imbi1i 3bitri
    wph vx wex wps vx wex df-or bitr4i $.

  $( Obsolete proof of ~ 19.43 as of 3-May-2016.  Leave this in for the example
     on the mmrecent.html page.  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  19.43OLD $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    wph wps wo wn vx wal wn wph vx wex wn wps vx wex wn wa wn wph wps wo vx wex
    wph vx wex wps vx wex wo wph wps wo wn vx wal wph vx wex wn wps vx wex wn
    wa wph wps wo wn vx wal wph wn wps wn wa vx wal wph wn vx wal wps wn vx wal
    wa wph vx wex wn wps vx wex wn wa wph wps wo wn wph wn wps wn wa vx wph wps
    ioran albii wph wn wps wn vx 19.26 wph wn vx wal wph vx wex wn wps wn vx
    wal wps vx wex wn wph vx alnex wps vx alnex anbi12i 3bitri notbii wph wps
    wo vx df-ex wph vx wex wps vx wex oran 3bitr4i $.

  $( Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $=
    wph vx wal wph wps wo vx wal wps vx wal wph wph wps wo vx wph wps orc alimi
    wps wph wps wo vx wps wph olc alimi jaoi $.

  $( The antecedent provides a condition implying the converse of ~ 19.33 .
     Compare Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM,
     27-Mar-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
     shortened by Wolf Lammen, 5-Jul-2014.) $)
  19.33b $p |- ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    wph vx wex wps vx wex wa wn wph wps wo vx wal wph vx wal wps vx wal wo wph
    vx wex wps vx wex wa wn wph vx wex wn wps vx wex wn wo wph wps wo vx wal
    wph vx wal wps vx wal wo wi wph vx wex wps vx wex ianor wph vx wex wn wph
    wps wo vx wal wph vx wal wps vx wal wo wi wps vx wex wn wph wps wo vx wal
    wph vx wex wn wps vx wal wph vx wal wps vx wal wo wph vx wex wn wph wn vx
    wal wph wps wo vx wal wps vx wal wph vx alnex wph wps wo wph wn wps vx wph
    wps pm2.53 al2imi syl5bir wps vx wal wph vx wal olc syl6com wph wps wo vx
    wal wps vx wex wn wph vx wal wph vx wal wps vx wal wo wph wps wo vx wal wps
    vx wex wph vx wal wph wps wo vx wal wph vx wal wps vx wex wph wps vx 19.30
    orcomd ord wph vx wal wps vx wal orc syl6com jaoi sylbi wph wps vx 19.33
    impbid1 $.

  $( Theorem 19.40 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $=
    wph wps wa vx wex wph vx wex wps vx wex wph wps vx exsimpl wph wps wa wps
    vx wph wps simpr eximi jca $.

  $( Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  19.40-2 $p |- ( E. x E. y ( ph /\ ps ) ->
        ( E. x E. y ph /\ E. x E. y ps ) ) $=
    wph wps wa vy wex vx wex wph vy wex wps vy wex wa vx wex wph vy wex vx wex
    wps vy wex vx wex wa wph wps wa vy wex wph vy wex wps vy wex wa vx wph wps
    vy 19.40 eximi wph vy wex wps vy wex vx 19.40 syl $.

  $( Split a biconditional and distribute quantifier.  (Contributed by NM,
     18-Aug-1993.) $)
  albiim $p |- ( A. x ( ph <-> ps ) <->
             ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $=
    wph wps wb vx wal wph wps wi wps wph wi wa vx wal wph wps wi vx wal wps wph
    wi vx wal wa wph wps wb wph wps wi wps wph wi wa vx wph wps dfbi2 albii wph
    wps wi wps wph wi vx 19.26 bitri $.

  $( Split a biconditional and distribute 2 quantifiers.  (Contributed by NM,
     3-Feb-2005.) $)
  2albiim $p |- ( A. x A. y ( ph <-> ps ) <->
             ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) ) $=
    wph wps wb vy wal vx wal wph wps wi vy wal wps wph wi vy wal wa vx wal wph
    wps wi vy wal vx wal wps wph wi vy wal vx wal wa wph wps wb vy wal wph wps
    wi vy wal wps wph wi vy wal wa vx wph wps vy albiim albii wph wps wi vy wal
    wps wph wi vy wal vx 19.26 bitri $.

  $( Add/remove a conjunct in the scope of an existential quantifier.
     (Contributed by Raph Levien, 3-Jul-2006.) $)
  exintrbi $p |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) ) $=
    wph wps wi vx wal wph wph wps wa wb vx wal wph vx wex wph wps wa vx wex wb
    wph wps wi wph wph wps wa wb vx wph wps pm4.71 albii wph wph wps wa vx exbi
    sylbi $.

  $( Introduce a conjunct in the scope of an existential quantifier.
     (Contributed by NM, 11-Aug-1993.) $)
  exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $=
    wph wps wi vx wal wph vx wex wph wps wa vx wex wph wps vx exintrbi biimpd
    $.

  $( Theorem *10.3 in [WhiteheadRussell] p. 150.  (Contributed by Andrew
     Salmon, 8-Jun-2011.) $)
  alsyl $p |- ( ( A. x ( ph -> ps ) /\ A. x ( ps -> ch ) ) ->
        A. x ( ph -> ch ) ) $=
    wph wps wi wps wch wi wph wch wi vx wph wps wch pm3.33 alanimi $.


