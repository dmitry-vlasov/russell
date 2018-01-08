
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-6_(Quantified_Negation).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Axiom scheme ax-7 (Quantifier Commutation)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  One of the 4 axioms of pure predicate calculus.  Axiom
     scheme C6' in [Megill] p. 448 (p. 16 of the preprint).  Also appears as
     Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax7w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  (Contributed by NM,
     5-Aug-1993.) $)
  ax-7 $a |- ( A. x A. y ph -> A. y A. x ph ) $.

  ${
    a7s.1 $e |- ( A. x A. y ph -> ps ) $.
    $( Swap quantifiers in an antecedent.  (Contributed by NM, 5-Aug-1993.) $)
    a7s $p |- ( A. y A. x ph -> ps ) $=
      wph vx wal vy wal wph vy wal vx wal wps wph vy vx ax-7 a7s.1 syl $.
  $}

  ${
    hbal.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by NM, 5-Aug-1993.) $)
    hbal $p |- ( A. y ph -> A. x A. y ph ) $=
      wph vy wal wph vx wal vy wal wph vy wal vx wal wph wph vx wal vy hbal.1
      alimi wph vy vx ax-7 syl $.
  $}

  $( Theorem 19.5 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $=
    wph vy wal vx wal wph vx wal vy wal wph vx vy ax-7 wph vy vx ax-7 impbii $.

  $( Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $=
    wph vz wal vy wal vx wal wph vz wal vx wal vy wal wph vx wal vz wal vy wal
    wph vz wal vx vy alcom wph vz wal vx wal wph vx wal vz wal vy wph vx vz
    alcom albii bitri $.

  $( Rotate 4 universal quantifiers twice.  (Contributed by NM, 2-Feb-2005.)
     (Proof shortened by Fan Zheng, 6-Jun-2016.) $)
  alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    wph vw wal vz wal vy wal vx wal wph vy wal vw wal vz wal vx wal wph vy wal
    vx wal vw wal vz wal wph vw wal vz wal vy wal wph vy wal vw wal vz wal vx
    wph vy vz vw alrot3 albii wph vy wal vx vz vw alrot3 bitri $.

  ${
    hbald.1 $e |- ( ph -> A. y ph ) $.
    hbald.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbal .
       (Contributed by NM, 2-Jan-2002.) $)
    hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $=
      wph wps vy wal wps vx wal vy wal wps vy wal vx wal wph wps wps vx wal vy
      hbald.1 hbald.2 alimdh wps vy vx ax-7 syl6 $.
  $}


