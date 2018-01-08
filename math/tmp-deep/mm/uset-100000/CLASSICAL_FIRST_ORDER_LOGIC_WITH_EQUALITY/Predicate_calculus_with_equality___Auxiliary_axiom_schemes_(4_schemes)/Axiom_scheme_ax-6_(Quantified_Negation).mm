
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Axiom scheme ax-6 (Quantified Negation)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax6w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  (Contributed by NM,
     5-Aug-1993.) $)
  ax-6 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.

  $( ` x ` is not free in ` -. A. x ph ` .  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 18-Aug-2014.) $)
  hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    wph vx ax-6 $.

  $( ` x ` is not free in ` E. x ph ` .  (Contributed by NM, 5-Aug-1993.) $)
  hbe1 $p |- ( E. x ph -> A. x E. x ph ) $=
    wph vx wex wph wn vx wal wn vx wph vx df-ex wph wn vx hbn1 hbxfrbi $.

  $( ` x ` is not free in ` E. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfe1 $p |- F/ x E. x ph $=
    wph vx wex vx wph vx hbe1 nfi $.

  $( The analog in our "pure" predicate calculus of axiom 5 of modal logic S5.
     (Contributed by NM, 5-Oct-2005.) $)
  modal-5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $=
    wph wn vx hbn1 $.


