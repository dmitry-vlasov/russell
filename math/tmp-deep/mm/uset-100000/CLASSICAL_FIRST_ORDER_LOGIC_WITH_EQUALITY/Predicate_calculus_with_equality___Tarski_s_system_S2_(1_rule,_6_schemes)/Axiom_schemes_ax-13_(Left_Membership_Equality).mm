
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Membership_predicate.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom schemes ax-13 (Left Membership Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Left Membership Equality.  One of the equality and substitution
     axioms for a non-logical predicate in our predicate calculus with
     equality.  It substitutes equal variables into the left-hand side of the
     ` e. ` binary predicate.  This axiom scheme is a sub-scheme of Axiom
     Scheme B8 of system S2 of [Tarski], p. 75, whose general form cannot be
     represented with our notation.  Also appears as Axiom scheme C12' in
     [Megill] p. 448 (p. 16 of the preprint).  "Non-logical" means that the
     predicate is not a primitive of predicate calculus proper but instead is
     an extension to it.  "Binary" means that the predicate has two arguments.
     In a system of predicate calculus with equality, like ours, equality is
     not usually considered to be a non-logical predicate.  In systems of
     predicate calculus without equality, it typically would be.  (Contributed
     by NM, 5-Aug-1993.) $)
  ax-13 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     5-Aug-1993.) $)
  elequ1 $p |- ( x = y -> ( x e. z <-> y e. z ) ) $=
    vx vy weq vx vz wel vy vz wel vx vy vz ax-13 vy vz wel vx vz wel wi vy vx
    vy vx vz ax-13 equcoms impbid $.



