
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-17_(Distinctness)_-_first_use_of__d.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Equality predicate; define substitution

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( --- Start of patch to prevent connective overloading $)
  $c class $.

  $( Add 'class' as a typecode. $)
  $( $j syntax 'class'; $)

  $( This syntax construction states that a variable ` x ` , which has been
     declared to be a set variable by $f statement vx, is also a class
     expression.  This can be justified informally as follows.  We know that
     the class builder ` { y | y e. x } ` is a class by ~ cab .  Since (when
     ` y ` is distinct from ` x ` ) we have ` x = { y | y e. x } ` by
     ~ cvjust , we can argue that the syntax " ` class x ` " can be viewed as
     an abbreviation for " ` class { y | y e. x } ` ".  See the discussion
     under the definition of class in [Jech] p. 4 showing that "Every set can
     be considered to be a class."

     While it is tempting and perhaps occasionally useful to view ~ cv as a
     "type conversion" from a set variable to a class variable, keep in mind
     that ~ cv is intrinsically no different from any other class-building
     syntax such as ~ cab , ~ cun , or ~ c0 .

     For a general discussion of the theory of classes and the role of ~ cv ,
     see ~ http://us.metamath.org/mpeuni/mmset.html#class .

     (The description above applies to set theory, not predicate calculus.  The
     purpose of introducing ` class x ` here, and not in set theory where it
     belongs, is to allow us to express i.e.  "prove" the ~ weq of predicate
     calculus from the ~ wceq of set theory, so that we don't "overload" the
     ` = ` connective with two syntax definitions.  This is done to prevent
     ambiguity that would complicate some Metamath parsers.) $)
  cv $a class x $.
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(          (None - the above patch had no old code.) $)
  $( --- End of old code before overloading prevention patch. $)

  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    $v B $.
    wceq.cA $f class A $.
    wceq.cB $f class B $.
    $( Extend wff definition to include class equality.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The purpose of introducing ` wff A = B ` here, and not in set theory
       where it belongs, is to allow us to express i.e.  "prove" the ~ weq of
       predicate calculus in terms of the ~ wceq of set theory, so that we
       don't "overload" the ` = ` connective with two syntax definitions.  This
       is done to prevent ambiguity that would complicate some Metamath
       parsers.  For example, some parsers - although not the Metamath program
       - stumble on the fact that the ` = ` in ` x = y ` could be the ` = ` of
       either ~ weq or ~ wceq , although mathematically it makes no
       difference.  The class variables ` A ` and ` B ` are introduced
       temporarily for the purpose of this definition but otherwise not used in
       predicate calculus.  See ~ df-cleq for more information on the set
       theory usage of ~ wceq .) $)
    wceq $a wff A = B $.
  $}

  $( Extend wff definition to include atomic formulas using the equality
     predicate.

     (Instead of introducing ~ weq as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wceq .  This lets us avoid overloading
     the ` = ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ weq is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wceq .  Note:  To see the proof steps of this syntax proof, type "show
     proof weq /all" in the Metamath program.)  (Contributed by NM,
     24-Jan-2006.) $)
  weq $p wff x = y $=
    vx cv vy cv wceq $.
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include atomic formulas using the equality
     predicate.

     After we introduce ~ cv and ~ wceq in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wceq". @)
  weq @a wff x = y @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) $)
  equs3 $p |- ( E. x ( x = y /\ ph ) <-> -. A. x ( x = y -> -. ph ) ) $=
    vx vy weq wph wn wi vx wal vx vy weq wph wa vx wex vx vy weq wph vx alinexa
    con2bii $.

  ${
    speimfw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, with additional weakening to allow bundling of ` x ` and
       ` y ` .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       23-Apr-2017.)  (Proof shortened by Wolf Lammen, 5-Aug-2017.) $)
    speimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) ) $=
      vx vy weq vx wex wph wps wi vx wex vx vy weq wn vx wal wn wph vx wal wps
      vx wex wi vx vy weq wph wps wi vx speimfw.2 eximi vx vy weq vx df-ex wph
      wps vx 19.35 3imtr3i $.
  $}

  ${
    spimfw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spimfw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, with additional weakening to allow bundling of ` x ` and
       ` y ` .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       23-Apr-1017.)  (Proof shortened by Wolf Lammen, 7-Aug-2017.) $)
    spimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> ps ) ) $=
      vx vy weq wn vx wal wn wph vx wal wps vx wex wps wph wps vx vy spimfw.2
      speimfw wps vx wex wps wn vx wal wn wps wps vx df-ex wps wps wn vx wal
      spimfw.1 con1i sylbi syl6 $.
  $}

  ${
    ax11i.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax11i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference that has ~ ax-11 (without ` A. y ` ) as its conclusion.  Uses
       only Tarski's FOL axiom schemes.  The hypotheses may be eliminable
       without one or more of these axioms in special cases.  Proof similar to
       Lemma 16 of [Tarski] p. 70.  (Contributed by NM, 20-May-2008.) $)
    ax11i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      vx vy weq wph wps vx vy weq wph wi vx wal ax11i.1 wps vx vy weq wph wi vx
      ax11i.2 vx vy weq wph wps ax11i.1 biimprcd alrimih syl6bi $.
  $}

  $c [ $. $( Left bracket $)
  $c / $. $( Slash. $)
  $c ] $.  $( Right bracket $)

  $( Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").
     (Contributed by NM, 24-Jan-2006.) $)
  wsb $a wff [ y / x ] ph $.

  $( Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
     preprint).  For our notation, we use ` [ y / x ] ph ` to mean "the wff
     that results from the proper substitution of ` y ` for ` x ` in the wff
     ` ph ` ."  We can also use ` [ y / x ] ph ` in place of the "free for"
     side condition used in traditional predicate calculus; see, for example,
     ~ stdpc4 .

     Our notation was introduced in Haskell B. Curry's _Foundations of
     Mathematical Logic_ (1977), p. 316 and is frequently used in textbooks of
     lambda calculus and combinatory logic.  This notation improves the common
     but ambiguous notation, " ` ph ( y ) ` is the wff that results when ` y `
     is properly substituted for ` x ` in ` ph ( x ) ` ."  For example, if the
     original ` ph ( x ) ` is ` x = y ` , then ` ph ( y ) ` is ` y = y ` , from
     which we obtain that ` ph ( x ) ` is ` x = x ` .  So what exactly does
     ` ph ( x ) ` mean?  Curry's notation solves this problem.

     In most books, proper substitution has a somewhat complicated recursive
     definition with multiple cases based on the occurrences of free and bound
     variables in the wff.  Instead, we use a single formula that is exactly
     equivalent and gives us a direct definition.  We later prove that our
     definition has the properties we expect of proper substitution (see
     theorems ~ sbequ , ~ sbcom2 and ~ sbid2v ).

     Note that our definition is valid even when ` x ` and ` y ` are replaced
     with the same variable, as ~ sbid shows.  We achieve this by having ` x `
     free in the first conjunct and bound in the second.  We can also achieve
     this by using a dummy variable, as the alternate definition ~ dfsb7 shows
     (which some logicians may prefer because it doesn't mix free and bound
     variables).  Another version that mixes free and bound variables is
     ~ dfsb3 .  When ` x ` and ` y ` are distinct, we can express proper
     substitution with the simpler expressions of ~ sb5 and ~ sb6 .

     There are no restrictions on any of the variables, including what
     variables may occur in wff ` ph ` .  (Contributed by NM, 5-Aug-1993.) $)
  df-sb $a |- ( [ y / x ] ph <->
              ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ2 $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $=
    wph vx vy wsb vx vy weq wph wi vx vy weq wph wa vx wex wa vx vy weq wph wph
    vx vy df-sb vx vy weq wph wi vx vy weq wph wa vx wex wa vx vy weq wph vx vy
    weq wph wi vx vy weq wph wa vx wex simpl com12 syl5bi $.

  $( One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $=
    wph vx vy wsb vx vy weq wph wi vx vy weq wph wa vx wex wph vx vy df-sb
    simprbi $.

  ${
    sbimi.1 $e |- ( ph -> ps ) $.
    $( Infer substitution into antecedent and consequent of an implication.
       (Contributed by NM, 25-Jun-1998.) $)
    sbimi $p |- ( [ y / x ] ph -> [ y / x ] ps ) $=
      vx vy weq wph wi vx vy weq wph wa vx wex wa vx vy weq wps wi vx vy weq
      wps wa vx wex wa wph vx vy wsb wps vx vy wsb vx vy weq wph wi vx vy weq
      wps wi vx vy weq wph wa vx wex vx vy weq wps wa vx wex wph wps vx vy weq
      sbimi.1 imim2i vx vy weq wph wa vx vy weq wps wa vx wph wps vx vy weq
      sbimi.1 anim2i eximi anim12i wph vx vy df-sb wps vx vy df-sb 3imtr4i $.
  $}

  ${
    sbbii.1 $e |- ( ph <-> ps ) $.
    $( Infer substitution into both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    sbbii $p |- ( [ y / x ] ph <-> [ y / x ] ps ) $=
      wph vx vy wsb wps vx vy wsb wph wps vx vy wph wps sbbii.1 biimpi sbimi
      wps wph vx vy wph wps sbbii.1 biimpri sbimi impbii $.
  $}


