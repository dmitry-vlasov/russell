
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_universal_class.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    Conditional equality (experimental)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This is a very useless definition, which "abbreviates" ` ( x = y -> ph ) ` as
  ` CondEq ( x = y -> ph ) ` . What this display hides, though, is that the
  first expression, even though it has a shorter constant string, is actually
  much more complicated in its parse tree: it is parsed as
  (wi (wceq (cv vx) (cv vy)) wph), while the ` CondEq ` version is parsed as
  (wcdeq vx vy wph).  It also allows us to give a name to the specific 3-ary
  operation ` ( x = y -> ph ) ` .

  This is all used as part of a metatheorem: we want to say that
  ` |- ( x = y -> ( ph ( x ) <-> ph ( y ) ) ) ` and
  ` |- ( x = y -> A ( x ) = A ( y ) ) ` are provable, for any expressions
  ` ph ( x ) ` or ` A ( x ) ` in the language.  The proof is by induction, so
  the base case is each of the primitives, which is why you will see a theorem
  for each of the set.mm primitive operations.

  The metatheorem comes with a disjoint variables assumption: every variable in
  ` ph ( x ) ` is assumed disjoint from ` x ` except ` x ` itself.  For such a
  proof by induction, we must consider each of the possible forms of
  ` ph ( x ) ` .  If it is a variable other than ` x ` , then we have
  ` CondEq ( x = y -> A = A ) ` or ` CondEq ( x = y -> ( ph <-> ph ) ) ` ,
  which is provable by ~ cdeqth and reflexivity.  Since we are only working
  with class and wff expressions, it can't be ` x ` itself in set.mm, but if it
  was we'd have to also prove ` CondEq ( x = y -> x = y ) ` (where _set_
  equality is being used on the right).

  Otherwise, it is a primitive operation applied to smaller expressions.  In
  these cases, for each set variable parameter to the operation, we must
  consider if it is equal to ` x ` or not, which yields 2^n proof obligations.
  Luckily, all primitive operations in set.mm have either zero or one set
  variable, so we only need to prove one statement for the non-set constructors
  (like implication) and two for the constructors taking a set (the forall and
  the class builder).

  In each of the primitive proofs, we are allowed to assume that ` y ` is
  disjoint from ` ph ( x ) ` and vice versa, because this is maintained through
  the induction.  This is how we satisfy the DV assumptions of ~ cdeqab1 and
  ~ cdeqab .

$)

  $c CondEq $. $( conditional equality $)

  $( Extend wff notation to include conditional equality.  This is a technical
     device used in the proof that ` F/ ` is the not-free predicate, and that
     definitions are conservative as a result. $)
  wcdeq $a wff CondEq ( x = y -> ph ) $.

  $( Define conditional equality.  All the notation to the left of the ` <-> `
     is fake; the parentheses and arrows are all part of the notation, which
     could equally well be written ` CondEq x y ph ` .  On the right side is
     the actual implication arrow.  The reason for this definition is to
     "flatten" the structure on the right side (whose tree structure is
     something like (wi (wceq (cv vx) (cv vy)) wph) ) into just (wcdeq vx vy
     wph).  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
  df-cdeq $a |- ( CondEq ( x = y -> ph ) <-> ( x = y -> ph ) ) $.

  ${
    cdeqi.1 $e |- ( x = y -> ph ) $.
    $( Deduce conditional equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    cdeqi $p |- CondEq ( x = y -> ph ) $=
      wph vx vy wcdeq vx cv vy cv wceq wph wi cdeqi.1 wph vx vy df-cdeq mpbir
      $.
  $}

  ${
    cdeqri.1 $e |- CondEq ( x = y -> ph ) $.
    $( Property of conditional equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    cdeqri $p |- ( x = y -> ph ) $=
      wph vx vy wcdeq vx cv vy cv wceq wph wi cdeqri.1 wph vx vy df-cdeq mpbi
      $.
  $}

  ${
    cdeqth.1 $e |- ph $.
    $( Deduce conditional equality from a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    cdeqth $p |- CondEq ( x = y -> ph ) $=
      wph vx vy wph vx cv vy cv wceq cdeqth.1 a1i cdeqi $.
  $}

  ${
    cdeqnot.1 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
    $( Distribute conditional equality over negation.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    cdeqnot $p |- CondEq ( x = y -> ( -. ph <-> -. ps ) ) $=
      wph wn wps wn wb vx vy vx cv vy cv wceq wph wps wph wps wb vx vy
      cdeqnot.1 cdeqri notbid cdeqi $.

    ${
      $d x z $.  $d y z $.
      $( Distribute conditional equality over quantification.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)
      cdeqal $p |- CondEq ( x = y -> ( A. z ph <-> A. z ps ) ) $=
        wph vz wal wps vz wal wb vx vy vx cv vy cv wceq wph wps vz wph wps wb
        vx vy cdeqnot.1 cdeqri albidv cdeqi $.

      $( Distribute conditional equality over abstraction.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)
      cdeqab $p |- CondEq ( x = y -> { z | ph } = { z | ps } ) $=
        wph vz cab wps vz cab wceq vx vy vx cv vy cv wceq wph wps vz wph wps wb
        vx vy cdeqnot.1 cdeqri abbidv cdeqi $.
    $}

    ${
      $d x ps $.  $d y ph $.
      $( Distribute conditional equality over quantification.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)
      cdeqal1 $p |- CondEq ( x = y -> ( A. x ph <-> A. y ps ) ) $=
        wph vx wal wps vy wal wb vx vy wph vx wal wps vy wal wb vx cv vy cv
        wceq wph wps vx vy wph wps wb vx vy cdeqnot.1 cdeqri cbvalv a1i cdeqi
        $.

      $( Distribute conditional equality over abstraction.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)
      cdeqab1 $p |- CondEq ( x = y -> { x | ph } = { y | ps } ) $=
        wph vx cab wps vy cab wceq vx vy wph vx cab wps vy cab wceq vx cv vy cv
        wceq wph wps vx vy wph wps wb vx vy cdeqnot.1 cdeqri cbvabv a1i cdeqi
        $.
    $}

    cdeqim.1 $e |- CondEq ( x = y -> ( ch <-> th ) ) $.
    $( Distribute conditional equality over implication.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    cdeqim $p |- CondEq ( x = y -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) $=
      wph wch wi wps wth wi wb vx vy vx cv vy cv wceq wph wps wch wth wph wps
      wb vx vy cdeqnot.1 cdeqri wch wth wb vx vy cdeqim.1 cdeqri imbi12d cdeqi
      $.
  $}

  $( Conditional equality for set-to-class promotion.  (Contributed by Mario
     Carneiro, 11-Aug-2016.) $)
  cdeqcv $p |- CondEq ( x = y -> x = y ) $=
    vx cv vy cv wceq vx vy vx cv vy cv wceq id cdeqi $.

  ${
    cdeqeq.1 $e |- CondEq ( x = y -> A = B ) $.
    cdeqeq.2 $e |- CondEq ( x = y -> C = D ) $.
    $( Distribute conditional equality over equality.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    cdeqeq $p |- CondEq ( x = y -> ( A = C <-> B = D ) ) $=
      cA cC wceq cB cD wceq wb vx vy vx cv vy cv wceq cA cB cC cD cA cB wceq vx
      vy cdeqeq.1 cdeqri cC cD wceq vx vy cdeqeq.2 cdeqri eqeq12d cdeqi $.

    $( Distribute conditional equality over elementhood.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    cdeqel $p |- CondEq ( x = y -> ( A e. C <-> B e. D ) ) $=
      cA cC wcel cB cD wcel wb vx vy vx cv vy cv wceq cA cB cC cD cA cB wceq vx
      vy cdeqeq.1 cdeqri cC cD wceq vx vy cdeqeq.2 cdeqri eleq12d cdeqi $.
  $}

  ${
    $d x ps $.  $d y ph $.
    nfcdeq.1 $e |- F/ x ph $.
    nfcdeq.2 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
    $( If we have a conditional equality proof, where ` ph ` is ` ph ( x ) `
       and ` ps ` is ` ph ( y ) ` , and ` ph ( x ) ` in fact does not have
       ` x ` free in it according to ` F/ ` , then ` ph ( x ) <-> ph ( y ) `
       unconditionally.  This proves that ` F/ x ph ` is actually a not-free
       predicate.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfcdeq $p |- ( ph <-> ps ) $=
      wph wph vx vy wsb wps wph vx vy nfcdeq.1 sbf wph wps vx vy wps vx nfv wph
      wps wb vx vy nfcdeq.2 cdeqri sbie bitr3i $.
  $}

  ${
    $d x z B $.  $d y z A $.
    nfccdeq.1 $e |- F/_ x A $.
    nfccdeq.2 $e |- CondEq ( x = y -> A = B ) $.
    $( Variation of ~ nfcdeq for classes.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfccdeq $p |- A = B $=
      vz cA cB vz cv cA wcel vz cv cB wcel vx vy vx vz cA nfccdeq.1 nfcri vx vy
      vz cv vz cv cA cB vz cv vz cv wceq vx vy vz equid cdeqth nfccdeq.2 cdeqel
      nfcdeq eqriv $.
  $}

  $( Let the computer know the theorems to look for to prove the metatheorem $)
  $( $j
    condequality 'wcdeq' from 'cdeqth';
    condcongruence 'cdeqnot' 'cdeqim' 'cdeqal1' 'cdeqal' 'cdeqcv' 'cdeqeq'
      'cdeqel' 'cdeqab1' 'cdeqab';
    notfree 'wnf' from 'nfcdeq';
    notfree 'wnfc' from 'nfccdeq';
  $)


