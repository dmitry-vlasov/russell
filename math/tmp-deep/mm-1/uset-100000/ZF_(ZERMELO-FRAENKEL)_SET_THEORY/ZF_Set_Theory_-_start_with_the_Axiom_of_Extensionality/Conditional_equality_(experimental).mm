$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_universal_class.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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
$c CondEq  $.
$( conditional equality $)
$( Extend wff notation to include conditional equality.  This is a technical
     device used in the proof that ` F/ ` is the not-free predicate, and that
     definitions are conservative as a result. $)
${
	$v ph $.
	$v x $.
	$v y $.
	fwcdeq_0 $f wff ph $.
	fwcdeq_1 $f set x $.
	fwcdeq_2 $f set y $.
	wcdeq $a wff CondEq ( x = y -> ph ) $.
$}
$( Define conditional equality.  All the notation to the left of the ` <-> `
     is fake; the parentheses and arrows are all part of the notation, which
     could equally well be written ` CondEq x y ph ` .  On the right side is
     the actual implication arrow.  The reason for this definition is to
     "flatten" the structure on the right side (whose tree structure is
     something like (wi (wceq (cv vx) (cv vy)) wph) ) into just (wcdeq vx vy
     wph).  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fdf-cdeq_0 $f wff ph $.
	fdf-cdeq_1 $f set x $.
	fdf-cdeq_2 $f set y $.
	df-cdeq $a |- ( CondEq ( x = y -> ph ) <-> ( x = y -> ph ) ) $.
$}
$( Deduce conditional equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fcdeqi_0 $f wff ph $.
	fcdeqi_1 $f set x $.
	fcdeqi_2 $f set y $.
	ecdeqi_0 $e |- ( x = y -> ph ) $.
	cdeqi $p |- CondEq ( x = y -> ph ) $= fcdeqi_0 fcdeqi_1 fcdeqi_2 wcdeq fcdeqi_1 sup_set_class fcdeqi_2 sup_set_class wceq fcdeqi_0 wi ecdeqi_0 fcdeqi_0 fcdeqi_1 fcdeqi_2 df-cdeq mpbir $.
$}
$( Property of conditional equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fcdeqri_0 $f wff ph $.
	fcdeqri_1 $f set x $.
	fcdeqri_2 $f set y $.
	ecdeqri_0 $e |- CondEq ( x = y -> ph ) $.
	cdeqri $p |- ( x = y -> ph ) $= fcdeqri_0 fcdeqri_1 fcdeqri_2 wcdeq fcdeqri_1 sup_set_class fcdeqri_2 sup_set_class wceq fcdeqri_0 wi ecdeqri_0 fcdeqri_0 fcdeqri_1 fcdeqri_2 df-cdeq mpbi $.
$}
$( Deduce conditional equality from a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fcdeqth_0 $f wff ph $.
	fcdeqth_1 $f set x $.
	fcdeqth_2 $f set y $.
	ecdeqth_0 $e |- ph $.
	cdeqth $p |- CondEq ( x = y -> ph ) $= fcdeqth_0 fcdeqth_1 fcdeqth_2 fcdeqth_0 fcdeqth_1 sup_set_class fcdeqth_2 sup_set_class wceq ecdeqth_0 a1i cdeqi $.
$}
$( Distribute conditional equality over negation.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	fcdeqnot_0 $f wff ph $.
	fcdeqnot_1 $f wff ps $.
	fcdeqnot_2 $f set x $.
	fcdeqnot_3 $f set y $.
	ecdeqnot_0 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	cdeqnot $p |- CondEq ( x = y -> ( -. ph <-> -. ps ) ) $= fcdeqnot_0 wn fcdeqnot_1 wn wb fcdeqnot_2 fcdeqnot_3 fcdeqnot_2 sup_set_class fcdeqnot_3 sup_set_class wceq fcdeqnot_0 fcdeqnot_1 fcdeqnot_0 fcdeqnot_1 wb fcdeqnot_2 fcdeqnot_3 ecdeqnot_0 cdeqri notbid cdeqi $.
$}
$( Distribute conditional equality over quantification.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fcdeqal_0 $f wff ph $.
	fcdeqal_1 $f wff ps $.
	fcdeqal_2 $f set x $.
	fcdeqal_3 $f set y $.
	fcdeqal_4 $f set z $.
	ecdeqal_0 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	cdeqal $p |- CondEq ( x = y -> ( A. z ph <-> A. z ps ) ) $= fcdeqal_0 fcdeqal_4 wal fcdeqal_1 fcdeqal_4 wal wb fcdeqal_2 fcdeqal_3 fcdeqal_2 sup_set_class fcdeqal_3 sup_set_class wceq fcdeqal_0 fcdeqal_1 fcdeqal_4 fcdeqal_0 fcdeqal_1 wb fcdeqal_2 fcdeqal_3 ecdeqal_0 cdeqri albidv cdeqi $.
$}
$( Distribute conditional equality over abstraction.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	fcdeqab_0 $f wff ph $.
	fcdeqab_1 $f wff ps $.
	fcdeqab_2 $f set x $.
	fcdeqab_3 $f set y $.
	fcdeqab_4 $f set z $.
	ecdeqab_0 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	cdeqab $p |- CondEq ( x = y -> { z | ph } = { z | ps } ) $= fcdeqab_0 fcdeqab_4 cab fcdeqab_1 fcdeqab_4 cab wceq fcdeqab_2 fcdeqab_3 fcdeqab_2 sup_set_class fcdeqab_3 sup_set_class wceq fcdeqab_0 fcdeqab_1 fcdeqab_4 fcdeqab_0 fcdeqab_1 wb fcdeqab_2 fcdeqab_3 ecdeqab_0 cdeqri abbidv cdeqi $.
$}
$( Distribute conditional equality over quantification.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ps $.
	$d y ph $.
	fcdeqal1_0 $f wff ph $.
	fcdeqal1_1 $f wff ps $.
	fcdeqal1_2 $f set x $.
	fcdeqal1_3 $f set y $.
	ecdeqal1_0 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	cdeqal1 $p |- CondEq ( x = y -> ( A. x ph <-> A. y ps ) ) $= fcdeqal1_0 fcdeqal1_2 wal fcdeqal1_1 fcdeqal1_3 wal wb fcdeqal1_2 fcdeqal1_3 fcdeqal1_0 fcdeqal1_2 wal fcdeqal1_1 fcdeqal1_3 wal wb fcdeqal1_2 sup_set_class fcdeqal1_3 sup_set_class wceq fcdeqal1_0 fcdeqal1_1 fcdeqal1_2 fcdeqal1_3 fcdeqal1_0 fcdeqal1_1 wb fcdeqal1_2 fcdeqal1_3 ecdeqal1_0 cdeqri cbvalv a1i cdeqi $.
$}
$( Distribute conditional equality over abstraction.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ps $.
	$d y ph $.
	fcdeqab1_0 $f wff ph $.
	fcdeqab1_1 $f wff ps $.
	fcdeqab1_2 $f set x $.
	fcdeqab1_3 $f set y $.
	ecdeqab1_0 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	cdeqab1 $p |- CondEq ( x = y -> { x | ph } = { y | ps } ) $= fcdeqab1_0 fcdeqab1_2 cab fcdeqab1_1 fcdeqab1_3 cab wceq fcdeqab1_2 fcdeqab1_3 fcdeqab1_0 fcdeqab1_2 cab fcdeqab1_1 fcdeqab1_3 cab wceq fcdeqab1_2 sup_set_class fcdeqab1_3 sup_set_class wceq fcdeqab1_0 fcdeqab1_1 fcdeqab1_2 fcdeqab1_3 fcdeqab1_0 fcdeqab1_1 wb fcdeqab1_2 fcdeqab1_3 ecdeqab1_0 cdeqri cbvabv a1i cdeqi $.
$}
$( Distribute conditional equality over implication.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v x $.
	$v y $.
	fcdeqim_0 $f wff ph $.
	fcdeqim_1 $f wff ps $.
	fcdeqim_2 $f wff ch $.
	fcdeqim_3 $f wff th $.
	fcdeqim_4 $f set x $.
	fcdeqim_5 $f set y $.
	ecdeqim_0 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	ecdeqim_1 $e |- CondEq ( x = y -> ( ch <-> th ) ) $.
	cdeqim $p |- CondEq ( x = y -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) $= fcdeqim_0 fcdeqim_2 wi fcdeqim_1 fcdeqim_3 wi wb fcdeqim_4 fcdeqim_5 fcdeqim_4 sup_set_class fcdeqim_5 sup_set_class wceq fcdeqim_0 fcdeqim_1 fcdeqim_2 fcdeqim_3 fcdeqim_0 fcdeqim_1 wb fcdeqim_4 fcdeqim_5 ecdeqim_0 cdeqri fcdeqim_2 fcdeqim_3 wb fcdeqim_4 fcdeqim_5 ecdeqim_1 cdeqri imbi12d cdeqi $.
$}
$( Conditional equality for set-to-class promotion.  (Contributed by Mario
     Carneiro, 11-Aug-2016.) $)
${
	$v x $.
	$v y $.
	fcdeqcv_0 $f set x $.
	fcdeqcv_1 $f set y $.
	cdeqcv $p |- CondEq ( x = y -> x = y ) $= fcdeqcv_0 sup_set_class fcdeqcv_1 sup_set_class wceq fcdeqcv_0 fcdeqcv_1 fcdeqcv_0 sup_set_class fcdeqcv_1 sup_set_class wceq id cdeqi $.
$}
$( Distribute conditional equality over equality.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fcdeqeq_0 $f set x $.
	fcdeqeq_1 $f set y $.
	fcdeqeq_2 $f class A $.
	fcdeqeq_3 $f class B $.
	fcdeqeq_4 $f class C $.
	fcdeqeq_5 $f class D $.
	ecdeqeq_0 $e |- CondEq ( x = y -> A = B ) $.
	ecdeqeq_1 $e |- CondEq ( x = y -> C = D ) $.
	cdeqeq $p |- CondEq ( x = y -> ( A = C <-> B = D ) ) $= fcdeqeq_2 fcdeqeq_4 wceq fcdeqeq_3 fcdeqeq_5 wceq wb fcdeqeq_0 fcdeqeq_1 fcdeqeq_0 sup_set_class fcdeqeq_1 sup_set_class wceq fcdeqeq_2 fcdeqeq_3 fcdeqeq_4 fcdeqeq_5 fcdeqeq_2 fcdeqeq_3 wceq fcdeqeq_0 fcdeqeq_1 ecdeqeq_0 cdeqri fcdeqeq_4 fcdeqeq_5 wceq fcdeqeq_0 fcdeqeq_1 ecdeqeq_1 cdeqri eqeq12d cdeqi $.
$}
$( Distribute conditional equality over elementhood.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fcdeqel_0 $f set x $.
	fcdeqel_1 $f set y $.
	fcdeqel_2 $f class A $.
	fcdeqel_3 $f class B $.
	fcdeqel_4 $f class C $.
	fcdeqel_5 $f class D $.
	ecdeqel_0 $e |- CondEq ( x = y -> A = B ) $.
	ecdeqel_1 $e |- CondEq ( x = y -> C = D ) $.
	cdeqel $p |- CondEq ( x = y -> ( A e. C <-> B e. D ) ) $= fcdeqel_2 fcdeqel_4 wcel fcdeqel_3 fcdeqel_5 wcel wb fcdeqel_0 fcdeqel_1 fcdeqel_0 sup_set_class fcdeqel_1 sup_set_class wceq fcdeqel_2 fcdeqel_3 fcdeqel_4 fcdeqel_5 fcdeqel_2 fcdeqel_3 wceq fcdeqel_0 fcdeqel_1 ecdeqel_0 cdeqri fcdeqel_4 fcdeqel_5 wceq fcdeqel_0 fcdeqel_1 ecdeqel_1 cdeqri eleq12d cdeqi $.
$}
$( If we have a conditional equality proof, where ` ph ` is ` ph ( x ) `
       and ` ps ` is ` ph ( y ) ` , and ` ph ( x ) ` in fact does not have
       ` x ` free in it according to ` F/ ` , then ` ph ( x ) <-> ph ( y ) `
       unconditionally.  This proves that ` F/ x ph ` is actually a not-free
       predicate.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ps $.
	$d y ph $.
	fnfcdeq_0 $f wff ph $.
	fnfcdeq_1 $f wff ps $.
	fnfcdeq_2 $f set x $.
	fnfcdeq_3 $f set y $.
	enfcdeq_0 $e |- F/ x ph $.
	enfcdeq_1 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	nfcdeq $p |- ( ph <-> ps ) $= fnfcdeq_0 fnfcdeq_0 fnfcdeq_2 fnfcdeq_3 wsb fnfcdeq_1 fnfcdeq_0 fnfcdeq_2 fnfcdeq_3 enfcdeq_0 sbf fnfcdeq_0 fnfcdeq_1 fnfcdeq_2 fnfcdeq_3 fnfcdeq_1 fnfcdeq_2 nfv fnfcdeq_0 fnfcdeq_1 wb fnfcdeq_2 fnfcdeq_3 enfcdeq_1 cdeqri sbie bitr3i $.
$}
$( Variation of ~ nfcdeq for classes.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v z $.
	$d x z B $.
	$d y z A $.
	infccdeq_0 $f set z $.
	fnfccdeq_0 $f set x $.
	fnfccdeq_1 $f set y $.
	fnfccdeq_2 $f class A $.
	fnfccdeq_3 $f class B $.
	enfccdeq_0 $e |- F/_ x A $.
	enfccdeq_1 $e |- CondEq ( x = y -> A = B ) $.
	nfccdeq $p |- A = B $= infccdeq_0 fnfccdeq_2 fnfccdeq_3 infccdeq_0 sup_set_class fnfccdeq_2 wcel infccdeq_0 sup_set_class fnfccdeq_3 wcel fnfccdeq_0 fnfccdeq_1 fnfccdeq_0 infccdeq_0 fnfccdeq_2 enfccdeq_0 nfcri fnfccdeq_0 fnfccdeq_1 infccdeq_0 sup_set_class infccdeq_0 sup_set_class fnfccdeq_2 fnfccdeq_3 infccdeq_0 sup_set_class infccdeq_0 sup_set_class wceq fnfccdeq_0 fnfccdeq_1 infccdeq_0 equid cdeqth enfccdeq_1 cdeqel nfcdeq eqriv $.
$}
$( Let the computer know the theorems to look for to prove the metatheorem $)
$( $j
    condequality 'wcdeq' from 'cdeqth';
    condcongruence 'cdeqnot' 'cdeqim' 'cdeqal1' 'cdeqal' 'cdeqcv' 'cdeqeq'
      'cdeqel' 'cdeqab1' 'cdeqab';
    notfree 'wnf' from 'nfcdeq';
    notfree 'wnfc' from 'nfccdeq';
  $)

