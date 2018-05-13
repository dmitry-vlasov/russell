$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_universal_class.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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

$c CondEq $.

$(conditional equality $)

$(Extend wff notation to include conditional equality.  This is a technical
     device used in the proof that ` F/ ` is the not-free predicate, and that
     definitions are conservative as a result. $)

${
	$v ph x y  $.
	f0_wcdeq $f wff ph $.
	f1_wcdeq $f set x $.
	f2_wcdeq $f set y $.
	a_wcdeq $a wff CondEq ( x = y -> ph ) $.
$}

$(Define conditional equality.  All the notation to the left of the ` <-> `
     is fake; the parentheses and arrows are all part of the notation, which
     could equally well be written ` CondEq x y ph ` .  On the right side is
     the actual implication arrow.  The reason for this definition is to
     "flatten" the structure on the right side (whose tree structure is
     something like (wi (wceq (cv vx) (cv vy)) wph) ) into just (wcdeq vx vy
     wph).  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_df-cdeq $f wff ph $.
	f1_df-cdeq $f set x $.
	f2_df-cdeq $f set y $.
	a_df-cdeq $a |- ( CondEq ( x = y -> ph ) <-> ( x = y -> ph ) ) $.
$}

$(Deduce conditional equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_cdeqi $f wff ph $.
	f1_cdeqi $f set x $.
	f2_cdeqi $f set y $.
	e0_cdeqi $e |- ( x = y -> ph ) $.
	p_cdeqi $p |- CondEq ( x = y -> ph ) $= e0_cdeqi f0_cdeqi f1_cdeqi f2_cdeqi a_df-cdeq f0_cdeqi f1_cdeqi f2_cdeqi a_wcdeq f1_cdeqi a_sup_set_class f2_cdeqi a_sup_set_class a_wceq f0_cdeqi a_wi p_mpbir $.
$}

$(Property of conditional equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_cdeqri $f wff ph $.
	f1_cdeqri $f set x $.
	f2_cdeqri $f set y $.
	e0_cdeqri $e |- CondEq ( x = y -> ph ) $.
	p_cdeqri $p |- ( x = y -> ph ) $= e0_cdeqri f0_cdeqri f1_cdeqri f2_cdeqri a_df-cdeq f0_cdeqri f1_cdeqri f2_cdeqri a_wcdeq f1_cdeqri a_sup_set_class f2_cdeqri a_sup_set_class a_wceq f0_cdeqri a_wi p_mpbi $.
$}

$(Deduce conditional equality from a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_cdeqth $f wff ph $.
	f1_cdeqth $f set x $.
	f2_cdeqth $f set y $.
	e0_cdeqth $e |- ph $.
	p_cdeqth $p |- CondEq ( x = y -> ph ) $= e0_cdeqth f0_cdeqth f1_cdeqth a_sup_set_class f2_cdeqth a_sup_set_class a_wceq p_a1i f0_cdeqth f1_cdeqth f2_cdeqth p_cdeqi $.
$}

$(Distribute conditional equality over negation.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x y  $.
	f0_cdeqnot $f wff ph $.
	f1_cdeqnot $f wff ps $.
	f2_cdeqnot $f set x $.
	f3_cdeqnot $f set y $.
	e0_cdeqnot $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	p_cdeqnot $p |- CondEq ( x = y -> ( -. ph <-> -. ps ) ) $= e0_cdeqnot f0_cdeqnot f1_cdeqnot a_wb f2_cdeqnot f3_cdeqnot p_cdeqri f2_cdeqnot a_sup_set_class f3_cdeqnot a_sup_set_class a_wceq f0_cdeqnot f1_cdeqnot p_notbid f0_cdeqnot a_wn f1_cdeqnot a_wn a_wb f2_cdeqnot f3_cdeqnot p_cdeqi $.
$}

$(Distribute conditional equality over quantification.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x y z  $.
	$d x z  $.
	$d y z  $.
	f0_cdeqal $f wff ph $.
	f1_cdeqal $f wff ps $.
	f2_cdeqal $f set x $.
	f3_cdeqal $f set y $.
	f4_cdeqal $f set z $.
	e0_cdeqal $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	p_cdeqal $p |- CondEq ( x = y -> ( A. z ph <-> A. z ps ) ) $= e0_cdeqal f0_cdeqal f1_cdeqal a_wb f2_cdeqal f3_cdeqal p_cdeqri f2_cdeqal a_sup_set_class f3_cdeqal a_sup_set_class a_wceq f0_cdeqal f1_cdeqal f4_cdeqal p_albidv f0_cdeqal f4_cdeqal a_wal f1_cdeqal f4_cdeqal a_wal a_wb f2_cdeqal f3_cdeqal p_cdeqi $.
$}

$(Distribute conditional equality over abstraction.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x y z  $.
	$d x z  $.
	$d y z  $.
	f0_cdeqab $f wff ph $.
	f1_cdeqab $f wff ps $.
	f2_cdeqab $f set x $.
	f3_cdeqab $f set y $.
	f4_cdeqab $f set z $.
	e0_cdeqab $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	p_cdeqab $p |- CondEq ( x = y -> { z | ph } = { z | ps } ) $= e0_cdeqab f0_cdeqab f1_cdeqab a_wb f2_cdeqab f3_cdeqab p_cdeqri f2_cdeqab a_sup_set_class f3_cdeqab a_sup_set_class a_wceq f0_cdeqab f1_cdeqab f4_cdeqab p_abbidv f0_cdeqab f4_cdeqab a_cab f1_cdeqab f4_cdeqab a_cab a_wceq f2_cdeqab f3_cdeqab p_cdeqi $.
$}

$(Distribute conditional equality over quantification.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	$d y ph  $.
	f0_cdeqal1 $f wff ph $.
	f1_cdeqal1 $f wff ps $.
	f2_cdeqal1 $f set x $.
	f3_cdeqal1 $f set y $.
	e0_cdeqal1 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	p_cdeqal1 $p |- CondEq ( x = y -> ( A. x ph <-> A. y ps ) ) $= e0_cdeqal1 f0_cdeqal1 f1_cdeqal1 a_wb f2_cdeqal1 f3_cdeqal1 p_cdeqri f0_cdeqal1 f1_cdeqal1 f2_cdeqal1 f3_cdeqal1 p_cbvalv f0_cdeqal1 f2_cdeqal1 a_wal f1_cdeqal1 f3_cdeqal1 a_wal a_wb f2_cdeqal1 a_sup_set_class f3_cdeqal1 a_sup_set_class a_wceq p_a1i f0_cdeqal1 f2_cdeqal1 a_wal f1_cdeqal1 f3_cdeqal1 a_wal a_wb f2_cdeqal1 f3_cdeqal1 p_cdeqi $.
$}

$(Distribute conditional equality over abstraction.  (Contributed by
         Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	$d y ph  $.
	f0_cdeqab1 $f wff ph $.
	f1_cdeqab1 $f wff ps $.
	f2_cdeqab1 $f set x $.
	f3_cdeqab1 $f set y $.
	e0_cdeqab1 $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	p_cdeqab1 $p |- CondEq ( x = y -> { x | ph } = { y | ps } ) $= e0_cdeqab1 f0_cdeqab1 f1_cdeqab1 a_wb f2_cdeqab1 f3_cdeqab1 p_cdeqri f0_cdeqab1 f1_cdeqab1 f2_cdeqab1 f3_cdeqab1 p_cbvabv f0_cdeqab1 f2_cdeqab1 a_cab f1_cdeqab1 f3_cdeqab1 a_cab a_wceq f2_cdeqab1 a_sup_set_class f3_cdeqab1 a_sup_set_class a_wceq p_a1i f0_cdeqab1 f2_cdeqab1 a_cab f1_cdeqab1 f3_cdeqab1 a_cab a_wceq f2_cdeqab1 f3_cdeqab1 p_cdeqi $.
$}

$(Distribute conditional equality over implication.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v ph ps ch th x y  $.
	f0_cdeqim $f wff ph $.
	f1_cdeqim $f wff ps $.
	f2_cdeqim $f wff ch $.
	f3_cdeqim $f wff th $.
	f4_cdeqim $f set x $.
	f5_cdeqim $f set y $.
	e0_cdeqim $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	e1_cdeqim $e |- CondEq ( x = y -> ( ch <-> th ) ) $.
	p_cdeqim $p |- CondEq ( x = y -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) $= e0_cdeqim f0_cdeqim f1_cdeqim a_wb f4_cdeqim f5_cdeqim p_cdeqri e1_cdeqim f2_cdeqim f3_cdeqim a_wb f4_cdeqim f5_cdeqim p_cdeqri f4_cdeqim a_sup_set_class f5_cdeqim a_sup_set_class a_wceq f0_cdeqim f1_cdeqim f2_cdeqim f3_cdeqim p_imbi12d f0_cdeqim f2_cdeqim a_wi f1_cdeqim f3_cdeqim a_wi a_wb f4_cdeqim f5_cdeqim p_cdeqi $.
$}

$(Conditional equality for set-to-class promotion.  (Contributed by Mario
     Carneiro, 11-Aug-2016.) $)

${
	$v x y  $.
	f0_cdeqcv $f set x $.
	f1_cdeqcv $f set y $.
	p_cdeqcv $p |- CondEq ( x = y -> x = y ) $= f0_cdeqcv a_sup_set_class f1_cdeqcv a_sup_set_class a_wceq p_id f0_cdeqcv a_sup_set_class f1_cdeqcv a_sup_set_class a_wceq f0_cdeqcv f1_cdeqcv p_cdeqi $.
$}

$(Distribute conditional equality over equality.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v x y A B C D  $.
	f0_cdeqeq $f set x $.
	f1_cdeqeq $f set y $.
	f2_cdeqeq $f class A $.
	f3_cdeqeq $f class B $.
	f4_cdeqeq $f class C $.
	f5_cdeqeq $f class D $.
	e0_cdeqeq $e |- CondEq ( x = y -> A = B ) $.
	e1_cdeqeq $e |- CondEq ( x = y -> C = D ) $.
	p_cdeqeq $p |- CondEq ( x = y -> ( A = C <-> B = D ) ) $= e0_cdeqeq f2_cdeqeq f3_cdeqeq a_wceq f0_cdeqeq f1_cdeqeq p_cdeqri e1_cdeqeq f4_cdeqeq f5_cdeqeq a_wceq f0_cdeqeq f1_cdeqeq p_cdeqri f0_cdeqeq a_sup_set_class f1_cdeqeq a_sup_set_class a_wceq f2_cdeqeq f3_cdeqeq f4_cdeqeq f5_cdeqeq p_eqeq12d f2_cdeqeq f4_cdeqeq a_wceq f3_cdeqeq f5_cdeqeq a_wceq a_wb f0_cdeqeq f1_cdeqeq p_cdeqi $.
$}

$(Distribute conditional equality over elementhood.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v x y A B C D  $.
	f0_cdeqel $f set x $.
	f1_cdeqel $f set y $.
	f2_cdeqel $f class A $.
	f3_cdeqel $f class B $.
	f4_cdeqel $f class C $.
	f5_cdeqel $f class D $.
	e0_cdeqel $e |- CondEq ( x = y -> A = B ) $.
	e1_cdeqel $e |- CondEq ( x = y -> C = D ) $.
	p_cdeqel $p |- CondEq ( x = y -> ( A e. C <-> B e. D ) ) $= e0_cdeqel f2_cdeqel f3_cdeqel a_wceq f0_cdeqel f1_cdeqel p_cdeqri e1_cdeqel f4_cdeqel f5_cdeqel a_wceq f0_cdeqel f1_cdeqel p_cdeqri f0_cdeqel a_sup_set_class f1_cdeqel a_sup_set_class a_wceq f2_cdeqel f3_cdeqel f4_cdeqel f5_cdeqel p_eleq12d f2_cdeqel f4_cdeqel a_wcel f3_cdeqel f5_cdeqel a_wcel a_wb f0_cdeqel f1_cdeqel p_cdeqi $.
$}

$(If we have a conditional equality proof, where ` ph ` is ` ph ( x ) `
       and ` ps ` is ` ph ( y ) ` , and ` ph ( x ) ` in fact does not have
       ` x ` free in it according to ` F/ ` , then ` ph ( x ) <-> ph ( y ) `
       unconditionally.  This proves that ` F/ x ph ` is actually a not-free
       predicate.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	$d y ph  $.
	f0_nfcdeq $f wff ph $.
	f1_nfcdeq $f wff ps $.
	f2_nfcdeq $f set x $.
	f3_nfcdeq $f set y $.
	e0_nfcdeq $e |- F/ x ph $.
	e1_nfcdeq $e |- CondEq ( x = y -> ( ph <-> ps ) ) $.
	p_nfcdeq $p |- ( ph <-> ps ) $= e0_nfcdeq f0_nfcdeq f2_nfcdeq f3_nfcdeq p_sbf f1_nfcdeq f2_nfcdeq p_nfv e1_nfcdeq f0_nfcdeq f1_nfcdeq a_wb f2_nfcdeq f3_nfcdeq p_cdeqri f0_nfcdeq f1_nfcdeq f2_nfcdeq f3_nfcdeq p_sbie f0_nfcdeq f0_nfcdeq f2_nfcdeq f3_nfcdeq a_wsb f1_nfcdeq p_bitr3i $.
$}

$(Variation of ~ nfcdeq for classes.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v x y A B  $.
	$d x z B  $.
	$d y z A  $.
	f0_nfccdeq $f set x $.
	f1_nfccdeq $f set y $.
	f2_nfccdeq $f class A $.
	f3_nfccdeq $f class B $.
	i0_nfccdeq $f set z $.
	e0_nfccdeq $e |- F/_ x A $.
	e1_nfccdeq $e |- CondEq ( x = y -> A = B ) $.
	p_nfccdeq $p |- A = B $= e0_nfccdeq f0_nfccdeq i0_nfccdeq f2_nfccdeq p_nfcri i0_nfccdeq p_equid i0_nfccdeq a_sup_set_class i0_nfccdeq a_sup_set_class a_wceq f0_nfccdeq f1_nfccdeq p_cdeqth e1_nfccdeq f0_nfccdeq f1_nfccdeq i0_nfccdeq a_sup_set_class i0_nfccdeq a_sup_set_class f2_nfccdeq f3_nfccdeq p_cdeqel i0_nfccdeq a_sup_set_class f2_nfccdeq a_wcel i0_nfccdeq a_sup_set_class f3_nfccdeq a_wcel f0_nfccdeq f1_nfccdeq p_nfcdeq i0_nfccdeq f2_nfccdeq f3_nfccdeq p_eqriv $.
$}

$(Let the computer know the theorems to look for to prove the metatheorem $)

$($j
    condequality 'wcdeq' from 'cdeqth';
    condcongruence 'cdeqnot' 'cdeqim' 'cdeqal1' 'cdeqal' 'cdeqcv' 'cdeqeq'
      'cdeqel' 'cdeqab1' 'cdeqab';
    notfree 'wnf' from 'nfcdeq';
    notfree 'wnfc' from 'nfccdeq';
  $)


