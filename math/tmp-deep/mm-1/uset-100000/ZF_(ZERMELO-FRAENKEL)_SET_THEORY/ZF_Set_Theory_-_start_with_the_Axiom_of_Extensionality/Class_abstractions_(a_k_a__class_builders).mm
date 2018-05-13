$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Introduce_the_Axiom_of_Extensionality.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Class abstractions (a.k.a. class builders)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare new constants use in class definition. $)

$c { $.

$(Left brace $)

$c | $.

$(Vertical bar $)

$c } $.

$(Right brace $)

$(--- Start of old code before overloading prevention patch. $)

$(@c class @. @( Class variable type @)
  $)

$(--- End of old code before overloading prevention patch. $)

$(Declare symbols as variables $)

$(Declare variable symbols that will be used to represent classes.  Note
     that later on ` R ` , ` S ` , ` F ` and ` G ` denote relations and
     functions, but these letters serve as mnemonics only and in fact behave
     no differently from the variables ` A ` through ` D ` . $)

$(Introduce the class builder or class abstraction notation ("the class of
     sets ` x ` such that ` ph ` is true").  Our class variables ` A ` ,
     ` B ` , etc. range over class builders (implicitly in the case of defined
     class terms such as ~ df-nul ).  Note that a set variable can be expressed
     as a class builder per theorem ~ cvjust , justifying the assignment of set
     variables to class variables via the use of ~ cv . $)

${
	$v ph x  $.
	f0_cab $f wff ph $.
	f1_cab $f set x $.
	a_cab $a class { x | ph } $.
$}

$(--- Start of old code before overloading prevention patch. $)

$(@( A set variable is a class expression.  The syntax " ` class x ` " can be
     viewed as an abbreviation for " ` class { y | y e. x } ` " (a special case
     of ~ cab ), where ` y ` is distinct from ` x ` .  See the discussion under
     the definition of class in [Jech] p. 4.  Note that ` { y | y e. x } = x `
     by ~ cvjust . @)
  cv @a class x @.
  $)

$(--- End of old code before overloading prevention patch. $)

$($j primitive 'cv' 'wceq' 'wcel' 'cab'; $)

$(Let ` A ` be a class variable. $)

$(Let ` B ` be a class variable. $)

$(Let ` C ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` D ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` P ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` Q ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` R ` be a class variable. $)

$(Let ` S ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` T ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` U ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` e ` be an individual variable. $)

$(Let ` f ` be an individual variable. $)

$(Let ` g ` be an individual variable. $)

$(Let ` h ` be an individual variable. $)

$(Let ` i ` be an individual variable. $)

$(Let ` j ` be an individual variable. $)

$(Let ` k ` be an individual variable. $)

$(Let ` m ` be an individual variable. $)

$(Let ` n ` be an individual variable. $)

$(Let ` o ` be an individual variable. $)

$(Let ` E ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` F ` be a class variable. $)

$(Let ` G ` be a class variable. $)

$(Let ` H ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` I ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` J ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` K ` be a class variable. $)

$(Let ` L ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` M ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` N ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` O ` be a class variable. $)

$(Let ` V ` be a class variable. $)

$(Let ` W ` be a class variable. $)

$(Let ` X ` be a class variable. $)

$(Let ` Y ` be a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Define a connective symbol for use as a class variable. $)

$(Let ` Z ` be a class variable. $)

$(Let ` s ` be an individual variable. $)

$(Let ` r ` be an individual variable. $)

$(Let ` q ` be an individual variable. $)

$(Let ` p ` be an individual variable. $)

$(Let ` a ` be an individual variable. $)

$(Let ` b ` be an individual variable. $)

$(Let ` c ` be an individual variable. $)

$(Let ` d ` be an individual variable. $)

$(Let ` l ` be an individual variable. $)

$(--- Start of old code before overloading prevention patch. $)

$(@( Extend wff definition to include class equality. @)
  wceq @a wff A = B @.
  $)

$(--- End of old code before overloading prevention patch. $)

$(--- Start of old code before overloading prevention patch. $)

$(@( Extend wff definition to include the membership connective between
     classes. @)
  wcel @a wff A e. B @.
  $)

$(--- End of old code before overloading prevention patch. $)

$(Define class abstraction notation (so-called by Quine), also called a
     "class builder" in the literature. ` x ` and ` y ` need not be distinct.
     Definition 2.1 of [Quine] p. 16.  Typically, ` ph ` will have ` y ` as a
     free variable, and " ` { y | ph } ` " is read "the class of all sets ` y `
     such that ` ph ( y ) ` is true."  We do not define ` { y | ph } ` in
     isolation but only as part of an expression that extends or "overloads"
     the ` e. ` relationship.

     This is our first use of the ` e. ` symbol to connect classes instead of
     sets.  The syntax definition ~ wcel , which extends or "overloads" the
     ~ wel definition connecting set variables, requires that both sides of
     ` e. ` be a class.  In ~ df-cleq and ~ df-clel , we introduce a new kind
     of variable (class variable) that can substituted with expressions such as
     ` { y | ph } ` .  In the present definition, the ` x ` on the left-hand
     side is a set variable.  Syntax definition ~ cv allows us to substitute a
     set variable ` x ` for a class variable: all sets are classes by ~ cvjust
     (but not necessarily vice-versa).  For a full description of how classes
     are introduced and how to recover the primitive language, see the
     discussion in Quine (and under ~ abeq2 for a quick overview).

     Because class variables can be substituted with compound expressions and
     set variables cannot, it is often useful to convert a theorem containing a
     free set variable to a more general version with a class variable.  This
     is done with theorems such as ~ vtoclg which is used, for example, to
     convert ~ elirrv to ~ elirr .

     This is called the "axiom of class comprehension" by [Levy] p. 338, who
     treats the theory of classes as an extralogical extension to our logic and
     set theory axioms.  He calls the construction ` { y | ph } ` a "class
     term".

     For a general discussion of the theory of classes, see
     ~ http://us.metamath.org/mpeuni/mmset.html#class .  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_df-clab $f wff ph $.
	f1_df-clab $f set x $.
	f2_df-clab $f set y $.
	a_df-clab $a |- ( x e. { y | ph } <-> [ x / y ] ph ) $.
$}

$(Simplification of class abstraction notation when the free and bound
     variables are identical.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_abid $f wff ph $.
	f1_abid $f set x $.
	p_abid $p |- ( x e. { x | ph } <-> ph ) $= f0_abid f1_abid f1_abid a_df-clab f0_abid f1_abid p_sbid f1_abid a_sup_set_class f0_abid f1_abid a_cab a_wcel f0_abid f1_abid f1_abid a_wsb f0_abid p_bitri $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_hbab1 $f wff ph $.
	f1_hbab1 $f set x $.
	f2_hbab1 $f set y $.
	p_hbab1 $p |- ( y e. { x | ph } -> A. x y e. { x | ph } ) $= f0_hbab1 f2_hbab1 f1_hbab1 a_df-clab f0_hbab1 f1_hbab1 f2_hbab1 p_hbs1 f2_hbab1 a_sup_set_class f0_hbab1 f1_hbab1 a_cab a_wcel f0_hbab1 f1_hbab1 f2_hbab1 a_wsb f1_hbab1 p_hbxfrbi $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_nfsab1 $f wff ph $.
	f1_nfsab1 $f set x $.
	f2_nfsab1 $f set y $.
	p_nfsab1 $p |- F/ x y e. { x | ph } $= f0_nfsab1 f1_nfsab1 f2_nfsab1 p_hbab1 f2_nfsab1 a_sup_set_class f0_nfsab1 f1_nfsab1 a_cab a_wcel f1_nfsab1 p_nfi $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by NM, 1-Mar-1995.) $)

${
	$v ph x y z  $.
	$d x z  $.
	f0_hbab $f wff ph $.
	f1_hbab $f set x $.
	f2_hbab $f set y $.
	f3_hbab $f set z $.
	e0_hbab $e |- ( ph -> A. x ph ) $.
	p_hbab $p |- ( z e. { y | ph } -> A. x z e. { y | ph } ) $= f0_hbab f3_hbab f2_hbab a_df-clab e0_hbab f0_hbab f2_hbab f3_hbab f1_hbab p_hbsb f3_hbab a_sup_set_class f0_hbab f2_hbab a_cab a_wcel f0_hbab f2_hbab f3_hbab a_wsb f1_hbab p_hbxfrbi $.
$}

$(Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y z  $.
	$d x z  $.
	f0_nfsab $f wff ph $.
	f1_nfsab $f set x $.
	f2_nfsab $f set y $.
	f3_nfsab $f set z $.
	e0_nfsab $e |- F/ x ph $.
	p_nfsab $p |- F/ x z e. { y | ph } $= e0_nfsab f0_nfsab f1_nfsab p_nfri f0_nfsab f1_nfsab f2_nfsab f3_nfsab p_hbab f3_nfsab a_sup_set_class f0_nfsab f2_nfsab a_cab a_wcel f1_nfsab p_nfi $.
$}

$(Define the equality connective between classes.  Definition 2.7 of
       [Quine] p. 18.  Also Definition 4.5 of [TakeutiZaring] p. 13; Chapter 4
       provides its justification and methods for eliminating it.  Note that
       its elimination will not necessarily result in a single wff in the
       original language but possibly a "scheme" of wffs.

       This is an example of a somewhat "risky" definition, meaning that it has
       a more complex than usual soundness justification (outside of Metamath),
       because it "overloads" or reuses the existing equality symbol rather
       than introducing a new symbol.  This allows us to make statements that
       may not hold for the original symbol.  For example, it permits us to
       deduce ` y = z <-> A. x ( x e. y <-> x e. z ) ` , which is not a theorem
       of logic but rather presupposes the Axiom of Extensionality (see theorem
       ~ axext4 ).  We therefore include this axiom as a hypothesis, so that
       the use of Extensionality is properly indicated.

       We could avoid this complication by introducing a new symbol, say =_2,
       in place of ` = ` .  This would also have the advantage of making
       elimination of the definition straightforward, so that we could
       eliminate Extensionality as a hypothesis.  We would then also have the
       advantage of being able to identify in various proofs exactly where
       Extensionality truly comes into play rather than just being an artifact
       of a definition.  One of our theorems would then be ` x ` =_2
       ` y <-> x = y ` by invoking Extensionality.

       However, to conform to literature usage, we retain this overloaded
       definition.  This also makes some proofs shorter and probably easier to
       read, without the constant switching between two kinds of equality.

       See also comments under ~ df-clab , ~ df-clel , and ~ abeq2 .

       In the form of ~ dfcleq , this is called the "axiom of extensionality"
       by [Levy] p. 338, who treats the theory of classes as an extralogical
       extension to our logic and set theory axioms.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .  (Contributed by NM,
       15-Sep-1993.) $)

${
	$v x y z A B  $.
	$d x A  $.
	$d x B  $.
	$d x y z  $.
	f0_df-cleq $f set x $.
	f1_df-cleq $f set y $.
	f2_df-cleq $f set z $.
	f3_df-cleq $f class A $.
	f4_df-cleq $f class B $.
	e0_df-cleq $e |- ( A. x ( x e. y <-> x e. z ) -> y = z ) $.
	a_df-cleq $a |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $.
$}

$(The same as ~ df-cleq with the hypothesis removed using the Axiom of
       Extensionality ~ ax-ext .  (Contributed by NM, 15-Sep-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	$d x y z  $.
	f0_dfcleq $f set x $.
	f1_dfcleq $f class A $.
	f2_dfcleq $f class B $.
	i0_dfcleq $f set y $.
	i1_dfcleq $f set z $.
	p_dfcleq $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $= i0_dfcleq i1_dfcleq f0_dfcleq a_ax-ext f0_dfcleq i0_dfcleq i1_dfcleq f1_dfcleq f2_dfcleq a_df-cleq $.
$}

$(Every set is a class.  Proposition 4.9 of [TakeutiZaring] p. 13.  This
       theorem shows that a set variable can be expressed as a class
       abstraction.  This provides a motivation for the class syntax
       construction ~ cv , which allows us to substitute a set variable for a
       class variable.  See also ~ cab and ~ df-clab .  Note that this is not a
       rigorous justification, because ~ cv is used as part of the proof of
       this theorem, but a careful argument can be made outside of the
       formalism of Metamath, for example as is done in Chapter 4 of Takeuti
       and Zaring.  See also the discussion under the definition of class in
       [Jech] p. 4 showing that "Every set can be considered to be a class."
       (Contributed by NM, 7-Nov-2006.) $)

${
	$v x y  $.
	$d x y z  $.
	f0_cvjust $f set x $.
	f1_cvjust $f set y $.
	i0_cvjust $f set z $.
	p_cvjust $p |- x = { y | y e. x } $= i0_cvjust f0_cvjust a_sup_set_class f1_cvjust a_sup_set_class f0_cvjust a_sup_set_class a_wcel f1_cvjust a_cab p_dfcleq f1_cvjust a_sup_set_class f0_cvjust a_sup_set_class a_wcel i0_cvjust f1_cvjust a_df-clab i0_cvjust f1_cvjust f0_cvjust p_elsb3 i0_cvjust a_sup_set_class f1_cvjust a_sup_set_class f0_cvjust a_sup_set_class a_wcel f1_cvjust a_cab a_wcel f1_cvjust a_sup_set_class f0_cvjust a_sup_set_class a_wcel f1_cvjust i0_cvjust a_wsb i0_cvjust a_sup_set_class f0_cvjust a_sup_set_class a_wcel p_bitr2i f0_cvjust a_sup_set_class f1_cvjust a_sup_set_class f0_cvjust a_sup_set_class a_wcel f1_cvjust a_cab a_wceq i0_cvjust a_sup_set_class f0_cvjust a_sup_set_class a_wcel i0_cvjust a_sup_set_class f1_cvjust a_sup_set_class f0_cvjust a_sup_set_class a_wcel f1_cvjust a_cab a_wcel a_wb i0_cvjust p_mpgbir $.
$}

$(Define the membership connective between classes.  Theorem 6.3 of
       [Quine] p. 41, or Proposition 4.6 of [TakeutiZaring] p. 13, which we
       adopt as a definition.  See these references for its metalogical
       justification.  Note that like ~ df-cleq it extends or "overloads" the
       use of the existing membership symbol, but unlike ~ df-cleq it does not
       strengthen the set of valid wffs of logic when the class variables are
       replaced with set variables (see ~ cleljust ), so we don't include any
       set theory axiom as a hypothesis.  See also comments about the syntax
       under ~ df-clab .  Alternate definitions of ` A e. B ` (but that require
       either ` A ` or ` B ` to be a set) are shown by ~ clel2 , ~ clel3 , and
       ~ clel4 .

       This is called the "axiom of membership" by [Levy] p. 338, who treats
       the theory of classes as an extralogical extension to our logic and set
       theory axioms.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_df-clel $f set x $.
	f1_df-clel $f class A $.
	f2_df-clel $f class B $.
	a_df-clel $a |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $.
$}

$(Infer equality of classes from equivalence of membership.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_eqriv $f set x $.
	f1_eqriv $f class A $.
	f2_eqriv $f class B $.
	e0_eqriv $e |- ( x e. A <-> x e. B ) $.
	p_eqriv $p |- A = B $= f0_eqriv f1_eqriv f2_eqriv p_dfcleq e0_eqriv f1_eqriv f2_eqriv a_wceq f0_eqriv a_sup_set_class f1_eqriv a_wcel f0_eqriv a_sup_set_class f2_eqriv a_wcel a_wb f0_eqriv p_mpgbir $.
$}

$(Deduce equality of classes from equivalence of membership.  (Contributed
       by NM, 17-Mar-1996.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_eqrdv $f wff ph $.
	f1_eqrdv $f set x $.
	f2_eqrdv $f class A $.
	f3_eqrdv $f class B $.
	e0_eqrdv $e |- ( ph -> ( x e. A <-> x e. B ) ) $.
	p_eqrdv $p |- ( ph -> A = B ) $= e0_eqrdv f0_eqrdv f1_eqrdv a_sup_set_class f2_eqrdv a_wcel f1_eqrdv a_sup_set_class f3_eqrdv a_wcel a_wb f1_eqrdv p_alrimiv f1_eqrdv f2_eqrdv f3_eqrdv p_dfcleq f0_eqrdv f1_eqrdv a_sup_set_class f2_eqrdv a_wcel f1_eqrdv a_sup_set_class f3_eqrdv a_wcel a_wb f1_eqrdv a_wal f2_eqrdv f3_eqrdv a_wceq p_sylibr $.
$}

$(Deduce equality of classes from an equivalence of membership that
       depends on the membership variable.  (Contributed by NM, 7-Nov-2008.) $)

${
	$v ph x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_eqrdav $f wff ph $.
	f1_eqrdav $f set x $.
	f2_eqrdav $f class A $.
	f3_eqrdav $f class B $.
	f4_eqrdav $f class C $.
	e0_eqrdav $e |- ( ( ph /\ x e. A ) -> x e. C ) $.
	e1_eqrdav $e |- ( ( ph /\ x e. B ) -> x e. C ) $.
	e2_eqrdav $e |- ( ( ph /\ x e. C ) -> ( x e. A <-> x e. B ) ) $.
	p_eqrdav $p |- ( ph -> A = B ) $= e0_eqrdav e2_eqrdav f0_eqrdav f1_eqrdav a_sup_set_class f4_eqrdav a_wcel a_wa f1_eqrdav a_sup_set_class f2_eqrdav a_wcel f1_eqrdav a_sup_set_class f3_eqrdav a_wcel p_biimpd f0_eqrdav f1_eqrdav a_sup_set_class f4_eqrdav a_wcel f1_eqrdav a_sup_set_class f2_eqrdav a_wcel f1_eqrdav a_sup_set_class f3_eqrdav a_wcel p_impancom f0_eqrdav f1_eqrdav a_sup_set_class f2_eqrdav a_wcel a_wa f1_eqrdav a_sup_set_class f4_eqrdav a_wcel f1_eqrdav a_sup_set_class f3_eqrdav a_wcel p_mpd e1_eqrdav e2_eqrdav f0_eqrdav f1_eqrdav a_sup_set_class f4_eqrdav a_wcel f1_eqrdav a_sup_set_class f2_eqrdav a_wcel f1_eqrdav a_sup_set_class f3_eqrdav a_wcel p_exbiri f0_eqrdav f1_eqrdav a_sup_set_class f4_eqrdav a_wcel f1_eqrdav a_sup_set_class f3_eqrdav a_wcel f1_eqrdav a_sup_set_class f2_eqrdav a_wcel p_com23 f0_eqrdav f1_eqrdav a_sup_set_class f3_eqrdav a_wcel f1_eqrdav a_sup_set_class f4_eqrdav a_wcel f1_eqrdav a_sup_set_class f2_eqrdav a_wcel a_wi p_imp f0_eqrdav f1_eqrdav a_sup_set_class f3_eqrdav a_wcel a_wa f1_eqrdav a_sup_set_class f4_eqrdav a_wcel f1_eqrdav a_sup_set_class f2_eqrdav a_wcel p_mpd f0_eqrdav f1_eqrdav a_sup_set_class f2_eqrdav a_wcel f1_eqrdav a_sup_set_class f3_eqrdav a_wcel p_impbida f0_eqrdav f1_eqrdav f2_eqrdav f3_eqrdav p_eqrdv $.
$}

$(Law of identity (reflexivity of class equality).  Theorem 6.4 of [Quine]
       p. 41.

       This law is thought to have originated with Aristotle (_Metaphysics_,
       Zeta, 17, 1041 a, 10-20:  "Therefore, inquiring why a thing is itself,
       it's inquiring nothing; ... saying that the thing is itself constitutes
       the sole reasoning and the sole cause, in every case, to the question of
       why the man is man or the musician musician.").  (Thanks to Stefan Allan
       and Beno&icirc;t Jubin for this information.)  (Contributed by NM,
       5-Aug-1993.)  (Revised by Beno&icirc;t Jubin, 14-Oct-2017.) $)

${
	$v A  $.
	$d x A  $.
	f0_eqid $f class A $.
	i0_eqid $f set x $.
	p_eqid $p |- A = A $= i0_eqid a_sup_set_class f0_eqid a_wcel p_biid i0_eqid f0_eqid f0_eqid p_eqriv $.
$}

$(Class identity law with antecedent.  (Contributed by NM, 21-Aug-2008.) $)

${
	$v ph A  $.
	f0_eqidd $f wff ph $.
	f1_eqidd $f class A $.
	p_eqidd $p |- ( ph -> A = A ) $= f1_eqidd p_eqid f1_eqidd f1_eqidd a_wceq f0_eqidd p_a1i $.
$}

$(Commutative law for class equality.  Theorem 6.5 of [Quine] p. 41.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_eqcom $f class A $.
	f1_eqcom $f class B $.
	i0_eqcom $f set x $.
	p_eqcom $p |- ( A = B <-> B = A ) $= i0_eqcom a_sup_set_class f0_eqcom a_wcel i0_eqcom a_sup_set_class f1_eqcom a_wcel p_bicom i0_eqcom a_sup_set_class f0_eqcom a_wcel i0_eqcom a_sup_set_class f1_eqcom a_wcel a_wb i0_eqcom a_sup_set_class f1_eqcom a_wcel i0_eqcom a_sup_set_class f0_eqcom a_wcel a_wb i0_eqcom p_albii i0_eqcom f0_eqcom f1_eqcom p_dfcleq i0_eqcom f1_eqcom f0_eqcom p_dfcleq i0_eqcom a_sup_set_class f0_eqcom a_wcel i0_eqcom a_sup_set_class f1_eqcom a_wcel a_wb i0_eqcom a_wal i0_eqcom a_sup_set_class f1_eqcom a_wcel i0_eqcom a_sup_set_class f0_eqcom a_wcel a_wb i0_eqcom a_wal f0_eqcom f1_eqcom a_wceq f1_eqcom f0_eqcom a_wceq p_3bitr4i $.
$}

$(Inference applying commutative law for class equality to an antecedent.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph A B  $.
	f0_eqcoms $f wff ph $.
	f1_eqcoms $f class A $.
	f2_eqcoms $f class B $.
	e0_eqcoms $e |- ( A = B -> ph ) $.
	p_eqcoms $p |- ( B = A -> ph ) $= f2_eqcoms f1_eqcoms p_eqcom e0_eqcoms f2_eqcoms f1_eqcoms a_wceq f1_eqcoms f2_eqcoms a_wceq f0_eqcoms p_sylbi $.
$}

$(Inference from commutative law for class equality.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v A B  $.
	f0_eqcomi $f class A $.
	f1_eqcomi $f class B $.
	e0_eqcomi $e |- A = B $.
	p_eqcomi $p |- B = A $= e0_eqcomi f0_eqcomi f1_eqcomi p_eqcom f0_eqcomi f1_eqcomi a_wceq f1_eqcomi f0_eqcomi a_wceq p_mpbi $.
$}

$(Deduction from commutative law for class equality.  (Contributed by NM,
       15-Aug-1994.) $)

${
	$v ph A B  $.
	f0_eqcomd $f wff ph $.
	f1_eqcomd $f class A $.
	f2_eqcomd $f class B $.
	e0_eqcomd $e |- ( ph -> A = B ) $.
	p_eqcomd $p |- ( ph -> B = A ) $= e0_eqcomd f1_eqcomd f2_eqcomd p_eqcom f0_eqcomd f1_eqcomd f2_eqcomd a_wceq f2_eqcomd f1_eqcomd a_wceq p_sylib $.
$}

$(Equality implies equivalence of equalities.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_eqeq1 $f class A $.
	f1_eqeq1 $f class B $.
	f2_eqeq1 $f class C $.
	i0_eqeq1 $f set x $.
	p_eqeq1 $p |- ( A = B -> ( A = C <-> B = C ) ) $= i0_eqeq1 f0_eqeq1 f1_eqeq1 p_dfcleq f0_eqeq1 f1_eqeq1 a_wceq i0_eqeq1 a_sup_set_class f0_eqeq1 a_wcel i0_eqeq1 a_sup_set_class f1_eqeq1 a_wcel a_wb i0_eqeq1 a_wal p_biimpi f0_eqeq1 f1_eqeq1 a_wceq i0_eqeq1 a_sup_set_class f0_eqeq1 a_wcel i0_eqeq1 a_sup_set_class f1_eqeq1 a_wcel a_wb i0_eqeq1 p_19.21bi f0_eqeq1 f1_eqeq1 a_wceq i0_eqeq1 a_sup_set_class f0_eqeq1 a_wcel i0_eqeq1 a_sup_set_class f1_eqeq1 a_wcel i0_eqeq1 a_sup_set_class f2_eqeq1 a_wcel p_bibi1d f0_eqeq1 f1_eqeq1 a_wceq i0_eqeq1 a_sup_set_class f0_eqeq1 a_wcel i0_eqeq1 a_sup_set_class f2_eqeq1 a_wcel a_wb i0_eqeq1 a_sup_set_class f1_eqeq1 a_wcel i0_eqeq1 a_sup_set_class f2_eqeq1 a_wcel a_wb i0_eqeq1 p_albidv i0_eqeq1 f0_eqeq1 f2_eqeq1 p_dfcleq i0_eqeq1 f1_eqeq1 f2_eqeq1 p_dfcleq f0_eqeq1 f1_eqeq1 a_wceq i0_eqeq1 a_sup_set_class f0_eqeq1 a_wcel i0_eqeq1 a_sup_set_class f2_eqeq1 a_wcel a_wb i0_eqeq1 a_wal i0_eqeq1 a_sup_set_class f1_eqeq1 a_wcel i0_eqeq1 a_sup_set_class f2_eqeq1 a_wcel a_wb i0_eqeq1 a_wal f0_eqeq1 f2_eqeq1 a_wceq f1_eqeq1 f2_eqeq1 a_wceq p_3bitr4g $.
$}

$(Inference from equality to equivalence of equalities.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eqeq1i $f class A $.
	f1_eqeq1i $f class B $.
	f2_eqeq1i $f class C $.
	e0_eqeq1i $e |- A = B $.
	p_eqeq1i $p |- ( A = C <-> B = C ) $= e0_eqeq1i f0_eqeq1i f1_eqeq1i f2_eqeq1i p_eqeq1 f0_eqeq1i f1_eqeq1i a_wceq f0_eqeq1i f2_eqeq1i a_wceq f1_eqeq1i f2_eqeq1i a_wceq a_wb a_ax-mp $.
$}

$(Deduction from equality to equivalence of equalities.  (Contributed by
       NM, 27-Dec-1993.) $)

${
	$v ph A B C  $.
	f0_eqeq1d $f wff ph $.
	f1_eqeq1d $f class A $.
	f2_eqeq1d $f class B $.
	f3_eqeq1d $f class C $.
	e0_eqeq1d $e |- ( ph -> A = B ) $.
	p_eqeq1d $p |- ( ph -> ( A = C <-> B = C ) ) $= e0_eqeq1d f1_eqeq1d f2_eqeq1d f3_eqeq1d p_eqeq1 f0_eqeq1d f1_eqeq1d f2_eqeq1d a_wceq f1_eqeq1d f3_eqeq1d a_wceq f2_eqeq1d f3_eqeq1d a_wceq a_wb p_syl $.
$}

$(Equality implies equivalence of equalities.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eqeq2 $f class A $.
	f1_eqeq2 $f class B $.
	f2_eqeq2 $f class C $.
	p_eqeq2 $p |- ( A = B -> ( C = A <-> C = B ) ) $= f0_eqeq2 f1_eqeq2 f2_eqeq2 p_eqeq1 f2_eqeq2 f0_eqeq2 p_eqcom f2_eqeq2 f1_eqeq2 p_eqcom f0_eqeq2 f1_eqeq2 a_wceq f0_eqeq2 f2_eqeq2 a_wceq f1_eqeq2 f2_eqeq2 a_wceq f2_eqeq2 f0_eqeq2 a_wceq f2_eqeq2 f1_eqeq2 a_wceq p_3bitr4g $.
$}

$(Inference from equality to equivalence of equalities.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eqeq2i $f class A $.
	f1_eqeq2i $f class B $.
	f2_eqeq2i $f class C $.
	e0_eqeq2i $e |- A = B $.
	p_eqeq2i $p |- ( C = A <-> C = B ) $= e0_eqeq2i f0_eqeq2i f1_eqeq2i f2_eqeq2i p_eqeq2 f0_eqeq2i f1_eqeq2i a_wceq f2_eqeq2i f0_eqeq2i a_wceq f2_eqeq2i f1_eqeq2i a_wceq a_wb a_ax-mp $.
$}

$(Deduction from equality to equivalence of equalities.  (Contributed by
       NM, 27-Dec-1993.) $)

${
	$v ph A B C  $.
	f0_eqeq2d $f wff ph $.
	f1_eqeq2d $f class A $.
	f2_eqeq2d $f class B $.
	f3_eqeq2d $f class C $.
	e0_eqeq2d $e |- ( ph -> A = B ) $.
	p_eqeq2d $p |- ( ph -> ( C = A <-> C = B ) ) $= e0_eqeq2d f1_eqeq2d f2_eqeq2d f3_eqeq2d p_eqeq2 f0_eqeq2d f1_eqeq2d f2_eqeq2d a_wceq f3_eqeq2d f1_eqeq2d a_wceq f3_eqeq2d f2_eqeq2d a_wceq a_wb p_syl $.
$}

$(Equality relationship among 4 classes.  (Contributed by NM,
     3-Aug-1994.) $)

${
	$v A B C D  $.
	f0_eqeq12 $f class A $.
	f1_eqeq12 $f class B $.
	f2_eqeq12 $f class C $.
	f3_eqeq12 $f class D $.
	p_eqeq12 $p |- ( ( A = B /\ C = D ) -> ( A = C <-> B = D ) ) $= f0_eqeq12 f1_eqeq12 f2_eqeq12 p_eqeq1 f2_eqeq12 f3_eqeq12 f1_eqeq12 p_eqeq2 f0_eqeq12 f1_eqeq12 a_wceq f0_eqeq12 f2_eqeq12 a_wceq f1_eqeq12 f2_eqeq12 a_wceq f2_eqeq12 f3_eqeq12 a_wceq f1_eqeq12 f3_eqeq12 a_wceq p_sylan9bb $.
$}

$(A useful inference for substituting definitions into an equality.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)

${
	$v A B C D  $.
	f0_eqeq12i $f class A $.
	f1_eqeq12i $f class B $.
	f2_eqeq12i $f class C $.
	f3_eqeq12i $f class D $.
	e0_eqeq12i $e |- A = B $.
	e1_eqeq12i $e |- C = D $.
	p_eqeq12i $p |- ( A = C <-> B = D ) $= e0_eqeq12i e1_eqeq12i f0_eqeq12i f1_eqeq12i f2_eqeq12i f3_eqeq12i p_eqeq12 f0_eqeq12i f1_eqeq12i a_wceq f2_eqeq12i f3_eqeq12i a_wceq f0_eqeq12i f2_eqeq12i a_wceq f1_eqeq12i f3_eqeq12i a_wceq a_wb p_mp2an $.
$}

$(Theorem eqeq12i is the congruence law for equality. $)

$($j congruence 'eqeq12i'; $)

$(A useful inference for substituting definitions into an equality.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)

${
	$v ph A B C D  $.
	f0_eqeq12d $f wff ph $.
	f1_eqeq12d $f class A $.
	f2_eqeq12d $f class B $.
	f3_eqeq12d $f class C $.
	f4_eqeq12d $f class D $.
	e0_eqeq12d $e |- ( ph -> A = B ) $.
	e1_eqeq12d $e |- ( ph -> C = D ) $.
	p_eqeq12d $p |- ( ph -> ( A = C <-> B = D ) ) $= e0_eqeq12d e1_eqeq12d f1_eqeq12d f2_eqeq12d f3_eqeq12d f4_eqeq12d p_eqeq12 f0_eqeq12d f1_eqeq12d f2_eqeq12d a_wceq f3_eqeq12d f4_eqeq12d a_wceq f1_eqeq12d f3_eqeq12d a_wceq f2_eqeq12d f4_eqeq12d a_wceq a_wb p_syl2anc $.
$}

$(A useful inference for substituting definitions into an equality.
       (Contributed by NM, 9-Aug-1994.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)

${
	$v ph ps A B C D  $.
	f0_eqeqan12d $f wff ph $.
	f1_eqeqan12d $f wff ps $.
	f2_eqeqan12d $f class A $.
	f3_eqeqan12d $f class B $.
	f4_eqeqan12d $f class C $.
	f5_eqeqan12d $f class D $.
	e0_eqeqan12d $e |- ( ph -> A = B ) $.
	e1_eqeqan12d $e |- ( ps -> C = D ) $.
	p_eqeqan12d $p |- ( ( ph /\ ps ) -> ( A = C <-> B = D ) ) $= e0_eqeqan12d e1_eqeqan12d f2_eqeqan12d f3_eqeqan12d f4_eqeqan12d f5_eqeqan12d p_eqeq12 f0_eqeqan12d f2_eqeqan12d f3_eqeqan12d a_wceq f4_eqeqan12d f5_eqeqan12d a_wceq f2_eqeqan12d f4_eqeqan12d a_wceq f3_eqeqan12d f5_eqeqan12d a_wceq a_wb f1_eqeqan12d p_syl2an $.
$}

$(A useful inference for substituting definitions into an equality.
       (Contributed by NM, 9-Aug-1994.) $)

${
	$v ph ps A B C D  $.
	f0_eqeqan12rd $f wff ph $.
	f1_eqeqan12rd $f wff ps $.
	f2_eqeqan12rd $f class A $.
	f3_eqeqan12rd $f class B $.
	f4_eqeqan12rd $f class C $.
	f5_eqeqan12rd $f class D $.
	e0_eqeqan12rd $e |- ( ph -> A = B ) $.
	e1_eqeqan12rd $e |- ( ps -> C = D ) $.
	p_eqeqan12rd $p |- ( ( ps /\ ph ) -> ( A = C <-> B = D ) ) $= e0_eqeqan12rd e1_eqeqan12rd f0_eqeqan12rd f1_eqeqan12rd f2_eqeqan12rd f3_eqeqan12rd f4_eqeqan12rd f5_eqeqan12rd p_eqeqan12d f0_eqeqan12rd f1_eqeqan12rd f2_eqeqan12rd f4_eqeqan12rd a_wceq f3_eqeqan12rd f5_eqeqan12rd a_wceq a_wb p_ancoms $.
$}

$(Transitive law for class equality.  Proposition 4.7(3) of [TakeutiZaring]
     p. 13.  (Contributed by NM, 25-Jan-2004.) $)

${
	$v A B C  $.
	f0_eqtr $f class A $.
	f1_eqtr $f class B $.
	f2_eqtr $f class C $.
	p_eqtr $p |- ( ( A = B /\ B = C ) -> A = C ) $= f0_eqtr f1_eqtr f2_eqtr p_eqeq1 f0_eqtr f1_eqtr a_wceq f0_eqtr f2_eqtr a_wceq f1_eqtr f2_eqtr a_wceq p_biimpar $.
$}

$(A transitive law for class equality.  (Contributed by NM, 20-May-2005.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v A B C  $.
	f0_eqtr2 $f class A $.
	f1_eqtr2 $f class B $.
	f2_eqtr2 $f class C $.
	p_eqtr2 $p |- ( ( A = B /\ A = C ) -> B = C ) $= f0_eqtr2 f1_eqtr2 p_eqcom f1_eqtr2 f0_eqtr2 f2_eqtr2 p_eqtr f0_eqtr2 f1_eqtr2 a_wceq f1_eqtr2 f0_eqtr2 a_wceq f0_eqtr2 f2_eqtr2 a_wceq f1_eqtr2 f2_eqtr2 a_wceq p_sylanb $.
$}

$(A transitive law for class equality.  (Contributed by NM, 20-May-2005.) $)

${
	$v A B C  $.
	f0_eqtr3 $f class A $.
	f1_eqtr3 $f class B $.
	f2_eqtr3 $f class C $.
	p_eqtr3 $p |- ( ( A = C /\ B = C ) -> A = B ) $= f1_eqtr3 f2_eqtr3 p_eqcom f0_eqtr3 f2_eqtr3 f1_eqtr3 p_eqtr f1_eqtr3 f2_eqtr3 a_wceq f0_eqtr3 f2_eqtr3 a_wceq f2_eqtr3 f1_eqtr3 a_wceq f0_eqtr3 f1_eqtr3 a_wceq p_sylan2b $.
$}

$(An equality transitivity inference.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eqtri $f class A $.
	f1_eqtri $f class B $.
	f2_eqtri $f class C $.
	e0_eqtri $e |- A = B $.
	e1_eqtri $e |- B = C $.
	p_eqtri $p |- A = C $= e0_eqtri e1_eqtri f1_eqtri f2_eqtri f0_eqtri p_eqeq2i f0_eqtri f1_eqtri a_wceq f0_eqtri f2_eqtri a_wceq p_mpbi $.
$}

$(An equality transitivity inference.  (Contributed by NM,
       21-Feb-1995.) $)

${
	$v A B C  $.
	f0_eqtr2i $f class A $.
	f1_eqtr2i $f class B $.
	f2_eqtr2i $f class C $.
	e0_eqtr2i $e |- A = B $.
	e1_eqtr2i $e |- B = C $.
	p_eqtr2i $p |- C = A $= e0_eqtr2i e1_eqtr2i f0_eqtr2i f1_eqtr2i f2_eqtr2i p_eqtri f0_eqtr2i f2_eqtr2i p_eqcomi $.
$}

$(An equality transitivity inference.  (Contributed by NM, 6-May-1994.) $)

${
	$v A B C  $.
	f0_eqtr3i $f class A $.
	f1_eqtr3i $f class B $.
	f2_eqtr3i $f class C $.
	e0_eqtr3i $e |- A = B $.
	e1_eqtr3i $e |- A = C $.
	p_eqtr3i $p |- B = C $= e0_eqtr3i f0_eqtr3i f1_eqtr3i p_eqcomi e1_eqtr3i f1_eqtr3i f0_eqtr3i f2_eqtr3i p_eqtri $.
$}

$(An equality transitivity inference.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eqtr4i $f class A $.
	f1_eqtr4i $f class B $.
	f2_eqtr4i $f class C $.
	e0_eqtr4i $e |- A = B $.
	e1_eqtr4i $e |- C = B $.
	p_eqtr4i $p |- A = C $= e0_eqtr4i e1_eqtr4i f2_eqtr4i f1_eqtr4i p_eqcomi f0_eqtr4i f1_eqtr4i f2_eqtr4i p_eqtri $.
$}

$(Register '=' as an equality for its type (class). $)

$($j equality 'wceq' from 'eqid' 'eqcomi' 'eqtri'; $)

$(An inference from three chained equalities.  (Contributed by NM,
       29-Aug-1993.) $)

${
	$v A B C D  $.
	f0_3eqtri $f class A $.
	f1_3eqtri $f class B $.
	f2_3eqtri $f class C $.
	f3_3eqtri $f class D $.
	e0_3eqtri $e |- A = B $.
	e1_3eqtri $e |- B = C $.
	e2_3eqtri $e |- C = D $.
	p_3eqtri $p |- A = D $= e0_3eqtri e1_3eqtri e2_3eqtri f1_3eqtri f2_3eqtri f3_3eqtri p_eqtri f0_3eqtri f1_3eqtri f3_3eqtri p_eqtri $.
$}

$(An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v A B C D  $.
	f0_3eqtrri $f class A $.
	f1_3eqtrri $f class B $.
	f2_3eqtrri $f class C $.
	f3_3eqtrri $f class D $.
	e0_3eqtrri $e |- A = B $.
	e1_3eqtrri $e |- B = C $.
	e2_3eqtrri $e |- C = D $.
	p_3eqtrri $p |- D = A $= e0_3eqtrri e1_3eqtrri f0_3eqtrri f1_3eqtrri f2_3eqtrri p_eqtri e2_3eqtrri f0_3eqtrri f2_3eqtrri f3_3eqtrri p_eqtr2i $.
$}

$(An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.) $)

${
	$v A B C D  $.
	f0_3eqtr2i $f class A $.
	f1_3eqtr2i $f class B $.
	f2_3eqtr2i $f class C $.
	f3_3eqtr2i $f class D $.
	e0_3eqtr2i $e |- A = B $.
	e1_3eqtr2i $e |- C = B $.
	e2_3eqtr2i $e |- C = D $.
	p_3eqtr2i $p |- A = D $= e0_3eqtr2i e1_3eqtr2i f0_3eqtr2i f1_3eqtr2i f2_3eqtr2i p_eqtr4i e2_3eqtr2i f0_3eqtr2i f2_3eqtr2i f3_3eqtr2i p_eqtri $.
$}

$(An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v A B C D  $.
	f0_3eqtr2ri $f class A $.
	f1_3eqtr2ri $f class B $.
	f2_3eqtr2ri $f class C $.
	f3_3eqtr2ri $f class D $.
	e0_3eqtr2ri $e |- A = B $.
	e1_3eqtr2ri $e |- C = B $.
	e2_3eqtr2ri $e |- C = D $.
	p_3eqtr2ri $p |- D = A $= e0_3eqtr2ri e1_3eqtr2ri f0_3eqtr2ri f1_3eqtr2ri f2_3eqtr2ri p_eqtr4i e2_3eqtr2ri f0_3eqtr2ri f2_3eqtr2ri f3_3eqtr2ri p_eqtr2i $.
$}

$(An inference from three chained equalities.  (Contributed by NM,
       6-May-1994.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v A B C D  $.
	f0_3eqtr3i $f class A $.
	f1_3eqtr3i $f class B $.
	f2_3eqtr3i $f class C $.
	f3_3eqtr3i $f class D $.
	e0_3eqtr3i $e |- A = B $.
	e1_3eqtr3i $e |- A = C $.
	e2_3eqtr3i $e |- B = D $.
	p_3eqtr3i $p |- C = D $= e0_3eqtr3i e1_3eqtr3i f0_3eqtr3i f1_3eqtr3i f2_3eqtr3i p_eqtr3i e2_3eqtr3i f1_3eqtr3i f2_3eqtr3i f3_3eqtr3i p_eqtr3i $.
$}

$(An inference from three chained equalities.  (Contributed by NM,
       15-Aug-2004.) $)

${
	$v A B C D  $.
	f0_3eqtr3ri $f class A $.
	f1_3eqtr3ri $f class B $.
	f2_3eqtr3ri $f class C $.
	f3_3eqtr3ri $f class D $.
	e0_3eqtr3ri $e |- A = B $.
	e1_3eqtr3ri $e |- A = C $.
	e2_3eqtr3ri $e |- B = D $.
	p_3eqtr3ri $p |- D = C $= e2_3eqtr3ri e0_3eqtr3ri e1_3eqtr3ri f0_3eqtr3ri f1_3eqtr3ri f2_3eqtr3ri p_eqtr3i f1_3eqtr3ri f3_3eqtr3ri f2_3eqtr3ri p_eqtr3i $.
$}

$(An inference from three chained equalities.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v A B C D  $.
	f0_3eqtr4i $f class A $.
	f1_3eqtr4i $f class B $.
	f2_3eqtr4i $f class C $.
	f3_3eqtr4i $f class D $.
	e0_3eqtr4i $e |- A = B $.
	e1_3eqtr4i $e |- C = A $.
	e2_3eqtr4i $e |- D = B $.
	p_3eqtr4i $p |- C = D $= e1_3eqtr4i e2_3eqtr4i e0_3eqtr4i f3_3eqtr4i f1_3eqtr4i f0_3eqtr4i p_eqtr4i f2_3eqtr4i f0_3eqtr4i f3_3eqtr4i p_eqtr4i $.
$}

$(An inference from three chained equalities.  (Contributed by NM,
       2-Sep-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v A B C D  $.
	f0_3eqtr4ri $f class A $.
	f1_3eqtr4ri $f class B $.
	f2_3eqtr4ri $f class C $.
	f3_3eqtr4ri $f class D $.
	e0_3eqtr4ri $e |- A = B $.
	e1_3eqtr4ri $e |- C = A $.
	e2_3eqtr4ri $e |- D = B $.
	p_3eqtr4ri $p |- D = C $= e2_3eqtr4ri e0_3eqtr4ri f3_3eqtr4ri f1_3eqtr4ri f0_3eqtr4ri p_eqtr4i e1_3eqtr4ri f3_3eqtr4ri f0_3eqtr4ri f2_3eqtr4ri p_eqtr4i $.
$}

$(An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph A B C  $.
	f0_eqtrd $f wff ph $.
	f1_eqtrd $f class A $.
	f2_eqtrd $f class B $.
	f3_eqtrd $f class C $.
	e0_eqtrd $e |- ( ph -> A = B ) $.
	e1_eqtrd $e |- ( ph -> B = C ) $.
	p_eqtrd $p |- ( ph -> A = C ) $= e0_eqtrd e1_eqtrd f0_eqtrd f2_eqtrd f3_eqtrd f1_eqtrd p_eqeq2d f0_eqtrd f1_eqtrd f2_eqtrd a_wceq f1_eqtrd f3_eqtrd a_wceq p_mpbid $.
$}

$(An equality transitivity deduction.  (Contributed by NM,
       18-Oct-1999.) $)

${
	$v ph A B C  $.
	f0_eqtr2d $f wff ph $.
	f1_eqtr2d $f class A $.
	f2_eqtr2d $f class B $.
	f3_eqtr2d $f class C $.
	e0_eqtr2d $e |- ( ph -> A = B ) $.
	e1_eqtr2d $e |- ( ph -> B = C ) $.
	p_eqtr2d $p |- ( ph -> C = A ) $= e0_eqtr2d e1_eqtr2d f0_eqtr2d f1_eqtr2d f2_eqtr2d f3_eqtr2d p_eqtrd f0_eqtr2d f1_eqtr2d f3_eqtr2d p_eqcomd $.
$}

$(An equality transitivity equality deduction.  (Contributed by NM,
       18-Jul-1995.) $)

${
	$v ph A B C  $.
	f0_eqtr3d $f wff ph $.
	f1_eqtr3d $f class A $.
	f2_eqtr3d $f class B $.
	f3_eqtr3d $f class C $.
	e0_eqtr3d $e |- ( ph -> A = B ) $.
	e1_eqtr3d $e |- ( ph -> A = C ) $.
	p_eqtr3d $p |- ( ph -> B = C ) $= e0_eqtr3d f0_eqtr3d f1_eqtr3d f2_eqtr3d p_eqcomd e1_eqtr3d f0_eqtr3d f2_eqtr3d f1_eqtr3d f3_eqtr3d p_eqtrd $.
$}

$(An equality transitivity equality deduction.  (Contributed by NM,
       18-Jul-1995.) $)

${
	$v ph A B C  $.
	f0_eqtr4d $f wff ph $.
	f1_eqtr4d $f class A $.
	f2_eqtr4d $f class B $.
	f3_eqtr4d $f class C $.
	e0_eqtr4d $e |- ( ph -> A = B ) $.
	e1_eqtr4d $e |- ( ph -> C = B ) $.
	p_eqtr4d $p |- ( ph -> A = C ) $= e0_eqtr4d e1_eqtr4d f0_eqtr4d f3_eqtr4d f2_eqtr4d p_eqcomd f0_eqtr4d f1_eqtr4d f2_eqtr4d f3_eqtr4d p_eqtrd $.
$}

$(A deduction from three chained equalities.  (Contributed by NM,
       29-Oct-1995.) $)

${
	$v ph A B C D  $.
	f0_3eqtrd $f wff ph $.
	f1_3eqtrd $f class A $.
	f2_3eqtrd $f class B $.
	f3_3eqtrd $f class C $.
	f4_3eqtrd $f class D $.
	e0_3eqtrd $e |- ( ph -> A = B ) $.
	e1_3eqtrd $e |- ( ph -> B = C ) $.
	e2_3eqtrd $e |- ( ph -> C = D ) $.
	p_3eqtrd $p |- ( ph -> A = D ) $= e0_3eqtrd e1_3eqtrd e2_3eqtrd f0_3eqtrd f2_3eqtrd f3_3eqtrd f4_3eqtrd p_eqtrd f0_3eqtrd f1_3eqtrd f2_3eqtrd f4_3eqtrd p_eqtrd $.
$}

$(A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B C D  $.
	f0_3eqtrrd $f wff ph $.
	f1_3eqtrrd $f class A $.
	f2_3eqtrrd $f class B $.
	f3_3eqtrrd $f class C $.
	f4_3eqtrrd $f class D $.
	e0_3eqtrrd $e |- ( ph -> A = B ) $.
	e1_3eqtrrd $e |- ( ph -> B = C ) $.
	e2_3eqtrrd $e |- ( ph -> C = D ) $.
	p_3eqtrrd $p |- ( ph -> D = A ) $= e0_3eqtrrd e1_3eqtrrd f0_3eqtrrd f1_3eqtrrd f2_3eqtrrd f3_3eqtrrd p_eqtrd e2_3eqtrrd f0_3eqtrrd f1_3eqtrrd f3_3eqtrrd f4_3eqtrrd p_eqtr2d $.
$}

$(A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.) $)

${
	$v ph A B C D  $.
	f0_3eqtr2d $f wff ph $.
	f1_3eqtr2d $f class A $.
	f2_3eqtr2d $f class B $.
	f3_3eqtr2d $f class C $.
	f4_3eqtr2d $f class D $.
	e0_3eqtr2d $e |- ( ph -> A = B ) $.
	e1_3eqtr2d $e |- ( ph -> C = B ) $.
	e2_3eqtr2d $e |- ( ph -> C = D ) $.
	p_3eqtr2d $p |- ( ph -> A = D ) $= e0_3eqtr2d e1_3eqtr2d f0_3eqtr2d f1_3eqtr2d f2_3eqtr2d f3_3eqtr2d p_eqtr4d e2_3eqtr2d f0_3eqtr2d f1_3eqtr2d f3_3eqtr2d f4_3eqtr2d p_eqtrd $.
$}

$(A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.) $)

${
	$v ph A B C D  $.
	f0_3eqtr2rd $f wff ph $.
	f1_3eqtr2rd $f class A $.
	f2_3eqtr2rd $f class B $.
	f3_3eqtr2rd $f class C $.
	f4_3eqtr2rd $f class D $.
	e0_3eqtr2rd $e |- ( ph -> A = B ) $.
	e1_3eqtr2rd $e |- ( ph -> C = B ) $.
	e2_3eqtr2rd $e |- ( ph -> C = D ) $.
	p_3eqtr2rd $p |- ( ph -> D = A ) $= e0_3eqtr2rd e1_3eqtr2rd f0_3eqtr2rd f1_3eqtr2rd f2_3eqtr2rd f3_3eqtr2rd p_eqtr4d e2_3eqtr2rd f0_3eqtr2rd f1_3eqtr2rd f3_3eqtr2rd f4_3eqtr2rd p_eqtr2d $.
$}

$(A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B C D  $.
	f0_3eqtr3d $f wff ph $.
	f1_3eqtr3d $f class A $.
	f2_3eqtr3d $f class B $.
	f3_3eqtr3d $f class C $.
	f4_3eqtr3d $f class D $.
	e0_3eqtr3d $e |- ( ph -> A = B ) $.
	e1_3eqtr3d $e |- ( ph -> A = C ) $.
	e2_3eqtr3d $e |- ( ph -> B = D ) $.
	p_3eqtr3d $p |- ( ph -> C = D ) $= e0_3eqtr3d e1_3eqtr3d f0_3eqtr3d f1_3eqtr3d f2_3eqtr3d f3_3eqtr3d p_eqtr3d e2_3eqtr3d f0_3eqtr3d f2_3eqtr3d f3_3eqtr3d f4_3eqtr3d p_eqtr3d $.
$}

$(A deduction from three chained equalities.  (Contributed by NM,
       14-Jan-2006.) $)

${
	$v ph A B C D  $.
	f0_3eqtr3rd $f wff ph $.
	f1_3eqtr3rd $f class A $.
	f2_3eqtr3rd $f class B $.
	f3_3eqtr3rd $f class C $.
	f4_3eqtr3rd $f class D $.
	e0_3eqtr3rd $e |- ( ph -> A = B ) $.
	e1_3eqtr3rd $e |- ( ph -> A = C ) $.
	e2_3eqtr3rd $e |- ( ph -> B = D ) $.
	p_3eqtr3rd $p |- ( ph -> D = C ) $= e2_3eqtr3rd e0_3eqtr3rd e1_3eqtr3rd f0_3eqtr3rd f1_3eqtr3rd f2_3eqtr3rd f3_3eqtr3rd p_eqtr3d f0_3eqtr3rd f2_3eqtr3rd f4_3eqtr3rd f3_3eqtr3rd p_eqtr3d $.
$}

$(A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B C D  $.
	f0_3eqtr4d $f wff ph $.
	f1_3eqtr4d $f class A $.
	f2_3eqtr4d $f class B $.
	f3_3eqtr4d $f class C $.
	f4_3eqtr4d $f class D $.
	e0_3eqtr4d $e |- ( ph -> A = B ) $.
	e1_3eqtr4d $e |- ( ph -> C = A ) $.
	e2_3eqtr4d $e |- ( ph -> D = B ) $.
	p_3eqtr4d $p |- ( ph -> C = D ) $= e1_3eqtr4d e2_3eqtr4d e0_3eqtr4d f0_3eqtr4d f4_3eqtr4d f2_3eqtr4d f1_3eqtr4d p_eqtr4d f0_3eqtr4d f3_3eqtr4d f1_3eqtr4d f4_3eqtr4d p_eqtr4d $.
$}

$(A deduction from three chained equalities.  (Contributed by NM,
       21-Sep-1995.) $)

${
	$v ph A B C D  $.
	f0_3eqtr4rd $f wff ph $.
	f1_3eqtr4rd $f class A $.
	f2_3eqtr4rd $f class B $.
	f3_3eqtr4rd $f class C $.
	f4_3eqtr4rd $f class D $.
	e0_3eqtr4rd $e |- ( ph -> A = B ) $.
	e1_3eqtr4rd $e |- ( ph -> C = A ) $.
	e2_3eqtr4rd $e |- ( ph -> D = B ) $.
	p_3eqtr4rd $p |- ( ph -> D = C ) $= e2_3eqtr4rd e0_3eqtr4rd f0_3eqtr4rd f4_3eqtr4rd f2_3eqtr4rd f1_3eqtr4rd p_eqtr4d e1_3eqtr4rd f0_3eqtr4rd f4_3eqtr4rd f1_3eqtr4rd f3_3eqtr4rd p_eqtr4d $.
$}

$(An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph A B C  $.
	f0_syl5eq $f wff ph $.
	f1_syl5eq $f class A $.
	f2_syl5eq $f class B $.
	f3_syl5eq $f class C $.
	e0_syl5eq $e |- A = B $.
	e1_syl5eq $e |- ( ph -> B = C ) $.
	p_syl5eq $p |- ( ph -> A = C ) $= e0_syl5eq f1_syl5eq f2_syl5eq a_wceq f0_syl5eq p_a1i e1_syl5eq f0_syl5eq f1_syl5eq f2_syl5eq f3_syl5eq p_eqtrd $.
$}

$(An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) $)

${
	$v ph A B C  $.
	f0_syl5req $f wff ph $.
	f1_syl5req $f class A $.
	f2_syl5req $f class B $.
	f3_syl5req $f class C $.
	e0_syl5req $e |- A = B $.
	e1_syl5req $e |- ( ph -> B = C ) $.
	p_syl5req $p |- ( ph -> C = A ) $= e0_syl5req e1_syl5req f0_syl5req f1_syl5req f2_syl5req f3_syl5req p_syl5eq f0_syl5req f1_syl5req f3_syl5req p_eqcomd $.
$}

$(An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph A B C  $.
	f0_syl5eqr $f wff ph $.
	f1_syl5eqr $f class A $.
	f2_syl5eqr $f class B $.
	f3_syl5eqr $f class C $.
	e0_syl5eqr $e |- B = A $.
	e1_syl5eqr $e |- ( ph -> B = C ) $.
	p_syl5eqr $p |- ( ph -> A = C ) $= e0_syl5eqr f2_syl5eqr f1_syl5eqr p_eqcomi e1_syl5eqr f0_syl5eqr f1_syl5eqr f2_syl5eqr f3_syl5eqr p_syl5eq $.
$}

$(An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) $)

${
	$v ph A B C  $.
	f0_syl5reqr $f wff ph $.
	f1_syl5reqr $f class A $.
	f2_syl5reqr $f class B $.
	f3_syl5reqr $f class C $.
	e0_syl5reqr $e |- B = A $.
	e1_syl5reqr $e |- ( ph -> B = C ) $.
	p_syl5reqr $p |- ( ph -> C = A ) $= e0_syl5reqr f2_syl5reqr f1_syl5reqr p_eqcomi e1_syl5reqr f0_syl5reqr f1_syl5reqr f2_syl5reqr f3_syl5reqr p_syl5req $.
$}

$(An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph A B C  $.
	f0_syl6eq $f wff ph $.
	f1_syl6eq $f class A $.
	f2_syl6eq $f class B $.
	f3_syl6eq $f class C $.
	e0_syl6eq $e |- ( ph -> A = B ) $.
	e1_syl6eq $e |- B = C $.
	p_syl6eq $p |- ( ph -> A = C ) $= e0_syl6eq e1_syl6eq f2_syl6eq f3_syl6eq a_wceq f0_syl6eq p_a1i f0_syl6eq f1_syl6eq f2_syl6eq f3_syl6eq p_eqtrd $.
$}

$(An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) $)

${
	$v ph A B C  $.
	f0_syl6req $f wff ph $.
	f1_syl6req $f class A $.
	f2_syl6req $f class B $.
	f3_syl6req $f class C $.
	e0_syl6req $e |- ( ph -> A = B ) $.
	e1_syl6req $e |- B = C $.
	p_syl6req $p |- ( ph -> C = A ) $= e0_syl6req e1_syl6req f0_syl6req f1_syl6req f2_syl6req f3_syl6req p_syl6eq f0_syl6req f1_syl6req f3_syl6req p_eqcomd $.
$}

$(An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph A B C  $.
	f0_syl6eqr $f wff ph $.
	f1_syl6eqr $f class A $.
	f2_syl6eqr $f class B $.
	f3_syl6eqr $f class C $.
	e0_syl6eqr $e |- ( ph -> A = B ) $.
	e1_syl6eqr $e |- C = B $.
	p_syl6eqr $p |- ( ph -> A = C ) $= e0_syl6eqr e1_syl6eqr f3_syl6eqr f2_syl6eqr p_eqcomi f0_syl6eqr f1_syl6eqr f2_syl6eqr f3_syl6eqr p_syl6eq $.
$}

$(An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) $)

${
	$v ph A B C  $.
	f0_syl6reqr $f wff ph $.
	f1_syl6reqr $f class A $.
	f2_syl6reqr $f class B $.
	f3_syl6reqr $f class C $.
	e0_syl6reqr $e |- ( ph -> A = B ) $.
	e1_syl6reqr $e |- C = B $.
	p_syl6reqr $p |- ( ph -> C = A ) $= e0_syl6reqr e1_syl6reqr f3_syl6reqr f2_syl6reqr p_eqcomi f0_syl6reqr f1_syl6reqr f2_syl6reqr f3_syl6reqr p_syl6req $.
$}

$(An equality transitivity deduction.  (Contributed by NM, 8-May-1994.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps A B C  $.
	f0_sylan9eq $f wff ph $.
	f1_sylan9eq $f wff ps $.
	f2_sylan9eq $f class A $.
	f3_sylan9eq $f class B $.
	f4_sylan9eq $f class C $.
	e0_sylan9eq $e |- ( ph -> A = B ) $.
	e1_sylan9eq $e |- ( ps -> B = C ) $.
	p_sylan9eq $p |- ( ( ph /\ ps ) -> A = C ) $= e0_sylan9eq e1_sylan9eq f2_sylan9eq f3_sylan9eq f4_sylan9eq p_eqtr f0_sylan9eq f2_sylan9eq f3_sylan9eq a_wceq f3_sylan9eq f4_sylan9eq a_wceq f2_sylan9eq f4_sylan9eq a_wceq f1_sylan9eq p_syl2an $.
$}

$(An equality transitivity deduction.  (Contributed by NM,
       23-Jun-2007.) $)

${
	$v ph ps A B C  $.
	f0_sylan9req $f wff ph $.
	f1_sylan9req $f wff ps $.
	f2_sylan9req $f class A $.
	f3_sylan9req $f class B $.
	f4_sylan9req $f class C $.
	e0_sylan9req $e |- ( ph -> B = A ) $.
	e1_sylan9req $e |- ( ps -> B = C ) $.
	p_sylan9req $p |- ( ( ph /\ ps ) -> A = C ) $= e0_sylan9req f0_sylan9req f3_sylan9req f2_sylan9req p_eqcomd e1_sylan9req f0_sylan9req f1_sylan9req f2_sylan9req f3_sylan9req f4_sylan9req p_sylan9eq $.
$}

$(An equality transitivity deduction.  (Contributed by NM, 8-May-1994.) $)

${
	$v ph ps A B C  $.
	f0_sylan9eqr $f wff ph $.
	f1_sylan9eqr $f wff ps $.
	f2_sylan9eqr $f class A $.
	f3_sylan9eqr $f class B $.
	f4_sylan9eqr $f class C $.
	e0_sylan9eqr $e |- ( ph -> A = B ) $.
	e1_sylan9eqr $e |- ( ps -> B = C ) $.
	p_sylan9eqr $p |- ( ( ps /\ ph ) -> A = C ) $= e0_sylan9eqr e1_sylan9eqr f0_sylan9eqr f1_sylan9eqr f2_sylan9eqr f3_sylan9eqr f4_sylan9eqr p_sylan9eq f0_sylan9eqr f1_sylan9eqr f2_sylan9eqr f4_sylan9eqr a_wceq p_ancoms $.
$}

$(A chained equality inference, useful for converting from definitions.
       (Contributed by NM, 15-Nov-1994.) $)

${
	$v ph A B C D  $.
	f0_3eqtr3g $f wff ph $.
	f1_3eqtr3g $f class A $.
	f2_3eqtr3g $f class B $.
	f3_3eqtr3g $f class C $.
	f4_3eqtr3g $f class D $.
	e0_3eqtr3g $e |- ( ph -> A = B ) $.
	e1_3eqtr3g $e |- A = C $.
	e2_3eqtr3g $e |- B = D $.
	p_3eqtr3g $p |- ( ph -> C = D ) $= e1_3eqtr3g e0_3eqtr3g f0_3eqtr3g f3_3eqtr3g f1_3eqtr3g f2_3eqtr3g p_syl5eqr e2_3eqtr3g f0_3eqtr3g f3_3eqtr3g f2_3eqtr3g f4_3eqtr3g p_syl6eq $.
$}

$(A chained equality inference, useful for converting from definitions.
       (Contributed by Mario Carneiro, 6-Nov-2015.) $)

${
	$v ph A B C D  $.
	f0_3eqtr3a $f wff ph $.
	f1_3eqtr3a $f class A $.
	f2_3eqtr3a $f class B $.
	f3_3eqtr3a $f class C $.
	f4_3eqtr3a $f class D $.
	e0_3eqtr3a $e |- A = B $.
	e1_3eqtr3a $e |- ( ph -> A = C ) $.
	e2_3eqtr3a $e |- ( ph -> B = D ) $.
	p_3eqtr3a $p |- ( ph -> C = D ) $= e1_3eqtr3a e0_3eqtr3a e2_3eqtr3a f0_3eqtr3a f1_3eqtr3a f2_3eqtr3a f4_3eqtr3a p_syl5eq f0_3eqtr3a f1_3eqtr3a f3_3eqtr3a f4_3eqtr3a p_eqtr3d $.
$}

$(A chained equality inference, useful for converting to definitions.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph A B C D  $.
	f0_3eqtr4g $f wff ph $.
	f1_3eqtr4g $f class A $.
	f2_3eqtr4g $f class B $.
	f3_3eqtr4g $f class C $.
	f4_3eqtr4g $f class D $.
	e0_3eqtr4g $e |- ( ph -> A = B ) $.
	e1_3eqtr4g $e |- C = A $.
	e2_3eqtr4g $e |- D = B $.
	p_3eqtr4g $p |- ( ph -> C = D ) $= e1_3eqtr4g e0_3eqtr4g f0_3eqtr4g f3_3eqtr4g f1_3eqtr4g f2_3eqtr4g p_syl5eq e2_3eqtr4g f0_3eqtr4g f3_3eqtr4g f2_3eqtr4g f4_3eqtr4g p_syl6eqr $.
$}

$(A chained equality inference, useful for converting to definitions.
       (Contributed by NM, 2-Feb-2007.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)

${
	$v ph A B C D  $.
	f0_3eqtr4a $f wff ph $.
	f1_3eqtr4a $f class A $.
	f2_3eqtr4a $f class B $.
	f3_3eqtr4a $f class C $.
	f4_3eqtr4a $f class D $.
	e0_3eqtr4a $e |- A = B $.
	e1_3eqtr4a $e |- ( ph -> C = A ) $.
	e2_3eqtr4a $e |- ( ph -> D = B ) $.
	p_3eqtr4a $p |- ( ph -> C = D ) $= e1_3eqtr4a e0_3eqtr4a f0_3eqtr4a f3_3eqtr4a f1_3eqtr4a f2_3eqtr4a p_syl6eq e2_3eqtr4a f0_3eqtr4a f3_3eqtr4a f2_3eqtr4a f4_3eqtr4a p_eqtr4d $.
$}

$(A compound transitive inference for class equality.  (Contributed by NM,
       22-Jan-2004.) $)

${
	$v A B C D F G  $.
	f0_eq2tri $f class A $.
	f1_eq2tri $f class B $.
	f2_eq2tri $f class C $.
	f3_eq2tri $f class D $.
	f4_eq2tri $f class F $.
	f5_eq2tri $f class G $.
	e0_eq2tri $e |- ( A = C -> D = F ) $.
	e1_eq2tri $e |- ( B = D -> C = G ) $.
	p_eq2tri $p |- ( ( A = C /\ B = F ) <-> ( B = D /\ A = G ) ) $= f0_eq2tri f2_eq2tri a_wceq f1_eq2tri f3_eq2tri a_wceq p_ancom e0_eq2tri f0_eq2tri f2_eq2tri a_wceq f3_eq2tri f4_eq2tri f1_eq2tri p_eqeq2d f0_eq2tri f2_eq2tri a_wceq f1_eq2tri f3_eq2tri a_wceq f1_eq2tri f4_eq2tri a_wceq p_pm5.32i e1_eq2tri f1_eq2tri f3_eq2tri a_wceq f2_eq2tri f5_eq2tri f0_eq2tri p_eqeq2d f1_eq2tri f3_eq2tri a_wceq f0_eq2tri f2_eq2tri a_wceq f0_eq2tri f5_eq2tri a_wceq p_pm5.32i f0_eq2tri f2_eq2tri a_wceq f1_eq2tri f3_eq2tri a_wceq a_wa f1_eq2tri f3_eq2tri a_wceq f0_eq2tri f2_eq2tri a_wceq a_wa f0_eq2tri f2_eq2tri a_wceq f1_eq2tri f4_eq2tri a_wceq a_wa f1_eq2tri f3_eq2tri a_wceq f0_eq2tri f5_eq2tri a_wceq a_wa p_3bitr3i $.
$}

$(Equality implies equivalence of membership.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_eleq1 $f class A $.
	f1_eleq1 $f class B $.
	f2_eleq1 $f class C $.
	i0_eleq1 $f set x $.
	p_eleq1 $p |- ( A = B -> ( A e. C <-> B e. C ) ) $= f0_eleq1 f1_eleq1 i0_eleq1 a_sup_set_class p_eqeq2 f0_eleq1 f1_eleq1 a_wceq i0_eleq1 a_sup_set_class f0_eleq1 a_wceq i0_eleq1 a_sup_set_class f1_eleq1 a_wceq i0_eleq1 a_sup_set_class f2_eleq1 a_wcel p_anbi1d f0_eleq1 f1_eleq1 a_wceq i0_eleq1 a_sup_set_class f0_eleq1 a_wceq i0_eleq1 a_sup_set_class f2_eleq1 a_wcel a_wa i0_eleq1 a_sup_set_class f1_eleq1 a_wceq i0_eleq1 a_sup_set_class f2_eleq1 a_wcel a_wa i0_eleq1 p_exbidv i0_eleq1 f0_eleq1 f2_eleq1 a_df-clel i0_eleq1 f1_eleq1 f2_eleq1 a_df-clel f0_eleq1 f1_eleq1 a_wceq i0_eleq1 a_sup_set_class f0_eleq1 a_wceq i0_eleq1 a_sup_set_class f2_eleq1 a_wcel a_wa i0_eleq1 a_wex i0_eleq1 a_sup_set_class f1_eleq1 a_wceq i0_eleq1 a_sup_set_class f2_eleq1 a_wcel a_wa i0_eleq1 a_wex f0_eleq1 f2_eleq1 a_wcel f1_eleq1 f2_eleq1 a_wcel p_3bitr4g $.
$}

$(Equality implies equivalence of membership.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_eleq2 $f class A $.
	f1_eleq2 $f class B $.
	f2_eleq2 $f class C $.
	i0_eleq2 $f set x $.
	p_eleq2 $p |- ( A = B -> ( C e. A <-> C e. B ) ) $= i0_eleq2 f0_eleq2 f1_eleq2 p_dfcleq f0_eleq2 f1_eleq2 a_wceq i0_eleq2 a_sup_set_class f0_eleq2 a_wcel i0_eleq2 a_sup_set_class f1_eleq2 a_wcel a_wb i0_eleq2 a_wal p_biimpi f0_eleq2 f1_eleq2 a_wceq i0_eleq2 a_sup_set_class f0_eleq2 a_wcel i0_eleq2 a_sup_set_class f1_eleq2 a_wcel a_wb i0_eleq2 p_19.21bi f0_eleq2 f1_eleq2 a_wceq i0_eleq2 a_sup_set_class f0_eleq2 a_wcel i0_eleq2 a_sup_set_class f1_eleq2 a_wcel i0_eleq2 a_sup_set_class f2_eleq2 a_wceq p_anbi2d f0_eleq2 f1_eleq2 a_wceq i0_eleq2 a_sup_set_class f2_eleq2 a_wceq i0_eleq2 a_sup_set_class f0_eleq2 a_wcel a_wa i0_eleq2 a_sup_set_class f2_eleq2 a_wceq i0_eleq2 a_sup_set_class f1_eleq2 a_wcel a_wa i0_eleq2 p_exbidv i0_eleq2 f2_eleq2 f0_eleq2 a_df-clel i0_eleq2 f2_eleq2 f1_eleq2 a_df-clel f0_eleq2 f1_eleq2 a_wceq i0_eleq2 a_sup_set_class f2_eleq2 a_wceq i0_eleq2 a_sup_set_class f0_eleq2 a_wcel a_wa i0_eleq2 a_wex i0_eleq2 a_sup_set_class f2_eleq2 a_wceq i0_eleq2 a_sup_set_class f1_eleq2 a_wcel a_wa i0_eleq2 a_wex f2_eleq2 f0_eleq2 a_wcel f2_eleq2 f1_eleq2 a_wcel p_3bitr4g $.
$}

$(Equality implies equivalence of membership.  (Contributed by NM,
     31-May-1999.) $)

${
	$v A B C D  $.
	f0_eleq12 $f class A $.
	f1_eleq12 $f class B $.
	f2_eleq12 $f class C $.
	f3_eleq12 $f class D $.
	p_eleq12 $p |- ( ( A = B /\ C = D ) -> ( A e. C <-> B e. D ) ) $= f0_eleq12 f1_eleq12 f2_eleq12 p_eleq1 f2_eleq12 f3_eleq12 f1_eleq12 p_eleq2 f0_eleq12 f1_eleq12 a_wceq f0_eleq12 f2_eleq12 a_wcel f1_eleq12 f2_eleq12 a_wcel f2_eleq12 f3_eleq12 a_wceq f1_eleq12 f3_eleq12 a_wcel p_sylan9bb $.
$}

$(Inference from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eleq1i $f class A $.
	f1_eleq1i $f class B $.
	f2_eleq1i $f class C $.
	e0_eleq1i $e |- A = B $.
	p_eleq1i $p |- ( A e. C <-> B e. C ) $= e0_eleq1i f0_eleq1i f1_eleq1i f2_eleq1i p_eleq1 f0_eleq1i f1_eleq1i a_wceq f0_eleq1i f2_eleq1i a_wcel f1_eleq1i f2_eleq1i a_wcel a_wb a_ax-mp $.
$}

$(Inference from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eleq2i $f class A $.
	f1_eleq2i $f class B $.
	f2_eleq2i $f class C $.
	e0_eleq2i $e |- A = B $.
	p_eleq2i $p |- ( C e. A <-> C e. B ) $= e0_eleq2i f0_eleq2i f1_eleq2i f2_eleq2i p_eleq2 f0_eleq2i f1_eleq2i a_wceq f2_eleq2i f0_eleq2i a_wcel f2_eleq2i f1_eleq2i a_wcel a_wb a_ax-mp $.
$}

$(Inference from equality to equivalence of membership.  (Contributed by
         NM, 31-May-1994.) $)

${
	$v A B C D  $.
	f0_eleq12i $f class A $.
	f1_eleq12i $f class B $.
	f2_eleq12i $f class C $.
	f3_eleq12i $f class D $.
	e0_eleq12i $e |- A = B $.
	e1_eleq12i $e |- C = D $.
	p_eleq12i $p |- ( A e. C <-> B e. D ) $= e1_eleq12i f2_eleq12i f3_eleq12i f0_eleq12i p_eleq2i e0_eleq12i f0_eleq12i f1_eleq12i f3_eleq12i p_eleq1i f0_eleq12i f2_eleq12i a_wcel f0_eleq12i f3_eleq12i a_wcel f1_eleq12i f3_eleq12i a_wcel p_bitri $.
$}

$(Theorem eleq12i is the congruence law for elementhood. $)

$($j congruence 'eleq12i'; $)

$(Deduction from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph A B C  $.
	f0_eleq1d $f wff ph $.
	f1_eleq1d $f class A $.
	f2_eleq1d $f class B $.
	f3_eleq1d $f class C $.
	e0_eleq1d $e |- ( ph -> A = B ) $.
	p_eleq1d $p |- ( ph -> ( A e. C <-> B e. C ) ) $= e0_eleq1d f1_eleq1d f2_eleq1d f3_eleq1d p_eleq1 f0_eleq1d f1_eleq1d f2_eleq1d a_wceq f1_eleq1d f3_eleq1d a_wcel f2_eleq1d f3_eleq1d a_wcel a_wb p_syl $.
$}

$(Deduction from equality to equivalence of membership.  (Contributed by
       NM, 27-Dec-1993.) $)

${
	$v ph A B C  $.
	f0_eleq2d $f wff ph $.
	f1_eleq2d $f class A $.
	f2_eleq2d $f class B $.
	f3_eleq2d $f class C $.
	e0_eleq2d $e |- ( ph -> A = B ) $.
	p_eleq2d $p |- ( ph -> ( C e. A <-> C e. B ) ) $= e0_eleq2d f1_eleq2d f2_eleq2d f3_eleq2d p_eleq2 f0_eleq2d f1_eleq2d f2_eleq2d a_wceq f3_eleq2d f1_eleq2d a_wcel f3_eleq2d f2_eleq2d a_wcel a_wb p_syl $.
$}

$(Deduction from equality to equivalence of membership.  (Contributed by
         NM, 31-May-1994.) $)

${
	$v ph A B C D  $.
	f0_eleq12d $f wff ph $.
	f1_eleq12d $f class A $.
	f2_eleq12d $f class B $.
	f3_eleq12d $f class C $.
	f4_eleq12d $f class D $.
	e0_eleq12d $e |- ( ph -> A = B ) $.
	e1_eleq12d $e |- ( ph -> C = D ) $.
	p_eleq12d $p |- ( ph -> ( A e. C <-> B e. D ) ) $= e1_eleq12d f0_eleq12d f3_eleq12d f4_eleq12d f1_eleq12d p_eleq2d e0_eleq12d f0_eleq12d f1_eleq12d f2_eleq12d f4_eleq12d p_eleq1d f0_eleq12d f1_eleq12d f3_eleq12d a_wcel f1_eleq12d f4_eleq12d a_wcel f2_eleq12d f4_eleq12d a_wcel p_bitrd $.
$}

$(A transitive-type law relating membership and equality.  (Contributed by
     NM, 9-Apr-1994.) $)

${
	$v A B C  $.
	f0_eleq1a $f class A $.
	f1_eleq1a $f class B $.
	f2_eleq1a $f class C $.
	p_eleq1a $p |- ( A e. B -> ( C = A -> C e. B ) ) $= f2_eleq1a f0_eleq1a f1_eleq1a p_eleq1 f2_eleq1a f0_eleq1a a_wceq f2_eleq1a f1_eleq1a a_wcel f0_eleq1a f1_eleq1a a_wcel p_biimprcd $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eqeltri $f class A $.
	f1_eqeltri $f class B $.
	f2_eqeltri $f class C $.
	e0_eqeltri $e |- A = B $.
	e1_eqeltri $e |- B e. C $.
	p_eqeltri $p |- A e. C $= e1_eqeltri e0_eqeltri f0_eqeltri f1_eqeltri f2_eqeltri p_eleq1i f0_eqeltri f2_eqeltri a_wcel f1_eqeltri f2_eqeltri a_wcel p_mpbir $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eqeltrri $f class A $.
	f1_eqeltrri $f class B $.
	f2_eqeltrri $f class C $.
	e0_eqeltrri $e |- A = B $.
	e1_eqeltrri $e |- A e. C $.
	p_eqeltrri $p |- B e. C $= e0_eqeltrri f0_eqeltrri f1_eqeltrri p_eqcomi e1_eqeltrri f1_eqeltrri f0_eqeltrri f2_eqeltrri p_eqeltri $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eleqtri $f class A $.
	f1_eleqtri $f class B $.
	f2_eleqtri $f class C $.
	e0_eleqtri $e |- A e. B $.
	e1_eleqtri $e |- B = C $.
	p_eleqtri $p |- A e. C $= e0_eleqtri e1_eleqtri f1_eleqtri f2_eleqtri f0_eleqtri p_eleq2i f0_eleqtri f1_eleqtri a_wcel f0_eleqtri f2_eleqtri a_wcel p_mpbi $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_eleqtrri $f class A $.
	f1_eleqtrri $f class B $.
	f2_eleqtrri $f class C $.
	e0_eleqtrri $e |- A e. B $.
	e1_eleqtrri $e |- C = B $.
	p_eleqtrri $p |- A e. C $= e0_eleqtrri e1_eleqtrri f2_eleqtrri f1_eleqtrri p_eqcomi f0_eleqtrri f1_eleqtrri f2_eleqtrri p_eleqtri $.
$}

$(Substitution of equal classes into membership relation, deduction form.
       (Contributed by Raph Levien, 10-Dec-2002.) $)

${
	$v ph A B C  $.
	f0_eqeltrd $f wff ph $.
	f1_eqeltrd $f class A $.
	f2_eqeltrd $f class B $.
	f3_eqeltrd $f class C $.
	e0_eqeltrd $e |- ( ph -> A = B ) $.
	e1_eqeltrd $e |- ( ph -> B e. C ) $.
	p_eqeltrd $p |- ( ph -> A e. C ) $= e1_eqeltrd e0_eqeltrd f0_eqeltrd f1_eqeltrd f2_eqeltrd f3_eqeltrd p_eleq1d f0_eqeltrd f1_eqeltrd f3_eqeltrd a_wcel f2_eqeltrd f3_eqeltrd a_wcel p_mpbird $.
$}

$(Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) $)

${
	$v ph A B C  $.
	f0_eqeltrrd $f wff ph $.
	f1_eqeltrrd $f class A $.
	f2_eqeltrrd $f class B $.
	f3_eqeltrrd $f class C $.
	e0_eqeltrrd $e |- ( ph -> A = B ) $.
	e1_eqeltrrd $e |- ( ph -> A e. C ) $.
	p_eqeltrrd $p |- ( ph -> B e. C ) $= e0_eqeltrrd f0_eqeltrrd f1_eqeltrrd f2_eqeltrrd p_eqcomd e1_eqeltrrd f0_eqeltrrd f2_eqeltrrd f1_eqeltrrd f3_eqeltrrd p_eqeltrd $.
$}

$(Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) $)

${
	$v ph A B C  $.
	f0_eleqtrd $f wff ph $.
	f1_eleqtrd $f class A $.
	f2_eleqtrd $f class B $.
	f3_eleqtrd $f class C $.
	e0_eleqtrd $e |- ( ph -> A e. B ) $.
	e1_eleqtrd $e |- ( ph -> B = C ) $.
	p_eleqtrd $p |- ( ph -> A e. C ) $= e0_eleqtrd e1_eleqtrd f0_eleqtrd f2_eleqtrd f3_eleqtrd f1_eleqtrd p_eleq2d f0_eleqtrd f1_eleqtrd f2_eleqtrd a_wcel f1_eleqtrd f3_eleqtrd a_wcel p_mpbid $.
$}

$(Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) $)

${
	$v ph A B C  $.
	f0_eleqtrrd $f wff ph $.
	f1_eleqtrrd $f class A $.
	f2_eleqtrrd $f class B $.
	f3_eleqtrrd $f class C $.
	e0_eleqtrrd $e |- ( ph -> A e. B ) $.
	e1_eleqtrrd $e |- ( ph -> C = B ) $.
	p_eleqtrrd $p |- ( ph -> A e. C ) $= e0_eleqtrrd e1_eleqtrrd f0_eleqtrrd f3_eleqtrrd f2_eleqtrrd p_eqcomd f0_eleqtrrd f1_eleqtrrd f2_eleqtrrd f3_eleqtrrd p_eleqtrd $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)

${
	$v A B C D  $.
	f0_3eltr3i $f class A $.
	f1_3eltr3i $f class B $.
	f2_3eltr3i $f class C $.
	f3_3eltr3i $f class D $.
	e0_3eltr3i $e |- A e. B $.
	e1_3eltr3i $e |- A = C $.
	e2_3eltr3i $e |- B = D $.
	p_3eltr3i $p |- C e. D $= e1_3eltr3i e0_3eltr3i e2_3eltr3i f0_3eltr3i f1_3eltr3i f3_3eltr3i p_eleqtri f0_3eltr3i f2_3eltr3i f3_3eltr3i p_eqeltrri $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)

${
	$v A B C D  $.
	f0_3eltr4i $f class A $.
	f1_3eltr4i $f class B $.
	f2_3eltr4i $f class C $.
	f3_3eltr4i $f class D $.
	e0_3eltr4i $e |- A e. B $.
	e1_3eltr4i $e |- C = A $.
	e2_3eltr4i $e |- D = B $.
	p_3eltr4i $p |- C e. D $= e1_3eltr4i e0_3eltr4i e2_3eltr4i f0_3eltr4i f1_3eltr4i f3_3eltr4i p_eleqtrri f2_3eltr4i f0_3eltr4i f3_3eltr4i p_eqeltri $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)

${
	$v ph A B C D  $.
	f0_3eltr3d $f wff ph $.
	f1_3eltr3d $f class A $.
	f2_3eltr3d $f class B $.
	f3_3eltr3d $f class C $.
	f4_3eltr3d $f class D $.
	e0_3eltr3d $e |- ( ph -> A e. B ) $.
	e1_3eltr3d $e |- ( ph -> A = C ) $.
	e2_3eltr3d $e |- ( ph -> B = D ) $.
	p_3eltr3d $p |- ( ph -> C e. D ) $= e1_3eltr3d e0_3eltr3d e2_3eltr3d f0_3eltr3d f1_3eltr3d f2_3eltr3d f4_3eltr3d p_eleqtrd f0_3eltr3d f1_3eltr3d f3_3eltr3d f4_3eltr3d p_eqeltrrd $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)

${
	$v ph A B C D  $.
	f0_3eltr4d $f wff ph $.
	f1_3eltr4d $f class A $.
	f2_3eltr4d $f class B $.
	f3_3eltr4d $f class C $.
	f4_3eltr4d $f class D $.
	e0_3eltr4d $e |- ( ph -> A e. B ) $.
	e1_3eltr4d $e |- ( ph -> C = A ) $.
	e2_3eltr4d $e |- ( ph -> D = B ) $.
	p_3eltr4d $p |- ( ph -> C e. D ) $= e1_3eltr4d e0_3eltr4d e2_3eltr4d f0_3eltr4d f1_3eltr4d f2_3eltr4d f4_3eltr4d p_eleqtrrd f0_3eltr4d f3_3eltr4d f1_3eltr4d f4_3eltr4d p_eqeltrd $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)

${
	$v ph A B C D  $.
	f0_3eltr3g $f wff ph $.
	f1_3eltr3g $f class A $.
	f2_3eltr3g $f class B $.
	f3_3eltr3g $f class C $.
	f4_3eltr3g $f class D $.
	e0_3eltr3g $e |- ( ph -> A e. B ) $.
	e1_3eltr3g $e |- A = C $.
	e2_3eltr3g $e |- B = D $.
	p_3eltr3g $p |- ( ph -> C e. D ) $= e0_3eltr3g e1_3eltr3g e2_3eltr3g f1_3eltr3g f3_3eltr3g f2_3eltr3g f4_3eltr3g p_eleq12i f0_3eltr3g f1_3eltr3g f2_3eltr3g a_wcel f3_3eltr3g f4_3eltr3g a_wcel p_sylib $.
$}

$(Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)

${
	$v ph A B C D  $.
	f0_3eltr4g $f wff ph $.
	f1_3eltr4g $f class A $.
	f2_3eltr4g $f class B $.
	f3_3eltr4g $f class C $.
	f4_3eltr4g $f class D $.
	e0_3eltr4g $e |- ( ph -> A e. B ) $.
	e1_3eltr4g $e |- C = A $.
	e2_3eltr4g $e |- D = B $.
	p_3eltr4g $p |- ( ph -> C e. D ) $= e0_3eltr4g e1_3eltr4g e2_3eltr4g f3_3eltr4g f1_3eltr4g f4_3eltr4g f2_3eltr4g p_eleq12i f0_3eltr4g f1_3eltr4g f2_3eltr4g a_wcel f3_3eltr4g f4_3eltr4g a_wcel p_sylibr $.
$}

$(B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)

${
	$v ph A B C  $.
	f0_syl5eqel $f wff ph $.
	f1_syl5eqel $f class A $.
	f2_syl5eqel $f class B $.
	f3_syl5eqel $f class C $.
	e0_syl5eqel $e |- A = B $.
	e1_syl5eqel $e |- ( ph -> B e. C ) $.
	p_syl5eqel $p |- ( ph -> A e. C ) $= e0_syl5eqel f1_syl5eqel f2_syl5eqel a_wceq f0_syl5eqel p_a1i e1_syl5eqel f0_syl5eqel f1_syl5eqel f2_syl5eqel f3_syl5eqel p_eqeltrd $.
$}

$(B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)

${
	$v ph A B C  $.
	f0_syl5eqelr $f wff ph $.
	f1_syl5eqelr $f class A $.
	f2_syl5eqelr $f class B $.
	f3_syl5eqelr $f class C $.
	e0_syl5eqelr $e |- B = A $.
	e1_syl5eqelr $e |- ( ph -> B e. C ) $.
	p_syl5eqelr $p |- ( ph -> A e. C ) $= e0_syl5eqelr f2_syl5eqelr f1_syl5eqelr p_eqcomi e1_syl5eqelr f0_syl5eqelr f1_syl5eqelr f2_syl5eqelr f3_syl5eqelr p_syl5eqel $.
$}

$(B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)

${
	$v ph A B C  $.
	f0_syl5eleq $f wff ph $.
	f1_syl5eleq $f class A $.
	f2_syl5eleq $f class B $.
	f3_syl5eleq $f class C $.
	e0_syl5eleq $e |- A e. B $.
	e1_syl5eleq $e |- ( ph -> B = C ) $.
	p_syl5eleq $p |- ( ph -> A e. C ) $= e0_syl5eleq f1_syl5eleq f2_syl5eleq a_wcel f0_syl5eleq p_a1i e1_syl5eleq f0_syl5eleq f1_syl5eleq f2_syl5eleq f3_syl5eleq p_eleqtrd $.
$}

$(B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)

${
	$v ph A B C  $.
	f0_syl5eleqr $f wff ph $.
	f1_syl5eleqr $f class A $.
	f2_syl5eleqr $f class B $.
	f3_syl5eleqr $f class C $.
	e0_syl5eleqr $e |- A e. B $.
	e1_syl5eleqr $e |- ( ph -> C = B ) $.
	p_syl5eleqr $p |- ( ph -> A e. C ) $= e0_syl5eleqr e1_syl5eleqr f0_syl5eleqr f3_syl5eleqr f2_syl5eleqr p_eqcomd f0_syl5eleqr f1_syl5eleqr f2_syl5eleqr f3_syl5eleqr p_syl5eleq $.
$}

$(A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)

${
	$v ph A B C  $.
	f0_syl6eqel $f wff ph $.
	f1_syl6eqel $f class A $.
	f2_syl6eqel $f class B $.
	f3_syl6eqel $f class C $.
	e0_syl6eqel $e |- ( ph -> A = B ) $.
	e1_syl6eqel $e |- B e. C $.
	p_syl6eqel $p |- ( ph -> A e. C ) $= e0_syl6eqel e1_syl6eqel f2_syl6eqel f3_syl6eqel a_wcel f0_syl6eqel p_a1i f0_syl6eqel f1_syl6eqel f2_syl6eqel f3_syl6eqel p_eqeltrd $.
$}

$(A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)

${
	$v ph A B C  $.
	f0_syl6eqelr $f wff ph $.
	f1_syl6eqelr $f class A $.
	f2_syl6eqelr $f class B $.
	f3_syl6eqelr $f class C $.
	e0_syl6eqelr $e |- ( ph -> B = A ) $.
	e1_syl6eqelr $e |- B e. C $.
	p_syl6eqelr $p |- ( ph -> A e. C ) $= e0_syl6eqelr f0_syl6eqelr f2_syl6eqelr f1_syl6eqelr p_eqcomd e1_syl6eqelr f0_syl6eqelr f1_syl6eqelr f2_syl6eqelr f3_syl6eqelr p_syl6eqel $.
$}

$(A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)

${
	$v ph A B C  $.
	f0_syl6eleq $f wff ph $.
	f1_syl6eleq $f class A $.
	f2_syl6eleq $f class B $.
	f3_syl6eleq $f class C $.
	e0_syl6eleq $e |- ( ph -> A e. B ) $.
	e1_syl6eleq $e |- B = C $.
	p_syl6eleq $p |- ( ph -> A e. C ) $= e0_syl6eleq e1_syl6eleq f2_syl6eleq f3_syl6eleq a_wceq f0_syl6eleq p_a1i f0_syl6eleq f1_syl6eleq f2_syl6eleq f3_syl6eleq p_eleqtrd $.
$}

$(A membership and equality inference.  (Contributed by NM,
       24-Apr-2005.) $)

${
	$v ph A B C  $.
	f0_syl6eleqr $f wff ph $.
	f1_syl6eleqr $f class A $.
	f2_syl6eleqr $f class B $.
	f3_syl6eleqr $f class C $.
	e0_syl6eleqr $e |- ( ph -> A e. B ) $.
	e1_syl6eleqr $e |- C = B $.
	p_syl6eleqr $p |- ( ph -> A e. C ) $= e0_syl6eleqr e1_syl6eleqr f3_syl6eleqr f2_syl6eleqr p_eqcomi f0_syl6eleqr f1_syl6eleqr f2_syl6eleqr f3_syl6eleqr p_syl6eleq $.
$}

$(Substitution of equal classes into a membership antecedent.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)

${
	$v ph A B C  $.
	f0_eleq2s $f wff ph $.
	f1_eleq2s $f class A $.
	f2_eleq2s $f class B $.
	f3_eleq2s $f class C $.
	e0_eleq2s $e |- ( A e. B -> ph ) $.
	e1_eleq2s $e |- C = B $.
	p_eleq2s $p |- ( A e. C -> ph ) $= e1_eleq2s f3_eleq2s f2_eleq2s f1_eleq2s p_eleq2i e0_eleq2s f1_eleq2s f3_eleq2s a_wcel f1_eleq2s f2_eleq2s a_wcel f0_eleq2s p_sylbi $.
$}

$(If a class is not an element of another class, an equal class is also
       not an element.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph A B C  $.
	f0_eqneltrd $f wff ph $.
	f1_eqneltrd $f class A $.
	f2_eqneltrd $f class B $.
	f3_eqneltrd $f class C $.
	e0_eqneltrd $e |- ( ph -> A = B ) $.
	e1_eqneltrd $e |- ( ph -> -. B e. C ) $.
	p_eqneltrd $p |- ( ph -> -. A e. C ) $= e1_eqneltrd e0_eqneltrd f0_eqneltrd f1_eqneltrd f2_eqneltrd f3_eqneltrd p_eleq1d f0_eqneltrd f1_eqneltrd f3_eqneltrd a_wcel f2_eqneltrd f3_eqneltrd a_wcel p_mtbird $.
$}

$(If a class is not an element of another class, an equal class is also
       not an element.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph A B C  $.
	f0_eqneltrrd $f wff ph $.
	f1_eqneltrrd $f class A $.
	f2_eqneltrrd $f class B $.
	f3_eqneltrrd $f class C $.
	e0_eqneltrrd $e |- ( ph -> A = B ) $.
	e1_eqneltrrd $e |- ( ph -> -. A e. C ) $.
	p_eqneltrrd $p |- ( ph -> -. B e. C ) $= e1_eqneltrrd e0_eqneltrrd f0_eqneltrrd f1_eqneltrrd f2_eqneltrrd f3_eqneltrrd p_eleq1d f0_eqneltrrd f1_eqneltrrd f3_eqneltrrd a_wcel f2_eqneltrrd f3_eqneltrrd a_wcel p_mtbid $.
$}

$(If a class is not an element of another class, it is also not an element
       of an equal class.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph A B C  $.
	f0_neleqtrd $f wff ph $.
	f1_neleqtrd $f class A $.
	f2_neleqtrd $f class B $.
	f3_neleqtrd $f class C $.
	e0_neleqtrd $e |- ( ph -> -. C e. A ) $.
	e1_neleqtrd $e |- ( ph -> A = B ) $.
	p_neleqtrd $p |- ( ph -> -. C e. B ) $= e0_neleqtrd e1_neleqtrd f0_neleqtrd f1_neleqtrd f2_neleqtrd f3_neleqtrd p_eleq2d f0_neleqtrd f3_neleqtrd f1_neleqtrd a_wcel f3_neleqtrd f2_neleqtrd a_wcel p_mtbid $.
$}

$(If a class is not an element of another class, it is also not an element
       of an equal class.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph A B C  $.
	f0_neleqtrrd $f wff ph $.
	f1_neleqtrrd $f class A $.
	f2_neleqtrrd $f class B $.
	f3_neleqtrrd $f class C $.
	e0_neleqtrrd $e |- ( ph -> -. C e. B ) $.
	e1_neleqtrrd $e |- ( ph -> A = B ) $.
	p_neleqtrrd $p |- ( ph -> -. C e. A ) $= e0_neleqtrrd e1_neleqtrrd f0_neleqtrrd f1_neleqtrrd f2_neleqtrrd f3_neleqtrrd p_eleq2d f0_neleqtrrd f3_neleqtrrd f1_neleqtrrd a_wcel f3_neleqtrrd f2_neleqtrrd a_wcel p_mtbird $.
$}

$(Establish equality between classes, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v x y A B  $.
	$d y A  $.
	$d y B  $.
	$d x y  $.
	f0_cleqh $f set x $.
	f1_cleqh $f set y $.
	f2_cleqh $f class A $.
	f3_cleqh $f class B $.
	e0_cleqh $e |- ( y e. A -> A. x y e. A ) $.
	e1_cleqh $e |- ( y e. B -> A. x y e. B ) $.
	p_cleqh $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $= f1_cleqh f2_cleqh f3_cleqh p_dfcleq f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_ax-17 f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel p_dfbi2 e0_cleqh e1_cleqh f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel f0_cleqh p_hbim e1_cleqh e0_cleqh f1_cleqh a_sup_set_class f3_cleqh a_wcel f1_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh p_hbim f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wi f1_cleqh a_sup_set_class f3_cleqh a_wcel f1_cleqh a_sup_set_class f2_cleqh a_wcel a_wi f0_cleqh p_hban f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wi f1_cleqh a_sup_set_class f3_cleqh a_wcel f1_cleqh a_sup_set_class f2_cleqh a_wcel a_wi a_wa f0_cleqh p_hbxfrbi f0_cleqh a_sup_set_class f1_cleqh a_sup_set_class f2_cleqh p_eleq1 f0_cleqh a_sup_set_class f1_cleqh a_sup_set_class f3_cleqh p_eleq1 f0_cleqh a_sup_set_class f1_cleqh a_sup_set_class a_wceq f0_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel p_bibi12d f0_cleqh a_sup_set_class f1_cleqh a_sup_set_class a_wceq f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb p_biimpd f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f0_cleqh f1_cleqh p_cbv3h f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel p_dfbi2 e0_cleqh e1_cleqh f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel f0_cleqh p_hbim e1_cleqh e0_cleqh f1_cleqh a_sup_set_class f3_cleqh a_wcel f1_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh p_hbim f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wi f1_cleqh a_sup_set_class f3_cleqh a_wcel f1_cleqh a_sup_set_class f2_cleqh a_wcel a_wi f0_cleqh p_hban f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wi f1_cleqh a_sup_set_class f3_cleqh a_wcel f1_cleqh a_sup_set_class f2_cleqh a_wcel a_wi a_wa f0_cleqh p_hbxfrbi f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_ax-17 f0_cleqh a_sup_set_class f1_cleqh a_sup_set_class f2_cleqh p_eleq1 f0_cleqh a_sup_set_class f1_cleqh a_sup_set_class f3_cleqh p_eleq1 f0_cleqh a_sup_set_class f1_cleqh a_sup_set_class a_wceq f0_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel p_bibi12d f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb a_wb f0_cleqh f1_cleqh p_equcoms f1_cleqh a_sup_set_class f0_cleqh a_sup_set_class a_wceq f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb p_biimprd f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh f0_cleqh p_cbv3h f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f0_cleqh a_wal f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_wal p_impbii f2_cleqh f3_cleqh a_wceq f1_cleqh a_sup_set_class f2_cleqh a_wcel f1_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f1_cleqh a_wal f0_cleqh a_sup_set_class f2_cleqh a_wcel f0_cleqh a_sup_set_class f3_cleqh a_wcel a_wb f0_cleqh a_wal p_bitr4i $.
$}

$(A way of showing two classes are not equal.  (Contributed by NM,
     1-Apr-1997.) $)

${
	$v A B C  $.
	f0_nelneq $f class A $.
	f1_nelneq $f class B $.
	f2_nelneq $f class C $.
	p_nelneq $p |- ( ( A e. C /\ -. B e. C ) -> -. A = B ) $= f0_nelneq f1_nelneq f2_nelneq p_eleq1 f0_nelneq f1_nelneq a_wceq f0_nelneq f2_nelneq a_wcel f1_nelneq f2_nelneq a_wcel p_biimpcd f0_nelneq f2_nelneq a_wcel f0_nelneq f1_nelneq a_wceq f1_nelneq f2_nelneq a_wcel p_con3and $.
$}

$(A way of showing two classes are not equal.  (Contributed by NM,
     12-Jan-2002.) $)

${
	$v A B C  $.
	f0_nelneq2 $f class A $.
	f1_nelneq2 $f class B $.
	f2_nelneq2 $f class C $.
	p_nelneq2 $p |- ( ( A e. B /\ -. A e. C ) -> -. B = C ) $= f1_nelneq2 f2_nelneq2 f0_nelneq2 p_eleq2 f1_nelneq2 f2_nelneq2 a_wceq f0_nelneq2 f1_nelneq2 a_wcel f0_nelneq2 f2_nelneq2 a_wcel p_biimpcd f0_nelneq2 f1_nelneq2 a_wcel f1_nelneq2 f2_nelneq2 a_wceq f0_nelneq2 f2_nelneq2 a_wcel p_con3and $.
$}

$(Lemma for ~ eqsb3 .  (Contributed by Rodolfo Medina, 28-Apr-2010.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)

${
	$v x y A  $.
	$d x y  $.
	$d y A  $.
	f0_eqsb3lem $f set x $.
	f1_eqsb3lem $f set y $.
	f2_eqsb3lem $f class A $.
	p_eqsb3lem $p |- ( [ x / y ] y = A <-> x = A ) $= f0_eqsb3lem a_sup_set_class f2_eqsb3lem a_wceq f1_eqsb3lem p_nfv f1_eqsb3lem a_sup_set_class f0_eqsb3lem a_sup_set_class f2_eqsb3lem p_eqeq1 f1_eqsb3lem a_sup_set_class f2_eqsb3lem a_wceq f0_eqsb3lem a_sup_set_class f2_eqsb3lem a_wceq f1_eqsb3lem f0_eqsb3lem p_sbie $.
$}

$(Substitution applied to an atomic wff (class version of ~ equsb3 ).
       (Contributed by Rodolfo Medina, 28-Apr-2010.) $)

${
	$v x y A  $.
	$d y A  $.
	$d w y  $.
	$d w A  $.
	$d x w  $.
	f0_eqsb3 $f set x $.
	f1_eqsb3 $f set y $.
	f2_eqsb3 $f class A $.
	i0_eqsb3 $f set w $.
	p_eqsb3 $p |- ( [ x / y ] y = A <-> x = A ) $= i0_eqsb3 f1_eqsb3 f2_eqsb3 p_eqsb3lem f1_eqsb3 a_sup_set_class f2_eqsb3 a_wceq f1_eqsb3 i0_eqsb3 a_wsb i0_eqsb3 a_sup_set_class f2_eqsb3 a_wceq i0_eqsb3 f0_eqsb3 p_sbbii f1_eqsb3 a_sup_set_class f2_eqsb3 a_wceq i0_eqsb3 p_nfv f1_eqsb3 a_sup_set_class f2_eqsb3 a_wceq f1_eqsb3 f0_eqsb3 i0_eqsb3 p_sbco2 f0_eqsb3 i0_eqsb3 f2_eqsb3 p_eqsb3lem f1_eqsb3 a_sup_set_class f2_eqsb3 a_wceq f1_eqsb3 i0_eqsb3 a_wsb i0_eqsb3 f0_eqsb3 a_wsb i0_eqsb3 a_sup_set_class f2_eqsb3 a_wceq i0_eqsb3 f0_eqsb3 a_wsb f1_eqsb3 a_sup_set_class f2_eqsb3 a_wceq f1_eqsb3 f0_eqsb3 a_wsb f0_eqsb3 a_sup_set_class f2_eqsb3 a_wceq p_3bitr3i $.
$}

$(Substitution applied to an atomic wff (class version of ~ elsb3 ).
       (Contributed by Rodolfo Medina, 28-Apr-2010.)  (Proof shortened by
       Andrew Salmon, 14-Jun-2011.) $)

${
	$v x y A  $.
	$d y A  $.
	$d w y  $.
	$d w A  $.
	$d w x  $.
	f0_clelsb3 $f set x $.
	f1_clelsb3 $f set y $.
	f2_clelsb3 $f class A $.
	i0_clelsb3 $f set w $.
	p_clelsb3 $p |- ( [ x / y ] y e. A <-> x e. A ) $= i0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel f1_clelsb3 p_nfv i0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel i0_clelsb3 f0_clelsb3 f1_clelsb3 p_sbco2 f1_clelsb3 a_sup_set_class f2_clelsb3 a_wcel i0_clelsb3 p_nfv i0_clelsb3 a_sup_set_class f1_clelsb3 a_sup_set_class f2_clelsb3 p_eleq1 i0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel f1_clelsb3 a_sup_set_class f2_clelsb3 a_wcel i0_clelsb3 f1_clelsb3 p_sbie i0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel i0_clelsb3 f1_clelsb3 a_wsb f1_clelsb3 a_sup_set_class f2_clelsb3 a_wcel f1_clelsb3 f0_clelsb3 p_sbbii f0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel i0_clelsb3 p_nfv i0_clelsb3 a_sup_set_class f0_clelsb3 a_sup_set_class f2_clelsb3 p_eleq1 i0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel f0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel i0_clelsb3 f0_clelsb3 p_sbie i0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel i0_clelsb3 f1_clelsb3 a_wsb f1_clelsb3 f0_clelsb3 a_wsb i0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel i0_clelsb3 f0_clelsb3 a_wsb f1_clelsb3 a_sup_set_class f2_clelsb3 a_wcel f1_clelsb3 f0_clelsb3 a_wsb f0_clelsb3 a_sup_set_class f2_clelsb3 a_wcel p_3bitr3i $.
$}

$(A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfrbi for equivalence version.  (Contributed by NM,
       21-Aug-2007.) $)

${
	$v x y A B  $.
	f0_hbxfreq $f set x $.
	f1_hbxfreq $f set y $.
	f2_hbxfreq $f class A $.
	f3_hbxfreq $f class B $.
	e0_hbxfreq $e |- A = B $.
	e1_hbxfreq $e |- ( y e. B -> A. x y e. B ) $.
	p_hbxfreq $p |- ( y e. A -> A. x y e. A ) $= e0_hbxfreq f2_hbxfreq f3_hbxfreq f1_hbxfreq a_sup_set_class p_eleq2i e1_hbxfreq f1_hbxfreq a_sup_set_class f2_hbxfreq a_wcel f1_hbxfreq a_sup_set_class f3_hbxfreq a_wcel f0_hbxfreq p_hbxfrbi $.
$}

$(Change the free variable of a hypothesis builder.  Lemma for ~ nfcrii .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)

${
	$v x y z A  $.
	$d y A  $.
	$d x z  $.
	f0_hblem $f set x $.
	f1_hblem $f set y $.
	f2_hblem $f set z $.
	f3_hblem $f class A $.
	e0_hblem $e |- ( y e. A -> A. x y e. A ) $.
	p_hblem $p |- ( z e. A -> A. x z e. A ) $= e0_hblem f1_hblem a_sup_set_class f3_hblem a_wcel f1_hblem f2_hblem f0_hblem p_hbsb f2_hblem f1_hblem f3_hblem p_clelsb3 f2_hblem f1_hblem f3_hblem p_clelsb3 f1_hblem a_sup_set_class f3_hblem a_wcel f1_hblem f2_hblem a_wsb f2_hblem a_sup_set_class f3_hblem a_wcel f0_hblem p_albii f1_hblem a_sup_set_class f3_hblem a_wcel f1_hblem f2_hblem a_wsb f1_hblem a_sup_set_class f3_hblem a_wcel f1_hblem f2_hblem a_wsb f0_hblem a_wal f2_hblem a_sup_set_class f3_hblem a_wcel f2_hblem a_sup_set_class f3_hblem a_wcel f0_hblem a_wal p_3imtr3i $.
$}

$(Equality of a class variable and a class abstraction (also called a
       class builder).  Theorem 5.1 of [Quine] p. 34.  This theorem shows the
       relationship between expressions with class abstractions and expressions
       with class variables.  Note that ~ abbi and its relatives are among
       those useful for converting theorems with class variables to equivalent
       theorems with wff variables, by first substituting a class abstraction
       for each class variable.

       Class variables can always be eliminated from a theorem to result in an
       equivalent theorem with wff variables, and vice-versa.  The idea is
       roughly as follows.  To convert a theorem with a wff variable ` ph `
       (that has a free variable ` x ` ) to a theorem with a class variable
       ` A ` , we substitute ` x e. A ` for ` ph ` throughout and simplify,
       where ` A ` is a new class variable not already in the wff.  An example
       is the conversion of ~ zfauscl to ~ inex1 (look at the instance of
       ~ zfauscl that occurs in the proof of ~ inex1 ).  Conversely, to convert
       a theorem with a class variable ` A ` to one with ` ph ` , we substitute
       ` { x | ph } ` for ` A ` throughout and simplify, where ` x ` and ` ph `
       are new set and wff variables not already in the wff.  An example is
       ~ cp , which derives a formula containing wff variables from
       substitution instances of the class variables in its equivalent
       formulation ~ cplem2 .  For more information on class variables, see
       Quine pp. 15-21 and/or Takeuti and Zaring pp. 10-13.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph x A  $.
	$d x A y  $.
	$d ph y  $.
	f0_abeq2 $f wff ph $.
	f1_abeq2 $f set x $.
	f2_abeq2 $f class A $.
	i0_abeq2 $f set y $.
	p_abeq2 $p |- ( A = { x | ph } <-> A. x ( x e. A <-> ph ) ) $= i0_abeq2 a_sup_set_class f2_abeq2 a_wcel f1_abeq2 a_ax-17 f0_abeq2 f1_abeq2 i0_abeq2 p_hbab1 f1_abeq2 i0_abeq2 f2_abeq2 f0_abeq2 f1_abeq2 a_cab p_cleqh f0_abeq2 f1_abeq2 p_abid f1_abeq2 a_sup_set_class f0_abeq2 f1_abeq2 a_cab a_wcel f0_abeq2 f1_abeq2 a_sup_set_class f2_abeq2 a_wcel p_bibi2i f1_abeq2 a_sup_set_class f2_abeq2 a_wcel f1_abeq2 a_sup_set_class f0_abeq2 f1_abeq2 a_cab a_wcel a_wb f1_abeq2 a_sup_set_class f2_abeq2 a_wcel f0_abeq2 a_wb f1_abeq2 p_albii f2_abeq2 f0_abeq2 f1_abeq2 a_cab a_wceq f1_abeq2 a_sup_set_class f2_abeq2 a_wcel f1_abeq2 a_sup_set_class f0_abeq2 f1_abeq2 a_cab a_wcel a_wb f1_abeq2 a_wal f1_abeq2 a_sup_set_class f2_abeq2 a_wcel f0_abeq2 a_wb f1_abeq2 a_wal p_bitri $.
$}

$(Equality of a class variable and a class abstraction.  (Contributed by
       NM, 20-Aug-1993.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d ph  $.
	f0_abeq1 $f wff ph $.
	f1_abeq1 $f set x $.
	f2_abeq1 $f class A $.
	p_abeq1 $p |- ( { x | ph } = A <-> A. x ( ph <-> x e. A ) ) $= f0_abeq1 f1_abeq1 f2_abeq1 p_abeq2 f0_abeq1 f1_abeq1 a_cab f2_abeq1 p_eqcom f0_abeq1 f1_abeq1 a_sup_set_class f2_abeq1 a_wcel p_bicom f0_abeq1 f1_abeq1 a_sup_set_class f2_abeq1 a_wcel a_wb f1_abeq1 a_sup_set_class f2_abeq1 a_wcel f0_abeq1 a_wb f1_abeq1 p_albii f2_abeq1 f0_abeq1 f1_abeq1 a_cab a_wceq f1_abeq1 a_sup_set_class f2_abeq1 a_wcel f0_abeq1 a_wb f1_abeq1 a_wal f0_abeq1 f1_abeq1 a_cab f2_abeq1 a_wceq f0_abeq1 f1_abeq1 a_sup_set_class f2_abeq1 a_wcel a_wb f1_abeq1 a_wal p_3bitr4i $.
$}

$(Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 3-Apr-1996.) $)

${
	$v ph x A  $.
	f0_abeq2i $f wff ph $.
	f1_abeq2i $f set x $.
	f2_abeq2i $f class A $.
	e0_abeq2i $e |- A = { x | ph } $.
	p_abeq2i $p |- ( x e. A <-> ph ) $= e0_abeq2i f2_abeq2i f0_abeq2i f1_abeq2i a_cab f1_abeq2i a_sup_set_class p_eleq2i f0_abeq2i f1_abeq2i p_abid f1_abeq2i a_sup_set_class f2_abeq2i a_wcel f1_abeq2i a_sup_set_class f0_abeq2i f1_abeq2i a_cab a_wcel f0_abeq2i p_bitri $.
$}

$(Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 31-Jul-1994.) $)

${
	$v ph x A  $.
	f0_abeq1i $f wff ph $.
	f1_abeq1i $f set x $.
	f2_abeq1i $f class A $.
	e0_abeq1i $e |- { x | ph } = A $.
	p_abeq1i $p |- ( ph <-> x e. A ) $= f0_abeq1i f1_abeq1i p_abid e0_abeq1i f0_abeq1i f1_abeq1i a_cab f2_abeq1i f1_abeq1i a_sup_set_class p_eleq2i f0_abeq1i f1_abeq1i a_sup_set_class f0_abeq1i f1_abeq1i a_cab a_wcel f1_abeq1i a_sup_set_class f2_abeq1i a_wcel p_bitr3i $.
$}

$(Equality of a class variable and a class abstraction (deduction).
       (Contributed by NM, 16-Nov-1995.) $)

${
	$v ph ps x A  $.
	f0_abeq2d $f wff ph $.
	f1_abeq2d $f wff ps $.
	f2_abeq2d $f set x $.
	f3_abeq2d $f class A $.
	e0_abeq2d $e |- ( ph -> A = { x | ps } ) $.
	p_abeq2d $p |- ( ph -> ( x e. A <-> ps ) ) $= e0_abeq2d f0_abeq2d f3_abeq2d f1_abeq2d f2_abeq2d a_cab f2_abeq2d a_sup_set_class p_eleq2d f1_abeq2d f2_abeq2d p_abid f0_abeq2d f2_abeq2d a_sup_set_class f3_abeq2d a_wcel f2_abeq2d a_sup_set_class f1_abeq2d f2_abeq2d a_cab a_wcel f1_abeq2d p_syl6bb $.
$}

$(Equivalent wff's correspond to equal class abstractions.  (Contributed
       by NM, 25-Nov-2013.)  (Revised by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x  $.
	$d ph y  $.
	$d ps y  $.
	$d x y  $.
	f0_abbi $f wff ph $.
	f1_abbi $f wff ps $.
	f2_abbi $f set x $.
	i0_abbi $f set y $.
	p_abbi $p |- ( A. x ( ph <-> ps ) <-> { x | ph } = { x | ps } ) $= i0_abbi f0_abbi f2_abbi a_cab f1_abbi f2_abbi a_cab p_dfcleq f0_abbi f2_abbi i0_abbi p_nfsab1 f1_abbi f2_abbi i0_abbi p_nfsab1 i0_abbi a_sup_set_class f0_abbi f2_abbi a_cab a_wcel i0_abbi a_sup_set_class f1_abbi f2_abbi a_cab a_wcel f2_abbi p_nfbi f0_abbi f1_abbi a_wb i0_abbi p_nfv f0_abbi i0_abbi f2_abbi a_df-clab f0_abbi i0_abbi f2_abbi p_sbequ12r i0_abbi a_sup_set_class f0_abbi f2_abbi a_cab a_wcel f0_abbi f2_abbi i0_abbi a_wsb i0_abbi a_sup_set_class f2_abbi a_sup_set_class a_wceq f0_abbi p_syl5bb f1_abbi i0_abbi f2_abbi a_df-clab f1_abbi i0_abbi f2_abbi p_sbequ12r i0_abbi a_sup_set_class f1_abbi f2_abbi a_cab a_wcel f1_abbi f2_abbi i0_abbi a_wsb i0_abbi a_sup_set_class f2_abbi a_sup_set_class a_wceq f1_abbi p_syl5bb i0_abbi a_sup_set_class f2_abbi a_sup_set_class a_wceq i0_abbi a_sup_set_class f0_abbi f2_abbi a_cab a_wcel f0_abbi i0_abbi a_sup_set_class f1_abbi f2_abbi a_cab a_wcel f1_abbi p_bibi12d i0_abbi a_sup_set_class f0_abbi f2_abbi a_cab a_wcel i0_abbi a_sup_set_class f1_abbi f2_abbi a_cab a_wcel a_wb f0_abbi f1_abbi a_wb i0_abbi f2_abbi p_cbval f0_abbi f2_abbi a_cab f1_abbi f2_abbi a_cab a_wceq i0_abbi a_sup_set_class f0_abbi f2_abbi a_cab a_wcel i0_abbi a_sup_set_class f1_abbi f2_abbi a_cab a_wcel a_wb i0_abbi a_wal f0_abbi f1_abbi a_wb f2_abbi a_wal p_bitr2i $.
$}

$(Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_abbi2i $f wff ph $.
	f1_abbi2i $f set x $.
	f2_abbi2i $f class A $.
	e0_abbi2i $e |- ( x e. A <-> ph ) $.
	p_abbi2i $p |- A = { x | ph } $= f0_abbi2i f1_abbi2i f2_abbi2i p_abeq2 e0_abbi2i f2_abbi2i f0_abbi2i f1_abbi2i a_cab a_wceq f1_abbi2i a_sup_set_class f2_abbi2i a_wcel f0_abbi2i a_wb f1_abbi2i p_mpgbir $.
$}

$(Equivalent wff's yield equal class abstractions (inference rule).
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_abbii $f wff ph $.
	f1_abbii $f wff ps $.
	f2_abbii $f set x $.
	e0_abbii $e |- ( ph <-> ps ) $.
	p_abbii $p |- { x | ph } = { x | ps } $= f0_abbii f1_abbii f2_abbii p_abbi e0_abbii f0_abbii f1_abbii a_wb f0_abbii f2_abbii a_cab f1_abbii f2_abbii a_cab a_wceq f2_abbii p_mpgbi $.
$}

$(Theorem abbii is the congruence law for class abstraction. $)

$($j congruence 'abbii'; $)

$(` y ` is a dummy var. $)

$(Equivalent wff's yield equal class abstractions (deduction rule).
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph ps ch x  $.
	$d x  $.
	$d ph  $.
	$d ps  $.
	$d ch  $.
	f0_abbid $f wff ph $.
	f1_abbid $f wff ps $.
	f2_abbid $f wff ch $.
	f3_abbid $f set x $.
	e0_abbid $e |- F/ x ph $.
	e1_abbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_abbid $p |- ( ph -> { x | ps } = { x | ch } ) $= e0_abbid e1_abbid f0_abbid f1_abbid f2_abbid a_wb f3_abbid p_alrimi f1_abbid f2_abbid f3_abbid p_abbi f0_abbid f1_abbid f2_abbid a_wb f3_abbid a_wal f1_abbid f3_abbid a_cab f2_abbid f3_abbid a_cab a_wceq p_sylib $.
$}

$(Equivalent wff's yield equal class abstractions (deduction rule).
       (Contributed by NM, 10-Aug-1993.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_abbidv $f wff ph $.
	f1_abbidv $f wff ps $.
	f2_abbidv $f wff ch $.
	f3_abbidv $f set x $.
	e0_abbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_abbidv $p |- ( ph -> { x | ps } = { x | ch } ) $= f0_abbidv f3_abbidv p_nfv e0_abbidv f0_abbidv f1_abbidv f2_abbidv f3_abbidv p_abbid $.
$}

$(` y ` is a dummy var. $)

$(Deduction from a wff to a class abstraction.  (Contributed by NM,
       9-Jul-1994.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d ph x  $.
	$d ps  $.
	f0_abbi2dv $f wff ph $.
	f1_abbi2dv $f wff ps $.
	f2_abbi2dv $f set x $.
	f3_abbi2dv $f class A $.
	e0_abbi2dv $e |- ( ph -> ( x e. A <-> ps ) ) $.
	p_abbi2dv $p |- ( ph -> A = { x | ps } ) $= e0_abbi2dv f0_abbi2dv f2_abbi2dv a_sup_set_class f3_abbi2dv a_wcel f1_abbi2dv a_wb f2_abbi2dv p_alrimiv f1_abbi2dv f2_abbi2dv f3_abbi2dv p_abeq2 f0_abbi2dv f2_abbi2dv a_sup_set_class f3_abbi2dv a_wcel f1_abbi2dv a_wb f2_abbi2dv a_wal f3_abbi2dv f1_abbi2dv f2_abbi2dv a_cab a_wceq p_sylibr $.
$}

$(` y ` is a dummy var. $)

$(Deduction from a wff to a class abstraction.  (Contributed by NM,
       9-Jul-1994.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d ph x  $.
	$d ps  $.
	f0_abbi1dv $f wff ph $.
	f1_abbi1dv $f wff ps $.
	f2_abbi1dv $f set x $.
	f3_abbi1dv $f class A $.
	e0_abbi1dv $e |- ( ph -> ( ps <-> x e. A ) ) $.
	p_abbi1dv $p |- ( ph -> { x | ps } = A ) $= e0_abbi1dv f0_abbi1dv f1_abbi1dv f2_abbi1dv a_sup_set_class f3_abbi1dv a_wcel a_wb f2_abbi1dv p_alrimiv f1_abbi1dv f2_abbi1dv f3_abbi1dv p_abeq1 f0_abbi1dv f1_abbi1dv f2_abbi1dv a_sup_set_class f3_abbi1dv a_wcel a_wb f2_abbi1dv a_wal f1_abbi1dv f2_abbi1dv a_cab f3_abbi1dv a_wceq p_sylibr $.
$}

$(A simplification of class abstraction.  Theorem 5.2 of [Quine] p. 35.
       (Contributed by NM, 26-Dec-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_abid2 $f set x $.
	f1_abid2 $f class A $.
	p_abid2 $p |- { x | x e. A } = A $= f0_abid2 a_sup_set_class f1_abid2 a_wcel p_biid f0_abid2 a_sup_set_class f1_abid2 a_wcel f0_abid2 f1_abid2 p_abbi2i f1_abid2 f0_abid2 a_sup_set_class f1_abid2 a_wcel f0_abid2 a_cab p_eqcomi $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by Andrew Salmon, 11-Jul-2011.) $)

${
	$v ph ps x y  $.
	$d x z  $.
	$d y z  $.
	$d ph z  $.
	$d ps z  $.
	f0_cbvab $f wff ph $.
	f1_cbvab $f wff ps $.
	f2_cbvab $f set x $.
	f3_cbvab $f set y $.
	i0_cbvab $f set z $.
	e0_cbvab $e |- F/ y ph $.
	e1_cbvab $e |- F/ x ps $.
	e2_cbvab $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvab $p |- { x | ph } = { y | ps } $= e1_cbvab f1_cbvab f3_cbvab i0_cbvab f2_cbvab p_nfsb e0_cbvab e2_cbvab f0_cbvab f1_cbvab a_wb f2_cbvab f3_cbvab p_equcoms f3_cbvab a_sup_set_class f2_cbvab a_sup_set_class a_wceq f0_cbvab f1_cbvab p_bicomd f1_cbvab f0_cbvab f3_cbvab f2_cbvab p_sbie f1_cbvab f2_cbvab i0_cbvab f3_cbvab p_sbequ f0_cbvab f1_cbvab f3_cbvab f2_cbvab a_wsb f2_cbvab a_sup_set_class i0_cbvab a_sup_set_class a_wceq f1_cbvab f3_cbvab i0_cbvab a_wsb p_syl5bbr f0_cbvab f1_cbvab f3_cbvab i0_cbvab a_wsb f2_cbvab i0_cbvab p_sbie f0_cbvab i0_cbvab f2_cbvab a_df-clab f1_cbvab i0_cbvab f3_cbvab a_df-clab f0_cbvab f2_cbvab i0_cbvab a_wsb f1_cbvab f3_cbvab i0_cbvab a_wsb i0_cbvab a_sup_set_class f0_cbvab f2_cbvab a_cab a_wcel i0_cbvab a_sup_set_class f1_cbvab f3_cbvab a_cab a_wcel p_3bitr4i i0_cbvab f0_cbvab f2_cbvab a_cab f1_cbvab f3_cbvab a_cab p_eqriv $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-May-1999.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvabv $f wff ph $.
	f1_cbvabv $f wff ps $.
	f2_cbvabv $f set x $.
	f3_cbvabv $f set y $.
	e0_cbvabv $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvabv $p |- { x | ph } = { y | ps } $= f0_cbvabv f3_cbvabv p_nfv f1_cbvabv f2_cbvabv p_nfv e0_cbvabv f0_cbvabv f1_cbvabv f2_cbvabv f3_cbvabv p_cbvab $.
$}

$(Membership of a class variable in a class abstraction.  (Contributed by
       NM, 23-Dec-1993.) $)

${
	$v ph x A  $.
	$d x A y  $.
	$d ph y  $.
	f0_clelab $f wff ph $.
	f1_clelab $f set x $.
	f2_clelab $f class A $.
	i0_clelab $f set y $.
	p_clelab $p |- ( A e. { x | ph } <-> E. x ( x = A /\ ph ) ) $= f0_clelab i0_clelab f1_clelab a_df-clab i0_clelab a_sup_set_class f0_clelab f1_clelab a_cab a_wcel f0_clelab f1_clelab i0_clelab a_wsb i0_clelab a_sup_set_class f2_clelab a_wceq p_anbi2i i0_clelab a_sup_set_class f2_clelab a_wceq i0_clelab a_sup_set_class f0_clelab f1_clelab a_cab a_wcel a_wa i0_clelab a_sup_set_class f2_clelab a_wceq f0_clelab f1_clelab i0_clelab a_wsb a_wa i0_clelab p_exbii i0_clelab f2_clelab f0_clelab f1_clelab a_cab a_df-clel f1_clelab a_sup_set_class f2_clelab a_wceq f0_clelab a_wa i0_clelab p_nfv i0_clelab a_sup_set_class f2_clelab a_wceq f1_clelab p_nfv f0_clelab f1_clelab i0_clelab p_nfs1v i0_clelab a_sup_set_class f2_clelab a_wceq f0_clelab f1_clelab i0_clelab a_wsb f1_clelab p_nfan f1_clelab a_sup_set_class i0_clelab a_sup_set_class f2_clelab p_eqeq1 f0_clelab f1_clelab i0_clelab p_sbequ12 f1_clelab a_sup_set_class i0_clelab a_sup_set_class a_wceq f1_clelab a_sup_set_class f2_clelab a_wceq i0_clelab a_sup_set_class f2_clelab a_wceq f0_clelab f0_clelab f1_clelab i0_clelab a_wsb p_anbi12d f1_clelab a_sup_set_class f2_clelab a_wceq f0_clelab a_wa i0_clelab a_sup_set_class f2_clelab a_wceq f0_clelab f1_clelab i0_clelab a_wsb a_wa f1_clelab i0_clelab p_cbvex i0_clelab a_sup_set_class f2_clelab a_wceq i0_clelab a_sup_set_class f0_clelab f1_clelab a_cab a_wcel a_wa i0_clelab a_wex i0_clelab a_sup_set_class f2_clelab a_wceq f0_clelab f1_clelab i0_clelab a_wsb a_wa i0_clelab a_wex f2_clelab f0_clelab f1_clelab a_cab a_wcel f1_clelab a_sup_set_class f2_clelab a_wceq f0_clelab a_wa f1_clelab a_wex p_3bitr4i $.
$}

$(Membership of a class abstraction in another class.  (Contributed by NM,
       17-Jan-2006.) $)

${
	$v ph x y A  $.
	$d y A  $.
	$d y ph  $.
	$d x y  $.
	f0_clabel $f wff ph $.
	f1_clabel $f set x $.
	f2_clabel $f set y $.
	f3_clabel $f class A $.
	p_clabel $p |- ( { x | ph } e. A <-> E. y ( y e. A /\ A. x ( x e. y <-> ph ) ) ) $= f2_clabel f0_clabel f1_clabel a_cab f3_clabel a_df-clel f0_clabel f1_clabel f2_clabel a_sup_set_class p_abeq2 f2_clabel a_sup_set_class f0_clabel f1_clabel a_cab a_wceq f1_clabel a_sup_set_class f2_clabel a_sup_set_class a_wcel f0_clabel a_wb f1_clabel a_wal f2_clabel a_sup_set_class f3_clabel a_wcel p_anbi2ci f2_clabel a_sup_set_class f0_clabel f1_clabel a_cab a_wceq f2_clabel a_sup_set_class f3_clabel a_wcel a_wa f2_clabel a_sup_set_class f3_clabel a_wcel f1_clabel a_sup_set_class f2_clabel a_sup_set_class a_wcel f0_clabel a_wb f1_clabel a_wal a_wa f2_clabel p_exbii f0_clabel f1_clabel a_cab f3_clabel a_wcel f2_clabel a_sup_set_class f0_clabel f1_clabel a_cab a_wceq f2_clabel a_sup_set_class f3_clabel a_wcel a_wa f2_clabel a_wex f2_clabel a_sup_set_class f3_clabel a_wcel f1_clabel a_sup_set_class f2_clabel a_sup_set_class a_wcel f0_clabel a_wb f1_clabel a_wal a_wa f2_clabel a_wex p_bitri $.
$}

$(The right-hand side of the second equality is a way of representing
       proper substitution of ` y ` for ` x ` into a class variable.
       (Contributed by NM, 14-Sep-2003.) $)

${
	$v x y z A  $.
	$d z A  $.
	$d z x  $.
	$d z y  $.
	f0_sbab $f set x $.
	f1_sbab $f set y $.
	f2_sbab $f set z $.
	f3_sbab $f class A $.
	p_sbab $p |- ( x = y -> A = { z | [ y / x ] z e. A } ) $= f2_sbab a_sup_set_class f3_sbab a_wcel f0_sbab f1_sbab p_sbequ12 f0_sbab a_sup_set_class f1_sbab a_sup_set_class a_wceq f2_sbab a_sup_set_class f3_sbab a_wcel f0_sbab f1_sbab a_wsb f2_sbab f3_sbab p_abbi2dv $.
$}


