$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Introduce_the_Axiom_of_Extensionality.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Class abstractions (a.k.a. class builders)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Declare new constants use in class definition. */

$)
$c {  $.
$( /* Left brace */

$)
$c |  $.
$( /* Vertical bar */

$)
$c }  $.
$( /* Right brace */

$)
$( /* --- Start of old code before overloading prevention patch. */

$)
$( /* @c class @. @( Class variable type @)
  */

$)
$( /* --- End of old code before overloading prevention patch. */

$)
$( /* Declare symbols as variables */

$)
$( /* Declare variable symbols that will be used to represent classes.  Note
     that later on ` R ` , ` S ` , ` F ` and ` G ` denote relations and
     functions, but these letters serve as mnemonics only and in fact behave
     no differently from the variables ` A ` through ` D ` . */

$)
$( /* Introduce the class builder or class abstraction notation ("the class of
     sets ` x ` such that ` ph ` is true").  Our class variables ` A ` ,
     ` B ` , etc. range over class builders (implicitly in the case of defined
     class terms such as ~ df-nul ).  Note that a set variable can be expressed
     as a class builder per theorem ~ cvjust , justifying the assignment of set
     variables to class variables via the use of ~ cv . */

$)
${
	fcab_0 $f wff ph $.
	fcab_1 $f set x $.
	cab $a class { x | ph } $.
$}
$( /* --- Start of old code before overloading prevention patch. */

$)
$( /* @( A set variable is a class expression.  The syntax " ` class x ` " can be
     viewed as an abbreviation for " ` class { y | y e. x } ` " (a special case
     of ~ cab ), where ` y ` is distinct from ` x ` .  See the discussion under
     the definition of class in [Jech] p. 4.  Note that ` { y | y e. x } = x `
     by ~ cvjust . @)
  cv @a class x @.
  */

$)
$( /* --- End of old code before overloading prevention patch. */

$)
$( /* $j primitive 'cv' 'wceq' 'wcel' 'cab'; */

$)
$( /* Let ` A ` be a class variable. */

$)
$( /* Let ` B ` be a class variable. */

$)
$( /* Let ` C ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` D ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` P ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` Q ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` R ` be a class variable. */

$)
$( /* Let ` S ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` T ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` U ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` e ` be an individual variable. */

$)
$( /* Let ` f ` be an individual variable. */

$)
$( /* Let ` g ` be an individual variable. */

$)
$( /* Let ` h ` be an individual variable. */

$)
$( /* Let ` i ` be an individual variable. */

$)
$( /* Let ` j ` be an individual variable. */

$)
$( /* Let ` k ` be an individual variable. */

$)
$( /* Let ` m ` be an individual variable. */

$)
$( /* Let ` n ` be an individual variable. */

$)
$( /* Let ` o ` be an individual variable. */

$)
$( /* Let ` E ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` F ` be a class variable. */

$)
$( /* Let ` G ` be a class variable. */

$)
$( /* Let ` H ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` I ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` J ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` K ` be a class variable. */

$)
$( /* Let ` L ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` M ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` N ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` O ` be a class variable. */

$)
$( /* Let ` V ` be a class variable. */

$)
$( /* Let ` W ` be a class variable. */

$)
$( /* Let ` X ` be a class variable. */

$)
$( /* Let ` Y ` be a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Define a connective symbol for use as a class variable. */

$)
$( /* Let ` Z ` be a class variable. */

$)
$( /* Let ` s ` be an individual variable. */

$)
$( /* Let ` r ` be an individual variable. */

$)
$( /* Let ` q ` be an individual variable. */

$)
$( /* Let ` p ` be an individual variable. */

$)
$( /* Let ` a ` be an individual variable. */

$)
$( /* Let ` b ` be an individual variable. */

$)
$( /* Let ` c ` be an individual variable. */

$)
$( /* Let ` d ` be an individual variable. */

$)
$( /* Let ` l ` be an individual variable. */

$)
$( /* --- Start of old code before overloading prevention patch. */

$)
$( /* @( Extend wff definition to include class equality. @)
  wceq @a wff A = B @.
  */

$)
$( /* --- End of old code before overloading prevention patch. */

$)
$( /* --- Start of old code before overloading prevention patch. */

$)
$( /* @( Extend wff definition to include the membership connective between
     classes. @)
  wcel @a wff A e. B @.
  */

$)
$( /* --- End of old code before overloading prevention patch. */

$)
$( /* Define class abstraction notation (so-called by Quine), also called a
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
     5-Aug-1993.) */

$)
${
	fdf-clab_0 $f wff ph $.
	fdf-clab_1 $f set x $.
	fdf-clab_2 $f set y $.
	df-clab $a |- ( x e. { y | ph } <-> [ x / y ] ph ) $.
$}
$( /* Simplification of class abstraction notation when the free and bound
     variables are identical.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fabid_0 $f wff ph $.
	fabid_1 $f set x $.
	abid $p |- ( x e. { x | ph } <-> ph ) $= fabid_1 sup_set_class fabid_0 fabid_1 cab wcel fabid_0 fabid_1 fabid_1 wsb fabid_0 fabid_0 fabid_1 fabid_1 df-clab fabid_0 fabid_1 sbid bitri $.
$}
$( /* Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by NM, 5-Aug-1993.) */

$)
${
	$d x y $.
	fhbab1_0 $f wff ph $.
	fhbab1_1 $f set x $.
	fhbab1_2 $f set y $.
	hbab1 $p |- ( y e. { x | ph } -> A. x y e. { x | ph } ) $= fhbab1_2 sup_set_class fhbab1_0 fhbab1_1 cab wcel fhbab1_0 fhbab1_1 fhbab1_2 wsb fhbab1_1 fhbab1_0 fhbab1_2 fhbab1_1 df-clab fhbab1_0 fhbab1_1 fhbab1_2 hbs1 hbxfrbi $.
$}
$( /* Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) */

$)
${
	$d x y $.
	fnfsab1_0 $f wff ph $.
	fnfsab1_1 $f set x $.
	fnfsab1_2 $f set y $.
	nfsab1 $p |- F/ x y e. { x | ph } $= fnfsab1_2 sup_set_class fnfsab1_0 fnfsab1_1 cab wcel fnfsab1_1 fnfsab1_0 fnfsab1_1 fnfsab1_2 hbab1 nfi $.
$}
$( /* Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by NM, 1-Mar-1995.) */

$)
${
	$d x z $.
	fhbab_0 $f wff ph $.
	fhbab_1 $f set x $.
	fhbab_2 $f set y $.
	fhbab_3 $f set z $.
	ehbab_0 $e |- ( ph -> A. x ph ) $.
	hbab $p |- ( z e. { y | ph } -> A. x z e. { y | ph } ) $= fhbab_3 sup_set_class fhbab_0 fhbab_2 cab wcel fhbab_0 fhbab_2 fhbab_3 wsb fhbab_1 fhbab_0 fhbab_3 fhbab_2 df-clab fhbab_0 fhbab_2 fhbab_3 fhbab_1 ehbab_0 hbsb hbxfrbi $.
$}
$( /* Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) */

$)
${
	$d x z $.
	fnfsab_0 $f wff ph $.
	fnfsab_1 $f set x $.
	fnfsab_2 $f set y $.
	fnfsab_3 $f set z $.
	enfsab_0 $e |- F/ x ph $.
	nfsab $p |- F/ x z e. { y | ph } $= fnfsab_3 sup_set_class fnfsab_0 fnfsab_2 cab wcel fnfsab_1 fnfsab_0 fnfsab_1 fnfsab_2 fnfsab_3 fnfsab_0 fnfsab_1 enfsab_0 nfri hbab nfi $.
$}
$( /* Define the equality connective between classes.  Definition 2.7 of
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
       15-Sep-1993.) */

$)
${
	$d x A $.
	$d x B $.
	$d x y z $.
	fdf-cleq_0 $f set x $.
	fdf-cleq_1 $f set y $.
	fdf-cleq_2 $f set z $.
	fdf-cleq_3 $f class A $.
	fdf-cleq_4 $f class B $.
	edf-cleq_0 $e |- ( A. x ( x e. y <-> x e. z ) -> y = z ) $.
	df-cleq $a |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $.
$}
$( /* The same as ~ df-cleq with the hypothesis removed using the Axiom of
       Extensionality ~ ax-ext .  (Contributed by NM, 15-Sep-1993.) */

$)
${
	$d x A $.
	$d x B $.
	$d x y z $.
	idfcleq_0 $f set y $.
	idfcleq_1 $f set z $.
	fdfcleq_0 $f set x $.
	fdfcleq_1 $f class A $.
	fdfcleq_2 $f class B $.
	dfcleq $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $= fdfcleq_0 idfcleq_0 idfcleq_1 fdfcleq_1 fdfcleq_2 idfcleq_0 idfcleq_1 fdfcleq_0 ax-ext df-cleq $.
$}
$( /* Every set is a class.  Proposition 4.9 of [TakeutiZaring] p. 13.  This
       theorem shows that a set variable can be expressed as a class
       abstraction.  This provides a motivation for the class syntax
       construction ~ cv , which allows us to substitute a set variable for a
       class variable.  See also ~ cab and ~ df-clab .  Note that this is not a
       rigorous justification, because ~ cv is used as part of the proof of
       this theorem, but a careful argument can be made outside of the
       formalism of Metamath, for example as is done in Chapter 4 of Takeuti
       and Zaring.  See also the discussion under the definition of class in
       [Jech] p. 4 showing that "Every set can be considered to be a class."
       (Contributed by NM, 7-Nov-2006.) */

$)
${
	$d x y z $.
	icvjust_0 $f set z $.
	fcvjust_0 $f set x $.
	fcvjust_1 $f set y $.
	cvjust $p |- x = { y | y e. x } $= fcvjust_0 sup_set_class fcvjust_1 sup_set_class fcvjust_0 sup_set_class wcel fcvjust_1 cab wceq icvjust_0 sup_set_class fcvjust_0 sup_set_class wcel icvjust_0 sup_set_class fcvjust_1 sup_set_class fcvjust_0 sup_set_class wcel fcvjust_1 cab wcel wb icvjust_0 icvjust_0 fcvjust_0 sup_set_class fcvjust_1 sup_set_class fcvjust_0 sup_set_class wcel fcvjust_1 cab dfcleq icvjust_0 sup_set_class fcvjust_1 sup_set_class fcvjust_0 sup_set_class wcel fcvjust_1 cab wcel fcvjust_1 sup_set_class fcvjust_0 sup_set_class wcel fcvjust_1 icvjust_0 wsb icvjust_0 sup_set_class fcvjust_0 sup_set_class wcel fcvjust_1 sup_set_class fcvjust_0 sup_set_class wcel icvjust_0 fcvjust_1 df-clab icvjust_0 fcvjust_1 fcvjust_0 elsb3 bitr2i mpgbir $.
$}
$( /* Define the membership connective between classes.  Theorem 6.3 of
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
       5-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	fdf-clel_0 $f set x $.
	fdf-clel_1 $f class A $.
	fdf-clel_2 $f class B $.
	df-clel $a |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $.
$}
$( /* Infer equality of classes from equivalence of membership.  (Contributed
       by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	feqriv_0 $f set x $.
	feqriv_1 $f class A $.
	feqriv_2 $f class B $.
	eeqriv_0 $e |- ( x e. A <-> x e. B ) $.
	eqriv $p |- A = B $= feqriv_1 feqriv_2 wceq feqriv_0 sup_set_class feqriv_1 wcel feqriv_0 sup_set_class feqriv_2 wcel wb feqriv_0 feqriv_0 feqriv_1 feqriv_2 dfcleq eeqriv_0 mpgbir $.
$}
$( /* Deduce equality of classes from equivalence of membership.  (Contributed
       by NM, 17-Mar-1996.) */

$)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	feqrdv_0 $f wff ph $.
	feqrdv_1 $f set x $.
	feqrdv_2 $f class A $.
	feqrdv_3 $f class B $.
	eeqrdv_0 $e |- ( ph -> ( x e. A <-> x e. B ) ) $.
	eqrdv $p |- ( ph -> A = B ) $= feqrdv_0 feqrdv_1 sup_set_class feqrdv_2 wcel feqrdv_1 sup_set_class feqrdv_3 wcel wb feqrdv_1 wal feqrdv_2 feqrdv_3 wceq feqrdv_0 feqrdv_1 sup_set_class feqrdv_2 wcel feqrdv_1 sup_set_class feqrdv_3 wcel wb feqrdv_1 eeqrdv_0 alrimiv feqrdv_1 feqrdv_2 feqrdv_3 dfcleq sylibr $.
$}
$( /* Deduce equality of classes from an equivalence of membership that
       depends on the membership variable.  (Contributed by NM, 7-Nov-2008.) */

$)
$v C $.
${
	$d x A $.
	$d x B $.
	$d x ph $.
	feqrdav_0 $f wff ph $.
	feqrdav_1 $f set x $.
	feqrdav_2 $f class A $.
	feqrdav_3 $f class B $.
	feqrdav_4 $f class C $.
	eeqrdav_0 $e |- ( ( ph /\ x e. A ) -> x e. C ) $.
	eeqrdav_1 $e |- ( ( ph /\ x e. B ) -> x e. C ) $.
	eeqrdav_2 $e |- ( ( ph /\ x e. C ) -> ( x e. A <-> x e. B ) ) $.
	eqrdav $p |- ( ph -> A = B ) $= feqrdav_0 feqrdav_1 feqrdav_2 feqrdav_3 feqrdav_0 feqrdav_1 sup_set_class feqrdav_2 wcel feqrdav_1 sup_set_class feqrdav_3 wcel feqrdav_0 feqrdav_1 sup_set_class feqrdav_2 wcel wa feqrdav_1 sup_set_class feqrdav_4 wcel feqrdav_1 sup_set_class feqrdav_3 wcel eeqrdav_0 feqrdav_0 feqrdav_1 sup_set_class feqrdav_4 wcel feqrdav_1 sup_set_class feqrdav_2 wcel feqrdav_1 sup_set_class feqrdav_3 wcel feqrdav_0 feqrdav_1 sup_set_class feqrdav_4 wcel wa feqrdav_1 sup_set_class feqrdav_2 wcel feqrdav_1 sup_set_class feqrdav_3 wcel eeqrdav_2 biimpd impancom mpd feqrdav_0 feqrdav_1 sup_set_class feqrdav_3 wcel wa feqrdav_1 sup_set_class feqrdav_4 wcel feqrdav_1 sup_set_class feqrdav_2 wcel eeqrdav_1 feqrdav_0 feqrdav_1 sup_set_class feqrdav_3 wcel feqrdav_1 sup_set_class feqrdav_4 wcel feqrdav_1 sup_set_class feqrdav_2 wcel wi feqrdav_0 feqrdav_1 sup_set_class feqrdav_4 wcel feqrdav_1 sup_set_class feqrdav_3 wcel feqrdav_1 sup_set_class feqrdav_2 wcel feqrdav_0 feqrdav_1 sup_set_class feqrdav_4 wcel feqrdav_1 sup_set_class feqrdav_2 wcel feqrdav_1 sup_set_class feqrdav_3 wcel eeqrdav_2 exbiri com23 imp mpd impbida eqrdv $.
$}
$( /* Law of identity (reflexivity of class equality).  Theorem 6.4 of [Quine]
       p. 41.

       This law is thought to have originated with Aristotle (_Metaphysics_,
       Zeta, 17, 1041 a, 10-20:  "Therefore, inquiring why a thing is itself,
       it's inquiring nothing; ... saying that the thing is itself constitutes
       the sole reasoning and the sole cause, in every case, to the question of
       why the man is man or the musician musician.").  (Thanks to Stefan Allan
       and Beno&icirc;t Jubin for this information.)  (Contributed by NM,
       5-Aug-1993.)  (Revised by Beno&icirc;t Jubin, 14-Oct-2017.) */

$)
${
	$d x A $.
	ieqid_0 $f set x $.
	feqid_0 $f class A $.
	eqid $p |- A = A $= ieqid_0 feqid_0 feqid_0 ieqid_0 sup_set_class feqid_0 wcel biid eqriv $.
$}
$( /* Class identity law with antecedent.  (Contributed by NM, 21-Aug-2008.) */

$)
${
	feqidd_0 $f wff ph $.
	feqidd_1 $f class A $.
	eqidd $p |- ( ph -> A = A ) $= feqidd_1 feqidd_1 wceq feqidd_0 feqidd_1 eqid a1i $.
$}
$( /* Commutative law for class equality.  Theorem 6.5 of [Quine] p. 41.
       (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	ieqcom_0 $f set x $.
	feqcom_0 $f class A $.
	feqcom_1 $f class B $.
	eqcom $p |- ( A = B <-> B = A ) $= ieqcom_0 sup_set_class feqcom_0 wcel ieqcom_0 sup_set_class feqcom_1 wcel wb ieqcom_0 wal ieqcom_0 sup_set_class feqcom_1 wcel ieqcom_0 sup_set_class feqcom_0 wcel wb ieqcom_0 wal feqcom_0 feqcom_1 wceq feqcom_1 feqcom_0 wceq ieqcom_0 sup_set_class feqcom_0 wcel ieqcom_0 sup_set_class feqcom_1 wcel wb ieqcom_0 sup_set_class feqcom_1 wcel ieqcom_0 sup_set_class feqcom_0 wcel wb ieqcom_0 ieqcom_0 sup_set_class feqcom_0 wcel ieqcom_0 sup_set_class feqcom_1 wcel bicom albii ieqcom_0 feqcom_0 feqcom_1 dfcleq ieqcom_0 feqcom_1 feqcom_0 dfcleq 3bitr4i $.
$}
$( /* Inference applying commutative law for class equality to an antecedent.
       (Contributed by NM, 5-Aug-1993.) */

$)
${
	feqcoms_0 $f wff ph $.
	feqcoms_1 $f class A $.
	feqcoms_2 $f class B $.
	eeqcoms_0 $e |- ( A = B -> ph ) $.
	eqcoms $p |- ( B = A -> ph ) $= feqcoms_2 feqcoms_1 wceq feqcoms_1 feqcoms_2 wceq feqcoms_0 feqcoms_2 feqcoms_1 eqcom eeqcoms_0 sylbi $.
$}
$( /* Inference from commutative law for class equality.  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	feqcomi_0 $f class A $.
	feqcomi_1 $f class B $.
	eeqcomi_0 $e |- A = B $.
	eqcomi $p |- B = A $= feqcomi_0 feqcomi_1 wceq feqcomi_1 feqcomi_0 wceq eeqcomi_0 feqcomi_0 feqcomi_1 eqcom mpbi $.
$}
$( /* Deduction from commutative law for class equality.  (Contributed by NM,
       15-Aug-1994.) */

$)
${
	feqcomd_0 $f wff ph $.
	feqcomd_1 $f class A $.
	feqcomd_2 $f class B $.
	eeqcomd_0 $e |- ( ph -> A = B ) $.
	eqcomd $p |- ( ph -> B = A ) $= feqcomd_0 feqcomd_1 feqcomd_2 wceq feqcomd_2 feqcomd_1 wceq eeqcomd_0 feqcomd_1 feqcomd_2 eqcom sylib $.
$}
$( /* Equality implies equivalence of equalities.  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ieqeq1_0 $f set x $.
	feqeq1_0 $f class A $.
	feqeq1_1 $f class B $.
	feqeq1_2 $f class C $.
	eqeq1 $p |- ( A = B -> ( A = C <-> B = C ) ) $= feqeq1_0 feqeq1_1 wceq ieqeq1_0 sup_set_class feqeq1_0 wcel ieqeq1_0 sup_set_class feqeq1_2 wcel wb ieqeq1_0 wal ieqeq1_0 sup_set_class feqeq1_1 wcel ieqeq1_0 sup_set_class feqeq1_2 wcel wb ieqeq1_0 wal feqeq1_0 feqeq1_2 wceq feqeq1_1 feqeq1_2 wceq feqeq1_0 feqeq1_1 wceq ieqeq1_0 sup_set_class feqeq1_0 wcel ieqeq1_0 sup_set_class feqeq1_2 wcel wb ieqeq1_0 sup_set_class feqeq1_1 wcel ieqeq1_0 sup_set_class feqeq1_2 wcel wb ieqeq1_0 feqeq1_0 feqeq1_1 wceq ieqeq1_0 sup_set_class feqeq1_0 wcel ieqeq1_0 sup_set_class feqeq1_1 wcel ieqeq1_0 sup_set_class feqeq1_2 wcel feqeq1_0 feqeq1_1 wceq ieqeq1_0 sup_set_class feqeq1_0 wcel ieqeq1_0 sup_set_class feqeq1_1 wcel wb ieqeq1_0 feqeq1_0 feqeq1_1 wceq ieqeq1_0 sup_set_class feqeq1_0 wcel ieqeq1_0 sup_set_class feqeq1_1 wcel wb ieqeq1_0 wal ieqeq1_0 feqeq1_0 feqeq1_1 dfcleq biimpi 19.21bi bibi1d albidv ieqeq1_0 feqeq1_0 feqeq1_2 dfcleq ieqeq1_0 feqeq1_1 feqeq1_2 dfcleq 3bitr4g $.
$}
$( /* Inference from equality to equivalence of equalities.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feqeq1i_0 $f class A $.
	feqeq1i_1 $f class B $.
	feqeq1i_2 $f class C $.
	eeqeq1i_0 $e |- A = B $.
	eqeq1i $p |- ( A = C <-> B = C ) $= feqeq1i_0 feqeq1i_1 wceq feqeq1i_0 feqeq1i_2 wceq feqeq1i_1 feqeq1i_2 wceq wb eeqeq1i_0 feqeq1i_0 feqeq1i_1 feqeq1i_2 eqeq1 ax-mp $.
$}
$( /* Deduction from equality to equivalence of equalities.  (Contributed by
       NM, 27-Dec-1993.) */

$)
${
	feqeq1d_0 $f wff ph $.
	feqeq1d_1 $f class A $.
	feqeq1d_2 $f class B $.
	feqeq1d_3 $f class C $.
	eeqeq1d_0 $e |- ( ph -> A = B ) $.
	eqeq1d $p |- ( ph -> ( A = C <-> B = C ) ) $= feqeq1d_0 feqeq1d_1 feqeq1d_2 wceq feqeq1d_1 feqeq1d_3 wceq feqeq1d_2 feqeq1d_3 wceq wb eeqeq1d_0 feqeq1d_1 feqeq1d_2 feqeq1d_3 eqeq1 syl $.
$}
$( /* Equality implies equivalence of equalities.  (Contributed by NM,
     5-Aug-1993.) */

$)
${
	feqeq2_0 $f class A $.
	feqeq2_1 $f class B $.
	feqeq2_2 $f class C $.
	eqeq2 $p |- ( A = B -> ( C = A <-> C = B ) ) $= feqeq2_0 feqeq2_1 wceq feqeq2_0 feqeq2_2 wceq feqeq2_1 feqeq2_2 wceq feqeq2_2 feqeq2_0 wceq feqeq2_2 feqeq2_1 wceq feqeq2_0 feqeq2_1 feqeq2_2 eqeq1 feqeq2_2 feqeq2_0 eqcom feqeq2_2 feqeq2_1 eqcom 3bitr4g $.
$}
$( /* Inference from equality to equivalence of equalities.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feqeq2i_0 $f class A $.
	feqeq2i_1 $f class B $.
	feqeq2i_2 $f class C $.
	eeqeq2i_0 $e |- A = B $.
	eqeq2i $p |- ( C = A <-> C = B ) $= feqeq2i_0 feqeq2i_1 wceq feqeq2i_2 feqeq2i_0 wceq feqeq2i_2 feqeq2i_1 wceq wb eeqeq2i_0 feqeq2i_0 feqeq2i_1 feqeq2i_2 eqeq2 ax-mp $.
$}
$( /* Deduction from equality to equivalence of equalities.  (Contributed by
       NM, 27-Dec-1993.) */

$)
${
	feqeq2d_0 $f wff ph $.
	feqeq2d_1 $f class A $.
	feqeq2d_2 $f class B $.
	feqeq2d_3 $f class C $.
	eeqeq2d_0 $e |- ( ph -> A = B ) $.
	eqeq2d $p |- ( ph -> ( C = A <-> C = B ) ) $= feqeq2d_0 feqeq2d_1 feqeq2d_2 wceq feqeq2d_3 feqeq2d_1 wceq feqeq2d_3 feqeq2d_2 wceq wb eeqeq2d_0 feqeq2d_1 feqeq2d_2 feqeq2d_3 eqeq2 syl $.
$}
$( /* Equality relationship among 4 classes.  (Contributed by NM,
     3-Aug-1994.) */

$)
$v D $.
${
	feqeq12_0 $f class A $.
	feqeq12_1 $f class B $.
	feqeq12_2 $f class C $.
	feqeq12_3 $f class D $.
	eqeq12 $p |- ( ( A = B /\ C = D ) -> ( A = C <-> B = D ) ) $= feqeq12_0 feqeq12_1 wceq feqeq12_0 feqeq12_2 wceq feqeq12_1 feqeq12_2 wceq feqeq12_2 feqeq12_3 wceq feqeq12_1 feqeq12_3 wceq feqeq12_0 feqeq12_1 feqeq12_2 eqeq1 feqeq12_2 feqeq12_3 feqeq12_1 eqeq2 sylan9bb $.
$}
$( /* A useful inference for substituting definitions into an equality.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) */

$)
${
	feqeq12i_0 $f class A $.
	feqeq12i_1 $f class B $.
	feqeq12i_2 $f class C $.
	feqeq12i_3 $f class D $.
	eeqeq12i_0 $e |- A = B $.
	eeqeq12i_1 $e |- C = D $.
	eqeq12i $p |- ( A = C <-> B = D ) $= feqeq12i_0 feqeq12i_1 wceq feqeq12i_2 feqeq12i_3 wceq feqeq12i_0 feqeq12i_2 wceq feqeq12i_1 feqeq12i_3 wceq wb eeqeq12i_0 eeqeq12i_1 feqeq12i_0 feqeq12i_1 feqeq12i_2 feqeq12i_3 eqeq12 mp2an $.
$}
$( /* Theorem eqeq12i is the congruence law for equality. */

$)
$( /* $j congruence 'eqeq12i'; */

$)
$( /* A useful inference for substituting definitions into an equality.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) */

$)
${
	feqeq12d_0 $f wff ph $.
	feqeq12d_1 $f class A $.
	feqeq12d_2 $f class B $.
	feqeq12d_3 $f class C $.
	feqeq12d_4 $f class D $.
	eeqeq12d_0 $e |- ( ph -> A = B ) $.
	eeqeq12d_1 $e |- ( ph -> C = D ) $.
	eqeq12d $p |- ( ph -> ( A = C <-> B = D ) ) $= feqeq12d_0 feqeq12d_1 feqeq12d_2 wceq feqeq12d_3 feqeq12d_4 wceq feqeq12d_1 feqeq12d_3 wceq feqeq12d_2 feqeq12d_4 wceq wb eeqeq12d_0 eeqeq12d_1 feqeq12d_1 feqeq12d_2 feqeq12d_3 feqeq12d_4 eqeq12 syl2anc $.
$}
$( /* A useful inference for substituting definitions into an equality.
       (Contributed by NM, 9-Aug-1994.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) */

$)
${
	feqeqan12d_0 $f wff ph $.
	feqeqan12d_1 $f wff ps $.
	feqeqan12d_2 $f class A $.
	feqeqan12d_3 $f class B $.
	feqeqan12d_4 $f class C $.
	feqeqan12d_5 $f class D $.
	eeqeqan12d_0 $e |- ( ph -> A = B ) $.
	eeqeqan12d_1 $e |- ( ps -> C = D ) $.
	eqeqan12d $p |- ( ( ph /\ ps ) -> ( A = C <-> B = D ) ) $= feqeqan12d_0 feqeqan12d_2 feqeqan12d_3 wceq feqeqan12d_4 feqeqan12d_5 wceq feqeqan12d_2 feqeqan12d_4 wceq feqeqan12d_3 feqeqan12d_5 wceq wb feqeqan12d_1 eeqeqan12d_0 eeqeqan12d_1 feqeqan12d_2 feqeqan12d_3 feqeqan12d_4 feqeqan12d_5 eqeq12 syl2an $.
$}
$( /* A useful inference for substituting definitions into an equality.
       (Contributed by NM, 9-Aug-1994.) */

$)
${
	feqeqan12rd_0 $f wff ph $.
	feqeqan12rd_1 $f wff ps $.
	feqeqan12rd_2 $f class A $.
	feqeqan12rd_3 $f class B $.
	feqeqan12rd_4 $f class C $.
	feqeqan12rd_5 $f class D $.
	eeqeqan12rd_0 $e |- ( ph -> A = B ) $.
	eeqeqan12rd_1 $e |- ( ps -> C = D ) $.
	eqeqan12rd $p |- ( ( ps /\ ph ) -> ( A = C <-> B = D ) ) $= feqeqan12rd_0 feqeqan12rd_1 feqeqan12rd_2 feqeqan12rd_4 wceq feqeqan12rd_3 feqeqan12rd_5 wceq wb feqeqan12rd_0 feqeqan12rd_1 feqeqan12rd_2 feqeqan12rd_3 feqeqan12rd_4 feqeqan12rd_5 eeqeqan12rd_0 eeqeqan12rd_1 eqeqan12d ancoms $.
$}
$( /* Transitive law for class equality.  Proposition 4.7(3) of [TakeutiZaring]
     p. 13.  (Contributed by NM, 25-Jan-2004.) */

$)
${
	feqtr_0 $f class A $.
	feqtr_1 $f class B $.
	feqtr_2 $f class C $.
	eqtr $p |- ( ( A = B /\ B = C ) -> A = C ) $= feqtr_0 feqtr_1 wceq feqtr_0 feqtr_2 wceq feqtr_1 feqtr_2 wceq feqtr_0 feqtr_1 feqtr_2 eqeq1 biimpar $.
$}
$( /* A transitive law for class equality.  (Contributed by NM, 20-May-2005.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	feqtr2_0 $f class A $.
	feqtr2_1 $f class B $.
	feqtr2_2 $f class C $.
	eqtr2 $p |- ( ( A = B /\ A = C ) -> B = C ) $= feqtr2_0 feqtr2_1 wceq feqtr2_1 feqtr2_0 wceq feqtr2_0 feqtr2_2 wceq feqtr2_1 feqtr2_2 wceq feqtr2_0 feqtr2_1 eqcom feqtr2_1 feqtr2_0 feqtr2_2 eqtr sylanb $.
$}
$( /* A transitive law for class equality.  (Contributed by NM, 20-May-2005.) */

$)
${
	feqtr3_0 $f class A $.
	feqtr3_1 $f class B $.
	feqtr3_2 $f class C $.
	eqtr3 $p |- ( ( A = C /\ B = C ) -> A = B ) $= feqtr3_1 feqtr3_2 wceq feqtr3_0 feqtr3_2 wceq feqtr3_2 feqtr3_1 wceq feqtr3_0 feqtr3_1 wceq feqtr3_1 feqtr3_2 eqcom feqtr3_0 feqtr3_2 feqtr3_1 eqtr sylan2b $.
$}
$( /* An equality transitivity inference.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	feqtri_0 $f class A $.
	feqtri_1 $f class B $.
	feqtri_2 $f class C $.
	eeqtri_0 $e |- A = B $.
	eeqtri_1 $e |- B = C $.
	eqtri $p |- A = C $= feqtri_0 feqtri_1 wceq feqtri_0 feqtri_2 wceq eeqtri_0 feqtri_1 feqtri_2 feqtri_0 eeqtri_1 eqeq2i mpbi $.
$}
$( /* An equality transitivity inference.  (Contributed by NM,
       21-Feb-1995.) */

$)
${
	feqtr2i_0 $f class A $.
	feqtr2i_1 $f class B $.
	feqtr2i_2 $f class C $.
	eeqtr2i_0 $e |- A = B $.
	eeqtr2i_1 $e |- B = C $.
	eqtr2i $p |- C = A $= feqtr2i_0 feqtr2i_2 feqtr2i_0 feqtr2i_1 feqtr2i_2 eeqtr2i_0 eeqtr2i_1 eqtri eqcomi $.
$}
$( /* An equality transitivity inference.  (Contributed by NM, 6-May-1994.) */

$)
${
	feqtr3i_0 $f class A $.
	feqtr3i_1 $f class B $.
	feqtr3i_2 $f class C $.
	eeqtr3i_0 $e |- A = B $.
	eeqtr3i_1 $e |- A = C $.
	eqtr3i $p |- B = C $= feqtr3i_1 feqtr3i_0 feqtr3i_2 feqtr3i_0 feqtr3i_1 eeqtr3i_0 eqcomi eeqtr3i_1 eqtri $.
$}
$( /* An equality transitivity inference.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	feqtr4i_0 $f class A $.
	feqtr4i_1 $f class B $.
	feqtr4i_2 $f class C $.
	eeqtr4i_0 $e |- A = B $.
	eeqtr4i_1 $e |- C = B $.
	eqtr4i $p |- A = C $= feqtr4i_0 feqtr4i_1 feqtr4i_2 eeqtr4i_0 feqtr4i_2 feqtr4i_1 eeqtr4i_1 eqcomi eqtri $.
$}
$( /* Register '=' as an equality for its type (class). */

$)
$( /* $j equality 'wceq' from 'eqid' 'eqcomi' 'eqtri'; */

$)
$( /* An inference from three chained equalities.  (Contributed by NM,
       29-Aug-1993.) */

$)
${
	f3eqtri_0 $f class A $.
	f3eqtri_1 $f class B $.
	f3eqtri_2 $f class C $.
	f3eqtri_3 $f class D $.
	e3eqtri_0 $e |- A = B $.
	e3eqtri_1 $e |- B = C $.
	e3eqtri_2 $e |- C = D $.
	3eqtri $p |- A = D $= f3eqtri_0 f3eqtri_1 f3eqtri_3 e3eqtri_0 f3eqtri_1 f3eqtri_2 f3eqtri_3 e3eqtri_1 e3eqtri_2 eqtri eqtri $.
$}
$( /* An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	f3eqtrri_0 $f class A $.
	f3eqtrri_1 $f class B $.
	f3eqtrri_2 $f class C $.
	f3eqtrri_3 $f class D $.
	e3eqtrri_0 $e |- A = B $.
	e3eqtrri_1 $e |- B = C $.
	e3eqtrri_2 $e |- C = D $.
	3eqtrri $p |- D = A $= f3eqtrri_0 f3eqtrri_2 f3eqtrri_3 f3eqtrri_0 f3eqtrri_1 f3eqtrri_2 e3eqtrri_0 e3eqtrri_1 eqtri e3eqtrri_2 eqtr2i $.
$}
$( /* An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.) */

$)
${
	f3eqtr2i_0 $f class A $.
	f3eqtr2i_1 $f class B $.
	f3eqtr2i_2 $f class C $.
	f3eqtr2i_3 $f class D $.
	e3eqtr2i_0 $e |- A = B $.
	e3eqtr2i_1 $e |- C = B $.
	e3eqtr2i_2 $e |- C = D $.
	3eqtr2i $p |- A = D $= f3eqtr2i_0 f3eqtr2i_2 f3eqtr2i_3 f3eqtr2i_0 f3eqtr2i_1 f3eqtr2i_2 e3eqtr2i_0 e3eqtr2i_1 eqtr4i e3eqtr2i_2 eqtri $.
$}
$( /* An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	f3eqtr2ri_0 $f class A $.
	f3eqtr2ri_1 $f class B $.
	f3eqtr2ri_2 $f class C $.
	f3eqtr2ri_3 $f class D $.
	e3eqtr2ri_0 $e |- A = B $.
	e3eqtr2ri_1 $e |- C = B $.
	e3eqtr2ri_2 $e |- C = D $.
	3eqtr2ri $p |- D = A $= f3eqtr2ri_0 f3eqtr2ri_2 f3eqtr2ri_3 f3eqtr2ri_0 f3eqtr2ri_1 f3eqtr2ri_2 e3eqtr2ri_0 e3eqtr2ri_1 eqtr4i e3eqtr2ri_2 eqtr2i $.
$}
$( /* An inference from three chained equalities.  (Contributed by NM,
       6-May-1994.)  (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	f3eqtr3i_0 $f class A $.
	f3eqtr3i_1 $f class B $.
	f3eqtr3i_2 $f class C $.
	f3eqtr3i_3 $f class D $.
	e3eqtr3i_0 $e |- A = B $.
	e3eqtr3i_1 $e |- A = C $.
	e3eqtr3i_2 $e |- B = D $.
	3eqtr3i $p |- C = D $= f3eqtr3i_1 f3eqtr3i_2 f3eqtr3i_3 f3eqtr3i_0 f3eqtr3i_1 f3eqtr3i_2 e3eqtr3i_0 e3eqtr3i_1 eqtr3i e3eqtr3i_2 eqtr3i $.
$}
$( /* An inference from three chained equalities.  (Contributed by NM,
       15-Aug-2004.) */

$)
${
	f3eqtr3ri_0 $f class A $.
	f3eqtr3ri_1 $f class B $.
	f3eqtr3ri_2 $f class C $.
	f3eqtr3ri_3 $f class D $.
	e3eqtr3ri_0 $e |- A = B $.
	e3eqtr3ri_1 $e |- A = C $.
	e3eqtr3ri_2 $e |- B = D $.
	3eqtr3ri $p |- D = C $= f3eqtr3ri_1 f3eqtr3ri_3 f3eqtr3ri_2 e3eqtr3ri_2 f3eqtr3ri_0 f3eqtr3ri_1 f3eqtr3ri_2 e3eqtr3ri_0 e3eqtr3ri_1 eqtr3i eqtr3i $.
$}
$( /* An inference from three chained equalities.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	f3eqtr4i_0 $f class A $.
	f3eqtr4i_1 $f class B $.
	f3eqtr4i_2 $f class C $.
	f3eqtr4i_3 $f class D $.
	e3eqtr4i_0 $e |- A = B $.
	e3eqtr4i_1 $e |- C = A $.
	e3eqtr4i_2 $e |- D = B $.
	3eqtr4i $p |- C = D $= f3eqtr4i_2 f3eqtr4i_0 f3eqtr4i_3 e3eqtr4i_1 f3eqtr4i_3 f3eqtr4i_1 f3eqtr4i_0 e3eqtr4i_2 e3eqtr4i_0 eqtr4i eqtr4i $.
$}
$( /* An inference from three chained equalities.  (Contributed by NM,
       2-Sep-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	f3eqtr4ri_0 $f class A $.
	f3eqtr4ri_1 $f class B $.
	f3eqtr4ri_2 $f class C $.
	f3eqtr4ri_3 $f class D $.
	e3eqtr4ri_0 $e |- A = B $.
	e3eqtr4ri_1 $e |- C = A $.
	e3eqtr4ri_2 $e |- D = B $.
	3eqtr4ri $p |- D = C $= f3eqtr4ri_3 f3eqtr4ri_0 f3eqtr4ri_2 f3eqtr4ri_3 f3eqtr4ri_1 f3eqtr4ri_0 e3eqtr4ri_2 e3eqtr4ri_0 eqtr4i e3eqtr4ri_1 eqtr4i $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	feqtrd_0 $f wff ph $.
	feqtrd_1 $f class A $.
	feqtrd_2 $f class B $.
	feqtrd_3 $f class C $.
	eeqtrd_0 $e |- ( ph -> A = B ) $.
	eeqtrd_1 $e |- ( ph -> B = C ) $.
	eqtrd $p |- ( ph -> A = C ) $= feqtrd_0 feqtrd_1 feqtrd_2 wceq feqtrd_1 feqtrd_3 wceq eeqtrd_0 feqtrd_0 feqtrd_2 feqtrd_3 feqtrd_1 eeqtrd_1 eqeq2d mpbid $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM,
       18-Oct-1999.) */

$)
${
	feqtr2d_0 $f wff ph $.
	feqtr2d_1 $f class A $.
	feqtr2d_2 $f class B $.
	feqtr2d_3 $f class C $.
	eeqtr2d_0 $e |- ( ph -> A = B ) $.
	eeqtr2d_1 $e |- ( ph -> B = C ) $.
	eqtr2d $p |- ( ph -> C = A ) $= feqtr2d_0 feqtr2d_1 feqtr2d_3 feqtr2d_0 feqtr2d_1 feqtr2d_2 feqtr2d_3 eeqtr2d_0 eeqtr2d_1 eqtrd eqcomd $.
$}
$( /* An equality transitivity equality deduction.  (Contributed by NM,
       18-Jul-1995.) */

$)
${
	feqtr3d_0 $f wff ph $.
	feqtr3d_1 $f class A $.
	feqtr3d_2 $f class B $.
	feqtr3d_3 $f class C $.
	eeqtr3d_0 $e |- ( ph -> A = B ) $.
	eeqtr3d_1 $e |- ( ph -> A = C ) $.
	eqtr3d $p |- ( ph -> B = C ) $= feqtr3d_0 feqtr3d_2 feqtr3d_1 feqtr3d_3 feqtr3d_0 feqtr3d_1 feqtr3d_2 eeqtr3d_0 eqcomd eeqtr3d_1 eqtrd $.
$}
$( /* An equality transitivity equality deduction.  (Contributed by NM,
       18-Jul-1995.) */

$)
${
	feqtr4d_0 $f wff ph $.
	feqtr4d_1 $f class A $.
	feqtr4d_2 $f class B $.
	feqtr4d_3 $f class C $.
	eeqtr4d_0 $e |- ( ph -> A = B ) $.
	eeqtr4d_1 $e |- ( ph -> C = B ) $.
	eqtr4d $p |- ( ph -> A = C ) $= feqtr4d_0 feqtr4d_1 feqtr4d_2 feqtr4d_3 eeqtr4d_0 feqtr4d_0 feqtr4d_3 feqtr4d_2 eeqtr4d_1 eqcomd eqtrd $.
$}
$( /* A deduction from three chained equalities.  (Contributed by NM,
       29-Oct-1995.) */

$)
${
	f3eqtrd_0 $f wff ph $.
	f3eqtrd_1 $f class A $.
	f3eqtrd_2 $f class B $.
	f3eqtrd_3 $f class C $.
	f3eqtrd_4 $f class D $.
	e3eqtrd_0 $e |- ( ph -> A = B ) $.
	e3eqtrd_1 $e |- ( ph -> B = C ) $.
	e3eqtrd_2 $e |- ( ph -> C = D ) $.
	3eqtrd $p |- ( ph -> A = D ) $= f3eqtrd_0 f3eqtrd_1 f3eqtrd_2 f3eqtrd_4 e3eqtrd_0 f3eqtrd_0 f3eqtrd_2 f3eqtrd_3 f3eqtrd_4 e3eqtrd_1 e3eqtrd_2 eqtrd eqtrd $.
$}
$( /* A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	f3eqtrrd_0 $f wff ph $.
	f3eqtrrd_1 $f class A $.
	f3eqtrrd_2 $f class B $.
	f3eqtrrd_3 $f class C $.
	f3eqtrrd_4 $f class D $.
	e3eqtrrd_0 $e |- ( ph -> A = B ) $.
	e3eqtrrd_1 $e |- ( ph -> B = C ) $.
	e3eqtrrd_2 $e |- ( ph -> C = D ) $.
	3eqtrrd $p |- ( ph -> D = A ) $= f3eqtrrd_0 f3eqtrrd_1 f3eqtrrd_3 f3eqtrrd_4 f3eqtrrd_0 f3eqtrrd_1 f3eqtrrd_2 f3eqtrrd_3 e3eqtrrd_0 e3eqtrrd_1 eqtrd e3eqtrrd_2 eqtr2d $.
$}
$( /* A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.) */

$)
${
	f3eqtr2d_0 $f wff ph $.
	f3eqtr2d_1 $f class A $.
	f3eqtr2d_2 $f class B $.
	f3eqtr2d_3 $f class C $.
	f3eqtr2d_4 $f class D $.
	e3eqtr2d_0 $e |- ( ph -> A = B ) $.
	e3eqtr2d_1 $e |- ( ph -> C = B ) $.
	e3eqtr2d_2 $e |- ( ph -> C = D ) $.
	3eqtr2d $p |- ( ph -> A = D ) $= f3eqtr2d_0 f3eqtr2d_1 f3eqtr2d_3 f3eqtr2d_4 f3eqtr2d_0 f3eqtr2d_1 f3eqtr2d_2 f3eqtr2d_3 e3eqtr2d_0 e3eqtr2d_1 eqtr4d e3eqtr2d_2 eqtrd $.
$}
$( /* A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.) */

$)
${
	f3eqtr2rd_0 $f wff ph $.
	f3eqtr2rd_1 $f class A $.
	f3eqtr2rd_2 $f class B $.
	f3eqtr2rd_3 $f class C $.
	f3eqtr2rd_4 $f class D $.
	e3eqtr2rd_0 $e |- ( ph -> A = B ) $.
	e3eqtr2rd_1 $e |- ( ph -> C = B ) $.
	e3eqtr2rd_2 $e |- ( ph -> C = D ) $.
	3eqtr2rd $p |- ( ph -> D = A ) $= f3eqtr2rd_0 f3eqtr2rd_1 f3eqtr2rd_3 f3eqtr2rd_4 f3eqtr2rd_0 f3eqtr2rd_1 f3eqtr2rd_2 f3eqtr2rd_3 e3eqtr2rd_0 e3eqtr2rd_1 eqtr4d e3eqtr2rd_2 eqtr2d $.
$}
$( /* A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	f3eqtr3d_0 $f wff ph $.
	f3eqtr3d_1 $f class A $.
	f3eqtr3d_2 $f class B $.
	f3eqtr3d_3 $f class C $.
	f3eqtr3d_4 $f class D $.
	e3eqtr3d_0 $e |- ( ph -> A = B ) $.
	e3eqtr3d_1 $e |- ( ph -> A = C ) $.
	e3eqtr3d_2 $e |- ( ph -> B = D ) $.
	3eqtr3d $p |- ( ph -> C = D ) $= f3eqtr3d_0 f3eqtr3d_2 f3eqtr3d_3 f3eqtr3d_4 f3eqtr3d_0 f3eqtr3d_1 f3eqtr3d_2 f3eqtr3d_3 e3eqtr3d_0 e3eqtr3d_1 eqtr3d e3eqtr3d_2 eqtr3d $.
$}
$( /* A deduction from three chained equalities.  (Contributed by NM,
       14-Jan-2006.) */

$)
${
	f3eqtr3rd_0 $f wff ph $.
	f3eqtr3rd_1 $f class A $.
	f3eqtr3rd_2 $f class B $.
	f3eqtr3rd_3 $f class C $.
	f3eqtr3rd_4 $f class D $.
	e3eqtr3rd_0 $e |- ( ph -> A = B ) $.
	e3eqtr3rd_1 $e |- ( ph -> A = C ) $.
	e3eqtr3rd_2 $e |- ( ph -> B = D ) $.
	3eqtr3rd $p |- ( ph -> D = C ) $= f3eqtr3rd_0 f3eqtr3rd_2 f3eqtr3rd_4 f3eqtr3rd_3 e3eqtr3rd_2 f3eqtr3rd_0 f3eqtr3rd_1 f3eqtr3rd_2 f3eqtr3rd_3 e3eqtr3rd_0 e3eqtr3rd_1 eqtr3d eqtr3d $.
$}
$( /* A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	f3eqtr4d_0 $f wff ph $.
	f3eqtr4d_1 $f class A $.
	f3eqtr4d_2 $f class B $.
	f3eqtr4d_3 $f class C $.
	f3eqtr4d_4 $f class D $.
	e3eqtr4d_0 $e |- ( ph -> A = B ) $.
	e3eqtr4d_1 $e |- ( ph -> C = A ) $.
	e3eqtr4d_2 $e |- ( ph -> D = B ) $.
	3eqtr4d $p |- ( ph -> C = D ) $= f3eqtr4d_0 f3eqtr4d_3 f3eqtr4d_1 f3eqtr4d_4 e3eqtr4d_1 f3eqtr4d_0 f3eqtr4d_4 f3eqtr4d_2 f3eqtr4d_1 e3eqtr4d_2 e3eqtr4d_0 eqtr4d eqtr4d $.
$}
$( /* A deduction from three chained equalities.  (Contributed by NM,
       21-Sep-1995.) */

$)
${
	f3eqtr4rd_0 $f wff ph $.
	f3eqtr4rd_1 $f class A $.
	f3eqtr4rd_2 $f class B $.
	f3eqtr4rd_3 $f class C $.
	f3eqtr4rd_4 $f class D $.
	e3eqtr4rd_0 $e |- ( ph -> A = B ) $.
	e3eqtr4rd_1 $e |- ( ph -> C = A ) $.
	e3eqtr4rd_2 $e |- ( ph -> D = B ) $.
	3eqtr4rd $p |- ( ph -> D = C ) $= f3eqtr4rd_0 f3eqtr4rd_4 f3eqtr4rd_1 f3eqtr4rd_3 f3eqtr4rd_0 f3eqtr4rd_4 f3eqtr4rd_2 f3eqtr4rd_1 e3eqtr4rd_2 e3eqtr4rd_0 eqtr4d e3eqtr4rd_1 eqtr4d $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fsyl5eq_0 $f wff ph $.
	fsyl5eq_1 $f class A $.
	fsyl5eq_2 $f class B $.
	fsyl5eq_3 $f class C $.
	esyl5eq_0 $e |- A = B $.
	esyl5eq_1 $e |- ( ph -> B = C ) $.
	syl5eq $p |- ( ph -> A = C ) $= fsyl5eq_0 fsyl5eq_1 fsyl5eq_2 fsyl5eq_3 fsyl5eq_1 fsyl5eq_2 wceq fsyl5eq_0 esyl5eq_0 a1i esyl5eq_1 eqtrd $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) */

$)
${
	fsyl5req_0 $f wff ph $.
	fsyl5req_1 $f class A $.
	fsyl5req_2 $f class B $.
	fsyl5req_3 $f class C $.
	esyl5req_0 $e |- A = B $.
	esyl5req_1 $e |- ( ph -> B = C ) $.
	syl5req $p |- ( ph -> C = A ) $= fsyl5req_0 fsyl5req_1 fsyl5req_3 fsyl5req_0 fsyl5req_1 fsyl5req_2 fsyl5req_3 esyl5req_0 esyl5req_1 syl5eq eqcomd $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fsyl5eqr_0 $f wff ph $.
	fsyl5eqr_1 $f class A $.
	fsyl5eqr_2 $f class B $.
	fsyl5eqr_3 $f class C $.
	esyl5eqr_0 $e |- B = A $.
	esyl5eqr_1 $e |- ( ph -> B = C ) $.
	syl5eqr $p |- ( ph -> A = C ) $= fsyl5eqr_0 fsyl5eqr_1 fsyl5eqr_2 fsyl5eqr_3 fsyl5eqr_2 fsyl5eqr_1 esyl5eqr_0 eqcomi esyl5eqr_1 syl5eq $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) */

$)
${
	fsyl5reqr_0 $f wff ph $.
	fsyl5reqr_1 $f class A $.
	fsyl5reqr_2 $f class B $.
	fsyl5reqr_3 $f class C $.
	esyl5reqr_0 $e |- B = A $.
	esyl5reqr_1 $e |- ( ph -> B = C ) $.
	syl5reqr $p |- ( ph -> C = A ) $= fsyl5reqr_0 fsyl5reqr_1 fsyl5reqr_2 fsyl5reqr_3 fsyl5reqr_2 fsyl5reqr_1 esyl5reqr_0 eqcomi esyl5reqr_1 syl5req $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fsyl6eq_0 $f wff ph $.
	fsyl6eq_1 $f class A $.
	fsyl6eq_2 $f class B $.
	fsyl6eq_3 $f class C $.
	esyl6eq_0 $e |- ( ph -> A = B ) $.
	esyl6eq_1 $e |- B = C $.
	syl6eq $p |- ( ph -> A = C ) $= fsyl6eq_0 fsyl6eq_1 fsyl6eq_2 fsyl6eq_3 esyl6eq_0 fsyl6eq_2 fsyl6eq_3 wceq fsyl6eq_0 esyl6eq_1 a1i eqtrd $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) */

$)
${
	fsyl6req_0 $f wff ph $.
	fsyl6req_1 $f class A $.
	fsyl6req_2 $f class B $.
	fsyl6req_3 $f class C $.
	esyl6req_0 $e |- ( ph -> A = B ) $.
	esyl6req_1 $e |- B = C $.
	syl6req $p |- ( ph -> C = A ) $= fsyl6req_0 fsyl6req_1 fsyl6req_3 fsyl6req_0 fsyl6req_1 fsyl6req_2 fsyl6req_3 esyl6req_0 esyl6req_1 syl6eq eqcomd $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fsyl6eqr_0 $f wff ph $.
	fsyl6eqr_1 $f class A $.
	fsyl6eqr_2 $f class B $.
	fsyl6eqr_3 $f class C $.
	esyl6eqr_0 $e |- ( ph -> A = B ) $.
	esyl6eqr_1 $e |- C = B $.
	syl6eqr $p |- ( ph -> A = C ) $= fsyl6eqr_0 fsyl6eqr_1 fsyl6eqr_2 fsyl6eqr_3 esyl6eqr_0 fsyl6eqr_3 fsyl6eqr_2 esyl6eqr_1 eqcomi syl6eq $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) */

$)
${
	fsyl6reqr_0 $f wff ph $.
	fsyl6reqr_1 $f class A $.
	fsyl6reqr_2 $f class B $.
	fsyl6reqr_3 $f class C $.
	esyl6reqr_0 $e |- ( ph -> A = B ) $.
	esyl6reqr_1 $e |- C = B $.
	syl6reqr $p |- ( ph -> C = A ) $= fsyl6reqr_0 fsyl6reqr_1 fsyl6reqr_2 fsyl6reqr_3 esyl6reqr_0 fsyl6reqr_3 fsyl6reqr_2 esyl6reqr_1 eqcomi syl6req $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM, 8-May-1994.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) */

$)
${
	fsylan9eq_0 $f wff ph $.
	fsylan9eq_1 $f wff ps $.
	fsylan9eq_2 $f class A $.
	fsylan9eq_3 $f class B $.
	fsylan9eq_4 $f class C $.
	esylan9eq_0 $e |- ( ph -> A = B ) $.
	esylan9eq_1 $e |- ( ps -> B = C ) $.
	sylan9eq $p |- ( ( ph /\ ps ) -> A = C ) $= fsylan9eq_0 fsylan9eq_2 fsylan9eq_3 wceq fsylan9eq_3 fsylan9eq_4 wceq fsylan9eq_2 fsylan9eq_4 wceq fsylan9eq_1 esylan9eq_0 esylan9eq_1 fsylan9eq_2 fsylan9eq_3 fsylan9eq_4 eqtr syl2an $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM,
       23-Jun-2007.) */

$)
${
	fsylan9req_0 $f wff ph $.
	fsylan9req_1 $f wff ps $.
	fsylan9req_2 $f class A $.
	fsylan9req_3 $f class B $.
	fsylan9req_4 $f class C $.
	esylan9req_0 $e |- ( ph -> B = A ) $.
	esylan9req_1 $e |- ( ps -> B = C ) $.
	sylan9req $p |- ( ( ph /\ ps ) -> A = C ) $= fsylan9req_0 fsylan9req_1 fsylan9req_2 fsylan9req_3 fsylan9req_4 fsylan9req_0 fsylan9req_3 fsylan9req_2 esylan9req_0 eqcomd esylan9req_1 sylan9eq $.
$}
$( /* An equality transitivity deduction.  (Contributed by NM, 8-May-1994.) */

$)
${
	fsylan9eqr_0 $f wff ph $.
	fsylan9eqr_1 $f wff ps $.
	fsylan9eqr_2 $f class A $.
	fsylan9eqr_3 $f class B $.
	fsylan9eqr_4 $f class C $.
	esylan9eqr_0 $e |- ( ph -> A = B ) $.
	esylan9eqr_1 $e |- ( ps -> B = C ) $.
	sylan9eqr $p |- ( ( ps /\ ph ) -> A = C ) $= fsylan9eqr_0 fsylan9eqr_1 fsylan9eqr_2 fsylan9eqr_4 wceq fsylan9eqr_0 fsylan9eqr_1 fsylan9eqr_2 fsylan9eqr_3 fsylan9eqr_4 esylan9eqr_0 esylan9eqr_1 sylan9eq ancoms $.
$}
$( /* A chained equality inference, useful for converting from definitions.
       (Contributed by NM, 15-Nov-1994.) */

$)
${
	f3eqtr3g_0 $f wff ph $.
	f3eqtr3g_1 $f class A $.
	f3eqtr3g_2 $f class B $.
	f3eqtr3g_3 $f class C $.
	f3eqtr3g_4 $f class D $.
	e3eqtr3g_0 $e |- ( ph -> A = B ) $.
	e3eqtr3g_1 $e |- A = C $.
	e3eqtr3g_2 $e |- B = D $.
	3eqtr3g $p |- ( ph -> C = D ) $= f3eqtr3g_0 f3eqtr3g_3 f3eqtr3g_2 f3eqtr3g_4 f3eqtr3g_0 f3eqtr3g_3 f3eqtr3g_1 f3eqtr3g_2 e3eqtr3g_1 e3eqtr3g_0 syl5eqr e3eqtr3g_2 syl6eq $.
$}
$( /* A chained equality inference, useful for converting from definitions.
       (Contributed by Mario Carneiro, 6-Nov-2015.) */

$)
${
	f3eqtr3a_0 $f wff ph $.
	f3eqtr3a_1 $f class A $.
	f3eqtr3a_2 $f class B $.
	f3eqtr3a_3 $f class C $.
	f3eqtr3a_4 $f class D $.
	e3eqtr3a_0 $e |- A = B $.
	e3eqtr3a_1 $e |- ( ph -> A = C ) $.
	e3eqtr3a_2 $e |- ( ph -> B = D ) $.
	3eqtr3a $p |- ( ph -> C = D ) $= f3eqtr3a_0 f3eqtr3a_1 f3eqtr3a_3 f3eqtr3a_4 e3eqtr3a_1 f3eqtr3a_0 f3eqtr3a_1 f3eqtr3a_2 f3eqtr3a_4 e3eqtr3a_0 e3eqtr3a_2 syl5eq eqtr3d $.
$}
$( /* A chained equality inference, useful for converting to definitions.
       (Contributed by NM, 5-Aug-1993.) */

$)
${
	f3eqtr4g_0 $f wff ph $.
	f3eqtr4g_1 $f class A $.
	f3eqtr4g_2 $f class B $.
	f3eqtr4g_3 $f class C $.
	f3eqtr4g_4 $f class D $.
	e3eqtr4g_0 $e |- ( ph -> A = B ) $.
	e3eqtr4g_1 $e |- C = A $.
	e3eqtr4g_2 $e |- D = B $.
	3eqtr4g $p |- ( ph -> C = D ) $= f3eqtr4g_0 f3eqtr4g_3 f3eqtr4g_2 f3eqtr4g_4 f3eqtr4g_0 f3eqtr4g_3 f3eqtr4g_1 f3eqtr4g_2 e3eqtr4g_1 e3eqtr4g_0 syl5eq e3eqtr4g_2 syl6eqr $.
$}
$( /* A chained equality inference, useful for converting to definitions.
       (Contributed by NM, 2-Feb-2007.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) */

$)
${
	f3eqtr4a_0 $f wff ph $.
	f3eqtr4a_1 $f class A $.
	f3eqtr4a_2 $f class B $.
	f3eqtr4a_3 $f class C $.
	f3eqtr4a_4 $f class D $.
	e3eqtr4a_0 $e |- A = B $.
	e3eqtr4a_1 $e |- ( ph -> C = A ) $.
	e3eqtr4a_2 $e |- ( ph -> D = B ) $.
	3eqtr4a $p |- ( ph -> C = D ) $= f3eqtr4a_0 f3eqtr4a_3 f3eqtr4a_2 f3eqtr4a_4 f3eqtr4a_0 f3eqtr4a_3 f3eqtr4a_1 f3eqtr4a_2 e3eqtr4a_1 e3eqtr4a_0 syl6eq e3eqtr4a_2 eqtr4d $.
$}
$( /* A compound transitive inference for class equality.  (Contributed by NM,
       22-Jan-2004.) */

$)
$v F $.
$v G $.
${
	feq2tri_0 $f class A $.
	feq2tri_1 $f class B $.
	feq2tri_2 $f class C $.
	feq2tri_3 $f class D $.
	feq2tri_4 $f class F $.
	feq2tri_5 $f class G $.
	eeq2tri_0 $e |- ( A = C -> D = F ) $.
	eeq2tri_1 $e |- ( B = D -> C = G ) $.
	eq2tri $p |- ( ( A = C /\ B = F ) <-> ( B = D /\ A = G ) ) $= feq2tri_0 feq2tri_2 wceq feq2tri_1 feq2tri_3 wceq wa feq2tri_1 feq2tri_3 wceq feq2tri_0 feq2tri_2 wceq wa feq2tri_0 feq2tri_2 wceq feq2tri_1 feq2tri_4 wceq wa feq2tri_1 feq2tri_3 wceq feq2tri_0 feq2tri_5 wceq wa feq2tri_0 feq2tri_2 wceq feq2tri_1 feq2tri_3 wceq ancom feq2tri_0 feq2tri_2 wceq feq2tri_1 feq2tri_3 wceq feq2tri_1 feq2tri_4 wceq feq2tri_0 feq2tri_2 wceq feq2tri_3 feq2tri_4 feq2tri_1 eeq2tri_0 eqeq2d pm5.32i feq2tri_1 feq2tri_3 wceq feq2tri_0 feq2tri_2 wceq feq2tri_0 feq2tri_5 wceq feq2tri_1 feq2tri_3 wceq feq2tri_2 feq2tri_5 feq2tri_0 eeq2tri_1 eqeq2d pm5.32i 3bitr3i $.
$}
$( /* Equality implies equivalence of membership.  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ieleq1_0 $f set x $.
	feleq1_0 $f class A $.
	feleq1_1 $f class B $.
	feleq1_2 $f class C $.
	eleq1 $p |- ( A = B -> ( A e. C <-> B e. C ) ) $= feleq1_0 feleq1_1 wceq ieleq1_0 sup_set_class feleq1_0 wceq ieleq1_0 sup_set_class feleq1_2 wcel wa ieleq1_0 wex ieleq1_0 sup_set_class feleq1_1 wceq ieleq1_0 sup_set_class feleq1_2 wcel wa ieleq1_0 wex feleq1_0 feleq1_2 wcel feleq1_1 feleq1_2 wcel feleq1_0 feleq1_1 wceq ieleq1_0 sup_set_class feleq1_0 wceq ieleq1_0 sup_set_class feleq1_2 wcel wa ieleq1_0 sup_set_class feleq1_1 wceq ieleq1_0 sup_set_class feleq1_2 wcel wa ieleq1_0 feleq1_0 feleq1_1 wceq ieleq1_0 sup_set_class feleq1_0 wceq ieleq1_0 sup_set_class feleq1_1 wceq ieleq1_0 sup_set_class feleq1_2 wcel feleq1_0 feleq1_1 ieleq1_0 sup_set_class eqeq2 anbi1d exbidv ieleq1_0 feleq1_0 feleq1_2 df-clel ieleq1_0 feleq1_1 feleq1_2 df-clel 3bitr4g $.
$}
$( /* Equality implies equivalence of membership.  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ieleq2_0 $f set x $.
	feleq2_0 $f class A $.
	feleq2_1 $f class B $.
	feleq2_2 $f class C $.
	eleq2 $p |- ( A = B -> ( C e. A <-> C e. B ) ) $= feleq2_0 feleq2_1 wceq ieleq2_0 sup_set_class feleq2_2 wceq ieleq2_0 sup_set_class feleq2_0 wcel wa ieleq2_0 wex ieleq2_0 sup_set_class feleq2_2 wceq ieleq2_0 sup_set_class feleq2_1 wcel wa ieleq2_0 wex feleq2_2 feleq2_0 wcel feleq2_2 feleq2_1 wcel feleq2_0 feleq2_1 wceq ieleq2_0 sup_set_class feleq2_2 wceq ieleq2_0 sup_set_class feleq2_0 wcel wa ieleq2_0 sup_set_class feleq2_2 wceq ieleq2_0 sup_set_class feleq2_1 wcel wa ieleq2_0 feleq2_0 feleq2_1 wceq ieleq2_0 sup_set_class feleq2_0 wcel ieleq2_0 sup_set_class feleq2_1 wcel ieleq2_0 sup_set_class feleq2_2 wceq feleq2_0 feleq2_1 wceq ieleq2_0 sup_set_class feleq2_0 wcel ieleq2_0 sup_set_class feleq2_1 wcel wb ieleq2_0 feleq2_0 feleq2_1 wceq ieleq2_0 sup_set_class feleq2_0 wcel ieleq2_0 sup_set_class feleq2_1 wcel wb ieleq2_0 wal ieleq2_0 feleq2_0 feleq2_1 dfcleq biimpi 19.21bi anbi2d exbidv ieleq2_0 feleq2_2 feleq2_0 df-clel ieleq2_0 feleq2_2 feleq2_1 df-clel 3bitr4g $.
$}
$( /* Equality implies equivalence of membership.  (Contributed by NM,
     31-May-1999.) */

$)
${
	feleq12_0 $f class A $.
	feleq12_1 $f class B $.
	feleq12_2 $f class C $.
	feleq12_3 $f class D $.
	eleq12 $p |- ( ( A = B /\ C = D ) -> ( A e. C <-> B e. D ) ) $= feleq12_0 feleq12_1 wceq feleq12_0 feleq12_2 wcel feleq12_1 feleq12_2 wcel feleq12_2 feleq12_3 wceq feleq12_1 feleq12_3 wcel feleq12_0 feleq12_1 feleq12_2 eleq1 feleq12_2 feleq12_3 feleq12_1 eleq2 sylan9bb $.
$}
$( /* Inference from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feleq1i_0 $f class A $.
	feleq1i_1 $f class B $.
	feleq1i_2 $f class C $.
	eeleq1i_0 $e |- A = B $.
	eleq1i $p |- ( A e. C <-> B e. C ) $= feleq1i_0 feleq1i_1 wceq feleq1i_0 feleq1i_2 wcel feleq1i_1 feleq1i_2 wcel wb eeleq1i_0 feleq1i_0 feleq1i_1 feleq1i_2 eleq1 ax-mp $.
$}
$( /* Inference from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feleq2i_0 $f class A $.
	feleq2i_1 $f class B $.
	feleq2i_2 $f class C $.
	eeleq2i_0 $e |- A = B $.
	eleq2i $p |- ( C e. A <-> C e. B ) $= feleq2i_0 feleq2i_1 wceq feleq2i_2 feleq2i_0 wcel feleq2i_2 feleq2i_1 wcel wb eeleq2i_0 feleq2i_0 feleq2i_1 feleq2i_2 eleq2 ax-mp $.
$}
$( /* Inference from equality to equivalence of membership.  (Contributed by
         NM, 31-May-1994.) */

$)
${
	feleq12i_0 $f class A $.
	feleq12i_1 $f class B $.
	feleq12i_2 $f class C $.
	feleq12i_3 $f class D $.
	eeleq12i_0 $e |- A = B $.
	eeleq12i_1 $e |- C = D $.
	eleq12i $p |- ( A e. C <-> B e. D ) $= feleq12i_0 feleq12i_2 wcel feleq12i_0 feleq12i_3 wcel feleq12i_1 feleq12i_3 wcel feleq12i_2 feleq12i_3 feleq12i_0 eeleq12i_1 eleq2i feleq12i_0 feleq12i_1 feleq12i_3 eeleq12i_0 eleq1i bitri $.
$}
$( /* Theorem eleq12i is the congruence law for elementhood. */

$)
$( /* $j congruence 'eleq12i'; */

$)
$( /* Deduction from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feleq1d_0 $f wff ph $.
	feleq1d_1 $f class A $.
	feleq1d_2 $f class B $.
	feleq1d_3 $f class C $.
	eeleq1d_0 $e |- ( ph -> A = B ) $.
	eleq1d $p |- ( ph -> ( A e. C <-> B e. C ) ) $= feleq1d_0 feleq1d_1 feleq1d_2 wceq feleq1d_1 feleq1d_3 wcel feleq1d_2 feleq1d_3 wcel wb eeleq1d_0 feleq1d_1 feleq1d_2 feleq1d_3 eleq1 syl $.
$}
$( /* Deduction from equality to equivalence of membership.  (Contributed by
       NM, 27-Dec-1993.) */

$)
${
	feleq2d_0 $f wff ph $.
	feleq2d_1 $f class A $.
	feleq2d_2 $f class B $.
	feleq2d_3 $f class C $.
	eeleq2d_0 $e |- ( ph -> A = B ) $.
	eleq2d $p |- ( ph -> ( C e. A <-> C e. B ) ) $= feleq2d_0 feleq2d_1 feleq2d_2 wceq feleq2d_3 feleq2d_1 wcel feleq2d_3 feleq2d_2 wcel wb eeleq2d_0 feleq2d_1 feleq2d_2 feleq2d_3 eleq2 syl $.
$}
$( /* Deduction from equality to equivalence of membership.  (Contributed by
         NM, 31-May-1994.) */

$)
${
	feleq12d_0 $f wff ph $.
	feleq12d_1 $f class A $.
	feleq12d_2 $f class B $.
	feleq12d_3 $f class C $.
	feleq12d_4 $f class D $.
	eeleq12d_0 $e |- ( ph -> A = B ) $.
	eeleq12d_1 $e |- ( ph -> C = D ) $.
	eleq12d $p |- ( ph -> ( A e. C <-> B e. D ) ) $= feleq12d_0 feleq12d_1 feleq12d_3 wcel feleq12d_1 feleq12d_4 wcel feleq12d_2 feleq12d_4 wcel feleq12d_0 feleq12d_3 feleq12d_4 feleq12d_1 eeleq12d_1 eleq2d feleq12d_0 feleq12d_1 feleq12d_2 feleq12d_4 eeleq12d_0 eleq1d bitrd $.
$}
$( /* A transitive-type law relating membership and equality.  (Contributed by
     NM, 9-Apr-1994.) */

$)
${
	feleq1a_0 $f class A $.
	feleq1a_1 $f class B $.
	feleq1a_2 $f class C $.
	eleq1a $p |- ( A e. B -> ( C = A -> C e. B ) ) $= feleq1a_2 feleq1a_0 wceq feleq1a_2 feleq1a_1 wcel feleq1a_0 feleq1a_1 wcel feleq1a_2 feleq1a_0 feleq1a_1 eleq1 biimprcd $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feqeltri_0 $f class A $.
	feqeltri_1 $f class B $.
	feqeltri_2 $f class C $.
	eeqeltri_0 $e |- A = B $.
	eeqeltri_1 $e |- B e. C $.
	eqeltri $p |- A e. C $= feqeltri_0 feqeltri_2 wcel feqeltri_1 feqeltri_2 wcel eeqeltri_1 feqeltri_0 feqeltri_1 feqeltri_2 eeqeltri_0 eleq1i mpbir $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feqeltrri_0 $f class A $.
	feqeltrri_1 $f class B $.
	feqeltrri_2 $f class C $.
	eeqeltrri_0 $e |- A = B $.
	eeqeltrri_1 $e |- A e. C $.
	eqeltrri $p |- B e. C $= feqeltrri_1 feqeltrri_0 feqeltrri_2 feqeltrri_0 feqeltrri_1 eeqeltrri_0 eqcomi eeqeltrri_1 eqeltri $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feleqtri_0 $f class A $.
	feleqtri_1 $f class B $.
	feleqtri_2 $f class C $.
	eeleqtri_0 $e |- A e. B $.
	eeleqtri_1 $e |- B = C $.
	eleqtri $p |- A e. C $= feleqtri_0 feleqtri_1 wcel feleqtri_0 feleqtri_2 wcel eeleqtri_0 feleqtri_1 feleqtri_2 feleqtri_0 eeleqtri_1 eleq2i mpbi $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	feleqtrri_0 $f class A $.
	feleqtrri_1 $f class B $.
	feleqtrri_2 $f class C $.
	eeleqtrri_0 $e |- A e. B $.
	eeleqtrri_1 $e |- C = B $.
	eleqtrri $p |- A e. C $= feleqtrri_0 feleqtrri_1 feleqtrri_2 eeleqtrri_0 feleqtrri_2 feleqtrri_1 eeleqtrri_1 eqcomi eleqtri $.
$}
$( /* Substitution of equal classes into membership relation, deduction form.
       (Contributed by Raph Levien, 10-Dec-2002.) */

$)
${
	feqeltrd_0 $f wff ph $.
	feqeltrd_1 $f class A $.
	feqeltrd_2 $f class B $.
	feqeltrd_3 $f class C $.
	eeqeltrd_0 $e |- ( ph -> A = B ) $.
	eeqeltrd_1 $e |- ( ph -> B e. C ) $.
	eqeltrd $p |- ( ph -> A e. C ) $= feqeltrd_0 feqeltrd_1 feqeltrd_3 wcel feqeltrd_2 feqeltrd_3 wcel eeqeltrd_1 feqeltrd_0 feqeltrd_1 feqeltrd_2 feqeltrd_3 eeqeltrd_0 eleq1d mpbird $.
$}
$( /* Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) */

$)
${
	feqeltrrd_0 $f wff ph $.
	feqeltrrd_1 $f class A $.
	feqeltrrd_2 $f class B $.
	feqeltrrd_3 $f class C $.
	eeqeltrrd_0 $e |- ( ph -> A = B ) $.
	eeqeltrrd_1 $e |- ( ph -> A e. C ) $.
	eqeltrrd $p |- ( ph -> B e. C ) $= feqeltrrd_0 feqeltrrd_2 feqeltrrd_1 feqeltrrd_3 feqeltrrd_0 feqeltrrd_1 feqeltrrd_2 eeqeltrrd_0 eqcomd eeqeltrrd_1 eqeltrd $.
$}
$( /* Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) */

$)
${
	feleqtrd_0 $f wff ph $.
	feleqtrd_1 $f class A $.
	feleqtrd_2 $f class B $.
	feleqtrd_3 $f class C $.
	eeleqtrd_0 $e |- ( ph -> A e. B ) $.
	eeleqtrd_1 $e |- ( ph -> B = C ) $.
	eleqtrd $p |- ( ph -> A e. C ) $= feleqtrd_0 feleqtrd_1 feleqtrd_2 wcel feleqtrd_1 feleqtrd_3 wcel eeleqtrd_0 feleqtrd_0 feleqtrd_2 feleqtrd_3 feleqtrd_1 eeleqtrd_1 eleq2d mpbid $.
$}
$( /* Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) */

$)
${
	feleqtrrd_0 $f wff ph $.
	feleqtrrd_1 $f class A $.
	feleqtrrd_2 $f class B $.
	feleqtrrd_3 $f class C $.
	eeleqtrrd_0 $e |- ( ph -> A e. B ) $.
	eeleqtrrd_1 $e |- ( ph -> C = B ) $.
	eleqtrrd $p |- ( ph -> A e. C ) $= feleqtrrd_0 feleqtrrd_1 feleqtrrd_2 feleqtrrd_3 eeleqtrrd_0 feleqtrrd_0 feleqtrrd_3 feleqtrrd_2 eeleqtrrd_1 eqcomd eleqtrd $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) */

$)
${
	f3eltr3i_0 $f class A $.
	f3eltr3i_1 $f class B $.
	f3eltr3i_2 $f class C $.
	f3eltr3i_3 $f class D $.
	e3eltr3i_0 $e |- A e. B $.
	e3eltr3i_1 $e |- A = C $.
	e3eltr3i_2 $e |- B = D $.
	3eltr3i $p |- C e. D $= f3eltr3i_0 f3eltr3i_2 f3eltr3i_3 e3eltr3i_1 f3eltr3i_0 f3eltr3i_1 f3eltr3i_3 e3eltr3i_0 e3eltr3i_2 eleqtri eqeltrri $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) */

$)
${
	f3eltr4i_0 $f class A $.
	f3eltr4i_1 $f class B $.
	f3eltr4i_2 $f class C $.
	f3eltr4i_3 $f class D $.
	e3eltr4i_0 $e |- A e. B $.
	e3eltr4i_1 $e |- C = A $.
	e3eltr4i_2 $e |- D = B $.
	3eltr4i $p |- C e. D $= f3eltr4i_2 f3eltr4i_0 f3eltr4i_3 e3eltr4i_1 f3eltr4i_0 f3eltr4i_1 f3eltr4i_3 e3eltr4i_0 e3eltr4i_2 eleqtrri eqeltri $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) */

$)
${
	f3eltr3d_0 $f wff ph $.
	f3eltr3d_1 $f class A $.
	f3eltr3d_2 $f class B $.
	f3eltr3d_3 $f class C $.
	f3eltr3d_4 $f class D $.
	e3eltr3d_0 $e |- ( ph -> A e. B ) $.
	e3eltr3d_1 $e |- ( ph -> A = C ) $.
	e3eltr3d_2 $e |- ( ph -> B = D ) $.
	3eltr3d $p |- ( ph -> C e. D ) $= f3eltr3d_0 f3eltr3d_1 f3eltr3d_3 f3eltr3d_4 e3eltr3d_1 f3eltr3d_0 f3eltr3d_1 f3eltr3d_2 f3eltr3d_4 e3eltr3d_0 e3eltr3d_2 eleqtrd eqeltrrd $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) */

$)
${
	f3eltr4d_0 $f wff ph $.
	f3eltr4d_1 $f class A $.
	f3eltr4d_2 $f class B $.
	f3eltr4d_3 $f class C $.
	f3eltr4d_4 $f class D $.
	e3eltr4d_0 $e |- ( ph -> A e. B ) $.
	e3eltr4d_1 $e |- ( ph -> C = A ) $.
	e3eltr4d_2 $e |- ( ph -> D = B ) $.
	3eltr4d $p |- ( ph -> C e. D ) $= f3eltr4d_0 f3eltr4d_3 f3eltr4d_1 f3eltr4d_4 e3eltr4d_1 f3eltr4d_0 f3eltr4d_1 f3eltr4d_2 f3eltr4d_4 e3eltr4d_0 e3eltr4d_2 eleqtrrd eqeltrd $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) */

$)
${
	f3eltr3g_0 $f wff ph $.
	f3eltr3g_1 $f class A $.
	f3eltr3g_2 $f class B $.
	f3eltr3g_3 $f class C $.
	f3eltr3g_4 $f class D $.
	e3eltr3g_0 $e |- ( ph -> A e. B ) $.
	e3eltr3g_1 $e |- A = C $.
	e3eltr3g_2 $e |- B = D $.
	3eltr3g $p |- ( ph -> C e. D ) $= f3eltr3g_0 f3eltr3g_1 f3eltr3g_2 wcel f3eltr3g_3 f3eltr3g_4 wcel e3eltr3g_0 f3eltr3g_1 f3eltr3g_3 f3eltr3g_2 f3eltr3g_4 e3eltr3g_1 e3eltr3g_2 eleq12i sylib $.
$}
$( /* Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) */

$)
${
	f3eltr4g_0 $f wff ph $.
	f3eltr4g_1 $f class A $.
	f3eltr4g_2 $f class B $.
	f3eltr4g_3 $f class C $.
	f3eltr4g_4 $f class D $.
	e3eltr4g_0 $e |- ( ph -> A e. B ) $.
	e3eltr4g_1 $e |- C = A $.
	e3eltr4g_2 $e |- D = B $.
	3eltr4g $p |- ( ph -> C e. D ) $= f3eltr4g_0 f3eltr4g_1 f3eltr4g_2 wcel f3eltr4g_3 f3eltr4g_4 wcel e3eltr4g_0 f3eltr4g_3 f3eltr4g_1 f3eltr4g_4 f3eltr4g_2 e3eltr4g_1 e3eltr4g_2 eleq12i sylibr $.
$}
$( /* B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) */

$)
${
	fsyl5eqel_0 $f wff ph $.
	fsyl5eqel_1 $f class A $.
	fsyl5eqel_2 $f class B $.
	fsyl5eqel_3 $f class C $.
	esyl5eqel_0 $e |- A = B $.
	esyl5eqel_1 $e |- ( ph -> B e. C ) $.
	syl5eqel $p |- ( ph -> A e. C ) $= fsyl5eqel_0 fsyl5eqel_1 fsyl5eqel_2 fsyl5eqel_3 fsyl5eqel_1 fsyl5eqel_2 wceq fsyl5eqel_0 esyl5eqel_0 a1i esyl5eqel_1 eqeltrd $.
$}
$( /* B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) */

$)
${
	fsyl5eqelr_0 $f wff ph $.
	fsyl5eqelr_1 $f class A $.
	fsyl5eqelr_2 $f class B $.
	fsyl5eqelr_3 $f class C $.
	esyl5eqelr_0 $e |- B = A $.
	esyl5eqelr_1 $e |- ( ph -> B e. C ) $.
	syl5eqelr $p |- ( ph -> A e. C ) $= fsyl5eqelr_0 fsyl5eqelr_1 fsyl5eqelr_2 fsyl5eqelr_3 fsyl5eqelr_2 fsyl5eqelr_1 esyl5eqelr_0 eqcomi esyl5eqelr_1 syl5eqel $.
$}
$( /* B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) */

$)
${
	fsyl5eleq_0 $f wff ph $.
	fsyl5eleq_1 $f class A $.
	fsyl5eleq_2 $f class B $.
	fsyl5eleq_3 $f class C $.
	esyl5eleq_0 $e |- A e. B $.
	esyl5eleq_1 $e |- ( ph -> B = C ) $.
	syl5eleq $p |- ( ph -> A e. C ) $= fsyl5eleq_0 fsyl5eleq_1 fsyl5eleq_2 fsyl5eleq_3 fsyl5eleq_1 fsyl5eleq_2 wcel fsyl5eleq_0 esyl5eleq_0 a1i esyl5eleq_1 eleqtrd $.
$}
$( /* B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) */

$)
${
	fsyl5eleqr_0 $f wff ph $.
	fsyl5eleqr_1 $f class A $.
	fsyl5eleqr_2 $f class B $.
	fsyl5eleqr_3 $f class C $.
	esyl5eleqr_0 $e |- A e. B $.
	esyl5eleqr_1 $e |- ( ph -> C = B ) $.
	syl5eleqr $p |- ( ph -> A e. C ) $= fsyl5eleqr_0 fsyl5eleqr_1 fsyl5eleqr_2 fsyl5eleqr_3 esyl5eleqr_0 fsyl5eleqr_0 fsyl5eleqr_3 fsyl5eleqr_2 esyl5eleqr_1 eqcomd syl5eleq $.
$}
$( /* A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) */

$)
${
	fsyl6eqel_0 $f wff ph $.
	fsyl6eqel_1 $f class A $.
	fsyl6eqel_2 $f class B $.
	fsyl6eqel_3 $f class C $.
	esyl6eqel_0 $e |- ( ph -> A = B ) $.
	esyl6eqel_1 $e |- B e. C $.
	syl6eqel $p |- ( ph -> A e. C ) $= fsyl6eqel_0 fsyl6eqel_1 fsyl6eqel_2 fsyl6eqel_3 esyl6eqel_0 fsyl6eqel_2 fsyl6eqel_3 wcel fsyl6eqel_0 esyl6eqel_1 a1i eqeltrd $.
$}
$( /* A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) */

$)
${
	fsyl6eqelr_0 $f wff ph $.
	fsyl6eqelr_1 $f class A $.
	fsyl6eqelr_2 $f class B $.
	fsyl6eqelr_3 $f class C $.
	esyl6eqelr_0 $e |- ( ph -> B = A ) $.
	esyl6eqelr_1 $e |- B e. C $.
	syl6eqelr $p |- ( ph -> A e. C ) $= fsyl6eqelr_0 fsyl6eqelr_1 fsyl6eqelr_2 fsyl6eqelr_3 fsyl6eqelr_0 fsyl6eqelr_2 fsyl6eqelr_1 esyl6eqelr_0 eqcomd esyl6eqelr_1 syl6eqel $.
$}
$( /* A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) */

$)
${
	fsyl6eleq_0 $f wff ph $.
	fsyl6eleq_1 $f class A $.
	fsyl6eleq_2 $f class B $.
	fsyl6eleq_3 $f class C $.
	esyl6eleq_0 $e |- ( ph -> A e. B ) $.
	esyl6eleq_1 $e |- B = C $.
	syl6eleq $p |- ( ph -> A e. C ) $= fsyl6eleq_0 fsyl6eleq_1 fsyl6eleq_2 fsyl6eleq_3 esyl6eleq_0 fsyl6eleq_2 fsyl6eleq_3 wceq fsyl6eleq_0 esyl6eleq_1 a1i eleqtrd $.
$}
$( /* A membership and equality inference.  (Contributed by NM,
       24-Apr-2005.) */

$)
${
	fsyl6eleqr_0 $f wff ph $.
	fsyl6eleqr_1 $f class A $.
	fsyl6eleqr_2 $f class B $.
	fsyl6eleqr_3 $f class C $.
	esyl6eleqr_0 $e |- ( ph -> A e. B ) $.
	esyl6eleqr_1 $e |- C = B $.
	syl6eleqr $p |- ( ph -> A e. C ) $= fsyl6eleqr_0 fsyl6eleqr_1 fsyl6eleqr_2 fsyl6eleqr_3 esyl6eleqr_0 fsyl6eleqr_3 fsyl6eleqr_2 esyl6eleqr_1 eqcomi syl6eleq $.
$}
$( /* Substitution of equal classes into a membership antecedent.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) */

$)
${
	feleq2s_0 $f wff ph $.
	feleq2s_1 $f class A $.
	feleq2s_2 $f class B $.
	feleq2s_3 $f class C $.
	eeleq2s_0 $e |- ( A e. B -> ph ) $.
	eeleq2s_1 $e |- C = B $.
	eleq2s $p |- ( A e. C -> ph ) $= feleq2s_1 feleq2s_3 wcel feleq2s_1 feleq2s_2 wcel feleq2s_0 feleq2s_3 feleq2s_2 feleq2s_1 eeleq2s_1 eleq2i eeleq2s_0 sylbi $.
$}
$( /* If a class is not an element of another class, an equal class is also
       not an element.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) */

$)
${
	feqneltrd_0 $f wff ph $.
	feqneltrd_1 $f class A $.
	feqneltrd_2 $f class B $.
	feqneltrd_3 $f class C $.
	eeqneltrd_0 $e |- ( ph -> A = B ) $.
	eeqneltrd_1 $e |- ( ph -> -. B e. C ) $.
	eqneltrd $p |- ( ph -> -. A e. C ) $= feqneltrd_0 feqneltrd_1 feqneltrd_3 wcel feqneltrd_2 feqneltrd_3 wcel eeqneltrd_1 feqneltrd_0 feqneltrd_1 feqneltrd_2 feqneltrd_3 eeqneltrd_0 eleq1d mtbird $.
$}
$( /* If a class is not an element of another class, an equal class is also
       not an element.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) */

$)
${
	feqneltrrd_0 $f wff ph $.
	feqneltrrd_1 $f class A $.
	feqneltrrd_2 $f class B $.
	feqneltrrd_3 $f class C $.
	eeqneltrrd_0 $e |- ( ph -> A = B ) $.
	eeqneltrrd_1 $e |- ( ph -> -. A e. C ) $.
	eqneltrrd $p |- ( ph -> -. B e. C ) $= feqneltrrd_0 feqneltrrd_1 feqneltrrd_3 wcel feqneltrrd_2 feqneltrrd_3 wcel eeqneltrrd_1 feqneltrrd_0 feqneltrrd_1 feqneltrrd_2 feqneltrrd_3 eeqneltrrd_0 eleq1d mtbid $.
$}
$( /* If a class is not an element of another class, it is also not an element
       of an equal class.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) */

$)
${
	fneleqtrd_0 $f wff ph $.
	fneleqtrd_1 $f class A $.
	fneleqtrd_2 $f class B $.
	fneleqtrd_3 $f class C $.
	eneleqtrd_0 $e |- ( ph -> -. C e. A ) $.
	eneleqtrd_1 $e |- ( ph -> A = B ) $.
	neleqtrd $p |- ( ph -> -. C e. B ) $= fneleqtrd_0 fneleqtrd_3 fneleqtrd_1 wcel fneleqtrd_3 fneleqtrd_2 wcel eneleqtrd_0 fneleqtrd_0 fneleqtrd_1 fneleqtrd_2 fneleqtrd_3 eneleqtrd_1 eleq2d mtbid $.
$}
$( /* If a class is not an element of another class, it is also not an element
       of an equal class.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) */

$)
${
	fneleqtrrd_0 $f wff ph $.
	fneleqtrrd_1 $f class A $.
	fneleqtrrd_2 $f class B $.
	fneleqtrrd_3 $f class C $.
	eneleqtrrd_0 $e |- ( ph -> -. C e. B ) $.
	eneleqtrrd_1 $e |- ( ph -> A = B ) $.
	neleqtrrd $p |- ( ph -> -. C e. A ) $= fneleqtrrd_0 fneleqtrrd_3 fneleqtrrd_1 wcel fneleqtrrd_3 fneleqtrrd_2 wcel eneleqtrrd_0 fneleqtrrd_0 fneleqtrrd_1 fneleqtrrd_2 fneleqtrrd_3 eneleqtrrd_1 eleq2d mtbird $.
$}
$( /* Establish equality between classes, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	$d y A $.
	$d y B $.
	$d x y $.
	fcleqh_0 $f set x $.
	fcleqh_1 $f set y $.
	fcleqh_2 $f class A $.
	fcleqh_3 $f class B $.
	ecleqh_0 $e |- ( y e. A -> A. x y e. A ) $.
	ecleqh_1 $e |- ( y e. B -> A. x y e. B ) $.
	cleqh $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $= fcleqh_2 fcleqh_3 wceq fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb fcleqh_1 wal fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_0 wal fcleqh_1 fcleqh_2 fcleqh_3 dfcleq fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_0 wal fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb fcleqh_1 wal fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb fcleqh_0 fcleqh_1 fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_1 ax-17 fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wi fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_1 sup_set_class fcleqh_2 wcel wi wa fcleqh_0 fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel dfbi2 fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wi fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_1 sup_set_class fcleqh_2 wcel wi fcleqh_0 fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_0 ecleqh_0 ecleqh_1 hbim fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_0 ecleqh_1 ecleqh_0 hbim hban hbxfrbi fcleqh_0 sup_set_class fcleqh_1 sup_set_class wceq fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb fcleqh_0 sup_set_class fcleqh_1 sup_set_class wceq fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_0 sup_set_class fcleqh_1 sup_set_class fcleqh_2 eleq1 fcleqh_0 sup_set_class fcleqh_1 sup_set_class fcleqh_3 eleq1 bibi12d biimpd cbv3h fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_1 fcleqh_0 fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wi fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_1 sup_set_class fcleqh_2 wcel wi wa fcleqh_0 fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel dfbi2 fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wi fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_1 sup_set_class fcleqh_2 wcel wi fcleqh_0 fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_0 ecleqh_0 ecleqh_1 hbim fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_0 ecleqh_1 ecleqh_0 hbim hban hbxfrbi fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_1 ax-17 fcleqh_1 sup_set_class fcleqh_0 sup_set_class wceq fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel wb fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_3 wcel wb wb fcleqh_0 fcleqh_1 fcleqh_0 sup_set_class fcleqh_1 sup_set_class wceq fcleqh_0 sup_set_class fcleqh_2 wcel fcleqh_1 sup_set_class fcleqh_2 wcel fcleqh_0 sup_set_class fcleqh_3 wcel fcleqh_1 sup_set_class fcleqh_3 wcel fcleqh_0 sup_set_class fcleqh_1 sup_set_class fcleqh_2 eleq1 fcleqh_0 sup_set_class fcleqh_1 sup_set_class fcleqh_3 eleq1 bibi12d equcoms biimprd cbv3h impbii bitr4i $.
$}
$( /* A way of showing two classes are not equal.  (Contributed by NM,
     1-Apr-1997.) */

$)
${
	fnelneq_0 $f class A $.
	fnelneq_1 $f class B $.
	fnelneq_2 $f class C $.
	nelneq $p |- ( ( A e. C /\ -. B e. C ) -> -. A = B ) $= fnelneq_0 fnelneq_2 wcel fnelneq_0 fnelneq_1 wceq fnelneq_1 fnelneq_2 wcel fnelneq_0 fnelneq_1 wceq fnelneq_0 fnelneq_2 wcel fnelneq_1 fnelneq_2 wcel fnelneq_0 fnelneq_1 fnelneq_2 eleq1 biimpcd con3and $.
$}
$( /* A way of showing two classes are not equal.  (Contributed by NM,
     12-Jan-2002.) */

$)
${
	fnelneq2_0 $f class A $.
	fnelneq2_1 $f class B $.
	fnelneq2_2 $f class C $.
	nelneq2 $p |- ( ( A e. B /\ -. A e. C ) -> -. B = C ) $= fnelneq2_0 fnelneq2_1 wcel fnelneq2_1 fnelneq2_2 wceq fnelneq2_0 fnelneq2_2 wcel fnelneq2_1 fnelneq2_2 wceq fnelneq2_0 fnelneq2_1 wcel fnelneq2_0 fnelneq2_2 wcel fnelneq2_1 fnelneq2_2 fnelneq2_0 eleq2 biimpcd con3and $.
$}
$( /* Lemma for ~ eqsb3 .  (Contributed by Rodolfo Medina, 28-Apr-2010.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) */

$)
${
	$d x y $.
	$d y A $.
	feqsb3lem_0 $f set x $.
	feqsb3lem_1 $f set y $.
	feqsb3lem_2 $f class A $.
	eqsb3lem $p |- ( [ x / y ] y = A <-> x = A ) $= feqsb3lem_1 sup_set_class feqsb3lem_2 wceq feqsb3lem_0 sup_set_class feqsb3lem_2 wceq feqsb3lem_1 feqsb3lem_0 feqsb3lem_0 sup_set_class feqsb3lem_2 wceq feqsb3lem_1 nfv feqsb3lem_1 sup_set_class feqsb3lem_0 sup_set_class feqsb3lem_2 eqeq1 sbie $.
$}
$( /* Substitution applied to an atomic wff (class version of ~ equsb3 ).
       (Contributed by Rodolfo Medina, 28-Apr-2010.) */

$)
${
	$d y A $.
	$d w y $.
	$d w A $.
	$d x w $.
	ieqsb3_0 $f set w $.
	feqsb3_0 $f set x $.
	feqsb3_1 $f set y $.
	feqsb3_2 $f class A $.
	eqsb3 $p |- ( [ x / y ] y = A <-> x = A ) $= feqsb3_1 sup_set_class feqsb3_2 wceq feqsb3_1 ieqsb3_0 wsb ieqsb3_0 feqsb3_0 wsb ieqsb3_0 sup_set_class feqsb3_2 wceq ieqsb3_0 feqsb3_0 wsb feqsb3_1 sup_set_class feqsb3_2 wceq feqsb3_1 feqsb3_0 wsb feqsb3_0 sup_set_class feqsb3_2 wceq feqsb3_1 sup_set_class feqsb3_2 wceq feqsb3_1 ieqsb3_0 wsb ieqsb3_0 sup_set_class feqsb3_2 wceq ieqsb3_0 feqsb3_0 ieqsb3_0 feqsb3_1 feqsb3_2 eqsb3lem sbbii feqsb3_1 sup_set_class feqsb3_2 wceq feqsb3_1 feqsb3_0 ieqsb3_0 feqsb3_1 sup_set_class feqsb3_2 wceq ieqsb3_0 nfv sbco2 feqsb3_0 ieqsb3_0 feqsb3_2 eqsb3lem 3bitr3i $.
$}
$( /* Substitution applied to an atomic wff (class version of ~ elsb3 ).
       (Contributed by Rodolfo Medina, 28-Apr-2010.)  (Proof shortened by
       Andrew Salmon, 14-Jun-2011.) */

$)
${
	$d y A $.
	$d w y $.
	$d w A $.
	$d w x $.
	iclelsb3_0 $f set w $.
	fclelsb3_0 $f set x $.
	fclelsb3_1 $f set y $.
	fclelsb3_2 $f class A $.
	clelsb3 $p |- ( [ x / y ] y e. A <-> x e. A ) $= iclelsb3_0 sup_set_class fclelsb3_2 wcel iclelsb3_0 fclelsb3_1 wsb fclelsb3_1 fclelsb3_0 wsb iclelsb3_0 sup_set_class fclelsb3_2 wcel iclelsb3_0 fclelsb3_0 wsb fclelsb3_1 sup_set_class fclelsb3_2 wcel fclelsb3_1 fclelsb3_0 wsb fclelsb3_0 sup_set_class fclelsb3_2 wcel iclelsb3_0 sup_set_class fclelsb3_2 wcel iclelsb3_0 fclelsb3_0 fclelsb3_1 iclelsb3_0 sup_set_class fclelsb3_2 wcel fclelsb3_1 nfv sbco2 iclelsb3_0 sup_set_class fclelsb3_2 wcel iclelsb3_0 fclelsb3_1 wsb fclelsb3_1 sup_set_class fclelsb3_2 wcel fclelsb3_1 fclelsb3_0 iclelsb3_0 sup_set_class fclelsb3_2 wcel fclelsb3_1 sup_set_class fclelsb3_2 wcel iclelsb3_0 fclelsb3_1 fclelsb3_1 sup_set_class fclelsb3_2 wcel iclelsb3_0 nfv iclelsb3_0 sup_set_class fclelsb3_1 sup_set_class fclelsb3_2 eleq1 sbie sbbii iclelsb3_0 sup_set_class fclelsb3_2 wcel fclelsb3_0 sup_set_class fclelsb3_2 wcel iclelsb3_0 fclelsb3_0 fclelsb3_0 sup_set_class fclelsb3_2 wcel iclelsb3_0 nfv iclelsb3_0 sup_set_class fclelsb3_0 sup_set_class fclelsb3_2 eleq1 sbie 3bitr3i $.
$}
$( /* A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfrbi for equivalence version.  (Contributed by NM,
       21-Aug-2007.) */

$)
${
	fhbxfreq_0 $f set x $.
	fhbxfreq_1 $f set y $.
	fhbxfreq_2 $f class A $.
	fhbxfreq_3 $f class B $.
	ehbxfreq_0 $e |- A = B $.
	ehbxfreq_1 $e |- ( y e. B -> A. x y e. B ) $.
	hbxfreq $p |- ( y e. A -> A. x y e. A ) $= fhbxfreq_1 sup_set_class fhbxfreq_2 wcel fhbxfreq_1 sup_set_class fhbxfreq_3 wcel fhbxfreq_0 fhbxfreq_2 fhbxfreq_3 fhbxfreq_1 sup_set_class ehbxfreq_0 eleq2i ehbxfreq_1 hbxfrbi $.
$}
$( /* Change the free variable of a hypothesis builder.  Lemma for ~ nfcrii .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Andrew Salmon,
       11-Jul-2011.) */

$)
${
	$d y A $.
	$d x z $.
	fhblem_0 $f set x $.
	fhblem_1 $f set y $.
	fhblem_2 $f set z $.
	fhblem_3 $f class A $.
	ehblem_0 $e |- ( y e. A -> A. x y e. A ) $.
	hblem $p |- ( z e. A -> A. x z e. A ) $= fhblem_1 sup_set_class fhblem_3 wcel fhblem_1 fhblem_2 wsb fhblem_1 sup_set_class fhblem_3 wcel fhblem_1 fhblem_2 wsb fhblem_0 wal fhblem_2 sup_set_class fhblem_3 wcel fhblem_2 sup_set_class fhblem_3 wcel fhblem_0 wal fhblem_1 sup_set_class fhblem_3 wcel fhblem_1 fhblem_2 fhblem_0 ehblem_0 hbsb fhblem_2 fhblem_1 fhblem_3 clelsb3 fhblem_1 sup_set_class fhblem_3 wcel fhblem_1 fhblem_2 wsb fhblem_2 sup_set_class fhblem_3 wcel fhblem_0 fhblem_2 fhblem_1 fhblem_3 clelsb3 albii 3imtr3i $.
$}
$( /* Equality of a class variable and a class abstraction (also called a
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
       NM, 5-Aug-1993.) */

$)
${
	$d x A y $.
	$d ph y $.
	iabeq2_0 $f set y $.
	fabeq2_0 $f wff ph $.
	fabeq2_1 $f set x $.
	fabeq2_2 $f class A $.
	abeq2 $p |- ( A = { x | ph } <-> A. x ( x e. A <-> ph ) ) $= fabeq2_2 fabeq2_0 fabeq2_1 cab wceq fabeq2_1 sup_set_class fabeq2_2 wcel fabeq2_1 sup_set_class fabeq2_0 fabeq2_1 cab wcel wb fabeq2_1 wal fabeq2_1 sup_set_class fabeq2_2 wcel fabeq2_0 wb fabeq2_1 wal fabeq2_1 iabeq2_0 fabeq2_2 fabeq2_0 fabeq2_1 cab iabeq2_0 sup_set_class fabeq2_2 wcel fabeq2_1 ax-17 fabeq2_0 fabeq2_1 iabeq2_0 hbab1 cleqh fabeq2_1 sup_set_class fabeq2_2 wcel fabeq2_1 sup_set_class fabeq2_0 fabeq2_1 cab wcel wb fabeq2_1 sup_set_class fabeq2_2 wcel fabeq2_0 wb fabeq2_1 fabeq2_1 sup_set_class fabeq2_0 fabeq2_1 cab wcel fabeq2_0 fabeq2_1 sup_set_class fabeq2_2 wcel fabeq2_0 fabeq2_1 abid bibi2i albii bitri $.
$}
$( /* Equality of a class variable and a class abstraction.  (Contributed by
       NM, 20-Aug-1993.) */

$)
${
	$d x A $.
	fabeq1_0 $f wff ph $.
	fabeq1_1 $f set x $.
	fabeq1_2 $f class A $.
	abeq1 $p |- ( { x | ph } = A <-> A. x ( ph <-> x e. A ) ) $= fabeq1_2 fabeq1_0 fabeq1_1 cab wceq fabeq1_1 sup_set_class fabeq1_2 wcel fabeq1_0 wb fabeq1_1 wal fabeq1_0 fabeq1_1 cab fabeq1_2 wceq fabeq1_0 fabeq1_1 sup_set_class fabeq1_2 wcel wb fabeq1_1 wal fabeq1_0 fabeq1_1 fabeq1_2 abeq2 fabeq1_0 fabeq1_1 cab fabeq1_2 eqcom fabeq1_0 fabeq1_1 sup_set_class fabeq1_2 wcel wb fabeq1_1 sup_set_class fabeq1_2 wcel fabeq1_0 wb fabeq1_1 fabeq1_0 fabeq1_1 sup_set_class fabeq1_2 wcel bicom albii 3bitr4i $.
$}
$( /* Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 3-Apr-1996.) */

$)
${
	fabeq2i_0 $f wff ph $.
	fabeq2i_1 $f set x $.
	fabeq2i_2 $f class A $.
	eabeq2i_0 $e |- A = { x | ph } $.
	abeq2i $p |- ( x e. A <-> ph ) $= fabeq2i_1 sup_set_class fabeq2i_2 wcel fabeq2i_1 sup_set_class fabeq2i_0 fabeq2i_1 cab wcel fabeq2i_0 fabeq2i_2 fabeq2i_0 fabeq2i_1 cab fabeq2i_1 sup_set_class eabeq2i_0 eleq2i fabeq2i_0 fabeq2i_1 abid bitri $.
$}
$( /* Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 31-Jul-1994.) */

$)
${
	fabeq1i_0 $f wff ph $.
	fabeq1i_1 $f set x $.
	fabeq1i_2 $f class A $.
	eabeq1i_0 $e |- { x | ph } = A $.
	abeq1i $p |- ( ph <-> x e. A ) $= fabeq1i_0 fabeq1i_1 sup_set_class fabeq1i_0 fabeq1i_1 cab wcel fabeq1i_1 sup_set_class fabeq1i_2 wcel fabeq1i_0 fabeq1i_1 abid fabeq1i_0 fabeq1i_1 cab fabeq1i_2 fabeq1i_1 sup_set_class eabeq1i_0 eleq2i bitr3i $.
$}
$( /* Equality of a class variable and a class abstraction (deduction).
       (Contributed by NM, 16-Nov-1995.) */

$)
${
	fabeq2d_0 $f wff ph $.
	fabeq2d_1 $f wff ps $.
	fabeq2d_2 $f set x $.
	fabeq2d_3 $f class A $.
	eabeq2d_0 $e |- ( ph -> A = { x | ps } ) $.
	abeq2d $p |- ( ph -> ( x e. A <-> ps ) ) $= fabeq2d_0 fabeq2d_2 sup_set_class fabeq2d_3 wcel fabeq2d_2 sup_set_class fabeq2d_1 fabeq2d_2 cab wcel fabeq2d_1 fabeq2d_0 fabeq2d_3 fabeq2d_1 fabeq2d_2 cab fabeq2d_2 sup_set_class eabeq2d_0 eleq2d fabeq2d_1 fabeq2d_2 abid syl6bb $.
$}
$( /* Equivalent wff's correspond to equal class abstractions.  (Contributed
       by NM, 25-Nov-2013.)  (Revised by Mario Carneiro, 11-Aug-2016.) */

$)
${
	$d ph y $.
	$d ps y $.
	$d x y $.
	iabbi_0 $f set y $.
	fabbi_0 $f wff ph $.
	fabbi_1 $f wff ps $.
	fabbi_2 $f set x $.
	abbi $p |- ( A. x ( ph <-> ps ) <-> { x | ph } = { x | ps } ) $= fabbi_0 fabbi_2 cab fabbi_1 fabbi_2 cab wceq iabbi_0 sup_set_class fabbi_0 fabbi_2 cab wcel iabbi_0 sup_set_class fabbi_1 fabbi_2 cab wcel wb iabbi_0 wal fabbi_0 fabbi_1 wb fabbi_2 wal iabbi_0 fabbi_0 fabbi_2 cab fabbi_1 fabbi_2 cab dfcleq iabbi_0 sup_set_class fabbi_0 fabbi_2 cab wcel iabbi_0 sup_set_class fabbi_1 fabbi_2 cab wcel wb fabbi_0 fabbi_1 wb iabbi_0 fabbi_2 iabbi_0 sup_set_class fabbi_0 fabbi_2 cab wcel iabbi_0 sup_set_class fabbi_1 fabbi_2 cab wcel fabbi_2 fabbi_0 fabbi_2 iabbi_0 nfsab1 fabbi_1 fabbi_2 iabbi_0 nfsab1 nfbi fabbi_0 fabbi_1 wb iabbi_0 nfv iabbi_0 sup_set_class fabbi_2 sup_set_class wceq iabbi_0 sup_set_class fabbi_0 fabbi_2 cab wcel fabbi_0 iabbi_0 sup_set_class fabbi_1 fabbi_2 cab wcel fabbi_1 iabbi_0 sup_set_class fabbi_0 fabbi_2 cab wcel fabbi_0 fabbi_2 iabbi_0 wsb iabbi_0 sup_set_class fabbi_2 sup_set_class wceq fabbi_0 fabbi_0 iabbi_0 fabbi_2 df-clab fabbi_0 iabbi_0 fabbi_2 sbequ12r syl5bb iabbi_0 sup_set_class fabbi_1 fabbi_2 cab wcel fabbi_1 fabbi_2 iabbi_0 wsb iabbi_0 sup_set_class fabbi_2 sup_set_class wceq fabbi_1 fabbi_1 iabbi_0 fabbi_2 df-clab fabbi_1 iabbi_0 fabbi_2 sbequ12r syl5bb bibi12d cbval bitr2i $.
$}
$( /* Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	fabbi2i_0 $f wff ph $.
	fabbi2i_1 $f set x $.
	fabbi2i_2 $f class A $.
	eabbi2i_0 $e |- ( x e. A <-> ph ) $.
	abbi2i $p |- A = { x | ph } $= fabbi2i_2 fabbi2i_0 fabbi2i_1 cab wceq fabbi2i_1 sup_set_class fabbi2i_2 wcel fabbi2i_0 wb fabbi2i_1 fabbi2i_0 fabbi2i_1 fabbi2i_2 abeq2 eabbi2i_0 mpgbir $.
$}
$( /* Equivalent wff's yield equal class abstractions (inference rule).
       (Contributed by NM, 5-Aug-1993.) */

$)
${
	fabbii_0 $f wff ph $.
	fabbii_1 $f wff ps $.
	fabbii_2 $f set x $.
	eabbii_0 $e |- ( ph <-> ps ) $.
	abbii $p |- { x | ph } = { x | ps } $= fabbii_0 fabbii_1 wb fabbii_0 fabbii_2 cab fabbii_1 fabbii_2 cab wceq fabbii_2 fabbii_0 fabbii_1 fabbii_2 abbi eabbii_0 mpgbi $.
$}
$( /* Theorem abbii is the congruence law for class abstraction. */

$)
$( /* $j congruence 'abbii'; */

$)
$( /* ` y ` is a dummy var. */

$)
$( /* Equivalent wff's yield equal class abstractions (deduction rule).
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       7-Oct-2016.) */

$)
${
	fabbid_0 $f wff ph $.
	fabbid_1 $f wff ps $.
	fabbid_2 $f wff ch $.
	fabbid_3 $f set x $.
	eabbid_0 $e |- F/ x ph $.
	eabbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	abbid $p |- ( ph -> { x | ps } = { x | ch } ) $= fabbid_0 fabbid_1 fabbid_2 wb fabbid_3 wal fabbid_1 fabbid_3 cab fabbid_2 fabbid_3 cab wceq fabbid_0 fabbid_1 fabbid_2 wb fabbid_3 eabbid_0 eabbid_1 alrimi fabbid_1 fabbid_2 fabbid_3 abbi sylib $.
$}
$( /* Equivalent wff's yield equal class abstractions (deduction rule).
       (Contributed by NM, 10-Aug-1993.) */

$)
${
	$d x ph $.
	fabbidv_0 $f wff ph $.
	fabbidv_1 $f wff ps $.
	fabbidv_2 $f wff ch $.
	fabbidv_3 $f set x $.
	eabbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	abbidv $p |- ( ph -> { x | ps } = { x | ch } ) $= fabbidv_0 fabbidv_1 fabbidv_2 fabbidv_3 fabbidv_0 fabbidv_3 nfv eabbidv_0 abbid $.
$}
$( /* ` y ` is a dummy var. */

$)
$( /* Deduction from a wff to a class abstraction.  (Contributed by NM,
       9-Jul-1994.) */

$)
${
	$d x A $.
	$d ph x $.
	fabbi2dv_0 $f wff ph $.
	fabbi2dv_1 $f wff ps $.
	fabbi2dv_2 $f set x $.
	fabbi2dv_3 $f class A $.
	eabbi2dv_0 $e |- ( ph -> ( x e. A <-> ps ) ) $.
	abbi2dv $p |- ( ph -> A = { x | ps } ) $= fabbi2dv_0 fabbi2dv_2 sup_set_class fabbi2dv_3 wcel fabbi2dv_1 wb fabbi2dv_2 wal fabbi2dv_3 fabbi2dv_1 fabbi2dv_2 cab wceq fabbi2dv_0 fabbi2dv_2 sup_set_class fabbi2dv_3 wcel fabbi2dv_1 wb fabbi2dv_2 eabbi2dv_0 alrimiv fabbi2dv_1 fabbi2dv_2 fabbi2dv_3 abeq2 sylibr $.
$}
$( /* ` y ` is a dummy var. */

$)
$( /* Deduction from a wff to a class abstraction.  (Contributed by NM,
       9-Jul-1994.) */

$)
${
	$d x A $.
	$d ph x $.
	fabbi1dv_0 $f wff ph $.
	fabbi1dv_1 $f wff ps $.
	fabbi1dv_2 $f set x $.
	fabbi1dv_3 $f class A $.
	eabbi1dv_0 $e |- ( ph -> ( ps <-> x e. A ) ) $.
	abbi1dv $p |- ( ph -> { x | ps } = A ) $= fabbi1dv_0 fabbi1dv_1 fabbi1dv_2 sup_set_class fabbi1dv_3 wcel wb fabbi1dv_2 wal fabbi1dv_1 fabbi1dv_2 cab fabbi1dv_3 wceq fabbi1dv_0 fabbi1dv_1 fabbi1dv_2 sup_set_class fabbi1dv_3 wcel wb fabbi1dv_2 eabbi1dv_0 alrimiv fabbi1dv_1 fabbi1dv_2 fabbi1dv_3 abeq1 sylibr $.
$}
$( /* A simplification of class abstraction.  Theorem 5.2 of [Quine] p. 35.
       (Contributed by NM, 26-Dec-1993.) */

$)
${
	$d x A $.
	fabid2_0 $f set x $.
	fabid2_1 $f class A $.
	abid2 $p |- { x | x e. A } = A $= fabid2_1 fabid2_0 sup_set_class fabid2_1 wcel fabid2_0 cab fabid2_0 sup_set_class fabid2_1 wcel fabid2_0 fabid2_1 fabid2_0 sup_set_class fabid2_1 wcel biid abbi2i eqcomi $.
$}
$( /* Rule used to change bound variables, using implicit substitution.
       (Contributed by Andrew Salmon, 11-Jul-2011.) */

$)
${
	$d x z $.
	$d y z $.
	$d ph z $.
	$d ps z $.
	icbvab_0 $f set z $.
	fcbvab_0 $f wff ph $.
	fcbvab_1 $f wff ps $.
	fcbvab_2 $f set x $.
	fcbvab_3 $f set y $.
	ecbvab_0 $e |- F/ y ph $.
	ecbvab_1 $e |- F/ x ps $.
	ecbvab_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvab $p |- { x | ph } = { y | ps } $= icbvab_0 fcbvab_0 fcbvab_2 cab fcbvab_1 fcbvab_3 cab fcbvab_0 fcbvab_2 icbvab_0 wsb fcbvab_1 fcbvab_3 icbvab_0 wsb icbvab_0 sup_set_class fcbvab_0 fcbvab_2 cab wcel icbvab_0 sup_set_class fcbvab_1 fcbvab_3 cab wcel fcbvab_0 fcbvab_1 fcbvab_3 icbvab_0 wsb fcbvab_2 icbvab_0 fcbvab_1 fcbvab_3 icbvab_0 fcbvab_2 ecbvab_1 nfsb fcbvab_0 fcbvab_1 fcbvab_3 fcbvab_2 wsb fcbvab_2 sup_set_class icbvab_0 sup_set_class wceq fcbvab_1 fcbvab_3 icbvab_0 wsb fcbvab_1 fcbvab_0 fcbvab_3 fcbvab_2 ecbvab_0 fcbvab_3 sup_set_class fcbvab_2 sup_set_class wceq fcbvab_0 fcbvab_1 fcbvab_0 fcbvab_1 wb fcbvab_2 fcbvab_3 ecbvab_2 equcoms bicomd sbie fcbvab_1 fcbvab_2 icbvab_0 fcbvab_3 sbequ syl5bbr sbie fcbvab_0 icbvab_0 fcbvab_2 df-clab fcbvab_1 icbvab_0 fcbvab_3 df-clab 3bitr4i eqriv $.
$}
$( /* Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-May-1999.) */

$)
${
	$d y ph $.
	$d x ps $.
	fcbvabv_0 $f wff ph $.
	fcbvabv_1 $f wff ps $.
	fcbvabv_2 $f set x $.
	fcbvabv_3 $f set y $.
	ecbvabv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvabv $p |- { x | ph } = { y | ps } $= fcbvabv_0 fcbvabv_1 fcbvabv_2 fcbvabv_3 fcbvabv_0 fcbvabv_3 nfv fcbvabv_1 fcbvabv_2 nfv ecbvabv_0 cbvab $.
$}
$( /* Membership of a class variable in a class abstraction.  (Contributed by
       NM, 23-Dec-1993.) */

$)
${
	$d x A y $.
	$d ph y $.
	iclelab_0 $f set y $.
	fclelab_0 $f wff ph $.
	fclelab_1 $f set x $.
	fclelab_2 $f class A $.
	clelab $p |- ( A e. { x | ph } <-> E. x ( x = A /\ ph ) ) $= iclelab_0 sup_set_class fclelab_2 wceq iclelab_0 sup_set_class fclelab_0 fclelab_1 cab wcel wa iclelab_0 wex iclelab_0 sup_set_class fclelab_2 wceq fclelab_0 fclelab_1 iclelab_0 wsb wa iclelab_0 wex fclelab_2 fclelab_0 fclelab_1 cab wcel fclelab_1 sup_set_class fclelab_2 wceq fclelab_0 wa fclelab_1 wex iclelab_0 sup_set_class fclelab_2 wceq iclelab_0 sup_set_class fclelab_0 fclelab_1 cab wcel wa iclelab_0 sup_set_class fclelab_2 wceq fclelab_0 fclelab_1 iclelab_0 wsb wa iclelab_0 iclelab_0 sup_set_class fclelab_0 fclelab_1 cab wcel fclelab_0 fclelab_1 iclelab_0 wsb iclelab_0 sup_set_class fclelab_2 wceq fclelab_0 iclelab_0 fclelab_1 df-clab anbi2i exbii iclelab_0 fclelab_2 fclelab_0 fclelab_1 cab df-clel fclelab_1 sup_set_class fclelab_2 wceq fclelab_0 wa iclelab_0 sup_set_class fclelab_2 wceq fclelab_0 fclelab_1 iclelab_0 wsb wa fclelab_1 iclelab_0 fclelab_1 sup_set_class fclelab_2 wceq fclelab_0 wa iclelab_0 nfv iclelab_0 sup_set_class fclelab_2 wceq fclelab_0 fclelab_1 iclelab_0 wsb fclelab_1 iclelab_0 sup_set_class fclelab_2 wceq fclelab_1 nfv fclelab_0 fclelab_1 iclelab_0 nfs1v nfan fclelab_1 sup_set_class iclelab_0 sup_set_class wceq fclelab_1 sup_set_class fclelab_2 wceq iclelab_0 sup_set_class fclelab_2 wceq fclelab_0 fclelab_0 fclelab_1 iclelab_0 wsb fclelab_1 sup_set_class iclelab_0 sup_set_class fclelab_2 eqeq1 fclelab_0 fclelab_1 iclelab_0 sbequ12 anbi12d cbvex 3bitr4i $.
$}
$( /* Membership of a class abstraction in another class.  (Contributed by NM,
       17-Jan-2006.) */

$)
${
	$d y A $.
	$d y ph $.
	$d x y $.
	fclabel_0 $f wff ph $.
	fclabel_1 $f set x $.
	fclabel_2 $f set y $.
	fclabel_3 $f class A $.
	clabel $p |- ( { x | ph } e. A <-> E. y ( y e. A /\ A. x ( x e. y <-> ph ) ) ) $= fclabel_0 fclabel_1 cab fclabel_3 wcel fclabel_2 sup_set_class fclabel_0 fclabel_1 cab wceq fclabel_2 sup_set_class fclabel_3 wcel wa fclabel_2 wex fclabel_2 sup_set_class fclabel_3 wcel fclabel_1 sup_set_class fclabel_2 sup_set_class wcel fclabel_0 wb fclabel_1 wal wa fclabel_2 wex fclabel_2 fclabel_0 fclabel_1 cab fclabel_3 df-clel fclabel_2 sup_set_class fclabel_0 fclabel_1 cab wceq fclabel_2 sup_set_class fclabel_3 wcel wa fclabel_2 sup_set_class fclabel_3 wcel fclabel_1 sup_set_class fclabel_2 sup_set_class wcel fclabel_0 wb fclabel_1 wal wa fclabel_2 fclabel_2 sup_set_class fclabel_0 fclabel_1 cab wceq fclabel_1 sup_set_class fclabel_2 sup_set_class wcel fclabel_0 wb fclabel_1 wal fclabel_2 sup_set_class fclabel_3 wcel fclabel_0 fclabel_1 fclabel_2 sup_set_class abeq2 anbi2ci exbii bitri $.
$}
$( /* The right-hand side of the second equality is a way of representing
       proper substitution of ` y ` for ` x ` into a class variable.
       (Contributed by NM, 14-Sep-2003.) */

$)
${
	$d z A $.
	$d z x $.
	$d z y $.
	fsbab_0 $f set x $.
	fsbab_1 $f set y $.
	fsbab_2 $f set z $.
	fsbab_3 $f class A $.
	sbab $p |- ( x = y -> A = { z | [ y / x ] z e. A } ) $= fsbab_0 sup_set_class fsbab_1 sup_set_class wceq fsbab_2 sup_set_class fsbab_3 wcel fsbab_0 fsbab_1 wsb fsbab_2 fsbab_3 fsbab_2 sup_set_class fsbab_3 wcel fsbab_0 fsbab_1 sbequ12 abbi2dv $.
$}

