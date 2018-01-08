$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-17_(Distinctness)_-_first_use_of__d.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Equality predicate; define substitution

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* --- Start of patch to prevent connective overloading */

$)
$( /* Add 'class' as a typecode. */

$)
$( /* $j syntax 'class'; */

$)
$( /* This syntax construction states that a variable ` x ` , which has been
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
     ambiguity that would complicate some Metamath parsers.) */

$)
$( /* --- End of patch to prevent connective overloading */

$)
$( /* --- Start of old code before overloading prevention patch. */

$)
$( /* (None - the above patch had no old code.) */

$)
$( /* --- End of old code before overloading prevention patch. */

$)
$( /* Declare the equality predicate symbol. */

$)
$c =  $.
$( /* Equal sign (read:  'is equal to') */

$)
$( /* --- Start of patch to prevent connective overloading */

$)
$( /* Extend wff definition to include class equality.

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
       theory usage of ~ wceq .) */

$)
$v A $.
$v B $.
${
	fwceq_0 $f class A $.
	fwceq_1 $f class B $.
	wceq $a wff A = B $.
$}
$( /* Extend wff definition to include atomic formulas using the equality
     predicate.

     (Instead of introducing ~ weq as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wceq .  This lets us avoid overloading
     the ` = ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ weq is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wceq .  Note:  To see the proof steps of this syntax proof, type "show
     proof weq /all" in the Metamath program.)  (Contributed by NM,
     24-Jan-2006.) */

$)
$( /* --- End of patch to prevent connective overloading */

$)
$( /* --- Start of old code before overloading prevention patch. */

$)
$( /* @( Extend wff definition to include atomic formulas using the equality
     predicate.

     After we introduce ~ cv and ~ wceq in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wceq". @)
  weq @a wff x = y @.
  */

$)
$( /* --- End of old code before overloading prevention patch. */

$)
$( /* Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) */

$)
${
	fequs3_0 $f wff ph $.
	fequs3_1 $f set x $.
	fequs3_2 $f set y $.
	equs3 $p |- ( E. x ( x = y /\ ph ) <-> -. A. x ( x = y -> -. ph ) ) $= fequs3_1 sup_set_class fequs3_2 sup_set_class wceq fequs3_0 wn wi fequs3_1 wal fequs3_1 sup_set_class fequs3_2 sup_set_class wceq fequs3_0 wa fequs3_1 wex fequs3_1 sup_set_class fequs3_2 sup_set_class wceq fequs3_0 fequs3_1 alinexa con2bii $.
$}
$( /* Specialization, with additional weakening to allow bundling of ` x ` and
       ` y ` .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       23-Apr-2017.)  (Proof shortened by Wolf Lammen, 5-Aug-2017.) */

$)
${
	fspeimfw_0 $f wff ph $.
	fspeimfw_1 $f wff ps $.
	fspeimfw_2 $f set x $.
	fspeimfw_3 $f set y $.
	espeimfw_0 $e |- ( x = y -> ( ph -> ps ) ) $.
	speimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) ) $= fspeimfw_2 sup_set_class fspeimfw_3 sup_set_class wceq fspeimfw_2 wex fspeimfw_0 fspeimfw_1 wi fspeimfw_2 wex fspeimfw_2 sup_set_class fspeimfw_3 sup_set_class wceq wn fspeimfw_2 wal wn fspeimfw_0 fspeimfw_2 wal fspeimfw_1 fspeimfw_2 wex wi fspeimfw_2 sup_set_class fspeimfw_3 sup_set_class wceq fspeimfw_0 fspeimfw_1 wi fspeimfw_2 espeimfw_0 eximi fspeimfw_2 sup_set_class fspeimfw_3 sup_set_class wceq fspeimfw_2 df-ex fspeimfw_0 fspeimfw_1 fspeimfw_2 19.35 3imtr3i $.
$}
$( /* Specialization, with additional weakening to allow bundling of ` x ` and
       ` y ` .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       23-Apr-1017.)  (Proof shortened by Wolf Lammen, 7-Aug-2017.) */

$)
${
	fspimfw_0 $f wff ph $.
	fspimfw_1 $f wff ps $.
	fspimfw_2 $f set x $.
	fspimfw_3 $f set y $.
	espimfw_0 $e |- ( -. ps -> A. x -. ps ) $.
	espimfw_1 $e |- ( x = y -> ( ph -> ps ) ) $.
	spimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> ps ) ) $= fspimfw_2 sup_set_class fspimfw_3 sup_set_class wceq wn fspimfw_2 wal wn fspimfw_0 fspimfw_2 wal fspimfw_1 fspimfw_2 wex fspimfw_1 fspimfw_0 fspimfw_1 fspimfw_2 fspimfw_3 espimfw_1 speimfw fspimfw_1 fspimfw_2 wex fspimfw_1 wn fspimfw_2 wal wn fspimfw_1 fspimfw_1 fspimfw_2 df-ex fspimfw_1 fspimfw_1 wn fspimfw_2 wal espimfw_0 con1i sylbi syl6 $.
$}
$( /* Inference that has ~ ax-11 (without ` A. y ` ) as its conclusion.  Uses
       only Tarski's FOL axiom schemes.  The hypotheses may be eliminable
       without one or more of these axioms in special cases.  Proof similar to
       Lemma 16 of [Tarski] p. 70.  (Contributed by NM, 20-May-2008.) */

$)
${
	fax11i_0 $f wff ph $.
	fax11i_1 $f wff ps $.
	fax11i_2 $f set x $.
	fax11i_3 $f set y $.
	eax11i_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	eax11i_1 $e |- ( ps -> A. x ps ) $.
	ax11i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $= fax11i_2 sup_set_class fax11i_3 sup_set_class wceq fax11i_0 fax11i_1 fax11i_2 sup_set_class fax11i_3 sup_set_class wceq fax11i_0 wi fax11i_2 wal eax11i_0 fax11i_1 fax11i_2 sup_set_class fax11i_3 sup_set_class wceq fax11i_0 wi fax11i_2 eax11i_1 fax11i_2 sup_set_class fax11i_3 sup_set_class wceq fax11i_0 fax11i_1 eax11i_0 biimprcd alrimih syl6bi $.
$}
$c [  $.
$( /* Left bracket */

$)
$c /  $.
$( /* Slash. */

$)
$c ]  $.
$( /* Right bracket */

$)
$( /* Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").
     (Contributed by NM, 24-Jan-2006.) */

$)
${
	fwsb_0 $f wff ph $.
	fwsb_1 $f set x $.
	fwsb_2 $f set y $.
	wsb $a wff [ y / x ] ph $.
$}
$( /* Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
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
     variables may occur in wff ` ph ` .  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fdf-sb_0 $f wff ph $.
	fdf-sb_1 $f set x $.
	fdf-sb_2 $f set y $.
	df-sb $a |- ( [ y / x ] ph <-> ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.
$}
$( /* An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fsbequ2_0 $f wff ph $.
	fsbequ2_1 $f set x $.
	fsbequ2_2 $f set y $.
	sbequ2 $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $= fsbequ2_0 fsbequ2_1 fsbequ2_2 wsb fsbequ2_1 sup_set_class fsbequ2_2 sup_set_class wceq fsbequ2_0 wi fsbequ2_1 sup_set_class fsbequ2_2 sup_set_class wceq fsbequ2_0 wa fsbequ2_1 wex wa fsbequ2_1 sup_set_class fsbequ2_2 sup_set_class wceq fsbequ2_0 fsbequ2_0 fsbequ2_1 fsbequ2_2 df-sb fsbequ2_1 sup_set_class fsbequ2_2 sup_set_class wceq fsbequ2_0 wi fsbequ2_1 sup_set_class fsbequ2_2 sup_set_class wceq fsbequ2_0 wa fsbequ2_1 wex wa fsbequ2_1 sup_set_class fsbequ2_2 sup_set_class wceq fsbequ2_0 fsbequ2_1 sup_set_class fsbequ2_2 sup_set_class wceq fsbequ2_0 wi fsbequ2_1 sup_set_class fsbequ2_2 sup_set_class wceq fsbequ2_0 wa fsbequ2_1 wex simpl com12 syl5bi $.
$}
$( /* One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) */

$)
${
	fsb1_0 $f wff ph $.
	fsb1_1 $f set x $.
	fsb1_2 $f set y $.
	sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $= fsb1_0 fsb1_1 fsb1_2 wsb fsb1_1 sup_set_class fsb1_2 sup_set_class wceq fsb1_0 wi fsb1_1 sup_set_class fsb1_2 sup_set_class wceq fsb1_0 wa fsb1_1 wex fsb1_0 fsb1_1 fsb1_2 df-sb simprbi $.
$}
$( /* Infer substitution into antecedent and consequent of an implication.
       (Contributed by NM, 25-Jun-1998.) */

$)
${
	fsbimi_0 $f wff ph $.
	fsbimi_1 $f wff ps $.
	fsbimi_2 $f set x $.
	fsbimi_3 $f set y $.
	esbimi_0 $e |- ( ph -> ps ) $.
	sbimi $p |- ( [ y / x ] ph -> [ y / x ] ps ) $= fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_0 wi fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_0 wa fsbimi_2 wex wa fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_1 wi fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_1 wa fsbimi_2 wex wa fsbimi_0 fsbimi_2 fsbimi_3 wsb fsbimi_1 fsbimi_2 fsbimi_3 wsb fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_0 wi fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_1 wi fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_0 wa fsbimi_2 wex fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_1 wa fsbimi_2 wex fsbimi_0 fsbimi_1 fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq esbimi_0 imim2i fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_0 wa fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq fsbimi_1 wa fsbimi_2 fsbimi_0 fsbimi_1 fsbimi_2 sup_set_class fsbimi_3 sup_set_class wceq esbimi_0 anim2i eximi anim12i fsbimi_0 fsbimi_2 fsbimi_3 df-sb fsbimi_1 fsbimi_2 fsbimi_3 df-sb 3imtr4i $.
$}
$( /* Infer substitution into both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.) */

$)
${
	fsbbii_0 $f wff ph $.
	fsbbii_1 $f wff ps $.
	fsbbii_2 $f set x $.
	fsbbii_3 $f set y $.
	esbbii_0 $e |- ( ph <-> ps ) $.
	sbbii $p |- ( [ y / x ] ph <-> [ y / x ] ps ) $= fsbbii_0 fsbbii_2 fsbbii_3 wsb fsbbii_1 fsbbii_2 fsbbii_3 wsb fsbbii_0 fsbbii_1 fsbbii_2 fsbbii_3 fsbbii_0 fsbbii_1 esbbii_0 biimpi sbimi fsbbii_1 fsbbii_0 fsbbii_2 fsbbii_3 fsbbii_0 fsbbii_1 esbbii_0 biimpri sbimi impbii $.
$}

