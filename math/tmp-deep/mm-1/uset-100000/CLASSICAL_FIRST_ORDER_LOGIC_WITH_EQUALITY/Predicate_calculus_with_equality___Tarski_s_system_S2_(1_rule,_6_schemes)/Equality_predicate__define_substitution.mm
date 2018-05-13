$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-17_(Distinctness)_-_first_use_of__d.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Equality predicate; define substitution

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(--- Start of patch to prevent connective overloading $)

$(Add 'class' as a typecode. $)

$($j syntax 'class'; $)

$(This syntax construction states that a variable ` x ` , which has been
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

$(--- End of patch to prevent connective overloading $)

$(--- Start of old code before overloading prevention patch. $)

$((None - the above patch had no old code.) $)

$(--- End of old code before overloading prevention patch. $)

$(Declare the equality predicate symbol. $)

$c = $.

$(Equal sign (read:  'is equal to') $)

$(--- Start of patch to prevent connective overloading $)

$(Extend wff definition to include class equality.

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

${
	$v A B  $.
	f0_wceq $f class A $.
	f1_wceq $f class B $.
	a_wceq $a wff A = B $.
$}

$(Extend wff definition to include atomic formulas using the equality
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

$(--- End of patch to prevent connective overloading $)

$(--- Start of old code before overloading prevention patch. $)

$(@( Extend wff definition to include atomic formulas using the equality
     predicate.

     After we introduce ~ cv and ~ wceq in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wceq". @)
  weq @a wff x = y @.
  $)

$(--- End of old code before overloading prevention patch. $)

$(Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_equs3 $f wff ph $.
	f1_equs3 $f set x $.
	f2_equs3 $f set y $.
	p_equs3 $p |- ( E. x ( x = y /\ ph ) <-> -. A. x ( x = y -> -. ph ) ) $= f1_equs3 a_sup_set_class f2_equs3 a_sup_set_class a_wceq f0_equs3 f1_equs3 p_alinexa f1_equs3 a_sup_set_class f2_equs3 a_sup_set_class a_wceq f0_equs3 a_wn a_wi f1_equs3 a_wal f1_equs3 a_sup_set_class f2_equs3 a_sup_set_class a_wceq f0_equs3 a_wa f1_equs3 a_wex p_con2bii $.
$}

$(Specialization, with additional weakening to allow bundling of ` x ` and
       ` y ` .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       23-Apr-2017.)  (Proof shortened by Wolf Lammen, 5-Aug-2017.) $)

${
	$v ph ps x y  $.
	f0_speimfw $f wff ph $.
	f1_speimfw $f wff ps $.
	f2_speimfw $f set x $.
	f3_speimfw $f set y $.
	e0_speimfw $e |- ( x = y -> ( ph -> ps ) ) $.
	p_speimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) ) $= e0_speimfw f2_speimfw a_sup_set_class f3_speimfw a_sup_set_class a_wceq f0_speimfw f1_speimfw a_wi f2_speimfw p_eximi f2_speimfw a_sup_set_class f3_speimfw a_sup_set_class a_wceq f2_speimfw a_df-ex f0_speimfw f1_speimfw f2_speimfw p_19.35 f2_speimfw a_sup_set_class f3_speimfw a_sup_set_class a_wceq f2_speimfw a_wex f0_speimfw f1_speimfw a_wi f2_speimfw a_wex f2_speimfw a_sup_set_class f3_speimfw a_sup_set_class a_wceq a_wn f2_speimfw a_wal a_wn f0_speimfw f2_speimfw a_wal f1_speimfw f2_speimfw a_wex a_wi p_3imtr3i $.
$}

$(Specialization, with additional weakening to allow bundling of ` x ` and
       ` y ` .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       23-Apr-1017.)  (Proof shortened by Wolf Lammen, 7-Aug-2017.) $)

${
	$v ph ps x y  $.
	f0_spimfw $f wff ph $.
	f1_spimfw $f wff ps $.
	f2_spimfw $f set x $.
	f3_spimfw $f set y $.
	e0_spimfw $e |- ( -. ps -> A. x -. ps ) $.
	e1_spimfw $e |- ( x = y -> ( ph -> ps ) ) $.
	p_spimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> ps ) ) $= e1_spimfw f0_spimfw f1_spimfw f2_spimfw f3_spimfw p_speimfw f1_spimfw f2_spimfw a_df-ex e0_spimfw f1_spimfw f1_spimfw a_wn f2_spimfw a_wal p_con1i f1_spimfw f2_spimfw a_wex f1_spimfw a_wn f2_spimfw a_wal a_wn f1_spimfw p_sylbi f2_spimfw a_sup_set_class f3_spimfw a_sup_set_class a_wceq a_wn f2_spimfw a_wal a_wn f0_spimfw f2_spimfw a_wal f1_spimfw f2_spimfw a_wex f1_spimfw p_syl6 $.
$}

$(Inference that has ~ ax-11 (without ` A. y ` ) as its conclusion.  Uses
       only Tarski's FOL axiom schemes.  The hypotheses may be eliminable
       without one or more of these axioms in special cases.  Proof similar to
       Lemma 16 of [Tarski] p. 70.  (Contributed by NM, 20-May-2008.) $)

${
	$v ph ps x y  $.
	f0_ax11i $f wff ph $.
	f1_ax11i $f wff ps $.
	f2_ax11i $f set x $.
	f3_ax11i $f set y $.
	e0_ax11i $e |- ( x = y -> ( ph <-> ps ) ) $.
	e1_ax11i $e |- ( ps -> A. x ps ) $.
	p_ax11i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $= e0_ax11i e1_ax11i e0_ax11i f2_ax11i a_sup_set_class f3_ax11i a_sup_set_class a_wceq f0_ax11i f1_ax11i p_biimprcd f1_ax11i f2_ax11i a_sup_set_class f3_ax11i a_sup_set_class a_wceq f0_ax11i a_wi f2_ax11i p_alrimih f2_ax11i a_sup_set_class f3_ax11i a_sup_set_class a_wceq f0_ax11i f1_ax11i f2_ax11i a_sup_set_class f3_ax11i a_sup_set_class a_wceq f0_ax11i a_wi f2_ax11i a_wal p_syl6bi $.
$}

$c [ $.

$(Left bracket $)

$c / $.

$(Slash. $)

$c ] $.

$(Right bracket $)

$(Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").
     (Contributed by NM, 24-Jan-2006.) $)

${
	$v ph x y  $.
	f0_wsb $f wff ph $.
	f1_wsb $f set x $.
	f2_wsb $f set y $.
	a_wsb $a wff [ y / x ] ph $.
$}

$(Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
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

${
	$v ph x y  $.
	f0_df-sb $f wff ph $.
	f1_df-sb $f set x $.
	f2_df-sb $f set y $.
	a_df-sb $a |- ( [ y / x ] ph <-> ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.
$}

$(An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sbequ2 $f wff ph $.
	f1_sbequ2 $f set x $.
	f2_sbequ2 $f set y $.
	p_sbequ2 $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $= f0_sbequ2 f1_sbequ2 f2_sbequ2 a_df-sb f1_sbequ2 a_sup_set_class f2_sbequ2 a_sup_set_class a_wceq f0_sbequ2 a_wi f1_sbequ2 a_sup_set_class f2_sbequ2 a_sup_set_class a_wceq f0_sbequ2 a_wa f1_sbequ2 a_wex p_simpl f1_sbequ2 a_sup_set_class f2_sbequ2 a_sup_set_class a_wceq f0_sbequ2 a_wi f1_sbequ2 a_sup_set_class f2_sbequ2 a_sup_set_class a_wceq f0_sbequ2 a_wa f1_sbequ2 a_wex a_wa f1_sbequ2 a_sup_set_class f2_sbequ2 a_sup_set_class a_wceq f0_sbequ2 p_com12 f0_sbequ2 f1_sbequ2 f2_sbequ2 a_wsb f1_sbequ2 a_sup_set_class f2_sbequ2 a_sup_set_class a_wceq f0_sbequ2 a_wi f1_sbequ2 a_sup_set_class f2_sbequ2 a_sup_set_class a_wceq f0_sbequ2 a_wa f1_sbequ2 a_wex a_wa f1_sbequ2 a_sup_set_class f2_sbequ2 a_sup_set_class a_wceq f0_sbequ2 p_syl5bi $.
$}

$(One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sb1 $f wff ph $.
	f1_sb1 $f set x $.
	f2_sb1 $f set y $.
	p_sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $= f0_sb1 f1_sb1 f2_sb1 a_df-sb f0_sb1 f1_sb1 f2_sb1 a_wsb f1_sb1 a_sup_set_class f2_sb1 a_sup_set_class a_wceq f0_sb1 a_wi f1_sb1 a_sup_set_class f2_sb1 a_sup_set_class a_wceq f0_sb1 a_wa f1_sb1 a_wex p_simprbi $.
$}

$(Infer substitution into antecedent and consequent of an implication.
       (Contributed by NM, 25-Jun-1998.) $)

${
	$v ph ps x y  $.
	f0_sbimi $f wff ph $.
	f1_sbimi $f wff ps $.
	f2_sbimi $f set x $.
	f3_sbimi $f set y $.
	e0_sbimi $e |- ( ph -> ps ) $.
	p_sbimi $p |- ( [ y / x ] ph -> [ y / x ] ps ) $= e0_sbimi f0_sbimi f1_sbimi f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq p_imim2i e0_sbimi f0_sbimi f1_sbimi f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq p_anim2i f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f0_sbimi a_wa f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f1_sbimi a_wa f2_sbimi p_eximi f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f0_sbimi a_wi f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f1_sbimi a_wi f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f0_sbimi a_wa f2_sbimi a_wex f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f1_sbimi a_wa f2_sbimi a_wex p_anim12i f0_sbimi f2_sbimi f3_sbimi a_df-sb f1_sbimi f2_sbimi f3_sbimi a_df-sb f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f0_sbimi a_wi f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f0_sbimi a_wa f2_sbimi a_wex a_wa f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f1_sbimi a_wi f2_sbimi a_sup_set_class f3_sbimi a_sup_set_class a_wceq f1_sbimi a_wa f2_sbimi a_wex a_wa f0_sbimi f2_sbimi f3_sbimi a_wsb f1_sbimi f2_sbimi f3_sbimi a_wsb p_3imtr4i $.
$}

$(Infer substitution into both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_sbbii $f wff ph $.
	f1_sbbii $f wff ps $.
	f2_sbbii $f set x $.
	f3_sbbii $f set y $.
	e0_sbbii $e |- ( ph <-> ps ) $.
	p_sbbii $p |- ( [ y / x ] ph <-> [ y / x ] ps ) $= e0_sbbii f0_sbbii f1_sbbii p_biimpi f0_sbbii f1_sbbii f2_sbbii f3_sbbii p_sbimi e0_sbbii f0_sbbii f1_sbbii p_biimpri f1_sbbii f0_sbbii f2_sbbii f3_sbbii p_sbimi f0_sbbii f2_sbbii f3_sbbii a_wsb f1_sbbii f2_sbbii f3_sbbii a_wsb p_impbii $.
$}


