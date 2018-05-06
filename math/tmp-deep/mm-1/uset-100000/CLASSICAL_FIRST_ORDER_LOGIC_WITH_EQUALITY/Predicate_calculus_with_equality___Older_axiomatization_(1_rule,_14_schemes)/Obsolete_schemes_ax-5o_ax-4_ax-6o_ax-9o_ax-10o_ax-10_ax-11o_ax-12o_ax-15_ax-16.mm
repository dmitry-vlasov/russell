$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
 Obsolete schemes ax-5o ax-4 ax-6o ax-9o ax-10o ax-10 ax-11o ax-12o ax-15 ax-16

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These older axiom schemes are obsolete and should not be used outside of this
  section.  They are proved above as theorems ax5o , ~ sp , ~ ax6o , ~ ax9o ,
  ~ ax10o , ~ ax10 , ~ ax11o , ~ ax12o , ~ ax15 , and ~ ax16 .

$)
$( Axiom of Specialization.  A quantified wff implies the wff without a
     quantifier (i.e. an instance, or special case, of the generalized wff).
     In other words if something is true for all ` x ` , it is true for any
     specific ` x ` (that would typically occur as a free variable in the wff
     substituted for ` ph ` ).  (A free variable is one that does not occur in
     the scope of a quantifier: ` x ` and ` y ` are both free in ` x = y ` ,
     but only ` x ` is free in ` A. y x = y ` .)  This is one of the axioms of
     what we call "pure" predicate calculus ( ~ ax-4 through ~ ax-7 plus rule
     ~ ax-gen ).  Axiom scheme C5' in [Megill] p. 448 (p. 16 of the preprint).
     Also appears as Axiom B5 of [Tarski] p. 67 (under his system S2, defined
     in the last paragraph on p. 77).

     Note that the converse of this axiom does not hold in general, but a
     weaker inference form of the converse holds and is expressed as rule
     ~ ax-gen .  Conditional forms of the converse are given by ~ ax-12 ,
     ~ ax-15 , ~ ax-16 , and ~ ax-17 .

     Unlike the more general textbook Axiom of Specialization, we cannot choose
     a variable different from ` x ` for the special case.  For use, that
     requires the assistance of equality axioms, and we deal with it later
     after we introduce the definition of proper substitution - see ~ stdpc4 .

     An interesting alternate axiomatization uses ~ ax467 and ~ ax-5o in place
     of ~ ax-4 , ~ ax-5 , ~ ax-6 , and ~ ax-7 .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ sp .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	fax-4_0 $f wff ph $.
	fax-4_1 $f set x $.
	ax-4 $a |- ( A. x ph -> ph ) $.
$}
$( Axiom of Quantified Implication.  This axiom moves a quantifier from
     outside to inside an implication, quantifying ` ps ` .  Notice that ` x `
     must not be a free variable in the antecedent of the quantified
     implication, and we express this by binding ` ph ` to "protect" the axiom
     from a ` ph ` containing a free ` x ` .  One of the 4 axioms of "pure"
     predicate calculus.  Axiom scheme C4' in [Megill] p. 448 (p. 16 of the
     preprint).  It is a special case of Lemma 5 of [Monk2] p. 108 and Axiom 5
     of [Mendelson] p. 69.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax5o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	fax-5o_0 $f wff ph $.
	fax-5o_1 $f wff ps $.
	fax-5o_2 $f set x $.
	ax-5o $a |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.
$}
$( Axiom of Quantified Negation.  This axiom is used to manipulate negated
     quantifiers.  One of the 4 axioms of pure predicate calculus.  Equivalent
     to axiom scheme C7' in [Megill] p. 448 (p. 16 of the preprint).  An
     alternate axiomatization could use ~ ax467 in place of ~ ax-4 , ~ ax-6o ,
     and ~ ax-7 .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax6o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	fax-6o_0 $f wff ph $.
	fax-6o_1 $f set x $.
	ax-6o $a |- ( -. A. x -. A. x ph -> ph ) $.
$}
$( A variant of ~ ax9 .  Axiom scheme C10' in [Megill] p. 448 (p. 16 of the
     preprint).

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax9o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	fax-9o_0 $f wff ph $.
	fax-9o_1 $f set x $.
	fax-9o_2 $f set y $.
	ax-9o $a |- ( A. x ( x = y -> A. x ph ) -> ph ) $.
$}
$( Axiom ~ ax-10o ("o" for "old") was the original version of ~ ax-10 ,
     before it was discovered (in May 2008) that the shorter ~ ax-10 could
     replace it.  It appears as Axiom scheme C11' in [Megill] p. 448 (p. 16 of
     the preprint).

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax10o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	fax-10o_0 $f wff ph $.
	fax-10o_1 $f set x $.
	fax-10o_2 $f set y $.
	ax-10o $a |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $.
$}
$( Axiom of Quantifier Substitution.  One of the equality and substitution
     axioms of predicate calculus with equality.  Appears as Lemma L12 in
     [Megill] p. 445 (p. 12 of the preprint).

     The original version of this axiom was ~ ax-10o ("o" for "old") and was
     replaced with this shorter ~ ax-10 in May 2008.  The old axiom is proved
     from this one as theorem ~ ax10o .  Conversely, this axiom is proved from
     ~ ax-10o as theorem ~ ax10from10o .

     This axiom was proved redundant in July 2015.  See theorem ~ ax10 .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax10 .  (Contributed by NM, 16-May-2008.)
     (New usage is discouraged.) $)
${
	fax-10_0 $f set x $.
	fax-10_1 $f set y $.
	ax-10 $a |- ( A. x x = y -> A. y y = x ) $.
$}
$( Axiom ~ ax-11o ("o" for "old") was the original version of ~ ax-11 ,
     before it was discovered (in Jan. 2007) that the shorter ~ ax-11 could
     replace it.  It appears as Axiom scheme C15' in [Megill] p. 448 (p. 16 of
     the preprint).  It is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of
     [Monk2] p. 105, from which it can be proved by cases.  To understand this
     theorem more easily, think of " ` -. A. x x = y -> ` ..." as informally
     meaning "if ` x ` and ` y ` are distinct variables then..."  The
     antecedent becomes false if the same variable is substituted for ` x ` and
     ` y ` , ensuring the theorem is sound whenever this is the case.  In some
     later theorems, we call an antecedent of the form ` -. A. x x = y ` a
     "distinctor."

     Interestingly, if the wff expression substituted for ` ph ` contains no
     wff variables, the resulting statement _can_ be proved without invoking
     this axiom.  This means that even though this axiom is _metalogically_
     independent from the others, it is not _logically_ independent.
     Specifically, we can prove any wff-variable-free instance of axiom
     ~ ax-11o (from which the ~ ax-11 instance follows by theorem ~ ax11 .)
     The proof is by induction on formula length, using ~ ax11eq and ~ ax11el
     for the basis steps and ~ ax11indn , ~ ax11indi , and ~ ax11inda for the
     induction steps.  (This paragraph is true provided we use ~ ax-10o in
     place of ~ ax-10 .)

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax11o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	fax-11o_0 $f wff ph $.
	fax-11o_1 $f set x $.
	fax-11o_2 $f set y $.
	ax-11o $a |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
$}
$( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms of predicate calculus with equality.  Informally, it says that
     whenever ` z ` is distinct from ` x ` and ` y ` , and ` x = y ` is true,
     then ` x = y ` quantified with ` z ` is also true.  In other words, ` z `
     is irrelevant to the truth of ` x = y ` .  Axiom scheme C9' in [Megill]
     p. 448 (p. 16 of the preprint).  It apparently does not otherwise appear
     in the literature but is easily proved from textbook predicate calculus by
     cases.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax12o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	fax-12o_0 $f set x $.
	fax-12o_1 $f set y $.
	fax-12o_2 $f set z $.
	ax-12o $a |- ( -. A. z z = x -> ( -. A. z z = y -> ( x = y -> A. z x = y ) ) ) $.
$}
$( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms for a non-logical predicate in our predicate calculus with
     equality.  Axiom scheme C14' in [Megill] p. 448 (p. 16 of the preprint).
     It is redundant if we include ~ ax-17 ; see theorem ~ ax15 .  Alternately,
     ~ ax-17 becomes unnecessary in principle with this axiom, but we lose the
     more powerful metalogic afforded by ~ ax-17 .  We retain ~ ax-15 here to
     provide completeness for systems with the simpler metalogic that results
     from omitting ~ ax-17 , which might be easier to study for some
     theoretical purposes.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax15 .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
${
	fax-15_0 $f set x $.
	fax-15_1 $f set y $.
	fax-15_2 $f set z $.
	ax-15 $a |- ( -. A. z z = x -> ( -. A. z z = y -> ( x e. y -> A. z x e. y ) ) ) $.
$}
$( Axiom of Distinct Variables.  The only axiom of predicate calculus
       requiring that variables be distinct (if we consider ~ ax-17 to be a
       metatheorem and not an axiom).  Axiom scheme C16' in [Megill] p. 448 (p.
       16 of the preprint).  It apparently does not otherwise appear in the
       literature but is easily proved from textbook predicate calculus by
       cases.  It is a somewhat bizarre axiom since the antecedent is always
       false in set theory (see ~ dtru ), but nonetheless it is technically
       necessary as you can see from its uses.

       This axiom is redundant if we include ~ ax-17 ; see theorem ~ ax16 .
       Alternately, ~ ax-17 becomes logically redundant in the presence of this
       axiom, but without ~ ax-17 we lose the more powerful metalogic that
       results from being able to express the concept of a set variable not
       occurring in a wff (as opposed to just two set variables being
       distinct).  We retain ~ ax-16 here to provide logical completeness for
       systems with the simpler metalogic that results from omitting ~ ax-17 ,
       which might be easier to study for some theoretical purposes.

       This axiom is obsolete and should no longer be used.  It is proved above
       as theorem ~ ax16 .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
${
	$d x y $.
	fax-16_0 $f wff ph $.
	fax-16_1 $f set x $.
	fax-16_2 $f set y $.
	ax-16 $a |- ( A. x x = y -> ( ph -> A. x ph ) ) $.
$}

