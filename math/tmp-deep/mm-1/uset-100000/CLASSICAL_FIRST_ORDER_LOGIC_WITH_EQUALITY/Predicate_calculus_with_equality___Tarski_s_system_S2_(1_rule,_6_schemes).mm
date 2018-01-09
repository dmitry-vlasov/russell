$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Universal_quantifier__define__exists__and__not_free_.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Rule_scheme_ax-gen_(Generalization).mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-5_(Quantified_Implication).mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-17_(Distinctness)_-_first_use_of__d.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Equality_predicate__define_substitution.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-9_(Existence).mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-8_(Equality).mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Membership_predicate.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_schemes_ax-13_(Left_Membership_Equality).mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_schemes_ax-14_(Right_Membership_Equality).mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Logical_redundancy_of_ax-6_,_ax-7_,_ax-11_,_ax-12.mm $]
$( #*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
    Predicate calculus with equality:  Tarski's system S2 (1 rule, 6 schemes)

#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Here we extend the language of wffs with predicate calculus, which allows us
  to talk about individual objects in a domain of discussion (which for us will
  be the universe of all sets, so we call them "set variables") and make
  true/false statements about predicates, which are relationships between
  objects, such as whether or not two objects are equal.  In addition, we
  introduce universal quantification ("for all") in order to make statements
  about whether a wff holds for every object in the domain of discussion.
  Later we introduce existential quantification ("there exists", ~ df-ex )
  which is defined in terms of universal quantification.

  Our axioms are really axiom _schemes_, and our wff and set variables are
  metavariables ranging over expressions in an underlying "object language."
  This is explained here:  ~ http://us.metamath.org/mpeuni/mmset.html#axiomnote

  Our axiom system starts with the predicate calculus axiom schemes system S2
  of Tarski defined in his 1965 paper, "A Simplified Formalization of Predicate
  Logic with Identity" [Tarski].  System S2 is defined in the last paragraph on
  p. 77, and repeated on p. 81 of [KalishMontague].  We do not include scheme
  B5 (our ~ sp ) since [KalishMontague] shows it to be logically redundant
  (Lemma 9, p. 87, which we prove as theorem ~ spw below).

  Theorem ~ spw can be used to prove any instance of ~ sp having no wff
  metavariables and mutually distinct set variables.  However, it seems that
  ~ sp in its general form cannot be derived from only Tarski's schemes.  We
  do not include B5 i.e.  ~ sp as part of what we call "Tarski's system"
  because we want it to be the smallest set of axioms that is logically
  complete with no redundancies.  We later prove ~ sp as theorem ~ ax4
  using the auxiliary axioms that make our system metalogically complete.

  Our version of Tarski's system S2 consists of propositional calculus plus
  ~ ax-gen , ~ ax-5 , ~ ax-17 , ~ ax-9 , ~ ax-8 , ~ ax-13 , and ~ ax-14 . The
  last 3 are equality axioms that represent 3 sub-schemes of Tarski's scheme
  B8.  Due to its side-condition ("where ` ph ` is an atomic formula and ` ps `
  is obtained by replacing an occurrence of the variable ` x ` by the variable
  ` y ` "), we cannot represent his B8 directly without greatly complicating
  our scheme language, but the simpler schemes ~ ax-8 , ~ ax-13 , and ~ ax-14
  are sufficient for set theory.

  Tarski's system is exactly equivalent to the traditional axiom system in most
  logic textbooks but has the advantage of being easy to manipulate with a
  computer program, and its simpler metalogic (with no built-in notions of free
  variable and proper substitution) is arguably easier for a non-logician human
  to follow step by step in a proof.

  However, in our system that derives schemes (rather than object language
  theorems) from other schemes, Tarski's S2 is not complete.  For example, we
  cannot derive scheme ~ sp , even though (using ~ spw ) we can derive all
  instances of it that don't involve wff metavariables or bundled set
  metavariables.  (Two set metavariables are "bundled" if they can be
  substituted with the same set metavariable i.e. do not have a $d distinct
  variable proviso.)  Later we will introduce auxiliary axiom schemes ~ ax-6 ,
  ~ ax-7 , ~ ax-12 , and ~ ax-11 that are metatheorems of Tarski's system (i.e.
  are logically redundant) but which give our system the property of
  "metalogical completeness," allowing us to prove directly (instead of, say,
  by induction on formula length) all possible schemes that can be expressed in
  our language.

$)

