$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes).mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes)/Obsolete_schemes_ax-5o_ax-4_ax-6o_ax-9o_ax-10o_ax-10_ax-11o_ax-12o_ax-15_ax-16.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes)/Rederive_new_axioms_from_old__theorems_ax5_,_ax6_,_ax9from9o_,_ax11_,_ax12.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes)/Legacy_theorems_using_obsolete_axioms.mm $]

$(#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Predicate calculus with equality:  Older axiomatization (1 rule, 14 schemes)

#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  The "metalogical completeness theorem", Theorem 9.7 of [Megill] p. 448, uses
  a different but (logically and metalogically) equivalent set of axiom schemes
  for its proof.  In order to show that our axiomatization is also
  metalogically complete, we derive the axiom schemes of that paper in this
  section (or mention where they are derived, if they have already been derived
  as therorems above).  Additionally, we re-derive our axiomatization from the
  one in the paper, showing that the two systems are equivalent.

  The 14 predicate calculus axioms used by the paper are ~ ax-5o , ~ ax-4 ,
  ~ ax-7 , ~ ax-6o , ~ ax-8 , ~ ax-12o , ~ ax-9o , ~ ax-10o , ~ ax-13 ,
  ~ ax-14 , ~ ax-15 , ~ ax-11o , ~ ax-16 , and ~ ax-17 .  Like ours, it
  includes the rule of generalization ( ~ ax-gen ).

  The ones we need to prove from our axioms are ~ ax-5o , ~ ax-4 ,
  ~ ax-6o , ~ ax-12o , ~ ax-9o , ~ ax-10o , ~ ax-15 , ~ ax-11o ,
  and ~ ax-16 . The theorems showing the derivations of those axioms,
  which have all been proved earlier, are ~ ax5o , ~ ax4 (also called
  ~ sp ), ~ ax6o , ~ ax12o , ~ ax9o , ~ ax10o , ~ ax15 , ~ ax11o ,
  ~ ax16 , and ~ ax10 . In addition, ~ ax-10 was an intermediate axiom we
  adopted at one time, and we show its proof in this section as
  ~ ax10from10o .

  This section also includes a few miscellaneous legacy theorems such as
  ~ hbequid use the older axioms.

  Note:  The axioms and theorems in this section should not be used outside of
  this section.  Inside this section, we may use the external axioms ~ ax-gen ,
  ~ ax-17 , ~ ax-8 , ~ ax-9 , ~ ax-13 , and ~ ax-14 since they are common to
  both our current and the older axiomatizations.  (These are the ones that
  were never revised.)

  The following newer axioms may NOT be used in this section until we
  have proved them from the older axioms:  ~ ax-5 , ~ ax-6 , ~ ax-9 ,
  ~ ax-11 , and ~ ax-12 .  However, once we have rederived an axiom
  (e.g. theorem ~ ax5 for axiom ~ ax-5 ), we may make use of theorems
  outside of this section that make use of the rederived axiom (e.g. we
  may use theorem ~ alimi , which uses ~ ax-5 , after proving ~ ax5 ).

$)


