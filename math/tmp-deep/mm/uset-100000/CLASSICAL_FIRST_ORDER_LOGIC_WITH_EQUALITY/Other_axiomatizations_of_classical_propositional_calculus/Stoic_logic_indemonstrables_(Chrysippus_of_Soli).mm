
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_axioms_from_the_The_Russell-Bernays_Axioms.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Stoic logic indemonstrables (Chrysippus of Soli)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The Greek Stoics developed a system of logic.
  The Stoic Chrysippus, in particular, was often considered one of the greatest
  logicians of antiquity.
  Stoic logic is different from Aristotle's system, since it focuses
  on propositional logic,
  though later thinkers did combine the systems of the Stoics with Aristotle.
  Jan Lukasiewicz reports,
  "For anybody familiar with mathematical logic it is self-evident
  that the Stoic dialectic is the ancient form of modern propositional logic"
  ( _On the history of the logic of proposition_ by Jan Lukasiewicz (1934),
  translated in: _Selected Works_ - Edited by Ludwik Borkowski -
  Amsterdam, North-Holland, 1970 pp. 197-217,
  referenced in "History of Logic"
  ~ https://www.historyoflogic.com/logic-stoics.htm ).
  For more about Aristotle's system, see ~ barbara and related theorems.

  A key part of the Stoic logic system is a set of five "indemonstrables"
  assigned to Chrysippus of Soli by Diogenes Laertius, though in
  general it is difficult to assign specific
  ideas to specific thinkers.
  The indemonstrables are described in, for example,
  [Lopez-Astorga] p. 11 , [Sanford] p. 39, and [Hitchcock] p. 5.
  These indemonstrables are
  modus ponendo ponens (modus ponens) ~ ax-mp ,
  modus tollendo tollens (modus tollens) ~ mto ,
  modus ponendo tollens I ~ mpto1 ,
  modus ponendo tollens II ~ mpto2 , and
  modus tollendo ponens (exclusive-or version) ~ mtp-xor .
  The first is an axiom, the second is already proved; in this section
  we prove the other three.
  Since we assume or prove all of indemonstrables, the system of logic we use
  here is as at least as strong as the set of Stoic indemonstrables.
  Note that modus tollendo ponens ~ mtp-xor originally used exclusive-or,
  but over time the name modus tollendo ponens has increasingly referred
  to an inclusive-or variation, which is proved in ~ mtp-or .
  This set of indemonstrables is not the entire system of Stoic logic.

$)

  ${
    $( Minor premise for modus ponendo tollens 1. $)
    mpto1.1 $e |- ph $.
    $( Major premise for modus ponendo tollens 1. $)
    mpto1.2 $e |- -. ( ph /\ ps ) $.
    $( Modus ponendo tollens 1, one of the "indemonstrables" in Stoic logic.
       See rule 1 on [Lopez-Astorga] p. 12 , rule 1 on [Sanford] p. 40, and
       rule A3 in [Hitchcock] p. 5.  Sanford describes this rule second (after
       ~ mpto2 ) as a "safer, and these days much more common" version of modus
       ponendo tollens because it avoids confusion between inclusive-or and
       exclusive-or.  (Contributed by David A. Wheeler, 3-Jul-2016.) $)
    mpto1 $p |- -. ps $=
      wph wps wn mpto1.1 wph wps mpto1.2 imnani ax-mp $.
  $}

  ${
    $( Minor premise for modus ponendo tollens 2. $)
    mpto2.1 $e |- ph $.
    $( Major premise for modus ponendo tollens 2. $)
    mpto2.2 $e |- ( ph \/_ ps ) $.
    $( Modus ponendo tollens 2, one of the "indemonstrables" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (Proof shortened by Wolf Lammen, 12-Nov-2017.) $)
    mpto2 $p |- -. ps $=
      wph wps wn mpto2.1 wph wps wb wn wph wps wn wb wph wps wxo wph wps wb wn
      mpto2.2 wph wps df-xor mpbi wph wps xor3 mpbi mpbi $.
  $}

  ${
    $( Minor premise for modus ponendo tollens 2. $)
    mpto2OLD.1 $e |- ph $.
    $( Major premise for modus ponendo tollens 2. $)
    mpto2OLD.2 $e |- ( ph \/_ ps ) $.
    $( Modus ponendo tollens 2, one of the "indemonstrables" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    mpto2OLD $p |- -. ps $=
      wps wn wph mpto2OLD.1 wph wps wph wn wps wb wph wps wb wn wph wps wxo wph
      wps wb wn mpto2OLD.2 wph wps df-xor mpbi wph wps nbbn mpbir con1bii mpbir
      $.
  $}

  ${
    $( Minor premise for modus tollendo ponens (original exclusive-or version).
    $)
    mtp-xor.1 $e |- -. ph $.
    $( Major premise for modus tollendo ponens (original exclusive-or version).
    $)
    mtp-xor.2 $e |- ( ph \/_ ps ) $.
    $( Modus tollendo ponens (original exclusive-or version), aka disjunctive
       syllogism, one of the five "indemonstrables" in Stoic logic.  The rule
       says, "if ` ph ` is not true, and either ` ph ` or ` ps ` (exclusively)
       are true, then ` ps ` must be true."  Today the name "modus tollendo
       ponens" often refers to a variant, the inclusive-or version as defined
       in ~ mtp-or .  See rule 3 on [Lopez-Astorga] p. 12 (note that the "or"
       is the same as ~ mpto2 , that is, it is exclusive-or ~ df-xor ), rule 3
       of [Sanford] p. 39 (where it is not as clearly stated which kind of "or"
       is used but it appears to be in the same sense as ~ mpto2 ), and rule A5
       in [Hitchcock] p. 5 (exclusive-or is expressly used).  (Contributed by
       David A. Wheeler, 4-Jul-2016.)  (Proof shortened by Wolf Lammen,
       11-Nov-2017.) $)
    mtp-xor $p |- ps $=
      wps wph wn wps wn mtp-xor.1 wph wn wps wn wxo wph wps wxo mtp-xor.2 wph
      wps xorneg mpbir mpto2 notnotri $.

    $( Obsolete version of ~ mtp-xor as of 11-Nov-2017.  (Contributed by David
       A. Wheeler, 4-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    mtp-xorOLD $p |- ps $=
      wps wph wn mtp-xor.1 wps wph wb wn wps wph wn wb wph wps wb wps wph wb
      wph wps wxo wph wps wb wn mtp-xor.2 wph wps df-xor mpbi wph wps bicom
      mtbi wps wph xor3 mpbi mpbir $.
  $}

  ${
    $( Minor premise for modus tollendo ponens (inclusive-or version). $)
    mtp-or.1 $e |- -. ph $.
    $( Major premise for modus tollendo ponens (inclusive-or version). $)
    mtp-or.2 $e |- ( ph \/ ps ) $.
    $( Modus tollendo ponens (inclusive-or version), aka disjunctive
       syllogism.  This is similar to ~ mtp-xor , one of the five original
       "indemonstrables" in Stoic logic.  However, in Stoic logic this rule
       used exclusive-or, while the name modus tollendo ponens often refers to
       a variant of the rule that uses inclusive-or instead.  The rule says,
       "if ` ph ` is not true, and ` ph ` or ` ps ` (or both) are true, then
       ` ps ` must be true."  An alternative phrasing is, "Once you eliminate
       the impossible, whatever remains, no matter how improbable, must be the
       truth." -- Sherlock Holmes (Sir Arthur Conan Doyle, 1890:  The Sign of
       the Four, ch. 6).  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (Proof shortened by Wolf Lammen, 11-Nov-2017.) $)
    mtp-or $p |- ps $=
      wph wn wps mtp-or.1 wph wps mtp-or.2 ori ax-mp $.

    $( Obsolete version of ~ mtp-or as of 11-Nov-2017.  (Contributed by David
       A. Wheeler, 3-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    mtp-orOLD $p |- ps $=
      wph wn wps mtp-or.1 wph wps wo wph wn wps wi mtp-or.2 wph wps pm2.53
      ax-mp ax-mp $.
  $}



