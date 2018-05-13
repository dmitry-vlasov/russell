$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_axioms_from_the_The_Russell-Bernays_Axioms.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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

$(Minor premise for modus ponendo tollens 1. $)

$(Major premise for modus ponendo tollens 1. $)

$(Modus ponendo tollens 1, one of the "indemonstrables" in Stoic logic.
       See rule 1 on [Lopez-Astorga] p. 12 , rule 1 on [Sanford] p. 40, and
       rule A3 in [Hitchcock] p. 5.  Sanford describes this rule second (after
       ~ mpto2 ) as a "safer, and these days much more common" version of modus
       ponendo tollens because it avoids confusion between inclusive-or and
       exclusive-or.  (Contributed by David A. Wheeler, 3-Jul-2016.) $)

${
	$v ph ps  $.
	f0_mpto1 $f wff ph $.
	f1_mpto1 $f wff ps $.
	e0_mpto1 $e |- ph $.
	e1_mpto1 $e |- -. ( ph /\ ps ) $.
	p_mpto1 $p |- -. ps $= e0_mpto1 e1_mpto1 f0_mpto1 f1_mpto1 p_imnani f0_mpto1 f1_mpto1 a_wn a_ax-mp $.
$}

$(Minor premise for modus ponendo tollens 2. $)

$(Major premise for modus ponendo tollens 2. $)

$(Modus ponendo tollens 2, one of the "indemonstrables" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (Proof shortened by Wolf Lammen, 12-Nov-2017.) $)

${
	$v ph ps  $.
	f0_mpto2 $f wff ph $.
	f1_mpto2 $f wff ps $.
	e0_mpto2 $e |- ph $.
	e1_mpto2 $e |- ( ph \/_ ps ) $.
	p_mpto2 $p |- -. ps $= e0_mpto2 e1_mpto2 f0_mpto2 f1_mpto2 a_df-xor f0_mpto2 f1_mpto2 a_wxo f0_mpto2 f1_mpto2 a_wb a_wn p_mpbi f0_mpto2 f1_mpto2 p_xor3 f0_mpto2 f1_mpto2 a_wb a_wn f0_mpto2 f1_mpto2 a_wn a_wb p_mpbi f0_mpto2 f1_mpto2 a_wn p_mpbi $.
$}

$(Minor premise for modus ponendo tollens 2. $)

$(Major premise for modus ponendo tollens 2. $)

$(Modus ponendo tollens 2, one of the "indemonstrables" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)

${
	$v ph ps  $.
	f0_mpto2OLD $f wff ph $.
	f1_mpto2OLD $f wff ps $.
	e0_mpto2OLD $e |- ph $.
	e1_mpto2OLD $e |- ( ph \/_ ps ) $.
	p_mpto2OLD $p |- -. ps $= e0_mpto2OLD e1_mpto2OLD f0_mpto2OLD f1_mpto2OLD a_df-xor f0_mpto2OLD f1_mpto2OLD a_wxo f0_mpto2OLD f1_mpto2OLD a_wb a_wn p_mpbi f0_mpto2OLD f1_mpto2OLD p_nbbn f0_mpto2OLD a_wn f1_mpto2OLD a_wb f0_mpto2OLD f1_mpto2OLD a_wb a_wn p_mpbir f0_mpto2OLD f1_mpto2OLD p_con1bii f1_mpto2OLD a_wn f0_mpto2OLD p_mpbir $.
$}

$(Minor premise for modus tollendo ponens (original exclusive-or version).
    $)

$(Major premise for modus tollendo ponens (original exclusive-or version).
    $)

$(Modus tollendo ponens (original exclusive-or version), aka disjunctive
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

${
	$v ph ps  $.
	f0_mtp-xor $f wff ph $.
	f1_mtp-xor $f wff ps $.
	e0_mtp-xor $e |- -. ph $.
	e1_mtp-xor $e |- ( ph \/_ ps ) $.
	p_mtp-xor $p |- ps $= e0_mtp-xor e1_mtp-xor f0_mtp-xor f1_mtp-xor p_xorneg f0_mtp-xor a_wn f1_mtp-xor a_wn a_wxo f0_mtp-xor f1_mtp-xor a_wxo p_mpbir f0_mtp-xor a_wn f1_mtp-xor a_wn p_mpto2 f1_mtp-xor p_notnotri $.
$}

$(Obsolete version of ~ mtp-xor as of 11-Nov-2017.  (Contributed by David
       A. Wheeler, 4-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)

${
	$v ph ps  $.
	f0_mtp-xorOLD $f wff ph $.
	f1_mtp-xorOLD $f wff ps $.
	e0_mtp-xorOLD $e |- -. ph $.
	e1_mtp-xorOLD $e |- ( ph \/_ ps ) $.
	p_mtp-xorOLD $p |- ps $= e0_mtp-xorOLD e1_mtp-xorOLD f0_mtp-xorOLD f1_mtp-xorOLD a_df-xor f0_mtp-xorOLD f1_mtp-xorOLD a_wxo f0_mtp-xorOLD f1_mtp-xorOLD a_wb a_wn p_mpbi f0_mtp-xorOLD f1_mtp-xorOLD p_bicom f0_mtp-xorOLD f1_mtp-xorOLD a_wb f1_mtp-xorOLD f0_mtp-xorOLD a_wb p_mtbi f1_mtp-xorOLD f0_mtp-xorOLD p_xor3 f1_mtp-xorOLD f0_mtp-xorOLD a_wb a_wn f1_mtp-xorOLD f0_mtp-xorOLD a_wn a_wb p_mpbi f1_mtp-xorOLD f0_mtp-xorOLD a_wn p_mpbir $.
$}

$(Minor premise for modus tollendo ponens (inclusive-or version). $)

$(Major premise for modus tollendo ponens (inclusive-or version). $)

$(Modus tollendo ponens (inclusive-or version), aka disjunctive
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

${
	$v ph ps  $.
	f0_mtp-or $f wff ph $.
	f1_mtp-or $f wff ps $.
	e0_mtp-or $e |- -. ph $.
	e1_mtp-or $e |- ( ph \/ ps ) $.
	p_mtp-or $p |- ps $= e0_mtp-or e1_mtp-or f0_mtp-or f1_mtp-or p_ori f0_mtp-or a_wn f1_mtp-or a_ax-mp $.
$}

$(Obsolete version of ~ mtp-or as of 11-Nov-2017.  (Contributed by David
       A. Wheeler, 3-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)

${
	$v ph ps  $.
	f0_mtp-orOLD $f wff ph $.
	f1_mtp-orOLD $f wff ps $.
	e0_mtp-orOLD $e |- -. ph $.
	e1_mtp-orOLD $e |- ( ph \/ ps ) $.
	p_mtp-orOLD $p |- ps $= e0_mtp-orOLD e1_mtp-orOLD f0_mtp-orOLD f1_mtp-orOLD p_pm2.53 f0_mtp-orOLD f1_mtp-orOLD a_wo f0_mtp-orOLD a_wn f1_mtp-orOLD a_wi a_ax-mp f0_mtp-orOLD a_wn f1_mtp-orOLD a_ax-mp $.
$}


