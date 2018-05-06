$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_axioms_from_the_The_Russell-Bernays_Axioms.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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
$( Minor premise for modus ponendo tollens 1. $)
$( Major premise for modus ponendo tollens 1. $)
$( Modus ponendo tollens 1, one of the "indemonstrables" in Stoic logic.
       See rule 1 on [Lopez-Astorga] p. 12 , rule 1 on [Sanford] p. 40, and
       rule A3 in [Hitchcock] p. 5.  Sanford describes this rule second (after
       ~ mpto2 ) as a "safer, and these days much more common" version of modus
       ponendo tollens because it avoids confusion between inclusive-or and
       exclusive-or.  (Contributed by David A. Wheeler, 3-Jul-2016.) $)
${
	fmpto1_0 $f wff ph $.
	fmpto1_1 $f wff ps $.
	empto1_0 $e |- ph $.
	empto1_1 $e |- -. ( ph /\ ps ) $.
	mpto1 $p |- -. ps $= fmpto1_0 fmpto1_1 wn empto1_0 fmpto1_0 fmpto1_1 empto1_1 imnani ax-mp $.
$}
$( Minor premise for modus ponendo tollens 2. $)
$( Major premise for modus ponendo tollens 2. $)
$( Modus ponendo tollens 2, one of the "indemonstrables" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (Proof shortened by Wolf Lammen, 12-Nov-2017.) $)
${
	fmpto2_0 $f wff ph $.
	fmpto2_1 $f wff ps $.
	empto2_0 $e |- ph $.
	empto2_1 $e |- ( ph \/_ ps ) $.
	mpto2 $p |- -. ps $= fmpto2_0 fmpto2_1 wn empto2_0 fmpto2_0 fmpto2_1 wb wn fmpto2_0 fmpto2_1 wn wb fmpto2_0 fmpto2_1 wxo fmpto2_0 fmpto2_1 wb wn empto2_1 fmpto2_0 fmpto2_1 df-xor mpbi fmpto2_0 fmpto2_1 xor3 mpbi mpbi $.
$}
$( Minor premise for modus ponendo tollens 2. $)
$( Major premise for modus ponendo tollens 2. $)
$( Modus ponendo tollens 2, one of the "indemonstrables" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
${
	fmpto2OLD_0 $f wff ph $.
	fmpto2OLD_1 $f wff ps $.
	empto2OLD_0 $e |- ph $.
	empto2OLD_1 $e |- ( ph \/_ ps ) $.
	mpto2OLD $p |- -. ps $= fmpto2OLD_1 wn fmpto2OLD_0 empto2OLD_0 fmpto2OLD_0 fmpto2OLD_1 fmpto2OLD_0 wn fmpto2OLD_1 wb fmpto2OLD_0 fmpto2OLD_1 wb wn fmpto2OLD_0 fmpto2OLD_1 wxo fmpto2OLD_0 fmpto2OLD_1 wb wn empto2OLD_1 fmpto2OLD_0 fmpto2OLD_1 df-xor mpbi fmpto2OLD_0 fmpto2OLD_1 nbbn mpbir con1bii mpbir $.
$}
$( Minor premise for modus tollendo ponens (original exclusive-or version).
    $)
$( Major premise for modus tollendo ponens (original exclusive-or version).
    $)
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
${
	fmtp-xor_0 $f wff ph $.
	fmtp-xor_1 $f wff ps $.
	emtp-xor_0 $e |- -. ph $.
	emtp-xor_1 $e |- ( ph \/_ ps ) $.
	mtp-xor $p |- ps $= fmtp-xor_1 fmtp-xor_0 wn fmtp-xor_1 wn emtp-xor_0 fmtp-xor_0 wn fmtp-xor_1 wn wxo fmtp-xor_0 fmtp-xor_1 wxo emtp-xor_1 fmtp-xor_0 fmtp-xor_1 xorneg mpbir mpto2 notnotri $.
$}
$( Obsolete version of ~ mtp-xor as of 11-Nov-2017.  (Contributed by David
       A. Wheeler, 4-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
${
	fmtp-xorOLD_0 $f wff ph $.
	fmtp-xorOLD_1 $f wff ps $.
	emtp-xorOLD_0 $e |- -. ph $.
	emtp-xorOLD_1 $e |- ( ph \/_ ps ) $.
	mtp-xorOLD $p |- ps $= fmtp-xorOLD_1 fmtp-xorOLD_0 wn emtp-xorOLD_0 fmtp-xorOLD_1 fmtp-xorOLD_0 wb wn fmtp-xorOLD_1 fmtp-xorOLD_0 wn wb fmtp-xorOLD_0 fmtp-xorOLD_1 wb fmtp-xorOLD_1 fmtp-xorOLD_0 wb fmtp-xorOLD_0 fmtp-xorOLD_1 wxo fmtp-xorOLD_0 fmtp-xorOLD_1 wb wn emtp-xorOLD_1 fmtp-xorOLD_0 fmtp-xorOLD_1 df-xor mpbi fmtp-xorOLD_0 fmtp-xorOLD_1 bicom mtbi fmtp-xorOLD_1 fmtp-xorOLD_0 xor3 mpbi mpbir $.
$}
$( Minor premise for modus tollendo ponens (inclusive-or version). $)
$( Major premise for modus tollendo ponens (inclusive-or version). $)
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
${
	fmtp-or_0 $f wff ph $.
	fmtp-or_1 $f wff ps $.
	emtp-or_0 $e |- -. ph $.
	emtp-or_1 $e |- ( ph \/ ps ) $.
	mtp-or $p |- ps $= fmtp-or_0 wn fmtp-or_1 emtp-or_0 fmtp-or_0 fmtp-or_1 emtp-or_1 ori ax-mp $.
$}
$( Obsolete version of ~ mtp-or as of 11-Nov-2017.  (Contributed by David
       A. Wheeler, 3-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
${
	fmtp-orOLD_0 $f wff ph $.
	fmtp-orOLD_1 $f wff ps $.
	emtp-orOLD_0 $e |- -. ph $.
	emtp-orOLD_1 $e |- ( ph \/ ps ) $.
	mtp-orOLD $p |- ps $= fmtp-orOLD_0 wn fmtp-orOLD_1 emtp-orOLD_0 fmtp-orOLD_0 fmtp-orOLD_1 wo fmtp-orOLD_0 wn fmtp-orOLD_1 wi emtp-orOLD_1 fmtp-orOLD_0 fmtp-orOLD_1 pm2.53 ax-mp ax-mp $.
$}

