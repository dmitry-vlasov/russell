$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_related_to_classical_predicate_calculus/Predicate_calculus_with_all_distinct_variables.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Aristotelian logic: Assertic syllogisms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Model the Aristotelian assertic syllogisms using modern notation.
  This section shows that the Aristotelian assertic syllogisms can be proven
  with our axioms of logic, and also provides generally useful theorems.

  In antiquity Aristotelian logic and Stoic logic
  (see ~ mpto1 ) were the leading logical systems.
  Aristotelian logic became the leading system in medieval Europe;
  this section models this system (including later refinements to it).
  Aristotle defined syllogisms very generally
  ("a discourse in which certain (specific) things having been supposed,
  something different from the things supposed results of necessity
  because these things are so")
  Aristotle, _Prior Analytics_ 24b18-20.
  However, in _Prior Analytics_ he limits himself to
  categorical syllogisms that consist of three categorical propositions
  with specific structures.  The syllogisms are the valid subset of
  the possible combinations of these structures.
  The medieval schools used vowels to identify the types of terms
  (a=all, e=none, i=some, and o=some are not), and named the different
  syllogisms with Latin words that had the vowels in the intended order.

  "There is a surprising amount of scholarly debate
  about how best to formalize Aristotle's syllogisms..." according to
  _Aristotle's Modal Proofs: Prior Analytics A8-22 in Predicate Logic_,
  Adriane Rini, Springer, 2011, ISBN 978-94-007-0049-9, page 28.
  For example, Lukasiewicz believes it is important to note that
  "Aristotle does not introduce singular terms or premisses into his system".
  Lukasiewicz also believes that Aristotelian syllogisms are
  predicates (having a true/false value), not inference rules:
  "The characteristic sign of an inference is the word 'therefore'...
  no syllogism is formulated by Aristotle primarily as an inference,
  but they are all implications."
  Jan Lukasiewicz, _Aristotle's Syllogistic from the Standpoint of
  Modern Formal Logic_, Second edition, Oxford, 1957, page 1-2.
  Lukasiewicz devised a specialized prefix notation for representing
  Aristotelian syllogisms instead of using standard predicate logic notation.

  We instead translate each Aristotelian syllogism into an inference rule,
  and each rule is defined using standard predicate logic notation and
  predicates.  The predicates are represented by wff variables
  that may depend on the quantified variable ` x ` .
  Our translation is essentially identical to the one
  use in Rini page 18, Table 2 "Non-Modal Syllogisms in
  Lower Predicate Calculus (LPC)", which uses
  standard predicate logic with predicates.  Rini states,
  "the crucial point is that we capture the meaning Aristotle intends,
  and the method by which we represent that meaning is less important."
  There are two differences: we make the existence criteria explicit, and
  we use ` ph ` , ` ps ` , and ` ch ` in the order they appear
  (a common Metamath convention).
  Patzig also uses standard predicate logic notation and predicates
  (though he interprets them as conditional propositions, not as
  inference rules); see
  Gunther Patzig, _Aristotle's Theory of the Syllogism_ second edition, 1963,
  English translation by Jonathan Barnes, 1968, page 38.
  Terms such as "all" and "some" are translated into predicate logic
  using the aproach devised by Frege and Russell.
  "Frege (and Russell) devised an ingenious procedure for regimenting
  binary quantifiers like "every" and "some" in terms of unary quantifiers
  like "everything" and "something": they formalized sentences of the form
  "Some A is B" and "Every A is B" as
  exists x (Ax and Bx) and all x (Ax implies Bx), respectively."
  "Quantifiers and Quantification", _Stanford Encyclopedia of Philosophy_,
  ~ http://plato.stanford.edu/entries/quantification/ .
  See _Principia Mathematica_ page 22 and *10 for more information
  (especially *10.3 and *10.26).

  Expressions of the form "no ` ph ` is ` ps ` " are consistently translated as
  ` A. x ( ph -> -. ps ) ` .  These can also be expressed as
  ` -. E. x ( ph /\ ps ) ` , per ~ alinexa .
  We translate "all ` ph ` is ` ps ` " to ` A. x ( ph -> ps ) ` ,
  "some ` ph ` is ` ps ` " to ` E. x ( ph /\ ps ) ` , and
  "some ` ph ` is not ` ps ` " to ` E. x ( ph /\ -. ps ) ` .
  It is traditional to use the singular verb "is", not the plural
  verb "are", in the generic expressions.
  By convention the major premise is listed first.

  In traditional Aristotelian syllogisms the predicates
  have a restricted form ("x is a ..."); those predicates
  could be modeled in modern notation by constructs such as
  ` x = A ` , ` x e. A ` , or ` x C_ A ` .
  Here we use wff variables instead of specialized restricted forms.
  This generalization makes the syllogisms more useful
  in more circumstances.  In addition, these expressions make
  it clearer that the syllogisms of Aristolean logic are the
  forerunners of predicate calculus.  If we used restricted forms
  like ` x e. A ` instead, we would not only unnecessarily limit
  their use, but we would also need to use set and class axioms,
  making their relationship to predicate calculus less clear.

  There are some widespread misconceptions about the existential
  assumptions made by Aristotle (aka "existential import").
  Aristotle was not trying to develop something exactly corresponding
  to modern logic.  Aristotle devised "a companion-logic for science.
  He relegates fictions like fairy godmothers and mermaids and unicorns to
  the realms of poetry and literature. In his mind, they exist outside the
  ambit of science. This is why he leaves no room for such non-existent
  entities in his logic.  This is a thoughtful choice, not an inadvertent
  omission. Technically, Aristotelian science is a search for definitions,
  where a definition is "a phrase signifying a thing's essence."
  (Topics, I.5.102a37, Pickard-Cambridge.)...
  Because non-existent entities cannot be anything, they do not, in
  Aristotle's mind, possess an essence...  This is why he leaves
  no place for fictional entities like goat-stags (or unicorns)."
  Source: Louis F. Groarke, "Aristotle: Logic",
  section 7. (Existential Assumptions),
  _Internet Encyclopedia of Philosophy_ (A Peer-Reviewed Academic Resource),
  ~ http://www.iep.utm.edu/aris-log/ .
  Thus, some syllogisms have "extra" existence
  hypotheses that do not directly appear in Aristotle's original materials
  (since they were always assumed); they are added where they are needed.
  This affects ~ barbari , ~ celaront , ~ cesaro , ~ camestros , ~ felapton ,
  ~ darapti , ~ calemos , ~ fesapo , and ~ bamalip .

  These are only the _assertic_ syllogisms.
  Aristotle also defined modal syllogisms that deal with modal
  qualifiers such as "necessarily" and "possibly".
  Historically Aristotelian modal syllogisms were not as widely used.
  For more about modal syllogisms in a modern context, see Rini as well as
  _Aristotle's Modal Syllogistic_ by Marko Malink, Harvard
  University Press, November 2013.  We do not treat them further here.

  Aristotelean logic is essentially the forerunner of predicate calculus
  (as well as set theory since it discusses membership in groups),
  while Stoic logic is essentially the forerunner of propositional calculus.
$)

$(Figure 1.  Aristotelian syllogisms are grouped by "figures",
     which doesn't matter for our purposes but is a reasonable way
     to order them. $)

$(Major premise for the Aristotelian syllogism "Barbara", e.g.,
       "All men are mortal". By convention, the major premise is first. $)

$(Minor premise for Barbara, e.g., "Socrates is a man". $)

$("Barbara", one of the fundamental syllogisms of Aristotelian logic.  All
       ` ph ` is ` ps ` , and all ` ch ` is ` ph ` , therefore all ` ch ` is
       ` ps ` .  (In Aristotelian notation, AAA-1:  MaP and SaM therefore SaP.)
       For example, given "All men are mortal" and "Socrates is a man", we can
       prove "Socrates is mortal".  If H is the set of men, M is the set of
       mortal beings, and S is Socrates, these word phrases can be represented
       as ` A. x ( x e. H -> x e. M ) ` (all men are mortal) and
       ` A. x ( x = S -> x e. H ) ` (Socrates is a man) therefore
       ` A. x ( x = S -> x e. M ) ` (Socrates is mortal).  Russell and
       Whitehead note that the "syllogism in Barbara is derived..." from
       ~ syl .  (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Most
       of the proof is in ~ alsyl .  There are a legion of sources for Barbara,
       including ~ http://www.friesian.com/aristotl.htm ,
       ~ http://plato.stanford.edu/entries/aristotle-logic/ , and
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_barbara $f wff ph $.
	f1_barbara $f wff ps $.
	f2_barbara $f wff ch $.
	f3_barbara $f set x $.
	e0_barbara $e |- A. x ( ph -> ps ) $.
	e1_barbara $e |- A. x ( ch -> ph ) $.
	p_barbara $p |- A. x ( ch -> ps ) $= e1_barbara e0_barbara f2_barbara f0_barbara f1_barbara f3_barbara p_alsyl f2_barbara f0_barbara a_wi f3_barbara a_wal f0_barbara f1_barbara a_wi f3_barbara a_wal f2_barbara f1_barbara a_wi f3_barbara a_wal p_mp2an $.
$}

$(Major premise for the Aristotelian syllogism "Celarent", e.g.,
       "No reptiles have fur". $)

$(Minor premise for Celarent, e.g., "All snakes are reptiles". $)

$("Celarent", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ph ` , therefore no ` ch ` is ` ps ` .  (In
       Aristotelian notation, EAE-1:  MeP and SaM therefore SeP.) For example,
       given the "No reptiles have fur" and "All snakes are reptiles",
       therefore "No snakes have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_celarent $f wff ph $.
	f1_celarent $f wff ps $.
	f2_celarent $f wff ch $.
	f3_celarent $f set x $.
	e0_celarent $e |- A. x ( ph -> -. ps ) $.
	e1_celarent $e |- A. x ( ch -> ph ) $.
	p_celarent $p |- A. x ( ch -> -. ps ) $= e0_celarent e1_celarent f0_celarent f1_celarent a_wn f2_celarent f3_celarent p_barbara $.
$}

$(Major premise for the Aristotelian syllogism "Darii", e.g.,
       "All rabbits have fur". $)

$(Minor premise for Darii, e.g., "Some pets are rabbits." $)

$("Darii", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-1:  MaP and SiM therefore SiP.) For
       example, given "All rabbits have fur" and "Some pets are rabbits",
       therefore "Some pets have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_darii $f wff ph $.
	f1_darii $f wff ps $.
	f2_darii $f wff ch $.
	f3_darii $f set x $.
	e0_darii $e |- A. x ( ph -> ps ) $.
	e1_darii $e |- E. x ( ch /\ ph ) $.
	p_darii $p |- E. x ( ch /\ ps ) $= e1_darii e0_darii f0_darii f1_darii a_wi f3_darii p_spi f0_darii f1_darii f2_darii p_anim2i f2_darii f0_darii a_wa f2_darii f1_darii a_wa f3_darii p_eximi f2_darii f0_darii a_wa f3_darii a_wex f2_darii f1_darii a_wa f3_darii a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Ferio" ("Ferioque"),
       e.g., "No homework is fun". $)

$(Minor premise for Ferio, e.g., "Some reading is homework." $)

$("Ferio" ("Ferioque"), one of the syllogisms of Aristotelian logic.  No
       ` ph ` is ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is
       not ` ps ` .  (In Aristotelian notation, EIO-1:  MeP and SiM therefore
       SoP.) For example, given "No homework is fun" and "Some reading is
       homework", therefore "Some reading is not fun".  This is essentially a
       logical axiom in Aristotelian logic.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_ferio $f wff ph $.
	f1_ferio $f wff ps $.
	f2_ferio $f wff ch $.
	f3_ferio $f set x $.
	e0_ferio $e |- A. x ( ph -> -. ps ) $.
	e1_ferio $e |- E. x ( ch /\ ph ) $.
	p_ferio $p |- E. x ( ch /\ -. ps ) $= e0_ferio e1_ferio f0_ferio f1_ferio a_wn f2_ferio f3_ferio p_darii $.
$}

$(Major premise for the Aristotelian syllogism "Barbari", e.g.,
       e.g., "All men are mortal". $)

$(Minor premise for Barbari, e.g., "All Greeks are men." $)

$(Existence premise for Barbari, e.g., "Greeks exist." $)

$("Barbari", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-1:  MaP and SaM
       therefore SiP.) For example, given "All men are mortal", "All Greeks are
       men", and "Greeks exist", therefore "Some Greeks are mortal".  Note the
       existence hypothesis (to prove the "some" in the conclusion).  Example
       from ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David
       A. Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler,
       30-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_barbari $f wff ph $.
	f1_barbari $f wff ps $.
	f2_barbari $f wff ch $.
	f3_barbari $f set x $.
	e0_barbari $e |- A. x ( ph -> ps ) $.
	e1_barbari $e |- A. x ( ch -> ph ) $.
	e2_barbari $e |- E. x ch $.
	p_barbari $p |- E. x ( ch /\ ps ) $= e2_barbari e0_barbari e1_barbari f0_barbari f1_barbari f2_barbari f3_barbari p_barbara f2_barbari f1_barbari a_wi f3_barbari p_spi f2_barbari f1_barbari p_ancli f2_barbari f2_barbari f1_barbari a_wa f3_barbari p_eximi f2_barbari f3_barbari a_wex f2_barbari f1_barbari a_wa f3_barbari a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Celaront", e.g.,
       e.g., "No reptiles have fur". $)

$(Minor premise for Celaront, e.g., "All Snakes are reptiles." $)

$(Existence premise for Celaront, e.g., "Snakes exist." $)

$("Celaront", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-1:  MeP and SaM
       therefore SoP.) For example, given "No reptiles have fur", "All snakes
       are reptiles.", and "Snakes exist.", prove "Some snakes have no fur".
       Note the existence hypothesis.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_celaront $f wff ph $.
	f1_celaront $f wff ps $.
	f2_celaront $f wff ch $.
	f3_celaront $f set x $.
	e0_celaront $e |- A. x ( ph -> -. ps ) $.
	e1_celaront $e |- A. x ( ch -> ph ) $.
	e2_celaront $e |- E. x ch $.
	p_celaront $p |- E. x ( ch /\ -. ps ) $= e0_celaront e1_celaront e2_celaront f0_celaront f1_celaront a_wn f2_celaront f3_celaront p_barbari $.
$}

$(Figure 2 $)

$(Major premise for the Aristotelian syllogism "Cesare" $)

$(Minor premise for Cesare $)

$("Cesare", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, EAE-2:  PeM and SaM therefore SeP.) Related to
       ~ celarent .  (Contributed by David A. Wheeler, 27-Aug-2016.)  (Revised
       by David A. Wheeler, 13-Nov-2016.) $)

${
	$v ph ps ch x  $.
	f0_cesare $f wff ph $.
	f1_cesare $f wff ps $.
	f2_cesare $f wff ch $.
	f3_cesare $f set x $.
	e0_cesare $e |- A. x ( ph -> -. ps ) $.
	e1_cesare $e |- A. x ( ch -> ps ) $.
	p_cesare $p |- A. x ( ch -> -. ph ) $= e0_cesare f0_cesare f1_cesare a_wn a_wi f3_cesare p_spi e1_cesare f2_cesare f1_cesare a_wi f3_cesare p_spi f0_cesare f1_cesare f2_cesare p_nsyl3 f2_cesare f0_cesare a_wn a_wi f3_cesare a_ax-gen $.
$}

$(Major premise for the Aristotelian syllogism "Camestres" $)

$(Minor premise for Camestres $)

$("Camestres", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-2:  PaM and SeM therefore SeP.) (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_camestres $f wff ph $.
	f1_camestres $f wff ps $.
	f2_camestres $f wff ch $.
	f3_camestres $f set x $.
	e0_camestres $e |- A. x ( ph -> ps ) $.
	e1_camestres $e |- A. x ( ch -> -. ps ) $.
	p_camestres $p |- A. x ( ch -> -. ph ) $= e1_camestres f2_camestres f1_camestres a_wn a_wi f3_camestres p_spi e0_camestres f0_camestres f1_camestres a_wi f3_camestres p_spi f2_camestres f1_camestres f0_camestres p_nsyl f2_camestres f0_camestres a_wn a_wi f3_camestres a_ax-gen $.
$}

$(Major premise for the Aristotelian syllogism "Festino" $)

$(Minor premise for Festino $)

$("Festino", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ch ` is ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, EIO-2:  PeM and SiM therefore SoP.)
       (Contributed by David A. Wheeler, 25-Nov-2016.) $)

${
	$v ph ps ch x  $.
	f0_festino $f wff ph $.
	f1_festino $f wff ps $.
	f2_festino $f wff ch $.
	f3_festino $f set x $.
	e0_festino $e |- A. x ( ph -> -. ps ) $.
	e1_festino $e |- E. x ( ch /\ ps ) $.
	p_festino $p |- E. x ( ch /\ -. ph ) $= e1_festino e0_festino f0_festino f1_festino a_wn a_wi f3_festino p_spi f0_festino f1_festino p_con2i f1_festino f0_festino a_wn f2_festino p_anim2i f2_festino f1_festino a_wa f2_festino f0_festino a_wn a_wa f3_festino p_eximi f2_festino f1_festino a_wa f3_festino a_wex f2_festino f0_festino a_wn a_wa f3_festino a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Baroco" $)

$(Minor premise for Baroco $)

$("Baroco", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is not ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, AOO-2:  PaM and SoM therefore SoP.)
       For example, "All informative things are useful", "Some websites are not
       useful", therefore "Some websites are not informative."  (Contributed by
       David A. Wheeler, 28-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_baroco $f wff ph $.
	f1_baroco $f wff ps $.
	f2_baroco $f wff ch $.
	f3_baroco $f set x $.
	e0_baroco $e |- A. x ( ph -> ps ) $.
	e1_baroco $e |- E. x ( ch /\ -. ps ) $.
	p_baroco $p |- E. x ( ch /\ -. ph ) $= e1_baroco e0_baroco f0_baroco f1_baroco a_wi f3_baroco p_spi f0_baroco f1_baroco p_con3i f1_baroco a_wn f0_baroco a_wn f2_baroco p_anim2i f2_baroco f1_baroco a_wn a_wa f2_baroco f0_baroco a_wn a_wa f3_baroco p_eximi f2_baroco f1_baroco a_wn a_wa f3_baroco a_wex f2_baroco f0_baroco a_wn a_wa f3_baroco a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Cesaro" $)

$(Minor premise for Cesaro $)

$(Existence premise for Cesaro $)

$("Cesaro", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, EAO-2:  PeM and SaM
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_cesaro $f wff ph $.
	f1_cesaro $f wff ps $.
	f2_cesaro $f wff ch $.
	f3_cesaro $f set x $.
	e0_cesaro $e |- A. x ( ph -> -. ps ) $.
	e1_cesaro $e |- A. x ( ch -> ps ) $.
	e2_cesaro $e |- E. x ch $.
	p_cesaro $p |- E. x ( ch /\ -. ph ) $= e2_cesaro e0_cesaro f0_cesaro f1_cesaro a_wn a_wi f3_cesaro p_spi e1_cesaro f2_cesaro f1_cesaro a_wi f3_cesaro p_spi f0_cesaro f1_cesaro f2_cesaro p_nsyl3 f2_cesaro f0_cesaro a_wn p_ancli f2_cesaro f2_cesaro f0_cesaro a_wn a_wa f3_cesaro p_eximi f2_cesaro f3_cesaro a_wex f2_cesaro f0_cesaro a_wn a_wa f3_cesaro a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Camestros" $)

$(Minor premise for  $)

$(Existence premise for Camestros $)

$("Camestros", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , no ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, AEO-2:  PaM and SeM
       therefore SoP.) For example, "All horses have hooves", "No humans have
       hooves", and humans exist, therefore "Some humans are not horses".
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_camestros $f wff ph $.
	f1_camestros $f wff ps $.
	f2_camestros $f wff ch $.
	f3_camestros $f set x $.
	e0_camestros $e |- A. x ( ph -> ps ) $.
	e1_camestros $e |- A. x ( ch -> -. ps ) $.
	e2_camestros $e |- E. x ch $.
	p_camestros $p |- E. x ( ch /\ -. ph ) $= e2_camestros e1_camestros f2_camestros f1_camestros a_wn a_wi f3_camestros p_spi e0_camestros f0_camestros f1_camestros a_wi f3_camestros p_spi f2_camestros f1_camestros f0_camestros p_nsyl f2_camestros f0_camestros a_wn p_ancli f2_camestros f2_camestros f0_camestros a_wn a_wa f3_camestros p_eximi f2_camestros f3_camestros a_wex f2_camestros f0_camestros a_wn a_wa f3_camestros a_wex a_ax-mp $.
$}

$(Figure 3 $)

$(Major premise for the Aristotelian syllogism "Datisi" $)

$(Minor premise for  $)

$("Datisi", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-3:  MaP and MiS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_datisi $f wff ph $.
	f1_datisi $f wff ps $.
	f2_datisi $f wff ch $.
	f3_datisi $f set x $.
	e0_datisi $e |- A. x ( ph -> ps ) $.
	e1_datisi $e |- E. x ( ph /\ ch ) $.
	p_datisi $p |- E. x ( ch /\ ps ) $= e1_datisi f0_datisi f2_datisi p_simpr e0_datisi f0_datisi f1_datisi a_wi f3_datisi p_spi f0_datisi f1_datisi f2_datisi p_adantr f0_datisi f2_datisi a_wa f2_datisi f1_datisi p_jca f0_datisi f2_datisi a_wa f2_datisi f1_datisi a_wa f3_datisi p_eximi f0_datisi f2_datisi a_wa f3_datisi a_wex f2_datisi f1_datisi a_wa f3_datisi a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Disamis" $)

$(Minor premise for  $)

$("Disamis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, IAI-3:  MiP and MaS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_disamis $f wff ph $.
	f1_disamis $f wff ps $.
	f2_disamis $f wff ch $.
	f3_disamis $f set x $.
	e0_disamis $e |- E. x ( ph /\ ps ) $.
	e1_disamis $e |- A. x ( ph -> ch ) $.
	p_disamis $p |- E. x ( ch /\ ps ) $= e0_disamis e1_disamis f0_disamis f2_disamis a_wi f3_disamis p_spi f0_disamis f2_disamis f1_disamis p_anim1i f0_disamis f1_disamis a_wa f2_disamis f1_disamis a_wa f3_disamis p_eximi f0_disamis f1_disamis a_wa f3_disamis a_wex f2_disamis f1_disamis a_wa f3_disamis a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Ferison" $)

$(Minor premise for  $)

$("Ferison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, EIO-3:  MeP and MiS therefore SoP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_ferison $f wff ph $.
	f1_ferison $f wff ps $.
	f2_ferison $f wff ch $.
	f3_ferison $f set x $.
	e0_ferison $e |- A. x ( ph -> -. ps ) $.
	e1_ferison $e |- E. x ( ph /\ ch ) $.
	p_ferison $p |- E. x ( ch /\ -. ps ) $= e0_ferison e1_ferison f0_ferison f1_ferison a_wn f2_ferison f3_ferison p_datisi $.
$}

$(Major premise for the Aristotelian syllogism "Bocardo" $)

$(Minor premise for  $)

$("Bocardo", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       not ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, OAO-3:  MoP and MaS therefore SoP.)
       For example, "Some cats have no tails", "All cats are mammals",
       therefore "Some mammals have no tails".  A reorder of ~ disamis ; prefer
       using that instead.  (Contributed by David A. Wheeler, 28-Aug-2016.)
       (New usage is discouraged.) $)

${
	$v ph ps ch x  $.
	f0_bocardo $f wff ph $.
	f1_bocardo $f wff ps $.
	f2_bocardo $f wff ch $.
	f3_bocardo $f set x $.
	e0_bocardo $e |- E. x ( ph /\ -. ps ) $.
	e1_bocardo $e |- A. x ( ph -> ch ) $.
	p_bocardo $p |- E. x ( ch /\ -. ps ) $= e0_bocardo e1_bocardo f0_bocardo f1_bocardo a_wn f2_bocardo f3_bocardo p_disamis $.
$}

$(Major premise for the Aristotelian syllogism "Felapton" $)

$(Minor premise for  $)

$(Existence premise for Felapton $)

$("Felapton", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-3:  MeP and MaS
       therefore SoP.) For example, "No flowers are animals" and "All flowers
       are plants", therefore "Some plants are not animals".  (Contributed by
       David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_felapton $f wff ph $.
	f1_felapton $f wff ps $.
	f2_felapton $f wff ch $.
	f3_felapton $f set x $.
	e0_felapton $e |- A. x ( ph -> -. ps ) $.
	e1_felapton $e |- A. x ( ph -> ch ) $.
	e2_felapton $e |- E. x ph $.
	p_felapton $p |- E. x ( ch /\ -. ps ) $= e2_felapton e1_felapton f0_felapton f2_felapton a_wi f3_felapton p_spi e0_felapton f0_felapton f1_felapton a_wn a_wi f3_felapton p_spi f0_felapton f2_felapton f1_felapton a_wn p_jca f0_felapton f2_felapton f1_felapton a_wn a_wa f3_felapton p_eximi f0_felapton f3_felapton a_wex f2_felapton f1_felapton a_wn a_wa f3_felapton a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Darapti" $)

$(Minor premise for  $)

$(Existence premise for Darapti $)

$("Darapti", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-3:  MaP and MaS
       therefore SiP.) For example, "All squares are rectangles" and "All
       squares are rhombuses", therefore "Some rhombuses are rectangles".
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_darapti $f wff ph $.
	f1_darapti $f wff ps $.
	f2_darapti $f wff ch $.
	f3_darapti $f set x $.
	e0_darapti $e |- A. x ( ph -> ps ) $.
	e1_darapti $e |- A. x ( ph -> ch ) $.
	e2_darapti $e |- E. x ph $.
	p_darapti $p |- E. x ( ch /\ ps ) $= e2_darapti e1_darapti f0_darapti f2_darapti a_wi f3_darapti p_spi e0_darapti f0_darapti f1_darapti a_wi f3_darapti p_spi f0_darapti f2_darapti f1_darapti p_jca f0_darapti f2_darapti f1_darapti a_wa f3_darapti p_eximi f0_darapti f3_darapti a_wex f2_darapti f1_darapti a_wa f3_darapti a_wex a_ax-mp $.
$}

$(Figure 4 $)

$(Major premise for the Aristotelian syllogism "Calemes" $)

$(Minor premise for  $)

$("Calemes", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ps ` is ` ch ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-4:  PaM and MeS therefore SeP.) (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_calemes $f wff ph $.
	f1_calemes $f wff ps $.
	f2_calemes $f wff ch $.
	f3_calemes $f set x $.
	e0_calemes $e |- A. x ( ph -> ps ) $.
	e1_calemes $e |- A. x ( ps -> -. ch ) $.
	p_calemes $p |- A. x ( ch -> -. ph ) $= e1_calemes f1_calemes f2_calemes a_wn a_wi f3_calemes p_spi f1_calemes f2_calemes p_con2i e0_calemes f0_calemes f1_calemes a_wi f3_calemes p_spi f2_calemes f1_calemes f0_calemes p_nsyl f2_calemes f0_calemes a_wn a_wi f3_calemes a_ax-gen $.
$}

$(Major premise for the Aristotelian syllogism "Dimatis" $)

$(Minor premise for  $)

$("Dimatis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ps ` is ` ch ` , therefore some ` ch ` is ` ph ` .
       (In Aristotelian notation, IAI-4:  PiM and MaS therefore SiP.) For
       example, "Some pets are rabbits.", "All rabbits have fur", therefore
       "Some fur bearing animals are pets".  Like ~ darii with positions
       interchanged.  (Contributed by David A. Wheeler, 28-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_dimatis $f wff ph $.
	f1_dimatis $f wff ps $.
	f2_dimatis $f wff ch $.
	f3_dimatis $f set x $.
	e0_dimatis $e |- E. x ( ph /\ ps ) $.
	e1_dimatis $e |- A. x ( ps -> ch ) $.
	p_dimatis $p |- E. x ( ch /\ ph ) $= e0_dimatis e1_dimatis f1_dimatis f2_dimatis a_wi f3_dimatis p_spi f1_dimatis f2_dimatis f0_dimatis p_adantl f0_dimatis f1_dimatis p_simpl f0_dimatis f1_dimatis a_wa f2_dimatis f0_dimatis p_jca f0_dimatis f1_dimatis a_wa f2_dimatis f0_dimatis a_wa f3_dimatis p_eximi f0_dimatis f1_dimatis a_wa f3_dimatis a_wex f2_dimatis f0_dimatis a_wa f3_dimatis a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Fresison" $)

$(Minor premise for  $)

$("Fresison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` (PeM), and some ` ps ` is ` ch ` (MiS), therefore some ` ch ` is
       not ` ph ` (SoP).  (In Aristotelian notation, EIO-4:  PeM and MiS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_fresison $f wff ph $.
	f1_fresison $f wff ps $.
	f2_fresison $f wff ch $.
	f3_fresison $f set x $.
	e0_fresison $e |- A. x ( ph -> -. ps ) $.
	e1_fresison $e |- E. x ( ps /\ ch ) $.
	p_fresison $p |- E. x ( ch /\ -. ph ) $= e1_fresison f1_fresison f2_fresison p_simpr e0_fresison f0_fresison f1_fresison a_wn a_wi f3_fresison p_spi f0_fresison f1_fresison p_con2i f1_fresison f0_fresison a_wn f2_fresison p_adantr f1_fresison f2_fresison a_wa f2_fresison f0_fresison a_wn p_jca f1_fresison f2_fresison a_wa f2_fresison f0_fresison a_wn a_wa f3_fresison p_eximi f1_fresison f2_fresison a_wa f3_fresison a_wex f2_fresison f0_fresison a_wn a_wa f3_fresison a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Calemos" $)

$(Minor premise for  $)

$(Existence premise for Calemos $)

$("Calemos", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` (PaM), no ` ps ` is ` ch ` (MeS), and ` ch ` exist, therefore
       some ` ch ` is not ` ph ` (SoP).  (In Aristotelian notation, AEO-4:  PaM
       and MeS therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_calemos $f wff ph $.
	f1_calemos $f wff ps $.
	f2_calemos $f wff ch $.
	f3_calemos $f set x $.
	e0_calemos $e |- A. x ( ph -> ps ) $.
	e1_calemos $e |- A. x ( ps -> -. ch ) $.
	e2_calemos $e |- E. x ch $.
	p_calemos $p |- E. x ( ch /\ -. ph ) $= e2_calemos e1_calemos f1_calemos f2_calemos a_wn a_wi f3_calemos p_spi f1_calemos f2_calemos p_con2i e0_calemos f0_calemos f1_calemos a_wi f3_calemos p_spi f2_calemos f1_calemos f0_calemos p_nsyl f2_calemos f0_calemos a_wn p_ancli f2_calemos f2_calemos f0_calemos a_wn a_wa f3_calemos p_eximi f2_calemos f3_calemos a_wex f2_calemos f0_calemos a_wn a_wa f3_calemos a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Fesapo" $)

$(Minor premise for  $)

$(Existence premise for Fesapo $)

$("Fesapo", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ps ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, EAO-4:  PeM and MaS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_fesapo $f wff ph $.
	f1_fesapo $f wff ps $.
	f2_fesapo $f wff ch $.
	f3_fesapo $f set x $.
	e0_fesapo $e |- A. x ( ph -> -. ps ) $.
	e1_fesapo $e |- A. x ( ps -> ch ) $.
	e2_fesapo $e |- E. x ps $.
	p_fesapo $p |- E. x ( ch /\ -. ph ) $= e2_fesapo e1_fesapo f1_fesapo f2_fesapo a_wi f3_fesapo p_spi e0_fesapo f0_fesapo f1_fesapo a_wn a_wi f3_fesapo p_spi f0_fesapo f1_fesapo p_con2i f1_fesapo f2_fesapo f0_fesapo a_wn p_jca f1_fesapo f2_fesapo f0_fesapo a_wn a_wa f3_fesapo p_eximi f1_fesapo f3_fesapo a_wex f2_fesapo f0_fesapo a_wn a_wa f3_fesapo a_wex a_ax-mp $.
$}

$(Major premise for the Aristotelian syllogism "Bamalip" $)

$(Minor premise for  $)

$(Existence premise for Bamalip $)

$("Bamalip", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ph ` exist, therefore some ` ch `
       is ` ph ` .  (In Aristotelian notation, AAI-4:  PaM and MaS therefore
       SiP.) Like ~ barbari .  (Contributed by David A. Wheeler,
       28-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_bamalip $f wff ph $.
	f1_bamalip $f wff ps $.
	f2_bamalip $f wff ch $.
	f3_bamalip $f set x $.
	e0_bamalip $e |- A. x ( ph -> ps ) $.
	e1_bamalip $e |- A. x ( ps -> ch ) $.
	e2_bamalip $e |- E. x ph $.
	p_bamalip $p |- E. x ( ch /\ ph ) $= e2_bamalip e0_bamalip f0_bamalip f1_bamalip a_wi f3_bamalip p_spi e1_bamalip f1_bamalip f2_bamalip a_wi f3_bamalip p_spi f0_bamalip f1_bamalip f2_bamalip p_syl f0_bamalip f2_bamalip p_ancri f0_bamalip f2_bamalip f0_bamalip a_wa f3_bamalip p_eximi f0_bamalip f3_bamalip a_wex f2_bamalip f0_bamalip a_wa f3_bamalip a_wex a_ax-mp $.
$}


