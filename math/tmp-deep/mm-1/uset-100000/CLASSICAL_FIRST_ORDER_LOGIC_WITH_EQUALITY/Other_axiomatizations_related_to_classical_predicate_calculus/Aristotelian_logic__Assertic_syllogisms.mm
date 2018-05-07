$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_related_to_classical_predicate_calculus/Predicate_calculus_with_all_distinct_variables.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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
$( Figure 1.  Aristotelian syllogisms are grouped by "figures",
     which doesn't matter for our purposes but is a reasonable way
     to order them. $)
$( Major premise for the Aristotelian syllogism "Barbara", e.g.,
       "All men are mortal". By convention, the major premise is first. $)
$( Minor premise for Barbara, e.g., "Socrates is a man". $)
$( "Barbara", one of the fundamental syllogisms of Aristotelian logic.  All
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
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fbarbara_0 $f wff ph $.
	fbarbara_1 $f wff ps $.
	fbarbara_2 $f wff ch $.
	fbarbara_3 $f set x $.
	ebarbara_0 $e |- A. x ( ph -> ps ) $.
	ebarbara_1 $e |- A. x ( ch -> ph ) $.
	barbara $p |- A. x ( ch -> ps ) $= fbarbara_2 fbarbara_0 wi fbarbara_3 wal fbarbara_0 fbarbara_1 wi fbarbara_3 wal fbarbara_2 fbarbara_1 wi fbarbara_3 wal ebarbara_1 ebarbara_0 fbarbara_2 fbarbara_0 fbarbara_1 fbarbara_3 alsyl mp2an $.
$}
$( Major premise for the Aristotelian syllogism "Celarent", e.g.,
       "No reptiles have fur". $)
$( Minor premise for Celarent, e.g., "All snakes are reptiles". $)
$( "Celarent", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ph ` , therefore no ` ch ` is ` ps ` .  (In
       Aristotelian notation, EAE-1:  MeP and SaM therefore SeP.) For example,
       given the "No reptiles have fur" and "All snakes are reptiles",
       therefore "No snakes have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fcelarent_0 $f wff ph $.
	fcelarent_1 $f wff ps $.
	fcelarent_2 $f wff ch $.
	fcelarent_3 $f set x $.
	ecelarent_0 $e |- A. x ( ph -> -. ps ) $.
	ecelarent_1 $e |- A. x ( ch -> ph ) $.
	celarent $p |- A. x ( ch -> -. ps ) $= fcelarent_0 fcelarent_1 wn fcelarent_2 fcelarent_3 ecelarent_0 ecelarent_1 barbara $.
$}
$( Major premise for the Aristotelian syllogism "Darii", e.g.,
       "All rabbits have fur". $)
$( Minor premise for Darii, e.g., "Some pets are rabbits." $)
$( "Darii", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-1:  MaP and SiM therefore SiP.) For
       example, given "All rabbits have fur" and "Some pets are rabbits",
       therefore "Some pets have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fdarii_0 $f wff ph $.
	fdarii_1 $f wff ps $.
	fdarii_2 $f wff ch $.
	fdarii_3 $f set x $.
	edarii_0 $e |- A. x ( ph -> ps ) $.
	edarii_1 $e |- E. x ( ch /\ ph ) $.
	darii $p |- E. x ( ch /\ ps ) $= fdarii_2 fdarii_0 wa fdarii_3 wex fdarii_2 fdarii_1 wa fdarii_3 wex edarii_1 fdarii_2 fdarii_0 wa fdarii_2 fdarii_1 wa fdarii_3 fdarii_0 fdarii_1 fdarii_2 fdarii_0 fdarii_1 wi fdarii_3 edarii_0 spi anim2i eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Ferio" ("Ferioque"),
       e.g., "No homework is fun". $)
$( Minor premise for Ferio, e.g., "Some reading is homework." $)
$( "Ferio" ("Ferioque"), one of the syllogisms of Aristotelian logic.  No
       ` ph ` is ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is
       not ` ps ` .  (In Aristotelian notation, EIO-1:  MeP and SiM therefore
       SoP.) For example, given "No homework is fun" and "Some reading is
       homework", therefore "Some reading is not fun".  This is essentially a
       logical axiom in Aristotelian logic.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fferio_0 $f wff ph $.
	fferio_1 $f wff ps $.
	fferio_2 $f wff ch $.
	fferio_3 $f set x $.
	eferio_0 $e |- A. x ( ph -> -. ps ) $.
	eferio_1 $e |- E. x ( ch /\ ph ) $.
	ferio $p |- E. x ( ch /\ -. ps ) $= fferio_0 fferio_1 wn fferio_2 fferio_3 eferio_0 eferio_1 darii $.
$}
$( Major premise for the Aristotelian syllogism "Barbari", e.g.,
       e.g., "All men are mortal". $)
$( Minor premise for Barbari, e.g., "All Greeks are men." $)
$( Existence premise for Barbari, e.g., "Greeks exist." $)
$( "Barbari", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-1:  MaP and SaM
       therefore SiP.) For example, given "All men are mortal", "All Greeks are
       men", and "Greeks exist", therefore "Some Greeks are mortal".  Note the
       existence hypothesis (to prove the "some" in the conclusion).  Example
       from ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David
       A. Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler,
       30-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fbarbari_0 $f wff ph $.
	fbarbari_1 $f wff ps $.
	fbarbari_2 $f wff ch $.
	fbarbari_3 $f set x $.
	ebarbari_0 $e |- A. x ( ph -> ps ) $.
	ebarbari_1 $e |- A. x ( ch -> ph ) $.
	ebarbari_2 $e |- E. x ch $.
	barbari $p |- E. x ( ch /\ ps ) $= fbarbari_2 fbarbari_3 wex fbarbari_2 fbarbari_1 wa fbarbari_3 wex ebarbari_2 fbarbari_2 fbarbari_2 fbarbari_1 wa fbarbari_3 fbarbari_2 fbarbari_1 fbarbari_2 fbarbari_1 wi fbarbari_3 fbarbari_0 fbarbari_1 fbarbari_2 fbarbari_3 ebarbari_0 ebarbari_1 barbara spi ancli eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Celaront", e.g.,
       e.g., "No reptiles have fur". $)
$( Minor premise for Celaront, e.g., "All Snakes are reptiles." $)
$( Existence premise for Celaront, e.g., "Snakes exist." $)
$( "Celaront", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-1:  MeP and SaM
       therefore SoP.) For example, given "No reptiles have fur", "All snakes
       are reptiles.", and "Snakes exist.", prove "Some snakes have no fur".
       Note the existence hypothesis.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fcelaront_0 $f wff ph $.
	fcelaront_1 $f wff ps $.
	fcelaront_2 $f wff ch $.
	fcelaront_3 $f set x $.
	ecelaront_0 $e |- A. x ( ph -> -. ps ) $.
	ecelaront_1 $e |- A. x ( ch -> ph ) $.
	ecelaront_2 $e |- E. x ch $.
	celaront $p |- E. x ( ch /\ -. ps ) $= fcelaront_0 fcelaront_1 wn fcelaront_2 fcelaront_3 ecelaront_0 ecelaront_1 ecelaront_2 barbari $.
$}
$( Figure 2 $)
$( Major premise for the Aristotelian syllogism "Cesare" $)
$( Minor premise for Cesare $)
$( "Cesare", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, EAE-2:  PeM and SaM therefore SeP.) Related to
       ~ celarent .  (Contributed by David A. Wheeler, 27-Aug-2016.)  (Revised
       by David A. Wheeler, 13-Nov-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fcesare_0 $f wff ph $.
	fcesare_1 $f wff ps $.
	fcesare_2 $f wff ch $.
	fcesare_3 $f set x $.
	ecesare_0 $e |- A. x ( ph -> -. ps ) $.
	ecesare_1 $e |- A. x ( ch -> ps ) $.
	cesare $p |- A. x ( ch -> -. ph ) $= fcesare_2 fcesare_0 wn wi fcesare_3 fcesare_0 fcesare_1 fcesare_2 fcesare_0 fcesare_1 wn wi fcesare_3 ecesare_0 spi fcesare_2 fcesare_1 wi fcesare_3 ecesare_1 spi nsyl3 ax-gen $.
$}
$( Major premise for the Aristotelian syllogism "Camestres" $)
$( Minor premise for Camestres $)
$( "Camestres", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-2:  PaM and SeM therefore SeP.) (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fcamestres_0 $f wff ph $.
	fcamestres_1 $f wff ps $.
	fcamestres_2 $f wff ch $.
	fcamestres_3 $f set x $.
	ecamestres_0 $e |- A. x ( ph -> ps ) $.
	ecamestres_1 $e |- A. x ( ch -> -. ps ) $.
	camestres $p |- A. x ( ch -> -. ph ) $= fcamestres_2 fcamestres_0 wn wi fcamestres_3 fcamestres_2 fcamestres_1 fcamestres_0 fcamestres_2 fcamestres_1 wn wi fcamestres_3 ecamestres_1 spi fcamestres_0 fcamestres_1 wi fcamestres_3 ecamestres_0 spi nsyl ax-gen $.
$}
$( Major premise for the Aristotelian syllogism "Festino" $)
$( Minor premise for Festino $)
$( "Festino", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ch ` is ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, EIO-2:  PeM and SiM therefore SoP.)
       (Contributed by David A. Wheeler, 25-Nov-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	ffestino_0 $f wff ph $.
	ffestino_1 $f wff ps $.
	ffestino_2 $f wff ch $.
	ffestino_3 $f set x $.
	efestino_0 $e |- A. x ( ph -> -. ps ) $.
	efestino_1 $e |- E. x ( ch /\ ps ) $.
	festino $p |- E. x ( ch /\ -. ph ) $= ffestino_2 ffestino_1 wa ffestino_3 wex ffestino_2 ffestino_0 wn wa ffestino_3 wex efestino_1 ffestino_2 ffestino_1 wa ffestino_2 ffestino_0 wn wa ffestino_3 ffestino_1 ffestino_0 wn ffestino_2 ffestino_0 ffestino_1 ffestino_0 ffestino_1 wn wi ffestino_3 efestino_0 spi con2i anim2i eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Baroco" $)
$( Minor premise for Baroco $)
$( "Baroco", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is not ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, AOO-2:  PaM and SoM therefore SoP.)
       For example, "All informative things are useful", "Some websites are not
       useful", therefore "Some websites are not informative."  (Contributed by
       David A. Wheeler, 28-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fbaroco_0 $f wff ph $.
	fbaroco_1 $f wff ps $.
	fbaroco_2 $f wff ch $.
	fbaroco_3 $f set x $.
	ebaroco_0 $e |- A. x ( ph -> ps ) $.
	ebaroco_1 $e |- E. x ( ch /\ -. ps ) $.
	baroco $p |- E. x ( ch /\ -. ph ) $= fbaroco_2 fbaroco_1 wn wa fbaroco_3 wex fbaroco_2 fbaroco_0 wn wa fbaroco_3 wex ebaroco_1 fbaroco_2 fbaroco_1 wn wa fbaroco_2 fbaroco_0 wn wa fbaroco_3 fbaroco_1 wn fbaroco_0 wn fbaroco_2 fbaroco_0 fbaroco_1 fbaroco_0 fbaroco_1 wi fbaroco_3 ebaroco_0 spi con3i anim2i eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Cesaro" $)
$( Minor premise for Cesaro $)
$( Existence premise for Cesaro $)
$( "Cesaro", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, EAO-2:  PeM and SaM
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fcesaro_0 $f wff ph $.
	fcesaro_1 $f wff ps $.
	fcesaro_2 $f wff ch $.
	fcesaro_3 $f set x $.
	ecesaro_0 $e |- A. x ( ph -> -. ps ) $.
	ecesaro_1 $e |- A. x ( ch -> ps ) $.
	ecesaro_2 $e |- E. x ch $.
	cesaro $p |- E. x ( ch /\ -. ph ) $= fcesaro_2 fcesaro_3 wex fcesaro_2 fcesaro_0 wn wa fcesaro_3 wex ecesaro_2 fcesaro_2 fcesaro_2 fcesaro_0 wn wa fcesaro_3 fcesaro_2 fcesaro_0 wn fcesaro_0 fcesaro_1 fcesaro_2 fcesaro_0 fcesaro_1 wn wi fcesaro_3 ecesaro_0 spi fcesaro_2 fcesaro_1 wi fcesaro_3 ecesaro_1 spi nsyl3 ancli eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Camestros" $)
$( Minor premise for  $)
$( Existence premise for Camestros $)
$( "Camestros", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , no ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, AEO-2:  PaM and SeM
       therefore SoP.) For example, "All horses have hooves", "No humans have
       hooves", and humans exist, therefore "Some humans are not horses".
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fcamestros_0 $f wff ph $.
	fcamestros_1 $f wff ps $.
	fcamestros_2 $f wff ch $.
	fcamestros_3 $f set x $.
	ecamestros_0 $e |- A. x ( ph -> ps ) $.
	ecamestros_1 $e |- A. x ( ch -> -. ps ) $.
	ecamestros_2 $e |- E. x ch $.
	camestros $p |- E. x ( ch /\ -. ph ) $= fcamestros_2 fcamestros_3 wex fcamestros_2 fcamestros_0 wn wa fcamestros_3 wex ecamestros_2 fcamestros_2 fcamestros_2 fcamestros_0 wn wa fcamestros_3 fcamestros_2 fcamestros_0 wn fcamestros_2 fcamestros_1 fcamestros_0 fcamestros_2 fcamestros_1 wn wi fcamestros_3 ecamestros_1 spi fcamestros_0 fcamestros_1 wi fcamestros_3 ecamestros_0 spi nsyl ancli eximi ax-mp $.
$}
$( Figure 3 $)
$( Major premise for the Aristotelian syllogism "Datisi" $)
$( Minor premise for  $)
$( "Datisi", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-3:  MaP and MiS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fdatisi_0 $f wff ph $.
	fdatisi_1 $f wff ps $.
	fdatisi_2 $f wff ch $.
	fdatisi_3 $f set x $.
	edatisi_0 $e |- A. x ( ph -> ps ) $.
	edatisi_1 $e |- E. x ( ph /\ ch ) $.
	datisi $p |- E. x ( ch /\ ps ) $= fdatisi_0 fdatisi_2 wa fdatisi_3 wex fdatisi_2 fdatisi_1 wa fdatisi_3 wex edatisi_1 fdatisi_0 fdatisi_2 wa fdatisi_2 fdatisi_1 wa fdatisi_3 fdatisi_0 fdatisi_2 wa fdatisi_2 fdatisi_1 fdatisi_0 fdatisi_2 simpr fdatisi_0 fdatisi_1 fdatisi_2 fdatisi_0 fdatisi_1 wi fdatisi_3 edatisi_0 spi adantr jca eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Disamis" $)
$( Minor premise for  $)
$( "Disamis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, IAI-3:  MiP and MaS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fdisamis_0 $f wff ph $.
	fdisamis_1 $f wff ps $.
	fdisamis_2 $f wff ch $.
	fdisamis_3 $f set x $.
	edisamis_0 $e |- E. x ( ph /\ ps ) $.
	edisamis_1 $e |- A. x ( ph -> ch ) $.
	disamis $p |- E. x ( ch /\ ps ) $= fdisamis_0 fdisamis_1 wa fdisamis_3 wex fdisamis_2 fdisamis_1 wa fdisamis_3 wex edisamis_0 fdisamis_0 fdisamis_1 wa fdisamis_2 fdisamis_1 wa fdisamis_3 fdisamis_0 fdisamis_2 fdisamis_1 fdisamis_0 fdisamis_2 wi fdisamis_3 edisamis_1 spi anim1i eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Ferison" $)
$( Minor premise for  $)
$( "Ferison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, EIO-3:  MeP and MiS therefore SoP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fferison_0 $f wff ph $.
	fferison_1 $f wff ps $.
	fferison_2 $f wff ch $.
	fferison_3 $f set x $.
	eferison_0 $e |- A. x ( ph -> -. ps ) $.
	eferison_1 $e |- E. x ( ph /\ ch ) $.
	ferison $p |- E. x ( ch /\ -. ps ) $= fferison_0 fferison_1 wn fferison_2 fferison_3 eferison_0 eferison_1 datisi $.
$}
$( Major premise for the Aristotelian syllogism "Bocardo" $)
$( Minor premise for  $)
$( "Bocardo", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       not ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, OAO-3:  MoP and MaS therefore SoP.)
       For example, "Some cats have no tails", "All cats are mammals",
       therefore "Some mammals have no tails".  A reorder of ~ disamis ; prefer
       using that instead.  (Contributed by David A. Wheeler, 28-Aug-2016.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fbocardo_0 $f wff ph $.
	fbocardo_1 $f wff ps $.
	fbocardo_2 $f wff ch $.
	fbocardo_3 $f set x $.
	ebocardo_0 $e |- E. x ( ph /\ -. ps ) $.
	ebocardo_1 $e |- A. x ( ph -> ch ) $.
	bocardo $p |- E. x ( ch /\ -. ps ) $= fbocardo_0 fbocardo_1 wn fbocardo_2 fbocardo_3 ebocardo_0 ebocardo_1 disamis $.
$}
$( Major premise for the Aristotelian syllogism "Felapton" $)
$( Minor premise for  $)
$( Existence premise for Felapton $)
$( "Felapton", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-3:  MeP and MaS
       therefore SoP.) For example, "No flowers are animals" and "All flowers
       are plants", therefore "Some plants are not animals".  (Contributed by
       David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	ffelapton_0 $f wff ph $.
	ffelapton_1 $f wff ps $.
	ffelapton_2 $f wff ch $.
	ffelapton_3 $f set x $.
	efelapton_0 $e |- A. x ( ph -> -. ps ) $.
	efelapton_1 $e |- A. x ( ph -> ch ) $.
	efelapton_2 $e |- E. x ph $.
	felapton $p |- E. x ( ch /\ -. ps ) $= ffelapton_0 ffelapton_3 wex ffelapton_2 ffelapton_1 wn wa ffelapton_3 wex efelapton_2 ffelapton_0 ffelapton_2 ffelapton_1 wn wa ffelapton_3 ffelapton_0 ffelapton_2 ffelapton_1 wn ffelapton_0 ffelapton_2 wi ffelapton_3 efelapton_1 spi ffelapton_0 ffelapton_1 wn wi ffelapton_3 efelapton_0 spi jca eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Darapti" $)
$( Minor premise for  $)
$( Existence premise for Darapti $)
$( "Darapti", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-3:  MaP and MaS
       therefore SiP.) For example, "All squares are rectangles" and "All
       squares are rhombuses", therefore "Some rhombuses are rectangles".
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fdarapti_0 $f wff ph $.
	fdarapti_1 $f wff ps $.
	fdarapti_2 $f wff ch $.
	fdarapti_3 $f set x $.
	edarapti_0 $e |- A. x ( ph -> ps ) $.
	edarapti_1 $e |- A. x ( ph -> ch ) $.
	edarapti_2 $e |- E. x ph $.
	darapti $p |- E. x ( ch /\ ps ) $= fdarapti_0 fdarapti_3 wex fdarapti_2 fdarapti_1 wa fdarapti_3 wex edarapti_2 fdarapti_0 fdarapti_2 fdarapti_1 wa fdarapti_3 fdarapti_0 fdarapti_2 fdarapti_1 fdarapti_0 fdarapti_2 wi fdarapti_3 edarapti_1 spi fdarapti_0 fdarapti_1 wi fdarapti_3 edarapti_0 spi jca eximi ax-mp $.
$}
$( Figure 4 $)
$( Major premise for the Aristotelian syllogism "Calemes" $)
$( Minor premise for  $)
$( "Calemes", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ps ` is ` ch ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-4:  PaM and MeS therefore SeP.) (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fcalemes_0 $f wff ph $.
	fcalemes_1 $f wff ps $.
	fcalemes_2 $f wff ch $.
	fcalemes_3 $f set x $.
	ecalemes_0 $e |- A. x ( ph -> ps ) $.
	ecalemes_1 $e |- A. x ( ps -> -. ch ) $.
	calemes $p |- A. x ( ch -> -. ph ) $= fcalemes_2 fcalemes_0 wn wi fcalemes_3 fcalemes_2 fcalemes_1 fcalemes_0 fcalemes_1 fcalemes_2 fcalemes_1 fcalemes_2 wn wi fcalemes_3 ecalemes_1 spi con2i fcalemes_0 fcalemes_1 wi fcalemes_3 ecalemes_0 spi nsyl ax-gen $.
$}
$( Major premise for the Aristotelian syllogism "Dimatis" $)
$( Minor premise for  $)
$( "Dimatis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ps ` is ` ch ` , therefore some ` ch ` is ` ph ` .
       (In Aristotelian notation, IAI-4:  PiM and MaS therefore SiP.) For
       example, "Some pets are rabbits.", "All rabbits have fur", therefore
       "Some fur bearing animals are pets".  Like ~ darii with positions
       interchanged.  (Contributed by David A. Wheeler, 28-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fdimatis_0 $f wff ph $.
	fdimatis_1 $f wff ps $.
	fdimatis_2 $f wff ch $.
	fdimatis_3 $f set x $.
	edimatis_0 $e |- E. x ( ph /\ ps ) $.
	edimatis_1 $e |- A. x ( ps -> ch ) $.
	dimatis $p |- E. x ( ch /\ ph ) $= fdimatis_0 fdimatis_1 wa fdimatis_3 wex fdimatis_2 fdimatis_0 wa fdimatis_3 wex edimatis_0 fdimatis_0 fdimatis_1 wa fdimatis_2 fdimatis_0 wa fdimatis_3 fdimatis_0 fdimatis_1 wa fdimatis_2 fdimatis_0 fdimatis_1 fdimatis_2 fdimatis_0 fdimatis_1 fdimatis_2 wi fdimatis_3 edimatis_1 spi adantl fdimatis_0 fdimatis_1 simpl jca eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Fresison" $)
$( Minor premise for  $)
$( "Fresison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` (PeM), and some ` ps ` is ` ch ` (MiS), therefore some ` ch ` is
       not ` ph ` (SoP).  (In Aristotelian notation, EIO-4:  PeM and MiS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	ffresison_0 $f wff ph $.
	ffresison_1 $f wff ps $.
	ffresison_2 $f wff ch $.
	ffresison_3 $f set x $.
	efresison_0 $e |- A. x ( ph -> -. ps ) $.
	efresison_1 $e |- E. x ( ps /\ ch ) $.
	fresison $p |- E. x ( ch /\ -. ph ) $= ffresison_1 ffresison_2 wa ffresison_3 wex ffresison_2 ffresison_0 wn wa ffresison_3 wex efresison_1 ffresison_1 ffresison_2 wa ffresison_2 ffresison_0 wn wa ffresison_3 ffresison_1 ffresison_2 wa ffresison_2 ffresison_0 wn ffresison_1 ffresison_2 simpr ffresison_1 ffresison_0 wn ffresison_2 ffresison_0 ffresison_1 ffresison_0 ffresison_1 wn wi ffresison_3 efresison_0 spi con2i adantr jca eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Calemos" $)
$( Minor premise for  $)
$( Existence premise for Calemos $)
$( "Calemos", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` (PaM), no ` ps ` is ` ch ` (MeS), and ` ch ` exist, therefore
       some ` ch ` is not ` ph ` (SoP).  (In Aristotelian notation, AEO-4:  PaM
       and MeS therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fcalemos_0 $f wff ph $.
	fcalemos_1 $f wff ps $.
	fcalemos_2 $f wff ch $.
	fcalemos_3 $f set x $.
	ecalemos_0 $e |- A. x ( ph -> ps ) $.
	ecalemos_1 $e |- A. x ( ps -> -. ch ) $.
	ecalemos_2 $e |- E. x ch $.
	calemos $p |- E. x ( ch /\ -. ph ) $= fcalemos_2 fcalemos_3 wex fcalemos_2 fcalemos_0 wn wa fcalemos_3 wex ecalemos_2 fcalemos_2 fcalemos_2 fcalemos_0 wn wa fcalemos_3 fcalemos_2 fcalemos_0 wn fcalemos_2 fcalemos_1 fcalemos_0 fcalemos_1 fcalemos_2 fcalemos_1 fcalemos_2 wn wi fcalemos_3 ecalemos_1 spi con2i fcalemos_0 fcalemos_1 wi fcalemos_3 ecalemos_0 spi nsyl ancli eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Fesapo" $)
$( Minor premise for  $)
$( Existence premise for Fesapo $)
$( "Fesapo", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ps ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, EAO-4:  PeM and MaS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	ffesapo_0 $f wff ph $.
	ffesapo_1 $f wff ps $.
	ffesapo_2 $f wff ch $.
	ffesapo_3 $f set x $.
	efesapo_0 $e |- A. x ( ph -> -. ps ) $.
	efesapo_1 $e |- A. x ( ps -> ch ) $.
	efesapo_2 $e |- E. x ps $.
	fesapo $p |- E. x ( ch /\ -. ph ) $= ffesapo_1 ffesapo_3 wex ffesapo_2 ffesapo_0 wn wa ffesapo_3 wex efesapo_2 ffesapo_1 ffesapo_2 ffesapo_0 wn wa ffesapo_3 ffesapo_1 ffesapo_2 ffesapo_0 wn ffesapo_1 ffesapo_2 wi ffesapo_3 efesapo_1 spi ffesapo_0 ffesapo_1 ffesapo_0 ffesapo_1 wn wi ffesapo_3 efesapo_0 spi con2i jca eximi ax-mp $.
$}
$( Major premise for the Aristotelian syllogism "Bamalip" $)
$( Minor premise for  $)
$( Existence premise for Bamalip $)
$( "Bamalip", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ph ` exist, therefore some ` ch `
       is ` ph ` .  (In Aristotelian notation, AAI-4:  PaM and MaS therefore
       SiP.) Like ~ barbari .  (Contributed by David A. Wheeler,
       28-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fbamalip_0 $f wff ph $.
	fbamalip_1 $f wff ps $.
	fbamalip_2 $f wff ch $.
	fbamalip_3 $f set x $.
	ebamalip_0 $e |- A. x ( ph -> ps ) $.
	ebamalip_1 $e |- A. x ( ps -> ch ) $.
	ebamalip_2 $e |- E. x ph $.
	bamalip $p |- E. x ( ch /\ ph ) $= fbamalip_0 fbamalip_3 wex fbamalip_2 fbamalip_0 wa fbamalip_3 wex ebamalip_2 fbamalip_0 fbamalip_2 fbamalip_0 wa fbamalip_3 fbamalip_0 fbamalip_2 fbamalip_0 fbamalip_1 fbamalip_2 fbamalip_0 fbamalip_1 wi fbamalip_3 ebamalip_0 spi fbamalip_1 fbamalip_2 wi fbamalip_3 ebamalip_1 spi syl ancri eximi ax-mp $.
$}

