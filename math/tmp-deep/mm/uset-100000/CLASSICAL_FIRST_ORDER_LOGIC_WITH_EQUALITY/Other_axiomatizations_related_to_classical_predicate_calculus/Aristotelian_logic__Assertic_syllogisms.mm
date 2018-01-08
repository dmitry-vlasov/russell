
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_related_to_classical_predicate_calculus/Predicate_calculus_with_all_distinct_variables.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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

  ${
    $( Major premise for the Aristotelian syllogism "Barbara", e.g.,
       "All men are mortal". By convention, the major premise is first. $)
    barbara.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Barbara, e.g., "Socrates is a man". $)
    barbara.min $e |- A. x ( ch -> ph ) $.
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
    barbara $p |- A. x ( ch -> ps ) $=
      wch wph wi vx wal wph wps wi vx wal wch wps wi vx wal barbara.min
      barbara.maj wch wph wps vx alsyl mp2an $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Celarent", e.g.,
       "No reptiles have fur". $)
    celarent.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Celarent, e.g., "All snakes are reptiles". $)
    celarent.min $e |- A. x ( ch -> ph ) $.
    $( "Celarent", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ph ` , therefore no ` ch ` is ` ps ` .  (In
       Aristotelian notation, EAE-1:  MeP and SaM therefore SeP.) For example,
       given the "No reptiles have fur" and "All snakes are reptiles",
       therefore "No snakes have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    celarent $p |- A. x ( ch -> -. ps ) $=
      wph wps wn wch vx celarent.maj celarent.min barbara $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Darii", e.g.,
       "All rabbits have fur". $)
    darii.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Darii, e.g., "Some pets are rabbits." $)
    darii.min $e |- E. x ( ch /\ ph ) $.
    $( "Darii", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-1:  MaP and SiM therefore SiP.) For
       example, given "All rabbits have fur" and "Some pets are rabbits",
       therefore "Some pets have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
    darii $p |- E. x ( ch /\ ps ) $=
      wch wph wa vx wex wch wps wa vx wex darii.min wch wph wa wch wps wa vx
      wph wps wch wph wps wi vx darii.maj spi anim2i eximi ax-mp $.
  $}


  ${
    $( Major premise for the Aristotelian syllogism "Ferio" ("Ferioque"),
       e.g., "No homework is fun". $)
    ferio.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Ferio, e.g., "Some reading is homework." $)
    ferio.min $e |- E. x ( ch /\ ph ) $.
    $( "Ferio" ("Ferioque"), one of the syllogisms of Aristotelian logic.  No
       ` ph ` is ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is
       not ` ps ` .  (In Aristotelian notation, EIO-1:  MeP and SiM therefore
       SoP.) For example, given "No homework is fun" and "Some reading is
       homework", therefore "Some reading is not fun".  This is essentially a
       logical axiom in Aristotelian logic.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    ferio $p |- E. x ( ch /\ -. ps ) $=
      wph wps wn wch vx ferio.maj ferio.min darii $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Barbari", e.g.,
       e.g., "All men are mortal". $)
    barbari.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Barbari, e.g., "All Greeks are men." $)
    barbari.min $e |- A. x ( ch -> ph ) $.
    $( Existence premise for Barbari, e.g., "Greeks exist." $)
    barbari.e $e |- E. x ch $.
    $( "Barbari", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-1:  MaP and SaM
       therefore SiP.) For example, given "All men are mortal", "All Greeks are
       men", and "Greeks exist", therefore "Some Greeks are mortal".  Note the
       existence hypothesis (to prove the "some" in the conclusion).  Example
       from ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David
       A. Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler,
       30-Aug-2016.) $)
    barbari $p |- E. x ( ch /\ ps ) $=
      wch vx wex wch wps wa vx wex barbari.e wch wch wps wa vx wch wps wch wps
      wi vx wph wps wch vx barbari.maj barbari.min barbara spi ancli eximi
      ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Celaront", e.g.,
       e.g., "No reptiles have fur". $)
    celaront.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Celaront, e.g., "All Snakes are reptiles." $)
    celaront.min $e |- A. x ( ch -> ph ) $.
    $( Existence premise for Celaront, e.g., "Snakes exist." $)
    celaront.e $e |- E. x ch $.
    $( "Celaront", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-1:  MeP and SaM
       therefore SoP.) For example, given "No reptiles have fur", "All snakes
       are reptiles.", and "Snakes exist.", prove "Some snakes have no fur".
       Note the existence hypothesis.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    celaront $p |- E. x ( ch /\ -. ps ) $=
      wph wps wn wch vx celaront.maj celaront.min celaront.e barbari $.
  $}

  $( Figure 2 $)

  ${
    $( Major premise for the Aristotelian syllogism "Cesare" $)
    cesare.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Cesare $)
    cesare.min $e |- A. x ( ch -> ps ) $.
    $( "Cesare", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, EAE-2:  PeM and SaM therefore SeP.) Related to
       ~ celarent .  (Contributed by David A. Wheeler, 27-Aug-2016.)  (Revised
       by David A. Wheeler, 13-Nov-2016.) $)
    cesare $p |- A. x ( ch -> -. ph ) $=
      wch wph wn wi vx wph wps wch wph wps wn wi vx cesare.maj spi wch wps wi
      vx cesare.min spi nsyl3 ax-gen $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Camestres" $)
    camestres.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Camestres $)
    camestres.min $e |- A. x ( ch -> -. ps ) $.
    $( "Camestres", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-2:  PaM and SeM therefore SeP.) (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    camestres $p |- A. x ( ch -> -. ph ) $=
      wch wph wn wi vx wch wps wph wch wps wn wi vx camestres.min spi wph wps
      wi vx camestres.maj spi nsyl ax-gen $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Festino" $)
    festino.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Festino $)
    festino.min $e |- E. x ( ch /\ ps ) $.
    $( "Festino", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ch ` is ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, EIO-2:  PeM and SiM therefore SoP.)
       (Contributed by David A. Wheeler, 25-Nov-2016.) $)
    festino $p |- E. x ( ch /\ -. ph ) $=
      wch wps wa vx wex wch wph wn wa vx wex festino.min wch wps wa wch wph wn
      wa vx wps wph wn wch wph wps wph wps wn wi vx festino.maj spi con2i
      anim2i eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Baroco" $)
    baroco.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Baroco $)
    baroco.min $e |- E. x ( ch /\ -. ps ) $.
    $( "Baroco", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is not ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, AOO-2:  PaM and SoM therefore SoP.)
       For example, "All informative things are useful", "Some websites are not
       useful", therefore "Some websites are not informative."  (Contributed by
       David A. Wheeler, 28-Aug-2016.) $)
    baroco $p |- E. x ( ch /\ -. ph ) $=
      wch wps wn wa vx wex wch wph wn wa vx wex baroco.min wch wps wn wa wch
      wph wn wa vx wps wn wph wn wch wph wps wph wps wi vx baroco.maj spi con3i
      anim2i eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Cesaro" $)
    cesaro.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Cesaro $)
    cesaro.min $e |- A. x ( ch -> ps ) $.
    $( Existence premise for Cesaro $)
    cesaro.e $e |- E. x ch $.
    $( "Cesaro", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, EAO-2:  PeM and SaM
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    cesaro $p |- E. x ( ch /\ -. ph ) $=
      wch vx wex wch wph wn wa vx wex cesaro.e wch wch wph wn wa vx wch wph wn
      wph wps wch wph wps wn wi vx cesaro.maj spi wch wps wi vx cesaro.min spi
      nsyl3 ancli eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Camestros" $)
    camestros.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    camestros.min $e |- A. x ( ch -> -. ps ) $.
    $( Existence premise for Camestros $)
    camestros.e $e |- E. x ch $.
    $( "Camestros", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , no ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, AEO-2:  PaM and SeM
       therefore SoP.) For example, "All horses have hooves", "No humans have
       hooves", and humans exist, therefore "Some humans are not horses".
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)
    camestros $p |- E. x ( ch /\ -. ph ) $=
      wch vx wex wch wph wn wa vx wex camestros.e wch wch wph wn wa vx wch wph
      wn wch wps wph wch wps wn wi vx camestros.min spi wph wps wi vx
      camestros.maj spi nsyl ancli eximi ax-mp $.
  $}

  $( Figure 3 $)

  ${
    $( Major premise for the Aristotelian syllogism "Datisi" $)
    datisi.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    datisi.min $e |- E. x ( ph /\ ch ) $.
    $( "Datisi", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-3:  MaP and MiS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    datisi $p |- E. x ( ch /\ ps ) $=
      wph wch wa vx wex wch wps wa vx wex datisi.min wph wch wa wch wps wa vx
      wph wch wa wch wps wph wch simpr wph wps wch wph wps wi vx datisi.maj spi
      adantr jca eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Disamis" $)
    disamis.maj $e |- E. x ( ph /\ ps ) $.
    $( Minor premise for  $)
    disamis.min $e |- A. x ( ph -> ch ) $.
    $( "Disamis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, IAI-3:  MiP and MaS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    disamis $p |- E. x ( ch /\ ps ) $=
      wph wps wa vx wex wch wps wa vx wex disamis.maj wph wps wa wch wps wa vx
      wph wch wps wph wch wi vx disamis.min spi anim1i eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Ferison" $)
    ferison.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    ferison.min $e |- E. x ( ph /\ ch ) $.
    $( "Ferison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, EIO-3:  MeP and MiS therefore SoP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)
    ferison $p |- E. x ( ch /\ -. ps ) $=
      wph wps wn wch vx ferison.maj ferison.min datisi $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Bocardo" $)
    bocardo.maj $e |- E. x ( ph /\ -. ps ) $.
    $( Minor premise for  $)
    bocardo.min $e |- A. x ( ph -> ch ) $.
    $( "Bocardo", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       not ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, OAO-3:  MoP and MaS therefore SoP.)
       For example, "Some cats have no tails", "All cats are mammals",
       therefore "Some mammals have no tails".  A reorder of ~ disamis ; prefer
       using that instead.  (Contributed by David A. Wheeler, 28-Aug-2016.)
       (New usage is discouraged.) $)
    bocardo $p |- E. x ( ch /\ -. ps ) $=
      wph wps wn wch vx bocardo.maj bocardo.min disamis $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Felapton" $)
    felapton.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    felapton.min $e |- A. x ( ph -> ch ) $.
    $( Existence premise for Felapton $)
    felapton.e $e |- E. x ph $.
    $( "Felapton", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-3:  MeP and MaS
       therefore SoP.) For example, "No flowers are animals" and "All flowers
       are plants", therefore "Some plants are not animals".  (Contributed by
       David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    felapton $p |- E. x ( ch /\ -. ps ) $=
      wph vx wex wch wps wn wa vx wex felapton.e wph wch wps wn wa vx wph wch
      wps wn wph wch wi vx felapton.min spi wph wps wn wi vx felapton.maj spi
      jca eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Darapti" $)
    darapti.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    darapti.min $e |- A. x ( ph -> ch ) $.
    $( Existence premise for Darapti $)
    darapti.e $e |- E. x ph $.
    $( "Darapti", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-3:  MaP and MaS
       therefore SiP.) For example, "All squares are rectangles" and "All
       squares are rhombuses", therefore "Some rhombuses are rectangles".
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    darapti $p |- E. x ( ch /\ ps ) $=
      wph vx wex wch wps wa vx wex darapti.e wph wch wps wa vx wph wch wps wph
      wch wi vx darapti.min spi wph wps wi vx darapti.maj spi jca eximi ax-mp
      $.
  $}

  $( Figure 4 $)

  ${
    $( Major premise for the Aristotelian syllogism "Calemes" $)
    calemes.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    calemes.min $e |- A. x ( ps -> -. ch ) $.
    $( "Calemes", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ps ` is ` ch ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-4:  PaM and MeS therefore SeP.) (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    calemes $p |- A. x ( ch -> -. ph ) $=
      wch wph wn wi vx wch wps wph wps wch wps wch wn wi vx calemes.min spi
      con2i wph wps wi vx calemes.maj spi nsyl ax-gen $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Dimatis" $)
    dimatis.maj $e |- E. x ( ph /\ ps ) $.
    $( Minor premise for  $)
    dimatis.min $e |- A. x ( ps -> ch ) $.
    $( "Dimatis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ps ` is ` ch ` , therefore some ` ch ` is ` ph ` .
       (In Aristotelian notation, IAI-4:  PiM and MaS therefore SiP.) For
       example, "Some pets are rabbits.", "All rabbits have fur", therefore
       "Some fur bearing animals are pets".  Like ~ darii with positions
       interchanged.  (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    dimatis $p |- E. x ( ch /\ ph ) $=
      wph wps wa vx wex wch wph wa vx wex dimatis.maj wph wps wa wch wph wa vx
      wph wps wa wch wph wps wch wph wps wch wi vx dimatis.min spi adantl wph
      wps simpl jca eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Fresison" $)
    fresison.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    fresison.min $e |- E. x ( ps /\ ch ) $.
    $( "Fresison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` (PeM), and some ` ps ` is ` ch ` (MiS), therefore some ` ch ` is
       not ` ph ` (SoP).  (In Aristotelian notation, EIO-4:  PeM and MiS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    fresison $p |- E. x ( ch /\ -. ph ) $=
      wps wch wa vx wex wch wph wn wa vx wex fresison.min wps wch wa wch wph wn
      wa vx wps wch wa wch wph wn wps wch simpr wps wph wn wch wph wps wph wps
      wn wi vx fresison.maj spi con2i adantr jca eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Calemos" $)
    calemos.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    calemos.min $e |- A. x ( ps -> -. ch ) $.
    $( Existence premise for Calemos $)
    calemos.e $e |- E. x ch $.
    $( "Calemos", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` (PaM), no ` ps ` is ` ch ` (MeS), and ` ch ` exist, therefore
       some ` ch ` is not ` ph ` (SoP).  (In Aristotelian notation, AEO-4:  PaM
       and MeS therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    calemos $p |- E. x ( ch /\ -. ph ) $=
      wch vx wex wch wph wn wa vx wex calemos.e wch wch wph wn wa vx wch wph wn
      wch wps wph wps wch wps wch wn wi vx calemos.min spi con2i wph wps wi vx
      calemos.maj spi nsyl ancli eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Fesapo" $)
    fesapo.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    fesapo.min $e |- A. x ( ps -> ch ) $.
    $( Existence premise for Fesapo $)
    fesapo.e $e |- E. x ps $.
    $( "Fesapo", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ps ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, EAO-4:  PeM and MaS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    fesapo $p |- E. x ( ch /\ -. ph ) $=
      wps vx wex wch wph wn wa vx wex fesapo.e wps wch wph wn wa vx wps wch wph
      wn wps wch wi vx fesapo.min spi wph wps wph wps wn wi vx fesapo.maj spi
      con2i jca eximi ax-mp $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Bamalip" $)
    bamalip.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    bamalip.min $e |- A. x ( ps -> ch ) $.
    $( Existence premise for Bamalip $)
    bamalip.e $e |- E. x ph $.
    $( "Bamalip", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ph ` exist, therefore some ` ch `
       is ` ph ` .  (In Aristotelian notation, AAI-4:  PaM and MaS therefore
       SiP.) Like ~ barbari .  (Contributed by David A. Wheeler,
       28-Aug-2016.) $)
    bamalip $p |- E. x ( ch /\ ph ) $=
      wph vx wex wch wph wa vx wex bamalip.e wph wch wph wa vx wph wch wph wps
      wch wph wps wi vx bamalip.maj spi wps wch wi vx bamalip.min spi syl ancri
      eximi ax-mp $.
  $}


