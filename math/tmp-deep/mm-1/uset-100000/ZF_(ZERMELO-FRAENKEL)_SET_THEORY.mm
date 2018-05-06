$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union.mm $]
$( ###############################################################################
                ZF (ZERMELO-FRAENKEL) SET THEORY

###############################################################################

  Set theory uses the formalism of propositional and predicate calculus to
  assert properties of arbitrary mathematical objects called "sets."  A set can
  be contained in another set, and this relationship is indicated by the ` e. `
  symbol.  Starting with the simplest mathematical object, called the empty
  set, set theory builds up more and more complex structures whose existence
  follows from the axioms, eventually resulting in extremely complicated sets
  that we identify with the real numbers and other familiar mathematical
  objects.

  A simplistic concept of sets, sometimes called "naive set theory", is
  vulnerable to a paradox called "Russell's paradox" ( ~ ru ), a discovery that
  revolutionized the foundations of mathematics and logic.  Russell's Paradox
  spawned the development of set theories that countered the paradox, including
  the ZF set theory that is most widely used and is defined here.

  Except for Extensionality, the axioms basically say, "given an arbitrary set
  x (and, in the cases of Replacement and Regularity, provided that an
  antecedent is satisfied), there exists another set y based on or constructed
  from it, with the stated properties."  (The axiom of Extensionality can also
  be restated this way as shown by ~ axext2 .) The individual axiom links
  provide more detailed descriptions.  We derive the redundant ZF axioms of
  Separation, Null Set, and Pairing from the others as theorems.

$)

