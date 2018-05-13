$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-8_(Equality).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Membership predicate

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare the membership predicate symbol. $)

$c e. $.

$(Stylized epsilon $)

$(--- Start of patch to prevent connective overloading $)

$(Extend wff definition to include the membership connective between
       classes.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The purpose of introducing ` wff A e. B ` here is to allow us to
       express i.e.  "prove" the ~ wel of predicate calculus in terms of the
       ~ wceq of set theory, so that we don't "overload" the ` e. ` connective
       with two syntax definitions.  This is done to prevent ambiguity that
       would complicate some Metamath parsers.  The class variables ` A ` and
       ` B ` are introduced temporarily for the purpose of this definition but
       otherwise not used in predicate calculus.  See ~ df-clab for more
       information on the set theory usage of ~ wcel .) $)

${
	$v A B  $.
	f0_wcel $f class A $.
	f1_wcel $f class B $.
	a_wcel $a wff A e. B $.
$}

$(Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read " ` x ` is an element of
     ` y ` ," " ` x ` is a member of ` y ` ," " ` x ` belongs to ` y ` ,"
     or " ` y ` contains ` x ` ."  Note:  The phrase " ` y ` includes
     ` x ` " means " ` x ` is a subset of ` y ` ;" to use it also for
     ` x e. y ` , as some authors occasionally do, is poor form and causes
     confusion, according to George Boolos (1992 lecture at MIT).

     This syntactical construction introduces a binary non-logical predicate
     symbol ` e. ` (epsilon) into our predicate calculus.  We will eventually
     use it for the membership predicate of set theory, but that is irrelevant
     at this point: the predicate calculus axioms for ` e. ` apply to any
     arbitrary binary predicate symbol.  "Non-logical" means that the predicate
     is presumed to have additional properties beyond the realm of predicate
     calculus, although these additional properties are not specified by
     predicate calculus itself but rather by the axioms of a theory (in our
     case set theory) added to predicate calculus.  "Binary" means that the
     predicate has two arguments.

     (Instead of introducing ~ wel as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wcel .  This lets us avoid overloading
     the ` e. ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ wel is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wcel .  Note:  To see the proof steps of this syntax proof, type "show
     proof wel /all" in the Metamath program.)  (Contributed by NM,
     24-Jan-2006.) $)

$(--- End of patch to prevent connective overloading $)

$(--- Start of old code before overloading prevention patch. $)

$(@( Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read " ` x ` is an element of ` y ` ,"
     " ` x ` is a member of ` y ` ," " ` x ` belongs to ` y ` ," or " ` y `
     contains ` x ` ."  Note:  The phrase " ` y ` includes ` x ` " means
     " ` x ` is a subset of ` y ` "; to use it also for ` x e. y ` (as some
     authors occasionally do) is poor form and causes confusion.

     After we introduce ~ cv and ~ wcel in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wcel". @)
  wel @a wff x e. y @.
  $)

$(--- End of old code before overloading prevention patch. $)

$(Register class-to-set promotion and class equality and membership as
     primitive expressions. Although these are actually definitions, the above
     ambiguity prevention necessitates our taking class equality as the
     primitive, instead of set equality. $)

$($j primitive 'weq' 'wel'; $)


