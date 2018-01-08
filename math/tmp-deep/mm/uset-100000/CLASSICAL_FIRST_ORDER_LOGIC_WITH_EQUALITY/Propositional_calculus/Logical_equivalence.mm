
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_negation.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical equivalence

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The definition ~ df-bi in this section is our first definition, which
  introduces and defines the biconditional connective ` <-> ` . We define a wff
  of the form ` ( ph <-> ps ) ` as an abbreviation for
  ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

  Unlike most traditional developments, we have chosen not to have a separate
  symbol such as "Df." to mean "is defined as."  Instead, we will later use the
  biconditional connective for this purpose ( ~ df-or is its first use), as it
  allows us to use logic to manipulate definitions directly.  This greatly
  simplifies many proofs since it eliminates the need for a separate mechanism
  for introducing and eliminating definitions.
$)

  $( Declare the biconditional connective. $)
  $c <-> $. $( Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)

  $( Extend our wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( Define the biconditional (logical 'iff').

     The definition ~ df-bi in this section is our first definition, which
     introduces and defines the biconditional connective ` <-> ` .  We define a
     wff of the form ` ( ph <-> ps ) ` as an abbreviation for
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

     Unlike most traditional developments, we have chosen not to have a
     separate symbol such as "Df." to mean "is defined as."  Instead, we will
     later use the biconditional connective for this purpose ( ~ df-or is its
     first use), as it allows us to use logic to manipulate definitions
     directly.  This greatly simplifies many proofs since it eliminates the
     need for a separate mechanism for introducing and eliminating
     definitions.  Of course, we cannot use this mechanism to define the
     biconditional itself, since it hasn't been introduced yet.  Instead, we
     use a more general form of definition, described as follows.

     In its most general form, a definition is simply an assertion that
     introduces a new symbol (or a new combination of existing symbols, as in
     ~ df-3an ) that is eliminable and does not strengthen the existing
     language.  The latter requirement means that the set of provable
     statements not containing the new symbol (or new combination) should
     remain exactly the same after the definition is introduced.  Our
     definition of the biconditional may look unusual compared to most
     definitions, but it strictly satisfies these requirements.

     The justification for our definition is that if we mechanically replace
     ` ( ph <-> ps ) ` (the definiendum i.e. the thing being defined) with
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` (the definiens i.e. the
     defining expression) in the definition, the definition becomes the
     previously proved theorem ~ bijust .  It is impossible to use ~ df-bi to
     prove any statement expressed in the original language that can't be
     proved from the original axioms, because if we simply replace each
     instance of ~ df-bi in the proof with the corresponding ~ bijust instance,
     we will end up with a proof from the original axioms.

     Note that from Metamath's point of view, a definition is just another
     axiom - i.e. an assertion we claim to be true - but from our high level
     point of view, we are not strengthening the language.  To indicate this
     fact, we prefix definition labels with "df-" instead of "ax-".  (This
     prefixing is an informal convention that means nothing to the Metamath
     proof verifier; it is just a naming convention for human readability.)

     After we define the constant true ` T. ` ( ~ df-tru ) and the constant
     false ` F. ` ( ~ df-fal ), we will be able to prove these truth table
     values: ` ( ( T. <-> T. ) <-> T. ) ` ( ~ trubitru ),
     ` ( ( T. <-> F. ) <-> F. ) ` ( ~ trubifal ), ` ( ( F. <-> T. ) <-> F. ) `
     ( ~ falbitru ), and ` ( ( F. <-> F. ) <-> T. ) ` ( ~ falbifal ).

     See ~ dfbi1 , ~ dfbi2 , and ~ dfbi3 for theorems suggesting typical
     textbook definitions of ` <-> ` , showing that our definition has the
     properties we expect.  Theorem ~ dfbi1 is particularly useful if we want
     to eliminate ` <-> ` from an expression to convert it to primitives.
     Theorem ~ dfbi shows this definition rewritten in an abbreviated form
     after conjunction is introduced, for easier understanding.

     Contrast with ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), ` -/\ ` ( ~ df-nan ),
     and ` \/_ ` ( ~ df-xor ) .  In some sense ` <-> ` returns true if two
     truth values are equal; ` = ` ( ~ df-cleq ) returns true if two classes
     are equal.  (Contributed by NM, 5-Aug-1993.) $)
  df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

  $( $j justification 'bijust' for 'df-bi'; $)

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
  bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wph wps wi wph wps wb wph wps wi
    wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi
    wn wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps df-bi wph wps wb
    wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb
    wi wn simplim ax-mp wph wps wi wps wph wi wn simplim syl $.

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
  bi3 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    wph wps wi wps wph wi wph wps wb wph wps wb wph wps wi wps wph wi wn wi wn
    wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wi wps wph
    wi wn wi wn wph wps wb wi wph wps df-bi wph wps wb wph wps wi wps wph wi wn
    wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi simprim ax-mp expi $.

  ${
    impbii.1 $e |- ( ph -> ps ) $.
    impbii.2 $e |- ( ps -> ph ) $.
    $( Infer an equivalence from an implication and its converse.  (Contributed
       by NM, 5-Aug-1993.) $)
    impbii $p |- ( ph <-> ps ) $=
      wph wps wi wps wph wi wph wps wb impbii.1 impbii.2 wph wps bi3 mp2 $.
  $}

  ${
    impbidd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    impbidd.2 $e |- ( ph -> ( ps -> ( th -> ch ) ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Rodolfo
       Medina, 12-Oct-2010.) $)
    impbidd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      wph wps wch wth wi wth wch wi wch wth wb impbidd.1 impbidd.2 wch wth bi3
      syl6c $.
  $}

  ${
    impbid21d.1 $e |- ( ps -> ( ch -> th ) ) $.
    impbid21d.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Wolf
       Lammen, 12-May-2013.) $)
    impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      wph wps wch wth wps wch wth wi wi wph impbid21d.1 a1i wph wth wch wi wps
      impbid21d.2 a1d impbidd $.
  $}

  ${
    impbid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Wolf Lammen, 3-Nov-2012.) $)
    impbid $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wb wph wph wps wch impbid.1 impbid.2 impbid21d pm2.43i $.
  $}

  $( Relate the biconditional connective to primitive connectives.  See
     ~ dfbi1gb for an unusual version proved directly from axioms.
     (Contributed by NM, 5-Aug-1993.) $)
  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wph wps wb wph wps wi wps wph wi
    wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps
    wb wph wps wi wps wph wi wn wi wn wi wph wps df-bi wph wps wb wph wps wi
    wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    simplim ax-mp wph wps wi wps wph wi wph wps wb wph wps bi3 impi impbii $.

  $( This proof of ~ dfbi1 , discovered by Gregory Bush on 8-Mar-2004, has
     several curious properties.  First, it has only 17 steps directly from the
     axioms and ~ df-bi , compared to over 800 steps were the proof of ~ dfbi1
     expanded into axioms.  Second, step 2 demands only the property of "true";
     any axiom (or theorem) could be used.  It might be thought, therefore,
     that it is in some sense redundant, but in fact no proof is shorter than
     this (measured by number of steps).  Third, it illustrates how
     intermediate steps can "blow up" in size even in short proofs.  Fourth,
     the compressed proof is only 182 bytes (or 17 bytes in D-proof notation),
     but the generated web page is over 200kB with intermediate steps that are
     essentially incomprehensible to humans (other than Gregory Bush).  If
     there were an obfuscated code contest for proofs, this would be a
     contender.  This "blowing up" and incomprehensibility of the intermediate
     steps vividly demonstrate the advantages of using many layered
     intermediate theorems, since each theorem is easier to understand.
     (Contributed by Gregory Bush, 10-Mar-2004.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  dfbi1gb $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps
    df-bi wch wth wch wi wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph
    wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps
    wph wi wn wi wn wb wi wch wth ax-1 wph wps wb wph wps wi wps wph wi wn wi
    wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph
    wps wi wps wph wi wn wi wn wb wi wn wch wth wch wi wi wn wi wch wth wch wi
    wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi
    wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi
    wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi
    wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi
    wn wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps wi wps
    wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wi
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn
    wi wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn
    wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb
    wi wn wch wth wch wi wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi
    wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi
    wps wph wi wn wi wn wb wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wi ax-1 wph wps wb wph wps wi wps wph wi wn wi wn wi
    wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi
    wps wph wi wn wi wn wb wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph
    wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps
    wph wi wn wi wn wb wi wn wi wch wth wch wi wi wn wi wi wph wps wb wph wps
    wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wph wps wb wph wps
    wi wps wph wi wn wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph
    wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi
    wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi
    wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wi wi wph wps wb wph
    wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi
    wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wch wth wch wi
    wi wn wi wi wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps
    wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi
    wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn
    wb wi wn wi wch wth wch wi wi wn wi wph wps wb wph wps wi wps wph wi wn wi
    wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph
    wps wi wps wph wi wn wi wn wb wi wn wph wps wb wph wps wi wps wph wi wn wi
    wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn
    wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn
    wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps
    wi wps wph wi wn wi wn wb wi wn wi wch wth wch wi wi wn wi wi wch wth wch
    wi wi wn wn wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps
    wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi
    wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn
    wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb
    wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb
    wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps
    wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn
    wi wn wb wi wn wi wch wth wch wi wi wn wi wph wps wb wph wps wi wps wph wi
    wn wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph
    wi wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn
    wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb
    wph wps wi wps wph wi wn wi wn wb wi wn wi wn wch wth wch wi wi wn wn wph
    wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps wi wps wph wi
    wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wi wph
    wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph
    wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wi wn
    wi wph wps wb wph wps wi wps wph wi wn wi wn df-bi wph wps wb wph wps wi
    wps wph wi wn wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps
    wi wps wph wi wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps
    wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn
    wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wi wn wch wth wch wi wi
    wn wn ax-1 ax-mp wch wth wch wi wi wn wph wps wb wph wps wi wps wph wi wn
    wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi
    wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi
    wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph
    wps wi wps wph wi wn wi wn wb wi wn wi ax-3 ax-mp wph wps wb wph wps wi wps
    wph wi wn wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi
    wps wph wi wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph
    wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph
    wps wb wph wps wi wps wph wi wn wi wn wb wi wn wi wch wth wch wi wi wn wi
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn
    ax-1 ax-mp wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph
    wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi
    wn wb wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps
    wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi
    wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn
    wb wi wn wi wch wth wch wi wi wn ax-2 ax-mp ax-mp wph wps wb wph wps wi wps
    wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn
    wph wps wb wph wps wi wps wph wi wn wi wn wb wi wch wth wch wi wi ax-3
    ax-mp ax-mp ax-mp $.

  ${
    biimpi.1 $e |- ( ph <-> ps ) $.
    $( Infer an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)
    biimpi $p |- ( ph -> ps ) $=
      wph wps wb wph wps wi biimpi.1 wph wps bi1 ax-mp $.
  $}

  ${
    sylbi.1 $e |- ( ph <-> ps ) $.
    sylbi.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by NM, 5-Aug-1993.) $)
    sylbi $p |- ( ph -> ch ) $=
      wph wps wch wph wps sylbi.1 biimpi sylbi.2 syl $.
  $}

  ${
    sylib.1 $e |- ( ph -> ps ) $.
    sylib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by NM, 5-Aug-1993.) $)
    sylib $p |- ( ph -> ch ) $=
      wph wps wch sylib.1 wps wch sylib.2 biimpi syl $.
  $}

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
  bi2 $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wps wph wi wph wps dfbi1 wph wps
    wi wps wph wi simprim sylbi $.

  $( Commutative law for equivalence.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)
  bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    wph wps wb wps wph wph wps bi2 wph wps bi1 impbid $.

  $( Commutative law for equivalence.  Theorem *4.21 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.) $)
  bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $=
    wph wps wb wps wph wb wph wps bicom1 wps wph bicom1 impbii $.

  ${
    bicomd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Commute two sides of a biconditional in a deduction.  (Contributed by
       NM, 5-Aug-1993.) $)
    bicomd $p |- ( ph -> ( ch <-> ps ) ) $=
      wph wps wch wb wch wps wb bicomd.1 wps wch bicom sylib $.
  $}

  ${
    bicomi.1 $e |- ( ph <-> ps ) $.
    $( Inference from commutative law for logical equivalence.  (Contributed by
       NM, 5-Aug-1993.) $)
    bicomi $p |- ( ps <-> ph ) $=
      wph wps wb wps wph wb bicomi.1 wph wps bicom1 ax-mp $.
  $}

  ${
    impbid1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid1.2 $e |- ( ch -> ps ) $.
    $( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.) $)
    impbid1 $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch impbid1.1 wch wps wi wph impbid1.2 a1i impbid $.
  $}

  ${
    impbid2.1 $e |- ( ps -> ch ) $.
    impbid2.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.)  (Proof shortened by Wolf Lammen, 27-Sep-2013.) $)
    impbid2 $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wch wps wph wch wps impbid2.2 impbid2.1 impbid1 bicomd $.
  $}

  ${
    impcon4bid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impcon4bid.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( A variation on ~ impbid with contraposition.  (Contributed by Jeff
       Hankins, 3-Jul-2009.) $)
    impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch impcon4bid.1 wph wps wch impcon4bid.2 con4d impbid $.
  $}

  ${
    biimpri.1 $e |- ( ph <-> ps ) $.
    $( Infer a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 16-Sep-2013.) $)
    biimpri $p |- ( ps -> ph ) $=
      wps wph wph wps biimpri.1 bicomi biimpi $.
  $}

  ${
    biimpd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)
    biimpd $p |- ( ph -> ( ps -> ch ) ) $=
      wph wps wch wb wps wch wi biimpd.1 wps wch bi1 syl $.
  $}

  ${
    mpbi.min $e |- ph $.
    mpbi.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.) $)
    mpbi $p |- ps $=
      wph wps mpbi.min wph wps mpbi.maj biimpi ax-mp $.
  $}

  ${
    mpbir.min $e |- ps $.
    mpbir.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.) $)
    mpbir $p |- ph $=
      wps wph mpbir.min wph wps mpbir.maj biimpri ax-mp $.
  $}

  ${
    mpbid.min $e |- ( ph -> ps ) $.
    mpbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)
    mpbid $p |- ( ph -> ch ) $=
      wph wps wch mpbid.min wph wps wch mpbid.maj biimpd mpd $.
  $}

  ${
    mpbii.min $e |- ps $.
    mpbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mpbii $p |- ( ph -> ch ) $=
      wph wps wch wps wph mpbii.min a1i mpbii.maj mpbid $.
  $}

  ${
    sylibr.1 $e |- ( ph -> ps ) $.
    sylibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       NM, 5-Aug-1993.) $)
    sylibr $p |- ( ph -> ch ) $=
      wph wps wch sylibr.1 wch wps sylibr.2 biimpri syl $.
  $}

  ${
    sylbir.1 $e |- ( ps <-> ph ) $.
    sylbir.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by NM, 5-Aug-1993.) $)
    sylbir $p |- ( ph -> ch ) $=
      wph wps wch wps wph sylbir.1 biimpri sylbir.2 syl $.
  $}

  ${
    sylibd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylibd $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth sylibd.1 wph wch wth sylibd.2 biimpd syld $.
  $}

  ${
    sylbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylbid.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylbid $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wps wch sylbid.1 biimpd sylbid.2 syld $.
  $}

  ${
    mpbidi.min $e |- ( th -> ( ph -> ps ) ) $.
    mpbidi.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 9-Aug-1994.) $)
    mpbidi $p |- ( th -> ( ph -> ch ) ) $=
      wth wph wps wch mpbidi.min wph wps wch mpbidi.maj biimpd sylcom $.
  $}

  ${
    syl5bi.1 $e |- ( ph <-> ps ) $.
    syl5bi.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
    syl5bi $p |- ( ch -> ( ph -> th ) ) $=
      wph wps wch wth wph wps syl5bi.1 biimpi syl5bi.2 syl5 $.
  $}

  ${
    syl5bir.1 $e |- ( ps <-> ph ) $.
    syl5bir.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
    syl5bir $p |- ( ch -> ( ph -> th ) ) $=
      wph wps wch wth wps wph syl5bir.1 biimpri syl5bir.2 syl5 $.
  $}

  ${
    syl5ib.1 $e |- ( ph -> ps ) $.
    syl5ib.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 5-Aug-1993.) $)
    syl5ib $p |- ( ch -> ( ph -> th ) ) $=
      wph wps wch wth syl5ib.1 wch wps wth syl5ib.2 biimpd syl5 $.

    $( A mixed syllogism inference.  (Contributed by NM, 19-Jun-2007.) $)
    syl5ibcom $p |- ( ph -> ( ch -> th ) ) $=
      wch wph wth wph wps wch wth syl5ib.1 syl5ib.2 syl5ib com12 $.
  $}

  ${
    syl5ibr.1 $e |- ( ph -> th ) $.
    syl5ibr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 3-Apr-1994.) $)
    syl5ibr $p |- ( ch -> ( ph -> ps ) ) $=
      wph wth wch wps syl5ibr.1 wch wps wth syl5ibr.2 bicomd syl5ib $.

    $( A mixed syllogism inference.  (Contributed by NM, 20-Jun-2007.) $)
    syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $=
      wch wph wps wph wps wch wth syl5ibr.1 syl5ibr.2 syl5ibr com12 $.
  $}

  ${
    biimprd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimprd $p |- ( ph -> ( ch -> ps ) ) $=
      wch wps wph wch wch id biimprd.1 syl5ibr $.
  $}

  ${
    biimpcd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a commuted implication from a logical equivalence.  (Contributed
       by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimpcd $p |- ( ps -> ( ph -> ch ) ) $=
      wps wps wph wch wps id biimpcd.1 syl5ibcom $.

    $( Deduce a converse commuted implication from a logical equivalence.
       (Contributed by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen,
       20-Dec-2013.) $)
    biimprcd $p |- ( ch -> ( ph -> ps ) ) $=
      wch wps wph wch wch id biimpcd.1 syl5ibrcom $.
  $}

  ${
    syl6ib.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ib.2 $e |- ( ch <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
    syl6ib $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth syl6ib.1 wch wth syl6ib.2 biimpi syl6 $.
  $}

  ${
    syl6ibr.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ibr.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
    syl6ibr $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth syl6ibr.1 wth wch syl6ibr.2 biimpri syl6 $.
  $}


  ${
    syl6bi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 2-Jan-1994.) $)
    syl6bi $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wps wch syl6bi.1 biimpd syl6bi.2 syl6 $.
  $}

  ${
    syl6bir.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    syl6bir.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    syl6bir $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wch wps syl6bir.1 biimprd syl6bir.2 syl6 $.
  $}

  ${
    syl7bi.1 $e |- ( ph <-> ps ) $.
    syl7bi.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A mixed syllogism inference from a doubly nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
    syl7bi $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      wph wps wch wth wta wph wps syl7bi.1 biimpi syl7bi.2 syl7 $.
  $}

  ${
    syl8ib.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8ib.2 $e |- ( th <-> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM,
       1-Aug-1994.) $)
    syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      wph wps wch wth wta syl8ib.1 wth wta syl8ib.2 biimpi syl8 $.
  $}

  ${
    mpbird.min $e |- ( ph -> ch ) $.
    mpbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)
    mpbird $p |- ( ph -> ps ) $=
      wph wch wps mpbird.min wph wps wch mpbird.maj biimprd mpd $.
  $}

  ${
    mpbiri.min $e |- ch $.
    mpbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mpbiri $p |- ( ph -> ps ) $=
      wph wps wch wch wph mpbiri.min a1i mpbiri.maj mpbird $.
  $}

  ${
    sylibrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibrd.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylibrd $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth sylibrd.1 wph wth wch sylibrd.2 biimprd syld $.
  $}

  ${
    sylbird.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    sylbird.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylbird $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wch wps sylbird.1 biimprd sylbird.2 syld $.
  $}

  $( Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 5-Aug-1993.) $)
  biid $p |- ( ph <-> ph ) $=
    wph wph wph id wph id impbii $.

  $( Principle of identity with antecedent.  (Contributed by NM,
     25-Nov-1995.) $)
  biidd $p |- ( ph -> ( ps <-> ps ) ) $=
    wps wps wb wph wps biid a1i $.

  $( Two propositions are equivalent if they are both true.  Closed form of
     ~ 2th .  Equivalent to a ~ bi1 -like version of the xor-connective.  This
     theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version
     ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .  (Contributed by Wolf Lammen,
     12-May-2013.) $)
  pm5.1im $p |- ( ph -> ( ps -> ( ph <-> ps ) ) ) $=
    wph wps wph wps wps wph ax-1 wph wps ax-1 impbid21d $.

  ${
    2th.1 $e |- ph $.
    2th.2 $e |- ps $.
    $( Two truths are equivalent.  (Contributed by NM, 18-Aug-1993.) $)
    2th $p |- ( ph <-> ps ) $=
      wph wps wps wph 2th.2 a1i wph wps 2th.1 a1i impbii $.
  $}

  ${
    2thd.1 $e |- ( ph -> ps ) $.
    2thd.2 $e |- ( ph -> ch ) $.
    $( Two truths are equivalent (deduction rule).  (Contributed by NM,
       3-Jun-2012.) $)
    2thd $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wps wch wb 2thd.1 2thd.2 wps wch pm5.1im sylc $.
  $}

  ${
    ibi.1 $e |- ( ph -> ( ph <-> ps ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 17-Oct-2003.) $)
    ibi $p |- ( ph -> ps ) $=
      wph wps wph wph wps ibi.1 biimpd pm2.43i $.
  $}

  ${
    ibir.1 $e |- ( ph -> ( ps <-> ph ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 22-Jul-2004.) $)
    ibir $p |- ( ph -> ps ) $=
      wph wps wph wps wph ibir.1 bicomd ibi $.
  $}

  ${
    ibd.1 $e |- ( ph -> ( ps -> ( ps <-> ch ) ) ) $.
    $( Deduction that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 26-Jun-2004.) $)
    ibd $p |- ( ph -> ( ps -> ch ) ) $=
      wps wph wps wch wb wch ibd.1 wps wch bi1 syli $.
  $}

  $( Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126.  (Contributed by NM, 1-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 11-Apr-2013.) $)
  pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $=
    wph wps wch wb wi wph wps wi wph wch wi wb wph wps wch wb wi wph wps wi wph
    wch wi wps wch wb wps wch wph wps wch bi1 imim3i wps wch wb wch wps wph wps
    wch bi2 imim3i impbid wph wps wi wph wch wi wb wph wps wch wph wps wi wph
    wch wi wb wph wps wch wph wps wi wph wch wi bi1 pm2.86d wph wps wi wph wch
    wi wb wph wch wps wph wps wi wph wch wi bi2 pm2.86d impbidd impbii $.

  ${
    pm5.74i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $=
      wph wps wch wb wi wph wps wi wph wch wi wb pm5.74i.1 wph wps wch pm5.74
      mpbi $.
  $}

  ${
    pm5.74ri.1 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
    $( Distribution of implication over biconditional (reverse inference
       rule).  (Contributed by NM, 1-Aug-1994.) $)
    pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wb wi wph wps wi wph wch wi wb pm5.74ri.1 wph wps wch pm5.74
      mpbir $.
  $}

  ${
    pm5.74d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 21-Mar-1996.) $)
    pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      wph wps wch wth wb wi wps wch wi wps wth wi wb pm5.74d.1 wps wch wth
      pm5.74 sylib $.
  $}

  ${
    pm5.74rd.1 $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 19-Mar-1997.) $)
    pm5.74rd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      wph wps wch wi wps wth wi wb wps wch wth wb wi pm5.74rd.1 wps wch wth
      pm5.74 sylibr $.
  $}

  ${
    bitri.1 $e |- ( ph <-> ps ) $.
    bitri.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Oct-2012.) $)
    bitri $p |- ( ph <-> ch ) $=
      wph wch wph wps wch wph wps bitri.1 biimpi bitri.2 sylib wch wps wph wps
      wch bitri.2 biimpri bitri.1 sylibr impbii $.
  $}

  ${
    bitr2i.1 $e |- ( ph <-> ps ) $.
    bitr2i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
    bitr2i $p |- ( ch <-> ph ) $=
      wph wch wph wps wch bitr2i.1 bitr2i.2 bitri bicomi $.
  $}

  ${
    bitr3i.1 $e |- ( ps <-> ph ) $.
    bitr3i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
    bitr3i $p |- ( ph <-> ch ) $=
      wph wps wch wps wph bitr3i.1 bicomi bitr3i.2 bitri $.
  $}

  ${
    bitr4i.1 $e |- ( ph <-> ps ) $.
    bitr4i.2 $e |- ( ch <-> ps ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
    bitr4i $p |- ( ph <-> ch ) $=
      wph wps wch bitr4i.1 wch wps bitr4i.2 bicomi bitri $.
  $}

  $( Register '<->' as an equality for its type (wff). $)
  $( $j
    equality 'wb' from 'biid' 'bicomi' 'bitri';
    definition 'dfbi1' for 'wb';
  $)

  ${
    bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitri .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 14-Apr-2013.) $)
    bitrd $p |- ( ph -> ( ps <-> th ) ) $=
      wph wps wth wph wps wi wph wch wi wph wth wi wph wps wch bitrd.1 pm5.74i
      wph wch wth bitrd.2 pm5.74i bitri pm5.74ri $.
  $}

  ${
    bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2d.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitr2i .  (Contributed by NM, 9-Jun-2004.) $)
    bitr2d $p |- ( ph -> ( th <-> ps ) ) $=
      wph wps wth wph wps wch wth bitr2d.1 bitr2d.2 bitrd bicomd $.
  $}

  ${
    bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    $( Deduction form of ~ bitr3i .  (Contributed by NM, 5-Aug-1993.) $)
    bitr3d $p |- ( ph -> ( ch <-> th ) ) $=
      wph wch wps wth wph wps wch bitr3d.1 bicomd bitr3d.2 bitrd $.
  $}

  ${
    bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( Deduction form of ~ bitr4i .  (Contributed by NM, 5-Aug-1993.) $)
    bitr4d $p |- ( ph -> ( ps <-> th ) ) $=
      wph wps wch wth bitr4d.1 wph wth wch bitr4d.2 bicomd bitrd $.
  $}

  ${
    syl5bb.1 $e |- ( ph <-> ps ) $.
    syl5bb.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl5bb $p |- ( ch -> ( ph <-> th ) ) $=
      wch wph wps wth wph wps wb wch syl5bb.1 a1i syl5bb.2 bitrd $.
  $}

  ${
    syl5rbb.1 $e |- ( ph <-> ps ) $.
    syl5rbb.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl5rbb $p |- ( ch -> ( th <-> ph ) ) $=
      wch wph wth wph wps wch wth syl5rbb.1 syl5rbb.2 syl5bb bicomd $.
  $}

  ${
    syl5bbr.1 $e |- ( ps <-> ph ) $.
    syl5bbr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl5bbr $p |- ( ch -> ( ph <-> th ) ) $=
      wph wps wch wth wps wph syl5bbr.1 bicomi syl5bbr.2 syl5bb $.
  $}

  ${
    syl5rbbr.1 $e |- ( ps <-> ph ) $.
    syl5rbbr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    syl5rbbr $p |- ( ch -> ( th <-> ph ) ) $=
      wph wps wch wth wps wph syl5rbbr.1 bicomi syl5rbbr.2 syl5rbb $.
  $}

  ${
    syl6bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl6bb $p |- ( ph -> ( ps <-> th ) ) $=
      wph wps wch wth syl6bb.1 wch wth wb wph syl6bb.2 a1i bitrd $.
  $}

  ${
    syl6rbb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl6rbb $p |- ( ph -> ( th <-> ps ) ) $=
      wph wps wth wph wps wch wth syl6rbb.1 syl6rbb.2 syl6bb bicomd $.
  $}

  ${
    syl6bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl6bbr $p |- ( ph -> ( ps <-> th ) ) $=
      wph wps wch wth syl6bbr.1 wth wch syl6bbr.2 bicomi syl6bb $.
  $}

  ${
    syl6rbbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    syl6rbbr $p |- ( ph -> ( th <-> ps ) ) $=
      wph wps wch wth syl6rbbr.1 wth wch syl6rbbr.2 bicomi syl6rbb $.
  $}

  ${
    3imtr3.1 $e |- ( ph -> ps ) $.
    3imtr3.2 $e |- ( ph <-> ch ) $.
    3imtr3.3 $e |- ( ps <-> th ) $.
    $( A mixed syllogism inference, useful for removing a definition from both
       sides of an implication.  (Contributed by NM, 10-Aug-1994.) $)
    3imtr3i $p |- ( ch -> th ) $=
      wch wps wth wch wph wps 3imtr3.2 3imtr3.1 sylbir 3imtr3.3 sylib $.
  $}

  ${
    3imtr4.1 $e |- ( ph -> ps ) $.
    3imtr4.2 $e |- ( ch <-> ph ) $.
    3imtr4.3 $e |- ( th <-> ps ) $.
    $( A mixed syllogism inference, useful for applying a definition to both
       sides of an implication.  (Contributed by NM, 5-Aug-1993.) $)
    3imtr4i $p |- ( ch -> th ) $=
      wch wps wth wch wph wps 3imtr4.2 3imtr4.1 sylbi 3imtr4.3 sylibr $.
  $}

  ${
    3imtr3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3imtr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 8-Apr-1996.) $)
    3imtr3d $p |- ( ph -> ( th -> ta ) ) $=
      wph wth wps wta 3imtr3d.2 wph wps wch wta 3imtr3d.1 3imtr3d.3 sylibd
      sylbird $.
  $}

  ${
    3imtr4d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3imtr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 26-Oct-1995.) $)
    3imtr4d $p |- ( ph -> ( th -> ta ) ) $=
      wph wth wps wta 3imtr4d.2 wph wps wch wta 3imtr4d.1 3imtr4d.3 sylibrd
      sylbid $.
  $}

  ${
    3imtr3g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3g.2 $e |- ( ps <-> th ) $.
    3imtr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr3g $p |- ( ph -> ( th -> ta ) ) $=
      wph wth wch wta wth wps wph wch 3imtr3g.2 3imtr3g.1 syl5bir 3imtr3g.3
      syl6ib $.
  $}

  ${
    3imtr4g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4g.2 $e |- ( th <-> ps ) $.
    3imtr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr4g $p |- ( ph -> ( th -> ta ) ) $=
      wph wth wch wta wth wps wph wch 3imtr4g.2 3imtr4g.1 syl5bi 3imtr4g.3
      syl6ibr $.
  $}

  ${
    3bitri.1 $e |- ( ph <-> ps ) $.
    3bitri.2 $e |- ( ps <-> ch ) $.
    3bitri.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    3bitri $p |- ( ph <-> th ) $=
      wph wps wth 3bitri.1 wps wch wth 3bitri.2 3bitri.3 bitri bitri $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitrri $p |- ( th <-> ph ) $=
      wth wch wph 3bitri.3 wph wps wch 3bitri.1 3bitri.2 bitr2i bitr3i $.
  $}

  ${
    3bitr2i.1 $e |- ( ph <-> ps ) $.
    3bitr2i.2 $e |- ( ch <-> ps ) $.
    3bitr2i.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitr2i $p |- ( ph <-> th ) $=
      wph wch wth wph wps wch 3bitr2i.1 3bitr2i.2 bitr4i 3bitr2i.3 bitri $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitr2ri $p |- ( th <-> ph ) $=
      wph wch wth wph wps wch 3bitr2i.1 3bitr2i.2 bitr4i 3bitr2i.3 bitr2i $.
  $}

  ${
    3bitr3i.1 $e |- ( ph <-> ps ) $.
    3bitr3i.2 $e |- ( ph <-> ch ) $.
    3bitr3i.3 $e |- ( ps <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 19-Aug-1993.) $)
    3bitr3i $p |- ( ch <-> th ) $=
      wch wps wth wch wph wps 3bitr3i.2 3bitr3i.1 bitr3i 3bitr3i.3 bitri $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    3bitr3ri $p |- ( th <-> ch ) $=
      wth wps wch 3bitr3i.3 wps wph wch 3bitr3i.1 3bitr3i.2 bitr3i bitr3i $.
  $}

  ${
    3bitr4i.1 $e |- ( ph <-> ps ) $.
    3bitr4i.2 $e |- ( ch <-> ph ) $.
    3bitr4i.3 $e |- ( th <-> ps ) $.
    $( A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    3bitr4i $p |- ( ch <-> th ) $=
      wch wph wth 3bitr4i.2 wph wps wth 3bitr4i.1 3bitr4i.3 bitr4i bitri $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 2-Sep-1995.) $)
    3bitr4ri $p |- ( th <-> ch ) $=
      wch wph wth 3bitr4i.2 wph wps wth 3bitr4i.1 3bitr4i.3 bitr4i bitr2i $.
  $}

  ${
    3bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    3bitrd.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       13-Aug-1999.) $)
    3bitrd $p |- ( ph -> ( ps <-> ta ) ) $=
      wph wps wth wta wph wps wch wth 3bitrd.1 3bitrd.2 bitrd 3bitrd.3 bitrd $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitrrd $p |- ( ph -> ( ta <-> ps ) ) $=
      wph wth wta wps 3bitrd.3 wph wps wch wth 3bitrd.1 3bitrd.2 bitr2d bitr3d
      $.
  $}

  ${
    3bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr2d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    3bitr2d.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr2d $p |- ( ph -> ( ps <-> ta ) ) $=
      wph wps wth wta wph wps wch wth 3bitr2d.1 3bitr2d.2 bitr4d 3bitr2d.3
      bitrd $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr2rd $p |- ( ph -> ( ta <-> ps ) ) $=
      wph wps wth wta wph wps wch wth 3bitr2d.1 3bitr2d.2 bitr4d 3bitr2d.3
      bitr2d $.
  $}

  ${
    3bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3bitr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       24-Apr-1996.) $)
    3bitr3d $p |- ( ph -> ( th <-> ta ) ) $=
      wph wth wch wta wph wps wth wch 3bitr3d.2 3bitr3d.1 bitr3d 3bitr3d.3
      bitrd $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr3rd $p |- ( ph -> ( ta <-> th ) ) $=
      wph wch wta wth 3bitr3d.3 wph wps wch wth 3bitr3d.1 3bitr3d.2 bitr3d
      bitr3d $.
  $}

  ${
    3bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3bitr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       18-Oct-1995.) $)
    3bitr4d $p |- ( ph -> ( th <-> ta ) ) $=
      wph wth wps wta 3bitr4d.2 wph wps wch wta 3bitr4d.1 3bitr4d.3 bitr4d
      bitrd $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr4rd $p |- ( ph -> ( ta <-> th ) ) $=
      wph wta wps wth wph wta wch wps 3bitr4d.3 3bitr4d.1 bitr4d 3bitr4d.2
      bitr4d $.
  $}

  ${
    3bitr3g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3g.2 $e |- ( ps <-> th ) $.
    3bitr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3bitr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 4-Jun-1995.) $)
    3bitr3g $p |- ( ph -> ( th <-> ta ) ) $=
      wph wth wch wta wth wps wph wch 3bitr3g.2 3bitr3g.1 syl5bbr 3bitr3g.3
      syl6bb $.
  $}

  ${
    3bitr4g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4g.2 $e |- ( th <-> ps ) $.
    3bitr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3bitr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 5-Aug-1993.) $)
    3bitr4g $p |- ( ph -> ( th <-> ta ) ) $=
      wph wth wch wta wth wps wph wch 3bitr4g.2 3bitr4g.1 syl5bb 3bitr4g.3
      syl6bbr $.
  $}

  ${
    bi3ant.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Construct a bi-conditional in antecedent position.  (Contributed by Wolf
       Lammen, 14-May-2013.) $)
    bi3ant $p |- ( ( ( th -> ta ) -> ph )
        -> ( ( ( ta -> th ) -> ps ) -> ( ( th <-> ta ) -> ch ) ) ) $=
      wth wta wi wph wi wth wta wb wph wi wta wth wi wps wi wth wta wb wps wi
      wth wta wb wch wi wth wta wb wth wta wi wph wth wta bi1 imim1i wth wta wb
      wta wth wi wps wth wta bi2 imim1i wph wps wch wth wta wb bi3ant.1 imim3i
      syl2im $.
  $}

  $( Express symmetries of theorems in terms of biconditionals.  (Contributed
     by Wolf Lammen, 14-May-2013.) $)
  bisym $p |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph )
      -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) ) $=
    wch wth wi wth wch wi wch wth wb wph wps wch wth bi3 bi3ant $.

  $( Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117.
     (Contributed by NM, 5-Aug-1993.) $)
  notnot $p |- ( ph <-> -. -. ph ) $=
    wph wph wn wn wph notnot1 wph notnot2 impbii $.

  $( Contraposition.  Theorem *4.1 of [WhiteheadRussell] p. 116.  (Contributed
     by NM, 5-Aug-1993.) $)
  con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $=
    wph wps wi wps wn wph wn wi wph wps con3 wps wph ax-3 impbii $.

  ${
    con4bid.1 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 21-May-1994.) $)
    con4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wph wch wps wph wps wn wch wn con4bid.1 biimprd con4d wph wps
      wn wch wn con4bid.1 biimpd impcon4bid $.
  $}

  ${
    notbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction negating both sides of a logical equivalence.  (Contributed by
       NM, 21-May-1994.) $)
    notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $=
      wph wps wn wch wn wph wps wch wps wn wn wch wn wn notbid.1 wps notnot wch
      notnot 3bitr3g con4bid $.
  $}

  $( Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 21-May-1994.)  (Proof shortened by Wolf Lammen, 12-Jun-2013.) $)
  notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $=
    wph wps wb wph wn wps wn wb wph wps wb wph wps wph wps wb id notbid wph wn
    wps wn wb wph wps wph wn wps wn wb id con4bid impbii $.

  ${
    notbii.1 $e |- ( ph <-> ps ) $.
    $( Negate both sides of a logical equivalence.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
    notbii $p |- ( -. ph <-> -. ps ) $=
      wph wps wb wph wn wps wn wb notbii.1 wph wps notbi mpbi $.

    $( Theorem notbii is the congruence law for negation. $)
    $( $j congruence 'notbii'; $)
  $}

  ${
    con4bii.1 $e |- ( -. ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 21-May-1994.) $)
    con4bii $p |- ( ph <-> ps ) $=
      wph wps wb wph wn wps wn wb con4bii.1 wph wps notbi mpbir $.
  $}

  ${
    mtbi.1 $e |- -. ph $.
    mtbi.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mtbi $p |- -. ps $=
      wps wph mtbi.1 wph wps mtbi.2 biimpri mto $.
  $}

  ${
    mtbir.1 $e |- -. ps $.
    mtbir.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       14-Oct-2012.) $)
    mtbir $p |- -. ph $=
      wps wph mtbir.1 wph wps mtbir.2 bicomi mtbi $.
  $}

  ${
    mtbid.min $e |- ( ph -> -. ps ) $.
    mtbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 26-Nov-1995.) $)
    mtbid $p |- ( ph -> -. ch ) $=
      wph wch wps mtbid.min wph wps wch mtbid.maj biimprd mtod $.
  $}

  ${
    mtbird.min $e |- ( ph -> -. ch ) $.
    mtbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 10-May-1994.) $)
    mtbird $p |- ( ph -> -. ps ) $=
      wph wps wch mtbird.min wph wps wch mtbird.maj biimpd mtod $.
  $}

  ${
    mtbii.min $e |- -. ps $.
    mtbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 27-Nov-1995.) $)
    mtbii $p |- ( ph -> -. ch ) $=
      wph wch wps mtbii.min wph wps wch mtbii.maj biimprd mtoi $.
  $}

  ${
    mtbiri.min $e |- -. ch $.
    mtbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 24-Aug-1995.) $)
    mtbiri $p |- ( ph -> -. ps ) $=
      wph wps wch mtbiri.min wph wps wch mtbiri.maj biimpd mtoi $.
  $}

  ${
    sylnib.1 $e |- ( ph -> -. ps ) $.
    sylnib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnib $p |- ( ph -> -. ch ) $=
      wph wps wch sylnib.1 wps wch wb wph sylnib.2 a1i mtbid $.
  $}

  ${
    sylnibr.1 $e |- ( ph -> -. ps ) $.
    sylnibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       Wolf Lammen, 16-Dec-2013.) $)
    sylnibr $p |- ( ph -> -. ch ) $=
      wph wps wch sylnibr.1 wch wps sylnibr.2 bicomi sylnib $.
  $}

  ${
    sylnbi.1 $e |- ( ph <-> ps ) $.
    sylnbi.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnbi $p |- ( -. ph -> ch ) $=
      wph wn wps wn wch wph wps sylnbi.1 notbii sylnbi.2 sylbi $.
  $}

  ${
    sylnbir.1 $e |- ( ps <-> ph ) $.
    sylnbir.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnbir $p |- ( -. ph -> ch ) $=
      wph wps wch wps wph sylnbir.1 bicomi sylnbir.2 sylnbi $.
  $}

  ${
    xchnxbi.1 $e |- ( -. ph <-> ps ) $.
    xchnxbi.2 $e |- ( ph <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbi $p |- ( -. ch <-> ps ) $=
      wch wn wph wn wps wph wch xchnxbi.2 notbii xchnxbi.1 bitr3i $.
  $}

  ${
    xchnxbir.1 $e |- ( -. ph <-> ps ) $.
    xchnxbir.2 $e |- ( ch <-> ph ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbir $p |- ( -. ch <-> ps ) $=
      wph wps wch xchnxbir.1 wch wph xchnxbir.2 bicomi xchnxbi $.
  $}

  ${
    xchbinx.1 $e |- ( ph <-> -. ps ) $.
    xchbinx.2 $e |- ( ps <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinx $p |- ( ph <-> -. ch ) $=
      wph wps wn wch wn xchbinx.1 wps wch xchbinx.2 notbii bitri $.
  $}

  ${
    xchbinxr.1 $e |- ( ph <-> -. ps ) $.
    xchbinxr.2 $e |- ( ch <-> ps ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinxr $p |- ( ph <-> -. ch ) $=
      wph wps wch xchbinxr.1 wch wps xchbinxr.2 bicomi xchbinx $.
  $}

  $( The next three rules are useful for building up wff's around a
     definition, in order to make use of the definition. $)

  ${
    bi.a $e |- ( ph <-> ps ) $.
    $( Introduce an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       6-Feb-2013.) $)
    imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $=
      wch wph wps wph wps wb wch bi.a a1i pm5.74i $.
  $}

  ${
    bibi.a $e |- ( ph <-> ps ) $.
    $( Inference adding a biconditional to the left in an equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.)  (Proof shortened by Wolf Lammen, 16-May-2013.) $)
    bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $=
      wch wph wb wch wps wb wch wph wb wch wph wps wch wph wb id bibi.a syl6bb
      wch wps wb wch wps wph wch wps wb id bibi.a syl6bbr impbii $.

    $( Inference adding a biconditional to the right in an equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      wph wch wb wch wph wb wch wps wb wps wch wb wph wch bicom wph wps wch
      bibi.a bibi2i wch wps bicom 3bitri $.

    ${
      bibi12.2 $e |- ( ch <-> th ) $.
      $( The equivalence of two equivalences.  (Contributed by NM,
         5-Aug-1993.) $)
      bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $=
        wph wch wb wph wth wb wps wth wb wch wth wph bibi12.2 bibi2i wph wps
        wth bibi.a bibi1i bitri $.
    $}
  $}

  ${
    imbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    imbi2d $p |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ) $=
      wph wth wps wch wph wps wch wb wth imbid.1 a1d pm5.74d $.

    $( Deduction adding a consequent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
    imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $=
      wph wps wth wi wch wth wi wph wch wps wth wph wps wch imbid.1 biimprd
      imim1d wph wps wch wth wph wps wch imbid.1 biimpd imim1d impbid $.

    $( Deduction adding a biconditional to the left in an equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       19-May-2013.) $)
    bibi2d $p |- ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ) $=
      wph wth wps wb wth wch wb wph wth wi wph wps wi wb wph wth wi wph wch wi
      wb wph wth wps wb wi wph wth wch wb wi wph wps wi wph wch wi wph wth wi
      wph wps wch imbid.1 pm5.74i bibi2i wph wth wps pm5.74 wph wth wch pm5.74
      3bitr4i pm5.74ri $.

    $( Deduction adding a biconditional to the right in an equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    bibi1d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) ) $=
      wph wth wps wb wth wch wb wps wth wb wch wth wb wph wps wch wth imbid.1
      bibi2d wps wth bicom wch wth bicom 3bitr4g $.
  $}

  ${
    imbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    imbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of implications.
       (Contributed by NM, 5-Aug-1993.) $)
    imbi12d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
      wph wps wth wi wch wth wi wch wta wi wph wps wch wth imbi12d.1 imbi1d wph
      wth wta wch imbi12d.2 imbi2d bitrd $.

    $( Deduction joining two equivalences to form equivalence of
       biconditionals.  (Contributed by NM, 5-Aug-1993.) $)
    bibi12d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) ) $=
      wph wps wth wb wch wth wb wch wta wb wph wps wch wth imbi12d.1 bibi1d wph
      wth wta wch imbi12d.2 bibi2d bitrd $.
  $}

  $( Theorem *4.84 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $=
    wph wps wb wph wps wch wph wps wb id imbi1d $.

  $( Theorem *4.85 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
  imbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $=
    wph wps wb wph wps wch wph wps wb id imbi2d $.

  ${
    imbi1i.1 $e |- ( ph <-> ps ) $.
    $( Introduce a consequent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
    imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $=
      wph wps wb wph wch wi wps wch wi wb imbi1i.1 wph wps wch imbi1 ax-mp $.
  $}

  ${
    imbi12i.1 $e |- ( ph <-> ps ) $.
    imbi12i.2 $e |- ( ch <-> th ) $.
    $( Join two logical equivalences to form equivalence of implications.
       (Contributed by NM, 5-Aug-1993.) $)
    imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $=
      wph wch wi wph wth wi wps wth wi wch wth wph imbi12i.2 imbi2i wph wps wth
      imbi12i.1 imbi1i bitri $.

    $( Theorem imbi12i is the congruence law for implication. $)
    $( $j congruence 'imbi12i'; $)
  $}

  $( Theorem *4.86 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  bibi1 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $=
    wph wps wb wph wps wch wph wps wb id bibi1d $.

  $( Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 15-Apr-1995.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)
  con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $=
    wph wps wn wb wph wn wps wn wn wb wph wn wps wb wps wph wn wb wph wps wn
    notbi wps wps wn wn wph wn wps notnot bibi2i wph wn wps bicom 3bitr2i $.

  ${
    con2bid.1 $e |- ( ph -> ( ps <-> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 15-Apr-1995.) $)
    con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $=
      wph wps wch wn wb wch wps wn wb con2bid.1 wch wps con2bi sylibr $.
  $}

  ${
    con1bid.1 $e |- ( ph -> ( -. ps <-> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 9-Oct-1999.) $)
    con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $=
      wph wps wch wn wph wch wps wph wps wn wch con1bid.1 bicomd con2bid bicomd
      $.
  $}

  ${
    con1bii.1 $e |- ( -. ph <-> ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 13-Oct-2012.) $)
    con1bii $p |- ( -. ps <-> ph ) $=
      wph wps wn wph wph wn wps wph notnot con1bii.1 xchbinx bicomi $.
  $}

  ${
    con2bii.1 $e |- ( ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.) $)
    con2bii $p |- ( ps <-> -. ph ) $=
      wph wn wps wps wph wph wps wn con2bii.1 bicomi con1bii bicomi $.
  $}

  $( Contraposition.  Bidirectional version of ~ con1 .  (Contributed by NM,
     5-Aug-1993.) $)
  con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $=
    wph wn wps wi wps wn wph wi wph wps con1 wps wph con1 impbii $.

  $( Contraposition.  Bidirectional version of ~ con2 .  (Contributed by NM,
     5-Aug-1993.) $)
  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    wph wps wn wi wps wph wn wi wph wps con2 wps wph con2 impbii $.

  $( A wff is equivalent to itself with true antecedent.  (Contributed by NM,
     28-Jan-1996.) $)
  biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $=
    wph wps wph wps wi wps wph ax-1 wph wps pm2.27 impbid2 $.

  $( Theorem *5.5 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.5 $p |- ( ph -> ( ( ph -> ps ) <-> ps ) ) $=
    wph wps wph wps wi wph wps biimt bicomd $.

  ${
    a1bi.1 $e |- ph $.
    $( Inference rule introducing a theorem as an antecedent.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
    a1bi $p |- ( ps <-> ( ph -> ps ) ) $=
      wph wps wph wps wi wb a1bi.1 wph wps biimt ax-mp $.
  $}

  ${
    mt2bi.1 $e |- ph $.
    $( A false consequent falsifies an antecedent.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Nov-2012.) $)
    mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $=
      wps wn wph wps wn wi wps wph wn wi wph wps wn mt2bi.1 a1bi wph wps con2b
      bitri $.
  $}

  $( Modus-tollens-like theorem.  (Contributed by NM, 7-Apr-2001.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2012.) $)
  mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $=
    wph wn wps wn wph wn wps wn wi wps wph wi wph wn wps wn biimt wps wph
    con34b syl6bbr $.

  $( Theorem *5.501 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $=
    wph wps wph wps wb wph wps pm5.1im wph wps wb wph wps wph wps bi1 com12
    impbid $.

  $( Implication in terms of implication and biconditional.  (Contributed by
     NM, 31-Mar-1994.)  (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)
  ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $=
    wph wps wph wps wb wph wps pm5.501 pm5.74i $.

  $( Implication in terms of implication and biconditional.  (Contributed by
     NM, 29-Apr-2005.)  (Proof shortened by Wolf Lammen, 21-Dec-2013.) $)
  ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $=
    wph wps wps wph wb wph wps wph wps wb wps wph wb wph wps pm5.501 wph wps
    bicom syl6bb pm5.74i $.

  ${
    tbt.1 $e |- ph $.
    $( A wff is equivalent to its equivalence with truth.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    tbt $p |- ( ps <-> ( ps <-> ph ) ) $=
      wph wps wps wph wb wb tbt.1 wph wps wps wph wb wph wps ibibr pm5.74ri
      ax-mp $.
  $}

  $( The negation of a wff is equivalent to the wff's equivalence to
     falsehood.  (Contributed by Juha Arpiainen, 19-Jan-2006.)  (Proof
     shortened by Wolf Lammen, 28-Jan-2013.) $)
  nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $=
    wph wn wps wn wph wn wps wn wb wph wps wb wph wn wps wn pm5.501 wph wps
    notbi syl6bbr $.

  $( Transfer negation via an equivalence.  (Contributed by NM, 3-Oct-2007.)
     (Proof shortened by Wolf Lammen, 28-Jan-2013.) $)
  bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $=
    wps wn wph wn wps wph wb wph wps wb wps wph nbn2 wps wph bicom syl6rbb $.

  ${
    nbn.1 $e |- -. ph $.
    $( The negation of a wff is equivalent to the wff's equivalence to
       falsehood.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $=
      wps wph wb wps wn wph wn wps wph wb wps wn wb nbn.1 wps wph bibif ax-mp
      bicomi $.
  $}

  ${
    nbn3.1 $e |- ph $.
    $( Transfer falsehood via equivalence.  (Contributed by NM,
       11-Sep-2006.) $)
    nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $=
      wph wn wps wph nbn3.1 notnoti nbn $.
  $}

  $( Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ bi2 -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.) $)
  pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $=
    wph wn wps wn wph wps wb wph wps nbn2 biimpd $.

  ${
    2false.1 $e |- -. ph $.
    2false.2 $e |- -. ps $.
    $( Two falsehoods are equivalent.  (Contributed by NM, 4-Apr-2005.)  (Proof
       shortened by Wolf Lammen, 19-May-2013.) $)
    2false $p |- ( ph <-> ps ) $=
      wph wps wph wn wps wn 2false.1 2false.2 2th con4bii $.
  $}

  ${
    2falsed.1 $e |- ( ph -> -. ps ) $.
    2falsed.2 $e |- ( ph -> -. ch ) $.
    $( Two falsehoods are equivalent (deduction rule).  (Contributed by NM,
       11-Oct-2013.) $)
    2falsed $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wph wps wch 2falsed.1 pm2.21d wph wch wps 2falsed.2 pm2.21d
      impbid $.
  $}

  ${
    pm5.21ni.1 $e |- ( ph -> ps ) $.
    pm5.21ni.2 $e |- ( ch -> ps ) $.
    $( Two propositions implying a false one are equivalent.  (Contributed by
       NM, 16-Feb-1996.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
    pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $=
      wps wn wph wch wph wps pm5.21ni.1 con3i wch wps pm5.21ni.2 con3i 2falsed
      $.

    ${
      pm5.21nii.3 $e |- ( ps -> ( ph <-> ch ) ) $.
      $( Eliminate an antecedent implied by each side of a biconditional.
         (Contributed by NM, 21-May-1999.) $)
      pm5.21nii $p |- ( ph <-> ch ) $=
        wps wph wch wb pm5.21nii.3 wph wps wch pm5.21ni.1 pm5.21ni.2 pm5.21ni
        pm2.61i $.
    $}
  $}

  ${
    pm5.21ndd.1 $e |- ( ph -> ( ch -> ps ) ) $.
    pm5.21ndd.2 $e |- ( ph -> ( th -> ps ) ) $.
    pm5.21ndd.3 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional,
       deduction version.  (Contributed by Paul Chapman, 21-Nov-2012.)  (Proof
       shortened by Wolf Lammen, 6-Oct-2013.) $)
    pm5.21ndd $p |- ( ph -> ( ch <-> th ) ) $=
      wph wps wch wth wb pm5.21ndd.3 wph wps wn wch wn wth wn wch wth wb wph
      wch wps pm5.21ndd.1 con3d wph wth wps pm5.21ndd.2 con3d wch wth pm5.21im
      syl6c pm2.61d $.
  $}

  ${
    bija.1 $e |- ( ph -> ( ps -> ch ) ) $.
    bija.2 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    $( Combine antecedents into a single bi-conditional.  This inference,
       reminiscent of ~ ja , is reversible:  The hypotheses can be deduced from
       the conclusion alone (see ~ pm5.1im and ~ pm5.21im ).  (Contributed by
       Wolf Lammen, 13-May-2013.) $)
    bija $p |- ( ( ph <-> ps ) -> ch ) $=
      wph wps wb wps wch wps wph wps wb wph wch wph wps bi2 bija.1 syli wps wn
      wph wps wb wph wn wch wph wps wb wph wps wph wps bi1 con3d bija.2 syli
      pm2.61d $.
  $}

  $( Theorem *5.18 of [WhiteheadRussell] p. 124.  This theorem says that
     logical equivalence is the same as negated "exclusive-or."  (Contributed
     by NM, 28-Jun-2002.)  (Proof shortened by Andrew Salmon, 20-Jun-2011.)
     (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)
  pm5.18 $p |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) $=
    wph wph wps wb wph wps wn wb wn wb wph wph wps wn wb wn wps wph wps wb wph
    wps wph wps wn wb wph wps wn pm5.501 con1bid wph wps pm5.501 bitr2d wph wn
    wph wps wn wb wn wps wn wph wps wb wph wn wps wn wph wps wn wb wph wps wn
    nbn2 con1bid wph wps nbn2 bitr2d pm2.61i $.

  $( Two ways to express "exclusive or."  (Contributed by NM, 1-Jan-2006.) $)
  xor3 $p |- ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) $=
    wph wps wn wb wph wps wb wn wph wps wb wph wps wn wb wph wps pm5.18 con2bii
    bicomi $.

  $( Move negation outside of biconditional.  Compare Theorem *5.18 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 20-Sep-2013.) $)
  nbbn $p |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) $=
    wph wps wb wn wph wps wn wb wps wph wn wb wph wn wps wb wph wps xor3 wph
    wps con2bi wps wph wn bicom 3bitrri $.

  $( Associative law for the biconditional.  An axiom of system DS in Vladimir
     Lifschitz, "On calculational proofs", Annals of Pure and Applied Logic,
     113:207-224, 2002,
     ~ http://www.cs.utexas.edu/users/ai-lab/pub-view.php?PubID=26805 .
     Interestingly, this law was not included in _Principia Mathematica_ but
     was apparently first noted by Jan Lukasiewicz circa 1923.  (Contributed by
     NM, 8-Jan-2005.)  (Proof shortened by Juha Arpiainen, 19-Jan-2006.)
     (Proof shortened by Wolf Lammen, 21-Sep-2013.) $)
  biass $p |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $=
    wph wph wps wb wch wb wph wps wch wb wb wb wph wps wch wb wph wps wb wch wb
    wph wps wch wb wb wph wps wph wps wb wch wph wps pm5.501 bibi1d wph wps wch
    wb pm5.501 bitr3d wph wn wps wch wb wn wph wps wb wch wb wph wps wch wb wb
    wps wch wb wn wps wn wch wb wph wn wph wps wb wch wb wps wch nbbn wph wn
    wps wn wph wps wb wch wph wps nbn2 bibi1d syl5bbr wph wps wch wb nbn2
    bitr3d pm2.61i $.

  $( Theorem *5.19 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.19 $p |- -. ( ph <-> -. ph ) $=
    wph wph wb wph wph wn wb wn wph biid wph wph pm5.18 mpbi $.

  $( Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122.  (Contributed by NM, 5-Aug-1993.) $)
  bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wps wph wch wi wi wph wps wch pm2.04 wps wph wch pm2.04
    impbii $.

  $( Antecedent absorption implication.  Theorem *5.4 of [WhiteheadRussell]
     p. 125.  (Contributed by NM, 5-Aug-1993.) $)
  pm5.4 $p |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ) $=
    wph wph wps wi wi wph wps wi wph wps pm2.43 wph wps wi wph ax-1 impbii $.

  $( Distributive law for implication.  Compare Theorem *5.41 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 5-Aug-1993.) $)
  imdi $p |- ( ( ph -> ( ps -> ch ) ) <->
               ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wph wps wch ax-2 wph wps wch
    pm2.86 impbii $.

  $( Theorem *5.41 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 12-Oct-2012.) $)
  pm5.41 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) <->
                ( ph -> ( ps -> ch ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wph wps wch imdi bicomi $.

  $( Theorem *4.8 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.8 $p |- ( ( ph -> -. ph ) <-> -. ph ) $=
    wph wph wn wi wph wn wph pm2.01 wph wn wph ax-1 impbii $.

  $( Theorem *4.81 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.81 $p |- ( ( -. ph -> ph ) <-> ph ) $=
    wph wn wph wi wph wph pm2.18 wph wph pm2.24 impbii $.

  $( Simplify an implication between two implications when the antecedent of
     the first is a consequence of the antecedent of the second.  The reverse
     form is useful in producing the successor step in induction proofs.
     (Contributed by Paul Chapman, 22-Jun-2011.)  (Proof shortened by Wolf
     Lammen, 14-Sep-2013.) $)
  imim21b $p |- ( ( ps -> ph ) -> ( ( ( ph -> ch ) -> ( ps -> th ) ) <->
                                    ( ps -> ( ch -> th ) ) ) ) $=
    wph wch wi wps wth wi wi wps wph wch wi wth wi wi wps wph wi wps wch wth wi
    wi wph wch wi wps wth bi2.04 wps wph wi wps wph wch wi wth wi wch wth wi
    wph wph wch wi wth wi wch wth wi wb wps wph wph wch wi wch wth wph wch
    pm5.5 imbi1d imim2i pm5.74d syl5bb $.



