$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_negation.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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
$c <->  $.
$( Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)
$( Extend our wff definition to include the biconditional connective. $)
${
	fwb_0 $f wff ph $.
	fwb_1 $f wff ps $.
	wb $a wff ( ph <-> ps ) $.
$}
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
${
	fdf-bi_0 $f wff ph $.
	fdf-bi_1 $f wff ps $.
	df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.
$}
$( $j justification 'bijust' for 'df-bi'; $)
$( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
${
	fbi1_0 $f wff ph $.
	fbi1_1 $f wff ps $.
	bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $= fbi1_0 fbi1_1 wb fbi1_0 fbi1_1 wi fbi1_1 fbi1_0 wi wn wi wn fbi1_0 fbi1_1 wi fbi1_0 fbi1_1 wb fbi1_0 fbi1_1 wi fbi1_1 fbi1_0 wi wn wi wn wi fbi1_0 fbi1_1 wi fbi1_1 fbi1_0 wi wn wi wn fbi1_0 fbi1_1 wb wi wn wi wn fbi1_0 fbi1_1 wb fbi1_0 fbi1_1 wi fbi1_1 fbi1_0 wi wn wi wn wi fbi1_0 fbi1_1 df-bi fbi1_0 fbi1_1 wb fbi1_0 fbi1_1 wi fbi1_1 fbi1_0 wi wn wi wn wi fbi1_0 fbi1_1 wi fbi1_1 fbi1_0 wi wn wi wn fbi1_0 fbi1_1 wb wi wn simplim ax-mp fbi1_0 fbi1_1 wi fbi1_1 fbi1_0 wi wn simplim syl $.
$}
$( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
${
	fbi3_0 $f wff ph $.
	fbi3_1 $f wff ps $.
	bi3 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $= fbi3_0 fbi3_1 wi fbi3_1 fbi3_0 wi fbi3_0 fbi3_1 wb fbi3_0 fbi3_1 wb fbi3_0 fbi3_1 wi fbi3_1 fbi3_0 wi wn wi wn wi fbi3_0 fbi3_1 wi fbi3_1 fbi3_0 wi wn wi wn fbi3_0 fbi3_1 wb wi wn wi wn fbi3_0 fbi3_1 wi fbi3_1 fbi3_0 wi wn wi wn fbi3_0 fbi3_1 wb wi fbi3_0 fbi3_1 df-bi fbi3_0 fbi3_1 wb fbi3_0 fbi3_1 wi fbi3_1 fbi3_0 wi wn wi wn wi fbi3_0 fbi3_1 wi fbi3_1 fbi3_0 wi wn wi wn fbi3_0 fbi3_1 wb wi simprim ax-mp expi $.
$}
$( Infer an equivalence from an implication and its converse.  (Contributed
       by NM, 5-Aug-1993.) $)
${
	fimpbii_0 $f wff ph $.
	fimpbii_1 $f wff ps $.
	eimpbii_0 $e |- ( ph -> ps ) $.
	eimpbii_1 $e |- ( ps -> ph ) $.
	impbii $p |- ( ph <-> ps ) $= fimpbii_0 fimpbii_1 wi fimpbii_1 fimpbii_0 wi fimpbii_0 fimpbii_1 wb eimpbii_0 eimpbii_1 fimpbii_0 fimpbii_1 bi3 mp2 $.
$}
$( Deduce an equivalence from two implications.  (Contributed by Rodolfo
       Medina, 12-Oct-2010.) $)
${
	fimpbidd_0 $f wff ph $.
	fimpbidd_1 $f wff ps $.
	fimpbidd_2 $f wff ch $.
	fimpbidd_3 $f wff th $.
	eimpbidd_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	eimpbidd_1 $e |- ( ph -> ( ps -> ( th -> ch ) ) ) $.
	impbidd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $= fimpbidd_0 fimpbidd_1 fimpbidd_2 fimpbidd_3 wi fimpbidd_3 fimpbidd_2 wi fimpbidd_2 fimpbidd_3 wb eimpbidd_0 eimpbidd_1 fimpbidd_2 fimpbidd_3 bi3 syl6c $.
$}
$( Deduce an equivalence from two implications.  (Contributed by Wolf
       Lammen, 12-May-2013.) $)
${
	fimpbid21d_0 $f wff ph $.
	fimpbid21d_1 $f wff ps $.
	fimpbid21d_2 $f wff ch $.
	fimpbid21d_3 $f wff th $.
	eimpbid21d_0 $e |- ( ps -> ( ch -> th ) ) $.
	eimpbid21d_1 $e |- ( ph -> ( th -> ch ) ) $.
	impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $= fimpbid21d_0 fimpbid21d_1 fimpbid21d_2 fimpbid21d_3 fimpbid21d_1 fimpbid21d_2 fimpbid21d_3 wi wi fimpbid21d_0 eimpbid21d_0 a1i fimpbid21d_0 fimpbid21d_3 fimpbid21d_2 wi fimpbid21d_1 eimpbid21d_1 a1d impbidd $.
$}
$( Deduce an equivalence from two implications.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Wolf Lammen, 3-Nov-2012.) $)
${
	fimpbid_0 $f wff ph $.
	fimpbid_1 $f wff ps $.
	fimpbid_2 $f wff ch $.
	eimpbid_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eimpbid_1 $e |- ( ph -> ( ch -> ps ) ) $.
	impbid $p |- ( ph -> ( ps <-> ch ) ) $= fimpbid_0 fimpbid_1 fimpbid_2 wb fimpbid_0 fimpbid_0 fimpbid_1 fimpbid_2 eimpbid_0 eimpbid_1 impbid21d pm2.43i $.
$}
$( Relate the biconditional connective to primitive connectives.  See
     ~ dfbi1gb for an unusual version proved directly from axioms.
     (Contributed by NM, 5-Aug-1993.) $)
${
	fdfbi1_0 $f wff ph $.
	fdfbi1_1 $f wff ps $.
	dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $= fdfbi1_0 fdfbi1_1 wb fdfbi1_0 fdfbi1_1 wi fdfbi1_1 fdfbi1_0 wi wn wi wn fdfbi1_0 fdfbi1_1 wb fdfbi1_0 fdfbi1_1 wi fdfbi1_1 fdfbi1_0 wi wn wi wn wi fdfbi1_0 fdfbi1_1 wi fdfbi1_1 fdfbi1_0 wi wn wi wn fdfbi1_0 fdfbi1_1 wb wi wn wi wn fdfbi1_0 fdfbi1_1 wb fdfbi1_0 fdfbi1_1 wi fdfbi1_1 fdfbi1_0 wi wn wi wn wi fdfbi1_0 fdfbi1_1 df-bi fdfbi1_0 fdfbi1_1 wb fdfbi1_0 fdfbi1_1 wi fdfbi1_1 fdfbi1_0 wi wn wi wn wi fdfbi1_0 fdfbi1_1 wi fdfbi1_1 fdfbi1_0 wi wn wi wn fdfbi1_0 fdfbi1_1 wb wi wn simplim ax-mp fdfbi1_0 fdfbi1_1 wi fdfbi1_1 fdfbi1_0 wi fdfbi1_0 fdfbi1_1 wb fdfbi1_0 fdfbi1_1 bi3 impi impbii $.
$}
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
${
	idfbi1gb_0 $f wff ch $.
	idfbi1gb_1 $f wff th $.
	fdfbi1gb_0 $f wff ph $.
	fdfbi1gb_1 $f wff ps $.
	dfbi1gb $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $= fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 df-bi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi idfbi1gb_0 idfbi1gb_1 ax-1 fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi ax-1 fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wi wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wi wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wi wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi wn idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn df-bi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi wn idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wn ax-1 ax-mp idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi ax-3 ax-mp fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn ax-1 ax-mp fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi wn wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi wn ax-2 ax-mp ax-mp fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wi fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb wi wn wi wn fdfbi1gb_0 fdfbi1gb_1 wb fdfbi1gb_0 fdfbi1gb_1 wi fdfbi1gb_1 fdfbi1gb_0 wi wn wi wn wb wi idfbi1gb_0 idfbi1gb_1 idfbi1gb_0 wi wi ax-3 ax-mp ax-mp ax-mp $.
$}
$( Infer an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fbiimpi_0 $f wff ph $.
	fbiimpi_1 $f wff ps $.
	ebiimpi_0 $e |- ( ph <-> ps ) $.
	biimpi $p |- ( ph -> ps ) $= fbiimpi_0 fbiimpi_1 wb fbiimpi_0 fbiimpi_1 wi ebiimpi_0 fbiimpi_0 fbiimpi_1 bi1 ax-mp $.
$}
$( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by NM, 5-Aug-1993.) $)
${
	fsylbi_0 $f wff ph $.
	fsylbi_1 $f wff ps $.
	fsylbi_2 $f wff ch $.
	esylbi_0 $e |- ( ph <-> ps ) $.
	esylbi_1 $e |- ( ps -> ch ) $.
	sylbi $p |- ( ph -> ch ) $= fsylbi_0 fsylbi_1 fsylbi_2 fsylbi_0 fsylbi_1 esylbi_0 biimpi esylbi_1 syl $.
$}
$( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fsylib_0 $f wff ph $.
	fsylib_1 $f wff ps $.
	fsylib_2 $f wff ch $.
	esylib_0 $e |- ( ph -> ps ) $.
	esylib_1 $e |- ( ps <-> ch ) $.
	sylib $p |- ( ph -> ch ) $= fsylib_0 fsylib_1 fsylib_2 esylib_0 fsylib_1 fsylib_2 esylib_1 biimpi syl $.
$}
$( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
${
	fbi2_0 $f wff ph $.
	fbi2_1 $f wff ps $.
	bi2 $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $= fbi2_0 fbi2_1 wb fbi2_0 fbi2_1 wi fbi2_1 fbi2_0 wi wn wi wn fbi2_1 fbi2_0 wi fbi2_0 fbi2_1 dfbi1 fbi2_0 fbi2_1 wi fbi2_1 fbi2_0 wi simprim sylbi $.
$}
$( Commutative law for equivalence.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)
${
	fbicom1_0 $f wff ph $.
	fbicom1_1 $f wff ps $.
	bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $= fbicom1_0 fbicom1_1 wb fbicom1_1 fbicom1_0 fbicom1_0 fbicom1_1 bi2 fbicom1_0 fbicom1_1 bi1 impbid $.
$}
$( Commutative law for equivalence.  Theorem *4.21 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.) $)
${
	fbicom_0 $f wff ph $.
	fbicom_1 $f wff ps $.
	bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $= fbicom_0 fbicom_1 wb fbicom_1 fbicom_0 wb fbicom_0 fbicom_1 bicom1 fbicom_1 fbicom_0 bicom1 impbii $.
$}
$( Commute two sides of a biconditional in a deduction.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	fbicomd_0 $f wff ph $.
	fbicomd_1 $f wff ps $.
	fbicomd_2 $f wff ch $.
	ebicomd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	bicomd $p |- ( ph -> ( ch <-> ps ) ) $= fbicomd_0 fbicomd_1 fbicomd_2 wb fbicomd_2 fbicomd_1 wb ebicomd_0 fbicomd_1 fbicomd_2 bicom sylib $.
$}
$( Inference from commutative law for logical equivalence.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	fbicomi_0 $f wff ph $.
	fbicomi_1 $f wff ps $.
	ebicomi_0 $e |- ( ph <-> ps ) $.
	bicomi $p |- ( ps <-> ph ) $= fbicomi_0 fbicomi_1 wb fbicomi_1 fbicomi_0 wb ebicomi_0 fbicomi_0 fbicomi_1 bicom1 ax-mp $.
$}
$( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.) $)
${
	fimpbid1_0 $f wff ph $.
	fimpbid1_1 $f wff ps $.
	fimpbid1_2 $f wff ch $.
	eimpbid1_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eimpbid1_1 $e |- ( ch -> ps ) $.
	impbid1 $p |- ( ph -> ( ps <-> ch ) ) $= fimpbid1_0 fimpbid1_1 fimpbid1_2 eimpbid1_0 fimpbid1_2 fimpbid1_1 wi fimpbid1_0 eimpbid1_1 a1i impbid $.
$}
$( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.)  (Proof shortened by Wolf Lammen, 27-Sep-2013.) $)
${
	fimpbid2_0 $f wff ph $.
	fimpbid2_1 $f wff ps $.
	fimpbid2_2 $f wff ch $.
	eimpbid2_0 $e |- ( ps -> ch ) $.
	eimpbid2_1 $e |- ( ph -> ( ch -> ps ) ) $.
	impbid2 $p |- ( ph -> ( ps <-> ch ) ) $= fimpbid2_0 fimpbid2_2 fimpbid2_1 fimpbid2_0 fimpbid2_2 fimpbid2_1 eimpbid2_1 eimpbid2_0 impbid1 bicomd $.
$}
$( A variation on ~ impbid with contraposition.  (Contributed by Jeff
       Hankins, 3-Jul-2009.) $)
${
	fimpcon4bid_0 $f wff ph $.
	fimpcon4bid_1 $f wff ps $.
	fimpcon4bid_2 $f wff ch $.
	eimpcon4bid_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eimpcon4bid_1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
	impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $= fimpcon4bid_0 fimpcon4bid_1 fimpcon4bid_2 eimpcon4bid_0 fimpcon4bid_0 fimpcon4bid_1 fimpcon4bid_2 eimpcon4bid_1 con4d impbid $.
$}
$( Infer a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 16-Sep-2013.) $)
${
	fbiimpri_0 $f wff ph $.
	fbiimpri_1 $f wff ps $.
	ebiimpri_0 $e |- ( ph <-> ps ) $.
	biimpri $p |- ( ps -> ph ) $= fbiimpri_1 fbiimpri_0 fbiimpri_0 fbiimpri_1 ebiimpri_0 bicomi biimpi $.
$}
$( Deduce an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fbiimpd_0 $f wff ph $.
	fbiimpd_1 $f wff ps $.
	fbiimpd_2 $f wff ch $.
	ebiimpd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	biimpd $p |- ( ph -> ( ps -> ch ) ) $= fbiimpd_0 fbiimpd_1 fbiimpd_2 wb fbiimpd_1 fbiimpd_2 wi ebiimpd_0 fbiimpd_1 fbiimpd_2 bi1 syl $.
$}
$( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fmpbi_0 $f wff ph $.
	fmpbi_1 $f wff ps $.
	empbi_0 $e |- ph $.
	empbi_1 $e |- ( ph <-> ps ) $.
	mpbi $p |- ps $= fmpbi_0 fmpbi_1 empbi_0 fmpbi_0 fmpbi_1 empbi_1 biimpi ax-mp $.
$}
$( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fmpbir_0 $f wff ph $.
	fmpbir_1 $f wff ps $.
	empbir_0 $e |- ps $.
	empbir_1 $e |- ( ph <-> ps ) $.
	mpbir $p |- ph $= fmpbir_1 fmpbir_0 empbir_0 fmpbir_0 fmpbir_1 empbir_1 biimpri ax-mp $.
$}
$( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)
${
	fmpbid_0 $f wff ph $.
	fmpbid_1 $f wff ps $.
	fmpbid_2 $f wff ch $.
	empbid_0 $e |- ( ph -> ps ) $.
	empbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mpbid $p |- ( ph -> ch ) $= fmpbid_0 fmpbid_1 fmpbid_2 empbid_0 fmpbid_0 fmpbid_1 fmpbid_2 empbid_1 biimpd mpd $.
$}
$( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
${
	fmpbii_0 $f wff ph $.
	fmpbii_1 $f wff ps $.
	fmpbii_2 $f wff ch $.
	empbii_0 $e |- ps $.
	empbii_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mpbii $p |- ( ph -> ch ) $= fmpbii_0 fmpbii_1 fmpbii_2 fmpbii_1 fmpbii_0 empbii_0 a1i empbii_1 mpbid $.
$}
$( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	fsylibr_0 $f wff ph $.
	fsylibr_1 $f wff ps $.
	fsylibr_2 $f wff ch $.
	esylibr_0 $e |- ( ph -> ps ) $.
	esylibr_1 $e |- ( ch <-> ps ) $.
	sylibr $p |- ( ph -> ch ) $= fsylibr_0 fsylibr_1 fsylibr_2 esylibr_0 fsylibr_2 fsylibr_1 esylibr_1 biimpri syl $.
$}
$( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fsylbir_0 $f wff ph $.
	fsylbir_1 $f wff ps $.
	fsylbir_2 $f wff ch $.
	esylbir_0 $e |- ( ps <-> ph ) $.
	esylbir_1 $e |- ( ps -> ch ) $.
	sylbir $p |- ( ph -> ch ) $= fsylbir_0 fsylbir_1 fsylbir_2 fsylbir_1 fsylbir_0 esylbir_0 biimpri esylbir_1 syl $.
$}
$( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
${
	fsylibd_0 $f wff ph $.
	fsylibd_1 $f wff ps $.
	fsylibd_2 $f wff ch $.
	fsylibd_3 $f wff th $.
	esylibd_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esylibd_1 $e |- ( ph -> ( ch <-> th ) ) $.
	sylibd $p |- ( ph -> ( ps -> th ) ) $= fsylibd_0 fsylibd_1 fsylibd_2 fsylibd_3 esylibd_0 fsylibd_0 fsylibd_2 fsylibd_3 esylibd_1 biimpd syld $.
$}
$( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
${
	fsylbid_0 $f wff ph $.
	fsylbid_1 $f wff ps $.
	fsylbid_2 $f wff ch $.
	fsylbid_3 $f wff th $.
	esylbid_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esylbid_1 $e |- ( ph -> ( ch -> th ) ) $.
	sylbid $p |- ( ph -> ( ps -> th ) ) $= fsylbid_0 fsylbid_1 fsylbid_2 fsylbid_3 fsylbid_0 fsylbid_1 fsylbid_2 esylbid_0 biimpd esylbid_1 syld $.
$}
$( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 9-Aug-1994.) $)
${
	fmpbidi_0 $f wff ph $.
	fmpbidi_1 $f wff ps $.
	fmpbidi_2 $f wff ch $.
	fmpbidi_3 $f wff th $.
	empbidi_0 $e |- ( th -> ( ph -> ps ) ) $.
	empbidi_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mpbidi $p |- ( th -> ( ph -> ch ) ) $= fmpbidi_3 fmpbidi_0 fmpbidi_1 fmpbidi_2 empbidi_0 fmpbidi_0 fmpbidi_1 fmpbidi_2 empbidi_1 biimpd sylcom $.
$}
$( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsyl5bi_0 $f wff ph $.
	fsyl5bi_1 $f wff ps $.
	fsyl5bi_2 $f wff ch $.
	fsyl5bi_3 $f wff th $.
	esyl5bi_0 $e |- ( ph <-> ps ) $.
	esyl5bi_1 $e |- ( ch -> ( ps -> th ) ) $.
	syl5bi $p |- ( ch -> ( ph -> th ) ) $= fsyl5bi_0 fsyl5bi_1 fsyl5bi_2 fsyl5bi_3 fsyl5bi_0 fsyl5bi_1 esyl5bi_0 biimpi esyl5bi_1 syl5 $.
$}
$( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsyl5bir_0 $f wff ph $.
	fsyl5bir_1 $f wff ps $.
	fsyl5bir_2 $f wff ch $.
	fsyl5bir_3 $f wff th $.
	esyl5bir_0 $e |- ( ps <-> ph ) $.
	esyl5bir_1 $e |- ( ch -> ( ps -> th ) ) $.
	syl5bir $p |- ( ch -> ( ph -> th ) ) $= fsyl5bir_0 fsyl5bir_1 fsyl5bir_2 fsyl5bir_3 fsyl5bir_1 fsyl5bir_0 esyl5bir_0 biimpri esyl5bir_1 syl5 $.
$}
$( A mixed syllogism inference.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsyl5ib_0 $f wff ph $.
	fsyl5ib_1 $f wff ps $.
	fsyl5ib_2 $f wff ch $.
	fsyl5ib_3 $f wff th $.
	esyl5ib_0 $e |- ( ph -> ps ) $.
	esyl5ib_1 $e |- ( ch -> ( ps <-> th ) ) $.
	syl5ib $p |- ( ch -> ( ph -> th ) ) $= fsyl5ib_0 fsyl5ib_1 fsyl5ib_2 fsyl5ib_3 esyl5ib_0 fsyl5ib_2 fsyl5ib_1 fsyl5ib_3 esyl5ib_1 biimpd syl5 $.
$}
$( A mixed syllogism inference.  (Contributed by NM, 19-Jun-2007.) $)
${
	fsyl5ibcom_0 $f wff ph $.
	fsyl5ibcom_1 $f wff ps $.
	fsyl5ibcom_2 $f wff ch $.
	fsyl5ibcom_3 $f wff th $.
	esyl5ibcom_0 $e |- ( ph -> ps ) $.
	esyl5ibcom_1 $e |- ( ch -> ( ps <-> th ) ) $.
	syl5ibcom $p |- ( ph -> ( ch -> th ) ) $= fsyl5ibcom_2 fsyl5ibcom_0 fsyl5ibcom_3 fsyl5ibcom_0 fsyl5ibcom_1 fsyl5ibcom_2 fsyl5ibcom_3 esyl5ibcom_0 esyl5ibcom_1 syl5ib com12 $.
$}
$( A mixed syllogism inference.  (Contributed by NM, 3-Apr-1994.) $)
${
	fsyl5ibr_0 $f wff ph $.
	fsyl5ibr_1 $f wff ps $.
	fsyl5ibr_2 $f wff ch $.
	fsyl5ibr_3 $f wff th $.
	esyl5ibr_0 $e |- ( ph -> th ) $.
	esyl5ibr_1 $e |- ( ch -> ( ps <-> th ) ) $.
	syl5ibr $p |- ( ch -> ( ph -> ps ) ) $= fsyl5ibr_0 fsyl5ibr_3 fsyl5ibr_2 fsyl5ibr_1 esyl5ibr_0 fsyl5ibr_2 fsyl5ibr_1 fsyl5ibr_3 esyl5ibr_1 bicomd syl5ib $.
$}
$( A mixed syllogism inference.  (Contributed by NM, 20-Jun-2007.) $)
${
	fsyl5ibrcom_0 $f wff ph $.
	fsyl5ibrcom_1 $f wff ps $.
	fsyl5ibrcom_2 $f wff ch $.
	fsyl5ibrcom_3 $f wff th $.
	esyl5ibrcom_0 $e |- ( ph -> th ) $.
	esyl5ibrcom_1 $e |- ( ch -> ( ps <-> th ) ) $.
	syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $= fsyl5ibrcom_2 fsyl5ibrcom_0 fsyl5ibrcom_1 fsyl5ibrcom_0 fsyl5ibrcom_1 fsyl5ibrcom_2 fsyl5ibrcom_3 esyl5ibrcom_0 esyl5ibrcom_1 syl5ibr com12 $.
$}
$( Deduce a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
${
	fbiimprd_0 $f wff ph $.
	fbiimprd_1 $f wff ps $.
	fbiimprd_2 $f wff ch $.
	ebiimprd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	biimprd $p |- ( ph -> ( ch -> ps ) ) $= fbiimprd_2 fbiimprd_1 fbiimprd_0 fbiimprd_2 fbiimprd_2 id ebiimprd_0 syl5ibr $.
$}
$( Deduce a commuted implication from a logical equivalence.  (Contributed
       by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
${
	fbiimpcd_0 $f wff ph $.
	fbiimpcd_1 $f wff ps $.
	fbiimpcd_2 $f wff ch $.
	ebiimpcd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	biimpcd $p |- ( ps -> ( ph -> ch ) ) $= fbiimpcd_1 fbiimpcd_1 fbiimpcd_0 fbiimpcd_2 fbiimpcd_1 id ebiimpcd_0 syl5ibcom $.
$}
$( Deduce a converse commuted implication from a logical equivalence.
       (Contributed by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen,
       20-Dec-2013.) $)
${
	fbiimprcd_0 $f wff ph $.
	fbiimprcd_1 $f wff ps $.
	fbiimprcd_2 $f wff ch $.
	ebiimprcd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	biimprcd $p |- ( ch -> ( ph -> ps ) ) $= fbiimprcd_2 fbiimprcd_1 fbiimprcd_0 fbiimprcd_2 fbiimprcd_2 id ebiimprcd_0 syl5ibrcom $.
$}
$( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsyl6ib_0 $f wff ph $.
	fsyl6ib_1 $f wff ps $.
	fsyl6ib_2 $f wff ch $.
	fsyl6ib_3 $f wff th $.
	esyl6ib_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl6ib_1 $e |- ( ch <-> th ) $.
	syl6ib $p |- ( ph -> ( ps -> th ) ) $= fsyl6ib_0 fsyl6ib_1 fsyl6ib_2 fsyl6ib_3 esyl6ib_0 fsyl6ib_2 fsyl6ib_3 esyl6ib_1 biimpi syl6 $.
$}
$( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsyl6ibr_0 $f wff ph $.
	fsyl6ibr_1 $f wff ps $.
	fsyl6ibr_2 $f wff ch $.
	fsyl6ibr_3 $f wff th $.
	esyl6ibr_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl6ibr_1 $e |- ( th <-> ch ) $.
	syl6ibr $p |- ( ph -> ( ps -> th ) ) $= fsyl6ibr_0 fsyl6ibr_1 fsyl6ibr_2 fsyl6ibr_3 esyl6ibr_0 fsyl6ibr_3 fsyl6ibr_2 esyl6ibr_1 biimpri syl6 $.
$}
$( A mixed syllogism inference.  (Contributed by NM, 2-Jan-1994.) $)
${
	fsyl6bi_0 $f wff ph $.
	fsyl6bi_1 $f wff ps $.
	fsyl6bi_2 $f wff ch $.
	fsyl6bi_3 $f wff th $.
	esyl6bi_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esyl6bi_1 $e |- ( ch -> th ) $.
	syl6bi $p |- ( ph -> ( ps -> th ) ) $= fsyl6bi_0 fsyl6bi_1 fsyl6bi_2 fsyl6bi_3 fsyl6bi_0 fsyl6bi_1 fsyl6bi_2 esyl6bi_0 biimpd esyl6bi_1 syl6 $.
$}
$( A mixed syllogism inference.  (Contributed by NM, 18-May-1994.) $)
${
	fsyl6bir_0 $f wff ph $.
	fsyl6bir_1 $f wff ps $.
	fsyl6bir_2 $f wff ch $.
	fsyl6bir_3 $f wff th $.
	esyl6bir_0 $e |- ( ph -> ( ch <-> ps ) ) $.
	esyl6bir_1 $e |- ( ch -> th ) $.
	syl6bir $p |- ( ph -> ( ps -> th ) ) $= fsyl6bir_0 fsyl6bir_1 fsyl6bir_2 fsyl6bir_3 fsyl6bir_0 fsyl6bir_2 fsyl6bir_1 esyl6bir_0 biimprd esyl6bir_1 syl6 $.
$}
$( A mixed syllogism inference from a doubly nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsyl7bi_0 $f wff ph $.
	fsyl7bi_1 $f wff ps $.
	fsyl7bi_2 $f wff ch $.
	fsyl7bi_3 $f wff th $.
	fsyl7bi_4 $f wff ta $.
	esyl7bi_0 $e |- ( ph <-> ps ) $.
	esyl7bi_1 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
	syl7bi $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $= fsyl7bi_0 fsyl7bi_1 fsyl7bi_2 fsyl7bi_3 fsyl7bi_4 fsyl7bi_0 fsyl7bi_1 esyl7bi_0 biimpi esyl7bi_1 syl7 $.
$}
$( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM,
       1-Aug-1994.) $)
${
	fsyl8ib_0 $f wff ph $.
	fsyl8ib_1 $f wff ps $.
	fsyl8ib_2 $f wff ch $.
	fsyl8ib_3 $f wff th $.
	fsyl8ib_4 $f wff ta $.
	esyl8ib_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	esyl8ib_1 $e |- ( th <-> ta ) $.
	syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= fsyl8ib_0 fsyl8ib_1 fsyl8ib_2 fsyl8ib_3 fsyl8ib_4 esyl8ib_0 fsyl8ib_3 fsyl8ib_4 esyl8ib_1 biimpi syl8 $.
$}
$( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)
${
	fmpbird_0 $f wff ph $.
	fmpbird_1 $f wff ps $.
	fmpbird_2 $f wff ch $.
	empbird_0 $e |- ( ph -> ch ) $.
	empbird_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mpbird $p |- ( ph -> ps ) $= fmpbird_0 fmpbird_2 fmpbird_1 empbird_0 fmpbird_0 fmpbird_1 fmpbird_2 empbird_1 biimprd mpd $.
$}
$( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
${
	fmpbiri_0 $f wff ph $.
	fmpbiri_1 $f wff ps $.
	fmpbiri_2 $f wff ch $.
	empbiri_0 $e |- ch $.
	empbiri_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mpbiri $p |- ( ph -> ps ) $= fmpbiri_0 fmpbiri_1 fmpbiri_2 fmpbiri_2 fmpbiri_0 empbiri_0 a1i empbiri_1 mpbird $.
$}
$( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
${
	fsylibrd_0 $f wff ph $.
	fsylibrd_1 $f wff ps $.
	fsylibrd_2 $f wff ch $.
	fsylibrd_3 $f wff th $.
	esylibrd_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esylibrd_1 $e |- ( ph -> ( th <-> ch ) ) $.
	sylibrd $p |- ( ph -> ( ps -> th ) ) $= fsylibrd_0 fsylibrd_1 fsylibrd_2 fsylibrd_3 esylibrd_0 fsylibrd_0 fsylibrd_3 fsylibrd_2 esylibrd_1 biimprd syld $.
$}
$( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
${
	fsylbird_0 $f wff ph $.
	fsylbird_1 $f wff ps $.
	fsylbird_2 $f wff ch $.
	fsylbird_3 $f wff th $.
	esylbird_0 $e |- ( ph -> ( ch <-> ps ) ) $.
	esylbird_1 $e |- ( ph -> ( ch -> th ) ) $.
	sylbird $p |- ( ph -> ( ps -> th ) ) $= fsylbird_0 fsylbird_1 fsylbird_2 fsylbird_3 fsylbird_0 fsylbird_2 fsylbird_1 esylbird_0 biimprd esylbird_1 syld $.
$}
$( Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 5-Aug-1993.) $)
${
	fbiid_0 $f wff ph $.
	biid $p |- ( ph <-> ph ) $= fbiid_0 fbiid_0 fbiid_0 id fbiid_0 id impbii $.
$}
$( Principle of identity with antecedent.  (Contributed by NM,
     25-Nov-1995.) $)
${
	fbiidd_0 $f wff ph $.
	fbiidd_1 $f wff ps $.
	biidd $p |- ( ph -> ( ps <-> ps ) ) $= fbiidd_1 fbiidd_1 wb fbiidd_0 fbiidd_1 biid a1i $.
$}
$( Two propositions are equivalent if they are both true.  Closed form of
     ~ 2th .  Equivalent to a ~ bi1 -like version of the xor-connective.  This
     theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version
     ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .  (Contributed by Wolf Lammen,
     12-May-2013.) $)
${
	fpm5.1im_0 $f wff ph $.
	fpm5.1im_1 $f wff ps $.
	pm5.1im $p |- ( ph -> ( ps -> ( ph <-> ps ) ) ) $= fpm5.1im_0 fpm5.1im_1 fpm5.1im_0 fpm5.1im_1 fpm5.1im_1 fpm5.1im_0 ax-1 fpm5.1im_0 fpm5.1im_1 ax-1 impbid21d $.
$}
$( Two truths are equivalent.  (Contributed by NM, 18-Aug-1993.) $)
${
	f2th_0 $f wff ph $.
	f2th_1 $f wff ps $.
	e2th_0 $e |- ph $.
	e2th_1 $e |- ps $.
	2th $p |- ( ph <-> ps ) $= f2th_0 f2th_1 f2th_1 f2th_0 e2th_1 a1i f2th_0 f2th_1 e2th_0 a1i impbii $.
$}
$( Two truths are equivalent (deduction rule).  (Contributed by NM,
       3-Jun-2012.) $)
${
	f2thd_0 $f wff ph $.
	f2thd_1 $f wff ps $.
	f2thd_2 $f wff ch $.
	e2thd_0 $e |- ( ph -> ps ) $.
	e2thd_1 $e |- ( ph -> ch ) $.
	2thd $p |- ( ph -> ( ps <-> ch ) ) $= f2thd_0 f2thd_1 f2thd_2 f2thd_1 f2thd_2 wb e2thd_0 e2thd_1 f2thd_1 f2thd_2 pm5.1im sylc $.
$}
$( Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 17-Oct-2003.) $)
${
	fibi_0 $f wff ph $.
	fibi_1 $f wff ps $.
	eibi_0 $e |- ( ph -> ( ph <-> ps ) ) $.
	ibi $p |- ( ph -> ps ) $= fibi_0 fibi_1 fibi_0 fibi_0 fibi_1 eibi_0 biimpd pm2.43i $.
$}
$( Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 22-Jul-2004.) $)
${
	fibir_0 $f wff ph $.
	fibir_1 $f wff ps $.
	eibir_0 $e |- ( ph -> ( ps <-> ph ) ) $.
	ibir $p |- ( ph -> ps ) $= fibir_0 fibir_1 fibir_0 fibir_1 fibir_0 eibir_0 bicomd ibi $.
$}
$( Deduction that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 26-Jun-2004.) $)
${
	fibd_0 $f wff ph $.
	fibd_1 $f wff ps $.
	fibd_2 $f wff ch $.
	eibd_0 $e |- ( ph -> ( ps -> ( ps <-> ch ) ) ) $.
	ibd $p |- ( ph -> ( ps -> ch ) ) $= fibd_1 fibd_0 fibd_1 fibd_2 wb fibd_2 eibd_0 fibd_1 fibd_2 bi1 syli $.
$}
$( Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126.  (Contributed by NM, 1-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 11-Apr-2013.) $)
${
	fpm5.74_0 $f wff ph $.
	fpm5.74_1 $f wff ps $.
	fpm5.74_2 $f wff ch $.
	pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $= fpm5.74_0 fpm5.74_1 fpm5.74_2 wb wi fpm5.74_0 fpm5.74_1 wi fpm5.74_0 fpm5.74_2 wi wb fpm5.74_0 fpm5.74_1 fpm5.74_2 wb wi fpm5.74_0 fpm5.74_1 wi fpm5.74_0 fpm5.74_2 wi fpm5.74_1 fpm5.74_2 wb fpm5.74_1 fpm5.74_2 fpm5.74_0 fpm5.74_1 fpm5.74_2 bi1 imim3i fpm5.74_1 fpm5.74_2 wb fpm5.74_2 fpm5.74_1 fpm5.74_0 fpm5.74_1 fpm5.74_2 bi2 imim3i impbid fpm5.74_0 fpm5.74_1 wi fpm5.74_0 fpm5.74_2 wi wb fpm5.74_0 fpm5.74_1 fpm5.74_2 fpm5.74_0 fpm5.74_1 wi fpm5.74_0 fpm5.74_2 wi wb fpm5.74_0 fpm5.74_1 fpm5.74_2 fpm5.74_0 fpm5.74_1 wi fpm5.74_0 fpm5.74_2 wi bi1 pm2.86d fpm5.74_0 fpm5.74_1 wi fpm5.74_0 fpm5.74_2 wi wb fpm5.74_0 fpm5.74_2 fpm5.74_1 fpm5.74_0 fpm5.74_1 wi fpm5.74_0 fpm5.74_2 wi bi2 pm2.86d impbidd impbii $.
$}
$( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 1-Aug-1994.) $)
${
	fpm5.74i_0 $f wff ph $.
	fpm5.74i_1 $f wff ps $.
	fpm5.74i_2 $f wff ch $.
	epm5.74i_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $= fpm5.74i_0 fpm5.74i_1 fpm5.74i_2 wb wi fpm5.74i_0 fpm5.74i_1 wi fpm5.74i_0 fpm5.74i_2 wi wb epm5.74i_0 fpm5.74i_0 fpm5.74i_1 fpm5.74i_2 pm5.74 mpbi $.
$}
$( Distribution of implication over biconditional (reverse inference
       rule).  (Contributed by NM, 1-Aug-1994.) $)
${
	fpm5.74ri_0 $f wff ph $.
	fpm5.74ri_1 $f wff ps $.
	fpm5.74ri_2 $f wff ch $.
	epm5.74ri_0 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
	pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $= fpm5.74ri_0 fpm5.74ri_1 fpm5.74ri_2 wb wi fpm5.74ri_0 fpm5.74ri_1 wi fpm5.74ri_0 fpm5.74ri_2 wi wb epm5.74ri_0 fpm5.74ri_0 fpm5.74ri_1 fpm5.74ri_2 pm5.74 mpbir $.
$}
$( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 21-Mar-1996.) $)
${
	fpm5.74d_0 $f wff ph $.
	fpm5.74d_1 $f wff ps $.
	fpm5.74d_2 $f wff ch $.
	fpm5.74d_3 $f wff th $.
	epm5.74d_0 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
	pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $= fpm5.74d_0 fpm5.74d_1 fpm5.74d_2 fpm5.74d_3 wb wi fpm5.74d_1 fpm5.74d_2 wi fpm5.74d_1 fpm5.74d_3 wi wb epm5.74d_0 fpm5.74d_1 fpm5.74d_2 fpm5.74d_3 pm5.74 sylib $.
$}
$( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 19-Mar-1997.) $)
${
	fpm5.74rd_0 $f wff ph $.
	fpm5.74rd_1 $f wff ps $.
	fpm5.74rd_2 $f wff ch $.
	fpm5.74rd_3 $f wff th $.
	epm5.74rd_0 $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
	pm5.74rd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $= fpm5.74rd_0 fpm5.74rd_1 fpm5.74rd_2 wi fpm5.74rd_1 fpm5.74rd_3 wi wb fpm5.74rd_1 fpm5.74rd_2 fpm5.74rd_3 wb wi epm5.74rd_0 fpm5.74rd_1 fpm5.74rd_2 fpm5.74rd_3 pm5.74 sylibr $.
$}
$( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Oct-2012.) $)
${
	fbitri_0 $f wff ph $.
	fbitri_1 $f wff ps $.
	fbitri_2 $f wff ch $.
	ebitri_0 $e |- ( ph <-> ps ) $.
	ebitri_1 $e |- ( ps <-> ch ) $.
	bitri $p |- ( ph <-> ch ) $= fbitri_0 fbitri_2 fbitri_0 fbitri_1 fbitri_2 fbitri_0 fbitri_1 ebitri_0 biimpi ebitri_1 sylib fbitri_2 fbitri_1 fbitri_0 fbitri_1 fbitri_2 ebitri_1 biimpri ebitri_0 sylibr impbii $.
$}
$( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
${
	fbitr2i_0 $f wff ph $.
	fbitr2i_1 $f wff ps $.
	fbitr2i_2 $f wff ch $.
	ebitr2i_0 $e |- ( ph <-> ps ) $.
	ebitr2i_1 $e |- ( ps <-> ch ) $.
	bitr2i $p |- ( ch <-> ph ) $= fbitr2i_0 fbitr2i_2 fbitr2i_0 fbitr2i_1 fbitr2i_2 ebitr2i_0 ebitr2i_1 bitri bicomi $.
$}
$( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
${
	fbitr3i_0 $f wff ph $.
	fbitr3i_1 $f wff ps $.
	fbitr3i_2 $f wff ch $.
	ebitr3i_0 $e |- ( ps <-> ph ) $.
	ebitr3i_1 $e |- ( ps <-> ch ) $.
	bitr3i $p |- ( ph <-> ch ) $= fbitr3i_0 fbitr3i_1 fbitr3i_2 fbitr3i_1 fbitr3i_0 ebitr3i_0 bicomi ebitr3i_1 bitri $.
$}
$( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
${
	fbitr4i_0 $f wff ph $.
	fbitr4i_1 $f wff ps $.
	fbitr4i_2 $f wff ch $.
	ebitr4i_0 $e |- ( ph <-> ps ) $.
	ebitr4i_1 $e |- ( ch <-> ps ) $.
	bitr4i $p |- ( ph <-> ch ) $= fbitr4i_0 fbitr4i_1 fbitr4i_2 ebitr4i_0 fbitr4i_2 fbitr4i_1 ebitr4i_1 bicomi bitri $.
$}
$( Register '<->' as an equality for its type (wff). $)
$( $j
    equality 'wb' from 'biid' 'bicomi' 'bitri';
    definition 'dfbi1' for 'wb';
  $)
$( Deduction form of ~ bitri .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 14-Apr-2013.) $)
${
	fbitrd_0 $f wff ph $.
	fbitrd_1 $f wff ps $.
	fbitrd_2 $f wff ch $.
	fbitrd_3 $f wff th $.
	ebitrd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ebitrd_1 $e |- ( ph -> ( ch <-> th ) ) $.
	bitrd $p |- ( ph -> ( ps <-> th ) ) $= fbitrd_0 fbitrd_1 fbitrd_3 fbitrd_0 fbitrd_1 wi fbitrd_0 fbitrd_2 wi fbitrd_0 fbitrd_3 wi fbitrd_0 fbitrd_1 fbitrd_2 ebitrd_0 pm5.74i fbitrd_0 fbitrd_2 fbitrd_3 ebitrd_1 pm5.74i bitri pm5.74ri $.
$}
$( Deduction form of ~ bitr2i .  (Contributed by NM, 9-Jun-2004.) $)
${
	fbitr2d_0 $f wff ph $.
	fbitr2d_1 $f wff ps $.
	fbitr2d_2 $f wff ch $.
	fbitr2d_3 $f wff th $.
	ebitr2d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ebitr2d_1 $e |- ( ph -> ( ch <-> th ) ) $.
	bitr2d $p |- ( ph -> ( th <-> ps ) ) $= fbitr2d_0 fbitr2d_1 fbitr2d_3 fbitr2d_0 fbitr2d_1 fbitr2d_2 fbitr2d_3 ebitr2d_0 ebitr2d_1 bitrd bicomd $.
$}
$( Deduction form of ~ bitr3i .  (Contributed by NM, 5-Aug-1993.) $)
${
	fbitr3d_0 $f wff ph $.
	fbitr3d_1 $f wff ps $.
	fbitr3d_2 $f wff ch $.
	fbitr3d_3 $f wff th $.
	ebitr3d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ebitr3d_1 $e |- ( ph -> ( ps <-> th ) ) $.
	bitr3d $p |- ( ph -> ( ch <-> th ) ) $= fbitr3d_0 fbitr3d_2 fbitr3d_1 fbitr3d_3 fbitr3d_0 fbitr3d_1 fbitr3d_2 ebitr3d_0 bicomd ebitr3d_1 bitrd $.
$}
$( Deduction form of ~ bitr4i .  (Contributed by NM, 5-Aug-1993.) $)
${
	fbitr4d_0 $f wff ph $.
	fbitr4d_1 $f wff ps $.
	fbitr4d_2 $f wff ch $.
	fbitr4d_3 $f wff th $.
	ebitr4d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ebitr4d_1 $e |- ( ph -> ( th <-> ch ) ) $.
	bitr4d $p |- ( ph -> ( ps <-> th ) ) $= fbitr4d_0 fbitr4d_1 fbitr4d_2 fbitr4d_3 ebitr4d_0 fbitr4d_0 fbitr4d_3 fbitr4d_2 ebitr4d_1 bicomd bitrd $.
$}
$( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fsyl5bb_0 $f wff ph $.
	fsyl5bb_1 $f wff ps $.
	fsyl5bb_2 $f wff ch $.
	fsyl5bb_3 $f wff th $.
	esyl5bb_0 $e |- ( ph <-> ps ) $.
	esyl5bb_1 $e |- ( ch -> ( ps <-> th ) ) $.
	syl5bb $p |- ( ch -> ( ph <-> th ) ) $= fsyl5bb_2 fsyl5bb_0 fsyl5bb_1 fsyl5bb_3 fsyl5bb_0 fsyl5bb_1 wb fsyl5bb_2 esyl5bb_0 a1i esyl5bb_1 bitrd $.
$}
$( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fsyl5rbb_0 $f wff ph $.
	fsyl5rbb_1 $f wff ps $.
	fsyl5rbb_2 $f wff ch $.
	fsyl5rbb_3 $f wff th $.
	esyl5rbb_0 $e |- ( ph <-> ps ) $.
	esyl5rbb_1 $e |- ( ch -> ( ps <-> th ) ) $.
	syl5rbb $p |- ( ch -> ( th <-> ph ) ) $= fsyl5rbb_2 fsyl5rbb_0 fsyl5rbb_3 fsyl5rbb_0 fsyl5rbb_1 fsyl5rbb_2 fsyl5rbb_3 esyl5rbb_0 esyl5rbb_1 syl5bb bicomd $.
$}
$( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fsyl5bbr_0 $f wff ph $.
	fsyl5bbr_1 $f wff ps $.
	fsyl5bbr_2 $f wff ch $.
	fsyl5bbr_3 $f wff th $.
	esyl5bbr_0 $e |- ( ps <-> ph ) $.
	esyl5bbr_1 $e |- ( ch -> ( ps <-> th ) ) $.
	syl5bbr $p |- ( ch -> ( ph <-> th ) ) $= fsyl5bbr_0 fsyl5bbr_1 fsyl5bbr_2 fsyl5bbr_3 fsyl5bbr_1 fsyl5bbr_0 esyl5bbr_0 bicomi esyl5bbr_1 syl5bb $.
$}
$( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
${
	fsyl5rbbr_0 $f wff ph $.
	fsyl5rbbr_1 $f wff ps $.
	fsyl5rbbr_2 $f wff ch $.
	fsyl5rbbr_3 $f wff th $.
	esyl5rbbr_0 $e |- ( ps <-> ph ) $.
	esyl5rbbr_1 $e |- ( ch -> ( ps <-> th ) ) $.
	syl5rbbr $p |- ( ch -> ( th <-> ph ) ) $= fsyl5rbbr_0 fsyl5rbbr_1 fsyl5rbbr_2 fsyl5rbbr_3 fsyl5rbbr_1 fsyl5rbbr_0 esyl5rbbr_0 bicomi esyl5rbbr_1 syl5rbb $.
$}
$( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fsyl6bb_0 $f wff ph $.
	fsyl6bb_1 $f wff ps $.
	fsyl6bb_2 $f wff ch $.
	fsyl6bb_3 $f wff th $.
	esyl6bb_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esyl6bb_1 $e |- ( ch <-> th ) $.
	syl6bb $p |- ( ph -> ( ps <-> th ) ) $= fsyl6bb_0 fsyl6bb_1 fsyl6bb_2 fsyl6bb_3 esyl6bb_0 fsyl6bb_2 fsyl6bb_3 wb fsyl6bb_0 esyl6bb_1 a1i bitrd $.
$}
$( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fsyl6rbb_0 $f wff ph $.
	fsyl6rbb_1 $f wff ps $.
	fsyl6rbb_2 $f wff ch $.
	fsyl6rbb_3 $f wff th $.
	esyl6rbb_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esyl6rbb_1 $e |- ( ch <-> th ) $.
	syl6rbb $p |- ( ph -> ( th <-> ps ) ) $= fsyl6rbb_0 fsyl6rbb_1 fsyl6rbb_3 fsyl6rbb_0 fsyl6rbb_1 fsyl6rbb_2 fsyl6rbb_3 esyl6rbb_0 esyl6rbb_1 syl6bb bicomd $.
$}
$( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fsyl6bbr_0 $f wff ph $.
	fsyl6bbr_1 $f wff ps $.
	fsyl6bbr_2 $f wff ch $.
	fsyl6bbr_3 $f wff th $.
	esyl6bbr_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esyl6bbr_1 $e |- ( th <-> ch ) $.
	syl6bbr $p |- ( ph -> ( ps <-> th ) ) $= fsyl6bbr_0 fsyl6bbr_1 fsyl6bbr_2 fsyl6bbr_3 esyl6bbr_0 fsyl6bbr_3 fsyl6bbr_2 esyl6bbr_1 bicomi syl6bb $.
$}
$( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
${
	fsyl6rbbr_0 $f wff ph $.
	fsyl6rbbr_1 $f wff ps $.
	fsyl6rbbr_2 $f wff ch $.
	fsyl6rbbr_3 $f wff th $.
	esyl6rbbr_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esyl6rbbr_1 $e |- ( th <-> ch ) $.
	syl6rbbr $p |- ( ph -> ( th <-> ps ) ) $= fsyl6rbbr_0 fsyl6rbbr_1 fsyl6rbbr_2 fsyl6rbbr_3 esyl6rbbr_0 fsyl6rbbr_3 fsyl6rbbr_2 esyl6rbbr_1 bicomi syl6rbb $.
$}
$( A mixed syllogism inference, useful for removing a definition from both
       sides of an implication.  (Contributed by NM, 10-Aug-1994.) $)
${
	f3imtr3i_0 $f wff ph $.
	f3imtr3i_1 $f wff ps $.
	f3imtr3i_2 $f wff ch $.
	f3imtr3i_3 $f wff th $.
	e3imtr3i_0 $e |- ( ph -> ps ) $.
	e3imtr3i_1 $e |- ( ph <-> ch ) $.
	e3imtr3i_2 $e |- ( ps <-> th ) $.
	3imtr3i $p |- ( ch -> th ) $= f3imtr3i_2 f3imtr3i_1 f3imtr3i_3 f3imtr3i_2 f3imtr3i_0 f3imtr3i_1 e3imtr3i_1 e3imtr3i_0 sylbir e3imtr3i_2 sylib $.
$}
$( A mixed syllogism inference, useful for applying a definition to both
       sides of an implication.  (Contributed by NM, 5-Aug-1993.) $)
${
	f3imtr4i_0 $f wff ph $.
	f3imtr4i_1 $f wff ps $.
	f3imtr4i_2 $f wff ch $.
	f3imtr4i_3 $f wff th $.
	e3imtr4i_0 $e |- ( ph -> ps ) $.
	e3imtr4i_1 $e |- ( ch <-> ph ) $.
	e3imtr4i_2 $e |- ( th <-> ps ) $.
	3imtr4i $p |- ( ch -> th ) $= f3imtr4i_2 f3imtr4i_1 f3imtr4i_3 f3imtr4i_2 f3imtr4i_0 f3imtr4i_1 e3imtr4i_1 e3imtr4i_0 sylbi e3imtr4i_2 sylibr $.
$}
$( More general version of ~ 3imtr3i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 8-Apr-1996.) $)
${
	f3imtr3d_0 $f wff ph $.
	f3imtr3d_1 $f wff ps $.
	f3imtr3d_2 $f wff ch $.
	f3imtr3d_3 $f wff th $.
	f3imtr3d_4 $f wff ta $.
	e3imtr3d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3imtr3d_1 $e |- ( ph -> ( ps <-> th ) ) $.
	e3imtr3d_2 $e |- ( ph -> ( ch <-> ta ) ) $.
	3imtr3d $p |- ( ph -> ( th -> ta ) ) $= f3imtr3d_0 f3imtr3d_3 f3imtr3d_1 f3imtr3d_4 e3imtr3d_1 f3imtr3d_0 f3imtr3d_1 f3imtr3d_2 f3imtr3d_4 e3imtr3d_0 e3imtr3d_2 sylibd sylbird $.
$}
$( More general version of ~ 3imtr4i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 26-Oct-1995.) $)
${
	f3imtr4d_0 $f wff ph $.
	f3imtr4d_1 $f wff ps $.
	f3imtr4d_2 $f wff ch $.
	f3imtr4d_3 $f wff th $.
	f3imtr4d_4 $f wff ta $.
	e3imtr4d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3imtr4d_1 $e |- ( ph -> ( th <-> ps ) ) $.
	e3imtr4d_2 $e |- ( ph -> ( ta <-> ch ) ) $.
	3imtr4d $p |- ( ph -> ( th -> ta ) ) $= f3imtr4d_0 f3imtr4d_3 f3imtr4d_1 f3imtr4d_4 e3imtr4d_1 f3imtr4d_0 f3imtr4d_1 f3imtr4d_2 f3imtr4d_4 e3imtr4d_0 e3imtr4d_2 sylibrd sylbid $.
$}
$( More general version of ~ 3imtr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
${
	f3imtr3g_0 $f wff ph $.
	f3imtr3g_1 $f wff ps $.
	f3imtr3g_2 $f wff ch $.
	f3imtr3g_3 $f wff th $.
	f3imtr3g_4 $f wff ta $.
	e3imtr3g_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3imtr3g_1 $e |- ( ps <-> th ) $.
	e3imtr3g_2 $e |- ( ch <-> ta ) $.
	3imtr3g $p |- ( ph -> ( th -> ta ) ) $= f3imtr3g_0 f3imtr3g_3 f3imtr3g_2 f3imtr3g_4 f3imtr3g_3 f3imtr3g_1 f3imtr3g_0 f3imtr3g_2 e3imtr3g_1 e3imtr3g_0 syl5bir e3imtr3g_2 syl6ib $.
$}
$( More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
${
	f3imtr4g_0 $f wff ph $.
	f3imtr4g_1 $f wff ps $.
	f3imtr4g_2 $f wff ch $.
	f3imtr4g_3 $f wff th $.
	f3imtr4g_4 $f wff ta $.
	e3imtr4g_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3imtr4g_1 $e |- ( th <-> ps ) $.
	e3imtr4g_2 $e |- ( ta <-> ch ) $.
	3imtr4g $p |- ( ph -> ( th -> ta ) ) $= f3imtr4g_0 f3imtr4g_3 f3imtr4g_2 f3imtr4g_4 f3imtr4g_3 f3imtr4g_1 f3imtr4g_0 f3imtr4g_2 e3imtr4g_1 e3imtr4g_0 syl5bi e3imtr4g_2 syl6ibr $.
$}
$( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
${
	f3bitri_0 $f wff ph $.
	f3bitri_1 $f wff ps $.
	f3bitri_2 $f wff ch $.
	f3bitri_3 $f wff th $.
	e3bitri_0 $e |- ( ph <-> ps ) $.
	e3bitri_1 $e |- ( ps <-> ch ) $.
	e3bitri_2 $e |- ( ch <-> th ) $.
	3bitri $p |- ( ph <-> th ) $= f3bitri_0 f3bitri_1 f3bitri_3 e3bitri_0 f3bitri_1 f3bitri_2 f3bitri_3 e3bitri_1 e3bitri_2 bitri bitri $.
$}
$( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
${
	f3bitrri_0 $f wff ph $.
	f3bitrri_1 $f wff ps $.
	f3bitrri_2 $f wff ch $.
	f3bitrri_3 $f wff th $.
	e3bitrri_0 $e |- ( ph <-> ps ) $.
	e3bitrri_1 $e |- ( ps <-> ch ) $.
	e3bitrri_2 $e |- ( ch <-> th ) $.
	3bitrri $p |- ( th <-> ph ) $= f3bitrri_3 f3bitrri_2 f3bitrri_0 e3bitrri_2 f3bitrri_0 f3bitrri_1 f3bitrri_2 e3bitrri_0 e3bitrri_1 bitr2i bitr3i $.
$}
$( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
${
	f3bitr2i_0 $f wff ph $.
	f3bitr2i_1 $f wff ps $.
	f3bitr2i_2 $f wff ch $.
	f3bitr2i_3 $f wff th $.
	e3bitr2i_0 $e |- ( ph <-> ps ) $.
	e3bitr2i_1 $e |- ( ch <-> ps ) $.
	e3bitr2i_2 $e |- ( ch <-> th ) $.
	3bitr2i $p |- ( ph <-> th ) $= f3bitr2i_0 f3bitr2i_2 f3bitr2i_3 f3bitr2i_0 f3bitr2i_1 f3bitr2i_2 e3bitr2i_0 e3bitr2i_1 bitr4i e3bitr2i_2 bitri $.
$}
$( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
${
	f3bitr2ri_0 $f wff ph $.
	f3bitr2ri_1 $f wff ps $.
	f3bitr2ri_2 $f wff ch $.
	f3bitr2ri_3 $f wff th $.
	e3bitr2ri_0 $e |- ( ph <-> ps ) $.
	e3bitr2ri_1 $e |- ( ch <-> ps ) $.
	e3bitr2ri_2 $e |- ( ch <-> th ) $.
	3bitr2ri $p |- ( th <-> ph ) $= f3bitr2ri_0 f3bitr2ri_2 f3bitr2ri_3 f3bitr2ri_0 f3bitr2ri_1 f3bitr2ri_2 e3bitr2ri_0 e3bitr2ri_1 bitr4i e3bitr2ri_2 bitr2i $.
$}
$( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 19-Aug-1993.) $)
${
	f3bitr3i_0 $f wff ph $.
	f3bitr3i_1 $f wff ps $.
	f3bitr3i_2 $f wff ch $.
	f3bitr3i_3 $f wff th $.
	e3bitr3i_0 $e |- ( ph <-> ps ) $.
	e3bitr3i_1 $e |- ( ph <-> ch ) $.
	e3bitr3i_2 $e |- ( ps <-> th ) $.
	3bitr3i $p |- ( ch <-> th ) $= f3bitr3i_2 f3bitr3i_1 f3bitr3i_3 f3bitr3i_2 f3bitr3i_0 f3bitr3i_1 e3bitr3i_1 e3bitr3i_0 bitr3i e3bitr3i_2 bitri $.
$}
$( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
${
	f3bitr3ri_0 $f wff ph $.
	f3bitr3ri_1 $f wff ps $.
	f3bitr3ri_2 $f wff ch $.
	f3bitr3ri_3 $f wff th $.
	e3bitr3ri_0 $e |- ( ph <-> ps ) $.
	e3bitr3ri_1 $e |- ( ph <-> ch ) $.
	e3bitr3ri_2 $e |- ( ps <-> th ) $.
	3bitr3ri $p |- ( th <-> ch ) $= f3bitr3ri_3 f3bitr3ri_1 f3bitr3ri_2 e3bitr3ri_2 f3bitr3ri_1 f3bitr3ri_0 f3bitr3ri_2 e3bitr3ri_0 e3bitr3ri_1 bitr3i bitr3i $.
$}
$( A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence.  (Contributed by NM, 5-Aug-1993.) $)
${
	f3bitr4i_0 $f wff ph $.
	f3bitr4i_1 $f wff ps $.
	f3bitr4i_2 $f wff ch $.
	f3bitr4i_3 $f wff th $.
	e3bitr4i_0 $e |- ( ph <-> ps ) $.
	e3bitr4i_1 $e |- ( ch <-> ph ) $.
	e3bitr4i_2 $e |- ( th <-> ps ) $.
	3bitr4i $p |- ( ch <-> th ) $= f3bitr4i_2 f3bitr4i_0 f3bitr4i_3 e3bitr4i_1 f3bitr4i_0 f3bitr4i_1 f3bitr4i_3 e3bitr4i_0 e3bitr4i_2 bitr4i bitri $.
$}
$( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 2-Sep-1995.) $)
${
	f3bitr4ri_0 $f wff ph $.
	f3bitr4ri_1 $f wff ps $.
	f3bitr4ri_2 $f wff ch $.
	f3bitr4ri_3 $f wff th $.
	e3bitr4ri_0 $e |- ( ph <-> ps ) $.
	e3bitr4ri_1 $e |- ( ch <-> ph ) $.
	e3bitr4ri_2 $e |- ( th <-> ps ) $.
	3bitr4ri $p |- ( th <-> ch ) $= f3bitr4ri_2 f3bitr4ri_0 f3bitr4ri_3 e3bitr4ri_1 f3bitr4ri_0 f3bitr4ri_1 f3bitr4ri_3 e3bitr4ri_0 e3bitr4ri_2 bitr4i bitr2i $.
$}
$( Deduction from transitivity of biconditional.  (Contributed by NM,
       13-Aug-1999.) $)
${
	f3bitrd_0 $f wff ph $.
	f3bitrd_1 $f wff ps $.
	f3bitrd_2 $f wff ch $.
	f3bitrd_3 $f wff th $.
	f3bitrd_4 $f wff ta $.
	e3bitrd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitrd_1 $e |- ( ph -> ( ch <-> th ) ) $.
	e3bitrd_2 $e |- ( ph -> ( th <-> ta ) ) $.
	3bitrd $p |- ( ph -> ( ps <-> ta ) ) $= f3bitrd_0 f3bitrd_1 f3bitrd_3 f3bitrd_4 f3bitrd_0 f3bitrd_1 f3bitrd_2 f3bitrd_3 e3bitrd_0 e3bitrd_1 bitrd e3bitrd_2 bitrd $.
$}
$( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
${
	f3bitrrd_0 $f wff ph $.
	f3bitrrd_1 $f wff ps $.
	f3bitrrd_2 $f wff ch $.
	f3bitrrd_3 $f wff th $.
	f3bitrrd_4 $f wff ta $.
	e3bitrrd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitrrd_1 $e |- ( ph -> ( ch <-> th ) ) $.
	e3bitrrd_2 $e |- ( ph -> ( th <-> ta ) ) $.
	3bitrrd $p |- ( ph -> ( ta <-> ps ) ) $= f3bitrrd_0 f3bitrrd_3 f3bitrrd_4 f3bitrrd_1 e3bitrrd_2 f3bitrrd_0 f3bitrrd_1 f3bitrrd_2 f3bitrrd_3 e3bitrrd_0 e3bitrrd_1 bitr2d bitr3d $.
$}
$( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
${
	f3bitr2d_0 $f wff ph $.
	f3bitr2d_1 $f wff ps $.
	f3bitr2d_2 $f wff ch $.
	f3bitr2d_3 $f wff th $.
	f3bitr2d_4 $f wff ta $.
	e3bitr2d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitr2d_1 $e |- ( ph -> ( th <-> ch ) ) $.
	e3bitr2d_2 $e |- ( ph -> ( th <-> ta ) ) $.
	3bitr2d $p |- ( ph -> ( ps <-> ta ) ) $= f3bitr2d_0 f3bitr2d_1 f3bitr2d_3 f3bitr2d_4 f3bitr2d_0 f3bitr2d_1 f3bitr2d_2 f3bitr2d_3 e3bitr2d_0 e3bitr2d_1 bitr4d e3bitr2d_2 bitrd $.
$}
$( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
${
	f3bitr2rd_0 $f wff ph $.
	f3bitr2rd_1 $f wff ps $.
	f3bitr2rd_2 $f wff ch $.
	f3bitr2rd_3 $f wff th $.
	f3bitr2rd_4 $f wff ta $.
	e3bitr2rd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitr2rd_1 $e |- ( ph -> ( th <-> ch ) ) $.
	e3bitr2rd_2 $e |- ( ph -> ( th <-> ta ) ) $.
	3bitr2rd $p |- ( ph -> ( ta <-> ps ) ) $= f3bitr2rd_0 f3bitr2rd_1 f3bitr2rd_3 f3bitr2rd_4 f3bitr2rd_0 f3bitr2rd_1 f3bitr2rd_2 f3bitr2rd_3 e3bitr2rd_0 e3bitr2rd_1 bitr4d e3bitr2rd_2 bitr2d $.
$}
$( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       24-Apr-1996.) $)
${
	f3bitr3d_0 $f wff ph $.
	f3bitr3d_1 $f wff ps $.
	f3bitr3d_2 $f wff ch $.
	f3bitr3d_3 $f wff th $.
	f3bitr3d_4 $f wff ta $.
	e3bitr3d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitr3d_1 $e |- ( ph -> ( ps <-> th ) ) $.
	e3bitr3d_2 $e |- ( ph -> ( ch <-> ta ) ) $.
	3bitr3d $p |- ( ph -> ( th <-> ta ) ) $= f3bitr3d_0 f3bitr3d_3 f3bitr3d_2 f3bitr3d_4 f3bitr3d_0 f3bitr3d_1 f3bitr3d_3 f3bitr3d_2 e3bitr3d_1 e3bitr3d_0 bitr3d e3bitr3d_2 bitrd $.
$}
$( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
${
	f3bitr3rd_0 $f wff ph $.
	f3bitr3rd_1 $f wff ps $.
	f3bitr3rd_2 $f wff ch $.
	f3bitr3rd_3 $f wff th $.
	f3bitr3rd_4 $f wff ta $.
	e3bitr3rd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitr3rd_1 $e |- ( ph -> ( ps <-> th ) ) $.
	e3bitr3rd_2 $e |- ( ph -> ( ch <-> ta ) ) $.
	3bitr3rd $p |- ( ph -> ( ta <-> th ) ) $= f3bitr3rd_0 f3bitr3rd_2 f3bitr3rd_4 f3bitr3rd_3 e3bitr3rd_2 f3bitr3rd_0 f3bitr3rd_1 f3bitr3rd_2 f3bitr3rd_3 e3bitr3rd_0 e3bitr3rd_1 bitr3d bitr3d $.
$}
$( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       18-Oct-1995.) $)
${
	f3bitr4d_0 $f wff ph $.
	f3bitr4d_1 $f wff ps $.
	f3bitr4d_2 $f wff ch $.
	f3bitr4d_3 $f wff th $.
	f3bitr4d_4 $f wff ta $.
	e3bitr4d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitr4d_1 $e |- ( ph -> ( th <-> ps ) ) $.
	e3bitr4d_2 $e |- ( ph -> ( ta <-> ch ) ) $.
	3bitr4d $p |- ( ph -> ( th <-> ta ) ) $= f3bitr4d_0 f3bitr4d_3 f3bitr4d_1 f3bitr4d_4 e3bitr4d_1 f3bitr4d_0 f3bitr4d_1 f3bitr4d_2 f3bitr4d_4 e3bitr4d_0 e3bitr4d_2 bitr4d bitrd $.
$}
$( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
${
	f3bitr4rd_0 $f wff ph $.
	f3bitr4rd_1 $f wff ps $.
	f3bitr4rd_2 $f wff ch $.
	f3bitr4rd_3 $f wff th $.
	f3bitr4rd_4 $f wff ta $.
	e3bitr4rd_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitr4rd_1 $e |- ( ph -> ( th <-> ps ) ) $.
	e3bitr4rd_2 $e |- ( ph -> ( ta <-> ch ) ) $.
	3bitr4rd $p |- ( ph -> ( ta <-> th ) ) $= f3bitr4rd_0 f3bitr4rd_4 f3bitr4rd_1 f3bitr4rd_3 f3bitr4rd_0 f3bitr4rd_4 f3bitr4rd_2 f3bitr4rd_1 e3bitr4rd_2 e3bitr4rd_0 bitr4d e3bitr4rd_1 bitr4d $.
$}
$( More general version of ~ 3bitr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 4-Jun-1995.) $)
${
	f3bitr3g_0 $f wff ph $.
	f3bitr3g_1 $f wff ps $.
	f3bitr3g_2 $f wff ch $.
	f3bitr3g_3 $f wff th $.
	f3bitr3g_4 $f wff ta $.
	e3bitr3g_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitr3g_1 $e |- ( ps <-> th ) $.
	e3bitr3g_2 $e |- ( ch <-> ta ) $.
	3bitr3g $p |- ( ph -> ( th <-> ta ) ) $= f3bitr3g_0 f3bitr3g_3 f3bitr3g_2 f3bitr3g_4 f3bitr3g_3 f3bitr3g_1 f3bitr3g_0 f3bitr3g_2 e3bitr3g_1 e3bitr3g_0 syl5bbr e3bitr3g_2 syl6bb $.
$}
$( More general version of ~ 3bitr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 5-Aug-1993.) $)
${
	f3bitr4g_0 $f wff ph $.
	f3bitr4g_1 $f wff ps $.
	f3bitr4g_2 $f wff ch $.
	f3bitr4g_3 $f wff th $.
	f3bitr4g_4 $f wff ta $.
	e3bitr4g_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3bitr4g_1 $e |- ( th <-> ps ) $.
	e3bitr4g_2 $e |- ( ta <-> ch ) $.
	3bitr4g $p |- ( ph -> ( th <-> ta ) ) $= f3bitr4g_0 f3bitr4g_3 f3bitr4g_2 f3bitr4g_4 f3bitr4g_3 f3bitr4g_1 f3bitr4g_0 f3bitr4g_2 e3bitr4g_1 e3bitr4g_0 syl5bb e3bitr4g_2 syl6bbr $.
$}
$( Construct a bi-conditional in antecedent position.  (Contributed by Wolf
       Lammen, 14-May-2013.) $)
${
	fbi3ant_0 $f wff ph $.
	fbi3ant_1 $f wff ps $.
	fbi3ant_2 $f wff ch $.
	fbi3ant_3 $f wff th $.
	fbi3ant_4 $f wff ta $.
	ebi3ant_0 $e |- ( ph -> ( ps -> ch ) ) $.
	bi3ant $p |- ( ( ( th -> ta ) -> ph ) -> ( ( ( ta -> th ) -> ps ) -> ( ( th <-> ta ) -> ch ) ) ) $= fbi3ant_3 fbi3ant_4 wi fbi3ant_0 wi fbi3ant_3 fbi3ant_4 wb fbi3ant_0 wi fbi3ant_4 fbi3ant_3 wi fbi3ant_1 wi fbi3ant_3 fbi3ant_4 wb fbi3ant_1 wi fbi3ant_3 fbi3ant_4 wb fbi3ant_2 wi fbi3ant_3 fbi3ant_4 wb fbi3ant_3 fbi3ant_4 wi fbi3ant_0 fbi3ant_3 fbi3ant_4 bi1 imim1i fbi3ant_3 fbi3ant_4 wb fbi3ant_4 fbi3ant_3 wi fbi3ant_1 fbi3ant_3 fbi3ant_4 bi2 imim1i fbi3ant_0 fbi3ant_1 fbi3ant_2 fbi3ant_3 fbi3ant_4 wb ebi3ant_0 imim3i syl2im $.
$}
$( Express symmetries of theorems in terms of biconditionals.  (Contributed
     by Wolf Lammen, 14-May-2013.) $)
${
	fbisym_0 $f wff ph $.
	fbisym_1 $f wff ps $.
	fbisym_2 $f wff ch $.
	fbisym_3 $f wff th $.
	bisym $p |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph ) -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) ) $= fbisym_2 fbisym_3 wi fbisym_3 fbisym_2 wi fbisym_2 fbisym_3 wb fbisym_0 fbisym_1 fbisym_2 fbisym_3 bi3 bi3ant $.
$}
$( Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117.
     (Contributed by NM, 5-Aug-1993.) $)
${
	fnotnot_0 $f wff ph $.
	notnot $p |- ( ph <-> -. -. ph ) $= fnotnot_0 fnotnot_0 wn wn fnotnot_0 notnot1 fnotnot_0 notnot2 impbii $.
$}
$( Contraposition.  Theorem *4.1 of [WhiteheadRussell] p. 116.  (Contributed
     by NM, 5-Aug-1993.) $)
${
	fcon34b_0 $f wff ph $.
	fcon34b_1 $f wff ps $.
	con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $= fcon34b_0 fcon34b_1 wi fcon34b_1 wn fcon34b_0 wn wi fcon34b_0 fcon34b_1 con3 fcon34b_1 fcon34b_0 ax-3 impbii $.
$}
$( A contraposition deduction.  (Contributed by NM, 21-May-1994.) $)
${
	fcon4bid_0 $f wff ph $.
	fcon4bid_1 $f wff ps $.
	fcon4bid_2 $f wff ch $.
	econ4bid_0 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
	con4bid $p |- ( ph -> ( ps <-> ch ) ) $= fcon4bid_0 fcon4bid_1 fcon4bid_2 fcon4bid_0 fcon4bid_2 fcon4bid_1 fcon4bid_0 fcon4bid_1 wn fcon4bid_2 wn econ4bid_0 biimprd con4d fcon4bid_0 fcon4bid_1 wn fcon4bid_2 wn econ4bid_0 biimpd impcon4bid $.
$}
$( Deduction negating both sides of a logical equivalence.  (Contributed by
       NM, 21-May-1994.) $)
${
	fnotbid_0 $f wff ph $.
	fnotbid_1 $f wff ps $.
	fnotbid_2 $f wff ch $.
	enotbid_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $= fnotbid_0 fnotbid_1 wn fnotbid_2 wn fnotbid_0 fnotbid_1 fnotbid_2 fnotbid_1 wn wn fnotbid_2 wn wn enotbid_0 fnotbid_1 notnot fnotbid_2 notnot 3bitr3g con4bid $.
$}
$( Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 21-May-1994.)  (Proof shortened by Wolf Lammen, 12-Jun-2013.) $)
${
	fnotbi_0 $f wff ph $.
	fnotbi_1 $f wff ps $.
	notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $= fnotbi_0 fnotbi_1 wb fnotbi_0 wn fnotbi_1 wn wb fnotbi_0 fnotbi_1 wb fnotbi_0 fnotbi_1 fnotbi_0 fnotbi_1 wb id notbid fnotbi_0 wn fnotbi_1 wn wb fnotbi_0 fnotbi_1 fnotbi_0 wn fnotbi_1 wn wb id con4bid impbii $.
$}
$( Negate both sides of a logical equivalence.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
${
	fnotbii_0 $f wff ph $.
	fnotbii_1 $f wff ps $.
	enotbii_0 $e |- ( ph <-> ps ) $.
	notbii $p |- ( -. ph <-> -. ps ) $= fnotbii_0 fnotbii_1 wb fnotbii_0 wn fnotbii_1 wn wb enotbii_0 fnotbii_0 fnotbii_1 notbi mpbi $.
$}
$( Theorem notbii is the congruence law for negation. $)
$( $j congruence 'notbii'; $)
$( A contraposition inference.  (Contributed by NM, 21-May-1994.) $)
${
	fcon4bii_0 $f wff ph $.
	fcon4bii_1 $f wff ps $.
	econ4bii_0 $e |- ( -. ph <-> -. ps ) $.
	con4bii $p |- ( ph <-> ps ) $= fcon4bii_0 fcon4bii_1 wb fcon4bii_0 wn fcon4bii_1 wn wb econ4bii_0 fcon4bii_0 fcon4bii_1 notbi mpbir $.
$}
$( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
${
	fmtbi_0 $f wff ph $.
	fmtbi_1 $f wff ps $.
	emtbi_0 $e |- -. ph $.
	emtbi_1 $e |- ( ph <-> ps ) $.
	mtbi $p |- -. ps $= fmtbi_1 fmtbi_0 emtbi_0 fmtbi_0 fmtbi_1 emtbi_1 biimpri mto $.
$}
$( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       14-Oct-2012.) $)
${
	fmtbir_0 $f wff ph $.
	fmtbir_1 $f wff ps $.
	emtbir_0 $e |- -. ps $.
	emtbir_1 $e |- ( ph <-> ps ) $.
	mtbir $p |- -. ph $= fmtbir_1 fmtbir_0 emtbir_0 fmtbir_0 fmtbir_1 emtbir_1 bicomi mtbi $.
$}
$( A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 26-Nov-1995.) $)
${
	fmtbid_0 $f wff ph $.
	fmtbid_1 $f wff ps $.
	fmtbid_2 $f wff ch $.
	emtbid_0 $e |- ( ph -> -. ps ) $.
	emtbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mtbid $p |- ( ph -> -. ch ) $= fmtbid_0 fmtbid_2 fmtbid_1 emtbid_0 fmtbid_0 fmtbid_1 fmtbid_2 emtbid_1 biimprd mtod $.
$}
$( A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 10-May-1994.) $)
${
	fmtbird_0 $f wff ph $.
	fmtbird_1 $f wff ps $.
	fmtbird_2 $f wff ch $.
	emtbird_0 $e |- ( ph -> -. ch ) $.
	emtbird_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mtbird $p |- ( ph -> -. ps ) $= fmtbird_0 fmtbird_1 fmtbird_2 emtbird_0 fmtbird_0 fmtbird_1 fmtbird_2 emtbird_1 biimpd mtod $.
$}
$( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 27-Nov-1995.) $)
${
	fmtbii_0 $f wff ph $.
	fmtbii_1 $f wff ps $.
	fmtbii_2 $f wff ch $.
	emtbii_0 $e |- -. ps $.
	emtbii_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mtbii $p |- ( ph -> -. ch ) $= fmtbii_0 fmtbii_2 fmtbii_1 emtbii_0 fmtbii_0 fmtbii_1 fmtbii_2 emtbii_1 biimprd mtoi $.
$}
$( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 24-Aug-1995.) $)
${
	fmtbiri_0 $f wff ph $.
	fmtbiri_1 $f wff ps $.
	fmtbiri_2 $f wff ch $.
	emtbiri_0 $e |- -. ch $.
	emtbiri_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mtbiri $p |- ( ph -> -. ps ) $= fmtbiri_0 fmtbiri_1 fmtbiri_2 emtbiri_0 fmtbiri_0 fmtbiri_1 fmtbiri_2 emtbiri_1 biimpd mtoi $.
$}
$( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
${
	fsylnib_0 $f wff ph $.
	fsylnib_1 $f wff ps $.
	fsylnib_2 $f wff ch $.
	esylnib_0 $e |- ( ph -> -. ps ) $.
	esylnib_1 $e |- ( ps <-> ch ) $.
	sylnib $p |- ( ph -> -. ch ) $= fsylnib_0 fsylnib_1 fsylnib_2 esylnib_0 fsylnib_1 fsylnib_2 wb fsylnib_0 esylnib_1 a1i mtbid $.
$}
$( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       Wolf Lammen, 16-Dec-2013.) $)
${
	fsylnibr_0 $f wff ph $.
	fsylnibr_1 $f wff ps $.
	fsylnibr_2 $f wff ch $.
	esylnibr_0 $e |- ( ph -> -. ps ) $.
	esylnibr_1 $e |- ( ch <-> ps ) $.
	sylnibr $p |- ( ph -> -. ch ) $= fsylnibr_0 fsylnibr_1 fsylnibr_2 esylnibr_0 fsylnibr_2 fsylnibr_1 esylnibr_1 bicomi sylnib $.
$}
$( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
${
	fsylnbi_0 $f wff ph $.
	fsylnbi_1 $f wff ps $.
	fsylnbi_2 $f wff ch $.
	esylnbi_0 $e |- ( ph <-> ps ) $.
	esylnbi_1 $e |- ( -. ps -> ch ) $.
	sylnbi $p |- ( -. ph -> ch ) $= fsylnbi_0 wn fsylnbi_1 wn fsylnbi_2 fsylnbi_0 fsylnbi_1 esylnbi_0 notbii esylnbi_1 sylbi $.
$}
$( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
${
	fsylnbir_0 $f wff ph $.
	fsylnbir_1 $f wff ps $.
	fsylnbir_2 $f wff ch $.
	esylnbir_0 $e |- ( ps <-> ph ) $.
	esylnbir_1 $e |- ( -. ps -> ch ) $.
	sylnbir $p |- ( -. ph -> ch ) $= fsylnbir_0 fsylnbir_1 fsylnbir_2 fsylnbir_1 fsylnbir_0 esylnbir_0 bicomi esylnbir_1 sylnbi $.
$}
$( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
${
	fxchnxbi_0 $f wff ph $.
	fxchnxbi_1 $f wff ps $.
	fxchnxbi_2 $f wff ch $.
	exchnxbi_0 $e |- ( -. ph <-> ps ) $.
	exchnxbi_1 $e |- ( ph <-> ch ) $.
	xchnxbi $p |- ( -. ch <-> ps ) $= fxchnxbi_2 wn fxchnxbi_0 wn fxchnxbi_1 fxchnxbi_0 fxchnxbi_2 exchnxbi_1 notbii exchnxbi_0 bitr3i $.
$}
$( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
${
	fxchnxbir_0 $f wff ph $.
	fxchnxbir_1 $f wff ps $.
	fxchnxbir_2 $f wff ch $.
	exchnxbir_0 $e |- ( -. ph <-> ps ) $.
	exchnxbir_1 $e |- ( ch <-> ph ) $.
	xchnxbir $p |- ( -. ch <-> ps ) $= fxchnxbir_0 fxchnxbir_1 fxchnxbir_2 exchnxbir_0 fxchnxbir_2 fxchnxbir_0 exchnxbir_1 bicomi xchnxbi $.
$}
$( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
${
	fxchbinx_0 $f wff ph $.
	fxchbinx_1 $f wff ps $.
	fxchbinx_2 $f wff ch $.
	exchbinx_0 $e |- ( ph <-> -. ps ) $.
	exchbinx_1 $e |- ( ps <-> ch ) $.
	xchbinx $p |- ( ph <-> -. ch ) $= fxchbinx_0 fxchbinx_1 wn fxchbinx_2 wn exchbinx_0 fxchbinx_1 fxchbinx_2 exchbinx_1 notbii bitri $.
$}
$( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
${
	fxchbinxr_0 $f wff ph $.
	fxchbinxr_1 $f wff ps $.
	fxchbinxr_2 $f wff ch $.
	exchbinxr_0 $e |- ( ph <-> -. ps ) $.
	exchbinxr_1 $e |- ( ch <-> ps ) $.
	xchbinxr $p |- ( ph <-> -. ch ) $= fxchbinxr_0 fxchbinxr_1 fxchbinxr_2 exchbinxr_0 fxchbinxr_2 fxchbinxr_1 exchbinxr_1 bicomi xchbinx $.
$}
$( The next three rules are useful for building up wff's around a
     definition, in order to make use of the definition. $)
$( Introduce an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       6-Feb-2013.) $)
${
	fimbi2i_0 $f wff ph $.
	fimbi2i_1 $f wff ps $.
	fimbi2i_2 $f wff ch $.
	eimbi2i_0 $e |- ( ph <-> ps ) $.
	imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $= fimbi2i_2 fimbi2i_0 fimbi2i_1 fimbi2i_0 fimbi2i_1 wb fimbi2i_2 eimbi2i_0 a1i pm5.74i $.
$}
$( Inference adding a biconditional to the left in an equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.)  (Proof shortened by Wolf Lammen, 16-May-2013.) $)
${
	fbibi2i_0 $f wff ph $.
	fbibi2i_1 $f wff ps $.
	fbibi2i_2 $f wff ch $.
	ebibi2i_0 $e |- ( ph <-> ps ) $.
	bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $= fbibi2i_2 fbibi2i_0 wb fbibi2i_2 fbibi2i_1 wb fbibi2i_2 fbibi2i_0 wb fbibi2i_2 fbibi2i_0 fbibi2i_1 fbibi2i_2 fbibi2i_0 wb id ebibi2i_0 syl6bb fbibi2i_2 fbibi2i_1 wb fbibi2i_2 fbibi2i_1 fbibi2i_0 fbibi2i_2 fbibi2i_1 wb id ebibi2i_0 syl6bbr impbii $.
$}
$( Inference adding a biconditional to the right in an equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fbibi1i_0 $f wff ph $.
	fbibi1i_1 $f wff ps $.
	fbibi1i_2 $f wff ch $.
	ebibi1i_0 $e |- ( ph <-> ps ) $.
	bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $= fbibi1i_0 fbibi1i_2 wb fbibi1i_2 fbibi1i_0 wb fbibi1i_2 fbibi1i_1 wb fbibi1i_1 fbibi1i_2 wb fbibi1i_0 fbibi1i_2 bicom fbibi1i_0 fbibi1i_1 fbibi1i_2 ebibi1i_0 bibi2i fbibi1i_2 fbibi1i_1 bicom 3bitri $.
$}
$( The equivalence of two equivalences.  (Contributed by NM,
         5-Aug-1993.) $)
${
	fbibi12i_0 $f wff ph $.
	fbibi12i_1 $f wff ps $.
	fbibi12i_2 $f wff ch $.
	fbibi12i_3 $f wff th $.
	ebibi12i_0 $e |- ( ph <-> ps ) $.
	ebibi12i_1 $e |- ( ch <-> th ) $.
	bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $= fbibi12i_0 fbibi12i_2 wb fbibi12i_0 fbibi12i_3 wb fbibi12i_1 fbibi12i_3 wb fbibi12i_2 fbibi12i_3 fbibi12i_0 ebibi12i_1 bibi2i fbibi12i_0 fbibi12i_1 fbibi12i_3 ebibi12i_0 bibi1i bitri $.
$}
$( Deduction adding an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fimbi2d_0 $f wff ph $.
	fimbi2d_1 $f wff ps $.
	fimbi2d_2 $f wff ch $.
	fimbi2d_3 $f wff th $.
	eimbi2d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	imbi2d $p |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ) $= fimbi2d_0 fimbi2d_3 fimbi2d_1 fimbi2d_2 fimbi2d_0 fimbi2d_1 fimbi2d_2 wb fimbi2d_3 eimbi2d_0 a1d pm5.74d $.
$}
$( Deduction adding a consequent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
${
	fimbi1d_0 $f wff ph $.
	fimbi1d_1 $f wff ps $.
	fimbi1d_2 $f wff ch $.
	fimbi1d_3 $f wff th $.
	eimbi1d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $= fimbi1d_0 fimbi1d_1 fimbi1d_3 wi fimbi1d_2 fimbi1d_3 wi fimbi1d_0 fimbi1d_2 fimbi1d_1 fimbi1d_3 fimbi1d_0 fimbi1d_1 fimbi1d_2 eimbi1d_0 biimprd imim1d fimbi1d_0 fimbi1d_1 fimbi1d_2 fimbi1d_3 fimbi1d_0 fimbi1d_1 fimbi1d_2 eimbi1d_0 biimpd imim1d impbid $.
$}
$( Deduction adding a biconditional to the left in an equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       19-May-2013.) $)
${
	fbibi2d_0 $f wff ph $.
	fbibi2d_1 $f wff ps $.
	fbibi2d_2 $f wff ch $.
	fbibi2d_3 $f wff th $.
	ebibi2d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	bibi2d $p |- ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ) $= fbibi2d_0 fbibi2d_3 fbibi2d_1 wb fbibi2d_3 fbibi2d_2 wb fbibi2d_0 fbibi2d_3 wi fbibi2d_0 fbibi2d_1 wi wb fbibi2d_0 fbibi2d_3 wi fbibi2d_0 fbibi2d_2 wi wb fbibi2d_0 fbibi2d_3 fbibi2d_1 wb wi fbibi2d_0 fbibi2d_3 fbibi2d_2 wb wi fbibi2d_0 fbibi2d_1 wi fbibi2d_0 fbibi2d_2 wi fbibi2d_0 fbibi2d_3 wi fbibi2d_0 fbibi2d_1 fbibi2d_2 ebibi2d_0 pm5.74i bibi2i fbibi2d_0 fbibi2d_3 fbibi2d_1 pm5.74 fbibi2d_0 fbibi2d_3 fbibi2d_2 pm5.74 3bitr4i pm5.74ri $.
$}
$( Deduction adding a biconditional to the right in an equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fbibi1d_0 $f wff ph $.
	fbibi1d_1 $f wff ps $.
	fbibi1d_2 $f wff ch $.
	fbibi1d_3 $f wff th $.
	ebibi1d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	bibi1d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) ) $= fbibi1d_0 fbibi1d_3 fbibi1d_1 wb fbibi1d_3 fbibi1d_2 wb fbibi1d_1 fbibi1d_3 wb fbibi1d_2 fbibi1d_3 wb fbibi1d_0 fbibi1d_1 fbibi1d_2 fbibi1d_3 ebibi1d_0 bibi2d fbibi1d_1 fbibi1d_3 bicom fbibi1d_2 fbibi1d_3 bicom 3bitr4g $.
$}
$( Deduction joining two equivalences to form equivalence of implications.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fimbi12d_0 $f wff ph $.
	fimbi12d_1 $f wff ps $.
	fimbi12d_2 $f wff ch $.
	fimbi12d_3 $f wff th $.
	fimbi12d_4 $f wff ta $.
	eimbi12d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	eimbi12d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	imbi12d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $= fimbi12d_0 fimbi12d_1 fimbi12d_3 wi fimbi12d_2 fimbi12d_3 wi fimbi12d_2 fimbi12d_4 wi fimbi12d_0 fimbi12d_1 fimbi12d_2 fimbi12d_3 eimbi12d_0 imbi1d fimbi12d_0 fimbi12d_3 fimbi12d_4 fimbi12d_2 eimbi12d_1 imbi2d bitrd $.
$}
$( Deduction joining two equivalences to form equivalence of
       biconditionals.  (Contributed by NM, 5-Aug-1993.) $)
${
	fbibi12d_0 $f wff ph $.
	fbibi12d_1 $f wff ps $.
	fbibi12d_2 $f wff ch $.
	fbibi12d_3 $f wff th $.
	fbibi12d_4 $f wff ta $.
	ebibi12d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ebibi12d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	bibi12d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) ) $= fbibi12d_0 fbibi12d_1 fbibi12d_3 wb fbibi12d_2 fbibi12d_3 wb fbibi12d_2 fbibi12d_4 wb fbibi12d_0 fbibi12d_1 fbibi12d_2 fbibi12d_3 ebibi12d_0 bibi1d fbibi12d_0 fbibi12d_3 fbibi12d_4 fbibi12d_2 ebibi12d_1 bibi2d bitrd $.
$}
$( Theorem *4.84 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
${
	fimbi1_0 $f wff ph $.
	fimbi1_1 $f wff ps $.
	fimbi1_2 $f wff ch $.
	imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $= fimbi1_0 fimbi1_1 wb fimbi1_0 fimbi1_1 fimbi1_2 fimbi1_0 fimbi1_1 wb id imbi1d $.
$}
$( Theorem *4.85 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
${
	fimbi2_0 $f wff ph $.
	fimbi2_1 $f wff ps $.
	fimbi2_2 $f wff ch $.
	imbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $= fimbi2_0 fimbi2_1 wb fimbi2_0 fimbi2_1 fimbi2_2 fimbi2_0 fimbi2_1 wb id imbi2d $.
$}
$( Introduce a consequent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
${
	fimbi1i_0 $f wff ph $.
	fimbi1i_1 $f wff ps $.
	fimbi1i_2 $f wff ch $.
	eimbi1i_0 $e |- ( ph <-> ps ) $.
	imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $= fimbi1i_0 fimbi1i_1 wb fimbi1i_0 fimbi1i_2 wi fimbi1i_1 fimbi1i_2 wi wb eimbi1i_0 fimbi1i_0 fimbi1i_1 fimbi1i_2 imbi1 ax-mp $.
$}
$( Join two logical equivalences to form equivalence of implications.
       (Contributed by NM, 5-Aug-1993.) $)
${
	fimbi12i_0 $f wff ph $.
	fimbi12i_1 $f wff ps $.
	fimbi12i_2 $f wff ch $.
	fimbi12i_3 $f wff th $.
	eimbi12i_0 $e |- ( ph <-> ps ) $.
	eimbi12i_1 $e |- ( ch <-> th ) $.
	imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $= fimbi12i_0 fimbi12i_2 wi fimbi12i_0 fimbi12i_3 wi fimbi12i_1 fimbi12i_3 wi fimbi12i_2 fimbi12i_3 fimbi12i_0 eimbi12i_1 imbi2i fimbi12i_0 fimbi12i_1 fimbi12i_3 eimbi12i_0 imbi1i bitri $.
$}
$( Theorem imbi12i is the congruence law for implication. $)
$( $j congruence 'imbi12i'; $)
$( Theorem *4.86 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
${
	fbibi1_0 $f wff ph $.
	fbibi1_1 $f wff ps $.
	fbibi1_2 $f wff ch $.
	bibi1 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $= fbibi1_0 fbibi1_1 wb fbibi1_0 fbibi1_1 fbibi1_2 fbibi1_0 fbibi1_1 wb id bibi1d $.
$}
$( Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 15-Apr-1995.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)
${
	fcon2bi_0 $f wff ph $.
	fcon2bi_1 $f wff ps $.
	con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $= fcon2bi_0 fcon2bi_1 wn wb fcon2bi_0 wn fcon2bi_1 wn wn wb fcon2bi_0 wn fcon2bi_1 wb fcon2bi_1 fcon2bi_0 wn wb fcon2bi_0 fcon2bi_1 wn notbi fcon2bi_1 fcon2bi_1 wn wn fcon2bi_0 wn fcon2bi_1 notnot bibi2i fcon2bi_0 wn fcon2bi_1 bicom 3bitr2i $.
$}
$( A contraposition deduction.  (Contributed by NM, 15-Apr-1995.) $)
${
	fcon2bid_0 $f wff ph $.
	fcon2bid_1 $f wff ps $.
	fcon2bid_2 $f wff ch $.
	econ2bid_0 $e |- ( ph -> ( ps <-> -. ch ) ) $.
	con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $= fcon2bid_0 fcon2bid_1 fcon2bid_2 wn wb fcon2bid_2 fcon2bid_1 wn wb econ2bid_0 fcon2bid_2 fcon2bid_1 con2bi sylibr $.
$}
$( A contraposition deduction.  (Contributed by NM, 9-Oct-1999.) $)
${
	fcon1bid_0 $f wff ph $.
	fcon1bid_1 $f wff ps $.
	fcon1bid_2 $f wff ch $.
	econ1bid_0 $e |- ( ph -> ( -. ps <-> ch ) ) $.
	con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $= fcon1bid_0 fcon1bid_1 fcon1bid_2 wn fcon1bid_0 fcon1bid_2 fcon1bid_1 fcon1bid_0 fcon1bid_1 wn fcon1bid_2 econ1bid_0 bicomd con2bid bicomd $.
$}
$( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 13-Oct-2012.) $)
${
	fcon1bii_0 $f wff ph $.
	fcon1bii_1 $f wff ps $.
	econ1bii_0 $e |- ( -. ph <-> ps ) $.
	con1bii $p |- ( -. ps <-> ph ) $= fcon1bii_0 fcon1bii_1 wn fcon1bii_0 fcon1bii_0 wn fcon1bii_1 fcon1bii_0 notnot econ1bii_0 xchbinx bicomi $.
$}
$( A contraposition inference.  (Contributed by NM, 5-Aug-1993.) $)
${
	fcon2bii_0 $f wff ph $.
	fcon2bii_1 $f wff ps $.
	econ2bii_0 $e |- ( ph <-> -. ps ) $.
	con2bii $p |- ( ps <-> -. ph ) $= fcon2bii_0 wn fcon2bii_1 fcon2bii_1 fcon2bii_0 fcon2bii_0 fcon2bii_1 wn econ2bii_0 bicomi con1bii bicomi $.
$}
$( Contraposition.  Bidirectional version of ~ con1 .  (Contributed by NM,
     5-Aug-1993.) $)
${
	fcon1b_0 $f wff ph $.
	fcon1b_1 $f wff ps $.
	con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $= fcon1b_0 wn fcon1b_1 wi fcon1b_1 wn fcon1b_0 wi fcon1b_0 fcon1b_1 con1 fcon1b_1 fcon1b_0 con1 impbii $.
$}
$( Contraposition.  Bidirectional version of ~ con2 .  (Contributed by NM,
     5-Aug-1993.) $)
${
	fcon2b_0 $f wff ph $.
	fcon2b_1 $f wff ps $.
	con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $= fcon2b_0 fcon2b_1 wn wi fcon2b_1 fcon2b_0 wn wi fcon2b_0 fcon2b_1 con2 fcon2b_1 fcon2b_0 con2 impbii $.
$}
$( A wff is equivalent to itself with true antecedent.  (Contributed by NM,
     28-Jan-1996.) $)
${
	fbiimt_0 $f wff ph $.
	fbiimt_1 $f wff ps $.
	biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $= fbiimt_0 fbiimt_1 fbiimt_0 fbiimt_1 wi fbiimt_1 fbiimt_0 ax-1 fbiimt_0 fbiimt_1 pm2.27 impbid2 $.
$}
$( Theorem *5.5 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
${
	fpm5.5_0 $f wff ph $.
	fpm5.5_1 $f wff ps $.
	pm5.5 $p |- ( ph -> ( ( ph -> ps ) <-> ps ) ) $= fpm5.5_0 fpm5.5_1 fpm5.5_0 fpm5.5_1 wi fpm5.5_0 fpm5.5_1 biimt bicomd $.
$}
$( Inference rule introducing a theorem as an antecedent.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
${
	fa1bi_0 $f wff ph $.
	fa1bi_1 $f wff ps $.
	ea1bi_0 $e |- ph $.
	a1bi $p |- ( ps <-> ( ph -> ps ) ) $= fa1bi_0 fa1bi_1 fa1bi_0 fa1bi_1 wi wb ea1bi_0 fa1bi_0 fa1bi_1 biimt ax-mp $.
$}
$( A false consequent falsifies an antecedent.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Nov-2012.) $)
${
	fmt2bi_0 $f wff ph $.
	fmt2bi_1 $f wff ps $.
	emt2bi_0 $e |- ph $.
	mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $= fmt2bi_1 wn fmt2bi_0 fmt2bi_1 wn wi fmt2bi_1 fmt2bi_0 wn wi fmt2bi_0 fmt2bi_1 wn emt2bi_0 a1bi fmt2bi_0 fmt2bi_1 con2b bitri $.
$}
$( Modus-tollens-like theorem.  (Contributed by NM, 7-Apr-2001.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2012.) $)
${
	fmtt_0 $f wff ph $.
	fmtt_1 $f wff ps $.
	mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $= fmtt_0 wn fmtt_1 wn fmtt_0 wn fmtt_1 wn wi fmtt_1 fmtt_0 wi fmtt_0 wn fmtt_1 wn biimt fmtt_1 fmtt_0 con34b syl6bbr $.
$}
$( Theorem *5.501 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
${
	fpm5.501_0 $f wff ph $.
	fpm5.501_1 $f wff ps $.
	pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $= fpm5.501_0 fpm5.501_1 fpm5.501_0 fpm5.501_1 wb fpm5.501_0 fpm5.501_1 pm5.1im fpm5.501_0 fpm5.501_1 wb fpm5.501_0 fpm5.501_1 fpm5.501_0 fpm5.501_1 bi1 com12 impbid $.
$}
$( Implication in terms of implication and biconditional.  (Contributed by
     NM, 31-Mar-1994.)  (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)
${
	fibib_0 $f wff ph $.
	fibib_1 $f wff ps $.
	ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $= fibib_0 fibib_1 fibib_0 fibib_1 wb fibib_0 fibib_1 pm5.501 pm5.74i $.
$}
$( Implication in terms of implication and biconditional.  (Contributed by
     NM, 29-Apr-2005.)  (Proof shortened by Wolf Lammen, 21-Dec-2013.) $)
${
	fibibr_0 $f wff ph $.
	fibibr_1 $f wff ps $.
	ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $= fibibr_0 fibibr_1 fibibr_1 fibibr_0 wb fibibr_0 fibibr_1 fibibr_0 fibibr_1 wb fibibr_1 fibibr_0 wb fibibr_0 fibibr_1 pm5.501 fibibr_0 fibibr_1 bicom syl6bb pm5.74i $.
$}
$( A wff is equivalent to its equivalence with truth.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
${
	ftbt_0 $f wff ph $.
	ftbt_1 $f wff ps $.
	etbt_0 $e |- ph $.
	tbt $p |- ( ps <-> ( ps <-> ph ) ) $= ftbt_0 ftbt_1 ftbt_1 ftbt_0 wb wb etbt_0 ftbt_0 ftbt_1 ftbt_1 ftbt_0 wb ftbt_0 ftbt_1 ibibr pm5.74ri ax-mp $.
$}
$( The negation of a wff is equivalent to the wff's equivalence to
     falsehood.  (Contributed by Juha Arpiainen, 19-Jan-2006.)  (Proof
     shortened by Wolf Lammen, 28-Jan-2013.) $)
${
	fnbn2_0 $f wff ph $.
	fnbn2_1 $f wff ps $.
	nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $= fnbn2_0 wn fnbn2_1 wn fnbn2_0 wn fnbn2_1 wn wb fnbn2_0 fnbn2_1 wb fnbn2_0 wn fnbn2_1 wn pm5.501 fnbn2_0 fnbn2_1 notbi syl6bbr $.
$}
$( Transfer negation via an equivalence.  (Contributed by NM, 3-Oct-2007.)
     (Proof shortened by Wolf Lammen, 28-Jan-2013.) $)
${
	fbibif_0 $f wff ph $.
	fbibif_1 $f wff ps $.
	bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $= fbibif_1 wn fbibif_0 wn fbibif_1 fbibif_0 wb fbibif_0 fbibif_1 wb fbibif_1 fbibif_0 nbn2 fbibif_1 fbibif_0 bicom syl6rbb $.
$}
$( The negation of a wff is equivalent to the wff's equivalence to
       falsehood.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 3-Oct-2013.) $)
${
	fnbn_0 $f wff ph $.
	fnbn_1 $f wff ps $.
	enbn_0 $e |- -. ph $.
	nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $= fnbn_1 fnbn_0 wb fnbn_1 wn fnbn_0 wn fnbn_1 fnbn_0 wb fnbn_1 wn wb enbn_0 fnbn_1 fnbn_0 bibif ax-mp bicomi $.
$}
$( Transfer falsehood via equivalence.  (Contributed by NM,
       11-Sep-2006.) $)
${
	fnbn3_0 $f wff ph $.
	fnbn3_1 $f wff ps $.
	enbn3_0 $e |- ph $.
	nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $= fnbn3_0 wn fnbn3_1 fnbn3_0 enbn3_0 notnoti nbn $.
$}
$( Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ bi2 -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.) $)
${
	fpm5.21im_0 $f wff ph $.
	fpm5.21im_1 $f wff ps $.
	pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $= fpm5.21im_0 wn fpm5.21im_1 wn fpm5.21im_0 fpm5.21im_1 wb fpm5.21im_0 fpm5.21im_1 nbn2 biimpd $.
$}
$( Two falsehoods are equivalent.  (Contributed by NM, 4-Apr-2005.)  (Proof
       shortened by Wolf Lammen, 19-May-2013.) $)
${
	f2false_0 $f wff ph $.
	f2false_1 $f wff ps $.
	e2false_0 $e |- -. ph $.
	e2false_1 $e |- -. ps $.
	2false $p |- ( ph <-> ps ) $= f2false_0 f2false_1 f2false_0 wn f2false_1 wn e2false_0 e2false_1 2th con4bii $.
$}
$( Two falsehoods are equivalent (deduction rule).  (Contributed by NM,
       11-Oct-2013.) $)
${
	f2falsed_0 $f wff ph $.
	f2falsed_1 $f wff ps $.
	f2falsed_2 $f wff ch $.
	e2falsed_0 $e |- ( ph -> -. ps ) $.
	e2falsed_1 $e |- ( ph -> -. ch ) $.
	2falsed $p |- ( ph -> ( ps <-> ch ) ) $= f2falsed_0 f2falsed_1 f2falsed_2 f2falsed_0 f2falsed_1 f2falsed_2 e2falsed_0 pm2.21d f2falsed_0 f2falsed_2 f2falsed_1 e2falsed_1 pm2.21d impbid $.
$}
$( Two propositions implying a false one are equivalent.  (Contributed by
       NM, 16-Feb-1996.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
${
	fpm5.21ni_0 $f wff ph $.
	fpm5.21ni_1 $f wff ps $.
	fpm5.21ni_2 $f wff ch $.
	epm5.21ni_0 $e |- ( ph -> ps ) $.
	epm5.21ni_1 $e |- ( ch -> ps ) $.
	pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $= fpm5.21ni_1 wn fpm5.21ni_0 fpm5.21ni_2 fpm5.21ni_0 fpm5.21ni_1 epm5.21ni_0 con3i fpm5.21ni_2 fpm5.21ni_1 epm5.21ni_1 con3i 2falsed $.
$}
$( Eliminate an antecedent implied by each side of a biconditional.
         (Contributed by NM, 21-May-1999.) $)
${
	fpm5.21nii_0 $f wff ph $.
	fpm5.21nii_1 $f wff ps $.
	fpm5.21nii_2 $f wff ch $.
	epm5.21nii_0 $e |- ( ph -> ps ) $.
	epm5.21nii_1 $e |- ( ch -> ps ) $.
	epm5.21nii_2 $e |- ( ps -> ( ph <-> ch ) ) $.
	pm5.21nii $p |- ( ph <-> ch ) $= fpm5.21nii_1 fpm5.21nii_0 fpm5.21nii_2 wb epm5.21nii_2 fpm5.21nii_0 fpm5.21nii_1 fpm5.21nii_2 epm5.21nii_0 epm5.21nii_1 pm5.21ni pm2.61i $.
$}
$( Eliminate an antecedent implied by each side of a biconditional,
       deduction version.  (Contributed by Paul Chapman, 21-Nov-2012.)  (Proof
       shortened by Wolf Lammen, 6-Oct-2013.) $)
${
	fpm5.21ndd_0 $f wff ph $.
	fpm5.21ndd_1 $f wff ps $.
	fpm5.21ndd_2 $f wff ch $.
	fpm5.21ndd_3 $f wff th $.
	epm5.21ndd_0 $e |- ( ph -> ( ch -> ps ) ) $.
	epm5.21ndd_1 $e |- ( ph -> ( th -> ps ) ) $.
	epm5.21ndd_2 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
	pm5.21ndd $p |- ( ph -> ( ch <-> th ) ) $= fpm5.21ndd_0 fpm5.21ndd_1 fpm5.21ndd_2 fpm5.21ndd_3 wb epm5.21ndd_2 fpm5.21ndd_0 fpm5.21ndd_1 wn fpm5.21ndd_2 wn fpm5.21ndd_3 wn fpm5.21ndd_2 fpm5.21ndd_3 wb fpm5.21ndd_0 fpm5.21ndd_2 fpm5.21ndd_1 epm5.21ndd_0 con3d fpm5.21ndd_0 fpm5.21ndd_3 fpm5.21ndd_1 epm5.21ndd_1 con3d fpm5.21ndd_2 fpm5.21ndd_3 pm5.21im syl6c pm2.61d $.
$}
$( Combine antecedents into a single bi-conditional.  This inference,
       reminiscent of ~ ja , is reversible:  The hypotheses can be deduced from
       the conclusion alone (see ~ pm5.1im and ~ pm5.21im ).  (Contributed by
       Wolf Lammen, 13-May-2013.) $)
${
	fbija_0 $f wff ph $.
	fbija_1 $f wff ps $.
	fbija_2 $f wff ch $.
	ebija_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ebija_1 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
	bija $p |- ( ( ph <-> ps ) -> ch ) $= fbija_0 fbija_1 wb fbija_1 fbija_2 fbija_1 fbija_0 fbija_1 wb fbija_0 fbija_2 fbija_0 fbija_1 bi2 ebija_0 syli fbija_1 wn fbija_0 fbija_1 wb fbija_0 wn fbija_2 fbija_0 fbija_1 wb fbija_0 fbija_1 fbija_0 fbija_1 bi1 con3d ebija_1 syli pm2.61d $.
$}
$( Theorem *5.18 of [WhiteheadRussell] p. 124.  This theorem says that
     logical equivalence is the same as negated "exclusive-or."  (Contributed
     by NM, 28-Jun-2002.)  (Proof shortened by Andrew Salmon, 20-Jun-2011.)
     (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)
${
	fpm5.18_0 $f wff ph $.
	fpm5.18_1 $f wff ps $.
	pm5.18 $p |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) $= fpm5.18_0 fpm5.18_0 fpm5.18_1 wb fpm5.18_0 fpm5.18_1 wn wb wn wb fpm5.18_0 fpm5.18_0 fpm5.18_1 wn wb wn fpm5.18_1 fpm5.18_0 fpm5.18_1 wb fpm5.18_0 fpm5.18_1 fpm5.18_0 fpm5.18_1 wn wb fpm5.18_0 fpm5.18_1 wn pm5.501 con1bid fpm5.18_0 fpm5.18_1 pm5.501 bitr2d fpm5.18_0 wn fpm5.18_0 fpm5.18_1 wn wb wn fpm5.18_1 wn fpm5.18_0 fpm5.18_1 wb fpm5.18_0 wn fpm5.18_1 wn fpm5.18_0 fpm5.18_1 wn wb fpm5.18_0 fpm5.18_1 wn nbn2 con1bid fpm5.18_0 fpm5.18_1 nbn2 bitr2d pm2.61i $.
$}
$( Two ways to express "exclusive or."  (Contributed by NM, 1-Jan-2006.) $)
${
	fxor3_0 $f wff ph $.
	fxor3_1 $f wff ps $.
	xor3 $p |- ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) $= fxor3_0 fxor3_1 wn wb fxor3_0 fxor3_1 wb wn fxor3_0 fxor3_1 wb fxor3_0 fxor3_1 wn wb fxor3_0 fxor3_1 pm5.18 con2bii bicomi $.
$}
$( Move negation outside of biconditional.  Compare Theorem *5.18 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 20-Sep-2013.) $)
${
	fnbbn_0 $f wff ph $.
	fnbbn_1 $f wff ps $.
	nbbn $p |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) $= fnbbn_0 fnbbn_1 wb wn fnbbn_0 fnbbn_1 wn wb fnbbn_1 fnbbn_0 wn wb fnbbn_0 wn fnbbn_1 wb fnbbn_0 fnbbn_1 xor3 fnbbn_0 fnbbn_1 con2bi fnbbn_1 fnbbn_0 wn bicom 3bitrri $.
$}
$( Associative law for the biconditional.  An axiom of system DS in Vladimir
     Lifschitz, "On calculational proofs", Annals of Pure and Applied Logic,
     113:207-224, 2002,
     ~ http://www.cs.utexas.edu/users/ai-lab/pub-view.php?PubID=26805 .
     Interestingly, this law was not included in _Principia Mathematica_ but
     was apparently first noted by Jan Lukasiewicz circa 1923.  (Contributed by
     NM, 8-Jan-2005.)  (Proof shortened by Juha Arpiainen, 19-Jan-2006.)
     (Proof shortened by Wolf Lammen, 21-Sep-2013.) $)
${
	fbiass_0 $f wff ph $.
	fbiass_1 $f wff ps $.
	fbiass_2 $f wff ch $.
	biass $p |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $= fbiass_0 fbiass_0 fbiass_1 wb fbiass_2 wb fbiass_0 fbiass_1 fbiass_2 wb wb wb fbiass_0 fbiass_1 fbiass_2 wb fbiass_0 fbiass_1 wb fbiass_2 wb fbiass_0 fbiass_1 fbiass_2 wb wb fbiass_0 fbiass_1 fbiass_0 fbiass_1 wb fbiass_2 fbiass_0 fbiass_1 pm5.501 bibi1d fbiass_0 fbiass_1 fbiass_2 wb pm5.501 bitr3d fbiass_0 wn fbiass_1 fbiass_2 wb wn fbiass_0 fbiass_1 wb fbiass_2 wb fbiass_0 fbiass_1 fbiass_2 wb wb fbiass_1 fbiass_2 wb wn fbiass_1 wn fbiass_2 wb fbiass_0 wn fbiass_0 fbiass_1 wb fbiass_2 wb fbiass_1 fbiass_2 nbbn fbiass_0 wn fbiass_1 wn fbiass_0 fbiass_1 wb fbiass_2 fbiass_0 fbiass_1 nbn2 bibi1d syl5bbr fbiass_0 fbiass_1 fbiass_2 wb nbn2 bitr3d pm2.61i $.
$}
$( Theorem *5.19 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)
${
	fpm5.19_0 $f wff ph $.
	pm5.19 $p |- -. ( ph <-> -. ph ) $= fpm5.19_0 fpm5.19_0 wb fpm5.19_0 fpm5.19_0 wn wb wn fpm5.19_0 biid fpm5.19_0 fpm5.19_0 pm5.18 mpbi $.
$}
$( Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122.  (Contributed by NM, 5-Aug-1993.) $)
${
	fbi2.04_0 $f wff ph $.
	fbi2.04_1 $f wff ps $.
	fbi2.04_2 $f wff ch $.
	bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $= fbi2.04_0 fbi2.04_1 fbi2.04_2 wi wi fbi2.04_1 fbi2.04_0 fbi2.04_2 wi wi fbi2.04_0 fbi2.04_1 fbi2.04_2 pm2.04 fbi2.04_1 fbi2.04_0 fbi2.04_2 pm2.04 impbii $.
$}
$( Antecedent absorption implication.  Theorem *5.4 of [WhiteheadRussell]
     p. 125.  (Contributed by NM, 5-Aug-1993.) $)
${
	fpm5.4_0 $f wff ph $.
	fpm5.4_1 $f wff ps $.
	pm5.4 $p |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ) $= fpm5.4_0 fpm5.4_0 fpm5.4_1 wi wi fpm5.4_0 fpm5.4_1 wi fpm5.4_0 fpm5.4_1 pm2.43 fpm5.4_0 fpm5.4_1 wi fpm5.4_0 ax-1 impbii $.
$}
$( Distributive law for implication.  Compare Theorem *5.41 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 5-Aug-1993.) $)
${
	fimdi_0 $f wff ph $.
	fimdi_1 $f wff ps $.
	fimdi_2 $f wff ch $.
	imdi $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $= fimdi_0 fimdi_1 fimdi_2 wi wi fimdi_0 fimdi_1 wi fimdi_0 fimdi_2 wi wi fimdi_0 fimdi_1 fimdi_2 ax-2 fimdi_0 fimdi_1 fimdi_2 pm2.86 impbii $.
$}
$( Theorem *5.41 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 12-Oct-2012.) $)
${
	fpm5.41_0 $f wff ph $.
	fpm5.41_1 $f wff ps $.
	fpm5.41_2 $f wff ch $.
	pm5.41 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) <-> ( ph -> ( ps -> ch ) ) ) $= fpm5.41_0 fpm5.41_1 fpm5.41_2 wi wi fpm5.41_0 fpm5.41_1 wi fpm5.41_0 fpm5.41_2 wi wi fpm5.41_0 fpm5.41_1 fpm5.41_2 imdi bicomi $.
$}
$( Theorem *4.8 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
${
	fpm4.8_0 $f wff ph $.
	pm4.8 $p |- ( ( ph -> -. ph ) <-> -. ph ) $= fpm4.8_0 fpm4.8_0 wn wi fpm4.8_0 wn fpm4.8_0 pm2.01 fpm4.8_0 wn fpm4.8_0 ax-1 impbii $.
$}
$( Theorem *4.81 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
${
	fpm4.81_0 $f wff ph $.
	pm4.81 $p |- ( ( -. ph -> ph ) <-> ph ) $= fpm4.81_0 wn fpm4.81_0 wi fpm4.81_0 fpm4.81_0 pm2.18 fpm4.81_0 fpm4.81_0 pm2.24 impbii $.
$}
$( Simplify an implication between two implications when the antecedent of
     the first is a consequence of the antecedent of the second.  The reverse
     form is useful in producing the successor step in induction proofs.
     (Contributed by Paul Chapman, 22-Jun-2011.)  (Proof shortened by Wolf
     Lammen, 14-Sep-2013.) $)
${
	fimim21b_0 $f wff ph $.
	fimim21b_1 $f wff ps $.
	fimim21b_2 $f wff ch $.
	fimim21b_3 $f wff th $.
	imim21b $p |- ( ( ps -> ph ) -> ( ( ( ph -> ch ) -> ( ps -> th ) ) <-> ( ps -> ( ch -> th ) ) ) ) $= fimim21b_0 fimim21b_2 wi fimim21b_1 fimim21b_3 wi wi fimim21b_1 fimim21b_0 fimim21b_2 wi fimim21b_3 wi wi fimim21b_1 fimim21b_0 wi fimim21b_1 fimim21b_2 fimim21b_3 wi wi fimim21b_0 fimim21b_2 wi fimim21b_1 fimim21b_3 bi2.04 fimim21b_1 fimim21b_0 wi fimim21b_1 fimim21b_0 fimim21b_2 wi fimim21b_3 wi fimim21b_2 fimim21b_3 wi fimim21b_0 fimim21b_0 fimim21b_2 wi fimim21b_3 wi fimim21b_2 fimim21b_3 wi wb fimim21b_1 fimim21b_0 fimim21b_0 fimim21b_2 wi fimim21b_2 fimim21b_3 fimim21b_0 fimim21b_2 pm5.5 imbi1d imim2i pm5.74d syl5bb $.
$}

