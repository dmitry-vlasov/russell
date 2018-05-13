$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_negation.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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

$(Declare the biconditional connective. $)

$c <-> $.

$(Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)

$(Extend our wff definition to include the biconditional connective. $)

${
	$v ph ps  $.
	f0_wb $f wff ph $.
	f1_wb $f wff ps $.
	a_wb $a wff ( ph <-> ps ) $.
$}

$(Define the biconditional (logical 'iff').

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
	$v ph ps  $.
	f0_df-bi $f wff ph $.
	f1_df-bi $f wff ps $.
	a_df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.
$}

$($j justification 'bijust' for 'df-bi'; $)

$(Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)

${
	$v ph ps  $.
	f0_bi1 $f wff ph $.
	f1_bi1 $f wff ps $.
	p_bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $= f0_bi1 f1_bi1 a_df-bi f0_bi1 f1_bi1 a_wb f0_bi1 f1_bi1 a_wi f1_bi1 f0_bi1 a_wi a_wn a_wi a_wn a_wi f0_bi1 f1_bi1 a_wi f1_bi1 f0_bi1 a_wi a_wn a_wi a_wn f0_bi1 f1_bi1 a_wb a_wi a_wn p_simplim f0_bi1 f1_bi1 a_wb f0_bi1 f1_bi1 a_wi f1_bi1 f0_bi1 a_wi a_wn a_wi a_wn a_wi f0_bi1 f1_bi1 a_wi f1_bi1 f0_bi1 a_wi a_wn a_wi a_wn f0_bi1 f1_bi1 a_wb a_wi a_wn a_wi a_wn f0_bi1 f1_bi1 a_wb f0_bi1 f1_bi1 a_wi f1_bi1 f0_bi1 a_wi a_wn a_wi a_wn a_wi a_ax-mp f0_bi1 f1_bi1 a_wi f1_bi1 f0_bi1 a_wi a_wn p_simplim f0_bi1 f1_bi1 a_wb f0_bi1 f1_bi1 a_wi f1_bi1 f0_bi1 a_wi a_wn a_wi a_wn f0_bi1 f1_bi1 a_wi p_syl $.
$}

$(Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)

${
	$v ph ps  $.
	f0_bi3 $f wff ph $.
	f1_bi3 $f wff ps $.
	p_bi3 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $= f0_bi3 f1_bi3 a_df-bi f0_bi3 f1_bi3 a_wb f0_bi3 f1_bi3 a_wi f1_bi3 f0_bi3 a_wi a_wn a_wi a_wn a_wi f0_bi3 f1_bi3 a_wi f1_bi3 f0_bi3 a_wi a_wn a_wi a_wn f0_bi3 f1_bi3 a_wb a_wi p_simprim f0_bi3 f1_bi3 a_wb f0_bi3 f1_bi3 a_wi f1_bi3 f0_bi3 a_wi a_wn a_wi a_wn a_wi f0_bi3 f1_bi3 a_wi f1_bi3 f0_bi3 a_wi a_wn a_wi a_wn f0_bi3 f1_bi3 a_wb a_wi a_wn a_wi a_wn f0_bi3 f1_bi3 a_wi f1_bi3 f0_bi3 a_wi a_wn a_wi a_wn f0_bi3 f1_bi3 a_wb a_wi a_ax-mp f0_bi3 f1_bi3 a_wi f1_bi3 f0_bi3 a_wi f0_bi3 f1_bi3 a_wb p_expi $.
$}

$(Infer an equivalence from an implication and its converse.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_impbii $f wff ph $.
	f1_impbii $f wff ps $.
	e0_impbii $e |- ( ph -> ps ) $.
	e1_impbii $e |- ( ps -> ph ) $.
	p_impbii $p |- ( ph <-> ps ) $= e0_impbii e1_impbii f0_impbii f1_impbii p_bi3 f0_impbii f1_impbii a_wi f1_impbii f0_impbii a_wi f0_impbii f1_impbii a_wb p_mp2 $.
$}

$(Deduce an equivalence from two implications.  (Contributed by Rodolfo
       Medina, 12-Oct-2010.) $)

${
	$v ph ps ch th  $.
	f0_impbidd $f wff ph $.
	f1_impbidd $f wff ps $.
	f2_impbidd $f wff ch $.
	f3_impbidd $f wff th $.
	e0_impbidd $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	e1_impbidd $e |- ( ph -> ( ps -> ( th -> ch ) ) ) $.
	p_impbidd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $= e0_impbidd e1_impbidd f2_impbidd f3_impbidd p_bi3 f0_impbidd f1_impbidd f2_impbidd f3_impbidd a_wi f3_impbidd f2_impbidd a_wi f2_impbidd f3_impbidd a_wb p_syl6c $.
$}

$(Deduce an equivalence from two implications.  (Contributed by Wolf
       Lammen, 12-May-2013.) $)

${
	$v ph ps ch th  $.
	f0_impbid21d $f wff ph $.
	f1_impbid21d $f wff ps $.
	f2_impbid21d $f wff ch $.
	f3_impbid21d $f wff th $.
	e0_impbid21d $e |- ( ps -> ( ch -> th ) ) $.
	e1_impbid21d $e |- ( ph -> ( th -> ch ) ) $.
	p_impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $= e0_impbid21d f1_impbid21d f2_impbid21d f3_impbid21d a_wi a_wi f0_impbid21d p_a1i e1_impbid21d f0_impbid21d f3_impbid21d f2_impbid21d a_wi f1_impbid21d p_a1d f0_impbid21d f1_impbid21d f2_impbid21d f3_impbid21d p_impbidd $.
$}

$(Deduce an equivalence from two implications.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Wolf Lammen, 3-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_impbid $f wff ph $.
	f1_impbid $f wff ps $.
	f2_impbid $f wff ch $.
	e0_impbid $e |- ( ph -> ( ps -> ch ) ) $.
	e1_impbid $e |- ( ph -> ( ch -> ps ) ) $.
	p_impbid $p |- ( ph -> ( ps <-> ch ) ) $= e0_impbid e1_impbid f0_impbid f0_impbid f1_impbid f2_impbid p_impbid21d f0_impbid f1_impbid f2_impbid a_wb p_pm2.43i $.
$}

$(Relate the biconditional connective to primitive connectives.  See
     ~ dfbi1gb for an unusual version proved directly from axioms.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_dfbi1 $f wff ph $.
	f1_dfbi1 $f wff ps $.
	p_dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $= f0_dfbi1 f1_dfbi1 a_df-bi f0_dfbi1 f1_dfbi1 a_wb f0_dfbi1 f1_dfbi1 a_wi f1_dfbi1 f0_dfbi1 a_wi a_wn a_wi a_wn a_wi f0_dfbi1 f1_dfbi1 a_wi f1_dfbi1 f0_dfbi1 a_wi a_wn a_wi a_wn f0_dfbi1 f1_dfbi1 a_wb a_wi a_wn p_simplim f0_dfbi1 f1_dfbi1 a_wb f0_dfbi1 f1_dfbi1 a_wi f1_dfbi1 f0_dfbi1 a_wi a_wn a_wi a_wn a_wi f0_dfbi1 f1_dfbi1 a_wi f1_dfbi1 f0_dfbi1 a_wi a_wn a_wi a_wn f0_dfbi1 f1_dfbi1 a_wb a_wi a_wn a_wi a_wn f0_dfbi1 f1_dfbi1 a_wb f0_dfbi1 f1_dfbi1 a_wi f1_dfbi1 f0_dfbi1 a_wi a_wn a_wi a_wn a_wi a_ax-mp f0_dfbi1 f1_dfbi1 p_bi3 f0_dfbi1 f1_dfbi1 a_wi f1_dfbi1 f0_dfbi1 a_wi f0_dfbi1 f1_dfbi1 a_wb p_impi f0_dfbi1 f1_dfbi1 a_wb f0_dfbi1 f1_dfbi1 a_wi f1_dfbi1 f0_dfbi1 a_wi a_wn a_wi a_wn p_impbii $.
$}

$(This proof of ~ dfbi1 , discovered by Gregory Bush on 8-Mar-2004, has
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
	$v ph ps  $.
	f0_dfbi1gb $f wff ph $.
	f1_dfbi1gb $f wff ps $.
	i0_dfbi1gb $f wff ch $.
	i1_dfbi1gb $f wff th $.
	p_dfbi1gb $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $= f0_dfbi1gb f1_dfbi1gb a_df-bi i0_dfbi1gb i1_dfbi1gb a_ax-1 f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi a_ax-1 f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_df-bi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi a_wn i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wn a_ax-1 f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi a_wn i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi a_wn a_wi a_ax-mp i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi a_ax-3 i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wi a_ax-mp f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_ax-1 f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wi a_wi a_ax-mp f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_ax-2 f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wi a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wi a_wi a_ax-mp f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn a_wi a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wi a_ax-mp f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_ax-3 f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wn i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi a_wn a_wi i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_wi a_ax-mp i0_dfbi1gb i1_dfbi1gb i0_dfbi1gb a_wi a_wi f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_wi a_ax-mp f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wi f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb a_wi a_wn a_wi a_wn f0_dfbi1gb f1_dfbi1gb a_wb f0_dfbi1gb f1_dfbi1gb a_wi f1_dfbi1gb f0_dfbi1gb a_wi a_wn a_wi a_wn a_wb a_ax-mp $.
$}

$(Infer an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_biimpi $f wff ph $.
	f1_biimpi $f wff ps $.
	e0_biimpi $e |- ( ph <-> ps ) $.
	p_biimpi $p |- ( ph -> ps ) $= e0_biimpi f0_biimpi f1_biimpi p_bi1 f0_biimpi f1_biimpi a_wb f0_biimpi f1_biimpi a_wi a_ax-mp $.
$}

$(A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_sylbi $f wff ph $.
	f1_sylbi $f wff ps $.
	f2_sylbi $f wff ch $.
	e0_sylbi $e |- ( ph <-> ps ) $.
	e1_sylbi $e |- ( ps -> ch ) $.
	p_sylbi $p |- ( ph -> ch ) $= e0_sylbi f0_sylbi f1_sylbi p_biimpi e1_sylbi f0_sylbi f1_sylbi f2_sylbi p_syl $.
$}

$(A mixed syllogism inference from an implication and a biconditional.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_sylib $f wff ph $.
	f1_sylib $f wff ps $.
	f2_sylib $f wff ch $.
	e0_sylib $e |- ( ph -> ps ) $.
	e1_sylib $e |- ( ps <-> ch ) $.
	p_sylib $p |- ( ph -> ch ) $= e0_sylib e1_sylib f1_sylib f2_sylib p_biimpi f0_sylib f1_sylib f2_sylib p_syl $.
$}

$(Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)

${
	$v ph ps  $.
	f0_bi2 $f wff ph $.
	f1_bi2 $f wff ps $.
	p_bi2 $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $= f0_bi2 f1_bi2 p_dfbi1 f0_bi2 f1_bi2 a_wi f1_bi2 f0_bi2 a_wi p_simprim f0_bi2 f1_bi2 a_wb f0_bi2 f1_bi2 a_wi f1_bi2 f0_bi2 a_wi a_wn a_wi a_wn f1_bi2 f0_bi2 a_wi p_sylbi $.
$}

$(Commutative law for equivalence.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)

${
	$v ph ps  $.
	f0_bicom1 $f wff ph $.
	f1_bicom1 $f wff ps $.
	p_bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $= f0_bicom1 f1_bicom1 p_bi2 f0_bicom1 f1_bicom1 p_bi1 f0_bicom1 f1_bicom1 a_wb f1_bicom1 f0_bicom1 p_impbid $.
$}

$(Commutative law for equivalence.  Theorem *4.21 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_bicom $f wff ph $.
	f1_bicom $f wff ps $.
	p_bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $= f0_bicom f1_bicom p_bicom1 f1_bicom f0_bicom p_bicom1 f0_bicom f1_bicom a_wb f1_bicom f0_bicom a_wb p_impbii $.
$}

$(Commute two sides of a biconditional in a deduction.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_bicomd $f wff ph $.
	f1_bicomd $f wff ps $.
	f2_bicomd $f wff ch $.
	e0_bicomd $e |- ( ph -> ( ps <-> ch ) ) $.
	p_bicomd $p |- ( ph -> ( ch <-> ps ) ) $= e0_bicomd f1_bicomd f2_bicomd p_bicom f0_bicomd f1_bicomd f2_bicomd a_wb f2_bicomd f1_bicomd a_wb p_sylib $.
$}

$(Inference from commutative law for logical equivalence.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_bicomi $f wff ph $.
	f1_bicomi $f wff ps $.
	e0_bicomi $e |- ( ph <-> ps ) $.
	p_bicomi $p |- ( ps <-> ph ) $= e0_bicomi f0_bicomi f1_bicomi p_bicom1 f0_bicomi f1_bicomi a_wb f1_bicomi f0_bicomi a_wb a_ax-mp $.
$}

$(Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.) $)

${
	$v ph ps ch  $.
	f0_impbid1 $f wff ph $.
	f1_impbid1 $f wff ps $.
	f2_impbid1 $f wff ch $.
	e0_impbid1 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_impbid1 $e |- ( ch -> ps ) $.
	p_impbid1 $p |- ( ph -> ( ps <-> ch ) ) $= e0_impbid1 e1_impbid1 f2_impbid1 f1_impbid1 a_wi f0_impbid1 p_a1i f0_impbid1 f1_impbid1 f2_impbid1 p_impbid $.
$}

$(Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.)  (Proof shortened by Wolf Lammen, 27-Sep-2013.) $)

${
	$v ph ps ch  $.
	f0_impbid2 $f wff ph $.
	f1_impbid2 $f wff ps $.
	f2_impbid2 $f wff ch $.
	e0_impbid2 $e |- ( ps -> ch ) $.
	e1_impbid2 $e |- ( ph -> ( ch -> ps ) ) $.
	p_impbid2 $p |- ( ph -> ( ps <-> ch ) ) $= e1_impbid2 e0_impbid2 f0_impbid2 f2_impbid2 f1_impbid2 p_impbid1 f0_impbid2 f2_impbid2 f1_impbid2 p_bicomd $.
$}

$(A variation on ~ impbid with contraposition.  (Contributed by Jeff
       Hankins, 3-Jul-2009.) $)

${
	$v ph ps ch  $.
	f0_impcon4bid $f wff ph $.
	f1_impcon4bid $f wff ps $.
	f2_impcon4bid $f wff ch $.
	e0_impcon4bid $e |- ( ph -> ( ps -> ch ) ) $.
	e1_impcon4bid $e |- ( ph -> ( -. ps -> -. ch ) ) $.
	p_impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $= e0_impcon4bid e1_impcon4bid f0_impcon4bid f1_impcon4bid f2_impcon4bid p_con4d f0_impcon4bid f1_impcon4bid f2_impcon4bid p_impbid $.
$}

$(Infer a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 16-Sep-2013.) $)

${
	$v ph ps  $.
	f0_biimpri $f wff ph $.
	f1_biimpri $f wff ps $.
	e0_biimpri $e |- ( ph <-> ps ) $.
	p_biimpri $p |- ( ps -> ph ) $= e0_biimpri f0_biimpri f1_biimpri p_bicomi f1_biimpri f0_biimpri p_biimpi $.
$}

$(Deduce an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_biimpd $f wff ph $.
	f1_biimpd $f wff ps $.
	f2_biimpd $f wff ch $.
	e0_biimpd $e |- ( ph -> ( ps <-> ch ) ) $.
	p_biimpd $p |- ( ph -> ( ps -> ch ) ) $= e0_biimpd f1_biimpd f2_biimpd p_bi1 f0_biimpd f1_biimpd f2_biimpd a_wb f1_biimpd f2_biimpd a_wi p_syl $.
$}

$(An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_mpbi $f wff ph $.
	f1_mpbi $f wff ps $.
	e0_mpbi $e |- ph $.
	e1_mpbi $e |- ( ph <-> ps ) $.
	p_mpbi $p |- ps $= e0_mpbi e1_mpbi f0_mpbi f1_mpbi p_biimpi f0_mpbi f1_mpbi a_ax-mp $.
$}

$(An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_mpbir $f wff ph $.
	f1_mpbir $f wff ps $.
	e0_mpbir $e |- ps $.
	e1_mpbir $e |- ( ph <-> ps ) $.
	p_mpbir $p |- ph $= e0_mpbir e1_mpbir f0_mpbir f1_mpbir p_biimpri f1_mpbir f0_mpbir a_ax-mp $.
$}

$(A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_mpbid $f wff ph $.
	f1_mpbid $f wff ps $.
	f2_mpbid $f wff ch $.
	e0_mpbid $e |- ( ph -> ps ) $.
	e1_mpbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mpbid $p |- ( ph -> ch ) $= e0_mpbid e1_mpbid f0_mpbid f1_mpbid f2_mpbid p_biimpd f0_mpbid f1_mpbid f2_mpbid p_mpd $.
$}

$(An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)

${
	$v ph ps ch  $.
	f0_mpbii $f wff ph $.
	f1_mpbii $f wff ps $.
	f2_mpbii $f wff ch $.
	e0_mpbii $e |- ps $.
	e1_mpbii $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mpbii $p |- ( ph -> ch ) $= e0_mpbii f1_mpbii f0_mpbii p_a1i e1_mpbii f0_mpbii f1_mpbii f2_mpbii p_mpbid $.
$}

$(A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_sylibr $f wff ph $.
	f1_sylibr $f wff ps $.
	f2_sylibr $f wff ch $.
	e0_sylibr $e |- ( ph -> ps ) $.
	e1_sylibr $e |- ( ch <-> ps ) $.
	p_sylibr $p |- ( ph -> ch ) $= e0_sylibr e1_sylibr f2_sylibr f1_sylibr p_biimpri f0_sylibr f1_sylibr f2_sylibr p_syl $.
$}

$(A mixed syllogism inference from a biconditional and an implication.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_sylbir $f wff ph $.
	f1_sylbir $f wff ps $.
	f2_sylbir $f wff ch $.
	e0_sylbir $e |- ( ps <-> ph ) $.
	e1_sylbir $e |- ( ps -> ch ) $.
	p_sylbir $p |- ( ph -> ch ) $= e0_sylbir f1_sylbir f0_sylbir p_biimpri e1_sylbir f0_sylbir f1_sylbir f2_sylbir p_syl $.
$}

$(A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_sylibd $f wff ph $.
	f1_sylibd $f wff ps $.
	f2_sylibd $f wff ch $.
	f3_sylibd $f wff th $.
	e0_sylibd $e |- ( ph -> ( ps -> ch ) ) $.
	e1_sylibd $e |- ( ph -> ( ch <-> th ) ) $.
	p_sylibd $p |- ( ph -> ( ps -> th ) ) $= e0_sylibd e1_sylibd f0_sylibd f2_sylibd f3_sylibd p_biimpd f0_sylibd f1_sylibd f2_sylibd f3_sylibd p_syld $.
$}

$(A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_sylbid $f wff ph $.
	f1_sylbid $f wff ps $.
	f2_sylbid $f wff ch $.
	f3_sylbid $f wff th $.
	e0_sylbid $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_sylbid $e |- ( ph -> ( ch -> th ) ) $.
	p_sylbid $p |- ( ph -> ( ps -> th ) ) $= e0_sylbid f0_sylbid f1_sylbid f2_sylbid p_biimpd e1_sylbid f0_sylbid f1_sylbid f2_sylbid f3_sylbid p_syld $.
$}

$(A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 9-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_mpbidi $f wff ph $.
	f1_mpbidi $f wff ps $.
	f2_mpbidi $f wff ch $.
	f3_mpbidi $f wff th $.
	e0_mpbidi $e |- ( th -> ( ph -> ps ) ) $.
	e1_mpbidi $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mpbidi $p |- ( th -> ( ph -> ch ) ) $= e0_mpbidi e1_mpbidi f0_mpbidi f1_mpbidi f2_mpbidi p_biimpd f3_mpbidi f0_mpbidi f1_mpbidi f2_mpbidi p_sylcom $.
$}

$(A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl5bi $f wff ph $.
	f1_syl5bi $f wff ps $.
	f2_syl5bi $f wff ch $.
	f3_syl5bi $f wff th $.
	e0_syl5bi $e |- ( ph <-> ps ) $.
	e1_syl5bi $e |- ( ch -> ( ps -> th ) ) $.
	p_syl5bi $p |- ( ch -> ( ph -> th ) ) $= e0_syl5bi f0_syl5bi f1_syl5bi p_biimpi e1_syl5bi f0_syl5bi f1_syl5bi f2_syl5bi f3_syl5bi p_syl5 $.
$}

$(A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl5bir $f wff ph $.
	f1_syl5bir $f wff ps $.
	f2_syl5bir $f wff ch $.
	f3_syl5bir $f wff th $.
	e0_syl5bir $e |- ( ps <-> ph ) $.
	e1_syl5bir $e |- ( ch -> ( ps -> th ) ) $.
	p_syl5bir $p |- ( ch -> ( ph -> th ) ) $= e0_syl5bir f1_syl5bir f0_syl5bir p_biimpri e1_syl5bir f0_syl5bir f1_syl5bir f2_syl5bir f3_syl5bir p_syl5 $.
$}

$(A mixed syllogism inference.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl5ib $f wff ph $.
	f1_syl5ib $f wff ps $.
	f2_syl5ib $f wff ch $.
	f3_syl5ib $f wff th $.
	e0_syl5ib $e |- ( ph -> ps ) $.
	e1_syl5ib $e |- ( ch -> ( ps <-> th ) ) $.
	p_syl5ib $p |- ( ch -> ( ph -> th ) ) $= e0_syl5ib e1_syl5ib f2_syl5ib f1_syl5ib f3_syl5ib p_biimpd f0_syl5ib f1_syl5ib f2_syl5ib f3_syl5ib p_syl5 $.
$}

$(A mixed syllogism inference.  (Contributed by NM, 19-Jun-2007.) $)

${
	$v ph ps ch th  $.
	f0_syl5ibcom $f wff ph $.
	f1_syl5ibcom $f wff ps $.
	f2_syl5ibcom $f wff ch $.
	f3_syl5ibcom $f wff th $.
	e0_syl5ibcom $e |- ( ph -> ps ) $.
	e1_syl5ibcom $e |- ( ch -> ( ps <-> th ) ) $.
	p_syl5ibcom $p |- ( ph -> ( ch -> th ) ) $= e0_syl5ibcom e1_syl5ibcom f0_syl5ibcom f1_syl5ibcom f2_syl5ibcom f3_syl5ibcom p_syl5ib f2_syl5ibcom f0_syl5ibcom f3_syl5ibcom p_com12 $.
$}

$(A mixed syllogism inference.  (Contributed by NM, 3-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_syl5ibr $f wff ph $.
	f1_syl5ibr $f wff ps $.
	f2_syl5ibr $f wff ch $.
	f3_syl5ibr $f wff th $.
	e0_syl5ibr $e |- ( ph -> th ) $.
	e1_syl5ibr $e |- ( ch -> ( ps <-> th ) ) $.
	p_syl5ibr $p |- ( ch -> ( ph -> ps ) ) $= e0_syl5ibr e1_syl5ibr f2_syl5ibr f1_syl5ibr f3_syl5ibr p_bicomd f0_syl5ibr f3_syl5ibr f2_syl5ibr f1_syl5ibr p_syl5ib $.
$}

$(A mixed syllogism inference.  (Contributed by NM, 20-Jun-2007.) $)

${
	$v ph ps ch th  $.
	f0_syl5ibrcom $f wff ph $.
	f1_syl5ibrcom $f wff ps $.
	f2_syl5ibrcom $f wff ch $.
	f3_syl5ibrcom $f wff th $.
	e0_syl5ibrcom $e |- ( ph -> th ) $.
	e1_syl5ibrcom $e |- ( ch -> ( ps <-> th ) ) $.
	p_syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $= e0_syl5ibrcom e1_syl5ibrcom f0_syl5ibrcom f1_syl5ibrcom f2_syl5ibrcom f3_syl5ibrcom p_syl5ibr f2_syl5ibrcom f0_syl5ibrcom f1_syl5ibrcom p_com12 $.
$}

$(Deduce a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)

${
	$v ph ps ch  $.
	f0_biimprd $f wff ph $.
	f1_biimprd $f wff ps $.
	f2_biimprd $f wff ch $.
	e0_biimprd $e |- ( ph -> ( ps <-> ch ) ) $.
	p_biimprd $p |- ( ph -> ( ch -> ps ) ) $= f2_biimprd p_id e0_biimprd f2_biimprd f1_biimprd f0_biimprd f2_biimprd p_syl5ibr $.
$}

$(Deduce a commuted implication from a logical equivalence.  (Contributed
       by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)

${
	$v ph ps ch  $.
	f0_biimpcd $f wff ph $.
	f1_biimpcd $f wff ps $.
	f2_biimpcd $f wff ch $.
	e0_biimpcd $e |- ( ph -> ( ps <-> ch ) ) $.
	p_biimpcd $p |- ( ps -> ( ph -> ch ) ) $= f1_biimpcd p_id e0_biimpcd f1_biimpcd f1_biimpcd f0_biimpcd f2_biimpcd p_syl5ibcom $.
$}

$(Deduce a converse commuted implication from a logical equivalence.
       (Contributed by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen,
       20-Dec-2013.) $)

${
	$v ph ps ch  $.
	f0_biimprcd $f wff ph $.
	f1_biimprcd $f wff ps $.
	f2_biimprcd $f wff ch $.
	e0_biimprcd $e |- ( ph -> ( ps <-> ch ) ) $.
	p_biimprcd $p |- ( ch -> ( ph -> ps ) ) $= f2_biimprcd p_id e0_biimprcd f2_biimprcd f1_biimprcd f0_biimprcd f2_biimprcd p_syl5ibrcom $.
$}

$(A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl6ib $f wff ph $.
	f1_syl6ib $f wff ps $.
	f2_syl6ib $f wff ch $.
	f3_syl6ib $f wff th $.
	e0_syl6ib $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl6ib $e |- ( ch <-> th ) $.
	p_syl6ib $p |- ( ph -> ( ps -> th ) ) $= e0_syl6ib e1_syl6ib f2_syl6ib f3_syl6ib p_biimpi f0_syl6ib f1_syl6ib f2_syl6ib f3_syl6ib p_syl6 $.
$}

$(A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl6ibr $f wff ph $.
	f1_syl6ibr $f wff ps $.
	f2_syl6ibr $f wff ch $.
	f3_syl6ibr $f wff th $.
	e0_syl6ibr $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl6ibr $e |- ( th <-> ch ) $.
	p_syl6ibr $p |- ( ph -> ( ps -> th ) ) $= e0_syl6ibr e1_syl6ibr f3_syl6ibr f2_syl6ibr p_biimpri f0_syl6ibr f1_syl6ibr f2_syl6ibr f3_syl6ibr p_syl6 $.
$}

$(A mixed syllogism inference.  (Contributed by NM, 2-Jan-1994.) $)

${
	$v ph ps ch th  $.
	f0_syl6bi $f wff ph $.
	f1_syl6bi $f wff ps $.
	f2_syl6bi $f wff ch $.
	f3_syl6bi $f wff th $.
	e0_syl6bi $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_syl6bi $e |- ( ch -> th ) $.
	p_syl6bi $p |- ( ph -> ( ps -> th ) ) $= e0_syl6bi f0_syl6bi f1_syl6bi f2_syl6bi p_biimpd e1_syl6bi f0_syl6bi f1_syl6bi f2_syl6bi f3_syl6bi p_syl6 $.
$}

$(A mixed syllogism inference.  (Contributed by NM, 18-May-1994.) $)

${
	$v ph ps ch th  $.
	f0_syl6bir $f wff ph $.
	f1_syl6bir $f wff ps $.
	f2_syl6bir $f wff ch $.
	f3_syl6bir $f wff th $.
	e0_syl6bir $e |- ( ph -> ( ch <-> ps ) ) $.
	e1_syl6bir $e |- ( ch -> th ) $.
	p_syl6bir $p |- ( ph -> ( ps -> th ) ) $= e0_syl6bir f0_syl6bir f2_syl6bir f1_syl6bir p_biimprd e1_syl6bir f0_syl6bir f1_syl6bir f2_syl6bir f3_syl6bir p_syl6 $.
$}

$(A mixed syllogism inference from a doubly nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th ta  $.
	f0_syl7bi $f wff ph $.
	f1_syl7bi $f wff ps $.
	f2_syl7bi $f wff ch $.
	f3_syl7bi $f wff th $.
	f4_syl7bi $f wff ta $.
	e0_syl7bi $e |- ( ph <-> ps ) $.
	e1_syl7bi $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
	p_syl7bi $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $= e0_syl7bi f0_syl7bi f1_syl7bi p_biimpi e1_syl7bi f0_syl7bi f1_syl7bi f2_syl7bi f3_syl7bi f4_syl7bi p_syl7 $.
$}

$(A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM,
       1-Aug-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_syl8ib $f wff ph $.
	f1_syl8ib $f wff ps $.
	f2_syl8ib $f wff ch $.
	f3_syl8ib $f wff th $.
	f4_syl8ib $f wff ta $.
	e0_syl8ib $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	e1_syl8ib $e |- ( th <-> ta ) $.
	p_syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= e0_syl8ib e1_syl8ib f3_syl8ib f4_syl8ib p_biimpi f0_syl8ib f1_syl8ib f2_syl8ib f3_syl8ib f4_syl8ib p_syl8 $.
$}

$(A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_mpbird $f wff ph $.
	f1_mpbird $f wff ps $.
	f2_mpbird $f wff ch $.
	e0_mpbird $e |- ( ph -> ch ) $.
	e1_mpbird $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mpbird $p |- ( ph -> ps ) $= e0_mpbird e1_mpbird f0_mpbird f1_mpbird f2_mpbird p_biimprd f0_mpbird f2_mpbird f1_mpbird p_mpd $.
$}

$(An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)

${
	$v ph ps ch  $.
	f0_mpbiri $f wff ph $.
	f1_mpbiri $f wff ps $.
	f2_mpbiri $f wff ch $.
	e0_mpbiri $e |- ch $.
	e1_mpbiri $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mpbiri $p |- ( ph -> ps ) $= e0_mpbiri f2_mpbiri f0_mpbiri p_a1i e1_mpbiri f0_mpbiri f1_mpbiri f2_mpbiri p_mpbird $.
$}

$(A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_sylibrd $f wff ph $.
	f1_sylibrd $f wff ps $.
	f2_sylibrd $f wff ch $.
	f3_sylibrd $f wff th $.
	e0_sylibrd $e |- ( ph -> ( ps -> ch ) ) $.
	e1_sylibrd $e |- ( ph -> ( th <-> ch ) ) $.
	p_sylibrd $p |- ( ph -> ( ps -> th ) ) $= e0_sylibrd e1_sylibrd f0_sylibrd f3_sylibrd f2_sylibrd p_biimprd f0_sylibrd f1_sylibrd f2_sylibrd f3_sylibrd p_syld $.
$}

$(A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_sylbird $f wff ph $.
	f1_sylbird $f wff ps $.
	f2_sylbird $f wff ch $.
	f3_sylbird $f wff th $.
	e0_sylbird $e |- ( ph -> ( ch <-> ps ) ) $.
	e1_sylbird $e |- ( ph -> ( ch -> th ) ) $.
	p_sylbird $p |- ( ph -> ( ps -> th ) ) $= e0_sylbird f0_sylbird f2_sylbird f1_sylbird p_biimprd e1_sylbird f0_sylbird f1_sylbird f2_sylbird f3_sylbird p_syld $.
$}

$(Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph  $.
	f0_biid $f wff ph $.
	p_biid $p |- ( ph <-> ph ) $= f0_biid p_id f0_biid p_id f0_biid f0_biid p_impbii $.
$}

$(Principle of identity with antecedent.  (Contributed by NM,
     25-Nov-1995.) $)

${
	$v ph ps  $.
	f0_biidd $f wff ph $.
	f1_biidd $f wff ps $.
	p_biidd $p |- ( ph -> ( ps <-> ps ) ) $= f1_biidd p_biid f1_biidd f1_biidd a_wb f0_biidd p_a1i $.
$}

$(Two propositions are equivalent if they are both true.  Closed form of
     ~ 2th .  Equivalent to a ~ bi1 -like version of the xor-connective.  This
     theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version
     ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .  (Contributed by Wolf Lammen,
     12-May-2013.) $)

${
	$v ph ps  $.
	f0_pm5.1im $f wff ph $.
	f1_pm5.1im $f wff ps $.
	p_pm5.1im $p |- ( ph -> ( ps -> ( ph <-> ps ) ) ) $= f1_pm5.1im f0_pm5.1im a_ax-1 f0_pm5.1im f1_pm5.1im a_ax-1 f0_pm5.1im f1_pm5.1im f0_pm5.1im f1_pm5.1im p_impbid21d $.
$}

$(Two truths are equivalent.  (Contributed by NM, 18-Aug-1993.) $)

${
	$v ph ps  $.
	f0_2th $f wff ph $.
	f1_2th $f wff ps $.
	e0_2th $e |- ph $.
	e1_2th $e |- ps $.
	p_2th $p |- ( ph <-> ps ) $= e1_2th f1_2th f0_2th p_a1i e0_2th f0_2th f1_2th p_a1i f0_2th f1_2th p_impbii $.
$}

$(Two truths are equivalent (deduction rule).  (Contributed by NM,
       3-Jun-2012.) $)

${
	$v ph ps ch  $.
	f0_2thd $f wff ph $.
	f1_2thd $f wff ps $.
	f2_2thd $f wff ch $.
	e0_2thd $e |- ( ph -> ps ) $.
	e1_2thd $e |- ( ph -> ch ) $.
	p_2thd $p |- ( ph -> ( ps <-> ch ) ) $= e0_2thd e1_2thd f1_2thd f2_2thd p_pm5.1im f0_2thd f1_2thd f2_2thd f1_2thd f2_2thd a_wb p_sylc $.
$}

$(Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 17-Oct-2003.) $)

${
	$v ph ps  $.
	f0_ibi $f wff ph $.
	f1_ibi $f wff ps $.
	e0_ibi $e |- ( ph -> ( ph <-> ps ) ) $.
	p_ibi $p |- ( ph -> ps ) $= e0_ibi f0_ibi f0_ibi f1_ibi p_biimpd f0_ibi f1_ibi p_pm2.43i $.
$}

$(Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 22-Jul-2004.) $)

${
	$v ph ps  $.
	f0_ibir $f wff ph $.
	f1_ibir $f wff ps $.
	e0_ibir $e |- ( ph -> ( ps <-> ph ) ) $.
	p_ibir $p |- ( ph -> ps ) $= e0_ibir f0_ibir f1_ibir f0_ibir p_bicomd f0_ibir f1_ibir p_ibi $.
$}

$(Deduction that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 26-Jun-2004.) $)

${
	$v ph ps ch  $.
	f0_ibd $f wff ph $.
	f1_ibd $f wff ps $.
	f2_ibd $f wff ch $.
	e0_ibd $e |- ( ph -> ( ps -> ( ps <-> ch ) ) ) $.
	p_ibd $p |- ( ph -> ( ps -> ch ) ) $= e0_ibd f1_ibd f2_ibd p_bi1 f1_ibd f0_ibd f1_ibd f2_ibd a_wb f2_ibd p_syli $.
$}

$(Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126.  (Contributed by NM, 1-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 11-Apr-2013.) $)

${
	$v ph ps ch  $.
	f0_pm5.74 $f wff ph $.
	f1_pm5.74 $f wff ps $.
	f2_pm5.74 $f wff ch $.
	p_pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $= f1_pm5.74 f2_pm5.74 p_bi1 f1_pm5.74 f2_pm5.74 a_wb f1_pm5.74 f2_pm5.74 f0_pm5.74 p_imim3i f1_pm5.74 f2_pm5.74 p_bi2 f1_pm5.74 f2_pm5.74 a_wb f2_pm5.74 f1_pm5.74 f0_pm5.74 p_imim3i f0_pm5.74 f1_pm5.74 f2_pm5.74 a_wb a_wi f0_pm5.74 f1_pm5.74 a_wi f0_pm5.74 f2_pm5.74 a_wi p_impbid f0_pm5.74 f1_pm5.74 a_wi f0_pm5.74 f2_pm5.74 a_wi p_bi1 f0_pm5.74 f1_pm5.74 a_wi f0_pm5.74 f2_pm5.74 a_wi a_wb f0_pm5.74 f1_pm5.74 f2_pm5.74 p_pm2.86d f0_pm5.74 f1_pm5.74 a_wi f0_pm5.74 f2_pm5.74 a_wi p_bi2 f0_pm5.74 f1_pm5.74 a_wi f0_pm5.74 f2_pm5.74 a_wi a_wb f0_pm5.74 f2_pm5.74 f1_pm5.74 p_pm2.86d f0_pm5.74 f1_pm5.74 a_wi f0_pm5.74 f2_pm5.74 a_wi a_wb f0_pm5.74 f1_pm5.74 f2_pm5.74 p_impbidd f0_pm5.74 f1_pm5.74 f2_pm5.74 a_wb a_wi f0_pm5.74 f1_pm5.74 a_wi f0_pm5.74 f2_pm5.74 a_wi a_wb p_impbii $.
$}

$(Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 1-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_pm5.74i $f wff ph $.
	f1_pm5.74i $f wff ps $.
	f2_pm5.74i $f wff ch $.
	e0_pm5.74i $e |- ( ph -> ( ps <-> ch ) ) $.
	p_pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $= e0_pm5.74i f0_pm5.74i f1_pm5.74i f2_pm5.74i p_pm5.74 f0_pm5.74i f1_pm5.74i f2_pm5.74i a_wb a_wi f0_pm5.74i f1_pm5.74i a_wi f0_pm5.74i f2_pm5.74i a_wi a_wb p_mpbi $.
$}

$(Distribution of implication over biconditional (reverse inference
       rule).  (Contributed by NM, 1-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_pm5.74ri $f wff ph $.
	f1_pm5.74ri $f wff ps $.
	f2_pm5.74ri $f wff ch $.
	e0_pm5.74ri $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
	p_pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $= e0_pm5.74ri f0_pm5.74ri f1_pm5.74ri f2_pm5.74ri p_pm5.74 f0_pm5.74ri f1_pm5.74ri f2_pm5.74ri a_wb a_wi f0_pm5.74ri f1_pm5.74ri a_wi f0_pm5.74ri f2_pm5.74ri a_wi a_wb p_mpbir $.
$}

$(Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 21-Mar-1996.) $)

${
	$v ph ps ch th  $.
	f0_pm5.74d $f wff ph $.
	f1_pm5.74d $f wff ps $.
	f2_pm5.74d $f wff ch $.
	f3_pm5.74d $f wff th $.
	e0_pm5.74d $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
	p_pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $= e0_pm5.74d f1_pm5.74d f2_pm5.74d f3_pm5.74d p_pm5.74 f0_pm5.74d f1_pm5.74d f2_pm5.74d f3_pm5.74d a_wb a_wi f1_pm5.74d f2_pm5.74d a_wi f1_pm5.74d f3_pm5.74d a_wi a_wb p_sylib $.
$}

$(Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 19-Mar-1997.) $)

${
	$v ph ps ch th  $.
	f0_pm5.74rd $f wff ph $.
	f1_pm5.74rd $f wff ps $.
	f2_pm5.74rd $f wff ch $.
	f3_pm5.74rd $f wff th $.
	e0_pm5.74rd $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
	p_pm5.74rd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $= e0_pm5.74rd f1_pm5.74rd f2_pm5.74rd f3_pm5.74rd p_pm5.74 f0_pm5.74rd f1_pm5.74rd f2_pm5.74rd a_wi f1_pm5.74rd f3_pm5.74rd a_wi a_wb f1_pm5.74rd f2_pm5.74rd f3_pm5.74rd a_wb a_wi p_sylibr $.
$}

$(An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Oct-2012.) $)

${
	$v ph ps ch  $.
	f0_bitri $f wff ph $.
	f1_bitri $f wff ps $.
	f2_bitri $f wff ch $.
	e0_bitri $e |- ( ph <-> ps ) $.
	e1_bitri $e |- ( ps <-> ch ) $.
	p_bitri $p |- ( ph <-> ch ) $= e0_bitri f0_bitri f1_bitri p_biimpi e1_bitri f0_bitri f1_bitri f2_bitri p_sylib e1_bitri f1_bitri f2_bitri p_biimpri e0_bitri f2_bitri f1_bitri f0_bitri p_sylibr f0_bitri f2_bitri p_impbii $.
$}

$(An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_bitr2i $f wff ph $.
	f1_bitr2i $f wff ps $.
	f2_bitr2i $f wff ch $.
	e0_bitr2i $e |- ( ph <-> ps ) $.
	e1_bitr2i $e |- ( ps <-> ch ) $.
	p_bitr2i $p |- ( ch <-> ph ) $= e0_bitr2i e1_bitr2i f0_bitr2i f1_bitr2i f2_bitr2i p_bitri f0_bitr2i f2_bitr2i p_bicomi $.
$}

$(An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_bitr3i $f wff ph $.
	f1_bitr3i $f wff ps $.
	f2_bitr3i $f wff ch $.
	e0_bitr3i $e |- ( ps <-> ph ) $.
	e1_bitr3i $e |- ( ps <-> ch ) $.
	p_bitr3i $p |- ( ph <-> ch ) $= e0_bitr3i f1_bitr3i f0_bitr3i p_bicomi e1_bitr3i f0_bitr3i f1_bitr3i f2_bitr3i p_bitri $.
$}

$(An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_bitr4i $f wff ph $.
	f1_bitr4i $f wff ps $.
	f2_bitr4i $f wff ch $.
	e0_bitr4i $e |- ( ph <-> ps ) $.
	e1_bitr4i $e |- ( ch <-> ps ) $.
	p_bitr4i $p |- ( ph <-> ch ) $= e0_bitr4i e1_bitr4i f2_bitr4i f1_bitr4i p_bicomi f0_bitr4i f1_bitr4i f2_bitr4i p_bitri $.
$}

$(Register '<->' as an equality for its type (wff). $)

$($j
    equality 'wb' from 'biid' 'bicomi' 'bitri';
    definition 'dfbi1' for 'wb';
  $)

$(Deduction form of ~ bitri .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 14-Apr-2013.) $)

${
	$v ph ps ch th  $.
	f0_bitrd $f wff ph $.
	f1_bitrd $f wff ps $.
	f2_bitrd $f wff ch $.
	f3_bitrd $f wff th $.
	e0_bitrd $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_bitrd $e |- ( ph -> ( ch <-> th ) ) $.
	p_bitrd $p |- ( ph -> ( ps <-> th ) ) $= e0_bitrd f0_bitrd f1_bitrd f2_bitrd p_pm5.74i e1_bitrd f0_bitrd f2_bitrd f3_bitrd p_pm5.74i f0_bitrd f1_bitrd a_wi f0_bitrd f2_bitrd a_wi f0_bitrd f3_bitrd a_wi p_bitri f0_bitrd f1_bitrd f3_bitrd p_pm5.74ri $.
$}

$(Deduction form of ~ bitr2i .  (Contributed by NM, 9-Jun-2004.) $)

${
	$v ph ps ch th  $.
	f0_bitr2d $f wff ph $.
	f1_bitr2d $f wff ps $.
	f2_bitr2d $f wff ch $.
	f3_bitr2d $f wff th $.
	e0_bitr2d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_bitr2d $e |- ( ph -> ( ch <-> th ) ) $.
	p_bitr2d $p |- ( ph -> ( th <-> ps ) ) $= e0_bitr2d e1_bitr2d f0_bitr2d f1_bitr2d f2_bitr2d f3_bitr2d p_bitrd f0_bitr2d f1_bitr2d f3_bitr2d p_bicomd $.
$}

$(Deduction form of ~ bitr3i .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_bitr3d $f wff ph $.
	f1_bitr3d $f wff ps $.
	f2_bitr3d $f wff ch $.
	f3_bitr3d $f wff th $.
	e0_bitr3d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_bitr3d $e |- ( ph -> ( ps <-> th ) ) $.
	p_bitr3d $p |- ( ph -> ( ch <-> th ) ) $= e0_bitr3d f0_bitr3d f1_bitr3d f2_bitr3d p_bicomd e1_bitr3d f0_bitr3d f2_bitr3d f1_bitr3d f3_bitr3d p_bitrd $.
$}

$(Deduction form of ~ bitr4i .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_bitr4d $f wff ph $.
	f1_bitr4d $f wff ps $.
	f2_bitr4d $f wff ch $.
	f3_bitr4d $f wff th $.
	e0_bitr4d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_bitr4d $e |- ( ph -> ( th <-> ch ) ) $.
	p_bitr4d $p |- ( ph -> ( ps <-> th ) ) $= e0_bitr4d e1_bitr4d f0_bitr4d f3_bitr4d f2_bitr4d p_bicomd f0_bitr4d f1_bitr4d f2_bitr4d f3_bitr4d p_bitrd $.
$}

$(A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl5bb $f wff ph $.
	f1_syl5bb $f wff ps $.
	f2_syl5bb $f wff ch $.
	f3_syl5bb $f wff th $.
	e0_syl5bb $e |- ( ph <-> ps ) $.
	e1_syl5bb $e |- ( ch -> ( ps <-> th ) ) $.
	p_syl5bb $p |- ( ch -> ( ph <-> th ) ) $= e0_syl5bb f0_syl5bb f1_syl5bb a_wb f2_syl5bb p_a1i e1_syl5bb f2_syl5bb f0_syl5bb f1_syl5bb f3_syl5bb p_bitrd $.
$}

$(A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl5rbb $f wff ph $.
	f1_syl5rbb $f wff ps $.
	f2_syl5rbb $f wff ch $.
	f3_syl5rbb $f wff th $.
	e0_syl5rbb $e |- ( ph <-> ps ) $.
	e1_syl5rbb $e |- ( ch -> ( ps <-> th ) ) $.
	p_syl5rbb $p |- ( ch -> ( th <-> ph ) ) $= e0_syl5rbb e1_syl5rbb f0_syl5rbb f1_syl5rbb f2_syl5rbb f3_syl5rbb p_syl5bb f2_syl5rbb f0_syl5rbb f3_syl5rbb p_bicomd $.
$}

$(A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl5bbr $f wff ph $.
	f1_syl5bbr $f wff ps $.
	f2_syl5bbr $f wff ch $.
	f3_syl5bbr $f wff th $.
	e0_syl5bbr $e |- ( ps <-> ph ) $.
	e1_syl5bbr $e |- ( ch -> ( ps <-> th ) ) $.
	p_syl5bbr $p |- ( ch -> ( ph <-> th ) ) $= e0_syl5bbr f1_syl5bbr f0_syl5bbr p_bicomi e1_syl5bbr f0_syl5bbr f1_syl5bbr f2_syl5bbr f3_syl5bbr p_syl5bb $.
$}

$(A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)

${
	$v ph ps ch th  $.
	f0_syl5rbbr $f wff ph $.
	f1_syl5rbbr $f wff ps $.
	f2_syl5rbbr $f wff ch $.
	f3_syl5rbbr $f wff th $.
	e0_syl5rbbr $e |- ( ps <-> ph ) $.
	e1_syl5rbbr $e |- ( ch -> ( ps <-> th ) ) $.
	p_syl5rbbr $p |- ( ch -> ( th <-> ph ) ) $= e0_syl5rbbr f1_syl5rbbr f0_syl5rbbr p_bicomi e1_syl5rbbr f0_syl5rbbr f1_syl5rbbr f2_syl5rbbr f3_syl5rbbr p_syl5rbb $.
$}

$(A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl6bb $f wff ph $.
	f1_syl6bb $f wff ps $.
	f2_syl6bb $f wff ch $.
	f3_syl6bb $f wff th $.
	e0_syl6bb $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_syl6bb $e |- ( ch <-> th ) $.
	p_syl6bb $p |- ( ph -> ( ps <-> th ) ) $= e0_syl6bb e1_syl6bb f2_syl6bb f3_syl6bb a_wb f0_syl6bb p_a1i f0_syl6bb f1_syl6bb f2_syl6bb f3_syl6bb p_bitrd $.
$}

$(A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl6rbb $f wff ph $.
	f1_syl6rbb $f wff ps $.
	f2_syl6rbb $f wff ch $.
	f3_syl6rbb $f wff th $.
	e0_syl6rbb $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_syl6rbb $e |- ( ch <-> th ) $.
	p_syl6rbb $p |- ( ph -> ( th <-> ps ) ) $= e0_syl6rbb e1_syl6rbb f0_syl6rbb f1_syl6rbb f2_syl6rbb f3_syl6rbb p_syl6bb f0_syl6rbb f1_syl6rbb f3_syl6rbb p_bicomd $.
$}

$(A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_syl6bbr $f wff ph $.
	f1_syl6bbr $f wff ps $.
	f2_syl6bbr $f wff ch $.
	f3_syl6bbr $f wff th $.
	e0_syl6bbr $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_syl6bbr $e |- ( th <-> ch ) $.
	p_syl6bbr $p |- ( ph -> ( ps <-> th ) ) $= e0_syl6bbr e1_syl6bbr f3_syl6bbr f2_syl6bbr p_bicomi f0_syl6bbr f1_syl6bbr f2_syl6bbr f3_syl6bbr p_syl6bb $.
$}

$(A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)

${
	$v ph ps ch th  $.
	f0_syl6rbbr $f wff ph $.
	f1_syl6rbbr $f wff ps $.
	f2_syl6rbbr $f wff ch $.
	f3_syl6rbbr $f wff th $.
	e0_syl6rbbr $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_syl6rbbr $e |- ( th <-> ch ) $.
	p_syl6rbbr $p |- ( ph -> ( th <-> ps ) ) $= e0_syl6rbbr e1_syl6rbbr f3_syl6rbbr f2_syl6rbbr p_bicomi f0_syl6rbbr f1_syl6rbbr f2_syl6rbbr f3_syl6rbbr p_syl6rbb $.
$}

$(A mixed syllogism inference, useful for removing a definition from both
       sides of an implication.  (Contributed by NM, 10-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_3imtr3i $f wff ph $.
	f1_3imtr3i $f wff ps $.
	f2_3imtr3i $f wff ch $.
	f3_3imtr3i $f wff th $.
	e0_3imtr3i $e |- ( ph -> ps ) $.
	e1_3imtr3i $e |- ( ph <-> ch ) $.
	e2_3imtr3i $e |- ( ps <-> th ) $.
	p_3imtr3i $p |- ( ch -> th ) $= e1_3imtr3i e0_3imtr3i f2_3imtr3i f0_3imtr3i f1_3imtr3i p_sylbir e2_3imtr3i f2_3imtr3i f1_3imtr3i f3_3imtr3i p_sylib $.
$}

$(A mixed syllogism inference, useful for applying a definition to both
       sides of an implication.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_3imtr4i $f wff ph $.
	f1_3imtr4i $f wff ps $.
	f2_3imtr4i $f wff ch $.
	f3_3imtr4i $f wff th $.
	e0_3imtr4i $e |- ( ph -> ps ) $.
	e1_3imtr4i $e |- ( ch <-> ph ) $.
	e2_3imtr4i $e |- ( th <-> ps ) $.
	p_3imtr4i $p |- ( ch -> th ) $= e1_3imtr4i e0_3imtr4i f2_3imtr4i f0_3imtr4i f1_3imtr4i p_sylbi e2_3imtr4i f2_3imtr4i f1_3imtr4i f3_3imtr4i p_sylibr $.
$}

$(More general version of ~ 3imtr3i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 8-Apr-1996.) $)

${
	$v ph ps ch th ta  $.
	f0_3imtr3d $f wff ph $.
	f1_3imtr3d $f wff ps $.
	f2_3imtr3d $f wff ch $.
	f3_3imtr3d $f wff th $.
	f4_3imtr3d $f wff ta $.
	e0_3imtr3d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3imtr3d $e |- ( ph -> ( ps <-> th ) ) $.
	e2_3imtr3d $e |- ( ph -> ( ch <-> ta ) ) $.
	p_3imtr3d $p |- ( ph -> ( th -> ta ) ) $= e1_3imtr3d e0_3imtr3d e2_3imtr3d f0_3imtr3d f1_3imtr3d f2_3imtr3d f4_3imtr3d p_sylibd f0_3imtr3d f3_3imtr3d f1_3imtr3d f4_3imtr3d p_sylbird $.
$}

$(More general version of ~ 3imtr4i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 26-Oct-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_3imtr4d $f wff ph $.
	f1_3imtr4d $f wff ps $.
	f2_3imtr4d $f wff ch $.
	f3_3imtr4d $f wff th $.
	f4_3imtr4d $f wff ta $.
	e0_3imtr4d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3imtr4d $e |- ( ph -> ( th <-> ps ) ) $.
	e2_3imtr4d $e |- ( ph -> ( ta <-> ch ) ) $.
	p_3imtr4d $p |- ( ph -> ( th -> ta ) ) $= e1_3imtr4d e0_3imtr4d e2_3imtr4d f0_3imtr4d f1_3imtr4d f2_3imtr4d f4_3imtr4d p_sylibrd f0_3imtr4d f3_3imtr4d f1_3imtr4d f4_3imtr4d p_sylbid $.
$}

$(More general version of ~ 3imtr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_3imtr3g $f wff ph $.
	f1_3imtr3g $f wff ps $.
	f2_3imtr3g $f wff ch $.
	f3_3imtr3g $f wff th $.
	f4_3imtr3g $f wff ta $.
	e0_3imtr3g $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3imtr3g $e |- ( ps <-> th ) $.
	e2_3imtr3g $e |- ( ch <-> ta ) $.
	p_3imtr3g $p |- ( ph -> ( th -> ta ) ) $= e1_3imtr3g e0_3imtr3g f3_3imtr3g f1_3imtr3g f0_3imtr3g f2_3imtr3g p_syl5bir e2_3imtr3g f0_3imtr3g f3_3imtr3g f2_3imtr3g f4_3imtr3g p_syl6ib $.
$}

$(More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_3imtr4g $f wff ph $.
	f1_3imtr4g $f wff ps $.
	f2_3imtr4g $f wff ch $.
	f3_3imtr4g $f wff th $.
	f4_3imtr4g $f wff ta $.
	e0_3imtr4g $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3imtr4g $e |- ( th <-> ps ) $.
	e2_3imtr4g $e |- ( ta <-> ch ) $.
	p_3imtr4g $p |- ( ph -> ( th -> ta ) ) $= e1_3imtr4g e0_3imtr4g f3_3imtr4g f1_3imtr4g f0_3imtr4g f2_3imtr4g p_syl5bi e2_3imtr4g f0_3imtr4g f3_3imtr4g f2_3imtr4g f4_3imtr4g p_syl6ibr $.
$}

$(A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_3bitri $f wff ph $.
	f1_3bitri $f wff ps $.
	f2_3bitri $f wff ch $.
	f3_3bitri $f wff th $.
	e0_3bitri $e |- ( ph <-> ps ) $.
	e1_3bitri $e |- ( ps <-> ch ) $.
	e2_3bitri $e |- ( ch <-> th ) $.
	p_3bitri $p |- ( ph <-> th ) $= e0_3bitri e1_3bitri e2_3bitri f1_3bitri f2_3bitri f3_3bitri p_bitri f0_3bitri f1_3bitri f3_3bitri p_bitri $.
$}

$(A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)

${
	$v ph ps ch th  $.
	f0_3bitrri $f wff ph $.
	f1_3bitrri $f wff ps $.
	f2_3bitrri $f wff ch $.
	f3_3bitrri $f wff th $.
	e0_3bitrri $e |- ( ph <-> ps ) $.
	e1_3bitrri $e |- ( ps <-> ch ) $.
	e2_3bitrri $e |- ( ch <-> th ) $.
	p_3bitrri $p |- ( th <-> ph ) $= e2_3bitrri e0_3bitrri e1_3bitrri f0_3bitrri f1_3bitrri f2_3bitrri p_bitr2i f3_3bitrri f2_3bitrri f0_3bitrri p_bitr3i $.
$}

$(A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)

${
	$v ph ps ch th  $.
	f0_3bitr2i $f wff ph $.
	f1_3bitr2i $f wff ps $.
	f2_3bitr2i $f wff ch $.
	f3_3bitr2i $f wff th $.
	e0_3bitr2i $e |- ( ph <-> ps ) $.
	e1_3bitr2i $e |- ( ch <-> ps ) $.
	e2_3bitr2i $e |- ( ch <-> th ) $.
	p_3bitr2i $p |- ( ph <-> th ) $= e0_3bitr2i e1_3bitr2i f0_3bitr2i f1_3bitr2i f2_3bitr2i p_bitr4i e2_3bitr2i f0_3bitr2i f2_3bitr2i f3_3bitr2i p_bitri $.
$}

$(A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)

${
	$v ph ps ch th  $.
	f0_3bitr2ri $f wff ph $.
	f1_3bitr2ri $f wff ps $.
	f2_3bitr2ri $f wff ch $.
	f3_3bitr2ri $f wff th $.
	e0_3bitr2ri $e |- ( ph <-> ps ) $.
	e1_3bitr2ri $e |- ( ch <-> ps ) $.
	e2_3bitr2ri $e |- ( ch <-> th ) $.
	p_3bitr2ri $p |- ( th <-> ph ) $= e0_3bitr2ri e1_3bitr2ri f0_3bitr2ri f1_3bitr2ri f2_3bitr2ri p_bitr4i e2_3bitr2ri f0_3bitr2ri f2_3bitr2ri f3_3bitr2ri p_bitr2i $.
$}

$(A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 19-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_3bitr3i $f wff ph $.
	f1_3bitr3i $f wff ps $.
	f2_3bitr3i $f wff ch $.
	f3_3bitr3i $f wff th $.
	e0_3bitr3i $e |- ( ph <-> ps ) $.
	e1_3bitr3i $e |- ( ph <-> ch ) $.
	e2_3bitr3i $e |- ( ps <-> th ) $.
	p_3bitr3i $p |- ( ch <-> th ) $= e1_3bitr3i e0_3bitr3i f2_3bitr3i f0_3bitr3i f1_3bitr3i p_bitr3i e2_3bitr3i f2_3bitr3i f1_3bitr3i f3_3bitr3i p_bitri $.
$}

$(A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_3bitr3ri $f wff ph $.
	f1_3bitr3ri $f wff ps $.
	f2_3bitr3ri $f wff ch $.
	f3_3bitr3ri $f wff th $.
	e0_3bitr3ri $e |- ( ph <-> ps ) $.
	e1_3bitr3ri $e |- ( ph <-> ch ) $.
	e2_3bitr3ri $e |- ( ps <-> th ) $.
	p_3bitr3ri $p |- ( th <-> ch ) $= e2_3bitr3ri e0_3bitr3ri e1_3bitr3ri f1_3bitr3ri f0_3bitr3ri f2_3bitr3ri p_bitr3i f3_3bitr3ri f1_3bitr3ri f2_3bitr3ri p_bitr3i $.
$}

$(A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_3bitr4i $f wff ph $.
	f1_3bitr4i $f wff ps $.
	f2_3bitr4i $f wff ch $.
	f3_3bitr4i $f wff th $.
	e0_3bitr4i $e |- ( ph <-> ps ) $.
	e1_3bitr4i $e |- ( ch <-> ph ) $.
	e2_3bitr4i $e |- ( th <-> ps ) $.
	p_3bitr4i $p |- ( ch <-> th ) $= e1_3bitr4i e0_3bitr4i e2_3bitr4i f0_3bitr4i f1_3bitr4i f3_3bitr4i p_bitr4i f2_3bitr4i f0_3bitr4i f3_3bitr4i p_bitri $.
$}

$(A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 2-Sep-1995.) $)

${
	$v ph ps ch th  $.
	f0_3bitr4ri $f wff ph $.
	f1_3bitr4ri $f wff ps $.
	f2_3bitr4ri $f wff ch $.
	f3_3bitr4ri $f wff th $.
	e0_3bitr4ri $e |- ( ph <-> ps ) $.
	e1_3bitr4ri $e |- ( ch <-> ph ) $.
	e2_3bitr4ri $e |- ( th <-> ps ) $.
	p_3bitr4ri $p |- ( th <-> ch ) $= e1_3bitr4ri e0_3bitr4ri e2_3bitr4ri f0_3bitr4ri f1_3bitr4ri f3_3bitr4ri p_bitr4i f2_3bitr4ri f0_3bitr4ri f3_3bitr4ri p_bitr2i $.
$}

$(Deduction from transitivity of biconditional.  (Contributed by NM,
       13-Aug-1999.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitrd $f wff ph $.
	f1_3bitrd $f wff ps $.
	f2_3bitrd $f wff ch $.
	f3_3bitrd $f wff th $.
	f4_3bitrd $f wff ta $.
	e0_3bitrd $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitrd $e |- ( ph -> ( ch <-> th ) ) $.
	e2_3bitrd $e |- ( ph -> ( th <-> ta ) ) $.
	p_3bitrd $p |- ( ph -> ( ps <-> ta ) ) $= e0_3bitrd e1_3bitrd f0_3bitrd f1_3bitrd f2_3bitrd f3_3bitrd p_bitrd e2_3bitrd f0_3bitrd f1_3bitrd f3_3bitrd f4_3bitrd p_bitrd $.
$}

$(Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitrrd $f wff ph $.
	f1_3bitrrd $f wff ps $.
	f2_3bitrrd $f wff ch $.
	f3_3bitrrd $f wff th $.
	f4_3bitrrd $f wff ta $.
	e0_3bitrrd $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitrrd $e |- ( ph -> ( ch <-> th ) ) $.
	e2_3bitrrd $e |- ( ph -> ( th <-> ta ) ) $.
	p_3bitrrd $p |- ( ph -> ( ta <-> ps ) ) $= e2_3bitrrd e0_3bitrrd e1_3bitrrd f0_3bitrrd f1_3bitrrd f2_3bitrrd f3_3bitrrd p_bitr2d f0_3bitrrd f3_3bitrrd f4_3bitrrd f1_3bitrrd p_bitr3d $.
$}

$(Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitr2d $f wff ph $.
	f1_3bitr2d $f wff ps $.
	f2_3bitr2d $f wff ch $.
	f3_3bitr2d $f wff th $.
	f4_3bitr2d $f wff ta $.
	e0_3bitr2d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitr2d $e |- ( ph -> ( th <-> ch ) ) $.
	e2_3bitr2d $e |- ( ph -> ( th <-> ta ) ) $.
	p_3bitr2d $p |- ( ph -> ( ps <-> ta ) ) $= e0_3bitr2d e1_3bitr2d f0_3bitr2d f1_3bitr2d f2_3bitr2d f3_3bitr2d p_bitr4d e2_3bitr2d f0_3bitr2d f1_3bitr2d f3_3bitr2d f4_3bitr2d p_bitrd $.
$}

$(Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitr2rd $f wff ph $.
	f1_3bitr2rd $f wff ps $.
	f2_3bitr2rd $f wff ch $.
	f3_3bitr2rd $f wff th $.
	f4_3bitr2rd $f wff ta $.
	e0_3bitr2rd $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitr2rd $e |- ( ph -> ( th <-> ch ) ) $.
	e2_3bitr2rd $e |- ( ph -> ( th <-> ta ) ) $.
	p_3bitr2rd $p |- ( ph -> ( ta <-> ps ) ) $= e0_3bitr2rd e1_3bitr2rd f0_3bitr2rd f1_3bitr2rd f2_3bitr2rd f3_3bitr2rd p_bitr4d e2_3bitr2rd f0_3bitr2rd f1_3bitr2rd f3_3bitr2rd f4_3bitr2rd p_bitr2d $.
$}

$(Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       24-Apr-1996.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitr3d $f wff ph $.
	f1_3bitr3d $f wff ps $.
	f2_3bitr3d $f wff ch $.
	f3_3bitr3d $f wff th $.
	f4_3bitr3d $f wff ta $.
	e0_3bitr3d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitr3d $e |- ( ph -> ( ps <-> th ) ) $.
	e2_3bitr3d $e |- ( ph -> ( ch <-> ta ) ) $.
	p_3bitr3d $p |- ( ph -> ( th <-> ta ) ) $= e1_3bitr3d e0_3bitr3d f0_3bitr3d f1_3bitr3d f3_3bitr3d f2_3bitr3d p_bitr3d e2_3bitr3d f0_3bitr3d f3_3bitr3d f2_3bitr3d f4_3bitr3d p_bitrd $.
$}

$(Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitr3rd $f wff ph $.
	f1_3bitr3rd $f wff ps $.
	f2_3bitr3rd $f wff ch $.
	f3_3bitr3rd $f wff th $.
	f4_3bitr3rd $f wff ta $.
	e0_3bitr3rd $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitr3rd $e |- ( ph -> ( ps <-> th ) ) $.
	e2_3bitr3rd $e |- ( ph -> ( ch <-> ta ) ) $.
	p_3bitr3rd $p |- ( ph -> ( ta <-> th ) ) $= e2_3bitr3rd e0_3bitr3rd e1_3bitr3rd f0_3bitr3rd f1_3bitr3rd f2_3bitr3rd f3_3bitr3rd p_bitr3d f0_3bitr3rd f2_3bitr3rd f4_3bitr3rd f3_3bitr3rd p_bitr3d $.
$}

$(Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       18-Oct-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitr4d $f wff ph $.
	f1_3bitr4d $f wff ps $.
	f2_3bitr4d $f wff ch $.
	f3_3bitr4d $f wff th $.
	f4_3bitr4d $f wff ta $.
	e0_3bitr4d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitr4d $e |- ( ph -> ( th <-> ps ) ) $.
	e2_3bitr4d $e |- ( ph -> ( ta <-> ch ) ) $.
	p_3bitr4d $p |- ( ph -> ( th <-> ta ) ) $= e1_3bitr4d e0_3bitr4d e2_3bitr4d f0_3bitr4d f1_3bitr4d f2_3bitr4d f4_3bitr4d p_bitr4d f0_3bitr4d f3_3bitr4d f1_3bitr4d f4_3bitr4d p_bitrd $.
$}

$(Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitr4rd $f wff ph $.
	f1_3bitr4rd $f wff ps $.
	f2_3bitr4rd $f wff ch $.
	f3_3bitr4rd $f wff th $.
	f4_3bitr4rd $f wff ta $.
	e0_3bitr4rd $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitr4rd $e |- ( ph -> ( th <-> ps ) ) $.
	e2_3bitr4rd $e |- ( ph -> ( ta <-> ch ) ) $.
	p_3bitr4rd $p |- ( ph -> ( ta <-> th ) ) $= e2_3bitr4rd e0_3bitr4rd f0_3bitr4rd f4_3bitr4rd f2_3bitr4rd f1_3bitr4rd p_bitr4d e1_3bitr4rd f0_3bitr4rd f4_3bitr4rd f1_3bitr4rd f3_3bitr4rd p_bitr4d $.
$}

$(More general version of ~ 3bitr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 4-Jun-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitr3g $f wff ph $.
	f1_3bitr3g $f wff ps $.
	f2_3bitr3g $f wff ch $.
	f3_3bitr3g $f wff th $.
	f4_3bitr3g $f wff ta $.
	e0_3bitr3g $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitr3g $e |- ( ps <-> th ) $.
	e2_3bitr3g $e |- ( ch <-> ta ) $.
	p_3bitr3g $p |- ( ph -> ( th <-> ta ) ) $= e1_3bitr3g e0_3bitr3g f3_3bitr3g f1_3bitr3g f0_3bitr3g f2_3bitr3g p_syl5bbr e2_3bitr3g f0_3bitr3g f3_3bitr3g f2_3bitr3g f4_3bitr3g p_syl6bb $.
$}

$(More general version of ~ 3bitr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th ta  $.
	f0_3bitr4g $f wff ph $.
	f1_3bitr4g $f wff ps $.
	f2_3bitr4g $f wff ch $.
	f3_3bitr4g $f wff th $.
	f4_3bitr4g $f wff ta $.
	e0_3bitr4g $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_3bitr4g $e |- ( th <-> ps ) $.
	e2_3bitr4g $e |- ( ta <-> ch ) $.
	p_3bitr4g $p |- ( ph -> ( th <-> ta ) ) $= e1_3bitr4g e0_3bitr4g f3_3bitr4g f1_3bitr4g f0_3bitr4g f2_3bitr4g p_syl5bb e2_3bitr4g f0_3bitr4g f3_3bitr4g f2_3bitr4g f4_3bitr4g p_syl6bbr $.
$}

$(Construct a bi-conditional in antecedent position.  (Contributed by Wolf
       Lammen, 14-May-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_bi3ant $f wff ph $.
	f1_bi3ant $f wff ps $.
	f2_bi3ant $f wff ch $.
	f3_bi3ant $f wff th $.
	f4_bi3ant $f wff ta $.
	e0_bi3ant $e |- ( ph -> ( ps -> ch ) ) $.
	p_bi3ant $p |- ( ( ( th -> ta ) -> ph ) -> ( ( ( ta -> th ) -> ps ) -> ( ( th <-> ta ) -> ch ) ) ) $= f3_bi3ant f4_bi3ant p_bi1 f3_bi3ant f4_bi3ant a_wb f3_bi3ant f4_bi3ant a_wi f0_bi3ant p_imim1i f3_bi3ant f4_bi3ant p_bi2 f3_bi3ant f4_bi3ant a_wb f4_bi3ant f3_bi3ant a_wi f1_bi3ant p_imim1i e0_bi3ant f0_bi3ant f1_bi3ant f2_bi3ant f3_bi3ant f4_bi3ant a_wb p_imim3i f3_bi3ant f4_bi3ant a_wi f0_bi3ant a_wi f3_bi3ant f4_bi3ant a_wb f0_bi3ant a_wi f4_bi3ant f3_bi3ant a_wi f1_bi3ant a_wi f3_bi3ant f4_bi3ant a_wb f1_bi3ant a_wi f3_bi3ant f4_bi3ant a_wb f2_bi3ant a_wi p_syl2im $.
$}

$(Express symmetries of theorems in terms of biconditionals.  (Contributed
     by Wolf Lammen, 14-May-2013.) $)

${
	$v ph ps ch th  $.
	f0_bisym $f wff ph $.
	f1_bisym $f wff ps $.
	f2_bisym $f wff ch $.
	f3_bisym $f wff th $.
	p_bisym $p |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph ) -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) ) $= f2_bisym f3_bisym p_bi3 f2_bisym f3_bisym a_wi f3_bisym f2_bisym a_wi f2_bisym f3_bisym a_wb f0_bisym f1_bisym p_bi3ant $.
$}

$(Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph  $.
	f0_notnot $f wff ph $.
	p_notnot $p |- ( ph <-> -. -. ph ) $= f0_notnot p_notnot1 f0_notnot p_notnot2 f0_notnot f0_notnot a_wn a_wn p_impbii $.
$}

$(Contraposition.  Theorem *4.1 of [WhiteheadRussell] p. 116.  (Contributed
     by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_con34b $f wff ph $.
	f1_con34b $f wff ps $.
	p_con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $= f0_con34b f1_con34b p_con3 f1_con34b f0_con34b a_ax-3 f0_con34b f1_con34b a_wi f1_con34b a_wn f0_con34b a_wn a_wi p_impbii $.
$}

$(A contraposition deduction.  (Contributed by NM, 21-May-1994.) $)

${
	$v ph ps ch  $.
	f0_con4bid $f wff ph $.
	f1_con4bid $f wff ps $.
	f2_con4bid $f wff ch $.
	e0_con4bid $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
	p_con4bid $p |- ( ph -> ( ps <-> ch ) ) $= e0_con4bid f0_con4bid f1_con4bid a_wn f2_con4bid a_wn p_biimprd f0_con4bid f2_con4bid f1_con4bid p_con4d e0_con4bid f0_con4bid f1_con4bid a_wn f2_con4bid a_wn p_biimpd f0_con4bid f1_con4bid f2_con4bid p_impcon4bid $.
$}

$(Deduction negating both sides of a logical equivalence.  (Contributed by
       NM, 21-May-1994.) $)

${
	$v ph ps ch  $.
	f0_notbid $f wff ph $.
	f1_notbid $f wff ps $.
	f2_notbid $f wff ch $.
	e0_notbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $= e0_notbid f1_notbid p_notnot f2_notbid p_notnot f0_notbid f1_notbid f2_notbid f1_notbid a_wn a_wn f2_notbid a_wn a_wn p_3bitr3g f0_notbid f1_notbid a_wn f2_notbid a_wn p_con4bid $.
$}

$(Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 21-May-1994.)  (Proof shortened by Wolf Lammen, 12-Jun-2013.) $)

${
	$v ph ps  $.
	f0_notbi $f wff ph $.
	f1_notbi $f wff ps $.
	p_notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $= f0_notbi f1_notbi a_wb p_id f0_notbi f1_notbi a_wb f0_notbi f1_notbi p_notbid f0_notbi a_wn f1_notbi a_wn a_wb p_id f0_notbi a_wn f1_notbi a_wn a_wb f0_notbi f1_notbi p_con4bid f0_notbi f1_notbi a_wb f0_notbi a_wn f1_notbi a_wn a_wb p_impbii $.
$}

$(Negate both sides of a logical equivalence.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)

${
	$v ph ps  $.
	f0_notbii $f wff ph $.
	f1_notbii $f wff ps $.
	e0_notbii $e |- ( ph <-> ps ) $.
	p_notbii $p |- ( -. ph <-> -. ps ) $= e0_notbii f0_notbii f1_notbii p_notbi f0_notbii f1_notbii a_wb f0_notbii a_wn f1_notbii a_wn a_wb p_mpbi $.
$}

$(Theorem notbii is the congruence law for negation. $)

$($j congruence 'notbii'; $)

$(A contraposition inference.  (Contributed by NM, 21-May-1994.) $)

${
	$v ph ps  $.
	f0_con4bii $f wff ph $.
	f1_con4bii $f wff ps $.
	e0_con4bii $e |- ( -. ph <-> -. ps ) $.
	p_con4bii $p |- ( ph <-> ps ) $= e0_con4bii f0_con4bii f1_con4bii p_notbi f0_con4bii f1_con4bii a_wb f0_con4bii a_wn f1_con4bii a_wn a_wb p_mpbir $.
$}

$(An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)

${
	$v ph ps  $.
	f0_mtbi $f wff ph $.
	f1_mtbi $f wff ps $.
	e0_mtbi $e |- -. ph $.
	e1_mtbi $e |- ( ph <-> ps ) $.
	p_mtbi $p |- -. ps $= e0_mtbi e1_mtbi f0_mtbi f1_mtbi p_biimpri f1_mtbi f0_mtbi p_mto $.
$}

$(An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       14-Oct-2012.) $)

${
	$v ph ps  $.
	f0_mtbir $f wff ph $.
	f1_mtbir $f wff ps $.
	e0_mtbir $e |- -. ps $.
	e1_mtbir $e |- ( ph <-> ps ) $.
	p_mtbir $p |- -. ph $= e0_mtbir e1_mtbir f0_mtbir f1_mtbir p_bicomi f1_mtbir f0_mtbir p_mtbi $.
$}

$(A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 26-Nov-1995.) $)

${
	$v ph ps ch  $.
	f0_mtbid $f wff ph $.
	f1_mtbid $f wff ps $.
	f2_mtbid $f wff ch $.
	e0_mtbid $e |- ( ph -> -. ps ) $.
	e1_mtbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mtbid $p |- ( ph -> -. ch ) $= e0_mtbid e1_mtbid f0_mtbid f1_mtbid f2_mtbid p_biimprd f0_mtbid f2_mtbid f1_mtbid p_mtod $.
$}

$(A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 10-May-1994.) $)

${
	$v ph ps ch  $.
	f0_mtbird $f wff ph $.
	f1_mtbird $f wff ps $.
	f2_mtbird $f wff ch $.
	e0_mtbird $e |- ( ph -> -. ch ) $.
	e1_mtbird $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mtbird $p |- ( ph -> -. ps ) $= e0_mtbird e1_mtbird f0_mtbird f1_mtbird f2_mtbird p_biimpd f0_mtbird f1_mtbird f2_mtbird p_mtod $.
$}

$(An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 27-Nov-1995.) $)

${
	$v ph ps ch  $.
	f0_mtbii $f wff ph $.
	f1_mtbii $f wff ps $.
	f2_mtbii $f wff ch $.
	e0_mtbii $e |- -. ps $.
	e1_mtbii $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mtbii $p |- ( ph -> -. ch ) $= e0_mtbii e1_mtbii f0_mtbii f1_mtbii f2_mtbii p_biimprd f0_mtbii f2_mtbii f1_mtbii p_mtoi $.
$}

$(An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 24-Aug-1995.) $)

${
	$v ph ps ch  $.
	f0_mtbiri $f wff ph $.
	f1_mtbiri $f wff ps $.
	f2_mtbiri $f wff ch $.
	e0_mtbiri $e |- -. ch $.
	e1_mtbiri $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mtbiri $p |- ( ph -> -. ps ) $= e0_mtbiri e1_mtbiri f0_mtbiri f1_mtbiri f2_mtbiri p_biimpd f0_mtbiri f1_mtbiri f2_mtbiri p_mtoi $.
$}

$(A mixed syllogism inference from an implication and a biconditional.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)

${
	$v ph ps ch  $.
	f0_sylnib $f wff ph $.
	f1_sylnib $f wff ps $.
	f2_sylnib $f wff ch $.
	e0_sylnib $e |- ( ph -> -. ps ) $.
	e1_sylnib $e |- ( ps <-> ch ) $.
	p_sylnib $p |- ( ph -> -. ch ) $= e0_sylnib e1_sylnib f1_sylnib f2_sylnib a_wb f0_sylnib p_a1i f0_sylnib f1_sylnib f2_sylnib p_mtbid $.
$}

$(A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       Wolf Lammen, 16-Dec-2013.) $)

${
	$v ph ps ch  $.
	f0_sylnibr $f wff ph $.
	f1_sylnibr $f wff ps $.
	f2_sylnibr $f wff ch $.
	e0_sylnibr $e |- ( ph -> -. ps ) $.
	e1_sylnibr $e |- ( ch <-> ps ) $.
	p_sylnibr $p |- ( ph -> -. ch ) $= e0_sylnibr e1_sylnibr f2_sylnibr f1_sylnibr p_bicomi f0_sylnibr f1_sylnibr f2_sylnibr p_sylnib $.
$}

$(A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)

${
	$v ph ps ch  $.
	f0_sylnbi $f wff ph $.
	f1_sylnbi $f wff ps $.
	f2_sylnbi $f wff ch $.
	e0_sylnbi $e |- ( ph <-> ps ) $.
	e1_sylnbi $e |- ( -. ps -> ch ) $.
	p_sylnbi $p |- ( -. ph -> ch ) $= e0_sylnbi f0_sylnbi f1_sylnbi p_notbii e1_sylnbi f0_sylnbi a_wn f1_sylnbi a_wn f2_sylnbi p_sylbi $.
$}

$(A mixed syllogism inference from a biconditional and an implication.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)

${
	$v ph ps ch  $.
	f0_sylnbir $f wff ph $.
	f1_sylnbir $f wff ps $.
	f2_sylnbir $f wff ch $.
	e0_sylnbir $e |- ( ps <-> ph ) $.
	e1_sylnbir $e |- ( -. ps -> ch ) $.
	p_sylnbir $p |- ( -. ph -> ch ) $= e0_sylnbir f1_sylnbir f0_sylnbir p_bicomi e1_sylnbir f0_sylnbir f1_sylnbir f2_sylnbir p_sylnbi $.
$}

$(Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)

${
	$v ph ps ch  $.
	f0_xchnxbi $f wff ph $.
	f1_xchnxbi $f wff ps $.
	f2_xchnxbi $f wff ch $.
	e0_xchnxbi $e |- ( -. ph <-> ps ) $.
	e1_xchnxbi $e |- ( ph <-> ch ) $.
	p_xchnxbi $p |- ( -. ch <-> ps ) $= e1_xchnxbi f0_xchnxbi f2_xchnxbi p_notbii e0_xchnxbi f2_xchnxbi a_wn f0_xchnxbi a_wn f1_xchnxbi p_bitr3i $.
$}

$(Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)

${
	$v ph ps ch  $.
	f0_xchnxbir $f wff ph $.
	f1_xchnxbir $f wff ps $.
	f2_xchnxbir $f wff ch $.
	e0_xchnxbir $e |- ( -. ph <-> ps ) $.
	e1_xchnxbir $e |- ( ch <-> ph ) $.
	p_xchnxbir $p |- ( -. ch <-> ps ) $= e0_xchnxbir e1_xchnxbir f2_xchnxbir f0_xchnxbir p_bicomi f0_xchnxbir f1_xchnxbir f2_xchnxbir p_xchnxbi $.
$}

$(Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)

${
	$v ph ps ch  $.
	f0_xchbinx $f wff ph $.
	f1_xchbinx $f wff ps $.
	f2_xchbinx $f wff ch $.
	e0_xchbinx $e |- ( ph <-> -. ps ) $.
	e1_xchbinx $e |- ( ps <-> ch ) $.
	p_xchbinx $p |- ( ph <-> -. ch ) $= e0_xchbinx e1_xchbinx f1_xchbinx f2_xchbinx p_notbii f0_xchbinx f1_xchbinx a_wn f2_xchbinx a_wn p_bitri $.
$}

$(Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)

${
	$v ph ps ch  $.
	f0_xchbinxr $f wff ph $.
	f1_xchbinxr $f wff ps $.
	f2_xchbinxr $f wff ch $.
	e0_xchbinxr $e |- ( ph <-> -. ps ) $.
	e1_xchbinxr $e |- ( ch <-> ps ) $.
	p_xchbinxr $p |- ( ph <-> -. ch ) $= e0_xchbinxr e1_xchbinxr f2_xchbinxr f1_xchbinxr p_bicomi f0_xchbinxr f1_xchbinxr f2_xchbinxr p_xchbinx $.
$}

$(The next three rules are useful for building up wff's around a
     definition, in order to make use of the definition. $)

$(Introduce an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       6-Feb-2013.) $)

${
	$v ph ps ch  $.
	f0_imbi2i $f wff ph $.
	f1_imbi2i $f wff ps $.
	f2_imbi2i $f wff ch $.
	e0_imbi2i $e |- ( ph <-> ps ) $.
	p_imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $= e0_imbi2i f0_imbi2i f1_imbi2i a_wb f2_imbi2i p_a1i f2_imbi2i f0_imbi2i f1_imbi2i p_pm5.74i $.
$}

$(Inference adding a biconditional to the left in an equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.)  (Proof shortened by Wolf Lammen, 16-May-2013.) $)

${
	$v ph ps ch  $.
	f0_bibi2i $f wff ph $.
	f1_bibi2i $f wff ps $.
	f2_bibi2i $f wff ch $.
	e0_bibi2i $e |- ( ph <-> ps ) $.
	p_bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $= f2_bibi2i f0_bibi2i a_wb p_id e0_bibi2i f2_bibi2i f0_bibi2i a_wb f2_bibi2i f0_bibi2i f1_bibi2i p_syl6bb f2_bibi2i f1_bibi2i a_wb p_id e0_bibi2i f2_bibi2i f1_bibi2i a_wb f2_bibi2i f1_bibi2i f0_bibi2i p_syl6bbr f2_bibi2i f0_bibi2i a_wb f2_bibi2i f1_bibi2i a_wb p_impbii $.
$}

$(Inference adding a biconditional to the right in an equivalence.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_bibi1i $f wff ph $.
	f1_bibi1i $f wff ps $.
	f2_bibi1i $f wff ch $.
	e0_bibi1i $e |- ( ph <-> ps ) $.
	p_bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $= f0_bibi1i f2_bibi1i p_bicom e0_bibi1i f0_bibi1i f1_bibi1i f2_bibi1i p_bibi2i f2_bibi1i f1_bibi1i p_bicom f0_bibi1i f2_bibi1i a_wb f2_bibi1i f0_bibi1i a_wb f2_bibi1i f1_bibi1i a_wb f1_bibi1i f2_bibi1i a_wb p_3bitri $.
$}

$(The equivalence of two equivalences.  (Contributed by NM,
         5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_bibi12i $f wff ph $.
	f1_bibi12i $f wff ps $.
	f2_bibi12i $f wff ch $.
	f3_bibi12i $f wff th $.
	e0_bibi12i $e |- ( ph <-> ps ) $.
	e1_bibi12i $e |- ( ch <-> th ) $.
	p_bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $= e1_bibi12i f2_bibi12i f3_bibi12i f0_bibi12i p_bibi2i e0_bibi12i f0_bibi12i f1_bibi12i f3_bibi12i p_bibi1i f0_bibi12i f2_bibi12i a_wb f0_bibi12i f3_bibi12i a_wb f1_bibi12i f3_bibi12i a_wb p_bitri $.
$}

$(Deduction adding an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_imbi2d $f wff ph $.
	f1_imbi2d $f wff ps $.
	f2_imbi2d $f wff ch $.
	f3_imbi2d $f wff th $.
	e0_imbi2d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_imbi2d $p |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ) $= e0_imbi2d f0_imbi2d f1_imbi2d f2_imbi2d a_wb f3_imbi2d p_a1d f0_imbi2d f3_imbi2d f1_imbi2d f2_imbi2d p_pm5.74d $.
$}

$(Deduction adding a consequent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)

${
	$v ph ps ch th  $.
	f0_imbi1d $f wff ph $.
	f1_imbi1d $f wff ps $.
	f2_imbi1d $f wff ch $.
	f3_imbi1d $f wff th $.
	e0_imbi1d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $= e0_imbi1d f0_imbi1d f1_imbi1d f2_imbi1d p_biimprd f0_imbi1d f2_imbi1d f1_imbi1d f3_imbi1d p_imim1d e0_imbi1d f0_imbi1d f1_imbi1d f2_imbi1d p_biimpd f0_imbi1d f1_imbi1d f2_imbi1d f3_imbi1d p_imim1d f0_imbi1d f1_imbi1d f3_imbi1d a_wi f2_imbi1d f3_imbi1d a_wi p_impbid $.
$}

$(Deduction adding a biconditional to the left in an equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       19-May-2013.) $)

${
	$v ph ps ch th  $.
	f0_bibi2d $f wff ph $.
	f1_bibi2d $f wff ps $.
	f2_bibi2d $f wff ch $.
	f3_bibi2d $f wff th $.
	e0_bibi2d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_bibi2d $p |- ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ) $= e0_bibi2d f0_bibi2d f1_bibi2d f2_bibi2d p_pm5.74i f0_bibi2d f1_bibi2d a_wi f0_bibi2d f2_bibi2d a_wi f0_bibi2d f3_bibi2d a_wi p_bibi2i f0_bibi2d f3_bibi2d f1_bibi2d p_pm5.74 f0_bibi2d f3_bibi2d f2_bibi2d p_pm5.74 f0_bibi2d f3_bibi2d a_wi f0_bibi2d f1_bibi2d a_wi a_wb f0_bibi2d f3_bibi2d a_wi f0_bibi2d f2_bibi2d a_wi a_wb f0_bibi2d f3_bibi2d f1_bibi2d a_wb a_wi f0_bibi2d f3_bibi2d f2_bibi2d a_wb a_wi p_3bitr4i f0_bibi2d f3_bibi2d f1_bibi2d a_wb f3_bibi2d f2_bibi2d a_wb p_pm5.74ri $.
$}

$(Deduction adding a biconditional to the right in an equivalence.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_bibi1d $f wff ph $.
	f1_bibi1d $f wff ps $.
	f2_bibi1d $f wff ch $.
	f3_bibi1d $f wff th $.
	e0_bibi1d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_bibi1d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) ) $= e0_bibi1d f0_bibi1d f1_bibi1d f2_bibi1d f3_bibi1d p_bibi2d f1_bibi1d f3_bibi1d p_bicom f2_bibi1d f3_bibi1d p_bicom f0_bibi1d f3_bibi1d f1_bibi1d a_wb f3_bibi1d f2_bibi1d a_wb f1_bibi1d f3_bibi1d a_wb f2_bibi1d f3_bibi1d a_wb p_3bitr4g $.
$}

$(Deduction joining two equivalences to form equivalence of implications.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th ta  $.
	f0_imbi12d $f wff ph $.
	f1_imbi12d $f wff ps $.
	f2_imbi12d $f wff ch $.
	f3_imbi12d $f wff th $.
	f4_imbi12d $f wff ta $.
	e0_imbi12d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_imbi12d $e |- ( ph -> ( th <-> ta ) ) $.
	p_imbi12d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $= e0_imbi12d f0_imbi12d f1_imbi12d f2_imbi12d f3_imbi12d p_imbi1d e1_imbi12d f0_imbi12d f3_imbi12d f4_imbi12d f2_imbi12d p_imbi2d f0_imbi12d f1_imbi12d f3_imbi12d a_wi f2_imbi12d f3_imbi12d a_wi f2_imbi12d f4_imbi12d a_wi p_bitrd $.
$}

$(Deduction joining two equivalences to form equivalence of
       biconditionals.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th ta  $.
	f0_bibi12d $f wff ph $.
	f1_bibi12d $f wff ps $.
	f2_bibi12d $f wff ch $.
	f3_bibi12d $f wff th $.
	f4_bibi12d $f wff ta $.
	e0_bibi12d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_bibi12d $e |- ( ph -> ( th <-> ta ) ) $.
	p_bibi12d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) ) $= e0_bibi12d f0_bibi12d f1_bibi12d f2_bibi12d f3_bibi12d p_bibi1d e1_bibi12d f0_bibi12d f3_bibi12d f4_bibi12d f2_bibi12d p_bibi2d f0_bibi12d f1_bibi12d f3_bibi12d a_wb f2_bibi12d f3_bibi12d a_wb f2_bibi12d f4_bibi12d a_wb p_bitrd $.
$}

$(Theorem *4.84 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_imbi1 $f wff ph $.
	f1_imbi1 $f wff ps $.
	f2_imbi1 $f wff ch $.
	p_imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $= f0_imbi1 f1_imbi1 a_wb p_id f0_imbi1 f1_imbi1 a_wb f0_imbi1 f1_imbi1 f2_imbi1 p_imbi1d $.
$}

$(Theorem *4.85 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)

${
	$v ph ps ch  $.
	f0_imbi2 $f wff ph $.
	f1_imbi2 $f wff ps $.
	f2_imbi2 $f wff ch $.
	p_imbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $= f0_imbi2 f1_imbi2 a_wb p_id f0_imbi2 f1_imbi2 a_wb f0_imbi2 f1_imbi2 f2_imbi2 p_imbi2d $.
$}

$(Introduce a consequent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)

${
	$v ph ps ch  $.
	f0_imbi1i $f wff ph $.
	f1_imbi1i $f wff ps $.
	f2_imbi1i $f wff ch $.
	e0_imbi1i $e |- ( ph <-> ps ) $.
	p_imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $= e0_imbi1i f0_imbi1i f1_imbi1i f2_imbi1i p_imbi1 f0_imbi1i f1_imbi1i a_wb f0_imbi1i f2_imbi1i a_wi f1_imbi1i f2_imbi1i a_wi a_wb a_ax-mp $.
$}

$(Join two logical equivalences to form equivalence of implications.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_imbi12i $f wff ph $.
	f1_imbi12i $f wff ps $.
	f2_imbi12i $f wff ch $.
	f3_imbi12i $f wff th $.
	e0_imbi12i $e |- ( ph <-> ps ) $.
	e1_imbi12i $e |- ( ch <-> th ) $.
	p_imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $= e1_imbi12i f2_imbi12i f3_imbi12i f0_imbi12i p_imbi2i e0_imbi12i f0_imbi12i f1_imbi12i f3_imbi12i p_imbi1i f0_imbi12i f2_imbi12i a_wi f0_imbi12i f3_imbi12i a_wi f1_imbi12i f3_imbi12i a_wi p_bitri $.
$}

$(Theorem imbi12i is the congruence law for implication. $)

$($j congruence 'imbi12i'; $)

$(Theorem *4.86 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_bibi1 $f wff ph $.
	f1_bibi1 $f wff ps $.
	f2_bibi1 $f wff ch $.
	p_bibi1 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $= f0_bibi1 f1_bibi1 a_wb p_id f0_bibi1 f1_bibi1 a_wb f0_bibi1 f1_bibi1 f2_bibi1 p_bibi1d $.
$}

$(Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 15-Apr-1995.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)

${
	$v ph ps  $.
	f0_con2bi $f wff ph $.
	f1_con2bi $f wff ps $.
	p_con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $= f0_con2bi f1_con2bi a_wn p_notbi f1_con2bi p_notnot f1_con2bi f1_con2bi a_wn a_wn f0_con2bi a_wn p_bibi2i f0_con2bi a_wn f1_con2bi p_bicom f0_con2bi f1_con2bi a_wn a_wb f0_con2bi a_wn f1_con2bi a_wn a_wn a_wb f0_con2bi a_wn f1_con2bi a_wb f1_con2bi f0_con2bi a_wn a_wb p_3bitr2i $.
$}

$(A contraposition deduction.  (Contributed by NM, 15-Apr-1995.) $)

${
	$v ph ps ch  $.
	f0_con2bid $f wff ph $.
	f1_con2bid $f wff ps $.
	f2_con2bid $f wff ch $.
	e0_con2bid $e |- ( ph -> ( ps <-> -. ch ) ) $.
	p_con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $= e0_con2bid f2_con2bid f1_con2bid p_con2bi f0_con2bid f1_con2bid f2_con2bid a_wn a_wb f2_con2bid f1_con2bid a_wn a_wb p_sylibr $.
$}

$(A contraposition deduction.  (Contributed by NM, 9-Oct-1999.) $)

${
	$v ph ps ch  $.
	f0_con1bid $f wff ph $.
	f1_con1bid $f wff ps $.
	f2_con1bid $f wff ch $.
	e0_con1bid $e |- ( ph -> ( -. ps <-> ch ) ) $.
	p_con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $= e0_con1bid f0_con1bid f1_con1bid a_wn f2_con1bid p_bicomd f0_con1bid f2_con1bid f1_con1bid p_con2bid f0_con1bid f1_con1bid f2_con1bid a_wn p_bicomd $.
$}

$(A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 13-Oct-2012.) $)

${
	$v ph ps  $.
	f0_con1bii $f wff ph $.
	f1_con1bii $f wff ps $.
	e0_con1bii $e |- ( -. ph <-> ps ) $.
	p_con1bii $p |- ( -. ps <-> ph ) $= f0_con1bii p_notnot e0_con1bii f0_con1bii f0_con1bii a_wn f1_con1bii p_xchbinx f0_con1bii f1_con1bii a_wn p_bicomi $.
$}

$(A contraposition inference.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_con2bii $f wff ph $.
	f1_con2bii $f wff ps $.
	e0_con2bii $e |- ( ph <-> -. ps ) $.
	p_con2bii $p |- ( ps <-> -. ph ) $= e0_con2bii f0_con2bii f1_con2bii a_wn p_bicomi f1_con2bii f0_con2bii p_con1bii f0_con2bii a_wn f1_con2bii p_bicomi $.
$}

$(Contraposition.  Bidirectional version of ~ con1 .  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_con1b $f wff ph $.
	f1_con1b $f wff ps $.
	p_con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $= f0_con1b f1_con1b p_con1 f1_con1b f0_con1b p_con1 f0_con1b a_wn f1_con1b a_wi f1_con1b a_wn f0_con1b a_wi p_impbii $.
$}

$(Contraposition.  Bidirectional version of ~ con2 .  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_con2b $f wff ph $.
	f1_con2b $f wff ps $.
	p_con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $= f0_con2b f1_con2b p_con2 f1_con2b f0_con2b p_con2 f0_con2b f1_con2b a_wn a_wi f1_con2b f0_con2b a_wn a_wi p_impbii $.
$}

$(A wff is equivalent to itself with true antecedent.  (Contributed by NM,
     28-Jan-1996.) $)

${
	$v ph ps  $.
	f0_biimt $f wff ph $.
	f1_biimt $f wff ps $.
	p_biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $= f1_biimt f0_biimt a_ax-1 f0_biimt f1_biimt p_pm2.27 f0_biimt f1_biimt f0_biimt f1_biimt a_wi p_impbid2 $.
$}

$(Theorem *5.5 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm5.5 $f wff ph $.
	f1_pm5.5 $f wff ps $.
	p_pm5.5 $p |- ( ph -> ( ( ph -> ps ) <-> ps ) ) $= f0_pm5.5 f1_pm5.5 p_biimt f0_pm5.5 f1_pm5.5 f0_pm5.5 f1_pm5.5 a_wi p_bicomd $.
$}

$(Inference rule introducing a theorem as an antecedent.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)

${
	$v ph ps  $.
	f0_a1bi $f wff ph $.
	f1_a1bi $f wff ps $.
	e0_a1bi $e |- ph $.
	p_a1bi $p |- ( ps <-> ( ph -> ps ) ) $= e0_a1bi f0_a1bi f1_a1bi p_biimt f0_a1bi f1_a1bi f0_a1bi f1_a1bi a_wi a_wb a_ax-mp $.
$}

$(A false consequent falsifies an antecedent.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Nov-2012.) $)

${
	$v ph ps  $.
	f0_mt2bi $f wff ph $.
	f1_mt2bi $f wff ps $.
	e0_mt2bi $e |- ph $.
	p_mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $= e0_mt2bi f0_mt2bi f1_mt2bi a_wn p_a1bi f0_mt2bi f1_mt2bi p_con2b f1_mt2bi a_wn f0_mt2bi f1_mt2bi a_wn a_wi f1_mt2bi f0_mt2bi a_wn a_wi p_bitri $.
$}

$(Modus-tollens-like theorem.  (Contributed by NM, 7-Apr-2001.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2012.) $)

${
	$v ph ps  $.
	f0_mtt $f wff ph $.
	f1_mtt $f wff ps $.
	p_mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $= f0_mtt a_wn f1_mtt a_wn p_biimt f1_mtt f0_mtt p_con34b f0_mtt a_wn f1_mtt a_wn f0_mtt a_wn f1_mtt a_wn a_wi f1_mtt f0_mtt a_wi p_syl6bbr $.
$}

$(Theorem *5.501 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm5.501 $f wff ph $.
	f1_pm5.501 $f wff ps $.
	p_pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $= f0_pm5.501 f1_pm5.501 p_pm5.1im f0_pm5.501 f1_pm5.501 p_bi1 f0_pm5.501 f1_pm5.501 a_wb f0_pm5.501 f1_pm5.501 p_com12 f0_pm5.501 f1_pm5.501 f0_pm5.501 f1_pm5.501 a_wb p_impbid $.
$}

$(Implication in terms of implication and biconditional.  (Contributed by
     NM, 31-Mar-1994.)  (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)

${
	$v ph ps  $.
	f0_ibib $f wff ph $.
	f1_ibib $f wff ps $.
	p_ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $= f0_ibib f1_ibib p_pm5.501 f0_ibib f1_ibib f0_ibib f1_ibib a_wb p_pm5.74i $.
$}

$(Implication in terms of implication and biconditional.  (Contributed by
     NM, 29-Apr-2005.)  (Proof shortened by Wolf Lammen, 21-Dec-2013.) $)

${
	$v ph ps  $.
	f0_ibibr $f wff ph $.
	f1_ibibr $f wff ps $.
	p_ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $= f0_ibibr f1_ibibr p_pm5.501 f0_ibibr f1_ibibr p_bicom f0_ibibr f1_ibibr f0_ibibr f1_ibibr a_wb f1_ibibr f0_ibibr a_wb p_syl6bb f0_ibibr f1_ibibr f1_ibibr f0_ibibr a_wb p_pm5.74i $.
$}

$(A wff is equivalent to its equivalence with truth.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v ph ps  $.
	f0_tbt $f wff ph $.
	f1_tbt $f wff ps $.
	e0_tbt $e |- ph $.
	p_tbt $p |- ( ps <-> ( ps <-> ph ) ) $= e0_tbt f0_tbt f1_tbt p_ibibr f0_tbt f1_tbt f1_tbt f0_tbt a_wb p_pm5.74ri f0_tbt f1_tbt f1_tbt f0_tbt a_wb a_wb a_ax-mp $.
$}

$(The negation of a wff is equivalent to the wff's equivalence to
     falsehood.  (Contributed by Juha Arpiainen, 19-Jan-2006.)  (Proof
     shortened by Wolf Lammen, 28-Jan-2013.) $)

${
	$v ph ps  $.
	f0_nbn2 $f wff ph $.
	f1_nbn2 $f wff ps $.
	p_nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $= f0_nbn2 a_wn f1_nbn2 a_wn p_pm5.501 f0_nbn2 f1_nbn2 p_notbi f0_nbn2 a_wn f1_nbn2 a_wn f0_nbn2 a_wn f1_nbn2 a_wn a_wb f0_nbn2 f1_nbn2 a_wb p_syl6bbr $.
$}

$(Transfer negation via an equivalence.  (Contributed by NM, 3-Oct-2007.)
     (Proof shortened by Wolf Lammen, 28-Jan-2013.) $)

${
	$v ph ps  $.
	f0_bibif $f wff ph $.
	f1_bibif $f wff ps $.
	p_bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $= f1_bibif f0_bibif p_nbn2 f1_bibif f0_bibif p_bicom f1_bibif a_wn f0_bibif a_wn f1_bibif f0_bibif a_wb f0_bibif f1_bibif a_wb p_syl6rbb $.
$}

$(The negation of a wff is equivalent to the wff's equivalence to
       falsehood.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 3-Oct-2013.) $)

${
	$v ph ps  $.
	f0_nbn $f wff ph $.
	f1_nbn $f wff ps $.
	e0_nbn $e |- -. ph $.
	p_nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $= e0_nbn f1_nbn f0_nbn p_bibif f0_nbn a_wn f1_nbn f0_nbn a_wb f1_nbn a_wn a_wb a_ax-mp f1_nbn f0_nbn a_wb f1_nbn a_wn p_bicomi $.
$}

$(Transfer falsehood via equivalence.  (Contributed by NM,
       11-Sep-2006.) $)

${
	$v ph ps  $.
	f0_nbn3 $f wff ph $.
	f1_nbn3 $f wff ps $.
	e0_nbn3 $e |- ph $.
	p_nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $= e0_nbn3 f0_nbn3 p_notnoti f0_nbn3 a_wn f1_nbn3 p_nbn $.
$}

$(Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ bi2 -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.) $)

${
	$v ph ps  $.
	f0_pm5.21im $f wff ph $.
	f1_pm5.21im $f wff ps $.
	p_pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $= f0_pm5.21im f1_pm5.21im p_nbn2 f0_pm5.21im a_wn f1_pm5.21im a_wn f0_pm5.21im f1_pm5.21im a_wb p_biimpd $.
$}

$(Two falsehoods are equivalent.  (Contributed by NM, 4-Apr-2005.)  (Proof
       shortened by Wolf Lammen, 19-May-2013.) $)

${
	$v ph ps  $.
	f0_2false $f wff ph $.
	f1_2false $f wff ps $.
	e0_2false $e |- -. ph $.
	e1_2false $e |- -. ps $.
	p_2false $p |- ( ph <-> ps ) $= e0_2false e1_2false f0_2false a_wn f1_2false a_wn p_2th f0_2false f1_2false p_con4bii $.
$}

$(Two falsehoods are equivalent (deduction rule).  (Contributed by NM,
       11-Oct-2013.) $)

${
	$v ph ps ch  $.
	f0_2falsed $f wff ph $.
	f1_2falsed $f wff ps $.
	f2_2falsed $f wff ch $.
	e0_2falsed $e |- ( ph -> -. ps ) $.
	e1_2falsed $e |- ( ph -> -. ch ) $.
	p_2falsed $p |- ( ph -> ( ps <-> ch ) ) $= e0_2falsed f0_2falsed f1_2falsed f2_2falsed p_pm2.21d e1_2falsed f0_2falsed f2_2falsed f1_2falsed p_pm2.21d f0_2falsed f1_2falsed f2_2falsed p_impbid $.
$}

$(Two propositions implying a false one are equivalent.  (Contributed by
       NM, 16-Feb-1996.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)

${
	$v ph ps ch  $.
	f0_pm5.21ni $f wff ph $.
	f1_pm5.21ni $f wff ps $.
	f2_pm5.21ni $f wff ch $.
	e0_pm5.21ni $e |- ( ph -> ps ) $.
	e1_pm5.21ni $e |- ( ch -> ps ) $.
	p_pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $= e0_pm5.21ni f0_pm5.21ni f1_pm5.21ni p_con3i e1_pm5.21ni f2_pm5.21ni f1_pm5.21ni p_con3i f1_pm5.21ni a_wn f0_pm5.21ni f2_pm5.21ni p_2falsed $.
$}

$(Eliminate an antecedent implied by each side of a biconditional.
         (Contributed by NM, 21-May-1999.) $)

${
	$v ph ps ch  $.
	f0_pm5.21nii $f wff ph $.
	f1_pm5.21nii $f wff ps $.
	f2_pm5.21nii $f wff ch $.
	e0_pm5.21nii $e |- ( ph -> ps ) $.
	e1_pm5.21nii $e |- ( ch -> ps ) $.
	e2_pm5.21nii $e |- ( ps -> ( ph <-> ch ) ) $.
	p_pm5.21nii $p |- ( ph <-> ch ) $= e2_pm5.21nii e0_pm5.21nii e1_pm5.21nii f0_pm5.21nii f1_pm5.21nii f2_pm5.21nii p_pm5.21ni f1_pm5.21nii f0_pm5.21nii f2_pm5.21nii a_wb p_pm2.61i $.
$}

$(Eliminate an antecedent implied by each side of a biconditional,
       deduction version.  (Contributed by Paul Chapman, 21-Nov-2012.)  (Proof
       shortened by Wolf Lammen, 6-Oct-2013.) $)

${
	$v ph ps ch th  $.
	f0_pm5.21ndd $f wff ph $.
	f1_pm5.21ndd $f wff ps $.
	f2_pm5.21ndd $f wff ch $.
	f3_pm5.21ndd $f wff th $.
	e0_pm5.21ndd $e |- ( ph -> ( ch -> ps ) ) $.
	e1_pm5.21ndd $e |- ( ph -> ( th -> ps ) ) $.
	e2_pm5.21ndd $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
	p_pm5.21ndd $p |- ( ph -> ( ch <-> th ) ) $= e2_pm5.21ndd e0_pm5.21ndd f0_pm5.21ndd f2_pm5.21ndd f1_pm5.21ndd p_con3d e1_pm5.21ndd f0_pm5.21ndd f3_pm5.21ndd f1_pm5.21ndd p_con3d f2_pm5.21ndd f3_pm5.21ndd p_pm5.21im f0_pm5.21ndd f1_pm5.21ndd a_wn f2_pm5.21ndd a_wn f3_pm5.21ndd a_wn f2_pm5.21ndd f3_pm5.21ndd a_wb p_syl6c f0_pm5.21ndd f1_pm5.21ndd f2_pm5.21ndd f3_pm5.21ndd a_wb p_pm2.61d $.
$}

$(Combine antecedents into a single bi-conditional.  This inference,
       reminiscent of ~ ja , is reversible:  The hypotheses can be deduced from
       the conclusion alone (see ~ pm5.1im and ~ pm5.21im ).  (Contributed by
       Wolf Lammen, 13-May-2013.) $)

${
	$v ph ps ch  $.
	f0_bija $f wff ph $.
	f1_bija $f wff ps $.
	f2_bija $f wff ch $.
	e0_bija $e |- ( ph -> ( ps -> ch ) ) $.
	e1_bija $e |- ( -. ph -> ( -. ps -> ch ) ) $.
	p_bija $p |- ( ( ph <-> ps ) -> ch ) $= f0_bija f1_bija p_bi2 e0_bija f1_bija f0_bija f1_bija a_wb f0_bija f2_bija p_syli f0_bija f1_bija p_bi1 f0_bija f1_bija a_wb f0_bija f1_bija p_con3d e1_bija f1_bija a_wn f0_bija f1_bija a_wb f0_bija a_wn f2_bija p_syli f0_bija f1_bija a_wb f1_bija f2_bija p_pm2.61d $.
$}

$(Theorem *5.18 of [WhiteheadRussell] p. 124.  This theorem says that
     logical equivalence is the same as negated "exclusive-or."  (Contributed
     by NM, 28-Jun-2002.)  (Proof shortened by Andrew Salmon, 20-Jun-2011.)
     (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)

${
	$v ph ps  $.
	f0_pm5.18 $f wff ph $.
	f1_pm5.18 $f wff ps $.
	p_pm5.18 $p |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) $= f0_pm5.18 f1_pm5.18 a_wn p_pm5.501 f0_pm5.18 f1_pm5.18 f0_pm5.18 f1_pm5.18 a_wn a_wb p_con1bid f0_pm5.18 f1_pm5.18 p_pm5.501 f0_pm5.18 f0_pm5.18 f1_pm5.18 a_wn a_wb a_wn f1_pm5.18 f0_pm5.18 f1_pm5.18 a_wb p_bitr2d f0_pm5.18 f1_pm5.18 a_wn p_nbn2 f0_pm5.18 a_wn f1_pm5.18 a_wn f0_pm5.18 f1_pm5.18 a_wn a_wb p_con1bid f0_pm5.18 f1_pm5.18 p_nbn2 f0_pm5.18 a_wn f0_pm5.18 f1_pm5.18 a_wn a_wb a_wn f1_pm5.18 a_wn f0_pm5.18 f1_pm5.18 a_wb p_bitr2d f0_pm5.18 f0_pm5.18 f1_pm5.18 a_wb f0_pm5.18 f1_pm5.18 a_wn a_wb a_wn a_wb p_pm2.61i $.
$}

$(Two ways to express "exclusive or."  (Contributed by NM, 1-Jan-2006.) $)

${
	$v ph ps  $.
	f0_xor3 $f wff ph $.
	f1_xor3 $f wff ps $.
	p_xor3 $p |- ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) $= f0_xor3 f1_xor3 p_pm5.18 f0_xor3 f1_xor3 a_wb f0_xor3 f1_xor3 a_wn a_wb p_con2bii f0_xor3 f1_xor3 a_wn a_wb f0_xor3 f1_xor3 a_wb a_wn p_bicomi $.
$}

$(Move negation outside of biconditional.  Compare Theorem *5.18 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 20-Sep-2013.) $)

${
	$v ph ps  $.
	f0_nbbn $f wff ph $.
	f1_nbbn $f wff ps $.
	p_nbbn $p |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) $= f0_nbbn f1_nbbn p_xor3 f0_nbbn f1_nbbn p_con2bi f1_nbbn f0_nbbn a_wn p_bicom f0_nbbn f1_nbbn a_wb a_wn f0_nbbn f1_nbbn a_wn a_wb f1_nbbn f0_nbbn a_wn a_wb f0_nbbn a_wn f1_nbbn a_wb p_3bitrri $.
$}

$(Associative law for the biconditional.  An axiom of system DS in Vladimir
     Lifschitz, "On calculational proofs", Annals of Pure and Applied Logic,
     113:207-224, 2002,
     ~ http://www.cs.utexas.edu/users/ai-lab/pub-view.php?PubID=26805 .
     Interestingly, this law was not included in _Principia Mathematica_ but
     was apparently first noted by Jan Lukasiewicz circa 1923.  (Contributed by
     NM, 8-Jan-2005.)  (Proof shortened by Juha Arpiainen, 19-Jan-2006.)
     (Proof shortened by Wolf Lammen, 21-Sep-2013.) $)

${
	$v ph ps ch  $.
	f0_biass $f wff ph $.
	f1_biass $f wff ps $.
	f2_biass $f wff ch $.
	p_biass $p |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $= f0_biass f1_biass p_pm5.501 f0_biass f1_biass f0_biass f1_biass a_wb f2_biass p_bibi1d f0_biass f1_biass f2_biass a_wb p_pm5.501 f0_biass f1_biass f2_biass a_wb f0_biass f1_biass a_wb f2_biass a_wb f0_biass f1_biass f2_biass a_wb a_wb p_bitr3d f1_biass f2_biass p_nbbn f0_biass f1_biass p_nbn2 f0_biass a_wn f1_biass a_wn f0_biass f1_biass a_wb f2_biass p_bibi1d f1_biass f2_biass a_wb a_wn f1_biass a_wn f2_biass a_wb f0_biass a_wn f0_biass f1_biass a_wb f2_biass a_wb p_syl5bbr f0_biass f1_biass f2_biass a_wb p_nbn2 f0_biass a_wn f1_biass f2_biass a_wb a_wn f0_biass f1_biass a_wb f2_biass a_wb f0_biass f1_biass f2_biass a_wb a_wb p_bitr3d f0_biass f0_biass f1_biass a_wb f2_biass a_wb f0_biass f1_biass f2_biass a_wb a_wb a_wb p_pm2.61i $.
$}

$(Theorem *5.19 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph  $.
	f0_pm5.19 $f wff ph $.
	p_pm5.19 $p |- -. ( ph <-> -. ph ) $= f0_pm5.19 p_biid f0_pm5.19 f0_pm5.19 p_pm5.18 f0_pm5.19 f0_pm5.19 a_wb f0_pm5.19 f0_pm5.19 a_wn a_wb a_wn p_mpbi $.
$}

$(Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_bi2.04 $f wff ph $.
	f1_bi2.04 $f wff ps $.
	f2_bi2.04 $f wff ch $.
	p_bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $= f0_bi2.04 f1_bi2.04 f2_bi2.04 p_pm2.04 f1_bi2.04 f0_bi2.04 f2_bi2.04 p_pm2.04 f0_bi2.04 f1_bi2.04 f2_bi2.04 a_wi a_wi f1_bi2.04 f0_bi2.04 f2_bi2.04 a_wi a_wi p_impbii $.
$}

$(Antecedent absorption implication.  Theorem *5.4 of [WhiteheadRussell]
     p. 125.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_pm5.4 $f wff ph $.
	f1_pm5.4 $f wff ps $.
	p_pm5.4 $p |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ) $= f0_pm5.4 f1_pm5.4 p_pm2.43 f0_pm5.4 f1_pm5.4 a_wi f0_pm5.4 a_ax-1 f0_pm5.4 f0_pm5.4 f1_pm5.4 a_wi a_wi f0_pm5.4 f1_pm5.4 a_wi p_impbii $.
$}

$(Distributive law for implication.  Compare Theorem *5.41 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_imdi $f wff ph $.
	f1_imdi $f wff ps $.
	f2_imdi $f wff ch $.
	p_imdi $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $= f0_imdi f1_imdi f2_imdi a_ax-2 f0_imdi f1_imdi f2_imdi p_pm2.86 f0_imdi f1_imdi f2_imdi a_wi a_wi f0_imdi f1_imdi a_wi f0_imdi f2_imdi a_wi a_wi p_impbii $.
$}

$(Theorem *5.41 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 12-Oct-2012.) $)

${
	$v ph ps ch  $.
	f0_pm5.41 $f wff ph $.
	f1_pm5.41 $f wff ps $.
	f2_pm5.41 $f wff ch $.
	p_pm5.41 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) <-> ( ph -> ( ps -> ch ) ) ) $= f0_pm5.41 f1_pm5.41 f2_pm5.41 p_imdi f0_pm5.41 f1_pm5.41 f2_pm5.41 a_wi a_wi f0_pm5.41 f1_pm5.41 a_wi f0_pm5.41 f2_pm5.41 a_wi a_wi p_bicomi $.
$}

$(Theorem *4.8 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph  $.
	f0_pm4.8 $f wff ph $.
	p_pm4.8 $p |- ( ( ph -> -. ph ) <-> -. ph ) $= f0_pm4.8 p_pm2.01 f0_pm4.8 a_wn f0_pm4.8 a_ax-1 f0_pm4.8 f0_pm4.8 a_wn a_wi f0_pm4.8 a_wn p_impbii $.
$}

$(Theorem *4.81 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph  $.
	f0_pm4.81 $f wff ph $.
	p_pm4.81 $p |- ( ( -. ph -> ph ) <-> ph ) $= f0_pm4.81 p_pm2.18 f0_pm4.81 f0_pm4.81 p_pm2.24 f0_pm4.81 a_wn f0_pm4.81 a_wi f0_pm4.81 p_impbii $.
$}

$(Simplify an implication between two implications when the antecedent of
     the first is a consequence of the antecedent of the second.  The reverse
     form is useful in producing the successor step in induction proofs.
     (Contributed by Paul Chapman, 22-Jun-2011.)  (Proof shortened by Wolf
     Lammen, 14-Sep-2013.) $)

${
	$v ph ps ch th  $.
	f0_imim21b $f wff ph $.
	f1_imim21b $f wff ps $.
	f2_imim21b $f wff ch $.
	f3_imim21b $f wff th $.
	p_imim21b $p |- ( ( ps -> ph ) -> ( ( ( ph -> ch ) -> ( ps -> th ) ) <-> ( ps -> ( ch -> th ) ) ) ) $= f0_imim21b f2_imim21b a_wi f1_imim21b f3_imim21b p_bi2.04 f0_imim21b f2_imim21b p_pm5.5 f0_imim21b f0_imim21b f2_imim21b a_wi f2_imim21b f3_imim21b p_imbi1d f0_imim21b f0_imim21b f2_imim21b a_wi f3_imim21b a_wi f2_imim21b f3_imim21b a_wi a_wb f1_imim21b p_imim2i f1_imim21b f0_imim21b a_wi f1_imim21b f0_imim21b f2_imim21b a_wi f3_imim21b a_wi f2_imim21b f3_imim21b a_wi p_pm5.74d f0_imim21b f2_imim21b a_wi f1_imim21b f3_imim21b a_wi a_wi f1_imim21b f0_imim21b f2_imim21b a_wi f3_imim21b a_wi a_wi f1_imim21b f0_imim21b a_wi f1_imim21b f2_imim21b f3_imim21b a_wi a_wi p_syl5bb $.
$}


