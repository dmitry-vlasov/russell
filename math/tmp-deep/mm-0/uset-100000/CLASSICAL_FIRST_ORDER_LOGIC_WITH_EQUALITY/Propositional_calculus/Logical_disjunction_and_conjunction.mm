$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_equivalence.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical disjunction and conjunction

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Here we define disjunction (logical 'or') ` \/ ` ( ~ df-or ) and conjunction
  (logical 'and') ` /\ ` ( ~ df-an ). We also define various rules for
  simplifying and applying them, e.g., ~ olc , ~ orc , and ~ orcom .

$)
$( Declare connectives for disjunction ('or') and conjunction ('and'). $)
$c \/  $.
$( Vee (read:  'or') $)
$c /\  $.
$( Wedge (read:  'and') $)
$( Extend wff definition to include disjunction ('or'). $)
${
	$v ph $.
	$v ps $.
	fwo_0 $f wff ph $.
	fwo_1 $f wff ps $.
	wo $a wff ( ph \/ ps ) $.
$}
$( Extend wff definition to include conjunction ('and'). $)
${
	$v ph $.
	$v ps $.
	fwa_0 $f wff ph $.
	fwa_1 $f wff ps $.
	wa $a wff ( ph /\ ps ) $.
$}
$( Define disjunction (logical 'or').  Definition of [Margaris] p. 49.  When
     the left operand, right operand, or both are true, the result is true;
     when both sides are false, the result is false.  For example, it is true
     that ` ( 2 = 3 \/ 4 = 4 ) ` ( ~ ex-or ).  After we define the constant
     true ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we
     will be able to prove these truth table values:
     ` ( ( T. \/ T. ) <-> T. ) ` ( ~ truortru ), ` ( ( T. \/ F. ) <-> T. ) `
     ( ~ truorfal ), ` ( ( F. \/ T. ) <-> T. ) ` ( ~ falortru ), and
     ` ( ( F. \/ F. ) <-> F. ) ` ( ~ falorfal ).

     This is our first use of the biconditional connective in a definition; we
     use the biconditional connective in place of the traditional "<=def=>",
     which means the same thing, except that we can manipulate the
     biconditional connective directly in proofs rather than having to rely on
     an informal definition substitution rule.  Note that if we mechanically
     substitute ` ( -. ph -> ps ) ` for ` ( ph \/ ps ) ` , we end up with an
     instance of previously proved theorem ~ biid .  This is the justification
     for the definition, along with the fact that it introduces a new symbol
     ` \/ ` .  Contrast with ` /\ ` ( ~ df-an ), ` -> ` ( ~ wi ), ` -/\ `
     ( ~ df-nan ), and ` \/_ ` ( ~ df-xor ) .  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	fdf-or_0 $f wff ph $.
	fdf-or_1 $f wff ps $.
	df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.
$}
$( Define conjunction (logical 'and').  Definition of [Margaris] p. 49.  When
     both the left and right operand are true, the result is true; when either
     is false, the result is false.  For example, it is true that
     ` ( 2 = 2 /\ 3 = 3 ) ` .  After we define the constant true ` T. `
     ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be able
     to prove these truth table values: ` ( ( T. /\ T. ) <-> T. ) `
     ( ~ truantru ), ` ( ( T. /\ F. ) <-> F. ) ` ( ~ truanfal ),
     ` ( ( F. /\ T. ) <-> F. ) ` ( ~ falantru ), and
     ` ( ( F. /\ F. ) <-> F. ) ` ( ~ falanfal ).

     Contrast with ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), ` -/\ ` ( ~ df-nan ),
     and ` \/_ ` ( ~ df-xor ) .  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	fdf-an_0 $f wff ph $.
	fdf-an_1 $f wff ps $.
	df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.
$}
$( Theorem *4.64 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.64_0 $f wff ph $.
	fpm4.64_1 $f wff ps $.
	pm4.64 $p |- ( ( -. ph -> ps ) <-> ( ph \/ ps ) ) $= fpm4.64_0 fpm4.64_1 wo fpm4.64_0 wn fpm4.64_1 wi fpm4.64_0 fpm4.64_1 df-or bicomi $.
$}
$( Theorem *2.53 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.53_0 $f wff ph $.
	fpm2.53_1 $f wff ps $.
	pm2.53 $p |- ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $= fpm2.53_0 fpm2.53_1 wo fpm2.53_0 wn fpm2.53_1 wi fpm2.53_0 fpm2.53_1 df-or biimpi $.
$}
$( Theorem *2.54 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.54_0 $f wff ph $.
	fpm2.54_1 $f wff ps $.
	pm2.54 $p |- ( ( -. ph -> ps ) -> ( ph \/ ps ) ) $= fpm2.54_0 fpm2.54_1 wo fpm2.54_0 wn fpm2.54_1 wi fpm2.54_0 fpm2.54_1 df-or biimpri $.
$}
$( Infer implication from disjunction.  (Contributed by NM,
       11-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	fori_0 $f wff ph $.
	fori_1 $f wff ps $.
	eori_0 $e |- ( ph \/ ps ) $.
	ori $p |- ( -. ph -> ps ) $= fori_0 fori_1 wo fori_0 wn fori_1 wi eori_0 fori_0 fori_1 df-or mpbi $.
$}
$( Infer implication from disjunction.  (Contributed by NM,
       11-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	forri_0 $f wff ph $.
	forri_1 $f wff ps $.
	eorri_0 $e |- ( -. ph -> ps ) $.
	orri $p |- ( ph \/ ps ) $= forri_0 forri_1 wo forri_0 wn forri_1 wi eorri_0 forri_0 forri_1 df-or mpbir $.
$}
$( Deduce implication from disjunction.  (Contributed by NM,
       18-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	ford_0 $f wff ph $.
	ford_1 $f wff ps $.
	ford_2 $f wff ch $.
	eord_0 $e |- ( ph -> ( ps \/ ch ) ) $.
	ord $p |- ( ph -> ( -. ps -> ch ) ) $= ford_0 ford_1 ford_2 wo ford_1 wn ford_2 wi eord_0 ford_1 ford_2 df-or sylib $.
$}
$( Deduce implication from disjunction.  (Contributed by NM,
       27-Nov-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forrd_0 $f wff ph $.
	forrd_1 $f wff ps $.
	forrd_2 $f wff ch $.
	eorrd_0 $e |- ( ph -> ( -. ps -> ch ) ) $.
	orrd $p |- ( ph -> ( ps \/ ch ) ) $= forrd_0 forrd_1 wn forrd_2 wi forrd_1 forrd_2 wo eorrd_0 forrd_1 forrd_2 pm2.54 syl $.
$}
$( Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 5-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjaoi_0 $f wff ph $.
	fjaoi_1 $f wff ps $.
	fjaoi_2 $f wff ch $.
	ejaoi_0 $e |- ( ph -> ps ) $.
	ejaoi_1 $e |- ( ch -> ps ) $.
	jaoi $p |- ( ( ph \/ ch ) -> ps ) $= fjaoi_0 fjaoi_2 wo fjaoi_0 fjaoi_1 fjaoi_0 fjaoi_2 wo fjaoi_0 wn fjaoi_2 fjaoi_1 fjaoi_0 fjaoi_2 pm2.53 ejaoi_1 syl6 ejaoi_0 pm2.61d2 $.
$}
$( Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 18-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjaod_0 $f wff ph $.
	fjaod_1 $f wff ps $.
	fjaod_2 $f wff ch $.
	fjaod_3 $f wff th $.
	ejaod_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ejaod_1 $e |- ( ph -> ( th -> ch ) ) $.
	jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $= fjaod_1 fjaod_3 wo fjaod_0 fjaod_2 fjaod_1 fjaod_0 fjaod_2 wi fjaod_3 fjaod_0 fjaod_1 fjaod_2 ejaod_0 com12 fjaod_0 fjaod_3 fjaod_2 ejaod_1 com12 jaoi com12 $.
$}
$( Eliminate a disjunction in a deduction.  (Contributed by Mario Carneiro,
       29-May-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpjaod_0 $f wff ph $.
	fmpjaod_1 $f wff ps $.
	fmpjaod_2 $f wff ch $.
	fmpjaod_3 $f wff th $.
	empjaod_0 $e |- ( ph -> ( ps -> ch ) ) $.
	empjaod_1 $e |- ( ph -> ( th -> ch ) ) $.
	empjaod_2 $e |- ( ph -> ( ps \/ th ) ) $.
	mpjaod $p |- ( ph -> ch ) $= fmpjaod_0 fmpjaod_1 fmpjaod_3 wo fmpjaod_2 empjaod_2 fmpjaod_0 fmpjaod_1 fmpjaod_2 fmpjaod_3 empjaod_0 empjaod_1 jaod mpd $.
$}
$( Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107.  (Contributed by NM, 12-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 21-Jul-2012.) $)
${
	$v ph $.
	$v ps $.
	forel1_0 $f wff ph $.
	forel1_1 $f wff ps $.
	orel1 $p |- ( -. ph -> ( ( ph \/ ps ) -> ps ) ) $= forel1_0 forel1_1 wo forel1_0 wn forel1_1 forel1_0 forel1_1 pm2.53 com12 $.
$}
$( Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107.  (Contributed by NM, 12-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 5-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	forel2_0 $f wff ph $.
	forel2_1 $f wff ps $.
	orel2 $p |- ( -. ph -> ( ( ps \/ ph ) -> ps ) ) $= forel2_0 wn forel2_1 forel2_1 forel2_0 forel2_0 wn forel2_1 idd forel2_0 forel2_1 pm2.21 jaod $.
$}
$( Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96.
     (Contributed by NM, 30-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	folc_0 $f wff ph $.
	folc_1 $f wff ps $.
	olc $p |- ( ph -> ( ps \/ ph ) ) $= folc_0 folc_1 folc_0 folc_0 folc_1 wn ax-1 orrd $.
$}
$( Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 30-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	forc_0 $f wff ph $.
	forc_1 $f wff ps $.
	orc $p |- ( ph -> ( ph \/ ps ) ) $= forc_0 forc_0 forc_1 forc_0 forc_1 pm2.24 orrd $.
$}
$( Axiom *1.4 of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm1.4_0 $f wff ph $.
	fpm1.4_1 $f wff ps $.
	pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $= fpm1.4_0 fpm1.4_1 fpm1.4_0 wo fpm1.4_1 fpm1.4_0 fpm1.4_1 olc fpm1.4_1 fpm1.4_0 orc jaoi $.
$}
$( Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 15-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	forcom_0 $f wff ph $.
	forcom_1 $f wff ps $.
	orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $= forcom_0 forcom_1 wo forcom_1 forcom_0 wo forcom_0 forcom_1 pm1.4 forcom_1 forcom_0 pm1.4 impbii $.
$}
$( Commutation of disjuncts in consequent.  (Contributed by NM,
       2-Dec-2010.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forcomd_0 $f wff ph $.
	forcomd_1 $f wff ps $.
	forcomd_2 $f wff ch $.
	eorcomd_0 $e |- ( ph -> ( ps \/ ch ) ) $.
	orcomd $p |- ( ph -> ( ch \/ ps ) ) $= forcomd_0 forcomd_1 forcomd_2 wo forcomd_2 forcomd_1 wo eorcomd_0 forcomd_1 forcomd_2 orcom sylib $.
$}
$( Commutation of disjuncts in antecedent.  (Contributed by NM,
       2-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forcoms_0 $f wff ph $.
	forcoms_1 $f wff ps $.
	forcoms_2 $f wff ch $.
	eorcoms_0 $e |- ( ( ph \/ ps ) -> ch ) $.
	orcoms $p |- ( ( ps \/ ph ) -> ch ) $= forcoms_1 forcoms_0 wo forcoms_0 forcoms_1 wo forcoms_2 forcoms_1 forcoms_0 pm1.4 eorcoms_0 syl $.
$}
$( Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	forci_0 $f wff ph $.
	forci_1 $f wff ps $.
	eorci_0 $e |- ph $.
	orci $p |- ( ph \/ ps ) $= forci_0 forci_1 forci_0 forci_1 eorci_0 pm2.24i orri $.
$}
$( Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	folci_0 $f wff ph $.
	folci_1 $f wff ps $.
	eolci_0 $e |- ph $.
	olci $p |- ( ps \/ ph ) $= folci_1 folci_0 folci_0 folci_1 wn eolci_0 a1i orri $.
$}
$( Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IR ( ` \/ ` insertion right), see ~ natded .  (Contributed
       by NM, 20-Sep-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forcd_0 $f wff ph $.
	forcd_1 $f wff ps $.
	forcd_2 $f wff ch $.
	eorcd_0 $e |- ( ph -> ps ) $.
	orcd $p |- ( ph -> ( ps \/ ch ) ) $= forcd_0 forcd_1 forcd_1 forcd_2 wo eorcd_0 forcd_1 forcd_2 orc syl $.
$}
$( Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IL ( ` \/ ` insertion left), see ~ natded .  (Contributed by
       NM, 11-Apr-2008.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	folcd_0 $f wff ph $.
	folcd_1 $f wff ps $.
	folcd_2 $f wff ch $.
	eolcd_0 $e |- ( ph -> ps ) $.
	olcd $p |- ( ph -> ( ch \/ ps ) ) $= folcd_0 folcd_1 folcd_2 folcd_0 folcd_1 folcd_2 eolcd_0 orcd orcomd $.
$}
$( Deduction eliminating disjunct. _Notational convention_:  We sometimes
       suffix with "s" the label of an inference that manipulates an
       antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof.  (Contributed by NM, 21-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forcs_0 $f wff ph $.
	forcs_1 $f wff ps $.
	forcs_2 $f wff ch $.
	eorcs_0 $e |- ( ( ph \/ ps ) -> ch ) $.
	orcs $p |- ( ph -> ch ) $= forcs_0 forcs_0 forcs_1 wo forcs_2 forcs_0 forcs_1 orc eorcs_0 syl $.
$}
$( Deduction eliminating disjunct.  (Contributed by NM, 21-Jun-1994.)
       (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	folcs_0 $f wff ph $.
	folcs_1 $f wff ps $.
	folcs_2 $f wff ch $.
	eolcs_0 $e |- ( ( ph \/ ps ) -> ch ) $.
	olcs $p |- ( ps -> ch ) $= folcs_1 folcs_0 folcs_2 folcs_0 folcs_1 folcs_2 eolcs_0 orcoms orcs $.
$}
$( Theorem *2.07 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	fpm2.07_0 $f wff ph $.
	pm2.07 $p |- ( ph -> ( ph \/ ph ) ) $= fpm2.07_0 fpm2.07_0 olc $.
$}
$( Theorem *2.45 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.45_0 $f wff ph $.
	fpm2.45_1 $f wff ps $.
	pm2.45 $p |- ( -. ( ph \/ ps ) -> -. ph ) $= fpm2.45_0 fpm2.45_0 fpm2.45_1 wo fpm2.45_0 fpm2.45_1 orc con3i $.
$}
$( Theorem *2.46 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.46_0 $f wff ph $.
	fpm2.46_1 $f wff ps $.
	pm2.46 $p |- ( -. ( ph \/ ps ) -> -. ps ) $= fpm2.46_1 fpm2.46_0 fpm2.46_1 wo fpm2.46_1 fpm2.46_0 olc con3i $.
$}
$( Theorem *2.47 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.47_0 $f wff ph $.
	fpm2.47_1 $f wff ps $.
	pm2.47 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) ) $= fpm2.47_0 fpm2.47_1 wo wn fpm2.47_0 wn fpm2.47_1 fpm2.47_0 fpm2.47_1 pm2.45 orcd $.
$}
$( Theorem *2.48 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.48_0 $f wff ph $.
	fpm2.48_1 $f wff ps $.
	pm2.48 $p |- ( -. ( ph \/ ps ) -> ( ph \/ -. ps ) ) $= fpm2.48_0 fpm2.48_1 wo wn fpm2.48_1 wn fpm2.48_0 fpm2.48_0 fpm2.48_1 pm2.46 olcd $.
$}
$( Theorem *2.49 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.49_0 $f wff ph $.
	fpm2.49_1 $f wff ps $.
	pm2.49 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) ) $= fpm2.49_0 fpm2.49_1 wo wn fpm2.49_1 wn fpm2.49_0 wn fpm2.49_0 fpm2.49_1 pm2.46 olcd $.
$}
$( Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.67-2_0 $f wff ph $.
	fpm2.67-2_1 $f wff ps $.
	fpm2.67-2_2 $f wff ch $.
	pm2.67-2 $p |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) ) $= fpm2.67-2_0 fpm2.67-2_0 fpm2.67-2_2 wo fpm2.67-2_1 fpm2.67-2_0 fpm2.67-2_2 orc imim1i $.
$}
$( Theorem *2.67 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.67_0 $f wff ph $.
	fpm2.67_1 $f wff ps $.
	pm2.67 $p |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $= fpm2.67_0 fpm2.67_1 fpm2.67_1 pm2.67-2 $.
$}
$( Theorem *2.25 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.25_0 $f wff ph $.
	fpm2.25_1 $f wff ps $.
	pm2.25 $p |- ( ph \/ ( ( ph \/ ps ) -> ps ) ) $= fpm2.25_0 fpm2.25_0 fpm2.25_1 wo fpm2.25_1 wi fpm2.25_0 fpm2.25_1 orel1 orri $.
$}
$( A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 23-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 18-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fbiorf_0 $f wff ph $.
	fbiorf_1 $f wff ps $.
	biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $= fbiorf_0 wn fbiorf_1 fbiorf_0 fbiorf_1 wo fbiorf_1 fbiorf_0 olc fbiorf_0 fbiorf_1 orel1 impbid2 $.
$}
$( A wff is equivalent to its negated disjunction with falsehood.
     (Contributed by NM, 9-Jul-2012.) $)
${
	$v ph $.
	$v ps $.
	fbiortn_0 $f wff ph $.
	fbiortn_1 $f wff ps $.
	biortn $p |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) ) $= fbiortn_0 fbiortn_0 wn wn fbiortn_1 fbiortn_0 wn fbiortn_1 wo wb fbiortn_0 notnot1 fbiortn_0 wn fbiortn_1 biorf syl $.
$}
$( A wff is equivalent to its disjunction with falsehood.  (Contributed by
       NM, 23-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	fbiorfi_0 $f wff ph $.
	fbiorfi_1 $f wff ps $.
	ebiorfi_0 $e |- -. ph $.
	biorfi $p |- ( ps <-> ( ps \/ ph ) ) $= fbiorfi_0 wn fbiorfi_1 fbiorfi_1 fbiorfi_0 wo wb ebiorfi_0 fbiorfi_0 wn fbiorfi_1 fbiorfi_1 fbiorfi_0 wo fbiorfi_1 fbiorfi_0 orc fbiorfi_0 fbiorfi_1 orel2 impbid2 ax-mp $.
$}
$( Theorem *2.621 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.621_0 $f wff ph $.
	fpm2.621_1 $f wff ps $.
	pm2.621 $p |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $= fpm2.621_0 fpm2.621_1 wi fpm2.621_0 fpm2.621_1 fpm2.621_1 fpm2.621_0 fpm2.621_1 wi id fpm2.621_0 fpm2.621_1 wi fpm2.621_1 idd jaod $.
$}
$( Theorem *2.62 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Dec-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm2.62_0 $f wff ph $.
	fpm2.62_1 $f wff ps $.
	pm2.62 $p |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $= fpm2.62_0 fpm2.62_1 wi fpm2.62_0 fpm2.62_1 wo fpm2.62_1 fpm2.62_0 fpm2.62_1 pm2.621 com12 $.
$}
$( Theorem *2.68 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.68_0 $f wff ph $.
	fpm2.68_1 $f wff ps $.
	pm2.68 $p |- ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) $= fpm2.68_0 fpm2.68_1 wi fpm2.68_1 wi fpm2.68_0 fpm2.68_1 fpm2.68_0 fpm2.68_1 fpm2.68_1 jarl orrd $.
$}
$( Logical 'or' expressed in terms of implication only.  Theorem *5.25 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 12-Aug-2004.)  (Proof
     shortened by Wolf Lammen, 20-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	fdfor2_0 $f wff ph $.
	fdfor2_1 $f wff ps $.
	dfor2 $p |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) $= fdfor2_0 fdfor2_1 wo fdfor2_0 fdfor2_1 wi fdfor2_1 wi fdfor2_0 fdfor2_1 pm2.62 fdfor2_0 fdfor2_1 pm2.68 impbii $.
$}
$( Implication in terms of disjunction.  Theorem *4.6 of [WhiteheadRussell]
     p. 120.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	fimor_0 $f wff ph $.
	fimor_1 $f wff ps $.
	imor $p |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) $= fimor_0 fimor_1 wi fimor_0 wn wn fimor_1 wi fimor_0 wn fimor_1 wo fimor_0 fimor_0 wn wn fimor_1 fimor_0 notnot imbi1i fimor_0 wn fimor_1 df-or bitr4i $.
$}
$( Infer disjunction from implication.  (Contributed by NM,
       12-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	fimori_0 $f wff ph $.
	fimori_1 $f wff ps $.
	eimori_0 $e |- ( ph -> ps ) $.
	imori $p |- ( -. ph \/ ps ) $= fimori_0 fimori_1 wi fimori_0 wn fimori_1 wo eimori_0 fimori_0 fimori_1 imor mpbi $.
$}
$( Infer implication from disjunction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	fimorri_0 $f wff ph $.
	fimorri_1 $f wff ps $.
	eimorri_0 $e |- ( -. ph \/ ps ) $.
	imorri $p |- ( ph -> ps ) $= fimorri_0 fimorri_1 wi fimorri_0 wn fimorri_1 wo eimorri_0 fimorri_0 fimorri_1 imor mpbir $.
$}
$( Law of excluded middle, also called the principle of _tertium non datur_.
     Theorem *2.11 of [WhiteheadRussell] p. 101.  It says that something is
     either true or not true; there are no in-between values of truth.  This is
     an essential distinction of our classical logic and is not a theorem of
     intuitionistic logic.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	fexmid_0 $f wff ph $.
	exmid $p |- ( ph \/ -. ph ) $= fexmid_0 fexmid_0 wn fexmid_0 wn id orri $.
$}
$( Law of excluded middle in a context.  (Contributed by Mario Carneiro,
     9-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	fexmidd_0 $f wff ph $.
	fexmidd_1 $f wff ps $.
	exmidd $p |- ( ph -> ( ps \/ -. ps ) ) $= fexmidd_1 fexmidd_1 wn wo fexmidd_0 fexmidd_1 exmid a1i $.
$}
$( Theorem *2.1 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
${
	$v ph $.
	fpm2.1_0 $f wff ph $.
	pm2.1 $p |- ( -. ph \/ ph ) $= fpm2.1_0 fpm2.1_0 fpm2.1_0 id imori $.
$}
$( Theorem *2.13 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	fpm2.13_0 $f wff ph $.
	pm2.13 $p |- ( ph \/ -. -. -. ph ) $= fpm2.13_0 fpm2.13_0 wn wn wn fpm2.13_0 wn notnot1 orri $.
$}
$( Theorem *4.62 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.62_0 $f wff ph $.
	fpm4.62_1 $f wff ps $.
	pm4.62 $p |- ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) $= fpm4.62_0 fpm4.62_1 wn imor $.
$}
$( Theorem *4.66 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.66_0 $f wff ph $.
	fpm4.66_1 $f wff ps $.
	pm4.66 $p |- ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) ) $= fpm4.66_0 fpm4.66_1 wn pm4.64 $.
$}
$( Theorem *4.63 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.63_0 $f wff ph $.
	fpm4.63_1 $f wff ps $.
	pm4.63 $p |- ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) $= fpm4.63_0 fpm4.63_1 wa fpm4.63_0 fpm4.63_1 wn wi wn fpm4.63_0 fpm4.63_1 df-an bicomi $.
$}
$( Express implication in terms of conjunction.  (Contributed by NM,
     9-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	fimnan_0 $f wff ph $.
	fimnan_1 $f wff ps $.
	imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $= fimnan_0 fimnan_1 wa fimnan_0 fimnan_1 wn wi fimnan_0 fimnan_1 df-an con2bii $.
$}
$( Express implication in terms of conjunction.  (Contributed by Mario
       Carneiro, 28-Sep-2015.) $)
${
	$v ph $.
	$v ps $.
	fimnani_0 $f wff ph $.
	fimnani_1 $f wff ps $.
	eimnani_0 $e |- -. ( ph /\ ps ) $.
	imnani $p |- ( ph -> -. ps ) $= fimnani_0 fimnani_1 wn wi fimnani_0 fimnani_1 wa wn eimnani_0 fimnani_0 fimnani_1 imnan mpbir $.
$}
$( Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 30-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	fiman_0 $f wff ph $.
	fiman_1 $f wff ps $.
	iman $p |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) $= fiman_0 fiman_1 wi fiman_0 fiman_1 wn wn wi fiman_0 fiman_1 wn wa wn fiman_1 fiman_1 wn wn fiman_0 fiman_1 notnot imbi2i fiman_0 fiman_1 wn imnan bitri $.
$}
$( Express conjunction in terms of implication.  (Contributed by NM,
     2-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	fannim_0 $f wff ph $.
	fannim_1 $f wff ps $.
	annim $p |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) $= fannim_0 fannim_1 wi fannim_0 fannim_1 wn wa fannim_0 fannim_1 iman con2bii $.
$}
$( Theorem *4.61 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.61_0 $f wff ph $.
	fpm4.61_1 $f wff ps $.
	pm4.61 $p |- ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) ) $= fpm4.61_0 fpm4.61_1 wn wa fpm4.61_0 fpm4.61_1 wi wn fpm4.61_0 fpm4.61_1 annim bicomi $.
$}
$( Theorem *4.65 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.65_0 $f wff ph $.
	fpm4.65_1 $f wff ps $.
	pm4.65 $p |- ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) ) $= fpm4.65_0 wn fpm4.65_1 pm4.61 $.
$}
$( Theorem *4.67 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.67_0 $f wff ph $.
	fpm4.67_1 $f wff ps $.
	pm4.67 $p |- ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) $= fpm4.67_0 wn fpm4.67_1 pm4.63 $.
$}
$( Importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Eric Schmidt, 22-Dec-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimp_0 $f wff ph $.
	fimp_1 $f wff ps $.
	fimp_2 $f wff ch $.
	eimp_0 $e |- ( ph -> ( ps -> ch ) ) $.
	imp $p |- ( ( ph /\ ps ) -> ch ) $= fimp_0 fimp_1 wa fimp_0 fimp_1 wn wi wn fimp_2 fimp_0 fimp_1 df-an fimp_0 fimp_1 fimp_2 eimp_0 impi sylbi $.
$}
$( Importation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimpcom_0 $f wff ph $.
	fimpcom_1 $f wff ps $.
	fimpcom_2 $f wff ch $.
	eimpcom_0 $e |- ( ph -> ( ps -> ch ) ) $.
	impcom $p |- ( ( ps /\ ph ) -> ch ) $= fimpcom_1 fimpcom_0 fimpcom_2 fimpcom_0 fimpcom_1 fimpcom_2 eimpcom_0 com12 imp $.
$}
$( Importation deduction.  (Contributed by NM, 31-Mar-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fimp3a_0 $f wff ph $.
	fimp3a_1 $f wff ps $.
	fimp3a_2 $f wff ch $.
	fimp3a_3 $f wff th $.
	eimp3a_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	imp3a $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= fimp3a_1 fimp3a_2 wa fimp3a_0 fimp3a_3 fimp3a_1 fimp3a_2 fimp3a_0 fimp3a_3 wi fimp3a_0 fimp3a_1 fimp3a_2 fimp3a_3 eimp3a_0 com3l imp com12 $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fimp31_0 $f wff ph $.
	fimp31_1 $f wff ps $.
	fimp31_2 $f wff ch $.
	fimp31_3 $f wff th $.
	eimp31_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $= fimp31_0 fimp31_1 wa fimp31_2 fimp31_3 fimp31_0 fimp31_1 fimp31_2 fimp31_3 wi eimp31_0 imp imp $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fimp32_0 $f wff ph $.
	fimp32_1 $f wff ps $.
	fimp32_2 $f wff ch $.
	fimp32_3 $f wff th $.
	eimp32_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $= fimp32_0 fimp32_1 fimp32_2 wa fimp32_3 fimp32_0 fimp32_1 fimp32_2 fimp32_3 eimp32_0 imp3a imp $.
$}
$( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  A translation of natural deduction
       rule ` -> ` I ( ` -> ` introduction), see ~ natded .  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fex_0 $f wff ph $.
	fex_1 $f wff ps $.
	fex_2 $f wff ch $.
	eex_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	ex $p |- ( ph -> ( ps -> ch ) ) $= fex_0 fex_1 fex_2 fex_0 fex_1 wn wi wn fex_0 fex_1 wa fex_2 fex_0 fex_1 df-an eex_0 sylbir expi $.
$}
$( Exportation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fexpcom_0 $f wff ph $.
	fexpcom_1 $f wff ps $.
	fexpcom_2 $f wff ch $.
	eexpcom_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	expcom $p |- ( ps -> ( ph -> ch ) ) $= fexpcom_0 fexpcom_1 fexpcom_2 fexpcom_0 fexpcom_1 fexpcom_2 eexpcom_0 ex com12 $.
$}
$( Exportation deduction.  (Contributed by NM, 20-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fexp3a_0 $f wff ph $.
	fexp3a_1 $f wff ps $.
	fexp3a_2 $f wff ch $.
	fexp3a_3 $f wff th $.
	eexp3a_0 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	exp3a $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= fexp3a_1 fexp3a_2 fexp3a_0 fexp3a_3 fexp3a_1 fexp3a_2 fexp3a_0 fexp3a_3 wi fexp3a_0 fexp3a_1 fexp3a_2 wa fexp3a_3 eexp3a_0 com12 ex com3r $.
$}
$( A deduction version of exportation, followed by importation.
       (Contributed by NM, 6-Sep-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fexpdimp_0 $f wff ph $.
	fexpdimp_1 $f wff ps $.
	fexpdimp_2 $f wff ch $.
	fexpdimp_3 $f wff th $.
	eexpdimp_0 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $= fexpdimp_0 fexpdimp_1 fexpdimp_2 fexpdimp_3 wi fexpdimp_0 fexpdimp_1 fexpdimp_2 fexpdimp_3 eexpdimp_0 exp3a imp $.
$}
$( Mixed importation/commutation inference.  (Contributed by NM,
       22-Jun-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fimpancom_0 $f wff ph $.
	fimpancom_1 $f wff ps $.
	fimpancom_2 $f wff ch $.
	fimpancom_3 $f wff th $.
	eimpancom_0 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	impancom $p |- ( ( ph /\ ch ) -> ( ps -> th ) ) $= fimpancom_0 fimpancom_2 fimpancom_1 fimpancom_3 wi fimpancom_0 fimpancom_1 fimpancom_2 fimpancom_3 fimpancom_0 fimpancom_1 fimpancom_2 fimpancom_3 wi eimpancom_0 ex com23 imp $.
$}
$( Variant of ~ con3d with importation.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fcon3and_0 $f wff ph $.
	fcon3and_1 $f wff ps $.
	fcon3and_2 $f wff ch $.
	econ3and_0 $e |- ( ph -> ( ps -> ch ) ) $.
	con3and $p |- ( ( ph /\ -. ch ) -> -. ps ) $= fcon3and_0 fcon3and_2 wn fcon3and_1 wn fcon3and_0 fcon3and_1 fcon3and_2 econ3and_0 con3d imp $.
$}
$( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	fpm2.01da_0 $f wff ph $.
	fpm2.01da_1 $f wff ps $.
	epm2.01da_0 $e |- ( ( ph /\ ps ) -> -. ps ) $.
	pm2.01da $p |- ( ph -> -. ps ) $= fpm2.01da_0 fpm2.01da_1 fpm2.01da_0 fpm2.01da_1 fpm2.01da_1 wn epm2.01da_0 ex pm2.01d $.
$}
$( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	fpm2.18da_0 $f wff ph $.
	fpm2.18da_1 $f wff ps $.
	epm2.18da_0 $e |- ( ( ph /\ -. ps ) -> ps ) $.
	pm2.18da $p |- ( ph -> ps ) $= fpm2.18da_0 fpm2.18da_1 fpm2.18da_0 fpm2.18da_1 wn fpm2.18da_1 epm2.18da_0 ex pm2.18d $.
$}
$( Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.3_0 $f wff ph $.
	fpm3.3_1 $f wff ps $.
	fpm3.3_2 $f wff ch $.
	pm3.3 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $= fpm3.3_0 fpm3.3_1 wa fpm3.3_2 wi fpm3.3_0 fpm3.3_1 fpm3.3_2 fpm3.3_0 fpm3.3_1 wa fpm3.3_2 wi id exp3a $.
$}
$( Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.31_0 $f wff ph $.
	fpm3.31_1 $f wff ps $.
	fpm3.31_2 $f wff ch $.
	pm3.31 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $= fpm3.31_0 fpm3.31_1 fpm3.31_2 wi wi fpm3.31_0 fpm3.31_1 fpm3.31_2 fpm3.31_0 fpm3.31_1 fpm3.31_2 wi wi id imp3a $.
$}
$( Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimpexp_0 $f wff ph $.
	fimpexp_1 $f wff ps $.
	fimpexp_2 $f wff ch $.
	impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $= fimpexp_0 fimpexp_1 wa fimpexp_2 wi fimpexp_0 fimpexp_1 fimpexp_2 wi wi fimpexp_0 fimpexp_1 fimpexp_2 pm3.3 fimpexp_0 fimpexp_1 fimpexp_2 pm3.31 impbii $.
$}
$( Join antecedents with conjunction.  Theorem *3.2 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 12-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm3.2_0 $f wff ph $.
	fpm3.2_1 $f wff ps $.
	pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $= fpm3.2_0 fpm3.2_1 fpm3.2_0 fpm3.2_1 wa fpm3.2_0 fpm3.2_1 wa id ex $.
$}
$( Join antecedents with conjunction.  Theorem *3.21 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	fpm3.21_0 $f wff ph $.
	fpm3.21_1 $f wff ps $.
	pm3.21 $p |- ( ph -> ( ps -> ( ps /\ ph ) ) ) $= fpm3.21_1 fpm3.21_0 fpm3.21_1 fpm3.21_0 wa fpm3.21_1 fpm3.21_0 pm3.2 com12 $.
$}
$( Theorem *3.22 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm3.22_0 $f wff ph $.
	fpm3.22_1 $f wff ps $.
	pm3.22 $p |- ( ( ph /\ ps ) -> ( ps /\ ph ) ) $= fpm3.22_0 fpm3.22_1 fpm3.22_1 fpm3.22_0 wa fpm3.22_0 fpm3.22_1 pm3.21 imp $.
$}
$( Commutative law for conjunction.  Theorem *4.3 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 25-Jun-1998.)  (Proof shortened by Wolf
     Lammen, 4-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fancom_0 $f wff ph $.
	fancom_1 $f wff ps $.
	ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $= fancom_0 fancom_1 wa fancom_1 fancom_0 wa fancom_0 fancom_1 pm3.22 fancom_1 fancom_0 pm3.22 impbii $.
$}
$( Commutation of conjuncts in consequent.  (Contributed by Jeff Hankins,
       14-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fancomd_0 $f wff ph $.
	fancomd_1 $f wff ps $.
	fancomd_2 $f wff ch $.
	eancomd_0 $e |- ( ph -> ( ps /\ ch ) ) $.
	ancomd $p |- ( ph -> ( ch /\ ps ) ) $= fancomd_0 fancomd_1 fancomd_2 wa fancomd_2 fancomd_1 wa eancomd_0 fancomd_1 fancomd_2 ancom sylib $.
$}
$( Inference commuting conjunction in antecedent.  (Contributed by NM,
       21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fancoms_0 $f wff ph $.
	fancoms_1 $f wff ps $.
	fancoms_2 $f wff ch $.
	eancoms_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	ancoms $p |- ( ( ps /\ ph ) -> ch ) $= fancoms_1 fancoms_0 fancoms_2 fancoms_0 fancoms_1 fancoms_2 eancoms_0 expcom imp $.
$}
$( Deduction commuting conjunction in antecedent.  (Contributed by NM,
       12-Dec-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fancomsd_0 $f wff ph $.
	fancomsd_1 $f wff ps $.
	fancomsd_2 $f wff ch $.
	fancomsd_3 $f wff th $.
	eancomsd_0 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $= fancomsd_2 fancomsd_1 wa fancomsd_1 fancomsd_2 wa fancomsd_0 fancomsd_3 fancomsd_2 fancomsd_1 ancom eancomsd_0 syl5bi $.
$}
$( Infer conjunction of premises.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	fpm3.2i_0 $f wff ph $.
	fpm3.2i_1 $f wff ps $.
	epm3.2i_0 $e |- ph $.
	epm3.2i_1 $e |- ps $.
	pm3.2i $p |- ( ph /\ ps ) $= fpm3.2i_0 fpm3.2i_1 fpm3.2i_0 fpm3.2i_1 wa epm3.2i_0 epm3.2i_1 fpm3.2i_0 fpm3.2i_1 pm3.2 mp2 $.
$}
$( Nested conjunction of antecedents.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.43i_0 $f wff ph $.
	fpm3.43i_1 $f wff ps $.
	fpm3.43i_2 $f wff ch $.
	pm3.43i $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $= fpm3.43i_1 fpm3.43i_2 fpm3.43i_1 fpm3.43i_2 wa fpm3.43i_0 fpm3.43i_1 fpm3.43i_2 pm3.2 imim3i $.
$}
$( Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fsimpl_0 $f wff ph $.
	fsimpl_1 $f wff ps $.
	simpl $p |- ( ( ph /\ ps ) -> ph ) $= fsimpl_0 fsimpl_1 fsimpl_0 fsimpl_0 fsimpl_1 ax-1 imp $.
$}
$( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	fsimpli_0 $f wff ph $.
	fsimpli_1 $f wff ps $.
	esimpli_0 $e |- ( ph /\ ps ) $.
	simpli $p |- ph $= fsimpli_0 fsimpli_1 wa fsimpli_0 esimpli_0 fsimpli_0 fsimpli_1 simpl ax-mp $.
$}
$( Deduction eliminating a conjunct.  A translation of natural deduction
       rule ` /\ ` EL ( ` /\ ` elimination left), see ~ natded .  (Contributed
       by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimpld_0 $f wff ph $.
	fsimpld_1 $f wff ps $.
	fsimpld_2 $f wff ch $.
	esimpld_0 $e |- ( ph -> ( ps /\ ch ) ) $.
	simpld $p |- ( ph -> ps ) $= fsimpld_0 fsimpld_1 fsimpld_2 wa fsimpld_1 esimpld_0 fsimpld_1 fsimpld_2 simpl syl $.
$}
$( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimplbi_0 $f wff ph $.
	fsimplbi_1 $f wff ps $.
	fsimplbi_2 $f wff ch $.
	esimplbi_0 $e |- ( ph <-> ( ps /\ ch ) ) $.
	simplbi $p |- ( ph -> ps ) $= fsimplbi_0 fsimplbi_1 fsimplbi_2 fsimplbi_0 fsimplbi_1 fsimplbi_2 wa esimplbi_0 biimpi simpld $.
$}
$( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fsimpr_0 $f wff ph $.
	fsimpr_1 $f wff ps $.
	simpr $p |- ( ( ph /\ ps ) -> ps ) $= fsimpr_0 fsimpr_1 fsimpr_1 fsimpr_0 fsimpr_1 idd imp $.
$}
$( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	fsimpri_0 $f wff ph $.
	fsimpri_1 $f wff ps $.
	esimpri_0 $e |- ( ph /\ ps ) $.
	simpri $p |- ps $= fsimpri_0 fsimpri_1 wa fsimpri_1 esimpri_0 fsimpri_0 fsimpri_1 simpr ax-mp $.
$}
$( Deduction eliminating a conjunct.  (Contributed by NM, 5-Aug-1993.)  A
       translation of natural deduction rule ` /\ ` ER ( ` /\ ` elimination
       right), see ~ natded .  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimprd_0 $f wff ph $.
	fsimprd_1 $f wff ps $.
	fsimprd_2 $f wff ch $.
	esimprd_0 $e |- ( ph -> ( ps /\ ch ) ) $.
	simprd $p |- ( ph -> ch ) $= fsimprd_0 fsimprd_2 fsimprd_1 fsimprd_0 fsimprd_1 fsimprd_2 esimprd_0 ancomd simpld $.
$}
$( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimprbi_0 $f wff ph $.
	fsimprbi_1 $f wff ps $.
	fsimprbi_2 $f wff ch $.
	esimprbi_0 $e |- ( ph <-> ( ps /\ ch ) ) $.
	simprbi $p |- ( ph -> ch ) $= fsimprbi_0 fsimprbi_1 fsimprbi_2 fsimprbi_0 fsimprbi_1 fsimprbi_2 wa esimprbi_0 biimpi simprd $.
$}
$( Inference adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 30-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fadantr_0 $f wff ph $.
	fadantr_1 $f wff ps $.
	fadantr_2 $f wff ch $.
	eadantr_0 $e |- ( ph -> ps ) $.
	adantr $p |- ( ( ph /\ ch ) -> ps ) $= fadantr_0 fadantr_2 fadantr_1 fadantr_0 fadantr_1 fadantr_2 eadantr_0 a1d imp $.
$}
$( Inference adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 30-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fadantl_0 $f wff ph $.
	fadantl_1 $f wff ps $.
	fadantl_2 $f wff ch $.
	eadantl_0 $e |- ( ph -> ps ) $.
	adantl $p |- ( ( ch /\ ph ) -> ps ) $= fadantl_0 fadantl_2 fadantl_1 fadantl_0 fadantl_1 fadantl_2 eadantl_0 adantr ancoms $.
$}
$( Deduction adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 4-May-1994.)  (Proof shortened by Wolf Lammen, 20-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fadantld_0 $f wff ph $.
	fadantld_1 $f wff ps $.
	fadantld_2 $f wff ch $.
	fadantld_3 $f wff th $.
	eadantld_0 $e |- ( ph -> ( ps -> ch ) ) $.
	adantld $p |- ( ph -> ( ( th /\ ps ) -> ch ) ) $= fadantld_3 fadantld_1 wa fadantld_1 fadantld_0 fadantld_2 fadantld_3 fadantld_1 simpr eadantld_0 syl5 $.
$}
$( Deduction adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 4-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fadantrd_0 $f wff ph $.
	fadantrd_1 $f wff ps $.
	fadantrd_2 $f wff ch $.
	fadantrd_3 $f wff th $.
	eadantrd_0 $e |- ( ph -> ( ps -> ch ) ) $.
	adantrd $p |- ( ph -> ( ( ps /\ th ) -> ch ) ) $= fadantrd_1 fadantrd_3 wa fadantrd_1 fadantrd_0 fadantrd_2 fadantrd_1 fadantrd_3 simpl eadantrd_0 syl5 $.
$}
$( Modus ponens conjoining dissimilar antecedents.  (Contributed by NM,
       1-Feb-2008.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpan9_0 $f wff ph $.
	fmpan9_1 $f wff ps $.
	fmpan9_2 $f wff ch $.
	fmpan9_3 $f wff th $.
	empan9_0 $e |- ( ph -> ps ) $.
	empan9_1 $e |- ( ch -> ( ps -> th ) ) $.
	mpan9 $p |- ( ( ph /\ ch ) -> th ) $= fmpan9_2 fmpan9_0 fmpan9_3 fmpan9_0 fmpan9_1 fmpan9_2 fmpan9_3 empan9_0 empan9_1 syl5 impcom $.
$}
$( A syllogism deduction with conjoined antecedents.  (Contributed by NM,
       24-Feb-2005.)  (Proof shortened by Wolf Lammen, 6-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsyldan_0 $f wff ph $.
	fsyldan_1 $f wff ps $.
	fsyldan_2 $f wff ch $.
	fsyldan_3 $f wff th $.
	esyldan_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	esyldan_1 $e |- ( ( ph /\ ch ) -> th ) $.
	syldan $p |- ( ( ph /\ ps ) -> th ) $= fsyldan_2 fsyldan_0 fsyldan_1 wa fsyldan_3 esyldan_0 fsyldan_2 fsyldan_0 fsyldan_3 fsyldan_1 fsyldan_0 fsyldan_2 fsyldan_3 esyldan_1 expcom adantrd mpcom $.
$}
$( A syllogism inference.  (Contributed by NM, 21-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylan_0 $f wff ph $.
	fsylan_1 $f wff ps $.
	fsylan_2 $f wff ch $.
	fsylan_3 $f wff th $.
	esylan_0 $e |- ( ph -> ps ) $.
	esylan_1 $e |- ( ( ps /\ ch ) -> th ) $.
	sylan $p |- ( ( ph /\ ch ) -> th ) $= fsylan_0 fsylan_1 fsylan_2 fsylan_3 esylan_0 fsylan_1 fsylan_2 fsylan_3 esylan_1 expcom mpan9 $.
$}
$( A syllogism inference.  (Contributed by NM, 18-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylanb_0 $f wff ph $.
	fsylanb_1 $f wff ps $.
	fsylanb_2 $f wff ch $.
	fsylanb_3 $f wff th $.
	esylanb_0 $e |- ( ph <-> ps ) $.
	esylanb_1 $e |- ( ( ps /\ ch ) -> th ) $.
	sylanb $p |- ( ( ph /\ ch ) -> th ) $= fsylanb_0 fsylanb_1 fsylanb_2 fsylanb_3 fsylanb_0 fsylanb_1 esylanb_0 biimpi esylanb_1 sylan $.
$}
$( A syllogism inference.  (Contributed by NM, 18-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylanbr_0 $f wff ph $.
	fsylanbr_1 $f wff ps $.
	fsylanbr_2 $f wff ch $.
	fsylanbr_3 $f wff th $.
	esylanbr_0 $e |- ( ps <-> ph ) $.
	esylanbr_1 $e |- ( ( ps /\ ch ) -> th ) $.
	sylanbr $p |- ( ( ph /\ ch ) -> th ) $= fsylanbr_0 fsylanbr_1 fsylanbr_2 fsylanbr_3 fsylanbr_1 fsylanbr_0 esylanbr_0 biimpri esylanbr_1 sylan $.
$}
$( A syllogism inference.  (Contributed by NM, 21-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylan2_0 $f wff ph $.
	fsylan2_1 $f wff ps $.
	fsylan2_2 $f wff ch $.
	fsylan2_3 $f wff th $.
	esylan2_0 $e |- ( ph -> ch ) $.
	esylan2_1 $e |- ( ( ps /\ ch ) -> th ) $.
	sylan2 $p |- ( ( ps /\ ph ) -> th ) $= fsylan2_1 fsylan2_0 fsylan2_2 fsylan2_3 fsylan2_0 fsylan2_2 fsylan2_1 esylan2_0 adantl esylan2_1 syldan $.
$}
$( A syllogism inference.  (Contributed by NM, 21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylan2b_0 $f wff ph $.
	fsylan2b_1 $f wff ps $.
	fsylan2b_2 $f wff ch $.
	fsylan2b_3 $f wff th $.
	esylan2b_0 $e |- ( ph <-> ch ) $.
	esylan2b_1 $e |- ( ( ps /\ ch ) -> th ) $.
	sylan2b $p |- ( ( ps /\ ph ) -> th ) $= fsylan2b_0 fsylan2b_1 fsylan2b_2 fsylan2b_3 fsylan2b_0 fsylan2b_2 esylan2b_0 biimpi esylan2b_1 sylan2 $.
$}
$( A syllogism inference.  (Contributed by NM, 21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylan2br_0 $f wff ph $.
	fsylan2br_1 $f wff ps $.
	fsylan2br_2 $f wff ch $.
	fsylan2br_3 $f wff th $.
	esylan2br_0 $e |- ( ch <-> ph ) $.
	esylan2br_1 $e |- ( ( ps /\ ch ) -> th ) $.
	sylan2br $p |- ( ( ps /\ ph ) -> th ) $= fsylan2br_0 fsylan2br_1 fsylan2br_2 fsylan2br_3 fsylan2br_2 fsylan2br_0 esylan2br_0 biimpri esylan2br_1 sylan2 $.
$}
$( A double syllogism inference.  (Contributed by NM, 31-Jan-1997.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl2an_0 $f wff ph $.
	fsyl2an_1 $f wff ps $.
	fsyl2an_2 $f wff ch $.
	fsyl2an_3 $f wff th $.
	fsyl2an_4 $f wff ta $.
	esyl2an_0 $e |- ( ph -> ps ) $.
	esyl2an_1 $e |- ( ta -> ch ) $.
	esyl2an_2 $e |- ( ( ps /\ ch ) -> th ) $.
	syl2an $p |- ( ( ph /\ ta ) -> th ) $= fsyl2an_4 fsyl2an_0 fsyl2an_2 fsyl2an_3 esyl2an_1 fsyl2an_0 fsyl2an_1 fsyl2an_2 fsyl2an_3 esyl2an_0 esyl2an_2 sylan sylan2 $.
$}
$( A double syllogism inference.  (Contributed by NM, 17-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl2anr_0 $f wff ph $.
	fsyl2anr_1 $f wff ps $.
	fsyl2anr_2 $f wff ch $.
	fsyl2anr_3 $f wff th $.
	fsyl2anr_4 $f wff ta $.
	esyl2anr_0 $e |- ( ph -> ps ) $.
	esyl2anr_1 $e |- ( ta -> ch ) $.
	esyl2anr_2 $e |- ( ( ps /\ ch ) -> th ) $.
	syl2anr $p |- ( ( ta /\ ph ) -> th ) $= fsyl2anr_0 fsyl2anr_4 fsyl2anr_3 fsyl2anr_0 fsyl2anr_1 fsyl2anr_2 fsyl2anr_3 fsyl2anr_4 esyl2anr_0 esyl2anr_1 esyl2anr_2 syl2an ancoms $.
$}
$( A double syllogism inference.  (Contributed by NM, 29-Jul-1999.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl2anb_0 $f wff ph $.
	fsyl2anb_1 $f wff ps $.
	fsyl2anb_2 $f wff ch $.
	fsyl2anb_3 $f wff th $.
	fsyl2anb_4 $f wff ta $.
	esyl2anb_0 $e |- ( ph <-> ps ) $.
	esyl2anb_1 $e |- ( ta <-> ch ) $.
	esyl2anb_2 $e |- ( ( ps /\ ch ) -> th ) $.
	syl2anb $p |- ( ( ph /\ ta ) -> th ) $= fsyl2anb_4 fsyl2anb_0 fsyl2anb_2 fsyl2anb_3 esyl2anb_1 fsyl2anb_0 fsyl2anb_1 fsyl2anb_2 fsyl2anb_3 esyl2anb_0 esyl2anb_2 sylanb sylan2b $.
$}
$( A double syllogism inference.  (Contributed by NM, 29-Jul-1999.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl2anbr_0 $f wff ph $.
	fsyl2anbr_1 $f wff ps $.
	fsyl2anbr_2 $f wff ch $.
	fsyl2anbr_3 $f wff th $.
	fsyl2anbr_4 $f wff ta $.
	esyl2anbr_0 $e |- ( ps <-> ph ) $.
	esyl2anbr_1 $e |- ( ch <-> ta ) $.
	esyl2anbr_2 $e |- ( ( ps /\ ch ) -> th ) $.
	syl2anbr $p |- ( ( ph /\ ta ) -> th ) $= fsyl2anbr_4 fsyl2anbr_0 fsyl2anbr_2 fsyl2anbr_3 esyl2anbr_1 fsyl2anbr_0 fsyl2anbr_1 fsyl2anbr_2 fsyl2anbr_3 esyl2anbr_0 esyl2anbr_2 sylanbr sylan2br $.
$}
$( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyland_0 $f wff ph $.
	fsyland_1 $f wff ps $.
	fsyland_2 $f wff ch $.
	fsyland_3 $f wff th $.
	fsyland_4 $f wff ta $.
	esyland_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyland_1 $e |- ( ph -> ( ( ch /\ th ) -> ta ) ) $.
	syland $p |- ( ph -> ( ( ps /\ th ) -> ta ) ) $= fsyland_0 fsyland_1 fsyland_3 fsyland_4 fsyland_0 fsyland_1 fsyland_2 fsyland_3 fsyland_4 wi esyland_0 fsyland_0 fsyland_2 fsyland_3 fsyland_4 esyland_1 exp3a syld imp3a $.
$}
$( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylan2d_0 $f wff ph $.
	fsylan2d_1 $f wff ps $.
	fsylan2d_2 $f wff ch $.
	fsylan2d_3 $f wff th $.
	fsylan2d_4 $f wff ta $.
	esylan2d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esylan2d_1 $e |- ( ph -> ( ( th /\ ch ) -> ta ) ) $.
	sylan2d $p |- ( ph -> ( ( th /\ ps ) -> ta ) ) $= fsylan2d_0 fsylan2d_1 fsylan2d_3 fsylan2d_4 fsylan2d_0 fsylan2d_1 fsylan2d_2 fsylan2d_3 fsylan2d_4 esylan2d_0 fsylan2d_0 fsylan2d_3 fsylan2d_2 fsylan2d_4 esylan2d_1 ancomsd syland ancomsd $.
$}
$( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl2and_0 $f wff ph $.
	fsyl2and_1 $f wff ps $.
	fsyl2and_2 $f wff ch $.
	fsyl2and_3 $f wff th $.
	fsyl2and_4 $f wff ta $.
	fsyl2and_5 $f wff et $.
	esyl2and_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl2and_1 $e |- ( ph -> ( th -> ta ) ) $.
	esyl2and_2 $e |- ( ph -> ( ( ch /\ ta ) -> et ) ) $.
	syl2and $p |- ( ph -> ( ( ps /\ th ) -> et ) ) $= fsyl2and_0 fsyl2and_1 fsyl2and_2 fsyl2and_3 fsyl2and_5 esyl2and_0 fsyl2and_0 fsyl2and_3 fsyl2and_4 fsyl2and_2 fsyl2and_5 esyl2and_1 esyl2and_2 sylan2d syland $.
$}
$( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbiimpa_0 $f wff ph $.
	fbiimpa_1 $f wff ps $.
	fbiimpa_2 $f wff ch $.
	ebiimpa_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	biimpa $p |- ( ( ph /\ ps ) -> ch ) $= fbiimpa_0 fbiimpa_1 fbiimpa_2 fbiimpa_0 fbiimpa_1 fbiimpa_2 ebiimpa_0 biimpd imp $.
$}
$( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbiimpar_0 $f wff ph $.
	fbiimpar_1 $f wff ps $.
	fbiimpar_2 $f wff ch $.
	ebiimpar_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	biimpar $p |- ( ( ph /\ ch ) -> ps ) $= fbiimpar_0 fbiimpar_2 fbiimpar_1 fbiimpar_0 fbiimpar_1 fbiimpar_2 ebiimpar_0 biimprd imp $.
$}
$( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbiimpac_0 $f wff ph $.
	fbiimpac_1 $f wff ps $.
	fbiimpac_2 $f wff ch $.
	ebiimpac_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	biimpac $p |- ( ( ps /\ ph ) -> ch ) $= fbiimpac_1 fbiimpac_0 fbiimpac_2 fbiimpac_0 fbiimpac_1 fbiimpac_2 ebiimpac_0 biimpcd imp $.
$}
$( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbiimparc_0 $f wff ph $.
	fbiimparc_1 $f wff ps $.
	fbiimparc_2 $f wff ch $.
	ebiimparc_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	biimparc $p |- ( ( ch /\ ph ) -> ps ) $= fbiimparc_2 fbiimparc_0 fbiimparc_1 fbiimparc_0 fbiimparc_1 fbiimparc_2 ebiimparc_0 biimprcd imp $.
$}
$( Negated conjunction in terms of disjunction (De Morgan's law).  Theorem
     *4.51 of [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
${
	$v ph $.
	$v ps $.
	fianor_0 $f wff ph $.
	fianor_1 $f wff ps $.
	ianor $p |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) $= fianor_0 fianor_1 wa wn fianor_0 fianor_1 wn wi fianor_0 wn fianor_1 wn wo fianor_0 fianor_1 imnan fianor_0 fianor_1 pm4.62 bitr3i $.
$}
$( Conjunction in terms of disjunction (De Morgan's law).  Theorem *4.5 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 3-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fanor_0 $f wff ph $.
	fanor_1 $f wff ps $.
	anor $p |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) $= fanor_0 wn fanor_1 wn wo fanor_0 fanor_1 wa fanor_0 fanor_1 wa wn fanor_0 wn fanor_1 wn wo fanor_0 fanor_1 ianor bicomi con2bii $.
$}
$( Negated disjunction in terms of conjunction (De Morgan's law).  Compare
     Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	fioran_0 $f wff ph $.
	fioran_1 $f wff ps $.
	ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $= fioran_0 wn fioran_1 wi fioran_0 wn fioran_1 wn wa fioran_0 fioran_1 wo fioran_0 fioran_1 pm4.65 fioran_0 fioran_1 pm4.64 xchnxbi $.
$}
$( Theorem *4.52 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm4.52_0 $f wff ph $.
	fpm4.52_1 $f wff ps $.
	pm4.52 $p |- ( ( ph /\ -. ps ) <-> -. ( -. ph \/ ps ) ) $= fpm4.52_0 fpm4.52_1 wn wa fpm4.52_0 fpm4.52_1 wi fpm4.52_0 wn fpm4.52_1 wo fpm4.52_0 fpm4.52_1 annim fpm4.52_0 fpm4.52_1 imor xchbinx $.
$}
$( Theorem *4.53 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.53_0 $f wff ph $.
	fpm4.53_1 $f wff ps $.
	pm4.53 $p |- ( -. ( ph /\ -. ps ) <-> ( -. ph \/ ps ) ) $= fpm4.53_0 wn fpm4.53_1 wo fpm4.53_0 fpm4.53_1 wn wa wn fpm4.53_0 fpm4.53_1 wn wa fpm4.53_0 wn fpm4.53_1 wo fpm4.53_0 fpm4.53_1 pm4.52 con2bii bicomi $.
$}
$( Theorem *4.54 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm4.54_0 $f wff ph $.
	fpm4.54_1 $f wff ps $.
	pm4.54 $p |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $= fpm4.54_0 wn fpm4.54_1 wa fpm4.54_0 wn fpm4.54_1 wn wi fpm4.54_0 fpm4.54_1 wn wo fpm4.54_0 wn fpm4.54_1 df-an fpm4.54_0 fpm4.54_1 pm4.66 xchbinx $.
$}
$( Theorem *4.55 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.55_0 $f wff ph $.
	fpm4.55_1 $f wff ps $.
	pm4.55 $p |- ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) ) $= fpm4.55_0 fpm4.55_1 wn wo fpm4.55_0 wn fpm4.55_1 wa wn fpm4.55_0 wn fpm4.55_1 wa fpm4.55_0 fpm4.55_1 wn wo fpm4.55_0 fpm4.55_1 pm4.54 con2bii bicomi $.
$}
$( Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.56_0 $f wff ph $.
	fpm4.56_1 $f wff ps $.
	pm4.56 $p |- ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) ) $= fpm4.56_0 fpm4.56_1 wo wn fpm4.56_0 wn fpm4.56_1 wn wa fpm4.56_0 fpm4.56_1 ioran bicomi $.
$}
$( Disjunction in terms of conjunction (De Morgan's law).  Compare Theorem
     *4.57 of [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	foran_0 $f wff ph $.
	foran_1 $f wff ps $.
	oran $p |- ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) ) $= foran_0 wn foran_1 wn wa foran_0 foran_1 wo foran_0 foran_1 pm4.56 con2bii $.
$}
$( Theorem *4.57 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.57_0 $f wff ph $.
	fpm4.57_1 $f wff ps $.
	pm4.57 $p |- ( -. ( -. ph /\ -. ps ) <-> ( ph \/ ps ) ) $= fpm4.57_0 fpm4.57_1 wo fpm4.57_0 wn fpm4.57_1 wn wa wn fpm4.57_0 fpm4.57_1 oran bicomi $.
$}
$( Theorem *3.1 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm3.1_0 $f wff ph $.
	fpm3.1_1 $f wff ps $.
	pm3.1 $p |- ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) ) $= fpm3.1_0 fpm3.1_1 wa fpm3.1_0 wn fpm3.1_1 wn wo wn fpm3.1_0 fpm3.1_1 anor biimpi $.
$}
$( Theorem *3.11 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm3.11_0 $f wff ph $.
	fpm3.11_1 $f wff ps $.
	pm3.11 $p |- ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) ) $= fpm3.11_0 fpm3.11_1 wa fpm3.11_0 wn fpm3.11_1 wn wo wn fpm3.11_0 fpm3.11_1 anor biimpri $.
$}
$( Theorem *3.12 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm3.12_0 $f wff ph $.
	fpm3.12_1 $f wff ps $.
	pm3.12 $p |- ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) $= fpm3.12_0 wn fpm3.12_1 wn wo fpm3.12_0 fpm3.12_1 wa fpm3.12_0 fpm3.12_1 pm3.11 orri $.
$}
$( Theorem *3.13 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm3.13_0 $f wff ph $.
	fpm3.13_1 $f wff ps $.
	pm3.13 $p |- ( -. ( ph /\ ps ) -> ( -. ph \/ -. ps ) ) $= fpm3.13_0 wn fpm3.13_1 wn wo fpm3.13_0 fpm3.13_1 wa fpm3.13_0 fpm3.13_1 pm3.11 con1i $.
$}
$( Theorem *3.14 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm3.14_0 $f wff ph $.
	fpm3.14_1 $f wff ps $.
	pm3.14 $p |- ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) ) $= fpm3.14_0 fpm3.14_1 wa fpm3.14_0 wn fpm3.14_1 wn wo fpm3.14_0 fpm3.14_1 pm3.1 con2i $.
$}
$( Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Mar-1994.) $)
${
	$v ph $.
	$v ps $.
	fiba_0 $f wff ph $.
	fiba_1 $f wff ps $.
	iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $= fiba_0 fiba_1 fiba_1 fiba_0 wa fiba_0 fiba_1 pm3.21 fiba_1 fiba_0 simpl impbid1 $.
$}
$( Introduction of antecedent as conjunct.  (Contributed by NM,
     5-Dec-1995.) $)
${
	$v ph $.
	$v ps $.
	fibar_0 $f wff ph $.
	fibar_1 $f wff ps $.
	ibar $p |- ( ph -> ( ps <-> ( ph /\ ps ) ) ) $= fibar_0 fibar_1 fibar_0 fibar_1 wa fibar_0 fibar_1 pm3.2 fibar_0 fibar_1 simpr impbid1 $.
$}
$( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	fbiantru_0 $f wff ph $.
	fbiantru_1 $f wff ps $.
	ebiantru_0 $e |- ph $.
	biantru $p |- ( ps <-> ( ps /\ ph ) ) $= fbiantru_0 fbiantru_1 fbiantru_1 fbiantru_0 wa wb ebiantru_0 fbiantru_0 fbiantru_1 iba ax-mp $.
$}
$( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       3-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	fbiantrur_0 $f wff ph $.
	fbiantrur_1 $f wff ps $.
	ebiantrur_0 $e |- ph $.
	biantrur $p |- ( ps <-> ( ph /\ ps ) ) $= fbiantrur_0 fbiantrur_1 fbiantrur_0 fbiantrur_1 wa wb ebiantrur_0 fbiantrur_0 fbiantrur_1 ibar ax-mp $.
$}
$( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       2-Aug-1994.)  (Proof shortened by Wolf Lammen, 23-Oct-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbiantrud_0 $f wff ph $.
	fbiantrud_1 $f wff ps $.
	fbiantrud_2 $f wff ch $.
	ebiantrud_0 $e |- ( ph -> ps ) $.
	biantrud $p |- ( ph -> ( ch <-> ( ch /\ ps ) ) ) $= fbiantrud_0 fbiantrud_1 fbiantrud_2 fbiantrud_2 fbiantrud_1 wa wb ebiantrud_0 fbiantrud_1 fbiantrud_2 iba syl $.
$}
$( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       1-May-1995.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbiantrurd_0 $f wff ph $.
	fbiantrurd_1 $f wff ps $.
	fbiantrurd_2 $f wff ch $.
	ebiantrurd_0 $e |- ( ph -> ps ) $.
	biantrurd $p |- ( ph -> ( ch <-> ( ps /\ ch ) ) ) $= fbiantrurd_0 fbiantrurd_1 fbiantrurd_2 fbiantrurd_1 fbiantrurd_2 wa wb ebiantrurd_0 fbiantrurd_1 fbiantrurd_2 ibar syl $.
$}
$( Inference conjoining and disjoining the antecedents of two
       implications.  (Contributed by NM, 30-Sep-1999.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fjaao_0 $f wff ph $.
	fjaao_1 $f wff ps $.
	fjaao_2 $f wff ch $.
	fjaao_3 $f wff th $.
	fjaao_4 $f wff ta $.
	ejaao_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ejaao_1 $e |- ( th -> ( ta -> ch ) ) $.
	jaao $p |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) ) $= fjaao_0 fjaao_3 wa fjaao_1 fjaao_2 fjaao_4 fjaao_0 fjaao_1 fjaao_2 wi fjaao_3 ejaao_0 adantr fjaao_3 fjaao_4 fjaao_2 wi fjaao_0 ejaao_1 adantl jaod $.
$}
$( Inference disjoining and conjoining the antecedents of two
       implications.  (Contributed by Stefan Allan, 1-Nov-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fjaoa_0 $f wff ph $.
	fjaoa_1 $f wff ps $.
	fjaoa_2 $f wff ch $.
	fjaoa_3 $f wff th $.
	fjaoa_4 $f wff ta $.
	ejaoa_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ejaoa_1 $e |- ( th -> ( ta -> ch ) ) $.
	jaoa $p |- ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) ) $= fjaoa_0 fjaoa_1 fjaoa_4 wa fjaoa_2 wi fjaoa_3 fjaoa_0 fjaoa_1 fjaoa_2 fjaoa_4 ejaoa_0 adantrd fjaoa_3 fjaoa_4 fjaoa_2 fjaoa_1 ejaoa_1 adantld jaoi $.
$}
$( Theorem *3.44 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.44_0 $f wff ph $.
	fpm3.44_1 $f wff ps $.
	fpm3.44_2 $f wff ch $.
	pm3.44 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) -> ( ( ps \/ ch ) -> ph ) ) $= fpm3.44_1 fpm3.44_0 wi fpm3.44_1 fpm3.44_0 fpm3.44_2 fpm3.44_0 wi fpm3.44_2 fpm3.44_1 fpm3.44_0 wi id fpm3.44_2 fpm3.44_0 wi id jaao $.
$}
$( Disjunction of antecedents.  Compare Theorem *3.44 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 5-Apr-1994.)  (Proof shortened by Wolf
     Lammen, 4-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjao_0 $f wff ph $.
	fjao_1 $f wff ps $.
	fjao_2 $f wff ch $.
	jao $p |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) ) $= fjao_0 fjao_1 wi fjao_2 fjao_1 wi fjao_0 fjao_2 wo fjao_1 wi fjao_1 fjao_0 fjao_2 pm3.44 ex $.
$}
$( Axiom *1.2 of [WhiteheadRussell] p. 96, which they call "Taut".
     (Contributed by NM, 3-Jan-2005.) $)
${
	$v ph $.
	fpm1.2_0 $f wff ph $.
	pm1.2 $p |- ( ( ph \/ ph ) -> ph ) $= fpm1.2_0 fpm1.2_0 fpm1.2_0 fpm1.2_0 id fpm1.2_0 id jaoi $.
$}
$( Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 16-Apr-2011.)  (Proof shortened by Wolf Lammen, 10-Mar-2013.) $)
${
	$v ph $.
	foridm_0 $f wff ph $.
	oridm $p |- ( ( ph \/ ph ) <-> ph ) $= foridm_0 foridm_0 wo foridm_0 foridm_0 pm1.2 foridm_0 pm2.07 impbii $.
$}
$( Theorem *4.25 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	fpm4.25_0 $f wff ph $.
	pm4.25 $p |- ( ph <-> ( ph \/ ph ) ) $= fpm4.25_0 fpm4.25_0 wo fpm4.25_0 fpm4.25_0 oridm bicomi $.
$}
$( Disjoin antecedents and consequents of two premises.  (Contributed by
       NM, 6-Jun-1994.)  (Proof shortened by Wolf Lammen, 25-Jul-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	forim12i_0 $f wff ph $.
	forim12i_1 $f wff ps $.
	forim12i_2 $f wff ch $.
	forim12i_3 $f wff th $.
	eorim12i_0 $e |- ( ph -> ps ) $.
	eorim12i_1 $e |- ( ch -> th ) $.
	orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $= forim12i_0 forim12i_1 forim12i_3 wo forim12i_2 forim12i_0 forim12i_1 forim12i_3 eorim12i_0 orcd forim12i_2 forim12i_3 forim12i_1 eorim12i_1 olcd jaoi $.
$}
$( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forim1i_0 $f wff ph $.
	forim1i_1 $f wff ps $.
	forim1i_2 $f wff ch $.
	eorim1i_0 $e |- ( ph -> ps ) $.
	orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $= forim1i_0 forim1i_1 forim1i_2 forim1i_2 eorim1i_0 forim1i_2 id orim12i $.
$}
$( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forim2i_0 $f wff ph $.
	forim2i_1 $f wff ps $.
	forim2i_2 $f wff ch $.
	eorim2i_0 $e |- ( ph -> ps ) $.
	orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $= forim2i_2 forim2i_2 forim2i_0 forim2i_1 forim2i_2 id eorim2i_0 orim12i $.
$}
$( Inference adding a left disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 12-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forbi2i_0 $f wff ph $.
	forbi2i_1 $f wff ps $.
	forbi2i_2 $f wff ch $.
	eorbi2i_0 $e |- ( ph <-> ps ) $.
	orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $= forbi2i_2 forbi2i_0 wo forbi2i_2 forbi2i_1 wo forbi2i_0 forbi2i_1 forbi2i_2 forbi2i_0 forbi2i_1 eorbi2i_0 biimpi orim2i forbi2i_1 forbi2i_0 forbi2i_2 forbi2i_0 forbi2i_1 eorbi2i_0 biimpri orim2i impbii $.
$}
$( Inference adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forbi1i_0 $f wff ph $.
	forbi1i_1 $f wff ps $.
	forbi1i_2 $f wff ch $.
	eorbi1i_0 $e |- ( ph <-> ps ) $.
	orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $= forbi1i_0 forbi1i_2 wo forbi1i_2 forbi1i_0 wo forbi1i_2 forbi1i_1 wo forbi1i_1 forbi1i_2 wo forbi1i_0 forbi1i_2 orcom forbi1i_0 forbi1i_1 forbi1i_2 eorbi1i_0 orbi2i forbi1i_2 forbi1i_1 orcom 3bitri $.
$}
$( Infer the disjunction of two equivalences.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	forbi12i_0 $f wff ph $.
	forbi12i_1 $f wff ps $.
	forbi12i_2 $f wff ch $.
	forbi12i_3 $f wff th $.
	eorbi12i_0 $e |- ( ph <-> ps ) $.
	eorbi12i_1 $e |- ( ch <-> th ) $.
	orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $= forbi12i_0 forbi12i_2 wo forbi12i_0 forbi12i_3 wo forbi12i_1 forbi12i_3 wo forbi12i_2 forbi12i_3 forbi12i_0 eorbi12i_1 orbi2i forbi12i_0 forbi12i_1 forbi12i_3 eorbi12i_0 orbi1i bitri $.
$}
$( Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm1.5_0 $f wff ph $.
	fpm1.5_1 $f wff ps $.
	fpm1.5_2 $f wff ch $.
	pm1.5 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ) $= fpm1.5_0 fpm1.5_1 fpm1.5_0 fpm1.5_2 wo wo fpm1.5_1 fpm1.5_2 wo fpm1.5_0 fpm1.5_0 fpm1.5_2 wo fpm1.5_1 fpm1.5_0 fpm1.5_2 orc olcd fpm1.5_2 fpm1.5_0 fpm1.5_2 wo fpm1.5_1 fpm1.5_2 fpm1.5_0 olc orim2i jaoi $.
$}
$( Swap two disjuncts.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 14-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	for12_0 $f wff ph $.
	for12_1 $f wff ps $.
	for12_2 $f wff ch $.
	or12 $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ) $= for12_0 for12_1 for12_2 wo wo for12_1 for12_0 for12_2 wo wo for12_0 for12_1 for12_2 pm1.5 for12_1 for12_0 for12_2 pm1.5 impbii $.
$}
$( Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forass_0 $f wff ph $.
	forass_1 $f wff ps $.
	forass_2 $f wff ch $.
	orass $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $= forass_0 forass_1 wo forass_2 wo forass_2 forass_0 forass_1 wo wo forass_0 forass_2 forass_1 wo wo forass_0 forass_1 forass_2 wo wo forass_0 forass_1 wo forass_2 orcom forass_2 forass_0 forass_1 or12 forass_2 forass_1 wo forass_1 forass_2 wo forass_0 forass_2 forass_1 orcom orbi2i 3bitri $.
$}
$( Theorem *2.31 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.31_0 $f wff ph $.
	fpm2.31_1 $f wff ps $.
	fpm2.31_2 $f wff ch $.
	pm2.31 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ) $= fpm2.31_0 fpm2.31_1 wo fpm2.31_2 wo fpm2.31_0 fpm2.31_1 fpm2.31_2 wo wo fpm2.31_0 fpm2.31_1 fpm2.31_2 orass biimpri $.
$}
$( Theorem *2.32 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.32_0 $f wff ph $.
	fpm2.32_1 $f wff ps $.
	fpm2.32_2 $f wff ch $.
	pm2.32 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ) $= fpm2.32_0 fpm2.32_1 wo fpm2.32_2 wo fpm2.32_0 fpm2.32_1 fpm2.32_2 wo wo fpm2.32_0 fpm2.32_1 fpm2.32_2 orass biimpi $.
$}
$( A rearrangement of disjuncts.  (Contributed by NM, 18-Oct-1995.)  (Proof
     shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	for32_0 $f wff ph $.
	for32_1 $f wff ps $.
	for32_2 $f wff ch $.
	or32 $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ) $= for32_0 for32_1 wo for32_2 wo for32_0 for32_1 for32_2 wo wo for32_1 for32_0 for32_2 wo wo for32_0 for32_2 wo for32_1 wo for32_0 for32_1 for32_2 orass for32_0 for32_1 for32_2 or12 for32_1 for32_0 for32_2 wo orcom 3bitri $.
$}
$( Rearrangement of 4 disjuncts.  (Contributed by NM, 12-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	for4_0 $f wff ph $.
	for4_1 $f wff ps $.
	for4_2 $f wff ch $.
	for4_3 $f wff th $.
	or4 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( ps \/ th ) ) ) $= for4_0 for4_1 for4_2 for4_3 wo wo wo for4_0 for4_2 for4_1 for4_3 wo wo wo for4_0 for4_1 wo for4_2 for4_3 wo wo for4_0 for4_2 wo for4_1 for4_3 wo wo for4_1 for4_2 for4_3 wo wo for4_2 for4_1 for4_3 wo wo for4_0 for4_1 for4_2 for4_3 or12 orbi2i for4_0 for4_1 for4_2 for4_3 wo orass for4_0 for4_2 for4_1 for4_3 wo orass 3bitr4i $.
$}
$( Rearrangement of 4 disjuncts.  (Contributed by NM, 10-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	for42_0 $f wff ph $.
	for42_1 $f wff ps $.
	for42_2 $f wff ch $.
	for42_3 $f wff th $.
	or42 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( th \/ ps ) ) ) $= for42_0 for42_1 wo for42_2 for42_3 wo wo for42_0 for42_2 wo for42_1 for42_3 wo wo for42_0 for42_2 wo for42_3 for42_1 wo wo for42_0 for42_1 for42_2 for42_3 or4 for42_1 for42_3 wo for42_3 for42_1 wo for42_0 for42_2 wo for42_1 for42_3 orcom orbi2i bitri $.
$}
$( Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forordi_0 $f wff ph $.
	forordi_1 $f wff ps $.
	forordi_2 $f wff ch $.
	orordi $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $= forordi_0 forordi_1 forordi_2 wo wo forordi_0 forordi_0 wo forordi_1 forordi_2 wo wo forordi_0 forordi_1 wo forordi_0 forordi_2 wo wo forordi_0 forordi_0 wo forordi_0 forordi_1 forordi_2 wo forordi_0 oridm orbi1i forordi_0 forordi_0 forordi_1 forordi_2 or4 bitr3i $.
$}
$( Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forordir_0 $f wff ph $.
	forordir_1 $f wff ps $.
	forordir_2 $f wff ch $.
	orordir $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ( ps \/ ch ) ) ) $= forordir_0 forordir_1 wo forordir_2 wo forordir_0 forordir_1 wo forordir_2 forordir_2 wo wo forordir_0 forordir_2 wo forordir_1 forordir_2 wo wo forordir_2 forordir_2 wo forordir_2 forordir_0 forordir_1 wo forordir_2 oridm orbi2i forordir_0 forordir_1 forordir_2 forordir_2 or4 bitr3i $.
$}
$( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  Equivalent to the natural deduction rule
       ` /\ ` I ( ` /\ ` introduction), see ~ natded .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjca_0 $f wff ph $.
	fjca_1 $f wff ps $.
	fjca_2 $f wff ch $.
	ejca_0 $e |- ( ph -> ps ) $.
	ejca_1 $e |- ( ph -> ch ) $.
	jca $p |- ( ph -> ( ps /\ ch ) ) $= fjca_0 fjca_1 fjca_2 fjca_1 fjca_2 wa ejca_0 ejca_1 fjca_1 fjca_2 pm3.2 sylc $.
$}
$( Deduction conjoining the consequents of two implications.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjcad_0 $f wff ph $.
	fjcad_1 $f wff ps $.
	fjcad_2 $f wff ch $.
	fjcad_3 $f wff th $.
	ejcad_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ejcad_1 $e |- ( ph -> ( ps -> th ) ) $.
	jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $= fjcad_0 fjcad_1 fjcad_2 fjcad_3 fjcad_2 fjcad_3 wa ejcad_0 ejcad_1 fjcad_2 fjcad_3 pm3.2 syl6c $.
$}
$( Join three consequents.  (Contributed by Jeff Hankins, 1-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjca31_0 $f wff ph $.
	fjca31_1 $f wff ps $.
	fjca31_2 $f wff ch $.
	fjca31_3 $f wff th $.
	ejca31_0 $e |- ( ph -> ps ) $.
	ejca31_1 $e |- ( ph -> ch ) $.
	ejca31_2 $e |- ( ph -> th ) $.
	jca31 $p |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $= fjca31_0 fjca31_1 fjca31_2 wa fjca31_3 fjca31_0 fjca31_1 fjca31_2 ejca31_0 ejca31_1 jca ejca31_2 jca $.
$}
$( Join three consequents.  (Contributed by FL, 1-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjca32_0 $f wff ph $.
	fjca32_1 $f wff ps $.
	fjca32_2 $f wff ch $.
	fjca32_3 $f wff th $.
	ejca32_0 $e |- ( ph -> ps ) $.
	ejca32_1 $e |- ( ph -> ch ) $.
	ejca32_2 $e |- ( ph -> th ) $.
	jca32 $p |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $= fjca32_0 fjca32_1 fjca32_2 fjca32_3 wa ejca32_0 fjca32_0 fjca32_2 fjca32_3 ejca32_1 ejca32_2 jca jca $.
$}
$( Deduction replacing implication with conjunction.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjcai_0 $f wff ph $.
	fjcai_1 $f wff ps $.
	fjcai_2 $f wff ch $.
	ejcai_0 $e |- ( ph -> ps ) $.
	ejcai_1 $e |- ( ph -> ( ps -> ch ) ) $.
	jcai $p |- ( ph -> ( ps /\ ch ) ) $= fjcai_0 fjcai_1 fjcai_2 ejcai_0 fjcai_0 fjcai_1 fjcai_2 ejcai_0 ejcai_1 mpd jca $.
$}
$( Inference conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 31-Dec-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjctil_0 $f wff ph $.
	fjctil_1 $f wff ps $.
	fjctil_2 $f wff ch $.
	ejctil_0 $e |- ( ph -> ps ) $.
	ejctil_1 $e |- ch $.
	jctil $p |- ( ph -> ( ch /\ ps ) ) $= fjctil_0 fjctil_2 fjctil_1 fjctil_2 fjctil_0 ejctil_1 a1i ejctil_0 jca $.
$}
$( Inference conjoining a theorem to right of consequent in an
       implication.  (Contributed by NM, 31-Dec-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjctir_0 $f wff ph $.
	fjctir_1 $f wff ps $.
	fjctir_2 $f wff ch $.
	ejctir_0 $e |- ( ph -> ps ) $.
	ejctir_1 $e |- ch $.
	jctir $p |- ( ph -> ( ps /\ ch ) ) $= fjctir_0 fjctir_1 fjctir_2 ejctir_0 fjctir_2 fjctir_0 ejctir_1 a1i jca $.
$}
$( Inference conjoining a theorem to the left of a consequent.
       (Contributed by NM, 31-Dec-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	fjctl_0 $f wff ph $.
	fjctl_1 $f wff ps $.
	ejctl_0 $e |- ps $.
	jctl $p |- ( ph -> ( ps /\ ph ) ) $= fjctl_0 fjctl_0 fjctl_1 fjctl_0 id ejctl_0 jctil $.
$}
$( Inference conjoining a theorem to the right of a consequent.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	fjctr_0 $f wff ph $.
	fjctr_1 $f wff ps $.
	ejctr_0 $e |- ps $.
	jctr $p |- ( ph -> ( ph /\ ps ) ) $= fjctr_0 fjctr_0 fjctr_1 fjctr_0 id ejctr_0 jctir $.
$}
$( Deduction conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 21-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjctild_0 $f wff ph $.
	fjctild_1 $f wff ps $.
	fjctild_2 $f wff ch $.
	fjctild_3 $f wff th $.
	ejctild_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ejctild_1 $e |- ( ph -> th ) $.
	jctild $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $= fjctild_0 fjctild_1 fjctild_3 fjctild_2 fjctild_0 fjctild_3 fjctild_1 ejctild_1 a1d ejctild_0 jcad $.
$}
$( Deduction conjoining a theorem to right of consequent in an
       implication.  (Contributed by NM, 21-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjctird_0 $f wff ph $.
	fjctird_1 $f wff ps $.
	fjctird_2 $f wff ch $.
	fjctird_3 $f wff th $.
	ejctird_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ejctird_1 $e |- ( ph -> th ) $.
	jctird $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $= fjctird_0 fjctird_1 fjctird_2 fjctird_3 ejctird_0 fjctird_0 fjctird_3 fjctird_1 ejctird_1 a1d jcad $.
$}
$( Conjoin antecedent to left of consequent.  (Contributed by NM,
     15-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	fancl_0 $f wff ph $.
	fancl_1 $f wff ps $.
	ancl $p |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ) $= fancl_0 fancl_1 fancl_0 fancl_1 wa fancl_0 fancl_1 pm3.2 a2i $.
$}
$( Conjoin antecedent to left of consequent.  Theorem *4.7 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 25-Jul-1999.)  (Proof
     shortened by Wolf Lammen, 24-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	fanclb_0 $f wff ph $.
	fanclb_1 $f wff ps $.
	anclb $p |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) ) $= fanclb_0 fanclb_1 fanclb_0 fanclb_1 wa fanclb_0 fanclb_1 ibar pm5.74i $.
$}
$( Theorem *5.42 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm5.42_0 $f wff ph $.
	fpm5.42_1 $f wff ps $.
	fpm5.42_2 $f wff ch $.
	pm5.42 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $= fpm5.42_0 fpm5.42_1 fpm5.42_2 wi fpm5.42_1 fpm5.42_0 fpm5.42_2 wa wi fpm5.42_0 fpm5.42_2 fpm5.42_0 fpm5.42_2 wa fpm5.42_1 fpm5.42_0 fpm5.42_2 ibar imbi2d pm5.74i $.
$}
$( Conjoin antecedent to right of consequent.  (Contributed by NM,
     15-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	fancr_0 $f wff ph $.
	fancr_1 $f wff ps $.
	ancr $p |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) ) $= fancr_0 fancr_1 fancr_1 fancr_0 wa fancr_0 fancr_1 pm3.21 a2i $.
$}
$( Conjoin antecedent to right of consequent.  (Contributed by NM,
     25-Jul-1999.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	fancrb_0 $f wff ph $.
	fancrb_1 $f wff ps $.
	ancrb $p |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) ) $= fancrb_0 fancrb_1 fancrb_1 fancrb_0 wa fancrb_0 fancrb_1 iba pm5.74i $.
$}
$( Deduction conjoining antecedent to left of consequent.  (Contributed by
       NM, 12-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	fancli_0 $f wff ph $.
	fancli_1 $f wff ps $.
	eancli_0 $e |- ( ph -> ps ) $.
	ancli $p |- ( ph -> ( ph /\ ps ) ) $= fancli_0 fancli_0 fancli_1 fancli_0 id eancli_0 jca $.
$}
$( Deduction conjoining antecedent to right of consequent.  (Contributed by
       NM, 15-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	fancri_0 $f wff ph $.
	fancri_1 $f wff ps $.
	eancri_0 $e |- ( ph -> ps ) $.
	ancri $p |- ( ph -> ( ps /\ ph ) ) $= fancri_0 fancri_1 fancri_0 eancri_0 fancri_0 id jca $.
$}
$( Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fancld_0 $f wff ph $.
	fancld_1 $f wff ps $.
	fancld_2 $f wff ch $.
	eancld_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ancld $p |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $= fancld_0 fancld_1 fancld_1 fancld_2 fancld_0 fancld_1 idd eancld_0 jcad $.
$}
$( Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fancrd_0 $f wff ph $.
	fancrd_1 $f wff ps $.
	fancrd_2 $f wff ch $.
	eancrd_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ancrd $p |- ( ph -> ( ps -> ( ch /\ ps ) ) ) $= fancrd_0 fancrd_1 fancrd_2 fancrd_1 eancrd_0 fancrd_0 fancrd_1 idd jcad $.
$}
$( Conjoin antecedent to left of consequent in nested implication.
     (Contributed by NM, 10-Aug-1994.)  (Proof shortened by Wolf Lammen,
     14-Jul-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanc2l_0 $f wff ph $.
	fanc2l_1 $f wff ps $.
	fanc2l_2 $f wff ch $.
	anc2l $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $= fanc2l_0 fanc2l_1 fanc2l_2 wi wi fanc2l_0 fanc2l_1 fanc2l_0 fanc2l_2 wa wi wi fanc2l_0 fanc2l_1 fanc2l_2 pm5.42 biimpi $.
$}
$( Conjoin antecedent to right of consequent in nested implication.
     (Contributed by NM, 15-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanc2r_0 $f wff ph $.
	fanc2r_1 $f wff ps $.
	fanc2r_2 $f wff ch $.
	anc2r $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) ) $= fanc2r_0 fanc2r_1 fanc2r_2 wi fanc2r_1 fanc2r_2 fanc2r_0 wa wi fanc2r_0 fanc2r_2 fanc2r_2 fanc2r_0 wa fanc2r_1 fanc2r_0 fanc2r_2 pm3.21 imim2d a2i $.
$}
$( Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 10-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 7-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanc2li_0 $f wff ph $.
	fanc2li_1 $f wff ps $.
	fanc2li_2 $f wff ch $.
	eanc2li_0 $e |- ( ph -> ( ps -> ch ) ) $.
	anc2li $p |- ( ph -> ( ps -> ( ph /\ ch ) ) ) $= fanc2li_0 fanc2li_1 fanc2li_2 fanc2li_0 eanc2li_0 fanc2li_0 id jctild $.
$}
$( Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 7-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanc2ri_0 $f wff ph $.
	fanc2ri_1 $f wff ps $.
	fanc2ri_2 $f wff ch $.
	eanc2ri_0 $e |- ( ph -> ( ps -> ch ) ) $.
	anc2ri $p |- ( ph -> ( ps -> ( ch /\ ph ) ) ) $= fanc2ri_0 fanc2ri_1 fanc2ri_2 fanc2ri_0 eanc2ri_0 fanc2ri_0 id jctird $.
$}
$( Theorem *3.41 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.41_0 $f wff ph $.
	fpm3.41_1 $f wff ps $.
	fpm3.41_2 $f wff ch $.
	pm3.41 $p |- ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $= fpm3.41_0 fpm3.41_1 wa fpm3.41_0 fpm3.41_2 fpm3.41_0 fpm3.41_1 simpl imim1i $.
$}
$( Theorem *3.42 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.42_0 $f wff ph $.
	fpm3.42_1 $f wff ps $.
	fpm3.42_2 $f wff ch $.
	pm3.42 $p |- ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $= fpm3.42_0 fpm3.42_1 wa fpm3.42_1 fpm3.42_2 fpm3.42_0 fpm3.42_1 simpr imim1i $.
$}
$( Conjunction implies implication.  Theorem *3.4 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 31-Jul-1995.) $)
${
	$v ph $.
	$v ps $.
	fpm3.4_0 $f wff ph $.
	fpm3.4_1 $f wff ps $.
	pm3.4 $p |- ( ( ph /\ ps ) -> ( ph -> ps ) ) $= fpm3.4_0 fpm3.4_1 wa fpm3.4_1 fpm3.4_0 fpm3.4_0 fpm3.4_1 simpr a1d $.
$}
$( Conjunction with implication.  Compare Theorem *4.45 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 17-May-1998.) $)
${
	$v ph $.
	$v ps $.
	fpm4.45im_0 $f wff ph $.
	fpm4.45im_1 $f wff ps $.
	pm4.45im $p |- ( ph <-> ( ph /\ ( ps -> ph ) ) ) $= fpm4.45im_0 fpm4.45im_0 fpm4.45im_1 fpm4.45im_0 wi wa fpm4.45im_0 fpm4.45im_1 fpm4.45im_0 wi fpm4.45im_0 fpm4.45im_1 ax-1 ancli fpm4.45im_0 fpm4.45im_1 fpm4.45im_0 wi simpl impbii $.
$}
$( Conjoin antecedents and consequents in a deduction.  (Contributed by NM,
       3-Apr-1994.)  (Proof shortened by Wolf Lammen, 18-Dec-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fanim12d_0 $f wff ph $.
	fanim12d_1 $f wff ps $.
	fanim12d_2 $f wff ch $.
	fanim12d_3 $f wff th $.
	fanim12d_4 $f wff ta $.
	eanim12d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eanim12d_1 $e |- ( ph -> ( th -> ta ) ) $.
	anim12d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) ) $= fanim12d_0 fanim12d_1 fanim12d_2 fanim12d_3 fanim12d_4 fanim12d_2 fanim12d_4 wa eanim12d_0 eanim12d_1 fanim12d_0 fanim12d_2 fanim12d_4 wa idd syl2and $.
$}
$( Add a conjunct to right of antecedent and consequent in a deduction.
       (Contributed by NM, 3-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanim1d_0 $f wff ph $.
	fanim1d_1 $f wff ps $.
	fanim1d_2 $f wff ch $.
	fanim1d_3 $f wff th $.
	eanim1d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	anim1d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ th ) ) ) $= fanim1d_0 fanim1d_1 fanim1d_2 fanim1d_3 fanim1d_3 eanim1d_0 fanim1d_0 fanim1d_3 idd anim12d $.
$}
$( Add a conjunct to left of antecedent and consequent in a deduction.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanim2d_0 $f wff ph $.
	fanim2d_1 $f wff ps $.
	fanim2d_2 $f wff ch $.
	fanim2d_3 $f wff th $.
	eanim2d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	anim2d $p |- ( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) ) $= fanim2d_0 fanim2d_3 fanim2d_3 fanim2d_1 fanim2d_2 fanim2d_0 fanim2d_3 idd eanim2d_0 anim12d $.
$}
$( Conjoin antecedents and consequents of two premises.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 14-Dec-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanim12i_0 $f wff ph $.
	fanim12i_1 $f wff ps $.
	fanim12i_2 $f wff ch $.
	fanim12i_3 $f wff th $.
	eanim12i_0 $e |- ( ph -> ps ) $.
	eanim12i_1 $e |- ( ch -> th ) $.
	anim12i $p |- ( ( ph /\ ch ) -> ( ps /\ th ) ) $= fanim12i_0 fanim12i_1 fanim12i_3 fanim12i_1 fanim12i_3 wa fanim12i_2 eanim12i_0 eanim12i_1 fanim12i_1 fanim12i_3 wa id syl2an $.
$}
$( Variant of ~ anim12i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanim12ci_0 $f wff ph $.
	fanim12ci_1 $f wff ps $.
	fanim12ci_2 $f wff ch $.
	fanim12ci_3 $f wff th $.
	eanim12ci_0 $e |- ( ph -> ps ) $.
	eanim12ci_1 $e |- ( ch -> th ) $.
	anim12ci $p |- ( ( ph /\ ch ) -> ( th /\ ps ) ) $= fanim12ci_2 fanim12ci_0 fanim12ci_3 fanim12ci_1 wa fanim12ci_2 fanim12ci_3 fanim12ci_0 fanim12ci_1 eanim12ci_1 eanim12ci_0 anim12i ancoms $.
$}
$( Introduce conjunct to both sides of an implication.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanim1i_0 $f wff ph $.
	fanim1i_1 $f wff ps $.
	fanim1i_2 $f wff ch $.
	eanim1i_0 $e |- ( ph -> ps ) $.
	anim1i $p |- ( ( ph /\ ch ) -> ( ps /\ ch ) ) $= fanim1i_0 fanim1i_1 fanim1i_2 fanim1i_2 eanim1i_0 fanim1i_2 id anim12i $.
$}
$( Introduce conjunct to both sides of an implication.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanim2i_0 $f wff ph $.
	fanim2i_1 $f wff ps $.
	fanim2i_2 $f wff ch $.
	eanim2i_0 $e |- ( ph -> ps ) $.
	anim2i $p |- ( ( ch /\ ph ) -> ( ch /\ ps ) ) $= fanim2i_2 fanim2i_2 fanim2i_0 fanim2i_1 fanim2i_2 id eanim2i_0 anim12i $.
$}
$( Conjoin antecedents and consequents in a deduction.  (Contributed by NM,
       11-Nov-2007.)  (Proof shortened by Wolf Lammen, 19-Jul-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fanim12ii_0 $f wff ph $.
	fanim12ii_1 $f wff ps $.
	fanim12ii_2 $f wff ch $.
	fanim12ii_3 $f wff th $.
	fanim12ii_4 $f wff ta $.
	eanim12ii_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eanim12ii_1 $e |- ( th -> ( ps -> ta ) ) $.
	anim12ii $p |- ( ( ph /\ th ) -> ( ps -> ( ch /\ ta ) ) ) $= fanim12ii_0 fanim12ii_3 wa fanim12ii_1 fanim12ii_2 fanim12ii_4 fanim12ii_0 fanim12ii_1 fanim12ii_2 wi fanim12ii_3 eanim12ii_0 adantr fanim12ii_3 fanim12ii_1 fanim12ii_4 wi fanim12ii_0 eanim12ii_1 adantl jcad $.
$}
$( Conjoin antecedents and consequents of two premises.  This is the closed
     theorem form of ~ anim12d .  Theorem *3.47 of [WhiteheadRussell] p. 113.
     It was proved by Leibniz, and it evidently pleased him enough to call it
     _praeclarum theorema_ (splendid theorem).  (Contributed by NM,
     12-Aug-1993.)  (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fprth_0 $f wff ph $.
	fprth_1 $f wff ps $.
	fprth_2 $f wff ch $.
	fprth_3 $f wff th $.
	prth $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) -> ( ( ph /\ ch ) -> ( ps /\ th ) ) ) $= fprth_0 fprth_1 wi fprth_2 fprth_3 wi wa fprth_0 fprth_1 fprth_2 fprth_3 fprth_0 fprth_1 wi fprth_2 fprth_3 wi simpl fprth_0 fprth_1 wi fprth_2 fprth_3 wi simpr anim12d $.
$}
$( Theorem *2.3 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.3_0 $f wff ph $.
	fpm2.3_1 $f wff ps $.
	fpm2.3_2 $f wff ch $.
	pm2.3 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ) $= fpm2.3_1 fpm2.3_2 wo fpm2.3_2 fpm2.3_1 wo fpm2.3_0 fpm2.3_1 fpm2.3_2 pm1.4 orim2i $.
$}
$( Theorem *2.41 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.41_0 $f wff ph $.
	fpm2.41_1 $f wff ps $.
	pm2.41 $p |- ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $= fpm2.41_1 fpm2.41_0 fpm2.41_1 wo fpm2.41_0 fpm2.41_1 wo fpm2.41_1 fpm2.41_0 olc fpm2.41_0 fpm2.41_1 wo id jaoi $.
$}
$( Theorem *2.42 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.42_0 $f wff ph $.
	fpm2.42_1 $f wff ps $.
	pm2.42 $p |- ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) ) $= fpm2.42_0 wn fpm2.42_0 fpm2.42_1 wi fpm2.42_0 fpm2.42_1 wi fpm2.42_0 fpm2.42_1 pm2.21 fpm2.42_0 fpm2.42_1 wi id jaoi $.
$}
$( Theorem *2.4 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.4_0 $f wff ph $.
	fpm2.4_1 $f wff ps $.
	pm2.4 $p |- ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $= fpm2.4_0 fpm2.4_0 fpm2.4_1 wo fpm2.4_0 fpm2.4_1 wo fpm2.4_0 fpm2.4_1 orc fpm2.4_0 fpm2.4_1 wo id jaoi $.
$}
$( Deduction rule for proof by contradiction.  (Contributed by NM,
       12-Jun-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.65da_0 $f wff ph $.
	fpm2.65da_1 $f wff ps $.
	fpm2.65da_2 $f wff ch $.
	epm2.65da_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	epm2.65da_1 $e |- ( ( ph /\ ps ) -> -. ch ) $.
	pm2.65da $p |- ( ph -> -. ps ) $= fpm2.65da_0 fpm2.65da_1 fpm2.65da_2 fpm2.65da_0 fpm2.65da_1 fpm2.65da_2 epm2.65da_0 ex fpm2.65da_0 fpm2.65da_1 fpm2.65da_2 wn epm2.65da_1 ex pm2.65d $.
$}
$( Theorem *4.44 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.44_0 $f wff ph $.
	fpm4.44_1 $f wff ps $.
	pm4.44 $p |- ( ph <-> ( ph \/ ( ph /\ ps ) ) ) $= fpm4.44_0 fpm4.44_0 fpm4.44_0 fpm4.44_1 wa wo fpm4.44_0 fpm4.44_0 fpm4.44_1 wa orc fpm4.44_0 fpm4.44_0 fpm4.44_0 fpm4.44_1 wa fpm4.44_0 id fpm4.44_0 fpm4.44_1 simpl jaoi impbii $.
$}
$( Theorem *4.14 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.14_0 $f wff ph $.
	fpm4.14_1 $f wff ps $.
	fpm4.14_2 $f wff ch $.
	pm4.14 $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ) $= fpm4.14_0 fpm4.14_1 fpm4.14_2 wi wi fpm4.14_0 fpm4.14_2 wn fpm4.14_1 wn wi wi fpm4.14_0 fpm4.14_1 wa fpm4.14_2 wi fpm4.14_0 fpm4.14_2 wn wa fpm4.14_1 wn wi fpm4.14_1 fpm4.14_2 wi fpm4.14_2 wn fpm4.14_1 wn wi fpm4.14_0 fpm4.14_1 fpm4.14_2 con34b imbi2i fpm4.14_0 fpm4.14_1 fpm4.14_2 impexp fpm4.14_0 fpm4.14_2 wn fpm4.14_1 wn impexp 3bitr4i $.
$}
$( Theorem *3.37 (Transp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.37_0 $f wff ph $.
	fpm3.37_1 $f wff ps $.
	fpm3.37_2 $f wff ch $.
	pm3.37 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) ) $= fpm3.37_0 fpm3.37_1 wa fpm3.37_2 wi fpm3.37_0 fpm3.37_2 wn wa fpm3.37_1 wn wi fpm3.37_0 fpm3.37_1 fpm3.37_2 pm4.14 biimpi $.
$}
$( Theorem to move a conjunct in and out of a negation.  (Contributed by NM,
     9-Nov-2003.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnan_0 $f wff ph $.
	fnan_1 $f wff ps $.
	fnan_2 $f wff ch $.
	nan $p |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) ) $= fnan_0 fnan_1 wa fnan_2 wn wi fnan_0 fnan_1 fnan_2 wn wi wi fnan_0 fnan_1 fnan_2 wa wn wi fnan_0 fnan_1 fnan_2 wn impexp fnan_1 fnan_2 wn wi fnan_1 fnan_2 wa wn fnan_0 fnan_1 fnan_2 imnan imbi2i bitr2i $.
$}
$( Theorem *4.15 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 18-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.15_0 $f wff ph $.
	fpm4.15_1 $f wff ps $.
	fpm4.15_2 $f wff ch $.
	pm4.15 $p |- ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) ) $= fpm4.15_1 fpm4.15_2 wa fpm4.15_0 wn wi fpm4.15_0 fpm4.15_1 fpm4.15_2 wa wn wi fpm4.15_0 fpm4.15_1 wa fpm4.15_2 wn wi fpm4.15_1 fpm4.15_2 wa fpm4.15_0 con2b fpm4.15_0 fpm4.15_1 fpm4.15_2 nan bitr2i $.
$}
$( Theorem *4.78 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.78_0 $f wff ph $.
	fpm4.78_1 $f wff ps $.
	fpm4.78_2 $f wff ch $.
	pm4.78 $p |- ( ( ( ph -> ps ) \/ ( ph -> ch ) ) <-> ( ph -> ( ps \/ ch ) ) ) $= fpm4.78_0 wn fpm4.78_1 fpm4.78_2 wo wo fpm4.78_0 wn fpm4.78_1 wo fpm4.78_0 wn fpm4.78_2 wo wo fpm4.78_0 fpm4.78_1 fpm4.78_2 wo wi fpm4.78_0 fpm4.78_1 wi fpm4.78_0 fpm4.78_2 wi wo fpm4.78_0 wn fpm4.78_1 fpm4.78_2 orordi fpm4.78_0 fpm4.78_1 fpm4.78_2 wo imor fpm4.78_0 fpm4.78_1 wi fpm4.78_0 wn fpm4.78_1 wo fpm4.78_0 fpm4.78_2 wi fpm4.78_0 wn fpm4.78_2 wo fpm4.78_0 fpm4.78_1 imor fpm4.78_0 fpm4.78_2 imor orbi12i 3bitr4ri $.
$}
$( Theorem *4.79 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 27-Jun-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.79_0 $f wff ph $.
	fpm4.79_1 $f wff ps $.
	fpm4.79_2 $f wff ch $.
	pm4.79 $p |- ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <-> ( ( ps /\ ch ) -> ph ) ) $= fpm4.79_1 fpm4.79_0 wi fpm4.79_2 fpm4.79_0 wi wo fpm4.79_1 fpm4.79_2 wa fpm4.79_0 wi fpm4.79_1 fpm4.79_0 wi fpm4.79_1 fpm4.79_0 fpm4.79_2 fpm4.79_0 wi fpm4.79_2 fpm4.79_1 fpm4.79_0 wi id fpm4.79_2 fpm4.79_0 wi id jaoa fpm4.79_1 fpm4.79_2 wa fpm4.79_0 wi fpm4.79_1 fpm4.79_0 wi fpm4.79_2 fpm4.79_0 wi fpm4.79_1 fpm4.79_0 wi wn fpm4.79_1 fpm4.79_1 fpm4.79_2 wa fpm4.79_0 wi fpm4.79_2 fpm4.79_0 wi fpm4.79_1 fpm4.79_0 simplim fpm4.79_1 fpm4.79_2 fpm4.79_0 pm3.3 syl5 orrd impbii $.
$}
$( Theorem *4.87 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Eric Schmidt, 26-Oct-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.87_0 $f wff ph $.
	fpm4.87_1 $f wff ps $.
	fpm4.87_2 $f wff ch $.
	pm4.87 $p |- ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\ ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\ ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) ) $= fpm4.87_0 fpm4.87_1 wa fpm4.87_2 wi fpm4.87_0 fpm4.87_1 fpm4.87_2 wi wi wb fpm4.87_0 fpm4.87_1 fpm4.87_2 wi wi fpm4.87_1 fpm4.87_0 fpm4.87_2 wi wi wb wa fpm4.87_1 fpm4.87_0 fpm4.87_2 wi wi fpm4.87_1 fpm4.87_0 wa fpm4.87_2 wi wb fpm4.87_0 fpm4.87_1 wa fpm4.87_2 wi fpm4.87_0 fpm4.87_1 fpm4.87_2 wi wi wb fpm4.87_0 fpm4.87_1 fpm4.87_2 wi wi fpm4.87_1 fpm4.87_0 fpm4.87_2 wi wi wb fpm4.87_0 fpm4.87_1 fpm4.87_2 impexp fpm4.87_0 fpm4.87_1 fpm4.87_2 bi2.04 pm3.2i fpm4.87_1 fpm4.87_0 wa fpm4.87_2 wi fpm4.87_1 fpm4.87_0 fpm4.87_2 wi wi fpm4.87_1 fpm4.87_0 fpm4.87_2 impexp bicomi pm3.2i $.
$}
$( Theorem *3.33 (Syll) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.33_0 $f wff ph $.
	fpm3.33_1 $f wff ps $.
	fpm3.33_2 $f wff ch $.
	pm3.33 $p |- ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) ) $= fpm3.33_0 fpm3.33_1 wi fpm3.33_1 fpm3.33_2 wi fpm3.33_0 fpm3.33_2 wi fpm3.33_0 fpm3.33_1 fpm3.33_2 imim1 imp $.
$}
$( Theorem *3.34 (Syll) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.34_0 $f wff ph $.
	fpm3.34_1 $f wff ps $.
	fpm3.34_2 $f wff ch $.
	pm3.34 $p |- ( ( ( ps -> ch ) /\ ( ph -> ps ) ) -> ( ph -> ch ) ) $= fpm3.34_1 fpm3.34_2 wi fpm3.34_0 fpm3.34_1 wi fpm3.34_0 fpm3.34_2 wi fpm3.34_1 fpm3.34_2 fpm3.34_0 imim2 imp $.
$}
$( Conjunctive detachment.  Theorem *3.35 of [WhiteheadRussell] p. 112.
     (Contributed by NM, 14-Dec-2002.) $)
${
	$v ph $.
	$v ps $.
	fpm3.35_0 $f wff ph $.
	fpm3.35_1 $f wff ps $.
	pm3.35 $p |- ( ( ph /\ ( ph -> ps ) ) -> ps ) $= fpm3.35_0 fpm3.35_0 fpm3.35_1 wi fpm3.35_1 fpm3.35_0 fpm3.35_1 pm2.27 imp $.
$}
$( Theorem *5.31 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm5.31_0 $f wff ph $.
	fpm5.31_1 $f wff ps $.
	fpm5.31_2 $f wff ch $.
	pm5.31 $p |- ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ps /\ ch ) ) ) $= fpm5.31_2 fpm5.31_0 fpm5.31_1 wi fpm5.31_0 fpm5.31_1 fpm5.31_2 wa wi fpm5.31_2 fpm5.31_1 fpm5.31_1 fpm5.31_2 wa fpm5.31_0 fpm5.31_2 fpm5.31_1 pm3.21 imim2d imp $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp4a_0 $f wff ph $.
	fimp4a_1 $f wff ps $.
	fimp4a_2 $f wff ch $.
	fimp4a_3 $f wff th $.
	fimp4a_4 $f wff ta $.
	eimp4a_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp4a $p |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $= fimp4a_0 fimp4a_1 fimp4a_2 fimp4a_3 fimp4a_4 wi wi fimp4a_2 fimp4a_3 wa fimp4a_4 wi eimp4a_0 fimp4a_2 fimp4a_3 fimp4a_4 impexp syl6ibr $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp4b_0 $f wff ph $.
	fimp4b_1 $f wff ps $.
	fimp4b_2 $f wff ch $.
	fimp4b_3 $f wff th $.
	fimp4b_4 $f wff ta $.
	eimp4b_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $= fimp4b_0 fimp4b_1 fimp4b_2 fimp4b_3 wa fimp4b_4 wi fimp4b_0 fimp4b_1 fimp4b_2 fimp4b_3 fimp4b_4 eimp4b_0 imp4a imp $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp4c_0 $f wff ph $.
	fimp4c_1 $f wff ps $.
	fimp4c_2 $f wff ch $.
	fimp4c_3 $f wff th $.
	fimp4c_4 $f wff ta $.
	eimp4c_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $= fimp4c_0 fimp4c_1 fimp4c_2 wa fimp4c_3 fimp4c_4 fimp4c_0 fimp4c_1 fimp4c_2 fimp4c_3 fimp4c_4 wi eimp4c_0 imp3a imp3a $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp4d_0 $f wff ph $.
	fimp4d_1 $f wff ps $.
	fimp4d_2 $f wff ch $.
	fimp4d_3 $f wff th $.
	fimp4d_4 $f wff ta $.
	eimp4d_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $= fimp4d_0 fimp4d_1 fimp4d_2 fimp4d_3 wa fimp4d_4 fimp4d_0 fimp4d_1 fimp4d_2 fimp4d_3 fimp4d_4 eimp4d_0 imp4a imp3a $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp41_0 $f wff ph $.
	fimp41_1 $f wff ps $.
	fimp41_2 $f wff ch $.
	fimp41_3 $f wff th $.
	fimp41_4 $f wff ta $.
	eimp41_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp41 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $= fimp41_0 fimp41_1 wa fimp41_2 fimp41_3 fimp41_4 fimp41_0 fimp41_1 fimp41_2 fimp41_3 fimp41_4 wi wi eimp41_0 imp imp31 $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp42_0 $f wff ph $.
	fimp42_1 $f wff ps $.
	fimp42_2 $f wff ch $.
	fimp42_3 $f wff th $.
	fimp42_4 $f wff ta $.
	eimp42_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp42 $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $= fimp42_0 fimp42_1 fimp42_2 wa wa fimp42_3 fimp42_4 fimp42_0 fimp42_1 fimp42_2 fimp42_3 fimp42_4 wi eimp42_0 imp32 imp $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp43_0 $f wff ph $.
	fimp43_1 $f wff ps $.
	fimp43_2 $f wff ch $.
	fimp43_3 $f wff th $.
	fimp43_4 $f wff ta $.
	eimp43_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $= fimp43_0 fimp43_1 wa fimp43_2 fimp43_3 wa fimp43_4 fimp43_0 fimp43_1 fimp43_2 fimp43_3 fimp43_4 eimp43_0 imp4b imp $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp44_0 $f wff ph $.
	fimp44_1 $f wff ps $.
	fimp44_2 $f wff ch $.
	fimp44_3 $f wff th $.
	fimp44_4 $f wff ta $.
	eimp44_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp44 $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $= fimp44_0 fimp44_1 fimp44_2 wa fimp44_3 wa fimp44_4 fimp44_0 fimp44_1 fimp44_2 fimp44_3 fimp44_4 eimp44_0 imp4c imp $.
$}
$( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fimp45_0 $f wff ph $.
	fimp45_1 $f wff ps $.
	fimp45_2 $f wff ch $.
	fimp45_3 $f wff th $.
	fimp45_4 $f wff ta $.
	eimp45_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	imp45 $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $= fimp45_0 fimp45_1 fimp45_2 fimp45_3 wa wa fimp45_4 fimp45_0 fimp45_1 fimp45_2 fimp45_3 fimp45_4 eimp45_0 imp4d imp $.
$}
$( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fimp5a_0 $f wff ph $.
	fimp5a_1 $f wff ps $.
	fimp5a_2 $f wff ch $.
	fimp5a_3 $f wff th $.
	fimp5a_4 $f wff ta $.
	fimp5a_5 $f wff et $.
	eimp5a_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	imp5a $p |- ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) ) $= fimp5a_0 fimp5a_1 fimp5a_2 fimp5a_3 fimp5a_4 fimp5a_5 wi wi fimp5a_3 fimp5a_4 wa fimp5a_5 wi eimp5a_0 fimp5a_3 fimp5a_4 fimp5a_5 pm3.31 syl8 $.
$}
$( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fimp5d_0 $f wff ph $.
	fimp5d_1 $f wff ps $.
	fimp5d_2 $f wff ch $.
	fimp5d_3 $f wff th $.
	fimp5d_4 $f wff ta $.
	fimp5d_5 $f wff et $.
	eimp5d_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	imp5d $p |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ) $= fimp5d_0 fimp5d_1 wa fimp5d_2 wa fimp5d_3 fimp5d_4 fimp5d_5 fimp5d_0 fimp5d_1 fimp5d_2 fimp5d_3 fimp5d_4 fimp5d_5 wi wi eimp5d_0 imp31 imp3a $.
$}
$( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fimp5g_0 $f wff ph $.
	fimp5g_1 $f wff ps $.
	fimp5g_2 $f wff ch $.
	fimp5g_3 $f wff th $.
	fimp5g_4 $f wff ta $.
	fimp5g_5 $f wff et $.
	eimp5g_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	imp5g $p |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ) $= fimp5g_0 fimp5g_1 wa fimp5g_2 fimp5g_3 fimp5g_4 fimp5g_5 fimp5g_0 fimp5g_1 fimp5g_2 fimp5g_3 fimp5g_4 fimp5g_5 wi wi wi eimp5g_0 imp imp4c $.
$}
$( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fimp55_0 $f wff ph $.
	fimp55_1 $f wff ps $.
	fimp55_2 $f wff ch $.
	fimp55_3 $f wff th $.
	fimp55_4 $f wff ta $.
	fimp55_5 $f wff et $.
	eimp55_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	imp55 $p |- ( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et ) $= fimp55_0 fimp55_1 fimp55_2 fimp55_3 wa fimp55_4 fimp55_5 fimp55_0 fimp55_1 fimp55_2 fimp55_3 fimp55_4 fimp55_5 wi eimp55_0 imp4a imp42 $.
$}
$( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fimp511_0 $f wff ph $.
	fimp511_1 $f wff ps $.
	fimp511_2 $f wff ch $.
	fimp511_3 $f wff th $.
	fimp511_4 $f wff ta $.
	fimp511_5 $f wff et $.
	eimp511_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	imp511 $p |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ) $= fimp511_0 fimp511_1 fimp511_2 fimp511_3 wa fimp511_4 fimp511_5 fimp511_0 fimp511_1 fimp511_2 fimp511_3 fimp511_4 fimp511_5 wi eimp511_0 imp4a imp44 $.
$}
$( Exportation followed by a deduction version of importation.
       (Contributed by NM, 6-Sep-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fexpimpd_0 $f wff ph $.
	fexpimpd_1 $f wff ps $.
	fexpimpd_2 $f wff ch $.
	fexpimpd_3 $f wff th $.
	eexpimpd_0 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	expimpd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= fexpimpd_0 fexpimpd_1 fexpimpd_2 fexpimpd_3 fexpimpd_0 fexpimpd_1 fexpimpd_2 fexpimpd_3 wi eexpimpd_0 ex imp3a $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fexp31_0 $f wff ph $.
	fexp31_1 $f wff ps $.
	fexp31_2 $f wff ch $.
	fexp31_3 $f wff th $.
	eexp31_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	exp31 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= fexp31_0 fexp31_1 fexp31_2 fexp31_3 wi fexp31_0 fexp31_1 wa fexp31_2 fexp31_3 eexp31_0 ex ex $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fexp32_0 $f wff ph $.
	fexp32_1 $f wff ps $.
	fexp32_2 $f wff ch $.
	fexp32_3 $f wff th $.
	eexp32_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	exp32 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= fexp32_0 fexp32_1 fexp32_2 fexp32_3 fexp32_0 fexp32_1 fexp32_2 wa fexp32_3 eexp32_0 ex exp3a $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp4a_0 $f wff ph $.
	fexp4a_1 $f wff ps $.
	fexp4a_2 $f wff ch $.
	fexp4a_3 $f wff th $.
	fexp4a_4 $f wff ta $.
	eexp4a_0 $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
	exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp4a_0 fexp4a_1 fexp4a_2 fexp4a_3 wa fexp4a_4 wi fexp4a_2 fexp4a_3 fexp4a_4 wi wi eexp4a_0 fexp4a_2 fexp4a_3 fexp4a_4 impexp syl6ib $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 23-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp4b_0 $f wff ph $.
	fexp4b_1 $f wff ps $.
	fexp4b_2 $f wff ch $.
	fexp4b_3 $f wff th $.
	fexp4b_4 $f wff ta $.
	eexp4b_0 $e |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $.
	exp4b $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp4b_0 fexp4b_1 fexp4b_2 fexp4b_3 fexp4b_4 fexp4b_0 fexp4b_1 fexp4b_2 fexp4b_3 wa fexp4b_4 wi eexp4b_0 ex exp4a $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp4c_0 $f wff ph $.
	fexp4c_1 $f wff ps $.
	fexp4c_2 $f wff ch $.
	fexp4c_3 $f wff th $.
	fexp4c_4 $f wff ta $.
	eexp4c_0 $e |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $.
	exp4c $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp4c_0 fexp4c_1 fexp4c_2 fexp4c_3 fexp4c_4 wi fexp4c_0 fexp4c_1 fexp4c_2 wa fexp4c_3 fexp4c_4 eexp4c_0 exp3a exp3a $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp4d_0 $f wff ph $.
	fexp4d_1 $f wff ps $.
	fexp4d_2 $f wff ch $.
	fexp4d_3 $f wff th $.
	fexp4d_4 $f wff ta $.
	eexp4d_0 $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
	exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp4d_0 fexp4d_1 fexp4d_2 fexp4d_3 fexp4d_4 fexp4d_0 fexp4d_1 fexp4d_2 fexp4d_3 wa fexp4d_4 eexp4d_0 exp3a exp4a $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp41_0 $f wff ph $.
	fexp41_1 $f wff ps $.
	fexp41_2 $f wff ch $.
	fexp41_3 $f wff th $.
	fexp41_4 $f wff ta $.
	eexp41_0 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
	exp41 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp41_0 fexp41_1 fexp41_2 fexp41_3 fexp41_4 wi fexp41_0 fexp41_1 wa fexp41_2 wa fexp41_3 fexp41_4 eexp41_0 ex exp31 $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp42_0 $f wff ph $.
	fexp42_1 $f wff ps $.
	fexp42_2 $f wff ch $.
	fexp42_3 $f wff th $.
	fexp42_4 $f wff ta $.
	eexp42_0 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
	exp42 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp42_0 fexp42_1 fexp42_2 fexp42_3 fexp42_4 wi fexp42_0 fexp42_1 fexp42_2 wa fexp42_3 fexp42_4 eexp42_0 exp31 exp3a $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp43_0 $f wff ph $.
	fexp43_1 $f wff ps $.
	fexp43_2 $f wff ch $.
	fexp43_3 $f wff th $.
	fexp43_4 $f wff ta $.
	eexp43_0 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
	exp43 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp43_0 fexp43_1 fexp43_2 fexp43_3 fexp43_4 fexp43_0 fexp43_1 wa fexp43_2 fexp43_3 wa fexp43_4 eexp43_0 ex exp4b $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp44_0 $f wff ph $.
	fexp44_1 $f wff ps $.
	fexp44_2 $f wff ch $.
	fexp44_3 $f wff th $.
	fexp44_4 $f wff ta $.
	eexp44_0 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $.
	exp44 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp44_0 fexp44_1 fexp44_2 fexp44_3 fexp44_4 wi fexp44_0 fexp44_1 fexp44_2 wa fexp44_3 fexp44_4 eexp44_0 exp32 exp3a $.
$}
$( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fexp45_0 $f wff ph $.
	fexp45_1 $f wff ps $.
	fexp45_2 $f wff ch $.
	fexp45_3 $f wff th $.
	fexp45_4 $f wff ta $.
	eexp45_0 $e |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $.
	exp45 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= fexp45_0 fexp45_1 fexp45_2 fexp45_3 fexp45_4 fexp45_0 fexp45_1 fexp45_2 fexp45_3 wa fexp45_4 eexp45_0 exp32 exp4a $.
$}
$( Export a wff from a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fexpr_0 $f wff ph $.
	fexpr_1 $f wff ps $.
	fexpr_2 $f wff ch $.
	fexpr_3 $f wff th $.
	eexpr_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	expr $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $= fexpr_0 fexpr_1 fexpr_2 fexpr_3 wi fexpr_0 fexpr_1 fexpr_2 fexpr_3 eexpr_0 exp32 imp $.
$}
$( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fexp5c_0 $f wff ph $.
	fexp5c_1 $f wff ps $.
	fexp5c_2 $f wff ch $.
	fexp5c_3 $f wff th $.
	fexp5c_4 $f wff ta $.
	fexp5c_5 $f wff et $.
	eexp5c_0 $e |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) ) $.
	exp5c $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= fexp5c_0 fexp5c_1 fexp5c_2 fexp5c_3 fexp5c_4 fexp5c_5 wi wi fexp5c_0 fexp5c_1 fexp5c_2 wa fexp5c_3 fexp5c_4 fexp5c_5 eexp5c_0 exp4a exp3a $.
$}
$( An exportation inference.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fexp53_0 $f wff ph $.
	fexp53_1 $f wff ps $.
	fexp53_2 $f wff ch $.
	fexp53_3 $f wff th $.
	fexp53_4 $f wff ta $.
	fexp53_5 $f wff et $.
	eexp53_0 $e |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et ) $.
	exp53 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= fexp53_0 fexp53_1 fexp53_2 fexp53_3 fexp53_4 fexp53_5 wi fexp53_0 fexp53_1 wa fexp53_2 fexp53_3 wa wa fexp53_4 fexp53_5 eexp53_0 ex exp43 $.
$}
$( Export a wff from a left conjunct.  (Contributed by Jeff Hankins,
       28-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fexpl_0 $f wff ph $.
	fexpl_1 $f wff ps $.
	fexpl_2 $f wff ch $.
	fexpl_3 $f wff th $.
	eexpl_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	expl $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= fexpl_0 fexpl_1 fexpl_2 fexpl_3 fexpl_0 fexpl_1 fexpl_2 fexpl_3 eexpl_0 exp31 imp3a $.
$}
$( Import a wff into a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fimpr_0 $f wff ph $.
	fimpr_1 $f wff ps $.
	fimpr_2 $f wff ch $.
	fimpr_3 $f wff th $.
	eimpr_0 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	impr $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $= fimpr_0 fimpr_1 fimpr_2 fimpr_3 fimpr_0 fimpr_1 fimpr_2 fimpr_3 wi eimpr_0 ex imp32 $.
$}
$( Export a wff from a left conjunct.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fimpl_0 $f wff ph $.
	fimpl_1 $f wff ps $.
	fimpl_2 $f wff ch $.
	fimpl_3 $f wff th $.
	eimpl_0 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	impl $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $= fimpl_0 fimpl_1 fimpl_2 fimpl_3 fimpl_0 fimpl_1 fimpl_2 fimpl_3 eimpl_0 exp3a imp31 $.
$}
$( Importation with conjunction in consequent.  (Contributed by NM,
       9-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimpac_0 $f wff ph $.
	fimpac_1 $f wff ps $.
	fimpac_2 $f wff ch $.
	eimpac_0 $e |- ( ph -> ( ps -> ch ) ) $.
	impac $p |- ( ( ph /\ ps ) -> ( ch /\ ps ) ) $= fimpac_0 fimpac_1 fimpac_2 fimpac_1 wa fimpac_0 fimpac_1 fimpac_2 eimpac_0 ancrd imp $.
$}
$( Inference form of ~ exbir .  This proof is ~ exbiriVD automatically
       translated and minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
       (Proof shortened by Wolf Lammen, 27-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fexbiri_0 $f wff ph $.
	fexbiri_1 $f wff ps $.
	fexbiri_2 $f wff ch $.
	fexbiri_3 $f wff th $.
	eexbiri_0 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	exbiri $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $= fexbiri_0 fexbiri_1 fexbiri_3 fexbiri_2 fexbiri_0 fexbiri_1 wa fexbiri_2 fexbiri_3 eexbiri_0 biimpar exp31 $.
$}
$( Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimprbda_0 $f wff ph $.
	fsimprbda_1 $f wff ps $.
	fsimprbda_2 $f wff ch $.
	fsimprbda_3 $f wff th $.
	esimprbda_0 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	simprbda $p |- ( ( ph /\ ps ) -> ch ) $= fsimprbda_0 fsimprbda_1 wa fsimprbda_2 fsimprbda_3 fsimprbda_0 fsimprbda_1 fsimprbda_2 fsimprbda_3 wa esimprbda_0 biimpa simpld $.
$}
$( Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimplbda_0 $f wff ph $.
	fsimplbda_1 $f wff ps $.
	fsimplbda_2 $f wff ch $.
	fsimplbda_3 $f wff th $.
	esimplbda_0 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	simplbda $p |- ( ( ph /\ ps ) -> th ) $= fsimplbda_0 fsimplbda_1 wa fsimplbda_2 fsimplbda_3 fsimplbda_0 fsimplbda_1 fsimplbda_2 fsimplbda_3 wa esimplbda_0 biimpa simprd $.
$}
$( Deduction eliminating a conjunct.  Automatically derived from
       ~ simplbi2VD .  (Contributed by Alan Sare, 31-Dec-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimplbi2_0 $f wff ph $.
	fsimplbi2_1 $f wff ps $.
	fsimplbi2_2 $f wff ch $.
	esimplbi2_0 $e |- ( ph <-> ( ps /\ ch ) ) $.
	simplbi2 $p |- ( ps -> ( ch -> ph ) ) $= fsimplbi2_1 fsimplbi2_2 fsimplbi2_0 fsimplbi2_0 fsimplbi2_1 fsimplbi2_2 wa esimplbi2_0 biimpri ex $.
$}
$( A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	fdfbi2_0 $f wff ph $.
	fdfbi2_1 $f wff ps $.
	dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $= fdfbi2_0 fdfbi2_1 wb fdfbi2_0 fdfbi2_1 wi fdfbi2_1 fdfbi2_0 wi wn wi wn fdfbi2_0 fdfbi2_1 wi fdfbi2_1 fdfbi2_0 wi wa fdfbi2_0 fdfbi2_1 dfbi1 fdfbi2_0 fdfbi2_1 wi fdfbi2_1 fdfbi2_0 wi df-an bitr4i $.
$}
$( Definition ~ df-bi rewritten in an abbreviated form to help intuitive
     understanding of that definition.  Note that it is a conjunction of two
     implications; one which asserts properties that follow from the
     biconditional and one which asserts properties that imply the
     biconditional.  (Contributed by NM, 15-Aug-2008.) $)
${
	$v ph $.
	$v ps $.
	fdfbi_0 $f wff ph $.
	fdfbi_1 $f wff ps $.
	dfbi $p |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $= fdfbi_0 fdfbi_1 wb fdfbi_0 fdfbi_1 wi fdfbi_1 fdfbi_0 wi wa wi fdfbi_0 fdfbi_1 wi fdfbi_1 fdfbi_0 wi wa fdfbi_0 fdfbi_1 wb wi fdfbi_0 fdfbi_1 wb fdfbi_0 fdfbi_1 wi fdfbi_1 fdfbi_0 wi wa fdfbi_0 fdfbi_1 dfbi2 biimpi fdfbi_0 fdfbi_1 wb fdfbi_0 fdfbi_1 wi fdfbi_1 fdfbi_0 wi wa fdfbi_0 fdfbi_1 dfbi2 biimpri pm3.2i $.
$}
$( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 2-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm4.71_0 $f wff ph $.
	fpm4.71_1 $f wff ps $.
	pm4.71 $p |- ( ( ph -> ps ) <-> ( ph <-> ( ph /\ ps ) ) ) $= fpm4.71_0 fpm4.71_0 fpm4.71_1 wa wi fpm4.71_0 fpm4.71_0 fpm4.71_1 wa wi fpm4.71_0 fpm4.71_1 wa fpm4.71_0 wi wa fpm4.71_0 fpm4.71_1 wi fpm4.71_0 fpm4.71_0 fpm4.71_1 wa wb fpm4.71_0 fpm4.71_1 wa fpm4.71_0 wi fpm4.71_0 fpm4.71_0 fpm4.71_1 wa wi fpm4.71_0 fpm4.71_1 simpl biantru fpm4.71_0 fpm4.71_1 anclb fpm4.71_0 fpm4.71_0 fpm4.71_1 wa dfbi2 3bitr4i $.
$}
$( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120 (with conjunct reversed).  (Contributed by NM,
     25-Jul-1999.) $)
${
	$v ph $.
	$v ps $.
	fpm4.71r_0 $f wff ph $.
	fpm4.71r_1 $f wff ps $.
	pm4.71r $p |- ( ( ph -> ps ) <-> ( ph <-> ( ps /\ ph ) ) ) $= fpm4.71r_0 fpm4.71r_1 wi fpm4.71r_0 fpm4.71r_0 fpm4.71r_1 wa wb fpm4.71r_0 fpm4.71r_1 fpm4.71r_0 wa wb fpm4.71r_0 fpm4.71r_1 pm4.71 fpm4.71r_0 fpm4.71r_1 wa fpm4.71r_1 fpm4.71r_0 wa fpm4.71r_0 fpm4.71r_0 fpm4.71r_1 ancom bibi2i bitri $.
$}
$( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by NM, 4-Jan-2004.) $)
${
	$v ph $.
	$v ps $.
	fpm4.71i_0 $f wff ph $.
	fpm4.71i_1 $f wff ps $.
	epm4.71i_0 $e |- ( ph -> ps ) $.
	pm4.71i $p |- ( ph <-> ( ph /\ ps ) ) $= fpm4.71i_0 fpm4.71i_1 wi fpm4.71i_0 fpm4.71i_0 fpm4.71i_1 wa wb epm4.71i_0 fpm4.71i_0 fpm4.71i_1 pm4.71 mpbi $.
$}
$( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell] p. 120
       (with conjunct reversed).  (Contributed by NM, 1-Dec-2003.) $)
${
	$v ph $.
	$v ps $.
	fpm4.71ri_0 $f wff ph $.
	fpm4.71ri_1 $f wff ps $.
	epm4.71ri_0 $e |- ( ph -> ps ) $.
	pm4.71ri $p |- ( ph <-> ( ps /\ ph ) ) $= fpm4.71ri_0 fpm4.71ri_1 wi fpm4.71ri_0 fpm4.71ri_1 fpm4.71ri_0 wa wb epm4.71ri_0 fpm4.71ri_0 fpm4.71ri_1 pm4.71r mpbi $.
$}
$( Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by Mario Carneiro, 25-Dec-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.71d_0 $f wff ph $.
	fpm4.71d_1 $f wff ps $.
	fpm4.71d_2 $f wff ch $.
	epm4.71d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	pm4.71d $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $= fpm4.71d_0 fpm4.71d_1 fpm4.71d_2 wi fpm4.71d_1 fpm4.71d_1 fpm4.71d_2 wa wb epm4.71d_0 fpm4.71d_1 fpm4.71d_2 pm4.71 sylib $.
$}
$( Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by NM, 10-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.71rd_0 $f wff ph $.
	fpm4.71rd_1 $f wff ps $.
	fpm4.71rd_2 $f wff ch $.
	epm4.71rd_0 $e |- ( ph -> ( ps -> ch ) ) $.
	pm4.71rd $p |- ( ph -> ( ps <-> ( ch /\ ps ) ) ) $= fpm4.71rd_0 fpm4.71rd_1 fpm4.71rd_2 wi fpm4.71rd_1 fpm4.71rd_2 fpm4.71rd_1 wa wb epm4.71rd_0 fpm4.71rd_1 fpm4.71rd_2 pm4.71r sylib $.
$}
$( Distribution of implication over biconditional.  Theorem *5.32 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 1-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm5.32_0 $f wff ph $.
	fpm5.32_1 $f wff ps $.
	fpm5.32_2 $f wff ch $.
	pm5.32 $p |- ( ( ph -> ( ps <-> ch ) ) <-> ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $= fpm5.32_0 fpm5.32_1 fpm5.32_2 wb wi fpm5.32_0 fpm5.32_1 wn wi wn fpm5.32_0 fpm5.32_2 wn wi wn wb fpm5.32_0 fpm5.32_1 wa fpm5.32_0 fpm5.32_2 wa wb fpm5.32_0 fpm5.32_1 fpm5.32_2 wb wi fpm5.32_0 fpm5.32_1 wn fpm5.32_2 wn wb wi fpm5.32_0 fpm5.32_1 wn wi fpm5.32_0 fpm5.32_2 wn wi wb fpm5.32_0 fpm5.32_1 wn wi wn fpm5.32_0 fpm5.32_2 wn wi wn wb fpm5.32_1 fpm5.32_2 wb fpm5.32_1 wn fpm5.32_2 wn wb fpm5.32_0 fpm5.32_1 fpm5.32_2 notbi imbi2i fpm5.32_0 fpm5.32_1 wn fpm5.32_2 wn pm5.74 fpm5.32_0 fpm5.32_1 wn wi fpm5.32_0 fpm5.32_2 wn wi notbi 3bitri fpm5.32_0 fpm5.32_1 wa fpm5.32_0 fpm5.32_1 wn wi wn fpm5.32_0 fpm5.32_2 wa fpm5.32_0 fpm5.32_2 wn wi wn fpm5.32_0 fpm5.32_1 df-an fpm5.32_0 fpm5.32_2 df-an bibi12i bitr4i $.
$}
$( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 1-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm5.32i_0 $f wff ph $.
	fpm5.32i_1 $f wff ps $.
	fpm5.32i_2 $f wff ch $.
	epm5.32i_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	pm5.32i $p |- ( ( ph /\ ps ) <-> ( ph /\ ch ) ) $= fpm5.32i_0 fpm5.32i_1 fpm5.32i_2 wb wi fpm5.32i_0 fpm5.32i_1 wa fpm5.32i_0 fpm5.32i_2 wa wb epm5.32i_0 fpm5.32i_0 fpm5.32i_1 fpm5.32i_2 pm5.32 mpbi $.
$}
$( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 12-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm5.32ri_0 $f wff ph $.
	fpm5.32ri_1 $f wff ps $.
	fpm5.32ri_2 $f wff ch $.
	epm5.32ri_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	pm5.32ri $p |- ( ( ps /\ ph ) <-> ( ch /\ ph ) ) $= fpm5.32ri_0 fpm5.32ri_1 wa fpm5.32ri_0 fpm5.32ri_2 wa fpm5.32ri_1 fpm5.32ri_0 wa fpm5.32ri_2 fpm5.32ri_0 wa fpm5.32ri_0 fpm5.32ri_1 fpm5.32ri_2 epm5.32ri_0 pm5.32i fpm5.32ri_1 fpm5.32ri_0 ancom fpm5.32ri_2 fpm5.32ri_0 ancom 3bitr4i $.
$}
$( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 29-Oct-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm5.32d_0 $f wff ph $.
	fpm5.32d_1 $f wff ps $.
	fpm5.32d_2 $f wff ch $.
	fpm5.32d_3 $f wff th $.
	epm5.32d_0 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
	pm5.32d $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $= fpm5.32d_0 fpm5.32d_1 fpm5.32d_2 fpm5.32d_3 wb wi fpm5.32d_1 fpm5.32d_2 wa fpm5.32d_1 fpm5.32d_3 wa wb epm5.32d_0 fpm5.32d_1 fpm5.32d_2 fpm5.32d_3 pm5.32 sylib $.
$}
$( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 25-Dec-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm5.32rd_0 $f wff ph $.
	fpm5.32rd_1 $f wff ps $.
	fpm5.32rd_2 $f wff ch $.
	fpm5.32rd_3 $f wff th $.
	epm5.32rd_0 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
	pm5.32rd $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $= fpm5.32rd_0 fpm5.32rd_1 fpm5.32rd_2 wa fpm5.32rd_1 fpm5.32rd_3 wa fpm5.32rd_2 fpm5.32rd_1 wa fpm5.32rd_3 fpm5.32rd_1 wa fpm5.32rd_0 fpm5.32rd_1 fpm5.32rd_2 fpm5.32rd_3 epm5.32rd_0 pm5.32d fpm5.32rd_2 fpm5.32rd_1 ancom fpm5.32rd_3 fpm5.32rd_1 ancom 3bitr4g $.
$}
$( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 9-Dec-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm5.32da_0 $f wff ph $.
	fpm5.32da_1 $f wff ps $.
	fpm5.32da_2 $f wff ch $.
	fpm5.32da_3 $f wff th $.
	epm5.32da_0 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	pm5.32da $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $= fpm5.32da_0 fpm5.32da_1 fpm5.32da_2 fpm5.32da_3 fpm5.32da_0 fpm5.32da_1 fpm5.32da_2 fpm5.32da_3 wb epm5.32da_0 ex pm5.32d $.
$}
$( Add a conjunction to an equivalence.  (Contributed by Jeff Madsen,
       20-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbiadan2_0 $f wff ph $.
	fbiadan2_1 $f wff ps $.
	fbiadan2_2 $f wff ch $.
	ebiadan2_0 $e |- ( ph -> ps ) $.
	ebiadan2_1 $e |- ( ps -> ( ph <-> ch ) ) $.
	biadan2 $p |- ( ph <-> ( ps /\ ch ) ) $= fbiadan2_0 fbiadan2_1 fbiadan2_0 wa fbiadan2_1 fbiadan2_2 wa fbiadan2_0 fbiadan2_1 ebiadan2_0 pm4.71ri fbiadan2_1 fbiadan2_0 fbiadan2_2 ebiadan2_1 pm5.32i bitri $.
$}
$( Theorem *4.24 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	fpm4.24_0 $f wff ph $.
	pm4.24 $p |- ( ph <-> ( ph /\ ph ) ) $= fpm4.24_0 fpm4.24_0 fpm4.24_0 id pm4.71i $.
$}
$( Idempotent law for conjunction.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 14-Mar-2014.) $)
${
	$v ph $.
	fanidm_0 $f wff ph $.
	anidm $p |- ( ( ph /\ ph ) <-> ph ) $= fanidm_0 fanidm_0 fanidm_0 wa fanidm_0 pm4.24 bicomi $.
$}
$( Inference from idempotent law for conjunction.  (Contributed by NM,
       15-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	fanidms_0 $f wff ph $.
	fanidms_1 $f wff ps $.
	eanidms_0 $e |- ( ( ph /\ ph ) -> ps ) $.
	anidms $p |- ( ph -> ps ) $= fanidms_0 fanidms_1 fanidms_0 fanidms_0 fanidms_1 eanidms_0 ex pm2.43i $.
$}
$( Conjunction idempotence with antecedent.  (Contributed by Roy F. Longton,
     8-Aug-2005.) $)
${
	$v ph $.
	$v ps $.
	fanidmdbi_0 $f wff ph $.
	fanidmdbi_1 $f wff ps $.
	anidmdbi $p |- ( ( ph -> ( ps /\ ps ) ) <-> ( ph -> ps ) ) $= fanidmdbi_1 fanidmdbi_1 wa fanidmdbi_1 fanidmdbi_0 fanidmdbi_1 anidm imbi2i $.
$}
$( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanasss_0 $f wff ph $.
	fanasss_1 $f wff ps $.
	fanasss_2 $f wff ch $.
	fanasss_3 $f wff th $.
	eanasss_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	anasss $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $= fanasss_0 fanasss_1 fanasss_2 fanasss_3 fanasss_0 fanasss_1 fanasss_2 fanasss_3 eanasss_0 exp31 imp32 $.
$}
$( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanassrs_0 $f wff ph $.
	fanassrs_1 $f wff ps $.
	fanassrs_2 $f wff ch $.
	fanassrs_3 $f wff th $.
	eanassrs_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	anassrs $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $= fanassrs_0 fanassrs_1 fanassrs_2 fanassrs_3 fanassrs_0 fanassrs_1 fanassrs_2 fanassrs_3 eanassrs_0 exp32 imp31 $.
$}
$( Associative law for conjunction.  Theorem *4.32 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanass_0 $f wff ph $.
	fanass_1 $f wff ps $.
	fanass_2 $f wff ch $.
	anass $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $= fanass_0 fanass_1 wa fanass_2 wa fanass_0 fanass_1 fanass_2 wa wa fanass_0 fanass_1 fanass_2 fanass_0 fanass_1 fanass_2 wa wa fanass_0 fanass_1 fanass_2 wa wa id anassrs fanass_0 fanass_1 fanass_2 fanass_0 fanass_1 wa fanass_2 wa fanass_0 fanass_1 wa fanass_2 wa id anasss impbii $.
$}
$( A syllogism inference.  (Contributed by NM, 10-Mar-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylanl1_0 $f wff ph $.
	fsylanl1_1 $f wff ps $.
	fsylanl1_2 $f wff ch $.
	fsylanl1_3 $f wff th $.
	fsylanl1_4 $f wff ta $.
	esylanl1_0 $e |- ( ph -> ps ) $.
	esylanl1_1 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
	sylanl1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $= fsylanl1_0 fsylanl1_2 wa fsylanl1_1 fsylanl1_2 wa fsylanl1_3 fsylanl1_4 fsylanl1_0 fsylanl1_1 fsylanl1_2 esylanl1_0 anim1i esylanl1_1 sylan $.
$}
$( A syllogism inference.  (Contributed by NM, 1-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylanl2_0 $f wff ph $.
	fsylanl2_1 $f wff ps $.
	fsylanl2_2 $f wff ch $.
	fsylanl2_3 $f wff th $.
	fsylanl2_4 $f wff ta $.
	esylanl2_0 $e |- ( ph -> ch ) $.
	esylanl2_1 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
	sylanl2 $p |- ( ( ( ps /\ ph ) /\ th ) -> ta ) $= fsylanl2_1 fsylanl2_0 wa fsylanl2_1 fsylanl2_2 wa fsylanl2_3 fsylanl2_4 fsylanl2_0 fsylanl2_2 fsylanl2_1 esylanl2_0 anim2i esylanl2_1 sylan $.
$}
$( A syllogism inference.  (Contributed by NM, 9-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylanr1_0 $f wff ph $.
	fsylanr1_1 $f wff ps $.
	fsylanr1_2 $f wff ch $.
	fsylanr1_3 $f wff th $.
	fsylanr1_4 $f wff ta $.
	esylanr1_0 $e |- ( ph -> ch ) $.
	esylanr1_1 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
	sylanr1 $p |- ( ( ps /\ ( ph /\ th ) ) -> ta ) $= fsylanr1_0 fsylanr1_3 wa fsylanr1_1 fsylanr1_2 fsylanr1_3 wa fsylanr1_4 fsylanr1_0 fsylanr1_2 fsylanr1_3 esylanr1_0 anim1i esylanr1_1 sylan2 $.
$}
$( A syllogism inference.  (Contributed by NM, 9-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylanr2_0 $f wff ph $.
	fsylanr2_1 $f wff ps $.
	fsylanr2_2 $f wff ch $.
	fsylanr2_3 $f wff th $.
	fsylanr2_4 $f wff ta $.
	esylanr2_0 $e |- ( ph -> th ) $.
	esylanr2_1 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
	sylanr2 $p |- ( ( ps /\ ( ch /\ ph ) ) -> ta ) $= fsylanr2_2 fsylanr2_0 wa fsylanr2_1 fsylanr2_2 fsylanr2_3 wa fsylanr2_4 fsylanr2_0 fsylanr2_3 fsylanr2_2 esylanr2_0 anim2i esylanr2_1 sylan2 $.
$}
$( A syllogism inference.  (Contributed by NM, 2-May-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylani_0 $f wff ph $.
	fsylani_1 $f wff ps $.
	fsylani_2 $f wff ch $.
	fsylani_3 $f wff th $.
	fsylani_4 $f wff ta $.
	esylani_0 $e |- ( ph -> ch ) $.
	esylani_1 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
	sylani $p |- ( ps -> ( ( ph /\ th ) -> ta ) ) $= fsylani_1 fsylani_0 fsylani_2 fsylani_3 fsylani_4 fsylani_0 fsylani_2 wi fsylani_1 esylani_0 a1i esylani_1 syland $.
$}
$( A syllogism inference.  (Contributed by NM, 1-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylan2i_0 $f wff ph $.
	fsylan2i_1 $f wff ps $.
	fsylan2i_2 $f wff ch $.
	fsylan2i_3 $f wff th $.
	fsylan2i_4 $f wff ta $.
	esylan2i_0 $e |- ( ph -> th ) $.
	esylan2i_1 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
	sylan2i $p |- ( ps -> ( ( ch /\ ph ) -> ta ) ) $= fsylan2i_1 fsylan2i_0 fsylan2i_3 fsylan2i_2 fsylan2i_4 fsylan2i_0 fsylan2i_3 wi fsylan2i_1 esylan2i_0 a1i esylan2i_1 sylan2d $.
$}
$( A syllogism inference.  (Contributed by NM, 3-Aug-1999.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl2ani_0 $f wff ph $.
	fsyl2ani_1 $f wff ps $.
	fsyl2ani_2 $f wff ch $.
	fsyl2ani_3 $f wff th $.
	fsyl2ani_4 $f wff ta $.
	fsyl2ani_5 $f wff et $.
	esyl2ani_0 $e |- ( ph -> ch ) $.
	esyl2ani_1 $e |- ( et -> th ) $.
	esyl2ani_2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
	syl2ani $p |- ( ps -> ( ( ph /\ et ) -> ta ) ) $= fsyl2ani_0 fsyl2ani_1 fsyl2ani_2 fsyl2ani_5 fsyl2ani_4 esyl2ani_0 fsyl2ani_5 fsyl2ani_1 fsyl2ani_2 fsyl2ani_3 fsyl2ani_4 esyl2ani_1 esyl2ani_2 sylan2i sylani $.
$}
$( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylan9_0 $f wff ph $.
	fsylan9_1 $f wff ps $.
	fsylan9_2 $f wff ch $.
	fsylan9_3 $f wff th $.
	fsylan9_4 $f wff ta $.
	esylan9_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esylan9_1 $e |- ( th -> ( ch -> ta ) ) $.
	sylan9 $p |- ( ( ph /\ th ) -> ( ps -> ta ) ) $= fsylan9_0 fsylan9_3 fsylan9_1 fsylan9_4 wi fsylan9_0 fsylan9_1 fsylan9_2 fsylan9_3 fsylan9_4 esylan9_0 esylan9_1 syl9 imp $.
$}
$( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylan9r_0 $f wff ph $.
	fsylan9r_1 $f wff ps $.
	fsylan9r_2 $f wff ch $.
	fsylan9r_3 $f wff th $.
	fsylan9r_4 $f wff ta $.
	esylan9r_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esylan9r_1 $e |- ( th -> ( ch -> ta ) ) $.
	sylan9r $p |- ( ( th /\ ph ) -> ( ps -> ta ) ) $= fsylan9r_3 fsylan9r_0 fsylan9r_1 fsylan9r_4 wi fsylan9r_0 fsylan9r_1 fsylan9r_2 fsylan9r_3 fsylan9r_4 esylan9r_0 esylan9r_1 syl9r imp $.
$}
$( A modus tollens deduction.  (Contributed by Jeff Hankins,
       19-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmtand_0 $f wff ph $.
	fmtand_1 $f wff ps $.
	fmtand_2 $f wff ch $.
	emtand_0 $e |- ( ph -> -. ch ) $.
	emtand_1 $e |- ( ( ph /\ ps ) -> ch ) $.
	mtand $p |- ( ph -> -. ps ) $= fmtand_0 fmtand_1 fmtand_2 emtand_0 fmtand_0 fmtand_1 fmtand_2 emtand_1 ex mtod $.
$}
$( A modus tollens deduction involving disjunction.  (Contributed by Jeff
       Hankins, 15-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmtord_0 $f wff ph $.
	fmtord_1 $f wff ps $.
	fmtord_2 $f wff ch $.
	fmtord_3 $f wff th $.
	emtord_0 $e |- ( ph -> -. ch ) $.
	emtord_1 $e |- ( ph -> -. th ) $.
	emtord_2 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
	mtord $p |- ( ph -> -. ps ) $= fmtord_0 fmtord_1 fmtord_3 emtord_1 fmtord_0 fmtord_1 fmtord_2 wn fmtord_3 emtord_0 fmtord_0 fmtord_1 fmtord_2 fmtord_3 wo fmtord_2 wn fmtord_3 wi emtord_2 fmtord_2 fmtord_3 df-or syl6ib mpid mtod $.
$}
$( Syllogism inference combined with contraction.  (Contributed by NM,
       16-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsyl2anc_0 $f wff ph $.
	fsyl2anc_1 $f wff ps $.
	fsyl2anc_2 $f wff ch $.
	fsyl2anc_3 $f wff th $.
	esyl2anc_0 $e |- ( ph -> ps ) $.
	esyl2anc_1 $e |- ( ph -> ch ) $.
	esyl2anc_2 $e |- ( ( ps /\ ch ) -> th ) $.
	syl2anc $p |- ( ph -> th ) $= fsyl2anc_0 fsyl2anc_1 fsyl2anc_2 fsyl2anc_3 esyl2anc_0 esyl2anc_1 fsyl2anc_1 fsyl2anc_2 fsyl2anc_3 esyl2anc_2 ex sylc $.
$}
$( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylancl_0 $f wff ph $.
	fsylancl_1 $f wff ps $.
	fsylancl_2 $f wff ch $.
	fsylancl_3 $f wff th $.
	esylancl_0 $e |- ( ph -> ps ) $.
	esylancl_1 $e |- ch $.
	esylancl_2 $e |- ( ( ps /\ ch ) -> th ) $.
	sylancl $p |- ( ph -> th ) $= fsylancl_0 fsylancl_1 fsylancl_2 fsylancl_3 esylancl_0 fsylancl_2 fsylancl_0 esylancl_1 a1i esylancl_2 syl2anc $.
$}
$( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylancr_0 $f wff ph $.
	fsylancr_1 $f wff ps $.
	fsylancr_2 $f wff ch $.
	fsylancr_3 $f wff th $.
	esylancr_0 $e |- ps $.
	esylancr_1 $e |- ( ph -> ch ) $.
	esylancr_2 $e |- ( ( ps /\ ch ) -> th ) $.
	sylancr $p |- ( ph -> th ) $= fsylancr_0 fsylancr_1 fsylancr_2 fsylancr_3 fsylancr_1 fsylancr_0 esylancr_0 a1i esylancr_1 esylancr_2 syl2anc $.
$}
$( Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylanbrc_0 $f wff ph $.
	fsylanbrc_1 $f wff ps $.
	fsylanbrc_2 $f wff ch $.
	fsylanbrc_3 $f wff th $.
	esylanbrc_0 $e |- ( ph -> ps ) $.
	esylanbrc_1 $e |- ( ph -> ch ) $.
	esylanbrc_2 $e |- ( th <-> ( ps /\ ch ) ) $.
	sylanbrc $p |- ( ph -> th ) $= fsylanbrc_0 fsylanbrc_1 fsylanbrc_2 wa fsylanbrc_3 fsylanbrc_0 fsylanbrc_1 fsylanbrc_2 esylanbrc_0 esylanbrc_1 jca esylanbrc_2 sylibr $.
$}
$( A syllogism inference combined with contraction.  (Contributed by NM,
       3-Sep-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylancb_0 $f wff ph $.
	fsylancb_1 $f wff ps $.
	fsylancb_2 $f wff ch $.
	fsylancb_3 $f wff th $.
	esylancb_0 $e |- ( ph <-> ps ) $.
	esylancb_1 $e |- ( ph <-> ch ) $.
	esylancb_2 $e |- ( ( ps /\ ch ) -> th ) $.
	sylancb $p |- ( ph -> th ) $= fsylancb_0 fsylancb_3 fsylancb_0 fsylancb_1 fsylancb_2 fsylancb_3 fsylancb_0 esylancb_0 esylancb_1 esylancb_2 syl2anb anidms $.
$}
$( A syllogism inference combined with contraction.  (Contributed by NM,
       3-Sep-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylancbr_0 $f wff ph $.
	fsylancbr_1 $f wff ps $.
	fsylancbr_2 $f wff ch $.
	fsylancbr_3 $f wff th $.
	esylancbr_0 $e |- ( ps <-> ph ) $.
	esylancbr_1 $e |- ( ch <-> ph ) $.
	esylancbr_2 $e |- ( ( ps /\ ch ) -> th ) $.
	sylancbr $p |- ( ph -> th ) $= fsylancbr_0 fsylancbr_3 fsylancbr_0 fsylancbr_1 fsylancbr_2 fsylancbr_3 fsylancbr_0 esylancbr_0 esylancbr_1 esylancbr_2 syl2anbr anidms $.
$}
$( Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 2-Jul-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsylancom_0 $f wff ph $.
	fsylancom_1 $f wff ps $.
	fsylancom_2 $f wff ch $.
	fsylancom_3 $f wff th $.
	esylancom_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	esylancom_1 $e |- ( ( ch /\ ps ) -> th ) $.
	sylancom $p |- ( ( ph /\ ps ) -> th ) $= fsylancom_0 fsylancom_1 wa fsylancom_2 fsylancom_1 fsylancom_3 esylancom_0 fsylancom_0 fsylancom_1 simpr esylancom_1 syl2anc $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 23-May-1999.)
       (Proof shortened by Wolf Lammen, 22-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmpdan_0 $f wff ph $.
	fmpdan_1 $f wff ps $.
	fmpdan_2 $f wff ch $.
	empdan_0 $e |- ( ph -> ps ) $.
	empdan_1 $e |- ( ( ph /\ ps ) -> ch ) $.
	mpdan $p |- ( ph -> ch ) $= fmpdan_0 fmpdan_0 fmpdan_1 fmpdan_2 fmpdan_0 id empdan_0 empdan_1 syl2anc $.
$}
$( An inference based on modus ponens with commutation of antecedents.
       (Contributed by NM, 28-Oct-2003.)  (Proof shortened by Wolf Lammen,
       7-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmpancom_0 $f wff ph $.
	fmpancom_1 $f wff ps $.
	fmpancom_2 $f wff ch $.
	empancom_0 $e |- ( ps -> ph ) $.
	empancom_1 $e |- ( ( ph /\ ps ) -> ch ) $.
	mpancom $p |- ( ps -> ch ) $= fmpancom_1 fmpancom_0 fmpancom_1 fmpancom_2 empancom_0 fmpancom_1 id empancom_1 syl2anc $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 30-Aug-1993.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmpan_0 $f wff ph $.
	fmpan_1 $f wff ps $.
	fmpan_2 $f wff ch $.
	empan_0 $e |- ph $.
	empan_1 $e |- ( ( ph /\ ps ) -> ch ) $.
	mpan $p |- ( ps -> ch ) $= fmpan_0 fmpan_1 fmpan_2 fmpan_0 fmpan_1 empan_0 a1i empan_1 mpancom $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 16-Sep-1993.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmpan2_0 $f wff ph $.
	fmpan2_1 $f wff ps $.
	fmpan2_2 $f wff ch $.
	empan2_0 $e |- ps $.
	empan2_1 $e |- ( ( ph /\ ps ) -> ch ) $.
	mpan2 $p |- ( ph -> ch ) $= fmpan2_0 fmpan2_1 fmpan2_2 fmpan2_1 fmpan2_0 empan2_0 a1i empan2_1 mpdan $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       13-Apr-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmp2an_0 $f wff ph $.
	fmp2an_1 $f wff ps $.
	fmp2an_2 $f wff ch $.
	emp2an_0 $e |- ph $.
	emp2an_1 $e |- ps $.
	emp2an_2 $e |- ( ( ph /\ ps ) -> ch ) $.
	mp2an $p |- ch $= fmp2an_1 fmp2an_2 emp2an_1 fmp2an_0 fmp2an_1 fmp2an_2 emp2an_0 emp2an_2 mpan ax-mp $.
$}
$( An inference based on modus ponens.  (Contributed by Jeff Madsen,
       15-Jun-2010.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp4an_0 $f wff ph $.
	fmp4an_1 $f wff ps $.
	fmp4an_2 $f wff ch $.
	fmp4an_3 $f wff th $.
	fmp4an_4 $f wff ta $.
	emp4an_0 $e |- ph $.
	emp4an_1 $e |- ps $.
	emp4an_2 $e |- ch $.
	emp4an_3 $e |- th $.
	emp4an_4 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
	mp4an $p |- ta $= fmp4an_0 fmp4an_1 wa fmp4an_2 fmp4an_3 wa fmp4an_4 fmp4an_0 fmp4an_1 emp4an_0 emp4an_1 pm3.2i fmp4an_2 fmp4an_3 emp4an_2 emp4an_3 pm3.2i emp4an_4 mp2an $.
$}
$( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpan2d_0 $f wff ph $.
	fmpan2d_1 $f wff ps $.
	fmpan2d_2 $f wff ch $.
	fmpan2d_3 $f wff th $.
	empan2d_0 $e |- ( ph -> ch ) $.
	empan2d_1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	mpan2d $p |- ( ph -> ( ps -> th ) ) $= fmpan2d_0 fmpan2d_1 fmpan2d_2 fmpan2d_3 empan2d_0 fmpan2d_0 fmpan2d_1 fmpan2d_2 fmpan2d_3 empan2d_1 exp3a mpid $.
$}
$( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpand_0 $f wff ph $.
	fmpand_1 $f wff ps $.
	fmpand_2 $f wff ch $.
	fmpand_3 $f wff th $.
	empand_0 $e |- ( ph -> ps ) $.
	empand_1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	mpand $p |- ( ph -> ( ch -> th ) ) $= fmpand_0 fmpand_2 fmpand_1 fmpand_3 empand_0 fmpand_0 fmpand_1 fmpand_2 fmpand_3 empand_1 ancomsd mpan2d $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 10-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpani_0 $f wff ph $.
	fmpani_1 $f wff ps $.
	fmpani_2 $f wff ch $.
	fmpani_3 $f wff th $.
	empani_0 $e |- ps $.
	empani_1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	mpani $p |- ( ph -> ( ch -> th ) ) $= fmpani_0 fmpani_1 fmpani_2 fmpani_3 fmpani_1 fmpani_0 empani_0 a1i empani_1 mpand $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 10-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpan2i_0 $f wff ph $.
	fmpan2i_1 $f wff ps $.
	fmpan2i_2 $f wff ch $.
	fmpan2i_3 $f wff th $.
	empan2i_0 $e |- ch $.
	empan2i_1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	mpan2i $p |- ( ph -> ( ps -> th ) ) $= fmpan2i_0 fmpan2i_1 fmpan2i_2 fmpan2i_3 fmpan2i_2 fmpan2i_0 empan2i_0 a1i empan2i_1 mpan2d $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       12-Dec-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp2ani_0 $f wff ph $.
	fmp2ani_1 $f wff ps $.
	fmp2ani_2 $f wff ch $.
	fmp2ani_3 $f wff th $.
	emp2ani_0 $e |- ps $.
	emp2ani_1 $e |- ch $.
	emp2ani_2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	mp2ani $p |- ( ph -> th ) $= fmp2ani_0 fmp2ani_2 fmp2ani_3 emp2ani_1 fmp2ani_0 fmp2ani_1 fmp2ani_2 fmp2ani_3 emp2ani_0 emp2ani_2 mpani mpi $.
$}
$( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp2and_0 $f wff ph $.
	fmp2and_1 $f wff ps $.
	fmp2and_2 $f wff ch $.
	fmp2and_3 $f wff th $.
	emp2and_0 $e |- ( ph -> ps ) $.
	emp2and_1 $e |- ( ph -> ch ) $.
	emp2and_2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	mp2and $p |- ( ph -> th ) $= fmp2and_0 fmp2and_2 fmp2and_3 emp2and_1 fmp2and_0 fmp2and_1 fmp2and_2 fmp2and_3 emp2and_0 emp2and_2 mpand mpd $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 16-Aug-1994.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpanl1_0 $f wff ph $.
	fmpanl1_1 $f wff ps $.
	fmpanl1_2 $f wff ch $.
	fmpanl1_3 $f wff th $.
	empanl1_0 $e |- ph $.
	empanl1_1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	mpanl1 $p |- ( ( ps /\ ch ) -> th ) $= fmpanl1_1 fmpanl1_0 fmpanl1_1 wa fmpanl1_2 fmpanl1_3 fmpanl1_1 fmpanl1_0 empanl1_0 jctl empanl1_1 sylan $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 16-Aug-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpanl2_0 $f wff ph $.
	fmpanl2_1 $f wff ps $.
	fmpanl2_2 $f wff ch $.
	fmpanl2_3 $f wff th $.
	empanl2_0 $e |- ps $.
	empanl2_1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	mpanl2 $p |- ( ( ph /\ ch ) -> th ) $= fmpanl2_0 fmpanl2_0 fmpanl2_1 wa fmpanl2_2 fmpanl2_3 fmpanl2_0 fmpanl2_1 empanl2_0 jctr empanl2_1 sylan $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       13-Jul-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpanl12_0 $f wff ph $.
	fmpanl12_1 $f wff ps $.
	fmpanl12_2 $f wff ch $.
	fmpanl12_3 $f wff th $.
	empanl12_0 $e |- ph $.
	empanl12_1 $e |- ps $.
	empanl12_2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	mpanl12 $p |- ( ch -> th ) $= fmpanl12_1 fmpanl12_2 fmpanl12_3 empanl12_1 fmpanl12_0 fmpanl12_1 fmpanl12_2 fmpanl12_3 empanl12_0 empanl12_2 mpanl1 mpan $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 3-May-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpanr1_0 $f wff ph $.
	fmpanr1_1 $f wff ps $.
	fmpanr1_2 $f wff ch $.
	fmpanr1_3 $f wff th $.
	empanr1_0 $e |- ps $.
	empanr1_1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	mpanr1 $p |- ( ( ph /\ ch ) -> th ) $= fmpanr1_0 fmpanr1_1 fmpanr1_2 fmpanr1_3 empanr1_0 fmpanr1_0 fmpanr1_1 fmpanr1_2 fmpanr1_3 empanr1_1 anassrs mpanl2 $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 3-May-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof shortened by
       Wolf Lammen, 7-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpanr2_0 $f wff ph $.
	fmpanr2_1 $f wff ps $.
	fmpanr2_2 $f wff ch $.
	fmpanr2_3 $f wff th $.
	empanr2_0 $e |- ch $.
	empanr2_1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	mpanr2 $p |- ( ( ph /\ ps ) -> th ) $= fmpanr2_1 fmpanr2_0 fmpanr2_1 fmpanr2_2 wa fmpanr2_3 fmpanr2_1 fmpanr2_2 empanr2_0 jctr empanr2_1 sylan2 $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       24-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpanr12_0 $f wff ph $.
	fmpanr12_1 $f wff ps $.
	fmpanr12_2 $f wff ch $.
	fmpanr12_3 $f wff th $.
	empanr12_0 $e |- ps $.
	empanr12_1 $e |- ch $.
	empanr12_2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	mpanr12 $p |- ( ph -> th ) $= fmpanr12_0 fmpanr12_2 fmpanr12_3 empanr12_1 fmpanr12_0 fmpanr12_1 fmpanr12_2 fmpanr12_3 empanr12_0 empanr12_2 mpanr1 mpan2 $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 30-Dec-2004.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmpanlr1_0 $f wff ph $.
	fmpanlr1_1 $f wff ps $.
	fmpanlr1_2 $f wff ch $.
	fmpanlr1_3 $f wff th $.
	fmpanlr1_4 $f wff ta $.
	empanlr1_0 $e |- ps $.
	empanlr1_1 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
	mpanlr1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $= fmpanlr1_2 fmpanlr1_0 fmpanlr1_1 fmpanlr1_2 wa fmpanlr1_3 fmpanlr1_4 fmpanlr1_2 fmpanlr1_1 empanlr1_0 jctl empanlr1_1 sylanl2 $.
$}
$( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 4-May-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm5.74da_0 $f wff ph $.
	fpm5.74da_1 $f wff ps $.
	fpm5.74da_2 $f wff ch $.
	fpm5.74da_3 $f wff th $.
	epm5.74da_0 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	pm5.74da $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $= fpm5.74da_0 fpm5.74da_1 fpm5.74da_2 fpm5.74da_3 fpm5.74da_0 fpm5.74da_1 fpm5.74da_2 fpm5.74da_3 wb epm5.74da_0 ex pm5.74d $.
$}
$( Theorem *4.45 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm4.45_0 $f wff ph $.
	fpm4.45_1 $f wff ps $.
	pm4.45 $p |- ( ph <-> ( ph /\ ( ph \/ ps ) ) ) $= fpm4.45_0 fpm4.45_0 fpm4.45_1 wo fpm4.45_0 fpm4.45_1 orc pm4.71i $.
$}
$( Distribution of implication with conjunction.  (Contributed by NM,
     31-May-1999.)  (Proof shortened by Wolf Lammen, 6-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimdistan_0 $f wff ph $.
	fimdistan_1 $f wff ps $.
	fimdistan_2 $f wff ch $.
	imdistan $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $= fimdistan_0 fimdistan_1 fimdistan_2 wi wi fimdistan_0 fimdistan_1 fimdistan_0 fimdistan_2 wa wi wi fimdistan_0 fimdistan_1 wa fimdistan_0 fimdistan_2 wa wi fimdistan_0 fimdistan_1 fimdistan_2 pm5.42 fimdistan_0 fimdistan_1 fimdistan_0 fimdistan_2 wa impexp bitr4i $.
$}
$( Distribution of implication with conjunction.  (Contributed by NM,
       1-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimdistani_0 $f wff ph $.
	fimdistani_1 $f wff ps $.
	fimdistani_2 $f wff ch $.
	eimdistani_0 $e |- ( ph -> ( ps -> ch ) ) $.
	imdistani $p |- ( ( ph /\ ps ) -> ( ph /\ ch ) ) $= fimdistani_0 fimdistani_1 fimdistani_0 fimdistani_2 wa fimdistani_0 fimdistani_1 fimdistani_2 eimdistani_0 anc2li imp $.
$}
$( Distribution of implication with conjunction.  (Contributed by NM,
       8-Jan-2002.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimdistanri_0 $f wff ph $.
	fimdistanri_1 $f wff ps $.
	fimdistanri_2 $f wff ch $.
	eimdistanri_0 $e |- ( ph -> ( ps -> ch ) ) $.
	imdistanri $p |- ( ( ps /\ ph ) -> ( ch /\ ph ) ) $= fimdistanri_1 fimdistanri_0 fimdistanri_2 fimdistanri_0 fimdistanri_1 fimdistanri_2 eimdistanri_0 com12 impac $.
$}
$( Distribution of implication with conjunction (deduction rule).
       (Contributed by NM, 27-Aug-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fimdistand_0 $f wff ph $.
	fimdistand_1 $f wff ps $.
	fimdistand_2 $f wff ch $.
	fimdistand_3 $f wff th $.
	eimdistand_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	imdistand $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $= fimdistand_0 fimdistand_1 fimdistand_2 fimdistand_3 wi wi fimdistand_1 fimdistand_2 wa fimdistand_1 fimdistand_3 wa wi eimdistand_0 fimdistand_1 fimdistand_2 fimdistand_3 imdistan sylib $.
$}
$( Distribution of implication with conjunction (deduction version with
       conjoined antecedent).  (Contributed by Jeff Madsen, 19-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fimdistanda_0 $f wff ph $.
	fimdistanda_1 $f wff ps $.
	fimdistanda_2 $f wff ch $.
	fimdistanda_3 $f wff th $.
	eimdistanda_0 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	imdistanda $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $= fimdistanda_0 fimdistanda_1 fimdistanda_2 fimdistanda_3 fimdistanda_0 fimdistanda_1 fimdistanda_2 fimdistanda_3 wi eimdistanda_0 ex imdistand $.
$}
$( Introduce a left conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanbi2i_0 $f wff ph $.
	fanbi2i_1 $f wff ps $.
	fanbi2i_2 $f wff ch $.
	eanbi2i_0 $e |- ( ph <-> ps ) $.
	anbi2i $p |- ( ( ch /\ ph ) <-> ( ch /\ ps ) ) $= fanbi2i_2 fanbi2i_0 fanbi2i_1 fanbi2i_0 fanbi2i_1 wb fanbi2i_2 eanbi2i_0 a1i pm5.32i $.
$}
$( Introduce a right conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanbi1i_0 $f wff ph $.
	fanbi1i_1 $f wff ps $.
	fanbi1i_2 $f wff ch $.
	eanbi1i_0 $e |- ( ph <-> ps ) $.
	anbi1i $p |- ( ( ph /\ ch ) <-> ( ps /\ ch ) ) $= fanbi1i_2 fanbi1i_0 fanbi1i_1 fanbi1i_0 fanbi1i_1 wb fanbi1i_2 eanbi1i_0 a1i pm5.32ri $.
$}
$( Variant of ~ anbi2i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanbi2ci_0 $f wff ph $.
	fanbi2ci_1 $f wff ps $.
	fanbi2ci_2 $f wff ch $.
	eanbi2ci_0 $e |- ( ph <-> ps ) $.
	anbi2ci $p |- ( ( ph /\ ch ) <-> ( ch /\ ps ) ) $= fanbi2ci_0 fanbi2ci_2 wa fanbi2ci_1 fanbi2ci_2 wa fanbi2ci_2 fanbi2ci_1 wa fanbi2ci_0 fanbi2ci_1 fanbi2ci_2 eanbi2ci_0 anbi1i fanbi2ci_1 fanbi2ci_2 ancom bitri $.
$}
$( Conjoin both sides of two equivalences.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanbi12i_0 $f wff ph $.
	fanbi12i_1 $f wff ps $.
	fanbi12i_2 $f wff ch $.
	fanbi12i_3 $f wff th $.
	eanbi12i_0 $e |- ( ph <-> ps ) $.
	eanbi12i_1 $e |- ( ch <-> th ) $.
	anbi12i $p |- ( ( ph /\ ch ) <-> ( ps /\ th ) ) $= fanbi12i_0 fanbi12i_2 wa fanbi12i_1 fanbi12i_2 wa fanbi12i_1 fanbi12i_3 wa fanbi12i_0 fanbi12i_1 fanbi12i_2 eanbi12i_0 anbi1i fanbi12i_2 fanbi12i_3 fanbi12i_1 eanbi12i_1 anbi2i bitri $.
$}
$( Variant of ~ anbi12i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanbi12ci_0 $f wff ph $.
	fanbi12ci_1 $f wff ps $.
	fanbi12ci_2 $f wff ch $.
	fanbi12ci_3 $f wff th $.
	eanbi12ci_0 $e |- ( ph <-> ps ) $.
	eanbi12ci_1 $e |- ( ch <-> th ) $.
	anbi12ci $p |- ( ( ph /\ ch ) <-> ( th /\ ps ) ) $= fanbi12ci_0 fanbi12ci_2 wa fanbi12ci_1 fanbi12ci_3 wa fanbi12ci_3 fanbi12ci_1 wa fanbi12ci_0 fanbi12ci_1 fanbi12ci_2 fanbi12ci_3 eanbi12ci_0 eanbi12ci_1 anbi12i fanbi12ci_1 fanbi12ci_3 ancom bitri $.
$}
$( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylan9bb_0 $f wff ph $.
	fsylan9bb_1 $f wff ps $.
	fsylan9bb_2 $f wff ch $.
	fsylan9bb_3 $f wff th $.
	fsylan9bb_4 $f wff ta $.
	esylan9bb_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esylan9bb_1 $e |- ( th -> ( ch <-> ta ) ) $.
	sylan9bb $p |- ( ( ph /\ th ) -> ( ps <-> ta ) ) $= fsylan9bb_0 fsylan9bb_3 wa fsylan9bb_1 fsylan9bb_2 fsylan9bb_4 fsylan9bb_0 fsylan9bb_1 fsylan9bb_2 wb fsylan9bb_3 esylan9bb_0 adantr fsylan9bb_3 fsylan9bb_2 fsylan9bb_4 wb fsylan9bb_0 esylan9bb_1 adantl bitrd $.
$}
$( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsylan9bbr_0 $f wff ph $.
	fsylan9bbr_1 $f wff ps $.
	fsylan9bbr_2 $f wff ch $.
	fsylan9bbr_3 $f wff th $.
	fsylan9bbr_4 $f wff ta $.
	esylan9bbr_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esylan9bbr_1 $e |- ( th -> ( ch <-> ta ) ) $.
	sylan9bbr $p |- ( ( th /\ ph ) -> ( ps <-> ta ) ) $= fsylan9bbr_0 fsylan9bbr_3 fsylan9bbr_1 fsylan9bbr_4 wb fsylan9bbr_0 fsylan9bbr_1 fsylan9bbr_2 fsylan9bbr_3 fsylan9bbr_4 esylan9bbr_0 esylan9bbr_1 sylan9bb ancoms $.
$}
$( Deduction adding a left disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	forbi2d_0 $f wff ph $.
	forbi2d_1 $f wff ps $.
	forbi2d_2 $f wff ch $.
	forbi2d_3 $f wff th $.
	eorbi2d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	orbi2d $p |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) ) $= forbi2d_0 forbi2d_3 wn forbi2d_1 wi forbi2d_3 wn forbi2d_2 wi forbi2d_3 forbi2d_1 wo forbi2d_3 forbi2d_2 wo forbi2d_0 forbi2d_1 forbi2d_2 forbi2d_3 wn eorbi2d_0 imbi2d forbi2d_3 forbi2d_1 df-or forbi2d_3 forbi2d_2 df-or 3bitr4g $.
$}
$( Deduction adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	forbi1d_0 $f wff ph $.
	forbi1d_1 $f wff ps $.
	forbi1d_2 $f wff ch $.
	forbi1d_3 $f wff th $.
	eorbi1d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	orbi1d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) ) $= forbi1d_0 forbi1d_3 forbi1d_1 wo forbi1d_3 forbi1d_2 wo forbi1d_1 forbi1d_3 wo forbi1d_2 forbi1d_3 wo forbi1d_0 forbi1d_1 forbi1d_2 forbi1d_3 eorbi1d_0 orbi2d forbi1d_1 forbi1d_3 orcom forbi1d_2 forbi1d_3 orcom 3bitr4g $.
$}
$( Deduction adding a left conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanbi2d_0 $f wff ph $.
	fanbi2d_1 $f wff ps $.
	fanbi2d_2 $f wff ch $.
	fanbi2d_3 $f wff th $.
	eanbi2d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	anbi2d $p |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) ) $= fanbi2d_0 fanbi2d_3 fanbi2d_1 fanbi2d_2 fanbi2d_0 fanbi2d_1 fanbi2d_2 wb fanbi2d_3 eanbi2d_0 a1d pm5.32d $.
$}
$( Deduction adding a right conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanbi1d_0 $f wff ph $.
	fanbi1d_1 $f wff ps $.
	fanbi1d_2 $f wff ch $.
	fanbi1d_3 $f wff th $.
	eanbi1d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	anbi1d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) ) $= fanbi1d_0 fanbi1d_3 fanbi1d_1 fanbi1d_2 fanbi1d_0 fanbi1d_1 fanbi1d_2 wb fanbi1d_3 eanbi1d_0 a1d pm5.32rd $.
$}
$( Theorem *4.37 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forbi1_0 $f wff ph $.
	forbi1_1 $f wff ps $.
	forbi1_2 $f wff ch $.
	orbi1 $p |- ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $= forbi1_0 forbi1_1 wb forbi1_0 forbi1_1 forbi1_2 forbi1_0 forbi1_1 wb id orbi1d $.
$}
$( Introduce a right conjunct to both sides of a logical equivalence.
     Theorem *4.36 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanbi1_0 $f wff ph $.
	fanbi1_1 $f wff ps $.
	fanbi1_2 $f wff ch $.
	anbi1 $p |- ( ( ph <-> ps ) -> ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) $= fanbi1_0 fanbi1_1 wb fanbi1_0 fanbi1_1 fanbi1_2 fanbi1_0 fanbi1_1 wb id anbi1d $.
$}
$( Introduce a left conjunct to both sides of a logical equivalence.
     (Contributed by NM, 16-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanbi2_0 $f wff ph $.
	fanbi2_1 $f wff ps $.
	fanbi2_2 $f wff ch $.
	anbi2 $p |- ( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) ) $= fanbi2_0 fanbi2_1 wb fanbi2_0 fanbi2_1 fanbi2_2 fanbi2_0 fanbi2_1 wb id anbi2d $.
$}
$( Theorem *4.22 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbitr_0 $f wff ph $.
	fbitr_1 $f wff ps $.
	fbitr_2 $f wff ch $.
	bitr $p |- ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) ) $= fbitr_0 fbitr_1 wb fbitr_0 fbitr_2 wb fbitr_1 fbitr_2 wb fbitr_0 fbitr_1 fbitr_2 bibi1 biimpar $.
$}
$( Deduction joining two equivalences to form equivalence of disjunctions.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	forbi12d_0 $f wff ph $.
	forbi12d_1 $f wff ps $.
	forbi12d_2 $f wff ch $.
	forbi12d_3 $f wff th $.
	forbi12d_4 $f wff ta $.
	eorbi12d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	eorbi12d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	orbi12d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) ) $= forbi12d_0 forbi12d_1 forbi12d_3 wo forbi12d_2 forbi12d_3 wo forbi12d_2 forbi12d_4 wo forbi12d_0 forbi12d_1 forbi12d_2 forbi12d_3 eorbi12d_0 orbi1d forbi12d_0 forbi12d_3 forbi12d_4 forbi12d_2 eorbi12d_1 orbi2d bitrd $.
$}
$( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fanbi12d_0 $f wff ph $.
	fanbi12d_1 $f wff ps $.
	fanbi12d_2 $f wff ch $.
	fanbi12d_3 $f wff th $.
	fanbi12d_4 $f wff ta $.
	eanbi12d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	eanbi12d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	anbi12d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) ) $= fanbi12d_0 fanbi12d_1 fanbi12d_3 wa fanbi12d_2 fanbi12d_3 wa fanbi12d_2 fanbi12d_4 wa fanbi12d_0 fanbi12d_1 fanbi12d_2 fanbi12d_3 eanbi12d_0 anbi1d fanbi12d_0 fanbi12d_3 fanbi12d_4 fanbi12d_2 eanbi12d_1 anbi2d bitrd $.
$}
$( Theorem *5.3 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm5.3_0 $f wff ph $.
	fpm5.3_1 $f wff ps $.
	fpm5.3_2 $f wff ch $.
	pm5.3 $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $= fpm5.3_0 fpm5.3_1 wa fpm5.3_2 wi fpm5.3_0 fpm5.3_1 fpm5.3_2 wi wi fpm5.3_0 fpm5.3_1 wa fpm5.3_0 fpm5.3_2 wa wi fpm5.3_0 fpm5.3_1 fpm5.3_2 impexp fpm5.3_0 fpm5.3_1 fpm5.3_2 imdistan bitri $.
$}
$( Theorem *5.61 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 30-Jun-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm5.61_0 $f wff ph $.
	fpm5.61_1 $f wff ps $.
	pm5.61 $p |- ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) ) $= fpm5.61_1 wn fpm5.61_0 fpm5.61_1 wo fpm5.61_0 fpm5.61_1 wn fpm5.61_0 fpm5.61_1 fpm5.61_0 wo fpm5.61_0 fpm5.61_1 wo fpm5.61_1 fpm5.61_0 biorf fpm5.61_1 fpm5.61_0 orcom syl6rbb pm5.32ri $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fadantll_0 $f wff ph $.
	fadantll_1 $f wff ps $.
	fadantll_2 $f wff ch $.
	fadantll_3 $f wff th $.
	eadantll_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	adantll $p |- ( ( ( th /\ ph ) /\ ps ) -> ch ) $= fadantll_3 fadantll_0 wa fadantll_0 fadantll_1 fadantll_2 fadantll_3 fadantll_0 simpr eadantll_0 sylan $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fadantlr_0 $f wff ph $.
	fadantlr_1 $f wff ps $.
	fadantlr_2 $f wff ch $.
	fadantlr_3 $f wff th $.
	eadantlr_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	adantlr $p |- ( ( ( ph /\ th ) /\ ps ) -> ch ) $= fadantlr_0 fadantlr_3 wa fadantlr_0 fadantlr_1 fadantlr_2 fadantlr_0 fadantlr_3 simpl eadantlr_0 sylan $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fadantrl_0 $f wff ph $.
	fadantrl_1 $f wff ps $.
	fadantrl_2 $f wff ch $.
	fadantrl_3 $f wff th $.
	eadantrl_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	adantrl $p |- ( ( ph /\ ( th /\ ps ) ) -> ch ) $= fadantrl_3 fadantrl_1 wa fadantrl_0 fadantrl_1 fadantrl_2 fadantrl_3 fadantrl_1 simpr eadantrl_0 sylan2 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fadantrr_0 $f wff ph $.
	fadantrr_1 $f wff ps $.
	fadantrr_2 $f wff ch $.
	fadantrr_3 $f wff th $.
	eadantrr_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	adantrr $p |- ( ( ph /\ ( ps /\ th ) ) -> ch ) $= fadantrr_1 fadantrr_3 wa fadantrr_0 fadantrr_1 fadantrr_2 fadantrr_1 fadantrr_3 simpl eadantrr_0 sylan2 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 2-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fadantlll_0 $f wff ph $.
	fadantlll_1 $f wff ps $.
	fadantlll_2 $f wff ch $.
	fadantlll_3 $f wff th $.
	fadantlll_4 $f wff ta $.
	eadantlll_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	adantlll $p |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th ) $= fadantlll_4 fadantlll_0 wa fadantlll_0 fadantlll_1 fadantlll_2 fadantlll_3 fadantlll_4 fadantlll_0 simpr eadantlll_0 sylanl1 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fadantllr_0 $f wff ph $.
	fadantllr_1 $f wff ps $.
	fadantllr_2 $f wff ch $.
	fadantllr_3 $f wff th $.
	fadantllr_4 $f wff ta $.
	eadantllr_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	adantllr $p |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th ) $= fadantllr_0 fadantllr_4 wa fadantllr_0 fadantllr_1 fadantllr_2 fadantllr_3 fadantllr_0 fadantllr_4 simpl eadantllr_0 sylanl1 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fadantlrl_0 $f wff ph $.
	fadantlrl_1 $f wff ps $.
	fadantlrl_2 $f wff ch $.
	fadantlrl_3 $f wff th $.
	fadantlrl_4 $f wff ta $.
	eadantlrl_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	adantlrl $p |- ( ( ( ph /\ ( ta /\ ps ) ) /\ ch ) -> th ) $= fadantlrl_4 fadantlrl_1 wa fadantlrl_0 fadantlrl_1 fadantlrl_2 fadantlrl_3 fadantlrl_4 fadantlrl_1 simpr eadantlrl_0 sylanl2 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fadantlrr_0 $f wff ph $.
	fadantlrr_1 $f wff ps $.
	fadantlrr_2 $f wff ch $.
	fadantlrr_3 $f wff th $.
	fadantlrr_4 $f wff ta $.
	eadantlrr_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	adantlrr $p |- ( ( ( ph /\ ( ps /\ ta ) ) /\ ch ) -> th ) $= fadantlrr_1 fadantlrr_4 wa fadantlrr_0 fadantlrr_1 fadantlrr_2 fadantlrr_3 fadantlrr_1 fadantlrr_4 simpl eadantlrr_0 sylanl2 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fadantrll_0 $f wff ph $.
	fadantrll_1 $f wff ps $.
	fadantrll_2 $f wff ch $.
	fadantrll_3 $f wff th $.
	fadantrll_4 $f wff ta $.
	eadantrll_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	adantrll $p |- ( ( ph /\ ( ( ta /\ ps ) /\ ch ) ) -> th ) $= fadantrll_4 fadantrll_1 wa fadantrll_0 fadantrll_1 fadantrll_2 fadantrll_3 fadantrll_4 fadantrll_1 simpr eadantrll_0 sylanr1 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fadantrlr_0 $f wff ph $.
	fadantrlr_1 $f wff ps $.
	fadantrlr_2 $f wff ch $.
	fadantrlr_3 $f wff th $.
	fadantrlr_4 $f wff ta $.
	eadantrlr_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	adantrlr $p |- ( ( ph /\ ( ( ps /\ ta ) /\ ch ) ) -> th ) $= fadantrlr_1 fadantrlr_4 wa fadantrlr_0 fadantrlr_1 fadantrlr_2 fadantrlr_3 fadantrlr_1 fadantrlr_4 simpl eadantrlr_0 sylanr1 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fadantrrl_0 $f wff ph $.
	fadantrrl_1 $f wff ps $.
	fadantrrl_2 $f wff ch $.
	fadantrrl_3 $f wff th $.
	fadantrrl_4 $f wff ta $.
	eadantrrl_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	adantrrl $p |- ( ( ph /\ ( ps /\ ( ta /\ ch ) ) ) -> th ) $= fadantrrl_4 fadantrrl_2 wa fadantrrl_0 fadantrrl_1 fadantrrl_2 fadantrrl_3 fadantrrl_4 fadantrrl_2 simpr eadantrrl_0 sylanr2 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fadantrrr_0 $f wff ph $.
	fadantrrr_1 $f wff ps $.
	fadantrrr_2 $f wff ch $.
	fadantrrr_3 $f wff th $.
	fadantrrr_4 $f wff ta $.
	eadantrrr_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	adantrrr $p |- ( ( ph /\ ( ps /\ ( ch /\ ta ) ) ) -> th ) $= fadantrrr_2 fadantrrr_4 wa fadantrrr_0 fadantrrr_1 fadantrrr_2 fadantrrr_3 fadantrrr_2 fadantrrr_4 simpl eadantrrr_0 sylanr2 $.
$}
$( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fad2antrr_0 $f wff ph $.
	fad2antrr_1 $f wff ps $.
	fad2antrr_2 $f wff ch $.
	fad2antrr_3 $f wff th $.
	ead2antrr_0 $e |- ( ph -> ps ) $.
	ad2antrr $p |- ( ( ( ph /\ ch ) /\ th ) -> ps ) $= fad2antrr_0 fad2antrr_3 fad2antrr_1 fad2antrr_2 fad2antrr_0 fad2antrr_1 fad2antrr_3 ead2antrr_0 adantr adantlr $.
$}
$( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fad2antlr_0 $f wff ph $.
	fad2antlr_1 $f wff ps $.
	fad2antlr_2 $f wff ch $.
	fad2antlr_3 $f wff th $.
	ead2antlr_0 $e |- ( ph -> ps ) $.
	ad2antlr $p |- ( ( ( ch /\ ph ) /\ th ) -> ps ) $= fad2antlr_0 fad2antlr_3 fad2antlr_1 fad2antlr_2 fad2antlr_0 fad2antlr_1 fad2antlr_3 ead2antlr_0 adantr adantll $.
$}
$( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fad2antrl_0 $f wff ph $.
	fad2antrl_1 $f wff ps $.
	fad2antrl_2 $f wff ch $.
	fad2antrl_3 $f wff th $.
	ead2antrl_0 $e |- ( ph -> ps ) $.
	ad2antrl $p |- ( ( ch /\ ( ph /\ th ) ) -> ps ) $= fad2antrl_0 fad2antrl_3 wa fad2antrl_1 fad2antrl_2 fad2antrl_0 fad2antrl_1 fad2antrl_3 ead2antrl_0 adantr adantl $.
$}
$( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fad2antll_0 $f wff ph $.
	fad2antll_1 $f wff ps $.
	fad2antll_2 $f wff ch $.
	fad2antll_3 $f wff th $.
	ead2antll_0 $e |- ( ph -> ps ) $.
	ad2antll $p |- ( ( ch /\ ( th /\ ph ) ) -> ps ) $= fad2antll_3 fad2antll_0 wa fad2antll_1 fad2antll_2 fad2antll_0 fad2antll_1 fad2antll_3 ead2antll_0 adantl adantl $.
$}
$( Deduction adding three conjuncts to antecedent.  (Contributed by NM,
       28-Jul-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fad3antrrr_0 $f wff ph $.
	fad3antrrr_1 $f wff ps $.
	fad3antrrr_2 $f wff ch $.
	fad3antrrr_3 $f wff th $.
	fad3antrrr_4 $f wff ta $.
	ead3antrrr_0 $e |- ( ph -> ps ) $.
	ad3antrrr $p |- ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) -> ps ) $= fad3antrrr_0 fad3antrrr_2 wa fad3antrrr_1 fad3antrrr_3 fad3antrrr_4 fad3antrrr_0 fad3antrrr_1 fad3antrrr_2 ead3antrrr_0 adantr ad2antrr $.
$}
$( Deduction adding three conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fad3antlr_0 $f wff ph $.
	fad3antlr_1 $f wff ps $.
	fad3antlr_2 $f wff ch $.
	fad3antlr_3 $f wff th $.
	fad3antlr_4 $f wff ta $.
	ead3antlr_0 $e |- ( ph -> ps ) $.
	ad3antlr $p |- ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) -> ps ) $= fad3antlr_2 fad3antlr_0 wa fad3antlr_3 wa fad3antlr_1 fad3antlr_4 fad3antlr_0 fad3antlr_1 fad3antlr_2 fad3antlr_3 ead3antlr_0 ad2antlr adantr $.
$}
$( Deduction adding 4 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fad4antr_0 $f wff ph $.
	fad4antr_1 $f wff ps $.
	fad4antr_2 $f wff ch $.
	fad4antr_3 $f wff th $.
	fad4antr_4 $f wff ta $.
	fad4antr_5 $f wff et $.
	ead4antr_0 $e |- ( ph -> ps ) $.
	ad4antr $p |- ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) -> ps ) $= fad4antr_0 fad4antr_2 wa fad4antr_3 wa fad4antr_4 wa fad4antr_1 fad4antr_5 fad4antr_0 fad4antr_1 fad4antr_2 fad4antr_3 fad4antr_4 ead4antr_0 ad3antrrr adantr $.
$}
$( Deduction adding 4 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fad4antlr_0 $f wff ph $.
	fad4antlr_1 $f wff ps $.
	fad4antlr_2 $f wff ch $.
	fad4antlr_3 $f wff th $.
	fad4antlr_4 $f wff ta $.
	fad4antlr_5 $f wff et $.
	ead4antlr_0 $e |- ( ph -> ps ) $.
	ad4antlr $p |- ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) -> ps ) $= fad4antlr_2 fad4antlr_0 wa fad4antlr_3 wa fad4antlr_4 wa fad4antlr_1 fad4antlr_5 fad4antlr_0 fad4antlr_1 fad4antlr_2 fad4antlr_3 fad4antlr_4 ead4antlr_0 ad3antlr adantr $.
$}
$( Deduction adding 5 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fad5antr_0 $f wff ph $.
	fad5antr_1 $f wff ps $.
	fad5antr_2 $f wff ch $.
	fad5antr_3 $f wff th $.
	fad5antr_4 $f wff ta $.
	fad5antr_5 $f wff et $.
	fad5antr_6 $f wff ze $.
	ead5antr_0 $e |- ( ph -> ps ) $.
	ad5antr $p |- ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ps ) $= fad5antr_0 fad5antr_2 wa fad5antr_3 wa fad5antr_4 wa fad5antr_5 wa fad5antr_1 fad5antr_6 fad5antr_0 fad5antr_1 fad5antr_2 fad5antr_3 fad5antr_4 fad5antr_5 ead5antr_0 ad4antr adantr $.
$}
$( Deduction adding 5 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fad5antlr_0 $f wff ph $.
	fad5antlr_1 $f wff ps $.
	fad5antlr_2 $f wff ch $.
	fad5antlr_3 $f wff th $.
	fad5antlr_4 $f wff ta $.
	fad5antlr_5 $f wff et $.
	fad5antlr_6 $f wff ze $.
	ead5antlr_0 $e |- ( ph -> ps ) $.
	ad5antlr $p |- ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ps ) $= fad5antlr_2 fad5antlr_0 wa fad5antlr_3 wa fad5antlr_4 wa fad5antlr_5 wa fad5antlr_1 fad5antlr_6 fad5antlr_0 fad5antlr_1 fad5antlr_2 fad5antlr_3 fad5antlr_4 fad5antlr_5 ead5antlr_0 ad4antlr adantr $.
$}
$( Deduction adding 6 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fad6antr_0 $f wff ph $.
	fad6antr_1 $f wff ps $.
	fad6antr_2 $f wff ch $.
	fad6antr_3 $f wff th $.
	fad6antr_4 $f wff ta $.
	fad6antr_5 $f wff et $.
	fad6antr_6 $f wff ze $.
	fad6antr_7 $f wff si $.
	ead6antr_0 $e |- ( ph -> ps ) $.
	ad6antr $p |- ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps ) $= fad6antr_0 fad6antr_2 wa fad6antr_3 wa fad6antr_4 wa fad6antr_5 wa fad6antr_6 wa fad6antr_1 fad6antr_7 fad6antr_0 fad6antr_1 fad6antr_2 fad6antr_3 fad6antr_4 fad6antr_5 fad6antr_6 ead6antr_0 ad5antr adantr $.
$}
$( Deduction adding 6 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fad6antlr_0 $f wff ph $.
	fad6antlr_1 $f wff ps $.
	fad6antlr_2 $f wff ch $.
	fad6antlr_3 $f wff th $.
	fad6antlr_4 $f wff ta $.
	fad6antlr_5 $f wff et $.
	fad6antlr_6 $f wff ze $.
	fad6antlr_7 $f wff si $.
	ead6antlr_0 $e |- ( ph -> ps ) $.
	ad6antlr $p |- ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps ) $= fad6antlr_2 fad6antlr_0 wa fad6antlr_3 wa fad6antlr_4 wa fad6antlr_5 wa fad6antlr_6 wa fad6antlr_1 fad6antlr_7 fad6antlr_0 fad6antlr_1 fad6antlr_2 fad6antlr_3 fad6antlr_4 fad6antlr_5 fad6antlr_6 ead6antlr_0 ad5antlr adantr $.
$}
$( Deduction adding 7 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fad7antr_0 $f wff ph $.
	fad7antr_1 $f wff ps $.
	fad7antr_2 $f wff ch $.
	fad7antr_3 $f wff th $.
	fad7antr_4 $f wff ta $.
	fad7antr_5 $f wff et $.
	fad7antr_6 $f wff ze $.
	fad7antr_7 $f wff si $.
	fad7antr_8 $f wff rh $.
	ead7antr_0 $e |- ( ph -> ps ) $.
	ad7antr $p |- ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps ) $= fad7antr_0 fad7antr_2 wa fad7antr_3 wa fad7antr_4 wa fad7antr_5 wa fad7antr_6 wa fad7antr_7 wa fad7antr_1 fad7antr_8 fad7antr_0 fad7antr_1 fad7antr_2 fad7antr_3 fad7antr_4 fad7antr_5 fad7antr_6 fad7antr_7 ead7antr_0 ad6antr adantr $.
$}
$( Deduction adding 7 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fad7antlr_0 $f wff ph $.
	fad7antlr_1 $f wff ps $.
	fad7antlr_2 $f wff ch $.
	fad7antlr_3 $f wff th $.
	fad7antlr_4 $f wff ta $.
	fad7antlr_5 $f wff et $.
	fad7antlr_6 $f wff ze $.
	fad7antlr_7 $f wff si $.
	fad7antlr_8 $f wff rh $.
	ead7antlr_0 $e |- ( ph -> ps ) $.
	ad7antlr $p |- ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps ) $= fad7antlr_2 fad7antlr_0 wa fad7antlr_3 wa fad7antlr_4 wa fad7antlr_5 wa fad7antlr_6 wa fad7antlr_7 wa fad7antlr_1 fad7antlr_8 fad7antlr_0 fad7antlr_1 fad7antlr_2 fad7antlr_3 fad7antlr_4 fad7antlr_5 fad7antlr_6 fad7antlr_7 ead7antlr_0 ad6antlr adantr $.
$}
$( Deduction adding 8 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	fad8antr_0 $f wff ph $.
	fad8antr_1 $f wff ps $.
	fad8antr_2 $f wff ch $.
	fad8antr_3 $f wff th $.
	fad8antr_4 $f wff ta $.
	fad8antr_5 $f wff et $.
	fad8antr_6 $f wff ze $.
	fad8antr_7 $f wff si $.
	fad8antr_8 $f wff rh $.
	fad8antr_9 $f wff mu $.
	ead8antr_0 $e |- ( ph -> ps ) $.
	ad8antr $p |- ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $= fad8antr_0 fad8antr_2 wa fad8antr_3 wa fad8antr_4 wa fad8antr_5 wa fad8antr_6 wa fad8antr_7 wa fad8antr_8 wa fad8antr_1 fad8antr_9 fad8antr_0 fad8antr_1 fad8antr_2 fad8antr_3 fad8antr_4 fad8antr_5 fad8antr_6 fad8antr_7 fad8antr_8 ead8antr_0 ad7antr adantr $.
$}
$( Deduction adding 8 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	fad8antlr_0 $f wff ph $.
	fad8antlr_1 $f wff ps $.
	fad8antlr_2 $f wff ch $.
	fad8antlr_3 $f wff th $.
	fad8antlr_4 $f wff ta $.
	fad8antlr_5 $f wff et $.
	fad8antlr_6 $f wff ze $.
	fad8antlr_7 $f wff si $.
	fad8antlr_8 $f wff rh $.
	fad8antlr_9 $f wff mu $.
	ead8antlr_0 $e |- ( ph -> ps ) $.
	ad8antlr $p |- ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $= fad8antlr_2 fad8antlr_0 wa fad8antlr_3 wa fad8antlr_4 wa fad8antlr_5 wa fad8antlr_6 wa fad8antlr_7 wa fad8antlr_8 wa fad8antlr_1 fad8antlr_9 fad8antlr_0 fad8antlr_1 fad8antlr_2 fad8antlr_3 fad8antlr_4 fad8antlr_5 fad8antlr_6 fad8antlr_7 fad8antlr_8 ead8antlr_0 ad7antlr adantr $.
$}
$( Deduction adding 9 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	fad9antr_0 $f wff ph $.
	fad9antr_1 $f wff ps $.
	fad9antr_2 $f wff ch $.
	fad9antr_3 $f wff th $.
	fad9antr_4 $f wff ta $.
	fad9antr_5 $f wff et $.
	fad9antr_6 $f wff ze $.
	fad9antr_7 $f wff si $.
	fad9antr_8 $f wff rh $.
	fad9antr_9 $f wff mu $.
	fad9antr_10 $f wff la $.
	ead9antr_0 $e |- ( ph -> ps ) $.
	ad9antr $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $= fad9antr_0 fad9antr_2 wa fad9antr_3 wa fad9antr_4 wa fad9antr_5 wa fad9antr_6 wa fad9antr_7 wa fad9antr_8 wa fad9antr_9 wa fad9antr_1 fad9antr_10 fad9antr_0 fad9antr_1 fad9antr_2 fad9antr_3 fad9antr_4 fad9antr_5 fad9antr_6 fad9antr_7 fad9antr_8 fad9antr_9 ead9antr_0 ad8antr adantr $.
$}
$( Deduction adding 9 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	fad9antlr_0 $f wff ph $.
	fad9antlr_1 $f wff ps $.
	fad9antlr_2 $f wff ch $.
	fad9antlr_3 $f wff th $.
	fad9antlr_4 $f wff ta $.
	fad9antlr_5 $f wff et $.
	fad9antlr_6 $f wff ze $.
	fad9antlr_7 $f wff si $.
	fad9antlr_8 $f wff rh $.
	fad9antlr_9 $f wff mu $.
	fad9antlr_10 $f wff la $.
	ead9antlr_0 $e |- ( ph -> ps ) $.
	ad9antlr $p |- ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $= fad9antlr_2 fad9antlr_0 wa fad9antlr_3 wa fad9antlr_4 wa fad9antlr_5 wa fad9antlr_6 wa fad9antlr_7 wa fad9antlr_8 wa fad9antlr_9 wa fad9antlr_1 fad9antlr_10 fad9antlr_0 fad9antlr_1 fad9antlr_2 fad9antlr_3 fad9antlr_4 fad9antlr_5 fad9antlr_6 fad9antlr_7 fad9antlr_8 fad9antlr_9 ead9antlr_0 ad8antlr adantr $.
$}
$( Deduction adding 10 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	$v ka $.
	fad10antr_0 $f wff ph $.
	fad10antr_1 $f wff ps $.
	fad10antr_2 $f wff ch $.
	fad10antr_3 $f wff th $.
	fad10antr_4 $f wff ta $.
	fad10antr_5 $f wff et $.
	fad10antr_6 $f wff ze $.
	fad10antr_7 $f wff si $.
	fad10antr_8 $f wff rh $.
	fad10antr_9 $f wff mu $.
	fad10antr_10 $f wff la $.
	fad10antr_11 $f wff ka $.
	ead10antr_0 $e |- ( ph -> ps ) $.
	ad10antr $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $= fad10antr_0 fad10antr_2 wa fad10antr_3 wa fad10antr_4 wa fad10antr_5 wa fad10antr_6 wa fad10antr_7 wa fad10antr_8 wa fad10antr_9 wa fad10antr_10 wa fad10antr_1 fad10antr_11 fad10antr_0 fad10antr_1 fad10antr_2 fad10antr_3 fad10antr_4 fad10antr_5 fad10antr_6 fad10antr_7 fad10antr_8 fad10antr_9 fad10antr_10 ead10antr_0 ad9antr adantr $.
$}
$( Deduction adding 10 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	$v ka $.
	fad10antlr_0 $f wff ph $.
	fad10antlr_1 $f wff ps $.
	fad10antlr_2 $f wff ch $.
	fad10antlr_3 $f wff th $.
	fad10antlr_4 $f wff ta $.
	fad10antlr_5 $f wff et $.
	fad10antlr_6 $f wff ze $.
	fad10antlr_7 $f wff si $.
	fad10antlr_8 $f wff rh $.
	fad10antlr_9 $f wff mu $.
	fad10antlr_10 $f wff la $.
	fad10antlr_11 $f wff ka $.
	ead10antlr_0 $e |- ( ph -> ps ) $.
	ad10antlr $p |- ( ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $= fad10antlr_2 fad10antlr_0 wa fad10antlr_3 wa fad10antlr_4 wa fad10antlr_5 wa fad10antlr_6 wa fad10antlr_7 wa fad10antlr_8 wa fad10antlr_9 wa fad10antlr_10 wa fad10antlr_1 fad10antlr_11 fad10antlr_0 fad10antlr_1 fad10antlr_2 fad10antlr_3 fad10antlr_4 fad10antlr_5 fad10antlr_6 fad10antlr_7 fad10antlr_8 fad10antlr_9 fad10antlr_10 ead10antlr_0 ad9antlr adantr $.
$}
$( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fad2ant2l_0 $f wff ph $.
	fad2ant2l_1 $f wff ps $.
	fad2ant2l_2 $f wff ch $.
	fad2ant2l_3 $f wff th $.
	fad2ant2l_4 $f wff ta $.
	ead2ant2l_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	ad2ant2l $p |- ( ( ( th /\ ph ) /\ ( ta /\ ps ) ) -> ch ) $= fad2ant2l_0 fad2ant2l_4 fad2ant2l_1 wa fad2ant2l_2 fad2ant2l_3 fad2ant2l_0 fad2ant2l_1 fad2ant2l_2 fad2ant2l_4 ead2ant2l_0 adantrl adantll $.
$}
$( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fad2ant2r_0 $f wff ph $.
	fad2ant2r_1 $f wff ps $.
	fad2ant2r_2 $f wff ch $.
	fad2ant2r_3 $f wff th $.
	fad2ant2r_4 $f wff ta $.
	ead2ant2r_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	ad2ant2r $p |- ( ( ( ph /\ th ) /\ ( ps /\ ta ) ) -> ch ) $= fad2ant2r_0 fad2ant2r_1 fad2ant2r_4 wa fad2ant2r_2 fad2ant2r_3 fad2ant2r_0 fad2ant2r_1 fad2ant2r_2 fad2ant2r_4 ead2ant2r_0 adantrr adantlr $.
$}
$( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       23-Nov-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fad2ant2lr_0 $f wff ph $.
	fad2ant2lr_1 $f wff ps $.
	fad2ant2lr_2 $f wff ch $.
	fad2ant2lr_3 $f wff th $.
	fad2ant2lr_4 $f wff ta $.
	ead2ant2lr_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	ad2ant2lr $p |- ( ( ( th /\ ph ) /\ ( ps /\ ta ) ) -> ch ) $= fad2ant2lr_0 fad2ant2lr_1 fad2ant2lr_4 wa fad2ant2lr_2 fad2ant2lr_3 fad2ant2lr_0 fad2ant2lr_1 fad2ant2lr_2 fad2ant2lr_4 ead2ant2lr_0 adantrr adantll $.
$}
$( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       24-Nov-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fad2ant2rl_0 $f wff ph $.
	fad2ant2rl_1 $f wff ps $.
	fad2ant2rl_2 $f wff ch $.
	fad2ant2rl_3 $f wff th $.
	fad2ant2rl_4 $f wff ta $.
	ead2ant2rl_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	ad2ant2rl $p |- ( ( ( ph /\ th ) /\ ( ta /\ ps ) ) -> ch ) $= fad2ant2rl_0 fad2ant2rl_4 fad2ant2rl_1 wa fad2ant2rl_2 fad2ant2rl_3 fad2ant2rl_0 fad2ant2rl_1 fad2ant2rl_2 fad2ant2rl_4 ead2ant2rl_0 adantrl adantlr $.
$}
$( Simplification of a conjunction.  (Contributed by NM, 18-Mar-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimpll_0 $f wff ph $.
	fsimpll_1 $f wff ps $.
	fsimpll_2 $f wff ch $.
	simpll $p |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $= fsimpll_0 fsimpll_0 fsimpll_1 fsimpll_2 fsimpll_0 id ad2antrr $.
$}
$( Simplification of a conjunction.  (Contributed by NM, 20-Mar-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimplr_0 $f wff ph $.
	fsimplr_1 $f wff ps $.
	fsimplr_2 $f wff ch $.
	simplr $p |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $= fsimplr_1 fsimplr_1 fsimplr_0 fsimplr_2 fsimplr_1 id ad2antlr $.
$}
$( Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimprl_0 $f wff ph $.
	fsimprl_1 $f wff ps $.
	fsimprl_2 $f wff ch $.
	simprl $p |- ( ( ph /\ ( ps /\ ch ) ) -> ps ) $= fsimprl_1 fsimprl_1 fsimprl_0 fsimprl_2 fsimprl_1 id ad2antrl $.
$}
$( Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimprr_0 $f wff ph $.
	fsimprr_1 $f wff ps $.
	fsimprr_2 $f wff ch $.
	simprr $p |- ( ( ph /\ ( ps /\ ch ) ) -> ch ) $= fsimprr_2 fsimprr_2 fsimprr_0 fsimprr_1 fsimprr_2 id ad2antll $.
$}
$( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimplll_0 $f wff ph $.
	fsimplll_1 $f wff ps $.
	fsimplll_2 $f wff ch $.
	fsimplll_3 $f wff th $.
	simplll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ph ) $= fsimplll_0 fsimplll_1 wa fsimplll_0 fsimplll_2 fsimplll_3 fsimplll_0 fsimplll_1 simpl ad2antrr $.
$}
$( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimpllr_0 $f wff ph $.
	fsimpllr_1 $f wff ps $.
	fsimpllr_2 $f wff ch $.
	fsimpllr_3 $f wff th $.
	simpllr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ps ) $= fsimpllr_0 fsimpllr_1 wa fsimpllr_1 fsimpllr_2 fsimpllr_3 fsimpllr_0 fsimpllr_1 simpr ad2antrr $.
$}
$( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimplrl_0 $f wff ph $.
	fsimplrl_1 $f wff ps $.
	fsimplrl_2 $f wff ch $.
	fsimplrl_3 $f wff th $.
	simplrl $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ps ) $= fsimplrl_1 fsimplrl_2 wa fsimplrl_1 fsimplrl_0 fsimplrl_3 fsimplrl_1 fsimplrl_2 simpl ad2antlr $.
$}
$( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimplrr_0 $f wff ph $.
	fsimplrr_1 $f wff ps $.
	fsimplrr_2 $f wff ch $.
	fsimplrr_3 $f wff th $.
	simplrr $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ch ) $= fsimplrr_1 fsimplrr_2 wa fsimplrr_2 fsimplrr_0 fsimplrr_3 fsimplrr_1 fsimplrr_2 simpr ad2antlr $.
$}
$( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimprll_0 $f wff ph $.
	fsimprll_1 $f wff ps $.
	fsimprll_2 $f wff ch $.
	fsimprll_3 $f wff th $.
	simprll $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ps ) $= fsimprll_1 fsimprll_2 wa fsimprll_1 fsimprll_0 fsimprll_3 fsimprll_1 fsimprll_2 simpl ad2antrl $.
$}
$( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimprlr_0 $f wff ph $.
	fsimprlr_1 $f wff ps $.
	fsimprlr_2 $f wff ch $.
	fsimprlr_3 $f wff th $.
	simprlr $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ch ) $= fsimprlr_1 fsimprlr_2 wa fsimprlr_2 fsimprlr_0 fsimprlr_3 fsimprlr_1 fsimprlr_2 simpr ad2antrl $.
$}
$( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimprrl_0 $f wff ph $.
	fsimprrl_1 $f wff ps $.
	fsimprrl_2 $f wff ch $.
	fsimprrl_3 $f wff th $.
	simprrl $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ch ) $= fsimprrl_2 fsimprrl_3 wa fsimprrl_2 fsimprrl_0 fsimprrl_1 fsimprrl_2 fsimprrl_3 simpl ad2antll $.
$}
$( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimprrr_0 $f wff ph $.
	fsimprrr_1 $f wff ps $.
	fsimprrr_2 $f wff ch $.
	fsimprrr_3 $f wff th $.
	simprrr $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> th ) $= fsimprrr_2 fsimprrr_3 wa fsimprrr_3 fsimprrr_0 fsimprrr_1 fsimprrr_2 fsimprrr_3 simpr ad2antll $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp-4l_0 $f wff ph $.
	fsimp-4l_1 $f wff ps $.
	fsimp-4l_2 $f wff ch $.
	fsimp-4l_3 $f wff th $.
	fsimp-4l_4 $f wff ta $.
	simp-4l $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ph ) $= fsimp-4l_0 fsimp-4l_1 wa fsimp-4l_2 wa fsimp-4l_3 wa fsimp-4l_0 fsimp-4l_4 fsimp-4l_0 fsimp-4l_1 fsimp-4l_2 fsimp-4l_3 simplll adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp-4r_0 $f wff ph $.
	fsimp-4r_1 $f wff ps $.
	fsimp-4r_2 $f wff ch $.
	fsimp-4r_3 $f wff th $.
	fsimp-4r_4 $f wff ta $.
	simp-4r $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ps ) $= fsimp-4r_0 fsimp-4r_1 wa fsimp-4r_2 wa fsimp-4r_3 wa fsimp-4r_1 fsimp-4r_4 fsimp-4r_0 fsimp-4r_1 fsimp-4r_2 fsimp-4r_3 simpllr adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp-5l_0 $f wff ph $.
	fsimp-5l_1 $f wff ps $.
	fsimp-5l_2 $f wff ch $.
	fsimp-5l_3 $f wff th $.
	fsimp-5l_4 $f wff ta $.
	fsimp-5l_5 $f wff et $.
	simp-5l $p |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) -> ph ) $= fsimp-5l_0 fsimp-5l_1 wa fsimp-5l_2 wa fsimp-5l_3 wa fsimp-5l_4 wa fsimp-5l_0 fsimp-5l_5 fsimp-5l_0 fsimp-5l_1 fsimp-5l_2 fsimp-5l_3 fsimp-5l_4 simp-4l adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp-5r_0 $f wff ph $.
	fsimp-5r_1 $f wff ps $.
	fsimp-5r_2 $f wff ch $.
	fsimp-5r_3 $f wff th $.
	fsimp-5r_4 $f wff ta $.
	fsimp-5r_5 $f wff et $.
	simp-5r $p |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) -> ps ) $= fsimp-5r_0 fsimp-5r_1 wa fsimp-5r_2 wa fsimp-5r_3 wa fsimp-5r_4 wa fsimp-5r_1 fsimp-5r_5 fsimp-5r_0 fsimp-5r_1 fsimp-5r_2 fsimp-5r_3 fsimp-5r_4 simp-4r adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp-6l_0 $f wff ph $.
	fsimp-6l_1 $f wff ps $.
	fsimp-6l_2 $f wff ch $.
	fsimp-6l_3 $f wff th $.
	fsimp-6l_4 $f wff ta $.
	fsimp-6l_5 $f wff et $.
	fsimp-6l_6 $f wff ze $.
	simp-6l $p |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ph ) $= fsimp-6l_0 fsimp-6l_1 wa fsimp-6l_2 wa fsimp-6l_3 wa fsimp-6l_4 wa fsimp-6l_5 wa fsimp-6l_0 fsimp-6l_6 fsimp-6l_0 fsimp-6l_1 fsimp-6l_2 fsimp-6l_3 fsimp-6l_4 fsimp-6l_5 simp-5l adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp-6r_0 $f wff ph $.
	fsimp-6r_1 $f wff ps $.
	fsimp-6r_2 $f wff ch $.
	fsimp-6r_3 $f wff th $.
	fsimp-6r_4 $f wff ta $.
	fsimp-6r_5 $f wff et $.
	fsimp-6r_6 $f wff ze $.
	simp-6r $p |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ps ) $= fsimp-6r_0 fsimp-6r_1 wa fsimp-6r_2 wa fsimp-6r_3 wa fsimp-6r_4 wa fsimp-6r_5 wa fsimp-6r_1 fsimp-6r_6 fsimp-6r_0 fsimp-6r_1 fsimp-6r_2 fsimp-6r_3 fsimp-6r_4 fsimp-6r_5 simp-5r adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsimp-7l_0 $f wff ph $.
	fsimp-7l_1 $f wff ps $.
	fsimp-7l_2 $f wff ch $.
	fsimp-7l_3 $f wff th $.
	fsimp-7l_4 $f wff ta $.
	fsimp-7l_5 $f wff et $.
	fsimp-7l_6 $f wff ze $.
	fsimp-7l_7 $f wff si $.
	simp-7l $p |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ph ) $= fsimp-7l_0 fsimp-7l_1 wa fsimp-7l_2 wa fsimp-7l_3 wa fsimp-7l_4 wa fsimp-7l_5 wa fsimp-7l_6 wa fsimp-7l_0 fsimp-7l_7 fsimp-7l_0 fsimp-7l_1 fsimp-7l_2 fsimp-7l_3 fsimp-7l_4 fsimp-7l_5 fsimp-7l_6 simp-6l adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsimp-7r_0 $f wff ph $.
	fsimp-7r_1 $f wff ps $.
	fsimp-7r_2 $f wff ch $.
	fsimp-7r_3 $f wff th $.
	fsimp-7r_4 $f wff ta $.
	fsimp-7r_5 $f wff et $.
	fsimp-7r_6 $f wff ze $.
	fsimp-7r_7 $f wff si $.
	simp-7r $p |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps ) $= fsimp-7r_0 fsimp-7r_1 wa fsimp-7r_2 wa fsimp-7r_3 wa fsimp-7r_4 wa fsimp-7r_5 wa fsimp-7r_6 wa fsimp-7r_1 fsimp-7r_7 fsimp-7r_0 fsimp-7r_1 fsimp-7r_2 fsimp-7r_3 fsimp-7r_4 fsimp-7r_5 fsimp-7r_6 simp-6r adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fsimp-8l_0 $f wff ph $.
	fsimp-8l_1 $f wff ps $.
	fsimp-8l_2 $f wff ch $.
	fsimp-8l_3 $f wff th $.
	fsimp-8l_4 $f wff ta $.
	fsimp-8l_5 $f wff et $.
	fsimp-8l_6 $f wff ze $.
	fsimp-8l_7 $f wff si $.
	fsimp-8l_8 $f wff rh $.
	simp-8l $p |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ph ) $= fsimp-8l_0 fsimp-8l_1 wa fsimp-8l_2 wa fsimp-8l_3 wa fsimp-8l_4 wa fsimp-8l_5 wa fsimp-8l_6 wa fsimp-8l_7 wa fsimp-8l_0 fsimp-8l_8 fsimp-8l_0 fsimp-8l_1 fsimp-8l_2 fsimp-8l_3 fsimp-8l_4 fsimp-8l_5 fsimp-8l_6 fsimp-8l_7 simp-7l adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fsimp-8r_0 $f wff ph $.
	fsimp-8r_1 $f wff ps $.
	fsimp-8r_2 $f wff ch $.
	fsimp-8r_3 $f wff th $.
	fsimp-8r_4 $f wff ta $.
	fsimp-8r_5 $f wff et $.
	fsimp-8r_6 $f wff ze $.
	fsimp-8r_7 $f wff si $.
	fsimp-8r_8 $f wff rh $.
	simp-8r $p |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps ) $= fsimp-8r_0 fsimp-8r_1 wa fsimp-8r_2 wa fsimp-8r_3 wa fsimp-8r_4 wa fsimp-8r_5 wa fsimp-8r_6 wa fsimp-8r_7 wa fsimp-8r_1 fsimp-8r_8 fsimp-8r_0 fsimp-8r_1 fsimp-8r_2 fsimp-8r_3 fsimp-8r_4 fsimp-8r_5 fsimp-8r_6 fsimp-8r_7 simp-7r adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	fsimp-9l_0 $f wff ph $.
	fsimp-9l_1 $f wff ps $.
	fsimp-9l_2 $f wff ch $.
	fsimp-9l_3 $f wff th $.
	fsimp-9l_4 $f wff ta $.
	fsimp-9l_5 $f wff et $.
	fsimp-9l_6 $f wff ze $.
	fsimp-9l_7 $f wff si $.
	fsimp-9l_8 $f wff rh $.
	fsimp-9l_9 $f wff mu $.
	simp-9l $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ph ) $= fsimp-9l_0 fsimp-9l_1 wa fsimp-9l_2 wa fsimp-9l_3 wa fsimp-9l_4 wa fsimp-9l_5 wa fsimp-9l_6 wa fsimp-9l_7 wa fsimp-9l_8 wa fsimp-9l_0 fsimp-9l_9 fsimp-9l_0 fsimp-9l_1 fsimp-9l_2 fsimp-9l_3 fsimp-9l_4 fsimp-9l_5 fsimp-9l_6 fsimp-9l_7 fsimp-9l_8 simp-8l adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	fsimp-9r_0 $f wff ph $.
	fsimp-9r_1 $f wff ps $.
	fsimp-9r_2 $f wff ch $.
	fsimp-9r_3 $f wff th $.
	fsimp-9r_4 $f wff ta $.
	fsimp-9r_5 $f wff et $.
	fsimp-9r_6 $f wff ze $.
	fsimp-9r_7 $f wff si $.
	fsimp-9r_8 $f wff rh $.
	fsimp-9r_9 $f wff mu $.
	simp-9r $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $= fsimp-9r_0 fsimp-9r_1 wa fsimp-9r_2 wa fsimp-9r_3 wa fsimp-9r_4 wa fsimp-9r_5 wa fsimp-9r_6 wa fsimp-9r_7 wa fsimp-9r_8 wa fsimp-9r_1 fsimp-9r_9 fsimp-9r_0 fsimp-9r_1 fsimp-9r_2 fsimp-9r_3 fsimp-9r_4 fsimp-9r_5 fsimp-9r_6 fsimp-9r_7 fsimp-9r_8 simp-8r adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	fsimp-10l_0 $f wff ph $.
	fsimp-10l_1 $f wff ps $.
	fsimp-10l_2 $f wff ch $.
	fsimp-10l_3 $f wff th $.
	fsimp-10l_4 $f wff ta $.
	fsimp-10l_5 $f wff et $.
	fsimp-10l_6 $f wff ze $.
	fsimp-10l_7 $f wff si $.
	fsimp-10l_8 $f wff rh $.
	fsimp-10l_9 $f wff mu $.
	fsimp-10l_10 $f wff la $.
	simp-10l $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ph ) $= fsimp-10l_0 fsimp-10l_1 wa fsimp-10l_2 wa fsimp-10l_3 wa fsimp-10l_4 wa fsimp-10l_5 wa fsimp-10l_6 wa fsimp-10l_7 wa fsimp-10l_8 wa fsimp-10l_9 wa fsimp-10l_0 fsimp-10l_10 fsimp-10l_0 fsimp-10l_1 fsimp-10l_2 fsimp-10l_3 fsimp-10l_4 fsimp-10l_5 fsimp-10l_6 fsimp-10l_7 fsimp-10l_8 fsimp-10l_9 simp-9l adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	fsimp-10r_0 $f wff ph $.
	fsimp-10r_1 $f wff ps $.
	fsimp-10r_2 $f wff ch $.
	fsimp-10r_3 $f wff th $.
	fsimp-10r_4 $f wff ta $.
	fsimp-10r_5 $f wff et $.
	fsimp-10r_6 $f wff ze $.
	fsimp-10r_7 $f wff si $.
	fsimp-10r_8 $f wff rh $.
	fsimp-10r_9 $f wff mu $.
	fsimp-10r_10 $f wff la $.
	simp-10r $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $= fsimp-10r_0 fsimp-10r_1 wa fsimp-10r_2 wa fsimp-10r_3 wa fsimp-10r_4 wa fsimp-10r_5 wa fsimp-10r_6 wa fsimp-10r_7 wa fsimp-10r_8 wa fsimp-10r_9 wa fsimp-10r_1 fsimp-10r_10 fsimp-10r_0 fsimp-10r_1 fsimp-10r_2 fsimp-10r_3 fsimp-10r_4 fsimp-10r_5 fsimp-10r_6 fsimp-10r_7 fsimp-10r_8 fsimp-10r_9 simp-9r adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	$v ka $.
	fsimp-11l_0 $f wff ph $.
	fsimp-11l_1 $f wff ps $.
	fsimp-11l_2 $f wff ch $.
	fsimp-11l_3 $f wff th $.
	fsimp-11l_4 $f wff ta $.
	fsimp-11l_5 $f wff et $.
	fsimp-11l_6 $f wff ze $.
	fsimp-11l_7 $f wff si $.
	fsimp-11l_8 $f wff rh $.
	fsimp-11l_9 $f wff mu $.
	fsimp-11l_10 $f wff la $.
	fsimp-11l_11 $f wff ka $.
	simp-11l $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ph ) $= fsimp-11l_0 fsimp-11l_1 wa fsimp-11l_2 wa fsimp-11l_3 wa fsimp-11l_4 wa fsimp-11l_5 wa fsimp-11l_6 wa fsimp-11l_7 wa fsimp-11l_8 wa fsimp-11l_9 wa fsimp-11l_10 wa fsimp-11l_0 fsimp-11l_11 fsimp-11l_0 fsimp-11l_1 fsimp-11l_2 fsimp-11l_3 fsimp-11l_4 fsimp-11l_5 fsimp-11l_6 fsimp-11l_7 fsimp-11l_8 fsimp-11l_9 fsimp-11l_10 simp-10l adantr $.
$}
$( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	$v ka $.
	fsimp-11r_0 $f wff ph $.
	fsimp-11r_1 $f wff ps $.
	fsimp-11r_2 $f wff ch $.
	fsimp-11r_3 $f wff th $.
	fsimp-11r_4 $f wff ta $.
	fsimp-11r_5 $f wff et $.
	fsimp-11r_6 $f wff ze $.
	fsimp-11r_7 $f wff si $.
	fsimp-11r_8 $f wff rh $.
	fsimp-11r_9 $f wff mu $.
	fsimp-11r_10 $f wff la $.
	fsimp-11r_11 $f wff ka $.
	simp-11r $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $= fsimp-11r_0 fsimp-11r_1 wa fsimp-11r_2 wa fsimp-11r_3 wa fsimp-11r_4 wa fsimp-11r_5 wa fsimp-11r_6 wa fsimp-11r_7 wa fsimp-11r_8 wa fsimp-11r_9 wa fsimp-11r_10 wa fsimp-11r_1 fsimp-11r_11 fsimp-11r_0 fsimp-11r_1 fsimp-11r_2 fsimp-11r_3 fsimp-11r_4 fsimp-11r_5 fsimp-11r_6 fsimp-11r_7 fsimp-11r_8 fsimp-11r_9 fsimp-11r_10 simp-10r adantr $.
$}
$( Disjunction of antecedents.  Compare Theorem *4.77 of [WhiteheadRussell]
     p. 121.  (Contributed by NM, 30-May-1994.)  (Proof shortened by Wolf
     Lammen, 9-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjaob_0 $f wff ph $.
	fjaob_1 $f wff ps $.
	fjaob_2 $f wff ch $.
	jaob $p |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $= fjaob_0 fjaob_2 wo fjaob_1 wi fjaob_0 fjaob_1 wi fjaob_2 fjaob_1 wi wa fjaob_0 fjaob_2 wo fjaob_1 wi fjaob_0 fjaob_1 wi fjaob_2 fjaob_1 wi fjaob_0 fjaob_1 fjaob_2 pm2.67-2 fjaob_2 fjaob_0 fjaob_2 wo fjaob_1 fjaob_2 fjaob_0 olc imim1i jca fjaob_1 fjaob_0 fjaob_2 pm3.44 impbii $.
$}
$( Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 23-Oct-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjaoian_0 $f wff ph $.
	fjaoian_1 $f wff ps $.
	fjaoian_2 $f wff ch $.
	fjaoian_3 $f wff th $.
	ejaoian_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	ejaoian_1 $e |- ( ( th /\ ps ) -> ch ) $.
	jaoian $p |- ( ( ( ph \/ th ) /\ ps ) -> ch ) $= fjaoian_0 fjaoian_3 wo fjaoian_1 fjaoian_2 fjaoian_0 fjaoian_1 fjaoian_2 wi fjaoian_3 fjaoian_0 fjaoian_1 fjaoian_2 ejaoian_0 ex fjaoian_3 fjaoian_1 fjaoian_2 ejaoian_1 ex jaoi imp $.
$}
$( Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 14-Oct-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjaodan_0 $f wff ph $.
	fjaodan_1 $f wff ps $.
	fjaodan_2 $f wff ch $.
	fjaodan_3 $f wff th $.
	ejaodan_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	ejaodan_1 $e |- ( ( ph /\ th ) -> ch ) $.
	jaodan $p |- ( ( ph /\ ( ps \/ th ) ) -> ch ) $= fjaodan_0 fjaodan_1 fjaodan_3 wo fjaodan_2 fjaodan_0 fjaodan_1 fjaodan_2 fjaodan_3 fjaodan_0 fjaodan_1 fjaodan_2 ejaodan_0 ex fjaodan_0 fjaodan_3 fjaodan_2 ejaodan_1 ex jaod imp $.
$}
$( Eliminate a disjunction in a deduction.  A translation of natural
       deduction rule ` \/ ` E ( ` \/ ` elimination), see ~ natded .
       (Contributed by Mario Carneiro, 29-May-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpjaodan_0 $f wff ph $.
	fmpjaodan_1 $f wff ps $.
	fmpjaodan_2 $f wff ch $.
	fmpjaodan_3 $f wff th $.
	empjaodan_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	empjaodan_1 $e |- ( ( ph /\ th ) -> ch ) $.
	empjaodan_2 $e |- ( ph -> ( ps \/ th ) ) $.
	mpjaodan $p |- ( ph -> ch ) $= fmpjaodan_0 fmpjaodan_1 fmpjaodan_3 wo fmpjaodan_2 empjaodan_2 fmpjaodan_0 fmpjaodan_1 fmpjaodan_2 fmpjaodan_3 empjaodan_0 empjaodan_1 jaodan mpdan $.
$}
$( Theorem *4.77 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.77_0 $f wff ph $.
	fpm4.77_1 $f wff ps $.
	fpm4.77_2 $f wff ch $.
	pm4.77 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) <-> ( ( ps \/ ch ) -> ph ) ) $= fpm4.77_1 fpm4.77_2 wo fpm4.77_0 wi fpm4.77_1 fpm4.77_0 wi fpm4.77_2 fpm4.77_0 wi wa fpm4.77_1 fpm4.77_0 fpm4.77_2 jaob bicomi $.
$}
$( Theorem *2.63 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.63_0 $f wff ph $.
	fpm2.63_1 $f wff ps $.
	pm2.63 $p |- ( ( ph \/ ps ) -> ( ( -. ph \/ ps ) -> ps ) ) $= fpm2.63_0 fpm2.63_1 wo fpm2.63_0 wn fpm2.63_1 fpm2.63_1 fpm2.63_0 fpm2.63_1 pm2.53 fpm2.63_0 fpm2.63_1 wo fpm2.63_1 idd jaod $.
$}
$( Theorem *2.64 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.64_0 $f wff ph $.
	fpm2.64_1 $f wff ps $.
	pm2.64 $p |- ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) ) $= fpm2.64_0 fpm2.64_1 wn wo fpm2.64_0 fpm2.64_1 wo fpm2.64_0 fpm2.64_0 fpm2.64_0 fpm2.64_1 wo fpm2.64_0 wi fpm2.64_1 wn fpm2.64_0 fpm2.64_0 fpm2.64_1 wo ax-1 fpm2.64_1 fpm2.64_0 orel2 jaoi com12 $.
$}
$( Elimination of an antecedent.  (Contributed by NM, 1-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.61ian_0 $f wff ph $.
	fpm2.61ian_1 $f wff ps $.
	fpm2.61ian_2 $f wff ch $.
	epm2.61ian_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	epm2.61ian_1 $e |- ( ( -. ph /\ ps ) -> ch ) $.
	pm2.61ian $p |- ( ps -> ch ) $= fpm2.61ian_0 fpm2.61ian_1 fpm2.61ian_2 wi fpm2.61ian_0 fpm2.61ian_1 fpm2.61ian_2 epm2.61ian_0 ex fpm2.61ian_0 wn fpm2.61ian_1 fpm2.61ian_2 epm2.61ian_1 ex pm2.61i $.
$}
$( Elimination of an antecedent.  (Contributed by NM, 1-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.61dan_0 $f wff ph $.
	fpm2.61dan_1 $f wff ps $.
	fpm2.61dan_2 $f wff ch $.
	epm2.61dan_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	epm2.61dan_1 $e |- ( ( ph /\ -. ps ) -> ch ) $.
	pm2.61dan $p |- ( ph -> ch ) $= fpm2.61dan_0 fpm2.61dan_1 fpm2.61dan_2 fpm2.61dan_0 fpm2.61dan_1 fpm2.61dan_2 epm2.61dan_0 ex fpm2.61dan_0 fpm2.61dan_1 wn fpm2.61dan_2 epm2.61dan_1 ex pm2.61d $.
$}
$( Elimination of two antecedents.  (Contributed by NM, 9-Jul-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm2.61ddan_0 $f wff ph $.
	fpm2.61ddan_1 $f wff ps $.
	fpm2.61ddan_2 $f wff ch $.
	fpm2.61ddan_3 $f wff th $.
	epm2.61ddan_0 $e |- ( ( ph /\ ps ) -> th ) $.
	epm2.61ddan_1 $e |- ( ( ph /\ ch ) -> th ) $.
	epm2.61ddan_2 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
	pm2.61ddan $p |- ( ph -> th ) $= fpm2.61ddan_0 fpm2.61ddan_1 fpm2.61ddan_3 epm2.61ddan_0 fpm2.61ddan_0 fpm2.61ddan_1 wn wa fpm2.61ddan_2 fpm2.61ddan_3 fpm2.61ddan_0 fpm2.61ddan_2 fpm2.61ddan_3 fpm2.61ddan_1 wn epm2.61ddan_1 adantlr fpm2.61ddan_0 fpm2.61ddan_1 wn fpm2.61ddan_2 wn fpm2.61ddan_3 epm2.61ddan_2 anassrs pm2.61dan pm2.61dan $.
$}
$( Elimination of two antecedents.  (Contributed by NM, 9-Jul-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm2.61dda_0 $f wff ph $.
	fpm2.61dda_1 $f wff ps $.
	fpm2.61dda_2 $f wff ch $.
	fpm2.61dda_3 $f wff th $.
	epm2.61dda_0 $e |- ( ( ph /\ -. ps ) -> th ) $.
	epm2.61dda_1 $e |- ( ( ph /\ -. ch ) -> th ) $.
	epm2.61dda_2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	pm2.61dda $p |- ( ph -> th ) $= fpm2.61dda_0 fpm2.61dda_1 fpm2.61dda_3 fpm2.61dda_0 fpm2.61dda_1 wa fpm2.61dda_2 fpm2.61dda_3 fpm2.61dda_0 fpm2.61dda_1 fpm2.61dda_2 fpm2.61dda_3 epm2.61dda_2 anassrs fpm2.61dda_0 fpm2.61dda_2 wn fpm2.61dda_3 fpm2.61dda_1 epm2.61dda_1 adantlr pm2.61dan epm2.61dda_0 pm2.61dan $.
$}
$( Proof by contradiction.  (Contributed by NM, 9-Feb-2006.)  (Proof
       shortened by Wolf Lammen, 19-Jun-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fcondan_0 $f wff ph $.
	fcondan_1 $f wff ps $.
	fcondan_2 $f wff ch $.
	econdan_0 $e |- ( ( ph /\ -. ps ) -> ch ) $.
	econdan_1 $e |- ( ( ph /\ -. ps ) -> -. ch ) $.
	condan $p |- ( ph -> ps ) $= fcondan_0 fcondan_1 wn wn fcondan_1 fcondan_0 fcondan_1 wn fcondan_2 econdan_0 econdan_1 pm2.65da fcondan_1 notnot2 syl $.
$}
$( Introduce one conjunct as an antecedent to the other.  "abai" stands for
     "and, biconditional, and, implication".  (Contributed by NM,
     12-Aug-1993.)  (Proof shortened by Wolf Lammen, 7-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	fabai_0 $f wff ph $.
	fabai_1 $f wff ps $.
	abai $p |- ( ( ph /\ ps ) <-> ( ph /\ ( ph -> ps ) ) ) $= fabai_0 fabai_1 fabai_0 fabai_1 wi fabai_0 fabai_1 biimt pm5.32i $.
$}
$( Theorem *5.53 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm5.53_0 $f wff ph $.
	fpm5.53_1 $f wff ps $.
	fpm5.53_2 $f wff ch $.
	fpm5.53_3 $f wff th $.
	pm5.53 $p |- ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <-> ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) ) $= fpm5.53_0 fpm5.53_1 wo fpm5.53_2 wo fpm5.53_3 wi fpm5.53_0 fpm5.53_1 wo fpm5.53_3 wi fpm5.53_2 fpm5.53_3 wi wa fpm5.53_0 fpm5.53_3 wi fpm5.53_1 fpm5.53_3 wi wa fpm5.53_2 fpm5.53_3 wi wa fpm5.53_0 fpm5.53_1 wo fpm5.53_3 fpm5.53_2 jaob fpm5.53_0 fpm5.53_1 wo fpm5.53_3 wi fpm5.53_0 fpm5.53_3 wi fpm5.53_1 fpm5.53_3 wi wa fpm5.53_2 fpm5.53_3 wi fpm5.53_0 fpm5.53_3 fpm5.53_1 jaob anbi1i bitri $.
$}
$( Swap two conjuncts.  Note that the first digit (1) in the label refers to
     the outer conjunct position, and the next digit (2) to the inner conjunct
     position.  (Contributed by NM, 12-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fan12_0 $f wff ph $.
	fan12_1 $f wff ps $.
	fan12_2 $f wff ch $.
	an12 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ps /\ ( ph /\ ch ) ) ) $= fan12_0 fan12_1 wa fan12_2 wa fan12_1 fan12_0 wa fan12_2 wa fan12_0 fan12_1 fan12_2 wa wa fan12_1 fan12_0 fan12_2 wa wa fan12_0 fan12_1 wa fan12_1 fan12_0 wa fan12_2 fan12_0 fan12_1 ancom anbi1i fan12_0 fan12_1 fan12_2 anass fan12_1 fan12_0 fan12_2 anass 3bitr3i $.
$}
$( A rearrangement of conjuncts.  (Contributed by NM, 12-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 25-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fan32_0 $f wff ph $.
	fan32_1 $f wff ps $.
	fan32_2 $f wff ch $.
	an32 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $= fan32_0 fan32_1 wa fan32_2 wa fan32_0 fan32_1 fan32_2 wa wa fan32_1 fan32_0 fan32_2 wa wa fan32_0 fan32_2 wa fan32_1 wa fan32_0 fan32_1 fan32_2 anass fan32_0 fan32_1 fan32_2 an12 fan32_1 fan32_0 fan32_2 wa ancom 3bitri $.
$}
$( A rearrangement of conjuncts.  (Contributed by NM, 24-Jun-2012.)  (Proof
     shortened by Wolf Lammen, 31-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fan13_0 $f wff ph $.
	fan13_1 $f wff ps $.
	fan13_2 $f wff ch $.
	an13 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ch /\ ( ps /\ ph ) ) ) $= fan13_0 fan13_1 fan13_2 wa wa fan13_1 fan13_0 fan13_2 wa wa fan13_1 fan13_0 wa fan13_2 wa fan13_2 fan13_1 fan13_0 wa wa fan13_0 fan13_1 fan13_2 an12 fan13_1 fan13_0 fan13_2 anass fan13_1 fan13_0 wa fan13_2 ancom 3bitr2i $.
$}
$( A rearrangement of conjuncts.  (Contributed by NM, 24-Jun-2012.)  (Proof
     shortened by Wolf Lammen, 31-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fan31_0 $f wff ph $.
	fan31_1 $f wff ps $.
	fan31_2 $f wff ch $.
	an31 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps ) /\ ph ) ) $= fan31_0 fan31_1 fan31_2 wa wa fan31_2 fan31_1 fan31_0 wa wa fan31_0 fan31_1 wa fan31_2 wa fan31_2 fan31_1 wa fan31_0 wa fan31_0 fan31_1 fan31_2 an13 fan31_0 fan31_1 fan31_2 anass fan31_2 fan31_1 fan31_0 anass 3bitr4i $.
$}
$( Swap two conjuncts in antecedent.  The label suffix "s" means that
       ~ an12 is combined with ~ syl (or a variant).  (Contributed by NM,
       13-Mar-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fan12s_0 $f wff ph $.
	fan12s_1 $f wff ps $.
	fan12s_2 $f wff ch $.
	fan12s_3 $f wff th $.
	ean12s_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	an12s $p |- ( ( ps /\ ( ph /\ ch ) ) -> th ) $= fan12s_1 fan12s_0 fan12s_2 wa wa fan12s_0 fan12s_1 fan12s_2 wa wa fan12s_3 fan12s_1 fan12s_0 fan12s_2 an12 ean12s_0 sylbi $.
$}
$( Inference commuting a nested conjunction in antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fancom2s_0 $f wff ph $.
	fancom2s_1 $f wff ps $.
	fancom2s_2 $f wff ch $.
	fancom2s_3 $f wff th $.
	eancom2s_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	ancom2s $p |- ( ( ph /\ ( ch /\ ps ) ) -> th ) $= fancom2s_2 fancom2s_1 wa fancom2s_0 fancom2s_1 fancom2s_2 wa fancom2s_3 fancom2s_2 fancom2s_1 pm3.22 eancom2s_0 sylan2 $.
$}
$( Swap two conjuncts in antecedent.  (Contributed by NM, 31-May-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fan13s_0 $f wff ph $.
	fan13s_1 $f wff ps $.
	fan13s_2 $f wff ch $.
	fan13s_3 $f wff th $.
	ean13s_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	an13s $p |- ( ( ch /\ ( ps /\ ph ) ) -> th ) $= fan13s_2 fan13s_1 fan13s_0 fan13s_3 fan13s_0 fan13s_1 fan13s_2 fan13s_3 fan13s_0 fan13s_1 fan13s_2 fan13s_3 ean13s_0 exp32 com13 imp32 $.
$}
$( Swap two conjuncts in antecedent.  (Contributed by NM, 13-Mar-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fan32s_0 $f wff ph $.
	fan32s_1 $f wff ps $.
	fan32s_2 $f wff ch $.
	fan32s_3 $f wff th $.
	ean32s_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	an32s $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $= fan32s_0 fan32s_2 wa fan32s_1 wa fan32s_0 fan32s_1 wa fan32s_2 wa fan32s_3 fan32s_0 fan32s_2 fan32s_1 an32 ean32s_0 sylbi $.
$}
$( Inference commuting a nested conjunction in antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fancom1s_0 $f wff ph $.
	fancom1s_1 $f wff ps $.
	fancom1s_2 $f wff ch $.
	fancom1s_3 $f wff th $.
	eancom1s_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	ancom1s $p |- ( ( ( ps /\ ph ) /\ ch ) -> th ) $= fancom1s_1 fancom1s_0 wa fancom1s_0 fancom1s_1 wa fancom1s_2 fancom1s_3 fancom1s_1 fancom1s_0 pm3.22 eancom1s_0 sylan $.
$}
$( Swap two conjuncts in antecedent.  (Contributed by NM, 31-May-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fan31s_0 $f wff ph $.
	fan31s_1 $f wff ps $.
	fan31s_2 $f wff ch $.
	fan31s_3 $f wff th $.
	ean31s_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	an31s $p |- ( ( ( ch /\ ps ) /\ ph ) -> th ) $= fan31s_2 fan31s_1 fan31s_0 fan31s_3 fan31s_0 fan31s_1 fan31s_2 fan31s_3 fan31s_0 fan31s_1 fan31s_2 fan31s_3 ean31s_0 exp31 com13 imp31 $.
$}
$( Commutative-associative law for conjunction in an antecedent.
       (Contributed by Jeff Madsen, 19-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanass1rs_0 $f wff ph $.
	fanass1rs_1 $f wff ps $.
	fanass1rs_2 $f wff ch $.
	fanass1rs_3 $f wff th $.
	eanass1rs_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	anass1rs $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $= fanass1rs_0 fanass1rs_1 fanass1rs_2 fanass1rs_3 fanass1rs_0 fanass1rs_1 fanass1rs_2 fanass1rs_3 eanass1rs_0 anassrs an32s $.
$}
$( Absorption into embedded conjunct.  (Contributed by NM, 4-Sep-1995.)
     (Proof shortened by Wolf Lammen, 16-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	fanabs1_0 $f wff ph $.
	fanabs1_1 $f wff ps $.
	anabs1 $p |- ( ( ( ph /\ ps ) /\ ph ) <-> ( ph /\ ps ) ) $= fanabs1_0 fanabs1_1 wa fanabs1_0 fanabs1_1 wa fanabs1_0 wa fanabs1_0 fanabs1_1 wa fanabs1_0 fanabs1_0 fanabs1_1 simpl pm4.71i bicomi $.
$}
$( Absorption into embedded conjunct.  (Contributed by NM, 20-Jul-1996.)
     (Proof shortened by Wolf Lammen, 9-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	fanabs5_0 $f wff ph $.
	fanabs5_1 $f wff ps $.
	anabs5 $p |- ( ( ph /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $= fanabs5_0 fanabs5_0 fanabs5_1 wa fanabs5_1 fanabs5_0 fanabs5_1 fanabs5_0 fanabs5_1 wa fanabs5_0 fanabs5_1 ibar bicomd pm5.32i $.
$}
$( Absorption into embedded conjunct.  (Contributed by NM, 20-Jul-1996.)
     (Proof shortened by Wolf Lammen, 17-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	fanabs7_0 $f wff ph $.
	fanabs7_1 $f wff ps $.
	anabs7 $p |- ( ( ps /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $= fanabs7_0 fanabs7_1 wa fanabs7_1 fanabs7_0 fanabs7_1 wa wa fanabs7_0 fanabs7_1 wa fanabs7_1 fanabs7_0 fanabs7_1 simpr pm4.71ri bicomi $.
$}
$( Absorption of antecedent with conjunction.  (Contributed by NM,
       24-Mar-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabsan_0 $f wff ph $.
	fanabsan_1 $f wff ps $.
	fanabsan_2 $f wff ch $.
	eanabsan_0 $e |- ( ( ( ph /\ ph ) /\ ps ) -> ch ) $.
	anabsan $p |- ( ( ph /\ ps ) -> ch ) $= fanabsan_0 fanabsan_0 fanabsan_0 wa fanabsan_1 fanabsan_2 fanabsan_0 pm4.24 eanabsan_0 sylanb $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 31-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabss1_0 $f wff ph $.
	fanabss1_1 $f wff ps $.
	fanabss1_2 $f wff ch $.
	eanabss1_0 $e |- ( ( ( ph /\ ps ) /\ ph ) -> ch ) $.
	anabss1 $p |- ( ( ph /\ ps ) -> ch ) $= fanabss1_0 fanabss1_1 fanabss1_2 fanabss1_0 fanabss1_1 fanabss1_0 fanabss1_2 eanabss1_0 an32s anabsan $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabss4_0 $f wff ph $.
	fanabss4_1 $f wff ps $.
	fanabss4_2 $f wff ch $.
	eanabss4_0 $e |- ( ( ( ps /\ ph ) /\ ps ) -> ch ) $.
	anabss4 $p |- ( ( ph /\ ps ) -> ch ) $= fanabss4_1 fanabss4_0 fanabss4_2 fanabss4_1 fanabss4_0 fanabss4_2 eanabss4_0 anabss1 ancoms $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       10-May-1994.)  (Proof shortened by Wolf Lammen, 1-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabss5_0 $f wff ph $.
	fanabss5_1 $f wff ps $.
	fanabss5_2 $f wff ch $.
	eanabss5_0 $e |- ( ( ph /\ ( ph /\ ps ) ) -> ch ) $.
	anabss5 $p |- ( ( ph /\ ps ) -> ch ) $= fanabss5_0 fanabss5_1 fanabss5_2 fanabss5_0 fanabss5_0 fanabss5_1 fanabss5_2 eanabss5_0 anassrs anabsan $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       11-Jun-1995.)  (Proof shortened by Wolf Lammen, 18-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabsi5_0 $f wff ph $.
	fanabsi5_1 $f wff ps $.
	fanabsi5_2 $f wff ch $.
	eanabsi5_0 $e |- ( ph -> ( ( ph /\ ps ) -> ch ) ) $.
	anabsi5 $p |- ( ( ph /\ ps ) -> ch ) $= fanabsi5_0 fanabsi5_1 fanabsi5_2 fanabsi5_0 fanabsi5_0 fanabsi5_1 wa fanabsi5_2 eanabsi5_0 imp anabss5 $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       14-Aug-2000.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabsi6_0 $f wff ph $.
	fanabsi6_1 $f wff ps $.
	fanabsi6_2 $f wff ch $.
	eanabsi6_0 $e |- ( ph -> ( ( ps /\ ph ) -> ch ) ) $.
	anabsi6 $p |- ( ( ph /\ ps ) -> ch ) $= fanabsi6_0 fanabsi6_1 fanabsi6_2 fanabsi6_0 fanabsi6_1 fanabsi6_0 fanabsi6_2 eanabsi6_0 ancomsd anabsi5 $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 18-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabsi7_0 $f wff ph $.
	fanabsi7_1 $f wff ps $.
	fanabsi7_2 $f wff ch $.
	eanabsi7_0 $e |- ( ps -> ( ( ph /\ ps ) -> ch ) ) $.
	anabsi7 $p |- ( ( ph /\ ps ) -> ch ) $= fanabsi7_1 fanabsi7_0 fanabsi7_2 fanabsi7_1 fanabsi7_0 fanabsi7_2 eanabsi7_0 anabsi6 ancoms $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       26-Sep-1999.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabsi8_0 $f wff ph $.
	fanabsi8_1 $f wff ps $.
	fanabsi8_2 $f wff ch $.
	eanabsi8_0 $e |- ( ps -> ( ( ps /\ ph ) -> ch ) ) $.
	anabsi8 $p |- ( ( ph /\ ps ) -> ch ) $= fanabsi8_1 fanabsi8_0 fanabsi8_2 fanabsi8_1 fanabsi8_0 fanabsi8_2 eanabsi8_0 anabsi5 ancoms $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 19-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabss7_0 $f wff ph $.
	fanabss7_1 $f wff ps $.
	fanabss7_2 $f wff ch $.
	eanabss7_0 $e |- ( ( ps /\ ( ph /\ ps ) ) -> ch ) $.
	anabss7 $p |- ( ( ph /\ ps ) -> ch ) $= fanabss7_0 fanabss7_1 fanabss7_2 fanabss7_1 fanabss7_0 fanabss7_1 fanabss7_2 eanabss7_0 anassrs anabss4 $.
$}
$( Absorption of antecedent with conjunction.  (Contributed by NM,
       10-May-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabsan2_0 $f wff ph $.
	fanabsan2_1 $f wff ps $.
	fanabsan2_2 $f wff ch $.
	eanabsan2_0 $e |- ( ( ph /\ ( ps /\ ps ) ) -> ch ) $.
	anabsan2 $p |- ( ( ph /\ ps ) -> ch ) $= fanabsan2_0 fanabsan2_1 fanabsan2_2 fanabsan2_0 fanabsan2_1 fanabsan2_1 fanabsan2_2 eanabsan2_0 an12s anabss7 $.
$}
$( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 1-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanabss3_0 $f wff ph $.
	fanabss3_1 $f wff ps $.
	fanabss3_2 $f wff ch $.
	eanabss3_0 $e |- ( ( ( ph /\ ps ) /\ ps ) -> ch ) $.
	anabss3 $p |- ( ( ph /\ ps ) -> ch ) $= fanabss3_0 fanabss3_1 fanabss3_2 fanabss3_0 fanabss3_1 fanabss3_1 fanabss3_2 eanabss3_0 anasss anabsan2 $.
$}
$( Rearrangement of 4 conjuncts.  (Contributed by NM, 10-Jul-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fan4_0 $f wff ph $.
	fan4_1 $f wff ps $.
	fan4_2 $f wff ch $.
	fan4_3 $f wff th $.
	an4 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ph /\ ch ) /\ ( ps /\ th ) ) ) $= fan4_0 fan4_1 fan4_2 fan4_3 wa wa wa fan4_0 fan4_2 fan4_1 fan4_3 wa wa wa fan4_0 fan4_1 wa fan4_2 fan4_3 wa wa fan4_0 fan4_2 wa fan4_1 fan4_3 wa wa fan4_1 fan4_2 fan4_3 wa wa fan4_2 fan4_1 fan4_3 wa wa fan4_0 fan4_1 fan4_2 fan4_3 an12 anbi2i fan4_0 fan4_1 fan4_2 fan4_3 wa anass fan4_0 fan4_2 fan4_1 fan4_3 wa anass 3bitr4i $.
$}
$( Rearrangement of 4 conjuncts.  (Contributed by NM, 7-Feb-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fan42_0 $f wff ph $.
	fan42_1 $f wff ps $.
	fan42_2 $f wff ch $.
	fan42_3 $f wff th $.
	an42 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ph /\ ch ) /\ ( th /\ ps ) ) ) $= fan42_0 fan42_1 wa fan42_2 fan42_3 wa wa fan42_0 fan42_2 wa fan42_1 fan42_3 wa wa fan42_0 fan42_2 wa fan42_3 fan42_1 wa wa fan42_0 fan42_1 fan42_2 fan42_3 an4 fan42_1 fan42_3 wa fan42_3 fan42_1 wa fan42_0 fan42_2 wa fan42_1 fan42_3 ancom anbi2i bitri $.
$}
$( Inference rearranging 4 conjuncts in antecedent.  (Contributed by NM,
       10-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fan4s_0 $f wff ph $.
	fan4s_1 $f wff ps $.
	fan4s_2 $f wff ch $.
	fan4s_3 $f wff th $.
	fan4s_4 $f wff ta $.
	ean4s_0 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
	an4s $p |- ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) -> ta ) $= fan4s_0 fan4s_2 wa fan4s_1 fan4s_3 wa wa fan4s_0 fan4s_1 wa fan4s_2 fan4s_3 wa wa fan4s_4 fan4s_0 fan4s_2 fan4s_1 fan4s_3 an4 ean4s_0 sylbi $.
$}
$( Inference rearranging 4 conjuncts in antecedent.  (Contributed by NM,
       10-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fan42s_0 $f wff ph $.
	fan42s_1 $f wff ps $.
	fan42s_2 $f wff ch $.
	fan42s_3 $f wff th $.
	fan42s_4 $f wff ta $.
	ean42s_0 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
	an42s $p |- ( ( ( ph /\ ch ) /\ ( th /\ ps ) ) -> ta ) $= fan42s_0 fan42s_2 wa fan42s_1 fan42s_3 fan42s_4 fan42s_0 fan42s_1 fan42s_2 fan42s_3 fan42s_4 ean42s_0 an4s ancom2s $.
$}
$( Distribution of conjunction over conjunction.  (Contributed by NM,
     14-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanandi_0 $f wff ph $.
	fanandi_1 $f wff ps $.
	fanandi_2 $f wff ch $.
	anandi $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ( ph /\ ps ) /\ ( ph /\ ch ) ) ) $= fanandi_0 fanandi_1 fanandi_2 wa wa fanandi_0 fanandi_0 wa fanandi_1 fanandi_2 wa wa fanandi_0 fanandi_1 wa fanandi_0 fanandi_2 wa wa fanandi_0 fanandi_0 wa fanandi_0 fanandi_1 fanandi_2 wa fanandi_0 anidm anbi1i fanandi_0 fanandi_0 fanandi_1 fanandi_2 an4 bitr3i $.
$}
$( Distribution of conjunction over conjunction.  (Contributed by NM,
     24-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fanandir_0 $f wff ph $.
	fanandir_1 $f wff ps $.
	fanandir_2 $f wff ch $.
	anandir $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ( ps /\ ch ) ) ) $= fanandir_0 fanandir_1 wa fanandir_2 wa fanandir_0 fanandir_1 wa fanandir_2 fanandir_2 wa wa fanandir_0 fanandir_2 wa fanandir_1 fanandir_2 wa wa fanandir_2 fanandir_2 wa fanandir_2 fanandir_0 fanandir_1 wa fanandir_2 anidm anbi2i fanandir_0 fanandir_1 fanandir_2 fanandir_2 an4 bitr3i $.
$}
$( Inference that undistributes conjunction in the antecedent.
       (Contributed by NM, 7-Jun-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v ta $.
	fanandis_0 $f wff ph $.
	fanandis_1 $f wff ps $.
	fanandis_2 $f wff ch $.
	fanandis_3 $f wff ta $.
	eanandis_0 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> ta ) $.
	anandis $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $= fanandis_0 fanandis_1 fanandis_2 wa fanandis_3 fanandis_0 fanandis_1 fanandis_0 fanandis_2 fanandis_3 eanandis_0 an4s anabsan $.
$}
$( Inference that undistributes conjunction in the antecedent.
       (Contributed by NM, 7-Jun-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v ta $.
	fanandirs_0 $f wff ph $.
	fanandirs_1 $f wff ps $.
	fanandirs_2 $f wff ch $.
	fanandirs_3 $f wff ta $.
	eanandirs_0 $e |- ( ( ( ph /\ ch ) /\ ( ps /\ ch ) ) -> ta ) $.
	anandirs $p |- ( ( ( ph /\ ps ) /\ ch ) -> ta ) $= fanandirs_0 fanandirs_1 wa fanandirs_2 fanandirs_3 fanandirs_0 fanandirs_2 fanandirs_1 fanandirs_2 fanandirs_3 eanandirs_0 an4s anabsan2 $.
$}
$( Deduce an equivalence from two implications.  (Contributed by NM,
       17-Feb-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimpbida_0 $f wff ph $.
	fimpbida_1 $f wff ps $.
	fimpbida_2 $f wff ch $.
	eimpbida_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	eimpbida_1 $e |- ( ( ph /\ ch ) -> ps ) $.
	impbida $p |- ( ph -> ( ps <-> ch ) ) $= fimpbida_0 fimpbida_1 fimpbida_2 fimpbida_0 fimpbida_1 fimpbida_2 eimpbida_0 ex fimpbida_0 fimpbida_2 fimpbida_1 eimpbida_1 ex impbid $.
$}
$( Theorem *3.48 of [WhiteheadRussell] p. 114.  (Contributed by NM,
     28-Jan-1997.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm3.48_0 $f wff ph $.
	fpm3.48_1 $f wff ps $.
	fpm3.48_2 $f wff ch $.
	fpm3.48_3 $f wff th $.
	pm3.48 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) -> ( ( ph \/ ch ) -> ( ps \/ th ) ) ) $= fpm3.48_0 fpm3.48_1 wi fpm3.48_0 fpm3.48_1 fpm3.48_3 wo fpm3.48_2 fpm3.48_3 wi fpm3.48_2 fpm3.48_1 fpm3.48_1 fpm3.48_3 wo fpm3.48_0 fpm3.48_1 fpm3.48_3 orc imim2i fpm3.48_3 fpm3.48_1 fpm3.48_3 wo fpm3.48_2 fpm3.48_3 fpm3.48_1 olc imim2i jaao $.
$}
$( Theorem *3.45 (Fact) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.45_0 $f wff ph $.
	fpm3.45_1 $f wff ps $.
	fpm3.45_2 $f wff ch $.
	pm3.45 $p |- ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $= fpm3.45_0 fpm3.45_1 wi fpm3.45_0 fpm3.45_1 fpm3.45_2 fpm3.45_0 fpm3.45_1 wi id anim1d $.
$}
$( Deduction joining nested implications to form implication of
       conjunctions.  (Contributed by NM, 29-Feb-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fim2anan9_0 $f wff ph $.
	fim2anan9_1 $f wff ps $.
	fim2anan9_2 $f wff ch $.
	fim2anan9_3 $f wff th $.
	fim2anan9_4 $f wff ta $.
	fim2anan9_5 $f wff et $.
	eim2anan9_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eim2anan9_1 $e |- ( th -> ( ta -> et ) ) $.
	im2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $= fim2anan9_0 fim2anan9_3 wa fim2anan9_1 fim2anan9_2 fim2anan9_4 fim2anan9_5 fim2anan9_0 fim2anan9_1 fim2anan9_2 wi fim2anan9_3 eim2anan9_0 adantr fim2anan9_3 fim2anan9_4 fim2anan9_5 wi fim2anan9_0 eim2anan9_1 adantl anim12d $.
$}
$( Deduction joining nested implications to form implication of
       conjunctions.  (Contributed by NM, 29-Feb-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fim2anan9r_0 $f wff ph $.
	fim2anan9r_1 $f wff ps $.
	fim2anan9r_2 $f wff ch $.
	fim2anan9r_3 $f wff th $.
	fim2anan9r_4 $f wff ta $.
	fim2anan9r_5 $f wff et $.
	eim2anan9r_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eim2anan9r_1 $e |- ( th -> ( ta -> et ) ) $.
	im2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $= fim2anan9r_0 fim2anan9r_3 fim2anan9r_1 fim2anan9r_4 wa fim2anan9r_2 fim2anan9r_5 wa wi fim2anan9r_0 fim2anan9r_1 fim2anan9r_2 fim2anan9r_3 fim2anan9r_4 fim2anan9r_5 eim2anan9r_0 eim2anan9r_1 im2anan9 ancoms $.
$}
$( Conjoin antecedents and consequents in a deduction.  (Contributed by
       Mario Carneiro, 12-May-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fanim12dan_0 $f wff ph $.
	fanim12dan_1 $f wff ps $.
	fanim12dan_2 $f wff ch $.
	fanim12dan_3 $f wff th $.
	fanim12dan_4 $f wff ta $.
	eanim12dan_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	eanim12dan_1 $e |- ( ( ph /\ th ) -> ta ) $.
	anim12dan $p |- ( ( ph /\ ( ps /\ th ) ) -> ( ch /\ ta ) ) $= fanim12dan_0 fanim12dan_1 fanim12dan_3 wa fanim12dan_2 fanim12dan_4 wa fanim12dan_0 fanim12dan_1 fanim12dan_2 fanim12dan_3 fanim12dan_4 fanim12dan_0 fanim12dan_1 fanim12dan_2 eanim12dan_0 ex fanim12dan_0 fanim12dan_3 fanim12dan_4 eanim12dan_1 ex anim12d imp $.
$}
$( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       10-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	forim12d_0 $f wff ph $.
	forim12d_1 $f wff ps $.
	forim12d_2 $f wff ch $.
	forim12d_3 $f wff th $.
	forim12d_4 $f wff ta $.
	eorim12d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eorim12d_1 $e |- ( ph -> ( th -> ta ) ) $.
	orim12d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ ta ) ) ) $= forim12d_0 forim12d_1 forim12d_2 wi forim12d_3 forim12d_4 wi forim12d_1 forim12d_3 wo forim12d_2 forim12d_4 wo wi eorim12d_0 eorim12d_1 forim12d_1 forim12d_2 forim12d_3 forim12d_4 pm3.48 syl2anc $.
$}
$( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       23-Apr-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	forim1d_0 $f wff ph $.
	forim1d_1 $f wff ps $.
	forim1d_2 $f wff ch $.
	forim1d_3 $f wff th $.
	eorim1d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	orim1d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ th ) ) ) $= forim1d_0 forim1d_1 forim1d_2 forim1d_3 forim1d_3 eorim1d_0 forim1d_0 forim1d_3 idd orim12d $.
$}
$( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       23-Apr-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	forim2d_0 $f wff ph $.
	forim2d_1 $f wff ps $.
	forim2d_2 $f wff ch $.
	forim2d_3 $f wff th $.
	eorim2d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	orim2d $p |- ( ph -> ( ( th \/ ps ) -> ( th \/ ch ) ) ) $= forim2d_0 forim2d_3 forim2d_3 forim2d_1 forim2d_2 forim2d_0 forim2d_3 idd eorim2d_0 orim12d $.
$}
$( Axiom *1.6 (Sum) of [WhiteheadRussell] p. 97.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forim2_0 $f wff ph $.
	forim2_1 $f wff ps $.
	forim2_2 $f wff ch $.
	orim2 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $= forim2_1 forim2_2 wi forim2_1 forim2_2 forim2_0 forim2_1 forim2_2 wi id orim2d $.
$}
$( Theorem *2.38 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.38_0 $f wff ph $.
	fpm2.38_1 $f wff ps $.
	fpm2.38_2 $f wff ch $.
	pm2.38 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ch \/ ph ) ) ) $= fpm2.38_1 fpm2.38_2 wi fpm2.38_1 fpm2.38_2 fpm2.38_0 fpm2.38_1 fpm2.38_2 wi id orim1d $.
$}
$( Theorem *2.36 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.36_0 $f wff ph $.
	fpm2.36_1 $f wff ps $.
	fpm2.36_2 $f wff ch $.
	pm2.36 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ch \/ ph ) ) ) $= fpm2.36_0 fpm2.36_1 wo fpm2.36_1 fpm2.36_0 wo fpm2.36_1 fpm2.36_2 wi fpm2.36_2 fpm2.36_0 wo fpm2.36_0 fpm2.36_1 pm1.4 fpm2.36_0 fpm2.36_1 fpm2.36_2 pm2.38 syl5 $.
$}
$( Theorem *2.37 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.37_0 $f wff ph $.
	fpm2.37_1 $f wff ps $.
	fpm2.37_2 $f wff ch $.
	pm2.37 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ph \/ ch ) ) ) $= fpm2.37_1 fpm2.37_2 wi fpm2.37_1 fpm2.37_0 wo fpm2.37_2 fpm2.37_0 wo fpm2.37_0 fpm2.37_2 wo fpm2.37_0 fpm2.37_1 fpm2.37_2 pm2.38 fpm2.37_2 fpm2.37_0 pm1.4 syl6 $.
$}
$( Theorem *2.73 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.73_0 $f wff ph $.
	fpm2.73_1 $f wff ps $.
	fpm2.73_2 $f wff ch $.
	pm2.73 $p |- ( ( ph -> ps ) -> ( ( ( ph \/ ps ) \/ ch ) -> ( ps \/ ch ) ) ) $= fpm2.73_0 fpm2.73_1 wi fpm2.73_0 fpm2.73_1 wo fpm2.73_1 fpm2.73_2 fpm2.73_0 fpm2.73_1 pm2.621 orim1d $.
$}
$( Theorem *2.74 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.74_0 $f wff ph $.
	fpm2.74_1 $f wff ps $.
	fpm2.74_2 $f wff ch $.
	pm2.74 $p |- ( ( ps -> ph ) -> ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ch ) ) ) $= fpm2.74_1 fpm2.74_0 wi fpm2.74_0 fpm2.74_1 wo fpm2.74_0 fpm2.74_2 fpm2.74_1 fpm2.74_0 fpm2.74_0 fpm2.74_1 wo fpm2.74_0 wi fpm2.74_1 fpm2.74_0 orel2 fpm2.74_0 fpm2.74_0 fpm2.74_1 wo ax-1 ja orim1d $.
$}
$( Disjunction distributes over implication.  (Contributed by Wolf Lammen,
     5-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	forimdi_0 $f wff ph $.
	forimdi_1 $f wff ps $.
	forimdi_2 $f wff ch $.
	orimdi $p |- ( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $= forimdi_0 wn forimdi_1 forimdi_2 wi wi forimdi_0 wn forimdi_1 wi forimdi_0 wn forimdi_2 wi wi forimdi_0 forimdi_1 forimdi_2 wi wo forimdi_0 forimdi_1 wo forimdi_0 forimdi_2 wo wi forimdi_0 wn forimdi_1 forimdi_2 imdi forimdi_0 forimdi_1 forimdi_2 wi df-or forimdi_0 forimdi_1 wo forimdi_0 wn forimdi_1 wi forimdi_0 forimdi_2 wo forimdi_0 wn forimdi_2 wi forimdi_0 forimdi_1 df-or forimdi_0 forimdi_2 df-or imbi12i 3bitr4i $.
$}
$( Theorem *2.76 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.76_0 $f wff ph $.
	fpm2.76_1 $f wff ps $.
	fpm2.76_2 $f wff ch $.
	pm2.76 $p |- ( ( ph \/ ( ps -> ch ) ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $= fpm2.76_0 fpm2.76_1 fpm2.76_2 wi wo fpm2.76_0 fpm2.76_1 wo fpm2.76_0 fpm2.76_2 wo wi fpm2.76_0 fpm2.76_1 fpm2.76_2 orimdi biimpi $.
$}
$( Theorem *2.75 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 4-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.75_0 $f wff ph $.
	fpm2.75_1 $f wff ps $.
	fpm2.75_2 $f wff ch $.
	pm2.75 $p |- ( ( ph \/ ps ) -> ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) ) $= fpm2.75_0 fpm2.75_1 fpm2.75_2 wi wo fpm2.75_0 fpm2.75_1 wo fpm2.75_0 fpm2.75_2 wo fpm2.75_0 fpm2.75_1 fpm2.75_2 pm2.76 com12 $.
$}
$( Theorem *2.8 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.8_0 $f wff ph $.
	fpm2.8_1 $f wff ps $.
	fpm2.8_2 $f wff ch $.
	pm2.8 $p |- ( ( ph \/ ps ) -> ( ( -. ps \/ ch ) -> ( ph \/ ch ) ) ) $= fpm2.8_0 fpm2.8_1 wo fpm2.8_1 wn fpm2.8_0 fpm2.8_2 fpm2.8_0 fpm2.8_1 wo fpm2.8_0 fpm2.8_1 fpm2.8_0 fpm2.8_1 pm2.53 con1d orim1d $.
$}
$( Theorem *2.81 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm2.81_0 $f wff ph $.
	fpm2.81_1 $f wff ps $.
	fpm2.81_2 $f wff ch $.
	fpm2.81_3 $f wff th $.
	pm2.81 $p |- ( ( ps -> ( ch -> th ) ) -> ( ( ph \/ ps ) -> ( ( ph \/ ch ) -> ( ph \/ th ) ) ) ) $= fpm2.81_1 fpm2.81_2 fpm2.81_3 wi wi fpm2.81_0 fpm2.81_1 wo fpm2.81_0 fpm2.81_2 fpm2.81_3 wi wo fpm2.81_0 fpm2.81_2 wo fpm2.81_0 fpm2.81_3 wo wi fpm2.81_0 fpm2.81_1 fpm2.81_2 fpm2.81_3 wi orim2 fpm2.81_0 fpm2.81_2 fpm2.81_3 pm2.76 syl6 $.
$}
$( Theorem *2.82 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm2.82_0 $f wff ph $.
	fpm2.82_1 $f wff ps $.
	fpm2.82_2 $f wff ch $.
	fpm2.82_3 $f wff th $.
	pm2.82 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th ) -> ( ( ph \/ ps ) \/ th ) ) ) $= fpm2.82_0 fpm2.82_1 wo fpm2.82_2 wo fpm2.82_0 fpm2.82_2 wn wo fpm2.82_0 fpm2.82_1 wo fpm2.82_3 fpm2.82_0 fpm2.82_1 wo fpm2.82_0 fpm2.82_2 wn wo fpm2.82_0 fpm2.82_1 wo wi fpm2.82_2 fpm2.82_0 fpm2.82_1 wo fpm2.82_0 fpm2.82_2 wn wo ax-1 fpm2.82_2 fpm2.82_2 wn fpm2.82_1 fpm2.82_0 fpm2.82_2 fpm2.82_1 pm2.24 orim2d jaoi orim1d $.
$}
$( Theorem *2.85 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.85_0 $f wff ph $.
	fpm2.85_1 $f wff ps $.
	fpm2.85_2 $f wff ch $.
	pm2.85 $p |- ( ( ( ph \/ ps ) -> ( ph \/ ch ) ) -> ( ph \/ ( ps -> ch ) ) ) $= fpm2.85_0 fpm2.85_1 fpm2.85_2 wi wo fpm2.85_0 fpm2.85_1 wo fpm2.85_0 fpm2.85_2 wo wi fpm2.85_0 fpm2.85_1 fpm2.85_2 orimdi biimpri $.
$}
$( Infer negated disjunction of negated premises.  (Contributed by NM,
       4-Apr-1995.) $)
${
	$v ph $.
	$v ps $.
	fpm3.2ni_0 $f wff ph $.
	fpm3.2ni_1 $f wff ps $.
	epm3.2ni_0 $e |- -. ph $.
	epm3.2ni_1 $e |- -. ps $.
	pm3.2ni $p |- -. ( ph \/ ps ) $= fpm3.2ni_0 fpm3.2ni_1 wo fpm3.2ni_0 epm3.2ni_0 fpm3.2ni_0 fpm3.2ni_0 fpm3.2ni_1 fpm3.2ni_0 id fpm3.2ni_1 fpm3.2ni_0 epm3.2ni_1 pm2.21i jaoi mto $.
$}
$( Absorption of redundant internal disjunct.  Compare Theorem *4.45 of
     [WhiteheadRussell] p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 28-Feb-2014.) $)
${
	$v ph $.
	$v ps $.
	forabs_0 $f wff ph $.
	forabs_1 $f wff ps $.
	orabs $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $= forabs_0 forabs_0 forabs_1 wo forabs_0 forabs_1 orc pm4.71ri $.
$}
$( Absorb a disjunct into a conjunct.  (Contributed by Roy F. Longton,
     23-Jun-2005.)  (Proof shortened by Wolf Lammen, 10-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	foranabs_0 $f wff ph $.
	foranabs_1 $f wff ps $.
	oranabs $p |- ( ( ( ph \/ -. ps ) /\ ps ) <-> ( ph /\ ps ) ) $= foranabs_1 foranabs_0 foranabs_1 wn wo foranabs_0 foranabs_1 foranabs_0 foranabs_1 wn foranabs_0 wo foranabs_0 foranabs_1 wn wo foranabs_1 foranabs_0 biortn foranabs_1 wn foranabs_0 orcom syl6rbb pm5.32ri $.
$}
$( Two propositions are equivalent if they are both true.  Theorem *5.1 of
     [WhiteheadRussell] p. 123.  (Contributed by NM, 21-May-1994.) $)
${
	$v ph $.
	$v ps $.
	fpm5.1_0 $f wff ph $.
	fpm5.1_1 $f wff ps $.
	pm5.1 $p |- ( ( ph /\ ps ) -> ( ph <-> ps ) ) $= fpm5.1_0 fpm5.1_1 fpm5.1_0 fpm5.1_1 wb fpm5.1_0 fpm5.1_1 pm5.501 biimpa $.
$}
$( Two propositions are equivalent if they are both false.  Theorem *5.21 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 21-May-1994.) $)
${
	$v ph $.
	$v ps $.
	fpm5.21_0 $f wff ph $.
	fpm5.21_1 $f wff ps $.
	pm5.21 $p |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) ) $= fpm5.21_0 wn fpm5.21_1 wn fpm5.21_0 fpm5.21_1 wb fpm5.21_0 fpm5.21_1 pm5.21im imp $.
$}
$( Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.43_0 $f wff ph $.
	fpm3.43_1 $f wff ps $.
	fpm3.43_2 $f wff ch $.
	pm3.43 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) -> ( ph -> ( ps /\ ch ) ) ) $= fpm3.43_0 fpm3.43_1 wi fpm3.43_0 fpm3.43_2 wi fpm3.43_0 fpm3.43_1 fpm3.43_2 wa wi fpm3.43_0 fpm3.43_1 fpm3.43_2 pm3.43i imp $.
$}
$( Distributive law for implication over conjunction.  Compare Theorem *4.76
     of [WhiteheadRussell] p. 121.  (Contributed by NM, 3-Apr-1994.)  (Proof
     shortened by Wolf Lammen, 27-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjcab_0 $f wff ph $.
	fjcab_1 $f wff ps $.
	fjcab_2 $f wff ch $.
	jcab $p |- ( ( ph -> ( ps /\ ch ) ) <-> ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $= fjcab_0 fjcab_1 fjcab_2 wa wi fjcab_0 fjcab_1 wi fjcab_0 fjcab_2 wi wa fjcab_0 fjcab_1 fjcab_2 wa wi fjcab_0 fjcab_1 wi fjcab_0 fjcab_2 wi fjcab_1 fjcab_2 wa fjcab_1 fjcab_0 fjcab_1 fjcab_2 simpl imim2i fjcab_1 fjcab_2 wa fjcab_2 fjcab_0 fjcab_1 fjcab_2 simpr imim2i jca fjcab_0 fjcab_1 fjcab_2 pm3.43 impbii $.
$}
$( Distributive law for disjunction.  Theorem *4.41 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 7-May-2011.)  (Proof shortened by Wolf Lammen, 28-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fordi_0 $f wff ph $.
	fordi_1 $f wff ps $.
	fordi_2 $f wff ch $.
	ordi $p |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $= fordi_0 wn fordi_1 fordi_2 wa wi fordi_0 wn fordi_1 wi fordi_0 wn fordi_2 wi wa fordi_0 fordi_1 fordi_2 wa wo fordi_0 fordi_1 wo fordi_0 fordi_2 wo wa fordi_0 wn fordi_1 fordi_2 jcab fordi_0 fordi_1 fordi_2 wa df-or fordi_0 fordi_1 wo fordi_0 wn fordi_1 wi fordi_0 fordi_2 wo fordi_0 wn fordi_2 wi fordi_0 fordi_1 df-or fordi_0 fordi_2 df-or anbi12i 3bitr4i $.
$}
$( Distributive law for disjunction.  (Contributed by NM, 12-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fordir_0 $f wff ph $.
	fordir_1 $f wff ps $.
	fordir_2 $f wff ch $.
	ordir $p |- ( ( ( ph /\ ps ) \/ ch ) <-> ( ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $= fordir_2 fordir_0 fordir_1 wa wo fordir_2 fordir_0 wo fordir_2 fordir_1 wo wa fordir_0 fordir_1 wa fordir_2 wo fordir_0 fordir_2 wo fordir_1 fordir_2 wo wa fordir_2 fordir_0 fordir_1 ordi fordir_0 fordir_1 wa fordir_2 orcom fordir_0 fordir_2 wo fordir_2 fordir_0 wo fordir_1 fordir_2 wo fordir_2 fordir_1 wo fordir_0 fordir_2 orcom fordir_1 fordir_2 orcom anbi12i 3bitr4i $.
$}
$( Theorem *4.76 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm4.76_0 $f wff ph $.
	fpm4.76_1 $f wff ps $.
	fpm4.76_2 $f wff ch $.
	pm4.76 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <-> ( ph -> ( ps /\ ch ) ) ) $= fpm4.76_0 fpm4.76_1 fpm4.76_2 wa wi fpm4.76_0 fpm4.76_1 wi fpm4.76_0 fpm4.76_2 wi wa fpm4.76_0 fpm4.76_1 fpm4.76_2 jcab bicomi $.
$}
$( Distributive law for conjunction.  Theorem *4.4 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 5-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fandi_0 $f wff ph $.
	fandi_1 $f wff ps $.
	fandi_2 $f wff ch $.
	andi $p |- ( ( ph /\ ( ps \/ ch ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $= fandi_0 fandi_1 fandi_2 wo wa fandi_0 fandi_1 wa fandi_0 fandi_2 wa wo fandi_0 fandi_1 fandi_0 fandi_1 wa fandi_0 fandi_2 wa wo fandi_2 fandi_0 fandi_1 wa fandi_0 fandi_2 wa orc fandi_0 fandi_2 wa fandi_0 fandi_1 wa olc jaodan fandi_0 fandi_1 wa fandi_0 fandi_1 fandi_2 wo wa fandi_0 fandi_2 wa fandi_1 fandi_1 fandi_2 wo fandi_0 fandi_1 fandi_2 orc anim2i fandi_2 fandi_1 fandi_2 wo fandi_0 fandi_2 fandi_1 olc anim2i jaoi impbii $.
$}
$( Distributive law for conjunction.  (Contributed by NM, 12-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fandir_0 $f wff ph $.
	fandir_1 $f wff ps $.
	fandir_2 $f wff ch $.
	andir $p |- ( ( ( ph \/ ps ) /\ ch ) <-> ( ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $= fandir_2 fandir_0 fandir_1 wo wa fandir_2 fandir_0 wa fandir_2 fandir_1 wa wo fandir_0 fandir_1 wo fandir_2 wa fandir_0 fandir_2 wa fandir_1 fandir_2 wa wo fandir_2 fandir_0 fandir_1 andi fandir_0 fandir_1 wo fandir_2 ancom fandir_0 fandir_2 wa fandir_2 fandir_0 wa fandir_1 fandir_2 wa fandir_2 fandir_1 wa fandir_0 fandir_2 ancom fandir_1 fandir_2 ancom orbi12i 3bitr4i $.
$}
$( Double distributive law for disjunction.  (Contributed by NM,
     12-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	forddi_0 $f wff ph $.
	forddi_1 $f wff ps $.
	forddi_2 $f wff ch $.
	forddi_3 $f wff th $.
	orddi $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <-> ( ( ( ph \/ ch ) /\ ( ph \/ th ) ) /\ ( ( ps \/ ch ) /\ ( ps \/ th ) ) ) ) $= forddi_0 forddi_1 wa forddi_2 forddi_3 wa wo forddi_0 forddi_2 forddi_3 wa wo forddi_1 forddi_2 forddi_3 wa wo wa forddi_0 forddi_2 wo forddi_0 forddi_3 wo wa forddi_1 forddi_2 wo forddi_1 forddi_3 wo wa wa forddi_0 forddi_1 forddi_2 forddi_3 wa ordir forddi_0 forddi_2 forddi_3 wa wo forddi_0 forddi_2 wo forddi_0 forddi_3 wo wa forddi_1 forddi_2 forddi_3 wa wo forddi_1 forddi_2 wo forddi_1 forddi_3 wo wa forddi_0 forddi_2 forddi_3 ordi forddi_1 forddi_2 forddi_3 ordi anbi12i bitri $.
$}
$( Double distributive law for conjunction.  (Contributed by NM,
     12-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fanddi_0 $f wff ph $.
	fanddi_1 $f wff ps $.
	fanddi_2 $f wff ch $.
	fanddi_3 $f wff th $.
	anddi $p |- ( ( ( ph \/ ps ) /\ ( ch \/ th ) ) <-> ( ( ( ph /\ ch ) \/ ( ph /\ th ) ) \/ ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ) $= fanddi_0 fanddi_1 wo fanddi_2 fanddi_3 wo wa fanddi_0 fanddi_2 fanddi_3 wo wa fanddi_1 fanddi_2 fanddi_3 wo wa wo fanddi_0 fanddi_2 wa fanddi_0 fanddi_3 wa wo fanddi_1 fanddi_2 wa fanddi_1 fanddi_3 wa wo wo fanddi_0 fanddi_1 fanddi_2 fanddi_3 wo andir fanddi_0 fanddi_2 fanddi_3 wo wa fanddi_0 fanddi_2 wa fanddi_0 fanddi_3 wa wo fanddi_1 fanddi_2 fanddi_3 wo wa fanddi_1 fanddi_2 wa fanddi_1 fanddi_3 wa wo fanddi_0 fanddi_2 fanddi_3 andi fanddi_1 fanddi_2 fanddi_3 andi orbi12i bitri $.
$}
$( Prove formula-building rules for the biconditional connective. $)
$( Theorem *4.39 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm4.39_0 $f wff ph $.
	fpm4.39_1 $f wff ps $.
	fpm4.39_2 $f wff ch $.
	fpm4.39_3 $f wff th $.
	pm4.39 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) -> ( ( ph \/ ps ) <-> ( ch \/ th ) ) ) $= fpm4.39_0 fpm4.39_2 wb fpm4.39_1 fpm4.39_3 wb wa fpm4.39_0 fpm4.39_2 fpm4.39_1 fpm4.39_3 fpm4.39_0 fpm4.39_2 wb fpm4.39_1 fpm4.39_3 wb simpl fpm4.39_0 fpm4.39_2 wb fpm4.39_1 fpm4.39_3 wb simpr orbi12d $.
$}
$( Theorem *4.38 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm4.38_0 $f wff ph $.
	fpm4.38_1 $f wff ps $.
	fpm4.38_2 $f wff ch $.
	fpm4.38_3 $f wff th $.
	pm4.38 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) -> ( ( ph /\ ps ) <-> ( ch /\ th ) ) ) $= fpm4.38_0 fpm4.38_2 wb fpm4.38_1 fpm4.38_3 wb wa fpm4.38_0 fpm4.38_2 fpm4.38_1 fpm4.38_3 fpm4.38_0 fpm4.38_2 wb fpm4.38_1 fpm4.38_3 wb simpl fpm4.38_0 fpm4.38_2 wb fpm4.38_1 fpm4.38_3 wb simpr anbi12d $.
$}
$( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 31-Jul-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fbi2anan9_0 $f wff ph $.
	fbi2anan9_1 $f wff ps $.
	fbi2anan9_2 $f wff ch $.
	fbi2anan9_3 $f wff th $.
	fbi2anan9_4 $f wff ta $.
	fbi2anan9_5 $f wff et $.
	ebi2anan9_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ebi2anan9_1 $e |- ( th -> ( ta <-> et ) ) $.
	bi2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $= fbi2anan9_0 fbi2anan9_1 fbi2anan9_4 wa fbi2anan9_2 fbi2anan9_4 wa fbi2anan9_3 fbi2anan9_2 fbi2anan9_5 wa fbi2anan9_0 fbi2anan9_1 fbi2anan9_2 fbi2anan9_4 ebi2anan9_0 anbi1d fbi2anan9_3 fbi2anan9_4 fbi2anan9_5 fbi2anan9_2 ebi2anan9_1 anbi2d sylan9bb $.
$}
$( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 19-Feb-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fbi2anan9r_0 $f wff ph $.
	fbi2anan9r_1 $f wff ps $.
	fbi2anan9r_2 $f wff ch $.
	fbi2anan9r_3 $f wff th $.
	fbi2anan9r_4 $f wff ta $.
	fbi2anan9r_5 $f wff et $.
	ebi2anan9r_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ebi2anan9r_1 $e |- ( th -> ( ta <-> et ) ) $.
	bi2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $= fbi2anan9r_0 fbi2anan9r_3 fbi2anan9r_1 fbi2anan9r_4 wa fbi2anan9r_2 fbi2anan9r_5 wa wb fbi2anan9r_0 fbi2anan9r_1 fbi2anan9r_2 fbi2anan9r_3 fbi2anan9r_4 fbi2anan9r_5 ebi2anan9r_0 ebi2anan9r_1 bi2anan9 ancoms $.
$}
$( Deduction joining two biconditionals with different antecedents.
       (Contributed by NM, 12-May-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fbi2bian9_0 $f wff ph $.
	fbi2bian9_1 $f wff ps $.
	fbi2bian9_2 $f wff ch $.
	fbi2bian9_3 $f wff th $.
	fbi2bian9_4 $f wff ta $.
	fbi2bian9_5 $f wff et $.
	ebi2bian9_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ebi2bian9_1 $e |- ( th -> ( ta <-> et ) ) $.
	bi2bian9 $p |- ( ( ph /\ th ) -> ( ( ps <-> ta ) <-> ( ch <-> et ) ) ) $= fbi2bian9_0 fbi2bian9_3 wa fbi2bian9_1 fbi2bian9_2 fbi2bian9_4 fbi2bian9_5 fbi2bian9_0 fbi2bian9_1 fbi2bian9_2 wb fbi2bian9_3 ebi2bian9_0 adantr fbi2bian9_3 fbi2bian9_4 fbi2bian9_5 wb fbi2bian9_0 ebi2bian9_1 adantl bibi12d $.
$}
$( Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 30-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm4.72_0 $f wff ph $.
	fpm4.72_1 $f wff ps $.
	pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $= fpm4.72_0 fpm4.72_1 wi fpm4.72_1 fpm4.72_0 fpm4.72_1 wo wb fpm4.72_0 fpm4.72_1 wi fpm4.72_1 fpm4.72_0 fpm4.72_1 wo fpm4.72_1 fpm4.72_0 olc fpm4.72_0 fpm4.72_1 pm2.621 impbid2 fpm4.72_0 fpm4.72_0 fpm4.72_1 wo fpm4.72_1 fpm4.72_0 fpm4.72_1 wo wb fpm4.72_1 fpm4.72_0 fpm4.72_1 orc fpm4.72_1 fpm4.72_0 fpm4.72_1 wo bi2 syl5 impbii $.
$}
$( Simplify an implication between implications.  (Contributed by Paul
     Chapman, 17-Nov-2012.)  (Proof shortened by Wolf Lammen, 3-Apr-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimimorb_0 $f wff ph $.
	fimimorb_1 $f wff ps $.
	fimimorb_2 $f wff ch $.
	imimorb $p |- ( ( ( ps -> ch ) -> ( ph -> ch ) ) <-> ( ph -> ( ps \/ ch ) ) ) $= fimimorb_1 fimimorb_2 wi fimimorb_0 fimimorb_2 wi wi fimimorb_0 fimimorb_1 fimimorb_2 wi fimimorb_2 wi wi fimimorb_0 fimimorb_1 fimimorb_2 wo wi fimimorb_1 fimimorb_2 wi fimimorb_0 fimimorb_2 bi2.04 fimimorb_1 fimimorb_2 wo fimimorb_1 fimimorb_2 wi fimimorb_2 wi fimimorb_0 fimimorb_1 fimimorb_2 dfor2 imbi2i bitr4i $.
$}
$( Theorem *5.33 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm5.33_0 $f wff ph $.
	fpm5.33_1 $f wff ps $.
	fpm5.33_2 $f wff ch $.
	pm5.33 $p |- ( ( ph /\ ( ps -> ch ) ) <-> ( ph /\ ( ( ph /\ ps ) -> ch ) ) ) $= fpm5.33_0 fpm5.33_1 fpm5.33_2 wi fpm5.33_0 fpm5.33_1 wa fpm5.33_2 wi fpm5.33_0 fpm5.33_1 fpm5.33_0 fpm5.33_1 wa fpm5.33_2 fpm5.33_0 fpm5.33_1 ibar imbi1d pm5.32i $.
$}
$( Theorem *5.36 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm5.36_0 $f wff ph $.
	fpm5.36_1 $f wff ps $.
	pm5.36 $p |- ( ( ph /\ ( ph <-> ps ) ) <-> ( ps /\ ( ph <-> ps ) ) ) $= fpm5.36_0 fpm5.36_1 wb fpm5.36_0 fpm5.36_1 fpm5.36_0 fpm5.36_1 wb id pm5.32ri $.
$}
$( Absorb a hypothesis into the second member of a biconditional.
       (Contributed by FL, 15-Feb-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fbianabs_0 $f wff ph $.
	fbianabs_1 $f wff ps $.
	fbianabs_2 $f wff ch $.
	ebianabs_0 $e |- ( ph -> ( ps <-> ( ph /\ ch ) ) ) $.
	bianabs $p |- ( ph -> ( ps <-> ch ) ) $= fbianabs_0 fbianabs_1 fbianabs_0 fbianabs_2 wa fbianabs_2 ebianabs_0 fbianabs_0 fbianabs_2 ibar bitr4d $.
$}
$( Absorption of disjunction into equivalence.  (Contributed by NM,
     6-Aug-1995.)  (Proof shortened by Wolf Lammen, 3-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	foibabs_0 $f wff ph $.
	foibabs_1 $f wff ps $.
	oibabs $p |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) ) $= foibabs_0 foibabs_1 wo foibabs_0 foibabs_1 wb wi foibabs_0 foibabs_1 wb foibabs_0 foibabs_1 wo foibabs_0 foibabs_1 wb foibabs_0 foibabs_1 wb foibabs_0 foibabs_1 wo wn foibabs_0 wn foibabs_1 wn wa foibabs_0 foibabs_1 wb foibabs_0 foibabs_1 ioran foibabs_0 foibabs_1 pm5.21 sylbi foibabs_0 foibabs_1 wb id ja foibabs_0 foibabs_1 wb foibabs_0 foibabs_1 wo ax-1 impbii $.
$}
$( Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111 (who
     call it the "law of contradiction").  (Contributed by NM, 16-Sep-1993.)
     (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
${
	$v ph $.
	fpm3.24_0 $f wff ph $.
	pm3.24 $p |- -. ( ph /\ -. ph ) $= fpm3.24_0 fpm3.24_0 wi fpm3.24_0 fpm3.24_0 wn wa wn fpm3.24_0 id fpm3.24_0 fpm3.24_0 iman mpbi $.
$}
$( Theorem *2.26 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm2.26_0 $f wff ph $.
	fpm2.26_1 $f wff ps $.
	pm2.26 $p |- ( -. ph \/ ( ( ph -> ps ) -> ps ) ) $= fpm2.26_0 fpm2.26_0 fpm2.26_1 wi fpm2.26_1 wi fpm2.26_0 fpm2.26_1 pm2.27 imori $.
$}
$( Theorem *5.11 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm5.11_0 $f wff ph $.
	fpm5.11_1 $f wff ps $.
	pm5.11 $p |- ( ( ph -> ps ) \/ ( -. ph -> ps ) ) $= fpm5.11_0 fpm5.11_1 wi fpm5.11_0 wn fpm5.11_1 wi fpm5.11_0 fpm5.11_1 pm2.5 orri $.
$}
$( Theorem *5.12 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm5.12_0 $f wff ph $.
	fpm5.12_1 $f wff ps $.
	pm5.12 $p |- ( ( ph -> ps ) \/ ( ph -> -. ps ) ) $= fpm5.12_0 fpm5.12_1 wi fpm5.12_0 fpm5.12_1 wn wi fpm5.12_0 fpm5.12_1 pm2.51 orri $.
$}
$( Theorem *5.14 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm5.14_0 $f wff ph $.
	fpm5.14_1 $f wff ps $.
	fpm5.14_2 $f wff ch $.
	pm5.14 $p |- ( ( ph -> ps ) \/ ( ps -> ch ) ) $= fpm5.14_0 fpm5.14_1 wi fpm5.14_1 fpm5.14_2 wi fpm5.14_0 fpm5.14_1 wi wn fpm5.14_1 fpm5.14_2 fpm5.14_1 fpm5.14_0 fpm5.14_1 wi fpm5.14_1 fpm5.14_0 ax-1 con3i pm2.21d orri $.
$}
$( Theorem *5.13 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm5.13_0 $f wff ph $.
	fpm5.13_1 $f wff ps $.
	pm5.13 $p |- ( ( ph -> ps ) \/ ( ps -> ph ) ) $= fpm5.13_0 fpm5.13_1 fpm5.13_0 pm5.14 $.
$}
$( Theorem *5.17 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm5.17_0 $f wff ph $.
	fpm5.17_1 $f wff ps $.
	pm5.17 $p |- ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) ) $= fpm5.17_0 fpm5.17_1 wn wb fpm5.17_1 wn fpm5.17_0 wb fpm5.17_1 wn fpm5.17_0 wi fpm5.17_0 fpm5.17_1 wn wi wa fpm5.17_0 fpm5.17_1 wo fpm5.17_0 fpm5.17_1 wa wn wa fpm5.17_0 fpm5.17_1 wn bicom fpm5.17_1 wn fpm5.17_0 dfbi2 fpm5.17_1 wn fpm5.17_0 wi fpm5.17_0 fpm5.17_1 wo fpm5.17_0 fpm5.17_1 wn wi fpm5.17_0 fpm5.17_1 wa wn fpm5.17_0 fpm5.17_1 wo fpm5.17_1 fpm5.17_0 wo fpm5.17_1 wn fpm5.17_0 wi fpm5.17_0 fpm5.17_1 orcom fpm5.17_1 fpm5.17_0 df-or bitr2i fpm5.17_0 fpm5.17_1 imnan anbi12i 3bitrri $.
$}
$( Theorem *5.15 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm5.15_0 $f wff ph $.
	fpm5.15_1 $f wff ps $.
	pm5.15 $p |- ( ( ph <-> ps ) \/ ( ph <-> -. ps ) ) $= fpm5.15_0 fpm5.15_1 wb fpm5.15_0 fpm5.15_1 wn wb fpm5.15_0 fpm5.15_1 wb wn fpm5.15_0 fpm5.15_1 wn wb fpm5.15_0 fpm5.15_1 xor3 biimpi orri $.
$}
$( Theorem *5.16 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 17-Oct-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm5.16_0 $f wff ph $.
	fpm5.16_1 $f wff ps $.
	pm5.16 $p |- -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) ) $= fpm5.16_0 fpm5.16_1 wb fpm5.16_0 fpm5.16_1 wn wb wn wi fpm5.16_0 fpm5.16_1 wb fpm5.16_0 fpm5.16_1 wn wb wa wn fpm5.16_0 fpm5.16_1 wb fpm5.16_0 fpm5.16_1 wn wb wn fpm5.16_0 fpm5.16_1 pm5.18 biimpi fpm5.16_0 fpm5.16_1 wb fpm5.16_0 fpm5.16_1 wn wb imnan mpbi $.
$}
$( Two ways to express "exclusive or."  Theorem *5.22 of [WhiteheadRussell]
     p. 124.  (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf
     Lammen, 22-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	fxor_0 $f wff ph $.
	fxor_1 $f wff ps $.
	xor $p |- ( -. ( ph <-> ps ) <-> ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $= fxor_0 fxor_1 wn wa fxor_1 fxor_0 wn wa wo fxor_0 fxor_1 wb fxor_0 fxor_1 wi fxor_1 fxor_0 wi wa fxor_0 fxor_1 wn wa wn fxor_1 fxor_0 wn wa wn wa fxor_0 fxor_1 wb fxor_0 fxor_1 wn wa fxor_1 fxor_0 wn wa wo wn fxor_0 fxor_1 wi fxor_0 fxor_1 wn wa wn fxor_1 fxor_0 wi fxor_1 fxor_0 wn wa wn fxor_0 fxor_1 iman fxor_1 fxor_0 iman anbi12i fxor_0 fxor_1 dfbi2 fxor_0 fxor_1 wn wa fxor_1 fxor_0 wn wa ioran 3bitr4ri con1bii $.
$}
$( Two ways to express "exclusive or."  (Contributed by NM, 3-Jan-2005.)
     (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	fnbi2_0 $f wff ph $.
	fnbi2_1 $f wff ps $.
	nbi2 $p |- ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $= fnbi2_0 fnbi2_1 wb wn fnbi2_0 fnbi2_1 wn wb fnbi2_0 fnbi2_1 wo fnbi2_0 fnbi2_1 wa wn wa fnbi2_0 fnbi2_1 xor3 fnbi2_0 fnbi2_1 pm5.17 bitr4i $.
$}
$( An alternate definition of the biconditional.  Theorem *5.23 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 3-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	fdfbi3_0 $f wff ph $.
	fdfbi3_1 $f wff ps $.
	dfbi3 $p |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) ) $= fdfbi3_0 fdfbi3_1 wn wb wn fdfbi3_0 fdfbi3_1 wn wn wa fdfbi3_1 wn fdfbi3_0 wn wa wo fdfbi3_0 fdfbi3_1 wb fdfbi3_0 fdfbi3_1 wa fdfbi3_0 wn fdfbi3_1 wn wa wo fdfbi3_0 fdfbi3_1 wn xor fdfbi3_0 fdfbi3_1 pm5.18 fdfbi3_0 fdfbi3_1 wa fdfbi3_0 fdfbi3_1 wn wn wa fdfbi3_0 wn fdfbi3_1 wn wa fdfbi3_1 wn fdfbi3_0 wn wa fdfbi3_1 fdfbi3_1 wn wn fdfbi3_0 fdfbi3_1 notnot anbi2i fdfbi3_0 wn fdfbi3_1 wn ancom orbi12i 3bitr4i $.
$}
$( Theorem *5.24 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm5.24_0 $f wff ph $.
	fpm5.24_1 $f wff ps $.
	pm5.24 $p |- ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <-> ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $= fpm5.24_0 fpm5.24_1 wb fpm5.24_0 fpm5.24_1 wn wa fpm5.24_1 fpm5.24_0 wn wa wo fpm5.24_0 fpm5.24_1 wa fpm5.24_0 wn fpm5.24_1 wn wa wo fpm5.24_0 fpm5.24_1 xor fpm5.24_0 fpm5.24_1 dfbi3 xchnxbi $.
$}
$( Conjunction distributes over exclusive-or, using ` -. ( ph <-> ps ) ` to
     express exclusive-or.  This is one way to interpret the distributive law
     of multiplication over addition in modulo 2 arithmetic.  (Contributed by
     NM, 3-Oct-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fxordi_0 $f wff ph $.
	fxordi_1 $f wff ps $.
	fxordi_2 $f wff ch $.
	xordi $p |- ( ( ph /\ -. ( ps <-> ch ) ) <-> -. ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $= fxordi_0 fxordi_1 fxordi_2 wb wn wa fxordi_0 fxordi_1 fxordi_2 wb wi fxordi_0 fxordi_1 wa fxordi_0 fxordi_2 wa wb fxordi_0 fxordi_1 fxordi_2 wb annim fxordi_0 fxordi_1 fxordi_2 pm5.32 xchbinx $.
$}
$( A wff disjoined with truth is true.  (Contributed by NM, 23-May-1999.) $)
${
	$v ph $.
	$v ps $.
	fbiort_0 $f wff ph $.
	fbiort_1 $f wff ps $.
	biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $= fbiort_0 fbiort_0 fbiort_0 fbiort_1 wo fbiort_0 fbiort_1 orc fbiort_0 fbiort_0 fbiort_1 wo ax-1 impbid2 $.
$}
$( Theorem *5.55 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 20-Jan-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm5.55_0 $f wff ph $.
	fpm5.55_1 $f wff ps $.
	pm5.55 $p |- ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ) $= fpm5.55_0 fpm5.55_1 wo fpm5.55_0 wb fpm5.55_0 fpm5.55_1 wo fpm5.55_1 wb fpm5.55_0 fpm5.55_1 wo fpm5.55_1 wb fpm5.55_0 fpm5.55_1 wo fpm5.55_0 wb fpm5.55_0 fpm5.55_0 fpm5.55_1 wo fpm5.55_0 wb fpm5.55_0 fpm5.55_1 wo fpm5.55_1 wb fpm5.55_0 fpm5.55_0 fpm5.55_0 fpm5.55_1 wo fpm5.55_0 fpm5.55_1 biort bicomd fpm5.55_0 wn fpm5.55_1 fpm5.55_0 fpm5.55_1 wo fpm5.55_0 fpm5.55_1 biorf bicomd nsyl4 con1i orri $.
$}

