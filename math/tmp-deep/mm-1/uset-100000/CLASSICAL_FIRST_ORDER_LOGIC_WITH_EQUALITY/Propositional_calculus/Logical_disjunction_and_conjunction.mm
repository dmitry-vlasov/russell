$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_equivalence.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical disjunction and conjunction

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Here we define disjunction (logical 'or') ` \/ ` ( ~ df-or ) and conjunction
  (logical 'and') ` /\ ` ( ~ df-an ). We also define various rules for
  simplifying and applying them, e.g., ~ olc , ~ orc , and ~ orcom .

$)

$(Declare connectives for disjunction ('or') and conjunction ('and'). $)

$c \/ $.

$(Vee (read:  'or') $)

$c /\ $.

$(Wedge (read:  'and') $)

$(Extend wff definition to include disjunction ('or'). $)

${
	$v ph ps  $.
	f0_wo $f wff ph $.
	f1_wo $f wff ps $.
	a_wo $a wff ( ph \/ ps ) $.
$}

$(Extend wff definition to include conjunction ('and'). $)

${
	$v ph ps  $.
	f0_wa $f wff ph $.
	f1_wa $f wff ps $.
	a_wa $a wff ( ph /\ ps ) $.
$}

$(Define disjunction (logical 'or').  Definition of [Margaris] p. 49.  When
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
	$v ph ps  $.
	f0_df-or $f wff ph $.
	f1_df-or $f wff ps $.
	a_df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.
$}

$(Define conjunction (logical 'and').  Definition of [Margaris] p. 49.  When
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
	$v ph ps  $.
	f0_df-an $f wff ph $.
	f1_df-an $f wff ps $.
	a_df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.
$}

$(Theorem *4.64 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.64 $f wff ph $.
	f1_pm4.64 $f wff ps $.
	p_pm4.64 $p |- ( ( -. ph -> ps ) <-> ( ph \/ ps ) ) $= f0_pm4.64 f1_pm4.64 a_df-or f0_pm4.64 f1_pm4.64 a_wo f0_pm4.64 a_wn f1_pm4.64 a_wi p_bicomi $.
$}

$(Theorem *2.53 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.53 $f wff ph $.
	f1_pm2.53 $f wff ps $.
	p_pm2.53 $p |- ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $= f0_pm2.53 f1_pm2.53 a_df-or f0_pm2.53 f1_pm2.53 a_wo f0_pm2.53 a_wn f1_pm2.53 a_wi p_biimpi $.
$}

$(Theorem *2.54 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.54 $f wff ph $.
	f1_pm2.54 $f wff ps $.
	p_pm2.54 $p |- ( ( -. ph -> ps ) -> ( ph \/ ps ) ) $= f0_pm2.54 f1_pm2.54 a_df-or f0_pm2.54 f1_pm2.54 a_wo f0_pm2.54 a_wn f1_pm2.54 a_wi p_biimpri $.
$}

$(Infer implication from disjunction.  (Contributed by NM,
       11-Jun-1994.) $)

${
	$v ph ps  $.
	f0_ori $f wff ph $.
	f1_ori $f wff ps $.
	e0_ori $e |- ( ph \/ ps ) $.
	p_ori $p |- ( -. ph -> ps ) $= e0_ori f0_ori f1_ori a_df-or f0_ori f1_ori a_wo f0_ori a_wn f1_ori a_wi p_mpbi $.
$}

$(Infer implication from disjunction.  (Contributed by NM,
       11-Jun-1994.) $)

${
	$v ph ps  $.
	f0_orri $f wff ph $.
	f1_orri $f wff ps $.
	e0_orri $e |- ( -. ph -> ps ) $.
	p_orri $p |- ( ph \/ ps ) $= e0_orri f0_orri f1_orri a_df-or f0_orri f1_orri a_wo f0_orri a_wn f1_orri a_wi p_mpbir $.
$}

$(Deduce implication from disjunction.  (Contributed by NM,
       18-May-1994.) $)

${
	$v ph ps ch  $.
	f0_ord $f wff ph $.
	f1_ord $f wff ps $.
	f2_ord $f wff ch $.
	e0_ord $e |- ( ph -> ( ps \/ ch ) ) $.
	p_ord $p |- ( ph -> ( -. ps -> ch ) ) $= e0_ord f1_ord f2_ord a_df-or f0_ord f1_ord f2_ord a_wo f1_ord a_wn f2_ord a_wi p_sylib $.
$}

$(Deduce implication from disjunction.  (Contributed by NM,
       27-Nov-1995.) $)

${
	$v ph ps ch  $.
	f0_orrd $f wff ph $.
	f1_orrd $f wff ps $.
	f2_orrd $f wff ch $.
	e0_orrd $e |- ( ph -> ( -. ps -> ch ) ) $.
	p_orrd $p |- ( ph -> ( ps \/ ch ) ) $= e0_orrd f1_orrd f2_orrd p_pm2.54 f0_orrd f1_orrd a_wn f2_orrd a_wi f1_orrd f2_orrd a_wo p_syl $.
$}

$(Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 5-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_jaoi $f wff ph $.
	f1_jaoi $f wff ps $.
	f2_jaoi $f wff ch $.
	e0_jaoi $e |- ( ph -> ps ) $.
	e1_jaoi $e |- ( ch -> ps ) $.
	p_jaoi $p |- ( ( ph \/ ch ) -> ps ) $= f0_jaoi f2_jaoi p_pm2.53 e1_jaoi f0_jaoi f2_jaoi a_wo f0_jaoi a_wn f2_jaoi f1_jaoi p_syl6 e0_jaoi f0_jaoi f2_jaoi a_wo f0_jaoi f1_jaoi p_pm2.61d2 $.
$}

$(Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 18-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_jaod $f wff ph $.
	f1_jaod $f wff ps $.
	f2_jaod $f wff ch $.
	f3_jaod $f wff th $.
	e0_jaod $e |- ( ph -> ( ps -> ch ) ) $.
	e1_jaod $e |- ( ph -> ( th -> ch ) ) $.
	p_jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $= e0_jaod f0_jaod f1_jaod f2_jaod p_com12 e1_jaod f0_jaod f3_jaod f2_jaod p_com12 f1_jaod f0_jaod f2_jaod a_wi f3_jaod p_jaoi f1_jaod f3_jaod a_wo f0_jaod f2_jaod p_com12 $.
$}

$(Eliminate a disjunction in a deduction.  (Contributed by Mario Carneiro,
       29-May-2016.) $)

${
	$v ph ps ch th  $.
	f0_mpjaod $f wff ph $.
	f1_mpjaod $f wff ps $.
	f2_mpjaod $f wff ch $.
	f3_mpjaod $f wff th $.
	e0_mpjaod $e |- ( ph -> ( ps -> ch ) ) $.
	e1_mpjaod $e |- ( ph -> ( th -> ch ) ) $.
	e2_mpjaod $e |- ( ph -> ( ps \/ th ) ) $.
	p_mpjaod $p |- ( ph -> ch ) $= e2_mpjaod e0_mpjaod e1_mpjaod f0_mpjaod f1_mpjaod f2_mpjaod f3_mpjaod p_jaod f0_mpjaod f1_mpjaod f3_mpjaod a_wo f2_mpjaod p_mpd $.
$}

$(Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107.  (Contributed by NM, 12-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 21-Jul-2012.) $)

${
	$v ph ps  $.
	f0_orel1 $f wff ph $.
	f1_orel1 $f wff ps $.
	p_orel1 $p |- ( -. ph -> ( ( ph \/ ps ) -> ps ) ) $= f0_orel1 f1_orel1 p_pm2.53 f0_orel1 f1_orel1 a_wo f0_orel1 a_wn f1_orel1 p_com12 $.
$}

$(Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107.  (Contributed by NM, 12-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 5-Apr-2013.) $)

${
	$v ph ps  $.
	f0_orel2 $f wff ph $.
	f1_orel2 $f wff ps $.
	p_orel2 $p |- ( -. ph -> ( ( ps \/ ph ) -> ps ) ) $= f0_orel2 a_wn f1_orel2 p_idd f0_orel2 f1_orel2 p_pm2.21 f0_orel2 a_wn f1_orel2 f1_orel2 f0_orel2 p_jaod $.
$}

$(Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96.
     (Contributed by NM, 30-Aug-1993.) $)

${
	$v ph ps  $.
	f0_olc $f wff ph $.
	f1_olc $f wff ps $.
	p_olc $p |- ( ph -> ( ps \/ ph ) ) $= f0_olc f1_olc a_wn a_ax-1 f0_olc f1_olc f0_olc p_orrd $.
$}

$(Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 30-Aug-1993.) $)

${
	$v ph ps  $.
	f0_orc $f wff ph $.
	f1_orc $f wff ps $.
	p_orc $p |- ( ph -> ( ph \/ ps ) ) $= f0_orc f1_orc p_pm2.24 f0_orc f0_orc f1_orc p_orrd $.
$}

$(Axiom *1.4 of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm1.4 $f wff ph $.
	f1_pm1.4 $f wff ps $.
	p_pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $= f0_pm1.4 f1_pm1.4 p_olc f1_pm1.4 f0_pm1.4 p_orc f0_pm1.4 f1_pm1.4 f0_pm1.4 a_wo f1_pm1.4 p_jaoi $.
$}

$(Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 15-Nov-2012.) $)

${
	$v ph ps  $.
	f0_orcom $f wff ph $.
	f1_orcom $f wff ps $.
	p_orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $= f0_orcom f1_orcom p_pm1.4 f1_orcom f0_orcom p_pm1.4 f0_orcom f1_orcom a_wo f1_orcom f0_orcom a_wo p_impbii $.
$}

$(Commutation of disjuncts in consequent.  (Contributed by NM,
       2-Dec-2010.) $)

${
	$v ph ps ch  $.
	f0_orcomd $f wff ph $.
	f1_orcomd $f wff ps $.
	f2_orcomd $f wff ch $.
	e0_orcomd $e |- ( ph -> ( ps \/ ch ) ) $.
	p_orcomd $p |- ( ph -> ( ch \/ ps ) ) $= e0_orcomd f1_orcomd f2_orcomd p_orcom f0_orcomd f1_orcomd f2_orcomd a_wo f2_orcomd f1_orcomd a_wo p_sylib $.
$}

$(Commutation of disjuncts in antecedent.  (Contributed by NM,
       2-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_orcoms $f wff ph $.
	f1_orcoms $f wff ps $.
	f2_orcoms $f wff ch $.
	e0_orcoms $e |- ( ( ph \/ ps ) -> ch ) $.
	p_orcoms $p |- ( ( ps \/ ph ) -> ch ) $= f1_orcoms f0_orcoms p_pm1.4 e0_orcoms f1_orcoms f0_orcoms a_wo f0_orcoms f1_orcoms a_wo f2_orcoms p_syl $.
$}

$(Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)

${
	$v ph ps  $.
	f0_orci $f wff ph $.
	f1_orci $f wff ps $.
	e0_orci $e |- ph $.
	p_orci $p |- ( ph \/ ps ) $= e0_orci f0_orci f1_orci p_pm2.24i f0_orci f1_orci p_orri $.
$}

$(Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)

${
	$v ph ps  $.
	f0_olci $f wff ph $.
	f1_olci $f wff ps $.
	e0_olci $e |- ph $.
	p_olci $p |- ( ps \/ ph ) $= e0_olci f0_olci f1_olci a_wn p_a1i f1_olci f0_olci p_orri $.
$}

$(Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IR ( ` \/ ` insertion right), see ~ natded .  (Contributed
       by NM, 20-Sep-2007.) $)

${
	$v ph ps ch  $.
	f0_orcd $f wff ph $.
	f1_orcd $f wff ps $.
	f2_orcd $f wff ch $.
	e0_orcd $e |- ( ph -> ps ) $.
	p_orcd $p |- ( ph -> ( ps \/ ch ) ) $= e0_orcd f1_orcd f2_orcd p_orc f0_orcd f1_orcd f1_orcd f2_orcd a_wo p_syl $.
$}

$(Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IL ( ` \/ ` insertion left), see ~ natded .  (Contributed by
       NM, 11-Apr-2008.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)

${
	$v ph ps ch  $.
	f0_olcd $f wff ph $.
	f1_olcd $f wff ps $.
	f2_olcd $f wff ch $.
	e0_olcd $e |- ( ph -> ps ) $.
	p_olcd $p |- ( ph -> ( ch \/ ps ) ) $= e0_olcd f0_olcd f1_olcd f2_olcd p_orcd f0_olcd f1_olcd f2_olcd p_orcomd $.
$}

$(Deduction eliminating disjunct. _Notational convention_:  We sometimes
       suffix with "s" the label of an inference that manipulates an
       antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof.  (Contributed by NM, 21-Jun-1994.) $)

${
	$v ph ps ch  $.
	f0_orcs $f wff ph $.
	f1_orcs $f wff ps $.
	f2_orcs $f wff ch $.
	e0_orcs $e |- ( ( ph \/ ps ) -> ch ) $.
	p_orcs $p |- ( ph -> ch ) $= f0_orcs f1_orcs p_orc e0_orcs f0_orcs f0_orcs f1_orcs a_wo f2_orcs p_syl $.
$}

$(Deduction eliminating disjunct.  (Contributed by NM, 21-Jun-1994.)
       (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)

${
	$v ph ps ch  $.
	f0_olcs $f wff ph $.
	f1_olcs $f wff ps $.
	f2_olcs $f wff ch $.
	e0_olcs $e |- ( ( ph \/ ps ) -> ch ) $.
	p_olcs $p |- ( ps -> ch ) $= e0_olcs f0_olcs f1_olcs f2_olcs p_orcoms f1_olcs f0_olcs f2_olcs p_orcs $.
$}

$(Theorem *2.07 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph  $.
	f0_pm2.07 $f wff ph $.
	p_pm2.07 $p |- ( ph -> ( ph \/ ph ) ) $= f0_pm2.07 f0_pm2.07 p_olc $.
$}

$(Theorem *2.45 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.45 $f wff ph $.
	f1_pm2.45 $f wff ps $.
	p_pm2.45 $p |- ( -. ( ph \/ ps ) -> -. ph ) $= f0_pm2.45 f1_pm2.45 p_orc f0_pm2.45 f0_pm2.45 f1_pm2.45 a_wo p_con3i $.
$}

$(Theorem *2.46 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.46 $f wff ph $.
	f1_pm2.46 $f wff ps $.
	p_pm2.46 $p |- ( -. ( ph \/ ps ) -> -. ps ) $= f1_pm2.46 f0_pm2.46 p_olc f1_pm2.46 f0_pm2.46 f1_pm2.46 a_wo p_con3i $.
$}

$(Theorem *2.47 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.47 $f wff ph $.
	f1_pm2.47 $f wff ps $.
	p_pm2.47 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) ) $= f0_pm2.47 f1_pm2.47 p_pm2.45 f0_pm2.47 f1_pm2.47 a_wo a_wn f0_pm2.47 a_wn f1_pm2.47 p_orcd $.
$}

$(Theorem *2.48 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.48 $f wff ph $.
	f1_pm2.48 $f wff ps $.
	p_pm2.48 $p |- ( -. ( ph \/ ps ) -> ( ph \/ -. ps ) ) $= f0_pm2.48 f1_pm2.48 p_pm2.46 f0_pm2.48 f1_pm2.48 a_wo a_wn f1_pm2.48 a_wn f0_pm2.48 p_olcd $.
$}

$(Theorem *2.49 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.49 $f wff ph $.
	f1_pm2.49 $f wff ps $.
	p_pm2.49 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) ) $= f0_pm2.49 f1_pm2.49 p_pm2.46 f0_pm2.49 f1_pm2.49 a_wo a_wn f1_pm2.49 a_wn f0_pm2.49 a_wn p_olcd $.
$}

$(Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.67-2 $f wff ph $.
	f1_pm2.67-2 $f wff ps $.
	f2_pm2.67-2 $f wff ch $.
	p_pm2.67-2 $p |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) ) $= f0_pm2.67-2 f2_pm2.67-2 p_orc f0_pm2.67-2 f0_pm2.67-2 f2_pm2.67-2 a_wo f1_pm2.67-2 p_imim1i $.
$}

$(Theorem *2.67 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.67 $f wff ph $.
	f1_pm2.67 $f wff ps $.
	p_pm2.67 $p |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $= f0_pm2.67 f1_pm2.67 f1_pm2.67 p_pm2.67-2 $.
$}

$(Theorem *2.25 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.25 $f wff ph $.
	f1_pm2.25 $f wff ps $.
	p_pm2.25 $p |- ( ph \/ ( ( ph \/ ps ) -> ps ) ) $= f0_pm2.25 f1_pm2.25 p_orel1 f0_pm2.25 f0_pm2.25 f1_pm2.25 a_wo f1_pm2.25 a_wi p_orri $.
$}

$(A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 23-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 18-Nov-2012.) $)

${
	$v ph ps  $.
	f0_biorf $f wff ph $.
	f1_biorf $f wff ps $.
	p_biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $= f1_biorf f0_biorf p_olc f0_biorf f1_biorf p_orel1 f0_biorf a_wn f1_biorf f0_biorf f1_biorf a_wo p_impbid2 $.
$}

$(A wff is equivalent to its negated disjunction with falsehood.
     (Contributed by NM, 9-Jul-2012.) $)

${
	$v ph ps  $.
	f0_biortn $f wff ph $.
	f1_biortn $f wff ps $.
	p_biortn $p |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) ) $= f0_biortn p_notnot1 f0_biortn a_wn f1_biortn p_biorf f0_biortn f0_biortn a_wn a_wn f1_biortn f0_biortn a_wn f1_biortn a_wo a_wb p_syl $.
$}

$(A wff is equivalent to its disjunction with falsehood.  (Contributed by
       NM, 23-Mar-1995.) $)

${
	$v ph ps  $.
	f0_biorfi $f wff ph $.
	f1_biorfi $f wff ps $.
	e0_biorfi $e |- -. ph $.
	p_biorfi $p |- ( ps <-> ( ps \/ ph ) ) $= e0_biorfi f1_biorfi f0_biorfi p_orc f0_biorfi f1_biorfi p_orel2 f0_biorfi a_wn f1_biorfi f1_biorfi f0_biorfi a_wo p_impbid2 f0_biorfi a_wn f1_biorfi f1_biorfi f0_biorfi a_wo a_wb a_ax-mp $.
$}

$(Theorem *2.621 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.621 $f wff ph $.
	f1_pm2.621 $f wff ps $.
	p_pm2.621 $p |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $= f0_pm2.621 f1_pm2.621 a_wi p_id f0_pm2.621 f1_pm2.621 a_wi f1_pm2.621 p_idd f0_pm2.621 f1_pm2.621 a_wi f0_pm2.621 f1_pm2.621 f1_pm2.621 p_jaod $.
$}

$(Theorem *2.62 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Dec-2013.) $)

${
	$v ph ps  $.
	f0_pm2.62 $f wff ph $.
	f1_pm2.62 $f wff ps $.
	p_pm2.62 $p |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $= f0_pm2.62 f1_pm2.62 p_pm2.621 f0_pm2.62 f1_pm2.62 a_wi f0_pm2.62 f1_pm2.62 a_wo f1_pm2.62 p_com12 $.
$}

$(Theorem *2.68 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.68 $f wff ph $.
	f1_pm2.68 $f wff ps $.
	p_pm2.68 $p |- ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) $= f0_pm2.68 f1_pm2.68 f1_pm2.68 p_jarl f0_pm2.68 f1_pm2.68 a_wi f1_pm2.68 a_wi f0_pm2.68 f1_pm2.68 p_orrd $.
$}

$(Logical 'or' expressed in terms of implication only.  Theorem *5.25 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 12-Aug-2004.)  (Proof
     shortened by Wolf Lammen, 20-Oct-2012.) $)

${
	$v ph ps  $.
	f0_dfor2 $f wff ph $.
	f1_dfor2 $f wff ps $.
	p_dfor2 $p |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) $= f0_dfor2 f1_dfor2 p_pm2.62 f0_dfor2 f1_dfor2 p_pm2.68 f0_dfor2 f1_dfor2 a_wo f0_dfor2 f1_dfor2 a_wi f1_dfor2 a_wi p_impbii $.
$}

$(Implication in terms of disjunction.  Theorem *4.6 of [WhiteheadRussell]
     p. 120.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_imor $f wff ph $.
	f1_imor $f wff ps $.
	p_imor $p |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) $= f0_imor p_notnot f0_imor f0_imor a_wn a_wn f1_imor p_imbi1i f0_imor a_wn f1_imor a_df-or f0_imor f1_imor a_wi f0_imor a_wn a_wn f1_imor a_wi f0_imor a_wn f1_imor a_wo p_bitr4i $.
$}

$(Infer disjunction from implication.  (Contributed by NM,
       12-Mar-2012.) $)

${
	$v ph ps  $.
	f0_imori $f wff ph $.
	f1_imori $f wff ps $.
	e0_imori $e |- ( ph -> ps ) $.
	p_imori $p |- ( -. ph \/ ps ) $= e0_imori f0_imori f1_imori p_imor f0_imori f1_imori a_wi f0_imori a_wn f1_imori a_wo p_mpbi $.
$}

$(Infer implication from disjunction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)

${
	$v ph ps  $.
	f0_imorri $f wff ph $.
	f1_imorri $f wff ps $.
	e0_imorri $e |- ( -. ph \/ ps ) $.
	p_imorri $p |- ( ph -> ps ) $= e0_imorri f0_imorri f1_imorri p_imor f0_imorri f1_imorri a_wi f0_imorri a_wn f1_imorri a_wo p_mpbir $.
$}

$(Law of excluded middle, also called the principle of _tertium non datur_.
     Theorem *2.11 of [WhiteheadRussell] p. 101.  It says that something is
     either true or not true; there are no in-between values of truth.  This is
     an essential distinction of our classical logic and is not a theorem of
     intuitionistic logic.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph  $.
	f0_exmid $f wff ph $.
	p_exmid $p |- ( ph \/ -. ph ) $= f0_exmid a_wn p_id f0_exmid f0_exmid a_wn p_orri $.
$}

$(Law of excluded middle in a context.  (Contributed by Mario Carneiro,
     9-Feb-2017.) $)

${
	$v ph ps  $.
	f0_exmidd $f wff ph $.
	f1_exmidd $f wff ps $.
	p_exmidd $p |- ( ph -> ( ps \/ -. ps ) ) $= f1_exmidd p_exmid f1_exmidd f1_exmidd a_wn a_wo f0_exmidd p_a1i $.
$}

$(Theorem *2.1 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)

${
	$v ph  $.
	f0_pm2.1 $f wff ph $.
	p_pm2.1 $p |- ( -. ph \/ ph ) $= f0_pm2.1 p_id f0_pm2.1 f0_pm2.1 p_imori $.
$}

$(Theorem *2.13 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph  $.
	f0_pm2.13 $f wff ph $.
	p_pm2.13 $p |- ( ph \/ -. -. -. ph ) $= f0_pm2.13 a_wn p_notnot1 f0_pm2.13 f0_pm2.13 a_wn a_wn a_wn p_orri $.
$}

$(Theorem *4.62 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.62 $f wff ph $.
	f1_pm4.62 $f wff ps $.
	p_pm4.62 $p |- ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) $= f0_pm4.62 f1_pm4.62 a_wn p_imor $.
$}

$(Theorem *4.66 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.66 $f wff ph $.
	f1_pm4.66 $f wff ps $.
	p_pm4.66 $p |- ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) ) $= f0_pm4.66 f1_pm4.66 a_wn p_pm4.64 $.
$}

$(Theorem *4.63 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.63 $f wff ph $.
	f1_pm4.63 $f wff ps $.
	p_pm4.63 $p |- ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) $= f0_pm4.63 f1_pm4.63 a_df-an f0_pm4.63 f1_pm4.63 a_wa f0_pm4.63 f1_pm4.63 a_wn a_wi a_wn p_bicomi $.
$}

$(Express implication in terms of conjunction.  (Contributed by NM,
     9-Apr-1994.) $)

${
	$v ph ps  $.
	f0_imnan $f wff ph $.
	f1_imnan $f wff ps $.
	p_imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $= f0_imnan f1_imnan a_df-an f0_imnan f1_imnan a_wa f0_imnan f1_imnan a_wn a_wi p_con2bii $.
$}

$(Express implication in terms of conjunction.  (Contributed by Mario
       Carneiro, 28-Sep-2015.) $)

${
	$v ph ps  $.
	f0_imnani $f wff ph $.
	f1_imnani $f wff ps $.
	e0_imnani $e |- -. ( ph /\ ps ) $.
	p_imnani $p |- ( ph -> -. ps ) $= e0_imnani f0_imnani f1_imnani p_imnan f0_imnani f1_imnani a_wn a_wi f0_imnani f1_imnani a_wa a_wn p_mpbir $.
$}

$(Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 30-Oct-2012.) $)

${
	$v ph ps  $.
	f0_iman $f wff ph $.
	f1_iman $f wff ps $.
	p_iman $p |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) $= f1_iman p_notnot f1_iman f1_iman a_wn a_wn f0_iman p_imbi2i f0_iman f1_iman a_wn p_imnan f0_iman f1_iman a_wi f0_iman f1_iman a_wn a_wn a_wi f0_iman f1_iman a_wn a_wa a_wn p_bitri $.
$}

$(Express conjunction in terms of implication.  (Contributed by NM,
     2-Aug-1994.) $)

${
	$v ph ps  $.
	f0_annim $f wff ph $.
	f1_annim $f wff ps $.
	p_annim $p |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) $= f0_annim f1_annim p_iman f0_annim f1_annim a_wi f0_annim f1_annim a_wn a_wa p_con2bii $.
$}

$(Theorem *4.61 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.61 $f wff ph $.
	f1_pm4.61 $f wff ps $.
	p_pm4.61 $p |- ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) ) $= f0_pm4.61 f1_pm4.61 p_annim f0_pm4.61 f1_pm4.61 a_wn a_wa f0_pm4.61 f1_pm4.61 a_wi a_wn p_bicomi $.
$}

$(Theorem *4.65 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.65 $f wff ph $.
	f1_pm4.65 $f wff ps $.
	p_pm4.65 $p |- ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) ) $= f0_pm4.65 a_wn f1_pm4.65 p_pm4.61 $.
$}

$(Theorem *4.67 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.67 $f wff ph $.
	f1_pm4.67 $f wff ps $.
	p_pm4.67 $p |- ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) $= f0_pm4.67 a_wn f1_pm4.67 p_pm4.63 $.
$}

$(Importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Eric Schmidt, 22-Dec-2006.) $)

${
	$v ph ps ch  $.
	f0_imp $f wff ph $.
	f1_imp $f wff ps $.
	f2_imp $f wff ch $.
	e0_imp $e |- ( ph -> ( ps -> ch ) ) $.
	p_imp $p |- ( ( ph /\ ps ) -> ch ) $= f0_imp f1_imp a_df-an e0_imp f0_imp f1_imp f2_imp p_impi f0_imp f1_imp a_wa f0_imp f1_imp a_wn a_wi a_wn f2_imp p_sylbi $.
$}

$(Importation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)

${
	$v ph ps ch  $.
	f0_impcom $f wff ph $.
	f1_impcom $f wff ps $.
	f2_impcom $f wff ch $.
	e0_impcom $e |- ( ph -> ( ps -> ch ) ) $.
	p_impcom $p |- ( ( ps /\ ph ) -> ch ) $= e0_impcom f0_impcom f1_impcom f2_impcom p_com12 f1_impcom f0_impcom f2_impcom p_imp $.
$}

$(Importation deduction.  (Contributed by NM, 31-Mar-1994.) $)

${
	$v ph ps ch th  $.
	f0_imp3a $f wff ph $.
	f1_imp3a $f wff ps $.
	f2_imp3a $f wff ch $.
	f3_imp3a $f wff th $.
	e0_imp3a $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_imp3a $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= e0_imp3a f0_imp3a f1_imp3a f2_imp3a f3_imp3a p_com3l f1_imp3a f2_imp3a f0_imp3a f3_imp3a a_wi p_imp f1_imp3a f2_imp3a a_wa f0_imp3a f3_imp3a p_com12 $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_imp31 $f wff ph $.
	f1_imp31 $f wff ps $.
	f2_imp31 $f wff ch $.
	f3_imp31 $f wff th $.
	e0_imp31 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $= e0_imp31 f0_imp31 f1_imp31 f2_imp31 f3_imp31 a_wi p_imp f0_imp31 f1_imp31 a_wa f2_imp31 f3_imp31 p_imp $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_imp32 $f wff ph $.
	f1_imp32 $f wff ps $.
	f2_imp32 $f wff ch $.
	f3_imp32 $f wff th $.
	e0_imp32 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $= e0_imp32 f0_imp32 f1_imp32 f2_imp32 f3_imp32 p_imp3a f0_imp32 f1_imp32 f2_imp32 a_wa f3_imp32 p_imp $.
$}

$(Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  A translation of natural deduction
       rule ` -> ` I ( ` -> ` introduction), see ~ natded .  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)

${
	$v ph ps ch  $.
	f0_ex $f wff ph $.
	f1_ex $f wff ps $.
	f2_ex $f wff ch $.
	e0_ex $e |- ( ( ph /\ ps ) -> ch ) $.
	p_ex $p |- ( ph -> ( ps -> ch ) ) $= f0_ex f1_ex a_df-an e0_ex f0_ex f1_ex a_wn a_wi a_wn f0_ex f1_ex a_wa f2_ex p_sylbir f0_ex f1_ex f2_ex p_expi $.
$}

$(Exportation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)

${
	$v ph ps ch  $.
	f0_expcom $f wff ph $.
	f1_expcom $f wff ps $.
	f2_expcom $f wff ch $.
	e0_expcom $e |- ( ( ph /\ ps ) -> ch ) $.
	p_expcom $p |- ( ps -> ( ph -> ch ) ) $= e0_expcom f0_expcom f1_expcom f2_expcom p_ex f0_expcom f1_expcom f2_expcom p_com12 $.
$}

$(Exportation deduction.  (Contributed by NM, 20-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_exp3a $f wff ph $.
	f1_exp3a $f wff ps $.
	f2_exp3a $f wff ch $.
	f3_exp3a $f wff th $.
	e0_exp3a $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_exp3a $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= e0_exp3a f0_exp3a f1_exp3a f2_exp3a a_wa f3_exp3a p_com12 f1_exp3a f2_exp3a f0_exp3a f3_exp3a a_wi p_ex f1_exp3a f2_exp3a f0_exp3a f3_exp3a p_com3r $.
$}

$(A deduction version of exportation, followed by importation.
       (Contributed by NM, 6-Sep-2008.) $)

${
	$v ph ps ch th  $.
	f0_expdimp $f wff ph $.
	f1_expdimp $f wff ps $.
	f2_expdimp $f wff ch $.
	f3_expdimp $f wff th $.
	e0_expdimp $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $= e0_expdimp f0_expdimp f1_expdimp f2_expdimp f3_expdimp p_exp3a f0_expdimp f1_expdimp f2_expdimp f3_expdimp a_wi p_imp $.
$}

$(Mixed importation/commutation inference.  (Contributed by NM,
       22-Jun-2013.) $)

${
	$v ph ps ch th  $.
	f0_impancom $f wff ph $.
	f1_impancom $f wff ps $.
	f2_impancom $f wff ch $.
	f3_impancom $f wff th $.
	e0_impancom $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	p_impancom $p |- ( ( ph /\ ch ) -> ( ps -> th ) ) $= e0_impancom f0_impancom f1_impancom f2_impancom f3_impancom a_wi p_ex f0_impancom f1_impancom f2_impancom f3_impancom p_com23 f0_impancom f2_impancom f1_impancom f3_impancom a_wi p_imp $.
$}

$(Variant of ~ con3d with importation.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)

${
	$v ph ps ch  $.
	f0_con3and $f wff ph $.
	f1_con3and $f wff ps $.
	f2_con3and $f wff ch $.
	e0_con3and $e |- ( ph -> ( ps -> ch ) ) $.
	p_con3and $p |- ( ( ph /\ -. ch ) -> -. ps ) $= e0_con3and f0_con3and f1_con3and f2_con3and p_con3d f0_con3and f2_con3and a_wn f1_con3and a_wn p_imp $.
$}

$(Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)

${
	$v ph ps  $.
	f0_pm2.01da $f wff ph $.
	f1_pm2.01da $f wff ps $.
	e0_pm2.01da $e |- ( ( ph /\ ps ) -> -. ps ) $.
	p_pm2.01da $p |- ( ph -> -. ps ) $= e0_pm2.01da f0_pm2.01da f1_pm2.01da f1_pm2.01da a_wn p_ex f0_pm2.01da f1_pm2.01da p_pm2.01d $.
$}

$(Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)

${
	$v ph ps  $.
	f0_pm2.18da $f wff ph $.
	f1_pm2.18da $f wff ps $.
	e0_pm2.18da $e |- ( ( ph /\ -. ps ) -> ps ) $.
	p_pm2.18da $p |- ( ph -> ps ) $= e0_pm2.18da f0_pm2.18da f1_pm2.18da a_wn f1_pm2.18da p_ex f0_pm2.18da f1_pm2.18da p_pm2.18d $.
$}

$(Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)

${
	$v ph ps ch  $.
	f0_pm3.3 $f wff ph $.
	f1_pm3.3 $f wff ps $.
	f2_pm3.3 $f wff ch $.
	p_pm3.3 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $= f0_pm3.3 f1_pm3.3 a_wa f2_pm3.3 a_wi p_id f0_pm3.3 f1_pm3.3 a_wa f2_pm3.3 a_wi f0_pm3.3 f1_pm3.3 f2_pm3.3 p_exp3a $.
$}

$(Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)

${
	$v ph ps ch  $.
	f0_pm3.31 $f wff ph $.
	f1_pm3.31 $f wff ps $.
	f2_pm3.31 $f wff ch $.
	p_pm3.31 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $= f0_pm3.31 f1_pm3.31 f2_pm3.31 a_wi a_wi p_id f0_pm3.31 f1_pm3.31 f2_pm3.31 a_wi a_wi f0_pm3.31 f1_pm3.31 f2_pm3.31 p_imp3a $.
$}

$(Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Mar-2013.) $)

${
	$v ph ps ch  $.
	f0_impexp $f wff ph $.
	f1_impexp $f wff ps $.
	f2_impexp $f wff ch $.
	p_impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $= f0_impexp f1_impexp f2_impexp p_pm3.3 f0_impexp f1_impexp f2_impexp p_pm3.31 f0_impexp f1_impexp a_wa f2_impexp a_wi f0_impexp f1_impexp f2_impexp a_wi a_wi p_impbii $.
$}

$(Join antecedents with conjunction.  Theorem *3.2 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 12-Nov-2012.) $)

${
	$v ph ps  $.
	f0_pm3.2 $f wff ph $.
	f1_pm3.2 $f wff ps $.
	p_pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $= f0_pm3.2 f1_pm3.2 a_wa p_id f0_pm3.2 f1_pm3.2 f0_pm3.2 f1_pm3.2 a_wa p_ex $.
$}

$(Join antecedents with conjunction.  Theorem *3.21 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_pm3.21 $f wff ph $.
	f1_pm3.21 $f wff ps $.
	p_pm3.21 $p |- ( ph -> ( ps -> ( ps /\ ph ) ) ) $= f1_pm3.21 f0_pm3.21 p_pm3.2 f1_pm3.21 f0_pm3.21 f1_pm3.21 f0_pm3.21 a_wa p_com12 $.
$}

$(Theorem *3.22 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Nov-2012.) $)

${
	$v ph ps  $.
	f0_pm3.22 $f wff ph $.
	f1_pm3.22 $f wff ps $.
	p_pm3.22 $p |- ( ( ph /\ ps ) -> ( ps /\ ph ) ) $= f0_pm3.22 f1_pm3.22 p_pm3.21 f0_pm3.22 f1_pm3.22 f1_pm3.22 f0_pm3.22 a_wa p_imp $.
$}

$(Commutative law for conjunction.  Theorem *4.3 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 25-Jun-1998.)  (Proof shortened by Wolf
     Lammen, 4-Nov-2012.) $)

${
	$v ph ps  $.
	f0_ancom $f wff ph $.
	f1_ancom $f wff ps $.
	p_ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $= f0_ancom f1_ancom p_pm3.22 f1_ancom f0_ancom p_pm3.22 f0_ancom f1_ancom a_wa f1_ancom f0_ancom a_wa p_impbii $.
$}

$(Commutation of conjuncts in consequent.  (Contributed by Jeff Hankins,
       14-Aug-2009.) $)

${
	$v ph ps ch  $.
	f0_ancomd $f wff ph $.
	f1_ancomd $f wff ps $.
	f2_ancomd $f wff ch $.
	e0_ancomd $e |- ( ph -> ( ps /\ ch ) ) $.
	p_ancomd $p |- ( ph -> ( ch /\ ps ) ) $= e0_ancomd f1_ancomd f2_ancomd p_ancom f0_ancomd f1_ancomd f2_ancomd a_wa f2_ancomd f1_ancomd a_wa p_sylib $.
$}

$(Inference commuting conjunction in antecedent.  (Contributed by NM,
       21-Apr-1994.) $)

${
	$v ph ps ch  $.
	f0_ancoms $f wff ph $.
	f1_ancoms $f wff ps $.
	f2_ancoms $f wff ch $.
	e0_ancoms $e |- ( ( ph /\ ps ) -> ch ) $.
	p_ancoms $p |- ( ( ps /\ ph ) -> ch ) $= e0_ancoms f0_ancoms f1_ancoms f2_ancoms p_expcom f1_ancoms f0_ancoms f2_ancoms p_imp $.
$}

$(Deduction commuting conjunction in antecedent.  (Contributed by NM,
       12-Dec-2004.) $)

${
	$v ph ps ch th  $.
	f0_ancomsd $f wff ph $.
	f1_ancomsd $f wff ps $.
	f2_ancomsd $f wff ch $.
	f3_ancomsd $f wff th $.
	e0_ancomsd $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $= f2_ancomsd f1_ancomsd p_ancom e0_ancomsd f2_ancomsd f1_ancomsd a_wa f1_ancomsd f2_ancomsd a_wa f0_ancomsd f3_ancomsd p_syl5bi $.
$}

$(Infer conjunction of premises.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_pm3.2i $f wff ph $.
	f1_pm3.2i $f wff ps $.
	e0_pm3.2i $e |- ph $.
	e1_pm3.2i $e |- ps $.
	p_pm3.2i $p |- ( ph /\ ps ) $= e0_pm3.2i e1_pm3.2i f0_pm3.2i f1_pm3.2i p_pm3.2 f0_pm3.2i f1_pm3.2i f0_pm3.2i f1_pm3.2i a_wa p_mp2 $.
$}

$(Nested conjunction of antecedents.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_pm3.43i $f wff ph $.
	f1_pm3.43i $f wff ps $.
	f2_pm3.43i $f wff ch $.
	p_pm3.43i $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $= f1_pm3.43i f2_pm3.43i p_pm3.2 f1_pm3.43i f2_pm3.43i f1_pm3.43i f2_pm3.43i a_wa f0_pm3.43i p_imim3i $.
$}

$(Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)

${
	$v ph ps  $.
	f0_simpl $f wff ph $.
	f1_simpl $f wff ps $.
	p_simpl $p |- ( ( ph /\ ps ) -> ph ) $= f0_simpl f1_simpl a_ax-1 f0_simpl f1_simpl f0_simpl p_imp $.
$}

$(Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)

${
	$v ph ps  $.
	f0_simpli $f wff ph $.
	f1_simpli $f wff ps $.
	e0_simpli $e |- ( ph /\ ps ) $.
	p_simpli $p |- ph $= e0_simpli f0_simpli f1_simpli p_simpl f0_simpli f1_simpli a_wa f0_simpli a_ax-mp $.
$}

$(Deduction eliminating a conjunct.  A translation of natural deduction
       rule ` /\ ` EL ( ` /\ ` elimination left), see ~ natded .  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_simpld $f wff ph $.
	f1_simpld $f wff ps $.
	f2_simpld $f wff ch $.
	e0_simpld $e |- ( ph -> ( ps /\ ch ) ) $.
	p_simpld $p |- ( ph -> ps ) $= e0_simpld f1_simpld f2_simpld p_simpl f0_simpld f1_simpld f2_simpld a_wa f1_simpld p_syl $.
$}

$(Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)

${
	$v ph ps ch  $.
	f0_simplbi $f wff ph $.
	f1_simplbi $f wff ps $.
	f2_simplbi $f wff ch $.
	e0_simplbi $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_simplbi $p |- ( ph -> ps ) $= e0_simplbi f0_simplbi f1_simplbi f2_simplbi a_wa p_biimpi f0_simplbi f1_simplbi f2_simplbi p_simpld $.
$}

$(Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)

${
	$v ph ps  $.
	f0_simpr $f wff ph $.
	f1_simpr $f wff ps $.
	p_simpr $p |- ( ( ph /\ ps ) -> ps ) $= f0_simpr f1_simpr p_idd f0_simpr f1_simpr f1_simpr p_imp $.
$}

$(Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)

${
	$v ph ps  $.
	f0_simpri $f wff ph $.
	f1_simpri $f wff ps $.
	e0_simpri $e |- ( ph /\ ps ) $.
	p_simpri $p |- ps $= e0_simpri f0_simpri f1_simpri p_simpr f0_simpri f1_simpri a_wa f1_simpri a_ax-mp $.
$}

$(Deduction eliminating a conjunct.  (Contributed by NM, 5-Aug-1993.)  A
       translation of natural deduction rule ` /\ ` ER ( ` /\ ` elimination
       right), see ~ natded .  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)

${
	$v ph ps ch  $.
	f0_simprd $f wff ph $.
	f1_simprd $f wff ps $.
	f2_simprd $f wff ch $.
	e0_simprd $e |- ( ph -> ( ps /\ ch ) ) $.
	p_simprd $p |- ( ph -> ch ) $= e0_simprd f0_simprd f1_simprd f2_simprd p_ancomd f0_simprd f2_simprd f1_simprd p_simpld $.
$}

$(Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)

${
	$v ph ps ch  $.
	f0_simprbi $f wff ph $.
	f1_simprbi $f wff ps $.
	f2_simprbi $f wff ch $.
	e0_simprbi $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_simprbi $p |- ( ph -> ch ) $= e0_simprbi f0_simprbi f1_simprbi f2_simprbi a_wa p_biimpi f0_simprbi f1_simprbi f2_simprbi p_simprd $.
$}

$(Inference adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 30-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_adantr $f wff ph $.
	f1_adantr $f wff ps $.
	f2_adantr $f wff ch $.
	e0_adantr $e |- ( ph -> ps ) $.
	p_adantr $p |- ( ( ph /\ ch ) -> ps ) $= e0_adantr f0_adantr f1_adantr f2_adantr p_a1d f0_adantr f2_adantr f1_adantr p_imp $.
$}

$(Inference adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 30-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_adantl $f wff ph $.
	f1_adantl $f wff ps $.
	f2_adantl $f wff ch $.
	e0_adantl $e |- ( ph -> ps ) $.
	p_adantl $p |- ( ( ch /\ ph ) -> ps ) $= e0_adantl f0_adantl f1_adantl f2_adantl p_adantr f0_adantl f2_adantl f1_adantl p_ancoms $.
$}

$(Deduction adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 4-May-1994.)  (Proof shortened by Wolf Lammen, 20-Dec-2012.) $)

${
	$v ph ps ch th  $.
	f0_adantld $f wff ph $.
	f1_adantld $f wff ps $.
	f2_adantld $f wff ch $.
	f3_adantld $f wff th $.
	e0_adantld $e |- ( ph -> ( ps -> ch ) ) $.
	p_adantld $p |- ( ph -> ( ( th /\ ps ) -> ch ) ) $= f3_adantld f1_adantld p_simpr e0_adantld f3_adantld f1_adantld a_wa f1_adantld f0_adantld f2_adantld p_syl5 $.
$}

$(Deduction adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 4-May-1994.) $)

${
	$v ph ps ch th  $.
	f0_adantrd $f wff ph $.
	f1_adantrd $f wff ps $.
	f2_adantrd $f wff ch $.
	f3_adantrd $f wff th $.
	e0_adantrd $e |- ( ph -> ( ps -> ch ) ) $.
	p_adantrd $p |- ( ph -> ( ( ps /\ th ) -> ch ) ) $= f1_adantrd f3_adantrd p_simpl e0_adantrd f1_adantrd f3_adantrd a_wa f1_adantrd f0_adantrd f2_adantrd p_syl5 $.
$}

$(Modus ponens conjoining dissimilar antecedents.  (Contributed by NM,
       1-Feb-2008.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch th  $.
	f0_mpan9 $f wff ph $.
	f1_mpan9 $f wff ps $.
	f2_mpan9 $f wff ch $.
	f3_mpan9 $f wff th $.
	e0_mpan9 $e |- ( ph -> ps ) $.
	e1_mpan9 $e |- ( ch -> ( ps -> th ) ) $.
	p_mpan9 $p |- ( ( ph /\ ch ) -> th ) $= e0_mpan9 e1_mpan9 f0_mpan9 f1_mpan9 f2_mpan9 f3_mpan9 p_syl5 f2_mpan9 f0_mpan9 f3_mpan9 p_impcom $.
$}

$(A syllogism deduction with conjoined antecedents.  (Contributed by NM,
       24-Feb-2005.)  (Proof shortened by Wolf Lammen, 6-Apr-2013.) $)

${
	$v ph ps ch th  $.
	f0_syldan $f wff ph $.
	f1_syldan $f wff ps $.
	f2_syldan $f wff ch $.
	f3_syldan $f wff th $.
	e0_syldan $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_syldan $e |- ( ( ph /\ ch ) -> th ) $.
	p_syldan $p |- ( ( ph /\ ps ) -> th ) $= e0_syldan e1_syldan f0_syldan f2_syldan f3_syldan p_expcom f2_syldan f0_syldan f3_syldan f1_syldan p_adantrd f2_syldan f0_syldan f1_syldan a_wa f3_syldan p_mpcom $.
$}

$(A syllogism inference.  (Contributed by NM, 21-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_sylan $f wff ph $.
	f1_sylan $f wff ps $.
	f2_sylan $f wff ch $.
	f3_sylan $f wff th $.
	e0_sylan $e |- ( ph -> ps ) $.
	e1_sylan $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylan $p |- ( ( ph /\ ch ) -> th ) $= e0_sylan e1_sylan f1_sylan f2_sylan f3_sylan p_expcom f0_sylan f1_sylan f2_sylan f3_sylan p_mpan9 $.
$}

$(A syllogism inference.  (Contributed by NM, 18-May-1994.) $)

${
	$v ph ps ch th  $.
	f0_sylanb $f wff ph $.
	f1_sylanb $f wff ps $.
	f2_sylanb $f wff ch $.
	f3_sylanb $f wff th $.
	e0_sylanb $e |- ( ph <-> ps ) $.
	e1_sylanb $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylanb $p |- ( ( ph /\ ch ) -> th ) $= e0_sylanb f0_sylanb f1_sylanb p_biimpi e1_sylanb f0_sylanb f1_sylanb f2_sylanb f3_sylanb p_sylan $.
$}

$(A syllogism inference.  (Contributed by NM, 18-May-1994.) $)

${
	$v ph ps ch th  $.
	f0_sylanbr $f wff ph $.
	f1_sylanbr $f wff ps $.
	f2_sylanbr $f wff ch $.
	f3_sylanbr $f wff th $.
	e0_sylanbr $e |- ( ps <-> ph ) $.
	e1_sylanbr $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylanbr $p |- ( ( ph /\ ch ) -> th ) $= e0_sylanbr f1_sylanbr f0_sylanbr p_biimpri e1_sylanbr f0_sylanbr f1_sylanbr f2_sylanbr f3_sylanbr p_sylan $.
$}

$(A syllogism inference.  (Contributed by NM, 21-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_sylan2 $f wff ph $.
	f1_sylan2 $f wff ps $.
	f2_sylan2 $f wff ch $.
	f3_sylan2 $f wff th $.
	e0_sylan2 $e |- ( ph -> ch ) $.
	e1_sylan2 $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylan2 $p |- ( ( ps /\ ph ) -> th ) $= e0_sylan2 f0_sylan2 f2_sylan2 f1_sylan2 p_adantl e1_sylan2 f1_sylan2 f0_sylan2 f2_sylan2 f3_sylan2 p_syldan $.
$}

$(A syllogism inference.  (Contributed by NM, 21-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_sylan2b $f wff ph $.
	f1_sylan2b $f wff ps $.
	f2_sylan2b $f wff ch $.
	f3_sylan2b $f wff th $.
	e0_sylan2b $e |- ( ph <-> ch ) $.
	e1_sylan2b $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylan2b $p |- ( ( ps /\ ph ) -> th ) $= e0_sylan2b f0_sylan2b f2_sylan2b p_biimpi e1_sylan2b f0_sylan2b f1_sylan2b f2_sylan2b f3_sylan2b p_sylan2 $.
$}

$(A syllogism inference.  (Contributed by NM, 21-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_sylan2br $f wff ph $.
	f1_sylan2br $f wff ps $.
	f2_sylan2br $f wff ch $.
	f3_sylan2br $f wff th $.
	e0_sylan2br $e |- ( ch <-> ph ) $.
	e1_sylan2br $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylan2br $p |- ( ( ps /\ ph ) -> th ) $= e0_sylan2br f2_sylan2br f0_sylan2br p_biimpri e1_sylan2br f0_sylan2br f1_sylan2br f2_sylan2br f3_sylan2br p_sylan2 $.
$}

$(A double syllogism inference.  (Contributed by NM, 31-Jan-1997.) $)

${
	$v ph ps ch th ta  $.
	f0_syl2an $f wff ph $.
	f1_syl2an $f wff ps $.
	f2_syl2an $f wff ch $.
	f3_syl2an $f wff th $.
	f4_syl2an $f wff ta $.
	e0_syl2an $e |- ( ph -> ps ) $.
	e1_syl2an $e |- ( ta -> ch ) $.
	e2_syl2an $e |- ( ( ps /\ ch ) -> th ) $.
	p_syl2an $p |- ( ( ph /\ ta ) -> th ) $= e1_syl2an e0_syl2an e2_syl2an f0_syl2an f1_syl2an f2_syl2an f3_syl2an p_sylan f4_syl2an f0_syl2an f2_syl2an f3_syl2an p_sylan2 $.
$}

$(A double syllogism inference.  (Contributed by NM, 17-Sep-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_syl2anr $f wff ph $.
	f1_syl2anr $f wff ps $.
	f2_syl2anr $f wff ch $.
	f3_syl2anr $f wff th $.
	f4_syl2anr $f wff ta $.
	e0_syl2anr $e |- ( ph -> ps ) $.
	e1_syl2anr $e |- ( ta -> ch ) $.
	e2_syl2anr $e |- ( ( ps /\ ch ) -> th ) $.
	p_syl2anr $p |- ( ( ta /\ ph ) -> th ) $= e0_syl2anr e1_syl2anr e2_syl2anr f0_syl2anr f1_syl2anr f2_syl2anr f3_syl2anr f4_syl2anr p_syl2an f0_syl2anr f4_syl2anr f3_syl2anr p_ancoms $.
$}

$(A double syllogism inference.  (Contributed by NM, 29-Jul-1999.) $)

${
	$v ph ps ch th ta  $.
	f0_syl2anb $f wff ph $.
	f1_syl2anb $f wff ps $.
	f2_syl2anb $f wff ch $.
	f3_syl2anb $f wff th $.
	f4_syl2anb $f wff ta $.
	e0_syl2anb $e |- ( ph <-> ps ) $.
	e1_syl2anb $e |- ( ta <-> ch ) $.
	e2_syl2anb $e |- ( ( ps /\ ch ) -> th ) $.
	p_syl2anb $p |- ( ( ph /\ ta ) -> th ) $= e1_syl2anb e0_syl2anb e2_syl2anb f0_syl2anb f1_syl2anb f2_syl2anb f3_syl2anb p_sylanb f4_syl2anb f0_syl2anb f2_syl2anb f3_syl2anb p_sylan2b $.
$}

$(A double syllogism inference.  (Contributed by NM, 29-Jul-1999.) $)

${
	$v ph ps ch th ta  $.
	f0_syl2anbr $f wff ph $.
	f1_syl2anbr $f wff ps $.
	f2_syl2anbr $f wff ch $.
	f3_syl2anbr $f wff th $.
	f4_syl2anbr $f wff ta $.
	e0_syl2anbr $e |- ( ps <-> ph ) $.
	e1_syl2anbr $e |- ( ch <-> ta ) $.
	e2_syl2anbr $e |- ( ( ps /\ ch ) -> th ) $.
	p_syl2anbr $p |- ( ( ph /\ ta ) -> th ) $= e1_syl2anbr e0_syl2anbr e2_syl2anbr f0_syl2anbr f1_syl2anbr f2_syl2anbr f3_syl2anbr p_sylanbr f4_syl2anbr f0_syl2anbr f2_syl2anbr f3_syl2anbr p_sylan2br $.
$}

$(A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)

${
	$v ph ps ch th ta  $.
	f0_syland $f wff ph $.
	f1_syland $f wff ps $.
	f2_syland $f wff ch $.
	f3_syland $f wff th $.
	f4_syland $f wff ta $.
	e0_syland $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syland $e |- ( ph -> ( ( ch /\ th ) -> ta ) ) $.
	p_syland $p |- ( ph -> ( ( ps /\ th ) -> ta ) ) $= e0_syland e1_syland f0_syland f2_syland f3_syland f4_syland p_exp3a f0_syland f1_syland f2_syland f3_syland f4_syland a_wi p_syld f0_syland f1_syland f3_syland f4_syland p_imp3a $.
$}

$(A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)

${
	$v ph ps ch th ta  $.
	f0_sylan2d $f wff ph $.
	f1_sylan2d $f wff ps $.
	f2_sylan2d $f wff ch $.
	f3_sylan2d $f wff th $.
	f4_sylan2d $f wff ta $.
	e0_sylan2d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_sylan2d $e |- ( ph -> ( ( th /\ ch ) -> ta ) ) $.
	p_sylan2d $p |- ( ph -> ( ( th /\ ps ) -> ta ) ) $= e0_sylan2d e1_sylan2d f0_sylan2d f3_sylan2d f2_sylan2d f4_sylan2d p_ancomsd f0_sylan2d f1_sylan2d f2_sylan2d f3_sylan2d f4_sylan2d p_syland f0_sylan2d f1_sylan2d f3_sylan2d f4_sylan2d p_ancomsd $.
$}

$(A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl2and $f wff ph $.
	f1_syl2and $f wff ps $.
	f2_syl2and $f wff ch $.
	f3_syl2and $f wff th $.
	f4_syl2and $f wff ta $.
	f5_syl2and $f wff et $.
	e0_syl2and $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl2and $e |- ( ph -> ( th -> ta ) ) $.
	e2_syl2and $e |- ( ph -> ( ( ch /\ ta ) -> et ) ) $.
	p_syl2and $p |- ( ph -> ( ( ps /\ th ) -> et ) ) $= e0_syl2and e1_syl2and e2_syl2and f0_syl2and f3_syl2and f4_syl2and f2_syl2and f5_syl2and p_sylan2d f0_syl2and f1_syl2and f2_syl2and f3_syl2and f5_syl2and p_syland $.
$}

$(Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)

${
	$v ph ps ch  $.
	f0_biimpa $f wff ph $.
	f1_biimpa $f wff ps $.
	f2_biimpa $f wff ch $.
	e0_biimpa $e |- ( ph -> ( ps <-> ch ) ) $.
	p_biimpa $p |- ( ( ph /\ ps ) -> ch ) $= e0_biimpa f0_biimpa f1_biimpa f2_biimpa p_biimpd f0_biimpa f1_biimpa f2_biimpa p_imp $.
$}

$(Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)

${
	$v ph ps ch  $.
	f0_biimpar $f wff ph $.
	f1_biimpar $f wff ps $.
	f2_biimpar $f wff ch $.
	e0_biimpar $e |- ( ph -> ( ps <-> ch ) ) $.
	p_biimpar $p |- ( ( ph /\ ch ) -> ps ) $= e0_biimpar f0_biimpar f1_biimpar f2_biimpar p_biimprd f0_biimpar f2_biimpar f1_biimpar p_imp $.
$}

$(Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)

${
	$v ph ps ch  $.
	f0_biimpac $f wff ph $.
	f1_biimpac $f wff ps $.
	f2_biimpac $f wff ch $.
	e0_biimpac $e |- ( ph -> ( ps <-> ch ) ) $.
	p_biimpac $p |- ( ( ps /\ ph ) -> ch ) $= e0_biimpac f0_biimpac f1_biimpac f2_biimpac p_biimpcd f1_biimpac f0_biimpac f2_biimpac p_imp $.
$}

$(Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)

${
	$v ph ps ch  $.
	f0_biimparc $f wff ph $.
	f1_biimparc $f wff ps $.
	f2_biimparc $f wff ch $.
	e0_biimparc $e |- ( ph -> ( ps <-> ch ) ) $.
	p_biimparc $p |- ( ( ch /\ ph ) -> ps ) $= e0_biimparc f0_biimparc f1_biimparc f2_biimparc p_biimprcd f2_biimparc f0_biimparc f1_biimparc p_imp $.
$}

$(Negated conjunction in terms of disjunction (De Morgan's law).  Theorem
     *4.51 of [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v ph ps  $.
	f0_ianor $f wff ph $.
	f1_ianor $f wff ps $.
	p_ianor $p |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) $= f0_ianor f1_ianor p_imnan f0_ianor f1_ianor p_pm4.62 f0_ianor f1_ianor a_wa a_wn f0_ianor f1_ianor a_wn a_wi f0_ianor a_wn f1_ianor a_wn a_wo p_bitr3i $.
$}

$(Conjunction in terms of disjunction (De Morgan's law).  Theorem *4.5 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 3-Nov-2012.) $)

${
	$v ph ps  $.
	f0_anor $f wff ph $.
	f1_anor $f wff ps $.
	p_anor $p |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) $= f0_anor f1_anor p_ianor f0_anor f1_anor a_wa a_wn f0_anor a_wn f1_anor a_wn a_wo p_bicomi f0_anor a_wn f1_anor a_wn a_wo f0_anor f1_anor a_wa p_con2bii $.
$}

$(Negated disjunction in terms of conjunction (De Morgan's law).  Compare
     Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps  $.
	f0_ioran $f wff ph $.
	f1_ioran $f wff ps $.
	p_ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $= f0_ioran f1_ioran p_pm4.65 f0_ioran f1_ioran p_pm4.64 f0_ioran a_wn f1_ioran a_wi f0_ioran a_wn f1_ioran a_wn a_wa f0_ioran f1_ioran a_wo p_xchnxbi $.
$}

$(Theorem *4.52 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Nov-2012.) $)

${
	$v ph ps  $.
	f0_pm4.52 $f wff ph $.
	f1_pm4.52 $f wff ps $.
	p_pm4.52 $p |- ( ( ph /\ -. ps ) <-> -. ( -. ph \/ ps ) ) $= f0_pm4.52 f1_pm4.52 p_annim f0_pm4.52 f1_pm4.52 p_imor f0_pm4.52 f1_pm4.52 a_wn a_wa f0_pm4.52 f1_pm4.52 a_wi f0_pm4.52 a_wn f1_pm4.52 a_wo p_xchbinx $.
$}

$(Theorem *4.53 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.53 $f wff ph $.
	f1_pm4.53 $f wff ps $.
	p_pm4.53 $p |- ( -. ( ph /\ -. ps ) <-> ( -. ph \/ ps ) ) $= f0_pm4.53 f1_pm4.53 p_pm4.52 f0_pm4.53 f1_pm4.53 a_wn a_wa f0_pm4.53 a_wn f1_pm4.53 a_wo p_con2bii f0_pm4.53 a_wn f1_pm4.53 a_wo f0_pm4.53 f1_pm4.53 a_wn a_wa a_wn p_bicomi $.
$}

$(Theorem *4.54 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Nov-2012.) $)

${
	$v ph ps  $.
	f0_pm4.54 $f wff ph $.
	f1_pm4.54 $f wff ps $.
	p_pm4.54 $p |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $= f0_pm4.54 a_wn f1_pm4.54 a_df-an f0_pm4.54 f1_pm4.54 p_pm4.66 f0_pm4.54 a_wn f1_pm4.54 a_wa f0_pm4.54 a_wn f1_pm4.54 a_wn a_wi f0_pm4.54 f1_pm4.54 a_wn a_wo p_xchbinx $.
$}

$(Theorem *4.55 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.55 $f wff ph $.
	f1_pm4.55 $f wff ps $.
	p_pm4.55 $p |- ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) ) $= f0_pm4.55 f1_pm4.55 p_pm4.54 f0_pm4.55 a_wn f1_pm4.55 a_wa f0_pm4.55 f1_pm4.55 a_wn a_wo p_con2bii f0_pm4.55 f1_pm4.55 a_wn a_wo f0_pm4.55 a_wn f1_pm4.55 a_wa a_wn p_bicomi $.
$}

$(Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.56 $f wff ph $.
	f1_pm4.56 $f wff ps $.
	p_pm4.56 $p |- ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) ) $= f0_pm4.56 f1_pm4.56 p_ioran f0_pm4.56 f1_pm4.56 a_wo a_wn f0_pm4.56 a_wn f1_pm4.56 a_wn a_wa p_bicomi $.
$}

$(Disjunction in terms of conjunction (De Morgan's law).  Compare Theorem
     *4.57 of [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps  $.
	f0_oran $f wff ph $.
	f1_oran $f wff ps $.
	p_oran $p |- ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) ) $= f0_oran f1_oran p_pm4.56 f0_oran a_wn f1_oran a_wn a_wa f0_oran f1_oran a_wo p_con2bii $.
$}

$(Theorem *4.57 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.57 $f wff ph $.
	f1_pm4.57 $f wff ps $.
	p_pm4.57 $p |- ( -. ( -. ph /\ -. ps ) <-> ( ph \/ ps ) ) $= f0_pm4.57 f1_pm4.57 p_oran f0_pm4.57 f1_pm4.57 a_wo f0_pm4.57 a_wn f1_pm4.57 a_wn a_wa a_wn p_bicomi $.
$}

$(Theorem *3.1 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm3.1 $f wff ph $.
	f1_pm3.1 $f wff ps $.
	p_pm3.1 $p |- ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) ) $= f0_pm3.1 f1_pm3.1 p_anor f0_pm3.1 f1_pm3.1 a_wa f0_pm3.1 a_wn f1_pm3.1 a_wn a_wo a_wn p_biimpi $.
$}

$(Theorem *3.11 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm3.11 $f wff ph $.
	f1_pm3.11 $f wff ps $.
	p_pm3.11 $p |- ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) ) $= f0_pm3.11 f1_pm3.11 p_anor f0_pm3.11 f1_pm3.11 a_wa f0_pm3.11 a_wn f1_pm3.11 a_wn a_wo a_wn p_biimpri $.
$}

$(Theorem *3.12 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm3.12 $f wff ph $.
	f1_pm3.12 $f wff ps $.
	p_pm3.12 $p |- ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) $= f0_pm3.12 f1_pm3.12 p_pm3.11 f0_pm3.12 a_wn f1_pm3.12 a_wn a_wo f0_pm3.12 f1_pm3.12 a_wa p_orri $.
$}

$(Theorem *3.13 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm3.13 $f wff ph $.
	f1_pm3.13 $f wff ps $.
	p_pm3.13 $p |- ( -. ( ph /\ ps ) -> ( -. ph \/ -. ps ) ) $= f0_pm3.13 f1_pm3.13 p_pm3.11 f0_pm3.13 a_wn f1_pm3.13 a_wn a_wo f0_pm3.13 f1_pm3.13 a_wa p_con1i $.
$}

$(Theorem *3.14 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm3.14 $f wff ph $.
	f1_pm3.14 $f wff ps $.
	p_pm3.14 $p |- ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) ) $= f0_pm3.14 f1_pm3.14 p_pm3.1 f0_pm3.14 f1_pm3.14 a_wa f0_pm3.14 a_wn f1_pm3.14 a_wn a_wo p_con2i $.
$}

$(Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Mar-1994.) $)

${
	$v ph ps  $.
	f0_iba $f wff ph $.
	f1_iba $f wff ps $.
	p_iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $= f0_iba f1_iba p_pm3.21 f1_iba f0_iba p_simpl f0_iba f1_iba f1_iba f0_iba a_wa p_impbid1 $.
$}

$(Introduction of antecedent as conjunct.  (Contributed by NM,
     5-Dec-1995.) $)

${
	$v ph ps  $.
	f0_ibar $f wff ph $.
	f1_ibar $f wff ps $.
	p_ibar $p |- ( ph -> ( ps <-> ( ph /\ ps ) ) ) $= f0_ibar f1_ibar p_pm3.2 f0_ibar f1_ibar p_simpr f0_ibar f1_ibar f0_ibar f1_ibar a_wa p_impbid1 $.
$}

$(A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_biantru $f wff ph $.
	f1_biantru $f wff ps $.
	e0_biantru $e |- ph $.
	p_biantru $p |- ( ps <-> ( ps /\ ph ) ) $= e0_biantru f0_biantru f1_biantru p_iba f0_biantru f1_biantru f1_biantru f0_biantru a_wa a_wb a_ax-mp $.
$}

$(A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       3-Aug-1994.) $)

${
	$v ph ps  $.
	f0_biantrur $f wff ph $.
	f1_biantrur $f wff ps $.
	e0_biantrur $e |- ph $.
	p_biantrur $p |- ( ps <-> ( ph /\ ps ) ) $= e0_biantrur f0_biantrur f1_biantrur p_ibar f0_biantrur f1_biantrur f0_biantrur f1_biantrur a_wa a_wb a_ax-mp $.
$}

$(A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       2-Aug-1994.)  (Proof shortened by Wolf Lammen, 23-Oct-2013.) $)

${
	$v ph ps ch  $.
	f0_biantrud $f wff ph $.
	f1_biantrud $f wff ps $.
	f2_biantrud $f wff ch $.
	e0_biantrud $e |- ( ph -> ps ) $.
	p_biantrud $p |- ( ph -> ( ch <-> ( ch /\ ps ) ) ) $= e0_biantrud f1_biantrud f2_biantrud p_iba f0_biantrud f1_biantrud f2_biantrud f2_biantrud f1_biantrud a_wa a_wb p_syl $.
$}

$(A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       1-May-1995.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch  $.
	f0_biantrurd $f wff ph $.
	f1_biantrurd $f wff ps $.
	f2_biantrurd $f wff ch $.
	e0_biantrurd $e |- ( ph -> ps ) $.
	p_biantrurd $p |- ( ph -> ( ch <-> ( ps /\ ch ) ) ) $= e0_biantrurd f1_biantrurd f2_biantrurd p_ibar f0_biantrurd f1_biantrurd f2_biantrurd f1_biantrurd f2_biantrurd a_wa a_wb p_syl $.
$}

$(Inference conjoining and disjoining the antecedents of two
       implications.  (Contributed by NM, 30-Sep-1999.) $)

${
	$v ph ps ch th ta  $.
	f0_jaao $f wff ph $.
	f1_jaao $f wff ps $.
	f2_jaao $f wff ch $.
	f3_jaao $f wff th $.
	f4_jaao $f wff ta $.
	e0_jaao $e |- ( ph -> ( ps -> ch ) ) $.
	e1_jaao $e |- ( th -> ( ta -> ch ) ) $.
	p_jaao $p |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) ) $= e0_jaao f0_jaao f1_jaao f2_jaao a_wi f3_jaao p_adantr e1_jaao f3_jaao f4_jaao f2_jaao a_wi f0_jaao p_adantl f0_jaao f3_jaao a_wa f1_jaao f2_jaao f4_jaao p_jaod $.
$}

$(Inference disjoining and conjoining the antecedents of two
       implications.  (Contributed by Stefan Allan, 1-Nov-2008.) $)

${
	$v ph ps ch th ta  $.
	f0_jaoa $f wff ph $.
	f1_jaoa $f wff ps $.
	f2_jaoa $f wff ch $.
	f3_jaoa $f wff th $.
	f4_jaoa $f wff ta $.
	e0_jaoa $e |- ( ph -> ( ps -> ch ) ) $.
	e1_jaoa $e |- ( th -> ( ta -> ch ) ) $.
	p_jaoa $p |- ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) ) $= e0_jaoa f0_jaoa f1_jaoa f2_jaoa f4_jaoa p_adantrd e1_jaoa f3_jaoa f4_jaoa f2_jaoa f1_jaoa p_adantld f0_jaoa f1_jaoa f4_jaoa a_wa f2_jaoa a_wi f3_jaoa p_jaoi $.
$}

$(Theorem *3.44 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)

${
	$v ph ps ch  $.
	f0_pm3.44 $f wff ph $.
	f1_pm3.44 $f wff ps $.
	f2_pm3.44 $f wff ch $.
	p_pm3.44 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) -> ( ( ps \/ ch ) -> ph ) ) $= f1_pm3.44 f0_pm3.44 a_wi p_id f2_pm3.44 f0_pm3.44 a_wi p_id f1_pm3.44 f0_pm3.44 a_wi f1_pm3.44 f0_pm3.44 f2_pm3.44 f0_pm3.44 a_wi f2_pm3.44 p_jaao $.
$}

$(Disjunction of antecedents.  Compare Theorem *3.44 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 5-Apr-1994.)  (Proof shortened by Wolf
     Lammen, 4-Apr-2013.) $)

${
	$v ph ps ch  $.
	f0_jao $f wff ph $.
	f1_jao $f wff ps $.
	f2_jao $f wff ch $.
	p_jao $p |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) ) $= f1_jao f0_jao f2_jao p_pm3.44 f0_jao f1_jao a_wi f2_jao f1_jao a_wi f0_jao f2_jao a_wo f1_jao a_wi p_ex $.
$}

$(Axiom *1.2 of [WhiteheadRussell] p. 96, which they call "Taut".
     (Contributed by NM, 3-Jan-2005.) $)

${
	$v ph  $.
	f0_pm1.2 $f wff ph $.
	p_pm1.2 $p |- ( ( ph \/ ph ) -> ph ) $= f0_pm1.2 p_id f0_pm1.2 p_id f0_pm1.2 f0_pm1.2 f0_pm1.2 p_jaoi $.
$}

$(Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 16-Apr-2011.)  (Proof shortened by Wolf Lammen, 10-Mar-2013.) $)

${
	$v ph  $.
	f0_oridm $f wff ph $.
	p_oridm $p |- ( ( ph \/ ph ) <-> ph ) $= f0_oridm p_pm1.2 f0_oridm p_pm2.07 f0_oridm f0_oridm a_wo f0_oridm p_impbii $.
$}

$(Theorem *4.25 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph  $.
	f0_pm4.25 $f wff ph $.
	p_pm4.25 $p |- ( ph <-> ( ph \/ ph ) ) $= f0_pm4.25 p_oridm f0_pm4.25 f0_pm4.25 a_wo f0_pm4.25 p_bicomi $.
$}

$(Disjoin antecedents and consequents of two premises.  (Contributed by
       NM, 6-Jun-1994.)  (Proof shortened by Wolf Lammen, 25-Jul-2012.) $)

${
	$v ph ps ch th  $.
	f0_orim12i $f wff ph $.
	f1_orim12i $f wff ps $.
	f2_orim12i $f wff ch $.
	f3_orim12i $f wff th $.
	e0_orim12i $e |- ( ph -> ps ) $.
	e1_orim12i $e |- ( ch -> th ) $.
	p_orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $= e0_orim12i f0_orim12i f1_orim12i f3_orim12i p_orcd e1_orim12i f2_orim12i f3_orim12i f1_orim12i p_olcd f0_orim12i f1_orim12i f3_orim12i a_wo f2_orim12i p_jaoi $.
$}

$(Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)

${
	$v ph ps ch  $.
	f0_orim1i $f wff ph $.
	f1_orim1i $f wff ps $.
	f2_orim1i $f wff ch $.
	e0_orim1i $e |- ( ph -> ps ) $.
	p_orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $= e0_orim1i f2_orim1i p_id f0_orim1i f1_orim1i f2_orim1i f2_orim1i p_orim12i $.
$}

$(Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)

${
	$v ph ps ch  $.
	f0_orim2i $f wff ph $.
	f1_orim2i $f wff ps $.
	f2_orim2i $f wff ch $.
	e0_orim2i $e |- ( ph -> ps ) $.
	p_orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $= f2_orim2i p_id e0_orim2i f2_orim2i f2_orim2i f0_orim2i f1_orim2i p_orim12i $.
$}

$(Inference adding a left disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 12-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_orbi2i $f wff ph $.
	f1_orbi2i $f wff ps $.
	f2_orbi2i $f wff ch $.
	e0_orbi2i $e |- ( ph <-> ps ) $.
	p_orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $= e0_orbi2i f0_orbi2i f1_orbi2i p_biimpi f0_orbi2i f1_orbi2i f2_orbi2i p_orim2i e0_orbi2i f0_orbi2i f1_orbi2i p_biimpri f1_orbi2i f0_orbi2i f2_orbi2i p_orim2i f2_orbi2i f0_orbi2i a_wo f2_orbi2i f1_orbi2i a_wo p_impbii $.
$}

$(Inference adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_orbi1i $f wff ph $.
	f1_orbi1i $f wff ps $.
	f2_orbi1i $f wff ch $.
	e0_orbi1i $e |- ( ph <-> ps ) $.
	p_orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $= f0_orbi1i f2_orbi1i p_orcom e0_orbi1i f0_orbi1i f1_orbi1i f2_orbi1i p_orbi2i f2_orbi1i f1_orbi1i p_orcom f0_orbi1i f2_orbi1i a_wo f2_orbi1i f0_orbi1i a_wo f2_orbi1i f1_orbi1i a_wo f1_orbi1i f2_orbi1i a_wo p_3bitri $.
$}

$(Infer the disjunction of two equivalences.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_orbi12i $f wff ph $.
	f1_orbi12i $f wff ps $.
	f2_orbi12i $f wff ch $.
	f3_orbi12i $f wff th $.
	e0_orbi12i $e |- ( ph <-> ps ) $.
	e1_orbi12i $e |- ( ch <-> th ) $.
	p_orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $= e1_orbi12i f2_orbi12i f3_orbi12i f0_orbi12i p_orbi2i e0_orbi12i f0_orbi12i f1_orbi12i f3_orbi12i p_orbi1i f0_orbi12i f2_orbi12i a_wo f0_orbi12i f3_orbi12i a_wo f1_orbi12i f3_orbi12i a_wo p_bitri $.
$}

$(Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm1.5 $f wff ph $.
	f1_pm1.5 $f wff ps $.
	f2_pm1.5 $f wff ch $.
	p_pm1.5 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ) $= f0_pm1.5 f2_pm1.5 p_orc f0_pm1.5 f0_pm1.5 f2_pm1.5 a_wo f1_pm1.5 p_olcd f2_pm1.5 f0_pm1.5 p_olc f2_pm1.5 f0_pm1.5 f2_pm1.5 a_wo f1_pm1.5 p_orim2i f0_pm1.5 f1_pm1.5 f0_pm1.5 f2_pm1.5 a_wo a_wo f1_pm1.5 f2_pm1.5 a_wo p_jaoi $.
$}

$(Swap two disjuncts.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 14-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_or12 $f wff ph $.
	f1_or12 $f wff ps $.
	f2_or12 $f wff ch $.
	p_or12 $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ) $= f0_or12 f1_or12 f2_or12 p_pm1.5 f1_or12 f0_or12 f2_or12 p_pm1.5 f0_or12 f1_or12 f2_or12 a_wo a_wo f1_or12 f0_or12 f2_or12 a_wo a_wo p_impbii $.
$}

$(Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)

${
	$v ph ps ch  $.
	f0_orass $f wff ph $.
	f1_orass $f wff ps $.
	f2_orass $f wff ch $.
	p_orass $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $= f0_orass f1_orass a_wo f2_orass p_orcom f2_orass f0_orass f1_orass p_or12 f2_orass f1_orass p_orcom f2_orass f1_orass a_wo f1_orass f2_orass a_wo f0_orass p_orbi2i f0_orass f1_orass a_wo f2_orass a_wo f2_orass f0_orass f1_orass a_wo a_wo f0_orass f2_orass f1_orass a_wo a_wo f0_orass f1_orass f2_orass a_wo a_wo p_3bitri $.
$}

$(Theorem *2.31 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.31 $f wff ph $.
	f1_pm2.31 $f wff ps $.
	f2_pm2.31 $f wff ch $.
	p_pm2.31 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ) $= f0_pm2.31 f1_pm2.31 f2_pm2.31 p_orass f0_pm2.31 f1_pm2.31 a_wo f2_pm2.31 a_wo f0_pm2.31 f1_pm2.31 f2_pm2.31 a_wo a_wo p_biimpri $.
$}

$(Theorem *2.32 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.32 $f wff ph $.
	f1_pm2.32 $f wff ps $.
	f2_pm2.32 $f wff ch $.
	p_pm2.32 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ) $= f0_pm2.32 f1_pm2.32 f2_pm2.32 p_orass f0_pm2.32 f1_pm2.32 a_wo f2_pm2.32 a_wo f0_pm2.32 f1_pm2.32 f2_pm2.32 a_wo a_wo p_biimpi $.
$}

$(A rearrangement of disjuncts.  (Contributed by NM, 18-Oct-1995.)  (Proof
     shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph ps ch  $.
	f0_or32 $f wff ph $.
	f1_or32 $f wff ps $.
	f2_or32 $f wff ch $.
	p_or32 $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ) $= f0_or32 f1_or32 f2_or32 p_orass f0_or32 f1_or32 f2_or32 p_or12 f1_or32 f0_or32 f2_or32 a_wo p_orcom f0_or32 f1_or32 a_wo f2_or32 a_wo f0_or32 f1_or32 f2_or32 a_wo a_wo f1_or32 f0_or32 f2_or32 a_wo a_wo f0_or32 f2_or32 a_wo f1_or32 a_wo p_3bitri $.
$}

$(Rearrangement of 4 disjuncts.  (Contributed by NM, 12-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_or4 $f wff ph $.
	f1_or4 $f wff ps $.
	f2_or4 $f wff ch $.
	f3_or4 $f wff th $.
	p_or4 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( ps \/ th ) ) ) $= f1_or4 f2_or4 f3_or4 p_or12 f1_or4 f2_or4 f3_or4 a_wo a_wo f2_or4 f1_or4 f3_or4 a_wo a_wo f0_or4 p_orbi2i f0_or4 f1_or4 f2_or4 f3_or4 a_wo p_orass f0_or4 f2_or4 f1_or4 f3_or4 a_wo p_orass f0_or4 f1_or4 f2_or4 f3_or4 a_wo a_wo a_wo f0_or4 f2_or4 f1_or4 f3_or4 a_wo a_wo a_wo f0_or4 f1_or4 a_wo f2_or4 f3_or4 a_wo a_wo f0_or4 f2_or4 a_wo f1_or4 f3_or4 a_wo a_wo p_3bitr4i $.
$}

$(Rearrangement of 4 disjuncts.  (Contributed by NM, 10-Jan-2005.) $)

${
	$v ph ps ch th  $.
	f0_or42 $f wff ph $.
	f1_or42 $f wff ps $.
	f2_or42 $f wff ch $.
	f3_or42 $f wff th $.
	p_or42 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( th \/ ps ) ) ) $= f0_or42 f1_or42 f2_or42 f3_or42 p_or4 f1_or42 f3_or42 p_orcom f1_or42 f3_or42 a_wo f3_or42 f1_or42 a_wo f0_or42 f2_or42 a_wo p_orbi2i f0_or42 f1_or42 a_wo f2_or42 f3_or42 a_wo a_wo f0_or42 f2_or42 a_wo f1_or42 f3_or42 a_wo a_wo f0_or42 f2_or42 a_wo f3_or42 f1_or42 a_wo a_wo p_bitri $.
$}

$(Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)

${
	$v ph ps ch  $.
	f0_orordi $f wff ph $.
	f1_orordi $f wff ps $.
	f2_orordi $f wff ch $.
	p_orordi $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $= f0_orordi p_oridm f0_orordi f0_orordi a_wo f0_orordi f1_orordi f2_orordi a_wo p_orbi1i f0_orordi f0_orordi f1_orordi f2_orordi p_or4 f0_orordi f1_orordi f2_orordi a_wo a_wo f0_orordi f0_orordi a_wo f1_orordi f2_orordi a_wo a_wo f0_orordi f1_orordi a_wo f0_orordi f2_orordi a_wo a_wo p_bitr3i $.
$}

$(Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)

${
	$v ph ps ch  $.
	f0_orordir $f wff ph $.
	f1_orordir $f wff ps $.
	f2_orordir $f wff ch $.
	p_orordir $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ( ps \/ ch ) ) ) $= f2_orordir p_oridm f2_orordir f2_orordir a_wo f2_orordir f0_orordir f1_orordir a_wo p_orbi2i f0_orordir f1_orordir f2_orordir f2_orordir p_or4 f0_orordir f1_orordir a_wo f2_orordir a_wo f0_orordir f1_orordir a_wo f2_orordir f2_orordir a_wo a_wo f0_orordir f2_orordir a_wo f1_orordir f2_orordir a_wo a_wo p_bitr3i $.
$}

$(Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  Equivalent to the natural deduction rule
       ` /\ ` I ( ` /\ ` introduction), see ~ natded .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-Oct-2012.) $)

${
	$v ph ps ch  $.
	f0_jca $f wff ph $.
	f1_jca $f wff ps $.
	f2_jca $f wff ch $.
	e0_jca $e |- ( ph -> ps ) $.
	e1_jca $e |- ( ph -> ch ) $.
	p_jca $p |- ( ph -> ( ps /\ ch ) ) $= e0_jca e1_jca f1_jca f2_jca p_pm3.2 f0_jca f1_jca f2_jca f1_jca f2_jca a_wa p_sylc $.
$}

$(Deduction conjoining the consequents of two implications.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)

${
	$v ph ps ch th  $.
	f0_jcad $f wff ph $.
	f1_jcad $f wff ps $.
	f2_jcad $f wff ch $.
	f3_jcad $f wff th $.
	e0_jcad $e |- ( ph -> ( ps -> ch ) ) $.
	e1_jcad $e |- ( ph -> ( ps -> th ) ) $.
	p_jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $= e0_jcad e1_jcad f2_jcad f3_jcad p_pm3.2 f0_jcad f1_jcad f2_jcad f3_jcad f2_jcad f3_jcad a_wa p_syl6c $.
$}

$(Join three consequents.  (Contributed by Jeff Hankins, 1-Aug-2009.) $)

${
	$v ph ps ch th  $.
	f0_jca31 $f wff ph $.
	f1_jca31 $f wff ps $.
	f2_jca31 $f wff ch $.
	f3_jca31 $f wff th $.
	e0_jca31 $e |- ( ph -> ps ) $.
	e1_jca31 $e |- ( ph -> ch ) $.
	e2_jca31 $e |- ( ph -> th ) $.
	p_jca31 $p |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $= e0_jca31 e1_jca31 f0_jca31 f1_jca31 f2_jca31 p_jca e2_jca31 f0_jca31 f1_jca31 f2_jca31 a_wa f3_jca31 p_jca $.
$}

$(Join three consequents.  (Contributed by FL, 1-Aug-2009.) $)

${
	$v ph ps ch th  $.
	f0_jca32 $f wff ph $.
	f1_jca32 $f wff ps $.
	f2_jca32 $f wff ch $.
	f3_jca32 $f wff th $.
	e0_jca32 $e |- ( ph -> ps ) $.
	e1_jca32 $e |- ( ph -> ch ) $.
	e2_jca32 $e |- ( ph -> th ) $.
	p_jca32 $p |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $= e0_jca32 e1_jca32 e2_jca32 f0_jca32 f2_jca32 f3_jca32 p_jca f0_jca32 f1_jca32 f2_jca32 f3_jca32 a_wa p_jca $.
$}

$(Deduction replacing implication with conjunction.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_jcai $f wff ph $.
	f1_jcai $f wff ps $.
	f2_jcai $f wff ch $.
	e0_jcai $e |- ( ph -> ps ) $.
	e1_jcai $e |- ( ph -> ( ps -> ch ) ) $.
	p_jcai $p |- ( ph -> ( ps /\ ch ) ) $= e0_jcai e0_jcai e1_jcai f0_jcai f1_jcai f2_jcai p_mpd f0_jcai f1_jcai f2_jcai p_jca $.
$}

$(Inference conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 31-Dec-1993.) $)

${
	$v ph ps ch  $.
	f0_jctil $f wff ph $.
	f1_jctil $f wff ps $.
	f2_jctil $f wff ch $.
	e0_jctil $e |- ( ph -> ps ) $.
	e1_jctil $e |- ch $.
	p_jctil $p |- ( ph -> ( ch /\ ps ) ) $= e1_jctil f2_jctil f0_jctil p_a1i e0_jctil f0_jctil f2_jctil f1_jctil p_jca $.
$}

$(Inference conjoining a theorem to right of consequent in an
       implication.  (Contributed by NM, 31-Dec-1993.) $)

${
	$v ph ps ch  $.
	f0_jctir $f wff ph $.
	f1_jctir $f wff ps $.
	f2_jctir $f wff ch $.
	e0_jctir $e |- ( ph -> ps ) $.
	e1_jctir $e |- ch $.
	p_jctir $p |- ( ph -> ( ps /\ ch ) ) $= e0_jctir e1_jctir f2_jctir f0_jctir p_a1i f0_jctir f1_jctir f2_jctir p_jca $.
$}

$(Inference conjoining a theorem to the left of a consequent.
       (Contributed by NM, 31-Dec-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)

${
	$v ph ps  $.
	f0_jctl $f wff ph $.
	f1_jctl $f wff ps $.
	e0_jctl $e |- ps $.
	p_jctl $p |- ( ph -> ( ps /\ ph ) ) $= f0_jctl p_id e0_jctl f0_jctl f0_jctl f1_jctl p_jctil $.
$}

$(Inference conjoining a theorem to the right of a consequent.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)

${
	$v ph ps  $.
	f0_jctr $f wff ph $.
	f1_jctr $f wff ps $.
	e0_jctr $e |- ps $.
	p_jctr $p |- ( ph -> ( ph /\ ps ) ) $= f0_jctr p_id e0_jctr f0_jctr f0_jctr f1_jctr p_jctir $.
$}

$(Deduction conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 21-Apr-2005.) $)

${
	$v ph ps ch th  $.
	f0_jctild $f wff ph $.
	f1_jctild $f wff ps $.
	f2_jctild $f wff ch $.
	f3_jctild $f wff th $.
	e0_jctild $e |- ( ph -> ( ps -> ch ) ) $.
	e1_jctild $e |- ( ph -> th ) $.
	p_jctild $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $= e1_jctild f0_jctild f3_jctild f1_jctild p_a1d e0_jctild f0_jctild f1_jctild f3_jctild f2_jctild p_jcad $.
$}

$(Deduction conjoining a theorem to right of consequent in an
       implication.  (Contributed by NM, 21-Apr-2005.) $)

${
	$v ph ps ch th  $.
	f0_jctird $f wff ph $.
	f1_jctird $f wff ps $.
	f2_jctird $f wff ch $.
	f3_jctird $f wff th $.
	e0_jctird $e |- ( ph -> ( ps -> ch ) ) $.
	e1_jctird $e |- ( ph -> th ) $.
	p_jctird $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $= e0_jctird e1_jctird f0_jctird f3_jctird f1_jctird p_a1d f0_jctird f1_jctird f2_jctird f3_jctird p_jcad $.
$}

$(Conjoin antecedent to left of consequent.  (Contributed by NM,
     15-Aug-1994.) $)

${
	$v ph ps  $.
	f0_ancl $f wff ph $.
	f1_ancl $f wff ps $.
	p_ancl $p |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ) $= f0_ancl f1_ancl p_pm3.2 f0_ancl f1_ancl f0_ancl f1_ancl a_wa p_a2i $.
$}

$(Conjoin antecedent to left of consequent.  Theorem *4.7 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 25-Jul-1999.)  (Proof
     shortened by Wolf Lammen, 24-Mar-2013.) $)

${
	$v ph ps  $.
	f0_anclb $f wff ph $.
	f1_anclb $f wff ps $.
	p_anclb $p |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) ) $= f0_anclb f1_anclb p_ibar f0_anclb f1_anclb f0_anclb f1_anclb a_wa p_pm5.74i $.
$}

$(Theorem *5.42 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm5.42 $f wff ph $.
	f1_pm5.42 $f wff ps $.
	f2_pm5.42 $f wff ch $.
	p_pm5.42 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $= f0_pm5.42 f2_pm5.42 p_ibar f0_pm5.42 f2_pm5.42 f0_pm5.42 f2_pm5.42 a_wa f1_pm5.42 p_imbi2d f0_pm5.42 f1_pm5.42 f2_pm5.42 a_wi f1_pm5.42 f0_pm5.42 f2_pm5.42 a_wa a_wi p_pm5.74i $.
$}

$(Conjoin antecedent to right of consequent.  (Contributed by NM,
     15-Aug-1994.) $)

${
	$v ph ps  $.
	f0_ancr $f wff ph $.
	f1_ancr $f wff ps $.
	p_ancr $p |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) ) $= f0_ancr f1_ancr p_pm3.21 f0_ancr f1_ancr f1_ancr f0_ancr a_wa p_a2i $.
$}

$(Conjoin antecedent to right of consequent.  (Contributed by NM,
     25-Jul-1999.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)

${
	$v ph ps  $.
	f0_ancrb $f wff ph $.
	f1_ancrb $f wff ps $.
	p_ancrb $p |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) ) $= f0_ancrb f1_ancrb p_iba f0_ancrb f1_ancrb f1_ancrb f0_ancrb a_wa p_pm5.74i $.
$}

$(Deduction conjoining antecedent to left of consequent.  (Contributed by
       NM, 12-Aug-1993.) $)

${
	$v ph ps  $.
	f0_ancli $f wff ph $.
	f1_ancli $f wff ps $.
	e0_ancli $e |- ( ph -> ps ) $.
	p_ancli $p |- ( ph -> ( ph /\ ps ) ) $= f0_ancli p_id e0_ancli f0_ancli f0_ancli f1_ancli p_jca $.
$}

$(Deduction conjoining antecedent to right of consequent.  (Contributed by
       NM, 15-Aug-1994.) $)

${
	$v ph ps  $.
	f0_ancri $f wff ph $.
	f1_ancri $f wff ps $.
	e0_ancri $e |- ( ph -> ps ) $.
	p_ancri $p |- ( ph -> ( ps /\ ph ) ) $= e0_ancri f0_ancri p_id f0_ancri f1_ancri f0_ancri p_jca $.
$}

$(Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_ancld $f wff ph $.
	f1_ancld $f wff ps $.
	f2_ancld $f wff ch $.
	e0_ancld $e |- ( ph -> ( ps -> ch ) ) $.
	p_ancld $p |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $= f0_ancld f1_ancld p_idd e0_ancld f0_ancld f1_ancld f1_ancld f2_ancld p_jcad $.
$}

$(Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_ancrd $f wff ph $.
	f1_ancrd $f wff ps $.
	f2_ancrd $f wff ch $.
	e0_ancrd $e |- ( ph -> ( ps -> ch ) ) $.
	p_ancrd $p |- ( ph -> ( ps -> ( ch /\ ps ) ) ) $= e0_ancrd f0_ancrd f1_ancrd p_idd f0_ancrd f1_ancrd f2_ancrd f1_ancrd p_jcad $.
$}

$(Conjoin antecedent to left of consequent in nested implication.
     (Contributed by NM, 10-Aug-1994.)  (Proof shortened by Wolf Lammen,
     14-Jul-2013.) $)

${
	$v ph ps ch  $.
	f0_anc2l $f wff ph $.
	f1_anc2l $f wff ps $.
	f2_anc2l $f wff ch $.
	p_anc2l $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $= f0_anc2l f1_anc2l f2_anc2l p_pm5.42 f0_anc2l f1_anc2l f2_anc2l a_wi a_wi f0_anc2l f1_anc2l f0_anc2l f2_anc2l a_wa a_wi a_wi p_biimpi $.
$}

$(Conjoin antecedent to right of consequent in nested implication.
     (Contributed by NM, 15-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_anc2r $f wff ph $.
	f1_anc2r $f wff ps $.
	f2_anc2r $f wff ch $.
	p_anc2r $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) ) $= f0_anc2r f2_anc2r p_pm3.21 f0_anc2r f2_anc2r f2_anc2r f0_anc2r a_wa f1_anc2r p_imim2d f0_anc2r f1_anc2r f2_anc2r a_wi f1_anc2r f2_anc2r f0_anc2r a_wa a_wi p_a2i $.
$}

$(Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 10-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 7-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_anc2li $f wff ph $.
	f1_anc2li $f wff ps $.
	f2_anc2li $f wff ch $.
	e0_anc2li $e |- ( ph -> ( ps -> ch ) ) $.
	p_anc2li $p |- ( ph -> ( ps -> ( ph /\ ch ) ) ) $= e0_anc2li f0_anc2li p_id f0_anc2li f1_anc2li f2_anc2li f0_anc2li p_jctild $.
$}

$(Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 7-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_anc2ri $f wff ph $.
	f1_anc2ri $f wff ps $.
	f2_anc2ri $f wff ch $.
	e0_anc2ri $e |- ( ph -> ( ps -> ch ) ) $.
	p_anc2ri $p |- ( ph -> ( ps -> ( ch /\ ph ) ) ) $= e0_anc2ri f0_anc2ri p_id f0_anc2ri f1_anc2ri f2_anc2ri f0_anc2ri p_jctird $.
$}

$(Theorem *3.41 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm3.41 $f wff ph $.
	f1_pm3.41 $f wff ps $.
	f2_pm3.41 $f wff ch $.
	p_pm3.41 $p |- ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $= f0_pm3.41 f1_pm3.41 p_simpl f0_pm3.41 f1_pm3.41 a_wa f0_pm3.41 f2_pm3.41 p_imim1i $.
$}

$(Theorem *3.42 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm3.42 $f wff ph $.
	f1_pm3.42 $f wff ps $.
	f2_pm3.42 $f wff ch $.
	p_pm3.42 $p |- ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $= f0_pm3.42 f1_pm3.42 p_simpr f0_pm3.42 f1_pm3.42 a_wa f1_pm3.42 f2_pm3.42 p_imim1i $.
$}

$(Conjunction implies implication.  Theorem *3.4 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 31-Jul-1995.) $)

${
	$v ph ps  $.
	f0_pm3.4 $f wff ph $.
	f1_pm3.4 $f wff ps $.
	p_pm3.4 $p |- ( ( ph /\ ps ) -> ( ph -> ps ) ) $= f0_pm3.4 f1_pm3.4 p_simpr f0_pm3.4 f1_pm3.4 a_wa f1_pm3.4 f0_pm3.4 p_a1d $.
$}

$(Conjunction with implication.  Compare Theorem *4.45 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 17-May-1998.) $)

${
	$v ph ps  $.
	f0_pm4.45im $f wff ph $.
	f1_pm4.45im $f wff ps $.
	p_pm4.45im $p |- ( ph <-> ( ph /\ ( ps -> ph ) ) ) $= f0_pm4.45im f1_pm4.45im a_ax-1 f0_pm4.45im f1_pm4.45im f0_pm4.45im a_wi p_ancli f0_pm4.45im f1_pm4.45im f0_pm4.45im a_wi p_simpl f0_pm4.45im f0_pm4.45im f1_pm4.45im f0_pm4.45im a_wi a_wa p_impbii $.
$}

$(Conjoin antecedents and consequents in a deduction.  (Contributed by NM,
       3-Apr-1994.)  (Proof shortened by Wolf Lammen, 18-Dec-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_anim12d $f wff ph $.
	f1_anim12d $f wff ps $.
	f2_anim12d $f wff ch $.
	f3_anim12d $f wff th $.
	f4_anim12d $f wff ta $.
	e0_anim12d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_anim12d $e |- ( ph -> ( th -> ta ) ) $.
	p_anim12d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) ) $= e0_anim12d e1_anim12d f0_anim12d f2_anim12d f4_anim12d a_wa p_idd f0_anim12d f1_anim12d f2_anim12d f3_anim12d f4_anim12d f2_anim12d f4_anim12d a_wa p_syl2and $.
$}

$(Add a conjunct to right of antecedent and consequent in a deduction.
       (Contributed by NM, 3-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_anim1d $f wff ph $.
	f1_anim1d $f wff ps $.
	f2_anim1d $f wff ch $.
	f3_anim1d $f wff th $.
	e0_anim1d $e |- ( ph -> ( ps -> ch ) ) $.
	p_anim1d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ th ) ) ) $= e0_anim1d f0_anim1d f3_anim1d p_idd f0_anim1d f1_anim1d f2_anim1d f3_anim1d f3_anim1d p_anim12d $.
$}

$(Add a conjunct to left of antecedent and consequent in a deduction.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_anim2d $f wff ph $.
	f1_anim2d $f wff ps $.
	f2_anim2d $f wff ch $.
	f3_anim2d $f wff th $.
	e0_anim2d $e |- ( ph -> ( ps -> ch ) ) $.
	p_anim2d $p |- ( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) ) $= f0_anim2d f3_anim2d p_idd e0_anim2d f0_anim2d f3_anim2d f3_anim2d f1_anim2d f2_anim2d p_anim12d $.
$}

$(Conjoin antecedents and consequents of two premises.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 14-Dec-2013.) $)

${
	$v ph ps ch th  $.
	f0_anim12i $f wff ph $.
	f1_anim12i $f wff ps $.
	f2_anim12i $f wff ch $.
	f3_anim12i $f wff th $.
	e0_anim12i $e |- ( ph -> ps ) $.
	e1_anim12i $e |- ( ch -> th ) $.
	p_anim12i $p |- ( ( ph /\ ch ) -> ( ps /\ th ) ) $= e0_anim12i e1_anim12i f1_anim12i f3_anim12i a_wa p_id f0_anim12i f1_anim12i f3_anim12i f1_anim12i f3_anim12i a_wa f2_anim12i p_syl2an $.
$}

$(Variant of ~ anim12i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)

${
	$v ph ps ch th  $.
	f0_anim12ci $f wff ph $.
	f1_anim12ci $f wff ps $.
	f2_anim12ci $f wff ch $.
	f3_anim12ci $f wff th $.
	e0_anim12ci $e |- ( ph -> ps ) $.
	e1_anim12ci $e |- ( ch -> th ) $.
	p_anim12ci $p |- ( ( ph /\ ch ) -> ( th /\ ps ) ) $= e1_anim12ci e0_anim12ci f2_anim12ci f3_anim12ci f0_anim12ci f1_anim12ci p_anim12i f2_anim12ci f0_anim12ci f3_anim12ci f1_anim12ci a_wa p_ancoms $.
$}

$(Introduce conjunct to both sides of an implication.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_anim1i $f wff ph $.
	f1_anim1i $f wff ps $.
	f2_anim1i $f wff ch $.
	e0_anim1i $e |- ( ph -> ps ) $.
	p_anim1i $p |- ( ( ph /\ ch ) -> ( ps /\ ch ) ) $= e0_anim1i f2_anim1i p_id f0_anim1i f1_anim1i f2_anim1i f2_anim1i p_anim12i $.
$}

$(Introduce conjunct to both sides of an implication.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_anim2i $f wff ph $.
	f1_anim2i $f wff ps $.
	f2_anim2i $f wff ch $.
	e0_anim2i $e |- ( ph -> ps ) $.
	p_anim2i $p |- ( ( ch /\ ph ) -> ( ch /\ ps ) ) $= f2_anim2i p_id e0_anim2i f2_anim2i f2_anim2i f0_anim2i f1_anim2i p_anim12i $.
$}

$(Conjoin antecedents and consequents in a deduction.  (Contributed by NM,
       11-Nov-2007.)  (Proof shortened by Wolf Lammen, 19-Jul-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_anim12ii $f wff ph $.
	f1_anim12ii $f wff ps $.
	f2_anim12ii $f wff ch $.
	f3_anim12ii $f wff th $.
	f4_anim12ii $f wff ta $.
	e0_anim12ii $e |- ( ph -> ( ps -> ch ) ) $.
	e1_anim12ii $e |- ( th -> ( ps -> ta ) ) $.
	p_anim12ii $p |- ( ( ph /\ th ) -> ( ps -> ( ch /\ ta ) ) ) $= e0_anim12ii f0_anim12ii f1_anim12ii f2_anim12ii a_wi f3_anim12ii p_adantr e1_anim12ii f3_anim12ii f1_anim12ii f4_anim12ii a_wi f0_anim12ii p_adantl f0_anim12ii f3_anim12ii a_wa f1_anim12ii f2_anim12ii f4_anim12ii p_jcad $.
$}

$(Conjoin antecedents and consequents of two premises.  This is the closed
     theorem form of ~ anim12d .  Theorem *3.47 of [WhiteheadRussell] p. 113.
     It was proved by Leibniz, and it evidently pleased him enough to call it
     _praeclarum theorema_ (splendid theorem).  (Contributed by NM,
     12-Aug-1993.)  (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)

${
	$v ph ps ch th  $.
	f0_prth $f wff ph $.
	f1_prth $f wff ps $.
	f2_prth $f wff ch $.
	f3_prth $f wff th $.
	p_prth $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) -> ( ( ph /\ ch ) -> ( ps /\ th ) ) ) $= f0_prth f1_prth a_wi f2_prth f3_prth a_wi p_simpl f0_prth f1_prth a_wi f2_prth f3_prth a_wi p_simpr f0_prth f1_prth a_wi f2_prth f3_prth a_wi a_wa f0_prth f1_prth f2_prth f3_prth p_anim12d $.
$}

$(Theorem *2.3 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.3 $f wff ph $.
	f1_pm2.3 $f wff ps $.
	f2_pm2.3 $f wff ch $.
	p_pm2.3 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ) $= f1_pm2.3 f2_pm2.3 p_pm1.4 f1_pm2.3 f2_pm2.3 a_wo f2_pm2.3 f1_pm2.3 a_wo f0_pm2.3 p_orim2i $.
$}

$(Theorem *2.41 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.41 $f wff ph $.
	f1_pm2.41 $f wff ps $.
	p_pm2.41 $p |- ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $= f1_pm2.41 f0_pm2.41 p_olc f0_pm2.41 f1_pm2.41 a_wo p_id f1_pm2.41 f0_pm2.41 f1_pm2.41 a_wo f0_pm2.41 f1_pm2.41 a_wo p_jaoi $.
$}

$(Theorem *2.42 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.42 $f wff ph $.
	f1_pm2.42 $f wff ps $.
	p_pm2.42 $p |- ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) ) $= f0_pm2.42 f1_pm2.42 p_pm2.21 f0_pm2.42 f1_pm2.42 a_wi p_id f0_pm2.42 a_wn f0_pm2.42 f1_pm2.42 a_wi f0_pm2.42 f1_pm2.42 a_wi p_jaoi $.
$}

$(Theorem *2.4 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.4 $f wff ph $.
	f1_pm2.4 $f wff ps $.
	p_pm2.4 $p |- ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $= f0_pm2.4 f1_pm2.4 p_orc f0_pm2.4 f1_pm2.4 a_wo p_id f0_pm2.4 f0_pm2.4 f1_pm2.4 a_wo f0_pm2.4 f1_pm2.4 a_wo p_jaoi $.
$}

$(Deduction rule for proof by contradiction.  (Contributed by NM,
       12-Jun-2014.) $)

${
	$v ph ps ch  $.
	f0_pm2.65da $f wff ph $.
	f1_pm2.65da $f wff ps $.
	f2_pm2.65da $f wff ch $.
	e0_pm2.65da $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_pm2.65da $e |- ( ( ph /\ ps ) -> -. ch ) $.
	p_pm2.65da $p |- ( ph -> -. ps ) $= e0_pm2.65da f0_pm2.65da f1_pm2.65da f2_pm2.65da p_ex e1_pm2.65da f0_pm2.65da f1_pm2.65da f2_pm2.65da a_wn p_ex f0_pm2.65da f1_pm2.65da f2_pm2.65da p_pm2.65d $.
$}

$(Theorem *4.44 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.44 $f wff ph $.
	f1_pm4.44 $f wff ps $.
	p_pm4.44 $p |- ( ph <-> ( ph \/ ( ph /\ ps ) ) ) $= f0_pm4.44 f0_pm4.44 f1_pm4.44 a_wa p_orc f0_pm4.44 p_id f0_pm4.44 f1_pm4.44 p_simpl f0_pm4.44 f0_pm4.44 f0_pm4.44 f1_pm4.44 a_wa p_jaoi f0_pm4.44 f0_pm4.44 f0_pm4.44 f1_pm4.44 a_wa a_wo p_impbii $.
$}

$(Theorem *4.14 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Oct-2012.) $)

${
	$v ph ps ch  $.
	f0_pm4.14 $f wff ph $.
	f1_pm4.14 $f wff ps $.
	f2_pm4.14 $f wff ch $.
	p_pm4.14 $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ) $= f1_pm4.14 f2_pm4.14 p_con34b f1_pm4.14 f2_pm4.14 a_wi f2_pm4.14 a_wn f1_pm4.14 a_wn a_wi f0_pm4.14 p_imbi2i f0_pm4.14 f1_pm4.14 f2_pm4.14 p_impexp f0_pm4.14 f2_pm4.14 a_wn f1_pm4.14 a_wn p_impexp f0_pm4.14 f1_pm4.14 f2_pm4.14 a_wi a_wi f0_pm4.14 f2_pm4.14 a_wn f1_pm4.14 a_wn a_wi a_wi f0_pm4.14 f1_pm4.14 a_wa f2_pm4.14 a_wi f0_pm4.14 f2_pm4.14 a_wn a_wa f1_pm4.14 a_wn a_wi p_3bitr4i $.
$}

$(Theorem *3.37 (Transp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Oct-2012.) $)

${
	$v ph ps ch  $.
	f0_pm3.37 $f wff ph $.
	f1_pm3.37 $f wff ps $.
	f2_pm3.37 $f wff ch $.
	p_pm3.37 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) ) $= f0_pm3.37 f1_pm3.37 f2_pm3.37 p_pm4.14 f0_pm3.37 f1_pm3.37 a_wa f2_pm3.37 a_wi f0_pm3.37 f2_pm3.37 a_wn a_wa f1_pm3.37 a_wn a_wi p_biimpi $.
$}

$(Theorem to move a conjunct in and out of a negation.  (Contributed by NM,
     9-Nov-2003.) $)

${
	$v ph ps ch  $.
	f0_nan $f wff ph $.
	f1_nan $f wff ps $.
	f2_nan $f wff ch $.
	p_nan $p |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) ) $= f0_nan f1_nan f2_nan a_wn p_impexp f1_nan f2_nan p_imnan f1_nan f2_nan a_wn a_wi f1_nan f2_nan a_wa a_wn f0_nan p_imbi2i f0_nan f1_nan a_wa f2_nan a_wn a_wi f0_nan f1_nan f2_nan a_wn a_wi a_wi f0_nan f1_nan f2_nan a_wa a_wn a_wi p_bitr2i $.
$}

$(Theorem *4.15 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 18-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_pm4.15 $f wff ph $.
	f1_pm4.15 $f wff ps $.
	f2_pm4.15 $f wff ch $.
	p_pm4.15 $p |- ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) ) $= f1_pm4.15 f2_pm4.15 a_wa f0_pm4.15 p_con2b f0_pm4.15 f1_pm4.15 f2_pm4.15 p_nan f1_pm4.15 f2_pm4.15 a_wa f0_pm4.15 a_wn a_wi f0_pm4.15 f1_pm4.15 f2_pm4.15 a_wa a_wn a_wi f0_pm4.15 f1_pm4.15 a_wa f2_pm4.15 a_wn a_wi p_bitr2i $.
$}

$(Theorem *4.78 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_pm4.78 $f wff ph $.
	f1_pm4.78 $f wff ps $.
	f2_pm4.78 $f wff ch $.
	p_pm4.78 $p |- ( ( ( ph -> ps ) \/ ( ph -> ch ) ) <-> ( ph -> ( ps \/ ch ) ) ) $= f0_pm4.78 a_wn f1_pm4.78 f2_pm4.78 p_orordi f0_pm4.78 f1_pm4.78 f2_pm4.78 a_wo p_imor f0_pm4.78 f1_pm4.78 p_imor f0_pm4.78 f2_pm4.78 p_imor f0_pm4.78 f1_pm4.78 a_wi f0_pm4.78 a_wn f1_pm4.78 a_wo f0_pm4.78 f2_pm4.78 a_wi f0_pm4.78 a_wn f2_pm4.78 a_wo p_orbi12i f0_pm4.78 a_wn f1_pm4.78 f2_pm4.78 a_wo a_wo f0_pm4.78 a_wn f1_pm4.78 a_wo f0_pm4.78 a_wn f2_pm4.78 a_wo a_wo f0_pm4.78 f1_pm4.78 f2_pm4.78 a_wo a_wi f0_pm4.78 f1_pm4.78 a_wi f0_pm4.78 f2_pm4.78 a_wi a_wo p_3bitr4ri $.
$}

$(Theorem *4.79 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 27-Jun-2013.) $)

${
	$v ph ps ch  $.
	f0_pm4.79 $f wff ph $.
	f1_pm4.79 $f wff ps $.
	f2_pm4.79 $f wff ch $.
	p_pm4.79 $p |- ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <-> ( ( ps /\ ch ) -> ph ) ) $= f1_pm4.79 f0_pm4.79 a_wi p_id f2_pm4.79 f0_pm4.79 a_wi p_id f1_pm4.79 f0_pm4.79 a_wi f1_pm4.79 f0_pm4.79 f2_pm4.79 f0_pm4.79 a_wi f2_pm4.79 p_jaoa f1_pm4.79 f0_pm4.79 p_simplim f1_pm4.79 f2_pm4.79 f0_pm4.79 p_pm3.3 f1_pm4.79 f0_pm4.79 a_wi a_wn f1_pm4.79 f1_pm4.79 f2_pm4.79 a_wa f0_pm4.79 a_wi f2_pm4.79 f0_pm4.79 a_wi p_syl5 f1_pm4.79 f2_pm4.79 a_wa f0_pm4.79 a_wi f1_pm4.79 f0_pm4.79 a_wi f2_pm4.79 f0_pm4.79 a_wi p_orrd f1_pm4.79 f0_pm4.79 a_wi f2_pm4.79 f0_pm4.79 a_wi a_wo f1_pm4.79 f2_pm4.79 a_wa f0_pm4.79 a_wi p_impbii $.
$}

$(Theorem *4.87 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Eric Schmidt, 26-Oct-2006.) $)

${
	$v ph ps ch  $.
	f0_pm4.87 $f wff ph $.
	f1_pm4.87 $f wff ps $.
	f2_pm4.87 $f wff ch $.
	p_pm4.87 $p |- ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\ ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\ ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) ) $= f0_pm4.87 f1_pm4.87 f2_pm4.87 p_impexp f0_pm4.87 f1_pm4.87 f2_pm4.87 p_bi2.04 f0_pm4.87 f1_pm4.87 a_wa f2_pm4.87 a_wi f0_pm4.87 f1_pm4.87 f2_pm4.87 a_wi a_wi a_wb f0_pm4.87 f1_pm4.87 f2_pm4.87 a_wi a_wi f1_pm4.87 f0_pm4.87 f2_pm4.87 a_wi a_wi a_wb p_pm3.2i f1_pm4.87 f0_pm4.87 f2_pm4.87 p_impexp f1_pm4.87 f0_pm4.87 a_wa f2_pm4.87 a_wi f1_pm4.87 f0_pm4.87 f2_pm4.87 a_wi a_wi p_bicomi f0_pm4.87 f1_pm4.87 a_wa f2_pm4.87 a_wi f0_pm4.87 f1_pm4.87 f2_pm4.87 a_wi a_wi a_wb f0_pm4.87 f1_pm4.87 f2_pm4.87 a_wi a_wi f1_pm4.87 f0_pm4.87 f2_pm4.87 a_wi a_wi a_wb a_wa f1_pm4.87 f0_pm4.87 f2_pm4.87 a_wi a_wi f1_pm4.87 f0_pm4.87 a_wa f2_pm4.87 a_wi a_wb p_pm3.2i $.
$}

$(Theorem *3.33 (Syll) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm3.33 $f wff ph $.
	f1_pm3.33 $f wff ps $.
	f2_pm3.33 $f wff ch $.
	p_pm3.33 $p |- ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) ) $= f0_pm3.33 f1_pm3.33 f2_pm3.33 p_imim1 f0_pm3.33 f1_pm3.33 a_wi f1_pm3.33 f2_pm3.33 a_wi f0_pm3.33 f2_pm3.33 a_wi p_imp $.
$}

$(Theorem *3.34 (Syll) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm3.34 $f wff ph $.
	f1_pm3.34 $f wff ps $.
	f2_pm3.34 $f wff ch $.
	p_pm3.34 $p |- ( ( ( ps -> ch ) /\ ( ph -> ps ) ) -> ( ph -> ch ) ) $= f1_pm3.34 f2_pm3.34 f0_pm3.34 p_imim2 f1_pm3.34 f2_pm3.34 a_wi f0_pm3.34 f1_pm3.34 a_wi f0_pm3.34 f2_pm3.34 a_wi p_imp $.
$}

$(Conjunctive detachment.  Theorem *3.35 of [WhiteheadRussell] p. 112.
     (Contributed by NM, 14-Dec-2002.) $)

${
	$v ph ps  $.
	f0_pm3.35 $f wff ph $.
	f1_pm3.35 $f wff ps $.
	p_pm3.35 $p |- ( ( ph /\ ( ph -> ps ) ) -> ps ) $= f0_pm3.35 f1_pm3.35 p_pm2.27 f0_pm3.35 f0_pm3.35 f1_pm3.35 a_wi f1_pm3.35 p_imp $.
$}

$(Theorem *5.31 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm5.31 $f wff ph $.
	f1_pm5.31 $f wff ps $.
	f2_pm5.31 $f wff ch $.
	p_pm5.31 $p |- ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ps /\ ch ) ) ) $= f2_pm5.31 f1_pm5.31 p_pm3.21 f2_pm5.31 f1_pm5.31 f1_pm5.31 f2_pm5.31 a_wa f0_pm5.31 p_imim2d f2_pm5.31 f0_pm5.31 f1_pm5.31 a_wi f0_pm5.31 f1_pm5.31 f2_pm5.31 a_wa a_wi p_imp $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp4a $f wff ph $.
	f1_imp4a $f wff ps $.
	f2_imp4a $f wff ch $.
	f3_imp4a $f wff th $.
	f4_imp4a $f wff ta $.
	e0_imp4a $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp4a $p |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $= e0_imp4a f2_imp4a f3_imp4a f4_imp4a p_impexp f0_imp4a f1_imp4a f2_imp4a f3_imp4a f4_imp4a a_wi a_wi f2_imp4a f3_imp4a a_wa f4_imp4a a_wi p_syl6ibr $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp4b $f wff ph $.
	f1_imp4b $f wff ps $.
	f2_imp4b $f wff ch $.
	f3_imp4b $f wff th $.
	f4_imp4b $f wff ta $.
	e0_imp4b $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $= e0_imp4b f0_imp4b f1_imp4b f2_imp4b f3_imp4b f4_imp4b p_imp4a f0_imp4b f1_imp4b f2_imp4b f3_imp4b a_wa f4_imp4b a_wi p_imp $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp4c $f wff ph $.
	f1_imp4c $f wff ps $.
	f2_imp4c $f wff ch $.
	f3_imp4c $f wff th $.
	f4_imp4c $f wff ta $.
	e0_imp4c $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $= e0_imp4c f0_imp4c f1_imp4c f2_imp4c f3_imp4c f4_imp4c a_wi p_imp3a f0_imp4c f1_imp4c f2_imp4c a_wa f3_imp4c f4_imp4c p_imp3a $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp4d $f wff ph $.
	f1_imp4d $f wff ps $.
	f2_imp4d $f wff ch $.
	f3_imp4d $f wff th $.
	f4_imp4d $f wff ta $.
	e0_imp4d $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $= e0_imp4d f0_imp4d f1_imp4d f2_imp4d f3_imp4d f4_imp4d p_imp4a f0_imp4d f1_imp4d f2_imp4d f3_imp4d a_wa f4_imp4d p_imp3a $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp41 $f wff ph $.
	f1_imp41 $f wff ps $.
	f2_imp41 $f wff ch $.
	f3_imp41 $f wff th $.
	f4_imp41 $f wff ta $.
	e0_imp41 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp41 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $= e0_imp41 f0_imp41 f1_imp41 f2_imp41 f3_imp41 f4_imp41 a_wi a_wi p_imp f0_imp41 f1_imp41 a_wa f2_imp41 f3_imp41 f4_imp41 p_imp31 $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp42 $f wff ph $.
	f1_imp42 $f wff ps $.
	f2_imp42 $f wff ch $.
	f3_imp42 $f wff th $.
	f4_imp42 $f wff ta $.
	e0_imp42 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp42 $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $= e0_imp42 f0_imp42 f1_imp42 f2_imp42 f3_imp42 f4_imp42 a_wi p_imp32 f0_imp42 f1_imp42 f2_imp42 a_wa a_wa f3_imp42 f4_imp42 p_imp $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp43 $f wff ph $.
	f1_imp43 $f wff ps $.
	f2_imp43 $f wff ch $.
	f3_imp43 $f wff th $.
	f4_imp43 $f wff ta $.
	e0_imp43 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $= e0_imp43 f0_imp43 f1_imp43 f2_imp43 f3_imp43 f4_imp43 p_imp4b f0_imp43 f1_imp43 a_wa f2_imp43 f3_imp43 a_wa f4_imp43 p_imp $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp44 $f wff ph $.
	f1_imp44 $f wff ps $.
	f2_imp44 $f wff ch $.
	f3_imp44 $f wff th $.
	f4_imp44 $f wff ta $.
	e0_imp44 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp44 $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $= e0_imp44 f0_imp44 f1_imp44 f2_imp44 f3_imp44 f4_imp44 p_imp4c f0_imp44 f1_imp44 f2_imp44 a_wa f3_imp44 a_wa f4_imp44 p_imp $.
$}

$(An importation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_imp45 $f wff ph $.
	f1_imp45 $f wff ps $.
	f2_imp45 $f wff ch $.
	f3_imp45 $f wff th $.
	f4_imp45 $f wff ta $.
	e0_imp45 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_imp45 $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $= e0_imp45 f0_imp45 f1_imp45 f2_imp45 f3_imp45 f4_imp45 p_imp4d f0_imp45 f1_imp45 f2_imp45 f3_imp45 a_wa a_wa f4_imp45 p_imp $.
$}

$(An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_imp5a $f wff ph $.
	f1_imp5a $f wff ps $.
	f2_imp5a $f wff ch $.
	f3_imp5a $f wff th $.
	f4_imp5a $f wff ta $.
	f5_imp5a $f wff et $.
	e0_imp5a $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_imp5a $p |- ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) ) $= e0_imp5a f3_imp5a f4_imp5a f5_imp5a p_pm3.31 f0_imp5a f1_imp5a f2_imp5a f3_imp5a f4_imp5a f5_imp5a a_wi a_wi f3_imp5a f4_imp5a a_wa f5_imp5a a_wi p_syl8 $.
$}

$(An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_imp5d $f wff ph $.
	f1_imp5d $f wff ps $.
	f2_imp5d $f wff ch $.
	f3_imp5d $f wff th $.
	f4_imp5d $f wff ta $.
	f5_imp5d $f wff et $.
	e0_imp5d $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_imp5d $p |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ) $= e0_imp5d f0_imp5d f1_imp5d f2_imp5d f3_imp5d f4_imp5d f5_imp5d a_wi a_wi p_imp31 f0_imp5d f1_imp5d a_wa f2_imp5d a_wa f3_imp5d f4_imp5d f5_imp5d p_imp3a $.
$}

$(An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_imp5g $f wff ph $.
	f1_imp5g $f wff ps $.
	f2_imp5g $f wff ch $.
	f3_imp5g $f wff th $.
	f4_imp5g $f wff ta $.
	f5_imp5g $f wff et $.
	e0_imp5g $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_imp5g $p |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ) $= e0_imp5g f0_imp5g f1_imp5g f2_imp5g f3_imp5g f4_imp5g f5_imp5g a_wi a_wi a_wi p_imp f0_imp5g f1_imp5g a_wa f2_imp5g f3_imp5g f4_imp5g f5_imp5g p_imp4c $.
$}

$(An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_imp55 $f wff ph $.
	f1_imp55 $f wff ps $.
	f2_imp55 $f wff ch $.
	f3_imp55 $f wff th $.
	f4_imp55 $f wff ta $.
	f5_imp55 $f wff et $.
	e0_imp55 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_imp55 $p |- ( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et ) $= e0_imp55 f0_imp55 f1_imp55 f2_imp55 f3_imp55 f4_imp55 f5_imp55 a_wi p_imp4a f0_imp55 f1_imp55 f2_imp55 f3_imp55 a_wa f4_imp55 f5_imp55 p_imp42 $.
$}

$(An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_imp511 $f wff ph $.
	f1_imp511 $f wff ps $.
	f2_imp511 $f wff ch $.
	f3_imp511 $f wff th $.
	f4_imp511 $f wff ta $.
	f5_imp511 $f wff et $.
	e0_imp511 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_imp511 $p |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ) $= e0_imp511 f0_imp511 f1_imp511 f2_imp511 f3_imp511 f4_imp511 f5_imp511 a_wi p_imp4a f0_imp511 f1_imp511 f2_imp511 f3_imp511 a_wa f4_imp511 f5_imp511 p_imp44 $.
$}

$(Exportation followed by a deduction version of importation.
       (Contributed by NM, 6-Sep-2008.) $)

${
	$v ph ps ch th  $.
	f0_expimpd $f wff ph $.
	f1_expimpd $f wff ps $.
	f2_expimpd $f wff ch $.
	f3_expimpd $f wff th $.
	e0_expimpd $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	p_expimpd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= e0_expimpd f0_expimpd f1_expimpd f2_expimpd f3_expimpd a_wi p_ex f0_expimpd f1_expimpd f2_expimpd f3_expimpd p_imp3a $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_exp31 $f wff ph $.
	f1_exp31 $f wff ps $.
	f2_exp31 $f wff ch $.
	f3_exp31 $f wff th $.
	e0_exp31 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_exp31 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= e0_exp31 f0_exp31 f1_exp31 a_wa f2_exp31 f3_exp31 p_ex f0_exp31 f1_exp31 f2_exp31 f3_exp31 a_wi p_ex $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_exp32 $f wff ph $.
	f1_exp32 $f wff ps $.
	f2_exp32 $f wff ch $.
	f3_exp32 $f wff th $.
	e0_exp32 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_exp32 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= e0_exp32 f0_exp32 f1_exp32 f2_exp32 a_wa f3_exp32 p_ex f0_exp32 f1_exp32 f2_exp32 f3_exp32 p_exp3a $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_exp4a $f wff ph $.
	f1_exp4a $f wff ps $.
	f2_exp4a $f wff ch $.
	f3_exp4a $f wff th $.
	f4_exp4a $f wff ta $.
	e0_exp4a $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
	p_exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp4a f2_exp4a f3_exp4a f4_exp4a p_impexp f0_exp4a f1_exp4a f2_exp4a f3_exp4a a_wa f4_exp4a a_wi f2_exp4a f3_exp4a f4_exp4a a_wi a_wi p_syl6ib $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 23-Nov-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_exp4b $f wff ph $.
	f1_exp4b $f wff ps $.
	f2_exp4b $f wff ch $.
	f3_exp4b $f wff th $.
	f4_exp4b $f wff ta $.
	e0_exp4b $e |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $.
	p_exp4b $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp4b f0_exp4b f1_exp4b f2_exp4b f3_exp4b a_wa f4_exp4b a_wi p_ex f0_exp4b f1_exp4b f2_exp4b f3_exp4b f4_exp4b p_exp4a $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_exp4c $f wff ph $.
	f1_exp4c $f wff ps $.
	f2_exp4c $f wff ch $.
	f3_exp4c $f wff th $.
	f4_exp4c $f wff ta $.
	e0_exp4c $e |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $.
	p_exp4c $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp4c f0_exp4c f1_exp4c f2_exp4c a_wa f3_exp4c f4_exp4c p_exp3a f0_exp4c f1_exp4c f2_exp4c f3_exp4c f4_exp4c a_wi p_exp3a $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_exp4d $f wff ph $.
	f1_exp4d $f wff ps $.
	f2_exp4d $f wff ch $.
	f3_exp4d $f wff th $.
	f4_exp4d $f wff ta $.
	e0_exp4d $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
	p_exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp4d f0_exp4d f1_exp4d f2_exp4d f3_exp4d a_wa f4_exp4d p_exp3a f0_exp4d f1_exp4d f2_exp4d f3_exp4d f4_exp4d p_exp4a $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_exp41 $f wff ph $.
	f1_exp41 $f wff ps $.
	f2_exp41 $f wff ch $.
	f3_exp41 $f wff th $.
	f4_exp41 $f wff ta $.
	e0_exp41 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
	p_exp41 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp41 f0_exp41 f1_exp41 a_wa f2_exp41 a_wa f3_exp41 f4_exp41 p_ex f0_exp41 f1_exp41 f2_exp41 f3_exp41 f4_exp41 a_wi p_exp31 $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_exp42 $f wff ph $.
	f1_exp42 $f wff ps $.
	f2_exp42 $f wff ch $.
	f3_exp42 $f wff th $.
	f4_exp42 $f wff ta $.
	e0_exp42 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
	p_exp42 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp42 f0_exp42 f1_exp42 f2_exp42 a_wa f3_exp42 f4_exp42 p_exp31 f0_exp42 f1_exp42 f2_exp42 f3_exp42 f4_exp42 a_wi p_exp3a $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_exp43 $f wff ph $.
	f1_exp43 $f wff ps $.
	f2_exp43 $f wff ch $.
	f3_exp43 $f wff th $.
	f4_exp43 $f wff ta $.
	e0_exp43 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
	p_exp43 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp43 f0_exp43 f1_exp43 a_wa f2_exp43 f3_exp43 a_wa f4_exp43 p_ex f0_exp43 f1_exp43 f2_exp43 f3_exp43 f4_exp43 p_exp4b $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_exp44 $f wff ph $.
	f1_exp44 $f wff ps $.
	f2_exp44 $f wff ch $.
	f3_exp44 $f wff th $.
	f4_exp44 $f wff ta $.
	e0_exp44 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $.
	p_exp44 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp44 f0_exp44 f1_exp44 f2_exp44 a_wa f3_exp44 f4_exp44 p_exp32 f0_exp44 f1_exp44 f2_exp44 f3_exp44 f4_exp44 a_wi p_exp3a $.
$}

$(An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_exp45 $f wff ph $.
	f1_exp45 $f wff ps $.
	f2_exp45 $f wff ch $.
	f3_exp45 $f wff th $.
	f4_exp45 $f wff ta $.
	e0_exp45 $e |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $.
	p_exp45 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= e0_exp45 f0_exp45 f1_exp45 f2_exp45 f3_exp45 a_wa f4_exp45 p_exp32 f0_exp45 f1_exp45 f2_exp45 f3_exp45 f4_exp45 p_exp4a $.
$}

$(Export a wff from a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)

${
	$v ph ps ch th  $.
	f0_expr $f wff ph $.
	f1_expr $f wff ps $.
	f2_expr $f wff ch $.
	f3_expr $f wff th $.
	e0_expr $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_expr $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $= e0_expr f0_expr f1_expr f2_expr f3_expr p_exp32 f0_expr f1_expr f2_expr f3_expr a_wi p_imp $.
$}

$(An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_exp5c $f wff ph $.
	f1_exp5c $f wff ps $.
	f2_exp5c $f wff ch $.
	f3_exp5c $f wff th $.
	f4_exp5c $f wff ta $.
	f5_exp5c $f wff et $.
	e0_exp5c $e |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) ) $.
	p_exp5c $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= e0_exp5c f0_exp5c f1_exp5c f2_exp5c a_wa f3_exp5c f4_exp5c f5_exp5c p_exp4a f0_exp5c f1_exp5c f2_exp5c f3_exp5c f4_exp5c f5_exp5c a_wi a_wi p_exp3a $.
$}

$(An exportation inference.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_exp53 $f wff ph $.
	f1_exp53 $f wff ps $.
	f2_exp53 $f wff ch $.
	f3_exp53 $f wff th $.
	f4_exp53 $f wff ta $.
	f5_exp53 $f wff et $.
	e0_exp53 $e |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et ) $.
	p_exp53 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= e0_exp53 f0_exp53 f1_exp53 a_wa f2_exp53 f3_exp53 a_wa a_wa f4_exp53 f5_exp53 p_ex f0_exp53 f1_exp53 f2_exp53 f3_exp53 f4_exp53 f5_exp53 a_wi p_exp43 $.
$}

$(Export a wff from a left conjunct.  (Contributed by Jeff Hankins,
       28-Aug-2009.) $)

${
	$v ph ps ch th  $.
	f0_expl $f wff ph $.
	f1_expl $f wff ps $.
	f2_expl $f wff ch $.
	f3_expl $f wff th $.
	e0_expl $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_expl $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= e0_expl f0_expl f1_expl f2_expl f3_expl p_exp31 f0_expl f1_expl f2_expl f3_expl p_imp3a $.
$}

$(Import a wff into a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)

${
	$v ph ps ch th  $.
	f0_impr $f wff ph $.
	f1_impr $f wff ps $.
	f2_impr $f wff ch $.
	f3_impr $f wff th $.
	e0_impr $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	p_impr $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $= e0_impr f0_impr f1_impr f2_impr f3_impr a_wi p_ex f0_impr f1_impr f2_impr f3_impr p_imp32 $.
$}

$(Export a wff from a left conjunct.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)

${
	$v ph ps ch th  $.
	f0_impl $f wff ph $.
	f1_impl $f wff ps $.
	f2_impl $f wff ch $.
	f3_impl $f wff th $.
	e0_impl $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_impl $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $= e0_impl f0_impl f1_impl f2_impl f3_impl p_exp3a f0_impl f1_impl f2_impl f3_impl p_imp31 $.
$}

$(Importation with conjunction in consequent.  (Contributed by NM,
       9-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_impac $f wff ph $.
	f1_impac $f wff ps $.
	f2_impac $f wff ch $.
	e0_impac $e |- ( ph -> ( ps -> ch ) ) $.
	p_impac $p |- ( ( ph /\ ps ) -> ( ch /\ ps ) ) $= e0_impac f0_impac f1_impac f2_impac p_ancrd f0_impac f1_impac f2_impac f1_impac a_wa p_imp $.
$}

$(Inference form of ~ exbir .  This proof is ~ exbiriVD automatically
       translated and minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
       (Proof shortened by Wolf Lammen, 27-Jan-2013.) $)

${
	$v ph ps ch th  $.
	f0_exbiri $f wff ph $.
	f1_exbiri $f wff ps $.
	f2_exbiri $f wff ch $.
	f3_exbiri $f wff th $.
	e0_exbiri $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	p_exbiri $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $= e0_exbiri f0_exbiri f1_exbiri a_wa f2_exbiri f3_exbiri p_biimpar f0_exbiri f1_exbiri f3_exbiri f2_exbiri p_exp31 $.
$}

$(Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)

${
	$v ph ps ch th  $.
	f0_simprbda $f wff ph $.
	f1_simprbda $f wff ps $.
	f2_simprbda $f wff ch $.
	f3_simprbda $f wff th $.
	e0_simprbda $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	p_simprbda $p |- ( ( ph /\ ps ) -> ch ) $= e0_simprbda f0_simprbda f1_simprbda f2_simprbda f3_simprbda a_wa p_biimpa f0_simprbda f1_simprbda a_wa f2_simprbda f3_simprbda p_simpld $.
$}

$(Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)

${
	$v ph ps ch th  $.
	f0_simplbda $f wff ph $.
	f1_simplbda $f wff ps $.
	f2_simplbda $f wff ch $.
	f3_simplbda $f wff th $.
	e0_simplbda $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	p_simplbda $p |- ( ( ph /\ ps ) -> th ) $= e0_simplbda f0_simplbda f1_simplbda f2_simplbda f3_simplbda a_wa p_biimpa f0_simplbda f1_simplbda a_wa f2_simplbda f3_simplbda p_simprd $.
$}

$(Deduction eliminating a conjunct.  Automatically derived from
       ~ simplbi2VD .  (Contributed by Alan Sare, 31-Dec-2011.) $)

${
	$v ph ps ch  $.
	f0_simplbi2 $f wff ph $.
	f1_simplbi2 $f wff ps $.
	f2_simplbi2 $f wff ch $.
	e0_simplbi2 $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_simplbi2 $p |- ( ps -> ( ch -> ph ) ) $= e0_simplbi2 f0_simplbi2 f1_simplbi2 f2_simplbi2 a_wa p_biimpri f1_simplbi2 f2_simplbi2 f0_simplbi2 p_ex $.
$}

$(A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_dfbi2 $f wff ph $.
	f1_dfbi2 $f wff ps $.
	p_dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $= f0_dfbi2 f1_dfbi2 p_dfbi1 f0_dfbi2 f1_dfbi2 a_wi f1_dfbi2 f0_dfbi2 a_wi a_df-an f0_dfbi2 f1_dfbi2 a_wb f0_dfbi2 f1_dfbi2 a_wi f1_dfbi2 f0_dfbi2 a_wi a_wn a_wi a_wn f0_dfbi2 f1_dfbi2 a_wi f1_dfbi2 f0_dfbi2 a_wi a_wa p_bitr4i $.
$}

$(Definition ~ df-bi rewritten in an abbreviated form to help intuitive
     understanding of that definition.  Note that it is a conjunction of two
     implications; one which asserts properties that follow from the
     biconditional and one which asserts properties that imply the
     biconditional.  (Contributed by NM, 15-Aug-2008.) $)

${
	$v ph ps  $.
	f0_dfbi $f wff ph $.
	f1_dfbi $f wff ps $.
	p_dfbi $p |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $= f0_dfbi f1_dfbi p_dfbi2 f0_dfbi f1_dfbi a_wb f0_dfbi f1_dfbi a_wi f1_dfbi f0_dfbi a_wi a_wa p_biimpi f0_dfbi f1_dfbi p_dfbi2 f0_dfbi f1_dfbi a_wb f0_dfbi f1_dfbi a_wi f1_dfbi f0_dfbi a_wi a_wa p_biimpri f0_dfbi f1_dfbi a_wb f0_dfbi f1_dfbi a_wi f1_dfbi f0_dfbi a_wi a_wa a_wi f0_dfbi f1_dfbi a_wi f1_dfbi f0_dfbi a_wi a_wa f0_dfbi f1_dfbi a_wb a_wi p_pm3.2i $.
$}

$(Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 2-Dec-2012.) $)

${
	$v ph ps  $.
	f0_pm4.71 $f wff ph $.
	f1_pm4.71 $f wff ps $.
	p_pm4.71 $p |- ( ( ph -> ps ) <-> ( ph <-> ( ph /\ ps ) ) ) $= f0_pm4.71 f1_pm4.71 p_simpl f0_pm4.71 f1_pm4.71 a_wa f0_pm4.71 a_wi f0_pm4.71 f0_pm4.71 f1_pm4.71 a_wa a_wi p_biantru f0_pm4.71 f1_pm4.71 p_anclb f0_pm4.71 f0_pm4.71 f1_pm4.71 a_wa p_dfbi2 f0_pm4.71 f0_pm4.71 f1_pm4.71 a_wa a_wi f0_pm4.71 f0_pm4.71 f1_pm4.71 a_wa a_wi f0_pm4.71 f1_pm4.71 a_wa f0_pm4.71 a_wi a_wa f0_pm4.71 f1_pm4.71 a_wi f0_pm4.71 f0_pm4.71 f1_pm4.71 a_wa a_wb p_3bitr4i $.
$}

$(Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120 (with conjunct reversed).  (Contributed by NM,
     25-Jul-1999.) $)

${
	$v ph ps  $.
	f0_pm4.71r $f wff ph $.
	f1_pm4.71r $f wff ps $.
	p_pm4.71r $p |- ( ( ph -> ps ) <-> ( ph <-> ( ps /\ ph ) ) ) $= f0_pm4.71r f1_pm4.71r p_pm4.71 f0_pm4.71r f1_pm4.71r p_ancom f0_pm4.71r f1_pm4.71r a_wa f1_pm4.71r f0_pm4.71r a_wa f0_pm4.71r p_bibi2i f0_pm4.71r f1_pm4.71r a_wi f0_pm4.71r f0_pm4.71r f1_pm4.71r a_wa a_wb f0_pm4.71r f1_pm4.71r f0_pm4.71r a_wa a_wb p_bitri $.
$}

$(Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by NM, 4-Jan-2004.) $)

${
	$v ph ps  $.
	f0_pm4.71i $f wff ph $.
	f1_pm4.71i $f wff ps $.
	e0_pm4.71i $e |- ( ph -> ps ) $.
	p_pm4.71i $p |- ( ph <-> ( ph /\ ps ) ) $= e0_pm4.71i f0_pm4.71i f1_pm4.71i p_pm4.71 f0_pm4.71i f1_pm4.71i a_wi f0_pm4.71i f0_pm4.71i f1_pm4.71i a_wa a_wb p_mpbi $.
$}

$(Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell] p. 120
       (with conjunct reversed).  (Contributed by NM, 1-Dec-2003.) $)

${
	$v ph ps  $.
	f0_pm4.71ri $f wff ph $.
	f1_pm4.71ri $f wff ps $.
	e0_pm4.71ri $e |- ( ph -> ps ) $.
	p_pm4.71ri $p |- ( ph <-> ( ps /\ ph ) ) $= e0_pm4.71ri f0_pm4.71ri f1_pm4.71ri p_pm4.71r f0_pm4.71ri f1_pm4.71ri a_wi f0_pm4.71ri f1_pm4.71ri f0_pm4.71ri a_wa a_wb p_mpbi $.
$}

$(Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by Mario Carneiro, 25-Dec-2016.) $)

${
	$v ph ps ch  $.
	f0_pm4.71d $f wff ph $.
	f1_pm4.71d $f wff ps $.
	f2_pm4.71d $f wff ch $.
	e0_pm4.71d $e |- ( ph -> ( ps -> ch ) ) $.
	p_pm4.71d $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $= e0_pm4.71d f1_pm4.71d f2_pm4.71d p_pm4.71 f0_pm4.71d f1_pm4.71d f2_pm4.71d a_wi f1_pm4.71d f1_pm4.71d f2_pm4.71d a_wa a_wb p_sylib $.
$}

$(Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by NM, 10-Feb-2005.) $)

${
	$v ph ps ch  $.
	f0_pm4.71rd $f wff ph $.
	f1_pm4.71rd $f wff ps $.
	f2_pm4.71rd $f wff ch $.
	e0_pm4.71rd $e |- ( ph -> ( ps -> ch ) ) $.
	p_pm4.71rd $p |- ( ph -> ( ps <-> ( ch /\ ps ) ) ) $= e0_pm4.71rd f1_pm4.71rd f2_pm4.71rd p_pm4.71r f0_pm4.71rd f1_pm4.71rd f2_pm4.71rd a_wi f1_pm4.71rd f2_pm4.71rd f1_pm4.71rd a_wa a_wb p_sylib $.
$}

$(Distribution of implication over biconditional.  Theorem *5.32 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 1-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_pm5.32 $f wff ph $.
	f1_pm5.32 $f wff ps $.
	f2_pm5.32 $f wff ch $.
	p_pm5.32 $p |- ( ( ph -> ( ps <-> ch ) ) <-> ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $= f1_pm5.32 f2_pm5.32 p_notbi f1_pm5.32 f2_pm5.32 a_wb f1_pm5.32 a_wn f2_pm5.32 a_wn a_wb f0_pm5.32 p_imbi2i f0_pm5.32 f1_pm5.32 a_wn f2_pm5.32 a_wn p_pm5.74 f0_pm5.32 f1_pm5.32 a_wn a_wi f0_pm5.32 f2_pm5.32 a_wn a_wi p_notbi f0_pm5.32 f1_pm5.32 f2_pm5.32 a_wb a_wi f0_pm5.32 f1_pm5.32 a_wn f2_pm5.32 a_wn a_wb a_wi f0_pm5.32 f1_pm5.32 a_wn a_wi f0_pm5.32 f2_pm5.32 a_wn a_wi a_wb f0_pm5.32 f1_pm5.32 a_wn a_wi a_wn f0_pm5.32 f2_pm5.32 a_wn a_wi a_wn a_wb p_3bitri f0_pm5.32 f1_pm5.32 a_df-an f0_pm5.32 f2_pm5.32 a_df-an f0_pm5.32 f1_pm5.32 a_wa f0_pm5.32 f1_pm5.32 a_wn a_wi a_wn f0_pm5.32 f2_pm5.32 a_wa f0_pm5.32 f2_pm5.32 a_wn a_wi a_wn p_bibi12i f0_pm5.32 f1_pm5.32 f2_pm5.32 a_wb a_wi f0_pm5.32 f1_pm5.32 a_wn a_wi a_wn f0_pm5.32 f2_pm5.32 a_wn a_wi a_wn a_wb f0_pm5.32 f1_pm5.32 a_wa f0_pm5.32 f2_pm5.32 a_wa a_wb p_bitr4i $.
$}

$(Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 1-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_pm5.32i $f wff ph $.
	f1_pm5.32i $f wff ps $.
	f2_pm5.32i $f wff ch $.
	e0_pm5.32i $e |- ( ph -> ( ps <-> ch ) ) $.
	p_pm5.32i $p |- ( ( ph /\ ps ) <-> ( ph /\ ch ) ) $= e0_pm5.32i f0_pm5.32i f1_pm5.32i f2_pm5.32i p_pm5.32 f0_pm5.32i f1_pm5.32i f2_pm5.32i a_wb a_wi f0_pm5.32i f1_pm5.32i a_wa f0_pm5.32i f2_pm5.32i a_wa a_wb p_mpbi $.
$}

$(Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 12-Mar-1995.) $)

${
	$v ph ps ch  $.
	f0_pm5.32ri $f wff ph $.
	f1_pm5.32ri $f wff ps $.
	f2_pm5.32ri $f wff ch $.
	e0_pm5.32ri $e |- ( ph -> ( ps <-> ch ) ) $.
	p_pm5.32ri $p |- ( ( ps /\ ph ) <-> ( ch /\ ph ) ) $= e0_pm5.32ri f0_pm5.32ri f1_pm5.32ri f2_pm5.32ri p_pm5.32i f1_pm5.32ri f0_pm5.32ri p_ancom f2_pm5.32ri f0_pm5.32ri p_ancom f0_pm5.32ri f1_pm5.32ri a_wa f0_pm5.32ri f2_pm5.32ri a_wa f1_pm5.32ri f0_pm5.32ri a_wa f2_pm5.32ri f0_pm5.32ri a_wa p_3bitr4i $.
$}

$(Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 29-Oct-1996.) $)

${
	$v ph ps ch th  $.
	f0_pm5.32d $f wff ph $.
	f1_pm5.32d $f wff ps $.
	f2_pm5.32d $f wff ch $.
	f3_pm5.32d $f wff th $.
	e0_pm5.32d $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
	p_pm5.32d $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $= e0_pm5.32d f1_pm5.32d f2_pm5.32d f3_pm5.32d p_pm5.32 f0_pm5.32d f1_pm5.32d f2_pm5.32d f3_pm5.32d a_wb a_wi f1_pm5.32d f2_pm5.32d a_wa f1_pm5.32d f3_pm5.32d a_wa a_wb p_sylib $.
$}

$(Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 25-Dec-2004.) $)

${
	$v ph ps ch th  $.
	f0_pm5.32rd $f wff ph $.
	f1_pm5.32rd $f wff ps $.
	f2_pm5.32rd $f wff ch $.
	f3_pm5.32rd $f wff th $.
	e0_pm5.32rd $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
	p_pm5.32rd $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $= e0_pm5.32rd f0_pm5.32rd f1_pm5.32rd f2_pm5.32rd f3_pm5.32rd p_pm5.32d f2_pm5.32rd f1_pm5.32rd p_ancom f3_pm5.32rd f1_pm5.32rd p_ancom f0_pm5.32rd f1_pm5.32rd f2_pm5.32rd a_wa f1_pm5.32rd f3_pm5.32rd a_wa f2_pm5.32rd f1_pm5.32rd a_wa f3_pm5.32rd f1_pm5.32rd a_wa p_3bitr4g $.
$}

$(Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 9-Dec-2006.) $)

${
	$v ph ps ch th  $.
	f0_pm5.32da $f wff ph $.
	f1_pm5.32da $f wff ps $.
	f2_pm5.32da $f wff ch $.
	f3_pm5.32da $f wff th $.
	e0_pm5.32da $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	p_pm5.32da $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $= e0_pm5.32da f0_pm5.32da f1_pm5.32da f2_pm5.32da f3_pm5.32da a_wb p_ex f0_pm5.32da f1_pm5.32da f2_pm5.32da f3_pm5.32da p_pm5.32d $.
$}

$(Add a conjunction to an equivalence.  (Contributed by Jeff Madsen,
       20-Jun-2011.) $)

${
	$v ph ps ch  $.
	f0_biadan2 $f wff ph $.
	f1_biadan2 $f wff ps $.
	f2_biadan2 $f wff ch $.
	e0_biadan2 $e |- ( ph -> ps ) $.
	e1_biadan2 $e |- ( ps -> ( ph <-> ch ) ) $.
	p_biadan2 $p |- ( ph <-> ( ps /\ ch ) ) $= e0_biadan2 f0_biadan2 f1_biadan2 p_pm4.71ri e1_biadan2 f1_biadan2 f0_biadan2 f2_biadan2 p_pm5.32i f0_biadan2 f1_biadan2 f0_biadan2 a_wa f1_biadan2 f2_biadan2 a_wa p_bitri $.
$}

$(Theorem *4.24 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph  $.
	f0_pm4.24 $f wff ph $.
	p_pm4.24 $p |- ( ph <-> ( ph /\ ph ) ) $= f0_pm4.24 p_id f0_pm4.24 f0_pm4.24 p_pm4.71i $.
$}

$(Idempotent law for conjunction.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 14-Mar-2014.) $)

${
	$v ph  $.
	f0_anidm $f wff ph $.
	p_anidm $p |- ( ( ph /\ ph ) <-> ph ) $= f0_anidm p_pm4.24 f0_anidm f0_anidm f0_anidm a_wa p_bicomi $.
$}

$(Inference from idempotent law for conjunction.  (Contributed by NM,
       15-Jun-1994.) $)

${
	$v ph ps  $.
	f0_anidms $f wff ph $.
	f1_anidms $f wff ps $.
	e0_anidms $e |- ( ( ph /\ ph ) -> ps ) $.
	p_anidms $p |- ( ph -> ps ) $= e0_anidms f0_anidms f0_anidms f1_anidms p_ex f0_anidms f1_anidms p_pm2.43i $.
$}

$(Conjunction idempotence with antecedent.  (Contributed by Roy F. Longton,
     8-Aug-2005.) $)

${
	$v ph ps  $.
	f0_anidmdbi $f wff ph $.
	f1_anidmdbi $f wff ps $.
	p_anidmdbi $p |- ( ( ph -> ( ps /\ ps ) ) <-> ( ph -> ps ) ) $= f1_anidmdbi p_anidm f1_anidmdbi f1_anidmdbi a_wa f1_anidmdbi f0_anidmdbi p_imbi2i $.
$}

$(Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)

${
	$v ph ps ch th  $.
	f0_anasss $f wff ph $.
	f1_anasss $f wff ps $.
	f2_anasss $f wff ch $.
	f3_anasss $f wff th $.
	e0_anasss $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_anasss $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $= e0_anasss f0_anasss f1_anasss f2_anasss f3_anasss p_exp31 f0_anasss f1_anasss f2_anasss f3_anasss p_imp32 $.
$}

$(Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)

${
	$v ph ps ch th  $.
	f0_anassrs $f wff ph $.
	f1_anassrs $f wff ps $.
	f2_anassrs $f wff ch $.
	f3_anassrs $f wff th $.
	e0_anassrs $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_anassrs $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $= e0_anassrs f0_anassrs f1_anassrs f2_anassrs f3_anassrs p_exp32 f0_anassrs f1_anassrs f2_anassrs f3_anassrs p_imp31 $.
$}

$(Associative law for conjunction.  Theorem *4.32 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_anass $f wff ph $.
	f1_anass $f wff ps $.
	f2_anass $f wff ch $.
	p_anass $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $= f0_anass f1_anass f2_anass a_wa a_wa p_id f0_anass f1_anass f2_anass f0_anass f1_anass f2_anass a_wa a_wa p_anassrs f0_anass f1_anass a_wa f2_anass a_wa p_id f0_anass f1_anass f2_anass f0_anass f1_anass a_wa f2_anass a_wa p_anasss f0_anass f1_anass a_wa f2_anass a_wa f0_anass f1_anass f2_anass a_wa a_wa p_impbii $.
$}

$(A syllogism inference.  (Contributed by NM, 10-Mar-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_sylanl1 $f wff ph $.
	f1_sylanl1 $f wff ps $.
	f2_sylanl1 $f wff ch $.
	f3_sylanl1 $f wff th $.
	f4_sylanl1 $f wff ta $.
	e0_sylanl1 $e |- ( ph -> ps ) $.
	e1_sylanl1 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
	p_sylanl1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $= e0_sylanl1 f0_sylanl1 f1_sylanl1 f2_sylanl1 p_anim1i e1_sylanl1 f0_sylanl1 f2_sylanl1 a_wa f1_sylanl1 f2_sylanl1 a_wa f3_sylanl1 f4_sylanl1 p_sylan $.
$}

$(A syllogism inference.  (Contributed by NM, 1-Jan-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_sylanl2 $f wff ph $.
	f1_sylanl2 $f wff ps $.
	f2_sylanl2 $f wff ch $.
	f3_sylanl2 $f wff th $.
	f4_sylanl2 $f wff ta $.
	e0_sylanl2 $e |- ( ph -> ch ) $.
	e1_sylanl2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
	p_sylanl2 $p |- ( ( ( ps /\ ph ) /\ th ) -> ta ) $= e0_sylanl2 f0_sylanl2 f2_sylanl2 f1_sylanl2 p_anim2i e1_sylanl2 f1_sylanl2 f0_sylanl2 a_wa f1_sylanl2 f2_sylanl2 a_wa f3_sylanl2 f4_sylanl2 p_sylan $.
$}

$(A syllogism inference.  (Contributed by NM, 9-Apr-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_sylanr1 $f wff ph $.
	f1_sylanr1 $f wff ps $.
	f2_sylanr1 $f wff ch $.
	f3_sylanr1 $f wff th $.
	f4_sylanr1 $f wff ta $.
	e0_sylanr1 $e |- ( ph -> ch ) $.
	e1_sylanr1 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
	p_sylanr1 $p |- ( ( ps /\ ( ph /\ th ) ) -> ta ) $= e0_sylanr1 f0_sylanr1 f2_sylanr1 f3_sylanr1 p_anim1i e1_sylanr1 f0_sylanr1 f3_sylanr1 a_wa f1_sylanr1 f2_sylanr1 f3_sylanr1 a_wa f4_sylanr1 p_sylan2 $.
$}

$(A syllogism inference.  (Contributed by NM, 9-Apr-2005.) $)

${
	$v ph ps ch th ta  $.
	f0_sylanr2 $f wff ph $.
	f1_sylanr2 $f wff ps $.
	f2_sylanr2 $f wff ch $.
	f3_sylanr2 $f wff th $.
	f4_sylanr2 $f wff ta $.
	e0_sylanr2 $e |- ( ph -> th ) $.
	e1_sylanr2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
	p_sylanr2 $p |- ( ( ps /\ ( ch /\ ph ) ) -> ta ) $= e0_sylanr2 f0_sylanr2 f3_sylanr2 f2_sylanr2 p_anim2i e1_sylanr2 f2_sylanr2 f0_sylanr2 a_wa f1_sylanr2 f2_sylanr2 f3_sylanr2 a_wa f4_sylanr2 p_sylan2 $.
$}

$(A syllogism inference.  (Contributed by NM, 2-May-1996.) $)

${
	$v ph ps ch th ta  $.
	f0_sylani $f wff ph $.
	f1_sylani $f wff ps $.
	f2_sylani $f wff ch $.
	f3_sylani $f wff th $.
	f4_sylani $f wff ta $.
	e0_sylani $e |- ( ph -> ch ) $.
	e1_sylani $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
	p_sylani $p |- ( ps -> ( ( ph /\ th ) -> ta ) ) $= e0_sylani f0_sylani f2_sylani a_wi f1_sylani p_a1i e1_sylani f1_sylani f0_sylani f2_sylani f3_sylani f4_sylani p_syland $.
$}

$(A syllogism inference.  (Contributed by NM, 1-Aug-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_sylan2i $f wff ph $.
	f1_sylan2i $f wff ps $.
	f2_sylan2i $f wff ch $.
	f3_sylan2i $f wff th $.
	f4_sylan2i $f wff ta $.
	e0_sylan2i $e |- ( ph -> th ) $.
	e1_sylan2i $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
	p_sylan2i $p |- ( ps -> ( ( ch /\ ph ) -> ta ) ) $= e0_sylan2i f0_sylan2i f3_sylan2i a_wi f1_sylan2i p_a1i e1_sylan2i f1_sylan2i f0_sylan2i f3_sylan2i f2_sylan2i f4_sylan2i p_sylan2d $.
$}

$(A syllogism inference.  (Contributed by NM, 3-Aug-1999.) $)

${
	$v ph ps ch th ta et  $.
	f0_syl2ani $f wff ph $.
	f1_syl2ani $f wff ps $.
	f2_syl2ani $f wff ch $.
	f3_syl2ani $f wff th $.
	f4_syl2ani $f wff ta $.
	f5_syl2ani $f wff et $.
	e0_syl2ani $e |- ( ph -> ch ) $.
	e1_syl2ani $e |- ( et -> th ) $.
	e2_syl2ani $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
	p_syl2ani $p |- ( ps -> ( ( ph /\ et ) -> ta ) ) $= e0_syl2ani e1_syl2ani e2_syl2ani f5_syl2ani f1_syl2ani f2_syl2ani f3_syl2ani f4_syl2ani p_sylan2i f0_syl2ani f1_syl2ani f2_syl2ani f5_syl2ani f4_syl2ani p_sylani $.
$}

$(Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_sylan9 $f wff ph $.
	f1_sylan9 $f wff ps $.
	f2_sylan9 $f wff ch $.
	f3_sylan9 $f wff th $.
	f4_sylan9 $f wff ta $.
	e0_sylan9 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_sylan9 $e |- ( th -> ( ch -> ta ) ) $.
	p_sylan9 $p |- ( ( ph /\ th ) -> ( ps -> ta ) ) $= e0_sylan9 e1_sylan9 f0_sylan9 f1_sylan9 f2_sylan9 f3_sylan9 f4_sylan9 p_syl9 f0_sylan9 f3_sylan9 f1_sylan9 f4_sylan9 a_wi p_imp $.
$}

$(Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th ta  $.
	f0_sylan9r $f wff ph $.
	f1_sylan9r $f wff ps $.
	f2_sylan9r $f wff ch $.
	f3_sylan9r $f wff th $.
	f4_sylan9r $f wff ta $.
	e0_sylan9r $e |- ( ph -> ( ps -> ch ) ) $.
	e1_sylan9r $e |- ( th -> ( ch -> ta ) ) $.
	p_sylan9r $p |- ( ( th /\ ph ) -> ( ps -> ta ) ) $= e0_sylan9r e1_sylan9r f0_sylan9r f1_sylan9r f2_sylan9r f3_sylan9r f4_sylan9r p_syl9r f3_sylan9r f0_sylan9r f1_sylan9r f4_sylan9r a_wi p_imp $.
$}

$(A modus tollens deduction.  (Contributed by Jeff Hankins,
       19-Aug-2009.) $)

${
	$v ph ps ch  $.
	f0_mtand $f wff ph $.
	f1_mtand $f wff ps $.
	f2_mtand $f wff ch $.
	e0_mtand $e |- ( ph -> -. ch ) $.
	e1_mtand $e |- ( ( ph /\ ps ) -> ch ) $.
	p_mtand $p |- ( ph -> -. ps ) $= e0_mtand e1_mtand f0_mtand f1_mtand f2_mtand p_ex f0_mtand f1_mtand f2_mtand p_mtod $.
$}

$(A modus tollens deduction involving disjunction.  (Contributed by Jeff
       Hankins, 15-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_mtord $f wff ph $.
	f1_mtord $f wff ps $.
	f2_mtord $f wff ch $.
	f3_mtord $f wff th $.
	e0_mtord $e |- ( ph -> -. ch ) $.
	e1_mtord $e |- ( ph -> -. th ) $.
	e2_mtord $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
	p_mtord $p |- ( ph -> -. ps ) $= e1_mtord e0_mtord e2_mtord f2_mtord f3_mtord a_df-or f0_mtord f1_mtord f2_mtord f3_mtord a_wo f2_mtord a_wn f3_mtord a_wi p_syl6ib f0_mtord f1_mtord f2_mtord a_wn f3_mtord p_mpid f0_mtord f1_mtord f3_mtord p_mtod $.
$}

$(Syllogism inference combined with contraction.  (Contributed by NM,
       16-Mar-2012.) $)

${
	$v ph ps ch th  $.
	f0_syl2anc $f wff ph $.
	f1_syl2anc $f wff ps $.
	f2_syl2anc $f wff ch $.
	f3_syl2anc $f wff th $.
	e0_syl2anc $e |- ( ph -> ps ) $.
	e1_syl2anc $e |- ( ph -> ch ) $.
	e2_syl2anc $e |- ( ( ps /\ ch ) -> th ) $.
	p_syl2anc $p |- ( ph -> th ) $= e0_syl2anc e1_syl2anc e2_syl2anc f1_syl2anc f2_syl2anc f3_syl2anc p_ex f0_syl2anc f1_syl2anc f2_syl2anc f3_syl2anc p_sylc $.
$}

$(Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)

${
	$v ph ps ch th  $.
	f0_sylancl $f wff ph $.
	f1_sylancl $f wff ps $.
	f2_sylancl $f wff ch $.
	f3_sylancl $f wff th $.
	e0_sylancl $e |- ( ph -> ps ) $.
	e1_sylancl $e |- ch $.
	e2_sylancl $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylancl $p |- ( ph -> th ) $= e0_sylancl e1_sylancl f2_sylancl f0_sylancl p_a1i e2_sylancl f0_sylancl f1_sylancl f2_sylancl f3_sylancl p_syl2anc $.
$}

$(Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)

${
	$v ph ps ch th  $.
	f0_sylancr $f wff ph $.
	f1_sylancr $f wff ps $.
	f2_sylancr $f wff ch $.
	f3_sylancr $f wff th $.
	e0_sylancr $e |- ps $.
	e1_sylancr $e |- ( ph -> ch ) $.
	e2_sylancr $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylancr $p |- ( ph -> th ) $= e0_sylancr f1_sylancr f0_sylancr p_a1i e1_sylancr e2_sylancr f0_sylancr f1_sylancr f2_sylancr f3_sylancr p_syl2anc $.
$}

$(Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)

${
	$v ph ps ch th  $.
	f0_sylanbrc $f wff ph $.
	f1_sylanbrc $f wff ps $.
	f2_sylanbrc $f wff ch $.
	f3_sylanbrc $f wff th $.
	e0_sylanbrc $e |- ( ph -> ps ) $.
	e1_sylanbrc $e |- ( ph -> ch ) $.
	e2_sylanbrc $e |- ( th <-> ( ps /\ ch ) ) $.
	p_sylanbrc $p |- ( ph -> th ) $= e0_sylanbrc e1_sylanbrc f0_sylanbrc f1_sylanbrc f2_sylanbrc p_jca e2_sylanbrc f0_sylanbrc f1_sylanbrc f2_sylanbrc a_wa f3_sylanbrc p_sylibr $.
$}

$(A syllogism inference combined with contraction.  (Contributed by NM,
       3-Sep-2004.) $)

${
	$v ph ps ch th  $.
	f0_sylancb $f wff ph $.
	f1_sylancb $f wff ps $.
	f2_sylancb $f wff ch $.
	f3_sylancb $f wff th $.
	e0_sylancb $e |- ( ph <-> ps ) $.
	e1_sylancb $e |- ( ph <-> ch ) $.
	e2_sylancb $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylancb $p |- ( ph -> th ) $= e0_sylancb e1_sylancb e2_sylancb f0_sylancb f1_sylancb f2_sylancb f3_sylancb f0_sylancb p_syl2anb f0_sylancb f3_sylancb p_anidms $.
$}

$(A syllogism inference combined with contraction.  (Contributed by NM,
       3-Sep-2004.) $)

${
	$v ph ps ch th  $.
	f0_sylancbr $f wff ph $.
	f1_sylancbr $f wff ps $.
	f2_sylancbr $f wff ch $.
	f3_sylancbr $f wff th $.
	e0_sylancbr $e |- ( ps <-> ph ) $.
	e1_sylancbr $e |- ( ch <-> ph ) $.
	e2_sylancbr $e |- ( ( ps /\ ch ) -> th ) $.
	p_sylancbr $p |- ( ph -> th ) $= e0_sylancbr e1_sylancbr e2_sylancbr f0_sylancbr f1_sylancbr f2_sylancbr f3_sylancbr f0_sylancbr p_syl2anbr f0_sylancbr f3_sylancbr p_anidms $.
$}

$(Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 2-Jul-2008.) $)

${
	$v ph ps ch th  $.
	f0_sylancom $f wff ph $.
	f1_sylancom $f wff ps $.
	f2_sylancom $f wff ch $.
	f3_sylancom $f wff th $.
	e0_sylancom $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_sylancom $e |- ( ( ch /\ ps ) -> th ) $.
	p_sylancom $p |- ( ( ph /\ ps ) -> th ) $= e0_sylancom f0_sylancom f1_sylancom p_simpr e1_sylancom f0_sylancom f1_sylancom a_wa f2_sylancom f1_sylancom f3_sylancom p_syl2anc $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 23-May-1999.)
       (Proof shortened by Wolf Lammen, 22-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_mpdan $f wff ph $.
	f1_mpdan $f wff ps $.
	f2_mpdan $f wff ch $.
	e0_mpdan $e |- ( ph -> ps ) $.
	e1_mpdan $e |- ( ( ph /\ ps ) -> ch ) $.
	p_mpdan $p |- ( ph -> ch ) $= f0_mpdan p_id e0_mpdan e1_mpdan f0_mpdan f0_mpdan f1_mpdan f2_mpdan p_syl2anc $.
$}

$(An inference based on modus ponens with commutation of antecedents.
       (Contributed by NM, 28-Oct-2003.)  (Proof shortened by Wolf Lammen,
       7-Apr-2013.) $)

${
	$v ph ps ch  $.
	f0_mpancom $f wff ph $.
	f1_mpancom $f wff ps $.
	f2_mpancom $f wff ch $.
	e0_mpancom $e |- ( ps -> ph ) $.
	e1_mpancom $e |- ( ( ph /\ ps ) -> ch ) $.
	p_mpancom $p |- ( ps -> ch ) $= e0_mpancom f1_mpancom p_id e1_mpancom f1_mpancom f0_mpancom f1_mpancom f2_mpancom p_syl2anc $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 30-Aug-1993.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)

${
	$v ph ps ch  $.
	f0_mpan $f wff ph $.
	f1_mpan $f wff ps $.
	f2_mpan $f wff ch $.
	e0_mpan $e |- ph $.
	e1_mpan $e |- ( ( ph /\ ps ) -> ch ) $.
	p_mpan $p |- ( ps -> ch ) $= e0_mpan f0_mpan f1_mpan p_a1i e1_mpan f0_mpan f1_mpan f2_mpan p_mpancom $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 16-Sep-1993.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_mpan2 $f wff ph $.
	f1_mpan2 $f wff ps $.
	f2_mpan2 $f wff ch $.
	e0_mpan2 $e |- ps $.
	e1_mpan2 $e |- ( ( ph /\ ps ) -> ch ) $.
	p_mpan2 $p |- ( ph -> ch ) $= e0_mpan2 f1_mpan2 f0_mpan2 p_a1i e1_mpan2 f0_mpan2 f1_mpan2 f2_mpan2 p_mpdan $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       13-Apr-1995.) $)

${
	$v ph ps ch  $.
	f0_mp2an $f wff ph $.
	f1_mp2an $f wff ps $.
	f2_mp2an $f wff ch $.
	e0_mp2an $e |- ph $.
	e1_mp2an $e |- ps $.
	e2_mp2an $e |- ( ( ph /\ ps ) -> ch ) $.
	p_mp2an $p |- ch $= e1_mp2an e0_mp2an e2_mp2an f0_mp2an f1_mp2an f2_mp2an p_mpan f1_mp2an f2_mp2an a_ax-mp $.
$}

$(An inference based on modus ponens.  (Contributed by Jeff Madsen,
       15-Jun-2010.) $)

${
	$v ph ps ch th ta  $.
	f0_mp4an $f wff ph $.
	f1_mp4an $f wff ps $.
	f2_mp4an $f wff ch $.
	f3_mp4an $f wff th $.
	f4_mp4an $f wff ta $.
	e0_mp4an $e |- ph $.
	e1_mp4an $e |- ps $.
	e2_mp4an $e |- ch $.
	e3_mp4an $e |- th $.
	e4_mp4an $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
	p_mp4an $p |- ta $= e0_mp4an e1_mp4an f0_mp4an f1_mp4an p_pm3.2i e2_mp4an e3_mp4an f2_mp4an f3_mp4an p_pm3.2i e4_mp4an f0_mp4an f1_mp4an a_wa f2_mp4an f3_mp4an a_wa f4_mp4an p_mp2an $.
$}

$(A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)

${
	$v ph ps ch th  $.
	f0_mpan2d $f wff ph $.
	f1_mpan2d $f wff ps $.
	f2_mpan2d $f wff ch $.
	f3_mpan2d $f wff th $.
	e0_mpan2d $e |- ( ph -> ch ) $.
	e1_mpan2d $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_mpan2d $p |- ( ph -> ( ps -> th ) ) $= e0_mpan2d e1_mpan2d f0_mpan2d f1_mpan2d f2_mpan2d f3_mpan2d p_exp3a f0_mpan2d f1_mpan2d f2_mpan2d f3_mpan2d p_mpid $.
$}

$(A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)

${
	$v ph ps ch th  $.
	f0_mpand $f wff ph $.
	f1_mpand $f wff ps $.
	f2_mpand $f wff ch $.
	f3_mpand $f wff th $.
	e0_mpand $e |- ( ph -> ps ) $.
	e1_mpand $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_mpand $p |- ( ph -> ( ch -> th ) ) $= e0_mpand e1_mpand f0_mpand f1_mpand f2_mpand f3_mpand p_ancomsd f0_mpand f2_mpand f1_mpand f3_mpand p_mpan2d $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 10-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_mpani $f wff ph $.
	f1_mpani $f wff ps $.
	f2_mpani $f wff ch $.
	f3_mpani $f wff th $.
	e0_mpani $e |- ps $.
	e1_mpani $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_mpani $p |- ( ph -> ( ch -> th ) ) $= e0_mpani f1_mpani f0_mpani p_a1i e1_mpani f0_mpani f1_mpani f2_mpani f3_mpani p_mpand $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 10-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_mpan2i $f wff ph $.
	f1_mpan2i $f wff ps $.
	f2_mpan2i $f wff ch $.
	f3_mpan2i $f wff th $.
	e0_mpan2i $e |- ch $.
	e1_mpan2i $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_mpan2i $p |- ( ph -> ( ps -> th ) ) $= e0_mpan2i f2_mpan2i f0_mpan2i p_a1i e1_mpan2i f0_mpan2i f1_mpan2i f2_mpan2i f3_mpan2i p_mpan2d $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       12-Dec-2004.) $)

${
	$v ph ps ch th  $.
	f0_mp2ani $f wff ph $.
	f1_mp2ani $f wff ps $.
	f2_mp2ani $f wff ch $.
	f3_mp2ani $f wff th $.
	e0_mp2ani $e |- ps $.
	e1_mp2ani $e |- ch $.
	e2_mp2ani $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_mp2ani $p |- ( ph -> th ) $= e1_mp2ani e0_mp2ani e2_mp2ani f0_mp2ani f1_mp2ani f2_mp2ani f3_mp2ani p_mpani f0_mp2ani f2_mp2ani f3_mp2ani p_mpi $.
$}

$(A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)

${
	$v ph ps ch th  $.
	f0_mp2and $f wff ph $.
	f1_mp2and $f wff ps $.
	f2_mp2and $f wff ch $.
	f3_mp2and $f wff th $.
	e0_mp2and $e |- ( ph -> ps ) $.
	e1_mp2and $e |- ( ph -> ch ) $.
	e2_mp2and $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_mp2and $p |- ( ph -> th ) $= e1_mp2and e0_mp2and e2_mp2and f0_mp2and f1_mp2and f2_mp2and f3_mp2and p_mpand f0_mp2and f2_mp2and f3_mp2and p_mpd $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 16-Aug-1994.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)

${
	$v ph ps ch th  $.
	f0_mpanl1 $f wff ph $.
	f1_mpanl1 $f wff ps $.
	f2_mpanl1 $f wff ch $.
	f3_mpanl1 $f wff th $.
	e0_mpanl1 $e |- ph $.
	e1_mpanl1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_mpanl1 $p |- ( ( ps /\ ch ) -> th ) $= e0_mpanl1 f1_mpanl1 f0_mpanl1 p_jctl e1_mpanl1 f1_mpanl1 f0_mpanl1 f1_mpanl1 a_wa f2_mpanl1 f3_mpanl1 p_sylan $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 16-Aug-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch th  $.
	f0_mpanl2 $f wff ph $.
	f1_mpanl2 $f wff ps $.
	f2_mpanl2 $f wff ch $.
	f3_mpanl2 $f wff th $.
	e0_mpanl2 $e |- ps $.
	e1_mpanl2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_mpanl2 $p |- ( ( ph /\ ch ) -> th ) $= e0_mpanl2 f0_mpanl2 f1_mpanl2 p_jctr e1_mpanl2 f0_mpanl2 f0_mpanl2 f1_mpanl2 a_wa f2_mpanl2 f3_mpanl2 p_sylan $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       13-Jul-2005.) $)

${
	$v ph ps ch th  $.
	f0_mpanl12 $f wff ph $.
	f1_mpanl12 $f wff ps $.
	f2_mpanl12 $f wff ch $.
	f3_mpanl12 $f wff th $.
	e0_mpanl12 $e |- ph $.
	e1_mpanl12 $e |- ps $.
	e2_mpanl12 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_mpanl12 $p |- ( ch -> th ) $= e1_mpanl12 e0_mpanl12 e2_mpanl12 f0_mpanl12 f1_mpanl12 f2_mpanl12 f3_mpanl12 p_mpanl1 f1_mpanl12 f2_mpanl12 f3_mpanl12 p_mpan $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 3-May-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch th  $.
	f0_mpanr1 $f wff ph $.
	f1_mpanr1 $f wff ps $.
	f2_mpanr1 $f wff ch $.
	f3_mpanr1 $f wff th $.
	e0_mpanr1 $e |- ps $.
	e1_mpanr1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_mpanr1 $p |- ( ( ph /\ ch ) -> th ) $= e0_mpanr1 e1_mpanr1 f0_mpanr1 f1_mpanr1 f2_mpanr1 f3_mpanr1 p_anassrs f0_mpanr1 f1_mpanr1 f2_mpanr1 f3_mpanr1 p_mpanl2 $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 3-May-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof shortened by
       Wolf Lammen, 7-Apr-2013.) $)

${
	$v ph ps ch th  $.
	f0_mpanr2 $f wff ph $.
	f1_mpanr2 $f wff ps $.
	f2_mpanr2 $f wff ch $.
	f3_mpanr2 $f wff th $.
	e0_mpanr2 $e |- ch $.
	e1_mpanr2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_mpanr2 $p |- ( ( ph /\ ps ) -> th ) $= e0_mpanr2 f1_mpanr2 f2_mpanr2 p_jctr e1_mpanr2 f1_mpanr2 f0_mpanr2 f1_mpanr2 f2_mpanr2 a_wa f3_mpanr2 p_sylan2 $.
$}

$(An inference based on modus ponens.  (Contributed by NM,
       24-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_mpanr12 $f wff ph $.
	f1_mpanr12 $f wff ps $.
	f2_mpanr12 $f wff ch $.
	f3_mpanr12 $f wff th $.
	e0_mpanr12 $e |- ps $.
	e1_mpanr12 $e |- ch $.
	e2_mpanr12 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_mpanr12 $p |- ( ph -> th ) $= e1_mpanr12 e0_mpanr12 e2_mpanr12 f0_mpanr12 f1_mpanr12 f2_mpanr12 f3_mpanr12 p_mpanr1 f0_mpanr12 f2_mpanr12 f3_mpanr12 p_mpan2 $.
$}

$(An inference based on modus ponens.  (Contributed by NM, 30-Dec-2004.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_mpanlr1 $f wff ph $.
	f1_mpanlr1 $f wff ps $.
	f2_mpanlr1 $f wff ch $.
	f3_mpanlr1 $f wff th $.
	f4_mpanlr1 $f wff ta $.
	e0_mpanlr1 $e |- ps $.
	e1_mpanlr1 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
	p_mpanlr1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $= e0_mpanlr1 f2_mpanlr1 f1_mpanlr1 p_jctl e1_mpanlr1 f2_mpanlr1 f0_mpanlr1 f1_mpanlr1 f2_mpanlr1 a_wa f3_mpanlr1 f4_mpanlr1 p_sylanl2 $.
$}

$(Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 4-May-2007.) $)

${
	$v ph ps ch th  $.
	f0_pm5.74da $f wff ph $.
	f1_pm5.74da $f wff ps $.
	f2_pm5.74da $f wff ch $.
	f3_pm5.74da $f wff th $.
	e0_pm5.74da $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	p_pm5.74da $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $= e0_pm5.74da f0_pm5.74da f1_pm5.74da f2_pm5.74da f3_pm5.74da a_wb p_ex f0_pm5.74da f1_pm5.74da f2_pm5.74da f3_pm5.74da p_pm5.74d $.
$}

$(Theorem *4.45 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm4.45 $f wff ph $.
	f1_pm4.45 $f wff ps $.
	p_pm4.45 $p |- ( ph <-> ( ph /\ ( ph \/ ps ) ) ) $= f0_pm4.45 f1_pm4.45 p_orc f0_pm4.45 f0_pm4.45 f1_pm4.45 a_wo p_pm4.71i $.
$}

$(Distribution of implication with conjunction.  (Contributed by NM,
     31-May-1999.)  (Proof shortened by Wolf Lammen, 6-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_imdistan $f wff ph $.
	f1_imdistan $f wff ps $.
	f2_imdistan $f wff ch $.
	p_imdistan $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $= f0_imdistan f1_imdistan f2_imdistan p_pm5.42 f0_imdistan f1_imdistan f0_imdistan f2_imdistan a_wa p_impexp f0_imdistan f1_imdistan f2_imdistan a_wi a_wi f0_imdistan f1_imdistan f0_imdistan f2_imdistan a_wa a_wi a_wi f0_imdistan f1_imdistan a_wa f0_imdistan f2_imdistan a_wa a_wi p_bitr4i $.
$}

$(Distribution of implication with conjunction.  (Contributed by NM,
       1-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_imdistani $f wff ph $.
	f1_imdistani $f wff ps $.
	f2_imdistani $f wff ch $.
	e0_imdistani $e |- ( ph -> ( ps -> ch ) ) $.
	p_imdistani $p |- ( ( ph /\ ps ) -> ( ph /\ ch ) ) $= e0_imdistani f0_imdistani f1_imdistani f2_imdistani p_anc2li f0_imdistani f1_imdistani f0_imdistani f2_imdistani a_wa p_imp $.
$}

$(Distribution of implication with conjunction.  (Contributed by NM,
       8-Jan-2002.) $)

${
	$v ph ps ch  $.
	f0_imdistanri $f wff ph $.
	f1_imdistanri $f wff ps $.
	f2_imdistanri $f wff ch $.
	e0_imdistanri $e |- ( ph -> ( ps -> ch ) ) $.
	p_imdistanri $p |- ( ( ps /\ ph ) -> ( ch /\ ph ) ) $= e0_imdistanri f0_imdistanri f1_imdistanri f2_imdistanri p_com12 f1_imdistanri f0_imdistanri f2_imdistanri p_impac $.
$}

$(Distribution of implication with conjunction (deduction rule).
       (Contributed by NM, 27-Aug-2004.) $)

${
	$v ph ps ch th  $.
	f0_imdistand $f wff ph $.
	f1_imdistand $f wff ps $.
	f2_imdistand $f wff ch $.
	f3_imdistand $f wff th $.
	e0_imdistand $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_imdistand $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $= e0_imdistand f1_imdistand f2_imdistand f3_imdistand p_imdistan f0_imdistand f1_imdistand f2_imdistand f3_imdistand a_wi a_wi f1_imdistand f2_imdistand a_wa f1_imdistand f3_imdistand a_wa a_wi p_sylib $.
$}

$(Distribution of implication with conjunction (deduction version with
       conjoined antecedent).  (Contributed by Jeff Madsen, 19-Jun-2011.) $)

${
	$v ph ps ch th  $.
	f0_imdistanda $f wff ph $.
	f1_imdistanda $f wff ps $.
	f2_imdistanda $f wff ch $.
	f3_imdistanda $f wff th $.
	e0_imdistanda $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	p_imdistanda $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $= e0_imdistanda f0_imdistanda f1_imdistanda f2_imdistanda f3_imdistanda a_wi p_ex f0_imdistanda f1_imdistanda f2_imdistanda f3_imdistanda p_imdistand $.
$}

$(Introduce a left conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_anbi2i $f wff ph $.
	f1_anbi2i $f wff ps $.
	f2_anbi2i $f wff ch $.
	e0_anbi2i $e |- ( ph <-> ps ) $.
	p_anbi2i $p |- ( ( ch /\ ph ) <-> ( ch /\ ps ) ) $= e0_anbi2i f0_anbi2i f1_anbi2i a_wb f2_anbi2i p_a1i f2_anbi2i f0_anbi2i f1_anbi2i p_pm5.32i $.
$}

$(Introduce a right conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_anbi1i $f wff ph $.
	f1_anbi1i $f wff ps $.
	f2_anbi1i $f wff ch $.
	e0_anbi1i $e |- ( ph <-> ps ) $.
	p_anbi1i $p |- ( ( ph /\ ch ) <-> ( ps /\ ch ) ) $= e0_anbi1i f0_anbi1i f1_anbi1i a_wb f2_anbi1i p_a1i f2_anbi1i f0_anbi1i f1_anbi1i p_pm5.32ri $.
$}

$(Variant of ~ anbi2i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)

${
	$v ph ps ch  $.
	f0_anbi2ci $f wff ph $.
	f1_anbi2ci $f wff ps $.
	f2_anbi2ci $f wff ch $.
	e0_anbi2ci $e |- ( ph <-> ps ) $.
	p_anbi2ci $p |- ( ( ph /\ ch ) <-> ( ch /\ ps ) ) $= e0_anbi2ci f0_anbi2ci f1_anbi2ci f2_anbi2ci p_anbi1i f1_anbi2ci f2_anbi2ci p_ancom f0_anbi2ci f2_anbi2ci a_wa f1_anbi2ci f2_anbi2ci a_wa f2_anbi2ci f1_anbi2ci a_wa p_bitri $.
$}

$(Conjoin both sides of two equivalences.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_anbi12i $f wff ph $.
	f1_anbi12i $f wff ps $.
	f2_anbi12i $f wff ch $.
	f3_anbi12i $f wff th $.
	e0_anbi12i $e |- ( ph <-> ps ) $.
	e1_anbi12i $e |- ( ch <-> th ) $.
	p_anbi12i $p |- ( ( ph /\ ch ) <-> ( ps /\ th ) ) $= e0_anbi12i f0_anbi12i f1_anbi12i f2_anbi12i p_anbi1i e1_anbi12i f2_anbi12i f3_anbi12i f1_anbi12i p_anbi2i f0_anbi12i f2_anbi12i a_wa f1_anbi12i f2_anbi12i a_wa f1_anbi12i f3_anbi12i a_wa p_bitri $.
$}

$(Variant of ~ anbi12i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)

${
	$v ph ps ch th  $.
	f0_anbi12ci $f wff ph $.
	f1_anbi12ci $f wff ps $.
	f2_anbi12ci $f wff ch $.
	f3_anbi12ci $f wff th $.
	e0_anbi12ci $e |- ( ph <-> ps ) $.
	e1_anbi12ci $e |- ( ch <-> th ) $.
	p_anbi12ci $p |- ( ( ph /\ ch ) <-> ( th /\ ps ) ) $= e0_anbi12ci e1_anbi12ci f0_anbi12ci f1_anbi12ci f2_anbi12ci f3_anbi12ci p_anbi12i f1_anbi12ci f3_anbi12ci p_ancom f0_anbi12ci f2_anbi12ci a_wa f1_anbi12ci f3_anbi12ci a_wa f3_anbi12ci f1_anbi12ci a_wa p_bitri $.
$}

$(Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_sylan9bb $f wff ph $.
	f1_sylan9bb $f wff ps $.
	f2_sylan9bb $f wff ch $.
	f3_sylan9bb $f wff th $.
	f4_sylan9bb $f wff ta $.
	e0_sylan9bb $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_sylan9bb $e |- ( th -> ( ch <-> ta ) ) $.
	p_sylan9bb $p |- ( ( ph /\ th ) -> ( ps <-> ta ) ) $= e0_sylan9bb f0_sylan9bb f1_sylan9bb f2_sylan9bb a_wb f3_sylan9bb p_adantr e1_sylan9bb f3_sylan9bb f2_sylan9bb f4_sylan9bb a_wb f0_sylan9bb p_adantl f0_sylan9bb f3_sylan9bb a_wa f1_sylan9bb f2_sylan9bb f4_sylan9bb p_bitrd $.
$}

$(Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_sylan9bbr $f wff ph $.
	f1_sylan9bbr $f wff ps $.
	f2_sylan9bbr $f wff ch $.
	f3_sylan9bbr $f wff th $.
	f4_sylan9bbr $f wff ta $.
	e0_sylan9bbr $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_sylan9bbr $e |- ( th -> ( ch <-> ta ) ) $.
	p_sylan9bbr $p |- ( ( th /\ ph ) -> ( ps <-> ta ) ) $= e0_sylan9bbr e1_sylan9bbr f0_sylan9bbr f1_sylan9bbr f2_sylan9bbr f3_sylan9bbr f4_sylan9bbr p_sylan9bb f0_sylan9bbr f3_sylan9bbr f1_sylan9bbr f4_sylan9bbr a_wb p_ancoms $.
$}

$(Deduction adding a left disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_orbi2d $f wff ph $.
	f1_orbi2d $f wff ps $.
	f2_orbi2d $f wff ch $.
	f3_orbi2d $f wff th $.
	e0_orbi2d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_orbi2d $p |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) ) $= e0_orbi2d f0_orbi2d f1_orbi2d f2_orbi2d f3_orbi2d a_wn p_imbi2d f3_orbi2d f1_orbi2d a_df-or f3_orbi2d f2_orbi2d a_df-or f0_orbi2d f3_orbi2d a_wn f1_orbi2d a_wi f3_orbi2d a_wn f2_orbi2d a_wi f3_orbi2d f1_orbi2d a_wo f3_orbi2d f2_orbi2d a_wo p_3bitr4g $.
$}

$(Deduction adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_orbi1d $f wff ph $.
	f1_orbi1d $f wff ps $.
	f2_orbi1d $f wff ch $.
	f3_orbi1d $f wff th $.
	e0_orbi1d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_orbi1d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) ) $= e0_orbi1d f0_orbi1d f1_orbi1d f2_orbi1d f3_orbi1d p_orbi2d f1_orbi1d f3_orbi1d p_orcom f2_orbi1d f3_orbi1d p_orcom f0_orbi1d f3_orbi1d f1_orbi1d a_wo f3_orbi1d f2_orbi1d a_wo f1_orbi1d f3_orbi1d a_wo f2_orbi1d f3_orbi1d a_wo p_3bitr4g $.
$}

$(Deduction adding a left conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)

${
	$v ph ps ch th  $.
	f0_anbi2d $f wff ph $.
	f1_anbi2d $f wff ps $.
	f2_anbi2d $f wff ch $.
	f3_anbi2d $f wff th $.
	e0_anbi2d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_anbi2d $p |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) ) $= e0_anbi2d f0_anbi2d f1_anbi2d f2_anbi2d a_wb f3_anbi2d p_a1d f0_anbi2d f3_anbi2d f1_anbi2d f2_anbi2d p_pm5.32d $.
$}

$(Deduction adding a right conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)

${
	$v ph ps ch th  $.
	f0_anbi1d $f wff ph $.
	f1_anbi1d $f wff ps $.
	f2_anbi1d $f wff ch $.
	f3_anbi1d $f wff th $.
	e0_anbi1d $e |- ( ph -> ( ps <-> ch ) ) $.
	p_anbi1d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) ) $= e0_anbi1d f0_anbi1d f1_anbi1d f2_anbi1d a_wb f3_anbi1d p_a1d f0_anbi1d f3_anbi1d f1_anbi1d f2_anbi1d p_pm5.32rd $.
$}

$(Theorem *4.37 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_orbi1 $f wff ph $.
	f1_orbi1 $f wff ps $.
	f2_orbi1 $f wff ch $.
	p_orbi1 $p |- ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $= f0_orbi1 f1_orbi1 a_wb p_id f0_orbi1 f1_orbi1 a_wb f0_orbi1 f1_orbi1 f2_orbi1 p_orbi1d $.
$}

$(Introduce a right conjunct to both sides of a logical equivalence.
     Theorem *4.36 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_anbi1 $f wff ph $.
	f1_anbi1 $f wff ps $.
	f2_anbi1 $f wff ch $.
	p_anbi1 $p |- ( ( ph <-> ps ) -> ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) $= f0_anbi1 f1_anbi1 a_wb p_id f0_anbi1 f1_anbi1 a_wb f0_anbi1 f1_anbi1 f2_anbi1 p_anbi1d $.
$}

$(Introduce a left conjunct to both sides of a logical equivalence.
     (Contributed by NM, 16-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_anbi2 $f wff ph $.
	f1_anbi2 $f wff ps $.
	f2_anbi2 $f wff ch $.
	p_anbi2 $p |- ( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) ) $= f0_anbi2 f1_anbi2 a_wb p_id f0_anbi2 f1_anbi2 a_wb f0_anbi2 f1_anbi2 f2_anbi2 p_anbi2d $.
$}

$(Theorem *4.22 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_bitr $f wff ph $.
	f1_bitr $f wff ps $.
	f2_bitr $f wff ch $.
	p_bitr $p |- ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) ) $= f0_bitr f1_bitr f2_bitr p_bibi1 f0_bitr f1_bitr a_wb f0_bitr f2_bitr a_wb f1_bitr f2_bitr a_wb p_biimpar $.
$}

$(Deduction joining two equivalences to form equivalence of disjunctions.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th ta  $.
	f0_orbi12d $f wff ph $.
	f1_orbi12d $f wff ps $.
	f2_orbi12d $f wff ch $.
	f3_orbi12d $f wff th $.
	f4_orbi12d $f wff ta $.
	e0_orbi12d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_orbi12d $e |- ( ph -> ( th <-> ta ) ) $.
	p_orbi12d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) ) $= e0_orbi12d f0_orbi12d f1_orbi12d f2_orbi12d f3_orbi12d p_orbi1d e1_orbi12d f0_orbi12d f3_orbi12d f4_orbi12d f2_orbi12d p_orbi2d f0_orbi12d f1_orbi12d f3_orbi12d a_wo f2_orbi12d f3_orbi12d a_wo f2_orbi12d f4_orbi12d a_wo p_bitrd $.
$}

$(Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th ta  $.
	f0_anbi12d $f wff ph $.
	f1_anbi12d $f wff ps $.
	f2_anbi12d $f wff ch $.
	f3_anbi12d $f wff th $.
	f4_anbi12d $f wff ta $.
	e0_anbi12d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_anbi12d $e |- ( ph -> ( th <-> ta ) ) $.
	p_anbi12d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) ) $= e0_anbi12d f0_anbi12d f1_anbi12d f2_anbi12d f3_anbi12d p_anbi1d e1_anbi12d f0_anbi12d f3_anbi12d f4_anbi12d f2_anbi12d p_anbi2d f0_anbi12d f1_anbi12d f3_anbi12d a_wa f2_anbi12d f3_anbi12d a_wa f2_anbi12d f4_anbi12d a_wa p_bitrd $.
$}

$(Theorem *5.3 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch  $.
	f0_pm5.3 $f wff ph $.
	f1_pm5.3 $f wff ps $.
	f2_pm5.3 $f wff ch $.
	p_pm5.3 $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $= f0_pm5.3 f1_pm5.3 f2_pm5.3 p_impexp f0_pm5.3 f1_pm5.3 f2_pm5.3 p_imdistan f0_pm5.3 f1_pm5.3 a_wa f2_pm5.3 a_wi f0_pm5.3 f1_pm5.3 f2_pm5.3 a_wi a_wi f0_pm5.3 f1_pm5.3 a_wa f0_pm5.3 f2_pm5.3 a_wa a_wi p_bitri $.
$}

$(Theorem *5.61 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 30-Jun-2013.) $)

${
	$v ph ps  $.
	f0_pm5.61 $f wff ph $.
	f1_pm5.61 $f wff ps $.
	p_pm5.61 $p |- ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) ) $= f1_pm5.61 f0_pm5.61 p_biorf f1_pm5.61 f0_pm5.61 p_orcom f1_pm5.61 a_wn f0_pm5.61 f1_pm5.61 f0_pm5.61 a_wo f0_pm5.61 f1_pm5.61 a_wo p_syl6rbb f1_pm5.61 a_wn f0_pm5.61 f1_pm5.61 a_wo f0_pm5.61 p_pm5.32ri $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_adantll $f wff ph $.
	f1_adantll $f wff ps $.
	f2_adantll $f wff ch $.
	f3_adantll $f wff th $.
	e0_adantll $e |- ( ( ph /\ ps ) -> ch ) $.
	p_adantll $p |- ( ( ( th /\ ph ) /\ ps ) -> ch ) $= f3_adantll f0_adantll p_simpr e0_adantll f3_adantll f0_adantll a_wa f0_adantll f1_adantll f2_adantll p_sylan $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_adantlr $f wff ph $.
	f1_adantlr $f wff ps $.
	f2_adantlr $f wff ch $.
	f3_adantlr $f wff th $.
	e0_adantlr $e |- ( ( ph /\ ps ) -> ch ) $.
	p_adantlr $p |- ( ( ( ph /\ th ) /\ ps ) -> ch ) $= f0_adantlr f3_adantlr p_simpl e0_adantlr f0_adantlr f3_adantlr a_wa f0_adantlr f1_adantlr f2_adantlr p_sylan $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_adantrl $f wff ph $.
	f1_adantrl $f wff ps $.
	f2_adantrl $f wff ch $.
	f3_adantrl $f wff th $.
	e0_adantrl $e |- ( ( ph /\ ps ) -> ch ) $.
	p_adantrl $p |- ( ( ph /\ ( th /\ ps ) ) -> ch ) $= f3_adantrl f1_adantrl p_simpr e0_adantrl f3_adantrl f1_adantrl a_wa f0_adantrl f1_adantrl f2_adantrl p_sylan2 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_adantrr $f wff ph $.
	f1_adantrr $f wff ps $.
	f2_adantrr $f wff ch $.
	f3_adantrr $f wff th $.
	e0_adantrr $e |- ( ( ph /\ ps ) -> ch ) $.
	p_adantrr $p |- ( ( ph /\ ( ps /\ th ) ) -> ch ) $= f1_adantrr f3_adantrr p_simpl e0_adantrr f1_adantrr f3_adantrr a_wa f0_adantrr f1_adantrr f2_adantrr p_sylan2 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 2-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_adantlll $f wff ph $.
	f1_adantlll $f wff ps $.
	f2_adantlll $f wff ch $.
	f3_adantlll $f wff th $.
	f4_adantlll $f wff ta $.
	e0_adantlll $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_adantlll $p |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th ) $= f4_adantlll f0_adantlll p_simpr e0_adantlll f4_adantlll f0_adantlll a_wa f0_adantlll f1_adantlll f2_adantlll f3_adantlll p_sylanl1 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_adantllr $f wff ph $.
	f1_adantllr $f wff ps $.
	f2_adantllr $f wff ch $.
	f3_adantllr $f wff th $.
	f4_adantllr $f wff ta $.
	e0_adantllr $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_adantllr $p |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th ) $= f0_adantllr f4_adantllr p_simpl e0_adantllr f0_adantllr f4_adantllr a_wa f0_adantllr f1_adantllr f2_adantllr f3_adantllr p_sylanl1 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_adantlrl $f wff ph $.
	f1_adantlrl $f wff ps $.
	f2_adantlrl $f wff ch $.
	f3_adantlrl $f wff th $.
	f4_adantlrl $f wff ta $.
	e0_adantlrl $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_adantlrl $p |- ( ( ( ph /\ ( ta /\ ps ) ) /\ ch ) -> th ) $= f4_adantlrl f1_adantlrl p_simpr e0_adantlrl f4_adantlrl f1_adantlrl a_wa f0_adantlrl f1_adantlrl f2_adantlrl f3_adantlrl p_sylanl2 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_adantlrr $f wff ph $.
	f1_adantlrr $f wff ps $.
	f2_adantlrr $f wff ch $.
	f3_adantlrr $f wff th $.
	f4_adantlrr $f wff ta $.
	e0_adantlrr $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_adantlrr $p |- ( ( ( ph /\ ( ps /\ ta ) ) /\ ch ) -> th ) $= f1_adantlrr f4_adantlrr p_simpl e0_adantlrr f1_adantlrr f4_adantlrr a_wa f0_adantlrr f1_adantlrr f2_adantlrr f3_adantlrr p_sylanl2 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_adantrll $f wff ph $.
	f1_adantrll $f wff ps $.
	f2_adantrll $f wff ch $.
	f3_adantrll $f wff th $.
	f4_adantrll $f wff ta $.
	e0_adantrll $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_adantrll $p |- ( ( ph /\ ( ( ta /\ ps ) /\ ch ) ) -> th ) $= f4_adantrll f1_adantrll p_simpr e0_adantrll f4_adantrll f1_adantrll a_wa f0_adantrll f1_adantrll f2_adantrll f3_adantrll p_sylanr1 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_adantrlr $f wff ph $.
	f1_adantrlr $f wff ps $.
	f2_adantrlr $f wff ch $.
	f3_adantrlr $f wff th $.
	f4_adantrlr $f wff ta $.
	e0_adantrlr $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_adantrlr $p |- ( ( ph /\ ( ( ps /\ ta ) /\ ch ) ) -> th ) $= f1_adantrlr f4_adantrlr p_simpl e0_adantrlr f1_adantrlr f4_adantrlr a_wa f0_adantrlr f1_adantrlr f2_adantrlr f3_adantrlr p_sylanr1 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_adantrrl $f wff ph $.
	f1_adantrrl $f wff ps $.
	f2_adantrrl $f wff ch $.
	f3_adantrrl $f wff th $.
	f4_adantrrl $f wff ta $.
	e0_adantrrl $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_adantrrl $p |- ( ( ph /\ ( ps /\ ( ta /\ ch ) ) ) -> th ) $= f4_adantrrl f2_adantrrl p_simpr e0_adantrrl f4_adantrrl f2_adantrrl a_wa f0_adantrrl f1_adantrrl f2_adantrrl f3_adantrrl p_sylanr2 $.
$}

$(Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_adantrrr $f wff ph $.
	f1_adantrrr $f wff ps $.
	f2_adantrrr $f wff ch $.
	f3_adantrrr $f wff th $.
	f4_adantrrr $f wff ta $.
	e0_adantrrr $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_adantrrr $p |- ( ( ph /\ ( ps /\ ( ch /\ ta ) ) ) -> th ) $= f2_adantrrr f4_adantrrr p_simpl e0_adantrrr f2_adantrrr f4_adantrrr a_wa f0_adantrrr f1_adantrrr f2_adantrrr f3_adantrrr p_sylanr2 $.
$}

$(Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_ad2antrr $f wff ph $.
	f1_ad2antrr $f wff ps $.
	f2_ad2antrr $f wff ch $.
	f3_ad2antrr $f wff th $.
	e0_ad2antrr $e |- ( ph -> ps ) $.
	p_ad2antrr $p |- ( ( ( ph /\ ch ) /\ th ) -> ps ) $= e0_ad2antrr f0_ad2antrr f1_ad2antrr f3_ad2antrr p_adantr f0_ad2antrr f3_ad2antrr f1_ad2antrr f2_ad2antrr p_adantlr $.
$}

$(Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_ad2antlr $f wff ph $.
	f1_ad2antlr $f wff ps $.
	f2_ad2antlr $f wff ch $.
	f3_ad2antlr $f wff th $.
	e0_ad2antlr $e |- ( ph -> ps ) $.
	p_ad2antlr $p |- ( ( ( ch /\ ph ) /\ th ) -> ps ) $= e0_ad2antlr f0_ad2antlr f1_ad2antlr f3_ad2antlr p_adantr f0_ad2antlr f3_ad2antlr f1_ad2antlr f2_ad2antlr p_adantll $.
$}

$(Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.) $)

${
	$v ph ps ch th  $.
	f0_ad2antrl $f wff ph $.
	f1_ad2antrl $f wff ps $.
	f2_ad2antrl $f wff ch $.
	f3_ad2antrl $f wff th $.
	e0_ad2antrl $e |- ( ph -> ps ) $.
	p_ad2antrl $p |- ( ( ch /\ ( ph /\ th ) ) -> ps ) $= e0_ad2antrl f0_ad2antrl f1_ad2antrl f3_ad2antrl p_adantr f0_ad2antrl f3_ad2antrl a_wa f1_ad2antrl f2_ad2antrl p_adantl $.
$}

$(Deduction adding conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.) $)

${
	$v ph ps ch th  $.
	f0_ad2antll $f wff ph $.
	f1_ad2antll $f wff ps $.
	f2_ad2antll $f wff ch $.
	f3_ad2antll $f wff th $.
	e0_ad2antll $e |- ( ph -> ps ) $.
	p_ad2antll $p |- ( ( ch /\ ( th /\ ph ) ) -> ps ) $= e0_ad2antll f0_ad2antll f1_ad2antll f3_ad2antll p_adantl f3_ad2antll f0_ad2antll a_wa f1_ad2antll f2_ad2antll p_adantl $.
$}

$(Deduction adding three conjuncts to antecedent.  (Contributed by NM,
       28-Jul-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_ad3antrrr $f wff ph $.
	f1_ad3antrrr $f wff ps $.
	f2_ad3antrrr $f wff ch $.
	f3_ad3antrrr $f wff th $.
	f4_ad3antrrr $f wff ta $.
	e0_ad3antrrr $e |- ( ph -> ps ) $.
	p_ad3antrrr $p |- ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) -> ps ) $= e0_ad3antrrr f0_ad3antrrr f1_ad3antrrr f2_ad3antrrr p_adantr f0_ad3antrrr f2_ad3antrrr a_wa f1_ad3antrrr f3_ad3antrrr f4_ad3antrrr p_ad2antrr $.
$}

$(Deduction adding three conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch th ta  $.
	f0_ad3antlr $f wff ph $.
	f1_ad3antlr $f wff ps $.
	f2_ad3antlr $f wff ch $.
	f3_ad3antlr $f wff th $.
	f4_ad3antlr $f wff ta $.
	e0_ad3antlr $e |- ( ph -> ps ) $.
	p_ad3antlr $p |- ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) -> ps ) $= e0_ad3antlr f0_ad3antlr f1_ad3antlr f2_ad3antlr f3_ad3antlr p_ad2antlr f2_ad3antlr f0_ad3antlr a_wa f3_ad3antlr a_wa f1_ad3antlr f4_ad3antlr p_adantr $.
$}

$(Deduction adding 4 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch th ta et  $.
	f0_ad4antr $f wff ph $.
	f1_ad4antr $f wff ps $.
	f2_ad4antr $f wff ch $.
	f3_ad4antr $f wff th $.
	f4_ad4antr $f wff ta $.
	f5_ad4antr $f wff et $.
	e0_ad4antr $e |- ( ph -> ps ) $.
	p_ad4antr $p |- ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) -> ps ) $= e0_ad4antr f0_ad4antr f1_ad4antr f2_ad4antr f3_ad4antr f4_ad4antr p_ad3antrrr f0_ad4antr f2_ad4antr a_wa f3_ad4antr a_wa f4_ad4antr a_wa f1_ad4antr f5_ad4antr p_adantr $.
$}

$(Deduction adding 4 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch th ta et  $.
	f0_ad4antlr $f wff ph $.
	f1_ad4antlr $f wff ps $.
	f2_ad4antlr $f wff ch $.
	f3_ad4antlr $f wff th $.
	f4_ad4antlr $f wff ta $.
	f5_ad4antlr $f wff et $.
	e0_ad4antlr $e |- ( ph -> ps ) $.
	p_ad4antlr $p |- ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) -> ps ) $= e0_ad4antlr f0_ad4antlr f1_ad4antlr f2_ad4antlr f3_ad4antlr f4_ad4antlr p_ad3antlr f2_ad4antlr f0_ad4antlr a_wa f3_ad4antlr a_wa f4_ad4antlr a_wa f1_ad4antlr f5_ad4antlr p_adantr $.
$}

$(Deduction adding 5 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_ad5antr $f wff ph $.
	f1_ad5antr $f wff ps $.
	f2_ad5antr $f wff ch $.
	f3_ad5antr $f wff th $.
	f4_ad5antr $f wff ta $.
	f5_ad5antr $f wff et $.
	f6_ad5antr $f wff ze $.
	e0_ad5antr $e |- ( ph -> ps ) $.
	p_ad5antr $p |- ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ps ) $= e0_ad5antr f0_ad5antr f1_ad5antr f2_ad5antr f3_ad5antr f4_ad5antr f5_ad5antr p_ad4antr f0_ad5antr f2_ad5antr a_wa f3_ad5antr a_wa f4_ad5antr a_wa f5_ad5antr a_wa f1_ad5antr f6_ad5antr p_adantr $.
$}

$(Deduction adding 5 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_ad5antlr $f wff ph $.
	f1_ad5antlr $f wff ps $.
	f2_ad5antlr $f wff ch $.
	f3_ad5antlr $f wff th $.
	f4_ad5antlr $f wff ta $.
	f5_ad5antlr $f wff et $.
	f6_ad5antlr $f wff ze $.
	e0_ad5antlr $e |- ( ph -> ps ) $.
	p_ad5antlr $p |- ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ps ) $= e0_ad5antlr f0_ad5antlr f1_ad5antlr f2_ad5antlr f3_ad5antlr f4_ad5antlr f5_ad5antlr p_ad4antlr f2_ad5antlr f0_ad5antlr a_wa f3_ad5antlr a_wa f4_ad5antlr a_wa f5_ad5antlr a_wa f1_ad5antlr f6_ad5antlr p_adantr $.
$}

$(Deduction adding 6 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_ad6antr $f wff ph $.
	f1_ad6antr $f wff ps $.
	f2_ad6antr $f wff ch $.
	f3_ad6antr $f wff th $.
	f4_ad6antr $f wff ta $.
	f5_ad6antr $f wff et $.
	f6_ad6antr $f wff ze $.
	f7_ad6antr $f wff si $.
	e0_ad6antr $e |- ( ph -> ps ) $.
	p_ad6antr $p |- ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps ) $= e0_ad6antr f0_ad6antr f1_ad6antr f2_ad6antr f3_ad6antr f4_ad6antr f5_ad6antr f6_ad6antr p_ad5antr f0_ad6antr f2_ad6antr a_wa f3_ad6antr a_wa f4_ad6antr a_wa f5_ad6antr a_wa f6_ad6antr a_wa f1_ad6antr f7_ad6antr p_adantr $.
$}

$(Deduction adding 6 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_ad6antlr $f wff ph $.
	f1_ad6antlr $f wff ps $.
	f2_ad6antlr $f wff ch $.
	f3_ad6antlr $f wff th $.
	f4_ad6antlr $f wff ta $.
	f5_ad6antlr $f wff et $.
	f6_ad6antlr $f wff ze $.
	f7_ad6antlr $f wff si $.
	e0_ad6antlr $e |- ( ph -> ps ) $.
	p_ad6antlr $p |- ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps ) $= e0_ad6antlr f0_ad6antlr f1_ad6antlr f2_ad6antlr f3_ad6antlr f4_ad6antlr f5_ad6antlr f6_ad6antlr p_ad5antlr f2_ad6antlr f0_ad6antlr a_wa f3_ad6antlr a_wa f4_ad6antlr a_wa f5_ad6antlr a_wa f6_ad6antlr a_wa f1_ad6antlr f7_ad6antlr p_adantr $.
$}

$(Deduction adding 7 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_ad7antr $f wff ph $.
	f1_ad7antr $f wff ps $.
	f2_ad7antr $f wff ch $.
	f3_ad7antr $f wff th $.
	f4_ad7antr $f wff ta $.
	f5_ad7antr $f wff et $.
	f6_ad7antr $f wff ze $.
	f7_ad7antr $f wff si $.
	f8_ad7antr $f wff rh $.
	e0_ad7antr $e |- ( ph -> ps ) $.
	p_ad7antr $p |- ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps ) $= e0_ad7antr f0_ad7antr f1_ad7antr f2_ad7antr f3_ad7antr f4_ad7antr f5_ad7antr f6_ad7antr f7_ad7antr p_ad6antr f0_ad7antr f2_ad7antr a_wa f3_ad7antr a_wa f4_ad7antr a_wa f5_ad7antr a_wa f6_ad7antr a_wa f7_ad7antr a_wa f1_ad7antr f8_ad7antr p_adantr $.
$}

$(Deduction adding 7 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_ad7antlr $f wff ph $.
	f1_ad7antlr $f wff ps $.
	f2_ad7antlr $f wff ch $.
	f3_ad7antlr $f wff th $.
	f4_ad7antlr $f wff ta $.
	f5_ad7antlr $f wff et $.
	f6_ad7antlr $f wff ze $.
	f7_ad7antlr $f wff si $.
	f8_ad7antlr $f wff rh $.
	e0_ad7antlr $e |- ( ph -> ps ) $.
	p_ad7antlr $p |- ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps ) $= e0_ad7antlr f0_ad7antlr f1_ad7antlr f2_ad7antlr f3_ad7antlr f4_ad7antlr f5_ad7antlr f6_ad7antlr f7_ad7antlr p_ad6antlr f2_ad7antlr f0_ad7antlr a_wa f3_ad7antlr a_wa f4_ad7antlr a_wa f5_ad7antlr a_wa f6_ad7antlr a_wa f7_ad7antlr a_wa f1_ad7antlr f8_ad7antlr p_adantr $.
$}

$(Deduction adding 8 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu  $.
	f0_ad8antr $f wff ph $.
	f1_ad8antr $f wff ps $.
	f2_ad8antr $f wff ch $.
	f3_ad8antr $f wff th $.
	f4_ad8antr $f wff ta $.
	f5_ad8antr $f wff et $.
	f6_ad8antr $f wff ze $.
	f7_ad8antr $f wff si $.
	f8_ad8antr $f wff rh $.
	f9_ad8antr $f wff mu $.
	e0_ad8antr $e |- ( ph -> ps ) $.
	p_ad8antr $p |- ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $= e0_ad8antr f0_ad8antr f1_ad8antr f2_ad8antr f3_ad8antr f4_ad8antr f5_ad8antr f6_ad8antr f7_ad8antr f8_ad8antr p_ad7antr f0_ad8antr f2_ad8antr a_wa f3_ad8antr a_wa f4_ad8antr a_wa f5_ad8antr a_wa f6_ad8antr a_wa f7_ad8antr a_wa f8_ad8antr a_wa f1_ad8antr f9_ad8antr p_adantr $.
$}

$(Deduction adding 8 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu  $.
	f0_ad8antlr $f wff ph $.
	f1_ad8antlr $f wff ps $.
	f2_ad8antlr $f wff ch $.
	f3_ad8antlr $f wff th $.
	f4_ad8antlr $f wff ta $.
	f5_ad8antlr $f wff et $.
	f6_ad8antlr $f wff ze $.
	f7_ad8antlr $f wff si $.
	f8_ad8antlr $f wff rh $.
	f9_ad8antlr $f wff mu $.
	e0_ad8antlr $e |- ( ph -> ps ) $.
	p_ad8antlr $p |- ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $= e0_ad8antlr f0_ad8antlr f1_ad8antlr f2_ad8antlr f3_ad8antlr f4_ad8antlr f5_ad8antlr f6_ad8antlr f7_ad8antlr f8_ad8antlr p_ad7antlr f2_ad8antlr f0_ad8antlr a_wa f3_ad8antlr a_wa f4_ad8antlr a_wa f5_ad8antlr a_wa f6_ad8antlr a_wa f7_ad8antlr a_wa f8_ad8antlr a_wa f1_ad8antlr f9_ad8antlr p_adantr $.
$}

$(Deduction adding 9 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu la  $.
	f0_ad9antr $f wff ph $.
	f1_ad9antr $f wff ps $.
	f2_ad9antr $f wff ch $.
	f3_ad9antr $f wff th $.
	f4_ad9antr $f wff ta $.
	f5_ad9antr $f wff et $.
	f6_ad9antr $f wff ze $.
	f7_ad9antr $f wff si $.
	f8_ad9antr $f wff rh $.
	f9_ad9antr $f wff mu $.
	f10_ad9antr $f wff la $.
	e0_ad9antr $e |- ( ph -> ps ) $.
	p_ad9antr $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $= e0_ad9antr f0_ad9antr f1_ad9antr f2_ad9antr f3_ad9antr f4_ad9antr f5_ad9antr f6_ad9antr f7_ad9antr f8_ad9antr f9_ad9antr p_ad8antr f0_ad9antr f2_ad9antr a_wa f3_ad9antr a_wa f4_ad9antr a_wa f5_ad9antr a_wa f6_ad9antr a_wa f7_ad9antr a_wa f8_ad9antr a_wa f9_ad9antr a_wa f1_ad9antr f10_ad9antr p_adantr $.
$}

$(Deduction adding 9 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu la  $.
	f0_ad9antlr $f wff ph $.
	f1_ad9antlr $f wff ps $.
	f2_ad9antlr $f wff ch $.
	f3_ad9antlr $f wff th $.
	f4_ad9antlr $f wff ta $.
	f5_ad9antlr $f wff et $.
	f6_ad9antlr $f wff ze $.
	f7_ad9antlr $f wff si $.
	f8_ad9antlr $f wff rh $.
	f9_ad9antlr $f wff mu $.
	f10_ad9antlr $f wff la $.
	e0_ad9antlr $e |- ( ph -> ps ) $.
	p_ad9antlr $p |- ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $= e0_ad9antlr f0_ad9antlr f1_ad9antlr f2_ad9antlr f3_ad9antlr f4_ad9antlr f5_ad9antlr f6_ad9antlr f7_ad9antlr f8_ad9antlr f9_ad9antlr p_ad8antlr f2_ad9antlr f0_ad9antlr a_wa f3_ad9antlr a_wa f4_ad9antlr a_wa f5_ad9antlr a_wa f6_ad9antlr a_wa f7_ad9antlr a_wa f8_ad9antlr a_wa f9_ad9antlr a_wa f1_ad9antlr f10_ad9antlr p_adantr $.
$}

$(Deduction adding 10 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu la ka  $.
	f0_ad10antr $f wff ph $.
	f1_ad10antr $f wff ps $.
	f2_ad10antr $f wff ch $.
	f3_ad10antr $f wff th $.
	f4_ad10antr $f wff ta $.
	f5_ad10antr $f wff et $.
	f6_ad10antr $f wff ze $.
	f7_ad10antr $f wff si $.
	f8_ad10antr $f wff rh $.
	f9_ad10antr $f wff mu $.
	f10_ad10antr $f wff la $.
	f11_ad10antr $f wff ka $.
	e0_ad10antr $e |- ( ph -> ps ) $.
	p_ad10antr $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $= e0_ad10antr f0_ad10antr f1_ad10antr f2_ad10antr f3_ad10antr f4_ad10antr f5_ad10antr f6_ad10antr f7_ad10antr f8_ad10antr f9_ad10antr f10_ad10antr p_ad9antr f0_ad10antr f2_ad10antr a_wa f3_ad10antr a_wa f4_ad10antr a_wa f5_ad10antr a_wa f6_ad10antr a_wa f7_ad10antr a_wa f8_ad10antr a_wa f9_ad10antr a_wa f10_ad10antr a_wa f1_ad10antr f11_ad10antr p_adantr $.
$}

$(Deduction adding 10 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu la ka  $.
	f0_ad10antlr $f wff ph $.
	f1_ad10antlr $f wff ps $.
	f2_ad10antlr $f wff ch $.
	f3_ad10antlr $f wff th $.
	f4_ad10antlr $f wff ta $.
	f5_ad10antlr $f wff et $.
	f6_ad10antlr $f wff ze $.
	f7_ad10antlr $f wff si $.
	f8_ad10antlr $f wff rh $.
	f9_ad10antlr $f wff mu $.
	f10_ad10antlr $f wff la $.
	f11_ad10antlr $f wff ka $.
	e0_ad10antlr $e |- ( ph -> ps ) $.
	p_ad10antlr $p |- ( ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $= e0_ad10antlr f0_ad10antlr f1_ad10antlr f2_ad10antlr f3_ad10antlr f4_ad10antlr f5_ad10antlr f6_ad10antlr f7_ad10antlr f8_ad10antlr f9_ad10antlr f10_ad10antlr p_ad9antlr f2_ad10antlr f0_ad10antlr a_wa f3_ad10antlr a_wa f4_ad10antlr a_wa f5_ad10antlr a_wa f6_ad10antlr a_wa f7_ad10antlr a_wa f8_ad10antlr a_wa f9_ad10antlr a_wa f10_ad10antlr a_wa f1_ad10antlr f11_ad10antlr p_adantr $.
$}

$(Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_ad2ant2l $f wff ph $.
	f1_ad2ant2l $f wff ps $.
	f2_ad2ant2l $f wff ch $.
	f3_ad2ant2l $f wff th $.
	f4_ad2ant2l $f wff ta $.
	e0_ad2ant2l $e |- ( ( ph /\ ps ) -> ch ) $.
	p_ad2ant2l $p |- ( ( ( th /\ ph ) /\ ( ta /\ ps ) ) -> ch ) $= e0_ad2ant2l f0_ad2ant2l f1_ad2ant2l f2_ad2ant2l f4_ad2ant2l p_adantrl f0_ad2ant2l f4_ad2ant2l f1_ad2ant2l a_wa f2_ad2ant2l f3_ad2ant2l p_adantll $.
$}

$(Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_ad2ant2r $f wff ph $.
	f1_ad2ant2r $f wff ps $.
	f2_ad2ant2r $f wff ch $.
	f3_ad2ant2r $f wff th $.
	f4_ad2ant2r $f wff ta $.
	e0_ad2ant2r $e |- ( ( ph /\ ps ) -> ch ) $.
	p_ad2ant2r $p |- ( ( ( ph /\ th ) /\ ( ps /\ ta ) ) -> ch ) $= e0_ad2ant2r f0_ad2ant2r f1_ad2ant2r f2_ad2ant2r f4_ad2ant2r p_adantrr f0_ad2ant2r f1_ad2ant2r f4_ad2ant2r a_wa f2_ad2ant2r f3_ad2ant2r p_adantlr $.
$}

$(Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       23-Nov-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_ad2ant2lr $f wff ph $.
	f1_ad2ant2lr $f wff ps $.
	f2_ad2ant2lr $f wff ch $.
	f3_ad2ant2lr $f wff th $.
	f4_ad2ant2lr $f wff ta $.
	e0_ad2ant2lr $e |- ( ( ph /\ ps ) -> ch ) $.
	p_ad2ant2lr $p |- ( ( ( th /\ ph ) /\ ( ps /\ ta ) ) -> ch ) $= e0_ad2ant2lr f0_ad2ant2lr f1_ad2ant2lr f2_ad2ant2lr f4_ad2ant2lr p_adantrr f0_ad2ant2lr f1_ad2ant2lr f4_ad2ant2lr a_wa f2_ad2ant2lr f3_ad2ant2lr p_adantll $.
$}

$(Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       24-Nov-2007.) $)

${
	$v ph ps ch th ta  $.
	f0_ad2ant2rl $f wff ph $.
	f1_ad2ant2rl $f wff ps $.
	f2_ad2ant2rl $f wff ch $.
	f3_ad2ant2rl $f wff th $.
	f4_ad2ant2rl $f wff ta $.
	e0_ad2ant2rl $e |- ( ( ph /\ ps ) -> ch ) $.
	p_ad2ant2rl $p |- ( ( ( ph /\ th ) /\ ( ta /\ ps ) ) -> ch ) $= e0_ad2ant2rl f0_ad2ant2rl f1_ad2ant2rl f2_ad2ant2rl f4_ad2ant2rl p_adantrl f0_ad2ant2rl f4_ad2ant2rl f1_ad2ant2rl a_wa f2_ad2ant2rl f3_ad2ant2rl p_adantlr $.
$}

$(Simplification of a conjunction.  (Contributed by NM, 18-Mar-2007.) $)

${
	$v ph ps ch  $.
	f0_simpll $f wff ph $.
	f1_simpll $f wff ps $.
	f2_simpll $f wff ch $.
	p_simpll $p |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $= f0_simpll p_id f0_simpll f0_simpll f1_simpll f2_simpll p_ad2antrr $.
$}

$(Simplification of a conjunction.  (Contributed by NM, 20-Mar-2007.) $)

${
	$v ph ps ch  $.
	f0_simplr $f wff ph $.
	f1_simplr $f wff ps $.
	f2_simplr $f wff ch $.
	p_simplr $p |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $= f1_simplr p_id f1_simplr f1_simplr f0_simplr f2_simplr p_ad2antlr $.
$}

$(Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)

${
	$v ph ps ch  $.
	f0_simprl $f wff ph $.
	f1_simprl $f wff ps $.
	f2_simprl $f wff ch $.
	p_simprl $p |- ( ( ph /\ ( ps /\ ch ) ) -> ps ) $= f1_simprl p_id f1_simprl f1_simprl f0_simprl f2_simprl p_ad2antrl $.
$}

$(Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)

${
	$v ph ps ch  $.
	f0_simprr $f wff ph $.
	f1_simprr $f wff ps $.
	f2_simprr $f wff ch $.
	p_simprr $p |- ( ( ph /\ ( ps /\ ch ) ) -> ch ) $= f2_simprr p_id f2_simprr f2_simprr f0_simprr f1_simprr p_ad2antll $.
$}

$(Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_simplll $f wff ph $.
	f1_simplll $f wff ps $.
	f2_simplll $f wff ch $.
	f3_simplll $f wff th $.
	p_simplll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ph ) $= f0_simplll f1_simplll p_simpl f0_simplll f1_simplll a_wa f0_simplll f2_simplll f3_simplll p_ad2antrr $.
$}

$(Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_simpllr $f wff ph $.
	f1_simpllr $f wff ps $.
	f2_simpllr $f wff ch $.
	f3_simpllr $f wff th $.
	p_simpllr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ps ) $= f0_simpllr f1_simpllr p_simpr f0_simpllr f1_simpllr a_wa f1_simpllr f2_simpllr f3_simpllr p_ad2antrr $.
$}

$(Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_simplrl $f wff ph $.
	f1_simplrl $f wff ps $.
	f2_simplrl $f wff ch $.
	f3_simplrl $f wff th $.
	p_simplrl $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ps ) $= f1_simplrl f2_simplrl p_simpl f1_simplrl f2_simplrl a_wa f1_simplrl f0_simplrl f3_simplrl p_ad2antlr $.
$}

$(Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_simplrr $f wff ph $.
	f1_simplrr $f wff ps $.
	f2_simplrr $f wff ch $.
	f3_simplrr $f wff th $.
	p_simplrr $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ch ) $= f1_simplrr f2_simplrr p_simpr f1_simplrr f2_simplrr a_wa f2_simplrr f0_simplrr f3_simplrr p_ad2antlr $.
$}

$(Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_simprll $f wff ph $.
	f1_simprll $f wff ps $.
	f2_simprll $f wff ch $.
	f3_simprll $f wff th $.
	p_simprll $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ps ) $= f1_simprll f2_simprll p_simpl f1_simprll f2_simprll a_wa f1_simprll f0_simprll f3_simprll p_ad2antrl $.
$}

$(Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_simprlr $f wff ph $.
	f1_simprlr $f wff ps $.
	f2_simprlr $f wff ch $.
	f3_simprlr $f wff th $.
	p_simprlr $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ch ) $= f1_simprlr f2_simprlr p_simpr f1_simprlr f2_simprlr a_wa f2_simprlr f0_simprlr f3_simprlr p_ad2antrl $.
$}

$(Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_simprrl $f wff ph $.
	f1_simprrl $f wff ps $.
	f2_simprrl $f wff ch $.
	f3_simprrl $f wff th $.
	p_simprrl $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ch ) $= f2_simprrl f3_simprrl p_simpl f2_simprrl f3_simprrl a_wa f2_simprrl f0_simprrl f1_simprrl p_ad2antll $.
$}

$(Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)

${
	$v ph ps ch th  $.
	f0_simprrr $f wff ph $.
	f1_simprrr $f wff ps $.
	f2_simprrr $f wff ch $.
	f3_simprrr $f wff th $.
	p_simprrr $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> th ) $= f2_simprrr f3_simprrr p_simpr f2_simprrr f3_simprrr a_wa f3_simprrr f0_simprrr f1_simprrr p_ad2antll $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta  $.
	f0_simp-4l $f wff ph $.
	f1_simp-4l $f wff ps $.
	f2_simp-4l $f wff ch $.
	f3_simp-4l $f wff th $.
	f4_simp-4l $f wff ta $.
	p_simp-4l $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ph ) $= f0_simp-4l f1_simp-4l f2_simp-4l f3_simp-4l p_simplll f0_simp-4l f1_simp-4l a_wa f2_simp-4l a_wa f3_simp-4l a_wa f0_simp-4l f4_simp-4l p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta  $.
	f0_simp-4r $f wff ph $.
	f1_simp-4r $f wff ps $.
	f2_simp-4r $f wff ch $.
	f3_simp-4r $f wff th $.
	f4_simp-4r $f wff ta $.
	p_simp-4r $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ps ) $= f0_simp-4r f1_simp-4r f2_simp-4r f3_simp-4r p_simpllr f0_simp-4r f1_simp-4r a_wa f2_simp-4r a_wa f3_simp-4r a_wa f1_simp-4r f4_simp-4r p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp-5l $f wff ph $.
	f1_simp-5l $f wff ps $.
	f2_simp-5l $f wff ch $.
	f3_simp-5l $f wff th $.
	f4_simp-5l $f wff ta $.
	f5_simp-5l $f wff et $.
	p_simp-5l $p |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) -> ph ) $= f0_simp-5l f1_simp-5l f2_simp-5l f3_simp-5l f4_simp-5l p_simp-4l f0_simp-5l f1_simp-5l a_wa f2_simp-5l a_wa f3_simp-5l a_wa f4_simp-5l a_wa f0_simp-5l f5_simp-5l p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et  $.
	f0_simp-5r $f wff ph $.
	f1_simp-5r $f wff ps $.
	f2_simp-5r $f wff ch $.
	f3_simp-5r $f wff th $.
	f4_simp-5r $f wff ta $.
	f5_simp-5r $f wff et $.
	p_simp-5r $p |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) -> ps ) $= f0_simp-5r f1_simp-5r f2_simp-5r f3_simp-5r f4_simp-5r p_simp-4r f0_simp-5r f1_simp-5r a_wa f2_simp-5r a_wa f3_simp-5r a_wa f4_simp-5r a_wa f1_simp-5r f5_simp-5r p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp-6l $f wff ph $.
	f1_simp-6l $f wff ps $.
	f2_simp-6l $f wff ch $.
	f3_simp-6l $f wff th $.
	f4_simp-6l $f wff ta $.
	f5_simp-6l $f wff et $.
	f6_simp-6l $f wff ze $.
	p_simp-6l $p |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ph ) $= f0_simp-6l f1_simp-6l f2_simp-6l f3_simp-6l f4_simp-6l f5_simp-6l p_simp-5l f0_simp-6l f1_simp-6l a_wa f2_simp-6l a_wa f3_simp-6l a_wa f4_simp-6l a_wa f5_simp-6l a_wa f0_simp-6l f6_simp-6l p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_simp-6r $f wff ph $.
	f1_simp-6r $f wff ps $.
	f2_simp-6r $f wff ch $.
	f3_simp-6r $f wff th $.
	f4_simp-6r $f wff ta $.
	f5_simp-6r $f wff et $.
	f6_simp-6r $f wff ze $.
	p_simp-6r $p |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ps ) $= f0_simp-6r f1_simp-6r f2_simp-6r f3_simp-6r f4_simp-6r f5_simp-6r p_simp-5r f0_simp-6r f1_simp-6r a_wa f2_simp-6r a_wa f3_simp-6r a_wa f4_simp-6r a_wa f5_simp-6r a_wa f1_simp-6r f6_simp-6r p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_simp-7l $f wff ph $.
	f1_simp-7l $f wff ps $.
	f2_simp-7l $f wff ch $.
	f3_simp-7l $f wff th $.
	f4_simp-7l $f wff ta $.
	f5_simp-7l $f wff et $.
	f6_simp-7l $f wff ze $.
	f7_simp-7l $f wff si $.
	p_simp-7l $p |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ph ) $= f0_simp-7l f1_simp-7l f2_simp-7l f3_simp-7l f4_simp-7l f5_simp-7l f6_simp-7l p_simp-6l f0_simp-7l f1_simp-7l a_wa f2_simp-7l a_wa f3_simp-7l a_wa f4_simp-7l a_wa f5_simp-7l a_wa f6_simp-7l a_wa f0_simp-7l f7_simp-7l p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si  $.
	f0_simp-7r $f wff ph $.
	f1_simp-7r $f wff ps $.
	f2_simp-7r $f wff ch $.
	f3_simp-7r $f wff th $.
	f4_simp-7r $f wff ta $.
	f5_simp-7r $f wff et $.
	f6_simp-7r $f wff ze $.
	f7_simp-7r $f wff si $.
	p_simp-7r $p |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps ) $= f0_simp-7r f1_simp-7r f2_simp-7r f3_simp-7r f4_simp-7r f5_simp-7r f6_simp-7r p_simp-6r f0_simp-7r f1_simp-7r a_wa f2_simp-7r a_wa f3_simp-7r a_wa f4_simp-7r a_wa f5_simp-7r a_wa f6_simp-7r a_wa f1_simp-7r f7_simp-7r p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_simp-8l $f wff ph $.
	f1_simp-8l $f wff ps $.
	f2_simp-8l $f wff ch $.
	f3_simp-8l $f wff th $.
	f4_simp-8l $f wff ta $.
	f5_simp-8l $f wff et $.
	f6_simp-8l $f wff ze $.
	f7_simp-8l $f wff si $.
	f8_simp-8l $f wff rh $.
	p_simp-8l $p |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ph ) $= f0_simp-8l f1_simp-8l f2_simp-8l f3_simp-8l f4_simp-8l f5_simp-8l f6_simp-8l f7_simp-8l p_simp-7l f0_simp-8l f1_simp-8l a_wa f2_simp-8l a_wa f3_simp-8l a_wa f4_simp-8l a_wa f5_simp-8l a_wa f6_simp-8l a_wa f7_simp-8l a_wa f0_simp-8l f8_simp-8l p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh  $.
	f0_simp-8r $f wff ph $.
	f1_simp-8r $f wff ps $.
	f2_simp-8r $f wff ch $.
	f3_simp-8r $f wff th $.
	f4_simp-8r $f wff ta $.
	f5_simp-8r $f wff et $.
	f6_simp-8r $f wff ze $.
	f7_simp-8r $f wff si $.
	f8_simp-8r $f wff rh $.
	p_simp-8r $p |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps ) $= f0_simp-8r f1_simp-8r f2_simp-8r f3_simp-8r f4_simp-8r f5_simp-8r f6_simp-8r f7_simp-8r p_simp-7r f0_simp-8r f1_simp-8r a_wa f2_simp-8r a_wa f3_simp-8r a_wa f4_simp-8r a_wa f5_simp-8r a_wa f6_simp-8r a_wa f7_simp-8r a_wa f1_simp-8r f8_simp-8r p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu  $.
	f0_simp-9l $f wff ph $.
	f1_simp-9l $f wff ps $.
	f2_simp-9l $f wff ch $.
	f3_simp-9l $f wff th $.
	f4_simp-9l $f wff ta $.
	f5_simp-9l $f wff et $.
	f6_simp-9l $f wff ze $.
	f7_simp-9l $f wff si $.
	f8_simp-9l $f wff rh $.
	f9_simp-9l $f wff mu $.
	p_simp-9l $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ph ) $= f0_simp-9l f1_simp-9l f2_simp-9l f3_simp-9l f4_simp-9l f5_simp-9l f6_simp-9l f7_simp-9l f8_simp-9l p_simp-8l f0_simp-9l f1_simp-9l a_wa f2_simp-9l a_wa f3_simp-9l a_wa f4_simp-9l a_wa f5_simp-9l a_wa f6_simp-9l a_wa f7_simp-9l a_wa f8_simp-9l a_wa f0_simp-9l f9_simp-9l p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu  $.
	f0_simp-9r $f wff ph $.
	f1_simp-9r $f wff ps $.
	f2_simp-9r $f wff ch $.
	f3_simp-9r $f wff th $.
	f4_simp-9r $f wff ta $.
	f5_simp-9r $f wff et $.
	f6_simp-9r $f wff ze $.
	f7_simp-9r $f wff si $.
	f8_simp-9r $f wff rh $.
	f9_simp-9r $f wff mu $.
	p_simp-9r $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $= f0_simp-9r f1_simp-9r f2_simp-9r f3_simp-9r f4_simp-9r f5_simp-9r f6_simp-9r f7_simp-9r f8_simp-9r p_simp-8r f0_simp-9r f1_simp-9r a_wa f2_simp-9r a_wa f3_simp-9r a_wa f4_simp-9r a_wa f5_simp-9r a_wa f6_simp-9r a_wa f7_simp-9r a_wa f8_simp-9r a_wa f1_simp-9r f9_simp-9r p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu la  $.
	f0_simp-10l $f wff ph $.
	f1_simp-10l $f wff ps $.
	f2_simp-10l $f wff ch $.
	f3_simp-10l $f wff th $.
	f4_simp-10l $f wff ta $.
	f5_simp-10l $f wff et $.
	f6_simp-10l $f wff ze $.
	f7_simp-10l $f wff si $.
	f8_simp-10l $f wff rh $.
	f9_simp-10l $f wff mu $.
	f10_simp-10l $f wff la $.
	p_simp-10l $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ph ) $= f0_simp-10l f1_simp-10l f2_simp-10l f3_simp-10l f4_simp-10l f5_simp-10l f6_simp-10l f7_simp-10l f8_simp-10l f9_simp-10l p_simp-9l f0_simp-10l f1_simp-10l a_wa f2_simp-10l a_wa f3_simp-10l a_wa f4_simp-10l a_wa f5_simp-10l a_wa f6_simp-10l a_wa f7_simp-10l a_wa f8_simp-10l a_wa f9_simp-10l a_wa f0_simp-10l f10_simp-10l p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu la  $.
	f0_simp-10r $f wff ph $.
	f1_simp-10r $f wff ps $.
	f2_simp-10r $f wff ch $.
	f3_simp-10r $f wff th $.
	f4_simp-10r $f wff ta $.
	f5_simp-10r $f wff et $.
	f6_simp-10r $f wff ze $.
	f7_simp-10r $f wff si $.
	f8_simp-10r $f wff rh $.
	f9_simp-10r $f wff mu $.
	f10_simp-10r $f wff la $.
	p_simp-10r $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $= f0_simp-10r f1_simp-10r f2_simp-10r f3_simp-10r f4_simp-10r f5_simp-10r f6_simp-10r f7_simp-10r f8_simp-10r f9_simp-10r p_simp-9r f0_simp-10r f1_simp-10r a_wa f2_simp-10r a_wa f3_simp-10r a_wa f4_simp-10r a_wa f5_simp-10r a_wa f6_simp-10r a_wa f7_simp-10r a_wa f8_simp-10r a_wa f9_simp-10r a_wa f1_simp-10r f10_simp-10r p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu la ka  $.
	f0_simp-11l $f wff ph $.
	f1_simp-11l $f wff ps $.
	f2_simp-11l $f wff ch $.
	f3_simp-11l $f wff th $.
	f4_simp-11l $f wff ta $.
	f5_simp-11l $f wff et $.
	f6_simp-11l $f wff ze $.
	f7_simp-11l $f wff si $.
	f8_simp-11l $f wff rh $.
	f9_simp-11l $f wff mu $.
	f10_simp-11l $f wff la $.
	f11_simp-11l $f wff ka $.
	p_simp-11l $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ph ) $= f0_simp-11l f1_simp-11l f2_simp-11l f3_simp-11l f4_simp-11l f5_simp-11l f6_simp-11l f7_simp-11l f8_simp-11l f9_simp-11l f10_simp-11l p_simp-10l f0_simp-11l f1_simp-11l a_wa f2_simp-11l a_wa f3_simp-11l a_wa f4_simp-11l a_wa f5_simp-11l a_wa f6_simp-11l a_wa f7_simp-11l a_wa f8_simp-11l a_wa f9_simp-11l a_wa f10_simp-11l a_wa f0_simp-11l f11_simp-11l p_adantr $.
$}

$(Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)

${
	$v ph ps ch th ta et ze si rh mu la ka  $.
	f0_simp-11r $f wff ph $.
	f1_simp-11r $f wff ps $.
	f2_simp-11r $f wff ch $.
	f3_simp-11r $f wff th $.
	f4_simp-11r $f wff ta $.
	f5_simp-11r $f wff et $.
	f6_simp-11r $f wff ze $.
	f7_simp-11r $f wff si $.
	f8_simp-11r $f wff rh $.
	f9_simp-11r $f wff mu $.
	f10_simp-11r $f wff la $.
	f11_simp-11r $f wff ka $.
	p_simp-11r $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $= f0_simp-11r f1_simp-11r f2_simp-11r f3_simp-11r f4_simp-11r f5_simp-11r f6_simp-11r f7_simp-11r f8_simp-11r f9_simp-11r f10_simp-11r p_simp-10r f0_simp-11r f1_simp-11r a_wa f2_simp-11r a_wa f3_simp-11r a_wa f4_simp-11r a_wa f5_simp-11r a_wa f6_simp-11r a_wa f7_simp-11r a_wa f8_simp-11r a_wa f9_simp-11r a_wa f10_simp-11r a_wa f1_simp-11r f11_simp-11r p_adantr $.
$}

$(Disjunction of antecedents.  Compare Theorem *4.77 of [WhiteheadRussell]
     p. 121.  (Contributed by NM, 30-May-1994.)  (Proof shortened by Wolf
     Lammen, 9-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_jaob $f wff ph $.
	f1_jaob $f wff ps $.
	f2_jaob $f wff ch $.
	p_jaob $p |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $= f0_jaob f1_jaob f2_jaob p_pm2.67-2 f2_jaob f0_jaob p_olc f2_jaob f0_jaob f2_jaob a_wo f1_jaob p_imim1i f0_jaob f2_jaob a_wo f1_jaob a_wi f0_jaob f1_jaob a_wi f2_jaob f1_jaob a_wi p_jca f1_jaob f0_jaob f2_jaob p_pm3.44 f0_jaob f2_jaob a_wo f1_jaob a_wi f0_jaob f1_jaob a_wi f2_jaob f1_jaob a_wi a_wa p_impbii $.
$}

$(Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 23-Oct-2005.) $)

${
	$v ph ps ch th  $.
	f0_jaoian $f wff ph $.
	f1_jaoian $f wff ps $.
	f2_jaoian $f wff ch $.
	f3_jaoian $f wff th $.
	e0_jaoian $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_jaoian $e |- ( ( th /\ ps ) -> ch ) $.
	p_jaoian $p |- ( ( ( ph \/ th ) /\ ps ) -> ch ) $= e0_jaoian f0_jaoian f1_jaoian f2_jaoian p_ex e1_jaoian f3_jaoian f1_jaoian f2_jaoian p_ex f0_jaoian f1_jaoian f2_jaoian a_wi f3_jaoian p_jaoi f0_jaoian f3_jaoian a_wo f1_jaoian f2_jaoian p_imp $.
$}

$(Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 14-Oct-2005.) $)

${
	$v ph ps ch th  $.
	f0_jaodan $f wff ph $.
	f1_jaodan $f wff ps $.
	f2_jaodan $f wff ch $.
	f3_jaodan $f wff th $.
	e0_jaodan $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_jaodan $e |- ( ( ph /\ th ) -> ch ) $.
	p_jaodan $p |- ( ( ph /\ ( ps \/ th ) ) -> ch ) $= e0_jaodan f0_jaodan f1_jaodan f2_jaodan p_ex e1_jaodan f0_jaodan f3_jaodan f2_jaodan p_ex f0_jaodan f1_jaodan f2_jaodan f3_jaodan p_jaod f0_jaodan f1_jaodan f3_jaodan a_wo f2_jaodan p_imp $.
$}

$(Eliminate a disjunction in a deduction.  A translation of natural
       deduction rule ` \/ ` E ( ` \/ ` elimination), see ~ natded .
       (Contributed by Mario Carneiro, 29-May-2016.) $)

${
	$v ph ps ch th  $.
	f0_mpjaodan $f wff ph $.
	f1_mpjaodan $f wff ps $.
	f2_mpjaodan $f wff ch $.
	f3_mpjaodan $f wff th $.
	e0_mpjaodan $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_mpjaodan $e |- ( ( ph /\ th ) -> ch ) $.
	e2_mpjaodan $e |- ( ph -> ( ps \/ th ) ) $.
	p_mpjaodan $p |- ( ph -> ch ) $= e2_mpjaodan e0_mpjaodan e1_mpjaodan f0_mpjaodan f1_mpjaodan f2_mpjaodan f3_mpjaodan p_jaodan f0_mpjaodan f1_mpjaodan f3_mpjaodan a_wo f2_mpjaodan p_mpdan $.
$}

$(Theorem *4.77 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm4.77 $f wff ph $.
	f1_pm4.77 $f wff ps $.
	f2_pm4.77 $f wff ch $.
	p_pm4.77 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) <-> ( ( ps \/ ch ) -> ph ) ) $= f1_pm4.77 f0_pm4.77 f2_pm4.77 p_jaob f1_pm4.77 f2_pm4.77 a_wo f0_pm4.77 a_wi f1_pm4.77 f0_pm4.77 a_wi f2_pm4.77 f0_pm4.77 a_wi a_wa p_bicomi $.
$}

$(Theorem *2.63 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.63 $f wff ph $.
	f1_pm2.63 $f wff ps $.
	p_pm2.63 $p |- ( ( ph \/ ps ) -> ( ( -. ph \/ ps ) -> ps ) ) $= f0_pm2.63 f1_pm2.63 p_pm2.53 f0_pm2.63 f1_pm2.63 a_wo f1_pm2.63 p_idd f0_pm2.63 f1_pm2.63 a_wo f0_pm2.63 a_wn f1_pm2.63 f1_pm2.63 p_jaod $.
$}

$(Theorem *2.64 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.64 $f wff ph $.
	f1_pm2.64 $f wff ps $.
	p_pm2.64 $p |- ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) ) $= f0_pm2.64 f0_pm2.64 f1_pm2.64 a_wo a_ax-1 f1_pm2.64 f0_pm2.64 p_orel2 f0_pm2.64 f0_pm2.64 f1_pm2.64 a_wo f0_pm2.64 a_wi f1_pm2.64 a_wn p_jaoi f0_pm2.64 f1_pm2.64 a_wn a_wo f0_pm2.64 f1_pm2.64 a_wo f0_pm2.64 p_com12 $.
$}

$(Elimination of an antecedent.  (Contributed by NM, 1-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.61ian $f wff ph $.
	f1_pm2.61ian $f wff ps $.
	f2_pm2.61ian $f wff ch $.
	e0_pm2.61ian $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_pm2.61ian $e |- ( ( -. ph /\ ps ) -> ch ) $.
	p_pm2.61ian $p |- ( ps -> ch ) $= e0_pm2.61ian f0_pm2.61ian f1_pm2.61ian f2_pm2.61ian p_ex e1_pm2.61ian f0_pm2.61ian a_wn f1_pm2.61ian f2_pm2.61ian p_ex f0_pm2.61ian f1_pm2.61ian f2_pm2.61ian a_wi p_pm2.61i $.
$}

$(Elimination of an antecedent.  (Contributed by NM, 1-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.61dan $f wff ph $.
	f1_pm2.61dan $f wff ps $.
	f2_pm2.61dan $f wff ch $.
	e0_pm2.61dan $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_pm2.61dan $e |- ( ( ph /\ -. ps ) -> ch ) $.
	p_pm2.61dan $p |- ( ph -> ch ) $= e0_pm2.61dan f0_pm2.61dan f1_pm2.61dan f2_pm2.61dan p_ex e1_pm2.61dan f0_pm2.61dan f1_pm2.61dan a_wn f2_pm2.61dan p_ex f0_pm2.61dan f1_pm2.61dan f2_pm2.61dan p_pm2.61d $.
$}

$(Elimination of two antecedents.  (Contributed by NM, 9-Jul-2013.) $)

${
	$v ph ps ch th  $.
	f0_pm2.61ddan $f wff ph $.
	f1_pm2.61ddan $f wff ps $.
	f2_pm2.61ddan $f wff ch $.
	f3_pm2.61ddan $f wff th $.
	e0_pm2.61ddan $e |- ( ( ph /\ ps ) -> th ) $.
	e1_pm2.61ddan $e |- ( ( ph /\ ch ) -> th ) $.
	e2_pm2.61ddan $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
	p_pm2.61ddan $p |- ( ph -> th ) $= e0_pm2.61ddan e1_pm2.61ddan f0_pm2.61ddan f2_pm2.61ddan f3_pm2.61ddan f1_pm2.61ddan a_wn p_adantlr e2_pm2.61ddan f0_pm2.61ddan f1_pm2.61ddan a_wn f2_pm2.61ddan a_wn f3_pm2.61ddan p_anassrs f0_pm2.61ddan f1_pm2.61ddan a_wn a_wa f2_pm2.61ddan f3_pm2.61ddan p_pm2.61dan f0_pm2.61ddan f1_pm2.61ddan f3_pm2.61ddan p_pm2.61dan $.
$}

$(Elimination of two antecedents.  (Contributed by NM, 9-Jul-2013.) $)

${
	$v ph ps ch th  $.
	f0_pm2.61dda $f wff ph $.
	f1_pm2.61dda $f wff ps $.
	f2_pm2.61dda $f wff ch $.
	f3_pm2.61dda $f wff th $.
	e0_pm2.61dda $e |- ( ( ph /\ -. ps ) -> th ) $.
	e1_pm2.61dda $e |- ( ( ph /\ -. ch ) -> th ) $.
	e2_pm2.61dda $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_pm2.61dda $p |- ( ph -> th ) $= e2_pm2.61dda f0_pm2.61dda f1_pm2.61dda f2_pm2.61dda f3_pm2.61dda p_anassrs e1_pm2.61dda f0_pm2.61dda f2_pm2.61dda a_wn f3_pm2.61dda f1_pm2.61dda p_adantlr f0_pm2.61dda f1_pm2.61dda a_wa f2_pm2.61dda f3_pm2.61dda p_pm2.61dan e0_pm2.61dda f0_pm2.61dda f1_pm2.61dda f3_pm2.61dda p_pm2.61dan $.
$}

$(Proof by contradiction.  (Contributed by NM, 9-Feb-2006.)  (Proof
       shortened by Wolf Lammen, 19-Jun-2014.) $)

${
	$v ph ps ch  $.
	f0_condan $f wff ph $.
	f1_condan $f wff ps $.
	f2_condan $f wff ch $.
	e0_condan $e |- ( ( ph /\ -. ps ) -> ch ) $.
	e1_condan $e |- ( ( ph /\ -. ps ) -> -. ch ) $.
	p_condan $p |- ( ph -> ps ) $= e0_condan e1_condan f0_condan f1_condan a_wn f2_condan p_pm2.65da f1_condan p_notnot2 f0_condan f1_condan a_wn a_wn f1_condan p_syl $.
$}

$(Introduce one conjunct as an antecedent to the other.  "abai" stands for
     "and, biconditional, and, implication".  (Contributed by NM,
     12-Aug-1993.)  (Proof shortened by Wolf Lammen, 7-Dec-2012.) $)

${
	$v ph ps  $.
	f0_abai $f wff ph $.
	f1_abai $f wff ps $.
	p_abai $p |- ( ( ph /\ ps ) <-> ( ph /\ ( ph -> ps ) ) ) $= f0_abai f1_abai p_biimt f0_abai f1_abai f0_abai f1_abai a_wi p_pm5.32i $.
$}

$(Theorem *5.53 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch th  $.
	f0_pm5.53 $f wff ph $.
	f1_pm5.53 $f wff ps $.
	f2_pm5.53 $f wff ch $.
	f3_pm5.53 $f wff th $.
	p_pm5.53 $p |- ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <-> ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) ) $= f0_pm5.53 f1_pm5.53 a_wo f3_pm5.53 f2_pm5.53 p_jaob f0_pm5.53 f3_pm5.53 f1_pm5.53 p_jaob f0_pm5.53 f1_pm5.53 a_wo f3_pm5.53 a_wi f0_pm5.53 f3_pm5.53 a_wi f1_pm5.53 f3_pm5.53 a_wi a_wa f2_pm5.53 f3_pm5.53 a_wi p_anbi1i f0_pm5.53 f1_pm5.53 a_wo f2_pm5.53 a_wo f3_pm5.53 a_wi f0_pm5.53 f1_pm5.53 a_wo f3_pm5.53 a_wi f2_pm5.53 f3_pm5.53 a_wi a_wa f0_pm5.53 f3_pm5.53 a_wi f1_pm5.53 f3_pm5.53 a_wi a_wa f2_pm5.53 f3_pm5.53 a_wi a_wa p_bitri $.
$}

$(Swap two conjuncts.  Note that the first digit (1) in the label refers to
     the outer conjunct position, and the next digit (2) to the inner conjunct
     position.  (Contributed by NM, 12-Mar-1995.) $)

${
	$v ph ps ch  $.
	f0_an12 $f wff ph $.
	f1_an12 $f wff ps $.
	f2_an12 $f wff ch $.
	p_an12 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ps /\ ( ph /\ ch ) ) ) $= f0_an12 f1_an12 p_ancom f0_an12 f1_an12 a_wa f1_an12 f0_an12 a_wa f2_an12 p_anbi1i f0_an12 f1_an12 f2_an12 p_anass f1_an12 f0_an12 f2_an12 p_anass f0_an12 f1_an12 a_wa f2_an12 a_wa f1_an12 f0_an12 a_wa f2_an12 a_wa f0_an12 f1_an12 f2_an12 a_wa a_wa f1_an12 f0_an12 f2_an12 a_wa a_wa p_3bitr3i $.
$}

$(A rearrangement of conjuncts.  (Contributed by NM, 12-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 25-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_an32 $f wff ph $.
	f1_an32 $f wff ps $.
	f2_an32 $f wff ch $.
	p_an32 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $= f0_an32 f1_an32 f2_an32 p_anass f0_an32 f1_an32 f2_an32 p_an12 f1_an32 f0_an32 f2_an32 a_wa p_ancom f0_an32 f1_an32 a_wa f2_an32 a_wa f0_an32 f1_an32 f2_an32 a_wa a_wa f1_an32 f0_an32 f2_an32 a_wa a_wa f0_an32 f2_an32 a_wa f1_an32 a_wa p_3bitri $.
$}

$(A rearrangement of conjuncts.  (Contributed by NM, 24-Jun-2012.)  (Proof
     shortened by Wolf Lammen, 31-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_an13 $f wff ph $.
	f1_an13 $f wff ps $.
	f2_an13 $f wff ch $.
	p_an13 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ch /\ ( ps /\ ph ) ) ) $= f0_an13 f1_an13 f2_an13 p_an12 f1_an13 f0_an13 f2_an13 p_anass f1_an13 f0_an13 a_wa f2_an13 p_ancom f0_an13 f1_an13 f2_an13 a_wa a_wa f1_an13 f0_an13 f2_an13 a_wa a_wa f1_an13 f0_an13 a_wa f2_an13 a_wa f2_an13 f1_an13 f0_an13 a_wa a_wa p_3bitr2i $.
$}

$(A rearrangement of conjuncts.  (Contributed by NM, 24-Jun-2012.)  (Proof
     shortened by Wolf Lammen, 31-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_an31 $f wff ph $.
	f1_an31 $f wff ps $.
	f2_an31 $f wff ch $.
	p_an31 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps ) /\ ph ) ) $= f0_an31 f1_an31 f2_an31 p_an13 f0_an31 f1_an31 f2_an31 p_anass f2_an31 f1_an31 f0_an31 p_anass f0_an31 f1_an31 f2_an31 a_wa a_wa f2_an31 f1_an31 f0_an31 a_wa a_wa f0_an31 f1_an31 a_wa f2_an31 a_wa f2_an31 f1_an31 a_wa f0_an31 a_wa p_3bitr4i $.
$}

$(Swap two conjuncts in antecedent.  The label suffix "s" means that
       ~ an12 is combined with ~ syl (or a variant).  (Contributed by NM,
       13-Mar-1996.) $)

${
	$v ph ps ch th  $.
	f0_an12s $f wff ph $.
	f1_an12s $f wff ps $.
	f2_an12s $f wff ch $.
	f3_an12s $f wff th $.
	e0_an12s $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_an12s $p |- ( ( ps /\ ( ph /\ ch ) ) -> th ) $= f1_an12s f0_an12s f2_an12s p_an12 e0_an12s f1_an12s f0_an12s f2_an12s a_wa a_wa f0_an12s f1_an12s f2_an12s a_wa a_wa f3_an12s p_sylbi $.
$}

$(Inference commuting a nested conjunction in antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_ancom2s $f wff ph $.
	f1_ancom2s $f wff ps $.
	f2_ancom2s $f wff ch $.
	f3_ancom2s $f wff th $.
	e0_ancom2s $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_ancom2s $p |- ( ( ph /\ ( ch /\ ps ) ) -> th ) $= f2_ancom2s f1_ancom2s p_pm3.22 e0_ancom2s f2_ancom2s f1_ancom2s a_wa f0_ancom2s f1_ancom2s f2_ancom2s a_wa f3_ancom2s p_sylan2 $.
$}

$(Swap two conjuncts in antecedent.  (Contributed by NM, 31-May-2006.) $)

${
	$v ph ps ch th  $.
	f0_an13s $f wff ph $.
	f1_an13s $f wff ps $.
	f2_an13s $f wff ch $.
	f3_an13s $f wff th $.
	e0_an13s $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_an13s $p |- ( ( ch /\ ( ps /\ ph ) ) -> th ) $= e0_an13s f0_an13s f1_an13s f2_an13s f3_an13s p_exp32 f0_an13s f1_an13s f2_an13s f3_an13s p_com13 f2_an13s f1_an13s f0_an13s f3_an13s p_imp32 $.
$}

$(Swap two conjuncts in antecedent.  (Contributed by NM, 13-Mar-1996.) $)

${
	$v ph ps ch th  $.
	f0_an32s $f wff ph $.
	f1_an32s $f wff ps $.
	f2_an32s $f wff ch $.
	f3_an32s $f wff th $.
	e0_an32s $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_an32s $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $= f0_an32s f2_an32s f1_an32s p_an32 e0_an32s f0_an32s f2_an32s a_wa f1_an32s a_wa f0_an32s f1_an32s a_wa f2_an32s a_wa f3_an32s p_sylbi $.
$}

$(Inference commuting a nested conjunction in antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph ps ch th  $.
	f0_ancom1s $f wff ph $.
	f1_ancom1s $f wff ps $.
	f2_ancom1s $f wff ch $.
	f3_ancom1s $f wff th $.
	e0_ancom1s $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_ancom1s $p |- ( ( ( ps /\ ph ) /\ ch ) -> th ) $= f1_ancom1s f0_ancom1s p_pm3.22 e0_ancom1s f1_ancom1s f0_ancom1s a_wa f0_ancom1s f1_ancom1s a_wa f2_ancom1s f3_ancom1s p_sylan $.
$}

$(Swap two conjuncts in antecedent.  (Contributed by NM, 31-May-2006.) $)

${
	$v ph ps ch th  $.
	f0_an31s $f wff ph $.
	f1_an31s $f wff ps $.
	f2_an31s $f wff ch $.
	f3_an31s $f wff th $.
	e0_an31s $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	p_an31s $p |- ( ( ( ch /\ ps ) /\ ph ) -> th ) $= e0_an31s f0_an31s f1_an31s f2_an31s f3_an31s p_exp31 f0_an31s f1_an31s f2_an31s f3_an31s p_com13 f2_an31s f1_an31s f0_an31s f3_an31s p_imp31 $.
$}

$(Commutative-associative law for conjunction in an antecedent.
       (Contributed by Jeff Madsen, 19-Jun-2011.) $)

${
	$v ph ps ch th  $.
	f0_anass1rs $f wff ph $.
	f1_anass1rs $f wff ps $.
	f2_anass1rs $f wff ch $.
	f3_anass1rs $f wff th $.
	e0_anass1rs $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	p_anass1rs $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $= e0_anass1rs f0_anass1rs f1_anass1rs f2_anass1rs f3_anass1rs p_anassrs f0_anass1rs f1_anass1rs f2_anass1rs f3_anass1rs p_an32s $.
$}

$(Absorption into embedded conjunct.  (Contributed by NM, 4-Sep-1995.)
     (Proof shortened by Wolf Lammen, 16-Nov-2013.) $)

${
	$v ph ps  $.
	f0_anabs1 $f wff ph $.
	f1_anabs1 $f wff ps $.
	p_anabs1 $p |- ( ( ( ph /\ ps ) /\ ph ) <-> ( ph /\ ps ) ) $= f0_anabs1 f1_anabs1 p_simpl f0_anabs1 f1_anabs1 a_wa f0_anabs1 p_pm4.71i f0_anabs1 f1_anabs1 a_wa f0_anabs1 f1_anabs1 a_wa f0_anabs1 a_wa p_bicomi $.
$}

$(Absorption into embedded conjunct.  (Contributed by NM, 20-Jul-1996.)
     (Proof shortened by Wolf Lammen, 9-Dec-2012.) $)

${
	$v ph ps  $.
	f0_anabs5 $f wff ph $.
	f1_anabs5 $f wff ps $.
	p_anabs5 $p |- ( ( ph /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $= f0_anabs5 f1_anabs5 p_ibar f0_anabs5 f1_anabs5 f0_anabs5 f1_anabs5 a_wa p_bicomd f0_anabs5 f0_anabs5 f1_anabs5 a_wa f1_anabs5 p_pm5.32i $.
$}

$(Absorption into embedded conjunct.  (Contributed by NM, 20-Jul-1996.)
     (Proof shortened by Wolf Lammen, 17-Nov-2013.) $)

${
	$v ph ps  $.
	f0_anabs7 $f wff ph $.
	f1_anabs7 $f wff ps $.
	p_anabs7 $p |- ( ( ps /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $= f0_anabs7 f1_anabs7 p_simpr f0_anabs7 f1_anabs7 a_wa f1_anabs7 p_pm4.71ri f0_anabs7 f1_anabs7 a_wa f1_anabs7 f0_anabs7 f1_anabs7 a_wa a_wa p_bicomi $.
$}

$(Absorption of antecedent with conjunction.  (Contributed by NM,
       24-Mar-1996.) $)

${
	$v ph ps ch  $.
	f0_anabsan $f wff ph $.
	f1_anabsan $f wff ps $.
	f2_anabsan $f wff ch $.
	e0_anabsan $e |- ( ( ( ph /\ ph ) /\ ps ) -> ch ) $.
	p_anabsan $p |- ( ( ph /\ ps ) -> ch ) $= f0_anabsan p_pm4.24 e0_anabsan f0_anabsan f0_anabsan f0_anabsan a_wa f1_anabsan f2_anabsan p_sylanb $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 31-Dec-2012.) $)

${
	$v ph ps ch  $.
	f0_anabss1 $f wff ph $.
	f1_anabss1 $f wff ps $.
	f2_anabss1 $f wff ch $.
	e0_anabss1 $e |- ( ( ( ph /\ ps ) /\ ph ) -> ch ) $.
	p_anabss1 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabss1 f0_anabss1 f1_anabss1 f0_anabss1 f2_anabss1 p_an32s f0_anabss1 f1_anabss1 f2_anabss1 p_anabsan $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.) $)

${
	$v ph ps ch  $.
	f0_anabss4 $f wff ph $.
	f1_anabss4 $f wff ps $.
	f2_anabss4 $f wff ch $.
	e0_anabss4 $e |- ( ( ( ps /\ ph ) /\ ps ) -> ch ) $.
	p_anabss4 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabss4 f1_anabss4 f0_anabss4 f2_anabss4 p_anabss1 f1_anabss4 f0_anabss4 f2_anabss4 p_ancoms $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       10-May-1994.)  (Proof shortened by Wolf Lammen, 1-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_anabss5 $f wff ph $.
	f1_anabss5 $f wff ps $.
	f2_anabss5 $f wff ch $.
	e0_anabss5 $e |- ( ( ph /\ ( ph /\ ps ) ) -> ch ) $.
	p_anabss5 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabss5 f0_anabss5 f0_anabss5 f1_anabss5 f2_anabss5 p_anassrs f0_anabss5 f1_anabss5 f2_anabss5 p_anabsan $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       11-Jun-1995.)  (Proof shortened by Wolf Lammen, 18-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_anabsi5 $f wff ph $.
	f1_anabsi5 $f wff ps $.
	f2_anabsi5 $f wff ch $.
	e0_anabsi5 $e |- ( ph -> ( ( ph /\ ps ) -> ch ) ) $.
	p_anabsi5 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabsi5 f0_anabsi5 f0_anabsi5 f1_anabsi5 a_wa f2_anabsi5 p_imp f0_anabsi5 f1_anabsi5 f2_anabsi5 p_anabss5 $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       14-Aug-2000.) $)

${
	$v ph ps ch  $.
	f0_anabsi6 $f wff ph $.
	f1_anabsi6 $f wff ps $.
	f2_anabsi6 $f wff ch $.
	e0_anabsi6 $e |- ( ph -> ( ( ps /\ ph ) -> ch ) ) $.
	p_anabsi6 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabsi6 f0_anabsi6 f1_anabsi6 f0_anabsi6 f2_anabsi6 p_ancomsd f0_anabsi6 f1_anabsi6 f2_anabsi6 p_anabsi5 $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 18-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_anabsi7 $f wff ph $.
	f1_anabsi7 $f wff ps $.
	f2_anabsi7 $f wff ch $.
	e0_anabsi7 $e |- ( ps -> ( ( ph /\ ps ) -> ch ) ) $.
	p_anabsi7 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabsi7 f1_anabsi7 f0_anabsi7 f2_anabsi7 p_anabsi6 f1_anabsi7 f0_anabsi7 f2_anabsi7 p_ancoms $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       26-Sep-1999.) $)

${
	$v ph ps ch  $.
	f0_anabsi8 $f wff ph $.
	f1_anabsi8 $f wff ps $.
	f2_anabsi8 $f wff ch $.
	e0_anabsi8 $e |- ( ps -> ( ( ps /\ ph ) -> ch ) ) $.
	p_anabsi8 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabsi8 f1_anabsi8 f0_anabsi8 f2_anabsi8 p_anabsi5 f1_anabsi8 f0_anabsi8 f2_anabsi8 p_ancoms $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 19-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_anabss7 $f wff ph $.
	f1_anabss7 $f wff ps $.
	f2_anabss7 $f wff ch $.
	e0_anabss7 $e |- ( ( ps /\ ( ph /\ ps ) ) -> ch ) $.
	p_anabss7 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabss7 f1_anabss7 f0_anabss7 f1_anabss7 f2_anabss7 p_anassrs f0_anabss7 f1_anabss7 f2_anabss7 p_anabss4 $.
$}

$(Absorption of antecedent with conjunction.  (Contributed by NM,
       10-May-2004.) $)

${
	$v ph ps ch  $.
	f0_anabsan2 $f wff ph $.
	f1_anabsan2 $f wff ps $.
	f2_anabsan2 $f wff ch $.
	e0_anabsan2 $e |- ( ( ph /\ ( ps /\ ps ) ) -> ch ) $.
	p_anabsan2 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabsan2 f0_anabsan2 f1_anabsan2 f1_anabsan2 f2_anabsan2 p_an12s f0_anabsan2 f1_anabsan2 f2_anabsan2 p_anabss7 $.
$}

$(Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 1-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_anabss3 $f wff ph $.
	f1_anabss3 $f wff ps $.
	f2_anabss3 $f wff ch $.
	e0_anabss3 $e |- ( ( ( ph /\ ps ) /\ ps ) -> ch ) $.
	p_anabss3 $p |- ( ( ph /\ ps ) -> ch ) $= e0_anabss3 f0_anabss3 f1_anabss3 f1_anabss3 f2_anabss3 p_anasss f0_anabss3 f1_anabss3 f2_anabss3 p_anabsan2 $.
$}

$(Rearrangement of 4 conjuncts.  (Contributed by NM, 10-Jul-1994.) $)

${
	$v ph ps ch th  $.
	f0_an4 $f wff ph $.
	f1_an4 $f wff ps $.
	f2_an4 $f wff ch $.
	f3_an4 $f wff th $.
	p_an4 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ph /\ ch ) /\ ( ps /\ th ) ) ) $= f1_an4 f2_an4 f3_an4 p_an12 f1_an4 f2_an4 f3_an4 a_wa a_wa f2_an4 f1_an4 f3_an4 a_wa a_wa f0_an4 p_anbi2i f0_an4 f1_an4 f2_an4 f3_an4 a_wa p_anass f0_an4 f2_an4 f1_an4 f3_an4 a_wa p_anass f0_an4 f1_an4 f2_an4 f3_an4 a_wa a_wa a_wa f0_an4 f2_an4 f1_an4 f3_an4 a_wa a_wa a_wa f0_an4 f1_an4 a_wa f2_an4 f3_an4 a_wa a_wa f0_an4 f2_an4 a_wa f1_an4 f3_an4 a_wa a_wa p_3bitr4i $.
$}

$(Rearrangement of 4 conjuncts.  (Contributed by NM, 7-Feb-1996.) $)

${
	$v ph ps ch th  $.
	f0_an42 $f wff ph $.
	f1_an42 $f wff ps $.
	f2_an42 $f wff ch $.
	f3_an42 $f wff th $.
	p_an42 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ph /\ ch ) /\ ( th /\ ps ) ) ) $= f0_an42 f1_an42 f2_an42 f3_an42 p_an4 f1_an42 f3_an42 p_ancom f1_an42 f3_an42 a_wa f3_an42 f1_an42 a_wa f0_an42 f2_an42 a_wa p_anbi2i f0_an42 f1_an42 a_wa f2_an42 f3_an42 a_wa a_wa f0_an42 f2_an42 a_wa f1_an42 f3_an42 a_wa a_wa f0_an42 f2_an42 a_wa f3_an42 f1_an42 a_wa a_wa p_bitri $.
$}

$(Inference rearranging 4 conjuncts in antecedent.  (Contributed by NM,
       10-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_an4s $f wff ph $.
	f1_an4s $f wff ps $.
	f2_an4s $f wff ch $.
	f3_an4s $f wff th $.
	f4_an4s $f wff ta $.
	e0_an4s $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
	p_an4s $p |- ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) -> ta ) $= f0_an4s f2_an4s f1_an4s f3_an4s p_an4 e0_an4s f0_an4s f2_an4s a_wa f1_an4s f3_an4s a_wa a_wa f0_an4s f1_an4s a_wa f2_an4s f3_an4s a_wa a_wa f4_an4s p_sylbi $.
$}

$(Inference rearranging 4 conjuncts in antecedent.  (Contributed by NM,
       10-Aug-1995.) $)

${
	$v ph ps ch th ta  $.
	f0_an42s $f wff ph $.
	f1_an42s $f wff ps $.
	f2_an42s $f wff ch $.
	f3_an42s $f wff th $.
	f4_an42s $f wff ta $.
	e0_an42s $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
	p_an42s $p |- ( ( ( ph /\ ch ) /\ ( th /\ ps ) ) -> ta ) $= e0_an42s f0_an42s f1_an42s f2_an42s f3_an42s f4_an42s p_an4s f0_an42s f2_an42s a_wa f1_an42s f3_an42s f4_an42s p_ancom2s $.
$}

$(Distribution of conjunction over conjunction.  (Contributed by NM,
     14-Aug-1995.) $)

${
	$v ph ps ch  $.
	f0_anandi $f wff ph $.
	f1_anandi $f wff ps $.
	f2_anandi $f wff ch $.
	p_anandi $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ( ph /\ ps ) /\ ( ph /\ ch ) ) ) $= f0_anandi p_anidm f0_anandi f0_anandi a_wa f0_anandi f1_anandi f2_anandi a_wa p_anbi1i f0_anandi f0_anandi f1_anandi f2_anandi p_an4 f0_anandi f1_anandi f2_anandi a_wa a_wa f0_anandi f0_anandi a_wa f1_anandi f2_anandi a_wa a_wa f0_anandi f1_anandi a_wa f0_anandi f2_anandi a_wa a_wa p_bitr3i $.
$}

$(Distribution of conjunction over conjunction.  (Contributed by NM,
     24-Aug-1995.) $)

${
	$v ph ps ch  $.
	f0_anandir $f wff ph $.
	f1_anandir $f wff ps $.
	f2_anandir $f wff ch $.
	p_anandir $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ( ps /\ ch ) ) ) $= f2_anandir p_anidm f2_anandir f2_anandir a_wa f2_anandir f0_anandir f1_anandir a_wa p_anbi2i f0_anandir f1_anandir f2_anandir f2_anandir p_an4 f0_anandir f1_anandir a_wa f2_anandir a_wa f0_anandir f1_anandir a_wa f2_anandir f2_anandir a_wa a_wa f0_anandir f2_anandir a_wa f1_anandir f2_anandir a_wa a_wa p_bitr3i $.
$}

$(Inference that undistributes conjunction in the antecedent.
       (Contributed by NM, 7-Jun-2004.) $)

${
	$v ph ps ch ta  $.
	f0_anandis $f wff ph $.
	f1_anandis $f wff ps $.
	f2_anandis $f wff ch $.
	f3_anandis $f wff ta $.
	e0_anandis $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> ta ) $.
	p_anandis $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $= e0_anandis f0_anandis f1_anandis f0_anandis f2_anandis f3_anandis p_an4s f0_anandis f1_anandis f2_anandis a_wa f3_anandis p_anabsan $.
$}

$(Inference that undistributes conjunction in the antecedent.
       (Contributed by NM, 7-Jun-2004.) $)

${
	$v ph ps ch ta  $.
	f0_anandirs $f wff ph $.
	f1_anandirs $f wff ps $.
	f2_anandirs $f wff ch $.
	f3_anandirs $f wff ta $.
	e0_anandirs $e |- ( ( ( ph /\ ch ) /\ ( ps /\ ch ) ) -> ta ) $.
	p_anandirs $p |- ( ( ( ph /\ ps ) /\ ch ) -> ta ) $= e0_anandirs f0_anandirs f2_anandirs f1_anandirs f2_anandirs f3_anandirs p_an4s f0_anandirs f1_anandirs a_wa f2_anandirs f3_anandirs p_anabsan2 $.
$}

$(Deduce an equivalence from two implications.  (Contributed by NM,
       17-Feb-2007.) $)

${
	$v ph ps ch  $.
	f0_impbida $f wff ph $.
	f1_impbida $f wff ps $.
	f2_impbida $f wff ch $.
	e0_impbida $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_impbida $e |- ( ( ph /\ ch ) -> ps ) $.
	p_impbida $p |- ( ph -> ( ps <-> ch ) ) $= e0_impbida f0_impbida f1_impbida f2_impbida p_ex e1_impbida f0_impbida f2_impbida f1_impbida p_ex f0_impbida f1_impbida f2_impbida p_impbid $.
$}

$(Theorem *3.48 of [WhiteheadRussell] p. 114.  (Contributed by NM,
     28-Jan-1997.) $)

${
	$v ph ps ch th  $.
	f0_pm3.48 $f wff ph $.
	f1_pm3.48 $f wff ps $.
	f2_pm3.48 $f wff ch $.
	f3_pm3.48 $f wff th $.
	p_pm3.48 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) -> ( ( ph \/ ch ) -> ( ps \/ th ) ) ) $= f1_pm3.48 f3_pm3.48 p_orc f1_pm3.48 f1_pm3.48 f3_pm3.48 a_wo f0_pm3.48 p_imim2i f3_pm3.48 f1_pm3.48 p_olc f3_pm3.48 f1_pm3.48 f3_pm3.48 a_wo f2_pm3.48 p_imim2i f0_pm3.48 f1_pm3.48 a_wi f0_pm3.48 f1_pm3.48 f3_pm3.48 a_wo f2_pm3.48 f3_pm3.48 a_wi f2_pm3.48 p_jaao $.
$}

$(Theorem *3.45 (Fact) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm3.45 $f wff ph $.
	f1_pm3.45 $f wff ps $.
	f2_pm3.45 $f wff ch $.
	p_pm3.45 $p |- ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $= f0_pm3.45 f1_pm3.45 a_wi p_id f0_pm3.45 f1_pm3.45 a_wi f0_pm3.45 f1_pm3.45 f2_pm3.45 p_anim1d $.
$}

$(Deduction joining nested implications to form implication of
       conjunctions.  (Contributed by NM, 29-Feb-1996.) $)

${
	$v ph ps ch th ta et  $.
	f0_im2anan9 $f wff ph $.
	f1_im2anan9 $f wff ps $.
	f2_im2anan9 $f wff ch $.
	f3_im2anan9 $f wff th $.
	f4_im2anan9 $f wff ta $.
	f5_im2anan9 $f wff et $.
	e0_im2anan9 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_im2anan9 $e |- ( th -> ( ta -> et ) ) $.
	p_im2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $= e0_im2anan9 f0_im2anan9 f1_im2anan9 f2_im2anan9 a_wi f3_im2anan9 p_adantr e1_im2anan9 f3_im2anan9 f4_im2anan9 f5_im2anan9 a_wi f0_im2anan9 p_adantl f0_im2anan9 f3_im2anan9 a_wa f1_im2anan9 f2_im2anan9 f4_im2anan9 f5_im2anan9 p_anim12d $.
$}

$(Deduction joining nested implications to form implication of
       conjunctions.  (Contributed by NM, 29-Feb-1996.) $)

${
	$v ph ps ch th ta et  $.
	f0_im2anan9r $f wff ph $.
	f1_im2anan9r $f wff ps $.
	f2_im2anan9r $f wff ch $.
	f3_im2anan9r $f wff th $.
	f4_im2anan9r $f wff ta $.
	f5_im2anan9r $f wff et $.
	e0_im2anan9r $e |- ( ph -> ( ps -> ch ) ) $.
	e1_im2anan9r $e |- ( th -> ( ta -> et ) ) $.
	p_im2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $= e0_im2anan9r e1_im2anan9r f0_im2anan9r f1_im2anan9r f2_im2anan9r f3_im2anan9r f4_im2anan9r f5_im2anan9r p_im2anan9 f0_im2anan9r f3_im2anan9r f1_im2anan9r f4_im2anan9r a_wa f2_im2anan9r f5_im2anan9r a_wa a_wi p_ancoms $.
$}

$(Conjoin antecedents and consequents in a deduction.  (Contributed by
       Mario Carneiro, 12-May-2014.) $)

${
	$v ph ps ch th ta  $.
	f0_anim12dan $f wff ph $.
	f1_anim12dan $f wff ps $.
	f2_anim12dan $f wff ch $.
	f3_anim12dan $f wff th $.
	f4_anim12dan $f wff ta $.
	e0_anim12dan $e |- ( ( ph /\ ps ) -> ch ) $.
	e1_anim12dan $e |- ( ( ph /\ th ) -> ta ) $.
	p_anim12dan $p |- ( ( ph /\ ( ps /\ th ) ) -> ( ch /\ ta ) ) $= e0_anim12dan f0_anim12dan f1_anim12dan f2_anim12dan p_ex e1_anim12dan f0_anim12dan f3_anim12dan f4_anim12dan p_ex f0_anim12dan f1_anim12dan f2_anim12dan f3_anim12dan f4_anim12dan p_anim12d f0_anim12dan f1_anim12dan f3_anim12dan a_wa f2_anim12dan f4_anim12dan a_wa p_imp $.
$}

$(Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       10-May-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_orim12d $f wff ph $.
	f1_orim12d $f wff ps $.
	f2_orim12d $f wff ch $.
	f3_orim12d $f wff th $.
	f4_orim12d $f wff ta $.
	e0_orim12d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_orim12d $e |- ( ph -> ( th -> ta ) ) $.
	p_orim12d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ ta ) ) ) $= e0_orim12d e1_orim12d f1_orim12d f2_orim12d f3_orim12d f4_orim12d p_pm3.48 f0_orim12d f1_orim12d f2_orim12d a_wi f3_orim12d f4_orim12d a_wi f1_orim12d f3_orim12d a_wo f2_orim12d f4_orim12d a_wo a_wi p_syl2anc $.
$}

$(Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       23-Apr-1995.) $)

${
	$v ph ps ch th  $.
	f0_orim1d $f wff ph $.
	f1_orim1d $f wff ps $.
	f2_orim1d $f wff ch $.
	f3_orim1d $f wff th $.
	e0_orim1d $e |- ( ph -> ( ps -> ch ) ) $.
	p_orim1d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ th ) ) ) $= e0_orim1d f0_orim1d f3_orim1d p_idd f0_orim1d f1_orim1d f2_orim1d f3_orim1d f3_orim1d p_orim12d $.
$}

$(Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       23-Apr-1995.) $)

${
	$v ph ps ch th  $.
	f0_orim2d $f wff ph $.
	f1_orim2d $f wff ps $.
	f2_orim2d $f wff ch $.
	f3_orim2d $f wff th $.
	e0_orim2d $e |- ( ph -> ( ps -> ch ) ) $.
	p_orim2d $p |- ( ph -> ( ( th \/ ps ) -> ( th \/ ch ) ) ) $= f0_orim2d f3_orim2d p_idd e0_orim2d f0_orim2d f3_orim2d f3_orim2d f1_orim2d f2_orim2d p_orim12d $.
$}

$(Axiom *1.6 (Sum) of [WhiteheadRussell] p. 97.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_orim2 $f wff ph $.
	f1_orim2 $f wff ps $.
	f2_orim2 $f wff ch $.
	p_orim2 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $= f1_orim2 f2_orim2 a_wi p_id f1_orim2 f2_orim2 a_wi f1_orim2 f2_orim2 f0_orim2 p_orim2d $.
$}

$(Theorem *2.38 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)

${
	$v ph ps ch  $.
	f0_pm2.38 $f wff ph $.
	f1_pm2.38 $f wff ps $.
	f2_pm2.38 $f wff ch $.
	p_pm2.38 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ch \/ ph ) ) ) $= f1_pm2.38 f2_pm2.38 a_wi p_id f1_pm2.38 f2_pm2.38 a_wi f1_pm2.38 f2_pm2.38 f0_pm2.38 p_orim1d $.
$}

$(Theorem *2.36 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)

${
	$v ph ps ch  $.
	f0_pm2.36 $f wff ph $.
	f1_pm2.36 $f wff ps $.
	f2_pm2.36 $f wff ch $.
	p_pm2.36 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ch \/ ph ) ) ) $= f0_pm2.36 f1_pm2.36 p_pm1.4 f0_pm2.36 f1_pm2.36 f2_pm2.36 p_pm2.38 f0_pm2.36 f1_pm2.36 a_wo f1_pm2.36 f0_pm2.36 a_wo f1_pm2.36 f2_pm2.36 a_wi f2_pm2.36 f0_pm2.36 a_wo p_syl5 $.
$}

$(Theorem *2.37 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)

${
	$v ph ps ch  $.
	f0_pm2.37 $f wff ph $.
	f1_pm2.37 $f wff ps $.
	f2_pm2.37 $f wff ch $.
	p_pm2.37 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ph \/ ch ) ) ) $= f0_pm2.37 f1_pm2.37 f2_pm2.37 p_pm2.38 f2_pm2.37 f0_pm2.37 p_pm1.4 f1_pm2.37 f2_pm2.37 a_wi f1_pm2.37 f0_pm2.37 a_wo f2_pm2.37 f0_pm2.37 a_wo f0_pm2.37 f2_pm2.37 a_wo p_syl6 $.
$}

$(Theorem *2.73 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.73 $f wff ph $.
	f1_pm2.73 $f wff ps $.
	f2_pm2.73 $f wff ch $.
	p_pm2.73 $p |- ( ( ph -> ps ) -> ( ( ( ph \/ ps ) \/ ch ) -> ( ps \/ ch ) ) ) $= f0_pm2.73 f1_pm2.73 p_pm2.621 f0_pm2.73 f1_pm2.73 a_wi f0_pm2.73 f1_pm2.73 a_wo f1_pm2.73 f2_pm2.73 p_orim1d $.
$}

$(Theorem *2.74 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps ch  $.
	f0_pm2.74 $f wff ph $.
	f1_pm2.74 $f wff ps $.
	f2_pm2.74 $f wff ch $.
	p_pm2.74 $p |- ( ( ps -> ph ) -> ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ch ) ) ) $= f1_pm2.74 f0_pm2.74 p_orel2 f0_pm2.74 f0_pm2.74 f1_pm2.74 a_wo a_ax-1 f1_pm2.74 f0_pm2.74 f0_pm2.74 f1_pm2.74 a_wo f0_pm2.74 a_wi p_ja f1_pm2.74 f0_pm2.74 a_wi f0_pm2.74 f1_pm2.74 a_wo f0_pm2.74 f2_pm2.74 p_orim1d $.
$}

$(Disjunction distributes over implication.  (Contributed by Wolf Lammen,
     5-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_orimdi $f wff ph $.
	f1_orimdi $f wff ps $.
	f2_orimdi $f wff ch $.
	p_orimdi $p |- ( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $= f0_orimdi a_wn f1_orimdi f2_orimdi p_imdi f0_orimdi f1_orimdi f2_orimdi a_wi a_df-or f0_orimdi f1_orimdi a_df-or f0_orimdi f2_orimdi a_df-or f0_orimdi f1_orimdi a_wo f0_orimdi a_wn f1_orimdi a_wi f0_orimdi f2_orimdi a_wo f0_orimdi a_wn f2_orimdi a_wi p_imbi12i f0_orimdi a_wn f1_orimdi f2_orimdi a_wi a_wi f0_orimdi a_wn f1_orimdi a_wi f0_orimdi a_wn f2_orimdi a_wi a_wi f0_orimdi f1_orimdi f2_orimdi a_wi a_wo f0_orimdi f1_orimdi a_wo f0_orimdi f2_orimdi a_wo a_wi p_3bitr4i $.
$}

$(Theorem *2.76 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.76 $f wff ph $.
	f1_pm2.76 $f wff ps $.
	f2_pm2.76 $f wff ch $.
	p_pm2.76 $p |- ( ( ph \/ ( ps -> ch ) ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $= f0_pm2.76 f1_pm2.76 f2_pm2.76 p_orimdi f0_pm2.76 f1_pm2.76 f2_pm2.76 a_wi a_wo f0_pm2.76 f1_pm2.76 a_wo f0_pm2.76 f2_pm2.76 a_wo a_wi p_biimpi $.
$}

$(Theorem *2.75 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 4-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_pm2.75 $f wff ph $.
	f1_pm2.75 $f wff ps $.
	f2_pm2.75 $f wff ch $.
	p_pm2.75 $p |- ( ( ph \/ ps ) -> ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) ) $= f0_pm2.75 f1_pm2.75 f2_pm2.75 p_pm2.76 f0_pm2.75 f1_pm2.75 f2_pm2.75 a_wi a_wo f0_pm2.75 f1_pm2.75 a_wo f0_pm2.75 f2_pm2.75 a_wo p_com12 $.
$}

$(Theorem *2.8 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_pm2.8 $f wff ph $.
	f1_pm2.8 $f wff ps $.
	f2_pm2.8 $f wff ch $.
	p_pm2.8 $p |- ( ( ph \/ ps ) -> ( ( -. ps \/ ch ) -> ( ph \/ ch ) ) ) $= f0_pm2.8 f1_pm2.8 p_pm2.53 f0_pm2.8 f1_pm2.8 a_wo f0_pm2.8 f1_pm2.8 p_con1d f0_pm2.8 f1_pm2.8 a_wo f1_pm2.8 a_wn f0_pm2.8 f2_pm2.8 p_orim1d $.
$}

$(Theorem *2.81 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch th  $.
	f0_pm2.81 $f wff ph $.
	f1_pm2.81 $f wff ps $.
	f2_pm2.81 $f wff ch $.
	f3_pm2.81 $f wff th $.
	p_pm2.81 $p |- ( ( ps -> ( ch -> th ) ) -> ( ( ph \/ ps ) -> ( ( ph \/ ch ) -> ( ph \/ th ) ) ) ) $= f0_pm2.81 f1_pm2.81 f2_pm2.81 f3_pm2.81 a_wi p_orim2 f0_pm2.81 f2_pm2.81 f3_pm2.81 p_pm2.76 f1_pm2.81 f2_pm2.81 f3_pm2.81 a_wi a_wi f0_pm2.81 f1_pm2.81 a_wo f0_pm2.81 f2_pm2.81 f3_pm2.81 a_wi a_wo f0_pm2.81 f2_pm2.81 a_wo f0_pm2.81 f3_pm2.81 a_wo a_wi p_syl6 $.
$}

$(Theorem *2.82 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch th  $.
	f0_pm2.82 $f wff ph $.
	f1_pm2.82 $f wff ps $.
	f2_pm2.82 $f wff ch $.
	f3_pm2.82 $f wff th $.
	p_pm2.82 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th ) -> ( ( ph \/ ps ) \/ th ) ) ) $= f0_pm2.82 f1_pm2.82 a_wo f0_pm2.82 f2_pm2.82 a_wn a_wo a_ax-1 f2_pm2.82 f1_pm2.82 p_pm2.24 f2_pm2.82 f2_pm2.82 a_wn f1_pm2.82 f0_pm2.82 p_orim2d f0_pm2.82 f1_pm2.82 a_wo f0_pm2.82 f2_pm2.82 a_wn a_wo f0_pm2.82 f1_pm2.82 a_wo a_wi f2_pm2.82 p_jaoi f0_pm2.82 f1_pm2.82 a_wo f2_pm2.82 a_wo f0_pm2.82 f2_pm2.82 a_wn a_wo f0_pm2.82 f1_pm2.82 a_wo f3_pm2.82 p_orim1d $.
$}

$(Theorem *2.85 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_pm2.85 $f wff ph $.
	f1_pm2.85 $f wff ps $.
	f2_pm2.85 $f wff ch $.
	p_pm2.85 $p |- ( ( ( ph \/ ps ) -> ( ph \/ ch ) ) -> ( ph \/ ( ps -> ch ) ) ) $= f0_pm2.85 f1_pm2.85 f2_pm2.85 p_orimdi f0_pm2.85 f1_pm2.85 f2_pm2.85 a_wi a_wo f0_pm2.85 f1_pm2.85 a_wo f0_pm2.85 f2_pm2.85 a_wo a_wi p_biimpri $.
$}

$(Infer negated disjunction of negated premises.  (Contributed by NM,
       4-Apr-1995.) $)

${
	$v ph ps  $.
	f0_pm3.2ni $f wff ph $.
	f1_pm3.2ni $f wff ps $.
	e0_pm3.2ni $e |- -. ph $.
	e1_pm3.2ni $e |- -. ps $.
	p_pm3.2ni $p |- -. ( ph \/ ps ) $= e0_pm3.2ni f0_pm3.2ni p_id e1_pm3.2ni f1_pm3.2ni f0_pm3.2ni p_pm2.21i f0_pm3.2ni f0_pm3.2ni f1_pm3.2ni p_jaoi f0_pm3.2ni f1_pm3.2ni a_wo f0_pm3.2ni p_mto $.
$}

$(Absorption of redundant internal disjunct.  Compare Theorem *4.45 of
     [WhiteheadRussell] p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 28-Feb-2014.) $)

${
	$v ph ps  $.
	f0_orabs $f wff ph $.
	f1_orabs $f wff ps $.
	p_orabs $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $= f0_orabs f1_orabs p_orc f0_orabs f0_orabs f1_orabs a_wo p_pm4.71ri $.
$}

$(Absorb a disjunct into a conjunct.  (Contributed by Roy F. Longton,
     23-Jun-2005.)  (Proof shortened by Wolf Lammen, 10-Nov-2013.) $)

${
	$v ph ps  $.
	f0_oranabs $f wff ph $.
	f1_oranabs $f wff ps $.
	p_oranabs $p |- ( ( ( ph \/ -. ps ) /\ ps ) <-> ( ph /\ ps ) ) $= f1_oranabs f0_oranabs p_biortn f1_oranabs a_wn f0_oranabs p_orcom f1_oranabs f0_oranabs f1_oranabs a_wn f0_oranabs a_wo f0_oranabs f1_oranabs a_wn a_wo p_syl6rbb f1_oranabs f0_oranabs f1_oranabs a_wn a_wo f0_oranabs p_pm5.32ri $.
$}

$(Two propositions are equivalent if they are both true.  Theorem *5.1 of
     [WhiteheadRussell] p. 123.  (Contributed by NM, 21-May-1994.) $)

${
	$v ph ps  $.
	f0_pm5.1 $f wff ph $.
	f1_pm5.1 $f wff ps $.
	p_pm5.1 $p |- ( ( ph /\ ps ) -> ( ph <-> ps ) ) $= f0_pm5.1 f1_pm5.1 p_pm5.501 f0_pm5.1 f1_pm5.1 f0_pm5.1 f1_pm5.1 a_wb p_biimpa $.
$}

$(Two propositions are equivalent if they are both false.  Theorem *5.21 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 21-May-1994.) $)

${
	$v ph ps  $.
	f0_pm5.21 $f wff ph $.
	f1_pm5.21 $f wff ps $.
	p_pm5.21 $p |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) ) $= f0_pm5.21 f1_pm5.21 p_pm5.21im f0_pm5.21 a_wn f1_pm5.21 a_wn f0_pm5.21 f1_pm5.21 a_wb p_imp $.
$}

$(Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm3.43 $f wff ph $.
	f1_pm3.43 $f wff ps $.
	f2_pm3.43 $f wff ch $.
	p_pm3.43 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) -> ( ph -> ( ps /\ ch ) ) ) $= f0_pm3.43 f1_pm3.43 f2_pm3.43 p_pm3.43i f0_pm3.43 f1_pm3.43 a_wi f0_pm3.43 f2_pm3.43 a_wi f0_pm3.43 f1_pm3.43 f2_pm3.43 a_wa a_wi p_imp $.
$}

$(Distributive law for implication over conjunction.  Compare Theorem *4.76
     of [WhiteheadRussell] p. 121.  (Contributed by NM, 3-Apr-1994.)  (Proof
     shortened by Wolf Lammen, 27-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_jcab $f wff ph $.
	f1_jcab $f wff ps $.
	f2_jcab $f wff ch $.
	p_jcab $p |- ( ( ph -> ( ps /\ ch ) ) <-> ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $= f1_jcab f2_jcab p_simpl f1_jcab f2_jcab a_wa f1_jcab f0_jcab p_imim2i f1_jcab f2_jcab p_simpr f1_jcab f2_jcab a_wa f2_jcab f0_jcab p_imim2i f0_jcab f1_jcab f2_jcab a_wa a_wi f0_jcab f1_jcab a_wi f0_jcab f2_jcab a_wi p_jca f0_jcab f1_jcab f2_jcab p_pm3.43 f0_jcab f1_jcab f2_jcab a_wa a_wi f0_jcab f1_jcab a_wi f0_jcab f2_jcab a_wi a_wa p_impbii $.
$}

$(Distributive law for disjunction.  Theorem *4.41 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 7-May-2011.)  (Proof shortened by Wolf Lammen, 28-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_ordi $f wff ph $.
	f1_ordi $f wff ps $.
	f2_ordi $f wff ch $.
	p_ordi $p |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $= f0_ordi a_wn f1_ordi f2_ordi p_jcab f0_ordi f1_ordi f2_ordi a_wa a_df-or f0_ordi f1_ordi a_df-or f0_ordi f2_ordi a_df-or f0_ordi f1_ordi a_wo f0_ordi a_wn f1_ordi a_wi f0_ordi f2_ordi a_wo f0_ordi a_wn f2_ordi a_wi p_anbi12i f0_ordi a_wn f1_ordi f2_ordi a_wa a_wi f0_ordi a_wn f1_ordi a_wi f0_ordi a_wn f2_ordi a_wi a_wa f0_ordi f1_ordi f2_ordi a_wa a_wo f0_ordi f1_ordi a_wo f0_ordi f2_ordi a_wo a_wa p_3bitr4i $.
$}

$(Distributive law for disjunction.  (Contributed by NM, 12-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_ordir $f wff ph $.
	f1_ordir $f wff ps $.
	f2_ordir $f wff ch $.
	p_ordir $p |- ( ( ( ph /\ ps ) \/ ch ) <-> ( ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $= f2_ordir f0_ordir f1_ordir p_ordi f0_ordir f1_ordir a_wa f2_ordir p_orcom f0_ordir f2_ordir p_orcom f1_ordir f2_ordir p_orcom f0_ordir f2_ordir a_wo f2_ordir f0_ordir a_wo f1_ordir f2_ordir a_wo f2_ordir f1_ordir a_wo p_anbi12i f2_ordir f0_ordir f1_ordir a_wa a_wo f2_ordir f0_ordir a_wo f2_ordir f1_ordir a_wo a_wa f0_ordir f1_ordir a_wa f2_ordir a_wo f0_ordir f2_ordir a_wo f1_ordir f2_ordir a_wo a_wa p_3bitr4i $.
$}

$(Theorem *4.76 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm4.76 $f wff ph $.
	f1_pm4.76 $f wff ps $.
	f2_pm4.76 $f wff ch $.
	p_pm4.76 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <-> ( ph -> ( ps /\ ch ) ) ) $= f0_pm4.76 f1_pm4.76 f2_pm4.76 p_jcab f0_pm4.76 f1_pm4.76 f2_pm4.76 a_wa a_wi f0_pm4.76 f1_pm4.76 a_wi f0_pm4.76 f2_pm4.76 a_wi a_wa p_bicomi $.
$}

$(Distributive law for conjunction.  Theorem *4.4 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 5-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_andi $f wff ph $.
	f1_andi $f wff ps $.
	f2_andi $f wff ch $.
	p_andi $p |- ( ( ph /\ ( ps \/ ch ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $= f0_andi f1_andi a_wa f0_andi f2_andi a_wa p_orc f0_andi f2_andi a_wa f0_andi f1_andi a_wa p_olc f0_andi f1_andi f0_andi f1_andi a_wa f0_andi f2_andi a_wa a_wo f2_andi p_jaodan f1_andi f2_andi p_orc f1_andi f1_andi f2_andi a_wo f0_andi p_anim2i f2_andi f1_andi p_olc f2_andi f1_andi f2_andi a_wo f0_andi p_anim2i f0_andi f1_andi a_wa f0_andi f1_andi f2_andi a_wo a_wa f0_andi f2_andi a_wa p_jaoi f0_andi f1_andi f2_andi a_wo a_wa f0_andi f1_andi a_wa f0_andi f2_andi a_wa a_wo p_impbii $.
$}

$(Distributive law for conjunction.  (Contributed by NM, 12-Aug-1994.) $)

${
	$v ph ps ch  $.
	f0_andir $f wff ph $.
	f1_andir $f wff ps $.
	f2_andir $f wff ch $.
	p_andir $p |- ( ( ( ph \/ ps ) /\ ch ) <-> ( ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $= f2_andir f0_andir f1_andir p_andi f0_andir f1_andir a_wo f2_andir p_ancom f0_andir f2_andir p_ancom f1_andir f2_andir p_ancom f0_andir f2_andir a_wa f2_andir f0_andir a_wa f1_andir f2_andir a_wa f2_andir f1_andir a_wa p_orbi12i f2_andir f0_andir f1_andir a_wo a_wa f2_andir f0_andir a_wa f2_andir f1_andir a_wa a_wo f0_andir f1_andir a_wo f2_andir a_wa f0_andir f2_andir a_wa f1_andir f2_andir a_wa a_wo p_3bitr4i $.
$}

$(Double distributive law for disjunction.  (Contributed by NM,
     12-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_orddi $f wff ph $.
	f1_orddi $f wff ps $.
	f2_orddi $f wff ch $.
	f3_orddi $f wff th $.
	p_orddi $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <-> ( ( ( ph \/ ch ) /\ ( ph \/ th ) ) /\ ( ( ps \/ ch ) /\ ( ps \/ th ) ) ) ) $= f0_orddi f1_orddi f2_orddi f3_orddi a_wa p_ordir f0_orddi f2_orddi f3_orddi p_ordi f1_orddi f2_orddi f3_orddi p_ordi f0_orddi f2_orddi f3_orddi a_wa a_wo f0_orddi f2_orddi a_wo f0_orddi f3_orddi a_wo a_wa f1_orddi f2_orddi f3_orddi a_wa a_wo f1_orddi f2_orddi a_wo f1_orddi f3_orddi a_wo a_wa p_anbi12i f0_orddi f1_orddi a_wa f2_orddi f3_orddi a_wa a_wo f0_orddi f2_orddi f3_orddi a_wa a_wo f1_orddi f2_orddi f3_orddi a_wa a_wo a_wa f0_orddi f2_orddi a_wo f0_orddi f3_orddi a_wo a_wa f1_orddi f2_orddi a_wo f1_orddi f3_orddi a_wo a_wa a_wa p_bitri $.
$}

$(Double distributive law for conjunction.  (Contributed by NM,
     12-Aug-1994.) $)

${
	$v ph ps ch th  $.
	f0_anddi $f wff ph $.
	f1_anddi $f wff ps $.
	f2_anddi $f wff ch $.
	f3_anddi $f wff th $.
	p_anddi $p |- ( ( ( ph \/ ps ) /\ ( ch \/ th ) ) <-> ( ( ( ph /\ ch ) \/ ( ph /\ th ) ) \/ ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ) $= f0_anddi f1_anddi f2_anddi f3_anddi a_wo p_andir f0_anddi f2_anddi f3_anddi p_andi f1_anddi f2_anddi f3_anddi p_andi f0_anddi f2_anddi f3_anddi a_wo a_wa f0_anddi f2_anddi a_wa f0_anddi f3_anddi a_wa a_wo f1_anddi f2_anddi f3_anddi a_wo a_wa f1_anddi f2_anddi a_wa f1_anddi f3_anddi a_wa a_wo p_orbi12i f0_anddi f1_anddi a_wo f2_anddi f3_anddi a_wo a_wa f0_anddi f2_anddi f3_anddi a_wo a_wa f1_anddi f2_anddi f3_anddi a_wo a_wa a_wo f0_anddi f2_anddi a_wa f0_anddi f3_anddi a_wa a_wo f1_anddi f2_anddi a_wa f1_anddi f3_anddi a_wa a_wo a_wo p_bitri $.
$}

$(Prove formula-building rules for the biconditional connective. $)

$(Theorem *4.39 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch th  $.
	f0_pm4.39 $f wff ph $.
	f1_pm4.39 $f wff ps $.
	f2_pm4.39 $f wff ch $.
	f3_pm4.39 $f wff th $.
	p_pm4.39 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) -> ( ( ph \/ ps ) <-> ( ch \/ th ) ) ) $= f0_pm4.39 f2_pm4.39 a_wb f1_pm4.39 f3_pm4.39 a_wb p_simpl f0_pm4.39 f2_pm4.39 a_wb f1_pm4.39 f3_pm4.39 a_wb p_simpr f0_pm4.39 f2_pm4.39 a_wb f1_pm4.39 f3_pm4.39 a_wb a_wa f0_pm4.39 f2_pm4.39 f1_pm4.39 f3_pm4.39 p_orbi12d $.
$}

$(Theorem *4.38 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch th  $.
	f0_pm4.38 $f wff ph $.
	f1_pm4.38 $f wff ps $.
	f2_pm4.38 $f wff ch $.
	f3_pm4.38 $f wff th $.
	p_pm4.38 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) -> ( ( ph /\ ps ) <-> ( ch /\ th ) ) ) $= f0_pm4.38 f2_pm4.38 a_wb f1_pm4.38 f3_pm4.38 a_wb p_simpl f0_pm4.38 f2_pm4.38 a_wb f1_pm4.38 f3_pm4.38 a_wb p_simpr f0_pm4.38 f2_pm4.38 a_wb f1_pm4.38 f3_pm4.38 a_wb a_wa f0_pm4.38 f2_pm4.38 f1_pm4.38 f3_pm4.38 p_anbi12d $.
$}

$(Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 31-Jul-1995.) $)

${
	$v ph ps ch th ta et  $.
	f0_bi2anan9 $f wff ph $.
	f1_bi2anan9 $f wff ps $.
	f2_bi2anan9 $f wff ch $.
	f3_bi2anan9 $f wff th $.
	f4_bi2anan9 $f wff ta $.
	f5_bi2anan9 $f wff et $.
	e0_bi2anan9 $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_bi2anan9 $e |- ( th -> ( ta <-> et ) ) $.
	p_bi2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $= e0_bi2anan9 f0_bi2anan9 f1_bi2anan9 f2_bi2anan9 f4_bi2anan9 p_anbi1d e1_bi2anan9 f3_bi2anan9 f4_bi2anan9 f5_bi2anan9 f2_bi2anan9 p_anbi2d f0_bi2anan9 f1_bi2anan9 f4_bi2anan9 a_wa f2_bi2anan9 f4_bi2anan9 a_wa f3_bi2anan9 f2_bi2anan9 f5_bi2anan9 a_wa p_sylan9bb $.
$}

$(Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 19-Feb-1996.) $)

${
	$v ph ps ch th ta et  $.
	f0_bi2anan9r $f wff ph $.
	f1_bi2anan9r $f wff ps $.
	f2_bi2anan9r $f wff ch $.
	f3_bi2anan9r $f wff th $.
	f4_bi2anan9r $f wff ta $.
	f5_bi2anan9r $f wff et $.
	e0_bi2anan9r $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_bi2anan9r $e |- ( th -> ( ta <-> et ) ) $.
	p_bi2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $= e0_bi2anan9r e1_bi2anan9r f0_bi2anan9r f1_bi2anan9r f2_bi2anan9r f3_bi2anan9r f4_bi2anan9r f5_bi2anan9r p_bi2anan9 f0_bi2anan9r f3_bi2anan9r f1_bi2anan9r f4_bi2anan9r a_wa f2_bi2anan9r f5_bi2anan9r a_wa a_wb p_ancoms $.
$}

$(Deduction joining two biconditionals with different antecedents.
       (Contributed by NM, 12-May-2004.) $)

${
	$v ph ps ch th ta et  $.
	f0_bi2bian9 $f wff ph $.
	f1_bi2bian9 $f wff ps $.
	f2_bi2bian9 $f wff ch $.
	f3_bi2bian9 $f wff th $.
	f4_bi2bian9 $f wff ta $.
	f5_bi2bian9 $f wff et $.
	e0_bi2bian9 $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_bi2bian9 $e |- ( th -> ( ta <-> et ) ) $.
	p_bi2bian9 $p |- ( ( ph /\ th ) -> ( ( ps <-> ta ) <-> ( ch <-> et ) ) ) $= e0_bi2bian9 f0_bi2bian9 f1_bi2bian9 f2_bi2bian9 a_wb f3_bi2bian9 p_adantr e1_bi2bian9 f3_bi2bian9 f4_bi2bian9 f5_bi2bian9 a_wb f0_bi2bian9 p_adantl f0_bi2bian9 f3_bi2bian9 a_wa f1_bi2bian9 f2_bi2bian9 f4_bi2bian9 f5_bi2bian9 p_bibi12d $.
$}

$(Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 30-Jan-2013.) $)

${
	$v ph ps  $.
	f0_pm4.72 $f wff ph $.
	f1_pm4.72 $f wff ps $.
	p_pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $= f1_pm4.72 f0_pm4.72 p_olc f0_pm4.72 f1_pm4.72 p_pm2.621 f0_pm4.72 f1_pm4.72 a_wi f1_pm4.72 f0_pm4.72 f1_pm4.72 a_wo p_impbid2 f0_pm4.72 f1_pm4.72 p_orc f1_pm4.72 f0_pm4.72 f1_pm4.72 a_wo p_bi2 f0_pm4.72 f0_pm4.72 f1_pm4.72 a_wo f1_pm4.72 f0_pm4.72 f1_pm4.72 a_wo a_wb f1_pm4.72 p_syl5 f0_pm4.72 f1_pm4.72 a_wi f1_pm4.72 f0_pm4.72 f1_pm4.72 a_wo a_wb p_impbii $.
$}

$(Simplify an implication between implications.  (Contributed by Paul
     Chapman, 17-Nov-2012.)  (Proof shortened by Wolf Lammen, 3-Apr-2013.) $)

${
	$v ph ps ch  $.
	f0_imimorb $f wff ph $.
	f1_imimorb $f wff ps $.
	f2_imimorb $f wff ch $.
	p_imimorb $p |- ( ( ( ps -> ch ) -> ( ph -> ch ) ) <-> ( ph -> ( ps \/ ch ) ) ) $= f1_imimorb f2_imimorb a_wi f0_imimorb f2_imimorb p_bi2.04 f1_imimorb f2_imimorb p_dfor2 f1_imimorb f2_imimorb a_wo f1_imimorb f2_imimorb a_wi f2_imimorb a_wi f0_imimorb p_imbi2i f1_imimorb f2_imimorb a_wi f0_imimorb f2_imimorb a_wi a_wi f0_imimorb f1_imimorb f2_imimorb a_wi f2_imimorb a_wi a_wi f0_imimorb f1_imimorb f2_imimorb a_wo a_wi p_bitr4i $.
$}

$(Theorem *5.33 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm5.33 $f wff ph $.
	f1_pm5.33 $f wff ps $.
	f2_pm5.33 $f wff ch $.
	p_pm5.33 $p |- ( ( ph /\ ( ps -> ch ) ) <-> ( ph /\ ( ( ph /\ ps ) -> ch ) ) ) $= f0_pm5.33 f1_pm5.33 p_ibar f0_pm5.33 f1_pm5.33 f0_pm5.33 f1_pm5.33 a_wa f2_pm5.33 p_imbi1d f0_pm5.33 f1_pm5.33 f2_pm5.33 a_wi f0_pm5.33 f1_pm5.33 a_wa f2_pm5.33 a_wi p_pm5.32i $.
$}

$(Theorem *5.36 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm5.36 $f wff ph $.
	f1_pm5.36 $f wff ps $.
	p_pm5.36 $p |- ( ( ph /\ ( ph <-> ps ) ) <-> ( ps /\ ( ph <-> ps ) ) ) $= f0_pm5.36 f1_pm5.36 a_wb p_id f0_pm5.36 f1_pm5.36 a_wb f0_pm5.36 f1_pm5.36 p_pm5.32ri $.
$}

$(Absorb a hypothesis into the second member of a biconditional.
       (Contributed by FL, 15-Feb-2007.) $)

${
	$v ph ps ch  $.
	f0_bianabs $f wff ph $.
	f1_bianabs $f wff ps $.
	f2_bianabs $f wff ch $.
	e0_bianabs $e |- ( ph -> ( ps <-> ( ph /\ ch ) ) ) $.
	p_bianabs $p |- ( ph -> ( ps <-> ch ) ) $= e0_bianabs f0_bianabs f2_bianabs p_ibar f0_bianabs f1_bianabs f0_bianabs f2_bianabs a_wa f2_bianabs p_bitr4d $.
$}

$(Absorption of disjunction into equivalence.  (Contributed by NM,
     6-Aug-1995.)  (Proof shortened by Wolf Lammen, 3-Nov-2013.) $)

${
	$v ph ps  $.
	f0_oibabs $f wff ph $.
	f1_oibabs $f wff ps $.
	p_oibabs $p |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) ) $= f0_oibabs f1_oibabs p_ioran f0_oibabs f1_oibabs p_pm5.21 f0_oibabs f1_oibabs a_wo a_wn f0_oibabs a_wn f1_oibabs a_wn a_wa f0_oibabs f1_oibabs a_wb p_sylbi f0_oibabs f1_oibabs a_wb p_id f0_oibabs f1_oibabs a_wo f0_oibabs f1_oibabs a_wb f0_oibabs f1_oibabs a_wb p_ja f0_oibabs f1_oibabs a_wb f0_oibabs f1_oibabs a_wo a_ax-1 f0_oibabs f1_oibabs a_wo f0_oibabs f1_oibabs a_wb a_wi f0_oibabs f1_oibabs a_wb p_impbii $.
$}

$(Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111 (who
     call it the "law of contradiction").  (Contributed by NM, 16-Sep-1993.)
     (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)

${
	$v ph  $.
	f0_pm3.24 $f wff ph $.
	p_pm3.24 $p |- -. ( ph /\ -. ph ) $= f0_pm3.24 p_id f0_pm3.24 f0_pm3.24 p_iman f0_pm3.24 f0_pm3.24 a_wi f0_pm3.24 f0_pm3.24 a_wn a_wa a_wn p_mpbi $.
$}

$(Theorem *2.26 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)

${
	$v ph ps  $.
	f0_pm2.26 $f wff ph $.
	f1_pm2.26 $f wff ps $.
	p_pm2.26 $p |- ( -. ph \/ ( ( ph -> ps ) -> ps ) ) $= f0_pm2.26 f1_pm2.26 p_pm2.27 f0_pm2.26 f0_pm2.26 f1_pm2.26 a_wi f1_pm2.26 a_wi p_imori $.
$}

$(Theorem *5.11 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm5.11 $f wff ph $.
	f1_pm5.11 $f wff ps $.
	p_pm5.11 $p |- ( ( ph -> ps ) \/ ( -. ph -> ps ) ) $= f0_pm5.11 f1_pm5.11 p_pm2.5 f0_pm5.11 f1_pm5.11 a_wi f0_pm5.11 a_wn f1_pm5.11 a_wi p_orri $.
$}

$(Theorem *5.12 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm5.12 $f wff ph $.
	f1_pm5.12 $f wff ps $.
	p_pm5.12 $p |- ( ( ph -> ps ) \/ ( ph -> -. ps ) ) $= f0_pm5.12 f1_pm5.12 p_pm2.51 f0_pm5.12 f1_pm5.12 a_wi f0_pm5.12 f1_pm5.12 a_wn a_wi p_orri $.
$}

$(Theorem *5.14 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch  $.
	f0_pm5.14 $f wff ph $.
	f1_pm5.14 $f wff ps $.
	f2_pm5.14 $f wff ch $.
	p_pm5.14 $p |- ( ( ph -> ps ) \/ ( ps -> ch ) ) $= f1_pm5.14 f0_pm5.14 a_ax-1 f1_pm5.14 f0_pm5.14 f1_pm5.14 a_wi p_con3i f0_pm5.14 f1_pm5.14 a_wi a_wn f1_pm5.14 f2_pm5.14 p_pm2.21d f0_pm5.14 f1_pm5.14 a_wi f1_pm5.14 f2_pm5.14 a_wi p_orri $.
$}

$(Theorem *5.13 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)

${
	$v ph ps  $.
	f0_pm5.13 $f wff ph $.
	f1_pm5.13 $f wff ps $.
	p_pm5.13 $p |- ( ( ph -> ps ) \/ ( ps -> ph ) ) $= f0_pm5.13 f1_pm5.13 f0_pm5.13 p_pm5.14 $.
$}

$(Theorem *5.17 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)

${
	$v ph ps  $.
	f0_pm5.17 $f wff ph $.
	f1_pm5.17 $f wff ps $.
	p_pm5.17 $p |- ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) ) $= f0_pm5.17 f1_pm5.17 a_wn p_bicom f1_pm5.17 a_wn f0_pm5.17 p_dfbi2 f0_pm5.17 f1_pm5.17 p_orcom f1_pm5.17 f0_pm5.17 a_df-or f0_pm5.17 f1_pm5.17 a_wo f1_pm5.17 f0_pm5.17 a_wo f1_pm5.17 a_wn f0_pm5.17 a_wi p_bitr2i f0_pm5.17 f1_pm5.17 p_imnan f1_pm5.17 a_wn f0_pm5.17 a_wi f0_pm5.17 f1_pm5.17 a_wo f0_pm5.17 f1_pm5.17 a_wn a_wi f0_pm5.17 f1_pm5.17 a_wa a_wn p_anbi12i f0_pm5.17 f1_pm5.17 a_wn a_wb f1_pm5.17 a_wn f0_pm5.17 a_wb f1_pm5.17 a_wn f0_pm5.17 a_wi f0_pm5.17 f1_pm5.17 a_wn a_wi a_wa f0_pm5.17 f1_pm5.17 a_wo f0_pm5.17 f1_pm5.17 a_wa a_wn a_wa p_3bitrri $.
$}

$(Theorem *5.15 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)

${
	$v ph ps  $.
	f0_pm5.15 $f wff ph $.
	f1_pm5.15 $f wff ps $.
	p_pm5.15 $p |- ( ( ph <-> ps ) \/ ( ph <-> -. ps ) ) $= f0_pm5.15 f1_pm5.15 p_xor3 f0_pm5.15 f1_pm5.15 a_wb a_wn f0_pm5.15 f1_pm5.15 a_wn a_wb p_biimpi f0_pm5.15 f1_pm5.15 a_wb f0_pm5.15 f1_pm5.15 a_wn a_wb p_orri $.
$}

$(Theorem *5.16 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 17-Oct-2013.) $)

${
	$v ph ps  $.
	f0_pm5.16 $f wff ph $.
	f1_pm5.16 $f wff ps $.
	p_pm5.16 $p |- -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) ) $= f0_pm5.16 f1_pm5.16 p_pm5.18 f0_pm5.16 f1_pm5.16 a_wb f0_pm5.16 f1_pm5.16 a_wn a_wb a_wn p_biimpi f0_pm5.16 f1_pm5.16 a_wb f0_pm5.16 f1_pm5.16 a_wn a_wb p_imnan f0_pm5.16 f1_pm5.16 a_wb f0_pm5.16 f1_pm5.16 a_wn a_wb a_wn a_wi f0_pm5.16 f1_pm5.16 a_wb f0_pm5.16 f1_pm5.16 a_wn a_wb a_wa a_wn p_mpbi $.
$}

$(Two ways to express "exclusive or."  Theorem *5.22 of [WhiteheadRussell]
     p. 124.  (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf
     Lammen, 22-Jan-2013.) $)

${
	$v ph ps  $.
	f0_xor $f wff ph $.
	f1_xor $f wff ps $.
	p_xor $p |- ( -. ( ph <-> ps ) <-> ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $= f0_xor f1_xor p_iman f1_xor f0_xor p_iman f0_xor f1_xor a_wi f0_xor f1_xor a_wn a_wa a_wn f1_xor f0_xor a_wi f1_xor f0_xor a_wn a_wa a_wn p_anbi12i f0_xor f1_xor p_dfbi2 f0_xor f1_xor a_wn a_wa f1_xor f0_xor a_wn a_wa p_ioran f0_xor f1_xor a_wi f1_xor f0_xor a_wi a_wa f0_xor f1_xor a_wn a_wa a_wn f1_xor f0_xor a_wn a_wa a_wn a_wa f0_xor f1_xor a_wb f0_xor f1_xor a_wn a_wa f1_xor f0_xor a_wn a_wa a_wo a_wn p_3bitr4ri f0_xor f1_xor a_wn a_wa f1_xor f0_xor a_wn a_wa a_wo f0_xor f1_xor a_wb p_con1bii $.
$}

$(Two ways to express "exclusive or."  (Contributed by NM, 3-Jan-2005.)
     (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)

${
	$v ph ps  $.
	f0_nbi2 $f wff ph $.
	f1_nbi2 $f wff ps $.
	p_nbi2 $p |- ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $= f0_nbi2 f1_nbi2 p_xor3 f0_nbi2 f1_nbi2 p_pm5.17 f0_nbi2 f1_nbi2 a_wb a_wn f0_nbi2 f1_nbi2 a_wn a_wb f0_nbi2 f1_nbi2 a_wo f0_nbi2 f1_nbi2 a_wa a_wn a_wa p_bitr4i $.
$}

$(An alternate definition of the biconditional.  Theorem *5.23 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 3-Nov-2013.) $)

${
	$v ph ps  $.
	f0_dfbi3 $f wff ph $.
	f1_dfbi3 $f wff ps $.
	p_dfbi3 $p |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) ) $= f0_dfbi3 f1_dfbi3 a_wn p_xor f0_dfbi3 f1_dfbi3 p_pm5.18 f1_dfbi3 p_notnot f1_dfbi3 f1_dfbi3 a_wn a_wn f0_dfbi3 p_anbi2i f0_dfbi3 a_wn f1_dfbi3 a_wn p_ancom f0_dfbi3 f1_dfbi3 a_wa f0_dfbi3 f1_dfbi3 a_wn a_wn a_wa f0_dfbi3 a_wn f1_dfbi3 a_wn a_wa f1_dfbi3 a_wn f0_dfbi3 a_wn a_wa p_orbi12i f0_dfbi3 f1_dfbi3 a_wn a_wb a_wn f0_dfbi3 f1_dfbi3 a_wn a_wn a_wa f1_dfbi3 a_wn f0_dfbi3 a_wn a_wa a_wo f0_dfbi3 f1_dfbi3 a_wb f0_dfbi3 f1_dfbi3 a_wa f0_dfbi3 a_wn f1_dfbi3 a_wn a_wa a_wo p_3bitr4i $.
$}

$(Theorem *5.24 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm5.24 $f wff ph $.
	f1_pm5.24 $f wff ps $.
	p_pm5.24 $p |- ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <-> ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $= f0_pm5.24 f1_pm5.24 p_xor f0_pm5.24 f1_pm5.24 p_dfbi3 f0_pm5.24 f1_pm5.24 a_wb f0_pm5.24 f1_pm5.24 a_wn a_wa f1_pm5.24 f0_pm5.24 a_wn a_wa a_wo f0_pm5.24 f1_pm5.24 a_wa f0_pm5.24 a_wn f1_pm5.24 a_wn a_wa a_wo p_xchnxbi $.
$}

$(Conjunction distributes over exclusive-or, using ` -. ( ph <-> ps ) ` to
     express exclusive-or.  This is one way to interpret the distributive law
     of multiplication over addition in modulo 2 arithmetic.  (Contributed by
     NM, 3-Oct-2008.) $)

${
	$v ph ps ch  $.
	f0_xordi $f wff ph $.
	f1_xordi $f wff ps $.
	f2_xordi $f wff ch $.
	p_xordi $p |- ( ( ph /\ -. ( ps <-> ch ) ) <-> -. ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $= f0_xordi f1_xordi f2_xordi a_wb p_annim f0_xordi f1_xordi f2_xordi p_pm5.32 f0_xordi f1_xordi f2_xordi a_wb a_wn a_wa f0_xordi f1_xordi f2_xordi a_wb a_wi f0_xordi f1_xordi a_wa f0_xordi f2_xordi a_wa a_wb p_xchbinx $.
$}

$(A wff disjoined with truth is true.  (Contributed by NM, 23-May-1999.) $)

${
	$v ph ps  $.
	f0_biort $f wff ph $.
	f1_biort $f wff ps $.
	p_biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $= f0_biort f1_biort p_orc f0_biort f0_biort f1_biort a_wo a_ax-1 f0_biort f0_biort f0_biort f1_biort a_wo p_impbid2 $.
$}

$(Theorem *5.55 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 20-Jan-2013.) $)

${
	$v ph ps  $.
	f0_pm5.55 $f wff ph $.
	f1_pm5.55 $f wff ps $.
	p_pm5.55 $p |- ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ) $= f0_pm5.55 f1_pm5.55 p_biort f0_pm5.55 f0_pm5.55 f0_pm5.55 f1_pm5.55 a_wo p_bicomd f0_pm5.55 f1_pm5.55 p_biorf f0_pm5.55 a_wn f1_pm5.55 f0_pm5.55 f1_pm5.55 a_wo p_bicomd f0_pm5.55 f0_pm5.55 f1_pm5.55 a_wo f0_pm5.55 a_wb f0_pm5.55 f1_pm5.55 a_wo f1_pm5.55 a_wb p_nsyl4 f0_pm5.55 f1_pm5.55 a_wo f1_pm5.55 a_wb f0_pm5.55 f1_pm5.55 a_wo f0_pm5.55 a_wb p_con1i f0_pm5.55 f1_pm5.55 a_wo f0_pm5.55 a_wb f0_pm5.55 f1_pm5.55 a_wo f1_pm5.55 a_wb p_orri $.
$}


