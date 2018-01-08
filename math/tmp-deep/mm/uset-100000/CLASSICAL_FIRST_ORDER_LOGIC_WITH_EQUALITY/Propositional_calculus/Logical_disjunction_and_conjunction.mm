
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_equivalence.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical disjunction and conjunction

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Here we define disjunction (logical 'or') ` \/ ` ( ~ df-or ) and conjunction
  (logical 'and') ` /\ ` ( ~ df-an ). We also define various rules for
  simplifying and applying them, e.g., ~ olc , ~ orc , and ~ orcom .

$)

  $( Declare connectives for disjunction ('or') and conjunction ('and'). $)
  $c \/ $. $( Vee (read:  'or') $)
  $c /\ $. $( Wedge (read:  'and') $)

  $( Extend wff definition to include disjunction ('or'). $)
  wo $a wff ( ph \/ ps ) $.
  $( Extend wff definition to include conjunction ('and'). $)
  wa $a wff ( ph /\ ps ) $.

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
  df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.

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
  df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

  $( Theorem *4.64 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.64 $p |- ( ( -. ph -> ps ) <-> ( ph \/ ps ) ) $=
    wph wps wo wph wn wps wi wph wps df-or bicomi $.

  $( Theorem *2.53 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.53 $p |- ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $=
    wph wps wo wph wn wps wi wph wps df-or biimpi $.

  $( Theorem *2.54 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.54 $p |- ( ( -. ph -> ps ) -> ( ph \/ ps ) ) $=
    wph wps wo wph wn wps wi wph wps df-or biimpri $.

  ${
    ori.1 $e |- ( ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by NM,
       11-Jun-1994.) $)
    ori $p |- ( -. ph -> ps ) $=
      wph wps wo wph wn wps wi ori.1 wph wps df-or mpbi $.
  $}

  ${
    orri.1 $e |- ( -. ph -> ps ) $.
    $( Infer implication from disjunction.  (Contributed by NM,
       11-Jun-1994.) $)
    orri $p |- ( ph \/ ps ) $=
      wph wps wo wph wn wps wi orri.1 wph wps df-or mpbir $.
  $}

  ${
    ord.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Deduce implication from disjunction.  (Contributed by NM,
       18-May-1994.) $)
    ord $p |- ( ph -> ( -. ps -> ch ) ) $=
      wph wps wch wo wps wn wch wi ord.1 wps wch df-or sylib $.
  $}

  ${
    orrd.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduce implication from disjunction.  (Contributed by NM,
       27-Nov-1995.) $)
    orrd $p |- ( ph -> ( ps \/ ch ) ) $=
      wph wps wn wch wi wps wch wo orrd.1 wps wch pm2.54 syl $.
  $}

  ${
    jaoi.1 $e |- ( ph -> ps ) $.
    jaoi.2 $e |- ( ch -> ps ) $.
    $( Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 5-Apr-1994.) $)
    jaoi $p |- ( ( ph \/ ch ) -> ps ) $=
      wph wch wo wph wps wph wch wo wph wn wch wps wph wch pm2.53 jaoi.2 syl6
      jaoi.1 pm2.61d2 $.
  $}

  ${
    jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 18-Aug-1994.) $)
    jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $=
      wps wth wo wph wch wps wph wch wi wth wph wps wch jaod.1 com12 wph wth
      wch jaod.2 com12 jaoi com12 $.

    jaod.3 $e |- ( ph -> ( ps \/ th ) ) $.
    $( Eliminate a disjunction in a deduction.  (Contributed by Mario Carneiro,
       29-May-2016.) $)
    mpjaod $p |- ( ph -> ch ) $=
      wph wps wth wo wch jaod.3 wph wps wch wth jaod.1 jaod.2 jaod mpd $.
  $}

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107.  (Contributed by NM, 12-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 21-Jul-2012.) $)
  orel1 $p |- ( -. ph -> ( ( ph \/ ps ) -> ps ) ) $=
    wph wps wo wph wn wps wph wps pm2.53 com12 $.

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107.  (Contributed by NM, 12-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 5-Apr-2013.) $)
  orel2 $p |- ( -. ph -> ( ( ps \/ ph ) -> ps ) ) $=
    wph wn wps wps wph wph wn wps idd wph wps pm2.21 jaod $.

  $( Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96.
     (Contributed by NM, 30-Aug-1993.) $)
  olc $p |- ( ph -> ( ps \/ ph ) ) $=
    wph wps wph wph wps wn ax-1 orrd $.

  $( Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 30-Aug-1993.) $)
  orc $p |- ( ph -> ( ph \/ ps ) ) $=
    wph wph wps wph wps pm2.24 orrd $.

  $( Axiom *1.4 of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)
  pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
    wph wps wph wo wps wph wps olc wps wph orc jaoi $.

  $( Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 15-Nov-2012.) $)
  orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $=
    wph wps wo wps wph wo wph wps pm1.4 wps wph pm1.4 impbii $.

  ${
    orcomd.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Commutation of disjuncts in consequent.  (Contributed by NM,
       2-Dec-2010.) $)
    orcomd $p |- ( ph -> ( ch \/ ps ) ) $=
      wph wps wch wo wch wps wo orcomd.1 wps wch orcom sylib $.
  $}

  ${
    orcoms.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Commutation of disjuncts in antecedent.  (Contributed by NM,
       2-Dec-2012.) $)
    orcoms $p |- ( ( ps \/ ph ) -> ch ) $=
      wps wph wo wph wps wo wch wps wph pm1.4 orcoms.1 syl $.
  $}

  ${
    orci.1 $e |- ph $.
    $( Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
    orci $p |- ( ph \/ ps ) $=
      wph wps wph wps orci.1 pm2.24i orri $.

    $( Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
    olci $p |- ( ps \/ ph ) $=
      wps wph wph wps wn orci.1 a1i orri $.
  $}

  ${
    orcd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IR ( ` \/ ` insertion right), see ~ natded .  (Contributed
       by NM, 20-Sep-2007.) $)
    orcd $p |- ( ph -> ( ps \/ ch ) ) $=
      wph wps wps wch wo orcd.1 wps wch orc syl $.

    $( Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IL ( ` \/ ` insertion left), see ~ natded .  (Contributed by
       NM, 11-Apr-2008.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    olcd $p |- ( ph -> ( ch \/ ps ) ) $=
      wph wps wch wph wps wch orcd.1 orcd orcomd $.
  $}

  ${
    orcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct. _Notational convention_:  We sometimes
       suffix with "s" the label of an inference that manipulates an
       antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof.  (Contributed by NM, 21-Jun-1994.) $)
    orcs $p |- ( ph -> ch ) $=
      wph wph wps wo wch wph wps orc orcs.1 syl $.
  $}

  ${
    olcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct.  (Contributed by NM, 21-Jun-1994.)
       (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    olcs $p |- ( ps -> ch ) $=
      wps wph wch wph wps wch olcs.1 orcoms orcs $.
  $}

  $( Theorem *2.07 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.07 $p |- ( ph -> ( ph \/ ph ) ) $=
    wph wph olc $.

  $( Theorem *2.45 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.45 $p |- ( -. ( ph \/ ps ) -> -. ph ) $=
    wph wph wps wo wph wps orc con3i $.

  $( Theorem *2.46 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.46 $p |- ( -. ( ph \/ ps ) -> -. ps ) $=
    wps wph wps wo wps wph olc con3i $.

  $( Theorem *2.47 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.47 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) ) $=
    wph wps wo wn wph wn wps wph wps pm2.45 orcd $.

  $( Theorem *2.48 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.48 $p |- ( -. ( ph \/ ps ) -> ( ph \/ -. ps ) ) $=
    wph wps wo wn wps wn wph wph wps pm2.46 olcd $.

  $( Theorem *2.49 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.49 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) ) $=
    wph wps wo wn wps wn wph wn wph wps pm2.46 olcd $.

  $( Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.) $)
  pm2.67-2 $p |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) ) $=
    wph wph wch wo wps wph wch orc imim1i $.

  $( Theorem *2.67 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.67 $p |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $=
    wph wps wps pm2.67-2 $.

  $( Theorem *2.25 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.25 $p |- ( ph \/ ( ( ph \/ ps ) -> ps ) ) $=
    wph wph wps wo wps wi wph wps orel1 orri $.

  $( A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 23-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 18-Nov-2012.) $)
  biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $=
    wph wn wps wph wps wo wps wph olc wph wps orel1 impbid2 $.

  $( A wff is equivalent to its negated disjunction with falsehood.
     (Contributed by NM, 9-Jul-2012.) $)
  biortn $p |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) ) $=
    wph wph wn wn wps wph wn wps wo wb wph notnot1 wph wn wps biorf syl $.

  ${
    biorfi.1 $e |- -. ph $.
    $( A wff is equivalent to its disjunction with falsehood.  (Contributed by
       NM, 23-Mar-1995.) $)
    biorfi $p |- ( ps <-> ( ps \/ ph ) ) $=
      wph wn wps wps wph wo wb biorfi.1 wph wn wps wps wph wo wps wph orc wph
      wps orel2 impbid2 ax-mp $.
  $}

  $( Theorem *2.621 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.621 $p |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $=
    wph wps wi wph wps wps wph wps wi id wph wps wi wps idd jaod $.

  $( Theorem *2.62 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Dec-2013.) $)
  pm2.62 $p |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    wph wps wi wph wps wo wps wph wps pm2.621 com12 $.

  $( Theorem *2.68 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.68 $p |- ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) $=
    wph wps wi wps wi wph wps wph wps wps jarl orrd $.

  $( Logical 'or' expressed in terms of implication only.  Theorem *5.25 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 12-Aug-2004.)  (Proof
     shortened by Wolf Lammen, 20-Oct-2012.) $)
  dfor2 $p |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) $=
    wph wps wo wph wps wi wps wi wph wps pm2.62 wph wps pm2.68 impbii $.

  $( Implication in terms of disjunction.  Theorem *4.6 of [WhiteheadRussell]
     p. 120.  (Contributed by NM, 5-Aug-1993.) $)
  imor $p |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) $=
    wph wps wi wph wn wn wps wi wph wn wps wo wph wph wn wn wps wph notnot
    imbi1i wph wn wps df-or bitr4i $.

  ${
    imori.1 $e |- ( ph -> ps ) $.
    $( Infer disjunction from implication.  (Contributed by NM,
       12-Mar-2012.) $)
    imori $p |- ( -. ph \/ ps ) $=
      wph wps wi wph wn wps wo imori.1 wph wps imor mpbi $.
  $}

  ${
    imorri.1 $e |- ( -. ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    imorri $p |- ( ph -> ps ) $=
      wph wps wi wph wn wps wo imorri.1 wph wps imor mpbir $.
  $}

  $( Law of excluded middle, also called the principle of _tertium non datur_.
     Theorem *2.11 of [WhiteheadRussell] p. 101.  It says that something is
     either true or not true; there are no in-between values of truth.  This is
     an essential distinction of our classical logic and is not a theorem of
     intuitionistic logic.  (Contributed by NM, 5-Aug-1993.) $)
  exmid $p |- ( ph \/ -. ph ) $=
    wph wph wn wph wn id orri $.

  $( Law of excluded middle in a context.  (Contributed by Mario Carneiro,
     9-Feb-2017.) $)
  exmidd $p |- ( ph -> ( ps \/ -. ps ) ) $=
    wps wps wn wo wph wps exmid a1i $.

  $( Theorem *2.1 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
  pm2.1 $p |- ( -. ph \/ ph ) $=
    wph wph wph id imori $.

  $( Theorem *2.13 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.13 $p |- ( ph \/ -. -. -. ph ) $=
    wph wph wn wn wn wph wn notnot1 orri $.

  $( Theorem *4.62 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.62 $p |- ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) $=
    wph wps wn imor $.

  $( Theorem *4.66 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.66 $p |- ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) ) $=
    wph wps wn pm4.64 $.

  $( Theorem *4.63 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.63 $p |- ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) $=
    wph wps wa wph wps wn wi wn wph wps df-an bicomi $.

  $( Express implication in terms of conjunction.  (Contributed by NM,
     9-Apr-1994.) $)
  imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $=
    wph wps wa wph wps wn wi wph wps df-an con2bii $.

  ${
    imnani.1 $e |- -. ( ph /\ ps ) $.
    $( Express implication in terms of conjunction.  (Contributed by Mario
       Carneiro, 28-Sep-2015.) $)
    imnani $p |- ( ph -> -. ps ) $=
      wph wps wn wi wph wps wa wn imnani.1 wph wps imnan mpbir $.
  $}

  $( Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 30-Oct-2012.) $)
  iman $p |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) $=
    wph wps wi wph wps wn wn wi wph wps wn wa wn wps wps wn wn wph wps notnot
    imbi2i wph wps wn imnan bitri $.

  $( Express conjunction in terms of implication.  (Contributed by NM,
     2-Aug-1994.) $)
  annim $p |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) $=
    wph wps wi wph wps wn wa wph wps iman con2bii $.

  $( Theorem *4.61 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.61 $p |- ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) ) $=
    wph wps wn wa wph wps wi wn wph wps annim bicomi $.

  $( Theorem *4.65 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.65 $p |- ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) ) $=
    wph wn wps pm4.61 $.

  $( Theorem *4.67 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.67 $p |- ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) $=
    wph wn wps pm4.63 $.

  ${
    imp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Eric Schmidt, 22-Dec-2006.) $)
    imp $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wa wph wps wn wi wn wch wph wps df-an wph wps wch imp.1 impi
      sylbi $.

    $( Importation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    impcom $p |- ( ( ps /\ ph ) -> ch ) $=
      wps wph wch wph wps wch imp.1 com12 imp $.
  $}

  ${
    imp3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation deduction.  (Contributed by NM, 31-Mar-1994.) $)
    imp3a $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      wps wch wa wph wth wps wch wph wth wi wph wps wch wth imp3.1 com3l imp
      com12 $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      wph wps wa wch wth wph wps wch wth wi imp3.1 imp imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      wph wps wch wa wth wph wps wch wth imp3.1 imp3a imp $.
  $}

  ${
    exp.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  A translation of natural deduction
       rule ` -> ` I ( ` -> ` introduction), see ~ natded .  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)
    ex $p |- ( ph -> ( ps -> ch ) ) $=
      wph wps wch wph wps wn wi wn wph wps wa wch wph wps df-an exp.1 sylbir
      expi $.

    $( Exportation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    expcom $p |- ( ps -> ( ph -> ch ) ) $=
      wph wps wch wph wps wch exp.1 ex com12 $.
  $}

  ${
    exp3a.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Exportation deduction.  (Contributed by NM, 20-Aug-1993.) $)
    exp3a $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wps wch wph wth wps wch wph wth wi wph wps wch wa wth exp3a.1 com12 ex
      com3r $.

    $( A deduction version of exportation, followed by importation.
       (Contributed by NM, 6-Sep-2008.) $)
    expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      wph wps wch wth wi wph wps wch wth exp3a.1 exp3a imp $.
  $}

  ${
    impancom.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Mixed importation/commutation inference.  (Contributed by NM,
       22-Jun-2013.) $)
    impancom $p |- ( ( ph /\ ch ) -> ( ps -> th ) ) $=
      wph wch wps wth wi wph wps wch wth wph wps wch wth wi impancom.1 ex com23
      imp $.
  $}

  ${
    con3and.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Variant of ~ con3d with importation.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    con3and $p |- ( ( ph /\ -. ch ) -> -. ps ) $=
      wph wch wn wps wn wph wps wch con3and.1 con3d imp $.
  $}

  ${
    pm2.01da.1 $e |- ( ( ph /\ ps ) -> -. ps ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    pm2.01da $p |- ( ph -> -. ps ) $=
      wph wps wph wps wps wn pm2.01da.1 ex pm2.01d $.
  $}

  ${
    pm2.18da.1 $e |- ( ( ph /\ -. ps ) -> ps ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    pm2.18da $p |- ( ph -> ps ) $=
      wph wps wph wps wn wps pm2.18da.1 ex pm2.18d $.
  $}

  $( Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.3 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    wph wps wa wch wi wph wps wch wph wps wa wch wi id exp3a $.

  $( Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.31 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
    wph wps wch wi wi wph wps wch wph wps wch wi wi id imp3a $.

  $( Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Mar-2013.) $)
  impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $=
    wph wps wa wch wi wph wps wch wi wi wph wps wch pm3.3 wph wps wch pm3.31
    impbii $.

  $( Join antecedents with conjunction.  Theorem *3.2 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 12-Nov-2012.) $)
  pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    wph wps wph wps wa wph wps wa id ex $.

  $( Join antecedents with conjunction.  Theorem *3.21 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.) $)
  pm3.21 $p |- ( ph -> ( ps -> ( ps /\ ph ) ) ) $=
    wps wph wps wph wa wps wph pm3.2 com12 $.

  $( Theorem *3.22 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Nov-2012.) $)
  pm3.22 $p |- ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
    wph wps wps wph wa wph wps pm3.21 imp $.

  $( Commutative law for conjunction.  Theorem *4.3 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 25-Jun-1998.)  (Proof shortened by Wolf
     Lammen, 4-Nov-2012.) $)
  ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $=
    wph wps wa wps wph wa wph wps pm3.22 wps wph pm3.22 impbii $.

  ${
    ancomd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Commutation of conjuncts in consequent.  (Contributed by Jeff Hankins,
       14-Aug-2009.) $)
    ancomd $p |- ( ph -> ( ch /\ ps ) ) $=
      wph wps wch wa wch wps wa ancomd.1 wps wch ancom sylib $.
  $}

  ${
    ancoms.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference commuting conjunction in antecedent.  (Contributed by NM,
       21-Apr-1994.) $)
    ancoms $p |- ( ( ps /\ ph ) -> ch ) $=
      wps wph wch wph wps wch ancoms.1 expcom imp $.
  $}

  ${
    ancomsd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction commuting conjunction in antecedent.  (Contributed by NM,
       12-Dec-2004.) $)
    ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $=
      wch wps wa wps wch wa wph wth wch wps ancom ancomsd.1 syl5bi $.
  $}

  ${
    pm3.2i.1 $e |- ph $.
    pm3.2i.2 $e |- ps $.
    $( Infer conjunction of premises.  (Contributed by NM, 5-Aug-1993.) $)
    pm3.2i $p |- ( ph /\ ps ) $=
      wph wps wph wps wa pm3.2i.1 pm3.2i.2 wph wps pm3.2 mp2 $.
  $}

  $( Nested conjunction of antecedents.  (Contributed by NM, 5-Aug-1993.) $)
  pm3.43i $p |- ( ( ph -> ps )
      -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $=
    wps wch wps wch wa wph wps wch pm3.2 imim3i $.

  $( Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simpl $p |- ( ( ph /\ ps ) -> ph ) $=
    wph wps wph wph wps ax-1 imp $.

  ${
    simpli.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
    simpli $p |- ph $=
      wph wps wa wph simpli.1 wph wps simpl ax-mp $.
  $}

  ${
    simpld.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  A translation of natural deduction
       rule ` /\ ` EL ( ` /\ ` elimination left), see ~ natded .  (Contributed
       by NM, 5-Aug-1993.) $)
    simpld $p |- ( ph -> ps ) $=
      wph wps wch wa wps simpld.1 wps wch simpl syl $.
  $}

  ${
    simplbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
    simplbi $p |- ( ph -> ps ) $=
      wph wps wch wph wps wch wa simplbi.1 biimpi simpld $.
  $}

  $( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simpr $p |- ( ( ph /\ ps ) -> ps ) $=
    wph wps wps wph wps idd imp $.

  ${
    simpri.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
    simpri $p |- ps $=
      wph wps wa wps simpri.1 wph wps simpr ax-mp $.
  $}

  ${
    simprd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 5-Aug-1993.)  A
       translation of natural deduction rule ` /\ ` ER ( ` /\ ` elimination
       right), see ~ natded .  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    simprd $p |- ( ph -> ch ) $=
      wph wch wps wph wps wch simprd.1 ancomd simpld $.
  $}

  ${
    simprbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
    simprbi $p |- ( ph -> ch ) $=
      wph wps wch wph wps wch wa simprbi.1 biimpi simprd $.
  $}

  ${
    adantr.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 30-Aug-1993.) $)
    adantr $p |- ( ( ph /\ ch ) -> ps ) $=
      wph wch wps wph wps wch adantr.1 a1d imp $.
  $}

  ${
    adantl.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 30-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
    adantl $p |- ( ( ch /\ ph ) -> ps ) $=
      wph wch wps wph wps wch adantl.1 adantr ancoms $.
  $}

  ${
    adantld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 4-May-1994.)  (Proof shortened by Wolf Lammen, 20-Dec-2012.) $)
    adantld $p |- ( ph -> ( ( th /\ ps ) -> ch ) ) $=
      wth wps wa wps wph wch wth wps simpr adantld.1 syl5 $.
  $}

  ${
    adantrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 4-May-1994.) $)
    adantrd $p |- ( ph -> ( ( ps /\ th ) -> ch ) ) $=
      wps wth wa wps wph wch wps wth simpl adantrd.1 syl5 $.
  $}

  ${
    mpan9.1 $e |- ( ph -> ps ) $.
    mpan9.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Modus ponens conjoining dissimilar antecedents.  (Contributed by NM,
       1-Feb-2008.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    mpan9 $p |- ( ( ph /\ ch ) -> th ) $=
      wch wph wth wph wps wch wth mpan9.1 mpan9.2 syl5 impcom $.
  $}

  ${
    syldan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    syldan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    $( A syllogism deduction with conjoined antecedents.  (Contributed by NM,
       24-Feb-2005.)  (Proof shortened by Wolf Lammen, 6-Apr-2013.) $)
    syldan $p |- ( ( ph /\ ps ) -> th ) $=
      wch wph wps wa wth syldan.1 wch wph wth wps wph wch wth syldan.2 expcom
      adantrd mpcom $.
  $}

  ${
    sylan.1 $e |- ( ph -> ps ) $.
    sylan.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 21-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Nov-2012.) $)
    sylan $p |- ( ( ph /\ ch ) -> th ) $=
      wph wps wch wth sylan.1 wps wch wth sylan.2 expcom mpan9 $.
  $}

  ${
    sylanb.1 $e |- ( ph <-> ps ) $.
    sylanb.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    sylanb $p |- ( ( ph /\ ch ) -> th ) $=
      wph wps wch wth wph wps sylanb.1 biimpi sylanb.2 sylan $.
  $}

  ${
    sylanbr.1 $e |- ( ps <-> ph ) $.
    sylanbr.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    sylanbr $p |- ( ( ph /\ ch ) -> th ) $=
      wph wps wch wth wps wph sylanbr.1 biimpri sylanbr.2 sylan $.
  $}

  ${
    sylan2.1 $e |- ( ph -> ch ) $.
    sylan2.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 21-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Nov-2012.) $)
    sylan2 $p |- ( ( ps /\ ph ) -> th ) $=
      wps wph wch wth wph wch wps sylan2.1 adantl sylan2.2 syldan $.
  $}

  ${
    sylan2b.1 $e |- ( ph <-> ch ) $.
    sylan2b.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 21-Apr-1994.) $)
    sylan2b $p |- ( ( ps /\ ph ) -> th ) $=
      wph wps wch wth wph wch sylan2b.1 biimpi sylan2b.2 sylan2 $.
  $}

  ${
    sylan2br.1 $e |- ( ch <-> ph ) $.
    sylan2br.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 21-Apr-1994.) $)
    sylan2br $p |- ( ( ps /\ ph ) -> th ) $=
      wph wps wch wth wch wph sylan2br.1 biimpri sylan2br.2 sylan2 $.
  $}

  ${
    syl2an.1 $e |- ( ph -> ps ) $.
    syl2an.2 $e |- ( ta -> ch ) $.
    syl2an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference.  (Contributed by NM, 31-Jan-1997.) $)
    syl2an $p |- ( ( ph /\ ta ) -> th ) $=
      wta wph wch wth syl2an.2 wph wps wch wth syl2an.1 syl2an.3 sylan sylan2
      $.

    $( A double syllogism inference.  (Contributed by NM, 17-Sep-2013.) $)
    syl2anr $p |- ( ( ta /\ ph ) -> th ) $=
      wph wta wth wph wps wch wth wta syl2an.1 syl2an.2 syl2an.3 syl2an ancoms
      $.
  $}

  ${
    syl2anb.1 $e |- ( ph <-> ps ) $.
    syl2anb.2 $e |- ( ta <-> ch ) $.
    syl2anb.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference.  (Contributed by NM, 29-Jul-1999.) $)
    syl2anb $p |- ( ( ph /\ ta ) -> th ) $=
      wta wph wch wth syl2anb.2 wph wps wch wth syl2anb.1 syl2anb.3 sylanb
      sylan2b $.
  $}

  ${
    syl2anbr.1 $e |- ( ps <-> ph ) $.
    syl2anbr.2 $e |- ( ch <-> ta ) $.
    syl2anbr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference.  (Contributed by NM, 29-Jul-1999.) $)
    syl2anbr $p |- ( ( ph /\ ta ) -> th ) $=
      wta wph wch wth syl2anbr.2 wph wps wch wth syl2anbr.1 syl2anbr.3 sylanbr
      sylan2br $.
  $}

  ${
    syland.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syland.2 $e |- ( ph -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
    syland $p |- ( ph -> ( ( ps /\ th ) -> ta ) ) $=
      wph wps wth wta wph wps wch wth wta wi syland.1 wph wch wth wta syland.2
      exp3a syld imp3a $.
  $}

  ${
    sylan2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan2d.2 $e |- ( ph -> ( ( th /\ ch ) -> ta ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
    sylan2d $p |- ( ph -> ( ( th /\ ps ) -> ta ) ) $=
      wph wps wth wta wph wps wch wth wta sylan2d.1 wph wth wch wta sylan2d.2
      ancomsd syland ancomsd $.
  $}

  ${
    syl2and.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl2and.2 $e |- ( ph -> ( th -> ta ) ) $.
    syl2and.3 $e |- ( ph -> ( ( ch /\ ta ) -> et ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
    syl2and $p |- ( ph -> ( ( ps /\ th ) -> et ) ) $=
      wph wps wch wth wet syl2and.1 wph wth wta wch wet syl2and.2 syl2and.3
      sylan2d syland $.
  $}

  ${
    biimpa.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpa $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wch biimpa.1 biimpd imp $.

    $( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpar $p |- ( ( ph /\ ch ) -> ps ) $=
      wph wch wps wph wps wch biimpa.1 biimprd imp $.

    $( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpac $p |- ( ( ps /\ ph ) -> ch ) $=
      wps wph wch wph wps wch biimpa.1 biimpcd imp $.

    $( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimparc $p |- ( ( ch /\ ph ) -> ps ) $=
      wch wph wps wph wps wch biimpa.1 biimprcd imp $.
  $}

  $( Negated conjunction in terms of disjunction (De Morgan's law).  Theorem
     *4.51 of [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  ianor $p |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) $=
    wph wps wa wn wph wps wn wi wph wn wps wn wo wph wps imnan wph wps pm4.62
    bitr3i $.

  $( Conjunction in terms of disjunction (De Morgan's law).  Theorem *4.5 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 3-Nov-2012.) $)
  anor $p |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) $=
    wph wn wps wn wo wph wps wa wph wps wa wn wph wn wps wn wo wph wps ianor
    bicomi con2bii $.

  $( Negated disjunction in terms of conjunction (De Morgan's law).  Compare
     Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    wph wn wps wi wph wn wps wn wa wph wps wo wph wps pm4.65 wph wps pm4.64
    xchnxbi $.

  $( Theorem *4.52 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Nov-2012.) $)
  pm4.52 $p |- ( ( ph /\ -. ps ) <-> -. ( -. ph \/ ps ) ) $=
    wph wps wn wa wph wps wi wph wn wps wo wph wps annim wph wps imor xchbinx
    $.

  $( Theorem *4.53 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.53 $p |- ( -. ( ph /\ -. ps ) <-> ( -. ph \/ ps ) ) $=
    wph wn wps wo wph wps wn wa wn wph wps wn wa wph wn wps wo wph wps pm4.52
    con2bii bicomi $.

  $( Theorem *4.54 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Nov-2012.) $)
  pm4.54 $p |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $=
    wph wn wps wa wph wn wps wn wi wph wps wn wo wph wn wps df-an wph wps
    pm4.66 xchbinx $.

  $( Theorem *4.55 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.55 $p |- ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) ) $=
    wph wps wn wo wph wn wps wa wn wph wn wps wa wph wps wn wo wph wps pm4.54
    con2bii bicomi $.

  $( Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.56 $p |- ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) ) $=
    wph wps wo wn wph wn wps wn wa wph wps ioran bicomi $.

  $( Disjunction in terms of conjunction (De Morgan's law).  Compare Theorem
     *4.57 of [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  oran $p |- ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) ) $=
    wph wn wps wn wa wph wps wo wph wps pm4.56 con2bii $.

  $( Theorem *4.57 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.57 $p |- ( -. ( -. ph /\ -. ps ) <-> ( ph \/ ps ) ) $=
    wph wps wo wph wn wps wn wa wn wph wps oran bicomi $.

  $( Theorem *3.1 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.1 $p |- ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) ) $=
    wph wps wa wph wn wps wn wo wn wph wps anor biimpi $.

  $( Theorem *3.11 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.11 $p |- ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) ) $=
    wph wps wa wph wn wps wn wo wn wph wps anor biimpri $.

  $( Theorem *3.12 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.12 $p |- ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) $=
    wph wn wps wn wo wph wps wa wph wps pm3.11 orri $.

  $( Theorem *3.13 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.13 $p |- ( -. ( ph /\ ps ) -> ( -. ph \/ -. ps ) ) $=
    wph wn wps wn wo wph wps wa wph wps pm3.11 con1i $.

  $( Theorem *3.14 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.14 $p |- ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) ) $=
    wph wps wa wph wn wps wn wo wph wps pm3.1 con2i $.

  $( Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Mar-1994.) $)
  iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $=
    wph wps wps wph wa wph wps pm3.21 wps wph simpl impbid1 $.

  $( Introduction of antecedent as conjunct.  (Contributed by NM,
     5-Dec-1995.) $)
  ibar $p |- ( ph -> ( ps <-> ( ph /\ ps ) ) ) $=
    wph wps wph wps wa wph wps pm3.2 wph wps simpr impbid1 $.

  ${
    biantru.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       5-Aug-1993.) $)
    biantru $p |- ( ps <-> ( ps /\ ph ) ) $=
      wph wps wps wph wa wb biantru.1 wph wps iba ax-mp $.
  $}

  ${
    biantrur.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       3-Aug-1994.) $)
    biantrur $p |- ( ps <-> ( ph /\ ps ) ) $=
      wph wps wph wps wa wb biantrur.1 wph wps ibar ax-mp $.
  $}

  ${
    biantrud.1 $e |- ( ph -> ps ) $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       2-Aug-1994.)  (Proof shortened by Wolf Lammen, 23-Oct-2013.) $)
    biantrud $p |- ( ph -> ( ch <-> ( ch /\ ps ) ) ) $=
      wph wps wch wch wps wa wb biantrud.1 wps wch iba syl $.

    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       1-May-1995.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    biantrurd $p |- ( ph -> ( ch <-> ( ps /\ ch ) ) ) $=
      wph wps wch wps wch wa wb biantrud.1 wps wch ibar syl $.
  $}

  ${
    jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of two
       implications.  (Contributed by NM, 30-Sep-1999.) $)
    jaao $p |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) ) $=
      wph wth wa wps wch wta wph wps wch wi wth jaao.1 adantr wth wta wch wi
      wph jaao.2 adantl jaod $.

    $( Inference disjoining and conjoining the antecedents of two
       implications.  (Contributed by Stefan Allan, 1-Nov-2008.) $)
    jaoa $p |- ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) ) $=
      wph wps wta wa wch wi wth wph wps wch wta jaao.1 adantrd wth wta wch wps
      jaao.2 adantld jaoi $.
  $}

  $( Theorem *3.44 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
  pm3.44 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) )
      -> ( ( ps \/ ch ) -> ph ) ) $=
    wps wph wi wps wph wch wph wi wch wps wph wi id wch wph wi id jaao $.

  $( Disjunction of antecedents.  Compare Theorem *3.44 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 5-Apr-1994.)  (Proof shortened by Wolf
     Lammen, 4-Apr-2013.) $)
  jao $p |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) ) $=
    wph wps wi wch wps wi wph wch wo wps wi wps wph wch pm3.44 ex $.

  $( Axiom *1.2 of [WhiteheadRussell] p. 96, which they call "Taut".
     (Contributed by NM, 3-Jan-2005.) $)
  pm1.2 $p |- ( ( ph \/ ph ) -> ph ) $=
    wph wph wph wph id wph id jaoi $.

  $( Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 16-Apr-2011.)  (Proof shortened by Wolf Lammen, 10-Mar-2013.) $)
  oridm $p |- ( ( ph \/ ph ) <-> ph ) $=
    wph wph wo wph wph pm1.2 wph pm2.07 impbii $.

  $( Theorem *4.25 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.25 $p |- ( ph <-> ( ph \/ ph ) ) $=
    wph wph wo wph wph oridm bicomi $.

  ${
    orim12i.1 $e |- ( ph -> ps ) $.
    orim12i.2 $e |- ( ch -> th ) $.
    $( Disjoin antecedents and consequents of two premises.  (Contributed by
       NM, 6-Jun-1994.)  (Proof shortened by Wolf Lammen, 25-Jul-2012.) $)
    orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $=
      wph wps wth wo wch wph wps wth orim12i.1 orcd wch wth wps orim12i.2 olcd
      jaoi $.
  $}

  ${
    orim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
    orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $=
      wph wps wch wch orim1i.1 wch id orim12i $.

    $( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
    orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $=
      wch wch wph wps wch id orim1i.1 orim12i $.
  $}

  ${
    orbi2i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a left disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 12-Dec-2012.) $)
    orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $=
      wch wph wo wch wps wo wph wps wch wph wps orbi2i.1 biimpi orim2i wps wph
      wch wph wps orbi2i.1 biimpri orim2i impbii $.

    $( Inference adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $=
      wph wch wo wch wph wo wch wps wo wps wch wo wph wch orcom wph wps wch
      orbi2i.1 orbi2i wch wps orcom 3bitri $.
  $}

  ${
    orbi12i.1 $e |- ( ph <-> ps ) $.
    orbi12i.2 $e |- ( ch <-> th ) $.
    $( Infer the disjunction of two equivalences.  (Contributed by NM,
       5-Aug-1993.) $)
    orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $=
      wph wch wo wph wth wo wps wth wo wch wth wph orbi12i.2 orbi2i wph wps wth
      orbi12i.1 orbi1i bitri $.
  $}

  $( Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)
  pm1.5 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ) $=
    wph wps wph wch wo wo wps wch wo wph wph wch wo wps wph wch orc olcd wch
    wph wch wo wps wch wph olc orim2i jaoi $.

  $( Swap two disjuncts.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 14-Nov-2012.) $)
  or12 $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ) $=
    wph wps wch wo wo wps wph wch wo wo wph wps wch pm1.5 wps wph wch pm1.5
    impbii $.

  $( Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
  orass $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    wph wps wo wch wo wch wph wps wo wo wph wch wps wo wo wph wps wch wo wo wph
    wps wo wch orcom wch wph wps or12 wch wps wo wps wch wo wph wch wps orcom
    orbi2i 3bitri $.

  $( Theorem *2.31 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.31 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ) $=
    wph wps wo wch wo wph wps wch wo wo wph wps wch orass biimpri $.

  $( Theorem *2.32 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.32 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ) $=
    wph wps wo wch wo wph wps wch wo wo wph wps wch orass biimpi $.

  $( A rearrangement of disjuncts.  (Contributed by NM, 18-Oct-1995.)  (Proof
     shortened by Andrew Salmon, 26-Jun-2011.) $)
  or32 $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ) $=
    wph wps wo wch wo wph wps wch wo wo wps wph wch wo wo wph wch wo wps wo wph
    wps wch orass wph wps wch or12 wps wph wch wo orcom 3bitri $.

  $( Rearrangement of 4 disjuncts.  (Contributed by NM, 12-Aug-1994.) $)
  or4 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                ( ( ph \/ ch ) \/ ( ps \/ th ) ) ) $=
    wph wps wch wth wo wo wo wph wch wps wth wo wo wo wph wps wo wch wth wo wo
    wph wch wo wps wth wo wo wps wch wth wo wo wch wps wth wo wo wph wps wch
    wth or12 orbi2i wph wps wch wth wo orass wph wch wps wth wo orass 3bitr4i
    $.

  $( Rearrangement of 4 disjuncts.  (Contributed by NM, 10-Jan-2005.) $)
  or42 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                 ( ( ph \/ ch ) \/ ( th \/ ps ) ) ) $=
    wph wps wo wch wth wo wo wph wch wo wps wth wo wo wph wch wo wth wps wo wo
    wph wps wch wth or4 wps wth wo wth wps wo wph wch wo wps wth orcom orbi2i
    bitri $.

  $( Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)
  orordi $p |- ( ( ph \/ ( ps \/ ch ) ) <->
               ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    wph wps wch wo wo wph wph wo wps wch wo wo wph wps wo wph wch wo wo wph wph
    wo wph wps wch wo wph oridm orbi1i wph wph wps wch or4 bitr3i $.

  $( Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)
  orordir $p |- ( ( ( ph \/ ps ) \/ ch ) <->
               ( ( ph \/ ch ) \/ ( ps \/ ch ) ) ) $=
    wph wps wo wch wo wph wps wo wch wch wo wo wph wch wo wps wch wo wo wch wch
    wo wch wph wps wo wch oridm orbi2i wph wps wch wch or4 bitr3i $.

  ${
    jca.1 $e |- ( ph -> ps ) $.
    jca.2 $e |- ( ph -> ch ) $.
    $( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  Equivalent to the natural deduction rule
       ` /\ ` I ( ` /\ ` introduction), see ~ natded .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-Oct-2012.) $)
    jca $p |- ( ph -> ( ps /\ ch ) ) $=
      wph wps wch wps wch wa jca.1 jca.2 wps wch pm3.2 sylc $.
  $}

  ${
    jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    $( Deduction conjoining the consequents of two implications.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
    jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      wph wps wch wth wch wth wa jcad.1 jcad.2 wch wth pm3.2 syl6c $.
  $}

  ${
    jca31.1 $e |- ( ph -> ps ) $.
    jca31.2 $e |- ( ph -> ch ) $.
    jca31.3 $e |- ( ph -> th ) $.
    $( Join three consequents.  (Contributed by Jeff Hankins, 1-Aug-2009.) $)
    jca31 $p |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $=
      wph wps wch wa wth wph wps wch jca31.1 jca31.2 jca jca31.3 jca $.

    $( Join three consequents.  (Contributed by FL, 1-Aug-2009.) $)
    jca32 $p |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $=
      wph wps wch wth wa jca31.1 wph wch wth jca31.2 jca31.3 jca jca $.
  $}

  ${
    jcai.1 $e |- ( ph -> ps ) $.
    jcai.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction replacing implication with conjunction.  (Contributed by NM,
       5-Aug-1993.) $)
    jcai $p |- ( ph -> ( ps /\ ch ) ) $=
      wph wps wch jcai.1 wph wps wch jcai.1 jcai.2 mpd jca $.
  $}

  ${
    jctil.1 $e |- ( ph -> ps ) $.
    jctil.2 $e |- ch $.
    $( Inference conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 31-Dec-1993.) $)
    jctil $p |- ( ph -> ( ch /\ ps ) ) $=
      wph wch wps wch wph jctil.2 a1i jctil.1 jca $.

    $( Inference conjoining a theorem to right of consequent in an
       implication.  (Contributed by NM, 31-Dec-1993.) $)
    jctir $p |- ( ph -> ( ps /\ ch ) ) $=
      wph wps wch jctil.1 wch wph jctil.2 a1i jca $.
  $}

  ${
    jctl.1 $e |- ps $.
    $( Inference conjoining a theorem to the left of a consequent.
       (Contributed by NM, 31-Dec-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)
    jctl $p |- ( ph -> ( ps /\ ph ) ) $=
      wph wph wps wph id jctl.1 jctil $.

    $( Inference conjoining a theorem to the right of a consequent.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)
    jctr $p |- ( ph -> ( ph /\ ps ) ) $=
      wph wph wps wph id jctl.1 jctir $.
  $}

  ${
    jctild.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctild.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 21-Apr-2005.) $)
    jctild $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $=
      wph wps wth wch wph wth wps jctild.2 a1d jctild.1 jcad $.
  $}

  ${
    jctird.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctird.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to right of consequent in an
       implication.  (Contributed by NM, 21-Apr-2005.) $)
    jctird $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      wph wps wch wth jctird.1 wph wth wps jctird.2 a1d jcad $.
  $}

  $( Conjoin antecedent to left of consequent.  (Contributed by NM,
     15-Aug-1994.) $)
  ancl $p |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ) $=
    wph wps wph wps wa wph wps pm3.2 a2i $.

  $( Conjoin antecedent to left of consequent.  Theorem *4.7 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 25-Jul-1999.)  (Proof
     shortened by Wolf Lammen, 24-Mar-2013.) $)
  anclb $p |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) ) $=
    wph wps wph wps wa wph wps ibar pm5.74i $.

  $( Theorem *5.42 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.42 $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    wph wps wch wi wps wph wch wa wi wph wch wph wch wa wps wph wch ibar imbi2d
    pm5.74i $.

  $( Conjoin antecedent to right of consequent.  (Contributed by NM,
     15-Aug-1994.) $)
  ancr $p |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) ) $=
    wph wps wps wph wa wph wps pm3.21 a2i $.

  $( Conjoin antecedent to right of consequent.  (Contributed by NM,
     25-Jul-1999.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  ancrb $p |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) ) $=
    wph wps wps wph wa wph wps iba pm5.74i $.

  ${
    ancli.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to left of consequent.  (Contributed by
       NM, 12-Aug-1993.) $)
    ancli $p |- ( ph -> ( ph /\ ps ) ) $=
      wph wph wps wph id ancli.1 jca $.
  $}

  ${
    ancri.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to right of consequent.  (Contributed by
       NM, 15-Aug-1994.) $)
    ancri $p |- ( ph -> ( ps /\ ph ) ) $=
      wph wps wph ancri.1 wph id jca $.
  $}

  ${
    ancld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
    ancld $p |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $=
      wph wps wps wch wph wps idd ancld.1 jcad $.
  $}

  ${
    ancrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
    ancrd $p |- ( ph -> ( ps -> ( ch /\ ps ) ) ) $=
      wph wps wch wps ancrd.1 wph wps idd jcad $.
  $}

  $( Conjoin antecedent to left of consequent in nested implication.
     (Contributed by NM, 10-Aug-1994.)  (Proof shortened by Wolf Lammen,
     14-Jul-2013.) $)
  anc2l $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    wph wps wch wi wi wph wps wph wch wa wi wi wph wps wch pm5.42 biimpi $.

  $( Conjoin antecedent to right of consequent in nested implication.
     (Contributed by NM, 15-Aug-1994.) $)
  anc2r $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) ) $=
    wph wps wch wi wps wch wph wa wi wph wch wch wph wa wps wph wch pm3.21
    imim2d a2i $.

  ${
    anc2li.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 10-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 7-Dec-2012.) $)
    anc2li $p |- ( ph -> ( ps -> ( ph /\ ch ) ) ) $=
      wph wps wch wph anc2li.1 wph id jctild $.
  $}

  ${
    anc2ri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 7-Dec-2012.) $)
    anc2ri $p |- ( ph -> ( ps -> ( ch /\ ph ) ) ) $=
      wph wps wch wph anc2ri.1 wph id jctird $.
  $}

  $( Theorem *3.41 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.41 $p |- ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    wph wps wa wph wch wph wps simpl imim1i $.

  $( Theorem *3.42 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.42 $p |- ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    wph wps wa wps wch wph wps simpr imim1i $.

  $( Conjunction implies implication.  Theorem *3.4 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 31-Jul-1995.) $)
  pm3.4 $p |- ( ( ph /\ ps ) -> ( ph -> ps ) ) $=
    wph wps wa wps wph wph wps simpr a1d $.

  $( Conjunction with implication.  Compare Theorem *4.45 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 17-May-1998.) $)
  pm4.45im $p |- ( ph <-> ( ph /\ ( ps -> ph ) ) ) $=
    wph wph wps wph wi wa wph wps wph wi wph wps ax-1 ancli wph wps wph wi
    simpl impbii $.

  ${
    anim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction.  (Contributed by NM,
       3-Apr-1994.)  (Proof shortened by Wolf Lammen, 18-Dec-2013.) $)
    anim12d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) ) $=
      wph wps wch wth wta wch wta wa anim12d.1 anim12d.2 wph wch wta wa idd
      syl2and $.
  $}

  ${
    anim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Add a conjunct to right of antecedent and consequent in a deduction.
       (Contributed by NM, 3-Apr-1994.) $)
    anim1d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ th ) ) ) $=
      wph wps wch wth wth anim1d.1 wph wth idd anim12d $.

    $( Add a conjunct to left of antecedent and consequent in a deduction.
       (Contributed by NM, 5-Aug-1993.) $)
    anim2d $p |- ( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) ) $=
      wph wth wth wps wch wph wth idd anim1d.1 anim12d $.
  $}

  ${
    anim12i.1 $e |- ( ph -> ps ) $.
    anim12i.2 $e |- ( ch -> th ) $.
    $( Conjoin antecedents and consequents of two premises.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 14-Dec-2013.) $)
    anim12i $p |- ( ( ph /\ ch ) -> ( ps /\ th ) ) $=
      wph wps wth wps wth wa wch anim12i.1 anim12i.2 wps wth wa id syl2an $.

    $( Variant of ~ anim12i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    anim12ci $p |- ( ( ph /\ ch ) -> ( th /\ ps ) ) $=
      wch wph wth wps wa wch wth wph wps anim12i.2 anim12i.1 anim12i ancoms $.
  $}

  ${
    anim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce conjunct to both sides of an implication.  (Contributed by NM,
       5-Aug-1993.) $)
    anim1i $p |- ( ( ph /\ ch ) -> ( ps /\ ch ) ) $=
      wph wps wch wch anim1i.1 wch id anim12i $.

    $( Introduce conjunct to both sides of an implication.  (Contributed by NM,
       5-Aug-1993.) $)
    anim2i $p |- ( ( ch /\ ph ) -> ( ch /\ ps ) ) $=
      wch wch wph wps wch id anim1i.1 anim12i $.
  $}

  ${
    anim12ii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12ii.2 $e |- ( th -> ( ps -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction.  (Contributed by NM,
       11-Nov-2007.)  (Proof shortened by Wolf Lammen, 19-Jul-2013.) $)
    anim12ii $p |- ( ( ph /\ th ) -> ( ps -> ( ch /\ ta ) ) ) $=
      wph wth wa wps wch wta wph wps wch wi wth anim12ii.1 adantr wth wps wta
      wi wph anim12ii.2 adantl jcad $.
  $}

  $( Conjoin antecedents and consequents of two premises.  This is the closed
     theorem form of ~ anim12d .  Theorem *3.47 of [WhiteheadRussell] p. 113.
     It was proved by Leibniz, and it evidently pleased him enough to call it
     _praeclarum theorema_ (splendid theorem).  (Contributed by NM,
     12-Aug-1993.)  (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
  prth $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) )
       -> ( ( ph /\ ch ) -> ( ps /\ th ) ) ) $=
    wph wps wi wch wth wi wa wph wps wch wth wph wps wi wch wth wi simpl wph
    wps wi wch wth wi simpr anim12d $.

  $( Theorem *2.3 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.3 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ) $=
    wps wch wo wch wps wo wph wps wch pm1.4 orim2i $.

  $( Theorem *2.41 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.41 $p |- ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    wps wph wps wo wph wps wo wps wph olc wph wps wo id jaoi $.

  $( Theorem *2.42 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.42 $p |- ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    wph wn wph wps wi wph wps wi wph wps pm2.21 wph wps wi id jaoi $.

  $( Theorem *2.4 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.4 $p |- ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    wph wph wps wo wph wps wo wph wps orc wph wps wo id jaoi $.

  ${
    pm2.65da.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.65da.2 $e |- ( ( ph /\ ps ) -> -. ch ) $.
    $( Deduction rule for proof by contradiction.  (Contributed by NM,
       12-Jun-2014.) $)
    pm2.65da $p |- ( ph -> -. ps ) $=
      wph wps wch wph wps wch pm2.65da.1 ex wph wps wch wn pm2.65da.2 ex
      pm2.65d $.
  $}

  $( Theorem *4.44 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.44 $p |- ( ph <-> ( ph \/ ( ph /\ ps ) ) ) $=
    wph wph wph wps wa wo wph wph wps wa orc wph wph wph wps wa wph id wph wps
    simpl jaoi impbii $.

  $( Theorem *4.14 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Oct-2012.) $)
  pm4.14 $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    wph wps wch wi wi wph wch wn wps wn wi wi wph wps wa wch wi wph wch wn wa
    wps wn wi wps wch wi wch wn wps wn wi wph wps wch con34b imbi2i wph wps wch
    impexp wph wch wn wps wn impexp 3bitr4i $.

  $( Theorem *3.37 (Transp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Oct-2012.) $)
  pm3.37 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    wph wps wa wch wi wph wch wn wa wps wn wi wph wps wch pm4.14 biimpi $.

  $( Theorem to move a conjunct in and out of a negation.  (Contributed by NM,
     9-Nov-2003.) $)
  nan $p |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) ) $=
    wph wps wa wch wn wi wph wps wch wn wi wi wph wps wch wa wn wi wph wps wch
    wn impexp wps wch wn wi wps wch wa wn wph wps wch imnan imbi2i bitr2i $.

  $( Theorem *4.15 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 18-Nov-2012.) $)
  pm4.15 $p |- ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) ) $=
    wps wch wa wph wn wi wph wps wch wa wn wi wph wps wa wch wn wi wps wch wa
    wph con2b wph wps wch nan bitr2i $.

  $( Theorem *4.78 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
  pm4.78 $p |- ( ( ( ph -> ps ) \/ ( ph -> ch ) ) <->
                ( ph -> ( ps \/ ch ) ) ) $=
    wph wn wps wch wo wo wph wn wps wo wph wn wch wo wo wph wps wch wo wi wph
    wps wi wph wch wi wo wph wn wps wch orordi wph wps wch wo imor wph wps wi
    wph wn wps wo wph wch wi wph wn wch wo wph wps imor wph wch imor orbi12i
    3bitr4ri $.

  $( Theorem *4.79 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 27-Jun-2013.) $)
  pm4.79 $p |- ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <->
                ( ( ps /\ ch ) -> ph ) ) $=
    wps wph wi wch wph wi wo wps wch wa wph wi wps wph wi wps wph wch wph wi
    wch wps wph wi id wch wph wi id jaoa wps wch wa wph wi wps wph wi wch wph
    wi wps wph wi wn wps wps wch wa wph wi wch wph wi wps wph simplim wps wch
    wph pm3.3 syl5 orrd impbii $.

  $( Theorem *4.87 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Eric Schmidt, 26-Oct-2006.) $)
  pm4.87 $p |- ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\
                ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\
                ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) ) $=
    wph wps wa wch wi wph wps wch wi wi wb wph wps wch wi wi wps wph wch wi wi
    wb wa wps wph wch wi wi wps wph wa wch wi wb wph wps wa wch wi wph wps wch
    wi wi wb wph wps wch wi wi wps wph wch wi wi wb wph wps wch impexp wph wps
    wch bi2.04 pm3.2i wps wph wa wch wi wps wph wch wi wi wps wph wch impexp
    bicomi pm3.2i $.

  $( Theorem *3.33 (Syll) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.33 $p |- ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) ) $=
    wph wps wi wps wch wi wph wch wi wph wps wch imim1 imp $.

  $( Theorem *3.34 (Syll) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.34 $p |- ( ( ( ps -> ch ) /\ ( ph -> ps ) ) -> ( ph -> ch ) ) $=
    wps wch wi wph wps wi wph wch wi wps wch wph imim2 imp $.

  $( Conjunctive detachment.  Theorem *3.35 of [WhiteheadRussell] p. 112.
     (Contributed by NM, 14-Dec-2002.) $)
  pm3.35 $p |- ( ( ph /\ ( ph -> ps ) ) -> ps ) $=
    wph wph wps wi wps wph wps pm2.27 imp $.

  $( Theorem *5.31 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.31 $p |- ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ps /\ ch ) ) ) $=
    wch wph wps wi wph wps wch wa wi wch wps wps wch wa wph wch wps pm3.21
    imim2d imp $.

  ${
    imp4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4a $p |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $=
      wph wps wch wth wta wi wi wch wth wa wta wi imp4.1 wch wth wta impexp
      syl6ibr $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $=
      wph wps wch wth wa wta wi wph wps wch wth wta imp4.1 imp4a imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $=
      wph wps wch wa wth wta wph wps wch wth wta wi imp4.1 imp3a imp3a $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $=
      wph wps wch wth wa wta wph wps wch wth wta imp4.1 imp4a imp3a $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp41 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      wph wps wa wch wth wta wph wps wch wth wta wi wi imp4.1 imp imp31 $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp42 $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $=
      wph wps wch wa wa wth wta wph wps wch wth wta wi imp4.1 imp32 imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $=
      wph wps wa wch wth wa wta wph wps wch wth wta imp4.1 imp4b imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp44 $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $=
      wph wps wch wa wth wa wta wph wps wch wth wta imp4.1 imp4c imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp45 $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $=
      wph wps wch wth wa wa wta wph wps wch wth wta imp4.1 imp4d imp $.

  $}

  ${
    imp5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5a $p |- ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) ) $=
      wph wps wch wth wta wet wi wi wth wta wa wet wi imp5.1 wth wta wet pm3.31
      syl8 $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5d $p |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ) $=
      wph wps wa wch wa wth wta wet wph wps wch wth wta wet wi wi imp5.1 imp31
      imp3a $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5g $p |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ) $=
      wph wps wa wch wth wta wet wph wps wch wth wta wet wi wi wi imp5.1 imp
      imp4c $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp55 $p |- ( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et ) $=
      wph wps wch wth wa wta wet wph wps wch wth wta wet wi imp5.1 imp4a imp42
      $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp511 $p |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ) $=
      wph wps wch wth wa wta wet wph wps wch wth wta wet wi imp5.1 imp4a imp44
      $.
  $}

  ${
    expimpd.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Exportation followed by a deduction version of importation.
       (Contributed by NM, 6-Sep-2008.) $)
    expimpd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      wph wps wch wth wph wps wch wth wi expimpd.1 ex imp3a $.
  $}

  ${
    exp31.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp31 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wph wps wch wth wi wph wps wa wch wth exp31.1 ex ex $.
  $}

  ${
    exp32.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp32 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wph wps wch wth wph wps wch wa wth exp32.1 ex exp3a $.
  $}

  ${
    exp4a.1 $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wa wta wi wch wth wta wi wi exp4a.1 wch wth wta impexp
      syl6ib $.
  $}

  ${
    exp4b.1 $e |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 23-Nov-2012.) $)
    exp4b $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wch wth wa wta wi exp4b.1 ex exp4a $.
  $}

  ${
    exp4c.1 $e |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4c $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wch wa wth wta exp4c.1 exp3a exp3a $.
  $}

  ${
    exp4d.1 $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wch wth wa wta exp4d.1 exp3a exp4a $.
  $}

  ${
    exp41.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp41 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wa wch wa wth wta exp41.1 ex exp31 $.
  $}

  ${
    exp42.1 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp42 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wch wa wth wta exp42.1 exp31 exp3a $.
  $}

  ${
    exp43.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp43 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wa wch wth wa wta exp43.1 ex exp4b $.
  $}

  ${
    exp44.1 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp44 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wch wa wth wta exp44.1 exp32 exp3a $.
  $}

  ${
    exp45.1 $e |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp45 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wch wth wa wta exp45.1 exp32 exp4a $.
  $}

  ${
    expr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Export a wff from a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    expr $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      wph wps wch wth wi wph wps wch wth expr.1 exp32 imp $.
  $}

  ${
    exp5c.1 $e |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5c $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wi wph wps wch wa wth wta wet exp5c.1 exp4a
      exp3a $.
  $}

  ${
    exp53.1 $e |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    exp53 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wph wps wa wch wth wa wa wta wet exp53.1 ex
      exp43 $.
  $}

  ${
    expl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Export a wff from a left conjunct.  (Contributed by Jeff Hankins,
       28-Aug-2009.) $)
    expl $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      wph wps wch wth wph wps wch wth expl.1 exp31 imp3a $.
  $}

  ${
    impr.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Import a wff into a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    impr $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      wph wps wch wth wph wps wch wth wi impr.1 ex imp32 $.
  $}

  ${
    impl.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export a wff from a left conjunct.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)
    impl $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth impl.1 exp3a imp31 $.
  $}

  ${
    impac.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation with conjunction in consequent.  (Contributed by NM,
       9-Aug-1994.) $)
    impac $p |- ( ( ph /\ ps ) -> ( ch /\ ps ) ) $=
      wph wps wch wps wa wph wps wch impac.1 ancrd imp $.
  $}

  ${
    exbiri.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Inference form of ~ exbir .  This proof is ~ exbiriVD automatically
       translated and minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
       (Proof shortened by Wolf Lammen, 27-Jan-2013.) $)
    exbiri $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      wph wps wth wch wph wps wa wch wth exbiri.1 biimpar exp31 $.
  $}

  ${
    pm3.26bda.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)
    simprbda $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wa wch wth wph wps wch wth wa pm3.26bda.1 biimpa simpld $.

    $( Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)
    simplbda $p |- ( ( ph /\ ps ) -> th ) $=
      wph wps wa wch wth wph wps wch wth wa pm3.26bda.1 biimpa simprd $.
  $}

  ${
    pm3.26bi2.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  Automatically derived from
       ~ simplbi2VD .  (Contributed by Alan Sare, 31-Dec-2011.) $)
    simplbi2 $p |- ( ps -> ( ch -> ph ) ) $=
      wps wch wph wph wps wch wa pm3.26bi2.1 biimpri ex $.
  $}

  $( A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49.  (Contributed by NM, 5-Aug-1993.) $)
  dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wph wps wi wps wph wi wa wph wps
    dfbi1 wph wps wi wps wph wi df-an bitr4i $.

  $( Definition ~ df-bi rewritten in an abbreviated form to help intuitive
     understanding of that definition.  Note that it is a conjunction of two
     implications; one which asserts properties that follow from the
     biconditional and one which asserts properties that imply the
     biconditional.  (Contributed by NM, 15-Aug-2008.) $)
  dfbi $p |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
        /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $=
    wph wps wb wph wps wi wps wph wi wa wi wph wps wi wps wph wi wa wph wps wb
    wi wph wps wb wph wps wi wps wph wi wa wph wps dfbi2 biimpi wph wps wb wph
    wps wi wps wph wi wa wph wps dfbi2 biimpri pm3.2i $.

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 2-Dec-2012.) $)
  pm4.71 $p |- ( ( ph -> ps ) <-> ( ph <-> ( ph /\ ps ) ) ) $=
    wph wph wps wa wi wph wph wps wa wi wph wps wa wph wi wa wph wps wi wph wph
    wps wa wb wph wps wa wph wi wph wph wps wa wi wph wps simpl biantru wph wps
    anclb wph wph wps wa dfbi2 3bitr4i $.

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120 (with conjunct reversed).  (Contributed by NM,
     25-Jul-1999.) $)
  pm4.71r $p |- ( ( ph -> ps ) <-> ( ph <-> ( ps /\ ph ) ) ) $=
    wph wps wi wph wph wps wa wb wph wps wph wa wb wph wps pm4.71 wph wps wa
    wps wph wa wph wph wps ancom bibi2i bitri $.

  ${
    pm4.71i.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by NM, 4-Jan-2004.) $)
    pm4.71i $p |- ( ph <-> ( ph /\ ps ) ) $=
      wph wps wi wph wph wps wa wb pm4.71i.1 wph wps pm4.71 mpbi $.
  $}

  ${
    pm4.71ri.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell] p. 120
       (with conjunct reversed).  (Contributed by NM, 1-Dec-2003.) $)
    pm4.71ri $p |- ( ph <-> ( ps /\ ph ) ) $=
      wph wps wi wph wps wph wa wb pm4.71ri.1 wph wps pm4.71r mpbi $.
  $}

  ${
    pm4.71rd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by Mario Carneiro, 25-Dec-2016.) $)
    pm4.71d $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      wph wps wch wi wps wps wch wa wb pm4.71rd.1 wps wch pm4.71 sylib $.

    $( Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by NM, 10-Feb-2005.) $)
    pm4.71rd $p |- ( ph -> ( ps <-> ( ch /\ ps ) ) ) $=
      wph wps wch wi wps wch wps wa wb pm4.71rd.1 wps wch pm4.71r sylib $.
  $}

  $( Distribution of implication over biconditional.  Theorem *5.32 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 1-Aug-1994.) $)
  pm5.32 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    wph wps wch wb wi wph wps wn wi wn wph wch wn wi wn wb wph wps wa wph wch
    wa wb wph wps wch wb wi wph wps wn wch wn wb wi wph wps wn wi wph wch wn wi
    wb wph wps wn wi wn wph wch wn wi wn wb wps wch wb wps wn wch wn wb wph wps
    wch notbi imbi2i wph wps wn wch wn pm5.74 wph wps wn wi wph wch wn wi notbi
    3bitri wph wps wa wph wps wn wi wn wph wch wa wph wch wn wi wn wph wps
    df-an wph wch df-an bibi12i bitr4i $.

  ${
    pm5.32i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.32i $p |- ( ( ph /\ ps ) <-> ( ph /\ ch ) ) $=
      wph wps wch wb wi wph wps wa wph wch wa wb pm5.32i.1 wph wps wch pm5.32
      mpbi $.

    $( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 12-Mar-1995.) $)
    pm5.32ri $p |- ( ( ps /\ ph ) <-> ( ch /\ ph ) ) $=
      wph wps wa wph wch wa wps wph wa wch wph wa wph wps wch pm5.32i.1 pm5.32i
      wps wph ancom wch wph ancom 3bitr4i $.
  $}

  ${
    pm5.32d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 29-Oct-1996.) $)
    pm5.32d $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      wph wps wch wth wb wi wps wch wa wps wth wa wb pm5.32d.1 wps wch wth
      pm5.32 sylib $.

    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 25-Dec-2004.) $)
    pm5.32rd $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $=
      wph wps wch wa wps wth wa wch wps wa wth wps wa wph wps wch wth pm5.32d.1
      pm5.32d wch wps ancom wth wps ancom 3bitr4g $.
  $}

  ${
    pm5.32da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 9-Dec-2006.) $)
    pm5.32da $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      wph wps wch wth wph wps wch wth wb pm5.32da.1 ex pm5.32d $.
  $}

  ${
    biadan2.1 $e |- ( ph -> ps ) $.
    biadan2.2 $e |- ( ps -> ( ph <-> ch ) ) $.
    $( Add a conjunction to an equivalence.  (Contributed by Jeff Madsen,
       20-Jun-2011.) $)
    biadan2 $p |- ( ph <-> ( ps /\ ch ) ) $=
      wph wps wph wa wps wch wa wph wps biadan2.1 pm4.71ri wps wph wch
      biadan2.2 pm5.32i bitri $.
  $}

  $( Theorem *4.24 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.24 $p |- ( ph <-> ( ph /\ ph ) ) $=
    wph wph wph id pm4.71i $.

  $( Idempotent law for conjunction.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 14-Mar-2014.) $)
  anidm $p |- ( ( ph /\ ph ) <-> ph ) $=
    wph wph wph wa wph pm4.24 bicomi $.

  ${
    anidms.1 $e |- ( ( ph /\ ph ) -> ps ) $.
    $( Inference from idempotent law for conjunction.  (Contributed by NM,
       15-Jun-1994.) $)
    anidms $p |- ( ph -> ps ) $=
      wph wps wph wph wps anidms.1 ex pm2.43i $.
  $}

  $( Conjunction idempotence with antecedent.  (Contributed by Roy F. Longton,
     8-Aug-2005.) $)
  anidmdbi $p |- ( ( ph -> ( ps /\ ps ) ) <-> ( ph -> ps ) ) $=
    wps wps wa wps wph wps anidm imbi2i $.

  ${
    anasss.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)
    anasss $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      wph wps wch wth wph wps wch wth anasss.1 exp31 imp32 $.
  $}

  ${
    anassrs.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)
    anassrs $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth anassrs.1 exp32 imp31 $.
  $}

  $( Associative law for conjunction.  Theorem *4.32 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Nov-2012.) $)
  anass $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    wph wps wa wch wa wph wps wch wa wa wph wps wch wph wps wch wa wa wph wps
    wch wa wa id anassrs wph wps wch wph wps wa wch wa wph wps wa wch wa id
    anasss impbii $.

  ${
    sylanl1.1 $e |- ( ph -> ps ) $.
    sylanl1.2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 10-Mar-2005.) $)
    sylanl1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      wph wch wa wps wch wa wth wta wph wps wch sylanl1.1 anim1i sylanl1.2
      sylan $.
  $}

  ${
    sylanl2.1 $e |- ( ph -> ch ) $.
    sylanl2.2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 1-Jan-2005.) $)
    sylanl2 $p |- ( ( ( ps /\ ph ) /\ th ) -> ta ) $=
      wps wph wa wps wch wa wth wta wph wch wps sylanl2.1 anim2i sylanl2.2
      sylan $.
  $}

  ${
    sylanr1.1 $e |- ( ph -> ch ) $.
    sylanr1.2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 9-Apr-2005.) $)
    sylanr1 $p |- ( ( ps /\ ( ph /\ th ) ) -> ta ) $=
      wph wth wa wps wch wth wa wta wph wch wth sylanr1.1 anim1i sylanr1.2
      sylan2 $.
  $}

  ${
    sylanr2.1 $e |- ( ph -> th ) $.
    sylanr2.2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 9-Apr-2005.) $)
    sylanr2 $p |- ( ( ps /\ ( ch /\ ph ) ) -> ta ) $=
      wch wph wa wps wch wth wa wta wph wth wch sylanr2.1 anim2i sylanr2.2
      sylan2 $.
  $}

  ${
    sylani.1 $e |- ( ph -> ch ) $.
    sylani.2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference.  (Contributed by NM, 2-May-1996.) $)
    sylani $p |- ( ps -> ( ( ph /\ th ) -> ta ) ) $=
      wps wph wch wth wta wph wch wi wps sylani.1 a1i sylani.2 syland $.
  $}

  ${
    sylan2i.1 $e |- ( ph -> th ) $.
    sylan2i.2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference.  (Contributed by NM, 1-Aug-1994.) $)
    sylan2i $p |- ( ps -> ( ( ch /\ ph ) -> ta ) ) $=
      wps wph wth wch wta wph wth wi wps sylan2i.1 a1i sylan2i.2 sylan2d $.
  $}

  ${
    syl2ani.1 $e |- ( ph -> ch ) $.
    syl2ani.2 $e |- ( et -> th ) $.
    syl2ani.3 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference.  (Contributed by NM, 3-Aug-1999.) $)
    syl2ani $p |- ( ps -> ( ( ph /\ et ) -> ta ) ) $=
      wph wps wch wet wta syl2ani.1 wet wps wch wth wta syl2ani.2 syl2ani.3
      sylan2i sylani $.
  $}

  ${
    sylan9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.) $)
    sylan9 $p |- ( ( ph /\ th ) -> ( ps -> ta ) ) $=
      wph wth wps wta wi wph wps wch wth wta sylan9.1 sylan9.2 syl9 imp $.
  $}

  ${
    sylan9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 5-Aug-1993.) $)
    sylan9r $p |- ( ( th /\ ph ) -> ( ps -> ta ) ) $=
      wth wph wps wta wi wph wps wch wth wta sylan9r.1 sylan9r.2 syl9r imp $.
  $}

  ${
    mtand.1 $e |- ( ph -> -. ch ) $.
    mtand.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( A modus tollens deduction.  (Contributed by Jeff Hankins,
       19-Aug-2009.) $)
    mtand $p |- ( ph -> -. ps ) $=
      wph wps wch mtand.1 wph wps wch mtand.2 ex mtod $.
  $}

  ${
    mtord.1 $e |- ( ph -> -. ch ) $.
    mtord.2 $e |- ( ph -> -. th ) $.
    mtord.3 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
    $( A modus tollens deduction involving disjunction.  (Contributed by Jeff
       Hankins, 15-Jul-2009.) $)
    mtord $p |- ( ph -> -. ps ) $=
      wph wps wth mtord.2 wph wps wch wn wth mtord.1 wph wps wch wth wo wch wn
      wth wi mtord.3 wch wth df-or syl6ib mpid mtod $.
  $}

  ${
    syl2anc.1 $e |- ( ph -> ps ) $.
    syl2anc.2 $e |- ( ph -> ch ) $.
    syl2anc.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with contraction.  (Contributed by NM,
       16-Mar-2012.) $)
    syl2anc $p |- ( ph -> th ) $=
      wph wps wch wth syl2anc.1 syl2anc.2 wps wch wth syl2anc.3 ex sylc $.
  $}

  ${
    sylancl.1 $e |- ( ph -> ps ) $.
    sylancl.2 $e |- ch $.
    sylancl.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sylancl $p |- ( ph -> th ) $=
      wph wps wch wth sylancl.1 wch wph sylancl.2 a1i sylancl.3 syl2anc $.
  $}

  ${
    sylancr.1 $e |- ps $.
    sylancr.2 $e |- ( ph -> ch ) $.
    sylancr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sylancr $p |- ( ph -> th ) $=
      wph wps wch wth wps wph sylancr.1 a1i sylancr.2 sylancr.3 syl2anc $.
  $}

  ${
    sylanbrc.1 $e |- ( ph -> ps ) $.
    sylanbrc.2 $e |- ( ph -> ch ) $.
    sylanbrc.3 $e |- ( th <-> ( ps /\ ch ) ) $.
    $( Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    sylanbrc $p |- ( ph -> th ) $=
      wph wps wch wa wth wph wps wch sylanbrc.1 sylanbrc.2 jca sylanbrc.3
      sylibr $.
  $}

  ${
    sylancb.1 $e |- ( ph <-> ps ) $.
    sylancb.2 $e |- ( ph <-> ch ) $.
    sylancb.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference combined with contraction.  (Contributed by NM,
       3-Sep-2004.) $)
    sylancb $p |- ( ph -> th ) $=
      wph wth wph wps wch wth wph sylancb.1 sylancb.2 sylancb.3 syl2anb anidms
      $.
  $}

  ${
    sylancbr.1 $e |- ( ps <-> ph ) $.
    sylancbr.2 $e |- ( ch <-> ph ) $.
    sylancbr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference combined with contraction.  (Contributed by NM,
       3-Sep-2004.) $)
    sylancbr $p |- ( ph -> th ) $=
      wph wth wph wps wch wth wph sylancbr.1 sylancbr.2 sylancbr.3 syl2anbr
      anidms $.
  $}

  ${
    sylancom.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancom.2 $e |- ( ( ch /\ ps ) -> th ) $.
    $( Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 2-Jul-2008.) $)
    sylancom $p |- ( ( ph /\ ps ) -> th ) $=
      wph wps wa wch wps wth sylancom.1 wph wps simpr sylancom.2 syl2anc $.
  $}

  ${
    mpdan.1 $e |- ( ph -> ps ) $.
    mpdan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 23-May-1999.)
       (Proof shortened by Wolf Lammen, 22-Nov-2012.) $)
    mpdan $p |- ( ph -> ch ) $=
      wph wph wps wch wph id mpdan.1 mpdan.2 syl2anc $.
  $}

  ${
    mpancom.1 $e |- ( ps -> ph ) $.
    mpancom.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens with commutation of antecedents.
       (Contributed by NM, 28-Oct-2003.)  (Proof shortened by Wolf Lammen,
       7-Apr-2013.) $)
    mpancom $p |- ( ps -> ch ) $=
      wps wph wps wch mpancom.1 wps id mpancom.2 syl2anc $.
  $}

  ${
    mpan.1 $e |- ph $.
    mpan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 30-Aug-1993.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpan $p |- ( ps -> ch ) $=
      wph wps wch wph wps mpan.1 a1i mpan.2 mpancom $.
  $}

  ${
    mpan2.1 $e |- ps $.
    mpan2.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 16-Sep-1993.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
    mpan2 $p |- ( ph -> ch ) $=
      wph wps wch wps wph mpan2.1 a1i mpan2.2 mpdan $.
  $}

  ${
    mp2an.1 $e |- ph $.
    mp2an.2 $e |- ps $.
    mp2an.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       13-Apr-1995.) $)
    mp2an $p |- ch $=
      wps wch mp2an.2 wph wps wch mp2an.1 mp2an.3 mpan ax-mp $.
  $}

  ${
    mp4an.1 $e |- ph $.
    mp4an.2 $e |- ps $.
    mp4an.3 $e |- ch $.
    mp4an.4 $e |- th $.
    mp4an.5 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by Jeff Madsen,
       15-Jun-2010.) $)
    mp4an $p |- ta $=
      wph wps wa wch wth wa wta wph wps mp4an.1 mp4an.2 pm3.2i wch wth mp4an.3
      mp4an.4 pm3.2i mp4an.5 mp2an $.
  $}

  ${
    mpan2d.1 $e |- ( ph -> ch ) $.
    mpan2d.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)
    mpan2d $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth mpan2d.1 wph wps wch wth mpan2d.2 exp3a mpid $.
  $}

  ${
    mpand.1 $e |- ( ph -> ps ) $.
    mpand.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpand $p |- ( ph -> ( ch -> th ) ) $=
      wph wch wps wth mpand.1 wph wps wch wth mpand.2 ancomsd mpan2d $.
  $}

  ${
    mpani.1 $e |- ps $.
    mpani.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 10-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
    mpani $p |- ( ph -> ( ch -> th ) ) $=
      wph wps wch wth wps wph mpani.1 a1i mpani.2 mpand $.
  $}

  ${
    mpan2i.1 $e |- ch $.
    mpan2i.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 10-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
    mpan2i $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wch wph mpan2i.1 a1i mpan2i.2 mpan2d $.
  $}

  ${
    mp2ani.1 $e |- ps $.
    mp2ani.2 $e |- ch $.
    mp2ani.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       12-Dec-2004.) $)
    mp2ani $p |- ( ph -> th ) $=
      wph wch wth mp2ani.2 wph wps wch wth mp2ani.1 mp2ani.3 mpani mpi $.
  $}

  ${
    mp2and.1 $e |- ( ph -> ps ) $.
    mp2and.2 $e |- ( ph -> ch ) $.
    mp2and.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)
    mp2and $p |- ( ph -> th ) $=
      wph wch wth mp2and.2 wph wps wch wth mp2and.1 mp2and.3 mpand mpd $.
  $}

  ${
    mpanl1.1 $e |- ph $.
    mpanl1.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 16-Aug-1994.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpanl1 $p |- ( ( ps /\ ch ) -> th ) $=
      wps wph wps wa wch wth wps wph mpanl1.1 jctl mpanl1.2 sylan $.
  $}

  ${
    mpanl2.1 $e |- ps $.
    mpanl2.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 16-Aug-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    mpanl2 $p |- ( ( ph /\ ch ) -> th ) $=
      wph wph wps wa wch wth wph wps mpanl2.1 jctr mpanl2.2 sylan $.
  $}

  ${
    mpanl12.1 $e |- ph $.
    mpanl12.2 $e |- ps $.
    mpanl12.3 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       13-Jul-2005.) $)
    mpanl12 $p |- ( ch -> th ) $=
      wps wch wth mpanl12.2 wph wps wch wth mpanl12.1 mpanl12.3 mpanl1 mpan $.
  $}

  ${
    mpanr1.1 $e |- ps $.
    mpanr1.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 3-May-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    mpanr1 $p |- ( ( ph /\ ch ) -> th ) $=
      wph wps wch wth mpanr1.1 wph wps wch wth mpanr1.2 anassrs mpanl2 $.
  $}

  ${
    mpanr2.1 $e |- ch $.
    mpanr2.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 3-May-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof shortened by
       Wolf Lammen, 7-Apr-2013.) $)
    mpanr2 $p |- ( ( ph /\ ps ) -> th ) $=
      wps wph wps wch wa wth wps wch mpanr2.1 jctr mpanr2.2 sylan2 $.
  $}

  ${
    mpanr12.1 $e |- ps $.
    mpanr12.2 $e |- ch $.
    mpanr12.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Jul-2009.) $)
    mpanr12 $p |- ( ph -> th ) $=
      wph wch wth mpanr12.2 wph wps wch wth mpanr12.1 mpanr12.3 mpanr1 mpan2 $.
  $}

  ${
    mpanlr1.1 $e |- ps $.
    mpanlr1.2 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 30-Dec-2004.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpanlr1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      wch wph wps wch wa wth wta wch wps mpanlr1.1 jctl mpanlr1.2 sylanl2 $.
  $}

  ${
    pm5.74da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 4-May-2007.) $)
    pm5.74da $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      wph wps wch wth wph wps wch wth wb pm5.74da.1 ex pm5.74d $.
  $}

  $( Theorem *4.45 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.45 $p |- ( ph <-> ( ph /\ ( ph \/ ps ) ) ) $=
    wph wph wps wo wph wps orc pm4.71i $.

  $( Distribution of implication with conjunction.  (Contributed by NM,
     31-May-1999.)  (Proof shortened by Wolf Lammen, 6-Dec-2012.) $)
  imdistan $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    wph wps wch wi wi wph wps wph wch wa wi wi wph wps wa wph wch wa wi wph wps
    wch pm5.42 wph wps wph wch wa impexp bitr4i $.

  ${
    imdistani.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction.  (Contributed by NM,
       1-Aug-1994.) $)
    imdistani $p |- ( ( ph /\ ps ) -> ( ph /\ ch ) ) $=
      wph wps wph wch wa wph wps wch imdistani.1 anc2li imp $.
  $}

  ${
    imdistanri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction.  (Contributed by NM,
       8-Jan-2002.) $)
    imdistanri $p |- ( ( ps /\ ph ) -> ( ch /\ ph ) ) $=
      wps wph wch wph wps wch imdistanri.1 com12 impac $.
  $}

  ${
    imdistand.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Distribution of implication with conjunction (deduction rule).
       (Contributed by NM, 27-Aug-2004.) $)
    imdistand $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      wph wps wch wth wi wi wps wch wa wps wth wa wi imdistand.1 wps wch wth
      imdistan sylib $.
  $}

  ${
    imdistanda.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Distribution of implication with conjunction (deduction version with
       conjoined antecedent).  (Contributed by Jeff Madsen, 19-Jun-2011.) $)
    imdistanda $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      wph wps wch wth wph wps wch wth wi imdistanda.1 ex imdistand $.
  $}

  ${
    bi.aa $e |- ( ph <-> ps ) $.
    $( Introduce a left conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)
    anbi2i $p |- ( ( ch /\ ph ) <-> ( ch /\ ps ) ) $=
      wch wph wps wph wps wb wch bi.aa a1i pm5.32i $.

    $( Introduce a right conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)
    anbi1i $p |- ( ( ph /\ ch ) <-> ( ps /\ ch ) ) $=
      wch wph wps wph wps wb wch bi.aa a1i pm5.32ri $.

    $( Variant of ~ anbi2i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
    anbi2ci $p |- ( ( ph /\ ch ) <-> ( ch /\ ps ) ) $=
      wph wch wa wps wch wa wch wps wa wph wps wch bi.aa anbi1i wps wch ancom
      bitri $.
  $}

  ${
    anbi12.1 $e |- ( ph <-> ps ) $.
    anbi12.2 $e |- ( ch <-> th ) $.
    $( Conjoin both sides of two equivalences.  (Contributed by NM,
       5-Aug-1993.) $)
    anbi12i $p |- ( ( ph /\ ch ) <-> ( ps /\ th ) ) $=
      wph wch wa wps wch wa wps wth wa wph wps wch anbi12.1 anbi1i wch wth wps
      anbi12.2 anbi2i bitri $.

    $( Variant of ~ anbi12i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    anbi12ci $p |- ( ( ph /\ ch ) <-> ( th /\ ps ) ) $=
      wph wch wa wps wth wa wth wps wa wph wps wch wth anbi12.1 anbi12.2
      anbi12i wps wth ancom bitri $.
  $}

  ${
    sylan9bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bb.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)
    sylan9bb $p |- ( ( ph /\ th ) -> ( ps <-> ta ) ) $=
      wph wth wa wps wch wta wph wps wch wb wth sylan9bb.1 adantr wth wch wta
      wb wph sylan9bb.2 adantl bitrd $.
  $}

  ${
    sylan9bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bbr.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)
    sylan9bbr $p |- ( ( th /\ ph ) -> ( ps <-> ta ) ) $=
      wph wth wps wta wb wph wps wch wth wta sylan9bbr.1 sylan9bbr.2 sylan9bb
      ancoms $.
  $}

  ${
    bid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding a left disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    orbi2d $p |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) ) $=
      wph wth wn wps wi wth wn wch wi wth wps wo wth wch wo wph wps wch wth wn
      bid.1 imbi2d wth wps df-or wth wch df-or 3bitr4g $.

    $( Deduction adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    orbi1d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) ) $=
      wph wth wps wo wth wch wo wps wth wo wch wth wo wph wps wch wth bid.1
      orbi2d wps wth orcom wch wth orcom 3bitr4g $.

    $( Deduction adding a left conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)
    anbi2d $p |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) ) $=
      wph wth wps wch wph wps wch wb wth bid.1 a1d pm5.32d $.

    $( Deduction adding a right conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)
    anbi1d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) ) $=
      wph wth wps wch wph wps wch wb wth bid.1 a1d pm5.32rd $.
  $}

  $( Theorem *4.37 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  orbi1 $p |- ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $=
    wph wps wb wph wps wch wph wps wb id orbi1d $.

  $( Introduce a right conjunct to both sides of a logical equivalence.
     Theorem *4.36 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  anbi1 $p |- ( ( ph <-> ps ) -> ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) $=
    wph wps wb wph wps wch wph wps wb id anbi1d $.

  $( Introduce a left conjunct to both sides of a logical equivalence.
     (Contributed by NM, 16-Nov-2013.) $)
  anbi2 $p |- ( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) ) $=
    wph wps wb wph wps wch wph wps wb id anbi2d $.

  $( Theorem *4.22 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
  bitr $p |- ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) ) $=
    wph wps wb wph wch wb wps wch wb wph wps wch bibi1 biimpar $.

  ${
    bi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of disjunctions.
       (Contributed by NM, 5-Aug-1993.) $)
    orbi12d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) ) $=
      wph wps wth wo wch wth wo wch wta wo wph wps wch wth bi12d.1 orbi1d wph
      wth wta wch bi12d.2 orbi2d bitrd $.

    $( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 5-Aug-1993.) $)
    anbi12d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) ) $=
      wph wps wth wa wch wth wa wch wta wa wph wps wch wth bi12d.1 anbi1d wph
      wth wta wch bi12d.2 anbi2d bitrd $.
  $}

  $( Theorem *5.3 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  pm5.3 $p |- ( ( ( ph /\ ps ) -> ch ) <->
               ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    wph wps wa wch wi wph wps wch wi wi wph wps wa wph wch wa wi wph wps wch
    impexp wph wps wch imdistan bitri $.

  $( Theorem *5.61 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 30-Jun-2013.) $)
  pm5.61 $p |- ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) ) $=
    wps wn wph wps wo wph wps wn wph wps wph wo wph wps wo wps wph biorf wps
    wph orcom syl6rbb pm5.32ri $.

  ${
    adant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    adantll $p |- ( ( ( th /\ ph ) /\ ps ) -> ch ) $=
      wth wph wa wph wps wch wth wph simpr adant2.1 sylan $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    adantlr $p |- ( ( ( ph /\ th ) /\ ps ) -> ch ) $=
      wph wth wa wph wps wch wph wth simpl adant2.1 sylan $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    adantrl $p |- ( ( ph /\ ( th /\ ps ) ) -> ch ) $=
      wth wps wa wph wps wch wth wps simpr adant2.1 sylan2 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    adantrr $p |- ( ( ph /\ ( ps /\ th ) ) -> ch ) $=
      wps wth wa wph wps wch wps wth simpl adant2.1 sylan2 $.
  $}

  ${
    adantl2.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 2-Dec-2012.) $)
    adantlll $p |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th ) $=
      wta wph wa wph wps wch wth wta wph simpr adantl2.1 sylanl1 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantllr $p |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th ) $=
      wph wta wa wph wps wch wth wph wta simpl adantl2.1 sylanl1 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantlrl $p |- ( ( ( ph /\ ( ta /\ ps ) ) /\ ch ) -> th ) $=
      wta wps wa wph wps wch wth wta wps simpr adantl2.1 sylanl2 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantlrr $p |- ( ( ( ph /\ ( ps /\ ta ) ) /\ ch ) -> th ) $=
      wps wta wa wph wps wch wth wps wta simpl adantl2.1 sylanl2 $.
  $}

  ${
    adantr2.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantrll $p |- ( ( ph /\ ( ( ta /\ ps ) /\ ch ) ) -> th ) $=
      wta wps wa wph wps wch wth wta wps simpr adantr2.1 sylanr1 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantrlr $p |- ( ( ph /\ ( ( ps /\ ta ) /\ ch ) ) -> th ) $=
      wps wta wa wph wps wch wth wps wta simpl adantr2.1 sylanr1 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantrrl $p |- ( ( ph /\ ( ps /\ ( ta /\ ch ) ) ) -> th ) $=
      wta wch wa wph wps wch wth wta wch simpr adantr2.1 sylanr2 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantrrr $p |- ( ( ph /\ ( ps /\ ( ch /\ ta ) ) ) -> th ) $=
      wch wta wa wph wps wch wth wch wta simpl adantr2.1 sylanr2 $.
  $}

  ${
    ad2ant.1 $e |- ( ph -> ps ) $.
    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)
    ad2antrr $p |- ( ( ( ph /\ ch ) /\ th ) -> ps ) $=
      wph wth wps wch wph wps wth ad2ant.1 adantr adantlr $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)
    ad2antlr $p |- ( ( ( ch /\ ph ) /\ th ) -> ps ) $=
      wph wth wps wch wph wps wth ad2ant.1 adantr adantll $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.) $)
    ad2antrl $p |- ( ( ch /\ ( ph /\ th ) ) -> ps ) $=
      wph wth wa wps wch wph wps wth ad2ant.1 adantr adantl $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.) $)
    ad2antll $p |- ( ( ch /\ ( th /\ ph ) ) -> ps ) $=
      wth wph wa wps wch wph wps wth ad2ant.1 adantl adantl $.

    $( Deduction adding three conjuncts to antecedent.  (Contributed by NM,
       28-Jul-2012.) $)
    ad3antrrr $p |- ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) -> ps ) $=
      wph wch wa wps wth wta wph wps wch ad2ant.1 adantr ad2antrr $.

    $( Deduction adding three conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad3antlr $p |- ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) -> ps ) $=
      wch wph wa wth wa wps wta wph wps wch wth ad2ant.1 ad2antlr adantr $.

    $( Deduction adding 4 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad4antr $p |- ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) -> ps ) $=
      wph wch wa wth wa wta wa wps wet wph wps wch wth wta ad2ant.1 ad3antrrr
      adantr $.

    $( Deduction adding 4 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad4antlr $p |- ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) -> ps ) $=
      wch wph wa wth wa wta wa wps wet wph wps wch wth wta ad2ant.1 ad3antlr
      adantr $.

    $( Deduction adding 5 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad5antr $p |- ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) -> ps ) $=
      wph wch wa wth wa wta wa wet wa wps wze wph wps wch wth wta wet ad2ant.1
      ad4antr adantr $.

    $( Deduction adding 5 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad5antlr $p |- ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) -> ps ) $=
      wch wph wa wth wa wta wa wet wa wps wze wph wps wch wth wta wet ad2ant.1
      ad4antlr adantr $.

    $( Deduction adding 6 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad6antr $p |- ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) -> ps ) $=
      wph wch wa wth wa wta wa wet wa wze wa wps wsi wph wps wch wth wta wet
      wze ad2ant.1 ad5antr adantr $.

    $( Deduction adding 6 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad6antlr $p |- ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) -> ps ) $=
      wch wph wa wth wa wta wa wet wa wze wa wps wsi wph wps wch wth wta wet
      wze ad2ant.1 ad5antlr adantr $.

    $( Deduction adding 7 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad7antr $p |- ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) -> ps ) $=
      wph wch wa wth wa wta wa wet wa wze wa wsi wa wps wrh wph wps wch wth wta
      wet wze wsi ad2ant.1 ad6antr adantr $.

    $( Deduction adding 7 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad7antlr $p |- ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) -> ps ) $=
      wch wph wa wth wa wta wa wet wa wze wa wsi wa wps wrh wph wps wch wth wta
      wet wze wsi ad2ant.1 ad6antlr adantr $.

    $( Deduction adding 8 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad8antr $p |- ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $=
      wph wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wps wmu wph wps wch
      wth wta wet wze wsi wrh ad2ant.1 ad7antr adantr $.

    $( Deduction adding 8 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad8antlr $p |- ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $=
      wch wph wa wth wa wta wa wet wa wze wa wsi wa wrh wa wps wmu wph wps wch
      wth wta wet wze wsi wrh ad2ant.1 ad7antlr adantr $.

    $( Deduction adding 9 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad9antr $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $=
      wph wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wmu wa wps wla wph
      wps wch wth wta wet wze wsi wrh wmu ad2ant.1 ad8antr adantr $.

    $( Deduction adding 9 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad9antlr $p |- ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $=
      wch wph wa wth wa wta wa wet wa wze wa wsi wa wrh wa wmu wa wps wla wph
      wps wch wth wta wet wze wsi wrh wmu ad2ant.1 ad8antlr adantr $.

    $( Deduction adding 10 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad10antr $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $=
      wph wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wmu wa wla wa wps
      wka wph wps wch wth wta wet wze wsi wrh wmu wla ad2ant.1 ad9antr adantr
      $.

    $( Deduction adding 10 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad10antlr $p |- ( ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $=
      wch wph wa wth wa wta wa wet wa wze wa wsi wa wrh wa wmu wa wla wa wps
      wka wph wps wch wth wta wet wze wsi wrh wmu wla ad2ant.1 ad9antlr adantr
      $.
  $}

  ${
    ad2ant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    ad2ant2l $p |- ( ( ( th /\ ph ) /\ ( ta /\ ps ) ) -> ch ) $=
      wph wta wps wa wch wth wph wps wch wta ad2ant2.1 adantrl adantll $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    ad2ant2r $p |- ( ( ( ph /\ th ) /\ ( ps /\ ta ) ) -> ch ) $=
      wph wps wta wa wch wth wph wps wch wta ad2ant2.1 adantrr adantlr $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       23-Nov-2007.) $)
    ad2ant2lr $p |- ( ( ( th /\ ph ) /\ ( ps /\ ta ) ) -> ch ) $=
      wph wps wta wa wch wth wph wps wch wta ad2ant2.1 adantrr adantll $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       24-Nov-2007.) $)
    ad2ant2rl $p |- ( ( ( ph /\ th ) /\ ( ta /\ ps ) ) -> ch ) $=
      wph wta wps wa wch wth wph wps wch wta ad2ant2.1 adantrl adantlr $.
  $}

  $( Simplification of a conjunction.  (Contributed by NM, 18-Mar-2007.) $)
  simpll $p |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $=
    wph wph wps wch wph id ad2antrr $.

  $( Simplification of a conjunction.  (Contributed by NM, 20-Mar-2007.) $)
  simplr $p |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $=
    wps wps wph wch wps id ad2antlr $.

  $( Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)
  simprl $p |- ( ( ph /\ ( ps /\ ch ) ) -> ps ) $=
    wps wps wph wch wps id ad2antrl $.

  $( Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)
  simprr $p |- ( ( ph /\ ( ps /\ ch ) ) -> ch ) $=
    wch wch wph wps wch id ad2antll $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ph ) $=
    wph wps wa wph wch wth wph wps simpl ad2antrr $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simpllr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ps ) $=
    wph wps wa wps wch wth wph wps simpr ad2antrr $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrl $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ps ) $=
    wps wch wa wps wph wth wps wch simpl ad2antlr $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrr $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ch ) $=
    wps wch wa wch wph wth wps wch simpr ad2antlr $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprll $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ps ) $=
    wps wch wa wps wph wth wps wch simpl ad2antrl $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprlr $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ch ) $=
    wps wch wa wch wph wth wps wch simpr ad2antrl $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrl $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ch ) $=
    wch wth wa wch wph wps wch wth simpl ad2antll $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrr $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> th ) $=
    wch wth wa wth wph wps wch wth simpr ad2antll $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-4l $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ph ) $=
    wph wps wa wch wa wth wa wph wta wph wps wch wth simplll adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-4r $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ps ) $=
    wph wps wa wch wa wth wa wps wta wph wps wch wth simpllr adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-5l $p |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) -> ph ) $=
    wph wps wa wch wa wth wa wta wa wph wet wph wps wch wth wta simp-4l adantr
    $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-5r $p |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) -> ps ) $=
    wph wps wa wch wa wth wa wta wa wps wet wph wps wch wth wta simp-4r adantr
    $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-6l $p |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) -> ph ) $=
    wph wps wa wch wa wth wa wta wa wet wa wph wze wph wps wch wth wta wet
    simp-5l adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-6r $p |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) -> ps ) $=
    wph wps wa wch wa wth wa wta wa wet wa wps wze wph wps wch wth wta wet
    simp-5r adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-7l $p |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) -> ph ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wph wsi wph wps wch wth wta
    wet wze simp-6l adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-7r $p |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) -> ps ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wps wsi wph wps wch wth wta
    wet wze simp-6r adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-8l $p |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) -> ph ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wsi wa wph wrh wph wps wch
    wth wta wet wze wsi simp-7l adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-8r $p |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wsi wa wps wrh wph wps wch
    wth wta wet wze wsi simp-7r adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-9l $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ph ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wph wmu wph wps
    wch wth wta wet wze wsi wrh simp-8l adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-9r $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wps wmu wph wps
    wch wth wta wet wze wsi wrh simp-8r adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-10l $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ph ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wmu wa wph wla
    wph wps wch wth wta wet wze wsi wrh wmu simp-9l adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-10r $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wmu wa wps wla
    wph wps wch wth wta wet wze wsi wrh wmu simp-9r adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-11l $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ph ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wmu wa wla wa
    wph wka wph wps wch wth wta wet wze wsi wrh wmu wla simp-10l adantr $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-11r $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $=
    wph wps wa wch wa wth wa wta wa wet wa wze wa wsi wa wrh wa wmu wa wla wa
    wps wka wph wps wch wth wta wet wze wsi wrh wmu wla simp-10r adantr $.

  $( Disjunction of antecedents.  Compare Theorem *4.77 of [WhiteheadRussell]
     p. 121.  (Contributed by NM, 30-May-1994.)  (Proof shortened by Wolf
     Lammen, 9-Dec-2012.) $)
  jaob $p |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    wph wch wo wps wi wph wps wi wch wps wi wa wph wch wo wps wi wph wps wi wch
    wps wi wph wps wch pm2.67-2 wch wph wch wo wps wch wph olc imim1i jca wps
    wph wch pm3.44 impbii $.

  ${
    jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    $( Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 23-Oct-2005.) $)
    jaoian $p |- ( ( ( ph \/ th ) /\ ps ) -> ch ) $=
      wph wth wo wps wch wph wps wch wi wth wph wps wch jaoian.1 ex wth wps wch
      jaoian.2 ex jaoi imp $.
  $}

  ${
    jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    $( Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 14-Oct-2005.) $)
    jaodan $p |- ( ( ph /\ ( ps \/ th ) ) -> ch ) $=
      wph wps wth wo wch wph wps wch wth wph wps wch jaodan.1 ex wph wth wch
      jaodan.2 ex jaod imp $.

    jaodan.3 $e |- ( ph -> ( ps \/ th ) ) $.
    $( Eliminate a disjunction in a deduction.  A translation of natural
       deduction rule ` \/ ` E ( ` \/ ` elimination), see ~ natded .
       (Contributed by Mario Carneiro, 29-May-2016.) $)
    mpjaodan $p |- ( ph -> ch ) $=
      wph wps wth wo wch jaodan.3 wph wps wch wth jaodan.1 jaodan.2 jaodan
      mpdan $.
  $}

  $( Theorem *4.77 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.77 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) <->
                ( ( ps \/ ch ) -> ph ) ) $=
    wps wch wo wph wi wps wph wi wch wph wi wa wps wph wch jaob bicomi $.

  $( Theorem *2.63 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.63 $p |- ( ( ph \/ ps ) -> ( ( -. ph \/ ps ) -> ps ) ) $=
    wph wps wo wph wn wps wps wph wps pm2.53 wph wps wo wps idd jaod $.

  $( Theorem *2.64 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.64 $p |- ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) ) $=
    wph wps wn wo wph wps wo wph wph wph wps wo wph wi wps wn wph wph wps wo
    ax-1 wps wph orel2 jaoi com12 $.

  ${
    pm2.61ian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61ian.2 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    $( Elimination of an antecedent.  (Contributed by NM, 1-Jan-2005.) $)
    pm2.61ian $p |- ( ps -> ch ) $=
      wph wps wch wi wph wps wch pm2.61ian.1 ex wph wn wps wch pm2.61ian.2 ex
      pm2.61i $.
  $}

  ${
    pm2.61dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61dan.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    $( Elimination of an antecedent.  (Contributed by NM, 1-Jan-2005.) $)
    pm2.61dan $p |- ( ph -> ch ) $=
      wph wps wch wph wps wch pm2.61dan.1 ex wph wps wn wch pm2.61dan.2 ex
      pm2.61d $.
  $}

  ${
    pm2.61ddan.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm2.61ddan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm2.61ddan.3 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
    $( Elimination of two antecedents.  (Contributed by NM, 9-Jul-2013.) $)
    pm2.61ddan $p |- ( ph -> th ) $=
      wph wps wth pm2.61ddan.1 wph wps wn wa wch wth wph wch wth wps wn
      pm2.61ddan.2 adantlr wph wps wn wch wn wth pm2.61ddan.3 anassrs pm2.61dan
      pm2.61dan $.
  $}

  ${
    pm2.61dda.1 $e |- ( ( ph /\ -. ps ) -> th ) $.
    pm2.61dda.2 $e |- ( ( ph /\ -. ch ) -> th ) $.
    pm2.61dda.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Elimination of two antecedents.  (Contributed by NM, 9-Jul-2013.) $)
    pm2.61dda $p |- ( ph -> th ) $=
      wph wps wth wph wps wa wch wth wph wps wch wth pm2.61dda.3 anassrs wph
      wch wn wth wps pm2.61dda.2 adantlr pm2.61dan pm2.61dda.1 pm2.61dan $.
  $}

  ${
    condan.1 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    condan.2 $e |- ( ( ph /\ -. ps ) -> -. ch ) $.
    $( Proof by contradiction.  (Contributed by NM, 9-Feb-2006.)  (Proof
       shortened by Wolf Lammen, 19-Jun-2014.) $)
    condan $p |- ( ph -> ps ) $=
      wph wps wn wn wps wph wps wn wch condan.1 condan.2 pm2.65da wps notnot2
      syl $.
  $}

  $( Introduce one conjunct as an antecedent to the other.  "abai" stands for
     "and, biconditional, and, implication".  (Contributed by NM,
     12-Aug-1993.)  (Proof shortened by Wolf Lammen, 7-Dec-2012.) $)
  abai $p |- ( ( ph /\ ps ) <-> ( ph /\ ( ph -> ps ) ) ) $=
    wph wps wph wps wi wph wps biimt pm5.32i $.

  $( Theorem *5.53 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.53 $p |- ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <->
                ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) ) $=
    wph wps wo wch wo wth wi wph wps wo wth wi wch wth wi wa wph wth wi wps wth
    wi wa wch wth wi wa wph wps wo wth wch jaob wph wps wo wth wi wph wth wi
    wps wth wi wa wch wth wi wph wth wps jaob anbi1i bitri $.

  $( Swap two conjuncts.  Note that the first digit (1) in the label refers to
     the outer conjunct position, and the next digit (2) to the inner conjunct
     position.  (Contributed by NM, 12-Mar-1995.) $)
  an12 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ps /\ ( ph /\ ch ) ) ) $=
    wph wps wa wch wa wps wph wa wch wa wph wps wch wa wa wps wph wch wa wa wph
    wps wa wps wph wa wch wph wps ancom anbi1i wph wps wch anass wps wph wch
    anass 3bitr3i $.

  $( A rearrangement of conjuncts.  (Contributed by NM, 12-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 25-Dec-2012.) $)
  an32 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $=
    wph wps wa wch wa wph wps wch wa wa wps wph wch wa wa wph wch wa wps wa wph
    wps wch anass wph wps wch an12 wps wph wch wa ancom 3bitri $.

  $( A rearrangement of conjuncts.  (Contributed by NM, 24-Jun-2012.)  (Proof
     shortened by Wolf Lammen, 31-Dec-2012.) $)
  an13 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ch /\ ( ps /\ ph ) ) ) $=
    wph wps wch wa wa wps wph wch wa wa wps wph wa wch wa wch wps wph wa wa wph
    wps wch an12 wps wph wch anass wps wph wa wch ancom 3bitr2i $.

  $( A rearrangement of conjuncts.  (Contributed by NM, 24-Jun-2012.)  (Proof
     shortened by Wolf Lammen, 31-Dec-2012.) $)
  an31 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps ) /\ ph ) ) $=
    wph wps wch wa wa wch wps wph wa wa wph wps wa wch wa wch wps wa wph wa wph
    wps wch an13 wph wps wch anass wch wps wph anass 3bitr4i $.

  ${
    an12s.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Swap two conjuncts in antecedent.  The label suffix "s" means that
       ~ an12 is combined with ~ syl (or a variant).  (Contributed by NM,
       13-Mar-1996.) $)
    an12s $p |- ( ( ps /\ ( ph /\ ch ) ) -> th ) $=
      wps wph wch wa wa wph wps wch wa wa wth wps wph wch an12 an12s.1 sylbi $.

    $( Inference commuting a nested conjunction in antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    ancom2s $p |- ( ( ph /\ ( ch /\ ps ) ) -> th ) $=
      wch wps wa wph wps wch wa wth wch wps pm3.22 an12s.1 sylan2 $.

    $( Swap two conjuncts in antecedent.  (Contributed by NM, 31-May-2006.) $)
    an13s $p |- ( ( ch /\ ( ps /\ ph ) ) -> th ) $=
      wch wps wph wth wph wps wch wth wph wps wch wth an12s.1 exp32 com13 imp32
      $.
  $}

  ${
    an32s.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Swap two conjuncts in antecedent.  (Contributed by NM, 13-Mar-1996.) $)
    an32s $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $=
      wph wch wa wps wa wph wps wa wch wa wth wph wch wps an32 an32s.1 sylbi $.

    $( Inference commuting a nested conjunction in antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    ancom1s $p |- ( ( ( ps /\ ph ) /\ ch ) -> th ) $=
      wps wph wa wph wps wa wch wth wps wph pm3.22 an32s.1 sylan $.

    $( Swap two conjuncts in antecedent.  (Contributed by NM, 31-May-2006.) $)
    an31s $p |- ( ( ( ch /\ ps ) /\ ph ) -> th ) $=
      wch wps wph wth wph wps wch wth wph wps wch wth an32s.1 exp31 com13 imp31
      $.
  $}

  ${
    anass1rs.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Commutative-associative law for conjunction in an antecedent.
       (Contributed by Jeff Madsen, 19-Jun-2011.) $)
    anass1rs $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $=
      wph wps wch wth wph wps wch wth anass1rs.1 anassrs an32s $.
  $}

  $( Absorption into embedded conjunct.  (Contributed by NM, 4-Sep-1995.)
     (Proof shortened by Wolf Lammen, 16-Nov-2013.) $)
  anabs1 $p |- ( ( ( ph /\ ps ) /\ ph ) <-> ( ph /\ ps ) ) $=
    wph wps wa wph wps wa wph wa wph wps wa wph wph wps simpl pm4.71i bicomi $.

  $( Absorption into embedded conjunct.  (Contributed by NM, 20-Jul-1996.)
     (Proof shortened by Wolf Lammen, 9-Dec-2012.) $)
  anabs5 $p |- ( ( ph /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    wph wph wps wa wps wph wps wph wps wa wph wps ibar bicomd pm5.32i $.

  $( Absorption into embedded conjunct.  (Contributed by NM, 20-Jul-1996.)
     (Proof shortened by Wolf Lammen, 17-Nov-2013.) $)
  anabs7 $p |- ( ( ps /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    wph wps wa wps wph wps wa wa wph wps wa wps wph wps simpr pm4.71ri bicomi
    $.

  ${
    anabsan.1 $e |- ( ( ( ph /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent with conjunction.  (Contributed by NM,
       24-Mar-1996.) $)
    anabsan $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wph wph wa wps wch wph pm4.24 anabsan.1 sylanb $.
  $}

  ${
    anabss1.1 $e |- ( ( ( ph /\ ps ) /\ ph ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 31-Dec-2012.) $)
    anabss1 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wph wch anabss1.1 an32s anabsan $.
  $}

  ${
    anabss4.1 $e |- ( ( ( ps /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.) $)
    anabss4 $p |- ( ( ph /\ ps ) -> ch ) $=
      wps wph wch wps wph wch anabss4.1 anabss1 ancoms $.
  $}

  ${
    anabss5.1 $e |- ( ( ph /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       10-May-1994.)  (Proof shortened by Wolf Lammen, 1-Jan-2013.) $)
    anabss5 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wph wps wch anabss5.1 anassrs anabsan $.
  $}

  ${
    anabsi5.1 $e |- ( ph -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       11-Jun-1995.)  (Proof shortened by Wolf Lammen, 18-Nov-2013.) $)
    anabsi5 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wph wps wa wch anabsi5.1 imp anabss5 $.
  $}

  ${
    anabsi6.1 $e |- ( ph -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       14-Aug-2000.) $)
    anabsi6 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wph wch anabsi6.1 ancomsd anabsi5 $.
  $}

  ${
    anabsi7.1 $e |- ( ps -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 18-Nov-2013.) $)
    anabsi7 $p |- ( ( ph /\ ps ) -> ch ) $=
      wps wph wch wps wph wch anabsi7.1 anabsi6 ancoms $.
  $}

  ${
    anabsi8.1 $e |- ( ps -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       26-Sep-1999.) $)
    anabsi8 $p |- ( ( ph /\ ps ) -> ch ) $=
      wps wph wch wps wph wch anabsi8.1 anabsi5 ancoms $.
  $}

  ${
    anabss7.1 $e |- ( ( ps /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 19-Nov-2013.) $)
    anabss7 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wps wph wps wch anabss7.1 anassrs anabss4 $.
  $}

  ${
    anabsan2.1 $e |- ( ( ph /\ ( ps /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent with conjunction.  (Contributed by NM,
       10-May-2004.) $)
    anabsan2 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wps wch anabsan2.1 an12s anabss7 $.
  $}

  ${
    anabss3.1 $e |- ( ( ( ph /\ ps ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 1-Jan-2013.) $)
    anabss3 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wps wch anabss3.1 anasss anabsan2 $.
  $}

  $( Rearrangement of 4 conjuncts.  (Contributed by NM, 10-Jul-1994.) $)
  an4 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
              ( ( ph /\ ch ) /\ ( ps /\ th ) ) ) $=
    wph wps wch wth wa wa wa wph wch wps wth wa wa wa wph wps wa wch wth wa wa
    wph wch wa wps wth wa wa wps wch wth wa wa wch wps wth wa wa wph wps wch
    wth an12 anbi2i wph wps wch wth wa anass wph wch wps wth wa anass 3bitr4i
    $.

  $( Rearrangement of 4 conjuncts.  (Contributed by NM, 7-Feb-1996.) $)
  an42 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                 ( ( ph /\ ch ) /\ ( th /\ ps ) ) ) $=
    wph wps wa wch wth wa wa wph wch wa wps wth wa wa wph wch wa wth wps wa wa
    wph wps wch wth an4 wps wth wa wth wps wa wph wch wa wps wth ancom anbi2i
    bitri $.

  ${
    an4s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent.  (Contributed by NM,
       10-Aug-1995.) $)
    an4s $p |- ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) -> ta ) $=
      wph wch wa wps wth wa wa wph wps wa wch wth wa wa wta wph wch wps wth an4
      an4s.1 sylbi $.
  $}

  ${
    an41r3s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent.  (Contributed by NM,
       10-Aug-1995.) $)
    an42s $p |- ( ( ( ph /\ ch ) /\ ( th /\ ps ) ) -> ta ) $=
      wph wch wa wps wth wta wph wps wch wth wta an41r3s.1 an4s ancom2s $.
  $}

  $( Distribution of conjunction over conjunction.  (Contributed by NM,
     14-Aug-1995.) $)
  anandi $p |- ( ( ph /\ ( ps /\ ch ) ) <->
               ( ( ph /\ ps ) /\ ( ph /\ ch ) ) ) $=
    wph wps wch wa wa wph wph wa wps wch wa wa wph wps wa wph wch wa wa wph wph
    wa wph wps wch wa wph anidm anbi1i wph wph wps wch an4 bitr3i $.

  $( Distribution of conjunction over conjunction.  (Contributed by NM,
     24-Aug-1995.) $)
  anandir $p |- ( ( ( ph /\ ps ) /\ ch ) <->
               ( ( ph /\ ch ) /\ ( ps /\ ch ) ) ) $=
    wph wps wa wch wa wph wps wa wch wch wa wa wph wch wa wps wch wa wa wch wch
    wa wch wph wps wa wch anidm anbi2i wph wps wch wch an4 bitr3i $.

  ${
    anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent.
       (Contributed by NM, 7-Jun-2004.) $)
    anandis $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      wph wps wch wa wta wph wps wph wch wta anandis.1 an4s anabsan $.
  $}

  ${
    anandirs.1 $e |- ( ( ( ph /\ ch ) /\ ( ps /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent.
       (Contributed by NM, 7-Jun-2004.) $)
    anandirs $p |- ( ( ( ph /\ ps ) /\ ch ) -> ta ) $=
      wph wps wa wch wta wph wch wps wch wta anandirs.1 an4s anabsan2 $.
  $}

  ${
    impbida.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    impbida.2 $e |- ( ( ph /\ ch ) -> ps ) $.
    $( Deduce an equivalence from two implications.  (Contributed by NM,
       17-Feb-2007.) $)
    impbida $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wph wps wch impbida.1 ex wph wch wps impbida.2 ex impbid $.
  $}

  $( Theorem *3.48 of [WhiteheadRussell] p. 114.  (Contributed by NM,
     28-Jan-1997.) $)
  pm3.48 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) )
      -> ( ( ph \/ ch ) -> ( ps \/ th ) ) ) $=
    wph wps wi wph wps wth wo wch wth wi wch wps wps wth wo wph wps wth orc
    imim2i wth wps wth wo wch wth wps olc imim2i jaao $.

  $( Theorem *3.45 (Fact) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.45 $p |- ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $=
    wph wps wi wph wps wch wph wps wi id anim1d $.

  ${
    im2an9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    im2an9.2 $e |- ( th -> ( ta -> et ) ) $.
    $( Deduction joining nested implications to form implication of
       conjunctions.  (Contributed by NM, 29-Feb-1996.) $)
    im2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      wph wth wa wps wch wta wet wph wps wch wi wth im2an9.1 adantr wth wta wet
      wi wph im2an9.2 adantl anim12d $.

    $( Deduction joining nested implications to form implication of
       conjunctions.  (Contributed by NM, 29-Feb-1996.) $)
    im2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      wph wth wps wta wa wch wet wa wi wph wps wch wth wta wet im2an9.1
      im2an9.2 im2anan9 ancoms $.
  $}

  ${
    anim12dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    anim12dan.2 $e |- ( ( ph /\ th ) -> ta ) $.
    $( Conjoin antecedents and consequents in a deduction.  (Contributed by
       Mario Carneiro, 12-May-2014.) $)
    anim12dan $p |- ( ( ph /\ ( ps /\ th ) ) -> ( ch /\ ta ) ) $=
      wph wps wth wa wch wta wa wph wps wch wth wta wph wps wch anim12dan.1 ex
      wph wth wta anim12dan.2 ex anim12d imp $.
  $}

  ${
    orim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    orim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       10-May-1994.) $)
    orim12d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ ta ) ) ) $=
      wph wps wch wi wth wta wi wps wth wo wch wta wo wi orim12d.1 orim12d.2
      wps wch wth wta pm3.48 syl2anc $.
  $}

  ${
    orim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       23-Apr-1995.) $)
    orim1d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ th ) ) ) $=
      wph wps wch wth wth orim1d.1 wph wth idd orim12d $.

    $( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       23-Apr-1995.) $)
    orim2d $p |- ( ph -> ( ( th \/ ps ) -> ( th \/ ch ) ) ) $=
      wph wth wth wps wch wph wth idd orim1d.1 orim12d $.
  $}

  $( Axiom *1.6 (Sum) of [WhiteheadRussell] p. 97.  (Contributed by NM,
     3-Jan-2005.) $)
  orim2 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    wps wch wi wps wch wph wps wch wi id orim2d $.

  $( Theorem *2.38 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
  pm2.38 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ch \/ ph ) ) ) $=
    wps wch wi wps wch wph wps wch wi id orim1d $.

  $( Theorem *2.36 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
  pm2.36 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ch \/ ph ) ) ) $=
    wph wps wo wps wph wo wps wch wi wch wph wo wph wps pm1.4 wph wps wch
    pm2.38 syl5 $.

  $( Theorem *2.37 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
  pm2.37 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ph \/ ch ) ) ) $=
    wps wch wi wps wph wo wch wph wo wph wch wo wph wps wch pm2.38 wch wph
    pm1.4 syl6 $.

  $( Theorem *2.73 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.73 $p |- ( ( ph -> ps )
       -> ( ( ( ph \/ ps ) \/ ch ) -> ( ps \/ ch ) ) ) $=
    wph wps wi wph wps wo wps wch wph wps pm2.621 orim1d $.

  $( Theorem *2.74 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  pm2.74 $p |- ( ( ps -> ph )
      -> ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ch ) ) ) $=
    wps wph wi wph wps wo wph wch wps wph wph wps wo wph wi wps wph orel2 wph
    wph wps wo ax-1 ja orim1d $.

  $( Disjunction distributes over implication.  (Contributed by Wolf Lammen,
     5-Jan-2013.) $)
  orimdi $p |- ( ( ph \/ ( ps -> ch ) )
        <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    wph wn wps wch wi wi wph wn wps wi wph wn wch wi wi wph wps wch wi wo wph
    wps wo wph wch wo wi wph wn wps wch imdi wph wps wch wi df-or wph wps wo
    wph wn wps wi wph wch wo wph wn wch wi wph wps df-or wph wch df-or imbi12i
    3bitr4i $.

  $( Theorem *2.76 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.76 $p |- ( ( ph \/ ( ps -> ch ) )
      -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    wph wps wch wi wo wph wps wo wph wch wo wi wph wps wch orimdi biimpi $.

  $( Theorem *2.75 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 4-Jan-2013.) $)
  pm2.75 $p |- ( ( ph \/ ps )
       -> ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) ) $=
    wph wps wch wi wo wph wps wo wph wch wo wph wps wch pm2.76 com12 $.

  $( Theorem *2.8 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)
  pm2.8 $p |- ( ( ph \/ ps ) -> ( ( -. ps \/ ch ) -> ( ph \/ ch ) ) ) $=
    wph wps wo wps wn wph wch wph wps wo wph wps wph wps pm2.53 con1d orim1d $.

  $( Theorem *2.81 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.81 $p |- ( ( ps -> ( ch -> th ) )
      -> ( ( ph \/ ps ) -> ( ( ph \/ ch ) -> ( ph \/ th ) ) ) ) $=
    wps wch wth wi wi wph wps wo wph wch wth wi wo wph wch wo wph wth wo wi wph
    wps wch wth wi orim2 wph wch wth pm2.76 syl6 $.

  $( Theorem *2.82 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.82 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th )
      -> ( ( ph \/ ps ) \/ th ) ) ) $=
    wph wps wo wch wo wph wch wn wo wph wps wo wth wph wps wo wph wch wn wo wph
    wps wo wi wch wph wps wo wph wch wn wo ax-1 wch wch wn wps wph wch wps
    pm2.24 orim2d jaoi orim1d $.

  $( Theorem *2.85 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)
  pm2.85 $p |- ( ( ( ph \/ ps ) -> ( ph \/ ch ) )
      -> ( ph \/ ( ps -> ch ) ) ) $=
    wph wps wch wi wo wph wps wo wph wch wo wi wph wps wch orimdi biimpri $.

  ${
    pm3.2ni.1 $e |- -. ph $.
    pm3.2ni.2 $e |- -. ps $.
    $( Infer negated disjunction of negated premises.  (Contributed by NM,
       4-Apr-1995.) $)
    pm3.2ni $p |- -. ( ph \/ ps ) $=
      wph wps wo wph pm3.2ni.1 wph wph wps wph id wps wph pm3.2ni.2 pm2.21i
      jaoi mto $.
  $}

  $( Absorption of redundant internal disjunct.  Compare Theorem *4.45 of
     [WhiteheadRussell] p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 28-Feb-2014.) $)
  orabs $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $=
    wph wph wps wo wph wps orc pm4.71ri $.

  $( Absorb a disjunct into a conjunct.  (Contributed by Roy F. Longton,
     23-Jun-2005.)  (Proof shortened by Wolf Lammen, 10-Nov-2013.) $)
  oranabs $p |- ( ( ( ph \/ -. ps ) /\ ps ) <-> ( ph /\ ps ) ) $=
    wps wph wps wn wo wph wps wph wps wn wph wo wph wps wn wo wps wph biortn
    wps wn wph orcom syl6rbb pm5.32ri $.

  $( Two propositions are equivalent if they are both true.  Theorem *5.1 of
     [WhiteheadRussell] p. 123.  (Contributed by NM, 21-May-1994.) $)
  pm5.1 $p |- ( ( ph /\ ps ) -> ( ph <-> ps ) ) $=
    wph wps wph wps wb wph wps pm5.501 biimpa $.

  $( Two propositions are equivalent if they are both false.  Theorem *5.21 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 21-May-1994.) $)
  pm5.21 $p |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) ) $=
    wph wn wps wn wph wps wb wph wps pm5.21im imp $.

  $( Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.43 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) )
      -> ( ph -> ( ps /\ ch ) ) ) $=
    wph wps wi wph wch wi wph wps wch wa wi wph wps wch pm3.43i imp $.

  $( Distributive law for implication over conjunction.  Compare Theorem *4.76
     of [WhiteheadRussell] p. 121.  (Contributed by NM, 3-Apr-1994.)  (Proof
     shortened by Wolf Lammen, 27-Nov-2013.) $)
  jcab $p |- ( ( ph -> ( ps /\ ch ) )
      <-> ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    wph wps wch wa wi wph wps wi wph wch wi wa wph wps wch wa wi wph wps wi wph
    wch wi wps wch wa wps wph wps wch simpl imim2i wps wch wa wch wph wps wch
    simpr imim2i jca wph wps wch pm3.43 impbii $.

  $( Distributive law for disjunction.  Theorem *4.41 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 7-May-2011.)  (Proof shortened by Wolf Lammen, 28-Nov-2013.) $)
  ordi $p |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
    wph wn wps wch wa wi wph wn wps wi wph wn wch wi wa wph wps wch wa wo wph
    wps wo wph wch wo wa wph wn wps wch jcab wph wps wch wa df-or wph wps wo
    wph wn wps wi wph wch wo wph wn wch wi wph wps df-or wph wch df-or anbi12i
    3bitr4i $.

  $( Distributive law for disjunction.  (Contributed by NM, 12-Aug-1994.) $)
  ordir $p |- ( ( ( ph /\ ps ) \/ ch ) <->
              ( ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    wch wph wps wa wo wch wph wo wch wps wo wa wph wps wa wch wo wph wch wo wps
    wch wo wa wch wph wps ordi wph wps wa wch orcom wph wch wo wch wph wo wps
    wch wo wch wps wo wph wch orcom wps wch orcom anbi12i 3bitr4i $.

  $( Theorem *4.76 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.76 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <->
                ( ph -> ( ps /\ ch ) ) ) $=
    wph wps wch wa wi wph wps wi wph wch wi wa wph wps wch jcab bicomi $.

  $( Distributive law for conjunction.  Theorem *4.4 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 5-Jan-2013.) $)
  andi $p |- ( ( ph /\ ( ps \/ ch ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $=
    wph wps wch wo wa wph wps wa wph wch wa wo wph wps wph wps wa wph wch wa wo
    wch wph wps wa wph wch wa orc wph wch wa wph wps wa olc jaodan wph wps wa
    wph wps wch wo wa wph wch wa wps wps wch wo wph wps wch orc anim2i wch wps
    wch wo wph wch wps olc anim2i jaoi impbii $.

  $( Distributive law for conjunction.  (Contributed by NM, 12-Aug-1994.) $)
  andir $p |- ( ( ( ph \/ ps ) /\ ch ) <->
              ( ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    wch wph wps wo wa wch wph wa wch wps wa wo wph wps wo wch wa wph wch wa wps
    wch wa wo wch wph wps andi wph wps wo wch ancom wph wch wa wch wph wa wps
    wch wa wch wps wa wph wch ancom wps wch ancom orbi12i 3bitr4i $.

  $( Double distributive law for disjunction.  (Contributed by NM,
     12-Aug-1994.) $)
  orddi $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ( ph \/ ch ) /\ ( ph \/ th ) ) /\
              ( ( ps \/ ch ) /\ ( ps \/ th ) ) ) ) $=
    wph wps wa wch wth wa wo wph wch wth wa wo wps wch wth wa wo wa wph wch wo
    wph wth wo wa wps wch wo wps wth wo wa wa wph wps wch wth wa ordir wph wch
    wth wa wo wph wch wo wph wth wo wa wps wch wth wa wo wps wch wo wps wth wo
    wa wph wch wth ordi wps wch wth ordi anbi12i bitri $.

  $( Double distributive law for conjunction.  (Contributed by NM,
     12-Aug-1994.) $)
  anddi $p |- ( ( ( ph \/ ps ) /\ ( ch \/ th ) ) <->
              ( ( ( ph /\ ch ) \/ ( ph /\ th ) ) \/
              ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ) $=
    wph wps wo wch wth wo wa wph wch wth wo wa wps wch wth wo wa wo wph wch wa
    wph wth wa wo wps wch wa wps wth wa wo wo wph wps wch wth wo andir wph wch
    wth wo wa wph wch wa wph wth wa wo wps wch wth wo wa wps wch wa wps wth wa
    wo wph wch wth andi wps wch wth andi orbi12i bitri $.

  $( Prove formula-building rules for the biconditional connective. $)

  $( Theorem *4.39 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.39 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph \/ ps ) <-> ( ch \/ th ) ) ) $=
    wph wch wb wps wth wb wa wph wch wps wth wph wch wb wps wth wb simpl wph
    wch wb wps wth wb simpr orbi12d $.

  $( Theorem *4.38 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.38 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph /\ ps ) <-> ( ch /\ th ) ) ) $=
    wph wch wb wps wth wb wa wph wch wps wth wph wch wb wps wth wb simpl wph
    wch wb wps wth wb simpr anbi12d $.

  ${
    bi2an9.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi2an9.2 $e |- ( th -> ( ta <-> et ) ) $.
    $( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 31-Jul-1995.) $)
    bi2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      wph wps wta wa wch wta wa wth wch wet wa wph wps wch wta bi2an9.1 anbi1d
      wth wta wet wch bi2an9.2 anbi2d sylan9bb $.

    $( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 19-Feb-1996.) $)
    bi2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      wph wth wps wta wa wch wet wa wb wph wps wch wth wta wet bi2an9.1
      bi2an9.2 bi2anan9 ancoms $.

    $( Deduction joining two biconditionals with different antecedents.
       (Contributed by NM, 12-May-2004.) $)
    bi2bian9 $p |- ( ( ph /\ th ) -> ( ( ps <-> ta ) <-> ( ch <-> et ) ) ) $=
      wph wth wa wps wch wta wet wph wps wch wb wth bi2an9.1 adantr wth wta wet
      wb wph bi2an9.2 adantl bibi12d $.
  $}

  $( Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 30-Jan-2013.) $)
  pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    wph wps wi wps wph wps wo wb wph wps wi wps wph wps wo wps wph olc wph wps
    pm2.621 impbid2 wph wph wps wo wps wph wps wo wb wps wph wps orc wps wph
    wps wo bi2 syl5 impbii $.

  $( Simplify an implication between implications.  (Contributed by Paul
     Chapman, 17-Nov-2012.)  (Proof shortened by Wolf Lammen, 3-Apr-2013.) $)
  imimorb $p |- ( ( ( ps -> ch ) -> ( ph -> ch ) ) <->
                  ( ph -> ( ps \/ ch ) ) ) $=
    wps wch wi wph wch wi wi wph wps wch wi wch wi wi wph wps wch wo wi wps wch
    wi wph wch bi2.04 wps wch wo wps wch wi wch wi wph wps wch dfor2 imbi2i
    bitr4i $.

  $( Theorem *5.33 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.33 $p |- ( ( ph /\ ( ps -> ch ) ) <->
                ( ph /\ ( ( ph /\ ps ) -> ch ) ) ) $=
    wph wps wch wi wph wps wa wch wi wph wps wph wps wa wch wph wps ibar imbi1d
    pm5.32i $.

  $( Theorem *5.36 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.36 $p |- ( ( ph /\ ( ph <-> ps ) ) <-> ( ps /\ ( ph <-> ps ) ) ) $=
    wph wps wb wph wps wph wps wb id pm5.32ri $.

  ${
    bianabs.1 $e |- ( ph -> ( ps <-> ( ph /\ ch ) ) ) $.
    $( Absorb a hypothesis into the second member of a biconditional.
       (Contributed by FL, 15-Feb-2007.) $)
    bianabs $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wph wch wa wch bianabs.1 wph wch ibar bitr4d $.
  $}

  $( Absorption of disjunction into equivalence.  (Contributed by NM,
     6-Aug-1995.)  (Proof shortened by Wolf Lammen, 3-Nov-2013.) $)
  oibabs $p |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) ) $=
    wph wps wo wph wps wb wi wph wps wb wph wps wo wph wps wb wph wps wb wph
    wps wo wn wph wn wps wn wa wph wps wb wph wps ioran wph wps pm5.21 sylbi
    wph wps wb id ja wph wps wb wph wps wo ax-1 impbii $.

  $( Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111 (who
     call it the "law of contradiction").  (Contributed by NM, 16-Sep-1993.)
     (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
  pm3.24 $p |- -. ( ph /\ -. ph ) $=
    wph wph wi wph wph wn wa wn wph id wph wph iman mpbi $.

  $( Theorem *2.26 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
  pm2.26 $p |- ( -. ph \/ ( ( ph -> ps ) -> ps ) ) $=
    wph wph wps wi wps wi wph wps pm2.27 imori $.

  $( Theorem *5.11 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.11 $p |- ( ( ph -> ps ) \/ ( -. ph -> ps ) ) $=
    wph wps wi wph wn wps wi wph wps pm2.5 orri $.

  $( Theorem *5.12 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.12 $p |- ( ( ph -> ps ) \/ ( ph -> -. ps ) ) $=
    wph wps wi wph wps wn wi wph wps pm2.51 orri $.

  $( Theorem *5.14 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.14 $p |- ( ( ph -> ps ) \/ ( ps -> ch ) ) $=
    wph wps wi wps wch wi wph wps wi wn wps wch wps wph wps wi wps wph ax-1
    con3i pm2.21d orri $.

  $( Theorem *5.13 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
  pm5.13 $p |- ( ( ph -> ps ) \/ ( ps -> ph ) ) $=
    wph wps wph pm5.14 $.

  $( Theorem *5.17 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)
  pm5.17 $p |- ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) ) $=
    wph wps wn wb wps wn wph wb wps wn wph wi wph wps wn wi wa wph wps wo wph
    wps wa wn wa wph wps wn bicom wps wn wph dfbi2 wps wn wph wi wph wps wo wph
    wps wn wi wph wps wa wn wph wps wo wps wph wo wps wn wph wi wph wps orcom
    wps wph df-or bitr2i wph wps imnan anbi12i 3bitrri $.

  $( Theorem *5.15 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)
  pm5.15 $p |- ( ( ph <-> ps ) \/ ( ph <-> -. ps ) ) $=
    wph wps wb wph wps wn wb wph wps wb wn wph wps wn wb wph wps xor3 biimpi
    orri $.

  $( Theorem *5.16 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 17-Oct-2013.) $)
  pm5.16 $p |- -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) ) $=
    wph wps wb wph wps wn wb wn wi wph wps wb wph wps wn wb wa wn wph wps wb
    wph wps wn wb wn wph wps pm5.18 biimpi wph wps wb wph wps wn wb imnan mpbi
    $.

  $( Two ways to express "exclusive or."  Theorem *5.22 of [WhiteheadRussell]
     p. 124.  (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf
     Lammen, 22-Jan-2013.) $)
  xor $p |- ( -. ( ph <-> ps ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    wph wps wn wa wps wph wn wa wo wph wps wb wph wps wi wps wph wi wa wph wps
    wn wa wn wps wph wn wa wn wa wph wps wb wph wps wn wa wps wph wn wa wo wn
    wph wps wi wph wps wn wa wn wps wph wi wps wph wn wa wn wph wps iman wps
    wph iman anbi12i wph wps dfbi2 wph wps wn wa wps wph wn wa ioran 3bitr4ri
    con1bii $.

  $( Two ways to express "exclusive or."  (Contributed by NM, 3-Jan-2005.)
     (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)
  nbi2 $p |- ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $=
    wph wps wb wn wph wps wn wb wph wps wo wph wps wa wn wa wph wps xor3 wph
    wps pm5.17 bitr4i $.

  $( An alternate definition of the biconditional.  Theorem *5.23 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 3-Nov-2013.) $)
  dfbi3 $p |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) ) $=
    wph wps wn wb wn wph wps wn wn wa wps wn wph wn wa wo wph wps wb wph wps wa
    wph wn wps wn wa wo wph wps wn xor wph wps pm5.18 wph wps wa wph wps wn wn
    wa wph wn wps wn wa wps wn wph wn wa wps wps wn wn wph wps notnot anbi2i
    wph wn wps wn ancom orbi12i 3bitr4i $.

  $( Theorem *5.24 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.24 $p |- ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    wph wps wb wph wps wn wa wps wph wn wa wo wph wps wa wph wn wps wn wa wo
    wph wps xor wph wps dfbi3 xchnxbi $.

  $( Conjunction distributes over exclusive-or, using ` -. ( ph <-> ps ) ` to
     express exclusive-or.  This is one way to interpret the distributive law
     of multiplication over addition in modulo 2 arithmetic.  (Contributed by
     NM, 3-Oct-2008.) $)
  xordi $p |- ( ( ph /\ -. ( ps <-> ch ) ) <->
                -. ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    wph wps wch wb wn wa wph wps wch wb wi wph wps wa wph wch wa wb wph wps wch
    wb annim wph wps wch pm5.32 xchbinx $.

  $( A wff disjoined with truth is true.  (Contributed by NM, 23-May-1999.) $)
  biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $=
    wph wph wph wps wo wph wps orc wph wph wps wo ax-1 impbid2 $.

  $( Theorem *5.55 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 20-Jan-2013.) $)
  pm5.55 $p |- ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ) $=
    wph wps wo wph wb wph wps wo wps wb wph wps wo wps wb wph wps wo wph wb wph
    wph wps wo wph wb wph wps wo wps wb wph wph wph wps wo wph wps biort bicomd
    wph wn wps wph wps wo wph wps biorf bicomd nsyl4 con1i orri $.


