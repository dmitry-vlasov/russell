
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_disjunction_and_conjunction.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Miscellaneous theorems of propositional calculus

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    pm5.21nd.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm5.21nd.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm5.21nd.3 $e |- ( th -> ( ps <-> ch ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional.
       (Contributed by NM, 20-Nov-2005.)  (Proof shortened by Wolf Lammen,
       4-Nov-2013.) $)
    pm5.21nd $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wth wps wch wph wps wth pm5.21nd.1 ex wph wch wth pm5.21nd.2 ex wth
      wps wch wb wi wph pm5.21nd.3 a1i pm5.21ndd $.
  $}

  $( Theorem *5.35 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.35 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps <-> ch ) ) ) $=
    wph wps wi wph wch wi wa wph wps wch wph wps wi wph wch wi pm5.1 pm5.74rd
    $.

  $( Theorem *5.54 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 7-Nov-2013.) $)
  pm5.54 $p |- ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) ) $=
    wph wps wa wph wb wph wps wa wps wb wph wps wa wph wps wa wph wb wps wps
    wph wps wa wph wb wph wps wph wph wps wa wps wph iba bicomd adantl wps wph
    wph wps wa wps wph iba bicomd pm5.21ni orri $.

  ${
    baib.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional.  (Contributed by NM,
       13-May-1999.) $)
    baib $p |- ( ps -> ( ph <-> ch ) ) $=
      wps wch wps wch wa wph wps wch ibar baib.1 syl6rbbr $.

    $( Move conjunction outside of biconditional.  (Contributed by NM,
       11-Jul-1994.) $)
    baibr $p |- ( ps -> ( ch <-> ph ) ) $=
      wps wph wch wph wps wch baib.1 baib bicomd $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    rbaib $p |- ( ch -> ( ph <-> ps ) ) $=
      wph wch wps wph wps wch wa wch wps wa baib.1 wps wch ancom bitri baib $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    rbaibr $p |- ( ch -> ( ps <-> ph ) ) $=
      wph wch wps wph wps wch wa wch wps wa baib.1 wps wch ancom bitri baibr $.
  $}

  ${
    baibd.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    baibd $p |- ( ( ph /\ ch ) -> ( ps <-> th ) ) $=
      wph wps wch wth wa wch wth baibd.1 wch wth wch wth wa wch wth ibar bicomd
      sylan9bb $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    rbaibd $p |- ( ( ph /\ th ) -> ( ps <-> ch ) ) $=
      wph wps wch wth wa wth wch baibd.1 wth wch wch wth wa wth wch iba bicomd
      sylan9bb $.
  $}

  $( Theorem *5.44 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.44 $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) <->
                ( ph -> ( ps /\ ch ) ) ) ) $=
    wph wps wch wa wi wph wps wi wph wch wi wph wps wch jcab baibr $.

  $( Conjunction in antecedent versus disjunction in consequent.  Theorem *5.6
     of [WhiteheadRussell] p. 125.  (Contributed by NM, 8-Jun-1994.) $)
  pm5.6 $p |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ) $=
    wph wps wn wa wch wi wph wps wn wch wi wi wph wps wch wo wi wph wps wn wch
    impexp wps wch wo wps wn wch wi wph wps wch df-or imbi2i bitr4i $.

  ${
    orcanai.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Change disjunction in consequent to conjunction in antecedent.
       (Contributed by NM, 8-Jun-1994.) $)
    orcanai $p |- ( ( ph /\ -. ps ) -> ch ) $=
      wph wps wn wch wph wps wch orcanai.1 ord imp $.
  $}


  ${
    intnan.1 $e |- -. ph $.
    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       16-Sep-1993.) $)
    intnan $p |- -. ( ps /\ ph ) $=
      wps wph wa wph intnan.1 wps wph simpr mto $.

    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       3-Apr-1995.) $)
    intnanr $p |- -. ( ph /\ ps ) $=
      wph wps wa wph intnan.1 wph wps simpl mto $.
  $}

  ${
    intnand.1 $e |- ( ph -> -. ps ) $.
    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) $)
    intnand $p |- ( ph -> -. ( ch /\ ps ) ) $=
      wph wps wch wps wa intnand.1 wch wps simpr nsyl $.

    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) $)
    intnanrd $p |- ( ph -> -. ( ps /\ ch ) ) $=
      wph wps wps wch wa intnand.1 wps wch simpl nsyl $.
  $}

  ${
    mpbiran.1 $e |- ps $.
    mpbiran.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional.  (Contributed by NM,
       27-Feb-1996.) $)
    mpbiran $p |- ( ph <-> ch ) $=
      wph wps wch wa wch mpbiran.2 wps wch mpbiran.1 biantrur bitr4i $.
  $}

  ${
    mpbiran2.1 $e |- ch $.
    mpbiran2.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional.  (Contributed by NM,
       22-Feb-1996.) $)
    mpbiran2 $p |- ( ph <-> ps ) $=
      wph wps wch wa wps mpbiran2.2 wch wps mpbiran2.1 biantru bitr4i $.
  $}

  ${
    mpbir2an.1 $e |- ps $.
    mpbir2an.2 $e |- ch $.
    mpbiran2an.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       10-May-2005.) $)
    mpbir2an $p |- ph $=
      wph wch mpbir2an.2 wph wps wch mpbir2an.1 mpbiran2an.1 mpbiran mpbir $.
  $}

  ${
    mpbi2and.1 $e |- ( ph -> ps ) $.
    mpbi2and.2 $e |- ( ph -> ch ) $.
    mpbi2and.3 $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       6-Nov-2011.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    mpbi2and $p |- ( ph -> th ) $=
      wph wps wch wa wth wph wps wch mpbi2and.1 mpbi2and.2 jca mpbi2and.3 mpbid
      $.
  $}

  ${
    mpbir2and.1 $e |- ( ph -> ch ) $.
    mpbir2and.2 $e |- ( ph -> th ) $.
    mpbir2and.3 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       6-Nov-2011.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    mpbir2and $p |- ( ph -> ps ) $=
      wph wps wch wth wa wph wch wth mpbir2and.1 mpbir2and.2 jca mpbir2and.3
      mpbird $.
  $}

  $( Theorem *5.62 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm5.62 $p |- ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) ) $=
    wph wps wa wps wn wo wph wps wn wo wps wps wn wo wps exmid wph wps wps wn
    ordir mpbiran2 $.

  $( Theorem *5.63 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 25-Dec-2012.) $)
  pm5.63 $p |- ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) ) $=
    wph wph wn wps wa wo wph wps wo wph wph wn wps wa wo wph wph wn wo wph wps
    wo wph exmid wph wph wn wps ordi mpbiran bicomi $.

  ${
    bianfi.1 $e |- -. ph $.
    $( A wff conjoined with falsehood is false.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)
    bianfi $p |- ( ph <-> ( ps /\ ph ) ) $=
      wph wps wph wa bianfi.1 wph wps bianfi.1 intnan 2false $.
  $}

  ${
    bianfd.1 $e |- ( ph -> -. ps ) $.
    $( A wff conjoined with falsehood is false.  (Contributed by NM,
       27-Mar-1995.)  (Proof shortened by Wolf Lammen, 5-Nov-2013.) $)
    bianfd $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      wph wps wps wch wa bianfd.1 wph wps wch bianfd.1 intnanrd 2falsed $.
  $}

  $( Theorem *4.43 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)
  pm4.43 $p |- ( ph <-> ( ( ph \/ ps ) /\ ( ph \/ -. ps ) ) ) $=
    wph wph wps wps wn wa wo wph wps wo wph wps wn wo wa wps wps wn wa wph wps
    pm3.24 biorfi wph wps wps wn ordi bitri $.

  $( Theorem *4.82 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.82 $p |- ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph ) $=
    wph wps wi wph wps wn wi wa wph wn wph wps wi wph wps wn wi wph wn wph wps
    pm2.65 imp wph wn wph wps wi wph wps wn wi wph wps pm2.21 wph wps wn pm2.21
    jca impbii $.

  $( Theorem *4.83 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.83 $p |- ( ( ( ph -> ps ) /\ ( -. ph -> ps ) ) <-> ps ) $=
    wps wph wph wn wo wps wi wph wps wi wph wn wps wi wa wph wph wn wo wps wph
    exmid a1bi wph wps wph wn jaob bitr2i $.

  $( Negation inferred from embedded conjunct.  (Contributed by NM,
     20-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-Nov-2012.) $)
  pclem6 $p |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps ) $=
    wps wph wps wph wn wa wb wps wph wn wps wph wn wa wb wph wps wph wn wa wb
    wn wps wph wn ibar wph wps wph wn wa nbbn sylib con2i $.

  $( A transitive law of equivalence.  Compare Theorem *4.22 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 18-Aug-1993.) $)
  biantr $p |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ) $=
    wch wps wb wph wch wb wph wps wb wch wps wb wch wps wph wch wps wb id
    bibi2d biimparc $.

  $( Disjunction distributes over the biconditional.  An axiom of system DS in
     Vladimir Lifschitz, "On calculational proofs" (1998),
     ~ http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.3384 .
     (Contributed by NM, 8-Jan-2005.)  (Proof shortened by Wolf Lammen,
     4-Feb-2013.) $)
  orbidi $p |- ( ( ph \/ ( ps <-> ch ) ) <->
                ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ) $=
    wph wn wps wch wb wi wph wn wps wi wph wn wch wi wb wph wps wch wb wo wph
    wps wo wph wch wo wb wph wn wps wch pm5.74 wph wps wch wb df-or wph wps wo
    wph wn wps wi wph wch wo wph wn wch wi wph wps df-or wph wch df-or bibi12i
    3bitr4i $.

  $( Lukasiewicz's shortest axiom for equivalential calculus.  Storrs McCall,
     ed., _Polish Logic 1920-1939_ (Oxford, 1967), p. 96.  (Contributed by NM,
     10-Jan-2005.) $)
  biluk $p |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) $=
    wph wps wb wch wps wph wch wb wb wb wch wps wb wph wch wb wb wph wps wb wch
    wb wps wph wch wb wb wb wph wps wb wch wps wph wch wb wb wb wb wph wps wb
    wch wb wps wph wb wch wb wps wph wch wb wb wph wps wb wps wph wb wch wph
    wps bicom bibi1i wps wph wch biass bitri wph wps wb wch wps wph wch wb wb
    biass mpbi wch wps wph wch wb biass bitr4i $.

  $( Disjunction distributes over the biconditional.  Theorem *5.7 of
     [WhiteheadRussell] p. 125.  This theorem is similar to ~ orbidi .
     (Contributed by Roy F. Longton, 21-Jun-2005.) $)
  pm5.7 $p |- ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <->
               ( ch \/ ( ph <-> ps ) ) ) $=
    wch wph wps wb wo wch wph wo wch wps wo wb wph wch wo wps wch wo wb wch wph
    wps orbidi wch wph wo wph wch wo wch wps wo wps wch wo wch wph orcom wch
    wps orcom bibi12i bitr2i $.

  $( Dijkstra-Scholten's Golden Rule for calculational proofs.  (Contributed by
     NM, 10-Jan-2005.) $)
  bigolden $p |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    wph wps wi wph wph wps wa wb wps wph wps wo wb wph wps wa wph wb wph wps
    pm4.71 wph wps pm4.72 wph wph wps wa bicom 3bitr3ri $.

  $( Theorem *5.71 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 23-Jun-2005.) $)
  pm5.71 $p |- ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <->
                ( ph /\ ch ) ) ) $=
    wps wch wn wph wps wo wch wa wph wch wa wb wps wn wph wps wo wph wch wps wn
    wph wps wo wph wps wph orel2 wph wps orc impbid1 anbi1d wch wn wch wph wps
    wo wph wch wph wps wo wph wb pm2.21 pm5.32rd ja $.

  $( Theorem *5.75 of [WhiteheadRussell] p. 126.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 23-Dec-2012.) $)
  pm5.75 $p |- ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) ->
                ( ( ph /\ -. ps ) <-> ch ) ) $=
    wph wps wch wo wb wph wps wn wa wch wps wn wa wch wps wn wi wch wph wps wch
    wo wb wph wps wn wa wps wch wo wps wn wa wch wps wn wa wph wps wch wo wps
    wn anbi1 wps wch wo wps wn wa wch wps wo wps wn wa wch wps wn wa wps wch wo
    wch wps wo wps wn wps wch orcom anbi1i wch wps pm5.61 bitri syl6bb wch wps
    wn wi wch wch wps wn wa wch wps wn wi wch wch wps wn wa wb wch wps wn
    pm4.71 biimpi bicomd sylan9bbr $.

  $( Removal of conjunct from one side of an equivalence.  (Contributed by NM,
     5-Aug-1993.) $)
  bimsc1 $p |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) )
               -> ( ch <-> ph ) ) $=
    wph wps wi wch wps wph wa wb wch wph wb wph wps wi wps wph wa wph wch wph
    wps wi wps wph wa wph wps wph simpr wph wps ancr impbid2 bibi2d biimpa $.

  $( The disjunction of the four possible combinations of two wffs and their
     negations is always true.  (Contributed by David Abernethy,
     28-Jan-2014.) $)
  4exmid $p |- ( ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) )
              \/ ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    wph wps wb wph wps wb wn wo wph wps wa wph wn wps wn wa wo wph wps wn wa
    wps wph wn wa wo wo wph wps wb exmid wph wps wb wph wps wa wph wn wps wn wa
    wo wph wps wb wn wph wps wn wa wps wph wn wa wo wph wps dfbi3 wph wps xor
    orbi12i mpbi $.

  ${
    ecase2d.1 $e |- ( ph -> ps ) $.
    ecase2d.2 $e |- ( ph -> -. ( ps /\ ch ) ) $.
    ecase2d.3 $e |- ( ph -> -. ( ps /\ th ) ) $.
    ecase2d.4 $e |- ( ph -> ( ta \/ ( ch \/ th ) ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM, 21-Apr-1994.)
       (Proof shortened by Wolf Lammen, 22-Dec-2012.) $)
    ecase2d $p |- ( ph -> ta ) $=
      wph wta wta wch wth wo wph wta idd wph wch wta wth wph wps wch wta
      ecase2d.1 wph wps wch wa wta ecase2d.2 pm2.21d mpand wph wps wth wta
      ecase2d.1 wph wps wth wa wta ecase2d.3 pm2.21d mpand jaod ecase2d.4
      mpjaod $.
  $}

  ${
    ecase3.1 $e |- ( ph -> ch ) $.
    ecase3.2 $e |- ( ps -> ch ) $.
    ecase3.3 $e |- ( -. ( ph \/ ps ) -> ch ) $.
    $( Inference for elimination by cases.  (Contributed by NM, 23-Mar-1995.)
       (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)
    ecase3 $p |- ch $=
      wph wps wo wch wph wch wps ecase3.1 ecase3.2 jaoi ecase3.3 pm2.61i $.
  $}

  ${
    ecase.1 $e |- ( -. ph -> ch ) $.
    ecase.2 $e |- ( -. ps -> ch ) $.
    ecase.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference for elimination by cases.  (Contributed by NM,
       13-Jul-2005.) $)
    ecase $p |- ch $=
      wph wps wch wph wps wch ecase.3 ex ecase.1 ecase.2 pm2.61nii $.
  $}

  ${
    ecase3d.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3d.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3d.3 $e |- ( ph -> ( -. ( ps \/ ch ) -> th ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM, 2-May-1996.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    ecase3d $p |- ( ph -> th ) $=
      wph wps wch wo wth wph wps wth wch ecase3d.1 ecase3d.2 jaod ecase3d.3
      pm2.61d $.
  $}

  ${
    ecased.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    ecased.2 $e |- ( ph -> ( -. ch -> th ) ) $.
    ecased.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM, 8-Oct-2012.) $)
    ecased $p |- ( ph -> th ) $=
      wph wps wn wch wn wth ecased.1 ecased.2 wps wn wch wn wo wn wps wch wa
      wph wth wps wch pm3.11 ecased.3 syl5 ecase3d $.
  $}

  ${
    ecase3ad.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3ad.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3ad.3 $e |- ( ph -> ( ( -. ps /\ -. ch ) -> th ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM,
       24-May-2013.) $)
    ecase3ad $p |- ( ph -> th ) $=
      wph wps wn wch wn wth wps wn wn wps wph wth wps notnot2 ecase3ad.1 syl5
      wch wn wn wch wph wth wch notnot2 ecase3ad.2 syl5 ecase3ad.3 ecased $.
  $}

  ${
    ccase.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase.2 $e |- ( ( ch /\ ps ) -> ta ) $.
    ccase.3 $e |- ( ( ph /\ th ) -> ta ) $.
    ccase.4 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Inference for combining cases.  (Contributed by NM, 29-Jul-1999.)
       (Proof shortened by Wolf Lammen, 6-Jan-2013.) $)
    ccase $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      wph wch wo wps wta wth wph wps wta wch ccase.1 ccase.2 jaoian wph wth wta
      wch ccase.3 ccase.4 jaoian jaodan $.
  $}

  ${
    ccased.1 $e |- ( ph -> ( ( ps /\ ch ) -> et ) ) $.
    ccased.2 $e |- ( ph -> ( ( th /\ ch ) -> et ) ) $.
    ccased.3 $e |- ( ph -> ( ( ps /\ ta ) -> et ) ) $.
    ccased.4 $e |- ( ph -> ( ( th /\ ta ) -> et ) ) $.
    $( Deduction for combining cases.  (Contributed by NM, 9-May-2004.) $)
    ccased $p |- ( ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ) ) $=
      wps wth wo wch wta wo wa wph wet wps wch wth wta wph wet wi wph wps wch
      wa wet ccased.1 com12 wph wth wch wa wet ccased.2 com12 wph wps wta wa
      wet ccased.3 com12 wph wth wta wa wet ccased.4 com12 ccase com12 $.
  $}

  ${
    ccase2.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase2.2 $e |- ( ch -> ta ) $.
    ccase2.3 $e |- ( th -> ta ) $.
    $( Inference for combining cases.  (Contributed by NM, 29-Jul-1999.) $)
    ccase2 $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      wph wps wch wth wta ccase2.1 wch wta wps ccase2.2 adantr wth wta wph
      ccase2.3 adantl wth wta wch ccase2.3 adantl ccase $.
  $}

  ${
    4cases.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    4cases.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    4cases.3 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    4cases.4 $e |- ( ( -. ph /\ -. ps ) -> ch ) $.
    $( Inference eliminating two antecedents from the four possible cases that
       result from their true/false combinations.  (Contributed by NM,
       25-Oct-2003.) $)
    4cases $p |- ch $=
      wps wch wph wps wch 4cases.1 4cases.3 pm2.61ian wph wps wn wch 4cases.2
      4cases.4 pm2.61ian pm2.61i $.
  $}

  ${
    4casesdan.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    4casesdan.2 $e |- ( ( ph /\ ( ps /\ -. ch ) ) -> th ) $.
    4casesdan.3 $e |- ( ( ph /\ ( -. ps /\ ch ) ) -> th ) $.
    4casesdan.4 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
    $( Deduction eliminating two antecedents from the four possible cases that
       result from their true/false combinations.  (Contributed by NM,
       19-Mar-2013.) $)
    4casesdan $p |- ( ph -> th ) $=
      wps wch wph wth wi wph wps wch wa wth 4casesdan.1 expcom wph wps wch wn
      wa wth 4casesdan.2 expcom wph wps wn wch wa wth 4casesdan.3 expcom wph
      wps wn wch wn wa wth 4casesdan.4 expcom 4cases $.
  $}

  ${
    niabn.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) $)
    niabn $p |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) ) $=
      wch wps wa wps wph wn wch wps simpr wph wps niabn.1 pm2.24i pm5.21ni $.
  $}

  $( Lemma for an alternate version of weak deduction theorem.  (Contributed by
     NM, 2-Apr-1994.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 4-Dec-2012.) $)
  dedlem0a $p |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) ) $=
    wph wps wps wph wa wch wph wi wps wph wa wi wph wps iba wph wch wph wi wps
    wph wa wch wph wi wps wph wa wi wb wph wch ax-1 wch wph wi wps wph wa biimt
    syl bitrd $.

  $( Lemma for an alternate version of weak deduction theorem.  (Contributed by
     NM, 2-Apr-1994.) $)
  dedlem0b $p |- ( -. ph -> ( ps <-> ( ( ps -> ph ) -> ( ch /\ ph ) ) ) ) $=
    wph wn wps wps wph wi wch wph wa wi wph wn wps wph wi wps wch wph wa wph wn
    wph wch wph wa wps wph wch wph wa pm2.21 imim2d com23 wps wph wi wch wph wa
    wi wph wn wps wps wph wi wch wph wa wi wps wph wps wn wps wph wi wch wph wa
    wph wps wph pm2.21 wch wph simpr imim12i con1d com12 impbid $.

  $( Lemma for weak deduction theorem.  (Contributed by NM, 26-Jun-2002.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  dedlema $p |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    wph wps wps wph wa wch wph wn wa wo wps wph wps wph wa wch wph wn wa wo wps
    wph wa wch wph wn wa orc expcom wph wps wph wa wps wch wph wn wa wps wph wa
    wps wi wph wps wph simpl a1i wph wph wn wps wch wph wps pm2.24 adantld jaod
    impbid $.

  $( Lemma for weak deduction theorem.  (Contributed by NM, 15-May-1999.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  dedlemb $p |- ( -. ph -> ( ch <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    wph wn wch wps wph wa wch wph wn wa wo wch wph wn wps wph wa wch wph wn wa
    wo wch wph wn wa wps wph wa olc expcom wph wn wps wph wa wch wch wph wn wa
    wph wn wph wch wps wph wch pm2.21 adantld wch wph wn wa wch wi wph wn wch
    wph wn simpl a1i jaod impbid $.

  ${
    elimh.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( ch <-> ta ) ) $.
    elimh.2 $e |- ( ( ps <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    elimh.3 $e |- th $.
    $( Hypothesis builder for weak deduction theorem.  For more information,
       see the Deduction Theorem link on the Metamath Proof Explorer home
       page.  (Contributed by NM, 26-Jun-2002.) $)
    elimh $p |- ta $=
      wch wta wch wta wch wph wph wch wa wps wch wn wa wo wb wch wta wb wch wph
      wps dedlema elimh.1 syl ibi wch wn wth wta elimh.3 wch wn wps wph wch wa
      wps wch wn wa wo wb wth wta wb wch wph wps dedlemb elimh.2 syl mpbii
      pm2.61i $.
  $}

  ${
    dedt.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    dedt.2 $e |- ta $.
    $( The weak deduction theorem.  For more information, see the Deduction
       Theorem link on the Metamath Proof Explorer home page.  (Contributed by
       NM, 26-Jun-2002.) $)
    dedt $p |- ( ch -> th ) $=
      wch wph wph wch wa wps wch wn wa wo wb wth wch wph wps dedlema wph wph
      wch wa wps wch wn wa wo wb wth wta dedt.2 dedt.1 mpbiri syl $.
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This version
     of ~ con3 demonstrates the use of the weak deduction theorem ~ dedt to
     derive it from ~ con3i .  (Contributed by NM, 27-Jun-2002.)
     (Proof modification is discouraged.) $)
  con3th $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    wps wph wph wps wi wps wn wph wn wi wps wph wps wi wa wph wph wps wi wn wa
    wo wn wph wn wi wps wps wph wps wi wa wph wph wps wi wn wa wo wb wps wn wps
    wph wps wi wa wph wph wps wi wn wa wo wn wph wn wps wps wph wps wi wa wph
    wph wps wi wn wa wo wb wps wps wph wps wi wa wph wph wps wi wn wa wo wps
    wps wph wps wi wa wph wph wps wi wn wa wo wb id notbid imbi1d wph wps wph
    wps wi wa wph wph wps wi wn wa wo wps wph wph wps wi wph wph wi wph wps wph
    wps wi wa wph wph wps wi wn wa wo wi wps wps wph wps wi wa wph wph wps wi
    wn wa wo wb wps wps wph wps wi wa wph wph wps wi wn wa wo wph wps wps wph
    wps wi wa wph wph wps wi wn wa wo wb id imbi2d wph wps wph wps wi wa wph
    wph wps wi wn wa wo wb wph wps wph wps wi wa wph wph wps wi wn wa wo wph
    wph wps wph wps wi wa wph wph wps wi wn wa wo wb id imbi2d wph id elimh
    con3i dedt $.

  $( The consensus theorem.  This theorem and its dual (with ` \/ ` and ` /\ `
     interchanged) are commonly used in computer logic design to eliminate
     redundant terms from Boolean expressions.  Specifically, we prove that the
     term ` ( ps /\ ch ) ` on the left-hand side is redundant.  (Contributed by
     NM, 16-May-2003.)  (Proof shortened by Andrew Salmon, 13-May-2011.)
     (Proof shortened by Wolf Lammen, 20-Jan-2013.) $)
  consensus $p |- ( ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) \/ ( ps /\ ch ) ) <->
                      ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) ) $=
    wph wps wa wph wn wch wa wo wps wch wa wo wph wps wa wph wn wch wa wo wph
    wps wa wph wn wch wa wo wph wps wa wph wn wch wa wo wps wch wa wph wps wa
    wph wn wch wa wo id wph wps wch wa wph wps wa wph wn wch wa wo wph wps wph
    wps wa wph wn wch wa wo wch wph wps wa wph wn wch wa orc adantrr wph wn wch
    wph wps wa wph wn wch wa wo wps wph wn wch wa wph wps wa olc adantrl
    pm2.61ian jaoi wph wps wa wph wn wch wa wo wps wch wa orc impbii $.

  $( Theorem *4.42 of [WhiteheadRussell] p. 119.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm4.42 $p |- ( ph <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) ) $=
    wps wph wph wps wa wph wps wn wa wo wb wps wph wph dedlema wps wph wph
    dedlemb pm2.61i $.

  ${
    ninba.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) $)
    ninba $p |- ( -. ps -> ( -. ph <-> ( ch /\ ps ) ) ) $=
      wps wn wch wps wa wph wn wph wps wch ninba.1 niabn bicomd $.
  $}

  ${
    prlem1.1 $e |- ( ph -> ( et <-> ch ) ) $.
    prlem1.2 $e |- ( ps -> -. th ) $.
    $( A specialized lemma for set theory (to derive the Axiom of Pairing).
       (Contributed by NM, 18-Oct-1995.)  (Proof shortened by Andrew Salmon,
       13-May-2011.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)
    prlem1 $p |- ( ph -> ( ps ->
                  ( ( ( ps /\ ch ) \/ ( th /\ ta ) ) -> et ) ) ) $=
      wph wps wps wch wa wth wta wa wo wet wi wph wps wch wa wet wps wth wta wa
      wph wch wet wps wph wet wch prlem1.1 biimprd adantld wps wth wet wta wps
      wth wet prlem1.2 pm2.21d adantrd jaao ex $.
  $}

  $( A specialized lemma for set theory (to derive the Axiom of Pairing).
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
     13-May-2011.)  (Proof shortened by Wolf Lammen, 9-Dec-2012.) $)
  prlem2 $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ph \/ ch ) /\ ( ( ph /\ ps ) \/ ( ch /\ th ) ) ) ) $=
    wph wps wa wch wth wa wo wph wch wo wph wps wa wph wch wth wa wch wph wps
    simpl wch wth simpl orim12i pm4.71ri $.

  ${
    oplem1.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    oplem1.2 $e |- ( ph -> ( th \/ ta ) ) $.
    oplem1.3 $e |- ( ps <-> th ) $.
    oplem1.4 $e |- ( ch -> ( th <-> ta ) ) $.
    $( A specialized lemma for set theory (ordered pair theorem).  (Contributed
       by NM, 18-Oct-1995.)  (Proof shortened by Wolf Lammen, 8-Dec-2012.) $)
    oplem1 $p |- ( ph -> ps ) $=
      wph wth wps wph wth wph wth wn wch wta wa wth wph wth wn wch wta wth wn
      wps wn wph wch wps wth oplem1.3 notbii wph wps wch oplem1.1 ord syl5bir
      wph wth wta oplem1.2 ord jcad wch wth wta oplem1.4 biimpar syl6 pm2.18d
      oplem1.3 sylibr $.
  $}

  $( Lemma used in construction of real numbers.  (Contributed by NM,
     4-Sep-1995.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  rnlem $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
  ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) /\ ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) ) $=
    wph wps wa wch wth wa wa wph wch wa wps wth wa wa wph wth wa wps wch wa wa
    wa wph wps wa wch wth wa wa wph wch wa wps wth wa wa wph wth wa wps wch wa
    wa wph wps wa wch wth wa wa wph wch wa wps wth wa wa wph wps wch wth an4
    biimpi wph wth wa wps wch wa wa wph wps wa wch wth wa wa wph wth wps wch
    an42 biimpri jca wph wth wa wps wch wa wa wph wps wa wch wth wa wa wph wch
    wa wps wth wa wa wph wth wa wps wch wa wa wph wps wa wch wth wa wa wph wth
    wps wch an42 biimpi adantl impbii $.

  $( A single axiom for Boolean algebra known as DN_1.  See
     ~ http://www-unix.mcs.anl.gov/~~mccune/papers/basax/v12.pdf .
     (Contributed by Jeffrey Hankins, 3-Jul-2009.)  (Proof shortened by Andrew
     Salmon, 13-May-2011.)  (Proof shortened by Wolf Lammen, 6-Jan-2013.) $)
  dn1 $p |- ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/
            -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch ) $=
    wch wph wps wo wn wch wo wph wch wo wa wph wps wo wn wch wo wph wch wn wch
    wth wo wn wo wn wo wa wph wps wo wn wch wo wn wph wch wn wch wth wo wn wo
    wn wo wn wo wn wch wch wph wps wo wn wph wa wo wph wps wo wn wch wo wph wch
    wo wa wph wps wo wn wph wa wch wph wps wo wn wph wn wi wph wps wo wn wph wa
    wn wph wps pm2.45 wph wps wo wn wph imnan mpbi biorfi wch wph wps wo wn wph
    wa wo wph wps wo wn wph wa wch wo wph wps wo wn wch wo wph wch wo wa wch
    wph wps wo wn wph wa orcom wph wps wo wn wph wch ordir bitri bitri wph wch
    wo wph wch wn wch wth wo wn wo wn wo wph wps wo wn wch wo wch wch wn wch
    wth wo wn wo wn wph wch wch wch wth wo wa wch wn wch wth wo wn wo wn wch
    wth pm4.45 wch wch wth wo anor bitri orbi2i anbi2i wph wps wo wn wch wo wph
    wch wn wch wth wo wn wo wn wo anor 3bitrri $.


