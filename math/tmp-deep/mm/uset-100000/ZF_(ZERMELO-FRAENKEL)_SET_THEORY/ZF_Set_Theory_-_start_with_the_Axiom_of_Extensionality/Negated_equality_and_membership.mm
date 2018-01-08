
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Class_form_not-free_predicate.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Negated equality and membership

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new connectives. $)
  $c =/= $. $( Not equal to (equal sign with slash through it). $)
  $c e/ $. $( Not an element of (epsilon with slash through it). $)

  $( Extend wff notation to include inequality. $)
  wne $a wff A =/= B $.

  $( Extend wff notation to include negated membership. $)
  wnel $a wff A e/ B $.

  $( Define inequality.  (Contributed by NM, 5-Aug-1993.) $)
  df-ne $a |- ( A =/= B <-> -. A = B ) $.

  $( Define negated membership.  (Contributed by NM, 7-Aug-1994.) $)
  df-nel $a |- ( A e/ B <-> -. A e. B ) $.

  $( Negation of inequality.  (Contributed by NM, 9-Jun-2006.) $)
  nne $p |- ( -. A =/= B <-> A = B ) $=
    cA cB wceq cA cB wne wn cA cB wne cA cB wceq cA cB df-ne con2bii bicomi $.

  $( No class is unequal to itself.  (Contributed by Stefan O'Rear,
     1-Jan-2015.) $)
  neirr $p |- -. A =/= A $=
    cA cA wne wn cA cA wceq cA eqid cA cA nne mpbir $.

  $( Excluded middle with equality and inequality.  (Contributed by NM,
     3-Feb-2012.) $)
  exmidne $p |- ( A = B \/ A =/= B ) $=
    cA cB wceq cA cB wne wo cA cB wceq cA cB wceq wn wo cA cB wceq exmid cA cB
    wne cA cB wceq wn cA cB wceq cA cB df-ne orbi2i mpbir $.

  $( Law of noncontradiction with equality and inequality.  (Contributed by NM,
     3-Feb-2012.) $)
  nonconne $p |- -. ( A = B /\ A =/= B ) $=
    cA cB wceq cA cB wne wa cA cB wceq cA cB wceq wn wa cA cB wceq pm3.24 cA cB
    wne cA cB wceq wn cA cB wceq cA cB df-ne anbi2i mtbir $.

  $( Equality theorem for inequality.  (Contributed by NM, 19-Nov-1994.) $)
  neeq1 $p |- ( A = B -> ( A =/= C <-> B =/= C ) ) $=
    cA cB wceq cA cC wceq wn cB cC wceq wn cA cC wne cB cC wne cA cB wceq cA cC
    wceq cB cC wceq cA cB cC eqeq1 notbid cA cC df-ne cB cC df-ne 3bitr4g $.

  $( Equality theorem for inequality.  (Contributed by NM, 19-Nov-1994.) $)
  neeq2 $p |- ( A = B -> ( C =/= A <-> C =/= B ) ) $=
    cA cB wceq cC cA wceq wn cC cB wceq wn cC cA wne cC cB wne cA cB wceq cC cA
    wceq cC cB wceq cA cB cC eqeq2 notbid cC cA df-ne cC cB df-ne 3bitr4g $.

  ${
    neeq1i.1 $e |- A = B $.
    $( Inference for inequality.  (Contributed by NM, 29-Apr-2005.) $)
    neeq1i $p |- ( A =/= C <-> B =/= C ) $=
      cA cB wceq cA cC wne cB cC wne wb neeq1i.1 cA cB cC neeq1 ax-mp $.

    $( Inference for inequality.  (Contributed by NM, 29-Apr-2005.) $)
    neeq2i $p |- ( C =/= A <-> C =/= B ) $=
      cA cB wceq cC cA wne cC cB wne wb neeq1i.1 cA cB cC neeq2 ax-mp $.

    neeq12i.2 $e |- C = D $.
    $( Inference for inequality.  (Contributed by NM, 24-Jul-2012.) $)
    neeq12i $p |- ( A =/= C <-> B =/= D ) $=
      cA cC wne cA cD wne cB cD wne cC cD cA neeq12i.2 neeq2i cA cB cD neeq1i.1
      neeq1i bitri $.
  $}

  ${
    neeq1d.1 $e |- ( ph -> A = B ) $.
    $( Deduction for inequality.  (Contributed by NM, 25-Oct-1999.) $)
    neeq1d $p |- ( ph -> ( A =/= C <-> B =/= C ) ) $=
      wph cA cB wceq cA cC wne cB cC wne wb neeq1d.1 cA cB cC neeq1 syl $.

    $( Deduction for inequality.  (Contributed by NM, 25-Oct-1999.) $)
    neeq2d $p |- ( ph -> ( C =/= A <-> C =/= B ) ) $=
      wph cA cB wceq cC cA wne cC cB wne wb neeq1d.1 cA cB cC neeq2 syl $.

    neeq12d.2 $e |- ( ph -> C = D ) $.
    $( Deduction for inequality.  (Contributed by NM, 24-Jul-2012.) $)
    neeq12d $p |- ( ph -> ( A =/= C <-> B =/= D ) ) $=
      wph cA cC wne cB cC wne cB cD wne wph cA cB cC neeq1d.1 neeq1d wph cC cD
      cB neeq12d.2 neeq2d bitrd $.
  $}

  ${
    neneqd.1 $e |- ( ph -> A =/= B ) $.
    $( Deduction eliminating inequality definition.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    neneqd $p |- ( ph -> -. A = B ) $=
      wph cA cB wne cA cB wceq wn neneqd.1 cA cB df-ne sylib $.
  $}

  ${
    eqnetr.1 $e |- A = B $.
    eqnetr.2 $e |- B =/= C $.
    $( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
    eqnetri $p |- A =/= C $=
      cA cC wne cB cC wne eqnetr.2 cA cB cC eqnetr.1 neeq1i mpbir $.
  $}

  ${
    eqnetrd.1 $e |- ( ph -> A = B ) $.
    eqnetrd.2 $e |- ( ph -> B =/= C ) $.
    $( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
    eqnetrd $p |- ( ph -> A =/= C ) $=
      wph cA cC wne cB cC wne eqnetrd.2 wph cA cB cC eqnetrd.1 neeq1d mpbird $.
  $}

  ${
    eqnetrr.1 $e |- A = B $.
    eqnetrr.2 $e |- A =/= C $.
    $( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
    eqnetrri $p |- B =/= C $=
      cB cA cC cA cB eqnetrr.1 eqcomi eqnetrr.2 eqnetri $.
  $}

  ${
    eqnetrrd.1 $e |- ( ph -> A = B ) $.
    eqnetrrd.2 $e |- ( ph -> A =/= C ) $.
    $( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
    eqnetrrd $p |- ( ph -> B =/= C ) $=
      wph cB cA cC wph cA cB eqnetrrd.1 eqcomd eqnetrrd.2 eqnetrd $.
  $}

  ${
    neeqtr.1 $e |- A =/= B $.
    neeqtr.2 $e |- B = C $.
    $( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
    neeqtri $p |- A =/= C $=
      cA cB wne cA cC wne neeqtr.1 cB cC cA neeqtr.2 neeq2i mpbi $.
  $}

  ${
    neeqtrd.1 $e |- ( ph -> A =/= B ) $.
    neeqtrd.2 $e |- ( ph -> B = C ) $.
    $( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
    neeqtrd $p |- ( ph -> A =/= C ) $=
      wph cA cB wne cA cC wne neeqtrd.1 wph cB cC cA neeqtrd.2 neeq2d mpbid $.
  $}

  ${
    neeqtrr.1 $e |- A =/= B $.
    neeqtrr.2 $e |- C = B $.
    $( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
    neeqtrri $p |- A =/= C $=
      cA cB cC neeqtrr.1 cC cB neeqtrr.2 eqcomi neeqtri $.
  $}

  ${
    neeqtrrd.1 $e |- ( ph -> A =/= B ) $.
    neeqtrrd.2 $e |- ( ph -> C = B ) $.
    $( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
    neeqtrrd $p |- ( ph -> A =/= C ) $=
      wph cA cB cC neeqtrrd.1 wph cC cB neeqtrrd.2 eqcomd neeqtrd $.
  $}

  ${
    syl5eqner.1 $e |- B = A $.
    syl5eqner.2 $e |- ( ph -> B =/= C ) $.
    $( B chained equality inference for inequality.  (Contributed by NM,
       6-Jun-2012.) $)
    syl5eqner $p |- ( ph -> A =/= C ) $=
      wph cB cC wne cA cC wne syl5eqner.2 cB cA cC syl5eqner.1 neeq1i sylib $.
  $}

  ${
    3netr3d.1 $e |- ( ph -> A =/= B ) $.
    3netr3d.2 $e |- ( ph -> A = C ) $.
    3netr3d.3 $e |- ( ph -> B = D ) $.
    $( Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)
    3netr3d $p |- ( ph -> C =/= D ) $=
      wph cA cB wne cC cD wne 3netr3d.1 wph cA cC cB cD 3netr3d.2 3netr3d.3
      neeq12d mpbid $.
  $}

  ${
    3netr4d.1 $e |- ( ph -> A =/= B ) $.
    3netr4d.2 $e |- ( ph -> C = A ) $.
    3netr4d.3 $e |- ( ph -> D = B ) $.
    $( Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)
    3netr4d $p |- ( ph -> C =/= D ) $=
      wph cC cD wne cA cB wne 3netr4d.1 wph cC cA cD cB 3netr4d.2 3netr4d.3
      neeq12d mpbird $.
  $}

  ${
    3netr3g.1 $e |- ( ph -> A =/= B ) $.
    3netr3g.2 $e |- A = C $.
    3netr3g.3 $e |- B = D $.
    $( Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)
    3netr3g $p |- ( ph -> C =/= D ) $=
      wph cA cB wne cC cD wne 3netr3g.1 cA cC cB cD 3netr3g.2 3netr3g.3 neeq12i
      sylib $.
  $}

  ${
    3netr4g.1 $e |- ( ph -> A =/= B ) $.
    3netr4g.2 $e |- C = A $.
    3netr4g.3 $e |- D = B $.
    $( Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 14-Jun-2012.) $)
    3netr4g $p |- ( ph -> C =/= D ) $=
      wph cA cB wne cC cD wne 3netr4g.1 cC cA cD cB 3netr4g.2 3netr4g.3 neeq12i
      sylibr $.
  $}

  ${
    necon3abii.1 $e |- ( A = B <-> ph ) $.
    $( Deduction from equality to inequality.  (Contributed by NM,
       9-Nov-2007.) $)
    necon3abii $p |- ( A =/= B <-> -. ph ) $=
      cA cB wne cA cB wceq wph cA cB df-ne necon3abii.1 xchbinx $.
  $}

  ${
    necon3bbii.1 $e |- ( ph <-> A = B ) $.
    $( Deduction from equality to inequality.  (Contributed by NM,
       13-Apr-2007.) $)
    necon3bbii $p |- ( -. ph <-> A =/= B ) $=
      cA cB wne wph wn wph cA cB wph cA cB wceq necon3bbii.1 bicomi necon3abii
      bicomi $.
  $}

  ${
    necon3bii.1 $e |- ( A = B <-> C = D ) $.
    $( Inference from equality to inequality.  (Contributed by NM,
       23-Feb-2005.) $)
    necon3bii $p |- ( A =/= B <-> C =/= D ) $=
      cA cB wne cC cD wceq wn cC cD wne cC cD wceq cA cB necon3bii.1 necon3abii
      cC cD df-ne bitr4i $.
  $}

  ${
    necon3abid.1 $e |- ( ph -> ( A = B <-> ps ) ) $.
    $( Deduction from equality to inequality.  (Contributed by NM,
       21-Mar-2007.) $)
    necon3abid $p |- ( ph -> ( A =/= B <-> -. ps ) ) $=
      cA cB wne cA cB wceq wn wph wps wn cA cB df-ne wph cA cB wceq wps
      necon3abid.1 notbid syl5bb $.
  $}

  ${
    necon3bbid.1 $e |- ( ph -> ( ps <-> A = B ) ) $.
    $( Deduction from equality to inequality.  (Contributed by NM,
       2-Jun-2007.) $)
    necon3bbid $p |- ( ph -> ( -. ps <-> A =/= B ) ) $=
      wph cA cB wne wps wn wph wps cA cB wph wps cA cB wceq necon3bbid.1 bicomd
      necon3abid bicomd $.
  $}

  ${
    necon3bid.1 $e |- ( ph -> ( A = B <-> C = D ) ) $.
    $( Deduction from equality to inequality.  (Contributed by NM,
       23-Feb-2005.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon3bid $p |- ( ph -> ( A =/= B <-> C =/= D ) ) $=
      cA cB wne cA cB wceq wn wph cC cD wne cA cB df-ne wph cA cB wceq cC cD
      necon3bid.1 necon3bbid syl5bb $.
  $}

  ${
    necon3ad.1 $e |- ( ph -> ( ps -> A = B ) ) $.
    $( Contrapositive law deduction for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon3ad $p |- ( ph -> ( A =/= B -> -. ps ) ) $=
      wph wps cA cB wne wph wps cA cB wceq cA cB wne wn necon3ad.1 cA cB nne
      syl6ibr con2d $.
  $}

  ${
    necon3bd.1 $e |- ( ph -> ( A = B -> ps ) ) $.
    $( Contrapositive law deduction for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon3bd $p |- ( ph -> ( -. ps -> A =/= B ) ) $=
      wph cA cB wne wps cA cB wne wn cA cB wceq wph wps cA cB nne necon3bd.1
      syl5bi con1d $.
  $}

  ${
    necon3d.1 $e |- ( ph -> ( A = B -> C = D ) ) $.
    $( Contrapositive law deduction for inequality.  (Contributed by NM,
       10-Jun-2006.) $)
    necon3d $p |- ( ph -> ( C =/= D -> A =/= B ) ) $=
      wph cC cD wne cA cB wceq wn cA cB wne wph cA cB wceq cC cD necon3d.1
      necon3ad cA cB df-ne syl6ibr $.
  $}

  ${
    necon3i.1 $e |- ( A = B -> C = D ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       9-Aug-2006.) $)
    necon3i $p |- ( C =/= D -> A =/= B ) $=
      cA cB wceq cC cD wceq wi cC cD wne cA cB wne wi necon3i.1 cA cB wceq cC
      cD wceq wi cA cB cC cD cA cB wceq cC cD wceq wi id necon3d ax-mp $.
  $}

  ${
    necon3ai.1 $e |- ( ph -> A = B ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       23-May-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon3ai $p |- ( A =/= B -> -. ph ) $=
      wph cA cB wne wph cA cB wceq cA cB wne wn necon3ai.1 cA cB nne sylibr
      con2i $.
  $}

  ${
    necon3bi.1 $e |- ( A = B -> ph ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon3bi $p |- ( -. ph -> A =/= B ) $=
      cA cB wne wph cA cB wne wn cA cB wceq wph cA cB nne necon3bi.1 sylbi
      con1i $.
  $}

  ${
    necon1ai.1 $e |- ( -. ph -> A = B ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       12-Feb-2007.) $)
    necon1ai $p |- ( A =/= B -> ph ) $=
      cA cB wne cA cB wceq wn wph cA cB df-ne wph cA cB wceq necon1ai.1 con1i
      sylbi $.
  $}

  ${
    necon1bi.1 $e |- ( A =/= B -> ph ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon1bi $p |- ( -. ph -> A = B ) $=
      wph wn cA cB wne wn cA cB wceq cA cB wne wph necon1bi.1 con3i cA cB nne
      sylib $.
  $}

  ${
    necon1i.1 $e |- ( A =/= B -> C = D ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.) $)
    necon1i $p |- ( C =/= D -> A = B ) $=
      cA cB wceq cC cD cA cB wceq wn cA cB wne cC cD wceq cA cB df-ne necon1i.1
      sylbir necon1ai $.
  $}

  ${
    necon2ai.1 $e |- ( A = B -> -. ph ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon2ai $p |- ( ph -> A =/= B ) $=
      cA cB wne wph cA cB wne wn cA cB wceq wph wn cA cB nne necon2ai.1 sylbi
      con4i $.
  $}

  ${
    necon2bi.1 $e |- ( ph -> A =/= B ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       1-Apr-2007.) $)
    necon2bi $p |- ( A = B -> -. ph ) $=
      wph cA cB wceq wph cA cB necon2bi.1 neneqd con2i $.
  $}

  ${
    necon2i.1 $e |- ( A = B -> C =/= D ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.) $)
    necon2i $p |- ( C = D -> A =/= B ) $=
      cC cD wceq cA cB cA cB wceq cC cD necon2i.1 neneqd necon2ai $.
  $}

  ${
    necon2ad.1 $e |- ( ph -> ( A = B -> -. ps ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       19-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon2ad $p |- ( ph -> ( ps -> A =/= B ) ) $=
      wph cA cB wne wps cA cB wne wn cA cB wceq wph wps wn cA cB nne necon2ad.1
      syl5bi con4d $.
  $}

  ${
    necon2bd.1 $e |- ( ph -> ( ps -> A =/= B ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       13-Apr-2007.) $)
    necon2bd $p |- ( ph -> ( A = B -> -. ps ) ) $=
      wph wps cA cB wceq wph wps cA cB wne cA cB wceq wn necon2bd.1 cA cB df-ne
      syl6ib con2d $.
  $}

  ${
    necon2d.1 $e |- ( ph -> ( A = B -> C =/= D ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       28-Dec-2008.) $)
    necon2d $p |- ( ph -> ( C = D -> A =/= B ) ) $=
      wph cC cD wceq cA cB wph cA cB wceq cC cD wne cC cD wceq wn necon2d.1 cC
      cD df-ne syl6ib necon2ad $.
  $}

  ${
    necon1abii.1 $e |- ( -. ph <-> A = B ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.) $)
    necon1abii $p |- ( A =/= B <-> ph ) $=
      cA cB wne cA cB wceq wn wph cA cB df-ne wph cA cB wceq necon1abii.1
      con1bii bitri $.
  $}

  ${
    necon1bbii.1 $e |- ( A =/= B <-> ph ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.) $)
    necon1bbii $p |- ( -. ph <-> A = B ) $=
      cA cB wceq wph cA cB wceq wn cA cB wne wph cA cB df-ne necon1bbii.1
      bitr3i con1bii $.
  $}

  ${
    necon1abid.1 $e |- ( ph -> ( -. ps <-> A = B ) ) $.
    $( Contrapositive deduction for inequality.  (Contributed by NM,
       21-Aug-2007.) $)
    necon1abid $p |- ( ph -> ( A =/= B <-> ps ) ) $=
      cA cB wne cA cB wceq wn wph wps cA cB df-ne wph wps cA cB wceq
      necon1abid.1 con1bid syl5bb $.
  $}

  ${
    necon1bbid.1 $e |- ( ph -> ( A =/= B <-> ps ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       31-Jan-2008.) $)
    necon1bbid $p |- ( ph -> ( -. ps <-> A = B ) ) $=
      wph cA cB wceq wps cA cB wceq wn cA cB wne wph wps cA cB df-ne
      necon1bbid.1 syl5bbr con1bid $.
  $}

  ${
    necon2abii.1 $e |- ( A = B <-> -. ph ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       2-Mar-2007.) $)
    necon2abii $p |- ( ph <-> A =/= B ) $=
      cA cB wne wph wph cA cB cA cB wceq wph wn necon2abii.1 bicomi necon1abii
      bicomi $.
  $}

  ${
    necon2bbii.1 $e |- ( ph <-> A =/= B ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       13-Apr-2007.) $)
    necon2bbii $p |- ( A = B <-> -. ph ) $=
      wph wn cA cB wceq wph cA cB wph cA cB wne necon2bbii.1 bicomi necon1bbii
      bicomi $.
  $}

  ${
    necon2abid.1 $e |- ( ph -> ( A = B <-> -. ps ) ) $.
    $( Contrapositive deduction for inequality.  (Contributed by NM,
       18-Jul-2007.) $)
    necon2abid $p |- ( ph -> ( ps <-> A =/= B ) ) $=
      wph wps cA cB wceq wn cA cB wne wph cA cB wceq wps necon2abid.1 con2bid
      cA cB df-ne syl6bbr $.
  $}

  ${
    necon2bbid.1 $e |- ( ph -> ( ps <-> A =/= B ) ) $.
    $( Contrapositive deduction for inequality.  (Contributed by NM,
       13-Apr-2007.) $)
    necon2bbid $p |- ( ph -> ( A = B <-> -. ps ) ) $=
      wph wps cA cB wceq wph wps cA cB wne cA cB wceq wn necon2bbid.1 cA cB
      df-ne syl6bb con2bid $.
  $}

  ${
    necon4ai.1 $e |- ( A =/= B -> -. ph ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon4ai $p |- ( ph -> A = B ) $=
      wph cA cB wne wn cA cB wceq cA cB wne wph necon4ai.1 con2i cA cB nne
      sylib $.
  $}

  ${
    necon4i.1 $e |- ( A =/= B -> C =/= D ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon4i $p |- ( C = D -> A = B ) $=
      cC cD wceq cA cB wne wn cA cB wceq cA cB wne cC cD necon4i.1 necon2bi cA
      cB nne sylib $.
  $}

  ${
    necon4ad.1 $e |- ( ph -> ( A =/= B -> -. ps ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon4ad $p |- ( ph -> ( ps -> A = B ) ) $=
      wph wps cA cB wne wn cA cB wceq wph cA cB wne wps necon4ad.1 con2d cA cB
      nne syl6ib $.
  $}

  ${
    necon4bd.1 $e |- ( ph -> ( -. ps -> A =/= B ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon4bd $p |- ( ph -> ( A = B -> ps ) ) $=
      cA cB wceq cA cB wne wn wph wps cA cB nne wph wps cA cB wne necon4bd.1
      con1d syl5bir $.
  $}

  ${
    necon4d.1 $e |- ( ph -> ( A =/= B -> C =/= D ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon4d $p |- ( ph -> ( C = D -> A = B ) ) $=
      wph cC cD wceq cA cB wne wn cA cB wceq wph cA cB wne cC cD necon4d.1
      necon2bd cA cB nne syl6ib $.
  $}

  ${
    necon4abid.1 $e |- ( ph -> ( A =/= B <-> -. ps ) ) $.
    $( Contrapositive law deduction for inequality.  (Contributed by NM,
       11-Jan-2008.) $)
    necon4abid $p |- ( ph -> ( A = B <-> ps ) ) $=
      wph cA cB wceq wps cA cB wceq wn cA cB wne wph wps wn cA cB df-ne
      necon4abid.1 syl5bbr con4bid $.
  $}

  ${
    necon4bbid.1 $e |- ( ph -> ( -. ps <-> A =/= B ) ) $.
    $( Contrapositive law deduction for inequality.  (Contributed by NM,
       9-May-2012.) $)
    necon4bbid $p |- ( ph -> ( ps <-> A = B ) ) $=
      wph cA cB wceq wps wph wps cA cB wph wps wn cA cB wne necon4bbid.1 bicomd
      necon4abid bicomd $.
  $}

  ${
    necon4bid.1 $e |- ( ph -> ( A =/= B <-> C =/= D ) ) $.
    $( Contrapositive law deduction for inequality.  (Contributed by NM,
       29-Jun-2007.) $)
    necon4bid $p |- ( ph -> ( A = B <-> C = D ) ) $=
      wph cC cD wceq cA cB wne wn cA cB wceq wph cA cB wne cC cD necon4bid.1
      necon2bbid cA cB nne syl6rbb $.
  $}

  ${
    necon1ad.1 $e |- ( ph -> ( -. ps -> A = B ) ) $.
    $( Contrapositive deduction for inequality.  (Contributed by NM,
       2-Apr-2007.) $)
    necon1ad $p |- ( ph -> ( A =/= B -> ps ) ) $=
      cA cB wne cA cB wceq wn wph wps cA cB df-ne wph wps cA cB wceq necon1ad.1
      con1d syl5bi $.
  $}

  ${
    necon1bd.1 $e |- ( ph -> ( A =/= B -> ps ) ) $.
    $( Contrapositive deduction for inequality.  (Contributed by NM,
       21-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon1bd $p |- ( ph -> ( -. ps -> A = B ) ) $=
      wph wps wn cA cB wne wn cA cB wceq wph cA cB wne wps necon1bd.1 con3d cA
      cB nne syl6ib $.
  $}

  ${
    necon1d.1 $e |- ( ph -> ( A =/= B -> C = D ) ) $.
    $( Contrapositive law deduction for inequality.  (Contributed by NM,
       28-Dec-2008.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    necon1d $p |- ( ph -> ( C =/= D -> A = B ) ) $=
      wph cC cD wne cA cB wph cA cB wne cC cD wceq cC cD wne wn necon1d.1 cC cD
      nne syl6ibr necon4ad $.
  $}

  ${
    neneqad.1 $e |- ( ph -> -. A = B ) $.
    $( If it is not the case that two classes are equal, they are unequal.
       Converse of ~ neneqd .  One-way deduction form of ~ df-ne .
       (Contributed by David Moews, 28-Feb-2017.) $)
    neneqad $p |- ( ph -> A =/= B ) $=
      wph cA cB wph cA cB wceq neneqad.1 con2i necon2ai $.
  $}

  $( Contraposition law for inequality.  (Contributed by NM, 28-Dec-2008.) $)
  nebi $p |- ( ( A = B <-> C = D ) <-> ( A =/= B <-> C =/= D ) ) $=
    cA cB wceq cC cD wceq wb cA cB wne cC cD wne wb cA cB wceq cC cD wceq wb cA
    cB cC cD cA cB wceq cC cD wceq wb id necon3bid cA cB wne cC cD wne wb cA cB
    cC cD cA cB wne cC cD wne wb id necon4bid impbii $.

  $( Theorem *13.18 in [WhiteheadRussell] p. 178.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)
  pm13.18 $p |- ( ( A = B /\ A =/= C ) -> B =/= C ) $=
    cA cB wceq cA cC wne cB cC wne cA cB wceq cB cC cA cC cA cB wceq cA cC wceq
    cB cC wceq cA cB cC eqeq1 biimprd necon3d imp $.

  $( Theorem *13.181 in [WhiteheadRussell] p. 178.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)
  pm13.181 $p |- ( ( A = B /\ B =/= C ) -> A =/= C ) $=
    cA cB wceq cB cA wceq cB cC wne cA cC wne cA cB eqcom cB cA cC pm13.18
    sylanb $.

  ${
    pm2.21ddne.1 $e |- ( ph -> A = B ) $.
    pm2.21ddne.2 $e |- ( ph -> A =/= B ) $.
    $( A contradiction implies anything.  Equality/inequality deduction form.
       (Contributed by David Moews, 28-Feb-2017.) $)
    pm2.21ddne $p |- ( ph -> ps ) $=
      wph cA cB wceq wps pm2.21ddne.1 wph cA cB pm2.21ddne.2 neneqd pm2.21dd $.
  $}

  ${
    pm2.61ne.1 $e |- ( A = B -> ( ps <-> ch ) ) $.
    pm2.61ne.2 $e |- ( ( ph /\ A =/= B ) -> ps ) $.
    pm2.61ne.3 $e |- ( ph -> ch ) $.
    $( Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    pm2.61ne $p |- ( ph -> ps ) $=
      cA cB wne wph wps wi wph cA cB wne wps pm2.61ne.2 expcom cA cB wne wn cA
      cB wceq wph wps wi cA cB nne wph wps cA cB wceq wch pm2.61ne.3 pm2.61ne.1
      syl5ibr sylbi pm2.61i $.
  $}

  ${
    pm2.61ine.1 $e |- ( A = B -> ph ) $.
    pm2.61ine.2 $e |- ( A =/= B -> ph ) $.
    $( Inference eliminating an inequality in an antecedent.  (Contributed by
       NM, 16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    pm2.61ine $p |- ph $=
      cA cB wne wph pm2.61ine.2 cA cB wne wn cA cB wceq wph cA cB nne
      pm2.61ine.1 sylbi pm2.61i $.
  $}

  ${
    pm2.61dne.1 $e |- ( ph -> ( A = B -> ps ) ) $.
    pm2.61dne.2 $e |- ( ph -> ( A =/= B -> ps ) ) $.
    $( Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    pm2.61dne $p |- ( ph -> ps ) $=
      wph cA cB wne wps pm2.61dne.2 cA cB wne wn cA cB wceq wph wps cA cB nne
      pm2.61dne.1 syl5bi pm2.61d $.
  $}

  ${
    pm2.61dane.1 $e |- ( ( ph /\ A = B ) -> ps ) $.
    pm2.61dane.2 $e |- ( ( ph /\ A =/= B ) -> ps ) $.
    $( Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 30-Nov-2011.) $)
    pm2.61dane $p |- ( ph -> ps ) $=
      wph wps cA cB wph cA cB wceq wps pm2.61dane.1 ex wph cA cB wne wps
      pm2.61dane.2 ex pm2.61dne $.
  $}

  ${
    pm2.61da2ne.1 $e |- ( ( ph /\ A = B ) -> ps ) $.
    pm2.61da2ne.2 $e |- ( ( ph /\ C = D ) -> ps ) $.
    pm2.61da2ne.3 $e |- ( ( ph /\ ( A =/= B /\ C =/= D ) ) -> ps ) $.
    $( Deduction eliminating two inequalities in an antecedent.  (Contributed
       by NM, 29-May-2013.) $)
    pm2.61da2ne $p |- ( ph -> ps ) $=
      wph wps cA cB pm2.61da2ne.1 wph cA cB wne wa wps cC cD wph cC cD wceq wps
      cA cB wne pm2.61da2ne.2 adantlr wph cA cB wne cC cD wne wps pm2.61da2ne.3
      anassrs pm2.61dane pm2.61dane $.
  $}

  ${
    pm2.61da3ne.1 $e |- ( ( ph /\ A = B ) -> ps ) $.
    pm2.61da3ne.2 $e |- ( ( ph /\ C = D ) -> ps ) $.
    pm2.61da3ne.3 $e |- ( ( ph /\ E = F ) -> ps ) $.
    pm2.61da3ne.4 $e |- ( ( ph /\ ( A =/= B /\ C =/= D /\ E =/= F ) )
          -> ps ) $.
    $( Deduction eliminating three inequalities in an antecedent.  (Contributed
       by NM, 15-Jun-2013.) $)
    pm2.61da3ne $p |- ( ph -> ps ) $=
      wph wps cA cB cC cD pm2.61da3ne.1 pm2.61da3ne.2 wph cA cB wne cC cD wne
      wa wa wps cE cF wph cE cF wceq wps cA cB wne cC cD wne wa pm2.61da3ne.3
      adantlr wph cA cB wne cC cD wne wa wa cE cF wne wa wph cA cB wne cC cD
      wne cE cF wne wps wph cA cB wne cC cD wne wa cE cF wne simpll wph cA cB
      wne cC cD wne cE cF wne simplrl wph cA cB wne cC cD wne cE cF wne simplrr
      wph cA cB wne cC cD wne wa wa cE cF wne simpr pm2.61da3ne.4 syl13anc
      pm2.61dane pm2.61da2ne $.
  $}

  $( Commutation of inequality.  (Contributed by NM, 14-May-1999.) $)
  necom $p |- ( A =/= B <-> B =/= A ) $=
    cA cB cB cA cA cB eqcom necon3bii $.

  ${
    necomi.1 $e |- A =/= B $.
    $( Inference from commutative law for inequality.  (Contributed by NM,
       17-Oct-2012.) $)
    necomi $p |- B =/= A $=
      cA cB wne cB cA wne necomi.1 cA cB necom mpbi $.
  $}

  ${
    necomd.1 $e |- ( ph -> A =/= B ) $.
    $( Deduction from commutative law for inequality.  (Contributed by NM,
       12-Feb-2008.) $)
    necomd $p |- ( ph -> B =/= A ) $=
      wph cA cB wne cB cA wne necomd.1 cA cB necom sylib $.
  $}

  $( Logical OR with an equality.  (Contributed by NM, 29-Apr-2007.) $)
  neor $p |- ( ( A = B \/ ps ) <-> ( A =/= B -> ps ) ) $=
    cA cB wceq wps wo cA cB wceq wn wps wi cA cB wne wps wi cA cB wceq wps
    df-or cA cB wne cA cB wceq wn wps cA cB df-ne imbi1i bitr4i $.

  $( A De Morgan's law for inequality.  (Contributed by NM, 18-May-2007.) $)
  neanior $p |- ( ( A =/= B /\ C =/= D ) <-> -. ( A = B \/ C = D ) ) $=
    cA cB wne cC cD wne wa cA cB wceq wn cC cD wceq wn wa cA cB wceq cC cD wceq
    wo wn cA cB wne cA cB wceq wn cC cD wne cC cD wceq wn cA cB df-ne cC cD
    df-ne anbi12i cA cB wceq cC cD wceq pm4.56 bitri $.

  $( A De Morgan's law for inequality.  (Contributed by NM, 30-Sep-2013.) $)
  ne3anior $p |- ( ( A =/= B /\ C =/= D /\ E =/= F )
        <-> -. ( A = B \/ C = D \/ E = F ) ) $=
    cA cB wne cC cD wne cE cF wne w3a cA cB wne wn cC cD wne wn cE cF wne wn
    w3o cA cB wceq cC cD wceq cE cF wceq w3o cA cB wne cC cD wne cE cF wne
    3anor cA cB wne wn cA cB wceq cC cD wne wn cC cD wceq cE cF wne wn cE cF
    wceq cA cB nne cC cD nne cE cF nne 3orbi123i xchbinx $.

  $( A De Morgan's law for inequality.  (Contributed by NM, 18-May-2007.) $)
  neorian $p |- ( ( A =/= B \/ C =/= D ) <-> -. ( A = B /\ C = D ) ) $=
    cA cB wne cC cD wne wo cA cB wceq wn cC cD wceq wn wo cA cB wceq cC cD wceq
    wa wn cA cB wne cA cB wceq wn cC cD wne cC cD wceq wn cA cB df-ne cC cD
    df-ne orbi12i cA cB wceq cC cD wceq ianor bitr4i $.

  ${
    nemtbir.1 $e |- A =/= B $.
    nemtbir.2 $e |- ( ph <-> A = B ) $.
    $( An inference from an inequality, related to modus tollens.  (Contributed
       by NM, 13-Apr-2007.) $)
    nemtbir $p |- -. ph $=
      wph cA cB wceq cA cB wne cA cB wceq wn nemtbir.1 cA cB df-ne mpbi
      nemtbir.2 mtbir $.
  $}

  $( Two classes are different if they don't contain the same element.
     (Contributed by NM, 3-Feb-2012.) $)
  nelne1 $p |- ( ( A e. B /\ -. A e. C ) -> B =/= C ) $=
    cA cB wcel cA cC wcel wn cB cC wne cA cB wcel cA cC wcel cB cC cB cC wceq
    cA cB wcel cA cC wcel cB cC cA eleq2 biimpcd necon3bd imp $.

  $( Two classes are different if they don't belong to the same class.
     (Contributed by NM, 25-Jun-2012.) $)
  nelne2 $p |- ( ( A e. C /\ -. B e. C ) -> A =/= B ) $=
    cA cC wcel cB cC wcel wn cA cB wne cA cC wcel cB cC wcel cA cB cA cB wceq
    cA cC wcel cB cC wcel cA cB cC eleq1 biimpcd necon3bd imp $.

  $( Equality theorem for negated membership.  (Contributed by NM,
     20-Nov-1994.) $)
  neleq1 $p |- ( A = B -> ( A e/ C <-> B e/ C ) ) $=
    cA cB wceq cA cC wcel wn cB cC wcel wn cA cC wnel cB cC wnel cA cB wceq cA
    cC wcel cB cC wcel cA cB cC eleq1 notbid cA cC df-nel cB cC df-nel 3bitr4g
    $.

  $( Equality theorem for negated membership.  (Contributed by NM,
     20-Nov-1994.) $)
  neleq2 $p |- ( A = B -> ( C e/ A <-> C e/ B ) ) $=
    cA cB wceq cC cA wcel wn cC cB wcel wn cC cA wnel cC cB wnel cA cB wceq cC
    cA wcel cC cB wcel cA cB cC eleq2 notbid cC cA df-nel cC cB df-nel 3bitr4g
    $.

  ${
    $d y A $.  $d y B $.
    nfne.1 $e |- F/_ x A $.
    nfne.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for inequality.  (Contributed by NM,
       10-Nov-2007.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfne $p |- F/ x A =/= B $=
      cA cB wne cA cB wceq wn vx cA cB df-ne cA cB wceq vx vx cA cB nfne.1
      nfne.2 nfeq nfn nfxfr $.
  $}

  ${
    $d y A $.  $d z B $.
    nfnel.1 $e |- F/_ x A $.
    nfnel.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for inequality.  (Contributed by David
       Abernethy, 26-Jun-2011.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfnel $p |- F/ x A e/ B $=
      cA cB wnel cA cB wcel wn vx cA cB df-nel cA cB wcel vx vx cA cB nfnel.1
      nfnel.2 nfel nfn nfxfr $.
  $}

  ${
    $d y A $.  $d y B $.
    nfned.1 $e |- ( ph -> F/_ x A ) $.
    nfned.2 $e |- ( ph -> F/_ x B ) $.
    $( Bound-variable hypothesis builder for inequality.  (Contributed by NM,
       10-Nov-2007.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfned $p |- ( ph -> F/ x A =/= B ) $=
      cA cB wne cA cB wceq wn wph vx cA cB df-ne wph cA cB wceq vx wph vx cA cB
      nfned.1 nfned.2 nfeqd nfnd nfxfrd $.
  $}

  ${
    $d y A $.  $d z B $.
    nfneld.1 $e |- ( ph -> F/_ x A ) $.
    nfneld.2 $e |- ( ph -> F/_ x B ) $.
    $( Bound-variable hypothesis builder for inequality.  (Contributed by David
       Abernethy, 26-Jun-2011.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfneld $p |- ( ph -> F/ x A e/ B ) $=
      cA cB wnel cA cB wcel wn wph vx cA cB df-nel wph cA cB wcel vx wph vx cA
      cB nfneld.1 nfneld.2 nfeld nfnd nfxfrd $.
  $}



