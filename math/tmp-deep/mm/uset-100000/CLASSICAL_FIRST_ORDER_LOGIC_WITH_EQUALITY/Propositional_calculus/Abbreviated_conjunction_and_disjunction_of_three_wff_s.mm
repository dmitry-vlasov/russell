
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Miscellaneous_theorems_of_propositional_calculus.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Abbreviated conjunction and disjunction of three wff's

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend wff definition to include 3-way disjunction ('or'). $)
  w3o $a wff ( ph \/ ps \/ ch ) $.
  $( Extend wff definition to include 3-way conjunction ('and'). $)
  w3a $a wff ( ph /\ ps /\ ch ) $.

  $( These abbreviations help eliminate parentheses to aid readability. $)

  $( Define disjunction ('or') of three wff's.  Definition *2.33 of
     [WhiteheadRussell] p. 105.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ orass .  (Contributed by NM,
     8-Apr-1994.) $)
  df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.

  $( Define conjunction ('and') of three wff's.  Definition *4.34 of
     [WhiteheadRussell] p. 118.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ anass .  (Contributed by NM,
     8-Apr-1994.) $)
  df-3an $a |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) ) $.

  $( Associative law for triple disjunction.  (Contributed by NM,
     8-Apr-1994.) $)
  3orass $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    wph wps wch w3o wph wps wo wch wo wph wps wch wo wo wph wps wch df-3or wph
    wps wch orass bitri $.

  $( Associative law for triple conjunction.  (Contributed by NM,
     8-Apr-1994.) $)
  3anass $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    wph wps wch w3a wph wps wa wch wa wph wps wch wa wa wph wps wch df-3an wph
    wps wch anass bitri $.

  $( Rotation law for triple conjunction.  (Contributed by NM, 8-Apr-1994.) $)
  3anrot $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ch /\ ph ) ) $=
    wph wps wch wa wa wps wch wa wph wa wph wps wch w3a wps wch wph w3a wph wps
    wch wa ancom wph wps wch 3anass wps wch wph df-3an 3bitr4i $.

  $( Rotation law for triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
  3orrot $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) ) $=
    wph wps wch wo wo wps wch wo wph wo wph wps wch w3o wps wch wph w3o wph wps
    wch wo orcom wph wps wch 3orass wps wch wph df-3or 3bitr4i $.

  $( Commutation law for triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  3ancoma $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ph /\ ch ) ) $=
    wph wps wa wch wa wps wph wa wch wa wph wps wch w3a wps wph wch w3a wph wps
    wa wps wph wa wch wph wps ancom anbi1i wph wps wch df-3an wps wph wch
    df-3an 3bitr4i $.

  $( Commutation law for triple disjunction.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  3orcoma $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ph \/ ch ) ) $=
    wph wps wch wo wo wps wph wch wo wo wph wps wch w3o wps wph wch w3o wph wps
    wch or12 wph wps wch 3orass wps wph wch 3orass 3bitr4i $.

  $( Commutation law for triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  3ancomb $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ch /\ ps ) ) $=
    wph wps wch w3a wps wph wch w3a wph wch wps w3a wph wps wch 3ancoma wps wph
    wch 3anrot bitri $.

  $( Commutation law for triple disjunction.  (Contributed by Scott Fenton,
     20-Apr-2011.) $)
  3orcomb $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) ) $=
    wph wps wch wo wo wph wch wps wo wo wph wps wch w3o wph wch wps w3o wps wch
    wo wch wps wo wph wps wch orcom orbi2i wph wps wch 3orass wph wch wps
    3orass 3bitr4i $.

  $( Reversal law for triple conjunction.  (Contributed by NM, 21-Apr-1994.) $)
  3anrev $p |- ( ( ph /\ ps /\ ch ) <-> ( ch /\ ps /\ ph ) ) $=
    wph wps wch w3a wps wph wch w3a wch wps wph w3a wph wps wch 3ancoma wch wps
    wph 3anrot bitr4i $.

  $( Convert triple conjunction to conjunction, then commute.  (Contributed by
     Jonathan Ben-Naim, 3-Jun-2011.) $)
  3anan32 $p |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $=
    wph wps wch w3a wph wps wa wch wa wph wch wa wps wa wph wps wch df-3an wph
    wps wch an32 bitri $.

  $( Convert triple conjunction to conjunction, then commute.  (Contributed by
     Jonathan Ben-Naim, 3-Jun-2011.)  (Proof shortened by Andrew Salmon,
     14-Jun-2011.) $)
  3anan12 $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ( ph /\ ch ) ) ) $=
    wph wps wch w3a wps wph wch w3a wps wph wch wa wa wph wps wch 3ancoma wps
    wph wch 3anass bitri $.

  $( Triple conjunction expressed in terms of triple disjunction.  (Contributed
     by Jeff Hankins, 15-Aug-2009.) $)
  3anor $p |- ( ( ph /\ ps /\ ch ) <-> -. ( -. ph \/ -. ps \/ -. ch ) ) $=
    wph wps wch w3a wph wps wa wch wa wph wn wps wn wch wn w3o wn wph wps wch
    df-3an wph wps wa wch wa wph wn wps wn wo wch wn wo wph wn wps wn wch wn
    w3o wph wps wa wch wa wph wps wa wn wch wn wo wph wn wps wn wo wch wn wo
    wph wps wa wch anor wph wps wa wn wph wn wps wn wo wch wn wph wps ianor
    orbi1i xchbinx wph wn wps wn wch wn df-3or xchbinxr bitri $.

  $( Negated triple conjunction expressed in terms of triple disjunction.
     (Contributed by Jeff Hankins, 15-Aug-2009.)  (Proof shortened by Andrew
     Salmon, 13-May-2011.) $)
  3ianor $p |- ( -. ( ph /\ ps /\ ch ) <-> ( -. ph \/ -. ps \/ -. ch ) ) $=
    wph wn wps wn wch wn w3o wph wps wch w3a wn wph wps wch w3a wph wn wps wn
    wch wn w3o wph wps wch 3anor con2bii bicomi $.

  $( Negated triple disjunction as triple conjunction.  (Contributed by Scott
     Fenton, 19-Apr-2011.) $)
  3ioran $p |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) ) $=
    wph wps wo wn wch wn wa wph wn wps wn wa wch wn wa wph wps wch w3o wn wph
    wn wps wn wch wn w3a wph wps wo wn wph wn wps wn wa wch wn wph wps ioran
    anbi1i wph wps wo wch wo wph wps wo wn wch wn wa wph wps wch w3o wph wps wo
    wch ioran wph wps wch df-3or xchnxbir wph wn wps wn wch wn df-3an 3bitr4i
    $.

  $( Triple disjunction in terms of triple conjunction.  (Contributed by NM,
     8-Oct-2012.) $)
  3oran $p |- ( ( ph \/ ps \/ ch ) <-> -. ( -. ph /\ -. ps /\ -. ch ) ) $=
    wph wn wps wn wch wn w3a wn wph wps wch w3o wph wps wch w3o wph wn wps wn
    wch wn w3a wph wps wch 3ioran con1bii bicomi $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  3simpa $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ps ) ) $=
    wph wps wch w3a wph wps wa wch wph wps wch df-3an simplbi $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  3simpb $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ch ) ) $=
    wph wps wch w3a wph wch wps w3a wph wch wa wph wps wch 3ancomb wph wch wps
    3simpa sylbi $.

  $( Simplification of triple conjunction.  (Contributed by NM, 21-Apr-1994.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  3simpc $p |- ( ( ph /\ ps /\ ch ) -> ( ps /\ ch ) ) $=
    wph wps wch w3a wps wch wph w3a wps wch wa wph wps wch 3anrot wps wch wph
    3simpa sylbi $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  simp1 $p |- ( ( ph /\ ps /\ ch ) -> ph ) $=
    wph wps wch w3a wph wps wph wps wch 3simpa simpld $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  simp2 $p |- ( ( ph /\ ps /\ ch ) -> ps ) $=
    wph wps wch w3a wph wps wph wps wch 3simpa simprd $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  simp3 $p |- ( ( ph /\ ps /\ ch ) -> ch ) $=
    wph wps wch w3a wps wch wph wps wch 3simpc simprd $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ph ) $=
    wph wps wch w3a wph wth wph wps wch simp1 adantr $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl2 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ps ) $=
    wph wps wch w3a wps wth wph wps wch simp2 adantr $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl3 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ch ) $=
    wph wps wch w3a wch wth wph wps wch simp3 adantr $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr1 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ps ) $=
    wps wch wth w3a wps wph wps wch wth simp1 adantl $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ch ) $=
    wps wch wth w3a wch wph wps wch wth simp2 adantl $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr3 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> th ) $=
    wps wch wth w3a wth wph wps wch wth simp3 adantl $.

  ${
    3simp1i.1 $e |- ( ph /\ ps /\ ch ) $.
    $( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
    simp1i $p |- ph $=
      wph wps wch w3a wph 3simp1i.1 wph wps wch simp1 ax-mp $.

    $( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
    simp2i $p |- ps $=
      wph wps wch w3a wps 3simp1i.1 wph wps wch simp2 ax-mp $.

    $( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
    simp3i $p |- ch $=
      wph wps wch w3a wch 3simp1i.1 wph wps wch simp3 ax-mp $.
  $}

  ${
    3simp1d.1 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
    simp1d $p |- ( ph -> ps ) $=
      wph wps wch wth w3a wps 3simp1d.1 wps wch wth simp1 syl $.

    $( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
    simp2d $p |- ( ph -> ch ) $=
      wph wps wch wth w3a wch 3simp1d.1 wps wch wth simp2 syl $.

    $( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
    simp3d $p |- ( ph -> th ) $=
      wph wps wch wth w3a wth 3simp1d.1 wps wch wth simp3 syl $.
  $}

  ${
    3simp1bi.1 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp1bi $p |- ( ph -> ps ) $=
      wph wps wch wth wph wps wch wth w3a 3simp1bi.1 biimpi simp1d $.

    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp2bi $p |- ( ph -> ch ) $=
      wph wps wch wth wph wps wch wth w3a 3simp1bi.1 biimpi simp2d $.

    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp3bi $p |- ( ph -> th ) $=
      wph wps wch wth wph wps wch wth w3a 3simp1bi.1 biimpi simp3d $.
  $}

  ${
    3adant.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
    3adant1 $p |- ( ( th /\ ph /\ ps ) -> ch ) $=
      wth wph wps w3a wph wps wa wch wth wph wps 3simpc 3adant.1 syl $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
    3adant2 $p |- ( ( ph /\ th /\ ps ) -> ch ) $=
      wph wth wps w3a wph wps wa wch wph wth wps 3simpb 3adant.1 syl $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
    3adant3 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      wph wps wth w3a wph wps wa wch wph wps wth 3simpa 3adant.1 syl $.
  $}

  ${
    3ad2ant.1 $e |- ( ph -> ch ) $.
    $( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
    3ad2ant1 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      wph wth wch wps wph wch wth 3ad2ant.1 adantr 3adant2 $.

    $( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
    3ad2ant2 $p |- ( ( ps /\ ph /\ th ) -> ch ) $=
      wph wth wch wps wph wch wth 3ad2ant.1 adantr 3adant1 $.

    $( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
    3ad2ant3 $p |- ( ( ps /\ th /\ ph ) -> ch ) $=
      wth wph wch wps wph wch wth 3ad2ant.1 adantl 3adant1 $.
  $}

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp1l $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ph ) $=
    wph wps wa wch wph wth wph wps simpl 3ad2ant1 $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp1r $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ps ) $=
    wph wps wa wch wps wth wph wps simpr 3ad2ant1 $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp2l $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ps ) $=
    wps wch wa wph wps wth wps wch simpl 3ad2ant2 $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp2r $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ch ) $=
    wps wch wa wph wch wth wps wch simpr 3ad2ant2 $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp3l $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> ch ) $=
    wch wth wa wph wch wps wch wth simpl 3ad2ant3 $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp3r $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> th ) $=
    wch wth wa wph wth wps wch wth simpr 3ad2ant3 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp11 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ph ) $=
    wph wps wch w3a wth wph wta wph wps wch simp1 3ad2ant1 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp12 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ps ) $=
    wph wps wch w3a wth wps wta wph wps wch simp2 3ad2ant1 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp13 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ch ) $=
    wph wps wch w3a wth wch wta wph wps wch simp3 3ad2ant1 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp21 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ps ) $=
    wps wch wth w3a wph wps wta wps wch wth simp1 3ad2ant2 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp22 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ch ) $=
    wps wch wth w3a wph wch wta wps wch wth simp2 3ad2ant2 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp23 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> th ) $=
    wps wch wth w3a wph wth wta wps wch wth simp3 3ad2ant2 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp31 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ch ) $=
    wch wth wta w3a wph wch wps wch wth wta simp1 3ad2ant3 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp32 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> th ) $=
    wch wth wta w3a wph wth wps wch wth wta simp2 3ad2ant3 $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp33 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ta ) $=
    wch wth wta w3a wph wta wps wch wth wta simp3 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpll1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ph ) $=
    wph wps wch w3a wth wa wph wta wph wps wch wth simpl1 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpll2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ps ) $=
    wph wps wch w3a wth wa wps wta wph wps wch wth simpl2 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpll3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ch ) $=
    wph wps wch w3a wth wa wch wta wph wps wch wth simpl3 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simplr1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ph ) $=
    wth wph wps wch w3a wa wph wta wth wph wps wch simpr1 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simplr2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ps ) $=
    wth wph wps wch w3a wa wps wta wth wph wps wch simpr2 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simplr3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ch ) $=
    wth wph wps wch w3a wa wch wta wth wph wps wch simpr3 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprl1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $=
    wph wps wch w3a wth wa wph wta wph wps wch wth simpl1 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprl2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $=
    wph wps wch w3a wth wa wps wta wph wps wch wth simpl2 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprl3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $=
    wph wps wch w3a wth wa wch wta wph wps wch wth simpl3 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprr1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    wth wph wps wch w3a wa wph wta wth wph wps wch simpr1 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprr2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    wth wph wps wch w3a wa wps wta wth wph wps wch simpr2 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprr3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    wth wph wps wch w3a wa wch wta wth wph wps wch simpr3 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl1l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ph ) $=
    wph wps wa wch wth w3a wph wta wph wps wch wth simp1l adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl1r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ps ) $=
    wph wps wa wch wth w3a wps wta wph wps wch wth simp1r adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl2l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ph ) $=
    wch wph wps wa wth w3a wph wta wch wph wps wth simp2l adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl2r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ps ) $=
    wch wph wps wa wth w3a wps wta wch wph wps wth simp2r adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl3l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $=
    wch wth wph wps wa w3a wph wta wch wth wph wps simp3l adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl3r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $=
    wch wth wph wps wa w3a wps wta wch wth wph wps simp3r adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr1l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $=
    wph wps wa wch wth w3a wph wta wph wps wch wth simp1l adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr1r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $=
    wph wps wa wch wth w3a wps wta wph wps wch wth simp1r adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr2l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $=
    wch wph wps wa wth w3a wph wta wch wph wps wth simp2l adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr2r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $=
    wch wph wps wa wth w3a wps wta wch wph wps wth simp2r adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr3l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $=
    wch wth wph wps wa w3a wph wta wch wth wph wps simp3l adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr3r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $=
    wch wth wph wps wa w3a wps wta wch wth wph wps simp3r adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1ll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ph ) $=
    wph wps wa wch wa wth wph wta wph wps wch simpll 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1lr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ps ) $=
    wph wps wa wch wa wth wps wta wph wps wch simplr 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1rl $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ph ) $=
    wch wph wps wa wa wth wph wta wch wph wps simprl 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1rr $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ps ) $=
    wch wph wps wa wa wth wps wta wch wph wps simprr 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2ll $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ph ) $=
    wph wps wa wch wa wth wph wta wph wps wch simpll 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2lr $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ps ) $=
    wph wps wa wch wa wth wps wta wph wps wch simplr 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2rl $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $=
    wch wph wps wa wa wth wph wta wch wph wps simprl 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2rr $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $=
    wch wph wps wa wa wth wps wta wch wph wps simprr 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3ll $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ph ) $=
    wph wps wa wch wa wth wph wta wph wps wch simpll 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3lr $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ps ) $=
    wph wps wa wch wa wth wps wta wph wps wch simplr 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3rl $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ph ) $=
    wch wph wps wa wa wth wph wta wch wph wps simprl 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3rr $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ps ) $=
    wch wph wps wa wa wth wps wta wch wph wps simprr 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl11 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ph ) $=
    wph wps wch w3a wth wta w3a wph wet wph wps wch wth wta simp11 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl12 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ps ) $=
    wph wps wch w3a wth wta w3a wps wet wph wps wch wth wta simp12 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl13 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ch ) $=
    wph wps wch w3a wth wta w3a wch wet wph wps wch wth wta simp13 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl21 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ph ) $=
    wth wph wps wch w3a wta w3a wph wet wth wph wps wch wta simp21 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl22 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ps ) $=
    wth wph wps wch w3a wta w3a wps wet wth wph wps wch wta simp22 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl23 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ch ) $=
    wth wph wps wch w3a wta w3a wch wet wth wph wps wch wta simp23 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl31 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $=
    wth wta wph wps wch w3a w3a wph wet wth wta wph wps wch simp31 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl32 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $=
    wth wta wph wps wch w3a w3a wps wet wth wta wph wps wch simp32 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl33 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $=
    wth wta wph wps wch w3a w3a wch wet wth wta wph wps wch simp33 adantr $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr11 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $=
    wph wps wch w3a wth wta w3a wph wet wph wps wch wth wta simp11 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr12 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $=
    wph wps wch w3a wth wta w3a wps wet wph wps wch wth wta simp12 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr13 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $=
    wph wps wch w3a wth wta w3a wch wet wph wps wch wth wta simp13 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr21 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $=
    wth wph wps wch w3a wta w3a wph wet wth wph wps wch wta simp21 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr22 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $=
    wth wph wps wch w3a wta w3a wps wet wth wph wps wch wta simp22 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr23 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $=
    wth wph wps wch w3a wta w3a wch wet wth wph wps wch wta simp23 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr31 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    wth wta wph wps wch w3a w3a wph wet wth wta wph wps wch simp31 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr32 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    wth wta wph wps wch w3a w3a wps wet wth wta wph wps wch simp32 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr33 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    wth wta wph wps wch w3a w3a wch wet wth wta wph wps wch simp33 adantl $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1l1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ph ) $=
    wph wps wch w3a wth wa wta wph wet wph wps wch wth simpl1 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1l2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ps ) $=
    wph wps wch w3a wth wa wta wps wet wph wps wch wth simpl2 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1l3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ch ) $=
    wph wps wch w3a wth wa wta wch wet wph wps wch wth simpl3 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1r1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ph ) $=
    wth wph wps wch w3a wa wta wph wet wth wph wps wch simpr1 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1r2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ps ) $=
    wth wph wps wch w3a wa wta wps wet wth wph wps wch simpr2 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1r3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ch ) $=
    wth wph wps wch w3a wa wta wch wet wth wph wps wch simpr3 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2l1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ph ) $=
    wph wps wch w3a wth wa wta wph wet wph wps wch wth simpl1 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2l2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ps ) $=
    wph wps wch w3a wth wa wta wps wet wph wps wch wth simpl2 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2l3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ch ) $=
    wph wps wch w3a wth wa wta wch wet wph wps wch wth simpl3 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2r1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $=
    wth wph wps wch w3a wa wta wph wet wth wph wps wch simpr1 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2r2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $=
    wth wph wps wch w3a wa wta wps wet wth wph wps wch simpr2 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2r3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $=
    wth wph wps wch w3a wa wta wch wet wth wph wps wch simpr3 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3l1 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $=
    wph wps wch w3a wth wa wta wph wet wph wps wch wth simpl1 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3l2 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $=
    wph wps wch w3a wth wa wta wps wet wph wps wch wth simpl2 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3l3 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $=
    wph wps wch w3a wth wa wta wch wet wph wps wch wth simpl3 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3r1 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    wth wph wps wch w3a wa wta wph wet wth wph wps wch simpr1 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3r2 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    wth wph wps wch w3a wa wta wps wet wth wph wps wch simpr2 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3r3 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    wth wph wps wch w3a wa wta wch wet wth wph wps wch simpr3 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp11l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ph ) $=
    wph wps wa wch wth w3a wta wph wet wph wps wch wth simp1l 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp11r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ps ) $=
    wph wps wa wch wth w3a wta wps wet wph wps wch wth simp1r 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp12l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ph ) $=
    wch wph wps wa wth w3a wta wph wet wch wph wps wth simp2l 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp12r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ps ) $=
    wch wph wps wa wth w3a wta wps wet wch wph wps wth simp2r 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp13l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ph ) $=
    wch wth wph wps wa w3a wta wph wet wch wth wph wps simp3l 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp13r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ps ) $=
    wch wth wph wps wa w3a wta wps wet wch wth wph wps simp3r 3ad2ant1 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp21l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ph ) $=
    wph wps wa wch wth w3a wta wph wet wph wps wch wth simp1l 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp21r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ps ) $=
    wph wps wa wch wth w3a wta wps wet wph wps wch wth simp1r 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp22l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ph ) $=
    wch wph wps wa wth w3a wta wph wet wch wph wps wth simp2l 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp22r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ps ) $=
    wch wph wps wa wth w3a wta wps wet wch wph wps wth simp2r 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp23l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ph ) $=
    wch wth wph wps wa w3a wta wph wet wch wth wph wps simp3l 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp23r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ps ) $=
    wch wth wph wps wa w3a wta wps wet wch wth wph wps simp3r 3ad2ant2 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp31l $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $=
    wph wps wa wch wth w3a wta wph wet wph wps wch wth simp1l 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp31r $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $=
    wph wps wa wch wth w3a wta wps wet wph wps wch wth simp1r 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp32l $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $=
    wch wph wps wa wth w3a wta wph wet wch wph wps wth simp2l 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp32r $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $=
    wch wph wps wa wth w3a wta wps wet wch wph wps wth simp2r 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp33l $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $=
    wch wth wph wps wa w3a wta wph wet wch wth wph wps simp3l 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp33r $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $=
    wch wth wph wps wa w3a wta wps wet wch wth wph wps simp3r 3ad2ant3 $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp111 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ph ) $=
    wph wps wch w3a wth wta w3a wet wph wze wph wps wch wth wta simp11 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp112 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ps ) $=
    wph wps wch w3a wth wta w3a wet wps wze wph wps wch wth wta simp12 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp113 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ch ) $=
    wph wps wch w3a wth wta w3a wet wch wze wph wps wch wth wta simp13 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp121 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ph ) $=
    wth wph wps wch w3a wta w3a wet wph wze wth wph wps wch wta simp21 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp122 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ps ) $=
    wth wph wps wch w3a wta w3a wet wps wze wth wph wps wch wta simp22 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp123 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ch ) $=
    wth wph wps wch w3a wta w3a wet wch wze wth wph wps wch wta simp23 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp131 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ph ) $=
    wth wta wph wps wch w3a w3a wet wph wze wth wta wph wps wch simp31 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp132 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ps ) $=
    wth wta wph wps wch w3a w3a wet wps wze wth wta wph wps wch simp32 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp133 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ch ) $=
    wth wta wph wps wch w3a w3a wet wch wze wth wta wph wps wch simp33 3ad2ant1
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp211 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ph ) $=
    wph wps wch w3a wth wta w3a wet wph wze wph wps wch wth wta simp11 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp212 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ps ) $=
    wph wps wch w3a wth wta w3a wet wps wze wph wps wch wth wta simp12 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp213 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ch ) $=
    wph wps wch w3a wth wta w3a wet wch wze wph wps wch wth wta simp13 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp221 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ph ) $=
    wth wph wps wch w3a wta w3a wet wph wze wth wph wps wch wta simp21 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp222 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ps ) $=
    wth wph wps wch w3a wta w3a wet wps wze wth wph wps wch wta simp22 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp223 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ch ) $=
    wth wph wps wch w3a wta w3a wet wch wze wth wph wps wch wta simp23 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp231 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ph ) $=
    wth wta wph wps wch w3a w3a wet wph wze wth wta wph wps wch simp31 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp232 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ps ) $=
    wth wta wph wps wch w3a w3a wet wps wze wth wta wph wps wch simp32 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp233 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ch ) $=
    wth wta wph wps wch w3a w3a wet wch wze wth wta wph wps wch simp33 3ad2ant2
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp311 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $=
    wph wps wch w3a wth wta w3a wet wph wze wph wps wch wth wta simp11 3ad2ant3
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp312 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $=
    wph wps wch w3a wth wta w3a wet wps wze wph wps wch wth wta simp12 3ad2ant3
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp313 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $=
    wph wps wch w3a wth wta w3a wet wch wze wph wps wch wth wta simp13 3ad2ant3
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp321 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $=
    wth wph wps wch w3a wta w3a wet wph wze wth wph wps wch wta simp21 3ad2ant3
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp322 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $=
    wth wph wps wch w3a wta w3a wet wps wze wth wph wps wch wta simp22 3ad2ant3
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp323 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $=
    wth wph wps wch w3a wta w3a wet wch wze wth wph wps wch wta simp23 3ad2ant3
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp331 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    wth wta wph wps wch w3a w3a wet wph wze wth wta wph wps wch simp31 3ad2ant3
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp332 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    wth wta wph wps wch w3a w3a wet wps wze wth wta wph wps wch simp32 3ad2ant3
    $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp333 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    wth wta wph wps wch w3a w3a wet wch wze wth wta wph wps wch simp33 3ad2ant3
    $.

  ${
    3adantl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
    3adantl1 $p |- ( ( ( ta /\ ph /\ ps ) /\ ch ) -> th ) $=
      wta wph wps w3a wph wps wa wch wth wta wph wps 3simpc 3adantl.1 sylan $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
    3adantl2 $p |- ( ( ( ph /\ ta /\ ps ) /\ ch ) -> th ) $=
      wph wta wps w3a wph wps wa wch wth wph wta wps 3simpb 3adantl.1 sylan $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
    3adantl3 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      wph wps wta w3a wph wps wa wch wth wph wps wta 3simpa 3adantl.1 sylan $.
  $}

  ${
    3adantr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
    3adantr1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      wta wps wch w3a wph wps wch wa wth wta wps wch 3simpc 3adantr.1 sylan2 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
    3adantr2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      wps wta wch w3a wph wps wch wa wth wps wta wch 3simpb 3adantr.1 sylan2 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
    3adantr3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      wps wch wta w3a wph wps wch wa wth wps wch wta 3simpa 3adantr.1 sylan2 $.
  $}

  ${
    3ad2antl.1 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
    3ad2antl1 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      wph wta wch wth wps wph wch wth wta 3ad2antl.1 adantlr 3adantl2 $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
    3ad2antl2 $p |- ( ( ( ps /\ ph /\ ta ) /\ ch ) -> th ) $=
      wph wta wch wth wps wph wch wth wta 3ad2antl.1 adantlr 3adantl1 $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
    3ad2antl3 $p |- ( ( ( ps /\ ta /\ ph ) /\ ch ) -> th ) $=
      wta wph wch wth wps wph wch wth wta 3ad2antl.1 adantll 3adantl1 $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       25-Dec-2007.) $)
    3ad2antr1 $p |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th ) $=
      wph wch wps wth wta wph wch wth wps 3ad2antl.1 adantrr 3adantr3 $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       27-Dec-2007.) $)
    3ad2antr2 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      wph wps wch wth wta wph wch wth wps 3ad2antl.1 adantrl 3adantr3 $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       30-Dec-2007.) $)
    3ad2antr3 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      wph wta wch wth wps wph wch wth wta 3ad2antl.1 adantrl 3adantr1 $.
  $}

  ${
    3anibar.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ( ch /\ ta ) ) ) $.
    $( Remove a hypothesis from the second member of a biimplication.
       (Contributed by FL, 22-Jul-2008.) $)
    3anibar $p |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $=
      wph wps wch w3a wth wch wta wa wta 3anibar.1 wph wps wch w3a wch wta wph
      wps wch simp3 biantrurd bitr4d $.
  $}

  $( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
  3mix1 $p |- ( ph -> ( ph \/ ps \/ ch ) ) $=
    wph wph wps wch wo wo wph wps wch w3o wph wps wch wo orc wph wps wch 3orass
    sylibr $.

  $( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
  3mix2 $p |- ( ph -> ( ps \/ ph \/ ch ) ) $=
    wph wph wch wps w3o wps wph wch w3o wph wch wps 3mix1 wps wph wch 3orrot
    sylibr $.

  $( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
  3mix3 $p |- ( ph -> ( ps \/ ch \/ ph ) ) $=
    wph wph wps wch w3o wps wch wph w3o wph wps wch 3mix1 wph wps wch 3orrot
    sylib $.

  ${
    3mixi.1 $e |- ph $.
    $( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
    3mix1i $p |- ( ph \/ ps \/ ch ) $=
      wph wph wps wch w3o 3mixi.1 wph wps wch 3mix1 ax-mp $.

    $( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
    3mix2i $p |- ( ps \/ ph \/ ch ) $=
      wph wps wph wch w3o 3mixi.1 wph wps wch 3mix2 ax-mp $.

    $( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
    3mix3i $p |- ( ps \/ ch \/ ph ) $=
      wph wps wch wph w3o 3mixi.1 wph wps wch 3mix3 ax-mp $.
  $}

  ${
    3pm3.2i.1 $e |- ph $.
    3pm3.2i.2 $e |- ps $.
    3pm3.2i.3 $e |- ch $.
    $( Infer conjunction of premises.  (Contributed by NM, 10-Feb-1995.) $)
    3pm3.2i $p |- ( ph /\ ps /\ ch ) $=
      wph wps wch w3a wph wps wa wch wph wps 3pm3.2i.1 3pm3.2i.2 pm3.2i
      3pm3.2i.3 wph wps wch df-3an mpbir2an $.
  $}

  ${
    $( ~ pm3.2 for a triple conjunction.  (Contributed by Alan Sare,
       24-Oct-2011.) $)
    pm3.2an3 $p |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) ) $=
      wph wps wch wph wps wa wch wa wph wps wch w3a wph wps wch wph wps wa wch
      wa wi wph wps wa wch pm3.2 ex wph wps wch w3a wph wps wa wch wa wph wps
      wch df-3an bicomi syl8ib $.
  $}

  ${
    3jca.1 $e |- ( ph -> ps ) $.
    3jca.2 $e |- ( ph -> ch ) $.
    3jca.3 $e |- ( ph -> th ) $.
    $( Join consequents with conjunction.  (Contributed by NM, 9-Apr-1994.) $)
    3jca $p |- ( ph -> ( ps /\ ch /\ th ) ) $=
      wph wps wch wa wth wa wps wch wth w3a wph wps wch wth 3jca.1 3jca.2
      3jca.3 jca31 wps wch wth df-3an sylibr $.
  $}

  ${
    3jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    3jcad.3 $e |- ( ph -> ( ps -> ta ) ) $.
    $( Deduction conjoining the consequents of three implications.
       (Contributed by NM, 25-Sep-2005.) $)
    3jcad $p |- ( ph -> ( ps -> ( ch /\ th /\ ta ) ) ) $=
      wph wps wch wth wta w3a wph wps wa wch wth wta wph wps wch 3jcad.1 imp
      wph wps wth 3jcad.2 imp wph wps wta 3jcad.3 imp 3jca ex $.
  $}

  ${
    mpbir3an.1 $e |- ps $.
    mpbir3an.2 $e |- ch $.
    mpbir3an.3 $e |- th $.
    mpbir3an.4 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       16-Sep-2011.) $)
    mpbir3an $p |- ph $=
      wph wps wch wth w3a wps wch wth mpbir3an.1 mpbir3an.2 mpbir3an.3 3pm3.2i
      mpbir3an.4 mpbir $.
  $}

  ${
    mpbir3and.1 $e |- ( ph -> ch ) $.
    mpbir3and.2 $e |- ( ph -> th ) $.
    mpbir3and.3 $e |- ( ph -> ta ) $.
    mpbir3and.4 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by
       Mario Carneiro, 11-May-2014.)  (Revised by Mario Carneiro,
       9-Jan-2015.) $)
    mpbir3and $p |- ( ph -> ps ) $=
      wph wps wch wth wta w3a wph wch wth wta mpbir3and.1 mpbir3and.2
      mpbir3and.3 3jca mpbir3and.4 mpbird $.
  $}

  ${
    syl3anbrc.1 $e |- ( ph -> ps ) $.
    syl3anbrc.2 $e |- ( ph -> ch ) $.
    syl3anbrc.3 $e |- ( ph -> th ) $.
    syl3anbrc.4 $e |- ( ta <-> ( ps /\ ch /\ th ) ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 11-May-2014.) $)
    syl3anbrc $p |- ( ph -> ta ) $=
      wph wps wch wth w3a wta wph wps wch wth syl3anbrc.1 syl3anbrc.2
      syl3anbrc.3 3jca syl3anbrc.4 sylibr $.
  $}

  ${
    3anim123i.1 $e |- ( ph -> ps ) $.
    3anim123i.2 $e |- ( ch -> th ) $.
    3anim123i.3 $e |- ( ta -> et ) $.
    $( Join antecedents and consequents with conjunction.  (Contributed by NM,
       8-Apr-1994.) $)
    3anim123i $p |- ( ( ph /\ ch /\ ta ) -> ( ps /\ th /\ et ) ) $=
      wph wch wta w3a wps wth wet wph wch wps wta 3anim123i.1 3ad2ant1 wch wph
      wth wta 3anim123i.2 3ad2ant2 wta wph wet wch 3anim123i.3 3ad2ant3 3jca $.
  $}

  ${
    3animi.1 $e |- ( ph -> ps ) $.
    $( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 16-Aug-2009.) $)
    3anim1i $p |- ( ( ph /\ ch /\ th ) -> ( ps /\ ch /\ th ) ) $=
      wph wps wch wch wth wth 3animi.1 wch id wth id 3anim123i $.

    $( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 19-Aug-2009.) $)
    3anim3i $p |- ( ( ch /\ th /\ ph ) -> ( ch /\ th /\ ps ) ) $=
      wch wch wth wth wph wps wch id wth id 3animi.1 3anim123i $.
  $}

  ${
    bi3.1 $e |- ( ph <-> ps ) $.
    bi3.2 $e |- ( ch <-> th ) $.
    bi3.3 $e |- ( ta <-> et ) $.
    $( Join 3 biconditionals with conjunction.  (Contributed by NM,
       21-Apr-1994.) $)
    3anbi123i $p |- ( ( ph /\ ch /\ ta ) <-> ( ps /\ th /\ et ) ) $=
      wph wch wa wta wa wps wth wa wet wa wph wch wta w3a wps wth wet w3a wph
      wch wa wps wth wa wta wet wph wps wch wth bi3.1 bi3.2 anbi12i bi3.3
      anbi12i wph wch wta df-3an wps wth wet df-3an 3bitr4i $.

    $( Join 3 biconditionals with disjunction.  (Contributed by NM,
       17-May-1994.) $)
    3orbi123i $p |- ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) $=
      wph wch wo wta wo wps wth wo wet wo wph wch wta w3o wps wth wet w3o wph
      wch wo wps wth wo wta wet wph wps wch wth bi3.1 bi3.2 orbi12i bi3.3
      orbi12i wph wch wta df-3or wps wth wet df-3or 3bitr4i $.
  $}

  ${
    3anbi1i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi1i $p |- ( ( ph /\ ch /\ th ) <-> ( ps /\ ch /\ th ) ) $=
      wph wps wch wch wth wth 3anbi1i.1 wch biid wth biid 3anbi123i $.

    $( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi2i $p |- ( ( ch /\ ph /\ th ) <-> ( ch /\ ps /\ th ) ) $=
      wch wch wph wps wth wth wch biid 3anbi1i.1 wth biid 3anbi123i $.

    $( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi3i $p |- ( ( ch /\ th /\ ph ) <-> ( ch /\ th /\ ps ) ) $=
      wch wch wth wth wph wps wch biid wth biid 3anbi1i.1 3anbi123i $.
  $}

  ${
    3imp.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation inference.  (Contributed by NM, 8-Apr-1994.) $)
    3imp $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      wph wps wch w3a wph wps wa wch wa wth wph wps wch df-3an wph wps wch wth
      3imp.1 imp31 sylbi $.
  $}

  ${
    3impa.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Importation from double to triple conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
    3impa $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth 3impa.1 exp31 3imp $.
  $}

  ${
    3impb.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Importation from double to triple conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
    3impb $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth 3impb.1 exp32 3imp $.
  $}

  ${
    3impia.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Importation to triple conjunction.  (Contributed by NM, 13-Jun-2006.) $)
    3impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth wi 3impia.1 ex 3imp $.
  $}

  ${
    3impib.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Importation to triple conjunction.  (Contributed by NM, 13-Jun-2006.) $)
    3impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth 3impib.1 exp3a 3imp $.
  $}

  ${
    3exp.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Exportation inference.  (Contributed by NM, 30-May-1994.) $)
    3exp $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wph wps wch wph wps wch w3a wth wph wps wch pm3.2an3 3exp.1 syl8 $.

    $( Exportation from triple to double conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
    3expa $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth 3exp.1 3exp imp31 $.

    $( Exportation from triple to double conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
    3expb $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      wph wps wch wth wph wps wch wth 3exp.1 3exp imp32 $.

    $( Exportation from triple conjunction.  (Contributed by NM,
       19-May-2007.) $)
    3expia $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      wph wps wch wth wi wph wps wch wth 3exp.1 3exp imp $.

    $( Exportation from triple conjunction.  (Contributed by NM,
       19-May-2007.) $)
    3expib $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      wph wps wch wth wph wps wch wth 3exp.1 3exp imp3a $.

    $( Commutation in antecedent.  Swap 1st and 3rd.  (Contributed by NM,
       28-Jan-1996.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    3com12 $p |- ( ( ps /\ ph /\ ch ) -> th ) $=
      wps wph wch w3a wph wps wch w3a wth wps wph wch 3ancoma 3exp.1 sylbi $.

    $( Commutation in antecedent.  Swap 1st and 3rd.  (Contributed by NM,
       28-Jan-1996.) $)
    3com13 $p |- ( ( ch /\ ps /\ ph ) -> th ) $=
      wch wps wph w3a wph wps wch w3a wth wch wps wph 3anrev 3exp.1 sylbi $.

    $( Commutation in antecedent.  Swap 2nd and 3rd.  (Contributed by NM,
       28-Jan-1996.) $)
    3com23 $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      wph wch wps wth wph wps wch wth wph wps wch wth 3exp.1 3exp com23 3imp $.

    $( Commutation in antecedent.  Rotate left.  (Contributed by NM,
       28-Jan-1996.) $)
    3coml $p |- ( ( ps /\ ch /\ ph ) -> th ) $=
      wph wch wps wth wph wps wch wth 3exp.1 3com23 3com13 $.

    $( Commutation in antecedent.  Rotate right.  (Contributed by NM,
       28-Jan-1996.) $)
    3comr $p |- ( ( ch /\ ph /\ ps ) -> th ) $=
      wps wch wph wth wph wps wch wth 3exp.1 3coml 3coml $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Feb-2008.) $)
    3adant3r1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      wph wps wch wth wta wph wps wch wth 3exp.1 3expb 3adantr1 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       17-Feb-2008.) $)
    3adant3r2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      wph wps wch wth wta wph wps wch wth 3exp.1 3expb 3adantr2 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       18-Feb-2008.) $)
    3adant3r3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      wph wps wch wth wta wph wps wch wth 3exp.1 3expb 3adantr3 $.
  $}

  ${
    3an1rs.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Swap conjuncts.  (Contributed by NM, 16-Dec-2007.) $)
    3an1rs $p |- ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta ) $=
      wph wps wth w3a wch wta wph wps wth wch wta wi wph wps wch wth wta wph
      wps wch wth wta wi wph wps wch w3a wth wta 3an1rs.1 ex 3exp com34 3imp
      imp $.
  $}

  ${
    3imp1.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Importation to left triple conjunction.  (Contributed by NM,
       24-Feb-2005.) $)
    3imp1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      wph wps wch w3a wth wta wph wps wch wth wta wi 3imp1.1 3imp imp $.

    $( Importation deduction for triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
    3impd $p |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $=
      wps wch wth w3a wph wta wps wch wth wph wta wi wph wps wch wth wta
      3imp1.1 com4l 3imp com12 $.

    $( Importation to right triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
    3imp2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      wph wps wch wth w3a wta wph wps wch wth wta 3imp1.1 3impd imp $.
  $}

  ${
    3exp1.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Exportation from left triple conjunction.  (Contributed by NM,
       24-Feb-2005.) $)
    3exp1 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wch w3a wth wta 3exp1.1 ex 3exp $.
  $}

  ${
    3expd.1 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( Exportation deduction for triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
    3expd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wps wch wth wph wta wps wch wth wph wta wi wph wps wch wth w3a wta
      3expd.1 com12 3exp com4r $.
  $}

  ${
    3exp2.1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( Exportation from right triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
    3exp2 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wch wth w3a wta 3exp2.1 ex 3expd $.
  $}

  ${
    exp5o.1 $e |- ( ( ph /\ ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp5o $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wi wph wps wch w3a wth wta wet exp5o.1 exp3a
      3exp $.
  $}

  ${
    exp516.1 $e |- ( ( ( ph /\ ( ps /\ ch /\ th ) ) /\ ta ) -> et ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp516 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wph wps wch wth w3a wta wet exp516.1 exp31
      3expd $.
  $}

  ${
    exp520.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp520 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wph wps wch w3a wth wta wa wet exp520.1 ex exp5o
      $.
  $}

  ${
    3anassrs.1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    3anassrs $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      wph wps wch wth wta wph wps wch wth wta 3anassrs.1 3exp2 imp41 $.
  $}

  ${
    3adant1l.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant1l $p |- ( ( ( ta /\ ph ) /\ ps /\ ch ) -> th ) $=
      wta wph wa wps wch wth wph wps wch wa wth wta wph wps wch wth 3adant1l.1
      3expb adantll 3impb $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant1r $p |- ( ( ( ph /\ ta ) /\ ps /\ ch ) -> th ) $=
      wph wta wa wps wch wth wph wps wch wa wth wta wph wps wch wth 3adant1l.1
      3expb adantlr 3impb $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant2l $p |- ( ( ph /\ ( ta /\ ps ) /\ ch ) -> th ) $=
      wta wps wa wph wch wth wps wph wch wth wta wph wps wch wth 3adant1l.1
      3com12 3adant1l 3com12 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant2r $p |- ( ( ph /\ ( ps /\ ta ) /\ ch ) -> th ) $=
      wps wta wa wph wch wth wps wph wch wth wta wph wps wch wth 3adant1l.1
      3com12 3adant1r 3com12 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant3l $p |- ( ( ph /\ ps /\ ( ta /\ ch ) ) -> th ) $=
      wta wch wa wps wph wth wch wps wph wth wta wph wps wch wth 3adant1l.1
      3com13 3adant1l 3com13 $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant3r $p |- ( ( ph /\ ps /\ ( ch /\ ta ) ) -> th ) $=
      wch wta wa wps wph wth wch wps wph wth wta wph wps wch wth 3adant1l.1
      3com13 3adant1r 3com13 $.
  $}

  ${
    sylXanc.1 $e |- ( ph -> ps ) $.
    sylXanc.2 $e |- ( ph -> ch ) $.
    sylXanc.3 $e |- ( ph -> th ) $.
    ${
      syl12anc.4 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
      syl12anc $p |- ( ph -> ta ) $=
        wph wps wch wth wa wa wta wph wps wch wth sylXanc.1 sylXanc.2 sylXanc.3
        jca32 syl12anc.4 syl $.
    $}

    ${
      syl21anc.4 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
      syl21anc $p |- ( ph -> ta ) $=
        wph wps wch wa wth wa wta wph wps wch wth sylXanc.1 sylXanc.2 sylXanc.3
        jca31 syl21anc.4 syl $.
    $}

    ${
      syl111anc.4 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl3anc $p |- ( ph -> ta ) $=
        wph wps wch wth w3a wta wph wps wch wth sylXanc.1 sylXanc.2 sylXanc.3
        3jca syl111anc.4 syl $.
    $}

    sylXanc.4 $e |- ( ph -> ta ) $.
    ${
      syl22anc.5 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl22anc $p |- ( ph -> et ) $=
        wph wps wch wa wth wta wet wph wps wch sylXanc.1 sylXanc.2 jca
        sylXanc.3 sylXanc.4 syl22anc.5 syl12anc $.
    $}

    ${
      syl13anc.5 $e |- ( ( ps /\ ( ch /\ th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl13anc $p |- ( ph -> et ) $=
        wph wps wch wth wta w3a wet sylXanc.1 wph wch wth wta sylXanc.2
        sylXanc.3 sylXanc.4 3jca syl13anc.5 syl2anc $.
    $}

    ${
      syl31anc.5 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl31anc $p |- ( ph -> et ) $=
        wph wps wch wth w3a wta wet wph wps wch wth sylXanc.1 sylXanc.2
        sylXanc.3 3jca sylXanc.4 syl31anc.5 syl2anc $.
    $}

    ${
      syl112anc.5 $e |- ( ( ps /\ ch /\ ( th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl112anc $p |- ( ph -> et ) $=
        wph wps wch wth wta wa wet sylXanc.1 sylXanc.2 wph wth wta sylXanc.3
        sylXanc.4 jca syl112anc.5 syl3anc $.
    $}

    ${
      syl121anc.5 $e |- ( ( ps /\ ( ch /\ th ) /\ ta ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl121anc $p |- ( ph -> et ) $=
        wph wps wch wth wa wta wet sylXanc.1 wph wch wth sylXanc.2 sylXanc.3
        jca sylXanc.4 syl121anc.5 syl3anc $.
    $}

    ${
      syl211anc.5 $e |- ( ( ( ps /\ ch ) /\ th /\ ta ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl211anc $p |- ( ph -> et ) $=
        wph wps wch wa wth wta wet wph wps wch sylXanc.1 sylXanc.2 jca
        sylXanc.3 sylXanc.4 syl211anc.5 syl3anc $.
    $}

    sylXanc.5 $e |- ( ph -> et ) $.
    ${
      syl23anc.6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl23anc $p |- ( ph -> ze ) $=
        wph wps wch wa wth wta wet wze wph wps wch sylXanc.1 sylXanc.2 jca
        sylXanc.3 sylXanc.4 sylXanc.5 syl23anc.6 syl13anc $.
    $}

    ${
      syl32anc.6 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl32anc $p |- ( ph -> ze ) $=
        wph wps wch wth wta wet wa wze sylXanc.1 sylXanc.2 sylXanc.3 wph wta
        wet sylXanc.4 sylXanc.5 jca syl32anc.6 syl31anc $.
    $}

    ${
      syl122anc.6 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl122anc $p |- ( ph -> ze ) $=
        wph wps wch wth wta wet wa wze sylXanc.1 sylXanc.2 sylXanc.3 wph wta
        wet sylXanc.4 sylXanc.5 jca syl122anc.6 syl121anc $.
    $}

    ${
      syl212anc.6 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl212anc $p |- ( ph -> ze ) $=
        wph wps wch wth wta wet wa wze sylXanc.1 sylXanc.2 sylXanc.3 wph wta
        wet sylXanc.4 sylXanc.5 jca syl212anc.6 syl211anc $.
    $}

    ${
      syl221anc.6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ et ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl221anc $p |- ( ph -> ze ) $=
        wph wps wch wth wta wa wet wze sylXanc.1 sylXanc.2 wph wth wta
        sylXanc.3 sylXanc.4 jca sylXanc.5 syl221anc.6 syl211anc $.
    $}

    ${
      syl113anc.6 $e |- ( ( ps /\ ch /\ ( th /\ ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl113anc $p |- ( ph -> ze ) $=
        wph wps wch wth wta wet w3a wze sylXanc.1 sylXanc.2 wph wth wta wet
        sylXanc.3 sylXanc.4 sylXanc.5 3jca syl113anc.6 syl3anc $.
    $}

    ${
      syl131anc.6 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ et ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl131anc $p |- ( ph -> ze ) $=
        wph wps wch wth wta w3a wet wze sylXanc.1 wph wch wth wta sylXanc.2
        sylXanc.3 sylXanc.4 3jca sylXanc.5 syl131anc.6 syl3anc $.
    $}

    ${
      syl311anc.6 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ et ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl311anc $p |- ( ph -> ze ) $=
        wph wps wch wth w3a wta wet wze wph wps wch wth sylXanc.1 sylXanc.2
        sylXanc.3 3jca sylXanc.4 sylXanc.5 syl311anc.6 syl3anc $.
    $}

    sylXanc.6 $e |- ( ph -> ze ) $.
    ${
      syl33anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl33anc $p |- ( ph -> si ) $=
        wph wps wch wth w3a wta wet wze wsi wph wps wch wth sylXanc.1 sylXanc.2
        sylXanc.3 3jca sylXanc.4 sylXanc.5 sylXanc.6 syl33anc.7 syl13anc $.
    $}

    ${
      syl222anc.7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl222anc $p |- ( ph -> si ) $=
        wph wps wch wth wta wet wze wa wsi sylXanc.1 sylXanc.2 sylXanc.3
        sylXanc.4 wph wet wze sylXanc.5 sylXanc.6 jca syl222anc.7 syl221anc $.
    $}

    ${
      syl123anc.7 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl123anc $p |- ( ph -> si ) $=
        wph wps wch wth wa wta wet wze wsi sylXanc.1 wph wch wth sylXanc.2
        sylXanc.3 jca sylXanc.4 sylXanc.5 sylXanc.6 syl123anc.7 syl113anc $.
    $}

    ${
      syl132anc.7 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
      syl132anc $p |- ( ph -> si ) $=
        wph wps wch wth wta wet wze wa wsi sylXanc.1 sylXanc.2 sylXanc.3
        sylXanc.4 wph wet wze sylXanc.5 sylXanc.6 jca syl132anc.7 syl131anc $.
    $}

    ${
      syl213anc.7 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl213anc $p |- ( ph -> si ) $=
        wph wps wch wa wth wta wet wze wsi wph wps wch sylXanc.1 sylXanc.2 jca
        sylXanc.3 sylXanc.4 sylXanc.5 sylXanc.6 syl213anc.7 syl113anc $.
    $}

    ${
      syl231anc.7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl231anc $p |- ( ph -> si ) $=
        wph wps wch wa wth wta wet wze wsi wph wps wch sylXanc.1 sylXanc.2 jca
        sylXanc.3 sylXanc.4 sylXanc.5 sylXanc.6 syl231anc.7 syl131anc $.
    $}

    ${
      syl312anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
      syl312anc $p |- ( ph -> si ) $=
        wph wps wch wth wta wet wze wa wsi sylXanc.1 sylXanc.2 sylXanc.3
        sylXanc.4 wph wet wze sylXanc.5 sylXanc.6 jca syl312anc.7 syl311anc $.
    $}

    ${
      syl321anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
      syl321anc $p |- ( ph -> si ) $=
        wph wps wch wth wta wet wa wze wsi sylXanc.1 sylXanc.2 sylXanc.3 wph
        wta wet sylXanc.4 sylXanc.5 jca sylXanc.6 syl321anc.7 syl311anc $.
    $}

    sylXanc.7 $e |- ( ph -> si ) $.
    ${
      syl133anc.8 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze /\ si ) )
           -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl133anc $p |- ( ph -> rh ) $=
        wph wps wch wth wta wet wze wsi w3a wrh sylXanc.1 sylXanc.2 sylXanc.3
        sylXanc.4 wph wet wze wsi sylXanc.5 sylXanc.6 sylXanc.7 3jca
        syl133anc.8 syl131anc $.
    $}

    ${
      syl313anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze /\ si ) )
           -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl313anc $p |- ( ph -> rh ) $=
        wph wps wch wth wta wet wze wsi w3a wrh sylXanc.1 sylXanc.2 sylXanc.3
        sylXanc.4 wph wet wze wsi sylXanc.5 sylXanc.6 sylXanc.7 3jca
        syl313anc.8 syl311anc $.
    $}

    ${
      syl331anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ si )
           -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl331anc $p |- ( ph -> rh ) $=
        wph wps wch wth wta wet wze w3a wsi wrh sylXanc.1 sylXanc.2 sylXanc.3
        wph wta wet wze sylXanc.4 sylXanc.5 sylXanc.6 3jca sylXanc.7
        syl331anc.8 syl311anc $.
    $}

    ${
      syl223anc.8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl223anc $p |- ( ph -> rh ) $=
        wph wps wch wth wta wa wet wze wsi wrh sylXanc.1 sylXanc.2 wph wth wta
        sylXanc.3 sylXanc.4 jca sylXanc.5 sylXanc.6 sylXanc.7 syl223anc.8
        syl213anc $.
    $}

    ${
      syl232anc.8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl232anc $p |- ( ph -> rh ) $=
        wph wps wch wth wta wet wze wsi wa wrh sylXanc.1 sylXanc.2 sylXanc.3
        sylXanc.4 sylXanc.5 wph wze wsi sylXanc.6 sylXanc.7 jca syl232anc.8
        syl231anc $.
    $}

    ${
      syl322anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl322anc $p |- ( ph -> rh ) $=
        wph wps wch wth wta wet wze wsi wa wrh sylXanc.1 sylXanc.2 sylXanc.3
        sylXanc.4 sylXanc.5 wph wze wsi sylXanc.6 sylXanc.7 jca syl322anc.8
        syl321anc $.
    $}

    sylXanc.8 $e |- ( ph -> rh ) $.
    ${
      syl233anc.9 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl233anc $p |- ( ph -> mu ) $=
        wph wps wch wa wth wta wet wze wsi wrh wmu wph wps wch sylXanc.1
        sylXanc.2 jca sylXanc.3 sylXanc.4 sylXanc.5 sylXanc.6 sylXanc.7
        sylXanc.8 syl233anc.9 syl133anc $.
    $}

    ${
      syl323anc.9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl323anc $p |- ( ph -> mu ) $=
        wph wps wch wth wta wet wa wze wsi wrh wmu sylXanc.1 sylXanc.2
        sylXanc.3 wph wta wet sylXanc.4 sylXanc.5 jca sylXanc.6 sylXanc.7
        sylXanc.8 syl323anc.9 syl313anc $.
    $}

    ${
      syl332anc.9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl332anc $p |- ( ph -> mu ) $=
        wph wps wch wth wta wet wze wsi wrh wa wmu sylXanc.1 sylXanc.2
        sylXanc.3 sylXanc.4 sylXanc.5 sylXanc.6 wph wsi wrh sylXanc.7 sylXanc.8
        jca syl332anc.9 syl331anc $.
    $}

    sylXanc.9 $e |- ( ph -> mu ) $.
    ${
      syl333anc.10 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze )
          /\ ( si /\ rh /\ mu ) ) -> la ) $.
      $( A syllogism inference combined with contraction.  (Contributed by NM,
         10-Mar-2012.) $)
      syl333anc $p |- ( ph -> la ) $=
        wph wps wch wth wta wet wze wsi wrh wmu w3a wla sylXanc.1 sylXanc.2
        sylXanc.3 sylXanc.4 sylXanc.5 sylXanc.6 wph wsi wrh wmu sylXanc.7
        sylXanc.8 sylXanc.9 3jca syl333anc.10 syl331anc $.
    $}
  $}

  ${
    syl3an1.1 $e |- ( ph -> ps ) $.
    syl3an1.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an1 $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      wph wch wth w3a wps wch wth w3a wta wph wps wch wth syl3an1.1 3anim1i
      syl3an1.2 syl $.
  $}

  ${
    syl3an2.1 $e |- ( ph -> ch ) $.
    syl3an2.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an2 $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      wps wph wth wta wph wch wps wth wta wi syl3an2.1 wps wch wth wta
      syl3an2.2 3exp syl5 3imp $.
  $}

  ${
    syl3an3.1 $e |- ( ph -> th ) $.
    syl3an3.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an3 $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      wps wch wph wta wph wth wps wch wta syl3an3.1 wps wch wth wta syl3an3.2
      3exp syl7 3imp $.
  $}

  ${
    syl3an1b.1 $e |- ( ph <-> ps ) $.
    syl3an1b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an1b $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      wph wps wch wth wta wph wps syl3an1b.1 biimpi syl3an1b.2 syl3an1 $.
  $}

  ${
    syl3an2b.1 $e |- ( ph <-> ch ) $.
    syl3an2b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an2b $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      wph wps wch wth wta wph wch syl3an2b.1 biimpi syl3an2b.2 syl3an2 $.
  $}

  ${
    syl3an3b.1 $e |- ( ph <-> th ) $.
    syl3an3b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an3b $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      wph wps wch wth wta wph wth syl3an3b.1 biimpi syl3an3b.2 syl3an3 $.
  $}

  ${
    syl3an1br.1 $e |- ( ps <-> ph ) $.
    syl3an1br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an1br $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      wph wps wch wth wta wps wph syl3an1br.1 biimpri syl3an1br.2 syl3an1 $.
  $}

  ${
    syl3an2br.1 $e |- ( ch <-> ph ) $.
    syl3an2br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an2br $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      wph wps wch wth wta wch wph syl3an2br.1 biimpri syl3an2br.2 syl3an2 $.
  $}

  ${
    syl3an3br.1 $e |- ( th <-> ph ) $.
    syl3an3br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an3br $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      wph wps wch wth wta wth wph syl3an3br.1 biimpri syl3an3br.2 syl3an3 $.
  $}

  ${
    syl3an.1 $e |- ( ph -> ps ) $.
    syl3an.2 $e |- ( ch -> th ) $.
    syl3an.3 $e |- ( ta -> et ) $.
    syl3an.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference.  (Contributed by NM, 13-May-2004.) $)
    syl3an $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      wph wch wta w3a wps wth wet w3a wze wph wps wch wth wta wet syl3an.1
      syl3an.2 syl3an.3 3anim123i syl3an.4 syl $.
  $}

  ${
    syl3anb.1 $e |- ( ph <-> ps ) $.
    syl3anb.2 $e |- ( ch <-> th ) $.
    syl3anb.3 $e |- ( ta <-> et ) $.
    syl3anb.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference.  (Contributed by NM, 15-Oct-2005.) $)
    syl3anb $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      wph wch wta w3a wps wth wet w3a wze wph wps wch wth wta wet syl3anb.1
      syl3anb.2 syl3anb.3 3anbi123i syl3anb.4 sylbi $.
  $}

  ${
    syl3anbr.1 $e |- ( ps <-> ph ) $.
    syl3anbr.2 $e |- ( th <-> ch ) $.
    syl3anbr.3 $e |- ( et <-> ta ) $.
    syl3anbr.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference.  (Contributed by NM, 29-Dec-2011.) $)
    syl3anbr $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      wph wps wch wth wta wet wze wps wph syl3anbr.1 bicomi wth wch syl3anbr.2
      bicomi wet wta syl3anbr.3 bicomi syl3anbr.4 syl3anb $.
  $}

  ${
    syld3an3.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    syld3an3.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 20-May-2007.) $)
    syld3an3 $p |- ( ( ph /\ ps /\ ch ) -> ta ) $=
      wph wps wch w3a wph wps wth wta wph wps wch simp1 wph wps wch simp2
      syld3an3.1 syld3an3.2 syl3anc $.
  $}

  ${
    syld3an1.1 $e |- ( ( ch /\ ps /\ th ) -> ph ) $.
    syld3an1.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 7-Jul-2008.) $)
    syld3an1 $p |- ( ( ch /\ ps /\ th ) -> ta ) $=
      wth wps wch wta wth wps wch wph wta wch wps wth wph syld3an1.1 3com13 wph
      wps wth wta syld3an1.2 3com13 syld3an3 3com13 $.
  $}

  ${
    syld3an2.1 $e |- ( ( ph /\ ch /\ th ) -> ps ) $.
    syld3an2.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 20-May-2007.) $)
    syld3an2 $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      wph wth wch wta wph wth wch wps wta wph wch wth wps syld3an2.1 3com23 wph
      wps wth wta syld3an2.2 3com23 syld3an3 3com23 $.
  $}

  ${
    syl3anl1.1 $e |- ( ph -> ps ) $.
    syl3anl1.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
    syl3anl1 $p |- ( ( ( ph /\ ch /\ th ) /\ ta ) -> et ) $=
      wph wch wth w3a wps wch wth w3a wta wet wph wps wch wth syl3anl1.1
      3anim1i syl3anl1.2 sylan $.
  $}

  ${
    syl3anl2.1 $e |- ( ph -> ch ) $.
    syl3anl2.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
    syl3anl2 $p |- ( ( ( ps /\ ph /\ th ) /\ ta ) -> et ) $=
      wps wph wth w3a wta wet wph wps wch wth wta wet wi syl3anl2.1 wps wch wth
      w3a wta wet syl3anl2.2 ex syl3an2 imp $.
  $}

  ${
    syl3anl3.1 $e |- ( ph -> th ) $.
    syl3anl3.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
    syl3anl3 $p |- ( ( ( ps /\ ch /\ ph ) /\ ta ) -> et ) $=
      wps wch wph w3a wps wch wth w3a wta wet wph wth wps wch syl3anl3.1
      3anim3i syl3anl3.2 sylan $.
  $}

  ${
    syl3anl.1 $e |- ( ph -> ps ) $.
    syl3anl.2 $e |- ( ch -> th ) $.
    syl3anl.3 $e |- ( ta -> et ) $.
    syl3anl.4 $e |- ( ( ( ps /\ th /\ et ) /\ ze ) -> si ) $.
    $( A triple syllogism inference.  (Contributed by NM, 24-Dec-2006.) $)
    syl3anl $p |- ( ( ( ph /\ ch /\ ta ) /\ ze ) -> si ) $=
      wph wch wta w3a wps wth wet w3a wze wsi wph wps wch wth wta wet syl3anl.1
      syl3anl.2 syl3anl.3 3anim123i syl3anl.4 sylan $.
  $}

  ${
    syl3anr1.1 $e |- ( ph -> ps ) $.
    syl3anr1.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 31-Jul-2007.) $)
    syl3anr1 $p |- ( ( ch /\ ( ph /\ th /\ ta ) ) -> et ) $=
      wph wth wta w3a wch wps wth wta w3a wet wph wps wth wta syl3anr1.1
      3anim1i syl3anr1.2 sylan2 $.
  $}

  ${
    syl3anr2.1 $e |- ( ph -> th ) $.
    syl3anr2.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 1-Aug-2007.) $)
    syl3anr2 $p |- ( ( ch /\ ( ps /\ ph /\ ta ) ) -> et ) $=
      wps wph wta w3a wch wet wph wps wth wta wch wet syl3anr2.1 wch wps wth
      wta w3a wet syl3anr2.2 ancoms syl3anl2 ancoms $.
  $}

  ${
    syl3anr3.1 $e |- ( ph -> ta ) $.
    syl3anr3.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 23-Aug-2007.) $)
    syl3anr3 $p |- ( ( ch /\ ( ps /\ th /\ ph ) ) -> et ) $=
      wps wth wph w3a wch wps wth wta w3a wet wph wta wps wth syl3anr3.1
      3anim3i syl3anr3.2 sylan2 $.
  $}

  ${
    3impdi.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th ) $.
    $( Importation inference (undistribute conjunction).  (Contributed by NM,
       14-Aug-1995.) $)
    3impdi $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth 3impdi.1 anandis 3impb $.
  $}

  ${
    3impdir.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ ps ) ) -> th ) $.
    $( Importation inference (undistribute conjunction).  (Contributed by NM,
       20-Aug-1995.) $)
    3impdir $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      wph wch wps wth wph wch wps wth 3impdir.1 anandirs 3impa $.
  $}

  ${
    3anidm12.1 $e |- ( ( ph /\ ph /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction.  (Contributed by NM,
       7-Mar-2008.) $)
    3anidm12 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wph wps wch 3anidm12.1 3expib anabsi5 $.
  $}

  ${
    3anidm13.1 $e |- ( ( ph /\ ps /\ ph ) -> ch ) $.
    $( Inference from idempotent law for conjunction.  (Contributed by NM,
       7-Mar-2008.) $)
    3anidm13 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wph wch 3anidm13.1 3com23 3anidm12 $.
  $}

  ${
    3anidm23.1 $e |- ( ( ph /\ ps /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction.  (Contributed by NM,
       1-Feb-2007.) $)
    3anidm23 $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wps wch 3anidm23.1 3expa anabss3 $.
  $}

  ${
    3ori.1 $e |- ( ph \/ ps \/ ch ) $.
    $( Infer implication from triple disjunction.  (Contributed by NM,
       26-Sep-2006.) $)
    3ori $p |- ( ( -. ph /\ -. ps ) -> ch ) $=
      wph wn wps wn wa wph wps wo wn wch wph wps ioran wph wps wo wch wph wps
      wch w3o wph wps wo wch wo 3ori.1 wph wps wch df-3or mpbi ori sylbir $.
  $}

  $( Disjunction of 3 antecedents.  (Contributed by NM, 8-Apr-1994.) $)
  3jao $p |- ( ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ->
              ( ( ph \/ ch \/ th ) -> ps ) ) $=
    wph wch wth w3o wph wch wo wth wo wph wps wi wch wps wi wth wps wi w3a wps
    wph wch wth df-3or wph wps wi wch wps wi wth wps wi wph wch wo wth wo wps
    wi wph wps wi wch wps wi wph wch wo wps wi wth wps wi wph wch wo wth wo wps
    wi wi wph wps wch jao wph wch wo wps wth jao syl6 3imp syl5bi $.

  $( Disjunction of 3 antecedents.  (Contributed by NM, 13-Sep-2011.) $)
  3jaob $p |- ( ( ( ph \/ ch \/ th ) -> ps ) <->
              ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ) $=
    wph wch wth w3o wps wi wph wps wi wch wps wi wth wps wi w3a wph wch wth w3o
    wps wi wph wps wi wch wps wi wth wps wi wph wph wch wth w3o wps wph wch wth
    3mix1 imim1i wch wph wch wth w3o wps wch wph wth 3mix2 imim1i wth wph wch
    wth w3o wps wth wph wch 3mix3 imim1i 3jca wph wps wch wth 3jao impbii $.

  ${
    3jaoi.1 $e |- ( ph -> ps ) $.
    3jaoi.2 $e |- ( ch -> ps ) $.
    3jaoi.3 $e |- ( th -> ps ) $.
    $( Disjunction of 3 antecedents (inference).  (Contributed by NM,
       12-Sep-1995.) $)
    3jaoi $p |- ( ( ph \/ ch \/ th ) -> ps ) $=
      wph wps wi wch wps wi wth wps wi w3a wph wch wth w3o wps wi wph wps wi
      wch wps wi wth wps wi 3jaoi.1 3jaoi.2 3jaoi.3 3pm3.2i wph wps wch wth
      3jao ax-mp $.
  $}

  ${
    3jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    3jaod.3 $e |- ( ph -> ( ta -> ch ) ) $.
    $( Disjunction of 3 antecedents (deduction).  (Contributed by NM,
       14-Oct-2005.) $)
    3jaod $p |- ( ph -> ( ( ps \/ th \/ ta ) -> ch ) ) $=
      wph wps wch wi wth wch wi wta wch wi wps wth wta w3o wch wi 3jaod.1
      3jaod.2 3jaod.3 wps wch wth wta 3jao syl3anc $.
  $}

  ${
    3jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    3jaoian.3 $e |- ( ( ta /\ ps ) -> ch ) $.
    $( Disjunction of 3 antecedents (inference).  (Contributed by NM,
       14-Oct-2005.) $)
    3jaoian $p |- ( ( ( ph \/ th \/ ta ) /\ ps ) -> ch ) $=
      wph wth wta w3o wps wch wph wps wch wi wth wta wph wps wch 3jaoian.1 ex
      wth wps wch 3jaoian.2 ex wta wps wch 3jaoian.3 ex 3jaoi imp $.
  $}

  ${
    3jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    3jaodan.3 $e |- ( ( ph /\ ta ) -> ch ) $.
    $( Disjunction of 3 antecedents (deduction).  (Contributed by NM,
       14-Oct-2005.) $)
    3jaodan $p |- ( ( ph /\ ( ps \/ th \/ ta ) ) -> ch ) $=
      wph wps wth wta w3o wch wph wps wch wth wta wph wps wch 3jaodan.1 ex wph
      wth wch 3jaodan.2 ex wph wta wch 3jaodan.3 ex 3jaod imp $.
  $}

  ${
    3jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    3jaao.3 $e |- ( et -> ( ze -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of three
       implications.  (Contributed by Jeff Hankins, 15-Aug-2009.)  (Proof
       shortened by Andrew Salmon, 13-May-2011.) $)
    3jaao $p |- ( ( ph /\ th /\ et ) -> ( ( ps \/ ta \/ ze ) -> ch ) ) $=
      wph wth wet w3a wps wch wta wze wph wth wps wch wi wet 3jaao.1 3ad2ant1
      wth wph wta wch wi wet 3jaao.2 3ad2ant2 wet wph wze wch wi wth 3jaao.3
      3ad2ant3 3jaod $.
  $}

  ${
    syl3an9b.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl3an9b.2 $e |- ( th -> ( ch <-> ta ) ) $.
    syl3an9b.3 $e |- ( et -> ( ta <-> ze ) ) $.
    $( Nested syllogism inference conjoining 3 dissimilar antecedents.
       (Contributed by NM, 1-May-1995.) $)
    syl3an9b $p |- ( ( ph /\ th /\ et ) -> ( ps <-> ze ) ) $=
      wph wth wet wps wze wb wph wth wa wps wta wet wze wph wps wch wth wta
      syl3an9b.1 syl3an9b.2 sylan9bb syl3an9b.3 sylan9bb 3impa $.
  $}

  ${
    bi3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi3d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    bi3d.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Deduction joining 3 equivalences to form equivalence of disjunctions.
       (Contributed by NM, 20-Apr-1994.) $)
    3orbi123d $p |- ( ph -> ( ( ps \/ th \/ et ) <-> ( ch \/ ta \/ ze ) ) ) $=
      wph wps wth wo wet wo wch wta wo wze wo wps wth wet w3o wch wta wze w3o
      wph wps wth wo wch wta wo wet wze wph wps wch wth wta bi3d.1 bi3d.2
      orbi12d bi3d.3 orbi12d wps wth wet df-3or wch wta wze df-3or 3bitr4g $.

    $( Deduction joining 3 equivalences to form equivalence of conjunctions.
       (Contributed by NM, 22-Apr-1994.) $)
    3anbi123d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ ze ) ) ) $=
      wph wps wth wa wet wa wch wta wa wze wa wps wth wet w3a wch wta wze w3a
      wph wps wth wa wch wta wa wet wze wph wps wch wth wta bi3d.1 bi3d.2
      anbi12d bi3d.3 anbi12d wps wth wet df-3an wch wta wze df-3an 3bitr4g $.
  $}

  ${
    3anbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3anbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi12d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ et ) ) ) $=
      wph wps wch wth wta wet wet 3anbi12d.1 3anbi12d.2 wph wet biidd 3anbi123d
      $.

    $( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi13d $p |- ( ph -> ( ( ps /\ et /\ th ) <-> ( ch /\ et /\ ta ) ) ) $=
      wph wps wch wet wet wth wta 3anbi12d.1 wph wet biidd 3anbi12d.2 3anbi123d
      $.

    $( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi23d $p |- ( ph -> ( ( et /\ ps /\ th ) <-> ( et /\ ch /\ ta ) ) ) $=
      wph wet wet wps wch wth wta wph wet biidd 3anbi12d.1 3anbi12d.2 3anbi123d
      $.
  $}

  ${
    3anbi1d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
    3anbi1d $p |- ( ph -> ( ( ps /\ th /\ ta ) <-> ( ch /\ th /\ ta ) ) ) $=
      wph wps wch wth wth wta 3anbi1d.1 wph wth biidd 3anbi12d $.

    $( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
    3anbi2d $p |- ( ph -> ( ( th /\ ps /\ ta ) <-> ( th /\ ch /\ ta ) ) ) $=
      wph wth wth wps wch wta wph wth biidd 3anbi1d.1 3anbi12d $.

    $( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
    3anbi3d $p |- ( ph -> ( ( th /\ ta /\ ps ) <-> ( th /\ ta /\ ch ) ) ) $=
      wph wth wth wps wch wta wph wth biidd 3anbi1d.1 3anbi13d $.
  $}

  ${
    3anim123d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3anim123d.2 $e |- ( ph -> ( th -> ta ) ) $.
    3anim123d.3 $e |- ( ph -> ( et -> ze ) ) $.
    $( Deduction joining 3 implications to form implication of conjunctions.
       (Contributed by NM, 24-Feb-2005.) $)
    3anim123d $p |- ( ph -> ( ( ps /\ th /\ et ) -> ( ch /\ ta /\ ze ) ) ) $=
      wph wps wth wa wet wa wch wta wa wze wa wps wth wet w3a wch wta wze w3a
      wph wps wth wa wch wta wa wet wze wph wps wch wth wta 3anim123d.1
      3anim123d.2 anim12d 3anim123d.3 anim12d wps wth wet df-3an wch wta wze
      df-3an 3imtr4g $.

    $( Deduction joining 3 implications to form implication of disjunctions.
       (Contributed by NM, 4-Apr-1997.) $)
    3orim123d $p |- ( ph -> ( ( ps \/ th \/ et ) -> ( ch \/ ta \/ ze ) ) ) $=
      wph wps wth wo wet wo wch wta wo wze wo wps wth wet w3o wch wta wze w3o
      wph wps wth wo wch wta wo wet wze wph wps wch wth wta 3anim123d.1
      3anim123d.2 orim12d 3anim123d.3 orim12d wps wth wet df-3or wch wta wze
      df-3or 3imtr4g $.
  $}

  $( Rearrangement of 6 conjuncts.  (Contributed by NM, 13-Mar-1995.) $)
  an6 $p |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) ) <->
              ( ( ph /\ th ) /\ ( ps /\ ta ) /\ ( ch /\ et ) ) ) $=
    wph wps wa wch wa wth wta wa wet wa wa wph wth wa wps wta wa wa wch wet wa
    wa wph wps wch w3a wth wta wet w3a wa wph wth wa wps wta wa wch wet wa w3a
    wph wps wa wch wa wth wta wa wet wa wa wph wps wa wth wta wa wa wch wet wa
    wa wph wth wa wps wta wa wa wch wet wa wa wph wps wa wch wth wta wa wet an4
    wph wps wa wth wta wa wa wph wth wa wps wta wa wa wch wet wa wph wps wth
    wta an4 anbi1i bitri wph wps wch w3a wph wps wa wch wa wth wta wet w3a wth
    wta wa wet wa wph wps wch df-3an wth wta wet df-3an anbi12i wph wth wa wps
    wta wa wch wet wa df-3an 3bitr4i $.

  $( Analog of ~ an4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  3an6 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) /\ ( ta /\ et ) ) <->
                ( ( ph /\ ch /\ ta ) /\ ( ps /\ th /\ et ) ) ) $=
    wph wch wta w3a wps wth wet w3a wa wph wps wa wch wth wa wta wet wa w3a wph
    wch wta wps wth wet an6 bicomi $.

  $( Analog of ~ or4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.) $)
  3or6 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) \/ ( ta \/ et ) ) <->
                ( ( ph \/ ch \/ ta ) \/ ( ps \/ th \/ et ) ) ) $=
    wph wps wo wch wth wo wo wta wet wo wo wph wch wo wta wo wps wth wo wet wo
    wo wph wps wo wch wth wo wta wet wo w3o wph wch wta w3o wps wth wet w3o wo
    wph wch wo wta wo wps wth wo wet wo wo wph wch wo wps wth wo wo wta wet wo
    wo wph wps wo wch wth wo wo wta wet wo wo wph wch wo wta wps wth wo wet or4
    wph wch wo wps wth wo wo wph wps wo wch wth wo wo wta wet wo wph wch wps
    wth or4 orbi1i bitr2i wph wps wo wch wth wo wta wet wo df-3or wph wch wta
    w3o wph wch wo wta wo wps wth wet w3o wps wth wo wet wo wph wch wta df-3or
    wps wth wet df-3or orbi12i 3bitr4i $.

  ${
    mp3an1.1 $e |- ph $.
    mp3an1.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
    mp3an1 $p |- ( ( ps /\ ch ) -> th ) $=
      wph wps wch wa wth mp3an1.1 wph wps wch wth mp3an1.2 3expb mpan $.
  $}

  ${
    mp3an2.1 $e |- ps $.
    mp3an2.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
    mp3an2 $p |- ( ( ph /\ ch ) -> th ) $=
      wph wps wch wth mp3an2.1 wph wps wch wth mp3an2.2 3expa mpanl2 $.
  $}

  ${
    mp3an3.1 $e |- ch $.
    mp3an3.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
    mp3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      wph wps wa wch wth mp3an3.1 wph wps wch wth mp3an3.2 3expia mpi $.
  $}

  ${
    mp3an12.1 $e |- ph $.
    mp3an12.2 $e |- ps $.
    mp3an12.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       13-Jul-2005.) $)
    mp3an12 $p |- ( ch -> th ) $=
      wps wch wth mp3an12.2 wph wps wch wth mp3an12.1 mp3an12.3 mp3an1 mpan $.
  $}

  ${
    mp3an13.1 $e |- ph $.
    mp3an13.2 $e |- ch $.
    mp3an13.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       14-Jul-2005.) $)
    mp3an13 $p |- ( ps -> th ) $=
      wph wps wth mp3an13.1 wph wps wch wth mp3an13.2 mp3an13.3 mp3an3 mpan $.
  $}

  ${
    mp3an23.1 $e |- ps $.
    mp3an23.2 $e |- ch $.
    mp3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       14-Jul-2005.) $)
    mp3an23 $p |- ( ph -> th ) $=
      wph wps wth mp3an23.1 wph wps wch wth mp3an23.2 mp3an23.3 mp3an3 mpan2 $.
  $}

  ${
    mp3an1i.1 $e |- ps $.
    mp3an1i.2 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 5-Jul-2005.) $)
    mp3an1i $p |- ( ph -> ( ( ch /\ th ) -> ta ) ) $=
      wch wth wa wph wta wps wch wth wph wta wi mp3an1i.1 wph wps wch wth w3a
      wta mp3an1i.2 com12 mp3an1 com12 $.
  $}

  ${
    mp3anl1.1 $e |- ph $.
    mp3anl1.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
    mp3anl1 $p |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $=
      wps wch wa wth wta wph wps wch wth wta wi mp3anl1.1 wph wps wch w3a wth
      wta mp3anl1.2 ex mp3an1 imp $.
  $}

  ${
    mp3anl2.1 $e |- ps $.
    mp3anl2.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
    mp3anl2 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      wph wch wa wth wta wph wps wch wth wta wi mp3anl2.1 wph wps wch w3a wth
      wta mp3anl2.2 ex mp3an2 imp $.
  $}

  ${
    mp3anl3.1 $e |- ch $.
    mp3anl3.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
    mp3anl3 $p |- ( ( ( ph /\ ps ) /\ th ) -> ta ) $=
      wph wps wa wth wta wph wps wch wth wta wi mp3anl3.1 wph wps wch w3a wth
      wta mp3anl3.2 ex mp3an3 imp $.
  $}

  ${
    mp3anr1.1 $e |- ps $.
    mp3anr1.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 4-Nov-2006.) $)
    mp3anr1 $p |- ( ( ph /\ ( ch /\ th ) ) -> ta ) $=
      wch wth wa wph wta wps wch wth wph wta mp3anr1.1 wph wps wch wth w3a wta
      mp3anr1.2 ancoms mp3anl1 ancoms $.
  $}

  ${
    mp3anr2.1 $e |- ch $.
    mp3anr2.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Nov-2006.) $)
    mp3anr2 $p |- ( ( ph /\ ( ps /\ th ) ) -> ta ) $=
      wps wth wa wph wta wps wch wth wph wta mp3anr2.1 wph wps wch wth w3a wta
      mp3anr2.2 ancoms mp3anl2 ancoms $.
  $}

  ${
    mp3anr3.1 $e |- th $.
    mp3anr3.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       19-Oct-2007.) $)
    mp3anr3 $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      wps wch wa wph wta wps wch wth wph wta mp3anr3.1 wph wps wch wth w3a wta
      mp3anr3.2 ancoms mp3anl3 ancoms $.
  $}

  ${
    mp3an.1 $e |- ph $.
    mp3an.2 $e |- ps $.
    mp3an.3 $e |- ch $.
    mp3an.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       14-May-1999.) $)
    mp3an $p |- th $=
      wps wch wth mp3an.2 mp3an.3 wph wps wch wth mp3an.1 mp3an.4 mp3an1 mp2an
      $.
  $}

  ${
    mpd3an3.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    mpd3an3.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 8-Nov-2007.) $)
    mpd3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      wph wps wa wch wth mpd3an3.2 wph wps wch wth mpd3an3.3 3expa mpdan $.
  $}

  ${
    mpd3an23.1 $e |- ( ph -> ps ) $.
    mpd3an23.2 $e |- ( ph -> ch ) $.
    mpd3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 4-Dec-2006.) $)
    mpd3an23 $p |- ( ph -> th ) $=
      wph wph wps wch wth wph id mpd3an23.1 mpd3an23.2 mpd3an23.3 syl3anc $.
  $}

  ${
    mp3and.1 $e |- ( ph -> ps ) $.
    mp3and.2 $e |- ( ph -> ch ) $.
    mp3and.3 $e |- ( ph -> th ) $.
    mp3and.4 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( A deduction based on modus ponens.  (Contributed by Mario Carneiro,
       24-Dec-2016.) $)
    mp3and $p |- ( ph -> ta ) $=
      wph wps wch wth w3a wta wph wps wch wth mp3and.1 mp3and.2 mp3and.3 3jca
      mp3and.4 mpd $.
  $}

  ${
    biimp3a.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Infer implication from a logical equivalence.  Similar to ~ biimpa .
       (Contributed by NM, 4-Sep-2005.) $)
    biimp3a $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      wph wps wch wth wph wps wa wch wth biimp3a.1 biimpa 3impa $.

    $( Infer implication from a logical equivalence.  Similar to ~ biimpar .
       (Contributed by NM, 2-Jan-2009.) $)
    biimp3ar $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      wph wps wth wch wph wps wch wth biimp3a.1 exbiri 3imp $.
  $}

  ${
    3anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent.
       (Contributed by NM, 18-Apr-2007.) $)
    3anandis $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      wph wps wch wth w3a wa wph wps wph wch wph wth wta wph wps wch wth w3a
      simpl wph wps wch wth simpr1 wph wps wch wth w3a simpl wph wps wch wth
      simpr2 wph wps wch wth w3a simpl wph wps wch wth simpr3 3anandis.1
      syl222anc $.
  $}

  ${
    3anandirs.1 $e |- ( ( ( ph /\ th ) /\ ( ps /\ th ) /\ ( ch /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent.
       (Contributed by NM, 25-Jul-2006.) $)
    3anandirs $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      wph wps wch w3a wth wa wph wth wps wth wch wth wta wph wps wch wth simpl1
      wph wps wch w3a wth simpr wph wps wch wth simpl2 wph wps wch w3a wth
      simpr wph wps wch wth simpl3 wph wps wch w3a wth simpr 3anandirs.1
      syl222anc $.
  $}

  ${
    ecase23d.1 $e |- ( ph -> -. ch ) $.
    ecase23d.2 $e |- ( ph -> -. th ) $.
    ecase23d.3 $e |- ( ph -> ( ps \/ ch \/ th ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM,
       22-Apr-1994.) $)
    ecase23d $p |- ( ph -> ps ) $=
      wph wps wch wth wo wph wch wn wth wn wch wth wo wn ecase23d.1 ecase23d.2
      wch wth ioran sylanbrc wph wps wch wth wo wph wps wch wth w3o wps wch wth
      wo wo ecase23d.3 wps wch wth 3orass sylib ord mt3d $.
  $}

  ${
    3ecase.1 $e |- ( -. ph -> th ) $.
    3ecase.2 $e |- ( -. ps -> th ) $.
    3ecase.3 $e |- ( -. ch -> th ) $.
    3ecase.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Inference for elimination by cases.  (Contributed by NM,
       13-Jul-2005.) $)
    3ecase $p |- th $=
      wps wch wth wph wps wch wth wi wi wph wps wch wth 3ecase.4 3exp wph wn
      wch wth wi wps wph wn wth wch 3ecase.1 a1d a1d pm2.61i 3ecase.2 3ecase.3
      pm2.61nii $.
  $}


