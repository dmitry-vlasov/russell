
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_implication.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical negation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section makes our first use of the third axiom of propositional
  calculus, ~ ax-3 .

$)

  ${
    con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Deduction derived from axiom ~ ax-3 .  (Contributed by NM,
       26-Mar-1995.) $)
    con4d $p |- ( ph -> ( ch -> ps ) ) $=
      wph wps wn wch wn wi wch wps wi con4d.1 wps wch ax-3 syl $.
  $}

  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by NM, 10-Feb-1996.) $)
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      wph wch wps wph wps wn wch wn pm2.21d.1 a1d con4d $.
  $}

  ${
    pm2.21dd.1 $e |- ( ph -> ps ) $.
    pm2.21dd.2 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
    pm2.21dd $p |- ( ph -> ch ) $=
      wph wps wch pm2.21dd.1 wph wps wch pm2.21dd.2 pm2.21d mpd $.
  $}

  $( From a wff and its negation, anything is true.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 14-Sep-2012.) $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    wph wn wph wps wph wn id pm2.21d $.

  $( Theorem *2.24 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    wph wn wph wps wph wps pm2.21 com12 $.

  $( Proof by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.  Also
     called the Law of Clavius.  (Contributed by NM, 5-Aug-1993.) $)
  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    wph wn wph wi wph wph wn wph wi wph wph wn wph wi wph wn wph wph wn wph wi
    wn wph wph wn wph wi wn pm2.21 a2i con4d pm2.43i $.

  ${
    pm2.18d.1 $e |- ( ph -> ( -. ps -> ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by FL,
       12-Jul-2009.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    pm2.18d $p |- ( ph -> ps ) $=
      wph wps wn wps wi wps pm2.18d.1 wps pm2.18 syl $.
  $}

  $( Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by David Harvey,
     5-Sep-1999.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
  notnot2 $p |- ( -. -. ph -> ph ) $=
    wph wn wn wph wph wn wph pm2.21 pm2.18d $.

  ${
    notnotrd.1 $e |- ( ph -> -. -. ps ) $.
    $( Deduction converting double-negation into the original wff, aka the
       double negation rule.  A translation of natural deduction rule ` -. -. `
       -C, ` _G |- -. -. ps ` => ` _G |- ps ` ; see ~ natded .  This is
       definition NNC in [Pfenning] p. 17.  This rule is valid in classical
       logic (which MPE uses), but not intuitionistic logic.  (Contributed by
       DAW, 8-Feb-2017.) $)
    notnotrd $p |- ( ph -> ps ) $=
      wph wps wn wn wps notnotrd.1 wps notnot2 syl $.
  $}

  ${
    notnotri.1 $e |- -. -. ph $.
    $( Inference from double negation.  (Contributed by NM, 27-Feb-2008.) $)
    notnotri $p |- ph $=
      wph wn wn wph notnotri.1 wph notnot2 ax-mp $.
  $}

  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 19-Aug-1993.) $)
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      wph wps wn wch wps wn wn wps wph wch wn wps notnot2 con2d.1 syl5 con4d $.
  $}

  $( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    wph wps wn wi wph wps wph wps wn wi id con2d $.

  ${
    mt2d.1 $e |- ( ph -> ch ) $.
    mt2d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 4-Jul-1994.) $)
    mt2d $p |- ( ph -> -. ps ) $=
      wph wch wps wn mt2d.1 wph wps wch mt2d.2 con2d mpd $.
  $}

  ${
    mt2i.1 $e |- ch $.
    mt2i.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mt2i $p |- ( ph -> -. ps ) $=
      wph wps wch wch wph mt2i.1 a1i mt2i.2 mt2d $.
  $}

  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 1-Dec-1995.) $)
    nsyl3 $p |- ( ch -> -. ph ) $=
      wch wph wps nsyl3.2 wph wps wn wi wch nsyl3.1 a1i mt2d $.
  $}

  ${
    con2i.a $e |- ( ph -> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.)  (Proof shortened by Wolf Lammen,
       13-Jun-2013.) $)
    con2i $p |- ( ps -> -. ph ) $=
      wph wps wps con2i.a wps id nsyl3 $.
  $}

  ${
    nsyl.1 $e |- ( ph -> -. ps ) $.
    nsyl.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 31-Dec-1993.)
       (Proof shortened by Wolf Lammen, 2-Mar-2013.) $)
    nsyl $p |- ( ph -> -. ch ) $=
      wch wph wph wps wch nsyl.1 nsyl.2 nsyl3 con2i $.
  $}

  $( Converse of double negation.  Theorem *2.12 of [WhiteheadRussell] p. 101.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     2-Mar-2013.) $)
  notnot1 $p |- ( ph -> -. -. ph ) $=
    wph wn wph wph wn id con2i $.

  ${
    negbi.1 $e |- ph $.
    $( Infer double negation.  (Contributed by NM, 27-Feb-2008.) $)
    notnoti $p |- -. -. ph $=
      wph wph wn wn negbi.1 wph notnot1 ax-mp $.
  $}

  ${
    con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 5-Aug-1993.) $)
    con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
      wph wps wch wn wph wps wn wch wch wn wn con1d.1 wch notnot1 syl6 con4d $.
  $}

  ${
    mt3d.1 $e |- ( ph -> -. ch ) $.
    mt3d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 26-Mar-1995.) $)
    mt3d $p |- ( ph -> ps ) $=
      wph wch wn wps mt3d.1 wph wps wch mt3d.2 con1d mpd $.
  $}

  ${
    mt3i.1 $e |- -. ch $.
    mt3i.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mt3i $p |- ( ph -> ps ) $=
      wph wps wch wch wn wph mt3i.1 a1i mt3i.2 mt3d $.
  $}

  ${
    nsyl2.1 $e |- ( ph -> -. ps ) $.
    nsyl2.2 $e |- ( -. ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 26-Jun-1994.) $)
    nsyl2 $p |- ( ph -> ch ) $=
      wph wch wps nsyl2.1 wch wn wps wi wph nsyl2.2 a1i mt3d $.
  $}

  $( Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
  con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    wph wn wps wi wph wps wph wn wps wi id con1d $.

  ${
    con1i.a $e |- ( -. ph -> ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.)  (Proof shortened by Wolf Lammen,
       19-Jun-2013.) $)
    con1i $p |- ( -. ps -> ph ) $=
      wps wn wps wph wps wn id con1i.a nsyl2 $.
  $}

  ${
    con4i.1 $e |- ( -. ph -> -. ps ) $.
    $( Inference rule derived from axiom ~ ax-3 .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 21-Jun-2013.) $)
    con4i $p |- ( ps -> ph ) $=
      wps wps wn wph wps notnot1 con4i.1 nsyl2 $.
  $}

  ${
    pm2.21i.1 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.21 .
       (Contributed by NM, 16-Sep-1993.) $)
    pm2.21i $p |- ( ph -> ps ) $=
      wps wph wph wn wps wn pm2.21i.1 a1i con4i $.
  $}

  ${
    pm2.24ii.1 $e |- ph $.
    pm2.24ii.2 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.24 .
       (Contributed by NM, 27-Feb-2008.) $)
    pm2.24ii $p |- ps $=
      wph wps pm2.24ii.1 wph wps pm2.24ii.2 pm2.21i ax-mp $.
  $}

  ${
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 5-Aug-1993.) $)
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      wph wps wn wch wps wn wn wps wph wch wps notnot2 con3d.1 syl5 con1d $.
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Feb-2013.) $)
  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    wph wps wi wph wps wph wps wi id con3d $.

  ${
    con3i.a $e |- ( ph -> ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 20-Jun-2013.) $)
    con3i $p |- ( -. ps -> -. ph ) $=
      wps wn wps wph wps wn id con3i.a nsyl $.
  $}

  ${
    con3rr3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Rotate through consequent right.  (Contributed by Wolf Lammen,
       3-Nov-2013.) $)
    con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $=
      wph wch wn wps wn wph wps wch con3rr3.1 con3d com12 $.
  $}

  ${
    mt4.1 $e |- ph $.
    mt4.2 $e |- ( -. ps -> -. ph ) $.
    $( The rule of modus tollens.  (Contributed by Wolf Lammen,
       12-May-2013.) $)
    mt4 $p |- ps $=
      wph wps mt4.1 wps wph mt4.2 con4i ax-mp $.
  $}

  ${
    mt4d.1 $e |- ( ph -> ps ) $.
    mt4d.2 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 9-Jun-2006.) $)
    mt4d $p |- ( ph -> ch ) $=
      wph wps wch mt4d.1 wph wch wps mt4d.2 con4d mpd $.
  $}

  ${
    mt4i.1 $e |- ch $.
    mt4i.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by Wolf Lammen, 12-May-2013.) $)
    mt4i $p |- ( ph -> ps ) $=
      wph wch wps wch wph mt4i.1 a1i mt4i.2 mt4d $.
  $}

  ${
    nsyld.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    nsyld.2 $e |- ( ph -> ( ta -> ch ) ) $.
    $( A negated syllogism deduction.  (Contributed by NM, 9-Apr-2005.) $)
    nsyld $p |- ( ph -> ( ps -> -. ta ) ) $=
      wph wps wch wn wta wn nsyld.1 wph wta wch nsyld.2 con3d syld $.
  $}

  ${
    nsyli.1 $e |- ( ph -> ( ps -> ch ) ) $.
    nsyli.2 $e |- ( th -> -. ch ) $.
    $( A negated syllogism inference.  (Contributed by NM, 3-May-1994.) $)
    nsyli $p |- ( ph -> ( th -> -. ps ) ) $=
      wth wch wn wph wps wn nsyli.2 wph wps wch nsyli.1 con3d syl5 $.
  $}

  ${
    nsyl4.1 $e |- ( ph -> ps ) $.
    nsyl4.2 $e |- ( -. ph -> ch ) $.
    $( A negated syllogism inference.  (Contributed by NM, 15-Feb-1996.) $)
    nsyl4 $p |- ( -. ch -> ps ) $=
      wch wn wph wps wph wch nsyl4.2 con1i nsyl4.1 syl $.
  $}

  ${
    pm2.24d.1 $e |- ( ph -> ps ) $.
    $( Deduction version of ~ pm2.24 .  (Contributed by NM, 30-Jan-2006.) $)
    pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $=
      wph wch wps wph wps wch wn pm2.24d.1 a1d con1d $.
  $}

  ${
    pm2.24i.1 $e |- ph $.
    $( Inference version of ~ pm2.24 .  (Contributed by NM, 20-Aug-2001.) $)
    pm2.24i $p |- ( -. ph -> ps ) $=
      wps wph wph wps wn pm2.24i.1 a1i con1i $.
  $}

  $( Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Josh
     Purinton, 29-Dec-2000.) $)
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    wph wph wps wn wi wps wph wps wn pm2.27 con2d $.

  $( Theorem 8 of [Margaris] p. 60.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Josh Purinton, 29-Dec-2000.) $)
  mth8 $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    wph wph wps wi wps wph wps pm2.27 con3d $.

  ${
    jc.1 $e |- ( ph -> ps ) $.
    jc.2 $e |- ( ph -> ch ) $.
    $( Inference joining the consequents of two premises.  (Contributed by NM,
       5-Aug-1993.) $)
    jc $p |- ( ph -> -. ( ps -> -. ch ) ) $=
      wph wps wch wps wch wn wi wn jc.1 jc.2 wps wch pm3.2im sylc $.
  $}

  ${
    impi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2013.) $)
    impi $p |- ( -. ( ph -> -. ps ) -> ch ) $=
      wch wph wps wn wi wph wps wch impi.1 con3rr3 con1i $.
  $}

  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    $( An exportation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.) $)
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      wph wps wph wps wn wi wn wch wph wps pm3.2im expi.1 syl6 $.
  $}

  $( Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $=
    wph wps wps wph wps idd impi $.

  $( Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 21-Jul-2012.) $)
  simplim $p |- ( -. ( ph -> ps ) -> ph ) $=
    wph wph wps wi wph wps pm2.21 con1i $.

  $( Theorem *2.5 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 9-Oct-2012.) $)
  pm2.5 $p |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $=
    wph wps wi wn wph wps wph wps simplim pm2.24d $.

  $( Theorem *2.51 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $=
    wph wps wi wn wps wn wph wps wph wps wi wps wph ax-1 con3i a1d $.

  $( Theorem *2.521 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)
  pm2.521 $p |- ( -. ( ph -> ps ) -> ( ps -> ph ) ) $=
    wph wps wi wn wph wps wph wps simplim a1d $.

  $( Theorem *2.52 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)
  pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $=
    wph wps wi wn wps wph wph wps pm2.521 con3d $.

  $( Exportation theorem expressed with primitive connectives.  (Contributed by
     NM, 5-Aug-1993.) $)
  expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    wph wph wps wn wi wn wch wi wps wch wi wph wps wph wps wn wi wn wch wph wps
    pm3.2im imim1d com12 $.

  $( Importation theorem expressed with primitive connectives.  (Contributed by
     NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen, 20-Jul-2013.) $)
  impt $p |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ) $=
    wph wps wch wi wi wph wps wn wi wn wps wch wph wps simprim wph wps wn wi wn
    wph wps wch wi wph wps wn simplim imim1i mpdi $.

  ${
    pm2.61d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduction eliminating an antecedent.  (Contributed by NM, 27-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)
    pm2.61d $p |- ( ph -> ch ) $=
      wph wch wph wch wn wps wch wph wps wch pm2.61d.2 con1d pm2.61d.1 syld
      pm2.18d $.
  $}

  ${
    pm2.61d1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d1.2 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM,
       15-Jul-2005.) $)
    pm2.61d1 $p |- ( ph -> ch ) $=
      wph wps wch pm2.61d1.1 wps wn wch wi wph pm2.61d1.2 a1i pm2.61d $.
  $}

  ${
    pm2.61d2.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    pm2.61d2.2 $e |- ( ps -> ch ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM,
       18-Aug-1993.) $)
    pm2.61d2 $p |- ( ph -> ch ) $=
      wph wps wch wps wch wi wph pm2.61d2.2 a1i pm2.61d2.1 pm2.61d $.
  $}

  ${
    ja.1 $e |- ( -. ph -> ch ) $.
    ja.2 $e |- ( ps -> ch ) $.
    $( Inference joining the antecedents of two premises.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 19-Feb-2008.) $)
    ja $p |- ( ( ph -> ps ) -> ch ) $=
      wph wps wi wph wch wps wch wph ja.2 imim2i ja.1 pm2.61d1 $.
  $}

  ${
    jad.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    jad.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction form of ~ ja .  (Contributed by Scott Fenton, 13-Dec-2010.)
       (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    jad $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      wps wch wi wph wth wps wch wph wth wi wph wps wn wth jad.1 com12 wph wch
      wth jad.2 com12 ja com12 $.
  $}

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 10-May-2013.) $)
  jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $=
    wph wn wph wps wi wch wph wps pm2.21 imim1i $.

  ${
    pm2.61i.1 $e |- ( ph -> ps ) $.
    pm2.61i.2 $e |- ( -. ph -> ps ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)
    pm2.61i $p |- ps $=
      wph wph wi wps wph id wph wph wps pm2.61i.2 pm2.61i.1 ja ax-mp $.
  $}

  ${
    pm2.61ii.1 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    pm2.61ii.2 $e |- ( ph -> ch ) $.
    pm2.61ii.3 $e |- ( ps -> ch ) $.
    $( Inference eliminating two antecedents.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
    pm2.61ii $p |- ch $=
      wph wch pm2.61ii.2 wph wn wps wch pm2.61ii.1 pm2.61ii.3 pm2.61d2 pm2.61i
      $.
  $}

  ${
    pm2.61nii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61nii.2 $e |- ( -. ph -> ch ) $.
    pm2.61nii.3 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating two antecedents.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Wolf Lammen, 13-Nov-2012.) $)
    pm2.61nii $p |- ch $=
      wph wch wph wps wch pm2.61nii.1 pm2.61nii.3 pm2.61d1 pm2.61nii.2 pm2.61i
      $.
  $}

  ${
    pm2.61iii.1 $e |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) ) $.
    pm2.61iii.2 $e |- ( ph -> th ) $.
    pm2.61iii.3 $e |- ( ps -> th ) $.
    pm2.61iii.4 $e |- ( ch -> th ) $.
    $( Inference eliminating three antecedents.  (Contributed by NM,
       2-Jan-2002.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    pm2.61iii $p |- th $=
      wch wth pm2.61iii.4 wph wps wch wn wth wi pm2.61iii.1 wph wth wch wn
      pm2.61iii.2 a1d wps wth wch wn pm2.61iii.3 a1d pm2.61ii pm2.61i $.
  $}

  $( Reductio ad absurdum.  Theorem *2.01 of [WhiteheadRussell] p. 100.
     (Contributed by NM, 18-Aug-1993.)  (Proof shortened by O'Cat,
     21-Nov-2008.)  (Proof shortened by Wolf Lammen, 31-Oct-2012.) $)
  pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    wph wph wn wph wn wph wn id wph wn id ja $.

  ${
    pm2.01d.1 $e |- ( ph -> ( ps -> -. ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Wolf Lammen, 5-Mar-2013.) $)
    pm2.01d $p |- ( ph -> -. ps ) $=
      wph wps wps wn pm2.01d.1 wps wn id pm2.61d1 $.
  $}

  $( Theorem *2.6 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.6 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    wph wn wps wi wph wps wps wph wn wps wi id wph wn wps wi wps idd jad $.

  $( Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
     antecedent.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 22-Sep-2013.) $)
  pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $=
    wph wn wps wi wph wps wi wps wph wps pm2.6 com12 $.

  $( Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     8-Mar-2013.) $)
  pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $=
    wph wps wi wph wps wn wph wn wph wps wi wph wn idd wph wps con3 jad $.

  ${
    pm2.65i.1 $e |- ( ph -> ps ) $.
    pm2.65i.2 $e |- ( ph -> -. ps ) $.
    $( Inference rule for proof by contradiction.  (Contributed by NM,
       18-May-1994.)  (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
    pm2.65i $p |- -. ph $=
      wps wph wn wph wps pm2.65i.2 con2i wph wps pm2.65i.1 con3i pm2.61i $.
  $}

  ${
    pm2.65d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.65d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Deduction rule for proof by contradiction.  (Contributed by NM,
       26-Jun-1994.)  (Proof shortened by Wolf Lammen, 26-May-2013.) $)
    pm2.65d $p |- ( ph -> -. ps ) $=
      wph wps wph wps wch wps pm2.65d.2 pm2.65d.1 nsyld pm2.01d $.
  $}

  ${
    mto.1 $e |- -. ps $.
    mto.2 $e |- ( ph -> ps ) $.
    $( The rule of modus tollens.  The rule says, "if ` ps ` is not true, and
       ` ph ` implies ` ps ` , then ` ps ` must also be not true."  Modus
       tollens is short for "modus tollendo tollens," a Latin phrase that means
       "the mood that by denying affirms" [Sanford] p. 39.  It is also called
       denying the consequent.  Modus tollens is closely related to modus
       ponens ~ ax-mp .  (Contributed by NM, 19-Aug-1993.)  (Proof shortened by
       Wolf Lammen, 11-Sep-2013.) $)
    mto $p |- -. ph $=
      wph wps mto.2 wps wn wph mto.1 a1i pm2.65i $.
  $}

  ${
    mtod.1 $e |- ( ph -> -. ch ) $.
    mtod.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 3-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 11-Sep-2013.) $)
    mtod $p |- ( ph -> -. ps ) $=
      wph wps wch mtod.2 wph wch wn wps mtod.1 a1d pm2.65d $.
  $}

  ${
    mtoi.1 $e |- -. ch $.
    mtoi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 5-Jul-1994.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mtoi $p |- ( ph -> -. ps ) $=
      wph wps wch wch wn wph mtoi.1 a1i mtoi.2 mtod $.
  $}

  ${
    mt2.1 $e |- ps $.
    mt2.2 $e |- ( ph -> -. ps ) $.
    $( A rule similar to modus tollens.  (Contributed by NM, 19-Aug-1993.)
       (Proof shortened by Wolf Lammen, 10-Sep-2013.) $)
    mt2 $p |- -. ph $=
      wph wps wps wph mt2.1 a1i mt2.2 pm2.65i $.
  $}

  ${
    mt3.1 $e |- -. ps $.
    mt3.2 $e |- ( -. ph -> ps ) $.
    $( A rule similar to modus tollens.  (Contributed by NM, 18-May-1994.)
       (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
    mt3 $p |- ph $=
      wph wph wn wps mt3.1 mt3.2 mto notnotri $.
  $}

  $( Peirce's axiom.  This odd-looking theorem is the "difference" between an
     intuitionistic system of propositional calculus and a classical system and
     is not accepted by intuitionists.  When Peirce's axiom is added to an
     intuitionistic system, the system becomes equivalent to our classical
     system ~ ax-1 through ~ ax-3 .  A curious fact about this theorem is that
     it requires ~ ax-3 for its proof even though the result has no negation
     connectives in it.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 9-Oct-2012.) $)
  peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    wph wps wi wph wph wph wps simplim wph id ja $.

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  For a version not using ~ ax-3 , see ~ loolinALT .
     (Contributed by O'Cat, 12-Aug-2004.)  (Proof shortened by Wolf Lammen,
     2-Nov-2012.) $)
  loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    wph wps wi wps wph wi wps wph wi wph wps pm2.521 wps wph wi id ja $.

  $( The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  Using ~ dfor2 , we can see that this essentially
     expresses "disjunction commutes."  Theorem *2.69 of [WhiteheadRussell]
     p. 108.  (Contributed by NM, 12-Aug-2004.) $)
  looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    wph wps wi wps wi wps wph wi wph wps wi wph wi wph wph wps wi wps wph imim1
    wph wps peirce syl6 $.

  $( Theorem used to justify definition of biconditional ~ df-bi .
     (Contributed by NM, 11-May-1999.)  (Proof shortened by Josh Purinton,
     29-Dec-2000.) $)
  bijust $p |- -. ( ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
               -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) ) $=
    wph wps wi wps wph wi wn wi wn wph wps wi wps wph wi wn wi wn wi wph wps wi
    wps wph wi wn wi wn wph wps wi wps wph wi wn wi wn wi wn wi wph wps wi wps
    wph wi wn wi wn wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn
    wi wn id wph wps wi wps wph wi wn wi wn wph wps wi wps wph wi wn wi wn wi
    pm2.01 mt2 $.


