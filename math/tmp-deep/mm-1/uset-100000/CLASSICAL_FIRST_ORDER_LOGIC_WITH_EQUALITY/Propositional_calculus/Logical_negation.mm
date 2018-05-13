$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_implication.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical negation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section makes our first use of the third axiom of propositional
  calculus, ~ ax-3 .

$)

$(Deduction derived from axiom ~ ax-3 .  (Contributed by NM,
       26-Mar-1995.) $)

${
	$v ph ps ch  $.
	f0_con4d $f wff ph $.
	f1_con4d $f wff ps $.
	f2_con4d $f wff ch $.
	e0_con4d $e |- ( ph -> ( -. ps -> -. ch ) ) $.
	p_con4d $p |- ( ph -> ( ch -> ps ) ) $= e0_con4d f1_con4d f2_con4d a_ax-3 f0_con4d f1_con4d a_wn f2_con4d a_wn a_wi f2_con4d f1_con4d a_wi p_syl $.
$}

$(A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by NM, 10-Feb-1996.) $)

${
	$v ph ps ch  $.
	f0_pm2.21d $f wff ph $.
	f1_pm2.21d $f wff ps $.
	f2_pm2.21d $f wff ch $.
	e0_pm2.21d $e |- ( ph -> -. ps ) $.
	p_pm2.21d $p |- ( ph -> ( ps -> ch ) ) $= e0_pm2.21d f0_pm2.21d f1_pm2.21d a_wn f2_pm2.21d a_wn p_a1d f0_pm2.21d f2_pm2.21d f1_pm2.21d p_con4d $.
$}

$(A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)

${
	$v ph ps ch  $.
	f0_pm2.21dd $f wff ph $.
	f1_pm2.21dd $f wff ps $.
	f2_pm2.21dd $f wff ch $.
	e0_pm2.21dd $e |- ( ph -> ps ) $.
	e1_pm2.21dd $e |- ( ph -> -. ps ) $.
	p_pm2.21dd $p |- ( ph -> ch ) $= e0_pm2.21dd e1_pm2.21dd f0_pm2.21dd f1_pm2.21dd f2_pm2.21dd p_pm2.21d f0_pm2.21dd f1_pm2.21dd f2_pm2.21dd p_mpd $.
$}

$(From a wff and its negation, anything is true.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 14-Sep-2012.) $)

${
	$v ph ps  $.
	f0_pm2.21 $f wff ph $.
	f1_pm2.21 $f wff ps $.
	p_pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $= f0_pm2.21 a_wn p_id f0_pm2.21 a_wn f0_pm2.21 f1_pm2.21 p_pm2.21d $.
$}

$(Theorem *2.24 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.24 $f wff ph $.
	f1_pm2.24 $f wff ps $.
	p_pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $= f0_pm2.24 f1_pm2.24 p_pm2.21 f0_pm2.24 a_wn f0_pm2.24 f1_pm2.24 p_com12 $.
$}

$(Proof by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.  Also
     called the Law of Clavius.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph  $.
	f0_pm2.18 $f wff ph $.
	p_pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $= f0_pm2.18 f0_pm2.18 a_wn f0_pm2.18 a_wi a_wn p_pm2.21 f0_pm2.18 a_wn f0_pm2.18 f0_pm2.18 a_wn f0_pm2.18 a_wi a_wn p_a2i f0_pm2.18 a_wn f0_pm2.18 a_wi f0_pm2.18 f0_pm2.18 a_wn f0_pm2.18 a_wi p_con4d f0_pm2.18 a_wn f0_pm2.18 a_wi f0_pm2.18 p_pm2.43i $.
$}

$(Deduction based on reductio ad absurdum.  (Contributed by FL,
       12-Jul-2009.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)

${
	$v ph ps  $.
	f0_pm2.18d $f wff ph $.
	f1_pm2.18d $f wff ps $.
	e0_pm2.18d $e |- ( ph -> ( -. ps -> ps ) ) $.
	p_pm2.18d $p |- ( ph -> ps ) $= e0_pm2.18d f1_pm2.18d p_pm2.18 f0_pm2.18d f1_pm2.18d a_wn f1_pm2.18d a_wi f1_pm2.18d p_syl $.
$}

$(Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by David Harvey,
     5-Sep-1999.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)

${
	$v ph  $.
	f0_notnot2 $f wff ph $.
	p_notnot2 $p |- ( -. -. ph -> ph ) $= f0_notnot2 a_wn f0_notnot2 p_pm2.21 f0_notnot2 a_wn a_wn f0_notnot2 p_pm2.18d $.
$}

$(Deduction converting double-negation into the original wff, aka the
       double negation rule.  A translation of natural deduction rule ` -. -. `
       -C, ` _G |- -. -. ps ` => ` _G |- ps ` ; see ~ natded .  This is
       definition NNC in [Pfenning] p. 17.  This rule is valid in classical
       logic (which MPE uses), but not intuitionistic logic.  (Contributed by
       DAW, 8-Feb-2017.) $)

${
	$v ph ps  $.
	f0_notnotrd $f wff ph $.
	f1_notnotrd $f wff ps $.
	e0_notnotrd $e |- ( ph -> -. -. ps ) $.
	p_notnotrd $p |- ( ph -> ps ) $= e0_notnotrd f1_notnotrd p_notnot2 f0_notnotrd f1_notnotrd a_wn a_wn f1_notnotrd p_syl $.
$}

$(Inference from double negation.  (Contributed by NM, 27-Feb-2008.) $)

${
	$v ph  $.
	f0_notnotri $f wff ph $.
	e0_notnotri $e |- -. -. ph $.
	p_notnotri $p |- ph $= e0_notnotri f0_notnotri p_notnot2 f0_notnotri a_wn a_wn f0_notnotri a_ax-mp $.
$}

$(A contraposition deduction.  (Contributed by NM, 19-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_con2d $f wff ph $.
	f1_con2d $f wff ps $.
	f2_con2d $f wff ch $.
	e0_con2d $e |- ( ph -> ( ps -> -. ch ) ) $.
	p_con2d $p |- ( ph -> ( ch -> -. ps ) ) $= f1_con2d p_notnot2 e0_con2d f1_con2d a_wn a_wn f1_con2d f0_con2d f2_con2d a_wn p_syl5 f0_con2d f1_con2d a_wn f2_con2d p_con4d $.
$}

$(Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)

${
	$v ph ps  $.
	f0_con2 $f wff ph $.
	f1_con2 $f wff ps $.
	p_con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $= f0_con2 f1_con2 a_wn a_wi p_id f0_con2 f1_con2 a_wn a_wi f0_con2 f1_con2 p_con2d $.
$}

$(Modus tollens deduction.  (Contributed by NM, 4-Jul-1994.) $)

${
	$v ph ps ch  $.
	f0_mt2d $f wff ph $.
	f1_mt2d $f wff ps $.
	f2_mt2d $f wff ch $.
	e0_mt2d $e |- ( ph -> ch ) $.
	e1_mt2d $e |- ( ph -> ( ps -> -. ch ) ) $.
	p_mt2d $p |- ( ph -> -. ps ) $= e0_mt2d e1_mt2d f0_mt2d f1_mt2d f2_mt2d p_con2d f0_mt2d f2_mt2d f1_mt2d a_wn p_mpd $.
$}

$(Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)

${
	$v ph ps ch  $.
	f0_mt2i $f wff ph $.
	f1_mt2i $f wff ps $.
	f2_mt2i $f wff ch $.
	e0_mt2i $e |- ch $.
	e1_mt2i $e |- ( ph -> ( ps -> -. ch ) ) $.
	p_mt2i $p |- ( ph -> -. ps ) $= e0_mt2i f2_mt2i f0_mt2i p_a1i e1_mt2i f0_mt2i f1_mt2i f2_mt2i p_mt2d $.
$}

$(A negated syllogism inference.  (Contributed by NM, 1-Dec-1995.) $)

${
	$v ph ps ch  $.
	f0_nsyl3 $f wff ph $.
	f1_nsyl3 $f wff ps $.
	f2_nsyl3 $f wff ch $.
	e0_nsyl3 $e |- ( ph -> -. ps ) $.
	e1_nsyl3 $e |- ( ch -> ps ) $.
	p_nsyl3 $p |- ( ch -> -. ph ) $= e1_nsyl3 e0_nsyl3 f0_nsyl3 f1_nsyl3 a_wn a_wi f2_nsyl3 p_a1i f2_nsyl3 f0_nsyl3 f1_nsyl3 p_mt2d $.
$}

$(A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.)  (Proof shortened by Wolf Lammen,
       13-Jun-2013.) $)

${
	$v ph ps  $.
	f0_con2i $f wff ph $.
	f1_con2i $f wff ps $.
	e0_con2i $e |- ( ph -> -. ps ) $.
	p_con2i $p |- ( ps -> -. ph ) $= e0_con2i f1_con2i p_id f0_con2i f1_con2i f1_con2i p_nsyl3 $.
$}

$(A negated syllogism inference.  (Contributed by NM, 31-Dec-1993.)
       (Proof shortened by Wolf Lammen, 2-Mar-2013.) $)

${
	$v ph ps ch  $.
	f0_nsyl $f wff ph $.
	f1_nsyl $f wff ps $.
	f2_nsyl $f wff ch $.
	e0_nsyl $e |- ( ph -> -. ps ) $.
	e1_nsyl $e |- ( ch -> ps ) $.
	p_nsyl $p |- ( ph -> -. ch ) $= e0_nsyl e1_nsyl f0_nsyl f1_nsyl f2_nsyl p_nsyl3 f2_nsyl f0_nsyl p_con2i $.
$}

$(Converse of double negation.  Theorem *2.12 of [WhiteheadRussell] p. 101.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     2-Mar-2013.) $)

${
	$v ph  $.
	f0_notnot1 $f wff ph $.
	p_notnot1 $p |- ( ph -> -. -. ph ) $= f0_notnot1 a_wn p_id f0_notnot1 a_wn f0_notnot1 p_con2i $.
$}

$(Infer double negation.  (Contributed by NM, 27-Feb-2008.) $)

${
	$v ph  $.
	f0_notnoti $f wff ph $.
	e0_notnoti $e |- ph $.
	p_notnoti $p |- -. -. ph $= e0_notnoti f0_notnoti p_notnot1 f0_notnoti f0_notnoti a_wn a_wn a_ax-mp $.
$}

$(A contraposition deduction.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_con1d $f wff ph $.
	f1_con1d $f wff ps $.
	f2_con1d $f wff ch $.
	e0_con1d $e |- ( ph -> ( -. ps -> ch ) ) $.
	p_con1d $p |- ( ph -> ( -. ch -> ps ) ) $= e0_con1d f2_con1d p_notnot1 f0_con1d f1_con1d a_wn f2_con1d f2_con1d a_wn a_wn p_syl6 f0_con1d f1_con1d f2_con1d a_wn p_con4d $.
$}

$(Modus tollens deduction.  (Contributed by NM, 26-Mar-1995.) $)

${
	$v ph ps ch  $.
	f0_mt3d $f wff ph $.
	f1_mt3d $f wff ps $.
	f2_mt3d $f wff ch $.
	e0_mt3d $e |- ( ph -> -. ch ) $.
	e1_mt3d $e |- ( ph -> ( -. ps -> ch ) ) $.
	p_mt3d $p |- ( ph -> ps ) $= e0_mt3d e1_mt3d f0_mt3d f1_mt3d f2_mt3d p_con1d f0_mt3d f2_mt3d a_wn f1_mt3d p_mpd $.
$}

$(Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)

${
	$v ph ps ch  $.
	f0_mt3i $f wff ph $.
	f1_mt3i $f wff ps $.
	f2_mt3i $f wff ch $.
	e0_mt3i $e |- -. ch $.
	e1_mt3i $e |- ( ph -> ( -. ps -> ch ) ) $.
	p_mt3i $p |- ( ph -> ps ) $= e0_mt3i f2_mt3i a_wn f0_mt3i p_a1i e1_mt3i f0_mt3i f1_mt3i f2_mt3i p_mt3d $.
$}

$(A negated syllogism inference.  (Contributed by NM, 26-Jun-1994.) $)

${
	$v ph ps ch  $.
	f0_nsyl2 $f wff ph $.
	f1_nsyl2 $f wff ps $.
	f2_nsyl2 $f wff ch $.
	e0_nsyl2 $e |- ( ph -> -. ps ) $.
	e1_nsyl2 $e |- ( -. ch -> ps ) $.
	p_nsyl2 $p |- ( ph -> ch ) $= e0_nsyl2 e1_nsyl2 f2_nsyl2 a_wn f1_nsyl2 a_wi f0_nsyl2 p_a1i f0_nsyl2 f2_nsyl2 f1_nsyl2 p_mt3d $.
$}

$(Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)

${
	$v ph ps  $.
	f0_con1 $f wff ph $.
	f1_con1 $f wff ps $.
	p_con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $= f0_con1 a_wn f1_con1 a_wi p_id f0_con1 a_wn f1_con1 a_wi f0_con1 f1_con1 p_con1d $.
$}

$(A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.)  (Proof shortened by Wolf Lammen,
       19-Jun-2013.) $)

${
	$v ph ps  $.
	f0_con1i $f wff ph $.
	f1_con1i $f wff ps $.
	e0_con1i $e |- ( -. ph -> ps ) $.
	p_con1i $p |- ( -. ps -> ph ) $= f1_con1i a_wn p_id e0_con1i f1_con1i a_wn f1_con1i f0_con1i p_nsyl2 $.
$}

$(Inference rule derived from axiom ~ ax-3 .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 21-Jun-2013.) $)

${
	$v ph ps  $.
	f0_con4i $f wff ph $.
	f1_con4i $f wff ps $.
	e0_con4i $e |- ( -. ph -> -. ps ) $.
	p_con4i $p |- ( ps -> ph ) $= f1_con4i p_notnot1 e0_con4i f1_con4i f1_con4i a_wn f0_con4i p_nsyl2 $.
$}

$(A contradiction implies anything.  Inference from ~ pm2.21 .
       (Contributed by NM, 16-Sep-1993.) $)

${
	$v ph ps  $.
	f0_pm2.21i $f wff ph $.
	f1_pm2.21i $f wff ps $.
	e0_pm2.21i $e |- -. ph $.
	p_pm2.21i $p |- ( ph -> ps ) $= e0_pm2.21i f0_pm2.21i a_wn f1_pm2.21i a_wn p_a1i f1_pm2.21i f0_pm2.21i p_con4i $.
$}

$(A contradiction implies anything.  Inference from ~ pm2.24 .
       (Contributed by NM, 27-Feb-2008.) $)

${
	$v ph ps  $.
	f0_pm2.24ii $f wff ph $.
	f1_pm2.24ii $f wff ps $.
	e0_pm2.24ii $e |- ph $.
	e1_pm2.24ii $e |- -. ph $.
	p_pm2.24ii $p |- ps $= e0_pm2.24ii e1_pm2.24ii f0_pm2.24ii f1_pm2.24ii p_pm2.21i f0_pm2.24ii f1_pm2.24ii a_ax-mp $.
$}

$(A contraposition deduction.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_con3d $f wff ph $.
	f1_con3d $f wff ps $.
	f2_con3d $f wff ch $.
	e0_con3d $e |- ( ph -> ( ps -> ch ) ) $.
	p_con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $= f1_con3d p_notnot2 e0_con3d f1_con3d a_wn a_wn f1_con3d f0_con3d f2_con3d p_syl5 f0_con3d f1_con3d a_wn f2_con3d p_con1d $.
$}

$(Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Feb-2013.) $)

${
	$v ph ps  $.
	f0_con3 $f wff ph $.
	f1_con3 $f wff ps $.
	p_con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $= f0_con3 f1_con3 a_wi p_id f0_con3 f1_con3 a_wi f0_con3 f1_con3 p_con3d $.
$}

$(A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 20-Jun-2013.) $)

${
	$v ph ps  $.
	f0_con3i $f wff ph $.
	f1_con3i $f wff ps $.
	e0_con3i $e |- ( ph -> ps ) $.
	p_con3i $p |- ( -. ps -> -. ph ) $= f1_con3i a_wn p_id e0_con3i f1_con3i a_wn f1_con3i f0_con3i p_nsyl $.
$}

$(Rotate through consequent right.  (Contributed by Wolf Lammen,
       3-Nov-2013.) $)

${
	$v ph ps ch  $.
	f0_con3rr3 $f wff ph $.
	f1_con3rr3 $f wff ps $.
	f2_con3rr3 $f wff ch $.
	e0_con3rr3 $e |- ( ph -> ( ps -> ch ) ) $.
	p_con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $= e0_con3rr3 f0_con3rr3 f1_con3rr3 f2_con3rr3 p_con3d f0_con3rr3 f2_con3rr3 a_wn f1_con3rr3 a_wn p_com12 $.
$}

$(The rule of modus tollens.  (Contributed by Wolf Lammen,
       12-May-2013.) $)

${
	$v ph ps  $.
	f0_mt4 $f wff ph $.
	f1_mt4 $f wff ps $.
	e0_mt4 $e |- ph $.
	e1_mt4 $e |- ( -. ps -> -. ph ) $.
	p_mt4 $p |- ps $= e0_mt4 e1_mt4 f1_mt4 f0_mt4 p_con4i f0_mt4 f1_mt4 a_ax-mp $.
$}

$(Modus tollens deduction.  (Contributed by NM, 9-Jun-2006.) $)

${
	$v ph ps ch  $.
	f0_mt4d $f wff ph $.
	f1_mt4d $f wff ps $.
	f2_mt4d $f wff ch $.
	e0_mt4d $e |- ( ph -> ps ) $.
	e1_mt4d $e |- ( ph -> ( -. ch -> -. ps ) ) $.
	p_mt4d $p |- ( ph -> ch ) $= e0_mt4d e1_mt4d f0_mt4d f2_mt4d f1_mt4d p_con4d f0_mt4d f1_mt4d f2_mt4d p_mpd $.
$}

$(Modus tollens inference.  (Contributed by Wolf Lammen, 12-May-2013.) $)

${
	$v ph ps ch  $.
	f0_mt4i $f wff ph $.
	f1_mt4i $f wff ps $.
	f2_mt4i $f wff ch $.
	e0_mt4i $e |- ch $.
	e1_mt4i $e |- ( ph -> ( -. ps -> -. ch ) ) $.
	p_mt4i $p |- ( ph -> ps ) $= e0_mt4i f2_mt4i f0_mt4i p_a1i e1_mt4i f0_mt4i f2_mt4i f1_mt4i p_mt4d $.
$}

$(A negated syllogism deduction.  (Contributed by NM, 9-Apr-2005.) $)

${
	$v ph ps ch ta  $.
	f0_nsyld $f wff ph $.
	f1_nsyld $f wff ps $.
	f2_nsyld $f wff ch $.
	f3_nsyld $f wff ta $.
	e0_nsyld $e |- ( ph -> ( ps -> -. ch ) ) $.
	e1_nsyld $e |- ( ph -> ( ta -> ch ) ) $.
	p_nsyld $p |- ( ph -> ( ps -> -. ta ) ) $= e0_nsyld e1_nsyld f0_nsyld f3_nsyld f2_nsyld p_con3d f0_nsyld f1_nsyld f2_nsyld a_wn f3_nsyld a_wn p_syld $.
$}

$(A negated syllogism inference.  (Contributed by NM, 3-May-1994.) $)

${
	$v ph ps ch th  $.
	f0_nsyli $f wff ph $.
	f1_nsyli $f wff ps $.
	f2_nsyli $f wff ch $.
	f3_nsyli $f wff th $.
	e0_nsyli $e |- ( ph -> ( ps -> ch ) ) $.
	e1_nsyli $e |- ( th -> -. ch ) $.
	p_nsyli $p |- ( ph -> ( th -> -. ps ) ) $= e1_nsyli e0_nsyli f0_nsyli f1_nsyli f2_nsyli p_con3d f3_nsyli f2_nsyli a_wn f0_nsyli f1_nsyli a_wn p_syl5 $.
$}

$(A negated syllogism inference.  (Contributed by NM, 15-Feb-1996.) $)

${
	$v ph ps ch  $.
	f0_nsyl4 $f wff ph $.
	f1_nsyl4 $f wff ps $.
	f2_nsyl4 $f wff ch $.
	e0_nsyl4 $e |- ( ph -> ps ) $.
	e1_nsyl4 $e |- ( -. ph -> ch ) $.
	p_nsyl4 $p |- ( -. ch -> ps ) $= e1_nsyl4 f0_nsyl4 f2_nsyl4 p_con1i e0_nsyl4 f2_nsyl4 a_wn f0_nsyl4 f1_nsyl4 p_syl $.
$}

$(Deduction version of ~ pm2.24 .  (Contributed by NM, 30-Jan-2006.) $)

${
	$v ph ps ch  $.
	f0_pm2.24d $f wff ph $.
	f1_pm2.24d $f wff ps $.
	f2_pm2.24d $f wff ch $.
	e0_pm2.24d $e |- ( ph -> ps ) $.
	p_pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $= e0_pm2.24d f0_pm2.24d f1_pm2.24d f2_pm2.24d a_wn p_a1d f0_pm2.24d f2_pm2.24d f1_pm2.24d p_con1d $.
$}

$(Inference version of ~ pm2.24 .  (Contributed by NM, 20-Aug-2001.) $)

${
	$v ph ps  $.
	f0_pm2.24i $f wff ph $.
	f1_pm2.24i $f wff ps $.
	e0_pm2.24i $e |- ph $.
	p_pm2.24i $p |- ( -. ph -> ps ) $= e0_pm2.24i f0_pm2.24i f1_pm2.24i a_wn p_a1i f1_pm2.24i f0_pm2.24i p_con1i $.
$}

$(Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Josh
     Purinton, 29-Dec-2000.) $)

${
	$v ph ps  $.
	f0_pm3.2im $f wff ph $.
	f1_pm3.2im $f wff ps $.
	p_pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $= f0_pm3.2im f1_pm3.2im a_wn p_pm2.27 f0_pm3.2im f0_pm3.2im f1_pm3.2im a_wn a_wi f1_pm3.2im p_con2d $.
$}

$(Theorem 8 of [Margaris] p. 60.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Josh Purinton, 29-Dec-2000.) $)

${
	$v ph ps  $.
	f0_mth8 $f wff ph $.
	f1_mth8 $f wff ps $.
	p_mth8 $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $= f0_mth8 f1_mth8 p_pm2.27 f0_mth8 f0_mth8 f1_mth8 a_wi f1_mth8 p_con3d $.
$}

$(Inference joining the consequents of two premises.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_jc $f wff ph $.
	f1_jc $f wff ps $.
	f2_jc $f wff ch $.
	e0_jc $e |- ( ph -> ps ) $.
	e1_jc $e |- ( ph -> ch ) $.
	p_jc $p |- ( ph -> -. ( ps -> -. ch ) ) $= e0_jc e1_jc f1_jc f2_jc p_pm3.2im f0_jc f1_jc f2_jc f1_jc f2_jc a_wn a_wi a_wn p_sylc $.
$}

$(An importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2013.) $)

${
	$v ph ps ch  $.
	f0_impi $f wff ph $.
	f1_impi $f wff ps $.
	f2_impi $f wff ch $.
	e0_impi $e |- ( ph -> ( ps -> ch ) ) $.
	p_impi $p |- ( -. ( ph -> -. ps ) -> ch ) $= e0_impi f0_impi f1_impi f2_impi p_con3rr3 f2_impi f0_impi f1_impi a_wn a_wi p_con1i $.
$}

$(An exportation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.) $)

${
	$v ph ps ch  $.
	f0_expi $f wff ph $.
	f1_expi $f wff ps $.
	f2_expi $f wff ch $.
	e0_expi $e |- ( -. ( ph -> -. ps ) -> ch ) $.
	p_expi $p |- ( ph -> ( ps -> ch ) ) $= f0_expi f1_expi p_pm3.2im e0_expi f0_expi f1_expi f0_expi f1_expi a_wn a_wi a_wn f2_expi p_syl6 $.
$}

$(Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)

${
	$v ph ps  $.
	f0_simprim $f wff ph $.
	f1_simprim $f wff ps $.
	p_simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $= f0_simprim f1_simprim p_idd f0_simprim f1_simprim f1_simprim p_impi $.
$}

$(Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 21-Jul-2012.) $)

${
	$v ph ps  $.
	f0_simplim $f wff ph $.
	f1_simplim $f wff ps $.
	p_simplim $p |- ( -. ( ph -> ps ) -> ph ) $= f0_simplim f1_simplim p_pm2.21 f0_simplim f0_simplim f1_simplim a_wi p_con1i $.
$}

$(Theorem *2.5 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 9-Oct-2012.) $)

${
	$v ph ps  $.
	f0_pm2.5 $f wff ph $.
	f1_pm2.5 $f wff ps $.
	p_pm2.5 $p |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $= f0_pm2.5 f1_pm2.5 p_simplim f0_pm2.5 f1_pm2.5 a_wi a_wn f0_pm2.5 f1_pm2.5 p_pm2.24d $.
$}

$(Theorem *2.51 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.51 $f wff ph $.
	f1_pm2.51 $f wff ps $.
	p_pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $= f1_pm2.51 f0_pm2.51 a_ax-1 f1_pm2.51 f0_pm2.51 f1_pm2.51 a_wi p_con3i f0_pm2.51 f1_pm2.51 a_wi a_wn f1_pm2.51 a_wn f0_pm2.51 p_a1d $.
$}

$(Theorem *2.521 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)

${
	$v ph ps  $.
	f0_pm2.521 $f wff ph $.
	f1_pm2.521 $f wff ps $.
	p_pm2.521 $p |- ( -. ( ph -> ps ) -> ( ps -> ph ) ) $= f0_pm2.521 f1_pm2.521 p_simplim f0_pm2.521 f1_pm2.521 a_wi a_wn f0_pm2.521 f1_pm2.521 p_a1d $.
$}

$(Theorem *2.52 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)

${
	$v ph ps  $.
	f0_pm2.52 $f wff ph $.
	f1_pm2.52 $f wff ps $.
	p_pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $= f0_pm2.52 f1_pm2.52 p_pm2.521 f0_pm2.52 f1_pm2.52 a_wi a_wn f1_pm2.52 f0_pm2.52 p_con3d $.
$}

$(Exportation theorem expressed with primitive connectives.  (Contributed by
     NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_expt $f wff ph $.
	f1_expt $f wff ps $.
	f2_expt $f wff ch $.
	p_expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $= f0_expt f1_expt p_pm3.2im f0_expt f1_expt f0_expt f1_expt a_wn a_wi a_wn f2_expt p_imim1d f0_expt f0_expt f1_expt a_wn a_wi a_wn f2_expt a_wi f1_expt f2_expt a_wi p_com12 $.
$}

$(Importation theorem expressed with primitive connectives.  (Contributed by
     NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen, 20-Jul-2013.) $)

${
	$v ph ps ch  $.
	f0_impt $f wff ph $.
	f1_impt $f wff ps $.
	f2_impt $f wff ch $.
	p_impt $p |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ) $= f0_impt f1_impt p_simprim f0_impt f1_impt a_wn p_simplim f0_impt f1_impt a_wn a_wi a_wn f0_impt f1_impt f2_impt a_wi p_imim1i f0_impt f1_impt f2_impt a_wi a_wi f0_impt f1_impt a_wn a_wi a_wn f1_impt f2_impt p_mpdi $.
$}

$(Deduction eliminating an antecedent.  (Contributed by NM, 27-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)

${
	$v ph ps ch  $.
	f0_pm2.61d $f wff ph $.
	f1_pm2.61d $f wff ps $.
	f2_pm2.61d $f wff ch $.
	e0_pm2.61d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_pm2.61d $e |- ( ph -> ( -. ps -> ch ) ) $.
	p_pm2.61d $p |- ( ph -> ch ) $= e1_pm2.61d f0_pm2.61d f1_pm2.61d f2_pm2.61d p_con1d e0_pm2.61d f0_pm2.61d f2_pm2.61d a_wn f1_pm2.61d f2_pm2.61d p_syld f0_pm2.61d f2_pm2.61d p_pm2.18d $.
$}

$(Inference eliminating an antecedent.  (Contributed by NM,
       15-Jul-2005.) $)

${
	$v ph ps ch  $.
	f0_pm2.61d1 $f wff ph $.
	f1_pm2.61d1 $f wff ps $.
	f2_pm2.61d1 $f wff ch $.
	e0_pm2.61d1 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_pm2.61d1 $e |- ( -. ps -> ch ) $.
	p_pm2.61d1 $p |- ( ph -> ch ) $= e0_pm2.61d1 e1_pm2.61d1 f1_pm2.61d1 a_wn f2_pm2.61d1 a_wi f0_pm2.61d1 p_a1i f0_pm2.61d1 f1_pm2.61d1 f2_pm2.61d1 p_pm2.61d $.
$}

$(Inference eliminating an antecedent.  (Contributed by NM,
       18-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_pm2.61d2 $f wff ph $.
	f1_pm2.61d2 $f wff ps $.
	f2_pm2.61d2 $f wff ch $.
	e0_pm2.61d2 $e |- ( ph -> ( -. ps -> ch ) ) $.
	e1_pm2.61d2 $e |- ( ps -> ch ) $.
	p_pm2.61d2 $p |- ( ph -> ch ) $= e1_pm2.61d2 f1_pm2.61d2 f2_pm2.61d2 a_wi f0_pm2.61d2 p_a1i e0_pm2.61d2 f0_pm2.61d2 f1_pm2.61d2 f2_pm2.61d2 p_pm2.61d $.
$}

$(Inference joining the antecedents of two premises.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 19-Feb-2008.) $)

${
	$v ph ps ch  $.
	f0_ja $f wff ph $.
	f1_ja $f wff ps $.
	f2_ja $f wff ch $.
	e0_ja $e |- ( -. ph -> ch ) $.
	e1_ja $e |- ( ps -> ch ) $.
	p_ja $p |- ( ( ph -> ps ) -> ch ) $= e1_ja f1_ja f2_ja f0_ja p_imim2i e0_ja f0_ja f1_ja a_wi f0_ja f2_ja p_pm2.61d1 $.
$}

$(Deduction form of ~ ja .  (Contributed by Scott Fenton, 13-Dec-2010.)
       (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)

${
	$v ph ps ch th  $.
	f0_jad $f wff ph $.
	f1_jad $f wff ps $.
	f2_jad $f wff ch $.
	f3_jad $f wff th $.
	e0_jad $e |- ( ph -> ( -. ps -> th ) ) $.
	e1_jad $e |- ( ph -> ( ch -> th ) ) $.
	p_jad $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $= e0_jad f0_jad f1_jad a_wn f3_jad p_com12 e1_jad f0_jad f2_jad f3_jad p_com12 f1_jad f2_jad f0_jad f3_jad a_wi p_ja f1_jad f2_jad a_wi f0_jad f3_jad p_com12 $.
$}

$(Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 10-May-2013.) $)

${
	$v ph ps ch  $.
	f0_jarl $f wff ph $.
	f1_jarl $f wff ps $.
	f2_jarl $f wff ch $.
	p_jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $= f0_jarl f1_jarl p_pm2.21 f0_jarl a_wn f0_jarl f1_jarl a_wi f2_jarl p_imim1i $.
$}

$(Inference eliminating an antecedent.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)

${
	$v ph ps  $.
	f0_pm2.61i $f wff ph $.
	f1_pm2.61i $f wff ps $.
	e0_pm2.61i $e |- ( ph -> ps ) $.
	e1_pm2.61i $e |- ( -. ph -> ps ) $.
	p_pm2.61i $p |- ps $= f0_pm2.61i p_id e1_pm2.61i e0_pm2.61i f0_pm2.61i f0_pm2.61i f1_pm2.61i p_ja f0_pm2.61i f0_pm2.61i a_wi f1_pm2.61i a_ax-mp $.
$}

$(Inference eliminating two antecedents.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)

${
	$v ph ps ch  $.
	f0_pm2.61ii $f wff ph $.
	f1_pm2.61ii $f wff ps $.
	f2_pm2.61ii $f wff ch $.
	e0_pm2.61ii $e |- ( -. ph -> ( -. ps -> ch ) ) $.
	e1_pm2.61ii $e |- ( ph -> ch ) $.
	e2_pm2.61ii $e |- ( ps -> ch ) $.
	p_pm2.61ii $p |- ch $= e1_pm2.61ii e0_pm2.61ii e2_pm2.61ii f0_pm2.61ii a_wn f1_pm2.61ii f2_pm2.61ii p_pm2.61d2 f0_pm2.61ii f2_pm2.61ii p_pm2.61i $.
$}

$(Inference eliminating two antecedents.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Wolf Lammen, 13-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_pm2.61nii $f wff ph $.
	f1_pm2.61nii $f wff ps $.
	f2_pm2.61nii $f wff ch $.
	e0_pm2.61nii $e |- ( ph -> ( ps -> ch ) ) $.
	e1_pm2.61nii $e |- ( -. ph -> ch ) $.
	e2_pm2.61nii $e |- ( -. ps -> ch ) $.
	p_pm2.61nii $p |- ch $= e0_pm2.61nii e2_pm2.61nii f0_pm2.61nii f1_pm2.61nii f2_pm2.61nii p_pm2.61d1 e1_pm2.61nii f0_pm2.61nii f2_pm2.61nii p_pm2.61i $.
$}

$(Inference eliminating three antecedents.  (Contributed by NM,
       2-Jan-2002.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)

${
	$v ph ps ch th  $.
	f0_pm2.61iii $f wff ph $.
	f1_pm2.61iii $f wff ps $.
	f2_pm2.61iii $f wff ch $.
	f3_pm2.61iii $f wff th $.
	e0_pm2.61iii $e |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) ) $.
	e1_pm2.61iii $e |- ( ph -> th ) $.
	e2_pm2.61iii $e |- ( ps -> th ) $.
	e3_pm2.61iii $e |- ( ch -> th ) $.
	p_pm2.61iii $p |- th $= e3_pm2.61iii e0_pm2.61iii e1_pm2.61iii f0_pm2.61iii f3_pm2.61iii f2_pm2.61iii a_wn p_a1d e2_pm2.61iii f1_pm2.61iii f3_pm2.61iii f2_pm2.61iii a_wn p_a1d f0_pm2.61iii f1_pm2.61iii f2_pm2.61iii a_wn f3_pm2.61iii a_wi p_pm2.61ii f2_pm2.61iii f3_pm2.61iii p_pm2.61i $.
$}

$(Reductio ad absurdum.  Theorem *2.01 of [WhiteheadRussell] p. 100.
     (Contributed by NM, 18-Aug-1993.)  (Proof shortened by O'Cat,
     21-Nov-2008.)  (Proof shortened by Wolf Lammen, 31-Oct-2012.) $)

${
	$v ph  $.
	f0_pm2.01 $f wff ph $.
	p_pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $= f0_pm2.01 a_wn p_id f0_pm2.01 a_wn p_id f0_pm2.01 f0_pm2.01 a_wn f0_pm2.01 a_wn p_ja $.
$}

$(Deduction based on reductio ad absurdum.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Wolf Lammen, 5-Mar-2013.) $)

${
	$v ph ps  $.
	f0_pm2.01d $f wff ph $.
	f1_pm2.01d $f wff ps $.
	e0_pm2.01d $e |- ( ph -> ( ps -> -. ps ) ) $.
	p_pm2.01d $p |- ( ph -> -. ps ) $= e0_pm2.01d f1_pm2.01d a_wn p_id f0_pm2.01d f1_pm2.01d f1_pm2.01d a_wn p_pm2.61d1 $.
$}

$(Theorem *2.6 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps  $.
	f0_pm2.6 $f wff ph $.
	f1_pm2.6 $f wff ps $.
	p_pm2.6 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $= f0_pm2.6 a_wn f1_pm2.6 a_wi p_id f0_pm2.6 a_wn f1_pm2.6 a_wi f1_pm2.6 p_idd f0_pm2.6 a_wn f1_pm2.6 a_wi f0_pm2.6 f1_pm2.6 f1_pm2.6 p_jad $.
$}

$(Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
     antecedent.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 22-Sep-2013.) $)

${
	$v ph ps  $.
	f0_pm2.61 $f wff ph $.
	f1_pm2.61 $f wff ps $.
	p_pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $= f0_pm2.61 f1_pm2.61 p_pm2.6 f0_pm2.61 a_wn f1_pm2.61 a_wi f0_pm2.61 f1_pm2.61 a_wi f1_pm2.61 p_com12 $.
$}

$(Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     8-Mar-2013.) $)

${
	$v ph ps  $.
	f0_pm2.65 $f wff ph $.
	f1_pm2.65 $f wff ps $.
	p_pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $= f0_pm2.65 f1_pm2.65 a_wi f0_pm2.65 a_wn p_idd f0_pm2.65 f1_pm2.65 p_con3 f0_pm2.65 f1_pm2.65 a_wi f0_pm2.65 f1_pm2.65 a_wn f0_pm2.65 a_wn p_jad $.
$}

$(Inference rule for proof by contradiction.  (Contributed by NM,
       18-May-1994.)  (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)

${
	$v ph ps  $.
	f0_pm2.65i $f wff ph $.
	f1_pm2.65i $f wff ps $.
	e0_pm2.65i $e |- ( ph -> ps ) $.
	e1_pm2.65i $e |- ( ph -> -. ps ) $.
	p_pm2.65i $p |- -. ph $= e1_pm2.65i f0_pm2.65i f1_pm2.65i p_con2i e0_pm2.65i f0_pm2.65i f1_pm2.65i p_con3i f1_pm2.65i f0_pm2.65i a_wn p_pm2.61i $.
$}

$(Deduction rule for proof by contradiction.  (Contributed by NM,
       26-Jun-1994.)  (Proof shortened by Wolf Lammen, 26-May-2013.) $)

${
	$v ph ps ch  $.
	f0_pm2.65d $f wff ph $.
	f1_pm2.65d $f wff ps $.
	f2_pm2.65d $f wff ch $.
	e0_pm2.65d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_pm2.65d $e |- ( ph -> ( ps -> -. ch ) ) $.
	p_pm2.65d $p |- ( ph -> -. ps ) $= e1_pm2.65d e0_pm2.65d f0_pm2.65d f1_pm2.65d f2_pm2.65d f1_pm2.65d p_nsyld f0_pm2.65d f1_pm2.65d p_pm2.01d $.
$}

$(The rule of modus tollens.  The rule says, "if ` ps ` is not true, and
       ` ph ` implies ` ps ` , then ` ps ` must also be not true."  Modus
       tollens is short for "modus tollendo tollens," a Latin phrase that means
       "the mood that by denying affirms" [Sanford] p. 39.  It is also called
       denying the consequent.  Modus tollens is closely related to modus
       ponens ~ ax-mp .  (Contributed by NM, 19-Aug-1993.)  (Proof shortened by
       Wolf Lammen, 11-Sep-2013.) $)

${
	$v ph ps  $.
	f0_mto $f wff ph $.
	f1_mto $f wff ps $.
	e0_mto $e |- -. ps $.
	e1_mto $e |- ( ph -> ps ) $.
	p_mto $p |- -. ph $= e1_mto e0_mto f1_mto a_wn f0_mto p_a1i f0_mto f1_mto p_pm2.65i $.
$}

$(Modus tollens deduction.  (Contributed by NM, 3-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 11-Sep-2013.) $)

${
	$v ph ps ch  $.
	f0_mtod $f wff ph $.
	f1_mtod $f wff ps $.
	f2_mtod $f wff ch $.
	e0_mtod $e |- ( ph -> -. ch ) $.
	e1_mtod $e |- ( ph -> ( ps -> ch ) ) $.
	p_mtod $p |- ( ph -> -. ps ) $= e1_mtod e0_mtod f0_mtod f2_mtod a_wn f1_mtod p_a1d f0_mtod f1_mtod f2_mtod p_pm2.65d $.
$}

$(Modus tollens inference.  (Contributed by NM, 5-Jul-1994.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)

${
	$v ph ps ch  $.
	f0_mtoi $f wff ph $.
	f1_mtoi $f wff ps $.
	f2_mtoi $f wff ch $.
	e0_mtoi $e |- -. ch $.
	e1_mtoi $e |- ( ph -> ( ps -> ch ) ) $.
	p_mtoi $p |- ( ph -> -. ps ) $= e0_mtoi f2_mtoi a_wn f0_mtoi p_a1i e1_mtoi f0_mtoi f1_mtoi f2_mtoi p_mtod $.
$}

$(A rule similar to modus tollens.  (Contributed by NM, 19-Aug-1993.)
       (Proof shortened by Wolf Lammen, 10-Sep-2013.) $)

${
	$v ph ps  $.
	f0_mt2 $f wff ph $.
	f1_mt2 $f wff ps $.
	e0_mt2 $e |- ps $.
	e1_mt2 $e |- ( ph -> -. ps ) $.
	p_mt2 $p |- -. ph $= e0_mt2 f1_mt2 f0_mt2 p_a1i e1_mt2 f0_mt2 f1_mt2 p_pm2.65i $.
$}

$(A rule similar to modus tollens.  (Contributed by NM, 18-May-1994.)
       (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)

${
	$v ph ps  $.
	f0_mt3 $f wff ph $.
	f1_mt3 $f wff ps $.
	e0_mt3 $e |- -. ps $.
	e1_mt3 $e |- ( -. ph -> ps ) $.
	p_mt3 $p |- ph $= e0_mt3 e1_mt3 f0_mt3 a_wn f1_mt3 p_mto f0_mt3 p_notnotri $.
$}

$(Peirce's axiom.  This odd-looking theorem is the "difference" between an
     intuitionistic system of propositional calculus and a classical system and
     is not accepted by intuitionists.  When Peirce's axiom is added to an
     intuitionistic system, the system becomes equivalent to our classical
     system ~ ax-1 through ~ ax-3 .  A curious fact about this theorem is that
     it requires ~ ax-3 for its proof even though the result has no negation
     connectives in it.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 9-Oct-2012.) $)

${
	$v ph ps  $.
	f0_peirce $f wff ph $.
	f1_peirce $f wff ps $.
	p_peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $= f0_peirce f1_peirce p_simplim f0_peirce p_id f0_peirce f1_peirce a_wi f0_peirce f0_peirce p_ja $.
$}

$(The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  For a version not using ~ ax-3 , see ~ loolinALT .
     (Contributed by O'Cat, 12-Aug-2004.)  (Proof shortened by Wolf Lammen,
     2-Nov-2012.) $)

${
	$v ph ps  $.
	f0_loolin $f wff ph $.
	f1_loolin $f wff ps $.
	p_loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $= f0_loolin f1_loolin p_pm2.521 f1_loolin f0_loolin a_wi p_id f0_loolin f1_loolin a_wi f1_loolin f0_loolin a_wi f1_loolin f0_loolin a_wi p_ja $.
$}

$(The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  Using ~ dfor2 , we can see that this essentially
     expresses "disjunction commutes."  Theorem *2.69 of [WhiteheadRussell]
     p. 108.  (Contributed by NM, 12-Aug-2004.) $)

${
	$v ph ps  $.
	f0_looinv $f wff ph $.
	f1_looinv $f wff ps $.
	p_looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $= f0_looinv f1_looinv a_wi f1_looinv f0_looinv p_imim1 f0_looinv f1_looinv p_peirce f0_looinv f1_looinv a_wi f1_looinv a_wi f1_looinv f0_looinv a_wi f0_looinv f1_looinv a_wi f0_looinv a_wi f0_looinv p_syl6 $.
$}

$(Theorem used to justify definition of biconditional ~ df-bi .
     (Contributed by NM, 11-May-1999.)  (Proof shortened by Josh Purinton,
     29-Dec-2000.) $)

${
	$v ph ps  $.
	f0_bijust $f wff ph $.
	f1_bijust $f wff ps $.
	p_bijust $p |- -. ( ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) ) $= f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn p_id f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn a_wi p_pm2.01 f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn a_wi f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn a_wi a_wn a_wi f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn f0_bijust f1_bijust a_wi f1_bijust f0_bijust a_wi a_wn a_wi a_wn a_wi p_mt2 $.
$}


