$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_implication.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical negation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section makes our first use of the third axiom of propositional
  calculus, ~ ax-3 .

$)
$( Deduction derived from axiom ~ ax-3 .  (Contributed by NM,
       26-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fcon4d_0 $f wff ph $.
	fcon4d_1 $f wff ps $.
	fcon4d_2 $f wff ch $.
	econ4d_0 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
	con4d $p |- ( ph -> ( ch -> ps ) ) $= fcon4d_0 fcon4d_1 wn fcon4d_2 wn wi fcon4d_2 fcon4d_1 wi econ4d_0 fcon4d_1 fcon4d_2 ax-3 syl $.
$}
$( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by NM, 10-Feb-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.21d_0 $f wff ph $.
	fpm2.21d_1 $f wff ps $.
	fpm2.21d_2 $f wff ch $.
	epm2.21d_0 $e |- ( ph -> -. ps ) $.
	pm2.21d $p |- ( ph -> ( ps -> ch ) ) $= fpm2.21d_0 fpm2.21d_2 fpm2.21d_1 fpm2.21d_0 fpm2.21d_1 wn fpm2.21d_2 wn epm2.21d_0 a1d con4d $.
$}
$( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.21dd_0 $f wff ph $.
	fpm2.21dd_1 $f wff ps $.
	fpm2.21dd_2 $f wff ch $.
	epm2.21dd_0 $e |- ( ph -> ps ) $.
	epm2.21dd_1 $e |- ( ph -> -. ps ) $.
	pm2.21dd $p |- ( ph -> ch ) $= fpm2.21dd_0 fpm2.21dd_1 fpm2.21dd_2 epm2.21dd_0 fpm2.21dd_0 fpm2.21dd_1 fpm2.21dd_2 epm2.21dd_1 pm2.21d mpd $.
$}
$( From a wff and its negation, anything is true.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 14-Sep-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm2.21_0 $f wff ph $.
	fpm2.21_1 $f wff ps $.
	pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $= fpm2.21_0 wn fpm2.21_0 fpm2.21_1 fpm2.21_0 wn id pm2.21d $.
$}
$( Theorem *2.24 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.24_0 $f wff ph $.
	fpm2.24_1 $f wff ps $.
	pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $= fpm2.24_0 wn fpm2.24_0 fpm2.24_1 fpm2.24_0 fpm2.24_1 pm2.21 com12 $.
$}
$( Proof by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.  Also
     called the Law of Clavius.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	fpm2.18_0 $f wff ph $.
	pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $= fpm2.18_0 wn fpm2.18_0 wi fpm2.18_0 fpm2.18_0 wn fpm2.18_0 wi fpm2.18_0 fpm2.18_0 wn fpm2.18_0 wi fpm2.18_0 wn fpm2.18_0 fpm2.18_0 wn fpm2.18_0 wi wn fpm2.18_0 fpm2.18_0 wn fpm2.18_0 wi wn pm2.21 a2i con4d pm2.43i $.
$}
$( Deduction based on reductio ad absurdum.  (Contributed by FL,
       12-Jul-2009.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
${
	$v ph $.
	$v ps $.
	fpm2.18d_0 $f wff ph $.
	fpm2.18d_1 $f wff ps $.
	epm2.18d_0 $e |- ( ph -> ( -. ps -> ps ) ) $.
	pm2.18d $p |- ( ph -> ps ) $= fpm2.18d_0 fpm2.18d_1 wn fpm2.18d_1 wi fpm2.18d_1 epm2.18d_0 fpm2.18d_1 pm2.18 syl $.
$}
$( Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by David Harvey,
     5-Sep-1999.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
${
	$v ph $.
	fnotnot2_0 $f wff ph $.
	notnot2 $p |- ( -. -. ph -> ph ) $= fnotnot2_0 wn wn fnotnot2_0 fnotnot2_0 wn fnotnot2_0 pm2.21 pm2.18d $.
$}
$( Deduction converting double-negation into the original wff, aka the
       double negation rule.  A translation of natural deduction rule ` -. -. `
       -C, ` _G |- -. -. ps ` => ` _G |- ps ` ; see ~ natded .  This is
       definition NNC in [Pfenning] p. 17.  This rule is valid in classical
       logic (which MPE uses), but not intuitionistic logic.  (Contributed by
       DAW, 8-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	fnotnotrd_0 $f wff ph $.
	fnotnotrd_1 $f wff ps $.
	enotnotrd_0 $e |- ( ph -> -. -. ps ) $.
	notnotrd $p |- ( ph -> ps ) $= fnotnotrd_0 fnotnotrd_1 wn wn fnotnotrd_1 enotnotrd_0 fnotnotrd_1 notnot2 syl $.
$}
$( Inference from double negation.  (Contributed by NM, 27-Feb-2008.) $)
${
	$v ph $.
	fnotnotri_0 $f wff ph $.
	enotnotri_0 $e |- -. -. ph $.
	notnotri $p |- ph $= fnotnotri_0 wn wn fnotnotri_0 enotnotri_0 fnotnotri_0 notnot2 ax-mp $.
$}
$( A contraposition deduction.  (Contributed by NM, 19-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fcon2d_0 $f wff ph $.
	fcon2d_1 $f wff ps $.
	fcon2d_2 $f wff ch $.
	econ2d_0 $e |- ( ph -> ( ps -> -. ch ) ) $.
	con2d $p |- ( ph -> ( ch -> -. ps ) ) $= fcon2d_0 fcon2d_1 wn fcon2d_2 fcon2d_1 wn wn fcon2d_1 fcon2d_0 fcon2d_2 wn fcon2d_1 notnot2 econ2d_0 syl5 con4d $.
$}
$( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
${
	$v ph $.
	$v ps $.
	fcon2_0 $f wff ph $.
	fcon2_1 $f wff ps $.
	con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $= fcon2_0 fcon2_1 wn wi fcon2_0 fcon2_1 fcon2_0 fcon2_1 wn wi id con2d $.
$}
$( Modus tollens deduction.  (Contributed by NM, 4-Jul-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmt2d_0 $f wff ph $.
	fmt2d_1 $f wff ps $.
	fmt2d_2 $f wff ch $.
	emt2d_0 $e |- ( ph -> ch ) $.
	emt2d_1 $e |- ( ph -> ( ps -> -. ch ) ) $.
	mt2d $p |- ( ph -> -. ps ) $= fmt2d_0 fmt2d_2 fmt2d_1 wn emt2d_0 fmt2d_0 fmt2d_1 fmt2d_2 emt2d_1 con2d mpd $.
$}
$( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmt2i_0 $f wff ph $.
	fmt2i_1 $f wff ps $.
	fmt2i_2 $f wff ch $.
	emt2i_0 $e |- ch $.
	emt2i_1 $e |- ( ph -> ( ps -> -. ch ) ) $.
	mt2i $p |- ( ph -> -. ps ) $= fmt2i_0 fmt2i_1 fmt2i_2 fmt2i_2 fmt2i_0 emt2i_0 a1i emt2i_1 mt2d $.
$}
$( A negated syllogism inference.  (Contributed by NM, 1-Dec-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnsyl3_0 $f wff ph $.
	fnsyl3_1 $f wff ps $.
	fnsyl3_2 $f wff ch $.
	ensyl3_0 $e |- ( ph -> -. ps ) $.
	ensyl3_1 $e |- ( ch -> ps ) $.
	nsyl3 $p |- ( ch -> -. ph ) $= fnsyl3_2 fnsyl3_0 fnsyl3_1 ensyl3_1 fnsyl3_0 fnsyl3_1 wn wi fnsyl3_2 ensyl3_0 a1i mt2d $.
$}
$( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.)  (Proof shortened by Wolf Lammen,
       13-Jun-2013.) $)
${
	$v ph $.
	$v ps $.
	fcon2i_0 $f wff ph $.
	fcon2i_1 $f wff ps $.
	econ2i_0 $e |- ( ph -> -. ps ) $.
	con2i $p |- ( ps -> -. ph ) $= fcon2i_0 fcon2i_1 fcon2i_1 econ2i_0 fcon2i_1 id nsyl3 $.
$}
$( A negated syllogism inference.  (Contributed by NM, 31-Dec-1993.)
       (Proof shortened by Wolf Lammen, 2-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnsyl_0 $f wff ph $.
	fnsyl_1 $f wff ps $.
	fnsyl_2 $f wff ch $.
	ensyl_0 $e |- ( ph -> -. ps ) $.
	ensyl_1 $e |- ( ch -> ps ) $.
	nsyl $p |- ( ph -> -. ch ) $= fnsyl_2 fnsyl_0 fnsyl_0 fnsyl_1 fnsyl_2 ensyl_0 ensyl_1 nsyl3 con2i $.
$}
$( Converse of double negation.  Theorem *2.12 of [WhiteheadRussell] p. 101.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     2-Mar-2013.) $)
${
	$v ph $.
	fnotnot1_0 $f wff ph $.
	notnot1 $p |- ( ph -> -. -. ph ) $= fnotnot1_0 wn fnotnot1_0 fnotnot1_0 wn id con2i $.
$}
$( Infer double negation.  (Contributed by NM, 27-Feb-2008.) $)
${
	$v ph $.
	fnotnoti_0 $f wff ph $.
	enotnoti_0 $e |- ph $.
	notnoti $p |- -. -. ph $= fnotnoti_0 fnotnoti_0 wn wn enotnoti_0 fnotnoti_0 notnot1 ax-mp $.
$}
$( A contraposition deduction.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fcon1d_0 $f wff ph $.
	fcon1d_1 $f wff ps $.
	fcon1d_2 $f wff ch $.
	econ1d_0 $e |- ( ph -> ( -. ps -> ch ) ) $.
	con1d $p |- ( ph -> ( -. ch -> ps ) ) $= fcon1d_0 fcon1d_1 fcon1d_2 wn fcon1d_0 fcon1d_1 wn fcon1d_2 fcon1d_2 wn wn econ1d_0 fcon1d_2 notnot1 syl6 con4d $.
$}
$( Modus tollens deduction.  (Contributed by NM, 26-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmt3d_0 $f wff ph $.
	fmt3d_1 $f wff ps $.
	fmt3d_2 $f wff ch $.
	emt3d_0 $e |- ( ph -> -. ch ) $.
	emt3d_1 $e |- ( ph -> ( -. ps -> ch ) ) $.
	mt3d $p |- ( ph -> ps ) $= fmt3d_0 fmt3d_2 wn fmt3d_1 emt3d_0 fmt3d_0 fmt3d_1 fmt3d_2 emt3d_1 con1d mpd $.
$}
$( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmt3i_0 $f wff ph $.
	fmt3i_1 $f wff ps $.
	fmt3i_2 $f wff ch $.
	emt3i_0 $e |- -. ch $.
	emt3i_1 $e |- ( ph -> ( -. ps -> ch ) ) $.
	mt3i $p |- ( ph -> ps ) $= fmt3i_0 fmt3i_1 fmt3i_2 fmt3i_2 wn fmt3i_0 emt3i_0 a1i emt3i_1 mt3d $.
$}
$( A negated syllogism inference.  (Contributed by NM, 26-Jun-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnsyl2_0 $f wff ph $.
	fnsyl2_1 $f wff ps $.
	fnsyl2_2 $f wff ch $.
	ensyl2_0 $e |- ( ph -> -. ps ) $.
	ensyl2_1 $e |- ( -. ch -> ps ) $.
	nsyl2 $p |- ( ph -> ch ) $= fnsyl2_0 fnsyl2_2 fnsyl2_1 ensyl2_0 fnsyl2_2 wn fnsyl2_1 wi fnsyl2_0 ensyl2_1 a1i mt3d $.
$}
$( Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
${
	$v ph $.
	$v ps $.
	fcon1_0 $f wff ph $.
	fcon1_1 $f wff ps $.
	con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $= fcon1_0 wn fcon1_1 wi fcon1_0 fcon1_1 fcon1_0 wn fcon1_1 wi id con1d $.
$}
$( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.)  (Proof shortened by Wolf Lammen,
       19-Jun-2013.) $)
${
	$v ph $.
	$v ps $.
	fcon1i_0 $f wff ph $.
	fcon1i_1 $f wff ps $.
	econ1i_0 $e |- ( -. ph -> ps ) $.
	con1i $p |- ( -. ps -> ph ) $= fcon1i_1 wn fcon1i_1 fcon1i_0 fcon1i_1 wn id econ1i_0 nsyl2 $.
$}
$( Inference rule derived from axiom ~ ax-3 .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 21-Jun-2013.) $)
${
	$v ph $.
	$v ps $.
	fcon4i_0 $f wff ph $.
	fcon4i_1 $f wff ps $.
	econ4i_0 $e |- ( -. ph -> -. ps ) $.
	con4i $p |- ( ps -> ph ) $= fcon4i_1 fcon4i_1 wn fcon4i_0 fcon4i_1 notnot1 econ4i_0 nsyl2 $.
$}
$( A contradiction implies anything.  Inference from ~ pm2.21 .
       (Contributed by NM, 16-Sep-1993.) $)
${
	$v ph $.
	$v ps $.
	fpm2.21i_0 $f wff ph $.
	fpm2.21i_1 $f wff ps $.
	epm2.21i_0 $e |- -. ph $.
	pm2.21i $p |- ( ph -> ps ) $= fpm2.21i_1 fpm2.21i_0 fpm2.21i_0 wn fpm2.21i_1 wn epm2.21i_0 a1i con4i $.
$}
$( A contradiction implies anything.  Inference from ~ pm2.24 .
       (Contributed by NM, 27-Feb-2008.) $)
${
	$v ph $.
	$v ps $.
	fpm2.24ii_0 $f wff ph $.
	fpm2.24ii_1 $f wff ps $.
	epm2.24ii_0 $e |- ph $.
	epm2.24ii_1 $e |- -. ph $.
	pm2.24ii $p |- ps $= fpm2.24ii_0 fpm2.24ii_1 epm2.24ii_0 fpm2.24ii_0 fpm2.24ii_1 epm2.24ii_1 pm2.21i ax-mp $.
$}
$( A contraposition deduction.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fcon3d_0 $f wff ph $.
	fcon3d_1 $f wff ps $.
	fcon3d_2 $f wff ch $.
	econ3d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $= fcon3d_0 fcon3d_1 wn fcon3d_2 fcon3d_1 wn wn fcon3d_1 fcon3d_0 fcon3d_2 fcon3d_1 notnot2 econ3d_0 syl5 con1d $.
$}
$( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Feb-2013.) $)
${
	$v ph $.
	$v ps $.
	fcon3_0 $f wff ph $.
	fcon3_1 $f wff ps $.
	con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $= fcon3_0 fcon3_1 wi fcon3_0 fcon3_1 fcon3_0 fcon3_1 wi id con3d $.
$}
$( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 20-Jun-2013.) $)
${
	$v ph $.
	$v ps $.
	fcon3i_0 $f wff ph $.
	fcon3i_1 $f wff ps $.
	econ3i_0 $e |- ( ph -> ps ) $.
	con3i $p |- ( -. ps -> -. ph ) $= fcon3i_1 wn fcon3i_1 fcon3i_0 fcon3i_1 wn id econ3i_0 nsyl $.
$}
$( Rotate through consequent right.  (Contributed by Wolf Lammen,
       3-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fcon3rr3_0 $f wff ph $.
	fcon3rr3_1 $f wff ps $.
	fcon3rr3_2 $f wff ch $.
	econ3rr3_0 $e |- ( ph -> ( ps -> ch ) ) $.
	con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $= fcon3rr3_0 fcon3rr3_2 wn fcon3rr3_1 wn fcon3rr3_0 fcon3rr3_1 fcon3rr3_2 econ3rr3_0 con3d com12 $.
$}
$( The rule of modus tollens.  (Contributed by Wolf Lammen,
       12-May-2013.) $)
${
	$v ph $.
	$v ps $.
	fmt4_0 $f wff ph $.
	fmt4_1 $f wff ps $.
	emt4_0 $e |- ph $.
	emt4_1 $e |- ( -. ps -> -. ph ) $.
	mt4 $p |- ps $= fmt4_0 fmt4_1 emt4_0 fmt4_1 fmt4_0 emt4_1 con4i ax-mp $.
$}
$( Modus tollens deduction.  (Contributed by NM, 9-Jun-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmt4d_0 $f wff ph $.
	fmt4d_1 $f wff ps $.
	fmt4d_2 $f wff ch $.
	emt4d_0 $e |- ( ph -> ps ) $.
	emt4d_1 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
	mt4d $p |- ( ph -> ch ) $= fmt4d_0 fmt4d_1 fmt4d_2 emt4d_0 fmt4d_0 fmt4d_2 fmt4d_1 emt4d_1 con4d mpd $.
$}
$( Modus tollens inference.  (Contributed by Wolf Lammen, 12-May-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmt4i_0 $f wff ph $.
	fmt4i_1 $f wff ps $.
	fmt4i_2 $f wff ch $.
	emt4i_0 $e |- ch $.
	emt4i_1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
	mt4i $p |- ( ph -> ps ) $= fmt4i_0 fmt4i_2 fmt4i_1 fmt4i_2 fmt4i_0 emt4i_0 a1i emt4i_1 mt4d $.
$}
$( A negated syllogism deduction.  (Contributed by NM, 9-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v ta $.
	fnsyld_0 $f wff ph $.
	fnsyld_1 $f wff ps $.
	fnsyld_2 $f wff ch $.
	fnsyld_3 $f wff ta $.
	ensyld_0 $e |- ( ph -> ( ps -> -. ch ) ) $.
	ensyld_1 $e |- ( ph -> ( ta -> ch ) ) $.
	nsyld $p |- ( ph -> ( ps -> -. ta ) ) $= fnsyld_0 fnsyld_1 fnsyld_2 wn fnsyld_3 wn ensyld_0 fnsyld_0 fnsyld_3 fnsyld_2 ensyld_1 con3d syld $.
$}
$( A negated syllogism inference.  (Contributed by NM, 3-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fnsyli_0 $f wff ph $.
	fnsyli_1 $f wff ps $.
	fnsyli_2 $f wff ch $.
	fnsyli_3 $f wff th $.
	ensyli_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ensyli_1 $e |- ( th -> -. ch ) $.
	nsyli $p |- ( ph -> ( th -> -. ps ) ) $= fnsyli_3 fnsyli_2 wn fnsyli_0 fnsyli_1 wn ensyli_1 fnsyli_0 fnsyli_1 fnsyli_2 ensyli_0 con3d syl5 $.
$}
$( A negated syllogism inference.  (Contributed by NM, 15-Feb-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnsyl4_0 $f wff ph $.
	fnsyl4_1 $f wff ps $.
	fnsyl4_2 $f wff ch $.
	ensyl4_0 $e |- ( ph -> ps ) $.
	ensyl4_1 $e |- ( -. ph -> ch ) $.
	nsyl4 $p |- ( -. ch -> ps ) $= fnsyl4_2 wn fnsyl4_0 fnsyl4_1 fnsyl4_0 fnsyl4_2 ensyl4_1 con1i ensyl4_0 syl $.
$}
$( Deduction version of ~ pm2.24 .  (Contributed by NM, 30-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.24d_0 $f wff ph $.
	fpm2.24d_1 $f wff ps $.
	fpm2.24d_2 $f wff ch $.
	epm2.24d_0 $e |- ( ph -> ps ) $.
	pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $= fpm2.24d_0 fpm2.24d_2 fpm2.24d_1 fpm2.24d_0 fpm2.24d_1 fpm2.24d_2 wn epm2.24d_0 a1d con1d $.
$}
$( Inference version of ~ pm2.24 .  (Contributed by NM, 20-Aug-2001.) $)
${
	$v ph $.
	$v ps $.
	fpm2.24i_0 $f wff ph $.
	fpm2.24i_1 $f wff ps $.
	epm2.24i_0 $e |- ph $.
	pm2.24i $p |- ( -. ph -> ps ) $= fpm2.24i_1 fpm2.24i_0 fpm2.24i_0 fpm2.24i_1 wn epm2.24i_0 a1i con1i $.
$}
$( Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Josh
     Purinton, 29-Dec-2000.) $)
${
	$v ph $.
	$v ps $.
	fpm3.2im_0 $f wff ph $.
	fpm3.2im_1 $f wff ps $.
	pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $= fpm3.2im_0 fpm3.2im_0 fpm3.2im_1 wn wi fpm3.2im_1 fpm3.2im_0 fpm3.2im_1 wn pm2.27 con2d $.
$}
$( Theorem 8 of [Margaris] p. 60.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Josh Purinton, 29-Dec-2000.) $)
${
	$v ph $.
	$v ps $.
	fmth8_0 $f wff ph $.
	fmth8_1 $f wff ps $.
	mth8 $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $= fmth8_0 fmth8_0 fmth8_1 wi fmth8_1 fmth8_0 fmth8_1 pm2.27 con3d $.
$}
$( Inference joining the consequents of two premises.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjc_0 $f wff ph $.
	fjc_1 $f wff ps $.
	fjc_2 $f wff ch $.
	ejc_0 $e |- ( ph -> ps ) $.
	ejc_1 $e |- ( ph -> ch ) $.
	jc $p |- ( ph -> -. ( ps -> -. ch ) ) $= fjc_0 fjc_1 fjc_2 fjc_1 fjc_2 wn wi wn ejc_0 ejc_1 fjc_1 fjc_2 pm3.2im sylc $.
$}
$( An importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimpi_0 $f wff ph $.
	fimpi_1 $f wff ps $.
	fimpi_2 $f wff ch $.
	eimpi_0 $e |- ( ph -> ( ps -> ch ) ) $.
	impi $p |- ( -. ( ph -> -. ps ) -> ch ) $= fimpi_2 fimpi_0 fimpi_1 wn wi fimpi_0 fimpi_1 fimpi_2 eimpi_0 con3rr3 con1i $.
$}
$( An exportation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fexpi_0 $f wff ph $.
	fexpi_1 $f wff ps $.
	fexpi_2 $f wff ch $.
	eexpi_0 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
	expi $p |- ( ph -> ( ps -> ch ) ) $= fexpi_0 fexpi_1 fexpi_0 fexpi_1 wn wi wn fexpi_2 fexpi_0 fexpi_1 pm3.2im eexpi_0 syl6 $.
$}
$( Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	fsimprim_0 $f wff ph $.
	fsimprim_1 $f wff ps $.
	simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $= fsimprim_0 fsimprim_1 fsimprim_1 fsimprim_0 fsimprim_1 idd impi $.
$}
$( Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 21-Jul-2012.) $)
${
	$v ph $.
	$v ps $.
	fsimplim_0 $f wff ph $.
	fsimplim_1 $f wff ps $.
	simplim $p |- ( -. ( ph -> ps ) -> ph ) $= fsimplim_0 fsimplim_0 fsimplim_1 wi fsimplim_0 fsimplim_1 pm2.21 con1i $.
$}
$( Theorem *2.5 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 9-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm2.5_0 $f wff ph $.
	fpm2.5_1 $f wff ps $.
	pm2.5 $p |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $= fpm2.5_0 fpm2.5_1 wi wn fpm2.5_0 fpm2.5_1 fpm2.5_0 fpm2.5_1 simplim pm2.24d $.
$}
$( Theorem *2.51 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.51_0 $f wff ph $.
	fpm2.51_1 $f wff ps $.
	pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $= fpm2.51_0 fpm2.51_1 wi wn fpm2.51_1 wn fpm2.51_0 fpm2.51_1 fpm2.51_0 fpm2.51_1 wi fpm2.51_1 fpm2.51_0 ax-1 con3i a1d $.
$}
$( Theorem *2.521 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm2.521_0 $f wff ph $.
	fpm2.521_1 $f wff ps $.
	pm2.521 $p |- ( -. ( ph -> ps ) -> ( ps -> ph ) ) $= fpm2.521_0 fpm2.521_1 wi wn fpm2.521_0 fpm2.521_1 fpm2.521_0 fpm2.521_1 simplim a1d $.
$}
$( Theorem *2.52 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	fpm2.52_0 $f wff ph $.
	fpm2.52_1 $f wff ps $.
	pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $= fpm2.52_0 fpm2.52_1 wi wn fpm2.52_1 fpm2.52_0 fpm2.52_0 fpm2.52_1 pm2.521 con3d $.
$}
$( Exportation theorem expressed with primitive connectives.  (Contributed by
     NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fexpt_0 $f wff ph $.
	fexpt_1 $f wff ps $.
	fexpt_2 $f wff ch $.
	expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $= fexpt_0 fexpt_0 fexpt_1 wn wi wn fexpt_2 wi fexpt_1 fexpt_2 wi fexpt_0 fexpt_1 fexpt_0 fexpt_1 wn wi wn fexpt_2 fexpt_0 fexpt_1 pm3.2im imim1d com12 $.
$}
$( Importation theorem expressed with primitive connectives.  (Contributed by
     NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen, 20-Jul-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fimpt_0 $f wff ph $.
	fimpt_1 $f wff ps $.
	fimpt_2 $f wff ch $.
	impt $p |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ) $= fimpt_0 fimpt_1 fimpt_2 wi wi fimpt_0 fimpt_1 wn wi wn fimpt_1 fimpt_2 fimpt_0 fimpt_1 simprim fimpt_0 fimpt_1 wn wi wn fimpt_0 fimpt_1 fimpt_2 wi fimpt_0 fimpt_1 wn simplim imim1i mpdi $.
$}
$( Deduction eliminating an antecedent.  (Contributed by NM, 27-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.61d_0 $f wff ph $.
	fpm2.61d_1 $f wff ps $.
	fpm2.61d_2 $f wff ch $.
	epm2.61d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	epm2.61d_1 $e |- ( ph -> ( -. ps -> ch ) ) $.
	pm2.61d $p |- ( ph -> ch ) $= fpm2.61d_0 fpm2.61d_2 fpm2.61d_0 fpm2.61d_2 wn fpm2.61d_1 fpm2.61d_2 fpm2.61d_0 fpm2.61d_1 fpm2.61d_2 epm2.61d_1 con1d epm2.61d_0 syld pm2.18d $.
$}
$( Inference eliminating an antecedent.  (Contributed by NM,
       15-Jul-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.61d1_0 $f wff ph $.
	fpm2.61d1_1 $f wff ps $.
	fpm2.61d1_2 $f wff ch $.
	epm2.61d1_0 $e |- ( ph -> ( ps -> ch ) ) $.
	epm2.61d1_1 $e |- ( -. ps -> ch ) $.
	pm2.61d1 $p |- ( ph -> ch ) $= fpm2.61d1_0 fpm2.61d1_1 fpm2.61d1_2 epm2.61d1_0 fpm2.61d1_1 wn fpm2.61d1_2 wi fpm2.61d1_0 epm2.61d1_1 a1i pm2.61d $.
$}
$( Inference eliminating an antecedent.  (Contributed by NM,
       18-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.61d2_0 $f wff ph $.
	fpm2.61d2_1 $f wff ps $.
	fpm2.61d2_2 $f wff ch $.
	epm2.61d2_0 $e |- ( ph -> ( -. ps -> ch ) ) $.
	epm2.61d2_1 $e |- ( ps -> ch ) $.
	pm2.61d2 $p |- ( ph -> ch ) $= fpm2.61d2_0 fpm2.61d2_1 fpm2.61d2_2 fpm2.61d2_1 fpm2.61d2_2 wi fpm2.61d2_0 epm2.61d2_1 a1i epm2.61d2_0 pm2.61d $.
$}
$( Inference joining the antecedents of two premises.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 19-Feb-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fja_0 $f wff ph $.
	fja_1 $f wff ps $.
	fja_2 $f wff ch $.
	eja_0 $e |- ( -. ph -> ch ) $.
	eja_1 $e |- ( ps -> ch ) $.
	ja $p |- ( ( ph -> ps ) -> ch ) $= fja_0 fja_1 wi fja_0 fja_2 fja_1 fja_2 fja_0 eja_1 imim2i eja_0 pm2.61d1 $.
$}
$( Deduction form of ~ ja .  (Contributed by Scott Fenton, 13-Dec-2010.)
       (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fjad_0 $f wff ph $.
	fjad_1 $f wff ps $.
	fjad_2 $f wff ch $.
	fjad_3 $f wff th $.
	ejad_0 $e |- ( ph -> ( -. ps -> th ) ) $.
	ejad_1 $e |- ( ph -> ( ch -> th ) ) $.
	jad $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $= fjad_1 fjad_2 wi fjad_0 fjad_3 fjad_1 fjad_2 fjad_0 fjad_3 wi fjad_0 fjad_1 wn fjad_3 ejad_0 com12 fjad_0 fjad_2 fjad_3 ejad_1 com12 ja com12 $.
$}
$( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 10-May-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fjarl_0 $f wff ph $.
	fjarl_1 $f wff ps $.
	fjarl_2 $f wff ch $.
	jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $= fjarl_0 wn fjarl_0 fjarl_1 wi fjarl_2 fjarl_0 fjarl_1 pm2.21 imim1i $.
$}
$( Inference eliminating an antecedent.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm2.61i_0 $f wff ph $.
	fpm2.61i_1 $f wff ps $.
	epm2.61i_0 $e |- ( ph -> ps ) $.
	epm2.61i_1 $e |- ( -. ph -> ps ) $.
	pm2.61i $p |- ps $= fpm2.61i_0 fpm2.61i_0 wi fpm2.61i_1 fpm2.61i_0 id fpm2.61i_0 fpm2.61i_0 fpm2.61i_1 epm2.61i_1 epm2.61i_0 ja ax-mp $.
$}
$( Inference eliminating two antecedents.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.61ii_0 $f wff ph $.
	fpm2.61ii_1 $f wff ps $.
	fpm2.61ii_2 $f wff ch $.
	epm2.61ii_0 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
	epm2.61ii_1 $e |- ( ph -> ch ) $.
	epm2.61ii_2 $e |- ( ps -> ch ) $.
	pm2.61ii $p |- ch $= fpm2.61ii_0 fpm2.61ii_2 epm2.61ii_1 fpm2.61ii_0 wn fpm2.61ii_1 fpm2.61ii_2 epm2.61ii_0 epm2.61ii_2 pm2.61d2 pm2.61i $.
$}
$( Inference eliminating two antecedents.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Wolf Lammen, 13-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.61nii_0 $f wff ph $.
	fpm2.61nii_1 $f wff ps $.
	fpm2.61nii_2 $f wff ch $.
	epm2.61nii_0 $e |- ( ph -> ( ps -> ch ) ) $.
	epm2.61nii_1 $e |- ( -. ph -> ch ) $.
	epm2.61nii_2 $e |- ( -. ps -> ch ) $.
	pm2.61nii $p |- ch $= fpm2.61nii_0 fpm2.61nii_2 fpm2.61nii_0 fpm2.61nii_1 fpm2.61nii_2 epm2.61nii_0 epm2.61nii_2 pm2.61d1 epm2.61nii_1 pm2.61i $.
$}
$( Inference eliminating three antecedents.  (Contributed by NM,
       2-Jan-2002.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fpm2.61iii_0 $f wff ph $.
	fpm2.61iii_1 $f wff ps $.
	fpm2.61iii_2 $f wff ch $.
	fpm2.61iii_3 $f wff th $.
	epm2.61iii_0 $e |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) ) $.
	epm2.61iii_1 $e |- ( ph -> th ) $.
	epm2.61iii_2 $e |- ( ps -> th ) $.
	epm2.61iii_3 $e |- ( ch -> th ) $.
	pm2.61iii $p |- th $= fpm2.61iii_2 fpm2.61iii_3 epm2.61iii_3 fpm2.61iii_0 fpm2.61iii_1 fpm2.61iii_2 wn fpm2.61iii_3 wi epm2.61iii_0 fpm2.61iii_0 fpm2.61iii_3 fpm2.61iii_2 wn epm2.61iii_1 a1d fpm2.61iii_1 fpm2.61iii_3 fpm2.61iii_2 wn epm2.61iii_2 a1d pm2.61ii pm2.61i $.
$}
$( Reductio ad absurdum.  Theorem *2.01 of [WhiteheadRussell] p. 100.
     (Contributed by NM, 18-Aug-1993.)  (Proof shortened by O'Cat,
     21-Nov-2008.)  (Proof shortened by Wolf Lammen, 31-Oct-2012.) $)
${
	$v ph $.
	fpm2.01_0 $f wff ph $.
	pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $= fpm2.01_0 fpm2.01_0 wn fpm2.01_0 wn fpm2.01_0 wn id fpm2.01_0 wn id ja $.
$}
$( Deduction based on reductio ad absurdum.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Wolf Lammen, 5-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm2.01d_0 $f wff ph $.
	fpm2.01d_1 $f wff ps $.
	epm2.01d_0 $e |- ( ph -> ( ps -> -. ps ) ) $.
	pm2.01d $p |- ( ph -> -. ps ) $= fpm2.01d_0 fpm2.01d_1 fpm2.01d_1 wn epm2.01d_0 fpm2.01d_1 wn id pm2.61d1 $.
$}
$( Theorem *2.6 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
${
	$v ph $.
	$v ps $.
	fpm2.6_0 $f wff ph $.
	fpm2.6_1 $f wff ps $.
	pm2.6 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $= fpm2.6_0 wn fpm2.6_1 wi fpm2.6_0 fpm2.6_1 fpm2.6_1 fpm2.6_0 wn fpm2.6_1 wi id fpm2.6_0 wn fpm2.6_1 wi fpm2.6_1 idd jad $.
$}
$( Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
     antecedent.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 22-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm2.61_0 $f wff ph $.
	fpm2.61_1 $f wff ps $.
	pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $= fpm2.61_0 wn fpm2.61_1 wi fpm2.61_0 fpm2.61_1 wi fpm2.61_1 fpm2.61_0 fpm2.61_1 pm2.6 com12 $.
$}
$( Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     8-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm2.65_0 $f wff ph $.
	fpm2.65_1 $f wff ps $.
	pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $= fpm2.65_0 fpm2.65_1 wi fpm2.65_0 fpm2.65_1 wn fpm2.65_0 wn fpm2.65_0 fpm2.65_1 wi fpm2.65_0 wn idd fpm2.65_0 fpm2.65_1 con3 jad $.
$}
$( Inference rule for proof by contradiction.  (Contributed by NM,
       18-May-1994.)  (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	fpm2.65i_0 $f wff ph $.
	fpm2.65i_1 $f wff ps $.
	epm2.65i_0 $e |- ( ph -> ps ) $.
	epm2.65i_1 $e |- ( ph -> -. ps ) $.
	pm2.65i $p |- -. ph $= fpm2.65i_1 fpm2.65i_0 wn fpm2.65i_0 fpm2.65i_1 epm2.65i_1 con2i fpm2.65i_0 fpm2.65i_1 epm2.65i_0 con3i pm2.61i $.
$}
$( Deduction rule for proof by contradiction.  (Contributed by NM,
       26-Jun-1994.)  (Proof shortened by Wolf Lammen, 26-May-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm2.65d_0 $f wff ph $.
	fpm2.65d_1 $f wff ps $.
	fpm2.65d_2 $f wff ch $.
	epm2.65d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	epm2.65d_1 $e |- ( ph -> ( ps -> -. ch ) ) $.
	pm2.65d $p |- ( ph -> -. ps ) $= fpm2.65d_0 fpm2.65d_1 fpm2.65d_0 fpm2.65d_1 fpm2.65d_2 fpm2.65d_1 epm2.65d_1 epm2.65d_0 nsyld pm2.01d $.
$}
$( The rule of modus tollens.  The rule says, "if ` ps ` is not true, and
       ` ph ` implies ` ps ` , then ` ps ` must also be not true."  Modus
       tollens is short for "modus tollendo tollens," a Latin phrase that means
       "the mood that by denying affirms" [Sanford] p. 39.  It is also called
       denying the consequent.  Modus tollens is closely related to modus
       ponens ~ ax-mp .  (Contributed by NM, 19-Aug-1993.)  (Proof shortened by
       Wolf Lammen, 11-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	fmto_0 $f wff ph $.
	fmto_1 $f wff ps $.
	emto_0 $e |- -. ps $.
	emto_1 $e |- ( ph -> ps ) $.
	mto $p |- -. ph $= fmto_0 fmto_1 emto_1 fmto_1 wn fmto_0 emto_0 a1i pm2.65i $.
$}
$( Modus tollens deduction.  (Contributed by NM, 3-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 11-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmtod_0 $f wff ph $.
	fmtod_1 $f wff ps $.
	fmtod_2 $f wff ch $.
	emtod_0 $e |- ( ph -> -. ch ) $.
	emtod_1 $e |- ( ph -> ( ps -> ch ) ) $.
	mtod $p |- ( ph -> -. ps ) $= fmtod_0 fmtod_1 fmtod_2 emtod_1 fmtod_0 fmtod_2 wn fmtod_1 emtod_0 a1d pm2.65d $.
$}
$( Modus tollens inference.  (Contributed by NM, 5-Jul-1994.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fmtoi_0 $f wff ph $.
	fmtoi_1 $f wff ps $.
	fmtoi_2 $f wff ch $.
	emtoi_0 $e |- -. ch $.
	emtoi_1 $e |- ( ph -> ( ps -> ch ) ) $.
	mtoi $p |- ( ph -> -. ps ) $= fmtoi_0 fmtoi_1 fmtoi_2 fmtoi_2 wn fmtoi_0 emtoi_0 a1i emtoi_1 mtod $.
$}
$( A rule similar to modus tollens.  (Contributed by NM, 19-Aug-1993.)
       (Proof shortened by Wolf Lammen, 10-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	fmt2_0 $f wff ph $.
	fmt2_1 $f wff ps $.
	emt2_0 $e |- ps $.
	emt2_1 $e |- ( ph -> -. ps ) $.
	mt2 $p |- -. ph $= fmt2_0 fmt2_1 fmt2_1 fmt2_0 emt2_0 a1i emt2_1 pm2.65i $.
$}
$( A rule similar to modus tollens.  (Contributed by NM, 18-May-1994.)
       (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
${
	$v ph $.
	$v ps $.
	fmt3_0 $f wff ph $.
	fmt3_1 $f wff ps $.
	emt3_0 $e |- -. ps $.
	emt3_1 $e |- ( -. ph -> ps ) $.
	mt3 $p |- ph $= fmt3_0 fmt3_0 wn fmt3_1 emt3_0 emt3_1 mto notnotri $.
$}
$( Peirce's axiom.  This odd-looking theorem is the "difference" between an
     intuitionistic system of propositional calculus and a classical system and
     is not accepted by intuitionists.  When Peirce's axiom is added to an
     intuitionistic system, the system becomes equivalent to our classical
     system ~ ax-1 through ~ ax-3 .  A curious fact about this theorem is that
     it requires ~ ax-3 for its proof even though the result has no negation
     connectives in it.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 9-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	fpeirce_0 $f wff ph $.
	fpeirce_1 $f wff ps $.
	peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $= fpeirce_0 fpeirce_1 wi fpeirce_0 fpeirce_0 fpeirce_0 fpeirce_1 simplim fpeirce_0 id ja $.
$}
$( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  For a version not using ~ ax-3 , see ~ loolinALT .
     (Contributed by O'Cat, 12-Aug-2004.)  (Proof shortened by Wolf Lammen,
     2-Nov-2012.) $)
${
	$v ph $.
	$v ps $.
	floolin_0 $f wff ph $.
	floolin_1 $f wff ps $.
	loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $= floolin_0 floolin_1 wi floolin_1 floolin_0 wi floolin_1 floolin_0 wi floolin_0 floolin_1 pm2.521 floolin_1 floolin_0 wi id ja $.
$}
$( The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  Using ~ dfor2 , we can see that this essentially
     expresses "disjunction commutes."  Theorem *2.69 of [WhiteheadRussell]
     p. 108.  (Contributed by NM, 12-Aug-2004.) $)
${
	$v ph $.
	$v ps $.
	flooinv_0 $f wff ph $.
	flooinv_1 $f wff ps $.
	looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $= flooinv_0 flooinv_1 wi flooinv_1 wi flooinv_1 flooinv_0 wi flooinv_0 flooinv_1 wi flooinv_0 wi flooinv_0 flooinv_0 flooinv_1 wi flooinv_1 flooinv_0 imim1 flooinv_0 flooinv_1 peirce syl6 $.
$}
$( Theorem used to justify definition of biconditional ~ df-bi .
     (Contributed by NM, 11-May-1999.)  (Proof shortened by Josh Purinton,
     29-Dec-2000.) $)
${
	$v ph $.
	$v ps $.
	fbijust_0 $f wff ph $.
	fbijust_1 $f wff ps $.
	bijust $p |- -. ( ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) ) $= fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn wi fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn wi wn wi fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn wi fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn id fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn fbijust_0 fbijust_1 wi fbijust_1 fbijust_0 wi wn wi wn wi pm2.01 mt2 $.
$}

