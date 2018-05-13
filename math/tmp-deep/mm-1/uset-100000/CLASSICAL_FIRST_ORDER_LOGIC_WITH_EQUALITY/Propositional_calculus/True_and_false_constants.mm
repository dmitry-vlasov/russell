$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical__xor_.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                True and false constants

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c T. $.

$c F. $.

$(` T. ` is a wff. $)

${
	$v  $.
	a_wtru $a wff T. $.
$}

$(` F. ` is a wff. $)

${
	$v  $.
	a_wfal $a wff F. $.
$}

$(Soundness justification theorem for ~ df-tru .  (Contributed by Mario
     Carneiro, 17-Nov-2013.) $)

${
	$v ph ps  $.
	f0_trujust $f wff ph $.
	f1_trujust $f wff ps $.
	p_trujust $p |- ( ( ph <-> ph ) <-> ( ps <-> ps ) ) $= f0_trujust p_biid f1_trujust p_biid f0_trujust f0_trujust a_wb f1_trujust f1_trujust a_wb p_2th $.
$}

$(Definition of ` T. ` , a tautology. ` T. ` is a constant true.  In this
     definition ~ biid is used as an antecedent, however, any true wff, such as
     an axiom, can be used in its place.  (Contributed by Anthony Hart,
     13-Oct-2010.) $)

${
	$v ph  $.
	f0_df-tru $f wff ph $.
	a_df-tru $a |- ( T. <-> ( ph <-> ph ) ) $.
$}

$(Definition of ` F. ` , a contradiction. ` F. ` is a constant false.
     (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	a_df-fal $a |- ( F. <-> -. T. ) $.
$}

$(` T. ` is provable.  (Contributed by Anthony Hart, 13-Oct-2010.) $)

${
	$v  $.
	i0_tru $f wff ph $.
	p_tru $p |- T. $= i0_tru p_biid i0_tru a_df-tru a_wtru i0_tru i0_tru a_wb p_mpbir $.
$}

$(` F. ` is refutable.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Mel L. O'Cat, 11-Mar-2012.) $)

${
	$v  $.
	p_fal $p |- -. F. $= p_tru a_wtru p_notnoti a_df-fal a_wfal a_wtru a_wn p_mtbir $.
$}

$(Eliminate ` T. ` as an antecedent.  (Contributed by Mario Carneiro,
       13-Mar-2014.) $)

${
	$v ph  $.
	f0_trud $f wff ph $.
	e0_trud $e |- ( T. -> ph ) $.
	p_trud $p |- ph $= p_tru e0_trud a_wtru f0_trud a_ax-mp $.
$}

$(If something is true, it outputs ` T. ` .  (Contributed by Anthony Hart,
     14-Aug-2011.) $)

${
	$v ph  $.
	f0_tbtru $f wff ph $.
	p_tbtru $p |- ( ph <-> ( ph <-> T. ) ) $= p_tru a_wtru f0_tbtru p_tbt $.
$}

$(If something is not true, it outputs ` F. ` .  (Contributed by Anthony
     Hart, 14-Aug-2011.) $)

${
	$v ph  $.
	f0_nbfal $f wff ph $.
	p_nbfal $p |- ( -. ph <-> ( ph <-> F. ) ) $= p_fal a_wfal f0_nbfal p_nbn $.
$}

$(A theorem is equivalent to truth.  (Contributed by Mario Carneiro,
       9-May-2015.) $)

${
	$v ph  $.
	f0_bitru $f wff ph $.
	e0_bitru $e |- ph $.
	p_bitru $p |- ( ph <-> T. ) $= e0_bitru p_tru f0_bitru a_wtru p_2th $.
$}

$(A contradiction is equivalent to falsehood.  (Contributed by Mario
       Carneiro, 9-May-2015.) $)

${
	$v ph  $.
	f0_bifal $f wff ph $.
	e0_bifal $e |- -. ph $.
	p_bifal $p |- ( ph <-> F. ) $= e0_bifal p_fal f0_bifal a_wfal p_2false $.
$}

$(` F. ` implies anything.  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)

${
	$v ph  $.
	f0_falim $f wff ph $.
	p_falim $p |- ( F. -> ph ) $= p_fal a_wfal f0_falim p_pm2.21i $.
$}

$(` F. ` implies anything.  (Contributed by Mario Carneiro, 9-Feb-2017.) $)

${
	$v ph ps  $.
	f0_falimd $f wff ph $.
	f1_falimd $f wff ps $.
	p_falimd $p |- ( ( ph /\ F. ) -> ps ) $= f1_falimd p_falim a_wfal f1_falimd f0_falimd p_adantl $.
$}

$(Anything implies ` T. ` .  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)

${
	$v ph  $.
	f0_a1tru $f wff ph $.
	p_a1tru $p |- ( ph -> T. ) $= p_tru a_wtru f0_a1tru p_a1i $.
$}

$(Given falsum, we can define the negation of a wff ` ph ` as the statement
     that a contradiction follows from assuming ` ph ` .  (Contributed by Mario
     Carneiro, 9-Feb-2017.) $)

${
	$v ph  $.
	f0_dfnot $f wff ph $.
	p_dfnot $p |- ( -. ph <-> ( ph -> F. ) ) $= f0_dfnot a_wfal p_pm2.21 f0_dfnot a_wn p_id f0_dfnot a_wn p_falim f0_dfnot a_wfal f0_dfnot a_wn p_ja f0_dfnot a_wn f0_dfnot a_wfal a_wi p_impbii $.
$}

$(Negation introduction rule from natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)

${
	$v ph ps  $.
	f0_inegd $f wff ph $.
	f1_inegd $f wff ps $.
	e0_inegd $e |- ( ( ph /\ ps ) -> F. ) $.
	p_inegd $p |- ( ph -> -. ps ) $= e0_inegd f0_inegd f1_inegd a_wfal p_ex f1_inegd p_dfnot f0_inegd f1_inegd a_wfal a_wi f1_inegd a_wn p_sylibr $.
$}

$(Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)

${
	$v ph ps  $.
	f0_efald $f wff ph $.
	f1_efald $f wff ps $.
	e0_efald $e |- ( ( ph /\ -. ps ) -> F. ) $.
	p_efald $p |- ( ph -> ps ) $= e0_efald f0_efald f1_efald a_wn p_inegd f0_efald f1_efald p_notnotrd $.
$}

$(If a wff and its negation are provable, then falsum is provable.
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)

${
	$v ph ps  $.
	f0_pm2.21fal $f wff ph $.
	f1_pm2.21fal $f wff ps $.
	e0_pm2.21fal $e |- ( ph -> ps ) $.
	e1_pm2.21fal $e |- ( ph -> -. ps ) $.
	p_pm2.21fal $p |- ( ph -> F. ) $= e0_pm2.21fal e1_pm2.21fal f0_pm2.21fal f1_pm2.21fal a_wfal p_pm2.21dd $.
$}


