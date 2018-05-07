$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical__xor_.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                True and false constants

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c T.  $.
$c F.  $.
$( ` T. ` is a wff. $)
${
	wtru $a wff T. $.
$}
$( ` F. ` is a wff. $)
${
	wfal $a wff F. $.
$}
$( Soundness justification theorem for ~ df-tru .  (Contributed by Mario
     Carneiro, 17-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	ftrujust_0 $f wff ph $.
	ftrujust_1 $f wff ps $.
	trujust $p |- ( ( ph <-> ph ) <-> ( ps <-> ps ) ) $= ftrujust_0 ftrujust_0 wb ftrujust_1 ftrujust_1 wb ftrujust_0 biid ftrujust_1 biid 2th $.
$}
$( Definition of ` T. ` , a tautology. ` T. ` is a constant true.  In this
     definition ~ biid is used as an antecedent, however, any true wff, such as
     an axiom, can be used in its place.  (Contributed by Anthony Hart,
     13-Oct-2010.) $)
${
	$v ph $.
	fdf-tru_0 $f wff ph $.
	df-tru $a |- ( T. <-> ( ph <-> ph ) ) $.
$}
$( Definition of ` F. ` , a contradiction. ` F. ` is a constant false.
     (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	df-fal $a |- ( F. <-> -. T. ) $.
$}
$( ` T. ` is provable.  (Contributed by Anthony Hart, 13-Oct-2010.) $)
${
	$v ph $.
	itru_0 $f wff ph $.
	tru $p |- T. $= wtru itru_0 itru_0 wb itru_0 biid itru_0 df-tru mpbir $.
$}
$( ` F. ` is refutable.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Mel L. O'Cat, 11-Mar-2012.) $)
${
	fal $p |- -. F. $= wfal wtru wn wtru tru notnoti df-fal mtbir $.
$}
$( Eliminate ` T. ` as an antecedent.  (Contributed by Mario Carneiro,
       13-Mar-2014.) $)
${
	$v ph $.
	ftrud_0 $f wff ph $.
	etrud_0 $e |- ( T. -> ph ) $.
	trud $p |- ph $= wtru ftrud_0 tru etrud_0 ax-mp $.
$}
$( If something is true, it outputs ` T. ` .  (Contributed by Anthony Hart,
     14-Aug-2011.) $)
${
	$v ph $.
	ftbtru_0 $f wff ph $.
	tbtru $p |- ( ph <-> ( ph <-> T. ) ) $= wtru ftbtru_0 tru tbt $.
$}
$( If something is not true, it outputs ` F. ` .  (Contributed by Anthony
     Hart, 14-Aug-2011.) $)
${
	$v ph $.
	fnbfal_0 $f wff ph $.
	nbfal $p |- ( -. ph <-> ( ph <-> F. ) ) $= wfal fnbfal_0 fal nbn $.
$}
$( A theorem is equivalent to truth.  (Contributed by Mario Carneiro,
       9-May-2015.) $)
${
	$v ph $.
	fbitru_0 $f wff ph $.
	ebitru_0 $e |- ph $.
	bitru $p |- ( ph <-> T. ) $= fbitru_0 wtru ebitru_0 tru 2th $.
$}
$( A contradiction is equivalent to falsehood.  (Contributed by Mario
       Carneiro, 9-May-2015.) $)
${
	$v ph $.
	fbifal_0 $f wff ph $.
	ebifal_0 $e |- -. ph $.
	bifal $p |- ( ph <-> F. ) $= fbifal_0 wfal ebifal_0 fal 2false $.
$}
$( ` F. ` implies anything.  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)
${
	$v ph $.
	ffalim_0 $f wff ph $.
	falim $p |- ( F. -> ph ) $= wfal ffalim_0 fal pm2.21i $.
$}
$( ` F. ` implies anything.  (Contributed by Mario Carneiro, 9-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	ffalimd_0 $f wff ph $.
	ffalimd_1 $f wff ps $.
	falimd $p |- ( ( ph /\ F. ) -> ps ) $= wfal ffalimd_1 ffalimd_0 ffalimd_1 falim adantl $.
$}
$( Anything implies ` T. ` .  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)
${
	$v ph $.
	fa1tru_0 $f wff ph $.
	a1tru $p |- ( ph -> T. ) $= wtru fa1tru_0 tru a1i $.
$}
$( Given falsum, we can define the negation of a wff ` ph ` as the statement
     that a contradiction follows from assuming ` ph ` .  (Contributed by Mario
     Carneiro, 9-Feb-2017.) $)
${
	$v ph $.
	fdfnot_0 $f wff ph $.
	dfnot $p |- ( -. ph <-> ( ph -> F. ) ) $= fdfnot_0 wn fdfnot_0 wfal wi fdfnot_0 wfal pm2.21 fdfnot_0 wfal fdfnot_0 wn fdfnot_0 wn id fdfnot_0 wn falim ja impbii $.
$}
$( Negation introduction rule from natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	finegd_0 $f wff ph $.
	finegd_1 $f wff ps $.
	einegd_0 $e |- ( ( ph /\ ps ) -> F. ) $.
	inegd $p |- ( ph -> -. ps ) $= finegd_0 finegd_1 wfal wi finegd_1 wn finegd_0 finegd_1 wfal einegd_0 ex finegd_1 dfnot sylibr $.
$}
$( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	fefald_0 $f wff ph $.
	fefald_1 $f wff ps $.
	eefald_0 $e |- ( ( ph /\ -. ps ) -> F. ) $.
	efald $p |- ( ph -> ps ) $= fefald_0 fefald_1 fefald_0 fefald_1 wn eefald_0 inegd notnotrd $.
$}
$( If a wff and its negation are provable, then falsum is provable.
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	fpm2.21fal_0 $f wff ph $.
	fpm2.21fal_1 $f wff ps $.
	epm2.21fal_0 $e |- ( ph -> ps ) $.
	epm2.21fal_1 $e |- ( ph -> -. ps ) $.
	pm2.21fal $p |- ( ph -> F. ) $= fpm2.21fal_0 fpm2.21fal_1 wfal epm2.21fal_0 epm2.21fal_1 pm2.21dd $.
$}

