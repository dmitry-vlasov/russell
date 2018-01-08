$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Russell_s_Paradox.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Proper substitution of classes for sets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$c [.  $.
$c ].  $.
$( /* Extend wff notation to include the proper substitution of a class for a
     set.  Read this notation as "the proper substitution of class ` A ` for
     set variable ` x ` in wff ` ph ` ." */

$)
${
	fwsbc_0 $f wff ph $.
	fwsbc_1 $f set x $.
	fwsbc_2 $f class A $.
	wsbc $a wff [. A / x ]. ph $.
$}
$( /* Define the proper substitution of a class for a set.

     When ` A ` is a proper class, our definition evaluates to false.  This is
     somewhat arbitrary: we could have, instead, chosen the conclusion of
     ~ sbc6 for our definition, which always evaluates to true for proper
     classes.

     Our definition also does not produce the same results as discussed in the
     proof of Theorem 6.6 of [Quine] p. 42 (although Theorem 6.6 itself does
     hold, as shown by ~ dfsbcq below).  For example, if ` A ` is a proper
     class, Quine's substitution of ` A ` for ` y ` in ` 0 e. y ` evaluates to
     ` 0 e. A ` rather than our falsehood.  (This can be seen by substituting
     ` A ` , ` y ` , and ` 0 ` for alpha, beta, and gamma in Subcase 1 of
     Quine's discussion on p. 42.)  Unfortunately, Quine's definition requires
     a recursive syntactical breakdown of ` ph ` , and it does not seem
     possible to express it with a single closed formula.

     If we did not want to commit to any specific proper class behavior, we
     could use this definition _only_ to prove theorem ~ dfsbcq , which holds
     for both our definition and Quine's, and from which we can derive a weaker
     version of ~ df-sbc in the form of ~ sbc8g .  However, the behavior of
     Quine's definition at proper classes is similarly arbitrary, and for
     practical reasons (to avoid having to prove sethood of ` A ` in every use
     of this definition) we allow direct reference to ~ df-sbc and assert that
     ` [. A / x ]. ph ` is always false when ` A ` is a proper class.

     The theorem ~ sbc2or shows the apparently "strongest" statement we can
     make regarding behavior at proper classes if we start from ~ dfsbcq .

     The related definition ~ df-csb defines proper substitution into a class
     variable (as opposed to a wff variable).  (Contributed by NM,
     14-Apr-1995.)  (Revised by NM, 25-Dec-2016.) */

$)
${
	fdf-sbc_0 $f wff ph $.
	fdf-sbc_1 $f set x $.
	fdf-sbc_2 $f class A $.
	df-sbc $a |- ( [. A / x ]. ph <-> A e. { x | ph } ) $.
$}
$( /* --- Start of old code before overloading prevention patch. */

$)
$( /* @( Extend wff notation to include the proper substitution of a class for a
     set.  This definition "overloads" the previously defined variable
     substitution ~ wsb (where the first argument is a set variable rather
     than a class variable).  We take care to ensure that this new definition
     is a conservative extension.  Read this notation as "the proper
     substitution of class ` A ` for set variable ` x ` in wff ` ph ` ." @)
  wsbcSBC @a wff [ A / x ] ph @.
  */

$)
$( /* --- End of old code before overloading prevention patch. */

$)
$( /* This theorem, which is similar to Theorem 6.7 of [Quine] p. 42 and holds
     under both our definition and Quine's, provides us with a weak definition
     of the proper substitution of a class for a set.  Since our ~ df-sbc does
     not result in the same behavior as Quine's for proper classes, if we
     wished to avoid conflict with Quine's definition we could start with this
     theorem and ~ dfsbcq2 instead of ~ df-sbc .  ( ~ dfsbcq2 is needed because
     unlike Quine we do not overload the ~ df-sb syntax.)  As a consequence of
     these theorems, we can derive ~ sbc8g , which is a weaker version of
     ~ df-sbc that leaves substitution undefined when ` A ` is a proper class.

     However, it is often a nuisance to have to prove the sethood hypothesis of
     ~ sbc8g , so we will allow direct use of ~ df-sbc after theorem ~ sbc2or
     below.  Proper substiution with a proper class is rarely needed, and when
     it is, we can simply use the expansion of Quine's definition.
     (Contributed by NM, 14-Apr-1995.) */

$)
${
	fdfsbcq_0 $f wff ph $.
	fdfsbcq_1 $f set x $.
	fdfsbcq_2 $f class A $.
	fdfsbcq_3 $f class B $.
	dfsbcq $p |- ( A = B -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $= fdfsbcq_2 fdfsbcq_3 wceq fdfsbcq_2 fdfsbcq_0 fdfsbcq_1 cab wcel fdfsbcq_3 fdfsbcq_0 fdfsbcq_1 cab wcel fdfsbcq_0 fdfsbcq_1 fdfsbcq_2 wsbc fdfsbcq_0 fdfsbcq_1 fdfsbcq_3 wsbc fdfsbcq_2 fdfsbcq_3 fdfsbcq_0 fdfsbcq_1 cab eleq1 fdfsbcq_0 fdfsbcq_1 fdfsbcq_2 df-sbc fdfsbcq_0 fdfsbcq_1 fdfsbcq_3 df-sbc 3bitr4g $.
$}
$( /* This theorem, which is similar to Theorem 6.7 of [Quine] p. 42 and holds
     under both our definition and Quine's, relates logic substitution ~ df-sb
     and substitution for class variables ~ df-sbc .  Unlike Quine, we use a
     different syntax for each in order to avoid overloading it.  See remarks
     in ~ dfsbcq .  (Contributed by NM, 31-Dec-2016.) */

$)
${
	fdfsbcq2_0 $f wff ph $.
	fdfsbcq2_1 $f set x $.
	fdfsbcq2_2 $f set y $.
	fdfsbcq2_3 $f class A $.
	dfsbcq2 $p |- ( y = A -> ( [ y / x ] ph <-> [. A / x ]. ph ) ) $= fdfsbcq2_2 sup_set_class fdfsbcq2_3 wceq fdfsbcq2_2 sup_set_class fdfsbcq2_0 fdfsbcq2_1 cab wcel fdfsbcq2_3 fdfsbcq2_0 fdfsbcq2_1 cab wcel fdfsbcq2_0 fdfsbcq2_1 fdfsbcq2_2 wsb fdfsbcq2_0 fdfsbcq2_1 fdfsbcq2_3 wsbc fdfsbcq2_2 sup_set_class fdfsbcq2_3 fdfsbcq2_0 fdfsbcq2_1 cab eleq1 fdfsbcq2_0 fdfsbcq2_2 fdfsbcq2_1 df-clab fdfsbcq2_0 fdfsbcq2_1 fdfsbcq2_3 wsbc fdfsbcq2_3 fdfsbcq2_0 fdfsbcq2_1 cab wcel fdfsbcq2_0 fdfsbcq2_1 fdfsbcq2_3 df-sbc bicomi 3bitr3g $.
$}
$( /* Show that ~ df-sb and ~ df-sbc are equivalent when the class term ` A ` in
     ~ df-sbc is a set variable.  This theorem lets us reuse theorems based on
     ~ df-sb for proofs involving ~ df-sbc .  (Contributed by NM,
     31-Dec-2016.)  (Proof modification is discouraged.) */

$)
${
	fsbsbc_0 $f wff ph $.
	fsbsbc_1 $f set x $.
	fsbsbc_2 $f set y $.
	sbsbc $p |- ( [ y / x ] ph <-> [. y / x ]. ph ) $= fsbsbc_2 sup_set_class fsbsbc_2 sup_set_class wceq fsbsbc_0 fsbsbc_1 fsbsbc_2 wsb fsbsbc_0 fsbsbc_1 fsbsbc_2 sup_set_class wsbc wb fsbsbc_2 sup_set_class eqid fsbsbc_0 fsbsbc_1 fsbsbc_2 fsbsbc_2 sup_set_class dfsbcq2 ax-mp $.
$}
$( /* Equality theorem for class substitution.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) */

$)
${
	fsbceq1d_0 $f wff ph $.
	fsbceq1d_1 $f set x $.
	fsbceq1d_2 $f class A $.
	fsbceq1d_3 $f class B $.
	esbceq1d_0 $e |- ( ph -> A = B ) $.
	sbceq1d $p |- ( ph -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $= fsbceq1d_0 fsbceq1d_2 fsbceq1d_3 wceq fsbceq1d_0 fsbceq1d_1 fsbceq1d_2 wsbc fsbceq1d_0 fsbceq1d_1 fsbceq1d_3 wsbc wb esbceq1d_0 fsbceq1d_0 fsbceq1d_1 fsbceq1d_2 fsbceq1d_3 dfsbcq syl $.
$}
$( /* Equality theorem for class substitution.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) */

$)
${
	fsbceq1dd_0 $f wff ph $.
	fsbceq1dd_1 $f set x $.
	fsbceq1dd_2 $f class A $.
	fsbceq1dd_3 $f class B $.
	esbceq1dd_0 $e |- ( ph -> A = B ) $.
	esbceq1dd_1 $e |- ( ph -> [. A / x ]. ph ) $.
	sbceq1dd $p |- ( ph -> [. B / x ]. ph ) $= fsbceq1dd_0 fsbceq1dd_0 fsbceq1dd_1 fsbceq1dd_2 wsbc fsbceq1dd_0 fsbceq1dd_1 fsbceq1dd_3 wsbc esbceq1dd_1 fsbceq1dd_0 fsbceq1dd_1 fsbceq1dd_2 fsbceq1dd_3 esbceq1dd_0 sbceq1d mpbid $.
$}
$( /* This is the closest we can get to ~ df-sbc if we start from ~ dfsbcq
       (see its comments) and ~ dfsbcq2 .  (Contributed by NM, 18-Nov-2008.)
       (Proof shortened by Andrew Salmon, 29-Jun-2011.)
       (Proof modification is discouraged.) */

$)
${
	$d y A $.
	$d y ph $.
	$d x y $.
	isbc8g_0 $f set y $.
	fsbc8g_0 $f wff ph $.
	fsbc8g_1 $f set x $.
	fsbc8g_2 $f class A $.
	fsbc8g_3 $f class V $.
	sbc8g $p |- ( A e. V -> ( [. A / x ]. ph <-> A e. { x | ph } ) ) $= fsbc8g_0 fsbc8g_1 isbc8g_0 sup_set_class wsbc isbc8g_0 sup_set_class fsbc8g_0 fsbc8g_1 cab wcel fsbc8g_0 fsbc8g_1 fsbc8g_2 wsbc fsbc8g_2 fsbc8g_0 fsbc8g_1 cab wcel isbc8g_0 fsbc8g_2 fsbc8g_3 fsbc8g_0 fsbc8g_1 isbc8g_0 sup_set_class fsbc8g_2 dfsbcq isbc8g_0 sup_set_class fsbc8g_2 fsbc8g_0 fsbc8g_1 cab eleq1 isbc8g_0 sup_set_class fsbc8g_0 fsbc8g_1 cab wcel fsbc8g_0 fsbc8g_1 isbc8g_0 wsb fsbc8g_0 fsbc8g_1 isbc8g_0 sup_set_class wsbc fsbc8g_0 isbc8g_0 fsbc8g_1 df-clab isbc8g_0 sup_set_class isbc8g_0 sup_set_class wceq fsbc8g_0 fsbc8g_1 isbc8g_0 wsb fsbc8g_0 fsbc8g_1 isbc8g_0 sup_set_class wsbc wb isbc8g_0 equid fsbc8g_0 fsbc8g_1 isbc8g_0 isbc8g_0 sup_set_class dfsbcq2 ax-mp bitr2i vtoclbg $.
$}
$( /* The disjunction of two equivalences for class substitution does not
       require a class existence hypothesis.  This theorem tells us that there
       are only 2 possibilities for ` [ A / x ] ph ` behavior at proper
       classes, matching the ~ sbc5 (false) and ~ sbc6 (true) conclusions.
       This is interesting since ~ dfsbcq and ~ dfsbcq2 (from which it is
       derived) do not appear to say anything obvious about proper class
       behavior.  Note that this theorem doesn't tell us that it is always one
       or the other at proper classes; it could "flip" between false (the first
       disjunct) and true (the second disjunct) as a function of some other
       variable ` y ` that ` ph ` or ` A ` may contain.  (Contributed by NM,
       11-Oct-2004.)  (Proof modification is discouraged.) */

$)
${
	$d x y A $.
	$d y ph $.
	isbc2or_0 $f set y $.
	fsbc2or_0 $f wff ph $.
	fsbc2or_1 $f set x $.
	fsbc2or_2 $f class A $.
	sbc2or $p |- ( ( [. A / x ]. ph <-> E. x ( x = A /\ ph ) ) \/ ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) ) $= fsbc2or_2 cvv wcel fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wb fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wi fsbc2or_1 wal wb wo fsbc2or_2 cvv wcel fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wb fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wi fsbc2or_1 wal wb fsbc2or_0 fsbc2or_1 isbc2or_0 wsb fsbc2or_1 sup_set_class isbc2or_0 sup_set_class wceq fsbc2or_0 wa fsbc2or_1 wex fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex isbc2or_0 fsbc2or_2 cvv fsbc2or_0 fsbc2or_1 isbc2or_0 fsbc2or_2 dfsbcq2 isbc2or_0 sup_set_class fsbc2or_2 wceq fsbc2or_1 sup_set_class isbc2or_0 sup_set_class wceq fsbc2or_0 wa fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 isbc2or_0 sup_set_class fsbc2or_2 wceq fsbc2or_1 sup_set_class isbc2or_0 sup_set_class wceq fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 isbc2or_0 sup_set_class fsbc2or_2 fsbc2or_1 sup_set_class eqeq2 anbi1d exbidv fsbc2or_0 fsbc2or_1 isbc2or_0 sb5 vtoclbg orcd fsbc2or_2 cvv wcel wn fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wb fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wn wb wo fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wb fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wi fsbc2or_1 wal wb wo fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex pm5.15 fsbc2or_2 cvv wcel wn fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wn wb fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wi fsbc2or_1 wal wb fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wb fsbc2or_2 cvv wcel wn fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wn fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wi fsbc2or_1 wal fsbc2or_0 fsbc2or_1 fsbc2or_2 wsbc fsbc2or_2 cvv wcel wn fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 wex wn fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wi fsbc2or_1 wal fsbc2or_2 cvv wcel wn fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_1 fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wa fsbc2or_2 cvv wcel fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_2 cvv wcel fsbc2or_0 fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_1 sup_set_class cvv wcel fsbc2or_2 cvv wcel fsbc2or_1 vex fsbc2or_1 sup_set_class fsbc2or_2 cvv eleq1 mpbii adantr con3i nexdv fsbc2or_2 cvv wcel wn fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 wi fsbc2or_1 fsbc2or_2 cvv wcel wn fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_0 fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_2 cvv wcel fsbc2or_1 sup_set_class fsbc2or_2 wceq fsbc2or_1 sup_set_class cvv wcel fsbc2or_2 cvv wcel fsbc2or_1 vex fsbc2or_1 sup_set_class fsbc2or_2 cvv eleq1 mpbii con3i pm2.21d alrimiv 2thd bibi2d orbi2d mpbii pm2.61i $.
$}
$( /* By our definition of proper substitution, it can only be true if the
     substituted expression is a set.  (Contributed by Mario Carneiro,
     13-Oct-2016.) */

$)
${
	fsbcex_0 $f wff ph $.
	fsbcex_1 $f set x $.
	fsbcex_2 $f class A $.
	sbcex $p |- ( [. A / x ]. ph -> A e. _V ) $= fsbcex_0 fsbcex_1 fsbcex_2 wsbc fsbcex_2 fsbcex_0 fsbcex_1 cab wcel fsbcex_2 cvv wcel fsbcex_0 fsbcex_1 fsbcex_2 df-sbc fsbcex_2 fsbcex_0 fsbcex_1 cab elex sylbi $.
$}
$( /* Equality theorem for class substitution.  Class version of ~ sbequ12 .
     (Contributed by NM, 26-Sep-2003.) */

$)
${
	fsbceq1a_0 $f wff ph $.
	fsbceq1a_1 $f set x $.
	fsbceq1a_2 $f class A $.
	sbceq1a $p |- ( x = A -> ( ph <-> [. A / x ]. ph ) ) $= fsbceq1a_0 fsbceq1a_0 fsbceq1a_1 fsbceq1a_1 wsb fsbceq1a_1 sup_set_class fsbceq1a_2 wceq fsbceq1a_0 fsbceq1a_1 fsbceq1a_2 wsbc fsbceq1a_0 fsbceq1a_1 sbid fsbceq1a_0 fsbceq1a_1 fsbceq1a_1 fsbceq1a_2 dfsbcq2 syl5bbr $.
$}
$( /* Equality theorem for class substitution.  Class version of ~ sbequ12r .
     (Contributed by NM, 4-Jan-2017.) */

$)
${
	fsbceq2a_0 $f wff ph $.
	fsbceq2a_1 $f set x $.
	fsbceq2a_2 $f class A $.
	sbceq2a $p |- ( A = x -> ( [. A / x ]. ph <-> ph ) ) $= fsbceq2a_2 fsbceq2a_1 sup_set_class wceq fsbceq2a_0 fsbceq2a_0 fsbceq2a_1 fsbceq2a_2 wsbc fsbceq2a_0 fsbceq2a_0 fsbceq2a_1 fsbceq2a_2 wsbc wb fsbceq2a_1 sup_set_class fsbceq2a_2 fsbceq2a_0 fsbceq2a_1 fsbceq2a_2 sbceq1a eqcoms bicomd $.
$}
$( /* Specialization: if a formula is true for all sets, it is true for any
       class which is a set.  Similar to Theorem 6.11 of [Quine] p. 44.  See
       also ~ stdpc4 and ~ rspsbc .  (Contributed by NM, 16-Jan-2004.) */

$)
${
	$d ph y $.
	$d A y $.
	$d x y $.
	ispsbc_0 $f set y $.
	fspsbc_0 $f wff ph $.
	fspsbc_1 $f set x $.
	fspsbc_2 $f class A $.
	fspsbc_3 $f class V $.
	spsbc $p |- ( A e. V -> ( A. x ph -> [. A / x ]. ph ) ) $= fspsbc_0 fspsbc_1 wal fspsbc_0 fspsbc_1 fspsbc_2 wsbc wi ispsbc_0 fspsbc_2 fspsbc_3 fspsbc_0 fspsbc_1 wal fspsbc_0 fspsbc_1 ispsbc_0 sup_set_class wsbc ispsbc_0 sup_set_class fspsbc_2 wceq fspsbc_0 fspsbc_1 fspsbc_2 wsbc fspsbc_0 fspsbc_1 wal fspsbc_0 fspsbc_1 ispsbc_0 wsb fspsbc_0 fspsbc_1 ispsbc_0 sup_set_class wsbc fspsbc_0 fspsbc_1 ispsbc_0 stdpc4 fspsbc_0 fspsbc_1 ispsbc_0 sbsbc sylib fspsbc_0 fspsbc_1 ispsbc_0 sup_set_class fspsbc_2 dfsbcq syl5ib vtocleg $.
$}
$( /* Specialization: if a formula is true for all sets, it is true for any
       class which is a set.  Similar to Theorem 6.11 of [Quine] p. 44.  See
       also ~ stdpc4 and ~ rspsbc .  (Contributed by Mario Carneiro,
       9-Feb-2017.) */

$)
${
	fspsbcd_0 $f wff ph $.
	fspsbcd_1 $f wff ps $.
	fspsbcd_2 $f set x $.
	fspsbcd_3 $f class A $.
	fspsbcd_4 $f class V $.
	espsbcd_0 $e |- ( ph -> A e. V ) $.
	espsbcd_1 $e |- ( ph -> A. x ps ) $.
	spsbcd $p |- ( ph -> [. A / x ]. ps ) $= fspsbcd_0 fspsbcd_3 fspsbcd_4 wcel fspsbcd_1 fspsbcd_2 wal fspsbcd_1 fspsbcd_2 fspsbcd_3 wsbc espsbcd_0 espsbcd_1 fspsbcd_1 fspsbcd_2 fspsbcd_3 fspsbcd_4 spsbc sylc $.
$}
$( /* A substitution into a theorem remains true (when ` A ` is a set).
       (Contributed by NM, 5-Nov-2005.) */

$)
${
	fsbcth_0 $f wff ph $.
	fsbcth_1 $f set x $.
	fsbcth_2 $f class A $.
	fsbcth_3 $f class V $.
	esbcth_0 $e |- ph $.
	sbcth $p |- ( A e. V -> [. A / x ]. ph ) $= fsbcth_2 fsbcth_3 wcel fsbcth_0 fsbcth_1 wal fsbcth_0 fsbcth_1 fsbcth_2 wsbc fsbcth_0 fsbcth_1 esbcth_0 ax-gen fsbcth_0 fsbcth_1 fsbcth_2 fsbcth_3 spsbc mpi $.
$}
$( /* Deduction version of ~ sbcth .  (Contributed by NM, 30-Nov-2005.)
       (Proof shortened by Andrew Salmon, 8-Jun-2011.) */

$)
${
	$d x ph $.
	fsbcthdv_0 $f wff ph $.
	fsbcthdv_1 $f wff ps $.
	fsbcthdv_2 $f set x $.
	fsbcthdv_3 $f class A $.
	fsbcthdv_4 $f class V $.
	esbcthdv_0 $e |- ( ph -> ps ) $.
	sbcthdv $p |- ( ( ph /\ A e. V ) -> [. A / x ]. ps ) $= fsbcthdv_0 fsbcthdv_1 fsbcthdv_2 wal fsbcthdv_3 fsbcthdv_4 wcel fsbcthdv_1 fsbcthdv_2 fsbcthdv_3 wsbc fsbcthdv_0 fsbcthdv_1 fsbcthdv_2 esbcthdv_0 alrimiv fsbcthdv_1 fsbcthdv_2 fsbcthdv_3 fsbcthdv_4 spsbc mpan9 $.
$}
$( /* An identity theorem for substitution.  See ~ sbid .  (Contributed by Mario
     Carneiro, 18-Feb-2017.) */

$)
${
	fsbcid_0 $f wff ph $.
	fsbcid_1 $f set x $.
	sbcid $p |- ( [. x / x ]. ph <-> ph ) $= fsbcid_0 fsbcid_1 fsbcid_1 sup_set_class wsbc fsbcid_0 fsbcid_1 fsbcid_1 wsb fsbcid_0 fsbcid_0 fsbcid_1 fsbcid_1 sbsbc fsbcid_0 fsbcid_1 sbid bitr3i $.
$}
$( /* Deduction version of ~ nfsbc1 .  (Contributed by NM, 23-May-2006.)
       (Revised by Mario Carneiro, 12-Oct-2016.) */

$)
${
	fnfsbc1d_0 $f wff ph $.
	fnfsbc1d_1 $f wff ps $.
	fnfsbc1d_2 $f set x $.
	fnfsbc1d_3 $f class A $.
	enfsbc1d_0 $e |- ( ph -> F/_ x A ) $.
	nfsbc1d $p |- ( ph -> F/ x [. A / x ]. ps ) $= fnfsbc1d_1 fnfsbc1d_2 fnfsbc1d_3 wsbc fnfsbc1d_3 fnfsbc1d_1 fnfsbc1d_2 cab wcel fnfsbc1d_0 fnfsbc1d_2 fnfsbc1d_1 fnfsbc1d_2 fnfsbc1d_3 df-sbc fnfsbc1d_0 fnfsbc1d_2 fnfsbc1d_3 fnfsbc1d_1 fnfsbc1d_2 cab enfsbc1d_0 fnfsbc1d_2 fnfsbc1d_1 fnfsbc1d_2 cab wnfc fnfsbc1d_0 fnfsbc1d_1 fnfsbc1d_2 nfab1 a1i nfeld nfxfrd $.
$}
$( /* Bound-variable hypothesis builder for class substitution.  (Contributed
       by Mario Carneiro, 12-Oct-2016.) */

$)
${
	fnfsbc1_0 $f wff ph $.
	fnfsbc1_1 $f set x $.
	fnfsbc1_2 $f class A $.
	enfsbc1_0 $e |- F/_ x A $.
	nfsbc1 $p |- F/ x [. A / x ]. ph $= fnfsbc1_0 fnfsbc1_1 fnfsbc1_2 wsbc fnfsbc1_1 wnf wtru fnfsbc1_0 fnfsbc1_1 fnfsbc1_2 fnfsbc1_1 fnfsbc1_2 wnfc wtru enfsbc1_0 a1i nfsbc1d trud $.
$}
$( /* Bound-variable hypothesis builder for class substitution.  (Contributed
       by Mario Carneiro, 12-Oct-2016.) */

$)
${
	$d x A $.
	fnfsbc1v_0 $f wff ph $.
	fnfsbc1v_1 $f set x $.
	fnfsbc1v_2 $f class A $.
	nfsbc1v $p |- F/ x [. A / x ]. ph $= fnfsbc1v_0 fnfsbc1v_1 fnfsbc1v_2 fnfsbc1v_1 fnfsbc1v_2 nfcv nfsbc1 $.
$}
$( /* Deduction version of ~ nfsbc .  (Contributed by NM, 23-Nov-2005.)
       (Revised by Mario Carneiro, 12-Oct-2016.) */

$)
${
	fnfsbcd_0 $f wff ph $.
	fnfsbcd_1 $f wff ps $.
	fnfsbcd_2 $f set x $.
	fnfsbcd_3 $f set y $.
	fnfsbcd_4 $f class A $.
	enfsbcd_0 $e |- F/ y ph $.
	enfsbcd_1 $e |- ( ph -> F/_ x A ) $.
	enfsbcd_2 $e |- ( ph -> F/ x ps ) $.
	nfsbcd $p |- ( ph -> F/ x [. A / y ]. ps ) $= fnfsbcd_1 fnfsbcd_3 fnfsbcd_4 wsbc fnfsbcd_4 fnfsbcd_1 fnfsbcd_3 cab wcel fnfsbcd_0 fnfsbcd_2 fnfsbcd_1 fnfsbcd_3 fnfsbcd_4 df-sbc fnfsbcd_0 fnfsbcd_2 fnfsbcd_4 fnfsbcd_1 fnfsbcd_3 cab enfsbcd_1 fnfsbcd_0 fnfsbcd_1 fnfsbcd_2 fnfsbcd_3 enfsbcd_0 enfsbcd_2 nfabd nfeld nfxfrd $.
$}
$( /* Bound-variable hypothesis builder for class substitution.  (Contributed
       by NM, 7-Sep-2014.)  (Revised by Mario Carneiro, 12-Oct-2016.) */

$)
${
	fnfsbc_0 $f wff ph $.
	fnfsbc_1 $f set x $.
	fnfsbc_2 $f set y $.
	fnfsbc_3 $f class A $.
	enfsbc_0 $e |- F/_ x A $.
	enfsbc_1 $e |- F/ x ph $.
	nfsbc $p |- F/ x [. A / y ]. ph $= fnfsbc_0 fnfsbc_2 fnfsbc_3 wsbc fnfsbc_1 wnf wtru fnfsbc_0 fnfsbc_1 fnfsbc_2 fnfsbc_3 fnfsbc_2 nftru fnfsbc_1 fnfsbc_3 wnfc wtru enfsbc_0 a1i fnfsbc_0 fnfsbc_1 wnf wtru enfsbc_1 a1i nfsbcd trud $.
$}
$( /* A composition law for class substitution.  (Contributed by NM,
       26-Sep-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) */

$)
${
	$d x z $.
	$d z A $.
	$d y z ph $.
	isbcco_0 $f set z $.
	fsbcco_0 $f wff ph $.
	fsbcco_1 $f set x $.
	fsbcco_2 $f set y $.
	fsbcco_3 $f class A $.
	sbcco $p |- ( [. A / y ]. [. y / x ]. ph <-> [. A / x ]. ph ) $= fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 fsbcco_3 wsbc fsbcco_3 cvv wcel fsbcco_0 fsbcco_1 fsbcco_3 wsbc fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 fsbcco_3 sbcex fsbcco_0 fsbcco_1 fsbcco_3 sbcex fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 isbcco_0 sup_set_class wsbc fsbcco_0 fsbcco_1 isbcco_0 sup_set_class wsbc fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 fsbcco_3 wsbc fsbcco_0 fsbcco_1 fsbcco_3 wsbc isbcco_0 fsbcco_3 cvv fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 isbcco_0 sup_set_class fsbcco_3 dfsbcq fsbcco_0 fsbcco_1 isbcco_0 sup_set_class fsbcco_3 dfsbcq fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 isbcco_0 sup_set_class wsbc fsbcco_0 fsbcco_1 isbcco_0 wsb fsbcco_0 fsbcco_1 isbcco_0 sup_set_class wsbc fsbcco_0 fsbcco_1 fsbcco_2 wsb fsbcco_2 isbcco_0 wsb fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 isbcco_0 wsb fsbcco_0 fsbcco_1 isbcco_0 wsb fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 isbcco_0 sup_set_class wsbc fsbcco_0 fsbcco_1 fsbcco_2 wsb fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 isbcco_0 fsbcco_0 fsbcco_1 fsbcco_2 sbsbc sbbii fsbcco_0 fsbcco_1 isbcco_0 fsbcco_2 fsbcco_0 fsbcco_2 nfv sbco2 fsbcco_0 fsbcco_1 fsbcco_2 sup_set_class wsbc fsbcco_2 isbcco_0 sbsbc 3bitr3ri fsbcco_0 fsbcco_1 isbcco_0 sbsbc bitri vtoclbg pm5.21nii $.
$}
$( /* A composition law for class substitution.  Importantly, ` x ` may occur
       free in the class expression substituted for ` A ` .  (Contributed by
       NM, 5-Sep-2004.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) */

$)
${
	$d x y $.
	$d y ph $.
	$d A y $.
	fsbcco2_0 $f wff ph $.
	fsbcco2_1 $f set x $.
	fsbcco2_2 $f set y $.
	fsbcco2_3 $f class A $.
	fsbcco2_4 $f class B $.
	esbcco2_0 $e |- ( x = y -> A = B ) $.
	sbcco2 $p |- ( [. x / y ]. [. B / x ]. ph <-> [. A / x ]. ph ) $= fsbcco2_0 fsbcco2_1 fsbcco2_4 wsbc fsbcco2_2 fsbcco2_1 sup_set_class wsbc fsbcco2_0 fsbcco2_1 fsbcco2_4 wsbc fsbcco2_2 fsbcco2_1 wsb fsbcco2_0 fsbcco2_1 fsbcco2_3 wsbc fsbcco2_0 fsbcco2_1 fsbcco2_4 wsbc fsbcco2_2 fsbcco2_1 sbsbc fsbcco2_0 fsbcco2_1 fsbcco2_4 wsbc fsbcco2_0 fsbcco2_1 fsbcco2_3 wsbc fsbcco2_2 fsbcco2_1 fsbcco2_0 fsbcco2_1 fsbcco2_3 wsbc fsbcco2_2 nfv fsbcco2_2 sup_set_class fsbcco2_1 sup_set_class wceq fsbcco2_3 fsbcco2_4 wceq fsbcco2_0 fsbcco2_1 fsbcco2_4 wsbc fsbcco2_0 fsbcco2_1 fsbcco2_3 wsbc wb fsbcco2_3 fsbcco2_4 wceq fsbcco2_1 sup_set_class fsbcco2_2 sup_set_class esbcco2_0 eqcoms fsbcco2_3 fsbcco2_4 wceq fsbcco2_0 fsbcco2_1 fsbcco2_3 wsbc fsbcco2_0 fsbcco2_1 fsbcco2_4 wsbc fsbcco2_0 fsbcco2_1 fsbcco2_3 fsbcco2_4 dfsbcq bicomd syl sbie bitr3i $.
$}
$( /* An equivalence for class substitution.  (Contributed by NM,
       23-Aug-1993.)  (Revised by Mario Carneiro, 12-Oct-2016.) */

$)
${
	$d x y A $.
	$d y ph $.
	isbc5_0 $f set y $.
	fsbc5_0 $f wff ph $.
	fsbc5_1 $f set x $.
	fsbc5_2 $f class A $.
	sbc5 $p |- ( [. A / x ]. ph <-> E. x ( x = A /\ ph ) ) $= fsbc5_0 fsbc5_1 fsbc5_2 wsbc fsbc5_2 cvv wcel fsbc5_1 sup_set_class fsbc5_2 wceq fsbc5_0 wa fsbc5_1 wex fsbc5_0 fsbc5_1 fsbc5_2 sbcex fsbc5_1 sup_set_class fsbc5_2 wceq fsbc5_0 wa fsbc5_1 wex fsbc5_1 sup_set_class fsbc5_2 wceq fsbc5_1 wex fsbc5_2 cvv wcel fsbc5_1 sup_set_class fsbc5_2 wceq fsbc5_0 fsbc5_1 exsimpl fsbc5_1 fsbc5_2 isset sylibr fsbc5_0 fsbc5_1 isbc5_0 wsb fsbc5_1 sup_set_class isbc5_0 sup_set_class wceq fsbc5_0 wa fsbc5_1 wex fsbc5_0 fsbc5_1 fsbc5_2 wsbc fsbc5_1 sup_set_class fsbc5_2 wceq fsbc5_0 wa fsbc5_1 wex isbc5_0 fsbc5_2 cvv fsbc5_0 fsbc5_1 isbc5_0 fsbc5_2 dfsbcq2 isbc5_0 sup_set_class fsbc5_2 wceq fsbc5_1 sup_set_class isbc5_0 sup_set_class wceq fsbc5_0 wa fsbc5_1 sup_set_class fsbc5_2 wceq fsbc5_0 wa fsbc5_1 isbc5_0 sup_set_class fsbc5_2 wceq fsbc5_1 sup_set_class isbc5_0 sup_set_class wceq fsbc5_1 sup_set_class fsbc5_2 wceq fsbc5_0 isbc5_0 sup_set_class fsbc5_2 fsbc5_1 sup_set_class eqeq2 anbi1d exbidv fsbc5_0 fsbc5_1 isbc5_0 sb5 vtoclbg pm5.21nii $.
$}
$( /* An equivalence for class substitution.  (Contributed by NM,
       11-Oct-2004.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) */

$)
${
	$d x A $.
	fsbc6g_0 $f wff ph $.
	fsbc6g_1 $f set x $.
	fsbc6g_2 $f class A $.
	fsbc6g_3 $f class V $.
	sbc6g $p |- ( A e. V -> ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) ) $= fsbc6g_2 fsbc6g_3 wcel fsbc6g_1 sup_set_class fsbc6g_2 wceq fsbc6g_0 wi fsbc6g_1 wal fsbc6g_1 sup_set_class fsbc6g_2 wceq fsbc6g_0 wa fsbc6g_1 wex fsbc6g_0 fsbc6g_1 fsbc6g_2 wsbc fsbc6g_0 fsbc6g_1 sup_set_class fsbc6g_2 wceq fsbc6g_0 wa fsbc6g_1 wex fsbc6g_1 fsbc6g_2 fsbc6g_3 fsbc6g_1 sup_set_class fsbc6g_2 wceq fsbc6g_0 wa fsbc6g_1 nfe1 fsbc6g_0 fsbc6g_1 fsbc6g_2 ceqex ceqsalg fsbc6g_0 fsbc6g_1 fsbc6g_2 sbc5 syl6rbbr $.
$}
$( /* An equivalence for class substitution.  (Contributed by NM,
       23-Aug-1993.)  (Proof shortened by Eric Schmidt, 17-Jan-2007.) */

$)
${
	$d x A $.
	fsbc6_0 $f wff ph $.
	fsbc6_1 $f set x $.
	fsbc6_2 $f class A $.
	esbc6_0 $e |- A e. _V $.
	sbc6 $p |- ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) $= fsbc6_2 cvv wcel fsbc6_0 fsbc6_1 fsbc6_2 wsbc fsbc6_1 sup_set_class fsbc6_2 wceq fsbc6_0 wi fsbc6_1 wal wb esbc6_0 fsbc6_0 fsbc6_1 fsbc6_2 cvv sbc6g ax-mp $.
$}
$( /* An equivalence for class substitution in the spirit of ~ df-clab .  Note
       that ` x ` and ` A ` don't have to be distinct.  (Contributed by NM,
       18-Nov-2008.)  (Revised by Mario Carneiro, 13-Oct-2016.) */

$)
${
	$d y A $.
	$d y ph $.
	$d x y $.
	fsbc7_0 $f wff ph $.
	fsbc7_1 $f set x $.
	fsbc7_2 $f set y $.
	fsbc7_3 $f class A $.
	sbc7 $p |- ( [. A / x ]. ph <-> E. y ( y = A /\ [. y / x ]. ph ) ) $= fsbc7_0 fsbc7_1 fsbc7_3 wsbc fsbc7_0 fsbc7_1 fsbc7_2 sup_set_class wsbc fsbc7_2 fsbc7_3 wsbc fsbc7_2 sup_set_class fsbc7_3 wceq fsbc7_0 fsbc7_1 fsbc7_2 sup_set_class wsbc wa fsbc7_2 wex fsbc7_0 fsbc7_1 fsbc7_2 fsbc7_3 sbcco fsbc7_0 fsbc7_1 fsbc7_2 sup_set_class wsbc fsbc7_2 fsbc7_3 sbc5 bitr3i $.
$}
$( /* Change bound variables in a wff substitution.  (Contributed by Jeff
       Hankins, 19-Sep-2009.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) */

$)
${
	fcbvsbc_0 $f wff ph $.
	fcbvsbc_1 $f wff ps $.
	fcbvsbc_2 $f set x $.
	fcbvsbc_3 $f set y $.
	fcbvsbc_4 $f class A $.
	ecbvsbc_0 $e |- F/ y ph $.
	ecbvsbc_1 $e |- F/ x ps $.
	ecbvsbc_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvsbc $p |- ( [. A / x ]. ph <-> [. A / y ]. ps ) $= fcbvsbc_4 fcbvsbc_0 fcbvsbc_2 cab wcel fcbvsbc_4 fcbvsbc_1 fcbvsbc_3 cab wcel fcbvsbc_0 fcbvsbc_2 fcbvsbc_4 wsbc fcbvsbc_1 fcbvsbc_3 fcbvsbc_4 wsbc fcbvsbc_0 fcbvsbc_2 cab fcbvsbc_1 fcbvsbc_3 cab fcbvsbc_4 fcbvsbc_0 fcbvsbc_1 fcbvsbc_2 fcbvsbc_3 ecbvsbc_0 ecbvsbc_1 ecbvsbc_2 cbvab eleq2i fcbvsbc_0 fcbvsbc_2 fcbvsbc_4 df-sbc fcbvsbc_1 fcbvsbc_3 fcbvsbc_4 df-sbc 3bitr4i $.
$}
$( /* Change the bound variable of a class substitution using implicit
       substitution.  (Contributed by NM, 30-Sep-2008.)  (Revised by Mario
       Carneiro, 13-Oct-2016.) */

$)
${
	$d y ph $.
	$d x ps $.
	fcbvsbcv_0 $f wff ph $.
	fcbvsbcv_1 $f wff ps $.
	fcbvsbcv_2 $f set x $.
	fcbvsbcv_3 $f set y $.
	fcbvsbcv_4 $f class A $.
	ecbvsbcv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvsbcv $p |- ( [. A / x ]. ph <-> [. A / y ]. ps ) $= fcbvsbcv_0 fcbvsbcv_1 fcbvsbcv_2 fcbvsbcv_3 fcbvsbcv_4 fcbvsbcv_0 fcbvsbcv_3 nfv fcbvsbcv_1 fcbvsbcv_2 nfv ecbvsbcv_0 cbvsbc $.
$}
$( /* Conversion of implicit substitution to explicit class substitution,
       using a bound-variable hypothesis instead of distinct variables.
       (Closed theorem version of ~ sbciegf .)  (Contributed by NM,
       10-Nov-2005.)  (Revised by Mario Carneiro, 13-Oct-2016.) */

$)
${
	$d x A $.
	fsbciegft_0 $f wff ph $.
	fsbciegft_1 $f wff ps $.
	fsbciegft_2 $f set x $.
	fsbciegft_3 $f class A $.
	fsbciegft_4 $f class V $.
	sbciegft $p |- ( ( A e. V /\ F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) ) -> ( [. A / x ]. ph <-> ps ) ) $= fsbciegft_3 fsbciegft_4 wcel fsbciegft_1 fsbciegft_2 wnf fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 wal w3a fsbciegft_0 fsbciegft_2 fsbciegft_3 wsbc fsbciegft_1 fsbciegft_0 fsbciegft_2 fsbciegft_3 wsbc fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wa fsbciegft_2 wex fsbciegft_3 fsbciegft_4 wcel fsbciegft_1 fsbciegft_2 wnf fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 wal w3a fsbciegft_1 fsbciegft_0 fsbciegft_2 fsbciegft_3 sbc5 fsbciegft_1 fsbciegft_2 wnf fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 wal fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wa fsbciegft_2 wex fsbciegft_1 wi fsbciegft_3 fsbciegft_4 wcel fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 wal fsbciegft_1 fsbciegft_2 wnf fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wa fsbciegft_1 wi fsbciegft_2 wal fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wa fsbciegft_2 wex fsbciegft_1 wi fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wa fsbciegft_1 wi fsbciegft_2 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 fsbciegft_0 fsbciegft_1 wb fsbciegft_0 fsbciegft_1 wi fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 bi1 imim2i imp3a alimi fsbciegft_1 fsbciegft_2 wnf fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wa fsbciegft_1 wi fsbciegft_2 wal fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wa fsbciegft_2 wex fsbciegft_1 wi fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wa fsbciegft_1 fsbciegft_2 19.23t biimpa sylan2 3adant1 syl5bi fsbciegft_3 fsbciegft_4 wcel fsbciegft_1 fsbciegft_2 wnf fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 wal w3a fsbciegft_1 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi fsbciegft_2 wal fsbciegft_0 fsbciegft_2 fsbciegft_3 wsbc fsbciegft_1 fsbciegft_2 wnf fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 wal fsbciegft_1 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi fsbciegft_2 wal wi fsbciegft_3 fsbciegft_4 wcel fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 wal fsbciegft_1 fsbciegft_2 wnf fsbciegft_1 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi wi fsbciegft_2 wal fsbciegft_1 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi fsbciegft_2 wal wi fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_1 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi wi fsbciegft_2 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_1 fsbciegft_0 fsbciegft_0 fsbciegft_1 wb fsbciegft_1 fsbciegft_0 wi fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 bi2 imim2i com23 alimi fsbciegft_1 fsbciegft_2 wnf fsbciegft_1 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi wi fsbciegft_2 wal fsbciegft_1 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi fsbciegft_2 wal wi fsbciegft_1 fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi fsbciegft_2 19.21t biimpa sylan2 3adant1 fsbciegft_3 fsbciegft_4 wcel fsbciegft_1 fsbciegft_2 wnf fsbciegft_0 fsbciegft_2 fsbciegft_3 wsbc fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 wi fsbciegft_2 wal wb fsbciegft_2 sup_set_class fsbciegft_3 wceq fsbciegft_0 fsbciegft_1 wb wi fsbciegft_2 wal fsbciegft_0 fsbciegft_2 fsbciegft_3 fsbciegft_4 sbc6g 3ad2ant1 sylibrd impbid $.
$}
$( /* Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) */

$)
${
	$d x A $.
	fsbciegf_0 $f wff ph $.
	fsbciegf_1 $f wff ps $.
	fsbciegf_2 $f set x $.
	fsbciegf_3 $f class A $.
	fsbciegf_4 $f class V $.
	esbciegf_0 $e |- F/ x ps $.
	esbciegf_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	sbciegf $p |- ( A e. V -> ( [. A / x ]. ph <-> ps ) ) $= fsbciegf_3 fsbciegf_4 wcel fsbciegf_1 fsbciegf_2 wnf fsbciegf_2 sup_set_class fsbciegf_3 wceq fsbciegf_0 fsbciegf_1 wb wi fsbciegf_2 wal fsbciegf_0 fsbciegf_2 fsbciegf_3 wsbc fsbciegf_1 wb esbciegf_0 fsbciegf_2 sup_set_class fsbciegf_3 wceq fsbciegf_0 fsbciegf_1 wb wi fsbciegf_2 esbciegf_1 ax-gen fsbciegf_0 fsbciegf_1 fsbciegf_2 fsbciegf_3 fsbciegf_4 sbciegft mp3an23 $.
$}
$( /* Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 10-Nov-2005.) */

$)
${
	$d x A $.
	$d x ps $.
	fsbcieg_0 $f wff ph $.
	fsbcieg_1 $f wff ps $.
	fsbcieg_2 $f set x $.
	fsbcieg_3 $f class A $.
	fsbcieg_4 $f class V $.
	esbcieg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	sbcieg $p |- ( A e. V -> ( [. A / x ]. ph <-> ps ) ) $= fsbcieg_3 fsbcieg_4 wcel fsbcieg_3 cvv wcel fsbcieg_0 fsbcieg_2 fsbcieg_3 wsbc fsbcieg_1 wb fsbcieg_3 fsbcieg_4 elex fsbcieg_0 fsbcieg_1 fsbcieg_2 fsbcieg_3 cvv fsbcieg_1 fsbcieg_2 nfv esbcieg_0 sbciegf syl $.
$}
$( /* Conversion of implicit substitution to explicit class substitution.
       This version of ~ sbcie avoids a disjointness condition on ` x , A ` by
       substituting twice.  (Contributed by Mario Carneiro, 15-Oct-2016.) */

$)
${
	$d x y $.
	$d A y $.
	$d ch y $.
	$d ph y $.
	$d ps x $.
	fsbcie2g_0 $f wff ph $.
	fsbcie2g_1 $f wff ps $.
	fsbcie2g_2 $f wff ch $.
	fsbcie2g_3 $f set x $.
	fsbcie2g_4 $f set y $.
	fsbcie2g_5 $f class A $.
	fsbcie2g_6 $f class V $.
	esbcie2g_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	esbcie2g_1 $e |- ( y = A -> ( ps <-> ch ) ) $.
	sbcie2g $p |- ( A e. V -> ( [. A / x ]. ph <-> ch ) ) $= fsbcie2g_0 fsbcie2g_3 fsbcie2g_4 sup_set_class wsbc fsbcie2g_1 fsbcie2g_0 fsbcie2g_3 fsbcie2g_5 wsbc fsbcie2g_2 fsbcie2g_4 fsbcie2g_5 fsbcie2g_6 fsbcie2g_0 fsbcie2g_3 fsbcie2g_4 sup_set_class fsbcie2g_5 dfsbcq esbcie2g_1 fsbcie2g_0 fsbcie2g_3 fsbcie2g_4 sup_set_class wsbc fsbcie2g_0 fsbcie2g_3 fsbcie2g_4 wsb fsbcie2g_1 fsbcie2g_0 fsbcie2g_3 fsbcie2g_4 sbsbc fsbcie2g_0 fsbcie2g_1 fsbcie2g_3 fsbcie2g_4 fsbcie2g_1 fsbcie2g_3 nfv esbcie2g_0 sbie bitr3i vtoclbg $.
$}
$( /* Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 4-Sep-2004.) */

$)
${
	$d x A $.
	$d x ps $.
	fsbcie_0 $f wff ph $.
	fsbcie_1 $f wff ps $.
	fsbcie_2 $f set x $.
	fsbcie_3 $f class A $.
	esbcie_0 $e |- A e. _V $.
	esbcie_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	sbcie $p |- ( [. A / x ]. ph <-> ps ) $= fsbcie_3 cvv wcel fsbcie_0 fsbcie_2 fsbcie_3 wsbc fsbcie_1 wb esbcie_0 fsbcie_0 fsbcie_1 fsbcie_2 fsbcie_3 cvv esbcie_1 sbcieg ax-mp $.
$}
$( /* Conversion of implicit substitution to explicit class substitution,
         deduction form.  (Contributed by NM, 29-Dec-2014.) */

$)
${
	$d x A $.
	fsbciedf_0 $f wff ph $.
	fsbciedf_1 $f wff ps $.
	fsbciedf_2 $f wff ch $.
	fsbciedf_3 $f set x $.
	fsbciedf_4 $f class A $.
	fsbciedf_5 $f class V $.
	esbciedf_0 $e |- ( ph -> A e. V ) $.
	esbciedf_1 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	esbciedf_2 $e |- F/ x ph $.
	esbciedf_3 $e |- ( ph -> F/ x ch ) $.
	sbciedf $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $= fsbciedf_0 fsbciedf_4 fsbciedf_5 wcel fsbciedf_2 fsbciedf_3 wnf fsbciedf_3 sup_set_class fsbciedf_4 wceq fsbciedf_1 fsbciedf_2 wb wi fsbciedf_3 wal fsbciedf_1 fsbciedf_3 fsbciedf_4 wsbc fsbciedf_2 wb esbciedf_0 esbciedf_3 fsbciedf_0 fsbciedf_3 sup_set_class fsbciedf_4 wceq fsbciedf_1 fsbciedf_2 wb wi fsbciedf_3 esbciedf_2 fsbciedf_0 fsbciedf_3 sup_set_class fsbciedf_4 wceq fsbciedf_1 fsbciedf_2 wb esbciedf_1 ex alrimi fsbciedf_1 fsbciedf_2 fsbciedf_3 fsbciedf_4 fsbciedf_5 sbciegft syl3anc $.
$}
$( /* Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by NM, 13-Dec-2014.) */

$)
${
	$d x A $.
	$d x ph $.
	$d x ch $.
	fsbcied_0 $f wff ph $.
	fsbcied_1 $f wff ps $.
	fsbcied_2 $f wff ch $.
	fsbcied_3 $f set x $.
	fsbcied_4 $f class A $.
	fsbcied_5 $f class V $.
	esbcied_0 $e |- ( ph -> A e. V ) $.
	esbcied_1 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	sbcied $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $= fsbcied_0 fsbcied_1 fsbcied_2 fsbcied_3 fsbcied_4 fsbcied_5 esbcied_0 esbcied_1 fsbcied_0 fsbcied_3 nfv fsbcied_0 fsbcied_2 fsbcied_3 nfvd sbciedf $.
$}
$( /* Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by NM, 13-Dec-2014.) */

$)
${
	$d x A $.
	$d x ph $.
	$d x ch $.
	fsbcied2_0 $f wff ph $.
	fsbcied2_1 $f wff ps $.
	fsbcied2_2 $f wff ch $.
	fsbcied2_3 $f set x $.
	fsbcied2_4 $f class A $.
	fsbcied2_5 $f class B $.
	fsbcied2_6 $f class V $.
	esbcied2_0 $e |- ( ph -> A e. V ) $.
	esbcied2_1 $e |- ( ph -> A = B ) $.
	esbcied2_2 $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
	sbcied2 $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $= fsbcied2_0 fsbcied2_1 fsbcied2_2 fsbcied2_3 fsbcied2_4 fsbcied2_6 esbcied2_0 fsbcied2_0 fsbcied2_3 sup_set_class fsbcied2_4 wceq fsbcied2_3 sup_set_class fsbcied2_5 wceq fsbcied2_1 fsbcied2_2 wb fsbcied2_3 sup_set_class fsbcied2_4 wceq fsbcied2_0 fsbcied2_3 sup_set_class fsbcied2_4 fsbcied2_5 fsbcied2_3 sup_set_class fsbcied2_4 wceq id esbcied2_1 sylan9eqr esbcied2_2 syldan sbcied $.
$}
$( /* Membership in a restricted class abstraction, expressed with explicit
       class substitution.  (The variation ~ elrabf has implicit
       substitution).  The hypothesis specifies that ` x ` must not be a free
       variable in ` B ` .  (Contributed by NM, 30-Sep-2003.)  (Proof shortened
       by Mario Carneiro, 13-Oct-2016.) */

$)
${
	$d y A $.
	$d y B $.
	$d y ph $.
	$d x y $.
	ielrabsf_0 $f set y $.
	felrabsf_0 $f wff ph $.
	felrabsf_1 $f set x $.
	felrabsf_2 $f class A $.
	felrabsf_3 $f class B $.
	eelrabsf_0 $e |- F/_ x B $.
	elrabsf $p |- ( A e. { x e. B | ph } <-> ( A e. B /\ [. A / x ]. ph ) ) $= felrabsf_0 felrabsf_1 ielrabsf_0 sup_set_class wsbc felrabsf_0 felrabsf_1 felrabsf_2 wsbc ielrabsf_0 felrabsf_2 felrabsf_3 felrabsf_0 felrabsf_1 felrabsf_3 crab felrabsf_0 felrabsf_1 ielrabsf_0 sup_set_class felrabsf_2 dfsbcq felrabsf_0 felrabsf_0 felrabsf_1 ielrabsf_0 sup_set_class wsbc felrabsf_1 ielrabsf_0 felrabsf_3 eelrabsf_0 ielrabsf_0 felrabsf_3 nfcv felrabsf_0 ielrabsf_0 nfv felrabsf_0 felrabsf_1 ielrabsf_0 sup_set_class nfsbc1v felrabsf_0 felrabsf_1 ielrabsf_0 sup_set_class sbceq1a cbvrab elrab2 $.
$}
$( /* Substitution applied to an atomic wff.  Set theory version of ~ eqsb3 .
       (Contributed by Andrew Salmon, 29-Jun-2011.) */

$)
${
	$d x y B $.
	$d y A $.
	ieqsbc3_0 $f set y $.
	feqsbc3_0 $f set x $.
	feqsbc3_1 $f class A $.
	feqsbc3_2 $f class B $.
	feqsbc3_3 $f class V $.
	eqsbc3 $p |- ( A e. V -> ( [. A / x ]. x = B <-> A = B ) ) $= feqsbc3_0 sup_set_class feqsbc3_2 wceq feqsbc3_0 ieqsbc3_0 sup_set_class wsbc ieqsbc3_0 sup_set_class feqsbc3_2 wceq feqsbc3_0 sup_set_class feqsbc3_2 wceq feqsbc3_0 feqsbc3_1 wsbc feqsbc3_1 feqsbc3_2 wceq ieqsbc3_0 feqsbc3_1 feqsbc3_3 feqsbc3_0 sup_set_class feqsbc3_2 wceq feqsbc3_0 ieqsbc3_0 sup_set_class feqsbc3_1 dfsbcq ieqsbc3_0 sup_set_class feqsbc3_1 feqsbc3_2 eqeq1 feqsbc3_0 sup_set_class feqsbc3_2 wceq feqsbc3_0 ieqsbc3_0 sup_set_class wsbc feqsbc3_0 sup_set_class feqsbc3_2 wceq feqsbc3_0 ieqsbc3_0 wsb ieqsbc3_0 sup_set_class feqsbc3_2 wceq feqsbc3_0 sup_set_class feqsbc3_2 wceq feqsbc3_0 ieqsbc3_0 sbsbc ieqsbc3_0 feqsbc3_0 feqsbc3_2 eqsb3 bitr3i vtoclbg $.
$}
$( /* Move negation in and out of class substitution.  (Contributed by NM,
       16-Jan-2004.) */

$)
${
	$d x y $.
	$d y A $.
	$d y ph $.
	isbcng_0 $f set y $.
	fsbcng_0 $f wff ph $.
	fsbcng_1 $f set x $.
	fsbcng_2 $f class A $.
	fsbcng_3 $f class V $.
	sbcng $p |- ( A e. V -> ( [. A / x ]. -. ph <-> -. [. A / x ]. ph ) ) $= fsbcng_0 wn fsbcng_1 isbcng_0 wsb fsbcng_0 fsbcng_1 isbcng_0 wsb wn fsbcng_0 wn fsbcng_1 fsbcng_2 wsbc fsbcng_0 fsbcng_1 fsbcng_2 wsbc wn isbcng_0 fsbcng_2 fsbcng_3 fsbcng_0 wn fsbcng_1 isbcng_0 fsbcng_2 dfsbcq2 isbcng_0 sup_set_class fsbcng_2 wceq fsbcng_0 fsbcng_1 isbcng_0 wsb fsbcng_0 fsbcng_1 fsbcng_2 wsbc fsbcng_0 fsbcng_1 isbcng_0 fsbcng_2 dfsbcq2 notbid fsbcng_0 fsbcng_1 isbcng_0 sbn vtoclbg $.
$}
$( /* Distribution of class substitution over implication.  (Contributed by
       NM, 16-Jan-2004.) */

$)
${
	$d x y $.
	$d y A $.
	$d y ph $.
	$d y ps $.
	isbcimg_0 $f set y $.
	fsbcimg_0 $f wff ph $.
	fsbcimg_1 $f wff ps $.
	fsbcimg_2 $f set x $.
	fsbcimg_3 $f class A $.
	fsbcimg_4 $f class V $.
	sbcimg $p |- ( A e. V -> ( [. A / x ]. ( ph -> ps ) <-> ( [. A / x ]. ph -> [. A / x ]. ps ) ) ) $= fsbcimg_0 fsbcimg_1 wi fsbcimg_2 isbcimg_0 wsb fsbcimg_0 fsbcimg_2 isbcimg_0 wsb fsbcimg_1 fsbcimg_2 isbcimg_0 wsb wi fsbcimg_0 fsbcimg_1 wi fsbcimg_2 fsbcimg_3 wsbc fsbcimg_0 fsbcimg_2 fsbcimg_3 wsbc fsbcimg_1 fsbcimg_2 fsbcimg_3 wsbc wi isbcimg_0 fsbcimg_3 fsbcimg_4 fsbcimg_0 fsbcimg_1 wi fsbcimg_2 isbcimg_0 fsbcimg_3 dfsbcq2 isbcimg_0 sup_set_class fsbcimg_3 wceq fsbcimg_0 fsbcimg_2 isbcimg_0 wsb fsbcimg_0 fsbcimg_2 fsbcimg_3 wsbc fsbcimg_1 fsbcimg_2 isbcimg_0 wsb fsbcimg_1 fsbcimg_2 fsbcimg_3 wsbc fsbcimg_0 fsbcimg_2 isbcimg_0 fsbcimg_3 dfsbcq2 fsbcimg_1 fsbcimg_2 isbcimg_0 fsbcimg_3 dfsbcq2 imbi12d fsbcimg_0 fsbcimg_1 fsbcimg_2 isbcimg_0 sbim vtoclbg $.
$}
$( /* Distribution of class substitution over conjunction.  (Contributed by
       NM, 31-Dec-2016.) */

$)
${
	$d x y $.
	$d y A $.
	$d y ph $.
	$d y ps $.
	isbcan_0 $f set y $.
	fsbcan_0 $f wff ph $.
	fsbcan_1 $f wff ps $.
	fsbcan_2 $f set x $.
	fsbcan_3 $f class A $.
	sbcan $p |- ( [. A / x ]. ( ph /\ ps ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps ) ) $= fsbcan_0 fsbcan_1 wa fsbcan_2 fsbcan_3 wsbc fsbcan_3 cvv wcel fsbcan_0 fsbcan_2 fsbcan_3 wsbc fsbcan_1 fsbcan_2 fsbcan_3 wsbc wa fsbcan_0 fsbcan_1 wa fsbcan_2 fsbcan_3 sbcex fsbcan_1 fsbcan_2 fsbcan_3 wsbc fsbcan_3 cvv wcel fsbcan_0 fsbcan_2 fsbcan_3 wsbc fsbcan_1 fsbcan_2 fsbcan_3 sbcex adantl fsbcan_0 fsbcan_1 wa fsbcan_2 isbcan_0 wsb fsbcan_0 fsbcan_2 isbcan_0 wsb fsbcan_1 fsbcan_2 isbcan_0 wsb wa fsbcan_0 fsbcan_1 wa fsbcan_2 fsbcan_3 wsbc fsbcan_0 fsbcan_2 fsbcan_3 wsbc fsbcan_1 fsbcan_2 fsbcan_3 wsbc wa isbcan_0 fsbcan_3 cvv fsbcan_0 fsbcan_1 wa fsbcan_2 isbcan_0 fsbcan_3 dfsbcq2 isbcan_0 sup_set_class fsbcan_3 wceq fsbcan_0 fsbcan_2 isbcan_0 wsb fsbcan_0 fsbcan_2 fsbcan_3 wsbc fsbcan_1 fsbcan_2 isbcan_0 wsb fsbcan_1 fsbcan_2 fsbcan_3 wsbc fsbcan_0 fsbcan_2 isbcan_0 fsbcan_3 dfsbcq2 fsbcan_1 fsbcan_2 isbcan_0 fsbcan_3 dfsbcq2 anbi12d fsbcan_0 fsbcan_1 fsbcan_2 isbcan_0 sban vtoclbg pm5.21nii $.
$}
$( /* Distribution of class substitution over conjunction.  (Contributed by
       NM, 21-May-2004.) */

$)
${
	$d x y $.
	$d y A $.
	$d y ph $.
	$d y ps $.
	isbcang_0 $f set y $.
	fsbcang_0 $f wff ph $.
	fsbcang_1 $f wff ps $.
	fsbcang_2 $f set x $.
	fsbcang_3 $f class A $.
	fsbcang_4 $f class V $.
	sbcang $p |- ( A e. V -> ( [. A / x ]. ( ph /\ ps ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps ) ) ) $= fsbcang_0 fsbcang_1 wa fsbcang_2 isbcang_0 wsb fsbcang_0 fsbcang_2 isbcang_0 wsb fsbcang_1 fsbcang_2 isbcang_0 wsb wa fsbcang_0 fsbcang_1 wa fsbcang_2 fsbcang_3 wsbc fsbcang_0 fsbcang_2 fsbcang_3 wsbc fsbcang_1 fsbcang_2 fsbcang_3 wsbc wa isbcang_0 fsbcang_3 fsbcang_4 fsbcang_0 fsbcang_1 wa fsbcang_2 isbcang_0 fsbcang_3 dfsbcq2 isbcang_0 sup_set_class fsbcang_3 wceq fsbcang_0 fsbcang_2 isbcang_0 wsb fsbcang_0 fsbcang_2 fsbcang_3 wsbc fsbcang_1 fsbcang_2 isbcang_0 wsb fsbcang_1 fsbcang_2 fsbcang_3 wsbc fsbcang_0 fsbcang_2 isbcang_0 fsbcang_3 dfsbcq2 fsbcang_1 fsbcang_2 isbcang_0 fsbcang_3 dfsbcq2 anbi12d fsbcang_0 fsbcang_1 fsbcang_2 isbcang_0 sban vtoclbg $.
$}
$( /* Distribution of class substitution over disjunction.  (Contributed by
       NM, 31-Dec-2016.) */

$)
${
	$d x y $.
	$d y A $.
	$d y ph $.
	$d y ps $.
	isbcor_0 $f set y $.
	fsbcor_0 $f wff ph $.
	fsbcor_1 $f wff ps $.
	fsbcor_2 $f set x $.
	fsbcor_3 $f class A $.
	sbcor $p |- ( [. A / x ]. ( ph \/ ps ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) ) $= fsbcor_0 fsbcor_1 wo fsbcor_2 fsbcor_3 wsbc fsbcor_3 cvv wcel fsbcor_0 fsbcor_2 fsbcor_3 wsbc fsbcor_1 fsbcor_2 fsbcor_3 wsbc wo fsbcor_0 fsbcor_1 wo fsbcor_2 fsbcor_3 sbcex fsbcor_0 fsbcor_2 fsbcor_3 wsbc fsbcor_3 cvv wcel fsbcor_1 fsbcor_2 fsbcor_3 wsbc fsbcor_0 fsbcor_2 fsbcor_3 sbcex fsbcor_1 fsbcor_2 fsbcor_3 sbcex jaoi fsbcor_0 fsbcor_1 wo fsbcor_2 isbcor_0 wsb fsbcor_0 fsbcor_2 isbcor_0 wsb fsbcor_1 fsbcor_2 isbcor_0 wsb wo fsbcor_0 fsbcor_1 wo fsbcor_2 fsbcor_3 wsbc fsbcor_0 fsbcor_2 fsbcor_3 wsbc fsbcor_1 fsbcor_2 fsbcor_3 wsbc wo isbcor_0 fsbcor_3 cvv fsbcor_0 fsbcor_1 wo fsbcor_2 isbcor_0 fsbcor_3 dfsbcq2 isbcor_0 sup_set_class fsbcor_3 wceq fsbcor_0 fsbcor_2 isbcor_0 wsb fsbcor_0 fsbcor_2 fsbcor_3 wsbc fsbcor_1 fsbcor_2 isbcor_0 wsb fsbcor_1 fsbcor_2 fsbcor_3 wsbc fsbcor_0 fsbcor_2 isbcor_0 fsbcor_3 dfsbcq2 fsbcor_1 fsbcor_2 isbcor_0 fsbcor_3 dfsbcq2 orbi12d fsbcor_0 fsbcor_1 fsbcor_2 isbcor_0 sbor vtoclbg pm5.21nii $.
$}
$( /* Distribution of class substitution over disjunction.  (Contributed by
       NM, 21-May-2004.) */

$)
${
	$d x y $.
	$d y A $.
	$d y ph $.
	$d y ps $.
	isbcorg_0 $f set y $.
	fsbcorg_0 $f wff ph $.
	fsbcorg_1 $f wff ps $.
	fsbcorg_2 $f set x $.
	fsbcorg_3 $f class A $.
	fsbcorg_4 $f class V $.
	sbcorg $p |- ( A e. V -> ( [. A / x ]. ( ph \/ ps ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) ) ) $= fsbcorg_0 fsbcorg_1 wo fsbcorg_2 isbcorg_0 wsb fsbcorg_0 fsbcorg_2 isbcorg_0 wsb fsbcorg_1 fsbcorg_2 isbcorg_0 wsb wo fsbcorg_0 fsbcorg_1 wo fsbcorg_2 fsbcorg_3 wsbc fsbcorg_0 fsbcorg_2 fsbcorg_3 wsbc fsbcorg_1 fsbcorg_2 fsbcorg_3 wsbc wo isbcorg_0 fsbcorg_3 fsbcorg_4 fsbcorg_0 fsbcorg_1 wo fsbcorg_2 isbcorg_0 fsbcorg_3 dfsbcq2 isbcorg_0 sup_set_class fsbcorg_3 wceq fsbcorg_0 fsbcorg_2 isbcorg_0 wsb fsbcorg_0 fsbcorg_2 fsbcorg_3 wsbc fsbcorg_1 fsbcorg_2 isbcorg_0 wsb fsbcorg_1 fsbcorg_2 fsbcorg_3 wsbc fsbcorg_0 fsbcorg_2 isbcorg_0 fsbcorg_3 dfsbcq2 fsbcorg_1 fsbcorg_2 isbcorg_0 fsbcorg_3 dfsbcq2 orbi12d fsbcorg_0 fsbcorg_1 fsbcorg_2 isbcorg_0 sbor vtoclbg $.
$}
$( /* Distribution of class substitution over biconditional.  (Contributed by
       Raph Levien, 10-Apr-2004.) */

$)
${
	$d x y $.
	$d y A $.
	$d y ph $.
	$d y ps $.
	isbcbig_0 $f set y $.
	fsbcbig_0 $f wff ph $.
	fsbcbig_1 $f wff ps $.
	fsbcbig_2 $f set x $.
	fsbcbig_3 $f class A $.
	fsbcbig_4 $f class V $.
	sbcbig $p |- ( A e. V -> ( [. A / x ]. ( ph <-> ps ) <-> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) ) $= fsbcbig_0 fsbcbig_1 wb fsbcbig_2 isbcbig_0 wsb fsbcbig_0 fsbcbig_2 isbcbig_0 wsb fsbcbig_1 fsbcbig_2 isbcbig_0 wsb wb fsbcbig_0 fsbcbig_1 wb fsbcbig_2 fsbcbig_3 wsbc fsbcbig_0 fsbcbig_2 fsbcbig_3 wsbc fsbcbig_1 fsbcbig_2 fsbcbig_3 wsbc wb isbcbig_0 fsbcbig_3 fsbcbig_4 fsbcbig_0 fsbcbig_1 wb fsbcbig_2 isbcbig_0 fsbcbig_3 dfsbcq2 isbcbig_0 sup_set_class fsbcbig_3 wceq fsbcbig_0 fsbcbig_2 isbcbig_0 wsb fsbcbig_0 fsbcbig_2 fsbcbig_3 wsbc fsbcbig_1 fsbcbig_2 isbcbig_0 wsb fsbcbig_1 fsbcbig_2 fsbcbig_3 wsbc fsbcbig_0 fsbcbig_2 isbcbig_0 fsbcbig_3 dfsbcq2 fsbcbig_1 fsbcbig_2 isbcbig_0 fsbcbig_3 dfsbcq2 bibi12d fsbcbig_0 fsbcbig_1 fsbcbig_2 isbcbig_0 sbbi vtoclbg $.
$}
$( /* Move universal quantifier in and out of class substitution.
       (Contributed by NM, 31-Dec-2016.) */

$)
${
	$d x z A $.
	$d x y z $.
	$d z ph $.
	isbcal_0 $f set z $.
	fsbcal_0 $f wff ph $.
	fsbcal_1 $f set x $.
	fsbcal_2 $f set y $.
	fsbcal_3 $f class A $.
	sbcal $p |- ( [. A / y ]. A. x ph <-> A. x [. A / y ]. ph ) $= fsbcal_0 fsbcal_1 wal fsbcal_2 fsbcal_3 wsbc fsbcal_3 cvv wcel fsbcal_0 fsbcal_2 fsbcal_3 wsbc fsbcal_1 wal fsbcal_0 fsbcal_1 wal fsbcal_2 fsbcal_3 sbcex fsbcal_0 fsbcal_2 fsbcal_3 wsbc fsbcal_3 cvv wcel fsbcal_1 fsbcal_0 fsbcal_2 fsbcal_3 sbcex sps fsbcal_0 fsbcal_1 wal fsbcal_2 isbcal_0 wsb fsbcal_0 fsbcal_2 isbcal_0 wsb fsbcal_1 wal fsbcal_0 fsbcal_1 wal fsbcal_2 fsbcal_3 wsbc fsbcal_0 fsbcal_2 fsbcal_3 wsbc fsbcal_1 wal isbcal_0 fsbcal_3 cvv fsbcal_0 fsbcal_1 wal fsbcal_2 isbcal_0 fsbcal_3 dfsbcq2 isbcal_0 sup_set_class fsbcal_3 wceq fsbcal_0 fsbcal_2 isbcal_0 wsb fsbcal_0 fsbcal_2 fsbcal_3 wsbc fsbcal_1 fsbcal_0 fsbcal_2 isbcal_0 fsbcal_3 dfsbcq2 albidv fsbcal_0 fsbcal_1 fsbcal_2 isbcal_0 sbal vtoclbg pm5.21nii $.
$}
$( /* Move universal quantifier in and out of class substitution.
       (Contributed by NM, 16-Jan-2004.) */

$)
${
	$d x z A $.
	$d x y z $.
	$d z ph $.
	isbcalg_0 $f set z $.
	fsbcalg_0 $f wff ph $.
	fsbcalg_1 $f set x $.
	fsbcalg_2 $f set y $.
	fsbcalg_3 $f class A $.
	fsbcalg_4 $f class V $.
	sbcalg $p |- ( A e. V -> ( [. A / y ]. A. x ph <-> A. x [. A / y ]. ph ) ) $= fsbcalg_0 fsbcalg_1 wal fsbcalg_2 isbcalg_0 wsb fsbcalg_0 fsbcalg_2 isbcalg_0 wsb fsbcalg_1 wal fsbcalg_0 fsbcalg_1 wal fsbcalg_2 fsbcalg_3 wsbc fsbcalg_0 fsbcalg_2 fsbcalg_3 wsbc fsbcalg_1 wal isbcalg_0 fsbcalg_3 fsbcalg_4 fsbcalg_0 fsbcalg_1 wal fsbcalg_2 isbcalg_0 fsbcalg_3 dfsbcq2 isbcalg_0 sup_set_class fsbcalg_3 wceq fsbcalg_0 fsbcalg_2 isbcalg_0 wsb fsbcalg_0 fsbcalg_2 fsbcalg_3 wsbc fsbcalg_1 fsbcalg_0 fsbcalg_2 isbcalg_0 fsbcalg_3 dfsbcq2 albidv fsbcalg_0 fsbcalg_1 fsbcalg_2 isbcalg_0 sbal vtoclbg $.
$}
$( /* Move existential quantifier in and out of class substitution.
       (Contributed by NM, 21-May-2004.) */

$)
${
	$d x z A $.
	$d x y z $.
	$d z ph $.
	isbcex2_0 $f set z $.
	fsbcex2_0 $f wff ph $.
	fsbcex2_1 $f set x $.
	fsbcex2_2 $f set y $.
	fsbcex2_3 $f class A $.
	sbcex2 $p |- ( [. A / y ]. E. x ph <-> E. x [. A / y ]. ph ) $= fsbcex2_0 fsbcex2_1 wex fsbcex2_2 fsbcex2_3 wsbc fsbcex2_3 cvv wcel fsbcex2_0 fsbcex2_2 fsbcex2_3 wsbc fsbcex2_1 wex fsbcex2_0 fsbcex2_1 wex fsbcex2_2 fsbcex2_3 sbcex fsbcex2_0 fsbcex2_2 fsbcex2_3 wsbc fsbcex2_3 cvv wcel fsbcex2_1 fsbcex2_0 fsbcex2_2 fsbcex2_3 sbcex exlimiv fsbcex2_0 fsbcex2_1 wex fsbcex2_2 isbcex2_0 wsb fsbcex2_0 fsbcex2_2 isbcex2_0 wsb fsbcex2_1 wex fsbcex2_0 fsbcex2_1 wex fsbcex2_2 fsbcex2_3 wsbc fsbcex2_0 fsbcex2_2 fsbcex2_3 wsbc fsbcex2_1 wex isbcex2_0 fsbcex2_3 cvv fsbcex2_0 fsbcex2_1 wex fsbcex2_2 isbcex2_0 fsbcex2_3 dfsbcq2 isbcex2_0 sup_set_class fsbcex2_3 wceq fsbcex2_0 fsbcex2_2 isbcex2_0 wsb fsbcex2_0 fsbcex2_2 fsbcex2_3 wsbc fsbcex2_1 fsbcex2_0 fsbcex2_2 isbcex2_0 fsbcex2_3 dfsbcq2 exbidv fsbcex2_0 fsbcex2_1 fsbcex2_2 isbcex2_0 sbex vtoclbg pm5.21nii $.
$}
$( /* Move existential quantifier in and out of class substitution.
       (Contributed by NM, 21-May-2004.) */

$)
${
	$d x z A $.
	$d x y z $.
	$d z ph $.
	isbcexg_0 $f set z $.
	fsbcexg_0 $f wff ph $.
	fsbcexg_1 $f set x $.
	fsbcexg_2 $f set y $.
	fsbcexg_3 $f class A $.
	fsbcexg_4 $f class V $.
	sbcexg $p |- ( A e. V -> ( [. A / y ]. E. x ph <-> E. x [. A / y ]. ph ) ) $= fsbcexg_0 fsbcexg_1 wex fsbcexg_2 isbcexg_0 wsb fsbcexg_0 fsbcexg_2 isbcexg_0 wsb fsbcexg_1 wex fsbcexg_0 fsbcexg_1 wex fsbcexg_2 fsbcexg_3 wsbc fsbcexg_0 fsbcexg_2 fsbcexg_3 wsbc fsbcexg_1 wex isbcexg_0 fsbcexg_3 fsbcexg_4 fsbcexg_0 fsbcexg_1 wex fsbcexg_2 isbcexg_0 fsbcexg_3 dfsbcq2 isbcexg_0 sup_set_class fsbcexg_3 wceq fsbcexg_0 fsbcexg_2 isbcexg_0 wsb fsbcexg_0 fsbcexg_2 fsbcexg_3 wsbc fsbcexg_1 fsbcexg_0 fsbcexg_2 isbcexg_0 fsbcexg_3 dfsbcq2 exbidv fsbcexg_0 fsbcexg_1 fsbcexg_2 isbcexg_0 sbex vtoclbg $.
$}
$( /* Set theory version of ~ sbeqal1 .  (Contributed by Andrew Salmon,
       28-Jun-2011.) */

$)
${
	$d x B $.
	$d x A $.
	fsbceqal_0 $f set x $.
	fsbceqal_1 $f class A $.
	fsbceqal_2 $f class B $.
	fsbceqal_3 $f class V $.
	sbceqal $p |- ( A e. V -> ( A. x ( x = A -> x = B ) -> A = B ) ) $= fsbceqal_1 fsbceqal_3 wcel fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 sup_set_class fsbceqal_2 wceq wi fsbceqal_0 wal fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 sup_set_class fsbceqal_2 wceq wi fsbceqal_0 fsbceqal_1 wsbc fsbceqal_1 fsbceqal_2 wceq fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 sup_set_class fsbceqal_2 wceq wi fsbceqal_0 fsbceqal_1 fsbceqal_3 spsbc fsbceqal_1 fsbceqal_3 wcel fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 sup_set_class fsbceqal_2 wceq wi fsbceqal_0 fsbceqal_1 wsbc fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 fsbceqal_1 wsbc fsbceqal_0 sup_set_class fsbceqal_2 wceq fsbceqal_0 fsbceqal_1 wsbc wi fsbceqal_0 sup_set_class fsbceqal_2 wceq fsbceqal_0 fsbceqal_1 wsbc fsbceqal_1 fsbceqal_2 wceq fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 sup_set_class fsbceqal_2 wceq fsbceqal_0 fsbceqal_1 fsbceqal_3 sbcimg fsbceqal_1 fsbceqal_3 wcel fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 fsbceqal_1 wsbc fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 fsbceqal_1 wsbc fsbceqal_0 sup_set_class fsbceqal_2 wceq fsbceqal_0 fsbceqal_1 wsbc wi fsbceqal_0 sup_set_class fsbceqal_2 wceq fsbceqal_0 fsbceqal_1 wsbc wb fsbceqal_1 fsbceqal_3 wcel fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 fsbceqal_1 wsbc fsbceqal_1 fsbceqal_1 wceq fsbceqal_1 eqid fsbceqal_0 fsbceqal_1 fsbceqal_1 fsbceqal_3 eqsbc3 mpbiri fsbceqal_0 sup_set_class fsbceqal_1 wceq fsbceqal_0 fsbceqal_1 wsbc fsbceqal_0 sup_set_class fsbceqal_2 wceq fsbceqal_0 fsbceqal_1 wsbc pm5.5 syl fsbceqal_0 fsbceqal_1 fsbceqal_2 fsbceqal_3 eqsbc3 3bitrd sylibd $.
$}
$( /* Theorem *14.121 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 28-Jun-2011.)  (Proof shortened by Wolf Lammen, 9-May-2013.) */

$)
${
	$d x A $.
	$d x B $.
	fsbeqalb_0 $f wff ph $.
	fsbeqalb_1 $f set x $.
	fsbeqalb_2 $f class A $.
	fsbeqalb_3 $f class B $.
	fsbeqalb_4 $f class V $.
	sbeqalb $p |- ( A e. V -> ( ( A. x ( ph <-> x = A ) /\ A. x ( ph <-> x = B ) ) -> A = B ) ) $= fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_2 wceq wb fsbeqalb_1 wal fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_3 wceq wb fsbeqalb_1 wal wa fsbeqalb_1 sup_set_class fsbeqalb_2 wceq fsbeqalb_1 sup_set_class fsbeqalb_3 wceq wi fsbeqalb_1 wal fsbeqalb_2 fsbeqalb_4 wcel fsbeqalb_2 fsbeqalb_3 wceq fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_2 wceq wb fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_3 wceq wb fsbeqalb_1 sup_set_class fsbeqalb_2 wceq fsbeqalb_1 sup_set_class fsbeqalb_3 wceq wi fsbeqalb_1 fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_2 wceq wb fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_3 wceq wb wa fsbeqalb_1 sup_set_class fsbeqalb_2 wceq fsbeqalb_1 sup_set_class fsbeqalb_3 wceq fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_2 wceq wb fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_3 wceq wb fsbeqalb_1 sup_set_class fsbeqalb_2 wceq fsbeqalb_1 sup_set_class fsbeqalb_3 wceq wb fsbeqalb_0 fsbeqalb_1 sup_set_class fsbeqalb_2 wceq fsbeqalb_1 sup_set_class fsbeqalb_3 wceq bibi1 biimpa biimpd alanimi fsbeqalb_1 fsbeqalb_2 fsbeqalb_3 fsbeqalb_4 sbceqal syl5 $.
$}
$( /* Formula-building deduction rule for class substitution.  (Contributed by
       NM, 29-Dec-2014.) */

$)
${
	fsbcbid_0 $f wff ph $.
	fsbcbid_1 $f wff ps $.
	fsbcbid_2 $f wff ch $.
	fsbcbid_3 $f set x $.
	fsbcbid_4 $f class A $.
	esbcbid_0 $e |- F/ x ph $.
	esbcbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	sbcbid $p |- ( ph -> ( [. A / x ]. ps <-> [. A / x ]. ch ) ) $= fsbcbid_0 fsbcbid_4 fsbcbid_1 fsbcbid_3 cab wcel fsbcbid_4 fsbcbid_2 fsbcbid_3 cab wcel fsbcbid_1 fsbcbid_3 fsbcbid_4 wsbc fsbcbid_2 fsbcbid_3 fsbcbid_4 wsbc fsbcbid_0 fsbcbid_1 fsbcbid_3 cab fsbcbid_2 fsbcbid_3 cab fsbcbid_4 fsbcbid_0 fsbcbid_1 fsbcbid_2 fsbcbid_3 esbcbid_0 esbcbid_1 abbid eleq2d fsbcbid_1 fsbcbid_3 fsbcbid_4 df-sbc fsbcbid_2 fsbcbid_3 fsbcbid_4 df-sbc 3bitr4g $.
$}
$( /* Formula-building deduction rule for class substitution.  (Contributed by
       NM, 29-Dec-2014.) */

$)
${
	$d x ph $.
	fsbcbidv_0 $f wff ph $.
	fsbcbidv_1 $f wff ps $.
	fsbcbidv_2 $f wff ch $.
	fsbcbidv_3 $f set x $.
	fsbcbidv_4 $f class A $.
	esbcbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	sbcbidv $p |- ( ph -> ( [. A / x ]. ps <-> [. A / x ]. ch ) ) $= fsbcbidv_0 fsbcbidv_1 fsbcbidv_2 fsbcbidv_3 fsbcbidv_4 fsbcbidv_0 fsbcbidv_3 nfv esbcbidv_0 sbcbid $.
$}
$( /* Formula-building inference rule for class substitution.  (Contributed by
       NM, 11-Nov-2005.) */

$)
${
	fsbcbii_0 $f wff ph $.
	fsbcbii_1 $f wff ps $.
	fsbcbii_2 $f set x $.
	fsbcbii_3 $f class A $.
	esbcbii_0 $e |- ( ph <-> ps ) $.
	sbcbii $p |- ( [. A / x ]. ph <-> [. A / x ]. ps ) $= fsbcbii_0 fsbcbii_2 fsbcbii_3 wsbc fsbcbii_1 fsbcbii_2 fsbcbii_3 wsbc wb wtru fsbcbii_0 fsbcbii_1 fsbcbii_2 fsbcbii_3 fsbcbii_0 fsbcbii_1 wb wtru esbcbii_0 a1i sbcbidv trud $.
$}
$( /* Formula-building inference rule for class substitution.  (Contributed by
       NM, 11-Nov-2005.)  (New usage is discouraged.) */

$)
${
	fsbcbiiOLD_0 $f wff ph $.
	fsbcbiiOLD_1 $f wff ps $.
	fsbcbiiOLD_2 $f set x $.
	fsbcbiiOLD_3 $f class A $.
	fsbcbiiOLD_4 $f class V $.
	esbcbiiOLD_0 $e |- ( ph <-> ps ) $.
	sbcbiiOLD $p |- ( A e. V -> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) $= fsbcbiiOLD_0 fsbcbiiOLD_2 fsbcbiiOLD_3 wsbc fsbcbiiOLD_1 fsbcbiiOLD_2 fsbcbiiOLD_3 wsbc wb fsbcbiiOLD_3 fsbcbiiOLD_4 wcel fsbcbiiOLD_0 fsbcbiiOLD_1 fsbcbiiOLD_2 fsbcbiiOLD_3 esbcbiiOLD_0 sbcbii a1i $.
$}
$( /* ~ eqsbc3 with set variable on right side of equals sign.  This proof was
       automatically generated from the virtual deduction proof ~ eqsbc3rVD
       using a translation program.  (Contributed by Alan Sare,
       24-Oct-2011.) */

$)
${
	$d x C $.
	$d x A $.
	feqsbc3r_0 $f set x $.
	feqsbc3r_1 $f class A $.
	feqsbc3r_2 $f class B $.
	feqsbc3r_3 $f class C $.
	eqsbc3r $p |- ( A e. B -> ( [. A / x ]. C = x <-> C = A ) ) $= feqsbc3r_1 feqsbc3r_2 wcel feqsbc3r_3 feqsbc3r_0 sup_set_class wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_3 feqsbc3r_1 wceq feqsbc3r_1 feqsbc3r_2 wcel feqsbc3r_3 feqsbc3r_0 sup_set_class wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_1 feqsbc3r_3 wceq feqsbc3r_3 feqsbc3r_1 wceq feqsbc3r_3 feqsbc3r_0 sup_set_class wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_0 sup_set_class feqsbc3r_3 wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_1 feqsbc3r_2 wcel feqsbc3r_1 feqsbc3r_3 wceq feqsbc3r_3 feqsbc3r_0 sup_set_class wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_0 sup_set_class feqsbc3r_3 wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_3 feqsbc3r_0 sup_set_class wceq feqsbc3r_0 sup_set_class feqsbc3r_3 wceq feqsbc3r_0 feqsbc3r_1 feqsbc3r_3 feqsbc3r_0 sup_set_class eqcom sbcbii biimpi feqsbc3r_0 feqsbc3r_1 feqsbc3r_3 feqsbc3r_2 eqsbc3 syl5ib feqsbc3r_1 feqsbc3r_3 eqcom syl6ib feqsbc3r_1 feqsbc3r_2 wcel feqsbc3r_3 feqsbc3r_1 wceq feqsbc3r_0 sup_set_class feqsbc3r_3 wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_3 feqsbc3r_0 sup_set_class wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_1 feqsbc3r_2 wcel feqsbc3r_3 feqsbc3r_1 wceq feqsbc3r_1 feqsbc3r_3 wceq feqsbc3r_0 sup_set_class feqsbc3r_3 wceq feqsbc3r_0 feqsbc3r_1 wsbc feqsbc3r_1 feqsbc3r_2 wcel feqsbc3r_3 feqsbc3r_1 wceq feqsbc3r_3 feqsbc3r_1 wceq feqsbc3r_1 feqsbc3r_3 wceq feqsbc3r_1 feqsbc3r_2 wcel feqsbc3r_3 feqsbc3r_1 wceq idd feqsbc3r_1 feqsbc3r_3 eqcom syl6ibr feqsbc3r_0 feqsbc3r_1 feqsbc3r_3 feqsbc3r_2 eqsbc3 sylibrd feqsbc3r_3 feqsbc3r_0 sup_set_class wceq feqsbc3r_0 sup_set_class feqsbc3r_3 wceq feqsbc3r_0 feqsbc3r_1 feqsbc3r_3 feqsbc3r_0 sup_set_class eqcom sbcbii syl6ibr impbid $.
$}
$( /* Distribution of class substitution over triple conjunction.
       (Contributed by NM, 14-Dec-2006.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) */

$)
${
	$d y ch $.
	$d y ps $.
	$d y ph $.
	$d y A $.
	$d x y $.
	isbc3ang_0 $f set y $.
	fsbc3ang_0 $f wff ph $.
	fsbc3ang_1 $f wff ps $.
	fsbc3ang_2 $f wff ch $.
	fsbc3ang_3 $f set x $.
	fsbc3ang_4 $f class A $.
	fsbc3ang_5 $f class V $.
	sbc3ang $p |- ( A e. V -> ( [. A / x ]. ( ph /\ ps /\ ch ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps /\ [. A / x ]. ch ) ) ) $= fsbc3ang_0 fsbc3ang_1 fsbc3ang_2 w3a fsbc3ang_3 isbc3ang_0 wsb fsbc3ang_0 fsbc3ang_3 isbc3ang_0 wsb fsbc3ang_1 fsbc3ang_3 isbc3ang_0 wsb fsbc3ang_2 fsbc3ang_3 isbc3ang_0 wsb w3a fsbc3ang_0 fsbc3ang_1 fsbc3ang_2 w3a fsbc3ang_3 fsbc3ang_4 wsbc fsbc3ang_0 fsbc3ang_3 fsbc3ang_4 wsbc fsbc3ang_1 fsbc3ang_3 fsbc3ang_4 wsbc fsbc3ang_2 fsbc3ang_3 fsbc3ang_4 wsbc w3a isbc3ang_0 fsbc3ang_4 fsbc3ang_5 fsbc3ang_0 fsbc3ang_1 fsbc3ang_2 w3a fsbc3ang_3 isbc3ang_0 fsbc3ang_4 dfsbcq2 isbc3ang_0 sup_set_class fsbc3ang_4 wceq fsbc3ang_0 fsbc3ang_3 isbc3ang_0 wsb fsbc3ang_0 fsbc3ang_3 fsbc3ang_4 wsbc fsbc3ang_1 fsbc3ang_3 isbc3ang_0 wsb fsbc3ang_1 fsbc3ang_3 fsbc3ang_4 wsbc fsbc3ang_2 fsbc3ang_3 isbc3ang_0 wsb fsbc3ang_2 fsbc3ang_3 fsbc3ang_4 wsbc fsbc3ang_0 fsbc3ang_3 isbc3ang_0 fsbc3ang_4 dfsbcq2 fsbc3ang_1 fsbc3ang_3 isbc3ang_0 fsbc3ang_4 dfsbcq2 fsbc3ang_2 fsbc3ang_3 isbc3ang_0 fsbc3ang_4 dfsbcq2 3anbi123d fsbc3ang_0 fsbc3ang_1 fsbc3ang_2 fsbc3ang_3 isbc3ang_0 sb3an vtoclbg $.
$}
$( /* Class substitution into a membership relation.  (Contributed by NM,
       17-Nov-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	$d y A $.
	$d x y B $.
	isbcel1gv_0 $f set y $.
	fsbcel1gv_0 $f set x $.
	fsbcel1gv_1 $f class A $.
	fsbcel1gv_2 $f class B $.
	fsbcel1gv_3 $f class V $.
	sbcel1gv $p |- ( A e. V -> ( [. A / x ]. x e. B <-> A e. B ) ) $= fsbcel1gv_0 sup_set_class fsbcel1gv_2 wcel fsbcel1gv_0 isbcel1gv_0 wsb isbcel1gv_0 sup_set_class fsbcel1gv_2 wcel fsbcel1gv_0 sup_set_class fsbcel1gv_2 wcel fsbcel1gv_0 fsbcel1gv_1 wsbc fsbcel1gv_1 fsbcel1gv_2 wcel isbcel1gv_0 fsbcel1gv_1 fsbcel1gv_3 fsbcel1gv_0 sup_set_class fsbcel1gv_2 wcel fsbcel1gv_0 isbcel1gv_0 fsbcel1gv_1 dfsbcq2 isbcel1gv_0 sup_set_class fsbcel1gv_1 fsbcel1gv_2 eleq1 isbcel1gv_0 fsbcel1gv_0 fsbcel1gv_2 clelsb3 vtoclbg $.
$}
$( /* Class substitution into a membership relation.  (Contributed by NM,
       17-Nov-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	$d y B $.
	$d x y A $.
	isbcel2gv_0 $f set y $.
	fsbcel2gv_0 $f set x $.
	fsbcel2gv_1 $f class A $.
	fsbcel2gv_2 $f class B $.
	fsbcel2gv_3 $f class V $.
	sbcel2gv $p |- ( B e. V -> ( [. B / x ]. A e. x <-> A e. B ) ) $= fsbcel2gv_1 fsbcel2gv_0 sup_set_class wcel fsbcel2gv_0 isbcel2gv_0 wsb fsbcel2gv_1 isbcel2gv_0 sup_set_class wcel fsbcel2gv_1 fsbcel2gv_0 sup_set_class wcel fsbcel2gv_0 fsbcel2gv_2 wsbc fsbcel2gv_1 fsbcel2gv_2 wcel isbcel2gv_0 fsbcel2gv_2 fsbcel2gv_3 fsbcel2gv_1 fsbcel2gv_0 sup_set_class wcel fsbcel2gv_0 isbcel2gv_0 fsbcel2gv_2 dfsbcq2 isbcel2gv_0 sup_set_class fsbcel2gv_2 fsbcel2gv_1 eleq2 fsbcel2gv_1 fsbcel2gv_0 sup_set_class wcel fsbcel2gv_1 isbcel2gv_0 sup_set_class wcel fsbcel2gv_0 isbcel2gv_0 fsbcel2gv_1 isbcel2gv_0 sup_set_class wcel fsbcel2gv_0 nfv fsbcel2gv_0 sup_set_class isbcel2gv_0 sup_set_class fsbcel2gv_1 eleq2 sbie vtoclbg $.
$}
$( /* Substitution analog of Theorem 19.20 of [Margaris] p. 90.  (Contributed
       by NM, 11-Nov-2005.) */

$)
${
	$d x ph $.
	fsbcimdv_0 $f wff ph $.
	fsbcimdv_1 $f wff ps $.
	fsbcimdv_2 $f wff ch $.
	fsbcimdv_3 $f set x $.
	fsbcimdv_4 $f class A $.
	fsbcimdv_5 $f class V $.
	esbcimdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	sbcimdv $p |- ( ( ph /\ A e. V ) -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) $= fsbcimdv_4 fsbcimdv_5 wcel fsbcimdv_0 fsbcimdv_1 fsbcimdv_3 fsbcimdv_4 wsbc fsbcimdv_2 fsbcimdv_3 fsbcimdv_4 wsbc wi fsbcimdv_4 fsbcimdv_5 wcel fsbcimdv_0 fsbcimdv_1 fsbcimdv_2 wi fsbcimdv_3 fsbcimdv_4 wsbc fsbcimdv_1 fsbcimdv_3 fsbcimdv_4 wsbc fsbcimdv_2 fsbcimdv_3 fsbcimdv_4 wsbc wi fsbcimdv_0 fsbcimdv_1 fsbcimdv_2 wi fsbcimdv_3 wal fsbcimdv_4 fsbcimdv_5 wcel fsbcimdv_1 fsbcimdv_2 wi fsbcimdv_3 fsbcimdv_4 wsbc fsbcimdv_0 fsbcimdv_1 fsbcimdv_2 wi fsbcimdv_3 esbcimdv_0 alrimiv fsbcimdv_1 fsbcimdv_2 wi fsbcimdv_3 fsbcimdv_4 fsbcimdv_5 spsbc syl5 fsbcimdv_1 fsbcimdv_2 fsbcimdv_3 fsbcimdv_4 fsbcimdv_5 sbcimg sylibd impcom $.
$}
$( /* Substitution for a variable not free in a wff does not affect it.
       (Contributed by Mario Carneiro, 14-Oct-2016.) */

$)
${
	$d x y $.
	$d y A $.
	$d y ph $.
	isbctt_0 $f set y $.
	fsbctt_0 $f wff ph $.
	fsbctt_1 $f set x $.
	fsbctt_2 $f class A $.
	fsbctt_3 $f class V $.
	sbctt $p |- ( ( A e. V /\ F/ x ph ) -> ( [. A / x ]. ph <-> ph ) ) $= fsbctt_2 fsbctt_3 wcel fsbctt_0 fsbctt_1 wnf fsbctt_0 fsbctt_1 fsbctt_2 wsbc fsbctt_0 wb fsbctt_0 fsbctt_1 wnf fsbctt_0 fsbctt_1 isbctt_0 wsb fsbctt_0 wb wi fsbctt_0 fsbctt_1 wnf fsbctt_0 fsbctt_1 fsbctt_2 wsbc fsbctt_0 wb wi isbctt_0 fsbctt_2 fsbctt_3 isbctt_0 sup_set_class fsbctt_2 wceq fsbctt_0 fsbctt_1 isbctt_0 wsb fsbctt_0 wb fsbctt_0 fsbctt_1 fsbctt_2 wsbc fsbctt_0 wb fsbctt_0 fsbctt_1 wnf isbctt_0 sup_set_class fsbctt_2 wceq fsbctt_0 fsbctt_1 isbctt_0 wsb fsbctt_0 fsbctt_1 fsbctt_2 wsbc fsbctt_0 fsbctt_0 fsbctt_1 isbctt_0 fsbctt_2 dfsbcq2 bibi1d imbi2d fsbctt_0 fsbctt_1 isbctt_0 sbft vtoclg imp $.
$}
$( /* Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 11-Oct-2004.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) */

$)
${
	fsbcgf_0 $f wff ph $.
	fsbcgf_1 $f set x $.
	fsbcgf_2 $f class A $.
	fsbcgf_3 $f class V $.
	esbcgf_0 $e |- F/ x ph $.
	sbcgf $p |- ( A e. V -> ( [. A / x ]. ph <-> ph ) ) $= fsbcgf_2 fsbcgf_3 wcel fsbcgf_0 fsbcgf_1 wnf fsbcgf_0 fsbcgf_1 fsbcgf_2 wsbc fsbcgf_0 wb esbcgf_0 fsbcgf_0 fsbcgf_1 fsbcgf_2 fsbcgf_3 sbctt mpan2 $.
$}
$( /* Substitution for a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 11-Oct-2004.) */

$)
${
	fsbc19.21g_0 $f wff ph $.
	fsbc19.21g_1 $f wff ps $.
	fsbc19.21g_2 $f set x $.
	fsbc19.21g_3 $f class A $.
	fsbc19.21g_4 $f class V $.
	esbc19.21g_0 $e |- F/ x ph $.
	sbc19.21g $p |- ( A e. V -> ( [. A / x ]. ( ph -> ps ) <-> ( ph -> [. A / x ]. ps ) ) ) $= fsbc19.21g_3 fsbc19.21g_4 wcel fsbc19.21g_0 fsbc19.21g_1 wi fsbc19.21g_2 fsbc19.21g_3 wsbc fsbc19.21g_0 fsbc19.21g_2 fsbc19.21g_3 wsbc fsbc19.21g_1 fsbc19.21g_2 fsbc19.21g_3 wsbc wi fsbc19.21g_0 fsbc19.21g_1 fsbc19.21g_2 fsbc19.21g_3 wsbc wi fsbc19.21g_0 fsbc19.21g_1 fsbc19.21g_2 fsbc19.21g_3 fsbc19.21g_4 sbcimg fsbc19.21g_3 fsbc19.21g_4 wcel fsbc19.21g_0 fsbc19.21g_2 fsbc19.21g_3 wsbc fsbc19.21g_0 fsbc19.21g_1 fsbc19.21g_2 fsbc19.21g_3 wsbc fsbc19.21g_0 fsbc19.21g_2 fsbc19.21g_3 fsbc19.21g_4 esbc19.21g_0 sbcgf imbi1d bitrd $.
$}
$( /* Substitution for a variable not occurring in a wff does not affect it.
       Distinct variable form of ~ sbcgf .  (Contributed by Alan Sare,
       10-Nov-2012.) */

$)
${
	$d x ph $.
	fsbcg_0 $f wff ph $.
	fsbcg_1 $f set x $.
	fsbcg_2 $f class A $.
	fsbcg_3 $f class V $.
	sbcg $p |- ( A e. V -> ( [. A / x ]. ph <-> ph ) ) $= fsbcg_0 fsbcg_1 fsbcg_2 fsbcg_3 fsbcg_0 fsbcg_1 nfv sbcgf $.
$}
$( /* Conversion of implicit substitution to explicit class substitution.
       (Contributed by Mario Carneiro, 19-Dec-2013.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x V $.
	$d y W $.
	fsbc2iegf_0 $f wff ph $.
	fsbc2iegf_1 $f wff ps $.
	fsbc2iegf_2 $f set x $.
	fsbc2iegf_3 $f set y $.
	fsbc2iegf_4 $f class A $.
	fsbc2iegf_5 $f class B $.
	fsbc2iegf_6 $f class V $.
	fsbc2iegf_7 $f class W $.
	esbc2iegf_0 $e |- F/ x ps $.
	esbc2iegf_1 $e |- F/ y ps $.
	esbc2iegf_2 $e |- F/ x B e. W $.
	esbc2iegf_3 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	sbc2iegf $p |- ( ( A e. V /\ B e. W ) -> ( [. A / x ]. [. B / y ]. ph <-> ps ) ) $= fsbc2iegf_4 fsbc2iegf_6 wcel fsbc2iegf_5 fsbc2iegf_7 wcel wa fsbc2iegf_0 fsbc2iegf_3 fsbc2iegf_5 wsbc fsbc2iegf_1 fsbc2iegf_2 fsbc2iegf_4 fsbc2iegf_6 fsbc2iegf_4 fsbc2iegf_6 wcel fsbc2iegf_5 fsbc2iegf_7 wcel simpl fsbc2iegf_5 fsbc2iegf_7 wcel fsbc2iegf_2 sup_set_class fsbc2iegf_4 wceq fsbc2iegf_0 fsbc2iegf_3 fsbc2iegf_5 wsbc fsbc2iegf_1 wb fsbc2iegf_4 fsbc2iegf_6 wcel fsbc2iegf_5 fsbc2iegf_7 wcel fsbc2iegf_2 sup_set_class fsbc2iegf_4 wceq wa fsbc2iegf_0 fsbc2iegf_1 fsbc2iegf_3 fsbc2iegf_5 fsbc2iegf_7 fsbc2iegf_5 fsbc2iegf_7 wcel fsbc2iegf_2 sup_set_class fsbc2iegf_4 wceq simpl fsbc2iegf_2 sup_set_class fsbc2iegf_4 wceq fsbc2iegf_3 sup_set_class fsbc2iegf_5 wceq fsbc2iegf_0 fsbc2iegf_1 wb fsbc2iegf_5 fsbc2iegf_7 wcel esbc2iegf_3 adantll fsbc2iegf_5 fsbc2iegf_7 wcel fsbc2iegf_2 sup_set_class fsbc2iegf_4 wceq wa fsbc2iegf_3 nfv fsbc2iegf_1 fsbc2iegf_3 wnf fsbc2iegf_5 fsbc2iegf_7 wcel fsbc2iegf_2 sup_set_class fsbc2iegf_4 wceq wa esbc2iegf_1 a1i sbciedf adantll fsbc2iegf_4 fsbc2iegf_6 wcel fsbc2iegf_5 fsbc2iegf_7 wcel fsbc2iegf_2 fsbc2iegf_4 fsbc2iegf_6 wcel fsbc2iegf_2 nfv esbc2iegf_2 nfan fsbc2iegf_1 fsbc2iegf_2 wnf fsbc2iegf_4 fsbc2iegf_6 wcel fsbc2iegf_5 fsbc2iegf_7 wcel wa esbc2iegf_0 a1i sbciedf $.
$}
$( /* Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 16-Dec-2008.)  (Revised by Mario Carneiro,
       19-Dec-2013.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x y ps $.
	fsbc2ie_0 $f wff ph $.
	fsbc2ie_1 $f wff ps $.
	fsbc2ie_2 $f set x $.
	fsbc2ie_3 $f set y $.
	fsbc2ie_4 $f class A $.
	fsbc2ie_5 $f class B $.
	esbc2ie_0 $e |- A e. _V $.
	esbc2ie_1 $e |- B e. _V $.
	esbc2ie_2 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	sbc2ie $p |- ( [. A / x ]. [. B / y ]. ph <-> ps ) $= fsbc2ie_4 cvv wcel fsbc2ie_5 cvv wcel fsbc2ie_0 fsbc2ie_3 fsbc2ie_5 wsbc fsbc2ie_2 fsbc2ie_4 wsbc fsbc2ie_1 wb esbc2ie_0 esbc2ie_1 fsbc2ie_0 fsbc2ie_1 fsbc2ie_2 fsbc2ie_3 fsbc2ie_4 fsbc2ie_5 cvv cvv fsbc2ie_1 fsbc2ie_2 nfv fsbc2ie_1 fsbc2ie_3 nfv fsbc2ie_5 cvv wcel fsbc2ie_2 esbc2ie_1 nfth esbc2ie_2 sbc2iegf mp2an $.
$}
$( /* Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 16-Dec-2008.)  (Proof shortened by Mario Carneiro,
       18-Oct-2016.) */

$)
${
	$d x y A $.
	$d y B $.
	$d x y ph $.
	$d x y ch $.
	fsbc2iedv_0 $f wff ph $.
	fsbc2iedv_1 $f wff ps $.
	fsbc2iedv_2 $f wff ch $.
	fsbc2iedv_3 $f set x $.
	fsbc2iedv_4 $f set y $.
	fsbc2iedv_5 $f class A $.
	fsbc2iedv_6 $f class B $.
	esbc2iedv_0 $e |- A e. _V $.
	esbc2iedv_1 $e |- B e. _V $.
	esbc2iedv_2 $e |- ( ph -> ( ( x = A /\ y = B ) -> ( ps <-> ch ) ) ) $.
	sbc2iedv $p |- ( ph -> ( [. A / x ]. [. B / y ]. ps <-> ch ) ) $= fsbc2iedv_0 fsbc2iedv_1 fsbc2iedv_4 fsbc2iedv_6 wsbc fsbc2iedv_2 fsbc2iedv_3 fsbc2iedv_5 cvv fsbc2iedv_5 cvv wcel fsbc2iedv_0 esbc2iedv_0 a1i fsbc2iedv_0 fsbc2iedv_3 sup_set_class fsbc2iedv_5 wceq wa fsbc2iedv_1 fsbc2iedv_2 fsbc2iedv_4 fsbc2iedv_6 cvv fsbc2iedv_6 cvv wcel fsbc2iedv_0 fsbc2iedv_3 sup_set_class fsbc2iedv_5 wceq wa esbc2iedv_1 a1i fsbc2iedv_0 fsbc2iedv_3 sup_set_class fsbc2iedv_5 wceq fsbc2iedv_4 sup_set_class fsbc2iedv_6 wceq fsbc2iedv_1 fsbc2iedv_2 wb esbc2iedv_2 impl sbcied sbcied $.
$}
$( /* Conversion of implicit substitution to explicit class substitution.
       (Contributed by Mario Carneiro, 19-Jun-2014.)  (Revised by Mario
       Carneiro, 29-Dec-2014.) */

$)
${
	$d x y z A $.
	$d y z B $.
	$d z C $.
	$d x y z ps $.
	fsbc3ie_0 $f wff ph $.
	fsbc3ie_1 $f wff ps $.
	fsbc3ie_2 $f set x $.
	fsbc3ie_3 $f set y $.
	fsbc3ie_4 $f set z $.
	fsbc3ie_5 $f class A $.
	fsbc3ie_6 $f class B $.
	fsbc3ie_7 $f class C $.
	esbc3ie_0 $e |- A e. _V $.
	esbc3ie_1 $e |- B e. _V $.
	esbc3ie_2 $e |- C e. _V $.
	esbc3ie_3 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	sbc3ie $p |- ( [. A / x ]. [. B / y ]. [. C / z ]. ph <-> ps ) $= fsbc3ie_0 fsbc3ie_4 fsbc3ie_7 wsbc fsbc3ie_1 fsbc3ie_2 fsbc3ie_3 fsbc3ie_5 fsbc3ie_6 esbc3ie_0 esbc3ie_1 fsbc3ie_2 sup_set_class fsbc3ie_5 wceq fsbc3ie_3 sup_set_class fsbc3ie_6 wceq wa fsbc3ie_0 fsbc3ie_1 fsbc3ie_4 fsbc3ie_7 cvv fsbc3ie_7 cvv wcel fsbc3ie_2 sup_set_class fsbc3ie_5 wceq fsbc3ie_3 sup_set_class fsbc3ie_6 wceq wa esbc3ie_2 a1i fsbc3ie_2 sup_set_class fsbc3ie_5 wceq fsbc3ie_3 sup_set_class fsbc3ie_6 wceq fsbc3ie_4 sup_set_class fsbc3ie_7 wceq fsbc3ie_0 fsbc3ie_1 wb esbc3ie_3 3expa sbcied sbc2ie $.
$}
$( /* Lemma for ~ sbccom .  (Contributed by NM, 14-Nov-2005.)  (Revised by
       Mario Carneiro, 18-Oct-2016.) */

$)
${
	$d x y A $.
	$d x y B $.
	fsbccomlem_0 $f wff ph $.
	fsbccomlem_1 $f set x $.
	fsbccomlem_2 $f set y $.
	fsbccomlem_3 $f class A $.
	fsbccomlem_4 $f class B $.
	sbccomlem $p |- ( [. A / x ]. [. B / y ]. ph <-> [. B / y ]. [. A / x ]. ph ) $= fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa fsbccomlem_2 wex fsbccomlem_1 fsbccomlem_3 wsbc fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 wex fsbccomlem_2 fsbccomlem_4 wsbc fsbccomlem_0 fsbccomlem_2 fsbccomlem_4 wsbc fsbccomlem_1 fsbccomlem_3 wsbc fsbccomlem_0 fsbccomlem_1 fsbccomlem_3 wsbc fsbccomlem_2 fsbccomlem_4 wsbc fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa fsbccomlem_2 wex wa fsbccomlem_1 wex fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 wex wa fsbccomlem_2 wex fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa fsbccomlem_2 wex fsbccomlem_1 fsbccomlem_3 wsbc fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 wex fsbccomlem_2 fsbccomlem_4 wsbc fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa wa fsbccomlem_2 wex fsbccomlem_1 wex fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa wa fsbccomlem_1 wex fsbccomlem_2 wex fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa fsbccomlem_2 wex wa fsbccomlem_1 wex fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 wex wa fsbccomlem_2 wex fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa wa fsbccomlem_1 fsbccomlem_2 excom fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa fsbccomlem_1 fsbccomlem_2 exdistr fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa wa fsbccomlem_1 wex fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 wex wa fsbccomlem_2 fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa wa fsbccomlem_1 wex fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa wa fsbccomlem_1 wex fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 wex wa fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa wa fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa wa fsbccomlem_1 fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 an12 exbii fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 19.42v bitri exbii 3bitr3i fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa fsbccomlem_2 wex fsbccomlem_1 fsbccomlem_3 sbc5 fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 wex fsbccomlem_2 fsbccomlem_4 sbc5 3bitr4i fsbccomlem_0 fsbccomlem_2 fsbccomlem_4 wsbc fsbccomlem_2 sup_set_class fsbccomlem_4 wceq fsbccomlem_0 wa fsbccomlem_2 wex fsbccomlem_1 fsbccomlem_3 fsbccomlem_0 fsbccomlem_2 fsbccomlem_4 sbc5 sbcbii fsbccomlem_0 fsbccomlem_1 fsbccomlem_3 wsbc fsbccomlem_1 sup_set_class fsbccomlem_3 wceq fsbccomlem_0 wa fsbccomlem_1 wex fsbccomlem_2 fsbccomlem_4 fsbccomlem_0 fsbccomlem_1 fsbccomlem_3 sbc5 sbcbii 3bitr4i $.
$}
$( /* Commutative law for double class substitution.  (Contributed by NM,
       15-Nov-2005.)  (Proof shortened by Mario Carneiro, 18-Oct-2016.) */

$)
${
	$d w y z A $.
	$d w x z B $.
	$d w z ph $.
	$d x y $.
	isbccom_0 $f set z $.
	isbccom_1 $f set w $.
	fsbccom_0 $f wff ph $.
	fsbccom_1 $f set x $.
	fsbccom_2 $f set y $.
	fsbccom_3 $f class A $.
	fsbccom_4 $f class B $.
	sbccom $p |- ( [. A / x ]. [. B / y ]. ph <-> [. B / y ]. [. A / x ]. ph ) $= fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_1 fsbccom_3 wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_2 fsbccom_4 wsbc fsbccom_0 fsbccom_2 fsbccom_4 wsbc fsbccom_1 fsbccom_3 wsbc fsbccom_0 fsbccom_1 fsbccom_3 wsbc fsbccom_2 fsbccom_4 wsbc fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_1 fsbccom_3 wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_2 fsbccom_4 wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc isbccom_0 fsbccom_3 wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc isbccom_1 fsbccom_4 wsbc fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_0 isbccom_1 fsbccom_3 fsbccom_4 sbccomlem fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_1 isbccom_0 sup_set_class wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc fsbccom_2 isbccom_1 sup_set_class wsbc fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_1 fsbccom_4 fsbccom_0 fsbccom_2 fsbccom_1 isbccom_1 sup_set_class isbccom_0 sup_set_class sbccomlem sbcbii fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_1 fsbccom_4 isbccom_0 sup_set_class sbccomlem bitri sbcbii fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_2 fsbccom_3 isbccom_1 sup_set_class sbccomlem sbcbii 3bitr3i fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_1 isbccom_0 fsbccom_3 sbcco fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_2 isbccom_1 fsbccom_4 sbcco 3bitr3i fsbccom_0 fsbccom_2 isbccom_1 sup_set_class wsbc isbccom_1 fsbccom_4 wsbc fsbccom_0 fsbccom_2 fsbccom_4 wsbc fsbccom_1 fsbccom_3 fsbccom_0 fsbccom_2 isbccom_1 fsbccom_4 sbcco sbcbii fsbccom_0 fsbccom_1 isbccom_0 sup_set_class wsbc isbccom_0 fsbccom_3 wsbc fsbccom_0 fsbccom_1 fsbccom_3 wsbc fsbccom_2 fsbccom_4 fsbccom_0 fsbccom_1 isbccom_0 fsbccom_3 sbcco sbcbii 3bitr3i $.
$}
$( /* Interchange class substitution and restricted quantifier.  (Contributed
       by NM, 1-Mar-2008.)  (Revised by David Abernethy, 22-Feb-2010.) */

$)
${
	$d x y z $.
	$d A z $.
	$d B x z $.
	$d V z $.
	$d ph z $.
	isbcralt_0 $f set z $.
	fsbcralt_0 $f wff ph $.
	fsbcralt_1 $f set x $.
	fsbcralt_2 $f set y $.
	fsbcralt_3 $f class A $.
	fsbcralt_4 $f class B $.
	fsbcralt_5 $f class V $.
	sbcralt $p |- ( ( A e. V /\ F/_ y A ) -> ( [. A / x ]. A. y e. B ph <-> A. y e. B [. A / x ]. ph ) ) $= fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_1 fsbcralt_3 wsbc fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_1 isbcralt_0 sup_set_class wsbc isbcralt_0 fsbcralt_3 wsbc fsbcralt_3 fsbcralt_5 wcel fsbcralt_2 fsbcralt_3 wnfc wa fsbcralt_0 fsbcralt_1 fsbcralt_3 wsbc fsbcralt_2 fsbcralt_4 wral fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_1 isbcralt_0 fsbcralt_3 sbcco fsbcralt_3 fsbcralt_5 wcel fsbcralt_2 fsbcralt_3 wnfc wa fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_1 isbcralt_0 sup_set_class wsbc fsbcralt_0 fsbcralt_1 fsbcralt_3 wsbc fsbcralt_2 fsbcralt_4 wral isbcralt_0 fsbcralt_3 fsbcralt_5 fsbcralt_3 fsbcralt_5 wcel fsbcralt_2 fsbcralt_3 wnfc simpl fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_1 isbcralt_0 sup_set_class wsbc fsbcralt_0 fsbcralt_1 isbcralt_0 wsb fsbcralt_2 fsbcralt_4 wral fsbcralt_3 fsbcralt_5 wcel fsbcralt_2 fsbcralt_3 wnfc wa isbcralt_0 sup_set_class fsbcralt_3 wceq wa fsbcralt_0 fsbcralt_1 fsbcralt_3 wsbc fsbcralt_2 fsbcralt_4 wral fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_1 isbcralt_0 sup_set_class wsbc fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_1 isbcralt_0 wsb fsbcralt_0 fsbcralt_1 isbcralt_0 wsb fsbcralt_2 fsbcralt_4 wral fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_1 isbcralt_0 sbsbc fsbcralt_0 fsbcralt_2 fsbcralt_4 wral fsbcralt_0 fsbcralt_1 isbcralt_0 wsb fsbcralt_2 fsbcralt_4 wral fsbcralt_1 isbcralt_0 fsbcralt_0 fsbcralt_1 isbcralt_0 wsb fsbcralt_1 fsbcralt_2 fsbcralt_4 fsbcralt_1 fsbcralt_4 nfcv fsbcralt_0 fsbcralt_1 isbcralt_0 nfs1v nfral fsbcralt_1 sup_set_class isbcralt_0 sup_set_class wceq fsbcralt_0 fsbcralt_0 fsbcralt_1 isbcralt_0 wsb fsbcralt_2 fsbcralt_4 fsbcralt_0 fsbcralt_1 isbcralt_0 sbequ12 ralbidv sbie bitr3i fsbcralt_2 fsbcralt_3 wnfc isbcralt_0 sup_set_class fsbcralt_3 wceq fsbcralt_0 fsbcralt_1 isbcralt_0 wsb fsbcralt_2 fsbcralt_4 wral fsbcralt_0 fsbcralt_1 fsbcralt_3 wsbc fsbcralt_2 fsbcralt_4 wral wb fsbcralt_3 fsbcralt_5 wcel fsbcralt_2 fsbcralt_3 wnfc isbcralt_0 sup_set_class fsbcralt_3 wceq wa fsbcralt_0 fsbcralt_1 isbcralt_0 wsb fsbcralt_0 fsbcralt_1 fsbcralt_3 wsbc fsbcralt_2 fsbcralt_4 fsbcralt_2 fsbcralt_3 wnfc isbcralt_0 sup_set_class fsbcralt_3 wceq fsbcralt_2 fsbcralt_2 fsbcralt_3 nfnfc1 fsbcralt_2 fsbcralt_3 wnfc fsbcralt_2 isbcralt_0 sup_set_class fsbcralt_3 fsbcralt_2 fsbcralt_3 wnfc fsbcralt_2 isbcralt_0 sup_set_class nfcvd fsbcralt_2 fsbcralt_3 wnfc id nfeqd nfan1 isbcralt_0 sup_set_class fsbcralt_3 wceq fsbcralt_0 fsbcralt_1 isbcralt_0 wsb fsbcralt_0 fsbcralt_1 fsbcralt_3 wsbc wb fsbcralt_2 fsbcralt_3 wnfc fsbcralt_0 fsbcralt_1 isbcralt_0 fsbcralt_3 dfsbcq2 adantl ralbid adantll syl5bb sbcied syl5bbr $.
$}
$( /* Interchange class substitution and restricted existential quantifier.
       (Contributed by NM, 1-Mar-2008.)  (Proof shortened by Mario Carneiro,
       13-Oct-2016.) */

$)
${
	$d x y $.
	$d B x $.
	fsbcrext_0 $f wff ph $.
	fsbcrext_1 $f set x $.
	fsbcrext_2 $f set y $.
	fsbcrext_3 $f class A $.
	fsbcrext_4 $f class B $.
	fsbcrext_5 $f class V $.
	sbcrext $p |- ( ( A e. V /\ F/_ y A ) -> ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph ) ) $= fsbcrext_3 fsbcrext_5 wcel fsbcrext_3 cvv wcel fsbcrext_2 fsbcrext_3 wnfc fsbcrext_0 fsbcrext_2 fsbcrext_4 wrex fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc fsbcrext_2 fsbcrext_4 wrex wb fsbcrext_3 fsbcrext_5 elex fsbcrext_3 cvv wcel fsbcrext_2 fsbcrext_3 wnfc wa fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral wn fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc wn fsbcrext_2 fsbcrext_4 wral wn fsbcrext_0 fsbcrext_2 fsbcrext_4 wrex fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc fsbcrext_2 fsbcrext_4 wrex fsbcrext_3 cvv wcel fsbcrext_2 fsbcrext_3 wnfc wa fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral wn fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral fsbcrext_1 fsbcrext_3 wsbc wn fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc wn fsbcrext_2 fsbcrext_4 wral wn fsbcrext_3 cvv wcel fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral wn fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral fsbcrext_1 fsbcrext_3 wsbc wn wb fsbcrext_2 fsbcrext_3 wnfc fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral fsbcrext_1 fsbcrext_3 cvv sbcng adantr fsbcrext_3 cvv wcel fsbcrext_2 fsbcrext_3 wnfc wa fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc wn fsbcrext_2 fsbcrext_4 wral fsbcrext_3 cvv wcel fsbcrext_2 fsbcrext_3 wnfc wa fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 wn fsbcrext_1 fsbcrext_3 wsbc fsbcrext_2 fsbcrext_4 wral fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc wn fsbcrext_2 fsbcrext_4 wral fsbcrext_0 wn fsbcrext_1 fsbcrext_2 fsbcrext_3 fsbcrext_4 cvv sbcralt fsbcrext_2 fsbcrext_3 wnfc fsbcrext_3 cvv wcel fsbcrext_0 wn fsbcrext_1 fsbcrext_3 wsbc fsbcrext_2 fsbcrext_4 wral fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc wn fsbcrext_2 fsbcrext_4 wral wb fsbcrext_2 fsbcrext_3 wnfc fsbcrext_3 cvv wcel wa fsbcrext_0 wn fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc wn fsbcrext_2 fsbcrext_4 fsbcrext_2 fsbcrext_3 wnfc fsbcrext_3 cvv wcel fsbcrext_2 fsbcrext_2 fsbcrext_3 nfnfc1 fsbcrext_2 fsbcrext_3 wnfc fsbcrext_2 fsbcrext_3 cvv fsbcrext_2 fsbcrext_3 wnfc id fsbcrext_2 fsbcrext_3 wnfc fsbcrext_2 cvv nfcvd nfeld nfan1 fsbcrext_3 cvv wcel fsbcrext_0 wn fsbcrext_1 fsbcrext_3 wsbc fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc wn wb fsbcrext_2 fsbcrext_3 wnfc fsbcrext_0 fsbcrext_1 fsbcrext_3 cvv sbcng adantl ralbid ancoms bitrd notbid bitrd fsbcrext_0 fsbcrext_2 fsbcrext_4 wrex fsbcrext_0 wn fsbcrext_2 fsbcrext_4 wral wn fsbcrext_1 fsbcrext_3 fsbcrext_0 fsbcrext_2 fsbcrext_4 dfrex2 sbcbii fsbcrext_0 fsbcrext_1 fsbcrext_3 wsbc fsbcrext_2 fsbcrext_4 dfrex2 3bitr4g sylan $.
$}
$( /* Interchange class substitution and restricted quantifier.  (Contributed
       by NM, 15-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) */

$)
${
	$d y z A $.
	$d x B $.
	$d x y z $.
	$d ph z $.
	$d B z $.
	isbcralg_0 $f set z $.
	fsbcralg_0 $f wff ph $.
	fsbcralg_1 $f set x $.
	fsbcralg_2 $f set y $.
	fsbcralg_3 $f class A $.
	fsbcralg_4 $f class B $.
	fsbcralg_5 $f class V $.
	sbcralg $p |- ( A e. V -> ( [. A / x ]. A. y e. B ph <-> A. y e. B [. A / x ]. ph ) ) $= fsbcralg_0 fsbcralg_2 fsbcralg_4 wral fsbcralg_1 isbcralg_0 wsb fsbcralg_0 fsbcralg_1 isbcralg_0 wsb fsbcralg_2 fsbcralg_4 wral fsbcralg_0 fsbcralg_2 fsbcralg_4 wral fsbcralg_1 fsbcralg_3 wsbc fsbcralg_0 fsbcralg_1 fsbcralg_3 wsbc fsbcralg_2 fsbcralg_4 wral isbcralg_0 fsbcralg_3 fsbcralg_5 fsbcralg_0 fsbcralg_2 fsbcralg_4 wral fsbcralg_1 isbcralg_0 fsbcralg_3 dfsbcq2 isbcralg_0 sup_set_class fsbcralg_3 wceq fsbcralg_0 fsbcralg_1 isbcralg_0 wsb fsbcralg_0 fsbcralg_1 fsbcralg_3 wsbc fsbcralg_2 fsbcralg_4 fsbcralg_0 fsbcralg_1 isbcralg_0 fsbcralg_3 dfsbcq2 ralbidv fsbcralg_0 fsbcralg_2 fsbcralg_4 wral fsbcralg_0 fsbcralg_1 isbcralg_0 wsb fsbcralg_2 fsbcralg_4 wral fsbcralg_1 isbcralg_0 fsbcralg_0 fsbcralg_1 isbcralg_0 wsb fsbcralg_1 fsbcralg_2 fsbcralg_4 fsbcralg_1 fsbcralg_4 nfcv fsbcralg_0 fsbcralg_1 isbcralg_0 nfs1v nfral fsbcralg_1 sup_set_class isbcralg_0 sup_set_class wceq fsbcralg_0 fsbcralg_0 fsbcralg_1 isbcralg_0 wsb fsbcralg_2 fsbcralg_4 fsbcralg_0 fsbcralg_1 isbcralg_0 sbequ12 ralbidv sbie vtoclbg $.
$}
$( /* Interchange class substitution and restricted existential quantifier.
       (Contributed by NM, 15-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) */

$)
${
	$d y z A $.
	$d x B $.
	$d x y z $.
	$d ph z $.
	$d B z $.
	isbcrexg_0 $f set z $.
	fsbcrexg_0 $f wff ph $.
	fsbcrexg_1 $f set x $.
	fsbcrexg_2 $f set y $.
	fsbcrexg_3 $f class A $.
	fsbcrexg_4 $f class B $.
	fsbcrexg_5 $f class V $.
	sbcrexg $p |- ( A e. V -> ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph ) ) $= fsbcrexg_0 fsbcrexg_2 fsbcrexg_4 wrex fsbcrexg_1 isbcrexg_0 wsb fsbcrexg_0 fsbcrexg_1 isbcrexg_0 wsb fsbcrexg_2 fsbcrexg_4 wrex fsbcrexg_0 fsbcrexg_2 fsbcrexg_4 wrex fsbcrexg_1 fsbcrexg_3 wsbc fsbcrexg_0 fsbcrexg_1 fsbcrexg_3 wsbc fsbcrexg_2 fsbcrexg_4 wrex isbcrexg_0 fsbcrexg_3 fsbcrexg_5 fsbcrexg_0 fsbcrexg_2 fsbcrexg_4 wrex fsbcrexg_1 isbcrexg_0 fsbcrexg_3 dfsbcq2 isbcrexg_0 sup_set_class fsbcrexg_3 wceq fsbcrexg_0 fsbcrexg_1 isbcrexg_0 wsb fsbcrexg_0 fsbcrexg_1 fsbcrexg_3 wsbc fsbcrexg_2 fsbcrexg_4 fsbcrexg_0 fsbcrexg_1 isbcrexg_0 fsbcrexg_3 dfsbcq2 rexbidv fsbcrexg_0 fsbcrexg_2 fsbcrexg_4 wrex fsbcrexg_0 fsbcrexg_1 isbcrexg_0 wsb fsbcrexg_2 fsbcrexg_4 wrex fsbcrexg_1 isbcrexg_0 fsbcrexg_0 fsbcrexg_1 isbcrexg_0 wsb fsbcrexg_1 fsbcrexg_2 fsbcrexg_4 fsbcrexg_1 fsbcrexg_4 nfcv fsbcrexg_0 fsbcrexg_1 isbcrexg_0 nfs1v nfrex fsbcrexg_1 sup_set_class isbcrexg_0 sup_set_class wceq fsbcrexg_0 fsbcrexg_0 fsbcrexg_1 isbcrexg_0 wsb fsbcrexg_2 fsbcrexg_4 fsbcrexg_0 fsbcrexg_1 isbcrexg_0 sbequ12 rexbidv sbie vtoclbg $.
$}
$( /* Interchange class substitution and restricted uniqueness quantifier.
       (Contributed by NM, 24-Feb-2013.) */

$)
${
	$d y z A $.
	$d x B $.
	$d x y z $.
	$d ph z $.
	$d B z $.
	isbcreug_0 $f set z $.
	fsbcreug_0 $f wff ph $.
	fsbcreug_1 $f set x $.
	fsbcreug_2 $f set y $.
	fsbcreug_3 $f class A $.
	fsbcreug_4 $f class B $.
	fsbcreug_5 $f class V $.
	sbcreug $p |- ( A e. V -> ( [. A / x ]. E! y e. B ph <-> E! y e. B [. A / x ]. ph ) ) $= fsbcreug_0 fsbcreug_2 fsbcreug_4 wreu fsbcreug_1 isbcreug_0 wsb fsbcreug_0 fsbcreug_1 isbcreug_0 wsb fsbcreug_2 fsbcreug_4 wreu fsbcreug_0 fsbcreug_2 fsbcreug_4 wreu fsbcreug_1 fsbcreug_3 wsbc fsbcreug_0 fsbcreug_1 fsbcreug_3 wsbc fsbcreug_2 fsbcreug_4 wreu isbcreug_0 fsbcreug_3 fsbcreug_5 fsbcreug_0 fsbcreug_2 fsbcreug_4 wreu fsbcreug_1 isbcreug_0 fsbcreug_3 dfsbcq2 isbcreug_0 sup_set_class fsbcreug_3 wceq fsbcreug_0 fsbcreug_1 isbcreug_0 wsb fsbcreug_0 fsbcreug_1 fsbcreug_3 wsbc fsbcreug_2 fsbcreug_4 fsbcreug_0 fsbcreug_1 isbcreug_0 fsbcreug_3 dfsbcq2 reubidv fsbcreug_0 fsbcreug_2 fsbcreug_4 wreu fsbcreug_0 fsbcreug_1 isbcreug_0 wsb fsbcreug_2 fsbcreug_4 wreu fsbcreug_1 isbcreug_0 fsbcreug_0 fsbcreug_1 isbcreug_0 wsb fsbcreug_1 fsbcreug_2 fsbcreug_4 fsbcreug_1 fsbcreug_4 nfcv fsbcreug_0 fsbcreug_1 isbcreug_0 nfs1v nfreu fsbcreug_1 sup_set_class isbcreug_0 sup_set_class wceq fsbcreug_0 fsbcreug_0 fsbcreug_1 isbcreug_0 wsb fsbcreug_2 fsbcreug_4 fsbcreug_0 fsbcreug_1 isbcreug_0 sbequ12 reubidv sbie vtoclbg $.
$}
$( /* Interchange class substitution and class abstraction.  (Contributed by
       NM, 5-Nov-2005.) */

$)
${
	$d y w A $.
	$d w B $.
	$d w ph $.
	$d x y $.
	$d w x $.
	isbcabel_0 $f set w $.
	fsbcabel_0 $f wff ph $.
	fsbcabel_1 $f set x $.
	fsbcabel_2 $f set y $.
	fsbcabel_3 $f class A $.
	fsbcabel_4 $f class B $.
	fsbcabel_5 $f class V $.
	esbcabel_0 $e |- F/_ x B $.
	sbcabel $p |- ( A e. V -> ( [. A / x ]. { y | ph } e. B <-> { y | [. A / x ]. ph } e. B ) ) $= fsbcabel_3 fsbcabel_5 wcel fsbcabel_3 cvv wcel fsbcabel_0 fsbcabel_2 cab fsbcabel_4 wcel fsbcabel_1 fsbcabel_3 wsbc fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab fsbcabel_4 wcel wb fsbcabel_3 fsbcabel_5 elex fsbcabel_3 cvv wcel isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa isbcabel_0 wex fsbcabel_1 fsbcabel_3 wsbc isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa isbcabel_0 wex fsbcabel_0 fsbcabel_2 cab fsbcabel_4 wcel fsbcabel_1 fsbcabel_3 wsbc fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab fsbcabel_4 wcel fsbcabel_3 cvv wcel isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa isbcabel_0 wex fsbcabel_1 fsbcabel_3 wsbc isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa fsbcabel_1 fsbcabel_3 wsbc isbcabel_0 wex isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa isbcabel_0 wex isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa isbcabel_0 fsbcabel_1 fsbcabel_3 cvv sbcexg fsbcabel_3 cvv wcel isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa fsbcabel_1 fsbcabel_3 wsbc isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa isbcabel_0 fsbcabel_3 cvv wcel isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa fsbcabel_1 fsbcabel_3 wsbc isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq fsbcabel_1 fsbcabel_3 wsbc isbcabel_0 sup_set_class fsbcabel_4 wcel fsbcabel_1 fsbcabel_3 wsbc wa isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel fsbcabel_1 fsbcabel_3 cvv sbcang fsbcabel_3 cvv wcel isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq fsbcabel_1 fsbcabel_3 wsbc isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel fsbcabel_1 fsbcabel_3 wsbc isbcabel_0 sup_set_class fsbcabel_4 wcel fsbcabel_3 cvv wcel isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc wb fsbcabel_2 wal isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 wb fsbcabel_2 wal fsbcabel_1 fsbcabel_3 wsbc fsbcabel_3 cvv wcel fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc wb fsbcabel_2 wal isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 wb fsbcabel_2 wal fsbcabel_1 fsbcabel_3 fsbcabel_0 fsbcabel_2 isbcabel_0 sup_set_class abeq2 sbcbii fsbcabel_3 cvv wcel fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 wb fsbcabel_2 wal fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 wb fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 wal fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc wb fsbcabel_2 wal fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 wb fsbcabel_2 fsbcabel_1 fsbcabel_3 cvv sbcalg fsbcabel_3 cvv wcel fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 wb fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc wb fsbcabel_2 fsbcabel_3 cvv wcel fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 wb fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_1 fsbcabel_3 wsbc fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc wb fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc wb fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 fsbcabel_1 fsbcabel_3 cvv sbcbig fsbcabel_3 cvv wcel fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 sup_set_class isbcabel_0 sup_set_class wcel fsbcabel_1 fsbcabel_3 cvv sbcg bibi1d bitrd albidv bitrd syl5bb fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 isbcabel_0 sup_set_class abeq2 syl6bbr isbcabel_0 sup_set_class fsbcabel_4 wcel fsbcabel_1 fsbcabel_3 cvv fsbcabel_1 isbcabel_0 fsbcabel_4 esbcabel_0 nfcri sbcgf anbi12d bitrd exbidv bitrd fsbcabel_0 fsbcabel_2 cab fsbcabel_4 wcel isbcabel_0 sup_set_class fsbcabel_0 fsbcabel_2 cab wceq isbcabel_0 sup_set_class fsbcabel_4 wcel wa isbcabel_0 wex fsbcabel_1 fsbcabel_3 isbcabel_0 fsbcabel_0 fsbcabel_2 cab fsbcabel_4 df-clel sbcbii isbcabel_0 fsbcabel_0 fsbcabel_1 fsbcabel_3 wsbc fsbcabel_2 cab fsbcabel_4 df-clel 3bitr4g syl $.
$}
$( /* Restricted quantifier version of Axiom 4 of [Mendelson] p. 69.  This
       provides an axiom for a predicate calculus for a restricted domain.
       This theorem generalizes the unrestricted ~ stdpc4 and ~ spsbc .  See
       also ~ rspsbca and ~ rspcsbela .  (Contributed by NM, 17-Nov-2006.)
       (Proof shortened by Mario Carneiro, 13-Oct-2016.) */

$)
${
	$d y A $.
	$d x y B $.
	$d y ph $.
	irspsbc_0 $f set y $.
	frspsbc_0 $f wff ph $.
	frspsbc_1 $f set x $.
	frspsbc_2 $f class A $.
	frspsbc_3 $f class B $.
	rspsbc $p |- ( A e. B -> ( A. x e. B ph -> [. A / x ]. ph ) ) $= frspsbc_0 frspsbc_1 frspsbc_3 wral frspsbc_0 frspsbc_1 irspsbc_0 wsb irspsbc_0 frspsbc_3 wral frspsbc_2 frspsbc_3 wcel frspsbc_0 frspsbc_1 frspsbc_2 wsbc frspsbc_0 frspsbc_1 irspsbc_0 frspsbc_3 cbvralsv frspsbc_0 frspsbc_1 irspsbc_0 wsb frspsbc_0 frspsbc_1 frspsbc_2 wsbc irspsbc_0 frspsbc_2 frspsbc_3 frspsbc_0 frspsbc_1 irspsbc_0 frspsbc_2 dfsbcq2 rspcv syl5bi $.
$}
$( /* Restricted quantifier version of Axiom 4 of [Mendelson] p. 69.
       (Contributed by NM, 14-Dec-2005.) */

$)
${
	$d x B $.
	frspsbca_0 $f wff ph $.
	frspsbca_1 $f set x $.
	frspsbca_2 $f class A $.
	frspsbca_3 $f class B $.
	rspsbca $p |- ( ( A e. B /\ A. x e. B ph ) -> [. A / x ]. ph ) $= frspsbca_2 frspsbca_3 wcel frspsbca_0 frspsbca_1 frspsbca_3 wral frspsbca_0 frspsbca_1 frspsbca_2 wsbc frspsbca_0 frspsbca_1 frspsbca_2 frspsbca_3 rspsbc imp $.
$}
$( /* Existence form of ~ rspsbca .  (Contributed by NM, 29-Feb-2008.)  (Proof
       shortened by Mario Carneiro, 13-Oct-2016.) */

$)
${
	$d y A $.
	$d x y B $.
	$d y ph $.
	irspesbca_0 $f set y $.
	frspesbca_0 $f wff ph $.
	frspesbca_1 $f set x $.
	frspesbca_2 $f class A $.
	frspesbca_3 $f class B $.
	rspesbca $p |- ( ( A e. B /\ [. A / x ]. ph ) -> E. x e. B ph ) $= frspesbca_2 frspesbca_3 wcel frspesbca_0 frspesbca_1 frspesbca_2 wsbc wa frspesbca_0 frspesbca_1 irspesbca_0 wsb irspesbca_0 frspesbca_3 wrex frspesbca_0 frspesbca_1 frspesbca_3 wrex frspesbca_0 frspesbca_1 irspesbca_0 wsb frspesbca_0 frspesbca_1 frspesbca_2 wsbc irspesbca_0 frspesbca_2 frspesbca_3 frspesbca_0 frspesbca_1 irspesbca_0 frspesbca_2 dfsbcq2 rspcev frspesbca_0 frspesbca_1 irspesbca_0 frspesbca_3 cbvrexsv sylibr $.
$}
$( /* Existence form of ~ spsbc .  (Contributed by Mario Carneiro,
       18-Nov-2016.) */

$)
${
	fspesbc_0 $f wff ph $.
	fspesbc_1 $f set x $.
	fspesbc_2 $f class A $.
	spesbc $p |- ( [. A / x ]. ph -> E. x ph ) $= fspesbc_0 fspesbc_1 fspesbc_2 wsbc fspesbc_0 fspesbc_1 cvv wrex fspesbc_0 fspesbc_1 wex fspesbc_2 cvv wcel fspesbc_0 fspesbc_1 fspesbc_2 wsbc fspesbc_0 fspesbc_1 cvv wrex fspesbc_0 fspesbc_1 fspesbc_2 sbcex fspesbc_0 fspesbc_1 fspesbc_2 cvv rspesbca mpancom fspesbc_0 fspesbc_1 rexv sylib $.
$}
$( /* form of ~ spsbc .  (Contributed by Mario Carneiro, 9-Feb-2017.) */

$)
${
	fspesbcd_0 $f wff ph $.
	fspesbcd_1 $f wff ps $.
	fspesbcd_2 $f set x $.
	fspesbcd_3 $f class A $.
	espesbcd_0 $e |- ( ph -> [. A / x ]. ps ) $.
	spesbcd $p |- ( ph -> E. x ps ) $= fspesbcd_0 fspesbcd_1 fspesbcd_2 fspesbcd_3 wsbc fspesbcd_1 fspesbcd_2 wex espesbcd_0 fspesbcd_1 fspesbcd_2 fspesbcd_3 spesbc syl $.
$}
$( /* A substitution into a theorem.  (Contributed by NM, 1-Mar-2008.)  (Proof
       shortened by Mario Carneiro, 13-Oct-2016.) */

$)
${
	$d x B $.
	fsbcth2_0 $f wff ph $.
	fsbcth2_1 $f set x $.
	fsbcth2_2 $f class A $.
	fsbcth2_3 $f class B $.
	esbcth2_0 $e |- ( x e. B -> ph ) $.
	sbcth2 $p |- ( A e. B -> [. A / x ]. ph ) $= fsbcth2_2 fsbcth2_3 wcel fsbcth2_0 fsbcth2_1 fsbcth2_3 wral fsbcth2_0 fsbcth2_1 fsbcth2_2 wsbc fsbcth2_0 fsbcth2_1 fsbcth2_3 esbcth2_0 rgen fsbcth2_0 fsbcth2_1 fsbcth2_2 fsbcth2_3 rspsbc mpi $.
$}
$( /* Restricted quantifier version of Axiom 5 of [Mendelson] p. 69.  This is
       an axiom of a predicate calculus for a restricted domain.  Compare the
       unrestricted ~ stdpc5 .  (Contributed by NM, 16-Jan-2004.) */

$)
${
	fra5_0 $f wff ph $.
	fra5_1 $f wff ps $.
	fra5_2 $f set x $.
	fra5_3 $f class A $.
	era5_0 $e |- F/ x ph $.
	ra5 $p |- ( A. x e. A ( ph -> ps ) -> ( ph -> A. x e. A ps ) ) $= fra5_0 fra5_1 wi fra5_2 fra5_3 wral fra5_0 fra5_2 sup_set_class fra5_3 wcel fra5_1 wi fra5_2 wal fra5_1 fra5_2 fra5_3 wral fra5_0 fra5_1 wi fra5_2 fra5_3 wral fra5_0 fra5_2 sup_set_class fra5_3 wcel fra5_1 wi wi fra5_2 wal fra5_0 fra5_2 sup_set_class fra5_3 wcel fra5_1 wi fra5_2 wal wi fra5_0 fra5_1 wi fra5_2 fra5_3 wral fra5_2 sup_set_class fra5_3 wcel fra5_0 fra5_1 wi wi fra5_2 wal fra5_0 fra5_2 sup_set_class fra5_3 wcel fra5_1 wi wi fra5_2 wal fra5_0 fra5_1 wi fra5_2 fra5_3 df-ral fra5_2 sup_set_class fra5_3 wcel fra5_0 fra5_1 wi wi fra5_0 fra5_2 sup_set_class fra5_3 wcel fra5_1 wi wi fra5_2 fra5_2 sup_set_class fra5_3 wcel fra5_0 fra5_1 bi2.04 albii bitri fra5_0 fra5_2 sup_set_class fra5_3 wcel fra5_1 wi fra5_2 era5_0 stdpc5 sylbi fra5_1 fra5_2 fra5_3 df-ral syl6ibr $.
$}
$( /* Alternate definition of restricted "at most one."  Note that
       ` E* x e. A ph ` is not equivalent to
       ` E. y e. A A. x e. A ( ph -> x = y ) ` (in analogy to ~ reu6 ); to see
       this, let ` A ` be the empty set.  However, one direction of this
       pattern holds; see ~ rmo2i .  (Contributed by NM, 17-Jun-2017.) */

$)
${
	$d x y A $.
	frmo2_0 $f wff ph $.
	frmo2_1 $f set x $.
	frmo2_2 $f set y $.
	frmo2_3 $f class A $.
	ermo2_0 $e |- F/ y ph $.
	rmo2 $p |- ( E* x e. A ph <-> E. y A. x e. A ( ph -> x = y ) ) $= frmo2_0 frmo2_1 frmo2_3 wrmo frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 wa frmo2_1 wmo frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 wa frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi frmo2_1 wal frmo2_2 wex frmo2_0 frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi frmo2_1 frmo2_3 wral frmo2_2 wex frmo2_0 frmo2_1 frmo2_3 df-rmo frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 wa frmo2_1 frmo2_2 frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 frmo2_2 frmo2_1 sup_set_class frmo2_3 wcel frmo2_2 nfv ermo2_0 nfan mo2 frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 wa frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi frmo2_1 wal frmo2_0 frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi frmo2_1 frmo2_3 wral frmo2_2 frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 wa frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi frmo2_1 wal frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi wi frmo2_1 wal frmo2_0 frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi frmo2_1 frmo2_3 wral frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 wa frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi wi frmo2_1 frmo2_1 sup_set_class frmo2_3 wcel frmo2_0 frmo2_1 sup_set_class frmo2_2 sup_set_class wceq impexp albii frmo2_0 frmo2_1 sup_set_class frmo2_2 sup_set_class wceq wi frmo2_1 frmo2_3 df-ral bitr4i exbii 3bitri $.
$}
$( /* Condition implying restricted "at most one."  (Contributed by NM,
       17-Jun-2017.) */

$)
${
	$d x y A $.
	frmo2i_0 $f wff ph $.
	frmo2i_1 $f set x $.
	frmo2i_2 $f set y $.
	frmo2i_3 $f class A $.
	ermo2i_0 $e |- F/ y ph $.
	rmo2i $p |- ( E. y e. A A. x e. A ( ph -> x = y ) -> E* x e. A ph ) $= frmo2i_0 frmo2i_1 sup_set_class frmo2i_2 sup_set_class wceq wi frmo2i_1 frmo2i_3 wral frmo2i_2 frmo2i_3 wrex frmo2i_0 frmo2i_1 sup_set_class frmo2i_2 sup_set_class wceq wi frmo2i_1 frmo2i_3 wral frmo2i_2 wex frmo2i_0 frmo2i_1 frmo2i_3 wrmo frmo2i_0 frmo2i_1 sup_set_class frmo2i_2 sup_set_class wceq wi frmo2i_1 frmo2i_3 wral frmo2i_2 frmo2i_3 rexex frmo2i_0 frmo2i_1 frmo2i_2 frmo2i_3 ermo2i_0 rmo2 sylibr $.
$}
$( /* Restricted "at most one" using explicit substitution.  (Contributed by
       NM, 4-Nov-2012.)  (Revised by NM, 16-Jun-2017.) */

$)
${
	$d x y A $.
	frmo3_0 $f wff ph $.
	frmo3_1 $f set x $.
	frmo3_2 $f set y $.
	frmo3_3 $f class A $.
	ermo3_0 $e |- F/ y ph $.
	rmo3 $p |- ( E* x e. A ph <-> A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $= frmo3_0 frmo3_1 frmo3_3 wrmo frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 wmo frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 frmo3_3 wral frmo3_1 frmo3_3 wral frmo3_0 frmo3_1 frmo3_3 df-rmo frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 wal frmo3_1 wal frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 frmo3_3 wral wi frmo3_1 wal frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 wmo frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 frmo3_3 wral frmo3_1 frmo3_3 wral frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 wal frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 frmo3_3 wral wi frmo3_1 frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 wal frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi wi wi frmo3_2 wal frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi wi frmo3_2 frmo3_3 wral frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 frmo3_3 wral wi frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi wi wi frmo3_2 frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel wa frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel wa frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi wi frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi wi wi frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb wa frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel wa frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_2 sup_set_class frmo3_3 wcel frmo3_0 frmo3_1 frmo3_2 wsb wa wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_2 sup_set_class frmo3_3 wcel wa frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa wa frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel wa frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb frmo3_2 sup_set_class frmo3_3 wcel frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 wsb frmo3_1 sup_set_class frmo3_3 wcel frmo3_1 frmo3_2 wsb frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_2 sup_set_class frmo3_3 wcel frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_1 frmo3_2 sban frmo3_1 sup_set_class frmo3_3 wcel frmo3_1 frmo3_2 wsb frmo3_2 sup_set_class frmo3_3 wcel frmo3_0 frmo3_1 frmo3_2 wsb frmo3_2 frmo3_1 frmo3_3 clelsb3 anbi1i bitri anbi2i frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_2 sup_set_class frmo3_3 wcel frmo3_0 frmo3_1 frmo3_2 wsb an4 frmo3_1 sup_set_class frmo3_3 wcel frmo3_2 sup_set_class frmo3_3 wcel wa frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel wa frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_3 wcel frmo3_2 sup_set_class frmo3_3 wcel ancom anbi1i 3bitri imbi1i frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel wa frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq impexp frmo3_2 sup_set_class frmo3_3 wcel frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi impexp 3bitri albii frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi wi frmo3_2 frmo3_3 df-ral frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 frmo3_3 r19.21v 3bitr2i albii frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 wa frmo3_1 frmo3_2 frmo3_1 sup_set_class frmo3_3 wcel frmo3_0 frmo3_2 frmo3_1 sup_set_class frmo3_3 wcel frmo3_2 nfv ermo3_0 nfan mo3 frmo3_0 frmo3_0 frmo3_1 frmo3_2 wsb wa frmo3_1 sup_set_class frmo3_2 sup_set_class wceq wi frmo3_2 frmo3_3 wral frmo3_1 frmo3_3 df-ral 3bitr4i bitri $.
$}
$( /* Consequence of "at most one", using implicit substitution.  (Contributed
       by NM, 2-Jan-2015.)  (Revised by NM, 16-Jun-2017.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	$d x ch $.
	frmob_0 $f wff ph $.
	frmob_1 $f wff ps $.
	frmob_2 $f wff ch $.
	frmob_3 $f set x $.
	frmob_4 $f class A $.
	frmob_5 $f class B $.
	frmob_6 $f class C $.
	ermob_0 $e |- ( x = B -> ( ph <-> ps ) ) $.
	ermob_1 $e |- ( x = C -> ( ph <-> ch ) ) $.
	rmob $p |- ( ( E* x e. A ph /\ ( B e. A /\ ps ) ) -> ( B = C <-> ( C e. A /\ ch ) ) ) $= frmob_0 frmob_3 frmob_4 wrmo frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 wa frmob_5 frmob_6 wceq frmob_6 frmob_4 wcel frmob_2 wa wb frmob_0 frmob_3 frmob_4 df-rmo frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 wa wa frmob_6 frmob_4 wcel frmob_5 frmob_6 wceq frmob_6 frmob_4 wcel frmob_2 wa frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 wa wa frmob_5 frmob_4 wcel frmob_5 frmob_6 wceq frmob_6 frmob_4 wcel frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 simprl frmob_5 frmob_6 frmob_4 eleq1 syl5ibcom frmob_6 frmob_4 wcel frmob_2 wa frmob_6 frmob_4 wcel wi frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 wa wa frmob_6 frmob_4 wcel frmob_2 simpl a1i frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 wa wa frmob_6 frmob_4 wcel frmob_5 frmob_6 wceq frmob_6 frmob_4 wcel frmob_2 wa wb frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 wa wa frmob_6 frmob_4 wcel wa frmob_5 frmob_4 wcel frmob_6 frmob_4 wcel frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 frmob_5 frmob_6 wceq frmob_6 frmob_4 wcel frmob_2 wa wb frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 frmob_6 frmob_4 wcel simplrl frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 wa wa frmob_6 frmob_4 wcel simpr frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 wa frmob_6 frmob_4 wcel simpll frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 frmob_6 frmob_4 wcel simplrl frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_3 wmo frmob_5 frmob_4 wcel frmob_1 frmob_6 frmob_4 wcel simplrr frmob_3 sup_set_class frmob_4 wcel frmob_0 wa frmob_5 frmob_4 wcel frmob_1 wa frmob_6 frmob_4 wcel frmob_2 wa frmob_3 frmob_5 frmob_6 frmob_4 frmob_4 frmob_3 sup_set_class frmob_5 wceq frmob_3 sup_set_class frmob_4 wcel frmob_5 frmob_4 wcel frmob_0 frmob_1 frmob_3 sup_set_class frmob_5 frmob_4 eleq1 ermob_0 anbi12d frmob_3 sup_set_class frmob_6 wceq frmob_3 sup_set_class frmob_4 wcel frmob_6 frmob_4 wcel frmob_0 frmob_2 frmob_3 sup_set_class frmob_6 frmob_4 eleq1 ermob_1 anbi12d mob syl212anc ex pm5.21ndd sylanb $.
$}
$( /* Consequence of "at most one", using implicit substitution.  (Contributed
       by NM, 4-Nov-2012.)  (Revised by NM, 16-Jun-2017.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	$d x ch $.
	frmoi_0 $f wff ph $.
	frmoi_1 $f wff ps $.
	frmoi_2 $f wff ch $.
	frmoi_3 $f set x $.
	frmoi_4 $f class A $.
	frmoi_5 $f class B $.
	frmoi_6 $f class C $.
	ermoi_0 $e |- ( x = B -> ( ph <-> ps ) ) $.
	ermoi_1 $e |- ( x = C -> ( ph <-> ch ) ) $.
	rmoi $p |- ( ( E* x e. A ph /\ ( B e. A /\ ps ) /\ ( C e. A /\ ch ) ) -> B = C ) $= frmoi_0 frmoi_3 frmoi_4 wrmo frmoi_5 frmoi_4 wcel frmoi_1 wa frmoi_5 frmoi_6 wceq frmoi_6 frmoi_4 wcel frmoi_2 wa frmoi_0 frmoi_1 frmoi_2 frmoi_3 frmoi_4 frmoi_5 frmoi_6 ermoi_0 ermoi_1 rmob biimp3ar $.
$}

