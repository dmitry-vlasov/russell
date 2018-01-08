$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/The_axioms_of_propositional_calculus.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical implication

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The results in this section are based on implication only, and avoid ax-3.
  In an implication, the wff before the arrow is called the "antecedent" and
  the wff after the arrow is called the "consequent."

  We will use the following descriptive terms very loosely:  A "closed form" or
  "tautology" has no $e hypotheses.  An "inference" has one or more $e
  hypotheses.  A "deduction" is an inference in which the hypotheses and the
  conclusion share the same antecedent.

*/

$)
$( /* A double modus ponens inference.  (Contributed by Mario Carneiro,
       24-Jan-2013.) */

$)
${
	fmp2b_0 $f wff ph $.
	fmp2b_1 $f wff ps $.
	fmp2b_2 $f wff ch $.
	emp2b_0 $e |- ph $.
	emp2b_1 $e |- ( ph -> ps ) $.
	emp2b_2 $e |- ( ps -> ch ) $.
	mp2b $p |- ch $= fmp2b_1 fmp2b_2 fmp2b_0 fmp2b_1 emp2b_0 emp2b_1 ax-mp emp2b_2 ax-mp $.
$}
$( /* Premise for ~ a1i . */

$)
$( /* Inference derived from axiom ~ ax-1 .  See ~ a1d for an explanation of
       our informal use of the terms "inference" and "deduction."  See also the
       comment in ~ syld .  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fa1i_0 $f wff ph $.
	fa1i_1 $f wff ps $.
	ea1i_0 $e |- ph $.
	a1i $p |- ( ps -> ph ) $= fa1i_0 fa1i_1 fa1i_0 wi ea1i_0 fa1i_0 fa1i_1 ax-1 ax-mp $.
$}
$( /* Drop and replace an antecedent.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) */

$)
${
	fmp1i_0 $f wff ph $.
	fmp1i_1 $f wff ps $.
	fmp1i_2 $f wff ch $.
	emp1i_0 $e |- ph $.
	emp1i_1 $e |- ( ph -> ps ) $.
	mp1i $p |- ( ch -> ps ) $= fmp1i_1 fmp1i_2 fmp1i_0 fmp1i_1 emp1i_0 emp1i_1 ax-mp a1i $.
$}
$( /* Premise for ~ a2i . */

$)
$( /* Inference derived from axiom ~ ax-2 .  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	fa2i_0 $f wff ph $.
	fa2i_1 $f wff ps $.
	fa2i_2 $f wff ch $.
	ea2i_0 $e |- ( ph -> ( ps -> ch ) ) $.
	a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $= fa2i_0 fa2i_1 fa2i_2 wi wi fa2i_0 fa2i_1 wi fa2i_0 fa2i_2 wi wi ea2i_0 fa2i_0 fa2i_1 fa2i_2 ax-2 ax-mp $.
$}
$( /* Inference adding common antecedents in an implication.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	fimim2i_0 $f wff ph $.
	fimim2i_1 $f wff ps $.
	fimim2i_2 $f wff ch $.
	eimim2i_0 $e |- ( ph -> ps ) $.
	imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $= fimim2i_2 fimim2i_0 fimim2i_1 fimim2i_0 fimim2i_1 wi fimim2i_2 eimim2i_0 a1i a2i $.
$}
$( /* A modus ponens deduction.  A translation of natural deduction rule
       ` -> ` E ( ` -> ` elimination), see ~ natded .  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	fmpd_0 $f wff ph $.
	fmpd_1 $f wff ps $.
	fmpd_2 $f wff ch $.
	empd_0 $e |- ( ph -> ps ) $.
	empd_1 $e |- ( ph -> ( ps -> ch ) ) $.
	mpd $p |- ( ph -> ch ) $= fmpd_0 fmpd_1 wi fmpd_0 fmpd_2 wi empd_0 fmpd_0 fmpd_1 fmpd_2 empd_1 a2i ax-mp $.
$}
$( /* First of 2 premises for ~ syl . */

$)
$( /* Second of 2 premises for ~ syl . */

$)
$( /* An inference version of the transitive laws for implication ~ imim2 and
       ~ imim1 , which Russell and Whitehead call "the principle of the
       syllogism...because...the syllogism in Barbara is derived from them"
       (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Some authors
       call this law a "hypothetical syllogism."

       (A bit of trivia: this is the most commonly referenced assertion in our
       database.  In second place is ~ eqid , followed by ~ syl2anc ,
       ~ adantr , ~ syl3anc , and ~ ax-mp .  The Metamath program command 'show
       usage' shows the number of references.)  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 20-Oct-2011.)  (Proof shortened
       by Wolf Lammen, 26-Jul-2012.) */

$)
${
	fsyl_0 $f wff ph $.
	fsyl_1 $f wff ps $.
	fsyl_2 $f wff ch $.
	esyl_0 $e |- ( ph -> ps ) $.
	esyl_1 $e |- ( ps -> ch ) $.
	syl $p |- ( ph -> ch ) $= fsyl_0 fsyl_1 fsyl_2 esyl_0 fsyl_1 fsyl_2 wi fsyl_0 esyl_1 a1i mpd $.
$}
$( /* A nested modus ponens inference.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Stefan Allan, 20-Mar-2006.) */

$)
${
	fmpi_0 $f wff ph $.
	fmpi_1 $f wff ps $.
	fmpi_2 $f wff ch $.
	empi_0 $e |- ps $.
	empi_1 $e |- ( ph -> ( ps -> ch ) ) $.
	mpi $p |- ( ph -> ch ) $= fmpi_0 fmpi_1 fmpi_2 fmpi_1 fmpi_0 empi_0 a1i empi_1 mpd $.
$}
$( /* A double modus ponens inference.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.) */

$)
${
	fmp2_0 $f wff ph $.
	fmp2_1 $f wff ps $.
	fmp2_2 $f wff ch $.
	emp2_0 $e |- ph $.
	emp2_1 $e |- ps $.
	emp2_2 $e |- ( ph -> ( ps -> ch ) ) $.
	mp2 $p |- ch $= fmp2_0 fmp2_2 emp2_0 fmp2_0 fmp2_1 fmp2_2 emp2_1 emp2_2 mpi ax-mp $.
$}
$( /* Inference chaining two syllogisms.  (Contributed by NM, 5-Aug-1993.) */

$)
$v th $.
${
	f3syl_0 $f wff ph $.
	f3syl_1 $f wff ps $.
	f3syl_2 $f wff ch $.
	f3syl_3 $f wff th $.
	e3syl_0 $e |- ( ph -> ps ) $.
	e3syl_1 $e |- ( ps -> ch ) $.
	e3syl_2 $e |- ( ch -> th ) $.
	3syl $p |- ( ph -> th ) $= f3syl_0 f3syl_2 f3syl_3 f3syl_0 f3syl_1 f3syl_2 e3syl_0 e3syl_1 syl e3syl_2 syl $.
$}
$( /* Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ id1 .
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Stefan Allan,
     20-Mar-2006.) */

$)
${
	fid_0 $f wff ph $.
	id $p |- ( ph -> ph ) $= fid_0 fid_0 fid_0 wi fid_0 fid_0 fid_0 ax-1 fid_0 fid_0 fid_0 wi ax-1 mpd $.
$}
$( /* Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  This
     version is proved directly from the axioms for demonstration purposes.
     This proof is a popular example in the literature and is identical, step
     for step, to the proofs of Theorem 1 of [Margaris] p. 51, Example 2.7(a)
     of [Hamilton] p. 31, Lemma 10.3 of [BellMachover] p. 36, and Lemma 1.8 of
     [Mendelson] p. 36.  It is also "Our first proof" in Hirst and Hirst's _A
     Primer for Logic and Proof_ p. 17 (PDF p. 23) at
     ~ http://www.mathsci.appstate.edu/~~hirstjl/primer/hirst.pdf .  For a
     shorter version of the proof that takes advantage of previously proved
     theorems, see ~ id .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.)  (Proof modification is discouraged.) */

$)
${
	fid1_0 $f wff ph $.
	id1 $p |- ( ph -> ph ) $= fid1_0 fid1_0 fid1_0 wi wi fid1_0 fid1_0 wi fid1_0 fid1_0 ax-1 fid1_0 fid1_0 fid1_0 wi fid1_0 wi wi fid1_0 fid1_0 fid1_0 wi wi fid1_0 fid1_0 wi wi fid1_0 fid1_0 fid1_0 wi ax-1 fid1_0 fid1_0 fid1_0 wi fid1_0 ax-2 ax-mp ax-mp $.
$}
$( /* Principle of identity with antecedent.  (Contributed by NM,
     26-Nov-1995.) */

$)
${
	fidd_0 $f wff ph $.
	fidd_1 $f wff ps $.
	idd $p |- ( ph -> ( ps -> ps ) ) $= fidd_1 fidd_1 wi fidd_0 fidd_1 id a1i $.
$}
$( /* Deduction introducing an embedded antecedent.

       _Naming convention_:  We often call a theorem a "deduction" and suffix
       its label with "d" whenever the hypotheses and conclusion are each
       prefixed with the same antecedent.  This allows us to use the theorem in
       places where (in traditional textbook formalizations) the standard
       Deduction Theorem would be used; here ` ph ` would be replaced with a
       conjunction ( ~ df-an ) of the hypotheses of the would-be deduction.  By
       contrast, we tend to call the simpler version with no common antecedent
       an "inference" and suffix its label with "i"; compare theorem ~ a1i .
       Finally, a "theorem" would be the form with no hypotheses; in this case
       the "theorem" form would be the original axiom ~ ax-1 .  We usually show
       the theorem form without a suffix on its label (e.g. ~ pm2.43 vs.
       ~ pm2.43i vs. ~ pm2.43d ).  When an inference is converted to a theorem
       by eliminating an "is a set" hypothesis, we sometimes suffix the theorem
       form with "g" (for "more general") as in ~ uniex vs. ~ uniexg .
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Stefan Allan,
       20-Mar-2006.) */

$)
${
	fa1d_0 $f wff ph $.
	fa1d_1 $f wff ps $.
	fa1d_2 $f wff ch $.
	ea1d_0 $e |- ( ph -> ps ) $.
	a1d $p |- ( ph -> ( ch -> ps ) ) $= fa1d_0 fa1d_1 fa1d_2 fa1d_1 wi ea1d_0 fa1d_1 fa1d_2 ax-1 syl $.
$}
$( /* Deduction distributing an embedded antecedent.  (Contributed by NM,
       23-Jun-1994.) */

$)
${
	fa2d_0 $f wff ph $.
	fa2d_1 $f wff ps $.
	fa2d_2 $f wff ch $.
	fa2d_3 $f wff th $.
	ea2d_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $= fa2d_0 fa2d_1 fa2d_2 fa2d_3 wi wi fa2d_1 fa2d_2 wi fa2d_1 fa2d_3 wi wi ea2d_0 fa2d_1 fa2d_2 fa2d_3 ax-2 syl $.
$}
$( /* Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.) */

$)
${
	fa1ii_0 $f wff ph $.
	fa1ii_1 $f wff ps $.
	fa1ii_2 $f wff ch $.
	ea1ii_0 $e |- ch $.
	a1ii $p |- ( ph -> ( ps -> ch ) ) $= fa1ii_0 fa1ii_2 fa1ii_1 fa1ii_2 fa1ii_0 ea1ii_0 a1i a1d $.
$}
$( /* Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 29-Aug-2004.)  (Proof shortened by O'Cat, 2-Feb-2006.)  (Proof
       shortened by Stefan Allan, 23-Feb-2006.) */

$)
${
	fsylcom_0 $f wff ph $.
	fsylcom_1 $f wff ps $.
	fsylcom_2 $f wff ch $.
	fsylcom_3 $f wff th $.
	esylcom_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esylcom_1 $e |- ( ps -> ( ch -> th ) ) $.
	sylcom $p |- ( ph -> ( ps -> th ) ) $= fsylcom_0 fsylcom_1 fsylcom_2 wi fsylcom_1 fsylcom_3 wi esylcom_0 fsylcom_1 fsylcom_2 fsylcom_3 esylcom_1 a2i syl $.
$}
$( /* Syllogism inference with commuted antecedents.  (Contributed by NM,
       24-May-2005.) */

$)
${
	fsyl5com_0 $f wff ph $.
	fsyl5com_1 $f wff ps $.
	fsyl5com_2 $f wff ch $.
	fsyl5com_3 $f wff th $.
	esyl5com_0 $e |- ( ph -> ps ) $.
	esyl5com_1 $e |- ( ch -> ( ps -> th ) ) $.
	syl5com $p |- ( ph -> ( ch -> th ) ) $= fsyl5com_0 fsyl5com_2 fsyl5com_1 fsyl5com_3 fsyl5com_0 fsyl5com_1 fsyl5com_2 esyl5com_0 a1d esyl5com_1 sylcom $.
$}
$( /* Premise for ~ com12 .  See ~ pm2.04 for the theorem form. */

$)
$( /* Inference that swaps (commutes) antecedents in an implication.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       4-Aug-2012.) */

$)
${
	fcom12_0 $f wff ph $.
	fcom12_1 $f wff ps $.
	fcom12_2 $f wff ch $.
	ecom12_0 $e |- ( ph -> ( ps -> ch ) ) $.
	com12 $p |- ( ps -> ( ph -> ch ) ) $= fcom12_1 fcom12_1 fcom12_0 fcom12_2 fcom12_1 id ecom12_0 syl5com $.
$}
$( /* A syllogism rule of inference.  The first premise is used to replace the
       second antecedent of the second premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-May-2013.) */

$)
${
	fsyl5_0 $f wff ph $.
	fsyl5_1 $f wff ps $.
	fsyl5_2 $f wff ch $.
	fsyl5_3 $f wff th $.
	esyl5_0 $e |- ( ph -> ps ) $.
	esyl5_1 $e |- ( ch -> ( ps -> th ) ) $.
	syl5 $p |- ( ch -> ( ph -> th ) ) $= fsyl5_0 fsyl5_2 fsyl5_3 fsyl5_0 fsyl5_1 fsyl5_2 fsyl5_3 esyl5_0 esyl5_1 syl5com com12 $.
$}
$( /* A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Wolf Lammen, 30-Jul-2012.) */

$)
${
	fsyl6_0 $f wff ph $.
	fsyl6_1 $f wff ps $.
	fsyl6_2 $f wff ch $.
	fsyl6_3 $f wff th $.
	esyl6_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl6_1 $e |- ( ch -> th ) $.
	syl6 $p |- ( ph -> ( ps -> th ) ) $= fsyl6_0 fsyl6_1 fsyl6_2 fsyl6_3 esyl6_0 fsyl6_2 fsyl6_3 wi fsyl6_1 esyl6_1 a1i sylcom $.
$}
$( /* Combine ~ syl5 and ~ syl6 .  (Contributed by NM, 14-Nov-2013.) */

$)
$v ta $.
${
	fsyl56_0 $f wff ph $.
	fsyl56_1 $f wff ps $.
	fsyl56_2 $f wff ch $.
	fsyl56_3 $f wff th $.
	fsyl56_4 $f wff ta $.
	esyl56_0 $e |- ( ph -> ps ) $.
	esyl56_1 $e |- ( ch -> ( ps -> th ) ) $.
	esyl56_2 $e |- ( th -> ta ) $.
	syl56 $p |- ( ch -> ( ph -> ta ) ) $= fsyl56_0 fsyl56_1 fsyl56_2 fsyl56_4 esyl56_0 fsyl56_2 fsyl56_1 fsyl56_3 fsyl56_4 esyl56_1 esyl56_2 syl6 syl5 $.
$}
$( /* Syllogism inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) */

$)
${
	fsyl6com_0 $f wff ph $.
	fsyl6com_1 $f wff ps $.
	fsyl6com_2 $f wff ch $.
	fsyl6com_3 $f wff th $.
	esyl6com_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl6com_1 $e |- ( ch -> th ) $.
	syl6com $p |- ( ps -> ( ph -> th ) ) $= fsyl6com_0 fsyl6com_1 fsyl6com_3 fsyl6com_0 fsyl6com_1 fsyl6com_2 fsyl6com_3 esyl6com_0 esyl6com_1 syl6 com12 $.
$}
$( /* Modus ponens inference with commutation of antecedents.  (Contributed by
       NM, 17-Mar-1996.) */

$)
${
	fmpcom_0 $f wff ph $.
	fmpcom_1 $f wff ps $.
	fmpcom_2 $f wff ch $.
	empcom_0 $e |- ( ps -> ph ) $.
	empcom_1 $e |- ( ph -> ( ps -> ch ) ) $.
	mpcom $p |- ( ps -> ch ) $= fmpcom_1 fmpcom_0 fmpcom_2 empcom_0 fmpcom_0 fmpcom_1 fmpcom_2 empcom_1 com12 mpd $.
$}
$( /* Syllogism inference with common nested antecedent.  (Contributed by NM,
       4-Nov-2004.) */

$)
${
	fsyli_0 $f wff ph $.
	fsyli_1 $f wff ps $.
	fsyli_2 $f wff ch $.
	fsyli_3 $f wff th $.
	esyli_0 $e |- ( ps -> ( ph -> ch ) ) $.
	esyli_1 $e |- ( ch -> ( ph -> th ) ) $.
	syli $p |- ( ps -> ( ph -> th ) ) $= fsyli_1 fsyli_0 fsyli_2 fsyli_3 esyli_0 fsyli_2 fsyli_0 fsyli_3 esyli_1 com12 sylcom $.
$}
$( /* Replace two antecedents.  Implication-only version of ~ syl2an .
       (Contributed by Wolf Lammen, 14-May-2013.) */

$)
${
	fsyl2im_0 $f wff ph $.
	fsyl2im_1 $f wff ps $.
	fsyl2im_2 $f wff ch $.
	fsyl2im_3 $f wff th $.
	fsyl2im_4 $f wff ta $.
	esyl2im_0 $e |- ( ph -> ps ) $.
	esyl2im_1 $e |- ( ch -> th ) $.
	esyl2im_2 $e |- ( ps -> ( th -> ta ) ) $.
	syl2im $p |- ( ph -> ( ch -> ta ) ) $= fsyl2im_0 fsyl2im_1 fsyl2im_2 fsyl2im_4 wi esyl2im_0 fsyl2im_2 fsyl2im_3 fsyl2im_1 fsyl2im_4 esyl2im_1 esyl2im_2 syl5 syl $.
$}
$( /* This theorem, called "Assertion," can be thought of as closed form of
     modus ponens ~ ax-mp .  Theorem *2.27 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 5-Aug-1993.) */

$)
${
	fpm2.27_0 $f wff ph $.
	fpm2.27_1 $f wff ps $.
	pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $= fpm2.27_0 fpm2.27_1 wi fpm2.27_0 fpm2.27_1 fpm2.27_0 fpm2.27_1 wi id com12 $.
$}
$( /* A nested modus ponens deduction.  (Contributed by NM, 12-Dec-2004.) */

$)
${
	fmpdd_0 $f wff ph $.
	fmpdd_1 $f wff ps $.
	fmpdd_2 $f wff ch $.
	fmpdd_3 $f wff th $.
	empdd_0 $e |- ( ph -> ( ps -> ch ) ) $.
	empdd_1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	mpdd $p |- ( ph -> ( ps -> th ) ) $= fmpdd_0 fmpdd_1 fmpdd_2 wi fmpdd_1 fmpdd_3 wi empdd_0 fmpdd_0 fmpdd_1 fmpdd_2 fmpdd_3 empdd_1 a2d mpd $.
$}
$( /* A nested modus ponens deduction.  (Contributed by NM, 14-Dec-2004.) */

$)
${
	fmpid_0 $f wff ph $.
	fmpid_1 $f wff ps $.
	fmpid_2 $f wff ch $.
	fmpid_3 $f wff th $.
	empid_0 $e |- ( ph -> ch ) $.
	empid_1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	mpid $p |- ( ph -> ( ps -> th ) ) $= fmpid_0 fmpid_1 fmpid_2 fmpid_3 fmpid_0 fmpid_2 fmpid_1 empid_0 a1d empid_1 mpdd $.
$}
$( /* A nested modus ponens deduction.  (Contributed by NM, 16-Apr-2005.)
       (Proof shortened by O'Cat, 15-Jan-2008.) */

$)
${
	fmpdi_0 $f wff ph $.
	fmpdi_1 $f wff ps $.
	fmpdi_2 $f wff ch $.
	fmpdi_3 $f wff th $.
	empdi_0 $e |- ( ps -> ch ) $.
	empdi_1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	mpdi $p |- ( ph -> ( ps -> th ) ) $= fmpdi_0 fmpdi_1 fmpdi_2 fmpdi_3 fmpdi_1 fmpdi_2 wi fmpdi_0 empdi_0 a1i empdi_1 mpdd $.
$}
$( /* A doubly nested modus ponens inference.  (Contributed by NM,
       31-Dec-1993.)  (Proof shortened by Wolf Lammen, 31-Jul-2012.) */

$)
${
	fmpii_0 $f wff ph $.
	fmpii_1 $f wff ps $.
	fmpii_2 $f wff ch $.
	fmpii_3 $f wff th $.
	empii_0 $e |- ch $.
	empii_1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	mpii $p |- ( ph -> ( ps -> th ) ) $= fmpii_0 fmpii_1 fmpii_2 fmpii_3 fmpii_2 fmpii_1 empii_0 a1i empii_1 mpdi $.
$}
$( /* Syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 19-Feb-2008.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.)

       Notice that ~ syld has the same form as ~ syl with ` ph ` added in front
       of each hypothesis and conclusion.  When all theorems referenced in a
       proof are converted in this way, we can replace ` ph ` with a hypothesis
       of the proof, allowing the hypothesis to be eliminated with ~ id and
       become an antecedent.  The Deduction Theorem for propositional calculus,
       e.g.  Theorem 3 in [Margaris] p. 56, tells us that this procedure is
       always possible. */

$)
${
	fsyld_0 $f wff ph $.
	fsyld_1 $f wff ps $.
	fsyld_2 $f wff ch $.
	fsyld_3 $f wff th $.
	esyld_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyld_1 $e |- ( ph -> ( ch -> th ) ) $.
	syld $p |- ( ph -> ( ps -> th ) ) $= fsyld_0 fsyld_1 fsyld_2 fsyld_3 esyld_0 fsyld_0 fsyld_2 fsyld_3 wi fsyld_1 esyld_1 a1d mpdd $.
$}
$( /* A double modus ponens deduction.  (Contributed by NM, 23-May-2013.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.) */

$)
${
	fmp2d_0 $f wff ph $.
	fmp2d_1 $f wff ps $.
	fmp2d_2 $f wff ch $.
	fmp2d_3 $f wff th $.
	emp2d_0 $e |- ( ph -> ps ) $.
	emp2d_1 $e |- ( ph -> ch ) $.
	emp2d_2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	mp2d $p |- ( ph -> th ) $= fmp2d_0 fmp2d_1 fmp2d_3 emp2d_0 fmp2d_0 fmp2d_1 fmp2d_2 fmp2d_3 emp2d_1 emp2d_2 mpid mpd $.
$}
$( /* Deduction introducing a nested embedded antecedent.  (Contributed by NM,
       17-Dec-2004.)  (Proof shortened by O'Cat, 15-Jan-2008.) */

$)
${
	fa1dd_0 $f wff ph $.
	fa1dd_1 $f wff ps $.
	fa1dd_2 $f wff ch $.
	fa1dd_3 $f wff th $.
	ea1dd_0 $e |- ( ph -> ( ps -> ch ) ) $.
	a1dd $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $= fa1dd_0 fa1dd_1 fa1dd_2 fa1dd_3 fa1dd_2 wi ea1dd_0 fa1dd_2 fa1dd_3 ax-1 syl6 $.
$}
$( /* Inference absorbing redundant antecedent.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 28-Nov-2008.) */

$)
${
	fpm2.43i_0 $f wff ph $.
	fpm2.43i_1 $f wff ps $.
	epm2.43i_0 $e |- ( ph -> ( ph -> ps ) ) $.
	pm2.43i $p |- ( ph -> ps ) $= fpm2.43i_0 fpm2.43i_0 fpm2.43i_1 fpm2.43i_0 id epm2.43i_0 mpd $.
$}
$( /* Deduction absorbing redundant antecedent.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by O'Cat, 28-Nov-2008.) */

$)
${
	fpm2.43d_0 $f wff ph $.
	fpm2.43d_1 $f wff ps $.
	fpm2.43d_2 $f wff ch $.
	epm2.43d_0 $e |- ( ph -> ( ps -> ( ps -> ch ) ) ) $.
	pm2.43d $p |- ( ph -> ( ps -> ch ) ) $= fpm2.43d_0 fpm2.43d_1 fpm2.43d_1 fpm2.43d_2 fpm2.43d_1 id epm2.43d_0 mpdi $.
$}
$( /* Inference absorbing redundant antecedent.  (Contributed by NM,
       7-Nov-1995.)  (Proof shortened by O'Cat, 28-Nov-2008.) */

$)
${
	fpm2.43a_0 $f wff ph $.
	fpm2.43a_1 $f wff ps $.
	fpm2.43a_2 $f wff ch $.
	epm2.43a_0 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
	pm2.43a $p |- ( ps -> ( ph -> ch ) ) $= fpm2.43a_1 fpm2.43a_0 fpm2.43a_1 fpm2.43a_2 fpm2.43a_1 id epm2.43a_0 mpid $.
$}
$( /* Inference absorbing redundant antecedent.  (Contributed by NM,
       31-Oct-1995.) */

$)
${
	fpm2.43b_0 $f wff ph $.
	fpm2.43b_1 $f wff ps $.
	fpm2.43b_2 $f wff ch $.
	epm2.43b_0 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
	pm2.43b $p |- ( ph -> ( ps -> ch ) ) $= fpm2.43b_1 fpm2.43b_0 fpm2.43b_2 fpm2.43b_0 fpm2.43b_1 fpm2.43b_2 epm2.43b_0 pm2.43a com12 $.
$}
$( /* Absorption of redundant antecedent.  Also called the "Contraction" or
     "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by O'Cat,
     15-Aug-2004.) */

$)
${
	fpm2.43_0 $f wff ph $.
	fpm2.43_1 $f wff ps $.
	pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $= fpm2.43_0 fpm2.43_0 fpm2.43_1 wi fpm2.43_1 fpm2.43_0 fpm2.43_1 pm2.27 a2i $.
$}
$( /* Deduction adding nested antecedents.  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	fimim2d_0 $f wff ph $.
	fimim2d_1 $f wff ps $.
	fimim2d_2 $f wff ch $.
	fimim2d_3 $f wff th $.
	eimim2d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $= fimim2d_0 fimim2d_3 fimim2d_1 fimim2d_2 fimim2d_0 fimim2d_1 fimim2d_2 wi fimim2d_3 eimim2d_0 a1d a2d $.
$}
$( /* A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 6-Sep-2012.) */

$)
${
	fimim2_0 $f wff ph $.
	fimim2_1 $f wff ps $.
	fimim2_2 $f wff ch $.
	imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $= fimim2_0 fimim2_1 wi fimim2_0 fimim2_1 fimim2_2 fimim2_0 fimim2_1 wi id imim2d $.
$}
$( /* Deduction embedding an antecedent.  (Contributed by Wolf Lammen,
       4-Oct-2013.) */

$)
${
	fembantd_0 $f wff ph $.
	fembantd_1 $f wff ps $.
	fembantd_2 $f wff ch $.
	fembantd_3 $f wff th $.
	eembantd_0 $e |- ( ph -> ps ) $.
	eembantd_1 $e |- ( ph -> ( ch -> th ) ) $.
	embantd $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $= fembantd_0 fembantd_1 fembantd_2 wi fembantd_1 fembantd_3 eembantd_0 fembantd_0 fembantd_2 fembantd_3 fembantd_1 eembantd_1 imim2d mpid $.
$}
$( /* Triple syllogism deduction.  (Contributed by Jeff Hankins,
       4-Aug-2009.) */

$)
${
	f3syld_0 $f wff ph $.
	f3syld_1 $f wff ps $.
	f3syld_2 $f wff ch $.
	f3syld_3 $f wff th $.
	f3syld_4 $f wff ta $.
	e3syld_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3syld_1 $e |- ( ph -> ( ch -> th ) ) $.
	e3syld_2 $e |- ( ph -> ( th -> ta ) ) $.
	3syld $p |- ( ph -> ( ps -> ta ) ) $= f3syld_0 f3syld_1 f3syld_3 f3syld_4 f3syld_0 f3syld_1 f3syld_2 f3syld_3 e3syld_0 e3syld_1 syld e3syld_2 syld $.
$}
$( /* Virtual deduction rule ~ e12 without virtual deduction symbols.
       (Contributed by Alan Sare, 20-Apr-2011.) */

$)
${
	fsylsyld_0 $f wff ph $.
	fsylsyld_1 $f wff ps $.
	fsylsyld_2 $f wff ch $.
	fsylsyld_3 $f wff th $.
	fsylsyld_4 $f wff ta $.
	esylsyld_0 $e |- ( ph -> ps ) $.
	esylsyld_1 $e |- ( ph -> ( ch -> th ) ) $.
	esylsyld_2 $e |- ( ps -> ( th -> ta ) ) $.
	sylsyld $p |- ( ph -> ( ch -> ta ) ) $= fsylsyld_0 fsylsyld_2 fsylsyld_3 fsylsyld_4 esylsyld_1 fsylsyld_0 fsylsyld_1 fsylsyld_3 fsylsyld_4 wi esylsyld_0 esylsyld_2 syl syld $.
$}
$( /* Inference joining two implications.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by O'Cat, 29-Oct-2011.) */

$)
${
	fimim12i_0 $f wff ph $.
	fimim12i_1 $f wff ps $.
	fimim12i_2 $f wff ch $.
	fimim12i_3 $f wff th $.
	eimim12i_0 $e |- ( ph -> ps ) $.
	eimim12i_1 $e |- ( ch -> th ) $.
	imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $= fimim12i_0 fimim12i_1 fimim12i_1 fimim12i_2 wi fimim12i_3 eimim12i_0 fimim12i_2 fimim12i_3 fimim12i_1 eimim12i_1 imim2i syl5 $.
$}
$( /* Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Aug-2012.) */

$)
${
	fimim1i_0 $f wff ph $.
	fimim1i_1 $f wff ps $.
	fimim1i_2 $f wff ch $.
	eimim1i_0 $e |- ( ph -> ps ) $.
	imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $= fimim1i_0 fimim1i_1 fimim1i_2 fimim1i_2 eimim1i_0 fimim1i_2 id imim12i $.
$}
$( /* Inference adding three nested antecedents.  (Contributed by NM,
       19-Dec-2006.) */

$)
${
	fimim3i_0 $f wff ph $.
	fimim3i_1 $f wff ps $.
	fimim3i_2 $f wff ch $.
	fimim3i_3 $f wff th $.
	eimim3i_0 $e |- ( ph -> ( ps -> ch ) ) $.
	imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $= fimim3i_3 fimim3i_0 wi fimim3i_3 fimim3i_1 fimim3i_2 fimim3i_0 fimim3i_1 fimim3i_2 wi fimim3i_3 eimim3i_0 imim2i a2d $.
$}
$( /* A syllogism inference combined with contraction.  (Contributed by NM,
       4-May-1994.)  (Revised by NM, 13-Jul-2013.) */

$)
${
	fsylc_0 $f wff ph $.
	fsylc_1 $f wff ps $.
	fsylc_2 $f wff ch $.
	fsylc_3 $f wff th $.
	esylc_0 $e |- ( ph -> ps ) $.
	esylc_1 $e |- ( ph -> ch ) $.
	esylc_2 $e |- ( ps -> ( ch -> th ) ) $.
	sylc $p |- ( ph -> th ) $= fsylc_0 fsylc_3 fsylc_0 fsylc_1 fsylc_0 fsylc_2 fsylc_3 esylc_0 esylc_1 esylc_2 syl2im pm2.43i $.
$}
$( /* A syllogism inference combined with contraction. ~ e111 without virtual
       deductions.  (Contributed by Alan Sare, 7-Jul-2011.) */

$)
${
	fsyl3c_0 $f wff ph $.
	fsyl3c_1 $f wff ps $.
	fsyl3c_2 $f wff ch $.
	fsyl3c_3 $f wff th $.
	fsyl3c_4 $f wff ta $.
	esyl3c_0 $e |- ( ph -> ps ) $.
	esyl3c_1 $e |- ( ph -> ch ) $.
	esyl3c_2 $e |- ( ph -> th ) $.
	esyl3c_3 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
	syl3c $p |- ( ph -> ta ) $= fsyl3c_0 fsyl3c_3 fsyl3c_4 esyl3c_2 fsyl3c_0 fsyl3c_1 fsyl3c_2 fsyl3c_3 fsyl3c_4 wi esyl3c_0 esyl3c_1 esyl3c_3 sylc mpd $.
$}
$( /* ~ e20 without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof shortened by Wolf Lammen, 13-Sep-2012.) */

$)
${
	fsyl6mpi_0 $f wff ph $.
	fsyl6mpi_1 $f wff ps $.
	fsyl6mpi_2 $f wff ch $.
	fsyl6mpi_3 $f wff th $.
	fsyl6mpi_4 $f wff ta $.
	esyl6mpi_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl6mpi_1 $e |- th $.
	esyl6mpi_2 $e |- ( ch -> ( th -> ta ) ) $.
	syl6mpi $p |- ( ph -> ( ps -> ta ) ) $= fsyl6mpi_0 fsyl6mpi_1 fsyl6mpi_2 fsyl6mpi_4 esyl6mpi_0 fsyl6mpi_2 fsyl6mpi_3 fsyl6mpi_4 esyl6mpi_1 esyl6mpi_2 mpi syl6 $.
$}
$( /* Modus ponens combined with a syllogism inference.  (Contributed by Alan
       Sare, 20-Apr-2011.) */

$)
${
	fmpsyl_0 $f wff ph $.
	fmpsyl_1 $f wff ps $.
	fmpsyl_2 $f wff ch $.
	fmpsyl_3 $f wff th $.
	empsyl_0 $e |- ph $.
	empsyl_1 $e |- ( ps -> ch ) $.
	empsyl_2 $e |- ( ph -> ( ch -> th ) ) $.
	mpsyl $p |- ( ps -> th ) $= fmpsyl_1 fmpsyl_0 fmpsyl_2 fmpsyl_3 fmpsyl_0 fmpsyl_1 empsyl_0 a1i empsyl_1 empsyl_2 sylc $.
$}
$( /* Inference combining ~ syl6 with contraction.  (Contributed by Alan Sare,
       2-May-2011.) */

$)
${
	fsyl6c_0 $f wff ph $.
	fsyl6c_1 $f wff ps $.
	fsyl6c_2 $f wff ch $.
	fsyl6c_3 $f wff th $.
	fsyl6c_4 $f wff ta $.
	esyl6c_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl6c_1 $e |- ( ph -> ( ps -> th ) ) $.
	esyl6c_2 $e |- ( ch -> ( th -> ta ) ) $.
	syl6c $p |- ( ph -> ( ps -> ta ) ) $= fsyl6c_0 fsyl6c_1 fsyl6c_3 fsyl6c_4 esyl6c_1 fsyl6c_0 fsyl6c_1 fsyl6c_2 fsyl6c_3 fsyl6c_4 wi esyl6c_0 esyl6c_2 syl6 mpdd $.
$}
$( /* Nested syllogism deduction.  (Contributed by NM, 12-Dec-2004.)  (Proof
       shortened by Wolf Lammen, 11-May-2013.) */

$)
${
	fsyldd_0 $f wff ph $.
	fsyldd_1 $f wff ps $.
	fsyldd_2 $f wff ch $.
	fsyldd_3 $f wff th $.
	fsyldd_4 $f wff ta $.
	esyldd_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	esyldd_1 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
	syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= fsyldd_0 fsyldd_1 fsyldd_3 fsyldd_4 wi fsyldd_2 fsyldd_3 wi fsyldd_2 fsyldd_4 wi esyldd_1 esyldd_0 fsyldd_3 fsyldd_4 fsyldd_2 imim2 syl6c $.
$}
$( /* A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.) */

$)
${
	fsyl5d_0 $f wff ph $.
	fsyl5d_1 $f wff ps $.
	fsyl5d_2 $f wff ch $.
	fsyl5d_3 $f wff th $.
	fsyl5d_4 $f wff ta $.
	esyl5d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl5d_1 $e |- ( ph -> ( th -> ( ch -> ta ) ) ) $.
	syl5d $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $= fsyl5d_0 fsyl5d_3 fsyl5d_1 fsyl5d_2 fsyl5d_4 fsyl5d_0 fsyl5d_1 fsyl5d_2 wi fsyl5d_3 esyl5d_0 a1d esyl5d_1 syldd $.
$}
$( /* A syllogism rule of inference.  The first premise is used to replace the
       third antecedent of the second premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) */

$)
${
	fsyl7_0 $f wff ph $.
	fsyl7_1 $f wff ps $.
	fsyl7_2 $f wff ch $.
	fsyl7_3 $f wff th $.
	fsyl7_4 $f wff ta $.
	esyl7_0 $e |- ( ph -> ps ) $.
	esyl7_1 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
	syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $= fsyl7_2 fsyl7_0 fsyl7_1 fsyl7_3 fsyl7_4 fsyl7_0 fsyl7_1 wi fsyl7_2 esyl7_0 a1i esyl7_1 syl5d $.
$}
$( /* A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.) */

$)
${
	fsyl6d_0 $f wff ph $.
	fsyl6d_1 $f wff ps $.
	fsyl6d_2 $f wff ch $.
	fsyl6d_3 $f wff th $.
	fsyl6d_4 $f wff ta $.
	esyl6d_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	esyl6d_1 $e |- ( ph -> ( th -> ta ) ) $.
	syl6d $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= fsyl6d_0 fsyl6d_1 fsyl6d_2 fsyl6d_3 fsyl6d_4 esyl6d_0 fsyl6d_0 fsyl6d_3 fsyl6d_4 wi fsyl6d_1 esyl6d_1 a1d syldd $.
$}
$( /* A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 1-Aug-1994.)
       (Proof shortened by Wolf Lammen, 3-Aug-2012.) */

$)
${
	fsyl8_0 $f wff ph $.
	fsyl8_1 $f wff ps $.
	fsyl8_2 $f wff ch $.
	fsyl8_3 $f wff th $.
	fsyl8_4 $f wff ta $.
	esyl8_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	esyl8_1 $e |- ( th -> ta ) $.
	syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= fsyl8_0 fsyl8_1 fsyl8_2 fsyl8_3 fsyl8_4 esyl8_0 fsyl8_3 fsyl8_4 wi fsyl8_0 esyl8_1 a1i syl6d $.
$}
$( /* A nested syllogism inference with different antecedents.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) */

$)
${
	fsyl9_0 $f wff ph $.
	fsyl9_1 $f wff ps $.
	fsyl9_2 $f wff ch $.
	fsyl9_3 $f wff th $.
	fsyl9_4 $f wff ta $.
	esyl9_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl9_1 $e |- ( th -> ( ch -> ta ) ) $.
	syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $= fsyl9_0 fsyl9_1 fsyl9_2 fsyl9_3 fsyl9_4 esyl9_0 fsyl9_3 fsyl9_2 fsyl9_4 wi wi fsyl9_0 esyl9_1 a1i syl5d $.
$}
$( /* A nested syllogism inference with different antecedents.  (Contributed
       by NM, 5-Aug-1993.) */

$)
${
	fsyl9r_0 $f wff ph $.
	fsyl9r_1 $f wff ps $.
	fsyl9r_2 $f wff ch $.
	fsyl9r_3 $f wff th $.
	fsyl9r_4 $f wff ta $.
	esyl9r_0 $e |- ( ph -> ( ps -> ch ) ) $.
	esyl9r_1 $e |- ( th -> ( ch -> ta ) ) $.
	syl9r $p |- ( th -> ( ph -> ( ps -> ta ) ) ) $= fsyl9r_0 fsyl9r_3 fsyl9r_1 fsyl9r_4 wi fsyl9r_0 fsyl9r_1 fsyl9r_2 fsyl9r_3 fsyl9r_4 esyl9r_0 esyl9r_1 syl9 com12 $.
$}
$( /* Deduction combining antecedents and consequents.  (Contributed by NM,
       7-Aug-1994.)  (Proof shortened by O'Cat, 30-Oct-2011.) */

$)
${
	fimim12d_0 $f wff ph $.
	fimim12d_1 $f wff ps $.
	fimim12d_2 $f wff ch $.
	fimim12d_3 $f wff th $.
	fimim12d_4 $f wff ta $.
	eimim12d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eimim12d_1 $e |- ( ph -> ( th -> ta ) ) $.
	imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $= fimim12d_0 fimim12d_1 fimim12d_2 fimim12d_2 fimim12d_3 wi fimim12d_4 eimim12d_0 fimim12d_0 fimim12d_3 fimim12d_4 fimim12d_2 eimim12d_1 imim2d syl5d $.
$}
$( /* Deduction adding nested consequents.  (Contributed by NM, 3-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2012.) */

$)
${
	fimim1d_0 $f wff ph $.
	fimim1d_1 $f wff ps $.
	fimim1d_2 $f wff ch $.
	fimim1d_3 $f wff th $.
	eimim1d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $= fimim1d_0 fimim1d_1 fimim1d_2 fimim1d_3 fimim1d_3 eimim1d_0 fimim1d_0 fimim1d_3 idd imim12d $.
$}
$( /* A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
     [WhiteheadRussell] p. 100.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 25-May-2013.) */

$)
${
	fimim1_0 $f wff ph $.
	fimim1_1 $f wff ps $.
	fimim1_2 $f wff ch $.
	imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= fimim1_0 fimim1_1 wi fimim1_0 fimim1_1 fimim1_2 fimim1_0 fimim1_1 wi id imim1d $.
$}
$( /* Theorem *2.83 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) */

$)
${
	fpm2.83_0 $f wff ph $.
	fpm2.83_1 $f wff ps $.
	fpm2.83_2 $f wff ch $.
	fpm2.83_3 $f wff th $.
	pm2.83 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ( ch -> th ) ) -> ( ph -> ( ps -> th ) ) ) ) $= fpm2.83_1 fpm2.83_2 wi fpm2.83_2 fpm2.83_3 wi fpm2.83_1 fpm2.83_3 wi fpm2.83_0 fpm2.83_1 fpm2.83_2 fpm2.83_3 imim1 imim3i $.
$}
$( /* Commutation of antecedents.  Swap 2nd and 3rd.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Aug-2012.) */

$)
${
	fcom23_0 $f wff ph $.
	fcom23_1 $f wff ps $.
	fcom23_2 $f wff ch $.
	fcom23_3 $f wff th $.
	ecom23_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $= fcom23_0 fcom23_1 fcom23_2 fcom23_3 wi fcom23_2 fcom23_3 ecom23_0 fcom23_2 fcom23_3 pm2.27 syl9 $.
$}
$( /* Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) */

$)
${
	fcom3r_0 $f wff ph $.
	fcom3r_1 $f wff ps $.
	fcom3r_2 $f wff ch $.
	fcom3r_3 $f wff th $.
	ecom3r_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $= fcom3r_0 fcom3r_2 fcom3r_1 fcom3r_3 wi fcom3r_0 fcom3r_1 fcom3r_2 fcom3r_3 ecom3r_0 com23 com12 $.
$}
$( /* Commutation of antecedents.  Swap 1st and 3rd.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) */

$)
${
	fcom13_0 $f wff ph $.
	fcom13_1 $f wff ps $.
	fcom13_2 $f wff ch $.
	fcom13_3 $f wff th $.
	ecom13_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $= fcom13_2 fcom13_0 fcom13_1 fcom13_3 fcom13_0 fcom13_1 fcom13_2 fcom13_3 ecom13_0 com3r com23 $.
$}
$( /* Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) */

$)
${
	fcom3l_0 $f wff ph $.
	fcom3l_1 $f wff ps $.
	fcom3l_2 $f wff ch $.
	fcom3l_3 $f wff th $.
	ecom3l_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $= fcom3l_2 fcom3l_0 fcom3l_1 fcom3l_3 fcom3l_0 fcom3l_1 fcom3l_2 fcom3l_3 ecom3l_0 com3r com3r $.
$}
$( /* Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     12-Sep-2012.) */

$)
${
	fpm2.04_0 $f wff ph $.
	fpm2.04_1 $f wff ps $.
	fpm2.04_2 $f wff ch $.
	pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $= fpm2.04_0 fpm2.04_1 fpm2.04_2 wi wi fpm2.04_0 fpm2.04_1 fpm2.04_2 fpm2.04_0 fpm2.04_1 fpm2.04_2 wi wi id com23 $.
$}
$( /* Commutation of antecedents.  Swap 3rd and 4th.  (Contributed by NM,
       25-Apr-1994.) */

$)
${
	fcom34_0 $f wff ph $.
	fcom34_1 $f wff ps $.
	fcom34_2 $f wff ch $.
	fcom34_3 $f wff th $.
	fcom34_4 $f wff ta $.
	ecom34_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	com34 $p |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) $= fcom34_0 fcom34_1 fcom34_2 fcom34_3 fcom34_4 wi wi fcom34_3 fcom34_2 fcom34_4 wi wi ecom34_0 fcom34_2 fcom34_3 fcom34_4 pm2.04 syl6 $.
$}
$( /* Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by O'Cat, 15-Aug-2004.) */

$)
${
	fcom4l_0 $f wff ph $.
	fcom4l_1 $f wff ps $.
	fcom4l_2 $f wff ch $.
	fcom4l_3 $f wff th $.
	fcom4l_4 $f wff ta $.
	ecom4l_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	com4l $p |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) ) $= fcom4l_1 fcom4l_2 fcom4l_0 fcom4l_3 fcom4l_4 fcom4l_0 fcom4l_1 fcom4l_2 fcom4l_3 fcom4l_4 wi ecom4l_0 com3l com34 $.
$}
$( /* Commutation of antecedents.  Rotate twice.  (Contributed by NM,
       25-Apr-1994.) */

$)
${
	fcom4t_0 $f wff ph $.
	fcom4t_1 $f wff ps $.
	fcom4t_2 $f wff ch $.
	fcom4t_3 $f wff th $.
	fcom4t_4 $f wff ta $.
	ecom4t_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	com4t $p |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) ) $= fcom4t_1 fcom4t_2 fcom4t_3 fcom4t_0 fcom4t_4 fcom4t_0 fcom4t_1 fcom4t_2 fcom4t_3 fcom4t_4 ecom4t_0 com4l com4l $.
$}
$( /* Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) */

$)
${
	fcom4r_0 $f wff ph $.
	fcom4r_1 $f wff ps $.
	fcom4r_2 $f wff ch $.
	fcom4r_3 $f wff th $.
	fcom4r_4 $f wff ta $.
	ecom4r_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	com4r $p |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) $= fcom4r_2 fcom4r_3 fcom4r_0 fcom4r_1 fcom4r_4 fcom4r_0 fcom4r_1 fcom4r_2 fcom4r_3 fcom4r_4 ecom4r_0 com4t com4l $.
$}
$( /* Commutation of antecedents.  Swap 2nd and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) */

$)
${
	fcom24_0 $f wff ph $.
	fcom24_1 $f wff ps $.
	fcom24_2 $f wff ch $.
	fcom24_3 $f wff th $.
	fcom24_4 $f wff ta $.
	ecom24_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	com24 $p |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) ) $= fcom24_2 fcom24_3 fcom24_0 fcom24_1 fcom24_4 wi fcom24_0 fcom24_1 fcom24_2 fcom24_3 fcom24_4 ecom24_0 com4t com13 $.
$}
$( /* Commutation of antecedents.  Swap 1st and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) */

$)
${
	fcom14_0 $f wff ph $.
	fcom14_1 $f wff ps $.
	fcom14_2 $f wff ch $.
	fcom14_3 $f wff th $.
	fcom14_4 $f wff ta $.
	ecom14_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	com14 $p |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) ) $= fcom14_1 fcom14_2 fcom14_3 fcom14_0 fcom14_4 wi fcom14_0 fcom14_1 fcom14_2 fcom14_3 fcom14_4 ecom14_0 com4l com3r $.
$}
$( /* Commutation of antecedents.  Swap 4th and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) */

$)
$v et $.
${
	fcom45_0 $f wff ph $.
	fcom45_1 $f wff ps $.
	fcom45_2 $f wff ch $.
	fcom45_3 $f wff th $.
	fcom45_4 $f wff ta $.
	fcom45_5 $f wff et $.
	ecom45_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	com45 $p |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) $= fcom45_0 fcom45_1 fcom45_2 fcom45_3 fcom45_4 fcom45_5 wi wi fcom45_4 fcom45_3 fcom45_5 wi wi ecom45_0 fcom45_3 fcom45_4 fcom45_5 pm2.04 syl8 $.
$}
$( /* Commutation of antecedents.  Swap 3rd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) */

$)
${
	fcom35_0 $f wff ph $.
	fcom35_1 $f wff ps $.
	fcom35_2 $f wff ch $.
	fcom35_3 $f wff th $.
	fcom35_4 $f wff ta $.
	fcom35_5 $f wff et $.
	ecom35_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	com35 $p |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) ) $= fcom35_0 fcom35_1 fcom35_3 fcom35_4 fcom35_2 fcom35_5 wi fcom35_0 fcom35_1 fcom35_3 fcom35_2 fcom35_4 fcom35_5 fcom35_0 fcom35_1 fcom35_2 fcom35_3 fcom35_4 fcom35_5 wi ecom35_0 com34 com45 com34 $.
$}
$( /* Commutation of antecedents.  Swap 2nd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) */

$)
${
	fcom25_0 $f wff ph $.
	fcom25_1 $f wff ps $.
	fcom25_2 $f wff ch $.
	fcom25_3 $f wff th $.
	fcom25_4 $f wff ta $.
	fcom25_5 $f wff et $.
	ecom25_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	com25 $p |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) ) $= fcom25_0 fcom25_3 fcom25_2 fcom25_4 fcom25_1 fcom25_5 wi fcom25_0 fcom25_3 fcom25_2 fcom25_1 fcom25_4 fcom25_5 fcom25_0 fcom25_1 fcom25_2 fcom25_3 fcom25_4 fcom25_5 wi ecom25_0 com24 com45 com24 $.
$}
$( /* Commutation of antecedents.  Rotate left.  (Contributed by Jeff Hankins,
       28-Jun-2009.)  (Proof shortened by Wolf Lammen, 29-Jul-2012.) */

$)
${
	fcom5l_0 $f wff ph $.
	fcom5l_1 $f wff ps $.
	fcom5l_2 $f wff ch $.
	fcom5l_3 $f wff th $.
	fcom5l_4 $f wff ta $.
	fcom5l_5 $f wff et $.
	ecom5l_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	com5l $p |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) ) $= fcom5l_1 fcom5l_2 fcom5l_3 fcom5l_0 fcom5l_4 fcom5l_5 fcom5l_0 fcom5l_1 fcom5l_2 fcom5l_3 fcom5l_4 fcom5l_5 wi ecom5l_0 com4l com45 $.
$}
$( /* Commutation of antecedents.  Swap 1st and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.)  (Proof shortened by Wolf Lammen,
       29-Jul-2012.) */

$)
${
	fcom15_0 $f wff ph $.
	fcom15_1 $f wff ps $.
	fcom15_2 $f wff ch $.
	fcom15_3 $f wff th $.
	fcom15_4 $f wff ta $.
	fcom15_5 $f wff et $.
	ecom15_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	com15 $p |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) ) $= fcom15_1 fcom15_2 fcom15_3 fcom15_4 fcom15_0 fcom15_5 wi fcom15_0 fcom15_1 fcom15_2 fcom15_3 fcom15_4 fcom15_5 ecom15_0 com5l com4r $.
$}
$( /* Commutation of antecedents.  Rotate left twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) */

$)
${
	fcom52l_0 $f wff ph $.
	fcom52l_1 $f wff ps $.
	fcom52l_2 $f wff ch $.
	fcom52l_3 $f wff th $.
	fcom52l_4 $f wff ta $.
	fcom52l_5 $f wff et $.
	ecom52l_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	com52l $p |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) ) $= fcom52l_1 fcom52l_2 fcom52l_3 fcom52l_4 fcom52l_0 fcom52l_5 fcom52l_0 fcom52l_1 fcom52l_2 fcom52l_3 fcom52l_4 fcom52l_5 ecom52l_0 com5l com5l $.
$}
$( /* Commutation of antecedents.  Rotate right twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) */

$)
${
	fcom52r_0 $f wff ph $.
	fcom52r_1 $f wff ps $.
	fcom52r_2 $f wff ch $.
	fcom52r_3 $f wff th $.
	fcom52r_4 $f wff ta $.
	fcom52r_5 $f wff et $.
	ecom52r_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	com52r $p |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) ) $= fcom52r_2 fcom52r_3 fcom52r_4 fcom52r_0 fcom52r_1 fcom52r_5 fcom52r_0 fcom52r_1 fcom52r_2 fcom52r_3 fcom52r_4 fcom52r_5 ecom52r_0 com52l com5l $.
$}
$( /* Commutation of antecedents.  Rotate right.  (Contributed by Wolf Lammen,
       29-Jul-2012.) */

$)
${
	fcom5r_0 $f wff ph $.
	fcom5r_1 $f wff ps $.
	fcom5r_2 $f wff ch $.
	fcom5r_3 $f wff th $.
	fcom5r_4 $f wff ta $.
	fcom5r_5 $f wff et $.
	ecom5r_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	com5r $p |- ( ta -> ( ph -> ( ps -> ( ch -> ( th -> et ) ) ) ) ) $= fcom5r_2 fcom5r_3 fcom5r_4 fcom5r_0 fcom5r_1 fcom5r_5 fcom5r_0 fcom5r_1 fcom5r_2 fcom5r_3 fcom5r_4 fcom5r_5 ecom5r_0 com52l com52l $.
$}
$( /* Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 9-May-2013.) */

$)
${
	fjarr_0 $f wff ph $.
	fjarr_1 $f wff ps $.
	fjarr_2 $f wff ch $.
	jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $= fjarr_1 fjarr_0 fjarr_1 wi fjarr_2 fjarr_1 fjarr_0 ax-1 imim1i $.
$}
$( /* Inference based on ~ pm2.86 .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 3-Apr-2013.) */

$)
${
	fpm2.86i_0 $f wff ph $.
	fpm2.86i_1 $f wff ps $.
	fpm2.86i_2 $f wff ch $.
	epm2.86i_0 $e |- ( ( ph -> ps ) -> ( ph -> ch ) ) $.
	pm2.86i $p |- ( ph -> ( ps -> ch ) ) $= fpm2.86i_1 fpm2.86i_0 fpm2.86i_2 fpm2.86i_1 fpm2.86i_0 fpm2.86i_1 wi fpm2.86i_0 fpm2.86i_2 wi fpm2.86i_1 fpm2.86i_0 ax-1 epm2.86i_0 syl com12 $.
$}
$( /* Deduction based on ~ pm2.86 .  (Contributed by NM, 29-Jun-1995.)  (Proof
       shortened by Wolf Lammen, 3-Apr-2013.) */

$)
${
	fpm2.86d_0 $f wff ph $.
	fpm2.86d_1 $f wff ps $.
	fpm2.86d_2 $f wff ch $.
	fpm2.86d_3 $f wff th $.
	epm2.86d_0 $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
	pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= fpm2.86d_0 fpm2.86d_2 fpm2.86d_1 fpm2.86d_3 fpm2.86d_2 fpm2.86d_1 fpm2.86d_2 wi fpm2.86d_0 fpm2.86d_1 fpm2.86d_3 wi fpm2.86d_2 fpm2.86d_1 ax-1 epm2.86d_0 syl5 com23 $.
$}
$( /* Converse of axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
     (Contributed by NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen,
     3-Apr-2013.) */

$)
${
	fpm2.86_0 $f wff ph $.
	fpm2.86_1 $f wff ps $.
	fpm2.86_2 $f wff ch $.
	pm2.86 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) ) $= fpm2.86_0 fpm2.86_1 wi fpm2.86_0 fpm2.86_2 wi wi fpm2.86_0 fpm2.86_1 fpm2.86_2 fpm2.86_0 fpm2.86_1 wi fpm2.86_0 fpm2.86_2 wi wi id pm2.86d $.
$}
$( /* The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  This version of ~ loolin does not use ~ ax-3 , meaning
     that this theorem is intuitionistically valid.  (Contributed by O'Cat,
     12-Aug-2004.)  (New usage is discouraged.)
     (Proof modification is discouraged.) */

$)
${
	floolinALT_0 $f wff ph $.
	floolinALT_1 $f wff ps $.
	loolinALT $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $= floolinALT_0 floolinALT_1 wi floolinALT_1 floolinALT_0 wi wi floolinALT_1 floolinALT_0 floolinALT_0 floolinALT_1 floolinALT_1 floolinALT_0 wi jarr pm2.43d $.
$}
$( /* An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz, due to Barbara Wozniakowska, _Reports
     on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by O'Cat,
     8-Aug-2004.) */

$)
${
	floowoz_0 $f wff ph $.
	floowoz_1 $f wff ps $.
	floowoz_2 $f wff ch $.
	loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ( ps -> ph ) -> ( ps -> ch ) ) ) $= floowoz_0 floowoz_1 wi floowoz_0 floowoz_2 wi wi floowoz_1 floowoz_0 floowoz_2 floowoz_0 floowoz_1 floowoz_0 floowoz_2 wi jarr a2d $.
$}

