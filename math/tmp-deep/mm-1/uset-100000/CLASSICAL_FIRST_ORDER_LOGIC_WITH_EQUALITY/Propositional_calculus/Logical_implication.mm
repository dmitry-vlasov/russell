$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/The_axioms_of_propositional_calculus.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical implication

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The results in this section are based on implication only, and avoid ax-3.
  In an implication, the wff before the arrow is called the "antecedent" and
  the wff after the arrow is called the "consequent."

  We will use the following descriptive terms very loosely:  A "closed form" or
  "tautology" has no $e hypotheses.  An "inference" has one or more $e
  hypotheses.  A "deduction" is an inference in which the hypotheses and the
  conclusion share the same antecedent.

$)

$(A double modus ponens inference.  (Contributed by Mario Carneiro,
       24-Jan-2013.) $)

${
	$v ph ps ch  $.
	f0_mp2b $f wff ph $.
	f1_mp2b $f wff ps $.
	f2_mp2b $f wff ch $.
	e0_mp2b $e |- ph $.
	e1_mp2b $e |- ( ph -> ps ) $.
	e2_mp2b $e |- ( ps -> ch ) $.
	p_mp2b $p |- ch $= e0_mp2b e1_mp2b f0_mp2b f1_mp2b a_ax-mp e2_mp2b f1_mp2b f2_mp2b a_ax-mp $.
$}

$(Premise for ~ a1i . $)

$(Inference derived from axiom ~ ax-1 .  See ~ a1d for an explanation of
       our informal use of the terms "inference" and "deduction."  See also the
       comment in ~ syld .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_a1i $f wff ph $.
	f1_a1i $f wff ps $.
	e0_a1i $e |- ph $.
	p_a1i $p |- ( ps -> ph ) $= e0_a1i f0_a1i f1_a1i a_ax-1 f0_a1i f1_a1i f0_a1i a_wi a_ax-mp $.
$}

$(Drop and replace an antecedent.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) $)

${
	$v ph ps ch  $.
	f0_mp1i $f wff ph $.
	f1_mp1i $f wff ps $.
	f2_mp1i $f wff ch $.
	e0_mp1i $e |- ph $.
	e1_mp1i $e |- ( ph -> ps ) $.
	p_mp1i $p |- ( ch -> ps ) $= e0_mp1i e1_mp1i f0_mp1i f1_mp1i a_ax-mp f1_mp1i f2_mp1i p_a1i $.
$}

$(Premise for ~ a2i . $)

$(Inference derived from axiom ~ ax-2 .  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_a2i $f wff ph $.
	f1_a2i $f wff ps $.
	f2_a2i $f wff ch $.
	e0_a2i $e |- ( ph -> ( ps -> ch ) ) $.
	p_a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $= e0_a2i f0_a2i f1_a2i f2_a2i a_ax-2 f0_a2i f1_a2i f2_a2i a_wi a_wi f0_a2i f1_a2i a_wi f0_a2i f2_a2i a_wi a_wi a_ax-mp $.
$}

$(Inference adding common antecedents in an implication.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_imim2i $f wff ph $.
	f1_imim2i $f wff ps $.
	f2_imim2i $f wff ch $.
	e0_imim2i $e |- ( ph -> ps ) $.
	p_imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $= e0_imim2i f0_imim2i f1_imim2i a_wi f2_imim2i p_a1i f2_imim2i f0_imim2i f1_imim2i p_a2i $.
$}

$(A modus ponens deduction.  A translation of natural deduction rule
       ` -> ` E ( ` -> ` elimination), see ~ natded .  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch  $.
	f0_mpd $f wff ph $.
	f1_mpd $f wff ps $.
	f2_mpd $f wff ch $.
	e0_mpd $e |- ( ph -> ps ) $.
	e1_mpd $e |- ( ph -> ( ps -> ch ) ) $.
	p_mpd $p |- ( ph -> ch ) $= e0_mpd e1_mpd f0_mpd f1_mpd f2_mpd p_a2i f0_mpd f1_mpd a_wi f0_mpd f2_mpd a_wi a_ax-mp $.
$}

$(First of 2 premises for ~ syl . $)

$(Second of 2 premises for ~ syl . $)

$(An inference version of the transitive laws for implication ~ imim2 and
       ~ imim1 , which Russell and Whitehead call "the principle of the
       syllogism...because...the syllogism in Barbara is derived from them"
       (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Some authors
       call this law a "hypothetical syllogism."

       (A bit of trivia: this is the most commonly referenced assertion in our
       database.  In second place is ~ eqid , followed by ~ syl2anc ,
       ~ adantr , ~ syl3anc , and ~ ax-mp .  The Metamath program command 'show
       usage' shows the number of references.)  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 20-Oct-2011.)  (Proof shortened
       by Wolf Lammen, 26-Jul-2012.) $)

${
	$v ph ps ch  $.
	f0_syl $f wff ph $.
	f1_syl $f wff ps $.
	f2_syl $f wff ch $.
	e0_syl $e |- ( ph -> ps ) $.
	e1_syl $e |- ( ps -> ch ) $.
	p_syl $p |- ( ph -> ch ) $= e0_syl e1_syl f1_syl f2_syl a_wi f0_syl p_a1i f0_syl f1_syl f2_syl p_mpd $.
$}

$(A nested modus ponens inference.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Stefan Allan, 20-Mar-2006.) $)

${
	$v ph ps ch  $.
	f0_mpi $f wff ph $.
	f1_mpi $f wff ps $.
	f2_mpi $f wff ch $.
	e0_mpi $e |- ps $.
	e1_mpi $e |- ( ph -> ( ps -> ch ) ) $.
	p_mpi $p |- ( ph -> ch ) $= e0_mpi f1_mpi f0_mpi p_a1i e1_mpi f0_mpi f1_mpi f2_mpi p_mpd $.
$}

$(A double modus ponens inference.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)

${
	$v ph ps ch  $.
	f0_mp2 $f wff ph $.
	f1_mp2 $f wff ps $.
	f2_mp2 $f wff ch $.
	e0_mp2 $e |- ph $.
	e1_mp2 $e |- ps $.
	e2_mp2 $e |- ( ph -> ( ps -> ch ) ) $.
	p_mp2 $p |- ch $= e0_mp2 e1_mp2 e2_mp2 f0_mp2 f1_mp2 f2_mp2 p_mpi f0_mp2 f2_mp2 a_ax-mp $.
$}

$(Inference chaining two syllogisms.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_3syl $f wff ph $.
	f1_3syl $f wff ps $.
	f2_3syl $f wff ch $.
	f3_3syl $f wff th $.
	e0_3syl $e |- ( ph -> ps ) $.
	e1_3syl $e |- ( ps -> ch ) $.
	e2_3syl $e |- ( ch -> th ) $.
	p_3syl $p |- ( ph -> th ) $= e0_3syl e1_3syl f0_3syl f1_3syl f2_3syl p_syl e2_3syl f0_3syl f2_3syl f3_3syl p_syl $.
$}

$(Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ id1 .
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Stefan Allan,
     20-Mar-2006.) $)

${
	$v ph  $.
	f0_id $f wff ph $.
	p_id $p |- ( ph -> ph ) $= f0_id f0_id a_ax-1 f0_id f0_id f0_id a_wi a_ax-1 f0_id f0_id f0_id a_wi f0_id p_mpd $.
$}

$(Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  This
     version is proved directly from the axioms for demonstration purposes.
     This proof is a popular example in the literature and is identical, step
     for step, to the proofs of Theorem 1 of [Margaris] p. 51, Example 2.7(a)
     of [Hamilton] p. 31, Lemma 10.3 of [BellMachover] p. 36, and Lemma 1.8 of
     [Mendelson] p. 36.  It is also "Our first proof" in Hirst and Hirst's _A
     Primer for Logic and Proof_ p. 17 (PDF p. 23) at
     ~ http://www.mathsci.appstate.edu/~~hirstjl/primer/hirst.pdf .  For a
     shorter version of the proof that takes advantage of previously proved
     theorems, see ~ id .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)

${
	$v ph  $.
	f0_id1 $f wff ph $.
	p_id1 $p |- ( ph -> ph ) $= f0_id1 f0_id1 a_ax-1 f0_id1 f0_id1 f0_id1 a_wi a_ax-1 f0_id1 f0_id1 f0_id1 a_wi f0_id1 a_ax-2 f0_id1 f0_id1 f0_id1 a_wi f0_id1 a_wi a_wi f0_id1 f0_id1 f0_id1 a_wi a_wi f0_id1 f0_id1 a_wi a_wi a_ax-mp f0_id1 f0_id1 f0_id1 a_wi a_wi f0_id1 f0_id1 a_wi a_ax-mp $.
$}

$(Principle of identity with antecedent.  (Contributed by NM,
     26-Nov-1995.) $)

${
	$v ph ps  $.
	f0_idd $f wff ph $.
	f1_idd $f wff ps $.
	p_idd $p |- ( ph -> ( ps -> ps ) ) $= f1_idd p_id f1_idd f1_idd a_wi f0_idd p_a1i $.
$}

$(Deduction introducing an embedded antecedent.

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
       20-Mar-2006.) $)

${
	$v ph ps ch  $.
	f0_a1d $f wff ph $.
	f1_a1d $f wff ps $.
	f2_a1d $f wff ch $.
	e0_a1d $e |- ( ph -> ps ) $.
	p_a1d $p |- ( ph -> ( ch -> ps ) ) $= e0_a1d f1_a1d f2_a1d a_ax-1 f0_a1d f1_a1d f2_a1d f1_a1d a_wi p_syl $.
$}

$(Deduction distributing an embedded antecedent.  (Contributed by NM,
       23-Jun-1994.) $)

${
	$v ph ps ch th  $.
	f0_a2d $f wff ph $.
	f1_a2d $f wff ps $.
	f2_a2d $f wff ch $.
	f3_a2d $f wff th $.
	e0_a2d $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $= e0_a2d f1_a2d f2_a2d f3_a2d a_ax-2 f0_a2d f1_a2d f2_a2d f3_a2d a_wi a_wi f1_a2d f2_a2d a_wi f1_a2d f3_a2d a_wi a_wi p_syl $.
$}

$(Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)

${
	$v ph ps ch  $.
	f0_a1ii $f wff ph $.
	f1_a1ii $f wff ps $.
	f2_a1ii $f wff ch $.
	e0_a1ii $e |- ch $.
	p_a1ii $p |- ( ph -> ( ps -> ch ) ) $= e0_a1ii f2_a1ii f0_a1ii p_a1i f0_a1ii f2_a1ii f1_a1ii p_a1d $.
$}

$(Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 29-Aug-2004.)  (Proof shortened by O'Cat, 2-Feb-2006.)  (Proof
       shortened by Stefan Allan, 23-Feb-2006.) $)

${
	$v ph ps ch th  $.
	f0_sylcom $f wff ph $.
	f1_sylcom $f wff ps $.
	f2_sylcom $f wff ch $.
	f3_sylcom $f wff th $.
	e0_sylcom $e |- ( ph -> ( ps -> ch ) ) $.
	e1_sylcom $e |- ( ps -> ( ch -> th ) ) $.
	p_sylcom $p |- ( ph -> ( ps -> th ) ) $= e0_sylcom e1_sylcom f1_sylcom f2_sylcom f3_sylcom p_a2i f0_sylcom f1_sylcom f2_sylcom a_wi f1_sylcom f3_sylcom a_wi p_syl $.
$}

$(Syllogism inference with commuted antecedents.  (Contributed by NM,
       24-May-2005.) $)

${
	$v ph ps ch th  $.
	f0_syl5com $f wff ph $.
	f1_syl5com $f wff ps $.
	f2_syl5com $f wff ch $.
	f3_syl5com $f wff th $.
	e0_syl5com $e |- ( ph -> ps ) $.
	e1_syl5com $e |- ( ch -> ( ps -> th ) ) $.
	p_syl5com $p |- ( ph -> ( ch -> th ) ) $= e0_syl5com f0_syl5com f1_syl5com f2_syl5com p_a1d e1_syl5com f0_syl5com f2_syl5com f1_syl5com f3_syl5com p_sylcom $.
$}

$(Premise for ~ com12 .  See ~ pm2.04 for the theorem form. $)

$(Inference that swaps (commutes) antecedents in an implication.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       4-Aug-2012.) $)

${
	$v ph ps ch  $.
	f0_com12 $f wff ph $.
	f1_com12 $f wff ps $.
	f2_com12 $f wff ch $.
	e0_com12 $e |- ( ph -> ( ps -> ch ) ) $.
	p_com12 $p |- ( ps -> ( ph -> ch ) ) $= f1_com12 p_id e0_com12 f1_com12 f1_com12 f0_com12 f2_com12 p_syl5com $.
$}

$(A syllogism rule of inference.  The first premise is used to replace the
       second antecedent of the second premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-May-2013.) $)

${
	$v ph ps ch th  $.
	f0_syl5 $f wff ph $.
	f1_syl5 $f wff ps $.
	f2_syl5 $f wff ch $.
	f3_syl5 $f wff th $.
	e0_syl5 $e |- ( ph -> ps ) $.
	e1_syl5 $e |- ( ch -> ( ps -> th ) ) $.
	p_syl5 $p |- ( ch -> ( ph -> th ) ) $= e0_syl5 e1_syl5 f0_syl5 f1_syl5 f2_syl5 f3_syl5 p_syl5com f0_syl5 f2_syl5 f3_syl5 p_com12 $.
$}

$(A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Wolf Lammen, 30-Jul-2012.) $)

${
	$v ph ps ch th  $.
	f0_syl6 $f wff ph $.
	f1_syl6 $f wff ps $.
	f2_syl6 $f wff ch $.
	f3_syl6 $f wff th $.
	e0_syl6 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl6 $e |- ( ch -> th ) $.
	p_syl6 $p |- ( ph -> ( ps -> th ) ) $= e0_syl6 e1_syl6 f2_syl6 f3_syl6 a_wi f1_syl6 p_a1i f0_syl6 f1_syl6 f2_syl6 f3_syl6 p_sylcom $.
$}

$(Combine ~ syl5 and ~ syl6 .  (Contributed by NM, 14-Nov-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_syl56 $f wff ph $.
	f1_syl56 $f wff ps $.
	f2_syl56 $f wff ch $.
	f3_syl56 $f wff th $.
	f4_syl56 $f wff ta $.
	e0_syl56 $e |- ( ph -> ps ) $.
	e1_syl56 $e |- ( ch -> ( ps -> th ) ) $.
	e2_syl56 $e |- ( th -> ta ) $.
	p_syl56 $p |- ( ch -> ( ph -> ta ) ) $= e0_syl56 e1_syl56 e2_syl56 f2_syl56 f1_syl56 f3_syl56 f4_syl56 p_syl6 f0_syl56 f1_syl56 f2_syl56 f4_syl56 p_syl5 $.
$}

$(Syllogism inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)

${
	$v ph ps ch th  $.
	f0_syl6com $f wff ph $.
	f1_syl6com $f wff ps $.
	f2_syl6com $f wff ch $.
	f3_syl6com $f wff th $.
	e0_syl6com $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl6com $e |- ( ch -> th ) $.
	p_syl6com $p |- ( ps -> ( ph -> th ) ) $= e0_syl6com e1_syl6com f0_syl6com f1_syl6com f2_syl6com f3_syl6com p_syl6 f0_syl6com f1_syl6com f3_syl6com p_com12 $.
$}

$(Modus ponens inference with commutation of antecedents.  (Contributed by
       NM, 17-Mar-1996.) $)

${
	$v ph ps ch  $.
	f0_mpcom $f wff ph $.
	f1_mpcom $f wff ps $.
	f2_mpcom $f wff ch $.
	e0_mpcom $e |- ( ps -> ph ) $.
	e1_mpcom $e |- ( ph -> ( ps -> ch ) ) $.
	p_mpcom $p |- ( ps -> ch ) $= e0_mpcom e1_mpcom f0_mpcom f1_mpcom f2_mpcom p_com12 f1_mpcom f0_mpcom f2_mpcom p_mpd $.
$}

$(Syllogism inference with common nested antecedent.  (Contributed by NM,
       4-Nov-2004.) $)

${
	$v ph ps ch th  $.
	f0_syli $f wff ph $.
	f1_syli $f wff ps $.
	f2_syli $f wff ch $.
	f3_syli $f wff th $.
	e0_syli $e |- ( ps -> ( ph -> ch ) ) $.
	e1_syli $e |- ( ch -> ( ph -> th ) ) $.
	p_syli $p |- ( ps -> ( ph -> th ) ) $= e0_syli e1_syli f2_syli f0_syli f3_syli p_com12 f1_syli f0_syli f2_syli f3_syli p_sylcom $.
$}

$(Replace two antecedents.  Implication-only version of ~ syl2an .
       (Contributed by Wolf Lammen, 14-May-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_syl2im $f wff ph $.
	f1_syl2im $f wff ps $.
	f2_syl2im $f wff ch $.
	f3_syl2im $f wff th $.
	f4_syl2im $f wff ta $.
	e0_syl2im $e |- ( ph -> ps ) $.
	e1_syl2im $e |- ( ch -> th ) $.
	e2_syl2im $e |- ( ps -> ( th -> ta ) ) $.
	p_syl2im $p |- ( ph -> ( ch -> ta ) ) $= e0_syl2im e1_syl2im e2_syl2im f2_syl2im f3_syl2im f1_syl2im f4_syl2im p_syl5 f0_syl2im f1_syl2im f2_syl2im f4_syl2im a_wi p_syl $.
$}

$(This theorem, called "Assertion," can be thought of as closed form of
     modus ponens ~ ax-mp .  Theorem *2.27 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps  $.
	f0_pm2.27 $f wff ph $.
	f1_pm2.27 $f wff ps $.
	p_pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $= f0_pm2.27 f1_pm2.27 a_wi p_id f0_pm2.27 f1_pm2.27 a_wi f0_pm2.27 f1_pm2.27 p_com12 $.
$}

$(A nested modus ponens deduction.  (Contributed by NM, 12-Dec-2004.) $)

${
	$v ph ps ch th  $.
	f0_mpdd $f wff ph $.
	f1_mpdd $f wff ps $.
	f2_mpdd $f wff ch $.
	f3_mpdd $f wff th $.
	e0_mpdd $e |- ( ph -> ( ps -> ch ) ) $.
	e1_mpdd $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_mpdd $p |- ( ph -> ( ps -> th ) ) $= e0_mpdd e1_mpdd f0_mpdd f1_mpdd f2_mpdd f3_mpdd p_a2d f0_mpdd f1_mpdd f2_mpdd a_wi f1_mpdd f3_mpdd a_wi p_mpd $.
$}

$(A nested modus ponens deduction.  (Contributed by NM, 14-Dec-2004.) $)

${
	$v ph ps ch th  $.
	f0_mpid $f wff ph $.
	f1_mpid $f wff ps $.
	f2_mpid $f wff ch $.
	f3_mpid $f wff th $.
	e0_mpid $e |- ( ph -> ch ) $.
	e1_mpid $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_mpid $p |- ( ph -> ( ps -> th ) ) $= e0_mpid f0_mpid f2_mpid f1_mpid p_a1d e1_mpid f0_mpid f1_mpid f2_mpid f3_mpid p_mpdd $.
$}

$(A nested modus ponens deduction.  (Contributed by NM, 16-Apr-2005.)
       (Proof shortened by O'Cat, 15-Jan-2008.) $)

${
	$v ph ps ch th  $.
	f0_mpdi $f wff ph $.
	f1_mpdi $f wff ps $.
	f2_mpdi $f wff ch $.
	f3_mpdi $f wff th $.
	e0_mpdi $e |- ( ps -> ch ) $.
	e1_mpdi $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_mpdi $p |- ( ph -> ( ps -> th ) ) $= e0_mpdi f1_mpdi f2_mpdi a_wi f0_mpdi p_a1i e1_mpdi f0_mpdi f1_mpdi f2_mpdi f3_mpdi p_mpdd $.
$}

$(A doubly nested modus ponens inference.  (Contributed by NM,
       31-Dec-1993.)  (Proof shortened by Wolf Lammen, 31-Jul-2012.) $)

${
	$v ph ps ch th  $.
	f0_mpii $f wff ph $.
	f1_mpii $f wff ps $.
	f2_mpii $f wff ch $.
	f3_mpii $f wff th $.
	e0_mpii $e |- ch $.
	e1_mpii $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_mpii $p |- ( ph -> ( ps -> th ) ) $= e0_mpii f2_mpii f1_mpii p_a1i e1_mpii f0_mpii f1_mpii f2_mpii f3_mpii p_mpdi $.
$}

$(Syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 19-Feb-2008.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.)

       Notice that ~ syld has the same form as ~ syl with ` ph ` added in front
       of each hypothesis and conclusion.  When all theorems referenced in a
       proof are converted in this way, we can replace ` ph ` with a hypothesis
       of the proof, allowing the hypothesis to be eliminated with ~ id and
       become an antecedent.  The Deduction Theorem for propositional calculus,
       e.g.  Theorem 3 in [Margaris] p. 56, tells us that this procedure is
       always possible. $)

${
	$v ph ps ch th  $.
	f0_syld $f wff ph $.
	f1_syld $f wff ps $.
	f2_syld $f wff ch $.
	f3_syld $f wff th $.
	e0_syld $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syld $e |- ( ph -> ( ch -> th ) ) $.
	p_syld $p |- ( ph -> ( ps -> th ) ) $= e0_syld e1_syld f0_syld f2_syld f3_syld a_wi f1_syld p_a1d f0_syld f1_syld f2_syld f3_syld p_mpdd $.
$}

$(A double modus ponens deduction.  (Contributed by NM, 23-May-2013.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)

${
	$v ph ps ch th  $.
	f0_mp2d $f wff ph $.
	f1_mp2d $f wff ps $.
	f2_mp2d $f wff ch $.
	f3_mp2d $f wff th $.
	e0_mp2d $e |- ( ph -> ps ) $.
	e1_mp2d $e |- ( ph -> ch ) $.
	e2_mp2d $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_mp2d $p |- ( ph -> th ) $= e0_mp2d e1_mp2d e2_mp2d f0_mp2d f1_mp2d f2_mp2d f3_mp2d p_mpid f0_mp2d f1_mp2d f3_mp2d p_mpd $.
$}

$(Deduction introducing a nested embedded antecedent.  (Contributed by NM,
       17-Dec-2004.)  (Proof shortened by O'Cat, 15-Jan-2008.) $)

${
	$v ph ps ch th  $.
	f0_a1dd $f wff ph $.
	f1_a1dd $f wff ps $.
	f2_a1dd $f wff ch $.
	f3_a1dd $f wff th $.
	e0_a1dd $e |- ( ph -> ( ps -> ch ) ) $.
	p_a1dd $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $= e0_a1dd f2_a1dd f3_a1dd a_ax-1 f0_a1dd f1_a1dd f2_a1dd f3_a1dd f2_a1dd a_wi p_syl6 $.
$}

$(Inference absorbing redundant antecedent.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)

${
	$v ph ps  $.
	f0_pm2.43i $f wff ph $.
	f1_pm2.43i $f wff ps $.
	e0_pm2.43i $e |- ( ph -> ( ph -> ps ) ) $.
	p_pm2.43i $p |- ( ph -> ps ) $= f0_pm2.43i p_id e0_pm2.43i f0_pm2.43i f0_pm2.43i f1_pm2.43i p_mpd $.
$}

$(Deduction absorbing redundant antecedent.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)

${
	$v ph ps ch  $.
	f0_pm2.43d $f wff ph $.
	f1_pm2.43d $f wff ps $.
	f2_pm2.43d $f wff ch $.
	e0_pm2.43d $e |- ( ph -> ( ps -> ( ps -> ch ) ) ) $.
	p_pm2.43d $p |- ( ph -> ( ps -> ch ) ) $= f1_pm2.43d p_id e0_pm2.43d f0_pm2.43d f1_pm2.43d f1_pm2.43d f2_pm2.43d p_mpdi $.
$}

$(Inference absorbing redundant antecedent.  (Contributed by NM,
       7-Nov-1995.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)

${
	$v ph ps ch  $.
	f0_pm2.43a $f wff ph $.
	f1_pm2.43a $f wff ps $.
	f2_pm2.43a $f wff ch $.
	e0_pm2.43a $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
	p_pm2.43a $p |- ( ps -> ( ph -> ch ) ) $= f1_pm2.43a p_id e0_pm2.43a f1_pm2.43a f0_pm2.43a f1_pm2.43a f2_pm2.43a p_mpid $.
$}

$(Inference absorbing redundant antecedent.  (Contributed by NM,
       31-Oct-1995.) $)

${
	$v ph ps ch  $.
	f0_pm2.43b $f wff ph $.
	f1_pm2.43b $f wff ps $.
	f2_pm2.43b $f wff ch $.
	e0_pm2.43b $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
	p_pm2.43b $p |- ( ph -> ( ps -> ch ) ) $= e0_pm2.43b f0_pm2.43b f1_pm2.43b f2_pm2.43b p_pm2.43a f1_pm2.43b f0_pm2.43b f2_pm2.43b p_com12 $.
$}

$(Absorption of redundant antecedent.  Also called the "Contraction" or
     "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by O'Cat,
     15-Aug-2004.) $)

${
	$v ph ps  $.
	f0_pm2.43 $f wff ph $.
	f1_pm2.43 $f wff ps $.
	p_pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $= f0_pm2.43 f1_pm2.43 p_pm2.27 f0_pm2.43 f0_pm2.43 f1_pm2.43 a_wi f1_pm2.43 p_a2i $.
$}

$(Deduction adding nested antecedents.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps ch th  $.
	f0_imim2d $f wff ph $.
	f1_imim2d $f wff ps $.
	f2_imim2d $f wff ch $.
	f3_imim2d $f wff th $.
	e0_imim2d $e |- ( ph -> ( ps -> ch ) ) $.
	p_imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $= e0_imim2d f0_imim2d f1_imim2d f2_imim2d a_wi f3_imim2d p_a1d f0_imim2d f3_imim2d f1_imim2d f2_imim2d p_a2d $.
$}

$(A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 6-Sep-2012.) $)

${
	$v ph ps ch  $.
	f0_imim2 $f wff ph $.
	f1_imim2 $f wff ps $.
	f2_imim2 $f wff ch $.
	p_imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $= f0_imim2 f1_imim2 a_wi p_id f0_imim2 f1_imim2 a_wi f0_imim2 f1_imim2 f2_imim2 p_imim2d $.
$}

$(Deduction embedding an antecedent.  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)

${
	$v ph ps ch th  $.
	f0_embantd $f wff ph $.
	f1_embantd $f wff ps $.
	f2_embantd $f wff ch $.
	f3_embantd $f wff th $.
	e0_embantd $e |- ( ph -> ps ) $.
	e1_embantd $e |- ( ph -> ( ch -> th ) ) $.
	p_embantd $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $= e0_embantd e1_embantd f0_embantd f2_embantd f3_embantd f1_embantd p_imim2d f0_embantd f1_embantd f2_embantd a_wi f1_embantd f3_embantd p_mpid $.
$}

$(Triple syllogism deduction.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)

${
	$v ph ps ch th ta  $.
	f0_3syld $f wff ph $.
	f1_3syld $f wff ps $.
	f2_3syld $f wff ch $.
	f3_3syld $f wff th $.
	f4_3syld $f wff ta $.
	e0_3syld $e |- ( ph -> ( ps -> ch ) ) $.
	e1_3syld $e |- ( ph -> ( ch -> th ) ) $.
	e2_3syld $e |- ( ph -> ( th -> ta ) ) $.
	p_3syld $p |- ( ph -> ( ps -> ta ) ) $= e0_3syld e1_3syld f0_3syld f1_3syld f2_3syld f3_3syld p_syld e2_3syld f0_3syld f1_3syld f3_3syld f4_3syld p_syld $.
$}

$(Virtual deduction rule ~ e12 without virtual deduction symbols.
       (Contributed by Alan Sare, 20-Apr-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_sylsyld $f wff ph $.
	f1_sylsyld $f wff ps $.
	f2_sylsyld $f wff ch $.
	f3_sylsyld $f wff th $.
	f4_sylsyld $f wff ta $.
	e0_sylsyld $e |- ( ph -> ps ) $.
	e1_sylsyld $e |- ( ph -> ( ch -> th ) ) $.
	e2_sylsyld $e |- ( ps -> ( th -> ta ) ) $.
	p_sylsyld $p |- ( ph -> ( ch -> ta ) ) $= e1_sylsyld e0_sylsyld e2_sylsyld f0_sylsyld f1_sylsyld f3_sylsyld f4_sylsyld a_wi p_syl f0_sylsyld f2_sylsyld f3_sylsyld f4_sylsyld p_syld $.
$}

$(Inference joining two implications.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by O'Cat, 29-Oct-2011.) $)

${
	$v ph ps ch th  $.
	f0_imim12i $f wff ph $.
	f1_imim12i $f wff ps $.
	f2_imim12i $f wff ch $.
	f3_imim12i $f wff th $.
	e0_imim12i $e |- ( ph -> ps ) $.
	e1_imim12i $e |- ( ch -> th ) $.
	p_imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $= e0_imim12i e1_imim12i f2_imim12i f3_imim12i f1_imim12i p_imim2i f0_imim12i f1_imim12i f1_imim12i f2_imim12i a_wi f3_imim12i p_syl5 $.
$}

$(Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Aug-2012.) $)

${
	$v ph ps ch  $.
	f0_imim1i $f wff ph $.
	f1_imim1i $f wff ps $.
	f2_imim1i $f wff ch $.
	e0_imim1i $e |- ( ph -> ps ) $.
	p_imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $= e0_imim1i f2_imim1i p_id f0_imim1i f1_imim1i f2_imim1i f2_imim1i p_imim12i $.
$}

$(Inference adding three nested antecedents.  (Contributed by NM,
       19-Dec-2006.) $)

${
	$v ph ps ch th  $.
	f0_imim3i $f wff ph $.
	f1_imim3i $f wff ps $.
	f2_imim3i $f wff ch $.
	f3_imim3i $f wff th $.
	e0_imim3i $e |- ( ph -> ( ps -> ch ) ) $.
	p_imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $= e0_imim3i f0_imim3i f1_imim3i f2_imim3i a_wi f3_imim3i p_imim2i f3_imim3i f0_imim3i a_wi f3_imim3i f1_imim3i f2_imim3i p_a2d $.
$}

$(A syllogism inference combined with contraction.  (Contributed by NM,
       4-May-1994.)  (Revised by NM, 13-Jul-2013.) $)

${
	$v ph ps ch th  $.
	f0_sylc $f wff ph $.
	f1_sylc $f wff ps $.
	f2_sylc $f wff ch $.
	f3_sylc $f wff th $.
	e0_sylc $e |- ( ph -> ps ) $.
	e1_sylc $e |- ( ph -> ch ) $.
	e2_sylc $e |- ( ps -> ( ch -> th ) ) $.
	p_sylc $p |- ( ph -> th ) $= e0_sylc e1_sylc e2_sylc f0_sylc f1_sylc f0_sylc f2_sylc f3_sylc p_syl2im f0_sylc f3_sylc p_pm2.43i $.
$}

$(A syllogism inference combined with contraction. ~ e111 without virtual
       deductions.  (Contributed by Alan Sare, 7-Jul-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_syl3c $f wff ph $.
	f1_syl3c $f wff ps $.
	f2_syl3c $f wff ch $.
	f3_syl3c $f wff th $.
	f4_syl3c $f wff ta $.
	e0_syl3c $e |- ( ph -> ps ) $.
	e1_syl3c $e |- ( ph -> ch ) $.
	e2_syl3c $e |- ( ph -> th ) $.
	e3_syl3c $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
	p_syl3c $p |- ( ph -> ta ) $= e2_syl3c e0_syl3c e1_syl3c e3_syl3c f0_syl3c f1_syl3c f2_syl3c f3_syl3c f4_syl3c a_wi p_sylc f0_syl3c f3_syl3c f4_syl3c p_mpd $.
$}

$(~ e20 without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof shortened by Wolf Lammen, 13-Sep-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_syl6mpi $f wff ph $.
	f1_syl6mpi $f wff ps $.
	f2_syl6mpi $f wff ch $.
	f3_syl6mpi $f wff th $.
	f4_syl6mpi $f wff ta $.
	e0_syl6mpi $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl6mpi $e |- th $.
	e2_syl6mpi $e |- ( ch -> ( th -> ta ) ) $.
	p_syl6mpi $p |- ( ph -> ( ps -> ta ) ) $= e0_syl6mpi e1_syl6mpi e2_syl6mpi f2_syl6mpi f3_syl6mpi f4_syl6mpi p_mpi f0_syl6mpi f1_syl6mpi f2_syl6mpi f4_syl6mpi p_syl6 $.
$}

$(Modus ponens combined with a syllogism inference.  (Contributed by Alan
       Sare, 20-Apr-2011.) $)

${
	$v ph ps ch th  $.
	f0_mpsyl $f wff ph $.
	f1_mpsyl $f wff ps $.
	f2_mpsyl $f wff ch $.
	f3_mpsyl $f wff th $.
	e0_mpsyl $e |- ph $.
	e1_mpsyl $e |- ( ps -> ch ) $.
	e2_mpsyl $e |- ( ph -> ( ch -> th ) ) $.
	p_mpsyl $p |- ( ps -> th ) $= e0_mpsyl f0_mpsyl f1_mpsyl p_a1i e1_mpsyl e2_mpsyl f1_mpsyl f0_mpsyl f2_mpsyl f3_mpsyl p_sylc $.
$}

$(Inference combining ~ syl6 with contraction.  (Contributed by Alan Sare,
       2-May-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_syl6c $f wff ph $.
	f1_syl6c $f wff ps $.
	f2_syl6c $f wff ch $.
	f3_syl6c $f wff th $.
	f4_syl6c $f wff ta $.
	e0_syl6c $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl6c $e |- ( ph -> ( ps -> th ) ) $.
	e2_syl6c $e |- ( ch -> ( th -> ta ) ) $.
	p_syl6c $p |- ( ph -> ( ps -> ta ) ) $= e1_syl6c e0_syl6c e2_syl6c f0_syl6c f1_syl6c f2_syl6c f3_syl6c f4_syl6c a_wi p_syl6 f0_syl6c f1_syl6c f3_syl6c f4_syl6c p_mpdd $.
$}

$(Nested syllogism deduction.  (Contributed by NM, 12-Dec-2004.)  (Proof
       shortened by Wolf Lammen, 11-May-2013.) $)

${
	$v ph ps ch th ta  $.
	f0_syldd $f wff ph $.
	f1_syldd $f wff ps $.
	f2_syldd $f wff ch $.
	f3_syldd $f wff th $.
	f4_syldd $f wff ta $.
	e0_syldd $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	e1_syldd $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
	p_syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= e1_syldd e0_syldd f3_syldd f4_syldd f2_syldd p_imim2 f0_syldd f1_syldd f3_syldd f4_syldd a_wi f2_syldd f3_syldd a_wi f2_syldd f4_syldd a_wi p_syl6c $.
$}

$(A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_syl5d $f wff ph $.
	f1_syl5d $f wff ps $.
	f2_syl5d $f wff ch $.
	f3_syl5d $f wff th $.
	f4_syl5d $f wff ta $.
	e0_syl5d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl5d $e |- ( ph -> ( th -> ( ch -> ta ) ) ) $.
	p_syl5d $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $= e0_syl5d f0_syl5d f1_syl5d f2_syl5d a_wi f3_syl5d p_a1d e1_syl5d f0_syl5d f3_syl5d f1_syl5d f2_syl5d f4_syl5d p_syldd $.
$}

$(A syllogism rule of inference.  The first premise is used to replace the
       third antecedent of the second premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_syl7 $f wff ph $.
	f1_syl7 $f wff ps $.
	f2_syl7 $f wff ch $.
	f3_syl7 $f wff th $.
	f4_syl7 $f wff ta $.
	e0_syl7 $e |- ( ph -> ps ) $.
	e1_syl7 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
	p_syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $= e0_syl7 f0_syl7 f1_syl7 a_wi f2_syl7 p_a1i e1_syl7 f2_syl7 f0_syl7 f1_syl7 f3_syl7 f4_syl7 p_syl5d $.
$}

$(A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.) $)

${
	$v ph ps ch th ta  $.
	f0_syl6d $f wff ph $.
	f1_syl6d $f wff ps $.
	f2_syl6d $f wff ch $.
	f3_syl6d $f wff th $.
	f4_syl6d $f wff ta $.
	e0_syl6d $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	e1_syl6d $e |- ( ph -> ( th -> ta ) ) $.
	p_syl6d $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= e0_syl6d e1_syl6d f0_syl6d f3_syl6d f4_syl6d a_wi f1_syl6d p_a1d f0_syl6d f1_syl6d f2_syl6d f3_syl6d f4_syl6d p_syldd $.
$}

$(A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 1-Aug-1994.)
       (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_syl8 $f wff ph $.
	f1_syl8 $f wff ps $.
	f2_syl8 $f wff ch $.
	f3_syl8 $f wff th $.
	f4_syl8 $f wff ta $.
	e0_syl8 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	e1_syl8 $e |- ( th -> ta ) $.
	p_syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= e0_syl8 e1_syl8 f3_syl8 f4_syl8 a_wi f0_syl8 p_a1i f0_syl8 f1_syl8 f2_syl8 f3_syl8 f4_syl8 p_syl6d $.
$}

$(A nested syllogism inference with different antecedents.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)

${
	$v ph ps ch th ta  $.
	f0_syl9 $f wff ph $.
	f1_syl9 $f wff ps $.
	f2_syl9 $f wff ch $.
	f3_syl9 $f wff th $.
	f4_syl9 $f wff ta $.
	e0_syl9 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl9 $e |- ( th -> ( ch -> ta ) ) $.
	p_syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $= e0_syl9 e1_syl9 f3_syl9 f2_syl9 f4_syl9 a_wi a_wi f0_syl9 p_a1i f0_syl9 f1_syl9 f2_syl9 f3_syl9 f4_syl9 p_syl5d $.
$}

$(A nested syllogism inference with different antecedents.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v ph ps ch th ta  $.
	f0_syl9r $f wff ph $.
	f1_syl9r $f wff ps $.
	f2_syl9r $f wff ch $.
	f3_syl9r $f wff th $.
	f4_syl9r $f wff ta $.
	e0_syl9r $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl9r $e |- ( th -> ( ch -> ta ) ) $.
	p_syl9r $p |- ( th -> ( ph -> ( ps -> ta ) ) ) $= e0_syl9r e1_syl9r f0_syl9r f1_syl9r f2_syl9r f3_syl9r f4_syl9r p_syl9 f0_syl9r f3_syl9r f1_syl9r f4_syl9r a_wi p_com12 $.
$}

$(Deduction combining antecedents and consequents.  (Contributed by NM,
       7-Aug-1994.)  (Proof shortened by O'Cat, 30-Oct-2011.) $)

${
	$v ph ps ch th ta  $.
	f0_imim12d $f wff ph $.
	f1_imim12d $f wff ps $.
	f2_imim12d $f wff ch $.
	f3_imim12d $f wff th $.
	f4_imim12d $f wff ta $.
	e0_imim12d $e |- ( ph -> ( ps -> ch ) ) $.
	e1_imim12d $e |- ( ph -> ( th -> ta ) ) $.
	p_imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $= e0_imim12d e1_imim12d f0_imim12d f3_imim12d f4_imim12d f2_imim12d p_imim2d f0_imim12d f1_imim12d f2_imim12d f2_imim12d f3_imim12d a_wi f4_imim12d p_syl5d $.
$}

$(Deduction adding nested consequents.  (Contributed by NM, 3-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2012.) $)

${
	$v ph ps ch th  $.
	f0_imim1d $f wff ph $.
	f1_imim1d $f wff ps $.
	f2_imim1d $f wff ch $.
	f3_imim1d $f wff th $.
	e0_imim1d $e |- ( ph -> ( ps -> ch ) ) $.
	p_imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $= e0_imim1d f0_imim1d f3_imim1d p_idd f0_imim1d f1_imim1d f2_imim1d f3_imim1d f3_imim1d p_imim12d $.
$}

$(A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
     [WhiteheadRussell] p. 100.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 25-May-2013.) $)

${
	$v ph ps ch  $.
	f0_imim1 $f wff ph $.
	f1_imim1 $f wff ps $.
	f2_imim1 $f wff ch $.
	p_imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= f0_imim1 f1_imim1 a_wi p_id f0_imim1 f1_imim1 a_wi f0_imim1 f1_imim1 f2_imim1 p_imim1d $.
$}

$(Theorem *2.83 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)

${
	$v ph ps ch th  $.
	f0_pm2.83 $f wff ph $.
	f1_pm2.83 $f wff ps $.
	f2_pm2.83 $f wff ch $.
	f3_pm2.83 $f wff th $.
	p_pm2.83 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ( ch -> th ) ) -> ( ph -> ( ps -> th ) ) ) ) $= f1_pm2.83 f2_pm2.83 f3_pm2.83 p_imim1 f1_pm2.83 f2_pm2.83 a_wi f2_pm2.83 f3_pm2.83 a_wi f1_pm2.83 f3_pm2.83 a_wi f0_pm2.83 p_imim3i $.
$}

$(Commutation of antecedents.  Swap 2nd and 3rd.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Aug-2012.) $)

${
	$v ph ps ch th  $.
	f0_com23 $f wff ph $.
	f1_com23 $f wff ps $.
	f2_com23 $f wff ch $.
	f3_com23 $f wff th $.
	e0_com23 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $= e0_com23 f2_com23 f3_com23 p_pm2.27 f0_com23 f1_com23 f2_com23 f3_com23 a_wi f2_com23 f3_com23 p_syl9 $.
$}

$(Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)

${
	$v ph ps ch th  $.
	f0_com3r $f wff ph $.
	f1_com3r $f wff ps $.
	f2_com3r $f wff ch $.
	f3_com3r $f wff th $.
	e0_com3r $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $= e0_com3r f0_com3r f1_com3r f2_com3r f3_com3r p_com23 f0_com3r f2_com3r f1_com3r f3_com3r a_wi p_com12 $.
$}

$(Commutation of antecedents.  Swap 1st and 3rd.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)

${
	$v ph ps ch th  $.
	f0_com13 $f wff ph $.
	f1_com13 $f wff ps $.
	f2_com13 $f wff ch $.
	f3_com13 $f wff th $.
	e0_com13 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $= e0_com13 f0_com13 f1_com13 f2_com13 f3_com13 p_com3r f2_com13 f0_com13 f1_com13 f3_com13 p_com23 $.
$}

$(Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)

${
	$v ph ps ch th  $.
	f0_com3l $f wff ph $.
	f1_com3l $f wff ps $.
	f2_com3l $f wff ch $.
	f3_com3l $f wff th $.
	e0_com3l $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $= e0_com3l f0_com3l f1_com3l f2_com3l f3_com3l p_com3r f2_com3l f0_com3l f1_com3l f3_com3l p_com3r $.
$}

$(Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     12-Sep-2012.) $)

${
	$v ph ps ch  $.
	f0_pm2.04 $f wff ph $.
	f1_pm2.04 $f wff ps $.
	f2_pm2.04 $f wff ch $.
	p_pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $= f0_pm2.04 f1_pm2.04 f2_pm2.04 a_wi a_wi p_id f0_pm2.04 f1_pm2.04 f2_pm2.04 a_wi a_wi f0_pm2.04 f1_pm2.04 f2_pm2.04 p_com23 $.
$}

$(Commutation of antecedents.  Swap 3rd and 4th.  (Contributed by NM,
       25-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_com34 $f wff ph $.
	f1_com34 $f wff ps $.
	f2_com34 $f wff ch $.
	f3_com34 $f wff th $.
	f4_com34 $f wff ta $.
	e0_com34 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_com34 $p |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) $= e0_com34 f2_com34 f3_com34 f4_com34 p_pm2.04 f0_com34 f1_com34 f2_com34 f3_com34 f4_com34 a_wi a_wi f3_com34 f2_com34 f4_com34 a_wi a_wi p_syl6 $.
$}

$(Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by O'Cat, 15-Aug-2004.) $)

${
	$v ph ps ch th ta  $.
	f0_com4l $f wff ph $.
	f1_com4l $f wff ps $.
	f2_com4l $f wff ch $.
	f3_com4l $f wff th $.
	f4_com4l $f wff ta $.
	e0_com4l $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_com4l $p |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) ) $= e0_com4l f0_com4l f1_com4l f2_com4l f3_com4l f4_com4l a_wi p_com3l f1_com4l f2_com4l f0_com4l f3_com4l f4_com4l p_com34 $.
$}

$(Commutation of antecedents.  Rotate twice.  (Contributed by NM,
       25-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_com4t $f wff ph $.
	f1_com4t $f wff ps $.
	f2_com4t $f wff ch $.
	f3_com4t $f wff th $.
	f4_com4t $f wff ta $.
	e0_com4t $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_com4t $p |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) ) $= e0_com4t f0_com4t f1_com4t f2_com4t f3_com4t f4_com4t p_com4l f1_com4t f2_com4t f3_com4t f0_com4t f4_com4t p_com4l $.
$}

$(Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)

${
	$v ph ps ch th ta  $.
	f0_com4r $f wff ph $.
	f1_com4r $f wff ps $.
	f2_com4r $f wff ch $.
	f3_com4r $f wff th $.
	f4_com4r $f wff ta $.
	e0_com4r $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_com4r $p |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) $= e0_com4r f0_com4r f1_com4r f2_com4r f3_com4r f4_com4r p_com4t f2_com4r f3_com4r f0_com4r f1_com4r f4_com4r p_com4l $.
$}

$(Commutation of antecedents.  Swap 2nd and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_com24 $f wff ph $.
	f1_com24 $f wff ps $.
	f2_com24 $f wff ch $.
	f3_com24 $f wff th $.
	f4_com24 $f wff ta $.
	e0_com24 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_com24 $p |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) ) $= e0_com24 f0_com24 f1_com24 f2_com24 f3_com24 f4_com24 p_com4t f2_com24 f3_com24 f0_com24 f1_com24 f4_com24 a_wi p_com13 $.
$}

$(Commutation of antecedents.  Swap 1st and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)

${
	$v ph ps ch th ta  $.
	f0_com14 $f wff ph $.
	f1_com14 $f wff ps $.
	f2_com14 $f wff ch $.
	f3_com14 $f wff th $.
	f4_com14 $f wff ta $.
	e0_com14 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	p_com14 $p |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) ) $= e0_com14 f0_com14 f1_com14 f2_com14 f3_com14 f4_com14 p_com4l f1_com14 f2_com14 f3_com14 f0_com14 f4_com14 a_wi p_com3r $.
$}

$(Commutation of antecedents.  Swap 4th and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_com45 $f wff ph $.
	f1_com45 $f wff ps $.
	f2_com45 $f wff ch $.
	f3_com45 $f wff th $.
	f4_com45 $f wff ta $.
	f5_com45 $f wff et $.
	e0_com45 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_com45 $p |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) $= e0_com45 f3_com45 f4_com45 f5_com45 p_pm2.04 f0_com45 f1_com45 f2_com45 f3_com45 f4_com45 f5_com45 a_wi a_wi f4_com45 f3_com45 f5_com45 a_wi a_wi p_syl8 $.
$}

$(Commutation of antecedents.  Swap 3rd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_com35 $f wff ph $.
	f1_com35 $f wff ps $.
	f2_com35 $f wff ch $.
	f3_com35 $f wff th $.
	f4_com35 $f wff ta $.
	f5_com35 $f wff et $.
	e0_com35 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_com35 $p |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) ) $= e0_com35 f0_com35 f1_com35 f2_com35 f3_com35 f4_com35 f5_com35 a_wi p_com34 f0_com35 f1_com35 f3_com35 f2_com35 f4_com35 f5_com35 p_com45 f0_com35 f1_com35 f3_com35 f4_com35 f2_com35 f5_com35 a_wi p_com34 $.
$}

$(Commutation of antecedents.  Swap 2nd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_com25 $f wff ph $.
	f1_com25 $f wff ps $.
	f2_com25 $f wff ch $.
	f3_com25 $f wff th $.
	f4_com25 $f wff ta $.
	f5_com25 $f wff et $.
	e0_com25 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_com25 $p |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) ) $= e0_com25 f0_com25 f1_com25 f2_com25 f3_com25 f4_com25 f5_com25 a_wi p_com24 f0_com25 f3_com25 f2_com25 f1_com25 f4_com25 f5_com25 p_com45 f0_com25 f3_com25 f2_com25 f4_com25 f1_com25 f5_com25 a_wi p_com24 $.
$}

$(Commutation of antecedents.  Rotate left.  (Contributed by Jeff Hankins,
       28-Jun-2009.)  (Proof shortened by Wolf Lammen, 29-Jul-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_com5l $f wff ph $.
	f1_com5l $f wff ps $.
	f2_com5l $f wff ch $.
	f3_com5l $f wff th $.
	f4_com5l $f wff ta $.
	f5_com5l $f wff et $.
	e0_com5l $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_com5l $p |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) ) $= e0_com5l f0_com5l f1_com5l f2_com5l f3_com5l f4_com5l f5_com5l a_wi p_com4l f1_com5l f2_com5l f3_com5l f0_com5l f4_com5l f5_com5l p_com45 $.
$}

$(Commutation of antecedents.  Swap 1st and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.)  (Proof shortened by Wolf Lammen,
       29-Jul-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_com15 $f wff ph $.
	f1_com15 $f wff ps $.
	f2_com15 $f wff ch $.
	f3_com15 $f wff th $.
	f4_com15 $f wff ta $.
	f5_com15 $f wff et $.
	e0_com15 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_com15 $p |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) ) $= e0_com15 f0_com15 f1_com15 f2_com15 f3_com15 f4_com15 f5_com15 p_com5l f1_com15 f2_com15 f3_com15 f4_com15 f0_com15 f5_com15 a_wi p_com4r $.
$}

$(Commutation of antecedents.  Rotate left twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_com52l $f wff ph $.
	f1_com52l $f wff ps $.
	f2_com52l $f wff ch $.
	f3_com52l $f wff th $.
	f4_com52l $f wff ta $.
	f5_com52l $f wff et $.
	e0_com52l $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_com52l $p |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) ) $= e0_com52l f0_com52l f1_com52l f2_com52l f3_com52l f4_com52l f5_com52l p_com5l f1_com52l f2_com52l f3_com52l f4_com52l f0_com52l f5_com52l p_com5l $.
$}

$(Commutation of antecedents.  Rotate right twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)

${
	$v ph ps ch th ta et  $.
	f0_com52r $f wff ph $.
	f1_com52r $f wff ps $.
	f2_com52r $f wff ch $.
	f3_com52r $f wff th $.
	f4_com52r $f wff ta $.
	f5_com52r $f wff et $.
	e0_com52r $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_com52r $p |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) ) $= e0_com52r f0_com52r f1_com52r f2_com52r f3_com52r f4_com52r f5_com52r p_com52l f2_com52r f3_com52r f4_com52r f0_com52r f1_com52r f5_com52r p_com5l $.
$}

$(Commutation of antecedents.  Rotate right.  (Contributed by Wolf Lammen,
       29-Jul-2012.) $)

${
	$v ph ps ch th ta et  $.
	f0_com5r $f wff ph $.
	f1_com5r $f wff ps $.
	f2_com5r $f wff ch $.
	f3_com5r $f wff th $.
	f4_com5r $f wff ta $.
	f5_com5r $f wff et $.
	e0_com5r $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
	p_com5r $p |- ( ta -> ( ph -> ( ps -> ( ch -> ( th -> et ) ) ) ) ) $= e0_com5r f0_com5r f1_com5r f2_com5r f3_com5r f4_com5r f5_com5r p_com52l f2_com5r f3_com5r f4_com5r f0_com5r f1_com5r f5_com5r p_com52l $.
$}

$(Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 9-May-2013.) $)

${
	$v ph ps ch  $.
	f0_jarr $f wff ph $.
	f1_jarr $f wff ps $.
	f2_jarr $f wff ch $.
	p_jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $= f1_jarr f0_jarr a_ax-1 f1_jarr f0_jarr f1_jarr a_wi f2_jarr p_imim1i $.
$}

$(Inference based on ~ pm2.86 .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 3-Apr-2013.) $)

${
	$v ph ps ch  $.
	f0_pm2.86i $f wff ph $.
	f1_pm2.86i $f wff ps $.
	f2_pm2.86i $f wff ch $.
	e0_pm2.86i $e |- ( ( ph -> ps ) -> ( ph -> ch ) ) $.
	p_pm2.86i $p |- ( ph -> ( ps -> ch ) ) $= f1_pm2.86i f0_pm2.86i a_ax-1 e0_pm2.86i f1_pm2.86i f0_pm2.86i f1_pm2.86i a_wi f0_pm2.86i f2_pm2.86i a_wi p_syl f1_pm2.86i f0_pm2.86i f2_pm2.86i p_com12 $.
$}

$(Deduction based on ~ pm2.86 .  (Contributed by NM, 29-Jun-1995.)  (Proof
       shortened by Wolf Lammen, 3-Apr-2013.) $)

${
	$v ph ps ch th  $.
	f0_pm2.86d $f wff ph $.
	f1_pm2.86d $f wff ps $.
	f2_pm2.86d $f wff ch $.
	f3_pm2.86d $f wff th $.
	e0_pm2.86d $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
	p_pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= f2_pm2.86d f1_pm2.86d a_ax-1 e0_pm2.86d f2_pm2.86d f1_pm2.86d f2_pm2.86d a_wi f0_pm2.86d f1_pm2.86d f3_pm2.86d a_wi p_syl5 f0_pm2.86d f2_pm2.86d f1_pm2.86d f3_pm2.86d p_com23 $.
$}

$(Converse of axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
     (Contributed by NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen,
     3-Apr-2013.) $)

${
	$v ph ps ch  $.
	f0_pm2.86 $f wff ph $.
	f1_pm2.86 $f wff ps $.
	f2_pm2.86 $f wff ch $.
	p_pm2.86 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) ) $= f0_pm2.86 f1_pm2.86 a_wi f0_pm2.86 f2_pm2.86 a_wi a_wi p_id f0_pm2.86 f1_pm2.86 a_wi f0_pm2.86 f2_pm2.86 a_wi a_wi f0_pm2.86 f1_pm2.86 f2_pm2.86 p_pm2.86d $.
$}

$(The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  This version of ~ loolin does not use ~ ax-3 , meaning
     that this theorem is intuitionistically valid.  (Contributed by O'Cat,
     12-Aug-2004.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)

${
	$v ph ps  $.
	f0_loolinALT $f wff ph $.
	f1_loolinALT $f wff ps $.
	p_loolinALT $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $= f0_loolinALT f1_loolinALT f1_loolinALT f0_loolinALT a_wi p_jarr f0_loolinALT f1_loolinALT a_wi f1_loolinALT f0_loolinALT a_wi a_wi f1_loolinALT f0_loolinALT p_pm2.43d $.
$}

$(An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz, due to Barbara Wozniakowska, _Reports
     on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by O'Cat,
     8-Aug-2004.) $)

${
	$v ph ps ch  $.
	f0_loowoz $f wff ph $.
	f1_loowoz $f wff ps $.
	f2_loowoz $f wff ch $.
	p_loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ( ps -> ph ) -> ( ps -> ch ) ) ) $= f0_loowoz f1_loowoz f0_loowoz f2_loowoz a_wi p_jarr f0_loowoz f1_loowoz a_wi f0_loowoz f2_loowoz a_wi a_wi f1_loowoz f0_loowoz f2_loowoz p_a2d $.
$}


