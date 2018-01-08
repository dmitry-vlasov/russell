
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/The_axioms_of_propositional_calculus.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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

  ${
    mp2b.1 $e |- ph $.
    mp2b.2 $e |- ( ph -> ps ) $.
    mp2b.3 $e |- ( ps -> ch ) $.
    $( A double modus ponens inference.  (Contributed by Mario Carneiro,
       24-Jan-2013.) $)
    mp2b $p |- ch $=
      wps wch wph wps mp2b.1 mp2b.2 ax-mp mp2b.3 ax-mp $.
  $}

  ${
    $( Premise for ~ a1i . $)
    a1i.1 $e |- ph $.
    $( Inference derived from axiom ~ ax-1 .  See ~ a1d for an explanation of
       our informal use of the terms "inference" and "deduction."  See also the
       comment in ~ syld .  (Contributed by NM, 5-Aug-1993.) $)
    a1i $p |- ( ps -> ph ) $=
      wph wps wph wi a1i.1 wph wps ax-1 ax-mp $.
  $}

  ${
    mp1i.a $e |- ph $.
    mp1i.b $e |- ( ph -> ps ) $.
    $( Drop and replace an antecedent.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) $)
    mp1i $p |- ( ch -> ps ) $=
      wps wch wph wps mp1i.a mp1i.b ax-mp a1i $.
  $}

  ${
    $( Premise for ~ a2i . $)
    a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference derived from axiom ~ ax-2 .  (Contributed by NM,
       5-Aug-1993.) $)
    a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
      wph wps wch wi wi wph wps wi wph wch wi wi a2i.1 wph wps wch ax-2 ax-mp
      $.
  $}

  ${
    imim2i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common antecedents in an implication.  (Contributed by
       NM, 5-Aug-1993.) $)
    imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
      wch wph wps wph wps wi wch imim2i.1 a1i a2i $.
  $}

  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A modus ponens deduction.  A translation of natural deduction rule
       ` -> ` E ( ` -> ` elimination), see ~ natded .  (Contributed by NM,
       5-Aug-1993.) $)
    mpd $p |- ( ph -> ch ) $=
      wph wps wi wph wch wi mpd.1 wph wps wch mpd.2 a2i ax-mp $.
  $}

  ${
    $( First of 2 premises for ~ syl . $)
    syl.1 $e |- ( ph -> ps ) $.
    $( Second of 2 premises for ~ syl . $)
    syl.2 $e |- ( ps -> ch ) $.
    $( An inference version of the transitive laws for implication ~ imim2 and
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
    syl $p |- ( ph -> ch ) $=
      wph wps wch syl.1 wps wch wi wph syl.2 a1i mpd $.
  $}

  ${
    mpi.1 $e |- ps $.
    mpi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A nested modus ponens inference.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Stefan Allan, 20-Mar-2006.) $)
    mpi $p |- ( ph -> ch ) $=
      wph wps wch wps wph mpi.1 a1i mpi.2 mpd $.
  $}

  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A double modus ponens inference.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
    mp2 $p |- ch $=
      wph wch mp2.1 wph wps wch mp2.2 mp2.3 mpi ax-mp $.
  $}

  ${
    3syl.1 $e |- ( ph -> ps ) $.
    3syl.2 $e |- ( ps -> ch ) $.
    3syl.3 $e |- ( ch -> th ) $.
    $( Inference chaining two syllogisms.  (Contributed by NM, 5-Aug-1993.) $)
    3syl $p |- ( ph -> th ) $=
      wph wch wth wph wps wch 3syl.1 3syl.2 syl 3syl.3 syl $.
  $}

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ id1 .
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Stefan Allan,
     20-Mar-2006.) $)
  id $p |- ( ph -> ph ) $=
    wph wph wph wi wph wph wph ax-1 wph wph wph wi ax-1 mpd $.

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  This
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
  id1 $p |- ( ph -> ph ) $=
    wph wph wph wi wi wph wph wi wph wph ax-1 wph wph wph wi wph wi wi wph wph
    wph wi wi wph wph wi wi wph wph wph wi ax-1 wph wph wph wi wph ax-2 ax-mp
    ax-mp $.

  $( Principle of identity with antecedent.  (Contributed by NM,
     26-Nov-1995.) $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    wps wps wi wph wps id a1i $.

  ${
    a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.

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
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      wph wps wch wps wi a1d.1 wps wch ax-1 syl $.
  $}

  ${
    a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Deduction distributing an embedded antecedent.  (Contributed by NM,
       23-Jun-1994.) $)
    a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
      wph wps wch wth wi wi wps wch wi wps wth wi wi a2d.1 wps wch wth ax-2 syl
      $.
  $}

  ${
    a1ii.1 $e |- ch $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
    a1ii $p |- ( ph -> ( ps -> ch ) ) $=
      wph wch wps wch wph a1ii.1 a1i a1d $.
  $}

  ${
    sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
    $( Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 29-Aug-2004.)  (Proof shortened by O'Cat, 2-Feb-2006.)  (Proof
       shortened by Stefan Allan, 23-Feb-2006.) $)
    sylcom $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wi wps wth wi sylcom.1 wps wch wth sylcom.2 a2i syl $.
  $}

  ${
    syl5com.1 $e |- ( ph -> ps ) $.
    syl5com.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Syllogism inference with commuted antecedents.  (Contributed by NM,
       24-May-2005.) $)
    syl5com $p |- ( ph -> ( ch -> th ) ) $=
      wph wch wps wth wph wps wch syl5com.1 a1d syl5com.2 sylcom $.
  $}

  ${
    $( Premise for ~ com12 .  See ~ pm2.04 for the theorem form. $)
    com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference that swaps (commutes) antecedents in an implication.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       4-Aug-2012.) $)
    com12 $p |- ( ps -> ( ph -> ch ) ) $=
      wps wps wph wch wps id com12.1 syl5com $.
  $}

  ${
    syl5.1 $e |- ( ph -> ps ) $.
    syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A syllogism rule of inference.  The first premise is used to replace the
       second antecedent of the second premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-May-2013.) $)
    syl5 $p |- ( ch -> ( ph -> th ) ) $=
      wph wch wth wph wps wch wth syl5.1 syl5.2 syl5com com12 $.
  $}

  ${
    syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6.2 $e |- ( ch -> th ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Wolf Lammen, 30-Jul-2012.) $)
    syl6 $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth syl6.1 wch wth wi wps syl6.2 a1i sylcom $.
  $}

  ${
    syl56.1 $e |- ( ph -> ps ) $.
    syl56.2 $e |- ( ch -> ( ps -> th ) ) $.
    syl56.3 $e |- ( th -> ta ) $.
    $( Combine ~ syl5 and ~ syl6 .  (Contributed by NM, 14-Nov-2013.) $)
    syl56 $p |- ( ch -> ( ph -> ta ) ) $=
      wph wps wch wta syl56.1 wch wps wth wta syl56.2 syl56.3 syl6 syl5 $.
  $}

  ${
    syl6com.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6com.2 $e |- ( ch -> th ) $.
    $( Syllogism inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    syl6com $p |- ( ps -> ( ph -> th ) ) $=
      wph wps wth wph wps wch wth syl6com.1 syl6com.2 syl6 com12 $.
  $}

  ${
    mpcom.1 $e |- ( ps -> ph ) $.
    mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus ponens inference with commutation of antecedents.  (Contributed by
       NM, 17-Mar-1996.) $)
    mpcom $p |- ( ps -> ch ) $=
      wps wph wch mpcom.1 wph wps wch mpcom.2 com12 mpd $.
  $}

  ${
    syli.1 $e |- ( ps -> ( ph -> ch ) ) $.
    syli.2 $e |- ( ch -> ( ph -> th ) ) $.
    $( Syllogism inference with common nested antecedent.  (Contributed by NM,
       4-Nov-2004.) $)
    syli $p |- ( ps -> ( ph -> th ) ) $=
      wps wph wch wth syli.1 wch wph wth syli.2 com12 sylcom $.
  $}

  ${
    syl2im.1 $e |- ( ph -> ps ) $.
    syl2im.2 $e |- ( ch -> th ) $.
    syl2im.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Replace two antecedents.  Implication-only version of ~ syl2an .
       (Contributed by Wolf Lammen, 14-May-2013.) $)
    syl2im $p |- ( ph -> ( ch -> ta ) ) $=
      wph wps wch wta wi syl2im.1 wch wth wps wta syl2im.2 syl2im.3 syl5 syl $.
  $}

  $( This theorem, called "Assertion," can be thought of as closed form of
     modus ponens ~ ax-mp .  Theorem *2.27 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 5-Aug-1993.) $)
  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    wph wps wi wph wps wph wps wi id com12 $.

  ${
    mpdd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    mpdd.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (Contributed by NM, 12-Dec-2004.) $)
    mpdd $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wi wps wth wi mpdd.1 wph wps wch wth mpdd.2 a2d mpd $.
  $}

  ${
    mpid.1 $e |- ( ph -> ch ) $.
    mpid.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (Contributed by NM, 14-Dec-2004.) $)
    mpid $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wch wps mpid.1 a1d mpid.2 mpdd $.
  $}

  ${
    mpdi.1 $e |- ( ps -> ch ) $.
    mpdi.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (Contributed by NM, 16-Apr-2005.)
       (Proof shortened by O'Cat, 15-Jan-2008.) $)
    mpdi $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wps wch wi wph mpdi.1 a1i mpdi.2 mpdd $.
  $}

  ${
    mpii.1 $e |- ch $.
    mpii.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A doubly nested modus ponens inference.  (Contributed by NM,
       31-Dec-1993.)  (Proof shortened by Wolf Lammen, 31-Jul-2012.) $)
    mpii $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wch wps mpii.1 a1i mpii.2 mpdi $.
  $}

  ${
    syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 19-Feb-2008.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.)

       Notice that ~ syld has the same form as ~ syl with ` ph ` added in front
       of each hypothesis and conclusion.  When all theorems referenced in a
       proof are converted in this way, we can replace ` ph ` with a hypothesis
       of the proof, allowing the hypothesis to be eliminated with ~ id and
       become an antecedent.  The Deduction Theorem for propositional calculus,
       e.g.  Theorem 3 in [Margaris] p. 56, tells us that this procedure is
       always possible. $)
    syld $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth syld.1 wph wch wth wi wps syld.2 a1d mpdd $.
  $}

  ${
    mp2d.1 $e |- ( ph -> ps ) $.
    mp2d.2 $e |- ( ph -> ch ) $.
    mp2d.3 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A double modus ponens deduction.  (Contributed by NM, 23-May-2013.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
    mp2d $p |- ( ph -> th ) $=
      wph wps wth mp2d.1 wph wps wch wth mp2d.2 mp2d.3 mpid mpd $.
  $}

  ${
    a1dd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction introducing a nested embedded antecedent.  (Contributed by NM,
       17-Dec-2004.)  (Proof shortened by O'Cat, 15-Jan-2008.) $)
    a1dd $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      wph wps wch wth wch wi a1dd.1 wch wth ax-1 syl6 $.
  $}

  ${
    pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
    $( Inference absorbing redundant antecedent.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)
    pm2.43i $p |- ( ph -> ps ) $=
      wph wph wps wph id pm2.43i.1 mpd $.
  $}

  ${
    pm2.43d.1 $e |- ( ph -> ( ps -> ( ps -> ch ) ) ) $.
    $( Deduction absorbing redundant antecedent.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)
    pm2.43d $p |- ( ph -> ( ps -> ch ) ) $=
      wph wps wps wch wps id pm2.43d.1 mpdi $.
  $}

  ${
    pm2.43a.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (Contributed by NM,
       7-Nov-1995.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)
    pm2.43a $p |- ( ps -> ( ph -> ch ) ) $=
      wps wph wps wch wps id pm2.43a.1 mpid $.
  $}

  ${
    pm2.43b.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (Contributed by NM,
       31-Oct-1995.) $)
    pm2.43b $p |- ( ph -> ( ps -> ch ) ) $=
      wps wph wch wph wps wch pm2.43b.1 pm2.43a com12 $.
  $}

  $( Absorption of redundant antecedent.  Also called the "Contraction" or
     "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by O'Cat,
     15-Aug-2004.) $)
  pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    wph wph wps wi wps wph wps pm2.27 a2i $.

  ${
    imim2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested antecedents.  (Contributed by NM,
       5-Aug-1993.) $)
    imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      wph wth wps wch wph wps wch wi wth imim2d.1 a1d a2d $.
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 6-Sep-2012.) $)
  imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    wph wps wi wph wps wch wph wps wi id imim2d $.

  ${
    embantd.1 $e |- ( ph -> ps ) $.
    embantd.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction embedding an antecedent.  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)
    embantd $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      wph wps wch wi wps wth embantd.1 wph wch wth wps embantd.2 imim2d mpid $.
  $}

  ${
    3syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    3syld.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( Triple syllogism deduction.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    3syld $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wth wta wph wps wch wth 3syld.1 3syld.2 syld 3syld.3 syld $.
  $}

  ${
    sylsyld.1 $e |- ( ph -> ps ) $.
    sylsyld.2 $e |- ( ph -> ( ch -> th ) ) $.
    sylsyld.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Virtual deduction rule ~ e12 without virtual deduction symbols.
       (Contributed by Alan Sare, 20-Apr-2011.) $)
    sylsyld $p |- ( ph -> ( ch -> ta ) ) $=
      wph wch wth wta sylsyld.2 wph wps wth wta wi sylsyld.1 sylsyld.3 syl syld
      $.
  $}

  ${
    imim12i.1 $e |- ( ph -> ps ) $.
    imim12i.2 $e |- ( ch -> th ) $.
    $( Inference joining two implications.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by O'Cat, 29-Oct-2011.) $)
    imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $=
      wph wps wps wch wi wth imim12i.1 wch wth wps imim12i.2 imim2i syl5 $.
  $}

  ${
    imim1i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Aug-2012.) $)
    imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      wph wps wch wch imim1i.1 wch id imim12i $.
  $}

  ${
    imim3i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference adding three nested antecedents.  (Contributed by NM,
       19-Dec-2006.) $)
    imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      wth wph wi wth wps wch wph wps wch wi wth imim3i.1 imim2i a2d $.
  $}

  ${
    sylc.1 $e |- ( ph -> ps ) $.
    sylc.2 $e |- ( ph -> ch ) $.
    sylc.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A syllogism inference combined with contraction.  (Contributed by NM,
       4-May-1994.)  (Revised by NM, 13-Jul-2013.) $)
    sylc $p |- ( ph -> th ) $=
      wph wth wph wps wph wch wth sylc.1 sylc.2 sylc.3 syl2im pm2.43i $.
  $}

  ${
    syl3c.1 $e |- ( ph -> ps ) $.
    syl3c.2 $e |- ( ph -> ch ) $.
    syl3c.3 $e |- ( ph -> th ) $.
    syl3c.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A syllogism inference combined with contraction. ~ e111 without virtual
       deductions.  (Contributed by Alan Sare, 7-Jul-2011.) $)
    syl3c $p |- ( ph -> ta ) $=
      wph wth wta syl3c.3 wph wps wch wth wta wi syl3c.1 syl3c.2 syl3c.4 sylc
      mpd $.
  $}

  ${
    syl6mpi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6mpi.2 $e |- th $.
    syl6mpi.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( ~ e20 without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof shortened by Wolf Lammen, 13-Sep-2012.) $)
    syl6mpi $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wch wta syl6mpi.1 wch wth wta syl6mpi.2 syl6mpi.3 mpi syl6 $.
  $}

  ${
    mpsyl.1 $e |- ph $.
    mpsyl.2 $e |- ( ps -> ch ) $.
    mpsyl.3 $e |- ( ph -> ( ch -> th ) ) $.
    $( Modus ponens combined with a syllogism inference.  (Contributed by Alan
       Sare, 20-Apr-2011.) $)
    mpsyl $p |- ( ps -> th ) $=
      wps wph wch wth wph wps mpsyl.1 a1i mpsyl.2 mpsyl.3 sylc $.
  $}

  ${
    syl6c.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6c.2 $e |- ( ph -> ( ps -> th ) ) $.
    syl6c.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Inference combining ~ syl6 with contraction.  (Contributed by Alan Sare,
       2-May-2011.) $)
    syl6c $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wth wta syl6c.2 wph wps wch wth wta wi syl6c.1 syl6c.3 syl6 mpdd
      $.
  $}

  ${
    syldd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syldd.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    $( Nested syllogism deduction.  (Contributed by NM, 12-Dec-2004.)  (Proof
       shortened by Wolf Lammen, 11-May-2013.) $)
    syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      wph wps wth wta wi wch wth wi wch wta wi syldd.2 syldd.1 wth wta wch
      imim2 syl6c $.
  $}

  ${
    syl5d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5d.2 $e |- ( ph -> ( th -> ( ch -> ta ) ) ) $.
    $( A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.) $)
    syl5d $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      wph wth wps wch wta wph wps wch wi wth syl5d.1 a1d syl5d.2 syldd $.
  $}

  ${
    syl7.1 $e |- ( ph -> ps ) $.
    syl7.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A syllogism rule of inference.  The first premise is used to replace the
       third antecedent of the second premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      wch wph wps wth wta wph wps wi wch syl7.1 a1i syl7.2 syl5d $.
  $}

  ${
    syl6d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl6d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.) $)
    syl6d $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      wph wps wch wth wta syl6d.1 wph wth wta wi wps syl6d.2 a1d syldd $.
  $}

  ${
    syl8.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8.2 $e |- ( th -> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 1-Aug-1994.)
       (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      wph wps wch wth wta syl8.1 wth wta wi wph syl8.2 a1i syl6d $.
  $}

  ${
    syl9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
    syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      wph wps wch wth wta syl9.1 wth wch wta wi wi wph syl9.2 a1i syl5d $.
  $}

  ${
    syl9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (Contributed
       by NM, 5-Aug-1993.) $)
    syl9r $p |- ( th -> ( ph -> ( ps -> ta ) ) ) $=
      wph wth wps wta wi wph wps wch wth wta syl9r.1 syl9r.2 syl9 com12 $.
  $}

  ${
    imim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Deduction combining antecedents and consequents.  (Contributed by NM,
       7-Aug-1994.)  (Proof shortened by O'Cat, 30-Oct-2011.) $)
    imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $=
      wph wps wch wch wth wi wta imim12d.1 wph wth wta wch imim12d.2 imim2d
      syl5d $.
  $}

  ${
    imim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested consequents.  (Contributed by NM, 3-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2012.) $)
    imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $=
      wph wps wch wth wth imim1d.1 wph wth idd imim12d $.
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
     [WhiteheadRussell] p. 100.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 25-May-2013.) $)
  imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wph wps wi wph wps wch wph wps wi id imim1d $.

  $( Theorem *2.83 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.83 $p |- ( ( ph -> ( ps -> ch ) )
      -> ( ( ph -> ( ch -> th ) ) -> ( ph -> ( ps -> th ) ) ) ) $=
    wps wch wi wch wth wi wps wth wi wph wps wch wth imim1 imim3i $.

  ${
    com3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Commutation of antecedents.  Swap 2nd and 3rd.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Aug-2012.) $)
    com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      wph wps wch wth wi wch wth com3.1 wch wth pm2.27 syl9 $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)
    com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $=
      wph wch wps wth wi wph wps wch wth com3.1 com23 com12 $.

    $( Commutation of antecedents.  Swap 1st and 3rd.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $=
      wch wph wps wth wph wps wch wth com3.1 com3r com23 $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      wch wph wps wth wph wps wch wth com3.1 com3r com3r $.
  $}

  $( Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     12-Sep-2012.) $)
  pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wph wps wch wph wps wch wi wi id com23 $.

  ${
    com4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Commutation of antecedents.  Swap 3rd and 4th.  (Contributed by NM,
       25-Apr-1994.) $)
    com34 $p |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) $=
      wph wps wch wth wta wi wi wth wch wta wi wi com4.1 wch wth wta pm2.04
      syl6 $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by O'Cat, 15-Aug-2004.) $)
    com4l $p |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) ) $=
      wps wch wph wth wta wph wps wch wth wta wi com4.1 com3l com34 $.

    $( Commutation of antecedents.  Rotate twice.  (Contributed by NM,
       25-Apr-1994.) $)
    com4t $p |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) ) $=
      wps wch wth wph wta wph wps wch wth wta com4.1 com4l com4l $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)
    com4r $p |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) $=
      wch wth wph wps wta wph wps wch wth wta com4.1 com4t com4l $.

    $( Commutation of antecedents.  Swap 2nd and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com24 $p |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) ) $=
      wch wth wph wps wta wi wph wps wch wth wta com4.1 com4t com13 $.

    $( Commutation of antecedents.  Swap 1st and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com14 $p |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) ) $=
      wps wch wth wph wta wi wph wps wch wth wta com4.1 com4l com3r $.
  $}

  ${
    com5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( Commutation of antecedents.  Swap 4th and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com45 $p |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wi wta wth wet wi wi com5.1 wth wta wet pm2.04
      syl8 $.

    $( Commutation of antecedents.  Swap 3rd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com35 $p |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) ) $=
      wph wps wth wta wch wet wi wph wps wth wch wta wet wph wps wch wth wta
      wet wi com5.1 com34 com45 com34 $.

    $( Commutation of antecedents.  Swap 2nd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com25 $p |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) ) $=
      wph wth wch wta wps wet wi wph wth wch wps wta wet wph wps wch wth wta
      wet wi com5.1 com24 com45 com24 $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by Jeff Hankins,
       28-Jun-2009.)  (Proof shortened by Wolf Lammen, 29-Jul-2012.) $)
    com5l $p |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) ) $=
      wps wch wth wph wta wet wph wps wch wth wta wet wi com5.1 com4l com45 $.

    $( Commutation of antecedents.  Swap 1st and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.)  (Proof shortened by Wolf Lammen,
       29-Jul-2012.) $)
    com15 $p |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) ) $=
      wps wch wth wta wph wet wi wph wps wch wth wta wet com5.1 com5l com4r $.

    $( Commutation of antecedents.  Rotate left twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52l $p |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) ) $=
      wps wch wth wta wph wet wph wps wch wth wta wet com5.1 com5l com5l $.

    $( Commutation of antecedents.  Rotate right twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52r $p |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) ) $=
      wch wth wta wph wps wet wph wps wch wth wta wet com5.1 com52l com5l $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by Wolf Lammen,
       29-Jul-2012.) $)
    com5r $p |- ( ta -> ( ph -> ( ps -> ( ch -> ( th -> et ) ) ) ) ) $=
      wch wth wta wph wps wet wph wps wch wth wta wet com5.1 com52l com52l $.
  $}

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 9-May-2013.) $)
  jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    wps wph wps wi wch wps wph ax-1 imim1i $.

  ${
    pm2.86i.1 $e |- ( ( ph -> ps ) -> ( ph -> ch ) ) $.
    $( Inference based on ~ pm2.86 .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 3-Apr-2013.) $)
    pm2.86i $p |- ( ph -> ( ps -> ch ) ) $=
      wps wph wch wps wph wps wi wph wch wi wps wph ax-1 pm2.86i.1 syl com12 $.
  $}

  ${
    pm2.86d.1 $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
    $( Deduction based on ~ pm2.86 .  (Contributed by NM, 29-Jun-1995.)  (Proof
       shortened by Wolf Lammen, 3-Apr-2013.) $)
    pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wph wch wps wth wch wps wch wi wph wps wth wi wch wps ax-1 pm2.86d.1 syl5
      com23 $.
  $}

  $( Converse of axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
     (Contributed by NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen,
     3-Apr-2013.) $)
  pm2.86 $p |- ( ( ( ph -> ps )
       -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) ) $=
    wph wps wi wph wch wi wi wph wps wch wph wps wi wph wch wi wi id pm2.86d $.

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  This version of ~ loolin does not use ~ ax-3 , meaning
     that this theorem is intuitionistically valid.  (Contributed by O'Cat,
     12-Aug-2004.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  loolinALT $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    wph wps wi wps wph wi wi wps wph wph wps wps wph wi jarr pm2.43d $.

  $( An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz, due to Barbara Wozniakowska, _Reports
     on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by O'Cat,
     8-Aug-2004.) $)
  loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) )
      -> ( ( ps -> ph ) -> ( ps -> ch ) ) ) $=
    wph wps wi wph wch wi wi wps wph wch wph wps wph wch wi jarr a2d $.


