$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Universal_quantifier__define__exists__and__not_free_.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Rule scheme ax-gen (Generalization)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Rule of Generalization.  The postulated inference rule of pure predicate
       calculus.  See e.g.  Rule 2 of [Hamilton] p. 74.  This rule says that if
       something is unconditionally true, then it is true for all values of a
       variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ allt shows the
       special case ` A. x T. ` .  Theorem ~ spi shows we can go the other way
       also: in other words we can add or remove universal quantifiers from the
       beginning of any theorem as required.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph x  $.
	f0_ax-gen $f wff ph $.
	f1_ax-gen $f set x $.
	e0_ax-gen $e |- ph $.
	a_ax-gen $a |- A. x ph $.
$}

$(Generalization applied twice.  (Contributed by NM, 30-Apr-1998.) $)

${
	$v ph x y  $.
	f0_gen2 $f wff ph $.
	f1_gen2 $f set x $.
	f2_gen2 $f set y $.
	e0_gen2 $e |- ph $.
	p_gen2 $p |- A. x A. y ph $= e0_gen2 f0_gen2 f2_gen2 a_ax-gen f0_gen2 f2_gen2 a_wal f1_gen2 a_ax-gen $.
$}

$(Modus ponens combined with generalization.  (Contributed by NM,
       24-May-1994.) $)

${
	$v ph ps x  $.
	f0_mpg $f wff ph $.
	f1_mpg $f wff ps $.
	f2_mpg $f set x $.
	e0_mpg $e |- ( A. x ph -> ps ) $.
	e1_mpg $e |- ph $.
	p_mpg $p |- ps $= e1_mpg f0_mpg f2_mpg a_ax-gen e0_mpg f0_mpg f2_mpg a_wal f1_mpg a_ax-mp $.
$}

$(Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)

${
	$v ph ps x  $.
	f0_mpgbi $f wff ph $.
	f1_mpgbi $f wff ps $.
	f2_mpgbi $f set x $.
	e0_mpgbi $e |- ( A. x ph <-> ps ) $.
	e1_mpgbi $e |- ph $.
	p_mpgbi $p |- ps $= e1_mpgbi f0_mpgbi f2_mpgbi a_ax-gen e0_mpgbi f0_mpgbi f2_mpgbi a_wal f1_mpgbi p_mpbi $.
$}

$(Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)

${
	$v ph ps x  $.
	f0_mpgbir $f wff ph $.
	f1_mpgbir $f wff ps $.
	f2_mpgbir $f set x $.
	e0_mpgbir $e |- ( ph <-> A. x ps ) $.
	e1_mpgbir $e |- ps $.
	p_mpgbir $p |- ph $= e1_mpgbir f1_mpgbir f2_mpgbir a_ax-gen e0_mpgbir f0_mpgbir f1_mpgbir f2_mpgbir a_wal p_mpbir $.
$}

$(Deduce that ` x ` is not free in ` ph ` from the definition.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x  $.
	f0_nfi $f wff ph $.
	f1_nfi $f set x $.
	e0_nfi $e |- ( ph -> A. x ph ) $.
	p_nfi $p |- F/ x ph $= f0_nfi f1_nfi a_df-nf e0_nfi f0_nfi f1_nfi a_wnf f0_nfi f0_nfi f1_nfi a_wal a_wi f1_nfi p_mpgbir $.
$}

$(No variable is (effectively) free in a theorem.

       This and later "hypothesis-building" lemmas, with labels starting
       "hb...", allow us to construct proofs of formulas of the form
       ` |- ( ph -> A. x ph ) ` from smaller formulas of this form.  These are
       useful for constructing hypotheses that state " ` x ` is (effectively)
       not free in ` ph ` ."  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_hbth $f wff ph $.
	f1_hbth $f set x $.
	e0_hbth $e |- ph $.
	p_hbth $p |- ( ph -> A. x ph ) $= e0_hbth f0_hbth f1_hbth a_ax-gen f0_hbth f1_hbth a_wal f0_hbth p_a1i $.
$}

$(No variable is (effectively) free in a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v ph x  $.
	f0_nfth $f wff ph $.
	f1_nfth $f set x $.
	e0_nfth $e |- ph $.
	p_nfth $p |- F/ x ph $= e0_nfth f0_nfth f1_nfth p_hbth f0_nfth f1_nfth p_nfi $.
$}

$(The true constant has no free variables.  (This can also be proven in one
     step with ~ nfv , but this proof does not use ~ ax-17 .)  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)

${
	$v x  $.
	f0_nftru $f set x $.
	p_nftru $p |- F/ x T. $= p_tru a_wtru f0_nftru p_nfth $.
$}

$(Generalization rule for negated wff.  (Contributed by NM,
       18-May-1994.) $)

${
	$v ph x  $.
	f0_nex $f wff ph $.
	f1_nex $f set x $.
	e0_nex $e |- -. ph $.
	p_nex $p |- -. E. x ph $= f0_nex f1_nex p_alnex e0_nex f0_nex a_wn f0_nex f1_nex a_wex a_wn f1_nex p_mpgbi $.
$}

$(No variable is (effectively) free in a non-theorem.  (Contributed by
       Mario Carneiro, 6-Dec-2016.) $)

${
	$v ph x  $.
	f0_nfnth $f wff ph $.
	f1_nfnth $f set x $.
	e0_nfnth $e |- -. ph $.
	p_nfnth $p |- F/ x ph $= e0_nfnth f0_nfnth f0_nfnth f1_nfnth a_wal p_pm2.21i f0_nfnth f1_nfnth p_nfi $.
$}


