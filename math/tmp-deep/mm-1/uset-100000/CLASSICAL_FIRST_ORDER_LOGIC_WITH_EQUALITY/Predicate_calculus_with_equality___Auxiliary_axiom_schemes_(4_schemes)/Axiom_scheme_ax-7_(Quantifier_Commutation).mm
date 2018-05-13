$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-6_(Quantified_Negation).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Axiom scheme ax-7 (Quantifier Commutation)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  One of the 4 axioms of pure predicate calculus.  Axiom
     scheme C6' in [Megill] p. 448 (p. 16 of the preprint).  Also appears as
     Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax7w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_ax-7 $f wff ph $.
	f1_ax-7 $f set x $.
	f2_ax-7 $f set y $.
	a_ax-7 $a |- ( A. x A. y ph -> A. y A. x ph ) $.
$}

$(Swap quantifiers in an antecedent.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_a7s $f wff ph $.
	f1_a7s $f wff ps $.
	f2_a7s $f set x $.
	f3_a7s $f set y $.
	e0_a7s $e |- ( A. x A. y ph -> ps ) $.
	p_a7s $p |- ( A. y A. x ph -> ps ) $= f0_a7s f3_a7s f2_a7s a_ax-7 e0_a7s f0_a7s f2_a7s a_wal f3_a7s a_wal f0_a7s f3_a7s a_wal f2_a7s a_wal f1_a7s p_syl $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_hbal $f wff ph $.
	f1_hbal $f set x $.
	f2_hbal $f set y $.
	e0_hbal $e |- ( ph -> A. x ph ) $.
	p_hbal $p |- ( A. y ph -> A. x A. y ph ) $= e0_hbal f0_hbal f0_hbal f1_hbal a_wal f2_hbal p_alimi f0_hbal f2_hbal f1_hbal a_ax-7 f0_hbal f2_hbal a_wal f0_hbal f1_hbal a_wal f2_hbal a_wal f0_hbal f2_hbal a_wal f1_hbal a_wal p_syl $.
$}

$(Theorem 19.5 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_alcom $f wff ph $.
	f1_alcom $f set x $.
	f2_alcom $f set y $.
	p_alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $= f0_alcom f1_alcom f2_alcom a_ax-7 f0_alcom f2_alcom f1_alcom a_ax-7 f0_alcom f2_alcom a_wal f1_alcom a_wal f0_alcom f1_alcom a_wal f2_alcom a_wal p_impbii $.
$}

$(Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)

${
	$v ph x y z  $.
	f0_alrot3 $f wff ph $.
	f1_alrot3 $f set x $.
	f2_alrot3 $f set y $.
	f3_alrot3 $f set z $.
	p_alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $= f0_alrot3 f3_alrot3 a_wal f1_alrot3 f2_alrot3 p_alcom f0_alrot3 f1_alrot3 f3_alrot3 p_alcom f0_alrot3 f3_alrot3 a_wal f1_alrot3 a_wal f0_alrot3 f1_alrot3 a_wal f3_alrot3 a_wal f2_alrot3 p_albii f0_alrot3 f3_alrot3 a_wal f2_alrot3 a_wal f1_alrot3 a_wal f0_alrot3 f3_alrot3 a_wal f1_alrot3 a_wal f2_alrot3 a_wal f0_alrot3 f1_alrot3 a_wal f3_alrot3 a_wal f2_alrot3 a_wal p_bitri $.
$}

$(Rotate 4 universal quantifiers twice.  (Contributed by NM, 2-Feb-2005.)
     (Proof shortened by Fan Zheng, 6-Jun-2016.) $)

${
	$v ph x y z w  $.
	f0_alrot4 $f wff ph $.
	f1_alrot4 $f set x $.
	f2_alrot4 $f set y $.
	f3_alrot4 $f set z $.
	f4_alrot4 $f set w $.
	p_alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $= f0_alrot4 f2_alrot4 f3_alrot4 f4_alrot4 p_alrot3 f0_alrot4 f4_alrot4 a_wal f3_alrot4 a_wal f2_alrot4 a_wal f0_alrot4 f2_alrot4 a_wal f4_alrot4 a_wal f3_alrot4 a_wal f1_alrot4 p_albii f0_alrot4 f2_alrot4 a_wal f1_alrot4 f3_alrot4 f4_alrot4 p_alrot3 f0_alrot4 f4_alrot4 a_wal f3_alrot4 a_wal f2_alrot4 a_wal f1_alrot4 a_wal f0_alrot4 f2_alrot4 a_wal f4_alrot4 a_wal f3_alrot4 a_wal f1_alrot4 a_wal f0_alrot4 f2_alrot4 a_wal f1_alrot4 a_wal f4_alrot4 a_wal f3_alrot4 a_wal p_bitri $.
$}

$(Deduction form of bound-variable hypothesis builder ~ hbal .
       (Contributed by NM, 2-Jan-2002.) $)

${
	$v ph ps x y  $.
	f0_hbald $f wff ph $.
	f1_hbald $f wff ps $.
	f2_hbald $f set x $.
	f3_hbald $f set y $.
	e0_hbald $e |- ( ph -> A. y ph ) $.
	e1_hbald $e |- ( ph -> ( ps -> A. x ps ) ) $.
	p_hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $= e0_hbald e1_hbald f0_hbald f1_hbald f1_hbald f2_hbald a_wal f3_hbald p_alimdh f1_hbald f3_hbald f2_hbald a_ax-7 f0_hbald f1_hbald f3_hbald a_wal f1_hbald f2_hbald a_wal f3_hbald a_wal f1_hbald f3_hbald a_wal f2_hbald a_wal p_syl6 $.
$}


