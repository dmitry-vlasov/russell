$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Rule_scheme_ax-gen_(Generalization).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
         Axiom scheme ax-5 (Quantified Implication)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105.
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_ax-5 $f wff ph $.
	f1_ax-5 $f wff ps $.
	f2_ax-5 $f set x $.
	a_ax-5 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.
$}

$(Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by O'Cat, 30-Mar-2008.) $)

${
	$v ph ps x  $.
	f0_alim $f wff ph $.
	f1_alim $f wff ps $.
	f2_alim $f set x $.
	p_alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $= f0_alim f1_alim f2_alim a_ax-5 $.
$}

$(Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_alimi $f wff ph $.
	f1_alimi $f wff ps $.
	f2_alimi $f set x $.
	e0_alimi $e |- ( ph -> ps ) $.
	p_alimi $p |- ( A. x ph -> A. x ps ) $= f0_alimi f1_alimi f2_alimi a_ax-5 e0_alimi f0_alimi f1_alimi a_wi f0_alimi f2_alimi a_wal f1_alimi f2_alimi a_wal a_wi f2_alimi p_mpg $.
$}

$(Inference doubly quantifying both antecedent and consequent.
       (Contributed by NM, 3-Feb-2005.) $)

${
	$v ph ps x y  $.
	f0_2alimi $f wff ph $.
	f1_2alimi $f wff ps $.
	f2_2alimi $f set x $.
	f3_2alimi $f set y $.
	e0_2alimi $e |- ( ph -> ps ) $.
	p_2alimi $p |- ( A. x A. y ph -> A. x A. y ps ) $= e0_2alimi f0_2alimi f1_2alimi f3_2alimi p_alimi f0_2alimi f3_2alimi a_wal f1_2alimi f3_2alimi a_wal f2_2alimi p_alimi $.
$}

$(Inference quantifying antecedent, nested antecedent, and consequent.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch x  $.
	f0_al2imi $f wff ph $.
	f1_al2imi $f wff ps $.
	f2_al2imi $f wff ch $.
	f3_al2imi $f set x $.
	e0_al2imi $e |- ( ph -> ( ps -> ch ) ) $.
	p_al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $= e0_al2imi f0_al2imi f1_al2imi f2_al2imi a_wi f3_al2imi p_alimi f1_al2imi f2_al2imi f3_al2imi p_alim f0_al2imi f3_al2imi a_wal f1_al2imi f2_al2imi a_wi f3_al2imi a_wal f1_al2imi f3_al2imi a_wal f2_al2imi f3_al2imi a_wal a_wi p_syl $.
$}

$(Variant of ~ al2imi with conjunctive antecedent.  (Contributed by Andrew
       Salmon, 8-Jun-2011.) $)

${
	$v ph ps ch x  $.
	f0_alanimi $f wff ph $.
	f1_alanimi $f wff ps $.
	f2_alanimi $f wff ch $.
	f3_alanimi $f set x $.
	e0_alanimi $e |- ( ( ph /\ ps ) -> ch ) $.
	p_alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $= e0_alanimi f0_alanimi f1_alanimi f2_alanimi p_ex f0_alanimi f1_alanimi f2_alanimi f3_alanimi p_al2imi f0_alanimi f3_alanimi a_wal f1_alanimi f3_alanimi a_wal f2_alanimi f3_alanimi a_wal p_imp $.
$}

$(Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM,
       4-Jan-2002.) $)

${
	$v ph ps ch x  $.
	f0_alimdh $f wff ph $.
	f1_alimdh $f wff ps $.
	f2_alimdh $f wff ch $.
	f3_alimdh $f set x $.
	e0_alimdh $e |- ( ph -> A. x ph ) $.
	e1_alimdh $e |- ( ph -> ( ps -> ch ) ) $.
	p_alimdh $p |- ( ph -> ( A. x ps -> A. x ch ) ) $= e0_alimdh e1_alimdh f0_alimdh f1_alimdh f2_alimdh f3_alimdh p_al2imi f0_alimdh f0_alimdh f3_alimdh a_wal f1_alimdh f3_alimdh a_wal f2_alimdh f3_alimdh a_wal a_wi p_syl $.
$}

$(Theorem 19.15 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_albi $f wff ph $.
	f1_albi $f wff ps $.
	f2_albi $f set x $.
	p_albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $= f0_albi f1_albi p_bi1 f0_albi f1_albi a_wb f0_albi f1_albi f2_albi p_al2imi f0_albi f1_albi p_bi2 f0_albi f1_albi a_wb f1_albi f0_albi f2_albi p_al2imi f0_albi f1_albi a_wb f2_albi a_wal f0_albi f2_albi a_wal f1_albi f2_albi a_wal p_impbid $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_alrimih $f wff ph $.
	f1_alrimih $f wff ps $.
	f2_alrimih $f set x $.
	e0_alrimih $e |- ( ph -> A. x ph ) $.
	e1_alrimih $e |- ( ph -> ps ) $.
	p_alrimih $p |- ( ph -> A. x ps ) $= e0_alrimih e1_alrimih f0_alrimih f1_alrimih f2_alrimih p_alimi f0_alrimih f0_alrimih f2_alrimih a_wal f1_alrimih f2_alrimih a_wal p_syl $.
$}

$(Inference adding universal quantifier to both sides of an equivalence.
       (Contributed by NM, 7-Aug-1994.) $)

${
	$v ph ps x  $.
	f0_albii $f wff ph $.
	f1_albii $f wff ps $.
	f2_albii $f set x $.
	e0_albii $e |- ( ph <-> ps ) $.
	p_albii $p |- ( A. x ph <-> A. x ps ) $= f0_albii f1_albii f2_albii p_albi e0_albii f0_albii f1_albii a_wb f0_albii f2_albii a_wal f1_albii f2_albii a_wal a_wb f2_albii p_mpg $.
$}

$(Theorem albii is the congruence law for universal quantification. $)

$($j congruence 'albii'; $)

$(Inference adding two universal quantifiers to both sides of an
       equivalence.  (Contributed by NM, 9-Mar-1997.) $)

${
	$v ph ps x y  $.
	f0_2albii $f wff ph $.
	f1_2albii $f wff ps $.
	f2_2albii $f set x $.
	f3_2albii $f set y $.
	e0_2albii $e |- ( ph <-> ps ) $.
	p_2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $= e0_2albii f0_2albii f1_2albii f3_2albii p_albii f0_2albii f3_2albii a_wal f1_2albii f3_2albii a_wal f2_2albii p_albii $.
$}

$(A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfreq for equality version.  (Contributed by
       Jonathan Ben-Naim, 3-Jun-2011.) $)

${
	$v ph ps x  $.
	f0_hbxfrbi $f wff ph $.
	f1_hbxfrbi $f wff ps $.
	f2_hbxfrbi $f set x $.
	e0_hbxfrbi $e |- ( ph <-> ps ) $.
	e1_hbxfrbi $e |- ( ps -> A. x ps ) $.
	p_hbxfrbi $p |- ( ph -> A. x ph ) $= e1_hbxfrbi e0_hbxfrbi e0_hbxfrbi f0_hbxfrbi f1_hbxfrbi f2_hbxfrbi p_albii f1_hbxfrbi f1_hbxfrbi f2_hbxfrbi a_wal f0_hbxfrbi f0_hbxfrbi f2_hbxfrbi a_wal p_3imtr4i $.
$}

$(Equality theorem for not-free.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v ph ps x  $.
	f0_nfbii $f wff ph $.
	f1_nfbii $f wff ps $.
	f2_nfbii $f set x $.
	e0_nfbii $e |- ( ph <-> ps ) $.
	p_nfbii $p |- ( F/ x ph <-> F/ x ps ) $= e0_nfbii e0_nfbii f0_nfbii f1_nfbii f2_nfbii p_albii f0_nfbii f1_nfbii f0_nfbii f2_nfbii a_wal f1_nfbii f2_nfbii a_wal p_imbi12i f0_nfbii f0_nfbii f2_nfbii a_wal a_wi f1_nfbii f1_nfbii f2_nfbii a_wal a_wi f2_nfbii p_albii f0_nfbii f2_nfbii a_df-nf f1_nfbii f2_nfbii a_df-nf f0_nfbii f0_nfbii f2_nfbii a_wal a_wi f2_nfbii a_wal f1_nfbii f1_nfbii f2_nfbii a_wal a_wi f2_nfbii a_wal f0_nfbii f2_nfbii a_wnf f1_nfbii f2_nfbii a_wnf p_3bitr4i $.
$}

$(A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x  $.
	f0_nfxfr $f wff ph $.
	f1_nfxfr $f wff ps $.
	f2_nfxfr $f set x $.
	e0_nfxfr $e |- ( ph <-> ps ) $.
	e1_nfxfr $e |- F/ x ps $.
	p_nfxfr $p |- F/ x ph $= e1_nfxfr e0_nfxfr f0_nfxfr f1_nfxfr f2_nfxfr p_nfbii f0_nfxfr f2_nfxfr a_wnf f1_nfxfr f2_nfxfr a_wnf p_mpbir $.
$}

$(A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_nfxfrd $f wff ph $.
	f1_nfxfrd $f wff ps $.
	f2_nfxfrd $f wff ch $.
	f3_nfxfrd $f set x $.
	e0_nfxfrd $e |- ( ph <-> ps ) $.
	e1_nfxfrd $e |- ( ch -> F/ x ps ) $.
	p_nfxfrd $p |- ( ch -> F/ x ph ) $= e1_nfxfrd e0_nfxfrd f0_nfxfrd f1_nfxfrd f3_nfxfrd p_nfbii f2_nfxfrd f1_nfxfrd f3_nfxfrd a_wnf f0_nfxfrd f3_nfxfrd a_wnf p_sylibr $.
$}

$(Theorem 19.6 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_alex $f wff ph $.
	f1_alex $f set x $.
	p_alex $p |- ( A. x ph <-> -. E. x -. ph ) $= f0_alex p_notnot f0_alex f0_alex a_wn a_wn f1_alex p_albii f0_alex a_wn f1_alex p_alnex f0_alex f1_alex a_wal f0_alex a_wn a_wn f1_alex a_wal f0_alex a_wn f1_alex a_wex a_wn p_bitri $.
$}

$(Part of theorem *11.5 in [WhiteheadRussell] p. 164.  (Contributed by
     Andrew Salmon, 24-May-2011.) $)

${
	$v ph x y  $.
	f0_2nalexn $f wff ph $.
	f1_2nalexn $f set x $.
	f2_2nalexn $f set y $.
	p_2nalexn $p |- ( -. A. x A. y ph <-> E. x E. y -. ph ) $= f0_2nalexn a_wn f2_2nalexn a_wex f1_2nalexn a_df-ex f0_2nalexn f2_2nalexn p_alex f0_2nalexn f2_2nalexn a_wal f0_2nalexn a_wn f2_2nalexn a_wex a_wn f1_2nalexn p_albii f0_2nalexn a_wn f2_2nalexn a_wex f1_2nalexn a_wex f0_2nalexn a_wn f2_2nalexn a_wex a_wn f1_2nalexn a_wal f0_2nalexn f2_2nalexn a_wal f1_2nalexn a_wal p_xchbinxr f0_2nalexn a_wn f2_2nalexn a_wex f1_2nalexn a_wex f0_2nalexn f2_2nalexn a_wal f1_2nalexn a_wal a_wn p_bicomi $.
$}

$(Theorem 19.14 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_exnal $f wff ph $.
	f1_exnal $f set x $.
	p_exnal $p |- ( E. x -. ph <-> -. A. x ph ) $= f0_exnal f1_exnal p_alex f0_exnal f1_exnal a_wal f0_exnal a_wn f1_exnal a_wex p_con2bii $.
$}

$(Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 4-Jul-2014.) $)

${
	$v ph ps x  $.
	f0_exim $f wff ph $.
	f1_exim $f wff ps $.
	f2_exim $f set x $.
	p_exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $= f0_exim f1_exim p_con3 f0_exim f1_exim a_wi f1_exim a_wn f0_exim a_wn f2_exim p_al2imi f1_exim f2_exim p_alnex f0_exim f2_exim p_alnex f0_exim f1_exim a_wi f2_exim a_wal f1_exim a_wn f2_exim a_wal f0_exim a_wn f2_exim a_wal f1_exim f2_exim a_wex a_wn f0_exim f2_exim a_wex a_wn p_3imtr3g f0_exim f1_exim a_wi f2_exim a_wal f1_exim f2_exim a_wex f0_exim f2_exim a_wex p_con4d $.
$}

$(Inference adding existential quantifier to antecedent and consequent.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_eximi $f wff ph $.
	f1_eximi $f wff ps $.
	f2_eximi $f set x $.
	e0_eximi $e |- ( ph -> ps ) $.
	p_eximi $p |- ( E. x ph -> E. x ps ) $= f0_eximi f1_eximi f2_eximi p_exim e0_eximi f0_eximi f1_eximi a_wi f0_eximi f2_eximi a_wex f1_eximi f2_eximi a_wex a_wi f2_eximi p_mpg $.
$}

$(Inference adding two existential quantifiers to antecedent and
       consequent.  (Contributed by NM, 3-Feb-2005.) $)

${
	$v ph ps x y  $.
	f0_2eximi $f wff ph $.
	f1_2eximi $f wff ps $.
	f2_2eximi $f set x $.
	f3_2eximi $f set y $.
	e0_2eximi $e |- ( ph -> ps ) $.
	p_2eximi $p |- ( E. x E. y ph -> E. x E. y ps ) $= e0_2eximi f0_2eximi f1_2eximi f3_2eximi p_eximi f0_2eximi f3_2eximi a_wex f1_2eximi f3_2eximi a_wex f2_2eximi p_eximi $.
$}

$(A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 19-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_alinexa $f wff ph $.
	f1_alinexa $f wff ps $.
	f2_alinexa $f set x $.
	p_alinexa $p |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) ) $= f0_alinexa f1_alinexa p_imnan f0_alinexa f1_alinexa a_wn a_wi f0_alinexa f1_alinexa a_wa a_wn f2_alinexa p_albii f0_alinexa f1_alinexa a_wa f2_alinexa p_alnex f0_alinexa f1_alinexa a_wn a_wi f2_alinexa a_wal f0_alinexa f1_alinexa a_wa a_wn f2_alinexa a_wal f0_alinexa f1_alinexa a_wa f2_alinexa a_wex a_wn p_bitri $.
$}

$(A relationship between two quantifiers and negation.  (Contributed by NM,
     18-Aug-1993.) $)

${
	$v ph x y  $.
	f0_alexn $f wff ph $.
	f1_alexn $f set x $.
	f2_alexn $f set y $.
	p_alexn $p |- ( A. x E. y -. ph <-> -. E. x A. y ph ) $= f0_alexn f2_alexn p_exnal f0_alexn a_wn f2_alexn a_wex f0_alexn f2_alexn a_wal a_wn f1_alexn p_albii f0_alexn f2_alexn a_wal f1_alexn p_alnex f0_alexn a_wn f2_alexn a_wex f1_alexn a_wal f0_alexn f2_alexn a_wal a_wn f1_alexn a_wal f0_alexn f2_alexn a_wal f1_alexn a_wex a_wn p_bitri $.
$}

$(Theorem *11.51 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.)  (Proof shortened by Wolf Lammen, 25-Sep-2014.) $)

${
	$v ph x y  $.
	f0_2exnexn $f wff ph $.
	f1_2exnexn $f set x $.
	f2_2exnexn $f set y $.
	p_2exnexn $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $= f0_2exnexn f1_2exnexn f2_2exnexn p_alexn f0_2exnexn a_wn f2_2exnexn a_wex f1_2exnexn a_wal f0_2exnexn f2_2exnexn a_wal f1_2exnexn a_wex p_con2bii $.
$}

$(Theorem 19.18 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_exbi $f wff ph $.
	f1_exbi $f wff ps $.
	f2_exbi $f set x $.
	p_exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $= f0_exbi f1_exbi p_bi1 f0_exbi f1_exbi a_wb f0_exbi f1_exbi a_wi f2_exbi p_alimi f0_exbi f1_exbi f2_exbi p_exim f0_exbi f1_exbi a_wb f2_exbi a_wal f0_exbi f1_exbi a_wi f2_exbi a_wal f0_exbi f2_exbi a_wex f1_exbi f2_exbi a_wex a_wi p_syl f0_exbi f1_exbi p_bi2 f0_exbi f1_exbi a_wb f1_exbi f0_exbi a_wi f2_exbi p_alimi f1_exbi f0_exbi f2_exbi p_exim f0_exbi f1_exbi a_wb f2_exbi a_wal f1_exbi f0_exbi a_wi f2_exbi a_wal f1_exbi f2_exbi a_wex f0_exbi f2_exbi a_wex a_wi p_syl f0_exbi f1_exbi a_wb f2_exbi a_wal f0_exbi f2_exbi a_wex f1_exbi f2_exbi a_wex p_impbid $.
$}

$(Inference adding existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 24-May-1994.) $)

${
	$v ph ps x  $.
	f0_exbii $f wff ph $.
	f1_exbii $f wff ps $.
	f2_exbii $f set x $.
	e0_exbii $e |- ( ph <-> ps ) $.
	p_exbii $p |- ( E. x ph <-> E. x ps ) $= f0_exbii f1_exbii f2_exbii p_exbi e0_exbii f0_exbii f1_exbii a_wb f0_exbii f2_exbii a_wex f1_exbii f2_exbii a_wex a_wb f2_exbii p_mpg $.
$}

$(Inference adding two existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 16-Mar-1995.) $)

${
	$v ph ps x y  $.
	f0_2exbii $f wff ph $.
	f1_2exbii $f wff ps $.
	f2_2exbii $f set x $.
	f3_2exbii $f set y $.
	e0_2exbii $e |- ( ph <-> ps ) $.
	p_2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $= e0_2exbii f0_2exbii f1_2exbii f3_2exbii p_exbii f0_2exbii f3_2exbii a_wex f1_2exbii f3_2exbii a_wex f2_2exbii p_exbii $.
$}

$(Inference adding 3 existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 2-May-1995.) $)

${
	$v ph ps x y z  $.
	f0_3exbii $f wff ph $.
	f1_3exbii $f wff ps $.
	f2_3exbii $f set x $.
	f3_3exbii $f set y $.
	f4_3exbii $f set z $.
	e0_3exbii $e |- ( ph <-> ps ) $.
	p_3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $= e0_3exbii f0_3exbii f1_3exbii f4_3exbii p_exbii f0_3exbii f4_3exbii a_wex f1_3exbii f4_3exbii a_wex f2_3exbii f3_3exbii p_2exbii $.
$}

$(A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 25-Mar-1996.)  (Proof shortened by Wolf Lammen, 4-Sep-2014.) $)

${
	$v ph ps x  $.
	f0_exanali $f wff ph $.
	f1_exanali $f wff ps $.
	f2_exanali $f set x $.
	p_exanali $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $= f0_exanali f1_exanali p_annim f0_exanali f1_exanali a_wn a_wa f0_exanali f1_exanali a_wi a_wn f2_exanali p_exbii f0_exanali f1_exanali a_wi f2_exanali p_exnal f0_exanali f1_exanali a_wn a_wa f2_exanali a_wex f0_exanali f1_exanali a_wi a_wn f2_exanali a_wex f0_exanali f1_exanali a_wi f2_exanali a_wal a_wn p_bitri $.
$}

$(Commutation of conjunction inside an existential quantifier.  (Contributed
     by NM, 18-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_exancom $f wff ph $.
	f1_exancom $f wff ps $.
	f2_exancom $f set x $.
	p_exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $= f0_exancom f1_exancom p_ancom f0_exancom f1_exancom a_wa f1_exancom f0_exancom a_wa f2_exancom p_exbii $.
$}

$(Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v ph ps ch x  $.
	f0_alrimdh $f wff ph $.
	f1_alrimdh $f wff ps $.
	f2_alrimdh $f wff ch $.
	f3_alrimdh $f set x $.
	e0_alrimdh $e |- ( ph -> A. x ph ) $.
	e1_alrimdh $e |- ( ps -> A. x ps ) $.
	e2_alrimdh $e |- ( ph -> ( ps -> ch ) ) $.
	p_alrimdh $p |- ( ph -> ( ps -> A. x ch ) ) $= e1_alrimdh e0_alrimdh e2_alrimdh f0_alrimdh f1_alrimdh f2_alrimdh f3_alrimdh p_alimdh f1_alrimdh f1_alrimdh f3_alrimdh a_wal f0_alrimdh f2_alrimdh f3_alrimdh a_wal p_syl5 $.
$}

$(Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       20-May-1996.) $)

${
	$v ph ps ch x  $.
	f0_eximdh $f wff ph $.
	f1_eximdh $f wff ps $.
	f2_eximdh $f wff ch $.
	f3_eximdh $f set x $.
	e0_eximdh $e |- ( ph -> A. x ph ) $.
	e1_eximdh $e |- ( ph -> ( ps -> ch ) ) $.
	p_eximdh $p |- ( ph -> ( E. x ps -> E. x ch ) ) $= e0_eximdh e1_eximdh f0_eximdh f1_eximdh f2_eximdh a_wi f3_eximdh p_alrimih f1_eximdh f2_eximdh f3_eximdh p_exim f0_eximdh f1_eximdh f2_eximdh a_wi f3_eximdh a_wal f1_eximdh f3_eximdh a_wex f2_eximdh f3_eximdh a_wex a_wi p_syl $.
$}

$(Deduction for generalization rule for negated wff.  (Contributed by NM,
       2-Jan-2002.) $)

${
	$v ph ps x  $.
	f0_nexdh $f wff ph $.
	f1_nexdh $f wff ps $.
	f2_nexdh $f set x $.
	e0_nexdh $e |- ( ph -> A. x ph ) $.
	e1_nexdh $e |- ( ph -> -. ps ) $.
	p_nexdh $p |- ( ph -> -. E. x ps ) $= e0_nexdh e1_nexdh f0_nexdh f1_nexdh a_wn f2_nexdh p_alrimih f1_nexdh f2_nexdh p_alnex f0_nexdh f1_nexdh a_wn f2_nexdh a_wal f1_nexdh f2_nexdh a_wex a_wn p_sylib $.
$}

$(Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch x  $.
	f0_albidh $f wff ph $.
	f1_albidh $f wff ps $.
	f2_albidh $f wff ch $.
	f3_albidh $f set x $.
	e0_albidh $e |- ( ph -> A. x ph ) $.
	e1_albidh $e |- ( ph -> ( ps <-> ch ) ) $.
	p_albidh $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $= e0_albidh e1_albidh f0_albidh f1_albidh f2_albidh a_wb f3_albidh p_alrimih f1_albidh f2_albidh f3_albidh p_albi f0_albidh f1_albidh f2_albidh a_wb f3_albidh a_wal f1_albidh f3_albidh a_wal f2_albidh f3_albidh a_wal a_wb p_syl $.
$}

$(Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps ch x  $.
	f0_exbidh $f wff ph $.
	f1_exbidh $f wff ps $.
	f2_exbidh $f wff ch $.
	f3_exbidh $f set x $.
	e0_exbidh $e |- ( ph -> A. x ph ) $.
	e1_exbidh $e |- ( ph -> ( ps <-> ch ) ) $.
	p_exbidh $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $= e0_exbidh e1_exbidh f0_exbidh f1_exbidh f2_exbidh a_wb f3_exbidh p_alrimih f1_exbidh f2_exbidh f3_exbidh p_exbi f0_exbidh f1_exbidh f2_exbidh a_wb f3_exbidh a_wal f1_exbidh f3_exbidh a_wex f2_exbidh f3_exbidh a_wex a_wb p_syl $.
$}

$(Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)

${
	$v ph ps x  $.
	f0_exsimpl $f wff ph $.
	f1_exsimpl $f wff ps $.
	f2_exsimpl $f set x $.
	p_exsimpl $p |- ( E. x ( ph /\ ps ) -> E. x ph ) $= f0_exsimpl f1_exsimpl p_simpl f0_exsimpl f1_exsimpl a_wa f0_exsimpl f2_exsimpl p_eximi $.
$}

$(Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 147.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 4-Jul-2014.) $)

${
	$v ph ps x  $.
	f0_19.26 $f wff ph $.
	f1_19.26 $f wff ps $.
	f2_19.26 $f set x $.
	p_19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $= f0_19.26 f1_19.26 p_simpl f0_19.26 f1_19.26 a_wa f0_19.26 f2_19.26 p_alimi f0_19.26 f1_19.26 p_simpr f0_19.26 f1_19.26 a_wa f1_19.26 f2_19.26 p_alimi f0_19.26 f1_19.26 a_wa f2_19.26 a_wal f0_19.26 f2_19.26 a_wal f1_19.26 f2_19.26 a_wal p_jca f0_19.26 f1_19.26 a_wa p_id f0_19.26 f1_19.26 f0_19.26 f1_19.26 a_wa f2_19.26 p_alanimi f0_19.26 f1_19.26 a_wa f2_19.26 a_wal f0_19.26 f2_19.26 a_wal f1_19.26 f2_19.26 a_wal a_wa p_impbii $.
$}

$(Theorem 19.26 of [Margaris] p. 90 with two quantifiers.  (Contributed by
     NM, 3-Feb-2005.) $)

${
	$v ph ps x y  $.
	f0_19.26-2 $f wff ph $.
	f1_19.26-2 $f wff ps $.
	f2_19.26-2 $f set x $.
	f3_19.26-2 $f set y $.
	p_19.26-2 $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x A. y ph /\ A. x A. y ps ) ) $= f0_19.26-2 f1_19.26-2 f3_19.26-2 p_19.26 f0_19.26-2 f1_19.26-2 a_wa f3_19.26-2 a_wal f0_19.26-2 f3_19.26-2 a_wal f1_19.26-2 f3_19.26-2 a_wal a_wa f2_19.26-2 p_albii f0_19.26-2 f3_19.26-2 a_wal f1_19.26-2 f3_19.26-2 a_wal f2_19.26-2 p_19.26 f0_19.26-2 f1_19.26-2 a_wa f3_19.26-2 a_wal f2_19.26-2 a_wal f0_19.26-2 f3_19.26-2 a_wal f1_19.26-2 f3_19.26-2 a_wal a_wa f2_19.26-2 a_wal f0_19.26-2 f3_19.26-2 a_wal f2_19.26-2 a_wal f1_19.26-2 f3_19.26-2 a_wal f2_19.26-2 a_wal a_wa p_bitri $.
$}

$(Theorem 19.26 of [Margaris] p. 90 with triple conjunction.  (Contributed
     by NM, 13-Sep-2011.) $)

${
	$v ph ps ch x  $.
	f0_19.26-3an $f wff ph $.
	f1_19.26-3an $f wff ps $.
	f2_19.26-3an $f wff ch $.
	f3_19.26-3an $f set x $.
	p_19.26-3an $p |- ( A. x ( ph /\ ps /\ ch ) <-> ( A. x ph /\ A. x ps /\ A. x ch ) ) $= f0_19.26-3an f1_19.26-3an a_wa f2_19.26-3an f3_19.26-3an p_19.26 f0_19.26-3an f1_19.26-3an f3_19.26-3an p_19.26 f0_19.26-3an f1_19.26-3an a_wa f3_19.26-3an a_wal f0_19.26-3an f3_19.26-3an a_wal f1_19.26-3an f3_19.26-3an a_wal a_wa f2_19.26-3an f3_19.26-3an a_wal p_anbi1i f0_19.26-3an f1_19.26-3an a_wa f2_19.26-3an a_wa f3_19.26-3an a_wal f0_19.26-3an f1_19.26-3an a_wa f3_19.26-3an a_wal f2_19.26-3an f3_19.26-3an a_wal a_wa f0_19.26-3an f3_19.26-3an a_wal f1_19.26-3an f3_19.26-3an a_wal a_wa f2_19.26-3an f3_19.26-3an a_wal a_wa p_bitri f0_19.26-3an f1_19.26-3an f2_19.26-3an a_df-3an f0_19.26-3an f1_19.26-3an f2_19.26-3an a_w3a f0_19.26-3an f1_19.26-3an a_wa f2_19.26-3an a_wa f3_19.26-3an p_albii f0_19.26-3an f3_19.26-3an a_wal f1_19.26-3an f3_19.26-3an a_wal f2_19.26-3an f3_19.26-3an a_wal a_df-3an f0_19.26-3an f1_19.26-3an a_wa f2_19.26-3an a_wa f3_19.26-3an a_wal f0_19.26-3an f3_19.26-3an a_wal f1_19.26-3an f3_19.26-3an a_wal a_wa f2_19.26-3an f3_19.26-3an a_wal a_wa f0_19.26-3an f1_19.26-3an f2_19.26-3an a_w3a f3_19.26-3an a_wal f0_19.26-3an f3_19.26-3an a_wal f1_19.26-3an f3_19.26-3an a_wal f2_19.26-3an f3_19.26-3an a_wal a_w3a p_3bitr4i $.
$}

$(Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v ph ps x  $.
	f0_19.29 $f wff ph $.
	f1_19.29 $f wff ps $.
	f2_19.29 $f set x $.
	p_19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $= f0_19.29 f1_19.29 p_pm3.2 f0_19.29 f1_19.29 f0_19.29 f1_19.29 a_wa a_wi f2_19.29 p_alimi f1_19.29 f0_19.29 f1_19.29 a_wa f2_19.29 p_exim f0_19.29 f2_19.29 a_wal f1_19.29 f0_19.29 f1_19.29 a_wa a_wi f2_19.29 a_wal f1_19.29 f2_19.29 a_wex f0_19.29 f1_19.29 a_wa f2_19.29 a_wex a_wi p_syl f0_19.29 f2_19.29 a_wal f1_19.29 f2_19.29 a_wex f0_19.29 f1_19.29 a_wa f2_19.29 a_wex p_imp $.
$}

$(Variation of Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM,
     18-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.29r $f wff ph $.
	f1_19.29r $f wff ps $.
	f2_19.29r $f set x $.
	p_19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $= f1_19.29r f0_19.29r f2_19.29r p_19.29 f1_19.29r f2_19.29r a_wal f0_19.29r f2_19.29r a_wex f1_19.29r f0_19.29r a_wa f2_19.29r a_wex p_ancoms f0_19.29r f1_19.29r f2_19.29r p_exancom f0_19.29r f2_19.29r a_wex f1_19.29r f2_19.29r a_wal a_wa f1_19.29r f0_19.29r a_wa f2_19.29r a_wex f0_19.29r f1_19.29r a_wa f2_19.29r a_wex p_sylibr $.
$}

$(Variation of Theorem 19.29 of [Margaris] p. 90 with double
     quantification.  (Contributed by NM, 3-Feb-2005.) $)

${
	$v ph ps x y  $.
	f0_19.29r2 $f wff ph $.
	f1_19.29r2 $f wff ps $.
	f2_19.29r2 $f set x $.
	f3_19.29r2 $f set y $.
	p_19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) -> E. x E. y ( ph /\ ps ) ) $= f0_19.29r2 f3_19.29r2 a_wex f1_19.29r2 f3_19.29r2 a_wal f2_19.29r2 p_19.29r f0_19.29r2 f1_19.29r2 f3_19.29r2 p_19.29r f0_19.29r2 f3_19.29r2 a_wex f1_19.29r2 f3_19.29r2 a_wal a_wa f0_19.29r2 f1_19.29r2 a_wa f3_19.29r2 a_wex f2_19.29r2 p_eximi f0_19.29r2 f3_19.29r2 a_wex f2_19.29r2 a_wex f1_19.29r2 f3_19.29r2 a_wal f2_19.29r2 a_wal a_wa f0_19.29r2 f3_19.29r2 a_wex f1_19.29r2 f3_19.29r2 a_wal a_wa f2_19.29r2 a_wex f0_19.29r2 f1_19.29r2 a_wa f3_19.29r2 a_wex f2_19.29r2 a_wex p_syl $.
$}

$(Variation of Theorem 19.29 of [Margaris] p. 90 with mixed quantification.
     (Contributed by NM, 11-Feb-2005.) $)

${
	$v ph ps x y  $.
	f0_19.29x $f wff ph $.
	f1_19.29x $f wff ps $.
	f2_19.29x $f set x $.
	f3_19.29x $f set y $.
	p_19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) -> E. x E. y ( ph /\ ps ) ) $= f0_19.29x f3_19.29x a_wal f1_19.29x f3_19.29x a_wex f2_19.29x p_19.29r f0_19.29x f1_19.29x f3_19.29x p_19.29 f0_19.29x f3_19.29x a_wal f1_19.29x f3_19.29x a_wex a_wa f0_19.29x f1_19.29x a_wa f3_19.29x a_wex f2_19.29x p_eximi f0_19.29x f3_19.29x a_wal f2_19.29x a_wex f1_19.29x f3_19.29x a_wex f2_19.29x a_wal a_wa f0_19.29x f3_19.29x a_wal f1_19.29x f3_19.29x a_wex a_wa f2_19.29x a_wex f0_19.29x f1_19.29x a_wa f3_19.29x a_wex f2_19.29x a_wex p_syl $.
$}

$(Theorem 19.35 of [Margaris] p. 90.  This theorem is useful for moving an
     implication (in the form of the right-hand side) into the scope of a
     single existential quantifier.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 27-Jun-2014.) $)

${
	$v ph ps x  $.
	f0_19.35 $f wff ph $.
	f1_19.35 $f wff ps $.
	f2_19.35 $f set x $.
	p_19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $= f0_19.35 f1_19.35 a_wn f2_19.35 p_19.26 f0_19.35 f1_19.35 p_annim f0_19.35 f1_19.35 a_wn a_wa f0_19.35 f1_19.35 a_wi a_wn f2_19.35 p_albii f1_19.35 f2_19.35 p_alnex f1_19.35 a_wn f2_19.35 a_wal f1_19.35 f2_19.35 a_wex a_wn f0_19.35 f2_19.35 a_wal p_anbi2i f0_19.35 f1_19.35 a_wn a_wa f2_19.35 a_wal f0_19.35 f2_19.35 a_wal f1_19.35 a_wn f2_19.35 a_wal a_wa f0_19.35 f1_19.35 a_wi a_wn f2_19.35 a_wal f0_19.35 f2_19.35 a_wal f1_19.35 f2_19.35 a_wex a_wn a_wa p_3bitr3i f0_19.35 f1_19.35 a_wi f2_19.35 p_alnex f0_19.35 f2_19.35 a_wal f1_19.35 f2_19.35 a_wex p_annim f0_19.35 f1_19.35 a_wi a_wn f2_19.35 a_wal f0_19.35 f2_19.35 a_wal f1_19.35 f2_19.35 a_wex a_wn a_wa f0_19.35 f1_19.35 a_wi f2_19.35 a_wex a_wn f0_19.35 f2_19.35 a_wal f1_19.35 f2_19.35 a_wex a_wi a_wn p_3bitr3i f0_19.35 f1_19.35 a_wi f2_19.35 a_wex f0_19.35 f2_19.35 a_wal f1_19.35 f2_19.35 a_wex a_wi p_con4bii $.
$}

$(Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.35i $f wff ph $.
	f1_19.35i $f wff ps $.
	f2_19.35i $f set x $.
	e0_19.35i $e |- E. x ( ph -> ps ) $.
	p_19.35i $p |- ( A. x ph -> E. x ps ) $= e0_19.35i f0_19.35i f1_19.35i f2_19.35i p_19.35 f0_19.35i f1_19.35i a_wi f2_19.35i a_wex f0_19.35i f2_19.35i a_wal f1_19.35i f2_19.35i a_wex a_wi p_mpbi $.
$}

$(Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.35ri $f wff ph $.
	f1_19.35ri $f wff ps $.
	f2_19.35ri $f set x $.
	e0_19.35ri $e |- ( A. x ph -> E. x ps ) $.
	p_19.35ri $p |- E. x ( ph -> ps ) $= e0_19.35ri f0_19.35ri f1_19.35ri f2_19.35ri p_19.35 f0_19.35ri f1_19.35ri a_wi f2_19.35ri a_wex f0_19.35ri f2_19.35ri a_wal f1_19.35ri f2_19.35ri a_wex a_wi p_mpbir $.
$}

$(Theorem 19.25 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_19.25 $f wff ph $.
	f1_19.25 $f wff ps $.
	f2_19.25 $f set x $.
	f3_19.25 $f set y $.
	p_19.25 $p |- ( A. y E. x ( ph -> ps ) -> ( E. y A. x ph -> E. y E. x ps ) ) $= f0_19.25 f1_19.25 f2_19.25 p_19.35 f0_19.25 f1_19.25 a_wi f2_19.25 a_wex f0_19.25 f2_19.25 a_wal f1_19.25 f2_19.25 a_wex a_wi p_biimpi f0_19.25 f1_19.25 a_wi f2_19.25 a_wex f0_19.25 f2_19.25 a_wal f1_19.25 f2_19.25 a_wex a_wi f3_19.25 p_alimi f0_19.25 f2_19.25 a_wal f1_19.25 f2_19.25 a_wex f3_19.25 p_exim f0_19.25 f1_19.25 a_wi f2_19.25 a_wex f3_19.25 a_wal f0_19.25 f2_19.25 a_wal f1_19.25 f2_19.25 a_wex a_wi f3_19.25 a_wal f0_19.25 f2_19.25 a_wal f3_19.25 a_wex f1_19.25 f2_19.25 a_wex f3_19.25 a_wex a_wi p_syl $.
$}

$(Theorem 19.30 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps x  $.
	f0_19.30 $f wff ph $.
	f1_19.30 $f wff ps $.
	f2_19.30 $f set x $.
	p_19.30 $p |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) $= f0_19.30 f2_19.30 p_exnal f0_19.30 a_wn f1_19.30 f2_19.30 p_exim f0_19.30 f2_19.30 a_wal a_wn f0_19.30 a_wn f2_19.30 a_wex f0_19.30 a_wn f1_19.30 a_wi f2_19.30 a_wal f1_19.30 f2_19.30 a_wex p_syl5bir f0_19.30 f1_19.30 a_df-or f0_19.30 f1_19.30 a_wo f0_19.30 a_wn f1_19.30 a_wi f2_19.30 p_albii f0_19.30 f2_19.30 a_wal f1_19.30 f2_19.30 a_wex a_df-or f0_19.30 a_wn f1_19.30 a_wi f2_19.30 a_wal f0_19.30 f2_19.30 a_wal a_wn f1_19.30 f2_19.30 a_wex a_wi f0_19.30 f1_19.30 a_wo f2_19.30 a_wal f0_19.30 f2_19.30 a_wal f1_19.30 f2_19.30 a_wex a_wo p_3imtr4i $.
$}

$(Theorem 19.43 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 27-Jun-2014.) $)

${
	$v ph ps x  $.
	f0_19.43 $f wff ph $.
	f1_19.43 $f wff ps $.
	f2_19.43 $f set x $.
	p_19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $= f0_19.43 f1_19.43 a_df-or f0_19.43 f1_19.43 a_wo f0_19.43 a_wn f1_19.43 a_wi f2_19.43 p_exbii f0_19.43 a_wn f1_19.43 f2_19.43 p_19.35 f0_19.43 f2_19.43 p_alnex f0_19.43 a_wn f2_19.43 a_wal f0_19.43 f2_19.43 a_wex a_wn f1_19.43 f2_19.43 a_wex p_imbi1i f0_19.43 f1_19.43 a_wo f2_19.43 a_wex f0_19.43 a_wn f1_19.43 a_wi f2_19.43 a_wex f0_19.43 a_wn f2_19.43 a_wal f1_19.43 f2_19.43 a_wex a_wi f0_19.43 f2_19.43 a_wex a_wn f1_19.43 f2_19.43 a_wex a_wi p_3bitri f0_19.43 f2_19.43 a_wex f1_19.43 f2_19.43 a_wex a_df-or f0_19.43 f1_19.43 a_wo f2_19.43 a_wex f0_19.43 f2_19.43 a_wex a_wn f1_19.43 f2_19.43 a_wex a_wi f0_19.43 f2_19.43 a_wex f1_19.43 f2_19.43 a_wex a_wo p_bitr4i $.
$}

$(Obsolete proof of ~ 19.43 as of 3-May-2016.  Leave this in for the example
     on the mmrecent.html page.  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps x  $.
	f0_19.43OLD $f wff ph $.
	f1_19.43OLD $f wff ps $.
	f2_19.43OLD $f set x $.
	p_19.43OLD $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $= f0_19.43OLD f1_19.43OLD p_ioran f0_19.43OLD f1_19.43OLD a_wo a_wn f0_19.43OLD a_wn f1_19.43OLD a_wn a_wa f2_19.43OLD p_albii f0_19.43OLD a_wn f1_19.43OLD a_wn f2_19.43OLD p_19.26 f0_19.43OLD f2_19.43OLD p_alnex f1_19.43OLD f2_19.43OLD p_alnex f0_19.43OLD a_wn f2_19.43OLD a_wal f0_19.43OLD f2_19.43OLD a_wex a_wn f1_19.43OLD a_wn f2_19.43OLD a_wal f1_19.43OLD f2_19.43OLD a_wex a_wn p_anbi12i f0_19.43OLD f1_19.43OLD a_wo a_wn f2_19.43OLD a_wal f0_19.43OLD a_wn f1_19.43OLD a_wn a_wa f2_19.43OLD a_wal f0_19.43OLD a_wn f2_19.43OLD a_wal f1_19.43OLD a_wn f2_19.43OLD a_wal a_wa f0_19.43OLD f2_19.43OLD a_wex a_wn f1_19.43OLD f2_19.43OLD a_wex a_wn a_wa p_3bitri f0_19.43OLD f1_19.43OLD a_wo a_wn f2_19.43OLD a_wal f0_19.43OLD f2_19.43OLD a_wex a_wn f1_19.43OLD f2_19.43OLD a_wex a_wn a_wa p_notbii f0_19.43OLD f1_19.43OLD a_wo f2_19.43OLD a_df-ex f0_19.43OLD f2_19.43OLD a_wex f1_19.43OLD f2_19.43OLD a_wex p_oran f0_19.43OLD f1_19.43OLD a_wo a_wn f2_19.43OLD a_wal a_wn f0_19.43OLD f2_19.43OLD a_wex a_wn f1_19.43OLD f2_19.43OLD a_wex a_wn a_wa a_wn f0_19.43OLD f1_19.43OLD a_wo f2_19.43OLD a_wex f0_19.43OLD f2_19.43OLD a_wex f1_19.43OLD f2_19.43OLD a_wex a_wo p_3bitr4i $.
$}

$(Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.33 $f wff ph $.
	f1_19.33 $f wff ps $.
	f2_19.33 $f set x $.
	p_19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $= f0_19.33 f1_19.33 p_orc f0_19.33 f0_19.33 f1_19.33 a_wo f2_19.33 p_alimi f1_19.33 f0_19.33 p_olc f1_19.33 f0_19.33 f1_19.33 a_wo f2_19.33 p_alimi f0_19.33 f2_19.33 a_wal f0_19.33 f1_19.33 a_wo f2_19.33 a_wal f1_19.33 f2_19.33 a_wal p_jaoi $.
$}

$(The antecedent provides a condition implying the converse of ~ 19.33 .
     Compare Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM,
     27-Mar-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
     shortened by Wolf Lammen, 5-Jul-2014.) $)

${
	$v ph ps x  $.
	f0_19.33b $f wff ph $.
	f1_19.33b $f wff ps $.
	f2_19.33b $f set x $.
	p_19.33b $p |- ( -. ( E. x ph /\ E. x ps ) -> ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $= f0_19.33b f2_19.33b a_wex f1_19.33b f2_19.33b a_wex p_ianor f0_19.33b f2_19.33b p_alnex f0_19.33b f1_19.33b p_pm2.53 f0_19.33b f1_19.33b a_wo f0_19.33b a_wn f1_19.33b f2_19.33b p_al2imi f0_19.33b f2_19.33b a_wex a_wn f0_19.33b a_wn f2_19.33b a_wal f0_19.33b f1_19.33b a_wo f2_19.33b a_wal f1_19.33b f2_19.33b a_wal p_syl5bir f1_19.33b f2_19.33b a_wal f0_19.33b f2_19.33b a_wal p_olc f0_19.33b f1_19.33b a_wo f2_19.33b a_wal f0_19.33b f2_19.33b a_wex a_wn f1_19.33b f2_19.33b a_wal f0_19.33b f2_19.33b a_wal f1_19.33b f2_19.33b a_wal a_wo p_syl6com f0_19.33b f1_19.33b f2_19.33b p_19.30 f0_19.33b f1_19.33b a_wo f2_19.33b a_wal f0_19.33b f2_19.33b a_wal f1_19.33b f2_19.33b a_wex p_orcomd f0_19.33b f1_19.33b a_wo f2_19.33b a_wal f1_19.33b f2_19.33b a_wex f0_19.33b f2_19.33b a_wal p_ord f0_19.33b f2_19.33b a_wal f1_19.33b f2_19.33b a_wal p_orc f0_19.33b f1_19.33b a_wo f2_19.33b a_wal f1_19.33b f2_19.33b a_wex a_wn f0_19.33b f2_19.33b a_wal f0_19.33b f2_19.33b a_wal f1_19.33b f2_19.33b a_wal a_wo p_syl6com f0_19.33b f2_19.33b a_wex a_wn f0_19.33b f1_19.33b a_wo f2_19.33b a_wal f0_19.33b f2_19.33b a_wal f1_19.33b f2_19.33b a_wal a_wo a_wi f1_19.33b f2_19.33b a_wex a_wn p_jaoi f0_19.33b f2_19.33b a_wex f1_19.33b f2_19.33b a_wex a_wa a_wn f0_19.33b f2_19.33b a_wex a_wn f1_19.33b f2_19.33b a_wex a_wn a_wo f0_19.33b f1_19.33b a_wo f2_19.33b a_wal f0_19.33b f2_19.33b a_wal f1_19.33b f2_19.33b a_wal a_wo a_wi p_sylbi f0_19.33b f1_19.33b f2_19.33b p_19.33 f0_19.33b f2_19.33b a_wex f1_19.33b f2_19.33b a_wex a_wa a_wn f0_19.33b f1_19.33b a_wo f2_19.33b a_wal f0_19.33b f2_19.33b a_wal f1_19.33b f2_19.33b a_wal a_wo p_impbid1 $.
$}

$(Theorem 19.40 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.40 $f wff ph $.
	f1_19.40 $f wff ps $.
	f2_19.40 $f set x $.
	p_19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $= f0_19.40 f1_19.40 f2_19.40 p_exsimpl f0_19.40 f1_19.40 p_simpr f0_19.40 f1_19.40 a_wa f1_19.40 f2_19.40 p_eximi f0_19.40 f1_19.40 a_wa f2_19.40 a_wex f0_19.40 f2_19.40 a_wex f1_19.40 f2_19.40 a_wex p_jca $.
$}

$(Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)

${
	$v ph ps x y  $.
	f0_19.40-2 $f wff ph $.
	f1_19.40-2 $f wff ps $.
	f2_19.40-2 $f set x $.
	f3_19.40-2 $f set y $.
	p_19.40-2 $p |- ( E. x E. y ( ph /\ ps ) -> ( E. x E. y ph /\ E. x E. y ps ) ) $= f0_19.40-2 f1_19.40-2 f3_19.40-2 p_19.40 f0_19.40-2 f1_19.40-2 a_wa f3_19.40-2 a_wex f0_19.40-2 f3_19.40-2 a_wex f1_19.40-2 f3_19.40-2 a_wex a_wa f2_19.40-2 p_eximi f0_19.40-2 f3_19.40-2 a_wex f1_19.40-2 f3_19.40-2 a_wex f2_19.40-2 p_19.40 f0_19.40-2 f1_19.40-2 a_wa f3_19.40-2 a_wex f2_19.40-2 a_wex f0_19.40-2 f3_19.40-2 a_wex f1_19.40-2 f3_19.40-2 a_wex a_wa f2_19.40-2 a_wex f0_19.40-2 f3_19.40-2 a_wex f2_19.40-2 a_wex f1_19.40-2 f3_19.40-2 a_wex f2_19.40-2 a_wex a_wa p_syl $.
$}

$(Split a biconditional and distribute quantifier.  (Contributed by NM,
     18-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_albiim $f wff ph $.
	f1_albiim $f wff ps $.
	f2_albiim $f set x $.
	p_albiim $p |- ( A. x ( ph <-> ps ) <-> ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $= f0_albiim f1_albiim p_dfbi2 f0_albiim f1_albiim a_wb f0_albiim f1_albiim a_wi f1_albiim f0_albiim a_wi a_wa f2_albiim p_albii f0_albiim f1_albiim a_wi f1_albiim f0_albiim a_wi f2_albiim p_19.26 f0_albiim f1_albiim a_wb f2_albiim a_wal f0_albiim f1_albiim a_wi f1_albiim f0_albiim a_wi a_wa f2_albiim a_wal f0_albiim f1_albiim a_wi f2_albiim a_wal f1_albiim f0_albiim a_wi f2_albiim a_wal a_wa p_bitri $.
$}

$(Split a biconditional and distribute 2 quantifiers.  (Contributed by NM,
     3-Feb-2005.) $)

${
	$v ph ps x y  $.
	f0_2albiim $f wff ph $.
	f1_2albiim $f wff ps $.
	f2_2albiim $f set x $.
	f3_2albiim $f set y $.
	p_2albiim $p |- ( A. x A. y ( ph <-> ps ) <-> ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) ) $= f0_2albiim f1_2albiim f3_2albiim p_albiim f0_2albiim f1_2albiim a_wb f3_2albiim a_wal f0_2albiim f1_2albiim a_wi f3_2albiim a_wal f1_2albiim f0_2albiim a_wi f3_2albiim a_wal a_wa f2_2albiim p_albii f0_2albiim f1_2albiim a_wi f3_2albiim a_wal f1_2albiim f0_2albiim a_wi f3_2albiim a_wal f2_2albiim p_19.26 f0_2albiim f1_2albiim a_wb f3_2albiim a_wal f2_2albiim a_wal f0_2albiim f1_2albiim a_wi f3_2albiim a_wal f1_2albiim f0_2albiim a_wi f3_2albiim a_wal a_wa f2_2albiim a_wal f0_2albiim f1_2albiim a_wi f3_2albiim a_wal f2_2albiim a_wal f1_2albiim f0_2albiim a_wi f3_2albiim a_wal f2_2albiim a_wal a_wa p_bitri $.
$}

$(Add/remove a conjunct in the scope of an existential quantifier.
     (Contributed by Raph Levien, 3-Jul-2006.) $)

${
	$v ph ps x  $.
	f0_exintrbi $f wff ph $.
	f1_exintrbi $f wff ps $.
	f2_exintrbi $f set x $.
	p_exintrbi $p |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) ) $= f0_exintrbi f1_exintrbi p_pm4.71 f0_exintrbi f1_exintrbi a_wi f0_exintrbi f0_exintrbi f1_exintrbi a_wa a_wb f2_exintrbi p_albii f0_exintrbi f0_exintrbi f1_exintrbi a_wa f2_exintrbi p_exbi f0_exintrbi f1_exintrbi a_wi f2_exintrbi a_wal f0_exintrbi f0_exintrbi f1_exintrbi a_wa a_wb f2_exintrbi a_wal f0_exintrbi f2_exintrbi a_wex f0_exintrbi f1_exintrbi a_wa f2_exintrbi a_wex a_wb p_sylbi $.
$}

$(Introduce a conjunct in the scope of an existential quantifier.
     (Contributed by NM, 11-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_exintr $f wff ph $.
	f1_exintr $f wff ps $.
	f2_exintr $f set x $.
	p_exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $= f0_exintr f1_exintr f2_exintr p_exintrbi f0_exintr f1_exintr a_wi f2_exintr a_wal f0_exintr f2_exintr a_wex f0_exintr f1_exintr a_wa f2_exintr a_wex p_biimpd $.
$}

$(Theorem *10.3 in [WhiteheadRussell] p. 150.  (Contributed by Andrew
     Salmon, 8-Jun-2011.) $)

${
	$v ph ps ch x  $.
	f0_alsyl $f wff ph $.
	f1_alsyl $f wff ps $.
	f2_alsyl $f wff ch $.
	f3_alsyl $f set x $.
	p_alsyl $p |- ( ( A. x ( ph -> ps ) /\ A. x ( ps -> ch ) ) -> A. x ( ph -> ch ) ) $= f0_alsyl f1_alsyl f2_alsyl p_pm3.33 f0_alsyl f1_alsyl a_wi f1_alsyl f2_alsyl a_wi f0_alsyl f2_alsyl a_wi f3_alsyl p_alanimi $.
$}


