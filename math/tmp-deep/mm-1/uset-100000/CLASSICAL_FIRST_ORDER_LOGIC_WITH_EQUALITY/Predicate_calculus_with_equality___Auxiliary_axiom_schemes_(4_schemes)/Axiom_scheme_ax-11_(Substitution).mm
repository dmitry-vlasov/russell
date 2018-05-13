$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-7_(Quantifier_Commutation).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Axiom scheme ax-11 (Substitution)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing " ` y ` substituted for ` x ` in wff ` ph ` " (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     The original version of this axiom was ~ ax-11o ("o" for "old") and was
     replaced with this shorter ~ ax-11 in Jan. 2007.  The old axiom is proved
     from this one as theorem ~ ax11o .  Conversely, this axiom is proved from
     ~ ax-11o as theorem ~ ax11 .

     Juha Arpiainen proved the metalogical independence of this axiom (in the
     form of the older axiom ~ ax-11o ) from the others on 19-Jan-2006.  See
     item 9a at ~ http://us.metamath.org/award2003.html .

     See ~ ax11v and ~ ax11v2 for other equivalents of this axiom that (unlike
     this axiom) have distinct variable restrictions.

     This axiom scheme is logically redundant (see ~ ax11w ) but is used as an
     auxiliary axiom to achieve metalogical completeness.  (Contributed by NM,
     22-Jan-2007.) $)

${
	$v ph x y  $.
	f0_ax-11 $f wff ph $.
	f1_ax-11 $f set x $.
	f2_ax-11 $f set y $.
	a_ax-11 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.
$}

$(Specialization.  A universally quantified wff implies the wff without a
       quantifier Axiom scheme B5 of [Tarski] p. 67 (under his system S2,
       defined in the last paragraph on p. 77).  Also appears as Axiom scheme
       C5' in [Megill] p. 448 (p. 16 of the preprint).

       For the axiom of specialization presented in many logic textbooks, see
       theorem ~ stdpc4 .

       This theorem shows that our obsolete axiom ~ ax-4 can be derived from
       the others.  The proof uses ideas from the proof of Lemma 21 of [Monk2]
       p. 114.

       It appears that this scheme cannot be derived directly from Tarski's
       axioms without auxilliary axiom scheme ~ ax-11 .  It is thought the best
       we can do using only Tarski's axioms is ~ spw .  (Contributed by NM,
       21-May-2008.)  (Proof shortened by Scott Fenton, 24-Jan-2011.) $)

${
	$v ph x  $.
	$d x w  $.
	$d w ph  $.
	f0_sp $f wff ph $.
	f1_sp $f set x $.
	i0_sp $f set w $.
	p_sp $p |- ( A. x ph -> ph ) $= i0_sp f1_sp p_ax9v i0_sp f1_sp p_equcomi f0_sp a_wn i0_sp a_ax-17 f0_sp a_wn f1_sp i0_sp a_ax-11 i0_sp a_sup_set_class f1_sp a_sup_set_class a_wceq f1_sp a_sup_set_class i0_sp a_sup_set_class a_wceq f0_sp a_wn f0_sp a_wn i0_sp a_wal f1_sp a_sup_set_class i0_sp a_sup_set_class a_wceq f0_sp a_wn a_wi f1_sp a_wal p_syl2im f1_sp i0_sp p_ax9v f1_sp a_sup_set_class i0_sp a_sup_set_class a_wceq f0_sp p_con2 f1_sp a_sup_set_class i0_sp a_sup_set_class a_wceq f0_sp a_wn a_wi f0_sp f1_sp a_sup_set_class i0_sp a_sup_set_class a_wceq a_wn f1_sp p_al2imi f1_sp a_sup_set_class i0_sp a_sup_set_class a_wceq f0_sp a_wn a_wi f1_sp a_wal f0_sp f1_sp a_wal f1_sp a_sup_set_class i0_sp a_sup_set_class a_wceq a_wn f1_sp a_wal p_mtoi i0_sp a_sup_set_class f1_sp a_sup_set_class a_wceq f0_sp a_wn f1_sp a_sup_set_class i0_sp a_sup_set_class a_wceq f0_sp a_wn a_wi f1_sp a_wal f0_sp f1_sp a_wal a_wn p_syl6 i0_sp a_sup_set_class f1_sp a_sup_set_class a_wceq f0_sp f0_sp f1_sp a_wal p_con4d i0_sp a_sup_set_class f1_sp a_sup_set_class a_wceq f0_sp f1_sp a_wal f0_sp a_wi p_con3i f0_sp f1_sp a_wal f0_sp a_wi a_wn i0_sp a_sup_set_class f1_sp a_sup_set_class a_wceq a_wn i0_sp p_alrimiv f0_sp f1_sp a_wal f0_sp a_wi i0_sp a_sup_set_class f1_sp a_sup_set_class a_wceq a_wn i0_sp a_wal p_mt3 $.
$}

$(Show that the original axiom ~ ax-5o can be derived from ~ ax-5 and
     others.  See ~ ax5 for the rederivation of ~ ax-5 from ~ ax-5o .

     Part of the proof is based on the proof of Lemma 22 of [Monk2] p. 114.
     (Contributed by NM, 21-May-2008.)  (Proof modification is discouraged.) $)

${
	$v ph ps x  $.
	f0_ax5o $f wff ph $.
	f1_ax5o $f wff ps $.
	f2_ax5o $f set x $.
	p_ax5o $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $= f0_ax5o f2_ax5o a_wal a_wn f2_ax5o p_sp f0_ax5o f2_ax5o a_wal a_wn f2_ax5o a_wal f0_ax5o f2_ax5o a_wal p_con2i f0_ax5o f2_ax5o a_wal a_wn f2_ax5o p_hbn1 f0_ax5o f2_ax5o p_hbn1 f0_ax5o f2_ax5o a_wal f0_ax5o f2_ax5o a_wal a_wn f2_ax5o a_wal p_con1i f0_ax5o f2_ax5o a_wal a_wn f2_ax5o a_wal a_wn f0_ax5o f2_ax5o a_wal f2_ax5o p_alimi f0_ax5o f2_ax5o a_wal f0_ax5o f2_ax5o a_wal a_wn f2_ax5o a_wal a_wn f0_ax5o f2_ax5o a_wal a_wn f2_ax5o a_wal a_wn f2_ax5o a_wal f0_ax5o f2_ax5o a_wal f2_ax5o a_wal p_3syl f0_ax5o f2_ax5o a_wal f1_ax5o f2_ax5o a_ax-5 f0_ax5o f2_ax5o a_wal f0_ax5o f2_ax5o a_wal f2_ax5o a_wal f0_ax5o f2_ax5o a_wal f1_ax5o a_wi f2_ax5o a_wal f1_ax5o f2_ax5o a_wal p_syl5 $.
$}

$(If a wff is true, it is true for at least one instance.  Special case of
     Theorem 19.8 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_19.8a $f wff ph $.
	f1_19.8a $f set x $.
	p_19.8a $p |- ( ph -> E. x ph ) $= f0_19.8a a_wn f1_19.8a p_sp f0_19.8a a_wn f1_19.8a a_wal f0_19.8a p_con2i f0_19.8a f1_19.8a a_df-ex f0_19.8a f0_19.8a a_wn f1_19.8a a_wal a_wn f0_19.8a f1_19.8a a_wex p_sylibr $.
$}

$(` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_hba1 $f wff ph $.
	f1_hba1 $f set x $.
	p_hba1 $p |- ( A. x ph -> A. x A. x ph ) $= f0_hba1 f1_hba1 a_wal a_wn f1_hba1 p_sp f0_hba1 f1_hba1 a_wal a_wn f1_hba1 a_wal f0_hba1 f1_hba1 a_wal p_con2i f0_hba1 f1_hba1 a_wal a_wn f1_hba1 p_hbn1 f0_hba1 f1_hba1 p_hbn1 f0_hba1 f1_hba1 a_wal f0_hba1 f1_hba1 a_wal a_wn f1_hba1 a_wal p_con1i f0_hba1 f1_hba1 a_wal a_wn f1_hba1 a_wal a_wn f0_hba1 f1_hba1 a_wal f1_hba1 p_alimi f0_hba1 f1_hba1 a_wal f0_hba1 f1_hba1 a_wal a_wn f1_hba1 a_wal a_wn f0_hba1 f1_hba1 a_wal a_wn f1_hba1 a_wal a_wn f1_hba1 a_wal f0_hba1 f1_hba1 a_wal f1_hba1 a_wal p_3syl $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_hbn $f wff ph $.
	f1_hbn $f set x $.
	e0_hbn $e |- ( ph -> A. x ph ) $.
	p_hbn $p |- ( -. ph -> A. x -. ph ) $= f0_hbn f1_hbn p_sp f0_hbn f1_hbn a_wal f0_hbn p_con3i f0_hbn f1_hbn p_hbn1 e0_hbn f0_hbn f0_hbn f1_hbn a_wal p_con3i f0_hbn f1_hbn a_wal a_wn f0_hbn a_wn f1_hbn p_alrimih f0_hbn a_wn f0_hbn f1_hbn a_wal a_wn f0_hbn a_wn f1_hbn a_wal p_syl $.
$}

$(Deduction form of bound-variable hypothesis builder ~ hbim .
       (Contributed by NM, 1-Jan-2002.) $)

${
	$v ph ps ch x  $.
	f0_hbimd $f wff ph $.
	f1_hbimd $f wff ps $.
	f2_hbimd $f wff ch $.
	f3_hbimd $f set x $.
	e0_hbimd $e |- ( ph -> A. x ph ) $.
	e1_hbimd $e |- ( ph -> ( ps -> A. x ps ) ) $.
	e2_hbimd $e |- ( ph -> ( ch -> A. x ch ) ) $.
	p_hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $= e0_hbimd e1_hbimd f0_hbimd f1_hbimd f1_hbimd f3_hbimd a_wal a_wi f3_hbimd p_alrimih f1_hbimd f3_hbimd p_sp f1_hbimd f3_hbimd p_hbn1 f1_hbimd f3_hbimd a_wal f1_hbimd f1_hbimd f3_hbimd a_wal a_wn f3_hbimd a_wal p_nsyl4 f1_hbimd f3_hbimd a_wal a_wn f3_hbimd a_wal f1_hbimd p_con1i f1_hbimd f1_hbimd f3_hbimd a_wal p_con3 f1_hbimd f1_hbimd f3_hbimd a_wal a_wi f1_hbimd f3_hbimd a_wal a_wn f1_hbimd a_wn f3_hbimd p_al2imi f0_hbimd f1_hbimd f1_hbimd f3_hbimd a_wal a_wi f3_hbimd a_wal f1_hbimd a_wn f1_hbimd f3_hbimd a_wal a_wn f3_hbimd a_wal f1_hbimd a_wn f3_hbimd a_wal p_syl2im f1_hbimd f2_hbimd p_pm2.21 f1_hbimd a_wn f1_hbimd f2_hbimd a_wi f3_hbimd p_alimi f0_hbimd f1_hbimd a_wn f1_hbimd a_wn f3_hbimd a_wal f1_hbimd f2_hbimd a_wi f3_hbimd a_wal p_syl6 e2_hbimd f2_hbimd f1_hbimd a_ax-1 f2_hbimd f1_hbimd f2_hbimd a_wi f3_hbimd p_alimi f0_hbimd f2_hbimd f2_hbimd f3_hbimd a_wal f1_hbimd f2_hbimd a_wi f3_hbimd a_wal p_syl6 f0_hbimd f1_hbimd f2_hbimd f1_hbimd f2_hbimd a_wi f3_hbimd a_wal p_jad $.
$}

$(Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.) $)

${
	$v ph ps x z  $.
	$d x z  $.
	$d ph  $.
	f0_spimeh $f wff ph $.
	f1_spimeh $f wff ps $.
	f2_spimeh $f set x $.
	f3_spimeh $f set z $.
	e0_spimeh $e |- ( ph -> A. x ph ) $.
	e1_spimeh $e |- ( x = z -> ( ph -> ps ) ) $.
	p_spimeh $p |- ( ph -> E. x ps ) $= f2_spimeh f3_spimeh p_ax9v f0_spimeh p_id f0_spimeh p_id f0_spimeh f0_spimeh a_wi f2_spimeh p_hbth f1_spimeh a_wn f2_spimeh p_hba1 f1_spimeh a_wn f2_spimeh a_wal f1_spimeh a_wn f2_spimeh a_wal f2_spimeh a_wal a_wi f0_spimeh f0_spimeh a_wi p_a1i e0_spimeh f0_spimeh f2_spimeh p_hbn f0_spimeh a_wn f0_spimeh a_wn f2_spimeh a_wal a_wi f0_spimeh f0_spimeh a_wi p_a1i f0_spimeh f0_spimeh a_wi f1_spimeh a_wn f2_spimeh a_wal f0_spimeh a_wn f2_spimeh p_hbimd f0_spimeh f0_spimeh a_wi f1_spimeh a_wn f2_spimeh a_wal f0_spimeh a_wn a_wi f1_spimeh a_wn f2_spimeh a_wal f0_spimeh a_wn a_wi f2_spimeh a_wal a_wi a_ax-mp f1_spimeh a_wn f2_spimeh a_wal f0_spimeh a_wn a_wi f2_spimeh p_hbn e1_spimeh f1_spimeh a_wn f2_spimeh p_sp f2_spimeh a_sup_set_class f3_spimeh a_sup_set_class a_wceq f0_spimeh f1_spimeh f1_spimeh a_wn f2_spimeh a_wal p_nsyli f2_spimeh a_sup_set_class f3_spimeh a_sup_set_class a_wceq f1_spimeh a_wn f2_spimeh a_wal f0_spimeh a_wn a_wi p_con3i f1_spimeh a_wn f2_spimeh a_wal f0_spimeh a_wn a_wi a_wn f2_spimeh a_sup_set_class f3_spimeh a_sup_set_class a_wceq a_wn f2_spimeh p_alrimih f1_spimeh a_wn f2_spimeh a_wal f0_spimeh a_wn a_wi f2_spimeh a_sup_set_class f3_spimeh a_sup_set_class a_wceq a_wn f2_spimeh a_wal p_mt3 f1_spimeh a_wn f2_spimeh a_wal f0_spimeh p_con2i f1_spimeh f2_spimeh a_df-ex f0_spimeh f1_spimeh a_wn f2_spimeh a_wal a_wn f1_spimeh f2_spimeh a_wex p_sylibr $.
$}

$(Show that the original axiom ~ ax-6o can be derived from ~ ax-6 and
     others.  See ~ ax6 for the rederivation of ~ ax-6 from ~ ax-6o .

     Normally, ~ ax6o should be used rather than ~ ax-6o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     21-May-2008.) $)

${
	$v ph x  $.
	f0_ax6o $f wff ph $.
	f1_ax6o $f set x $.
	p_ax6o $p |- ( -. A. x -. A. x ph -> ph ) $= f0_ax6o f1_ax6o p_sp f0_ax6o f1_ax6o a_ax-6 f0_ax6o f1_ax6o a_wal f0_ax6o f0_ax6o f1_ax6o a_wal a_wn f1_ax6o a_wal p_nsyl4 $.
$}

$(Closed theorem version of bound-variable hypothesis builder ~ hbn .
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_hbnt $f wff ph $.
	f1_hbnt $f set x $.
	p_hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $= f0_hbnt f1_hbnt p_ax6o f0_hbnt f1_hbnt a_wal a_wn f1_hbnt a_wal f0_hbnt p_con1i f0_hbnt f0_hbnt f1_hbnt a_wal p_con3 f0_hbnt f0_hbnt f1_hbnt a_wal a_wi f0_hbnt f1_hbnt a_wal a_wn f0_hbnt a_wn f1_hbnt p_al2imi f0_hbnt a_wn f0_hbnt f1_hbnt a_wal a_wn f1_hbnt a_wal f0_hbnt f0_hbnt f1_hbnt a_wal a_wi f1_hbnt a_wal f0_hbnt a_wn f1_hbnt a_wal p_syl5 $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 3-Mar-2008.) $)

${
	$v ph ps x  $.
	f0_hbim $f wff ph $.
	f1_hbim $f wff ps $.
	f2_hbim $f set x $.
	e0_hbim $e |- ( ph -> A. x ph ) $.
	e1_hbim $e |- ( ps -> A. x ps ) $.
	p_hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $= e0_hbim f0_hbim f2_hbim p_hbn f0_hbim f1_hbim p_pm2.21 f0_hbim a_wn f0_hbim f1_hbim a_wi f2_hbim p_alrimih e1_hbim f1_hbim f0_hbim a_ax-1 f1_hbim f0_hbim f1_hbim a_wi f2_hbim p_alrimih f0_hbim f1_hbim f0_hbim f1_hbim a_wi f2_hbim a_wal p_ja $.
$}

$(A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_19.9ht $f wff ph $.
	f1_19.9ht $f set x $.
	p_19.9ht $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $= f0_19.9ht f1_19.9ht a_df-ex f0_19.9ht f1_19.9ht p_hbnt f0_19.9ht f0_19.9ht f1_19.9ht a_wal a_wi f1_19.9ht a_wal f0_19.9ht f0_19.9ht a_wn f1_19.9ht a_wal p_con1d f0_19.9ht f1_19.9ht a_wex f0_19.9ht a_wn f1_19.9ht a_wal a_wn f0_19.9ht f0_19.9ht f1_19.9ht a_wal a_wi f1_19.9ht a_wal f0_19.9ht p_syl5bi $.
$}

$(A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.) $)

${
	$v ph x  $.
	f0_19.9h $f wff ph $.
	f1_19.9h $f set x $.
	e0_19.9h $e |- ( ph -> A. x ph ) $.
	p_19.9h $p |- ( E. x ph <-> ph ) $= f0_19.9h f1_19.9h p_19.9ht e0_19.9h f0_19.9h f0_19.9h f1_19.9h a_wal a_wi f0_19.9h f1_19.9h a_wex f0_19.9h a_wi f1_19.9h p_mpg f0_19.9h f1_19.9h p_19.8a f0_19.9h f1_19.9h a_wex f0_19.9h p_impbii $.
$}

$(Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_19.23h $f wff ph $.
	f1_19.23h $f wff ps $.
	f2_19.23h $f set x $.
	e0_19.23h $e |- ( ps -> A. x ps ) $.
	p_19.23h $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $= f0_19.23h f1_19.23h f2_19.23h p_exim e0_19.23h f1_19.23h f2_19.23h p_19.9h f0_19.23h f1_19.23h a_wi f2_19.23h a_wal f0_19.23h f2_19.23h a_wex f1_19.23h f2_19.23h a_wex f1_19.23h p_syl6ib f0_19.23h f2_19.23h p_hbe1 e0_19.23h f0_19.23h f2_19.23h a_wex f1_19.23h f2_19.23h p_hbim f0_19.23h f2_19.23h p_19.8a f0_19.23h f0_19.23h f2_19.23h a_wex f1_19.23h p_imim1i f0_19.23h f2_19.23h a_wex f1_19.23h a_wi f0_19.23h f1_19.23h a_wi f2_19.23h p_alrimih f0_19.23h f1_19.23h a_wi f2_19.23h a_wal f0_19.23h f2_19.23h a_wex f1_19.23h a_wi p_impbii $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v ph ps x  $.
	f0_exlimih $f wff ph $.
	f1_exlimih $f wff ps $.
	f2_exlimih $f set x $.
	e0_exlimih $e |- ( ps -> A. x ps ) $.
	e1_exlimih $e |- ( ph -> ps ) $.
	p_exlimih $p |- ( E. x ph -> ps ) $= e0_exlimih f0_exlimih f1_exlimih f2_exlimih p_19.23h e1_exlimih f0_exlimih f1_exlimih a_wi f0_exlimih f2_exlimih a_wex f1_exlimih a_wi f2_exlimih p_mpgbi $.
$}

$(Weaker version of ~ equsalh (requiring distinct variables) without using
       ~ ax-12 .  (Contributed by NM, 29-Nov-2015.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	f0_equsalhw $f wff ph $.
	f1_equsalhw $f wff ps $.
	f2_equsalhw $f set x $.
	f3_equsalhw $f set y $.
	e0_equsalhw $e |- ( ps -> A. x ps ) $.
	e1_equsalhw $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_equsalhw $p |- ( A. x ( x = y -> ph ) <-> ps ) $= e1_equsalhw f1_equsalhw f2_equsalhw p_sp e0_equsalhw f1_equsalhw f2_equsalhw a_wal f1_equsalhw p_impbii f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f0_equsalhw f1_equsalhw f1_equsalhw f2_equsalhw a_wal p_syl6bbr f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f0_equsalhw f1_equsalhw f2_equsalhw a_wal p_pm5.74i f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f0_equsalhw a_wi f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f1_equsalhw f2_equsalhw a_wal a_wi f2_equsalhw p_albii e0_equsalhw e0_equsalhw f1_equsalhw f1_equsalhw f2_equsalhw a_wal f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq p_a1d f1_equsalhw f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f1_equsalhw f2_equsalhw a_wal a_wi f2_equsalhw p_alrimih f2_equsalhw f3_equsalhw p_ax9v f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f1_equsalhw f2_equsalhw a_wal p_con3 f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f1_equsalhw f2_equsalhw a_wal a_wi f1_equsalhw f2_equsalhw a_wal a_wn f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq a_wn f2_equsalhw p_al2imi f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f1_equsalhw f2_equsalhw a_wal a_wi f2_equsalhw a_wal f1_equsalhw f2_equsalhw a_wal a_wn f2_equsalhw a_wal f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq a_wn f2_equsalhw a_wal p_mtoi f1_equsalhw f2_equsalhw p_ax6o f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f1_equsalhw f2_equsalhw a_wal a_wi f2_equsalhw a_wal f1_equsalhw f2_equsalhw a_wal a_wn f2_equsalhw a_wal a_wn f1_equsalhw p_syl f1_equsalhw f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f1_equsalhw f2_equsalhw a_wal a_wi f2_equsalhw a_wal p_impbii f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f0_equsalhw a_wi f2_equsalhw a_wal f2_equsalhw a_sup_set_class f3_equsalhw a_sup_set_class a_wceq f1_equsalhw f2_equsalhw a_wal a_wi f2_equsalhw a_wal f1_equsalhw p_bitr4i $.
$}

$(Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ."  (Contributed by NM, 1-Aug-2017.) $)

${
	$v ph ps x  $.
	f0_19.21h $f wff ph $.
	f1_19.21h $f wff ps $.
	f2_19.21h $f set x $.
	e0_19.21h $e |- ( ph -> A. x ph ) $.
	p_19.21h $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $= e0_19.21h f0_19.21h f1_19.21h f2_19.21h p_alim f0_19.21h f0_19.21h f2_19.21h a_wal f0_19.21h f1_19.21h a_wi f2_19.21h a_wal f1_19.21h f2_19.21h a_wal p_syl5 e0_19.21h f1_19.21h f2_19.21h p_hba1 f0_19.21h f1_19.21h f2_19.21h a_wal f2_19.21h p_hbim f1_19.21h f2_19.21h p_sp f1_19.21h f2_19.21h a_wal f1_19.21h f0_19.21h p_imim2i f0_19.21h f1_19.21h f2_19.21h a_wal a_wi f0_19.21h f1_19.21h a_wi f2_19.21h p_alrimih f0_19.21h f1_19.21h a_wi f2_19.21h a_wal f0_19.21h f1_19.21h f2_19.21h a_wal a_wi p_impbii $.
$}

$(A closed form of ~ hbim .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_hbim1 $f wff ph $.
	f1_hbim1 $f wff ps $.
	f2_hbim1 $f set x $.
	e0_hbim1 $e |- ( ph -> A. x ph ) $.
	e1_hbim1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
	p_hbim1 $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $= e1_hbim1 f0_hbim1 f1_hbim1 f1_hbim1 f2_hbim1 a_wal p_a2i e0_hbim1 f0_hbim1 f1_hbim1 f2_hbim1 p_19.21h f0_hbim1 f1_hbim1 a_wi f0_hbim1 f1_hbim1 f2_hbim1 a_wal a_wi f0_hbim1 f1_hbim1 a_wi f2_hbim1 a_wal p_sylibr $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_hbex $f wff ph $.
	f1_hbex $f set x $.
	f2_hbex $f set y $.
	e0_hbex $e |- ( ph -> A. x ph ) $.
	p_hbex $p |- ( E. y ph -> A. x E. y ph ) $= f0_hbex f2_hbex a_df-ex e0_hbex f0_hbex f1_hbex p_hbn f0_hbex a_wn f1_hbex f2_hbex p_hbal f0_hbex a_wn f2_hbex a_wal f1_hbex p_hbn f0_hbex f2_hbex a_wex f0_hbex a_wn f2_hbex a_wal a_wn f1_hbex p_hbxfrbi $.
$}

$(Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  But sometimes the converse does hold, as in
     ~ 19.12vv and ~ r19.12sn .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_19.12 $f wff ph $.
	f1_19.12 $f set x $.
	f2_19.12 $f set y $.
	p_19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $= f0_19.12 f2_19.12 p_hba1 f0_19.12 f2_19.12 a_wal f2_19.12 f1_19.12 p_hbex f0_19.12 f2_19.12 p_sp f0_19.12 f2_19.12 a_wal f0_19.12 f1_19.12 p_eximi f0_19.12 f2_19.12 a_wal f1_19.12 a_wex f0_19.12 f1_19.12 a_wex f2_19.12 p_alrimih $.
$}

$(dvelimhw.4 $e |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $. $)

$(Proof of ~ dvelimh without using ~ ax-12 but with additional distinct
       variable conditions.  (Contributed by Andrew Salmon, 21-Jul-2011.)
       (Revised by NM, 1-Aug-2017.) $)

${
	$v ph ps x y z  $.
	$d x z  $.
	$d y z  $.
	f0_dvelimhw $f wff ph $.
	f1_dvelimhw $f wff ps $.
	f2_dvelimhw $f set x $.
	f3_dvelimhw $f set y $.
	f4_dvelimhw $f set z $.
	e0_dvelimhw $e |- ( ph -> A. x ph ) $.
	e1_dvelimhw $e |- ( ps -> A. z ps ) $.
	e2_dvelimhw $e |- ( z = y -> ( ph <-> ps ) ) $.
	e3_dvelimhw $e |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $.
	p_dvelimhw $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= f2_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_wal a_wn f4_dvelimhw a_ax-17 f2_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw p_hbn1 f4_dvelimhw f3_dvelimhw p_equcomi e3_dvelimhw f3_dvelimhw f4_dvelimhw p_equcomi f3_dvelimhw a_sup_set_class f4_dvelimhw a_sup_set_class a_wceq f4_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw p_alimi f4_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f3_dvelimhw a_sup_set_class f4_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_wal a_wn f3_dvelimhw a_sup_set_class f4_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_wal f4_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_wal p_syl56 e0_dvelimhw f0_dvelimhw f0_dvelimhw f2_dvelimhw a_wal a_wi f2_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_wal a_wn p_a1i f2_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_wal a_wn f4_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f0_dvelimhw f2_dvelimhw p_hbimd f2_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_wal a_wn f4_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f0_dvelimhw a_wi f2_dvelimhw f4_dvelimhw p_hbald e1_dvelimhw e2_dvelimhw f0_dvelimhw f1_dvelimhw f4_dvelimhw f3_dvelimhw p_equsalhw e1_dvelimhw e2_dvelimhw f0_dvelimhw f1_dvelimhw f4_dvelimhw f3_dvelimhw p_equsalhw f4_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f0_dvelimhw a_wi f4_dvelimhw a_wal f1_dvelimhw f2_dvelimhw p_albii f2_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f2_dvelimhw a_wal a_wn f4_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f0_dvelimhw a_wi f4_dvelimhw a_wal f4_dvelimhw a_sup_set_class f3_dvelimhw a_sup_set_class a_wceq f0_dvelimhw a_wi f4_dvelimhw a_wal f2_dvelimhw a_wal f1_dvelimhw f1_dvelimhw f2_dvelimhw a_wal p_3imtr3g $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_hban $f wff ph $.
	f1_hban $f wff ps $.
	f2_hban $f set x $.
	e0_hban $e |- ( ph -> A. x ph ) $.
	e1_hban $e |- ( ps -> A. x ps ) $.
	p_hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $= f0_hban f1_hban a_df-an e0_hban e1_hban f1_hban f2_hban p_hbn f0_hban f1_hban a_wn f2_hban p_hbim f0_hban f1_hban a_wn a_wi f2_hban p_hbn f0_hban f1_hban a_wa f0_hban f1_hban a_wn a_wi a_wn f2_hban p_hbxfrbi $.
$}

$(Lemma for ~ ax10 .  Similar to ~ cbv3h .  Requires distinct variables
       but avoids ~ ax-12 .  (Contributed by NM, 25-Jul-2015.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	f0_cbv3hv $f wff ph $.
	f1_cbv3hv $f wff ps $.
	f2_cbv3hv $f set x $.
	f3_cbv3hv $f set y $.
	e0_cbv3hv $e |- ( ph -> A. y ph ) $.
	e1_cbv3hv $e |- ( ps -> A. x ps ) $.
	e2_cbv3hv $e |- ( x = y -> ( ph -> ps ) ) $.
	p_cbv3hv $p |- ( A. x ph -> A. y ps ) $= e0_cbv3hv f0_cbv3hv f0_cbv3hv f3_cbv3hv a_wal f2_cbv3hv p_alimi f2_cbv3hv f3_cbv3hv p_ax9v f0_cbv3hv f2_cbv3hv p_hba1 e1_cbv3hv f0_cbv3hv f2_cbv3hv a_wal f1_cbv3hv f2_cbv3hv p_hbim f0_cbv3hv f2_cbv3hv a_wal f1_cbv3hv a_wi f2_cbv3hv p_hbn f0_cbv3hv f2_cbv3hv p_sp e2_cbv3hv f0_cbv3hv f2_cbv3hv a_wal f0_cbv3hv f2_cbv3hv a_sup_set_class f3_cbv3hv a_sup_set_class a_wceq f1_cbv3hv p_syl5 f2_cbv3hv a_sup_set_class f3_cbv3hv a_sup_set_class a_wceq f0_cbv3hv f2_cbv3hv a_wal f1_cbv3hv a_wi p_con3i f0_cbv3hv f2_cbv3hv a_wal f1_cbv3hv a_wi a_wn f2_cbv3hv a_sup_set_class f3_cbv3hv a_sup_set_class a_wceq a_wn f2_cbv3hv p_alrimih f0_cbv3hv f2_cbv3hv a_wal f1_cbv3hv a_wi f2_cbv3hv a_sup_set_class f3_cbv3hv a_sup_set_class a_wceq a_wn f2_cbv3hv a_wal p_mt3 f0_cbv3hv f2_cbv3hv a_wal f1_cbv3hv f3_cbv3hv p_alimi f0_cbv3hv f1_cbv3hv f3_cbv3hv a_wal f3_cbv3hv f2_cbv3hv p_a7s f0_cbv3hv f2_cbv3hv a_wal f0_cbv3hv f3_cbv3hv a_wal f2_cbv3hv a_wal f1_cbv3hv f3_cbv3hv a_wal p_syl $.
$}

$(Inference rule reversing generalization.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph x  $.
	f0_spi $f wff ph $.
	f1_spi $f set x $.
	e0_spi $e |- A. x ph $.
	p_spi $p |- ph $= e0_spi f0_spi f1_spi p_sp f0_spi f1_spi a_wal f0_spi a_ax-mp $.
$}

$(Generalization of antecedent.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_sps $f wff ph $.
	f1_sps $f wff ps $.
	f2_sps $f set x $.
	e0_sps $e |- ( ph -> ps ) $.
	p_sps $p |- ( A. x ph -> ps ) $= f0_sps f2_sps p_sp e0_sps f0_sps f2_sps a_wal f0_sps f1_sps p_syl $.
$}

$(Deduction generalizing antecedent.  (Contributed by NM, 17-Aug-1994.) $)

${
	$v ph ps ch x  $.
	f0_spsd $f wff ph $.
	f1_spsd $f wff ps $.
	f2_spsd $f wff ch $.
	f3_spsd $f set x $.
	e0_spsd $e |- ( ph -> ( ps -> ch ) ) $.
	p_spsd $p |- ( ph -> ( A. x ps -> ch ) ) $= f1_spsd f3_spsd p_sp e0_spsd f1_spsd f3_spsd a_wal f1_spsd f0_spsd f2_spsd p_syl5 $.
$}

$(Consequence of the definition of not-free.  (Contributed by Mario
     Carneiro, 26-Sep-2016.) $)

${
	$v ph x  $.
	f0_nfr $f wff ph $.
	f1_nfr $f set x $.
	p_nfr $p |- ( F/ x ph -> ( ph -> A. x ph ) ) $= f0_nfr f1_nfr a_df-nf f0_nfr f0_nfr f1_nfr a_wal a_wi f1_nfr p_sp f0_nfr f1_nfr a_wnf f0_nfr f0_nfr f1_nfr a_wal a_wi f1_nfr a_wal f0_nfr f0_nfr f1_nfr a_wal a_wi p_sylbi $.
$}

$(Consequence of the definition of not-free.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)

${
	$v ph x  $.
	f0_nfri $f wff ph $.
	f1_nfri $f set x $.
	e0_nfri $e |- F/ x ph $.
	p_nfri $p |- ( ph -> A. x ph ) $= e0_nfri f0_nfri f1_nfri p_nfr f0_nfri f1_nfri a_wnf f0_nfri f0_nfri f1_nfri a_wal a_wi a_ax-mp $.
$}

$(Consequence of the definition of not-free in a context.  (Contributed by
       Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x  $.
	f0_nfrd $f wff ph $.
	f1_nfrd $f wff ps $.
	f2_nfrd $f set x $.
	e0_nfrd $e |- ( ph -> F/ x ps ) $.
	p_nfrd $p |- ( ph -> ( ps -> A. x ps ) ) $= e0_nfrd f1_nfrd f2_nfrd p_nfr f0_nfrd f1_nfrd f2_nfrd a_wnf f1_nfrd f1_nfrd f2_nfrd a_wal a_wi p_syl $.
$}

$(Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_alimd $f wff ph $.
	f1_alimd $f wff ps $.
	f2_alimd $f wff ch $.
	f3_alimd $f set x $.
	e0_alimd $e |- F/ x ph $.
	e1_alimd $e |- ( ph -> ( ps -> ch ) ) $.
	p_alimd $p |- ( ph -> ( A. x ps -> A. x ch ) ) $= e0_alimd f0_alimd f3_alimd p_nfri e1_alimd f0_alimd f1_alimd f2_alimd f3_alimd p_alimdh $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_alrimi $f wff ph $.
	f1_alrimi $f wff ps $.
	f2_alrimi $f set x $.
	e0_alrimi $e |- F/ x ph $.
	e1_alrimi $e |- ( ph -> ps ) $.
	p_alrimi $p |- ( ph -> A. x ps ) $= e0_alrimi f0_alrimi f2_alrimi p_nfri e1_alrimi f0_alrimi f1_alrimi f2_alrimi p_alrimih $.
$}

$(Deduce that ` x ` is not free in ` ph ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_nfd $f wff ph $.
	f1_nfd $f wff ps $.
	f2_nfd $f set x $.
	e0_nfd $e |- F/ x ph $.
	e1_nfd $e |- ( ph -> ( ps -> A. x ps ) ) $.
	p_nfd $p |- ( ph -> F/ x ps ) $= e0_nfd e1_nfd f0_nfd f1_nfd f1_nfd f2_nfd a_wal a_wi f2_nfd p_alrimi f1_nfd f2_nfd a_df-nf f0_nfd f1_nfd f1_nfd f2_nfd a_wal a_wi f2_nfd a_wal f1_nfd f2_nfd a_wnf p_sylibr $.
$}

$(Deduce that ` x ` is not free in ` ph ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_nfdh $f wff ph $.
	f1_nfdh $f wff ps $.
	f2_nfdh $f set x $.
	e0_nfdh $e |- ( ph -> A. x ph ) $.
	e1_nfdh $e |- ( ph -> ( ps -> A. x ps ) ) $.
	p_nfdh $p |- ( ph -> F/ x ps ) $= e0_nfdh f0_nfdh f2_nfdh p_nfi e1_nfdh f0_nfdh f1_nfdh f2_nfdh p_nfd $.
$}

$(Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_alrimdd $f wff ph $.
	f1_alrimdd $f wff ps $.
	f2_alrimdd $f wff ch $.
	f3_alrimdd $f set x $.
	e0_alrimdd $e |- F/ x ph $.
	e1_alrimdd $e |- ( ph -> F/ x ps ) $.
	e2_alrimdd $e |- ( ph -> ( ps -> ch ) ) $.
	p_alrimdd $p |- ( ph -> ( ps -> A. x ch ) ) $= e1_alrimdd f0_alrimdd f1_alrimdd f3_alrimdd p_nfrd e0_alrimdd e2_alrimdd f0_alrimdd f1_alrimdd f2_alrimdd f3_alrimdd p_alimd f0_alrimdd f1_alrimdd f1_alrimdd f3_alrimdd a_wal f2_alrimdd f3_alrimdd a_wal p_syld $.
$}

$(Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_alrimd $f wff ph $.
	f1_alrimd $f wff ps $.
	f2_alrimd $f wff ch $.
	f3_alrimd $f set x $.
	e0_alrimd $e |- F/ x ph $.
	e1_alrimd $e |- F/ x ps $.
	e2_alrimd $e |- ( ph -> ( ps -> ch ) ) $.
	p_alrimd $p |- ( ph -> ( ps -> A. x ch ) ) $= e0_alrimd e1_alrimd f1_alrimd f3_alrimd a_wnf f0_alrimd p_a1i e2_alrimd f0_alrimd f1_alrimd f2_alrimd f3_alrimd p_alrimdd $.
$}

$(Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_eximd $f wff ph $.
	f1_eximd $f wff ps $.
	f2_eximd $f wff ch $.
	f3_eximd $f set x $.
	e0_eximd $e |- F/ x ph $.
	e1_eximd $e |- ( ph -> ( ps -> ch ) ) $.
	p_eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $= e0_eximd f0_eximd f3_eximd p_nfri e1_eximd f0_eximd f1_eximd f2_eximd f3_eximd p_eximdh $.
$}

$(Deduction for generalization rule for negated wff.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_nexd $f wff ph $.
	f1_nexd $f wff ps $.
	f2_nexd $f set x $.
	e0_nexd $e |- F/ x ph $.
	e1_nexd $e |- ( ph -> -. ps ) $.
	p_nexd $p |- ( ph -> -. E. x ps ) $= e0_nexd f0_nexd f2_nexd p_nfri e1_nexd f0_nexd f1_nexd f2_nexd p_nexdh $.
$}

$(Formula-building rule for universal quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_albid $f wff ph $.
	f1_albid $f wff ps $.
	f2_albid $f wff ch $.
	f3_albid $f set x $.
	e0_albid $e |- F/ x ph $.
	e1_albid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $= e0_albid f0_albid f3_albid p_nfri e1_albid f0_albid f1_albid f2_albid f3_albid p_albidh $.
$}

$(Formula-building rule for existential quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_exbid $f wff ph $.
	f1_exbid $f wff ps $.
	f2_exbid $f wff ch $.
	f3_exbid $f set x $.
	e0_exbid $e |- F/ x ph $.
	e1_exbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $= e0_exbid f0_exbid f3_exbid p_nfri e1_exbid f0_exbid f1_exbid f2_exbid f3_exbid p_exbidh $.
$}

$(An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 4-Oct-2016.) $)

${
	$v ph ps ch x  $.
	f0_nfbidf $f wff ph $.
	f1_nfbidf $f wff ps $.
	f2_nfbidf $f wff ch $.
	f3_nfbidf $f set x $.
	e0_nfbidf $e |- F/ x ph $.
	e1_nfbidf $e |- ( ph -> ( ps <-> ch ) ) $.
	p_nfbidf $p |- ( ph -> ( F/ x ps <-> F/ x ch ) ) $= e0_nfbidf e1_nfbidf e0_nfbidf e1_nfbidf f0_nfbidf f1_nfbidf f2_nfbidf f3_nfbidf p_albid f0_nfbidf f1_nfbidf f2_nfbidf f1_nfbidf f3_nfbidf a_wal f2_nfbidf f3_nfbidf a_wal p_imbi12d f0_nfbidf f1_nfbidf f1_nfbidf f3_nfbidf a_wal a_wi f2_nfbidf f2_nfbidf f3_nfbidf a_wal a_wi f3_nfbidf p_albid f1_nfbidf f3_nfbidf a_df-nf f2_nfbidf f3_nfbidf a_df-nf f0_nfbidf f1_nfbidf f1_nfbidf f3_nfbidf a_wal a_wi f3_nfbidf a_wal f2_nfbidf f2_nfbidf f3_nfbidf a_wal a_wi f3_nfbidf a_wal f1_nfbidf f3_nfbidf a_wnf f2_nfbidf f3_nfbidf a_wnf p_3bitr4g $.
$}

$(Abbreviated version of ~ ax6o .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_a6e $f wff ph $.
	f1_a6e $f set x $.
	p_a6e $p |- ( E. x A. x ph -> ph ) $= f0_a6e f1_a6e a_wal f1_a6e a_df-ex f0_a6e f1_a6e p_ax6o f0_a6e f1_a6e a_wal f1_a6e a_wex f0_a6e f1_a6e a_wal a_wn f1_a6e a_wal a_wn f0_a6e p_sylbi $.
$}

$(` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)

${
	$v ph x  $.
	f0_nfa1 $f wff ph $.
	f1_nfa1 $f set x $.
	p_nfa1 $p |- F/ x A. x ph $= f0_nfa1 f1_nfa1 p_hba1 f0_nfa1 f1_nfa1 a_wal f1_nfa1 p_nfi $.
$}

$(` x ` is not free in ` F/ x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)

${
	$v ph x  $.
	f0_nfnf1 $f wff ph $.
	f1_nfnf1 $f set x $.
	p_nfnf1 $p |- F/ x F/ x ph $= f0_nfnf1 f1_nfnf1 a_df-nf f0_nfnf1 f0_nfnf1 f1_nfnf1 a_wal a_wi f1_nfnf1 p_nfa1 f0_nfnf1 f1_nfnf1 a_wnf f0_nfnf1 f0_nfnf1 f1_nfnf1 a_wal a_wi f1_nfnf1 a_wal f1_nfnf1 p_nfxfr $.
$}

$(Inference version of ~ ax5o .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_a5i $f wff ph $.
	f1_a5i $f wff ps $.
	f2_a5i $f set x $.
	e0_a5i $e |- ( A. x ph -> ps ) $.
	p_a5i $p |- ( A. x ph -> A. x ps ) $= f0_a5i f2_a5i p_nfa1 e0_a5i f0_a5i f2_a5i a_wal f1_a5i f2_a5i p_alrimi $.
$}

$(If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by NM, 14-Sep-2003.) $)

${
	$v ph ps ch x  $.
	f0_hb3an $f wff ph $.
	f1_hb3an $f wff ps $.
	f2_hb3an $f wff ch $.
	f3_hb3an $f set x $.
	e0_hb3an $e |- ( ph -> A. x ph ) $.
	e1_hb3an $e |- ( ps -> A. x ps ) $.
	e2_hb3an $e |- ( ch -> A. x ch ) $.
	p_hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $= f0_hb3an f1_hb3an f2_hb3an a_df-3an e0_hb3an e1_hb3an f0_hb3an f1_hb3an f3_hb3an p_hban e2_hb3an f0_hb3an f1_hb3an a_wa f2_hb3an f3_hb3an p_hban f0_hb3an f1_hb3an f2_hb3an a_w3a f0_hb3an f1_hb3an a_wa f2_hb3an a_wa f3_hb3an p_hbxfrbi $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_nfnd $f wff ph $.
	f1_nfnd $f wff ps $.
	f2_nfnd $f set x $.
	e0_nfnd $e |- ( ph -> F/ x ps ) $.
	p_nfnd $p |- ( ph -> F/ x -. ps ) $= e0_nfnd f1_nfnd f2_nfnd p_nfnf1 f1_nfnd f2_nfnd p_ax6o f1_nfnd f2_nfnd a_wal a_wn f2_nfnd a_wal f1_nfnd p_con1i f1_nfnd f2_nfnd a_df-nf f1_nfnd f1_nfnd f2_nfnd a_wal p_con3 f1_nfnd f1_nfnd f2_nfnd a_wal a_wi f1_nfnd f2_nfnd a_wal a_wn f1_nfnd a_wn f2_nfnd p_al2imi f1_nfnd f2_nfnd a_wnf f1_nfnd f1_nfnd f2_nfnd a_wal a_wi f2_nfnd a_wal f1_nfnd f2_nfnd a_wal a_wn f2_nfnd a_wal f1_nfnd a_wn f2_nfnd a_wal a_wi p_sylbi f1_nfnd a_wn f1_nfnd f2_nfnd a_wal a_wn f2_nfnd a_wal f1_nfnd f2_nfnd a_wnf f1_nfnd a_wn f2_nfnd a_wal p_syl5 f1_nfnd f2_nfnd a_wnf f1_nfnd a_wn f2_nfnd p_nfd f0_nfnd f1_nfnd f2_nfnd a_wnf f1_nfnd a_wn f2_nfnd a_wnf p_syl $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_nfimd $f wff ph $.
	f1_nfimd $f wff ps $.
	f2_nfimd $f wff ch $.
	f3_nfimd $f set x $.
	e0_nfimd $e |- ( ph -> F/ x ps ) $.
	e1_nfimd $e |- ( ph -> F/ x ch ) $.
	p_nfimd $p |- ( ph -> F/ x ( ps -> ch ) ) $= e0_nfimd e1_nfimd f1_nfimd f1_nfimd f3_nfimd a_wal a_wi f3_nfimd p_nfa1 f1_nfimd f3_nfimd p_hbnt f1_nfimd f2_nfimd p_pm2.21 f1_nfimd a_wn f1_nfimd f2_nfimd a_wi f3_nfimd p_alimi f1_nfimd a_wn f3_nfimd a_wal f1_nfimd f2_nfimd a_wi f3_nfimd a_wal f1_nfimd a_wn p_imim2i f1_nfimd a_wn f1_nfimd a_wn f3_nfimd a_wal a_wi f1_nfimd a_wn f1_nfimd f2_nfimd a_wi f3_nfimd a_wal a_wi f2_nfimd f2_nfimd f3_nfimd a_wal a_wi p_adantr f2_nfimd f1_nfimd a_ax-1 f2_nfimd f1_nfimd f2_nfimd a_wi f3_nfimd p_alimi f2_nfimd f3_nfimd a_wal f1_nfimd f2_nfimd a_wi f3_nfimd a_wal f2_nfimd p_imim2i f2_nfimd f2_nfimd f3_nfimd a_wal a_wi f2_nfimd f1_nfimd f2_nfimd a_wi f3_nfimd a_wal a_wi f1_nfimd a_wn f1_nfimd a_wn f3_nfimd a_wal a_wi p_adantl f1_nfimd a_wn f1_nfimd a_wn f3_nfimd a_wal a_wi f2_nfimd f2_nfimd f3_nfimd a_wal a_wi a_wa f1_nfimd f2_nfimd f1_nfimd f2_nfimd a_wi f3_nfimd a_wal p_jad f1_nfimd a_wn f1_nfimd a_wn f3_nfimd a_wal a_wi f2_nfimd f2_nfimd f3_nfimd a_wal a_wi f1_nfimd f2_nfimd a_wi f1_nfimd f2_nfimd a_wi f3_nfimd a_wal a_wi p_ex f1_nfimd f1_nfimd f3_nfimd a_wal a_wi f3_nfimd a_wal f1_nfimd a_wn f1_nfimd a_wn f3_nfimd a_wal a_wi f2_nfimd f2_nfimd f3_nfimd a_wal a_wi f1_nfimd f2_nfimd a_wi f1_nfimd f2_nfimd a_wi f3_nfimd a_wal a_wi a_wi p_syl f1_nfimd f1_nfimd f3_nfimd a_wal a_wi f3_nfimd a_wal f2_nfimd f2_nfimd f3_nfimd a_wal a_wi f1_nfimd f2_nfimd a_wi f1_nfimd f2_nfimd a_wi f3_nfimd a_wal a_wi f3_nfimd p_alimd f1_nfimd f1_nfimd f3_nfimd a_wal a_wi f3_nfimd a_wal f2_nfimd f2_nfimd f3_nfimd a_wal a_wi f3_nfimd a_wal f1_nfimd f2_nfimd a_wi f1_nfimd f2_nfimd a_wi f3_nfimd a_wal a_wi f3_nfimd a_wal p_imp f1_nfimd f3_nfimd a_df-nf f2_nfimd f3_nfimd a_df-nf f1_nfimd f3_nfimd a_wnf f1_nfimd f1_nfimd f3_nfimd a_wal a_wi f3_nfimd a_wal f2_nfimd f3_nfimd a_wnf f2_nfimd f2_nfimd f3_nfimd a_wal a_wi f3_nfimd a_wal p_anbi12i f1_nfimd f2_nfimd a_wi f3_nfimd a_df-nf f1_nfimd f1_nfimd f3_nfimd a_wal a_wi f3_nfimd a_wal f2_nfimd f2_nfimd f3_nfimd a_wal a_wi f3_nfimd a_wal a_wa f1_nfimd f2_nfimd a_wi f1_nfimd f2_nfimd a_wi f3_nfimd a_wal a_wi f3_nfimd a_wal f1_nfimd f3_nfimd a_wnf f2_nfimd f3_nfimd a_wnf a_wa f1_nfimd f2_nfimd a_wi f3_nfimd a_wnf p_3imtr4i f0_nfimd f1_nfimd f3_nfimd a_wnf f2_nfimd f3_nfimd a_wnf f1_nfimd f2_nfimd a_wi f3_nfimd a_wnf p_syl2anc $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_nfbid $f wff ph $.
	f1_nfbid $f wff ps $.
	f2_nfbid $f wff ch $.
	f3_nfbid $f set x $.
	e0_nfbid $e |- ( ph -> F/ x ps ) $.
	e1_nfbid $e |- ( ph -> F/ x ch ) $.
	p_nfbid $p |- ( ph -> F/ x ( ps <-> ch ) ) $= f1_nfbid f2_nfbid p_dfbi1 e0_nfbid e1_nfbid f0_nfbid f1_nfbid f2_nfbid f3_nfbid p_nfimd e1_nfbid e0_nfbid f0_nfbid f2_nfbid f1_nfbid f3_nfbid p_nfimd f0_nfbid f2_nfbid f1_nfbid a_wi f3_nfbid p_nfnd f0_nfbid f1_nfbid f2_nfbid a_wi f2_nfbid f1_nfbid a_wi a_wn f3_nfbid p_nfimd f0_nfbid f1_nfbid f2_nfbid a_wi f2_nfbid f1_nfbid a_wi a_wn a_wi f3_nfbid p_nfnd f1_nfbid f2_nfbid a_wb f1_nfbid f2_nfbid a_wi f2_nfbid f1_nfbid a_wi a_wn a_wi a_wn f0_nfbid f3_nfbid p_nfxfrd $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph ps ch x  $.
	f0_nfand $f wff ph $.
	f1_nfand $f wff ps $.
	f2_nfand $f wff ch $.
	f3_nfand $f set x $.
	e0_nfand $e |- ( ph -> F/ x ps ) $.
	e1_nfand $e |- ( ph -> F/ x ch ) $.
	p_nfand $p |- ( ph -> F/ x ( ps /\ ch ) ) $= f1_nfand f2_nfand a_df-an e0_nfand e1_nfand f0_nfand f2_nfand f3_nfand p_nfnd f0_nfand f1_nfand f2_nfand a_wn f3_nfand p_nfimd f0_nfand f1_nfand f2_nfand a_wn a_wi f3_nfand p_nfnd f1_nfand f2_nfand a_wa f1_nfand f2_nfand a_wn a_wi a_wn f0_nfand f3_nfand p_nfxfrd $.
$}

$(Deduction form of bound-variable hypothesis builder ~ nf3an .
       (Contributed by NM, 17-Feb-2013.)  (Revised by Mario Carneiro,
       16-Oct-2016.) $)

${
	$v ph ps ch th x  $.
	f0_nf3and $f wff ph $.
	f1_nf3and $f wff ps $.
	f2_nf3and $f wff ch $.
	f3_nf3and $f wff th $.
	f4_nf3and $f set x $.
	e0_nf3and $e |- ( ph -> F/ x ps ) $.
	e1_nf3and $e |- ( ph -> F/ x ch ) $.
	e2_nf3and $e |- ( ph -> F/ x th ) $.
	p_nf3and $p |- ( ph -> F/ x ( ps /\ ch /\ th ) ) $= f1_nf3and f2_nf3and f3_nf3and a_df-3an e0_nf3and e1_nf3and f0_nf3and f1_nf3and f2_nf3and f4_nf3and p_nfand e2_nf3and f0_nf3and f1_nf3and f2_nf3and a_wa f3_nf3and f4_nf3and p_nfand f1_nf3and f2_nf3and f3_nf3and a_w3a f1_nf3and f2_nf3and a_wa f3_nf3and a_wa f0_nf3and f4_nf3and p_nfxfrd $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x  $.
	f0_nfn $f wff ph $.
	f1_nfn $f set x $.
	e0_nfn $e |- F/ x ph $.
	p_nfn $p |- F/ x -. ph $= e0_nfn f0_nfn f1_nfn a_wnf a_wtru p_a1i a_wtru f0_nfn f1_nfn p_nfnd f0_nfn a_wn f1_nfn a_wnf p_trud $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_nfal $f wff ph $.
	f1_nfal $f set x $.
	f2_nfal $f set y $.
	e0_nfal $e |- F/ x ph $.
	p_nfal $p |- F/ x A. y ph $= e0_nfal f0_nfal f1_nfal p_nfri f0_nfal f1_nfal f2_nfal p_hbal f0_nfal f2_nfal a_wal f1_nfal p_nfi $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_nfex $f wff ph $.
	f1_nfex $f set x $.
	f2_nfex $f set y $.
	e0_nfex $e |- F/ x ph $.
	p_nfex $p |- F/ x E. y ph $= f0_nfex f2_nfex a_df-ex e0_nfex f0_nfex f1_nfex p_nfn f0_nfex a_wn f1_nfex f2_nfex p_nfal f0_nfex a_wn f2_nfex a_wal f1_nfex p_nfn f0_nfex f2_nfex a_wex f0_nfex a_wn f2_nfex a_wal a_wn f1_nfex p_nfxfr $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` F/ y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph x y  $.
	f0_nfnf $f wff ph $.
	f1_nfnf $f set x $.
	f2_nfnf $f set y $.
	e0_nfnf $e |- F/ x ph $.
	p_nfnf $p |- F/ x F/ y ph $= f0_nfnf f2_nfnf a_df-nf e0_nfnf f0_nfnf f1_nfnf a_wnf a_wtru p_a1i e0_nfnf f0_nfnf f1_nfnf f2_nfnf p_nfal f0_nfnf f2_nfnf a_wal f1_nfnf a_wnf a_wtru p_a1i a_wtru f0_nfnf f0_nfnf f2_nfnf a_wal f1_nfnf p_nfimd f0_nfnf f0_nfnf f2_nfnf a_wal a_wi f1_nfnf a_wnf p_trud f0_nfnf f0_nfnf f2_nfnf a_wal a_wi f1_nfnf f2_nfnf p_nfal f0_nfnf f2_nfnf a_wnf f0_nfnf f0_nfnf f2_nfnf a_wal a_wi f2_nfnf a_wal f1_nfnf p_nfxfr $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x  $.
	f0_nfim $f wff ph $.
	f1_nfim $f wff ps $.
	f2_nfim $f set x $.
	e0_nfim $e |- F/ x ph $.
	e1_nfim $e |- F/ x ps $.
	p_nfim $p |- F/ x ( ph -> ps ) $= e0_nfim f0_nfim f2_nfim a_wnf a_wtru p_a1i e1_nfim f1_nfim f2_nfim a_wnf a_wtru p_a1i a_wtru f0_nfim f1_nfim f2_nfim p_nfimd f0_nfim f1_nfim a_wi f2_nfim a_wnf p_trud $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph \/ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x  $.
	f0_nfor $f wff ph $.
	f1_nfor $f wff ps $.
	f2_nfor $f set x $.
	e0_nfor $e |- F/ x ph $.
	e1_nfor $e |- F/ x ps $.
	p_nfor $p |- F/ x ( ph \/ ps ) $= f0_nfor f1_nfor a_df-or e0_nfor f0_nfor f2_nfor p_nfn e1_nfor f0_nfor a_wn f1_nfor f2_nfor p_nfim f0_nfor f1_nfor a_wo f0_nfor a_wn f1_nfor a_wi f2_nfor p_nfxfr $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x  $.
	f0_nfan $f wff ph $.
	f1_nfan $f wff ps $.
	f2_nfan $f set x $.
	e0_nfan $e |- F/ x ph $.
	e1_nfan $e |- F/ x ps $.
	p_nfan $p |- F/ x ( ph /\ ps ) $= f0_nfan f1_nfan a_df-an e0_nfan e1_nfan f1_nfan f2_nfan p_nfn f0_nfan f1_nfan a_wn f2_nfan p_nfim f0_nfan f1_nfan a_wn a_wi f2_nfan p_nfn f0_nfan f1_nfan a_wa f0_nfan f1_nfan a_wn a_wi a_wn f2_nfan p_nfxfr $.
$}

$(If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)

${
	$v ph ps x  $.
	f0_nfbi $f wff ph $.
	f1_nfbi $f wff ps $.
	f2_nfbi $f set x $.
	e0_nfbi $e |- F/ x ph $.
	e1_nfbi $e |- F/ x ps $.
	p_nfbi $p |- F/ x ( ph <-> ps ) $= f0_nfbi f1_nfbi p_dfbi2 e0_nfbi e1_nfbi f0_nfbi f1_nfbi f2_nfbi p_nfim e1_nfbi e0_nfbi f1_nfbi f0_nfbi f2_nfbi p_nfim f0_nfbi f1_nfbi a_wi f1_nfbi f0_nfbi a_wi f2_nfbi p_nfan f0_nfbi f1_nfbi a_wb f0_nfbi f1_nfbi a_wi f1_nfbi f0_nfbi a_wi a_wa f2_nfbi p_nfxfr $.
$}

$(If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph \/ ps \/ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_nf3or $f wff ph $.
	f1_nf3or $f wff ps $.
	f2_nf3or $f wff ch $.
	f3_nf3or $f set x $.
	e0_nf3or $e |- F/ x ph $.
	e1_nf3or $e |- F/ x ps $.
	e2_nf3or $e |- F/ x ch $.
	p_nf3or $p |- F/ x ( ph \/ ps \/ ch ) $= f0_nf3or f1_nf3or f2_nf3or a_df-3or e0_nf3or e1_nf3or f0_nf3or f1_nf3or f3_nf3or p_nfor e2_nf3or f0_nf3or f1_nf3or a_wo f2_nf3or f3_nf3or p_nfor f0_nf3or f1_nf3or f2_nf3or a_w3o f0_nf3or f1_nf3or a_wo f2_nf3or a_wo f3_nf3or p_nfxfr $.
$}

$(If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)

${
	$v ph ps ch x  $.
	f0_nf3an $f wff ph $.
	f1_nf3an $f wff ps $.
	f2_nf3an $f wff ch $.
	f3_nf3an $f set x $.
	e0_nf3an $e |- F/ x ph $.
	e1_nf3an $e |- F/ x ps $.
	e2_nf3an $e |- F/ x ch $.
	p_nf3an $p |- F/ x ( ph /\ ps /\ ch ) $= f0_nf3an f1_nf3an f2_nf3an a_df-3an e0_nf3an e1_nf3an f0_nf3an f1_nf3an f3_nf3an p_nfan e2_nf3an f0_nf3an f1_nf3an a_wa f2_nf3an f3_nf3an p_nfan f0_nf3an f1_nf3an f2_nf3an a_w3a f0_nf3an f1_nf3an a_wa f2_nf3an a_wa f3_nf3an p_nfxfr $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x y  $.
	f0_nfald $f wff ph $.
	f1_nfald $f wff ps $.
	f2_nfald $f set x $.
	f3_nfald $f set y $.
	e0_nfald $e |- F/ y ph $.
	e1_nfald $e |- ( ph -> F/ x ps ) $.
	p_nfald $p |- ( ph -> F/ x A. y ps ) $= e0_nfald e1_nfald f0_nfald f1_nfald f2_nfald a_wnf f3_nfald p_alrimi f1_nfald f2_nfald p_nfnf1 f1_nfald f2_nfald a_wnf f2_nfald f3_nfald p_nfal f1_nfald f2_nfald p_nfr f1_nfald f2_nfald a_wnf f1_nfald f1_nfald f2_nfald a_wal f3_nfald p_al2imi f1_nfald f3_nfald f2_nfald a_ax-7 f1_nfald f2_nfald a_wnf f3_nfald a_wal f1_nfald f3_nfald a_wal f1_nfald f2_nfald a_wal f3_nfald a_wal f1_nfald f3_nfald a_wal f2_nfald a_wal p_syl6 f1_nfald f2_nfald a_wnf f3_nfald a_wal f1_nfald f3_nfald a_wal f2_nfald p_nfd f0_nfald f1_nfald f2_nfald a_wnf f3_nfald a_wal f1_nfald f3_nfald a_wal f2_nfald a_wnf p_syl $.
$}

$(If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x y  $.
	f0_nfexd $f wff ph $.
	f1_nfexd $f wff ps $.
	f2_nfexd $f set x $.
	f3_nfexd $f set y $.
	e0_nfexd $e |- F/ y ph $.
	e1_nfexd $e |- ( ph -> F/ x ps ) $.
	p_nfexd $p |- ( ph -> F/ x E. y ps ) $= f1_nfexd f3_nfexd a_df-ex e0_nfexd e1_nfexd f0_nfexd f1_nfexd f2_nfexd p_nfnd f0_nfexd f1_nfexd a_wn f2_nfexd f3_nfexd p_nfald f0_nfexd f1_nfexd a_wn f3_nfexd a_wal f2_nfexd p_nfnd f1_nfexd f3_nfexd a_wex f1_nfexd a_wn f3_nfexd a_wal a_wn f0_nfexd f2_nfexd p_nfxfrd $.
$}

$(Lemma 24 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)

${
	$v ph x y  $.
	f0_nfa2 $f wff ph $.
	f1_nfa2 $f set x $.
	f2_nfa2 $f set y $.
	p_nfa2 $p |- F/ x A. y A. x ph $= f0_nfa2 f1_nfa2 p_nfa1 f0_nfa2 f1_nfa2 a_wal f1_nfa2 f2_nfa2 p_nfal $.
$}

$(Lemma 23 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_nfia1 $f wff ph $.
	f1_nfia1 $f wff ps $.
	f2_nfia1 $f set x $.
	p_nfia1 $p |- F/ x ( A. x ph -> A. x ps ) $= f0_nfia1 f2_nfia1 p_nfa1 f1_nfia1 f2_nfia1 p_nfa1 f0_nfia1 f2_nfia1 a_wal f1_nfia1 f2_nfia1 a_wal f2_nfia1 p_nfim $.
$}

$(The analog in our "pure" predicate calculus of the Brouwer axiom (B) of
     modal logic S5.  (Contributed by NM, 5-Oct-2005.) $)

${
	$v ph x  $.
	f0_modal-b $f wff ph $.
	f1_modal-b $f set x $.
	p_modal-b $p |- ( ph -> A. x -. A. x -. ph ) $= f0_modal-b a_wn f1_modal-b p_ax6o f0_modal-b a_wn f1_modal-b a_wal a_wn f1_modal-b a_wal f0_modal-b p_con4i $.
$}

$(Theorem 19.2 of [Margaris] p. 89, generalized to use two set variables.
     (Contributed by O'Cat, 31-Mar-2008.) $)

${
	$v ph x y  $.
	f0_19.2g $f wff ph $.
	f1_19.2g $f set x $.
	f2_19.2g $f set y $.
	p_19.2g $p |- ( A. x ph -> E. y ph ) $= f0_19.2g f2_19.2g p_19.8a f0_19.2g f0_19.2g f2_19.2g a_wex f1_19.2g p_sps $.
$}

$(A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)

${
	$v ph x  $.
	f0_19.3 $f wff ph $.
	f1_19.3 $f set x $.
	e0_19.3 $e |- F/ x ph $.
	p_19.3 $p |- ( A. x ph <-> ph ) $= f0_19.3 f1_19.3 p_sp e0_19.3 f0_19.3 f1_19.3 p_nfri f0_19.3 f1_19.3 a_wal f0_19.3 p_impbii $.
$}

$(A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.)  (Revised
     by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph x  $.
	f0_19.9t $f wff ph $.
	f1_19.9t $f set x $.
	p_19.9t $p |- ( F/ x ph -> ( E. x ph <-> ph ) ) $= f0_19.9t f1_19.9t a_df-ex f0_19.9t f1_19.9t a_wnf p_id f0_19.9t f1_19.9t a_wnf f0_19.9t f1_19.9t p_nfnd f0_19.9t f1_19.9t a_wnf f0_19.9t a_wn f1_19.9t p_nfrd f0_19.9t f1_19.9t a_wnf f0_19.9t f0_19.9t a_wn f1_19.9t a_wal p_con1d f0_19.9t f1_19.9t a_wex f0_19.9t a_wn f1_19.9t a_wal a_wn f0_19.9t f1_19.9t a_wnf f0_19.9t p_syl5bi f0_19.9t f1_19.9t p_19.8a f0_19.9t f1_19.9t a_wnf f0_19.9t f1_19.9t a_wex f0_19.9t p_impbid1 $.
$}

$(A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph x  $.
	f0_19.9 $f wff ph $.
	f1_19.9 $f set x $.
	e0_19.9 $e |- F/ x ph $.
	p_19.9 $p |- ( E. x ph <-> ph ) $= e0_19.9 f0_19.9 f1_19.9 p_19.9t f0_19.9 f1_19.9 a_wnf f0_19.9 f1_19.9 a_wex f0_19.9 a_wb a_ax-mp $.
$}

$(A deduction version of one direction of ~ 19.9 .  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_19.9d $f wff ph $.
	f1_19.9d $f wff ps $.
	f2_19.9d $f set x $.
	e0_19.9d $e |- ( ps -> F/ x ph ) $.
	p_19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $= e0_19.9d f0_19.9d f2_19.9d p_19.9t f1_19.9d f0_19.9d f2_19.9d a_wnf f0_19.9d f2_19.9d a_wex f0_19.9d a_wb p_syl f1_19.9d f0_19.9d f2_19.9d a_wex f0_19.9d p_biimpd $.
$}

$(One direction of Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM,
     5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph x y  $.
	f0_excomim $f wff ph $.
	f1_excomim $f set x $.
	f2_excomim $f set y $.
	p_excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $= f0_excomim f1_excomim p_19.8a f0_excomim f0_excomim f1_excomim a_wex f1_excomim f2_excomim p_2eximi f0_excomim f1_excomim p_nfe1 f0_excomim f1_excomim a_wex f1_excomim f2_excomim p_nfex f0_excomim f1_excomim a_wex f2_excomim a_wex f1_excomim p_19.9 f0_excomim f2_excomim a_wex f1_excomim a_wex f0_excomim f1_excomim a_wex f2_excomim a_wex f1_excomim a_wex f0_excomim f1_excomim a_wex f2_excomim a_wex p_sylib $.
$}

$(Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_excom $f wff ph $.
	f1_excom $f set x $.
	f2_excom $f set y $.
	p_excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $= f0_excom f1_excom f2_excom p_excomim f0_excom f2_excom f1_excom p_excomim f0_excom f2_excom a_wex f1_excom a_wex f0_excom f1_excom a_wex f2_excom a_wex p_impbii $.
$}

$(Theorem 19.16 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.16 $f wff ph $.
	f1_19.16 $f wff ps $.
	f2_19.16 $f set x $.
	e0_19.16 $e |- F/ x ph $.
	p_19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $= e0_19.16 f0_19.16 f2_19.16 p_19.3 f0_19.16 f1_19.16 f2_19.16 p_albi f0_19.16 f0_19.16 f2_19.16 a_wal f0_19.16 f1_19.16 a_wb f2_19.16 a_wal f1_19.16 f2_19.16 a_wal p_syl5bbr $.
$}

$(Theorem 19.17 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.17 $f wff ph $.
	f1_19.17 $f wff ps $.
	f2_19.17 $f set x $.
	e0_19.17 $e |- F/ x ps $.
	p_19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $= f0_19.17 f1_19.17 f2_19.17 p_albi e0_19.17 f1_19.17 f2_19.17 p_19.3 f0_19.17 f1_19.17 a_wb f2_19.17 a_wal f0_19.17 f2_19.17 a_wal f1_19.17 f2_19.17 a_wal f1_19.17 p_syl6bb $.
$}

$(Theorem 19.19 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.19 $f wff ph $.
	f1_19.19 $f wff ps $.
	f2_19.19 $f set x $.
	e0_19.19 $e |- F/ x ph $.
	p_19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $= e0_19.19 f0_19.19 f2_19.19 p_19.9 f0_19.19 f1_19.19 f2_19.19 p_exbi f0_19.19 f0_19.19 f2_19.19 a_wex f0_19.19 f1_19.19 a_wb f2_19.19 a_wal f1_19.19 f2_19.19 a_wex p_syl5bbr $.
$}

$(Closed form of Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
     27-May-1997.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_19.21t $f wff ph $.
	f1_19.21t $f wff ps $.
	f2_19.21t $f set x $.
	p_19.21t $p |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $= f0_19.21t f2_19.21t a_wnf p_id f0_19.21t f2_19.21t a_wnf f0_19.21t f2_19.21t p_nfrd f0_19.21t f1_19.21t f2_19.21t p_alim f0_19.21t f2_19.21t a_wnf f0_19.21t f0_19.21t f2_19.21t a_wal f0_19.21t f1_19.21t a_wi f2_19.21t a_wal f1_19.21t f2_19.21t a_wal p_syl9 f0_19.21t f2_19.21t a_wnf p_id f1_19.21t f2_19.21t p_nfa1 f1_19.21t f2_19.21t a_wal f2_19.21t a_wnf f0_19.21t f2_19.21t a_wnf p_a1i f0_19.21t f2_19.21t a_wnf f0_19.21t f1_19.21t f2_19.21t a_wal f2_19.21t p_nfimd f0_19.21t f2_19.21t a_wnf f0_19.21t f1_19.21t f2_19.21t a_wal a_wi f2_19.21t p_nfrd f1_19.21t f2_19.21t p_sp f1_19.21t f2_19.21t a_wal f1_19.21t f0_19.21t p_imim2i f0_19.21t f1_19.21t f2_19.21t a_wal a_wi f0_19.21t f1_19.21t a_wi f2_19.21t p_alimi f0_19.21t f2_19.21t a_wnf f0_19.21t f1_19.21t f2_19.21t a_wal a_wi f0_19.21t f1_19.21t f2_19.21t a_wal a_wi f2_19.21t a_wal f0_19.21t f1_19.21t a_wi f2_19.21t a_wal p_syl6 f0_19.21t f2_19.21t a_wnf f0_19.21t f1_19.21t a_wi f2_19.21t a_wal f0_19.21t f1_19.21t f2_19.21t a_wal a_wi p_impbid $.
$}

$(Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ."  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_19.21 $f wff ph $.
	f1_19.21 $f wff ps $.
	f2_19.21 $f set x $.
	e0_19.21 $e |- F/ x ph $.
	p_19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $= e0_19.21 f0_19.21 f1_19.21 f2_19.21 p_19.21t f0_19.21 f2_19.21 a_wnf f0_19.21 f1_19.21 a_wi f2_19.21 a_wal f0_19.21 f1_19.21 f2_19.21 a_wal a_wi a_wb a_ax-mp $.
$}

$(Theorem 19.21 of [Margaris] p. 90 but with 2 quantifiers.  (Contributed
       by NM, 4-Feb-2005.) $)

${
	$v ph ps x y  $.
	f0_19.21-2 $f wff ph $.
	f1_19.21-2 $f wff ps $.
	f2_19.21-2 $f set x $.
	f3_19.21-2 $f set y $.
	e0_19.21-2 $e |- F/ x ph $.
	e1_19.21-2 $e |- F/ y ph $.
	p_19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $= e1_19.21-2 f0_19.21-2 f1_19.21-2 f3_19.21-2 p_19.21 f0_19.21-2 f1_19.21-2 a_wi f3_19.21-2 a_wal f0_19.21-2 f1_19.21-2 f3_19.21-2 a_wal a_wi f2_19.21-2 p_albii e0_19.21-2 f0_19.21-2 f1_19.21-2 f3_19.21-2 a_wal f2_19.21-2 p_19.21 f0_19.21-2 f1_19.21-2 a_wi f3_19.21-2 a_wal f2_19.21-2 a_wal f0_19.21-2 f1_19.21-2 f3_19.21-2 a_wal a_wi f2_19.21-2 a_wal f0_19.21-2 f1_19.21-2 f3_19.21-2 a_wal f2_19.21-2 a_wal a_wi p_bitri $.
$}

$(An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` F/ x ph ` can be thought of as
       emulating " ` x ` is not free in ` ph ` ."  With this definition, the
       meaning of "not free" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ nfequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5.  (Contributed by NM, 22-Sep-1993.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)

${
	$v ph ps x  $.
	f0_stdpc5 $f wff ph $.
	f1_stdpc5 $f wff ps $.
	f2_stdpc5 $f set x $.
	e0_stdpc5 $e |- F/ x ph $.
	p_stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $= e0_stdpc5 f0_stdpc5 f2_stdpc5 p_nfri f0_stdpc5 f1_stdpc5 f2_stdpc5 p_alim f0_stdpc5 f0_stdpc5 f2_stdpc5 a_wal f0_stdpc5 f1_stdpc5 a_wi f2_stdpc5 a_wal f1_stdpc5 f2_stdpc5 a_wal p_syl5 $.
$}

$(Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.21bi $f wff ph $.
	f1_19.21bi $f wff ps $.
	f2_19.21bi $f set x $.
	e0_19.21bi $e |- ( ph -> A. x ps ) $.
	p_19.21bi $p |- ( ph -> ps ) $= e0_19.21bi f1_19.21bi f2_19.21bi p_sp f0_19.21bi f1_19.21bi f2_19.21bi a_wal f1_19.21bi p_syl $.
$}

$(Inference removing double quantifier.  (Contributed by NM,
       20-Apr-1994.) $)

${
	$v ph ps x y  $.
	f0_19.21bbi $f wff ph $.
	f1_19.21bbi $f wff ps $.
	f2_19.21bbi $f set x $.
	f3_19.21bbi $f set y $.
	e0_19.21bbi $e |- ( ph -> A. x A. y ps ) $.
	p_19.21bbi $p |- ( ph -> ps ) $= e0_19.21bbi f0_19.21bbi f1_19.21bbi f3_19.21bbi a_wal f2_19.21bbi p_19.21bi f0_19.21bbi f1_19.21bbi f3_19.21bbi p_19.21bi $.
$}

$(Closed form of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
     7-Nov-2005.) $)

${
	$v ph ps x  $.
	f0_19.23t $f wff ph $.
	f1_19.23t $f wff ps $.
	f2_19.23t $f set x $.
	p_19.23t $p |- ( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $= f0_19.23t f1_19.23t f2_19.23t p_exim f1_19.23t f2_19.23t p_19.9t f1_19.23t f2_19.23t a_wnf f1_19.23t f2_19.23t a_wex f1_19.23t f0_19.23t f2_19.23t a_wex p_imbi2d f0_19.23t f1_19.23t a_wi f2_19.23t a_wal f0_19.23t f2_19.23t a_wex f1_19.23t f2_19.23t a_wex a_wi f1_19.23t f2_19.23t a_wnf f0_19.23t f2_19.23t a_wex f1_19.23t a_wi p_syl5ib f1_19.23t f2_19.23t p_nfnf1 f0_19.23t f2_19.23t p_nfe1 f0_19.23t f2_19.23t a_wex f2_19.23t a_wnf f1_19.23t f2_19.23t a_wnf p_a1i f1_19.23t f2_19.23t a_wnf p_id f1_19.23t f2_19.23t a_wnf f0_19.23t f2_19.23t a_wex f1_19.23t f2_19.23t p_nfimd f0_19.23t f2_19.23t p_19.8a f0_19.23t f0_19.23t f2_19.23t a_wex a_wi f1_19.23t f2_19.23t a_wnf p_a1i f1_19.23t f2_19.23t a_wnf f0_19.23t f0_19.23t f2_19.23t a_wex f1_19.23t p_imim1d f1_19.23t f2_19.23t a_wnf f0_19.23t f2_19.23t a_wex f1_19.23t a_wi f0_19.23t f1_19.23t a_wi f2_19.23t p_alrimdd f1_19.23t f2_19.23t a_wnf f0_19.23t f1_19.23t a_wi f2_19.23t a_wal f0_19.23t f2_19.23t a_wex f1_19.23t a_wi p_impbid $.
$}

$(Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_19.23 $f wff ph $.
	f1_19.23 $f wff ps $.
	f2_19.23 $f set x $.
	e0_19.23 $e |- F/ x ps $.
	p_19.23 $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $= e0_19.23 f0_19.23 f1_19.23 f2_19.23 p_19.23t f1_19.23 f2_19.23 a_wnf f0_19.23 f1_19.23 a_wi f2_19.23 a_wal f0_19.23 f2_19.23 a_wex f1_19.23 a_wi a_wb a_ax-mp $.
$}

$(An alternative definition of ~ df-nf , which does not involve nested
     quantifiers on the same variable.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)

${
	$v ph x  $.
	f0_nf2 $f wff ph $.
	f1_nf2 $f set x $.
	p_nf2 $p |- ( F/ x ph <-> ( E. x ph -> A. x ph ) ) $= f0_nf2 f1_nf2 a_df-nf f0_nf2 f1_nf2 p_nfa1 f0_nf2 f0_nf2 f1_nf2 a_wal f1_nf2 p_19.23 f0_nf2 f1_nf2 a_wnf f0_nf2 f0_nf2 f1_nf2 a_wal a_wi f1_nf2 a_wal f0_nf2 f1_nf2 a_wex f0_nf2 f1_nf2 a_wal a_wi p_bitri $.
$}

$(An alternative definition of ~ df-nf .  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)

${
	$v ph x  $.
	f0_nf3 $f wff ph $.
	f1_nf3 $f set x $.
	p_nf3 $p |- ( F/ x ph <-> A. x ( E. x ph -> ph ) ) $= f0_nf3 f1_nf3 p_nf2 f0_nf3 f1_nf3 p_nfe1 f0_nf3 f1_nf3 a_wex f0_nf3 f1_nf3 p_19.21 f0_nf3 f1_nf3 a_wnf f0_nf3 f1_nf3 a_wex f0_nf3 f1_nf3 a_wal a_wi f0_nf3 f1_nf3 a_wex f0_nf3 a_wi f1_nf3 a_wal p_bitr4i $.
$}

$(Variable ` x ` is effectively not free in ` ph ` iff ` ph ` is always true
     or always false.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph x  $.
	f0_nf4 $f wff ph $.
	f1_nf4 $f set x $.
	p_nf4 $p |- ( F/ x ph <-> ( A. x ph \/ A. x -. ph ) ) $= f0_nf4 f1_nf4 p_nf2 f0_nf4 f1_nf4 a_wex f0_nf4 f1_nf4 a_wal p_imor f0_nf4 f1_nf4 a_wex a_wn f0_nf4 f1_nf4 a_wal p_orcom f0_nf4 f1_nf4 p_alnex f0_nf4 a_wn f1_nf4 a_wal f0_nf4 f1_nf4 a_wex a_wn f0_nf4 f1_nf4 a_wal p_orbi2i f0_nf4 f1_nf4 a_wex a_wn f0_nf4 f1_nf4 a_wal a_wo f0_nf4 f1_nf4 a_wal f0_nf4 f1_nf4 a_wex a_wn a_wo f0_nf4 f1_nf4 a_wal f0_nf4 a_wn f1_nf4 a_wal a_wo p_bitr4i f0_nf4 f1_nf4 a_wnf f0_nf4 f1_nf4 a_wex f0_nf4 f1_nf4 a_wal a_wi f0_nf4 f1_nf4 a_wex a_wn f0_nf4 f1_nf4 a_wal a_wo f0_nf4 f1_nf4 a_wal f0_nf4 a_wn f1_nf4 a_wal a_wo p_3bitri $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_exlimi $f wff ph $.
	f1_exlimi $f wff ps $.
	f2_exlimi $f set x $.
	e0_exlimi $e |- F/ x ps $.
	e1_exlimi $e |- ( ph -> ps ) $.
	p_exlimi $p |- ( E. x ph -> ps ) $= e0_exlimi f0_exlimi f1_exlimi f2_exlimi p_19.23 e1_exlimi f0_exlimi f1_exlimi a_wi f0_exlimi f2_exlimi a_wex f1_exlimi a_wi f2_exlimi p_mpgbi $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.23bi $f wff ph $.
	f1_19.23bi $f wff ps $.
	f2_19.23bi $f set x $.
	e0_19.23bi $e |- ( E. x ph -> ps ) $.
	p_19.23bi $p |- ( ph -> ps ) $= f0_19.23bi f2_19.23bi p_19.8a e0_19.23bi f0_19.23bi f0_19.23bi f2_19.23bi a_wex f1_19.23bi p_syl $.
$}

$(Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)

${
	$v ph ps ch x  $.
	f0_exlimd $f wff ph $.
	f1_exlimd $f wff ps $.
	f2_exlimd $f wff ch $.
	f3_exlimd $f set x $.
	e0_exlimd $e |- F/ x ph $.
	e1_exlimd $e |- F/ x ch $.
	e2_exlimd $e |- ( ph -> ( ps -> ch ) ) $.
	p_exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $= e0_exlimd e2_exlimd f0_exlimd f1_exlimd f2_exlimd a_wi f3_exlimd p_alrimi e1_exlimd f1_exlimd f2_exlimd f3_exlimd p_19.23 f0_exlimd f1_exlimd f2_exlimd a_wi f3_exlimd a_wal f1_exlimd f3_exlimd a_wex f2_exlimd a_wi p_sylib $.
$}

$(Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jan-1997.) $)

${
	$v ph ps ch x  $.
	f0_exlimdh $f wff ph $.
	f1_exlimdh $f wff ps $.
	f2_exlimdh $f wff ch $.
	f3_exlimdh $f set x $.
	e0_exlimdh $e |- ( ph -> A. x ph ) $.
	e1_exlimdh $e |- ( ch -> A. x ch ) $.
	e2_exlimdh $e |- ( ph -> ( ps -> ch ) ) $.
	p_exlimdh $p |- ( ph -> ( E. x ps -> ch ) ) $= e0_exlimdh f0_exlimdh f3_exlimdh p_nfi e1_exlimdh f2_exlimdh f3_exlimdh p_nfi e2_exlimdh f0_exlimdh f1_exlimdh f2_exlimdh f3_exlimdh p_exlimd $.
$}

$(Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.27 $f wff ph $.
	f1_19.27 $f wff ps $.
	f2_19.27 $f set x $.
	e0_19.27 $e |- F/ x ps $.
	p_19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $= f0_19.27 f1_19.27 f2_19.27 p_19.26 e0_19.27 f1_19.27 f2_19.27 p_19.3 f1_19.27 f2_19.27 a_wal f1_19.27 f0_19.27 f2_19.27 a_wal p_anbi2i f0_19.27 f1_19.27 a_wa f2_19.27 a_wal f0_19.27 f2_19.27 a_wal f1_19.27 f2_19.27 a_wal a_wa f0_19.27 f2_19.27 a_wal f1_19.27 a_wa p_bitri $.
$}

$(Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.28 $f wff ph $.
	f1_19.28 $f wff ps $.
	f2_19.28 $f set x $.
	e0_19.28 $e |- F/ x ph $.
	p_19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $= f0_19.28 f1_19.28 f2_19.28 p_19.26 e0_19.28 f0_19.28 f2_19.28 p_19.3 f0_19.28 f2_19.28 a_wal f0_19.28 f1_19.28 f2_19.28 a_wal p_anbi1i f0_19.28 f1_19.28 a_wa f2_19.28 a_wal f0_19.28 f2_19.28 a_wal f1_19.28 f2_19.28 a_wal a_wa f0_19.28 f1_19.28 f2_19.28 a_wal a_wa p_bitri $.
$}

$(Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.36 $f wff ph $.
	f1_19.36 $f wff ps $.
	f2_19.36 $f set x $.
	e0_19.36 $e |- F/ x ps $.
	p_19.36 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $= f0_19.36 f1_19.36 f2_19.36 p_19.35 e0_19.36 f1_19.36 f2_19.36 p_19.9 f1_19.36 f2_19.36 a_wex f1_19.36 f0_19.36 f2_19.36 a_wal p_imbi2i f0_19.36 f1_19.36 a_wi f2_19.36 a_wex f0_19.36 f2_19.36 a_wal f1_19.36 f2_19.36 a_wex a_wi f0_19.36 f2_19.36 a_wal f1_19.36 a_wi p_bitri $.
$}

$(Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.36i $f wff ph $.
	f1_19.36i $f wff ps $.
	f2_19.36i $f set x $.
	e0_19.36i $e |- F/ x ps $.
	e1_19.36i $e |- E. x ( ph -> ps ) $.
	p_19.36i $p |- ( A. x ph -> ps ) $= e1_19.36i e0_19.36i f0_19.36i f1_19.36i f2_19.36i p_19.36 f0_19.36i f1_19.36i a_wi f2_19.36i a_wex f0_19.36i f2_19.36i a_wal f1_19.36i a_wi p_mpbi $.
$}

$(Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.37 $f wff ph $.
	f1_19.37 $f wff ps $.
	f2_19.37 $f set x $.
	e0_19.37 $e |- F/ x ph $.
	p_19.37 $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $= f0_19.37 f1_19.37 f2_19.37 p_19.35 e0_19.37 f0_19.37 f2_19.37 p_19.3 f0_19.37 f2_19.37 a_wal f0_19.37 f1_19.37 f2_19.37 a_wex p_imbi1i f0_19.37 f1_19.37 a_wi f2_19.37 a_wex f0_19.37 f2_19.37 a_wal f1_19.37 f2_19.37 a_wex a_wi f0_19.37 f1_19.37 f2_19.37 a_wex a_wi p_bitri $.
$}

$(Theorem 19.38 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.38 $f wff ph $.
	f1_19.38 $f wff ps $.
	f2_19.38 $f set x $.
	p_19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $= f0_19.38 f2_19.38 p_nfe1 f1_19.38 f2_19.38 p_nfa1 f0_19.38 f2_19.38 a_wex f1_19.38 f2_19.38 a_wal f2_19.38 p_nfim f0_19.38 f2_19.38 p_19.8a f1_19.38 f2_19.38 p_sp f0_19.38 f0_19.38 f2_19.38 a_wex f1_19.38 f2_19.38 a_wal f1_19.38 p_imim12i f0_19.38 f2_19.38 a_wex f1_19.38 f2_19.38 a_wal a_wi f0_19.38 f1_19.38 a_wi f2_19.38 p_alrimi $.
$}

$(Theorem 19.32 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_19.32 $f wff ph $.
	f1_19.32 $f wff ps $.
	f2_19.32 $f set x $.
	e0_19.32 $e |- F/ x ph $.
	p_19.32 $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $= e0_19.32 f0_19.32 f2_19.32 p_nfn f0_19.32 a_wn f1_19.32 f2_19.32 p_19.21 f0_19.32 f1_19.32 a_df-or f0_19.32 f1_19.32 a_wo f0_19.32 a_wn f1_19.32 a_wi f2_19.32 p_albii f0_19.32 f1_19.32 f2_19.32 a_wal a_df-or f0_19.32 a_wn f1_19.32 a_wi f2_19.32 a_wal f0_19.32 a_wn f1_19.32 f2_19.32 a_wal a_wi f0_19.32 f1_19.32 a_wo f2_19.32 a_wal f0_19.32 f1_19.32 f2_19.32 a_wal a_wo p_3bitr4i $.
$}

$(Theorem 19.31 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.31 $f wff ph $.
	f1_19.31 $f wff ps $.
	f2_19.31 $f set x $.
	e0_19.31 $e |- F/ x ps $.
	p_19.31 $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $= e0_19.31 f1_19.31 f0_19.31 f2_19.31 p_19.32 f0_19.31 f1_19.31 p_orcom f0_19.31 f1_19.31 a_wo f1_19.31 f0_19.31 a_wo f2_19.31 p_albii f0_19.31 f2_19.31 a_wal f1_19.31 p_orcom f1_19.31 f0_19.31 a_wo f2_19.31 a_wal f1_19.31 f0_19.31 f2_19.31 a_wal a_wo f0_19.31 f1_19.31 a_wo f2_19.31 a_wal f0_19.31 f2_19.31 a_wal f1_19.31 a_wo p_3bitr4i $.
$}

$(Theorem 19.44 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.44 $f wff ph $.
	f1_19.44 $f wff ps $.
	f2_19.44 $f set x $.
	e0_19.44 $e |- F/ x ps $.
	p_19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $= f0_19.44 f1_19.44 f2_19.44 p_19.43 e0_19.44 f1_19.44 f2_19.44 p_19.9 f1_19.44 f2_19.44 a_wex f1_19.44 f0_19.44 f2_19.44 a_wex p_orbi2i f0_19.44 f1_19.44 a_wo f2_19.44 a_wex f0_19.44 f2_19.44 a_wex f1_19.44 f2_19.44 a_wex a_wo f0_19.44 f2_19.44 a_wex f1_19.44 a_wo p_bitri $.
$}

$(Theorem 19.45 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.45 $f wff ph $.
	f1_19.45 $f wff ps $.
	f2_19.45 $f set x $.
	e0_19.45 $e |- F/ x ph $.
	p_19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $= f0_19.45 f1_19.45 f2_19.45 p_19.43 e0_19.45 f0_19.45 f2_19.45 p_19.9 f0_19.45 f2_19.45 a_wex f0_19.45 f1_19.45 f2_19.45 a_wex p_orbi1i f0_19.45 f1_19.45 a_wo f2_19.45 a_wex f0_19.45 f2_19.45 a_wex f1_19.45 f2_19.45 a_wex a_wo f0_19.45 f1_19.45 f2_19.45 a_wex a_wo p_bitri $.
$}

$(Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps x  $.
	f0_19.41 $f wff ph $.
	f1_19.41 $f wff ps $.
	f2_19.41 $f set x $.
	e0_19.41 $e |- F/ x ps $.
	p_19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $= f0_19.41 f1_19.41 f2_19.41 p_19.40 e0_19.41 f1_19.41 p_id f1_19.41 f1_19.41 f2_19.41 p_exlimi f1_19.41 f2_19.41 a_wex f1_19.41 f0_19.41 f2_19.41 a_wex p_anim2i f0_19.41 f1_19.41 a_wa f2_19.41 a_wex f0_19.41 f2_19.41 a_wex f1_19.41 f2_19.41 a_wex a_wa f0_19.41 f2_19.41 a_wex f1_19.41 a_wa p_syl e0_19.41 f1_19.41 f0_19.41 p_pm3.21 f1_19.41 f0_19.41 f0_19.41 f1_19.41 a_wa f2_19.41 p_eximd f1_19.41 f0_19.41 f2_19.41 a_wex f0_19.41 f1_19.41 a_wa f2_19.41 a_wex p_impcom f0_19.41 f1_19.41 a_wa f2_19.41 a_wex f0_19.41 f2_19.41 a_wex f1_19.41 a_wa p_impbii $.
$}

$(Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM, 18-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.42 $f wff ph $.
	f1_19.42 $f wff ps $.
	f2_19.42 $f set x $.
	e0_19.42 $e |- F/ x ph $.
	p_19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $= e0_19.42 f1_19.42 f0_19.42 f2_19.42 p_19.41 f0_19.42 f1_19.42 f2_19.42 p_exancom f0_19.42 f1_19.42 f2_19.42 a_wex p_ancom f1_19.42 f0_19.42 a_wa f2_19.42 a_wex f1_19.42 f2_19.42 a_wex f0_19.42 a_wa f0_19.42 f1_19.42 a_wa f2_19.42 a_wex f0_19.42 f1_19.42 f2_19.42 a_wex a_wa p_3bitr4i $.
$}

$(Swap 1st and 3rd existential quantifiers.  (Contributed by NM,
     9-Mar-1995.) $)

${
	$v ph x y z  $.
	f0_excom13 $f wff ph $.
	f1_excom13 $f set x $.
	f2_excom13 $f set y $.
	f3_excom13 $f set z $.
	p_excom13 $p |- ( E. x E. y E. z ph <-> E. z E. y E. x ph ) $= f0_excom13 f3_excom13 a_wex f1_excom13 f2_excom13 p_excom f0_excom13 f1_excom13 f3_excom13 p_excom f0_excom13 f3_excom13 a_wex f1_excom13 a_wex f0_excom13 f1_excom13 a_wex f3_excom13 a_wex f2_excom13 p_exbii f0_excom13 f1_excom13 a_wex f2_excom13 f3_excom13 p_excom f0_excom13 f3_excom13 a_wex f2_excom13 a_wex f1_excom13 a_wex f0_excom13 f3_excom13 a_wex f1_excom13 a_wex f2_excom13 a_wex f0_excom13 f1_excom13 a_wex f3_excom13 a_wex f2_excom13 a_wex f0_excom13 f1_excom13 a_wex f2_excom13 a_wex f3_excom13 a_wex p_3bitri $.
$}

$(Rotate existential quantifiers.  (Contributed by NM, 17-Mar-1995.) $)

${
	$v ph x y z  $.
	f0_exrot3 $f wff ph $.
	f1_exrot3 $f set x $.
	f2_exrot3 $f set y $.
	f3_exrot3 $f set z $.
	p_exrot3 $p |- ( E. x E. y E. z ph <-> E. y E. z E. x ph ) $= f0_exrot3 f1_exrot3 f2_exrot3 f3_exrot3 p_excom13 f0_exrot3 f1_exrot3 a_wex f3_exrot3 f2_exrot3 p_excom f0_exrot3 f3_exrot3 a_wex f2_exrot3 a_wex f1_exrot3 a_wex f0_exrot3 f1_exrot3 a_wex f2_exrot3 a_wex f3_exrot3 a_wex f0_exrot3 f1_exrot3 a_wex f3_exrot3 a_wex f2_exrot3 a_wex p_bitri $.
$}

$(Rotate existential quantifiers twice.  (Contributed by NM, 9-Mar-1995.) $)

${
	$v ph x y z w  $.
	f0_exrot4 $f wff ph $.
	f1_exrot4 $f set x $.
	f2_exrot4 $f set y $.
	f3_exrot4 $f set z $.
	f4_exrot4 $f set w $.
	p_exrot4 $p |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph ) $= f0_exrot4 f2_exrot4 f3_exrot4 f4_exrot4 p_excom13 f0_exrot4 f4_exrot4 a_wex f3_exrot4 a_wex f2_exrot4 a_wex f0_exrot4 f2_exrot4 a_wex f3_exrot4 a_wex f4_exrot4 a_wex f1_exrot4 p_exbii f0_exrot4 f2_exrot4 a_wex f1_exrot4 f4_exrot4 f3_exrot4 p_excom13 f0_exrot4 f4_exrot4 a_wex f3_exrot4 a_wex f2_exrot4 a_wex f1_exrot4 a_wex f0_exrot4 f2_exrot4 a_wex f3_exrot4 a_wex f4_exrot4 a_wex f1_exrot4 a_wex f0_exrot4 f2_exrot4 a_wex f1_exrot4 a_wex f4_exrot4 a_wex f3_exrot4 a_wex p_bitri $.
$}

$(Inference from ~ 19.8a .  (Contributed by Jeff Hankins, 26-Jul-2009.) $)

${
	$v ph x  $.
	f0_nexr $f wff ph $.
	f1_nexr $f set x $.
	e0_nexr $e |- -. E. x ph $.
	p_nexr $p |- -. ph $= e0_nexr f0_nexr f1_nexr p_19.8a f0_nexr f0_nexr f1_nexr a_wex p_mto $.
$}

$(A closed form of ~ nfim .  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 24-Sep-2016.) $)

${
	$v ph ps x  $.
	f0_nfim1 $f wff ph $.
	f1_nfim1 $f wff ps $.
	f2_nfim1 $f set x $.
	e0_nfim1 $e |- F/ x ph $.
	e1_nfim1 $e |- ( ph -> F/ x ps ) $.
	p_nfim1 $p |- F/ x ( ph -> ps ) $= e1_nfim1 f0_nfim1 f1_nfim1 f2_nfim1 p_nfrd f0_nfim1 f1_nfim1 f1_nfim1 f2_nfim1 a_wal p_a2i e0_nfim1 f0_nfim1 f1_nfim1 f2_nfim1 p_19.21 f0_nfim1 f1_nfim1 a_wi f0_nfim1 f1_nfim1 f2_nfim1 a_wal a_wi f0_nfim1 f1_nfim1 a_wi f2_nfim1 a_wal p_sylibr f0_nfim1 f1_nfim1 a_wi f2_nfim1 p_nfi $.
$}

$(A closed form of ~ nfan .  (Contributed by Mario Carneiro,
       3-Oct-2016.) $)

${
	$v ph ps x  $.
	f0_nfan1 $f wff ph $.
	f1_nfan1 $f wff ps $.
	f2_nfan1 $f set x $.
	e0_nfan1 $e |- F/ x ph $.
	e1_nfan1 $e |- ( ph -> F/ x ps ) $.
	p_nfan1 $p |- F/ x ( ph /\ ps ) $= e1_nfan1 f0_nfan1 f1_nfan1 f2_nfan1 p_nfrd f0_nfan1 f1_nfan1 f1_nfan1 f2_nfan1 a_wal p_imdistani e0_nfan1 f0_nfan1 f1_nfan1 f2_nfan1 p_19.28 f0_nfan1 f1_nfan1 a_wa f0_nfan1 f1_nfan1 f2_nfan1 a_wal a_wa f0_nfan1 f1_nfan1 a_wa f2_nfan1 a_wal p_sylibr f0_nfan1 f1_nfan1 a_wa f2_nfan1 p_nfi $.
$}

$(Place a conjunct in the scope of an existential quantifier.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)

${
	$v ph ps x  $.
	f0_exan $f wff ph $.
	f1_exan $f wff ps $.
	f2_exan $f set x $.
	e0_exan $e |- ( E. x ph /\ ps ) $.
	p_exan $p |- E. x ( ph /\ ps ) $= f0_exan f2_exan p_nfe1 f0_exan f2_exan a_wex f1_exan f2_exan p_19.28 e0_exan f0_exan f2_exan a_wex f1_exan a_wa f0_exan f2_exan a_wex f1_exan f2_exan a_wal a_wa f2_exan p_mpgbi f0_exan f1_exan f2_exan p_19.29r f0_exan f2_exan a_wex f1_exan f2_exan a_wal a_wa f0_exan f1_exan a_wa f2_exan a_wex a_ax-mp $.
$}

$(Deduction form of bound-variable hypothesis builder ~ hbn .
       (Contributed by NM, 3-Jan-2002.) $)

${
	$v ph ps x  $.
	f0_hbnd $f wff ph $.
	f1_hbnd $f wff ps $.
	f2_hbnd $f set x $.
	e0_hbnd $e |- ( ph -> A. x ph ) $.
	e1_hbnd $e |- ( ph -> ( ps -> A. x ps ) ) $.
	p_hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $= e0_hbnd e1_hbnd f0_hbnd f1_hbnd f1_hbnd f2_hbnd a_wal a_wi f2_hbnd p_alrimih f1_hbnd f2_hbnd p_hbnt f0_hbnd f1_hbnd f1_hbnd f2_hbnd a_wal a_wi f2_hbnd a_wal f1_hbnd a_wn f1_hbnd a_wn f2_hbnd a_wal a_wi p_syl $.
$}

$(Rearrange universal quantifiers.  (Contributed by NM, 12-Aug-1993.) $)

${
	$v ph ps x y  $.
	f0_aaan $f wff ph $.
	f1_aaan $f wff ps $.
	f2_aaan $f set x $.
	f3_aaan $f set y $.
	e0_aaan $e |- F/ y ph $.
	e1_aaan $e |- F/ x ps $.
	p_aaan $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $= e0_aaan f0_aaan f1_aaan f3_aaan p_19.28 f0_aaan f1_aaan a_wa f3_aaan a_wal f0_aaan f1_aaan f3_aaan a_wal a_wa f2_aaan p_albii e1_aaan f1_aaan f2_aaan f3_aaan p_nfal f0_aaan f1_aaan f3_aaan a_wal f2_aaan p_19.27 f0_aaan f1_aaan a_wa f3_aaan a_wal f2_aaan a_wal f0_aaan f1_aaan f3_aaan a_wal a_wa f2_aaan a_wal f0_aaan f2_aaan a_wal f1_aaan f3_aaan a_wal a_wa p_bitri $.
$}

$(Rearrange existential quantifiers.  (Contributed by NM, 8-Aug-1994.) $)

${
	$v ph ps x y  $.
	f0_eeor $f wff ph $.
	f1_eeor $f wff ps $.
	f2_eeor $f set x $.
	f3_eeor $f set y $.
	e0_eeor $e |- F/ y ph $.
	e1_eeor $e |- F/ x ps $.
	p_eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $= e0_eeor f0_eeor f1_eeor f3_eeor p_19.45 f0_eeor f1_eeor a_wo f3_eeor a_wex f0_eeor f1_eeor f3_eeor a_wex a_wo f2_eeor p_exbii e1_eeor f1_eeor f2_eeor f3_eeor p_nfex f0_eeor f1_eeor f3_eeor a_wex f2_eeor p_19.44 f0_eeor f1_eeor a_wo f3_eeor a_wex f2_eeor a_wex f0_eeor f1_eeor f3_eeor a_wex a_wo f2_eeor a_wex f0_eeor f2_eeor a_wex f1_eeor f3_eeor a_wex a_wo p_bitri $.
$}

$(Quantified "excluded middle."  Exercise 9.2a of Boolos, p. 111,
     _Computability and Logic_.  (Contributed by NM, 10-Dec-2000.) $)

${
	$v ph x  $.
	f0_qexmid $f wff ph $.
	f1_qexmid $f set x $.
	p_qexmid $p |- E. x ( ph -> A. x ph ) $= f0_qexmid f1_qexmid a_wal f1_qexmid p_19.8a f0_qexmid f0_qexmid f1_qexmid a_wal f1_qexmid p_19.35ri $.
$}

$(A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)

${
	$v ph x y  $.
	f0_equs5a $f wff ph $.
	f1_equs5a $f set x $.
	f2_equs5a $f set y $.
	p_equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $= f1_equs5a a_sup_set_class f2_equs5a a_sup_set_class a_wceq f0_equs5a a_wi f1_equs5a p_nfa1 f0_equs5a f1_equs5a f2_equs5a a_ax-11 f1_equs5a a_sup_set_class f2_equs5a a_sup_set_class a_wceq f0_equs5a f2_equs5a a_wal f1_equs5a a_sup_set_class f2_equs5a a_sup_set_class a_wceq f0_equs5a a_wi f1_equs5a a_wal p_imp f1_equs5a a_sup_set_class f2_equs5a a_sup_set_class a_wceq f0_equs5a f2_equs5a a_wal a_wa f1_equs5a a_sup_set_class f2_equs5a a_sup_set_class a_wceq f0_equs5a a_wi f1_equs5a a_wal f1_equs5a p_exlimi $.
$}

$(A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)

${
	$v ph x y  $.
	f0_equs5e $f wff ph $.
	f1_equs5e $f set x $.
	f2_equs5e $f set y $.
	p_equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $= f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e a_wa f1_equs5e p_nfe1 f0_equs5e f1_equs5e f2_equs5e p_equs3 f0_equs5e a_wn f1_equs5e f2_equs5e a_ax-11 f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e a_wn f2_equs5e a_wal f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e a_wn a_wi f1_equs5e a_wal p_con3rr3 f0_equs5e f2_equs5e a_df-ex f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e a_wn a_wi f1_equs5e a_wal a_wn f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e a_wn f2_equs5e a_wal a_wn f0_equs5e f2_equs5e a_wex p_syl6ibr f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e a_wa f1_equs5e a_wex f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e a_wn a_wi f1_equs5e a_wal a_wn f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e f2_equs5e a_wex a_wi p_sylbi f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e a_wa f1_equs5e a_wex f1_equs5e a_sup_set_class f2_equs5e a_sup_set_class a_wceq f0_equs5e f2_equs5e a_wex a_wi f1_equs5e p_alrimi $.
$}

$(Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)

${
	$v ph ps ch x  $.
	f0_exlimdd $f wff ph $.
	f1_exlimdd $f wff ps $.
	f2_exlimdd $f wff ch $.
	f3_exlimdd $f set x $.
	e0_exlimdd $e |- F/ x ph $.
	e1_exlimdd $e |- F/ x ch $.
	e2_exlimdd $e |- ( ph -> E. x ps ) $.
	e3_exlimdd $e |- ( ( ph /\ ps ) -> ch ) $.
	p_exlimdd $p |- ( ph -> ch ) $= e2_exlimdd e0_exlimdd e1_exlimdd e3_exlimdd f0_exlimdd f1_exlimdd f2_exlimdd p_ex f0_exlimdd f1_exlimdd f2_exlimdd f3_exlimdd p_exlimd f0_exlimdd f1_exlimdd f3_exlimdd a_wex f2_exlimdd p_mpd $.
$}

$(Special case of Theorem 19.21 of [Margaris] p. 90. _Notational
       convention_:  We sometimes suffix with "v" the label of a theorem
       eliminating a hypothesis such as ` F/ x ph ` in ~ 19.21 via the use of
       distinct variable conditions combined with ~ nfv .  Conversely, we
       sometimes suffix with "f" the label of a theorem introducing such a
       hypothesis to eliminate the need for the distinct variable condition;
       e.g. ~ euf derived from ~ df-eu .  The "f" stands for "not free in"
       which is less restrictive than "does not occur in."  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_19.21v $f wff ph $.
	f1_19.21v $f wff ps $.
	f2_19.21v $f set x $.
	p_19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $= f0_19.21v f2_19.21v p_nfv f0_19.21v f1_19.21v f2_19.21v p_19.21 $.
$}

$(Special case of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jun-1998.) $)

${
	$v ph ps x  $.
	$d x ps  $.
	f0_19.23v $f wff ph $.
	f1_19.23v $f wff ps $.
	f2_19.23v $f set x $.
	p_19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $= f1_19.23v f2_19.23v p_nfv f0_19.23v f1_19.23v f2_19.23v p_19.23 $.
$}

$(Theorem 19.23 of [Margaris] p. 90 extended to two variables.
       (Contributed by NM, 10-Aug-2004.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	$d y ps  $.
	f0_19.23vv $f wff ph $.
	f1_19.23vv $f wff ps $.
	f2_19.23vv $f set x $.
	f3_19.23vv $f set y $.
	p_19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $= f0_19.23vv f1_19.23vv f3_19.23vv p_19.23v f0_19.23vv f1_19.23vv a_wi f3_19.23vv a_wal f0_19.23vv f3_19.23vv a_wex f1_19.23vv a_wi f2_19.23vv p_albii f0_19.23vv f3_19.23vv a_wex f1_19.23vv f2_19.23vv p_19.23v f0_19.23vv f1_19.23vv a_wi f3_19.23vv a_wal f2_19.23vv a_wal f0_19.23vv f3_19.23vv a_wex f1_19.23vv a_wi f2_19.23vv a_wal f0_19.23vv f3_19.23vv a_wex f2_19.23vv a_wex f1_19.23vv a_wi p_bitri $.
$}

$(Theorem *11.53 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)

${
	$v ph ps x y  $.
	$d ph y  $.
	$d ps x  $.
	f0_pm11.53 $f wff ph $.
	f1_pm11.53 $f wff ps $.
	f2_pm11.53 $f set x $.
	f3_pm11.53 $f set y $.
	p_pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $= f0_pm11.53 f1_pm11.53 f3_pm11.53 p_19.21v f0_pm11.53 f1_pm11.53 a_wi f3_pm11.53 a_wal f0_pm11.53 f1_pm11.53 f3_pm11.53 a_wal a_wi f2_pm11.53 p_albii f1_pm11.53 f2_pm11.53 p_nfv f1_pm11.53 f2_pm11.53 f3_pm11.53 p_nfal f0_pm11.53 f1_pm11.53 f3_pm11.53 a_wal f2_pm11.53 p_19.23 f0_pm11.53 f1_pm11.53 a_wi f3_pm11.53 a_wal f2_pm11.53 a_wal f0_pm11.53 f1_pm11.53 f3_pm11.53 a_wal a_wi f2_pm11.53 a_wal f0_pm11.53 f2_pm11.53 a_wex f1_pm11.53 f3_pm11.53 a_wal a_wi p_bitri $.
$}

$(Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 3-Jun-2004.) $)

${
	$v ph ps x  $.
	$d x ps  $.
	f0_19.27v $f wff ph $.
	f1_19.27v $f wff ps $.
	f2_19.27v $f set x $.
	p_19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $= f1_19.27v f2_19.27v p_nfv f0_19.27v f1_19.27v f2_19.27v p_19.27 $.
$}

$(Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 25-Mar-2004.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_19.28v $f wff ph $.
	f1_19.28v $f wff ps $.
	f2_19.28v $f set x $.
	p_19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $= f0_19.28v f2_19.28v p_nfv f0_19.28v f1_19.28v f2_19.28v p_19.28 $.
$}

$(Special case of Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       18-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ps  $.
	f0_19.36v $f wff ph $.
	f1_19.36v $f wff ps $.
	f2_19.36v $f set x $.
	p_19.36v $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $= f1_19.36v f2_19.36v p_nfv f0_19.36v f1_19.36v f2_19.36v p_19.36 $.
$}

$(Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ps  $.
	f0_19.36aiv $f wff ph $.
	f1_19.36aiv $f wff ps $.
	f2_19.36aiv $f set x $.
	e0_19.36aiv $e |- E. x ( ph -> ps ) $.
	p_19.36aiv $p |- ( A. x ph -> ps ) $= f1_19.36aiv f2_19.36aiv p_nfv e0_19.36aiv f0_19.36aiv f1_19.36aiv f2_19.36aiv p_19.36i $.
$}

$(Special case of ~ 19.12 where its converse holds.  (Contributed by NM,
       18-Jul-2001.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	$d y ph  $.
	f0_19.12vv $f wff ph $.
	f1_19.12vv $f wff ps $.
	f2_19.12vv $f set x $.
	f3_19.12vv $f set y $.
	p_19.12vv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $= f0_19.12vv f1_19.12vv f3_19.12vv p_19.21v f0_19.12vv f1_19.12vv a_wi f3_19.12vv a_wal f0_19.12vv f1_19.12vv f3_19.12vv a_wal a_wi f2_19.12vv p_exbii f1_19.12vv f2_19.12vv p_nfv f1_19.12vv f2_19.12vv f3_19.12vv p_nfal f0_19.12vv f1_19.12vv f3_19.12vv a_wal f2_19.12vv p_19.36 f0_19.12vv f1_19.12vv f2_19.12vv p_19.36v f0_19.12vv f1_19.12vv a_wi f2_19.12vv a_wex f0_19.12vv f2_19.12vv a_wal f1_19.12vv a_wi f3_19.12vv p_albii f0_19.12vv f3_19.12vv p_nfv f0_19.12vv f3_19.12vv f2_19.12vv p_nfal f0_19.12vv f2_19.12vv a_wal f1_19.12vv f3_19.12vv p_19.21 f0_19.12vv f1_19.12vv a_wi f2_19.12vv a_wex f3_19.12vv a_wal f0_19.12vv f2_19.12vv a_wal f1_19.12vv a_wi f3_19.12vv a_wal f0_19.12vv f2_19.12vv a_wal f1_19.12vv f3_19.12vv a_wal a_wi p_bitr2i f0_19.12vv f1_19.12vv a_wi f3_19.12vv a_wal f2_19.12vv a_wex f0_19.12vv f1_19.12vv f3_19.12vv a_wal a_wi f2_19.12vv a_wex f0_19.12vv f2_19.12vv a_wal f1_19.12vv f3_19.12vv a_wal a_wi f0_19.12vv f1_19.12vv a_wi f2_19.12vv a_wex f3_19.12vv a_wal p_3bitri $.
$}

$(Special case of Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_19.37v $f wff ph $.
	f1_19.37v $f wff ps $.
	f2_19.37v $f set x $.
	p_19.37v $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $= f0_19.37v f2_19.37v p_nfv f0_19.37v f1_19.37v f2_19.37v p_19.37 $.
$}

$(Inference from Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_19.37aiv $f wff ph $.
	f1_19.37aiv $f wff ps $.
	f2_19.37aiv $f set x $.
	e0_19.37aiv $e |- E. x ( ph -> ps ) $.
	p_19.37aiv $p |- ( ph -> E. x ps ) $= e0_19.37aiv f0_19.37aiv f1_19.37aiv f2_19.37aiv p_19.37v f0_19.37aiv f1_19.37aiv a_wi f2_19.37aiv a_wex f0_19.37aiv f1_19.37aiv f2_19.37aiv a_wex a_wi p_mpbi $.
$}

$(Special case of Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ps  $.
	f0_19.41v $f wff ph $.
	f1_19.41v $f wff ps $.
	f2_19.41v $f set x $.
	p_19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $= f1_19.41v f2_19.41v p_nfv f0_19.41v f1_19.41v f2_19.41v p_19.41 $.
$}

$(Theorem 19.41 of [Margaris] p. 90 with 2 quantifiers.  (Contributed by
       NM, 30-Apr-1995.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	$d y ps  $.
	f0_19.41vv $f wff ph $.
	f1_19.41vv $f wff ps $.
	f2_19.41vv $f set x $.
	f3_19.41vv $f set y $.
	p_19.41vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) ) $= f0_19.41vv f1_19.41vv f3_19.41vv p_19.41v f0_19.41vv f1_19.41vv a_wa f3_19.41vv a_wex f0_19.41vv f3_19.41vv a_wex f1_19.41vv a_wa f2_19.41vv p_exbii f0_19.41vv f3_19.41vv a_wex f1_19.41vv f2_19.41vv p_19.41v f0_19.41vv f1_19.41vv a_wa f3_19.41vv a_wex f2_19.41vv a_wex f0_19.41vv f3_19.41vv a_wex f1_19.41vv a_wa f2_19.41vv a_wex f0_19.41vv f3_19.41vv a_wex f2_19.41vv a_wex f1_19.41vv a_wa p_bitri $.
$}

$(Theorem 19.41 of [Margaris] p. 90 with 3 quantifiers.  (Contributed by
       NM, 30-Apr-1995.) $)

${
	$v ph ps x y z  $.
	$d x ps  $.
	$d y ps  $.
	$d z ps  $.
	f0_19.41vvv $f wff ph $.
	f1_19.41vvv $f wff ps $.
	f2_19.41vvv $f set x $.
	f3_19.41vvv $f set y $.
	f4_19.41vvv $f set z $.
	p_19.41vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <-> ( E. x E. y E. z ph /\ ps ) ) $= f0_19.41vvv f1_19.41vvv f3_19.41vvv f4_19.41vvv p_19.41vv f0_19.41vvv f1_19.41vvv a_wa f4_19.41vvv a_wex f3_19.41vvv a_wex f0_19.41vvv f4_19.41vvv a_wex f3_19.41vvv a_wex f1_19.41vvv a_wa f2_19.41vvv p_exbii f0_19.41vvv f4_19.41vvv a_wex f3_19.41vvv a_wex f1_19.41vvv f2_19.41vvv p_19.41v f0_19.41vvv f1_19.41vvv a_wa f4_19.41vvv a_wex f3_19.41vvv a_wex f2_19.41vvv a_wex f0_19.41vvv f4_19.41vvv a_wex f3_19.41vvv a_wex f1_19.41vvv a_wa f2_19.41vvv a_wex f0_19.41vvv f4_19.41vvv a_wex f3_19.41vvv a_wex f2_19.41vvv a_wex f1_19.41vvv a_wa p_bitri $.
$}

$(Theorem 19.41 of [Margaris] p. 90 with 4 quantifiers.  (Contributed by
       FL, 14-Jul-2007.) $)

${
	$v ph ps x y z w  $.
	$d w ps  $.
	$d x ps  $.
	$d y ps  $.
	$d z ps  $.
	f0_19.41vvvv $f wff ph $.
	f1_19.41vvvv $f wff ps $.
	f2_19.41vvvv $f set x $.
	f3_19.41vvvv $f set y $.
	f4_19.41vvvv $f set z $.
	f5_19.41vvvv $f set w $.
	p_19.41vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <-> ( E. w E. x E. y E. z ph /\ ps ) ) $= f0_19.41vvvv f1_19.41vvvv f2_19.41vvvv f3_19.41vvvv f4_19.41vvvv p_19.41vvv f0_19.41vvvv f1_19.41vvvv a_wa f4_19.41vvvv a_wex f3_19.41vvvv a_wex f2_19.41vvvv a_wex f0_19.41vvvv f4_19.41vvvv a_wex f3_19.41vvvv a_wex f2_19.41vvvv a_wex f1_19.41vvvv a_wa f5_19.41vvvv p_exbii f0_19.41vvvv f4_19.41vvvv a_wex f3_19.41vvvv a_wex f2_19.41vvvv a_wex f1_19.41vvvv f5_19.41vvvv p_19.41v f0_19.41vvvv f1_19.41vvvv a_wa f4_19.41vvvv a_wex f3_19.41vvvv a_wex f2_19.41vvvv a_wex f5_19.41vvvv a_wex f0_19.41vvvv f4_19.41vvvv a_wex f3_19.41vvvv a_wex f2_19.41vvvv a_wex f1_19.41vvvv a_wa f5_19.41vvvv a_wex f0_19.41vvvv f4_19.41vvvv a_wex f3_19.41vvvv a_wex f2_19.41vvvv a_wex f5_19.41vvvv a_wex f1_19.41vvvv a_wa p_bitri $.
$}

$(Special case of Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_19.42v $f wff ph $.
	f1_19.42v $f wff ps $.
	f2_19.42v $f set x $.
	p_19.42v $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $= f0_19.42v f2_19.42v p_nfv f0_19.42v f1_19.42v f2_19.42v p_19.42 $.
$}

$(Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	f0_exdistr $f wff ph $.
	f1_exdistr $f wff ps $.
	f2_exdistr $f set x $.
	f3_exdistr $f set y $.
	p_exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $= f0_exdistr f1_exdistr f3_exdistr p_19.42v f0_exdistr f1_exdistr a_wa f3_exdistr a_wex f0_exdistr f1_exdistr f3_exdistr a_wex a_wa f2_exdistr p_exbii $.
$}

$(Theorem 19.42 of [Margaris] p. 90 with 2 quantifiers.  (Contributed by
       NM, 16-Mar-1995.) $)

${
	$v ph ps x y  $.
	$d x ph  $.
	$d y ph  $.
	f0_19.42vv $f wff ph $.
	f1_19.42vv $f wff ps $.
	f2_19.42vv $f set x $.
	f3_19.42vv $f set y $.
	p_19.42vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) ) $= f0_19.42vv f1_19.42vv f2_19.42vv f3_19.42vv p_exdistr f0_19.42vv f1_19.42vv f3_19.42vv a_wex f2_19.42vv p_19.42v f0_19.42vv f1_19.42vv a_wa f3_19.42vv a_wex f2_19.42vv a_wex f0_19.42vv f1_19.42vv f3_19.42vv a_wex a_wa f2_19.42vv a_wex f0_19.42vv f1_19.42vv f3_19.42vv a_wex f2_19.42vv a_wex a_wa p_bitri $.
$}

$(Theorem 19.42 of [Margaris] p. 90 with 3 quantifiers.  (Contributed by
       NM, 21-Sep-2011.) $)

${
	$v ph ps x y z  $.
	$d x ph  $.
	$d y ph  $.
	$d z ph  $.
	f0_19.42vvv $f wff ph $.
	f1_19.42vvv $f wff ps $.
	f2_19.42vvv $f set x $.
	f3_19.42vvv $f set y $.
	f4_19.42vvv $f set z $.
	p_19.42vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <-> ( ph /\ E. x E. y E. z ps ) ) $= f0_19.42vvv f1_19.42vvv f3_19.42vvv f4_19.42vvv p_19.42vv f0_19.42vvv f1_19.42vvv a_wa f4_19.42vvv a_wex f3_19.42vvv a_wex f0_19.42vvv f1_19.42vvv f4_19.42vvv a_wex f3_19.42vvv a_wex a_wa f2_19.42vvv p_exbii f0_19.42vvv f1_19.42vvv f4_19.42vvv a_wex f3_19.42vvv a_wex f2_19.42vvv p_19.42v f0_19.42vvv f1_19.42vvv a_wa f4_19.42vvv a_wex f3_19.42vvv a_wex f2_19.42vvv a_wex f0_19.42vvv f1_19.42vvv f4_19.42vvv a_wex f3_19.42vvv a_wex a_wa f2_19.42vvv a_wex f0_19.42vvv f1_19.42vvv f4_19.42vvv a_wex f3_19.42vvv a_wex f2_19.42vvv a_wex a_wa p_bitri $.
$}

$(Distribution of existential quantifiers.  (Contributed by NM,
       17-Mar-1995.) $)

${
	$v ph ps x y z  $.
	$d y ph  $.
	$d z ph  $.
	f0_exdistr2 $f wff ph $.
	f1_exdistr2 $f wff ps $.
	f2_exdistr2 $f set x $.
	f3_exdistr2 $f set y $.
	f4_exdistr2 $f set z $.
	p_exdistr2 $p |- ( E. x E. y E. z ( ph /\ ps ) <-> E. x ( ph /\ E. y E. z ps ) ) $= f0_exdistr2 f1_exdistr2 f3_exdistr2 f4_exdistr2 p_19.42vv f0_exdistr2 f1_exdistr2 a_wa f4_exdistr2 a_wex f3_exdistr2 a_wex f0_exdistr2 f1_exdistr2 f4_exdistr2 a_wex f3_exdistr2 a_wex a_wa f2_exdistr2 p_exbii $.
$}

$(Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps ch x y z  $.
	$d y ph  $.
	$d z ph  $.
	$d z ps  $.
	f0_3exdistr $f wff ph $.
	f1_3exdistr $f wff ps $.
	f2_3exdistr $f wff ch $.
	f3_3exdistr $f set x $.
	f4_3exdistr $f set y $.
	f5_3exdistr $f set z $.
	p_3exdistr $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <-> E. x ( ph /\ E. y ( ps /\ E. z ch ) ) ) $= f0_3exdistr f1_3exdistr f2_3exdistr p_3anass f0_3exdistr f1_3exdistr f2_3exdistr a_w3a f0_3exdistr f1_3exdistr f2_3exdistr a_wa a_wa f4_3exdistr f5_3exdistr p_2exbii f0_3exdistr f1_3exdistr f2_3exdistr a_wa f4_3exdistr f5_3exdistr p_19.42vv f1_3exdistr f2_3exdistr f4_3exdistr f5_3exdistr p_exdistr f1_3exdistr f2_3exdistr a_wa f5_3exdistr a_wex f4_3exdistr a_wex f1_3exdistr f2_3exdistr f5_3exdistr a_wex a_wa f4_3exdistr a_wex f0_3exdistr p_anbi2i f0_3exdistr f1_3exdistr f2_3exdistr a_w3a f5_3exdistr a_wex f4_3exdistr a_wex f0_3exdistr f1_3exdistr f2_3exdistr a_wa a_wa f5_3exdistr a_wex f4_3exdistr a_wex f0_3exdistr f1_3exdistr f2_3exdistr a_wa f5_3exdistr a_wex f4_3exdistr a_wex a_wa f0_3exdistr f1_3exdistr f2_3exdistr f5_3exdistr a_wex a_wa f4_3exdistr a_wex a_wa p_3bitri f0_3exdistr f1_3exdistr f2_3exdistr a_w3a f5_3exdistr a_wex f4_3exdistr a_wex f0_3exdistr f1_3exdistr f2_3exdistr f5_3exdistr a_wex a_wa f4_3exdistr a_wex a_wa f3_3exdistr p_exbii $.
$}

$(Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)

${
	$v ph ps ch th x y z w  $.
	$d y ph  $.
	$d z ph  $.
	$d w ph  $.
	$d z ps  $.
	$d w ps  $.
	$d w ch  $.
	f0_4exdistr $f wff ph $.
	f1_4exdistr $f wff ps $.
	f2_4exdistr $f wff ch $.
	f3_4exdistr $f wff th $.
	f4_4exdistr $f set x $.
	f5_4exdistr $f set y $.
	f6_4exdistr $f set z $.
	f7_4exdistr $f set w $.
	p_4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $= f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr a_wa p_anass f0_4exdistr f1_4exdistr a_wa f2_4exdistr f3_4exdistr a_wa a_wa f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr a_wa a_wa a_wa f7_4exdistr p_exbii f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr p_19.42v f1_4exdistr f2_4exdistr f3_4exdistr a_wa f7_4exdistr p_19.42v f1_4exdistr f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr a_wex f1_4exdistr f2_4exdistr f3_4exdistr a_wa f7_4exdistr a_wex a_wa f0_4exdistr p_anbi2i f2_4exdistr f3_4exdistr f7_4exdistr p_19.42v f2_4exdistr f3_4exdistr a_wa f7_4exdistr a_wex f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f1_4exdistr p_anbi2i f1_4exdistr f2_4exdistr f3_4exdistr a_wa f7_4exdistr a_wex a_wa f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa a_wa f0_4exdistr p_anbi2i f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr a_wa a_wa a_wa f7_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr a_wex a_wa f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr a_wa f7_4exdistr a_wex a_wa a_wa f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa a_wa a_wa p_3bitri f0_4exdistr f1_4exdistr a_wa f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr a_wa a_wa a_wa f7_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa a_wa a_wa p_bitri f0_4exdistr f1_4exdistr a_wa f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa a_wa a_wa f6_4exdistr p_exbii f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa a_wa f6_4exdistr p_19.42v f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f6_4exdistr p_19.42v f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa a_wa f6_4exdistr a_wex f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f6_4exdistr a_wex a_wa f0_4exdistr p_anbi2i f0_4exdistr f1_4exdistr a_wa f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr a_wex f6_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa a_wa a_wa f6_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa a_wa f6_4exdistr a_wex a_wa f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f6_4exdistr a_wex a_wa a_wa p_3bitri f0_4exdistr f1_4exdistr a_wa f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr a_wex f6_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f6_4exdistr a_wex a_wa a_wa f5_4exdistr p_exbii f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f6_4exdistr a_wex a_wa f5_4exdistr p_19.42v f0_4exdistr f1_4exdistr a_wa f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr a_wex f6_4exdistr a_wex f5_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f6_4exdistr a_wex a_wa a_wa f5_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f6_4exdistr a_wex a_wa f5_4exdistr a_wex a_wa p_bitri f0_4exdistr f1_4exdistr a_wa f2_4exdistr f3_4exdistr a_wa a_wa f7_4exdistr a_wex f6_4exdistr a_wex f5_4exdistr a_wex f0_4exdistr f1_4exdistr f2_4exdistr f3_4exdistr f7_4exdistr a_wex a_wa f6_4exdistr a_wex a_wa f5_4exdistr a_wex a_wa f4_4exdistr p_exbii $.
$}

$(Rearrange existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_eean $f wff ph $.
	f1_eean $f wff ps $.
	f2_eean $f set x $.
	f3_eean $f set y $.
	e0_eean $e |- F/ y ph $.
	e1_eean $e |- F/ x ps $.
	p_eean $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $= e0_eean f0_eean f1_eean f3_eean p_19.42 f0_eean f1_eean a_wa f3_eean a_wex f0_eean f1_eean f3_eean a_wex a_wa f2_eean p_exbii e1_eean f1_eean f2_eean f3_eean p_nfex f0_eean f1_eean f3_eean a_wex f2_eean p_19.41 f0_eean f1_eean a_wa f3_eean a_wex f2_eean a_wex f0_eean f1_eean f3_eean a_wex a_wa f2_eean a_wex f0_eean f2_eean a_wex f1_eean f3_eean a_wex a_wa p_bitri $.
$}

$(Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	$d x ps  $.
	f0_eeanv $f wff ph $.
	f1_eeanv $f wff ps $.
	f2_eeanv $f set x $.
	f3_eeanv $f set y $.
	p_eeanv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $= f0_eeanv f3_eeanv p_nfv f1_eeanv f2_eeanv p_nfv f0_eeanv f1_eeanv f2_eeanv f3_eeanv p_eean $.
$}

$(Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps ch x y z  $.
	$d y ph  $.
	$d z ph  $.
	$d x z ps  $.
	$d x y ch  $.
	f0_eeeanv $f wff ph $.
	f1_eeeanv $f wff ps $.
	f2_eeeanv $f wff ch $.
	f3_eeeanv $f set x $.
	f4_eeeanv $f set y $.
	f5_eeeanv $f set z $.
	p_eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <-> ( E. x ph /\ E. y ps /\ E. z ch ) ) $= f0_eeeanv f1_eeeanv f2_eeeanv a_df-3an f0_eeeanv f1_eeeanv f2_eeeanv a_w3a f0_eeeanv f1_eeeanv a_wa f2_eeeanv a_wa f3_eeeanv f4_eeeanv f5_eeeanv p_3exbii f0_eeeanv f1_eeeanv a_wa f2_eeeanv f4_eeeanv f5_eeeanv p_eeanv f0_eeeanv f1_eeeanv a_wa f2_eeeanv a_wa f5_eeeanv a_wex f4_eeeanv a_wex f0_eeeanv f1_eeeanv a_wa f4_eeeanv a_wex f2_eeeanv f5_eeeanv a_wex a_wa f3_eeeanv p_exbii f0_eeeanv f1_eeeanv f3_eeeanv f4_eeeanv p_eeanv f0_eeeanv f1_eeeanv a_wa f4_eeeanv a_wex f3_eeeanv a_wex f0_eeeanv f3_eeeanv a_wex f1_eeeanv f4_eeeanv a_wex a_wa f2_eeeanv f5_eeeanv a_wex p_anbi1i f0_eeeanv f1_eeeanv a_wa f4_eeeanv a_wex f2_eeeanv f5_eeeanv a_wex f3_eeeanv p_19.41v f0_eeeanv f3_eeeanv a_wex f1_eeeanv f4_eeeanv a_wex f2_eeeanv f5_eeeanv a_wex a_df-3an f0_eeeanv f1_eeeanv a_wa f4_eeeanv a_wex f3_eeeanv a_wex f2_eeeanv f5_eeeanv a_wex a_wa f0_eeeanv f3_eeeanv a_wex f1_eeeanv f4_eeeanv a_wex a_wa f2_eeeanv f5_eeeanv a_wex a_wa f0_eeeanv f1_eeeanv a_wa f4_eeeanv a_wex f2_eeeanv f5_eeeanv a_wex a_wa f3_eeeanv a_wex f0_eeeanv f3_eeeanv a_wex f1_eeeanv f4_eeeanv a_wex f2_eeeanv f5_eeeanv a_wex a_w3a p_3bitr4i f0_eeeanv f1_eeeanv f2_eeeanv a_w3a f5_eeeanv a_wex f4_eeeanv a_wex f3_eeeanv a_wex f0_eeeanv f1_eeeanv a_wa f2_eeeanv a_wa f5_eeeanv a_wex f4_eeeanv a_wex f3_eeeanv a_wex f0_eeeanv f1_eeeanv a_wa f4_eeeanv a_wex f2_eeeanv f5_eeeanv a_wex a_wa f3_eeeanv a_wex f0_eeeanv f3_eeeanv a_wex f1_eeeanv f4_eeeanv a_wex f2_eeeanv f5_eeeanv a_wex a_w3a p_3bitri $.
$}

$(Rearrange existential quantifiers.  (Contributed by NM, 31-Jul-1995.) $)

${
	$v ph ps x y z w  $.
	$d z ph  $.
	$d w ph  $.
	$d x ps  $.
	$d y ps  $.
	$d y z  $.
	$d w x  $.
	f0_ee4anv $f wff ph $.
	f1_ee4anv $f wff ps $.
	f2_ee4anv $f set x $.
	f3_ee4anv $f set y $.
	f4_ee4anv $f set z $.
	f5_ee4anv $f set w $.
	p_ee4anv $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <-> ( E. x E. y ph /\ E. z E. w ps ) ) $= f0_ee4anv f1_ee4anv a_wa f5_ee4anv a_wex f3_ee4anv f4_ee4anv p_excom f0_ee4anv f1_ee4anv a_wa f5_ee4anv a_wex f4_ee4anv a_wex f3_ee4anv a_wex f0_ee4anv f1_ee4anv a_wa f5_ee4anv a_wex f3_ee4anv a_wex f4_ee4anv a_wex f2_ee4anv p_exbii f0_ee4anv f1_ee4anv f3_ee4anv f5_ee4anv p_eeanv f0_ee4anv f1_ee4anv a_wa f5_ee4anv a_wex f3_ee4anv a_wex f0_ee4anv f3_ee4anv a_wex f1_ee4anv f5_ee4anv a_wex a_wa f2_ee4anv f4_ee4anv p_2exbii f0_ee4anv f3_ee4anv a_wex f1_ee4anv f5_ee4anv a_wex f2_ee4anv f4_ee4anv p_eeanv f0_ee4anv f1_ee4anv a_wa f5_ee4anv a_wex f4_ee4anv a_wex f3_ee4anv a_wex f2_ee4anv a_wex f0_ee4anv f1_ee4anv a_wa f5_ee4anv a_wex f3_ee4anv a_wex f4_ee4anv a_wex f2_ee4anv a_wex f0_ee4anv f3_ee4anv a_wex f1_ee4anv f5_ee4anv a_wex a_wa f4_ee4anv a_wex f2_ee4anv a_wex f0_ee4anv f3_ee4anv a_wex f2_ee4anv a_wex f1_ee4anv f5_ee4anv a_wex f4_ee4anv a_wex a_wa p_3bitri $.
$}

$(Deduction for generalization rule for negated wff.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_nexdv $f wff ph $.
	f1_nexdv $f wff ps $.
	f2_nexdv $f set x $.
	e0_nexdv $e |- ( ph -> -. ps ) $.
	p_nexdv $p |- ( ph -> -. E. x ps ) $= f0_nexdv f2_nexdv p_nfv e0_nexdv f0_nexdv f1_nexdv f2_nexdv p_nexd $.
$}

$(One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be
     read:  " ` x = y -> ( ph ( x , x ) -> ph ( x , y ) ) ` , provided that
     ` y ` is free for ` x ` in ` ph ( x , x ) ` ."  Axiom 7 of [Mendelson]
     p. 95.  (Contributed by NM, 15-Feb-2005.) $)

${
	$v ph x y  $.
	f0_stdpc7 $f wff ph $.
	f1_stdpc7 $f set x $.
	f2_stdpc7 $f set y $.
	p_stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $= f0_stdpc7 f2_stdpc7 f1_stdpc7 p_sbequ2 f0_stdpc7 f2_stdpc7 f1_stdpc7 a_wsb f0_stdpc7 a_wi f2_stdpc7 f1_stdpc7 p_equcoms $.
$}

$(An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sbequ1 $f wff ph $.
	f1_sbequ1 $f set x $.
	f2_sbequ1 $f set y $.
	p_sbequ1 $p |- ( x = y -> ( ph -> [ y / x ] ph ) ) $= f1_sbequ1 a_sup_set_class f2_sbequ1 a_sup_set_class a_wceq f0_sbequ1 p_pm3.4 f1_sbequ1 a_sup_set_class f2_sbequ1 a_sup_set_class a_wceq f0_sbequ1 a_wa f1_sbequ1 p_19.8a f0_sbequ1 f1_sbequ1 f2_sbequ1 a_df-sb f1_sbequ1 a_sup_set_class f2_sbequ1 a_sup_set_class a_wceq f0_sbequ1 a_wa f1_sbequ1 a_sup_set_class f2_sbequ1 a_sup_set_class a_wceq f0_sbequ1 a_wi f1_sbequ1 a_sup_set_class f2_sbequ1 a_sup_set_class a_wceq f0_sbequ1 a_wa f1_sbequ1 a_wex f0_sbequ1 f1_sbequ1 f2_sbequ1 a_wsb p_sylanbrc f1_sbequ1 a_sup_set_class f2_sbequ1 a_sup_set_class a_wceq f0_sbequ1 f0_sbequ1 f1_sbequ1 f2_sbequ1 a_wsb p_ex $.
$}

$(An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sbequ12 $f wff ph $.
	f1_sbequ12 $f set x $.
	f2_sbequ12 $f set y $.
	p_sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $= f0_sbequ12 f1_sbequ12 f2_sbequ12 p_sbequ1 f0_sbequ12 f1_sbequ12 f2_sbequ12 p_sbequ2 f1_sbequ12 a_sup_set_class f2_sbequ12 a_sup_set_class a_wceq f0_sbequ12 f0_sbequ12 f1_sbequ12 f2_sbequ12 a_wsb p_impbid $.
$}

$(An equality theorem for substitution.  (Contributed by NM, 6-Oct-2004.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)

${
	$v ph x y  $.
	f0_sbequ12r $f wff ph $.
	f1_sbequ12r $f set x $.
	f2_sbequ12r $f set y $.
	p_sbequ12r $p |- ( x = y -> ( [ x / y ] ph <-> ph ) ) $= f0_sbequ12r f2_sbequ12r f1_sbequ12r p_sbequ12 f2_sbequ12r a_sup_set_class f1_sbequ12r a_sup_set_class a_wceq f0_sbequ12r f0_sbequ12r f2_sbequ12r f1_sbequ12r a_wsb p_bicomd f0_sbequ12r f2_sbequ12r f1_sbequ12r a_wsb f0_sbequ12r a_wb f2_sbequ12r f1_sbequ12r p_equcoms $.
$}

$(An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_sbequ12a $f wff ph $.
	f1_sbequ12a $f set x $.
	f2_sbequ12a $f set y $.
	p_sbequ12a $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $= f0_sbequ12a f1_sbequ12a f2_sbequ12a p_sbequ12 f0_sbequ12a f2_sbequ12a f1_sbequ12a p_sbequ12 f0_sbequ12a f0_sbequ12a f2_sbequ12a f1_sbequ12a a_wsb a_wb f2_sbequ12a f1_sbequ12a p_equcoms f1_sbequ12a a_sup_set_class f2_sbequ12a a_sup_set_class a_wceq f0_sbequ12a f0_sbequ12a f1_sbequ12a f2_sbequ12a a_wsb f0_sbequ12a f2_sbequ12a f1_sbequ12a a_wsb p_bitr3d $.
$}

$(An identity theorem for substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint).  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x  $.
	f0_sbid $f wff ph $.
	f1_sbid $f set x $.
	p_sbid $p |- ( [ x / x ] ph <-> ph ) $= f1_sbid p_equid f0_sbid f1_sbid f1_sbid p_sbequ12 f1_sbid a_sup_set_class f1_sbid a_sup_set_class a_wceq f0_sbid f0_sbid f1_sbid f1_sbid a_wsb a_wb a_ax-mp f0_sbid f0_sbid f1_sbid f1_sbid a_wsb p_bicomi $.
$}

$(A version of ~ sb4 that doesn't require a distinctor antecedent.
     (Contributed by NM, 2-Feb-2007.) $)

${
	$v ph x y  $.
	f0_sb4a $f wff ph $.
	f1_sb4a $f set x $.
	f2_sb4a $f set y $.
	p_sb4a $p |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) ) $= f0_sb4a f2_sb4a a_wal f1_sb4a f2_sb4a p_sb1 f0_sb4a f1_sb4a f2_sb4a p_equs5a f0_sb4a f2_sb4a a_wal f1_sb4a f2_sb4a a_wsb f1_sb4a a_sup_set_class f2_sb4a a_sup_set_class a_wceq f0_sb4a f2_sb4a a_wal a_wa f1_sb4a a_wex f1_sb4a a_sup_set_class f2_sb4a a_sup_set_class a_wceq f0_sb4a a_wi f1_sb4a a_wal p_syl $.
$}

$(One direction of a simplified definition of substitution that unlike ~ sb4
     doesn't require a distinctor antecedent.  (Contributed by NM,
     2-Feb-2007.) $)

${
	$v ph x y  $.
	f0_sb4e $f wff ph $.
	f1_sb4e $f set x $.
	f2_sb4e $f set y $.
	p_sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $= f0_sb4e f1_sb4e f2_sb4e p_sb1 f0_sb4e f1_sb4e f2_sb4e p_equs5e f0_sb4e f1_sb4e f2_sb4e a_wsb f1_sb4e a_sup_set_class f2_sb4e a_sup_set_class a_wceq f0_sb4e a_wa f1_sb4e a_wex f1_sb4e a_sup_set_class f2_sb4e a_sup_set_class a_wceq f0_sb4e f2_sb4e a_wex a_wi f1_sb4e a_wal p_syl $.
$}


