$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-7_(Quantifier_Commutation).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Axiom scheme ax-11 (Substitution)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Substitution.  One of the 5 equality axioms of predicate
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
	fax-11_0 $f wff ph $.
	fax-11_1 $f set x $.
	fax-11_2 $f set y $.
	ax-11 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.
$}
$( Specialization.  A universally quantified wff implies the wff without a
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
	$d x w $.
	$d w ph $.
	isp_0 $f set w $.
	fsp_0 $f wff ph $.
	fsp_1 $f set x $.
	sp $p |- ( A. x ph -> ph ) $= fsp_0 fsp_1 wal fsp_0 wi isp_0 fsp_1 weq wn isp_0 wal isp_0 fsp_1 ax9v fsp_0 fsp_1 wal fsp_0 wi wn isp_0 fsp_1 weq wn isp_0 isp_0 fsp_1 weq fsp_0 fsp_1 wal fsp_0 wi isp_0 fsp_1 weq fsp_0 fsp_0 fsp_1 wal isp_0 fsp_1 weq fsp_0 wn fsp_1 isp_0 weq fsp_0 wn wi fsp_1 wal fsp_0 fsp_1 wal wn isp_0 fsp_1 weq fsp_1 isp_0 weq fsp_0 wn fsp_0 wn isp_0 wal fsp_1 isp_0 weq fsp_0 wn wi fsp_1 wal isp_0 fsp_1 equcomi fsp_0 wn isp_0 ax-17 fsp_0 wn fsp_1 isp_0 ax-11 syl2im fsp_1 isp_0 weq fsp_0 wn wi fsp_1 wal fsp_0 fsp_1 wal fsp_1 isp_0 weq wn fsp_1 wal fsp_1 isp_0 ax9v fsp_1 isp_0 weq fsp_0 wn wi fsp_0 fsp_1 isp_0 weq wn fsp_1 fsp_1 isp_0 weq fsp_0 con2 al2imi mtoi syl6 con4d con3i alrimiv mt3 $.
$}
$( Show that the original axiom ~ ax-5o can be derived from ~ ax-5 and
     others.  See ~ ax5 for the rederivation of ~ ax-5 from ~ ax-5o .

     Part of the proof is based on the proof of Lemma 22 of [Monk2] p. 114.
     (Contributed by NM, 21-May-2008.)  (Proof modification is discouraged.) $)
${
	fax5o_0 $f wff ph $.
	fax5o_1 $f wff ps $.
	fax5o_2 $f set x $.
	ax5o $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $= fax5o_0 fax5o_2 wal fax5o_0 fax5o_2 wal fax5o_2 wal fax5o_0 fax5o_2 wal fax5o_1 wi fax5o_2 wal fax5o_1 fax5o_2 wal fax5o_0 fax5o_2 wal fax5o_0 fax5o_2 wal wn fax5o_2 wal wn fax5o_0 fax5o_2 wal wn fax5o_2 wal wn fax5o_2 wal fax5o_0 fax5o_2 wal fax5o_2 wal fax5o_0 fax5o_2 wal wn fax5o_2 wal fax5o_0 fax5o_2 wal fax5o_0 fax5o_2 wal wn fax5o_2 sp con2i fax5o_0 fax5o_2 wal wn fax5o_2 hbn1 fax5o_0 fax5o_2 wal wn fax5o_2 wal wn fax5o_0 fax5o_2 wal fax5o_2 fax5o_0 fax5o_2 wal fax5o_0 fax5o_2 wal wn fax5o_2 wal fax5o_0 fax5o_2 hbn1 con1i alimi 3syl fax5o_0 fax5o_2 wal fax5o_1 fax5o_2 ax-5 syl5 $.
$}
$( If a wff is true, it is true for at least one instance.  Special case of
     Theorem 19.8 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.8a_0 $f wff ph $.
	f19.8a_1 $f set x $.
	19.8a $p |- ( ph -> E. x ph ) $= f19.8a_0 f19.8a_0 wn f19.8a_1 wal wn f19.8a_0 f19.8a_1 wex f19.8a_0 wn f19.8a_1 wal f19.8a_0 f19.8a_0 wn f19.8a_1 sp con2i f19.8a_0 f19.8a_1 df-ex sylibr $.
$}
$( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.) $)
${
	fhba1_0 $f wff ph $.
	fhba1_1 $f set x $.
	hba1 $p |- ( A. x ph -> A. x A. x ph ) $= fhba1_0 fhba1_1 wal fhba1_0 fhba1_1 wal wn fhba1_1 wal wn fhba1_0 fhba1_1 wal wn fhba1_1 wal wn fhba1_1 wal fhba1_0 fhba1_1 wal fhba1_1 wal fhba1_0 fhba1_1 wal wn fhba1_1 wal fhba1_0 fhba1_1 wal fhba1_0 fhba1_1 wal wn fhba1_1 sp con2i fhba1_0 fhba1_1 wal wn fhba1_1 hbn1 fhba1_0 fhba1_1 wal wn fhba1_1 wal wn fhba1_0 fhba1_1 wal fhba1_1 fhba1_0 fhba1_1 wal fhba1_0 fhba1_1 wal wn fhba1_1 wal fhba1_0 fhba1_1 hbn1 con1i alimi 3syl $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by NM, 5-Aug-1993.) $)
${
	fhbn_0 $f wff ph $.
	fhbn_1 $f set x $.
	ehbn_0 $e |- ( ph -> A. x ph ) $.
	hbn $p |- ( -. ph -> A. x -. ph ) $= fhbn_0 wn fhbn_0 fhbn_1 wal wn fhbn_0 wn fhbn_1 wal fhbn_0 fhbn_1 wal fhbn_0 fhbn_0 fhbn_1 sp con3i fhbn_0 fhbn_1 wal wn fhbn_0 wn fhbn_1 fhbn_0 fhbn_1 hbn1 fhbn_0 fhbn_0 fhbn_1 wal ehbn_0 con3i alrimih syl $.
$}
$( Deduction form of bound-variable hypothesis builder ~ hbim .
       (Contributed by NM, 1-Jan-2002.) $)
${
	fhbimd_0 $f wff ph $.
	fhbimd_1 $f wff ps $.
	fhbimd_2 $f wff ch $.
	fhbimd_3 $f set x $.
	ehbimd_0 $e |- ( ph -> A. x ph ) $.
	ehbimd_1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
	ehbimd_2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
	hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $= fhbimd_0 fhbimd_1 fhbimd_2 fhbimd_1 fhbimd_2 wi fhbimd_3 wal fhbimd_0 fhbimd_1 wn fhbimd_1 wn fhbimd_3 wal fhbimd_1 fhbimd_2 wi fhbimd_3 wal fhbimd_0 fhbimd_1 fhbimd_1 fhbimd_3 wal wi fhbimd_3 wal fhbimd_1 wn fhbimd_1 fhbimd_3 wal wn fhbimd_3 wal fhbimd_1 wn fhbimd_3 wal fhbimd_0 fhbimd_1 fhbimd_1 fhbimd_3 wal wi fhbimd_3 ehbimd_0 ehbimd_1 alrimih fhbimd_1 fhbimd_3 wal wn fhbimd_3 wal fhbimd_1 fhbimd_1 fhbimd_3 wal fhbimd_1 fhbimd_1 fhbimd_3 wal wn fhbimd_3 wal fhbimd_1 fhbimd_3 sp fhbimd_1 fhbimd_3 hbn1 nsyl4 con1i fhbimd_1 fhbimd_1 fhbimd_3 wal wi fhbimd_1 fhbimd_3 wal wn fhbimd_1 wn fhbimd_3 fhbimd_1 fhbimd_1 fhbimd_3 wal con3 al2imi syl2im fhbimd_1 wn fhbimd_1 fhbimd_2 wi fhbimd_3 fhbimd_1 fhbimd_2 pm2.21 alimi syl6 fhbimd_0 fhbimd_2 fhbimd_2 fhbimd_3 wal fhbimd_1 fhbimd_2 wi fhbimd_3 wal ehbimd_2 fhbimd_2 fhbimd_1 fhbimd_2 wi fhbimd_3 fhbimd_2 fhbimd_1 ax-1 alimi syl6 jad $.
$}
$( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.) $)
${
	$d x z $.
	fspimeh_0 $f wff ph $.
	fspimeh_1 $f wff ps $.
	fspimeh_2 $f set x $.
	fspimeh_3 $f set z $.
	espimeh_0 $e |- ( ph -> A. x ph ) $.
	espimeh_1 $e |- ( x = z -> ( ph -> ps ) ) $.
	spimeh $p |- ( ph -> E. x ps ) $= fspimeh_0 fspimeh_1 wn fspimeh_2 wal wn fspimeh_1 fspimeh_2 wex fspimeh_1 wn fspimeh_2 wal fspimeh_0 fspimeh_1 wn fspimeh_2 wal fspimeh_0 wn wi fspimeh_2 fspimeh_3 weq wn fspimeh_2 wal fspimeh_2 fspimeh_3 ax9v fspimeh_1 wn fspimeh_2 wal fspimeh_0 wn wi wn fspimeh_2 fspimeh_3 weq wn fspimeh_2 fspimeh_1 wn fspimeh_2 wal fspimeh_0 wn wi fspimeh_2 fspimeh_0 fspimeh_0 wi fspimeh_1 wn fspimeh_2 wal fspimeh_0 wn wi fspimeh_1 wn fspimeh_2 wal fspimeh_0 wn wi fspimeh_2 wal wi fspimeh_0 id fspimeh_0 fspimeh_0 wi fspimeh_1 wn fspimeh_2 wal fspimeh_0 wn fspimeh_2 fspimeh_0 fspimeh_0 wi fspimeh_2 fspimeh_0 id hbth fspimeh_1 wn fspimeh_2 wal fspimeh_1 wn fspimeh_2 wal fspimeh_2 wal wi fspimeh_0 fspimeh_0 wi fspimeh_1 wn fspimeh_2 hba1 a1i fspimeh_0 wn fspimeh_0 wn fspimeh_2 wal wi fspimeh_0 fspimeh_0 wi fspimeh_0 fspimeh_2 espimeh_0 hbn a1i hbimd ax-mp hbn fspimeh_2 fspimeh_3 weq fspimeh_1 wn fspimeh_2 wal fspimeh_0 wn wi fspimeh_2 fspimeh_3 weq fspimeh_0 fspimeh_1 fspimeh_1 wn fspimeh_2 wal espimeh_1 fspimeh_1 wn fspimeh_2 sp nsyli con3i alrimih mt3 con2i fspimeh_1 fspimeh_2 df-ex sylibr $.
$}
$( Show that the original axiom ~ ax-6o can be derived from ~ ax-6 and
     others.  See ~ ax6 for the rederivation of ~ ax-6 from ~ ax-6o .

     Normally, ~ ax6o should be used rather than ~ ax-6o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     21-May-2008.) $)
${
	fax6o_0 $f wff ph $.
	fax6o_1 $f set x $.
	ax6o $p |- ( -. A. x -. A. x ph -> ph ) $= fax6o_0 fax6o_1 wal fax6o_0 fax6o_0 fax6o_1 wal wn fax6o_1 wal fax6o_0 fax6o_1 sp fax6o_0 fax6o_1 ax-6 nsyl4 $.
$}
$( Closed theorem version of bound-variable hypothesis builder ~ hbn .
     (Contributed by NM, 5-Aug-1993.) $)
${
	fhbnt_0 $f wff ph $.
	fhbnt_1 $f set x $.
	hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $= fhbnt_0 wn fhbnt_0 fhbnt_1 wal wn fhbnt_1 wal fhbnt_0 fhbnt_0 fhbnt_1 wal wi fhbnt_1 wal fhbnt_0 wn fhbnt_1 wal fhbnt_0 fhbnt_1 wal wn fhbnt_1 wal fhbnt_0 fhbnt_0 fhbnt_1 ax6o con1i fhbnt_0 fhbnt_0 fhbnt_1 wal wi fhbnt_0 fhbnt_1 wal wn fhbnt_0 wn fhbnt_1 fhbnt_0 fhbnt_0 fhbnt_1 wal con3 al2imi syl5 $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 3-Mar-2008.) $)
${
	fhbim_0 $f wff ph $.
	fhbim_1 $f wff ps $.
	fhbim_2 $f set x $.
	ehbim_0 $e |- ( ph -> A. x ph ) $.
	ehbim_1 $e |- ( ps -> A. x ps ) $.
	hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $= fhbim_0 fhbim_1 fhbim_0 fhbim_1 wi fhbim_2 wal fhbim_0 wn fhbim_0 fhbim_1 wi fhbim_2 fhbim_0 fhbim_2 ehbim_0 hbn fhbim_0 fhbim_1 pm2.21 alrimih fhbim_1 fhbim_0 fhbim_1 wi fhbim_2 ehbim_1 fhbim_1 fhbim_0 ax-1 alrimih ja $.
$}
$( A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.9ht_0 $f wff ph $.
	f19.9ht_1 $f set x $.
	19.9ht $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $= f19.9ht_0 f19.9ht_1 wex f19.9ht_0 wn f19.9ht_1 wal wn f19.9ht_0 f19.9ht_0 f19.9ht_1 wal wi f19.9ht_1 wal f19.9ht_0 f19.9ht_0 f19.9ht_1 df-ex f19.9ht_0 f19.9ht_0 f19.9ht_1 wal wi f19.9ht_1 wal f19.9ht_0 f19.9ht_0 wn f19.9ht_1 wal f19.9ht_0 f19.9ht_1 hbnt con1d syl5bi $.
$}
$( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.) $)
${
	f19.9h_0 $f wff ph $.
	f19.9h_1 $f set x $.
	e19.9h_0 $e |- ( ph -> A. x ph ) $.
	19.9h $p |- ( E. x ph <-> ph ) $= f19.9h_0 f19.9h_1 wex f19.9h_0 f19.9h_0 f19.9h_0 f19.9h_1 wal wi f19.9h_0 f19.9h_1 wex f19.9h_0 wi f19.9h_1 f19.9h_0 f19.9h_1 19.9ht e19.9h_0 mpg f19.9h_0 f19.9h_1 19.8a impbii $.
$}
$( Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
${
	f19.23h_0 $f wff ph $.
	f19.23h_1 $f wff ps $.
	f19.23h_2 $f set x $.
	e19.23h_0 $e |- ( ps -> A. x ps ) $.
	19.23h $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $= f19.23h_0 f19.23h_1 wi f19.23h_2 wal f19.23h_0 f19.23h_2 wex f19.23h_1 wi f19.23h_0 f19.23h_1 wi f19.23h_2 wal f19.23h_0 f19.23h_2 wex f19.23h_1 f19.23h_2 wex f19.23h_1 f19.23h_0 f19.23h_1 f19.23h_2 exim f19.23h_1 f19.23h_2 e19.23h_0 19.9h syl6ib f19.23h_0 f19.23h_2 wex f19.23h_1 wi f19.23h_0 f19.23h_1 wi f19.23h_2 f19.23h_0 f19.23h_2 wex f19.23h_1 f19.23h_2 f19.23h_0 f19.23h_2 hbe1 e19.23h_0 hbim f19.23h_0 f19.23h_0 f19.23h_2 wex f19.23h_1 f19.23h_0 f19.23h_2 19.8a imim1i alrimih impbii $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
${
	fexlimih_0 $f wff ph $.
	fexlimih_1 $f wff ps $.
	fexlimih_2 $f set x $.
	eexlimih_0 $e |- ( ps -> A. x ps ) $.
	eexlimih_1 $e |- ( ph -> ps ) $.
	exlimih $p |- ( E. x ph -> ps ) $= fexlimih_0 fexlimih_1 wi fexlimih_0 fexlimih_2 wex fexlimih_1 wi fexlimih_2 fexlimih_0 fexlimih_1 fexlimih_2 eexlimih_0 19.23h eexlimih_1 mpgbi $.
$}
$( Weaker version of ~ equsalh (requiring distinct variables) without using
       ~ ax-12 .  (Contributed by NM, 29-Nov-2015.) $)
${
	$d x y $.
	fequsalhw_0 $f wff ph $.
	fequsalhw_1 $f wff ps $.
	fequsalhw_2 $f set x $.
	fequsalhw_3 $f set y $.
	eequsalhw_0 $e |- ( ps -> A. x ps ) $.
	eequsalhw_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	equsalhw $p |- ( A. x ( x = y -> ph ) <-> ps ) $= fequsalhw_2 fequsalhw_3 weq fequsalhw_0 wi fequsalhw_2 wal fequsalhw_2 fequsalhw_3 weq fequsalhw_1 fequsalhw_2 wal wi fequsalhw_2 wal fequsalhw_1 fequsalhw_2 fequsalhw_3 weq fequsalhw_0 wi fequsalhw_2 fequsalhw_3 weq fequsalhw_1 fequsalhw_2 wal wi fequsalhw_2 fequsalhw_2 fequsalhw_3 weq fequsalhw_0 fequsalhw_1 fequsalhw_2 wal fequsalhw_2 fequsalhw_3 weq fequsalhw_0 fequsalhw_1 fequsalhw_1 fequsalhw_2 wal eequsalhw_1 fequsalhw_1 fequsalhw_2 wal fequsalhw_1 fequsalhw_1 fequsalhw_2 sp eequsalhw_0 impbii syl6bbr pm5.74i albii fequsalhw_1 fequsalhw_2 fequsalhw_3 weq fequsalhw_1 fequsalhw_2 wal wi fequsalhw_2 wal fequsalhw_1 fequsalhw_2 fequsalhw_3 weq fequsalhw_1 fequsalhw_2 wal wi fequsalhw_2 eequsalhw_0 fequsalhw_1 fequsalhw_1 fequsalhw_2 wal fequsalhw_2 fequsalhw_3 weq eequsalhw_0 a1d alrimih fequsalhw_2 fequsalhw_3 weq fequsalhw_1 fequsalhw_2 wal wi fequsalhw_2 wal fequsalhw_1 fequsalhw_2 wal wn fequsalhw_2 wal wn fequsalhw_1 fequsalhw_2 fequsalhw_3 weq fequsalhw_1 fequsalhw_2 wal wi fequsalhw_2 wal fequsalhw_1 fequsalhw_2 wal wn fequsalhw_2 wal fequsalhw_2 fequsalhw_3 weq wn fequsalhw_2 wal fequsalhw_2 fequsalhw_3 ax9v fequsalhw_2 fequsalhw_3 weq fequsalhw_1 fequsalhw_2 wal wi fequsalhw_1 fequsalhw_2 wal wn fequsalhw_2 fequsalhw_3 weq wn fequsalhw_2 fequsalhw_2 fequsalhw_3 weq fequsalhw_1 fequsalhw_2 wal con3 al2imi mtoi fequsalhw_1 fequsalhw_2 ax6o syl impbii bitr4i $.
$}
$( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ."  (Contributed by NM, 1-Aug-2017.) $)
${
	f19.21h_0 $f wff ph $.
	f19.21h_1 $f wff ps $.
	f19.21h_2 $f set x $.
	e19.21h_0 $e |- ( ph -> A. x ph ) $.
	19.21h $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $= f19.21h_0 f19.21h_1 wi f19.21h_2 wal f19.21h_0 f19.21h_1 f19.21h_2 wal wi f19.21h_0 f19.21h_0 f19.21h_2 wal f19.21h_0 f19.21h_1 wi f19.21h_2 wal f19.21h_1 f19.21h_2 wal e19.21h_0 f19.21h_0 f19.21h_1 f19.21h_2 alim syl5 f19.21h_0 f19.21h_1 f19.21h_2 wal wi f19.21h_0 f19.21h_1 wi f19.21h_2 f19.21h_0 f19.21h_1 f19.21h_2 wal f19.21h_2 e19.21h_0 f19.21h_1 f19.21h_2 hba1 hbim f19.21h_1 f19.21h_2 wal f19.21h_1 f19.21h_0 f19.21h_1 f19.21h_2 sp imim2i alrimih impbii $.
$}
$( A closed form of ~ hbim .  (Contributed by NM, 5-Aug-1993.) $)
${
	fhbim1_0 $f wff ph $.
	fhbim1_1 $f wff ps $.
	fhbim1_2 $f set x $.
	ehbim1_0 $e |- ( ph -> A. x ph ) $.
	ehbim1_1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
	hbim1 $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $= fhbim1_0 fhbim1_1 wi fhbim1_0 fhbim1_1 fhbim1_2 wal wi fhbim1_0 fhbim1_1 wi fhbim1_2 wal fhbim1_0 fhbim1_1 fhbim1_1 fhbim1_2 wal ehbim1_1 a2i fhbim1_0 fhbim1_1 fhbim1_2 ehbim1_0 19.21h sylibr $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by NM, 5-Aug-1993.) $)
${
	fhbex_0 $f wff ph $.
	fhbex_1 $f set x $.
	fhbex_2 $f set y $.
	ehbex_0 $e |- ( ph -> A. x ph ) $.
	hbex $p |- ( E. y ph -> A. x E. y ph ) $= fhbex_0 fhbex_2 wex fhbex_0 wn fhbex_2 wal wn fhbex_1 fhbex_0 fhbex_2 df-ex fhbex_0 wn fhbex_2 wal fhbex_1 fhbex_0 wn fhbex_1 fhbex_2 fhbex_0 fhbex_1 ehbex_0 hbn hbal hbn hbxfrbi $.
$}
$( Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  But sometimes the converse does hold, as in
     ~ 19.12vv and ~ r19.12sn .  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.12_0 $f wff ph $.
	f19.12_1 $f set x $.
	f19.12_2 $f set y $.
	19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $= f19.12_0 f19.12_2 wal f19.12_1 wex f19.12_0 f19.12_1 wex f19.12_2 f19.12_0 f19.12_2 wal f19.12_2 f19.12_1 f19.12_0 f19.12_2 hba1 hbex f19.12_0 f19.12_2 wal f19.12_0 f19.12_1 f19.12_0 f19.12_2 sp eximi alrimih $.
$}
$( dvelimhw.4 $e |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $. $)
$( Proof of ~ dvelimh without using ~ ax-12 but with additional distinct
       variable conditions.  (Contributed by Andrew Salmon, 21-Jul-2011.)
       (Revised by NM, 1-Aug-2017.) $)
${
	$d x z $.
	$d y z $.
	fdvelimhw_0 $f wff ph $.
	fdvelimhw_1 $f wff ps $.
	fdvelimhw_2 $f set x $.
	fdvelimhw_3 $f set y $.
	fdvelimhw_4 $f set z $.
	edvelimhw_0 $e |- ( ph -> A. x ph ) $.
	edvelimhw_1 $e |- ( ps -> A. z ps ) $.
	edvelimhw_2 $e |- ( z = y -> ( ph <-> ps ) ) $.
	edvelimhw_3 $e |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $.
	dvelimhw $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= fdvelimhw_2 fdvelimhw_3 weq fdvelimhw_2 wal wn fdvelimhw_4 fdvelimhw_3 weq fdvelimhw_0 wi fdvelimhw_4 wal fdvelimhw_4 fdvelimhw_3 weq fdvelimhw_0 wi fdvelimhw_4 wal fdvelimhw_2 wal fdvelimhw_1 fdvelimhw_1 fdvelimhw_2 wal fdvelimhw_2 fdvelimhw_3 weq fdvelimhw_2 wal wn fdvelimhw_4 fdvelimhw_3 weq fdvelimhw_0 wi fdvelimhw_2 fdvelimhw_4 fdvelimhw_2 fdvelimhw_3 weq fdvelimhw_2 wal wn fdvelimhw_4 ax-17 fdvelimhw_2 fdvelimhw_3 weq fdvelimhw_2 wal wn fdvelimhw_4 fdvelimhw_3 weq fdvelimhw_0 fdvelimhw_2 fdvelimhw_2 fdvelimhw_3 weq fdvelimhw_2 hbn1 fdvelimhw_4 fdvelimhw_3 weq fdvelimhw_3 fdvelimhw_4 weq fdvelimhw_2 fdvelimhw_3 weq fdvelimhw_2 wal wn fdvelimhw_3 fdvelimhw_4 weq fdvelimhw_2 wal fdvelimhw_4 fdvelimhw_3 weq fdvelimhw_2 wal fdvelimhw_4 fdvelimhw_3 equcomi edvelimhw_3 fdvelimhw_3 fdvelimhw_4 weq fdvelimhw_4 fdvelimhw_3 weq fdvelimhw_2 fdvelimhw_3 fdvelimhw_4 equcomi alimi syl56 fdvelimhw_0 fdvelimhw_0 fdvelimhw_2 wal wi fdvelimhw_2 fdvelimhw_3 weq fdvelimhw_2 wal wn edvelimhw_0 a1i hbimd hbald fdvelimhw_0 fdvelimhw_1 fdvelimhw_4 fdvelimhw_3 edvelimhw_1 edvelimhw_2 equsalhw fdvelimhw_4 fdvelimhw_3 weq fdvelimhw_0 wi fdvelimhw_4 wal fdvelimhw_1 fdvelimhw_2 fdvelimhw_0 fdvelimhw_1 fdvelimhw_4 fdvelimhw_3 edvelimhw_1 edvelimhw_2 equsalhw albii 3imtr3g $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by NM, 5-Aug-1993.) $)
${
	fhban_0 $f wff ph $.
	fhban_1 $f wff ps $.
	fhban_2 $f set x $.
	ehban_0 $e |- ( ph -> A. x ph ) $.
	ehban_1 $e |- ( ps -> A. x ps ) $.
	hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $= fhban_0 fhban_1 wa fhban_0 fhban_1 wn wi wn fhban_2 fhban_0 fhban_1 df-an fhban_0 fhban_1 wn wi fhban_2 fhban_0 fhban_1 wn fhban_2 ehban_0 fhban_1 fhban_2 ehban_1 hbn hbim hbn hbxfrbi $.
$}
$( Lemma for ~ ax10 .  Similar to ~ cbv3h .  Requires distinct variables
       but avoids ~ ax-12 .  (Contributed by NM, 25-Jul-2015.) $)
${
	$d x y $.
	fcbv3hv_0 $f wff ph $.
	fcbv3hv_1 $f wff ps $.
	fcbv3hv_2 $f set x $.
	fcbv3hv_3 $f set y $.
	ecbv3hv_0 $e |- ( ph -> A. y ph ) $.
	ecbv3hv_1 $e |- ( ps -> A. x ps ) $.
	ecbv3hv_2 $e |- ( x = y -> ( ph -> ps ) ) $.
	cbv3hv $p |- ( A. x ph -> A. y ps ) $= fcbv3hv_0 fcbv3hv_2 wal fcbv3hv_0 fcbv3hv_3 wal fcbv3hv_2 wal fcbv3hv_1 fcbv3hv_3 wal fcbv3hv_0 fcbv3hv_0 fcbv3hv_3 wal fcbv3hv_2 ecbv3hv_0 alimi fcbv3hv_0 fcbv3hv_1 fcbv3hv_3 wal fcbv3hv_3 fcbv3hv_2 fcbv3hv_0 fcbv3hv_2 wal fcbv3hv_1 fcbv3hv_3 fcbv3hv_0 fcbv3hv_2 wal fcbv3hv_1 wi fcbv3hv_2 fcbv3hv_3 weq wn fcbv3hv_2 wal fcbv3hv_2 fcbv3hv_3 ax9v fcbv3hv_0 fcbv3hv_2 wal fcbv3hv_1 wi wn fcbv3hv_2 fcbv3hv_3 weq wn fcbv3hv_2 fcbv3hv_0 fcbv3hv_2 wal fcbv3hv_1 wi fcbv3hv_2 fcbv3hv_0 fcbv3hv_2 wal fcbv3hv_1 fcbv3hv_2 fcbv3hv_0 fcbv3hv_2 hba1 ecbv3hv_1 hbim hbn fcbv3hv_2 fcbv3hv_3 weq fcbv3hv_0 fcbv3hv_2 wal fcbv3hv_1 wi fcbv3hv_0 fcbv3hv_2 wal fcbv3hv_0 fcbv3hv_2 fcbv3hv_3 weq fcbv3hv_1 fcbv3hv_0 fcbv3hv_2 sp ecbv3hv_2 syl5 con3i alrimih mt3 alimi a7s syl $.
$}
$( Inference rule reversing generalization.  (Contributed by NM,
       5-Aug-1993.) $)
${
	fspi_0 $f wff ph $.
	fspi_1 $f set x $.
	espi_0 $e |- A. x ph $.
	spi $p |- ph $= fspi_0 fspi_1 wal fspi_0 espi_0 fspi_0 fspi_1 sp ax-mp $.
$}
$( Generalization of antecedent.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsps_0 $f wff ph $.
	fsps_1 $f wff ps $.
	fsps_2 $f set x $.
	esps_0 $e |- ( ph -> ps ) $.
	sps $p |- ( A. x ph -> ps ) $= fsps_0 fsps_2 wal fsps_0 fsps_1 fsps_0 fsps_2 sp esps_0 syl $.
$}
$( Deduction generalizing antecedent.  (Contributed by NM, 17-Aug-1994.) $)
${
	fspsd_0 $f wff ph $.
	fspsd_1 $f wff ps $.
	fspsd_2 $f wff ch $.
	fspsd_3 $f set x $.
	espsd_0 $e |- ( ph -> ( ps -> ch ) ) $.
	spsd $p |- ( ph -> ( A. x ps -> ch ) ) $= fspsd_1 fspsd_3 wal fspsd_1 fspsd_0 fspsd_2 fspsd_1 fspsd_3 sp espsd_0 syl5 $.
$}
$( Consequence of the definition of not-free.  (Contributed by Mario
     Carneiro, 26-Sep-2016.) $)
${
	fnfr_0 $f wff ph $.
	fnfr_1 $f set x $.
	nfr $p |- ( F/ x ph -> ( ph -> A. x ph ) ) $= fnfr_0 fnfr_1 wnf fnfr_0 fnfr_0 fnfr_1 wal wi fnfr_1 wal fnfr_0 fnfr_0 fnfr_1 wal wi fnfr_0 fnfr_1 df-nf fnfr_0 fnfr_0 fnfr_1 wal wi fnfr_1 sp sylbi $.
$}
$( Consequence of the definition of not-free.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
${
	fnfri_0 $f wff ph $.
	fnfri_1 $f set x $.
	enfri_0 $e |- F/ x ph $.
	nfri $p |- ( ph -> A. x ph ) $= fnfri_0 fnfri_1 wnf fnfri_0 fnfri_0 fnfri_1 wal wi enfri_0 fnfri_0 fnfri_1 nfr ax-mp $.
$}
$( Consequence of the definition of not-free in a context.  (Contributed by
       Mario Carneiro, 11-Aug-2016.) $)
${
	fnfrd_0 $f wff ph $.
	fnfrd_1 $f wff ps $.
	fnfrd_2 $f set x $.
	enfrd_0 $e |- ( ph -> F/ x ps ) $.
	nfrd $p |- ( ph -> ( ps -> A. x ps ) ) $= fnfrd_0 fnfrd_1 fnfrd_2 wnf fnfrd_1 fnfrd_1 fnfrd_2 wal wi enfrd_0 fnfrd_1 fnfrd_2 nfr syl $.
$}
$( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
${
	falimd_0 $f wff ph $.
	falimd_1 $f wff ps $.
	falimd_2 $f wff ch $.
	falimd_3 $f set x $.
	ealimd_0 $e |- F/ x ph $.
	ealimd_1 $e |- ( ph -> ( ps -> ch ) ) $.
	alimd $p |- ( ph -> ( A. x ps -> A. x ch ) ) $= falimd_0 falimd_1 falimd_2 falimd_3 falimd_0 falimd_3 ealimd_0 nfri ealimd_1 alimdh $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
${
	falrimi_0 $f wff ph $.
	falrimi_1 $f wff ps $.
	falrimi_2 $f set x $.
	ealrimi_0 $e |- F/ x ph $.
	ealrimi_1 $e |- ( ph -> ps ) $.
	alrimi $p |- ( ph -> A. x ps ) $= falrimi_0 falrimi_1 falrimi_2 falrimi_0 falrimi_2 ealrimi_0 nfri ealrimi_1 alrimih $.
$}
$( Deduce that ` x ` is not free in ` ph ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
${
	fnfd_0 $f wff ph $.
	fnfd_1 $f wff ps $.
	fnfd_2 $f set x $.
	enfd_0 $e |- F/ x ph $.
	enfd_1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
	nfd $p |- ( ph -> F/ x ps ) $= fnfd_0 fnfd_1 fnfd_1 fnfd_2 wal wi fnfd_2 wal fnfd_1 fnfd_2 wnf fnfd_0 fnfd_1 fnfd_1 fnfd_2 wal wi fnfd_2 enfd_0 enfd_1 alrimi fnfd_1 fnfd_2 df-nf sylibr $.
$}
$( Deduce that ` x ` is not free in ` ph ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
${
	fnfdh_0 $f wff ph $.
	fnfdh_1 $f wff ps $.
	fnfdh_2 $f set x $.
	enfdh_0 $e |- ( ph -> A. x ph ) $.
	enfdh_1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
	nfdh $p |- ( ph -> F/ x ps ) $= fnfdh_0 fnfdh_1 fnfdh_2 fnfdh_0 fnfdh_2 enfdh_0 nfi enfdh_1 nfd $.
$}
$( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
${
	falrimdd_0 $f wff ph $.
	falrimdd_1 $f wff ps $.
	falrimdd_2 $f wff ch $.
	falrimdd_3 $f set x $.
	ealrimdd_0 $e |- F/ x ph $.
	ealrimdd_1 $e |- ( ph -> F/ x ps ) $.
	ealrimdd_2 $e |- ( ph -> ( ps -> ch ) ) $.
	alrimdd $p |- ( ph -> ( ps -> A. x ch ) ) $= falrimdd_0 falrimdd_1 falrimdd_1 falrimdd_3 wal falrimdd_2 falrimdd_3 wal falrimdd_0 falrimdd_1 falrimdd_3 ealrimdd_1 nfrd falrimdd_0 falrimdd_1 falrimdd_2 falrimdd_3 ealrimdd_0 ealrimdd_2 alimd syld $.
$}
$( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
${
	falrimd_0 $f wff ph $.
	falrimd_1 $f wff ps $.
	falrimd_2 $f wff ch $.
	falrimd_3 $f set x $.
	ealrimd_0 $e |- F/ x ph $.
	ealrimd_1 $e |- F/ x ps $.
	ealrimd_2 $e |- ( ph -> ( ps -> ch ) ) $.
	alrimd $p |- ( ph -> ( ps -> A. x ch ) ) $= falrimd_0 falrimd_1 falrimd_2 falrimd_3 ealrimd_0 falrimd_1 falrimd_3 wnf falrimd_0 ealrimd_1 a1i ealrimd_2 alrimdd $.
$}
$( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
${
	feximd_0 $f wff ph $.
	feximd_1 $f wff ps $.
	feximd_2 $f wff ch $.
	feximd_3 $f set x $.
	eeximd_0 $e |- F/ x ph $.
	eeximd_1 $e |- ( ph -> ( ps -> ch ) ) $.
	eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $= feximd_0 feximd_1 feximd_2 feximd_3 feximd_0 feximd_3 eeximd_0 nfri eeximd_1 eximdh $.
$}
$( Deduction for generalization rule for negated wff.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
${
	fnexd_0 $f wff ph $.
	fnexd_1 $f wff ps $.
	fnexd_2 $f set x $.
	enexd_0 $e |- F/ x ph $.
	enexd_1 $e |- ( ph -> -. ps ) $.
	nexd $p |- ( ph -> -. E. x ps ) $= fnexd_0 fnexd_1 fnexd_2 fnexd_0 fnexd_2 enexd_0 nfri enexd_1 nexdh $.
$}
$( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	falbid_0 $f wff ph $.
	falbid_1 $f wff ps $.
	falbid_2 $f wff ch $.
	falbid_3 $f set x $.
	ealbid_0 $e |- F/ x ph $.
	ealbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $= falbid_0 falbid_1 falbid_2 falbid_3 falbid_0 falbid_3 ealbid_0 nfri ealbid_1 albidh $.
$}
$( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	fexbid_0 $f wff ph $.
	fexbid_1 $f wff ps $.
	fexbid_2 $f wff ch $.
	fexbid_3 $f set x $.
	eexbid_0 $e |- F/ x ph $.
	eexbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $= fexbid_0 fexbid_1 fexbid_2 fexbid_3 fexbid_0 fexbid_3 eexbid_0 nfri eexbid_1 exbidh $.
$}
$( An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 4-Oct-2016.) $)
${
	fnfbidf_0 $f wff ph $.
	fnfbidf_1 $f wff ps $.
	fnfbidf_2 $f wff ch $.
	fnfbidf_3 $f set x $.
	enfbidf_0 $e |- F/ x ph $.
	enfbidf_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	nfbidf $p |- ( ph -> ( F/ x ps <-> F/ x ch ) ) $= fnfbidf_0 fnfbidf_1 fnfbidf_1 fnfbidf_3 wal wi fnfbidf_3 wal fnfbidf_2 fnfbidf_2 fnfbidf_3 wal wi fnfbidf_3 wal fnfbidf_1 fnfbidf_3 wnf fnfbidf_2 fnfbidf_3 wnf fnfbidf_0 fnfbidf_1 fnfbidf_1 fnfbidf_3 wal wi fnfbidf_2 fnfbidf_2 fnfbidf_3 wal wi fnfbidf_3 enfbidf_0 fnfbidf_0 fnfbidf_1 fnfbidf_2 fnfbidf_1 fnfbidf_3 wal fnfbidf_2 fnfbidf_3 wal enfbidf_1 fnfbidf_0 fnfbidf_1 fnfbidf_2 fnfbidf_3 enfbidf_0 enfbidf_1 albid imbi12d albid fnfbidf_1 fnfbidf_3 df-nf fnfbidf_2 fnfbidf_3 df-nf 3bitr4g $.
$}
$( Abbreviated version of ~ ax6o .  (Contributed by NM, 5-Aug-1993.) $)
${
	fa6e_0 $f wff ph $.
	fa6e_1 $f set x $.
	a6e $p |- ( E. x A. x ph -> ph ) $= fa6e_0 fa6e_1 wal fa6e_1 wex fa6e_0 fa6e_1 wal wn fa6e_1 wal wn fa6e_0 fa6e_0 fa6e_1 wal fa6e_1 df-ex fa6e_0 fa6e_1 ax6o sylbi $.
$}
$( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
${
	fnfa1_0 $f wff ph $.
	fnfa1_1 $f set x $.
	nfa1 $p |- F/ x A. x ph $= fnfa1_0 fnfa1_1 wal fnfa1_1 fnfa1_0 fnfa1_1 hba1 nfi $.
$}
$( ` x ` is not free in ` F/ x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
${
	fnfnf1_0 $f wff ph $.
	fnfnf1_1 $f set x $.
	nfnf1 $p |- F/ x F/ x ph $= fnfnf1_0 fnfnf1_1 wnf fnfnf1_0 fnfnf1_0 fnfnf1_1 wal wi fnfnf1_1 wal fnfnf1_1 fnfnf1_0 fnfnf1_1 df-nf fnfnf1_0 fnfnf1_0 fnfnf1_1 wal wi fnfnf1_1 nfa1 nfxfr $.
$}
$( Inference version of ~ ax5o .  (Contributed by NM, 5-Aug-1993.) $)
${
	fa5i_0 $f wff ph $.
	fa5i_1 $f wff ps $.
	fa5i_2 $f set x $.
	ea5i_0 $e |- ( A. x ph -> ps ) $.
	a5i $p |- ( A. x ph -> A. x ps ) $= fa5i_0 fa5i_2 wal fa5i_1 fa5i_2 fa5i_0 fa5i_2 nfa1 ea5i_0 alrimi $.
$}
$( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by NM, 14-Sep-2003.) $)
${
	fhb3an_0 $f wff ph $.
	fhb3an_1 $f wff ps $.
	fhb3an_2 $f wff ch $.
	fhb3an_3 $f set x $.
	ehb3an_0 $e |- ( ph -> A. x ph ) $.
	ehb3an_1 $e |- ( ps -> A. x ps ) $.
	ehb3an_2 $e |- ( ch -> A. x ch ) $.
	hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $= fhb3an_0 fhb3an_1 fhb3an_2 w3a fhb3an_0 fhb3an_1 wa fhb3an_2 wa fhb3an_3 fhb3an_0 fhb3an_1 fhb3an_2 df-3an fhb3an_0 fhb3an_1 wa fhb3an_2 fhb3an_3 fhb3an_0 fhb3an_1 fhb3an_3 ehb3an_0 ehb3an_1 hban ehb3an_2 hban hbxfrbi $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	fnfnd_0 $f wff ph $.
	fnfnd_1 $f wff ps $.
	fnfnd_2 $f set x $.
	enfnd_0 $e |- ( ph -> F/ x ps ) $.
	nfnd $p |- ( ph -> F/ x -. ps ) $= fnfnd_0 fnfnd_1 fnfnd_2 wnf fnfnd_1 wn fnfnd_2 wnf enfnd_0 fnfnd_1 fnfnd_2 wnf fnfnd_1 wn fnfnd_2 fnfnd_1 fnfnd_2 nfnf1 fnfnd_1 wn fnfnd_1 fnfnd_2 wal wn fnfnd_2 wal fnfnd_1 fnfnd_2 wnf fnfnd_1 wn fnfnd_2 wal fnfnd_1 fnfnd_2 wal wn fnfnd_2 wal fnfnd_1 fnfnd_1 fnfnd_2 ax6o con1i fnfnd_1 fnfnd_2 wnf fnfnd_1 fnfnd_1 fnfnd_2 wal wi fnfnd_2 wal fnfnd_1 fnfnd_2 wal wn fnfnd_2 wal fnfnd_1 wn fnfnd_2 wal wi fnfnd_1 fnfnd_2 df-nf fnfnd_1 fnfnd_1 fnfnd_2 wal wi fnfnd_1 fnfnd_2 wal wn fnfnd_1 wn fnfnd_2 fnfnd_1 fnfnd_1 fnfnd_2 wal con3 al2imi sylbi syl5 nfd syl $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	fnfimd_0 $f wff ph $.
	fnfimd_1 $f wff ps $.
	fnfimd_2 $f wff ch $.
	fnfimd_3 $f set x $.
	enfimd_0 $e |- ( ph -> F/ x ps ) $.
	enfimd_1 $e |- ( ph -> F/ x ch ) $.
	nfimd $p |- ( ph -> F/ x ( ps -> ch ) ) $= fnfimd_0 fnfimd_1 fnfimd_3 wnf fnfimd_2 fnfimd_3 wnf fnfimd_1 fnfimd_2 wi fnfimd_3 wnf enfimd_0 enfimd_1 fnfimd_1 fnfimd_1 fnfimd_3 wal wi fnfimd_3 wal fnfimd_2 fnfimd_2 fnfimd_3 wal wi fnfimd_3 wal wa fnfimd_1 fnfimd_2 wi fnfimd_1 fnfimd_2 wi fnfimd_3 wal wi fnfimd_3 wal fnfimd_1 fnfimd_3 wnf fnfimd_2 fnfimd_3 wnf wa fnfimd_1 fnfimd_2 wi fnfimd_3 wnf fnfimd_1 fnfimd_1 fnfimd_3 wal wi fnfimd_3 wal fnfimd_2 fnfimd_2 fnfimd_3 wal wi fnfimd_3 wal fnfimd_1 fnfimd_2 wi fnfimd_1 fnfimd_2 wi fnfimd_3 wal wi fnfimd_3 wal fnfimd_1 fnfimd_1 fnfimd_3 wal wi fnfimd_3 wal fnfimd_2 fnfimd_2 fnfimd_3 wal wi fnfimd_1 fnfimd_2 wi fnfimd_1 fnfimd_2 wi fnfimd_3 wal wi fnfimd_3 fnfimd_1 fnfimd_1 fnfimd_3 wal wi fnfimd_3 nfa1 fnfimd_1 fnfimd_1 fnfimd_3 wal wi fnfimd_3 wal fnfimd_1 wn fnfimd_1 wn fnfimd_3 wal wi fnfimd_2 fnfimd_2 fnfimd_3 wal wi fnfimd_1 fnfimd_2 wi fnfimd_1 fnfimd_2 wi fnfimd_3 wal wi wi fnfimd_1 fnfimd_3 hbnt fnfimd_1 wn fnfimd_1 wn fnfimd_3 wal wi fnfimd_2 fnfimd_2 fnfimd_3 wal wi fnfimd_1 fnfimd_2 wi fnfimd_1 fnfimd_2 wi fnfimd_3 wal wi fnfimd_1 wn fnfimd_1 wn fnfimd_3 wal wi fnfimd_2 fnfimd_2 fnfimd_3 wal wi wa fnfimd_1 fnfimd_2 fnfimd_1 fnfimd_2 wi fnfimd_3 wal fnfimd_1 wn fnfimd_1 wn fnfimd_3 wal wi fnfimd_1 wn fnfimd_1 fnfimd_2 wi fnfimd_3 wal wi fnfimd_2 fnfimd_2 fnfimd_3 wal wi fnfimd_1 wn fnfimd_3 wal fnfimd_1 fnfimd_2 wi fnfimd_3 wal fnfimd_1 wn fnfimd_1 wn fnfimd_1 fnfimd_2 wi fnfimd_3 fnfimd_1 fnfimd_2 pm2.21 alimi imim2i adantr fnfimd_2 fnfimd_2 fnfimd_3 wal wi fnfimd_2 fnfimd_1 fnfimd_2 wi fnfimd_3 wal wi fnfimd_1 wn fnfimd_1 wn fnfimd_3 wal wi fnfimd_2 fnfimd_3 wal fnfimd_1 fnfimd_2 wi fnfimd_3 wal fnfimd_2 fnfimd_2 fnfimd_1 fnfimd_2 wi fnfimd_3 fnfimd_2 fnfimd_1 ax-1 alimi imim2i adantl jad ex syl alimd imp fnfimd_1 fnfimd_3 wnf fnfimd_1 fnfimd_1 fnfimd_3 wal wi fnfimd_3 wal fnfimd_2 fnfimd_3 wnf fnfimd_2 fnfimd_2 fnfimd_3 wal wi fnfimd_3 wal fnfimd_1 fnfimd_3 df-nf fnfimd_2 fnfimd_3 df-nf anbi12i fnfimd_1 fnfimd_2 wi fnfimd_3 df-nf 3imtr4i syl2anc $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	fnfbid_0 $f wff ph $.
	fnfbid_1 $f wff ps $.
	fnfbid_2 $f wff ch $.
	fnfbid_3 $f set x $.
	enfbid_0 $e |- ( ph -> F/ x ps ) $.
	enfbid_1 $e |- ( ph -> F/ x ch ) $.
	nfbid $p |- ( ph -> F/ x ( ps <-> ch ) ) $= fnfbid_1 fnfbid_2 wb fnfbid_1 fnfbid_2 wi fnfbid_2 fnfbid_1 wi wn wi wn fnfbid_0 fnfbid_3 fnfbid_1 fnfbid_2 dfbi1 fnfbid_0 fnfbid_1 fnfbid_2 wi fnfbid_2 fnfbid_1 wi wn wi fnfbid_3 fnfbid_0 fnfbid_1 fnfbid_2 wi fnfbid_2 fnfbid_1 wi wn fnfbid_3 fnfbid_0 fnfbid_1 fnfbid_2 fnfbid_3 enfbid_0 enfbid_1 nfimd fnfbid_0 fnfbid_2 fnfbid_1 wi fnfbid_3 fnfbid_0 fnfbid_2 fnfbid_1 fnfbid_3 enfbid_1 enfbid_0 nfimd nfnd nfimd nfnd nfxfrd $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 7-Oct-2016.) $)
${
	fnfand_0 $f wff ph $.
	fnfand_1 $f wff ps $.
	fnfand_2 $f wff ch $.
	fnfand_3 $f set x $.
	enfand_0 $e |- ( ph -> F/ x ps ) $.
	enfand_1 $e |- ( ph -> F/ x ch ) $.
	nfand $p |- ( ph -> F/ x ( ps /\ ch ) ) $= fnfand_1 fnfand_2 wa fnfand_1 fnfand_2 wn wi wn fnfand_0 fnfand_3 fnfand_1 fnfand_2 df-an fnfand_0 fnfand_1 fnfand_2 wn wi fnfand_3 fnfand_0 fnfand_1 fnfand_2 wn fnfand_3 enfand_0 fnfand_0 fnfand_2 fnfand_3 enfand_1 nfnd nfimd nfnd nfxfrd $.
$}
$( Deduction form of bound-variable hypothesis builder ~ nf3an .
       (Contributed by NM, 17-Feb-2013.)  (Revised by Mario Carneiro,
       16-Oct-2016.) $)
${
	fnf3and_0 $f wff ph $.
	fnf3and_1 $f wff ps $.
	fnf3and_2 $f wff ch $.
	fnf3and_3 $f wff th $.
	fnf3and_4 $f set x $.
	enf3and_0 $e |- ( ph -> F/ x ps ) $.
	enf3and_1 $e |- ( ph -> F/ x ch ) $.
	enf3and_2 $e |- ( ph -> F/ x th ) $.
	nf3and $p |- ( ph -> F/ x ( ps /\ ch /\ th ) ) $= fnf3and_1 fnf3and_2 fnf3and_3 w3a fnf3and_1 fnf3and_2 wa fnf3and_3 wa fnf3and_0 fnf3and_4 fnf3and_1 fnf3and_2 fnf3and_3 df-3an fnf3and_0 fnf3and_1 fnf3and_2 wa fnf3and_3 fnf3and_4 fnf3and_0 fnf3and_1 fnf3and_2 fnf3and_4 enf3and_0 enf3and_1 nfand enf3and_2 nfand nfxfrd $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfn_0 $f wff ph $.
	fnfn_1 $f set x $.
	enfn_0 $e |- F/ x ph $.
	nfn $p |- F/ x -. ph $= fnfn_0 wn fnfn_1 wnf wtru fnfn_0 fnfn_1 fnfn_0 fnfn_1 wnf wtru enfn_0 a1i nfnd trud $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfal_0 $f wff ph $.
	fnfal_1 $f set x $.
	fnfal_2 $f set y $.
	enfal_0 $e |- F/ x ph $.
	nfal $p |- F/ x A. y ph $= fnfal_0 fnfal_2 wal fnfal_1 fnfal_0 fnfal_1 fnfal_2 fnfal_0 fnfal_1 enfal_0 nfri hbal nfi $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfex_0 $f wff ph $.
	fnfex_1 $f set x $.
	fnfex_2 $f set y $.
	enfex_0 $e |- F/ x ph $.
	nfex $p |- F/ x E. y ph $= fnfex_0 fnfex_2 wex fnfex_0 wn fnfex_2 wal wn fnfex_1 fnfex_0 fnfex_2 df-ex fnfex_0 wn fnfex_2 wal fnfex_1 fnfex_0 wn fnfex_1 fnfex_2 fnfex_0 fnfex_1 enfex_0 nfn nfal nfn nfxfr $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` F/ y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfnf_0 $f wff ph $.
	fnfnf_1 $f set x $.
	fnfnf_2 $f set y $.
	enfnf_0 $e |- F/ x ph $.
	nfnf $p |- F/ x F/ y ph $= fnfnf_0 fnfnf_2 wnf fnfnf_0 fnfnf_0 fnfnf_2 wal wi fnfnf_2 wal fnfnf_1 fnfnf_0 fnfnf_2 df-nf fnfnf_0 fnfnf_0 fnfnf_2 wal wi fnfnf_1 fnfnf_2 fnfnf_0 fnfnf_0 fnfnf_2 wal wi fnfnf_1 wnf wtru fnfnf_0 fnfnf_0 fnfnf_2 wal fnfnf_1 fnfnf_0 fnfnf_1 wnf wtru enfnf_0 a1i fnfnf_0 fnfnf_2 wal fnfnf_1 wnf wtru fnfnf_0 fnfnf_1 fnfnf_2 enfnf_0 nfal a1i nfimd trud nfal nfxfr $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfim_0 $f wff ph $.
	fnfim_1 $f wff ps $.
	fnfim_2 $f set x $.
	enfim_0 $e |- F/ x ph $.
	enfim_1 $e |- F/ x ps $.
	nfim $p |- F/ x ( ph -> ps ) $= fnfim_0 fnfim_1 wi fnfim_2 wnf wtru fnfim_0 fnfim_1 fnfim_2 fnfim_0 fnfim_2 wnf wtru enfim_0 a1i fnfim_1 fnfim_2 wnf wtru enfim_1 a1i nfimd trud $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph \/ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfor_0 $f wff ph $.
	fnfor_1 $f wff ps $.
	fnfor_2 $f set x $.
	enfor_0 $e |- F/ x ph $.
	enfor_1 $e |- F/ x ps $.
	nfor $p |- F/ x ( ph \/ ps ) $= fnfor_0 fnfor_1 wo fnfor_0 wn fnfor_1 wi fnfor_2 fnfor_0 fnfor_1 df-or fnfor_0 wn fnfor_1 fnfor_2 fnfor_0 fnfor_2 enfor_0 nfn enfor_1 nfim nfxfr $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfan_0 $f wff ph $.
	fnfan_1 $f wff ps $.
	fnfan_2 $f set x $.
	enfan_0 $e |- F/ x ph $.
	enfan_1 $e |- F/ x ps $.
	nfan $p |- F/ x ( ph /\ ps ) $= fnfan_0 fnfan_1 wa fnfan_0 fnfan_1 wn wi wn fnfan_2 fnfan_0 fnfan_1 df-an fnfan_0 fnfan_1 wn wi fnfan_2 fnfan_0 fnfan_1 wn fnfan_2 enfan_0 fnfan_1 fnfan_2 enfan_1 nfn nfim nfn nfxfr $.
$}
$( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfbi_0 $f wff ph $.
	fnfbi_1 $f wff ps $.
	fnfbi_2 $f set x $.
	enfbi_0 $e |- F/ x ph $.
	enfbi_1 $e |- F/ x ps $.
	nfbi $p |- F/ x ( ph <-> ps ) $= fnfbi_0 fnfbi_1 wb fnfbi_0 fnfbi_1 wi fnfbi_1 fnfbi_0 wi wa fnfbi_2 fnfbi_0 fnfbi_1 dfbi2 fnfbi_0 fnfbi_1 wi fnfbi_1 fnfbi_0 wi fnfbi_2 fnfbi_0 fnfbi_1 fnfbi_2 enfbi_0 enfbi_1 nfim fnfbi_1 fnfbi_0 fnfbi_2 enfbi_1 enfbi_0 nfim nfan nfxfr $.
$}
$( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph \/ ps \/ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	fnf3or_0 $f wff ph $.
	fnf3or_1 $f wff ps $.
	fnf3or_2 $f wff ch $.
	fnf3or_3 $f set x $.
	enf3or_0 $e |- F/ x ph $.
	enf3or_1 $e |- F/ x ps $.
	enf3or_2 $e |- F/ x ch $.
	nf3or $p |- F/ x ( ph \/ ps \/ ch ) $= fnf3or_0 fnf3or_1 fnf3or_2 w3o fnf3or_0 fnf3or_1 wo fnf3or_2 wo fnf3or_3 fnf3or_0 fnf3or_1 fnf3or_2 df-3or fnf3or_0 fnf3or_1 wo fnf3or_2 fnf3or_3 fnf3or_0 fnf3or_1 fnf3or_3 enf3or_0 enf3or_1 nfor enf3or_2 nfor nfxfr $.
$}
$( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	fnf3an_0 $f wff ph $.
	fnf3an_1 $f wff ps $.
	fnf3an_2 $f wff ch $.
	fnf3an_3 $f set x $.
	enf3an_0 $e |- F/ x ph $.
	enf3an_1 $e |- F/ x ps $.
	enf3an_2 $e |- F/ x ch $.
	nf3an $p |- F/ x ( ph /\ ps /\ ch ) $= fnf3an_0 fnf3an_1 fnf3an_2 w3a fnf3an_0 fnf3an_1 wa fnf3an_2 wa fnf3an_3 fnf3an_0 fnf3an_1 fnf3an_2 df-3an fnf3an_0 fnf3an_1 wa fnf3an_2 fnf3an_3 fnf3an_0 fnf3an_1 fnf3an_3 enf3an_0 enf3an_1 nfan enf3an_2 nfan nfxfr $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	fnfald_0 $f wff ph $.
	fnfald_1 $f wff ps $.
	fnfald_2 $f set x $.
	fnfald_3 $f set y $.
	enfald_0 $e |- F/ y ph $.
	enfald_1 $e |- ( ph -> F/ x ps ) $.
	nfald $p |- ( ph -> F/ x A. y ps ) $= fnfald_0 fnfald_1 fnfald_2 wnf fnfald_3 wal fnfald_1 fnfald_3 wal fnfald_2 wnf fnfald_0 fnfald_1 fnfald_2 wnf fnfald_3 enfald_0 enfald_1 alrimi fnfald_1 fnfald_2 wnf fnfald_3 wal fnfald_1 fnfald_3 wal fnfald_2 fnfald_1 fnfald_2 wnf fnfald_2 fnfald_3 fnfald_1 fnfald_2 nfnf1 nfal fnfald_1 fnfald_2 wnf fnfald_3 wal fnfald_1 fnfald_3 wal fnfald_1 fnfald_2 wal fnfald_3 wal fnfald_1 fnfald_3 wal fnfald_2 wal fnfald_1 fnfald_2 wnf fnfald_1 fnfald_1 fnfald_2 wal fnfald_3 fnfald_1 fnfald_2 nfr al2imi fnfald_1 fnfald_3 fnfald_2 ax-7 syl6 nfd syl $.
$}
$( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	fnfexd_0 $f wff ph $.
	fnfexd_1 $f wff ps $.
	fnfexd_2 $f set x $.
	fnfexd_3 $f set y $.
	enfexd_0 $e |- F/ y ph $.
	enfexd_1 $e |- ( ph -> F/ x ps ) $.
	nfexd $p |- ( ph -> F/ x E. y ps ) $= fnfexd_1 fnfexd_3 wex fnfexd_1 wn fnfexd_3 wal wn fnfexd_0 fnfexd_2 fnfexd_1 fnfexd_3 df-ex fnfexd_0 fnfexd_1 wn fnfexd_3 wal fnfexd_2 fnfexd_0 fnfexd_1 wn fnfexd_2 fnfexd_3 enfexd_0 fnfexd_0 fnfexd_1 fnfexd_2 enfexd_1 nfnd nfald nfnd nfxfrd $.
$}
$( Lemma 24 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
${
	fnfa2_0 $f wff ph $.
	fnfa2_1 $f set x $.
	fnfa2_2 $f set y $.
	nfa2 $p |- F/ x A. y A. x ph $= fnfa2_0 fnfa2_1 wal fnfa2_1 fnfa2_2 fnfa2_0 fnfa2_1 nfa1 nfal $.
$}
$( Lemma 23 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
${
	fnfia1_0 $f wff ph $.
	fnfia1_1 $f wff ps $.
	fnfia1_2 $f set x $.
	nfia1 $p |- F/ x ( A. x ph -> A. x ps ) $= fnfia1_0 fnfia1_2 wal fnfia1_1 fnfia1_2 wal fnfia1_2 fnfia1_0 fnfia1_2 nfa1 fnfia1_1 fnfia1_2 nfa1 nfim $.
$}
$( The analog in our "pure" predicate calculus of the Brouwer axiom (B) of
     modal logic S5.  (Contributed by NM, 5-Oct-2005.) $)
${
	fmodal-b_0 $f wff ph $.
	fmodal-b_1 $f set x $.
	modal-b $p |- ( ph -> A. x -. A. x -. ph ) $= fmodal-b_0 wn fmodal-b_1 wal wn fmodal-b_1 wal fmodal-b_0 fmodal-b_0 wn fmodal-b_1 ax6o con4i $.
$}
$( Theorem 19.2 of [Margaris] p. 89, generalized to use two set variables.
     (Contributed by O'Cat, 31-Mar-2008.) $)
${
	f19.2g_0 $f wff ph $.
	f19.2g_1 $f set x $.
	f19.2g_2 $f set y $.
	19.2g $p |- ( A. x ph -> E. y ph ) $= f19.2g_0 f19.2g_0 f19.2g_2 wex f19.2g_1 f19.2g_0 f19.2g_2 19.8a sps $.
$}
$( A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)
${
	f19.3_0 $f wff ph $.
	f19.3_1 $f set x $.
	e19.3_0 $e |- F/ x ph $.
	19.3 $p |- ( A. x ph <-> ph ) $= f19.3_0 f19.3_1 wal f19.3_0 f19.3_0 f19.3_1 sp f19.3_0 f19.3_1 e19.3_0 nfri impbii $.
$}
$( A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.)  (Revised
     by Mario Carneiro, 24-Sep-2016.) $)
${
	f19.9t_0 $f wff ph $.
	f19.9t_1 $f set x $.
	19.9t $p |- ( F/ x ph -> ( E. x ph <-> ph ) ) $= f19.9t_0 f19.9t_1 wnf f19.9t_0 f19.9t_1 wex f19.9t_0 f19.9t_0 f19.9t_1 wex f19.9t_0 wn f19.9t_1 wal wn f19.9t_0 f19.9t_1 wnf f19.9t_0 f19.9t_0 f19.9t_1 df-ex f19.9t_0 f19.9t_1 wnf f19.9t_0 f19.9t_0 wn f19.9t_1 wal f19.9t_0 f19.9t_1 wnf f19.9t_0 wn f19.9t_1 f19.9t_0 f19.9t_1 wnf f19.9t_0 f19.9t_1 f19.9t_0 f19.9t_1 wnf id nfnd nfrd con1d syl5bi f19.9t_0 f19.9t_1 19.8a impbid1 $.
$}
$( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
${
	f19.9_0 $f wff ph $.
	f19.9_1 $f set x $.
	e19.9_0 $e |- F/ x ph $.
	19.9 $p |- ( E. x ph <-> ph ) $= f19.9_0 f19.9_1 wnf f19.9_0 f19.9_1 wex f19.9_0 wb e19.9_0 f19.9_0 f19.9_1 19.9t ax-mp $.
$}
$( A deduction version of one direction of ~ 19.9 .  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
${
	f19.9d_0 $f wff ph $.
	f19.9d_1 $f wff ps $.
	f19.9d_2 $f set x $.
	e19.9d_0 $e |- ( ps -> F/ x ph ) $.
	19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $= f19.9d_1 f19.9d_0 f19.9d_2 wex f19.9d_0 f19.9d_1 f19.9d_0 f19.9d_2 wnf f19.9d_0 f19.9d_2 wex f19.9d_0 wb e19.9d_0 f19.9d_0 f19.9d_2 19.9t syl biimpd $.
$}
$( One direction of Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM,
     5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
${
	fexcomim_0 $f wff ph $.
	fexcomim_1 $f set x $.
	fexcomim_2 $f set y $.
	excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $= fexcomim_0 fexcomim_2 wex fexcomim_1 wex fexcomim_0 fexcomim_1 wex fexcomim_2 wex fexcomim_1 wex fexcomim_0 fexcomim_1 wex fexcomim_2 wex fexcomim_0 fexcomim_0 fexcomim_1 wex fexcomim_1 fexcomim_2 fexcomim_0 fexcomim_1 19.8a 2eximi fexcomim_0 fexcomim_1 wex fexcomim_2 wex fexcomim_1 fexcomim_0 fexcomim_1 wex fexcomim_1 fexcomim_2 fexcomim_0 fexcomim_1 nfe1 nfex 19.9 sylib $.
$}
$( Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
${
	fexcom_0 $f wff ph $.
	fexcom_1 $f set x $.
	fexcom_2 $f set y $.
	excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $= fexcom_0 fexcom_2 wex fexcom_1 wex fexcom_0 fexcom_1 wex fexcom_2 wex fexcom_0 fexcom_1 fexcom_2 excomim fexcom_0 fexcom_2 fexcom_1 excomim impbii $.
$}
$( Theorem 19.16 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.16_0 $f wff ph $.
	f19.16_1 $f wff ps $.
	f19.16_2 $f set x $.
	e19.16_0 $e |- F/ x ph $.
	19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $= f19.16_0 f19.16_0 f19.16_2 wal f19.16_0 f19.16_1 wb f19.16_2 wal f19.16_1 f19.16_2 wal f19.16_0 f19.16_2 e19.16_0 19.3 f19.16_0 f19.16_1 f19.16_2 albi syl5bbr $.
$}
$( Theorem 19.17 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.17_0 $f wff ph $.
	f19.17_1 $f wff ps $.
	f19.17_2 $f set x $.
	e19.17_0 $e |- F/ x ps $.
	19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $= f19.17_0 f19.17_1 wb f19.17_2 wal f19.17_0 f19.17_2 wal f19.17_1 f19.17_2 wal f19.17_1 f19.17_0 f19.17_1 f19.17_2 albi f19.17_1 f19.17_2 e19.17_0 19.3 syl6bb $.
$}
$( Theorem 19.19 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.19_0 $f wff ph $.
	f19.19_1 $f wff ps $.
	f19.19_2 $f set x $.
	e19.19_0 $e |- F/ x ph $.
	19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $= f19.19_0 f19.19_0 f19.19_2 wex f19.19_0 f19.19_1 wb f19.19_2 wal f19.19_1 f19.19_2 wex f19.19_0 f19.19_2 e19.19_0 19.9 f19.19_0 f19.19_1 f19.19_2 exbi syl5bbr $.
$}
$( Closed form of Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
     27-May-1997.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
${
	f19.21t_0 $f wff ph $.
	f19.21t_1 $f wff ps $.
	f19.21t_2 $f set x $.
	19.21t $p |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $= f19.21t_0 f19.21t_2 wnf f19.21t_0 f19.21t_1 wi f19.21t_2 wal f19.21t_0 f19.21t_1 f19.21t_2 wal wi f19.21t_0 f19.21t_2 wnf f19.21t_0 f19.21t_0 f19.21t_2 wal f19.21t_0 f19.21t_1 wi f19.21t_2 wal f19.21t_1 f19.21t_2 wal f19.21t_0 f19.21t_2 wnf f19.21t_0 f19.21t_2 f19.21t_0 f19.21t_2 wnf id nfrd f19.21t_0 f19.21t_1 f19.21t_2 alim syl9 f19.21t_0 f19.21t_2 wnf f19.21t_0 f19.21t_1 f19.21t_2 wal wi f19.21t_0 f19.21t_1 f19.21t_2 wal wi f19.21t_2 wal f19.21t_0 f19.21t_1 wi f19.21t_2 wal f19.21t_0 f19.21t_2 wnf f19.21t_0 f19.21t_1 f19.21t_2 wal wi f19.21t_2 f19.21t_0 f19.21t_2 wnf f19.21t_0 f19.21t_1 f19.21t_2 wal f19.21t_2 f19.21t_0 f19.21t_2 wnf id f19.21t_1 f19.21t_2 wal f19.21t_2 wnf f19.21t_0 f19.21t_2 wnf f19.21t_1 f19.21t_2 nfa1 a1i nfimd nfrd f19.21t_0 f19.21t_1 f19.21t_2 wal wi f19.21t_0 f19.21t_1 wi f19.21t_2 f19.21t_1 f19.21t_2 wal f19.21t_1 f19.21t_0 f19.21t_1 f19.21t_2 sp imim2i alimi syl6 impbid $.
$}
$( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ."  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
${
	f19.21_0 $f wff ph $.
	f19.21_1 $f wff ps $.
	f19.21_2 $f set x $.
	e19.21_0 $e |- F/ x ph $.
	19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $= f19.21_0 f19.21_2 wnf f19.21_0 f19.21_1 wi f19.21_2 wal f19.21_0 f19.21_1 f19.21_2 wal wi wb e19.21_0 f19.21_0 f19.21_1 f19.21_2 19.21t ax-mp $.
$}
$( Theorem 19.21 of [Margaris] p. 90 but with 2 quantifiers.  (Contributed
       by NM, 4-Feb-2005.) $)
${
	f19.21-2_0 $f wff ph $.
	f19.21-2_1 $f wff ps $.
	f19.21-2_2 $f set x $.
	f19.21-2_3 $f set y $.
	e19.21-2_0 $e |- F/ x ph $.
	e19.21-2_1 $e |- F/ y ph $.
	19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $= f19.21-2_0 f19.21-2_1 wi f19.21-2_3 wal f19.21-2_2 wal f19.21-2_0 f19.21-2_1 f19.21-2_3 wal wi f19.21-2_2 wal f19.21-2_0 f19.21-2_1 f19.21-2_3 wal f19.21-2_2 wal wi f19.21-2_0 f19.21-2_1 wi f19.21-2_3 wal f19.21-2_0 f19.21-2_1 f19.21-2_3 wal wi f19.21-2_2 f19.21-2_0 f19.21-2_1 f19.21-2_3 e19.21-2_1 19.21 albii f19.21-2_0 f19.21-2_1 f19.21-2_3 wal f19.21-2_2 e19.21-2_0 19.21 bitri $.
$}
$( An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` F/ x ph ` can be thought of as
       emulating " ` x ` is not free in ` ph ` ."  With this definition, the
       meaning of "not free" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ nfequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5.  (Contributed by NM, 22-Sep-1993.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)
${
	fstdpc5_0 $f wff ph $.
	fstdpc5_1 $f wff ps $.
	fstdpc5_2 $f set x $.
	estdpc5_0 $e |- F/ x ph $.
	stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $= fstdpc5_0 fstdpc5_0 fstdpc5_2 wal fstdpc5_0 fstdpc5_1 wi fstdpc5_2 wal fstdpc5_1 fstdpc5_2 wal fstdpc5_0 fstdpc5_2 estdpc5_0 nfri fstdpc5_0 fstdpc5_1 fstdpc5_2 alim syl5 $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	f19.21bi_0 $f wff ph $.
	f19.21bi_1 $f wff ps $.
	f19.21bi_2 $f set x $.
	e19.21bi_0 $e |- ( ph -> A. x ps ) $.
	19.21bi $p |- ( ph -> ps ) $= f19.21bi_0 f19.21bi_1 f19.21bi_2 wal f19.21bi_1 e19.21bi_0 f19.21bi_1 f19.21bi_2 sp syl $.
$}
$( Inference removing double quantifier.  (Contributed by NM,
       20-Apr-1994.) $)
${
	f19.21bbi_0 $f wff ph $.
	f19.21bbi_1 $f wff ps $.
	f19.21bbi_2 $f set x $.
	f19.21bbi_3 $f set y $.
	e19.21bbi_0 $e |- ( ph -> A. x A. y ps ) $.
	19.21bbi $p |- ( ph -> ps ) $= f19.21bbi_0 f19.21bbi_1 f19.21bbi_3 f19.21bbi_0 f19.21bbi_1 f19.21bbi_3 wal f19.21bbi_2 e19.21bbi_0 19.21bi 19.21bi $.
$}
$( Closed form of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
     7-Nov-2005.) $)
${
	f19.23t_0 $f wff ph $.
	f19.23t_1 $f wff ps $.
	f19.23t_2 $f set x $.
	19.23t $p |- ( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $= f19.23t_1 f19.23t_2 wnf f19.23t_0 f19.23t_1 wi f19.23t_2 wal f19.23t_0 f19.23t_2 wex f19.23t_1 wi f19.23t_0 f19.23t_1 wi f19.23t_2 wal f19.23t_0 f19.23t_2 wex f19.23t_1 f19.23t_2 wex wi f19.23t_1 f19.23t_2 wnf f19.23t_0 f19.23t_2 wex f19.23t_1 wi f19.23t_0 f19.23t_1 f19.23t_2 exim f19.23t_1 f19.23t_2 wnf f19.23t_1 f19.23t_2 wex f19.23t_1 f19.23t_0 f19.23t_2 wex f19.23t_1 f19.23t_2 19.9t imbi2d syl5ib f19.23t_1 f19.23t_2 wnf f19.23t_0 f19.23t_2 wex f19.23t_1 wi f19.23t_0 f19.23t_1 wi f19.23t_2 f19.23t_1 f19.23t_2 nfnf1 f19.23t_1 f19.23t_2 wnf f19.23t_0 f19.23t_2 wex f19.23t_1 f19.23t_2 f19.23t_0 f19.23t_2 wex f19.23t_2 wnf f19.23t_1 f19.23t_2 wnf f19.23t_0 f19.23t_2 nfe1 a1i f19.23t_1 f19.23t_2 wnf id nfimd f19.23t_1 f19.23t_2 wnf f19.23t_0 f19.23t_0 f19.23t_2 wex f19.23t_1 f19.23t_0 f19.23t_0 f19.23t_2 wex wi f19.23t_1 f19.23t_2 wnf f19.23t_0 f19.23t_2 19.8a a1i imim1d alrimdd impbid $.
$}
$( Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
${
	f19.23_0 $f wff ph $.
	f19.23_1 $f wff ps $.
	f19.23_2 $f set x $.
	e19.23_0 $e |- F/ x ps $.
	19.23 $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $= f19.23_1 f19.23_2 wnf f19.23_0 f19.23_1 wi f19.23_2 wal f19.23_0 f19.23_2 wex f19.23_1 wi wb e19.23_0 f19.23_0 f19.23_1 f19.23_2 19.23t ax-mp $.
$}
$( An alternative definition of ~ df-nf , which does not involve nested
     quantifiers on the same variable.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
${
	fnf2_0 $f wff ph $.
	fnf2_1 $f set x $.
	nf2 $p |- ( F/ x ph <-> ( E. x ph -> A. x ph ) ) $= fnf2_0 fnf2_1 wnf fnf2_0 fnf2_0 fnf2_1 wal wi fnf2_1 wal fnf2_0 fnf2_1 wex fnf2_0 fnf2_1 wal wi fnf2_0 fnf2_1 df-nf fnf2_0 fnf2_0 fnf2_1 wal fnf2_1 fnf2_0 fnf2_1 nfa1 19.23 bitri $.
$}
$( An alternative definition of ~ df-nf .  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
${
	fnf3_0 $f wff ph $.
	fnf3_1 $f set x $.
	nf3 $p |- ( F/ x ph <-> A. x ( E. x ph -> ph ) ) $= fnf3_0 fnf3_1 wnf fnf3_0 fnf3_1 wex fnf3_0 fnf3_1 wal wi fnf3_0 fnf3_1 wex fnf3_0 wi fnf3_1 wal fnf3_0 fnf3_1 nf2 fnf3_0 fnf3_1 wex fnf3_0 fnf3_1 fnf3_0 fnf3_1 nfe1 19.21 bitr4i $.
$}
$( Variable ` x ` is effectively not free in ` ph ` iff ` ph ` is always true
     or always false.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	fnf4_0 $f wff ph $.
	fnf4_1 $f set x $.
	nf4 $p |- ( F/ x ph <-> ( A. x ph \/ A. x -. ph ) ) $= fnf4_0 fnf4_1 wnf fnf4_0 fnf4_1 wex fnf4_0 fnf4_1 wal wi fnf4_0 fnf4_1 wex wn fnf4_0 fnf4_1 wal wo fnf4_0 fnf4_1 wal fnf4_0 wn fnf4_1 wal wo fnf4_0 fnf4_1 nf2 fnf4_0 fnf4_1 wex fnf4_0 fnf4_1 wal imor fnf4_0 fnf4_1 wex wn fnf4_0 fnf4_1 wal wo fnf4_0 fnf4_1 wal fnf4_0 fnf4_1 wex wn wo fnf4_0 fnf4_1 wal fnf4_0 wn fnf4_1 wal wo fnf4_0 fnf4_1 wex wn fnf4_0 fnf4_1 wal orcom fnf4_0 wn fnf4_1 wal fnf4_0 fnf4_1 wex wn fnf4_0 fnf4_1 wal fnf4_0 fnf4_1 alnex orbi2i bitr4i 3bitri $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
${
	fexlimi_0 $f wff ph $.
	fexlimi_1 $f wff ps $.
	fexlimi_2 $f set x $.
	eexlimi_0 $e |- F/ x ps $.
	eexlimi_1 $e |- ( ph -> ps ) $.
	exlimi $p |- ( E. x ph -> ps ) $= fexlimi_0 fexlimi_1 wi fexlimi_0 fexlimi_2 wex fexlimi_1 wi fexlimi_2 fexlimi_0 fexlimi_1 fexlimi_2 eexlimi_0 19.23 eexlimi_1 mpgbi $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	f19.23bi_0 $f wff ph $.
	f19.23bi_1 $f wff ps $.
	f19.23bi_2 $f set x $.
	e19.23bi_0 $e |- ( E. x ph -> ps ) $.
	19.23bi $p |- ( ph -> ps ) $= f19.23bi_0 f19.23bi_0 f19.23bi_2 wex f19.23bi_1 f19.23bi_0 f19.23bi_2 19.8a e19.23bi_0 syl $.
$}
$( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
${
	fexlimd_0 $f wff ph $.
	fexlimd_1 $f wff ps $.
	fexlimd_2 $f wff ch $.
	fexlimd_3 $f set x $.
	eexlimd_0 $e |- F/ x ph $.
	eexlimd_1 $e |- F/ x ch $.
	eexlimd_2 $e |- ( ph -> ( ps -> ch ) ) $.
	exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $= fexlimd_0 fexlimd_1 fexlimd_2 wi fexlimd_3 wal fexlimd_1 fexlimd_3 wex fexlimd_2 wi fexlimd_0 fexlimd_1 fexlimd_2 wi fexlimd_3 eexlimd_0 eexlimd_2 alrimi fexlimd_1 fexlimd_2 fexlimd_3 eexlimd_1 19.23 sylib $.
$}
$( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jan-1997.) $)
${
	fexlimdh_0 $f wff ph $.
	fexlimdh_1 $f wff ps $.
	fexlimdh_2 $f wff ch $.
	fexlimdh_3 $f set x $.
	eexlimdh_0 $e |- ( ph -> A. x ph ) $.
	eexlimdh_1 $e |- ( ch -> A. x ch ) $.
	eexlimdh_2 $e |- ( ph -> ( ps -> ch ) ) $.
	exlimdh $p |- ( ph -> ( E. x ps -> ch ) ) $= fexlimdh_0 fexlimdh_1 fexlimdh_2 fexlimdh_3 fexlimdh_0 fexlimdh_3 eexlimdh_0 nfi fexlimdh_2 fexlimdh_3 eexlimdh_1 nfi eexlimdh_2 exlimd $.
$}
$( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.27_0 $f wff ph $.
	f19.27_1 $f wff ps $.
	f19.27_2 $f set x $.
	e19.27_0 $e |- F/ x ps $.
	19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $= f19.27_0 f19.27_1 wa f19.27_2 wal f19.27_0 f19.27_2 wal f19.27_1 f19.27_2 wal wa f19.27_0 f19.27_2 wal f19.27_1 wa f19.27_0 f19.27_1 f19.27_2 19.26 f19.27_1 f19.27_2 wal f19.27_1 f19.27_0 f19.27_2 wal f19.27_1 f19.27_2 e19.27_0 19.3 anbi2i bitri $.
$}
$( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.28_0 $f wff ph $.
	f19.28_1 $f wff ps $.
	f19.28_2 $f set x $.
	e19.28_0 $e |- F/ x ph $.
	19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $= f19.28_0 f19.28_1 wa f19.28_2 wal f19.28_0 f19.28_2 wal f19.28_1 f19.28_2 wal wa f19.28_0 f19.28_1 f19.28_2 wal wa f19.28_0 f19.28_1 f19.28_2 19.26 f19.28_0 f19.28_2 wal f19.28_0 f19.28_1 f19.28_2 wal f19.28_0 f19.28_2 e19.28_0 19.3 anbi1i bitri $.
$}
$( Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.36_0 $f wff ph $.
	f19.36_1 $f wff ps $.
	f19.36_2 $f set x $.
	e19.36_0 $e |- F/ x ps $.
	19.36 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $= f19.36_0 f19.36_1 wi f19.36_2 wex f19.36_0 f19.36_2 wal f19.36_1 f19.36_2 wex wi f19.36_0 f19.36_2 wal f19.36_1 wi f19.36_0 f19.36_1 f19.36_2 19.35 f19.36_1 f19.36_2 wex f19.36_1 f19.36_0 f19.36_2 wal f19.36_1 f19.36_2 e19.36_0 19.9 imbi2i bitri $.
$}
$( Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	f19.36i_0 $f wff ph $.
	f19.36i_1 $f wff ps $.
	f19.36i_2 $f set x $.
	e19.36i_0 $e |- F/ x ps $.
	e19.36i_1 $e |- E. x ( ph -> ps ) $.
	19.36i $p |- ( A. x ph -> ps ) $= f19.36i_0 f19.36i_1 wi f19.36i_2 wex f19.36i_0 f19.36i_2 wal f19.36i_1 wi e19.36i_1 f19.36i_0 f19.36i_1 f19.36i_2 e19.36i_0 19.36 mpbi $.
$}
$( Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.37_0 $f wff ph $.
	f19.37_1 $f wff ps $.
	f19.37_2 $f set x $.
	e19.37_0 $e |- F/ x ph $.
	19.37 $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $= f19.37_0 f19.37_1 wi f19.37_2 wex f19.37_0 f19.37_2 wal f19.37_1 f19.37_2 wex wi f19.37_0 f19.37_1 f19.37_2 wex wi f19.37_0 f19.37_1 f19.37_2 19.35 f19.37_0 f19.37_2 wal f19.37_0 f19.37_1 f19.37_2 wex f19.37_0 f19.37_2 e19.37_0 19.3 imbi1i bitri $.
$}
$( Theorem 19.38 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.38_0 $f wff ph $.
	f19.38_1 $f wff ps $.
	f19.38_2 $f set x $.
	19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $= f19.38_0 f19.38_2 wex f19.38_1 f19.38_2 wal wi f19.38_0 f19.38_1 wi f19.38_2 f19.38_0 f19.38_2 wex f19.38_1 f19.38_2 wal f19.38_2 f19.38_0 f19.38_2 nfe1 f19.38_1 f19.38_2 nfa1 nfim f19.38_0 f19.38_0 f19.38_2 wex f19.38_1 f19.38_2 wal f19.38_1 f19.38_0 f19.38_2 19.8a f19.38_1 f19.38_2 sp imim12i alrimi $.
$}
$( Theorem 19.32 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
${
	f19.32_0 $f wff ph $.
	f19.32_1 $f wff ps $.
	f19.32_2 $f set x $.
	e19.32_0 $e |- F/ x ph $.
	19.32 $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $= f19.32_0 wn f19.32_1 wi f19.32_2 wal f19.32_0 wn f19.32_1 f19.32_2 wal wi f19.32_0 f19.32_1 wo f19.32_2 wal f19.32_0 f19.32_1 f19.32_2 wal wo f19.32_0 wn f19.32_1 f19.32_2 f19.32_0 f19.32_2 e19.32_0 nfn 19.21 f19.32_0 f19.32_1 wo f19.32_0 wn f19.32_1 wi f19.32_2 f19.32_0 f19.32_1 df-or albii f19.32_0 f19.32_1 f19.32_2 wal df-or 3bitr4i $.
$}
$( Theorem 19.31 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.31_0 $f wff ph $.
	f19.31_1 $f wff ps $.
	f19.31_2 $f set x $.
	e19.31_0 $e |- F/ x ps $.
	19.31 $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $= f19.31_1 f19.31_0 wo f19.31_2 wal f19.31_1 f19.31_0 f19.31_2 wal wo f19.31_0 f19.31_1 wo f19.31_2 wal f19.31_0 f19.31_2 wal f19.31_1 wo f19.31_1 f19.31_0 f19.31_2 e19.31_0 19.32 f19.31_0 f19.31_1 wo f19.31_1 f19.31_0 wo f19.31_2 f19.31_0 f19.31_1 orcom albii f19.31_0 f19.31_2 wal f19.31_1 orcom 3bitr4i $.
$}
$( Theorem 19.44 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.44_0 $f wff ph $.
	f19.44_1 $f wff ps $.
	f19.44_2 $f set x $.
	e19.44_0 $e |- F/ x ps $.
	19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $= f19.44_0 f19.44_1 wo f19.44_2 wex f19.44_0 f19.44_2 wex f19.44_1 f19.44_2 wex wo f19.44_0 f19.44_2 wex f19.44_1 wo f19.44_0 f19.44_1 f19.44_2 19.43 f19.44_1 f19.44_2 wex f19.44_1 f19.44_0 f19.44_2 wex f19.44_1 f19.44_2 e19.44_0 19.9 orbi2i bitri $.
$}
$( Theorem 19.45 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	f19.45_0 $f wff ph $.
	f19.45_1 $f wff ps $.
	f19.45_2 $f set x $.
	e19.45_0 $e |- F/ x ph $.
	19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $= f19.45_0 f19.45_1 wo f19.45_2 wex f19.45_0 f19.45_2 wex f19.45_1 f19.45_2 wex wo f19.45_0 f19.45_1 f19.45_2 wex wo f19.45_0 f19.45_1 f19.45_2 19.43 f19.45_0 f19.45_2 wex f19.45_0 f19.45_1 f19.45_2 wex f19.45_0 f19.45_2 e19.45_0 19.9 orbi1i bitri $.
$}
$( Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	f19.41_0 $f wff ph $.
	f19.41_1 $f wff ps $.
	f19.41_2 $f set x $.
	e19.41_0 $e |- F/ x ps $.
	19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $= f19.41_0 f19.41_1 wa f19.41_2 wex f19.41_0 f19.41_2 wex f19.41_1 wa f19.41_0 f19.41_1 wa f19.41_2 wex f19.41_0 f19.41_2 wex f19.41_1 f19.41_2 wex wa f19.41_0 f19.41_2 wex f19.41_1 wa f19.41_0 f19.41_1 f19.41_2 19.40 f19.41_1 f19.41_2 wex f19.41_1 f19.41_0 f19.41_2 wex f19.41_1 f19.41_1 f19.41_2 e19.41_0 f19.41_1 id exlimi anim2i syl f19.41_1 f19.41_0 f19.41_2 wex f19.41_0 f19.41_1 wa f19.41_2 wex f19.41_1 f19.41_0 f19.41_0 f19.41_1 wa f19.41_2 e19.41_0 f19.41_1 f19.41_0 pm3.21 eximd impcom impbii $.
$}
$( Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM, 18-Aug-1993.) $)
${
	f19.42_0 $f wff ph $.
	f19.42_1 $f wff ps $.
	f19.42_2 $f set x $.
	e19.42_0 $e |- F/ x ph $.
	19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $= f19.42_1 f19.42_0 wa f19.42_2 wex f19.42_1 f19.42_2 wex f19.42_0 wa f19.42_0 f19.42_1 wa f19.42_2 wex f19.42_0 f19.42_1 f19.42_2 wex wa f19.42_1 f19.42_0 f19.42_2 e19.42_0 19.41 f19.42_0 f19.42_1 f19.42_2 exancom f19.42_0 f19.42_1 f19.42_2 wex ancom 3bitr4i $.
$}
$( Swap 1st and 3rd existential quantifiers.  (Contributed by NM,
     9-Mar-1995.) $)
${
	fexcom13_0 $f wff ph $.
	fexcom13_1 $f set x $.
	fexcom13_2 $f set y $.
	fexcom13_3 $f set z $.
	excom13 $p |- ( E. x E. y E. z ph <-> E. z E. y E. x ph ) $= fexcom13_0 fexcom13_3 wex fexcom13_2 wex fexcom13_1 wex fexcom13_0 fexcom13_3 wex fexcom13_1 wex fexcom13_2 wex fexcom13_0 fexcom13_1 wex fexcom13_3 wex fexcom13_2 wex fexcom13_0 fexcom13_1 wex fexcom13_2 wex fexcom13_3 wex fexcom13_0 fexcom13_3 wex fexcom13_1 fexcom13_2 excom fexcom13_0 fexcom13_3 wex fexcom13_1 wex fexcom13_0 fexcom13_1 wex fexcom13_3 wex fexcom13_2 fexcom13_0 fexcom13_1 fexcom13_3 excom exbii fexcom13_0 fexcom13_1 wex fexcom13_2 fexcom13_3 excom 3bitri $.
$}
$( Rotate existential quantifiers.  (Contributed by NM, 17-Mar-1995.) $)
${
	fexrot3_0 $f wff ph $.
	fexrot3_1 $f set x $.
	fexrot3_2 $f set y $.
	fexrot3_3 $f set z $.
	exrot3 $p |- ( E. x E. y E. z ph <-> E. y E. z E. x ph ) $= fexrot3_0 fexrot3_3 wex fexrot3_2 wex fexrot3_1 wex fexrot3_0 fexrot3_1 wex fexrot3_2 wex fexrot3_3 wex fexrot3_0 fexrot3_1 wex fexrot3_3 wex fexrot3_2 wex fexrot3_0 fexrot3_1 fexrot3_2 fexrot3_3 excom13 fexrot3_0 fexrot3_1 wex fexrot3_3 fexrot3_2 excom bitri $.
$}
$( Rotate existential quantifiers twice.  (Contributed by NM, 9-Mar-1995.) $)
${
	fexrot4_0 $f wff ph $.
	fexrot4_1 $f set x $.
	fexrot4_2 $f set y $.
	fexrot4_3 $f set z $.
	fexrot4_4 $f set w $.
	exrot4 $p |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph ) $= fexrot4_0 fexrot4_4 wex fexrot4_3 wex fexrot4_2 wex fexrot4_1 wex fexrot4_0 fexrot4_2 wex fexrot4_3 wex fexrot4_4 wex fexrot4_1 wex fexrot4_0 fexrot4_2 wex fexrot4_1 wex fexrot4_4 wex fexrot4_3 wex fexrot4_0 fexrot4_4 wex fexrot4_3 wex fexrot4_2 wex fexrot4_0 fexrot4_2 wex fexrot4_3 wex fexrot4_4 wex fexrot4_1 fexrot4_0 fexrot4_2 fexrot4_3 fexrot4_4 excom13 exbii fexrot4_0 fexrot4_2 wex fexrot4_1 fexrot4_4 fexrot4_3 excom13 bitri $.
$}
$( Inference from ~ 19.8a .  (Contributed by Jeff Hankins, 26-Jul-2009.) $)
${
	fnexr_0 $f wff ph $.
	fnexr_1 $f set x $.
	enexr_0 $e |- -. E. x ph $.
	nexr $p |- -. ph $= fnexr_0 fnexr_0 fnexr_1 wex enexr_0 fnexr_0 fnexr_1 19.8a mto $.
$}
$( A closed form of ~ nfim .  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 24-Sep-2016.) $)
${
	fnfim1_0 $f wff ph $.
	fnfim1_1 $f wff ps $.
	fnfim1_2 $f set x $.
	enfim1_0 $e |- F/ x ph $.
	enfim1_1 $e |- ( ph -> F/ x ps ) $.
	nfim1 $p |- F/ x ( ph -> ps ) $= fnfim1_0 fnfim1_1 wi fnfim1_2 fnfim1_0 fnfim1_1 wi fnfim1_0 fnfim1_1 fnfim1_2 wal wi fnfim1_0 fnfim1_1 wi fnfim1_2 wal fnfim1_0 fnfim1_1 fnfim1_1 fnfim1_2 wal fnfim1_0 fnfim1_1 fnfim1_2 enfim1_1 nfrd a2i fnfim1_0 fnfim1_1 fnfim1_2 enfim1_0 19.21 sylibr nfi $.
$}
$( A closed form of ~ nfan .  (Contributed by Mario Carneiro,
       3-Oct-2016.) $)
${
	fnfan1_0 $f wff ph $.
	fnfan1_1 $f wff ps $.
	fnfan1_2 $f set x $.
	enfan1_0 $e |- F/ x ph $.
	enfan1_1 $e |- ( ph -> F/ x ps ) $.
	nfan1 $p |- F/ x ( ph /\ ps ) $= fnfan1_0 fnfan1_1 wa fnfan1_2 fnfan1_0 fnfan1_1 wa fnfan1_0 fnfan1_1 fnfan1_2 wal wa fnfan1_0 fnfan1_1 wa fnfan1_2 wal fnfan1_0 fnfan1_1 fnfan1_1 fnfan1_2 wal fnfan1_0 fnfan1_1 fnfan1_2 enfan1_1 nfrd imdistani fnfan1_0 fnfan1_1 fnfan1_2 enfan1_0 19.28 sylibr nfi $.
$}
$( Place a conjunct in the scope of an existential quantifier.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
${
	fexan_0 $f wff ph $.
	fexan_1 $f wff ps $.
	fexan_2 $f set x $.
	eexan_0 $e |- ( E. x ph /\ ps ) $.
	exan $p |- E. x ( ph /\ ps ) $= fexan_0 fexan_2 wex fexan_1 fexan_2 wal wa fexan_0 fexan_1 wa fexan_2 wex fexan_0 fexan_2 wex fexan_1 wa fexan_0 fexan_2 wex fexan_1 fexan_2 wal wa fexan_2 fexan_0 fexan_2 wex fexan_1 fexan_2 fexan_0 fexan_2 nfe1 19.28 eexan_0 mpgbi fexan_0 fexan_1 fexan_2 19.29r ax-mp $.
$}
$( Deduction form of bound-variable hypothesis builder ~ hbn .
       (Contributed by NM, 3-Jan-2002.) $)
${
	fhbnd_0 $f wff ph $.
	fhbnd_1 $f wff ps $.
	fhbnd_2 $f set x $.
	ehbnd_0 $e |- ( ph -> A. x ph ) $.
	ehbnd_1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
	hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $= fhbnd_0 fhbnd_1 fhbnd_1 fhbnd_2 wal wi fhbnd_2 wal fhbnd_1 wn fhbnd_1 wn fhbnd_2 wal wi fhbnd_0 fhbnd_1 fhbnd_1 fhbnd_2 wal wi fhbnd_2 ehbnd_0 ehbnd_1 alrimih fhbnd_1 fhbnd_2 hbnt syl $.
$}
$( Rearrange universal quantifiers.  (Contributed by NM, 12-Aug-1993.) $)
${
	faaan_0 $f wff ph $.
	faaan_1 $f wff ps $.
	faaan_2 $f set x $.
	faaan_3 $f set y $.
	eaaan_0 $e |- F/ y ph $.
	eaaan_1 $e |- F/ x ps $.
	aaan $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $= faaan_0 faaan_1 wa faaan_3 wal faaan_2 wal faaan_0 faaan_1 faaan_3 wal wa faaan_2 wal faaan_0 faaan_2 wal faaan_1 faaan_3 wal wa faaan_0 faaan_1 wa faaan_3 wal faaan_0 faaan_1 faaan_3 wal wa faaan_2 faaan_0 faaan_1 faaan_3 eaaan_0 19.28 albii faaan_0 faaan_1 faaan_3 wal faaan_2 faaan_1 faaan_2 faaan_3 eaaan_1 nfal 19.27 bitri $.
$}
$( Rearrange existential quantifiers.  (Contributed by NM, 8-Aug-1994.) $)
${
	feeor_0 $f wff ph $.
	feeor_1 $f wff ps $.
	feeor_2 $f set x $.
	feeor_3 $f set y $.
	eeeor_0 $e |- F/ y ph $.
	eeeor_1 $e |- F/ x ps $.
	eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $= feeor_0 feeor_1 wo feeor_3 wex feeor_2 wex feeor_0 feeor_1 feeor_3 wex wo feeor_2 wex feeor_0 feeor_2 wex feeor_1 feeor_3 wex wo feeor_0 feeor_1 wo feeor_3 wex feeor_0 feeor_1 feeor_3 wex wo feeor_2 feeor_0 feeor_1 feeor_3 eeeor_0 19.45 exbii feeor_0 feeor_1 feeor_3 wex feeor_2 feeor_1 feeor_2 feeor_3 eeeor_1 nfex 19.44 bitri $.
$}
$( Quantified "excluded middle."  Exercise 9.2a of Boolos, p. 111,
     _Computability and Logic_.  (Contributed by NM, 10-Dec-2000.) $)
${
	fqexmid_0 $f wff ph $.
	fqexmid_1 $f set x $.
	qexmid $p |- E. x ( ph -> A. x ph ) $= fqexmid_0 fqexmid_0 fqexmid_1 wal fqexmid_1 fqexmid_0 fqexmid_1 wal fqexmid_1 19.8a 19.35ri $.
$}
$( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)
${
	fequs5a_0 $f wff ph $.
	fequs5a_1 $f set x $.
	fequs5a_2 $f set y $.
	equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $= fequs5a_1 fequs5a_2 weq fequs5a_0 fequs5a_2 wal wa fequs5a_1 fequs5a_2 weq fequs5a_0 wi fequs5a_1 wal fequs5a_1 fequs5a_1 fequs5a_2 weq fequs5a_0 wi fequs5a_1 nfa1 fequs5a_1 fequs5a_2 weq fequs5a_0 fequs5a_2 wal fequs5a_1 fequs5a_2 weq fequs5a_0 wi fequs5a_1 wal fequs5a_0 fequs5a_1 fequs5a_2 ax-11 imp exlimi $.
$}
$( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)
${
	fequs5e_0 $f wff ph $.
	fequs5e_1 $f set x $.
	fequs5e_2 $f set y $.
	equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $= fequs5e_1 fequs5e_2 weq fequs5e_0 wa fequs5e_1 wex fequs5e_1 fequs5e_2 weq fequs5e_0 fequs5e_2 wex wi fequs5e_1 fequs5e_1 fequs5e_2 weq fequs5e_0 wa fequs5e_1 nfe1 fequs5e_1 fequs5e_2 weq fequs5e_0 wa fequs5e_1 wex fequs5e_1 fequs5e_2 weq fequs5e_0 wn wi fequs5e_1 wal wn fequs5e_1 fequs5e_2 weq fequs5e_0 fequs5e_2 wex wi fequs5e_0 fequs5e_1 fequs5e_2 equs3 fequs5e_1 fequs5e_2 weq fequs5e_0 wn wi fequs5e_1 wal wn fequs5e_1 fequs5e_2 weq fequs5e_0 wn fequs5e_2 wal wn fequs5e_0 fequs5e_2 wex fequs5e_1 fequs5e_2 weq fequs5e_0 wn fequs5e_2 wal fequs5e_1 fequs5e_2 weq fequs5e_0 wn wi fequs5e_1 wal fequs5e_0 wn fequs5e_1 fequs5e_2 ax-11 con3rr3 fequs5e_0 fequs5e_2 df-ex syl6ibr sylbi alrimi $.
$}
$( Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
${
	fexlimdd_0 $f wff ph $.
	fexlimdd_1 $f wff ps $.
	fexlimdd_2 $f wff ch $.
	fexlimdd_3 $f set x $.
	eexlimdd_0 $e |- F/ x ph $.
	eexlimdd_1 $e |- F/ x ch $.
	eexlimdd_2 $e |- ( ph -> E. x ps ) $.
	eexlimdd_3 $e |- ( ( ph /\ ps ) -> ch ) $.
	exlimdd $p |- ( ph -> ch ) $= fexlimdd_0 fexlimdd_1 fexlimdd_3 wex fexlimdd_2 eexlimdd_2 fexlimdd_0 fexlimdd_1 fexlimdd_2 fexlimdd_3 eexlimdd_0 eexlimdd_1 fexlimdd_0 fexlimdd_1 fexlimdd_2 eexlimdd_3 ex exlimd mpd $.
$}
$( Special case of Theorem 19.21 of [Margaris] p. 90. _Notational
       convention_:  We sometimes suffix with "v" the label of a theorem
       eliminating a hypothesis such as ` F/ x ph ` in ~ 19.21 via the use of
       distinct variable conditions combined with ~ nfv .  Conversely, we
       sometimes suffix with "f" the label of a theorem introducing such a
       hypothesis to eliminate the need for the distinct variable condition;
       e.g. ~ euf derived from ~ df-eu .  The "f" stands for "not free in"
       which is less restrictive than "does not occur in."  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ph $.
	f19.21v_0 $f wff ph $.
	f19.21v_1 $f wff ps $.
	f19.21v_2 $f set x $.
	19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $= f19.21v_0 f19.21v_1 f19.21v_2 f19.21v_0 f19.21v_2 nfv 19.21 $.
$}
$( Special case of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jun-1998.) $)
${
	$d x ps $.
	f19.23v_0 $f wff ph $.
	f19.23v_1 $f wff ps $.
	f19.23v_2 $f set x $.
	19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $= f19.23v_0 f19.23v_1 f19.23v_2 f19.23v_1 f19.23v_2 nfv 19.23 $.
$}
$( Theorem 19.23 of [Margaris] p. 90 extended to two variables.
       (Contributed by NM, 10-Aug-2004.) $)
${
	$d x ps $.
	$d y ps $.
	f19.23vv_0 $f wff ph $.
	f19.23vv_1 $f wff ps $.
	f19.23vv_2 $f set x $.
	f19.23vv_3 $f set y $.
	19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $= f19.23vv_0 f19.23vv_1 wi f19.23vv_3 wal f19.23vv_2 wal f19.23vv_0 f19.23vv_3 wex f19.23vv_1 wi f19.23vv_2 wal f19.23vv_0 f19.23vv_3 wex f19.23vv_2 wex f19.23vv_1 wi f19.23vv_0 f19.23vv_1 wi f19.23vv_3 wal f19.23vv_0 f19.23vv_3 wex f19.23vv_1 wi f19.23vv_2 f19.23vv_0 f19.23vv_1 f19.23vv_3 19.23v albii f19.23vv_0 f19.23vv_3 wex f19.23vv_1 f19.23vv_2 19.23v bitri $.
$}
$( Theorem *11.53 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
${
	$d ph y $.
	$d ps x $.
	fpm11.53_0 $f wff ph $.
	fpm11.53_1 $f wff ps $.
	fpm11.53_2 $f set x $.
	fpm11.53_3 $f set y $.
	pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $= fpm11.53_0 fpm11.53_1 wi fpm11.53_3 wal fpm11.53_2 wal fpm11.53_0 fpm11.53_1 fpm11.53_3 wal wi fpm11.53_2 wal fpm11.53_0 fpm11.53_2 wex fpm11.53_1 fpm11.53_3 wal wi fpm11.53_0 fpm11.53_1 wi fpm11.53_3 wal fpm11.53_0 fpm11.53_1 fpm11.53_3 wal wi fpm11.53_2 fpm11.53_0 fpm11.53_1 fpm11.53_3 19.21v albii fpm11.53_0 fpm11.53_1 fpm11.53_3 wal fpm11.53_2 fpm11.53_1 fpm11.53_2 fpm11.53_3 fpm11.53_1 fpm11.53_2 nfv nfal 19.23 bitri $.
$}
$( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 3-Jun-2004.) $)
${
	$d x ps $.
	f19.27v_0 $f wff ph $.
	f19.27v_1 $f wff ps $.
	f19.27v_2 $f set x $.
	19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $= f19.27v_0 f19.27v_1 f19.27v_2 f19.27v_1 f19.27v_2 nfv 19.27 $.
$}
$( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 25-Mar-2004.) $)
${
	$d x ph $.
	f19.28v_0 $f wff ph $.
	f19.28v_1 $f wff ps $.
	f19.28v_2 $f set x $.
	19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $= f19.28v_0 f19.28v_1 f19.28v_2 f19.28v_0 f19.28v_2 nfv 19.28 $.
$}
$( Special case of Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       18-Aug-1993.) $)
${
	$d x ps $.
	f19.36v_0 $f wff ph $.
	f19.36v_1 $f wff ps $.
	f19.36v_2 $f set x $.
	19.36v $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $= f19.36v_0 f19.36v_1 f19.36v_2 f19.36v_1 f19.36v_2 nfv 19.36 $.
$}
$( Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ps $.
	f19.36aiv_0 $f wff ph $.
	f19.36aiv_1 $f wff ps $.
	f19.36aiv_2 $f set x $.
	e19.36aiv_0 $e |- E. x ( ph -> ps ) $.
	19.36aiv $p |- ( A. x ph -> ps ) $= f19.36aiv_0 f19.36aiv_1 f19.36aiv_2 f19.36aiv_1 f19.36aiv_2 nfv e19.36aiv_0 19.36i $.
$}
$( Special case of ~ 19.12 where its converse holds.  (Contributed by NM,
       18-Jul-2001.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)
${
	$d x ps $.
	$d y ph $.
	f19.12vv_0 $f wff ph $.
	f19.12vv_1 $f wff ps $.
	f19.12vv_2 $f set x $.
	f19.12vv_3 $f set y $.
	19.12vv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $= f19.12vv_0 f19.12vv_1 wi f19.12vv_3 wal f19.12vv_2 wex f19.12vv_0 f19.12vv_1 f19.12vv_3 wal wi f19.12vv_2 wex f19.12vv_0 f19.12vv_2 wal f19.12vv_1 f19.12vv_3 wal wi f19.12vv_0 f19.12vv_1 wi f19.12vv_2 wex f19.12vv_3 wal f19.12vv_0 f19.12vv_1 wi f19.12vv_3 wal f19.12vv_0 f19.12vv_1 f19.12vv_3 wal wi f19.12vv_2 f19.12vv_0 f19.12vv_1 f19.12vv_3 19.21v exbii f19.12vv_0 f19.12vv_1 f19.12vv_3 wal f19.12vv_2 f19.12vv_1 f19.12vv_2 f19.12vv_3 f19.12vv_1 f19.12vv_2 nfv nfal 19.36 f19.12vv_0 f19.12vv_1 wi f19.12vv_2 wex f19.12vv_3 wal f19.12vv_0 f19.12vv_2 wal f19.12vv_1 wi f19.12vv_3 wal f19.12vv_0 f19.12vv_2 wal f19.12vv_1 f19.12vv_3 wal wi f19.12vv_0 f19.12vv_1 wi f19.12vv_2 wex f19.12vv_0 f19.12vv_2 wal f19.12vv_1 wi f19.12vv_3 f19.12vv_0 f19.12vv_1 f19.12vv_2 19.36v albii f19.12vv_0 f19.12vv_2 wal f19.12vv_1 f19.12vv_3 f19.12vv_0 f19.12vv_3 f19.12vv_2 f19.12vv_0 f19.12vv_3 nfv nfal 19.21 bitr2i 3bitri $.
$}
$( Special case of Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ph $.
	f19.37v_0 $f wff ph $.
	f19.37v_1 $f wff ps $.
	f19.37v_2 $f set x $.
	19.37v $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $= f19.37v_0 f19.37v_1 f19.37v_2 f19.37v_0 f19.37v_2 nfv 19.37 $.
$}
$( Inference from Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ph $.
	f19.37aiv_0 $f wff ph $.
	f19.37aiv_1 $f wff ps $.
	f19.37aiv_2 $f set x $.
	e19.37aiv_0 $e |- E. x ( ph -> ps ) $.
	19.37aiv $p |- ( ph -> E. x ps ) $= f19.37aiv_0 f19.37aiv_1 wi f19.37aiv_2 wex f19.37aiv_0 f19.37aiv_1 f19.37aiv_2 wex wi e19.37aiv_0 f19.37aiv_0 f19.37aiv_1 f19.37aiv_2 19.37v mpbi $.
$}
$( Special case of Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ps $.
	f19.41v_0 $f wff ph $.
	f19.41v_1 $f wff ps $.
	f19.41v_2 $f set x $.
	19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $= f19.41v_0 f19.41v_1 f19.41v_2 f19.41v_1 f19.41v_2 nfv 19.41 $.
$}
$( Theorem 19.41 of [Margaris] p. 90 with 2 quantifiers.  (Contributed by
       NM, 30-Apr-1995.) $)
${
	$d x ps $.
	$d y ps $.
	f19.41vv_0 $f wff ph $.
	f19.41vv_1 $f wff ps $.
	f19.41vv_2 $f set x $.
	f19.41vv_3 $f set y $.
	19.41vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) ) $= f19.41vv_0 f19.41vv_1 wa f19.41vv_3 wex f19.41vv_2 wex f19.41vv_0 f19.41vv_3 wex f19.41vv_1 wa f19.41vv_2 wex f19.41vv_0 f19.41vv_3 wex f19.41vv_2 wex f19.41vv_1 wa f19.41vv_0 f19.41vv_1 wa f19.41vv_3 wex f19.41vv_0 f19.41vv_3 wex f19.41vv_1 wa f19.41vv_2 f19.41vv_0 f19.41vv_1 f19.41vv_3 19.41v exbii f19.41vv_0 f19.41vv_3 wex f19.41vv_1 f19.41vv_2 19.41v bitri $.
$}
$( Theorem 19.41 of [Margaris] p. 90 with 3 quantifiers.  (Contributed by
       NM, 30-Apr-1995.) $)
${
	$d x ps $.
	$d y ps $.
	$d z ps $.
	f19.41vvv_0 $f wff ph $.
	f19.41vvv_1 $f wff ps $.
	f19.41vvv_2 $f set x $.
	f19.41vvv_3 $f set y $.
	f19.41vvv_4 $f set z $.
	19.41vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <-> ( E. x E. y E. z ph /\ ps ) ) $= f19.41vvv_0 f19.41vvv_1 wa f19.41vvv_4 wex f19.41vvv_3 wex f19.41vvv_2 wex f19.41vvv_0 f19.41vvv_4 wex f19.41vvv_3 wex f19.41vvv_1 wa f19.41vvv_2 wex f19.41vvv_0 f19.41vvv_4 wex f19.41vvv_3 wex f19.41vvv_2 wex f19.41vvv_1 wa f19.41vvv_0 f19.41vvv_1 wa f19.41vvv_4 wex f19.41vvv_3 wex f19.41vvv_0 f19.41vvv_4 wex f19.41vvv_3 wex f19.41vvv_1 wa f19.41vvv_2 f19.41vvv_0 f19.41vvv_1 f19.41vvv_3 f19.41vvv_4 19.41vv exbii f19.41vvv_0 f19.41vvv_4 wex f19.41vvv_3 wex f19.41vvv_1 f19.41vvv_2 19.41v bitri $.
$}
$( Theorem 19.41 of [Margaris] p. 90 with 4 quantifiers.  (Contributed by
       FL, 14-Jul-2007.) $)
${
	$d w ps $.
	$d x ps $.
	$d y ps $.
	$d z ps $.
	f19.41vvvv_0 $f wff ph $.
	f19.41vvvv_1 $f wff ps $.
	f19.41vvvv_2 $f set x $.
	f19.41vvvv_3 $f set y $.
	f19.41vvvv_4 $f set z $.
	f19.41vvvv_5 $f set w $.
	19.41vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <-> ( E. w E. x E. y E. z ph /\ ps ) ) $= f19.41vvvv_0 f19.41vvvv_1 wa f19.41vvvv_4 wex f19.41vvvv_3 wex f19.41vvvv_2 wex f19.41vvvv_5 wex f19.41vvvv_0 f19.41vvvv_4 wex f19.41vvvv_3 wex f19.41vvvv_2 wex f19.41vvvv_1 wa f19.41vvvv_5 wex f19.41vvvv_0 f19.41vvvv_4 wex f19.41vvvv_3 wex f19.41vvvv_2 wex f19.41vvvv_5 wex f19.41vvvv_1 wa f19.41vvvv_0 f19.41vvvv_1 wa f19.41vvvv_4 wex f19.41vvvv_3 wex f19.41vvvv_2 wex f19.41vvvv_0 f19.41vvvv_4 wex f19.41vvvv_3 wex f19.41vvvv_2 wex f19.41vvvv_1 wa f19.41vvvv_5 f19.41vvvv_0 f19.41vvvv_1 f19.41vvvv_2 f19.41vvvv_3 f19.41vvvv_4 19.41vvv exbii f19.41vvvv_0 f19.41vvvv_4 wex f19.41vvvv_3 wex f19.41vvvv_2 wex f19.41vvvv_1 f19.41vvvv_5 19.41v bitri $.
$}
$( Special case of Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ph $.
	f19.42v_0 $f wff ph $.
	f19.42v_1 $f wff ps $.
	f19.42v_2 $f set x $.
	19.42v $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $= f19.42v_0 f19.42v_1 f19.42v_2 f19.42v_0 f19.42v_2 nfv 19.42 $.
$}
$( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)
${
	$d y ph $.
	fexdistr_0 $f wff ph $.
	fexdistr_1 $f wff ps $.
	fexdistr_2 $f set x $.
	fexdistr_3 $f set y $.
	exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $= fexdistr_0 fexdistr_1 wa fexdistr_3 wex fexdistr_0 fexdistr_1 fexdistr_3 wex wa fexdistr_2 fexdistr_0 fexdistr_1 fexdistr_3 19.42v exbii $.
$}
$( Theorem 19.42 of [Margaris] p. 90 with 2 quantifiers.  (Contributed by
       NM, 16-Mar-1995.) $)
${
	$d x ph $.
	$d y ph $.
	f19.42vv_0 $f wff ph $.
	f19.42vv_1 $f wff ps $.
	f19.42vv_2 $f set x $.
	f19.42vv_3 $f set y $.
	19.42vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) ) $= f19.42vv_0 f19.42vv_1 wa f19.42vv_3 wex f19.42vv_2 wex f19.42vv_0 f19.42vv_1 f19.42vv_3 wex wa f19.42vv_2 wex f19.42vv_0 f19.42vv_1 f19.42vv_3 wex f19.42vv_2 wex wa f19.42vv_0 f19.42vv_1 f19.42vv_2 f19.42vv_3 exdistr f19.42vv_0 f19.42vv_1 f19.42vv_3 wex f19.42vv_2 19.42v bitri $.
$}
$( Theorem 19.42 of [Margaris] p. 90 with 3 quantifiers.  (Contributed by
       NM, 21-Sep-2011.) $)
${
	$d x ph $.
	$d y ph $.
	$d z ph $.
	f19.42vvv_0 $f wff ph $.
	f19.42vvv_1 $f wff ps $.
	f19.42vvv_2 $f set x $.
	f19.42vvv_3 $f set y $.
	f19.42vvv_4 $f set z $.
	19.42vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <-> ( ph /\ E. x E. y E. z ps ) ) $= f19.42vvv_0 f19.42vvv_1 wa f19.42vvv_4 wex f19.42vvv_3 wex f19.42vvv_2 wex f19.42vvv_0 f19.42vvv_1 f19.42vvv_4 wex f19.42vvv_3 wex wa f19.42vvv_2 wex f19.42vvv_0 f19.42vvv_1 f19.42vvv_4 wex f19.42vvv_3 wex f19.42vvv_2 wex wa f19.42vvv_0 f19.42vvv_1 wa f19.42vvv_4 wex f19.42vvv_3 wex f19.42vvv_0 f19.42vvv_1 f19.42vvv_4 wex f19.42vvv_3 wex wa f19.42vvv_2 f19.42vvv_0 f19.42vvv_1 f19.42vvv_3 f19.42vvv_4 19.42vv exbii f19.42vvv_0 f19.42vvv_1 f19.42vvv_4 wex f19.42vvv_3 wex f19.42vvv_2 19.42v bitri $.
$}
$( Distribution of existential quantifiers.  (Contributed by NM,
       17-Mar-1995.) $)
${
	$d y ph $.
	$d z ph $.
	fexdistr2_0 $f wff ph $.
	fexdistr2_1 $f wff ps $.
	fexdistr2_2 $f set x $.
	fexdistr2_3 $f set y $.
	fexdistr2_4 $f set z $.
	exdistr2 $p |- ( E. x E. y E. z ( ph /\ ps ) <-> E. x ( ph /\ E. y E. z ps ) ) $= fexdistr2_0 fexdistr2_1 wa fexdistr2_4 wex fexdistr2_3 wex fexdistr2_0 fexdistr2_1 fexdistr2_4 wex fexdistr2_3 wex wa fexdistr2_2 fexdistr2_0 fexdistr2_1 fexdistr2_3 fexdistr2_4 19.42vv exbii $.
$}
$( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$d y ph $.
	$d z ph $.
	$d z ps $.
	f3exdistr_0 $f wff ph $.
	f3exdistr_1 $f wff ps $.
	f3exdistr_2 $f wff ch $.
	f3exdistr_3 $f set x $.
	f3exdistr_4 $f set y $.
	f3exdistr_5 $f set z $.
	3exdistr $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <-> E. x ( ph /\ E. y ( ps /\ E. z ch ) ) ) $= f3exdistr_0 f3exdistr_1 f3exdistr_2 w3a f3exdistr_5 wex f3exdistr_4 wex f3exdistr_0 f3exdistr_1 f3exdistr_2 f3exdistr_5 wex wa f3exdistr_4 wex wa f3exdistr_3 f3exdistr_0 f3exdistr_1 f3exdistr_2 w3a f3exdistr_5 wex f3exdistr_4 wex f3exdistr_0 f3exdistr_1 f3exdistr_2 wa wa f3exdistr_5 wex f3exdistr_4 wex f3exdistr_0 f3exdistr_1 f3exdistr_2 wa f3exdistr_5 wex f3exdistr_4 wex wa f3exdistr_0 f3exdistr_1 f3exdistr_2 f3exdistr_5 wex wa f3exdistr_4 wex wa f3exdistr_0 f3exdistr_1 f3exdistr_2 w3a f3exdistr_0 f3exdistr_1 f3exdistr_2 wa wa f3exdistr_4 f3exdistr_5 f3exdistr_0 f3exdistr_1 f3exdistr_2 3anass 2exbii f3exdistr_0 f3exdistr_1 f3exdistr_2 wa f3exdistr_4 f3exdistr_5 19.42vv f3exdistr_1 f3exdistr_2 wa f3exdistr_5 wex f3exdistr_4 wex f3exdistr_1 f3exdistr_2 f3exdistr_5 wex wa f3exdistr_4 wex f3exdistr_0 f3exdistr_1 f3exdistr_2 f3exdistr_4 f3exdistr_5 exdistr anbi2i 3bitri exbii $.
$}
$( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)
${
	$d y ph $.
	$d z ph $.
	$d w ph $.
	$d z ps $.
	$d w ps $.
	$d w ch $.
	f4exdistr_0 $f wff ph $.
	f4exdistr_1 $f wff ps $.
	f4exdistr_2 $f wff ch $.
	f4exdistr_3 $f wff th $.
	f4exdistr_4 $f set x $.
	f4exdistr_5 $f set y $.
	f4exdistr_6 $f set z $.
	f4exdistr_7 $f set w $.
	4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $= f4exdistr_0 f4exdistr_1 wa f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 wex f4exdistr_6 wex f4exdistr_5 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_6 wex wa f4exdistr_5 wex wa f4exdistr_4 f4exdistr_0 f4exdistr_1 wa f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 wex f4exdistr_6 wex f4exdistr_5 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_6 wex wa wa f4exdistr_5 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_6 wex wa f4exdistr_5 wex wa f4exdistr_0 f4exdistr_1 wa f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 wex f4exdistr_6 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_6 wex wa wa f4exdistr_5 f4exdistr_0 f4exdistr_1 wa f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 wex f4exdistr_6 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa wa wa f4exdistr_6 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa wa f4exdistr_6 wex wa f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_6 wex wa wa f4exdistr_0 f4exdistr_1 wa f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa wa wa f4exdistr_6 f4exdistr_0 f4exdistr_1 wa f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 wa wa wa f4exdistr_7 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa wa wa f4exdistr_0 f4exdistr_1 wa f4exdistr_2 f4exdistr_3 wa wa f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 wa wa wa f4exdistr_7 f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 wa anass exbii f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 wa wa wa f4exdistr_7 wex f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 wex wa f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 wa f4exdistr_7 wex wa wa f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa wa wa f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 19.42v f4exdistr_1 f4exdistr_2 f4exdistr_3 wa wa f4exdistr_7 wex f4exdistr_1 f4exdistr_2 f4exdistr_3 wa f4exdistr_7 wex wa f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 wa f4exdistr_7 19.42v anbi2i f4exdistr_1 f4exdistr_2 f4exdistr_3 wa f4exdistr_7 wex wa f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa wa f4exdistr_0 f4exdistr_2 f4exdistr_3 wa f4exdistr_7 wex f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 19.42v anbi2i anbi2i 3bitri bitri exbii f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa wa f4exdistr_6 19.42v f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa wa f4exdistr_6 wex f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_6 wex wa f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_6 19.42v anbi2i 3bitri exbii f4exdistr_0 f4exdistr_1 f4exdistr_2 f4exdistr_3 f4exdistr_7 wex wa f4exdistr_6 wex wa f4exdistr_5 19.42v bitri exbii $.
$}
$( Rearrange existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
${
	feean_0 $f wff ph $.
	feean_1 $f wff ps $.
	feean_2 $f set x $.
	feean_3 $f set y $.
	eeean_0 $e |- F/ y ph $.
	eeean_1 $e |- F/ x ps $.
	eean $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $= feean_0 feean_1 wa feean_3 wex feean_2 wex feean_0 feean_1 feean_3 wex wa feean_2 wex feean_0 feean_2 wex feean_1 feean_3 wex wa feean_0 feean_1 wa feean_3 wex feean_0 feean_1 feean_3 wex wa feean_2 feean_0 feean_1 feean_3 eeean_0 19.42 exbii feean_0 feean_1 feean_3 wex feean_2 feean_1 feean_2 feean_3 eeean_1 nfex 19.41 bitri $.
$}
$( Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.) $)
${
	$d y ph $.
	$d x ps $.
	feeanv_0 $f wff ph $.
	feeanv_1 $f wff ps $.
	feeanv_2 $f set x $.
	feeanv_3 $f set y $.
	eeanv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $= feeanv_0 feeanv_1 feeanv_2 feeanv_3 feeanv_0 feeanv_3 nfv feeanv_1 feeanv_2 nfv eean $.
$}
$( Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$d y ph $.
	$d z ph $.
	$d x z ps $.
	$d x y ch $.
	feeeanv_0 $f wff ph $.
	feeeanv_1 $f wff ps $.
	feeeanv_2 $f wff ch $.
	feeeanv_3 $f set x $.
	feeeanv_4 $f set y $.
	feeeanv_5 $f set z $.
	eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <-> ( E. x ph /\ E. y ps /\ E. z ch ) ) $= feeeanv_0 feeeanv_1 feeeanv_2 w3a feeeanv_5 wex feeeanv_4 wex feeeanv_3 wex feeeanv_0 feeeanv_1 wa feeeanv_2 wa feeeanv_5 wex feeeanv_4 wex feeeanv_3 wex feeeanv_0 feeeanv_1 wa feeeanv_4 wex feeeanv_2 feeeanv_5 wex wa feeeanv_3 wex feeeanv_0 feeeanv_3 wex feeeanv_1 feeeanv_4 wex feeeanv_2 feeeanv_5 wex w3a feeeanv_0 feeeanv_1 feeeanv_2 w3a feeeanv_0 feeeanv_1 wa feeeanv_2 wa feeeanv_3 feeeanv_4 feeeanv_5 feeeanv_0 feeeanv_1 feeeanv_2 df-3an 3exbii feeeanv_0 feeeanv_1 wa feeeanv_2 wa feeeanv_5 wex feeeanv_4 wex feeeanv_0 feeeanv_1 wa feeeanv_4 wex feeeanv_2 feeeanv_5 wex wa feeeanv_3 feeeanv_0 feeeanv_1 wa feeeanv_2 feeeanv_4 feeeanv_5 eeanv exbii feeeanv_0 feeeanv_1 wa feeeanv_4 wex feeeanv_3 wex feeeanv_2 feeeanv_5 wex wa feeeanv_0 feeeanv_3 wex feeeanv_1 feeeanv_4 wex wa feeeanv_2 feeeanv_5 wex wa feeeanv_0 feeeanv_1 wa feeeanv_4 wex feeeanv_2 feeeanv_5 wex wa feeeanv_3 wex feeeanv_0 feeeanv_3 wex feeeanv_1 feeeanv_4 wex feeeanv_2 feeeanv_5 wex w3a feeeanv_0 feeeanv_1 wa feeeanv_4 wex feeeanv_3 wex feeeanv_0 feeeanv_3 wex feeeanv_1 feeeanv_4 wex wa feeeanv_2 feeeanv_5 wex feeeanv_0 feeeanv_1 feeeanv_3 feeeanv_4 eeanv anbi1i feeeanv_0 feeeanv_1 wa feeeanv_4 wex feeeanv_2 feeeanv_5 wex feeeanv_3 19.41v feeeanv_0 feeeanv_3 wex feeeanv_1 feeeanv_4 wex feeeanv_2 feeeanv_5 wex df-3an 3bitr4i 3bitri $.
$}
$( Rearrange existential quantifiers.  (Contributed by NM, 31-Jul-1995.) $)
${
	$d z ph $.
	$d w ph $.
	$d x ps $.
	$d y ps $.
	$d y z $.
	$d w x $.
	fee4anv_0 $f wff ph $.
	fee4anv_1 $f wff ps $.
	fee4anv_2 $f set x $.
	fee4anv_3 $f set y $.
	fee4anv_4 $f set z $.
	fee4anv_5 $f set w $.
	ee4anv $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <-> ( E. x E. y ph /\ E. z E. w ps ) ) $= fee4anv_0 fee4anv_1 wa fee4anv_5 wex fee4anv_4 wex fee4anv_3 wex fee4anv_2 wex fee4anv_0 fee4anv_1 wa fee4anv_5 wex fee4anv_3 wex fee4anv_4 wex fee4anv_2 wex fee4anv_0 fee4anv_3 wex fee4anv_1 fee4anv_5 wex wa fee4anv_4 wex fee4anv_2 wex fee4anv_0 fee4anv_3 wex fee4anv_2 wex fee4anv_1 fee4anv_5 wex fee4anv_4 wex wa fee4anv_0 fee4anv_1 wa fee4anv_5 wex fee4anv_4 wex fee4anv_3 wex fee4anv_0 fee4anv_1 wa fee4anv_5 wex fee4anv_3 wex fee4anv_4 wex fee4anv_2 fee4anv_0 fee4anv_1 wa fee4anv_5 wex fee4anv_3 fee4anv_4 excom exbii fee4anv_0 fee4anv_1 wa fee4anv_5 wex fee4anv_3 wex fee4anv_0 fee4anv_3 wex fee4anv_1 fee4anv_5 wex wa fee4anv_2 fee4anv_4 fee4anv_0 fee4anv_1 fee4anv_3 fee4anv_5 eeanv 2exbii fee4anv_0 fee4anv_3 wex fee4anv_1 fee4anv_5 wex fee4anv_2 fee4anv_4 eeanv 3bitri $.
$}
$( Deduction for generalization rule for negated wff.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x ph $.
	fnexdv_0 $f wff ph $.
	fnexdv_1 $f wff ps $.
	fnexdv_2 $f set x $.
	enexdv_0 $e |- ( ph -> -. ps ) $.
	nexdv $p |- ( ph -> -. E. x ps ) $= fnexdv_0 fnexdv_1 fnexdv_2 fnexdv_0 fnexdv_2 nfv enexdv_0 nexd $.
$}
$( One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be
     read:  " ` x = y -> ( ph ( x , x ) -> ph ( x , y ) ) ` , provided that
     ` y ` is free for ` x ` in ` ph ( x , x ) ` ."  Axiom 7 of [Mendelson]
     p. 95.  (Contributed by NM, 15-Feb-2005.) $)
${
	fstdpc7_0 $f wff ph $.
	fstdpc7_1 $f set x $.
	fstdpc7_2 $f set y $.
	stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $= fstdpc7_0 fstdpc7_2 fstdpc7_1 wsb fstdpc7_0 wi fstdpc7_2 fstdpc7_1 fstdpc7_0 fstdpc7_2 fstdpc7_1 sbequ2 equcoms $.
$}
$( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsbequ1_0 $f wff ph $.
	fsbequ1_1 $f set x $.
	fsbequ1_2 $f set y $.
	sbequ1 $p |- ( x = y -> ( ph -> [ y / x ] ph ) ) $= fsbequ1_1 fsbequ1_2 weq fsbequ1_0 fsbequ1_0 fsbequ1_1 fsbequ1_2 wsb fsbequ1_1 fsbequ1_2 weq fsbequ1_0 wa fsbequ1_1 fsbequ1_2 weq fsbequ1_0 wi fsbequ1_1 fsbequ1_2 weq fsbequ1_0 wa fsbequ1_1 wex fsbequ1_0 fsbequ1_1 fsbequ1_2 wsb fsbequ1_1 fsbequ1_2 weq fsbequ1_0 pm3.4 fsbequ1_1 fsbequ1_2 weq fsbequ1_0 wa fsbequ1_1 19.8a fsbequ1_0 fsbequ1_1 fsbequ1_2 df-sb sylanbrc ex $.
$}
$( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsbequ12_0 $f wff ph $.
	fsbequ12_1 $f set x $.
	fsbequ12_2 $f set y $.
	sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $= fsbequ12_1 fsbequ12_2 weq fsbequ12_0 fsbequ12_0 fsbequ12_1 fsbequ12_2 wsb fsbequ12_0 fsbequ12_1 fsbequ12_2 sbequ1 fsbequ12_0 fsbequ12_1 fsbequ12_2 sbequ2 impbid $.
$}
$( An equality theorem for substitution.  (Contributed by NM, 6-Oct-2004.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)
${
	fsbequ12r_0 $f wff ph $.
	fsbequ12r_1 $f set x $.
	fsbequ12r_2 $f set y $.
	sbequ12r $p |- ( x = y -> ( [ x / y ] ph <-> ph ) ) $= fsbequ12r_0 fsbequ12r_2 fsbequ12r_1 wsb fsbequ12r_0 wb fsbequ12r_2 fsbequ12r_1 fsbequ12r_2 fsbequ12r_1 weq fsbequ12r_0 fsbequ12r_0 fsbequ12r_2 fsbequ12r_1 wsb fsbequ12r_0 fsbequ12r_2 fsbequ12r_1 sbequ12 bicomd equcoms $.
$}
$( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
${
	fsbequ12a_0 $f wff ph $.
	fsbequ12a_1 $f set x $.
	fsbequ12a_2 $f set y $.
	sbequ12a $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $= fsbequ12a_1 fsbequ12a_2 weq fsbequ12a_0 fsbequ12a_0 fsbequ12a_1 fsbequ12a_2 wsb fsbequ12a_0 fsbequ12a_2 fsbequ12a_1 wsb fsbequ12a_0 fsbequ12a_1 fsbequ12a_2 sbequ12 fsbequ12a_0 fsbequ12a_0 fsbequ12a_2 fsbequ12a_1 wsb wb fsbequ12a_2 fsbequ12a_1 fsbequ12a_0 fsbequ12a_2 fsbequ12a_1 sbequ12 equcoms bitr3d $.
$}
$( An identity theorem for substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint).  (Contributed by NM, 5-Aug-1993.) $)
${
	fsbid_0 $f wff ph $.
	fsbid_1 $f set x $.
	sbid $p |- ( [ x / x ] ph <-> ph ) $= fsbid_0 fsbid_0 fsbid_1 fsbid_1 wsb fsbid_1 fsbid_1 weq fsbid_0 fsbid_0 fsbid_1 fsbid_1 wsb wb fsbid_1 equid fsbid_0 fsbid_1 fsbid_1 sbequ12 ax-mp bicomi $.
$}
$( A version of ~ sb4 that doesn't require a distinctor antecedent.
     (Contributed by NM, 2-Feb-2007.) $)
${
	fsb4a_0 $f wff ph $.
	fsb4a_1 $f set x $.
	fsb4a_2 $f set y $.
	sb4a $p |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) ) $= fsb4a_0 fsb4a_2 wal fsb4a_1 fsb4a_2 wsb fsb4a_1 fsb4a_2 weq fsb4a_0 fsb4a_2 wal wa fsb4a_1 wex fsb4a_1 fsb4a_2 weq fsb4a_0 wi fsb4a_1 wal fsb4a_0 fsb4a_2 wal fsb4a_1 fsb4a_2 sb1 fsb4a_0 fsb4a_1 fsb4a_2 equs5a syl $.
$}
$( One direction of a simplified definition of substitution that unlike ~ sb4
     doesn't require a distinctor antecedent.  (Contributed by NM,
     2-Feb-2007.) $)
${
	fsb4e_0 $f wff ph $.
	fsb4e_1 $f set x $.
	fsb4e_2 $f set y $.
	sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $= fsb4e_0 fsb4e_1 fsb4e_2 wsb fsb4e_1 fsb4e_2 weq fsb4e_0 wa fsb4e_1 wex fsb4e_1 fsb4e_2 weq fsb4e_0 fsb4e_2 wex wi fsb4e_1 wal fsb4e_0 fsb4e_1 fsb4e_2 sb1 fsb4e_0 fsb4e_1 fsb4e_2 equs5e syl $.
$}

