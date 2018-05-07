$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Rule_scheme_ax-gen_(Generalization).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
         Axiom scheme ax-5 (Quantified Implication)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105.
     (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fax-5_0 $f wff ph $.
	fax-5_1 $f wff ps $.
	fax-5_2 $f set x $.
	ax-5 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.
$}
$( Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by O'Cat, 30-Mar-2008.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	falim_0 $f wff ph $.
	falim_1 $f wff ps $.
	falim_2 $f set x $.
	alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $= falim_0 falim_1 falim_2 ax-5 $.
$}
$( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	falimi_0 $f wff ph $.
	falimi_1 $f wff ps $.
	falimi_2 $f set x $.
	ealimi_0 $e |- ( ph -> ps ) $.
	alimi $p |- ( A. x ph -> A. x ps ) $= falimi_0 falimi_1 wi falimi_0 falimi_2 wal falimi_1 falimi_2 wal wi falimi_2 falimi_0 falimi_1 falimi_2 ax-5 ealimi_0 mpg $.
$}
$( Inference doubly quantifying both antecedent and consequent.
       (Contributed by NM, 3-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f2alimi_0 $f wff ph $.
	f2alimi_1 $f wff ps $.
	f2alimi_2 $f set x $.
	f2alimi_3 $f set y $.
	e2alimi_0 $e |- ( ph -> ps ) $.
	2alimi $p |- ( A. x A. y ph -> A. x A. y ps ) $= f2alimi_0 f2alimi_3 wal f2alimi_1 f2alimi_3 wal f2alimi_2 f2alimi_0 f2alimi_1 f2alimi_3 e2alimi_0 alimi alimi $.
$}
$( Inference quantifying antecedent, nested antecedent, and consequent.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fal2imi_0 $f wff ph $.
	fal2imi_1 $f wff ps $.
	fal2imi_2 $f wff ch $.
	fal2imi_3 $f set x $.
	eal2imi_0 $e |- ( ph -> ( ps -> ch ) ) $.
	al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $= fal2imi_0 fal2imi_3 wal fal2imi_1 fal2imi_2 wi fal2imi_3 wal fal2imi_1 fal2imi_3 wal fal2imi_2 fal2imi_3 wal wi fal2imi_0 fal2imi_1 fal2imi_2 wi fal2imi_3 eal2imi_0 alimi fal2imi_1 fal2imi_2 fal2imi_3 alim syl $.
$}
$( Variant of ~ al2imi with conjunctive antecedent.  (Contributed by Andrew
       Salmon, 8-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	falanimi_0 $f wff ph $.
	falanimi_1 $f wff ps $.
	falanimi_2 $f wff ch $.
	falanimi_3 $f set x $.
	ealanimi_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $= falanimi_0 falanimi_3 wal falanimi_1 falanimi_3 wal falanimi_2 falanimi_3 wal falanimi_0 falanimi_1 falanimi_2 falanimi_3 falanimi_0 falanimi_1 falanimi_2 ealanimi_0 ex al2imi imp $.
$}
$( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM,
       4-Jan-2002.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	falimdh_0 $f wff ph $.
	falimdh_1 $f wff ps $.
	falimdh_2 $f wff ch $.
	falimdh_3 $f set x $.
	ealimdh_0 $e |- ( ph -> A. x ph ) $.
	ealimdh_1 $e |- ( ph -> ( ps -> ch ) ) $.
	alimdh $p |- ( ph -> ( A. x ps -> A. x ch ) ) $= falimdh_0 falimdh_0 falimdh_3 wal falimdh_1 falimdh_3 wal falimdh_2 falimdh_3 wal wi ealimdh_0 falimdh_0 falimdh_1 falimdh_2 falimdh_3 ealimdh_1 al2imi syl $.
$}
$( Theorem 19.15 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	falbi_0 $f wff ph $.
	falbi_1 $f wff ps $.
	falbi_2 $f set x $.
	albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $= falbi_0 falbi_1 wb falbi_2 wal falbi_0 falbi_2 wal falbi_1 falbi_2 wal falbi_0 falbi_1 wb falbi_0 falbi_1 falbi_2 falbi_0 falbi_1 bi1 al2imi falbi_0 falbi_1 wb falbi_1 falbi_0 falbi_2 falbi_0 falbi_1 bi2 al2imi impbid $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	falrimih_0 $f wff ph $.
	falrimih_1 $f wff ps $.
	falrimih_2 $f set x $.
	ealrimih_0 $e |- ( ph -> A. x ph ) $.
	ealrimih_1 $e |- ( ph -> ps ) $.
	alrimih $p |- ( ph -> A. x ps ) $= falrimih_0 falrimih_0 falrimih_2 wal falrimih_1 falrimih_2 wal ealrimih_0 falrimih_0 falrimih_1 falrimih_2 ealrimih_1 alimi syl $.
$}
$( Inference adding universal quantifier to both sides of an equivalence.
       (Contributed by NM, 7-Aug-1994.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	falbii_0 $f wff ph $.
	falbii_1 $f wff ps $.
	falbii_2 $f set x $.
	ealbii_0 $e |- ( ph <-> ps ) $.
	albii $p |- ( A. x ph <-> A. x ps ) $= falbii_0 falbii_1 wb falbii_0 falbii_2 wal falbii_1 falbii_2 wal wb falbii_2 falbii_0 falbii_1 falbii_2 albi ealbii_0 mpg $.
$}
$( Theorem albii is the congruence law for universal quantification. $)
$( $j congruence 'albii'; $)
$( Inference adding two universal quantifiers to both sides of an
       equivalence.  (Contributed by NM, 9-Mar-1997.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f2albii_0 $f wff ph $.
	f2albii_1 $f wff ps $.
	f2albii_2 $f set x $.
	f2albii_3 $f set y $.
	e2albii_0 $e |- ( ph <-> ps ) $.
	2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $= f2albii_0 f2albii_3 wal f2albii_1 f2albii_3 wal f2albii_2 f2albii_0 f2albii_1 f2albii_3 e2albii_0 albii albii $.
$}
$( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfreq for equality version.  (Contributed by
       Jonathan Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fhbxfrbi_0 $f wff ph $.
	fhbxfrbi_1 $f wff ps $.
	fhbxfrbi_2 $f set x $.
	ehbxfrbi_0 $e |- ( ph <-> ps ) $.
	ehbxfrbi_1 $e |- ( ps -> A. x ps ) $.
	hbxfrbi $p |- ( ph -> A. x ph ) $= fhbxfrbi_1 fhbxfrbi_1 fhbxfrbi_2 wal fhbxfrbi_0 fhbxfrbi_0 fhbxfrbi_2 wal ehbxfrbi_1 ehbxfrbi_0 fhbxfrbi_0 fhbxfrbi_1 fhbxfrbi_2 ehbxfrbi_0 albii 3imtr4i $.
$}
$( Equality theorem for not-free.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fnfbii_0 $f wff ph $.
	fnfbii_1 $f wff ps $.
	fnfbii_2 $f set x $.
	enfbii_0 $e |- ( ph <-> ps ) $.
	nfbii $p |- ( F/ x ph <-> F/ x ps ) $= fnfbii_0 fnfbii_0 fnfbii_2 wal wi fnfbii_2 wal fnfbii_1 fnfbii_1 fnfbii_2 wal wi fnfbii_2 wal fnfbii_0 fnfbii_2 wnf fnfbii_1 fnfbii_2 wnf fnfbii_0 fnfbii_0 fnfbii_2 wal wi fnfbii_1 fnfbii_1 fnfbii_2 wal wi fnfbii_2 fnfbii_0 fnfbii_1 fnfbii_0 fnfbii_2 wal fnfbii_1 fnfbii_2 wal enfbii_0 fnfbii_0 fnfbii_1 fnfbii_2 enfbii_0 albii imbi12i albii fnfbii_0 fnfbii_2 df-nf fnfbii_1 fnfbii_2 df-nf 3bitr4i $.
$}
$( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fnfxfr_0 $f wff ph $.
	fnfxfr_1 $f wff ps $.
	fnfxfr_2 $f set x $.
	enfxfr_0 $e |- ( ph <-> ps ) $.
	enfxfr_1 $e |- F/ x ps $.
	nfxfr $p |- F/ x ph $= fnfxfr_0 fnfxfr_2 wnf fnfxfr_1 fnfxfr_2 wnf enfxfr_1 fnfxfr_0 fnfxfr_1 fnfxfr_2 enfxfr_0 nfbii mpbir $.
$}
$( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fnfxfrd_0 $f wff ph $.
	fnfxfrd_1 $f wff ps $.
	fnfxfrd_2 $f wff ch $.
	fnfxfrd_3 $f set x $.
	enfxfrd_0 $e |- ( ph <-> ps ) $.
	enfxfrd_1 $e |- ( ch -> F/ x ps ) $.
	nfxfrd $p |- ( ch -> F/ x ph ) $= fnfxfrd_2 fnfxfrd_1 fnfxfrd_3 wnf fnfxfrd_0 fnfxfrd_3 wnf enfxfrd_1 fnfxfrd_0 fnfxfrd_1 fnfxfrd_3 enfxfrd_0 nfbii sylibr $.
$}
$( Theorem 19.6 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	falex_0 $f wff ph $.
	falex_1 $f set x $.
	alex $p |- ( A. x ph <-> -. E. x -. ph ) $= falex_0 falex_1 wal falex_0 wn wn falex_1 wal falex_0 wn falex_1 wex wn falex_0 falex_0 wn wn falex_1 falex_0 notnot albii falex_0 wn falex_1 alnex bitri $.
$}
$( Part of theorem *11.5 in [WhiteheadRussell] p. 164.  (Contributed by
     Andrew Salmon, 24-May-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	f2nalexn_0 $f wff ph $.
	f2nalexn_1 $f set x $.
	f2nalexn_2 $f set y $.
	2nalexn $p |- ( -. A. x A. y ph <-> E. x E. y -. ph ) $= f2nalexn_0 wn f2nalexn_2 wex f2nalexn_1 wex f2nalexn_0 f2nalexn_2 wal f2nalexn_1 wal wn f2nalexn_0 wn f2nalexn_2 wex f2nalexn_1 wex f2nalexn_0 wn f2nalexn_2 wex wn f2nalexn_1 wal f2nalexn_0 f2nalexn_2 wal f2nalexn_1 wal f2nalexn_0 wn f2nalexn_2 wex f2nalexn_1 df-ex f2nalexn_0 f2nalexn_2 wal f2nalexn_0 wn f2nalexn_2 wex wn f2nalexn_1 f2nalexn_0 f2nalexn_2 alex albii xchbinxr bicomi $.
$}
$( Theorem 19.14 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	fexnal_0 $f wff ph $.
	fexnal_1 $f set x $.
	exnal $p |- ( E. x -. ph <-> -. A. x ph ) $= fexnal_0 fexnal_1 wal fexnal_0 wn fexnal_1 wex fexnal_0 fexnal_1 alex con2bii $.
$}
$( Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 4-Jul-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fexim_0 $f wff ph $.
	fexim_1 $f wff ps $.
	fexim_2 $f set x $.
	exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $= fexim_0 fexim_1 wi fexim_2 wal fexim_1 fexim_2 wex fexim_0 fexim_2 wex fexim_0 fexim_1 wi fexim_2 wal fexim_1 wn fexim_2 wal fexim_0 wn fexim_2 wal fexim_1 fexim_2 wex wn fexim_0 fexim_2 wex wn fexim_0 fexim_1 wi fexim_1 wn fexim_0 wn fexim_2 fexim_0 fexim_1 con3 al2imi fexim_1 fexim_2 alnex fexim_0 fexim_2 alnex 3imtr3g con4d $.
$}
$( Inference adding existential quantifier to antecedent and consequent.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	feximi_0 $f wff ph $.
	feximi_1 $f wff ps $.
	feximi_2 $f set x $.
	eeximi_0 $e |- ( ph -> ps ) $.
	eximi $p |- ( E. x ph -> E. x ps ) $= feximi_0 feximi_1 wi feximi_0 feximi_2 wex feximi_1 feximi_2 wex wi feximi_2 feximi_0 feximi_1 feximi_2 exim eeximi_0 mpg $.
$}
$( Inference adding two existential quantifiers to antecedent and
       consequent.  (Contributed by NM, 3-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f2eximi_0 $f wff ph $.
	f2eximi_1 $f wff ps $.
	f2eximi_2 $f set x $.
	f2eximi_3 $f set y $.
	e2eximi_0 $e |- ( ph -> ps ) $.
	2eximi $p |- ( E. x E. y ph -> E. x E. y ps ) $= f2eximi_0 f2eximi_3 wex f2eximi_1 f2eximi_3 wex f2eximi_2 f2eximi_0 f2eximi_1 f2eximi_3 e2eximi_0 eximi eximi $.
$}
$( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 19-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	falinexa_0 $f wff ph $.
	falinexa_1 $f wff ps $.
	falinexa_2 $f set x $.
	alinexa $p |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) ) $= falinexa_0 falinexa_1 wn wi falinexa_2 wal falinexa_0 falinexa_1 wa wn falinexa_2 wal falinexa_0 falinexa_1 wa falinexa_2 wex wn falinexa_0 falinexa_1 wn wi falinexa_0 falinexa_1 wa wn falinexa_2 falinexa_0 falinexa_1 imnan albii falinexa_0 falinexa_1 wa falinexa_2 alnex bitri $.
$}
$( A relationship between two quantifiers and negation.  (Contributed by NM,
     18-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	falexn_0 $f wff ph $.
	falexn_1 $f set x $.
	falexn_2 $f set y $.
	alexn $p |- ( A. x E. y -. ph <-> -. E. x A. y ph ) $= falexn_0 wn falexn_2 wex falexn_1 wal falexn_0 falexn_2 wal wn falexn_1 wal falexn_0 falexn_2 wal falexn_1 wex wn falexn_0 wn falexn_2 wex falexn_0 falexn_2 wal wn falexn_1 falexn_0 falexn_2 exnal albii falexn_0 falexn_2 wal falexn_1 alnex bitri $.
$}
$( Theorem *11.51 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.)  (Proof shortened by Wolf Lammen, 25-Sep-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	f2exnexn_0 $f wff ph $.
	f2exnexn_1 $f set x $.
	f2exnexn_2 $f set y $.
	2exnexn $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $= f2exnexn_0 wn f2exnexn_2 wex f2exnexn_1 wal f2exnexn_0 f2exnexn_2 wal f2exnexn_1 wex f2exnexn_0 f2exnexn_1 f2exnexn_2 alexn con2bii $.
$}
$( Theorem 19.18 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fexbi_0 $f wff ph $.
	fexbi_1 $f wff ps $.
	fexbi_2 $f set x $.
	exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $= fexbi_0 fexbi_1 wb fexbi_2 wal fexbi_0 fexbi_2 wex fexbi_1 fexbi_2 wex fexbi_0 fexbi_1 wb fexbi_2 wal fexbi_0 fexbi_1 wi fexbi_2 wal fexbi_0 fexbi_2 wex fexbi_1 fexbi_2 wex wi fexbi_0 fexbi_1 wb fexbi_0 fexbi_1 wi fexbi_2 fexbi_0 fexbi_1 bi1 alimi fexbi_0 fexbi_1 fexbi_2 exim syl fexbi_0 fexbi_1 wb fexbi_2 wal fexbi_1 fexbi_0 wi fexbi_2 wal fexbi_1 fexbi_2 wex fexbi_0 fexbi_2 wex wi fexbi_0 fexbi_1 wb fexbi_1 fexbi_0 wi fexbi_2 fexbi_0 fexbi_1 bi2 alimi fexbi_1 fexbi_0 fexbi_2 exim syl impbid $.
$}
$( Inference adding existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 24-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fexbii_0 $f wff ph $.
	fexbii_1 $f wff ps $.
	fexbii_2 $f set x $.
	eexbii_0 $e |- ( ph <-> ps ) $.
	exbii $p |- ( E. x ph <-> E. x ps ) $= fexbii_0 fexbii_1 wb fexbii_0 fexbii_2 wex fexbii_1 fexbii_2 wex wb fexbii_2 fexbii_0 fexbii_1 fexbii_2 exbi eexbii_0 mpg $.
$}
$( Inference adding two existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 16-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f2exbii_0 $f wff ph $.
	f2exbii_1 $f wff ps $.
	f2exbii_2 $f set x $.
	f2exbii_3 $f set y $.
	e2exbii_0 $e |- ( ph <-> ps ) $.
	2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $= f2exbii_0 f2exbii_3 wex f2exbii_1 f2exbii_3 wex f2exbii_2 f2exbii_0 f2exbii_1 f2exbii_3 e2exbii_0 exbii exbii $.
$}
$( Inference adding 3 existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 2-May-1995.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	f3exbii_0 $f wff ph $.
	f3exbii_1 $f wff ps $.
	f3exbii_2 $f set x $.
	f3exbii_3 $f set y $.
	f3exbii_4 $f set z $.
	e3exbii_0 $e |- ( ph <-> ps ) $.
	3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $= f3exbii_0 f3exbii_4 wex f3exbii_1 f3exbii_4 wex f3exbii_2 f3exbii_3 f3exbii_0 f3exbii_1 f3exbii_4 e3exbii_0 exbii 2exbii $.
$}
$( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 25-Mar-1996.)  (Proof shortened by Wolf Lammen, 4-Sep-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fexanali_0 $f wff ph $.
	fexanali_1 $f wff ps $.
	fexanali_2 $f set x $.
	exanali $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $= fexanali_0 fexanali_1 wn wa fexanali_2 wex fexanali_0 fexanali_1 wi wn fexanali_2 wex fexanali_0 fexanali_1 wi fexanali_2 wal wn fexanali_0 fexanali_1 wn wa fexanali_0 fexanali_1 wi wn fexanali_2 fexanali_0 fexanali_1 annim exbii fexanali_0 fexanali_1 wi fexanali_2 exnal bitri $.
$}
$( Commutation of conjunction inside an existential quantifier.  (Contributed
     by NM, 18-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fexancom_0 $f wff ph $.
	fexancom_1 $f wff ps $.
	fexancom_2 $f set x $.
	exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $= fexancom_0 fexancom_1 wa fexancom_1 fexancom_0 wa fexancom_2 fexancom_0 fexancom_1 ancom exbii $.
$}
$( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	falrimdh_0 $f wff ph $.
	falrimdh_1 $f wff ps $.
	falrimdh_2 $f wff ch $.
	falrimdh_3 $f set x $.
	ealrimdh_0 $e |- ( ph -> A. x ph ) $.
	ealrimdh_1 $e |- ( ps -> A. x ps ) $.
	ealrimdh_2 $e |- ( ph -> ( ps -> ch ) ) $.
	alrimdh $p |- ( ph -> ( ps -> A. x ch ) ) $= falrimdh_1 falrimdh_1 falrimdh_3 wal falrimdh_0 falrimdh_2 falrimdh_3 wal ealrimdh_1 falrimdh_0 falrimdh_1 falrimdh_2 falrimdh_3 ealrimdh_0 ealrimdh_2 alimdh syl5 $.
$}
$( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       20-May-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	feximdh_0 $f wff ph $.
	feximdh_1 $f wff ps $.
	feximdh_2 $f wff ch $.
	feximdh_3 $f set x $.
	eeximdh_0 $e |- ( ph -> A. x ph ) $.
	eeximdh_1 $e |- ( ph -> ( ps -> ch ) ) $.
	eximdh $p |- ( ph -> ( E. x ps -> E. x ch ) ) $= feximdh_0 feximdh_1 feximdh_2 wi feximdh_3 wal feximdh_1 feximdh_3 wex feximdh_2 feximdh_3 wex wi feximdh_0 feximdh_1 feximdh_2 wi feximdh_3 eeximdh_0 eeximdh_1 alrimih feximdh_1 feximdh_2 feximdh_3 exim syl $.
$}
$( Deduction for generalization rule for negated wff.  (Contributed by NM,
       2-Jan-2002.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fnexdh_0 $f wff ph $.
	fnexdh_1 $f wff ps $.
	fnexdh_2 $f set x $.
	enexdh_0 $e |- ( ph -> A. x ph ) $.
	enexdh_1 $e |- ( ph -> -. ps ) $.
	nexdh $p |- ( ph -> -. E. x ps ) $= fnexdh_0 fnexdh_1 wn fnexdh_2 wal fnexdh_1 fnexdh_2 wex wn fnexdh_0 fnexdh_1 wn fnexdh_2 enexdh_0 enexdh_1 alrimih fnexdh_1 fnexdh_2 alnex sylib $.
$}
$( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	falbidh_0 $f wff ph $.
	falbidh_1 $f wff ps $.
	falbidh_2 $f wff ch $.
	falbidh_3 $f set x $.
	ealbidh_0 $e |- ( ph -> A. x ph ) $.
	ealbidh_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	albidh $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $= falbidh_0 falbidh_1 falbidh_2 wb falbidh_3 wal falbidh_1 falbidh_3 wal falbidh_2 falbidh_3 wal wb falbidh_0 falbidh_1 falbidh_2 wb falbidh_3 ealbidh_0 ealbidh_1 alrimih falbidh_1 falbidh_2 falbidh_3 albi syl $.
$}
$( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	fexbidh_0 $f wff ph $.
	fexbidh_1 $f wff ps $.
	fexbidh_2 $f wff ch $.
	fexbidh_3 $f set x $.
	eexbidh_0 $e |- ( ph -> A. x ph ) $.
	eexbidh_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	exbidh $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $= fexbidh_0 fexbidh_1 fexbidh_2 wb fexbidh_3 wal fexbidh_1 fexbidh_3 wex fexbidh_2 fexbidh_3 wex wb fexbidh_0 fexbidh_1 fexbidh_2 wb fexbidh_3 eexbidh_0 eexbidh_1 alrimih fexbidh_1 fexbidh_2 fexbidh_3 exbi syl $.
$}
$( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fexsimpl_0 $f wff ph $.
	fexsimpl_1 $f wff ps $.
	fexsimpl_2 $f set x $.
	exsimpl $p |- ( E. x ( ph /\ ps ) -> E. x ph ) $= fexsimpl_0 fexsimpl_1 wa fexsimpl_0 fexsimpl_2 fexsimpl_0 fexsimpl_1 simpl eximi $.
$}
$( Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 147.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 4-Jul-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.26_0 $f wff ph $.
	f19.26_1 $f wff ps $.
	f19.26_2 $f set x $.
	19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $= f19.26_0 f19.26_1 wa f19.26_2 wal f19.26_0 f19.26_2 wal f19.26_1 f19.26_2 wal wa f19.26_0 f19.26_1 wa f19.26_2 wal f19.26_0 f19.26_2 wal f19.26_1 f19.26_2 wal f19.26_0 f19.26_1 wa f19.26_0 f19.26_2 f19.26_0 f19.26_1 simpl alimi f19.26_0 f19.26_1 wa f19.26_1 f19.26_2 f19.26_0 f19.26_1 simpr alimi jca f19.26_0 f19.26_1 f19.26_0 f19.26_1 wa f19.26_2 f19.26_0 f19.26_1 wa id alanimi impbii $.
$}
$( Theorem 19.26 of [Margaris] p. 90 with two quantifiers.  (Contributed by
     NM, 3-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f19.26-2_0 $f wff ph $.
	f19.26-2_1 $f wff ps $.
	f19.26-2_2 $f set x $.
	f19.26-2_3 $f set y $.
	19.26-2 $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x A. y ph /\ A. x A. y ps ) ) $= f19.26-2_0 f19.26-2_1 wa f19.26-2_3 wal f19.26-2_2 wal f19.26-2_0 f19.26-2_3 wal f19.26-2_1 f19.26-2_3 wal wa f19.26-2_2 wal f19.26-2_0 f19.26-2_3 wal f19.26-2_2 wal f19.26-2_1 f19.26-2_3 wal f19.26-2_2 wal wa f19.26-2_0 f19.26-2_1 wa f19.26-2_3 wal f19.26-2_0 f19.26-2_3 wal f19.26-2_1 f19.26-2_3 wal wa f19.26-2_2 f19.26-2_0 f19.26-2_1 f19.26-2_3 19.26 albii f19.26-2_0 f19.26-2_3 wal f19.26-2_1 f19.26-2_3 wal f19.26-2_2 19.26 bitri $.
$}
$( Theorem 19.26 of [Margaris] p. 90 with triple conjunction.  (Contributed
     by NM, 13-Sep-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	f19.26-3an_0 $f wff ph $.
	f19.26-3an_1 $f wff ps $.
	f19.26-3an_2 $f wff ch $.
	f19.26-3an_3 $f set x $.
	19.26-3an $p |- ( A. x ( ph /\ ps /\ ch ) <-> ( A. x ph /\ A. x ps /\ A. x ch ) ) $= f19.26-3an_0 f19.26-3an_1 wa f19.26-3an_2 wa f19.26-3an_3 wal f19.26-3an_0 f19.26-3an_3 wal f19.26-3an_1 f19.26-3an_3 wal wa f19.26-3an_2 f19.26-3an_3 wal wa f19.26-3an_0 f19.26-3an_1 f19.26-3an_2 w3a f19.26-3an_3 wal f19.26-3an_0 f19.26-3an_3 wal f19.26-3an_1 f19.26-3an_3 wal f19.26-3an_2 f19.26-3an_3 wal w3a f19.26-3an_0 f19.26-3an_1 wa f19.26-3an_2 wa f19.26-3an_3 wal f19.26-3an_0 f19.26-3an_1 wa f19.26-3an_3 wal f19.26-3an_2 f19.26-3an_3 wal wa f19.26-3an_0 f19.26-3an_3 wal f19.26-3an_1 f19.26-3an_3 wal wa f19.26-3an_2 f19.26-3an_3 wal wa f19.26-3an_0 f19.26-3an_1 wa f19.26-3an_2 f19.26-3an_3 19.26 f19.26-3an_0 f19.26-3an_1 wa f19.26-3an_3 wal f19.26-3an_0 f19.26-3an_3 wal f19.26-3an_1 f19.26-3an_3 wal wa f19.26-3an_2 f19.26-3an_3 wal f19.26-3an_0 f19.26-3an_1 f19.26-3an_3 19.26 anbi1i bitri f19.26-3an_0 f19.26-3an_1 f19.26-3an_2 w3a f19.26-3an_0 f19.26-3an_1 wa f19.26-3an_2 wa f19.26-3an_3 f19.26-3an_0 f19.26-3an_1 f19.26-3an_2 df-3an albii f19.26-3an_0 f19.26-3an_3 wal f19.26-3an_1 f19.26-3an_3 wal f19.26-3an_2 f19.26-3an_3 wal df-3an 3bitr4i $.
$}
$( Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.29_0 $f wff ph $.
	f19.29_1 $f wff ps $.
	f19.29_2 $f set x $.
	19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $= f19.29_0 f19.29_2 wal f19.29_1 f19.29_2 wex f19.29_0 f19.29_1 wa f19.29_2 wex f19.29_0 f19.29_2 wal f19.29_1 f19.29_0 f19.29_1 wa wi f19.29_2 wal f19.29_1 f19.29_2 wex f19.29_0 f19.29_1 wa f19.29_2 wex wi f19.29_0 f19.29_1 f19.29_0 f19.29_1 wa wi f19.29_2 f19.29_0 f19.29_1 pm3.2 alimi f19.29_1 f19.29_0 f19.29_1 wa f19.29_2 exim syl imp $.
$}
$( Variation of Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM,
     18-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.29r_0 $f wff ph $.
	f19.29r_1 $f wff ps $.
	f19.29r_2 $f set x $.
	19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $= f19.29r_0 f19.29r_2 wex f19.29r_1 f19.29r_2 wal wa f19.29r_1 f19.29r_0 wa f19.29r_2 wex f19.29r_0 f19.29r_1 wa f19.29r_2 wex f19.29r_1 f19.29r_2 wal f19.29r_0 f19.29r_2 wex f19.29r_1 f19.29r_0 wa f19.29r_2 wex f19.29r_1 f19.29r_0 f19.29r_2 19.29 ancoms f19.29r_0 f19.29r_1 f19.29r_2 exancom sylibr $.
$}
$( Variation of Theorem 19.29 of [Margaris] p. 90 with double
     quantification.  (Contributed by NM, 3-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f19.29r2_0 $f wff ph $.
	f19.29r2_1 $f wff ps $.
	f19.29r2_2 $f set x $.
	f19.29r2_3 $f set y $.
	19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) -> E. x E. y ( ph /\ ps ) ) $= f19.29r2_0 f19.29r2_3 wex f19.29r2_2 wex f19.29r2_1 f19.29r2_3 wal f19.29r2_2 wal wa f19.29r2_0 f19.29r2_3 wex f19.29r2_1 f19.29r2_3 wal wa f19.29r2_2 wex f19.29r2_0 f19.29r2_1 wa f19.29r2_3 wex f19.29r2_2 wex f19.29r2_0 f19.29r2_3 wex f19.29r2_1 f19.29r2_3 wal f19.29r2_2 19.29r f19.29r2_0 f19.29r2_3 wex f19.29r2_1 f19.29r2_3 wal wa f19.29r2_0 f19.29r2_1 wa f19.29r2_3 wex f19.29r2_2 f19.29r2_0 f19.29r2_1 f19.29r2_3 19.29r eximi syl $.
$}
$( Variation of Theorem 19.29 of [Margaris] p. 90 with mixed quantification.
     (Contributed by NM, 11-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f19.29x_0 $f wff ph $.
	f19.29x_1 $f wff ps $.
	f19.29x_2 $f set x $.
	f19.29x_3 $f set y $.
	19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) -> E. x E. y ( ph /\ ps ) ) $= f19.29x_0 f19.29x_3 wal f19.29x_2 wex f19.29x_1 f19.29x_3 wex f19.29x_2 wal wa f19.29x_0 f19.29x_3 wal f19.29x_1 f19.29x_3 wex wa f19.29x_2 wex f19.29x_0 f19.29x_1 wa f19.29x_3 wex f19.29x_2 wex f19.29x_0 f19.29x_3 wal f19.29x_1 f19.29x_3 wex f19.29x_2 19.29r f19.29x_0 f19.29x_3 wal f19.29x_1 f19.29x_3 wex wa f19.29x_0 f19.29x_1 wa f19.29x_3 wex f19.29x_2 f19.29x_0 f19.29x_1 f19.29x_3 19.29 eximi syl $.
$}
$( Theorem 19.35 of [Margaris] p. 90.  This theorem is useful for moving an
     implication (in the form of the right-hand side) into the scope of a
     single existential quantifier.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 27-Jun-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.35_0 $f wff ph $.
	f19.35_1 $f wff ps $.
	f19.35_2 $f set x $.
	19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $= f19.35_0 f19.35_1 wi f19.35_2 wex f19.35_0 f19.35_2 wal f19.35_1 f19.35_2 wex wi f19.35_0 f19.35_1 wi wn f19.35_2 wal f19.35_0 f19.35_2 wal f19.35_1 f19.35_2 wex wn wa f19.35_0 f19.35_1 wi f19.35_2 wex wn f19.35_0 f19.35_2 wal f19.35_1 f19.35_2 wex wi wn f19.35_0 f19.35_1 wn wa f19.35_2 wal f19.35_0 f19.35_2 wal f19.35_1 wn f19.35_2 wal wa f19.35_0 f19.35_1 wi wn f19.35_2 wal f19.35_0 f19.35_2 wal f19.35_1 f19.35_2 wex wn wa f19.35_0 f19.35_1 wn f19.35_2 19.26 f19.35_0 f19.35_1 wn wa f19.35_0 f19.35_1 wi wn f19.35_2 f19.35_0 f19.35_1 annim albii f19.35_1 wn f19.35_2 wal f19.35_1 f19.35_2 wex wn f19.35_0 f19.35_2 wal f19.35_1 f19.35_2 alnex anbi2i 3bitr3i f19.35_0 f19.35_1 wi f19.35_2 alnex f19.35_0 f19.35_2 wal f19.35_1 f19.35_2 wex annim 3bitr3i con4bii $.
$}
$( Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.35i_0 $f wff ph $.
	f19.35i_1 $f wff ps $.
	f19.35i_2 $f set x $.
	e19.35i_0 $e |- E. x ( ph -> ps ) $.
	19.35i $p |- ( A. x ph -> E. x ps ) $= f19.35i_0 f19.35i_1 wi f19.35i_2 wex f19.35i_0 f19.35i_2 wal f19.35i_1 f19.35i_2 wex wi e19.35i_0 f19.35i_0 f19.35i_1 f19.35i_2 19.35 mpbi $.
$}
$( Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.35ri_0 $f wff ph $.
	f19.35ri_1 $f wff ps $.
	f19.35ri_2 $f set x $.
	e19.35ri_0 $e |- ( A. x ph -> E. x ps ) $.
	19.35ri $p |- E. x ( ph -> ps ) $= f19.35ri_0 f19.35ri_1 wi f19.35ri_2 wex f19.35ri_0 f19.35ri_2 wal f19.35ri_1 f19.35ri_2 wex wi e19.35ri_0 f19.35ri_0 f19.35ri_1 f19.35ri_2 19.35 mpbir $.
$}
$( Theorem 19.25 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f19.25_0 $f wff ph $.
	f19.25_1 $f wff ps $.
	f19.25_2 $f set x $.
	f19.25_3 $f set y $.
	19.25 $p |- ( A. y E. x ( ph -> ps ) -> ( E. y A. x ph -> E. y E. x ps ) ) $= f19.25_0 f19.25_1 wi f19.25_2 wex f19.25_3 wal f19.25_0 f19.25_2 wal f19.25_1 f19.25_2 wex wi f19.25_3 wal f19.25_0 f19.25_2 wal f19.25_3 wex f19.25_1 f19.25_2 wex f19.25_3 wex wi f19.25_0 f19.25_1 wi f19.25_2 wex f19.25_0 f19.25_2 wal f19.25_1 f19.25_2 wex wi f19.25_3 f19.25_0 f19.25_1 wi f19.25_2 wex f19.25_0 f19.25_2 wal f19.25_1 f19.25_2 wex wi f19.25_0 f19.25_1 f19.25_2 19.35 biimpi alimi f19.25_0 f19.25_2 wal f19.25_1 f19.25_2 wex f19.25_3 exim syl $.
$}
$( Theorem 19.30 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.30_0 $f wff ph $.
	f19.30_1 $f wff ps $.
	f19.30_2 $f set x $.
	19.30 $p |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) $= f19.30_0 wn f19.30_1 wi f19.30_2 wal f19.30_0 f19.30_2 wal wn f19.30_1 f19.30_2 wex wi f19.30_0 f19.30_1 wo f19.30_2 wal f19.30_0 f19.30_2 wal f19.30_1 f19.30_2 wex wo f19.30_0 f19.30_2 wal wn f19.30_0 wn f19.30_2 wex f19.30_0 wn f19.30_1 wi f19.30_2 wal f19.30_1 f19.30_2 wex f19.30_0 f19.30_2 exnal f19.30_0 wn f19.30_1 f19.30_2 exim syl5bir f19.30_0 f19.30_1 wo f19.30_0 wn f19.30_1 wi f19.30_2 f19.30_0 f19.30_1 df-or albii f19.30_0 f19.30_2 wal f19.30_1 f19.30_2 wex df-or 3imtr4i $.
$}
$( Theorem 19.43 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 27-Jun-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.43_0 $f wff ph $.
	f19.43_1 $f wff ps $.
	f19.43_2 $f set x $.
	19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $= f19.43_0 f19.43_1 wo f19.43_2 wex f19.43_0 f19.43_2 wex wn f19.43_1 f19.43_2 wex wi f19.43_0 f19.43_2 wex f19.43_1 f19.43_2 wex wo f19.43_0 f19.43_1 wo f19.43_2 wex f19.43_0 wn f19.43_1 wi f19.43_2 wex f19.43_0 wn f19.43_2 wal f19.43_1 f19.43_2 wex wi f19.43_0 f19.43_2 wex wn f19.43_1 f19.43_2 wex wi f19.43_0 f19.43_1 wo f19.43_0 wn f19.43_1 wi f19.43_2 f19.43_0 f19.43_1 df-or exbii f19.43_0 wn f19.43_1 f19.43_2 19.35 f19.43_0 wn f19.43_2 wal f19.43_0 f19.43_2 wex wn f19.43_1 f19.43_2 wex f19.43_0 f19.43_2 alnex imbi1i 3bitri f19.43_0 f19.43_2 wex f19.43_1 f19.43_2 wex df-or bitr4i $.
$}
$( Obsolete proof of ~ 19.43 as of 3-May-2016.  Leave this in for the example
     on the mmrecent.html page.  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.43OLD_0 $f wff ph $.
	f19.43OLD_1 $f wff ps $.
	f19.43OLD_2 $f set x $.
	19.43OLD $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $= f19.43OLD_0 f19.43OLD_1 wo wn f19.43OLD_2 wal wn f19.43OLD_0 f19.43OLD_2 wex wn f19.43OLD_1 f19.43OLD_2 wex wn wa wn f19.43OLD_0 f19.43OLD_1 wo f19.43OLD_2 wex f19.43OLD_0 f19.43OLD_2 wex f19.43OLD_1 f19.43OLD_2 wex wo f19.43OLD_0 f19.43OLD_1 wo wn f19.43OLD_2 wal f19.43OLD_0 f19.43OLD_2 wex wn f19.43OLD_1 f19.43OLD_2 wex wn wa f19.43OLD_0 f19.43OLD_1 wo wn f19.43OLD_2 wal f19.43OLD_0 wn f19.43OLD_1 wn wa f19.43OLD_2 wal f19.43OLD_0 wn f19.43OLD_2 wal f19.43OLD_1 wn f19.43OLD_2 wal wa f19.43OLD_0 f19.43OLD_2 wex wn f19.43OLD_1 f19.43OLD_2 wex wn wa f19.43OLD_0 f19.43OLD_1 wo wn f19.43OLD_0 wn f19.43OLD_1 wn wa f19.43OLD_2 f19.43OLD_0 f19.43OLD_1 ioran albii f19.43OLD_0 wn f19.43OLD_1 wn f19.43OLD_2 19.26 f19.43OLD_0 wn f19.43OLD_2 wal f19.43OLD_0 f19.43OLD_2 wex wn f19.43OLD_1 wn f19.43OLD_2 wal f19.43OLD_1 f19.43OLD_2 wex wn f19.43OLD_0 f19.43OLD_2 alnex f19.43OLD_1 f19.43OLD_2 alnex anbi12i 3bitri notbii f19.43OLD_0 f19.43OLD_1 wo f19.43OLD_2 df-ex f19.43OLD_0 f19.43OLD_2 wex f19.43OLD_1 f19.43OLD_2 wex oran 3bitr4i $.
$}
$( Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.33_0 $f wff ph $.
	f19.33_1 $f wff ps $.
	f19.33_2 $f set x $.
	19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $= f19.33_0 f19.33_2 wal f19.33_0 f19.33_1 wo f19.33_2 wal f19.33_1 f19.33_2 wal f19.33_0 f19.33_0 f19.33_1 wo f19.33_2 f19.33_0 f19.33_1 orc alimi f19.33_1 f19.33_0 f19.33_1 wo f19.33_2 f19.33_1 f19.33_0 olc alimi jaoi $.
$}
$( The antecedent provides a condition implying the converse of ~ 19.33 .
     Compare Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM,
     27-Mar-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
     shortened by Wolf Lammen, 5-Jul-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.33b_0 $f wff ph $.
	f19.33b_1 $f wff ps $.
	f19.33b_2 $f set x $.
	19.33b $p |- ( -. ( E. x ph /\ E. x ps ) -> ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $= f19.33b_0 f19.33b_2 wex f19.33b_1 f19.33b_2 wex wa wn f19.33b_0 f19.33b_1 wo f19.33b_2 wal f19.33b_0 f19.33b_2 wal f19.33b_1 f19.33b_2 wal wo f19.33b_0 f19.33b_2 wex f19.33b_1 f19.33b_2 wex wa wn f19.33b_0 f19.33b_2 wex wn f19.33b_1 f19.33b_2 wex wn wo f19.33b_0 f19.33b_1 wo f19.33b_2 wal f19.33b_0 f19.33b_2 wal f19.33b_1 f19.33b_2 wal wo wi f19.33b_0 f19.33b_2 wex f19.33b_1 f19.33b_2 wex ianor f19.33b_0 f19.33b_2 wex wn f19.33b_0 f19.33b_1 wo f19.33b_2 wal f19.33b_0 f19.33b_2 wal f19.33b_1 f19.33b_2 wal wo wi f19.33b_1 f19.33b_2 wex wn f19.33b_0 f19.33b_1 wo f19.33b_2 wal f19.33b_0 f19.33b_2 wex wn f19.33b_1 f19.33b_2 wal f19.33b_0 f19.33b_2 wal f19.33b_1 f19.33b_2 wal wo f19.33b_0 f19.33b_2 wex wn f19.33b_0 wn f19.33b_2 wal f19.33b_0 f19.33b_1 wo f19.33b_2 wal f19.33b_1 f19.33b_2 wal f19.33b_0 f19.33b_2 alnex f19.33b_0 f19.33b_1 wo f19.33b_0 wn f19.33b_1 f19.33b_2 f19.33b_0 f19.33b_1 pm2.53 al2imi syl5bir f19.33b_1 f19.33b_2 wal f19.33b_0 f19.33b_2 wal olc syl6com f19.33b_0 f19.33b_1 wo f19.33b_2 wal f19.33b_1 f19.33b_2 wex wn f19.33b_0 f19.33b_2 wal f19.33b_0 f19.33b_2 wal f19.33b_1 f19.33b_2 wal wo f19.33b_0 f19.33b_1 wo f19.33b_2 wal f19.33b_1 f19.33b_2 wex f19.33b_0 f19.33b_2 wal f19.33b_0 f19.33b_1 wo f19.33b_2 wal f19.33b_0 f19.33b_2 wal f19.33b_1 f19.33b_2 wex f19.33b_0 f19.33b_1 f19.33b_2 19.30 orcomd ord f19.33b_0 f19.33b_2 wal f19.33b_1 f19.33b_2 wal orc syl6com jaoi sylbi f19.33b_0 f19.33b_1 f19.33b_2 19.33 impbid1 $.
$}
$( Theorem 19.40 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.40_0 $f wff ph $.
	f19.40_1 $f wff ps $.
	f19.40_2 $f set x $.
	19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $= f19.40_0 f19.40_1 wa f19.40_2 wex f19.40_0 f19.40_2 wex f19.40_1 f19.40_2 wex f19.40_0 f19.40_1 f19.40_2 exsimpl f19.40_0 f19.40_1 wa f19.40_1 f19.40_2 f19.40_0 f19.40_1 simpr eximi jca $.
$}
$( Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f19.40-2_0 $f wff ph $.
	f19.40-2_1 $f wff ps $.
	f19.40-2_2 $f set x $.
	f19.40-2_3 $f set y $.
	19.40-2 $p |- ( E. x E. y ( ph /\ ps ) -> ( E. x E. y ph /\ E. x E. y ps ) ) $= f19.40-2_0 f19.40-2_1 wa f19.40-2_3 wex f19.40-2_2 wex f19.40-2_0 f19.40-2_3 wex f19.40-2_1 f19.40-2_3 wex wa f19.40-2_2 wex f19.40-2_0 f19.40-2_3 wex f19.40-2_2 wex f19.40-2_1 f19.40-2_3 wex f19.40-2_2 wex wa f19.40-2_0 f19.40-2_1 wa f19.40-2_3 wex f19.40-2_0 f19.40-2_3 wex f19.40-2_1 f19.40-2_3 wex wa f19.40-2_2 f19.40-2_0 f19.40-2_1 f19.40-2_3 19.40 eximi f19.40-2_0 f19.40-2_3 wex f19.40-2_1 f19.40-2_3 wex f19.40-2_2 19.40 syl $.
$}
$( Split a biconditional and distribute quantifier.  (Contributed by NM,
     18-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	falbiim_0 $f wff ph $.
	falbiim_1 $f wff ps $.
	falbiim_2 $f set x $.
	albiim $p |- ( A. x ( ph <-> ps ) <-> ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $= falbiim_0 falbiim_1 wb falbiim_2 wal falbiim_0 falbiim_1 wi falbiim_1 falbiim_0 wi wa falbiim_2 wal falbiim_0 falbiim_1 wi falbiim_2 wal falbiim_1 falbiim_0 wi falbiim_2 wal wa falbiim_0 falbiim_1 wb falbiim_0 falbiim_1 wi falbiim_1 falbiim_0 wi wa falbiim_2 falbiim_0 falbiim_1 dfbi2 albii falbiim_0 falbiim_1 wi falbiim_1 falbiim_0 wi falbiim_2 19.26 bitri $.
$}
$( Split a biconditional and distribute 2 quantifiers.  (Contributed by NM,
     3-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	f2albiim_0 $f wff ph $.
	f2albiim_1 $f wff ps $.
	f2albiim_2 $f set x $.
	f2albiim_3 $f set y $.
	2albiim $p |- ( A. x A. y ( ph <-> ps ) <-> ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) ) $= f2albiim_0 f2albiim_1 wb f2albiim_3 wal f2albiim_2 wal f2albiim_0 f2albiim_1 wi f2albiim_3 wal f2albiim_1 f2albiim_0 wi f2albiim_3 wal wa f2albiim_2 wal f2albiim_0 f2albiim_1 wi f2albiim_3 wal f2albiim_2 wal f2albiim_1 f2albiim_0 wi f2albiim_3 wal f2albiim_2 wal wa f2albiim_0 f2albiim_1 wb f2albiim_3 wal f2albiim_0 f2albiim_1 wi f2albiim_3 wal f2albiim_1 f2albiim_0 wi f2albiim_3 wal wa f2albiim_2 f2albiim_0 f2albiim_1 f2albiim_3 albiim albii f2albiim_0 f2albiim_1 wi f2albiim_3 wal f2albiim_1 f2albiim_0 wi f2albiim_3 wal f2albiim_2 19.26 bitri $.
$}
$( Add/remove a conjunct in the scope of an existential quantifier.
     (Contributed by Raph Levien, 3-Jul-2006.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fexintrbi_0 $f wff ph $.
	fexintrbi_1 $f wff ps $.
	fexintrbi_2 $f set x $.
	exintrbi $p |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) ) $= fexintrbi_0 fexintrbi_1 wi fexintrbi_2 wal fexintrbi_0 fexintrbi_0 fexintrbi_1 wa wb fexintrbi_2 wal fexintrbi_0 fexintrbi_2 wex fexintrbi_0 fexintrbi_1 wa fexintrbi_2 wex wb fexintrbi_0 fexintrbi_1 wi fexintrbi_0 fexintrbi_0 fexintrbi_1 wa wb fexintrbi_2 fexintrbi_0 fexintrbi_1 pm4.71 albii fexintrbi_0 fexintrbi_0 fexintrbi_1 wa fexintrbi_2 exbi sylbi $.
$}
$( Introduce a conjunct in the scope of an existential quantifier.
     (Contributed by NM, 11-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fexintr_0 $f wff ph $.
	fexintr_1 $f wff ps $.
	fexintr_2 $f set x $.
	exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $= fexintr_0 fexintr_1 wi fexintr_2 wal fexintr_0 fexintr_2 wex fexintr_0 fexintr_1 wa fexintr_2 wex fexintr_0 fexintr_1 fexintr_2 exintrbi biimpd $.
$}
$( Theorem *10.3 in [WhiteheadRussell] p. 150.  (Contributed by Andrew
     Salmon, 8-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	falsyl_0 $f wff ph $.
	falsyl_1 $f wff ps $.
	falsyl_2 $f wff ch $.
	falsyl_3 $f set x $.
	alsyl $p |- ( ( A. x ( ph -> ps ) /\ A. x ( ps -> ch ) ) -> A. x ( ph -> ch ) ) $= falsyl_0 falsyl_1 wi falsyl_1 falsyl_2 wi falsyl_0 falsyl_2 wi falsyl_3 falsyl_0 falsyl_1 falsyl_2 pm3.33 alanimi $.
$}

