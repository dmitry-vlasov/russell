$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Negated_equality_and_membership.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Restricted quantification

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Extend wff notation to include restricted universal quantification. $)
${
	fwral_0 $f wff ph $.
	fwral_1 $f set x $.
	fwral_2 $f class A $.
	wral $a wff A. x e. A ph $.
$}
$( Extend wff notation to include restricted existential quantification. $)
${
	fwrex_0 $f wff ph $.
	fwrex_1 $f set x $.
	fwrex_2 $f class A $.
	wrex $a wff E. x e. A ph $.
$}
$( Extend wff notation to include restricted existential uniqueness. $)
${
	fwreu_0 $f wff ph $.
	fwreu_1 $f set x $.
	fwreu_2 $f class A $.
	wreu $a wff E! x e. A ph $.
$}
$( Extend wff notation to include restricted "at most one." $)
${
	fwrmo_0 $f wff ph $.
	fwrmo_1 $f set x $.
	fwrmo_2 $f class A $.
	wrmo $a wff E* x e. A ph $.
$}
$( Extend class notation to include the restricted class abstraction (class
     builder). $)
${
	fcrab_0 $f wff ph $.
	fcrab_1 $f set x $.
	fcrab_2 $f class A $.
	crab $a class { x e. A | ph } $.
$}
$( Define restricted universal quantification.  Special case of Definition
     4.15(3) of [TakeutiZaring] p. 22.  (Contributed by NM, 19-Aug-1993.) $)
${
	fdf-ral_0 $f wff ph $.
	fdf-ral_1 $f set x $.
	fdf-ral_2 $f class A $.
	df-ral $a |- ( A. x e. A ph <-> A. x ( x e. A -> ph ) ) $.
$}
$( Define restricted existential quantification.  Special case of Definition
     4.15(4) of [TakeutiZaring] p. 22.  (Contributed by NM, 30-Aug-1993.) $)
${
	fdf-rex_0 $f wff ph $.
	fdf-rex_1 $f set x $.
	fdf-rex_2 $f class A $.
	df-rex $a |- ( E. x e. A ph <-> E. x ( x e. A /\ ph ) ) $.
$}
$( Define restricted existential uniqueness.  (Contributed by NM,
     22-Nov-1994.) $)
${
	fdf-reu_0 $f wff ph $.
	fdf-reu_1 $f set x $.
	fdf-reu_2 $f class A $.
	df-reu $a |- ( E! x e. A ph <-> E! x ( x e. A /\ ph ) ) $.
$}
$( Define restricted "at most one".  (Contributed by NM, 16-Jun-2017.) $)
${
	fdf-rmo_0 $f wff ph $.
	fdf-rmo_1 $f set x $.
	fdf-rmo_2 $f class A $.
	df-rmo $a |- ( E* x e. A ph <-> E* x ( x e. A /\ ph ) ) $.
$}
$( Define a restricted class abstraction (class builder), which is the class
     of all ` x ` in ` A ` such that ` ph ` is true.  Definition of
     [TakeutiZaring] p. 20.  (Contributed by NM, 22-Nov-1994.) $)
${
	fdf-rab_0 $f wff ph $.
	fdf-rab_1 $f set x $.
	fdf-rab_2 $f class A $.
	df-rab $a |- { x e. A | ph } = { x | ( x e. A /\ ph ) } $.
$}
$( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)
${
	fralnex_0 $f wff ph $.
	fralnex_1 $f set x $.
	fralnex_2 $f class A $.
	ralnex $p |- ( A. x e. A -. ph <-> -. E. x e. A ph ) $= fralnex_0 wn fralnex_1 fralnex_2 wral fralnex_1 cv fralnex_2 wcel fralnex_0 wn wi fralnex_1 wal fralnex_0 fralnex_1 fralnex_2 wrex wn fralnex_0 wn fralnex_1 fralnex_2 df-ral fralnex_1 cv fralnex_2 wcel fralnex_0 wn wi fralnex_1 wal fralnex_1 cv fralnex_2 wcel fralnex_0 wa fralnex_1 wex fralnex_0 fralnex_1 fralnex_2 wrex fralnex_1 cv fralnex_2 wcel fralnex_0 fralnex_1 alinexa fralnex_0 fralnex_1 fralnex_2 df-rex xchbinxr bitri $.
$}
$( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)
${
	frexnal_0 $f wff ph $.
	frexnal_1 $f set x $.
	frexnal_2 $f class A $.
	rexnal $p |- ( E. x e. A -. ph <-> -. A. x e. A ph ) $= frexnal_0 wn frexnal_1 frexnal_2 wrex frexnal_1 cv frexnal_2 wcel frexnal_0 wn wa frexnal_1 wex frexnal_0 frexnal_1 frexnal_2 wral wn frexnal_0 wn frexnal_1 frexnal_2 df-rex frexnal_1 cv frexnal_2 wcel frexnal_0 wn wa frexnal_1 wex frexnal_1 cv frexnal_2 wcel frexnal_0 wi frexnal_1 wal frexnal_0 frexnal_1 frexnal_2 wral frexnal_1 cv frexnal_2 wcel frexnal_0 frexnal_1 exanali frexnal_0 frexnal_1 frexnal_2 df-ral xchbinxr bitri $.
$}
$( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)
${
	fdfral2_0 $f wff ph $.
	fdfral2_1 $f set x $.
	fdfral2_2 $f class A $.
	dfral2 $p |- ( A. x e. A ph <-> -. E. x e. A -. ph ) $= fdfral2_0 wn fdfral2_1 fdfral2_2 wrex fdfral2_0 fdfral2_1 fdfral2_2 wral fdfral2_0 fdfral2_1 fdfral2_2 rexnal con2bii $.
$}
$( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)
${
	fdfrex2_0 $f wff ph $.
	fdfrex2_1 $f set x $.
	fdfrex2_2 $f class A $.
	dfrex2 $p |- ( E. x e. A ph <-> -. A. x e. A -. ph ) $= fdfrex2_0 wn fdfrex2_1 fdfrex2_2 wral fdfrex2_0 fdfrex2_1 fdfrex2_2 wrex fdfrex2_0 fdfrex2_1 fdfrex2_2 ralnex con2bii $.
$}
$( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 6-Oct-2003.) $)
${
	fralbida_0 $f wff ph $.
	fralbida_1 $f wff ps $.
	fralbida_2 $f wff ch $.
	fralbida_3 $f set x $.
	fralbida_4 $f class A $.
	eralbida_0 $e |- F/ x ph $.
	eralbida_1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	ralbida $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $= fralbida_0 fralbida_3 cv fralbida_4 wcel fralbida_1 wi fralbida_3 wal fralbida_3 cv fralbida_4 wcel fralbida_2 wi fralbida_3 wal fralbida_1 fralbida_3 fralbida_4 wral fralbida_2 fralbida_3 fralbida_4 wral fralbida_0 fralbida_3 cv fralbida_4 wcel fralbida_1 wi fralbida_3 cv fralbida_4 wcel fralbida_2 wi fralbida_3 eralbida_0 fralbida_0 fralbida_3 cv fralbida_4 wcel fralbida_1 fralbida_2 eralbida_1 pm5.74da albid fralbida_1 fralbida_3 fralbida_4 df-ral fralbida_2 fralbida_3 fralbida_4 df-ral 3bitr4g $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 6-Oct-2003.) $)
${
	frexbida_0 $f wff ph $.
	frexbida_1 $f wff ps $.
	frexbida_2 $f wff ch $.
	frexbida_3 $f set x $.
	frexbida_4 $f class A $.
	erexbida_0 $e |- F/ x ph $.
	erexbida_1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	rexbida $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $= frexbida_0 frexbida_3 cv frexbida_4 wcel frexbida_1 wa frexbida_3 wex frexbida_3 cv frexbida_4 wcel frexbida_2 wa frexbida_3 wex frexbida_1 frexbida_3 frexbida_4 wrex frexbida_2 frexbida_3 frexbida_4 wrex frexbida_0 frexbida_3 cv frexbida_4 wcel frexbida_1 wa frexbida_3 cv frexbida_4 wcel frexbida_2 wa frexbida_3 erexbida_0 frexbida_0 frexbida_3 cv frexbida_4 wcel frexbida_1 frexbida_2 erexbida_1 pm5.32da exbid frexbida_1 frexbida_3 frexbida_4 df-rex frexbida_2 frexbida_3 frexbida_4 df-rex 3bitr4g $.
$}
$( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 4-Mar-1997.) $)
${
	$d x ph $.
	fralbidva_0 $f wff ph $.
	fralbidva_1 $f wff ps $.
	fralbidva_2 $f wff ch $.
	fralbidva_3 $f set x $.
	fralbidva_4 $f class A $.
	eralbidva_0 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	ralbidva $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $= fralbidva_0 fralbidva_1 fralbidva_2 fralbidva_3 fralbidva_4 fralbidva_0 fralbidva_3 nfv eralbidva_0 ralbida $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 9-Mar-1997.) $)
${
	$d x ph $.
	frexbidva_0 $f wff ph $.
	frexbidva_1 $f wff ps $.
	frexbidva_2 $f wff ch $.
	frexbidva_3 $f set x $.
	frexbidva_4 $f class A $.
	erexbidva_0 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	rexbidva $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $= frexbidva_0 frexbidva_1 frexbidva_2 frexbidva_3 frexbidva_4 frexbidva_0 frexbidva_3 nfv erexbidva_0 rexbida $.
$}
$( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 27-Jun-1998.) $)
${
	fralbid_0 $f wff ph $.
	fralbid_1 $f wff ps $.
	fralbid_2 $f wff ch $.
	fralbid_3 $f set x $.
	fralbid_4 $f class A $.
	eralbid_0 $e |- F/ x ph $.
	eralbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	ralbid $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $= fralbid_0 fralbid_1 fralbid_2 fralbid_3 fralbid_4 eralbid_0 fralbid_0 fralbid_1 fralbid_2 wb fralbid_3 cv fralbid_4 wcel eralbid_1 adantr ralbida $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 27-Jun-1998.) $)
${
	frexbid_0 $f wff ph $.
	frexbid_1 $f wff ps $.
	frexbid_2 $f wff ch $.
	frexbid_3 $f set x $.
	frexbid_4 $f class A $.
	erexbid_0 $e |- F/ x ph $.
	erexbid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	rexbid $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $= frexbid_0 frexbid_1 frexbid_2 frexbid_3 frexbid_4 erexbid_0 frexbid_0 frexbid_1 frexbid_2 wb frexbid_3 cv frexbid_4 wcel erexbid_1 adantr rexbida $.
$}
$( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 20-Nov-1994.) $)
${
	$d x ph $.
	fralbidv_0 $f wff ph $.
	fralbidv_1 $f wff ps $.
	fralbidv_2 $f wff ch $.
	fralbidv_3 $f set x $.
	fralbidv_4 $f class A $.
	eralbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ralbidv $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $= fralbidv_0 fralbidv_1 fralbidv_2 fralbidv_3 fralbidv_4 fralbidv_0 fralbidv_3 nfv eralbidv_0 ralbid $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 20-Nov-1994.) $)
${
	$d x ph $.
	frexbidv_0 $f wff ph $.
	frexbidv_1 $f wff ps $.
	frexbidv_2 $f wff ch $.
	frexbidv_3 $f set x $.
	frexbidv_4 $f class A $.
	erexbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	rexbidv $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $= frexbidv_0 frexbidv_1 frexbidv_2 frexbidv_3 frexbidv_4 frexbidv_0 frexbidv_3 nfv erexbidv_0 rexbid $.
$}
$( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 6-Apr-1997.) $)
${
	$d x ph $.
	fralbidv2_0 $f wff ph $.
	fralbidv2_1 $f wff ps $.
	fralbidv2_2 $f wff ch $.
	fralbidv2_3 $f set x $.
	fralbidv2_4 $f class A $.
	fralbidv2_5 $f class B $.
	eralbidv2_0 $e |- ( ph -> ( ( x e. A -> ps ) <-> ( x e. B -> ch ) ) ) $.
	ralbidv2 $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $= fralbidv2_0 fralbidv2_3 cv fralbidv2_4 wcel fralbidv2_1 wi fralbidv2_3 wal fralbidv2_3 cv fralbidv2_5 wcel fralbidv2_2 wi fralbidv2_3 wal fralbidv2_1 fralbidv2_3 fralbidv2_4 wral fralbidv2_2 fralbidv2_3 fralbidv2_5 wral fralbidv2_0 fralbidv2_3 cv fralbidv2_4 wcel fralbidv2_1 wi fralbidv2_3 cv fralbidv2_5 wcel fralbidv2_2 wi fralbidv2_3 eralbidv2_0 albidv fralbidv2_1 fralbidv2_3 fralbidv2_4 df-ral fralbidv2_2 fralbidv2_3 fralbidv2_5 df-ral 3bitr4g $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 22-May-1999.) $)
${
	$d x ph $.
	frexbidv2_0 $f wff ph $.
	frexbidv2_1 $f wff ps $.
	frexbidv2_2 $f wff ch $.
	frexbidv2_3 $f set x $.
	frexbidv2_4 $f class A $.
	frexbidv2_5 $f class B $.
	erexbidv2_0 $e |- ( ph -> ( ( x e. A /\ ps ) <-> ( x e. B /\ ch ) ) ) $.
	rexbidv2 $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $= frexbidv2_0 frexbidv2_3 cv frexbidv2_4 wcel frexbidv2_1 wa frexbidv2_3 wex frexbidv2_3 cv frexbidv2_5 wcel frexbidv2_2 wa frexbidv2_3 wex frexbidv2_1 frexbidv2_3 frexbidv2_4 wrex frexbidv2_2 frexbidv2_3 frexbidv2_5 wrex frexbidv2_0 frexbidv2_3 cv frexbidv2_4 wcel frexbidv2_1 wa frexbidv2_3 cv frexbidv2_5 wcel frexbidv2_2 wa frexbidv2_3 erexbidv2_0 exbidv frexbidv2_1 frexbidv2_3 frexbidv2_4 df-rex frexbidv2_2 frexbidv2_3 frexbidv2_5 df-rex 3bitr4g $.
$}
$( Inference adding restricted universal quantifier to both sides of an
       equivalence.  (Contributed by NM, 23-Nov-1994.)  (Revised by Mario
       Carneiro, 17-Oct-2016.) $)
${
	fralbii_0 $f wff ph $.
	fralbii_1 $f wff ps $.
	fralbii_2 $f set x $.
	fralbii_3 $f class A $.
	eralbii_0 $e |- ( ph <-> ps ) $.
	ralbii $p |- ( A. x e. A ph <-> A. x e. A ps ) $= fralbii_0 fralbii_2 fralbii_3 wral fralbii_1 fralbii_2 fralbii_3 wral wb wtru fralbii_0 fralbii_1 fralbii_2 fralbii_3 fralbii_0 fralbii_1 wb wtru eralbii_0 a1i ralbidv trud $.
$}
$( Inference adding restricted existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 23-Nov-1994.)  (Revised by Mario
       Carneiro, 17-Oct-2016.) $)
${
	frexbii_0 $f wff ph $.
	frexbii_1 $f wff ps $.
	frexbii_2 $f set x $.
	frexbii_3 $f class A $.
	erexbii_0 $e |- ( ph <-> ps ) $.
	rexbii $p |- ( E. x e. A ph <-> E. x e. A ps ) $= frexbii_0 frexbii_2 frexbii_3 wrex frexbii_1 frexbii_2 frexbii_3 wrex wb wtru frexbii_0 frexbii_1 frexbii_2 frexbii_3 frexbii_0 frexbii_1 wb wtru erexbii_0 a1i rexbidv trud $.
$}
$( Inference adding two restricted universal quantifiers to both sides of
       an equivalence.  (Contributed by NM, 1-Aug-2004.) $)
${
	f2ralbii_0 $f wff ph $.
	f2ralbii_1 $f wff ps $.
	f2ralbii_2 $f set x $.
	f2ralbii_3 $f set y $.
	f2ralbii_4 $f class A $.
	f2ralbii_5 $f class B $.
	e2ralbii_0 $e |- ( ph <-> ps ) $.
	2ralbii $p |- ( A. x e. A A. y e. B ph <-> A. x e. A A. y e. B ps ) $= f2ralbii_0 f2ralbii_3 f2ralbii_5 wral f2ralbii_1 f2ralbii_3 f2ralbii_5 wral f2ralbii_2 f2ralbii_4 f2ralbii_0 f2ralbii_1 f2ralbii_3 f2ralbii_5 e2ralbii_0 ralbii ralbii $.
$}
$( Inference adding two restricted existential quantifiers to both sides of
       an equivalence.  (Contributed by NM, 11-Nov-1995.) $)
${
	f2rexbii_0 $f wff ph $.
	f2rexbii_1 $f wff ps $.
	f2rexbii_2 $f set x $.
	f2rexbii_3 $f set y $.
	f2rexbii_4 $f class A $.
	f2rexbii_5 $f class B $.
	e2rexbii_0 $e |- ( ph <-> ps ) $.
	2rexbii $p |- ( E. x e. A E. y e. B ph <-> E. x e. A E. y e. B ps ) $= f2rexbii_0 f2rexbii_3 f2rexbii_5 wrex f2rexbii_1 f2rexbii_3 f2rexbii_5 wrex f2rexbii_2 f2rexbii_4 f2rexbii_0 f2rexbii_1 f2rexbii_3 f2rexbii_5 e2rexbii_0 rexbii rexbii $.
$}
$( Inference adding different restricted universal quantifiers to each side
       of an equivalence.  (Contributed by NM, 15-Aug-2005.) $)
${
	fralbii2_0 $f wff ph $.
	fralbii2_1 $f wff ps $.
	fralbii2_2 $f set x $.
	fralbii2_3 $f class A $.
	fralbii2_4 $f class B $.
	eralbii2_0 $e |- ( ( x e. A -> ph ) <-> ( x e. B -> ps ) ) $.
	ralbii2 $p |- ( A. x e. A ph <-> A. x e. B ps ) $= fralbii2_2 cv fralbii2_3 wcel fralbii2_0 wi fralbii2_2 wal fralbii2_2 cv fralbii2_4 wcel fralbii2_1 wi fralbii2_2 wal fralbii2_0 fralbii2_2 fralbii2_3 wral fralbii2_1 fralbii2_2 fralbii2_4 wral fralbii2_2 cv fralbii2_3 wcel fralbii2_0 wi fralbii2_2 cv fralbii2_4 wcel fralbii2_1 wi fralbii2_2 eralbii2_0 albii fralbii2_0 fralbii2_2 fralbii2_3 df-ral fralbii2_1 fralbii2_2 fralbii2_4 df-ral 3bitr4i $.
$}
$( Inference adding different restricted existential quantifiers to each
       side of an equivalence.  (Contributed by NM, 4-Feb-2004.) $)
${
	frexbii2_0 $f wff ph $.
	frexbii2_1 $f wff ps $.
	frexbii2_2 $f set x $.
	frexbii2_3 $f class A $.
	frexbii2_4 $f class B $.
	erexbii2_0 $e |- ( ( x e. A /\ ph ) <-> ( x e. B /\ ps ) ) $.
	rexbii2 $p |- ( E. x e. A ph <-> E. x e. B ps ) $= frexbii2_2 cv frexbii2_3 wcel frexbii2_0 wa frexbii2_2 wex frexbii2_2 cv frexbii2_4 wcel frexbii2_1 wa frexbii2_2 wex frexbii2_0 frexbii2_2 frexbii2_3 wrex frexbii2_1 frexbii2_2 frexbii2_4 wrex frexbii2_2 cv frexbii2_3 wcel frexbii2_0 wa frexbii2_2 cv frexbii2_4 wcel frexbii2_1 wa frexbii2_2 erexbii2_0 exbii frexbii2_0 frexbii2_2 frexbii2_3 df-rex frexbii2_1 frexbii2_2 frexbii2_4 df-rex 3bitr4i $.
$}
$( Equality deduction for restricted universal quantifier, changing both
       formula and quantifier domain.  Inference form.  (Contributed by David
       Moews, 1-May-2017.) $)
${
	fraleqbii_0 $f wff ps $.
	fraleqbii_1 $f wff ch $.
	fraleqbii_2 $f set x $.
	fraleqbii_3 $f class A $.
	fraleqbii_4 $f class B $.
	eraleqbii_0 $e |- A = B $.
	eraleqbii_1 $e |- ( ps <-> ch ) $.
	raleqbii $p |- ( A. x e. A ps <-> A. x e. B ch ) $= fraleqbii_0 fraleqbii_1 fraleqbii_2 fraleqbii_3 fraleqbii_4 fraleqbii_2 cv fraleqbii_3 wcel fraleqbii_2 cv fraleqbii_4 wcel fraleqbii_0 fraleqbii_1 fraleqbii_3 fraleqbii_4 fraleqbii_2 cv eraleqbii_0 eleq2i eraleqbii_1 imbi12i ralbii2 $.
$}
$( Equality deduction for restricted existential quantifier, changing both
       formula and quantifier domain.  Inference form.  (Contributed by David
       Moews, 1-May-2017.) $)
${
	frexeqbii_0 $f wff ps $.
	frexeqbii_1 $f wff ch $.
	frexeqbii_2 $f set x $.
	frexeqbii_3 $f class A $.
	frexeqbii_4 $f class B $.
	erexeqbii_0 $e |- A = B $.
	erexeqbii_1 $e |- ( ps <-> ch ) $.
	rexeqbii $p |- ( E. x e. A ps <-> E. x e. B ch ) $= frexeqbii_0 frexeqbii_1 frexeqbii_2 frexeqbii_3 frexeqbii_4 frexeqbii_2 cv frexeqbii_3 wcel frexeqbii_2 cv frexeqbii_4 wcel frexeqbii_0 frexeqbii_1 frexeqbii_3 frexeqbii_4 frexeqbii_2 cv erexeqbii_0 eleq2i erexeqbii_1 anbi12i rexbii2 $.
$}
$( Inference adding restricted universal quantifier to both sides of an
       equivalence.  (Contributed by NM, 26-Nov-2000.) $)
${
	fralbiia_0 $f wff ph $.
	fralbiia_1 $f wff ps $.
	fralbiia_2 $f set x $.
	fralbiia_3 $f class A $.
	eralbiia_0 $e |- ( x e. A -> ( ph <-> ps ) ) $.
	ralbiia $p |- ( A. x e. A ph <-> A. x e. A ps ) $= fralbiia_0 fralbiia_1 fralbiia_2 fralbiia_3 fralbiia_3 fralbiia_2 cv fralbiia_3 wcel fralbiia_0 fralbiia_1 eralbiia_0 pm5.74i ralbii2 $.
$}
$( Inference adding restricted existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 26-Oct-1999.) $)
${
	frexbiia_0 $f wff ph $.
	frexbiia_1 $f wff ps $.
	frexbiia_2 $f set x $.
	frexbiia_3 $f class A $.
	erexbiia_0 $e |- ( x e. A -> ( ph <-> ps ) ) $.
	rexbiia $p |- ( E. x e. A ph <-> E. x e. A ps ) $= frexbiia_0 frexbiia_1 frexbiia_2 frexbiia_3 frexbiia_3 frexbiia_2 cv frexbiia_3 wcel frexbiia_0 frexbiia_1 erexbiia_0 pm5.32i rexbii2 $.
$}
$( Inference adding two restricted existential quantifiers to both sides of
       an equivalence.  (Contributed by NM, 1-Aug-2004.) $)
${
	$d x y $.
	$d y A $.
	f2rexbiia_0 $f wff ph $.
	f2rexbiia_1 $f wff ps $.
	f2rexbiia_2 $f set x $.
	f2rexbiia_3 $f set y $.
	f2rexbiia_4 $f class A $.
	f2rexbiia_5 $f class B $.
	e2rexbiia_0 $e |- ( ( x e. A /\ y e. B ) -> ( ph <-> ps ) ) $.
	2rexbiia $p |- ( E. x e. A E. y e. B ph <-> E. x e. A E. y e. B ps ) $= f2rexbiia_0 f2rexbiia_3 f2rexbiia_5 wrex f2rexbiia_1 f2rexbiia_3 f2rexbiia_5 wrex f2rexbiia_2 f2rexbiia_4 f2rexbiia_2 cv f2rexbiia_4 wcel f2rexbiia_0 f2rexbiia_1 f2rexbiia_3 f2rexbiia_5 e2rexbiia_0 rexbidva rexbiia $.
$}
$( Double restricted universal quantification.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)
${
	$d x y $.
	fr2alf_0 $f wff ph $.
	fr2alf_1 $f set x $.
	fr2alf_2 $f set y $.
	fr2alf_3 $f class A $.
	fr2alf_4 $f class B $.
	er2alf_0 $e |- F/_ y A $.
	r2alf $p |- ( A. x e. A A. y e. B ph <-> A. x A. y ( ( x e. A /\ y e. B ) -> ph ) ) $= fr2alf_0 fr2alf_2 fr2alf_4 wral fr2alf_1 fr2alf_3 wral fr2alf_1 cv fr2alf_3 wcel fr2alf_0 fr2alf_2 fr2alf_4 wral wi fr2alf_1 wal fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel wa fr2alf_0 wi fr2alf_2 wal fr2alf_1 wal fr2alf_0 fr2alf_2 fr2alf_4 wral fr2alf_1 fr2alf_3 df-ral fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel wa fr2alf_0 wi fr2alf_2 wal fr2alf_1 cv fr2alf_3 wcel fr2alf_0 fr2alf_2 fr2alf_4 wral wi fr2alf_1 fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel fr2alf_0 wi wi fr2alf_2 wal fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel fr2alf_0 wi fr2alf_2 wal wi fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel wa fr2alf_0 wi fr2alf_2 wal fr2alf_1 cv fr2alf_3 wcel fr2alf_0 fr2alf_2 fr2alf_4 wral wi fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel fr2alf_0 wi fr2alf_2 fr2alf_2 fr2alf_1 fr2alf_3 er2alf_0 nfcri 19.21 fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel wa fr2alf_0 wi fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel fr2alf_0 wi wi fr2alf_2 fr2alf_1 cv fr2alf_3 wcel fr2alf_2 cv fr2alf_4 wcel fr2alf_0 impexp albii fr2alf_0 fr2alf_2 fr2alf_4 wral fr2alf_2 cv fr2alf_4 wcel fr2alf_0 wi fr2alf_2 wal fr2alf_1 cv fr2alf_3 wcel fr2alf_0 fr2alf_2 fr2alf_4 df-ral imbi2i 3bitr4i albii bitr4i $.
$}
$( Double restricted existential quantification.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)
${
	$d x y $.
	fr2exf_0 $f wff ph $.
	fr2exf_1 $f set x $.
	fr2exf_2 $f set y $.
	fr2exf_3 $f class A $.
	fr2exf_4 $f class B $.
	er2exf_0 $e |- F/_ y A $.
	r2exf $p |- ( E. x e. A E. y e. B ph <-> E. x E. y ( ( x e. A /\ y e. B ) /\ ph ) ) $= fr2exf_0 fr2exf_2 fr2exf_4 wrex fr2exf_1 fr2exf_3 wrex fr2exf_1 cv fr2exf_3 wcel fr2exf_0 fr2exf_2 fr2exf_4 wrex wa fr2exf_1 wex fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel wa fr2exf_0 wa fr2exf_2 wex fr2exf_1 wex fr2exf_0 fr2exf_2 fr2exf_4 wrex fr2exf_1 fr2exf_3 df-rex fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel wa fr2exf_0 wa fr2exf_2 wex fr2exf_1 cv fr2exf_3 wcel fr2exf_0 fr2exf_2 fr2exf_4 wrex wa fr2exf_1 fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel fr2exf_0 wa wa fr2exf_2 wex fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel fr2exf_0 wa fr2exf_2 wex wa fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel wa fr2exf_0 wa fr2exf_2 wex fr2exf_1 cv fr2exf_3 wcel fr2exf_0 fr2exf_2 fr2exf_4 wrex wa fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel fr2exf_0 wa fr2exf_2 fr2exf_2 fr2exf_1 fr2exf_3 er2exf_0 nfcri 19.42 fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel wa fr2exf_0 wa fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel fr2exf_0 wa wa fr2exf_2 fr2exf_1 cv fr2exf_3 wcel fr2exf_2 cv fr2exf_4 wcel fr2exf_0 anass exbii fr2exf_0 fr2exf_2 fr2exf_4 wrex fr2exf_2 cv fr2exf_4 wcel fr2exf_0 wa fr2exf_2 wex fr2exf_1 cv fr2exf_3 wcel fr2exf_0 fr2exf_2 fr2exf_4 df-rex anbi2i 3bitr4i exbii bitr4i $.
$}
$( Double restricted universal quantification.  (Contributed by NM,
       19-Nov-1995.) $)
${
	$d x y $.
	$d y A $.
	fr2al_0 $f wff ph $.
	fr2al_1 $f set x $.
	fr2al_2 $f set y $.
	fr2al_3 $f class A $.
	fr2al_4 $f class B $.
	r2al $p |- ( A. x e. A A. y e. B ph <-> A. x A. y ( ( x e. A /\ y e. B ) -> ph ) ) $= fr2al_0 fr2al_1 fr2al_2 fr2al_3 fr2al_4 fr2al_2 fr2al_3 nfcv r2alf $.
$}
$( Double restricted existential quantification.  (Contributed by NM,
       11-Nov-1995.) $)
${
	$d x y $.
	$d y A $.
	fr2ex_0 $f wff ph $.
	fr2ex_1 $f set x $.
	fr2ex_2 $f set y $.
	fr2ex_3 $f class A $.
	fr2ex_4 $f class B $.
	r2ex $p |- ( E. x e. A E. y e. B ph <-> E. x E. y ( ( x e. A /\ y e. B ) /\ ph ) ) $= fr2ex_0 fr2ex_1 fr2ex_2 fr2ex_3 fr2ex_4 fr2ex_2 fr2ex_3 nfcv r2exf $.
$}
$( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 24-Feb-2004.) $)
${
	$d x y $.
	$d y A $.
	f2ralbida_0 $f wff ph $.
	f2ralbida_1 $f wff ps $.
	f2ralbida_2 $f wff ch $.
	f2ralbida_3 $f set x $.
	f2ralbida_4 $f set y $.
	f2ralbida_5 $f class A $.
	f2ralbida_6 $f class B $.
	e2ralbida_0 $e |- F/ x ph $.
	e2ralbida_1 $e |- F/ y ph $.
	e2ralbida_2 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) ) $.
	2ralbida $p |- ( ph -> ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $= f2ralbida_0 f2ralbida_1 f2ralbida_4 f2ralbida_6 wral f2ralbida_2 f2ralbida_4 f2ralbida_6 wral f2ralbida_3 f2ralbida_5 e2ralbida_0 f2ralbida_0 f2ralbida_3 cv f2ralbida_5 wcel wa f2ralbida_1 f2ralbida_2 f2ralbida_4 f2ralbida_6 f2ralbida_0 f2ralbida_3 cv f2ralbida_5 wcel f2ralbida_4 e2ralbida_1 f2ralbida_3 cv f2ralbida_5 wcel f2ralbida_4 nfv nfan f2ralbida_0 f2ralbida_3 cv f2ralbida_5 wcel f2ralbida_4 cv f2ralbida_6 wcel f2ralbida_1 f2ralbida_2 wb e2ralbida_2 anassrs ralbida ralbida $.
$}
$( Formula-building rule for restricted universal quantifiers (deduction
       rule).  (Contributed by NM, 4-Mar-1997.) $)
${
	$d x y ph $.
	$d y A $.
	f2ralbidva_0 $f wff ph $.
	f2ralbidva_1 $f wff ps $.
	f2ralbidva_2 $f wff ch $.
	f2ralbidva_3 $f set x $.
	f2ralbidva_4 $f set y $.
	f2ralbidva_5 $f class A $.
	f2ralbidva_6 $f class B $.
	e2ralbidva_0 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) ) $.
	2ralbidva $p |- ( ph -> ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $= f2ralbidva_0 f2ralbidva_1 f2ralbidva_2 f2ralbidva_3 f2ralbidva_4 f2ralbidva_5 f2ralbidva_6 f2ralbidva_0 f2ralbidva_3 nfv f2ralbidva_0 f2ralbidva_4 nfv e2ralbidva_0 2ralbida $.
$}
$( Formula-building rule for restricted existential quantifiers (deduction
       rule).  (Contributed by NM, 15-Dec-2004.) $)
${
	$d x y ph $.
	$d y A $.
	f2rexbidva_0 $f wff ph $.
	f2rexbidva_1 $f wff ps $.
	f2rexbidva_2 $f wff ch $.
	f2rexbidva_3 $f set x $.
	f2rexbidva_4 $f set y $.
	f2rexbidva_5 $f class A $.
	f2rexbidva_6 $f class B $.
	e2rexbidva_0 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) ) $.
	2rexbidva $p |- ( ph -> ( E. x e. A E. y e. B ps <-> E. x e. A E. y e. B ch ) ) $= f2rexbidva_0 f2rexbidva_1 f2rexbidva_4 f2rexbidva_6 wrex f2rexbidva_2 f2rexbidva_4 f2rexbidva_6 wrex f2rexbidva_3 f2rexbidva_5 f2rexbidva_0 f2rexbidva_3 cv f2rexbidva_5 wcel wa f2rexbidva_1 f2rexbidva_2 f2rexbidva_4 f2rexbidva_6 f2rexbidva_0 f2rexbidva_3 cv f2rexbidva_5 wcel f2rexbidva_4 cv f2rexbidva_6 wcel f2rexbidva_1 f2rexbidva_2 wb e2rexbidva_0 anassrs rexbidva rexbidva $.
$}
$( Formula-building rule for restricted universal quantifiers (deduction
       rule).  (Contributed by NM, 28-Jan-2006.)  (Revised by Szymon
       Jaroszewicz, 16-Mar-2007.) $)
${
	$d x ph $.
	$d y ph $.
	f2ralbidv_0 $f wff ph $.
	f2ralbidv_1 $f wff ps $.
	f2ralbidv_2 $f wff ch $.
	f2ralbidv_3 $f set x $.
	f2ralbidv_4 $f set y $.
	f2ralbidv_5 $f class A $.
	f2ralbidv_6 $f class B $.
	e2ralbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	2ralbidv $p |- ( ph -> ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $= f2ralbidv_0 f2ralbidv_1 f2ralbidv_4 f2ralbidv_6 wral f2ralbidv_2 f2ralbidv_4 f2ralbidv_6 wral f2ralbidv_3 f2ralbidv_5 f2ralbidv_0 f2ralbidv_1 f2ralbidv_2 f2ralbidv_4 f2ralbidv_6 e2ralbidv_0 ralbidv ralbidv $.
$}
$( Formula-building rule for restricted existential quantifiers (deduction
       rule).  (Contributed by NM, 28-Jan-2006.) $)
${
	$d x ph $.
	$d y ph $.
	f2rexbidv_0 $f wff ph $.
	f2rexbidv_1 $f wff ps $.
	f2rexbidv_2 $f wff ch $.
	f2rexbidv_3 $f set x $.
	f2rexbidv_4 $f set y $.
	f2rexbidv_5 $f class A $.
	f2rexbidv_6 $f class B $.
	e2rexbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	2rexbidv $p |- ( ph -> ( E. x e. A E. y e. B ps <-> E. x e. A E. y e. B ch ) ) $= f2rexbidv_0 f2rexbidv_1 f2rexbidv_4 f2rexbidv_6 wrex f2rexbidv_2 f2rexbidv_4 f2rexbidv_6 wrex f2rexbidv_3 f2rexbidv_5 f2rexbidv_0 f2rexbidv_1 f2rexbidv_2 f2rexbidv_4 f2rexbidv_6 e2rexbidv_0 rexbidv rexbidv $.
$}
$( Formula-building rule for restricted quantifiers (deduction rule).
       (Contributed by NM, 28-Jan-2006.) $)
${
	$d x ph $.
	$d y ph $.
	frexralbidv_0 $f wff ph $.
	frexralbidv_1 $f wff ps $.
	frexralbidv_2 $f wff ch $.
	frexralbidv_3 $f set x $.
	frexralbidv_4 $f set y $.
	frexralbidv_5 $f class A $.
	frexralbidv_6 $f class B $.
	erexralbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	rexralbidv $p |- ( ph -> ( E. x e. A A. y e. B ps <-> E. x e. A A. y e. B ch ) ) $= frexralbidv_0 frexralbidv_1 frexralbidv_4 frexralbidv_6 wral frexralbidv_2 frexralbidv_4 frexralbidv_6 wral frexralbidv_3 frexralbidv_5 frexralbidv_0 frexralbidv_1 frexralbidv_2 frexralbidv_4 frexralbidv_6 erexralbidv_0 ralbidv rexbidv $.
$}
$( A transformation of restricted quantifiers and logical connectives.
     (Contributed by NM, 4-Sep-2005.) $)
${
	fralinexa_0 $f wff ph $.
	fralinexa_1 $f wff ps $.
	fralinexa_2 $f set x $.
	fralinexa_3 $f class A $.
	ralinexa $p |- ( A. x e. A ( ph -> -. ps ) <-> -. E. x e. A ( ph /\ ps ) ) $= fralinexa_0 fralinexa_1 wn wi fralinexa_2 fralinexa_3 wral fralinexa_0 fralinexa_1 wa wn fralinexa_2 fralinexa_3 wral fralinexa_0 fralinexa_1 wa fralinexa_2 fralinexa_3 wrex wn fralinexa_0 fralinexa_1 wn wi fralinexa_0 fralinexa_1 wa wn fralinexa_2 fralinexa_3 fralinexa_0 fralinexa_1 imnan ralbii fralinexa_0 fralinexa_1 wa fralinexa_2 fralinexa_3 ralnex bitri $.
$}
$( A transformation of restricted quantifiers and logical connectives.
     (Contributed by NM, 4-Sep-2005.) $)
${
	frexanali_0 $f wff ph $.
	frexanali_1 $f wff ps $.
	frexanali_2 $f set x $.
	frexanali_3 $f class A $.
	rexanali $p |- ( E. x e. A ( ph /\ -. ps ) <-> -. A. x e. A ( ph -> ps ) ) $= frexanali_0 frexanali_1 wn wa frexanali_2 frexanali_3 wrex frexanali_0 frexanali_1 wi wn frexanali_2 frexanali_3 wrex frexanali_0 frexanali_1 wi frexanali_2 frexanali_3 wral wn frexanali_0 frexanali_1 wn wa frexanali_0 frexanali_1 wi wn frexanali_2 frexanali_3 frexanali_0 frexanali_1 annim rexbii frexanali_0 frexanali_1 wi frexanali_2 frexanali_3 rexnal bitri $.
$}
$( Two ways to say " ` A ` belongs to ` B ` ."  (Contributed by NM,
       22-Nov-1994.) $)
${
	$d x A $.
	$d x B $.
	frisset_0 $f set x $.
	frisset_1 $f class A $.
	frisset_2 $f class B $.
	risset $p |- ( A e. B <-> E. x e. B x = A ) $= frisset_0 cv frisset_2 wcel frisset_0 cv frisset_1 wceq wa frisset_0 wex frisset_0 cv frisset_1 wceq frisset_0 cv frisset_2 wcel wa frisset_0 wex frisset_0 cv frisset_1 wceq frisset_0 frisset_2 wrex frisset_1 frisset_2 wcel frisset_0 cv frisset_2 wcel frisset_0 cv frisset_1 wceq frisset_0 exancom frisset_0 cv frisset_1 wceq frisset_0 frisset_2 df-rex frisset_0 frisset_1 frisset_2 df-clel 3bitr4ri $.
$}
$( Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by David Abernethy,
       13-Dec-2009.) $)
${
	fhbral_0 $f wff ph $.
	fhbral_1 $f set x $.
	fhbral_2 $f set y $.
	fhbral_3 $f class A $.
	ehbral_0 $e |- ( y e. A -> A. x y e. A ) $.
	ehbral_1 $e |- ( ph -> A. x ph ) $.
	hbral $p |- ( A. y e. A ph -> A. x A. y e. A ph ) $= fhbral_0 fhbral_2 fhbral_3 wral fhbral_2 cv fhbral_3 wcel fhbral_0 wi fhbral_2 wal fhbral_1 fhbral_0 fhbral_2 fhbral_3 df-ral fhbral_2 cv fhbral_3 wcel fhbral_0 wi fhbral_1 fhbral_2 fhbral_2 cv fhbral_3 wcel fhbral_0 fhbral_1 ehbral_0 ehbral_1 hbim hbal hbxfrbi $.
$}
$( ` x ` is not free in ` A. x e. A ph ` .  (Contributed by NM,
     18-Oct-1996.) $)
${
	fhbra1_0 $f wff ph $.
	fhbra1_1 $f set x $.
	fhbra1_2 $f class A $.
	hbra1 $p |- ( A. x e. A ph -> A. x A. x e. A ph ) $= fhbra1_0 fhbra1_1 fhbra1_2 wral fhbra1_1 cv fhbra1_2 wcel fhbra1_0 wi fhbra1_1 wal fhbra1_1 fhbra1_0 fhbra1_1 fhbra1_2 df-ral fhbra1_1 cv fhbra1_2 wcel fhbra1_0 wi fhbra1_1 hba1 hbxfrbi $.
$}
$( ` x ` is not free in ` A. x e. A ph ` .  (Contributed by NM,
     18-Oct-1996.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	fnfra1_0 $f wff ph $.
	fnfra1_1 $f set x $.
	fnfra1_2 $f class A $.
	nfra1 $p |- F/ x A. x e. A ph $= fnfra1_0 fnfra1_1 fnfra1_2 wral fnfra1_1 cv fnfra1_2 wcel fnfra1_0 wi fnfra1_1 wal fnfra1_1 fnfra1_0 fnfra1_1 fnfra1_2 df-ral fnfra1_1 cv fnfra1_2 wcel fnfra1_0 wi fnfra1_1 nfa1 nfxfr $.
$}
$( Deduction version of ~ nfral .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	fnfrald_0 $f wff ph $.
	fnfrald_1 $f wff ps $.
	fnfrald_2 $f set x $.
	fnfrald_3 $f set y $.
	fnfrald_4 $f class A $.
	enfrald_0 $e |- F/ y ph $.
	enfrald_1 $e |- ( ph -> F/_ x A ) $.
	enfrald_2 $e |- ( ph -> F/ x ps ) $.
	nfrald $p |- ( ph -> F/ x A. y e. A ps ) $= fnfrald_1 fnfrald_3 fnfrald_4 wral fnfrald_3 cv fnfrald_4 wcel fnfrald_1 wi fnfrald_3 wal fnfrald_0 fnfrald_2 fnfrald_1 fnfrald_3 fnfrald_4 df-ral fnfrald_0 fnfrald_3 cv fnfrald_4 wcel fnfrald_1 wi fnfrald_2 fnfrald_3 enfrald_0 fnfrald_0 fnfrald_2 cv fnfrald_3 cv wceq fnfrald_2 wal wn wa fnfrald_3 cv fnfrald_4 wcel fnfrald_1 fnfrald_2 fnfrald_0 fnfrald_2 cv fnfrald_3 cv wceq fnfrald_2 wal wn wa fnfrald_2 fnfrald_3 cv fnfrald_4 fnfrald_2 cv fnfrald_3 cv wceq fnfrald_2 wal wn fnfrald_2 fnfrald_3 cv wnfc fnfrald_0 fnfrald_2 fnfrald_3 nfcvf adantl fnfrald_0 fnfrald_2 fnfrald_4 wnfc fnfrald_2 cv fnfrald_3 cv wceq fnfrald_2 wal wn enfrald_1 adantr nfeld fnfrald_0 fnfrald_1 fnfrald_2 wnf fnfrald_2 cv fnfrald_3 cv wceq fnfrald_2 wal wn enfrald_2 adantr nfimd nfald2 nfxfrd $.
$}
$( Deduction version of ~ nfrex .  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)
${
	fnfrexd_0 $f wff ph $.
	fnfrexd_1 $f wff ps $.
	fnfrexd_2 $f set x $.
	fnfrexd_3 $f set y $.
	fnfrexd_4 $f class A $.
	enfrexd_0 $e |- F/ y ph $.
	enfrexd_1 $e |- ( ph -> F/_ x A ) $.
	enfrexd_2 $e |- ( ph -> F/ x ps ) $.
	nfrexd $p |- ( ph -> F/ x E. y e. A ps ) $= fnfrexd_1 fnfrexd_3 fnfrexd_4 wrex fnfrexd_1 wn fnfrexd_3 fnfrexd_4 wral wn fnfrexd_0 fnfrexd_2 fnfrexd_1 fnfrexd_3 fnfrexd_4 dfrex2 fnfrexd_0 fnfrexd_1 wn fnfrexd_3 fnfrexd_4 wral fnfrexd_2 fnfrexd_0 fnfrexd_1 wn fnfrexd_2 fnfrexd_3 fnfrexd_4 enfrexd_0 enfrexd_1 fnfrexd_0 fnfrexd_1 fnfrexd_2 enfrexd_2 nfnd nfrald nfnd nfxfrd $.
$}
$( Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
${
	fnfral_0 $f wff ph $.
	fnfral_1 $f set x $.
	fnfral_2 $f set y $.
	fnfral_3 $f class A $.
	enfral_0 $e |- F/_ x A $.
	enfral_1 $e |- F/ x ph $.
	nfral $p |- F/ x A. y e. A ph $= fnfral_0 fnfral_2 fnfral_3 wral fnfral_1 wnf wtru fnfral_0 fnfral_1 fnfral_2 fnfral_3 fnfral_2 nftru fnfral_1 fnfral_3 wnfc wtru enfral_0 a1i fnfral_0 fnfral_1 wnf wtru enfral_1 a1i nfrald trud $.
$}
$( Similar to Lemma 24 of [Monk2] p. 114, except the quantification of the
       antecedent is restricted.  Derived automatically from ~ hbra2VD .
       Contributed by Alan Sare 31-Dec-2011.  (Contributed by NM,
       31-Dec-2011.) $)
${
	$d A y $.
	fnfra2_0 $f wff ph $.
	fnfra2_1 $f set x $.
	fnfra2_2 $f set y $.
	fnfra2_3 $f class A $.
	fnfra2_4 $f class B $.
	nfra2 $p |- F/ y A. x e. A A. y e. B ph $= fnfra2_0 fnfra2_2 fnfra2_4 wral fnfra2_2 fnfra2_1 fnfra2_3 fnfra2_2 fnfra2_3 nfcv fnfra2_0 fnfra2_2 fnfra2_4 nfra1 nfral $.
$}
$( Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
${
	fnfrex_0 $f wff ph $.
	fnfrex_1 $f set x $.
	fnfrex_2 $f set y $.
	fnfrex_3 $f class A $.
	enfrex_0 $e |- F/_ x A $.
	enfrex_1 $e |- F/ x ph $.
	nfrex $p |- F/ x E. y e. A ph $= fnfrex_0 fnfrex_2 fnfrex_3 wrex fnfrex_0 wn fnfrex_2 fnfrex_3 wral wn fnfrex_1 fnfrex_0 fnfrex_2 fnfrex_3 dfrex2 fnfrex_0 wn fnfrex_2 fnfrex_3 wral fnfrex_1 fnfrex_0 wn fnfrex_1 fnfrex_2 fnfrex_3 enfrex_0 fnfrex_0 fnfrex_1 enfrex_1 nfn nfral nfn nfxfr $.
$}
$( ` x ` is not free in ` E. x e. A ph ` .  (Contributed by NM,
     19-Mar-1997.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	fnfre1_0 $f wff ph $.
	fnfre1_1 $f set x $.
	fnfre1_2 $f class A $.
	nfre1 $p |- F/ x E. x e. A ph $= fnfre1_0 fnfre1_1 fnfre1_2 wrex fnfre1_1 cv fnfre1_2 wcel fnfre1_0 wa fnfre1_1 wex fnfre1_1 fnfre1_0 fnfre1_1 fnfre1_2 df-rex fnfre1_1 cv fnfre1_2 wcel fnfre1_0 wa fnfre1_1 nfe1 nfxfr $.
$}
$( Triple restricted universal quantification.  (Contributed by NM,
       19-Nov-1995.) $)
${
	$d x y z $.
	$d y z A $.
	$d z B $.
	fr3al_0 $f wff ph $.
	fr3al_1 $f set x $.
	fr3al_2 $f set y $.
	fr3al_3 $f set z $.
	fr3al_4 $f class A $.
	fr3al_5 $f class B $.
	fr3al_6 $f class C $.
	r3al $p |- ( A. x e. A A. y e. B A. z e. C ph <-> A. x A. y A. z ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) ) $= fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal fr3al_2 wal fr3al_1 fr3al_4 wral fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal fr3al_2 wal wi fr3al_1 wal fr3al_0 fr3al_3 fr3al_6 wral fr3al_2 fr3al_5 wral fr3al_1 fr3al_4 wral fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel w3a fr3al_0 wi fr3al_3 wal fr3al_2 wal fr3al_1 wal fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal fr3al_2 wal fr3al_1 fr3al_4 df-ral fr3al_0 fr3al_3 fr3al_6 wral fr3al_2 fr3al_5 wral fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal fr3al_2 wal fr3al_1 fr3al_4 fr3al_0 fr3al_2 fr3al_3 fr3al_5 fr3al_6 r2al ralbii fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel w3a fr3al_0 wi fr3al_3 wal fr3al_2 wal fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal fr3al_2 wal wi fr3al_1 fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel w3a fr3al_0 wi fr3al_3 wal fr3al_2 wal fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal wi fr3al_2 wal fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal fr3al_2 wal wi fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel w3a fr3al_0 wi fr3al_3 wal fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal wi fr3al_2 fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel w3a fr3al_0 wi fr3al_3 wal fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi wi fr3al_3 wal fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal wi fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel w3a fr3al_0 wi fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi wi fr3al_3 fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel w3a fr3al_0 wi fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa wa fr3al_0 wi fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi wi fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel w3a fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa wa fr3al_0 fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel 3anass imbi1i fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 impexp bitri albii fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 19.21v bitri albii fr3al_1 cv fr3al_4 wcel fr3al_2 cv fr3al_5 wcel fr3al_3 cv fr3al_6 wcel wa fr3al_0 wi fr3al_3 wal fr3al_2 19.21v bitri albii 3bitr4i $.
$}
$( Universal quantification implies restricted quantification.  (Contributed
     by NM, 20-Oct-2006.) $)
${
	falral_0 $f wff ph $.
	falral_1 $f set x $.
	falral_2 $f class A $.
	alral $p |- ( A. x ph -> A. x e. A ph ) $= falral_0 falral_1 wal falral_1 cv falral_2 wcel falral_0 wi falral_1 wal falral_0 falral_1 falral_2 wral falral_0 falral_1 cv falral_2 wcel falral_0 wi falral_1 falral_0 falral_1 cv falral_2 wcel ax-1 alimi falral_0 falral_1 falral_2 df-ral sylibr $.
$}
$( Restricted existence implies existence.  (Contributed by NM,
     11-Nov-1995.) $)
${
	frexex_0 $f wff ph $.
	frexex_1 $f set x $.
	frexex_2 $f class A $.
	rexex $p |- ( E. x e. A ph -> E. x ph ) $= frexex_0 frexex_1 frexex_2 wrex frexex_1 cv frexex_2 wcel frexex_0 wa frexex_1 wex frexex_0 frexex_1 wex frexex_0 frexex_1 frexex_2 df-rex frexex_1 cv frexex_2 wcel frexex_0 wa frexex_0 frexex_1 frexex_1 cv frexex_2 wcel frexex_0 simpr eximi sylbi $.
$}
$( Restricted specialization.  (Contributed by NM, 17-Oct-1996.) $)
${
	frsp_0 $f wff ph $.
	frsp_1 $f set x $.
	frsp_2 $f class A $.
	rsp $p |- ( A. x e. A ph -> ( x e. A -> ph ) ) $= frsp_0 frsp_1 frsp_2 wral frsp_1 cv frsp_2 wcel frsp_0 wi frsp_1 wal frsp_1 cv frsp_2 wcel frsp_0 wi frsp_0 frsp_1 frsp_2 df-ral frsp_1 cv frsp_2 wcel frsp_0 wi frsp_1 sp sylbi $.
$}
$( Restricted specialization.  (Contributed by NM, 12-Oct-1999.) $)
${
	frspe_0 $f wff ph $.
	frspe_1 $f set x $.
	frspe_2 $f class A $.
	rspe $p |- ( ( x e. A /\ ph ) -> E. x e. A ph ) $= frspe_1 cv frspe_2 wcel frspe_0 wa frspe_1 cv frspe_2 wcel frspe_0 wa frspe_1 wex frspe_0 frspe_1 frspe_2 wrex frspe_1 cv frspe_2 wcel frspe_0 wa frspe_1 19.8a frspe_0 frspe_1 frspe_2 df-rex sylibr $.
$}
$( Restricted specialization.  (Contributed by NM, 11-Feb-1997.) $)
${
	frsp2_0 $f wff ph $.
	frsp2_1 $f set x $.
	frsp2_2 $f set y $.
	frsp2_3 $f class A $.
	frsp2_4 $f class B $.
	rsp2 $p |- ( A. x e. A A. y e. B ph -> ( ( x e. A /\ y e. B ) -> ph ) ) $= frsp2_0 frsp2_2 frsp2_4 wral frsp2_1 frsp2_3 wral frsp2_1 cv frsp2_3 wcel frsp2_2 cv frsp2_4 wcel frsp2_0 frsp2_0 frsp2_2 frsp2_4 wral frsp2_1 frsp2_3 wral frsp2_1 cv frsp2_3 wcel frsp2_0 frsp2_2 frsp2_4 wral frsp2_2 cv frsp2_4 wcel frsp2_0 wi frsp2_0 frsp2_2 frsp2_4 wral frsp2_1 frsp2_3 rsp frsp2_0 frsp2_2 frsp2_4 rsp syl6 imp3a $.
$}
$( Restricted specialization.  (Contributed by FL, 4-Jun-2012.) $)
${
	frsp2e_0 $f wff ph $.
	frsp2e_1 $f set x $.
	frsp2e_2 $f set y $.
	frsp2e_3 $f class A $.
	frsp2e_4 $f class B $.
	rsp2e $p |- ( ( x e. A /\ y e. B /\ ph ) -> E. x e. A E. y e. B ph ) $= frsp2e_1 cv frsp2e_3 wcel frsp2e_2 cv frsp2e_4 wcel frsp2e_0 w3a frsp2e_1 cv frsp2e_3 wcel frsp2e_0 frsp2e_2 frsp2e_4 wrex wa frsp2e_1 wex frsp2e_0 frsp2e_2 frsp2e_4 wrex frsp2e_1 frsp2e_3 wrex frsp2e_1 cv frsp2e_3 wcel frsp2e_2 cv frsp2e_4 wcel frsp2e_0 w3a frsp2e_1 cv frsp2e_3 wcel frsp2e_0 frsp2e_2 frsp2e_4 wrex frsp2e_1 cv frsp2e_3 wcel frsp2e_0 frsp2e_2 frsp2e_4 wrex wa frsp2e_1 wex frsp2e_1 cv frsp2e_3 wcel frsp2e_2 cv frsp2e_4 wcel frsp2e_0 simp1 frsp2e_2 cv frsp2e_4 wcel frsp2e_0 frsp2e_0 frsp2e_2 frsp2e_4 wrex frsp2e_1 cv frsp2e_3 wcel frsp2e_0 frsp2e_2 frsp2e_4 rspe 3adant1 frsp2e_1 cv frsp2e_3 wcel frsp2e_0 frsp2e_2 frsp2e_4 wrex wa frsp2e_1 19.8a syl2anc frsp2e_0 frsp2e_2 frsp2e_4 wrex frsp2e_1 frsp2e_3 df-rex sylibr $.
$}
$( Specialization rule for restricted quantification.  (Contributed by NM,
       19-Nov-1994.) $)
${
	frspec_0 $f wff ph $.
	frspec_1 $f set x $.
	frspec_2 $f class A $.
	erspec_0 $e |- A. x e. A ph $.
	rspec $p |- ( x e. A -> ph ) $= frspec_0 frspec_1 frspec_2 wral frspec_1 cv frspec_2 wcel frspec_0 wi erspec_0 frspec_0 frspec_1 frspec_2 rsp ax-mp $.
$}
$( Generalization rule for restricted quantification.  (Contributed by NM,
       19-Nov-1994.) $)
${
	frgen_0 $f wff ph $.
	frgen_1 $f set x $.
	frgen_2 $f class A $.
	ergen_0 $e |- ( x e. A -> ph ) $.
	rgen $p |- A. x e. A ph $= frgen_0 frgen_1 frgen_2 wral frgen_1 cv frgen_2 wcel frgen_0 wi frgen_1 frgen_0 frgen_1 frgen_2 df-ral ergen_0 mpgbir $.
$}
$( Generalization rule for restricted quantification.  Note that ` x ` and
       ` y ` needn't be distinct (and illustrates the use of ~ dvelim ).
       (Contributed by NM, 23-Nov-1994.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged. $)
${
	$d y z A $.
	$d x z $.
	irgen2a_0 $f set z $.
	frgen2a_0 $f wff ph $.
	frgen2a_1 $f set x $.
	frgen2a_2 $f set y $.
	frgen2a_3 $f class A $.
	ergen2a_0 $e |- ( ( x e. A /\ y e. A ) -> ph ) $.
	rgen2a $p |- A. x e. A A. y e. A ph $= frgen2a_0 frgen2a_2 frgen2a_3 wral frgen2a_1 frgen2a_3 frgen2a_1 cv frgen2a_3 wcel frgen2a_2 cv frgen2a_3 wcel frgen2a_0 wi frgen2a_2 wal frgen2a_0 frgen2a_2 frgen2a_3 wral frgen2a_2 cv frgen2a_1 cv wceq frgen2a_2 wal frgen2a_1 cv frgen2a_3 wcel frgen2a_2 cv frgen2a_3 wcel frgen2a_0 wi frgen2a_2 wal wi frgen2a_2 cv frgen2a_1 cv wceq frgen2a_2 wal frgen2a_2 cv frgen2a_3 wcel frgen2a_0 wi frgen2a_2 wal frgen2a_1 cv frgen2a_3 wcel frgen2a_2 cv frgen2a_1 cv wceq frgen2a_2 cv frgen2a_3 wcel frgen2a_0 wi frgen2a_2 frgen2a_2 cv frgen2a_1 cv wceq frgen2a_2 cv frgen2a_3 wcel frgen2a_0 frgen2a_2 cv frgen2a_1 cv wceq frgen2a_2 cv frgen2a_3 wcel frgen2a_1 cv frgen2a_3 wcel frgen2a_2 cv frgen2a_3 wcel frgen2a_0 wi frgen2a_2 cv frgen2a_1 cv frgen2a_3 eleq1 frgen2a_1 cv frgen2a_3 wcel frgen2a_2 cv frgen2a_3 wcel frgen2a_0 ergen2a_0 ex syl6bi pm2.43d alimi a1d frgen2a_2 cv frgen2a_1 cv wceq frgen2a_2 wal wn frgen2a_1 cv frgen2a_3 wcel frgen2a_1 cv frgen2a_3 wcel frgen2a_2 wal frgen2a_2 cv frgen2a_3 wcel frgen2a_0 wi frgen2a_2 wal irgen2a_0 cv frgen2a_3 wcel frgen2a_1 cv frgen2a_3 wcel frgen2a_2 frgen2a_1 irgen2a_0 irgen2a_0 cv frgen2a_1 cv frgen2a_3 eleq1 dvelimv frgen2a_1 cv frgen2a_3 wcel frgen2a_2 cv frgen2a_3 wcel frgen2a_0 wi frgen2a_2 frgen2a_1 cv frgen2a_3 wcel frgen2a_2 cv frgen2a_3 wcel frgen2a_0 ergen2a_0 ex alimi syl6 pm2.61i frgen2a_0 frgen2a_2 frgen2a_3 df-ral sylibr rgen $.
$}
$( Generalization rule for restricted quantification.  (Contributed by NM,
       18-Jun-2014.) $)
${
	frgenw_0 $f wff ph $.
	frgenw_1 $f set x $.
	frgenw_2 $f class A $.
	ergenw_0 $e |- ph $.
	rgenw $p |- A. x e. A ph $= frgenw_0 frgenw_1 frgenw_2 frgenw_0 frgenw_1 cv frgenw_2 wcel ergenw_0 a1i rgen $.
$}
$( Generalization rule for restricted quantification.  Note that ` x ` and
       ` y ` needn't be distinct.  (Contributed by NM, 18-Jun-2014.) $)
${
	frgen2w_0 $f wff ph $.
	frgen2w_1 $f set x $.
	frgen2w_2 $f set y $.
	frgen2w_3 $f class A $.
	frgen2w_4 $f class B $.
	ergen2w_0 $e |- ph $.
	rgen2w $p |- A. x e. A A. y e. B ph $= frgen2w_0 frgen2w_2 frgen2w_4 wral frgen2w_1 frgen2w_3 frgen2w_0 frgen2w_2 frgen2w_4 ergen2w_0 rgenw rgenw $.
$}
$( Modus ponens combined with restricted generalization.  (Contributed by
       NM, 10-Aug-2004.) $)
${
	fmprg_0 $f wff ph $.
	fmprg_1 $f wff ps $.
	fmprg_2 $f set x $.
	fmprg_3 $f class A $.
	emprg_0 $e |- ( A. x e. A ph -> ps ) $.
	emprg_1 $e |- ( x e. A -> ph ) $.
	mprg $p |- ps $= fmprg_0 fmprg_2 fmprg_3 wral fmprg_1 fmprg_0 fmprg_2 fmprg_3 emprg_1 rgen emprg_0 ax-mp $.
$}
$( Modus ponens on biconditional combined with restricted generalization.
       (Contributed by NM, 21-Mar-2004.) $)
${
	fmprgbir_0 $f wff ph $.
	fmprgbir_1 $f wff ps $.
	fmprgbir_2 $f set x $.
	fmprgbir_3 $f class A $.
	emprgbir_0 $e |- ( ph <-> A. x e. A ps ) $.
	emprgbir_1 $e |- ( x e. A -> ps ) $.
	mprgbir $p |- ph $= fmprgbir_0 fmprgbir_1 fmprgbir_2 fmprgbir_3 wral fmprgbir_1 fmprgbir_2 fmprgbir_3 emprgbir_1 rgen emprgbir_0 mpbir $.
$}
$( Distribution of restricted quantification over implication.  (Contributed
     by NM, 9-Feb-1997.) $)
${
	fralim_0 $f wff ph $.
	fralim_1 $f wff ps $.
	fralim_2 $f set x $.
	fralim_3 $f class A $.
	ralim $p |- ( A. x e. A ( ph -> ps ) -> ( A. x e. A ph -> A. x e. A ps ) ) $= fralim_0 fralim_1 wi fralim_2 fralim_3 wral fralim_2 cv fralim_3 wcel fralim_0 wi fralim_2 wal fralim_2 cv fralim_3 wcel fralim_1 wi fralim_2 wal fralim_0 fralim_2 fralim_3 wral fralim_1 fralim_2 fralim_3 wral fralim_0 fralim_1 wi fralim_2 fralim_3 wral fralim_2 cv fralim_3 wcel fralim_0 fralim_1 wi wi fralim_2 wal fralim_2 cv fralim_3 wcel fralim_0 wi fralim_2 wal fralim_2 cv fralim_3 wcel fralim_1 wi fralim_2 wal wi fralim_0 fralim_1 wi fralim_2 fralim_3 df-ral fralim_2 cv fralim_3 wcel fralim_0 fralim_1 wi wi fralim_2 cv fralim_3 wcel fralim_0 wi fralim_2 cv fralim_3 wcel fralim_1 wi fralim_2 fralim_2 cv fralim_3 wcel fralim_0 fralim_1 ax-2 al2imi sylbi fralim_0 fralim_2 fralim_3 df-ral fralim_1 fralim_2 fralim_3 df-ral 3imtr4g $.
$}
$( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 22-Feb-2004.) $)
${
	fralimi2_0 $f wff ph $.
	fralimi2_1 $f wff ps $.
	fralimi2_2 $f set x $.
	fralimi2_3 $f class A $.
	fralimi2_4 $f class B $.
	eralimi2_0 $e |- ( ( x e. A -> ph ) -> ( x e. B -> ps ) ) $.
	ralimi2 $p |- ( A. x e. A ph -> A. x e. B ps ) $= fralimi2_2 cv fralimi2_3 wcel fralimi2_0 wi fralimi2_2 wal fralimi2_2 cv fralimi2_4 wcel fralimi2_1 wi fralimi2_2 wal fralimi2_0 fralimi2_2 fralimi2_3 wral fralimi2_1 fralimi2_2 fralimi2_4 wral fralimi2_2 cv fralimi2_3 wcel fralimi2_0 wi fralimi2_2 cv fralimi2_4 wcel fralimi2_1 wi fralimi2_2 eralimi2_0 alimi fralimi2_0 fralimi2_2 fralimi2_3 df-ral fralimi2_1 fralimi2_2 fralimi2_4 df-ral 3imtr4i $.
$}
$( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 19-Jul-1996.) $)
${
	fralimia_0 $f wff ph $.
	fralimia_1 $f wff ps $.
	fralimia_2 $f set x $.
	fralimia_3 $f class A $.
	eralimia_0 $e |- ( x e. A -> ( ph -> ps ) ) $.
	ralimia $p |- ( A. x e. A ph -> A. x e. A ps ) $= fralimia_0 fralimia_1 fralimia_2 fralimia_3 fralimia_3 fralimia_2 cv fralimia_3 wcel fralimia_0 fralimia_1 eralimia_0 a2i ralimi2 $.
$}
$( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 4-Aug-2007.) $)
${
	fralimiaa_0 $f wff ph $.
	fralimiaa_1 $f wff ps $.
	fralimiaa_2 $f set x $.
	fralimiaa_3 $f class A $.
	eralimiaa_0 $e |- ( ( x e. A /\ ph ) -> ps ) $.
	ralimiaa $p |- ( A. x e. A ph -> A. x e. A ps ) $= fralimiaa_0 fralimiaa_1 fralimiaa_2 fralimiaa_3 fralimiaa_2 cv fralimiaa_3 wcel fralimiaa_0 fralimiaa_1 eralimiaa_0 ex ralimia $.
$}
$( Inference quantifying both antecedent and consequent, with strong
       hypothesis.  (Contributed by NM, 4-Mar-1997.) $)
${
	fralimi_0 $f wff ph $.
	fralimi_1 $f wff ps $.
	fralimi_2 $f set x $.
	fralimi_3 $f class A $.
	eralimi_0 $e |- ( ph -> ps ) $.
	ralimi $p |- ( A. x e. A ph -> A. x e. A ps ) $= fralimi_0 fralimi_1 fralimi_2 fralimi_3 fralimi_0 fralimi_1 wi fralimi_2 cv fralimi_3 wcel eralimi_0 a1i ralimia $.
$}
$( Inference quantifying antecedent, nested antecedent, and consequent,
       with a strong hypothesis.  (Contributed by NM, 19-Dec-2006.) $)
${
	fral2imi_0 $f wff ph $.
	fral2imi_1 $f wff ps $.
	fral2imi_2 $f wff ch $.
	fral2imi_3 $f set x $.
	fral2imi_4 $f class A $.
	eral2imi_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ral2imi $p |- ( A. x e. A ph -> ( A. x e. A ps -> A. x e. A ch ) ) $= fral2imi_0 fral2imi_3 fral2imi_4 wral fral2imi_1 fral2imi_2 wi fral2imi_3 fral2imi_4 wral fral2imi_1 fral2imi_3 fral2imi_4 wral fral2imi_2 fral2imi_3 fral2imi_4 wral wi fral2imi_0 fral2imi_1 fral2imi_2 wi fral2imi_3 fral2imi_4 eral2imi_0 ralimi fral2imi_1 fral2imi_2 fral2imi_3 fral2imi_4 ralim syl $.
$}
$( Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 22-Sep-2003.) $)
${
	fralimdaa_0 $f wff ph $.
	fralimdaa_1 $f wff ps $.
	fralimdaa_2 $f wff ch $.
	fralimdaa_3 $f set x $.
	fralimdaa_4 $f class A $.
	eralimdaa_0 $e |- F/ x ph $.
	eralimdaa_1 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	ralimdaa $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $= fralimdaa_0 fralimdaa_3 cv fralimdaa_4 wcel fralimdaa_1 wi fralimdaa_3 wal fralimdaa_3 cv fralimdaa_4 wcel fralimdaa_2 wi fralimdaa_3 wal fralimdaa_1 fralimdaa_3 fralimdaa_4 wral fralimdaa_2 fralimdaa_3 fralimdaa_4 wral fralimdaa_0 fralimdaa_3 cv fralimdaa_4 wcel fralimdaa_1 wi fralimdaa_3 cv fralimdaa_4 wcel fralimdaa_2 wi fralimdaa_3 eralimdaa_0 fralimdaa_0 fralimdaa_3 cv fralimdaa_4 wcel fralimdaa_1 fralimdaa_2 fralimdaa_0 fralimdaa_3 cv fralimdaa_4 wcel fralimdaa_1 fralimdaa_2 wi eralimdaa_1 ex a2d alimd fralimdaa_1 fralimdaa_3 fralimdaa_4 df-ral fralimdaa_2 fralimdaa_3 fralimdaa_4 df-ral 3imtr4g $.
$}
$( Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 22-May-1999.) $)
${
	$d x ph $.
	fralimdva_0 $f wff ph $.
	fralimdva_1 $f wff ps $.
	fralimdva_2 $f wff ch $.
	fralimdva_3 $f set x $.
	fralimdva_4 $f class A $.
	eralimdva_0 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	ralimdva $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $= fralimdva_0 fralimdva_1 fralimdva_2 fralimdva_3 fralimdva_4 fralimdva_0 fralimdva_3 nfv eralimdva_0 ralimdaa $.
$}
$( Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 8-Oct-2003.) $)
${
	$d x ph $.
	fralimdv_0 $f wff ph $.
	fralimdv_1 $f wff ps $.
	fralimdv_2 $f wff ch $.
	fralimdv_3 $f set x $.
	fralimdv_4 $f class A $.
	eralimdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ralimdv $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $= fralimdv_0 fralimdv_1 fralimdv_2 fralimdv_3 fralimdv_4 fralimdv_0 fralimdv_1 fralimdv_2 wi fralimdv_3 cv fralimdv_4 wcel eralimdv_0 adantr ralimdva $.
$}
$( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 1-Feb-2005.) $)
${
	$d x ph $.
	fralimdv2_0 $f wff ph $.
	fralimdv2_1 $f wff ps $.
	fralimdv2_2 $f wff ch $.
	fralimdv2_3 $f set x $.
	fralimdv2_4 $f class A $.
	fralimdv2_5 $f class B $.
	eralimdv2_0 $e |- ( ph -> ( ( x e. A -> ps ) -> ( x e. B -> ch ) ) ) $.
	ralimdv2 $p |- ( ph -> ( A. x e. A ps -> A. x e. B ch ) ) $= fralimdv2_0 fralimdv2_3 cv fralimdv2_4 wcel fralimdv2_1 wi fralimdv2_3 wal fralimdv2_3 cv fralimdv2_5 wcel fralimdv2_2 wi fralimdv2_3 wal fralimdv2_1 fralimdv2_3 fralimdv2_4 wral fralimdv2_2 fralimdv2_3 fralimdv2_5 wral fralimdv2_0 fralimdv2_3 cv fralimdv2_4 wcel fralimdv2_1 wi fralimdv2_3 cv fralimdv2_5 wcel fralimdv2_2 wi fralimdv2_3 eralimdv2_0 alimdv fralimdv2_1 fralimdv2_3 fralimdv2_4 df-ral fralimdv2_2 fralimdv2_3 fralimdv2_5 df-ral 3imtr4g $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 10-Oct-1999.) $)
${
	fralrimi_0 $f wff ph $.
	fralrimi_1 $f wff ps $.
	fralrimi_2 $f set x $.
	fralrimi_3 $f class A $.
	eralrimi_0 $e |- F/ x ph $.
	eralrimi_1 $e |- ( ph -> ( x e. A -> ps ) ) $.
	ralrimi $p |- ( ph -> A. x e. A ps ) $= fralrimi_0 fralrimi_2 cv fralrimi_3 wcel fralrimi_1 wi fralrimi_2 wal fralrimi_1 fralrimi_2 fralrimi_3 wral fralrimi_0 fralrimi_2 cv fralrimi_3 wcel fralrimi_1 wi fralrimi_2 eralrimi_0 eralrimi_1 alrimi fralrimi_1 fralrimi_2 fralrimi_3 df-ral sylibr $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 22-Nov-1994.) $)
${
	$d x ph $.
	fralrimiv_0 $f wff ph $.
	fralrimiv_1 $f wff ps $.
	fralrimiv_2 $f set x $.
	fralrimiv_3 $f class A $.
	eralrimiv_0 $e |- ( ph -> ( x e. A -> ps ) ) $.
	ralrimiv $p |- ( ph -> A. x e. A ps ) $= fralrimiv_0 fralrimiv_1 fralrimiv_2 fralrimiv_3 fralrimiv_0 fralrimiv_2 nfv eralrimiv_0 ralrimi $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 2-Jan-2006.) $)
${
	$d x ph $.
	fralrimiva_0 $f wff ph $.
	fralrimiva_1 $f wff ps $.
	fralrimiva_2 $f set x $.
	fralrimiva_3 $f class A $.
	eralrimiva_0 $e |- ( ( ph /\ x e. A ) -> ps ) $.
	ralrimiva $p |- ( ph -> A. x e. A ps ) $= fralrimiva_0 fralrimiva_1 fralrimiva_2 fralrimiva_3 fralrimiva_0 fralrimiva_2 cv fralrimiva_3 wcel fralrimiva_1 eralrimiva_0 ex ralrimiv $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 18-Jun-2014.) $)
${
	$d x ph $.
	fralrimivw_0 $f wff ph $.
	fralrimivw_1 $f wff ps $.
	fralrimivw_2 $f set x $.
	fralrimivw_3 $f class A $.
	eralrimivw_0 $e |- ( ph -> ps ) $.
	ralrimivw $p |- ( ph -> A. x e. A ps ) $= fralrimivw_0 fralrimivw_1 fralrimivw_2 fralrimivw_3 fralrimivw_0 fralrimivw_1 fralrimivw_2 cv fralrimivw_3 wcel eralrimivw_0 a1d ralrimiv $.
$}
$( Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers (closed
       theorem version).  (Contributed by NM, 1-Mar-2008.) $)
${
	fr19.21t_0 $f wff ph $.
	fr19.21t_1 $f wff ps $.
	fr19.21t_2 $f set x $.
	fr19.21t_3 $f class A $.
	r19.21t $p |- ( F/ x ph -> ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) ) $= fr19.21t_0 fr19.21t_2 wnf fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_0 fr19.21t_1 wi wi fr19.21t_2 wal fr19.21t_0 fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_1 wi fr19.21t_2 wal wi fr19.21t_0 fr19.21t_1 wi fr19.21t_2 fr19.21t_3 wral fr19.21t_0 fr19.21t_1 fr19.21t_2 fr19.21t_3 wral wi fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_0 fr19.21t_1 wi wi fr19.21t_2 wal fr19.21t_0 fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_1 wi wi fr19.21t_2 wal fr19.21t_0 fr19.21t_2 wnf fr19.21t_0 fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_1 wi fr19.21t_2 wal wi fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_0 fr19.21t_1 wi wi fr19.21t_0 fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_1 wi wi fr19.21t_2 fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_0 fr19.21t_1 bi2.04 albii fr19.21t_0 fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_1 wi fr19.21t_2 19.21t syl5bb fr19.21t_0 fr19.21t_1 wi fr19.21t_2 fr19.21t_3 df-ral fr19.21t_1 fr19.21t_2 fr19.21t_3 wral fr19.21t_2 cv fr19.21t_3 wcel fr19.21t_1 wi fr19.21t_2 wal fr19.21t_0 fr19.21t_1 fr19.21t_2 fr19.21t_3 df-ral imbi2i 3bitr4g $.
$}
$( Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by Scott Fenton, 30-Mar-2011.) $)
${
	fr19.21_0 $f wff ph $.
	fr19.21_1 $f wff ps $.
	fr19.21_2 $f set x $.
	fr19.21_3 $f class A $.
	er19.21_0 $e |- F/ x ph $.
	r19.21 $p |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) $= fr19.21_0 fr19.21_2 wnf fr19.21_0 fr19.21_1 wi fr19.21_2 fr19.21_3 wral fr19.21_0 fr19.21_1 fr19.21_2 fr19.21_3 wral wi wb er19.21_0 fr19.21_0 fr19.21_1 fr19.21_2 fr19.21_3 r19.21t ax-mp $.
$}
$( Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)
${
	$d x ph $.
	fr19.21v_0 $f wff ph $.
	fr19.21v_1 $f wff ps $.
	fr19.21v_2 $f set x $.
	fr19.21v_3 $f class A $.
	r19.21v $p |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) $= fr19.21v_0 fr19.21v_1 fr19.21v_2 fr19.21v_3 fr19.21v_0 fr19.21v_2 nfv r19.21 $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 16-Feb-2004.) $)
${
	fralrimd_0 $f wff ph $.
	fralrimd_1 $f wff ps $.
	fralrimd_2 $f wff ch $.
	fralrimd_3 $f set x $.
	fralrimd_4 $f class A $.
	eralrimd_0 $e |- F/ x ph $.
	eralrimd_1 $e |- F/ x ps $.
	eralrimd_2 $e |- ( ph -> ( ps -> ( x e. A -> ch ) ) ) $.
	ralrimd $p |- ( ph -> ( ps -> A. x e. A ch ) ) $= fralrimd_0 fralrimd_1 fralrimd_3 cv fralrimd_4 wcel fralrimd_2 wi fralrimd_3 wal fralrimd_2 fralrimd_3 fralrimd_4 wral fralrimd_0 fralrimd_1 fralrimd_3 cv fralrimd_4 wcel fralrimd_2 wi fralrimd_3 eralrimd_0 eralrimd_1 eralrimd_2 alrimd fralrimd_2 fralrimd_3 fralrimd_4 df-ral syl6ibr $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 27-May-1998.) $)
${
	$d x ph $.
	$d x ps $.
	fralrimdv_0 $f wff ph $.
	fralrimdv_1 $f wff ps $.
	fralrimdv_2 $f wff ch $.
	fralrimdv_3 $f set x $.
	fralrimdv_4 $f class A $.
	eralrimdv_0 $e |- ( ph -> ( ps -> ( x e. A -> ch ) ) ) $.
	ralrimdv $p |- ( ph -> ( ps -> A. x e. A ch ) ) $= fralrimdv_0 fralrimdv_1 fralrimdv_2 fralrimdv_3 fralrimdv_4 fralrimdv_0 fralrimdv_3 nfv fralrimdv_1 fralrimdv_3 nfv eralrimdv_0 ralrimd $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 2-Feb-2008.) $)
${
	$d x ph $.
	$d x ps $.
	fralrimdva_0 $f wff ph $.
	fralrimdva_1 $f wff ps $.
	fralrimdva_2 $f wff ch $.
	fralrimdva_3 $f set x $.
	fralrimdva_4 $f class A $.
	eralrimdva_0 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	ralrimdva $p |- ( ph -> ( ps -> A. x e. A ch ) ) $= fralrimdva_0 fralrimdva_1 fralrimdva_2 fralrimdva_3 fralrimdva_4 fralrimdva_0 fralrimdva_3 cv fralrimdva_4 wcel fralrimdva_1 fralrimdva_2 fralrimdva_0 fralrimdva_3 cv fralrimdva_4 wcel fralrimdva_1 fralrimdva_2 wi eralrimdva_0 ex com23 ralrimdv $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       24-Jul-2004.) $)
${
	$d x y ph $.
	$d y A $.
	fralrimivv_0 $f wff ph $.
	fralrimivv_1 $f wff ps $.
	fralrimivv_2 $f set x $.
	fralrimivv_3 $f set y $.
	fralrimivv_4 $f class A $.
	fralrimivv_5 $f class B $.
	eralrimivv_0 $e |- ( ph -> ( ( x e. A /\ y e. B ) -> ps ) ) $.
	ralrimivv $p |- ( ph -> A. x e. A A. y e. B ps ) $= fralrimivv_0 fralrimivv_1 fralrimivv_3 fralrimivv_5 wral fralrimivv_2 fralrimivv_4 fralrimivv_0 fralrimivv_2 cv fralrimivv_4 wcel fralrimivv_1 fralrimivv_3 fralrimivv_5 fralrimivv_0 fralrimivv_2 cv fralrimivv_4 wcel fralrimivv_3 cv fralrimivv_5 wcel fralrimivv_1 eralrimivv_0 exp3a ralrimdv ralrimiv $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by Jeff
       Madsen, 19-Jun-2011.) $)
${
	$d ph x y $.
	$d A y $.
	fralrimivva_0 $f wff ph $.
	fralrimivva_1 $f wff ps $.
	fralrimivva_2 $f set x $.
	fralrimivva_3 $f set y $.
	fralrimivva_4 $f class A $.
	fralrimivva_5 $f class B $.
	eralrimivva_0 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ps ) $.
	ralrimivva $p |- ( ph -> A. x e. A A. y e. B ps ) $= fralrimivva_0 fralrimivva_1 fralrimivva_2 fralrimivva_3 fralrimivva_4 fralrimivva_5 fralrimivva_0 fralrimivva_2 cv fralrimivva_4 wcel fralrimivva_3 cv fralrimivva_5 wcel wa fralrimivva_1 eralrimivva_0 ex ralrimivv $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with triple quantification.)  (Contributed by Mario
       Carneiro, 9-Jul-2014.) $)
${
	$d ph x y z $.
	$d A y z $.
	$d B z $.
	fralrimivvva_0 $f wff ph $.
	fralrimivvva_1 $f wff ps $.
	fralrimivvva_2 $f set x $.
	fralrimivvva_3 $f set y $.
	fralrimivvva_4 $f set z $.
	fralrimivvva_5 $f class A $.
	fralrimivvva_6 $f class B $.
	fralrimivvva_7 $f class C $.
	eralrimivvva_0 $e |- ( ( ph /\ ( x e. A /\ y e. B /\ z e. C ) ) -> ps ) $.
	ralrimivvva $p |- ( ph -> A. x e. A A. y e. B A. z e. C ps ) $= fralrimivvva_0 fralrimivvva_1 fralrimivvva_4 fralrimivvva_7 wral fralrimivvva_3 fralrimivvva_6 wral fralrimivvva_2 fralrimivvva_5 fralrimivvva_0 fralrimivvva_2 cv fralrimivvva_5 wcel wa fralrimivvva_1 fralrimivvva_4 fralrimivvva_7 wral fralrimivvva_3 fralrimivvva_6 fralrimivvva_0 fralrimivvva_2 cv fralrimivvva_5 wcel wa fralrimivvva_3 cv fralrimivvva_6 wcel wa fralrimivvva_1 fralrimivvva_4 fralrimivvva_7 fralrimivvva_0 fralrimivvva_2 cv fralrimivvva_5 wcel fralrimivvva_3 cv fralrimivvva_6 wcel fralrimivvva_4 cv fralrimivvva_7 wcel fralrimivvva_1 fralrimivvva_0 fralrimivvva_2 cv fralrimivvva_5 wcel fralrimivvva_3 cv fralrimivvva_6 wcel fralrimivvva_4 cv fralrimivvva_7 wcel fralrimivvva_1 eralrimivvva_0 3exp2 imp41 ralrimiva ralrimiva ralrimiva $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       1-Jun-2005.) $)
${
	$d x y ph $.
	$d x y ps $.
	$d y A $.
	fralrimdvv_0 $f wff ph $.
	fralrimdvv_1 $f wff ps $.
	fralrimdvv_2 $f wff ch $.
	fralrimdvv_3 $f set x $.
	fralrimdvv_4 $f set y $.
	fralrimdvv_5 $f class A $.
	fralrimdvv_6 $f class B $.
	eralrimdvv_0 $e |- ( ph -> ( ps -> ( ( x e. A /\ y e. B ) -> ch ) ) ) $.
	ralrimdvv $p |- ( ph -> ( ps -> A. x e. A A. y e. B ch ) ) $= fralrimdvv_0 fralrimdvv_1 fralrimdvv_2 fralrimdvv_4 fralrimdvv_6 wral fralrimdvv_3 fralrimdvv_5 wral fralrimdvv_0 fralrimdvv_1 wa fralrimdvv_2 fralrimdvv_3 fralrimdvv_4 fralrimdvv_5 fralrimdvv_6 fralrimdvv_0 fralrimdvv_1 fralrimdvv_3 cv fralrimdvv_5 wcel fralrimdvv_4 cv fralrimdvv_6 wcel wa fralrimdvv_2 wi eralrimdvv_0 imp ralrimivv ex $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       2-Feb-2008.) $)
${
	$d x y ph $.
	$d x y ps $.
	$d y A $.
	fralrimdvva_0 $f wff ph $.
	fralrimdvva_1 $f wff ps $.
	fralrimdvva_2 $f wff ch $.
	fralrimdvva_3 $f set x $.
	fralrimdvva_4 $f set y $.
	fralrimdvva_5 $f class A $.
	fralrimdvva_6 $f class B $.
	eralrimdvva_0 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) ) $.
	ralrimdvva $p |- ( ph -> ( ps -> A. x e. A A. y e. B ch ) ) $= fralrimdvva_0 fralrimdvva_1 fralrimdvva_2 fralrimdvva_3 fralrimdvva_4 fralrimdvva_5 fralrimdvva_6 fralrimdvva_0 fralrimdvva_3 cv fralrimdvva_5 wcel fralrimdvva_4 cv fralrimdvva_6 wcel wa fralrimdvva_1 fralrimdvva_2 fralrimdvva_0 fralrimdvva_3 cv fralrimdvva_5 wcel fralrimdvva_4 cv fralrimdvva_6 wcel wa fralrimdvva_1 fralrimdvva_2 wi eralrimdvva_0 ex com23 ralrimdvv $.
$}
$( Generalization rule for restricted quantification.  (Contributed by NM,
       30-May-1999.) $)
${
	$d x y $.
	$d y A $.
	frgen2_0 $f wff ph $.
	frgen2_1 $f set x $.
	frgen2_2 $f set y $.
	frgen2_3 $f class A $.
	frgen2_4 $f class B $.
	ergen2_0 $e |- ( ( x e. A /\ y e. B ) -> ph ) $.
	rgen2 $p |- A. x e. A A. y e. B ph $= frgen2_0 frgen2_2 frgen2_4 wral frgen2_1 frgen2_3 frgen2_1 cv frgen2_3 wcel frgen2_0 frgen2_2 frgen2_4 ergen2_0 ralrimiva rgen $.
$}
$( Generalization rule for restricted quantification.  (Contributed by NM,
       12-Jan-2008.) $)
${
	$d y z A $.
	$d z B $.
	$d x y z $.
	frgen3_0 $f wff ph $.
	frgen3_1 $f set x $.
	frgen3_2 $f set y $.
	frgen3_3 $f set z $.
	frgen3_4 $f class A $.
	frgen3_5 $f class B $.
	frgen3_6 $f class C $.
	ergen3_0 $e |- ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) $.
	rgen3 $p |- A. x e. A A. y e. B A. z e. C ph $= frgen3_0 frgen3_3 frgen3_6 wral frgen3_1 frgen3_2 frgen3_4 frgen3_5 frgen3_1 cv frgen3_4 wcel frgen3_2 cv frgen3_5 wcel wa frgen3_0 frgen3_3 frgen3_6 frgen3_1 cv frgen3_4 wcel frgen3_2 cv frgen3_5 wcel frgen3_3 cv frgen3_6 wcel frgen3_0 ergen3_0 3expa ralrimiva rgen2 $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 20-Nov-1994.) $)
${
	fr19.21bi_0 $f wff ph $.
	fr19.21bi_1 $f wff ps $.
	fr19.21bi_2 $f set x $.
	fr19.21bi_3 $f class A $.
	er19.21bi_0 $e |- ( ph -> A. x e. A ps ) $.
	r19.21bi $p |- ( ( ph /\ x e. A ) -> ps ) $= fr19.21bi_0 fr19.21bi_2 cv fr19.21bi_3 wcel fr19.21bi_1 fr19.21bi_0 fr19.21bi_2 cv fr19.21bi_3 wcel fr19.21bi_1 wi fr19.21bi_2 fr19.21bi_0 fr19.21bi_1 fr19.21bi_2 fr19.21bi_3 wral fr19.21bi_2 cv fr19.21bi_3 wcel fr19.21bi_1 wi fr19.21bi_2 wal er19.21bi_0 fr19.21bi_1 fr19.21bi_2 fr19.21bi_3 df-ral sylib 19.21bi imp $.
$}
$( Specialization rule for restricted quantification.  (Contributed by NM,
       20-Nov-1994.) $)
${
	frspec2_0 $f wff ph $.
	frspec2_1 $f set x $.
	frspec2_2 $f set y $.
	frspec2_3 $f class A $.
	frspec2_4 $f class B $.
	erspec2_0 $e |- A. x e. A A. y e. B ph $.
	rspec2 $p |- ( ( x e. A /\ y e. B ) -> ph ) $= frspec2_1 cv frspec2_3 wcel frspec2_0 frspec2_2 frspec2_4 frspec2_0 frspec2_2 frspec2_4 wral frspec2_1 frspec2_3 erspec2_0 rspec r19.21bi $.
$}
$( Specialization rule for restricted quantification.  (Contributed by NM,
       20-Nov-1994.) $)
${
	frspec3_0 $f wff ph $.
	frspec3_1 $f set x $.
	frspec3_2 $f set y $.
	frspec3_3 $f set z $.
	frspec3_4 $f class A $.
	frspec3_5 $f class B $.
	frspec3_6 $f class C $.
	erspec3_0 $e |- A. x e. A A. y e. B A. z e. C ph $.
	rspec3 $p |- ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) $= frspec3_1 cv frspec3_4 wcel frspec3_2 cv frspec3_5 wcel frspec3_3 cv frspec3_6 wcel frspec3_0 frspec3_1 cv frspec3_4 wcel frspec3_2 cv frspec3_5 wcel wa frspec3_0 frspec3_3 frspec3_6 frspec3_0 frspec3_3 frspec3_6 wral frspec3_1 frspec3_2 frspec3_4 frspec3_5 erspec3_0 rspec2 r19.21bi 3impa $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 21-Nov-1994.) $)
${
	fr19.21be_0 $f wff ph $.
	fr19.21be_1 $f wff ps $.
	fr19.21be_2 $f set x $.
	fr19.21be_3 $f class A $.
	er19.21be_0 $e |- ( ph -> A. x e. A ps ) $.
	r19.21be $p |- A. x e. A ( ph -> ps ) $= fr19.21be_0 fr19.21be_1 wi fr19.21be_2 fr19.21be_3 fr19.21be_0 fr19.21be_2 cv fr19.21be_3 wcel fr19.21be_1 fr19.21be_0 fr19.21be_1 fr19.21be_2 fr19.21be_3 er19.21be_0 r19.21bi expcom rgen $.
$}
$( Inference adding restricted existential quantifier to negated wff.
       (Contributed by NM, 16-Oct-2003.) $)
${
	fnrex_0 $f wff ps $.
	fnrex_1 $f set x $.
	fnrex_2 $f class A $.
	enrex_0 $e |- ( x e. A -> -. ps ) $.
	nrex $p |- -. E. x e. A ps $= fnrex_0 wn fnrex_1 fnrex_2 wral fnrex_0 fnrex_1 fnrex_2 wrex wn fnrex_0 wn fnrex_1 fnrex_2 enrex_0 rgen fnrex_0 fnrex_1 fnrex_2 ralnex mpbi $.
$}
$( Deduction adding restricted existential quantifier to negated wff.
       (Contributed by NM, 16-Oct-2003.) $)
${
	$d x ph $.
	fnrexdv_0 $f wff ph $.
	fnrexdv_1 $f wff ps $.
	fnrexdv_2 $f set x $.
	fnrexdv_3 $f class A $.
	enrexdv_0 $e |- ( ( ph /\ x e. A ) -> -. ps ) $.
	nrexdv $p |- ( ph -> -. E. x e. A ps ) $= fnrexdv_0 fnrexdv_1 wn fnrexdv_2 fnrexdv_3 wral fnrexdv_1 fnrexdv_2 fnrexdv_3 wrex wn fnrexdv_0 fnrexdv_1 wn fnrexdv_2 fnrexdv_3 enrexdv_0 ralrimiva fnrexdv_1 fnrexdv_2 fnrexdv_3 ralnex sylib $.
$}
$( Theorem 19.22 of [Margaris] p. 90.  (Restricted quantifier version.)
     (Contributed by NM, 22-Nov-1994.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)
${
	frexim_0 $f wff ph $.
	frexim_1 $f wff ps $.
	frexim_2 $f set x $.
	frexim_3 $f class A $.
	rexim $p |- ( A. x e. A ( ph -> ps ) -> ( E. x e. A ph -> E. x e. A ps ) ) $= frexim_0 frexim_1 wi frexim_2 frexim_3 wral frexim_0 wn frexim_2 frexim_3 wral wn frexim_1 wn frexim_2 frexim_3 wral wn frexim_0 frexim_2 frexim_3 wrex frexim_1 frexim_2 frexim_3 wrex frexim_0 frexim_1 wi frexim_2 frexim_3 wral frexim_1 wn frexim_2 frexim_3 wral frexim_0 wn frexim_2 frexim_3 wral frexim_0 frexim_1 wi frexim_1 wn frexim_0 wn frexim_2 frexim_3 frexim_0 frexim_1 con3 ral2imi con3d frexim_0 frexim_2 frexim_3 dfrex2 frexim_1 frexim_2 frexim_3 dfrex2 3imtr4g $.
$}
$( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 10-Feb-1997.) $)
${
	freximia_0 $f wff ph $.
	freximia_1 $f wff ps $.
	freximia_2 $f set x $.
	freximia_3 $f class A $.
	ereximia_0 $e |- ( x e. A -> ( ph -> ps ) ) $.
	reximia $p |- ( E. x e. A ph -> E. x e. A ps ) $= freximia_0 freximia_1 wi freximia_0 freximia_2 freximia_3 wrex freximia_1 freximia_2 freximia_3 wrex wi freximia_2 freximia_3 freximia_0 freximia_1 freximia_2 freximia_3 rexim ereximia_0 mprg $.
$}
$( Inference quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 8-Nov-2004.) $)
${
	freximi2_0 $f wff ph $.
	freximi2_1 $f wff ps $.
	freximi2_2 $f set x $.
	freximi2_3 $f class A $.
	freximi2_4 $f class B $.
	ereximi2_0 $e |- ( ( x e. A /\ ph ) -> ( x e. B /\ ps ) ) $.
	reximi2 $p |- ( E. x e. A ph -> E. x e. B ps ) $= freximi2_2 cv freximi2_3 wcel freximi2_0 wa freximi2_2 wex freximi2_2 cv freximi2_4 wcel freximi2_1 wa freximi2_2 wex freximi2_0 freximi2_2 freximi2_3 wrex freximi2_1 freximi2_2 freximi2_4 wrex freximi2_2 cv freximi2_3 wcel freximi2_0 wa freximi2_2 cv freximi2_4 wcel freximi2_1 wa freximi2_2 ereximi2_0 eximi freximi2_0 freximi2_2 freximi2_3 df-rex freximi2_1 freximi2_2 freximi2_4 df-rex 3imtr4i $.
$}
$( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 18-Oct-1996.) $)
${
	freximi_0 $f wff ph $.
	freximi_1 $f wff ps $.
	freximi_2 $f set x $.
	freximi_3 $f class A $.
	ereximi_0 $e |- ( ph -> ps ) $.
	reximi $p |- ( E. x e. A ph -> E. x e. A ps ) $= freximi_0 freximi_1 freximi_2 freximi_3 freximi_0 freximi_1 wi freximi_2 cv freximi_3 wcel ereximi_0 a1i reximia $.
$}
$( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 31-Aug-1999.) $)
${
	freximdai_0 $f wff ph $.
	freximdai_1 $f wff ps $.
	freximdai_2 $f wff ch $.
	freximdai_3 $f set x $.
	freximdai_4 $f class A $.
	ereximdai_0 $e |- F/ x ph $.
	ereximdai_1 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	reximdai $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $= freximdai_0 freximdai_1 freximdai_2 wi freximdai_3 freximdai_4 wral freximdai_1 freximdai_3 freximdai_4 wrex freximdai_2 freximdai_3 freximdai_4 wrex wi freximdai_0 freximdai_1 freximdai_2 wi freximdai_3 freximdai_4 ereximdai_0 ereximdai_1 ralrimi freximdai_1 freximdai_2 freximdai_3 freximdai_4 rexim syl $.
$}
$( Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 17-Sep-2003.) $)
${
	$d x ph $.
	freximdv2_0 $f wff ph $.
	freximdv2_1 $f wff ps $.
	freximdv2_2 $f wff ch $.
	freximdv2_3 $f set x $.
	freximdv2_4 $f class A $.
	freximdv2_5 $f class B $.
	ereximdv2_0 $e |- ( ph -> ( ( x e. A /\ ps ) -> ( x e. B /\ ch ) ) ) $.
	reximdv2 $p |- ( ph -> ( E. x e. A ps -> E. x e. B ch ) ) $= freximdv2_0 freximdv2_3 cv freximdv2_4 wcel freximdv2_1 wa freximdv2_3 wex freximdv2_3 cv freximdv2_5 wcel freximdv2_2 wa freximdv2_3 wex freximdv2_1 freximdv2_3 freximdv2_4 wrex freximdv2_2 freximdv2_3 freximdv2_5 wrex freximdv2_0 freximdv2_3 cv freximdv2_4 wcel freximdv2_1 wa freximdv2_3 cv freximdv2_5 wcel freximdv2_2 wa freximdv2_3 ereximdv2_0 eximdv freximdv2_1 freximdv2_3 freximdv2_4 df-rex freximdv2_2 freximdv2_3 freximdv2_5 df-rex 3imtr4g $.
$}
$( Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 14-Nov-2002.) $)
${
	$d x ph $.
	freximdvai_0 $f wff ph $.
	freximdvai_1 $f wff ps $.
	freximdvai_2 $f wff ch $.
	freximdvai_3 $f set x $.
	freximdvai_4 $f class A $.
	ereximdvai_0 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	reximdvai $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $= freximdvai_0 freximdvai_1 freximdvai_2 freximdvai_3 freximdvai_4 freximdvai_0 freximdvai_3 nfv ereximdvai_0 reximdai $.
$}
$( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Restricted
       quantifier version with strong hypothesis.)  (Contributed by NM,
       24-Jun-1998.) $)
${
	$d x ph $.
	freximdv_0 $f wff ph $.
	freximdv_1 $f wff ps $.
	freximdv_2 $f wff ch $.
	freximdv_3 $f set x $.
	freximdv_4 $f class A $.
	ereximdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	reximdv $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $= freximdv_0 freximdv_1 freximdv_2 freximdv_3 freximdv_4 freximdv_0 freximdv_1 freximdv_2 wi freximdv_3 cv freximdv_4 wcel ereximdv_0 a1d reximdvai $.
$}
$( Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 22-May-1999.) $)
${
	$d x ph $.
	freximdva_0 $f wff ph $.
	freximdva_1 $f wff ps $.
	freximdva_2 $f wff ch $.
	freximdva_3 $f set x $.
	freximdva_4 $f class A $.
	ereximdva_0 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	reximdva $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $= freximdva_0 freximdva_1 freximdva_2 freximdva_3 freximdva_4 freximdva_0 freximdva_3 cv freximdva_4 wcel freximdva_1 freximdva_2 wi ereximdva_0 ex reximdvai $.
$}
$( Theorem 19.12 of [Margaris] p. 89 with restricted quantifiers.
       (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)
${
	$d x y $.
	$d y A $.
	$d x B $.
	fr19.12_0 $f wff ph $.
	fr19.12_1 $f set x $.
	fr19.12_2 $f set y $.
	fr19.12_3 $f class A $.
	fr19.12_4 $f class B $.
	r19.12 $p |- ( E. x e. A A. y e. B ph -> A. y e. B E. x e. A ph ) $= fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_1 fr19.12_3 wrex fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_1 fr19.12_3 wrex fr19.12_2 fr19.12_4 wral fr19.12_0 fr19.12_1 fr19.12_3 wrex fr19.12_2 fr19.12_4 wral fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_1 fr19.12_3 wrex fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_1 fr19.12_3 wrex fr19.12_2 fr19.12_4 fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_2 fr19.12_1 fr19.12_3 fr19.12_2 fr19.12_3 nfcv fr19.12_0 fr19.12_2 fr19.12_4 nfra1 nfrex fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_1 fr19.12_3 wrex fr19.12_2 cv fr19.12_4 wcel ax-1 ralrimi fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_1 fr19.12_3 wrex fr19.12_0 fr19.12_1 fr19.12_3 wrex fr19.12_2 fr19.12_4 fr19.12_2 cv fr19.12_4 wcel fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_0 fr19.12_1 fr19.12_3 fr19.12_0 fr19.12_2 fr19.12_4 wral fr19.12_2 cv fr19.12_4 wcel fr19.12_0 fr19.12_0 fr19.12_2 fr19.12_4 rsp com12 reximdv ralimia syl $.
$}
$( Closed theorem form of ~ r19.23 .  (Contributed by NM, 4-Mar-2013.)
     (Revised by Mario Carneiro, 8-Oct-2016.) $)
${
	fr19.23t_0 $f wff ph $.
	fr19.23t_1 $f wff ps $.
	fr19.23t_2 $f set x $.
	fr19.23t_3 $f class A $.
	r19.23t $p |- ( F/ x ps -> ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) ) $= fr19.23t_1 fr19.23t_2 wnf fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 wa fr19.23t_1 wi fr19.23t_2 wal fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 wa fr19.23t_2 wex fr19.23t_1 wi fr19.23t_0 fr19.23t_1 wi fr19.23t_2 fr19.23t_3 wral fr19.23t_0 fr19.23t_2 fr19.23t_3 wrex fr19.23t_1 wi fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 wa fr19.23t_1 fr19.23t_2 19.23t fr19.23t_0 fr19.23t_1 wi fr19.23t_2 fr19.23t_3 wral fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 fr19.23t_1 wi wi fr19.23t_2 wal fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 wa fr19.23t_1 wi fr19.23t_2 wal fr19.23t_0 fr19.23t_1 wi fr19.23t_2 fr19.23t_3 df-ral fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 wa fr19.23t_1 wi fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 fr19.23t_1 wi wi fr19.23t_2 fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 fr19.23t_1 impexp albii bitr4i fr19.23t_0 fr19.23t_2 fr19.23t_3 wrex fr19.23t_2 cv fr19.23t_3 wcel fr19.23t_0 wa fr19.23t_2 wex fr19.23t_1 fr19.23t_0 fr19.23t_2 fr19.23t_3 df-rex imbi1i 3bitr4g $.
$}
$( Theorem 19.23 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 22-Oct-2010.)  (Proof shortened by Mario Carneiro,
       8-Oct-2016.) $)
${
	fr19.23_0 $f wff ph $.
	fr19.23_1 $f wff ps $.
	fr19.23_2 $f set x $.
	fr19.23_3 $f class A $.
	er19.23_0 $e |- F/ x ps $.
	r19.23 $p |- ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) $= fr19.23_1 fr19.23_2 wnf fr19.23_0 fr19.23_1 wi fr19.23_2 fr19.23_3 wral fr19.23_0 fr19.23_2 fr19.23_3 wrex fr19.23_1 wi wb er19.23_0 fr19.23_0 fr19.23_1 fr19.23_2 fr19.23_3 r19.23t ax-mp $.
$}
$( Theorem 19.23 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 31-Aug-1999.) $)
${
	$d x ps $.
	fr19.23v_0 $f wff ph $.
	fr19.23v_1 $f wff ps $.
	fr19.23v_2 $f set x $.
	fr19.23v_3 $f class A $.
	r19.23v $p |- ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) $= fr19.23v_0 fr19.23v_1 fr19.23v_2 fr19.23v_3 fr19.23v_1 fr19.23v_2 nfv r19.23 $.
$}
$( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 30-Nov-2003.)  (Proof
       shortened by Andrew Salmon, 30-May-2011.) $)
${
	frexlimi_0 $f wff ph $.
	frexlimi_1 $f wff ps $.
	frexlimi_2 $f set x $.
	frexlimi_3 $f class A $.
	erexlimi_0 $e |- F/ x ps $.
	erexlimi_1 $e |- ( x e. A -> ( ph -> ps ) ) $.
	rexlimi $p |- ( E. x e. A ph -> ps ) $= frexlimi_0 frexlimi_1 wi frexlimi_2 frexlimi_3 wral frexlimi_0 frexlimi_2 frexlimi_3 wrex frexlimi_1 wi frexlimi_0 frexlimi_1 wi frexlimi_2 frexlimi_3 erexlimi_1 rgen frexlimi_0 frexlimi_1 frexlimi_2 frexlimi_3 erexlimi_0 r19.23 mpbi $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 20-Nov-1994.) $)
${
	$d x ps $.
	frexlimiv_0 $f wff ph $.
	frexlimiv_1 $f wff ps $.
	frexlimiv_2 $f set x $.
	frexlimiv_3 $f class A $.
	erexlimiv_0 $e |- ( x e. A -> ( ph -> ps ) ) $.
	rexlimiv $p |- ( E. x e. A ph -> ps ) $= frexlimiv_0 frexlimiv_1 frexlimiv_2 frexlimiv_3 frexlimiv_1 frexlimiv_2 nfv erexlimiv_0 rexlimi $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 18-Dec-2006.) $)
${
	$d x ps $.
	frexlimiva_0 $f wff ph $.
	frexlimiva_1 $f wff ps $.
	frexlimiva_2 $f set x $.
	frexlimiva_3 $f class A $.
	erexlimiva_0 $e |- ( ( x e. A /\ ph ) -> ps ) $.
	rexlimiva $p |- ( E. x e. A ph -> ps ) $= frexlimiva_0 frexlimiva_1 frexlimiva_2 frexlimiva_3 frexlimiva_2 cv frexlimiva_3 wcel frexlimiva_0 frexlimiva_1 erexlimiva_0 ex rexlimiv $.
$}
$( Weaker version of ~ rexlimiv .  (Contributed by FL, 19-Sep-2011.) $)
${
	$d ps x $.
	frexlimivw_0 $f wff ph $.
	frexlimivw_1 $f wff ps $.
	frexlimivw_2 $f set x $.
	frexlimivw_3 $f class A $.
	erexlimivw_0 $e |- ( ph -> ps ) $.
	rexlimivw $p |- ( E. x e. A ph -> ps ) $= frexlimivw_0 frexlimivw_1 frexlimivw_2 frexlimivw_3 frexlimivw_0 frexlimivw_1 wi frexlimivw_2 cv frexlimivw_3 wcel erexlimivw_0 a1i rexlimiv $.
$}
$( Deduction from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 27-May-1998.)  (Proof shortened by Andrew
       Salmon, 30-May-2011.) $)
${
	frexlimd_0 $f wff ph $.
	frexlimd_1 $f wff ps $.
	frexlimd_2 $f wff ch $.
	frexlimd_3 $f set x $.
	frexlimd_4 $f class A $.
	erexlimd_0 $e |- F/ x ph $.
	erexlimd_1 $e |- F/ x ch $.
	erexlimd_2 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	rexlimd $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= frexlimd_0 frexlimd_1 frexlimd_2 wi frexlimd_3 frexlimd_4 wral frexlimd_1 frexlimd_3 frexlimd_4 wrex frexlimd_2 wi frexlimd_0 frexlimd_1 frexlimd_2 wi frexlimd_3 frexlimd_4 erexlimd_0 erexlimd_2 ralrimi frexlimd_1 frexlimd_2 frexlimd_3 frexlimd_4 erexlimd_1 r19.23 sylib $.
$}
$( Version of ~ rexlimd with deduction version of second hypothesis.
       (Contributed by NM, 21-Jul-2013.)  (Revised by Mario Carneiro,
       8-Oct-2016.) $)
${
	frexlimd2_0 $f wff ph $.
	frexlimd2_1 $f wff ps $.
	frexlimd2_2 $f wff ch $.
	frexlimd2_3 $f set x $.
	frexlimd2_4 $f class A $.
	erexlimd2_0 $e |- F/ x ph $.
	erexlimd2_1 $e |- ( ph -> F/ x ch ) $.
	erexlimd2_2 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	rexlimd2 $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= frexlimd2_0 frexlimd2_1 frexlimd2_2 wi frexlimd2_3 frexlimd2_4 wral frexlimd2_1 frexlimd2_3 frexlimd2_4 wrex frexlimd2_2 wi frexlimd2_0 frexlimd2_1 frexlimd2_2 wi frexlimd2_3 frexlimd2_4 erexlimd2_0 erexlimd2_2 ralrimi frexlimd2_0 frexlimd2_2 frexlimd2_3 wnf frexlimd2_1 frexlimd2_2 wi frexlimd2_3 frexlimd2_4 wral frexlimd2_1 frexlimd2_3 frexlimd2_4 wrex frexlimd2_2 wi wb erexlimd2_1 frexlimd2_1 frexlimd2_2 frexlimd2_3 frexlimd2_4 r19.23t syl mpbid $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 14-Nov-2002.)  (Proof shortened by Eric
       Schmidt, 22-Dec-2006.) $)
${
	$d x ph $.
	$d x ch $.
	frexlimdv_0 $f wff ph $.
	frexlimdv_1 $f wff ps $.
	frexlimdv_2 $f wff ch $.
	frexlimdv_3 $f set x $.
	frexlimdv_4 $f class A $.
	erexlimdv_0 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
	rexlimdv $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= frexlimdv_0 frexlimdv_1 frexlimdv_2 frexlimdv_3 frexlimdv_4 frexlimdv_0 frexlimdv_3 nfv frexlimdv_2 frexlimdv_3 nfv erexlimdv_0 rexlimd $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 20-Jan-2007.) $)
${
	$d x ph $.
	$d x ch $.
	frexlimdva_0 $f wff ph $.
	frexlimdva_1 $f wff ps $.
	frexlimdva_2 $f wff ch $.
	frexlimdva_3 $f set x $.
	frexlimdva_4 $f class A $.
	erexlimdva_0 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	rexlimdva $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= frexlimdva_0 frexlimdva_1 frexlimdva_2 frexlimdva_3 frexlimdva_4 frexlimdva_0 frexlimdva_3 cv frexlimdva_4 wcel frexlimdva_1 frexlimdva_2 wi erexlimdva_0 ex rexlimdv $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by Mario Carneiro, 15-Jun-2016.) $)
${
	$d x ph $.
	$d x ch $.
	frexlimdvaa_0 $f wff ph $.
	frexlimdvaa_1 $f wff ps $.
	frexlimdvaa_2 $f wff ch $.
	frexlimdvaa_3 $f set x $.
	frexlimdvaa_4 $f class A $.
	erexlimdvaa_0 $e |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch ) $.
	rexlimdvaa $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= frexlimdvaa_0 frexlimdvaa_1 frexlimdvaa_2 frexlimdvaa_3 frexlimdvaa_4 frexlimdvaa_0 frexlimdvaa_3 cv frexlimdvaa_4 wcel frexlimdvaa_1 frexlimdvaa_2 erexlimdvaa_0 expr rexlimdva $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  Frequently-used variant of ~ rexlimdv .  (Contributed by NM,
       7-Jun-2015.) $)
${
	$d x ph $.
	$d x ch $.
	frexlimdv3a_0 $f wff ph $.
	frexlimdv3a_1 $f wff ps $.
	frexlimdv3a_2 $f wff ch $.
	frexlimdv3a_3 $f set x $.
	frexlimdv3a_4 $f class A $.
	erexlimdv3a_0 $e |- ( ( ph /\ x e. A /\ ps ) -> ch ) $.
	rexlimdv3a $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= frexlimdv3a_0 frexlimdv3a_1 frexlimdv3a_2 frexlimdv3a_3 frexlimdv3a_4 frexlimdv3a_0 frexlimdv3a_3 cv frexlimdv3a_4 wcel frexlimdv3a_1 frexlimdv3a_2 erexlimdv3a_0 3exp rexlimdv $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 18-Jun-2014.) $)
${
	$d x ph $.
	$d x ch $.
	frexlimdvw_0 $f wff ph $.
	frexlimdvw_1 $f wff ps $.
	frexlimdvw_2 $f wff ch $.
	frexlimdvw_3 $f set x $.
	frexlimdvw_4 $f class A $.
	erexlimdvw_0 $e |- ( ph -> ( ps -> ch ) ) $.
	rexlimdvw $p |- ( ph -> ( E. x e. A ps -> ch ) ) $= frexlimdvw_0 frexlimdvw_1 frexlimdvw_2 frexlimdvw_3 frexlimdvw_4 frexlimdvw_0 frexlimdvw_1 frexlimdvw_2 wi frexlimdvw_3 cv frexlimdvw_4 wcel erexlimdvw_0 a1d rexlimdv $.
$}
$( Restricted existential elimination rule of natural deduction.
       (Contributed by Mario Carneiro, 15-Jun-2016.) $)
${
	$d x ph $.
	$d x ch $.
	frexlimddv_0 $f wff ph $.
	frexlimddv_1 $f wff ps $.
	frexlimddv_2 $f wff ch $.
	frexlimddv_3 $f set x $.
	frexlimddv_4 $f class A $.
	erexlimddv_0 $e |- ( ph -> E. x e. A ps ) $.
	erexlimddv_1 $e |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch ) $.
	rexlimddv $p |- ( ph -> ch ) $= frexlimddv_0 frexlimddv_1 frexlimddv_3 frexlimddv_4 wrex frexlimddv_2 erexlimddv_0 frexlimddv_0 frexlimddv_1 frexlimddv_2 frexlimddv_3 frexlimddv_4 erexlimddv_1 rexlimdvaa mpd $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 17-Feb-2004.) $)
${
	$d x y ps $.
	$d y A $.
	frexlimivv_0 $f wff ph $.
	frexlimivv_1 $f wff ps $.
	frexlimivv_2 $f set x $.
	frexlimivv_3 $f set y $.
	frexlimivv_4 $f class A $.
	frexlimivv_5 $f class B $.
	erexlimivv_0 $e |- ( ( x e. A /\ y e. B ) -> ( ph -> ps ) ) $.
	rexlimivv $p |- ( E. x e. A E. y e. B ph -> ps ) $= frexlimivv_0 frexlimivv_3 frexlimivv_5 wrex frexlimivv_1 frexlimivv_2 frexlimivv_4 frexlimivv_2 cv frexlimivv_4 wcel frexlimivv_0 frexlimivv_1 frexlimivv_3 frexlimivv_5 erexlimivv_0 rexlimdva rexlimiv $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 22-Jul-2004.) $)
${
	$d x y ph $.
	$d x y ch $.
	$d y A $.
	frexlimdvv_0 $f wff ph $.
	frexlimdvv_1 $f wff ps $.
	frexlimdvv_2 $f wff ch $.
	frexlimdvv_3 $f set x $.
	frexlimdvv_4 $f set y $.
	frexlimdvv_5 $f class A $.
	frexlimdvv_6 $f class B $.
	erexlimdvv_0 $e |- ( ph -> ( ( x e. A /\ y e. B ) -> ( ps -> ch ) ) ) $.
	rexlimdvv $p |- ( ph -> ( E. x e. A E. y e. B ps -> ch ) ) $= frexlimdvv_0 frexlimdvv_1 frexlimdvv_4 frexlimdvv_6 wrex frexlimdvv_2 frexlimdvv_3 frexlimdvv_5 frexlimdvv_0 frexlimdvv_3 cv frexlimdvv_5 wcel wa frexlimdvv_1 frexlimdvv_2 frexlimdvv_4 frexlimdvv_6 frexlimdvv_0 frexlimdvv_3 cv frexlimdvv_5 wcel frexlimdvv_4 cv frexlimdvv_6 wcel frexlimdvv_1 frexlimdvv_2 wi erexlimdvv_0 expdimp rexlimdv rexlimdva $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 18-Jun-2014.) $)
${
	$d x y ph $.
	$d x y ch $.
	$d y A $.
	frexlimdvva_0 $f wff ph $.
	frexlimdvva_1 $f wff ps $.
	frexlimdvva_2 $f wff ch $.
	frexlimdvva_3 $f set x $.
	frexlimdvva_4 $f set y $.
	frexlimdvva_5 $f class A $.
	frexlimdvva_6 $f class B $.
	erexlimdvva_0 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) ) $.
	rexlimdvva $p |- ( ph -> ( E. x e. A E. y e. B ps -> ch ) ) $= frexlimdvva_0 frexlimdvva_1 frexlimdvva_2 frexlimdvva_3 frexlimdvva_4 frexlimdvva_5 frexlimdvva_6 frexlimdvva_0 frexlimdvva_3 cv frexlimdvva_5 wcel frexlimdvva_4 cv frexlimdvva_6 wcel wa frexlimdvva_1 frexlimdvva_2 wi erexlimdvva_0 ex rexlimdvv $.
$}
$( Theorem 19.26 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by NM, 28-Jan-1997.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)
${
	fr19.26_0 $f wff ph $.
	fr19.26_1 $f wff ps $.
	fr19.26_2 $f set x $.
	fr19.26_3 $f class A $.
	r19.26 $p |- ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. x e. A ps ) ) $= fr19.26_0 fr19.26_1 wa fr19.26_2 fr19.26_3 wral fr19.26_0 fr19.26_2 fr19.26_3 wral fr19.26_1 fr19.26_2 fr19.26_3 wral wa fr19.26_0 fr19.26_1 wa fr19.26_2 fr19.26_3 wral fr19.26_0 fr19.26_2 fr19.26_3 wral fr19.26_1 fr19.26_2 fr19.26_3 wral fr19.26_0 fr19.26_1 wa fr19.26_0 fr19.26_2 fr19.26_3 fr19.26_0 fr19.26_1 simpl ralimi fr19.26_0 fr19.26_1 wa fr19.26_1 fr19.26_2 fr19.26_3 fr19.26_0 fr19.26_1 simpr ralimi jca fr19.26_0 fr19.26_2 fr19.26_3 wral fr19.26_1 fr19.26_2 fr19.26_3 wral fr19.26_0 fr19.26_1 wa fr19.26_2 fr19.26_3 wral fr19.26_0 fr19.26_1 fr19.26_0 fr19.26_1 wa fr19.26_2 fr19.26_3 fr19.26_0 fr19.26_1 pm3.2 ral2imi imp impbii $.
$}
$( Theorem 19.26 of [Margaris] p. 90 with 2 restricted quantifiers.
     (Contributed by NM, 10-Aug-2004.) $)
${
	fr19.26-2_0 $f wff ph $.
	fr19.26-2_1 $f wff ps $.
	fr19.26-2_2 $f set x $.
	fr19.26-2_3 $f set y $.
	fr19.26-2_4 $f class A $.
	fr19.26-2_5 $f class B $.
	r19.26-2 $p |- ( A. x e. A A. y e. B ( ph /\ ps ) <-> ( A. x e. A A. y e. B ph /\ A. x e. A A. y e. B ps ) ) $= fr19.26-2_0 fr19.26-2_1 wa fr19.26-2_3 fr19.26-2_5 wral fr19.26-2_2 fr19.26-2_4 wral fr19.26-2_0 fr19.26-2_3 fr19.26-2_5 wral fr19.26-2_1 fr19.26-2_3 fr19.26-2_5 wral wa fr19.26-2_2 fr19.26-2_4 wral fr19.26-2_0 fr19.26-2_3 fr19.26-2_5 wral fr19.26-2_2 fr19.26-2_4 wral fr19.26-2_1 fr19.26-2_3 fr19.26-2_5 wral fr19.26-2_2 fr19.26-2_4 wral wa fr19.26-2_0 fr19.26-2_1 wa fr19.26-2_3 fr19.26-2_5 wral fr19.26-2_0 fr19.26-2_3 fr19.26-2_5 wral fr19.26-2_1 fr19.26-2_3 fr19.26-2_5 wral wa fr19.26-2_2 fr19.26-2_4 fr19.26-2_0 fr19.26-2_1 fr19.26-2_3 fr19.26-2_5 r19.26 ralbii fr19.26-2_0 fr19.26-2_3 fr19.26-2_5 wral fr19.26-2_1 fr19.26-2_3 fr19.26-2_5 wral fr19.26-2_2 fr19.26-2_4 r19.26 bitri $.
$}
$( Theorem 19.26 of [Margaris] p. 90 with 3 restricted quantifiers.
     (Contributed by FL, 22-Nov-2010.) $)
${
	fr19.26-3_0 $f wff ph $.
	fr19.26-3_1 $f wff ps $.
	fr19.26-3_2 $f wff ch $.
	fr19.26-3_3 $f set x $.
	fr19.26-3_4 $f class A $.
	r19.26-3 $p |- ( A. x e. A ( ph /\ ps /\ ch ) <-> ( A. x e. A ph /\ A. x e. A ps /\ A. x e. A ch ) ) $= fr19.26-3_0 fr19.26-3_1 fr19.26-3_2 w3a fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_0 fr19.26-3_1 wa fr19.26-3_2 wa fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_0 fr19.26-3_1 wa fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_2 fr19.26-3_3 fr19.26-3_4 wral wa fr19.26-3_0 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_1 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_2 fr19.26-3_3 fr19.26-3_4 wral w3a fr19.26-3_0 fr19.26-3_1 fr19.26-3_2 w3a fr19.26-3_0 fr19.26-3_1 wa fr19.26-3_2 wa fr19.26-3_3 fr19.26-3_4 fr19.26-3_0 fr19.26-3_1 fr19.26-3_2 df-3an ralbii fr19.26-3_0 fr19.26-3_1 wa fr19.26-3_2 fr19.26-3_3 fr19.26-3_4 r19.26 fr19.26-3_0 fr19.26-3_1 wa fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_2 fr19.26-3_3 fr19.26-3_4 wral wa fr19.26-3_0 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_1 fr19.26-3_3 fr19.26-3_4 wral wa fr19.26-3_2 fr19.26-3_3 fr19.26-3_4 wral wa fr19.26-3_0 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_1 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_2 fr19.26-3_3 fr19.26-3_4 wral w3a fr19.26-3_0 fr19.26-3_1 wa fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_0 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_1 fr19.26-3_3 fr19.26-3_4 wral wa fr19.26-3_2 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_0 fr19.26-3_1 fr19.26-3_3 fr19.26-3_4 r19.26 anbi1i fr19.26-3_0 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_1 fr19.26-3_3 fr19.26-3_4 wral fr19.26-3_2 fr19.26-3_3 fr19.26-3_4 wral df-3an bitr4i 3bitri $.
$}
$( Theorem 19.26 of [Margaris] p. 90 with mixed quantifiers.  (Contributed by
     NM, 22-Feb-2004.) $)
${
	fr19.26m_0 $f wff ph $.
	fr19.26m_1 $f wff ps $.
	fr19.26m_2 $f set x $.
	fr19.26m_3 $f class A $.
	fr19.26m_4 $f class B $.
	r19.26m $p |- ( A. x ( ( x e. A -> ph ) /\ ( x e. B -> ps ) ) <-> ( A. x e. A ph /\ A. x e. B ps ) ) $= fr19.26m_2 cv fr19.26m_3 wcel fr19.26m_0 wi fr19.26m_2 cv fr19.26m_4 wcel fr19.26m_1 wi wa fr19.26m_2 wal fr19.26m_2 cv fr19.26m_3 wcel fr19.26m_0 wi fr19.26m_2 wal fr19.26m_2 cv fr19.26m_4 wcel fr19.26m_1 wi fr19.26m_2 wal wa fr19.26m_0 fr19.26m_2 fr19.26m_3 wral fr19.26m_1 fr19.26m_2 fr19.26m_4 wral wa fr19.26m_2 cv fr19.26m_3 wcel fr19.26m_0 wi fr19.26m_2 cv fr19.26m_4 wcel fr19.26m_1 wi fr19.26m_2 19.26 fr19.26m_0 fr19.26m_2 fr19.26m_3 wral fr19.26m_2 cv fr19.26m_3 wcel fr19.26m_0 wi fr19.26m_2 wal fr19.26m_1 fr19.26m_2 fr19.26m_4 wral fr19.26m_2 cv fr19.26m_4 wcel fr19.26m_1 wi fr19.26m_2 wal fr19.26m_0 fr19.26m_2 fr19.26m_3 df-ral fr19.26m_1 fr19.26m_2 fr19.26m_4 df-ral anbi12i bitr4i $.
$}
$( Distribute a restricted universal quantifier over a biconditional.
     Theorem 19.15 of [Margaris] p. 90 with restricted quantification.
     (Contributed by NM, 6-Oct-2003.) $)
${
	fralbi_0 $f wff ph $.
	fralbi_1 $f wff ps $.
	fralbi_2 $f set x $.
	fralbi_3 $f class A $.
	ralbi $p |- ( A. x e. A ( ph <-> ps ) -> ( A. x e. A ph <-> A. x e. A ps ) ) $= fralbi_0 fralbi_1 wb fralbi_2 fralbi_3 wral fralbi_0 fralbi_1 fralbi_2 fralbi_3 fralbi_0 fralbi_1 wb fralbi_2 fralbi_3 nfra1 fralbi_0 fralbi_1 wb fralbi_2 fralbi_3 wral fralbi_2 cv fralbi_3 wcel fralbi_0 fralbi_1 wb fralbi_0 fralbi_1 wb fralbi_2 fralbi_3 rsp imp ralbida $.
$}
$( Split a biconditional and distribute quantifier.  (Contributed by NM,
     3-Jun-2012.) $)
${
	fralbiim_0 $f wff ph $.
	fralbiim_1 $f wff ps $.
	fralbiim_2 $f set x $.
	fralbiim_3 $f class A $.
	ralbiim $p |- ( A. x e. A ( ph <-> ps ) <-> ( A. x e. A ( ph -> ps ) /\ A. x e. A ( ps -> ph ) ) ) $= fralbiim_0 fralbiim_1 wb fralbiim_2 fralbiim_3 wral fralbiim_0 fralbiim_1 wi fralbiim_1 fralbiim_0 wi wa fralbiim_2 fralbiim_3 wral fralbiim_0 fralbiim_1 wi fralbiim_2 fralbiim_3 wral fralbiim_1 fralbiim_0 wi fralbiim_2 fralbiim_3 wral wa fralbiim_0 fralbiim_1 wb fralbiim_0 fralbiim_1 wi fralbiim_1 fralbiim_0 wi wa fralbiim_2 fralbiim_3 fralbiim_0 fralbiim_1 dfbi2 ralbii fralbiim_0 fralbiim_1 wi fralbiim_1 fralbiim_0 wi fralbiim_2 fralbiim_3 r19.26 bitri $.
$}
$( Restricted version of one direction of Theorem 19.27 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 3-Jun-2004.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)
${
	$d x ps $.
	fr19.27av_0 $f wff ph $.
	fr19.27av_1 $f wff ps $.
	fr19.27av_2 $f set x $.
	fr19.27av_3 $f class A $.
	r19.27av $p |- ( ( A. x e. A ph /\ ps ) -> A. x e. A ( ph /\ ps ) ) $= fr19.27av_0 fr19.27av_2 fr19.27av_3 wral fr19.27av_1 wa fr19.27av_0 fr19.27av_2 fr19.27av_3 wral fr19.27av_1 fr19.27av_2 fr19.27av_3 wral wa fr19.27av_0 fr19.27av_1 wa fr19.27av_2 fr19.27av_3 wral fr19.27av_1 fr19.27av_1 fr19.27av_2 fr19.27av_3 wral fr19.27av_0 fr19.27av_2 fr19.27av_3 wral fr19.27av_1 fr19.27av_1 fr19.27av_2 fr19.27av_3 fr19.27av_1 fr19.27av_2 cv fr19.27av_3 wcel ax-1 ralrimiv anim2i fr19.27av_0 fr19.27av_1 fr19.27av_2 fr19.27av_3 r19.26 sylibr $.
$}
$( Restricted version of one direction of Theorem 19.28 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)
${
	$d x ph $.
	fr19.28av_0 $f wff ph $.
	fr19.28av_1 $f wff ps $.
	fr19.28av_2 $f set x $.
	fr19.28av_3 $f class A $.
	r19.28av $p |- ( ( ph /\ A. x e. A ps ) -> A. x e. A ( ph /\ ps ) ) $= fr19.28av_1 fr19.28av_2 fr19.28av_3 wral fr19.28av_0 wa fr19.28av_1 fr19.28av_0 wa fr19.28av_2 fr19.28av_3 wral fr19.28av_0 fr19.28av_1 fr19.28av_2 fr19.28av_3 wral wa fr19.28av_0 fr19.28av_1 wa fr19.28av_2 fr19.28av_3 wral fr19.28av_1 fr19.28av_0 fr19.28av_2 fr19.28av_3 r19.27av fr19.28av_0 fr19.28av_1 fr19.28av_2 fr19.28av_3 wral ancom fr19.28av_0 fr19.28av_1 wa fr19.28av_1 fr19.28av_0 wa fr19.28av_2 fr19.28av_3 fr19.28av_0 fr19.28av_1 ancom ralbii 3imtr4i $.
$}
$( Theorem 19.29 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by NM, 31-Aug-1999.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)
${
	fr19.29_0 $f wff ph $.
	fr19.29_1 $f wff ps $.
	fr19.29_2 $f set x $.
	fr19.29_3 $f class A $.
	r19.29 $p |- ( ( A. x e. A ph /\ E. x e. A ps ) -> E. x e. A ( ph /\ ps ) ) $= fr19.29_0 fr19.29_2 fr19.29_3 wral fr19.29_1 fr19.29_2 fr19.29_3 wrex fr19.29_0 fr19.29_1 wa fr19.29_2 fr19.29_3 wrex fr19.29_0 fr19.29_2 fr19.29_3 wral fr19.29_1 fr19.29_0 fr19.29_1 wa wi fr19.29_2 fr19.29_3 wral fr19.29_1 fr19.29_2 fr19.29_3 wrex fr19.29_0 fr19.29_1 wa fr19.29_2 fr19.29_3 wrex wi fr19.29_0 fr19.29_1 fr19.29_0 fr19.29_1 wa wi fr19.29_2 fr19.29_3 fr19.29_0 fr19.29_1 pm3.2 ralimi fr19.29_1 fr19.29_0 fr19.29_1 wa fr19.29_2 fr19.29_3 rexim syl imp $.
$}
$( Variation of Theorem 19.29 of [Margaris] p. 90 with restricted
     quantifiers.  (Contributed by NM, 31-Aug-1999.) $)
${
	fr19.29r_0 $f wff ph $.
	fr19.29r_1 $f wff ps $.
	fr19.29r_2 $f set x $.
	fr19.29r_3 $f class A $.
	r19.29r $p |- ( ( E. x e. A ph /\ A. x e. A ps ) -> E. x e. A ( ph /\ ps ) ) $= fr19.29r_1 fr19.29r_2 fr19.29r_3 wral fr19.29r_0 fr19.29r_2 fr19.29r_3 wrex wa fr19.29r_1 fr19.29r_0 wa fr19.29r_2 fr19.29r_3 wrex fr19.29r_0 fr19.29r_2 fr19.29r_3 wrex fr19.29r_1 fr19.29r_2 fr19.29r_3 wral wa fr19.29r_0 fr19.29r_1 wa fr19.29r_2 fr19.29r_3 wrex fr19.29r_1 fr19.29r_0 fr19.29r_2 fr19.29r_3 r19.29 fr19.29r_0 fr19.29r_2 fr19.29r_3 wrex fr19.29r_1 fr19.29r_2 fr19.29r_3 wral ancom fr19.29r_0 fr19.29r_1 wa fr19.29r_1 fr19.29r_0 wa fr19.29r_2 fr19.29r_3 fr19.29r_0 fr19.29r_1 ancom rexbii 3imtr4i $.
$}
$( Theorem 19.30 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by Scott Fenton, 25-Feb-2011.) $)
${
	fr19.30_0 $f wff ph $.
	fr19.30_1 $f wff ps $.
	fr19.30_2 $f set x $.
	fr19.30_3 $f class A $.
	r19.30 $p |- ( A. x e. A ( ph \/ ps ) -> ( A. x e. A ph \/ E. x e. A ps ) ) $= fr19.30_1 wn fr19.30_0 wi fr19.30_2 fr19.30_3 wral fr19.30_1 wn fr19.30_2 fr19.30_3 wral fr19.30_0 fr19.30_2 fr19.30_3 wral wi fr19.30_0 fr19.30_1 wo fr19.30_2 fr19.30_3 wral fr19.30_0 fr19.30_2 fr19.30_3 wral fr19.30_1 fr19.30_2 fr19.30_3 wrex wo fr19.30_1 wn fr19.30_0 fr19.30_2 fr19.30_3 ralim fr19.30_0 fr19.30_1 wo fr19.30_1 wn fr19.30_0 wi fr19.30_2 fr19.30_3 fr19.30_0 fr19.30_1 wo fr19.30_1 fr19.30_0 wo fr19.30_1 wn fr19.30_0 wi fr19.30_0 fr19.30_1 orcom fr19.30_1 fr19.30_0 df-or bitri ralbii fr19.30_0 fr19.30_2 fr19.30_3 wral fr19.30_1 wn fr19.30_2 fr19.30_3 wral wn wo fr19.30_1 wn fr19.30_2 fr19.30_3 wral wn fr19.30_0 fr19.30_2 fr19.30_3 wral wo fr19.30_0 fr19.30_2 fr19.30_3 wral fr19.30_1 fr19.30_2 fr19.30_3 wrex wo fr19.30_1 wn fr19.30_2 fr19.30_3 wral fr19.30_0 fr19.30_2 fr19.30_3 wral wi fr19.30_0 fr19.30_2 fr19.30_3 wral fr19.30_1 wn fr19.30_2 fr19.30_3 wral wn orcom fr19.30_1 fr19.30_2 fr19.30_3 wrex fr19.30_1 wn fr19.30_2 fr19.30_3 wral wn fr19.30_0 fr19.30_2 fr19.30_3 wral fr19.30_1 fr19.30_2 fr19.30_3 dfrex2 orbi2i fr19.30_1 wn fr19.30_2 fr19.30_3 wral fr19.30_0 fr19.30_2 fr19.30_3 wral imor 3bitr4i 3imtr4i $.
$}
$( Theorem 19.32 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 25-Nov-2003.) $)
${
	$d x ph $.
	fr19.32v_0 $f wff ph $.
	fr19.32v_1 $f wff ps $.
	fr19.32v_2 $f set x $.
	fr19.32v_3 $f class A $.
	r19.32v $p |- ( A. x e. A ( ph \/ ps ) <-> ( ph \/ A. x e. A ps ) ) $= fr19.32v_0 wn fr19.32v_1 wi fr19.32v_2 fr19.32v_3 wral fr19.32v_0 wn fr19.32v_1 fr19.32v_2 fr19.32v_3 wral wi fr19.32v_0 fr19.32v_1 wo fr19.32v_2 fr19.32v_3 wral fr19.32v_0 fr19.32v_1 fr19.32v_2 fr19.32v_3 wral wo fr19.32v_0 wn fr19.32v_1 fr19.32v_2 fr19.32v_3 r19.21v fr19.32v_0 fr19.32v_1 wo fr19.32v_0 wn fr19.32v_1 wi fr19.32v_2 fr19.32v_3 fr19.32v_0 fr19.32v_1 df-or ralbii fr19.32v_0 fr19.32v_1 fr19.32v_2 fr19.32v_3 wral df-or 3bitr4i $.
$}
$( Restricted quantifier version of Theorem 19.35 of [Margaris] p. 90.
     (Contributed by NM, 20-Sep-2003.) $)
${
	fr19.35_0 $f wff ph $.
	fr19.35_1 $f wff ps $.
	fr19.35_2 $f set x $.
	fr19.35_3 $f class A $.
	r19.35 $p |- ( E. x e. A ( ph -> ps ) <-> ( A. x e. A ph -> E. x e. A ps ) ) $= fr19.35_0 fr19.35_2 fr19.35_3 wral fr19.35_1 wn fr19.35_2 fr19.35_3 wral wn wi fr19.35_0 fr19.35_1 wi wn fr19.35_2 fr19.35_3 wral wn fr19.35_0 fr19.35_2 fr19.35_3 wral fr19.35_1 fr19.35_2 fr19.35_3 wrex wi fr19.35_0 fr19.35_1 wi fr19.35_2 fr19.35_3 wrex fr19.35_0 fr19.35_1 wi wn fr19.35_2 fr19.35_3 wral fr19.35_0 fr19.35_2 fr19.35_3 wral fr19.35_1 wn fr19.35_2 fr19.35_3 wral wn wi fr19.35_0 fr19.35_1 wn wa fr19.35_2 fr19.35_3 wral fr19.35_0 fr19.35_2 fr19.35_3 wral fr19.35_1 wn fr19.35_2 fr19.35_3 wral wa fr19.35_0 fr19.35_1 wi wn fr19.35_2 fr19.35_3 wral fr19.35_0 fr19.35_2 fr19.35_3 wral fr19.35_1 wn fr19.35_2 fr19.35_3 wral wn wi wn fr19.35_0 fr19.35_1 wn fr19.35_2 fr19.35_3 r19.26 fr19.35_0 fr19.35_1 wn wa fr19.35_0 fr19.35_1 wi wn fr19.35_2 fr19.35_3 fr19.35_0 fr19.35_1 annim ralbii fr19.35_0 fr19.35_2 fr19.35_3 wral fr19.35_1 wn fr19.35_2 fr19.35_3 wral df-an 3bitr3i con2bii fr19.35_1 fr19.35_2 fr19.35_3 wrex fr19.35_1 wn fr19.35_2 fr19.35_3 wral wn fr19.35_0 fr19.35_2 fr19.35_3 wral fr19.35_1 fr19.35_2 fr19.35_3 dfrex2 imbi2i fr19.35_0 fr19.35_1 wi fr19.35_2 fr19.35_3 dfrex2 3bitr4ri $.
$}
$( One direction of a restricted quantifier version of Theorem 19.36 of
       [Margaris] p. 90.  The other direction doesn't hold when ` A ` is
       empty.  (Contributed by NM, 22-Oct-2003.) $)
${
	$d x ps $.
	fr19.36av_0 $f wff ph $.
	fr19.36av_1 $f wff ps $.
	fr19.36av_2 $f set x $.
	fr19.36av_3 $f class A $.
	r19.36av $p |- ( E. x e. A ( ph -> ps ) -> ( A. x e. A ph -> ps ) ) $= fr19.36av_0 fr19.36av_1 wi fr19.36av_2 fr19.36av_3 wrex fr19.36av_0 fr19.36av_2 fr19.36av_3 wral fr19.36av_1 fr19.36av_2 fr19.36av_3 wrex wi fr19.36av_0 fr19.36av_2 fr19.36av_3 wral fr19.36av_1 wi fr19.36av_0 fr19.36av_1 fr19.36av_2 fr19.36av_3 r19.35 fr19.36av_1 fr19.36av_2 fr19.36av_3 wrex fr19.36av_1 fr19.36av_0 fr19.36av_2 fr19.36av_3 wral fr19.36av_1 fr19.36av_1 fr19.36av_2 fr19.36av_3 fr19.36av_2 cv fr19.36av_3 wcel fr19.36av_1 idd rexlimiv imim2i sylbi $.
$}
$( Restricted version of one direction of Theorem 19.37 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by FL, 13-May-2012.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
${
	fr19.37_0 $f wff ph $.
	fr19.37_1 $f wff ps $.
	fr19.37_2 $f set x $.
	fr19.37_3 $f class A $.
	er19.37_0 $e |- F/ x ph $.
	r19.37 $p |- ( E. x e. A ( ph -> ps ) -> ( ph -> E. x e. A ps ) ) $= fr19.37_0 fr19.37_1 wi fr19.37_2 fr19.37_3 wrex fr19.37_0 fr19.37_2 fr19.37_3 wral fr19.37_1 fr19.37_2 fr19.37_3 wrex wi fr19.37_0 fr19.37_1 fr19.37_2 fr19.37_3 wrex wi fr19.37_0 fr19.37_1 fr19.37_2 fr19.37_3 r19.35 fr19.37_0 fr19.37_0 fr19.37_2 fr19.37_3 wral fr19.37_1 fr19.37_2 fr19.37_3 wrex fr19.37_0 fr19.37_0 fr19.37_2 fr19.37_3 er19.37_0 fr19.37_0 fr19.37_2 cv fr19.37_3 wcel ax-1 ralrimi imim1i sylbi $.
$}
$( Restricted version of one direction of Theorem 19.37 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)
${
	$d x ph $.
	fr19.37av_0 $f wff ph $.
	fr19.37av_1 $f wff ps $.
	fr19.37av_2 $f set x $.
	fr19.37av_3 $f class A $.
	r19.37av $p |- ( E. x e. A ( ph -> ps ) -> ( ph -> E. x e. A ps ) ) $= fr19.37av_0 fr19.37av_1 fr19.37av_2 fr19.37av_3 fr19.37av_0 fr19.37av_2 nfv r19.37 $.
$}
$( Restricted quantifier version of Theorem 19.40 of [Margaris] p. 90.
     (Contributed by NM, 2-Apr-2004.) $)
${
	fr19.40_0 $f wff ph $.
	fr19.40_1 $f wff ps $.
	fr19.40_2 $f set x $.
	fr19.40_3 $f class A $.
	r19.40 $p |- ( E. x e. A ( ph /\ ps ) -> ( E. x e. A ph /\ E. x e. A ps ) ) $= fr19.40_0 fr19.40_1 wa fr19.40_2 fr19.40_3 wrex fr19.40_0 fr19.40_2 fr19.40_3 wrex fr19.40_1 fr19.40_2 fr19.40_3 wrex fr19.40_0 fr19.40_1 wa fr19.40_0 fr19.40_2 fr19.40_3 fr19.40_0 fr19.40_1 simpl reximi fr19.40_0 fr19.40_1 wa fr19.40_1 fr19.40_2 fr19.40_3 fr19.40_0 fr19.40_1 simpr reximi jca $.
$}
$( Restricted quantifier version of Theorem 19.41 of [Margaris] p. 90.
       (Contributed by NM, 1-Nov-2010.) $)
${
	fr19.41_0 $f wff ph $.
	fr19.41_1 $f wff ps $.
	fr19.41_2 $f set x $.
	fr19.41_3 $f class A $.
	er19.41_0 $e |- F/ x ps $.
	r19.41 $p |- ( E. x e. A ( ph /\ ps ) <-> ( E. x e. A ph /\ ps ) ) $= fr19.41_2 cv fr19.41_3 wcel fr19.41_0 fr19.41_1 wa wa fr19.41_2 wex fr19.41_2 cv fr19.41_3 wcel fr19.41_0 wa fr19.41_2 wex fr19.41_1 wa fr19.41_0 fr19.41_1 wa fr19.41_2 fr19.41_3 wrex fr19.41_0 fr19.41_2 fr19.41_3 wrex fr19.41_1 wa fr19.41_2 cv fr19.41_3 wcel fr19.41_0 fr19.41_1 wa wa fr19.41_2 wex fr19.41_2 cv fr19.41_3 wcel fr19.41_0 wa fr19.41_1 wa fr19.41_2 wex fr19.41_2 cv fr19.41_3 wcel fr19.41_0 wa fr19.41_2 wex fr19.41_1 wa fr19.41_2 cv fr19.41_3 wcel fr19.41_0 wa fr19.41_1 wa fr19.41_2 cv fr19.41_3 wcel fr19.41_0 fr19.41_1 wa wa fr19.41_2 fr19.41_2 cv fr19.41_3 wcel fr19.41_0 fr19.41_1 anass exbii fr19.41_2 cv fr19.41_3 wcel fr19.41_0 wa fr19.41_1 fr19.41_2 er19.41_0 19.41 bitr3i fr19.41_0 fr19.41_1 wa fr19.41_2 fr19.41_3 df-rex fr19.41_0 fr19.41_2 fr19.41_3 wrex fr19.41_2 cv fr19.41_3 wcel fr19.41_0 wa fr19.41_2 wex fr19.41_1 fr19.41_0 fr19.41_2 fr19.41_3 df-rex anbi1i 3bitr4i $.
$}
$( Restricted quantifier version of Theorem 19.41 of [Margaris] p. 90.
       (Contributed by NM, 17-Dec-2003.) $)
${
	$d x ps $.
	fr19.41v_0 $f wff ph $.
	fr19.41v_1 $f wff ps $.
	fr19.41v_2 $f set x $.
	fr19.41v_3 $f class A $.
	r19.41v $p |- ( E. x e. A ( ph /\ ps ) <-> ( E. x e. A ph /\ ps ) ) $= fr19.41v_0 fr19.41v_1 fr19.41v_2 fr19.41v_3 fr19.41v_1 fr19.41v_2 nfv r19.41 $.
$}
$( Restricted version of Theorem 19.42 of [Margaris] p. 90.  (Contributed
       by NM, 27-May-1998.) $)
${
	$d x ph $.
	fr19.42v_0 $f wff ph $.
	fr19.42v_1 $f wff ps $.
	fr19.42v_2 $f set x $.
	fr19.42v_3 $f class A $.
	r19.42v $p |- ( E. x e. A ( ph /\ ps ) <-> ( ph /\ E. x e. A ps ) ) $= fr19.42v_1 fr19.42v_0 wa fr19.42v_2 fr19.42v_3 wrex fr19.42v_1 fr19.42v_2 fr19.42v_3 wrex fr19.42v_0 wa fr19.42v_0 fr19.42v_1 wa fr19.42v_2 fr19.42v_3 wrex fr19.42v_0 fr19.42v_1 fr19.42v_2 fr19.42v_3 wrex wa fr19.42v_1 fr19.42v_0 fr19.42v_2 fr19.42v_3 r19.41v fr19.42v_0 fr19.42v_1 wa fr19.42v_1 fr19.42v_0 wa fr19.42v_2 fr19.42v_3 fr19.42v_0 fr19.42v_1 ancom rexbii fr19.42v_0 fr19.42v_1 fr19.42v_2 fr19.42v_3 wrex ancom 3bitr4i $.
$}
$( Restricted version of Theorem 19.43 of [Margaris] p. 90.  (Contributed by
     NM, 27-May-1998.)  (Proof shortened by Andrew Salmon, 30-May-2011.) $)
${
	fr19.43_0 $f wff ph $.
	fr19.43_1 $f wff ps $.
	fr19.43_2 $f set x $.
	fr19.43_3 $f class A $.
	r19.43 $p |- ( E. x e. A ( ph \/ ps ) <-> ( E. x e. A ph \/ E. x e. A ps ) ) $= fr19.43_0 wn fr19.43_1 wi fr19.43_2 fr19.43_3 wrex fr19.43_0 wn fr19.43_2 fr19.43_3 wral fr19.43_1 fr19.43_2 fr19.43_3 wrex wi fr19.43_0 fr19.43_1 wo fr19.43_2 fr19.43_3 wrex fr19.43_0 fr19.43_2 fr19.43_3 wrex fr19.43_1 fr19.43_2 fr19.43_3 wrex wo fr19.43_0 wn fr19.43_1 fr19.43_2 fr19.43_3 r19.35 fr19.43_0 fr19.43_1 wo fr19.43_0 wn fr19.43_1 wi fr19.43_2 fr19.43_3 fr19.43_0 fr19.43_1 df-or rexbii fr19.43_0 fr19.43_2 fr19.43_3 wrex fr19.43_1 fr19.43_2 fr19.43_3 wrex wo fr19.43_0 fr19.43_2 fr19.43_3 wrex wn fr19.43_1 fr19.43_2 fr19.43_3 wrex wi fr19.43_0 wn fr19.43_2 fr19.43_3 wral fr19.43_1 fr19.43_2 fr19.43_3 wrex wi fr19.43_0 fr19.43_2 fr19.43_3 wrex fr19.43_1 fr19.43_2 fr19.43_3 wrex df-or fr19.43_0 wn fr19.43_2 fr19.43_3 wral fr19.43_0 fr19.43_2 fr19.43_3 wrex wn fr19.43_1 fr19.43_2 fr19.43_3 wrex fr19.43_0 fr19.43_2 fr19.43_3 ralnex imbi1i bitr4i 3bitr4i $.
$}
$( One direction of a restricted quantifier version of Theorem 19.44 of
       [Margaris] p. 90.  The other direction doesn't hold when ` A ` is
       empty.  (Contributed by NM, 2-Apr-2004.) $)
${
	$d x ps $.
	fr19.44av_0 $f wff ph $.
	fr19.44av_1 $f wff ps $.
	fr19.44av_2 $f set x $.
	fr19.44av_3 $f class A $.
	r19.44av $p |- ( E. x e. A ( ph \/ ps ) -> ( E. x e. A ph \/ ps ) ) $= fr19.44av_0 fr19.44av_1 wo fr19.44av_2 fr19.44av_3 wrex fr19.44av_0 fr19.44av_2 fr19.44av_3 wrex fr19.44av_1 fr19.44av_2 fr19.44av_3 wrex wo fr19.44av_0 fr19.44av_2 fr19.44av_3 wrex fr19.44av_1 wo fr19.44av_0 fr19.44av_1 fr19.44av_2 fr19.44av_3 r19.43 fr19.44av_1 fr19.44av_2 fr19.44av_3 wrex fr19.44av_1 fr19.44av_0 fr19.44av_2 fr19.44av_3 wrex fr19.44av_1 fr19.44av_1 fr19.44av_2 fr19.44av_3 fr19.44av_2 cv fr19.44av_3 wcel fr19.44av_1 idd rexlimiv orim2i sylbi $.
$}
$( Restricted version of one direction of Theorem 19.45 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)
${
	$d x ph $.
	fr19.45av_0 $f wff ph $.
	fr19.45av_1 $f wff ps $.
	fr19.45av_2 $f set x $.
	fr19.45av_3 $f class A $.
	r19.45av $p |- ( E. x e. A ( ph \/ ps ) -> ( ph \/ E. x e. A ps ) ) $= fr19.45av_0 fr19.45av_1 wo fr19.45av_2 fr19.45av_3 wrex fr19.45av_0 fr19.45av_2 fr19.45av_3 wrex fr19.45av_1 fr19.45av_2 fr19.45av_3 wrex wo fr19.45av_0 fr19.45av_1 fr19.45av_2 fr19.45av_3 wrex wo fr19.45av_0 fr19.45av_1 fr19.45av_2 fr19.45av_3 r19.43 fr19.45av_0 fr19.45av_2 fr19.45av_3 wrex fr19.45av_0 fr19.45av_1 fr19.45av_2 fr19.45av_3 wrex fr19.45av_0 fr19.45av_0 fr19.45av_2 fr19.45av_3 fr19.45av_2 cv fr19.45av_3 wcel fr19.45av_0 idd rexlimiv orim1i sylbi $.
$}
$( Commutation of restricted quantifiers.  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)
${
	$d x y $.
	fralcomf_0 $f wff ph $.
	fralcomf_1 $f set x $.
	fralcomf_2 $f set y $.
	fralcomf_3 $f class A $.
	fralcomf_4 $f class B $.
	eralcomf_0 $e |- F/_ y A $.
	eralcomf_1 $e |- F/_ x B $.
	ralcomf $p |- ( A. x e. A A. y e. B ph <-> A. y e. B A. x e. A ph ) $= fralcomf_1 cv fralcomf_3 wcel fralcomf_2 cv fralcomf_4 wcel wa fralcomf_0 wi fralcomf_2 wal fralcomf_1 wal fralcomf_2 cv fralcomf_4 wcel fralcomf_1 cv fralcomf_3 wcel wa fralcomf_0 wi fralcomf_1 wal fralcomf_2 wal fralcomf_0 fralcomf_2 fralcomf_4 wral fralcomf_1 fralcomf_3 wral fralcomf_0 fralcomf_1 fralcomf_3 wral fralcomf_2 fralcomf_4 wral fralcomf_1 cv fralcomf_3 wcel fralcomf_2 cv fralcomf_4 wcel wa fralcomf_0 wi fralcomf_2 wal fralcomf_1 wal fralcomf_2 cv fralcomf_4 wcel fralcomf_1 cv fralcomf_3 wcel wa fralcomf_0 wi fralcomf_2 wal fralcomf_1 wal fralcomf_2 cv fralcomf_4 wcel fralcomf_1 cv fralcomf_3 wcel wa fralcomf_0 wi fralcomf_1 wal fralcomf_2 wal fralcomf_1 cv fralcomf_3 wcel fralcomf_2 cv fralcomf_4 wcel wa fralcomf_0 wi fralcomf_2 cv fralcomf_4 wcel fralcomf_1 cv fralcomf_3 wcel wa fralcomf_0 wi fralcomf_1 fralcomf_2 fralcomf_1 cv fralcomf_3 wcel fralcomf_2 cv fralcomf_4 wcel fralcomf_0 ancomsimp 2albii fralcomf_2 cv fralcomf_4 wcel fralcomf_1 cv fralcomf_3 wcel wa fralcomf_0 wi fralcomf_1 fralcomf_2 alcom bitri fralcomf_0 fralcomf_1 fralcomf_2 fralcomf_3 fralcomf_4 eralcomf_0 r2alf fralcomf_0 fralcomf_2 fralcomf_1 fralcomf_4 fralcomf_3 eralcomf_1 r2alf 3bitr4i $.
$}
$( Commutation of restricted quantifiers.  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)
${
	$d x y $.
	frexcomf_0 $f wff ph $.
	frexcomf_1 $f set x $.
	frexcomf_2 $f set y $.
	frexcomf_3 $f class A $.
	frexcomf_4 $f class B $.
	erexcomf_0 $e |- F/_ y A $.
	erexcomf_1 $e |- F/_ x B $.
	rexcomf $p |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph ) $= frexcomf_1 cv frexcomf_3 wcel frexcomf_2 cv frexcomf_4 wcel wa frexcomf_0 wa frexcomf_2 wex frexcomf_1 wex frexcomf_2 cv frexcomf_4 wcel frexcomf_1 cv frexcomf_3 wcel wa frexcomf_0 wa frexcomf_1 wex frexcomf_2 wex frexcomf_0 frexcomf_2 frexcomf_4 wrex frexcomf_1 frexcomf_3 wrex frexcomf_0 frexcomf_1 frexcomf_3 wrex frexcomf_2 frexcomf_4 wrex frexcomf_1 cv frexcomf_3 wcel frexcomf_2 cv frexcomf_4 wcel wa frexcomf_0 wa frexcomf_2 wex frexcomf_1 wex frexcomf_2 cv frexcomf_4 wcel frexcomf_1 cv frexcomf_3 wcel wa frexcomf_0 wa frexcomf_2 wex frexcomf_1 wex frexcomf_2 cv frexcomf_4 wcel frexcomf_1 cv frexcomf_3 wcel wa frexcomf_0 wa frexcomf_1 wex frexcomf_2 wex frexcomf_1 cv frexcomf_3 wcel frexcomf_2 cv frexcomf_4 wcel wa frexcomf_0 wa frexcomf_2 cv frexcomf_4 wcel frexcomf_1 cv frexcomf_3 wcel wa frexcomf_0 wa frexcomf_1 frexcomf_2 frexcomf_1 cv frexcomf_3 wcel frexcomf_2 cv frexcomf_4 wcel wa frexcomf_2 cv frexcomf_4 wcel frexcomf_1 cv frexcomf_3 wcel wa frexcomf_0 frexcomf_1 cv frexcomf_3 wcel frexcomf_2 cv frexcomf_4 wcel ancom anbi1i 2exbii frexcomf_2 cv frexcomf_4 wcel frexcomf_1 cv frexcomf_3 wcel wa frexcomf_0 wa frexcomf_1 frexcomf_2 excom bitri frexcomf_0 frexcomf_1 frexcomf_2 frexcomf_3 frexcomf_4 erexcomf_0 r2exf frexcomf_0 frexcomf_2 frexcomf_1 frexcomf_4 frexcomf_3 erexcomf_1 r2exf 3bitr4i $.
$}
$( Commutation of restricted quantifiers.  (Contributed by NM,
       13-Oct-1999.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
${
	$d x y $.
	$d x B $.
	$d y A $.
	fralcom_0 $f wff ph $.
	fralcom_1 $f set x $.
	fralcom_2 $f set y $.
	fralcom_3 $f class A $.
	fralcom_4 $f class B $.
	ralcom $p |- ( A. x e. A A. y e. B ph <-> A. y e. B A. x e. A ph ) $= fralcom_0 fralcom_1 fralcom_2 fralcom_3 fralcom_4 fralcom_2 fralcom_3 nfcv fralcom_1 fralcom_4 nfcv ralcomf $.
$}
$( Commutation of restricted quantifiers.  (Contributed by NM,
       19-Nov-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
${
	$d x y $.
	$d x B $.
	$d y A $.
	frexcom_0 $f wff ph $.
	frexcom_1 $f set x $.
	frexcom_2 $f set y $.
	frexcom_3 $f class A $.
	frexcom_4 $f class B $.
	rexcom $p |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph ) $= frexcom_0 frexcom_1 frexcom_2 frexcom_3 frexcom_4 frexcom_2 frexcom_3 nfcv frexcom_1 frexcom_4 nfcv rexcomf $.
$}
$( Swap 1st and 3rd restricted existential quantifiers.  (Contributed by
       NM, 8-Apr-2015.) $)
${
	$d y z A $.
	$d x z B $.
	$d x y C $.
	frexcom13_0 $f wff ph $.
	frexcom13_1 $f set x $.
	frexcom13_2 $f set y $.
	frexcom13_3 $f set z $.
	frexcom13_4 $f class A $.
	frexcom13_5 $f class B $.
	frexcom13_6 $f class C $.
	rexcom13 $p |- ( E. x e. A E. y e. B E. z e. C ph <-> E. z e. C E. y e. B E. x e. A ph ) $= frexcom13_0 frexcom13_3 frexcom13_6 wrex frexcom13_2 frexcom13_5 wrex frexcom13_1 frexcom13_4 wrex frexcom13_0 frexcom13_3 frexcom13_6 wrex frexcom13_1 frexcom13_4 wrex frexcom13_2 frexcom13_5 wrex frexcom13_0 frexcom13_1 frexcom13_4 wrex frexcom13_3 frexcom13_6 wrex frexcom13_2 frexcom13_5 wrex frexcom13_0 frexcom13_1 frexcom13_4 wrex frexcom13_2 frexcom13_5 wrex frexcom13_3 frexcom13_6 wrex frexcom13_0 frexcom13_3 frexcom13_6 wrex frexcom13_1 frexcom13_2 frexcom13_4 frexcom13_5 rexcom frexcom13_0 frexcom13_3 frexcom13_6 wrex frexcom13_1 frexcom13_4 wrex frexcom13_0 frexcom13_1 frexcom13_4 wrex frexcom13_3 frexcom13_6 wrex frexcom13_2 frexcom13_5 frexcom13_0 frexcom13_1 frexcom13_3 frexcom13_4 frexcom13_6 rexcom rexbii frexcom13_0 frexcom13_1 frexcom13_4 wrex frexcom13_2 frexcom13_3 frexcom13_5 frexcom13_6 rexcom 3bitri $.
$}
$( Rotate existential restricted quantifiers twice.  (Contributed by NM,
       8-Apr-2015.) $)
${
	$d w z A $.
	$d w z B $.
	$d w x y C $.
	$d x y z D $.
	frexrot4_0 $f wff ph $.
	frexrot4_1 $f set x $.
	frexrot4_2 $f set y $.
	frexrot4_3 $f set z $.
	frexrot4_4 $f set w $.
	frexrot4_5 $f class A $.
	frexrot4_6 $f class B $.
	frexrot4_7 $f class C $.
	frexrot4_8 $f class D $.
	rexrot4 $p |- ( E. x e. A E. y e. B E. z e. C E. w e. D ph <-> E. z e. C E. w e. D E. x e. A E. y e. B ph ) $= frexrot4_0 frexrot4_4 frexrot4_8 wrex frexrot4_3 frexrot4_7 wrex frexrot4_2 frexrot4_6 wrex frexrot4_1 frexrot4_5 wrex frexrot4_0 frexrot4_2 frexrot4_6 wrex frexrot4_3 frexrot4_7 wrex frexrot4_4 frexrot4_8 wrex frexrot4_1 frexrot4_5 wrex frexrot4_0 frexrot4_2 frexrot4_6 wrex frexrot4_1 frexrot4_5 wrex frexrot4_4 frexrot4_8 wrex frexrot4_3 frexrot4_7 wrex frexrot4_0 frexrot4_4 frexrot4_8 wrex frexrot4_3 frexrot4_7 wrex frexrot4_2 frexrot4_6 wrex frexrot4_0 frexrot4_2 frexrot4_6 wrex frexrot4_3 frexrot4_7 wrex frexrot4_4 frexrot4_8 wrex frexrot4_1 frexrot4_5 frexrot4_0 frexrot4_2 frexrot4_3 frexrot4_4 frexrot4_6 frexrot4_7 frexrot4_8 rexcom13 rexbii frexrot4_0 frexrot4_2 frexrot4_6 wrex frexrot4_1 frexrot4_4 frexrot4_3 frexrot4_5 frexrot4_8 frexrot4_7 rexcom13 bitri $.
$}
$( Commutation of restricted quantifiers.  Note that ` x ` and ` y `
       needn't be distinct (this makes the proof longer).  (Contributed by NM,
       24-Nov-1994.)  (Proof shortened by Mario Carneiro, 17-Oct-2016.) $)
${
	$d y A $.
	$d x A $.
	fralcom2_0 $f wff ph $.
	fralcom2_1 $f set x $.
	fralcom2_2 $f set y $.
	fralcom2_3 $f class A $.
	ralcom2 $p |- ( A. x e. A A. y e. A ph -> A. y e. A A. x e. A ph ) $= fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_2 fralcom2_3 wral wi fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_2 fralcom2_3 wral fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal fralcom2_1 cv fralcom2_3 wcel fralcom2_0 fralcom2_2 fralcom2_3 wral wi fralcom2_1 wal fralcom2_2 cv fralcom2_3 wcel fralcom2_0 fralcom2_1 fralcom2_3 wral wi fralcom2_2 wal fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_2 fralcom2_3 wral fralcom2_1 cv fralcom2_3 wcel fralcom2_0 fralcom2_2 fralcom2_3 wral wi fralcom2_2 cv fralcom2_3 wcel fralcom2_0 fralcom2_1 fralcom2_3 wral wi fralcom2_1 fralcom2_2 fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal fralcom2_1 cv fralcom2_3 wcel fralcom2_2 cv fralcom2_3 wcel fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 cv fralcom2_3 wcel fralcom2_2 cv fralcom2_3 wcel wb fralcom2_1 fralcom2_1 cv fralcom2_2 cv fralcom2_3 eleq1 sps fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal fralcom2_2 cv fralcom2_3 wcel fralcom2_0 wi fralcom2_2 wal fralcom2_1 cv fralcom2_3 wcel fralcom2_0 wi fralcom2_1 wal fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal fralcom2_1 cv fralcom2_3 wcel fralcom2_0 wi fralcom2_1 wal fralcom2_2 cv fralcom2_3 wcel fralcom2_0 wi fralcom2_2 wal fralcom2_1 cv fralcom2_3 wcel fralcom2_0 wi fralcom2_2 cv fralcom2_3 wcel fralcom2_0 wi fralcom2_1 fralcom2_2 fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal fralcom2_1 cv fralcom2_3 wcel fralcom2_2 cv fralcom2_3 wcel fralcom2_0 fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 cv fralcom2_3 wcel fralcom2_2 cv fralcom2_3 wcel wb fralcom2_1 fralcom2_1 cv fralcom2_2 cv fralcom2_3 eleq1 sps imbi1d dral1 bicomd fralcom2_0 fralcom2_2 fralcom2_3 df-ral fralcom2_0 fralcom2_1 fralcom2_3 df-ral 3bitr4g imbi12d dral1 fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 df-ral fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_2 fralcom2_3 df-ral 3bitr4g biimpd fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_2 fralcom2_3 wral fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral wa fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_2 fralcom2_3 fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_2 fralcom2_1 fralcom2_2 fralcom2_2 nfnae fralcom2_0 fralcom2_1 fralcom2_2 fralcom2_3 fralcom2_3 nfra2 nfan fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral wa fralcom2_2 cv fralcom2_3 wcel fralcom2_0 fralcom2_1 fralcom2_3 wral fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral wa fralcom2_2 cv fralcom2_3 wcel wa fralcom2_0 fralcom2_1 fralcom2_3 fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral wa fralcom2_2 cv fralcom2_3 wcel fralcom2_1 fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_1 fralcom2_1 fralcom2_2 fralcom2_1 nfnae fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 nfra1 nfan fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral wa fralcom2_1 fralcom2_2 cv fralcom2_3 fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_1 fralcom2_2 cv wnfc fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_1 fralcom2_2 nfcvf adantr fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral wa fralcom2_1 fralcom2_3 nfcvd nfeld nfan1 fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_2 cv fralcom2_3 wcel fralcom2_1 cv fralcom2_3 wcel fralcom2_0 wi fralcom2_1 cv fralcom2_2 cv wceq fralcom2_1 wal wn fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_2 cv fralcom2_3 wcel fralcom2_1 cv fralcom2_3 wcel fralcom2_0 fralcom2_0 fralcom2_2 fralcom2_3 wral fralcom2_1 fralcom2_3 wral fralcom2_1 cv fralcom2_3 wcel fralcom2_2 cv fralcom2_3 wcel fralcom2_0 fralcom2_0 fralcom2_1 fralcom2_2 fralcom2_3 fralcom2_3 rsp2 ancomsd expdimp adantll ralrimi ex ralrimi ex pm2.61i $.
$}
$( A commutative law for restricted quantifiers that swaps the domain of
       the restriction.  (Contributed by NM, 22-Feb-2004.) $)
${
	fralcom3_0 $f wff ph $.
	fralcom3_1 $f set x $.
	fralcom3_2 $f class A $.
	fralcom3_3 $f class B $.
	ralcom3 $p |- ( A. x e. A ( x e. B -> ph ) <-> A. x e. B ( x e. A -> ph ) ) $= fralcom3_1 cv fralcom3_3 wcel fralcom3_0 wi fralcom3_1 fralcom3_2 wral fralcom3_1 cv fralcom3_2 wcel fralcom3_0 wi fralcom3_1 fralcom3_3 wral fralcom3_1 cv fralcom3_3 wcel fralcom3_0 wi fralcom3_1 cv fralcom3_2 wcel fralcom3_0 wi fralcom3_1 fralcom3_2 fralcom3_3 fralcom3_1 cv fralcom3_2 wcel fralcom3_1 cv fralcom3_3 wcel fralcom3_0 pm2.04 ralimi2 fralcom3_1 cv fralcom3_2 wcel fralcom3_0 wi fralcom3_1 cv fralcom3_3 wcel fralcom3_0 wi fralcom3_1 fralcom3_3 fralcom3_2 fralcom3_1 cv fralcom3_3 wcel fralcom3_1 cv fralcom3_2 wcel fralcom3_0 pm2.04 ralimi2 impbii $.
$}
$( Rearrange existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Proof shortened by Andrew Salmon, 30-May-2011.) $)
${
	$d y A $.
	$d x B $.
	$d x y $.
	freean_0 $f wff ph $.
	freean_1 $f wff ps $.
	freean_2 $f set x $.
	freean_3 $f set y $.
	freean_4 $f class A $.
	freean_5 $f class B $.
	ereean_0 $e |- F/ y ph $.
	ereean_1 $e |- F/ x ps $.
	reean $p |- ( E. x e. A E. y e. B ( ph /\ ps ) <-> ( E. x e. A ph /\ E. y e. B ps ) ) $= freean_2 cv freean_4 wcel freean_3 cv freean_5 wcel wa freean_0 freean_1 wa wa freean_3 wex freean_2 wex freean_2 cv freean_4 wcel freean_0 wa freean_2 wex freean_3 cv freean_5 wcel freean_1 wa freean_3 wex wa freean_0 freean_1 wa freean_3 freean_5 wrex freean_2 freean_4 wrex freean_0 freean_2 freean_4 wrex freean_1 freean_3 freean_5 wrex wa freean_2 cv freean_4 wcel freean_3 cv freean_5 wcel wa freean_0 freean_1 wa wa freean_3 wex freean_2 wex freean_2 cv freean_4 wcel freean_0 wa freean_3 cv freean_5 wcel freean_1 wa wa freean_3 wex freean_2 wex freean_2 cv freean_4 wcel freean_0 wa freean_2 wex freean_3 cv freean_5 wcel freean_1 wa freean_3 wex wa freean_2 cv freean_4 wcel freean_3 cv freean_5 wcel wa freean_0 freean_1 wa wa freean_2 cv freean_4 wcel freean_0 wa freean_3 cv freean_5 wcel freean_1 wa wa freean_2 freean_3 freean_2 cv freean_4 wcel freean_3 cv freean_5 wcel freean_0 freean_1 an4 2exbii freean_2 cv freean_4 wcel freean_0 wa freean_3 cv freean_5 wcel freean_1 wa freean_2 freean_3 freean_2 cv freean_4 wcel freean_0 freean_3 freean_2 cv freean_4 wcel freean_3 nfv ereean_0 nfan freean_3 cv freean_5 wcel freean_1 freean_2 freean_3 cv freean_5 wcel freean_2 nfv ereean_1 nfan eean bitri freean_0 freean_1 wa freean_2 freean_3 freean_4 freean_5 r2ex freean_0 freean_2 freean_4 wrex freean_2 cv freean_4 wcel freean_0 wa freean_2 wex freean_1 freean_3 freean_5 wrex freean_3 cv freean_5 wcel freean_1 wa freean_3 wex freean_0 freean_2 freean_4 df-rex freean_1 freean_3 freean_5 df-rex anbi12i 3bitr4i $.
$}
$( Rearrange existential quantifiers.  (Contributed by NM, 9-May-1999.) $)
${
	$d y ph $.
	$d x ps $.
	$d x y $.
	$d y A $.
	$d x B $.
	freeanv_0 $f wff ph $.
	freeanv_1 $f wff ps $.
	freeanv_2 $f set x $.
	freeanv_3 $f set y $.
	freeanv_4 $f class A $.
	freeanv_5 $f class B $.
	reeanv $p |- ( E. x e. A E. y e. B ( ph /\ ps ) <-> ( E. x e. A ph /\ E. y e. B ps ) ) $= freeanv_0 freeanv_1 freeanv_2 freeanv_3 freeanv_4 freeanv_5 freeanv_0 freeanv_3 nfv freeanv_1 freeanv_2 nfv reean $.
$}
$( Rearrange three existential quantifiers.  (Contributed by Jeff Madsen,
       11-Jun-2010.) $)
${
	$d ph y z $.
	$d ps x z $.
	$d ch x y $.
	$d A y $.
	$d B x z $.
	$d C x y $.
	f3reeanv_0 $f wff ph $.
	f3reeanv_1 $f wff ps $.
	f3reeanv_2 $f wff ch $.
	f3reeanv_3 $f set x $.
	f3reeanv_4 $f set y $.
	f3reeanv_5 $f set z $.
	f3reeanv_6 $f class A $.
	f3reeanv_7 $f class B $.
	f3reeanv_8 $f class C $.
	3reeanv $p |- ( E. x e. A E. y e. B E. z e. C ( ph /\ ps /\ ch ) <-> ( E. x e. A ph /\ E. y e. B ps /\ E. z e. C ch ) ) $= f3reeanv_0 f3reeanv_1 wa f3reeanv_4 f3reeanv_7 wrex f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex wa f3reeanv_3 f3reeanv_6 wrex f3reeanv_0 f3reeanv_3 f3reeanv_6 wrex f3reeanv_1 f3reeanv_4 f3reeanv_7 wrex wa f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex wa f3reeanv_0 f3reeanv_1 f3reeanv_2 w3a f3reeanv_5 f3reeanv_8 wrex f3reeanv_4 f3reeanv_7 wrex f3reeanv_3 f3reeanv_6 wrex f3reeanv_0 f3reeanv_3 f3reeanv_6 wrex f3reeanv_1 f3reeanv_4 f3reeanv_7 wrex f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex w3a f3reeanv_0 f3reeanv_1 wa f3reeanv_4 f3reeanv_7 wrex f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex wa f3reeanv_3 f3reeanv_6 wrex f3reeanv_0 f3reeanv_1 wa f3reeanv_4 f3reeanv_7 wrex f3reeanv_3 f3reeanv_6 wrex f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex wa f3reeanv_0 f3reeanv_3 f3reeanv_6 wrex f3reeanv_1 f3reeanv_4 f3reeanv_7 wrex wa f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex wa f3reeanv_0 f3reeanv_1 wa f3reeanv_4 f3reeanv_7 wrex f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex f3reeanv_3 f3reeanv_6 r19.41v f3reeanv_0 f3reeanv_1 wa f3reeanv_4 f3reeanv_7 wrex f3reeanv_3 f3reeanv_6 wrex f3reeanv_0 f3reeanv_3 f3reeanv_6 wrex f3reeanv_1 f3reeanv_4 f3reeanv_7 wrex wa f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex f3reeanv_0 f3reeanv_1 f3reeanv_3 f3reeanv_4 f3reeanv_6 f3reeanv_7 reeanv anbi1i bitri f3reeanv_0 f3reeanv_1 f3reeanv_2 w3a f3reeanv_5 f3reeanv_8 wrex f3reeanv_4 f3reeanv_7 wrex f3reeanv_0 f3reeanv_1 wa f3reeanv_4 f3reeanv_7 wrex f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex wa f3reeanv_3 f3reeanv_6 f3reeanv_0 f3reeanv_1 f3reeanv_2 w3a f3reeanv_5 f3reeanv_8 wrex f3reeanv_4 f3reeanv_7 wrex f3reeanv_0 f3reeanv_1 wa f3reeanv_2 wa f3reeanv_5 f3reeanv_8 wrex f3reeanv_4 f3reeanv_7 wrex f3reeanv_0 f3reeanv_1 wa f3reeanv_4 f3reeanv_7 wrex f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex wa f3reeanv_0 f3reeanv_1 f3reeanv_2 w3a f3reeanv_0 f3reeanv_1 wa f3reeanv_2 wa f3reeanv_4 f3reeanv_5 f3reeanv_7 f3reeanv_8 f3reeanv_0 f3reeanv_1 f3reeanv_2 df-3an 2rexbii f3reeanv_0 f3reeanv_1 wa f3reeanv_2 f3reeanv_4 f3reeanv_5 f3reeanv_7 f3reeanv_8 reeanv bitri rexbii f3reeanv_0 f3reeanv_3 f3reeanv_6 wrex f3reeanv_1 f3reeanv_4 f3reeanv_7 wrex f3reeanv_2 f3reeanv_5 f3reeanv_8 wrex df-3an 3bitr4i $.
$}
$( Distribute quantification over "or".  (Contributed by Jeff Madsen,
       19-Jun-2010.) $)
${
	$d ph y $.
	$d ps x $.
	$d A y $.
	$d B x $.
	$d x y $.
	f2ralor_0 $f wff ph $.
	f2ralor_1 $f wff ps $.
	f2ralor_2 $f set x $.
	f2ralor_3 $f set y $.
	f2ralor_4 $f class A $.
	f2ralor_5 $f class B $.
	2ralor $p |- ( A. x e. A A. y e. B ( ph \/ ps ) <-> ( A. x e. A ph \/ A. y e. B ps ) ) $= f2ralor_0 f2ralor_1 wo f2ralor_3 f2ralor_5 wral f2ralor_2 f2ralor_4 wral f2ralor_0 f2ralor_2 f2ralor_4 wral f2ralor_1 f2ralor_3 f2ralor_5 wral wo f2ralor_0 wn f2ralor_2 f2ralor_4 wrex f2ralor_1 wn f2ralor_3 f2ralor_5 wrex wa f2ralor_0 f2ralor_2 f2ralor_4 wral wn f2ralor_1 f2ralor_3 f2ralor_5 wral wn wa f2ralor_0 f2ralor_1 wo f2ralor_3 f2ralor_5 wral f2ralor_2 f2ralor_4 wral wn f2ralor_0 f2ralor_2 f2ralor_4 wral f2ralor_1 f2ralor_3 f2ralor_5 wral wo wn f2ralor_0 wn f2ralor_2 f2ralor_4 wrex f2ralor_0 f2ralor_2 f2ralor_4 wral wn f2ralor_1 wn f2ralor_3 f2ralor_5 wrex f2ralor_1 f2ralor_3 f2ralor_5 wral wn f2ralor_0 f2ralor_2 f2ralor_4 rexnal f2ralor_1 f2ralor_3 f2ralor_5 rexnal anbi12i f2ralor_0 wn f2ralor_1 wn wa f2ralor_3 f2ralor_5 wrex f2ralor_2 f2ralor_4 wrex f2ralor_0 f2ralor_1 wo f2ralor_3 f2ralor_5 wral wn f2ralor_2 f2ralor_4 wrex f2ralor_0 wn f2ralor_2 f2ralor_4 wrex f2ralor_1 wn f2ralor_3 f2ralor_5 wrex wa f2ralor_0 f2ralor_1 wo f2ralor_3 f2ralor_5 wral f2ralor_2 f2ralor_4 wral wn f2ralor_0 wn f2ralor_1 wn wa f2ralor_3 f2ralor_5 wrex f2ralor_0 f2ralor_1 wo f2ralor_3 f2ralor_5 wral wn f2ralor_2 f2ralor_4 f2ralor_0 wn f2ralor_1 wn wa f2ralor_3 f2ralor_5 wrex f2ralor_0 f2ralor_1 wo wn f2ralor_3 f2ralor_5 wrex f2ralor_0 f2ralor_1 wo f2ralor_3 f2ralor_5 wral wn f2ralor_0 f2ralor_1 wo wn f2ralor_0 wn f2ralor_1 wn wa f2ralor_3 f2ralor_5 f2ralor_0 f2ralor_1 ioran rexbii f2ralor_0 f2ralor_1 wo f2ralor_3 f2ralor_5 rexnal bitr3i rexbii f2ralor_0 wn f2ralor_1 wn f2ralor_2 f2ralor_3 f2ralor_4 f2ralor_5 reeanv f2ralor_0 f2ralor_1 wo f2ralor_3 f2ralor_5 wral f2ralor_2 f2ralor_4 rexnal 3bitr3ri f2ralor_0 f2ralor_2 f2ralor_4 wral f2ralor_1 f2ralor_3 f2ralor_5 wral ioran 3bitr4i con4bii $.
$}
$( ` x ` is not free in ` E! x e. A ph ` .  (Contributed by NM,
     19-Mar-1997.) $)
${
	fnfreu1_0 $f wff ph $.
	fnfreu1_1 $f set x $.
	fnfreu1_2 $f class A $.
	nfreu1 $p |- F/ x E! x e. A ph $= fnfreu1_0 fnfreu1_1 fnfreu1_2 wreu fnfreu1_1 cv fnfreu1_2 wcel fnfreu1_0 wa fnfreu1_1 weu fnfreu1_1 fnfreu1_0 fnfreu1_1 fnfreu1_2 df-reu fnfreu1_1 cv fnfreu1_2 wcel fnfreu1_0 wa fnfreu1_1 nfeu1 nfxfr $.
$}
$( ` x ` is not free in ` E* x e. A ph ` .  (Contributed by NM,
     16-Jun-2017.) $)
${
	fnfrmo1_0 $f wff ph $.
	fnfrmo1_1 $f set x $.
	fnfrmo1_2 $f class A $.
	nfrmo1 $p |- F/ x E* x e. A ph $= fnfrmo1_0 fnfrmo1_1 fnfrmo1_2 wrmo fnfrmo1_1 cv fnfrmo1_2 wcel fnfrmo1_0 wa fnfrmo1_1 wmo fnfrmo1_1 fnfrmo1_0 fnfrmo1_1 fnfrmo1_2 df-rmo fnfrmo1_1 cv fnfrmo1_2 wcel fnfrmo1_0 wa fnfrmo1_1 nfmo1 nfxfr $.
$}
$( Deduction version of ~ nfreu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 8-Oct-2016.) $)
${
	fnfreud_0 $f wff ph $.
	fnfreud_1 $f wff ps $.
	fnfreud_2 $f set x $.
	fnfreud_3 $f set y $.
	fnfreud_4 $f class A $.
	enfreud_0 $e |- F/ y ph $.
	enfreud_1 $e |- ( ph -> F/_ x A ) $.
	enfreud_2 $e |- ( ph -> F/ x ps ) $.
	nfreud $p |- ( ph -> F/ x E! y e. A ps ) $= fnfreud_1 fnfreud_3 fnfreud_4 wreu fnfreud_3 cv fnfreud_4 wcel fnfreud_1 wa fnfreud_3 weu fnfreud_0 fnfreud_2 fnfreud_1 fnfreud_3 fnfreud_4 df-reu fnfreud_0 fnfreud_3 cv fnfreud_4 wcel fnfreud_1 wa fnfreud_2 fnfreud_3 enfreud_0 fnfreud_0 fnfreud_2 cv fnfreud_3 cv wceq fnfreud_2 wal wn wa fnfreud_3 cv fnfreud_4 wcel fnfreud_1 fnfreud_2 fnfreud_0 fnfreud_2 cv fnfreud_3 cv wceq fnfreud_2 wal wn wa fnfreud_2 fnfreud_3 cv fnfreud_4 fnfreud_2 cv fnfreud_3 cv wceq fnfreud_2 wal wn fnfreud_2 fnfreud_3 cv wnfc fnfreud_0 fnfreud_2 fnfreud_3 nfcvf adantl fnfreud_0 fnfreud_2 fnfreud_4 wnfc fnfreud_2 cv fnfreud_3 cv wceq fnfreud_2 wal wn enfreud_1 adantr nfeld fnfreud_0 fnfreud_1 fnfreud_2 wnf fnfreud_2 cv fnfreud_3 cv wceq fnfreud_2 wal wn enfreud_2 adantr nfand nfeud2 nfxfrd $.
$}
$( Deduction version of ~ nfrmo .  (Contributed by NM, 17-Jun-2017.) $)
${
	fnfrmod_0 $f wff ph $.
	fnfrmod_1 $f wff ps $.
	fnfrmod_2 $f set x $.
	fnfrmod_3 $f set y $.
	fnfrmod_4 $f class A $.
	enfrmod_0 $e |- F/ y ph $.
	enfrmod_1 $e |- ( ph -> F/_ x A ) $.
	enfrmod_2 $e |- ( ph -> F/ x ps ) $.
	nfrmod $p |- ( ph -> F/ x E* y e. A ps ) $= fnfrmod_1 fnfrmod_3 fnfrmod_4 wrmo fnfrmod_3 cv fnfrmod_4 wcel fnfrmod_1 wa fnfrmod_3 wmo fnfrmod_0 fnfrmod_2 fnfrmod_1 fnfrmod_3 fnfrmod_4 df-rmo fnfrmod_0 fnfrmod_3 cv fnfrmod_4 wcel fnfrmod_1 wa fnfrmod_2 fnfrmod_3 enfrmod_0 fnfrmod_0 fnfrmod_2 fnfrmod_3 weq fnfrmod_2 wal wn wa fnfrmod_3 cv fnfrmod_4 wcel fnfrmod_1 fnfrmod_2 fnfrmod_0 fnfrmod_2 fnfrmod_3 weq fnfrmod_2 wal wn wa fnfrmod_2 fnfrmod_3 cv fnfrmod_4 fnfrmod_2 fnfrmod_3 weq fnfrmod_2 wal wn fnfrmod_2 fnfrmod_3 cv wnfc fnfrmod_0 fnfrmod_2 fnfrmod_3 nfcvf adantl fnfrmod_0 fnfrmod_2 fnfrmod_4 wnfc fnfrmod_2 fnfrmod_3 weq fnfrmod_2 wal wn enfrmod_1 adantr nfeld fnfrmod_0 fnfrmod_1 fnfrmod_2 wnf fnfrmod_2 fnfrmod_3 weq fnfrmod_2 wal wn enfrmod_2 adantr nfand nfmod2 nfxfrd $.
$}
$( Bound-variable hypothesis builder for restricted uniqueness.
       (Contributed by NM, 30-Oct-2010.)  (Revised by Mario Carneiro,
       8-Oct-2016.) $)
${
	fnfreu_0 $f wff ph $.
	fnfreu_1 $f set x $.
	fnfreu_2 $f set y $.
	fnfreu_3 $f class A $.
	enfreu_0 $e |- F/_ x A $.
	enfreu_1 $e |- F/ x ph $.
	nfreu $p |- F/ x E! y e. A ph $= fnfreu_0 fnfreu_2 fnfreu_3 wreu fnfreu_1 wnf wtru fnfreu_0 fnfreu_1 fnfreu_2 fnfreu_3 fnfreu_2 nftru fnfreu_1 fnfreu_3 wnfc wtru enfreu_0 a1i fnfreu_0 fnfreu_1 wnf wtru enfreu_1 a1i nfreud trud $.
$}
$( Bound-variable hypothesis builder for restricted uniqueness.
       (Contributed by NM, 16-Jun-2017.) $)
${
	fnfrmo_0 $f wff ph $.
	fnfrmo_1 $f set x $.
	fnfrmo_2 $f set y $.
	fnfrmo_3 $f class A $.
	enfrmo_0 $e |- F/_ x A $.
	enfrmo_1 $e |- F/ x ph $.
	nfrmo $p |- F/ x E* y e. A ph $= fnfrmo_0 fnfrmo_2 fnfrmo_3 wrmo fnfrmo_2 cv fnfrmo_3 wcel fnfrmo_0 wa fnfrmo_2 wmo fnfrmo_1 fnfrmo_0 fnfrmo_2 fnfrmo_3 df-rmo fnfrmo_2 cv fnfrmo_3 wcel fnfrmo_0 wa fnfrmo_2 wmo fnfrmo_1 wnf wtru fnfrmo_2 cv fnfrmo_3 wcel fnfrmo_0 wa fnfrmo_1 fnfrmo_2 fnfrmo_2 nftru fnfrmo_1 fnfrmo_2 weq fnfrmo_1 wal wn fnfrmo_2 cv fnfrmo_3 wcel fnfrmo_0 wa fnfrmo_1 wnf wtru fnfrmo_1 fnfrmo_2 weq fnfrmo_1 wal wn fnfrmo_2 cv fnfrmo_3 wcel fnfrmo_0 fnfrmo_1 fnfrmo_1 fnfrmo_2 weq fnfrmo_1 wal wn fnfrmo_1 fnfrmo_2 cv fnfrmo_3 fnfrmo_1 fnfrmo_2 nfcvf fnfrmo_1 fnfrmo_3 wnfc fnfrmo_1 fnfrmo_2 weq fnfrmo_1 wal wn enfrmo_0 a1i nfeld fnfrmo_0 fnfrmo_1 wnf fnfrmo_1 fnfrmo_2 weq fnfrmo_1 wal wn enfrmo_1 a1i nfand adantl nfmod2 trud nfxfr $.
$}
$( An "identity" law of concretion for restricted abstraction.  Special case
     of Definition 2.1 of [Quine] p. 16.  (Contributed by NM, 9-Oct-2003.) $)
${
	frabid_0 $f wff ph $.
	frabid_1 $f set x $.
	frabid_2 $f class A $.
	rabid $p |- ( x e. { x e. A | ph } <-> ( x e. A /\ ph ) ) $= frabid_1 cv frabid_2 wcel frabid_0 wa frabid_1 frabid_0 frabid_1 frabid_2 crab frabid_0 frabid_1 frabid_2 df-rab abeq2i $.
$}
$( An "identity" law for restricted class abstraction.  (Contributed by NM,
       9-Oct-2003.)  (Proof shortened by Andrew Salmon, 30-May-2011.) $)
${
	$d x A $.
	frabid2_0 $f wff ph $.
	frabid2_1 $f set x $.
	frabid2_2 $f class A $.
	rabid2 $p |- ( A = { x e. A | ph } <-> A. x e. A ph ) $= frabid2_2 frabid2_1 cv frabid2_2 wcel frabid2_0 wa frabid2_1 cab wceq frabid2_1 cv frabid2_2 wcel frabid2_0 wi frabid2_1 wal frabid2_2 frabid2_0 frabid2_1 frabid2_2 crab wceq frabid2_0 frabid2_1 frabid2_2 wral frabid2_2 frabid2_1 cv frabid2_2 wcel frabid2_0 wa frabid2_1 cab wceq frabid2_1 cv frabid2_2 wcel frabid2_1 cv frabid2_2 wcel frabid2_0 wa wb frabid2_1 wal frabid2_1 cv frabid2_2 wcel frabid2_0 wi frabid2_1 wal frabid2_1 cv frabid2_2 wcel frabid2_0 wa frabid2_1 frabid2_2 abeq2 frabid2_1 cv frabid2_2 wcel frabid2_0 wi frabid2_1 cv frabid2_2 wcel frabid2_1 cv frabid2_2 wcel frabid2_0 wa wb frabid2_1 frabid2_1 cv frabid2_2 wcel frabid2_0 pm4.71 albii bitr4i frabid2_0 frabid2_1 frabid2_2 crab frabid2_1 cv frabid2_2 wcel frabid2_0 wa frabid2_1 cab frabid2_2 frabid2_0 frabid2_1 frabid2_2 df-rab eqeq2i frabid2_0 frabid2_1 frabid2_2 df-ral 3bitr4i $.
$}
$( Equivalent wff's correspond to equal restricted class abstractions.
       Closed theorem form of ~ rabbidva .  (Contributed by NM,
       25-Nov-2013.) $)
${
	frabbi_0 $f wff ps $.
	frabbi_1 $f wff ch $.
	frabbi_2 $f set x $.
	frabbi_3 $f class A $.
	rabbi $p |- ( A. x e. A ( ps <-> ch ) <-> { x e. A | ps } = { x e. A | ch } ) $= frabbi_2 cv frabbi_3 wcel frabbi_0 wa frabbi_2 cv frabbi_3 wcel frabbi_1 wa wb frabbi_2 wal frabbi_2 cv frabbi_3 wcel frabbi_0 wa frabbi_2 cab frabbi_2 cv frabbi_3 wcel frabbi_1 wa frabbi_2 cab wceq frabbi_0 frabbi_1 wb frabbi_2 frabbi_3 wral frabbi_0 frabbi_2 frabbi_3 crab frabbi_1 frabbi_2 frabbi_3 crab wceq frabbi_2 cv frabbi_3 wcel frabbi_0 wa frabbi_2 cv frabbi_3 wcel frabbi_1 wa frabbi_2 abbi frabbi_0 frabbi_1 wb frabbi_2 frabbi_3 wral frabbi_2 cv frabbi_3 wcel frabbi_0 frabbi_1 wb wi frabbi_2 wal frabbi_2 cv frabbi_3 wcel frabbi_0 wa frabbi_2 cv frabbi_3 wcel frabbi_1 wa wb frabbi_2 wal frabbi_0 frabbi_1 wb frabbi_2 frabbi_3 df-ral frabbi_2 cv frabbi_3 wcel frabbi_0 frabbi_1 wb wi frabbi_2 cv frabbi_3 wcel frabbi_0 wa frabbi_2 cv frabbi_3 wcel frabbi_1 wa wb frabbi_2 frabbi_2 cv frabbi_3 wcel frabbi_0 frabbi_1 pm5.32 albii bitri frabbi_0 frabbi_2 frabbi_3 crab frabbi_2 cv frabbi_3 wcel frabbi_0 wa frabbi_2 cab frabbi_1 frabbi_2 frabbi_3 crab frabbi_2 cv frabbi_3 wcel frabbi_1 wa frabbi_2 cab frabbi_0 frabbi_2 frabbi_3 df-rab frabbi_1 frabbi_2 frabbi_3 df-rab eqeq12i 3bitr4i $.
$}
$( Swap with a membership relation in a restricted class abstraction.
     (Contributed by NM, 4-Jul-2005.) $)
${
	frabswap_0 $f set x $.
	frabswap_1 $f class A $.
	frabswap_2 $f class B $.
	rabswap $p |- { x e. A | x e. B } = { x e. B | x e. A } $= frabswap_0 cv frabswap_1 wcel frabswap_0 cv frabswap_2 wcel wa frabswap_0 cab frabswap_0 cv frabswap_2 wcel frabswap_0 cv frabswap_1 wcel wa frabswap_0 cab frabswap_0 cv frabswap_2 wcel frabswap_0 frabswap_1 crab frabswap_0 cv frabswap_1 wcel frabswap_0 frabswap_2 crab frabswap_0 cv frabswap_1 wcel frabswap_0 cv frabswap_2 wcel wa frabswap_0 cv frabswap_2 wcel frabswap_0 cv frabswap_1 wcel wa frabswap_0 frabswap_0 cv frabswap_1 wcel frabswap_0 cv frabswap_2 wcel ancom abbii frabswap_0 cv frabswap_2 wcel frabswap_0 frabswap_1 df-rab frabswap_0 cv frabswap_1 wcel frabswap_0 frabswap_2 df-rab 3eqtr4i $.
$}
$( The abstraction variable in a restricted class abstraction isn't free.
       (Contributed by NM, 19-Mar-1997.) $)
${
	fnfrab1_0 $f wff ph $.
	fnfrab1_1 $f set x $.
	fnfrab1_2 $f class A $.
	nfrab1 $p |- F/_ x { x e. A | ph } $= fnfrab1_1 fnfrab1_0 fnfrab1_1 fnfrab1_2 crab fnfrab1_1 cv fnfrab1_2 wcel fnfrab1_0 wa fnfrab1_1 cab fnfrab1_0 fnfrab1_1 fnfrab1_2 df-rab fnfrab1_1 cv fnfrab1_2 wcel fnfrab1_0 wa fnfrab1_1 nfab1 nfcxfr $.
$}
$( A variable not free in a wff remains so in a restricted class
       abstraction.  (Contributed by NM, 13-Oct-2003.)  (Revised by Mario
       Carneiro, 9-Oct-2016.) $)
${
	$d x z $.
	$d y z $.
	$d z A $.
	infrab_0 $f set z $.
	fnfrab_0 $f wff ph $.
	fnfrab_1 $f set x $.
	fnfrab_2 $f set y $.
	fnfrab_3 $f class A $.
	enfrab_0 $e |- F/ x ph $.
	enfrab_1 $e |- F/_ x A $.
	nfrab $p |- F/_ x { y e. A | ph } $= fnfrab_1 fnfrab_0 fnfrab_2 fnfrab_3 crab fnfrab_2 cv fnfrab_3 wcel fnfrab_0 wa fnfrab_2 cab fnfrab_0 fnfrab_2 fnfrab_3 df-rab fnfrab_1 fnfrab_2 cv fnfrab_3 wcel fnfrab_0 wa fnfrab_2 cab wnfc wtru fnfrab_2 cv fnfrab_3 wcel fnfrab_0 wa fnfrab_1 fnfrab_2 fnfrab_2 nftru fnfrab_1 cv fnfrab_2 cv wceq fnfrab_1 wal wn fnfrab_2 cv fnfrab_3 wcel fnfrab_0 wa fnfrab_1 wnf wtru fnfrab_1 cv fnfrab_2 cv wceq fnfrab_1 wal wn fnfrab_2 cv fnfrab_3 wcel fnfrab_0 fnfrab_1 infrab_0 cv fnfrab_3 wcel fnfrab_2 cv fnfrab_3 wcel fnfrab_1 fnfrab_2 infrab_0 fnfrab_1 infrab_0 fnfrab_3 enfrab_1 nfcri infrab_0 cv fnfrab_2 cv fnfrab_3 eleq1 dvelimnf fnfrab_0 fnfrab_1 wnf fnfrab_1 cv fnfrab_2 cv wceq fnfrab_1 wal wn enfrab_0 a1i nfand adantl nfabd2 trud nfcxfr $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by Mario Carneiro, 19-Nov-2016.) $)
${
	freubida_0 $f wff ph $.
	freubida_1 $f wff ps $.
	freubida_2 $f wff ch $.
	freubida_3 $f set x $.
	freubida_4 $f class A $.
	ereubida_0 $e |- F/ x ph $.
	ereubida_1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	reubida $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $= freubida_0 freubida_3 cv freubida_4 wcel freubida_1 wa freubida_3 weu freubida_3 cv freubida_4 wcel freubida_2 wa freubida_3 weu freubida_1 freubida_3 freubida_4 wreu freubida_2 freubida_3 freubida_4 wreu freubida_0 freubida_3 cv freubida_4 wcel freubida_1 wa freubida_3 cv freubida_4 wcel freubida_2 wa freubida_3 ereubida_0 freubida_0 freubida_3 cv freubida_4 wcel freubida_1 freubida_2 ereubida_1 pm5.32da eubid freubida_1 freubida_3 freubida_4 df-reu freubida_2 freubida_3 freubida_4 df-reu 3bitr4g $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 13-Nov-2004.) $)
${
	$d x ph $.
	freubidva_0 $f wff ph $.
	freubidva_1 $f wff ps $.
	freubidva_2 $f wff ch $.
	freubidva_3 $f set x $.
	freubidva_4 $f class A $.
	ereubidva_0 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	reubidva $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $= freubidva_0 freubidva_1 freubidva_2 freubidva_3 freubidva_4 freubidva_0 freubidva_3 nfv ereubidva_0 reubida $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 17-Oct-1996.) $)
${
	$d x ph $.
	freubidv_0 $f wff ph $.
	freubidv_1 $f wff ps $.
	freubidv_2 $f wff ch $.
	freubidv_3 $f set x $.
	freubidv_4 $f class A $.
	ereubidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	reubidv $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $= freubidv_0 freubidv_1 freubidv_2 freubidv_3 freubidv_4 freubidv_0 freubidv_1 freubidv_2 wb freubidv_3 cv freubidv_4 wcel ereubidv_0 adantr reubidva $.
$}
$( Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 14-Nov-2004.) $)
${
	freubiia_0 $f wff ph $.
	freubiia_1 $f wff ps $.
	freubiia_2 $f set x $.
	freubiia_3 $f class A $.
	ereubiia_0 $e |- ( x e. A -> ( ph <-> ps ) ) $.
	reubiia $p |- ( E! x e. A ph <-> E! x e. A ps ) $= freubiia_2 cv freubiia_3 wcel freubiia_0 wa freubiia_2 weu freubiia_2 cv freubiia_3 wcel freubiia_1 wa freubiia_2 weu freubiia_0 freubiia_2 freubiia_3 wreu freubiia_1 freubiia_2 freubiia_3 wreu freubiia_2 cv freubiia_3 wcel freubiia_0 wa freubiia_2 cv freubiia_3 wcel freubiia_1 wa freubiia_2 freubiia_2 cv freubiia_3 wcel freubiia_0 freubiia_1 ereubiia_0 pm5.32i eubii freubiia_0 freubiia_2 freubiia_3 df-reu freubiia_1 freubiia_2 freubiia_3 df-reu 3bitr4i $.
$}
$( Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 22-Oct-1999.) $)
${
	freubii_0 $f wff ph $.
	freubii_1 $f wff ps $.
	freubii_2 $f set x $.
	freubii_3 $f class A $.
	ereubii_0 $e |- ( ph <-> ps ) $.
	reubii $p |- ( E! x e. A ph <-> E! x e. A ps ) $= freubii_0 freubii_1 freubii_2 freubii_3 freubii_0 freubii_1 wb freubii_2 cv freubii_3 wcel ereubii_0 a1i reubiia $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)
${
	frmobida_0 $f wff ph $.
	frmobida_1 $f wff ps $.
	frmobida_2 $f wff ch $.
	frmobida_3 $f set x $.
	frmobida_4 $f class A $.
	ermobida_0 $e |- F/ x ph $.
	ermobida_1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	rmobida $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $= frmobida_0 frmobida_3 cv frmobida_4 wcel frmobida_1 wa frmobida_3 wmo frmobida_3 cv frmobida_4 wcel frmobida_2 wa frmobida_3 wmo frmobida_1 frmobida_3 frmobida_4 wrmo frmobida_2 frmobida_3 frmobida_4 wrmo frmobida_0 frmobida_3 cv frmobida_4 wcel frmobida_1 wa frmobida_3 cv frmobida_4 wcel frmobida_2 wa frmobida_3 ermobida_0 frmobida_0 frmobida_3 cv frmobida_4 wcel frmobida_1 frmobida_2 ermobida_1 pm5.32da mobid frmobida_1 frmobida_3 frmobida_4 df-rmo frmobida_2 frmobida_3 frmobida_4 df-rmo 3bitr4g $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)
${
	$d x ph $.
	frmobidva_0 $f wff ph $.
	frmobidva_1 $f wff ps $.
	frmobidva_2 $f wff ch $.
	frmobidva_3 $f set x $.
	frmobidva_4 $f class A $.
	ermobidva_0 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	rmobidva $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $= frmobidva_0 frmobidva_1 frmobidva_2 frmobidva_3 frmobidva_4 frmobidva_0 frmobidva_3 nfv ermobidva_0 rmobida $.
$}
$( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)
${
	$d x ph $.
	frmobidv_0 $f wff ph $.
	frmobidv_1 $f wff ps $.
	frmobidv_2 $f wff ch $.
	frmobidv_3 $f set x $.
	frmobidv_4 $f class A $.
	ermobidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	rmobidv $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $= frmobidv_0 frmobidv_1 frmobidv_2 frmobidv_3 frmobidv_4 frmobidv_0 frmobidv_1 frmobidv_2 wb frmobidv_3 cv frmobidv_4 wcel ermobidv_0 adantr rmobidva $.
$}
$( Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 16-Jun-2017.) $)
${
	frmobiia_0 $f wff ph $.
	frmobiia_1 $f wff ps $.
	frmobiia_2 $f set x $.
	frmobiia_3 $f class A $.
	ermobiia_0 $e |- ( x e. A -> ( ph <-> ps ) ) $.
	rmobiia $p |- ( E* x e. A ph <-> E* x e. A ps ) $= frmobiia_2 cv frmobiia_3 wcel frmobiia_0 wa frmobiia_2 wmo frmobiia_2 cv frmobiia_3 wcel frmobiia_1 wa frmobiia_2 wmo frmobiia_0 frmobiia_2 frmobiia_3 wrmo frmobiia_1 frmobiia_2 frmobiia_3 wrmo frmobiia_2 cv frmobiia_3 wcel frmobiia_0 wa frmobiia_2 cv frmobiia_3 wcel frmobiia_1 wa frmobiia_2 frmobiia_2 cv frmobiia_3 wcel frmobiia_0 frmobiia_1 ermobiia_0 pm5.32i mobii frmobiia_0 frmobiia_2 frmobiia_3 df-rmo frmobiia_1 frmobiia_2 frmobiia_3 df-rmo 3bitr4i $.
$}
$( Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 16-Jun-2017.) $)
${
	frmobii_0 $f wff ph $.
	frmobii_1 $f wff ps $.
	frmobii_2 $f set x $.
	frmobii_3 $f class A $.
	ermobii_0 $e |- ( ph <-> ps ) $.
	rmobii $p |- ( E* x e. A ph <-> E* x e. A ps ) $= frmobii_0 frmobii_1 frmobii_2 frmobii_3 frmobii_0 frmobii_1 wb frmobii_2 cv frmobii_3 wcel ermobii_0 a1i rmobiia $.
$}
$( Equality theorem for restricted universal quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 7-Mar-2004.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
${
	fraleqf_0 $f wff ph $.
	fraleqf_1 $f set x $.
	fraleqf_2 $f class A $.
	fraleqf_3 $f class B $.
	eraleqf_0 $e |- F/_ x A $.
	eraleqf_1 $e |- F/_ x B $.
	raleqf $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ph ) ) $= fraleqf_2 fraleqf_3 wceq fraleqf_1 cv fraleqf_2 wcel fraleqf_0 wi fraleqf_1 wal fraleqf_1 cv fraleqf_3 wcel fraleqf_0 wi fraleqf_1 wal fraleqf_0 fraleqf_1 fraleqf_2 wral fraleqf_0 fraleqf_1 fraleqf_3 wral fraleqf_2 fraleqf_3 wceq fraleqf_1 cv fraleqf_2 wcel fraleqf_0 wi fraleqf_1 cv fraleqf_3 wcel fraleqf_0 wi fraleqf_1 fraleqf_1 fraleqf_2 fraleqf_3 eraleqf_0 eraleqf_1 nfeq fraleqf_2 fraleqf_3 wceq fraleqf_1 cv fraleqf_2 wcel fraleqf_1 cv fraleqf_3 wcel fraleqf_0 fraleqf_2 fraleqf_3 fraleqf_1 cv eleq2 imbi1d albid fraleqf_0 fraleqf_1 fraleqf_2 df-ral fraleqf_0 fraleqf_1 fraleqf_3 df-ral 3bitr4g $.
$}
$( Equality theorem for restricted existential quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 9-Oct-2003.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
${
	frexeqf_0 $f wff ph $.
	frexeqf_1 $f set x $.
	frexeqf_2 $f class A $.
	frexeqf_3 $f class B $.
	erexeqf_0 $e |- F/_ x A $.
	erexeqf_1 $e |- F/_ x B $.
	rexeqf $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ph ) ) $= frexeqf_2 frexeqf_3 wceq frexeqf_1 cv frexeqf_2 wcel frexeqf_0 wa frexeqf_1 wex frexeqf_1 cv frexeqf_3 wcel frexeqf_0 wa frexeqf_1 wex frexeqf_0 frexeqf_1 frexeqf_2 wrex frexeqf_0 frexeqf_1 frexeqf_3 wrex frexeqf_2 frexeqf_3 wceq frexeqf_1 cv frexeqf_2 wcel frexeqf_0 wa frexeqf_1 cv frexeqf_3 wcel frexeqf_0 wa frexeqf_1 frexeqf_1 frexeqf_2 frexeqf_3 erexeqf_0 erexeqf_1 nfeq frexeqf_2 frexeqf_3 wceq frexeqf_1 cv frexeqf_2 wcel frexeqf_1 cv frexeqf_3 wcel frexeqf_0 frexeqf_2 frexeqf_3 frexeqf_1 cv eleq2 anbi1d exbid frexeqf_0 frexeqf_1 frexeqf_2 df-rex frexeqf_0 frexeqf_1 frexeqf_3 df-rex 3bitr4g $.
$}
$( Equality theorem for restricted uniqueness quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 5-Apr-2004.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
${
	freueq1f_0 $f wff ph $.
	freueq1f_1 $f set x $.
	freueq1f_2 $f class A $.
	freueq1f_3 $f class B $.
	ereueq1f_0 $e |- F/_ x A $.
	ereueq1f_1 $e |- F/_ x B $.
	reueq1f $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ph ) ) $= freueq1f_2 freueq1f_3 wceq freueq1f_1 cv freueq1f_2 wcel freueq1f_0 wa freueq1f_1 weu freueq1f_1 cv freueq1f_3 wcel freueq1f_0 wa freueq1f_1 weu freueq1f_0 freueq1f_1 freueq1f_2 wreu freueq1f_0 freueq1f_1 freueq1f_3 wreu freueq1f_2 freueq1f_3 wceq freueq1f_1 cv freueq1f_2 wcel freueq1f_0 wa freueq1f_1 cv freueq1f_3 wcel freueq1f_0 wa freueq1f_1 freueq1f_1 freueq1f_2 freueq1f_3 ereueq1f_0 ereueq1f_1 nfeq freueq1f_2 freueq1f_3 wceq freueq1f_1 cv freueq1f_2 wcel freueq1f_1 cv freueq1f_3 wcel freueq1f_0 freueq1f_2 freueq1f_3 freueq1f_1 cv eleq2 anbi1d eubid freueq1f_0 freueq1f_1 freueq1f_2 df-reu freueq1f_0 freueq1f_1 freueq1f_3 df-reu 3bitr4g $.
$}
$( Equality theorem for restricted uniqueness quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
${
	frmoeq1f_0 $f wff ph $.
	frmoeq1f_1 $f set x $.
	frmoeq1f_2 $f class A $.
	frmoeq1f_3 $f class B $.
	ermoeq1f_0 $e |- F/_ x A $.
	ermoeq1f_1 $e |- F/_ x B $.
	rmoeq1f $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ph ) ) $= frmoeq1f_2 frmoeq1f_3 wceq frmoeq1f_1 cv frmoeq1f_2 wcel frmoeq1f_0 wa frmoeq1f_1 wmo frmoeq1f_1 cv frmoeq1f_3 wcel frmoeq1f_0 wa frmoeq1f_1 wmo frmoeq1f_0 frmoeq1f_1 frmoeq1f_2 wrmo frmoeq1f_0 frmoeq1f_1 frmoeq1f_3 wrmo frmoeq1f_2 frmoeq1f_3 wceq frmoeq1f_1 cv frmoeq1f_2 wcel frmoeq1f_0 wa frmoeq1f_1 cv frmoeq1f_3 wcel frmoeq1f_0 wa frmoeq1f_1 frmoeq1f_1 frmoeq1f_2 frmoeq1f_3 ermoeq1f_0 ermoeq1f_1 nfeq frmoeq1f_2 frmoeq1f_3 wceq frmoeq1f_1 cv frmoeq1f_2 wcel frmoeq1f_1 cv frmoeq1f_3 wcel frmoeq1f_0 frmoeq1f_2 frmoeq1f_3 frmoeq1f_1 cv eleq2 anbi1d mobid frmoeq1f_0 frmoeq1f_1 frmoeq1f_2 df-rmo frmoeq1f_0 frmoeq1f_1 frmoeq1f_3 df-rmo 3bitr4g $.
$}
$( Equality theorem for restricted universal quantifier.  (Contributed by
       NM, 16-Nov-1995.) $)
${
	$d x A $.
	$d x B $.
	fraleq_0 $f wff ph $.
	fraleq_1 $f set x $.
	fraleq_2 $f class A $.
	fraleq_3 $f class B $.
	raleq $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ph ) ) $= fraleq_0 fraleq_1 fraleq_2 fraleq_3 fraleq_1 fraleq_2 nfcv fraleq_1 fraleq_3 nfcv raleqf $.
$}
$( Equality theorem for restricted existential quantifier.  (Contributed by
       NM, 29-Oct-1995.) $)
${
	$d x A $.
	$d x B $.
	frexeq_0 $f wff ph $.
	frexeq_1 $f set x $.
	frexeq_2 $f class A $.
	frexeq_3 $f class B $.
	rexeq $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ph ) ) $= frexeq_0 frexeq_1 frexeq_2 frexeq_3 frexeq_1 frexeq_2 nfcv frexeq_1 frexeq_3 nfcv rexeqf $.
$}
$( Equality theorem for restricted uniqueness quantifier.  (Contributed by
       NM, 5-Apr-2004.) $)
${
	$d x A $.
	$d x B $.
	freueq1_0 $f wff ph $.
	freueq1_1 $f set x $.
	freueq1_2 $f class A $.
	freueq1_3 $f class B $.
	reueq1 $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ph ) ) $= freueq1_0 freueq1_1 freueq1_2 freueq1_3 freueq1_1 freueq1_2 nfcv freueq1_1 freueq1_3 nfcv reueq1f $.
$}
$( Equality theorem for restricted uniqueness quantifier.  (Contributed by
       Alexander van der Vekens, 17-Jun-2017.) $)
${
	$d x A $.
	$d x B $.
	frmoeq1_0 $f wff ph $.
	frmoeq1_1 $f set x $.
	frmoeq1_2 $f class A $.
	frmoeq1_3 $f class B $.
	rmoeq1 $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ph ) ) $= frmoeq1_0 frmoeq1_1 frmoeq1_2 frmoeq1_3 frmoeq1_1 frmoeq1_2 nfcv frmoeq1_1 frmoeq1_3 nfcv rmoeq1f $.
$}
$( Equality inference for restricted universal qualifier.  (Contributed by
       Paul Chapman, 22-Jun-2011.) $)
${
	$d A x $.
	$d B x $.
	fraleqi_0 $f wff ph $.
	fraleqi_1 $f set x $.
	fraleqi_2 $f class A $.
	fraleqi_3 $f class B $.
	eraleqi_0 $e |- A = B $.
	raleqi $p |- ( A. x e. A ph <-> A. x e. B ph ) $= fraleqi_2 fraleqi_3 wceq fraleqi_0 fraleqi_1 fraleqi_2 wral fraleqi_0 fraleqi_1 fraleqi_3 wral wb eraleqi_0 fraleqi_0 fraleqi_1 fraleqi_2 fraleqi_3 raleq ax-mp $.
$}
$( Equality inference for restricted existential qualifier.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) $)
${
	$d A x $.
	$d B x $.
	frexeqi_0 $f wff ph $.
	frexeqi_1 $f set x $.
	frexeqi_2 $f class A $.
	frexeqi_3 $f class B $.
	erexeqi_0 $e |- A = B $.
	rexeqi $p |- ( E. x e. A ph <-> E. x e. B ph ) $= frexeqi_2 frexeqi_3 wceq frexeqi_0 frexeqi_1 frexeqi_2 wrex frexeqi_0 frexeqi_1 frexeqi_3 wrex wb erexeqi_0 frexeqi_0 frexeqi_1 frexeqi_2 frexeqi_3 rexeq ax-mp $.
$}
$( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 13-Nov-2005.) $)
${
	$d x A $.
	$d x B $.
	fraleqdv_0 $f wff ph $.
	fraleqdv_1 $f wff ps $.
	fraleqdv_2 $f set x $.
	fraleqdv_3 $f class A $.
	fraleqdv_4 $f class B $.
	eraleqdv_0 $e |- ( ph -> A = B ) $.
	raleqdv $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ps ) ) $= fraleqdv_0 fraleqdv_3 fraleqdv_4 wceq fraleqdv_1 fraleqdv_2 fraleqdv_3 wral fraleqdv_1 fraleqdv_2 fraleqdv_4 wral wb eraleqdv_0 fraleqdv_1 fraleqdv_2 fraleqdv_3 fraleqdv_4 raleq syl $.
$}
$( Equality deduction for restricted existential quantifier.  (Contributed
       by NM, 14-Jan-2007.) $)
${
	$d x A $.
	$d x B $.
	frexeqdv_0 $f wff ph $.
	frexeqdv_1 $f wff ps $.
	frexeqdv_2 $f set x $.
	frexeqdv_3 $f class A $.
	frexeqdv_4 $f class B $.
	erexeqdv_0 $e |- ( ph -> A = B ) $.
	rexeqdv $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ps ) ) $= frexeqdv_0 frexeqdv_3 frexeqdv_4 wceq frexeqdv_1 frexeqdv_2 frexeqdv_3 wrex frexeqdv_1 frexeqdv_2 frexeqdv_4 wrex wb erexeqdv_0 frexeqdv_1 frexeqdv_2 frexeqdv_3 frexeqdv_4 rexeq syl $.
$}
$( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 16-Nov-1995.) $)
${
	$d x A $.
	$d x B $.
	fraleqbi1dv_0 $f wff ph $.
	fraleqbi1dv_1 $f wff ps $.
	fraleqbi1dv_2 $f set x $.
	fraleqbi1dv_3 $f class A $.
	fraleqbi1dv_4 $f class B $.
	eraleqbi1dv_0 $e |- ( A = B -> ( ph <-> ps ) ) $.
	raleqbi1dv $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ps ) ) $= fraleqbi1dv_3 fraleqbi1dv_4 wceq fraleqbi1dv_0 fraleqbi1dv_2 fraleqbi1dv_3 wral fraleqbi1dv_0 fraleqbi1dv_2 fraleqbi1dv_4 wral fraleqbi1dv_1 fraleqbi1dv_2 fraleqbi1dv_4 wral fraleqbi1dv_0 fraleqbi1dv_2 fraleqbi1dv_3 fraleqbi1dv_4 raleq fraleqbi1dv_3 fraleqbi1dv_4 wceq fraleqbi1dv_0 fraleqbi1dv_1 fraleqbi1dv_2 fraleqbi1dv_4 eraleqbi1dv_0 ralbidv bitrd $.
$}
$( Equality deduction for restricted existential quantifier.  (Contributed
       by NM, 18-Mar-1997.) $)
${
	$d x A $.
	$d x B $.
	frexeqbi1dv_0 $f wff ph $.
	frexeqbi1dv_1 $f wff ps $.
	frexeqbi1dv_2 $f set x $.
	frexeqbi1dv_3 $f class A $.
	frexeqbi1dv_4 $f class B $.
	erexeqbi1dv_0 $e |- ( A = B -> ( ph <-> ps ) ) $.
	rexeqbi1dv $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ps ) ) $= frexeqbi1dv_3 frexeqbi1dv_4 wceq frexeqbi1dv_0 frexeqbi1dv_2 frexeqbi1dv_3 wrex frexeqbi1dv_0 frexeqbi1dv_2 frexeqbi1dv_4 wrex frexeqbi1dv_1 frexeqbi1dv_2 frexeqbi1dv_4 wrex frexeqbi1dv_0 frexeqbi1dv_2 frexeqbi1dv_3 frexeqbi1dv_4 rexeq frexeqbi1dv_3 frexeqbi1dv_4 wceq frexeqbi1dv_0 frexeqbi1dv_1 frexeqbi1dv_2 frexeqbi1dv_4 erexeqbi1dv_0 rexbidv bitrd $.
$}
$( Equality deduction for restricted uniqueness quantifier.  (Contributed
       by NM, 5-Apr-2004.) $)
${
	$d x A $.
	$d x B $.
	freueqd_0 $f wff ph $.
	freueqd_1 $f wff ps $.
	freueqd_2 $f set x $.
	freueqd_3 $f class A $.
	freueqd_4 $f class B $.
	ereueqd_0 $e |- ( A = B -> ( ph <-> ps ) ) $.
	reueqd $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ps ) ) $= freueqd_3 freueqd_4 wceq freueqd_0 freueqd_2 freueqd_3 wreu freueqd_0 freueqd_2 freueqd_4 wreu freueqd_1 freueqd_2 freueqd_4 wreu freueqd_0 freueqd_2 freueqd_3 freueqd_4 reueq1 freueqd_3 freueqd_4 wceq freueqd_0 freueqd_1 freueqd_2 freueqd_4 ereueqd_0 reubidv bitrd $.
$}
$( Equality deduction for restricted uniqueness quantifier.  (Contributed
       by Alexander van der Vekens, 17-Jun-2017.) $)
${
	$d x A $.
	$d x B $.
	frmoeqd_0 $f wff ph $.
	frmoeqd_1 $f wff ps $.
	frmoeqd_2 $f set x $.
	frmoeqd_3 $f class A $.
	frmoeqd_4 $f class B $.
	ermoeqd_0 $e |- ( A = B -> ( ph <-> ps ) ) $.
	rmoeqd $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ps ) ) $= frmoeqd_3 frmoeqd_4 wceq frmoeqd_0 frmoeqd_2 frmoeqd_3 wrmo frmoeqd_0 frmoeqd_2 frmoeqd_4 wrmo frmoeqd_1 frmoeqd_2 frmoeqd_4 wrmo frmoeqd_0 frmoeqd_2 frmoeqd_3 frmoeqd_4 rmoeq1 frmoeqd_3 frmoeqd_4 wceq frmoeqd_0 frmoeqd_1 frmoeqd_2 frmoeqd_4 ermoeqd_0 rmobidv bitrd $.
$}
$( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 6-Nov-2007.) $)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	fraleqbidv_0 $f wff ph $.
	fraleqbidv_1 $f wff ps $.
	fraleqbidv_2 $f wff ch $.
	fraleqbidv_3 $f set x $.
	fraleqbidv_4 $f class A $.
	fraleqbidv_5 $f class B $.
	eraleqbidv_0 $e |- ( ph -> A = B ) $.
	eraleqbidv_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	raleqbidv $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $= fraleqbidv_0 fraleqbidv_1 fraleqbidv_3 fraleqbidv_4 wral fraleqbidv_1 fraleqbidv_3 fraleqbidv_5 wral fraleqbidv_2 fraleqbidv_3 fraleqbidv_5 wral fraleqbidv_0 fraleqbidv_1 fraleqbidv_3 fraleqbidv_4 fraleqbidv_5 eraleqbidv_0 raleqdv fraleqbidv_0 fraleqbidv_1 fraleqbidv_2 fraleqbidv_3 fraleqbidv_5 eraleqbidv_1 ralbidv bitrd $.
$}
$( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 6-Nov-2007.) $)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	frexeqbidv_0 $f wff ph $.
	frexeqbidv_1 $f wff ps $.
	frexeqbidv_2 $f wff ch $.
	frexeqbidv_3 $f set x $.
	frexeqbidv_4 $f class A $.
	frexeqbidv_5 $f class B $.
	erexeqbidv_0 $e |- ( ph -> A = B ) $.
	erexeqbidv_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	rexeqbidv $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $= frexeqbidv_0 frexeqbidv_1 frexeqbidv_3 frexeqbidv_4 wrex frexeqbidv_1 frexeqbidv_3 frexeqbidv_5 wrex frexeqbidv_2 frexeqbidv_3 frexeqbidv_5 wrex frexeqbidv_0 frexeqbidv_1 frexeqbidv_3 frexeqbidv_4 frexeqbidv_5 erexeqbidv_0 rexeqdv frexeqbidv_0 frexeqbidv_1 frexeqbidv_2 frexeqbidv_3 frexeqbidv_5 erexeqbidv_1 rexbidv bitrd $.
$}
$( Equality deduction for restricted universal quantifier.  (Contributed by
       Mario Carneiro, 5-Jan-2017.) $)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	fraleqbidva_0 $f wff ph $.
	fraleqbidva_1 $f wff ps $.
	fraleqbidva_2 $f wff ch $.
	fraleqbidva_3 $f set x $.
	fraleqbidva_4 $f class A $.
	fraleqbidva_5 $f class B $.
	eraleqbidva_0 $e |- ( ph -> A = B ) $.
	eraleqbidva_1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	raleqbidva $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $= fraleqbidva_0 fraleqbidva_1 fraleqbidva_3 fraleqbidva_4 wral fraleqbidva_2 fraleqbidva_3 fraleqbidva_4 wral fraleqbidva_2 fraleqbidva_3 fraleqbidva_5 wral fraleqbidva_0 fraleqbidva_1 fraleqbidva_2 fraleqbidva_3 fraleqbidva_4 eraleqbidva_1 ralbidva fraleqbidva_0 fraleqbidva_2 fraleqbidva_3 fraleqbidva_4 fraleqbidva_5 eraleqbidva_0 raleqdv bitrd $.
$}
$( Equality deduction for restricted universal quantifier.  (Contributed by
       Mario Carneiro, 5-Jan-2017.) $)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	frexeqbidva_0 $f wff ph $.
	frexeqbidva_1 $f wff ps $.
	frexeqbidva_2 $f wff ch $.
	frexeqbidva_3 $f set x $.
	frexeqbidva_4 $f class A $.
	frexeqbidva_5 $f class B $.
	erexeqbidva_0 $e |- ( ph -> A = B ) $.
	erexeqbidva_1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	rexeqbidva $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $= frexeqbidva_0 frexeqbidva_1 frexeqbidva_3 frexeqbidva_4 wrex frexeqbidva_2 frexeqbidva_3 frexeqbidva_4 wrex frexeqbidva_2 frexeqbidva_3 frexeqbidva_5 wrex frexeqbidva_0 frexeqbidva_1 frexeqbidva_2 frexeqbidva_3 frexeqbidva_4 erexeqbidva_1 rexbidva frexeqbidva_0 frexeqbidva_2 frexeqbidva_3 frexeqbidva_4 frexeqbidva_5 erexeqbidva_0 rexeqdv bitrd $.
$}
$( Unrestricted "at most one" implies restricted "at most one".  (Contributed
     by NM, 16-Jun-2017.) $)
${
	fmormo_0 $f wff ph $.
	fmormo_1 $f set x $.
	fmormo_2 $f class A $.
	mormo $p |- ( E* x ph -> E* x e. A ph ) $= fmormo_0 fmormo_1 wmo fmormo_1 cv fmormo_2 wcel fmormo_0 wa fmormo_1 wmo fmormo_0 fmormo_1 fmormo_2 wrmo fmormo_0 fmormo_1 cv fmormo_2 wcel fmormo_1 moan fmormo_0 fmormo_1 fmormo_2 df-rmo sylibr $.
$}
$( Restricted uniqueness in terms of "at most one."  (Contributed by NM,
     23-May-1999.)  (Revised by NM, 16-Jun-2017.) $)
${
	freu5_0 $f wff ph $.
	freu5_1 $f set x $.
	freu5_2 $f class A $.
	reu5 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ E* x e. A ph ) ) $= freu5_1 cv freu5_2 wcel freu5_0 wa freu5_1 weu freu5_1 cv freu5_2 wcel freu5_0 wa freu5_1 wex freu5_1 cv freu5_2 wcel freu5_0 wa freu5_1 wmo wa freu5_0 freu5_1 freu5_2 wreu freu5_0 freu5_1 freu5_2 wrex freu5_0 freu5_1 freu5_2 wrmo wa freu5_1 cv freu5_2 wcel freu5_0 wa freu5_1 eu5 freu5_0 freu5_1 freu5_2 df-reu freu5_0 freu5_1 freu5_2 wrex freu5_1 cv freu5_2 wcel freu5_0 wa freu5_1 wex freu5_0 freu5_1 freu5_2 wrmo freu5_1 cv freu5_2 wcel freu5_0 wa freu5_1 wmo freu5_0 freu5_1 freu5_2 df-rex freu5_0 freu5_1 freu5_2 df-rmo anbi12i 3bitr4i $.
$}
$( Restricted unique existence implies restricted existence.  (Contributed by
     NM, 19-Aug-1999.) $)
${
	freurex_0 $f wff ph $.
	freurex_1 $f set x $.
	freurex_2 $f class A $.
	reurex $p |- ( E! x e. A ph -> E. x e. A ph ) $= freurex_0 freurex_1 freurex_2 wreu freurex_0 freurex_1 freurex_2 wrex freurex_0 freurex_1 freurex_2 wrmo freurex_0 freurex_1 freurex_2 reu5 simplbi $.
$}
$( Restricted existential uniqueness implies restricted "at most one."
     (Contributed by NM, 16-Jun-2017.) $)
${
	freurmo_0 $f wff ph $.
	freurmo_1 $f set x $.
	freurmo_2 $f class A $.
	reurmo $p |- ( E! x e. A ph -> E* x e. A ph ) $= freurmo_0 freurmo_1 freurmo_2 wreu freurmo_0 freurmo_1 freurmo_2 wrex freurmo_0 freurmo_1 freurmo_2 wrmo freurmo_0 freurmo_1 freurmo_2 reu5 simprbi $.
$}
$( Restricted "at most one" in term of uniqueness.  (Contributed by NM,
     16-Jun-2017.) $)
${
	frmo5_0 $f wff ph $.
	frmo5_1 $f set x $.
	frmo5_2 $f class A $.
	rmo5 $p |- ( E* x e. A ph <-> ( E. x e. A ph -> E! x e. A ph ) ) $= frmo5_1 cv frmo5_2 wcel frmo5_0 wa frmo5_1 wmo frmo5_1 cv frmo5_2 wcel frmo5_0 wa frmo5_1 wex frmo5_1 cv frmo5_2 wcel frmo5_0 wa frmo5_1 weu wi frmo5_0 frmo5_1 frmo5_2 wrmo frmo5_0 frmo5_1 frmo5_2 wrex frmo5_0 frmo5_1 frmo5_2 wreu wi frmo5_1 cv frmo5_2 wcel frmo5_0 wa frmo5_1 df-mo frmo5_0 frmo5_1 frmo5_2 df-rmo frmo5_0 frmo5_1 frmo5_2 wrex frmo5_1 cv frmo5_2 wcel frmo5_0 wa frmo5_1 wex frmo5_0 frmo5_1 frmo5_2 wreu frmo5_1 cv frmo5_2 wcel frmo5_0 wa frmo5_1 weu frmo5_0 frmo5_1 frmo5_2 df-rex frmo5_0 frmo5_1 frmo5_2 df-reu imbi12i 3bitr4i $.
$}
$( Nonexistence implies restricted "at most one".  (Contributed by NM,
     17-Jun-2017.) $)
${
	fnrexrmo_0 $f wff ph $.
	fnrexrmo_1 $f set x $.
	fnrexrmo_2 $f class A $.
	nrexrmo $p |- ( -. E. x e. A ph -> E* x e. A ph ) $= fnrexrmo_0 fnrexrmo_1 fnrexrmo_2 wrex wn fnrexrmo_0 fnrexrmo_1 fnrexrmo_2 wrex fnrexrmo_0 fnrexrmo_1 fnrexrmo_2 wreu wi fnrexrmo_0 fnrexrmo_1 fnrexrmo_2 wrmo fnrexrmo_0 fnrexrmo_1 fnrexrmo_2 wrex fnrexrmo_0 fnrexrmo_1 fnrexrmo_2 wreu pm2.21 fnrexrmo_0 fnrexrmo_1 fnrexrmo_2 rmo5 sylibr $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 7-Mar-2004.)  (Revised by Mario Carneiro,
       9-Oct-2016.) $)
${
	$d x z $.
	$d y z $.
	$d z A $.
	$d z ps $.
	$d z ph $.
	icbvralf_0 $f set z $.
	fcbvralf_0 $f wff ph $.
	fcbvralf_1 $f wff ps $.
	fcbvralf_2 $f set x $.
	fcbvralf_3 $f set y $.
	fcbvralf_4 $f class A $.
	ecbvralf_0 $e |- F/_ x A $.
	ecbvralf_1 $e |- F/_ y A $.
	ecbvralf_2 $e |- F/ y ph $.
	ecbvralf_3 $e |- F/ x ps $.
	ecbvralf_4 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvralf $p |- ( A. x e. A ph <-> A. y e. A ps ) $= fcbvralf_2 cv fcbvralf_4 wcel fcbvralf_0 wi fcbvralf_2 wal fcbvralf_3 cv fcbvralf_4 wcel fcbvralf_1 wi fcbvralf_3 wal fcbvralf_0 fcbvralf_2 fcbvralf_4 wral fcbvralf_1 fcbvralf_3 fcbvralf_4 wral fcbvralf_2 cv fcbvralf_4 wcel fcbvralf_0 wi fcbvralf_2 wal icbvralf_0 cv fcbvralf_4 wcel fcbvralf_0 fcbvralf_2 icbvralf_0 wsb wi icbvralf_0 wal fcbvralf_3 cv fcbvralf_4 wcel fcbvralf_1 wi fcbvralf_3 wal fcbvralf_2 cv fcbvralf_4 wcel fcbvralf_0 wi icbvralf_0 cv fcbvralf_4 wcel fcbvralf_0 fcbvralf_2 icbvralf_0 wsb wi fcbvralf_2 icbvralf_0 fcbvralf_2 cv fcbvralf_4 wcel fcbvralf_0 wi icbvralf_0 nfv icbvralf_0 cv fcbvralf_4 wcel fcbvralf_0 fcbvralf_2 icbvralf_0 wsb fcbvralf_2 fcbvralf_2 icbvralf_0 fcbvralf_4 ecbvralf_0 nfcri fcbvralf_0 fcbvralf_2 icbvralf_0 nfs1v nfim fcbvralf_2 cv icbvralf_0 cv wceq fcbvralf_2 cv fcbvralf_4 wcel icbvralf_0 cv fcbvralf_4 wcel fcbvralf_0 fcbvralf_0 fcbvralf_2 icbvralf_0 wsb fcbvralf_2 cv icbvralf_0 cv fcbvralf_4 eleq1 fcbvralf_0 fcbvralf_2 icbvralf_0 sbequ12 imbi12d cbval icbvralf_0 cv fcbvralf_4 wcel fcbvralf_0 fcbvralf_2 icbvralf_0 wsb wi fcbvralf_3 cv fcbvralf_4 wcel fcbvralf_1 wi icbvralf_0 fcbvralf_3 icbvralf_0 cv fcbvralf_4 wcel fcbvralf_0 fcbvralf_2 icbvralf_0 wsb fcbvralf_3 fcbvralf_3 icbvralf_0 fcbvralf_4 ecbvralf_1 nfcri fcbvralf_0 fcbvralf_2 icbvralf_0 fcbvralf_3 ecbvralf_2 nfsb nfim fcbvralf_3 cv fcbvralf_4 wcel fcbvralf_1 wi icbvralf_0 nfv icbvralf_0 cv fcbvralf_3 cv wceq icbvralf_0 cv fcbvralf_4 wcel fcbvralf_3 cv fcbvralf_4 wcel fcbvralf_0 fcbvralf_2 icbvralf_0 wsb fcbvralf_1 icbvralf_0 cv fcbvralf_3 cv fcbvralf_4 eleq1 icbvralf_0 cv fcbvralf_3 cv wceq fcbvralf_0 fcbvralf_2 icbvralf_0 wsb fcbvralf_0 fcbvralf_2 fcbvralf_3 wsb fcbvralf_1 fcbvralf_0 icbvralf_0 fcbvralf_3 fcbvralf_2 sbequ fcbvralf_0 fcbvralf_1 fcbvralf_2 fcbvralf_3 ecbvralf_3 ecbvralf_4 sbie syl6bb imbi12d cbval bitri fcbvralf_0 fcbvralf_2 fcbvralf_4 df-ral fcbvralf_1 fcbvralf_3 fcbvralf_4 df-ral 3bitr4i $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by FL, 27-Apr-2008.)  (Revised by Mario Carneiro,
       9-Oct-2016.) $)
${
	fcbvrexf_0 $f wff ph $.
	fcbvrexf_1 $f wff ps $.
	fcbvrexf_2 $f set x $.
	fcbvrexf_3 $f set y $.
	fcbvrexf_4 $f class A $.
	ecbvrexf_0 $e |- F/_ x A $.
	ecbvrexf_1 $e |- F/_ y A $.
	ecbvrexf_2 $e |- F/ y ph $.
	ecbvrexf_3 $e |- F/ x ps $.
	ecbvrexf_4 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrexf $p |- ( E. x e. A ph <-> E. y e. A ps ) $= fcbvrexf_0 wn fcbvrexf_2 fcbvrexf_4 wral wn fcbvrexf_1 wn fcbvrexf_3 fcbvrexf_4 wral wn fcbvrexf_0 fcbvrexf_2 fcbvrexf_4 wrex fcbvrexf_1 fcbvrexf_3 fcbvrexf_4 wrex fcbvrexf_0 wn fcbvrexf_2 fcbvrexf_4 wral fcbvrexf_1 wn fcbvrexf_3 fcbvrexf_4 wral fcbvrexf_0 wn fcbvrexf_1 wn fcbvrexf_2 fcbvrexf_3 fcbvrexf_4 ecbvrexf_0 ecbvrexf_1 fcbvrexf_0 fcbvrexf_3 ecbvrexf_2 nfn fcbvrexf_1 fcbvrexf_2 ecbvrexf_3 nfn fcbvrexf_2 cv fcbvrexf_3 cv wceq fcbvrexf_0 fcbvrexf_1 ecbvrexf_4 notbid cbvralf notbii fcbvrexf_0 fcbvrexf_2 fcbvrexf_4 dfrex2 fcbvrexf_1 fcbvrexf_3 fcbvrexf_4 dfrex2 3bitr4i $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 31-Jul-2003.) $)
${
	$d x A $.
	$d y A $.
	fcbvral_0 $f wff ph $.
	fcbvral_1 $f wff ps $.
	fcbvral_2 $f set x $.
	fcbvral_3 $f set y $.
	fcbvral_4 $f class A $.
	ecbvral_0 $e |- F/ y ph $.
	ecbvral_1 $e |- F/ x ps $.
	ecbvral_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvral $p |- ( A. x e. A ph <-> A. y e. A ps ) $= fcbvral_0 fcbvral_1 fcbvral_2 fcbvral_3 fcbvral_4 fcbvral_2 fcbvral_4 nfcv fcbvral_3 fcbvral_4 nfcv ecbvral_0 ecbvral_1 ecbvral_2 cbvralf $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 31-Jul-2003.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)
${
	$d x A $.
	$d y A $.
	fcbvrex_0 $f wff ph $.
	fcbvrex_1 $f wff ps $.
	fcbvrex_2 $f set x $.
	fcbvrex_3 $f set y $.
	fcbvrex_4 $f class A $.
	ecbvrex_0 $e |- F/ y ph $.
	ecbvrex_1 $e |- F/ x ps $.
	ecbvrex_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrex $p |- ( E. x e. A ph <-> E. y e. A ps ) $= fcbvrex_0 fcbvrex_1 fcbvrex_2 fcbvrex_3 fcbvrex_4 fcbvrex_2 fcbvrex_4 nfcv fcbvrex_3 fcbvrex_4 nfcv ecbvrex_0 ecbvrex_1 ecbvrex_2 cbvrexf $.
$}
$( Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by Mario Carneiro, 15-Oct-2016.) $)
${
	$d x z A $.
	$d y z A $.
	$d z ph $.
	$d z ps $.
	icbvreu_0 $f set z $.
	fcbvreu_0 $f wff ph $.
	fcbvreu_1 $f wff ps $.
	fcbvreu_2 $f set x $.
	fcbvreu_3 $f set y $.
	fcbvreu_4 $f class A $.
	ecbvreu_0 $e |- F/ y ph $.
	ecbvreu_1 $e |- F/ x ps $.
	ecbvreu_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvreu $p |- ( E! x e. A ph <-> E! y e. A ps ) $= fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_0 wa fcbvreu_2 weu fcbvreu_3 cv fcbvreu_4 wcel fcbvreu_1 wa fcbvreu_3 weu fcbvreu_0 fcbvreu_2 fcbvreu_4 wreu fcbvreu_1 fcbvreu_3 fcbvreu_4 wreu fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_0 wa fcbvreu_2 weu fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_0 wa fcbvreu_2 icbvreu_0 wsb icbvreu_0 weu fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_2 icbvreu_0 wsb fcbvreu_0 fcbvreu_2 icbvreu_0 wsb wa icbvreu_0 weu fcbvreu_3 cv fcbvreu_4 wcel fcbvreu_1 wa fcbvreu_3 weu fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_0 wa fcbvreu_2 icbvreu_0 fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_0 wa icbvreu_0 nfv sb8eu fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_0 wa fcbvreu_2 icbvreu_0 wsb fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_2 icbvreu_0 wsb fcbvreu_0 fcbvreu_2 icbvreu_0 wsb wa icbvreu_0 fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_0 fcbvreu_2 icbvreu_0 sban eubii fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_2 icbvreu_0 wsb fcbvreu_0 fcbvreu_2 icbvreu_0 wsb wa icbvreu_0 weu icbvreu_0 cv fcbvreu_4 wcel fcbvreu_0 fcbvreu_2 icbvreu_0 wsb wa icbvreu_0 weu fcbvreu_3 cv fcbvreu_4 wcel fcbvreu_1 wa fcbvreu_3 weu fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_2 icbvreu_0 wsb fcbvreu_0 fcbvreu_2 icbvreu_0 wsb wa icbvreu_0 cv fcbvreu_4 wcel fcbvreu_0 fcbvreu_2 icbvreu_0 wsb wa icbvreu_0 fcbvreu_2 cv fcbvreu_4 wcel fcbvreu_2 icbvreu_0 wsb icbvreu_0 cv fcbvreu_4 wcel fcbvreu_0 fcbvreu_2 icbvreu_0 wsb icbvreu_0 fcbvreu_2 fcbvreu_4 clelsb3 anbi1i eubii icbvreu_0 cv fcbvreu_4 wcel fcbvreu_0 fcbvreu_2 icbvreu_0 wsb wa fcbvreu_3 cv fcbvreu_4 wcel fcbvreu_1 wa icbvreu_0 fcbvreu_3 icbvreu_0 cv fcbvreu_4 wcel fcbvreu_0 fcbvreu_2 icbvreu_0 wsb fcbvreu_3 icbvreu_0 cv fcbvreu_4 wcel fcbvreu_3 nfv fcbvreu_0 fcbvreu_2 icbvreu_0 fcbvreu_3 ecbvreu_0 nfsb nfan fcbvreu_3 cv fcbvreu_4 wcel fcbvreu_1 wa icbvreu_0 nfv icbvreu_0 cv fcbvreu_3 cv wceq icbvreu_0 cv fcbvreu_4 wcel fcbvreu_3 cv fcbvreu_4 wcel fcbvreu_0 fcbvreu_2 icbvreu_0 wsb fcbvreu_1 icbvreu_0 cv fcbvreu_3 cv fcbvreu_4 eleq1 icbvreu_0 cv fcbvreu_3 cv wceq fcbvreu_0 fcbvreu_2 icbvreu_0 wsb fcbvreu_0 fcbvreu_2 fcbvreu_3 wsb fcbvreu_1 fcbvreu_0 icbvreu_0 fcbvreu_3 fcbvreu_2 sbequ fcbvreu_0 fcbvreu_1 fcbvreu_2 fcbvreu_3 ecbvreu_1 ecbvreu_2 sbie syl6bb anbi12d cbveu bitri 3bitri fcbvreu_0 fcbvreu_2 fcbvreu_4 df-reu fcbvreu_1 fcbvreu_3 fcbvreu_4 df-reu 3bitr4i $.
$}
$( Change the bound variable of restricted "at most one" using implicit
       substitution.  (Contributed by NM, 16-Jun-2017.) $)
${
	$d x A $.
	$d y A $.
	fcbvrmo_0 $f wff ph $.
	fcbvrmo_1 $f wff ps $.
	fcbvrmo_2 $f set x $.
	fcbvrmo_3 $f set y $.
	fcbvrmo_4 $f class A $.
	ecbvrmo_0 $e |- F/ y ph $.
	ecbvrmo_1 $e |- F/ x ps $.
	ecbvrmo_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrmo $p |- ( E* x e. A ph <-> E* y e. A ps ) $= fcbvrmo_0 fcbvrmo_2 fcbvrmo_4 wrex fcbvrmo_0 fcbvrmo_2 fcbvrmo_4 wreu wi fcbvrmo_1 fcbvrmo_3 fcbvrmo_4 wrex fcbvrmo_1 fcbvrmo_3 fcbvrmo_4 wreu wi fcbvrmo_0 fcbvrmo_2 fcbvrmo_4 wrmo fcbvrmo_1 fcbvrmo_3 fcbvrmo_4 wrmo fcbvrmo_0 fcbvrmo_2 fcbvrmo_4 wrex fcbvrmo_1 fcbvrmo_3 fcbvrmo_4 wrex fcbvrmo_0 fcbvrmo_2 fcbvrmo_4 wreu fcbvrmo_1 fcbvrmo_3 fcbvrmo_4 wreu fcbvrmo_0 fcbvrmo_1 fcbvrmo_2 fcbvrmo_3 fcbvrmo_4 ecbvrmo_0 ecbvrmo_1 ecbvrmo_2 cbvrex fcbvrmo_0 fcbvrmo_1 fcbvrmo_2 fcbvrmo_3 fcbvrmo_4 ecbvrmo_0 ecbvrmo_1 ecbvrmo_2 cbvreu imbi12i fcbvrmo_0 fcbvrmo_2 fcbvrmo_4 rmo5 fcbvrmo_1 fcbvrmo_3 fcbvrmo_4 rmo5 3bitr4i $.
$}
$( Change the bound variable of a restricted universal quantifier using
       implicit substitution.  (Contributed by NM, 28-Jan-1997.) $)
${
	$d x A $.
	$d y A $.
	$d y ph $.
	$d x ps $.
	fcbvralv_0 $f wff ph $.
	fcbvralv_1 $f wff ps $.
	fcbvralv_2 $f set x $.
	fcbvralv_3 $f set y $.
	fcbvralv_4 $f class A $.
	ecbvralv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvralv $p |- ( A. x e. A ph <-> A. y e. A ps ) $= fcbvralv_0 fcbvralv_1 fcbvralv_2 fcbvralv_3 fcbvralv_4 fcbvralv_0 fcbvralv_3 nfv fcbvralv_1 fcbvralv_2 nfv ecbvralv_0 cbvral $.
$}
$( Change the bound variable of a restricted existential quantifier using
       implicit substitution.  (Contributed by NM, 2-Jun-1998.) $)
${
	$d x A $.
	$d y A $.
	$d y ph $.
	$d x ps $.
	fcbvrexv_0 $f wff ph $.
	fcbvrexv_1 $f wff ps $.
	fcbvrexv_2 $f set x $.
	fcbvrexv_3 $f set y $.
	fcbvrexv_4 $f class A $.
	ecbvrexv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrexv $p |- ( E. x e. A ph <-> E. y e. A ps ) $= fcbvrexv_0 fcbvrexv_1 fcbvrexv_2 fcbvrexv_3 fcbvrexv_4 fcbvrexv_0 fcbvrexv_3 nfv fcbvrexv_1 fcbvrexv_2 nfv ecbvrexv_0 cbvrex $.
$}
$( Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by NM, 5-Apr-2004.)  (Revised by
       Mario Carneiro, 15-Oct-2016.) $)
${
	$d x A $.
	$d y A $.
	$d y ph $.
	$d x ps $.
	fcbvreuv_0 $f wff ph $.
	fcbvreuv_1 $f wff ps $.
	fcbvreuv_2 $f set x $.
	fcbvreuv_3 $f set y $.
	fcbvreuv_4 $f class A $.
	ecbvreuv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvreuv $p |- ( E! x e. A ph <-> E! y e. A ps ) $= fcbvreuv_0 fcbvreuv_1 fcbvreuv_2 fcbvreuv_3 fcbvreuv_4 fcbvreuv_0 fcbvreuv_3 nfv fcbvreuv_1 fcbvreuv_2 nfv ecbvreuv_0 cbvreu $.
$}
$( Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by Alexander van der Vekens,
       17-Jun-2017.) $)
${
	$d x A $.
	$d y A $.
	$d y ph $.
	$d x ps $.
	fcbvrmov_0 $f wff ph $.
	fcbvrmov_1 $f wff ps $.
	fcbvrmov_2 $f set x $.
	fcbvrmov_3 $f set y $.
	fcbvrmov_4 $f class A $.
	ecbvrmov_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrmov $p |- ( E* x e. A ph <-> E* y e. A ps ) $= fcbvrmov_0 fcbvrmov_1 fcbvrmov_2 fcbvrmov_3 fcbvrmov_4 fcbvrmov_0 fcbvrmov_3 nfv fcbvrmov_1 fcbvrmov_2 nfv ecbvrmov_0 cbvrmo $.
$}
$( Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution which also changes the quantifier
       domain.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
${
	$d A y $.
	$d ps y $.
	$d B x $.
	$d ch x $.
	$d x ph y $.
	fcbvraldva2_0 $f wff ph $.
	fcbvraldva2_1 $f wff ps $.
	fcbvraldva2_2 $f wff ch $.
	fcbvraldva2_3 $f set x $.
	fcbvraldva2_4 $f set y $.
	fcbvraldva2_5 $f class A $.
	fcbvraldva2_6 $f class B $.
	ecbvraldva2_0 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	ecbvraldva2_1 $e |- ( ( ph /\ x = y ) -> A = B ) $.
	cbvraldva2 $p |- ( ph -> ( A. x e. A ps <-> A. y e. B ch ) ) $= fcbvraldva2_0 fcbvraldva2_3 cv fcbvraldva2_5 wcel fcbvraldva2_1 wi fcbvraldva2_3 wal fcbvraldva2_4 cv fcbvraldva2_6 wcel fcbvraldva2_2 wi fcbvraldva2_4 wal fcbvraldva2_1 fcbvraldva2_3 fcbvraldva2_5 wral fcbvraldva2_2 fcbvraldva2_4 fcbvraldva2_6 wral fcbvraldva2_0 fcbvraldva2_3 cv fcbvraldva2_5 wcel fcbvraldva2_1 wi fcbvraldva2_4 cv fcbvraldva2_6 wcel fcbvraldva2_2 wi fcbvraldva2_3 fcbvraldva2_4 fcbvraldva2_0 fcbvraldva2_3 fcbvraldva2_4 weq wa fcbvraldva2_3 cv fcbvraldva2_5 wcel fcbvraldva2_4 cv fcbvraldva2_6 wcel fcbvraldva2_1 fcbvraldva2_2 fcbvraldva2_0 fcbvraldva2_3 fcbvraldva2_4 weq wa fcbvraldva2_3 cv fcbvraldva2_4 cv fcbvraldva2_5 fcbvraldva2_6 fcbvraldva2_0 fcbvraldva2_3 fcbvraldva2_4 weq simpr ecbvraldva2_1 eleq12d ecbvraldva2_0 imbi12d cbvaldva fcbvraldva2_1 fcbvraldva2_3 fcbvraldva2_5 df-ral fcbvraldva2_2 fcbvraldva2_4 fcbvraldva2_6 df-ral 3bitr4g $.
$}
$( Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution which also changes the quantifier
       domain.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
${
	$d A y $.
	$d ps y $.
	$d B x $.
	$d ch x $.
	$d x ph y $.
	fcbvrexdva2_0 $f wff ph $.
	fcbvrexdva2_1 $f wff ps $.
	fcbvrexdva2_2 $f wff ch $.
	fcbvrexdva2_3 $f set x $.
	fcbvrexdva2_4 $f set y $.
	fcbvrexdva2_5 $f class A $.
	fcbvrexdva2_6 $f class B $.
	ecbvrexdva2_0 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	ecbvrexdva2_1 $e |- ( ( ph /\ x = y ) -> A = B ) $.
	cbvrexdva2 $p |- ( ph -> ( E. x e. A ps <-> E. y e. B ch ) ) $= fcbvrexdva2_0 fcbvrexdva2_3 cv fcbvrexdva2_5 wcel fcbvrexdva2_1 wa fcbvrexdva2_3 wex fcbvrexdva2_4 cv fcbvrexdva2_6 wcel fcbvrexdva2_2 wa fcbvrexdva2_4 wex fcbvrexdva2_1 fcbvrexdva2_3 fcbvrexdva2_5 wrex fcbvrexdva2_2 fcbvrexdva2_4 fcbvrexdva2_6 wrex fcbvrexdva2_0 fcbvrexdva2_3 cv fcbvrexdva2_5 wcel fcbvrexdva2_1 wa fcbvrexdva2_4 cv fcbvrexdva2_6 wcel fcbvrexdva2_2 wa fcbvrexdva2_3 fcbvrexdva2_4 fcbvrexdva2_0 fcbvrexdva2_3 fcbvrexdva2_4 weq wa fcbvrexdva2_3 cv fcbvrexdva2_5 wcel fcbvrexdva2_4 cv fcbvrexdva2_6 wcel fcbvrexdva2_1 fcbvrexdva2_2 fcbvrexdva2_0 fcbvrexdva2_3 fcbvrexdva2_4 weq wa fcbvrexdva2_3 cv fcbvrexdva2_4 cv fcbvrexdva2_5 fcbvrexdva2_6 fcbvrexdva2_0 fcbvrexdva2_3 fcbvrexdva2_4 weq simpr ecbvrexdva2_1 eleq12d ecbvrexdva2_0 anbi12d cbvexdva fcbvrexdva2_1 fcbvrexdva2_3 fcbvrexdva2_5 df-rex fcbvrexdva2_2 fcbvrexdva2_4 fcbvrexdva2_6 df-rex 3bitr4g $.
$}
$( Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution.  Deduction form.  (Contributed by
       David Moews, 1-May-2017.) $)
${
	$d ps y $.
	$d ch x $.
	$d A x y $.
	$d x ph y $.
	fcbvraldva_0 $f wff ph $.
	fcbvraldva_1 $f wff ps $.
	fcbvraldva_2 $f wff ch $.
	fcbvraldva_3 $f set x $.
	fcbvraldva_4 $f set y $.
	fcbvraldva_5 $f class A $.
	ecbvraldva_0 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	cbvraldva $p |- ( ph -> ( A. x e. A ps <-> A. y e. A ch ) ) $= fcbvraldva_0 fcbvraldva_1 fcbvraldva_2 fcbvraldva_3 fcbvraldva_4 fcbvraldva_5 fcbvraldva_5 ecbvraldva_0 fcbvraldva_0 fcbvraldva_3 fcbvraldva_4 weq wa fcbvraldva_5 eqidd cbvraldva2 $.
$}
$( Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution.  Deduction form.  (Contributed by
       David Moews, 1-May-2017.) $)
${
	$d ps y $.
	$d ch x $.
	$d A x y $.
	$d x ph y $.
	fcbvrexdva_0 $f wff ph $.
	fcbvrexdva_1 $f wff ps $.
	fcbvrexdva_2 $f wff ch $.
	fcbvrexdva_3 $f set x $.
	fcbvrexdva_4 $f set y $.
	fcbvrexdva_5 $f class A $.
	ecbvrexdva_0 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
	cbvrexdva $p |- ( ph -> ( E. x e. A ps <-> E. y e. A ch ) ) $= fcbvrexdva_0 fcbvrexdva_1 fcbvrexdva_2 fcbvrexdva_3 fcbvrexdva_4 fcbvrexdva_5 fcbvrexdva_5 ecbvrexdva_0 fcbvrexdva_0 fcbvrexdva_3 fcbvrexdva_4 weq wa fcbvrexdva_5 eqidd cbvrexdva2 $.
$}
$( Change bound variables of double restricted universal quantification,
       using implicit substitution.  (Contributed by NM, 10-Aug-2004.) $)
${
	$d x A $.
	$d z A $.
	$d x y B $.
	$d z y B $.
	$d w B $.
	$d z ph $.
	$d y ps $.
	$d x ch $.
	$d w ch $.
	fcbvral2v_0 $f wff ph $.
	fcbvral2v_1 $f wff ps $.
	fcbvral2v_2 $f wff ch $.
	fcbvral2v_3 $f set x $.
	fcbvral2v_4 $f set y $.
	fcbvral2v_5 $f set z $.
	fcbvral2v_6 $f set w $.
	fcbvral2v_7 $f class A $.
	fcbvral2v_8 $f class B $.
	ecbvral2v_0 $e |- ( x = z -> ( ph <-> ch ) ) $.
	ecbvral2v_1 $e |- ( y = w -> ( ch <-> ps ) ) $.
	cbvral2v $p |- ( A. x e. A A. y e. B ph <-> A. z e. A A. w e. B ps ) $= fcbvral2v_0 fcbvral2v_4 fcbvral2v_8 wral fcbvral2v_3 fcbvral2v_7 wral fcbvral2v_2 fcbvral2v_4 fcbvral2v_8 wral fcbvral2v_5 fcbvral2v_7 wral fcbvral2v_1 fcbvral2v_6 fcbvral2v_8 wral fcbvral2v_5 fcbvral2v_7 wral fcbvral2v_0 fcbvral2v_4 fcbvral2v_8 wral fcbvral2v_2 fcbvral2v_4 fcbvral2v_8 wral fcbvral2v_3 fcbvral2v_5 fcbvral2v_7 fcbvral2v_3 cv fcbvral2v_5 cv wceq fcbvral2v_0 fcbvral2v_2 fcbvral2v_4 fcbvral2v_8 ecbvral2v_0 ralbidv cbvralv fcbvral2v_2 fcbvral2v_4 fcbvral2v_8 wral fcbvral2v_1 fcbvral2v_6 fcbvral2v_8 wral fcbvral2v_5 fcbvral2v_7 fcbvral2v_2 fcbvral2v_1 fcbvral2v_4 fcbvral2v_6 fcbvral2v_8 ecbvral2v_1 cbvralv ralbii bitri $.
$}
$( Change bound variables of double restricted universal quantification,
       using implicit substitution.  (Contributed by FL, 2-Jul-2012.) $)
${
	$d A x $.
	$d A z $.
	$d B w $.
	$d B x y $.
	$d B z y $.
	$d ch w $.
	$d ch x $.
	$d ph z $.
	$d ps y $.
	fcbvrex2v_0 $f wff ph $.
	fcbvrex2v_1 $f wff ps $.
	fcbvrex2v_2 $f wff ch $.
	fcbvrex2v_3 $f set x $.
	fcbvrex2v_4 $f set y $.
	fcbvrex2v_5 $f set z $.
	fcbvrex2v_6 $f set w $.
	fcbvrex2v_7 $f class A $.
	fcbvrex2v_8 $f class B $.
	ecbvrex2v_0 $e |- ( x = z -> ( ph <-> ch ) ) $.
	ecbvrex2v_1 $e |- ( y = w -> ( ch <-> ps ) ) $.
	cbvrex2v $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B ps ) $= fcbvrex2v_0 fcbvrex2v_4 fcbvrex2v_8 wrex fcbvrex2v_3 fcbvrex2v_7 wrex fcbvrex2v_2 fcbvrex2v_4 fcbvrex2v_8 wrex fcbvrex2v_5 fcbvrex2v_7 wrex fcbvrex2v_1 fcbvrex2v_6 fcbvrex2v_8 wrex fcbvrex2v_5 fcbvrex2v_7 wrex fcbvrex2v_0 fcbvrex2v_4 fcbvrex2v_8 wrex fcbvrex2v_2 fcbvrex2v_4 fcbvrex2v_8 wrex fcbvrex2v_3 fcbvrex2v_5 fcbvrex2v_7 fcbvrex2v_3 fcbvrex2v_5 weq fcbvrex2v_0 fcbvrex2v_2 fcbvrex2v_4 fcbvrex2v_8 ecbvrex2v_0 rexbidv cbvrexv fcbvrex2v_2 fcbvrex2v_4 fcbvrex2v_8 wrex fcbvrex2v_1 fcbvrex2v_6 fcbvrex2v_8 wrex fcbvrex2v_5 fcbvrex2v_7 fcbvrex2v_2 fcbvrex2v_1 fcbvrex2v_4 fcbvrex2v_6 fcbvrex2v_8 ecbvrex2v_1 cbvrexv rexbii bitri $.
$}
$( Change bound variables of triple restricted universal quantification,
       using implicit substitution.  (Contributed by NM, 10-May-2005.) $)
${
	$d w ph $.
	$d z ps $.
	$d x ch $.
	$d v ch $.
	$d y u th $.
	$d x A $.
	$d w A $.
	$d x y B $.
	$d w y B $.
	$d v B $.
	$d x y z C $.
	$d w y z C $.
	$d v z C $.
	$d z y C $.
	$d z C $.
	$d u C $.
	fcbvral3v_0 $f wff ph $.
	fcbvral3v_1 $f wff ps $.
	fcbvral3v_2 $f wff ch $.
	fcbvral3v_3 $f wff th $.
	fcbvral3v_4 $f set x $.
	fcbvral3v_5 $f set y $.
	fcbvral3v_6 $f set z $.
	fcbvral3v_7 $f set w $.
	fcbvral3v_8 $f set v $.
	fcbvral3v_9 $f set u $.
	fcbvral3v_10 $f class A $.
	fcbvral3v_11 $f class B $.
	fcbvral3v_12 $f class C $.
	ecbvral3v_0 $e |- ( x = w -> ( ph <-> ch ) ) $.
	ecbvral3v_1 $e |- ( y = v -> ( ch <-> th ) ) $.
	ecbvral3v_2 $e |- ( z = u -> ( th <-> ps ) ) $.
	cbvral3v $p |- ( A. x e. A A. y e. B A. z e. C ph <-> A. w e. A A. v e. B A. u e. C ps ) $= fcbvral3v_0 fcbvral3v_6 fcbvral3v_12 wral fcbvral3v_5 fcbvral3v_11 wral fcbvral3v_4 fcbvral3v_10 wral fcbvral3v_2 fcbvral3v_6 fcbvral3v_12 wral fcbvral3v_5 fcbvral3v_11 wral fcbvral3v_7 fcbvral3v_10 wral fcbvral3v_1 fcbvral3v_9 fcbvral3v_12 wral fcbvral3v_8 fcbvral3v_11 wral fcbvral3v_7 fcbvral3v_10 wral fcbvral3v_0 fcbvral3v_6 fcbvral3v_12 wral fcbvral3v_5 fcbvral3v_11 wral fcbvral3v_2 fcbvral3v_6 fcbvral3v_12 wral fcbvral3v_5 fcbvral3v_11 wral fcbvral3v_4 fcbvral3v_7 fcbvral3v_10 fcbvral3v_4 cv fcbvral3v_7 cv wceq fcbvral3v_0 fcbvral3v_2 fcbvral3v_5 fcbvral3v_6 fcbvral3v_11 fcbvral3v_12 ecbvral3v_0 2ralbidv cbvralv fcbvral3v_2 fcbvral3v_6 fcbvral3v_12 wral fcbvral3v_5 fcbvral3v_11 wral fcbvral3v_1 fcbvral3v_9 fcbvral3v_12 wral fcbvral3v_8 fcbvral3v_11 wral fcbvral3v_7 fcbvral3v_10 fcbvral3v_2 fcbvral3v_1 fcbvral3v_3 fcbvral3v_5 fcbvral3v_6 fcbvral3v_8 fcbvral3v_9 fcbvral3v_11 fcbvral3v_12 ecbvral3v_1 ecbvral3v_2 cbvral2v ralbii bitri $.
$}
$( Change bound variable by using a substitution.  (Contributed by NM,
       20-Nov-2005.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)
${
	$d z x A $.
	$d y A $.
	$d z y ph $.
	icbvralsv_0 $f set z $.
	fcbvralsv_0 $f wff ph $.
	fcbvralsv_1 $f set x $.
	fcbvralsv_2 $f set y $.
	fcbvralsv_3 $f class A $.
	cbvralsv $p |- ( A. x e. A ph <-> A. y e. A [ y / x ] ph ) $= fcbvralsv_0 fcbvralsv_1 fcbvralsv_3 wral fcbvralsv_0 fcbvralsv_1 icbvralsv_0 wsb icbvralsv_0 fcbvralsv_3 wral fcbvralsv_0 fcbvralsv_1 fcbvralsv_2 wsb fcbvralsv_2 fcbvralsv_3 wral fcbvralsv_0 fcbvralsv_0 fcbvralsv_1 icbvralsv_0 wsb fcbvralsv_1 icbvralsv_0 fcbvralsv_3 fcbvralsv_0 icbvralsv_0 nfv fcbvralsv_0 fcbvralsv_1 icbvralsv_0 nfs1v fcbvralsv_0 fcbvralsv_1 icbvralsv_0 sbequ12 cbvral fcbvralsv_0 fcbvralsv_1 icbvralsv_0 wsb fcbvralsv_0 fcbvralsv_1 fcbvralsv_2 wsb icbvralsv_0 fcbvralsv_2 fcbvralsv_3 fcbvralsv_0 fcbvralsv_1 icbvralsv_0 fcbvralsv_2 fcbvralsv_0 fcbvralsv_2 nfv nfsb fcbvralsv_0 fcbvralsv_1 fcbvralsv_2 wsb icbvralsv_0 nfv fcbvralsv_0 icbvralsv_0 fcbvralsv_2 fcbvralsv_1 sbequ cbvral bitri $.
$}
$( Change bound variable by using a substitution.  (Contributed by NM,
       2-Mar-2008.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)
${
	$d z x A $.
	$d y z ph $.
	$d y A $.
	icbvrexsv_0 $f set z $.
	fcbvrexsv_0 $f wff ph $.
	fcbvrexsv_1 $f set x $.
	fcbvrexsv_2 $f set y $.
	fcbvrexsv_3 $f class A $.
	cbvrexsv $p |- ( E. x e. A ph <-> E. y e. A [ y / x ] ph ) $= fcbvrexsv_0 fcbvrexsv_1 fcbvrexsv_3 wrex fcbvrexsv_0 fcbvrexsv_1 icbvrexsv_0 wsb icbvrexsv_0 fcbvrexsv_3 wrex fcbvrexsv_0 fcbvrexsv_1 fcbvrexsv_2 wsb fcbvrexsv_2 fcbvrexsv_3 wrex fcbvrexsv_0 fcbvrexsv_0 fcbvrexsv_1 icbvrexsv_0 wsb fcbvrexsv_1 icbvrexsv_0 fcbvrexsv_3 fcbvrexsv_0 icbvrexsv_0 nfv fcbvrexsv_0 fcbvrexsv_1 icbvrexsv_0 nfs1v fcbvrexsv_0 fcbvrexsv_1 icbvrexsv_0 sbequ12 cbvrex fcbvrexsv_0 fcbvrexsv_1 icbvrexsv_0 wsb fcbvrexsv_0 fcbvrexsv_1 fcbvrexsv_2 wsb icbvrexsv_0 fcbvrexsv_2 fcbvrexsv_3 fcbvrexsv_0 fcbvrexsv_1 icbvrexsv_0 fcbvrexsv_2 fcbvrexsv_0 fcbvrexsv_2 nfv nfsb fcbvrexsv_0 fcbvrexsv_1 fcbvrexsv_2 wsb icbvrexsv_0 nfv fcbvrexsv_0 icbvrexsv_0 fcbvrexsv_2 fcbvrexsv_1 sbequ cbvrex bitri $.
$}
$( Implicit to explicit substitution that swaps variables in a quantified
       expression.  (Contributed by NM, 5-Sep-2004.) $)
${
	$d x y z $.
	$d y z ph $.
	$d x z ps $.
	isbralie_0 $f set z $.
	fsbralie_0 $f wff ph $.
	fsbralie_1 $f wff ps $.
	fsbralie_2 $f set x $.
	fsbralie_3 $f set y $.
	esbralie_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	sbralie $p |- ( [ x / y ] A. x e. y ph <-> A. y e. x ps ) $= fsbralie_0 fsbralie_2 fsbralie_3 cv wral fsbralie_3 fsbralie_2 wsb fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_2 cv wral fsbralie_1 fsbralie_3 fsbralie_2 cv wral fsbralie_0 fsbralie_2 fsbralie_3 cv wral fsbralie_3 fsbralie_2 wsb fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_3 cv wral fsbralie_3 fsbralie_2 wsb fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_2 cv wral fsbralie_0 fsbralie_2 fsbralie_3 cv wral fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_3 cv wral fsbralie_3 fsbralie_2 fsbralie_0 fsbralie_2 isbralie_0 fsbralie_3 cv cbvralsv sbbii fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_3 cv wral fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_2 cv wral fsbralie_3 fsbralie_2 fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_2 cv wral fsbralie_3 nfv fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_3 cv fsbralie_2 cv raleq sbie bitri fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_2 cv wral fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_3 wsb fsbralie_3 fsbralie_2 cv wral fsbralie_1 fsbralie_3 fsbralie_2 cv wral fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_3 fsbralie_2 cv cbvralsv fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_3 wsb fsbralie_1 fsbralie_3 fsbralie_2 cv fsbralie_0 fsbralie_2 isbralie_0 wsb isbralie_0 fsbralie_3 wsb fsbralie_0 fsbralie_2 fsbralie_3 wsb fsbralie_1 fsbralie_0 fsbralie_2 fsbralie_3 isbralie_0 fsbralie_0 isbralie_0 nfv sbco2 fsbralie_0 fsbralie_1 fsbralie_2 fsbralie_3 fsbralie_1 fsbralie_2 nfv esbralie_0 sbie bitri ralbii bitri bitri $.
$}
$( Equivalent wff's yield equal restricted class abstractions (inference
       rule).  (Contributed by NM, 22-May-1999.) $)
${
	frabbiia_0 $f wff ph $.
	frabbiia_1 $f wff ps $.
	frabbiia_2 $f set x $.
	frabbiia_3 $f class A $.
	erabbiia_0 $e |- ( x e. A -> ( ph <-> ps ) ) $.
	rabbiia $p |- { x e. A | ph } = { x e. A | ps } $= frabbiia_2 cv frabbiia_3 wcel frabbiia_0 wa frabbiia_2 cab frabbiia_2 cv frabbiia_3 wcel frabbiia_1 wa frabbiia_2 cab frabbiia_0 frabbiia_2 frabbiia_3 crab frabbiia_1 frabbiia_2 frabbiia_3 crab frabbiia_2 cv frabbiia_3 wcel frabbiia_0 wa frabbiia_2 cv frabbiia_3 wcel frabbiia_1 wa frabbiia_2 frabbiia_2 cv frabbiia_3 wcel frabbiia_0 frabbiia_1 erabbiia_0 pm5.32i abbii frabbiia_0 frabbiia_2 frabbiia_3 df-rab frabbiia_1 frabbiia_2 frabbiia_3 df-rab 3eqtr4i $.
$}
$( Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  (Contributed by NM, 28-Nov-2003.) $)
${
	$d x ph $.
	frabbidva_0 $f wff ph $.
	frabbidva_1 $f wff ps $.
	frabbidva_2 $f wff ch $.
	frabbidva_3 $f set x $.
	frabbidva_4 $f class A $.
	erabbidva_0 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	rabbidva $p |- ( ph -> { x e. A | ps } = { x e. A | ch } ) $= frabbidva_0 frabbidva_1 frabbidva_2 wb frabbidva_3 frabbidva_4 wral frabbidva_1 frabbidva_3 frabbidva_4 crab frabbidva_2 frabbidva_3 frabbidva_4 crab wceq frabbidva_0 frabbidva_1 frabbidva_2 wb frabbidva_3 frabbidva_4 erabbidva_0 ralrimiva frabbidva_1 frabbidva_2 frabbidva_3 frabbidva_4 rabbi sylib $.
$}
$( Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  (Contributed by NM, 10-Feb-1995.) $)
${
	$d x ph $.
	frabbidv_0 $f wff ph $.
	frabbidv_1 $f wff ps $.
	frabbidv_2 $f wff ch $.
	frabbidv_3 $f set x $.
	frabbidv_4 $f class A $.
	erabbidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	rabbidv $p |- ( ph -> { x e. A | ps } = { x e. A | ch } ) $= frabbidv_0 frabbidv_1 frabbidv_2 frabbidv_3 frabbidv_4 frabbidv_0 frabbidv_1 frabbidv_2 wb frabbidv_3 cv frabbidv_4 wcel erabbidv_0 adantr rabbidva $.
$}
$( Equality theorem for restricted class abstractions, with bound-variable
       hypotheses instead of distinct variable restrictions.  (Contributed by
       NM, 7-Mar-2004.) $)
${
	frabeqf_0 $f wff ph $.
	frabeqf_1 $f set x $.
	frabeqf_2 $f class A $.
	frabeqf_3 $f class B $.
	erabeqf_0 $e |- F/_ x A $.
	erabeqf_1 $e |- F/_ x B $.
	rabeqf $p |- ( A = B -> { x e. A | ph } = { x e. B | ph } ) $= frabeqf_2 frabeqf_3 wceq frabeqf_1 cv frabeqf_2 wcel frabeqf_0 wa frabeqf_1 cab frabeqf_1 cv frabeqf_3 wcel frabeqf_0 wa frabeqf_1 cab frabeqf_0 frabeqf_1 frabeqf_2 crab frabeqf_0 frabeqf_1 frabeqf_3 crab frabeqf_2 frabeqf_3 wceq frabeqf_1 cv frabeqf_2 wcel frabeqf_0 wa frabeqf_1 cv frabeqf_3 wcel frabeqf_0 wa frabeqf_1 frabeqf_1 frabeqf_2 frabeqf_3 erabeqf_0 erabeqf_1 nfeq frabeqf_2 frabeqf_3 wceq frabeqf_1 cv frabeqf_2 wcel frabeqf_1 cv frabeqf_3 wcel frabeqf_0 frabeqf_2 frabeqf_3 frabeqf_1 cv eleq2 anbi1d abbid frabeqf_0 frabeqf_1 frabeqf_2 df-rab frabeqf_0 frabeqf_1 frabeqf_3 df-rab 3eqtr4g $.
$}
$( Equality theorem for restricted class abstractions.  (Contributed by NM,
       15-Oct-2003.) $)
${
	$d x A $.
	$d x B $.
	frabeq_0 $f wff ph $.
	frabeq_1 $f set x $.
	frabeq_2 $f class A $.
	frabeq_3 $f class B $.
	rabeq $p |- ( A = B -> { x e. A | ph } = { x e. B | ph } ) $= frabeq_0 frabeq_1 frabeq_2 frabeq_3 frabeq_1 frabeq_2 nfcv frabeq_1 frabeq_3 nfcv rabeqf $.
$}
$( Equality of restricted class abstractions.  (Contributed by Jeff Madsen,
       1-Dec-2009.) $)
${
	$d A x $.
	$d B x $.
	$d ph x $.
	frabeqbidv_0 $f wff ph $.
	frabeqbidv_1 $f wff ps $.
	frabeqbidv_2 $f wff ch $.
	frabeqbidv_3 $f set x $.
	frabeqbidv_4 $f class A $.
	frabeqbidv_5 $f class B $.
	erabeqbidv_0 $e |- ( ph -> A = B ) $.
	erabeqbidv_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	rabeqbidv $p |- ( ph -> { x e. A | ps } = { x e. B | ch } ) $= frabeqbidv_0 frabeqbidv_1 frabeqbidv_3 frabeqbidv_4 crab frabeqbidv_1 frabeqbidv_3 frabeqbidv_5 crab frabeqbidv_2 frabeqbidv_3 frabeqbidv_5 crab frabeqbidv_0 frabeqbidv_4 frabeqbidv_5 wceq frabeqbidv_1 frabeqbidv_3 frabeqbidv_4 crab frabeqbidv_1 frabeqbidv_3 frabeqbidv_5 crab wceq erabeqbidv_0 frabeqbidv_1 frabeqbidv_3 frabeqbidv_4 frabeqbidv_5 rabeq syl frabeqbidv_0 frabeqbidv_1 frabeqbidv_2 frabeqbidv_3 frabeqbidv_5 erabeqbidv_1 rabbidv eqtrd $.
$}
$( Equality of restricted class abstractions.  (Contributed by Mario
       Carneiro, 26-Jan-2017.) $)
${
	$d A x $.
	$d B x $.
	$d ph x $.
	frabeqbidva_0 $f wff ph $.
	frabeqbidva_1 $f wff ps $.
	frabeqbidva_2 $f wff ch $.
	frabeqbidva_3 $f set x $.
	frabeqbidva_4 $f class A $.
	frabeqbidva_5 $f class B $.
	erabeqbidva_0 $e |- ( ph -> A = B ) $.
	erabeqbidva_1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	rabeqbidva $p |- ( ph -> { x e. A | ps } = { x e. B | ch } ) $= frabeqbidva_0 frabeqbidva_1 frabeqbidva_3 frabeqbidva_4 crab frabeqbidva_2 frabeqbidva_3 frabeqbidva_4 crab frabeqbidva_2 frabeqbidva_3 frabeqbidva_5 crab frabeqbidva_0 frabeqbidva_1 frabeqbidva_2 frabeqbidva_3 frabeqbidva_4 erabeqbidva_1 rabbidva frabeqbidva_0 frabeqbidva_4 frabeqbidva_5 wceq frabeqbidva_2 frabeqbidva_3 frabeqbidva_4 crab frabeqbidva_2 frabeqbidva_3 frabeqbidva_5 crab wceq erabeqbidva_0 frabeqbidva_2 frabeqbidva_3 frabeqbidva_4 frabeqbidva_5 rabeq syl eqtrd $.
$}
$( Inference rule from equality of a class variable and a restricted class
       abstraction.  (Contributed by NM, 16-Feb-2004.) $)
${
	frabeq2i_0 $f wff ph $.
	frabeq2i_1 $f set x $.
	frabeq2i_2 $f class A $.
	frabeq2i_3 $f class B $.
	erabeq2i_0 $e |- A = { x e. B | ph } $.
	rabeq2i $p |- ( x e. A <-> ( x e. B /\ ph ) ) $= frabeq2i_1 cv frabeq2i_2 wcel frabeq2i_1 cv frabeq2i_0 frabeq2i_1 frabeq2i_3 crab wcel frabeq2i_1 cv frabeq2i_3 wcel frabeq2i_0 wa frabeq2i_2 frabeq2i_0 frabeq2i_1 frabeq2i_3 crab frabeq2i_1 cv erabeq2i_0 eleq2i frabeq2i_0 frabeq2i_1 frabeq2i_3 rabid bitri $.
$}
$( Rule to change the bound variable in a restricted class abstraction,
       using implicit substitution.  This version has bound-variable hypotheses
       in place of distinct variable conditions.  (Contributed by Andrew
       Salmon, 11-Jul-2011.)  (Revised by Mario Carneiro, 9-Oct-2016.) $)
${
	$d x z $.
	$d y z $.
	$d A z $.
	$d ph z $.
	$d ps z $.
	icbvrab_0 $f set z $.
	fcbvrab_0 $f wff ph $.
	fcbvrab_1 $f wff ps $.
	fcbvrab_2 $f set x $.
	fcbvrab_3 $f set y $.
	fcbvrab_4 $f class A $.
	ecbvrab_0 $e |- F/_ x A $.
	ecbvrab_1 $e |- F/_ y A $.
	ecbvrab_2 $e |- F/ y ph $.
	ecbvrab_3 $e |- F/ x ps $.
	ecbvrab_4 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrab $p |- { x e. A | ph } = { y e. A | ps } $= fcbvrab_2 cv fcbvrab_4 wcel fcbvrab_0 wa fcbvrab_2 cab fcbvrab_3 cv fcbvrab_4 wcel fcbvrab_1 wa fcbvrab_3 cab fcbvrab_0 fcbvrab_2 fcbvrab_4 crab fcbvrab_1 fcbvrab_3 fcbvrab_4 crab fcbvrab_2 cv fcbvrab_4 wcel fcbvrab_0 wa fcbvrab_2 cab icbvrab_0 cv fcbvrab_4 wcel fcbvrab_0 fcbvrab_2 icbvrab_0 wsb wa icbvrab_0 cab fcbvrab_3 cv fcbvrab_4 wcel fcbvrab_1 wa fcbvrab_3 cab fcbvrab_2 cv fcbvrab_4 wcel fcbvrab_0 wa icbvrab_0 cv fcbvrab_4 wcel fcbvrab_0 fcbvrab_2 icbvrab_0 wsb wa fcbvrab_2 icbvrab_0 fcbvrab_2 cv fcbvrab_4 wcel fcbvrab_0 wa icbvrab_0 nfv icbvrab_0 cv fcbvrab_4 wcel fcbvrab_0 fcbvrab_2 icbvrab_0 wsb fcbvrab_2 fcbvrab_2 icbvrab_0 fcbvrab_4 ecbvrab_0 nfcri fcbvrab_0 fcbvrab_2 icbvrab_0 nfs1v nfan fcbvrab_2 cv icbvrab_0 cv wceq fcbvrab_2 cv fcbvrab_4 wcel icbvrab_0 cv fcbvrab_4 wcel fcbvrab_0 fcbvrab_0 fcbvrab_2 icbvrab_0 wsb fcbvrab_2 cv icbvrab_0 cv fcbvrab_4 eleq1 fcbvrab_0 fcbvrab_2 icbvrab_0 sbequ12 anbi12d cbvab icbvrab_0 cv fcbvrab_4 wcel fcbvrab_0 fcbvrab_2 icbvrab_0 wsb wa fcbvrab_3 cv fcbvrab_4 wcel fcbvrab_1 wa icbvrab_0 fcbvrab_3 icbvrab_0 cv fcbvrab_4 wcel fcbvrab_0 fcbvrab_2 icbvrab_0 wsb fcbvrab_3 fcbvrab_3 icbvrab_0 fcbvrab_4 ecbvrab_1 nfcri fcbvrab_0 fcbvrab_2 icbvrab_0 fcbvrab_3 ecbvrab_2 nfsb nfan fcbvrab_3 cv fcbvrab_4 wcel fcbvrab_1 wa icbvrab_0 nfv icbvrab_0 cv fcbvrab_3 cv wceq icbvrab_0 cv fcbvrab_4 wcel fcbvrab_3 cv fcbvrab_4 wcel fcbvrab_0 fcbvrab_2 icbvrab_0 wsb fcbvrab_1 icbvrab_0 cv fcbvrab_3 cv fcbvrab_4 eleq1 icbvrab_0 cv fcbvrab_3 cv wceq fcbvrab_0 fcbvrab_2 icbvrab_0 wsb fcbvrab_0 fcbvrab_2 fcbvrab_3 wsb fcbvrab_1 fcbvrab_0 icbvrab_0 fcbvrab_3 fcbvrab_2 sbequ fcbvrab_0 fcbvrab_1 fcbvrab_2 fcbvrab_3 ecbvrab_3 ecbvrab_4 sbie syl6bb anbi12d cbvab eqtri fcbvrab_0 fcbvrab_2 fcbvrab_4 df-rab fcbvrab_1 fcbvrab_3 fcbvrab_4 df-rab 3eqtr4i $.
$}
$( Rule to change the bound variable in a restricted class abstraction,
       using implicit substitution.  (Contributed by NM, 26-May-1999.) $)
${
	$d x y A $.
	$d y ph $.
	$d x ps $.
	fcbvrabv_0 $f wff ph $.
	fcbvrabv_1 $f wff ps $.
	fcbvrabv_2 $f set x $.
	fcbvrabv_3 $f set y $.
	fcbvrabv_4 $f class A $.
	ecbvrabv_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrabv $p |- { x e. A | ph } = { y e. A | ps } $= fcbvrabv_0 fcbvrabv_1 fcbvrabv_2 fcbvrabv_3 fcbvrabv_4 fcbvrabv_2 fcbvrabv_4 nfcv fcbvrabv_3 fcbvrabv_4 nfcv fcbvrabv_0 fcbvrabv_3 nfv fcbvrabv_1 fcbvrabv_2 nfv ecbvrabv_0 cbvrab $.
$}

