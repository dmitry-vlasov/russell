$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Restricted_quantification.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The universal class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare the symbol for the universal class. $)
$c _V  $.
$( Letter V (for the universal class) $)
$( Extend class notation to include the universal class symbol. $)
${
	cvv $a class _V $.
$}
$( Soundness justification theorem for ~ df-v .  (Contributed by Rodolfo
       Medina, 27-Apr-2010.) $)
${
	$d z x $.
	$d z y $.
	ivjust_0 $f set z $.
	fvjust_0 $f set x $.
	fvjust_1 $f set y $.
	vjust $p |- { x | x = x } = { y | y = y } $= ivjust_0 fvjust_0 sup_set_class fvjust_0 sup_set_class wceq fvjust_0 cab fvjust_1 sup_set_class fvjust_1 sup_set_class wceq fvjust_1 cab fvjust_0 sup_set_class fvjust_0 sup_set_class wceq fvjust_0 ivjust_0 wsb fvjust_1 sup_set_class fvjust_1 sup_set_class wceq fvjust_1 ivjust_0 wsb ivjust_0 sup_set_class fvjust_0 sup_set_class fvjust_0 sup_set_class wceq fvjust_0 cab wcel ivjust_0 sup_set_class fvjust_1 sup_set_class fvjust_1 sup_set_class wceq fvjust_1 cab wcel fvjust_0 sup_set_class fvjust_0 sup_set_class wceq fvjust_0 ivjust_0 wsb fvjust_1 sup_set_class fvjust_1 sup_set_class wceq fvjust_1 ivjust_0 wsb fvjust_0 sup_set_class fvjust_0 sup_set_class wceq fvjust_0 ivjust_0 fvjust_0 equid sbt fvjust_1 sup_set_class fvjust_1 sup_set_class wceq fvjust_1 ivjust_0 fvjust_1 equid sbt 2th fvjust_0 sup_set_class fvjust_0 sup_set_class wceq ivjust_0 fvjust_0 df-clab fvjust_1 sup_set_class fvjust_1 sup_set_class wceq ivjust_0 fvjust_1 df-clab 3bitr4i eqriv $.
$}
$( Define the universal class.  Definition 5.20 of [TakeutiZaring] p. 21.
     Also Definition 2.9 of [Quine] p. 19.  (Contributed by NM, 5-Aug-1993.) $)
${
	fdf-v_0 $f set x $.
	df-v $a |- _V = { x | x = x } $.
$}
$( All set variables are sets (see ~ isset ).  Theorem 6.8 of [Quine] p. 43.
     (Contributed by NM, 5-Aug-1993.) $)
${
	fvex_0 $f set x $.
	vex $p |- x e. _V $= fvex_0 sup_set_class cvv wcel fvex_0 sup_set_class fvex_0 sup_set_class wceq fvex_0 sup_set_class eqid fvex_0 sup_set_class fvex_0 sup_set_class wceq fvex_0 cvv fvex_0 df-v abeq2i mpbir $.
$}
$( Two ways to say " ` A ` is a set":  A class ` A ` is a member of the
       universal class ` _V ` (see ~ df-v ) if and only if the class ` A `
       exists (i.e. there exists some set ` x ` equal to class ` A ` ).
       Theorem 6.9 of [Quine] p. 43. _Notational convention_:  We will use the
       notational device " ` A e. _V ` " to mean " ` A ` is a set" very
       frequently, for example in ~ uniex .  Note the when ` A ` is not a set,
       it is called a proper class.  In some theorems, such as ~ uniexg , in
       order to shorten certain proofs we use the more general antecedent
       ` A e. V ` instead of ` A e. _V ` to mean " ` A ` is a set."

       Note that a constant is implicitly considered distinct from all
       variables.  This is why ` _V ` is not included in the distinct variable
       list, even though ~ df-clel requires that the expression substituted for
       ` B ` not contain ` x ` .  (Also, the Metamath spec does not allow
       constants in the distinct variable list.)  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x A $.
	fisset_0 $f set x $.
	fisset_1 $f class A $.
	isset $p |- ( A e. _V <-> E. x x = A ) $= fisset_1 cvv wcel fisset_0 sup_set_class fisset_1 wceq fisset_0 sup_set_class cvv wcel wa fisset_0 wex fisset_0 sup_set_class fisset_1 wceq fisset_0 wex fisset_0 fisset_1 cvv df-clel fisset_0 sup_set_class fisset_1 wceq fisset_0 sup_set_class fisset_1 wceq fisset_0 sup_set_class cvv wcel wa fisset_0 fisset_0 sup_set_class cvv wcel fisset_0 sup_set_class fisset_1 wceq fisset_0 vex biantru exbii bitr4i $.
$}
$( A version of isset that does not require x and A to be distinct.
       (Contributed by Andrew Salmon, 6-Jun-2011.)  (Revised by Mario Carneiro,
       10-Oct-2016.) $)
${
	$d A y $.
	$d x y $.
	iissetf_0 $f set y $.
	fissetf_0 $f set x $.
	fissetf_1 $f class A $.
	eissetf_0 $e |- F/_ x A $.
	issetf $p |- ( A e. _V <-> E. x x = A ) $= fissetf_1 cvv wcel iissetf_0 sup_set_class fissetf_1 wceq iissetf_0 wex fissetf_0 sup_set_class fissetf_1 wceq fissetf_0 wex iissetf_0 fissetf_1 isset iissetf_0 sup_set_class fissetf_1 wceq fissetf_0 sup_set_class fissetf_1 wceq iissetf_0 fissetf_0 fissetf_0 iissetf_0 sup_set_class fissetf_1 eissetf_0 nfeq2 fissetf_0 sup_set_class fissetf_1 wceq iissetf_0 nfv iissetf_0 sup_set_class fissetf_0 sup_set_class fissetf_1 eqeq1 cbvex bitri $.
$}
$( A way to say " ` A ` is a set" (inference rule).  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x A $.
	fisseti_0 $f set x $.
	fisseti_1 $f class A $.
	eisseti_0 $e |- A e. _V $.
	isseti $p |- E. x x = A $= fisseti_1 cvv wcel fisseti_0 sup_set_class fisseti_1 wceq fisseti_0 wex eisseti_0 fisseti_0 fisseti_1 isset mpbi $.
$}
$( A way to say " ` A ` is a set" (inference rule).  (Contributed by NM,
       5-Aug-1993.) $)
${
	$d x A $.
	fissetri_0 $f set x $.
	fissetri_1 $f class A $.
	eissetri_0 $e |- E. x x = A $.
	issetri $p |- A e. _V $= fissetri_1 cvv wcel fissetri_0 sup_set_class fissetri_1 wceq fissetri_0 wex eissetri_0 fissetri_0 fissetri_1 isset mpbir $.
$}
$( If a class is a member of another class, it is a set.  Theorem 6.12 of
       [Quine] p. 44.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
       Andrew Salmon, 8-Jun-2011.) $)
${
	$d x A $.
	$d x B $.
	ielex_0 $f set x $.
	felex_0 $f class A $.
	felex_1 $f class B $.
	elex $p |- ( A e. B -> A e. _V ) $= ielex_0 sup_set_class felex_0 wceq ielex_0 sup_set_class felex_1 wcel wa ielex_0 wex ielex_0 sup_set_class felex_0 wceq ielex_0 wex felex_0 felex_1 wcel felex_0 cvv wcel ielex_0 sup_set_class felex_0 wceq ielex_0 sup_set_class felex_1 wcel ielex_0 exsimpl ielex_0 felex_0 felex_1 df-clel ielex_0 felex_0 isset 3imtr4i $.
$}
$( If a class is a member of another class, it is a set.  (Contributed by
       NM, 11-Jun-1994.) $)
${
	felexi_0 $f class A $.
	felexi_1 $f class B $.
	eelexi_0 $e |- A e. B $.
	elexi $p |- A e. _V $= felexi_0 felexi_1 wcel felexi_0 cvv wcel eelexi_0 felexi_0 felexi_1 elex ax-mp $.
$}
$( An element of a class exists.  (Contributed by NM, 1-May-1995.) $)
$v V $.
${
	$d x A $.
	felisset_0 $f set x $.
	felisset_1 $f class A $.
	felisset_2 $f class V $.
	elisset $p |- ( A e. V -> E. x x = A ) $= felisset_1 felisset_2 wcel felisset_1 cvv wcel felisset_0 sup_set_class felisset_1 wceq felisset_0 wex felisset_1 felisset_2 elex felisset_0 felisset_1 isset sylib $.
$}
$( If two classes each contain another class, then both contain some set.
       (Contributed by Alan Sare, 24-Oct-2011.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	felex22_0 $f set x $.
	felex22_1 $f class A $.
	felex22_2 $f class B $.
	felex22_3 $f class C $.
	elex22 $p |- ( ( A e. B /\ A e. C ) -> E. x ( x e. B /\ x e. C ) ) $= felex22_1 felex22_2 wcel felex22_1 felex22_3 wcel wa felex22_0 sup_set_class felex22_1 wceq felex22_0 sup_set_class felex22_2 wcel felex22_0 sup_set_class felex22_3 wcel wa wi felex22_0 wal felex22_0 sup_set_class felex22_1 wceq felex22_0 wex felex22_0 sup_set_class felex22_2 wcel felex22_0 sup_set_class felex22_3 wcel wa felex22_0 wex felex22_1 felex22_2 wcel felex22_1 felex22_3 wcel wa felex22_0 sup_set_class felex22_1 wceq felex22_0 sup_set_class felex22_2 wcel felex22_0 sup_set_class felex22_3 wcel wa wi felex22_0 felex22_1 felex22_2 wcel felex22_0 sup_set_class felex22_1 wceq felex22_0 sup_set_class felex22_2 wcel felex22_1 felex22_3 wcel felex22_0 sup_set_class felex22_3 wcel felex22_1 felex22_2 felex22_0 sup_set_class eleq1a felex22_1 felex22_3 felex22_0 sup_set_class eleq1a anim12ii alrimiv felex22_1 felex22_2 wcel felex22_0 sup_set_class felex22_1 wceq felex22_0 wex felex22_1 felex22_3 wcel felex22_0 felex22_1 felex22_2 elisset adantr felex22_0 sup_set_class felex22_1 wceq felex22_0 sup_set_class felex22_2 wcel felex22_0 sup_set_class felex22_3 wcel wa felex22_0 exim sylc $.
$}
$( If a class contains another class, then it contains some set.
       (Contributed by Alan Sare, 25-Sep-2011.) $)
${
	$d x A $.
	$d x B $.
	felex2_0 $f set x $.
	felex2_1 $f class A $.
	felex2_2 $f class B $.
	elex2 $p |- ( A e. B -> E. x x e. B ) $= felex2_1 felex2_2 wcel felex2_0 sup_set_class felex2_1 wceq felex2_0 sup_set_class felex2_2 wcel wi felex2_0 wal felex2_0 sup_set_class felex2_1 wceq felex2_0 wex felex2_0 sup_set_class felex2_2 wcel felex2_0 wex felex2_1 felex2_2 wcel felex2_0 sup_set_class felex2_1 wceq felex2_0 sup_set_class felex2_2 wcel wi felex2_0 felex2_1 felex2_2 felex2_0 sup_set_class eleq1a alrimiv felex2_0 felex2_1 felex2_2 elisset felex2_0 sup_set_class felex2_1 wceq felex2_0 sup_set_class felex2_2 wcel felex2_0 exim sylc $.
$}
$( A universal quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 26-Mar-2004.) $)
${
	fralv_0 $f wff ph $.
	fralv_1 $f set x $.
	ralv $p |- ( A. x e. _V ph <-> A. x ph ) $= fralv_0 fralv_1 cvv wral fralv_1 sup_set_class cvv wcel fralv_0 wi fralv_1 wal fralv_0 fralv_1 wal fralv_0 fralv_1 cvv df-ral fralv_0 fralv_1 sup_set_class cvv wcel fralv_0 wi fralv_1 fralv_1 sup_set_class cvv wcel fralv_0 fralv_1 vex a1bi albii bitr4i $.
$}
$( An existential quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 26-Mar-2004.) $)
${
	frexv_0 $f wff ph $.
	frexv_1 $f set x $.
	rexv $p |- ( E. x e. _V ph <-> E. x ph ) $= frexv_0 frexv_1 cvv wrex frexv_1 sup_set_class cvv wcel frexv_0 wa frexv_1 wex frexv_0 frexv_1 wex frexv_0 frexv_1 cvv df-rex frexv_0 frexv_1 sup_set_class cvv wcel frexv_0 wa frexv_1 frexv_1 sup_set_class cvv wcel frexv_0 frexv_1 vex biantrur exbii bitr4i $.
$}
$( A uniqueness quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 1-Nov-2010.) $)
${
	freuv_0 $f wff ph $.
	freuv_1 $f set x $.
	reuv $p |- ( E! x e. _V ph <-> E! x ph ) $= freuv_0 freuv_1 cvv wreu freuv_1 sup_set_class cvv wcel freuv_0 wa freuv_1 weu freuv_0 freuv_1 weu freuv_0 freuv_1 cvv df-reu freuv_0 freuv_1 sup_set_class cvv wcel freuv_0 wa freuv_1 freuv_1 sup_set_class cvv wcel freuv_0 freuv_1 vex biantrur eubii bitr4i $.
$}
$( A uniqueness quantifier restricted to the universe is unrestricted.
     (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
${
	frmov_0 $f wff ph $.
	frmov_1 $f set x $.
	rmov $p |- ( E* x e. _V ph <-> E* x ph ) $= frmov_0 frmov_1 cvv wrmo frmov_1 sup_set_class cvv wcel frmov_0 wa frmov_1 wmo frmov_0 frmov_1 wmo frmov_0 frmov_1 cvv df-rmo frmov_0 frmov_1 sup_set_class cvv wcel frmov_0 wa frmov_1 frmov_1 sup_set_class cvv wcel frmov_0 frmov_1 vex biantrur mobii bitr4i $.
$}
$( A class abstraction restricted to the universe is unrestricted.
     (Contributed by NM, 27-Dec-2004.)  (Proof shortened by Andrew Salmon,
     8-Jun-2011.) $)
${
	frabab_0 $f wff ph $.
	frabab_1 $f set x $.
	rabab $p |- { x e. _V | ph } = { x | ph } $= frabab_0 frabab_1 cvv crab frabab_1 sup_set_class cvv wcel frabab_0 wa frabab_1 cab frabab_0 frabab_1 cab frabab_0 frabab_1 cvv df-rab frabab_0 frabab_1 sup_set_class cvv wcel frabab_0 wa frabab_1 frabab_1 sup_set_class cvv wcel frabab_0 frabab_1 vex biantrur abbii eqtr4i $.
$}
$( Commutation of restricted and unrestricted universal quantifiers.
       (Contributed by NM, 26-Mar-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)
${
	$d x y $.
	$d y A $.
	fralcom4_0 $f wff ph $.
	fralcom4_1 $f set x $.
	fralcom4_2 $f set y $.
	fralcom4_3 $f class A $.
	ralcom4 $p |- ( A. x e. A A. y ph <-> A. y A. x e. A ph ) $= fralcom4_0 fralcom4_2 cvv wral fralcom4_1 fralcom4_3 wral fralcom4_0 fralcom4_1 fralcom4_3 wral fralcom4_2 cvv wral fralcom4_0 fralcom4_2 wal fralcom4_1 fralcom4_3 wral fralcom4_0 fralcom4_1 fralcom4_3 wral fralcom4_2 wal fralcom4_0 fralcom4_1 fralcom4_2 fralcom4_3 cvv ralcom fralcom4_0 fralcom4_2 cvv wral fralcom4_0 fralcom4_2 wal fralcom4_1 fralcom4_3 fralcom4_0 fralcom4_2 ralv ralbii fralcom4_0 fralcom4_1 fralcom4_3 wral fralcom4_2 ralv 3bitr3i $.
$}
$( Commutation of restricted and unrestricted existential quantifiers.
       (Contributed by NM, 12-Apr-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)
${
	$d x y $.
	$d y A $.
	frexcom4_0 $f wff ph $.
	frexcom4_1 $f set x $.
	frexcom4_2 $f set y $.
	frexcom4_3 $f class A $.
	rexcom4 $p |- ( E. x e. A E. y ph <-> E. y E. x e. A ph ) $= frexcom4_0 frexcom4_2 cvv wrex frexcom4_1 frexcom4_3 wrex frexcom4_0 frexcom4_1 frexcom4_3 wrex frexcom4_2 cvv wrex frexcom4_0 frexcom4_2 wex frexcom4_1 frexcom4_3 wrex frexcom4_0 frexcom4_1 frexcom4_3 wrex frexcom4_2 wex frexcom4_0 frexcom4_1 frexcom4_2 frexcom4_3 cvv rexcom frexcom4_0 frexcom4_2 cvv wrex frexcom4_0 frexcom4_2 wex frexcom4_1 frexcom4_3 frexcom4_0 frexcom4_2 rexv rexbii frexcom4_0 frexcom4_1 frexcom4_3 wrex frexcom4_2 rexv 3bitr3i $.
$}
$( Specialized existential commutation lemma.  (Contributed by Jeff Madsen,
       1-Jun-2011.) $)
${
	$d A x $.
	$d x y $.
	$d ph x $.
	frexcom4a_0 $f wff ph $.
	frexcom4a_1 $f wff ps $.
	frexcom4a_2 $f set x $.
	frexcom4a_3 $f set y $.
	frexcom4a_4 $f class A $.
	rexcom4a $p |- ( E. x E. y e. A ( ph /\ ps ) <-> E. y e. A ( ph /\ E. x ps ) ) $= frexcom4a_0 frexcom4a_1 wa frexcom4a_3 frexcom4a_4 wrex frexcom4a_2 wex frexcom4a_0 frexcom4a_1 wa frexcom4a_2 wex frexcom4a_3 frexcom4a_4 wrex frexcom4a_0 frexcom4a_1 frexcom4a_2 wex wa frexcom4a_3 frexcom4a_4 wrex frexcom4a_0 frexcom4a_1 wa frexcom4a_3 frexcom4a_2 frexcom4a_4 rexcom4 frexcom4a_0 frexcom4a_1 wa frexcom4a_2 wex frexcom4a_0 frexcom4a_1 frexcom4a_2 wex wa frexcom4a_3 frexcom4a_4 frexcom4a_0 frexcom4a_1 frexcom4a_2 19.42v rexbii bitr3i $.
$}
$( Specialized existential commutation lemma.  (Contributed by Jeff Madsen,
       1-Jun-2011.) $)
${
	$d A x $.
	$d x y $.
	$d ph x $.
	$d B x $.
	frexcom4b_0 $f wff ph $.
	frexcom4b_1 $f set x $.
	frexcom4b_2 $f set y $.
	frexcom4b_3 $f class A $.
	frexcom4b_4 $f class B $.
	erexcom4b_0 $e |- B e. _V $.
	rexcom4b $p |- ( E. x E. y e. A ( ph /\ x = B ) <-> E. y e. A ph ) $= frexcom4b_0 frexcom4b_1 sup_set_class frexcom4b_4 wceq wa frexcom4b_2 frexcom4b_3 wrex frexcom4b_1 wex frexcom4b_0 frexcom4b_1 sup_set_class frexcom4b_4 wceq frexcom4b_1 wex wa frexcom4b_2 frexcom4b_3 wrex frexcom4b_0 frexcom4b_2 frexcom4b_3 wrex frexcom4b_0 frexcom4b_1 sup_set_class frexcom4b_4 wceq frexcom4b_1 frexcom4b_2 frexcom4b_3 rexcom4a frexcom4b_0 frexcom4b_0 frexcom4b_1 sup_set_class frexcom4b_4 wceq frexcom4b_1 wex wa frexcom4b_2 frexcom4b_3 frexcom4b_1 sup_set_class frexcom4b_4 wceq frexcom4b_1 wex frexcom4b_0 frexcom4b_1 frexcom4b_4 erexcom4b_0 isseti biantru rexbii bitr4i $.
$}
$( Closed theorem version of ~ ceqsalg .  (Contributed by NM,
       28-Feb-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)
${
	$d x A $.
	fceqsalt_0 $f wff ph $.
	fceqsalt_1 $f wff ps $.
	fceqsalt_2 $f set x $.
	fceqsalt_3 $f class A $.
	fceqsalt_4 $f class V $.
	ceqsalt $p |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. V ) -> ( A. x ( x = A -> ph ) <-> ps ) ) $= fceqsalt_1 fceqsalt_2 wnf fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_3 fceqsalt_4 wcel w3a fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi fceqsalt_2 wal fceqsalt_1 fceqsalt_1 fceqsalt_2 wnf fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_3 fceqsalt_4 wcel w3a fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi fceqsalt_2 wal fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_2 wex fceqsalt_1 fceqsalt_3 fceqsalt_4 wcel fceqsalt_1 fceqsalt_2 wnf fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_2 wex fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_2 fceqsalt_3 fceqsalt_4 elisset 3ad2ant3 fceqsalt_1 fceqsalt_2 wnf fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_3 fceqsalt_4 wcel w3a fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi fceqsalt_2 wal fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_1 wi fceqsalt_2 wal fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_2 wex fceqsalt_1 wi fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_1 fceqsalt_2 wnf fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi fceqsalt_2 wal fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_1 wi fceqsalt_2 wal wi fceqsalt_3 fceqsalt_4 wcel fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_1 wi fceqsalt_2 fceqsalt_0 fceqsalt_1 wb fceqsalt_0 fceqsalt_1 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 bi1 imim3i al2imi 3ad2ant2 fceqsalt_1 fceqsalt_2 wnf fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_1 wi fceqsalt_2 wal fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_2 wex fceqsalt_1 wi wb fceqsalt_3 fceqsalt_4 wcel fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_1 fceqsalt_2 19.23t 3ad2ant1 sylibd mpid fceqsalt_1 fceqsalt_2 wnf fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_3 fceqsalt_4 wcel w3a fceqsalt_1 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi wi fceqsalt_2 wal fceqsalt_1 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi fceqsalt_2 wal wi fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_1 fceqsalt_2 wnf fceqsalt_1 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi wi fceqsalt_2 wal fceqsalt_3 fceqsalt_4 wcel fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_1 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi wi fceqsalt_2 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_1 fceqsalt_0 fceqsalt_0 fceqsalt_1 wb fceqsalt_1 fceqsalt_0 wi fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 bi2 imim2i com23 alimi 3ad2ant2 fceqsalt_1 fceqsalt_2 wnf fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 fceqsalt_1 wb wi fceqsalt_2 wal fceqsalt_1 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi wi fceqsalt_2 wal fceqsalt_1 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi fceqsalt_2 wal wi wb fceqsalt_3 fceqsalt_4 wcel fceqsalt_1 fceqsalt_2 sup_set_class fceqsalt_3 wceq fceqsalt_0 wi fceqsalt_2 19.21t 3ad2ant1 mpbid impbid $.
$}
$( Restricted quantifier version of ~ ceqsalt .  (Contributed by NM,
       28-Feb-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)
${
	$d x A $.
	$d x B $.
	fceqsralt_0 $f wff ph $.
	fceqsralt_1 $f wff ps $.
	fceqsralt_2 $f set x $.
	fceqsralt_3 $f class A $.
	fceqsralt_4 $f class B $.
	ceqsralt $p |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. B ) -> ( A. x e. B ( x = A -> ph ) <-> ps ) ) $= fceqsralt_1 fceqsralt_2 wnf fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 fceqsralt_1 wb wi fceqsralt_2 wal fceqsralt_3 fceqsralt_4 wcel w3a fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 fceqsralt_4 wral fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 wal wi fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 wal fceqsralt_1 fceqsralt_1 fceqsralt_2 wnf fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 fceqsralt_1 wb wi fceqsralt_2 wal fceqsralt_3 fceqsralt_4 wcel w3a fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 fceqsralt_4 wral fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_2 wal fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 wal wi fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 fceqsralt_4 wral fceqsralt_2 sup_set_class fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_2 wal fceqsralt_1 fceqsralt_2 wnf fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 fceqsralt_1 wb wi fceqsralt_2 wal fceqsralt_3 fceqsralt_4 wcel w3a fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_2 wal fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 fceqsralt_4 df-ral fceqsralt_2 sup_set_class fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_2 wal fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_2 wal wb fceqsralt_1 fceqsralt_2 wnf fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 fceqsralt_1 wb wi fceqsralt_2 wal fceqsralt_3 fceqsralt_4 wcel w3a fceqsralt_2 sup_set_class fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_2 fceqsralt_2 sup_set_class fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq wa fceqsralt_0 wi fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq wa fceqsralt_0 wi fceqsralt_2 sup_set_class fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi wi fceqsralt_2 sup_set_class fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq wa fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq wa fceqsralt_0 fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_2 sup_set_class fceqsralt_4 wcel fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 fceqsralt_4 eleq1 pm5.32ri imbi1i fceqsralt_2 sup_set_class fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 impexp fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 impexp 3bitr3i albii a1i syl5bb fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 19.21v syl6bb fceqsralt_3 fceqsralt_4 wcel fceqsralt_1 fceqsralt_2 wnf fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 wal fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 wal wi wb fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 fceqsralt_1 wb wi fceqsralt_2 wal fceqsralt_3 fceqsralt_4 wcel fceqsralt_2 sup_set_class fceqsralt_3 wceq fceqsralt_0 wi fceqsralt_2 wal biimt 3ad2ant3 fceqsralt_0 fceqsralt_1 fceqsralt_2 fceqsralt_3 fceqsralt_4 ceqsalt 3bitr2d $.
$}
$( A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       29-Oct-2003.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
${
	$d x A $.
	fceqsalg_0 $f wff ph $.
	fceqsalg_1 $f wff ps $.
	fceqsalg_2 $f set x $.
	fceqsalg_3 $f class A $.
	fceqsalg_4 $f class V $.
	eceqsalg_0 $e |- F/ x ps $.
	eceqsalg_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsalg $p |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) ) $= fceqsalg_3 fceqsalg_4 wcel fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 wi fceqsalg_2 wal fceqsalg_1 fceqsalg_3 fceqsalg_4 wcel fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_2 wex fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 wi fceqsalg_2 wal fceqsalg_1 fceqsalg_2 fceqsalg_3 fceqsalg_4 elisset fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 wi fceqsalg_2 wal fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_1 fceqsalg_2 fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 wi fceqsalg_2 nfa1 eceqsalg_0 fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 wi fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_1 wi fceqsalg_2 fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 fceqsalg_1 fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 fceqsalg_1 eceqsalg_1 biimpd a2i sps exlimd syl5com fceqsalg_1 fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 wi fceqsalg_2 eceqsalg_0 fceqsalg_2 sup_set_class fceqsalg_3 wceq fceqsalg_0 fceqsalg_1 eceqsalg_1 biimprcd alrimi impbid1 $.
$}
$( A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       18-Aug-1993.) $)
${
	$d x A $.
	fceqsal_0 $f wff ph $.
	fceqsal_1 $f wff ps $.
	fceqsal_2 $f set x $.
	fceqsal_3 $f class A $.
	eceqsal_0 $e |- F/ x ps $.
	eceqsal_1 $e |- A e. _V $.
	eceqsal_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsal $p |- ( A. x ( x = A -> ph ) <-> ps ) $= fceqsal_3 cvv wcel fceqsal_2 sup_set_class fceqsal_3 wceq fceqsal_0 wi fceqsal_2 wal fceqsal_1 wb eceqsal_1 fceqsal_0 fceqsal_1 fceqsal_2 fceqsal_3 cvv eceqsal_0 eceqsal_2 ceqsalg ax-mp $.
$}
$( A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       18-Aug-1993.) $)
${
	$d x A $.
	$d x ps $.
	fceqsalv_0 $f wff ph $.
	fceqsalv_1 $f wff ps $.
	fceqsalv_2 $f set x $.
	fceqsalv_3 $f class A $.
	eceqsalv_0 $e |- A e. _V $.
	eceqsalv_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsalv $p |- ( A. x ( x = A -> ph ) <-> ps ) $= fceqsalv_0 fceqsalv_1 fceqsalv_2 fceqsalv_3 fceqsalv_1 fceqsalv_2 nfv eceqsalv_0 eceqsalv_1 ceqsal $.
$}
$( Restricted quantifier version of ~ ceqsalv .  (Contributed by NM,
       21-Jun-2013.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	fceqsralv_0 $f wff ph $.
	fceqsralv_1 $f wff ps $.
	fceqsralv_2 $f set x $.
	fceqsralv_3 $f class A $.
	fceqsralv_4 $f class B $.
	eceqsralv_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsralv $p |- ( A e. B -> ( A. x e. B ( x = A -> ph ) <-> ps ) ) $= fceqsralv_1 fceqsralv_2 wnf fceqsralv_2 sup_set_class fceqsralv_3 wceq fceqsralv_0 fceqsralv_1 wb wi fceqsralv_2 wal fceqsralv_3 fceqsralv_4 wcel fceqsralv_2 sup_set_class fceqsralv_3 wceq fceqsralv_0 wi fceqsralv_2 fceqsralv_4 wral fceqsralv_1 wb fceqsralv_1 fceqsralv_2 nfv fceqsralv_2 sup_set_class fceqsralv_3 wceq fceqsralv_0 fceqsralv_1 wb wi fceqsralv_2 eceqsralv_0 ax-gen fceqsralv_0 fceqsralv_1 fceqsralv_2 fceqsralv_3 fceqsralv_4 ceqsralt mp3an12 $.
$}
$( Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)
${
	$d x ps $.
	fgencl_0 $f wff ph $.
	fgencl_1 $f wff ps $.
	fgencl_2 $f wff ch $.
	fgencl_3 $f wff th $.
	fgencl_4 $f set x $.
	fgencl_5 $f class A $.
	fgencl_6 $f class B $.
	egencl_0 $e |- ( th <-> E. x ( ch /\ A = B ) ) $.
	egencl_1 $e |- ( A = B -> ( ph <-> ps ) ) $.
	egencl_2 $e |- ( ch -> ph ) $.
	gencl $p |- ( th -> ps ) $= fgencl_3 fgencl_2 fgencl_5 fgencl_6 wceq wa fgencl_4 wex fgencl_1 egencl_0 fgencl_2 fgencl_5 fgencl_6 wceq wa fgencl_1 fgencl_4 fgencl_5 fgencl_6 wceq fgencl_2 fgencl_1 fgencl_2 fgencl_0 fgencl_5 fgencl_6 wceq fgencl_1 egencl_2 egencl_1 syl5ib impcom exlimiv sylbi $.
$}
$( Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)
$v R $.
$v S $.
${
	$d x y $.
	$d x R $.
	$d x ps $.
	$d y C $.
	$d y S $.
	$d y ch $.
	f2gencl_0 $f wff ph $.
	f2gencl_1 $f wff ps $.
	f2gencl_2 $f wff ch $.
	f2gencl_3 $f set x $.
	f2gencl_4 $f set y $.
	f2gencl_5 $f class A $.
	f2gencl_6 $f class B $.
	f2gencl_7 $f class C $.
	f2gencl_8 $f class D $.
	f2gencl_9 $f class R $.
	f2gencl_10 $f class S $.
	e2gencl_0 $e |- ( C e. S <-> E. x e. R A = C ) $.
	e2gencl_1 $e |- ( D e. S <-> E. y e. R B = D ) $.
	e2gencl_2 $e |- ( A = C -> ( ph <-> ps ) ) $.
	e2gencl_3 $e |- ( B = D -> ( ps <-> ch ) ) $.
	e2gencl_4 $e |- ( ( x e. R /\ y e. R ) -> ph ) $.
	2gencl $p |- ( ( C e. S /\ D e. S ) -> ch ) $= f2gencl_8 f2gencl_10 wcel f2gencl_7 f2gencl_10 wcel f2gencl_2 f2gencl_7 f2gencl_10 wcel f2gencl_1 wi f2gencl_7 f2gencl_10 wcel f2gencl_2 wi f2gencl_4 sup_set_class f2gencl_9 wcel f2gencl_8 f2gencl_10 wcel f2gencl_4 f2gencl_6 f2gencl_8 f2gencl_8 f2gencl_10 wcel f2gencl_6 f2gencl_8 wceq f2gencl_4 f2gencl_9 wrex f2gencl_4 sup_set_class f2gencl_9 wcel f2gencl_6 f2gencl_8 wceq wa f2gencl_4 wex e2gencl_1 f2gencl_6 f2gencl_8 wceq f2gencl_4 f2gencl_9 df-rex bitri f2gencl_6 f2gencl_8 wceq f2gencl_1 f2gencl_2 f2gencl_7 f2gencl_10 wcel e2gencl_3 imbi2d f2gencl_7 f2gencl_10 wcel f2gencl_4 sup_set_class f2gencl_9 wcel f2gencl_1 f2gencl_4 sup_set_class f2gencl_9 wcel f2gencl_0 wi f2gencl_4 sup_set_class f2gencl_9 wcel f2gencl_1 wi f2gencl_3 sup_set_class f2gencl_9 wcel f2gencl_7 f2gencl_10 wcel f2gencl_3 f2gencl_5 f2gencl_7 f2gencl_7 f2gencl_10 wcel f2gencl_5 f2gencl_7 wceq f2gencl_3 f2gencl_9 wrex f2gencl_3 sup_set_class f2gencl_9 wcel f2gencl_5 f2gencl_7 wceq wa f2gencl_3 wex e2gencl_0 f2gencl_5 f2gencl_7 wceq f2gencl_3 f2gencl_9 df-rex bitri f2gencl_5 f2gencl_7 wceq f2gencl_0 f2gencl_1 f2gencl_4 sup_set_class f2gencl_9 wcel e2gencl_2 imbi2d f2gencl_3 sup_set_class f2gencl_9 wcel f2gencl_4 sup_set_class f2gencl_9 wcel f2gencl_0 e2gencl_4 ex gencl com12 gencl impcom $.
$}
$( Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)
${
	$d x y z $.
	$d y z D $.
	$d z F $.
	$d x y R $.
	$d y z S $.
	$d x ps $.
	$d y ch $.
	$d z th $.
	f3gencl_0 $f wff ph $.
	f3gencl_1 $f wff ps $.
	f3gencl_2 $f wff ch $.
	f3gencl_3 $f wff th $.
	f3gencl_4 $f set x $.
	f3gencl_5 $f set y $.
	f3gencl_6 $f set z $.
	f3gencl_7 $f class A $.
	f3gencl_8 $f class B $.
	f3gencl_9 $f class C $.
	f3gencl_10 $f class D $.
	f3gencl_11 $f class R $.
	f3gencl_12 $f class S $.
	f3gencl_13 $f class F $.
	f3gencl_14 $f class G $.
	e3gencl_0 $e |- ( D e. S <-> E. x e. R A = D ) $.
	e3gencl_1 $e |- ( F e. S <-> E. y e. R B = F ) $.
	e3gencl_2 $e |- ( G e. S <-> E. z e. R C = G ) $.
	e3gencl_3 $e |- ( A = D -> ( ph <-> ps ) ) $.
	e3gencl_4 $e |- ( B = F -> ( ps <-> ch ) ) $.
	e3gencl_5 $e |- ( C = G -> ( ch <-> th ) ) $.
	e3gencl_6 $e |- ( ( x e. R /\ y e. R /\ z e. R ) -> ph ) $.
	3gencl $p |- ( ( D e. S /\ F e. S /\ G e. S ) -> th ) $= f3gencl_10 f3gencl_12 wcel f3gencl_13 f3gencl_12 wcel f3gencl_14 f3gencl_12 wcel f3gencl_3 f3gencl_14 f3gencl_12 wcel f3gencl_10 f3gencl_12 wcel f3gencl_13 f3gencl_12 wcel wa f3gencl_3 f3gencl_10 f3gencl_12 wcel f3gencl_13 f3gencl_12 wcel wa f3gencl_2 wi f3gencl_10 f3gencl_12 wcel f3gencl_13 f3gencl_12 wcel wa f3gencl_3 wi f3gencl_6 sup_set_class f3gencl_11 wcel f3gencl_14 f3gencl_12 wcel f3gencl_6 f3gencl_9 f3gencl_14 f3gencl_14 f3gencl_12 wcel f3gencl_9 f3gencl_14 wceq f3gencl_6 f3gencl_11 wrex f3gencl_6 sup_set_class f3gencl_11 wcel f3gencl_9 f3gencl_14 wceq wa f3gencl_6 wex e3gencl_2 f3gencl_9 f3gencl_14 wceq f3gencl_6 f3gencl_11 df-rex bitri f3gencl_9 f3gencl_14 wceq f3gencl_2 f3gencl_3 f3gencl_10 f3gencl_12 wcel f3gencl_13 f3gencl_12 wcel wa e3gencl_5 imbi2d f3gencl_10 f3gencl_12 wcel f3gencl_13 f3gencl_12 wcel wa f3gencl_6 sup_set_class f3gencl_11 wcel f3gencl_2 f3gencl_6 sup_set_class f3gencl_11 wcel f3gencl_0 wi f3gencl_6 sup_set_class f3gencl_11 wcel f3gencl_1 wi f3gencl_6 sup_set_class f3gencl_11 wcel f3gencl_2 wi f3gencl_4 f3gencl_5 f3gencl_7 f3gencl_8 f3gencl_10 f3gencl_13 f3gencl_11 f3gencl_12 e3gencl_0 e3gencl_1 f3gencl_7 f3gencl_10 wceq f3gencl_0 f3gencl_1 f3gencl_6 sup_set_class f3gencl_11 wcel e3gencl_3 imbi2d f3gencl_8 f3gencl_13 wceq f3gencl_1 f3gencl_2 f3gencl_6 sup_set_class f3gencl_11 wcel e3gencl_4 imbi2d f3gencl_4 sup_set_class f3gencl_11 wcel f3gencl_5 sup_set_class f3gencl_11 wcel f3gencl_6 sup_set_class f3gencl_11 wcel f3gencl_0 e3gencl_6 3expia 2gencl com12 gencl com12 3impia $.
$}
$( Implicit substitution inference for general classes.  (Contributed by
       NM, 26-Aug-2007.) $)
${
	$d x A $.
	$d x ps $.
	fcgsexg_0 $f wff ph $.
	fcgsexg_1 $f wff ps $.
	fcgsexg_2 $f wff ch $.
	fcgsexg_3 $f set x $.
	fcgsexg_4 $f class A $.
	fcgsexg_5 $f class V $.
	ecgsexg_0 $e |- ( x = A -> ch ) $.
	ecgsexg_1 $e |- ( ch -> ( ph <-> ps ) ) $.
	cgsexg $p |- ( A e. V -> ( E. x ( ch /\ ph ) <-> ps ) ) $= fcgsexg_4 fcgsexg_5 wcel fcgsexg_2 fcgsexg_0 wa fcgsexg_3 wex fcgsexg_1 fcgsexg_2 fcgsexg_0 wa fcgsexg_1 fcgsexg_3 fcgsexg_2 fcgsexg_0 fcgsexg_1 ecgsexg_1 biimpa exlimiv fcgsexg_4 fcgsexg_5 wcel fcgsexg_2 fcgsexg_3 wex fcgsexg_1 fcgsexg_2 fcgsexg_0 wa fcgsexg_3 wex fcgsexg_4 fcgsexg_5 wcel fcgsexg_3 sup_set_class fcgsexg_4 wceq fcgsexg_3 wex fcgsexg_2 fcgsexg_3 wex fcgsexg_3 fcgsexg_4 fcgsexg_5 elisset fcgsexg_3 sup_set_class fcgsexg_4 wceq fcgsexg_2 fcgsexg_3 ecgsexg_0 eximi syl fcgsexg_1 fcgsexg_2 fcgsexg_2 fcgsexg_0 wa fcgsexg_3 fcgsexg_1 fcgsexg_2 fcgsexg_0 fcgsexg_2 fcgsexg_0 fcgsexg_1 ecgsexg_1 biimprcd ancld eximdv syl5com impbid2 $.
$}
$( Implicit substitution inference for general classes.  (Contributed by
       NM, 26-Jul-1995.) $)
$v W $.
${
	$d x y ps $.
	$d x y A $.
	$d x y B $.
	fcgsex2g_0 $f wff ph $.
	fcgsex2g_1 $f wff ps $.
	fcgsex2g_2 $f wff ch $.
	fcgsex2g_3 $f set x $.
	fcgsex2g_4 $f set y $.
	fcgsex2g_5 $f class A $.
	fcgsex2g_6 $f class B $.
	fcgsex2g_7 $f class V $.
	fcgsex2g_8 $f class W $.
	ecgsex2g_0 $e |- ( ( x = A /\ y = B ) -> ch ) $.
	ecgsex2g_1 $e |- ( ch -> ( ph <-> ps ) ) $.
	cgsex2g $p |- ( ( A e. V /\ B e. W ) -> ( E. x E. y ( ch /\ ph ) <-> ps ) ) $= fcgsex2g_5 fcgsex2g_7 wcel fcgsex2g_6 fcgsex2g_8 wcel wa fcgsex2g_2 fcgsex2g_0 wa fcgsex2g_4 wex fcgsex2g_3 wex fcgsex2g_1 fcgsex2g_2 fcgsex2g_0 wa fcgsex2g_1 fcgsex2g_3 fcgsex2g_4 fcgsex2g_2 fcgsex2g_0 fcgsex2g_1 ecgsex2g_1 biimpa exlimivv fcgsex2g_5 fcgsex2g_7 wcel fcgsex2g_6 fcgsex2g_8 wcel wa fcgsex2g_2 fcgsex2g_4 wex fcgsex2g_3 wex fcgsex2g_1 fcgsex2g_2 fcgsex2g_0 wa fcgsex2g_4 wex fcgsex2g_3 wex fcgsex2g_5 fcgsex2g_7 wcel fcgsex2g_6 fcgsex2g_8 wcel wa fcgsex2g_3 sup_set_class fcgsex2g_5 wceq fcgsex2g_4 sup_set_class fcgsex2g_6 wceq wa fcgsex2g_4 wex fcgsex2g_3 wex fcgsex2g_2 fcgsex2g_4 wex fcgsex2g_3 wex fcgsex2g_5 fcgsex2g_7 wcel fcgsex2g_6 fcgsex2g_8 wcel wa fcgsex2g_3 sup_set_class fcgsex2g_5 wceq fcgsex2g_3 wex fcgsex2g_4 sup_set_class fcgsex2g_6 wceq fcgsex2g_4 wex wa fcgsex2g_3 sup_set_class fcgsex2g_5 wceq fcgsex2g_4 sup_set_class fcgsex2g_6 wceq wa fcgsex2g_4 wex fcgsex2g_3 wex fcgsex2g_5 fcgsex2g_7 wcel fcgsex2g_3 sup_set_class fcgsex2g_5 wceq fcgsex2g_3 wex fcgsex2g_6 fcgsex2g_8 wcel fcgsex2g_4 sup_set_class fcgsex2g_6 wceq fcgsex2g_4 wex fcgsex2g_3 fcgsex2g_5 fcgsex2g_7 elisset fcgsex2g_4 fcgsex2g_6 fcgsex2g_8 elisset anim12i fcgsex2g_3 sup_set_class fcgsex2g_5 wceq fcgsex2g_4 sup_set_class fcgsex2g_6 wceq fcgsex2g_3 fcgsex2g_4 eeanv sylibr fcgsex2g_3 sup_set_class fcgsex2g_5 wceq fcgsex2g_4 sup_set_class fcgsex2g_6 wceq wa fcgsex2g_2 fcgsex2g_3 fcgsex2g_4 ecgsex2g_0 2eximi syl fcgsex2g_1 fcgsex2g_2 fcgsex2g_2 fcgsex2g_0 wa fcgsex2g_3 fcgsex2g_4 fcgsex2g_1 fcgsex2g_2 fcgsex2g_0 fcgsex2g_2 fcgsex2g_0 fcgsex2g_1 ecgsex2g_1 biimprcd ancld 2eximdv syl5com impbid2 $.
$}
$( An implicit substitution inference for 4 general classes.  (Contributed
       by NM, 5-Aug-1995.) $)
${
	$d x y z w A $.
	$d x y z w B $.
	$d x y z w C $.
	$d x y z w D $.
	$d x y z w ps $.
	fcgsex4g_0 $f wff ph $.
	fcgsex4g_1 $f wff ps $.
	fcgsex4g_2 $f wff ch $.
	fcgsex4g_3 $f set x $.
	fcgsex4g_4 $f set y $.
	fcgsex4g_5 $f set z $.
	fcgsex4g_6 $f set w $.
	fcgsex4g_7 $f class A $.
	fcgsex4g_8 $f class B $.
	fcgsex4g_9 $f class C $.
	fcgsex4g_10 $f class D $.
	fcgsex4g_11 $f class R $.
	fcgsex4g_12 $f class S $.
	ecgsex4g_0 $e |- ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) -> ch ) $.
	ecgsex4g_1 $e |- ( ch -> ( ph <-> ps ) ) $.
	cgsex4g $p |- ( ( ( A e. R /\ B e. S ) /\ ( C e. R /\ D e. S ) ) -> ( E. x E. y E. z E. w ( ch /\ ph ) <-> ps ) ) $= fcgsex4g_7 fcgsex4g_11 wcel fcgsex4g_8 fcgsex4g_12 wcel wa fcgsex4g_9 fcgsex4g_11 wcel fcgsex4g_10 fcgsex4g_12 wcel wa wa fcgsex4g_2 fcgsex4g_0 wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_1 fcgsex4g_2 fcgsex4g_0 wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_1 fcgsex4g_3 fcgsex4g_4 fcgsex4g_2 fcgsex4g_0 wa fcgsex4g_1 fcgsex4g_5 fcgsex4g_6 fcgsex4g_2 fcgsex4g_0 fcgsex4g_1 ecgsex4g_1 biimpa exlimivv exlimivv fcgsex4g_7 fcgsex4g_11 wcel fcgsex4g_8 fcgsex4g_12 wcel wa fcgsex4g_9 fcgsex4g_11 wcel fcgsex4g_10 fcgsex4g_12 wcel wa wa fcgsex4g_2 fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_1 fcgsex4g_2 fcgsex4g_0 wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_7 fcgsex4g_11 wcel fcgsex4g_8 fcgsex4g_12 wcel wa fcgsex4g_9 fcgsex4g_11 wcel fcgsex4g_10 fcgsex4g_12 wcel wa wa fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq wa fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq wa wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_2 fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_7 fcgsex4g_11 wcel fcgsex4g_8 fcgsex4g_12 wcel wa fcgsex4g_9 fcgsex4g_11 wcel fcgsex4g_10 fcgsex4g_12 wcel wa wa fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq wa fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq wa fcgsex4g_6 wex fcgsex4g_5 wex wa fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq wa fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq wa wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_7 fcgsex4g_11 wcel fcgsex4g_8 fcgsex4g_12 wcel wa fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq wa fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_9 fcgsex4g_11 wcel fcgsex4g_10 fcgsex4g_12 wcel wa fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_7 fcgsex4g_11 wcel fcgsex4g_8 fcgsex4g_12 wcel wa fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_3 wex fcgsex4g_4 sup_set_class fcgsex4g_8 wceq fcgsex4g_4 wex wa fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq wa fcgsex4g_4 wex fcgsex4g_3 wex fcgsex4g_7 fcgsex4g_11 wcel fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_3 wex fcgsex4g_8 fcgsex4g_12 wcel fcgsex4g_4 sup_set_class fcgsex4g_8 wceq fcgsex4g_4 wex fcgsex4g_3 fcgsex4g_7 fcgsex4g_11 elisset fcgsex4g_4 fcgsex4g_8 fcgsex4g_12 elisset anim12i fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq fcgsex4g_3 fcgsex4g_4 eeanv sylibr fcgsex4g_9 fcgsex4g_11 wcel fcgsex4g_10 fcgsex4g_12 wcel wa fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_5 wex fcgsex4g_6 sup_set_class fcgsex4g_10 wceq fcgsex4g_6 wex wa fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_9 fcgsex4g_11 wcel fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_5 wex fcgsex4g_10 fcgsex4g_12 wcel fcgsex4g_6 sup_set_class fcgsex4g_10 wceq fcgsex4g_6 wex fcgsex4g_5 fcgsex4g_9 fcgsex4g_11 elisset fcgsex4g_6 fcgsex4g_10 fcgsex4g_12 elisset anim12i fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq fcgsex4g_5 fcgsex4g_6 eeanv sylibr anim12i fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq wa fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq wa fcgsex4g_3 fcgsex4g_4 fcgsex4g_5 fcgsex4g_6 ee4anv sylibr fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq wa fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq wa wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_2 fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_3 fcgsex4g_4 fcgsex4g_3 sup_set_class fcgsex4g_7 wceq fcgsex4g_4 sup_set_class fcgsex4g_8 wceq wa fcgsex4g_5 sup_set_class fcgsex4g_9 wceq fcgsex4g_6 sup_set_class fcgsex4g_10 wceq wa wa fcgsex4g_2 fcgsex4g_5 fcgsex4g_6 ecgsex4g_0 2eximi 2eximi syl fcgsex4g_1 fcgsex4g_2 fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_2 fcgsex4g_0 wa fcgsex4g_6 wex fcgsex4g_5 wex fcgsex4g_3 fcgsex4g_4 fcgsex4g_1 fcgsex4g_2 fcgsex4g_2 fcgsex4g_0 wa fcgsex4g_5 fcgsex4g_6 fcgsex4g_1 fcgsex4g_2 fcgsex4g_0 fcgsex4g_2 fcgsex4g_0 fcgsex4g_1 ecgsex4g_1 biimprcd ancld 2eximdv 2eximdv syl5com impbid2 $.
$}
$( Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 2-Mar-1995.)  (Revised by Mario Carneiro,
       10-Oct-2016.) $)
${
	$d x A $.
	fceqsex_0 $f wff ph $.
	fceqsex_1 $f wff ps $.
	fceqsex_2 $f set x $.
	fceqsex_3 $f class A $.
	eceqsex_0 $e |- F/ x ps $.
	eceqsex_1 $e |- A e. _V $.
	eceqsex_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsex $p |- ( E. x ( x = A /\ ph ) <-> ps ) $= fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_0 wa fceqsex_2 wex fceqsex_1 fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_0 wa fceqsex_1 fceqsex_2 eceqsex_0 fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_0 fceqsex_1 eceqsex_2 biimpa exlimi fceqsex_1 fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_0 wi fceqsex_2 wal fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_2 wex fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_0 wa fceqsex_2 wex fceqsex_1 fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_0 wi fceqsex_2 eceqsex_0 fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_0 fceqsex_1 eceqsex_2 biimprcd alrimi fceqsex_2 fceqsex_3 eceqsex_1 isseti fceqsex_2 sup_set_class fceqsex_3 wceq fceqsex_0 fceqsex_2 exintr ee10 impbii $.
$}
$( Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 2-Mar-1995.) $)
${
	$d x A $.
	$d x ps $.
	fceqsexv_0 $f wff ph $.
	fceqsexv_1 $f wff ps $.
	fceqsexv_2 $f set x $.
	fceqsexv_3 $f class A $.
	eceqsexv_0 $e |- A e. _V $.
	eceqsexv_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsexv $p |- ( E. x ( x = A /\ ph ) <-> ps ) $= fceqsexv_0 fceqsexv_1 fceqsexv_2 fceqsexv_3 fceqsexv_1 fceqsexv_2 nfv eceqsexv_0 eceqsexv_1 ceqsex $.
$}
$( Elimination of two existential quantifiers, using implicit
       substitution.  (Contributed by Scott Fenton, 7-Jun-2006.) $)
${
	$d x y A $.
	$d x y B $.
	fceqsex2_0 $f wff ph $.
	fceqsex2_1 $f wff ps $.
	fceqsex2_2 $f wff ch $.
	fceqsex2_3 $f set x $.
	fceqsex2_4 $f set y $.
	fceqsex2_5 $f class A $.
	fceqsex2_6 $f class B $.
	eceqsex2_0 $e |- F/ x ps $.
	eceqsex2_1 $e |- F/ y ch $.
	eceqsex2_2 $e |- A e. _V $.
	eceqsex2_3 $e |- B e. _V $.
	eceqsex2_4 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eceqsex2_5 $e |- ( y = B -> ( ps <-> ch ) ) $.
	ceqsex2 $p |- ( E. x E. y ( x = A /\ y = B /\ ph ) <-> ch ) $= fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 w3a fceqsex2_4 wex fceqsex2_3 wex fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 wa fceqsex2_4 wex wa fceqsex2_3 wex fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_1 wa fceqsex2_4 wex fceqsex2_2 fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 w3a fceqsex2_4 wex fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 wa fceqsex2_4 wex wa fceqsex2_3 fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 w3a fceqsex2_4 wex fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 wa wa fceqsex2_4 wex fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 wa fceqsex2_4 wex wa fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 w3a fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 wa wa fceqsex2_4 fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 3anass exbii fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 wa fceqsex2_4 19.42v bitri exbii fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 wa fceqsex2_4 wex fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_1 wa fceqsex2_4 wex fceqsex2_3 fceqsex2_5 fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_1 wa fceqsex2_3 fceqsex2_4 fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_1 fceqsex2_3 fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_3 nfv eceqsex2_0 nfan nfex eceqsex2_2 fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_0 wa fceqsex2_4 sup_set_class fceqsex2_6 wceq fceqsex2_1 wa fceqsex2_4 fceqsex2_3 sup_set_class fceqsex2_5 wceq fceqsex2_0 fceqsex2_1 fceqsex2_4 sup_set_class fceqsex2_6 wceq eceqsex2_4 anbi2d exbidv ceqsex fceqsex2_1 fceqsex2_2 fceqsex2_4 fceqsex2_6 eceqsex2_1 eceqsex2_3 eceqsex2_5 ceqsex 3bitri $.
$}
$( Elimination of two existential quantifiers, using implicit
       substitution.  (Contributed by Scott Fenton, 7-Jun-2006.) $)
${
	$d x y A $.
	$d x y B $.
	$d x ps $.
	$d y ch $.
	fceqsex2v_0 $f wff ph $.
	fceqsex2v_1 $f wff ps $.
	fceqsex2v_2 $f wff ch $.
	fceqsex2v_3 $f set x $.
	fceqsex2v_4 $f set y $.
	fceqsex2v_5 $f class A $.
	fceqsex2v_6 $f class B $.
	eceqsex2v_0 $e |- A e. _V $.
	eceqsex2v_1 $e |- B e. _V $.
	eceqsex2v_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eceqsex2v_3 $e |- ( y = B -> ( ps <-> ch ) ) $.
	ceqsex2v $p |- ( E. x E. y ( x = A /\ y = B /\ ph ) <-> ch ) $= fceqsex2v_0 fceqsex2v_1 fceqsex2v_2 fceqsex2v_3 fceqsex2v_4 fceqsex2v_5 fceqsex2v_6 fceqsex2v_1 fceqsex2v_3 nfv fceqsex2v_2 fceqsex2v_4 nfv eceqsex2v_0 eceqsex2v_1 eceqsex2v_2 eceqsex2v_3 ceqsex2 $.
$}
$( Elimination of three existential quantifiers, using implicit
       substitution.  (Contributed by NM, 16-Aug-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x ps $.
	$d y ch $.
	$d z th $.
	fceqsex3v_0 $f wff ph $.
	fceqsex3v_1 $f wff ps $.
	fceqsex3v_2 $f wff ch $.
	fceqsex3v_3 $f wff th $.
	fceqsex3v_4 $f set x $.
	fceqsex3v_5 $f set y $.
	fceqsex3v_6 $f set z $.
	fceqsex3v_7 $f class A $.
	fceqsex3v_8 $f class B $.
	fceqsex3v_9 $f class C $.
	eceqsex3v_0 $e |- A e. _V $.
	eceqsex3v_1 $e |- B e. _V $.
	eceqsex3v_2 $e |- C e. _V $.
	eceqsex3v_3 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eceqsex3v_4 $e |- ( y = B -> ( ps <-> ch ) ) $.
	eceqsex3v_5 $e |- ( z = C -> ( ch <-> th ) ) $.
	ceqsex3v $p |- ( E. x E. y E. z ( ( x = A /\ y = B /\ z = C ) /\ ph ) <-> th ) $= fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq w3a fceqsex3v_0 wa fceqsex3v_6 wex fceqsex3v_5 wex fceqsex3v_4 wex fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a fceqsex3v_6 wex fceqsex3v_5 wex wa fceqsex3v_4 wex fceqsex3v_3 fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq w3a fceqsex3v_0 wa fceqsex3v_6 wex fceqsex3v_5 wex fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a fceqsex3v_6 wex fceqsex3v_5 wex wa fceqsex3v_4 fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq w3a fceqsex3v_0 wa fceqsex3v_6 wex fceqsex3v_5 wex fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a wa fceqsex3v_6 wex fceqsex3v_5 wex fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a fceqsex3v_6 wex fceqsex3v_5 wex wa fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq w3a fceqsex3v_0 wa fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a wa fceqsex3v_5 fceqsex3v_6 fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq wa wa fceqsex3v_0 wa fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq wa fceqsex3v_0 wa wa fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq w3a fceqsex3v_0 wa fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a wa fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq wa fceqsex3v_0 anass fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq w3a fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq wa wa fceqsex3v_0 fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq 3anass anbi1i fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq wa fceqsex3v_0 wa fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 df-3an anbi2i 3bitr4i 2exbii fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a fceqsex3v_5 fceqsex3v_6 19.42vv bitri exbii fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a fceqsex3v_6 wex fceqsex3v_5 wex wa fceqsex3v_4 wex fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_1 w3a fceqsex3v_6 wex fceqsex3v_5 wex fceqsex3v_3 fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a fceqsex3v_6 wex fceqsex3v_5 wex fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_1 w3a fceqsex3v_6 wex fceqsex3v_5 wex fceqsex3v_4 fceqsex3v_7 eceqsex3v_0 fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_0 w3a fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq fceqsex3v_1 w3a fceqsex3v_5 fceqsex3v_6 fceqsex3v_4 sup_set_class fceqsex3v_7 wceq fceqsex3v_0 fceqsex3v_1 fceqsex3v_5 sup_set_class fceqsex3v_8 wceq fceqsex3v_6 sup_set_class fceqsex3v_9 wceq eceqsex3v_3 3anbi3d 2exbidv ceqsexv fceqsex3v_1 fceqsex3v_2 fceqsex3v_3 fceqsex3v_5 fceqsex3v_6 fceqsex3v_8 fceqsex3v_9 eceqsex3v_1 eceqsex3v_2 eceqsex3v_4 eceqsex3v_5 ceqsex2v bitri bitri $.
$}
$( Elimination of four existential quantifiers, using implicit
       substitution.  (Contributed by NM, 23-Sep-2011.) $)
${
	$d x y z w A $.
	$d x y z w B $.
	$d x y z w C $.
	$d x y z w D $.
	$d x ps $.
	$d y ch $.
	$d z th $.
	$d w ta $.
	fceqsex4v_0 $f wff ph $.
	fceqsex4v_1 $f wff ps $.
	fceqsex4v_2 $f wff ch $.
	fceqsex4v_3 $f wff th $.
	fceqsex4v_4 $f wff ta $.
	fceqsex4v_5 $f set x $.
	fceqsex4v_6 $f set y $.
	fceqsex4v_7 $f set z $.
	fceqsex4v_8 $f set w $.
	fceqsex4v_9 $f class A $.
	fceqsex4v_10 $f class B $.
	fceqsex4v_11 $f class C $.
	fceqsex4v_12 $f class D $.
	eceqsex4v_0 $e |- A e. _V $.
	eceqsex4v_1 $e |- B e. _V $.
	eceqsex4v_2 $e |- C e. _V $.
	eceqsex4v_3 $e |- D e. _V $.
	eceqsex4v_4 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eceqsex4v_5 $e |- ( y = B -> ( ps <-> ch ) ) $.
	eceqsex4v_6 $e |- ( z = C -> ( ch <-> th ) ) $.
	eceqsex4v_7 $e |- ( w = D -> ( th <-> ta ) ) $.
	ceqsex4v $p |- ( E. x E. y E. z E. w ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) /\ ph ) <-> ta ) $= fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq wa fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex fceqsex4v_6 wex fceqsex4v_5 wex fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex w3a fceqsex4v_6 wex fceqsex4v_5 wex fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_2 w3a fceqsex4v_8 wex fceqsex4v_7 wex fceqsex4v_4 fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq wa fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex w3a fceqsex4v_5 fceqsex4v_6 fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a wa fceqsex4v_8 wex fceqsex4v_7 wex fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex wa fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq wa fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex w3a fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_7 fceqsex4v_8 19.42vv fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq wa fceqsex4v_0 w3a fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a wa fceqsex4v_7 fceqsex4v_8 fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq wa fceqsex4v_0 w3a fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq wa fceqsex4v_0 wa wa fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a wa fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq wa fceqsex4v_0 3anass fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq wa fceqsex4v_0 wa fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq wa fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 df-3an anbi2i bitr4i 2exbii fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_6 sup_set_class fceqsex4v_10 wceq fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex df-3an 3bitr4i 2exbii fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_8 wex fceqsex4v_7 wex fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_1 w3a fceqsex4v_8 wex fceqsex4v_7 wex fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_2 w3a fceqsex4v_8 wex fceqsex4v_7 wex fceqsex4v_5 fceqsex4v_6 fceqsex4v_9 fceqsex4v_10 eceqsex4v_0 eceqsex4v_1 fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_0 w3a fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_1 w3a fceqsex4v_7 fceqsex4v_8 fceqsex4v_5 sup_set_class fceqsex4v_9 wceq fceqsex4v_0 fceqsex4v_1 fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq eceqsex4v_4 3anbi3d 2exbidv fceqsex4v_6 sup_set_class fceqsex4v_10 wceq fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_1 w3a fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq fceqsex4v_2 w3a fceqsex4v_7 fceqsex4v_8 fceqsex4v_6 sup_set_class fceqsex4v_10 wceq fceqsex4v_1 fceqsex4v_2 fceqsex4v_7 sup_set_class fceqsex4v_11 wceq fceqsex4v_8 sup_set_class fceqsex4v_12 wceq eceqsex4v_5 3anbi3d 2exbidv ceqsex2v fceqsex4v_2 fceqsex4v_3 fceqsex4v_4 fceqsex4v_7 fceqsex4v_8 fceqsex4v_11 fceqsex4v_12 eceqsex4v_2 eceqsex4v_3 eceqsex4v_6 eceqsex4v_7 ceqsex2v 3bitri $.
$}
$( Elimination of six existential quantifiers, using implicit
       substitution.  (Contributed by NM, 21-Sep-2011.) $)
${
	$d x y z w v u A $.
	$d x y z w v u B $.
	$d x y z w v u C $.
	$d x y z w v u D $.
	$d x y z w v u E $.
	$d x y z w v u F $.
	$d x ps $.
	$d y ch $.
	$d z th $.
	$d w ta $.
	$d v et $.
	$d u ze $.
	fceqsex6v_0 $f wff ph $.
	fceqsex6v_1 $f wff ps $.
	fceqsex6v_2 $f wff ch $.
	fceqsex6v_3 $f wff th $.
	fceqsex6v_4 $f wff ta $.
	fceqsex6v_5 $f wff et $.
	fceqsex6v_6 $f wff ze $.
	fceqsex6v_7 $f set x $.
	fceqsex6v_8 $f set y $.
	fceqsex6v_9 $f set z $.
	fceqsex6v_10 $f set w $.
	fceqsex6v_11 $f set v $.
	fceqsex6v_12 $f set u $.
	fceqsex6v_13 $f class A $.
	fceqsex6v_14 $f class B $.
	fceqsex6v_15 $f class C $.
	fceqsex6v_16 $f class D $.
	fceqsex6v_17 $f class E $.
	fceqsex6v_18 $f class F $.
	eceqsex6v_0 $e |- A e. _V $.
	eceqsex6v_1 $e |- B e. _V $.
	eceqsex6v_2 $e |- C e. _V $.
	eceqsex6v_3 $e |- D e. _V $.
	eceqsex6v_4 $e |- E e. _V $.
	eceqsex6v_5 $e |- F e. _V $.
	eceqsex6v_6 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eceqsex6v_7 $e |- ( y = B -> ( ps <-> ch ) ) $.
	eceqsex6v_8 $e |- ( z = C -> ( ch <-> th ) ) $.
	eceqsex6v_9 $e |- ( w = D -> ( th <-> ta ) ) $.
	eceqsex6v_10 $e |- ( v = E -> ( ta <-> et ) ) $.
	eceqsex6v_11 $e |- ( u = F -> ( et <-> ze ) ) $.
	ceqsex6v $p |- ( E. x E. y E. z E. w E. v E. u ( ( x = A /\ y = B /\ z = C ) /\ ( w = D /\ v = E /\ u = F ) /\ ph ) <-> ze ) $= fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 w3a fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_9 wex fceqsex6v_8 wex fceqsex6v_7 wex fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex wa fceqsex6v_9 wex fceqsex6v_8 wex fceqsex6v_7 wex fceqsex6v_6 fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 w3a fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex wa fceqsex6v_7 fceqsex6v_8 fceqsex6v_9 fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 w3a fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex wa fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 w3a fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa wa fceqsex6v_10 fceqsex6v_11 fceqsex6v_12 fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 3anass 3exbii fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa fceqsex6v_10 fceqsex6v_11 fceqsex6v_12 19.42vvv bitri 3exbii fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_9 sup_set_class fceqsex6v_15 wceq w3a fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex wa fceqsex6v_9 wex fceqsex6v_8 wex fceqsex6v_7 wex fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_3 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_6 fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_1 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_2 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_3 wa fceqsex6v_12 wex fceqsex6v_11 wex fceqsex6v_10 wex fceqsex6v_7 fceqsex6v_8 fceqsex6v_9 fceqsex6v_13 fceqsex6v_14 fceqsex6v_15 eceqsex6v_0 eceqsex6v_1 eceqsex6v_2 fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_0 wa fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_1 wa fceqsex6v_10 fceqsex6v_11 fceqsex6v_12 fceqsex6v_7 sup_set_class fceqsex6v_13 wceq fceqsex6v_0 fceqsex6v_1 fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a eceqsex6v_6 anbi2d 3exbidv fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_1 wa fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_2 wa fceqsex6v_10 fceqsex6v_11 fceqsex6v_12 fceqsex6v_8 sup_set_class fceqsex6v_14 wceq fceqsex6v_1 fceqsex6v_2 fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a eceqsex6v_7 anbi2d 3exbidv fceqsex6v_9 sup_set_class fceqsex6v_15 wceq fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_2 wa fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a fceqsex6v_3 wa fceqsex6v_10 fceqsex6v_11 fceqsex6v_12 fceqsex6v_9 sup_set_class fceqsex6v_15 wceq fceqsex6v_2 fceqsex6v_3 fceqsex6v_10 sup_set_class fceqsex6v_16 wceq fceqsex6v_11 sup_set_class fceqsex6v_17 wceq fceqsex6v_12 sup_set_class fceqsex6v_18 wceq w3a eceqsex6v_8 anbi2d 3exbidv ceqsex3v fceqsex6v_3 fceqsex6v_4 fceqsex6v_5 fceqsex6v_6 fceqsex6v_10 fceqsex6v_11 fceqsex6v_12 fceqsex6v_16 fceqsex6v_17 fceqsex6v_18 eceqsex6v_3 eceqsex6v_4 eceqsex6v_5 eceqsex6v_9 eceqsex6v_10 eceqsex6v_11 ceqsex3v bitri bitri $.
$}
$( Elimination of eight existential quantifiers, using implicit
       substitution.  (Contributed by NM, 23-Sep-2011.) $)
$v H $.
$v s $.
${
	$d x y z w v u t s A $.
	$d x y z w v u t s B $.
	$d x y z w v u t s C $.
	$d x y z w v u t s D $.
	$d x y z w v u t s E $.
	$d x y z w v u t s F $.
	$d x y z w v u t s G $.
	$d x y z w v u t s H $.
	$d x ps $.
	$d y ch $.
	$d z th $.
	$d w ta $.
	$d v et $.
	$d u ze $.
	$d t si $.
	$d s rh $.
	fceqsex8v_0 $f wff ph $.
	fceqsex8v_1 $f wff ps $.
	fceqsex8v_2 $f wff ch $.
	fceqsex8v_3 $f wff th $.
	fceqsex8v_4 $f wff ta $.
	fceqsex8v_5 $f wff et $.
	fceqsex8v_6 $f wff ze $.
	fceqsex8v_7 $f wff si $.
	fceqsex8v_8 $f wff rh $.
	fceqsex8v_9 $f set x $.
	fceqsex8v_10 $f set y $.
	fceqsex8v_11 $f set z $.
	fceqsex8v_12 $f set w $.
	fceqsex8v_13 $f set v $.
	fceqsex8v_14 $f set u $.
	fceqsex8v_15 $f set t $.
	fceqsex8v_16 $f class A $.
	fceqsex8v_17 $f class B $.
	fceqsex8v_18 $f class C $.
	fceqsex8v_19 $f class D $.
	fceqsex8v_20 $f class E $.
	fceqsex8v_21 $f class F $.
	fceqsex8v_22 $f class G $.
	fceqsex8v_23 $f class H $.
	fceqsex8v_24 $f set s $.
	eceqsex8v_0 $e |- A e. _V $.
	eceqsex8v_1 $e |- B e. _V $.
	eceqsex8v_2 $e |- C e. _V $.
	eceqsex8v_3 $e |- D e. _V $.
	eceqsex8v_4 $e |- E e. _V $.
	eceqsex8v_5 $e |- F e. _V $.
	eceqsex8v_6 $e |- G e. _V $.
	eceqsex8v_7 $e |- H e. _V $.
	eceqsex8v_8 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eceqsex8v_9 $e |- ( y = B -> ( ps <-> ch ) ) $.
	eceqsex8v_10 $e |- ( z = C -> ( ch <-> th ) ) $.
	eceqsex8v_11 $e |- ( w = D -> ( th <-> ta ) ) $.
	eceqsex8v_12 $e |- ( v = E -> ( ta <-> et ) ) $.
	eceqsex8v_13 $e |- ( u = F -> ( et <-> ze ) ) $.
	eceqsex8v_14 $e |- ( t = G -> ( ze <-> si ) ) $.
	eceqsex8v_15 $e |- ( s = H -> ( si <-> rh ) ) $.
	ceqsex8v $p |- ( E. x E. y E. z E. w E. v E. u E. t E. s ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) /\ ( ( v = E /\ u = F ) /\ ( t = G /\ s = H ) ) /\ ph ) <-> rh ) $= fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_12 wex fceqsex8v_11 wex fceqsex8v_10 wex fceqsex8v_9 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex w3a fceqsex8v_12 wex fceqsex8v_11 wex fceqsex8v_10 wex fceqsex8v_9 wex fceqsex8v_8 fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_12 wex fceqsex8v_11 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex w3a fceqsex8v_12 wex fceqsex8v_11 wex fceqsex8v_9 fceqsex8v_10 fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex w3a fceqsex8v_11 fceqsex8v_12 fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a wa fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex wa fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex w3a fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a wa fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex wa fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex wa fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a wa fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex wa fceqsex8v_13 fceqsex8v_14 fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_15 fceqsex8v_24 19.42vv 2exbii fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_13 fceqsex8v_14 19.42vv bitri fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a wa fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_13 fceqsex8v_14 fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 w3a fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a wa fceqsex8v_15 fceqsex8v_24 fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 w3a fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 wa wa fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a wa fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 3anass fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa wa fceqsex8v_0 wa fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 df-3an anbi2i bitr4i 2exbii 2exbii fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex df-3an 3bitr4i 2exbii 2exbii fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_10 sup_set_class fceqsex8v_17 wceq wa fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_12 sup_set_class fceqsex8v_19 wceq wa fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex w3a fceqsex8v_12 wex fceqsex8v_11 wex fceqsex8v_10 wex fceqsex8v_9 wex fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_4 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_8 fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_1 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_2 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_3 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_4 w3a fceqsex8v_24 wex fceqsex8v_15 wex fceqsex8v_14 wex fceqsex8v_13 wex fceqsex8v_9 fceqsex8v_10 fceqsex8v_11 fceqsex8v_12 fceqsex8v_16 fceqsex8v_17 fceqsex8v_18 fceqsex8v_19 eceqsex8v_0 eceqsex8v_1 eceqsex8v_2 eceqsex8v_3 fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_0 w3a fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_1 w3a fceqsex8v_13 fceqsex8v_14 fceqsex8v_15 fceqsex8v_24 fceqsex8v_9 sup_set_class fceqsex8v_16 wceq fceqsex8v_0 fceqsex8v_1 fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa eceqsex8v_8 3anbi3d 4exbidv fceqsex8v_10 sup_set_class fceqsex8v_17 wceq fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_1 w3a fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_2 w3a fceqsex8v_13 fceqsex8v_14 fceqsex8v_15 fceqsex8v_24 fceqsex8v_10 sup_set_class fceqsex8v_17 wceq fceqsex8v_1 fceqsex8v_2 fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa eceqsex8v_9 3anbi3d 4exbidv fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_2 w3a fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_3 w3a fceqsex8v_13 fceqsex8v_14 fceqsex8v_15 fceqsex8v_24 fceqsex8v_11 sup_set_class fceqsex8v_18 wceq fceqsex8v_2 fceqsex8v_3 fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa eceqsex8v_10 3anbi3d 4exbidv fceqsex8v_12 sup_set_class fceqsex8v_19 wceq fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_3 w3a fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa fceqsex8v_4 w3a fceqsex8v_13 fceqsex8v_14 fceqsex8v_15 fceqsex8v_24 fceqsex8v_12 sup_set_class fceqsex8v_19 wceq fceqsex8v_3 fceqsex8v_4 fceqsex8v_13 sup_set_class fceqsex8v_20 wceq fceqsex8v_14 sup_set_class fceqsex8v_21 wceq wa fceqsex8v_15 sup_set_class fceqsex8v_22 wceq fceqsex8v_24 sup_set_class fceqsex8v_23 wceq wa eceqsex8v_11 3anbi3d 4exbidv ceqsex4v fceqsex8v_4 fceqsex8v_5 fceqsex8v_6 fceqsex8v_7 fceqsex8v_8 fceqsex8v_13 fceqsex8v_14 fceqsex8v_15 fceqsex8v_24 fceqsex8v_20 fceqsex8v_21 fceqsex8v_22 fceqsex8v_23 eceqsex8v_4 eceqsex8v_5 eceqsex8v_6 eceqsex8v_7 eceqsex8v_12 eceqsex8v_13 eceqsex8v_14 eceqsex8v_15 ceqsex4v bitri bitri $.
$}
$( Change of bound variable using implicit substitution.  (Contributed by
       NM, 17-May-1996.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
${
	$d x ps $.
	$d y ph $.
	$d x th $.
	$d y ch $.
	$d y A $.
	fgencbvex_0 $f wff ph $.
	fgencbvex_1 $f wff ps $.
	fgencbvex_2 $f wff ch $.
	fgencbvex_3 $f wff th $.
	fgencbvex_4 $f set x $.
	fgencbvex_5 $f set y $.
	fgencbvex_6 $f class A $.
	egencbvex_0 $e |- A e. _V $.
	egencbvex_1 $e |- ( A = y -> ( ph <-> ps ) ) $.
	egencbvex_2 $e |- ( A = y -> ( ch <-> th ) ) $.
	egencbvex_3 $e |- ( th <-> E. x ( ch /\ A = y ) ) $.
	gencbvex $p |- ( E. x ( ch /\ ph ) <-> E. y ( th /\ ps ) ) $= fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_3 fgencbvex_1 wa wa fgencbvex_5 wex fgencbvex_4 wex fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_3 fgencbvex_1 wa wa fgencbvex_4 wex fgencbvex_5 wex fgencbvex_2 fgencbvex_0 wa fgencbvex_4 wex fgencbvex_3 fgencbvex_1 wa fgencbvex_5 wex fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_3 fgencbvex_1 wa wa fgencbvex_4 fgencbvex_5 excom fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_3 fgencbvex_1 wa wa fgencbvex_5 wex fgencbvex_2 fgencbvex_0 wa fgencbvex_4 fgencbvex_3 fgencbvex_1 wa fgencbvex_2 fgencbvex_0 wa fgencbvex_5 fgencbvex_6 egencbvex_0 fgencbvex_3 fgencbvex_1 wa fgencbvex_2 fgencbvex_0 wa wb fgencbvex_6 fgencbvex_5 sup_set_class fgencbvex_6 fgencbvex_5 sup_set_class wceq fgencbvex_2 fgencbvex_0 wa fgencbvex_3 fgencbvex_1 wa fgencbvex_6 fgencbvex_5 sup_set_class wceq fgencbvex_2 fgencbvex_3 fgencbvex_0 fgencbvex_1 egencbvex_2 egencbvex_1 anbi12d bicomd eqcoms ceqsexv exbii fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_3 fgencbvex_1 wa wa fgencbvex_4 wex fgencbvex_3 fgencbvex_1 wa fgencbvex_5 fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_3 fgencbvex_1 wa wa fgencbvex_4 wex fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_4 wex fgencbvex_3 fgencbvex_1 wa wa fgencbvex_3 fgencbvex_1 wa fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_3 fgencbvex_1 wa fgencbvex_4 19.41v fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_4 wex fgencbvex_3 fgencbvex_1 wa wa fgencbvex_3 fgencbvex_1 wa fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_4 wex fgencbvex_3 fgencbvex_1 wa simpr fgencbvex_3 fgencbvex_1 wa fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_4 wex fgencbvex_3 fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_4 wex fgencbvex_1 fgencbvex_3 fgencbvex_2 fgencbvex_6 fgencbvex_5 sup_set_class wceq wa fgencbvex_4 wex fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_4 wex egencbvex_3 fgencbvex_2 fgencbvex_6 fgencbvex_5 sup_set_class wceq wa fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_4 fgencbvex_6 fgencbvex_5 sup_set_class wceq fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_2 fgencbvex_6 fgencbvex_5 sup_set_class wceq fgencbvex_5 sup_set_class fgencbvex_6 wceq fgencbvex_6 fgencbvex_5 sup_set_class eqcom biimpi adantl eximi sylbi adantr ancri impbii bitri exbii 3bitr3i $.
$}
$( Restatement of ~ gencbvex with weaker hypotheses.  (Contributed by
       Jeffrey Hankins, 6-Dec-2006.) $)
${
	$d x ps $.
	$d y ph $.
	$d x th $.
	$d y ch $.
	$d y A $.
	fgencbvex2_0 $f wff ph $.
	fgencbvex2_1 $f wff ps $.
	fgencbvex2_2 $f wff ch $.
	fgencbvex2_3 $f wff th $.
	fgencbvex2_4 $f set x $.
	fgencbvex2_5 $f set y $.
	fgencbvex2_6 $f class A $.
	egencbvex2_0 $e |- A e. _V $.
	egencbvex2_1 $e |- ( A = y -> ( ph <-> ps ) ) $.
	egencbvex2_2 $e |- ( A = y -> ( ch <-> th ) ) $.
	egencbvex2_3 $e |- ( th -> E. x ( ch /\ A = y ) ) $.
	gencbvex2 $p |- ( E. x ( ch /\ ph ) <-> E. y ( th /\ ps ) ) $= fgencbvex2_0 fgencbvex2_1 fgencbvex2_2 fgencbvex2_3 fgencbvex2_4 fgencbvex2_5 fgencbvex2_6 egencbvex2_0 egencbvex2_1 egencbvex2_2 fgencbvex2_3 fgencbvex2_2 fgencbvex2_6 fgencbvex2_5 sup_set_class wceq wa fgencbvex2_4 wex egencbvex2_3 fgencbvex2_2 fgencbvex2_6 fgencbvex2_5 sup_set_class wceq wa fgencbvex2_3 fgencbvex2_4 fgencbvex2_6 fgencbvex2_5 sup_set_class wceq fgencbvex2_2 fgencbvex2_3 egencbvex2_2 biimpac exlimiv impbii gencbvex $.
$}
$( Change of bound variable using implicit substitution.  (Contributed by
       NM, 17-May-1996.) $)
${
	$d x ps $.
	$d y ph $.
	$d x th $.
	$d y ch $.
	$d y A $.
	fgencbval_0 $f wff ph $.
	fgencbval_1 $f wff ps $.
	fgencbval_2 $f wff ch $.
	fgencbval_3 $f wff th $.
	fgencbval_4 $f set x $.
	fgencbval_5 $f set y $.
	fgencbval_6 $f class A $.
	egencbval_0 $e |- A e. _V $.
	egencbval_1 $e |- ( A = y -> ( ph <-> ps ) ) $.
	egencbval_2 $e |- ( A = y -> ( ch <-> th ) ) $.
	egencbval_3 $e |- ( th <-> E. x ( ch /\ A = y ) ) $.
	gencbval $p |- ( A. x ( ch -> ph ) <-> A. y ( th -> ps ) ) $= fgencbval_2 fgencbval_0 wi fgencbval_4 wal fgencbval_3 fgencbval_1 wi fgencbval_5 wal fgencbval_2 fgencbval_0 wn wa fgencbval_4 wex fgencbval_3 fgencbval_1 wn wa fgencbval_5 wex fgencbval_2 fgencbval_0 wi fgencbval_4 wal wn fgencbval_3 fgencbval_1 wi fgencbval_5 wal wn fgencbval_0 wn fgencbval_1 wn fgencbval_2 fgencbval_3 fgencbval_4 fgencbval_5 fgencbval_6 egencbval_0 fgencbval_6 fgencbval_5 sup_set_class wceq fgencbval_0 fgencbval_1 egencbval_1 notbid egencbval_2 egencbval_3 gencbvex fgencbval_2 fgencbval_0 fgencbval_4 exanali fgencbval_3 fgencbval_1 fgencbval_5 exanali 3bitr3i con4bii $.
$}
$( Introduce an explicit substitution into an implicit substitution
       hypothesis.  See also ~ csbhypf .  (Contributed by Raph Levien,
       10-Apr-2004.) $)
${
	$d A x $.
	$d x y $.
	fsbhypf_0 $f wff ph $.
	fsbhypf_1 $f wff ps $.
	fsbhypf_2 $f set x $.
	fsbhypf_3 $f set y $.
	fsbhypf_4 $f class A $.
	esbhypf_0 $e |- F/ x ps $.
	esbhypf_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	sbhypf $p |- ( y = A -> ( [ y / x ] ph <-> ps ) ) $= fsbhypf_3 sup_set_class fsbhypf_4 wceq fsbhypf_2 sup_set_class fsbhypf_3 sup_set_class wceq fsbhypf_2 sup_set_class fsbhypf_4 wceq wa fsbhypf_2 wex fsbhypf_0 fsbhypf_2 fsbhypf_3 wsb fsbhypf_1 wb fsbhypf_2 sup_set_class fsbhypf_4 wceq fsbhypf_3 sup_set_class fsbhypf_4 wceq fsbhypf_2 fsbhypf_3 sup_set_class fsbhypf_3 vex fsbhypf_2 sup_set_class fsbhypf_3 sup_set_class fsbhypf_4 eqeq1 ceqsexv fsbhypf_2 sup_set_class fsbhypf_3 sup_set_class wceq fsbhypf_2 sup_set_class fsbhypf_4 wceq wa fsbhypf_0 fsbhypf_2 fsbhypf_3 wsb fsbhypf_1 wb fsbhypf_2 fsbhypf_0 fsbhypf_2 fsbhypf_3 wsb fsbhypf_1 fsbhypf_2 fsbhypf_0 fsbhypf_2 fsbhypf_3 nfs1v esbhypf_0 nfbi fsbhypf_2 sup_set_class fsbhypf_3 sup_set_class wceq fsbhypf_0 fsbhypf_2 fsbhypf_3 wsb fsbhypf_0 fsbhypf_2 sup_set_class fsbhypf_4 wceq fsbhypf_1 fsbhypf_2 sup_set_class fsbhypf_3 sup_set_class wceq fsbhypf_0 fsbhypf_0 fsbhypf_2 fsbhypf_3 wsb fsbhypf_0 fsbhypf_2 fsbhypf_3 sbequ12 bicomd esbhypf_1 sylan9bb exlimi sylbir $.
$}
$( Closed theorem form of ~ vtoclgf .  (Contributed by NM, 17-Feb-2013.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)
${
	$d z A $.
	$d x z $.
	ivtoclgft_0 $f set z $.
	fvtoclgft_0 $f wff ph $.
	fvtoclgft_1 $f wff ps $.
	fvtoclgft_2 $f set x $.
	fvtoclgft_3 $f class A $.
	fvtoclgft_4 $f class V $.
	vtoclgft $p |- ( ( ( F/_ x A /\ F/ x ps ) /\ ( A. x ( x = A -> ( ph <-> ps ) ) /\ A. x ph ) /\ A e. V ) -> ps ) $= fvtoclgft_3 fvtoclgft_4 wcel fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf wa fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa fvtoclgft_3 cvv wcel fvtoclgft_1 fvtoclgft_3 fvtoclgft_4 elex fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf wa fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa fvtoclgft_3 cvv wcel w3a fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_2 wex fvtoclgft_1 fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf wa fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa fvtoclgft_3 cvv wcel w3a ivtoclgft_0 sup_set_class fvtoclgft_3 wceq ivtoclgft_0 wex fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_2 wex fvtoclgft_3 cvv wcel fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf wa ivtoclgft_0 sup_set_class fvtoclgft_3 wceq ivtoclgft_0 wex fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa ivtoclgft_0 fvtoclgft_3 cvv elisset 3ad2ant3 fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf wa fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa ivtoclgft_0 sup_set_class fvtoclgft_3 wceq ivtoclgft_0 wex fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_2 wex wb fvtoclgft_3 cvv wcel fvtoclgft_2 fvtoclgft_3 wnfc ivtoclgft_0 sup_set_class fvtoclgft_3 wceq ivtoclgft_0 wex fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_2 wex wb fvtoclgft_1 fvtoclgft_2 wnf fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa fvtoclgft_2 fvtoclgft_3 wnfc ivtoclgft_0 sup_set_class fvtoclgft_3 wceq fvtoclgft_2 sup_set_class fvtoclgft_3 wceq ivtoclgft_0 fvtoclgft_2 fvtoclgft_2 fvtoclgft_3 nfnfc1 fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_2 ivtoclgft_0 sup_set_class fvtoclgft_3 fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_2 ivtoclgft_0 sup_set_class nfcvd fvtoclgft_2 fvtoclgft_3 wnfc id nfeqd ivtoclgft_0 sup_set_class fvtoclgft_2 sup_set_class wceq ivtoclgft_0 sup_set_class fvtoclgft_3 wceq fvtoclgft_2 sup_set_class fvtoclgft_3 wceq wb wi fvtoclgft_2 fvtoclgft_3 wnfc ivtoclgft_0 sup_set_class fvtoclgft_2 sup_set_class fvtoclgft_3 eqeq1 a1i cbvexd ad2antrr 3adant3 mpbid fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf wa fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa fvtoclgft_3 cvv wcel w3a fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_1 wi fvtoclgft_2 wal fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_2 wex fvtoclgft_1 wi fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf wa fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_1 wi fvtoclgft_2 wal fvtoclgft_3 cvv wcel fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_0 fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_1 wi fvtoclgft_2 fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_0 fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_1 wi fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 fvtoclgft_0 fvtoclgft_1 wb fvtoclgft_0 fvtoclgft_1 wi fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 bi1 imim2i com23 imp alanimi 3ad2ant2 fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf wa fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa fvtoclgft_3 cvv wcel w3a fvtoclgft_1 fvtoclgft_2 wnf fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_1 wi fvtoclgft_2 wal fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_2 wex fvtoclgft_1 wi wb fvtoclgft_2 fvtoclgft_3 wnfc fvtoclgft_1 fvtoclgft_2 wnf fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_0 fvtoclgft_1 wb wi fvtoclgft_2 wal fvtoclgft_0 fvtoclgft_2 wal wa fvtoclgft_3 cvv wcel simp1r fvtoclgft_2 sup_set_class fvtoclgft_3 wceq fvtoclgft_1 fvtoclgft_2 19.23t syl mpbid mpd syl3an3 $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
         Mario Carneiro, 15-Oct-2016.) $)
${
	fvtocldf_0 $f wff ph $.
	fvtocldf_1 $f wff ps $.
	fvtocldf_2 $f wff ch $.
	fvtocldf_3 $f set x $.
	fvtocldf_4 $f class A $.
	fvtocldf_5 $f class V $.
	evtocldf_0 $e |- ( ph -> A e. V ) $.
	evtocldf_1 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	evtocldf_2 $e |- ( ph -> ps ) $.
	evtocldf_3 $e |- F/ x ph $.
	evtocldf_4 $e |- ( ph -> F/_ x A ) $.
	evtocldf_5 $e |- ( ph -> F/ x ch ) $.
	vtocldf $p |- ( ph -> ch ) $= fvtocldf_0 fvtocldf_3 fvtocldf_4 wnfc fvtocldf_2 fvtocldf_3 wnf fvtocldf_3 sup_set_class fvtocldf_4 wceq fvtocldf_1 fvtocldf_2 wb wi fvtocldf_3 wal fvtocldf_1 fvtocldf_3 wal fvtocldf_4 fvtocldf_5 wcel fvtocldf_2 evtocldf_4 evtocldf_5 fvtocldf_0 fvtocldf_3 sup_set_class fvtocldf_4 wceq fvtocldf_1 fvtocldf_2 wb wi fvtocldf_3 evtocldf_3 fvtocldf_0 fvtocldf_3 sup_set_class fvtocldf_4 wceq fvtocldf_1 fvtocldf_2 wb evtocldf_1 ex alrimi fvtocldf_0 fvtocldf_1 fvtocldf_3 evtocldf_3 evtocldf_2 alrimi evtocldf_0 fvtocldf_1 fvtocldf_2 fvtocldf_3 fvtocldf_4 fvtocldf_5 vtoclgft syl221anc $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       Mario Carneiro, 15-Oct-2016.) $)
${
	$d x A $.
	$d x ph $.
	$d x ch $.
	fvtocld_0 $f wff ph $.
	fvtocld_1 $f wff ps $.
	fvtocld_2 $f wff ch $.
	fvtocld_3 $f set x $.
	fvtocld_4 $f class A $.
	fvtocld_5 $f class V $.
	evtocld_0 $e |- ( ph -> A e. V ) $.
	evtocld_1 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	evtocld_2 $e |- ( ph -> ps ) $.
	vtocld $p |- ( ph -> ch ) $= fvtocld_0 fvtocld_1 fvtocld_2 fvtocld_3 fvtocld_4 fvtocld_5 evtocld_0 evtocld_1 evtocld_2 fvtocld_0 fvtocld_3 nfv fvtocld_0 fvtocld_3 fvtocld_4 nfcvd fvtocld_0 fvtocld_2 fvtocld_3 nfvd vtocldf $.
$}
$( Implicit substitution of a class for a set variable.  This is a
       generalization of ~ chvar .  (Contributed by NM, 30-Aug-1993.) $)
${
	$d x A $.
	fvtoclf_0 $f wff ph $.
	fvtoclf_1 $f wff ps $.
	fvtoclf_2 $f set x $.
	fvtoclf_3 $f class A $.
	evtoclf_0 $e |- F/ x ps $.
	evtoclf_1 $e |- A e. _V $.
	evtoclf_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtoclf_3 $e |- ph $.
	vtoclf $p |- ps $= fvtoclf_0 fvtoclf_1 fvtoclf_2 fvtoclf_0 fvtoclf_1 fvtoclf_2 evtoclf_0 fvtoclf_2 sup_set_class fvtoclf_3 wceq fvtoclf_2 wex fvtoclf_0 fvtoclf_1 wi fvtoclf_2 wex fvtoclf_2 fvtoclf_3 evtoclf_1 isseti fvtoclf_2 sup_set_class fvtoclf_3 wceq fvtoclf_0 fvtoclf_1 wi fvtoclf_2 fvtoclf_2 sup_set_class fvtoclf_3 wceq fvtoclf_0 fvtoclf_1 evtoclf_2 biimpd eximi ax-mp 19.36i evtoclf_3 mpg $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 30-Aug-1993.) $)
${
	$d x A $.
	$d x ps $.
	fvtocl_0 $f wff ph $.
	fvtocl_1 $f wff ps $.
	fvtocl_2 $f set x $.
	fvtocl_3 $f class A $.
	evtocl_0 $e |- A e. _V $.
	evtocl_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtocl_2 $e |- ph $.
	vtocl $p |- ps $= fvtocl_0 fvtocl_1 fvtocl_2 fvtocl_3 fvtocl_1 fvtocl_2 nfv evtocl_0 evtocl_1 evtocl_2 vtoclf $.
$}
$( Implicit substitution of classes for set variables.  (Contributed by NM,
       26-Jul-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	fvtocl2_0 $f wff ph $.
	fvtocl2_1 $f wff ps $.
	fvtocl2_2 $f set x $.
	fvtocl2_3 $f set y $.
	fvtocl2_4 $f class A $.
	fvtocl2_5 $f class B $.
	evtocl2_0 $e |- A e. _V $.
	evtocl2_1 $e |- B e. _V $.
	evtocl2_2 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	evtocl2_3 $e |- ph $.
	vtocl2 $p |- ps $= fvtocl2_0 fvtocl2_3 wal fvtocl2_1 fvtocl2_2 fvtocl2_0 fvtocl2_3 wal fvtocl2_1 fvtocl2_2 fvtocl2_0 fvtocl2_1 wi fvtocl2_3 wex fvtocl2_2 wex fvtocl2_0 fvtocl2_3 wal fvtocl2_1 wi fvtocl2_2 wex fvtocl2_2 sup_set_class fvtocl2_4 wceq fvtocl2_2 wex fvtocl2_3 sup_set_class fvtocl2_5 wceq fvtocl2_3 wex fvtocl2_0 fvtocl2_1 wi fvtocl2_3 wex fvtocl2_2 wex fvtocl2_2 fvtocl2_4 evtocl2_0 isseti fvtocl2_3 fvtocl2_5 evtocl2_1 isseti fvtocl2_2 sup_set_class fvtocl2_4 wceq fvtocl2_2 wex fvtocl2_3 sup_set_class fvtocl2_5 wceq fvtocl2_3 wex wa fvtocl2_2 sup_set_class fvtocl2_4 wceq fvtocl2_3 sup_set_class fvtocl2_5 wceq wa fvtocl2_3 wex fvtocl2_2 wex fvtocl2_0 fvtocl2_1 wi fvtocl2_3 wex fvtocl2_2 wex fvtocl2_2 sup_set_class fvtocl2_4 wceq fvtocl2_3 sup_set_class fvtocl2_5 wceq fvtocl2_2 fvtocl2_3 eeanv fvtocl2_2 sup_set_class fvtocl2_4 wceq fvtocl2_3 sup_set_class fvtocl2_5 wceq wa fvtocl2_0 fvtocl2_1 wi fvtocl2_2 fvtocl2_3 fvtocl2_2 sup_set_class fvtocl2_4 wceq fvtocl2_3 sup_set_class fvtocl2_5 wceq wa fvtocl2_0 fvtocl2_1 evtocl2_2 biimpd 2eximi sylbir mp2an fvtocl2_0 fvtocl2_1 wi fvtocl2_3 wex fvtocl2_0 fvtocl2_3 wal fvtocl2_1 wi fvtocl2_2 fvtocl2_0 fvtocl2_1 fvtocl2_3 19.36v exbii mpbi 19.36aiv fvtocl2_0 fvtocl2_3 evtocl2_3 ax-gen mpg $.
$}
$( Implicit substitution of classes for set variables.  (Contributed by NM,
       3-Jun-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z ps $.
	fvtocl3_0 $f wff ph $.
	fvtocl3_1 $f wff ps $.
	fvtocl3_2 $f set x $.
	fvtocl3_3 $f set y $.
	fvtocl3_4 $f set z $.
	fvtocl3_5 $f class A $.
	fvtocl3_6 $f class B $.
	fvtocl3_7 $f class C $.
	evtocl3_0 $e |- A e. _V $.
	evtocl3_1 $e |- B e. _V $.
	evtocl3_2 $e |- C e. _V $.
	evtocl3_3 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	evtocl3_4 $e |- ph $.
	vtocl3 $p |- ps $= fvtocl3_0 fvtocl3_4 wal fvtocl3_3 wal fvtocl3_1 fvtocl3_2 fvtocl3_0 fvtocl3_4 wal fvtocl3_3 wal fvtocl3_1 fvtocl3_2 fvtocl3_0 fvtocl3_4 wal fvtocl3_1 wi fvtocl3_3 wex fvtocl3_2 wex fvtocl3_0 fvtocl3_4 wal fvtocl3_3 wal fvtocl3_1 wi fvtocl3_2 wex fvtocl3_0 fvtocl3_1 wi fvtocl3_4 wex fvtocl3_3 wex fvtocl3_2 wex fvtocl3_0 fvtocl3_4 wal fvtocl3_1 wi fvtocl3_3 wex fvtocl3_2 wex fvtocl3_2 sup_set_class fvtocl3_5 wceq fvtocl3_2 wex fvtocl3_3 sup_set_class fvtocl3_6 wceq fvtocl3_3 wex fvtocl3_4 sup_set_class fvtocl3_7 wceq fvtocl3_4 wex fvtocl3_0 fvtocl3_1 wi fvtocl3_4 wex fvtocl3_3 wex fvtocl3_2 wex fvtocl3_2 fvtocl3_5 evtocl3_0 isseti fvtocl3_3 fvtocl3_6 evtocl3_1 isseti fvtocl3_4 fvtocl3_7 evtocl3_2 isseti fvtocl3_2 sup_set_class fvtocl3_5 wceq fvtocl3_2 wex fvtocl3_3 sup_set_class fvtocl3_6 wceq fvtocl3_3 wex fvtocl3_4 sup_set_class fvtocl3_7 wceq fvtocl3_4 wex w3a fvtocl3_2 sup_set_class fvtocl3_5 wceq fvtocl3_3 sup_set_class fvtocl3_6 wceq fvtocl3_4 sup_set_class fvtocl3_7 wceq w3a fvtocl3_4 wex fvtocl3_3 wex fvtocl3_2 wex fvtocl3_0 fvtocl3_1 wi fvtocl3_4 wex fvtocl3_3 wex fvtocl3_2 wex fvtocl3_2 sup_set_class fvtocl3_5 wceq fvtocl3_3 sup_set_class fvtocl3_6 wceq fvtocl3_4 sup_set_class fvtocl3_7 wceq fvtocl3_2 fvtocl3_3 fvtocl3_4 eeeanv fvtocl3_2 sup_set_class fvtocl3_5 wceq fvtocl3_3 sup_set_class fvtocl3_6 wceq fvtocl3_4 sup_set_class fvtocl3_7 wceq w3a fvtocl3_4 wex fvtocl3_0 fvtocl3_1 wi fvtocl3_4 wex fvtocl3_2 fvtocl3_3 fvtocl3_2 sup_set_class fvtocl3_5 wceq fvtocl3_3 sup_set_class fvtocl3_6 wceq fvtocl3_4 sup_set_class fvtocl3_7 wceq w3a fvtocl3_0 fvtocl3_1 wi fvtocl3_4 fvtocl3_2 sup_set_class fvtocl3_5 wceq fvtocl3_3 sup_set_class fvtocl3_6 wceq fvtocl3_4 sup_set_class fvtocl3_7 wceq w3a fvtocl3_0 fvtocl3_1 evtocl3_3 biimpd eximi 2eximi sylbir mp3an fvtocl3_0 fvtocl3_1 wi fvtocl3_4 wex fvtocl3_0 fvtocl3_4 wal fvtocl3_1 wi fvtocl3_2 fvtocl3_3 fvtocl3_0 fvtocl3_1 fvtocl3_4 19.36v 2exbii mpbi fvtocl3_0 fvtocl3_4 wal fvtocl3_1 wi fvtocl3_3 wex fvtocl3_0 fvtocl3_4 wal fvtocl3_3 wal fvtocl3_1 wi fvtocl3_2 fvtocl3_0 fvtocl3_4 wal fvtocl3_1 fvtocl3_3 19.36v exbii mpbi 19.36aiv fvtocl3_0 fvtocl3_3 fvtocl3_4 evtocl3_4 gen2 mpg $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 23-Dec-1993.) $)
${
	$d x A $.
	$d x ch $.
	$d x th $.
	fvtoclb_0 $f wff ph $.
	fvtoclb_1 $f wff ps $.
	fvtoclb_2 $f wff ch $.
	fvtoclb_3 $f wff th $.
	fvtoclb_4 $f set x $.
	fvtoclb_5 $f class A $.
	evtoclb_0 $e |- A e. _V $.
	evtoclb_1 $e |- ( x = A -> ( ph <-> ch ) ) $.
	evtoclb_2 $e |- ( x = A -> ( ps <-> th ) ) $.
	evtoclb_3 $e |- ( ph <-> ps ) $.
	vtoclb $p |- ( ch <-> th ) $= fvtoclb_0 fvtoclb_1 wb fvtoclb_2 fvtoclb_3 wb fvtoclb_4 fvtoclb_5 evtoclb_0 fvtoclb_4 sup_set_class fvtoclb_5 wceq fvtoclb_0 fvtoclb_2 fvtoclb_1 fvtoclb_3 evtoclb_1 evtoclb_2 bibi12d evtoclb_3 vtocl $.
$}
$( Implicit substitution of a class for a set variable, with bound-variable
       hypotheses in place of distinct variable restrictions.  (Contributed by
       NM, 21-Sep-2003.)  (Proof shortened by Mario Carneiro, 10-Oct-2016.) $)
${
	fvtoclgf_0 $f wff ph $.
	fvtoclgf_1 $f wff ps $.
	fvtoclgf_2 $f set x $.
	fvtoclgf_3 $f class A $.
	fvtoclgf_4 $f class V $.
	evtoclgf_0 $e |- F/_ x A $.
	evtoclgf_1 $e |- F/ x ps $.
	evtoclgf_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtoclgf_3 $e |- ph $.
	vtoclgf $p |- ( A e. V -> ps ) $= fvtoclgf_3 fvtoclgf_4 wcel fvtoclgf_3 cvv wcel fvtoclgf_1 fvtoclgf_3 fvtoclgf_4 elex fvtoclgf_3 cvv wcel fvtoclgf_2 sup_set_class fvtoclgf_3 wceq fvtoclgf_2 wex fvtoclgf_1 fvtoclgf_2 fvtoclgf_3 evtoclgf_0 issetf fvtoclgf_2 sup_set_class fvtoclgf_3 wceq fvtoclgf_1 fvtoclgf_2 evtoclgf_1 fvtoclgf_2 sup_set_class fvtoclgf_3 wceq fvtoclgf_0 fvtoclgf_1 evtoclgf_3 evtoclgf_2 mpbii exlimi sylbi syl $.
$}
$( Implicit substitution of a class expression for a set variable.
       (Contributed by NM, 17-Apr-1995.) $)
${
	$d x A $.
	$d x ps $.
	fvtoclg_0 $f wff ph $.
	fvtoclg_1 $f wff ps $.
	fvtoclg_2 $f set x $.
	fvtoclg_3 $f class A $.
	fvtoclg_4 $f class V $.
	evtoclg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtoclg_1 $e |- ph $.
	vtoclg $p |- ( A e. V -> ps ) $= fvtoclg_0 fvtoclg_1 fvtoclg_2 fvtoclg_3 fvtoclg_4 fvtoclg_2 fvtoclg_3 nfcv fvtoclg_1 fvtoclg_2 nfv evtoclg_0 evtoclg_1 vtoclgf $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 29-Apr-1994.) $)
${
	$d x A $.
	$d x ch $.
	$d x th $.
	fvtoclbg_0 $f wff ph $.
	fvtoclbg_1 $f wff ps $.
	fvtoclbg_2 $f wff ch $.
	fvtoclbg_3 $f wff th $.
	fvtoclbg_4 $f set x $.
	fvtoclbg_5 $f class A $.
	fvtoclbg_6 $f class V $.
	evtoclbg_0 $e |- ( x = A -> ( ph <-> ch ) ) $.
	evtoclbg_1 $e |- ( x = A -> ( ps <-> th ) ) $.
	evtoclbg_2 $e |- ( ph <-> ps ) $.
	vtoclbg $p |- ( A e. V -> ( ch <-> th ) ) $= fvtoclbg_0 fvtoclbg_1 wb fvtoclbg_2 fvtoclbg_3 wb fvtoclbg_4 fvtoclbg_5 fvtoclbg_6 fvtoclbg_4 sup_set_class fvtoclbg_5 wceq fvtoclbg_0 fvtoclbg_2 fvtoclbg_1 fvtoclbg_3 evtoclbg_0 evtoclbg_1 bibi12d evtoclbg_2 vtoclg $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 25-Apr-1995.) $)
${
	fvtocl2gf_0 $f wff ph $.
	fvtocl2gf_1 $f wff ps $.
	fvtocl2gf_2 $f wff ch $.
	fvtocl2gf_3 $f set x $.
	fvtocl2gf_4 $f set y $.
	fvtocl2gf_5 $f class A $.
	fvtocl2gf_6 $f class B $.
	fvtocl2gf_7 $f class V $.
	fvtocl2gf_8 $f class W $.
	evtocl2gf_0 $e |- F/_ x A $.
	evtocl2gf_1 $e |- F/_ y A $.
	evtocl2gf_2 $e |- F/_ y B $.
	evtocl2gf_3 $e |- F/ x ps $.
	evtocl2gf_4 $e |- F/ y ch $.
	evtocl2gf_5 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtocl2gf_6 $e |- ( y = B -> ( ps <-> ch ) ) $.
	evtocl2gf_7 $e |- ph $.
	vtocl2gf $p |- ( ( A e. V /\ B e. W ) -> ch ) $= fvtocl2gf_5 fvtocl2gf_7 wcel fvtocl2gf_5 cvv wcel fvtocl2gf_6 fvtocl2gf_8 wcel fvtocl2gf_2 fvtocl2gf_5 fvtocl2gf_7 elex fvtocl2gf_5 cvv wcel fvtocl2gf_1 wi fvtocl2gf_5 cvv wcel fvtocl2gf_2 wi fvtocl2gf_4 fvtocl2gf_6 fvtocl2gf_8 evtocl2gf_2 fvtocl2gf_5 cvv wcel fvtocl2gf_2 fvtocl2gf_4 fvtocl2gf_4 fvtocl2gf_5 cvv evtocl2gf_1 nfel1 evtocl2gf_4 nfim fvtocl2gf_4 sup_set_class fvtocl2gf_6 wceq fvtocl2gf_1 fvtocl2gf_2 fvtocl2gf_5 cvv wcel evtocl2gf_6 imbi2d fvtocl2gf_0 fvtocl2gf_1 fvtocl2gf_3 fvtocl2gf_5 cvv evtocl2gf_0 evtocl2gf_3 evtocl2gf_5 evtocl2gf_7 vtoclgf vtoclgf mpan9 $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 10-Aug-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)
$v X $.
${
	fvtocl3gf_0 $f wff ph $.
	fvtocl3gf_1 $f wff ps $.
	fvtocl3gf_2 $f wff ch $.
	fvtocl3gf_3 $f wff th $.
	fvtocl3gf_4 $f set x $.
	fvtocl3gf_5 $f set y $.
	fvtocl3gf_6 $f set z $.
	fvtocl3gf_7 $f class A $.
	fvtocl3gf_8 $f class B $.
	fvtocl3gf_9 $f class C $.
	fvtocl3gf_10 $f class V $.
	fvtocl3gf_11 $f class W $.
	fvtocl3gf_12 $f class X $.
	evtocl3gf_0 $e |- F/_ x A $.
	evtocl3gf_1 $e |- F/_ y A $.
	evtocl3gf_2 $e |- F/_ z A $.
	evtocl3gf_3 $e |- F/_ y B $.
	evtocl3gf_4 $e |- F/_ z B $.
	evtocl3gf_5 $e |- F/_ z C $.
	evtocl3gf_6 $e |- F/ x ps $.
	evtocl3gf_7 $e |- F/ y ch $.
	evtocl3gf_8 $e |- F/ z th $.
	evtocl3gf_9 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtocl3gf_10 $e |- ( y = B -> ( ps <-> ch ) ) $.
	evtocl3gf_11 $e |- ( z = C -> ( ch <-> th ) ) $.
	evtocl3gf_12 $e |- ph $.
	vtocl3gf $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> th ) $= fvtocl3gf_7 fvtocl3gf_10 wcel fvtocl3gf_8 fvtocl3gf_11 wcel fvtocl3gf_9 fvtocl3gf_12 wcel fvtocl3gf_3 fvtocl3gf_7 fvtocl3gf_10 wcel fvtocl3gf_7 cvv wcel fvtocl3gf_8 fvtocl3gf_11 wcel fvtocl3gf_9 fvtocl3gf_12 wcel wa fvtocl3gf_3 fvtocl3gf_7 fvtocl3gf_10 elex fvtocl3gf_7 cvv wcel fvtocl3gf_1 wi fvtocl3gf_7 cvv wcel fvtocl3gf_2 wi fvtocl3gf_7 cvv wcel fvtocl3gf_3 wi fvtocl3gf_5 fvtocl3gf_6 fvtocl3gf_8 fvtocl3gf_9 fvtocl3gf_11 fvtocl3gf_12 evtocl3gf_3 evtocl3gf_4 evtocl3gf_5 fvtocl3gf_7 cvv wcel fvtocl3gf_2 fvtocl3gf_5 fvtocl3gf_5 fvtocl3gf_7 cvv evtocl3gf_1 nfel1 evtocl3gf_7 nfim fvtocl3gf_7 cvv wcel fvtocl3gf_3 fvtocl3gf_6 fvtocl3gf_6 fvtocl3gf_7 cvv evtocl3gf_2 nfel1 evtocl3gf_8 nfim fvtocl3gf_5 sup_set_class fvtocl3gf_8 wceq fvtocl3gf_1 fvtocl3gf_2 fvtocl3gf_7 cvv wcel evtocl3gf_10 imbi2d fvtocl3gf_6 sup_set_class fvtocl3gf_9 wceq fvtocl3gf_2 fvtocl3gf_3 fvtocl3gf_7 cvv wcel evtocl3gf_11 imbi2d fvtocl3gf_0 fvtocl3gf_1 fvtocl3gf_4 fvtocl3gf_7 cvv evtocl3gf_0 evtocl3gf_6 evtocl3gf_9 evtocl3gf_12 vtoclgf vtocl2gf mpan9 3impb $.
$}
$( Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 25-Apr-1995.) $)
${
	$d x A $.
	$d y A $.
	$d y B $.
	$d x ps $.
	$d y ch $.
	fvtocl2g_0 $f wff ph $.
	fvtocl2g_1 $f wff ps $.
	fvtocl2g_2 $f wff ch $.
	fvtocl2g_3 $f set x $.
	fvtocl2g_4 $f set y $.
	fvtocl2g_5 $f class A $.
	fvtocl2g_6 $f class B $.
	fvtocl2g_7 $f class V $.
	fvtocl2g_8 $f class W $.
	evtocl2g_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtocl2g_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	evtocl2g_2 $e |- ph $.
	vtocl2g $p |- ( ( A e. V /\ B e. W ) -> ch ) $= fvtocl2g_0 fvtocl2g_1 fvtocl2g_2 fvtocl2g_3 fvtocl2g_4 fvtocl2g_5 fvtocl2g_6 fvtocl2g_7 fvtocl2g_8 fvtocl2g_3 fvtocl2g_5 nfcv fvtocl2g_4 fvtocl2g_5 nfcv fvtocl2g_4 fvtocl2g_6 nfcv fvtocl2g_1 fvtocl2g_3 nfv fvtocl2g_2 fvtocl2g_4 nfv evtocl2g_0 evtocl2g_1 evtocl2g_2 vtocl2gf $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 17-Feb-2006.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)
${
	$d x B $.
	fvtoclgaf_0 $f wff ph $.
	fvtoclgaf_1 $f wff ps $.
	fvtoclgaf_2 $f set x $.
	fvtoclgaf_3 $f class A $.
	fvtoclgaf_4 $f class B $.
	evtoclgaf_0 $e |- F/_ x A $.
	evtoclgaf_1 $e |- F/ x ps $.
	evtoclgaf_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtoclgaf_3 $e |- ( x e. B -> ph ) $.
	vtoclgaf $p |- ( A e. B -> ps ) $= fvtoclgaf_3 fvtoclgaf_4 wcel fvtoclgaf_1 fvtoclgaf_2 sup_set_class fvtoclgaf_4 wcel fvtoclgaf_0 wi fvtoclgaf_3 fvtoclgaf_4 wcel fvtoclgaf_1 wi fvtoclgaf_2 fvtoclgaf_3 fvtoclgaf_4 evtoclgaf_0 fvtoclgaf_3 fvtoclgaf_4 wcel fvtoclgaf_1 fvtoclgaf_2 fvtoclgaf_2 fvtoclgaf_3 fvtoclgaf_4 evtoclgaf_0 nfel1 evtoclgaf_1 nfim fvtoclgaf_2 sup_set_class fvtoclgaf_3 wceq fvtoclgaf_2 sup_set_class fvtoclgaf_4 wcel fvtoclgaf_3 fvtoclgaf_4 wcel fvtoclgaf_0 fvtoclgaf_1 fvtoclgaf_2 sup_set_class fvtoclgaf_3 fvtoclgaf_4 eleq1 evtoclgaf_2 imbi12d evtoclgaf_3 vtoclgf pm2.43i $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 20-Aug-1995.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	fvtoclga_0 $f wff ph $.
	fvtoclga_1 $f wff ps $.
	fvtoclga_2 $f set x $.
	fvtoclga_3 $f class A $.
	fvtoclga_4 $f class B $.
	evtoclga_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtoclga_1 $e |- ( x e. B -> ph ) $.
	vtoclga $p |- ( A e. B -> ps ) $= fvtoclga_0 fvtoclga_1 fvtoclga_2 fvtoclga_3 fvtoclga_4 fvtoclga_2 fvtoclga_3 nfcv fvtoclga_1 fvtoclga_2 nfv evtoclga_0 evtoclga_1 vtoclgaf $.
$}
$( Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 10-Aug-2013.) $)
${
	$d x y C $.
	$d x y D $.
	fvtocl2gaf_0 $f wff ph $.
	fvtocl2gaf_1 $f wff ps $.
	fvtocl2gaf_2 $f wff ch $.
	fvtocl2gaf_3 $f set x $.
	fvtocl2gaf_4 $f set y $.
	fvtocl2gaf_5 $f class A $.
	fvtocl2gaf_6 $f class B $.
	fvtocl2gaf_7 $f class C $.
	fvtocl2gaf_8 $f class D $.
	evtocl2gaf_0 $e |- F/_ x A $.
	evtocl2gaf_1 $e |- F/_ y A $.
	evtocl2gaf_2 $e |- F/_ y B $.
	evtocl2gaf_3 $e |- F/ x ps $.
	evtocl2gaf_4 $e |- F/ y ch $.
	evtocl2gaf_5 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtocl2gaf_6 $e |- ( y = B -> ( ps <-> ch ) ) $.
	evtocl2gaf_7 $e |- ( ( x e. C /\ y e. D ) -> ph ) $.
	vtocl2gaf $p |- ( ( A e. C /\ B e. D ) -> ch ) $= fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_6 fvtocl2gaf_8 wcel wa fvtocl2gaf_2 fvtocl2gaf_3 sup_set_class fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel wa fvtocl2gaf_0 wi fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel wa fvtocl2gaf_1 wi fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_6 fvtocl2gaf_8 wcel wa fvtocl2gaf_2 wi fvtocl2gaf_3 fvtocl2gaf_4 fvtocl2gaf_5 fvtocl2gaf_6 fvtocl2gaf_7 fvtocl2gaf_8 evtocl2gaf_0 evtocl2gaf_1 evtocl2gaf_2 fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel wa fvtocl2gaf_1 fvtocl2gaf_3 fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel fvtocl2gaf_3 fvtocl2gaf_3 fvtocl2gaf_5 fvtocl2gaf_7 evtocl2gaf_0 nfel1 fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel fvtocl2gaf_3 nfv nfan evtocl2gaf_3 nfim fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_6 fvtocl2gaf_8 wcel wa fvtocl2gaf_2 fvtocl2gaf_4 fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_6 fvtocl2gaf_8 wcel fvtocl2gaf_4 fvtocl2gaf_4 fvtocl2gaf_5 fvtocl2gaf_7 evtocl2gaf_1 nfel1 fvtocl2gaf_4 fvtocl2gaf_6 fvtocl2gaf_8 evtocl2gaf_2 nfel1 nfan evtocl2gaf_4 nfim fvtocl2gaf_3 sup_set_class fvtocl2gaf_5 wceq fvtocl2gaf_3 sup_set_class fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel wa fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel wa fvtocl2gaf_0 fvtocl2gaf_1 fvtocl2gaf_3 sup_set_class fvtocl2gaf_5 wceq fvtocl2gaf_3 sup_set_class fvtocl2gaf_7 wcel fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel fvtocl2gaf_3 sup_set_class fvtocl2gaf_5 fvtocl2gaf_7 eleq1 anbi1d evtocl2gaf_5 imbi12d fvtocl2gaf_4 sup_set_class fvtocl2gaf_6 wceq fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel wa fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_6 fvtocl2gaf_8 wcel wa fvtocl2gaf_1 fvtocl2gaf_2 fvtocl2gaf_4 sup_set_class fvtocl2gaf_6 wceq fvtocl2gaf_4 sup_set_class fvtocl2gaf_8 wcel fvtocl2gaf_6 fvtocl2gaf_8 wcel fvtocl2gaf_5 fvtocl2gaf_7 wcel fvtocl2gaf_4 sup_set_class fvtocl2gaf_6 fvtocl2gaf_8 eleq1 anbi2d evtocl2gaf_6 imbi12d evtocl2gaf_7 vtocl2gf pm2.43i $.
$}
$( Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 20-Aug-1995.) $)
${
	$d x y A $.
	$d y B $.
	$d x y C $.
	$d x y D $.
	$d x ps $.
	$d y ch $.
	fvtocl2ga_0 $f wff ph $.
	fvtocl2ga_1 $f wff ps $.
	fvtocl2ga_2 $f wff ch $.
	fvtocl2ga_3 $f set x $.
	fvtocl2ga_4 $f set y $.
	fvtocl2ga_5 $f class A $.
	fvtocl2ga_6 $f class B $.
	fvtocl2ga_7 $f class C $.
	fvtocl2ga_8 $f class D $.
	evtocl2ga_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtocl2ga_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	evtocl2ga_2 $e |- ( ( x e. C /\ y e. D ) -> ph ) $.
	vtocl2ga $p |- ( ( A e. C /\ B e. D ) -> ch ) $= fvtocl2ga_0 fvtocl2ga_1 fvtocl2ga_2 fvtocl2ga_3 fvtocl2ga_4 fvtocl2ga_5 fvtocl2ga_6 fvtocl2ga_7 fvtocl2ga_8 fvtocl2ga_3 fvtocl2ga_5 nfcv fvtocl2ga_4 fvtocl2ga_5 nfcv fvtocl2ga_4 fvtocl2ga_6 nfcv fvtocl2ga_1 fvtocl2ga_3 nfv fvtocl2ga_2 fvtocl2ga_4 nfv evtocl2ga_0 evtocl2ga_1 evtocl2ga_2 vtocl2gaf $.
$}
$( Implicit substitution of 3 classes for 3 set variables.  (Contributed by
       NM, 10-Aug-2013.)  (Revised by Mario Carneiro, 11-Oct-2016.) $)
$v T $.
${
	$d x y z R $.
	$d x y z S $.
	$d x y z T $.
	fvtocl3gaf_0 $f wff ph $.
	fvtocl3gaf_1 $f wff ps $.
	fvtocl3gaf_2 $f wff ch $.
	fvtocl3gaf_3 $f wff th $.
	fvtocl3gaf_4 $f set x $.
	fvtocl3gaf_5 $f set y $.
	fvtocl3gaf_6 $f set z $.
	fvtocl3gaf_7 $f class A $.
	fvtocl3gaf_8 $f class B $.
	fvtocl3gaf_9 $f class C $.
	fvtocl3gaf_10 $f class R $.
	fvtocl3gaf_11 $f class S $.
	fvtocl3gaf_12 $f class T $.
	evtocl3gaf_0 $e |- F/_ x A $.
	evtocl3gaf_1 $e |- F/_ y A $.
	evtocl3gaf_2 $e |- F/_ z A $.
	evtocl3gaf_3 $e |- F/_ y B $.
	evtocl3gaf_4 $e |- F/_ z B $.
	evtocl3gaf_5 $e |- F/_ z C $.
	evtocl3gaf_6 $e |- F/ x ps $.
	evtocl3gaf_7 $e |- F/ y ch $.
	evtocl3gaf_8 $e |- F/ z th $.
	evtocl3gaf_9 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtocl3gaf_10 $e |- ( y = B -> ( ps <-> ch ) ) $.
	evtocl3gaf_11 $e |- ( z = C -> ( ch <-> th ) ) $.
	evtocl3gaf_12 $e |- ( ( x e. R /\ y e. S /\ z e. T ) -> ph ) $.
	vtocl3gaf $p |- ( ( A e. R /\ B e. S /\ C e. T ) -> th ) $= fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_9 fvtocl3gaf_12 wcel w3a fvtocl3gaf_3 fvtocl3gaf_4 sup_set_class fvtocl3gaf_10 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_0 wi fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_1 wi fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_2 wi fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_9 fvtocl3gaf_12 wcel w3a fvtocl3gaf_3 wi fvtocl3gaf_4 fvtocl3gaf_5 fvtocl3gaf_6 fvtocl3gaf_7 fvtocl3gaf_8 fvtocl3gaf_9 fvtocl3gaf_10 fvtocl3gaf_11 fvtocl3gaf_12 evtocl3gaf_0 evtocl3gaf_1 evtocl3gaf_2 evtocl3gaf_3 evtocl3gaf_4 evtocl3gaf_5 fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_1 fvtocl3gaf_4 fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel fvtocl3gaf_4 fvtocl3gaf_4 fvtocl3gaf_7 fvtocl3gaf_10 evtocl3gaf_0 nfel1 fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_4 nfv fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel fvtocl3gaf_4 nfv nf3an evtocl3gaf_6 nfim fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_2 fvtocl3gaf_5 fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel fvtocl3gaf_5 fvtocl3gaf_5 fvtocl3gaf_7 fvtocl3gaf_10 evtocl3gaf_1 nfel1 fvtocl3gaf_5 fvtocl3gaf_8 fvtocl3gaf_11 evtocl3gaf_3 nfel1 fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel fvtocl3gaf_5 nfv nf3an evtocl3gaf_7 nfim fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_9 fvtocl3gaf_12 wcel w3a fvtocl3gaf_3 fvtocl3gaf_6 fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_9 fvtocl3gaf_12 wcel fvtocl3gaf_6 fvtocl3gaf_6 fvtocl3gaf_7 fvtocl3gaf_10 evtocl3gaf_2 nfel1 fvtocl3gaf_6 fvtocl3gaf_8 fvtocl3gaf_11 evtocl3gaf_4 nfel1 fvtocl3gaf_6 fvtocl3gaf_9 fvtocl3gaf_12 evtocl3gaf_5 nfel1 nf3an evtocl3gaf_8 nfim fvtocl3gaf_4 sup_set_class fvtocl3gaf_7 wceq fvtocl3gaf_4 sup_set_class fvtocl3gaf_10 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_0 fvtocl3gaf_1 fvtocl3gaf_4 sup_set_class fvtocl3gaf_7 wceq fvtocl3gaf_4 sup_set_class fvtocl3gaf_10 wcel fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel fvtocl3gaf_4 sup_set_class fvtocl3gaf_7 fvtocl3gaf_10 eleq1 3anbi1d evtocl3gaf_9 imbi12d fvtocl3gaf_5 sup_set_class fvtocl3gaf_8 wceq fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_1 fvtocl3gaf_2 fvtocl3gaf_5 sup_set_class fvtocl3gaf_8 wceq fvtocl3gaf_5 sup_set_class fvtocl3gaf_11 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel fvtocl3gaf_5 sup_set_class fvtocl3gaf_8 fvtocl3gaf_11 eleq1 3anbi2d evtocl3gaf_10 imbi12d fvtocl3gaf_6 sup_set_class fvtocl3gaf_9 wceq fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel w3a fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_9 fvtocl3gaf_12 wcel w3a fvtocl3gaf_2 fvtocl3gaf_3 fvtocl3gaf_6 sup_set_class fvtocl3gaf_9 wceq fvtocl3gaf_6 sup_set_class fvtocl3gaf_12 wcel fvtocl3gaf_9 fvtocl3gaf_12 wcel fvtocl3gaf_7 fvtocl3gaf_10 wcel fvtocl3gaf_8 fvtocl3gaf_11 wcel fvtocl3gaf_6 sup_set_class fvtocl3gaf_9 fvtocl3gaf_12 eleq1 3anbi3d evtocl3gaf_11 imbi12d evtocl3gaf_12 vtocl3gf pm2.43i $.
$}
$( Implicit substitution of 3 classes for 3 set variables.  (Contributed by
       NM, 20-Aug-1995.) $)
${
	$d x y z A $.
	$d y z B $.
	$d z C $.
	$d x y z D $.
	$d x y z R $.
	$d x y z S $.
	$d x ps $.
	$d y ch $.
	$d z th $.
	fvtocl3ga_0 $f wff ph $.
	fvtocl3ga_1 $f wff ps $.
	fvtocl3ga_2 $f wff ch $.
	fvtocl3ga_3 $f wff th $.
	fvtocl3ga_4 $f set x $.
	fvtocl3ga_5 $f set y $.
	fvtocl3ga_6 $f set z $.
	fvtocl3ga_7 $f class A $.
	fvtocl3ga_8 $f class B $.
	fvtocl3ga_9 $f class C $.
	fvtocl3ga_10 $f class D $.
	fvtocl3ga_11 $f class R $.
	fvtocl3ga_12 $f class S $.
	evtocl3ga_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtocl3ga_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	evtocl3ga_2 $e |- ( z = C -> ( ch <-> th ) ) $.
	evtocl3ga_3 $e |- ( ( x e. D /\ y e. R /\ z e. S ) -> ph ) $.
	vtocl3ga $p |- ( ( A e. D /\ B e. R /\ C e. S ) -> th ) $= fvtocl3ga_0 fvtocl3ga_1 fvtocl3ga_2 fvtocl3ga_3 fvtocl3ga_4 fvtocl3ga_5 fvtocl3ga_6 fvtocl3ga_7 fvtocl3ga_8 fvtocl3ga_9 fvtocl3ga_10 fvtocl3ga_11 fvtocl3ga_12 fvtocl3ga_4 fvtocl3ga_7 nfcv fvtocl3ga_5 fvtocl3ga_7 nfcv fvtocl3ga_6 fvtocl3ga_7 nfcv fvtocl3ga_5 fvtocl3ga_8 nfcv fvtocl3ga_6 fvtocl3ga_8 nfcv fvtocl3ga_6 fvtocl3ga_9 nfcv fvtocl3ga_1 fvtocl3ga_4 nfv fvtocl3ga_2 fvtocl3ga_5 nfv fvtocl3ga_3 fvtocl3ga_6 nfv evtocl3ga_0 evtocl3ga_1 evtocl3ga_2 evtocl3ga_3 vtocl3gaf $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 10-Jan-2004.) $)
${
	$d x A $.
	$d x ph $.
	fvtocleg_0 $f wff ph $.
	fvtocleg_1 $f set x $.
	fvtocleg_2 $f class A $.
	fvtocleg_3 $f class V $.
	evtocleg_0 $e |- ( x = A -> ph ) $.
	vtocleg $p |- ( A e. V -> ph ) $= fvtocleg_2 fvtocleg_3 wcel fvtocleg_1 sup_set_class fvtocleg_2 wceq fvtocleg_1 wex fvtocleg_0 fvtocleg_1 fvtocleg_2 fvtocleg_3 elisset fvtocleg_1 sup_set_class fvtocleg_2 wceq fvtocleg_0 fvtocleg_1 evtocleg_0 exlimiv syl $.
$}
$( Implicit substitution of a class for a set variable.  (Closed theorem
       version of ~ vtoclef .)  (Contributed by NM, 7-Nov-2005.)  (Revised by
       Mario Carneiro, 11-Oct-2016.) $)
${
	$d x A $.
	fvtoclegft_0 $f wff ph $.
	fvtoclegft_1 $f set x $.
	fvtoclegft_2 $f class A $.
	fvtoclegft_3 $f class B $.
	vtoclegft $p |- ( ( A e. B /\ F/ x ph /\ A. x ( x = A -> ph ) ) -> ph ) $= fvtoclegft_2 fvtoclegft_3 wcel fvtoclegft_0 fvtoclegft_1 wnf fvtoclegft_1 sup_set_class fvtoclegft_2 wceq fvtoclegft_0 wi fvtoclegft_1 wal w3a fvtoclegft_0 fvtoclegft_1 wex fvtoclegft_0 fvtoclegft_2 fvtoclegft_3 wcel fvtoclegft_1 sup_set_class fvtoclegft_2 wceq fvtoclegft_0 wi fvtoclegft_1 wal fvtoclegft_0 fvtoclegft_1 wex fvtoclegft_0 fvtoclegft_1 wnf fvtoclegft_2 fvtoclegft_3 wcel fvtoclegft_1 sup_set_class fvtoclegft_2 wceq fvtoclegft_1 wex fvtoclegft_1 sup_set_class fvtoclegft_2 wceq fvtoclegft_0 wi fvtoclegft_1 wal fvtoclegft_0 fvtoclegft_1 wex fvtoclegft_1 fvtoclegft_2 fvtoclegft_3 elisset fvtoclegft_1 sup_set_class fvtoclegft_2 wceq fvtoclegft_0 fvtoclegft_1 exim mpan9 3adant2 fvtoclegft_0 fvtoclegft_1 wnf fvtoclegft_2 fvtoclegft_3 wcel fvtoclegft_0 fvtoclegft_1 wex fvtoclegft_0 wb fvtoclegft_1 sup_set_class fvtoclegft_2 wceq fvtoclegft_0 wi fvtoclegft_1 wal fvtoclegft_0 fvtoclegft_1 19.9t 3ad2ant2 mpbid $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 18-Aug-1993.) $)
${
	$d x A $.
	fvtoclef_0 $f wff ph $.
	fvtoclef_1 $f set x $.
	fvtoclef_2 $f class A $.
	evtoclef_0 $e |- F/ x ph $.
	evtoclef_1 $e |- A e. _V $.
	evtoclef_2 $e |- ( x = A -> ph ) $.
	vtoclef $p |- ph $= fvtoclef_1 sup_set_class fvtoclef_2 wceq fvtoclef_1 wex fvtoclef_0 fvtoclef_1 fvtoclef_2 evtoclef_1 isseti fvtoclef_1 sup_set_class fvtoclef_2 wceq fvtoclef_0 fvtoclef_1 evtoclef_0 evtoclef_2 exlimi ax-mp $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 9-Sep-1993.) $)
${
	$d x A $.
	$d x ph $.
	fvtocle_0 $f wff ph $.
	fvtocle_1 $f set x $.
	fvtocle_2 $f class A $.
	evtocle_0 $e |- A e. _V $.
	evtocle_1 $e |- ( x = A -> ph ) $.
	vtocle $p |- ph $= fvtocle_2 cvv wcel fvtocle_0 evtocle_0 fvtocle_0 fvtocle_1 fvtocle_2 cvv evtocle_1 vtocleg ax-mp $.
$}
$( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 21-Nov-1994.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	fvtoclri_0 $f wff ph $.
	fvtoclri_1 $f wff ps $.
	fvtoclri_2 $f set x $.
	fvtoclri_3 $f class A $.
	fvtoclri_4 $f class B $.
	evtoclri_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	evtoclri_1 $e |- A. x e. B ph $.
	vtoclri $p |- ( A e. B -> ps ) $= fvtoclri_0 fvtoclri_1 fvtoclri_2 fvtoclri_3 fvtoclri_4 evtoclri_0 fvtoclri_0 fvtoclri_2 fvtoclri_4 evtoclri_1 rspec vtoclga $.
$}
$( A closed version of ~ spcimgf .  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)
${
	fspcimgft_0 $f wff ph $.
	fspcimgft_1 $f wff ps $.
	fspcimgft_2 $f set x $.
	fspcimgft_3 $f class A $.
	fspcimgft_4 $f class B $.
	espcimgft_0 $e |- F/ x ps $.
	espcimgft_1 $e |- F/_ x A $.
	spcimgft $p |- ( A. x ( x = A -> ( ph -> ps ) ) -> ( A e. B -> ( A. x ph -> ps ) ) ) $= fspcimgft_3 fspcimgft_4 wcel fspcimgft_3 cvv wcel fspcimgft_2 sup_set_class fspcimgft_3 wceq fspcimgft_0 fspcimgft_1 wi wi fspcimgft_2 wal fspcimgft_0 fspcimgft_2 wal fspcimgft_1 wi fspcimgft_3 fspcimgft_4 elex fspcimgft_2 sup_set_class fspcimgft_3 wceq fspcimgft_0 fspcimgft_1 wi wi fspcimgft_2 wal fspcimgft_3 cvv wcel fspcimgft_0 fspcimgft_1 wi fspcimgft_2 wex fspcimgft_0 fspcimgft_2 wal fspcimgft_1 wi fspcimgft_3 cvv wcel fspcimgft_2 sup_set_class fspcimgft_3 wceq fspcimgft_2 wex fspcimgft_2 sup_set_class fspcimgft_3 wceq fspcimgft_0 fspcimgft_1 wi wi fspcimgft_2 wal fspcimgft_0 fspcimgft_1 wi fspcimgft_2 wex fspcimgft_2 fspcimgft_3 espcimgft_1 issetf fspcimgft_2 sup_set_class fspcimgft_3 wceq fspcimgft_0 fspcimgft_1 wi fspcimgft_2 exim syl5bi fspcimgft_0 fspcimgft_1 fspcimgft_2 espcimgft_0 19.36 syl6ib syl5 $.
$}
$( A closed version of ~ spcgf .  (Contributed by Andrew Salmon,
       6-Jun-2011.)  (Revised by Mario Carneiro, 4-Jan-2017.) $)
${
	fspcgft_0 $f wff ph $.
	fspcgft_1 $f wff ps $.
	fspcgft_2 $f set x $.
	fspcgft_3 $f class A $.
	fspcgft_4 $f class B $.
	espcgft_0 $e |- F/ x ps $.
	espcgft_1 $e |- F/_ x A $.
	spcgft $p |- ( A. x ( x = A -> ( ph <-> ps ) ) -> ( A e. B -> ( A. x ph -> ps ) ) ) $= fspcgft_2 sup_set_class fspcgft_3 wceq fspcgft_0 fspcgft_1 wb wi fspcgft_2 wal fspcgft_2 sup_set_class fspcgft_3 wceq fspcgft_0 fspcgft_1 wi wi fspcgft_2 wal fspcgft_3 fspcgft_4 wcel fspcgft_0 fspcgft_2 wal fspcgft_1 wi wi fspcgft_2 sup_set_class fspcgft_3 wceq fspcgft_0 fspcgft_1 wb wi fspcgft_2 sup_set_class fspcgft_3 wceq fspcgft_0 fspcgft_1 wi wi fspcgft_2 fspcgft_0 fspcgft_1 wb fspcgft_0 fspcgft_1 wi fspcgft_2 sup_set_class fspcgft_3 wceq fspcgft_0 fspcgft_1 bi1 imim2i alimi fspcgft_0 fspcgft_1 fspcgft_2 fspcgft_3 fspcgft_4 espcgft_0 espcgft_1 spcimgft syl $.
$}
$( Rule of specialization, using implicit substitution.  Compare Theorem
         7.3 of [Quine] p. 44.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
${
	fspcimgf_0 $f wff ph $.
	fspcimgf_1 $f wff ps $.
	fspcimgf_2 $f set x $.
	fspcimgf_3 $f class A $.
	fspcimgf_4 $f class V $.
	espcimgf_0 $e |- F/_ x A $.
	espcimgf_1 $e |- F/ x ps $.
	espcimgf_2 $e |- ( x = A -> ( ph -> ps ) ) $.
	spcimgf $p |- ( A e. V -> ( A. x ph -> ps ) ) $= fspcimgf_2 sup_set_class fspcimgf_3 wceq fspcimgf_0 fspcimgf_1 wi wi fspcimgf_3 fspcimgf_4 wcel fspcimgf_0 fspcimgf_2 wal fspcimgf_1 wi wi fspcimgf_2 fspcimgf_0 fspcimgf_1 fspcimgf_2 fspcimgf_3 fspcimgf_4 espcimgf_1 espcimgf_0 spcimgft espcimgf_2 mpg $.
$}
$( Existential specialization, using implicit substitution.  (Contributed
       by Mario Carneiro, 4-Jan-2017.) $)
${
	fspcimegf_0 $f wff ph $.
	fspcimegf_1 $f wff ps $.
	fspcimegf_2 $f set x $.
	fspcimegf_3 $f class A $.
	fspcimegf_4 $f class V $.
	espcimegf_0 $e |- F/_ x A $.
	espcimegf_1 $e |- F/ x ps $.
	espcimegf_2 $e |- ( x = A -> ( ps -> ph ) ) $.
	spcimegf $p |- ( A e. V -> ( ps -> E. x ph ) ) $= fspcimegf_3 fspcimegf_4 wcel fspcimegf_1 fspcimegf_0 wn fspcimegf_2 wal wn fspcimegf_0 fspcimegf_2 wex fspcimegf_3 fspcimegf_4 wcel fspcimegf_0 wn fspcimegf_2 wal fspcimegf_1 fspcimegf_0 wn fspcimegf_1 wn fspcimegf_2 fspcimegf_3 fspcimegf_4 espcimegf_0 fspcimegf_1 fspcimegf_2 espcimegf_1 nfn fspcimegf_2 sup_set_class fspcimegf_3 wceq fspcimegf_1 fspcimegf_0 espcimegf_2 con3d spcimgf con2d fspcimegf_0 fspcimegf_2 df-ex syl6ibr $.
$}
$( Rule of specialization, using implicit substitution.  Compare Theorem
       7.3 of [Quine] p. 44.  (Contributed by NM, 2-Feb-1997.)  (Revised by
       Andrew Salmon, 12-Aug-2011.) $)
${
	fspcgf_0 $f wff ph $.
	fspcgf_1 $f wff ps $.
	fspcgf_2 $f set x $.
	fspcgf_3 $f class A $.
	fspcgf_4 $f class V $.
	espcgf_0 $e |- F/_ x A $.
	espcgf_1 $e |- F/ x ps $.
	espcgf_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	spcgf $p |- ( A e. V -> ( A. x ph -> ps ) ) $= fspcgf_2 sup_set_class fspcgf_3 wceq fspcgf_0 fspcgf_1 wb wi fspcgf_3 fspcgf_4 wcel fspcgf_0 fspcgf_2 wal fspcgf_1 wi wi fspcgf_2 fspcgf_0 fspcgf_1 fspcgf_2 fspcgf_3 fspcgf_4 espcgf_1 espcgf_0 spcgft espcgf_2 mpg $.
$}
$( Existential specialization, using implicit substitution.  (Contributed
       by NM, 2-Feb-1997.) $)
${
	fspcegf_0 $f wff ph $.
	fspcegf_1 $f wff ps $.
	fspcegf_2 $f set x $.
	fspcegf_3 $f class A $.
	fspcegf_4 $f class V $.
	espcegf_0 $e |- F/_ x A $.
	espcegf_1 $e |- F/ x ps $.
	espcegf_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	spcegf $p |- ( A e. V -> ( ps -> E. x ph ) ) $= fspcegf_3 fspcegf_4 wcel fspcegf_1 fspcegf_0 wn fspcegf_2 wal wn fspcegf_0 fspcegf_2 wex fspcegf_3 fspcegf_4 wcel fspcegf_0 wn fspcegf_2 wal fspcegf_1 fspcegf_0 wn fspcegf_1 wn fspcegf_2 fspcegf_3 fspcegf_4 espcegf_0 fspcegf_1 fspcegf_2 espcegf_1 nfn fspcegf_2 sup_set_class fspcegf_3 wceq fspcegf_0 fspcegf_1 espcegf_2 notbid spcgf con2d fspcegf_0 fspcegf_2 df-ex syl6ibr $.
$}
$( Restricted specialization, using implicit substitution.  (Contributed
         by Mario Carneiro, 4-Jan-2017.) $)
${
	$d x A $.
	$d x ph $.
	$d x ch $.
	fspcimdv_0 $f wff ph $.
	fspcimdv_1 $f wff ps $.
	fspcimdv_2 $f wff ch $.
	fspcimdv_3 $f set x $.
	fspcimdv_4 $f class A $.
	fspcimdv_5 $f class B $.
	espcimdv_0 $e |- ( ph -> A e. B ) $.
	espcimdv_1 $e |- ( ( ph /\ x = A ) -> ( ps -> ch ) ) $.
	spcimdv $p |- ( ph -> ( A. x ps -> ch ) ) $= fspcimdv_0 fspcimdv_3 sup_set_class fspcimdv_4 wceq fspcimdv_1 fspcimdv_2 wi wi fspcimdv_3 wal fspcimdv_4 fspcimdv_5 wcel fspcimdv_1 fspcimdv_3 wal fspcimdv_2 wi fspcimdv_0 fspcimdv_3 sup_set_class fspcimdv_4 wceq fspcimdv_1 fspcimdv_2 wi wi fspcimdv_3 fspcimdv_0 fspcimdv_3 sup_set_class fspcimdv_4 wceq fspcimdv_1 fspcimdv_2 wi espcimdv_1 ex alrimiv espcimdv_0 fspcimdv_1 fspcimdv_2 fspcimdv_3 fspcimdv_4 fspcimdv_5 fspcimdv_2 fspcimdv_3 nfv fspcimdv_3 fspcimdv_4 nfcv spcimgft sylc $.
$}
$( Rule of specialization, using implicit substitution.  Analogous to
         ~ rspcdv .  (Contributed by David Moews, 1-May-2017.) $)
${
	$d x A $.
	$d x ph $.
	$d x ch $.
	fspcdv_0 $f wff ph $.
	fspcdv_1 $f wff ps $.
	fspcdv_2 $f wff ch $.
	fspcdv_3 $f set x $.
	fspcdv_4 $f class A $.
	fspcdv_5 $f class B $.
	espcdv_0 $e |- ( ph -> A e. B ) $.
	espcdv_1 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	spcdv $p |- ( ph -> ( A. x ps -> ch ) ) $= fspcdv_0 fspcdv_1 fspcdv_2 fspcdv_3 fspcdv_4 fspcdv_5 espcdv_0 fspcdv_0 fspcdv_3 sup_set_class fspcdv_4 wceq wa fspcdv_1 fspcdv_2 espcdv_1 biimpd spcimdv $.
$}
$( Restricted existential specialization, using implicit substitution.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
${
	$d x A $.
	$d x ph $.
	$d x ch $.
	fspcimedv_0 $f wff ph $.
	fspcimedv_1 $f wff ps $.
	fspcimedv_2 $f wff ch $.
	fspcimedv_3 $f set x $.
	fspcimedv_4 $f class A $.
	fspcimedv_5 $f class B $.
	espcimedv_0 $e |- ( ph -> A e. B ) $.
	espcimedv_1 $e |- ( ( ph /\ x = A ) -> ( ch -> ps ) ) $.
	spcimedv $p |- ( ph -> ( ch -> E. x ps ) ) $= fspcimedv_0 fspcimedv_2 fspcimedv_1 wn fspcimedv_3 wal wn fspcimedv_1 fspcimedv_3 wex fspcimedv_0 fspcimedv_1 wn fspcimedv_3 wal fspcimedv_2 fspcimedv_0 fspcimedv_1 wn fspcimedv_2 wn fspcimedv_3 fspcimedv_4 fspcimedv_5 espcimedv_0 fspcimedv_0 fspcimedv_3 sup_set_class fspcimedv_4 wceq wa fspcimedv_2 fspcimedv_1 espcimedv_1 con3d spcimdv con2d fspcimedv_1 fspcimedv_3 df-ex syl6ibr $.
$}
$( Rule of specialization, using implicit substitution.  Compare Theorem
       7.3 of [Quine] p. 44.  (Contributed by NM, 22-Jun-1994.) $)
${
	$d x ps $.
	$d x A $.
	fspcgv_0 $f wff ph $.
	fspcgv_1 $f wff ps $.
	fspcgv_2 $f set x $.
	fspcgv_3 $f class A $.
	fspcgv_4 $f class V $.
	espcgv_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	spcgv $p |- ( A e. V -> ( A. x ph -> ps ) ) $= fspcgv_0 fspcgv_1 fspcgv_2 fspcgv_3 fspcgv_4 fspcgv_2 fspcgv_3 nfcv fspcgv_1 fspcgv_2 nfv espcgv_0 spcgf $.
$}
$( Existential specialization, using implicit substitution.  (Contributed
       by NM, 14-Aug-1994.) $)
${
	$d x ps $.
	$d x A $.
	fspcegv_0 $f wff ph $.
	fspcegv_1 $f wff ps $.
	fspcegv_2 $f set x $.
	fspcegv_3 $f class A $.
	fspcegv_4 $f class V $.
	espcegv_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	spcegv $p |- ( A e. V -> ( ps -> E. x ph ) ) $= fspcegv_0 fspcegv_1 fspcegv_2 fspcegv_3 fspcegv_4 fspcegv_2 fspcegv_3 nfcv fspcegv_1 fspcegv_2 nfv espcegv_0 spcegf $.
$}
$( Existential specialization with 2 quantifiers, using implicit
       substitution.  (Contributed by NM, 3-Aug-1995.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	fspc2egv_0 $f wff ph $.
	fspc2egv_1 $f wff ps $.
	fspc2egv_2 $f set x $.
	fspc2egv_3 $f set y $.
	fspc2egv_4 $f class A $.
	fspc2egv_5 $f class B $.
	fspc2egv_6 $f class V $.
	fspc2egv_7 $f class W $.
	espc2egv_0 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	spc2egv $p |- ( ( A e. V /\ B e. W ) -> ( ps -> E. x E. y ph ) ) $= fspc2egv_4 fspc2egv_6 wcel fspc2egv_5 fspc2egv_7 wcel wa fspc2egv_2 sup_set_class fspc2egv_4 wceq fspc2egv_3 sup_set_class fspc2egv_5 wceq wa fspc2egv_3 wex fspc2egv_2 wex fspc2egv_1 fspc2egv_0 fspc2egv_3 wex fspc2egv_2 wex fspc2egv_4 fspc2egv_6 wcel fspc2egv_5 fspc2egv_7 wcel wa fspc2egv_2 sup_set_class fspc2egv_4 wceq fspc2egv_2 wex fspc2egv_3 sup_set_class fspc2egv_5 wceq fspc2egv_3 wex wa fspc2egv_2 sup_set_class fspc2egv_4 wceq fspc2egv_3 sup_set_class fspc2egv_5 wceq wa fspc2egv_3 wex fspc2egv_2 wex fspc2egv_4 fspc2egv_6 wcel fspc2egv_2 sup_set_class fspc2egv_4 wceq fspc2egv_2 wex fspc2egv_5 fspc2egv_7 wcel fspc2egv_3 sup_set_class fspc2egv_5 wceq fspc2egv_3 wex fspc2egv_2 fspc2egv_4 fspc2egv_6 elisset fspc2egv_3 fspc2egv_5 fspc2egv_7 elisset anim12i fspc2egv_2 sup_set_class fspc2egv_4 wceq fspc2egv_3 sup_set_class fspc2egv_5 wceq fspc2egv_2 fspc2egv_3 eeanv sylibr fspc2egv_1 fspc2egv_2 sup_set_class fspc2egv_4 wceq fspc2egv_3 sup_set_class fspc2egv_5 wceq wa fspc2egv_0 fspc2egv_2 fspc2egv_3 fspc2egv_2 sup_set_class fspc2egv_4 wceq fspc2egv_3 sup_set_class fspc2egv_5 wceq wa fspc2egv_0 fspc2egv_1 espc2egv_0 biimprcd 2eximdv syl5com $.
$}
$( Specialization with 2 quantifiers, using implicit substitution.
       (Contributed by NM, 27-Apr-2004.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	fspc2gv_0 $f wff ph $.
	fspc2gv_1 $f wff ps $.
	fspc2gv_2 $f set x $.
	fspc2gv_3 $f set y $.
	fspc2gv_4 $f class A $.
	fspc2gv_5 $f class B $.
	fspc2gv_6 $f class V $.
	fspc2gv_7 $f class W $.
	espc2gv_0 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	spc2gv $p |- ( ( A e. V /\ B e. W ) -> ( A. x A. y ph -> ps ) ) $= fspc2gv_4 fspc2gv_6 wcel fspc2gv_5 fspc2gv_7 wcel wa fspc2gv_1 fspc2gv_0 fspc2gv_3 wal fspc2gv_2 wal fspc2gv_4 fspc2gv_6 wcel fspc2gv_5 fspc2gv_7 wcel wa fspc2gv_1 wn fspc2gv_0 wn fspc2gv_3 wex fspc2gv_2 wex fspc2gv_0 fspc2gv_3 wal fspc2gv_2 wal wn fspc2gv_0 wn fspc2gv_1 wn fspc2gv_2 fspc2gv_3 fspc2gv_4 fspc2gv_5 fspc2gv_6 fspc2gv_7 fspc2gv_2 sup_set_class fspc2gv_4 wceq fspc2gv_3 sup_set_class fspc2gv_5 wceq wa fspc2gv_0 fspc2gv_1 espc2gv_0 notbid spc2egv fspc2gv_0 fspc2gv_2 fspc2gv_3 2nalexn syl6ibr con4d $.
$}
$( Existential specialization with 3 quantifiers, using implicit
       substitution.  (Contributed by NM, 12-May-2008.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z ps $.
	fspc3egv_0 $f wff ph $.
	fspc3egv_1 $f wff ps $.
	fspc3egv_2 $f set x $.
	fspc3egv_3 $f set y $.
	fspc3egv_4 $f set z $.
	fspc3egv_5 $f class A $.
	fspc3egv_6 $f class B $.
	fspc3egv_7 $f class C $.
	fspc3egv_8 $f class V $.
	fspc3egv_9 $f class W $.
	fspc3egv_10 $f class X $.
	espc3egv_0 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	spc3egv $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ps -> E. x E. y E. z ph ) ) $= fspc3egv_5 fspc3egv_8 wcel fspc3egv_6 fspc3egv_9 wcel fspc3egv_7 fspc3egv_10 wcel w3a fspc3egv_2 sup_set_class fspc3egv_5 wceq fspc3egv_3 sup_set_class fspc3egv_6 wceq fspc3egv_4 sup_set_class fspc3egv_7 wceq w3a fspc3egv_4 wex fspc3egv_3 wex fspc3egv_2 wex fspc3egv_1 fspc3egv_0 fspc3egv_4 wex fspc3egv_3 wex fspc3egv_2 wex fspc3egv_5 fspc3egv_8 wcel fspc3egv_6 fspc3egv_9 wcel fspc3egv_7 fspc3egv_10 wcel w3a fspc3egv_2 sup_set_class fspc3egv_5 wceq fspc3egv_2 wex fspc3egv_3 sup_set_class fspc3egv_6 wceq fspc3egv_3 wex fspc3egv_4 sup_set_class fspc3egv_7 wceq fspc3egv_4 wex w3a fspc3egv_2 sup_set_class fspc3egv_5 wceq fspc3egv_3 sup_set_class fspc3egv_6 wceq fspc3egv_4 sup_set_class fspc3egv_7 wceq w3a fspc3egv_4 wex fspc3egv_3 wex fspc3egv_2 wex fspc3egv_5 fspc3egv_8 wcel fspc3egv_2 sup_set_class fspc3egv_5 wceq fspc3egv_2 wex fspc3egv_6 fspc3egv_9 wcel fspc3egv_3 sup_set_class fspc3egv_6 wceq fspc3egv_3 wex fspc3egv_7 fspc3egv_10 wcel fspc3egv_4 sup_set_class fspc3egv_7 wceq fspc3egv_4 wex fspc3egv_2 fspc3egv_5 fspc3egv_8 elisset fspc3egv_3 fspc3egv_6 fspc3egv_9 elisset fspc3egv_4 fspc3egv_7 fspc3egv_10 elisset 3anim123i fspc3egv_2 sup_set_class fspc3egv_5 wceq fspc3egv_3 sup_set_class fspc3egv_6 wceq fspc3egv_4 sup_set_class fspc3egv_7 wceq fspc3egv_2 fspc3egv_3 fspc3egv_4 eeeanv sylibr fspc3egv_1 fspc3egv_2 sup_set_class fspc3egv_5 wceq fspc3egv_3 sup_set_class fspc3egv_6 wceq fspc3egv_4 sup_set_class fspc3egv_7 wceq w3a fspc3egv_4 wex fspc3egv_0 fspc3egv_4 wex fspc3egv_2 fspc3egv_3 fspc3egv_1 fspc3egv_2 sup_set_class fspc3egv_5 wceq fspc3egv_3 sup_set_class fspc3egv_6 wceq fspc3egv_4 sup_set_class fspc3egv_7 wceq w3a fspc3egv_0 fspc3egv_4 fspc3egv_2 sup_set_class fspc3egv_5 wceq fspc3egv_3 sup_set_class fspc3egv_6 wceq fspc3egv_4 sup_set_class fspc3egv_7 wceq w3a fspc3egv_0 fspc3egv_1 espc3egv_0 biimprcd eximdv 2eximdv syl5com $.
$}
$( Specialization with 3 quantifiers, using implicit substitution.
       (Contributed by NM, 12-May-2008.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z ps $.
	fspc3gv_0 $f wff ph $.
	fspc3gv_1 $f wff ps $.
	fspc3gv_2 $f set x $.
	fspc3gv_3 $f set y $.
	fspc3gv_4 $f set z $.
	fspc3gv_5 $f class A $.
	fspc3gv_6 $f class B $.
	fspc3gv_7 $f class C $.
	fspc3gv_8 $f class V $.
	fspc3gv_9 $f class W $.
	fspc3gv_10 $f class X $.
	espc3gv_0 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
	spc3gv $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A. x A. y A. z ph -> ps ) ) $= fspc3gv_5 fspc3gv_8 wcel fspc3gv_6 fspc3gv_9 wcel fspc3gv_7 fspc3gv_10 wcel w3a fspc3gv_1 fspc3gv_0 fspc3gv_4 wal fspc3gv_3 wal fspc3gv_2 wal fspc3gv_5 fspc3gv_8 wcel fspc3gv_6 fspc3gv_9 wcel fspc3gv_7 fspc3gv_10 wcel w3a fspc3gv_1 wn fspc3gv_0 wn fspc3gv_4 wex fspc3gv_3 wex fspc3gv_2 wex fspc3gv_0 fspc3gv_4 wal fspc3gv_3 wal fspc3gv_2 wal wn fspc3gv_0 wn fspc3gv_1 wn fspc3gv_2 fspc3gv_3 fspc3gv_4 fspc3gv_5 fspc3gv_6 fspc3gv_7 fspc3gv_8 fspc3gv_9 fspc3gv_10 fspc3gv_2 sup_set_class fspc3gv_5 wceq fspc3gv_3 sup_set_class fspc3gv_6 wceq fspc3gv_4 sup_set_class fspc3gv_7 wceq w3a fspc3gv_0 fspc3gv_1 espc3gv_0 notbid spc3egv fspc3gv_0 wn fspc3gv_4 wex fspc3gv_3 wex fspc3gv_2 wex fspc3gv_0 fspc3gv_4 wal fspc3gv_3 wal wn fspc3gv_2 wex fspc3gv_0 fspc3gv_4 wal fspc3gv_3 wal fspc3gv_2 wal wn fspc3gv_0 wn fspc3gv_4 wex fspc3gv_3 wex fspc3gv_0 fspc3gv_4 wal fspc3gv_3 wal wn fspc3gv_2 fspc3gv_0 wn fspc3gv_4 wex fspc3gv_3 wex fspc3gv_0 fspc3gv_4 wal wn fspc3gv_3 wex fspc3gv_0 fspc3gv_4 wal fspc3gv_3 wal wn fspc3gv_0 wn fspc3gv_4 wex fspc3gv_0 fspc3gv_4 wal wn fspc3gv_3 fspc3gv_0 fspc3gv_4 exnal exbii fspc3gv_0 fspc3gv_4 wal fspc3gv_3 exnal bitri exbii fspc3gv_0 fspc3gv_4 wal fspc3gv_3 wal fspc3gv_2 exnal bitr2i syl6ibr con4d $.
$}
$( Rule of specialization, using implicit substitution.  (Contributed by
       NM, 22-Jun-1994.) $)
${
	$d x A $.
	$d x ps $.
	fspcv_0 $f wff ph $.
	fspcv_1 $f wff ps $.
	fspcv_2 $f set x $.
	fspcv_3 $f class A $.
	espcv_0 $e |- A e. _V $.
	espcv_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	spcv $p |- ( A. x ph -> ps ) $= fspcv_3 cvv wcel fspcv_0 fspcv_2 wal fspcv_1 wi espcv_0 fspcv_0 fspcv_1 fspcv_2 fspcv_3 cvv espcv_1 spcgv ax-mp $.
$}
$( Existential specialization, using implicit substitution.  (Contributed
       by NM, 31-Dec-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)
${
	$d x A $.
	$d x ps $.
	fspcev_0 $f wff ph $.
	fspcev_1 $f wff ps $.
	fspcev_2 $f set x $.
	fspcev_3 $f class A $.
	espcev_0 $e |- A e. _V $.
	espcev_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	spcev $p |- ( ps -> E. x ph ) $= fspcev_3 cvv wcel fspcev_1 fspcev_0 fspcev_2 wex wi espcev_0 fspcev_0 fspcev_1 fspcev_2 fspcev_3 cvv espcev_1 spcegv ax-mp $.
$}
$( Existential specialization, using implicit substitution.  (Contributed
       by NM, 3-Aug-1995.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	fspc2ev_0 $f wff ph $.
	fspc2ev_1 $f wff ps $.
	fspc2ev_2 $f set x $.
	fspc2ev_3 $f set y $.
	fspc2ev_4 $f class A $.
	fspc2ev_5 $f class B $.
	espc2ev_0 $e |- A e. _V $.
	espc2ev_1 $e |- B e. _V $.
	espc2ev_2 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	spc2ev $p |- ( ps -> E. x E. y ph ) $= fspc2ev_4 cvv wcel fspc2ev_5 cvv wcel fspc2ev_1 fspc2ev_0 fspc2ev_3 wex fspc2ev_2 wex wi espc2ev_0 espc2ev_1 fspc2ev_0 fspc2ev_1 fspc2ev_2 fspc2ev_3 fspc2ev_4 fspc2ev_5 cvv cvv espc2ev_2 spc2egv mp2an $.
$}
$( A closed version of ~ rspc .  (Contributed by Andrew Salmon,
       6-Jun-2011.) $)
${
	$d x A $.
	$d x B $.
	frspct_0 $f wff ph $.
	frspct_1 $f wff ps $.
	frspct_2 $f set x $.
	frspct_3 $f class A $.
	frspct_4 $f class B $.
	erspct_0 $e |- F/ x ps $.
	rspct $p |- ( A. x ( x = A -> ( ph <-> ps ) ) -> ( A e. B -> ( A. x e. B ph -> ps ) ) ) $= frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb wi frspct_2 wal frspct_3 frspct_4 wcel frspct_0 frspct_2 frspct_4 wral frspct_1 wi frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb wi frspct_2 wal frspct_3 frspct_4 wcel frspct_0 frspct_2 frspct_4 wral frspct_3 frspct_4 wcel frspct_1 frspct_0 frspct_2 frspct_4 wral frspct_2 sup_set_class frspct_4 wcel frspct_0 wi frspct_2 wal frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb wi frspct_2 wal frspct_3 frspct_4 wcel frspct_3 frspct_4 wcel frspct_1 wi frspct_0 frspct_2 frspct_4 df-ral frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb wi frspct_2 wal frspct_2 sup_set_class frspct_3 wceq frspct_2 sup_set_class frspct_4 wcel frspct_0 wi frspct_3 frspct_4 wcel frspct_1 wi wb wi frspct_2 wal frspct_3 frspct_4 wcel frspct_2 sup_set_class frspct_4 wcel frspct_0 wi frspct_2 wal frspct_3 frspct_4 wcel frspct_1 wi wi wi frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb wi frspct_2 sup_set_class frspct_3 wceq frspct_2 sup_set_class frspct_4 wcel frspct_0 wi frspct_3 frspct_4 wcel frspct_1 wi wb wi frspct_2 frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb frspct_2 sup_set_class frspct_4 wcel frspct_0 wi frspct_3 frspct_4 wcel frspct_1 wi wb frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb frspct_2 sup_set_class frspct_4 wcel frspct_0 wi frspct_3 frspct_4 wcel frspct_1 wi wb frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb wa frspct_2 sup_set_class frspct_4 wcel frspct_3 frspct_4 wcel frspct_0 frspct_1 frspct_2 sup_set_class frspct_3 wceq frspct_2 sup_set_class frspct_4 wcel frspct_3 frspct_4 wcel wb frspct_0 frspct_1 wb frspct_2 sup_set_class frspct_3 frspct_4 eleq1 adantr frspct_2 sup_set_class frspct_3 wceq frspct_0 frspct_1 wb simpr imbi12d ex a2i alimi frspct_2 sup_set_class frspct_4 wcel frspct_0 wi frspct_3 frspct_4 wcel frspct_1 wi frspct_2 frspct_3 frspct_4 frspct_3 frspct_4 wcel frspct_1 frspct_2 frspct_3 frspct_4 wcel frspct_2 nfv erspct_0 nfim frspct_2 frspct_3 nfcv spcgft syl syl7bi com34 pm2.43d $.
$}
$( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 19-Apr-2005.)  (Revised by Mario Carneiro, 11-Oct-2016.) $)
${
	$d x A $.
	$d x B $.
	frspc_0 $f wff ph $.
	frspc_1 $f wff ps $.
	frspc_2 $f set x $.
	frspc_3 $f class A $.
	frspc_4 $f class B $.
	erspc_0 $e |- F/ x ps $.
	erspc_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rspc $p |- ( A e. B -> ( A. x e. B ph -> ps ) ) $= frspc_0 frspc_2 frspc_4 wral frspc_2 sup_set_class frspc_4 wcel frspc_0 wi frspc_2 wal frspc_3 frspc_4 wcel frspc_1 frspc_0 frspc_2 frspc_4 df-ral frspc_2 sup_set_class frspc_4 wcel frspc_0 wi frspc_2 wal frspc_3 frspc_4 wcel frspc_1 frspc_2 sup_set_class frspc_4 wcel frspc_0 wi frspc_3 frspc_4 wcel frspc_1 wi frspc_2 frspc_3 frspc_4 frspc_2 frspc_3 nfcv frspc_3 frspc_4 wcel frspc_1 frspc_2 frspc_3 frspc_4 wcel frspc_2 nfv erspc_0 nfim frspc_2 sup_set_class frspc_3 wceq frspc_2 sup_set_class frspc_4 wcel frspc_3 frspc_4 wcel frspc_0 frspc_1 frspc_2 sup_set_class frspc_3 frspc_4 eleq1 erspc_1 imbi12d spcgf pm2.43a syl5bi $.
$}
$( Restricted existential specialization, using implicit substitution.
       (Contributed by NM, 26-May-1998.)  (Revised by Mario Carneiro,
       11-Oct-2016.) $)
${
	$d x A $.
	$d x B $.
	frspce_0 $f wff ph $.
	frspce_1 $f wff ps $.
	frspce_2 $f set x $.
	frspce_3 $f class A $.
	frspce_4 $f class B $.
	erspce_0 $e |- F/ x ps $.
	erspce_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rspce $p |- ( ( A e. B /\ ps ) -> E. x e. B ph ) $= frspce_3 frspce_4 wcel frspce_1 wa frspce_2 sup_set_class frspce_4 wcel frspce_0 wa frspce_2 wex frspce_0 frspce_2 frspce_4 wrex frspce_3 frspce_4 wcel frspce_1 frspce_2 sup_set_class frspce_4 wcel frspce_0 wa frspce_2 wex frspce_2 sup_set_class frspce_4 wcel frspce_0 wa frspce_3 frspce_4 wcel frspce_1 wa frspce_2 frspce_3 frspce_4 frspce_2 frspce_3 nfcv frspce_3 frspce_4 wcel frspce_1 frspce_2 frspce_3 frspce_4 wcel frspce_2 nfv erspce_0 nfan frspce_2 sup_set_class frspce_3 wceq frspce_2 sup_set_class frspce_4 wcel frspce_3 frspce_4 wcel frspce_0 frspce_1 frspce_2 sup_set_class frspce_3 frspce_4 eleq1 erspce_1 anbi12d spcegf anabsi5 frspce_0 frspce_2 frspce_4 df-rex sylibr $.
$}
$( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 26-May-1998.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	frspcv_0 $f wff ph $.
	frspcv_1 $f wff ps $.
	frspcv_2 $f set x $.
	frspcv_3 $f class A $.
	frspcv_4 $f class B $.
	erspcv_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rspcv $p |- ( A e. B -> ( A. x e. B ph -> ps ) ) $= frspcv_0 frspcv_1 frspcv_2 frspcv_3 frspcv_4 frspcv_1 frspcv_2 nfv erspcv_0 rspc $.
$}
$( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 2-Feb-2006.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	frspccv_0 $f wff ph $.
	frspccv_1 $f wff ps $.
	frspccv_2 $f set x $.
	frspccv_3 $f class A $.
	frspccv_4 $f class B $.
	erspccv_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rspccv $p |- ( A. x e. B ph -> ( A e. B -> ps ) ) $= frspccv_3 frspccv_4 wcel frspccv_0 frspccv_2 frspccv_4 wral frspccv_1 frspccv_0 frspccv_1 frspccv_2 frspccv_3 frspccv_4 erspccv_0 rspcv com12 $.
$}
$( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 13-Sep-2005.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	frspcva_0 $f wff ph $.
	frspcva_1 $f wff ps $.
	frspcva_2 $f set x $.
	frspcva_3 $f class A $.
	frspcva_4 $f class B $.
	erspcva_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rspcva $p |- ( ( A e. B /\ A. x e. B ph ) -> ps ) $= frspcva_3 frspcva_4 wcel frspcva_0 frspcva_2 frspcva_4 wral frspcva_1 frspcva_0 frspcva_1 frspcva_2 frspcva_3 frspcva_4 erspcva_0 rspcv imp $.
$}
$( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 26-Jul-2006.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	frspccva_0 $f wff ph $.
	frspccva_1 $f wff ps $.
	frspccva_2 $f set x $.
	frspccva_3 $f class A $.
	frspccva_4 $f class B $.
	erspccva_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rspccva $p |- ( ( A. x e. B ph /\ A e. B ) -> ps ) $= frspccva_3 frspccva_4 wcel frspccva_0 frspccva_2 frspccva_4 wral frspccva_1 frspccva_0 frspccva_1 frspccva_2 frspccva_3 frspccva_4 erspccva_0 rspcv impcom $.
$}
$( Restricted existential specialization, using implicit substitution.
       (Contributed by NM, 26-May-1998.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	frspcev_0 $f wff ph $.
	frspcev_1 $f wff ps $.
	frspcev_2 $f set x $.
	frspcev_3 $f class A $.
	frspcev_4 $f class B $.
	erspcev_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rspcev $p |- ( ( A e. B /\ ps ) -> E. x e. B ph ) $= frspcev_0 frspcev_1 frspcev_2 frspcev_3 frspcev_4 frspcev_1 frspcev_2 nfv erspcev_0 rspce $.
$}
$( Restricted specialization, using implicit substitution.  (Contributed
         by Mario Carneiro, 4-Jan-2017.) $)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	$d x ch $.
	frspcimdv_0 $f wff ph $.
	frspcimdv_1 $f wff ps $.
	frspcimdv_2 $f wff ch $.
	frspcimdv_3 $f set x $.
	frspcimdv_4 $f class A $.
	frspcimdv_5 $f class B $.
	erspcimdv_0 $e |- ( ph -> A e. B ) $.
	erspcimdv_1 $e |- ( ( ph /\ x = A ) -> ( ps -> ch ) ) $.
	rspcimdv $p |- ( ph -> ( A. x e. B ps -> ch ) ) $= frspcimdv_1 frspcimdv_3 frspcimdv_5 wral frspcimdv_3 sup_set_class frspcimdv_5 wcel frspcimdv_1 wi frspcimdv_3 wal frspcimdv_0 frspcimdv_2 frspcimdv_1 frspcimdv_3 frspcimdv_5 df-ral frspcimdv_0 frspcimdv_3 sup_set_class frspcimdv_5 wcel frspcimdv_1 wi frspcimdv_3 wal frspcimdv_4 frspcimdv_5 wcel frspcimdv_2 erspcimdv_0 frspcimdv_0 frspcimdv_3 sup_set_class frspcimdv_5 wcel frspcimdv_1 wi frspcimdv_4 frspcimdv_5 wcel frspcimdv_2 wi frspcimdv_3 frspcimdv_4 frspcimdv_5 erspcimdv_0 frspcimdv_0 frspcimdv_3 sup_set_class frspcimdv_4 wceq wa frspcimdv_4 frspcimdv_5 wcel frspcimdv_3 sup_set_class frspcimdv_5 wcel frspcimdv_1 frspcimdv_2 frspcimdv_0 frspcimdv_3 sup_set_class frspcimdv_4 wceq wa frspcimdv_3 sup_set_class frspcimdv_5 wcel frspcimdv_4 frspcimdv_5 wcel frspcimdv_0 frspcimdv_3 sup_set_class frspcimdv_4 wceq wa frspcimdv_3 sup_set_class frspcimdv_4 frspcimdv_5 frspcimdv_0 frspcimdv_3 sup_set_class frspcimdv_4 wceq simpr eleq1d biimprd erspcimdv_1 imim12d spcimdv mpid syl5bi $.
$}
$( Restricted existential specialization, using implicit substitution.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	$d x ch $.
	frspcimedv_0 $f wff ph $.
	frspcimedv_1 $f wff ps $.
	frspcimedv_2 $f wff ch $.
	frspcimedv_3 $f set x $.
	frspcimedv_4 $f class A $.
	frspcimedv_5 $f class B $.
	erspcimedv_0 $e |- ( ph -> A e. B ) $.
	erspcimedv_1 $e |- ( ( ph /\ x = A ) -> ( ch -> ps ) ) $.
	rspcimedv $p |- ( ph -> ( ch -> E. x e. B ps ) ) $= frspcimedv_0 frspcimedv_2 frspcimedv_1 wn frspcimedv_3 frspcimedv_5 wral wn frspcimedv_1 frspcimedv_3 frspcimedv_5 wrex frspcimedv_0 frspcimedv_1 wn frspcimedv_3 frspcimedv_5 wral frspcimedv_2 frspcimedv_0 frspcimedv_1 wn frspcimedv_2 wn frspcimedv_3 frspcimedv_4 frspcimedv_5 erspcimedv_0 frspcimedv_0 frspcimedv_3 sup_set_class frspcimedv_4 wceq wa frspcimedv_2 frspcimedv_1 erspcimedv_1 con3d rspcimdv con2d frspcimedv_1 frspcimedv_3 frspcimedv_5 dfrex2 syl6ibr $.
$}
$( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 17-Feb-2007.)  (Revised by Mario Carneiro, 4-Jan-2017.) $)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	$d x ch $.
	frspcdv_0 $f wff ph $.
	frspcdv_1 $f wff ps $.
	frspcdv_2 $f wff ch $.
	frspcdv_3 $f set x $.
	frspcdv_4 $f class A $.
	frspcdv_5 $f class B $.
	erspcdv_0 $e |- ( ph -> A e. B ) $.
	erspcdv_1 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	rspcdv $p |- ( ph -> ( A. x e. B ps -> ch ) ) $= frspcdv_0 frspcdv_1 frspcdv_2 frspcdv_3 frspcdv_4 frspcdv_5 erspcdv_0 frspcdv_0 frspcdv_3 sup_set_class frspcdv_4 wceq wa frspcdv_1 frspcdv_2 erspcdv_1 biimpd rspcimdv $.
$}
$( Restricted existential specialization, using implicit substitution.
       (Contributed by FL, 17-Apr-2007.)  (Revised by Mario Carneiro,
       4-Jan-2017.) $)
${
	$d x A $.
	$d x B $.
	$d x ph $.
	$d x ch $.
	frspcedv_0 $f wff ph $.
	frspcedv_1 $f wff ps $.
	frspcedv_2 $f wff ch $.
	frspcedv_3 $f set x $.
	frspcedv_4 $f class A $.
	frspcedv_5 $f class B $.
	erspcedv_0 $e |- ( ph -> A e. B ) $.
	erspcedv_1 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	rspcedv $p |- ( ph -> ( ch -> E. x e. B ps ) ) $= frspcedv_0 frspcedv_1 frspcedv_2 frspcedv_3 frspcedv_4 frspcedv_5 erspcedv_0 frspcedv_0 frspcedv_3 sup_set_class frspcedv_4 wceq wa frspcedv_1 frspcedv_2 erspcedv_1 biimprd rspcimedv $.
$}
$( 2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 9-Nov-2012.) $)
${
	$d x y A $.
	$d y B $.
	$d x C $.
	$d x y D $.
	frspc2_0 $f wff ph $.
	frspc2_1 $f wff ps $.
	frspc2_2 $f wff ch $.
	frspc2_3 $f set x $.
	frspc2_4 $f set y $.
	frspc2_5 $f class A $.
	frspc2_6 $f class B $.
	frspc2_7 $f class C $.
	frspc2_8 $f class D $.
	erspc2_0 $e |- F/ x ch $.
	erspc2_1 $e |- F/ y ps $.
	erspc2_2 $e |- ( x = A -> ( ph <-> ch ) ) $.
	erspc2_3 $e |- ( y = B -> ( ch <-> ps ) ) $.
	rspc2 $p |- ( ( A e. C /\ B e. D ) -> ( A. x e. C A. y e. D ph -> ps ) ) $= frspc2_5 frspc2_7 wcel frspc2_0 frspc2_4 frspc2_8 wral frspc2_3 frspc2_7 wral frspc2_2 frspc2_4 frspc2_8 wral frspc2_6 frspc2_8 wcel frspc2_1 frspc2_0 frspc2_4 frspc2_8 wral frspc2_2 frspc2_4 frspc2_8 wral frspc2_3 frspc2_5 frspc2_7 frspc2_2 frspc2_3 frspc2_4 frspc2_8 frspc2_3 frspc2_8 nfcv erspc2_0 nfral frspc2_3 sup_set_class frspc2_5 wceq frspc2_0 frspc2_2 frspc2_4 frspc2_8 erspc2_2 ralbidv rspc frspc2_2 frspc2_1 frspc2_4 frspc2_6 frspc2_8 erspc2_1 erspc2_3 rspc sylan9 $.
$}
$( 2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 13-Sep-1999.) $)
${
	$d x y A $.
	$d y B $.
	$d x C $.
	$d x y D $.
	$d x ch $.
	$d y ps $.
	frspc2v_0 $f wff ph $.
	frspc2v_1 $f wff ps $.
	frspc2v_2 $f wff ch $.
	frspc2v_3 $f set x $.
	frspc2v_4 $f set y $.
	frspc2v_5 $f class A $.
	frspc2v_6 $f class B $.
	frspc2v_7 $f class C $.
	frspc2v_8 $f class D $.
	erspc2v_0 $e |- ( x = A -> ( ph <-> ch ) ) $.
	erspc2v_1 $e |- ( y = B -> ( ch <-> ps ) ) $.
	rspc2v $p |- ( ( A e. C /\ B e. D ) -> ( A. x e. C A. y e. D ph -> ps ) ) $= frspc2v_0 frspc2v_1 frspc2v_2 frspc2v_3 frspc2v_4 frspc2v_5 frspc2v_6 frspc2v_7 frspc2v_8 frspc2v_2 frspc2v_3 nfv frspc2v_1 frspc2v_4 nfv erspc2v_0 erspc2v_1 rspc2 $.
$}
$( 2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 18-Jun-2014.) $)
${
	$d x y A $.
	$d y B $.
	$d x C $.
	$d x y D $.
	$d x ch $.
	$d y ps $.
	frspc2va_0 $f wff ph $.
	frspc2va_1 $f wff ps $.
	frspc2va_2 $f wff ch $.
	frspc2va_3 $f set x $.
	frspc2va_4 $f set y $.
	frspc2va_5 $f class A $.
	frspc2va_6 $f class B $.
	frspc2va_7 $f class C $.
	frspc2va_8 $f class D $.
	erspc2va_0 $e |- ( x = A -> ( ph <-> ch ) ) $.
	erspc2va_1 $e |- ( y = B -> ( ch <-> ps ) ) $.
	rspc2va $p |- ( ( ( A e. C /\ B e. D ) /\ A. x e. C A. y e. D ph ) -> ps ) $= frspc2va_5 frspc2va_7 wcel frspc2va_6 frspc2va_8 wcel wa frspc2va_0 frspc2va_4 frspc2va_8 wral frspc2va_3 frspc2va_7 wral frspc2va_1 frspc2va_0 frspc2va_1 frspc2va_2 frspc2va_3 frspc2va_4 frspc2va_5 frspc2va_6 frspc2va_7 frspc2va_8 erspc2va_0 erspc2va_1 rspc2v imp $.
$}
$( 2-variable restricted existential specialization, using implicit
       substitution.  (Contributed by NM, 16-Oct-1999.) $)
${
	$d x y A $.
	$d y B $.
	$d x C $.
	$d x y D $.
	$d x ch $.
	$d y ps $.
	frspc2ev_0 $f wff ph $.
	frspc2ev_1 $f wff ps $.
	frspc2ev_2 $f wff ch $.
	frspc2ev_3 $f set x $.
	frspc2ev_4 $f set y $.
	frspc2ev_5 $f class A $.
	frspc2ev_6 $f class B $.
	frspc2ev_7 $f class C $.
	frspc2ev_8 $f class D $.
	erspc2ev_0 $e |- ( x = A -> ( ph <-> ch ) ) $.
	erspc2ev_1 $e |- ( y = B -> ( ch <-> ps ) ) $.
	rspc2ev $p |- ( ( A e. C /\ B e. D /\ ps ) -> E. x e. C E. y e. D ph ) $= frspc2ev_5 frspc2ev_7 wcel frspc2ev_6 frspc2ev_8 wcel frspc2ev_1 w3a frspc2ev_5 frspc2ev_7 wcel frspc2ev_2 frspc2ev_4 frspc2ev_8 wrex wa frspc2ev_0 frspc2ev_4 frspc2ev_8 wrex frspc2ev_3 frspc2ev_7 wrex frspc2ev_5 frspc2ev_7 wcel frspc2ev_6 frspc2ev_8 wcel frspc2ev_1 frspc2ev_5 frspc2ev_7 wcel frspc2ev_2 frspc2ev_4 frspc2ev_8 wrex wa frspc2ev_6 frspc2ev_8 wcel frspc2ev_1 wa frspc2ev_2 frspc2ev_4 frspc2ev_8 wrex frspc2ev_5 frspc2ev_7 wcel frspc2ev_2 frspc2ev_1 frspc2ev_4 frspc2ev_6 frspc2ev_8 erspc2ev_1 rspcev anim2i 3impb frspc2ev_0 frspc2ev_4 frspc2ev_8 wrex frspc2ev_2 frspc2ev_4 frspc2ev_8 wrex frspc2ev_3 frspc2ev_5 frspc2ev_7 frspc2ev_3 sup_set_class frspc2ev_5 wceq frspc2ev_0 frspc2ev_2 frspc2ev_4 frspc2ev_8 erspc2ev_0 rexbidv rspcev syl $.
$}
$( 3-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 10-May-2005.) $)
${
	$d z ps $.
	$d x ch $.
	$d y th $.
	$d x y z A $.
	$d y z B $.
	$d z C $.
	$d x R $.
	$d x y S $.
	$d x y z T $.
	frspc3v_0 $f wff ph $.
	frspc3v_1 $f wff ps $.
	frspc3v_2 $f wff ch $.
	frspc3v_3 $f wff th $.
	frspc3v_4 $f set x $.
	frspc3v_5 $f set y $.
	frspc3v_6 $f set z $.
	frspc3v_7 $f class A $.
	frspc3v_8 $f class B $.
	frspc3v_9 $f class C $.
	frspc3v_10 $f class R $.
	frspc3v_11 $f class S $.
	frspc3v_12 $f class T $.
	erspc3v_0 $e |- ( x = A -> ( ph <-> ch ) ) $.
	erspc3v_1 $e |- ( y = B -> ( ch <-> th ) ) $.
	erspc3v_2 $e |- ( z = C -> ( th <-> ps ) ) $.
	rspc3v $p |- ( ( A e. R /\ B e. S /\ C e. T ) -> ( A. x e. R A. y e. S A. z e. T ph -> ps ) ) $= frspc3v_7 frspc3v_10 wcel frspc3v_8 frspc3v_11 wcel frspc3v_9 frspc3v_12 wcel frspc3v_0 frspc3v_6 frspc3v_12 wral frspc3v_5 frspc3v_11 wral frspc3v_4 frspc3v_10 wral frspc3v_1 wi frspc3v_7 frspc3v_10 wcel frspc3v_8 frspc3v_11 wcel wa frspc3v_0 frspc3v_6 frspc3v_12 wral frspc3v_5 frspc3v_11 wral frspc3v_4 frspc3v_10 wral frspc3v_3 frspc3v_6 frspc3v_12 wral frspc3v_9 frspc3v_12 wcel frspc3v_1 frspc3v_0 frspc3v_6 frspc3v_12 wral frspc3v_3 frspc3v_6 frspc3v_12 wral frspc3v_2 frspc3v_6 frspc3v_12 wral frspc3v_4 frspc3v_5 frspc3v_7 frspc3v_8 frspc3v_10 frspc3v_11 frspc3v_4 sup_set_class frspc3v_7 wceq frspc3v_0 frspc3v_2 frspc3v_6 frspc3v_12 erspc3v_0 ralbidv frspc3v_5 sup_set_class frspc3v_8 wceq frspc3v_2 frspc3v_3 frspc3v_6 frspc3v_12 erspc3v_1 ralbidv rspc2v frspc3v_3 frspc3v_1 frspc3v_6 frspc3v_9 frspc3v_12 erspc3v_2 rspcv sylan9 3impa $.
$}
$( 3-variable restricted existentional specialization, using implicit
       substitution.  (Contributed by NM, 25-Jul-2012.) $)
${
	$d z ps $.
	$d x ch $.
	$d y th $.
	$d x y z A $.
	$d y z B $.
	$d z C $.
	$d x R $.
	$d x y S $.
	$d x y z T $.
	frspc3ev_0 $f wff ph $.
	frspc3ev_1 $f wff ps $.
	frspc3ev_2 $f wff ch $.
	frspc3ev_3 $f wff th $.
	frspc3ev_4 $f set x $.
	frspc3ev_5 $f set y $.
	frspc3ev_6 $f set z $.
	frspc3ev_7 $f class A $.
	frspc3ev_8 $f class B $.
	frspc3ev_9 $f class C $.
	frspc3ev_10 $f class R $.
	frspc3ev_11 $f class S $.
	frspc3ev_12 $f class T $.
	erspc3ev_0 $e |- ( x = A -> ( ph <-> ch ) ) $.
	erspc3ev_1 $e |- ( y = B -> ( ch <-> th ) ) $.
	erspc3ev_2 $e |- ( z = C -> ( th <-> ps ) ) $.
	rspc3ev $p |- ( ( ( A e. R /\ B e. S /\ C e. T ) /\ ps ) -> E. x e. R E. y e. S E. z e. T ph ) $= frspc3ev_7 frspc3ev_10 wcel frspc3ev_8 frspc3ev_11 wcel frspc3ev_9 frspc3ev_12 wcel w3a frspc3ev_1 wa frspc3ev_7 frspc3ev_10 wcel frspc3ev_8 frspc3ev_11 wcel frspc3ev_3 frspc3ev_6 frspc3ev_12 wrex frspc3ev_0 frspc3ev_6 frspc3ev_12 wrex frspc3ev_5 frspc3ev_11 wrex frspc3ev_4 frspc3ev_10 wrex frspc3ev_7 frspc3ev_10 wcel frspc3ev_8 frspc3ev_11 wcel frspc3ev_9 frspc3ev_12 wcel frspc3ev_1 simpl1 frspc3ev_7 frspc3ev_10 wcel frspc3ev_8 frspc3ev_11 wcel frspc3ev_9 frspc3ev_12 wcel frspc3ev_1 simpl2 frspc3ev_9 frspc3ev_12 wcel frspc3ev_7 frspc3ev_10 wcel frspc3ev_1 frspc3ev_3 frspc3ev_6 frspc3ev_12 wrex frspc3ev_8 frspc3ev_11 wcel frspc3ev_3 frspc3ev_1 frspc3ev_6 frspc3ev_9 frspc3ev_12 erspc3ev_2 rspcev 3ad2antl3 frspc3ev_0 frspc3ev_6 frspc3ev_12 wrex frspc3ev_3 frspc3ev_6 frspc3ev_12 wrex frspc3ev_2 frspc3ev_6 frspc3ev_12 wrex frspc3ev_4 frspc3ev_5 frspc3ev_7 frspc3ev_8 frspc3ev_10 frspc3ev_11 frspc3ev_4 sup_set_class frspc3ev_7 wceq frspc3ev_0 frspc3ev_2 frspc3ev_6 frspc3ev_12 erspc3ev_0 rexbidv frspc3ev_5 sup_set_class frspc3ev_8 wceq frspc3ev_2 frspc3ev_3 frspc3ev_6 frspc3ev_12 erspc3ev_1 rexbidv rspc2ev syl3anc $.
$}
$( A variable introduction law for class equality.  (Contributed by NM,
       14-Apr-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
${
	$d x A $.
	$d x B $.
	feqvinc_0 $f set x $.
	feqvinc_1 $f class A $.
	feqvinc_2 $f class B $.
	eeqvinc_0 $e |- A e. _V $.
	eqvinc $p |- ( A = B <-> E. x ( x = A /\ x = B ) ) $= feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wa feqvinc_0 wex feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wa feqvinc_0 feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_0 wex feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq wi feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wi wa feqvinc_0 wex feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wa wi feqvinc_0 wex feqvinc_0 feqvinc_1 eeqvinc_0 isseti feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq wi feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wi wa feqvinc_0 feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq wi feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wi feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_1 feqvinc_2 wceq ax-1 feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 feqvinc_2 eqtr ex jca eximi feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq wi feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wi wa feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wa wi feqvinc_0 feqvinc_1 feqvinc_2 wceq feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_0 sup_set_class feqvinc_2 wceq pm3.43 eximi mp2b 19.37aiv feqvinc_0 sup_set_class feqvinc_1 wceq feqvinc_0 sup_set_class feqvinc_2 wceq wa feqvinc_1 feqvinc_2 wceq feqvinc_0 feqvinc_0 sup_set_class feqvinc_1 feqvinc_2 eqtr2 exlimiv impbii $.
$}
$( A variable introduction law for class equality, using bound-variable
       hypotheses instead of distinct variable conditions.  (Contributed by NM,
       14-Sep-2003.) $)
${
	$d A y $.
	$d B y $.
	$d x y $.
	ieqvincf_0 $f set y $.
	feqvincf_0 $f set x $.
	feqvincf_1 $f class A $.
	feqvincf_2 $f class B $.
	eeqvincf_0 $e |- F/_ x A $.
	eeqvincf_1 $e |- F/_ x B $.
	eeqvincf_2 $e |- A e. _V $.
	eqvincf $p |- ( A = B <-> E. x ( x = A /\ x = B ) ) $= feqvincf_1 feqvincf_2 wceq ieqvincf_0 sup_set_class feqvincf_1 wceq ieqvincf_0 sup_set_class feqvincf_2 wceq wa ieqvincf_0 wex feqvincf_0 sup_set_class feqvincf_1 wceq feqvincf_0 sup_set_class feqvincf_2 wceq wa feqvincf_0 wex ieqvincf_0 feqvincf_1 feqvincf_2 eeqvincf_2 eqvinc ieqvincf_0 sup_set_class feqvincf_1 wceq ieqvincf_0 sup_set_class feqvincf_2 wceq wa feqvincf_0 sup_set_class feqvincf_1 wceq feqvincf_0 sup_set_class feqvincf_2 wceq wa ieqvincf_0 feqvincf_0 ieqvincf_0 sup_set_class feqvincf_1 wceq ieqvincf_0 sup_set_class feqvincf_2 wceq feqvincf_0 feqvincf_0 ieqvincf_0 sup_set_class feqvincf_1 eeqvincf_0 nfeq2 feqvincf_0 ieqvincf_0 sup_set_class feqvincf_2 eeqvincf_1 nfeq2 nfan feqvincf_0 sup_set_class feqvincf_1 wceq feqvincf_0 sup_set_class feqvincf_2 wceq wa ieqvincf_0 nfv ieqvincf_0 sup_set_class feqvincf_0 sup_set_class wceq ieqvincf_0 sup_set_class feqvincf_1 wceq feqvincf_0 sup_set_class feqvincf_1 wceq ieqvincf_0 sup_set_class feqvincf_2 wceq feqvincf_0 sup_set_class feqvincf_2 wceq ieqvincf_0 sup_set_class feqvincf_0 sup_set_class feqvincf_1 eqeq1 ieqvincf_0 sup_set_class feqvincf_0 sup_set_class feqvincf_2 eqeq1 anbi12d cbvex bitri $.
$}
$( Two ways to express substitution of ` A ` for ` x ` in ` ph ` .
       (Contributed by NM, 2-Mar-1995.) $)
${
	$d x A y $.
	$d ph y $.
	ialexeq_0 $f set y $.
	falexeq_0 $f wff ph $.
	falexeq_1 $f set x $.
	falexeq_2 $f class A $.
	ealexeq_0 $e |- A e. _V $.
	alexeq $p |- ( A. x ( x = A -> ph ) <-> E. x ( x = A /\ ph ) ) $= falexeq_1 sup_set_class falexeq_2 wceq falexeq_0 wa falexeq_1 wex falexeq_1 sup_set_class falexeq_2 wceq falexeq_0 wi falexeq_1 wal falexeq_1 sup_set_class ialexeq_0 sup_set_class wceq falexeq_0 wa falexeq_1 wex falexeq_1 sup_set_class ialexeq_0 sup_set_class wceq falexeq_0 wi falexeq_1 wal falexeq_1 sup_set_class falexeq_2 wceq falexeq_0 wa falexeq_1 wex falexeq_1 sup_set_class falexeq_2 wceq falexeq_0 wi falexeq_1 wal ialexeq_0 falexeq_2 ealexeq_0 ialexeq_0 sup_set_class falexeq_2 wceq falexeq_1 sup_set_class ialexeq_0 sup_set_class wceq falexeq_0 wa falexeq_1 sup_set_class falexeq_2 wceq falexeq_0 wa falexeq_1 ialexeq_0 sup_set_class falexeq_2 wceq falexeq_1 sup_set_class ialexeq_0 sup_set_class wceq falexeq_1 sup_set_class falexeq_2 wceq falexeq_0 ialexeq_0 sup_set_class falexeq_2 falexeq_1 sup_set_class eqeq2 anbi1d exbidv ialexeq_0 sup_set_class falexeq_2 wceq falexeq_1 sup_set_class ialexeq_0 sup_set_class wceq falexeq_0 wi falexeq_1 sup_set_class falexeq_2 wceq falexeq_0 wi falexeq_1 ialexeq_0 sup_set_class falexeq_2 wceq falexeq_1 sup_set_class ialexeq_0 sup_set_class wceq falexeq_1 sup_set_class falexeq_2 wceq falexeq_0 ialexeq_0 sup_set_class falexeq_2 falexeq_1 sup_set_class eqeq2 imbi1d albidv falexeq_0 falexeq_1 ialexeq_0 sb56 vtoclb bicomi $.
$}
$( Equality implies equivalence with substitution.  (Contributed by NM,
       2-Mar-1995.) $)
${
	$d x A y $.
	$d ph y $.
	iceqex_0 $f set y $.
	fceqex_0 $f wff ph $.
	fceqex_1 $f set x $.
	fceqex_2 $f class A $.
	ceqex $p |- ( x = A -> ( ph <-> E. x ( x = A /\ ph ) ) ) $= fceqex_2 cvv wcel fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 wa fceqex_1 wex wb fceqex_1 sup_set_class fceqex_2 wceq fceqex_1 sup_set_class fceqex_2 wceq fceqex_1 wex fceqex_2 cvv wcel fceqex_1 sup_set_class fceqex_2 wceq fceqex_1 19.8a fceqex_1 fceqex_2 isset sylibr fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wa fceqex_1 wex wb wi fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 wa fceqex_1 wex wb wi iceqex_0 fceqex_2 cvv iceqex_0 sup_set_class fceqex_2 wceq fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wa fceqex_1 wex wb fceqex_0 fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 wa fceqex_1 wex wb iceqex_0 sup_set_class fceqex_2 fceqex_1 sup_set_class eqeq2 iceqex_0 sup_set_class fceqex_2 wceq fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wa fceqex_1 wex fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 wa fceqex_1 wex fceqex_0 iceqex_0 sup_set_class fceqex_2 wceq fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wa fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 wa fceqex_1 iceqex_0 sup_set_class fceqex_2 wceq fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_1 sup_set_class fceqex_2 wceq fceqex_0 iceqex_0 sup_set_class fceqex_2 fceqex_1 sup_set_class eqeq2 anbi1d exbidv bibi2d imbi12d fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wa fceqex_1 wex fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wa fceqex_1 wex fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wa fceqex_1 19.8a ex fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wa fceqex_1 wex fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wi fceqex_1 wal fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 fceqex_0 fceqex_1 iceqex_0 sup_set_class iceqex_0 vex alexeq fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wi fceqex_1 wal fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 fceqex_1 sup_set_class iceqex_0 sup_set_class wceq fceqex_0 wi fceqex_1 sp com12 syl5bir impbid vtoclg mpcom $.
$}
$( A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       11-Oct-2004.) $)
${
	$d x A $.
	fceqsexg_0 $f wff ph $.
	fceqsexg_1 $f wff ps $.
	fceqsexg_2 $f set x $.
	fceqsexg_3 $f class A $.
	fceqsexg_4 $f class V $.
	eceqsexg_0 $e |- F/ x ps $.
	eceqsexg_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsexg $p |- ( A e. V -> ( E. x ( x = A /\ ph ) <-> ps ) ) $= fceqsexg_0 fceqsexg_0 wb fceqsexg_2 sup_set_class fceqsexg_3 wceq fceqsexg_0 wa fceqsexg_2 wex fceqsexg_1 wb fceqsexg_2 fceqsexg_3 fceqsexg_4 fceqsexg_2 fceqsexg_3 nfcv fceqsexg_2 sup_set_class fceqsexg_3 wceq fceqsexg_0 wa fceqsexg_2 wex fceqsexg_1 fceqsexg_2 fceqsexg_2 sup_set_class fceqsexg_3 wceq fceqsexg_0 wa fceqsexg_2 nfe1 eceqsexg_0 nfbi fceqsexg_2 sup_set_class fceqsexg_3 wceq fceqsexg_0 fceqsexg_2 sup_set_class fceqsexg_3 wceq fceqsexg_0 wa fceqsexg_2 wex fceqsexg_0 fceqsexg_1 fceqsexg_0 fceqsexg_2 fceqsexg_3 ceqex eceqsexg_1 bibi12d fceqsexg_0 biid vtoclgf $.
$}
$( Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 29-Dec-1996.) $)
${
	$d x A $.
	$d x ps $.
	fceqsexgv_0 $f wff ph $.
	fceqsexgv_1 $f wff ps $.
	fceqsexgv_2 $f set x $.
	fceqsexgv_3 $f class A $.
	fceqsexgv_4 $f class V $.
	eceqsexgv_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsexgv $p |- ( A e. V -> ( E. x ( x = A /\ ph ) <-> ps ) ) $= fceqsexgv_0 fceqsexgv_1 fceqsexgv_2 fceqsexgv_3 fceqsexgv_4 fceqsexgv_1 fceqsexgv_2 nfv eceqsexgv_0 ceqsexg $.
$}
$( Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by NM, 30-Apr-2004.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	fceqsrexv_0 $f wff ph $.
	fceqsrexv_1 $f wff ps $.
	fceqsrexv_2 $f set x $.
	fceqsrexv_3 $f class A $.
	fceqsrexv_4 $f class B $.
	eceqsrexv_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsrexv $p |- ( A e. B -> ( E. x e. B ( x = A /\ ph ) <-> ps ) ) $= fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_0 wa fceqsrexv_2 fceqsrexv_4 wrex fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_0 wa wa fceqsrexv_2 wex fceqsrexv_3 fceqsrexv_4 wcel fceqsrexv_1 fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_0 wa fceqsrexv_2 fceqsrexv_4 wrex fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_0 wa wa fceqsrexv_2 wex fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_0 wa wa fceqsrexv_2 wex fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_0 wa fceqsrexv_2 fceqsrexv_4 df-rex fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_0 wa wa fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_0 wa wa fceqsrexv_2 fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_0 an12 exbii bitr4i fceqsrexv_3 fceqsrexv_4 wcel fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_0 wa wa fceqsrexv_2 wex fceqsrexv_1 fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_0 wa fceqsrexv_3 fceqsrexv_4 wcel fceqsrexv_1 wa fceqsrexv_2 fceqsrexv_3 fceqsrexv_4 fceqsrexv_2 sup_set_class fceqsrexv_3 wceq fceqsrexv_2 sup_set_class fceqsrexv_4 wcel fceqsrexv_3 fceqsrexv_4 wcel fceqsrexv_0 fceqsrexv_1 fceqsrexv_2 sup_set_class fceqsrexv_3 fceqsrexv_4 eleq1 eceqsrexv_0 anbi12d ceqsexgv bianabs syl5bb $.
$}
$( Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by Mario Carneiro, 14-Mar-2014.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	fceqsrexbv_0 $f wff ph $.
	fceqsrexbv_1 $f wff ps $.
	fceqsrexbv_2 $f set x $.
	fceqsrexbv_3 $f class A $.
	fceqsrexbv_4 $f class B $.
	eceqsrexbv_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ceqsrexbv $p |- ( E. x e. B ( x = A /\ ph ) <-> ( A e. B /\ ps ) ) $= fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa wa fceqsrexbv_2 fceqsrexbv_4 wrex fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa fceqsrexbv_2 fceqsrexbv_4 wrex wa fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa fceqsrexbv_2 fceqsrexbv_4 wrex fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_1 wa fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa fceqsrexbv_2 fceqsrexbv_4 r19.42v fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa wa fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa fceqsrexbv_2 fceqsrexbv_4 fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa wa fceqsrexbv_2 sup_set_class fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa fceqsrexbv_2 sup_set_class fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa wa fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa wa fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa fceqsrexbv_2 sup_set_class fceqsrexbv_4 wcel fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_2 sup_set_class fceqsrexbv_4 wcel fceqsrexbv_3 fceqsrexbv_4 wcel wb fceqsrexbv_0 fceqsrexbv_2 sup_set_class fceqsrexbv_3 fceqsrexbv_4 eleq1 adantr pm5.32ri bicomi baib rexbiia fceqsrexbv_3 fceqsrexbv_4 wcel fceqsrexbv_2 sup_set_class fceqsrexbv_3 wceq fceqsrexbv_0 wa fceqsrexbv_2 fceqsrexbv_4 wrex fceqsrexbv_1 fceqsrexbv_0 fceqsrexbv_1 fceqsrexbv_2 fceqsrexbv_3 fceqsrexbv_4 eceqsrexbv_0 ceqsrexv pm5.32i 3bitr3i $.
$}
$( Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by NM, 29-Oct-2005.) $)
${
	$d x y A $.
	$d x y B $.
	$d x C $.
	$d x y D $.
	$d x ps $.
	$d y ch $.
	fceqsrex2v_0 $f wff ph $.
	fceqsrex2v_1 $f wff ps $.
	fceqsrex2v_2 $f wff ch $.
	fceqsrex2v_3 $f set x $.
	fceqsrex2v_4 $f set y $.
	fceqsrex2v_5 $f class A $.
	fceqsrex2v_6 $f class B $.
	fceqsrex2v_7 $f class C $.
	fceqsrex2v_8 $f class D $.
	eceqsrex2v_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eceqsrex2v_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	ceqsrex2v $p |- ( ( A e. C /\ B e. D ) -> ( E. x e. C E. y e. D ( ( x = A /\ y = B ) /\ ph ) <-> ch ) ) $= fceqsrex2v_5 fceqsrex2v_7 wcel fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq wa fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_3 fceqsrex2v_7 wrex fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_1 wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_6 fceqsrex2v_8 wcel fceqsrex2v_2 fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq wa fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_3 fceqsrex2v_7 wrex fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 wrex wa fceqsrex2v_3 fceqsrex2v_7 wrex fceqsrex2v_5 fceqsrex2v_7 wcel fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_1 wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq wa fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 wrex wa fceqsrex2v_3 fceqsrex2v_7 fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq wa fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 wa wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 wrex wa fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq wa fceqsrex2v_0 wa fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 wa wa fceqsrex2v_4 fceqsrex2v_8 fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 anass rexbii fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 r19.42v bitri rexbii fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_1 wa fceqsrex2v_4 fceqsrex2v_8 wrex fceqsrex2v_3 fceqsrex2v_5 fceqsrex2v_7 fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_0 wa fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq fceqsrex2v_1 wa fceqsrex2v_4 fceqsrex2v_8 fceqsrex2v_3 sup_set_class fceqsrex2v_5 wceq fceqsrex2v_0 fceqsrex2v_1 fceqsrex2v_4 sup_set_class fceqsrex2v_6 wceq eceqsrex2v_0 anbi2d rexbidv ceqsrexv syl5bb fceqsrex2v_1 fceqsrex2v_2 fceqsrex2v_4 fceqsrex2v_6 fceqsrex2v_8 eceqsrex2v_1 ceqsrexv sylan9bb $.
$}
$( An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)
${
	$d x A $.
	$d x B $.
	fclel2_0 $f set x $.
	fclel2_1 $f class A $.
	fclel2_2 $f class B $.
	eclel2_0 $e |- A e. _V $.
	clel2 $p |- ( A e. B <-> A. x ( x = A -> x e. B ) ) $= fclel2_0 sup_set_class fclel2_1 wceq fclel2_0 sup_set_class fclel2_2 wcel wi fclel2_0 wal fclel2_1 fclel2_2 wcel fclel2_0 sup_set_class fclel2_2 wcel fclel2_1 fclel2_2 wcel fclel2_0 fclel2_1 eclel2_0 fclel2_0 sup_set_class fclel2_1 fclel2_2 eleq1 ceqsalv bicomi $.
$}
$( An alternate definition of class membership when the class is a set.
       (Contributed by NM, 13-Aug-2005.) $)
${
	$d x A $.
	$d x B $.
	fclel3g_0 $f set x $.
	fclel3g_1 $f class A $.
	fclel3g_2 $f class B $.
	fclel3g_3 $f class V $.
	clel3g $p |- ( B e. V -> ( A e. B <-> E. x ( x = B /\ A e. x ) ) ) $= fclel3g_2 fclel3g_3 wcel fclel3g_0 sup_set_class fclel3g_2 wceq fclel3g_1 fclel3g_0 sup_set_class wcel wa fclel3g_0 wex fclel3g_1 fclel3g_2 wcel fclel3g_1 fclel3g_0 sup_set_class wcel fclel3g_1 fclel3g_2 wcel fclel3g_0 fclel3g_2 fclel3g_3 fclel3g_0 sup_set_class fclel3g_2 fclel3g_1 eleq2 ceqsexgv bicomd $.
$}
$( An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)
${
	$d x A $.
	$d x B $.
	fclel3_0 $f set x $.
	fclel3_1 $f class A $.
	fclel3_2 $f class B $.
	eclel3_0 $e |- B e. _V $.
	clel3 $p |- ( A e. B <-> E. x ( x = B /\ A e. x ) ) $= fclel3_2 cvv wcel fclel3_1 fclel3_2 wcel fclel3_0 sup_set_class fclel3_2 wceq fclel3_1 fclel3_0 sup_set_class wcel wa fclel3_0 wex wb eclel3_0 fclel3_0 fclel3_1 fclel3_2 cvv clel3g ax-mp $.
$}
$( An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)
${
	$d x A $.
	$d x B $.
	fclel4_0 $f set x $.
	fclel4_1 $f class A $.
	fclel4_2 $f class B $.
	eclel4_0 $e |- B e. _V $.
	clel4 $p |- ( A e. B <-> A. x ( x = B -> A e. x ) ) $= fclel4_0 sup_set_class fclel4_2 wceq fclel4_1 fclel4_0 sup_set_class wcel wi fclel4_0 wal fclel4_1 fclel4_2 wcel fclel4_1 fclel4_0 sup_set_class wcel fclel4_1 fclel4_2 wcel fclel4_0 fclel4_2 eclel4_0 fclel4_0 sup_set_class fclel4_2 fclel4_1 eleq2 ceqsalv bicomi $.
$}
$( Compare theorem *13.183 in [WhiteheadRussell] p. 178.  Only ` A ` is
       required to be a set.  (Contributed by Andrew Salmon, 3-Jun-2011.) $)
${
	$d y A z $.
	$d y B z $.
	ipm13.183_0 $f set y $.
	fpm13.183_0 $f set z $.
	fpm13.183_1 $f class A $.
	fpm13.183_2 $f class B $.
	fpm13.183_3 $f class V $.
	pm13.183 $p |- ( A e. V -> ( A = B <-> A. z ( z = A <-> z = B ) ) ) $= ipm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 wal fpm13.183_1 fpm13.183_2 wceq fpm13.183_0 sup_set_class fpm13.183_1 wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 wal ipm13.183_0 fpm13.183_1 fpm13.183_3 ipm13.183_0 sup_set_class fpm13.183_1 fpm13.183_2 eqeq1 ipm13.183_0 sup_set_class fpm13.183_1 wceq fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 sup_set_class fpm13.183_1 wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 ipm13.183_0 sup_set_class fpm13.183_1 wceq fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_1 wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq ipm13.183_0 sup_set_class fpm13.183_1 fpm13.183_0 sup_set_class eqeq2 bibi1d albidv ipm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 wal ipm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 ipm13.183_0 sup_set_class fpm13.183_2 fpm13.183_0 sup_set_class eqeq2 alrimiv fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 wal fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 ipm13.183_0 wsb ipm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 ipm13.183_0 stdpc4 fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 ipm13.183_0 wsb fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 ipm13.183_0 wsb fpm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 ipm13.183_0 wsb wb ipm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 ipm13.183_0 sbbi fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 ipm13.183_0 wsb fpm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 ipm13.183_0 wsb wb fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 ipm13.183_0 wsb ipm13.183_0 sup_set_class fpm13.183_2 wceq wb ipm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 ipm13.183_0 wsb ipm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 ipm13.183_0 wsb ipm13.183_0 fpm13.183_0 fpm13.183_2 eqsb3 bibi2i fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 ipm13.183_0 wsb ipm13.183_0 sup_set_class fpm13.183_2 wceq wb fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 ipm13.183_0 wsb ipm13.183_0 sup_set_class fpm13.183_2 wceq fpm13.183_0 ipm13.183_0 equsb1 fpm13.183_0 sup_set_class ipm13.183_0 sup_set_class wceq fpm13.183_0 ipm13.183_0 wsb ipm13.183_0 sup_set_class fpm13.183_2 wceq bi1 mpi sylbi sylbi syl impbii vtoclbg $.
$}
$( Restricted quantifier version of Theorem 19.3 of [Margaris] p. 89.  We
       don't need the non-empty class condition of ~ r19.3rzv when there is an
       outer quantifier.  (Contributed by NM, 25-Oct-2012.) $)
${
	$d y A $.
	$d x y $.
	$d y ph $.
	frr19.3v_0 $f wff ph $.
	frr19.3v_1 $f set x $.
	frr19.3v_2 $f set y $.
	frr19.3v_3 $f class A $.
	rr19.3v $p |- ( A. x e. A A. y e. A ph <-> A. x e. A ph ) $= frr19.3v_0 frr19.3v_2 frr19.3v_3 wral frr19.3v_1 frr19.3v_3 wral frr19.3v_0 frr19.3v_1 frr19.3v_3 wral frr19.3v_0 frr19.3v_2 frr19.3v_3 wral frr19.3v_0 frr19.3v_1 frr19.3v_3 frr19.3v_0 frr19.3v_0 frr19.3v_2 frr19.3v_1 sup_set_class frr19.3v_3 frr19.3v_2 sup_set_class frr19.3v_1 sup_set_class wceq frr19.3v_0 biidd rspcv ralimia frr19.3v_0 frr19.3v_0 frr19.3v_2 frr19.3v_3 wral frr19.3v_1 frr19.3v_3 frr19.3v_0 frr19.3v_0 frr19.3v_2 frr19.3v_3 frr19.3v_0 frr19.3v_2 sup_set_class frr19.3v_3 wcel ax-1 ralrimiv ralimi impbii $.
$}
$( Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  We
       don't need the non-empty class condition of ~ r19.28zv when there is an
       outer quantifier.  (Contributed by NM, 29-Oct-2012.) $)
${
	$d y A $.
	$d x y $.
	$d y ph $.
	frr19.28v_0 $f wff ph $.
	frr19.28v_1 $f wff ps $.
	frr19.28v_2 $f set x $.
	frr19.28v_3 $f set y $.
	frr19.28v_4 $f class A $.
	rr19.28v $p |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> A. x e. A ( ph /\ A. y e. A ps ) ) $= frr19.28v_0 frr19.28v_1 wa frr19.28v_3 frr19.28v_4 wral frr19.28v_2 frr19.28v_4 wral frr19.28v_0 frr19.28v_1 frr19.28v_3 frr19.28v_4 wral wa frr19.28v_2 frr19.28v_4 wral frr19.28v_0 frr19.28v_1 wa frr19.28v_3 frr19.28v_4 wral frr19.28v_0 frr19.28v_1 frr19.28v_3 frr19.28v_4 wral wa frr19.28v_2 frr19.28v_4 frr19.28v_2 sup_set_class frr19.28v_4 wcel frr19.28v_0 frr19.28v_1 wa frr19.28v_3 frr19.28v_4 wral frr19.28v_0 frr19.28v_1 frr19.28v_3 frr19.28v_4 wral frr19.28v_0 frr19.28v_1 wa frr19.28v_3 frr19.28v_4 wral frr19.28v_0 frr19.28v_3 frr19.28v_4 wral frr19.28v_2 sup_set_class frr19.28v_4 wcel frr19.28v_0 frr19.28v_0 frr19.28v_1 wa frr19.28v_0 frr19.28v_3 frr19.28v_4 frr19.28v_0 frr19.28v_1 simpl ralimi frr19.28v_0 frr19.28v_0 frr19.28v_3 frr19.28v_2 sup_set_class frr19.28v_4 frr19.28v_3 sup_set_class frr19.28v_2 sup_set_class wceq frr19.28v_0 biidd rspcv syl5 frr19.28v_0 frr19.28v_1 wa frr19.28v_3 frr19.28v_4 wral frr19.28v_1 frr19.28v_3 frr19.28v_4 wral wi frr19.28v_2 sup_set_class frr19.28v_4 wcel frr19.28v_0 frr19.28v_1 wa frr19.28v_1 frr19.28v_3 frr19.28v_4 frr19.28v_0 frr19.28v_1 simpr ralimi a1i jcad ralimia frr19.28v_0 frr19.28v_1 frr19.28v_3 frr19.28v_4 wral wa frr19.28v_0 frr19.28v_1 wa frr19.28v_3 frr19.28v_4 wral frr19.28v_2 frr19.28v_4 frr19.28v_0 frr19.28v_1 frr19.28v_3 frr19.28v_4 r19.28av ralimi impbii $.
$}
$( Membership in a class abstraction, using implicit substitution.  (Closed
       theorem version of ~ elabg .)  (Contributed by NM, 7-Nov-2005.)  (Proof
       shortened by Andrew Salmon, 8-Jun-2011.) $)
${
	$d x A $.
	$d x ps $.
	felabgt_0 $f wff ph $.
	felabgt_1 $f wff ps $.
	felabgt_2 $f set x $.
	felabgt_3 $f class A $.
	felabgt_4 $f class B $.
	elabgt $p |- ( ( A e. B /\ A. x ( x = A -> ( ph <-> ps ) ) ) -> ( A e. { x | ph } <-> ps ) ) $= felabgt_2 sup_set_class felabgt_3 wceq felabgt_0 felabgt_1 wb wi felabgt_2 wal felabgt_3 felabgt_4 wcel felabgt_2 sup_set_class felabgt_3 wceq felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb wi felabgt_2 wal felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb felabgt_2 sup_set_class felabgt_3 wceq felabgt_0 felabgt_1 wb wi felabgt_2 sup_set_class felabgt_3 wceq felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb wi felabgt_2 felabgt_2 sup_set_class felabgt_3 wceq felabgt_0 felabgt_1 wb felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb felabgt_2 sup_set_class felabgt_3 wceq felabgt_0 felabgt_1 wb felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb felabgt_2 sup_set_class felabgt_3 wceq felabgt_0 felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 felabgt_0 felabgt_2 sup_set_class felabgt_0 felabgt_2 cab wcel felabgt_2 sup_set_class felabgt_3 wceq felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_0 felabgt_2 abid felabgt_2 sup_set_class felabgt_3 felabgt_0 felabgt_2 cab eleq1 syl5bbr bibi1d biimpd a2i alimi felabgt_3 felabgt_4 wcel felabgt_2 sup_set_class felabgt_3 wceq felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb wi felabgt_2 wal felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb felabgt_2 sup_set_class felabgt_3 wceq felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb wi felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb felabgt_2 felabgt_3 felabgt_4 felabgt_2 felabgt_3 nfcv felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 felabgt_2 felabgt_2 felabgt_3 felabgt_0 felabgt_2 cab felabgt_0 felabgt_2 nfab1 nfel2 felabgt_1 felabgt_2 nfv nfbi felabgt_2 sup_set_class felabgt_3 wceq felabgt_3 felabgt_0 felabgt_2 cab wcel felabgt_1 wb pm5.5 spcgf imp sylan2 $.
$}
$( Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  This version has bound-variable
       hypotheses in place of distinct variable restrictions.  (Contributed by
       NM, 21-Sep-2003.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)
${
	felabgf_0 $f wff ph $.
	felabgf_1 $f wff ps $.
	felabgf_2 $f set x $.
	felabgf_3 $f class A $.
	felabgf_4 $f class B $.
	eelabgf_0 $e |- F/_ x A $.
	eelabgf_1 $e |- F/ x ps $.
	eelabgf_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elabgf $p |- ( A e. B -> ( A e. { x | ph } <-> ps ) ) $= felabgf_2 sup_set_class felabgf_0 felabgf_2 cab wcel felabgf_0 wb felabgf_3 felabgf_0 felabgf_2 cab wcel felabgf_1 wb felabgf_2 felabgf_3 felabgf_4 eelabgf_0 felabgf_3 felabgf_0 felabgf_2 cab wcel felabgf_1 felabgf_2 felabgf_2 felabgf_3 felabgf_0 felabgf_2 cab eelabgf_0 felabgf_0 felabgf_2 nfab1 nfel eelabgf_1 nfbi felabgf_2 sup_set_class felabgf_3 wceq felabgf_2 sup_set_class felabgf_0 felabgf_2 cab wcel felabgf_3 felabgf_0 felabgf_2 cab wcel felabgf_0 felabgf_1 felabgf_2 sup_set_class felabgf_3 felabgf_0 felabgf_2 cab eleq1 eelabgf_2 bibi12d felabgf_0 felabgf_2 abid vtoclgf $.
$}
$( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 1-Aug-1994.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)
${
	$d x A $.
	felabf_0 $f wff ph $.
	felabf_1 $f wff ps $.
	felabf_2 $f set x $.
	felabf_3 $f class A $.
	eelabf_0 $e |- F/ x ps $.
	eelabf_1 $e |- A e. _V $.
	eelabf_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elabf $p |- ( A e. { x | ph } <-> ps ) $= felabf_3 cvv wcel felabf_3 felabf_0 felabf_2 cab wcel felabf_1 wb eelabf_1 felabf_0 felabf_1 felabf_2 felabf_3 cvv felabf_2 felabf_3 nfcv eelabf_0 eelabf_2 elabgf ax-mp $.
$}
$( Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  (Contributed by NM, 1-Aug-1994.) $)
${
	$d x ps $.
	$d x A $.
	felab_0 $f wff ph $.
	felab_1 $f wff ps $.
	felab_2 $f set x $.
	felab_3 $f class A $.
	eelab_0 $e |- A e. _V $.
	eelab_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elab $p |- ( A e. { x | ph } <-> ps ) $= felab_0 felab_1 felab_2 felab_3 felab_1 felab_2 nfv eelab_0 eelab_1 elabf $.
$}
$( Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  (Contributed by NM, 14-Apr-1995.) $)
${
	$d x ps $.
	$d x A $.
	felabg_0 $f wff ph $.
	felabg_1 $f wff ps $.
	felabg_2 $f set x $.
	felabg_3 $f class A $.
	felabg_4 $f class V $.
	eelabg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elabg $p |- ( A e. V -> ( A e. { x | ph } <-> ps ) ) $= felabg_0 felabg_1 felabg_2 felabg_3 felabg_4 felabg_2 felabg_3 nfcv felabg_1 felabg_2 nfv eelabg_0 elabgf $.
$}
$( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 13-Sep-1995.) $)
${
	$d x ps $.
	$d x A $.
	felab2g_0 $f wff ph $.
	felab2g_1 $f wff ps $.
	felab2g_2 $f set x $.
	felab2g_3 $f class A $.
	felab2g_4 $f class B $.
	felab2g_5 $f class V $.
	eelab2g_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eelab2g_1 $e |- B = { x | ph } $.
	elab2g $p |- ( A e. V -> ( A e. B <-> ps ) ) $= felab2g_3 felab2g_4 wcel felab2g_3 felab2g_0 felab2g_2 cab wcel felab2g_3 felab2g_5 wcel felab2g_1 felab2g_4 felab2g_0 felab2g_2 cab felab2g_3 eelab2g_1 eleq2i felab2g_0 felab2g_1 felab2g_2 felab2g_3 felab2g_5 eelab2g_0 elabg syl5bb $.
$}
$( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 13-Sep-1995.) $)
${
	$d x ps $.
	$d x A $.
	felab2_0 $f wff ph $.
	felab2_1 $f wff ps $.
	felab2_2 $f set x $.
	felab2_3 $f class A $.
	felab2_4 $f class B $.
	eelab2_0 $e |- A e. _V $.
	eelab2_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eelab2_2 $e |- B = { x | ph } $.
	elab2 $p |- ( A e. B <-> ps ) $= felab2_3 cvv wcel felab2_3 felab2_4 wcel felab2_1 wb eelab2_0 felab2_0 felab2_1 felab2_2 felab2_3 felab2_4 cvv eelab2_1 eelab2_2 elab2g ax-mp $.
$}
$( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 17-Oct-2012.) $)
${
	$d x ps $.
	$d x A $.
	felab4g_0 $f wff ph $.
	felab4g_1 $f wff ps $.
	felab4g_2 $f set x $.
	felab4g_3 $f class A $.
	felab4g_4 $f class B $.
	eelab4g_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eelab4g_1 $e |- B = { x | ph } $.
	elab4g $p |- ( A e. B <-> ( A e. _V /\ ps ) ) $= felab4g_3 felab4g_4 wcel felab4g_3 cvv wcel felab4g_1 felab4g_3 felab4g_4 elex felab4g_0 felab4g_1 felab4g_2 felab4g_3 felab4g_4 cvv eelab4g_0 eelab4g_1 elab2g biadan2 $.
$}
$( Membership in a class abstraction, with a weaker antecedent than
       ~ elabgf .  (Contributed by NM, 6-Sep-2011.) $)
${
	felab3gf_0 $f wff ph $.
	felab3gf_1 $f wff ps $.
	felab3gf_2 $f set x $.
	felab3gf_3 $f class A $.
	felab3gf_4 $f class B $.
	eelab3gf_0 $e |- F/_ x A $.
	eelab3gf_1 $e |- F/ x ps $.
	eelab3gf_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elab3gf $p |- ( ( ps -> A e. B ) -> ( A e. { x | ph } <-> ps ) ) $= felab3gf_1 felab3gf_3 felab3gf_4 wcel felab3gf_3 felab3gf_0 felab3gf_2 cab wcel felab3gf_1 wb felab3gf_1 wn felab3gf_3 felab3gf_0 felab3gf_2 cab wcel felab3gf_1 felab3gf_3 felab3gf_0 felab3gf_2 cab wcel felab3gf_1 felab3gf_0 felab3gf_1 felab3gf_2 felab3gf_3 felab3gf_0 felab3gf_2 cab eelab3gf_0 eelab3gf_1 eelab3gf_2 elabgf ibi felab3gf_1 felab3gf_3 felab3gf_0 felab3gf_2 cab wcel pm2.21 impbid2 felab3gf_0 felab3gf_1 felab3gf_2 felab3gf_3 felab3gf_4 eelab3gf_0 eelab3gf_1 eelab3gf_2 elabgf ja $.
$}
$( Membership in a class abstraction, with a weaker antecedent than
       ~ elabg .  (Contributed by NM, 29-Aug-2006.) $)
${
	$d x ps $.
	$d x A $.
	felab3g_0 $f wff ph $.
	felab3g_1 $f wff ps $.
	felab3g_2 $f set x $.
	felab3g_3 $f class A $.
	felab3g_4 $f class B $.
	eelab3g_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elab3g $p |- ( ( ps -> A e. B ) -> ( A e. { x | ph } <-> ps ) ) $= felab3g_0 felab3g_1 felab3g_2 felab3g_3 felab3g_4 felab3g_2 felab3g_3 nfcv felab3g_1 felab3g_2 nfv eelab3g_0 elab3gf $.
$}
$( Membership in a class abstraction using implicit substitution.
       (Contributed by NM, 10-Nov-2000.) $)
${
	$d x ps $.
	$d x A $.
	felab3_0 $f wff ph $.
	felab3_1 $f wff ps $.
	felab3_2 $f set x $.
	felab3_3 $f class A $.
	eelab3_0 $e |- ( ps -> A e. _V ) $.
	eelab3_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elab3 $p |- ( A e. { x | ph } <-> ps ) $= felab3_1 felab3_3 cvv wcel wi felab3_3 felab3_0 felab3_2 cab wcel felab3_1 wb eelab3_0 felab3_0 felab3_1 felab3_2 felab3_3 cvv eelab3_1 elab3g ax-mp $.
$}
$( Membership in a restricted class abstraction, using implicit
       substitution.  This version has bound-variable hypotheses in place of
       distinct variable restrictions.  (Contributed by NM, 21-Sep-2003.) $)
${
	felrabf_0 $f wff ph $.
	felrabf_1 $f wff ps $.
	felrabf_2 $f set x $.
	felrabf_3 $f class A $.
	felrabf_4 $f class B $.
	eelrabf_0 $e |- F/_ x A $.
	eelrabf_1 $e |- F/_ x B $.
	eelrabf_2 $e |- F/ x ps $.
	eelrabf_3 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elrabf $p |- ( A e. { x e. B | ph } <-> ( A e. B /\ ps ) ) $= felrabf_3 felrabf_0 felrabf_2 felrabf_4 crab wcel felrabf_3 cvv wcel felrabf_3 felrabf_4 wcel felrabf_1 wa felrabf_3 felrabf_0 felrabf_2 felrabf_4 crab elex felrabf_3 felrabf_4 wcel felrabf_3 cvv wcel felrabf_1 felrabf_3 felrabf_4 elex adantr felrabf_3 felrabf_0 felrabf_2 felrabf_4 crab wcel felrabf_3 felrabf_2 sup_set_class felrabf_4 wcel felrabf_0 wa felrabf_2 cab wcel felrabf_3 cvv wcel felrabf_3 felrabf_4 wcel felrabf_1 wa felrabf_0 felrabf_2 felrabf_4 crab felrabf_2 sup_set_class felrabf_4 wcel felrabf_0 wa felrabf_2 cab felrabf_3 felrabf_0 felrabf_2 felrabf_4 df-rab eleq2i felrabf_2 sup_set_class felrabf_4 wcel felrabf_0 wa felrabf_3 felrabf_4 wcel felrabf_1 wa felrabf_2 felrabf_3 cvv eelrabf_0 felrabf_3 felrabf_4 wcel felrabf_1 felrabf_2 felrabf_2 felrabf_3 felrabf_4 eelrabf_0 eelrabf_1 nfel eelrabf_2 nfan felrabf_2 sup_set_class felrabf_3 wceq felrabf_2 sup_set_class felrabf_4 wcel felrabf_3 felrabf_4 wcel felrabf_0 felrabf_1 felrabf_2 sup_set_class felrabf_3 felrabf_4 eleq1 eelrabf_3 anbi12d elabgf syl5bb pm5.21nii $.
$}
$( Membership in a restricted class abstraction, using implicit
       substitution.  (Contributed by NM, 21-May-1999.) $)
${
	$d x ps $.
	$d x A $.
	$d x B $.
	felrab_0 $f wff ph $.
	felrab_1 $f wff ps $.
	felrab_2 $f set x $.
	felrab_3 $f class A $.
	felrab_4 $f class B $.
	eelrab_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elrab $p |- ( A e. { x e. B | ph } <-> ( A e. B /\ ps ) ) $= felrab_0 felrab_1 felrab_2 felrab_3 felrab_4 felrab_2 felrab_3 nfcv felrab_2 felrab_4 nfcv felrab_1 felrab_2 nfv eelrab_0 elrabf $.
$}
$( Membership in a restricted class abstraction, using implicit
       substitution.  (Contributed by NM, 5-Oct-2006.) $)
${
	$d x ps $.
	$d x A $.
	$d x B $.
	felrab3_0 $f wff ph $.
	felrab3_1 $f wff ps $.
	felrab3_2 $f set x $.
	felrab3_3 $f class A $.
	felrab3_4 $f class B $.
	eelrab3_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elrab3 $p |- ( A e. B -> ( A e. { x e. B | ph } <-> ps ) ) $= felrab3_3 felrab3_0 felrab3_2 felrab3_4 crab wcel felrab3_3 felrab3_4 wcel felrab3_1 felrab3_0 felrab3_1 felrab3_2 felrab3_3 felrab3_4 eelrab3_0 elrab baib $.
$}
$( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 2-Nov-2006.) $)
${
	$d x ps $.
	$d x A $.
	$d x B $.
	felrab2_0 $f wff ph $.
	felrab2_1 $f wff ps $.
	felrab2_2 $f set x $.
	felrab2_3 $f class A $.
	felrab2_4 $f class B $.
	felrab2_5 $f class C $.
	eelrab2_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eelrab2_1 $e |- C = { x e. B | ph } $.
	elrab2 $p |- ( A e. C <-> ( A e. B /\ ps ) ) $= felrab2_3 felrab2_5 wcel felrab2_3 felrab2_0 felrab2_2 felrab2_4 crab wcel felrab2_3 felrab2_4 wcel felrab2_1 wa felrab2_5 felrab2_0 felrab2_2 felrab2_4 crab felrab2_3 eelrab2_1 eleq2i felrab2_0 felrab2_1 felrab2_2 felrab2_3 felrab2_4 eelrab2_0 elrab bitri $.
$}
$( Universal quantification over a class abstraction.  (Contributed by Jeff
       Madsen, 10-Jun-2010.) $)
${
	$d x y $.
	$d y ps $.
	fralab_0 $f wff ph $.
	fralab_1 $f wff ps $.
	fralab_2 $f wff ch $.
	fralab_3 $f set x $.
	fralab_4 $f set y $.
	eralab_0 $e |- ( y = x -> ( ph <-> ps ) ) $.
	ralab $p |- ( A. x e. { y | ph } ch <-> A. x ( ps -> ch ) ) $= fralab_2 fralab_3 fralab_0 fralab_4 cab wral fralab_3 sup_set_class fralab_0 fralab_4 cab wcel fralab_2 wi fralab_3 wal fralab_1 fralab_2 wi fralab_3 wal fralab_2 fralab_3 fralab_0 fralab_4 cab df-ral fralab_3 sup_set_class fralab_0 fralab_4 cab wcel fralab_2 wi fralab_1 fralab_2 wi fralab_3 fralab_3 sup_set_class fralab_0 fralab_4 cab wcel fralab_1 fralab_2 fralab_0 fralab_1 fralab_4 fralab_3 sup_set_class fralab_3 vex eralab_0 elab imbi1i albii bitri $.
$}
$( Universal quantification over a restricted class abstraction.
       (Contributed by Jeff Madsen, 10-Jun-2010.) $)
${
	$d x y $.
	$d y A $.
	$d y ps $.
	fralrab_0 $f wff ph $.
	fralrab_1 $f wff ps $.
	fralrab_2 $f wff ch $.
	fralrab_3 $f set x $.
	fralrab_4 $f set y $.
	fralrab_5 $f class A $.
	eralrab_0 $e |- ( y = x -> ( ph <-> ps ) ) $.
	ralrab $p |- ( A. x e. { y e. A | ph } ch <-> A. x e. A ( ps -> ch ) ) $= fralrab_2 fralrab_1 fralrab_2 wi fralrab_3 fralrab_0 fralrab_4 fralrab_5 crab fralrab_5 fralrab_3 sup_set_class fralrab_0 fralrab_4 fralrab_5 crab wcel fralrab_2 wi fralrab_3 sup_set_class fralrab_5 wcel fralrab_1 wa fralrab_2 wi fralrab_3 sup_set_class fralrab_5 wcel fralrab_1 fralrab_2 wi wi fralrab_3 sup_set_class fralrab_0 fralrab_4 fralrab_5 crab wcel fralrab_3 sup_set_class fralrab_5 wcel fralrab_1 wa fralrab_2 fralrab_0 fralrab_1 fralrab_4 fralrab_3 sup_set_class fralrab_5 eralrab_0 elrab imbi1i fralrab_3 sup_set_class fralrab_5 wcel fralrab_1 fralrab_2 impexp bitri ralbii2 $.
$}
$( Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 23-Jan-2014.)  (Revised by Mario Carneiro,
       3-Sep-2015.) $)
${
	$d x y $.
	$d y ps $.
	frexab_0 $f wff ph $.
	frexab_1 $f wff ps $.
	frexab_2 $f wff ch $.
	frexab_3 $f set x $.
	frexab_4 $f set y $.
	erexab_0 $e |- ( y = x -> ( ph <-> ps ) ) $.
	rexab $p |- ( E. x e. { y | ph } ch <-> E. x ( ps /\ ch ) ) $= frexab_2 frexab_3 frexab_0 frexab_4 cab wrex frexab_3 sup_set_class frexab_0 frexab_4 cab wcel frexab_2 wa frexab_3 wex frexab_1 frexab_2 wa frexab_3 wex frexab_2 frexab_3 frexab_0 frexab_4 cab df-rex frexab_3 sup_set_class frexab_0 frexab_4 cab wcel frexab_2 wa frexab_1 frexab_2 wa frexab_3 frexab_3 sup_set_class frexab_0 frexab_4 cab wcel frexab_1 frexab_2 frexab_0 frexab_1 frexab_4 frexab_3 sup_set_class frexab_3 vex erexab_0 elab anbi1i exbii bitri $.
$}
$( Existential quantification over a class abstraction.  (Contributed by
       Jeff Madsen, 17-Jun-2011.)  (Revised by Mario Carneiro, 3-Sep-2015.) $)
${
	$d x y $.
	$d y A $.
	$d y ps $.
	frexrab_0 $f wff ph $.
	frexrab_1 $f wff ps $.
	frexrab_2 $f wff ch $.
	frexrab_3 $f set x $.
	frexrab_4 $f set y $.
	frexrab_5 $f class A $.
	erexrab_0 $e |- ( y = x -> ( ph <-> ps ) ) $.
	rexrab $p |- ( E. x e. { y e. A | ph } ch <-> E. x e. A ( ps /\ ch ) ) $= frexrab_2 frexrab_1 frexrab_2 wa frexrab_3 frexrab_0 frexrab_4 frexrab_5 crab frexrab_5 frexrab_3 sup_set_class frexrab_0 frexrab_4 frexrab_5 crab wcel frexrab_2 wa frexrab_3 sup_set_class frexrab_5 wcel frexrab_1 wa frexrab_2 wa frexrab_3 sup_set_class frexrab_5 wcel frexrab_1 frexrab_2 wa wa frexrab_3 sup_set_class frexrab_0 frexrab_4 frexrab_5 crab wcel frexrab_3 sup_set_class frexrab_5 wcel frexrab_1 wa frexrab_2 frexrab_0 frexrab_1 frexrab_4 frexrab_3 sup_set_class frexrab_5 erexrab_0 elrab anbi1i frexrab_3 sup_set_class frexrab_5 wcel frexrab_1 frexrab_2 anass bitri rexbii2 $.
$}
$( Universal quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)
${
	$d x y $.
	$d x ch $.
	$d x ph $.
	$d y ps $.
	fralab2_0 $f wff ph $.
	fralab2_1 $f wff ps $.
	fralab2_2 $f wff ch $.
	fralab2_3 $f set x $.
	fralab2_4 $f set y $.
	eralab2_0 $e |- ( x = y -> ( ps <-> ch ) ) $.
	ralab2 $p |- ( A. x e. { y | ph } ps <-> A. y ( ph -> ch ) ) $= fralab2_1 fralab2_3 fralab2_0 fralab2_4 cab wral fralab2_3 sup_set_class fralab2_0 fralab2_4 cab wcel fralab2_1 wi fralab2_3 wal fralab2_0 fralab2_2 wi fralab2_4 wal fralab2_1 fralab2_3 fralab2_0 fralab2_4 cab df-ral fralab2_3 sup_set_class fralab2_0 fralab2_4 cab wcel fralab2_1 wi fralab2_0 fralab2_2 wi fralab2_3 fralab2_4 fralab2_3 sup_set_class fralab2_0 fralab2_4 cab wcel fralab2_1 fralab2_4 fralab2_0 fralab2_4 fralab2_3 nfsab1 fralab2_1 fralab2_4 nfv nfim fralab2_0 fralab2_2 wi fralab2_3 nfv fralab2_3 sup_set_class fralab2_4 sup_set_class wceq fralab2_3 sup_set_class fralab2_0 fralab2_4 cab wcel fralab2_0 fralab2_1 fralab2_2 fralab2_3 sup_set_class fralab2_4 sup_set_class wceq fralab2_3 sup_set_class fralab2_0 fralab2_4 cab wcel fralab2_4 sup_set_class fralab2_0 fralab2_4 cab wcel fralab2_0 fralab2_3 sup_set_class fralab2_4 sup_set_class fralab2_0 fralab2_4 cab eleq1 fralab2_0 fralab2_4 abid syl6bb eralab2_0 imbi12d cbval bitri $.
$}
$( Universal quantification over a restricted class abstraction.
       (Contributed by Mario Carneiro, 3-Sep-2015.) $)
${
	$d x y $.
	$d x A $.
	$d x ch $.
	$d x ph $.
	$d y ps $.
	fralrab2_0 $f wff ph $.
	fralrab2_1 $f wff ps $.
	fralrab2_2 $f wff ch $.
	fralrab2_3 $f set x $.
	fralrab2_4 $f set y $.
	fralrab2_5 $f class A $.
	eralrab2_0 $e |- ( x = y -> ( ps <-> ch ) ) $.
	ralrab2 $p |- ( A. x e. { y e. A | ph } ps <-> A. y e. A ( ph -> ch ) ) $= fralrab2_1 fralrab2_3 fralrab2_0 fralrab2_4 fralrab2_5 crab wral fralrab2_1 fralrab2_3 fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 wa fralrab2_4 cab wral fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 wa fralrab2_2 wi fralrab2_4 wal fralrab2_0 fralrab2_2 wi fralrab2_4 fralrab2_5 wral fralrab2_1 fralrab2_3 fralrab2_0 fralrab2_4 fralrab2_5 crab fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 wa fralrab2_4 cab fralrab2_0 fralrab2_4 fralrab2_5 df-rab raleqi fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 wa fralrab2_1 fralrab2_2 fralrab2_3 fralrab2_4 eralrab2_0 ralab2 fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 wa fralrab2_2 wi fralrab2_4 wal fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 fralrab2_2 wi wi fralrab2_4 wal fralrab2_0 fralrab2_2 wi fralrab2_4 fralrab2_5 wral fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 wa fralrab2_2 wi fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 fralrab2_2 wi wi fralrab2_4 fralrab2_4 sup_set_class fralrab2_5 wcel fralrab2_0 fralrab2_2 impexp albii fralrab2_0 fralrab2_2 wi fralrab2_4 fralrab2_5 df-ral bitr4i 3bitri $.
$}
$( Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)
${
	$d x y $.
	$d x ch $.
	$d x ph $.
	$d y ps $.
	frexab2_0 $f wff ph $.
	frexab2_1 $f wff ps $.
	frexab2_2 $f wff ch $.
	frexab2_3 $f set x $.
	frexab2_4 $f set y $.
	erexab2_0 $e |- ( x = y -> ( ps <-> ch ) ) $.
	rexab2 $p |- ( E. x e. { y | ph } ps <-> E. y ( ph /\ ch ) ) $= frexab2_1 frexab2_3 frexab2_0 frexab2_4 cab wrex frexab2_3 sup_set_class frexab2_0 frexab2_4 cab wcel frexab2_1 wa frexab2_3 wex frexab2_0 frexab2_2 wa frexab2_4 wex frexab2_1 frexab2_3 frexab2_0 frexab2_4 cab df-rex frexab2_3 sup_set_class frexab2_0 frexab2_4 cab wcel frexab2_1 wa frexab2_0 frexab2_2 wa frexab2_3 frexab2_4 frexab2_3 sup_set_class frexab2_0 frexab2_4 cab wcel frexab2_1 frexab2_4 frexab2_0 frexab2_4 frexab2_3 nfsab1 frexab2_1 frexab2_4 nfv nfan frexab2_0 frexab2_2 wa frexab2_3 nfv frexab2_3 sup_set_class frexab2_4 sup_set_class wceq frexab2_3 sup_set_class frexab2_0 frexab2_4 cab wcel frexab2_0 frexab2_1 frexab2_2 frexab2_3 sup_set_class frexab2_4 sup_set_class wceq frexab2_3 sup_set_class frexab2_0 frexab2_4 cab wcel frexab2_4 sup_set_class frexab2_0 frexab2_4 cab wcel frexab2_0 frexab2_3 sup_set_class frexab2_4 sup_set_class frexab2_0 frexab2_4 cab eleq1 frexab2_0 frexab2_4 abid syl6bb erexab2_0 anbi12d cbvex bitri $.
$}
$( Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)
${
	$d x y $.
	$d x A $.
	$d x ch $.
	$d x ph $.
	$d y ps $.
	frexrab2_0 $f wff ph $.
	frexrab2_1 $f wff ps $.
	frexrab2_2 $f wff ch $.
	frexrab2_3 $f set x $.
	frexrab2_4 $f set y $.
	frexrab2_5 $f class A $.
	erexrab2_0 $e |- ( x = y -> ( ps <-> ch ) ) $.
	rexrab2 $p |- ( E. x e. { y e. A | ph } ps <-> E. y e. A ( ph /\ ch ) ) $= frexrab2_1 frexrab2_3 frexrab2_0 frexrab2_4 frexrab2_5 crab wrex frexrab2_1 frexrab2_3 frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 wa frexrab2_4 cab wrex frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 wa frexrab2_2 wa frexrab2_4 wex frexrab2_0 frexrab2_2 wa frexrab2_4 frexrab2_5 wrex frexrab2_1 frexrab2_3 frexrab2_0 frexrab2_4 frexrab2_5 crab frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 wa frexrab2_4 cab frexrab2_0 frexrab2_4 frexrab2_5 df-rab rexeqi frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 wa frexrab2_1 frexrab2_2 frexrab2_3 frexrab2_4 erexrab2_0 rexab2 frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 wa frexrab2_2 wa frexrab2_4 wex frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 frexrab2_2 wa wa frexrab2_4 wex frexrab2_0 frexrab2_2 wa frexrab2_4 frexrab2_5 wrex frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 wa frexrab2_2 wa frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 frexrab2_2 wa wa frexrab2_4 frexrab2_4 sup_set_class frexrab2_5 wcel frexrab2_0 frexrab2_2 anass exbii frexrab2_0 frexrab2_2 wa frexrab2_4 frexrab2_5 df-rex bitr4i 3bitri $.
$}
$( Identity used to create closed-form versions of bound-variable
       hypothesis builders for class expressions.  (Contributed by NM,
       10-Nov-2005.)  (Proof shortened by Mario Carneiro, 12-Oct-2016.) $)
${
	$d x z $.
	$d A z $.
	fabidnf_0 $f set x $.
	fabidnf_1 $f set z $.
	fabidnf_2 $f class A $.
	abidnf $p |- ( F/_ x A -> { z | A. x z e. A } = A ) $= fabidnf_0 fabidnf_2 wnfc fabidnf_1 sup_set_class fabidnf_2 wcel fabidnf_0 wal fabidnf_1 fabidnf_2 fabidnf_0 fabidnf_2 wnfc fabidnf_1 sup_set_class fabidnf_2 wcel fabidnf_0 wal fabidnf_1 sup_set_class fabidnf_2 wcel fabidnf_1 sup_set_class fabidnf_2 wcel fabidnf_0 sp fabidnf_0 fabidnf_2 wnfc fabidnf_1 sup_set_class fabidnf_2 wcel fabidnf_0 fabidnf_0 fabidnf_1 fabidnf_2 nfcr nfrd impbid2 abbi1dv $.
$}
$( A deduction theorem for converting the inference ` |- F/_ x A ` =>
       ` |- ph ` into a closed theorem.  Use ~ nfa1 and ~ nfab to eliminate the
       hypothesis of the substitution instance ` ps ` of the inference.  For
       converting the inference form into a deduction form, ~ abidnf is
       useful.  (Contributed by NM, 8-Dec-2006.) $)
${
	$d x z $.
	$d z A $.
	fdedhb_0 $f wff ph $.
	fdedhb_1 $f wff ps $.
	fdedhb_2 $f set x $.
	fdedhb_3 $f set z $.
	fdedhb_4 $f class A $.
	ededhb_0 $e |- ( A = { z | A. x z e. A } -> ( ph <-> ps ) ) $.
	ededhb_1 $e |- ps $.
	dedhb $p |- ( F/_ x A -> ph ) $= fdedhb_2 fdedhb_4 wnfc fdedhb_0 fdedhb_1 ededhb_1 fdedhb_2 fdedhb_4 wnfc fdedhb_4 fdedhb_3 sup_set_class fdedhb_4 wcel fdedhb_2 wal fdedhb_3 cab wceq fdedhb_0 fdedhb_1 wb fdedhb_2 fdedhb_4 wnfc fdedhb_3 sup_set_class fdedhb_4 wcel fdedhb_2 wal fdedhb_3 cab fdedhb_4 fdedhb_2 fdedhb_3 fdedhb_4 abidnf eqcomd ededhb_0 syl mpbiri $.
$}
$( A condition which implies existential uniqueness.  (Contributed by Jeff
       Hankins, 8-Sep-2009.) $)
${
	$d y ph $.
	$d x y ps $.
	$d x y A $.
	ieqeu_0 $f set y $.
	feqeu_0 $f wff ph $.
	feqeu_1 $f wff ps $.
	feqeu_2 $f set x $.
	feqeu_3 $f class A $.
	feqeu_4 $f class B $.
	eeqeu_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eqeu $p |- ( ( A e. B /\ ps /\ A. x ( ph -> x = A ) ) -> E! x ph ) $= feqeu_3 feqeu_4 wcel feqeu_1 feqeu_0 feqeu_2 sup_set_class feqeu_3 wceq wi feqeu_2 wal w3a feqeu_0 feqeu_2 wex feqeu_0 feqeu_2 sup_set_class ieqeu_0 sup_set_class wceq wi feqeu_2 wal ieqeu_0 wex feqeu_0 feqeu_2 weu feqeu_3 feqeu_4 wcel feqeu_1 feqeu_0 feqeu_2 wex feqeu_0 feqeu_2 sup_set_class feqeu_3 wceq wi feqeu_2 wal feqeu_3 feqeu_4 wcel feqeu_1 feqeu_0 feqeu_2 wex feqeu_0 feqeu_1 feqeu_2 feqeu_3 feqeu_4 eeqeu_0 spcegv imp 3adant3 feqeu_3 feqeu_4 wcel feqeu_0 feqeu_2 sup_set_class feqeu_3 wceq wi feqeu_2 wal feqeu_0 feqeu_2 sup_set_class ieqeu_0 sup_set_class wceq wi feqeu_2 wal ieqeu_0 wex feqeu_1 feqeu_3 feqeu_4 wcel feqeu_0 feqeu_2 sup_set_class feqeu_3 wceq wi feqeu_2 wal feqeu_0 feqeu_2 sup_set_class ieqeu_0 sup_set_class wceq wi feqeu_2 wal ieqeu_0 wex feqeu_0 feqeu_2 sup_set_class ieqeu_0 sup_set_class wceq wi feqeu_2 wal feqeu_0 feqeu_2 sup_set_class feqeu_3 wceq wi feqeu_2 wal ieqeu_0 feqeu_3 feqeu_4 ieqeu_0 sup_set_class feqeu_3 wceq feqeu_0 feqeu_2 sup_set_class ieqeu_0 sup_set_class wceq wi feqeu_0 feqeu_2 sup_set_class feqeu_3 wceq wi feqeu_2 ieqeu_0 sup_set_class feqeu_3 wceq feqeu_2 sup_set_class ieqeu_0 sup_set_class wceq feqeu_2 sup_set_class feqeu_3 wceq feqeu_0 ieqeu_0 sup_set_class feqeu_3 feqeu_2 sup_set_class eqeq2 imbi2d albidv spcegv imp 3adant2 feqeu_0 feqeu_2 ieqeu_0 feqeu_0 ieqeu_0 nfv eu3 sylanbrc $.
$}
$( Equality has existential uniqueness.  (Contributed by NM,
       25-Nov-1994.) $)
${
	$d x y A $.
	ieueq_0 $f set y $.
	feueq_0 $f set x $.
	feueq_1 $f class A $.
	eueq $p |- ( A e. _V <-> E! x x = A ) $= feueq_0 sup_set_class feueq_1 wceq feueq_0 wex feueq_0 sup_set_class feueq_1 wceq feueq_0 wex feueq_0 sup_set_class feueq_1 wceq ieueq_0 sup_set_class feueq_1 wceq wa feueq_0 sup_set_class ieueq_0 sup_set_class wceq wi ieueq_0 wal feueq_0 wal wa feueq_1 cvv wcel feueq_0 sup_set_class feueq_1 wceq feueq_0 weu feueq_0 sup_set_class feueq_1 wceq ieueq_0 sup_set_class feueq_1 wceq wa feueq_0 sup_set_class ieueq_0 sup_set_class wceq wi ieueq_0 wal feueq_0 wal feueq_0 sup_set_class feueq_1 wceq feueq_0 wex feueq_0 sup_set_class feueq_1 wceq ieueq_0 sup_set_class feueq_1 wceq wa feueq_0 sup_set_class ieueq_0 sup_set_class wceq wi feueq_0 ieueq_0 feueq_0 sup_set_class ieueq_0 sup_set_class feueq_1 eqtr3 gen2 biantru feueq_0 feueq_1 isset feueq_0 sup_set_class feueq_1 wceq ieueq_0 sup_set_class feueq_1 wceq feueq_0 ieueq_0 feueq_0 sup_set_class ieueq_0 sup_set_class feueq_1 eqeq1 eu4 3bitr4i $.
$}
$( Equality has existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)
${
	$d x A $.
	feueq1_0 $f set x $.
	feueq1_1 $f class A $.
	eeueq1_0 $e |- A e. _V $.
	eueq1 $p |- E! x x = A $= feueq1_1 cvv wcel feueq1_0 sup_set_class feueq1_1 wceq feueq1_0 weu eeueq1_0 feueq1_0 feueq1_1 eueq mpbi $.
$}
$( Equality has existential uniqueness (split into 2 cases).  (Contributed
       by NM, 5-Apr-1995.) $)
${
	$d x ph $.
	$d x A $.
	$d x B $.
	feueq2_0 $f wff ph $.
	feueq2_1 $f set x $.
	feueq2_2 $f class A $.
	feueq2_3 $f class B $.
	eeueq2_0 $e |- A e. _V $.
	eeueq2_1 $e |- B e. _V $.
	eueq2 $p |- E! x ( ( ph /\ x = A ) \/ ( -. ph /\ x = B ) ) $= feueq2_0 feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_1 weu feueq2_0 feueq2_0 wn feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa wo feueq2_1 weu feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_1 weu feueq2_0 feueq2_0 wn wn feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_1 weu feueq2_0 wn feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa wo feueq2_1 weu feueq2_0 notnot1 feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq feueq2_1 weu feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_1 weu feueq2_1 feueq2_2 eeueq2_0 eueq1 feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_1 weu feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq feueq2_1 weu wa feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq feueq2_1 euanv biimpri mpan2 feueq2_0 wn feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_1 euorv syl2anc feueq2_0 feueq2_0 wn feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa wo feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_1 feueq2_0 wn feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa wo feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 wn wo feueq2_0 feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_0 wn feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa orcom feueq2_0 feueq2_0 wn feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq feueq2_0 notnot1 bianfd orbi2d syl5bb eubidv mpbid feueq2_0 wn feueq2_0 feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_1 weu feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_1 weu feueq2_0 wn feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa feueq2_1 weu feueq2_0 feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_1 weu feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq feueq2_1 weu feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa feueq2_1 weu feueq2_1 feueq2_3 eeueq2_1 eueq1 feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa feueq2_1 weu feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq feueq2_1 weu wa feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq feueq2_1 euanv biimpri mpan2 feueq2_0 feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa feueq2_1 euorv mpdan feueq2_0 wn feueq2_0 feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa wo feueq2_1 feueq2_0 wn feueq2_0 feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq wa feueq2_0 wn feueq2_1 sup_set_class feueq2_3 wceq wa feueq2_0 wn feueq2_0 feueq2_1 sup_set_class feueq2_2 wceq feueq2_0 wn id bianfd orbi1d eubidv mpbid pm2.61i $.
$}
$( Equality has existential uniqueness (split into 3 cases).  (Contributed
       by NM, 5-Apr-1995.)  (Proof shortened by Mario Carneiro,
       28-Sep-2015.) $)
${
	$d x ph $.
	$d x ps $.
	$d x A $.
	$d x B $.
	$d x C $.
	feueq3_0 $f wff ph $.
	feueq3_1 $f wff ps $.
	feueq3_2 $f set x $.
	feueq3_3 $f class A $.
	feueq3_4 $f class B $.
	feueq3_5 $f class C $.
	eeueq3_0 $e |- A e. _V $.
	eeueq3_1 $e |- B e. _V $.
	eeueq3_2 $e |- C e. _V $.
	eeueq3_3 $e |- -. ( ph /\ ps ) $.
	eueq3 $p |- E! x ( ( ph /\ x = A ) \/ ( -. ( ph \/ ps ) /\ x = B ) \/ ( ps /\ x = C ) ) $= feueq3_0 feueq3_1 feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_2 weu feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq feueq3_2 weu feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_2 weu feueq3_2 feueq3_3 eeueq3_0 eueq1 feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_2 feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq ibar feueq3_0 feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo wn feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa wo wb feueq3_0 feueq3_0 feueq3_1 wo wn feueq3_1 wo feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_1 wo wn feueq3_1 wo feueq3_0 feueq3_0 feueq3_1 wo wn feueq3_0 wn feueq3_1 feueq3_0 feueq3_1 pm2.45 feueq3_0 feueq3_1 feueq3_0 feueq3_1 eeueq3_3 imnani con2i jaoi con2i feueq3_0 feueq3_0 feueq3_1 wo wn feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa feueq3_0 feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq feueq3_0 feueq3_1 wo wn feueq3_0 feueq3_0 feueq3_1 pm2.45 con2i bianfd feueq3_0 feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq feueq3_0 feueq3_1 eeueq3_3 imnani bianfd orbi12d mtbid feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa biorf syl bitrd feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa w3o feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa 3orrot feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa df-3or bitri syl6bbr eubidv mpbii feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq feueq3_2 weu feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_2 weu feueq3_2 feueq3_5 eeueq3_2 eueq1 feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_2 feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq ibar feueq3_1 feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo wn feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo wb feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo feueq3_1 feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 wn feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_0 feueq3_1 wn feueq3_2 sup_set_class feueq3_3 wceq feueq3_0 feueq3_1 eeueq3_3 imnani adantr feueq3_0 feueq3_1 wo wn feueq3_1 wn feueq3_2 sup_set_class feueq3_4 wceq feueq3_0 feueq3_1 pm2.46 adantr jaoi con2i feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa biorf syl bitrd feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa df-3or syl6bbr eubidv mpbii feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq feueq3_2 weu feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_2 weu feueq3_2 feueq3_4 eeueq3_1 eueq1 feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_2 feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq ibar feueq3_0 feueq3_1 wo wn feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo wn feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo wb feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_1 wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa feueq3_1 feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq simpl feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq simpl orim12i con3i feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa biorf syl bitrd feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa w3o feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa w3o feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa wo feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa wo feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa 3orcomb feueq3_0 feueq3_2 sup_set_class feueq3_3 wceq wa feueq3_1 feueq3_2 sup_set_class feueq3_5 wceq wa feueq3_0 feueq3_1 wo wn feueq3_2 sup_set_class feueq3_4 wceq wa df-3or bitri syl6bbr eubidv mpbii ecase3 $.
$}
$( There is at most one set equal to a class.  (Contributed by NM,
       8-Mar-1995.) $)
${
	$d x A $.
	fmoeq_0 $f set x $.
	fmoeq_1 $f class A $.
	moeq $p |- E* x x = A $= fmoeq_0 sup_set_class fmoeq_1 wceq fmoeq_0 wmo fmoeq_0 sup_set_class fmoeq_1 wceq fmoeq_0 wex fmoeq_0 sup_set_class fmoeq_1 wceq fmoeq_0 weu wi fmoeq_0 sup_set_class fmoeq_1 wceq fmoeq_0 wex fmoeq_0 sup_set_class fmoeq_1 wceq fmoeq_0 weu fmoeq_0 sup_set_class fmoeq_1 wceq fmoeq_0 wex fmoeq_1 cvv wcel fmoeq_0 sup_set_class fmoeq_1 wceq fmoeq_0 weu fmoeq_0 fmoeq_1 isset fmoeq_0 fmoeq_1 eueq bitr3i biimpi fmoeq_0 sup_set_class fmoeq_1 wceq fmoeq_0 df-mo mpbir $.
$}
$( "At most one" property of equality (split into 3 cases).  (The first 2
       hypotheses could be eliminated with longer proof.)  (Contributed by NM,
       23-Apr-1995.) $)
${
	$d x y ph $.
	$d x y ps $.
	$d x y A $.
	$d x y B $.
	$d x y C $.
	imoeq3_0 $f set y $.
	fmoeq3_0 $f wff ph $.
	fmoeq3_1 $f wff ps $.
	fmoeq3_2 $f set x $.
	fmoeq3_3 $f class A $.
	fmoeq3_4 $f class B $.
	fmoeq3_5 $f class C $.
	emoeq3_0 $e |- B e. _V $.
	emoeq3_1 $e |- C e. _V $.
	emoeq3_2 $e |- -. ( ph /\ ps ) $.
	moeq3 $p |- E* x ( ( ph /\ x = A ) \/ ( -. ( ph \/ ps ) /\ x = B ) \/ ( ps /\ x = C ) ) $= fmoeq3_3 cvv wcel fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 wmo fmoeq3_3 cvv wcel fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 weu fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 wmo fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 weu fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 weu imoeq3_0 fmoeq3_3 cvv imoeq3_0 sup_set_class fmoeq3_3 wceq fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 imoeq3_0 sup_set_class fmoeq3_3 wceq fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa imoeq3_0 sup_set_class fmoeq3_3 wceq fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq fmoeq3_2 sup_set_class fmoeq3_3 wceq fmoeq3_0 imoeq3_0 sup_set_class fmoeq3_3 fmoeq3_2 sup_set_class eqeq2 anbi2d imoeq3_0 sup_set_class fmoeq3_3 wceq fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa biidd imoeq3_0 sup_set_class fmoeq3_3 wceq fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa biidd 3orbi123d eubidv fmoeq3_0 fmoeq3_1 fmoeq3_2 imoeq3_0 sup_set_class fmoeq3_4 fmoeq3_5 imoeq3_0 vex emoeq3_0 emoeq3_1 emoeq3_2 eueq3 vtoclg fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 eumo syl fmoeq3_3 cvv wcel wn fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o wi fmoeq3_2 wal fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 weu fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 wmo fmoeq3_3 cvv wcel wn fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o wi fmoeq3_2 fmoeq3_3 cvv wcel wn fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa wo wo fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa wo wo fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_3 cvv wcel wn fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa wo fmoeq3_3 cvv wcel wn fmoeq3_2 sup_set_class fmoeq3_3 wceq fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq fmoeq3_3 cvv wcel fmoeq3_3 cvv wcel wn fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq fmoeq3_2 sup_set_class fmoeq3_3 wceq fmoeq3_2 sup_set_class cvv wcel fmoeq3_3 cvv wcel fmoeq3_2 vex fmoeq3_2 sup_set_class fmoeq3_3 cvv eleq1 mpbii fmoeq3_3 cvv wcel fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq pm2.21 syl5 anim2d orim1d fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa 3orass fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa 3orass 3imtr4g alrimiv fmoeq3_0 fmoeq3_1 fmoeq3_2 imoeq3_0 sup_set_class fmoeq3_4 fmoeq3_5 imoeq3_0 vex emoeq3_0 emoeq3_1 emoeq3_2 eueq3 fmoeq3_0 fmoeq3_2 sup_set_class fmoeq3_3 wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_0 fmoeq3_2 sup_set_class imoeq3_0 sup_set_class wceq wa fmoeq3_0 fmoeq3_1 wo wn fmoeq3_2 sup_set_class fmoeq3_4 wceq wa fmoeq3_1 fmoeq3_2 sup_set_class fmoeq3_5 wceq wa w3o fmoeq3_2 euimmo ee10 pm2.61i $.
$}
$( "At most one" remains true after substitution.  (Contributed by NM,
       9-Mar-1995.) $)
${
	$d x y A $.
	fmosub_0 $f wff ph $.
	fmosub_1 $f set x $.
	fmosub_2 $f set y $.
	fmosub_3 $f class A $.
	emosub_0 $e |- E* x ph $.
	mosub $p |- E* x E. y ( y = A /\ ph ) $= fmosub_2 sup_set_class fmosub_3 wceq fmosub_2 wmo fmosub_0 fmosub_1 wmo fmosub_2 wal fmosub_2 sup_set_class fmosub_3 wceq fmosub_0 wa fmosub_2 wex fmosub_1 wmo fmosub_2 fmosub_3 moeq fmosub_0 fmosub_1 wmo fmosub_2 emosub_0 ax-gen fmosub_2 sup_set_class fmosub_3 wceq fmosub_0 fmosub_2 fmosub_1 moexexv mp2an $.
$}
$( Theorem for inferring "at most one."  (Contributed by NM,
       17-Oct-1996.) $)
${
	$d x y A $.
	$d y ph $.
	imo2icl_0 $f set y $.
	fmo2icl_0 $f wff ph $.
	fmo2icl_1 $f set x $.
	fmo2icl_2 $f class A $.
	mo2icl $p |- ( A. x ( ph -> x = A ) -> E* x ph ) $= fmo2icl_2 cvv wcel fmo2icl_0 fmo2icl_1 sup_set_class fmo2icl_2 wceq wi fmo2icl_1 wal fmo2icl_0 fmo2icl_1 wmo wi fmo2icl_0 fmo2icl_1 sup_set_class imo2icl_0 sup_set_class wceq wi fmo2icl_1 wal fmo2icl_0 fmo2icl_1 wmo wi fmo2icl_0 fmo2icl_1 sup_set_class fmo2icl_2 wceq wi fmo2icl_1 wal fmo2icl_0 fmo2icl_1 wmo wi imo2icl_0 fmo2icl_2 cvv imo2icl_0 sup_set_class fmo2icl_2 wceq fmo2icl_0 fmo2icl_1 sup_set_class imo2icl_0 sup_set_class wceq wi fmo2icl_1 wal fmo2icl_0 fmo2icl_1 sup_set_class fmo2icl_2 wceq wi fmo2icl_1 wal fmo2icl_0 fmo2icl_1 wmo imo2icl_0 sup_set_class fmo2icl_2 wceq fmo2icl_0 fmo2icl_1 sup_set_class imo2icl_0 sup_set_class wceq wi fmo2icl_0 fmo2icl_1 sup_set_class fmo2icl_2 wceq wi fmo2icl_1 imo2icl_0 sup_set_class fmo2icl_2 wceq fmo2icl_1 sup_set_class imo2icl_0 sup_set_class wceq fmo2icl_1 sup_set_class fmo2icl_2 wceq fmo2icl_0 imo2icl_0 sup_set_class fmo2icl_2 fmo2icl_1 sup_set_class eqeq2 imbi2d albidv imbi1d fmo2icl_0 fmo2icl_1 sup_set_class imo2icl_0 sup_set_class wceq wi fmo2icl_1 wal fmo2icl_0 fmo2icl_1 sup_set_class imo2icl_0 sup_set_class wceq wi fmo2icl_1 wal imo2icl_0 wex fmo2icl_0 fmo2icl_1 wmo fmo2icl_0 fmo2icl_1 sup_set_class imo2icl_0 sup_set_class wceq wi fmo2icl_1 wal imo2icl_0 19.8a fmo2icl_0 fmo2icl_1 imo2icl_0 fmo2icl_0 imo2icl_0 nfv mo2 sylibr vtoclg fmo2icl_2 cvv wcel wn fmo2icl_0 fmo2icl_1 sup_set_class fmo2icl_2 wceq wi fmo2icl_1 wal fmo2icl_0 wn fmo2icl_1 wal fmo2icl_0 fmo2icl_1 wmo fmo2icl_2 cvv wcel wn fmo2icl_0 fmo2icl_1 sup_set_class fmo2icl_2 wceq wi fmo2icl_0 wn fmo2icl_1 fmo2icl_0 fmo2icl_1 sup_set_class fmo2icl_2 wceq wi fmo2icl_0 fmo2icl_2 cvv wcel fmo2icl_1 sup_set_class fmo2icl_2 wceq fmo2icl_2 cvv wcel fmo2icl_0 fmo2icl_1 sup_set_class fmo2icl_2 wceq fmo2icl_1 sup_set_class cvv wcel fmo2icl_2 cvv wcel fmo2icl_1 vex fmo2icl_1 sup_set_class fmo2icl_2 cvv eleq1 mpbii imim2i con3rr3 alimdv fmo2icl_0 wn fmo2icl_1 wal fmo2icl_0 fmo2icl_1 wex wn fmo2icl_0 fmo2icl_1 wmo fmo2icl_0 fmo2icl_1 alnex fmo2icl_0 fmo2icl_1 wex fmo2icl_0 fmo2icl_1 wmo fmo2icl_0 fmo2icl_1 exmo ori sylbi syl6 pm2.61i $.
$}
$( Consequence of "at most one."  (Contributed by NM, 2-Jan-2015.) $)
${
	$d x y A $.
	$d y ph $.
	$d x y ps $.
	imob2_0 $f set y $.
	fmob2_0 $f wff ph $.
	fmob2_1 $f wff ps $.
	fmob2_2 $f set x $.
	fmob2_3 $f class A $.
	fmob2_4 $f class B $.
	emob2_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	mob2 $p |- ( ( A e. B /\ E* x ph /\ ph ) -> ( x = A <-> ps ) ) $= fmob2_3 fmob2_4 wcel fmob2_0 fmob2_2 wmo fmob2_0 w3a fmob2_2 sup_set_class fmob2_3 wceq fmob2_1 fmob2_3 fmob2_4 wcel fmob2_0 fmob2_2 wmo fmob2_0 w3a fmob2_0 fmob2_2 sup_set_class fmob2_3 wceq fmob2_1 fmob2_3 fmob2_4 wcel fmob2_0 fmob2_2 wmo fmob2_0 simp3 emob2_0 syl5ibcom fmob2_3 fmob2_4 wcel fmob2_0 fmob2_2 wmo fmob2_0 fmob2_1 fmob2_2 sup_set_class fmob2_3 wceq wi fmob2_3 fmob2_4 wcel fmob2_0 fmob2_2 wmo wa fmob2_0 fmob2_1 fmob2_2 sup_set_class fmob2_3 wceq fmob2_3 fmob2_4 wcel fmob2_0 fmob2_2 wmo fmob2_0 fmob2_1 wa fmob2_2 sup_set_class fmob2_3 wceq wi fmob2_0 fmob2_2 wmo fmob2_0 fmob2_0 fmob2_2 imob2_0 wsb wa fmob2_2 sup_set_class imob2_0 sup_set_class wceq wi imob2_0 wal fmob2_3 fmob2_4 wcel fmob2_0 fmob2_1 wa fmob2_2 sup_set_class fmob2_3 wceq wi fmob2_0 fmob2_2 wmo fmob2_0 fmob2_0 fmob2_2 imob2_0 wsb wa fmob2_2 sup_set_class imob2_0 sup_set_class wceq wi imob2_0 wal fmob2_2 wal fmob2_0 fmob2_0 fmob2_2 imob2_0 wsb wa fmob2_2 sup_set_class imob2_0 sup_set_class wceq wi imob2_0 wal fmob2_0 fmob2_0 fmob2_2 imob2_0 wsb fmob2_2 imob2_0 fmob2_0 fmob2_2 imob2_0 nfs1v fmob2_0 fmob2_2 imob2_0 sbequ12 mo4f fmob2_0 fmob2_0 fmob2_2 imob2_0 wsb wa fmob2_2 sup_set_class imob2_0 sup_set_class wceq wi imob2_0 wal fmob2_2 sp sylbi fmob2_0 fmob2_0 fmob2_2 imob2_0 wsb wa fmob2_2 sup_set_class imob2_0 sup_set_class wceq wi fmob2_0 fmob2_1 wa fmob2_2 sup_set_class fmob2_3 wceq wi imob2_0 fmob2_3 fmob2_4 imob2_0 sup_set_class fmob2_3 wceq fmob2_0 fmob2_0 fmob2_2 imob2_0 wsb wa fmob2_0 fmob2_1 wa fmob2_2 sup_set_class imob2_0 sup_set_class wceq fmob2_2 sup_set_class fmob2_3 wceq imob2_0 sup_set_class fmob2_3 wceq fmob2_0 fmob2_2 imob2_0 wsb fmob2_1 fmob2_0 fmob2_0 fmob2_1 fmob2_2 imob2_0 fmob2_3 fmob2_1 fmob2_2 nfv emob2_0 sbhypf anbi2d imob2_0 sup_set_class fmob2_3 fmob2_2 sup_set_class eqeq2 imbi12d spcgv syl5 imp exp3a 3impia impbid $.
$}
$( Consequence of "at most one."  (Contributed by NM, 29-Jun-2008.) $)
${
	$d x A $.
	$d x ps $.
	fmoi2_0 $f wff ph $.
	fmoi2_1 $f wff ps $.
	fmoi2_2 $f set x $.
	fmoi2_3 $f class A $.
	fmoi2_4 $f class B $.
	emoi2_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	moi2 $p |- ( ( ( A e. B /\ E* x ph ) /\ ( ph /\ ps ) ) -> x = A ) $= fmoi2_3 fmoi2_4 wcel fmoi2_0 fmoi2_2 wmo wa fmoi2_0 fmoi2_1 fmoi2_2 sup_set_class fmoi2_3 wceq fmoi2_3 fmoi2_4 wcel fmoi2_0 fmoi2_2 wmo wa fmoi2_0 wa fmoi2_2 sup_set_class fmoi2_3 wceq fmoi2_1 fmoi2_3 fmoi2_4 wcel fmoi2_0 fmoi2_2 wmo fmoi2_0 fmoi2_2 sup_set_class fmoi2_3 wceq fmoi2_1 wb fmoi2_0 fmoi2_1 fmoi2_2 fmoi2_3 fmoi2_4 emoi2_0 mob2 3expa biimprd impr $.
$}
$( Equality implied by "at most one."  (Contributed by NM, 18-Feb-2006.) $)
${
	$d x A $.
	$d x B $.
	$d x ch $.
	$d x ps $.
	fmob_0 $f wff ph $.
	fmob_1 $f wff ps $.
	fmob_2 $f wff ch $.
	fmob_3 $f set x $.
	fmob_4 $f class A $.
	fmob_5 $f class B $.
	fmob_6 $f class C $.
	fmob_7 $f class D $.
	emob_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	emob_1 $e |- ( x = B -> ( ph <-> ch ) ) $.
	mob $p |- ( ( ( A e. C /\ B e. D ) /\ E* x ph /\ ps ) -> ( A = B <-> ch ) ) $= fmob_4 fmob_6 wcel fmob_5 fmob_7 wcel wa fmob_0 fmob_3 wmo fmob_1 fmob_4 fmob_5 wceq fmob_2 wb fmob_4 fmob_6 wcel fmob_5 fmob_7 wcel fmob_0 fmob_3 wmo fmob_1 wa fmob_4 fmob_5 wceq fmob_2 wb wi fmob_5 fmob_7 wcel fmob_0 fmob_3 wmo fmob_1 wa fmob_4 fmob_6 wcel fmob_4 fmob_5 wceq fmob_2 wb fmob_5 fmob_7 wcel fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_1 wa fmob_4 fmob_6 wcel fmob_4 fmob_5 wceq fmob_2 wb wi wi fmob_5 fmob_7 elex fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_1 fmob_4 fmob_6 wcel fmob_4 fmob_5 wceq fmob_2 wb wi fmob_4 fmob_6 wcel fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_1 w3a fmob_4 fmob_5 wceq fmob_2 wb fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_0 w3a fmob_3 sup_set_class fmob_5 wceq fmob_2 wb wi fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_1 w3a fmob_4 fmob_5 wceq fmob_2 wb wi fmob_3 fmob_4 fmob_6 fmob_3 fmob_4 nfcv fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_1 w3a fmob_4 fmob_5 wceq fmob_2 wb fmob_3 fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_1 fmob_3 fmob_5 cvv wcel fmob_3 nfv fmob_0 fmob_3 nfmo1 fmob_1 fmob_3 nfv nf3an fmob_4 fmob_5 wceq fmob_2 wb fmob_3 nfv nfim fmob_3 sup_set_class fmob_4 wceq fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_0 w3a fmob_5 cvv wcel fmob_0 fmob_3 wmo fmob_1 w3a fmob_3 sup_set_class fmob_5 wceq fmob_2 wb fmob_4 fmob_5 wceq fmob_2 wb fmob_3 sup_set_class fmob_4 wceq fmob_0 fmob_1 fmob_5 cvv wcel fmob_0 fmob_3 wmo emob_0 3anbi3d fmob_3 sup_set_class fmob_4 wceq fmob_3 sup_set_class fmob_5 wceq fmob_4 fmob_5 wceq fmob_2 fmob_3 sup_set_class fmob_4 fmob_5 eqeq1 bibi1d imbi12d fmob_0 fmob_2 fmob_3 fmob_5 cvv emob_1 mob2 vtoclgf com12 3expib syl com3r imp 3impib $.
$}
$( Equality implied by "at most one."  (Contributed by NM, 18-Feb-2006.) $)
${
	$d x A $.
	$d x B $.
	$d x ch $.
	$d x ps $.
	fmoi_0 $f wff ph $.
	fmoi_1 $f wff ps $.
	fmoi_2 $f wff ch $.
	fmoi_3 $f set x $.
	fmoi_4 $f class A $.
	fmoi_5 $f class B $.
	fmoi_6 $f class C $.
	fmoi_7 $f class D $.
	emoi_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	emoi_1 $e |- ( x = B -> ( ph <-> ch ) ) $.
	moi $p |- ( ( ( A e. C /\ B e. D ) /\ E* x ph /\ ( ps /\ ch ) ) -> A = B ) $= fmoi_4 fmoi_6 wcel fmoi_5 fmoi_7 wcel wa fmoi_0 fmoi_3 wmo fmoi_1 fmoi_2 wa fmoi_4 fmoi_5 wceq fmoi_4 fmoi_6 wcel fmoi_5 fmoi_7 wcel wa fmoi_0 fmoi_3 wmo wa fmoi_1 fmoi_2 fmoi_4 fmoi_5 wceq fmoi_4 fmoi_6 wcel fmoi_5 fmoi_7 wcel wa fmoi_0 fmoi_3 wmo fmoi_1 fmoi_2 fmoi_4 fmoi_5 wceq wi fmoi_4 fmoi_6 wcel fmoi_5 fmoi_7 wcel wa fmoi_0 fmoi_3 wmo fmoi_1 w3a fmoi_4 fmoi_5 wceq fmoi_2 fmoi_0 fmoi_1 fmoi_2 fmoi_3 fmoi_4 fmoi_5 fmoi_6 fmoi_7 emoi_0 emoi_1 mob biimprd 3expia imp3a 3impia $.
$}
$( Derive membership from uniqueness.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
${
	$d B x $.
	$d A x $.
	$d ps x $.
	fmorex_0 $f wff ph $.
	fmorex_1 $f wff ps $.
	fmorex_2 $f set x $.
	fmorex_3 $f class A $.
	fmorex_4 $f class B $.
	emorex_0 $e |- B e. _V $.
	emorex_1 $e |- ( x = B -> ( ph <-> ps ) ) $.
	morex $p |- ( ( E. x e. A ph /\ E* x ph ) -> ( ps -> B e. A ) ) $= fmorex_0 fmorex_2 wmo fmorex_0 fmorex_2 fmorex_3 wrex fmorex_1 fmorex_4 fmorex_3 wcel wi fmorex_0 fmorex_2 fmorex_3 wrex fmorex_0 fmorex_2 wmo fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wa fmorex_2 wex fmorex_1 fmorex_4 fmorex_3 wcel wi fmorex_0 fmorex_2 fmorex_3 wrex fmorex_2 sup_set_class fmorex_3 wcel fmorex_0 wa fmorex_2 wex fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wa fmorex_2 wex fmorex_0 fmorex_2 fmorex_3 df-rex fmorex_2 sup_set_class fmorex_3 wcel fmorex_0 fmorex_2 exancom bitri fmorex_0 fmorex_2 wmo fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wa fmorex_2 wex wa fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wi fmorex_2 wal fmorex_1 fmorex_4 fmorex_3 wcel wi fmorex_0 fmorex_2 wmo fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wa fmorex_2 wex wa fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wi fmorex_2 fmorex_0 fmorex_2 wmo fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wa fmorex_2 wex fmorex_2 fmorex_0 fmorex_2 nfmo1 fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wa fmorex_2 nfe1 nfan fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel fmorex_2 mopick alrimi fmorex_0 fmorex_2 sup_set_class fmorex_3 wcel wi fmorex_1 fmorex_4 fmorex_3 wcel wi fmorex_2 fmorex_4 emorex_0 fmorex_2 sup_set_class fmorex_4 wceq fmorex_0 fmorex_1 fmorex_2 sup_set_class fmorex_3 wcel fmorex_4 fmorex_3 wcel emorex_1 fmorex_2 sup_set_class fmorex_4 fmorex_3 eleq1 imbi12d spcv syl sylan2b ancoms $.
$}
$( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       14-Nov-2004.) $)
${
	$d x ph $.
	$d x A $.
	feuxfr2_0 $f wff ph $.
	feuxfr2_1 $f set x $.
	feuxfr2_2 $f set y $.
	feuxfr2_3 $f class A $.
	eeuxfr2_0 $e |- A e. _V $.
	eeuxfr2_1 $e |- E* y x = A $.
	euxfr2 $p |- ( E! x E. y ( x = A /\ ph ) <-> E! y ph ) $= feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_2 wex feuxfr2_1 weu feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 wex feuxfr2_2 weu feuxfr2_0 feuxfr2_2 weu feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_2 wex feuxfr2_1 weu feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 wex feuxfr2_2 weu feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_2 wmo feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_2 wex feuxfr2_1 weu feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 wex feuxfr2_2 weu wi feuxfr2_1 feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 feuxfr2_2 2euswap feuxfr2_0 feuxfr2_1 sup_set_class feuxfr2_3 wceq wa feuxfr2_2 wmo feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_2 wmo feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 feuxfr2_2 eeuxfr2_1 moani feuxfr2_0 feuxfr2_1 sup_set_class feuxfr2_3 wceq wa feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_2 feuxfr2_0 feuxfr2_1 sup_set_class feuxfr2_3 wceq ancom mobii mpbi mpg feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 wmo feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 wex feuxfr2_2 weu feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_2 wex feuxfr2_1 weu wi feuxfr2_2 feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_2 feuxfr2_1 2euswap feuxfr2_0 feuxfr2_1 sup_set_class feuxfr2_3 wceq wa feuxfr2_1 wmo feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 wmo feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 feuxfr2_1 feuxfr2_1 feuxfr2_3 moeq moani feuxfr2_0 feuxfr2_1 sup_set_class feuxfr2_3 wceq wa feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 feuxfr2_0 feuxfr2_1 sup_set_class feuxfr2_3 wceq ancom mobii mpbi mpg impbii feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 wa feuxfr2_1 wex feuxfr2_0 feuxfr2_2 feuxfr2_0 feuxfr2_0 feuxfr2_1 feuxfr2_3 eeuxfr2_0 feuxfr2_1 sup_set_class feuxfr2_3 wceq feuxfr2_0 biidd ceqsexv eubii bitri $.
$}
$( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       14-Nov-2004.) $)
${
	$d x ps $.
	$d y ph $.
	$d x A $.
	feuxfr_0 $f wff ph $.
	feuxfr_1 $f wff ps $.
	feuxfr_2 $f set x $.
	feuxfr_3 $f set y $.
	feuxfr_4 $f class A $.
	eeuxfr_0 $e |- A e. _V $.
	eeuxfr_1 $e |- E! y x = A $.
	eeuxfr_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	euxfr $p |- ( E! x ph <-> E! y ps ) $= feuxfr_0 feuxfr_2 weu feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_1 wa feuxfr_3 wex feuxfr_2 weu feuxfr_1 feuxfr_3 weu feuxfr_0 feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_1 wa feuxfr_3 wex feuxfr_2 feuxfr_0 feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_3 wex feuxfr_0 wa feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_0 wa feuxfr_3 wex feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_1 wa feuxfr_3 wex feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_3 wex feuxfr_0 feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_3 weu feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_3 wex eeuxfr_1 feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_3 euex ax-mp biantrur feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_0 feuxfr_3 19.41v feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_0 wa feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_1 wa feuxfr_3 feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_0 feuxfr_1 eeuxfr_2 pm5.32i exbii 3bitr2i eubii feuxfr_1 feuxfr_2 feuxfr_3 feuxfr_4 eeuxfr_0 feuxfr_2 sup_set_class feuxfr_4 wceq feuxfr_3 eeuxfr_1 eumoi euxfr2 bitri $.
$}
$( Existential uniqueness via an indirect equality.  (Contributed by NM,
       11-Oct-2010.) $)
${
	$d y z w ph $.
	$d x z ps $.
	$d y z w A $.
	$d x z B $.
	$d x y w $.
	ieuind_0 $f set w $.
	feuind_0 $f wff ph $.
	feuind_1 $f wff ps $.
	feuind_2 $f set x $.
	feuind_3 $f set y $.
	feuind_4 $f set z $.
	feuind_5 $f class A $.
	feuind_6 $f class B $.
	eeuind_0 $e |- B e. _V $.
	eeuind_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	eeuind_2 $e |- ( x = y -> A = B ) $.
	euind $p |- ( ( A. x A. y ( ( ph /\ ps ) -> A = B ) /\ E. x ph ) -> E! z A. x ( ph -> z = A ) ) $= feuind_0 feuind_1 wa feuind_5 feuind_6 wceq wi feuind_3 wal feuind_2 wal feuind_0 feuind_2 wex wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_4 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_0 ieuind_0 sup_set_class feuind_5 wceq wi feuind_2 wal wa feuind_4 sup_set_class ieuind_0 sup_set_class wceq wi ieuind_0 wal feuind_4 wal feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_4 weu feuind_0 feuind_1 wa feuind_5 feuind_6 wceq wi feuind_3 wal feuind_2 wal feuind_0 feuind_2 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_4 wex feuind_0 feuind_2 wex feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_4 wex feuind_0 feuind_1 wa feuind_5 feuind_6 wceq wi feuind_3 wal feuind_2 wal feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_4 wex feuind_0 feuind_2 wex feuind_1 feuind_3 wex feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_4 wex feuind_0 feuind_1 feuind_2 feuind_3 eeuind_1 cbvexv feuind_1 feuind_3 wex feuind_4 sup_set_class feuind_6 wceq feuind_4 wex feuind_1 wa feuind_3 wex feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_4 wex feuind_1 feuind_4 sup_set_class feuind_6 wceq feuind_4 wex feuind_1 wa feuind_3 feuind_4 sup_set_class feuind_6 wceq feuind_4 wex feuind_1 feuind_4 feuind_6 eeuind_0 isseti biantrur exbii feuind_4 sup_set_class feuind_6 wceq feuind_4 wex feuind_1 wa feuind_3 wex feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_4 wex feuind_3 wex feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_4 wex feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_4 wex feuind_4 sup_set_class feuind_6 wceq feuind_4 wex feuind_1 wa feuind_3 feuind_4 sup_set_class feuind_6 wceq feuind_1 feuind_4 19.41v exbii feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 feuind_4 excom bitr3i bitri bitri feuind_0 feuind_1 wa feuind_5 feuind_6 wceq wi feuind_3 wal feuind_2 wal feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_4 feuind_0 feuind_1 wa feuind_5 feuind_6 wceq wi feuind_3 wal feuind_2 wal feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_3 wal feuind_2 wal feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal wi feuind_0 feuind_1 wa feuind_5 feuind_6 wceq wi feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_2 feuind_3 feuind_0 feuind_1 wa feuind_5 feuind_6 wceq wi feuind_0 feuind_1 wa feuind_4 sup_set_class feuind_5 wceq feuind_4 sup_set_class feuind_6 wceq wb wi feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_5 feuind_6 wceq feuind_4 sup_set_class feuind_5 wceq feuind_4 sup_set_class feuind_6 wceq wb feuind_0 feuind_1 wa feuind_5 feuind_6 feuind_4 sup_set_class eqeq2 imim2i feuind_0 feuind_1 wa feuind_4 sup_set_class feuind_5 wceq feuind_4 sup_set_class feuind_6 wceq wb wi feuind_0 feuind_1 wa feuind_4 sup_set_class feuind_6 wceq feuind_4 sup_set_class feuind_5 wceq wi wi feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_4 sup_set_class feuind_5 wceq feuind_4 sup_set_class feuind_6 wceq wb feuind_4 sup_set_class feuind_6 wceq feuind_4 sup_set_class feuind_5 wceq wi feuind_0 feuind_1 wa feuind_4 sup_set_class feuind_5 wceq feuind_4 sup_set_class feuind_6 wceq bi2 imim2i feuind_0 feuind_1 wa feuind_4 sup_set_class feuind_6 wceq wa feuind_4 sup_set_class feuind_5 wceq wi feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 wa feuind_4 sup_set_class feuind_5 wceq wi feuind_0 feuind_1 wa feuind_4 sup_set_class feuind_6 wceq feuind_4 sup_set_class feuind_5 wceq wi wi feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_0 feuind_1 wa feuind_4 sup_set_class feuind_6 wceq wa feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 wa feuind_4 sup_set_class feuind_5 wceq feuind_0 feuind_1 feuind_4 sup_set_class feuind_6 wceq an31 imbi1i feuind_0 feuind_1 wa feuind_4 sup_set_class feuind_6 wceq feuind_4 sup_set_class feuind_5 wceq impexp feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq impexp 3bitr3i sylib syl 2alimi feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_3 wal feuind_2 wal feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_2 wal feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal wi feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_3 wal feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi wi feuind_2 feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_3 19.23v albii feuind_4 sup_set_class feuind_6 wceq feuind_1 wa feuind_3 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 19.21v bitri sylib eximdv syl5bi imp feuind_0 feuind_2 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_0 ieuind_0 sup_set_class feuind_5 wceq wi feuind_2 wal wa feuind_4 sup_set_class ieuind_0 sup_set_class wceq wi ieuind_0 wal feuind_4 wal feuind_0 feuind_1 wa feuind_5 feuind_6 wceq wi feuind_3 wal feuind_2 wal feuind_0 feuind_2 wex feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_0 ieuind_0 sup_set_class feuind_5 wceq wi feuind_2 wal wa feuind_4 sup_set_class ieuind_0 sup_set_class wceq wi feuind_4 ieuind_0 feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_0 ieuind_0 sup_set_class feuind_5 wceq wi feuind_2 wal wa feuind_0 feuind_4 sup_set_class ieuind_0 sup_set_class wceq wi feuind_2 wal feuind_0 feuind_2 wex feuind_4 sup_set_class ieuind_0 sup_set_class wceq feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_0 ieuind_0 sup_set_class feuind_5 wceq wi feuind_0 feuind_4 sup_set_class ieuind_0 sup_set_class wceq wi feuind_2 feuind_0 feuind_0 feuind_0 wa feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_0 ieuind_0 sup_set_class feuind_5 wceq wi wa feuind_4 sup_set_class feuind_5 wceq ieuind_0 sup_set_class feuind_5 wceq wa feuind_4 sup_set_class ieuind_0 sup_set_class wceq feuind_0 feuind_0 feuind_0 wa feuind_0 pm4.24 biimpi feuind_0 feuind_4 sup_set_class feuind_5 wceq feuind_0 ieuind_0 sup_set_class feuind_5 wceq prth feuind_4 sup_set_class ieuind_0 sup_set_class feuind_5 eqtr3 syl56 alanimi feuind_0 feuind_4 sup_set_class ieuind_0 sup_set_class wceq wi feuind_2 wal feuind_0 feuind_2 wex feuind_4 sup_set_class ieuind_0 sup_set_class wceq feuind_0 feuind_4 sup_set_class ieuind_0 sup_set_class wceq wi feuind_2 wal feuind_0 feuind_2 wex feuind_4 sup_set_class ieuind_0 sup_set_class wceq wi feuind_0 feuind_4 sup_set_class ieuind_0 sup_set_class wceq feuind_2 19.23v biimpi com12 syl5 alrimivv adantl feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_0 ieuind_0 sup_set_class feuind_5 wceq wi feuind_2 wal feuind_4 ieuind_0 feuind_4 sup_set_class ieuind_0 sup_set_class wceq feuind_0 feuind_4 sup_set_class feuind_5 wceq wi feuind_0 ieuind_0 sup_set_class feuind_5 wceq wi feuind_2 feuind_4 sup_set_class ieuind_0 sup_set_class wceq feuind_4 sup_set_class feuind_5 wceq ieuind_0 sup_set_class feuind_5 wceq feuind_0 feuind_4 sup_set_class ieuind_0 sup_set_class feuind_5 eqeq1 imbi2d albidv eu4 sylanbrc $.
$}
$( A way to express restricted uniqueness.  (Contributed by NM,
       22-Nov-1994.) $)
${
	$d x y A $.
	$d x y $.
	$d y ph $.
	freu2_0 $f wff ph $.
	freu2_1 $f set x $.
	freu2_2 $f set y $.
	freu2_3 $f class A $.
	reu2 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $= freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 weu freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 wex freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 wal freu2_1 wal wa freu2_0 freu2_1 freu2_3 wreu freu2_0 freu2_1 freu2_3 wrex freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 wral freu2_1 freu2_3 wral wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_2 nfv eu2 freu2_0 freu2_1 freu2_3 df-reu freu2_0 freu2_1 freu2_3 wrex freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 wex freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 wral freu2_1 freu2_3 wral freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 wal freu2_1 wal freu2_0 freu2_1 freu2_3 df-rex freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 wral freu2_1 freu2_3 wral freu2_1 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 wral wi freu2_1 wal freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 wal freu2_1 wal freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 wral freu2_1 freu2_3 df-ral freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 wal freu2_1 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 wral wi freu2_1 freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi wi wi freu2_2 wal freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi wi freu2_2 wal wi freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 wal freu2_1 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 wral wi freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi wi freu2_2 19.21v freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi wi wi freu2_2 freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel wa freu2_0 freu2_0 freu2_1 freu2_2 wsb wa wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel wa freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi wi freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi wi wi freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel wa freu2_0 freu2_0 freu2_1 freu2_2 wsb wa wa freu2_1 sup_set_class freu2_2 sup_set_class wceq freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_1 freu2_2 wsb wa wa freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel wa freu2_0 freu2_0 freu2_1 freu2_2 wsb wa wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 freu2_2 wsb freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_1 sup_set_class freu2_3 wcel freu2_0 wa freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_1 freu2_2 wsb wa freu2_1 freu2_2 freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_1 freu2_2 wsb freu2_1 freu2_2 sup_set_class freu2_3 wcel freu2_1 nfv freu2_0 freu2_1 freu2_2 nfs1v nfan freu2_1 sup_set_class freu2_2 sup_set_class wceq freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb freu2_1 sup_set_class freu2_2 sup_set_class freu2_3 eleq1 freu2_0 freu2_1 freu2_2 sbequ12 anbi12d sbie anbi2i freu2_1 sup_set_class freu2_3 wcel freu2_0 freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_1 freu2_2 wsb an4 bitri imbi1i freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel wa freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq impexp freu2_1 sup_set_class freu2_3 wcel freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi impexp 3bitri albii freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 wral freu2_2 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi wi freu2_2 wal freu2_1 sup_set_class freu2_3 wcel freu2_0 freu2_0 freu2_1 freu2_2 wsb wa freu2_1 sup_set_class freu2_2 sup_set_class wceq wi freu2_2 freu2_3 df-ral imbi2i 3bitr4i albii bitr4i anbi12i 3bitr4i $.
$}
$( A way to express restricted uniqueness.  (Contributed by NM,
       20-Oct-2006.) $)
${
	$d x y A $.
	$d x y $.
	$d y ph $.
	freu6_0 $f wff ph $.
	freu6_1 $f set x $.
	freu6_2 $f set y $.
	freu6_3 $f class A $.
	reu6 $p |- ( E! x e. A ph <-> E. y e. A A. x e. A ( ph <-> x = y ) ) $= freu6_0 freu6_1 freu6_3 wreu freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 weu freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_3 wral freu6_2 freu6_3 wrex freu6_0 freu6_1 freu6_3 df-reu freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 wal freu6_2 wex freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_3 wral wa freu6_2 wex freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 weu freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_3 wral freu6_2 freu6_3 wrex freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 wal freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_3 wral wa freu6_2 freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi wa freu6_1 wal freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 wal wa freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 wal freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_3 wral wa freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 19.28v freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 wal freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi wa freu6_1 wal freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi wa freu6_1 freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 wal freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_2 sup_set_class freu6_3 wcel freu6_1 freu6_2 freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 freu6_2 wsb wa freu6_2 sup_set_class freu6_2 sup_set_class wceq wb freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 freu6_2 wsb wa freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_2 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_0 freu6_1 freu6_2 wsb freu6_1 sup_set_class freu6_2 sup_set_class freu6_3 eleq1 freu6_0 freu6_1 freu6_2 sbequ12 anbi12d freu6_1 sup_set_class freu6_2 sup_set_class freu6_2 sup_set_class eqeq1 bibi12d freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 freu6_2 wsb wa freu6_2 sup_set_class freu6_2 sup_set_class wceq wb freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 freu6_2 wsb wa freu6_2 sup_set_class freu6_3 wcel freu6_2 sup_set_class freu6_2 sup_set_class wceq freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 freu6_2 wsb wa freu6_2 sup_set_class eqid tbt freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 freu6_2 wsb simpl sylbir syl6bi spimv freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 sup_set_class freu6_3 wcel wa freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq bi1 expdimp freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_0 wi freu6_1 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_0 freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq bi2 freu6_1 sup_set_class freu6_3 wcel freu6_0 simpr syl6 adantr impbid ex sps jca a5i freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi wa freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi wa freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wi freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wi freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq bi1 imim2i imp3a adantl freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi wa freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi wa freu6_1 sup_set_class freu6_2 sup_set_class wceq wa freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi wa freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel wi freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_2 sup_set_class freu6_3 freu6_1 sup_set_class eleq1a adantr imp freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 wi freu6_2 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_1 sup_set_class freu6_3 wcel freu6_0 wi freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 sup_set_class freu6_3 wcel freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_0 freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 sup_set_class freu6_2 sup_set_class wceq freu6_0 wi freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq bi2 imim2i com23 imp adantll jcai ex impbid alimi impbii freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_3 wral freu6_1 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb wi freu6_1 wal freu6_2 sup_set_class freu6_3 wcel freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_3 df-ral anbi2i 3bitr4i exbii freu6_1 sup_set_class freu6_3 wcel freu6_0 wa freu6_1 freu6_2 df-eu freu6_0 freu6_1 sup_set_class freu6_2 sup_set_class wceq wb freu6_1 freu6_3 wral freu6_2 freu6_3 df-rex 3bitr4i bitri $.
$}
$( A way to express restricted uniqueness.  (Contributed by NM,
       24-Oct-2006.) $)
${
	$d x y A $.
	$d x y $.
	$d y ph $.
	freu3_0 $f wff ph $.
	freu3_1 $f set x $.
	freu3_2 $f set y $.
	freu3_3 $f class A $.
	reu3 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ E. y e. A A. x e. A ( ph -> x = y ) ) ) $= freu3_0 freu3_1 freu3_3 wreu freu3_0 freu3_1 freu3_3 wrex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 freu3_3 wrex wa freu3_0 freu3_1 freu3_3 wreu freu3_0 freu3_1 freu3_3 wrex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 freu3_3 wrex freu3_0 freu3_1 freu3_3 reurex freu3_0 freu3_1 freu3_3 wreu freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wb freu3_1 freu3_3 wral freu3_2 freu3_3 wrex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 freu3_3 wrex freu3_0 freu3_1 freu3_2 freu3_3 reu6 freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wb freu3_1 freu3_3 wral freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 freu3_3 freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wb freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq bi1 ralimi reximi sylbi jca freu3_0 freu3_1 freu3_3 wrex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 freu3_3 wrex wa freu3_0 freu3_1 freu3_3 wrex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 wex wa freu3_0 freu3_1 freu3_3 wreu freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 freu3_3 wrex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 wex freu3_0 freu3_1 freu3_3 wrex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 freu3_3 rexex anim2i freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 weu freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 wex freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 wal freu3_2 wex wa freu3_0 freu3_1 freu3_3 wreu freu3_0 freu3_1 freu3_3 wrex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 wex wa freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 freu3_2 freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_2 nfv eu3 freu3_0 freu3_1 freu3_3 df-reu freu3_0 freu3_1 freu3_3 wrex freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 wex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_2 wex freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 wal freu3_2 wex freu3_0 freu3_1 freu3_3 df-rex freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 wal freu3_2 freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 wral freu3_1 sup_set_class freu3_3 wcel freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi wi freu3_1 wal freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 wal freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 freu3_3 df-ral freu3_1 sup_set_class freu3_3 wcel freu3_0 wa freu3_1 sup_set_class freu3_2 sup_set_class wceq wi freu3_1 sup_set_class freu3_3 wcel freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq wi wi freu3_1 freu3_1 sup_set_class freu3_3 wcel freu3_0 freu3_1 sup_set_class freu3_2 sup_set_class wceq impexp albii bitr4i exbii anbi12i 3bitr4i sylibr impbii $.
$}
$( A condition which implies existential uniqueness.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d y ph $.
	ireu6i_0 $f set y $.
	freu6i_0 $f wff ph $.
	freu6i_1 $f set x $.
	freu6i_2 $f class A $.
	freu6i_3 $f class B $.
	reu6i $p |- ( ( B e. A /\ A. x e. A ( ph <-> x = B ) ) -> E! x e. A ph ) $= freu6i_3 freu6i_2 wcel freu6i_0 freu6i_1 sup_set_class freu6i_3 wceq wb freu6i_1 freu6i_2 wral wa freu6i_0 freu6i_1 sup_set_class ireu6i_0 sup_set_class wceq wb freu6i_1 freu6i_2 wral ireu6i_0 freu6i_2 wrex freu6i_0 freu6i_1 freu6i_2 wreu freu6i_0 freu6i_1 sup_set_class ireu6i_0 sup_set_class wceq wb freu6i_1 freu6i_2 wral freu6i_0 freu6i_1 sup_set_class freu6i_3 wceq wb freu6i_1 freu6i_2 wral ireu6i_0 freu6i_3 freu6i_2 ireu6i_0 sup_set_class freu6i_3 wceq freu6i_0 freu6i_1 sup_set_class ireu6i_0 sup_set_class wceq wb freu6i_0 freu6i_1 sup_set_class freu6i_3 wceq wb freu6i_1 freu6i_2 ireu6i_0 sup_set_class freu6i_3 wceq freu6i_1 sup_set_class ireu6i_0 sup_set_class wceq freu6i_1 sup_set_class freu6i_3 wceq freu6i_0 ireu6i_0 sup_set_class freu6i_3 freu6i_1 sup_set_class eqeq2 bibi2d ralbidv rspcev freu6i_0 freu6i_1 ireu6i_0 freu6i_2 reu6 sylibr $.
$}
$( A condition which implies existential uniqueness.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	feqreu_0 $f wff ph $.
	feqreu_1 $f wff ps $.
	feqreu_2 $f set x $.
	feqreu_3 $f class A $.
	feqreu_4 $f class B $.
	eeqreu_0 $e |- ( x = B -> ( ph <-> ps ) ) $.
	eqreu $p |- ( ( B e. A /\ ps /\ A. x e. A ( ph -> x = B ) ) -> E! x e. A ph ) $= feqreu_4 feqreu_3 wcel feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wi feqreu_2 feqreu_3 wral feqreu_1 feqreu_0 feqreu_2 feqreu_3 wreu feqreu_4 feqreu_3 wcel feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wi feqreu_2 feqreu_3 wral feqreu_1 feqreu_0 feqreu_2 feqreu_3 wreu feqreu_4 feqreu_3 wcel feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wi feqreu_2 feqreu_3 wral feqreu_1 wa feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wb feqreu_2 feqreu_3 wral feqreu_0 feqreu_2 feqreu_3 wreu feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wb feqreu_2 feqreu_3 wral feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wi feqreu_2 feqreu_3 wral feqreu_2 sup_set_class feqreu_4 wceq feqreu_0 wi feqreu_2 feqreu_3 wral wa feqreu_4 feqreu_3 wcel feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wi feqreu_2 feqreu_3 wral feqreu_1 wa feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq feqreu_2 feqreu_3 ralbiim feqreu_4 feqreu_3 wcel feqreu_2 sup_set_class feqreu_4 wceq feqreu_0 wi feqreu_2 feqreu_3 wral feqreu_1 feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wi feqreu_2 feqreu_3 wral feqreu_0 feqreu_1 feqreu_2 feqreu_4 feqreu_3 eeqreu_0 ceqsralv anbi2d syl5bb feqreu_4 feqreu_3 wcel feqreu_0 feqreu_2 sup_set_class feqreu_4 wceq wb feqreu_2 feqreu_3 wral feqreu_0 feqreu_2 feqreu_3 wreu feqreu_0 feqreu_2 feqreu_3 feqreu_4 reu6i ex sylbird 3impib 3com23 $.
$}
$( Restricted "at most one" using implicit substitution.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by NM, 16-Jun-2017.) $)
${
	$d x y A $.
	$d y ph $.
	$d x ps $.
	frmo4_0 $f wff ph $.
	frmo4_1 $f wff ps $.
	frmo4_2 $f set x $.
	frmo4_3 $f set y $.
	frmo4_4 $f class A $.
	ermo4_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	rmo4 $p |- ( E* x e. A ph <-> A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) $= frmo4_0 frmo4_2 frmo4_4 wrmo frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_2 wmo frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 frmo4_4 wral frmo4_2 frmo4_4 wral frmo4_0 frmo4_2 frmo4_4 df-rmo frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 wa wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 wal frmo4_2 wal frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 frmo4_4 wral wi frmo4_2 wal frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_2 wmo frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 frmo4_4 wral frmo4_2 frmo4_4 wral frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 wa wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 wal frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 frmo4_4 wral wi frmo4_2 frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 wa wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 wal frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi wi wi frmo4_3 wal frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi wi frmo4_3 frmo4_4 wral frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 frmo4_4 wral wi frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 wa wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi wi wi frmo4_3 frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 wa wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel wa frmo4_0 frmo4_1 wa wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel wa frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi wi frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi wi wi frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 wa wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel wa frmo4_0 frmo4_1 wa wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 wa wa frmo4_2 sup_set_class frmo4_4 wcel frmo4_3 sup_set_class frmo4_4 wcel wa frmo4_0 frmo4_1 wa wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel wa frmo4_0 frmo4_1 wa wa frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 an4 frmo4_2 sup_set_class frmo4_4 wcel frmo4_3 sup_set_class frmo4_4 wcel wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel wa frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_4 wcel frmo4_3 sup_set_class frmo4_4 wcel ancom anbi1i bitri imbi1i frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel wa frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq impexp frmo4_3 sup_set_class frmo4_4 wcel frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi impexp 3bitri albii frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi wi frmo4_3 frmo4_4 df-ral frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 frmo4_4 r19.21v 3bitr2i albii frmo4_2 sup_set_class frmo4_4 wcel frmo4_0 wa frmo4_3 sup_set_class frmo4_4 wcel frmo4_1 wa frmo4_2 frmo4_3 frmo4_2 sup_set_class frmo4_3 sup_set_class wceq frmo4_2 sup_set_class frmo4_4 wcel frmo4_3 sup_set_class frmo4_4 wcel frmo4_0 frmo4_1 frmo4_2 sup_set_class frmo4_3 sup_set_class frmo4_4 eleq1 ermo4_0 anbi12d mo4 frmo4_0 frmo4_1 wa frmo4_2 sup_set_class frmo4_3 sup_set_class wceq wi frmo4_3 frmo4_4 wral frmo4_2 frmo4_4 df-ral 3bitr4i bitri $.
$}
$( Restricted uniqueness using implicit substitution.  (Contributed by NM,
       23-Nov-1994.) $)
${
	$d x y A $.
	$d y ph $.
	$d x ps $.
	freu4_0 $f wff ph $.
	freu4_1 $f wff ps $.
	freu4_2 $f set x $.
	freu4_3 $f set y $.
	freu4_4 $f class A $.
	ereu4_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	reu4 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) ) $= freu4_0 freu4_2 freu4_4 wreu freu4_0 freu4_2 freu4_4 wrex freu4_0 freu4_2 freu4_4 wrmo wa freu4_0 freu4_2 freu4_4 wrex freu4_0 freu4_1 wa freu4_2 sup_set_class freu4_3 sup_set_class wceq wi freu4_3 freu4_4 wral freu4_2 freu4_4 wral wa freu4_0 freu4_2 freu4_4 reu5 freu4_0 freu4_2 freu4_4 wrmo freu4_0 freu4_1 wa freu4_2 sup_set_class freu4_3 sup_set_class wceq wi freu4_3 freu4_4 wral freu4_2 freu4_4 wral freu4_0 freu4_2 freu4_4 wrex freu4_0 freu4_1 freu4_2 freu4_3 freu4_4 ereu4_0 rmo4 anbi2i bitri $.
$}
$( Restricted uniqueness using implicit substitution.  (Contributed by NM,
       24-Oct-2006.) $)
${
	$d x y z A $.
	$d y z ph $.
	$d x z ps $.
	ireu7_0 $f set z $.
	freu7_0 $f wff ph $.
	freu7_1 $f wff ps $.
	freu7_2 $f set x $.
	freu7_3 $f set y $.
	freu7_4 $f class A $.
	ereu7_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	reu7 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ E. x e. A A. y e. A ( ps -> x = y ) ) ) $= freu7_0 freu7_2 freu7_4 wreu freu7_0 freu7_2 freu7_4 wrex freu7_0 freu7_2 sup_set_class ireu7_0 sup_set_class wceq wi freu7_2 freu7_4 wral ireu7_0 freu7_4 wrex wa freu7_0 freu7_2 freu7_4 wrex freu7_1 freu7_2 sup_set_class freu7_3 sup_set_class wceq wi freu7_3 freu7_4 wral freu7_2 freu7_4 wrex wa freu7_0 freu7_2 ireu7_0 freu7_4 reu3 freu7_0 freu7_2 sup_set_class ireu7_0 sup_set_class wceq wi freu7_2 freu7_4 wral ireu7_0 freu7_4 wrex freu7_1 freu7_2 sup_set_class freu7_3 sup_set_class wceq wi freu7_3 freu7_4 wral freu7_2 freu7_4 wrex freu7_0 freu7_2 freu7_4 wrex freu7_0 freu7_2 sup_set_class ireu7_0 sup_set_class wceq wi freu7_2 freu7_4 wral ireu7_0 freu7_4 wrex freu7_1 ireu7_0 sup_set_class freu7_3 sup_set_class wceq wi freu7_3 freu7_4 wral ireu7_0 freu7_4 wrex freu7_1 freu7_2 sup_set_class freu7_3 sup_set_class wceq wi freu7_3 freu7_4 wral freu7_2 freu7_4 wrex freu7_0 freu7_2 sup_set_class ireu7_0 sup_set_class wceq wi freu7_2 freu7_4 wral freu7_1 ireu7_0 sup_set_class freu7_3 sup_set_class wceq wi freu7_3 freu7_4 wral ireu7_0 freu7_4 freu7_0 freu7_2 sup_set_class ireu7_0 sup_set_class wceq wi freu7_1 ireu7_0 sup_set_class freu7_3 sup_set_class wceq wi freu7_2 freu7_3 freu7_4 freu7_2 sup_set_class freu7_3 sup_set_class wceq freu7_0 freu7_1 freu7_2 sup_set_class ireu7_0 sup_set_class wceq ireu7_0 sup_set_class freu7_3 sup_set_class wceq ereu7_0 freu7_2 sup_set_class freu7_3 sup_set_class wceq freu7_2 sup_set_class ireu7_0 sup_set_class wceq freu7_3 sup_set_class ireu7_0 sup_set_class wceq ireu7_0 sup_set_class freu7_3 sup_set_class wceq freu7_2 sup_set_class freu7_3 sup_set_class ireu7_0 sup_set_class eqeq1 freu7_3 sup_set_class ireu7_0 sup_set_class eqcom syl6bb imbi12d cbvralv rexbii freu7_1 ireu7_0 sup_set_class freu7_3 sup_set_class wceq wi freu7_3 freu7_4 wral freu7_1 freu7_2 sup_set_class freu7_3 sup_set_class wceq wi freu7_3 freu7_4 wral ireu7_0 freu7_2 freu7_4 ireu7_0 sup_set_class freu7_2 sup_set_class wceq freu7_1 ireu7_0 sup_set_class freu7_3 sup_set_class wceq wi freu7_1 freu7_2 sup_set_class freu7_3 sup_set_class wceq wi freu7_3 freu7_4 ireu7_0 sup_set_class freu7_2 sup_set_class wceq ireu7_0 sup_set_class freu7_3 sup_set_class wceq freu7_2 sup_set_class freu7_3 sup_set_class wceq freu7_1 ireu7_0 sup_set_class freu7_2 sup_set_class freu7_3 sup_set_class eqeq1 imbi2d ralbidv cbvrexv bitri anbi2i bitri $.
$}
$( Restricted uniqueness using implicit substitution.  (Contributed by NM,
       24-Oct-2006.) $)
${
	$d x y A $.
	$d y ph $.
	$d x ps $.
	freu8_0 $f wff ph $.
	freu8_1 $f wff ps $.
	freu8_2 $f set x $.
	freu8_3 $f set y $.
	freu8_4 $f class A $.
	ereu8_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	reu8 $p |- ( E! x e. A ph <-> E. x e. A ( ph /\ A. y e. A ( ps -> x = y ) ) ) $= freu8_0 freu8_2 freu8_4 wreu freu8_1 freu8_3 freu8_4 wreu freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wb freu8_3 freu8_4 wral freu8_2 freu8_4 wrex freu8_0 freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral wa freu8_2 freu8_4 wrex freu8_0 freu8_1 freu8_2 freu8_3 freu8_4 ereu8_0 cbvreuv freu8_1 freu8_3 freu8_2 freu8_4 reu6 freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wb freu8_3 freu8_4 wral freu8_0 freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral wa freu8_2 freu8_4 freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wb freu8_3 freu8_4 wral freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi wa freu8_3 freu8_4 wral freu8_2 sup_set_class freu8_4 wcel freu8_0 freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral wa freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wb freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi wa freu8_3 freu8_4 freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq dfbi2 ralbii freu8_2 sup_set_class freu8_4 wcel freu8_0 freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral wa freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 freu8_4 wral freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi freu8_3 freu8_4 wral wa freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi wa freu8_3 freu8_4 wral freu8_0 freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral wa freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral freu8_0 wa freu8_2 sup_set_class freu8_4 wcel freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 freu8_4 wral freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi freu8_3 freu8_4 wral wa freu8_0 freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral ancom freu8_2 sup_set_class freu8_4 wcel freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 freu8_4 wral freu8_0 freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi freu8_3 freu8_4 wral freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_3 freu8_4 wral freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 freu8_4 wral wb freu8_2 sup_set_class freu8_4 wcel freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class wceq wi freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 freu8_4 freu8_2 sup_set_class freu8_3 sup_set_class wceq freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 freu8_2 freu8_3 equcom imbi2i ralbii a1i freu8_2 sup_set_class freu8_4 wcel freu8_0 freu8_2 sup_set_class freu8_4 wcel freu8_0 wi freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi freu8_3 freu8_4 wral freu8_2 sup_set_class freu8_4 wcel freu8_0 biimt freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi freu8_3 freu8_4 wral freu8_3 sup_set_class freu8_4 wcel freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi wi freu8_3 wal freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_3 sup_set_class freu8_4 wcel freu8_1 wi wi freu8_3 wal freu8_2 sup_set_class freu8_4 wcel freu8_0 wi freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi freu8_3 freu8_4 df-ral freu8_3 sup_set_class freu8_4 wcel freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi wi freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_3 sup_set_class freu8_4 wcel freu8_1 wi wi freu8_3 freu8_3 sup_set_class freu8_4 wcel freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 bi2.04 albii freu8_3 sup_set_class freu8_4 wcel freu8_1 wi freu8_2 sup_set_class freu8_4 wcel freu8_0 wi freu8_3 freu8_2 sup_set_class freu8_2 vex freu8_3 sup_set_class freu8_4 wcel freu8_1 wi freu8_2 sup_set_class freu8_4 wcel freu8_0 wi wb freu8_2 freu8_3 freu8_2 sup_set_class freu8_3 sup_set_class wceq freu8_2 sup_set_class freu8_4 wcel freu8_0 wi freu8_3 sup_set_class freu8_4 wcel freu8_1 wi freu8_2 sup_set_class freu8_3 sup_set_class wceq freu8_2 sup_set_class freu8_4 wcel freu8_3 sup_set_class freu8_4 wcel freu8_0 freu8_1 freu8_2 sup_set_class freu8_3 sup_set_class freu8_4 eleq1 ereu8_0 imbi12d bicomd equcoms ceqsalv 3bitrri syl6bb anbi12d syl5bb freu8_1 freu8_3 sup_set_class freu8_2 sup_set_class wceq wi freu8_3 sup_set_class freu8_2 sup_set_class wceq freu8_1 wi freu8_3 freu8_4 r19.26 syl6rbbr syl5bb rexbiia 3bitri $.
$}
$( Equality has existential uniqueness.  (Contributed by Mario Carneiro,
       1-Sep-2015.) $)
${
	$d x A $.
	$d x B $.
	freueq_0 $f set x $.
	freueq_1 $f class A $.
	freueq_2 $f class B $.
	reueq $p |- ( B e. A <-> E! x e. A x = B ) $= freueq_2 freueq_1 wcel freueq_0 sup_set_class freueq_2 wceq freueq_0 freueq_1 wrex freueq_0 sup_set_class freueq_2 wceq freueq_0 freueq_1 wreu freueq_0 freueq_2 freueq_1 risset freueq_0 sup_set_class freueq_2 wceq freueq_0 freueq_1 wreu freueq_0 sup_set_class freueq_2 wceq freueq_0 freueq_1 wrex freueq_0 sup_set_class freueq_2 wceq freueq_0 freueq_1 wrmo freueq_0 sup_set_class freueq_2 wceq freueq_0 wmo freueq_0 sup_set_class freueq_2 wceq freueq_0 freueq_1 wrmo freueq_0 freueq_2 moeq freueq_0 sup_set_class freueq_2 wceq freueq_0 freueq_1 mormo ax-mp freueq_0 sup_set_class freueq_2 wceq freueq_0 freueq_1 reu5 mpbiran2 bitr4i $.
$}
$( Restricted "at most one" still holds when a conjunct is added.
     (Contributed by NM, 16-Jun-2017.) $)
${
	frmoan_0 $f wff ph $.
	frmoan_1 $f wff ps $.
	frmoan_2 $f set x $.
	frmoan_3 $f class A $.
	rmoan $p |- ( E* x e. A ph -> E* x e. A ( ps /\ ph ) ) $= frmoan_2 sup_set_class frmoan_3 wcel frmoan_0 wa frmoan_2 wmo frmoan_2 sup_set_class frmoan_3 wcel frmoan_1 frmoan_0 wa wa frmoan_2 wmo frmoan_0 frmoan_2 frmoan_3 wrmo frmoan_1 frmoan_0 wa frmoan_2 frmoan_3 wrmo frmoan_2 sup_set_class frmoan_3 wcel frmoan_0 wa frmoan_2 wmo frmoan_1 frmoan_2 sup_set_class frmoan_3 wcel frmoan_0 wa wa frmoan_2 wmo frmoan_2 sup_set_class frmoan_3 wcel frmoan_1 frmoan_0 wa wa frmoan_2 wmo frmoan_2 sup_set_class frmoan_3 wcel frmoan_0 wa frmoan_1 frmoan_2 moan frmoan_1 frmoan_2 sup_set_class frmoan_3 wcel frmoan_0 wa wa frmoan_2 sup_set_class frmoan_3 wcel frmoan_1 frmoan_0 wa wa frmoan_2 frmoan_1 frmoan_2 sup_set_class frmoan_3 wcel frmoan_0 an12 mobii sylib frmoan_0 frmoan_2 frmoan_3 df-rmo frmoan_1 frmoan_0 wa frmoan_2 frmoan_3 df-rmo 3imtr4i $.
$}
$( Restricted "at most one" is preserved through implication (note wff
     reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
${
	frmoim_0 $f wff ph $.
	frmoim_1 $f wff ps $.
	frmoim_2 $f set x $.
	frmoim_3 $f class A $.
	rmoim $p |- ( A. x e. A ( ph -> ps ) -> ( E* x e. A ps -> E* x e. A ph ) ) $= frmoim_0 frmoim_1 wi frmoim_2 frmoim_3 wral frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 wa frmoim_2 sup_set_class frmoim_3 wcel frmoim_1 wa wi frmoim_2 wal frmoim_1 frmoim_2 frmoim_3 wrmo frmoim_0 frmoim_2 frmoim_3 wrmo wi frmoim_0 frmoim_1 wi frmoim_2 frmoim_3 wral frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 frmoim_1 wi wi frmoim_2 wal frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 wa frmoim_2 sup_set_class frmoim_3 wcel frmoim_1 wa wi frmoim_2 wal frmoim_0 frmoim_1 wi frmoim_2 frmoim_3 df-ral frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 frmoim_1 wi wi frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 wa frmoim_2 sup_set_class frmoim_3 wcel frmoim_1 wa wi frmoim_2 frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 frmoim_1 imdistan albii bitri frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 wa frmoim_2 sup_set_class frmoim_3 wcel frmoim_1 wa wi frmoim_2 wal frmoim_2 sup_set_class frmoim_3 wcel frmoim_1 wa frmoim_2 wmo frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 wa frmoim_2 wmo frmoim_1 frmoim_2 frmoim_3 wrmo frmoim_0 frmoim_2 frmoim_3 wrmo frmoim_2 sup_set_class frmoim_3 wcel frmoim_0 wa frmoim_2 sup_set_class frmoim_3 wcel frmoim_1 wa frmoim_2 moim frmoim_1 frmoim_2 frmoim_3 df-rmo frmoim_0 frmoim_2 frmoim_3 df-rmo 3imtr4g sylbi $.
$}
$( Restricted "at most one" is preserved through implication (note wff
       reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
${
	frmoimia_0 $f wff ph $.
	frmoimia_1 $f wff ps $.
	frmoimia_2 $f set x $.
	frmoimia_3 $f class A $.
	ermoimia_0 $e |- ( x e. A -> ( ph -> ps ) ) $.
	rmoimia $p |- ( E* x e. A ps -> E* x e. A ph ) $= frmoimia_0 frmoimia_1 wi frmoimia_1 frmoimia_2 frmoimia_3 wrmo frmoimia_0 frmoimia_2 frmoimia_3 wrmo wi frmoimia_2 frmoimia_3 frmoimia_0 frmoimia_1 frmoimia_2 frmoimia_3 rmoim ermoimia_0 mprg $.
$}
$( Restricted "at most one" is preserved through implication (note wff
       reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
${
	frmoimi2_0 $f wff ph $.
	frmoimi2_1 $f wff ps $.
	frmoimi2_2 $f set x $.
	frmoimi2_3 $f class A $.
	frmoimi2_4 $f class B $.
	ermoimi2_0 $e |- A. x ( ( x e. A /\ ph ) -> ( x e. B /\ ps ) ) $.
	rmoimi2 $p |- ( E* x e. B ps -> E* x e. A ph ) $= frmoimi2_2 sup_set_class frmoimi2_4 wcel frmoimi2_1 wa frmoimi2_2 wmo frmoimi2_2 sup_set_class frmoimi2_3 wcel frmoimi2_0 wa frmoimi2_2 wmo frmoimi2_1 frmoimi2_2 frmoimi2_4 wrmo frmoimi2_0 frmoimi2_2 frmoimi2_3 wrmo frmoimi2_2 sup_set_class frmoimi2_3 wcel frmoimi2_0 wa frmoimi2_2 sup_set_class frmoimi2_4 wcel frmoimi2_1 wa wi frmoimi2_2 wal frmoimi2_2 sup_set_class frmoimi2_4 wcel frmoimi2_1 wa frmoimi2_2 wmo frmoimi2_2 sup_set_class frmoimi2_3 wcel frmoimi2_0 wa frmoimi2_2 wmo wi ermoimi2_0 frmoimi2_2 sup_set_class frmoimi2_3 wcel frmoimi2_0 wa frmoimi2_2 sup_set_class frmoimi2_4 wcel frmoimi2_1 wa frmoimi2_2 moim ax-mp frmoimi2_1 frmoimi2_2 frmoimi2_4 df-rmo frmoimi2_0 frmoimi2_2 frmoimi2_3 df-rmo 3imtr4i $.
$}
$( A condition allowing swap of uniqueness and existential quantifiers.
       (Contributed by Thierry Arnoux, 7-Apr-2017.)  (Revised by NM,
       16-Jun-2017.) $)
${
	$d x y A $.
	$d x B $.
	f2reuswap_0 $f wff ph $.
	f2reuswap_1 $f set x $.
	f2reuswap_2 $f set y $.
	f2reuswap_3 $f class A $.
	f2reuswap_4 $f class B $.
	2reuswap $p |- ( A. x e. A E* y e. B ph -> ( E! x e. A E. y e. B ph -> E! y e. B E. x e. A ph ) ) $= f2reuswap_0 f2reuswap_2 f2reuswap_4 wrmo f2reuswap_1 f2reuswap_3 wral f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_2 wmo f2reuswap_1 f2reuswap_3 wral f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex f2reuswap_1 f2reuswap_3 wreu f2reuswap_0 f2reuswap_1 f2reuswap_3 wrex f2reuswap_2 f2reuswap_4 wreu wi f2reuswap_0 f2reuswap_2 f2reuswap_4 wrmo f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_2 wmo f2reuswap_1 f2reuswap_3 f2reuswap_0 f2reuswap_2 f2reuswap_4 df-rmo ralbii f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_2 wmo f2reuswap_1 f2reuswap_3 wral f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 wmo f2reuswap_1 wal f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex f2reuswap_1 f2reuswap_3 wreu f2reuswap_0 f2reuswap_1 f2reuswap_3 wrex f2reuswap_2 f2reuswap_4 wreu wi f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_2 wmo f2reuswap_1 f2reuswap_3 wral f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_2 wmo wi f2reuswap_1 wal f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 wmo f2reuswap_1 wal f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_2 wmo f2reuswap_1 f2reuswap_3 df-ral f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 wmo f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_2 wmo wi f2reuswap_1 f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_2 moanimv albii bitr4i f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 wmo f2reuswap_1 wal f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 wex f2reuswap_1 weu f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_1 wex f2reuswap_2 weu f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex f2reuswap_1 f2reuswap_3 wreu f2reuswap_0 f2reuswap_1 f2reuswap_3 wrex f2reuswap_2 f2reuswap_4 wreu f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_1 f2reuswap_2 2euswap f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex f2reuswap_1 f2reuswap_3 wreu f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex wa f2reuswap_1 weu f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 wex f2reuswap_1 weu f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex f2reuswap_1 f2reuswap_3 df-reu f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex wa f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 wex f2reuswap_1 f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex wa f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 wa wa f2reuswap_2 wex f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 wex f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 f2reuswap_2 f2reuswap_4 wrex wa f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 wa f2reuswap_2 f2reuswap_4 wrex f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 wa wa f2reuswap_2 wex f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 f2reuswap_2 f2reuswap_4 r19.42v f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 wa f2reuswap_2 f2reuswap_4 df-rex bitr3i f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 wa wa f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_2 f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_0 an12 exbii bitri eubii bitri f2reuswap_0 f2reuswap_1 f2reuswap_3 wrex f2reuswap_2 f2reuswap_4 wreu f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 f2reuswap_1 f2reuswap_3 wrex wa f2reuswap_2 weu f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_1 wex f2reuswap_2 weu f2reuswap_0 f2reuswap_1 f2reuswap_3 wrex f2reuswap_2 f2reuswap_4 df-reu f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 f2reuswap_1 f2reuswap_3 wrex wa f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_1 wex f2reuswap_2 f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 f2reuswap_1 f2reuswap_3 wrex wa f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_1 f2reuswap_3 wrex f2reuswap_1 sup_set_class f2reuswap_3 wcel f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa wa f2reuswap_1 wex f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 f2reuswap_1 f2reuswap_3 r19.42v f2reuswap_2 sup_set_class f2reuswap_4 wcel f2reuswap_0 wa f2reuswap_1 f2reuswap_3 df-rex bitr3i eubii bitri 3imtr4g sylbi sylbi $.
$}
$( Existential uniqueness via an indirect equality.  (Contributed by NM,
       16-Oct-2010.) $)
${
	$d w y z A $.
	$d x z B $.
	$d w x y z C $.
	$d w y z ph $.
	$d x z ps $.
	ireuind_0 $f set w $.
	freuind_0 $f wff ph $.
	freuind_1 $f wff ps $.
	freuind_2 $f set x $.
	freuind_3 $f set y $.
	freuind_4 $f set z $.
	freuind_5 $f class A $.
	freuind_6 $f class B $.
	freuind_7 $f class C $.
	ereuind_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	ereuind_1 $e |- ( x = y -> A = B ) $.
	reuind $p |- ( ( A. x A. y ( ( ( A e. C /\ ph ) /\ ( B e. C /\ ps ) ) -> A = B ) /\ E. x ( A e. C /\ ph ) ) -> E! z e. C A. x ( ( A e. C /\ ph ) -> z = A ) ) $= freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_3 wal freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_4 freuind_7 wrex freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi freuind_2 wal wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi ireuind_0 freuind_7 wral freuind_4 freuind_7 wral freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_4 freuind_7 wreu freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_3 wal freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_4 freuind_7 wrex freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex freuind_4 freuind_7 wrex freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_3 wal freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_4 freuind_7 wrex freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_6 freuind_7 wcel freuind_1 wa freuind_3 wex freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex freuind_4 freuind_7 wrex freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa freuind_2 freuind_3 freuind_2 sup_set_class freuind_3 sup_set_class wceq freuind_5 freuind_7 wcel freuind_6 freuind_7 wcel freuind_0 freuind_1 freuind_2 sup_set_class freuind_3 sup_set_class wceq freuind_5 freuind_6 freuind_7 ereuind_1 eleq1d ereuind_0 anbi12d cbvexv freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_4 freuind_7 wrex freuind_3 wex freuind_4 sup_set_class freuind_6 wceq freuind_4 freuind_7 wrex freuind_1 wa freuind_3 wex freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex freuind_4 freuind_7 wrex freuind_6 freuind_7 wcel freuind_1 wa freuind_3 wex freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_4 freuind_7 wrex freuind_4 sup_set_class freuind_6 wceq freuind_4 freuind_7 wrex freuind_1 wa freuind_3 freuind_4 sup_set_class freuind_6 wceq freuind_1 freuind_4 freuind_7 r19.41v exbii freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_4 freuind_3 freuind_7 rexcom4 freuind_6 freuind_7 wcel freuind_1 wa freuind_4 sup_set_class freuind_6 wceq freuind_4 freuind_7 wrex freuind_1 wa freuind_3 freuind_6 freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_4 freuind_7 wrex freuind_1 freuind_4 freuind_6 freuind_7 risset anbi1i exbii 3bitr4ri bitri freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_3 wal freuind_2 wal freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_4 freuind_7 freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_3 wal freuind_2 wal freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_3 wal freuind_2 wal freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_3 wal freuind_2 wal freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal wi freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_2 freuind_3 freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_5 wceq freuind_4 sup_set_class freuind_6 wceq wb wi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_5 freuind_6 wceq freuind_4 sup_set_class freuind_5 wceq freuind_4 sup_set_class freuind_6 wceq wb freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 freuind_4 sup_set_class eqeq2 imim2i freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_5 wceq freuind_4 sup_set_class freuind_6 wceq wb wi freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_6 wceq freuind_4 sup_set_class freuind_5 wceq wi wi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_4 sup_set_class freuind_5 wceq freuind_4 sup_set_class freuind_6 wceq wb freuind_4 sup_set_class freuind_6 wceq freuind_4 sup_set_class freuind_5 wceq wi freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_5 wceq freuind_4 sup_set_class freuind_6 wceq bi2 imim2i freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_6 wceq wa freuind_4 sup_set_class freuind_5 wceq wi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa wa freuind_4 sup_set_class freuind_5 wceq wi freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_6 wceq freuind_4 sup_set_class freuind_5 wceq wi wi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_6 wceq wa freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa wa freuind_4 sup_set_class freuind_5 wceq freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa freuind_4 sup_set_class freuind_6 wceq an31 imbi1i freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_6 wceq freuind_4 sup_set_class freuind_5 wceq impexp freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq impexp 3bitr3i sylib syl 2alimi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_3 wal freuind_2 wal freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_2 wal freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal wi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_3 wal freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_2 freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_3 wal freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_3 wex freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi wi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_3 19.23v freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_3 wex freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_3 wex freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa wa freuind_3 wex freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex wa freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa wa freuind_3 freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 wa wa freuind_6 freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa wa freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa wa freuind_4 sup_set_class freuind_6 wceq freuind_6 freuind_7 wcel freuind_1 an12 freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_4 sup_set_class freuind_7 wcel freuind_6 freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_4 sup_set_class freuind_7 wcel freuind_6 freuind_7 wcel wb freuind_1 freuind_4 sup_set_class freuind_6 freuind_7 eleq1 adantr pm5.32ri bitr4i exbii freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 19.42v bitri imbi1i bitri albii freuind_4 sup_set_class freuind_7 wcel freuind_4 sup_set_class freuind_6 wceq freuind_1 wa freuind_3 wex wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 19.21v bitri sylib exp3a reximdvai syl5bi imp freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi freuind_2 wal wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi ireuind_0 freuind_7 wral freuind_4 freuind_7 wral freuind_5 freuind_7 wcel freuind_0 wa freuind_6 freuind_7 wcel freuind_1 wa wa freuind_5 freuind_6 wceq wi freuind_3 wal freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi freuind_2 wal wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi freuind_4 ireuind_0 freuind_7 freuind_7 freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi freuind_2 wal wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi freuind_4 sup_set_class freuind_7 wcel ireuind_0 sup_set_class freuind_7 wcel wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi freuind_2 wal wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_4 sup_set_class ireuind_0 sup_set_class wceq freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi freuind_2 freuind_5 freuind_7 wcel freuind_0 wa freuind_5 freuind_7 wcel freuind_0 wa freuind_5 freuind_7 wcel freuind_0 wa wa freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi wa freuind_4 sup_set_class freuind_5 wceq ireuind_0 sup_set_class freuind_5 wceq wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq freuind_5 freuind_7 wcel freuind_0 wa freuind_5 freuind_7 wcel freuind_0 wa freuind_5 freuind_7 wcel freuind_0 wa wa freuind_5 freuind_7 wcel freuind_0 wa pm4.24 biimpi freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq prth freuind_4 sup_set_class ireuind_0 sup_set_class freuind_5 eqtr3 syl56 alanimi freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_4 sup_set_class ireuind_0 sup_set_class wceq freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa freuind_2 wex freuind_4 sup_set_class ireuind_0 sup_set_class wceq wi freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class ireuind_0 sup_set_class wceq freuind_2 19.23v biimpi com12 syl5 a1d ralrimivv adantl freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi freuind_2 wal freuind_4 ireuind_0 freuind_7 freuind_4 sup_set_class ireuind_0 sup_set_class wceq freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class freuind_5 wceq wi freuind_5 freuind_7 wcel freuind_0 wa ireuind_0 sup_set_class freuind_5 wceq wi freuind_2 freuind_4 sup_set_class ireuind_0 sup_set_class wceq freuind_4 sup_set_class freuind_5 wceq ireuind_0 sup_set_class freuind_5 wceq freuind_5 freuind_7 wcel freuind_0 wa freuind_4 sup_set_class ireuind_0 sup_set_class freuind_5 eqeq1 imbi2d albidv reu4 sylanbrc $.
$}
$( Double restricted quantification with "at most one," analogous to
       ~ 2moex .  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
${
	$d y A $.
	$d x B $.
	$d x y $.
	f2rmorex_0 $f wff ph $.
	f2rmorex_1 $f set x $.
	f2rmorex_2 $f set y $.
	f2rmorex_3 $f class A $.
	f2rmorex_4 $f class B $.
	2rmorex $p |- ( E* x e. A E. y e. B ph -> A. y e. B E* x e. A ph ) $= f2rmorex_0 f2rmorex_2 f2rmorex_4 wrex f2rmorex_1 f2rmorex_3 wrmo f2rmorex_0 f2rmorex_1 f2rmorex_3 wrmo f2rmorex_2 f2rmorex_4 f2rmorex_0 f2rmorex_2 f2rmorex_4 wrex f2rmorex_2 f2rmorex_1 f2rmorex_3 f2rmorex_2 f2rmorex_3 nfcv f2rmorex_0 f2rmorex_2 f2rmorex_4 nfre1 nfrmo f2rmorex_2 sup_set_class f2rmorex_4 wcel f2rmorex_0 f2rmorex_2 f2rmorex_4 wrex f2rmorex_1 f2rmorex_3 wrmo f2rmorex_0 f2rmorex_1 f2rmorex_3 wrmo f2rmorex_2 sup_set_class f2rmorex_4 wcel f2rmorex_0 f2rmorex_0 f2rmorex_2 f2rmorex_4 wrex wi f2rmorex_1 f2rmorex_3 wral f2rmorex_0 f2rmorex_2 f2rmorex_4 wrex f2rmorex_1 f2rmorex_3 wrmo f2rmorex_0 f2rmorex_1 f2rmorex_3 wrmo wi f2rmorex_2 sup_set_class f2rmorex_4 wcel f2rmorex_0 f2rmorex_0 f2rmorex_2 f2rmorex_4 wrex wi f2rmorex_1 f2rmorex_3 f2rmorex_2 sup_set_class f2rmorex_4 wcel f2rmorex_0 f2rmorex_0 f2rmorex_2 f2rmorex_4 wrex f2rmorex_0 f2rmorex_2 f2rmorex_4 rspe ex ralrimivw f2rmorex_0 f2rmorex_0 f2rmorex_2 f2rmorex_4 wrex f2rmorex_1 f2rmorex_3 rmoim syl com12 ralrimi $.
$}
$( Lemma for ~ 2reu5 .  Note that ` E! x e. A E! y e. B ph ` does not mean
       "there is exactly one ` x ` in ` A ` and exactly one ` y ` in ` B ` such
       that ` ph ` holds;" see comment for ~ 2eu5 .  (Contributed by Alexander
       van der Vekens, 17-Jun-2017.) $)
${
	$d y A $.
	$d x B $.
	$d x y $.
	f2reu5lem1_0 $f wff ph $.
	f2reu5lem1_1 $f set x $.
	f2reu5lem1_2 $f set y $.
	f2reu5lem1_3 $f class A $.
	f2reu5lem1_4 $f class B $.
	2reu5lem1 $p |- ( E! x e. A E! y e. B ph <-> E! x E! y ( x e. A /\ y e. B /\ ph ) ) $= f2reu5lem1_0 f2reu5lem1_2 f2reu5lem1_4 wreu f2reu5lem1_1 f2reu5lem1_3 wreu f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 weu f2reu5lem1_1 f2reu5lem1_3 wreu f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 w3a f2reu5lem1_2 weu f2reu5lem1_1 weu f2reu5lem1_0 f2reu5lem1_2 f2reu5lem1_4 wreu f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 weu f2reu5lem1_1 f2reu5lem1_3 f2reu5lem1_0 f2reu5lem1_2 f2reu5lem1_4 df-reu reubii f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 weu f2reu5lem1_1 f2reu5lem1_3 wreu f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 weu wa f2reu5lem1_1 weu f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 w3a f2reu5lem1_2 weu f2reu5lem1_1 weu f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 weu f2reu5lem1_1 f2reu5lem1_3 df-reu f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 weu wa f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 w3a f2reu5lem1_2 weu f2reu5lem1_1 f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 weu wa f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa wa f2reu5lem1_2 weu f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 w3a f2reu5lem1_2 weu f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa wa f2reu5lem1_2 weu f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 weu wa f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa f2reu5lem1_2 euanv bicomi f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa wa f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 w3a f2reu5lem1_2 f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 w3a f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 wa wa f2reu5lem1_1 sup_set_class f2reu5lem1_3 wcel f2reu5lem1_2 sup_set_class f2reu5lem1_4 wcel f2reu5lem1_0 3anass bicomi eubii bitri eubii bitri bitri $.
$}
$( Lemma for ~ 2reu5 .  (Contributed by Alexander van der Vekens,
       17-Jun-2017.) $)
${
	$d y A $.
	$d x B $.
	$d x y $.
	f2reu5lem2_0 $f wff ph $.
	f2reu5lem2_1 $f set x $.
	f2reu5lem2_2 $f set y $.
	f2reu5lem2_3 $f class A $.
	f2reu5lem2_4 $f class B $.
	2reu5lem2 $p |- ( A. x e. A E* y e. B ph <-> A. x E* y ( x e. A /\ y e. B /\ ph ) ) $= f2reu5lem2_0 f2reu5lem2_2 f2reu5lem2_4 wrmo f2reu5lem2_1 f2reu5lem2_3 wral f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 wmo f2reu5lem2_1 f2reu5lem2_3 wral f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 w3a f2reu5lem2_2 wmo f2reu5lem2_1 wal f2reu5lem2_0 f2reu5lem2_2 f2reu5lem2_4 wrmo f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 wmo f2reu5lem2_1 f2reu5lem2_3 f2reu5lem2_0 f2reu5lem2_2 f2reu5lem2_4 df-rmo ralbii f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 wmo f2reu5lem2_1 f2reu5lem2_3 wral f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 wmo wi f2reu5lem2_1 wal f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 w3a f2reu5lem2_2 wmo f2reu5lem2_1 wal f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 wmo f2reu5lem2_1 f2reu5lem2_3 df-ral f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 wmo wi f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 w3a f2reu5lem2_2 wmo f2reu5lem2_1 f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 wmo wi f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa wa f2reu5lem2_2 wmo f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 w3a f2reu5lem2_2 wmo f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa wa f2reu5lem2_2 wmo f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 wmo wi f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa f2reu5lem2_2 moanimv bicomi f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa wa f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 w3a f2reu5lem2_2 f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 w3a f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 wa wa f2reu5lem2_1 sup_set_class f2reu5lem2_3 wcel f2reu5lem2_2 sup_set_class f2reu5lem2_4 wcel f2reu5lem2_0 3anass bicomi mobii bitri albii bitri bitri $.
$}
$( Lemma for ~ 2reu5 .  This lemma is interesting in its own right, showing
       that existential restriction in the last conjunct (the "at most one"
       part) is optional; compare ~ rmo2 .  (Contributed by Alexander van der
       Vekens, 17-Jun-2017.) $)
${
	$d w y z A $.
	$d w x z B $.
	$d x y $.
	$d ph w $.
	$d ph z $.
	f2reu5lem3_0 $f wff ph $.
	f2reu5lem3_1 $f set x $.
	f2reu5lem3_2 $f set y $.
	f2reu5lem3_3 $f set z $.
	f2reu5lem3_4 $f set w $.
	f2reu5lem3_5 $f class A $.
	f2reu5lem3_6 $f class B $.
	2reu5lem3 $p |- ( ( E! x e. A E! y e. B ph /\ A. x e. A E* y e. B ph ) <-> ( E. x e. A E. y e. B ph /\ E. z E. w A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) ) $= f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wreu f2reu5lem3_1 f2reu5lem3_5 wreu f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrmo f2reu5lem3_1 f2reu5lem3_5 wral wa f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 weu f2reu5lem3_1 weu f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 wmo f2reu5lem3_1 wal wa f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 wex f2reu5lem3_1 wex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 wal f2reu5lem3_1 wal f2reu5lem3_4 wex f2reu5lem3_3 wex wa f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex f2reu5lem3_1 f2reu5lem3_5 wrex f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral f2reu5lem3_1 f2reu5lem3_5 wral f2reu5lem3_4 wex f2reu5lem3_3 wex wa f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wreu f2reu5lem3_1 f2reu5lem3_5 wreu f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 weu f2reu5lem3_1 weu f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrmo f2reu5lem3_1 f2reu5lem3_5 wral f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 wmo f2reu5lem3_1 wal f2reu5lem3_0 f2reu5lem3_1 f2reu5lem3_2 f2reu5lem3_5 f2reu5lem3_6 2reu5lem1 f2reu5lem3_0 f2reu5lem3_1 f2reu5lem3_2 f2reu5lem3_5 f2reu5lem3_6 2reu5lem2 anbi12i f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 f2reu5lem3_2 f2reu5lem3_3 f2reu5lem3_4 2eu5 f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 wex f2reu5lem3_1 wex f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex f2reu5lem3_1 f2reu5lem3_5 wrex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 wal f2reu5lem3_1 wal f2reu5lem3_4 wex f2reu5lem3_3 wex f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral f2reu5lem3_1 f2reu5lem3_5 wral f2reu5lem3_4 wex f2reu5lem3_3 wex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 wex f2reu5lem3_1 wex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex wa f2reu5lem3_1 wex f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex f2reu5lem3_1 f2reu5lem3_5 wrex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 wex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex wa f2reu5lem3_1 f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 wex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 wa wa f2reu5lem3_2 wex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 wa f2reu5lem3_2 wex wa f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex wa f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 wa wa f2reu5lem3_2 f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 3anass exbii f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 wa f2reu5lem3_2 19.42v f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 wa f2reu5lem3_2 wex f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 wa f2reu5lem3_2 wex f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 df-rex bicomi anbi2i 3bitri exbii f2reu5lem3_0 f2reu5lem3_2 f2reu5lem3_6 wrex f2reu5lem3_1 f2reu5lem3_5 df-rex bitr4i f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 wal f2reu5lem3_1 wal f2reu5lem3_4 wex f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral f2reu5lem3_1 f2reu5lem3_5 wral f2reu5lem3_4 wex f2reu5lem3_3 f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 wal f2reu5lem3_1 wal f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral f2reu5lem3_1 f2reu5lem3_5 wral f2reu5lem3_4 f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 wal f2reu5lem3_1 wal f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral wi f2reu5lem3_1 wal f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral f2reu5lem3_1 f2reu5lem3_5 wral f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 wal f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral wi f2reu5lem3_1 f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 wal f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi wi wi f2reu5lem3_2 wal f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi wi f2reu5lem3_2 f2reu5lem3_6 wral f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral wi f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi wi wi f2reu5lem3_2 f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 wa wa f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 wa f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi wi f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi wi wi f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 w3a f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 wa wa f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_0 3anan12 imbi1i f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 wa f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa impexp f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 wa f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi wi f2reu5lem3_2 sup_set_class f2reu5lem3_6 wcel f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa impexp imbi2i 3bitri albii f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi wi f2reu5lem3_2 f2reu5lem3_6 df-ral f2reu5lem3_1 sup_set_class f2reu5lem3_5 wcel f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 r19.21v 3bitr2i albii f2reu5lem3_0 f2reu5lem3_1 sup_set_class f2reu5lem3_3 sup_set_class wceq f2reu5lem3_2 sup_set_class f2reu5lem3_4 sup_set_class wceq wa wi f2reu5lem3_2 f2reu5lem3_6 wral f2reu5lem3_1 f2reu5lem3_5 df-ral bitr4i exbii exbii anbi12i 3bitri $.
$}
$( Double restricted existential uniqueness in terms of restricted
       existential quantification and restricted universal quantification,
       analogous to ~ 2eu5 and ~ reu3 .  (Contributed by Alexander van der
       Vekens, 17-Jun-2017.) $)
${
	$d w y z A $.
	$d w x z B $.
	$d x y $.
	$d ph w $.
	$d ph z $.
	$d x A $.
	$d y B $.
	f2reu5_0 $f wff ph $.
	f2reu5_1 $f set x $.
	f2reu5_2 $f set y $.
	f2reu5_3 $f set z $.
	f2reu5_4 $f set w $.
	f2reu5_5 $f class A $.
	f2reu5_6 $f class B $.
	2reu5 $p |- ( ( E! x e. A E! y e. B ph /\ A. x e. A E* y e. B ph ) <-> ( E. x e. A E. y e. B ph /\ E. z e. A E. w e. B A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) ) $= f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 wex f2reu5_3 wex wa f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa wa f2reu5_4 wex f2reu5_3 wex wa f2reu5_0 f2reu5_2 f2reu5_6 wreu f2reu5_1 f2reu5_5 wreu f2reu5_0 f2reu5_2 f2reu5_6 wrmo f2reu5_1 f2reu5_5 wral wa f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 f2reu5_6 wrex f2reu5_3 f2reu5_5 wrex wa f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 wex f2reu5_3 wex f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa wa f2reu5_4 wex f2reu5_3 wex f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa wa f2reu5_3 f2reu5_4 f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel wa f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa wa f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel wa f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel wa f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral wa f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi wa f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel wa f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 r19.29r f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral wa f2reu5_0 f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi wa f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 f2reu5_0 f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 r19.29r reximi f2reu5_0 f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi wa f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel wa f2reu5_0 f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi wa f2reu5_2 f2reu5_6 wrex f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 f2reu5_0 f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi wa f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa f2reu5_2 f2reu5_6 f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa pm3.35 reximi reximi f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel wa f2reu5_1 f2reu5_2 f2reu5_5 f2reu5_6 f2reu5_1 sup_set_class f2reu5_5 wcel f2reu5_2 sup_set_class f2reu5_6 wcel wa f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel wa f2reu5_1 sup_set_class f2reu5_5 wcel f2reu5_2 sup_set_class f2reu5_6 wcel wa f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wa f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa f2reu5_1 sup_set_class f2reu5_5 wcel f2reu5_2 sup_set_class f2reu5_6 wcel wa f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_4 sup_set_class f2reu5_6 wcel wa f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_1 sup_set_class f2reu5_5 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_6 wcel f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_1 sup_set_class f2reu5_3 sup_set_class f2reu5_5 eleq1 f2reu5_2 sup_set_class f2reu5_4 sup_set_class f2reu5_6 eleq1 bi2anan9 biimpac ancomd ex rexlimivv syl 3syl ex pm4.71rd f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral anass syl6bb 2exbidv pm5.32i f2reu5_0 f2reu5_1 f2reu5_2 f2reu5_3 f2reu5_4 f2reu5_5 f2reu5_6 2reu5lem3 f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 f2reu5_6 wrex f2reu5_3 f2reu5_5 wrex f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa wa f2reu5_4 wex f2reu5_3 wex f2reu5_0 f2reu5_2 f2reu5_6 wrex f2reu5_1 f2reu5_5 wrex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 f2reu5_6 wrex f2reu5_3 f2reu5_5 wrex f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 f2reu5_6 wrex wa f2reu5_3 wex f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa wa f2reu5_4 wex f2reu5_3 wex f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 f2reu5_6 wrex f2reu5_3 f2reu5_5 df-rex f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 f2reu5_6 wrex wa f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa wa f2reu5_4 wex f2reu5_3 f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 f2reu5_6 wrex wa f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa f2reu5_4 f2reu5_6 wrex f2reu5_4 sup_set_class f2reu5_6 wcel f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa wa f2reu5_4 wex f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral f2reu5_4 f2reu5_6 r19.42v f2reu5_3 sup_set_class f2reu5_5 wcel f2reu5_0 f2reu5_1 sup_set_class f2reu5_3 sup_set_class wceq f2reu5_2 sup_set_class f2reu5_4 sup_set_class wceq wa wi f2reu5_2 f2reu5_6 wral f2reu5_1 f2reu5_5 wral wa f2reu5_4 f2reu5_6 df-rex bitr3i exbii bitri anbi2i 3bitr4i $.
$}

