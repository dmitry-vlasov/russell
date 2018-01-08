$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/_Weak_deduction_theorem__for_set_theory.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          Power classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Declare the symbol for power class. */

$)
$c ~P  $.
$( /* Calligraphic P */

$)
$( /* Extend class notation to include power class.  (The tilde in the Metamath
     token is meant to suggest the calligraphic font of the P.) */

$)
${
	fcpw_0 $f class A $.
	cpw $a class ~P A $.
$}
$( /* Soundness justification theorem for ~ df-pw .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) */

$)
${
	$d x A $.
	$d y A $.
	$d z x $.
	$d z y $.
	$d z A $.
	ipwjust_0 $f set z $.
	fpwjust_0 $f set x $.
	fpwjust_1 $f set y $.
	fpwjust_2 $f class A $.
	pwjust $p |- { x | x C_ A } = { y | y C_ A } $= fpwjust_0 sup_set_class fpwjust_2 wss fpwjust_0 cab ipwjust_0 sup_set_class fpwjust_2 wss ipwjust_0 cab fpwjust_1 sup_set_class fpwjust_2 wss fpwjust_1 cab fpwjust_0 sup_set_class fpwjust_2 wss ipwjust_0 sup_set_class fpwjust_2 wss fpwjust_0 ipwjust_0 fpwjust_0 sup_set_class ipwjust_0 sup_set_class fpwjust_2 sseq1 cbvabv ipwjust_0 sup_set_class fpwjust_2 wss fpwjust_1 sup_set_class fpwjust_2 wss ipwjust_0 fpwjust_1 ipwjust_0 sup_set_class fpwjust_1 sup_set_class fpwjust_2 sseq1 cbvabv eqtri $.
$}
$( /* Define power class.  Definition 5.10 of [TakeutiZaring] p. 17, but we
       also let it apply to proper classes, i.e. those that are not members of
       ` _V ` .  When applied to a set, this produces its power set.  A power
       set of S is the set of all subsets of S, including the empty set and S
       itself.  For example, if ` A = { 3 , 5 , 7 } ` , then
       ` ~P A = { (/) , { 3 } , { 5 } , { 7 } , { 3 , 5 } , `
       ` { 3 , 7 } , { 5 , 7 } , { 3 , 5 , 7 } } ` ( ~ ex-pw ).  We will later
       introduce the Axiom of Power Sets ~ ax-pow , which can be expressed in
       class notation per ~ pwexg .  Still later we will prove, in ~ hashpw ,
       that the size of the power set of a finite set is 2 raised to the power
       of the size of the set.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	fdf-pw_0 $f set x $.
	fdf-pw_1 $f class A $.
	df-pw $a |- ~P A = { x | x C_ A } $.
$}
$( /* Equality theorem for power class.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	ipweq_0 $f set x $.
	fpweq_0 $f class A $.
	fpweq_1 $f class B $.
	pweq $p |- ( A = B -> ~P A = ~P B ) $= fpweq_0 fpweq_1 wceq ipweq_0 sup_set_class fpweq_0 wss ipweq_0 cab ipweq_0 sup_set_class fpweq_1 wss ipweq_0 cab fpweq_0 cpw fpweq_1 cpw fpweq_0 fpweq_1 wceq ipweq_0 sup_set_class fpweq_0 wss ipweq_0 sup_set_class fpweq_1 wss ipweq_0 fpweq_0 fpweq_1 ipweq_0 sup_set_class sseq2 abbidv ipweq_0 fpweq_0 df-pw ipweq_0 fpweq_1 df-pw 3eqtr4g $.
$}
$( /* Equality inference for power class.  (Contributed by NM,
       27-Nov-2013.) */

$)
${
	fpweqi_0 $f class A $.
	fpweqi_1 $f class B $.
	epweqi_0 $e |- A = B $.
	pweqi $p |- ~P A = ~P B $= fpweqi_0 fpweqi_1 wceq fpweqi_0 cpw fpweqi_1 cpw wceq epweqi_0 fpweqi_0 fpweqi_1 pweq ax-mp $.
$}
$( /* Equality deduction for power class.  (Contributed by NM,
       27-Nov-2013.) */

$)
${
	fpweqd_0 $f wff ph $.
	fpweqd_1 $f class A $.
	fpweqd_2 $f class B $.
	epweqd_0 $e |- ( ph -> A = B ) $.
	pweqd $p |- ( ph -> ~P A = ~P B ) $= fpweqd_0 fpweqd_1 fpweqd_2 wceq fpweqd_1 cpw fpweqd_2 cpw wceq epweqd_0 fpweqd_1 fpweqd_2 pweq syl $.
$}
$( /* Membership in a power class.  Theorem 86 of [Suppes] p. 47.
         (Contributed by NM, 31-Dec-1993.) */

$)
${
	$d A x $.
	$d B x $.
	ielpw_0 $f set x $.
	felpw_0 $f class A $.
	felpw_1 $f class B $.
	eelpw_0 $e |- A e. _V $.
	elpw $p |- ( A e. ~P B <-> A C_ B ) $= ielpw_0 sup_set_class felpw_1 wss felpw_0 felpw_1 wss ielpw_0 felpw_0 felpw_1 cpw eelpw_0 ielpw_0 sup_set_class felpw_0 felpw_1 sseq1 ielpw_0 felpw_1 df-pw elab2 $.
$}
$( /* Membership in a power class.  Theorem 86 of [Suppes] p. 47.  See also
       ~ elpw2g .  (Contributed by NM, 6-Aug-2000.) */

$)
${
	$d A x $.
	$d B x $.
	ielpwg_0 $f set x $.
	felpwg_0 $f class A $.
	felpwg_1 $f class B $.
	felpwg_2 $f class V $.
	elpwg $p |- ( A e. V -> ( A e. ~P B <-> A C_ B ) ) $= ielpwg_0 sup_set_class felpwg_1 cpw wcel ielpwg_0 sup_set_class felpwg_1 wss felpwg_0 felpwg_1 cpw wcel felpwg_0 felpwg_1 wss ielpwg_0 felpwg_0 felpwg_2 ielpwg_0 sup_set_class felpwg_0 felpwg_1 cpw eleq1 ielpwg_0 sup_set_class felpwg_0 felpwg_1 sseq1 ielpwg_0 sup_set_class felpwg_1 ielpwg_0 vex elpw vtoclbg $.
$}
$( /* Subset relation implied by membership in a power class.  (Contributed by
     NM, 17-Feb-2007.) */

$)
${
	felpwi_0 $f class A $.
	felpwi_1 $f class B $.
	elpwi $p |- ( A e. ~P B -> A C_ B ) $= felpwi_0 felpwi_1 cpw wcel felpwi_0 felpwi_1 wss felpwi_0 felpwi_1 felpwi_1 cpw elpwg ibi $.
$}
$( /* An element of a power class is a subclass.  Deduction form of ~ elpwi .
       (Contributed by David Moews, 1-May-2017.) */

$)
${
	felpwid_0 $f wff ph $.
	felpwid_1 $f class A $.
	felpwid_2 $f class B $.
	eelpwid_0 $e |- ( ph -> A e. ~P B ) $.
	elpwid $p |- ( ph -> A C_ B ) $= felpwid_0 felpwid_1 felpwid_2 cpw wcel felpwid_1 felpwid_2 wss eelpwid_0 felpwid_1 felpwid_2 elpwi syl $.
$}
$( /* If ` A ` belongs to a part of ` C ` then ` A ` belongs to ` C ` .
     (Contributed by FL, 3-Aug-2009.) */

$)
${
	felelpwi_0 $f class A $.
	felelpwi_1 $f class B $.
	felelpwi_2 $f class C $.
	elelpwi $p |- ( ( A e. B /\ B e. ~P C ) -> A e. C ) $= felelpwi_1 felelpwi_2 cpw wcel felelpwi_0 felelpwi_1 wcel felelpwi_0 felelpwi_2 wcel felelpwi_1 felelpwi_2 cpw wcel felelpwi_1 felelpwi_2 felelpwi_0 felelpwi_1 felelpwi_2 elpwi sseld impcom $.
$}
$( /* Bound-variable hypothesis builder for power class.  (Contributed by NM,
       28-Oct-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) */

$)
${
	$d y A $.
	$d x y $.
	infpw_0 $f set y $.
	fnfpw_0 $f set x $.
	fnfpw_1 $f class A $.
	enfpw_0 $e |- F/_ x A $.
	nfpw $p |- F/_ x ~P A $= fnfpw_0 fnfpw_1 cpw infpw_0 sup_set_class fnfpw_1 wss infpw_0 cab infpw_0 fnfpw_1 df-pw infpw_0 sup_set_class fnfpw_1 wss fnfpw_0 infpw_0 fnfpw_0 infpw_0 sup_set_class fnfpw_1 fnfpw_0 infpw_0 sup_set_class nfcv enfpw_0 nfss nfab nfcxfr $.
$}
$( /* Membership of the original in a power set.  (Contributed by Stefan O'Rear,
     1-Feb-2015.) */

$)
${
	fpwidg_0 $f class A $.
	fpwidg_1 $f class V $.
	pwidg $p |- ( A e. V -> A e. ~P A ) $= fpwidg_0 fpwidg_1 wcel fpwidg_0 fpwidg_0 cpw wcel fpwidg_0 fpwidg_0 wss fpwidg_0 ssid fpwidg_0 fpwidg_0 fpwidg_1 elpwg mpbiri $.
$}
$( /* A set is a member of its power class.  Theorem 87 of [Suppes] p. 47.
       (Contributed by NM, 5-Aug-1993.) */

$)
${
	fpwid_0 $f class A $.
	epwid_0 $e |- A e. _V $.
	pwid $p |- A e. ~P A $= fpwid_0 cvv wcel fpwid_0 fpwid_0 cpw wcel epwid_0 fpwid_0 cvv pwidg ax-mp $.
$}
$( /* Subclass relationship for power class.  (Contributed by NM,
       21-Jun-2009.) */

$)
${
	$d x A $.
	$d x B $.
	fpwss_0 $f set x $.
	fpwss_1 $f class A $.
	fpwss_2 $f class B $.
	pwss $p |- ( ~P A C_ B <-> A. x ( x C_ A -> x e. B ) ) $= fpwss_1 cpw fpwss_2 wss fpwss_0 sup_set_class fpwss_1 cpw wcel fpwss_0 sup_set_class fpwss_2 wcel wi fpwss_0 wal fpwss_0 sup_set_class fpwss_1 wss fpwss_0 sup_set_class fpwss_2 wcel wi fpwss_0 wal fpwss_0 fpwss_1 cpw fpwss_2 dfss2 fpwss_0 sup_set_class fpwss_1 cpw wcel fpwss_0 sup_set_class fpwss_2 wcel wi fpwss_0 sup_set_class fpwss_1 wss fpwss_0 sup_set_class fpwss_2 wcel wi fpwss_0 fpwss_0 sup_set_class fpwss_1 cpw wcel fpwss_0 sup_set_class fpwss_1 wss fpwss_0 sup_set_class fpwss_2 wcel fpwss_0 sup_set_class fpwss_1 wss fpwss_0 fpwss_1 cpw fpwss_0 fpwss_1 df-pw abeq2i imbi1i albii bitri $.
$}

