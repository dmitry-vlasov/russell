$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Partial_and_complete_ordering.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Founded and well-ordering relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare new constant symbols. $)
$c Fr  $.
$( Well-founded predicate symbol (read: 'well-founded'). $)
$c Se  $.
$( Set-like predicate symbol (read: 'set-like'). $)
$c We  $.
$( Well-ordering predicate symbol (read: 'well-orders') $)
$( Extend wff notation to include the well-founded predicate.  Read:  ' ` R `
     is a well-founded relation on ` A ` .' $)
${
	fwfr_0 $f class A $.
	fwfr_1 $f class R $.
	wfr $a wff R Fr A $.
$}
$( Extend wff notation to include the set-like predicate.  Read:  ' ` R ` is
     set-like on ` A ` .' $)
${
	fwse_0 $f class A $.
	fwse_1 $f class R $.
	wse $a wff R Se A $.
$}
$( Extend wff notation to include the well-ordering predicate.
     Read:  ' ` R ` well-orders ` A ` .' $)
${
	fwwe_0 $f class A $.
	fwwe_1 $f class R $.
	wwe $a wff R We A $.
$}
$( Define the well-founded relation predicate.  Definition 6.24(1) of
       [TakeutiZaring] p. 30.  For alternate definitions, see ~ dffr2 and
       ~ dffr3 .  (Contributed by NM, 3-Apr-1994.) $)
${
	$d x y z R $.
	$d x y z A $.
	fdf-fr_0 $f set x $.
	fdf-fr_1 $f set y $.
	fdf-fr_2 $f set z $.
	fdf-fr_3 $f class A $.
	fdf-fr_4 $f class R $.
	df-fr $a |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x A. z e. x -. z R y ) ) $.
$}
$( Define the set-like predicate.  (Contributed by Mario Carneiro,
       19-Nov-2014.) $)
${
	$d x y R $.
	$d x y A $.
	fdf-se_0 $f set x $.
	fdf-se_1 $f set y $.
	fdf-se_2 $f class A $.
	fdf-se_3 $f class R $.
	df-se $a |- ( R Se A <-> A. x e. A { y e. A | y R x } e. _V ) $.
$}
$( Define the well-ordering predicate.  For an alternate definition, see
     ~ dfwe2 .  (Contributed by NM, 3-Apr-1994.) $)
${
	fdf-we_0 $f class A $.
	fdf-we_1 $f class R $.
	df-we $a |- ( R We A <-> ( R Fr A /\ R Or A ) ) $.
$}
$( Property of well-founded relation (one direction of definition).
       (Contributed by NM, 18-Mar-1997.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z R $.
	$d x y $.
	ifri_0 $f set z $.
	ffri_0 $f set x $.
	ffri_1 $f set y $.
	ffri_2 $f class A $.
	ffri_3 $f class B $.
	ffri_4 $f class C $.
	ffri_5 $f class R $.
	fri $p |- ( ( ( B e. C /\ R Fr A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E. x e. B A. y e. B -. y R x ) $= ffri_3 ffri_4 wcel ffri_2 ffri_5 wfr ffri_3 ffri_2 wss ffri_3 c0 wne wa ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ffri_3 wral ffri_0 ffri_3 wrex ffri_2 ffri_5 wfr ifri_0 sup_set_class ffri_2 wss ifri_0 sup_set_class c0 wne wa ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ifri_0 sup_set_class wral ffri_0 ifri_0 sup_set_class wrex wi ifri_0 wal ffri_3 ffri_4 wcel ffri_3 ffri_2 wss ffri_3 c0 wne wa ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ffri_3 wral ffri_0 ffri_3 wrex wi ifri_0 ffri_0 ffri_1 ffri_2 ffri_5 df-fr ifri_0 sup_set_class ffri_2 wss ifri_0 sup_set_class c0 wne wa ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ifri_0 sup_set_class wral ffri_0 ifri_0 sup_set_class wrex wi ffri_3 ffri_2 wss ffri_3 c0 wne wa ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ffri_3 wral ffri_0 ffri_3 wrex wi ifri_0 ffri_3 ffri_4 ifri_0 sup_set_class ffri_3 wceq ifri_0 sup_set_class ffri_2 wss ifri_0 sup_set_class c0 wne wa ffri_3 ffri_2 wss ffri_3 c0 wne wa ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ifri_0 sup_set_class wral ffri_0 ifri_0 sup_set_class wrex ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ffri_3 wral ffri_0 ffri_3 wrex ifri_0 sup_set_class ffri_3 wceq ifri_0 sup_set_class ffri_2 wss ffri_3 ffri_2 wss ifri_0 sup_set_class c0 wne ffri_3 c0 wne ifri_0 sup_set_class ffri_3 ffri_2 sseq1 ifri_0 sup_set_class ffri_3 c0 neeq1 anbi12d ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ifri_0 sup_set_class wral ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ffri_3 wral ffri_0 ifri_0 sup_set_class ffri_3 ffri_1 sup_set_class ffri_0 sup_set_class ffri_5 wbr wn ffri_1 ifri_0 sup_set_class ffri_3 raleq rexeqbi1dv imbi12d spcgv syl5bi imp31 $.
$}
$( The ` R ` -preimage of an element of the base set in a set-like relation
       is a set.  (Contributed by Mario Carneiro, 19-Nov-2014.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y R $.
	$d x y $.
	iseex_0 $f set y $.
	fseex_0 $f set x $.
	fseex_1 $f class A $.
	fseex_2 $f class B $.
	fseex_3 $f class R $.
	seex $p |- ( ( R Se A /\ B e. A ) -> { x e. A | x R B } e. _V ) $= fseex_1 fseex_3 wse fseex_0 sup_set_class iseex_0 sup_set_class fseex_3 wbr fseex_0 fseex_1 crab cvv wcel iseex_0 fseex_1 wral fseex_2 fseex_1 wcel fseex_0 sup_set_class fseex_2 fseex_3 wbr fseex_0 fseex_1 crab cvv wcel iseex_0 fseex_0 fseex_1 fseex_3 df-se fseex_0 sup_set_class iseex_0 sup_set_class fseex_3 wbr fseex_0 fseex_1 crab cvv wcel fseex_0 sup_set_class fseex_2 fseex_3 wbr fseex_0 fseex_1 crab cvv wcel iseex_0 fseex_2 fseex_1 iseex_0 sup_set_class fseex_2 wceq fseex_0 sup_set_class iseex_0 sup_set_class fseex_3 wbr fseex_0 fseex_1 crab fseex_0 sup_set_class fseex_2 fseex_3 wbr fseex_0 fseex_1 crab cvv iseex_0 sup_set_class fseex_2 wceq fseex_0 sup_set_class iseex_0 sup_set_class fseex_3 wbr fseex_0 sup_set_class fseex_2 fseex_3 wbr fseex_0 fseex_1 iseex_0 sup_set_class fseex_2 fseex_0 sup_set_class fseex_3 breq2 rabbidv eleq1d rspccva sylanb $.
$}
$( Any relation on a set is set-like on it.  (Contributed by Mario
       Carneiro, 22-Jun-2015.) $)
${
	$d x y A $.
	$d x y $.
	$d x y R $.
	$d x y V $.
	iexse_0 $f set x $.
	iexse_1 $f set y $.
	fexse_0 $f class A $.
	fexse_1 $f class R $.
	fexse_2 $f class V $.
	exse $p |- ( A e. V -> R Se A ) $= fexse_0 fexse_2 wcel iexse_1 sup_set_class iexse_0 sup_set_class fexse_1 wbr iexse_1 fexse_0 crab cvv wcel iexse_0 fexse_0 wral fexse_0 fexse_1 wse fexse_0 fexse_2 wcel iexse_1 sup_set_class iexse_0 sup_set_class fexse_1 wbr iexse_1 fexse_0 crab cvv wcel iexse_0 fexse_0 iexse_1 sup_set_class iexse_0 sup_set_class fexse_1 wbr iexse_1 fexse_0 fexse_2 rabexg ralrimivw iexse_0 iexse_1 fexse_0 fexse_1 df-se sylibr $.
$}
$( Alternate definition of well-founded relation.  Similar to Definition
       6.21 of [TakeutiZaring] p. 30.  (Contributed by NM, 17-Feb-2004.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.)  (Proof shortened by
       Mario Carneiro, 23-Jun-2015.) $)
${
	$d x y z A $.
	$d x y z R $.
	fdffr2_0 $f set x $.
	fdffr2_1 $f set y $.
	fdffr2_2 $f set z $.
	fdffr2_3 $f class A $.
	fdffr2_4 $f class R $.
	dffr2 $p |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x { z e. x | z R y } = (/) ) ) $= fdffr2_3 fdffr2_4 wfr fdffr2_0 sup_set_class fdffr2_3 wss fdffr2_0 sup_set_class c0 wne wa fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr wn fdffr2_2 fdffr2_0 sup_set_class wral fdffr2_1 fdffr2_0 sup_set_class wrex wi fdffr2_0 wal fdffr2_0 sup_set_class fdffr2_3 wss fdffr2_0 sup_set_class c0 wne wa fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr fdffr2_2 fdffr2_0 sup_set_class crab c0 wceq fdffr2_1 fdffr2_0 sup_set_class wrex wi fdffr2_0 wal fdffr2_0 fdffr2_1 fdffr2_2 fdffr2_3 fdffr2_4 df-fr fdffr2_0 sup_set_class fdffr2_3 wss fdffr2_0 sup_set_class c0 wne wa fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr fdffr2_2 fdffr2_0 sup_set_class crab c0 wceq fdffr2_1 fdffr2_0 sup_set_class wrex wi fdffr2_0 sup_set_class fdffr2_3 wss fdffr2_0 sup_set_class c0 wne wa fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr wn fdffr2_2 fdffr2_0 sup_set_class wral fdffr2_1 fdffr2_0 sup_set_class wrex wi fdffr2_0 fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr fdffr2_2 fdffr2_0 sup_set_class crab c0 wceq fdffr2_1 fdffr2_0 sup_set_class wrex fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr wn fdffr2_2 fdffr2_0 sup_set_class wral fdffr2_1 fdffr2_0 sup_set_class wrex fdffr2_0 sup_set_class fdffr2_3 wss fdffr2_0 sup_set_class c0 wne wa fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr fdffr2_2 fdffr2_0 sup_set_class crab c0 wceq fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr wn fdffr2_2 fdffr2_0 sup_set_class wral fdffr2_1 fdffr2_0 sup_set_class fdffr2_2 sup_set_class fdffr2_1 sup_set_class fdffr2_4 wbr fdffr2_2 fdffr2_0 sup_set_class rabeq0 rexbii imbi2i albii bitr4i $.
$}
$( Property of well-founded relation (one direction of definition using
       class variables).  (Contributed by NM, 17-Feb-2004.)  (Revised by Mario
       Carneiro, 19-Nov-2014.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y R $.
	ffrc_0 $f set x $.
	ffrc_1 $f set y $.
	ffrc_2 $f class A $.
	ffrc_3 $f class B $.
	ffrc_4 $f class R $.
	efrc_0 $e |- B e. _V $.
	frc $p |- ( ( R Fr A /\ B C_ A /\ B =/= (/) ) -> E. x e. B { y e. B | y R x } = (/) ) $= ffrc_2 ffrc_4 wfr ffrc_3 ffrc_2 wss ffrc_3 c0 wne w3a ffrc_1 sup_set_class ffrc_0 sup_set_class ffrc_4 wbr wn ffrc_1 ffrc_3 wral ffrc_0 ffrc_3 wrex ffrc_1 sup_set_class ffrc_0 sup_set_class ffrc_4 wbr ffrc_1 ffrc_3 crab c0 wceq ffrc_0 ffrc_3 wrex ffrc_2 ffrc_4 wfr ffrc_3 ffrc_2 wss ffrc_3 c0 wne ffrc_1 sup_set_class ffrc_0 sup_set_class ffrc_4 wbr wn ffrc_1 ffrc_3 wral ffrc_0 ffrc_3 wrex ffrc_3 cvv wcel ffrc_2 ffrc_4 wfr ffrc_3 ffrc_2 wss ffrc_3 c0 wne wa ffrc_1 sup_set_class ffrc_0 sup_set_class ffrc_4 wbr wn ffrc_1 ffrc_3 wral ffrc_0 ffrc_3 wrex efrc_0 ffrc_0 ffrc_1 ffrc_2 ffrc_3 cvv ffrc_4 fri mpanl1 3impb ffrc_1 sup_set_class ffrc_0 sup_set_class ffrc_4 wbr ffrc_1 ffrc_3 crab c0 wceq ffrc_1 sup_set_class ffrc_0 sup_set_class ffrc_4 wbr wn ffrc_1 ffrc_3 wral ffrc_0 ffrc_3 ffrc_1 sup_set_class ffrc_0 sup_set_class ffrc_4 wbr ffrc_1 ffrc_3 rabeq0 rexbii sylibr $.
$}
$( Subset theorem for the well-founded predicate.  Exercise 1 of
       [TakeutiZaring] p. 31.  (Contributed by NM, 3-Apr-1994.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z R $.
	$d x y $.
	ifrss_0 $f set x $.
	ifrss_1 $f set y $.
	ifrss_2 $f set z $.
	ffrss_0 $f class A $.
	ffrss_1 $f class B $.
	ffrss_2 $f class R $.
	frss $p |- ( A C_ B -> ( R Fr B -> R Fr A ) ) $= ffrss_0 ffrss_1 wss ifrss_0 sup_set_class ffrss_1 wss ifrss_0 sup_set_class c0 wne wa ifrss_2 sup_set_class ifrss_1 sup_set_class ffrss_2 wbr wn ifrss_2 ifrss_0 sup_set_class wral ifrss_1 ifrss_0 sup_set_class wrex wi ifrss_0 wal ifrss_0 sup_set_class ffrss_0 wss ifrss_0 sup_set_class c0 wne wa ifrss_2 sup_set_class ifrss_1 sup_set_class ffrss_2 wbr wn ifrss_2 ifrss_0 sup_set_class wral ifrss_1 ifrss_0 sup_set_class wrex wi ifrss_0 wal ffrss_1 ffrss_2 wfr ffrss_0 ffrss_2 wfr ffrss_0 ffrss_1 wss ifrss_0 sup_set_class ffrss_1 wss ifrss_0 sup_set_class c0 wne wa ifrss_2 sup_set_class ifrss_1 sup_set_class ffrss_2 wbr wn ifrss_2 ifrss_0 sup_set_class wral ifrss_1 ifrss_0 sup_set_class wrex wi ifrss_0 sup_set_class ffrss_0 wss ifrss_0 sup_set_class c0 wne wa ifrss_2 sup_set_class ifrss_1 sup_set_class ffrss_2 wbr wn ifrss_2 ifrss_0 sup_set_class wral ifrss_1 ifrss_0 sup_set_class wrex wi ifrss_0 ffrss_0 ffrss_1 wss ifrss_0 sup_set_class ffrss_0 wss ifrss_0 sup_set_class c0 wne wa ifrss_0 sup_set_class ffrss_1 wss ifrss_0 sup_set_class c0 wne wa ifrss_2 sup_set_class ifrss_1 sup_set_class ffrss_2 wbr wn ifrss_2 ifrss_0 sup_set_class wral ifrss_1 ifrss_0 sup_set_class wrex ffrss_0 ffrss_1 wss ifrss_0 sup_set_class ffrss_0 wss ifrss_0 sup_set_class ffrss_1 wss ifrss_0 sup_set_class c0 wne ifrss_0 sup_set_class ffrss_0 wss ffrss_0 ffrss_1 wss ifrss_0 sup_set_class ffrss_1 wss ifrss_0 sup_set_class ffrss_0 ffrss_1 sstr2 com12 anim1d imim1d alimdv ifrss_0 ifrss_1 ifrss_2 ffrss_1 ffrss_2 df-fr ifrss_0 ifrss_1 ifrss_2 ffrss_0 ffrss_2 df-fr 3imtr4g $.
$}
$( Subset theorem for the set-like predicate.  (Contributed by Mario
       Carneiro, 24-Jun-2015.) $)
${
	$d x y A $.
	$d x y $.
	$d x y R $.
	$d x y S $.
	isess1_0 $f set x $.
	isess1_1 $f set y $.
	fsess1_0 $f class A $.
	fsess1_1 $f class R $.
	fsess1_2 $f class S $.
	sess1 $p |- ( R C_ S -> ( S Se A -> R Se A ) ) $= fsess1_1 fsess1_2 wss isess1_1 sup_set_class isess1_0 sup_set_class fsess1_2 wbr isess1_1 fsess1_0 crab cvv wcel isess1_0 fsess1_0 wral isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 wbr isess1_1 fsess1_0 crab cvv wcel isess1_0 fsess1_0 wral fsess1_0 fsess1_2 wse fsess1_0 fsess1_1 wse fsess1_1 fsess1_2 wss isess1_1 sup_set_class isess1_0 sup_set_class fsess1_2 wbr isess1_1 fsess1_0 crab cvv wcel isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 wbr isess1_1 fsess1_0 crab cvv wcel isess1_0 fsess1_0 fsess1_1 fsess1_2 wss isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 wbr isess1_1 fsess1_0 crab isess1_1 sup_set_class isess1_0 sup_set_class fsess1_2 wbr isess1_1 fsess1_0 crab wss isess1_1 sup_set_class isess1_0 sup_set_class fsess1_2 wbr isess1_1 fsess1_0 crab cvv wcel isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 wbr isess1_1 fsess1_0 crab cvv wcel wi fsess1_1 fsess1_2 wss isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 wbr isess1_1 sup_set_class isess1_0 sup_set_class fsess1_2 wbr isess1_1 fsess1_0 fsess1_1 fsess1_2 wss isess1_1 sup_set_class fsess1_0 wcel wa fsess1_1 fsess1_2 isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 fsess1_2 wss isess1_1 sup_set_class fsess1_0 wcel simpl ssbrd ss2rabdv isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 wbr isess1_1 fsess1_0 crab isess1_1 sup_set_class isess1_0 sup_set_class fsess1_2 wbr isess1_1 fsess1_0 crab wss isess1_1 sup_set_class isess1_0 sup_set_class fsess1_2 wbr isess1_1 fsess1_0 crab cvv wcel isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 wbr isess1_1 fsess1_0 crab cvv wcel isess1_1 sup_set_class isess1_0 sup_set_class fsess1_1 wbr isess1_1 fsess1_0 crab isess1_1 sup_set_class isess1_0 sup_set_class fsess1_2 wbr isess1_1 fsess1_0 crab cvv ssexg ex syl ralimdv isess1_0 isess1_1 fsess1_0 fsess1_2 df-se isess1_0 isess1_1 fsess1_0 fsess1_1 df-se 3imtr4g $.
$}
$( Subset theorem for the set-like predicate.  (Contributed by Mario
       Carneiro, 24-Jun-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y R $.
	$d x y $.
	isess2_0 $f set x $.
	isess2_1 $f set y $.
	fsess2_0 $f class A $.
	fsess2_1 $f class B $.
	fsess2_2 $f class R $.
	sess2 $p |- ( A C_ B -> ( R Se B -> R Se A ) ) $= fsess2_0 fsess2_1 wss isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab cvv wcel isess2_0 fsess2_1 wral isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 crab cvv wcel isess2_0 fsess2_0 wral fsess2_1 fsess2_2 wse fsess2_0 fsess2_2 wse fsess2_0 fsess2_1 wss isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab cvv wcel isess2_0 fsess2_1 wral isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab cvv wcel isess2_0 fsess2_0 wral isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 crab cvv wcel isess2_0 fsess2_0 wral isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab cvv wcel isess2_0 fsess2_0 fsess2_1 ssralv fsess2_0 fsess2_1 wss isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab cvv wcel isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 crab cvv wcel isess2_0 fsess2_0 fsess2_0 fsess2_1 wss isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 crab isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab wss isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab cvv wcel isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 crab cvv wcel wi isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 fsess2_1 rabss2 isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 crab isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab wss isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab cvv wcel isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 crab cvv wcel isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_0 crab isess2_1 sup_set_class isess2_0 sup_set_class fsess2_2 wbr isess2_1 fsess2_1 crab cvv ssexg ex syl ralimdv syld isess2_0 isess2_1 fsess2_1 fsess2_2 df-se isess2_0 isess2_1 fsess2_0 fsess2_2 df-se 3imtr4g $.
$}
$( Equality theorem for the well-founded predicate.  (Contributed by NM,
       9-Mar-1997.) $)
${
	$d x y z R $.
	$d x y z S $.
	$d x y z A $.
	ifreq1_0 $f set x $.
	ifreq1_1 $f set y $.
	ifreq1_2 $f set z $.
	ffreq1_0 $f class A $.
	ffreq1_1 $f class R $.
	ffreq1_2 $f class S $.
	freq1 $p |- ( R = S -> ( R Fr A <-> S Fr A ) ) $= ffreq1_1 ffreq1_2 wceq ifreq1_0 sup_set_class ffreq1_0 wss ifreq1_0 sup_set_class c0 wne wa ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_1 wbr wn ifreq1_2 ifreq1_0 sup_set_class wral ifreq1_1 ifreq1_0 sup_set_class wrex wi ifreq1_0 wal ifreq1_0 sup_set_class ffreq1_0 wss ifreq1_0 sup_set_class c0 wne wa ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_2 wbr wn ifreq1_2 ifreq1_0 sup_set_class wral ifreq1_1 ifreq1_0 sup_set_class wrex wi ifreq1_0 wal ffreq1_0 ffreq1_1 wfr ffreq1_0 ffreq1_2 wfr ffreq1_1 ffreq1_2 wceq ifreq1_0 sup_set_class ffreq1_0 wss ifreq1_0 sup_set_class c0 wne wa ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_1 wbr wn ifreq1_2 ifreq1_0 sup_set_class wral ifreq1_1 ifreq1_0 sup_set_class wrex wi ifreq1_0 sup_set_class ffreq1_0 wss ifreq1_0 sup_set_class c0 wne wa ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_2 wbr wn ifreq1_2 ifreq1_0 sup_set_class wral ifreq1_1 ifreq1_0 sup_set_class wrex wi ifreq1_0 ffreq1_1 ffreq1_2 wceq ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_1 wbr wn ifreq1_2 ifreq1_0 sup_set_class wral ifreq1_1 ifreq1_0 sup_set_class wrex ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_2 wbr wn ifreq1_2 ifreq1_0 sup_set_class wral ifreq1_1 ifreq1_0 sup_set_class wrex ifreq1_0 sup_set_class ffreq1_0 wss ifreq1_0 sup_set_class c0 wne wa ffreq1_1 ffreq1_2 wceq ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_1 wbr wn ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_2 wbr wn ifreq1_1 ifreq1_2 ifreq1_0 sup_set_class ifreq1_0 sup_set_class ffreq1_1 ffreq1_2 wceq ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_1 wbr ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_2 wbr ifreq1_2 sup_set_class ifreq1_1 sup_set_class ffreq1_1 ffreq1_2 breq notbid rexralbidv imbi2d albidv ifreq1_0 ifreq1_1 ifreq1_2 ffreq1_0 ffreq1_1 df-fr ifreq1_0 ifreq1_1 ifreq1_2 ffreq1_0 ffreq1_2 df-fr 3bitr4g $.
$}
$( Equality theorem for the well-founded predicate.  (Contributed by NM,
     3-Apr-1994.) $)
${
	ffreq2_0 $f class A $.
	ffreq2_1 $f class B $.
	ffreq2_2 $f class R $.
	freq2 $p |- ( A = B -> ( R Fr A <-> R Fr B ) ) $= ffreq2_0 ffreq2_1 wceq ffreq2_0 ffreq2_2 wfr ffreq2_1 ffreq2_2 wfr ffreq2_0 ffreq2_1 wceq ffreq2_1 ffreq2_0 wss ffreq2_0 ffreq2_2 wfr ffreq2_1 ffreq2_2 wfr wi ffreq2_1 ffreq2_0 eqimss2 ffreq2_1 ffreq2_0 ffreq2_2 frss syl ffreq2_0 ffreq2_1 wceq ffreq2_0 ffreq2_1 wss ffreq2_1 ffreq2_2 wfr ffreq2_0 ffreq2_2 wfr wi ffreq2_0 ffreq2_1 eqimss ffreq2_0 ffreq2_1 ffreq2_2 frss syl impbid $.
$}
$( Equality theorem for the set-like predicate.  (Contributed by Mario
     Carneiro, 24-Jun-2015.) $)
${
	fseeq1_0 $f class A $.
	fseeq1_1 $f class R $.
	fseeq1_2 $f class S $.
	seeq1 $p |- ( R = S -> ( R Se A <-> S Se A ) ) $= fseeq1_1 fseeq1_2 wceq fseeq1_0 fseeq1_1 wse fseeq1_0 fseeq1_2 wse fseeq1_1 fseeq1_2 wceq fseeq1_2 fseeq1_1 wss fseeq1_0 fseeq1_1 wse fseeq1_0 fseeq1_2 wse wi fseeq1_2 fseeq1_1 eqimss2 fseeq1_0 fseeq1_2 fseeq1_1 sess1 syl fseeq1_1 fseeq1_2 wceq fseeq1_1 fseeq1_2 wss fseeq1_0 fseeq1_2 wse fseeq1_0 fseeq1_1 wse wi fseeq1_1 fseeq1_2 eqimss fseeq1_0 fseeq1_1 fseeq1_2 sess1 syl impbid $.
$}
$( Equality theorem for the set-like predicate.  (Contributed by Mario
     Carneiro, 24-Jun-2015.) $)
${
	fseeq2_0 $f class A $.
	fseeq2_1 $f class B $.
	fseeq2_2 $f class R $.
	seeq2 $p |- ( A = B -> ( R Se A <-> R Se B ) ) $= fseeq2_0 fseeq2_1 wceq fseeq2_0 fseeq2_2 wse fseeq2_1 fseeq2_2 wse fseeq2_0 fseeq2_1 wceq fseeq2_1 fseeq2_0 wss fseeq2_0 fseeq2_2 wse fseeq2_1 fseeq2_2 wse wi fseeq2_1 fseeq2_0 eqimss2 fseeq2_1 fseeq2_0 fseeq2_2 sess2 syl fseeq2_0 fseeq2_1 wceq fseeq2_0 fseeq2_1 wss fseeq2_1 fseeq2_2 wse fseeq2_0 fseeq2_2 wse wi fseeq2_0 fseeq2_1 eqimss fseeq2_0 fseeq2_1 fseeq2_2 sess2 syl impbid $.
$}
$( Bound-variable hypothesis builder for well-founded relations.
       (Contributed by Stefan O'Rear, 20-Jan-2015.)  (Revised by Mario
       Carneiro, 14-Oct-2016.) $)
${
	$d R a b c $.
	$d A a b c $.
	$d x a b c $.
	inffr_0 $f set a $.
	inffr_1 $f set b $.
	inffr_2 $f set c $.
	fnffr_0 $f set x $.
	fnffr_1 $f class A $.
	fnffr_2 $f class R $.
	enffr_0 $e |- F/_ x R $.
	enffr_1 $e |- F/_ x A $.
	nffr $p |- F/ x R Fr A $= fnffr_1 fnffr_2 wfr inffr_0 sup_set_class fnffr_1 wss inffr_0 sup_set_class c0 wne wa inffr_2 sup_set_class inffr_1 sup_set_class fnffr_2 wbr wn inffr_2 inffr_0 sup_set_class wral inffr_1 inffr_0 sup_set_class wrex wi inffr_0 wal fnffr_0 inffr_0 inffr_1 inffr_2 fnffr_1 fnffr_2 df-fr inffr_0 sup_set_class fnffr_1 wss inffr_0 sup_set_class c0 wne wa inffr_2 sup_set_class inffr_1 sup_set_class fnffr_2 wbr wn inffr_2 inffr_0 sup_set_class wral inffr_1 inffr_0 sup_set_class wrex wi fnffr_0 inffr_0 inffr_0 sup_set_class fnffr_1 wss inffr_0 sup_set_class c0 wne wa inffr_2 sup_set_class inffr_1 sup_set_class fnffr_2 wbr wn inffr_2 inffr_0 sup_set_class wral inffr_1 inffr_0 sup_set_class wrex fnffr_0 inffr_0 sup_set_class fnffr_1 wss inffr_0 sup_set_class c0 wne fnffr_0 fnffr_0 inffr_0 sup_set_class fnffr_1 fnffr_0 inffr_0 sup_set_class nfcv enffr_1 nfss inffr_0 sup_set_class c0 wne fnffr_0 nfv nfan inffr_2 sup_set_class inffr_1 sup_set_class fnffr_2 wbr wn inffr_2 inffr_0 sup_set_class wral fnffr_0 inffr_1 inffr_0 sup_set_class fnffr_0 inffr_0 sup_set_class nfcv inffr_2 sup_set_class inffr_1 sup_set_class fnffr_2 wbr wn fnffr_0 inffr_2 inffr_0 sup_set_class fnffr_0 inffr_0 sup_set_class nfcv inffr_2 sup_set_class inffr_1 sup_set_class fnffr_2 wbr fnffr_0 fnffr_0 inffr_2 sup_set_class inffr_1 sup_set_class fnffr_2 fnffr_0 inffr_2 sup_set_class nfcv enffr_0 fnffr_0 inffr_1 sup_set_class nfcv nfbr nfn nfral nfrex nfim nfal nfxfr $.
$}
$( Bound-variable hypothesis builder for set-like relations.  (Contributed
       by Mario Carneiro, 24-Jun-2015.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
${
	$d R a b $.
	$d A a b $.
	$d x a b $.
	infse_0 $f set a $.
	infse_1 $f set b $.
	fnfse_0 $f set x $.
	fnfse_1 $f class A $.
	fnfse_2 $f class R $.
	enfse_0 $e |- F/_ x R $.
	enfse_1 $e |- F/_ x A $.
	nfse $p |- F/ x R Se A $= fnfse_1 fnfse_2 wse infse_0 sup_set_class infse_1 sup_set_class fnfse_2 wbr infse_0 fnfse_1 crab cvv wcel infse_1 fnfse_1 wral fnfse_0 infse_1 infse_0 fnfse_1 fnfse_2 df-se infse_0 sup_set_class infse_1 sup_set_class fnfse_2 wbr infse_0 fnfse_1 crab cvv wcel fnfse_0 infse_1 fnfse_1 enfse_1 fnfse_0 infse_0 sup_set_class infse_1 sup_set_class fnfse_2 wbr infse_0 fnfse_1 crab cvv infse_0 sup_set_class infse_1 sup_set_class fnfse_2 wbr fnfse_0 infse_0 fnfse_1 fnfse_0 infse_0 sup_set_class infse_1 sup_set_class fnfse_2 fnfse_0 infse_0 sup_set_class nfcv enfse_0 fnfse_0 infse_1 sup_set_class nfcv nfbr enfse_1 nfrab nfel1 nfral nfxfr $.
$}
$( Bound-variable hypothesis builder for well-orderings.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
${
	fnfwe_0 $f set x $.
	fnfwe_1 $f class A $.
	fnfwe_2 $f class R $.
	enfwe_0 $e |- F/_ x R $.
	enfwe_1 $e |- F/_ x A $.
	nfwe $p |- F/ x R We A $= fnfwe_1 fnfwe_2 wwe fnfwe_1 fnfwe_2 wfr fnfwe_1 fnfwe_2 wor wa fnfwe_0 fnfwe_1 fnfwe_2 df-we fnfwe_1 fnfwe_2 wfr fnfwe_1 fnfwe_2 wor fnfwe_0 fnfwe_0 fnfwe_1 fnfwe_2 enfwe_0 enfwe_1 nffr fnfwe_0 fnfwe_1 fnfwe_2 enfwe_0 enfwe_1 nfso nfan nfxfr $.
$}
$( A well-founded relation is irreflexive.  Special case of Proposition
       6.23 of [TakeutiZaring] p. 30.  (Contributed by NM, 2-Jan-1994.)
       (Revised by Mario Carneiro, 22-Jun-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y R $.
	ifrirr_0 $f set x $.
	ifrirr_1 $f set y $.
	ffrirr_0 $f class A $.
	ffrirr_1 $f class B $.
	ffrirr_2 $f class R $.
	frirr $p |- ( ( R Fr A /\ B e. A ) -> -. B R B ) $= ffrirr_0 ffrirr_2 wfr ffrirr_1 ffrirr_0 wcel wa ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr ifrirr_0 ffrirr_1 csn crab c0 wceq ifrirr_1 ffrirr_1 csn wrex ffrirr_1 ffrirr_1 ffrirr_2 wbr wn ffrirr_0 ffrirr_2 wfr ffrirr_1 ffrirr_0 wcel wa ffrirr_0 ffrirr_2 wfr ffrirr_1 csn ffrirr_0 wss ffrirr_1 csn c0 wne ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr ifrirr_0 ffrirr_1 csn crab c0 wceq ifrirr_1 ffrirr_1 csn wrex ffrirr_0 ffrirr_2 wfr ffrirr_1 ffrirr_0 wcel simpl ffrirr_0 ffrirr_2 wfr ffrirr_1 ffrirr_0 wcel wa ffrirr_1 ffrirr_0 ffrirr_0 ffrirr_2 wfr ffrirr_1 ffrirr_0 wcel simpr snssd ffrirr_1 ffrirr_0 wcel ffrirr_1 csn c0 wne ffrirr_0 ffrirr_2 wfr ffrirr_1 ffrirr_0 snnzg adantl ifrirr_1 ifrirr_0 ffrirr_0 ffrirr_1 csn ffrirr_2 ffrirr_1 snex frc syl3anc ffrirr_1 ffrirr_0 wcel ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr ifrirr_0 ffrirr_1 csn crab c0 wceq ifrirr_1 ffrirr_1 csn wrex ffrirr_1 ffrirr_1 ffrirr_2 wbr wn wb ffrirr_0 ffrirr_2 wfr ffrirr_1 ffrirr_0 wcel ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr ifrirr_0 ffrirr_1 csn crab c0 wceq ifrirr_1 ffrirr_1 csn wrex ifrirr_0 sup_set_class ffrirr_1 ffrirr_2 wbr wn ifrirr_0 ffrirr_1 csn wral ffrirr_1 ffrirr_1 ffrirr_2 wbr wn ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr ifrirr_0 ffrirr_1 csn crab c0 wceq ifrirr_0 sup_set_class ffrirr_1 ffrirr_2 wbr wn ifrirr_0 ffrirr_1 csn wral ifrirr_1 ffrirr_1 ffrirr_0 ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr ifrirr_0 ffrirr_1 csn crab c0 wceq ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr wn ifrirr_0 ffrirr_1 csn wral ifrirr_1 sup_set_class ffrirr_1 wceq ifrirr_0 sup_set_class ffrirr_1 ffrirr_2 wbr wn ifrirr_0 ffrirr_1 csn wral ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr ifrirr_0 ffrirr_1 csn rabeq0 ifrirr_1 sup_set_class ffrirr_1 wceq ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr wn ifrirr_0 sup_set_class ffrirr_1 ffrirr_2 wbr wn ifrirr_0 ffrirr_1 csn ifrirr_1 sup_set_class ffrirr_1 wceq ifrirr_0 sup_set_class ifrirr_1 sup_set_class ffrirr_2 wbr ifrirr_0 sup_set_class ffrirr_1 ffrirr_2 wbr ifrirr_1 sup_set_class ffrirr_1 ifrirr_0 sup_set_class ffrirr_2 breq2 notbid ralbidv syl5bb rexsng ifrirr_0 sup_set_class ffrirr_1 ffrirr_2 wbr wn ffrirr_1 ffrirr_1 ffrirr_2 wbr wn ifrirr_0 ffrirr_1 ffrirr_0 ifrirr_0 sup_set_class ffrirr_1 wceq ifrirr_0 sup_set_class ffrirr_1 ffrirr_2 wbr ffrirr_1 ffrirr_1 ffrirr_2 wbr ifrirr_0 sup_set_class ffrirr_1 ffrirr_1 ffrirr_2 breq1 notbid ralsng bitrd adantl mpbid $.
$}
$( A well-founded relation has no 2-cycle loops.  Special case of
       Proposition 6.23 of [TakeutiZaring] p. 30.  (Contributed by NM,
       30-May-1994.)  (Revised by Mario Carneiro, 22-Jun-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y R $.
	ifr2nr_0 $f set x $.
	ifr2nr_1 $f set y $.
	ffr2nr_0 $f class A $.
	ffr2nr_1 $f class B $.
	ffr2nr_2 $f class C $.
	ffr2nr_3 $f class R $.
	fr2nr $p |- ( ( R Fr A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) ) $= ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr wn ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr wn wo ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr wa wn ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr wn ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr wn ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral wo ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr wn ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr wn wo ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ifr2nr_0 sup_set_class ifr2nr_1 sup_set_class ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_1 ffr2nr_1 ffr2nr_2 cpr wrex ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral wo ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ffr2nr_1 ffr2nr_2 cpr cvv wcel ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_2 cpr ffr2nr_0 wss ffr2nr_1 ffr2nr_2 cpr c0 wne ifr2nr_0 sup_set_class ifr2nr_1 sup_set_class ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_1 ffr2nr_1 ffr2nr_2 cpr wrex ffr2nr_1 ffr2nr_2 cpr cvv wcel ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ffr2nr_1 ffr2nr_2 prex a1i ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa simpl ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa ffr2nr_1 ffr2nr_2 cpr ffr2nr_0 wss ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_2 ffr2nr_0 prssi adantl ffr2nr_1 ffr2nr_0 wcel ffr2nr_1 ffr2nr_2 cpr c0 wne ffr2nr_0 ffr2nr_3 wfr ffr2nr_2 ffr2nr_0 wcel ffr2nr_1 ffr2nr_2 ffr2nr_0 prnzg ad2antrl ifr2nr_1 ifr2nr_0 ffr2nr_0 ffr2nr_1 ffr2nr_2 cpr cvv ffr2nr_3 fri syl22anc ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa ifr2nr_0 sup_set_class ifr2nr_1 sup_set_class ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_1 ffr2nr_1 ffr2nr_2 cpr wrex ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral wo wb ffr2nr_0 ffr2nr_3 wfr ifr2nr_0 sup_set_class ifr2nr_1 sup_set_class ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ifr2nr_1 ffr2nr_1 ffr2nr_2 ffr2nr_0 ffr2nr_0 ifr2nr_1 sup_set_class ffr2nr_1 wceq ifr2nr_0 sup_set_class ifr2nr_1 sup_set_class ffr2nr_3 wbr wn ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr ifr2nr_1 sup_set_class ffr2nr_1 wceq ifr2nr_0 sup_set_class ifr2nr_1 sup_set_class ffr2nr_3 wbr ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr ifr2nr_1 sup_set_class ffr2nr_1 ifr2nr_0 sup_set_class ffr2nr_3 breq2 notbid ralbidv ifr2nr_1 sup_set_class ffr2nr_2 wceq ifr2nr_0 sup_set_class ifr2nr_1 sup_set_class ffr2nr_3 wbr wn ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr ifr2nr_1 sup_set_class ffr2nr_2 wceq ifr2nr_0 sup_set_class ifr2nr_1 sup_set_class ffr2nr_3 wbr ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr ifr2nr_1 sup_set_class ffr2nr_2 ifr2nr_0 sup_set_class ffr2nr_3 breq2 notbid ralbidv rexprg adantl mpbid ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr wn ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ffr2nr_2 ffr2nr_1 ffr2nr_2 cpr wcel ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr wn wi ffr2nr_2 ffr2nr_0 wcel ffr2nr_2 ffr2nr_1 ffr2nr_2 cpr wcel ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_1 ffr2nr_2 ffr2nr_0 prid2g ad2antll ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr wn ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_2 ffr2nr_1 ffr2nr_2 cpr ifr2nr_0 sup_set_class ffr2nr_2 wceq ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_3 wbr ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_1 ffr2nr_3 breq1 notbid rspcv syl ffr2nr_0 ffr2nr_3 wfr ffr2nr_1 ffr2nr_0 wcel ffr2nr_2 ffr2nr_0 wcel wa wa ffr2nr_1 ffr2nr_1 ffr2nr_2 cpr wcel ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_2 cpr wral ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr wn wi ffr2nr_1 ffr2nr_0 wcel ffr2nr_1 ffr2nr_1 ffr2nr_2 cpr wcel ffr2nr_0 ffr2nr_3 wfr ffr2nr_2 ffr2nr_0 wcel ffr2nr_1 ffr2nr_2 ffr2nr_0 prid1g ad2antrl ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr wn ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr wn ifr2nr_0 ffr2nr_1 ffr2nr_1 ffr2nr_2 cpr ifr2nr_0 sup_set_class ffr2nr_1 wceq ifr2nr_0 sup_set_class ffr2nr_2 ffr2nr_3 wbr ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr ifr2nr_0 sup_set_class ffr2nr_1 ffr2nr_2 ffr2nr_3 breq1 notbid rspcv syl orim12d mpd orcomd ffr2nr_1 ffr2nr_2 ffr2nr_3 wbr ffr2nr_2 ffr2nr_1 ffr2nr_3 wbr ianor sylibr $.
$}
$( Any relation is well-founded on the empty set.  (Contributed by NM,
       17-Sep-1993.) $)
${
	$d x y z R $.
	ifr0_0 $f set x $.
	ifr0_1 $f set y $.
	ifr0_2 $f set z $.
	ffr0_0 $f class R $.
	fr0 $p |- R Fr (/) $= c0 ffr0_0 wfr ifr0_0 sup_set_class c0 wss ifr0_0 sup_set_class c0 wne wa ifr0_2 sup_set_class ifr0_1 sup_set_class ffr0_0 wbr ifr0_2 ifr0_0 sup_set_class crab c0 wceq ifr0_1 ifr0_0 sup_set_class wrex wi ifr0_0 ifr0_0 ifr0_1 ifr0_2 c0 ffr0_0 dffr2 ifr0_0 sup_set_class c0 wss ifr0_0 sup_set_class c0 wne ifr0_2 sup_set_class ifr0_1 sup_set_class ffr0_0 wbr ifr0_2 ifr0_0 sup_set_class crab c0 wceq ifr0_1 ifr0_0 sup_set_class wrex ifr0_0 sup_set_class c0 wss ifr0_2 sup_set_class ifr0_1 sup_set_class ffr0_0 wbr ifr0_2 ifr0_0 sup_set_class crab c0 wceq ifr0_1 ifr0_0 sup_set_class wrex ifr0_0 sup_set_class c0 ifr0_0 sup_set_class c0 wss ifr0_0 sup_set_class c0 wceq ifr0_2 sup_set_class ifr0_1 sup_set_class ffr0_0 wbr ifr0_2 ifr0_0 sup_set_class crab c0 wceq ifr0_1 ifr0_0 sup_set_class wrex wn ifr0_0 sup_set_class ss0 a1d necon1ad imp mpgbir $.
$}
$( If an element of a well-founded set satisfies a property ` ph ` , then
       there is a minimal element that satisfies ` ph ` .  (Contributed by Jeff
       Madsen, 18-Jun-2010.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)
${
	$d A x y z $.
	$d R x y z $.
	$d ph y z $.
	$d ps x z $.
	ifrminex_0 $f set z $.
	ffrminex_0 $f wff ph $.
	ffrminex_1 $f wff ps $.
	ffrminex_2 $f set x $.
	ffrminex_3 $f set y $.
	ffrminex_4 $f class A $.
	ffrminex_5 $f class R $.
	efrminex_0 $e |- A e. _V $.
	efrminex_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	frminex $p |- ( R Fr A -> ( E. x e. A ph -> E. x e. A ( ph /\ A. y e. A ( ps -> -. y R x ) ) ) ) $= ffrminex_0 ffrminex_2 ffrminex_4 wrex ffrminex_0 ffrminex_2 ffrminex_4 crab c0 wne ffrminex_4 ffrminex_5 wfr ffrminex_0 ffrminex_1 ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral wa ffrminex_2 ffrminex_4 wrex ffrminex_0 ffrminex_2 ffrminex_4 rabn0 ffrminex_4 ffrminex_5 wfr ffrminex_0 ffrminex_2 ffrminex_4 crab c0 wne ffrminex_0 ffrminex_1 ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral wa ffrminex_2 ffrminex_4 wrex ffrminex_0 ffrminex_2 ffrminex_4 crab cvv wcel ffrminex_0 ffrminex_2 ffrminex_4 crab ffrminex_4 wss ffrminex_4 ffrminex_5 wfr ffrminex_0 ffrminex_2 ffrminex_4 crab c0 wne wa ffrminex_0 ffrminex_1 ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral wa ffrminex_2 ffrminex_4 wrex ffrminex_0 ffrminex_2 ffrminex_4 efrminex_0 rabex ffrminex_0 ffrminex_2 ffrminex_4 ssrab2 ffrminex_0 ffrminex_2 ffrminex_4 crab cvv wcel ffrminex_4 ffrminex_5 wfr ffrminex_0 ffrminex_2 ffrminex_4 crab ffrminex_4 wss ffrminex_0 ffrminex_2 ffrminex_4 crab c0 wne ffrminex_0 ffrminex_1 ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral wa ffrminex_2 ffrminex_4 wrex ffrminex_0 ffrminex_2 ffrminex_4 crab cvv wcel ffrminex_4 ffrminex_5 wfr wa ffrminex_0 ffrminex_2 ffrminex_4 crab ffrminex_4 wss ffrminex_0 ffrminex_2 ffrminex_4 crab c0 wne wa wa ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn ffrminex_3 ffrminex_0 ffrminex_2 ffrminex_4 crab wral ifrminex_0 ffrminex_0 ffrminex_2 ffrminex_4 crab wrex ffrminex_0 ffrminex_1 ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral wa ffrminex_2 ffrminex_4 wrex ifrminex_0 ffrminex_3 ffrminex_4 ffrminex_0 ffrminex_2 ffrminex_4 crab cvv ffrminex_5 fri ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn ffrminex_3 ffrminex_0 ffrminex_2 ffrminex_4 crab wral ifrminex_0 ffrminex_0 ffrminex_2 ffrminex_4 crab wrex ffrminex_1 ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral ifrminex_0 ffrminex_0 ffrminex_2 ffrminex_4 crab wrex ffrminex_0 ffrminex_1 ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral wa ffrminex_2 ffrminex_4 wrex ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn ffrminex_3 ffrminex_0 ffrminex_2 ffrminex_4 crab wral ffrminex_1 ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral ifrminex_0 ffrminex_0 ffrminex_2 ffrminex_4 crab ffrminex_0 ffrminex_1 ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn ffrminex_3 ffrminex_2 ffrminex_4 efrminex_1 ralrab rexbii ffrminex_0 ffrminex_1 ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral ffrminex_1 ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 wral ifrminex_0 ffrminex_2 ffrminex_4 ifrminex_0 sup_set_class ffrminex_2 sup_set_class wceq ffrminex_1 ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn wi ffrminex_1 ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn wi ffrminex_3 ffrminex_4 ifrminex_0 sup_set_class ffrminex_2 sup_set_class wceq ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr wn ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr wn ffrminex_1 ifrminex_0 sup_set_class ffrminex_2 sup_set_class wceq ffrminex_3 sup_set_class ifrminex_0 sup_set_class ffrminex_5 wbr ffrminex_3 sup_set_class ffrminex_2 sup_set_class ffrminex_5 wbr ifrminex_0 sup_set_class ffrminex_2 sup_set_class ffrminex_3 sup_set_class ffrminex_5 breq2 notbid imbi2d ralbidv rexrab2 bitri sylib an4s mpanl12 ex syl5bir $.
$}
$( Irreflexivity of the epsilon relation: a class founded by epsilon is not
       a member of itself.  (Contributed by NM, 18-Apr-1994.)  (Revised by
       Mario Carneiro, 22-Jun-2015.) $)
${
	fefrirr_0 $f class A $.
	efrirr $p |- ( _E Fr A -> -. A e. A ) $= fefrirr_0 cep wfr fefrirr_0 fefrirr_0 wcel fefrirr_0 cep wfr fefrirr_0 fefrirr_0 wcel fefrirr_0 fefrirr_0 wcel wn fefrirr_0 cep wfr fefrirr_0 fefrirr_0 wcel wa fefrirr_0 fefrirr_0 cep wbr fefrirr_0 fefrirr_0 wcel fefrirr_0 fefrirr_0 cep frirr fefrirr_0 fefrirr_0 wcel fefrirr_0 fefrirr_0 cep wbr fefrirr_0 fefrirr_0 wcel wb fefrirr_0 cep wfr fefrirr_0 fefrirr_0 fefrirr_0 epelg adantl mtbid ex pm2.01d $.
$}
$( A set founded by epsilon contains no 2-cycle loops.  (Contributed by NM,
     19-Apr-1994.) $)
${
	fefrn2lp_0 $f class A $.
	fefrn2lp_1 $f class B $.
	fefrn2lp_2 $f class C $.
	efrn2lp $p |- ( ( _E Fr A /\ ( B e. A /\ C e. A ) ) -> -. ( B e. C /\ C e. B ) ) $= fefrn2lp_0 cep wfr fefrn2lp_1 fefrn2lp_0 wcel fefrn2lp_2 fefrn2lp_0 wcel wa wa fefrn2lp_1 fefrn2lp_2 cep wbr fefrn2lp_2 fefrn2lp_1 cep wbr wa fefrn2lp_1 fefrn2lp_2 wcel fefrn2lp_2 fefrn2lp_1 wcel wa fefrn2lp_0 fefrn2lp_1 fefrn2lp_2 cep fr2nr fefrn2lp_1 fefrn2lp_0 wcel fefrn2lp_2 fefrn2lp_0 wcel wa fefrn2lp_1 fefrn2lp_2 cep wbr fefrn2lp_2 fefrn2lp_1 cep wbr wa fefrn2lp_1 fefrn2lp_2 wcel fefrn2lp_2 fefrn2lp_1 wcel wa wb fefrn2lp_0 cep wfr fefrn2lp_2 fefrn2lp_0 wcel fefrn2lp_1 fefrn2lp_2 cep wbr fefrn2lp_1 fefrn2lp_2 wcel fefrn2lp_1 fefrn2lp_0 wcel fefrn2lp_2 fefrn2lp_1 cep wbr fefrn2lp_2 fefrn2lp_1 wcel fefrn2lp_1 fefrn2lp_2 fefrn2lp_0 epelg fefrn2lp_2 fefrn2lp_1 fefrn2lp_0 epelg bi2anan9r adantl mtbid $.
$}
$( The epsilon relation is set-like on any class.  (This is the origin of
       the term "set-like": a set-like relation "acts like" the epsilon
       relation of sets and their elements.)  (Contributed by Mario Carneiro,
       22-Jun-2015.) $)
${
	$d x y A $.
	iepse_0 $f set x $.
	iepse_1 $f set y $.
	fepse_0 $f class A $.
	epse $p |- _E Se A $= fepse_0 cep wse iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 fepse_0 crab cvv wcel iepse_0 fepse_0 wral iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 fepse_0 crab cvv wcel iepse_0 fepse_0 iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 fepse_0 crab iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 cab iepse_0 sup_set_class iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 cab cvv iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 iepse_0 sup_set_class iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 sup_set_class iepse_0 sup_set_class wcel iepse_1 iepse_0 epel bicomi abbi2i iepse_0 vex eqeltrri iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 fepse_0 crab iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 cab fepse_0 cin iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 cab iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 fepse_0 dfrab2 iepse_1 sup_set_class iepse_0 sup_set_class cep wbr iepse_1 cab fepse_0 inss1 eqsstri ssexi rgenw iepse_0 iepse_1 fepse_0 cep df-se mpbir $.
$}
$( Similar to Theorem 7.2 of [TakeutiZaring] p. 35, of except that the Axiom
     of Regularity is not required due to antecedent ` _E Fr A ` .
     (Contributed by NM, 4-May-1994.) $)
${
	ftz7.2_0 $f class A $.
	ftz7.2_1 $f class B $.
	tz7.2 $p |- ( ( Tr A /\ _E Fr A /\ B e. A ) -> ( B C_ A /\ B =/= A ) ) $= ftz7.2_0 wtr ftz7.2_0 cep wfr ftz7.2_1 ftz7.2_0 wcel ftz7.2_1 ftz7.2_0 wss ftz7.2_1 ftz7.2_0 wne wa ftz7.2_0 wtr ftz7.2_1 ftz7.2_0 wcel ftz7.2_1 ftz7.2_0 wss ftz7.2_0 cep wfr ftz7.2_1 ftz7.2_0 wne ftz7.2_0 ftz7.2_1 trss ftz7.2_0 cep wfr ftz7.2_1 ftz7.2_0 wcel ftz7.2_1 ftz7.2_0 ftz7.2_0 cep wfr ftz7.2_1 ftz7.2_0 wcel wn ftz7.2_1 ftz7.2_0 wceq ftz7.2_0 ftz7.2_0 wcel wn ftz7.2_0 efrirr ftz7.2_1 ftz7.2_0 wceq ftz7.2_1 ftz7.2_0 wcel ftz7.2_0 ftz7.2_0 wcel ftz7.2_1 ftz7.2_0 ftz7.2_0 eleq1 notbid syl5ibrcom necon2ad anim12ii 3impia $.
$}
$( An alternate way of saying that the epsilon relation is well-founded.
       (Contributed by NM, 17-Feb-2004.)  (Revised by Mario Carneiro,
       23-Jun-2015.) $)
${
	$d x y z A $.
	idfepfr_0 $f set z $.
	fdfepfr_0 $f set x $.
	fdfepfr_1 $f set y $.
	fdfepfr_2 $f class A $.
	dfepfr $p |- ( _E Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x ( x i^i y ) = (/) ) ) $= fdfepfr_2 cep wfr fdfepfr_0 sup_set_class fdfepfr_2 wss fdfepfr_0 sup_set_class c0 wne wa idfepfr_0 sup_set_class fdfepfr_1 sup_set_class cep wbr idfepfr_0 fdfepfr_0 sup_set_class crab c0 wceq fdfepfr_1 fdfepfr_0 sup_set_class wrex wi fdfepfr_0 wal fdfepfr_0 sup_set_class fdfepfr_2 wss fdfepfr_0 sup_set_class c0 wne wa fdfepfr_0 sup_set_class fdfepfr_1 sup_set_class cin c0 wceq fdfepfr_1 fdfepfr_0 sup_set_class wrex wi fdfepfr_0 wal fdfepfr_0 fdfepfr_1 idfepfr_0 fdfepfr_2 cep dffr2 fdfepfr_0 sup_set_class fdfepfr_2 wss fdfepfr_0 sup_set_class c0 wne wa idfepfr_0 sup_set_class fdfepfr_1 sup_set_class cep wbr idfepfr_0 fdfepfr_0 sup_set_class crab c0 wceq fdfepfr_1 fdfepfr_0 sup_set_class wrex wi fdfepfr_0 sup_set_class fdfepfr_2 wss fdfepfr_0 sup_set_class c0 wne wa fdfepfr_0 sup_set_class fdfepfr_1 sup_set_class cin c0 wceq fdfepfr_1 fdfepfr_0 sup_set_class wrex wi fdfepfr_0 idfepfr_0 sup_set_class fdfepfr_1 sup_set_class cep wbr idfepfr_0 fdfepfr_0 sup_set_class crab c0 wceq fdfepfr_1 fdfepfr_0 sup_set_class wrex fdfepfr_0 sup_set_class fdfepfr_1 sup_set_class cin c0 wceq fdfepfr_1 fdfepfr_0 sup_set_class wrex fdfepfr_0 sup_set_class fdfepfr_2 wss fdfepfr_0 sup_set_class c0 wne wa idfepfr_0 sup_set_class fdfepfr_1 sup_set_class cep wbr idfepfr_0 fdfepfr_0 sup_set_class crab c0 wceq fdfepfr_0 sup_set_class fdfepfr_1 sup_set_class cin c0 wceq fdfepfr_1 fdfepfr_0 sup_set_class idfepfr_0 sup_set_class fdfepfr_1 sup_set_class cep wbr idfepfr_0 fdfepfr_0 sup_set_class crab fdfepfr_0 sup_set_class fdfepfr_1 sup_set_class cin c0 idfepfr_0 sup_set_class fdfepfr_1 sup_set_class cep wbr idfepfr_0 fdfepfr_0 sup_set_class crab idfepfr_0 sup_set_class fdfepfr_1 sup_set_class wcel idfepfr_0 fdfepfr_0 sup_set_class crab fdfepfr_0 sup_set_class fdfepfr_1 sup_set_class cin idfepfr_0 sup_set_class fdfepfr_1 sup_set_class cep wbr idfepfr_0 sup_set_class fdfepfr_1 sup_set_class wcel idfepfr_0 fdfepfr_0 sup_set_class idfepfr_0 sup_set_class fdfepfr_1 sup_set_class cep wbr idfepfr_0 sup_set_class fdfepfr_1 sup_set_class wcel wb idfepfr_0 sup_set_class fdfepfr_0 sup_set_class wcel idfepfr_0 fdfepfr_1 epel a1i rabbiia idfepfr_0 fdfepfr_0 sup_set_class fdfepfr_1 sup_set_class dfin5 eqtr4i eqeq1i rexbii imbi2i albii bitri $.
$}
$( A subset of an epsilon-founded class has a minimal element.
       (Contributed by NM, 17-Feb-2004.)  (Revised by David Abernethy,
       22-Feb-2011.) $)
${
	$d x y A $.
	$d x y B $.
	iepfrc_0 $f set y $.
	fepfrc_0 $f set x $.
	fepfrc_1 $f class A $.
	fepfrc_2 $f class B $.
	eepfrc_0 $e |- B e. _V $.
	epfrc $p |- ( ( _E Fr A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) ) $= fepfrc_1 cep wfr fepfrc_2 fepfrc_1 wss fepfrc_2 c0 wne w3a iepfrc_0 sup_set_class fepfrc_0 sup_set_class cep wbr iepfrc_0 fepfrc_2 crab c0 wceq fepfrc_0 fepfrc_2 wrex fepfrc_2 fepfrc_0 sup_set_class cin c0 wceq fepfrc_0 fepfrc_2 wrex fepfrc_0 iepfrc_0 fepfrc_1 fepfrc_2 cep eepfrc_0 frc fepfrc_2 fepfrc_0 sup_set_class cin c0 wceq iepfrc_0 sup_set_class fepfrc_0 sup_set_class cep wbr iepfrc_0 fepfrc_2 crab c0 wceq fepfrc_0 fepfrc_2 fepfrc_2 fepfrc_0 sup_set_class cin iepfrc_0 sup_set_class fepfrc_0 sup_set_class cep wbr iepfrc_0 fepfrc_2 crab c0 fepfrc_2 fepfrc_0 sup_set_class cin iepfrc_0 sup_set_class fepfrc_0 sup_set_class wcel iepfrc_0 fepfrc_2 crab iepfrc_0 sup_set_class fepfrc_0 sup_set_class cep wbr iepfrc_0 fepfrc_2 crab iepfrc_0 fepfrc_2 fepfrc_0 sup_set_class dfin5 iepfrc_0 sup_set_class fepfrc_0 sup_set_class cep wbr iepfrc_0 sup_set_class fepfrc_0 sup_set_class wcel iepfrc_0 fepfrc_2 iepfrc_0 sup_set_class fepfrc_0 sup_set_class cep wbr iepfrc_0 sup_set_class fepfrc_0 sup_set_class wcel wb iepfrc_0 sup_set_class fepfrc_2 wcel iepfrc_0 fepfrc_0 epel a1i rabbiia eqtr4i eqeq1i rexbii sylibr $.
$}
$( Subset theorem for the well-ordering predicate.  Exercise 4 of
     [TakeutiZaring] p. 31.  (Contributed by NM, 19-Apr-1994.) $)
${
	fwess_0 $f class A $.
	fwess_1 $f class B $.
	fwess_2 $f class R $.
	wess $p |- ( A C_ B -> ( R We B -> R We A ) ) $= fwess_0 fwess_1 wss fwess_1 fwess_2 wfr fwess_1 fwess_2 wor wa fwess_0 fwess_2 wfr fwess_0 fwess_2 wor wa fwess_1 fwess_2 wwe fwess_0 fwess_2 wwe fwess_0 fwess_1 wss fwess_1 fwess_2 wfr fwess_0 fwess_2 wfr fwess_1 fwess_2 wor fwess_0 fwess_2 wor fwess_0 fwess_1 fwess_2 frss fwess_0 fwess_1 fwess_2 soss anim12d fwess_1 fwess_2 df-we fwess_0 fwess_2 df-we 3imtr4g $.
$}
$( Equality theorem for the well-ordering predicate.  (Contributed by NM,
     9-Mar-1997.) $)
${
	fweeq1_0 $f class A $.
	fweeq1_1 $f class R $.
	fweeq1_2 $f class S $.
	weeq1 $p |- ( R = S -> ( R We A <-> S We A ) ) $= fweeq1_1 fweeq1_2 wceq fweeq1_0 fweeq1_1 wfr fweeq1_0 fweeq1_1 wor wa fweeq1_0 fweeq1_2 wfr fweeq1_0 fweeq1_2 wor wa fweeq1_0 fweeq1_1 wwe fweeq1_0 fweeq1_2 wwe fweeq1_1 fweeq1_2 wceq fweeq1_0 fweeq1_1 wfr fweeq1_0 fweeq1_2 wfr fweeq1_0 fweeq1_1 wor fweeq1_0 fweeq1_2 wor fweeq1_0 fweeq1_1 fweeq1_2 freq1 fweeq1_0 fweeq1_1 fweeq1_2 soeq1 anbi12d fweeq1_0 fweeq1_1 df-we fweeq1_0 fweeq1_2 df-we 3bitr4g $.
$}
$( Equality theorem for the well-ordering predicate.  (Contributed by NM,
     3-Apr-1994.) $)
${
	fweeq2_0 $f class A $.
	fweeq2_1 $f class B $.
	fweeq2_2 $f class R $.
	weeq2 $p |- ( A = B -> ( R We A <-> R We B ) ) $= fweeq2_0 fweeq2_1 wceq fweeq2_0 fweeq2_2 wfr fweeq2_0 fweeq2_2 wor wa fweeq2_1 fweeq2_2 wfr fweeq2_1 fweeq2_2 wor wa fweeq2_0 fweeq2_2 wwe fweeq2_1 fweeq2_2 wwe fweeq2_0 fweeq2_1 wceq fweeq2_0 fweeq2_2 wfr fweeq2_1 fweeq2_2 wfr fweeq2_0 fweeq2_2 wor fweeq2_1 fweeq2_2 wor fweeq2_0 fweeq2_1 fweeq2_2 freq2 fweeq2_0 fweeq2_1 fweeq2_2 soeq2 anbi12d fweeq2_0 fweeq2_2 df-we fweeq2_1 fweeq2_2 df-we 3bitr4g $.
$}
$( A well-ordering is well-founded.  (Contributed by NM, 22-Apr-1994.) $)
${
	fwefr_0 $f class A $.
	fwefr_1 $f class R $.
	wefr $p |- ( R We A -> R Fr A ) $= fwefr_0 fwefr_1 wwe fwefr_0 fwefr_1 wfr fwefr_0 fwefr_1 wor fwefr_0 fwefr_1 df-we simplbi $.
$}
$( A well-ordering is a strict ordering.  (Contributed by NM,
     16-Mar-1997.) $)
${
	fweso_0 $f class A $.
	fweso_1 $f class R $.
	weso $p |- ( R We A -> R Or A ) $= fweso_0 fweso_1 wwe fweso_0 fweso_1 wfr fweso_0 fweso_1 wor fweso_0 fweso_1 df-we simprbi $.
$}
$( The elements of an epsilon well-ordering are comparable.  (Contributed by
     NM, 17-May-1994.) $)
${
	fwecmpep_0 $f set x $.
	fwecmpep_1 $f set y $.
	fwecmpep_2 $f class A $.
	wecmpep $p |- ( ( _E We A /\ ( x e. A /\ y e. A ) ) -> ( x e. y \/ x = y \/ y e. x ) ) $= fwecmpep_2 cep wwe fwecmpep_2 cep wor fwecmpep_0 sup_set_class fwecmpep_2 wcel fwecmpep_1 sup_set_class fwecmpep_2 wcel wa fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wcel fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wceq fwecmpep_1 sup_set_class fwecmpep_0 sup_set_class wcel w3o fwecmpep_2 cep weso fwecmpep_2 cep wor fwecmpep_0 sup_set_class fwecmpep_2 wcel fwecmpep_1 sup_set_class fwecmpep_2 wcel wa wa fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class cep wbr fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wceq fwecmpep_1 sup_set_class fwecmpep_0 sup_set_class cep wbr w3o fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wcel fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wceq fwecmpep_1 sup_set_class fwecmpep_0 sup_set_class wcel w3o fwecmpep_2 fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class cep solin fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class cep wbr fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wcel fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wceq fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wceq fwecmpep_1 sup_set_class fwecmpep_0 sup_set_class cep wbr fwecmpep_1 sup_set_class fwecmpep_0 sup_set_class wcel fwecmpep_0 fwecmpep_1 epel fwecmpep_0 sup_set_class fwecmpep_1 sup_set_class wceq biid fwecmpep_1 fwecmpep_0 epel 3orbi123i sylib sylan $.
$}
$( An epsilon well-ordering is a transitive relation.  (Contributed by NM,
     22-Apr-1994.) $)
${
	fwetrep_0 $f set x $.
	fwetrep_1 $f set y $.
	fwetrep_2 $f set z $.
	fwetrep_3 $f class A $.
	wetrep $p |- ( ( _E We A /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( ( x e. y /\ y e. z ) -> x e. z ) ) $= fwetrep_3 cep wwe fwetrep_0 sup_set_class fwetrep_3 wcel fwetrep_1 sup_set_class fwetrep_3 wcel fwetrep_2 sup_set_class fwetrep_3 wcel w3a wa fwetrep_0 sup_set_class fwetrep_1 sup_set_class cep wbr fwetrep_1 sup_set_class fwetrep_2 sup_set_class cep wbr wa fwetrep_0 sup_set_class fwetrep_2 sup_set_class cep wbr fwetrep_0 sup_set_class fwetrep_1 sup_set_class wcel fwetrep_1 sup_set_class fwetrep_2 sup_set_class wcel wa fwetrep_0 sup_set_class fwetrep_2 sup_set_class wcel fwetrep_3 cep wwe fwetrep_3 cep wor fwetrep_0 sup_set_class fwetrep_3 wcel fwetrep_1 sup_set_class fwetrep_3 wcel fwetrep_2 sup_set_class fwetrep_3 wcel w3a fwetrep_0 sup_set_class fwetrep_1 sup_set_class cep wbr fwetrep_1 sup_set_class fwetrep_2 sup_set_class cep wbr wa fwetrep_0 sup_set_class fwetrep_2 sup_set_class cep wbr wi fwetrep_3 cep weso fwetrep_3 fwetrep_0 sup_set_class fwetrep_1 sup_set_class fwetrep_2 sup_set_class cep sotr sylan fwetrep_0 sup_set_class fwetrep_1 sup_set_class cep wbr fwetrep_0 sup_set_class fwetrep_1 sup_set_class wcel fwetrep_1 sup_set_class fwetrep_2 sup_set_class cep wbr fwetrep_1 sup_set_class fwetrep_2 sup_set_class wcel fwetrep_0 fwetrep_1 epel fwetrep_1 fwetrep_2 epel anbi12i fwetrep_0 fwetrep_2 epel 3imtr3g $.
$}
$( A non-empty (possibly proper) subclass of a class well-ordered by ` _E `
       has a minimal element.  Special case of Proposition 6.26 of
       [TakeutiZaring] p. 31.  (Contributed by NM, 17-Feb-2004.) $)
${
	$d x y z $.
	$d y z A $.
	$d x y z B $.
	iwefrc_0 $f set y $.
	iwefrc_1 $f set z $.
	fwefrc_0 $f set x $.
	fwefrc_1 $f class A $.
	fwefrc_2 $f class B $.
	wefrc $p |- ( ( _E We A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) ) $= fwefrc_1 cep wwe fwefrc_2 fwefrc_1 wss fwefrc_2 c0 wne fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex fwefrc_2 fwefrc_1 wss fwefrc_1 cep wwe fwefrc_2 cep wwe fwefrc_2 c0 wne fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex wi fwefrc_2 fwefrc_1 cep wess fwefrc_2 c0 wne iwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_0 wex fwefrc_2 cep wwe fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex iwefrc_0 fwefrc_2 n0 fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex iwefrc_0 fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex fwefrc_2 iwefrc_0 sup_set_class cin c0 iwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_2 iwefrc_0 sup_set_class cin c0 wceq fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex wi fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_2 iwefrc_0 sup_set_class cin c0 wceq fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_2 iwefrc_0 sup_set_class cin c0 wceq fwefrc_0 iwefrc_0 sup_set_class fwefrc_2 fwefrc_0 sup_set_class iwefrc_0 sup_set_class wceq fwefrc_2 fwefrc_0 sup_set_class cin fwefrc_2 iwefrc_0 sup_set_class cin c0 fwefrc_0 sup_set_class iwefrc_0 sup_set_class fwefrc_2 ineq2 eqeq1d rspcev ex adantl fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_2 iwefrc_0 sup_set_class cin c0 wne fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq wa fwefrc_0 fwefrc_2 wrex fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 wrex fwefrc_2 cep wwe fwefrc_2 iwefrc_0 sup_set_class cin c0 wne fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq wa fwefrc_0 fwefrc_2 wrex wi iwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_2 cep wwe fwefrc_2 iwefrc_0 sup_set_class cin c0 wne fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 iwefrc_0 sup_set_class cin wrex fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq wa fwefrc_0 fwefrc_2 wrex fwefrc_2 cep wwe fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_2 wss fwefrc_2 iwefrc_0 sup_set_class cin c0 wne fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 iwefrc_0 sup_set_class cin wrex wi fwefrc_2 iwefrc_0 sup_set_class inss1 fwefrc_2 cep wwe fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_2 wss fwefrc_2 iwefrc_0 sup_set_class cin c0 wne fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 iwefrc_0 sup_set_class cin wrex fwefrc_2 cep wwe fwefrc_2 cep wfr fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_2 wss fwefrc_2 iwefrc_0 sup_set_class cin c0 wne fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 iwefrc_0 sup_set_class cin wrex fwefrc_2 cep wefr fwefrc_0 fwefrc_2 fwefrc_2 iwefrc_0 sup_set_class cin iwefrc_0 sup_set_class fwefrc_2 iwefrc_0 vex inex2 epfrc syl3an1 3exp mpi fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq wa fwefrc_0 fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_2 fwefrc_0 sup_set_class fwefrc_2 iwefrc_0 sup_set_class cin wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq wa fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel wa fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq wa fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq wa wa fwefrc_0 sup_set_class fwefrc_2 iwefrc_0 sup_set_class cin wcel fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel wa fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 sup_set_class fwefrc_2 iwefrc_0 sup_set_class elin anbi1i fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq anass bitri rexbii2 syl6ib adantr fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq wa fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_0 fwefrc_2 fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq wi fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel wa fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class wss fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq wi fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel wa iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 fwefrc_2 fwefrc_0 sup_set_class cin wral fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class wss fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel wa iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 fwefrc_2 fwefrc_0 sup_set_class cin fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa iwefrc_1 sup_set_class fwefrc_2 fwefrc_0 sup_set_class cin wcel fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel wa iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa iwefrc_1 sup_set_class fwefrc_2 fwefrc_0 sup_set_class cin wcel fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class fwefrc_2 fwefrc_0 sup_set_class cin wcel iwefrc_1 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_0 sup_set_class wcel wa fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel wi wi iwefrc_1 sup_set_class fwefrc_2 fwefrc_0 sup_set_class elin fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa iwefrc_1 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_0 sup_set_class wcel fwefrc_0 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel wi wi fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel wa iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_0 sup_set_class wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel wi fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_0 sup_set_class wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel wi wi wi wi fwefrc_2 cep wwe iwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_0 sup_set_class wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel wi wi iwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class fwefrc_2 wcel wa fwefrc_2 cep wwe iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_0 sup_set_class fwefrc_2 wcel w3a iwefrc_1 sup_set_class fwefrc_0 sup_set_class wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel wi wi iwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_2 wcel wa fwefrc_0 sup_set_class fwefrc_2 wcel wa iwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel w3a iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_0 sup_set_class fwefrc_2 wcel w3a iwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel df-3an iwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel 3anrot bitr3i fwefrc_2 cep wwe iwefrc_1 sup_set_class fwefrc_2 wcel fwefrc_0 sup_set_class fwefrc_2 wcel iwefrc_0 sup_set_class fwefrc_2 wcel w3a wa iwefrc_1 sup_set_class fwefrc_0 sup_set_class wcel fwefrc_0 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 sup_set_class iwefrc_0 sup_set_class wcel iwefrc_1 fwefrc_0 iwefrc_0 fwefrc_2 wetrep exp3a sylan2b exp44 imp com34 imp3a syl5bi imp4a com23 ralrimdv iwefrc_1 fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class dfss3 syl6ibr fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class wss fwefrc_2 fwefrc_0 sup_set_class cin c0 wceq fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 wceq fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class wss fwefrc_2 fwefrc_0 sup_set_class cin fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin c0 fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class wss fwefrc_2 fwefrc_0 sup_set_class cin fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin wceq fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class wss fwefrc_2 fwefrc_0 sup_set_class cin fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class cin wceq fwefrc_2 fwefrc_0 sup_set_class cin fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin wceq fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class dfss fwefrc_2 fwefrc_0 sup_set_class cin iwefrc_0 sup_set_class cin fwefrc_2 iwefrc_0 sup_set_class cin fwefrc_0 sup_set_class cin fwefrc_2 fwefrc_0 sup_set_class cin fwefrc_2 fwefrc_0 sup_set_class iwefrc_0 sup_set_class in32 eqeq2i bitri biimpi eqeq1d biimprd syl6 exp3a imp4a reximdvai syld pm2.61dne ex exlimdv syl5bi syl6com 3imp $.
$}
$( Any relation is a well-ordering of the empty set.  (Contributed by NM,
     16-Mar-1997.) $)
${
	fwe0_0 $f class R $.
	we0 $p |- R We (/) $= c0 fwe0_0 wwe c0 fwe0_0 wfr c0 fwe0_0 wor fwe0_0 fr0 fwe0_0 so0 c0 fwe0_0 df-we mpbir2an $.
$}
$( A subset of a well-ordered set has a unique minimal element.
       (Contributed by NM, 18-Mar-1997.)  (Revised by Mario Carneiro,
       28-Apr-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y R $.
	fwereu_0 $f set x $.
	fwereu_1 $f set y $.
	fwereu_2 $f class A $.
	fwereu_3 $f class B $.
	fwereu_4 $f class R $.
	fwereu_5 $f class V $.
	wereu $p |- ( ( R We A /\ ( B e. V /\ B C_ A /\ B =/= (/) ) ) -> E! x e. B A. y e. B -. y R x ) $= fwereu_2 fwereu_4 wwe fwereu_3 fwereu_5 wcel fwereu_3 fwereu_2 wss fwereu_3 c0 wne w3a wa fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 wrex fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 wrmo fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 wreu fwereu_2 fwereu_4 wwe fwereu_2 fwereu_4 wfr fwereu_3 fwereu_5 wcel fwereu_3 fwereu_2 wss fwereu_3 c0 wne w3a fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 wrex fwereu_2 fwereu_4 wefr fwereu_2 fwereu_4 wfr fwereu_3 fwereu_5 wcel fwereu_3 fwereu_2 wss fwereu_3 c0 wne fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 wrex fwereu_3 fwereu_5 wcel fwereu_2 fwereu_4 wfr fwereu_3 fwereu_2 wss fwereu_3 c0 wne fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 wrex wi wi fwereu_3 fwereu_5 wcel fwereu_2 fwereu_4 wfr wa fwereu_3 fwereu_2 wss fwereu_3 c0 wne fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 wrex fwereu_0 fwereu_1 fwereu_2 fwereu_3 fwereu_5 fwereu_4 fri exp32 expcom 3imp2 sylan fwereu_2 fwereu_4 wwe fwereu_3 fwereu_5 wcel fwereu_3 fwereu_2 wss fwereu_3 c0 wne w3a wa fwereu_3 fwereu_4 wor fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 wrmo fwereu_2 fwereu_4 wwe fwereu_3 fwereu_5 wcel fwereu_3 fwereu_2 wss fwereu_3 c0 wne w3a wa fwereu_3 fwereu_2 wss fwereu_2 fwereu_4 wor fwereu_3 fwereu_4 wor fwereu_2 fwereu_4 wwe fwereu_3 fwereu_5 wcel fwereu_3 fwereu_2 wss fwereu_3 c0 wne simpr2 fwereu_2 fwereu_4 wwe fwereu_2 fwereu_4 wor fwereu_3 fwereu_5 wcel fwereu_3 fwereu_2 wss fwereu_3 c0 wne w3a fwereu_2 fwereu_4 weso adantr fwereu_3 fwereu_2 fwereu_4 soss sylc fwereu_0 fwereu_1 fwereu_3 fwereu_4 somo syl fwereu_1 sup_set_class fwereu_0 sup_set_class fwereu_4 wbr wn fwereu_1 fwereu_3 wral fwereu_0 fwereu_3 reu5 sylanbrc $.
$}
$( All nonempty (possibly proper) subclasses of ` A ` , which has a
       well-founded relation ` R ` , have ` R `-minimal elements.  Proposition
       6.26 of [TakeutiZaring] p. 31.  (Contributed by Scott Fenton,
       29-Jan-2011.)  (Revised by Mario Carneiro, 24-Jun-2015.) $)
${
	$d x y z A $.
	$d w x y z B $.
	$d w x y z R $.
	iwereu2_0 $f set z $.
	iwereu2_1 $f set w $.
	fwereu2_0 $f set x $.
	fwereu2_1 $f set y $.
	fwereu2_2 $f class A $.
	fwereu2_3 $f class B $.
	fwereu2_4 $f class R $.
	wereu2 $p |- ( ( ( R We A /\ R Se A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E! x e. B A. y e. B -. y R x ) $= fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss fwereu2_3 c0 wne wa wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrmo fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wreu fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss fwereu2_3 c0 wne fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex fwereu2_3 c0 wne iwereu2_0 sup_set_class fwereu2_3 wcel iwereu2_0 wex fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex iwereu2_0 fwereu2_3 n0 fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss wa iwereu2_0 sup_set_class fwereu2_3 wcel fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex iwereu2_0 fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab c0 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab c0 wceq iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 fwereu2_3 wral fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 rabeq0 iwereu2_0 sup_set_class fwereu2_3 wcel iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 fwereu2_3 wral fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex wi fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 fwereu2_3 wral fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 fwereu2_3 wral fwereu2_0 iwereu2_0 sup_set_class fwereu2_3 fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral iwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 fwereu2_3 wral fwereu2_0 sup_set_class iwereu2_0 sup_set_class wceq iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 fwereu2_3 wral fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 fwereu2_3 fwereu2_1 sup_set_class iwereu2_1 sup_set_class wceq fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class iwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 breq1 notbid cbvralv fwereu2_0 sup_set_class iwereu2_0 sup_set_class wceq iwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wn iwereu2_1 fwereu2_3 fwereu2_0 sup_set_class iwereu2_0 sup_set_class wceq iwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_0 sup_set_class iwereu2_0 sup_set_class iwereu2_1 sup_set_class fwereu2_4 breq2 notbid ralbidv syl5bb rspcev ex ad2antll syl5bi fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab c0 wne fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral fwereu2_0 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wrex fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab cvv wcel fwereu2_2 fwereu2_4 wfr iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab fwereu2_2 wss iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab c0 wne fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral fwereu2_0 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wrex wi fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_3 fwereu2_4 wse iwereu2_0 sup_set_class fwereu2_3 wcel iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab cvv wcel fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_3 fwereu2_2 wss fwereu2_2 fwereu2_4 wse fwereu2_3 fwereu2_4 wse fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel simprl fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa simplr fwereu2_3 fwereu2_2 fwereu2_4 sess2 sylc fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel simprr iwereu2_1 fwereu2_3 iwereu2_0 sup_set_class fwereu2_4 seex syl2anc fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wfr fwereu2_2 fwereu2_4 wse fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_2 fwereu2_4 wefr ad2antrr fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab fwereu2_3 fwereu2_2 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 ssrab2 fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel simprl syl5ss iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab cvv wcel fwereu2_2 fwereu2_4 wfr wa iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab fwereu2_2 wss iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab c0 wne fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral fwereu2_0 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wrex fwereu2_0 fwereu2_1 fwereu2_2 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab cvv fwereu2_4 fri expr syl21anc fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral fwereu2_0 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wrex fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral wa fwereu2_0 fwereu2_3 wrex fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrex iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral fwereu2_0 iwereu2_1 fwereu2_3 iwereu2_1 sup_set_class fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 breq1 rexrab fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr iwereu2_1 fwereu2_3 crab wral fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn wi fwereu2_1 fwereu2_3 wral fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral iwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 iwereu2_1 fwereu2_3 iwereu2_1 sup_set_class fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 breq1 ralrab fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wa fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn wi fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wa fwereu2_1 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wa fwereu2_1 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class fwereu2_3 wcel fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wi fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class fwereu2_3 wcel wa fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class fwereu2_3 wcel wa fwereu2_3 fwereu2_4 wor fwereu2_1 sup_set_class fwereu2_3 wcel fwereu2_0 sup_set_class fwereu2_3 wcel iwereu2_0 sup_set_class fwereu2_3 wcel fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wa fwereu2_1 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wi fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_3 fwereu2_4 wor fwereu2_0 sup_set_class fwereu2_3 wcel fwereu2_1 sup_set_class fwereu2_3 wcel fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_3 fwereu2_2 wss fwereu2_2 fwereu2_4 wor fwereu2_3 fwereu2_4 wor fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel simprl fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wor fwereu2_2 fwereu2_4 wse fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_2 fwereu2_4 weso ad2antrr fwereu2_3 fwereu2_2 fwereu2_4 soss sylc ad2antrr fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class fwereu2_3 wcel simpr fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel fwereu2_1 sup_set_class fwereu2_3 wcel simplr fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa iwereu2_0 sup_set_class fwereu2_3 wcel fwereu2_0 sup_set_class fwereu2_3 wcel fwereu2_1 sup_set_class fwereu2_3 wcel fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel simprr ad2antrr fwereu2_3 fwereu2_1 sup_set_class fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 sotr syl13anc ancomsd expdimp an32s con3d fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss iwereu2_0 sup_set_class fwereu2_3 wcel wa wa fwereu2_0 sup_set_class fwereu2_3 wcel wa fwereu2_0 sup_set_class iwereu2_0 sup_set_class fwereu2_4 wbr wa fwereu2_1 sup_set_class fwereu2_3 wcel wa fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn idd jad ralimdva syl5bi expimpd reximdva syl5bi syld pm2.61dne expr exlimdv syl5bi impr fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss fwereu2_3 c0 wne wa wa fwereu2_3 fwereu2_4 wor fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 wrmo fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss fwereu2_3 c0 wne wa wa fwereu2_3 fwereu2_2 wss fwereu2_2 fwereu2_4 wor fwereu2_3 fwereu2_4 wor fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wse wa fwereu2_3 fwereu2_2 wss fwereu2_3 c0 wne simprl fwereu2_2 fwereu2_4 wwe fwereu2_2 fwereu2_4 wor fwereu2_2 fwereu2_4 wse fwereu2_3 fwereu2_2 wss fwereu2_3 c0 wne wa fwereu2_2 fwereu2_4 weso ad2antrr fwereu2_3 fwereu2_2 fwereu2_4 soss sylc fwereu2_0 fwereu2_1 fwereu2_3 fwereu2_4 somo syl fwereu2_1 sup_set_class fwereu2_0 sup_set_class fwereu2_4 wbr wn fwereu2_1 fwereu2_3 wral fwereu2_0 fwereu2_3 reu5 sylanbrc $.
$}

