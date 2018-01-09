$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Proper_subset_relation.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            Iota properties

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( The value of a function that is expressed as an ordered pair
       abstraction.  (Contributed by NM, 19-Feb-2006.)  (Revised by Mario
       Carneiro, 11-Sep-2015.) $)
${
	$d x y z A $.
	$d z F $.
	$d x ps $.
	ifvopab5_0 $f set z $.
	ffvopab5_0 $f wff ph $.
	ffvopab5_1 $f wff ps $.
	ffvopab5_2 $f set x $.
	ffvopab5_3 $f set y $.
	ffvopab5_4 $f class A $.
	ffvopab5_5 $f class F $.
	ffvopab5_6 $f class V $.
	efvopab5_0 $e |- F = { <. x , y >. | ph } $.
	efvopab5_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	fvopab5 $p |- ( A e. V -> ( F ` A ) = ( iota y ps ) ) $= ffvopab5_4 ffvopab5_6 wcel ffvopab5_4 cvv wcel ffvopab5_4 ffvopab5_5 cfv ffvopab5_1 ffvopab5_3 cio wceq ffvopab5_4 ffvopab5_6 elex ffvopab5_4 cvv wcel ffvopab5_4 ffvopab5_5 cfv ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_3 cio ffvopab5_1 ffvopab5_3 cio ffvopab5_4 ffvopab5_5 cfv ffvopab5_4 ifvopab5_0 sup_set_class ffvopab5_5 wbr ifvopab5_0 cio ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_3 cio ifvopab5_0 ffvopab5_4 ffvopab5_5 df-fv ffvopab5_4 ifvopab5_0 sup_set_class ffvopab5_5 wbr ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 wbr ifvopab5_0 ffvopab5_3 ifvopab5_0 sup_set_class ffvopab5_3 sup_set_class ffvopab5_4 ffvopab5_5 breq2 ffvopab5_3 ffvopab5_4 ifvopab5_0 sup_set_class ffvopab5_5 ffvopab5_3 ffvopab5_4 nfcv ffvopab5_3 ffvopab5_5 ffvopab5_0 ffvopab5_2 ffvopab5_3 copab efvopab5_0 ffvopab5_0 ffvopab5_2 ffvopab5_3 nfopab2 nfcxfr ffvopab5_3 ifvopab5_0 sup_set_class nfcv nfbr ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 wbr ifvopab5_0 nfv cbviota eqtri ffvopab5_4 cvv wcel ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_1 ffvopab5_3 ffvopab5_2 sup_set_class ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_0 wb ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_1 wb ffvopab5_2 ffvopab5_4 cvv ffvopab5_2 ffvopab5_4 nfcv ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_1 ffvopab5_2 ffvopab5_2 ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 ffvopab5_2 ffvopab5_4 nfcv ffvopab5_2 ffvopab5_5 ffvopab5_0 ffvopab5_2 ffvopab5_3 copab efvopab5_0 ffvopab5_0 ffvopab5_2 ffvopab5_3 nfopab1 nfcxfr ffvopab5_2 ffvopab5_3 sup_set_class nfcv nfbr ffvopab5_1 ffvopab5_2 nfv nfbi ffvopab5_2 sup_set_class ffvopab5_4 wceq ffvopab5_2 sup_set_class ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_0 ffvopab5_1 ffvopab5_2 sup_set_class ffvopab5_4 ffvopab5_3 sup_set_class ffvopab5_5 breq1 efvopab5_1 bibi12d ffvopab5_2 sup_set_class ffvopab5_3 sup_set_class ffvopab5_5 wbr ffvopab5_2 sup_set_class ffvopab5_3 sup_set_class cop ffvopab5_5 wcel ffvopab5_2 sup_set_class ffvopab5_3 sup_set_class cop ffvopab5_0 ffvopab5_2 ffvopab5_3 copab wcel ffvopab5_0 ffvopab5_2 sup_set_class ffvopab5_3 sup_set_class ffvopab5_5 df-br ffvopab5_5 ffvopab5_0 ffvopab5_2 ffvopab5_3 copab ffvopab5_2 sup_set_class ffvopab5_3 sup_set_class cop efvopab5_0 eleq2i ffvopab5_0 ffvopab5_2 ffvopab5_3 opabid 3bitri vtoclgf iotabidv syl5eq syl $.
$}
$( The property of a uniquely specified ordered pair.  (Contributed by
       Mario Carneiro, 21-May-2015.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d y ch $.
	$d z ph $.
	$d x y z D $.
	$d x ps $.
	fopiota_0 $f wff ph $.
	fopiota_1 $f wff ps $.
	fopiota_2 $f wff ch $.
	fopiota_3 $f set x $.
	fopiota_4 $f set y $.
	fopiota_5 $f set z $.
	fopiota_6 $f class A $.
	fopiota_7 $f class B $.
	fopiota_8 $f class C $.
	fopiota_9 $f class D $.
	fopiota_10 $f class I $.
	fopiota_11 $f class X $.
	fopiota_12 $f class Y $.
	eopiota_0 $e |- I = ( iota z E. x e. A E. y e. B ( z = <. x , y >. /\ ph ) ) $.
	eopiota_1 $e |- X = ( 1st ` I ) $.
	eopiota_2 $e |- Y = ( 2nd ` I ) $.
	eopiota_3 $e |- ( x = C -> ( ph <-> ps ) ) $.
	eopiota_4 $e |- ( y = D -> ( ps <-> ch ) ) $.
	opiota $p |- ( E! z E. x e. A E. y e. B ( z = <. x , y >. /\ ph ) -> ( ( C e. A /\ D e. B /\ ch ) <-> ( C = X /\ D = Y ) ) ) $= fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_2 wa fopiota_8 fopiota_9 cop fopiota_10 c1st cfv fopiota_10 c2nd cfv cop wceq fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel fopiota_2 w3a fopiota_8 fopiota_11 wceq fopiota_9 fopiota_12 wceq wa fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_2 wa fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_8 fopiota_9 cop fopiota_10 wceq wa fopiota_8 fopiota_9 cop fopiota_10 wceq fopiota_8 fopiota_9 cop fopiota_10 c1st cfv fopiota_10 c2nd cfv cop wceq fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_2 fopiota_8 fopiota_9 cop fopiota_10 wceq fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_2 fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_8 fopiota_9 cop fopiota_10 wceq fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_2 fopiota_0 fopiota_1 fopiota_2 fopiota_3 fopiota_4 fopiota_8 fopiota_9 fopiota_6 fopiota_7 eopiota_3 eopiota_4 ceqsrex2v bicomd fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cio fopiota_8 fopiota_9 cop wceq fopiota_8 fopiota_9 cop fopiota_10 wceq fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 fopiota_8 fopiota_9 cop cvv fopiota_8 fopiota_9 cop cvv wcel fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_8 fopiota_9 opex a1i fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu id fopiota_5 sup_set_class fopiota_8 fopiota_9 cop wceq fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex wb fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_5 sup_set_class fopiota_8 fopiota_9 cop wceq fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_0 wa fopiota_3 fopiota_4 fopiota_6 fopiota_7 fopiota_5 sup_set_class fopiota_8 fopiota_9 cop wceq fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_0 fopiota_5 sup_set_class fopiota_8 fopiota_9 cop wceq fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_8 fopiota_9 cop fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_5 sup_set_class fopiota_8 fopiota_9 cop fopiota_3 sup_set_class fopiota_4 sup_set_class cop eqeq1 fopiota_8 fopiota_9 cop fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_3 sup_set_class fopiota_4 sup_set_class cop fopiota_8 fopiota_9 cop wceq fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_8 fopiota_9 cop fopiota_3 sup_set_class fopiota_4 sup_set_class cop eqcom fopiota_3 sup_set_class fopiota_4 sup_set_class fopiota_8 fopiota_9 fopiota_3 vex fopiota_4 vex opth bitri syl6bb anbi1d 2rexbidv adantl fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 nfeu1 fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_3 sup_set_class fopiota_8 wceq fopiota_4 sup_set_class fopiota_9 wceq wa fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 nfvd fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_5 fopiota_8 fopiota_9 cop nfcvd iota2df fopiota_8 fopiota_9 cop fopiota_10 wceq fopiota_10 fopiota_8 fopiota_9 cop wceq fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cio fopiota_8 fopiota_9 cop wceq fopiota_8 fopiota_9 cop fopiota_10 eqcom fopiota_10 fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cio fopiota_8 fopiota_9 cop eopiota_0 eqeq1i bitri syl6bbr sylan9bbr pm5.32da fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_8 fopiota_9 cop fopiota_10 wceq fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_8 fopiota_9 cop fopiota_10 wceq fopiota_10 fopiota_6 fopiota_7 cxp wcel fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_10 fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cio fopiota_6 fopiota_7 cxp eopiota_0 fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cab fopiota_6 fopiota_7 cxp fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cio fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 fopiota_6 fopiota_7 cxp fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_5 sup_set_class fopiota_6 fopiota_7 cxp wcel fopiota_3 fopiota_4 fopiota_6 fopiota_7 fopiota_3 sup_set_class fopiota_6 wcel fopiota_4 sup_set_class fopiota_7 wcel wa fopiota_5 sup_set_class fopiota_6 fopiota_7 cxp wcel fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_3 sup_set_class fopiota_4 sup_set_class cop fopiota_6 fopiota_7 cxp wcel fopiota_3 sup_set_class fopiota_4 sup_set_class fopiota_6 fopiota_7 opelxpi fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop fopiota_6 fopiota_7 cxp fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 simpl eleq1d syl5ibrcom rexlimivv abssi fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 iotacl sseldi syl5eqel fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel wa fopiota_8 fopiota_9 cop fopiota_6 fopiota_7 cxp wcel fopiota_8 fopiota_9 cop fopiota_10 wceq fopiota_10 fopiota_6 fopiota_7 cxp wcel fopiota_8 fopiota_9 fopiota_6 fopiota_7 opelxp fopiota_8 fopiota_9 cop fopiota_10 fopiota_6 fopiota_7 cxp eleq1 syl5bbr syl5ibrcom pm4.71rd fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_10 fopiota_10 c1st cfv fopiota_10 c2nd cfv cop fopiota_8 fopiota_9 cop fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_10 fopiota_6 fopiota_7 cxp wcel fopiota_10 fopiota_10 c1st cfv fopiota_10 c2nd cfv cop wceq fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_10 fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cio fopiota_6 fopiota_7 cxp eopiota_0 fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 weu fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cab fopiota_6 fopiota_7 cxp fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 cio fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 fopiota_6 fopiota_7 cxp fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_5 sup_set_class fopiota_6 fopiota_7 cxp wcel fopiota_3 fopiota_4 fopiota_6 fopiota_7 fopiota_3 sup_set_class fopiota_6 wcel fopiota_4 sup_set_class fopiota_7 wcel wa fopiota_5 sup_set_class fopiota_6 fopiota_7 cxp wcel fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_3 sup_set_class fopiota_4 sup_set_class cop fopiota_6 fopiota_7 cxp wcel fopiota_3 sup_set_class fopiota_4 sup_set_class fopiota_6 fopiota_7 opelxpi fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop fopiota_6 fopiota_7 cxp fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 simpl eleq1d syl5ibrcom rexlimivv abssi fopiota_5 sup_set_class fopiota_3 sup_set_class fopiota_4 sup_set_class cop wceq fopiota_0 wa fopiota_4 fopiota_7 wrex fopiota_3 fopiota_6 wrex fopiota_5 iotacl sseldi syl5eqel fopiota_10 fopiota_6 fopiota_7 1st2nd2 syl eqeq2d 3bitr2d fopiota_8 fopiota_6 wcel fopiota_9 fopiota_7 wcel fopiota_2 df-3an fopiota_8 fopiota_11 wceq fopiota_9 fopiota_12 wceq wa fopiota_8 fopiota_10 c1st cfv wceq fopiota_9 fopiota_10 c2nd cfv wceq wa fopiota_8 fopiota_9 cop fopiota_10 c1st cfv fopiota_10 c2nd cfv cop wceq fopiota_8 fopiota_11 wceq fopiota_8 fopiota_10 c1st cfv wceq fopiota_9 fopiota_12 wceq fopiota_9 fopiota_10 c2nd cfv wceq fopiota_11 fopiota_10 c1st cfv fopiota_8 eopiota_1 eqeq2i fopiota_12 fopiota_10 c2nd cfv fopiota_9 eopiota_2 eqeq2i anbi12i fopiota_8 fopiota_9 fopiota_10 c1st cfv fopiota_10 c2nd cfv fopiota_10 c1st fvex fopiota_10 c2nd fvex opth2 bitr4i 3bitr4g $.
$}
$( Define a function whose value is "the unique ` y ` such that
       ` ph ( x , y ) ` ".  (Contributed by NM, 19-May-2015.) $)
${
	$d x y z $.
	$d x y z F $.
	$d z ph $.
	$d x z $.
	iopabiotafun_0 $f set z $.
	fopabiotafun_0 $f wff ph $.
	fopabiotafun_1 $f set x $.
	fopabiotafun_2 $f set y $.
	fopabiotafun_3 $f class F $.
	eopabiotafun_0 $e |- F = { <. x , y >. | { y | ph } = { y } } $.
	opabiotafun $p |- Fun F $= fopabiotafun_3 wfun fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class csn wceq fopabiotafun_1 fopabiotafun_2 copab wfun fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class csn wceq fopabiotafun_1 fopabiotafun_2 copab wfun fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class csn wceq fopabiotafun_2 wmo fopabiotafun_1 fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class csn wceq fopabiotafun_1 fopabiotafun_2 funopab fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class csn wceq fopabiotafun_2 wmo fopabiotafun_0 fopabiotafun_2 cab iopabiotafun_0 sup_set_class csn wceq iopabiotafun_0 wmo fopabiotafun_0 fopabiotafun_2 cab iopabiotafun_0 sup_set_class csn wceq iopabiotafun_0 sup_set_class fopabiotafun_0 fopabiotafun_2 cab cuni wceq wi fopabiotafun_0 fopabiotafun_2 cab iopabiotafun_0 sup_set_class csn wceq iopabiotafun_0 wmo iopabiotafun_0 fopabiotafun_0 fopabiotafun_2 cab iopabiotafun_0 sup_set_class csn wceq iopabiotafun_0 fopabiotafun_0 fopabiotafun_2 cab cuni mo2icl fopabiotafun_0 fopabiotafun_2 cab iopabiotafun_0 sup_set_class csn wceq fopabiotafun_0 fopabiotafun_2 cab cuni iopabiotafun_0 sup_set_class csn cuni iopabiotafun_0 sup_set_class fopabiotafun_0 fopabiotafun_2 cab iopabiotafun_0 sup_set_class csn unieq iopabiotafun_0 sup_set_class iopabiotafun_0 vex unisn syl6req mpg fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class csn wceq fopabiotafun_0 fopabiotafun_2 cab iopabiotafun_0 sup_set_class csn wceq fopabiotafun_2 iopabiotafun_0 fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class csn wceq iopabiotafun_0 nfv fopabiotafun_2 fopabiotafun_0 fopabiotafun_2 cab iopabiotafun_0 sup_set_class csn fopabiotafun_0 fopabiotafun_2 nfab1 nfeq1 fopabiotafun_2 sup_set_class iopabiotafun_0 sup_set_class wceq fopabiotafun_2 sup_set_class csn iopabiotafun_0 sup_set_class csn fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class iopabiotafun_0 sup_set_class sneq eqeq2d cbvmo mpbir mpgbir fopabiotafun_3 fopabiotafun_0 fopabiotafun_2 cab fopabiotafun_2 sup_set_class csn wceq fopabiotafun_1 fopabiotafun_2 copab eopabiotafun_0 funeqi mpbir $.
$}
$( Define a function whose value is "the unique ` y ` such that
       ` ph ( x , y ) ` ".  (Contributed by NM, 16-Nov-2013.) $)
${
	$d x y $.
	$d x y F $.
	fopabiotadm_0 $f wff ph $.
	fopabiotadm_1 $f set x $.
	fopabiotadm_2 $f set y $.
	fopabiotadm_3 $f class F $.
	eopabiotadm_0 $e |- F = { <. x , y >. | { y | ph } = { y } } $.
	opabiotadm $p |- dom F = { x | E! y ph } $= fopabiotadm_0 fopabiotadm_2 cab fopabiotadm_2 sup_set_class csn wceq fopabiotadm_1 fopabiotadm_2 copab cdm fopabiotadm_0 fopabiotadm_2 cab fopabiotadm_2 sup_set_class csn wceq fopabiotadm_2 wex fopabiotadm_1 cab fopabiotadm_3 cdm fopabiotadm_0 fopabiotadm_2 weu fopabiotadm_1 cab fopabiotadm_0 fopabiotadm_2 cab fopabiotadm_2 sup_set_class csn wceq fopabiotadm_1 fopabiotadm_2 dmopab fopabiotadm_3 fopabiotadm_0 fopabiotadm_2 cab fopabiotadm_2 sup_set_class csn wceq fopabiotadm_1 fopabiotadm_2 copab eopabiotadm_0 dmeqi fopabiotadm_0 fopabiotadm_2 weu fopabiotadm_0 fopabiotadm_2 cab fopabiotadm_2 sup_set_class csn wceq fopabiotadm_2 wex fopabiotadm_1 fopabiotadm_0 fopabiotadm_2 euabsn abbii 3eqtr4i $.
$}
$( Define a function whose value is "the unique ` y ` such that
       ` ph ( x , y ) ` ".  (Contributed by NM, 16-Nov-2013.) $)
${
	$d x y B $.
	$d x y F $.
	$d x ps $.
	fopabiota_0 $f wff ph $.
	fopabiota_1 $f wff ps $.
	fopabiota_2 $f set x $.
	fopabiota_3 $f set y $.
	fopabiota_4 $f class B $.
	fopabiota_5 $f class F $.
	eopabiota_0 $e |- F = { <. x , y >. | { y | ph } = { y } } $.
	eopabiota_1 $e |- ( x = B -> ( ph <-> ps ) ) $.
	opabiota $p |- ( B e. dom F -> ( F ` B ) = ( iota y ps ) ) $= fopabiota_2 sup_set_class fopabiota_5 cfv fopabiota_0 fopabiota_3 cio wceq fopabiota_4 fopabiota_5 cfv fopabiota_1 fopabiota_3 cio wceq fopabiota_2 fopabiota_4 fopabiota_5 cdm fopabiota_2 sup_set_class fopabiota_4 wceq fopabiota_2 sup_set_class fopabiota_5 cfv fopabiota_4 fopabiota_5 cfv fopabiota_0 fopabiota_3 cio fopabiota_1 fopabiota_3 cio fopabiota_2 sup_set_class fopabiota_4 fopabiota_5 fveq2 fopabiota_2 sup_set_class fopabiota_4 wceq fopabiota_0 fopabiota_1 fopabiota_3 eopabiota_1 iotabidv eqeq12d fopabiota_2 sup_set_class fopabiota_5 cdm wcel fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_3 wex fopabiota_2 sup_set_class fopabiota_5 cfv fopabiota_0 fopabiota_3 cio wceq fopabiota_3 fopabiota_2 sup_set_class fopabiota_5 fopabiota_2 vex eldm fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_2 sup_set_class fopabiota_5 cfv fopabiota_0 fopabiota_3 cio wceq fopabiota_3 fopabiota_3 fopabiota_2 sup_set_class fopabiota_5 cfv fopabiota_0 fopabiota_3 cio fopabiota_3 fopabiota_2 sup_set_class fopabiota_5 fopabiota_3 fopabiota_5 fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_2 fopabiota_3 copab eopabiota_0 fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_2 fopabiota_3 nfopab2 nfcxfr fopabiota_3 fopabiota_2 sup_set_class nfcv nffv fopabiota_0 fopabiota_3 nfiota1 nfeq fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_2 sup_set_class fopabiota_5 cfv fopabiota_3 sup_set_class fopabiota_0 fopabiota_3 cio fopabiota_5 wfun fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_2 sup_set_class fopabiota_5 cfv fopabiota_3 sup_set_class wceq wi fopabiota_0 fopabiota_2 fopabiota_3 fopabiota_5 eopabiota_0 opabiotafun fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 funbrfv ax-mp fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_0 fopabiota_0 fopabiota_3 cio fopabiota_3 sup_set_class wceq fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_0 fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_2 sup_set_class fopabiota_3 sup_set_class cop fopabiota_5 wcel fopabiota_2 sup_set_class fopabiota_3 sup_set_class cop fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_2 fopabiota_3 copab wcel fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 df-br fopabiota_5 fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_2 fopabiota_3 copab fopabiota_2 sup_set_class fopabiota_3 sup_set_class cop eopabiota_0 eleq2i fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_2 fopabiota_3 opabid 3bitri fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_3 sup_set_class fopabiota_0 fopabiota_3 cab wcel fopabiota_0 fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq fopabiota_3 sup_set_class fopabiota_3 sup_set_class csn fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class fopabiota_3 vex snid fopabiota_0 fopabiota_3 cab fopabiota_3 sup_set_class csn wceq id syl5eleqr fopabiota_0 fopabiota_3 abid sylib sylbi fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_0 fopabiota_3 weu fopabiota_0 fopabiota_0 fopabiota_3 cio fopabiota_3 sup_set_class wceq wb fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 wbr fopabiota_2 sup_set_class fopabiota_5 cdm wcel fopabiota_0 fopabiota_3 weu fopabiota_2 sup_set_class fopabiota_3 sup_set_class fopabiota_5 fopabiota_2 vex fopabiota_3 vex breldm fopabiota_0 fopabiota_3 weu fopabiota_2 fopabiota_5 cdm fopabiota_0 fopabiota_2 fopabiota_3 fopabiota_5 eopabiota_0 opabiotadm abeq2i sylib fopabiota_0 fopabiota_3 iota1 syl mpbid eqtr4d exlimi sylbi vtoclga $.
$}

