$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Curry_and_uncurry.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Proper subset relation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c [C.]  $.
$( Extend class notation to include the reified proper subset relation. $)
${
	crpss $a class [C.] $.
$}
$( Define a relation which corresponds to proper subsethood ~ df-pss on
       sets.  This allows us to use proper subsethood with general concepts
       that require relations, such as strict ordering, see ~ sorpss .
       (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	$d x y $.
	fdf-rpss_0 $f set x $.
	fdf-rpss_1 $f set y $.
	df-rpss $a |- [C.] = { <. x , y >. | x C. y } $.
$}
$( The proper subset relation is a relation.  (Contributed by Stefan
       O'Rear, 2-Nov-2014.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	$d x y $.
	irelrpss_0 $f set x $.
	irelrpss_1 $f set y $.
	relrpss $p |- Rel [C.] $= irelrpss_0 cv irelrpss_1 cv wpss irelrpss_0 irelrpss_1 crpss irelrpss_0 irelrpss_1 df-rpss relopabi $.
$}
$( The proper subset relation on sets is the same as class proper
       subsethood.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$d x y A $.
	$d x y B $.
	ibrrpssg_0 $f set x $.
	ibrrpssg_1 $f set y $.
	fbrrpssg_0 $f class A $.
	fbrrpssg_1 $f class B $.
	fbrrpssg_2 $f class V $.
	brrpssg $p |- ( B e. V -> ( A [C.] B <-> A C. B ) ) $= fbrrpssg_1 fbrrpssg_2 wcel fbrrpssg_0 fbrrpssg_1 crpss wbr fbrrpssg_0 fbrrpssg_1 wpss fbrrpssg_1 cvv wcel fbrrpssg_0 cvv wcel wa fbrrpssg_1 fbrrpssg_2 wcel fbrrpssg_1 cvv wcel fbrrpssg_0 fbrrpssg_1 crpss wbr fbrrpssg_0 cvv wcel fbrrpssg_1 fbrrpssg_2 elex fbrrpssg_0 fbrrpssg_1 crpss relrpss brrelexi anim12i fbrrpssg_1 fbrrpssg_2 wcel fbrrpssg_0 fbrrpssg_1 wpss wa fbrrpssg_1 cvv wcel fbrrpssg_0 cvv wcel fbrrpssg_1 fbrrpssg_2 wcel fbrrpssg_1 cvv wcel fbrrpssg_0 fbrrpssg_1 wpss fbrrpssg_1 fbrrpssg_2 elex adantr fbrrpssg_0 fbrrpssg_1 wpss fbrrpssg_0 fbrrpssg_1 wss fbrrpssg_1 cvv wcel fbrrpssg_0 cvv wcel fbrrpssg_1 fbrrpssg_2 wcel fbrrpssg_0 fbrrpssg_1 pssss fbrrpssg_1 fbrrpssg_2 elex fbrrpssg_0 fbrrpssg_1 cvv ssexg syl2anr jca fbrrpssg_0 cvv wcel fbrrpssg_1 cvv wcel fbrrpssg_0 fbrrpssg_1 crpss wbr fbrrpssg_0 fbrrpssg_1 wpss wb ibrrpssg_0 cv ibrrpssg_1 cv wpss fbrrpssg_0 ibrrpssg_1 cv wpss fbrrpssg_0 fbrrpssg_1 wpss ibrrpssg_0 ibrrpssg_1 fbrrpssg_0 fbrrpssg_1 cvv cvv crpss ibrrpssg_0 cv fbrrpssg_0 ibrrpssg_1 cv psseq1 ibrrpssg_1 cv fbrrpssg_1 fbrrpssg_0 psseq2 ibrrpssg_0 ibrrpssg_1 df-rpss brabg ancoms pm5.21nd $.
$}
$( The proper subset relation on sets is the same as class proper
       subsethood.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
${
	$v A $.
	$v B $.
	fbrrpss_0 $f class A $.
	fbrrpss_1 $f class B $.
	ebrrpss_0 $e |- B e. _V $.
	brrpss $p |- ( A [C.] B <-> A C. B ) $= fbrrpss_1 cvv wcel fbrrpss_0 fbrrpss_1 crpss wbr fbrrpss_0 fbrrpss_1 wpss wb ebrrpss_0 fbrrpss_0 fbrrpss_1 cvv brrpssg ax-mp $.
$}
$( Every class is partially ordered by proper subsets.  (Contributed by
       Stefan O'Rear, 2-Nov-2014.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$d x y z A $.
	iporpss_0 $f set x $.
	iporpss_1 $f set y $.
	iporpss_2 $f set z $.
	fporpss_0 $f class A $.
	porpss $p |- [C.] Po A $= fporpss_0 crpss wpo iporpss_0 cv iporpss_0 cv crpss wbr wn iporpss_0 cv iporpss_1 cv crpss wbr iporpss_1 cv iporpss_2 cv crpss wbr wa iporpss_0 cv iporpss_2 cv crpss wbr wi wa iporpss_2 fporpss_0 wral iporpss_1 fporpss_0 wral iporpss_0 fporpss_0 wral iporpss_0 cv iporpss_0 cv crpss wbr wn iporpss_0 cv iporpss_1 cv crpss wbr iporpss_1 cv iporpss_2 cv crpss wbr wa iporpss_0 cv iporpss_2 cv crpss wbr wi wa iporpss_2 fporpss_0 wral iporpss_0 iporpss_1 fporpss_0 fporpss_0 iporpss_0 cv iporpss_0 cv crpss wbr wn iporpss_0 cv iporpss_1 cv crpss wbr iporpss_1 cv iporpss_2 cv crpss wbr wa iporpss_0 cv iporpss_2 cv crpss wbr wi wa iporpss_2 fporpss_0 iporpss_0 cv iporpss_0 cv crpss wbr wn iporpss_0 cv iporpss_1 cv crpss wbr iporpss_1 cv iporpss_2 cv crpss wbr wa iporpss_0 cv iporpss_2 cv crpss wbr wi wa iporpss_0 cv iporpss_0 cv wpss wn iporpss_0 cv iporpss_1 cv wpss iporpss_1 cv iporpss_2 cv wpss wa iporpss_0 cv iporpss_2 cv wpss wi iporpss_0 cv pssirr iporpss_0 cv iporpss_1 cv iporpss_2 cv psstr iporpss_0 cv iporpss_0 cv crpss wbr wn iporpss_0 cv iporpss_0 cv wpss wn iporpss_0 cv iporpss_1 cv crpss wbr iporpss_1 cv iporpss_2 cv crpss wbr wa iporpss_0 cv iporpss_2 cv crpss wbr wi iporpss_0 cv iporpss_1 cv wpss iporpss_1 cv iporpss_2 cv wpss wa iporpss_0 cv iporpss_2 cv wpss wi iporpss_0 cv iporpss_0 cv crpss wbr iporpss_0 cv iporpss_0 cv wpss iporpss_0 cv iporpss_0 cv iporpss_0 vex brrpss notbii iporpss_0 cv iporpss_1 cv crpss wbr iporpss_1 cv iporpss_2 cv crpss wbr wa iporpss_0 cv iporpss_1 cv wpss iporpss_1 cv iporpss_2 cv wpss wa iporpss_0 cv iporpss_2 cv crpss wbr iporpss_0 cv iporpss_2 cv wpss iporpss_0 cv iporpss_1 cv crpss wbr iporpss_0 cv iporpss_1 cv wpss iporpss_1 cv iporpss_2 cv crpss wbr iporpss_1 cv iporpss_2 cv wpss iporpss_0 cv iporpss_1 cv iporpss_1 vex brrpss iporpss_1 cv iporpss_2 cv iporpss_2 vex brrpss anbi12i iporpss_0 cv iporpss_2 cv iporpss_2 vex brrpss imbi12i anbi12i mpbir2an rgenw rgen2w iporpss_0 iporpss_1 iporpss_2 fporpss_0 crpss df-po mpbir $.
$}
$( Express strict ordering under proper subsets, i.e. the notion of a chain
       of sets.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	fsorpss_0 $f set x $.
	fsorpss_1 $f set y $.
	fsorpss_2 $f class A $.
	sorpss $p |- ( [C.] Or A <-> A. x e. A A. y e. A ( x C_ y \/ y C_ x ) ) $= fsorpss_0 cv fsorpss_1 cv crpss wbr fsorpss_0 fsorpss_1 weq fsorpss_1 cv fsorpss_0 cv crpss wbr w3o fsorpss_1 fsorpss_2 wral fsorpss_0 fsorpss_2 wral fsorpss_2 crpss wpo fsorpss_0 cv fsorpss_1 cv crpss wbr fsorpss_0 fsorpss_1 weq fsorpss_1 cv fsorpss_0 cv crpss wbr w3o fsorpss_1 fsorpss_2 wral fsorpss_0 fsorpss_2 wral wa fsorpss_0 cv fsorpss_1 cv wss fsorpss_1 cv fsorpss_0 cv wss wo fsorpss_1 fsorpss_2 wral fsorpss_0 fsorpss_2 wral fsorpss_2 crpss wor fsorpss_2 crpss wpo fsorpss_0 cv fsorpss_1 cv crpss wbr fsorpss_0 fsorpss_1 weq fsorpss_1 cv fsorpss_0 cv crpss wbr w3o fsorpss_1 fsorpss_2 wral fsorpss_0 fsorpss_2 wral fsorpss_2 porpss biantrur fsorpss_0 cv fsorpss_1 cv wss fsorpss_1 cv fsorpss_0 cv wss wo fsorpss_0 cv fsorpss_1 cv crpss wbr fsorpss_0 fsorpss_1 weq fsorpss_1 cv fsorpss_0 cv crpss wbr w3o fsorpss_0 fsorpss_1 fsorpss_2 fsorpss_2 fsorpss_0 cv fsorpss_1 cv wss fsorpss_1 cv fsorpss_0 cv wss wo fsorpss_0 cv fsorpss_1 cv wpss fsorpss_0 fsorpss_1 weq fsorpss_1 cv fsorpss_0 cv wpss w3o fsorpss_0 cv fsorpss_1 cv crpss wbr fsorpss_0 fsorpss_1 weq fsorpss_1 cv fsorpss_0 cv crpss wbr w3o fsorpss_0 cv fsorpss_1 cv sspsstri fsorpss_0 cv fsorpss_1 cv crpss wbr fsorpss_0 cv fsorpss_1 cv wpss fsorpss_0 fsorpss_1 weq fsorpss_0 fsorpss_1 weq fsorpss_1 cv fsorpss_0 cv crpss wbr fsorpss_1 cv fsorpss_0 cv wpss fsorpss_0 cv fsorpss_1 cv fsorpss_1 vex brrpss fsorpss_0 fsorpss_1 weq biid fsorpss_1 cv fsorpss_0 cv fsorpss_0 vex brrpss 3orbi123i bitr4i 2ralbii fsorpss_0 fsorpss_1 fsorpss_2 crpss df-so 3bitr4ri $.
$}
$( Property of a chain of sets.  (Contributed by Stefan O'Rear,
     2-Nov-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsorpssi_0 $f class A $.
	fsorpssi_1 $f class B $.
	fsorpssi_2 $f class C $.
	sorpssi $p |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) -> ( B C_ C \/ C C_ B ) ) $= fsorpssi_0 crpss wor fsorpssi_1 fsorpssi_0 wcel fsorpssi_2 fsorpssi_0 wcel wa wa fsorpssi_1 fsorpssi_2 wpss fsorpssi_1 fsorpssi_2 wceq fsorpssi_2 fsorpssi_1 wpss w3o fsorpssi_1 fsorpssi_2 wss fsorpssi_2 fsorpssi_1 wss wo fsorpssi_0 crpss wor fsorpssi_1 fsorpssi_0 wcel fsorpssi_2 fsorpssi_0 wcel wa wa fsorpssi_1 fsorpssi_2 crpss wbr fsorpssi_1 fsorpssi_2 wceq fsorpssi_2 fsorpssi_1 crpss wbr w3o fsorpssi_1 fsorpssi_2 wpss fsorpssi_1 fsorpssi_2 wceq fsorpssi_2 fsorpssi_1 wpss w3o fsorpssi_0 fsorpssi_1 fsorpssi_2 crpss solin fsorpssi_0 crpss wor fsorpssi_1 fsorpssi_0 wcel fsorpssi_2 fsorpssi_0 wcel wa wa fsorpssi_1 fsorpssi_2 crpss wbr fsorpssi_1 fsorpssi_2 wpss fsorpssi_1 fsorpssi_2 wceq fsorpssi_1 fsorpssi_2 wceq fsorpssi_2 fsorpssi_1 crpss wbr fsorpssi_2 fsorpssi_1 wpss fsorpssi_0 crpss wor fsorpssi_1 fsorpssi_0 wcel fsorpssi_2 fsorpssi_0 wcel wa wa fsorpssi_2 cvv wcel fsorpssi_1 fsorpssi_2 crpss wbr fsorpssi_1 fsorpssi_2 wpss wb fsorpssi_2 fsorpssi_0 wcel fsorpssi_2 cvv wcel fsorpssi_0 crpss wor fsorpssi_1 fsorpssi_0 wcel fsorpssi_2 fsorpssi_0 elex ad2antll fsorpssi_1 fsorpssi_2 cvv brrpssg syl fsorpssi_0 crpss wor fsorpssi_1 fsorpssi_0 wcel fsorpssi_2 fsorpssi_0 wcel wa wa fsorpssi_1 fsorpssi_2 wceq biidd fsorpssi_0 crpss wor fsorpssi_1 fsorpssi_0 wcel fsorpssi_2 fsorpssi_0 wcel wa wa fsorpssi_1 cvv wcel fsorpssi_2 fsorpssi_1 crpss wbr fsorpssi_2 fsorpssi_1 wpss wb fsorpssi_1 fsorpssi_0 wcel fsorpssi_1 cvv wcel fsorpssi_0 crpss wor fsorpssi_2 fsorpssi_0 wcel fsorpssi_1 fsorpssi_0 elex ad2antrl fsorpssi_2 fsorpssi_1 cvv brrpssg syl 3orbi123d mpbid fsorpssi_1 fsorpssi_2 sspsstri sylibr $.
$}
$( A chain of sets is closed under binary union.  (Contributed by Mario
     Carneiro, 16-May-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsorpssun_0 $f class A $.
	fsorpssun_1 $f class B $.
	fsorpssun_2 $f class C $.
	sorpssun $p |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) -> ( B u. C ) e. A ) $= fsorpssun_0 crpss wor fsorpssun_1 fsorpssun_0 wcel fsorpssun_2 fsorpssun_0 wcel wa wa fsorpssun_1 fsorpssun_2 wss fsorpssun_1 fsorpssun_2 cun fsorpssun_0 wcel fsorpssun_2 fsorpssun_1 wss fsorpssun_0 crpss wor fsorpssun_1 fsorpssun_0 wcel fsorpssun_2 fsorpssun_0 wcel wa wa fsorpssun_1 fsorpssun_2 cun fsorpssun_0 wcel fsorpssun_1 fsorpssun_2 wss fsorpssun_2 fsorpssun_0 wcel fsorpssun_0 crpss wor fsorpssun_1 fsorpssun_0 wcel fsorpssun_2 fsorpssun_0 wcel simprr fsorpssun_1 fsorpssun_2 wss fsorpssun_1 fsorpssun_2 cun fsorpssun_2 wceq fsorpssun_1 fsorpssun_2 cun fsorpssun_0 wcel fsorpssun_2 fsorpssun_0 wcel wb fsorpssun_1 fsorpssun_2 ssequn1 fsorpssun_1 fsorpssun_2 cun fsorpssun_2 fsorpssun_0 eleq1 sylbi syl5ibrcom fsorpssun_0 crpss wor fsorpssun_1 fsorpssun_0 wcel fsorpssun_2 fsorpssun_0 wcel wa wa fsorpssun_1 fsorpssun_2 cun fsorpssun_0 wcel fsorpssun_2 fsorpssun_1 wss fsorpssun_1 fsorpssun_0 wcel fsorpssun_0 crpss wor fsorpssun_1 fsorpssun_0 wcel fsorpssun_2 fsorpssun_0 wcel simprl fsorpssun_2 fsorpssun_1 wss fsorpssun_1 fsorpssun_2 cun fsorpssun_1 wceq fsorpssun_1 fsorpssun_2 cun fsorpssun_0 wcel fsorpssun_1 fsorpssun_0 wcel wb fsorpssun_2 fsorpssun_1 ssequn2 fsorpssun_1 fsorpssun_2 cun fsorpssun_1 fsorpssun_0 eleq1 sylbi syl5ibrcom fsorpssun_0 fsorpssun_1 fsorpssun_2 sorpssi mpjaod $.
$}
$( A chain of sets is closed under binary intersection.  (Contributed by
     Mario Carneiro, 16-May-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsorpssin_0 $f class A $.
	fsorpssin_1 $f class B $.
	fsorpssin_2 $f class C $.
	sorpssin $p |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) -> ( B i^i C ) e. A ) $= fsorpssin_0 crpss wor fsorpssin_1 fsorpssin_0 wcel fsorpssin_2 fsorpssin_0 wcel wa wa fsorpssin_1 fsorpssin_2 wss fsorpssin_1 fsorpssin_2 cin fsorpssin_0 wcel fsorpssin_2 fsorpssin_1 wss fsorpssin_0 crpss wor fsorpssin_1 fsorpssin_0 wcel fsorpssin_2 fsorpssin_0 wcel wa wa fsorpssin_1 fsorpssin_2 cin fsorpssin_0 wcel fsorpssin_1 fsorpssin_2 wss fsorpssin_1 fsorpssin_0 wcel fsorpssin_0 crpss wor fsorpssin_1 fsorpssin_0 wcel fsorpssin_2 fsorpssin_0 wcel simprl fsorpssin_1 fsorpssin_2 wss fsorpssin_1 fsorpssin_2 cin fsorpssin_1 wceq fsorpssin_1 fsorpssin_2 cin fsorpssin_0 wcel fsorpssin_1 fsorpssin_0 wcel wb fsorpssin_1 fsorpssin_2 df-ss fsorpssin_1 fsorpssin_2 cin fsorpssin_1 fsorpssin_0 eleq1 sylbi syl5ibrcom fsorpssin_0 crpss wor fsorpssin_1 fsorpssin_0 wcel fsorpssin_2 fsorpssin_0 wcel wa wa fsorpssin_1 fsorpssin_2 cin fsorpssin_0 wcel fsorpssin_2 fsorpssin_1 wss fsorpssin_2 fsorpssin_0 wcel fsorpssin_0 crpss wor fsorpssin_1 fsorpssin_0 wcel fsorpssin_2 fsorpssin_0 wcel simprr fsorpssin_2 fsorpssin_1 wss fsorpssin_1 fsorpssin_2 cin fsorpssin_2 wceq fsorpssin_1 fsorpssin_2 cin fsorpssin_0 wcel fsorpssin_2 fsorpssin_0 wcel wb fsorpssin_2 fsorpssin_1 dfss1 fsorpssin_1 fsorpssin_2 cin fsorpssin_2 fsorpssin_0 eleq1 sylbi syl5ibrcom fsorpssin_0 fsorpssin_1 fsorpssin_2 sorpssi mpjaod $.
$}
$( In a chain of sets, a maximal element is the union of the chain.
       (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
${
	$v v $.
	$v u $.
	$v Y $.
	$d Y u v $.
	fsorpssuni_0 $f set v $.
	fsorpssuni_1 $f set u $.
	fsorpssuni_2 $f class Y $.
	sorpssuni $p |- ( [C.] Or Y -> ( E. u e. Y A. v e. Y -. u C. v <-> U. Y e. Y ) ) $= fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_1 fsorpssuni_2 wrex fsorpssuni_2 cuni fsorpssuni_2 wcel fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_2 cuni fsorpssuni_2 wcel fsorpssuni_1 fsorpssuni_2 fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 wcel fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral w3a fsorpssuni_2 cuni fsorpssuni_1 cv fsorpssuni_2 fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 wcel fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral w3a fsorpssuni_2 cuni fsorpssuni_1 cv fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 wcel fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral w3a fsorpssuni_0 cv fsorpssuni_1 cv wss fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_2 cuni fsorpssuni_1 cv wss fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 wcel fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_0 cv fsorpssuni_1 cv wss fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 wcel wa fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 cv fsorpssuni_1 cv wss fsorpssuni_0 fsorpssuni_2 fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 wcel wa fsorpssuni_0 cv fsorpssuni_2 wcel wa fsorpssuni_1 cv fsorpssuni_0 cv wss fsorpssuni_0 cv fsorpssuni_1 cv wss wo fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 cv fsorpssuni_1 cv wss wi fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 wcel fsorpssuni_0 cv fsorpssuni_2 wcel fsorpssuni_1 cv fsorpssuni_0 cv wss fsorpssuni_0 cv fsorpssuni_1 cv wss wo fsorpssuni_2 fsorpssuni_1 cv fsorpssuni_0 cv sorpssi anassrs fsorpssuni_1 cv fsorpssuni_0 cv wss fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 cv fsorpssuni_1 cv wss wi fsorpssuni_0 cv fsorpssuni_1 cv wss fsorpssuni_1 cv fsorpssuni_0 cv wss fsorpssuni_1 cv fsorpssuni_0 cv wpss fsorpssuni_1 fsorpssuni_0 weq wo fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 cv fsorpssuni_1 cv wss wi fsorpssuni_1 cv fsorpssuni_0 cv sspss fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_1 cv fsorpssuni_0 cv wpss fsorpssuni_1 fsorpssuni_0 weq wo fsorpssuni_1 fsorpssuni_0 weq fsorpssuni_0 cv fsorpssuni_1 cv wss fsorpssuni_1 cv fsorpssuni_0 cv wpss fsorpssuni_1 fsorpssuni_0 weq orel1 fsorpssuni_0 cv fsorpssuni_1 cv eqimss2 syl6com sylbi fsorpssuni_0 cv fsorpssuni_1 cv wss fsorpssuni_1 cv fsorpssuni_0 cv wpss wn ax-1 jaoi syl ralimdva 3impia fsorpssuni_0 fsorpssuni_2 fsorpssuni_1 cv unissb sylibr fsorpssuni_1 cv fsorpssuni_2 wcel fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 cuni wss fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_1 cv fsorpssuni_2 elssuni 3ad2ant2 eqssd fsorpssuni_2 crpss wor fsorpssuni_1 cv fsorpssuni_2 wcel fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral simp2 eqeltrd rexlimdv3a fsorpssuni_2 cuni fsorpssuni_2 wcel fsorpssuni_2 cuni fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_1 fsorpssuni_2 wrex fsorpssuni_2 cuni fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 fsorpssuni_0 cv fsorpssuni_2 wcel fsorpssuni_0 cv fsorpssuni_2 cuni wss fsorpssuni_2 cuni fsorpssuni_0 cv wpss wn fsorpssuni_0 cv fsorpssuni_2 elssuni fsorpssuni_0 cv fsorpssuni_2 cuni ssnpss syl rgen fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_2 cuni fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 wral fsorpssuni_1 fsorpssuni_2 cuni fsorpssuni_2 fsorpssuni_1 cv fsorpssuni_2 cuni wceq fsorpssuni_1 cv fsorpssuni_0 cv wpss wn fsorpssuni_2 cuni fsorpssuni_0 cv wpss wn fsorpssuni_0 fsorpssuni_2 fsorpssuni_1 cv fsorpssuni_2 cuni wceq fsorpssuni_1 cv fsorpssuni_0 cv wpss fsorpssuni_2 cuni fsorpssuni_0 cv wpss fsorpssuni_1 cv fsorpssuni_2 cuni fsorpssuni_0 cv psseq1 notbid ralbidv rspcev mpan2 impbid1 $.
$}
$( In a chain of sets, a minimal element is the intersection of the chain.
       (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
${
	$v v $.
	$v u $.
	$v Y $.
	$d Y u v $.
	fsorpssint_0 $f set v $.
	fsorpssint_1 $f set u $.
	fsorpssint_2 $f class Y $.
	sorpssint $p |- ( [C.] Or Y -> ( E. u e. Y A. v e. Y -. v C. u <-> |^| Y e. Y ) ) $= fsorpssint_2 crpss wor fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral fsorpssint_1 fsorpssint_2 wrex fsorpssint_2 cint fsorpssint_2 wcel fsorpssint_2 crpss wor fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral fsorpssint_2 cint fsorpssint_2 wcel fsorpssint_1 fsorpssint_2 fsorpssint_2 crpss wor fsorpssint_1 cv fsorpssint_2 wcel fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral w3a fsorpssint_2 cint fsorpssint_1 cv fsorpssint_2 fsorpssint_2 crpss wor fsorpssint_1 cv fsorpssint_2 wcel fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral w3a fsorpssint_2 cint fsorpssint_1 cv fsorpssint_1 cv fsorpssint_2 wcel fsorpssint_2 crpss wor fsorpssint_2 cint fsorpssint_1 cv wss fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral fsorpssint_1 cv fsorpssint_2 intss1 3ad2ant2 fsorpssint_2 crpss wor fsorpssint_1 cv fsorpssint_2 wcel fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral w3a fsorpssint_1 cv fsorpssint_0 cv wss fsorpssint_0 fsorpssint_2 wral fsorpssint_1 cv fsorpssint_2 cint wss fsorpssint_2 crpss wor fsorpssint_1 cv fsorpssint_2 wcel fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral fsorpssint_1 cv fsorpssint_0 cv wss fsorpssint_0 fsorpssint_2 wral fsorpssint_2 crpss wor fsorpssint_1 cv fsorpssint_2 wcel wa fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_1 cv fsorpssint_0 cv wss fsorpssint_0 fsorpssint_2 fsorpssint_2 crpss wor fsorpssint_1 cv fsorpssint_2 wcel wa fsorpssint_0 cv fsorpssint_2 wcel wa fsorpssint_1 cv fsorpssint_0 cv wss fsorpssint_0 cv fsorpssint_1 cv wss wo fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_1 cv fsorpssint_0 cv wss wi fsorpssint_2 crpss wor fsorpssint_1 cv fsorpssint_2 wcel fsorpssint_0 cv fsorpssint_2 wcel fsorpssint_1 cv fsorpssint_0 cv wss fsorpssint_0 cv fsorpssint_1 cv wss wo fsorpssint_2 fsorpssint_1 cv fsorpssint_0 cv sorpssi anassrs fsorpssint_1 cv fsorpssint_0 cv wss fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_1 cv fsorpssint_0 cv wss wi fsorpssint_0 cv fsorpssint_1 cv wss fsorpssint_1 cv fsorpssint_0 cv wss fsorpssint_0 cv fsorpssint_1 cv wpss wn ax-1 fsorpssint_0 cv fsorpssint_1 cv wss fsorpssint_0 cv fsorpssint_1 cv wpss fsorpssint_0 fsorpssint_1 weq wo fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_1 cv fsorpssint_0 cv wss wi fsorpssint_0 cv fsorpssint_1 cv sspss fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 cv fsorpssint_1 cv wpss fsorpssint_0 fsorpssint_1 weq wo fsorpssint_0 fsorpssint_1 weq fsorpssint_1 cv fsorpssint_0 cv wss fsorpssint_0 cv fsorpssint_1 cv wpss fsorpssint_0 fsorpssint_1 weq orel1 fsorpssint_1 cv fsorpssint_0 cv eqimss2 syl6com sylbi jaoi syl ralimdva 3impia fsorpssint_0 fsorpssint_1 cv fsorpssint_2 ssint sylibr eqssd fsorpssint_2 crpss wor fsorpssint_1 cv fsorpssint_2 wcel fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral simp2 eqeltrd rexlimdv3a fsorpssint_2 cint fsorpssint_2 wcel fsorpssint_0 cv fsorpssint_2 cint wpss wn fsorpssint_0 fsorpssint_2 wral fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral fsorpssint_1 fsorpssint_2 wrex fsorpssint_0 cv fsorpssint_2 cint wpss wn fsorpssint_0 fsorpssint_2 fsorpssint_0 cv fsorpssint_2 wcel fsorpssint_2 cint fsorpssint_0 cv wss fsorpssint_0 cv fsorpssint_2 cint wpss wn fsorpssint_0 cv fsorpssint_2 intss1 fsorpssint_2 cint fsorpssint_0 cv ssnpss syl rgen fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 fsorpssint_2 wral fsorpssint_0 cv fsorpssint_2 cint wpss wn fsorpssint_0 fsorpssint_2 wral fsorpssint_1 fsorpssint_2 cint fsorpssint_2 fsorpssint_1 cv fsorpssint_2 cint wceq fsorpssint_0 cv fsorpssint_1 cv wpss wn fsorpssint_0 cv fsorpssint_2 cint wpss wn fsorpssint_0 fsorpssint_2 fsorpssint_1 cv fsorpssint_2 cint wceq fsorpssint_0 cv fsorpssint_1 cv wpss fsorpssint_0 cv fsorpssint_2 cint wpss fsorpssint_1 cv fsorpssint_2 cint fsorpssint_0 cv psseq2 notbid ralbidv rspcev mpan2 impbid1 $.
$}
$( The componentwise complement of a chain of sets is also a chain of
       sets.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
${
	$v x $.
	$v y $.
	$v u $.
	$v A $.
	$v Y $.
	$d Y x y $.
	$d A x y $.
	$d Y u $.
	$d A u $.
	$d u x y $.
	isorpsscmpl_0 $f set x $.
	isorpsscmpl_1 $f set y $.
	fsorpsscmpl_0 $f set u $.
	fsorpsscmpl_1 $f class A $.
	fsorpsscmpl_2 $f class Y $.
	sorpsscmpl $p |- ( [C.] Or Y -> [C.] Or { u e. ~P A | ( A \ u ) e. Y } ) $= fsorpsscmpl_2 crpss wor isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo isorpsscmpl_1 fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab wral isorpsscmpl_0 fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab wral fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab crpss wor fsorpsscmpl_2 crpss wor isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo isorpsscmpl_0 isorpsscmpl_1 fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab isorpsscmpl_0 cv fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab wcel isorpsscmpl_1 cv fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab wcel wa isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel wa fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa wa fsorpsscmpl_2 crpss wor isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo isorpsscmpl_0 cv fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab wcel isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel wa isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel wa fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa wa isorpsscmpl_1 cv fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab wcel fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 isorpsscmpl_0 cv fsorpsscmpl_1 cpw fsorpsscmpl_0 isorpsscmpl_0 weq fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 fsorpsscmpl_0 cv isorpsscmpl_0 cv fsorpsscmpl_1 difeq2 eleq1d elrab fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 isorpsscmpl_1 cv fsorpsscmpl_1 cpw fsorpsscmpl_0 isorpsscmpl_1 weq fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 fsorpsscmpl_0 cv isorpsscmpl_1 cv fsorpsscmpl_1 difeq2 eleq1d elrab isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel wa isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa wa isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel wa fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa wa isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel an4 biimpi syl2anb fsorpsscmpl_2 crpss wor isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel wa fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa fsorpsscmpl_2 crpss wor isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel wa isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa fsorpsscmpl_2 crpss wor fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif wss fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif wss wo isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel wa isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo wi fsorpsscmpl_2 crpss wor fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_2 wcel wa fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif wss fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif wss wo fsorpsscmpl_2 fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif sorpssi expcom fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif wss fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif wss isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel wa isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo wi isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel wa fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif wss fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif wss wo isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif isorpsscmpl_0 cv wceq fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif isorpsscmpl_1 cv wceq fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif wss fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif wss wo isorpsscmpl_0 cv isorpsscmpl_1 cv wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wo wi isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_0 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_0 cv fsorpsscmpl_1 wss fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif isorpsscmpl_0 cv wceq isorpsscmpl_0 cv fsorpsscmpl_1 isorpsscmpl_0 vex elpw isorpsscmpl_0 cv fsorpsscmpl_1 dfss4 bitri isorpsscmpl_1 cv fsorpsscmpl_1 cpw wcel isorpsscmpl_1 cv fsorpsscmpl_1 wss fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif isorpsscmpl_1 cv wceq isorpsscmpl_1 cv fsorpsscmpl_1 isorpsscmpl_1 vex elpw isorpsscmpl_1 cv fsorpsscmpl_1 dfss4 bitri fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif isorpsscmpl_0 cv wceq fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif isorpsscmpl_1 cv wceq wa fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif wss isorpsscmpl_0 cv isorpsscmpl_1 cv wss fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif wss fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif wss fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif isorpsscmpl_0 cv wceq fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif isorpsscmpl_1 cv wceq wa isorpsscmpl_0 cv isorpsscmpl_1 cv wss fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 sscon fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif isorpsscmpl_0 cv fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif isorpsscmpl_1 cv sseq12 syl5ib fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif wss fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif wss fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif isorpsscmpl_0 cv wceq fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif isorpsscmpl_1 cv wceq wa isorpsscmpl_1 cv isorpsscmpl_0 cv wss fsorpsscmpl_1 isorpsscmpl_0 cv cdif fsorpsscmpl_1 isorpsscmpl_1 cv cdif fsorpsscmpl_1 sscon fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif isorpsscmpl_1 cv wceq fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif isorpsscmpl_0 cv wceq fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif wss isorpsscmpl_1 cv isorpsscmpl_0 cv wss wb fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_1 cv cdif cdif isorpsscmpl_1 cv fsorpsscmpl_1 fsorpsscmpl_1 isorpsscmpl_0 cv cdif cdif isorpsscmpl_0 cv sseq12 ancoms syl5ib orim12d syl2anb com12 orcoms syl6 com3l imp3a syl5 ralrimivv isorpsscmpl_0 isorpsscmpl_1 fsorpsscmpl_1 fsorpsscmpl_0 cv cdif fsorpsscmpl_2 wcel fsorpsscmpl_0 fsorpsscmpl_1 cpw crab sorpss sylibr $.
$}

