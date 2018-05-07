$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Function_operation.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        First and second members of an ordered pair

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c 1st  $.
$( First member of an ordered pair $)
$c 2nd  $.
$( Second member of an ordered pair $)
$( Extend the definition of a class to include the first member an ordered
     pair function. $)
${
	c1st $a class 1st $.
$}
$( Extend the definition of a class to include the second member an ordered
     pair function. $)
${
	c2nd $a class 2nd $.
$}
$( Define a function that extracts the first member, or abscissa, of an
     ordered pair.  Theorem ~ op1st proves that it does this.  For example,
     ` ( 1st `` <. 3 , 4 >. ) = 3 ` .  Equivalent to Definition 5.13 (i) of
     [Monk1] p. 52 (compare ~ op1sta and ~ op1stb ).  The notation is the same
     as Monk's.  (Contributed by NM, 9-Oct-2004.) $)
${
	$v x $.
	fdf-1st_0 $f set x $.
	df-1st $a |- 1st = ( x e. _V |-> U. dom { x } ) $.
$}
$( Define a function that extracts the second member, or ordinate, of an
     ordered pair.  Theorem ~ op2nd proves that it does this.  For example,
     ` ( 2nd `` <. 3 , 4 >. ) = 4 ` .  Equivalent to Definition 5.13 (ii) of
     [Monk1] p. 52 (compare ~ op2nda and ~ op2ndb ).  The notation is the same
     as Monk's.  (Contributed by NM, 9-Oct-2004.) $)
${
	$v x $.
	fdf-2nd_0 $f set x $.
	df-2nd $a |- 2nd = ( x e. _V |-> U. ran { x } ) $.
$}
$( The value of the function that extracts the first member of an ordered
       pair.  (Contributed by NM, 9-Oct-2004.)  (Revised by Mario Carneiro,
       8-Sep-2013.) $)
${
	$v x $.
	$v A $.
	$d x A $.
	i1stval_0 $f set x $.
	f1stval_0 $f class A $.
	1stval $p |- ( 1st ` A ) = U. dom { A } $= f1stval_0 cvv wcel f1stval_0 c1st cfv f1stval_0 csn cdm cuni wceq i1stval_0 f1stval_0 i1stval_0 cv csn cdm cuni f1stval_0 csn cdm cuni cvv c1st i1stval_0 cv f1stval_0 wceq i1stval_0 cv csn cdm f1stval_0 csn cdm i1stval_0 cv f1stval_0 wceq i1stval_0 cv csn f1stval_0 csn i1stval_0 cv f1stval_0 sneq dmeqd unieqd i1stval_0 df-1st f1stval_0 csn cdm f1stval_0 csn f1stval_0 snex dmex uniex fvmpt f1stval_0 cvv wcel wn f1stval_0 c1st cfv c0 f1stval_0 csn cdm cuni f1stval_0 c1st fvprc f1stval_0 cvv wcel wn f1stval_0 csn cdm cuni c0 cuni c0 f1stval_0 cvv wcel wn f1stval_0 csn cdm c0 f1stval_0 cvv wcel wn f1stval_0 csn cdm c0 cdm c0 f1stval_0 cvv wcel wn f1stval_0 csn c0 f1stval_0 cvv wcel wn f1stval_0 csn c0 wceq f1stval_0 snprc biimpi dmeqd dm0 syl6eq unieqd uni0 syl6eq eqtr4d pm2.61i $.
$}
$( The value of the function that extracts the second member of an ordered
       pair.  (Contributed by NM, 9-Oct-2004.)  (Revised by Mario Carneiro,
       8-Sep-2013.) $)
${
	$v x $.
	$v A $.
	$d x A $.
	i2ndval_0 $f set x $.
	f2ndval_0 $f class A $.
	2ndval $p |- ( 2nd ` A ) = U. ran { A } $= f2ndval_0 cvv wcel f2ndval_0 c2nd cfv f2ndval_0 csn crn cuni wceq i2ndval_0 f2ndval_0 i2ndval_0 cv csn crn cuni f2ndval_0 csn crn cuni cvv c2nd i2ndval_0 cv f2ndval_0 wceq i2ndval_0 cv csn crn f2ndval_0 csn crn i2ndval_0 cv f2ndval_0 wceq i2ndval_0 cv csn f2ndval_0 csn i2ndval_0 cv f2ndval_0 sneq rneqd unieqd i2ndval_0 df-2nd f2ndval_0 csn crn f2ndval_0 csn f2ndval_0 snex rnex uniex fvmpt f2ndval_0 cvv wcel wn f2ndval_0 c2nd cfv c0 f2ndval_0 csn crn cuni f2ndval_0 c2nd fvprc f2ndval_0 cvv wcel wn f2ndval_0 csn crn cuni c0 cuni c0 f2ndval_0 cvv wcel wn f2ndval_0 csn crn c0 f2ndval_0 cvv wcel wn f2ndval_0 csn crn c0 crn c0 f2ndval_0 cvv wcel wn f2ndval_0 csn c0 f2ndval_0 cvv wcel wn f2ndval_0 csn c0 wceq f2ndval_0 snprc biimpi rneqd rn0 syl6eq unieqd uni0 syl6eq eqtr4d pm2.61i $.
$}
$( The value of the first-member function at the empty set.  (Contributed by
     NM, 23-Apr-2007.) $)
${
	1st0 $p |- ( 1st ` (/) ) = (/) $= c0 c1st cfv c0 csn cdm cuni c0 cuni c0 c0 1stval c0 csn cdm c0 dmsn0 unieqi uni0 3eqtri $.
$}
$( The value of the second-member function at the empty set.  (Contributed by
     NM, 23-Apr-2007.) $)
${
	2nd0 $p |- ( 2nd ` (/) ) = (/) $= c0 c2nd cfv c0 csn crn cuni c0 cuni c0 c0 2ndval c0 csn crn c0 c0 csn cdm c0 wceq c0 csn crn c0 wceq dmsn0 c0 csn dm0rn0 mpbi unieqi uni0 3eqtri $.
$}
$( Extract the first member of an ordered pair.  (Contributed by NM,
       5-Oct-2004.) $)
${
	$v A $.
	$v B $.
	fop1st_0 $f class A $.
	fop1st_1 $f class B $.
	eop1st_0 $e |- A e. _V $.
	eop1st_1 $e |- B e. _V $.
	op1st $p |- ( 1st ` <. A , B >. ) = A $= fop1st_0 fop1st_1 cop c1st cfv fop1st_0 fop1st_1 cop csn cdm cuni fop1st_0 fop1st_0 fop1st_1 cop 1stval fop1st_0 fop1st_1 eop1st_0 eop1st_1 op1sta eqtri $.
$}
$( Extract the second member of an ordered pair.  (Contributed by NM,
       5-Oct-2004.) $)
${
	$v A $.
	$v B $.
	fop2nd_0 $f class A $.
	fop2nd_1 $f class B $.
	eop2nd_0 $e |- A e. _V $.
	eop2nd_1 $e |- B e. _V $.
	op2nd $p |- ( 2nd ` <. A , B >. ) = B $= fop2nd_0 fop2nd_1 cop c2nd cfv fop2nd_0 fop2nd_1 cop csn crn cuni fop2nd_1 fop2nd_0 fop2nd_1 cop 2ndval fop2nd_0 fop2nd_1 eop2nd_0 eop2nd_1 op2nda eqtri $.
$}
$( Extract the first member of an ordered pair.  (Contributed by Mario
       Carneiro, 31-Aug-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fop1std_0 $f class A $.
	fop1std_1 $f class B $.
	fop1std_2 $f class C $.
	eop1std_0 $e |- A e. _V $.
	eop1std_1 $e |- B e. _V $.
	op1std $p |- ( C = <. A , B >. -> ( 1st ` C ) = A ) $= fop1std_2 fop1std_0 fop1std_1 cop wceq fop1std_2 c1st cfv fop1std_0 fop1std_1 cop c1st cfv fop1std_0 fop1std_2 fop1std_0 fop1std_1 cop c1st fveq2 fop1std_0 fop1std_1 eop1std_0 eop1std_1 op1st syl6eq $.
$}
$( Extract the second member of an ordered pair.  (Contributed by Mario
       Carneiro, 31-Aug-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fop2ndd_0 $f class A $.
	fop2ndd_1 $f class B $.
	fop2ndd_2 $f class C $.
	eop2ndd_0 $e |- A e. _V $.
	eop2ndd_1 $e |- B e. _V $.
	op2ndd $p |- ( C = <. A , B >. -> ( 2nd ` C ) = B ) $= fop2ndd_2 fop2ndd_0 fop2ndd_1 cop wceq fop2ndd_2 c2nd cfv fop2ndd_0 fop2ndd_1 cop c2nd cfv fop2ndd_1 fop2ndd_2 fop2ndd_0 fop2ndd_1 cop c2nd fveq2 fop2ndd_0 fop2ndd_1 eop2ndd_0 eop2ndd_1 op2nd syl6eq $.
$}
$( Extract the first member of an ordered pair.  (Contributed by NM,
       19-Jul-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$v W $.
	$d x y A $.
	$d x y B $.
	iop1stg_0 $f set x $.
	iop1stg_1 $f set y $.
	fop1stg_0 $f class A $.
	fop1stg_1 $f class B $.
	fop1stg_2 $f class V $.
	fop1stg_3 $f class W $.
	op1stg $p |- ( ( A e. V /\ B e. W ) -> ( 1st ` <. A , B >. ) = A ) $= iop1stg_0 cv iop1stg_1 cv cop c1st cfv iop1stg_0 cv wceq fop1stg_0 iop1stg_1 cv cop c1st cfv fop1stg_0 wceq fop1stg_0 fop1stg_1 cop c1st cfv fop1stg_0 wceq iop1stg_0 iop1stg_1 fop1stg_0 fop1stg_1 fop1stg_2 fop1stg_3 iop1stg_0 cv fop1stg_0 wceq iop1stg_0 cv iop1stg_1 cv cop c1st cfv fop1stg_0 iop1stg_1 cv cop c1st cfv iop1stg_0 cv fop1stg_0 iop1stg_0 cv fop1stg_0 wceq iop1stg_0 cv iop1stg_1 cv cop fop1stg_0 iop1stg_1 cv cop c1st iop1stg_0 cv fop1stg_0 iop1stg_1 cv opeq1 fveq2d iop1stg_0 cv fop1stg_0 wceq id eqeq12d iop1stg_1 cv fop1stg_1 wceq fop1stg_0 iop1stg_1 cv cop c1st cfv fop1stg_0 fop1stg_1 cop c1st cfv fop1stg_0 iop1stg_1 cv fop1stg_1 wceq fop1stg_0 iop1stg_1 cv cop fop1stg_0 fop1stg_1 cop c1st iop1stg_1 cv fop1stg_1 fop1stg_0 opeq2 fveq2d eqeq1d iop1stg_0 cv iop1stg_1 cv iop1stg_0 vex iop1stg_1 vex op1st vtocl2g $.
$}
$( Extract the second member of an ordered pair.  (Contributed by NM,
       19-Jul-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$v W $.
	$d x y A $.
	$d x y B $.
	iop2ndg_0 $f set x $.
	iop2ndg_1 $f set y $.
	fop2ndg_0 $f class A $.
	fop2ndg_1 $f class B $.
	fop2ndg_2 $f class V $.
	fop2ndg_3 $f class W $.
	op2ndg $p |- ( ( A e. V /\ B e. W ) -> ( 2nd ` <. A , B >. ) = B ) $= iop2ndg_0 cv iop2ndg_1 cv cop c2nd cfv iop2ndg_1 cv wceq fop2ndg_0 iop2ndg_1 cv cop c2nd cfv iop2ndg_1 cv wceq fop2ndg_0 fop2ndg_1 cop c2nd cfv fop2ndg_1 wceq iop2ndg_0 iop2ndg_1 fop2ndg_0 fop2ndg_1 fop2ndg_2 fop2ndg_3 iop2ndg_0 cv fop2ndg_0 wceq iop2ndg_0 cv iop2ndg_1 cv cop c2nd cfv fop2ndg_0 iop2ndg_1 cv cop c2nd cfv iop2ndg_1 cv iop2ndg_0 cv fop2ndg_0 wceq iop2ndg_0 cv iop2ndg_1 cv cop fop2ndg_0 iop2ndg_1 cv cop c2nd iop2ndg_0 cv fop2ndg_0 iop2ndg_1 cv opeq1 fveq2d eqeq1d iop2ndg_1 cv fop2ndg_1 wceq fop2ndg_0 iop2ndg_1 cv cop c2nd cfv fop2ndg_0 fop2ndg_1 cop c2nd cfv iop2ndg_1 cv fop2ndg_1 iop2ndg_1 cv fop2ndg_1 wceq fop2ndg_0 iop2ndg_1 cv cop fop2ndg_0 fop2ndg_1 cop c2nd iop2ndg_1 cv fop2ndg_1 fop2ndg_0 opeq2 fveq2d iop2ndg_1 cv fop2ndg_1 wceq id eqeq12d iop2ndg_0 cv iop2ndg_1 cv iop2ndg_0 vex iop2ndg_1 vex op2nd vtocl2g $.
$}
$( Extract the first member of an ordered triple.  (Due to infrequent
       usage, it isn't worthwhile at this point to define special extractors
       for triples, so we reuse the ordered pair extractors for ~ ot1stg ,
       ~ ot2ndg , ~ ot3rdg .)  (Contributed by NM, 3-Apr-2015.)  (Revised by
       Mario Carneiro, 2-May-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	$v X $.
	fot1stg_0 $f class A $.
	fot1stg_1 $f class B $.
	fot1stg_2 $f class C $.
	fot1stg_3 $f class V $.
	fot1stg_4 $f class W $.
	fot1stg_5 $f class X $.
	ot1stg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( 1st ` ( 1st ` <. A , B , C >. ) ) = A ) $= fot1stg_0 fot1stg_3 wcel fot1stg_1 fot1stg_4 wcel fot1stg_2 fot1stg_5 wcel fot1stg_0 fot1stg_1 fot1stg_2 cotp c1st cfv c1st cfv fot1stg_0 wceq fot1stg_2 fot1stg_5 wcel fot1stg_0 fot1stg_3 wcel fot1stg_1 fot1stg_4 wcel wa fot1stg_0 fot1stg_1 fot1stg_2 cotp c1st cfv c1st cfv fot1stg_0 fot1stg_1 cop c1st cfv fot1stg_0 fot1stg_2 fot1stg_5 wcel fot1stg_0 fot1stg_1 fot1stg_2 cotp c1st cfv fot1stg_0 fot1stg_1 cop c1st fot1stg_2 fot1stg_5 wcel fot1stg_0 fot1stg_1 fot1stg_2 cotp c1st cfv fot1stg_0 fot1stg_1 cop fot1stg_2 cop c1st cfv fot1stg_0 fot1stg_1 cop fot1stg_0 fot1stg_1 fot1stg_2 cotp fot1stg_0 fot1stg_1 cop fot1stg_2 cop c1st fot1stg_0 fot1stg_1 fot1stg_2 df-ot fveq2i fot1stg_0 fot1stg_1 cop cvv wcel fot1stg_2 fot1stg_5 wcel fot1stg_0 fot1stg_1 cop fot1stg_2 cop c1st cfv fot1stg_0 fot1stg_1 cop wceq fot1stg_0 fot1stg_1 opex fot1stg_0 fot1stg_1 cop fot1stg_2 cvv fot1stg_5 op1stg mpan syl5eq fveq2d fot1stg_0 fot1stg_1 fot1stg_3 fot1stg_4 op1stg sylan9eqr 3impa $.
$}
$( Extract the second member of an ordered triple.  (See ~ ot1stg
       comment.)  (Contributed by NM, 3-Apr-2015.)  (Revised by Mario Carneiro,
       2-May-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	$v X $.
	fot2ndg_0 $f class A $.
	fot2ndg_1 $f class B $.
	fot2ndg_2 $f class C $.
	fot2ndg_3 $f class V $.
	fot2ndg_4 $f class W $.
	fot2ndg_5 $f class X $.
	ot2ndg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( 2nd ` ( 1st ` <. A , B , C >. ) ) = B ) $= fot2ndg_0 fot2ndg_3 wcel fot2ndg_1 fot2ndg_4 wcel fot2ndg_2 fot2ndg_5 wcel fot2ndg_0 fot2ndg_1 fot2ndg_2 cotp c1st cfv c2nd cfv fot2ndg_1 wceq fot2ndg_2 fot2ndg_5 wcel fot2ndg_0 fot2ndg_3 wcel fot2ndg_1 fot2ndg_4 wcel wa fot2ndg_0 fot2ndg_1 fot2ndg_2 cotp c1st cfv c2nd cfv fot2ndg_0 fot2ndg_1 cop c2nd cfv fot2ndg_1 fot2ndg_2 fot2ndg_5 wcel fot2ndg_0 fot2ndg_1 fot2ndg_2 cotp c1st cfv fot2ndg_0 fot2ndg_1 cop c2nd fot2ndg_2 fot2ndg_5 wcel fot2ndg_0 fot2ndg_1 fot2ndg_2 cotp c1st cfv fot2ndg_0 fot2ndg_1 cop fot2ndg_2 cop c1st cfv fot2ndg_0 fot2ndg_1 cop fot2ndg_0 fot2ndg_1 fot2ndg_2 cotp fot2ndg_0 fot2ndg_1 cop fot2ndg_2 cop c1st fot2ndg_0 fot2ndg_1 fot2ndg_2 df-ot fveq2i fot2ndg_0 fot2ndg_1 cop cvv wcel fot2ndg_2 fot2ndg_5 wcel fot2ndg_0 fot2ndg_1 cop fot2ndg_2 cop c1st cfv fot2ndg_0 fot2ndg_1 cop wceq fot2ndg_0 fot2ndg_1 opex fot2ndg_0 fot2ndg_1 cop fot2ndg_2 cvv fot2ndg_5 op1stg mpan syl5eq fveq2d fot2ndg_0 fot2ndg_1 fot2ndg_3 fot2ndg_4 op2ndg sylan9eqr 3impa $.
$}
$( Extract the third member of an ordered triple.  (See ~ ot1stg comment.)
       (Contributed by NM, 3-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	fot3rdg_0 $f class A $.
	fot3rdg_1 $f class B $.
	fot3rdg_2 $f class C $.
	fot3rdg_3 $f class V $.
	ot3rdg $p |- ( C e. V -> ( 2nd ` <. A , B , C >. ) = C ) $= fot3rdg_2 fot3rdg_3 wcel fot3rdg_0 fot3rdg_1 fot3rdg_2 cotp c2nd cfv fot3rdg_0 fot3rdg_1 cop fot3rdg_2 cop c2nd cfv fot3rdg_2 fot3rdg_0 fot3rdg_1 fot3rdg_2 cotp fot3rdg_0 fot3rdg_1 cop fot3rdg_2 cop c2nd fot3rdg_0 fot3rdg_1 fot3rdg_2 df-ot fveq2i fot3rdg_0 fot3rdg_1 cop cvv wcel fot3rdg_2 fot3rdg_3 wcel fot3rdg_0 fot3rdg_1 cop fot3rdg_2 cop c2nd cfv fot3rdg_2 wceq fot3rdg_0 fot3rdg_1 opex fot3rdg_0 fot3rdg_1 cop fot3rdg_2 cvv fot3rdg_3 op2ndg mpan syl5eq $.
$}
$( Alternate value of the function that extracts the first member of an
       ordered pair.  Definition 5.13 (i) of [Monk1] p. 52.  (Contributed by
       NM, 18-Aug-2006.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	$d x y $.
	i1stval2_0 $f set x $.
	i1stval2_1 $f set y $.
	f1stval2_0 $f class A $.
	1stval2 $p |- ( A e. ( _V X. _V ) -> ( 1st ` A ) = |^| |^| A ) $= f1stval2_0 cvv cvv cxp wcel f1stval2_0 i1stval2_0 cv i1stval2_1 cv cop wceq i1stval2_1 wex i1stval2_0 wex f1stval2_0 c1st cfv f1stval2_0 cint cint wceq i1stval2_0 i1stval2_1 f1stval2_0 elvv f1stval2_0 i1stval2_0 cv i1stval2_1 cv cop wceq f1stval2_0 c1st cfv f1stval2_0 cint cint wceq i1stval2_0 i1stval2_1 f1stval2_0 i1stval2_0 cv i1stval2_1 cv cop wceq i1stval2_0 cv i1stval2_1 cv cop c1st cfv i1stval2_0 cv i1stval2_1 cv cop cint cint f1stval2_0 c1st cfv f1stval2_0 cint cint i1stval2_0 cv i1stval2_1 cv cop c1st cfv i1stval2_0 cv i1stval2_0 cv i1stval2_1 cv cop cint cint i1stval2_0 cv i1stval2_1 cv i1stval2_0 vex i1stval2_1 vex op1st i1stval2_0 cv i1stval2_1 cv i1stval2_0 vex i1stval2_1 vex op1stb eqtr4i f1stval2_0 i1stval2_0 cv i1stval2_1 cv cop c1st fveq2 f1stval2_0 i1stval2_0 cv i1stval2_1 cv cop wceq f1stval2_0 cint i1stval2_0 cv i1stval2_1 cv cop cint f1stval2_0 i1stval2_0 cv i1stval2_1 cv cop inteq inteqd 3eqtr4a exlimivv sylbi $.
$}
$( Alternate value of the function that extracts the second member of an
       ordered pair.  Definition 5.13 (ii) of [Monk1] p. 52.  (Contributed by
       NM, 18-Aug-2006.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	$d x y $.
	i2ndval2_0 $f set x $.
	i2ndval2_1 $f set y $.
	f2ndval2_0 $f class A $.
	2ndval2 $p |- ( A e. ( _V X. _V ) -> ( 2nd ` A ) = |^| |^| |^| `' { A } ) $= f2ndval2_0 cvv cvv cxp wcel f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop wceq i2ndval2_1 wex i2ndval2_0 wex f2ndval2_0 c2nd cfv f2ndval2_0 csn ccnv cint cint cint wceq i2ndval2_0 i2ndval2_1 f2ndval2_0 elvv f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop wceq f2ndval2_0 c2nd cfv f2ndval2_0 csn ccnv cint cint cint wceq i2ndval2_0 i2ndval2_1 f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop wceq i2ndval2_0 cv i2ndval2_1 cv cop c2nd cfv i2ndval2_0 cv i2ndval2_1 cv cop csn ccnv cint cint cint f2ndval2_0 c2nd cfv f2ndval2_0 csn ccnv cint cint cint i2ndval2_0 cv i2ndval2_1 cv cop c2nd cfv i2ndval2_1 cv i2ndval2_0 cv i2ndval2_1 cv cop csn ccnv cint cint cint i2ndval2_0 cv i2ndval2_1 cv i2ndval2_0 vex i2ndval2_1 vex op2nd i2ndval2_0 cv i2ndval2_1 cv i2ndval2_0 vex i2ndval2_1 vex op2ndb eqtr4i f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop c2nd fveq2 f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop wceq f2ndval2_0 csn ccnv cint cint i2ndval2_0 cv i2ndval2_1 cv cop csn ccnv cint cint f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop wceq f2ndval2_0 csn ccnv cint i2ndval2_0 cv i2ndval2_1 cv cop csn ccnv cint f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop wceq f2ndval2_0 csn ccnv i2ndval2_0 cv i2ndval2_1 cv cop csn ccnv f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop wceq f2ndval2_0 csn i2ndval2_0 cv i2ndval2_1 cv cop csn f2ndval2_0 i2ndval2_0 cv i2ndval2_1 cv cop sneq cnveqd inteqd inteqd inteqd 3eqtr4a exlimivv sylbi $.
$}
$( The ` 1st ` function maps the universe onto the universe.  (Contributed
       by NM, 14-Oct-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	$d x y $.
	$d x y $.
	ifo1st_0 $f set x $.
	ifo1st_1 $f set y $.
	fo1st $p |- 1st : _V -onto-> _V $= cvv cvv c1st wfo c1st cvv wfn c1st crn cvv wceq ifo1st_0 cvv ifo1st_0 cv csn cdm cuni c1st ifo1st_0 cv csn cdm ifo1st_0 cv csn ifo1st_0 cv snex dmex uniex ifo1st_0 df-1st fnmpti c1st crn ifo1st_1 cv ifo1st_0 cv csn cdm cuni wceq ifo1st_0 cvv wrex ifo1st_1 cab cvv ifo1st_0 ifo1st_1 cvv ifo1st_0 cv csn cdm cuni c1st ifo1st_0 df-1st rnmpt ifo1st_1 cv ifo1st_0 cv csn cdm cuni wceq ifo1st_0 cvv wrex ifo1st_1 cvv ifo1st_1 cv cvv wcel ifo1st_1 cv ifo1st_0 cv csn cdm cuni wceq ifo1st_0 cvv wrex ifo1st_1 vex ifo1st_1 cv ifo1st_1 cv cop cvv wcel ifo1st_1 cv ifo1st_1 cv ifo1st_1 cv cop csn cdm cuni wceq ifo1st_1 cv ifo1st_0 cv csn cdm cuni wceq ifo1st_0 cvv wrex ifo1st_1 cv ifo1st_1 cv opex ifo1st_1 cv ifo1st_1 cv cop csn cdm cuni ifo1st_1 cv ifo1st_1 cv ifo1st_1 cv ifo1st_1 vex ifo1st_1 vex op1sta eqcomi ifo1st_1 cv ifo1st_0 cv csn cdm cuni wceq ifo1st_1 cv ifo1st_1 cv ifo1st_1 cv cop csn cdm cuni wceq ifo1st_0 ifo1st_1 cv ifo1st_1 cv cop cvv ifo1st_0 cv ifo1st_1 cv ifo1st_1 cv cop wceq ifo1st_0 cv csn cdm cuni ifo1st_1 cv ifo1st_1 cv cop csn cdm cuni ifo1st_1 cv ifo1st_0 cv ifo1st_1 cv ifo1st_1 cv cop wceq ifo1st_0 cv csn cdm ifo1st_1 cv ifo1st_1 cv cop csn cdm ifo1st_0 cv ifo1st_1 cv ifo1st_1 cv cop wceq ifo1st_0 cv csn ifo1st_1 cv ifo1st_1 cv cop csn ifo1st_0 cv ifo1st_1 cv ifo1st_1 cv cop sneq dmeqd unieqd eqeq2d rspcev mp2an 2th abbi2i eqtr4i cvv cvv c1st df-fo mpbir2an $.
$}
$( The ` 2nd ` function maps the universe onto the universe.  (Contributed
       by NM, 14-Oct-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	ifo2nd_0 $f set x $.
	ifo2nd_1 $f set y $.
	fo2nd $p |- 2nd : _V -onto-> _V $= cvv cvv c2nd wfo c2nd cvv wfn c2nd crn cvv wceq ifo2nd_0 cvv ifo2nd_0 cv csn crn cuni c2nd ifo2nd_0 cv csn crn ifo2nd_0 cv csn ifo2nd_0 cv snex rnex uniex ifo2nd_0 df-2nd fnmpti c2nd crn ifo2nd_1 cv ifo2nd_0 cv csn crn cuni wceq ifo2nd_0 cvv wrex ifo2nd_1 cab cvv ifo2nd_0 ifo2nd_1 cvv ifo2nd_0 cv csn crn cuni c2nd ifo2nd_0 df-2nd rnmpt ifo2nd_1 cv ifo2nd_0 cv csn crn cuni wceq ifo2nd_0 cvv wrex ifo2nd_1 cvv ifo2nd_1 cv cvv wcel ifo2nd_1 cv ifo2nd_0 cv csn crn cuni wceq ifo2nd_0 cvv wrex ifo2nd_1 vex ifo2nd_1 cv ifo2nd_1 cv cop cvv wcel ifo2nd_1 cv ifo2nd_1 cv ifo2nd_1 cv cop csn crn cuni wceq ifo2nd_1 cv ifo2nd_0 cv csn crn cuni wceq ifo2nd_0 cvv wrex ifo2nd_1 cv ifo2nd_1 cv opex ifo2nd_1 cv ifo2nd_1 cv cop csn crn cuni ifo2nd_1 cv ifo2nd_1 cv ifo2nd_1 cv ifo2nd_1 vex ifo2nd_1 vex op2nda eqcomi ifo2nd_1 cv ifo2nd_0 cv csn crn cuni wceq ifo2nd_1 cv ifo2nd_1 cv ifo2nd_1 cv cop csn crn cuni wceq ifo2nd_0 ifo2nd_1 cv ifo2nd_1 cv cop cvv ifo2nd_0 cv ifo2nd_1 cv ifo2nd_1 cv cop wceq ifo2nd_0 cv csn crn cuni ifo2nd_1 cv ifo2nd_1 cv cop csn crn cuni ifo2nd_1 cv ifo2nd_0 cv ifo2nd_1 cv ifo2nd_1 cv cop wceq ifo2nd_0 cv csn crn ifo2nd_1 cv ifo2nd_1 cv cop csn crn ifo2nd_0 cv ifo2nd_1 cv ifo2nd_1 cv cop wceq ifo2nd_0 cv csn ifo2nd_1 cv ifo2nd_1 cv cop csn ifo2nd_0 cv ifo2nd_1 cv ifo2nd_1 cv cop sneq rneqd unieqd eqeq2d rspcev mp2an 2th abbi2i eqtr4i cvv cvv c2nd df-fo mpbir2an $.
$}
$( Mapping of a restriction of the ` 1st ` (first member of an ordered
       pair) function.  (Contributed by NM, 11-Oct-2004.)  (Revised by Mario
       Carneiro, 8-Sep-2013.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d x y z A $.
	$d x y z B $.
	$d x y z $.
	$d x y z A $.
	$d x y z B $.
	$d x y z $.
	if1stres_0 $f set x $.
	if1stres_1 $f set y $.
	if1stres_2 $f set z $.
	ff1stres_0 $f class A $.
	ff1stres_1 $f class B $.
	f1stres $p |- ( 1st |` ( A X. B ) ) : ( A X. B ) --> A $= if1stres_0 cv csn cdm cuni ff1stres_0 wcel if1stres_0 ff1stres_0 ff1stres_1 cxp wral ff1stres_0 ff1stres_1 cxp ff1stres_0 c1st ff1stres_0 ff1stres_1 cxp cres wf if1stres_0 cv csn cdm cuni ff1stres_0 wcel if1stres_0 ff1stres_0 ff1stres_1 cxp wral if1stres_1 cv if1stres_2 cv cop csn cdm cuni ff1stres_0 wcel if1stres_2 ff1stres_1 wral if1stres_1 ff1stres_0 wral if1stres_1 cv if1stres_2 cv cop csn cdm cuni ff1stres_0 wcel if1stres_1 if1stres_2 ff1stres_0 ff1stres_1 if1stres_1 cv ff1stres_0 wcel if1stres_1 cv if1stres_2 cv cop csn cdm cuni ff1stres_0 wcel if1stres_2 cv ff1stres_1 wcel if1stres_1 cv if1stres_2 cv cop csn cdm cuni ff1stres_0 wcel if1stres_1 cv ff1stres_0 wcel if1stres_1 cv if1stres_2 cv cop csn cdm cuni if1stres_1 cv ff1stres_0 if1stres_1 cv if1stres_2 cv if1stres_1 vex if1stres_2 vex op1sta eleq1i biimpri adantr rgen2 if1stres_0 cv csn cdm cuni ff1stres_0 wcel if1stres_1 cv if1stres_2 cv cop csn cdm cuni ff1stres_0 wcel if1stres_0 if1stres_1 if1stres_2 ff1stres_0 ff1stres_1 if1stres_0 cv if1stres_1 cv if1stres_2 cv cop wceq if1stres_0 cv csn cdm cuni if1stres_1 cv if1stres_2 cv cop csn cdm cuni ff1stres_0 if1stres_0 cv if1stres_1 cv if1stres_2 cv cop wceq if1stres_0 cv csn cdm if1stres_1 cv if1stres_2 cv cop csn cdm if1stres_0 cv if1stres_1 cv if1stres_2 cv cop wceq if1stres_0 cv csn if1stres_1 cv if1stres_2 cv cop csn if1stres_0 cv if1stres_1 cv if1stres_2 cv cop sneq dmeqd unieqd eleq1d ralxp mpbir if1stres_0 ff1stres_0 ff1stres_1 cxp ff1stres_0 if1stres_0 cv csn cdm cuni c1st ff1stres_0 ff1stres_1 cxp cres c1st ff1stres_0 ff1stres_1 cxp cres if1stres_0 cvv if1stres_0 cv csn cdm cuni cmpt ff1stres_0 ff1stres_1 cxp cres if1stres_0 ff1stres_0 ff1stres_1 cxp if1stres_0 cv csn cdm cuni cmpt c1st if1stres_0 cvv if1stres_0 cv csn cdm cuni cmpt ff1stres_0 ff1stres_1 cxp if1stres_0 df-1st reseq1i ff1stres_0 ff1stres_1 cxp cvv wss if1stres_0 cvv if1stres_0 cv csn cdm cuni cmpt ff1stres_0 ff1stres_1 cxp cres if1stres_0 ff1stres_0 ff1stres_1 cxp if1stres_0 cv csn cdm cuni cmpt wceq ff1stres_0 ff1stres_1 cxp ssv if1stres_0 cvv ff1stres_0 ff1stres_1 cxp if1stres_0 cv csn cdm cuni resmpt ax-mp eqtri fmpt mpbi $.
$}
$( Mapping of a restriction of the ` 2nd ` (second member of an ordered
       pair) function.  (Contributed by NM, 7-Aug-2006.)  (Revised by Mario
       Carneiro, 8-Sep-2013.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d x y z A $.
	$d x y z B $.
	$d x y z $.
	$d x y z A $.
	$d x y z B $.
	$d x y z $.
	if2ndres_0 $f set x $.
	if2ndres_1 $f set y $.
	if2ndres_2 $f set z $.
	ff2ndres_0 $f class A $.
	ff2ndres_1 $f class B $.
	f2ndres $p |- ( 2nd |` ( A X. B ) ) : ( A X. B ) --> B $= if2ndres_0 cv csn crn cuni ff2ndres_1 wcel if2ndres_0 ff2ndres_0 ff2ndres_1 cxp wral ff2ndres_0 ff2ndres_1 cxp ff2ndres_1 c2nd ff2ndres_0 ff2ndres_1 cxp cres wf if2ndres_0 cv csn crn cuni ff2ndres_1 wcel if2ndres_0 ff2ndres_0 ff2ndres_1 cxp wral if2ndres_1 cv if2ndres_2 cv cop csn crn cuni ff2ndres_1 wcel if2ndres_2 ff2ndres_1 wral if2ndres_1 ff2ndres_0 wral if2ndres_1 cv if2ndres_2 cv cop csn crn cuni ff2ndres_1 wcel if2ndres_1 if2ndres_2 ff2ndres_0 ff2ndres_1 if2ndres_2 cv ff2ndres_1 wcel if2ndres_1 cv if2ndres_2 cv cop csn crn cuni ff2ndres_1 wcel if2ndres_1 cv ff2ndres_0 wcel if2ndres_1 cv if2ndres_2 cv cop csn crn cuni ff2ndres_1 wcel if2ndres_2 cv ff2ndres_1 wcel if2ndres_1 cv if2ndres_2 cv cop csn crn cuni if2ndres_2 cv ff2ndres_1 if2ndres_1 cv if2ndres_2 cv if2ndres_1 vex if2ndres_2 vex op2nda eleq1i biimpri adantl rgen2 if2ndres_0 cv csn crn cuni ff2ndres_1 wcel if2ndres_1 cv if2ndres_2 cv cop csn crn cuni ff2ndres_1 wcel if2ndres_0 if2ndres_1 if2ndres_2 ff2ndres_0 ff2ndres_1 if2ndres_0 cv if2ndres_1 cv if2ndres_2 cv cop wceq if2ndres_0 cv csn crn cuni if2ndres_1 cv if2ndres_2 cv cop csn crn cuni ff2ndres_1 if2ndres_0 cv if2ndres_1 cv if2ndres_2 cv cop wceq if2ndres_0 cv csn crn if2ndres_1 cv if2ndres_2 cv cop csn crn if2ndres_0 cv if2ndres_1 cv if2ndres_2 cv cop wceq if2ndres_0 cv csn if2ndres_1 cv if2ndres_2 cv cop csn if2ndres_0 cv if2ndres_1 cv if2ndres_2 cv cop sneq rneqd unieqd eleq1d ralxp mpbir if2ndres_0 ff2ndres_0 ff2ndres_1 cxp ff2ndres_1 if2ndres_0 cv csn crn cuni c2nd ff2ndres_0 ff2ndres_1 cxp cres c2nd ff2ndres_0 ff2ndres_1 cxp cres if2ndres_0 cvv if2ndres_0 cv csn crn cuni cmpt ff2ndres_0 ff2ndres_1 cxp cres if2ndres_0 ff2ndres_0 ff2ndres_1 cxp if2ndres_0 cv csn crn cuni cmpt c2nd if2ndres_0 cvv if2ndres_0 cv csn crn cuni cmpt ff2ndres_0 ff2ndres_1 cxp if2ndres_0 df-2nd reseq1i ff2ndres_0 ff2ndres_1 cxp cvv wss if2ndres_0 cvv if2ndres_0 cv csn crn cuni cmpt ff2ndres_0 ff2ndres_1 cxp cres if2ndres_0 ff2ndres_0 ff2ndres_1 cxp if2ndres_0 cv csn crn cuni cmpt wceq ff2ndres_0 ff2ndres_1 cxp ssv if2ndres_0 cvv ff2ndres_0 ff2ndres_1 cxp if2ndres_0 cv csn crn cuni resmpt ax-mp eqtri fmpt mpbi $.
$}
$( Onto mapping of a restriction of the ` 1st ` (first member of an ordered
       pair) function.  (Contributed by NM, 14-Dec-2008.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x y B $.
	$d x y $.
	$d x y A $.
	$d x y B $.
	$d x y $.
	ifo1stres_0 $f set x $.
	ifo1stres_1 $f set y $.
	ffo1stres_0 $f class A $.
	ffo1stres_1 $f class B $.
	fo1stres $p |- ( B =/= (/) -> ( 1st |` ( A X. B ) ) : ( A X. B ) -onto-> A ) $= ffo1stres_1 c0 wne ffo1stres_0 ffo1stres_1 cxp ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres wf c1st ffo1stres_0 ffo1stres_1 cxp cres crn ffo1stres_0 wceq wa ffo1stres_0 ffo1stres_1 cxp ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres wfo ffo1stres_1 c0 wne c1st ffo1stres_0 ffo1stres_1 cxp cres crn ffo1stres_0 wceq ffo1stres_0 ffo1stres_1 cxp ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres wf ffo1stres_1 c0 wne c1st ffo1stres_0 ffo1stres_1 cxp cres crn ffo1stres_0 wss ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres crn wss wa c1st ffo1stres_0 ffo1stres_1 cxp cres crn ffo1stres_0 wceq ffo1stres_1 c0 wne ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres crn wss c1st ffo1stres_0 ffo1stres_1 cxp cres crn ffo1stres_0 wss ffo1stres_1 c0 wne ifo1stres_0 ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres crn ffo1stres_1 c0 wne ifo1stres_1 cv ffo1stres_1 wcel ifo1stres_1 wex ifo1stres_0 cv ffo1stres_0 wcel ifo1stres_0 cv c1st ffo1stres_0 ffo1stres_1 cxp cres crn wcel wi ifo1stres_1 ffo1stres_1 n0 ifo1stres_1 cv ffo1stres_1 wcel ifo1stres_0 cv ffo1stres_0 wcel ifo1stres_0 cv c1st ffo1stres_0 ffo1stres_1 cxp cres crn wcel wi ifo1stres_1 ifo1stres_0 cv ffo1stres_0 wcel ifo1stres_1 cv ffo1stres_1 wcel ifo1stres_0 cv c1st ffo1stres_0 ffo1stres_1 cxp cres crn wcel ifo1stres_0 cv ffo1stres_0 wcel ifo1stres_1 cv ffo1stres_1 wcel wa ifo1stres_0 cv ifo1stres_1 cv cop ffo1stres_0 ffo1stres_1 cxp wcel ifo1stres_0 cv c1st ffo1stres_0 ffo1stres_1 cxp cres crn wcel ifo1stres_0 cv ifo1stres_1 cv ffo1stres_0 ffo1stres_1 opelxp ifo1stres_0 cv ifo1stres_1 cv cop ffo1stres_0 ffo1stres_1 cxp wcel ifo1stres_0 cv ifo1stres_0 cv ifo1stres_1 cv cop c1st ffo1stres_0 ffo1stres_1 cxp cres cfv c1st ffo1stres_0 ffo1stres_1 cxp cres crn ifo1stres_0 cv ifo1stres_1 cv cop ffo1stres_0 ffo1stres_1 cxp wcel ifo1stres_0 cv ifo1stres_1 cv cop c1st ffo1stres_0 ffo1stres_1 cxp cres cfv ifo1stres_0 cv ifo1stres_1 cv cop c1st cfv ifo1stres_0 cv ifo1stres_0 cv ifo1stres_1 cv cop ffo1stres_0 ffo1stres_1 cxp c1st fvres ifo1stres_0 cv ifo1stres_1 cv ifo1stres_0 vex ifo1stres_1 vex op1st syl6req c1st ffo1stres_0 ffo1stres_1 cxp cres ffo1stres_0 ffo1stres_1 cxp wfn ifo1stres_0 cv ifo1stres_1 cv cop ffo1stres_0 ffo1stres_1 cxp wcel ifo1stres_0 cv ifo1stres_1 cv cop c1st ffo1stres_0 ffo1stres_1 cxp cres cfv c1st ffo1stres_0 ffo1stres_1 cxp cres crn wcel ffo1stres_0 ffo1stres_1 cxp ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres wf c1st ffo1stres_0 ffo1stres_1 cxp cres ffo1stres_0 ffo1stres_1 cxp wfn ffo1stres_0 ffo1stres_1 f1stres ffo1stres_0 ffo1stres_1 cxp ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres ffn ax-mp ffo1stres_0 ffo1stres_1 cxp ifo1stres_0 cv ifo1stres_1 cv cop c1st ffo1stres_0 ffo1stres_1 cxp cres fnfvelrn mpan eqeltrd sylbir expcom exlimiv sylbi ssrdv ffo1stres_0 ffo1stres_1 cxp ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres wf c1st ffo1stres_0 ffo1stres_1 cxp cres crn ffo1stres_0 wss ffo1stres_0 ffo1stres_1 f1stres ffo1stres_0 ffo1stres_1 cxp ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres frn ax-mp jctil c1st ffo1stres_0 ffo1stres_1 cxp cres crn ffo1stres_0 eqss sylibr ffo1stres_0 ffo1stres_1 f1stres jctil ffo1stres_0 ffo1stres_1 cxp ffo1stres_0 c1st ffo1stres_0 ffo1stres_1 cxp cres dffo2 sylibr $.
$}
$( Onto mapping of a restriction of the ` 2nd ` (second member of an
       ordered pair) function.  (Contributed by NM, 14-Dec-2008.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x y B $.
	$d x y $.
	$d x y A $.
	$d x y B $.
	$d x y $.
	ifo2ndres_0 $f set x $.
	ifo2ndres_1 $f set y $.
	ffo2ndres_0 $f class A $.
	ffo2ndres_1 $f class B $.
	fo2ndres $p |- ( A =/= (/) -> ( 2nd |` ( A X. B ) ) : ( A X. B ) -onto-> B ) $= ffo2ndres_0 c0 wne ffo2ndres_0 ffo2ndres_1 cxp ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres wf c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ffo2ndres_1 wceq wa ffo2ndres_0 ffo2ndres_1 cxp ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres wfo ffo2ndres_0 c0 wne c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ffo2ndres_1 wceq ffo2ndres_0 ffo2ndres_1 cxp ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres wf ffo2ndres_0 c0 wne c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ffo2ndres_1 wss ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn wss wa c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ffo2ndres_1 wceq ffo2ndres_0 c0 wne ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn wss c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ffo2ndres_1 wss ffo2ndres_0 c0 wne ifo2ndres_1 ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ffo2ndres_0 c0 wne ifo2ndres_0 cv ffo2ndres_0 wcel ifo2ndres_0 wex ifo2ndres_1 cv ffo2ndres_1 wcel ifo2ndres_1 cv c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn wcel wi ifo2ndres_0 ffo2ndres_0 n0 ifo2ndres_0 cv ffo2ndres_0 wcel ifo2ndres_1 cv ffo2ndres_1 wcel ifo2ndres_1 cv c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn wcel wi ifo2ndres_0 ifo2ndres_0 cv ffo2ndres_0 wcel ifo2ndres_1 cv ffo2ndres_1 wcel ifo2ndres_1 cv c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn wcel ifo2ndres_0 cv ffo2ndres_0 wcel ifo2ndres_1 cv ffo2ndres_1 wcel wa ifo2ndres_0 cv ifo2ndres_1 cv cop ffo2ndres_0 ffo2ndres_1 cxp wcel ifo2ndres_1 cv c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn wcel ifo2ndres_0 cv ifo2ndres_1 cv ffo2ndres_0 ffo2ndres_1 opelxp ifo2ndres_0 cv ifo2ndres_1 cv cop ffo2ndres_0 ffo2ndres_1 cxp wcel ifo2ndres_1 cv ifo2ndres_0 cv ifo2ndres_1 cv cop c2nd ffo2ndres_0 ffo2ndres_1 cxp cres cfv c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ifo2ndres_0 cv ifo2ndres_1 cv cop ffo2ndres_0 ffo2ndres_1 cxp wcel ifo2ndres_0 cv ifo2ndres_1 cv cop c2nd ffo2ndres_0 ffo2ndres_1 cxp cres cfv ifo2ndres_0 cv ifo2ndres_1 cv cop c2nd cfv ifo2ndres_1 cv ifo2ndres_0 cv ifo2ndres_1 cv cop ffo2ndres_0 ffo2ndres_1 cxp c2nd fvres ifo2ndres_0 cv ifo2ndres_1 cv ifo2ndres_0 vex ifo2ndres_1 vex op2nd syl6req c2nd ffo2ndres_0 ffo2ndres_1 cxp cres ffo2ndres_0 ffo2ndres_1 cxp wfn ifo2ndres_0 cv ifo2ndres_1 cv cop ffo2ndres_0 ffo2ndres_1 cxp wcel ifo2ndres_0 cv ifo2ndres_1 cv cop c2nd ffo2ndres_0 ffo2ndres_1 cxp cres cfv c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn wcel ffo2ndres_0 ffo2ndres_1 cxp ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres wf c2nd ffo2ndres_0 ffo2ndres_1 cxp cres ffo2ndres_0 ffo2ndres_1 cxp wfn ffo2ndres_0 ffo2ndres_1 f2ndres ffo2ndres_0 ffo2ndres_1 cxp ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres ffn ax-mp ffo2ndres_0 ffo2ndres_1 cxp ifo2ndres_0 cv ifo2ndres_1 cv cop c2nd ffo2ndres_0 ffo2ndres_1 cxp cres fnfvelrn mpan eqeltrd sylbir ex exlimiv sylbi ssrdv ffo2ndres_0 ffo2ndres_1 cxp ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres wf c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ffo2ndres_1 wss ffo2ndres_0 ffo2ndres_1 f2ndres ffo2ndres_0 ffo2ndres_1 cxp ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres frn ax-mp jctil c2nd ffo2ndres_0 ffo2ndres_1 cxp cres crn ffo2ndres_1 eqss sylibr ffo2ndres_0 ffo2ndres_1 f2ndres jctil ffo2ndres_0 ffo2ndres_1 cxp ffo2ndres_1 c2nd ffo2ndres_0 ffo2ndres_1 cxp cres dffo2 sylibr $.
$}
$( Value of an alternate definition of the ` 1st ` function.  (Contributed
       by NM, 14-Oct-2004.)  (Revised by Mario Carneiro, 30-Dec-2014.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v A $.
	$d x y z w v $.
	$d v w A $.
	i1st2val_0 $f set w $.
	i1st2val_1 $f set v $.
	f1st2val_0 $f set x $.
	f1st2val_1 $f set y $.
	f1st2val_2 $f set z $.
	f1st2val_3 $f class A $.
	1st2val $p |- ( { <. <. x , y >. , z >. | z = x } ` A ) = ( 1st ` A ) $= f1st2val_3 cvv cvv cxp wcel f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv f1st2val_3 c1st cfv wceq f1st2val_3 cvv cvv cxp wcel f1st2val_3 i1st2val_0 cv i1st2val_1 cv cop wceq i1st2val_1 wex i1st2val_0 wex f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv f1st2val_3 c1st cfv wceq i1st2val_0 i1st2val_1 f1st2val_3 elvv f1st2val_3 i1st2val_0 cv i1st2val_1 cv cop wceq f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv f1st2val_3 c1st cfv wceq i1st2val_0 i1st2val_1 f1st2val_3 i1st2val_0 cv i1st2val_1 cv cop wceq f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv i1st2val_0 cv f1st2val_3 c1st cfv f1st2val_3 i1st2val_0 cv i1st2val_1 cv cop wceq f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv i1st2val_0 cv i1st2val_1 cv cop f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv i1st2val_0 cv f1st2val_3 i1st2val_0 cv i1st2val_1 cv cop f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab fveq2 i1st2val_0 cv i1st2val_1 cv f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab co i1st2val_0 cv i1st2val_1 cv cop f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv i1st2val_0 cv i1st2val_0 cv i1st2val_1 cv f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab df-ov i1st2val_0 cv cvv wcel i1st2val_1 cv cvv wcel i1st2val_0 cv i1st2val_1 cv f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab co i1st2val_0 cv wceq i1st2val_0 vex i1st2val_1 vex f1st2val_0 f1st2val_1 i1st2val_0 cv i1st2val_1 cv cvv cvv f1st2val_0 cv i1st2val_0 cv f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab f1st2val_0 cv i1st2val_0 cv wceq f1st2val_1 cv i1st2val_1 cv wceq simpl f1st2val_0 f1st2val_1 cvv cvv f1st2val_0 cv cmpt2 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab f1st2val_0 f1st2val_1 f1st2val_2 f1st2val_0 cv mpt2v eqcomi i1st2val_0 vex ovmpt2a mp2an eqtr3i syl6eq i1st2val_0 cv i1st2val_1 cv f1st2val_3 i1st2val_0 vex i1st2val_1 vex op1std eqtr4d exlimivv sylbi f1st2val_3 cvv cvv cxp wcel wn f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv f1st2val_3 csn cdm cuni f1st2val_3 c1st cfv f1st2val_3 cvv cvv cxp wcel wn f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv c0 f1st2val_3 csn cdm cuni f1st2val_3 cvv cvv cxp wcel f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cdm wcel f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cfv c0 wceq f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cdm cvv cvv cxp f1st2val_3 f1st2val_0 cv cvv wcel f1st2val_1 cv cvv wcel wa f1st2val_0 f1st2val_1 copab f1st2val_2 cv f1st2val_0 cv wceq f1st2val_2 wex f1st2val_0 f1st2val_1 copab cvv cvv cxp f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab cdm f1st2val_0 cv cvv wcel f1st2val_1 cv cvv wcel wa f1st2val_2 cv f1st2val_0 cv wceq f1st2val_2 wex f1st2val_0 f1st2val_1 f1st2val_0 cv cvv wcel f1st2val_1 cv cvv wcel wa f1st2val_2 cv f1st2val_0 cv wceq f1st2val_2 wex f1st2val_0 cv cvv wcel f1st2val_1 cv cvv wcel f1st2val_0 vex f1st2val_1 vex pm3.2i f1st2val_2 f1st2val_0 a9ev 2th opabbii f1st2val_0 f1st2val_1 cvv cvv df-xp f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 dmoprab 3eqtr4ri eleq2i f1st2val_3 f1st2val_2 cv f1st2val_0 cv wceq f1st2val_0 f1st2val_1 f1st2val_2 coprab ndmfv sylnbir f1st2val_3 cvv cvv cxp wcel wn f1st2val_3 csn cdm cuni c0 cuni c0 f1st2val_3 cvv cvv cxp wcel wn f1st2val_3 csn cdm c0 f1st2val_3 cvv cvv cxp wcel f1st2val_3 csn cdm c0 f1st2val_3 cvv cvv cxp wcel f1st2val_3 csn cdm c0 wne f1st2val_3 dmsnn0 biimpri necon1bi unieqd uni0 syl6eq eqtr4d f1st2val_3 1stval syl6eqr pm2.61i $.
$}
$( Value of an alternate definition of the ` 2nd ` function.  (Contributed
       by NM, 10-Aug-2006.)  (Revised by Mario Carneiro, 30-Dec-2014.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v A $.
	$d x y z w v $.
	$d v w A $.
	i2nd2val_0 $f set w $.
	i2nd2val_1 $f set v $.
	f2nd2val_0 $f set x $.
	f2nd2val_1 $f set y $.
	f2nd2val_2 $f set z $.
	f2nd2val_3 $f class A $.
	2nd2val $p |- ( { <. <. x , y >. , z >. | z = y } ` A ) = ( 2nd ` A ) $= f2nd2val_3 cvv cvv cxp wcel f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv f2nd2val_3 c2nd cfv wceq f2nd2val_3 cvv cvv cxp wcel f2nd2val_3 i2nd2val_0 cv i2nd2val_1 cv cop wceq i2nd2val_1 wex i2nd2val_0 wex f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv f2nd2val_3 c2nd cfv wceq i2nd2val_0 i2nd2val_1 f2nd2val_3 elvv f2nd2val_3 i2nd2val_0 cv i2nd2val_1 cv cop wceq f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv f2nd2val_3 c2nd cfv wceq i2nd2val_0 i2nd2val_1 f2nd2val_3 i2nd2val_0 cv i2nd2val_1 cv cop wceq f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv i2nd2val_1 cv f2nd2val_3 c2nd cfv f2nd2val_3 i2nd2val_0 cv i2nd2val_1 cv cop wceq f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv i2nd2val_0 cv i2nd2val_1 cv cop f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv i2nd2val_1 cv f2nd2val_3 i2nd2val_0 cv i2nd2val_1 cv cop f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab fveq2 i2nd2val_0 cv i2nd2val_1 cv f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab co i2nd2val_0 cv i2nd2val_1 cv cop f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv i2nd2val_1 cv i2nd2val_0 cv i2nd2val_1 cv f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab df-ov i2nd2val_0 cv cvv wcel i2nd2val_1 cv cvv wcel i2nd2val_0 cv i2nd2val_1 cv f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab co i2nd2val_1 cv wceq i2nd2val_0 vex i2nd2val_1 vex f2nd2val_0 f2nd2val_1 i2nd2val_0 cv i2nd2val_1 cv cvv cvv f2nd2val_1 cv i2nd2val_1 cv f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab f2nd2val_0 cv i2nd2val_0 cv wceq f2nd2val_1 cv i2nd2val_1 cv wceq simpr f2nd2val_0 f2nd2val_1 cvv cvv f2nd2val_1 cv cmpt2 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab f2nd2val_0 f2nd2val_1 f2nd2val_2 f2nd2val_1 cv mpt2v eqcomi i2nd2val_1 vex ovmpt2a mp2an eqtr3i syl6eq i2nd2val_0 cv i2nd2val_1 cv f2nd2val_3 i2nd2val_0 vex i2nd2val_1 vex op2ndd eqtr4d exlimivv sylbi f2nd2val_3 cvv cvv cxp wcel wn f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv f2nd2val_3 csn crn cuni f2nd2val_3 c2nd cfv f2nd2val_3 cvv cvv cxp wcel wn f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv c0 f2nd2val_3 csn crn cuni f2nd2val_3 cvv cvv cxp wcel f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cdm wcel f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cfv c0 wceq f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cdm cvv cvv cxp f2nd2val_3 f2nd2val_0 cv cvv wcel f2nd2val_1 cv cvv wcel wa f2nd2val_0 f2nd2val_1 copab f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_2 wex f2nd2val_0 f2nd2val_1 copab cvv cvv cxp f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab cdm f2nd2val_0 cv cvv wcel f2nd2val_1 cv cvv wcel wa f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_2 wex f2nd2val_0 f2nd2val_1 f2nd2val_0 cv cvv wcel f2nd2val_1 cv cvv wcel wa f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_2 wex f2nd2val_0 cv cvv wcel f2nd2val_1 cv cvv wcel f2nd2val_0 vex f2nd2val_1 vex pm3.2i f2nd2val_2 f2nd2val_1 a9ev 2th opabbii f2nd2val_0 f2nd2val_1 cvv cvv df-xp f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 dmoprab 3eqtr4ri eleq2i f2nd2val_3 f2nd2val_2 cv f2nd2val_1 cv wceq f2nd2val_0 f2nd2val_1 f2nd2val_2 coprab ndmfv sylnbir f2nd2val_3 cvv cvv cxp wcel wn f2nd2val_3 csn crn cuni c0 cuni c0 f2nd2val_3 cvv cvv cxp wcel wn f2nd2val_3 csn crn c0 f2nd2val_3 cvv cvv cxp wcel f2nd2val_3 csn crn c0 f2nd2val_3 cvv cvv cxp wcel f2nd2val_3 csn crn c0 wne f2nd2val_3 rnsnn0 biimpri necon1bi unieqd uni0 syl6eq eqtr4d f2nd2val_3 2ndval syl6eqr pm2.61i $.
$}
$( Composition of the first member function with another function.
     (Contributed by NM, 12-Oct-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	f1stcof_0 $f class A $.
	f1stcof_1 $f class B $.
	f1stcof_2 $f class C $.
	f1stcof_3 $f class F $.
	1stcof $p |- ( F : A --> ( B X. C ) -> ( 1st o. F ) : A --> B ) $= f1stcof_0 f1stcof_1 f1stcof_2 cxp f1stcof_3 wf c1st f1stcof_3 ccom f1stcof_0 wfn c1st f1stcof_3 ccom crn f1stcof_1 wss f1stcof_0 f1stcof_1 c1st f1stcof_3 ccom wf f1stcof_0 f1stcof_1 f1stcof_2 cxp f1stcof_3 wf c1st cvv wfn f1stcof_0 cvv f1stcof_3 wf c1st f1stcof_3 ccom f1stcof_0 wfn cvv cvv c1st wfo c1st cvv wfn fo1st cvv cvv c1st fofn ax-mp f1stcof_0 f1stcof_1 f1stcof_2 cxp f1stcof_3 wf f1stcof_3 f1stcof_0 wfn f1stcof_0 cvv f1stcof_3 wf f1stcof_0 f1stcof_1 f1stcof_2 cxp f1stcof_3 ffn f1stcof_0 f1stcof_3 dffn2 sylib cvv f1stcof_0 c1st f1stcof_3 fnfco sylancr f1stcof_0 f1stcof_1 f1stcof_2 cxp f1stcof_3 wf c1st f1stcof_3 ccom crn c1st f1stcof_3 crn cres crn f1stcof_1 c1st f1stcof_3 rnco f1stcof_0 f1stcof_1 f1stcof_2 cxp f1stcof_3 wf c1st f1stcof_3 crn cres crn c1st f1stcof_1 f1stcof_2 cxp cres crn f1stcof_1 f1stcof_0 f1stcof_1 f1stcof_2 cxp f1stcof_3 wf f1stcof_3 crn f1stcof_1 f1stcof_2 cxp wss c1st f1stcof_3 crn cres c1st f1stcof_1 f1stcof_2 cxp cres wss c1st f1stcof_3 crn cres crn c1st f1stcof_1 f1stcof_2 cxp cres crn wss f1stcof_0 f1stcof_1 f1stcof_2 cxp f1stcof_3 frn f1stcof_3 crn f1stcof_1 f1stcof_2 cxp c1st ssres2 c1st f1stcof_3 crn cres c1st f1stcof_1 f1stcof_2 cxp cres rnss 3syl f1stcof_1 f1stcof_2 cxp f1stcof_1 c1st f1stcof_1 f1stcof_2 cxp cres wf c1st f1stcof_1 f1stcof_2 cxp cres crn f1stcof_1 wss f1stcof_1 f1stcof_2 f1stres f1stcof_1 f1stcof_2 cxp f1stcof_1 c1st f1stcof_1 f1stcof_2 cxp cres frn ax-mp syl6ss syl5eqss f1stcof_0 f1stcof_1 c1st f1stcof_3 ccom df-f sylanbrc $.
$}
$( Composition of the first member function with another function.
     (Contributed by FL, 15-Oct-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	f2ndcof_0 $f class A $.
	f2ndcof_1 $f class B $.
	f2ndcof_2 $f class C $.
	f2ndcof_3 $f class F $.
	2ndcof $p |- ( F : A --> ( B X. C ) -> ( 2nd o. F ) : A --> C ) $= f2ndcof_0 f2ndcof_1 f2ndcof_2 cxp f2ndcof_3 wf c2nd f2ndcof_3 ccom f2ndcof_0 wfn c2nd f2ndcof_3 ccom crn f2ndcof_2 wss f2ndcof_0 f2ndcof_2 c2nd f2ndcof_3 ccom wf f2ndcof_0 f2ndcof_1 f2ndcof_2 cxp f2ndcof_3 wf c2nd cvv wfn f2ndcof_0 cvv f2ndcof_3 wf c2nd f2ndcof_3 ccom f2ndcof_0 wfn cvv cvv c2nd wfo c2nd cvv wfn fo2nd cvv cvv c2nd fofn ax-mp f2ndcof_0 f2ndcof_1 f2ndcof_2 cxp f2ndcof_3 wf f2ndcof_3 f2ndcof_0 wfn f2ndcof_0 cvv f2ndcof_3 wf f2ndcof_0 f2ndcof_1 f2ndcof_2 cxp f2ndcof_3 ffn f2ndcof_0 f2ndcof_3 dffn2 sylib cvv f2ndcof_0 c2nd f2ndcof_3 fnfco sylancr f2ndcof_0 f2ndcof_1 f2ndcof_2 cxp f2ndcof_3 wf c2nd f2ndcof_3 ccom crn c2nd f2ndcof_3 crn cres crn f2ndcof_2 c2nd f2ndcof_3 rnco f2ndcof_0 f2ndcof_1 f2ndcof_2 cxp f2ndcof_3 wf c2nd f2ndcof_3 crn cres crn c2nd f2ndcof_1 f2ndcof_2 cxp cres crn f2ndcof_2 f2ndcof_0 f2ndcof_1 f2ndcof_2 cxp f2ndcof_3 wf f2ndcof_3 crn f2ndcof_1 f2ndcof_2 cxp wss c2nd f2ndcof_3 crn cres c2nd f2ndcof_1 f2ndcof_2 cxp cres wss c2nd f2ndcof_3 crn cres crn c2nd f2ndcof_1 f2ndcof_2 cxp cres crn wss f2ndcof_0 f2ndcof_1 f2ndcof_2 cxp f2ndcof_3 frn f2ndcof_3 crn f2ndcof_1 f2ndcof_2 cxp c2nd ssres2 c2nd f2ndcof_3 crn cres c2nd f2ndcof_1 f2ndcof_2 cxp cres rnss 3syl f2ndcof_1 f2ndcof_2 cxp f2ndcof_2 c2nd f2ndcof_1 f2ndcof_2 cxp cres wf c2nd f2ndcof_1 f2ndcof_2 cxp cres crn f2ndcof_2 wss f2ndcof_1 f2ndcof_2 f2ndres f2ndcof_1 f2ndcof_2 cxp f2ndcof_2 c2nd f2ndcof_1 f2ndcof_2 cxp cres frn ax-mp syl6ss syl5eqss f2ndcof_0 f2ndcof_2 c2nd f2ndcof_3 ccom df-f sylanbrc $.
$}
$( Location of the first element of a Cartesian product.  (Contributed by
       Jeff Madsen, 2-Sep-2009.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v b $.
	$v c $.
	$d A b c $.
	$d B b c $.
	$d C b c $.
	ixp1st_0 $f set b $.
	ixp1st_1 $f set c $.
	fxp1st_0 $f class A $.
	fxp1st_1 $f class B $.
	fxp1st_2 $f class C $.
	xp1st $p |- ( A e. ( B X. C ) -> ( 1st ` A ) e. B ) $= fxp1st_0 fxp1st_1 fxp1st_2 cxp wcel fxp1st_0 ixp1st_0 cv ixp1st_1 cv cop wceq ixp1st_0 cv fxp1st_1 wcel ixp1st_1 cv fxp1st_2 wcel wa wa ixp1st_1 wex ixp1st_0 wex fxp1st_0 c1st cfv fxp1st_1 wcel ixp1st_0 ixp1st_1 fxp1st_0 fxp1st_1 fxp1st_2 elxp fxp1st_0 ixp1st_0 cv ixp1st_1 cv cop wceq ixp1st_0 cv fxp1st_1 wcel ixp1st_1 cv fxp1st_2 wcel wa wa fxp1st_0 c1st cfv fxp1st_1 wcel ixp1st_0 ixp1st_1 fxp1st_0 ixp1st_0 cv ixp1st_1 cv cop wceq ixp1st_0 cv fxp1st_1 wcel fxp1st_0 c1st cfv fxp1st_1 wcel ixp1st_1 cv fxp1st_2 wcel fxp1st_0 ixp1st_0 cv ixp1st_1 cv cop wceq fxp1st_0 c1st cfv fxp1st_1 wcel ixp1st_0 cv fxp1st_1 wcel fxp1st_0 ixp1st_0 cv ixp1st_1 cv cop wceq fxp1st_0 c1st cfv ixp1st_0 cv fxp1st_1 ixp1st_0 cv ixp1st_1 cv fxp1st_0 ixp1st_0 vex ixp1st_1 vex op1std eleq1d biimpar adantrr exlimivv sylbi $.
$}
$( Location of the second element of a Cartesian product.  (Contributed by
       Jeff Madsen, 2-Sep-2009.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v b $.
	$v c $.
	$d A b c $.
	$d B b c $.
	$d C b c $.
	ixp2nd_0 $f set b $.
	ixp2nd_1 $f set c $.
	fxp2nd_0 $f class A $.
	fxp2nd_1 $f class B $.
	fxp2nd_2 $f class C $.
	xp2nd $p |- ( A e. ( B X. C ) -> ( 2nd ` A ) e. C ) $= fxp2nd_0 fxp2nd_1 fxp2nd_2 cxp wcel fxp2nd_0 ixp2nd_0 cv ixp2nd_1 cv cop wceq ixp2nd_0 cv fxp2nd_1 wcel ixp2nd_1 cv fxp2nd_2 wcel wa wa ixp2nd_1 wex ixp2nd_0 wex fxp2nd_0 c2nd cfv fxp2nd_2 wcel ixp2nd_0 ixp2nd_1 fxp2nd_0 fxp2nd_1 fxp2nd_2 elxp fxp2nd_0 ixp2nd_0 cv ixp2nd_1 cv cop wceq ixp2nd_0 cv fxp2nd_1 wcel ixp2nd_1 cv fxp2nd_2 wcel wa wa fxp2nd_0 c2nd cfv fxp2nd_2 wcel ixp2nd_0 ixp2nd_1 fxp2nd_0 ixp2nd_0 cv ixp2nd_1 cv cop wceq ixp2nd_1 cv fxp2nd_2 wcel fxp2nd_0 c2nd cfv fxp2nd_2 wcel ixp2nd_0 cv fxp2nd_1 wcel fxp2nd_0 ixp2nd_0 cv ixp2nd_1 cv cop wceq fxp2nd_0 c2nd cfv fxp2nd_2 wcel ixp2nd_1 cv fxp2nd_2 wcel fxp2nd_0 ixp2nd_0 cv ixp2nd_1 cv cop wceq fxp2nd_0 c2nd cfv ixp2nd_1 cv fxp2nd_2 ixp2nd_0 cv ixp2nd_1 cv fxp2nd_0 ixp2nd_0 vex ixp2nd_1 vex op2ndd eleq1d biimpar adantrl exlimivv sylbi $.
$}
$( Membership in a cross product.  This version requires no quantifiers or
     dummy variables.  See also ~ elxp4 .  (Contributed by NM, 9-Oct-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	felxp6_0 $f class A $.
	felxp6_1 $f class B $.
	felxp6_2 $f class C $.
	elxp6 $p |- ( A e. ( B X. C ) <-> ( A = <. ( 1st ` A ) , ( 2nd ` A ) >. /\ ( ( 1st ` A ) e. B /\ ( 2nd ` A ) e. C ) ) ) $= felxp6_0 felxp6_1 felxp6_2 cxp wcel felxp6_0 felxp6_0 csn cdm cuni felxp6_0 csn crn cuni cop wceq felxp6_0 csn cdm cuni felxp6_1 wcel felxp6_0 csn crn cuni felxp6_2 wcel wa wa felxp6_0 felxp6_0 c1st cfv felxp6_0 c2nd cfv cop wceq felxp6_0 c1st cfv felxp6_1 wcel felxp6_0 c2nd cfv felxp6_2 wcel wa wa felxp6_0 felxp6_1 felxp6_2 elxp4 felxp6_0 felxp6_0 c1st cfv felxp6_0 c2nd cfv cop wceq felxp6_0 felxp6_0 csn cdm cuni felxp6_0 csn crn cuni cop wceq felxp6_0 c1st cfv felxp6_1 wcel felxp6_0 c2nd cfv felxp6_2 wcel wa felxp6_0 csn cdm cuni felxp6_1 wcel felxp6_0 csn crn cuni felxp6_2 wcel wa felxp6_0 c1st cfv felxp6_0 c2nd cfv cop felxp6_0 csn cdm cuni felxp6_0 csn crn cuni cop felxp6_0 felxp6_0 c1st cfv felxp6_0 csn cdm cuni felxp6_0 c2nd cfv felxp6_0 csn crn cuni felxp6_0 1stval felxp6_0 2ndval opeq12i eqeq2i felxp6_0 c1st cfv felxp6_1 wcel felxp6_0 csn cdm cuni felxp6_1 wcel felxp6_0 c2nd cfv felxp6_2 wcel felxp6_0 csn crn cuni felxp6_2 wcel felxp6_0 c1st cfv felxp6_0 csn cdm cuni felxp6_1 felxp6_0 1stval eleq1i felxp6_0 c2nd cfv felxp6_0 csn crn cuni felxp6_2 felxp6_0 2ndval eleq1i anbi12i anbi12i bitr4i $.
$}
$( Membership in a cross product.  This version requires no quantifiers or
     dummy variables.  See also ~ elxp4 .  (Contributed by NM, 19-Aug-2006.) $)
${
	$v A $.
	$v B $.
	$v C $.
	felxp7_0 $f class A $.
	felxp7_1 $f class B $.
	felxp7_2 $f class C $.
	elxp7 $p |- ( A e. ( B X. C ) <-> ( A e. ( _V X. _V ) /\ ( ( 1st ` A ) e. B /\ ( 2nd ` A ) e. C ) ) ) $= felxp7_0 felxp7_1 felxp7_2 cxp wcel felxp7_0 felxp7_0 c1st cfv felxp7_0 c2nd cfv cop wceq felxp7_0 c1st cfv felxp7_1 wcel felxp7_0 c2nd cfv felxp7_2 wcel wa wa felxp7_0 cvv cvv cxp wcel felxp7_0 c1st cfv felxp7_1 wcel felxp7_0 c2nd cfv felxp7_2 wcel wa wa felxp7_0 felxp7_1 felxp7_2 elxp6 felxp7_0 cvv cvv cxp wcel felxp7_0 felxp7_0 c1st cfv felxp7_0 c2nd cfv cop wceq felxp7_0 c1st cfv felxp7_1 wcel felxp7_0 c2nd cfv felxp7_2 wcel wa felxp7_0 cvv cvv cxp wcel felxp7_0 felxp7_0 c1st cfv felxp7_0 c2nd cfv cop wceq felxp7_0 c1st cfv cvv wcel felxp7_0 c2nd cfv cvv wcel wa felxp7_0 c1st cfv cvv wcel felxp7_0 c2nd cfv cvv wcel felxp7_0 c1st fvex felxp7_0 c2nd fvex pm3.2i felxp7_0 cvv cvv elxp6 mpbiran2 anbi1i bitr4i $.
$}
$( Difference of Cartesian products, expressed in terms of a union of
       Cartesian products of differences.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 26-Jun-2014.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d A x y $.
	$d B x y $.
	$d C x y $.
	$d D x y $.
	idifxp_0 $f set x $.
	idifxp_1 $f set y $.
	fdifxp_0 $f class A $.
	fdifxp_1 $f class B $.
	fdifxp_2 $f class C $.
	fdifxp_3 $f class D $.
	difxp $p |- ( ( C X. D ) \ ( A X. B ) ) = ( ( ( C \ A ) X. D ) u. ( C X. ( D \ B ) ) ) $= idifxp_0 idifxp_1 fdifxp_2 fdifxp_3 cxp fdifxp_0 fdifxp_1 cxp cdif fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp cun fdifxp_2 fdifxp_3 cxp fdifxp_0 fdifxp_1 cxp cdif fdifxp_2 fdifxp_3 cxp wss fdifxp_2 fdifxp_3 cxp wrel fdifxp_2 fdifxp_3 cxp fdifxp_0 fdifxp_1 cxp cdif wrel fdifxp_2 fdifxp_3 cxp fdifxp_0 fdifxp_1 cxp difss fdifxp_2 fdifxp_3 relxp fdifxp_2 fdifxp_3 cxp fdifxp_0 fdifxp_1 cxp cdif fdifxp_2 fdifxp_3 cxp relss mp2 fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp cun wrel fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp wrel fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp wrel fdifxp_2 fdifxp_0 cdif fdifxp_3 relxp fdifxp_2 fdifxp_3 fdifxp_1 cdif relxp fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp relun mpbir2an idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 cxp wcel idifxp_0 cv idifxp_1 cv cop fdifxp_0 fdifxp_1 cxp wcel wn wa idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp wcel idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp wcel wo idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 cxp fdifxp_0 fdifxp_1 cxp cdif wcel idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp cun wcel idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel idifxp_1 cv fdifxp_1 wcel wa wn wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel wn wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_1 cv fdifxp_1 wcel wn wa wo idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 cxp wcel idifxp_0 cv idifxp_1 cv cop fdifxp_0 fdifxp_1 cxp wcel wn wa idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp wcel idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp wcel wo idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel idifxp_1 cv fdifxp_1 wcel wa wn wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel wn idifxp_1 cv fdifxp_1 wcel wn wo wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel wn wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_1 cv fdifxp_1 wcel wn wa wo idifxp_0 cv fdifxp_0 wcel idifxp_1 cv fdifxp_1 wcel wa wn idifxp_0 cv fdifxp_0 wcel wn idifxp_1 cv fdifxp_1 wcel wn wo idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel idifxp_1 cv fdifxp_1 wcel ianor anbi2i idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel wn idifxp_1 cv fdifxp_1 wcel wn andi bitri idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 cxp wcel idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv idifxp_1 cv cop fdifxp_0 fdifxp_1 cxp wcel wn idifxp_0 cv fdifxp_0 wcel idifxp_1 cv fdifxp_1 wcel wa wn idifxp_0 cv idifxp_1 cv fdifxp_2 fdifxp_3 opelxp idifxp_0 cv idifxp_1 cv cop fdifxp_0 fdifxp_1 cxp wcel idifxp_0 cv fdifxp_0 wcel idifxp_1 cv fdifxp_1 wcel wa idifxp_0 cv idifxp_1 cv fdifxp_0 fdifxp_1 opelxp notbii anbi12i idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp wcel idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel wn wa idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp wcel idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_1 cv fdifxp_1 wcel wn wa idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp wcel idifxp_0 cv fdifxp_2 fdifxp_0 cdif wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel wn wa idifxp_0 cv idifxp_1 cv fdifxp_2 fdifxp_0 cdif fdifxp_3 opelxp idifxp_0 cv fdifxp_2 fdifxp_0 cdif wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_2 wcel idifxp_0 cv fdifxp_0 wcel wn wa idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_0 cv fdifxp_0 wcel wn wa idifxp_0 cv fdifxp_2 fdifxp_0 cdif wcel idifxp_0 cv fdifxp_2 wcel idifxp_0 cv fdifxp_0 wcel wn wa idifxp_1 cv fdifxp_3 wcel idifxp_0 cv fdifxp_2 fdifxp_0 eldif anbi1i idifxp_0 cv fdifxp_2 wcel idifxp_0 cv fdifxp_0 wcel wn idifxp_1 cv fdifxp_3 wcel an32 bitri bitri idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 fdifxp_1 cdif wcel wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel idifxp_1 cv fdifxp_1 wcel wn wa wa idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp wcel idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel wa idifxp_1 cv fdifxp_1 wcel wn wa idifxp_1 cv fdifxp_3 fdifxp_1 cdif wcel idifxp_1 cv fdifxp_3 wcel idifxp_1 cv fdifxp_1 wcel wn wa idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 fdifxp_1 eldif anbi2i idifxp_0 cv idifxp_1 cv fdifxp_2 fdifxp_3 fdifxp_1 cdif opelxp idifxp_0 cv fdifxp_2 wcel idifxp_1 cv fdifxp_3 wcel idifxp_1 cv fdifxp_1 wcel wn anass 3bitr4i orbi12i 3bitr4i idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_3 cxp fdifxp_0 fdifxp_1 cxp eldif idifxp_0 cv idifxp_1 cv cop fdifxp_2 fdifxp_0 cdif fdifxp_3 cxp fdifxp_2 fdifxp_3 fdifxp_1 cdif cxp elun 3bitr4i eqrelriiv $.
$}
$( Difference law for cross product.  (Contributed by Scott Fenton,
     18-Feb-2013.)  (Revised by Mario Carneiro, 26-Jun-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifxp1_0 $f class A $.
	fdifxp1_1 $f class B $.
	fdifxp1_2 $f class C $.
	difxp1 $p |- ( ( A \ B ) X. C ) = ( ( A X. C ) \ ( B X. C ) ) $= fdifxp1_0 fdifxp1_2 cxp fdifxp1_1 fdifxp1_2 cxp cdif fdifxp1_0 fdifxp1_1 cdif fdifxp1_2 cxp fdifxp1_0 fdifxp1_2 fdifxp1_2 cdif cxp cun fdifxp1_0 fdifxp1_1 cdif fdifxp1_2 cxp c0 cun fdifxp1_0 fdifxp1_1 cdif fdifxp1_2 cxp fdifxp1_1 fdifxp1_2 fdifxp1_0 fdifxp1_2 difxp fdifxp1_0 fdifxp1_2 fdifxp1_2 cdif cxp c0 fdifxp1_0 fdifxp1_1 cdif fdifxp1_2 cxp fdifxp1_0 fdifxp1_2 fdifxp1_2 cdif cxp fdifxp1_0 c0 cxp c0 fdifxp1_2 fdifxp1_2 cdif c0 fdifxp1_0 fdifxp1_2 difid xpeq2i fdifxp1_0 xp0 eqtri uneq2i fdifxp1_0 fdifxp1_1 cdif fdifxp1_2 cxp un0 3eqtrri $.
$}
$( Difference law for cross product.  (Contributed by Scott Fenton,
     18-Feb-2013.)  (Revised by Mario Carneiro, 26-Jun-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifxp2_0 $f class A $.
	fdifxp2_1 $f class B $.
	fdifxp2_2 $f class C $.
	difxp2 $p |- ( A X. ( B \ C ) ) = ( ( A X. B ) \ ( A X. C ) ) $= fdifxp2_0 fdifxp2_1 cxp fdifxp2_0 fdifxp2_2 cxp cdif fdifxp2_0 fdifxp2_0 cdif fdifxp2_1 cxp fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp cun c0 fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp cun fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp fdifxp2_0 fdifxp2_2 fdifxp2_0 fdifxp2_1 difxp fdifxp2_0 fdifxp2_0 cdif fdifxp2_1 cxp c0 fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp fdifxp2_0 fdifxp2_0 cdif fdifxp2_1 cxp c0 fdifxp2_1 cxp c0 fdifxp2_0 fdifxp2_0 cdif c0 fdifxp2_1 fdifxp2_0 difid xpeq1i fdifxp2_1 xp0r eqtri uneq1i c0 fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp cun fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp c0 cun fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp c0 fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp uncom fdifxp2_0 fdifxp2_1 fdifxp2_2 cdif cxp un0 eqtri 3eqtrri $.
$}
$( Equality with an ordered pair.  (Contributed by NM, 15-Dec-2008.)
     (Revised by Mario Carneiro, 23-Feb-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	feqopi_0 $f class A $.
	feqopi_1 $f class B $.
	feqopi_2 $f class C $.
	feqopi_3 $f class V $.
	feqopi_4 $f class W $.
	eqopi $p |- ( ( A e. ( V X. W ) /\ ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) ) -> A = <. B , C >. ) $= feqopi_0 feqopi_3 feqopi_4 cxp wcel feqopi_0 cvv cvv cxp wcel feqopi_0 c1st cfv feqopi_1 wceq feqopi_0 c2nd cfv feqopi_2 wceq wa feqopi_0 feqopi_1 feqopi_2 cop wceq feqopi_3 feqopi_4 cxp cvv cvv cxp feqopi_0 feqopi_3 feqopi_4 xpss sseli feqopi_0 cvv cvv cxp wcel feqopi_0 c1st cfv feqopi_1 wceq feqopi_0 c2nd cfv feqopi_2 wceq wa feqopi_0 feqopi_0 c1st cfv feqopi_0 c2nd cfv cop feqopi_1 feqopi_2 cop feqopi_0 cvv cvv cxp wcel feqopi_0 feqopi_0 c1st cfv feqopi_0 c2nd cfv cop wceq feqopi_0 c1st cfv cvv wcel feqopi_0 c2nd cfv cvv wcel wa feqopi_0 cvv cvv elxp6 simplbi feqopi_0 c1st cfv feqopi_0 c2nd cfv feqopi_1 feqopi_2 opeq12 sylan9eq sylan $.
$}
$( Representation of cross product based on ordered pair component
       functions.  (Contributed by NM, 16-Sep-2006.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fxp2_0 $f set x $.
	fxp2_1 $f class A $.
	fxp2_2 $f class B $.
	xp2 $p |- ( A X. B ) = { x e. ( _V X. _V ) | ( ( 1st ` x ) e. A /\ ( 2nd ` x ) e. B ) } $= fxp2_1 fxp2_2 cxp fxp2_0 cv cvv cvv cxp wcel fxp2_0 cv c1st cfv fxp2_1 wcel fxp2_0 cv c2nd cfv fxp2_2 wcel wa wa fxp2_0 cab fxp2_0 cv c1st cfv fxp2_1 wcel fxp2_0 cv c2nd cfv fxp2_2 wcel wa fxp2_0 cvv cvv cxp crab fxp2_0 cv cvv cvv cxp wcel fxp2_0 cv c1st cfv fxp2_1 wcel fxp2_0 cv c2nd cfv fxp2_2 wcel wa wa fxp2_0 fxp2_1 fxp2_2 cxp fxp2_0 cv fxp2_1 fxp2_2 elxp7 abbi2i fxp2_0 cv c1st cfv fxp2_1 wcel fxp2_0 cv c2nd cfv fxp2_2 wcel wa fxp2_0 cvv cvv cxp df-rab eqtr4i $.
$}
$( The membership relation for a cross product is inherited by union.
       (Contributed by NM, 16-Sep-2006.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	iunielxp_0 $f set x $.
	funielxp_0 $f class A $.
	funielxp_1 $f class B $.
	funielxp_2 $f class C $.
	unielxp $p |- ( A e. ( B X. C ) -> U. A e. U. ( B X. C ) ) $= funielxp_0 funielxp_1 funielxp_2 cxp wcel funielxp_0 cvv cvv cxp wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa wa funielxp_0 cuni funielxp_1 funielxp_2 cxp cuni wcel funielxp_0 funielxp_1 funielxp_2 elxp7 funielxp_0 cuni funielxp_0 wcel funielxp_0 cvv cvv cxp wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa wa funielxp_0 cuni funielxp_1 funielxp_2 cxp cuni wcel funielxp_0 cvv cvv cxp wcel funielxp_0 cuni funielxp_0 wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa funielxp_0 elvvuni adantr funielxp_0 cuni funielxp_0 wcel funielxp_0 cvv cvv cxp wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa wa wa funielxp_0 cuni iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa iunielxp_0 cab cuni funielxp_1 funielxp_2 cxp cuni funielxp_0 cuni funielxp_0 wcel funielxp_0 cvv cvv cxp wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa wa wa funielxp_0 cuni iunielxp_0 cv wcel iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa wa iunielxp_0 wex funielxp_0 cuni iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa iunielxp_0 cab cuni wcel funielxp_0 cvv cvv cxp wcel funielxp_0 cuni funielxp_0 wcel funielxp_0 cvv cvv cxp wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa wa wa funielxp_0 cuni iunielxp_0 cv wcel iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa wa iunielxp_0 wex funielxp_0 cuni funielxp_0 wcel funielxp_0 cvv cvv cxp wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa simprl funielxp_0 cuni iunielxp_0 cv wcel iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa wa funielxp_0 cuni funielxp_0 wcel funielxp_0 cvv cvv cxp wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa wa wa iunielxp_0 funielxp_0 cvv cvv cxp iunielxp_0 cv funielxp_0 wceq funielxp_0 cuni iunielxp_0 cv wcel funielxp_0 cuni funielxp_0 wcel iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa funielxp_0 cvv cvv cxp wcel funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa wa iunielxp_0 cv funielxp_0 funielxp_0 cuni eleq2 iunielxp_0 cv funielxp_0 wceq iunielxp_0 cv cvv cvv cxp wcel funielxp_0 cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa funielxp_0 c1st cfv funielxp_1 wcel funielxp_0 c2nd cfv funielxp_2 wcel wa iunielxp_0 cv funielxp_0 cvv cvv cxp eleq1 iunielxp_0 cv funielxp_0 wceq iunielxp_0 cv c1st cfv funielxp_1 wcel funielxp_0 c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel funielxp_0 c2nd cfv funielxp_2 wcel iunielxp_0 cv funielxp_0 wceq iunielxp_0 cv c1st cfv funielxp_0 c1st cfv funielxp_1 iunielxp_0 cv funielxp_0 c1st fveq2 eleq1d iunielxp_0 cv funielxp_0 wceq iunielxp_0 cv c2nd cfv funielxp_0 c2nd cfv funielxp_2 iunielxp_0 cv funielxp_0 c2nd fveq2 eleq1d anbi12d anbi12d anbi12d spcegv mpcom iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa iunielxp_0 funielxp_0 cuni eluniab sylibr funielxp_1 funielxp_2 cxp iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa iunielxp_0 cab funielxp_1 funielxp_2 cxp iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa iunielxp_0 cvv cvv cxp crab iunielxp_0 cv cvv cvv cxp wcel iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa wa iunielxp_0 cab iunielxp_0 funielxp_1 funielxp_2 xp2 iunielxp_0 cv c1st cfv funielxp_1 wcel iunielxp_0 cv c2nd cfv funielxp_2 wcel wa iunielxp_0 cvv cvv cxp df-rab eqtri unieqi syl6eleqr mpancom sylbi $.
$}
$( Reconstruction of a member of a cross product in terms of its ordered pair
     components.  (Contributed by NM, 20-Oct-2013.) $)
${
	$v A $.
	$v B $.
	$v C $.
	f1st2nd2_0 $f class A $.
	f1st2nd2_1 $f class B $.
	f1st2nd2_2 $f class C $.
	1st2nd2 $p |- ( A e. ( B X. C ) -> A = <. ( 1st ` A ) , ( 2nd ` A ) >. ) $= f1st2nd2_0 f1st2nd2_1 f1st2nd2_2 cxp wcel f1st2nd2_0 f1st2nd2_0 c1st cfv f1st2nd2_0 c2nd cfv cop wceq f1st2nd2_0 c1st cfv f1st2nd2_1 wcel f1st2nd2_0 c2nd cfv f1st2nd2_2 wcel wa f1st2nd2_0 f1st2nd2_1 f1st2nd2_2 elxp6 simplbi $.
$}
$( Reconstruction of an ordered pair in terms of its components.
     (Contributed by NM, 25-Feb-2014.) $)
${
	$v A $.
	f1st2ndb_0 $f class A $.
	1st2ndb $p |- ( A e. ( _V X. _V ) <-> A = <. ( 1st ` A ) , ( 2nd ` A ) >. ) $= f1st2ndb_0 cvv cvv cxp wcel f1st2ndb_0 f1st2ndb_0 c1st cfv f1st2ndb_0 c2nd cfv cop wceq f1st2ndb_0 cvv cvv 1st2nd2 f1st2ndb_0 f1st2ndb_0 c1st cfv f1st2ndb_0 c2nd cfv cop wceq f1st2ndb_0 f1st2ndb_0 c1st cfv f1st2ndb_0 c2nd cfv cop cvv cvv cxp f1st2ndb_0 f1st2ndb_0 c1st cfv f1st2ndb_0 c2nd cfv cop wceq id f1st2ndb_0 c1st cfv f1st2ndb_0 c2nd cfv f1st2ndb_0 c1st fvex f1st2ndb_0 c2nd fvex opelvv syl6eqel impbii $.
$}
$( An ordered pair theorem for members of cross products.  (Contributed by
     NM, 20-Jun-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	fxpopth_0 $f class A $.
	fxpopth_1 $f class B $.
	fxpopth_2 $f class C $.
	fxpopth_3 $f class D $.
	fxpopth_4 $f class R $.
	fxpopth_5 $f class S $.
	xpopth $p |- ( ( A e. ( C X. D ) /\ B e. ( R X. S ) ) -> ( ( ( 1st ` A ) = ( 1st ` B ) /\ ( 2nd ` A ) = ( 2nd ` B ) ) <-> A = B ) ) $= fxpopth_0 fxpopth_2 fxpopth_3 cxp wcel fxpopth_1 fxpopth_4 fxpopth_5 cxp wcel wa fxpopth_0 fxpopth_1 wceq fxpopth_0 c1st cfv fxpopth_0 c2nd cfv cop fxpopth_1 c1st cfv fxpopth_1 c2nd cfv cop wceq fxpopth_0 c1st cfv fxpopth_1 c1st cfv wceq fxpopth_0 c2nd cfv fxpopth_1 c2nd cfv wceq wa fxpopth_0 fxpopth_2 fxpopth_3 cxp wcel fxpopth_1 fxpopth_4 fxpopth_5 cxp wcel fxpopth_0 fxpopth_0 c1st cfv fxpopth_0 c2nd cfv cop fxpopth_1 fxpopth_1 c1st cfv fxpopth_1 c2nd cfv cop fxpopth_0 fxpopth_2 fxpopth_3 1st2nd2 fxpopth_1 fxpopth_4 fxpopth_5 1st2nd2 eqeqan12d fxpopth_0 c1st cfv fxpopth_0 c2nd cfv fxpopth_1 c1st cfv fxpopth_1 c2nd cfv fxpopth_0 c1st fvex fxpopth_0 c2nd fvex opth syl6rbb $.
$}
$( Two ways to express equality with an ordered pair.  (Contributed by NM,
     3-Sep-2007.)  (Proof shortened by Mario Carneiro, 26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	feqop_0 $f class A $.
	feqop_1 $f class B $.
	feqop_2 $f class C $.
	feqop_3 $f class V $.
	feqop_4 $f class W $.
	eqop $p |- ( A e. ( V X. W ) -> ( A = <. B , C >. <-> ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) ) ) $= feqop_0 feqop_3 feqop_4 cxp wcel feqop_0 feqop_1 feqop_2 cop wceq feqop_0 c1st cfv feqop_0 c2nd cfv cop feqop_1 feqop_2 cop wceq feqop_0 c1st cfv feqop_1 wceq feqop_0 c2nd cfv feqop_2 wceq wa feqop_0 feqop_3 feqop_4 cxp wcel feqop_0 feqop_0 c1st cfv feqop_0 c2nd cfv cop feqop_1 feqop_2 cop feqop_0 feqop_3 feqop_4 1st2nd2 eqeq1d feqop_0 c1st cfv feqop_0 c2nd cfv feqop_1 feqop_2 feqop_0 c1st fvex feqop_0 c2nd fvex opth syl6bb $.
$}
$( Two ways to express equality with an ordered pair.  (Contributed by NM,
       25-Feb-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	feqop2_0 $f class A $.
	feqop2_1 $f class B $.
	feqop2_2 $f class C $.
	eeqop2_0 $e |- B e. _V $.
	eeqop2_1 $e |- C e. _V $.
	eqop2 $p |- ( A = <. B , C >. <-> ( A e. ( _V X. _V ) /\ ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) ) ) $= feqop2_0 feqop2_1 feqop2_2 cop wceq feqop2_0 cvv cvv cxp wcel feqop2_0 c1st cfv feqop2_1 wceq feqop2_0 c2nd cfv feqop2_2 wceq wa feqop2_0 feqop2_1 feqop2_2 cop wceq feqop2_0 cvv cvv cxp wcel feqop2_1 feqop2_2 cop cvv cvv cxp wcel feqop2_1 feqop2_2 eeqop2_0 eeqop2_1 opelvv feqop2_0 feqop2_1 feqop2_2 cop cvv cvv cxp eleq1 mpbiri feqop2_0 feqop2_1 feqop2_2 cvv cvv eqop biadan2 $.
$}
$( Two ways of expressing that an element is the first member of an ordered
       pair.  (Contributed by NM, 22-Sep-2013.)  (Revised by Mario Carneiro,
       23-Feb-2014.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v V $.
	$v W $.
	$d x A $.
	$d x B $.
	fop1steq_0 $f set x $.
	fop1steq_1 $f class A $.
	fop1steq_2 $f class B $.
	fop1steq_3 $f class V $.
	fop1steq_4 $f class W $.
	op1steq $p |- ( A e. ( V X. W ) -> ( ( 1st ` A ) = B <-> E. x A = <. B , x >. ) ) $= fop1steq_1 fop1steq_3 fop1steq_4 cxp wcel fop1steq_1 cvv cvv cxp wcel fop1steq_1 c1st cfv fop1steq_2 wceq fop1steq_1 fop1steq_2 fop1steq_0 cv cop wceq fop1steq_0 wex wb fop1steq_3 fop1steq_4 cxp cvv cvv cxp fop1steq_1 fop1steq_3 fop1steq_4 xpss sseli fop1steq_1 cvv cvv cxp wcel fop1steq_1 c1st cfv fop1steq_2 wceq fop1steq_1 fop1steq_2 fop1steq_0 cv cop wceq fop1steq_0 wex fop1steq_1 cvv cvv cxp wcel fop1steq_1 c1st cfv fop1steq_2 wceq fop1steq_1 fop1steq_2 fop1steq_0 cv cop wceq fop1steq_0 wex fop1steq_1 cvv cvv cxp wcel fop1steq_1 c1st cfv fop1steq_2 wceq wa fop1steq_1 fop1steq_2 fop1steq_1 c2nd cfv cop wceq fop1steq_1 fop1steq_2 fop1steq_0 cv cop wceq fop1steq_0 wex fop1steq_1 cvv cvv cxp wcel fop1steq_1 c1st cfv fop1steq_2 wceq fop1steq_1 c2nd cfv fop1steq_1 c2nd cfv wceq fop1steq_1 fop1steq_2 fop1steq_1 c2nd cfv cop wceq fop1steq_1 c2nd cfv eqid fop1steq_1 fop1steq_2 fop1steq_1 c2nd cfv cvv cvv eqopi mpanr2 fop1steq_1 fop1steq_2 fop1steq_0 cv cop wceq fop1steq_1 fop1steq_2 fop1steq_1 c2nd cfv cop wceq fop1steq_0 fop1steq_1 c2nd cfv fop1steq_1 c2nd fvex fop1steq_0 cv fop1steq_1 c2nd cfv wceq fop1steq_2 fop1steq_0 cv cop fop1steq_2 fop1steq_1 c2nd cfv cop fop1steq_1 fop1steq_0 cv fop1steq_1 c2nd cfv fop1steq_2 opeq2 eqeq2d spcev syl ex fop1steq_1 cvv cvv cxp wcel fop1steq_1 fop1steq_2 fop1steq_0 cv cop wceq fop1steq_1 c1st cfv fop1steq_2 wceq fop1steq_0 fop1steq_1 cvv cvv cxp wcel fop1steq_1 fop1steq_2 fop1steq_0 cv cop wceq fop1steq_1 c1st cfv fop1steq_2 wceq fop1steq_1 c2nd cfv fop1steq_0 cv wceq wa fop1steq_1 c1st cfv fop1steq_2 wceq fop1steq_1 fop1steq_2 fop1steq_0 cv cvv cvv eqop fop1steq_1 c1st cfv fop1steq_2 wceq fop1steq_1 c2nd cfv fop1steq_0 cv wceq simpl syl6bi exlimdv impbid syl $.
$}
$( Swap the members of an ordered pair.  (Contributed by NM, 31-Dec-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	f2nd1st_0 $f class A $.
	f2nd1st_1 $f class B $.
	f2nd1st_2 $f class C $.
	2nd1st $p |- ( A e. ( B X. C ) -> U. `' { A } = <. ( 2nd ` A ) , ( 1st ` A ) >. ) $= f2nd1st_0 f2nd1st_1 f2nd1st_2 cxp wcel f2nd1st_0 csn ccnv cuni f2nd1st_0 c1st cfv f2nd1st_0 c2nd cfv cop csn ccnv cuni f2nd1st_0 c2nd cfv f2nd1st_0 c1st cfv cop f2nd1st_0 f2nd1st_1 f2nd1st_2 cxp wcel f2nd1st_0 csn ccnv f2nd1st_0 c1st cfv f2nd1st_0 c2nd cfv cop csn ccnv f2nd1st_0 f2nd1st_1 f2nd1st_2 cxp wcel f2nd1st_0 csn f2nd1st_0 c1st cfv f2nd1st_0 c2nd cfv cop csn f2nd1st_0 f2nd1st_1 f2nd1st_2 cxp wcel f2nd1st_0 f2nd1st_0 c1st cfv f2nd1st_0 c2nd cfv cop f2nd1st_0 f2nd1st_1 f2nd1st_2 1st2nd2 sneqd cnveqd unieqd f2nd1st_0 c1st cfv f2nd1st_0 c2nd cfv opswap syl6eq $.
$}
$( Reconstruction of a member of a relation in terms of its ordered pair
     components.  (Contributed by NM, 29-Aug-2006.) $)
${
	$v A $.
	$v B $.
	f1st2nd_0 $f class A $.
	f1st2nd_1 $f class B $.
	1st2nd $p |- ( ( Rel B /\ A e. B ) -> A = <. ( 1st ` A ) , ( 2nd ` A ) >. ) $= f1st2nd_1 wrel f1st2nd_0 f1st2nd_1 wcel wa f1st2nd_0 cvv cvv cxp wcel f1st2nd_0 f1st2nd_0 c1st cfv f1st2nd_0 c2nd cfv cop wceq f1st2nd_1 wrel f1st2nd_1 cvv cvv cxp wss f1st2nd_0 f1st2nd_1 wcel f1st2nd_0 cvv cvv cxp wcel f1st2nd_1 df-rel f1st2nd_1 cvv cvv cxp f1st2nd_0 ssel2 sylanb f1st2nd_0 cvv cvv 1st2nd2 syl $.
$}
$( The first ordered pair component of a member of a relation belongs to the
     domain of the relation.  (Contributed by NM, 17-Sep-2006.) $)
${
	$v A $.
	$v R $.
	f1stdm_0 $f class A $.
	f1stdm_1 $f class R $.
	1stdm $p |- ( ( Rel R /\ A e. R ) -> ( 1st ` A ) e. dom R ) $= f1stdm_1 wrel f1stdm_0 f1stdm_1 wcel wa f1stdm_0 c1st cfv f1stdm_0 cint cint f1stdm_1 cdm f1stdm_1 wrel f1stdm_0 f1stdm_1 wcel wa f1stdm_0 cvv cvv cxp wcel f1stdm_0 c1st cfv f1stdm_0 cint cint wceq f1stdm_1 wrel f1stdm_1 cvv cvv cxp f1stdm_0 f1stdm_1 wrel f1stdm_1 cvv cvv cxp wss f1stdm_1 df-rel biimpi sselda f1stdm_0 1stval2 syl f1stdm_1 f1stdm_0 elreldm eqeltrd $.
$}
$( The second ordered pair component of a member of a relation belongs to the
     range of the relation.  (Contributed by NM, 17-Sep-2006.) $)
${
	$v A $.
	$v R $.
	f2ndrn_0 $f class A $.
	f2ndrn_1 $f class R $.
	2ndrn $p |- ( ( Rel R /\ A e. R ) -> ( 2nd ` A ) e. ran R ) $= f2ndrn_1 wrel f2ndrn_0 f2ndrn_1 wcel wa f2ndrn_0 c1st cfv f2ndrn_0 c2nd cfv cop f2ndrn_1 wcel f2ndrn_0 c2nd cfv f2ndrn_1 crn wcel f2ndrn_1 wrel f2ndrn_0 f2ndrn_1 wcel wa f2ndrn_0 f2ndrn_0 c1st cfv f2ndrn_0 c2nd cfv cop f2ndrn_1 f2ndrn_0 f2ndrn_1 1st2nd f2ndrn_1 wrel f2ndrn_0 f2ndrn_1 wcel simpr eqeltrrd f2ndrn_0 c1st cfv f2ndrn_0 c2nd cfv f2ndrn_1 f2ndrn_0 c1st fvex f2ndrn_0 c2nd fvex opelrn syl $.
$}
$( Express an element of a relation as a relationship between first and
     second components.  (Contributed by Mario Carneiro, 22-Jun-2016.) $)
${
	$v A $.
	$v B $.
	f1st2ndbr_0 $f class A $.
	f1st2ndbr_1 $f class B $.
	1st2ndbr $p |- ( ( Rel B /\ A e. B ) -> ( 1st ` A ) B ( 2nd ` A ) ) $= f1st2ndbr_1 wrel f1st2ndbr_0 f1st2ndbr_1 wcel wa f1st2ndbr_0 c1st cfv f1st2ndbr_0 c2nd cfv cop f1st2ndbr_1 wcel f1st2ndbr_0 c1st cfv f1st2ndbr_0 c2nd cfv f1st2ndbr_1 wbr f1st2ndbr_1 wrel f1st2ndbr_0 f1st2ndbr_1 wcel wa f1st2ndbr_0 f1st2ndbr_0 c1st cfv f1st2ndbr_0 c2nd cfv cop f1st2ndbr_1 f1st2ndbr_0 f1st2ndbr_1 1st2nd f1st2ndbr_1 wrel f1st2ndbr_0 f1st2ndbr_1 wcel simpr eqeltrrd f1st2ndbr_0 c1st cfv f1st2ndbr_0 c2nd cfv f1st2ndbr_1 df-br sylibr $.
$}
$( Two ways of expressing membership in the domain of a relation.
       (Contributed by NM, 22-Sep-2013.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x y B $.
	ireleldm2_0 $f set y $.
	freleldm2_0 $f set x $.
	freleldm2_1 $f class A $.
	freleldm2_2 $f class B $.
	releldm2 $p |- ( Rel A -> ( B e. dom A <-> E. x e. A ( 1st ` x ) = B ) ) $= freleldm2_1 wrel freleldm2_2 freleldm2_1 cdm wcel freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_0 freleldm2_1 wrex freleldm2_1 wrel freleldm2_2 cvv wcel wa freleldm2_2 freleldm2_1 cdm wcel freleldm2_2 cvv wcel freleldm2_1 wrel freleldm2_2 freleldm2_1 cdm elex anim2i freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_0 freleldm2_1 wrex freleldm2_2 cvv wcel freleldm2_1 wrel freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_2 cvv wcel freleldm2_0 freleldm2_1 freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_2 freleldm2_0 cv c1st cfv cvv freleldm2_0 cv c1st cfv freleldm2_2 wceq id freleldm2_0 cv c1st fvex syl6eqelr rexlimivw anim2i freleldm2_1 wrel freleldm2_2 cvv wcel wa freleldm2_2 freleldm2_1 cdm wcel freleldm2_2 ireleldm2_0 cv cop freleldm2_1 wcel ireleldm2_0 wex freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_0 freleldm2_1 wrex freleldm2_2 cvv wcel freleldm2_2 freleldm2_1 cdm wcel freleldm2_2 ireleldm2_0 cv cop freleldm2_1 wcel ireleldm2_0 wex wb freleldm2_1 wrel ireleldm2_0 freleldm2_2 freleldm2_1 cvv eldm2g adantl freleldm2_1 wrel freleldm2_2 cvv wcel wa freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_0 freleldm2_1 wrex freleldm2_0 cv freleldm2_2 ireleldm2_0 cv cop wceq ireleldm2_0 wex freleldm2_0 freleldm2_1 wrex freleldm2_2 ireleldm2_0 cv cop freleldm2_1 wcel ireleldm2_0 wex freleldm2_1 wrel freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_0 freleldm2_1 wrex freleldm2_0 cv freleldm2_2 ireleldm2_0 cv cop wceq ireleldm2_0 wex freleldm2_0 freleldm2_1 wrex wb freleldm2_2 cvv wcel freleldm2_1 wrel freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_0 cv freleldm2_2 ireleldm2_0 cv cop wceq ireleldm2_0 wex freleldm2_0 freleldm2_1 freleldm2_1 wrel freleldm2_0 cv freleldm2_1 wcel wa freleldm2_0 cv cvv cvv cxp wcel freleldm2_0 cv c1st cfv freleldm2_2 wceq freleldm2_0 cv freleldm2_2 ireleldm2_0 cv cop wceq ireleldm2_0 wex wb freleldm2_1 wrel freleldm2_0 cv freleldm2_1 wcel freleldm2_0 cv cvv cvv cxp wcel freleldm2_1 wrel freleldm2_1 cvv cvv cxp wss freleldm2_0 cv freleldm2_1 wcel freleldm2_0 cv cvv cvv cxp wcel wi freleldm2_1 df-rel freleldm2_1 cvv cvv cxp freleldm2_0 cv ssel sylbi imp ireleldm2_0 freleldm2_0 cv freleldm2_2 cvv cvv op1steq syl rexbidva adantr freleldm2_0 cv freleldm2_2 ireleldm2_0 cv cop wceq ireleldm2_0 wex freleldm2_0 freleldm2_1 wrex freleldm2_0 cv freleldm2_2 ireleldm2_0 cv cop wceq freleldm2_0 freleldm2_1 wrex ireleldm2_0 wex freleldm2_2 ireleldm2_0 cv cop freleldm2_1 wcel ireleldm2_0 wex freleldm2_0 cv freleldm2_2 ireleldm2_0 cv cop wceq freleldm2_0 ireleldm2_0 freleldm2_1 rexcom4 freleldm2_2 ireleldm2_0 cv cop freleldm2_1 wcel freleldm2_0 cv freleldm2_2 ireleldm2_0 cv cop wceq freleldm2_0 freleldm2_1 wrex ireleldm2_0 freleldm2_0 freleldm2_2 ireleldm2_0 cv cop freleldm2_1 risset exbii bitr4i syl6bb bitr4d pm5.21nd $.
$}
$( An expression for the domain of a relation.  (Contributed by NM,
       22-Sep-2013.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$d x y z A $.
	ireldm_0 $f set y $.
	ireldm_1 $f set z $.
	freldm_0 $f set x $.
	freldm_1 $f class A $.
	reldm $p |- ( Rel A -> dom A = ran ( x e. A |-> ( 1st ` x ) ) ) $= freldm_1 wrel ireldm_0 freldm_1 cdm freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt crn freldm_1 wrel ireldm_0 cv freldm_1 cdm wcel ireldm_1 cv c1st cfv ireldm_0 cv wceq ireldm_1 freldm_1 wrex ireldm_0 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt crn wcel ireldm_1 freldm_1 ireldm_0 cv releldm2 ireldm_0 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt crn wcel ireldm_1 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt cfv ireldm_0 cv wceq ireldm_1 freldm_1 wrex freldm_1 wrel ireldm_1 cv c1st cfv ireldm_0 cv wceq ireldm_1 freldm_1 wrex freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt freldm_1 wfn ireldm_0 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt crn wcel ireldm_1 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt cfv ireldm_0 cv wceq ireldm_1 freldm_1 wrex wb freldm_0 freldm_1 freldm_0 cv c1st cfv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt freldm_0 cv c1st fvex freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt eqid fnmpti ireldm_1 freldm_1 ireldm_0 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt fvelrnb ax-mp ireldm_1 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt cfv ireldm_0 cv wceq ireldm_1 freldm_1 wrex ireldm_1 cv c1st cfv ireldm_0 cv wceq ireldm_1 freldm_1 wrex wb freldm_1 wrel ireldm_1 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt cfv ireldm_0 cv wceq ireldm_1 cv c1st cfv ireldm_0 cv wceq ireldm_1 freldm_1 ireldm_1 cv freldm_1 wcel ireldm_1 cv freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt cfv ireldm_1 cv c1st cfv ireldm_0 cv freldm_0 ireldm_1 cv freldm_0 cv c1st cfv ireldm_1 cv c1st cfv freldm_1 freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt freldm_0 cv ireldm_1 cv c1st fveq2 freldm_0 freldm_1 freldm_0 cv c1st cfv cmpt eqid ireldm_1 cv c1st fvex fvmpt eqeq1d rexbiia a1i syl5rbb bitrd eqrdv $.
$}
$( Equality theorem for substitution of a class for an ordered pair (analog
     of ~ sbceq1a that avoids the existential quantifiers of ~ copsexg ).
     (Contributed by NM, 19-Aug-2006.)  (Revised by Mario Carneiro,
     31-Aug-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	fsbcopeq1a_0 $f wff ph $.
	fsbcopeq1a_1 $f set x $.
	fsbcopeq1a_2 $f set y $.
	fsbcopeq1a_3 $f class A $.
	sbcopeq1a $p |- ( A = <. x , y >. -> ( [. ( 1st ` A ) / x ]. [. ( 2nd ` A ) / y ]. ph <-> ph ) ) $= fsbcopeq1a_3 fsbcopeq1a_1 cv fsbcopeq1a_2 cv cop wceq fsbcopeq1a_0 fsbcopeq1a_0 fsbcopeq1a_2 fsbcopeq1a_3 c2nd cfv wsbc fsbcopeq1a_0 fsbcopeq1a_2 fsbcopeq1a_3 c2nd cfv wsbc fsbcopeq1a_1 fsbcopeq1a_3 c1st cfv wsbc fsbcopeq1a_3 fsbcopeq1a_1 cv fsbcopeq1a_2 cv cop wceq fsbcopeq1a_2 cv fsbcopeq1a_3 c2nd cfv wceq fsbcopeq1a_0 fsbcopeq1a_0 fsbcopeq1a_2 fsbcopeq1a_3 c2nd cfv wsbc wb fsbcopeq1a_3 fsbcopeq1a_1 cv fsbcopeq1a_2 cv cop wceq fsbcopeq1a_3 c2nd cfv fsbcopeq1a_2 cv fsbcopeq1a_1 cv fsbcopeq1a_2 cv fsbcopeq1a_3 fsbcopeq1a_1 vex fsbcopeq1a_2 vex op2ndd eqcomd fsbcopeq1a_0 fsbcopeq1a_2 fsbcopeq1a_3 c2nd cfv sbceq1a syl fsbcopeq1a_3 fsbcopeq1a_1 cv fsbcopeq1a_2 cv cop wceq fsbcopeq1a_1 cv fsbcopeq1a_3 c1st cfv wceq fsbcopeq1a_0 fsbcopeq1a_2 fsbcopeq1a_3 c2nd cfv wsbc fsbcopeq1a_0 fsbcopeq1a_2 fsbcopeq1a_3 c2nd cfv wsbc fsbcopeq1a_1 fsbcopeq1a_3 c1st cfv wsbc wb fsbcopeq1a_3 fsbcopeq1a_1 cv fsbcopeq1a_2 cv cop wceq fsbcopeq1a_3 c1st cfv fsbcopeq1a_1 cv fsbcopeq1a_1 cv fsbcopeq1a_2 cv fsbcopeq1a_3 fsbcopeq1a_1 vex fsbcopeq1a_2 vex op1std eqcomd fsbcopeq1a_0 fsbcopeq1a_2 fsbcopeq1a_3 c2nd cfv wsbc fsbcopeq1a_1 fsbcopeq1a_3 c1st cfv sbceq1a syl bitr2d $.
$}
$( Equality theorem for substitution of a class ` A ` for an ordered pair
     ` <. x , y >. ` in ` B ` (analog of ~ csbeq1a ).  (Contributed by NM,
     19-Aug-2006.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	fcsbopeq1a_0 $f set x $.
	fcsbopeq1a_1 $f set y $.
	fcsbopeq1a_2 $f class A $.
	fcsbopeq1a_3 $f class B $.
	csbopeq1a $p |- ( A = <. x , y >. -> [_ ( 1st ` A ) / x ]_ [_ ( 2nd ` A ) / y ]_ B = B ) $= fcsbopeq1a_2 fcsbopeq1a_0 cv fcsbopeq1a_1 cv cop wceq fcsbopeq1a_3 fcsbopeq1a_1 fcsbopeq1a_2 c2nd cfv fcsbopeq1a_3 csb fcsbopeq1a_0 fcsbopeq1a_2 c1st cfv fcsbopeq1a_1 fcsbopeq1a_2 c2nd cfv fcsbopeq1a_3 csb csb fcsbopeq1a_2 fcsbopeq1a_0 cv fcsbopeq1a_1 cv cop wceq fcsbopeq1a_1 cv fcsbopeq1a_2 c2nd cfv wceq fcsbopeq1a_3 fcsbopeq1a_1 fcsbopeq1a_2 c2nd cfv fcsbopeq1a_3 csb wceq fcsbopeq1a_2 fcsbopeq1a_0 cv fcsbopeq1a_1 cv cop wceq fcsbopeq1a_2 c2nd cfv fcsbopeq1a_1 cv fcsbopeq1a_0 cv fcsbopeq1a_1 cv fcsbopeq1a_2 fcsbopeq1a_0 vex fcsbopeq1a_1 vex op2ndd eqcomd fcsbopeq1a_1 fcsbopeq1a_2 c2nd cfv fcsbopeq1a_3 csbeq1a syl fcsbopeq1a_2 fcsbopeq1a_0 cv fcsbopeq1a_1 cv cop wceq fcsbopeq1a_0 cv fcsbopeq1a_2 c1st cfv wceq fcsbopeq1a_1 fcsbopeq1a_2 c2nd cfv fcsbopeq1a_3 csb fcsbopeq1a_0 fcsbopeq1a_2 c1st cfv fcsbopeq1a_1 fcsbopeq1a_2 c2nd cfv fcsbopeq1a_3 csb csb wceq fcsbopeq1a_2 fcsbopeq1a_0 cv fcsbopeq1a_1 cv cop wceq fcsbopeq1a_2 c1st cfv fcsbopeq1a_0 cv fcsbopeq1a_0 cv fcsbopeq1a_1 cv fcsbopeq1a_2 fcsbopeq1a_0 vex fcsbopeq1a_1 vex op1std eqcomd fcsbopeq1a_0 fcsbopeq1a_2 c1st cfv fcsbopeq1a_1 fcsbopeq1a_2 c2nd cfv fcsbopeq1a_3 csb csbeq1a syl eqtr2d $.
$}
$( A way to define an ordered-pair class abstraction without using
       existential quantifiers.  (Contributed by NM, 18-Aug-2006.)  (Revised by
       Mario Carneiro, 31-Aug-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d z ph $.
	$d x y z $.
	fdfopab2_0 $f wff ph $.
	fdfopab2_1 $f set x $.
	fdfopab2_2 $f set y $.
	fdfopab2_3 $f set z $.
	dfopab2 $p |- { <. x , y >. | ph } = { z e. ( _V X. _V ) | [. ( 1st ` z ) / x ]. [. ( 2nd ` z ) / y ]. ph } $= fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 wa fdfopab2_2 wex fdfopab2_1 wex fdfopab2_3 cab fdfopab2_3 cv cvv cvv cxp wcel fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_3 cab fdfopab2_0 fdfopab2_1 fdfopab2_2 copab fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc fdfopab2_3 cvv cvv cxp crab fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 wa fdfopab2_2 wex fdfopab2_1 wex fdfopab2_3 cv cvv cvv cxp wcel fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_3 fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_2 wex fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_1 wex fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_2 wex fdfopab2_1 wex fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 wa fdfopab2_2 wex fdfopab2_1 wex fdfopab2_3 cv cvv cvv cxp wcel fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_2 wex fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc fdfopab2_1 fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv nfsbc1v 19.41 fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 wa fdfopab2_2 wex fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_2 wex fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_1 fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 wa fdfopab2_2 wex fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_2 wex fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_2 wex fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc wa fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 wa fdfopab2_2 fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc fdfopab2_0 fdfopab2_0 fdfopab2_1 fdfopab2_2 fdfopab2_3 cv sbcopeq1a pm5.32i exbii fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc fdfopab2_2 fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_2 fdfopab2_1 fdfopab2_3 cv c1st cfv fdfopab2_2 fdfopab2_3 cv c1st cfv nfcv fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv nfsbc1v nfsbc 19.41 bitr3i exbii fdfopab2_3 cv cvv cvv cxp wcel fdfopab2_3 cv fdfopab2_1 cv fdfopab2_2 cv cop wceq fdfopab2_2 wex fdfopab2_1 wex fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc fdfopab2_1 fdfopab2_2 fdfopab2_3 cv elvv anbi1i 3bitr4i abbii fdfopab2_0 fdfopab2_1 fdfopab2_2 fdfopab2_3 df-opab fdfopab2_0 fdfopab2_2 fdfopab2_3 cv c2nd cfv wsbc fdfopab2_1 fdfopab2_3 cv c1st cfv wsbc fdfopab2_3 cvv cvv cxp df-rab 3eqtr4i $.
$}
$( A way to define an operation class abstraction without using existential
       quantifiers.  (Contributed by NM, 18-Aug-2006.)  (Revised by Mario
       Carneiro, 31-Aug-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w ph $.
	$d x y z w $.
	fdfoprab3s_0 $f wff ph $.
	fdfoprab3s_1 $f set x $.
	fdfoprab3s_2 $f set y $.
	fdfoprab3s_3 $f set z $.
	fdfoprab3s_4 $f set w $.
	dfoprab3s $p |- { <. <. x , y >. , z >. | ph } = { <. w , z >. | ( w e. ( _V X. _V ) /\ [. ( 1st ` w ) / x ]. [. ( 2nd ` w ) / y ]. ph ) } $= fdfoprab3s_0 fdfoprab3s_1 fdfoprab3s_2 fdfoprab3s_3 coprab fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 wa fdfoprab3s_2 wex fdfoprab3s_1 wex fdfoprab3s_4 fdfoprab3s_3 copab fdfoprab3s_4 cv cvv cvv cxp wcel fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_4 fdfoprab3s_3 copab fdfoprab3s_0 fdfoprab3s_1 fdfoprab3s_2 fdfoprab3s_3 fdfoprab3s_4 dfoprab2 fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 wa fdfoprab3s_2 wex fdfoprab3s_1 wex fdfoprab3s_4 cv cvv cvv cxp wcel fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_4 fdfoprab3s_3 fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_2 wex fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_1 wex fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_2 wex fdfoprab3s_1 wex fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 wa fdfoprab3s_2 wex fdfoprab3s_1 wex fdfoprab3s_4 cv cvv cvv cxp wcel fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_2 wex fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc fdfoprab3s_1 fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv nfsbc1v 19.41 fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 wa fdfoprab3s_2 wex fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_2 wex fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_1 fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 wa fdfoprab3s_2 wex fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_2 wex fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_2 wex fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc wa fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 wa fdfoprab3s_2 fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc fdfoprab3s_0 fdfoprab3s_0 fdfoprab3s_1 fdfoprab3s_2 fdfoprab3s_4 cv sbcopeq1a pm5.32i exbii fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc fdfoprab3s_2 fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_2 fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv fdfoprab3s_2 fdfoprab3s_4 cv c1st cfv nfcv fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv nfsbc1v nfsbc 19.41 bitr3i exbii fdfoprab3s_4 cv cvv cvv cxp wcel fdfoprab3s_4 cv fdfoprab3s_1 cv fdfoprab3s_2 cv cop wceq fdfoprab3s_2 wex fdfoprab3s_1 wex fdfoprab3s_0 fdfoprab3s_2 fdfoprab3s_4 cv c2nd cfv wsbc fdfoprab3s_1 fdfoprab3s_4 cv c1st cfv wsbc fdfoprab3s_1 fdfoprab3s_2 fdfoprab3s_4 cv elvv anbi1i 3bitr4i opabbii eqtri $.
$}
$( Operation class abstraction expressed without existential quantifiers.
       (Contributed by NM, 16-Dec-2008.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y ph $.
	$d w ps $.
	$d x y z w $.
	fdfoprab3_0 $f wff ph $.
	fdfoprab3_1 $f wff ps $.
	fdfoprab3_2 $f set x $.
	fdfoprab3_3 $f set y $.
	fdfoprab3_4 $f set z $.
	fdfoprab3_5 $f set w $.
	edfoprab3_0 $e |- ( w = <. x , y >. -> ( ph <-> ps ) ) $.
	dfoprab3 $p |- { <. w , z >. | ( w e. ( _V X. _V ) /\ ph ) } = { <. <. x , y >. , z >. | ps } $= fdfoprab3_1 fdfoprab3_2 fdfoprab3_3 fdfoprab3_4 coprab fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_1 fdfoprab3_3 fdfoprab3_5 cv c2nd cfv wsbc fdfoprab3_2 fdfoprab3_5 cv c1st cfv wsbc wa fdfoprab3_5 fdfoprab3_4 copab fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_0 wa fdfoprab3_5 fdfoprab3_4 copab fdfoprab3_1 fdfoprab3_2 fdfoprab3_3 fdfoprab3_4 fdfoprab3_5 dfoprab3s fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_1 fdfoprab3_3 fdfoprab3_5 cv c2nd cfv wsbc fdfoprab3_2 fdfoprab3_5 cv c1st cfv wsbc wa fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_0 wa fdfoprab3_5 fdfoprab3_4 fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_1 fdfoprab3_3 fdfoprab3_5 cv c2nd cfv wsbc fdfoprab3_2 fdfoprab3_5 cv c1st cfv wsbc fdfoprab3_0 fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_1 fdfoprab3_0 fdfoprab3_2 fdfoprab3_3 fdfoprab3_5 cv c1st cfv fdfoprab3_5 cv c2nd cfv fdfoprab3_5 cv c1st fvex fdfoprab3_5 cv c2nd fvex fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_2 cv fdfoprab3_5 cv c1st cfv wceq fdfoprab3_3 cv fdfoprab3_5 cv c2nd cfv wceq wa fdfoprab3_1 fdfoprab3_0 wb fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_2 cv fdfoprab3_5 cv c1st cfv wceq fdfoprab3_3 cv fdfoprab3_5 cv c2nd cfv wceq wa wa fdfoprab3_0 fdfoprab3_1 fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_2 cv fdfoprab3_5 cv c1st cfv wceq fdfoprab3_3 cv fdfoprab3_5 cv c2nd cfv wceq wa wa fdfoprab3_5 cv fdfoprab3_2 cv fdfoprab3_3 cv cop wceq fdfoprab3_0 fdfoprab3_1 wb fdfoprab3_2 cv fdfoprab3_5 cv c1st cfv wceq fdfoprab3_3 cv fdfoprab3_5 cv c2nd cfv wceq wa fdfoprab3_5 cv cvv cvv cxp wcel fdfoprab3_5 cv c1st cfv fdfoprab3_2 cv wceq fdfoprab3_5 cv c2nd cfv fdfoprab3_3 cv wceq wa fdfoprab3_5 cv fdfoprab3_2 cv fdfoprab3_3 cv cop wceq fdfoprab3_2 cv fdfoprab3_5 cv c1st cfv wceq fdfoprab3_5 cv c1st cfv fdfoprab3_2 cv wceq fdfoprab3_3 cv fdfoprab3_5 cv c2nd cfv wceq fdfoprab3_5 cv c2nd cfv fdfoprab3_3 cv wceq fdfoprab3_2 cv fdfoprab3_5 cv c1st cfv eqcom fdfoprab3_3 cv fdfoprab3_5 cv c2nd cfv eqcom anbi12i fdfoprab3_5 cv fdfoprab3_2 cv fdfoprab3_3 cv cvv cvv eqopi sylan2b edfoprab3_0 syl bicomd ex sbc2iedv pm5.32i opabbii eqtr2i $.
$}
$( Operation class abstraction expressed without existential quantifiers.
       (Contributed by NM, 3-Sep-2007.)  (Revised by Mario Carneiro,
       31-Aug-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v A $.
	$v B $.
	$d w x y A $.
	$d w x y B $.
	$d x y ph $.
	$d w ps $.
	$d w x y z $.
	fdfoprab4_0 $f wff ph $.
	fdfoprab4_1 $f wff ps $.
	fdfoprab4_2 $f set x $.
	fdfoprab4_3 $f set y $.
	fdfoprab4_4 $f set z $.
	fdfoprab4_5 $f set w $.
	fdfoprab4_6 $f class A $.
	fdfoprab4_7 $f class B $.
	edfoprab4_0 $e |- ( w = <. x , y >. -> ( ph <-> ps ) ) $.
	dfoprab4 $p |- { <. w , z >. | ( w e. ( A X. B ) /\ ph ) } = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) } $= fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_0 wa fdfoprab4_5 fdfoprab4_4 copab fdfoprab4_5 cv cvv cvv cxp wcel fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_0 wa wa fdfoprab4_5 fdfoprab4_4 copab fdfoprab4_2 cv fdfoprab4_6 wcel fdfoprab4_3 cv fdfoprab4_7 wcel wa fdfoprab4_1 wa fdfoprab4_2 fdfoprab4_3 fdfoprab4_4 coprab fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_0 wa fdfoprab4_5 cv cvv cvv cxp wcel fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_0 wa wa fdfoprab4_5 fdfoprab4_4 fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_0 wa fdfoprab4_5 cv cvv cvv cxp wcel fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_5 cv cvv cvv cxp wcel fdfoprab4_0 fdfoprab4_6 fdfoprab4_7 cxp cvv cvv cxp fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 xpss sseli adantr pm4.71ri opabbii fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_0 wa fdfoprab4_2 cv fdfoprab4_6 wcel fdfoprab4_3 cv fdfoprab4_7 wcel wa fdfoprab4_1 wa fdfoprab4_2 fdfoprab4_3 fdfoprab4_4 fdfoprab4_5 fdfoprab4_5 cv fdfoprab4_2 cv fdfoprab4_3 cv cop wceq fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_2 cv fdfoprab4_6 wcel fdfoprab4_3 cv fdfoprab4_7 wcel wa fdfoprab4_0 fdfoprab4_1 fdfoprab4_5 cv fdfoprab4_2 cv fdfoprab4_3 cv cop wceq fdfoprab4_5 cv fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_2 cv fdfoprab4_3 cv cop fdfoprab4_6 fdfoprab4_7 cxp wcel fdfoprab4_2 cv fdfoprab4_6 wcel fdfoprab4_3 cv fdfoprab4_7 wcel wa fdfoprab4_5 cv fdfoprab4_2 cv fdfoprab4_3 cv cop fdfoprab4_6 fdfoprab4_7 cxp eleq1 fdfoprab4_2 cv fdfoprab4_3 cv fdfoprab4_6 fdfoprab4_7 opelxp syl6bb edfoprab4_0 anbi12d dfoprab3 eqtri $.
$}
$( Operation class abstraction expressed without existential quantifiers.
       (Unnecessary distinct variable restrictions were removed by David
       Abernethy, 19-Jun-2012.)  (Contributed by NM, 20-Dec-2008.)  (Revised by
       Mario Carneiro, 31-Aug-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v u $.
	$v t $.
	$v A $.
	$v B $.
	$d t u w x y z $.
	$d t u w x y A $.
	$d t u w x y B $.
	$d t u w ps $.
	$d t u ph $.
	idfoprab4f_0 $f set u $.
	idfoprab4f_1 $f set t $.
	fdfoprab4f_0 $f wff ph $.
	fdfoprab4f_1 $f wff ps $.
	fdfoprab4f_2 $f set x $.
	fdfoprab4f_3 $f set y $.
	fdfoprab4f_4 $f set z $.
	fdfoprab4f_5 $f set w $.
	fdfoprab4f_6 $f class A $.
	fdfoprab4f_7 $f class B $.
	edfoprab4f_0 $e |- F/ x ph $.
	edfoprab4f_1 $e |- F/ y ph $.
	edfoprab4f_2 $e |- ( w = <. x , y >. -> ( ph <-> ps ) ) $.
	dfoprab4f $p |- { <. w , z >. | ( w e. ( A X. B ) /\ ph ) } = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) } $= fdfoprab4f_5 cv fdfoprab4f_6 fdfoprab4f_7 cxp wcel fdfoprab4f_0 wa fdfoprab4f_5 fdfoprab4f_4 copab idfoprab4f_1 cv fdfoprab4f_6 wcel idfoprab4f_0 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb wa idfoprab4f_1 idfoprab4f_0 fdfoprab4f_4 coprab fdfoprab4f_2 cv fdfoprab4f_6 wcel fdfoprab4f_3 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 wa fdfoprab4f_2 fdfoprab4f_3 fdfoprab4f_4 coprab fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb idfoprab4f_1 idfoprab4f_0 fdfoprab4f_4 fdfoprab4f_5 fdfoprab4f_6 fdfoprab4f_7 fdfoprab4f_5 cv fdfoprab4f_2 cv idfoprab4f_0 cv cop wceq fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb wb wi fdfoprab4f_5 cv idfoprab4f_1 cv idfoprab4f_0 cv cop wceq fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb wb wi fdfoprab4f_2 idfoprab4f_1 fdfoprab4f_5 cv idfoprab4f_1 cv idfoprab4f_0 cv cop wceq fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb wb fdfoprab4f_2 fdfoprab4f_5 cv idfoprab4f_1 cv idfoprab4f_0 cv cop wceq fdfoprab4f_2 nfv fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb fdfoprab4f_2 edfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 nfs1v nfbi nfim fdfoprab4f_2 cv idfoprab4f_1 cv wceq fdfoprab4f_5 cv fdfoprab4f_2 cv idfoprab4f_0 cv cop wceq fdfoprab4f_5 cv idfoprab4f_1 cv idfoprab4f_0 cv cop wceq fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb wb fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb wb fdfoprab4f_2 cv idfoprab4f_1 cv wceq fdfoprab4f_2 cv idfoprab4f_0 cv cop idfoprab4f_1 cv idfoprab4f_0 cv cop fdfoprab4f_5 cv fdfoprab4f_2 cv idfoprab4f_1 cv idfoprab4f_0 cv opeq1 eqeq2d fdfoprab4f_2 cv idfoprab4f_1 cv wceq fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 sbequ12 bibi2d imbi12d fdfoprab4f_5 cv fdfoprab4f_2 cv fdfoprab4f_3 cv cop wceq fdfoprab4f_0 fdfoprab4f_1 wb wi fdfoprab4f_5 cv fdfoprab4f_2 cv idfoprab4f_0 cv cop wceq fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb wb wi fdfoprab4f_3 idfoprab4f_0 fdfoprab4f_5 cv fdfoprab4f_2 cv idfoprab4f_0 cv cop wceq fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb wb fdfoprab4f_3 fdfoprab4f_5 cv fdfoprab4f_2 cv idfoprab4f_0 cv cop wceq fdfoprab4f_3 nfv fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_3 edfoprab4f_1 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 nfs1v nfbi nfim fdfoprab4f_3 cv idfoprab4f_0 cv wceq fdfoprab4f_5 cv fdfoprab4f_2 cv fdfoprab4f_3 cv cop wceq fdfoprab4f_5 cv fdfoprab4f_2 cv idfoprab4f_0 cv cop wceq fdfoprab4f_0 fdfoprab4f_1 wb fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb wb fdfoprab4f_3 cv idfoprab4f_0 cv wceq fdfoprab4f_2 cv fdfoprab4f_3 cv cop fdfoprab4f_2 cv idfoprab4f_0 cv cop fdfoprab4f_5 cv fdfoprab4f_3 cv idfoprab4f_0 cv fdfoprab4f_2 cv opeq2 eqeq2d fdfoprab4f_3 cv idfoprab4f_0 cv wceq fdfoprab4f_1 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_0 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 sbequ12 bibi2d imbi12d edfoprab4f_2 chvar chvar dfoprab4 fdfoprab4f_2 cv fdfoprab4f_6 wcel fdfoprab4f_3 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 wa idfoprab4f_1 cv fdfoprab4f_6 wcel idfoprab4f_0 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb wa fdfoprab4f_2 fdfoprab4f_3 fdfoprab4f_4 idfoprab4f_1 idfoprab4f_0 fdfoprab4f_2 cv fdfoprab4f_6 wcel fdfoprab4f_3 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 wa idfoprab4f_1 nfv fdfoprab4f_2 cv fdfoprab4f_6 wcel fdfoprab4f_3 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 wa idfoprab4f_0 nfv idfoprab4f_1 cv fdfoprab4f_6 wcel idfoprab4f_0 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb fdfoprab4f_2 idfoprab4f_1 cv fdfoprab4f_6 wcel idfoprab4f_0 cv fdfoprab4f_7 wcel wa fdfoprab4f_2 nfv fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 nfs1v nfan idfoprab4f_1 cv fdfoprab4f_6 wcel idfoprab4f_0 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb fdfoprab4f_3 idfoprab4f_1 cv fdfoprab4f_6 wcel idfoprab4f_0 cv fdfoprab4f_7 wcel wa fdfoprab4f_3 nfv fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 fdfoprab4f_3 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 nfs1v nfsb nfan fdfoprab4f_2 cv idfoprab4f_1 cv wceq fdfoprab4f_3 cv idfoprab4f_0 cv wceq wa fdfoprab4f_2 cv fdfoprab4f_6 wcel fdfoprab4f_3 cv fdfoprab4f_7 wcel wa idfoprab4f_1 cv fdfoprab4f_6 wcel idfoprab4f_0 cv fdfoprab4f_7 wcel wa fdfoprab4f_1 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb fdfoprab4f_2 cv idfoprab4f_1 cv wceq fdfoprab4f_2 cv fdfoprab4f_6 wcel idfoprab4f_1 cv fdfoprab4f_6 wcel fdfoprab4f_3 cv idfoprab4f_0 cv wceq fdfoprab4f_3 cv fdfoprab4f_7 wcel idfoprab4f_0 cv fdfoprab4f_7 wcel fdfoprab4f_2 cv idfoprab4f_1 cv fdfoprab4f_6 eleq1 fdfoprab4f_3 cv idfoprab4f_0 cv fdfoprab4f_7 eleq1 bi2anan9 fdfoprab4f_3 cv idfoprab4f_0 cv wceq fdfoprab4f_1 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 cv idfoprab4f_1 cv wceq fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 wsb fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 sbequ12 fdfoprab4f_1 fdfoprab4f_3 idfoprab4f_0 wsb fdfoprab4f_2 idfoprab4f_1 sbequ12 sylan9bbr anbi12d cbvoprab12 eqtr4i $.
$}
$( Define the cross product of three classes.  Compare ~ df-xp .
       (Contributed by FL, 6-Nov-2013.)  (Proof shortened by Mario Carneiro,
       3-Nov-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v u $.
	$v A $.
	$v B $.
	$v C $.
	$d x y z u A $.
	$d x y z u B $.
	$d x y z u C $.
	idfxp3_0 $f set u $.
	fdfxp3_0 $f set x $.
	fdfxp3_1 $f set y $.
	fdfxp3_2 $f set z $.
	fdfxp3_3 $f class A $.
	fdfxp3_4 $f class B $.
	fdfxp3_5 $f class C $.
	dfxp3 $p |- ( ( A X. B ) X. C ) = { <. <. x , y >. , z >. | ( x e. A /\ y e. B /\ z e. C ) } $= idfxp3_0 cv fdfxp3_3 fdfxp3_4 cxp wcel fdfxp3_2 cv fdfxp3_5 wcel wa idfxp3_0 fdfxp3_2 copab fdfxp3_0 cv fdfxp3_3 wcel fdfxp3_1 cv fdfxp3_4 wcel wa fdfxp3_2 cv fdfxp3_5 wcel wa fdfxp3_0 fdfxp3_1 fdfxp3_2 coprab fdfxp3_3 fdfxp3_4 cxp fdfxp3_5 cxp fdfxp3_0 cv fdfxp3_3 wcel fdfxp3_1 cv fdfxp3_4 wcel fdfxp3_2 cv fdfxp3_5 wcel w3a fdfxp3_0 fdfxp3_1 fdfxp3_2 coprab fdfxp3_2 cv fdfxp3_5 wcel fdfxp3_2 cv fdfxp3_5 wcel fdfxp3_0 fdfxp3_1 fdfxp3_2 idfxp3_0 fdfxp3_3 fdfxp3_4 idfxp3_0 cv fdfxp3_0 cv fdfxp3_1 cv cop wceq fdfxp3_2 cv fdfxp3_5 wcel biidd dfoprab4 idfxp3_0 fdfxp3_2 fdfxp3_3 fdfxp3_4 cxp fdfxp3_5 df-xp fdfxp3_0 cv fdfxp3_3 wcel fdfxp3_1 cv fdfxp3_4 wcel fdfxp3_2 cv fdfxp3_5 wcel w3a fdfxp3_0 cv fdfxp3_3 wcel fdfxp3_1 cv fdfxp3_4 wcel wa fdfxp3_2 cv fdfxp3_5 wcel wa fdfxp3_0 fdfxp3_1 fdfxp3_2 fdfxp3_0 cv fdfxp3_3 wcel fdfxp3_1 cv fdfxp3_4 wcel fdfxp3_2 cv fdfxp3_5 wcel df-3an oprabbii 3eqtr4i $.
$}
$( Implicit substitution inference for ordered pairs.  Compare
       ~ copsex2ga .  (Contributed by NM, 12-Mar-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	$d x y ph $.
	fcopsex2gb_0 $f wff ph $.
	fcopsex2gb_1 $f wff ps $.
	fcopsex2gb_2 $f set x $.
	fcopsex2gb_3 $f set y $.
	fcopsex2gb_4 $f class A $.
	ecopsex2gb_0 $e |- ( A = <. x , y >. -> ( ph <-> ps ) ) $.
	copsex2gb $p |- ( E. x E. y ( A = <. x , y >. /\ ps ) <-> ( A e. ( _V X. _V ) /\ ph ) ) $= fcopsex2gb_4 cvv cvv cxp wcel fcopsex2gb_0 wa fcopsex2gb_4 fcopsex2gb_2 cv fcopsex2gb_3 cv cop wceq fcopsex2gb_3 wex fcopsex2gb_2 wex fcopsex2gb_0 wa fcopsex2gb_4 fcopsex2gb_2 cv fcopsex2gb_3 cv cop wceq fcopsex2gb_0 wa fcopsex2gb_3 wex fcopsex2gb_2 wex fcopsex2gb_4 fcopsex2gb_2 cv fcopsex2gb_3 cv cop wceq fcopsex2gb_1 wa fcopsex2gb_3 wex fcopsex2gb_2 wex fcopsex2gb_4 cvv cvv cxp wcel fcopsex2gb_4 fcopsex2gb_2 cv fcopsex2gb_3 cv cop wceq fcopsex2gb_3 wex fcopsex2gb_2 wex fcopsex2gb_0 fcopsex2gb_2 fcopsex2gb_3 fcopsex2gb_4 elvv anbi1i fcopsex2gb_4 fcopsex2gb_2 cv fcopsex2gb_3 cv cop wceq fcopsex2gb_0 fcopsex2gb_2 fcopsex2gb_3 19.41vv fcopsex2gb_4 fcopsex2gb_2 cv fcopsex2gb_3 cv cop wceq fcopsex2gb_0 wa fcopsex2gb_4 fcopsex2gb_2 cv fcopsex2gb_3 cv cop wceq fcopsex2gb_1 wa fcopsex2gb_2 fcopsex2gb_3 fcopsex2gb_4 fcopsex2gb_2 cv fcopsex2gb_3 cv cop wceq fcopsex2gb_0 fcopsex2gb_1 ecopsex2gb_0 pm5.32i 2exbii 3bitr2ri $.
$}
$( Implicit substitution inference for ordered pairs.  Compare
       ~ copsex2g .  (Contributed by NM, 26-Feb-2014.)  (Proof shortened by
       Mario Carneiro, 31-Aug-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v V $.
	$v W $.
	$d x y A $.
	$d x y ph $.
	fcopsex2ga_0 $f wff ph $.
	fcopsex2ga_1 $f wff ps $.
	fcopsex2ga_2 $f set x $.
	fcopsex2ga_3 $f set y $.
	fcopsex2ga_4 $f class A $.
	fcopsex2ga_5 $f class V $.
	fcopsex2ga_6 $f class W $.
	ecopsex2ga_0 $e |- ( A = <. x , y >. -> ( ph <-> ps ) ) $.
	copsex2ga $p |- ( A e. ( V X. W ) -> ( ph <-> E. x E. y ( A = <. x , y >. /\ ps ) ) ) $= fcopsex2ga_4 fcopsex2ga_5 fcopsex2ga_6 cxp wcel fcopsex2ga_4 cvv cvv cxp wcel fcopsex2ga_0 fcopsex2ga_4 fcopsex2ga_2 cv fcopsex2ga_3 cv cop wceq fcopsex2ga_1 wa fcopsex2ga_3 wex fcopsex2ga_2 wex wb fcopsex2ga_5 fcopsex2ga_6 cxp cvv cvv cxp fcopsex2ga_4 fcopsex2ga_5 fcopsex2ga_6 xpss sseli fcopsex2ga_4 fcopsex2ga_2 cv fcopsex2ga_3 cv cop wceq fcopsex2ga_1 wa fcopsex2ga_3 wex fcopsex2ga_2 wex fcopsex2ga_4 cvv cvv cxp wcel fcopsex2ga_0 fcopsex2ga_0 fcopsex2ga_1 fcopsex2ga_2 fcopsex2ga_3 fcopsex2ga_4 ecopsex2ga_0 copsex2gb baibr syl $.
$}
$( Membership in an ordered pair class builder.  (Contributed by NM,
       25-Feb-2014.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	$d x y ph $.
	felopaba_0 $f wff ph $.
	felopaba_1 $f wff ps $.
	felopaba_2 $f set x $.
	felopaba_3 $f set y $.
	felopaba_4 $f class A $.
	eelopaba_0 $e |- ( A = <. x , y >. -> ( ph <-> ps ) ) $.
	elopaba $p |- ( A e. { <. x , y >. | ps } <-> ( A e. ( _V X. _V ) /\ ph ) ) $= felopaba_4 felopaba_1 felopaba_2 felopaba_3 copab wcel felopaba_4 felopaba_2 cv felopaba_3 cv cop wceq felopaba_1 wa felopaba_3 wex felopaba_2 wex felopaba_4 cvv cvv cxp wcel felopaba_0 wa felopaba_1 felopaba_2 felopaba_3 felopaba_4 elopab felopaba_0 felopaba_1 felopaba_2 felopaba_3 felopaba_4 eelopaba_0 copsex2gb bitri $.
$}
$( Transfer ordered-pair existence from/to single variable existence.
       (Contributed by NM, 26-Feb-2014.)  (Proof shortened by Mario Carneiro,
       31-Aug-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d y z ph $.
	$d x ps $.
	$d x y z $.
	fexopxfr_0 $f wff ph $.
	fexopxfr_1 $f wff ps $.
	fexopxfr_2 $f set x $.
	fexopxfr_3 $f set y $.
	fexopxfr_4 $f set z $.
	eexopxfr_0 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	exopxfr $p |- ( E. x e. ( _V X. _V ) ph <-> E. y E. z ps ) $= fexopxfr_0 fexopxfr_2 cvv cvv cxp wrex fexopxfr_1 fexopxfr_4 cvv wrex fexopxfr_3 cvv wrex fexopxfr_1 fexopxfr_4 cvv wrex fexopxfr_3 wex fexopxfr_1 fexopxfr_4 wex fexopxfr_3 wex fexopxfr_0 fexopxfr_1 fexopxfr_2 fexopxfr_3 fexopxfr_4 cvv cvv eexopxfr_0 rexxp fexopxfr_1 fexopxfr_4 cvv wrex fexopxfr_3 rexv fexopxfr_1 fexopxfr_4 cvv wrex fexopxfr_1 fexopxfr_4 wex fexopxfr_3 fexopxfr_1 fexopxfr_4 rexv exbii 3bitri $.
$}
$( Transfer ordered-pair existence from/to single variable existence.
       (Contributed by NM, 26-Feb-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$d x y z A $.
	$d y z ph $.
	$d x ps $.
	fexopxfr2_0 $f wff ph $.
	fexopxfr2_1 $f wff ps $.
	fexopxfr2_2 $f set x $.
	fexopxfr2_3 $f set y $.
	fexopxfr2_4 $f set z $.
	fexopxfr2_5 $f class A $.
	eexopxfr2_0 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	exopxfr2 $p |- ( Rel A -> ( E. x e. A ph <-> E. y E. z ( <. y , z >. e. A /\ ps ) ) ) $= fexopxfr2_5 wrel fexopxfr2_0 fexopxfr2_2 fexopxfr2_5 wrex fexopxfr2_2 cv fexopxfr2_5 wcel fexopxfr2_0 wa fexopxfr2_2 cvv cvv cxp wrex fexopxfr2_3 cv fexopxfr2_4 cv cop fexopxfr2_5 wcel fexopxfr2_1 wa fexopxfr2_4 wex fexopxfr2_3 wex fexopxfr2_5 wrel fexopxfr2_0 fexopxfr2_2 cv fexopxfr2_5 wcel fexopxfr2_0 wa fexopxfr2_2 fexopxfr2_5 cvv cvv cxp fexopxfr2_5 wrel fexopxfr2_2 cv fexopxfr2_5 wcel fexopxfr2_0 wa fexopxfr2_2 cv cvv cvv cxp wcel fexopxfr2_5 wrel fexopxfr2_2 cv fexopxfr2_5 wcel fexopxfr2_2 cv cvv cvv cxp wcel fexopxfr2_0 fexopxfr2_5 wrel fexopxfr2_5 cvv cvv cxp fexopxfr2_2 cv fexopxfr2_5 wrel fexopxfr2_5 cvv cvv cxp wss fexopxfr2_5 df-rel biimpi sseld adantrd pm4.71rd rexbidv2 fexopxfr2_2 cv fexopxfr2_5 wcel fexopxfr2_0 wa fexopxfr2_3 cv fexopxfr2_4 cv cop fexopxfr2_5 wcel fexopxfr2_1 wa fexopxfr2_2 fexopxfr2_3 fexopxfr2_4 fexopxfr2_2 cv fexopxfr2_3 cv fexopxfr2_4 cv cop wceq fexopxfr2_2 cv fexopxfr2_5 wcel fexopxfr2_3 cv fexopxfr2_4 cv cop fexopxfr2_5 wcel fexopxfr2_0 fexopxfr2_1 fexopxfr2_2 cv fexopxfr2_3 cv fexopxfr2_4 cv cop fexopxfr2_5 eleq1 eexopxfr2_0 anbi12d exopxfr syl6bb $.
$}
$( A consequence of membership in an ordered-pair class abstraction, using
       ordered pair extractors.  (Contributed by NM, 29-Aug-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	$d x y ch $.
	felopabi_0 $f wff ph $.
	felopabi_1 $f wff ps $.
	felopabi_2 $f wff ch $.
	felopabi_3 $f set x $.
	felopabi_4 $f set y $.
	felopabi_5 $f class A $.
	eelopabi_0 $e |- ( x = ( 1st ` A ) -> ( ph <-> ps ) ) $.
	eelopabi_1 $e |- ( y = ( 2nd ` A ) -> ( ps <-> ch ) ) $.
	elopabi $p |- ( A e. { <. x , y >. | ph } -> ch ) $= felopabi_5 felopabi_0 felopabi_3 felopabi_4 copab wcel felopabi_5 c1st cfv felopabi_5 c2nd cfv cop felopabi_0 felopabi_3 felopabi_4 copab wcel felopabi_2 felopabi_5 felopabi_0 felopabi_3 felopabi_4 copab wcel felopabi_5 felopabi_5 c1st cfv felopabi_5 c2nd cfv cop felopabi_0 felopabi_3 felopabi_4 copab felopabi_0 felopabi_3 felopabi_4 copab wrel felopabi_5 felopabi_0 felopabi_3 felopabi_4 copab wcel felopabi_5 felopabi_5 c1st cfv felopabi_5 c2nd cfv cop wceq felopabi_0 felopabi_3 felopabi_4 relopab felopabi_5 felopabi_0 felopabi_3 felopabi_4 copab 1st2nd mpan felopabi_5 felopabi_0 felopabi_3 felopabi_4 copab wcel id eqeltrrd felopabi_0 felopabi_1 felopabi_2 felopabi_3 felopabi_4 felopabi_5 c1st cfv felopabi_5 c2nd cfv felopabi_5 c1st fvex felopabi_5 c2nd fvex eelopabi_0 eelopabi_1 opelopab sylib $.
$}
$( A consequence of membership in an operation class abstraction, using
       ordered pair extractors.  (Contributed by NM, 6-Nov-2006.)  (Revised by
       David Abernethy, 19-Jun-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v A $.
	$d w x y z A $.
	$d w ph $.
	$d x y z th $.
	ieloprabi_0 $f set w $.
	feloprabi_0 $f wff ph $.
	feloprabi_1 $f wff ps $.
	feloprabi_2 $f wff ch $.
	feloprabi_3 $f wff th $.
	feloprabi_4 $f set x $.
	feloprabi_5 $f set y $.
	feloprabi_6 $f set z $.
	feloprabi_7 $f class A $.
	eeloprabi_0 $e |- ( x = ( 1st ` ( 1st ` A ) ) -> ( ph <-> ps ) ) $.
	eeloprabi_1 $e |- ( y = ( 2nd ` ( 1st ` A ) ) -> ( ps <-> ch ) ) $.
	eeloprabi_2 $e |- ( z = ( 2nd ` A ) -> ( ch <-> th ) ) $.
	eloprabi $p |- ( A e. { <. <. x , y >. , z >. | ph } -> th ) $= feloprabi_7 feloprabi_0 feloprabi_4 feloprabi_5 feloprabi_6 coprab wcel feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_6 wex feloprabi_5 wex feloprabi_4 wex feloprabi_3 feloprabi_7 feloprabi_0 feloprabi_4 feloprabi_5 feloprabi_6 coprab wcel feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_6 wex feloprabi_5 wex feloprabi_4 wex ieloprabi_0 cv feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_6 wex feloprabi_5 wex feloprabi_4 wex feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_6 wex feloprabi_5 wex feloprabi_4 wex ieloprabi_0 feloprabi_7 feloprabi_0 feloprabi_4 feloprabi_5 feloprabi_6 coprab feloprabi_0 feloprabi_4 feloprabi_5 feloprabi_6 coprab ieloprabi_0 cv feloprabi_7 wceq ieloprabi_0 cv feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_4 feloprabi_5 feloprabi_6 ieloprabi_0 cv feloprabi_7 wceq ieloprabi_0 cv feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 ieloprabi_0 cv feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop eqeq1 anbi1d 3exbidv feloprabi_0 feloprabi_4 feloprabi_5 feloprabi_6 ieloprabi_0 df-oprab elab2g ibi feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_6 wex feloprabi_5 wex feloprabi_3 feloprabi_4 feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_6 wex feloprabi_3 feloprabi_5 feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 wa feloprabi_3 feloprabi_6 feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 feloprabi_3 feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_0 feloprabi_1 feloprabi_2 feloprabi_3 feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_4 cv feloprabi_7 c1st cfv c1st cfv wceq feloprabi_0 feloprabi_1 wb feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_7 c1st cfv c1st cfv feloprabi_4 cv feloprabi_5 cv cop c1st cfv feloprabi_4 cv feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_7 c1st cfv feloprabi_4 cv feloprabi_5 cv cop c1st feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv feloprabi_7 feloprabi_4 cv feloprabi_5 cv opex feloprabi_6 vex op1std fveq2d feloprabi_4 cv feloprabi_5 cv feloprabi_4 vex feloprabi_5 vex op1st syl6req eeloprabi_0 syl feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_5 cv feloprabi_7 c1st cfv c2nd cfv wceq feloprabi_1 feloprabi_2 wb feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_7 c1st cfv c2nd cfv feloprabi_4 cv feloprabi_5 cv cop c2nd cfv feloprabi_5 cv feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_7 c1st cfv feloprabi_4 cv feloprabi_5 cv cop c2nd feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv feloprabi_7 feloprabi_4 cv feloprabi_5 cv opex feloprabi_6 vex op1std fveq2d feloprabi_4 cv feloprabi_5 cv feloprabi_4 vex feloprabi_5 vex op2nd syl6req eeloprabi_1 syl feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_6 cv feloprabi_7 c2nd cfv wceq feloprabi_2 feloprabi_3 wb feloprabi_7 feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv cop wceq feloprabi_7 c2nd cfv feloprabi_6 cv feloprabi_4 cv feloprabi_5 cv cop feloprabi_6 cv feloprabi_7 feloprabi_4 cv feloprabi_5 cv opex feloprabi_6 vex op2ndd eqcomd eeloprabi_2 syl 3bitrd biimpa exlimiv exlimiv exlimiv syl $.
$}
$( Express a two-argument function as a one-argument function, or
       vice-versa.  (Contributed by Mario Carneiro, 24-Dec-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v v $.
	$v u $.
	$v A $.
	$v B $.
	$v C $.
	$d u v x y z A $.
	$d u v y z B $.
	$d u v z C $.
	impt2mptsx_0 $f set v $.
	impt2mptsx_1 $f set u $.
	fmpt2mptsx_0 $f set x $.
	fmpt2mptsx_1 $f set y $.
	fmpt2mptsx_2 $f set z $.
	fmpt2mptsx_3 $f class A $.
	fmpt2mptsx_4 $f class B $.
	fmpt2mptsx_5 $f class C $.
	mpt2mptsx $p |- ( x e. A , y e. B |-> C ) = ( z e. U_ x e. A ( { x } X. B ) |-> [_ ( 1st ` z ) / x ]_ [_ ( 2nd ` z ) / y ]_ C ) $= fmpt2mptsx_2 impt2mptsx_1 fmpt2mptsx_3 impt2mptsx_1 cv csn fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb cxp ciun fmpt2mptsx_0 fmpt2mptsx_2 cv c1st cfv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb csb cmpt impt2mptsx_1 impt2mptsx_0 fmpt2mptsx_3 fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb csb cmpt2 fmpt2mptsx_2 fmpt2mptsx_0 fmpt2mptsx_3 fmpt2mptsx_0 cv csn fmpt2mptsx_4 cxp ciun fmpt2mptsx_0 fmpt2mptsx_2 cv c1st cfv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb csb cmpt fmpt2mptsx_0 fmpt2mptsx_1 fmpt2mptsx_3 fmpt2mptsx_4 fmpt2mptsx_5 cmpt2 impt2mptsx_1 impt2mptsx_0 fmpt2mptsx_2 fmpt2mptsx_3 fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb fmpt2mptsx_0 fmpt2mptsx_2 cv c1st cfv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb csb fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb csb fmpt2mptsx_2 cv impt2mptsx_1 cv impt2mptsx_0 cv cop wceq fmpt2mptsx_0 fmpt2mptsx_2 cv c1st cfv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb csb fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb csb fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb csb fmpt2mptsx_2 cv impt2mptsx_1 cv impt2mptsx_0 cv cop wceq fmpt2mptsx_0 fmpt2mptsx_2 cv c1st cfv impt2mptsx_1 cv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb impt2mptsx_1 cv impt2mptsx_0 cv fmpt2mptsx_2 cv impt2mptsx_1 vex impt2mptsx_0 vex op1std csbeq1d fmpt2mptsx_2 cv impt2mptsx_1 cv impt2mptsx_0 cv cop wceq fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb fmpt2mptsx_2 cv impt2mptsx_1 cv impt2mptsx_0 cv cop wceq fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv impt2mptsx_0 cv fmpt2mptsx_5 impt2mptsx_1 cv impt2mptsx_0 cv fmpt2mptsx_2 cv impt2mptsx_1 vex impt2mptsx_0 vex op2ndd csbeq1d csbeq2dv eqtrd mpt2mptx fmpt2mptsx_0 fmpt2mptsx_3 fmpt2mptsx_0 cv csn fmpt2mptsx_4 cxp ciun impt2mptsx_1 fmpt2mptsx_3 impt2mptsx_1 cv csn fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb cxp ciun wceq fmpt2mptsx_2 fmpt2mptsx_0 fmpt2mptsx_3 fmpt2mptsx_0 cv csn fmpt2mptsx_4 cxp ciun fmpt2mptsx_0 fmpt2mptsx_2 cv c1st cfv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb csb cmpt fmpt2mptsx_2 impt2mptsx_1 fmpt2mptsx_3 impt2mptsx_1 cv csn fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb cxp ciun fmpt2mptsx_0 fmpt2mptsx_2 cv c1st cfv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb csb cmpt wceq fmpt2mptsx_0 impt2mptsx_1 fmpt2mptsx_3 fmpt2mptsx_0 cv csn fmpt2mptsx_4 cxp impt2mptsx_1 cv csn fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb cxp impt2mptsx_1 fmpt2mptsx_0 cv csn fmpt2mptsx_4 cxp nfcv fmpt2mptsx_0 impt2mptsx_1 cv csn fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb fmpt2mptsx_0 impt2mptsx_1 cv csn nfcv fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 nfcsb1v nfxp fmpt2mptsx_0 cv impt2mptsx_1 cv wceq fmpt2mptsx_0 cv csn impt2mptsx_1 cv csn fmpt2mptsx_4 fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb fmpt2mptsx_0 cv impt2mptsx_1 cv sneq fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csbeq1a xpeq12d cbviun fmpt2mptsx_2 fmpt2mptsx_0 fmpt2mptsx_3 fmpt2mptsx_0 cv csn fmpt2mptsx_4 cxp ciun impt2mptsx_1 fmpt2mptsx_3 impt2mptsx_1 cv csn fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb cxp ciun fmpt2mptsx_0 fmpt2mptsx_2 cv c1st cfv fmpt2mptsx_1 fmpt2mptsx_2 cv c2nd cfv fmpt2mptsx_5 csb csb mpteq1 ax-mp fmpt2mptsx_0 fmpt2mptsx_1 impt2mptsx_1 impt2mptsx_0 fmpt2mptsx_3 fmpt2mptsx_4 fmpt2mptsx_5 fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csb fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb csb impt2mptsx_1 fmpt2mptsx_4 nfcv fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 nfcsb1v impt2mptsx_1 fmpt2mptsx_5 nfcv impt2mptsx_0 fmpt2mptsx_5 nfcv fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb nfcsb1v fmpt2mptsx_1 fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb fmpt2mptsx_1 impt2mptsx_1 cv nfcv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 nfcsb1v nfcsb fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_4 csbeq1a fmpt2mptsx_1 cv impt2mptsx_0 cv wceq fmpt2mptsx_0 cv impt2mptsx_1 cv wceq fmpt2mptsx_5 fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb csb fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csbeq1a fmpt2mptsx_0 impt2mptsx_1 cv fmpt2mptsx_1 impt2mptsx_0 cv fmpt2mptsx_5 csb csbeq1a sylan9eqr cbvmpt2x 3eqtr4ri $.
$}
$( Express a two-argument function as a one-argument function, or
       vice-versa.  (Contributed by Mario Carneiro, 24-Sep-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$d x y z A $.
	$d y z B $.
	$d z C $.
	$d x B $.
	fmpt2mpts_0 $f set x $.
	fmpt2mpts_1 $f set y $.
	fmpt2mpts_2 $f set z $.
	fmpt2mpts_3 $f class A $.
	fmpt2mpts_4 $f class B $.
	fmpt2mpts_5 $f class C $.
	mpt2mpts $p |- ( x e. A , y e. B |-> C ) = ( z e. ( A X. B ) |-> [_ ( 1st ` z ) / x ]_ [_ ( 2nd ` z ) / y ]_ C ) $= fmpt2mpts_0 fmpt2mpts_1 fmpt2mpts_3 fmpt2mpts_4 fmpt2mpts_5 cmpt2 fmpt2mpts_2 fmpt2mpts_0 fmpt2mpts_3 fmpt2mpts_0 cv csn fmpt2mpts_4 cxp ciun fmpt2mpts_0 fmpt2mpts_2 cv c1st cfv fmpt2mpts_1 fmpt2mpts_2 cv c2nd cfv fmpt2mpts_5 csb csb cmpt fmpt2mpts_2 fmpt2mpts_3 fmpt2mpts_4 cxp fmpt2mpts_0 fmpt2mpts_2 cv c1st cfv fmpt2mpts_1 fmpt2mpts_2 cv c2nd cfv fmpt2mpts_5 csb csb cmpt fmpt2mpts_0 fmpt2mpts_1 fmpt2mpts_2 fmpt2mpts_3 fmpt2mpts_4 fmpt2mpts_5 mpt2mptsx fmpt2mpts_0 fmpt2mpts_3 fmpt2mpts_0 cv csn fmpt2mpts_4 cxp ciun fmpt2mpts_3 fmpt2mpts_4 cxp wceq fmpt2mpts_2 fmpt2mpts_0 fmpt2mpts_3 fmpt2mpts_0 cv csn fmpt2mpts_4 cxp ciun fmpt2mpts_0 fmpt2mpts_2 cv c1st cfv fmpt2mpts_1 fmpt2mpts_2 cv c2nd cfv fmpt2mpts_5 csb csb cmpt fmpt2mpts_2 fmpt2mpts_3 fmpt2mpts_4 cxp fmpt2mpts_0 fmpt2mpts_2 cv c1st cfv fmpt2mpts_1 fmpt2mpts_2 cv c2nd cfv fmpt2mpts_5 csb csb cmpt wceq fmpt2mpts_0 fmpt2mpts_3 fmpt2mpts_4 iunxpconst fmpt2mpts_2 fmpt2mpts_0 fmpt2mpts_3 fmpt2mpts_0 cv csn fmpt2mpts_4 cxp ciun fmpt2mpts_3 fmpt2mpts_4 cxp fmpt2mpts_0 fmpt2mpts_2 cv c1st cfv fmpt2mpts_1 fmpt2mpts_2 cv c2nd cfv fmpt2mpts_5 csb csb mpteq1 ax-mp eqtri $.
$}
$( The domain of a mapping is a subset of its base class.  (Contributed by
       Mario Carneiro, 9-Feb-2015.) $)
${
	$v x $.
	$v y $.
	$v v $.
	$v u $.
	$v t $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$d t u v x y A $.
	$d t u v y B $.
	$d t u v C $.
	$d v x y $.
	idmmpt2ssx_0 $f set v $.
	idmmpt2ssx_1 $f set u $.
	idmmpt2ssx_2 $f set t $.
	fdmmpt2ssx_0 $f set x $.
	fdmmpt2ssx_1 $f set y $.
	fdmmpt2ssx_2 $f class A $.
	fdmmpt2ssx_3 $f class B $.
	fdmmpt2ssx_4 $f class C $.
	fdmmpt2ssx_5 $f class F $.
	edmmpt2ssx_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	dmmpt2ssx $p |- dom F C_ U_ x e. A ( { x } X. B ) $= fdmmpt2ssx_5 cdm idmmpt2ssx_1 fdmmpt2ssx_2 idmmpt2ssx_1 cv csn fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb cxp ciun fdmmpt2ssx_0 fdmmpt2ssx_2 fdmmpt2ssx_0 cv csn fdmmpt2ssx_3 cxp ciun idmmpt2ssx_2 idmmpt2ssx_1 fdmmpt2ssx_2 idmmpt2ssx_1 cv csn fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb cxp ciun fdmmpt2ssx_0 idmmpt2ssx_2 cv c1st cfv fdmmpt2ssx_1 idmmpt2ssx_2 cv c2nd cfv fdmmpt2ssx_4 csb csb fdmmpt2ssx_5 fdmmpt2ssx_0 fdmmpt2ssx_1 fdmmpt2ssx_2 fdmmpt2ssx_3 fdmmpt2ssx_4 cmpt2 idmmpt2ssx_1 idmmpt2ssx_0 fdmmpt2ssx_2 fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb csb cmpt2 fdmmpt2ssx_5 idmmpt2ssx_2 idmmpt2ssx_1 fdmmpt2ssx_2 idmmpt2ssx_1 cv csn fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb cxp ciun fdmmpt2ssx_0 idmmpt2ssx_2 cv c1st cfv fdmmpt2ssx_1 idmmpt2ssx_2 cv c2nd cfv fdmmpt2ssx_4 csb csb cmpt fdmmpt2ssx_0 fdmmpt2ssx_1 idmmpt2ssx_1 idmmpt2ssx_0 fdmmpt2ssx_2 fdmmpt2ssx_3 fdmmpt2ssx_4 fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb csb idmmpt2ssx_1 fdmmpt2ssx_3 nfcv fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 nfcsb1v idmmpt2ssx_1 fdmmpt2ssx_4 nfcv idmmpt2ssx_0 fdmmpt2ssx_4 nfcv fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb nfcsb1v fdmmpt2ssx_1 fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb fdmmpt2ssx_1 idmmpt2ssx_1 cv nfcv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 nfcsb1v nfcsb fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csbeq1a fdmmpt2ssx_1 cv idmmpt2ssx_0 cv wceq fdmmpt2ssx_0 cv idmmpt2ssx_1 cv wceq fdmmpt2ssx_4 fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb csb fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csbeq1a fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb csbeq1a sylan9eqr cbvmpt2x edmmpt2ssx_0 idmmpt2ssx_1 idmmpt2ssx_0 idmmpt2ssx_2 fdmmpt2ssx_2 fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb fdmmpt2ssx_0 idmmpt2ssx_2 cv c1st cfv fdmmpt2ssx_1 idmmpt2ssx_2 cv c2nd cfv fdmmpt2ssx_4 csb csb fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb csb idmmpt2ssx_2 cv idmmpt2ssx_1 cv idmmpt2ssx_0 cv cop wceq fdmmpt2ssx_0 idmmpt2ssx_2 cv c1st cfv fdmmpt2ssx_1 idmmpt2ssx_2 cv c2nd cfv fdmmpt2ssx_4 csb csb fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_2 cv c2nd cfv fdmmpt2ssx_4 csb csb fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb csb idmmpt2ssx_2 cv idmmpt2ssx_1 cv idmmpt2ssx_0 cv cop wceq fdmmpt2ssx_0 idmmpt2ssx_2 cv c1st cfv idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_2 cv c2nd cfv fdmmpt2ssx_4 csb idmmpt2ssx_1 cv idmmpt2ssx_0 cv idmmpt2ssx_2 cv idmmpt2ssx_1 vex idmmpt2ssx_0 vex op1std csbeq1d idmmpt2ssx_2 cv idmmpt2ssx_1 cv idmmpt2ssx_0 cv cop wceq fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_1 idmmpt2ssx_2 cv c2nd cfv fdmmpt2ssx_4 csb fdmmpt2ssx_1 idmmpt2ssx_0 cv fdmmpt2ssx_4 csb idmmpt2ssx_2 cv idmmpt2ssx_1 cv idmmpt2ssx_0 cv cop wceq fdmmpt2ssx_1 idmmpt2ssx_2 cv c2nd cfv idmmpt2ssx_0 cv fdmmpt2ssx_4 idmmpt2ssx_1 cv idmmpt2ssx_0 cv idmmpt2ssx_2 cv idmmpt2ssx_1 vex idmmpt2ssx_0 vex op2ndd csbeq1d csbeq2dv eqtrd mpt2mptx 3eqtr4i dmmptss fdmmpt2ssx_0 idmmpt2ssx_1 fdmmpt2ssx_2 fdmmpt2ssx_0 cv csn fdmmpt2ssx_3 cxp idmmpt2ssx_1 cv csn fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb cxp idmmpt2ssx_1 fdmmpt2ssx_0 cv csn fdmmpt2ssx_3 cxp nfcv fdmmpt2ssx_0 idmmpt2ssx_1 cv csn fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb fdmmpt2ssx_0 idmmpt2ssx_1 cv csn nfcv fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 nfcsb1v nfxp fdmmpt2ssx_0 cv idmmpt2ssx_1 cv wceq fdmmpt2ssx_0 cv csn idmmpt2ssx_1 cv csn fdmmpt2ssx_3 fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csb fdmmpt2ssx_0 cv idmmpt2ssx_1 cv sneq fdmmpt2ssx_0 idmmpt2ssx_1 cv fdmmpt2ssx_3 csbeq1a xpeq12d cbviun sseqtr4i $.
$}
$( Functionality, domain and codomain of a class given by the "maps to"
       notation, where ` B ( x ) ` is not constant but depends on ` x ` .
       (Contributed by NM, 29-Dec-2014.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v F $.
	$d v w x y z A $.
	$d v w y z B $.
	$d v w z C $.
	$d v w x y z D $.
	ifmpt2x_0 $f set z $.
	ifmpt2x_1 $f set w $.
	ifmpt2x_2 $f set v $.
	ffmpt2x_0 $f set x $.
	ffmpt2x_1 $f set y $.
	ffmpt2x_2 $f class A $.
	ffmpt2x_3 $f class B $.
	ffmpt2x_4 $f class C $.
	ffmpt2x_5 $f class D $.
	ffmpt2x_6 $f class F $.
	efmpt2x_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	fmpt2x $p |- ( A. x e. A A. y e. B C e. D <-> F : U_ x e. A ( { x } X. B ) --> D ) $= ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 wcel ifmpt2x_1 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wral ifmpt2x_0 ffmpt2x_2 wral ifmpt2x_0 ffmpt2x_2 ifmpt2x_0 cv csn ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb cxp ciun ffmpt2x_5 ffmpt2x_6 wf ffmpt2x_4 ffmpt2x_5 wcel ffmpt2x_1 ffmpt2x_3 wral ffmpt2x_0 ffmpt2x_2 wral ffmpt2x_0 ffmpt2x_2 ffmpt2x_0 cv csn ffmpt2x_3 cxp ciun ffmpt2x_5 ffmpt2x_6 wf ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 wcel ifmpt2x_1 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wral ifmpt2x_0 ffmpt2x_2 wral ffmpt2x_0 ifmpt2x_2 cv c1st cfv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_5 wcel ifmpt2x_2 ifmpt2x_0 ffmpt2x_2 ifmpt2x_0 cv csn ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb cxp ciun wral ifmpt2x_0 ffmpt2x_2 ifmpt2x_0 cv csn ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb cxp ciun ffmpt2x_5 ffmpt2x_6 wf ffmpt2x_0 ifmpt2x_2 cv c1st cfv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_5 wcel ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 wcel ifmpt2x_2 ifmpt2x_0 ifmpt2x_1 ffmpt2x_2 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_0 ifmpt2x_2 cv c1st cfv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_0 ifmpt2x_2 cv c1st cfv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_0 ifmpt2x_2 cv c1st cfv ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb ifmpt2x_0 cv ifmpt2x_1 cv ifmpt2x_2 cv ifmpt2x_0 vex ifmpt2x_1 vex op1std csbeq1d ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ifmpt2x_1 cv ffmpt2x_4 ifmpt2x_0 cv ifmpt2x_1 cv ifmpt2x_2 cv ifmpt2x_0 vex ifmpt2x_1 vex op2ndd csbeq1d csbeq2dv eqtrd eleq1d raliunxp ifmpt2x_2 ifmpt2x_0 ffmpt2x_2 ifmpt2x_0 cv csn ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb cxp ciun ffmpt2x_5 ffmpt2x_0 ifmpt2x_2 cv c1st cfv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_6 ffmpt2x_0 ffmpt2x_1 ffmpt2x_2 ffmpt2x_3 ffmpt2x_4 cmpt2 ifmpt2x_0 ifmpt2x_1 ffmpt2x_2 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb cmpt2 ffmpt2x_6 ifmpt2x_2 ifmpt2x_0 ffmpt2x_2 ifmpt2x_0 cv csn ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb cxp ciun ffmpt2x_0 ifmpt2x_2 cv c1st cfv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb cmpt ffmpt2x_0 cv ffmpt2x_2 wcel ffmpt2x_1 cv ffmpt2x_3 wcel wa ifmpt2x_2 cv ffmpt2x_4 wceq wa ffmpt2x_0 ffmpt2x_1 ifmpt2x_2 coprab ifmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel wa ifmpt2x_2 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb wceq wa ifmpt2x_0 ifmpt2x_1 ifmpt2x_2 coprab ffmpt2x_0 ffmpt2x_1 ffmpt2x_2 ffmpt2x_3 ffmpt2x_4 cmpt2 ifmpt2x_0 ifmpt2x_1 ffmpt2x_2 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb cmpt2 ffmpt2x_0 cv ffmpt2x_2 wcel ffmpt2x_1 cv ffmpt2x_3 wcel wa ifmpt2x_2 cv ffmpt2x_4 wceq wa ifmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel wa ifmpt2x_2 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb wceq wa ffmpt2x_0 ffmpt2x_1 ifmpt2x_2 ifmpt2x_0 ifmpt2x_1 ffmpt2x_0 cv ffmpt2x_2 wcel ffmpt2x_1 cv ffmpt2x_3 wcel wa ifmpt2x_2 cv ffmpt2x_4 wceq wa ifmpt2x_0 nfv ffmpt2x_0 cv ffmpt2x_2 wcel ffmpt2x_1 cv ffmpt2x_3 wcel wa ifmpt2x_2 cv ffmpt2x_4 wceq wa ifmpt2x_1 nfv ifmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel wa ifmpt2x_2 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb wceq ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_2 wcel ffmpt2x_0 nfv ffmpt2x_0 ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 nfcsb1v nfel2 nfan ffmpt2x_0 ifmpt2x_2 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb nfcsb1v nfeq2 nfan ifmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel wa ifmpt2x_2 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb wceq ffmpt2x_1 ifmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel wa ffmpt2x_1 nfv ffmpt2x_1 ifmpt2x_2 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_1 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ffmpt2x_1 ifmpt2x_0 cv nfcv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 nfcsb1v nfcsb nfeq2 nfan ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_1 cv ifmpt2x_1 cv wceq wa ffmpt2x_0 cv ffmpt2x_2 wcel ffmpt2x_1 cv ffmpt2x_3 wcel wa ifmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel wa ifmpt2x_2 cv ffmpt2x_4 wceq ifmpt2x_2 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb wceq ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_1 cv ifmpt2x_1 cv wceq wa ffmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_0 cv ffmpt2x_2 wcel ffmpt2x_1 cv ffmpt2x_3 wcel ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_0 cv ffmpt2x_2 wcel ifmpt2x_0 cv ffmpt2x_2 wcel wb ffmpt2x_1 cv ifmpt2x_1 cv wceq ffmpt2x_0 cv ifmpt2x_0 cv ffmpt2x_2 eleq1 adantr ffmpt2x_1 cv ifmpt2x_1 cv wceq ffmpt2x_1 cv ffmpt2x_3 wcel ifmpt2x_1 cv ffmpt2x_3 wcel ffmpt2x_0 cv ifmpt2x_0 cv wceq ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wcel ffmpt2x_1 cv ifmpt2x_1 cv ffmpt2x_3 eleq1 ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_3 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ifmpt2x_1 cv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csbeq1a eleq2d sylan9bbr anbi12d ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_1 cv ifmpt2x_1 cv wceq wa ffmpt2x_4 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ifmpt2x_2 cv ffmpt2x_1 cv ifmpt2x_1 cv wceq ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_4 ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csbeq1a ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csbeq1a sylan9eqr eqeq2d anbi12d cbvoprab12 ffmpt2x_0 ffmpt2x_1 ifmpt2x_2 ffmpt2x_2 ffmpt2x_3 ffmpt2x_4 df-mpt2 ifmpt2x_0 ifmpt2x_1 ifmpt2x_2 ffmpt2x_2 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb df-mpt2 3eqtr4i efmpt2x_0 ifmpt2x_0 ifmpt2x_1 ifmpt2x_2 ffmpt2x_2 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 ifmpt2x_2 cv c1st cfv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_0 ifmpt2x_2 cv c1st cfv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_0 ifmpt2x_2 cv c1st cfv ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb ifmpt2x_0 cv ifmpt2x_1 cv ifmpt2x_2 cv ifmpt2x_0 vex ifmpt2x_1 vex op1std csbeq1d ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ffmpt2x_4 csb ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ifmpt2x_2 cv ifmpt2x_0 cv ifmpt2x_1 cv cop wceq ffmpt2x_1 ifmpt2x_2 cv c2nd cfv ifmpt2x_1 cv ffmpt2x_4 ifmpt2x_0 cv ifmpt2x_1 cv ifmpt2x_2 cv ifmpt2x_0 vex ifmpt2x_1 vex op2ndd csbeq1d csbeq2dv eqtrd mpt2mptx 3eqtr4i fmpt bitr3i ffmpt2x_4 ffmpt2x_5 wcel ffmpt2x_1 ffmpt2x_3 wral ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 wcel ifmpt2x_1 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wral ffmpt2x_0 ifmpt2x_0 ffmpt2x_2 ffmpt2x_4 ffmpt2x_5 wcel ffmpt2x_1 ffmpt2x_3 wral ifmpt2x_0 nfv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 wcel ffmpt2x_0 ifmpt2x_1 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 nfcsb1v ffmpt2x_0 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb nfcsb1v nfel1 nfral ffmpt2x_4 ffmpt2x_5 wcel ffmpt2x_1 ffmpt2x_3 wral ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ffmpt2x_5 wcel ifmpt2x_1 ffmpt2x_3 wral ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 wcel ifmpt2x_1 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb wral ffmpt2x_4 ffmpt2x_5 wcel ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ffmpt2x_5 wcel ffmpt2x_1 ifmpt2x_1 ffmpt2x_3 ffmpt2x_4 ffmpt2x_5 wcel ifmpt2x_1 nfv ffmpt2x_1 ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ffmpt2x_5 ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 nfcsb1v nfel1 ffmpt2x_1 cv ifmpt2x_1 cv wceq ffmpt2x_4 ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ffmpt2x_5 ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csbeq1a eleq1d cbvral ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ffmpt2x_5 wcel ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 wcel ifmpt2x_1 ffmpt2x_3 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csbeq1a ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csb ffmpt2x_5 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_1 ifmpt2x_1 cv ffmpt2x_4 csb csbeq1a eleq1d raleqbidv syl5bb cbvral ffmpt2x_0 ffmpt2x_2 ffmpt2x_0 cv csn ffmpt2x_3 cxp ciun ifmpt2x_0 ffmpt2x_2 ifmpt2x_0 cv csn ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb cxp ciun ffmpt2x_5 ffmpt2x_6 ffmpt2x_0 ifmpt2x_0 ffmpt2x_2 ffmpt2x_0 cv csn ffmpt2x_3 cxp ifmpt2x_0 cv csn ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb cxp ifmpt2x_0 ffmpt2x_0 cv csn ffmpt2x_3 cxp nfcv ffmpt2x_0 ifmpt2x_0 cv csn ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 ifmpt2x_0 cv csn nfcv ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 nfcsb1v nfxp ffmpt2x_0 cv ifmpt2x_0 cv wceq ffmpt2x_0 cv csn ifmpt2x_0 cv csn ffmpt2x_3 ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csb ffmpt2x_0 cv ifmpt2x_0 cv sneq ffmpt2x_0 ifmpt2x_0 cv ffmpt2x_3 csbeq1a xpeq12d cbviun feq2i 3bitr4i $.
$}
$( Functionality, domain and range of a class given by the "maps to"
       notation.  (Contributed by FL, 17-May-2010.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v F $.
	$d A x y $.
	$d B x y $.
	$d D x y $.
	ffmpt2_0 $f set x $.
	ffmpt2_1 $f set y $.
	ffmpt2_2 $f class A $.
	ffmpt2_3 $f class B $.
	ffmpt2_4 $f class C $.
	ffmpt2_5 $f class D $.
	ffmpt2_6 $f class F $.
	efmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	fmpt2 $p |- ( A. x e. A A. y e. B C e. D <-> F : ( A X. B ) --> D ) $= ffmpt2_4 ffmpt2_5 wcel ffmpt2_1 ffmpt2_3 wral ffmpt2_0 ffmpt2_2 wral ffmpt2_0 ffmpt2_2 ffmpt2_0 cv csn ffmpt2_3 cxp ciun ffmpt2_5 ffmpt2_6 wf ffmpt2_2 ffmpt2_3 cxp ffmpt2_5 ffmpt2_6 wf ffmpt2_0 ffmpt2_1 ffmpt2_2 ffmpt2_3 ffmpt2_4 ffmpt2_5 ffmpt2_6 efmpt2_0 fmpt2x ffmpt2_0 ffmpt2_2 ffmpt2_0 cv csn ffmpt2_3 cxp ciun ffmpt2_2 ffmpt2_3 cxp ffmpt2_5 ffmpt2_6 ffmpt2_0 ffmpt2_2 ffmpt2_3 iunxpconst feq2i bitri $.
$}
$( Functionality and domain of a class given by the "maps to" notation.
       (Contributed by FL, 17-May-2010.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$v V $.
	$d A x y $.
	$d B x y $.
	$d x y $.
	ffnmpt2_0 $f set x $.
	ffnmpt2_1 $f set y $.
	ffnmpt2_2 $f class A $.
	ffnmpt2_3 $f class B $.
	ffnmpt2_4 $f class C $.
	ffnmpt2_5 $f class F $.
	ffnmpt2_6 $f class V $.
	efnmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	fnmpt2 $p |- ( A. x e. A A. y e. B C e. V -> F Fn ( A X. B ) ) $= ffnmpt2_4 ffnmpt2_6 wcel ffnmpt2_1 ffnmpt2_3 wral ffnmpt2_0 ffnmpt2_2 wral ffnmpt2_4 cvv wcel ffnmpt2_1 ffnmpt2_3 wral ffnmpt2_0 ffnmpt2_2 wral ffnmpt2_5 ffnmpt2_2 ffnmpt2_3 cxp wfn ffnmpt2_4 ffnmpt2_6 wcel ffnmpt2_1 ffnmpt2_3 wral ffnmpt2_4 cvv wcel ffnmpt2_1 ffnmpt2_3 wral ffnmpt2_0 ffnmpt2_2 ffnmpt2_4 ffnmpt2_6 wcel ffnmpt2_4 cvv wcel ffnmpt2_1 ffnmpt2_3 ffnmpt2_4 ffnmpt2_6 elex ralimi ralimi ffnmpt2_4 cvv wcel ffnmpt2_1 ffnmpt2_3 wral ffnmpt2_0 ffnmpt2_2 wral ffnmpt2_2 ffnmpt2_3 cxp cvv ffnmpt2_5 wf ffnmpt2_5 ffnmpt2_2 ffnmpt2_3 cxp wfn ffnmpt2_0 ffnmpt2_1 ffnmpt2_2 ffnmpt2_3 ffnmpt2_4 cvv ffnmpt2_5 efnmpt2_0 fmpt2 ffnmpt2_2 ffnmpt2_3 cxp ffnmpt2_5 dffn2 bitr4i sylib $.
$}
$( Functionality and domain of a class given by the "maps to" notation.
       (Contributed by FL, 17-May-2010.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$d A x y $.
	$d B x y $.
	$d x y $.
	ffnmpt2i_0 $f set x $.
	ffnmpt2i_1 $f set y $.
	ffnmpt2i_2 $f class A $.
	ffnmpt2i_3 $f class B $.
	ffnmpt2i_4 $f class C $.
	ffnmpt2i_5 $f class F $.
	efnmpt2i_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	efnmpt2i_1 $e |- C e. _V $.
	fnmpt2i $p |- F Fn ( A X. B ) $= ffnmpt2i_4 cvv wcel ffnmpt2i_1 ffnmpt2i_3 wral ffnmpt2i_0 ffnmpt2i_2 wral ffnmpt2i_5 ffnmpt2i_2 ffnmpt2i_3 cxp wfn ffnmpt2i_4 cvv wcel ffnmpt2i_0 ffnmpt2i_1 ffnmpt2i_2 ffnmpt2i_3 efnmpt2i_1 rgen2w ffnmpt2i_0 ffnmpt2i_1 ffnmpt2i_2 ffnmpt2i_3 ffnmpt2i_4 ffnmpt2i_5 cvv efnmpt2i_0 fnmpt2 ax-mp $.
$}
$( Domain of a class given by the "maps to" notation.  (Contributed by FL,
       17-May-2010.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$d A x y $.
	$d B x y $.
	$d x y $.
	fdmmpt2_0 $f set x $.
	fdmmpt2_1 $f set y $.
	fdmmpt2_2 $f class A $.
	fdmmpt2_3 $f class B $.
	fdmmpt2_4 $f class C $.
	fdmmpt2_5 $f class F $.
	edmmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	edmmpt2_1 $e |- C e. _V $.
	dmmpt2 $p |- dom F = ( A X. B ) $= fdmmpt2_5 fdmmpt2_2 fdmmpt2_3 cxp wfn fdmmpt2_5 cdm fdmmpt2_2 fdmmpt2_3 cxp wceq fdmmpt2_0 fdmmpt2_1 fdmmpt2_2 fdmmpt2_3 fdmmpt2_4 fdmmpt2_5 edmmpt2_0 edmmpt2_1 fnmpt2i fdmmpt2_2 fdmmpt2_3 cxp fdmmpt2_5 fndm ax-mp $.
$}
$( Existence of an operation class abstraction (version for dependent
       domains).  (Contributed by Mario Carneiro, 30-Dec-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v S $.
	$v F $.
	$d A x y $.
	$d B y $.
	fmpt2exxg_0 $f set x $.
	fmpt2exxg_1 $f set y $.
	fmpt2exxg_2 $f class A $.
	fmpt2exxg_3 $f class B $.
	fmpt2exxg_4 $f class C $.
	fmpt2exxg_5 $f class R $.
	fmpt2exxg_6 $f class S $.
	fmpt2exxg_7 $f class F $.
	empt2exxg_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	mpt2exxg $p |- ( ( A e. R /\ A. x e. A B e. S ) -> F e. _V ) $= fmpt2exxg_2 fmpt2exxg_5 wcel fmpt2exxg_3 fmpt2exxg_6 wcel fmpt2exxg_0 fmpt2exxg_2 wral wa fmpt2exxg_7 wfun fmpt2exxg_7 cdm cvv wcel fmpt2exxg_7 cvv wcel fmpt2exxg_0 fmpt2exxg_1 fmpt2exxg_2 fmpt2exxg_3 fmpt2exxg_4 fmpt2exxg_7 empt2exxg_0 mpt2fun fmpt2exxg_2 fmpt2exxg_5 wcel fmpt2exxg_3 fmpt2exxg_6 wcel fmpt2exxg_0 fmpt2exxg_2 wral wa fmpt2exxg_7 cdm fmpt2exxg_0 fmpt2exxg_2 fmpt2exxg_0 cv csn fmpt2exxg_3 cxp ciun wss fmpt2exxg_0 fmpt2exxg_2 fmpt2exxg_0 cv csn fmpt2exxg_3 cxp ciun cvv wcel fmpt2exxg_7 cdm cvv wcel fmpt2exxg_0 fmpt2exxg_1 fmpt2exxg_2 fmpt2exxg_3 fmpt2exxg_4 fmpt2exxg_7 empt2exxg_0 dmmpt2ssx fmpt2exxg_3 fmpt2exxg_6 wcel fmpt2exxg_0 fmpt2exxg_2 wral fmpt2exxg_2 fmpt2exxg_5 wcel fmpt2exxg_0 cv csn fmpt2exxg_3 cxp cvv wcel fmpt2exxg_0 fmpt2exxg_2 wral fmpt2exxg_0 fmpt2exxg_2 fmpt2exxg_0 cv csn fmpt2exxg_3 cxp ciun cvv wcel fmpt2exxg_3 fmpt2exxg_6 wcel fmpt2exxg_0 cv csn fmpt2exxg_3 cxp cvv wcel fmpt2exxg_0 fmpt2exxg_2 fmpt2exxg_0 cv csn cvv wcel fmpt2exxg_3 fmpt2exxg_6 wcel fmpt2exxg_0 cv csn fmpt2exxg_3 cxp cvv wcel fmpt2exxg_0 cv snex fmpt2exxg_0 cv csn fmpt2exxg_3 cvv fmpt2exxg_6 xpexg mpan ralimi fmpt2exxg_0 fmpt2exxg_2 fmpt2exxg_0 cv csn fmpt2exxg_3 cxp fmpt2exxg_5 cvv iunexg sylan2 fmpt2exxg_7 cdm fmpt2exxg_0 fmpt2exxg_2 fmpt2exxg_0 cv csn fmpt2exxg_3 cxp ciun cvv ssexg sylancr cvv fmpt2exxg_7 funex sylancr $.
$}
$( Existence of an operation class abstraction (special case).
       (Contributed by FL, 17-May-2010.)  (Revised by Mario Carneiro,
       1-Sep-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v S $.
	$v F $.
	$d A x y $.
	$d B y $.
	$d x B $.
	fmpt2exg_0 $f set x $.
	fmpt2exg_1 $f set y $.
	fmpt2exg_2 $f class A $.
	fmpt2exg_3 $f class B $.
	fmpt2exg_4 $f class C $.
	fmpt2exg_5 $f class R $.
	fmpt2exg_6 $f class S $.
	fmpt2exg_7 $f class F $.
	empt2exg_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	mpt2exg $p |- ( ( A e. R /\ B e. S ) -> F e. _V ) $= fmpt2exg_3 fmpt2exg_6 wcel fmpt2exg_2 fmpt2exg_5 wcel fmpt2exg_3 cvv wcel fmpt2exg_0 fmpt2exg_2 wral fmpt2exg_7 cvv wcel fmpt2exg_3 fmpt2exg_6 wcel fmpt2exg_3 cvv wcel fmpt2exg_3 cvv wcel fmpt2exg_0 fmpt2exg_2 wral fmpt2exg_3 fmpt2exg_6 elex fmpt2exg_3 cvv wcel fmpt2exg_3 cvv wcel fmpt2exg_0 fmpt2exg_2 fmpt2exg_3 cvv elex ralrimivw syl fmpt2exg_0 fmpt2exg_1 fmpt2exg_2 fmpt2exg_3 fmpt2exg_4 fmpt2exg_5 cvv fmpt2exg_7 empt2exg_0 mpt2exxg sylan2 $.
$}
$( If the domain of a function given by maps-to notation is a set, the
       function is a set.  (Contributed by NM, 12-Sep-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	$d x y A $.
	$d x y B $.
	fmpt2exga_0 $f set x $.
	fmpt2exga_1 $f set y $.
	fmpt2exga_2 $f class A $.
	fmpt2exga_3 $f class B $.
	fmpt2exga_4 $f class C $.
	fmpt2exga_5 $f class V $.
	fmpt2exga_6 $f class W $.
	mpt2exga $p |- ( ( A e. V /\ B e. W ) -> ( x e. A , y e. B |-> C ) e. _V ) $= fmpt2exga_0 fmpt2exga_1 fmpt2exga_2 fmpt2exga_3 fmpt2exga_4 fmpt2exga_5 fmpt2exga_6 fmpt2exga_0 fmpt2exga_1 fmpt2exga_2 fmpt2exga_3 fmpt2exga_4 cmpt2 fmpt2exga_0 fmpt2exga_1 fmpt2exga_2 fmpt2exga_3 fmpt2exga_4 cmpt2 eqid mpt2exg $.
$}
$( If the domain of a function given by maps-to notation is a set, the
       function is a set.  (Contributed by Mario Carneiro, 20-Dec-2013.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d y B $.
	fmpt2ex_0 $f set x $.
	fmpt2ex_1 $f set y $.
	fmpt2ex_2 $f class A $.
	fmpt2ex_3 $f class B $.
	fmpt2ex_4 $f class C $.
	empt2ex_0 $e |- A e. _V $.
	empt2ex_1 $e |- B e. _V $.
	mpt2ex $p |- ( x e. A , y e. B |-> C ) e. _V $= fmpt2ex_2 cvv wcel fmpt2ex_3 cvv wcel fmpt2ex_0 fmpt2ex_2 wral fmpt2ex_0 fmpt2ex_1 fmpt2ex_2 fmpt2ex_3 fmpt2ex_4 cmpt2 cvv wcel empt2ex_0 fmpt2ex_3 cvv wcel fmpt2ex_0 fmpt2ex_2 empt2ex_1 rgenw fmpt2ex_0 fmpt2ex_1 fmpt2ex_2 fmpt2ex_3 fmpt2ex_4 cvv cvv fmpt2ex_0 fmpt2ex_1 fmpt2ex_2 fmpt2ex_3 fmpt2ex_4 cmpt2 fmpt2ex_0 fmpt2ex_1 fmpt2ex_2 fmpt2ex_3 fmpt2ex_4 cmpt2 eqid mpt2exxg mp2an $.
$}
$( A mapping operation with empty domain.  (Contributed by Stefan O'Rear,
       29-Jan-2015.)  (Revised by Mario Carneiro, 15-May-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v B $.
	$v C $.
	$d w x z $.
	$d w y z $.
	$d w z B $.
	$d w z C $.
	impt20_0 $f set z $.
	impt20_1 $f set w $.
	fmpt20_0 $f set x $.
	fmpt20_1 $f set y $.
	fmpt20_2 $f class B $.
	fmpt20_3 $f class C $.
	mpt20 $p |- ( x e. (/) , y e. B |-> C ) = (/) $= fmpt20_0 fmpt20_1 c0 fmpt20_2 fmpt20_3 cmpt2 fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel wa impt20_0 cv fmpt20_3 wceq wa fmpt20_0 fmpt20_1 impt20_0 coprab impt20_1 cv fmpt20_0 cv fmpt20_1 cv cop impt20_0 cv cop wceq fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel wa impt20_0 cv fmpt20_3 wceq wa wa impt20_0 wex fmpt20_1 wex fmpt20_0 wex impt20_1 cab c0 fmpt20_0 fmpt20_1 impt20_0 c0 fmpt20_2 fmpt20_3 df-mpt2 fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel wa impt20_0 cv fmpt20_3 wceq wa fmpt20_0 fmpt20_1 impt20_0 impt20_1 df-oprab impt20_1 cv fmpt20_0 cv fmpt20_1 cv cop impt20_0 cv cop wceq fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel wa impt20_0 cv fmpt20_3 wceq wa wa impt20_0 wex fmpt20_1 wex fmpt20_0 wex impt20_1 impt20_1 cv fmpt20_0 cv fmpt20_1 cv cop impt20_0 cv cop wceq fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel wa impt20_0 cv fmpt20_3 wceq wa wa impt20_0 wex fmpt20_1 wex fmpt20_0 impt20_1 cv fmpt20_0 cv fmpt20_1 cv cop impt20_0 cv cop wceq fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel wa impt20_0 cv fmpt20_3 wceq wa wa impt20_0 wex fmpt20_1 impt20_1 cv fmpt20_0 cv fmpt20_1 cv cop impt20_0 cv cop wceq fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel wa impt20_0 cv fmpt20_3 wceq wa wa impt20_0 impt20_1 cv fmpt20_0 cv fmpt20_1 cv cop impt20_0 cv cop wceq fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel wa impt20_0 cv fmpt20_3 wceq wa wa fmpt20_0 cv c0 wcel fmpt20_0 cv noel impt20_1 cv fmpt20_0 cv fmpt20_1 cv cop impt20_0 cv cop wceq fmpt20_0 cv c0 wcel fmpt20_1 cv fmpt20_2 wcel impt20_0 cv fmpt20_3 wceq simprll mto nex nex nex abf 3eqtri $.
$}
$( If all the values of the mapping are subsets of a class ` X ` , then so
       is any evaluation of the mapping.  (Contributed by Mario Carneiro,
       24-Dec-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v v $.
	$v u $.
	$v A $.
	$v B $.
	$v C $.
	$v E $.
	$v F $.
	$v G $.
	$v X $.
	$d u v x y z A $.
	$d u v y z B $.
	$d u v z C $.
	$d u v x y z X $.
	iovmptss_0 $f set z $.
	iovmptss_1 $f set v $.
	iovmptss_2 $f set u $.
	fovmptss_0 $f set x $.
	fovmptss_1 $f set y $.
	fovmptss_2 $f class A $.
	fovmptss_3 $f class B $.
	fovmptss_4 $f class C $.
	fovmptss_5 $f class E $.
	fovmptss_6 $f class F $.
	fovmptss_7 $f class G $.
	fovmptss_8 $f class X $.
	eovmptss_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	ovmptss $p |- ( A. x e. A A. y e. B C C_ X -> ( E F G ) C_ X ) $= fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_8 wss iovmptss_0 fovmptss_0 fovmptss_2 fovmptss_0 cv csn fovmptss_3 cxp ciun wral fovmptss_5 fovmptss_7 cop fovmptss_6 cfv fovmptss_8 wss fovmptss_4 fovmptss_8 wss fovmptss_1 fovmptss_3 wral fovmptss_0 fovmptss_2 wral fovmptss_5 fovmptss_7 fovmptss_6 co fovmptss_8 wss iovmptss_0 fovmptss_0 fovmptss_2 fovmptss_0 cv csn fovmptss_3 cxp ciun fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_8 fovmptss_5 fovmptss_7 cop fovmptss_6 fovmptss_6 fovmptss_0 fovmptss_1 fovmptss_2 fovmptss_3 fovmptss_4 cmpt2 iovmptss_0 fovmptss_0 fovmptss_2 fovmptss_0 cv csn fovmptss_3 cxp ciun fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb cmpt eovmptss_0 fovmptss_0 fovmptss_1 iovmptss_0 fovmptss_2 fovmptss_3 fovmptss_4 mpt2mptsx eqtri fvmptss fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_8 wss iovmptss_0 iovmptss_2 fovmptss_2 iovmptss_2 cv csn fovmptss_0 iovmptss_2 cv fovmptss_3 csb cxp ciun wral fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 wss iovmptss_1 fovmptss_0 iovmptss_2 cv fovmptss_3 csb wral iovmptss_2 fovmptss_2 wral fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_8 wss iovmptss_0 fovmptss_0 fovmptss_2 fovmptss_0 cv csn fovmptss_3 cxp ciun wral fovmptss_4 fovmptss_8 wss fovmptss_1 fovmptss_3 wral fovmptss_0 fovmptss_2 wral fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_8 wss fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 wss iovmptss_0 iovmptss_2 iovmptss_1 fovmptss_2 fovmptss_0 iovmptss_2 cv fovmptss_3 csb iovmptss_0 cv iovmptss_2 cv iovmptss_1 cv cop wceq fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 iovmptss_0 cv iovmptss_2 cv iovmptss_1 cv cop wceq fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb iovmptss_0 cv iovmptss_2 cv iovmptss_1 cv cop wceq fovmptss_0 iovmptss_0 cv c1st cfv iovmptss_2 cv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb iovmptss_2 cv iovmptss_1 cv iovmptss_0 cv iovmptss_2 vex iovmptss_1 vex op1std csbeq1d iovmptss_0 cv iovmptss_2 cv iovmptss_1 cv cop wceq fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb fovmptss_1 iovmptss_1 cv fovmptss_4 csb iovmptss_0 cv iovmptss_2 cv iovmptss_1 cv cop wceq fovmptss_1 iovmptss_0 cv c2nd cfv iovmptss_1 cv fovmptss_4 iovmptss_2 cv iovmptss_1 cv iovmptss_0 cv iovmptss_2 vex iovmptss_1 vex op2ndd csbeq1d csbeq2dv eqtrd sseq1d raliunxp fovmptss_0 iovmptss_0 cv c1st cfv fovmptss_1 iovmptss_0 cv c2nd cfv fovmptss_4 csb csb fovmptss_8 wss iovmptss_0 fovmptss_0 fovmptss_2 fovmptss_0 cv csn fovmptss_3 cxp ciun iovmptss_2 fovmptss_2 iovmptss_2 cv csn fovmptss_0 iovmptss_2 cv fovmptss_3 csb cxp ciun fovmptss_0 iovmptss_2 fovmptss_2 fovmptss_0 cv csn fovmptss_3 cxp iovmptss_2 cv csn fovmptss_0 iovmptss_2 cv fovmptss_3 csb cxp iovmptss_2 fovmptss_0 cv csn fovmptss_3 cxp nfcv fovmptss_0 iovmptss_2 cv csn fovmptss_0 iovmptss_2 cv fovmptss_3 csb fovmptss_0 iovmptss_2 cv csn nfcv fovmptss_0 iovmptss_2 cv fovmptss_3 nfcsb1v nfxp fovmptss_0 cv iovmptss_2 cv wceq fovmptss_0 cv csn iovmptss_2 cv csn fovmptss_3 fovmptss_0 iovmptss_2 cv fovmptss_3 csb fovmptss_0 cv iovmptss_2 cv sneq fovmptss_0 iovmptss_2 cv fovmptss_3 csbeq1a xpeq12d cbviun raleqi fovmptss_4 fovmptss_8 wss fovmptss_1 fovmptss_3 wral fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 wss iovmptss_1 fovmptss_0 iovmptss_2 cv fovmptss_3 csb wral fovmptss_0 iovmptss_2 fovmptss_2 fovmptss_4 fovmptss_8 wss fovmptss_1 fovmptss_3 wral iovmptss_2 nfv fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 wss fovmptss_0 iovmptss_1 fovmptss_0 iovmptss_2 cv fovmptss_3 csb fovmptss_0 iovmptss_2 cv fovmptss_3 nfcsb1v fovmptss_0 fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb nfcsb1v fovmptss_0 fovmptss_8 nfcv nfss nfral fovmptss_4 fovmptss_8 wss fovmptss_1 fovmptss_3 wral fovmptss_1 iovmptss_1 cv fovmptss_4 csb fovmptss_8 wss iovmptss_1 fovmptss_3 wral fovmptss_0 cv iovmptss_2 cv wceq fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 wss iovmptss_1 fovmptss_0 iovmptss_2 cv fovmptss_3 csb wral fovmptss_4 fovmptss_8 wss fovmptss_1 iovmptss_1 cv fovmptss_4 csb fovmptss_8 wss fovmptss_1 iovmptss_1 fovmptss_3 fovmptss_4 fovmptss_8 wss iovmptss_1 nfv fovmptss_1 fovmptss_1 iovmptss_1 cv fovmptss_4 csb fovmptss_8 fovmptss_1 iovmptss_1 cv fovmptss_4 nfcsb1v fovmptss_1 fovmptss_8 nfcv nfss fovmptss_1 cv iovmptss_1 cv wceq fovmptss_4 fovmptss_1 iovmptss_1 cv fovmptss_4 csb fovmptss_8 fovmptss_1 iovmptss_1 cv fovmptss_4 csbeq1a sseq1d cbvral fovmptss_0 cv iovmptss_2 cv wceq fovmptss_1 iovmptss_1 cv fovmptss_4 csb fovmptss_8 wss fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 wss iovmptss_1 fovmptss_3 fovmptss_0 iovmptss_2 cv fovmptss_3 csb fovmptss_0 iovmptss_2 cv fovmptss_3 csbeq1a fovmptss_0 cv iovmptss_2 cv wceq fovmptss_1 iovmptss_1 cv fovmptss_4 csb fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csb fovmptss_8 fovmptss_0 iovmptss_2 cv fovmptss_1 iovmptss_1 cv fovmptss_4 csb csbeq1a sseq1d raleqbidv syl5bb cbvral 3bitr4ri fovmptss_5 fovmptss_7 fovmptss_6 co fovmptss_5 fovmptss_7 cop fovmptss_6 cfv fovmptss_8 fovmptss_5 fovmptss_7 fovmptss_6 df-ov sseq1i 3imtr4i $.
$}
$( Any function to sets of ordered pairs produces a relation on function
       value unconditionally.  (Contributed by Mario Carneiro, 9-Feb-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v F $.
	$d w x y z $.
	$d y B $.
	$d x y A $.
	frelmpt2opab_0 $f wff ph $.
	frelmpt2opab_1 $f set x $.
	frelmpt2opab_2 $f set y $.
	frelmpt2opab_3 $f set z $.
	frelmpt2opab_4 $f set w $.
	frelmpt2opab_5 $f class A $.
	frelmpt2opab_6 $f class B $.
	frelmpt2opab_7 $f class C $.
	frelmpt2opab_8 $f class D $.
	frelmpt2opab_9 $f class F $.
	erelmpt2opab_0 $e |- F = ( x e. A , y e. B |-> { <. z , w >. | ph } ) $.
	relmpt2opab $p |- Rel ( C F D ) $= frelmpt2opab_7 frelmpt2opab_8 frelmpt2opab_9 co wrel frelmpt2opab_7 frelmpt2opab_8 frelmpt2opab_9 co cvv cvv cxp wss frelmpt2opab_0 frelmpt2opab_3 frelmpt2opab_4 copab cvv cvv cxp wss frelmpt2opab_2 frelmpt2opab_6 wral frelmpt2opab_1 frelmpt2opab_5 wral frelmpt2opab_7 frelmpt2opab_8 frelmpt2opab_9 co cvv cvv cxp wss frelmpt2opab_0 frelmpt2opab_3 frelmpt2opab_4 copab cvv cvv cxp wss frelmpt2opab_2 frelmpt2opab_6 wral frelmpt2opab_1 frelmpt2opab_5 frelmpt2opab_0 frelmpt2opab_3 frelmpt2opab_4 copab cvv cvv cxp wss frelmpt2opab_2 frelmpt2opab_6 frelmpt2opab_0 frelmpt2opab_3 frelmpt2opab_4 copab wrel frelmpt2opab_0 frelmpt2opab_3 frelmpt2opab_4 copab cvv cvv cxp wss frelmpt2opab_0 frelmpt2opab_3 frelmpt2opab_4 relopab frelmpt2opab_0 frelmpt2opab_3 frelmpt2opab_4 copab df-rel mpbi rgenw rgenw frelmpt2opab_1 frelmpt2opab_2 frelmpt2opab_5 frelmpt2opab_6 frelmpt2opab_0 frelmpt2opab_3 frelmpt2opab_4 copab frelmpt2opab_7 frelmpt2opab_9 frelmpt2opab_8 cvv cvv cxp erelmpt2opab_0 ovmptss ax-mp frelmpt2opab_7 frelmpt2opab_8 frelmpt2opab_9 co df-rel mpbir $.
$}
$( Composition of two functions.  Variation of ~ fmptco when the second
       function has two arguments.  (Contributed by Mario Carneiro,
       8-Feb-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v u $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v S $.
	$v T $.
	$v F $.
	$v G $.
	$d u v w x y B $.
	$d u w x y z C $.
	$d x y ph $.
	$d u v w x y S $.
	$d u v w x y A $.
	$d u v w z R $.
	$d z T $.
	ifmpt2co_0 $f set w $.
	ifmpt2co_1 $f set v $.
	ifmpt2co_2 $f set u $.
	ffmpt2co_0 $f wff ph $.
	ffmpt2co_1 $f set x $.
	ffmpt2co_2 $f set y $.
	ffmpt2co_3 $f set z $.
	ffmpt2co_4 $f class A $.
	ffmpt2co_5 $f class B $.
	ffmpt2co_6 $f class C $.
	ffmpt2co_7 $f class R $.
	ffmpt2co_8 $f class S $.
	ffmpt2co_9 $f class T $.
	ffmpt2co_10 $f class F $.
	ffmpt2co_11 $f class G $.
	efmpt2co_0 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> R e. C ) $.
	efmpt2co_1 $e |- ( ph -> F = ( x e. A , y e. B |-> R ) ) $.
	efmpt2co_2 $e |- ( ph -> G = ( z e. C |-> S ) ) $.
	efmpt2co_3 $e |- ( z = R -> S = T ) $.
	fmpt2co $p |- ( ph -> ( G o. F ) = ( x e. A , y e. B |-> T ) ) $= ffmpt2co_0 ffmpt2co_11 ffmpt2co_10 ccom ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_3 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_8 csb cmpt ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_9 cmpt2 ffmpt2co_0 ifmpt2co_0 ffmpt2co_3 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_6 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_8 ffmpt2co_10 ffmpt2co_11 ffmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_6 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 cmpt2 wf ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_6 wcel ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp wral ffmpt2co_0 ffmpt2co_7 ffmpt2co_6 wcel ffmpt2co_2 ffmpt2co_5 wral ffmpt2co_1 ffmpt2co_4 wral ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_6 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 cmpt2 wf ffmpt2co_0 ffmpt2co_7 ffmpt2co_6 wcel ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 efmpt2co_0 ralrimivva ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 ffmpt2co_6 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 cmpt2 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 cmpt2 eqid fmpt2 sylib ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_6 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 cmpt2 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 cmpt2 ifmpt2co_2 ifmpt2co_1 ffmpt2co_4 ffmpt2co_5 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb cmpt2 ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb cmpt ffmpt2co_1 ffmpt2co_2 ifmpt2co_2 ifmpt2co_1 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ifmpt2co_2 ffmpt2co_7 nfcv ifmpt2co_1 ffmpt2co_7 nfcv ffmpt2co_1 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ffmpt2co_1 ifmpt2co_1 cv nfcv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 nfcsb1v nfcsb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb nfcsb1v ffmpt2co_1 cv ifmpt2co_2 cv wceq ffmpt2co_2 cv ifmpt2co_1 cv wceq ffmpt2co_7 ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csbeq1a ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csbeq1a sylan9eq cbvmpt2 ifmpt2co_2 ifmpt2co_1 ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb ifmpt2co_2 cv ifmpt2co_1 cv ifmpt2co_0 cv ifmpt2co_2 vex ifmpt2co_1 vex op2ndd csbeq1d ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_1 ifmpt2co_0 cv c1st cfv ifmpt2co_2 cv ffmpt2co_7 ifmpt2co_2 cv ifmpt2co_1 cv ifmpt2co_0 cv ifmpt2co_2 vex ifmpt2co_1 vex op1std csbeq1d csbeq2dv eqtrd mpt2mpt eqtr4i fmpt sylibr ffmpt2co_0 ffmpt2co_10 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 cmpt2 ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb cmpt efmpt2co_1 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 cmpt2 ifmpt2co_2 ifmpt2co_1 ffmpt2co_4 ffmpt2co_5 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb cmpt2 ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb cmpt ffmpt2co_1 ffmpt2co_2 ifmpt2co_2 ifmpt2co_1 ffmpt2co_4 ffmpt2co_5 ffmpt2co_7 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ifmpt2co_2 ffmpt2co_7 nfcv ifmpt2co_1 ffmpt2co_7 nfcv ffmpt2co_1 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ffmpt2co_1 ifmpt2co_1 cv nfcv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 nfcsb1v nfcsb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb nfcsb1v ffmpt2co_1 cv ifmpt2co_2 cv wceq ffmpt2co_2 cv ifmpt2co_1 cv wceq ffmpt2co_7 ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csbeq1a ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csbeq1a sylan9eq cbvmpt2 ifmpt2co_2 ifmpt2co_1 ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb ifmpt2co_2 cv ifmpt2co_1 cv ifmpt2co_0 cv ifmpt2co_2 vex ifmpt2co_1 vex op2ndd csbeq1d ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_1 ifmpt2co_0 cv c1st cfv ifmpt2co_2 cv ffmpt2co_7 ifmpt2co_2 cv ifmpt2co_1 cv ifmpt2co_0 cv ifmpt2co_2 vex ifmpt2co_1 vex op1std csbeq1d csbeq2dv eqtrd mpt2mpt eqtr4i syl6eq efmpt2co_2 fmptcos ffmpt2co_0 ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_3 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_8 csb cmpt ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_3 ffmpt2co_7 ffmpt2co_8 csb cmpt2 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_9 cmpt2 ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 cxp ffmpt2co_3 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_8 csb cmpt ifmpt2co_2 ifmpt2co_1 ffmpt2co_4 ffmpt2co_5 ffmpt2co_3 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_8 csb cmpt2 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_3 ffmpt2co_7 ffmpt2co_8 csb cmpt2 ifmpt2co_2 ifmpt2co_1 ifmpt2co_0 ffmpt2co_4 ffmpt2co_5 ffmpt2co_3 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_8 csb ffmpt2co_3 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_8 csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_3 ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_8 ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_0 cv c2nd cfv ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb ifmpt2co_2 cv ifmpt2co_1 cv ifmpt2co_0 cv ifmpt2co_2 vex ifmpt2co_1 vex op2ndd csbeq1d ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_0 cv c1st cfv ffmpt2co_7 csb ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ifmpt2co_0 cv ifmpt2co_2 cv ifmpt2co_1 cv cop wceq ffmpt2co_1 ifmpt2co_0 cv c1st cfv ifmpt2co_2 cv ffmpt2co_7 ifmpt2co_2 cv ifmpt2co_1 cv ifmpt2co_0 cv ifmpt2co_2 vex ifmpt2co_1 vex op1std csbeq1d csbeq2dv eqtrd csbeq1d mpt2mpt ffmpt2co_1 ffmpt2co_2 ifmpt2co_2 ifmpt2co_1 ffmpt2co_4 ffmpt2co_5 ffmpt2co_3 ffmpt2co_7 ffmpt2co_8 csb ffmpt2co_3 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_8 csb ifmpt2co_2 ffmpt2co_3 ffmpt2co_7 ffmpt2co_8 csb nfcv ifmpt2co_1 ffmpt2co_3 ffmpt2co_7 ffmpt2co_8 csb nfcv ffmpt2co_1 ffmpt2co_3 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_8 ffmpt2co_1 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ffmpt2co_1 ifmpt2co_1 cv nfcv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 nfcsb1v nfcsb ffmpt2co_1 ffmpt2co_8 nfcv nfcsb ffmpt2co_2 ffmpt2co_3 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_8 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb nfcsb1v ffmpt2co_2 ffmpt2co_8 nfcv nfcsb ffmpt2co_1 cv ifmpt2co_2 cv wceq ffmpt2co_2 cv ifmpt2co_1 cv wceq wa ffmpt2co_3 ffmpt2co_7 ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_8 ffmpt2co_1 cv ifmpt2co_2 cv wceq ffmpt2co_2 cv ifmpt2co_1 cv wceq ffmpt2co_7 ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csb ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csbeq1a ffmpt2co_2 ifmpt2co_1 cv ffmpt2co_1 ifmpt2co_2 cv ffmpt2co_7 csb csbeq1a sylan9eq csbeq1d cbvmpt2 eqtr4i ffmpt2co_0 ffmpt2co_1 ffmpt2co_2 ffmpt2co_4 ffmpt2co_5 ffmpt2co_3 ffmpt2co_7 ffmpt2co_8 csb ffmpt2co_9 ffmpt2co_0 ffmpt2co_1 cv ffmpt2co_4 wcel ffmpt2co_2 cv ffmpt2co_5 wcel w3a ffmpt2co_7 ffmpt2co_6 wcel ffmpt2co_3 ffmpt2co_7 ffmpt2co_8 csb ffmpt2co_9 wceq ffmpt2co_0 ffmpt2co_1 cv ffmpt2co_4 wcel ffmpt2co_2 cv ffmpt2co_5 wcel ffmpt2co_7 ffmpt2co_6 wcel efmpt2co_0 3impb ffmpt2co_3 ffmpt2co_7 ffmpt2co_8 ffmpt2co_9 ffmpt2co_6 ffmpt2co_7 ffmpt2co_6 wcel ffmpt2co_3 ffmpt2co_9 nfcvd efmpt2co_3 csbiegf syl mpt2eq3dva syl5eq eqtrd $.
$}
$( Composition of a function with an operator abstraction.  (Contributed by
       Jeff Madsen, 2-Sep-2009.)  (Proof shortened by Mario Carneiro,
       26-Sep-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v F $.
	$v G $.
	$v H $.
	$d x y z A $.
	$d x y z B $.
	$d x y z D $.
	$d x y z H $.
	$d z C $.
	ioprabco_0 $f set z $.
	foprabco_0 $f set x $.
	foprabco_1 $f set y $.
	foprabco_2 $f class A $.
	foprabco_3 $f class B $.
	foprabco_4 $f class C $.
	foprabco_5 $f class D $.
	foprabco_6 $f class F $.
	foprabco_7 $f class G $.
	foprabco_8 $f class H $.
	eoprabco_0 $e |- ( ( x e. A /\ y e. B ) -> C e. D ) $.
	eoprabco_1 $e |- F = ( x e. A , y e. B |-> C ) $.
	eoprabco_2 $e |- G = ( x e. A , y e. B |-> ( H ` C ) ) $.
	oprabco $p |- ( H Fn D -> G = ( H o. F ) ) $= foprabco_8 foprabco_5 wfn foprabco_8 foprabco_6 ccom foprabco_0 foprabco_1 foprabco_2 foprabco_3 foprabco_4 foprabco_8 cfv cmpt2 foprabco_7 foprabco_8 foprabco_5 wfn foprabco_0 foprabco_1 ioprabco_0 foprabco_2 foprabco_3 foprabco_5 foprabco_4 ioprabco_0 cv foprabco_8 cfv foprabco_4 foprabco_8 cfv foprabco_6 foprabco_8 foprabco_0 cv foprabco_2 wcel foprabco_1 cv foprabco_3 wcel wa foprabco_4 foprabco_5 wcel foprabco_8 foprabco_5 wfn eoprabco_0 adantl foprabco_6 foprabco_0 foprabco_1 foprabco_2 foprabco_3 foprabco_4 cmpt2 wceq foprabco_8 foprabco_5 wfn eoprabco_1 a1i foprabco_8 foprabco_5 wfn foprabco_8 ioprabco_0 foprabco_5 ioprabco_0 cv foprabco_8 cfv cmpt wceq ioprabco_0 foprabco_5 foprabco_8 dffn5 biimpi ioprabco_0 cv foprabco_4 foprabco_8 fveq2 fmpt2co eoprabco_2 syl6reqr $.
$}
$( Composition of operator abstractions.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by David Abernethy, 23-Apr-2013.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	$v F $.
	$v G $.
	$v M $.
	$d x y A $.
	$d x y B $.
	$d x y M $.
	$d x y R $.
	$d x y S $.
	foprab2co_0 $f set x $.
	foprab2co_1 $f set y $.
	foprab2co_2 $f class A $.
	foprab2co_3 $f class B $.
	foprab2co_4 $f class C $.
	foprab2co_5 $f class D $.
	foprab2co_6 $f class R $.
	foprab2co_7 $f class S $.
	foprab2co_8 $f class F $.
	foprab2co_9 $f class G $.
	foprab2co_10 $f class M $.
	eoprab2co_0 $e |- ( ( x e. A /\ y e. B ) -> C e. R ) $.
	eoprab2co_1 $e |- ( ( x e. A /\ y e. B ) -> D e. S ) $.
	eoprab2co_2 $e |- F = ( x e. A , y e. B |-> <. C , D >. ) $.
	eoprab2co_3 $e |- G = ( x e. A , y e. B |-> ( C M D ) ) $.
	oprab2co $p |- ( M Fn ( R X. S ) -> G = ( M o. F ) ) $= foprab2co_0 foprab2co_1 foprab2co_2 foprab2co_3 foprab2co_4 foprab2co_5 cop foprab2co_6 foprab2co_7 cxp foprab2co_8 foprab2co_9 foprab2co_10 foprab2co_0 cv foprab2co_2 wcel foprab2co_1 cv foprab2co_3 wcel wa foprab2co_4 foprab2co_6 wcel foprab2co_5 foprab2co_7 wcel foprab2co_4 foprab2co_5 cop foprab2co_6 foprab2co_7 cxp wcel eoprab2co_0 eoprab2co_1 foprab2co_4 foprab2co_5 foprab2co_6 foprab2co_7 opelxpi syl2anc eoprab2co_2 foprab2co_9 foprab2co_0 foprab2co_1 foprab2co_2 foprab2co_3 foprab2co_4 foprab2co_5 foprab2co_10 co cmpt2 foprab2co_0 foprab2co_1 foprab2co_2 foprab2co_3 foprab2co_4 foprab2co_5 cop foprab2co_10 cfv cmpt2 eoprab2co_3 foprab2co_0 foprab2co_1 foprab2co_2 foprab2co_3 foprab2co_4 foprab2co_5 foprab2co_10 co foprab2co_4 foprab2co_5 cop foprab2co_10 cfv foprab2co_4 foprab2co_5 foprab2co_10 co foprab2co_4 foprab2co_5 cop foprab2co_10 cfv wceq foprab2co_0 cv foprab2co_2 wcel foprab2co_1 cv foprab2co_3 wcel wa foprab2co_4 foprab2co_5 foprab2co_10 df-ov a1i mpt2eq3ia eqtri oprabco $.
$}
$( An alternate possible definition of the ` 1st ` function.  (Contributed
       by NM, 14-Oct-2004.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y z $.
	idf1st2_0 $f set w $.
	fdf1st2_0 $f set x $.
	fdf1st2_1 $f set y $.
	fdf1st2_2 $f set z $.
	df1st2 $p |- { <. <. x , y >. , z >. | z = x } = ( 1st |` ( _V X. _V ) ) $= c1st cvv cvv cxp cres fdf1st2_2 cv idf1st2_0 cv c1st cfv wceq idf1st2_0 fdf1st2_2 copab cvv cvv cxp cres idf1st2_0 cv cvv cvv cxp wcel fdf1st2_2 cv idf1st2_0 cv c1st cfv wceq wa idf1st2_0 fdf1st2_2 copab fdf1st2_2 cv fdf1st2_0 cv wceq fdf1st2_0 fdf1st2_1 fdf1st2_2 coprab c1st fdf1st2_2 cv idf1st2_0 cv c1st cfv wceq idf1st2_0 fdf1st2_2 copab cvv cvv cxp c1st idf1st2_0 cvv idf1st2_0 cv c1st cfv cmpt fdf1st2_2 cv idf1st2_0 cv c1st cfv wceq idf1st2_0 fdf1st2_2 copab c1st cvv wfn c1st idf1st2_0 cvv idf1st2_0 cv c1st cfv cmpt wceq cvv cvv c1st wfo c1st cvv wfn fo1st cvv cvv c1st fofn ax-mp idf1st2_0 cvv c1st dffn5 mpbi idf1st2_0 fdf1st2_2 idf1st2_0 cv c1st cfv mptv eqtri reseq1i fdf1st2_2 cv idf1st2_0 cv c1st cfv wceq idf1st2_0 fdf1st2_2 cvv cvv cxp resopab fdf1st2_2 cv idf1st2_0 cv c1st cfv wceq fdf1st2_2 cv fdf1st2_0 cv wceq fdf1st2_0 fdf1st2_1 fdf1st2_2 idf1st2_0 idf1st2_0 cv fdf1st2_0 cv fdf1st2_1 cv cop wceq idf1st2_0 cv c1st cfv fdf1st2_0 cv fdf1st2_2 cv fdf1st2_0 cv fdf1st2_1 cv idf1st2_0 cv fdf1st2_0 vex fdf1st2_1 vex op1std eqeq2d dfoprab3 3eqtrri $.
$}
$( An alternate possible definition of the ` 2nd ` function.  (Contributed
       by NM, 10-Aug-2006.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y z $.
	idf2nd2_0 $f set w $.
	fdf2nd2_0 $f set x $.
	fdf2nd2_1 $f set y $.
	fdf2nd2_2 $f set z $.
	df2nd2 $p |- { <. <. x , y >. , z >. | z = y } = ( 2nd |` ( _V X. _V ) ) $= c2nd cvv cvv cxp cres fdf2nd2_2 cv idf2nd2_0 cv c2nd cfv wceq idf2nd2_0 fdf2nd2_2 copab cvv cvv cxp cres idf2nd2_0 cv cvv cvv cxp wcel fdf2nd2_2 cv idf2nd2_0 cv c2nd cfv wceq wa idf2nd2_0 fdf2nd2_2 copab fdf2nd2_2 cv fdf2nd2_1 cv wceq fdf2nd2_0 fdf2nd2_1 fdf2nd2_2 coprab c2nd fdf2nd2_2 cv idf2nd2_0 cv c2nd cfv wceq idf2nd2_0 fdf2nd2_2 copab cvv cvv cxp c2nd idf2nd2_0 cvv idf2nd2_0 cv c2nd cfv cmpt fdf2nd2_2 cv idf2nd2_0 cv c2nd cfv wceq idf2nd2_0 fdf2nd2_2 copab c2nd cvv wfn c2nd idf2nd2_0 cvv idf2nd2_0 cv c2nd cfv cmpt wceq cvv cvv c2nd wfo c2nd cvv wfn fo2nd cvv cvv c2nd fofn ax-mp idf2nd2_0 cvv c2nd dffn5 mpbi idf2nd2_0 fdf2nd2_2 idf2nd2_0 cv c2nd cfv mptv eqtri reseq1i fdf2nd2_2 cv idf2nd2_0 cv c2nd cfv wceq idf2nd2_0 fdf2nd2_2 cvv cvv cxp resopab fdf2nd2_2 cv idf2nd2_0 cv c2nd cfv wceq fdf2nd2_2 cv fdf2nd2_1 cv wceq fdf2nd2_0 fdf2nd2_1 fdf2nd2_2 idf2nd2_0 idf2nd2_0 cv fdf2nd2_0 cv fdf2nd2_1 cv cop wceq idf2nd2_0 cv c2nd cfv fdf2nd2_1 cv fdf2nd2_2 cv fdf2nd2_0 cv fdf2nd2_1 cv idf2nd2_0 cv fdf2nd2_0 vex fdf2nd2_1 vex op2ndd eqeq2d dfoprab3 3eqtrri $.
$}
$( The mapping of a restriction of the ` 1st ` function to a constant
       function.  (Contributed by NM, 14-Dec-2008.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$d x y A $.
	$d x y B $.
	$d x y V $.
	i1stconst_0 $f set x $.
	i1stconst_1 $f set y $.
	f1stconst_0 $f class A $.
	f1stconst_1 $f class B $.
	f1stconst_2 $f class V $.
	1stconst $p |- ( B e. V -> ( 1st |` ( A X. { B } ) ) : ( A X. { B } ) -1-1-onto-> A ) $= f1stconst_1 f1stconst_2 wcel f1stconst_0 f1stconst_1 csn cxp f1stconst_0 c1st f1stconst_0 f1stconst_1 csn cxp cres wfo c1st f1stconst_0 f1stconst_1 csn cxp cres ccnv wfun f1stconst_0 f1stconst_1 csn cxp f1stconst_0 c1st f1stconst_0 f1stconst_1 csn cxp cres wf1o f1stconst_1 f1stconst_2 wcel f1stconst_1 csn c0 wne f1stconst_0 f1stconst_1 csn cxp f1stconst_0 c1st f1stconst_0 f1stconst_1 csn cxp cres wfo f1stconst_1 f1stconst_2 snnzg f1stconst_0 f1stconst_1 csn fo1stres syl f1stconst_1 f1stconst_2 wcel i1stconst_0 cv i1stconst_1 cv c1st f1stconst_0 f1stconst_1 csn cxp cres wbr i1stconst_0 wmo i1stconst_1 wal c1st f1stconst_0 f1stconst_1 csn cxp cres ccnv wfun f1stconst_1 f1stconst_2 wcel i1stconst_0 cv i1stconst_1 cv c1st f1stconst_0 f1stconst_1 csn cxp cres wbr i1stconst_0 wmo i1stconst_1 f1stconst_1 f1stconst_2 wcel i1stconst_0 cv i1stconst_1 cv c1st f1stconst_0 f1stconst_1 csn cxp cres wbr i1stconst_0 wmo i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa i1stconst_0 wmo i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq i1stconst_1 cv f1stconst_0 wcel i1stconst_0 i1stconst_0 i1stconst_1 cv f1stconst_1 cop moeq moani f1stconst_1 f1stconst_2 wcel i1stconst_0 cv i1stconst_1 cv c1st f1stconst_0 f1stconst_1 csn cxp cres wbr i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa i1stconst_0 i1stconst_0 cv i1stconst_1 cv c1st f1stconst_0 f1stconst_1 csn cxp cres wbr i1stconst_0 cv i1stconst_1 cv c1st wbr i1stconst_0 cv f1stconst_0 f1stconst_1 csn cxp wcel wa f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa i1stconst_0 cv i1stconst_1 cv c1st f1stconst_0 f1stconst_1 csn cxp i1stconst_1 vex brres i1stconst_0 cv i1stconst_1 cv c1st wbr i1stconst_0 cv f1stconst_0 f1stconst_1 csn cxp wcel wa i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv f1stconst_0 f1stconst_1 csn cxp wcel wa f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv i1stconst_1 cv c1st wbr i1stconst_0 cv f1stconst_0 f1stconst_1 csn cxp wcel c1st cvv wfn i1stconst_0 cv cvv wcel i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv i1stconst_1 cv c1st wbr wb cvv cvv c1st wfo c1st cvv wfn fo1st cvv cvv c1st fofn ax-mp i1stconst_0 vex cvv i1stconst_0 cv i1stconst_1 cv c1st fnbrfvb mp2an anbi1i f1stconst_1 f1stconst_2 wcel i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv f1stconst_0 f1stconst_1 csn cxp wcel wa i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv f1stconst_0 f1stconst_1 csn cxp wcel wa i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa f1stconst_1 f1stconst_2 wcel i1stconst_0 cv f1stconst_0 f1stconst_1 csn cxp wcel i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv cvv cvv cxp wcel i1stconst_0 cv c1st cfv f1stconst_0 wcel i1stconst_0 cv c2nd cfv f1stconst_1 csn wcel wa wa i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa i1stconst_0 cv f1stconst_0 f1stconst_1 csn elxp7 i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv cvv cvv cxp wcel i1stconst_0 cv c1st cfv f1stconst_0 wcel i1stconst_0 cv c2nd cfv f1stconst_1 csn wcel wa wa wa i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv c1st cfv f1stconst_0 wcel i1stconst_0 cv c2nd cfv f1stconst_1 csn wcel wa i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv cvv cvv cxp wcel i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv c1st cfv f1stconst_0 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv c2nd cfv f1stconst_1 csn wcel i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv c1st cfv f1stconst_0 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv c1st cfv i1stconst_1 cv f1stconst_0 eleq1 biimpa adantrr adantrl i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv cvv cvv cxp wcel i1stconst_0 cv c2nd cfv f1stconst_1 csn wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq i1stconst_0 cv c1st cfv f1stconst_0 wcel i1stconst_0 cv c2nd cfv f1stconst_1 csn wcel i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv cvv cvv cxp wcel i1stconst_0 cv c2nd cfv f1stconst_1 wceq i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq i1stconst_0 cv c2nd cfv f1stconst_1 elsni i1stconst_0 cv cvv cvv cxp wcel i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv c2nd cfv f1stconst_1 wceq i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq i1stconst_0 cv i1stconst_1 cv f1stconst_1 cvv cvv eqopi an12s sylanr2 adantrrl jca sylan2b adantl f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa wa i1stconst_0 cv c1st cfv i1stconst_1 cv wceq i1stconst_0 cv f1stconst_0 f1stconst_1 csn cxp wcel f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa wa i1stconst_0 cv c1st cfv i1stconst_1 cv f1stconst_1 cop c1st cfv i1stconst_1 cv f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa wa i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop c1st f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq simprr fveq2d f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa wa i1stconst_1 cv f1stconst_0 wcel f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_1 cop c1st cfv i1stconst_1 cv wceq f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq simprl f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa simpl i1stconst_1 cv f1stconst_1 f1stconst_0 f1stconst_2 op1stg syl2anc eqtrd f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa wa i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop f1stconst_0 f1stconst_1 csn cxp f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq simprr f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa wa i1stconst_1 cv f1stconst_0 wcel f1stconst_1 f1stconst_1 csn wcel i1stconst_1 cv f1stconst_1 cop f1stconst_0 f1stconst_1 csn cxp wcel f1stconst_1 f1stconst_2 wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq simprl f1stconst_1 f1stconst_2 wcel f1stconst_1 f1stconst_1 csn wcel i1stconst_1 cv f1stconst_0 wcel i1stconst_0 cv i1stconst_1 cv f1stconst_1 cop wceq wa f1stconst_1 f1stconst_2 snidg adantr i1stconst_1 cv f1stconst_1 f1stconst_0 f1stconst_1 csn opelxpi syl2anc eqeltrd jca impbida syl5bbr syl5bb mobidv mpbiri alrimiv i1stconst_0 i1stconst_1 c1st f1stconst_0 f1stconst_1 csn cxp cres funcnv2 sylibr f1stconst_0 f1stconst_1 csn cxp f1stconst_0 c1st f1stconst_0 f1stconst_1 csn cxp cres dff1o3 sylanbrc $.
$}
$( The mapping of a restriction of the ` 2nd ` function to a converse
       constant function.  (Contributed by NM, 27-Mar-2008.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$d x y A $.
	$d x y B $.
	$d x y V $.
	i2ndconst_0 $f set x $.
	i2ndconst_1 $f set y $.
	f2ndconst_0 $f class A $.
	f2ndconst_1 $f class B $.
	f2ndconst_2 $f class V $.
	2ndconst $p |- ( A e. V -> ( 2nd |` ( { A } X. B ) ) : ( { A } X. B ) -1-1-onto-> B ) $= f2ndconst_0 f2ndconst_2 wcel f2ndconst_0 csn f2ndconst_1 cxp f2ndconst_1 c2nd f2ndconst_0 csn f2ndconst_1 cxp cres wfo c2nd f2ndconst_0 csn f2ndconst_1 cxp cres ccnv wfun f2ndconst_0 csn f2ndconst_1 cxp f2ndconst_1 c2nd f2ndconst_0 csn f2ndconst_1 cxp cres wf1o f2ndconst_0 f2ndconst_2 wcel f2ndconst_0 csn c0 wne f2ndconst_0 csn f2ndconst_1 cxp f2ndconst_1 c2nd f2ndconst_0 csn f2ndconst_1 cxp cres wfo f2ndconst_0 f2ndconst_2 snnzg f2ndconst_0 csn f2ndconst_1 fo2ndres syl f2ndconst_0 f2ndconst_2 wcel i2ndconst_0 cv i2ndconst_1 cv c2nd f2ndconst_0 csn f2ndconst_1 cxp cres wbr i2ndconst_0 wmo i2ndconst_1 wal c2nd f2ndconst_0 csn f2ndconst_1 cxp cres ccnv wfun f2ndconst_0 f2ndconst_2 wcel i2ndconst_0 cv i2ndconst_1 cv c2nd f2ndconst_0 csn f2ndconst_1 cxp cres wbr i2ndconst_0 wmo i2ndconst_1 f2ndconst_0 f2ndconst_2 wcel i2ndconst_0 cv i2ndconst_1 cv c2nd f2ndconst_0 csn f2ndconst_1 cxp cres wbr i2ndconst_0 wmo i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa i2ndconst_0 wmo i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 i2ndconst_0 f2ndconst_0 i2ndconst_1 cv cop moeq moani f2ndconst_0 f2ndconst_2 wcel i2ndconst_0 cv i2ndconst_1 cv c2nd f2ndconst_0 csn f2ndconst_1 cxp cres wbr i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa i2ndconst_0 i2ndconst_0 cv i2ndconst_1 cv c2nd f2ndconst_0 csn f2ndconst_1 cxp cres wbr i2ndconst_0 cv i2ndconst_1 cv c2nd wbr i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 cxp wcel wa f2ndconst_0 f2ndconst_2 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa i2ndconst_0 cv i2ndconst_1 cv c2nd f2ndconst_0 csn f2ndconst_1 cxp i2ndconst_1 vex brres i2ndconst_0 cv i2ndconst_1 cv c2nd wbr i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 cxp wcel wa i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 cxp wcel wa f2ndconst_0 f2ndconst_2 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv i2ndconst_1 cv c2nd wbr i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 cxp wcel c2nd cvv wfn i2ndconst_0 cv cvv wcel i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv i2ndconst_1 cv c2nd wbr wb cvv cvv c2nd wfo c2nd cvv wfn fo2nd cvv cvv c2nd fofn ax-mp i2ndconst_0 vex cvv i2ndconst_0 cv i2ndconst_1 cv c2nd fnbrfvb mp2an anbi1i f2ndconst_0 f2ndconst_2 wcel i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 cxp wcel wa i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 cxp wcel wa i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa f2ndconst_0 f2ndconst_2 wcel i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 cxp wcel i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv cvv cvv cxp wcel i2ndconst_0 cv c1st cfv f2ndconst_0 csn wcel i2ndconst_0 cv c2nd cfv f2ndconst_1 wcel wa wa i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 elxp7 i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv cvv cvv cxp wcel i2ndconst_0 cv c1st cfv f2ndconst_0 csn wcel i2ndconst_0 cv c2nd cfv f2ndconst_1 wcel wa wa wa i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv c1st cfv f2ndconst_0 csn wcel i2ndconst_0 cv c2nd cfv f2ndconst_1 wcel wa i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv cvv cvv cxp wcel i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv c2nd cfv f2ndconst_1 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv c1st cfv f2ndconst_0 csn wcel i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv c2nd cfv f2ndconst_1 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv c2nd cfv i2ndconst_1 cv f2ndconst_1 eleq1 biimpa adantrl adantrl i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv cvv cvv cxp wcel i2ndconst_0 cv c1st cfv f2ndconst_0 csn wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq i2ndconst_0 cv c2nd cfv f2ndconst_1 wcel i2ndconst_0 cv c1st cfv f2ndconst_0 csn wcel i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv cvv cvv cxp wcel i2ndconst_0 cv c1st cfv f2ndconst_0 wceq i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq i2ndconst_0 cv c1st cfv f2ndconst_0 elsni i2ndconst_0 cv cvv cvv cxp wcel i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv c1st cfv f2ndconst_0 wceq i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq i2ndconst_0 cv cvv cvv cxp wcel i2ndconst_0 cv c1st cfv f2ndconst_0 wceq i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cvv cvv eqopi ancom2s an12s sylanr2 adantrrr jca sylan2b adantl f2ndconst_0 f2ndconst_2 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa wa i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_0 cv f2ndconst_0 csn f2ndconst_1 cxp wcel f2ndconst_0 f2ndconst_2 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq i2ndconst_0 cv c2nd cfv i2ndconst_1 cv wceq i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq f2ndconst_0 f2ndconst_2 wcel i2ndconst_0 cv c2nd cfv f2ndconst_0 i2ndconst_1 cv cop c2nd cfv i2ndconst_1 cv i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop c2nd fveq2 f2ndconst_0 f2ndconst_2 wcel i2ndconst_1 cv cvv wcel f2ndconst_0 i2ndconst_1 cv cop c2nd cfv i2ndconst_1 cv wceq i2ndconst_1 vex f2ndconst_0 i2ndconst_1 cv f2ndconst_2 cvv op2ndg mpan2 sylan9eqr adantrl f2ndconst_0 f2ndconst_2 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa wa i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop f2ndconst_0 csn f2ndconst_1 cxp f2ndconst_0 f2ndconst_2 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq simprr f2ndconst_0 f2ndconst_2 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa wa f2ndconst_0 f2ndconst_0 csn wcel i2ndconst_1 cv f2ndconst_1 wcel f2ndconst_0 i2ndconst_1 cv cop f2ndconst_0 csn f2ndconst_1 cxp wcel f2ndconst_0 f2ndconst_2 wcel f2ndconst_0 f2ndconst_0 csn wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq wa f2ndconst_0 f2ndconst_2 snidg adantr f2ndconst_0 f2ndconst_2 wcel i2ndconst_1 cv f2ndconst_1 wcel i2ndconst_0 cv f2ndconst_0 i2ndconst_1 cv cop wceq simprl f2ndconst_0 i2ndconst_1 cv f2ndconst_0 csn f2ndconst_1 opelxpi syl2anc eqeltrd jca impbida syl5bbr syl5bb mobidv mpbiri alrimiv i2ndconst_0 i2ndconst_1 c2nd f2ndconst_0 csn f2ndconst_1 cxp cres funcnv2 sylibr f2ndconst_0 csn f2ndconst_1 cxp f2ndconst_1 c2nd f2ndconst_0 csn f2ndconst_1 cxp cres dff1o3 sylanbrc $.
$}
$( Alternate definition for the "maps to" notation ~ df-mpt2 (although it
       requires that ` C ` be a set).  (Contributed by NM, 19-Dec-2008.)
       (Revised by Mario Carneiro, 31-Aug-2015.) $)
${
	$v x $.
	$v y $.
	$v w $.
	$v A $.
	$v B $.
	$v C $.
	$d w x y A $.
	$d w x y B $.
	$d w C $.
	idfmpt2_0 $f set w $.
	fdfmpt2_0 $f set x $.
	fdfmpt2_1 $f set y $.
	fdfmpt2_2 $f class A $.
	fdfmpt2_3 $f class B $.
	fdfmpt2_4 $f class C $.
	edfmpt2_0 $e |- C e. _V $.
	dfmpt2 $p |- ( x e. A , y e. B |-> C ) = U_ x e. A U_ y e. B { <. <. x , y >. , C >. } $= fdfmpt2_0 fdfmpt2_1 fdfmpt2_2 fdfmpt2_3 fdfmpt2_4 cmpt2 idfmpt2_0 fdfmpt2_2 fdfmpt2_3 cxp fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb cmpt idfmpt2_0 fdfmpt2_2 fdfmpt2_3 cxp idfmpt2_0 cv fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb cop csn ciun fdfmpt2_0 fdfmpt2_2 fdfmpt2_1 fdfmpt2_3 fdfmpt2_0 cv fdfmpt2_1 cv cop fdfmpt2_4 cop csn ciun ciun fdfmpt2_0 fdfmpt2_1 idfmpt2_0 fdfmpt2_2 fdfmpt2_3 fdfmpt2_4 mpt2mpts idfmpt2_0 fdfmpt2_2 fdfmpt2_3 cxp fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb idfmpt2_0 cv c1st fvex fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 idfmpt2_0 cv c2nd fvex edfmpt2_0 csbex csbex dfmpt idfmpt2_0 fdfmpt2_0 fdfmpt2_1 fdfmpt2_2 fdfmpt2_3 idfmpt2_0 cv fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb cop csn fdfmpt2_0 cv fdfmpt2_1 cv cop fdfmpt2_4 cop csn fdfmpt2_0 idfmpt2_0 cv fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb cop fdfmpt2_0 idfmpt2_0 cv fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb fdfmpt2_0 idfmpt2_0 cv nfcv fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb nfcsb1v nfop nfsn fdfmpt2_1 idfmpt2_0 cv fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb cop fdfmpt2_1 idfmpt2_0 cv fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb fdfmpt2_1 idfmpt2_0 cv nfcv fdfmpt2_1 fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb fdfmpt2_1 idfmpt2_0 cv c1st cfv nfcv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 nfcsb1v nfcsb nfop nfsn idfmpt2_0 fdfmpt2_0 cv fdfmpt2_1 cv cop fdfmpt2_4 cop csn nfcv idfmpt2_0 cv fdfmpt2_0 cv fdfmpt2_1 cv cop wceq idfmpt2_0 cv fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb cop fdfmpt2_0 cv fdfmpt2_1 cv cop fdfmpt2_4 cop idfmpt2_0 cv fdfmpt2_0 cv fdfmpt2_1 cv cop wceq idfmpt2_0 cv fdfmpt2_0 cv fdfmpt2_1 cv cop fdfmpt2_0 idfmpt2_0 cv c1st cfv fdfmpt2_1 idfmpt2_0 cv c2nd cfv fdfmpt2_4 csb csb fdfmpt2_4 idfmpt2_0 cv fdfmpt2_0 cv fdfmpt2_1 cv cop wceq id fdfmpt2_0 fdfmpt2_1 idfmpt2_0 cv fdfmpt2_4 csbopeq1a opeq12d sneqd iunxpf 3eqtri $.
$}
$( Composition with ` ``' ( 2nd |`` ( { C } X. _V ) ) ` turns any binary
       operation ` F ` with a constant first operand into a function ` G ` of
       the second operand only.  This transformation is called "currying."
       (Contributed by NM, 28-Mar-2008.)  (Revised by Mario Carneiro,
       26-Dec-2014.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$v G $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x F $.
	$d x G $.
	fcurry1_0 $f set x $.
	fcurry1_1 $f class A $.
	fcurry1_2 $f class B $.
	fcurry1_3 $f class C $.
	fcurry1_4 $f class F $.
	fcurry1_5 $f class G $.
	ecurry1_0 $e |- G = ( F o. `' ( 2nd |` ( { C } X. _V ) ) ) $.
	curry1 $p |- ( ( F Fn ( A X. B ) /\ C e. A ) -> G = ( x e. B |-> ( C F x ) ) ) $= fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_5 fcurry1_0 fcurry1_2 fcurry1_0 cv fcurry1_5 cfv cmpt fcurry1_0 fcurry1_2 fcurry1_3 fcurry1_0 cv fcurry1_4 co cmpt fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_5 fcurry1_2 wfn fcurry1_5 fcurry1_0 fcurry1_2 fcurry1_0 cv fcurry1_5 cfv cmpt wceq fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom wfun fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom cdm fcurry1_2 wceq fcurry1_5 fcurry1_2 wfn fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_4 wfun c2nd fcurry1_3 csn cvv cxp cres ccnv wfun fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom wfun fcurry1_3 fcurry1_1 wcel fcurry1_1 fcurry1_2 cxp fcurry1_4 fnfun fcurry1_3 fcurry1_1 wcel fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres wf1o c2nd fcurry1_3 csn cvv cxp cres ccnv wfun fcurry1_3 cvv fcurry1_1 2ndconst fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres wf1o fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres wfo c2nd fcurry1_3 csn cvv cxp cres ccnv wfun fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres dff1o3 simprbi syl fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv funco syl2an fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom cdm c2nd fcurry1_3 csn cvv cxp cres ccnv ccnv fcurry1_4 cdm cima fcurry1_2 fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv dmco fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa c2nd fcurry1_3 csn cvv cxp cres ccnv ccnv fcurry1_4 cdm cima c2nd fcurry1_3 csn cvv cxp cres ccnv ccnv fcurry1_1 fcurry1_2 cxp cima fcurry1_2 fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_4 cdm fcurry1_1 fcurry1_2 cxp c2nd fcurry1_3 csn cvv cxp cres ccnv ccnv fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_4 cdm fcurry1_1 fcurry1_2 cxp wceq fcurry1_3 fcurry1_1 wcel fcurry1_1 fcurry1_2 cxp fcurry1_4 fndm adantr imaeq2d fcurry1_3 fcurry1_1 wcel c2nd fcurry1_3 csn cvv cxp cres ccnv ccnv fcurry1_1 fcurry1_2 cxp cima fcurry1_2 wceq fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel c2nd fcurry1_3 csn cvv cxp cres ccnv ccnv fcurry1_1 fcurry1_2 cxp cima c2nd fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp cin cres crn fcurry1_2 c2nd fcurry1_3 csn cvv cxp cres ccnv ccnv fcurry1_1 fcurry1_2 cxp cima c2nd fcurry1_3 csn cvv cxp cres fcurry1_1 fcurry1_2 cxp cima c2nd fcurry1_3 csn cvv cxp cres fcurry1_1 fcurry1_2 cxp cres crn c2nd fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp cin cres crn c2nd fcurry1_3 csn cvv cxp cres fcurry1_1 fcurry1_2 cxp imacnvcnv c2nd fcurry1_3 csn cvv cxp cres fcurry1_1 fcurry1_2 cxp df-ima c2nd fcurry1_3 csn cvv cxp cres fcurry1_1 fcurry1_2 cxp cres c2nd fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp cin cres c2nd fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp resres rneqi 3eqtri fcurry1_3 fcurry1_1 wcel c2nd fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp cin cres crn c2nd fcurry1_3 csn fcurry1_2 cxp cres crn fcurry1_2 fcurry1_3 fcurry1_1 wcel c2nd fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp cin cres c2nd fcurry1_3 csn fcurry1_2 cxp cres fcurry1_3 fcurry1_1 wcel fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp cin fcurry1_3 csn fcurry1_2 cxp c2nd fcurry1_3 fcurry1_1 wcel fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp cin fcurry1_3 csn fcurry1_1 cin fcurry1_2 cxp fcurry1_3 csn fcurry1_2 cxp fcurry1_3 csn cvv cxp fcurry1_1 fcurry1_2 cxp cin fcurry1_3 csn fcurry1_1 cin cvv fcurry1_2 cin cxp fcurry1_3 csn fcurry1_1 cin fcurry1_2 cxp fcurry1_3 csn cvv fcurry1_1 fcurry1_2 inxp cvv fcurry1_2 cin fcurry1_2 fcurry1_3 csn fcurry1_1 cin cvv fcurry1_2 cin fcurry1_2 cvv cin fcurry1_2 cvv fcurry1_2 incom fcurry1_2 inv1 eqtri xpeq2i eqtri fcurry1_3 fcurry1_1 wcel fcurry1_3 csn fcurry1_1 cin fcurry1_3 csn fcurry1_2 fcurry1_3 fcurry1_1 wcel fcurry1_3 csn fcurry1_1 wss fcurry1_3 csn fcurry1_1 cin fcurry1_3 csn wceq fcurry1_3 fcurry1_1 snssi fcurry1_3 csn fcurry1_1 df-ss sylib xpeq1d syl5eq reseq2d rneqd fcurry1_3 fcurry1_1 wcel fcurry1_3 csn fcurry1_2 cxp fcurry1_2 c2nd fcurry1_3 csn fcurry1_2 cxp cres wf1o fcurry1_3 csn fcurry1_2 cxp fcurry1_2 c2nd fcurry1_3 csn fcurry1_2 cxp cres wfo c2nd fcurry1_3 csn fcurry1_2 cxp cres crn fcurry1_2 wceq fcurry1_3 fcurry1_2 fcurry1_1 2ndconst fcurry1_3 csn fcurry1_2 cxp fcurry1_2 c2nd fcurry1_3 csn fcurry1_2 cxp cres f1ofo fcurry1_3 csn fcurry1_2 cxp fcurry1_2 c2nd fcurry1_3 csn fcurry1_2 cxp cres forn 3syl eqtrd syl5eq adantl eqtrd syl5eq fcurry1_5 fcurry1_2 wfn fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom fcurry1_2 wfn fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom wfun fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom cdm fcurry1_2 wceq wa fcurry1_2 fcurry1_5 fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom ecurry1_0 fneq1i fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom fcurry1_2 df-fn bitri sylanbrc fcurry1_0 fcurry1_2 fcurry1_5 dffn5 sylib fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_0 fcurry1_2 fcurry1_0 cv fcurry1_5 cfv fcurry1_3 fcurry1_0 cv fcurry1_4 co fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_0 cv fcurry1_2 wcel wa fcurry1_0 cv fcurry1_5 cfv fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_4 cfv fcurry1_3 fcurry1_0 cv fcurry1_4 co fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_0 cv fcurry1_2 wcel wa fcurry1_0 cv fcurry1_5 cfv fcurry1_0 cv fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom cfv fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_4 cfv fcurry1_0 cv fcurry1_5 fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom ecurry1_0 fveq1i fcurry1_3 fcurry1_1 wcel fcurry1_0 cv fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom cfv fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_4 cfv wceq fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_0 cv fcurry1_2 wcel fcurry1_3 fcurry1_1 wcel c2nd fcurry1_3 csn cvv cxp cres ccnv cvv wfn fcurry1_0 cv fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom cfv fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_4 cfv wceq fcurry1_3 fcurry1_1 wcel c2nd fcurry1_3 csn cvv cxp cres fcurry1_3 csn cvv cxp wfn c2nd fcurry1_3 csn cvv cxp cres ccnv cvv wfn fcurry1_3 fcurry1_1 wcel fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres wf1o c2nd fcurry1_3 csn cvv cxp cres fcurry1_3 csn cvv cxp wfn c2nd fcurry1_3 csn cvv cxp cres ccnv cvv wfn wa fcurry1_3 cvv fcurry1_1 2ndconst fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres dff1o4 sylib simprd c2nd fcurry1_3 csn cvv cxp cres ccnv cvv wfn fcurry1_0 cv cvv wcel fcurry1_0 cv fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv ccom cfv fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_4 cfv wceq fcurry1_0 vex cvv fcurry1_4 c2nd fcurry1_3 csn cvv cxp cres ccnv fcurry1_0 cv fvco2 mpan2 syl ad2antlr syl5eq fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel wa fcurry1_0 cv fcurry1_2 wcel wa fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_4 cfv fcurry1_3 fcurry1_0 cv cop fcurry1_4 cfv fcurry1_3 fcurry1_0 cv fcurry1_4 co fcurry1_3 fcurry1_1 wcel fcurry1_0 cv fcurry1_2 wcel fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_4 cfv fcurry1_3 fcurry1_0 cv cop fcurry1_4 cfv wceq fcurry1_4 fcurry1_1 fcurry1_2 cxp wfn fcurry1_3 fcurry1_1 wcel fcurry1_0 cv fcurry1_2 wcel wa fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_3 fcurry1_0 cv cop fcurry1_4 fcurry1_3 fcurry1_1 wcel fcurry1_0 cv fcurry1_2 wcel wa fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres wf1o fcurry1_3 fcurry1_0 cv cop fcurry1_3 csn cvv cxp wcel wa fcurry1_3 fcurry1_0 cv cop c2nd fcurry1_3 csn cvv cxp cres cfv fcurry1_0 cv wceq fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres ccnv cfv fcurry1_3 fcurry1_0 cv cop wceq fcurry1_3 fcurry1_1 wcel fcurry1_0 cv fcurry1_2 wcel wa fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres wf1o fcurry1_3 fcurry1_0 cv cop fcurry1_3 csn cvv cxp wcel fcurry1_3 fcurry1_1 wcel fcurry1_3 csn cvv cxp cvv c2nd fcurry1_3 csn cvv cxp cres wf1o fcurry1_0 cv fcurry1_2 wcel fcurry1_3 cvv fcurry1_1 2ndconst adantr fcurry1_3 fcurry1_1 wcel fcurry1_3 fcurry1_0 cv cop fcurry1_3 csn cvv cxp wcel fcurry1_0 cv fcurry1_2 wcel fcurry1_3 fcurry1_1 wcel fcurry1_3 fcurry1_3 csn wcel fcurry1_0 cv cvv wcel wa fcurry1_3 fcurry1_0 cv cop fcurry1_3 csn cvv cxp wcel fcurry1_3 fcurry1_1 wcel fcurry1_3 fcurry1_3 csn wcel fcurry1_0 cv cvv wcel fcurry1_3 fcurry1_1 snidg fcurry1_0 vex jctir fcurry1_3 fcurry1_0 cv fcurry1_3 csn cvv opelxp sylibr adantr jca fcurry1_3 fcurry1_1 wcel fcurry1_3 fcurry1_0 cv cop c2nd fcurry1_3 csn cvv cxp cres cfv fcurry1_0 cv wceq fcurry1_0 cv fcurry1_2 wcel fcurry1_3 fcurry1_1 wcel fcurry1_3 fcurry1_0 cv cop c2nd fcurry1_3 csn cvv cxp cres cfv fcurry1_3 fcurry1_0 cv cop c2nd cfv fcurry1_0 cv fcurry1_3 fcurry1_1 wcel fcurry1_3 fcurry1_0 cv cop fcurry1_3 csn cvv cxp wcel fcurry1_3 fcurry1_0 cv cop c2nd fcurry1_3 csn cvv cxp cres cfv fcurry1_3 fcurry1_0 cv cop c2nd cfv wceq fcurry1_3 fcurry1_1 wcel fcurry1_3 fcurry1_3 csn wcel fcurry1_0 cv cvv wcel wa fcurry1_3 fcurry1_0 cv cop fcurry1_3 csn cvv cxp wcel fcurry1_3 fcurry1_1 wcel fcurry1_3 fcurry1_3 csn wcel fcurry1_0 cv cvv wcel fcurry1_3 fcurry1_1 snidg fcurry1_0 vex jctir fcurry1_3 fcurry1_0 cv fcurry1_3 csn cvv opelxp sylibr fcurry1_3 fcurry1_0 cv cop fcurry1_3 csn cvv cxp c2nd fvres syl fcurry1_3 fcurry1_1 wcel fcurry1_0 cv cvv wcel fcurry1_3 fcurry1_0 cv cop c2nd cfv fcurry1_0 cv wceq fcurry1_0 vex fcurry1_3 fcurry1_0 cv fcurry1_1 cvv op2ndg mpan2 eqtrd adantr fcurry1_3 csn cvv cxp cvv fcurry1_3 fcurry1_0 cv cop fcurry1_0 cv c2nd fcurry1_3 csn cvv cxp cres f1ocnvfv sylc fveq2d adantll fcurry1_3 fcurry1_0 cv fcurry1_4 df-ov syl6eqr eqtrd mpteq2dva eqtrd $.
$}
$( The value of a curried function with a constant first argument.
       (Contributed by NM, 28-Mar-2008.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v F $.
	$v G $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	$d x F $.
	$d x G $.
	icurry1val_0 $f set x $.
	fcurry1val_0 $f class A $.
	fcurry1val_1 $f class B $.
	fcurry1val_2 $f class C $.
	fcurry1val_3 $f class D $.
	fcurry1val_4 $f class F $.
	fcurry1val_5 $f class G $.
	ecurry1val_0 $e |- G = ( F o. `' ( 2nd |` ( { C } X. _V ) ) ) $.
	curry1val $p |- ( ( F Fn ( A X. B ) /\ C e. A ) -> ( G ` D ) = ( C F D ) ) $= fcurry1val_4 fcurry1val_0 fcurry1val_1 cxp wfn fcurry1val_2 fcurry1val_0 wcel wa fcurry1val_3 fcurry1val_5 cfv fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cfv fcurry1val_2 fcurry1val_3 fcurry1val_4 co fcurry1val_4 fcurry1val_0 fcurry1val_1 cxp wfn fcurry1val_2 fcurry1val_0 wcel wa fcurry1val_3 fcurry1val_5 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt icurry1val_0 fcurry1val_0 fcurry1val_1 fcurry1val_2 fcurry1val_4 fcurry1val_5 ecurry1val_0 curry1 fveq1d fcurry1val_4 fcurry1val_0 fcurry1val_1 cxp wfn fcurry1val_2 fcurry1val_0 wcel wa fcurry1val_3 fcurry1val_1 wcel fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cfv fcurry1val_2 fcurry1val_3 fcurry1val_4 co wceq fcurry1val_4 fcurry1val_0 fcurry1val_1 cxp wfn fcurry1val_2 fcurry1val_0 wcel wa fcurry1val_3 fcurry1val_1 wcel wn fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cfv fcurry1val_2 fcurry1val_3 fcurry1val_4 co wceq fcurry1val_4 fcurry1val_0 fcurry1val_1 cxp wfn fcurry1val_2 fcurry1val_0 wcel wa fcurry1val_3 fcurry1val_1 wcel wn wa fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cfv c0 fcurry1val_2 fcurry1val_3 fcurry1val_4 co fcurry1val_3 fcurry1val_1 wcel wn fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cfv c0 wceq fcurry1val_4 fcurry1val_0 fcurry1val_1 cxp wfn fcurry1val_2 fcurry1val_0 wcel wa fcurry1val_3 fcurry1val_1 wcel wn fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cdm wcel wn fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cfv c0 wceq fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cdm wcel fcurry1val_3 fcurry1val_1 wcel icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt cdm fcurry1val_1 fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt eqid dmmptss sseli con3i fcurry1val_3 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt ndmfv syl adantl fcurry1val_4 fcurry1val_0 fcurry1val_1 cxp wfn fcurry1val_2 fcurry1val_0 wcel wa fcurry1val_4 cdm fcurry1val_0 fcurry1val_1 cxp wceq fcurry1val_2 fcurry1val_0 wcel fcurry1val_3 fcurry1val_1 wcel wa wn fcurry1val_2 fcurry1val_3 fcurry1val_4 co c0 wceq fcurry1val_3 fcurry1val_1 wcel wn fcurry1val_4 fcurry1val_0 fcurry1val_1 cxp wfn fcurry1val_4 cdm fcurry1val_0 fcurry1val_1 cxp wceq fcurry1val_2 fcurry1val_0 wcel fcurry1val_0 fcurry1val_1 cxp fcurry1val_4 fndm adantr fcurry1val_2 fcurry1val_0 wcel fcurry1val_3 fcurry1val_1 wcel wa fcurry1val_3 fcurry1val_1 wcel fcurry1val_2 fcurry1val_0 wcel fcurry1val_3 fcurry1val_1 wcel simpr con3i fcurry1val_2 fcurry1val_3 fcurry1val_0 fcurry1val_1 fcurry1val_4 ndmovg syl2an eqtr4d ex icurry1val_0 fcurry1val_3 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co fcurry1val_2 fcurry1val_3 fcurry1val_4 co fcurry1val_1 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt icurry1val_0 cv fcurry1val_3 fcurry1val_2 fcurry1val_4 oveq2 icurry1val_0 fcurry1val_1 fcurry1val_2 icurry1val_0 cv fcurry1val_4 co cmpt eqid fcurry1val_2 fcurry1val_3 fcurry1val_4 ovex fvmpt pm2.61d2 eqtrd $.
$}
$( Functionality of a curried function with a constant first argument.
       (Contributed by NM, 29-Mar-2008.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v F $.
	$v G $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	$d x F $.
	$d x G $.
	icurry1f_0 $f set x $.
	fcurry1f_0 $f class A $.
	fcurry1f_1 $f class B $.
	fcurry1f_2 $f class C $.
	fcurry1f_3 $f class D $.
	fcurry1f_4 $f class F $.
	fcurry1f_5 $f class G $.
	ecurry1f_0 $e |- G = ( F o. `' ( 2nd |` ( { C } X. _V ) ) ) $.
	curry1f $p |- ( ( F : ( A X. B ) --> D /\ C e. A ) -> G : B --> D ) $= fcurry1f_0 fcurry1f_1 cxp fcurry1f_3 fcurry1f_4 wf fcurry1f_2 fcurry1f_0 wcel wa fcurry1f_1 fcurry1f_3 fcurry1f_5 wf fcurry1f_1 fcurry1f_3 icurry1f_0 fcurry1f_1 fcurry1f_2 icurry1f_0 cv fcurry1f_4 co cmpt wf fcurry1f_0 fcurry1f_1 cxp fcurry1f_3 fcurry1f_4 wf fcurry1f_2 fcurry1f_0 wcel wa icurry1f_0 fcurry1f_1 fcurry1f_2 icurry1f_0 cv fcurry1f_4 co fcurry1f_3 icurry1f_0 fcurry1f_1 fcurry1f_2 icurry1f_0 cv fcurry1f_4 co cmpt fcurry1f_0 fcurry1f_1 cxp fcurry1f_3 fcurry1f_4 wf fcurry1f_2 fcurry1f_0 wcel icurry1f_0 cv fcurry1f_1 wcel fcurry1f_2 icurry1f_0 cv fcurry1f_4 co fcurry1f_3 wcel fcurry1f_2 icurry1f_0 cv fcurry1f_3 fcurry1f_0 fcurry1f_1 fcurry1f_4 fovrn 3expa icurry1f_0 fcurry1f_1 fcurry1f_2 icurry1f_0 cv fcurry1f_4 co cmpt eqid fmptd fcurry1f_0 fcurry1f_1 cxp fcurry1f_3 fcurry1f_4 wf fcurry1f_2 fcurry1f_0 wcel wa fcurry1f_1 fcurry1f_3 fcurry1f_5 icurry1f_0 fcurry1f_1 fcurry1f_2 icurry1f_0 cv fcurry1f_4 co cmpt fcurry1f_0 fcurry1f_1 cxp fcurry1f_3 fcurry1f_4 wf fcurry1f_4 fcurry1f_0 fcurry1f_1 cxp wfn fcurry1f_2 fcurry1f_0 wcel fcurry1f_5 icurry1f_0 fcurry1f_1 fcurry1f_2 icurry1f_0 cv fcurry1f_4 co cmpt wceq fcurry1f_0 fcurry1f_1 cxp fcurry1f_3 fcurry1f_4 ffn icurry1f_0 fcurry1f_0 fcurry1f_1 fcurry1f_2 fcurry1f_4 fcurry1f_5 ecurry1f_0 curry1 sylan feq1d mpbird $.
$}
$( Composition with ` ``' ( 1st |`` ( _V X. { C } ) ) ` turns any binary
       operation ` F ` with a constant second operand into a function ` G ` of
       the first operand only.  This transformation is called "currying."  (If
       this becomes frequently used, we can introduce a new notation for the
       hypothesis.)  (Contributed by NM, 16-Dec-2008.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$v G $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x F $.
	$d x G $.
	fcurry2_0 $f set x $.
	fcurry2_1 $f class A $.
	fcurry2_2 $f class B $.
	fcurry2_3 $f class C $.
	fcurry2_4 $f class F $.
	fcurry2_5 $f class G $.
	ecurry2_0 $e |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) ) $.
	curry2 $p |- ( ( F Fn ( A X. B ) /\ C e. B ) -> G = ( x e. A |-> ( x F C ) ) ) $= fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_5 fcurry2_0 fcurry2_1 fcurry2_0 cv fcurry2_5 cfv cmpt fcurry2_0 fcurry2_1 fcurry2_0 cv fcurry2_3 fcurry2_4 co cmpt fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_5 fcurry2_1 wfn fcurry2_5 fcurry2_0 fcurry2_1 fcurry2_0 cv fcurry2_5 cfv cmpt wceq fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom wfun fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom cdm fcurry2_1 wceq fcurry2_5 fcurry2_1 wfn fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_4 wfun c1st cvv fcurry2_3 csn cxp cres ccnv wfun fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom wfun fcurry2_3 fcurry2_2 wcel fcurry2_1 fcurry2_2 cxp fcurry2_4 fnfun fcurry2_3 fcurry2_2 wcel cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres wf1o c1st cvv fcurry2_3 csn cxp cres ccnv wfun cvv fcurry2_3 fcurry2_2 1stconst cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres wf1o cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres wfo c1st cvv fcurry2_3 csn cxp cres ccnv wfun cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres dff1o3 simprbi syl fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv funco syl2an fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom cdm c1st cvv fcurry2_3 csn cxp cres ccnv ccnv fcurry2_4 cdm cima fcurry2_1 fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv dmco fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa c1st cvv fcurry2_3 csn cxp cres ccnv ccnv fcurry2_4 cdm cima c1st cvv fcurry2_3 csn cxp cres ccnv ccnv fcurry2_1 fcurry2_2 cxp cima fcurry2_1 fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_4 cdm fcurry2_1 fcurry2_2 cxp c1st cvv fcurry2_3 csn cxp cres ccnv ccnv fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_4 cdm fcurry2_1 fcurry2_2 cxp wceq fcurry2_3 fcurry2_2 wcel fcurry2_1 fcurry2_2 cxp fcurry2_4 fndm adantr imaeq2d fcurry2_3 fcurry2_2 wcel c1st cvv fcurry2_3 csn cxp cres ccnv ccnv fcurry2_1 fcurry2_2 cxp cima fcurry2_1 wceq fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel c1st cvv fcurry2_3 csn cxp cres ccnv ccnv fcurry2_1 fcurry2_2 cxp cima c1st cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp cin cres crn fcurry2_1 c1st cvv fcurry2_3 csn cxp cres ccnv ccnv fcurry2_1 fcurry2_2 cxp cima c1st cvv fcurry2_3 csn cxp cres fcurry2_1 fcurry2_2 cxp cima c1st cvv fcurry2_3 csn cxp cres fcurry2_1 fcurry2_2 cxp cres crn c1st cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp cin cres crn c1st cvv fcurry2_3 csn cxp cres fcurry2_1 fcurry2_2 cxp imacnvcnv c1st cvv fcurry2_3 csn cxp cres fcurry2_1 fcurry2_2 cxp df-ima c1st cvv fcurry2_3 csn cxp cres fcurry2_1 fcurry2_2 cxp cres c1st cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp cin cres c1st cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp resres rneqi 3eqtri fcurry2_3 fcurry2_2 wcel c1st cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp cin cres crn c1st fcurry2_1 fcurry2_3 csn cxp cres crn fcurry2_1 fcurry2_3 fcurry2_2 wcel c1st cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp cin cres c1st fcurry2_1 fcurry2_3 csn cxp cres fcurry2_3 fcurry2_2 wcel cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp cin fcurry2_1 fcurry2_3 csn cxp c1st fcurry2_3 fcurry2_2 wcel cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp cin fcurry2_1 fcurry2_3 csn fcurry2_2 cin cxp fcurry2_1 fcurry2_3 csn cxp cvv fcurry2_3 csn cxp fcurry2_1 fcurry2_2 cxp cin cvv fcurry2_1 cin fcurry2_3 csn fcurry2_2 cin cxp fcurry2_1 fcurry2_3 csn fcurry2_2 cin cxp cvv fcurry2_3 csn fcurry2_1 fcurry2_2 inxp cvv fcurry2_1 cin fcurry2_1 fcurry2_3 csn fcurry2_2 cin cvv fcurry2_1 cin fcurry2_1 cvv cin fcurry2_1 cvv fcurry2_1 incom fcurry2_1 inv1 eqtri xpeq1i eqtri fcurry2_3 fcurry2_2 wcel fcurry2_3 csn fcurry2_2 cin fcurry2_3 csn fcurry2_1 fcurry2_3 fcurry2_2 wcel fcurry2_3 csn fcurry2_2 wss fcurry2_3 csn fcurry2_2 cin fcurry2_3 csn wceq fcurry2_3 fcurry2_2 snssi fcurry2_3 csn fcurry2_2 df-ss sylib xpeq2d syl5eq reseq2d rneqd fcurry2_3 fcurry2_2 wcel fcurry2_1 fcurry2_3 csn cxp fcurry2_1 c1st fcurry2_1 fcurry2_3 csn cxp cres wf1o fcurry2_1 fcurry2_3 csn cxp fcurry2_1 c1st fcurry2_1 fcurry2_3 csn cxp cres wfo c1st fcurry2_1 fcurry2_3 csn cxp cres crn fcurry2_1 wceq fcurry2_1 fcurry2_3 fcurry2_2 1stconst fcurry2_1 fcurry2_3 csn cxp fcurry2_1 c1st fcurry2_1 fcurry2_3 csn cxp cres f1ofo fcurry2_1 fcurry2_3 csn cxp fcurry2_1 c1st fcurry2_1 fcurry2_3 csn cxp cres forn 3syl eqtrd syl5eq adantl eqtrd syl5eq fcurry2_5 fcurry2_1 wfn fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom fcurry2_1 wfn fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom wfun fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom cdm fcurry2_1 wceq wa fcurry2_1 fcurry2_5 fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom ecurry2_0 fneq1i fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom fcurry2_1 df-fn bitri sylanbrc fcurry2_0 fcurry2_1 fcurry2_5 dffn5 sylib fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_0 fcurry2_1 fcurry2_0 cv fcurry2_5 cfv fcurry2_0 cv fcurry2_3 fcurry2_4 co fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_0 cv fcurry2_1 wcel wa fcurry2_0 cv fcurry2_5 cfv fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres ccnv cfv fcurry2_4 cfv fcurry2_0 cv fcurry2_3 fcurry2_4 co fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_0 cv fcurry2_1 wcel wa fcurry2_0 cv fcurry2_5 cfv fcurry2_0 cv fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom cfv fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres ccnv cfv fcurry2_4 cfv fcurry2_0 cv fcurry2_5 fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom ecurry2_0 fveq1i fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom cfv fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres ccnv cfv fcurry2_4 cfv wceq fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_0 cv fcurry2_1 wcel fcurry2_3 fcurry2_2 wcel c1st cvv fcurry2_3 csn cxp cres ccnv cvv wfn fcurry2_0 cv cvv wcel fcurry2_0 cv fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv ccom cfv fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres ccnv cfv fcurry2_4 cfv wceq fcurry2_3 fcurry2_2 wcel c1st cvv fcurry2_3 csn cxp cres cvv fcurry2_3 csn cxp wfn c1st cvv fcurry2_3 csn cxp cres ccnv cvv wfn fcurry2_3 fcurry2_2 wcel cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres wf1o c1st cvv fcurry2_3 csn cxp cres cvv fcurry2_3 csn cxp wfn c1st cvv fcurry2_3 csn cxp cres ccnv cvv wfn wa cvv fcurry2_3 fcurry2_2 1stconst cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres dff1o4 sylib simprd fcurry2_0 vex cvv fcurry2_4 c1st cvv fcurry2_3 csn cxp cres ccnv fcurry2_0 cv fvco2 sylancl ad2antlr syl5eq fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel wa fcurry2_0 cv fcurry2_1 wcel wa fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres ccnv cfv fcurry2_4 cfv fcurry2_0 cv fcurry2_3 cop fcurry2_4 cfv fcurry2_0 cv fcurry2_3 fcurry2_4 co fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_1 wcel fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres ccnv cfv fcurry2_4 cfv fcurry2_0 cv fcurry2_3 cop fcurry2_4 cfv wceq fcurry2_4 fcurry2_1 fcurry2_2 cxp wfn fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_1 wcel wa fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres ccnv cfv fcurry2_0 cv fcurry2_3 cop fcurry2_4 fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_1 wcel wa cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres wf1o fcurry2_0 cv fcurry2_3 cop cvv fcurry2_3 csn cxp wcel wa fcurry2_0 cv fcurry2_3 cop c1st cvv fcurry2_3 csn cxp cres cfv fcurry2_0 cv wceq fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres ccnv cfv fcurry2_0 cv fcurry2_3 cop wceq fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_1 wcel wa cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres wf1o fcurry2_0 cv fcurry2_3 cop cvv fcurry2_3 csn cxp wcel fcurry2_3 fcurry2_2 wcel cvv fcurry2_3 csn cxp cvv c1st cvv fcurry2_3 csn cxp cres wf1o fcurry2_0 cv fcurry2_1 wcel cvv fcurry2_3 fcurry2_2 1stconst adantr fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_1 wcel wa fcurry2_0 cv cvv wcel fcurry2_3 fcurry2_3 csn wcel fcurry2_0 cv fcurry2_3 cop cvv fcurry2_3 csn cxp wcel fcurry2_0 cv cvv wcel fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_1 wcel wa fcurry2_0 vex a1i fcurry2_3 fcurry2_2 wcel fcurry2_3 fcurry2_3 csn wcel fcurry2_0 cv fcurry2_1 wcel fcurry2_3 fcurry2_2 snidg adantr fcurry2_0 cv fcurry2_3 cvv fcurry2_3 csn opelxp sylanbrc jca fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_1 wcel wa fcurry2_0 cv fcurry2_3 cop c1st cvv fcurry2_3 csn cxp cres cfv fcurry2_0 cv fcurry2_3 cop c1st cfv fcurry2_0 cv fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_3 cop c1st cvv fcurry2_3 csn cxp cres cfv fcurry2_0 cv fcurry2_3 cop c1st cfv wceq fcurry2_0 cv fcurry2_1 wcel fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_3 cop cvv fcurry2_3 csn cxp wcel fcurry2_0 cv fcurry2_3 cop c1st cvv fcurry2_3 csn cxp cres cfv fcurry2_0 cv fcurry2_3 cop c1st cfv wceq fcurry2_3 fcurry2_2 wcel fcurry2_0 cv cvv wcel fcurry2_3 fcurry2_3 csn wcel fcurry2_0 cv fcurry2_3 cop cvv fcurry2_3 csn cxp wcel fcurry2_0 cv cvv wcel fcurry2_3 fcurry2_2 wcel fcurry2_0 vex a1i fcurry2_3 fcurry2_2 snidg fcurry2_0 cv fcurry2_3 cvv fcurry2_3 csn opelxp sylanbrc fcurry2_0 cv fcurry2_3 cop cvv fcurry2_3 csn cxp c1st fvres syl adantr fcurry2_0 cv fcurry2_1 wcel fcurry2_3 fcurry2_2 wcel fcurry2_0 cv fcurry2_3 cop c1st cfv fcurry2_0 cv wceq fcurry2_0 cv fcurry2_3 fcurry2_1 fcurry2_2 op1stg ancoms eqtrd cvv fcurry2_3 csn cxp cvv fcurry2_0 cv fcurry2_3 cop fcurry2_0 cv c1st cvv fcurry2_3 csn cxp cres f1ocnvfv sylc fveq2d adantll fcurry2_0 cv fcurry2_3 fcurry2_4 df-ov syl6eqr eqtrd mpteq2dva eqtrd $.
$}
$( Functionality of a curried function with a constant second argument.
       (Contributed by NM, 16-Dec-2008.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v F $.
	$v G $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	$d x F $.
	$d x G $.
	icurry2f_0 $f set x $.
	fcurry2f_0 $f class A $.
	fcurry2f_1 $f class B $.
	fcurry2f_2 $f class C $.
	fcurry2f_3 $f class D $.
	fcurry2f_4 $f class F $.
	fcurry2f_5 $f class G $.
	ecurry2f_0 $e |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) ) $.
	curry2f $p |- ( ( F : ( A X. B ) --> D /\ C e. B ) -> G : A --> D ) $= fcurry2f_0 fcurry2f_1 cxp fcurry2f_3 fcurry2f_4 wf fcurry2f_2 fcurry2f_1 wcel wa fcurry2f_0 fcurry2f_3 fcurry2f_5 wf fcurry2f_0 fcurry2f_3 icurry2f_0 fcurry2f_0 icurry2f_0 cv fcurry2f_2 fcurry2f_4 co cmpt wf fcurry2f_0 fcurry2f_1 cxp fcurry2f_3 fcurry2f_4 wf fcurry2f_2 fcurry2f_1 wcel wa icurry2f_0 fcurry2f_0 icurry2f_0 cv fcurry2f_2 fcurry2f_4 co fcurry2f_3 icurry2f_0 fcurry2f_0 icurry2f_0 cv fcurry2f_2 fcurry2f_4 co cmpt fcurry2f_0 fcurry2f_1 cxp fcurry2f_3 fcurry2f_4 wf fcurry2f_2 fcurry2f_1 wcel icurry2f_0 cv fcurry2f_0 wcel icurry2f_0 cv fcurry2f_2 fcurry2f_4 co fcurry2f_3 wcel fcurry2f_0 fcurry2f_1 cxp fcurry2f_3 fcurry2f_4 wf icurry2f_0 cv fcurry2f_0 wcel fcurry2f_2 fcurry2f_1 wcel icurry2f_0 cv fcurry2f_2 fcurry2f_4 co fcurry2f_3 wcel icurry2f_0 cv fcurry2f_2 fcurry2f_3 fcurry2f_0 fcurry2f_1 fcurry2f_4 fovrn 3com23 3expa icurry2f_0 fcurry2f_0 icurry2f_0 cv fcurry2f_2 fcurry2f_4 co cmpt eqid fmptd fcurry2f_0 fcurry2f_1 cxp fcurry2f_3 fcurry2f_4 wf fcurry2f_2 fcurry2f_1 wcel wa fcurry2f_0 fcurry2f_3 fcurry2f_5 icurry2f_0 fcurry2f_0 icurry2f_0 cv fcurry2f_2 fcurry2f_4 co cmpt fcurry2f_0 fcurry2f_1 cxp fcurry2f_3 fcurry2f_4 wf fcurry2f_4 fcurry2f_0 fcurry2f_1 cxp wfn fcurry2f_2 fcurry2f_1 wcel fcurry2f_5 icurry2f_0 fcurry2f_0 icurry2f_0 cv fcurry2f_2 fcurry2f_4 co cmpt wceq fcurry2f_0 fcurry2f_1 cxp fcurry2f_3 fcurry2f_4 ffn icurry2f_0 fcurry2f_0 fcurry2f_1 fcurry2f_2 fcurry2f_4 fcurry2f_5 ecurry2f_0 curry2 sylan feq1d mpbird $.
$}
$( The value of a curried function with a constant second argument.
       (Contributed by NM, 16-Dec-2008.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v F $.
	$v G $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	$d x F $.
	$d x G $.
	icurry2val_0 $f set x $.
	fcurry2val_0 $f class A $.
	fcurry2val_1 $f class B $.
	fcurry2val_2 $f class C $.
	fcurry2val_3 $f class D $.
	fcurry2val_4 $f class F $.
	fcurry2val_5 $f class G $.
	ecurry2val_0 $e |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) ) $.
	curry2val $p |- ( ( F Fn ( A X. B ) /\ C e. B ) -> ( G ` D ) = ( D F C ) ) $= fcurry2val_4 fcurry2val_0 fcurry2val_1 cxp wfn fcurry2val_2 fcurry2val_1 wcel wa fcurry2val_3 fcurry2val_5 cfv fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cfv fcurry2val_3 fcurry2val_2 fcurry2val_4 co fcurry2val_4 fcurry2val_0 fcurry2val_1 cxp wfn fcurry2val_2 fcurry2val_1 wcel wa fcurry2val_3 fcurry2val_5 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt icurry2val_0 fcurry2val_0 fcurry2val_1 fcurry2val_2 fcurry2val_4 fcurry2val_5 ecurry2val_0 curry2 fveq1d fcurry2val_4 fcurry2val_0 fcurry2val_1 cxp wfn fcurry2val_2 fcurry2val_1 wcel wa fcurry2val_3 fcurry2val_0 wcel fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cfv fcurry2val_3 fcurry2val_2 fcurry2val_4 co wceq fcurry2val_4 fcurry2val_0 fcurry2val_1 cxp wfn fcurry2val_3 fcurry2val_0 wcel wn fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cfv fcurry2val_3 fcurry2val_2 fcurry2val_4 co wceq wi fcurry2val_2 fcurry2val_1 wcel fcurry2val_4 fcurry2val_0 fcurry2val_1 cxp wfn fcurry2val_3 fcurry2val_0 wcel wn fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cfv fcurry2val_3 fcurry2val_2 fcurry2val_4 co wceq fcurry2val_4 fcurry2val_0 fcurry2val_1 cxp wfn fcurry2val_3 fcurry2val_0 wcel wn wa fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cfv c0 fcurry2val_3 fcurry2val_2 fcurry2val_4 co fcurry2val_3 fcurry2val_0 wcel wn fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cfv c0 wceq fcurry2val_4 fcurry2val_0 fcurry2val_1 cxp wfn fcurry2val_3 fcurry2val_0 wcel wn fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cdm wcel wn fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cfv c0 wceq fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cdm wcel fcurry2val_3 fcurry2val_0 wcel icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt cdm fcurry2val_0 fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt eqid dmmptss sseli con3i fcurry2val_3 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt ndmfv syl adantl fcurry2val_4 fcurry2val_0 fcurry2val_1 cxp wfn fcurry2val_4 cdm fcurry2val_0 fcurry2val_1 cxp wceq fcurry2val_3 fcurry2val_0 wcel fcurry2val_2 fcurry2val_1 wcel wa wn fcurry2val_3 fcurry2val_2 fcurry2val_4 co c0 wceq fcurry2val_3 fcurry2val_0 wcel wn fcurry2val_0 fcurry2val_1 cxp fcurry2val_4 fndm fcurry2val_3 fcurry2val_0 wcel fcurry2val_2 fcurry2val_1 wcel wa fcurry2val_3 fcurry2val_0 wcel fcurry2val_3 fcurry2val_0 wcel fcurry2val_2 fcurry2val_1 wcel simpl con3i fcurry2val_3 fcurry2val_2 fcurry2val_0 fcurry2val_1 fcurry2val_4 ndmovg syl2an eqtr4d ex adantr icurry2val_0 fcurry2val_3 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co fcurry2val_3 fcurry2val_2 fcurry2val_4 co fcurry2val_0 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt icurry2val_0 cv fcurry2val_3 fcurry2val_2 fcurry2val_4 oveq1 icurry2val_0 fcurry2val_0 icurry2val_0 cv fcurry2val_2 fcurry2val_4 co cmpt eqid fcurry2val_3 fcurry2val_2 fcurry2val_4 ovex fvmpt pm2.61d2 eqtrd $.
$}
$( Lemma for ~ cnvf1o .  (Contributed by Mario Carneiro, 27-Apr-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fcnvf1olem_0 $f class A $.
	fcnvf1olem_1 $f class B $.
	fcnvf1olem_2 $f class C $.
	cnvf1olem $p |- ( ( Rel A /\ ( B e. A /\ C = U. `' { B } ) ) -> ( C e. `' A /\ B = U. `' { C } ) ) $= fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 fcnvf1olem_0 ccnv wcel fcnvf1olem_1 fcnvf1olem_2 csn ccnv cuni wceq fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop fcnvf1olem_0 ccnv fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop csn ccnv cuni fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop csn ccnv cuni fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq simprr fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 csn ccnv fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop csn ccnv fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 csn fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop csn fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_1 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop wceq fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq fcnvf1olem_1 fcnvf1olem_0 1st2nd adantrr sneqd cnveqd unieqd eqtrd fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv opswap syl6eq fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop fcnvf1olem_0 wcel fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop fcnvf1olem_0 ccnv wcel fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop fcnvf1olem_0 fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_1 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop wceq fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq fcnvf1olem_1 fcnvf1olem_0 1st2nd adantrr fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq simprl eqeltrrd fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv fcnvf1olem_0 fcnvf1olem_1 c2nd fvex fcnvf1olem_1 c1st fvex opelcnv sylibr eqeltrd fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop csn ccnv cuni fcnvf1olem_1 fcnvf1olem_2 csn ccnv cuni fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop csn ccnv cuni fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv opswap eqcomi fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_1 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop wceq fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq fcnvf1olem_1 fcnvf1olem_0 1st2nd adantrr fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 csn ccnv fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop csn ccnv fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 csn fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop csn fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop csn ccnv cuni fcnvf1olem_1 c2nd cfv fcnvf1olem_1 c1st cfv cop fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop csn ccnv cuni fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq simprr fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 csn ccnv fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop csn ccnv fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 csn fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop csn fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq wa wa fcnvf1olem_1 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop fcnvf1olem_0 wrel fcnvf1olem_1 fcnvf1olem_0 wcel fcnvf1olem_1 fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv cop wceq fcnvf1olem_2 fcnvf1olem_1 csn ccnv cuni wceq fcnvf1olem_1 fcnvf1olem_0 1st2nd adantrr sneqd cnveqd unieqd eqtrd fcnvf1olem_1 c1st cfv fcnvf1olem_1 c2nd cfv opswap syl6eq sneqd cnveqd unieqd 3eqtr4a jca $.
$}
$( Describe a function that maps the elements of a set to its converse
       bijectively.  (Contributed by Mario Carneiro, 27-Apr-2014.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y A $.
	icnvf1o_0 $f set y $.
	fcnvf1o_0 $f set x $.
	fcnvf1o_1 $f class A $.
	cnvf1o $p |- ( Rel A -> ( x e. A |-> U. `' { x } ) : A -1-1-onto-> `' A ) $= fcnvf1o_1 wrel fcnvf1o_0 icnvf1o_0 fcnvf1o_1 fcnvf1o_1 ccnv fcnvf1o_0 cv csn ccnv cuni icnvf1o_0 cv csn ccnv cuni fcnvf1o_0 fcnvf1o_1 fcnvf1o_0 cv csn ccnv cuni cmpt cvv cvv fcnvf1o_0 fcnvf1o_1 fcnvf1o_0 cv csn ccnv cuni cmpt eqid fcnvf1o_0 cv csn ccnv cuni cvv wcel fcnvf1o_1 wrel fcnvf1o_0 cv fcnvf1o_1 wcel wa fcnvf1o_0 cv csn ccnv fcnvf1o_0 cv csn fcnvf1o_0 cv snex cnvex uniex a1i icnvf1o_0 cv csn ccnv cuni cvv wcel fcnvf1o_1 wrel icnvf1o_0 cv fcnvf1o_1 ccnv wcel wa icnvf1o_0 cv csn ccnv icnvf1o_0 cv csn icnvf1o_0 cv snex cnvex uniex a1i fcnvf1o_1 wrel fcnvf1o_0 cv fcnvf1o_1 wcel icnvf1o_0 cv fcnvf1o_0 cv csn ccnv cuni wceq wa icnvf1o_0 cv fcnvf1o_1 ccnv wcel fcnvf1o_0 cv icnvf1o_0 cv csn ccnv cuni wceq wa fcnvf1o_1 fcnvf1o_0 cv icnvf1o_0 cv cnvf1olem fcnvf1o_1 wrel icnvf1o_0 cv fcnvf1o_1 ccnv wcel fcnvf1o_0 cv icnvf1o_0 cv csn ccnv cuni wceq wa wa fcnvf1o_0 cv fcnvf1o_1 ccnv ccnv wcel icnvf1o_0 cv fcnvf1o_0 cv csn ccnv cuni wceq wa fcnvf1o_0 cv fcnvf1o_1 wcel icnvf1o_0 cv fcnvf1o_0 cv csn ccnv cuni wceq wa fcnvf1o_1 wrel icnvf1o_0 cv fcnvf1o_1 ccnv wcel fcnvf1o_0 cv icnvf1o_0 cv csn ccnv cuni wceq wa wa fcnvf1o_1 ccnv wrel icnvf1o_0 cv fcnvf1o_1 ccnv wcel fcnvf1o_0 cv icnvf1o_0 cv csn ccnv cuni wceq wa fcnvf1o_0 cv fcnvf1o_1 ccnv ccnv wcel icnvf1o_0 cv fcnvf1o_0 cv csn ccnv cuni wceq wa fcnvf1o_1 relcnv fcnvf1o_1 wrel icnvf1o_0 cv fcnvf1o_1 ccnv wcel fcnvf1o_0 cv icnvf1o_0 cv csn ccnv cuni wceq wa simpr fcnvf1o_1 ccnv icnvf1o_0 cv fcnvf1o_0 cv cnvf1olem sylancr fcnvf1o_1 wrel fcnvf1o_0 cv fcnvf1o_1 ccnv ccnv wcel icnvf1o_0 cv fcnvf1o_0 cv csn ccnv cuni wceq wa fcnvf1o_0 cv fcnvf1o_1 wcel icnvf1o_0 cv fcnvf1o_0 cv csn ccnv cuni wceq wa wb icnvf1o_0 cv fcnvf1o_1 ccnv wcel fcnvf1o_0 cv icnvf1o_0 cv csn ccnv cuni wceq wa fcnvf1o_1 wrel fcnvf1o_0 cv fcnvf1o_1 ccnv ccnv wcel fcnvf1o_0 cv fcnvf1o_1 wcel icnvf1o_0 cv fcnvf1o_0 cv csn ccnv cuni wceq fcnvf1o_1 wrel fcnvf1o_1 ccnv ccnv fcnvf1o_1 wceq fcnvf1o_0 cv fcnvf1o_1 ccnv ccnv wcel fcnvf1o_0 cv fcnvf1o_1 wcel wb fcnvf1o_1 dfrel2 fcnvf1o_1 ccnv ccnv fcnvf1o_1 fcnvf1o_0 cv eleq2 sylbi anbi1d adantr mpbid impbida f1od $.
$}
$( Lemma for ~ fpar .  (Contributed by NM, 22-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	$d x y $.
	$d x y $.
	ifparlem1_0 $f set y $.
	ffparlem1_0 $f set x $.
	fparlem1 $p |- ( `' ( 1st |` ( _V X. _V ) ) " { x } ) = ( { x } X. _V ) $= ifparlem1_0 c1st cvv cvv cxp cres ccnv ffparlem1_0 cv csn cima ffparlem1_0 cv csn cvv cxp ifparlem1_0 cv cvv cvv cxp wcel ifparlem1_0 cv c1st cvv cvv cxp cres cfv ffparlem1_0 cv wceq wa ifparlem1_0 cv cvv cvv cxp wcel ifparlem1_0 cv c1st cfv ffparlem1_0 cv csn wcel ifparlem1_0 cv c2nd cfv cvv wcel wa wa ifparlem1_0 cv c1st cvv cvv cxp cres ccnv ffparlem1_0 cv csn cima wcel ifparlem1_0 cv ffparlem1_0 cv csn cvv cxp wcel ifparlem1_0 cv cvv cvv cxp wcel ifparlem1_0 cv c1st cvv cvv cxp cres cfv ffparlem1_0 cv wceq ifparlem1_0 cv c1st cfv ffparlem1_0 cv csn wcel ifparlem1_0 cv c2nd cfv cvv wcel wa ifparlem1_0 cv cvv cvv cxp wcel ifparlem1_0 cv c1st cvv cvv cxp cres cfv ffparlem1_0 cv wceq ifparlem1_0 cv c1st cfv ffparlem1_0 cv wceq ifparlem1_0 cv c1st cfv ffparlem1_0 cv csn wcel ifparlem1_0 cv c2nd cfv cvv wcel wa ifparlem1_0 cv cvv cvv cxp wcel ifparlem1_0 cv c1st cvv cvv cxp cres cfv ifparlem1_0 cv c1st cfv ffparlem1_0 cv ifparlem1_0 cv cvv cvv cxp c1st fvres eqeq1d ifparlem1_0 cv c1st cfv ffparlem1_0 cv wceq ifparlem1_0 cv c1st cfv ffparlem1_0 cv csn wcel ifparlem1_0 cv c1st cfv ffparlem1_0 cv csn wcel ifparlem1_0 cv c2nd cfv cvv wcel wa ifparlem1_0 cv c1st cfv ffparlem1_0 cv ffparlem1_0 vex elsnc2 ifparlem1_0 cv c2nd cfv cvv wcel ifparlem1_0 cv c1st cfv ffparlem1_0 cv csn wcel ifparlem1_0 cv c2nd fvex biantru bitr3i syl6bb pm5.32i cvv cvv cxp cvv c1st cvv cvv cxp cres wf c1st cvv cvv cxp cres cvv cvv cxp wfn ifparlem1_0 cv c1st cvv cvv cxp cres ccnv ffparlem1_0 cv csn cima wcel ifparlem1_0 cv cvv cvv cxp wcel ifparlem1_0 cv c1st cvv cvv cxp cres cfv ffparlem1_0 cv wceq wa wb cvv cvv f1stres cvv cvv cxp cvv c1st cvv cvv cxp cres ffn cvv cvv cxp ffparlem1_0 cv ifparlem1_0 cv c1st cvv cvv cxp cres fniniseg mp2b ifparlem1_0 cv ffparlem1_0 cv csn cvv elxp7 3bitr4i eqriv $.
$}
$( Lemma for ~ fpar .  (Contributed by NM, 22-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	$d x y $.
	$d x y $.
	ifparlem2_0 $f set x $.
	ffparlem2_0 $f set y $.
	fparlem2 $p |- ( `' ( 2nd |` ( _V X. _V ) ) " { y } ) = ( _V X. { y } ) $= ifparlem2_0 c2nd cvv cvv cxp cres ccnv ffparlem2_0 cv csn cima cvv ffparlem2_0 cv csn cxp ifparlem2_0 cv cvv cvv cxp wcel ifparlem2_0 cv c2nd cvv cvv cxp cres cfv ffparlem2_0 cv wceq wa ifparlem2_0 cv cvv cvv cxp wcel ifparlem2_0 cv c1st cfv cvv wcel ifparlem2_0 cv c2nd cfv ffparlem2_0 cv csn wcel wa wa ifparlem2_0 cv c2nd cvv cvv cxp cres ccnv ffparlem2_0 cv csn cima wcel ifparlem2_0 cv cvv ffparlem2_0 cv csn cxp wcel ifparlem2_0 cv cvv cvv cxp wcel ifparlem2_0 cv c2nd cvv cvv cxp cres cfv ffparlem2_0 cv wceq ifparlem2_0 cv c1st cfv cvv wcel ifparlem2_0 cv c2nd cfv ffparlem2_0 cv csn wcel wa ifparlem2_0 cv cvv cvv cxp wcel ifparlem2_0 cv c2nd cvv cvv cxp cres cfv ffparlem2_0 cv wceq ifparlem2_0 cv c2nd cfv ffparlem2_0 cv wceq ifparlem2_0 cv c1st cfv cvv wcel ifparlem2_0 cv c2nd cfv ffparlem2_0 cv csn wcel wa ifparlem2_0 cv cvv cvv cxp wcel ifparlem2_0 cv c2nd cvv cvv cxp cres cfv ifparlem2_0 cv c2nd cfv ffparlem2_0 cv ifparlem2_0 cv cvv cvv cxp c2nd fvres eqeq1d ifparlem2_0 cv c2nd cfv ffparlem2_0 cv wceq ifparlem2_0 cv c2nd cfv ffparlem2_0 cv csn wcel ifparlem2_0 cv c1st cfv cvv wcel ifparlem2_0 cv c2nd cfv ffparlem2_0 cv csn wcel wa ifparlem2_0 cv c2nd cfv ffparlem2_0 cv ffparlem2_0 vex elsnc2 ifparlem2_0 cv c1st cfv cvv wcel ifparlem2_0 cv c2nd cfv ffparlem2_0 cv csn wcel ifparlem2_0 cv c1st fvex biantrur bitr3i syl6bb pm5.32i cvv cvv cxp cvv c2nd cvv cvv cxp cres wf c2nd cvv cvv cxp cres cvv cvv cxp wfn ifparlem2_0 cv c2nd cvv cvv cxp cres ccnv ffparlem2_0 cv csn cima wcel ifparlem2_0 cv cvv cvv cxp wcel ifparlem2_0 cv c2nd cvv cvv cxp cres cfv ffparlem2_0 cv wceq wa wb cvv cvv f2ndres cvv cvv cxp cvv c2nd cvv cvv cxp cres ffn cvv cvv cxp ffparlem2_0 cv ifparlem2_0 cv c2nd cvv cvv cxp cres fniniseg mp2b ifparlem2_0 cv cvv ffparlem2_0 cv csn elxp7 3bitr4i eqriv $.
$}
$( Lemma for ~ fpar .  (Contributed by NM, 22-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v F $.
	$d x A $.
	$d x y F $.
	$d x y $.
	$d x y $.
	ifparlem3_0 $f set y $.
	ffparlem3_0 $f set x $.
	ffparlem3_1 $f class A $.
	ffparlem3_2 $f class F $.
	fparlem3 $p |- ( F Fn A -> ( `' ( 1st |` ( _V X. _V ) ) o. ( F o. ( 1st |` ( _V X. _V ) ) ) ) = U_ x e. A ( ( { x } X. _V ) X. ( { ( F ` x ) } X. _V ) ) ) $= ffparlem3_2 ffparlem3_1 wfn c1st cvv cvv cxp cres ccnv ffparlem3_0 ffparlem3_1 c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp ciun ccom ffparlem3_0 ffparlem3_1 c1st cvv cvv cxp cres ccnv c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp ccom ciun c1st cvv cvv cxp cres ccnv ffparlem3_2 c1st cvv cvv cxp cres ccom ccom ffparlem3_0 ffparlem3_1 ffparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp cxp ciun ffparlem3_0 c1st cvv cvv cxp cres ccnv c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp ffparlem3_1 coiun ffparlem3_2 ffparlem3_1 wfn ffparlem3_2 c1st cvv cvv cxp cres ccom ffparlem3_0 ffparlem3_1 c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp ciun c1st cvv cvv cxp cres ccnv ffparlem3_2 ffparlem3_1 wfn ffparlem3_2 cdm c1st cvv cvv cxp cres crn cin ffparlem3_1 wss ffparlem3_2 c1st cvv cvv cxp cres ccom ffparlem3_0 ffparlem3_1 c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp ciun wceq ffparlem3_2 ffparlem3_1 wfn ffparlem3_2 cdm ffparlem3_2 cdm c1st cvv cvv cxp cres crn cin ffparlem3_1 ffparlem3_2 cdm c1st cvv cvv cxp cres crn inss1 ffparlem3_1 ffparlem3_2 fndm syl5sseq ffparlem3_0 ffparlem3_2 c1st cvv cvv cxp cres ffparlem3_1 dfco2a syl coeq2d ffparlem3_2 ffparlem3_1 wfn ffparlem3_0 ffparlem3_1 ffparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp cxp c1st cvv cvv cxp cres ccnv c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp ccom ffparlem3_2 ffparlem3_1 wfn ffparlem3_0 cv ffparlem3_1 wcel wa ffparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp cxp c1st cvv cvv cxp cres ccnv ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ccnv ccom c1st cvv cvv cxp cres ccnv c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp ccom ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp c1st cvv cvv cxp cres ccom ccnv ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp ffparlem3_0 cv csn cvv cxp cxp ccnv c1st cvv cvv cxp cres ccnv ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ccnv ccom ffparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp c1st cvv cvv cxp cres ccom ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp c1st cvv cvv cxp cres ccom ifparlem3_0 ffparlem3_0 cv ffparlem3_2 cfv csn c1st cvv cvv cxp cres ccnv ifparlem3_0 cv csn cima ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ifparlem3_0 cv csn cima cxp ciun ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp cdm c1st cvv cvv cxp cres crn cin ffparlem3_0 cv ffparlem3_2 cfv csn wss ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp c1st cvv cvv cxp cres ccom ifparlem3_0 ffparlem3_0 cv ffparlem3_2 cfv csn c1st cvv cvv cxp cres ccnv ifparlem3_0 cv csn cima ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ifparlem3_0 cv csn cima cxp ciun wceq ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp cdm c1st cvv cvv cxp cres crn cin ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp cdm ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp cdm c1st cvv cvv cxp cres crn inss1 ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp dmxpss sstri ifparlem3_0 ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp c1st cvv cvv cxp cres ffparlem3_0 cv ffparlem3_2 cfv csn dfco2a ax-mp ifparlem3_0 ffparlem3_0 cv ffparlem3_2 cfv c1st cvv cvv cxp cres ccnv ifparlem3_0 cv csn cima ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ifparlem3_0 cv csn cima cxp ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 fvex ifparlem3_0 cv ffparlem3_0 cv ffparlem3_2 cfv wceq c1st cvv cvv cxp cres ccnv ifparlem3_0 cv csn cima ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ifparlem3_0 cv csn cima ffparlem3_0 cv csn cvv cxp ifparlem3_0 cv ffparlem3_0 cv ffparlem3_2 cfv wceq c1st cvv cvv cxp cres ccnv ifparlem3_0 cv csn cima ifparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp ifparlem3_0 fparlem1 ifparlem3_0 cv ffparlem3_0 cv ffparlem3_2 cfv wceq ifparlem3_0 cv csn ffparlem3_0 cv ffparlem3_2 cfv csn cvv ifparlem3_0 cv ffparlem3_0 cv ffparlem3_2 cfv sneq xpeq1d syl5eq ifparlem3_0 cv ffparlem3_0 cv ffparlem3_2 cfv wceq ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ifparlem3_0 cv csn cima ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn cima ffparlem3_0 cv csn cvv cxp ifparlem3_0 cv ffparlem3_0 cv ffparlem3_2 cfv wceq ifparlem3_0 cv csn ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ifparlem3_0 cv ffparlem3_0 cv ffparlem3_2 cfv sneq imaeq2d ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn cima ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn cres crn ffparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn df-ima ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn cres crn ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp crn ffparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn cres ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv ffparlem3_2 cfv csn wss ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn cres ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp wceq ffparlem3_0 cv ffparlem3_2 cfv csn ssid ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn xpssres ax-mp rneqi ffparlem3_0 cv ffparlem3_2 cfv csn c0 wne ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp crn ffparlem3_0 cv csn cvv cxp wceq ffparlem3_0 cv ffparlem3_2 cfv ffparlem3_0 cv ffparlem3_2 fvex snnz ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp rnxp ax-mp eqtri eqtri syl6eq xpeq12d iunxsn eqtri cnveqi ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp c1st cvv cvv cxp cres cnvco ffparlem3_0 cv ffparlem3_2 cfv csn cvv cxp ffparlem3_0 cv csn cvv cxp cnvxp 3eqtr3i ffparlem3_2 ffparlem3_1 wfn ffparlem3_0 cv ffparlem3_1 wcel wa ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ccnv c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp c1st cvv cvv cxp cres ccnv ffparlem3_2 ffparlem3_1 wfn ffparlem3_0 cv ffparlem3_1 wcel wa ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ccnv ffparlem3_2 ffparlem3_0 cv csn cima c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima cxp ccnv c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_2 ffparlem3_0 cv csn cima cxp ffparlem3_2 ffparlem3_1 wfn ffparlem3_0 cv ffparlem3_1 wcel wa ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_2 ffparlem3_0 cv csn cima c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima cxp ffparlem3_2 ffparlem3_1 wfn ffparlem3_0 cv ffparlem3_1 wcel wa ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 cv csn cvv cxp cxp ffparlem3_0 cv ffparlem3_2 cfv csn c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima cxp ffparlem3_2 ffparlem3_0 cv csn cima c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima cxp c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_0 cv csn cvv cxp ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_0 fparlem1 xpeq2i ffparlem3_2 ffparlem3_1 wfn ffparlem3_0 cv ffparlem3_1 wcel wa ffparlem3_0 cv ffparlem3_2 cfv csn ffparlem3_2 ffparlem3_0 cv csn cima c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima ffparlem3_1 ffparlem3_0 cv ffparlem3_2 fnsnfv xpeq1d syl5eqr cnveqd ffparlem3_2 ffparlem3_0 cv csn cima c1st cvv cvv cxp cres ccnv ffparlem3_0 cv csn cima cnvxp syl6eq coeq2d syl5eqr iuneq2dv 3eqtr4a $.
$}
$( Lemma for ~ fpar .  (Contributed by NM, 22-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
${
	$v x $.
	$v y $.
	$v B $.
	$v G $.
	$d y B $.
	$d x y $.
	$d x y G $.
	$d x y $.
	ifparlem4_0 $f set x $.
	ffparlem4_0 $f set y $.
	ffparlem4_1 $f class B $.
	ffparlem4_2 $f class G $.
	fparlem4 $p |- ( G Fn B -> ( `' ( 2nd |` ( _V X. _V ) ) o. ( G o. ( 2nd |` ( _V X. _V ) ) ) ) = U_ y e. B ( ( _V X. { y } ) X. ( _V X. { ( G ` y ) } ) ) ) $= ffparlem4_2 ffparlem4_1 wfn c2nd cvv cvv cxp cres ccnv ffparlem4_0 ffparlem4_1 c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp ciun ccom ffparlem4_0 ffparlem4_1 c2nd cvv cvv cxp cres ccnv c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp ccom ciun c2nd cvv cvv cxp cres ccnv ffparlem4_2 c2nd cvv cvv cxp cres ccom ccom ffparlem4_0 ffparlem4_1 cvv ffparlem4_0 cv csn cxp cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cxp ciun ffparlem4_0 c2nd cvv cvv cxp cres ccnv c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp ffparlem4_1 coiun ffparlem4_2 ffparlem4_1 wfn ffparlem4_2 c2nd cvv cvv cxp cres ccom ffparlem4_0 ffparlem4_1 c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp ciun c2nd cvv cvv cxp cres ccnv ffparlem4_2 ffparlem4_1 wfn ffparlem4_2 cdm c2nd cvv cvv cxp cres crn cin ffparlem4_1 wss ffparlem4_2 c2nd cvv cvv cxp cres ccom ffparlem4_0 ffparlem4_1 c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp ciun wceq ffparlem4_2 ffparlem4_1 wfn ffparlem4_2 cdm ffparlem4_2 cdm c2nd cvv cvv cxp cres crn cin ffparlem4_1 ffparlem4_2 cdm c2nd cvv cvv cxp cres crn inss1 ffparlem4_1 ffparlem4_2 fndm syl5sseq ffparlem4_0 ffparlem4_2 c2nd cvv cvv cxp cres ffparlem4_1 dfco2a syl coeq2d ffparlem4_2 ffparlem4_1 wfn ffparlem4_0 ffparlem4_1 cvv ffparlem4_0 cv csn cxp cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cxp c2nd cvv cvv cxp cres ccnv c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp ccom ffparlem4_2 ffparlem4_1 wfn ffparlem4_0 cv ffparlem4_1 wcel wa cvv ffparlem4_0 cv csn cxp cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cxp c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ccnv ccom c2nd cvv cvv cxp cres ccnv c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp ccom ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp c2nd cvv cvv cxp cres ccom ccnv cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cvv ffparlem4_0 cv csn cxp cxp ccnv c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ccnv ccom cvv ffparlem4_0 cv csn cxp cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp c2nd cvv cvv cxp cres ccom cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp c2nd cvv cvv cxp cres ccom ifparlem4_0 ffparlem4_0 cv ffparlem4_2 cfv csn c2nd cvv cvv cxp cres ccnv ifparlem4_0 cv csn cima ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ifparlem4_0 cv csn cima cxp ciun cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp cdm c2nd cvv cvv cxp cres crn cin ffparlem4_0 cv ffparlem4_2 cfv csn wss ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp c2nd cvv cvv cxp cres ccom ifparlem4_0 ffparlem4_0 cv ffparlem4_2 cfv csn c2nd cvv cvv cxp cres ccnv ifparlem4_0 cv csn cima ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ifparlem4_0 cv csn cima cxp ciun wceq ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp cdm c2nd cvv cvv cxp cres crn cin ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp cdm ffparlem4_0 cv ffparlem4_2 cfv csn ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp cdm c2nd cvv cvv cxp cres crn inss1 ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp dmxpss sstri ifparlem4_0 ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp c2nd cvv cvv cxp cres ffparlem4_0 cv ffparlem4_2 cfv csn dfco2a ax-mp ifparlem4_0 ffparlem4_0 cv ffparlem4_2 cfv c2nd cvv cvv cxp cres ccnv ifparlem4_0 cv csn cima ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ifparlem4_0 cv csn cima cxp cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 fvex ifparlem4_0 cv ffparlem4_0 cv ffparlem4_2 cfv wceq c2nd cvv cvv cxp cres ccnv ifparlem4_0 cv csn cima cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ifparlem4_0 cv csn cima cvv ffparlem4_0 cv csn cxp ifparlem4_0 cv ffparlem4_0 cv ffparlem4_2 cfv wceq c2nd cvv cvv cxp cres ccnv ifparlem4_0 cv csn cima cvv ifparlem4_0 cv csn cxp cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp ifparlem4_0 fparlem2 ifparlem4_0 cv ffparlem4_0 cv ffparlem4_2 cfv wceq ifparlem4_0 cv csn ffparlem4_0 cv ffparlem4_2 cfv csn cvv ifparlem4_0 cv ffparlem4_0 cv ffparlem4_2 cfv sneq xpeq2d syl5eq ifparlem4_0 cv ffparlem4_0 cv ffparlem4_2 cfv wceq ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ifparlem4_0 cv csn cima ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cima cvv ffparlem4_0 cv csn cxp ifparlem4_0 cv ffparlem4_0 cv ffparlem4_2 cfv wceq ifparlem4_0 cv csn ffparlem4_0 cv ffparlem4_2 cfv csn ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ifparlem4_0 cv ffparlem4_0 cv ffparlem4_2 cfv sneq imaeq2d ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cima ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cres crn cvv ffparlem4_0 cv csn cxp ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn df-ima ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cres crn ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp crn cvv ffparlem4_0 cv csn cxp ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cres ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn ffparlem4_0 cv ffparlem4_2 cfv csn wss ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn cres ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp wceq ffparlem4_0 cv ffparlem4_2 cfv csn ssid ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp ffparlem4_0 cv ffparlem4_2 cfv csn xpssres ax-mp rneqi ffparlem4_0 cv ffparlem4_2 cfv csn c0 wne ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp crn cvv ffparlem4_0 cv csn cxp wceq ffparlem4_0 cv ffparlem4_2 cfv ffparlem4_0 cv ffparlem4_2 fvex snnz ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp rnxp ax-mp eqtri eqtri syl6eq xpeq12d iunxsn eqtri cnveqi ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp c2nd cvv cvv cxp cres cnvco cvv ffparlem4_0 cv ffparlem4_2 cfv csn cxp cvv ffparlem4_0 cv csn cxp cnvxp 3eqtr3i ffparlem4_2 ffparlem4_1 wfn ffparlem4_0 cv ffparlem4_1 wcel wa ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ccnv c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp c2nd cvv cvv cxp cres ccnv ffparlem4_2 ffparlem4_1 wfn ffparlem4_0 cv ffparlem4_1 wcel wa ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ccnv ffparlem4_2 ffparlem4_0 cv csn cima c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima cxp ccnv c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_2 ffparlem4_0 cv csn cima cxp ffparlem4_2 ffparlem4_1 wfn ffparlem4_0 cv ffparlem4_1 wcel wa ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_2 ffparlem4_0 cv csn cima c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima cxp ffparlem4_2 ffparlem4_1 wfn ffparlem4_0 cv ffparlem4_1 wcel wa ffparlem4_0 cv ffparlem4_2 cfv csn cvv ffparlem4_0 cv csn cxp cxp ffparlem4_0 cv ffparlem4_2 cfv csn c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima cxp ffparlem4_2 ffparlem4_0 cv csn cima c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima cxp c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima cvv ffparlem4_0 cv csn cxp ffparlem4_0 cv ffparlem4_2 cfv csn ffparlem4_0 fparlem2 xpeq2i ffparlem4_2 ffparlem4_1 wfn ffparlem4_0 cv ffparlem4_1 wcel wa ffparlem4_0 cv ffparlem4_2 cfv csn ffparlem4_2 ffparlem4_0 cv csn cima c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima ffparlem4_1 ffparlem4_0 cv ffparlem4_2 fnsnfv xpeq1d syl5eqr cnveqd ffparlem4_2 ffparlem4_0 cv csn cima c2nd cvv cvv cxp cres ccnv ffparlem4_0 cv csn cima cnvxp syl6eq coeq2d syl5eqr iuneq2dv 3eqtr4a $.
$}
$( Merge two functions in parallel.  Use as the second argument of a
       composition with a (2-place) operation to build compound operations such
       as ` z = ( ( sqr `` x ) + ( abs `` y ) ) ` .  (Contributed by NM,
       17-Sep-2007.)  (Proof shortened by Mario Carneiro, 28-Apr-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v F $.
	$v G $.
	$v H $.
	$d x y A $.
	$d x y B $.
	$d x y F $.
	$d x y G $.
	ffpar_0 $f set x $.
	ffpar_1 $f set y $.
	ffpar_2 $f class A $.
	ffpar_3 $f class B $.
	ffpar_4 $f class F $.
	ffpar_5 $f class G $.
	ffpar_6 $f class H $.
	efpar_0 $e |- H = ( ( `' ( 1st |` ( _V X. _V ) ) o. ( F o. ( 1st |` ( _V X. _V ) ) ) ) i^i ( `' ( 2nd |` ( _V X. _V ) ) o. ( G o. ( 2nd |` ( _V X. _V ) ) ) ) ) $.
	fpar $p |- ( ( F Fn A /\ G Fn B ) -> H = ( x e. A , y e. B |-> <. ( F ` x ) , ( G ` y ) >. ) ) $= ffpar_4 ffpar_2 wfn ffpar_5 ffpar_3 wfn wa c1st cvv cvv cxp cres ccnv ffpar_4 c1st cvv cvv cxp cres ccom ccom c2nd cvv cvv cxp cres ccnv ffpar_5 c2nd cvv cvv cxp cres ccom ccom cin ffpar_0 ffpar_2 ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp ciun ffpar_1 ffpar_3 cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp ciun cin ffpar_6 ffpar_0 ffpar_1 ffpar_2 ffpar_3 ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop cmpt2 ffpar_4 ffpar_2 wfn ffpar_5 ffpar_3 wfn c1st cvv cvv cxp cres ccnv ffpar_4 c1st cvv cvv cxp cres ccom ccom ffpar_0 ffpar_2 ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp ciun c2nd cvv cvv cxp cres ccnv ffpar_5 c2nd cvv cvv cxp cres ccom ccom ffpar_1 ffpar_3 cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp ciun ffpar_0 ffpar_2 ffpar_4 fparlem3 ffpar_1 ffpar_3 ffpar_5 fparlem4 ineqan12d efpar_0 ffpar_0 ffpar_1 ffpar_2 ffpar_3 ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop cmpt2 ffpar_0 ffpar_2 ffpar_1 ffpar_3 ffpar_0 cv ffpar_1 cv cop ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop cop csn ciun ciun ffpar_0 ffpar_2 ffpar_1 ffpar_3 ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp cin ciun ciun ffpar_0 ffpar_2 ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp ciun ffpar_1 ffpar_3 cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp ciun cin ffpar_0 ffpar_1 ffpar_2 ffpar_3 ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv opex dfmpt2 ffpar_0 ffpar_2 ffpar_1 ffpar_3 ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp cin ciun ffpar_1 ffpar_3 ffpar_0 cv ffpar_1 cv cop ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop cop csn ciun ffpar_1 ffpar_3 ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp cin ciun ffpar_1 ffpar_3 ffpar_0 cv ffpar_1 cv cop ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop cop csn ciun wceq ffpar_0 cv ffpar_2 wcel ffpar_1 ffpar_3 ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp cin ffpar_0 cv ffpar_1 cv cop ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop cop csn ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp cin ffpar_0 cv ffpar_1 cv cop ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop cop csn wceq ffpar_1 cv ffpar_3 wcel ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp cin ffpar_0 cv csn cvv cxp cvv ffpar_1 cv csn cxp cin ffpar_0 cv ffpar_4 cfv csn cvv cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cin cxp ffpar_0 cv ffpar_1 cv cop csn ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop csn cxp ffpar_0 cv ffpar_1 cv cop ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop cop csn ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp inxp ffpar_0 cv csn cvv cxp cvv ffpar_1 cv csn cxp cin ffpar_0 cv ffpar_1 cv cop csn ffpar_0 cv ffpar_4 cfv csn cvv cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cin ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop csn ffpar_0 cv csn cvv cxp cvv ffpar_1 cv csn cxp cin ffpar_0 cv csn cvv cin cvv ffpar_1 cv csn cin cxp ffpar_0 cv csn ffpar_1 cv csn cxp ffpar_0 cv ffpar_1 cv cop csn ffpar_0 cv csn cvv cvv ffpar_1 cv csn inxp ffpar_0 cv csn cvv cin ffpar_0 cv csn cvv ffpar_1 cv csn cin ffpar_1 cv csn ffpar_0 cv csn inv1 cvv ffpar_1 cv csn cin ffpar_1 cv csn cvv cin ffpar_1 cv csn cvv ffpar_1 cv csn incom ffpar_1 cv csn inv1 eqtri xpeq12i ffpar_0 cv ffpar_1 cv ffpar_0 vex ffpar_1 vex xpsn 3eqtri ffpar_0 cv ffpar_4 cfv csn cvv cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cin ffpar_0 cv ffpar_4 cfv csn cvv cin cvv ffpar_1 cv ffpar_5 cfv csn cin cxp ffpar_0 cv ffpar_4 cfv csn ffpar_1 cv ffpar_5 cfv csn cxp ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop csn ffpar_0 cv ffpar_4 cfv csn cvv cvv ffpar_1 cv ffpar_5 cfv csn inxp ffpar_0 cv ffpar_4 cfv csn cvv cin ffpar_0 cv ffpar_4 cfv csn cvv ffpar_1 cv ffpar_5 cfv csn cin ffpar_1 cv ffpar_5 cfv csn ffpar_0 cv ffpar_4 cfv csn inv1 cvv ffpar_1 cv ffpar_5 cfv csn cin ffpar_1 cv ffpar_5 cfv csn cvv cin ffpar_1 cv ffpar_5 cfv csn cvv ffpar_1 cv ffpar_5 cfv csn incom ffpar_1 cv ffpar_5 cfv csn inv1 eqtri xpeq12i ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv ffpar_0 cv ffpar_4 fvex ffpar_1 cv ffpar_5 fvex xpsn 3eqtri xpeq12i ffpar_0 cv ffpar_1 cv cop ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv cop ffpar_0 cv ffpar_1 cv opex ffpar_0 cv ffpar_4 cfv ffpar_1 cv ffpar_5 cfv opex xpsn 3eqtri a1i iuneq2i a1i iuneq2i ffpar_0 ffpar_1 ffpar_2 ffpar_3 ffpar_0 cv csn cvv cxp ffpar_0 cv ffpar_4 cfv csn cvv cxp cxp cvv ffpar_1 cv csn cxp cvv ffpar_1 cv ffpar_5 cfv csn cxp cxp 2iunin 3eqtr2i 3eqtr4g $.
$}
$( A function that can be used to feed a common value to both operands of
       an operation.  Use as the second argument of a composition with the
       function of ~ fpar in order to build compound functions such as
       ` y = ( ( sqr `` x ) + ( abs `` x ) ) ` .  (Contributed by NM,
       17-Sep-2007.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	ifsplit_0 $f set y $.
	ifsplit_1 $f set z $.
	ffsplit_0 $f set x $.
	fsplit $p |- `' ( 1st |` _I ) = ( x e. _V |-> <. x , x >. ) $= ffsplit_0 cv ifsplit_0 cv c1st cid cres ccnv wbr ffsplit_0 ifsplit_0 copab ifsplit_0 cv ffsplit_0 cv ffsplit_0 cv cop wceq ffsplit_0 ifsplit_0 copab c1st cid cres ccnv ffsplit_0 cvv ffsplit_0 cv ffsplit_0 cv cop cmpt ffsplit_0 cv ifsplit_0 cv c1st cid cres ccnv wbr ifsplit_0 cv ffsplit_0 cv ffsplit_0 cv cop wceq ffsplit_0 ifsplit_0 ffsplit_0 cv ifsplit_0 cv c1st cid cres ccnv wbr ifsplit_0 cv ffsplit_0 cv c1st cid cres wbr ifsplit_0 cv ffsplit_0 cv ffsplit_0 cv cop wceq ffsplit_0 cv ifsplit_0 cv c1st cid cres ffsplit_0 vex ifsplit_0 vex brcnv ifsplit_0 cv ffsplit_0 cv c1st cid cres wbr ifsplit_0 cv ffsplit_0 cv c1st wbr ifsplit_0 cv cid wcel wa ifsplit_0 cv ffsplit_0 cv ffsplit_0 cv cop wceq ifsplit_0 cv ffsplit_0 cv c1st cid ffsplit_0 vex brres ifsplit_0 cv ffsplit_0 cv c1st wbr ifsplit_0 cv cid wcel wa ifsplit_1 cv ffsplit_0 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq wa ifsplit_1 wex ifsplit_0 cv ffsplit_0 cv ffsplit_0 cv cop wceq ifsplit_0 cv c1st cfv ffsplit_0 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq wa ifsplit_1 wex ifsplit_0 cv c1st cfv ffsplit_0 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 wex wa ifsplit_1 cv ffsplit_0 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq wa ifsplit_1 wex ifsplit_0 cv ffsplit_0 cv c1st wbr ifsplit_0 cv cid wcel wa ifsplit_0 cv c1st cfv ffsplit_0 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 19.42v ifsplit_0 cv c1st cfv ffsplit_0 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq wa ifsplit_1 cv ffsplit_0 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq wa ifsplit_1 ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_0 cv c1st cfv ffsplit_0 cv wceq ifsplit_1 cv ffsplit_0 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_0 cv c1st cfv ifsplit_1 cv ffsplit_0 cv ifsplit_1 cv ifsplit_1 cv ifsplit_0 cv ifsplit_1 vex ifsplit_1 vex op1std eqeq1d pm5.32ri exbii ifsplit_0 cv c1st cfv ffsplit_0 cv wceq ifsplit_0 cv ffsplit_0 cv c1st wbr ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 wex ifsplit_0 cv cid wcel c1st cvv wfn ifsplit_0 cv cvv wcel ifsplit_0 cv c1st cfv ffsplit_0 cv wceq ifsplit_0 cv ffsplit_0 cv c1st wbr wb cvv cvv c1st wfo c1st cvv wfn fo1st cvv cvv c1st fofn ax-mp ifsplit_0 vex cvv ifsplit_0 cv ffsplit_0 cv c1st fnbrfvb mp2an ifsplit_0 cv cid wcel ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv wceq ifsplit_1 ifsplit_1 copab wcel ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 wex cid ifsplit_1 cv ifsplit_1 cv wceq ifsplit_1 ifsplit_1 copab ifsplit_0 cv ifsplit_1 dfid2 eleq2i ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 cv ifsplit_1 cv wceq wa ifsplit_1 wex ifsplit_1 wex ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 cv ifsplit_1 cv wceq wa ifsplit_1 wex ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv wceq ifsplit_1 ifsplit_1 copab wcel ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 wex ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 cv ifsplit_1 cv wceq wa ifsplit_1 wex ifsplit_1 ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 cv ifsplit_1 cv wceq wa ifsplit_1 nfe1 19.9 ifsplit_1 cv ifsplit_1 cv wceq ifsplit_1 ifsplit_1 ifsplit_0 cv elopab ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 cv ifsplit_1 cv wceq wa ifsplit_1 ifsplit_1 cv ifsplit_1 cv wceq ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_1 equid biantru exbii 3bitr4i bitr2i anbi12i 3bitr3ri ifsplit_0 cv ifsplit_1 cv ifsplit_1 cv cop wceq ifsplit_0 cv ffsplit_0 cv ffsplit_0 cv cop wceq ifsplit_1 ffsplit_0 cv ffsplit_0 vex ifsplit_1 cv ffsplit_0 cv wceq ifsplit_1 cv ifsplit_1 cv cop ffsplit_0 cv ffsplit_0 cv cop ifsplit_0 cv ifsplit_1 cv ffsplit_0 cv wceq ifsplit_1 cv ffsplit_0 cv ifsplit_1 cv ffsplit_0 cv ifsplit_1 cv ffsplit_0 cv wceq id ifsplit_1 cv ffsplit_0 cv wceq id opeq12d eqeq2d ceqsexv bitri bitri bitri opabbii c1st cid cres ccnv wrel c1st cid cres ccnv ffsplit_0 cv ifsplit_0 cv c1st cid cres ccnv wbr ffsplit_0 ifsplit_0 copab wceq c1st cid cres relcnv ffsplit_0 ifsplit_0 c1st cid cres ccnv dfrel4v mpbi ffsplit_0 ifsplit_0 ffsplit_0 cv ffsplit_0 cv cop mptv 3eqtr4i $.
$}
$( Lemma for ~ algrf and related theorems.  (Contributed by Mario Carneiro,
       28-May-2014.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
${
	$v B $.
	$v C $.
	$v F $.
	falgrflem_0 $f class B $.
	falgrflem_1 $f class C $.
	falgrflem_2 $f class F $.
	ealgrflem_0 $e |- B e. _V $.
	ealgrflem_1 $e |- C e. _V $.
	algrflem $p |- ( B ( F o. 1st ) C ) = ( F ` B ) $= falgrflem_0 falgrflem_1 falgrflem_2 c1st ccom co falgrflem_0 falgrflem_1 cop falgrflem_2 c1st ccom cfv falgrflem_0 falgrflem_1 cop c1st cfv falgrflem_2 cfv falgrflem_0 falgrflem_2 cfv falgrflem_0 falgrflem_1 falgrflem_2 c1st ccom df-ov cvv cvv c1st wf falgrflem_0 falgrflem_1 cop cvv wcel falgrflem_0 falgrflem_1 cop falgrflem_2 c1st ccom cfv falgrflem_0 falgrflem_1 cop c1st cfv falgrflem_2 cfv wceq cvv cvv c1st wfo cvv cvv c1st wf fo1st cvv cvv c1st fof ax-mp falgrflem_0 falgrflem_1 opex cvv cvv falgrflem_0 falgrflem_1 cop falgrflem_2 c1st fvco3 mp2an falgrflem_0 falgrflem_1 cop c1st cfv falgrflem_0 falgrflem_2 falgrflem_0 falgrflem_1 ealgrflem_0 ealgrflem_1 op1st fveq2i 3eqtri $.
$}
$( A lexicographical ordering of two well-founded classes.  (Contributed by
       Scott Fenton, 17-Mar-2011.)  (Revised by Mario Carneiro, 7-Mar-2013.)
       (Proof shortened by Wolf Lammen, 4-Oct-2014.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v u $.
	$v t $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v T $.
	$v s $.
	$v a $.
	$v b $.
	$v c $.
	$v d $.
	$d A a b c s v w x y z $.
	$d B a b d s v w x y z $.
	$d R a b c s v w x y $.
	$d S a b d s t u v w x y $.
	$d T a b s w z $.
	ifrxp_0 $f set z $.
	ifrxp_1 $f set w $.
	ifrxp_2 $f set v $.
	ifrxp_3 $f set u $.
	ifrxp_4 $f set t $.
	ifrxp_5 $f set s $.
	ifrxp_6 $f set a $.
	ifrxp_7 $f set b $.
	ifrxp_8 $f set c $.
	ifrxp_9 $f set d $.
	ffrxp_0 $f set x $.
	ffrxp_1 $f set y $.
	ffrxp_2 $f class A $.
	ffrxp_3 $f class B $.
	ffrxp_4 $f class R $.
	ffrxp_5 $f class S $.
	ffrxp_6 $f class T $.
	efrxp_0 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
	frxp $p |- ( ( R Fr A /\ S Fr B ) -> T Fr ( A X. B ) ) $= ffrxp_2 ffrxp_4 wfr ffrxp_3 ffrxp_5 wfr wa ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne wa ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex wi ifrxp_5 wal ffrxp_2 ffrxp_3 cxp ffrxp_6 wfr ffrxp_2 ffrxp_4 wfr ffrxp_3 ffrxp_5 wfr wa ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne wa ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex wi ifrxp_5 ffrxp_2 ffrxp_4 wfr ffrxp_3 ffrxp_5 wfr wa ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne wa ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_5 cv cdm wrex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex ffrxp_2 ffrxp_4 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne wa ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_5 cv cdm wrex wi ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne wa ifrxp_5 cv cdm ffrxp_2 wss ifrxp_5 cv cdm c0 wne wa ffrxp_2 ffrxp_4 wfr ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_5 cv cdm wrex ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne wa ifrxp_5 cv cdm ffrxp_2 wss ifrxp_5 cv cdm c0 wne ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne ffrxp_3 c0 wne ifrxp_5 cv cdm ffrxp_2 wss ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne wa ffrxp_2 ffrxp_3 cxp c0 wne ffrxp_3 c0 wne ifrxp_5 cv ffrxp_2 ffrxp_3 cxp ssn0 ffrxp_2 ffrxp_3 cxp c0 wne ffrxp_2 c0 wne ffrxp_3 c0 wne ffrxp_2 c0 wne ffrxp_3 c0 wne wa ffrxp_2 ffrxp_3 cxp c0 wne ffrxp_2 ffrxp_3 xpnz biimpri simprd syl ffrxp_3 c0 wne ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv cdm ffrxp_2 wss ffrxp_3 c0 wne ffrxp_2 ffrxp_3 cxp cdm ffrxp_2 wceq ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv cdm ffrxp_2 wss wi ffrxp_2 ffrxp_3 dmxp ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv cdm ffrxp_2 ffrxp_3 cxp cdm wss ffrxp_2 ffrxp_3 cxp cdm ffrxp_2 wceq ifrxp_5 cv cdm ffrxp_2 wss ifrxp_5 cv ffrxp_2 ffrxp_3 cxp dmss ffrxp_2 ffrxp_3 cxp cdm ffrxp_2 ifrxp_5 cv cdm sseq2 syl5ib syl impcom syldan ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne ifrxp_5 cv cdm c0 wne ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 ifrxp_5 cv cdm c0 ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv wrel ifrxp_5 cv c0 wceq ifrxp_5 cv cdm c0 wceq wb ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ffrxp_2 ffrxp_3 cxp wrel ifrxp_5 cv wrel ffrxp_2 ffrxp_3 relxp ifrxp_5 cv ffrxp_2 ffrxp_3 cxp relss mpi ifrxp_5 cv reldm0 syl necon3bid biimpa jca ffrxp_2 ffrxp_4 wfr ifrxp_2 cv ffrxp_2 wss ifrxp_2 cv c0 wne wa ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_2 cv wral ifrxp_6 ifrxp_2 cv wrex wi ifrxp_2 wal ifrxp_5 cv cdm ffrxp_2 wss ifrxp_5 cv cdm c0 wne wa ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_5 cv cdm wrex wi ifrxp_2 ifrxp_6 ifrxp_8 ffrxp_2 ffrxp_4 df-fr ifrxp_2 cv ffrxp_2 wss ifrxp_2 cv c0 wne wa ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_2 cv wral ifrxp_6 ifrxp_2 cv wrex wi ifrxp_5 cv cdm ffrxp_2 wss ifrxp_5 cv cdm c0 wne wa ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_5 cv cdm wrex wi ifrxp_2 ifrxp_5 cv cdm ifrxp_5 cv ifrxp_5 vex dmex ifrxp_2 cv ifrxp_5 cv cdm wceq ifrxp_2 cv ffrxp_2 wss ifrxp_2 cv c0 wne wa ifrxp_5 cv cdm ffrxp_2 wss ifrxp_5 cv cdm c0 wne wa ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_2 cv wral ifrxp_6 ifrxp_2 cv wrex ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_5 cv cdm wrex ifrxp_2 cv ifrxp_5 cv cdm wceq ifrxp_2 cv ffrxp_2 wss ifrxp_5 cv cdm ffrxp_2 wss ifrxp_2 cv c0 wne ifrxp_5 cv cdm c0 wne ifrxp_2 cv ifrxp_5 cv cdm ffrxp_2 sseq1 ifrxp_2 cv ifrxp_5 cv cdm c0 neeq1 anbi12d ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_2 cv wral ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_2 cv ifrxp_5 cv cdm ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_2 cv ifrxp_5 cv cdm raleq rexeqbi1dv imbi12d spcv sylbi syl5 adantr ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne wa ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_5 cv cdm wrex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex wi wi ffrxp_2 ffrxp_4 wfr ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_6 ifrxp_5 cv cdm wrex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex wi ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne w3a ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex ifrxp_6 ifrxp_5 cv cdm ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne w3a ifrxp_6 cv ifrxp_5 cv cdm wcel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wne w3a ifrxp_6 cv ifrxp_5 cv cdm wcel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_6 cv ifrxp_5 cv cdm wcel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex wi ifrxp_5 cv c0 wne ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss wa ifrxp_6 cv ifrxp_5 cv cdm wcel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_6 cv ifrxp_5 cv cdm wcel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex wi ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_6 cv ifrxp_5 cv cdm wcel wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex wi ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ffrxp_3 ffrxp_5 wfr ifrxp_5 cv ifrxp_6 cv csn cima ffrxp_3 wss ifrxp_5 cv ifrxp_6 cv csn cima c0 wne ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_6 cv ifrxp_5 cv cdm wcel ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv ifrxp_6 cv csn cima ifrxp_5 cv crn ffrxp_3 ifrxp_5 cv ifrxp_6 cv csn imassrn ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv crn ffrxp_3 wss wi ffrxp_2 c0 ffrxp_2 c0 wceq ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wceq ifrxp_5 cv crn ffrxp_3 wss ffrxp_2 c0 wceq ffrxp_2 ffrxp_3 cxp c0 wceq ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wceq wi ffrxp_2 c0 wceq ffrxp_3 c0 wceq ffrxp_2 ffrxp_3 cxp c0 wceq ffrxp_2 ffrxp_3 cxp c0 wceq ffrxp_2 c0 wceq ffrxp_3 c0 wceq wo ffrxp_2 ffrxp_3 xpeq0 biimpri orcs ffrxp_2 ffrxp_3 cxp c0 wceq ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv c0 wss ifrxp_5 cv c0 wceq ffrxp_2 ffrxp_3 cxp c0 ifrxp_5 cv sseq2 ifrxp_5 cv ss0 syl6bi syl ifrxp_5 cv c0 wceq ifrxp_5 cv crn c0 crn ffrxp_3 ifrxp_5 cv c0 rneq c0 crn ffrxp_3 wss ifrxp_5 cv c0 wceq c0 crn c0 ffrxp_3 rn0 ffrxp_3 0ss eqsstri a1i eqsstrd syl6 ffrxp_2 c0 wne ffrxp_2 ffrxp_3 cxp crn ffrxp_3 wceq ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv crn ffrxp_3 wss wi ffrxp_2 ffrxp_3 rnxp ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv crn ffrxp_2 ffrxp_3 cxp crn wss ffrxp_2 ffrxp_3 cxp crn ffrxp_3 wceq ifrxp_5 cv crn ffrxp_3 wss ifrxp_5 cv ffrxp_2 ffrxp_3 cxp rnss ffrxp_2 ffrxp_3 cxp crn ffrxp_3 ifrxp_5 cv crn sseq2 syl5ib syl pm2.61ine syl5ss ifrxp_6 cv ifrxp_5 cv cdm wcel ifrxp_6 cv ifrxp_7 cv ifrxp_5 cv wbr ifrxp_7 wex ifrxp_5 cv ifrxp_6 cv csn cima c0 wne ifrxp_7 ifrxp_6 cv ifrxp_5 cv ifrxp_6 vex eldm ifrxp_6 cv ifrxp_7 cv ifrxp_5 cv wbr ifrxp_5 cv ifrxp_6 cv csn cima c0 wne ifrxp_7 ifrxp_6 cv ifrxp_7 cv ifrxp_5 cv wbr ifrxp_7 cv ifrxp_5 cv ifrxp_6 cv csn cima wcel ifrxp_5 cv ifrxp_6 cv csn cima c0 wne ifrxp_7 cv ifrxp_5 cv ifrxp_6 cv csn cima wcel ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_6 cv ifrxp_7 cv ifrxp_5 cv wbr ifrxp_5 cv ifrxp_6 cv ifrxp_7 cv ifrxp_6 vex ifrxp_7 vex elimasn ifrxp_6 cv ifrxp_7 cv ifrxp_5 cv df-br bitr4i ifrxp_5 cv ifrxp_6 cv csn cima ifrxp_7 cv ne0i sylbir exlimiv sylbi ffrxp_3 ffrxp_5 wfr ifrxp_2 cv ffrxp_3 wss ifrxp_2 cv c0 wne wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_2 cv wral ifrxp_7 ifrxp_2 cv wrex wi ifrxp_2 wal ifrxp_5 cv ifrxp_6 cv csn cima ffrxp_3 wss ifrxp_5 cv ifrxp_6 cv csn cima c0 wne wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex wi ifrxp_2 ifrxp_7 ifrxp_9 ffrxp_3 ffrxp_5 df-fr ifrxp_2 cv ffrxp_3 wss ifrxp_2 cv c0 wne wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_2 cv wral ifrxp_7 ifrxp_2 cv wrex wi ifrxp_5 cv ifrxp_6 cv csn cima ffrxp_3 wss ifrxp_5 cv ifrxp_6 cv csn cima c0 wne wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex wi ifrxp_2 ifrxp_5 cv ifrxp_6 cv csn cima ifrxp_5 cv cvv wcel ifrxp_5 cv ifrxp_6 cv csn cima cvv wcel ifrxp_5 vex ifrxp_5 cv ifrxp_6 cv csn cvv imaexg ax-mp ifrxp_2 cv ifrxp_5 cv ifrxp_6 cv csn cima wceq ifrxp_2 cv ffrxp_3 wss ifrxp_2 cv c0 wne wa ifrxp_5 cv ifrxp_6 cv csn cima ffrxp_3 wss ifrxp_5 cv ifrxp_6 cv csn cima c0 wne wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_2 cv wral ifrxp_7 ifrxp_2 cv wrex ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_2 cv ifrxp_5 cv ifrxp_6 cv csn cima wceq ifrxp_2 cv ffrxp_3 wss ifrxp_5 cv ifrxp_6 cv csn cima ffrxp_3 wss ifrxp_2 cv c0 wne ifrxp_5 cv ifrxp_6 cv csn cima c0 wne ifrxp_2 cv ifrxp_5 cv ifrxp_6 cv csn cima ffrxp_3 sseq1 ifrxp_2 cv ifrxp_5 cv ifrxp_6 cv csn cima c0 neeq1 anbi12d ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_2 cv wral ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_2 cv ifrxp_5 cv ifrxp_6 cv csn cima ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_2 cv ifrxp_5 cv ifrxp_6 cv csn cima raleq rexeqbi1dv imbi12d spcv sylbi syl2ani ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex wi wi ifrxp_6 cv ifrxp_5 cv cdm wcel ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex wi ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa wo ifrxp_1 ifrxp_5 cv wral ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa ifrxp_1 ifrxp_5 cv wral ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa wo ifrxp_1 ifrxp_5 cv wral ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ifrxp_5 cv wrel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa ifrxp_1 ifrxp_5 cv wral wi ifrxp_5 cv ffrxp_2 ffrxp_3 cxp wss ffrxp_2 ffrxp_3 cxp wrel ifrxp_5 cv wrel ffrxp_2 ffrxp_3 relxp ifrxp_5 cv ffrxp_2 ffrxp_3 cxp relss mpi ifrxp_5 cv wrel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa ifrxp_1 ifrxp_5 cv wral ifrxp_5 cv wrel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral wa ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa ifrxp_1 ifrxp_5 cv ifrxp_5 cv wrel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral wa ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_5 cv wrel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral wa ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn wi ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_5 cv wrel ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn wi ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_5 cv wrel ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_5 cv wrel ifrxp_1 cv ifrxp_5 cv wcel wa ifrxp_1 cv c1st cfv ifrxp_5 cv cdm wcel ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv ifrxp_5 cv 1stdm ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_1 cv c1st cfv ifrxp_5 cv cdm ifrxp_8 cv ifrxp_1 cv c1st cfv wceq ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_8 cv ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 breq1 notbid rspccv syl5 exp3a impcom adantr ifrxp_5 cv wrel ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wi ifrxp_8 cv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_8 ifrxp_5 cv cdm wral ifrxp_5 cv wrel ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral wa ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_3 wex ifrxp_4 wex ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_5 cv wrel ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_3 wex ifrxp_4 wex wi ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_5 cv wrel ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_3 wex ifrxp_4 wex ifrxp_4 ifrxp_3 ifrxp_1 cv ifrxp_5 cv elrel ex adantr ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_3 wex ifrxp_4 wex ifrxp_5 cv wrel ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral wa ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_5 cv wrel ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral wa ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wi wi ifrxp_4 ifrxp_3 ifrxp_5 cv wrel ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral wa ifrxp_1 cv ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wi ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_4 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_4 cv ifrxp_6 cv wceq ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn wi wi ifrxp_4 cv ifrxp_6 cv wceq ifrxp_5 cv wrel ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral wa ifrxp_4 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_5 cv wrel ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral wa ifrxp_4 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_4 cv ifrxp_6 cv wceq ifrxp_6 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_6 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_5 cv wrel ifrxp_6 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_3 cv ifrxp_5 cv ifrxp_6 cv csn cima wcel ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_5 cv ifrxp_6 cv csn cima wral ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_5 cv ifrxp_6 cv ifrxp_3 cv ifrxp_6 vex ifrxp_3 vex elimasn ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_9 ifrxp_3 cv ifrxp_5 cv ifrxp_6 cv csn cima ifrxp_9 cv ifrxp_3 cv wceq ifrxp_9 cv ifrxp_7 cv ffrxp_5 wbr ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr ifrxp_9 cv ifrxp_3 cv ifrxp_7 cv ffrxp_5 breq1 notbid rspccv syl5bir adantl ifrxp_4 cv ifrxp_6 cv wceq ifrxp_4 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_6 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_4 cv ifrxp_6 cv wceq ifrxp_4 cv ifrxp_3 cv cop ifrxp_6 cv ifrxp_3 cv cop ifrxp_5 cv ifrxp_4 cv ifrxp_6 cv ifrxp_3 cv opeq1 eleq1d imbi1d syl5ibr com3l ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_1 cv ifrxp_5 cv wcel ifrxp_4 cv ifrxp_3 cv cop ifrxp_5 cv wcel ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_4 cv ifrxp_6 cv wceq ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop ifrxp_5 cv eleq1 ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_4 cv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr wn ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_1 cv c1st cfv ifrxp_4 cv ifrxp_6 cv ifrxp_4 cv ifrxp_3 cv ifrxp_1 cv ifrxp_4 vex ifrxp_3 vex op1std eqeq1d ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr ifrxp_3 cv ifrxp_7 cv ffrxp_5 wbr ifrxp_1 cv ifrxp_4 cv ifrxp_3 cv cop wceq ifrxp_1 cv c2nd cfv ifrxp_3 cv ifrxp_7 cv ffrxp_5 ifrxp_4 cv ifrxp_3 cv ifrxp_1 cv ifrxp_4 vex ifrxp_3 vex op2ndd breq1d notbid imbi12d imbi12d syl5ibr exlimivv com3l mpdd adantlr jcad ralrimiv ex sylan ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa wo ifrxp_1 ifrxp_5 cv ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn olc ralimi syl6 ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa wo ifrxp_1 ifrxp_5 cv ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wo wn wo ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa wo ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wo wa ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wo wn wo ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wo ianor ffrxp_0 cv ffrxp_2 ffrxp_3 cxp wcel ffrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel wa ffrxp_0 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 wbr ffrxp_0 cv c1st cfv ffrxp_1 cv c1st cfv wceq ffrxp_0 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr wa wo wa ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ffrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel wa ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 wbr ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv wceq ifrxp_1 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr wa wo wa ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wo wa ffrxp_0 ffrxp_1 ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 ifrxp_1 vex ifrxp_6 cv ifrxp_7 cv opex ffrxp_0 cv ifrxp_1 cv wceq ffrxp_0 cv ffrxp_2 ffrxp_3 cxp wcel ffrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel wa ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ffrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel wa ffrxp_0 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 wbr ffrxp_0 cv c1st cfv ffrxp_1 cv c1st cfv wceq ffrxp_0 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr wa wo ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 wbr ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv wceq ifrxp_1 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr wa wo ffrxp_0 cv ifrxp_1 cv wceq ffrxp_0 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ffrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ffrxp_0 cv ifrxp_1 cv ffrxp_2 ffrxp_3 cxp eleq1 anbi1d ffrxp_0 cv ifrxp_1 cv wceq ffrxp_0 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 wbr ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 wbr ffrxp_0 cv c1st cfv ffrxp_1 cv c1st cfv wceq ffrxp_0 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr wa ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv wceq ifrxp_1 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr wa ffrxp_0 cv ifrxp_1 cv wceq ffrxp_0 cv c1st cfv ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 ffrxp_0 cv ifrxp_1 cv c1st fveq2 breq1d ffrxp_0 cv ifrxp_1 cv wceq ffrxp_0 cv c1st cfv ffrxp_1 cv c1st cfv wceq ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv wceq ffrxp_0 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr ifrxp_1 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr ffrxp_0 cv ifrxp_1 cv wceq ffrxp_0 cv c1st cfv ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_0 cv ifrxp_1 cv c1st fveq2 eqeq1d ffrxp_0 cv ifrxp_1 cv wceq ffrxp_0 cv c2nd cfv ifrxp_1 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 ffrxp_0 cv ifrxp_1 cv c2nd fveq2 breq1d anbi12d orbi12d anbi12d ffrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ffrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel wa ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 wbr ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv wceq ifrxp_1 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr wa wo ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wo ffrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop wceq ffrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ffrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp eleq1 anbi2d ffrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv wceq ifrxp_1 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr wa ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa ffrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop wceq ffrxp_1 cv c1st cfv ifrxp_6 cv ifrxp_1 cv c1st cfv ffrxp_4 ifrxp_6 cv ifrxp_7 cv ffrxp_1 cv ifrxp_6 vex ifrxp_7 vex op1std breq2d ffrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_1 cv c1st cfv ffrxp_1 cv c1st cfv wceq ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ffrxp_1 cv c2nd cfv ffrxp_5 wbr ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr ffrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop wceq ffrxp_1 cv c1st cfv ifrxp_6 cv ifrxp_1 cv c1st cfv ifrxp_6 cv ifrxp_7 cv ffrxp_1 cv ifrxp_6 vex ifrxp_7 vex op1std eqeq2d ffrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop wceq ffrxp_1 cv c2nd cfv ifrxp_7 cv ifrxp_1 cv c2nd cfv ffrxp_5 ifrxp_6 cv ifrxp_7 cv ffrxp_1 cv ifrxp_6 vex ifrxp_7 vex op2ndd breq2d anbi12d orbi12d anbi12d efrxp_0 brab xchnxbir ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wo wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa ifrxp_1 cv ffrxp_2 ffrxp_3 cxp wcel ifrxp_6 cv ifrxp_7 cv cop ffrxp_2 ffrxp_3 cxp wcel wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wo wn ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wn wa ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi wa ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa ioran ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_1 cv c1st cfv ifrxp_6 cv ffrxp_4 wbr wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wa wn ifrxp_1 cv c1st cfv ifrxp_6 cv wceq wn ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wo ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr wn wi ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr ianor ifrxp_1 cv c1st cfv ifrxp_6 cv wceq ifrxp_1 cv c2nd cfv ifrxp_7 cv ffrxp_5 wbr pm4.62 bitr4i anbi2i bitri orbi2i bitri ralbii syl6ibr reximdv ex com23 adantr sylcom impl expimpd 3adant3 ifrxp_5 cv ifrxp_6 cv csn cres ifrxp_5 cv wss ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv ifrxp_6 cv csn cres wrex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv wrex ifrxp_5 cv ifrxp_6 cv csn resss ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_7 wex ifrxp_0 wex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv ifrxp_6 cv csn cres wrex ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_0 wex ifrxp_7 wex ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_7 wex ifrxp_0 wex ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima wrex ifrxp_7 cv ifrxp_5 cv ifrxp_6 cv csn cima wcel ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_7 wex ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_0 wex ifrxp_7 wex ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_5 cv ifrxp_6 cv csn cima df-rex ifrxp_7 cv ifrxp_5 cv ifrxp_6 cv csn cima wcel ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_0 wex ifrxp_7 ifrxp_7 cv ifrxp_5 cv ifrxp_6 cv csn cima wcel ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_0 wex ifrxp_5 cv ifrxp_6 cv ifrxp_7 cv ifrxp_6 vex ifrxp_7 vex elimasn ifrxp_6 cv ifrxp_7 cv cop ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_0 wex ifrxp_6 cv ifrxp_7 cv cop eqid ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_6 cv ifrxp_7 cv cop ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_0 ifrxp_6 cv ifrxp_7 cv cop ifrxp_6 cv ifrxp_7 cv opex ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop ifrxp_6 cv ifrxp_7 cv cop eqeq1 ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr ifrxp_1 cv ifrxp_6 cv ifrxp_7 cv cop ffrxp_6 wbr ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop ifrxp_1 cv ffrxp_6 breq2 notbid ralbidv anbi2d anbi12d spcev mpan sylanb eximi sylbi ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_7 ifrxp_0 excom sylib ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv ifrxp_6 cv csn cres wrex ifrxp_0 cv ifrxp_5 cv ifrxp_6 cv csn cres wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_0 wex ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_7 wex ifrxp_0 wex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv ifrxp_6 cv csn cres df-rex ifrxp_0 cv ifrxp_5 cv ifrxp_6 cv csn cres wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_7 wex ifrxp_0 ifrxp_0 cv ifrxp_5 cv ifrxp_6 cv csn cres wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel wa ifrxp_7 wex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel wa ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_7 wex ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_7 wex ifrxp_0 cv ifrxp_5 cv ifrxp_6 cv csn cres wcel ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel wa ifrxp_7 wex ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 ifrxp_0 cv ifrxp_5 cv ifrxp_6 cv ifrxp_6 vex elsnres anbi1i ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel wa ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_7 19.41v ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel wa ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral wa wa ifrxp_7 ifrxp_0 cv ifrxp_6 cv ifrxp_7 cv cop wceq ifrxp_6 cv ifrxp_7 cv cop ifrxp_5 cv wcel ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral anass exbii 3bitr2i exbii bitri sylibr ifrxp_1 cv ifrxp_0 cv ffrxp_6 wbr wn ifrxp_1 ifrxp_5 cv wral ifrxp_0 ifrxp_5 cv ifrxp_6 cv csn cres ifrxp_5 cv ssrexv mpsyl syl6 exp3a rexlimdv 3expib adantl mpdd alrimiv ifrxp_5 ifrxp_0 ifrxp_1 ffrxp_2 ffrxp_3 cxp ffrxp_6 df-fr sylibr $.
$}
$( Lemma for lexicographical ordering theorems.  (Contributed by Scott
       Fenton, 16-Mar-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v T $.
	$v a $.
	$v b $.
	$v c $.
	$v d $.
	$d A x y $.
	$d B x y $.
	$d R x y $.
	$d S x y $.
	$d a x y $.
	$d b x y $.
	$d c x y $.
	$d d x y $.
	fxporderlem_0 $f set x $.
	fxporderlem_1 $f set y $.
	fxporderlem_2 $f class A $.
	fxporderlem_3 $f class B $.
	fxporderlem_4 $f class R $.
	fxporderlem_5 $f class S $.
	fxporderlem_6 $f class T $.
	fxporderlem_7 $f set a $.
	fxporderlem_8 $f set b $.
	fxporderlem_9 $f set c $.
	fxporderlem_10 $f set d $.
	exporderlem_0 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
	xporderlem $p |- ( <. a , b >. T <. c , d >. <-> ( ( ( a e. A /\ c e. A ) /\ ( b e. B /\ d e. B ) ) /\ ( a R c \/ ( a = c /\ b S d ) ) ) ) $= fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_9 cv fxporderlem_10 cv cop fxporderlem_6 wbr fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_9 cv fxporderlem_10 cv cop cop fxporderlem_0 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel wa fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv wceq fxporderlem_0 cv c2nd cfv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa wo wa fxporderlem_0 fxporderlem_1 copab wcel fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_9 cv fxporderlem_2 wcel fxporderlem_10 cv fxporderlem_3 wcel wa wa fxporderlem_7 cv fxporderlem_9 cv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_9 cv wceq fxporderlem_8 cv fxporderlem_10 cv fxporderlem_5 wbr wa wo wa fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_9 cv fxporderlem_2 wcel wa fxporderlem_8 cv fxporderlem_3 wcel fxporderlem_10 cv fxporderlem_3 wcel wa wa fxporderlem_7 cv fxporderlem_9 cv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_9 cv wceq fxporderlem_8 cv fxporderlem_10 cv fxporderlem_5 wbr wa wo wa fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_9 cv fxporderlem_10 cv cop fxporderlem_6 wbr fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_9 cv fxporderlem_10 cv cop cop fxporderlem_6 wcel fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_9 cv fxporderlem_10 cv cop cop fxporderlem_0 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel wa fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv wceq fxporderlem_0 cv c2nd cfv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa wo wa fxporderlem_0 fxporderlem_1 copab wcel fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_9 cv fxporderlem_10 cv cop fxporderlem_6 df-br fxporderlem_6 fxporderlem_0 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel wa fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv wceq fxporderlem_0 cv c2nd cfv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa wo wa fxporderlem_0 fxporderlem_1 copab fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_9 cv fxporderlem_10 cv cop cop exporderlem_0 eleq2i bitri fxporderlem_0 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel wa fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv wceq fxporderlem_0 cv c2nd cfv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa wo wa fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel wa fxporderlem_7 cv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_1 cv c1st cfv wceq fxporderlem_8 cv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa wo wa fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_9 cv fxporderlem_2 wcel fxporderlem_10 cv fxporderlem_3 wcel wa wa fxporderlem_7 cv fxporderlem_9 cv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_9 cv wceq fxporderlem_8 cv fxporderlem_10 cv fxporderlem_5 wbr wa wo wa fxporderlem_0 fxporderlem_1 fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_9 cv fxporderlem_10 cv cop fxporderlem_7 cv fxporderlem_8 cv opex fxporderlem_9 cv fxporderlem_10 cv opex fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop wceq fxporderlem_0 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel wa fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel wa fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv wceq fxporderlem_0 cv c2nd cfv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa wo fxporderlem_7 cv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_1 cv c1st cfv wceq fxporderlem_8 cv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa wo fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop wceq fxporderlem_0 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop wceq fxporderlem_0 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop fxporderlem_2 fxporderlem_3 cxp eleq1 fxporderlem_7 cv fxporderlem_8 cv fxporderlem_2 fxporderlem_3 opelxp syl6bb anbi1d fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop wceq fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv wceq fxporderlem_0 cv c2nd cfv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa fxporderlem_7 cv fxporderlem_1 cv c1st cfv wceq fxporderlem_8 cv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop wceq fxporderlem_0 cv c1st cfv fxporderlem_7 cv fxporderlem_1 cv c1st cfv fxporderlem_4 fxporderlem_7 cv fxporderlem_8 cv fxporderlem_0 cv fxporderlem_7 vex fxporderlem_8 vex op1std breq1d fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop wceq fxporderlem_0 cv c1st cfv fxporderlem_1 cv c1st cfv wceq fxporderlem_7 cv fxporderlem_1 cv c1st cfv wceq fxporderlem_0 cv c2nd cfv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr fxporderlem_8 cv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop wceq fxporderlem_0 cv c1st cfv fxporderlem_7 cv fxporderlem_1 cv c1st cfv fxporderlem_7 cv fxporderlem_8 cv fxporderlem_0 cv fxporderlem_7 vex fxporderlem_8 vex op1std eqeq1d fxporderlem_0 cv fxporderlem_7 cv fxporderlem_8 cv cop wceq fxporderlem_0 cv c2nd cfv fxporderlem_8 cv fxporderlem_1 cv c2nd cfv fxporderlem_5 fxporderlem_7 cv fxporderlem_8 cv fxporderlem_0 cv fxporderlem_7 vex fxporderlem_8 vex op2ndd breq1d anbi12d orbi12d anbi12d fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop wceq fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel wa fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_9 cv fxporderlem_2 wcel fxporderlem_10 cv fxporderlem_3 wcel wa wa fxporderlem_7 cv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_1 cv c1st cfv wceq fxporderlem_8 cv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa wo fxporderlem_7 cv fxporderlem_9 cv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_9 cv wceq fxporderlem_8 cv fxporderlem_10 cv fxporderlem_5 wbr wa wo fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop wceq fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_9 cv fxporderlem_2 wcel fxporderlem_10 cv fxporderlem_3 wcel wa fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop wceq fxporderlem_1 cv fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_9 cv fxporderlem_10 cv cop fxporderlem_2 fxporderlem_3 cxp wcel fxporderlem_9 cv fxporderlem_2 wcel fxporderlem_10 cv fxporderlem_3 wcel wa fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop fxporderlem_2 fxporderlem_3 cxp eleq1 fxporderlem_9 cv fxporderlem_10 cv fxporderlem_2 fxporderlem_3 opelxp syl6bb anbi2d fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop wceq fxporderlem_7 cv fxporderlem_1 cv c1st cfv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_9 cv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_1 cv c1st cfv wceq fxporderlem_8 cv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr wa fxporderlem_7 cv fxporderlem_9 cv wceq fxporderlem_8 cv fxporderlem_10 cv fxporderlem_5 wbr wa fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop wceq fxporderlem_1 cv c1st cfv fxporderlem_9 cv fxporderlem_7 cv fxporderlem_4 fxporderlem_9 cv fxporderlem_10 cv fxporderlem_1 cv fxporderlem_9 vex fxporderlem_10 vex op1std breq2d fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop wceq fxporderlem_7 cv fxporderlem_1 cv c1st cfv wceq fxporderlem_7 cv fxporderlem_9 cv wceq fxporderlem_8 cv fxporderlem_1 cv c2nd cfv fxporderlem_5 wbr fxporderlem_8 cv fxporderlem_10 cv fxporderlem_5 wbr fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop wceq fxporderlem_1 cv c1st cfv fxporderlem_9 cv fxporderlem_7 cv fxporderlem_9 cv fxporderlem_10 cv fxporderlem_1 cv fxporderlem_9 vex fxporderlem_10 vex op1std eqeq2d fxporderlem_1 cv fxporderlem_9 cv fxporderlem_10 cv cop wceq fxporderlem_1 cv c2nd cfv fxporderlem_10 cv fxporderlem_8 cv fxporderlem_5 fxporderlem_9 cv fxporderlem_10 cv fxporderlem_1 cv fxporderlem_9 vex fxporderlem_10 vex op2ndd breq2d anbi12d orbi12d anbi12d opelopab fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel wa fxporderlem_9 cv fxporderlem_2 wcel fxporderlem_10 cv fxporderlem_3 wcel wa wa fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_9 cv fxporderlem_2 wcel wa fxporderlem_8 cv fxporderlem_3 wcel fxporderlem_10 cv fxporderlem_3 wcel wa wa fxporderlem_7 cv fxporderlem_9 cv fxporderlem_4 wbr fxporderlem_7 cv fxporderlem_9 cv wceq fxporderlem_8 cv fxporderlem_10 cv fxporderlem_5 wbr wa wo fxporderlem_7 cv fxporderlem_2 wcel fxporderlem_8 cv fxporderlem_3 wcel fxporderlem_9 cv fxporderlem_2 wcel fxporderlem_10 cv fxporderlem_3 wcel an4 anbi1i 3bitri $.
$}
$( A lexicographical ordering of two posets.  (Contributed by Scott Fenton,
       16-Mar-2011.)  (Revised by Mario Carneiro, 7-Mar-2013.) $)
${
	$v x $.
	$v y $.
	$v v $.
	$v u $.
	$v t $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v T $.
	$v e $.
	$v f $.
	$v a $.
	$v b $.
	$v c $.
	$v d $.
	$d A a b c d e f t u v x y $.
	$d B a b c d e f t u v x y $.
	$d R a b c d e f t u v x y $.
	$d S a b c d e f t u v x y $.
	$d T a b c d e f t u v $.
	ipoxp_0 $f set v $.
	ipoxp_1 $f set u $.
	ipoxp_2 $f set t $.
	ipoxp_3 $f set e $.
	ipoxp_4 $f set f $.
	ipoxp_5 $f set a $.
	ipoxp_6 $f set b $.
	ipoxp_7 $f set c $.
	ipoxp_8 $f set d $.
	fpoxp_0 $f set x $.
	fpoxp_1 $f set y $.
	fpoxp_2 $f class A $.
	fpoxp_3 $f class B $.
	fpoxp_4 $f class R $.
	fpoxp_5 $f class S $.
	fpoxp_6 $f class T $.
	epoxp_0 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
	poxp $p |- ( ( R Po A /\ S Po B ) -> T Po ( A X. B ) ) $= fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa ipoxp_0 fpoxp_2 fpoxp_3 cxp wral ipoxp_1 fpoxp_2 fpoxp_3 cxp wral ipoxp_2 fpoxp_2 fpoxp_3 cxp wral fpoxp_2 fpoxp_3 cxp fpoxp_6 wpo fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa ipoxp_0 fpoxp_2 fpoxp_3 cxp wral ipoxp_2 ipoxp_1 fpoxp_2 fpoxp_3 cxp fpoxp_2 fpoxp_3 cxp fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_1 cv fpoxp_2 fpoxp_3 cxp wcel wa wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa ipoxp_0 fpoxp_2 fpoxp_3 cxp fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_1 cv fpoxp_2 fpoxp_3 cxp wcel wa ipoxp_0 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_2 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_1 cv fpoxp_2 fpoxp_3 cxp wcel wa ipoxp_0 cv fpoxp_2 fpoxp_3 cxp wcel fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa ipoxp_2 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_1 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_0 cv fpoxp_2 fpoxp_3 cxp wcel fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_2 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_6 wex ipoxp_5 wex ipoxp_1 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_8 wex ipoxp_7 wex ipoxp_0 cv fpoxp_2 fpoxp_3 cxp wcel ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_4 wex ipoxp_3 wex fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_5 ipoxp_6 ipoxp_2 cv fpoxp_2 fpoxp_3 elxp ipoxp_7 ipoxp_8 ipoxp_1 cv fpoxp_2 fpoxp_3 elxp ipoxp_3 ipoxp_4 ipoxp_0 cv fpoxp_2 fpoxp_3 elxp ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_6 wex ipoxp_5 wex ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_8 wex ipoxp_7 wex ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_4 wex ipoxp_3 wex fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_8 wex ipoxp_7 wex ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_4 wex ipoxp_3 wex fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi wi wi ipoxp_5 ipoxp_6 ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_4 wex ipoxp_3 wex ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_8 wex ipoxp_7 wex fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_8 wex ipoxp_7 wex fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi wi wi ipoxp_3 ipoxp_4 ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_8 wex ipoxp_7 wex ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi wi wi ipoxp_7 ipoxp_8 ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa w3a ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq w3a ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa 3an6 ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq w3a ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa wi ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq w3a fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a wa ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq w3a ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo wa wn ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo wa ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wa ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wi wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a wa ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo wa wn ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo wa ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wa ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wi fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo wa wn ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_6 cv fpoxp_3 wcel wa wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo wn fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr wn ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wn wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo wn fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr wn fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wn fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr wn fpoxp_2 ipoxp_5 cv fpoxp_4 poirr ex fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wn fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel wa ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr ipoxp_5 ipoxp_5 weq fpoxp_3 ipoxp_6 cv fpoxp_5 poirr intnand ex im2anan9 ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa ioran syl6ibr imp intnand 3ad2antr1 ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo wa ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wa ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a wa ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo an4 fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel 3an6 fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a wa fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr wa w3a ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr fpoxp_2 ipoxp_5 cv ipoxp_7 cv ipoxp_3 cv fpoxp_4 potr 3impia orcd 3expia expdimp ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi fpoxp_2 fpoxp_4 wpo ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel w3a wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr ipoxp_7 ipoxp_3 weq ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_7 ipoxp_3 weq ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa ipoxp_7 ipoxp_3 weq ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 cv ipoxp_3 cv ipoxp_5 cv fpoxp_4 breq2 biimpa orcd expcom adantrd adantl jaod ex fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi ipoxp_5 ipoxp_7 weq fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi wi ipoxp_5 ipoxp_7 weq fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi ipoxp_5 ipoxp_7 weq ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wi fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa ipoxp_7 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr ipoxp_7 ipoxp_3 weq fpoxp_3 fpoxp_5 wpo ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel w3a wa ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr fpoxp_3 ipoxp_6 cv ipoxp_8 cv ipoxp_4 cv fpoxp_5 potr expdimp anim2d orim2d ipoxp_5 ipoxp_7 weq ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo ipoxp_5 ipoxp_7 weq ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa ipoxp_7 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa ipoxp_5 cv ipoxp_7 cv ipoxp_3 cv fpoxp_4 breq1 ipoxp_5 ipoxp_7 weq ipoxp_5 ipoxp_3 weq ipoxp_7 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr ipoxp_5 ipoxp_7 ipoxp_3 equequ1 anbi1d orbi12d imbi2d syl5ibr exp3a com12 imp3a jaao imp3a an4s sylan2b ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa w3a ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa fpoxp_2 fpoxp_4 wpo fpoxp_3 fpoxp_5 wpo wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv fpoxp_2 wcel ipoxp_8 cv fpoxp_3 wcel wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel wa ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv fpoxp_2 wcel ipoxp_6 cv fpoxp_3 wcel ipoxp_3 cv fpoxp_2 wcel ipoxp_4 cv fpoxp_3 wcel an4 biimpi 3adant2 adantl jctild adantld syl5bi jca ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq w3a ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi wa ipoxp_5 cv ipoxp_6 cv cop ipoxp_5 cv ipoxp_6 cv cop fpoxp_6 wbr wn ipoxp_5 cv ipoxp_6 cv cop ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 wbr ipoxp_7 cv ipoxp_8 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wa ipoxp_5 cv ipoxp_6 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wi wa ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo wa wn ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo wa ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wa ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wi wa ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq w3a ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_5 cv ipoxp_6 cv cop ipoxp_5 cv ipoxp_6 cv cop fpoxp_6 wbr wn ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr wi ipoxp_5 cv ipoxp_6 cv cop ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 wbr ipoxp_7 cv ipoxp_8 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wa ipoxp_5 cv ipoxp_6 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wi ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr wn ipoxp_5 cv ipoxp_6 cv cop ipoxp_5 cv ipoxp_6 cv cop fpoxp_6 wbr wn wb ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr ipoxp_5 cv ipoxp_6 cv cop ipoxp_5 cv ipoxp_6 cv cop fpoxp_6 wbr ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_2 cv ipoxp_2 cv fpoxp_6 wbr ipoxp_5 cv ipoxp_6 cv cop ipoxp_5 cv ipoxp_6 cv cop fpoxp_6 wbr wb ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop fpoxp_6 breq12 anidms notbid 3ad2ant1 ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq w3a ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr wa ipoxp_5 cv ipoxp_6 cv cop ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 wbr ipoxp_7 cv ipoxp_8 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wa ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr ipoxp_5 cv ipoxp_6 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq w3a ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_5 cv ipoxp_6 cv cop ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 wbr ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr ipoxp_7 cv ipoxp_8 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_2 cv ipoxp_1 cv fpoxp_6 wbr ipoxp_5 cv ipoxp_6 cv cop ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 wbr wb ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 breq12 3adant3 ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_1 cv ipoxp_0 cv fpoxp_6 wbr ipoxp_7 cv ipoxp_8 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wb ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 breq12 3adant1 anbi12d ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop wceq ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop wceq ipoxp_2 cv ipoxp_0 cv fpoxp_6 wbr ipoxp_5 cv ipoxp_6 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wb ipoxp_1 cv ipoxp_7 cv ipoxp_8 cv cop wceq ipoxp_2 cv ipoxp_5 cv ipoxp_6 cv cop ipoxp_0 cv ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 breq12 3adant2 imbi12d anbi12d ipoxp_5 cv ipoxp_6 cv cop ipoxp_5 cv ipoxp_6 cv cop fpoxp_6 wbr wn ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo wa wn ipoxp_5 cv ipoxp_6 cv cop ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 wbr ipoxp_7 cv ipoxp_8 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wa ipoxp_5 cv ipoxp_6 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wi ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo wa ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wa ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wi ipoxp_5 cv ipoxp_6 cv cop ipoxp_5 cv ipoxp_6 cv cop fpoxp_6 wbr ipoxp_5 cv fpoxp_2 wcel ipoxp_5 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_6 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_5 cv fpoxp_4 wbr ipoxp_5 ipoxp_5 weq ipoxp_6 cv ipoxp_6 cv fpoxp_5 wbr wa wo wa fpoxp_0 fpoxp_1 fpoxp_2 fpoxp_3 fpoxp_4 fpoxp_5 fpoxp_6 ipoxp_5 ipoxp_6 ipoxp_5 ipoxp_6 epoxp_0 xporderlem notbii ipoxp_5 cv ipoxp_6 cv cop ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 wbr ipoxp_7 cv ipoxp_8 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr wa ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo wa ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa wa ipoxp_5 cv ipoxp_6 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr ipoxp_5 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_5 ipoxp_3 weq ipoxp_6 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa ipoxp_5 cv ipoxp_6 cv cop ipoxp_7 cv ipoxp_8 cv cop fpoxp_6 wbr ipoxp_5 cv fpoxp_2 wcel ipoxp_7 cv fpoxp_2 wcel wa ipoxp_6 cv fpoxp_3 wcel ipoxp_8 cv fpoxp_3 wcel wa wa ipoxp_5 cv ipoxp_7 cv fpoxp_4 wbr ipoxp_5 ipoxp_7 weq ipoxp_6 cv ipoxp_8 cv fpoxp_5 wbr wa wo wa ipoxp_7 cv ipoxp_8 cv cop ipoxp_3 cv ipoxp_4 cv cop fpoxp_6 wbr ipoxp_7 cv fpoxp_2 wcel ipoxp_3 cv fpoxp_2 wcel wa ipoxp_8 cv fpoxp_3 wcel ipoxp_4 cv fpoxp_3 wcel wa wa ipoxp_7 cv ipoxp_3 cv fpoxp_4 wbr ipoxp_7 ipoxp_3 weq ipoxp_8 cv ipoxp_4 cv fpoxp_5 wbr wa wo wa fpoxp_0 fpoxp_1 fpoxp_2 fpoxp_3 fpoxp_4 fpoxp_5 fpoxp_6 ipoxp_5 ipoxp_6 ipoxp_7 ipoxp_8 epoxp_0 xporderlem fpoxp_0 fpoxp_1 fpoxp_2 fpoxp_3 fpoxp_4 fpoxp_5 fpoxp_6 ipoxp_7 ipoxp_8 ipoxp_3 ipoxp_4 epoxp_0 xporderlem anbi12i fpoxp_0 fpoxp_1 fpoxp_2 fpoxp_3 fpoxp_4 fpoxp_5 fpoxp_6 ipoxp_5 ipoxp_6 ipoxp_3 ipoxp_4 epoxp_0 xporderlem imbi12i anbi12i syl6bb syl5ibr exp3acom23 imp sylbi 3exp com3l exlimivv com3l exlimivv com3l exlimivv 3imp syl3anb 3expia com3r imp ralrimiv ralrimivva ipoxp_2 ipoxp_1 ipoxp_0 fpoxp_2 fpoxp_3 cxp fpoxp_6 df-po sylibr $.
$}
$( A lexicographical ordering of two strictly ordered classes.
       (Contributed by Scott Fenton, 17-Mar-2011.)  (Revised by Mario Carneiro,
       7-Mar-2013.) $)
${
	$v x $.
	$v y $.
	$v u $.
	$v t $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v T $.
	$v a $.
	$v b $.
	$v c $.
	$v d $.
	$d A a b c d t u x y $.
	$d B a b c d t u x y $.
	$d R a b c d t u x y $.
	$d S a b c d t u x y $.
	$d T a b c d t u $.
	isoxp_0 $f set u $.
	isoxp_1 $f set t $.
	isoxp_2 $f set a $.
	isoxp_3 $f set b $.
	isoxp_4 $f set c $.
	isoxp_5 $f set d $.
	fsoxp_0 $f set x $.
	fsoxp_1 $f set y $.
	fsoxp_2 $f class A $.
	fsoxp_3 $f class B $.
	fsoxp_4 $f class R $.
	fsoxp_5 $f class S $.
	fsoxp_6 $f class T $.
	esoxp_0 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
	soxp $p |- ( ( R Or A /\ S Or B ) -> T Or ( A X. B ) ) $= fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa fsoxp_2 fsoxp_3 cxp fsoxp_6 wpo isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o isoxp_0 fsoxp_2 fsoxp_3 cxp wral isoxp_1 fsoxp_2 fsoxp_3 cxp wral fsoxp_2 fsoxp_3 cxp fsoxp_6 wor fsoxp_2 fsoxp_4 wor fsoxp_2 fsoxp_4 wpo fsoxp_3 fsoxp_5 wpo fsoxp_2 fsoxp_3 cxp fsoxp_6 wpo fsoxp_3 fsoxp_5 wor fsoxp_2 fsoxp_4 sopo fsoxp_3 fsoxp_5 sopo fsoxp_0 fsoxp_1 fsoxp_2 fsoxp_3 fsoxp_4 fsoxp_5 fsoxp_6 esoxp_0 poxp syl2an fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o isoxp_1 isoxp_0 fsoxp_2 fsoxp_3 cxp fsoxp_2 fsoxp_3 cxp isoxp_1 cv fsoxp_2 fsoxp_3 cxp wcel isoxp_0 cv fsoxp_2 fsoxp_3 cxp wcel wa fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o isoxp_1 cv fsoxp_2 fsoxp_3 cxp wcel isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_3 wex isoxp_2 wex isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_5 wex isoxp_4 wex fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi isoxp_0 cv fsoxp_2 fsoxp_3 cxp wcel isoxp_2 isoxp_3 isoxp_1 cv fsoxp_2 fsoxp_3 elxp isoxp_4 isoxp_5 isoxp_0 cv fsoxp_2 fsoxp_3 elxp isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_3 wex isoxp_2 wex isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_5 wex isoxp_4 wex fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_5 wex isoxp_4 wex fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi wi isoxp_2 isoxp_3 isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_5 wex isoxp_4 wex isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa wa fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa wa fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi wi isoxp_4 isoxp_5 isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq wa isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o isoxp_2 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel wa isoxp_4 cv fsoxp_2 wcel isoxp_5 cv fsoxp_3 wcel wa wa fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa w3o isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o wi isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa w3o wi fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor wa isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa w3o fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa w3o fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo w3o isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa w3o fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa wo wn isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wi isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo w3o isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa wo wn isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn wo wa isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq wn wo wa fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa wo wn isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wn isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa wn wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn wo wa isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq wn wo wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa ioran isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wn isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq wn wo isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wn isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wn wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn wo wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa ioran isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn wo isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr ianor anbi2i bitri isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq ianor anbi12i bitri fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn wo wa isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq wn wo isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wo wa isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq wn wo isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wi fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wo fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr w3o isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo wi fsoxp_2 isoxp_2 cv isoxp_4 cv fsoxp_4 solin isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr w3o isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo wo isoxp_2 cv isoxp_4 cv fsoxp_4 wbr wn isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo wi isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr 3orass isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo df-or bitri sylib fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_2 cv isoxp_4 cv wceq wn fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_3 cv isoxp_5 cv fsoxp_5 wbr isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr w3o isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wi fsoxp_3 isoxp_3 cv isoxp_5 cv fsoxp_5 solin isoxp_3 cv isoxp_5 cv fsoxp_5 wbr isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr w3o isoxp_3 cv isoxp_5 cv fsoxp_5 wbr isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wo isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wi isoxp_3 cv isoxp_5 cv fsoxp_5 wbr isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr 3orass isoxp_3 cv isoxp_5 cv fsoxp_5 wbr isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo df-or bitri sylib orim2d im2anan9 isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wo wa isoxp_2 cv isoxp_4 cv wceq wn isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_3 cv isoxp_5 cv wceq wn isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wi isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wo isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr pm2.53 isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa orc syl6 adantr isoxp_3 cv isoxp_5 cv wceq wn isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_3 cv isoxp_5 cv wceq wn isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo isoxp_3 cv isoxp_5 cv wceq wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_5 cv isoxp_3 cv fsoxp_5 wbr isoxp_2 cv isoxp_4 cv wceq wn isoxp_3 cv isoxp_5 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr orel1 orim2d anim2d isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv fsoxp_4 wbr wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_2 cv isoxp_4 cv wceq wn isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wi isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_2 cv isoxp_4 cv wceq wn isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_5 cv isoxp_3 cv fsoxp_5 wbr isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_2 cv isoxp_4 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wi isoxp_2 cv isoxp_4 cv wceq wn isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_2 cv isoxp_4 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr imor biimpri com12 isoxp_2 cv isoxp_4 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr isoxp_2 isoxp_4 equcomi anim1i olcd ex syld isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq wn isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wo isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa orc a1d jaoi imp syl6com jaod syl6 imp3a syl5bi isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo w3o isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa wo isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wo isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa wo wn isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wi isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo df-3or isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa wo isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo df-or bitri sylibr fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa wi fsoxp_2 fsoxp_4 wor fsoxp_3 fsoxp_5 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo pm3.2 ad2ant2l fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa idd fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa wi fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa wa isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel fsoxp_2 fsoxp_4 wor isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa simpr ancomd fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel fsoxp_3 fsoxp_5 wor isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa simpr ancomd isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo pm3.2 syl2an 3orim123d mpd an4s expcom an4s isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa w3o isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr w3o isoxp_2 cv isoxp_3 cv cop isoxp_4 cv isoxp_5 cv cop fsoxp_6 wbr isoxp_2 cv isoxp_3 cv cop isoxp_4 cv isoxp_5 cv cop wceq isoxp_4 cv isoxp_5 cv cop isoxp_2 cv isoxp_3 cv cop fsoxp_6 wbr w3o isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa w3o isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq wa isoxp_1 cv isoxp_0 cv fsoxp_6 wbr isoxp_2 cv isoxp_3 cv cop isoxp_4 cv isoxp_5 cv cop fsoxp_6 wbr isoxp_1 cv isoxp_0 cv wceq isoxp_2 cv isoxp_3 cv cop isoxp_4 cv isoxp_5 cv cop wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr isoxp_4 cv isoxp_5 cv cop isoxp_2 cv isoxp_3 cv cop fsoxp_6 wbr isoxp_1 cv isoxp_2 cv isoxp_3 cv cop isoxp_0 cv isoxp_4 cv isoxp_5 cv cop fsoxp_6 breq12 isoxp_1 cv isoxp_2 cv isoxp_3 cv cop isoxp_0 cv isoxp_4 cv isoxp_5 cv cop eqeq12 isoxp_0 cv isoxp_4 cv isoxp_5 cv cop wceq isoxp_1 cv isoxp_2 cv isoxp_3 cv cop wceq isoxp_0 cv isoxp_1 cv fsoxp_6 wbr isoxp_4 cv isoxp_5 cv cop isoxp_2 cv isoxp_3 cv cop fsoxp_6 wbr wb isoxp_0 cv isoxp_4 cv isoxp_5 cv cop isoxp_1 cv isoxp_2 cv isoxp_3 cv cop fsoxp_6 breq12 ancoms 3orbi123d isoxp_2 cv isoxp_3 cv cop isoxp_4 cv isoxp_5 cv cop fsoxp_6 wbr isoxp_2 cv fsoxp_2 wcel isoxp_4 cv fsoxp_2 wcel wa isoxp_3 cv fsoxp_3 wcel isoxp_5 cv fsoxp_3 wcel wa wa isoxp_2 cv isoxp_4 cv fsoxp_4 wbr isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv fsoxp_5 wbr wa wo wa isoxp_2 cv isoxp_3 cv cop isoxp_4 cv isoxp_5 cv cop wceq isoxp_2 cv isoxp_4 cv wceq isoxp_3 cv isoxp_5 cv wceq wa isoxp_4 cv isoxp_5 cv cop isoxp_2 cv isoxp_3 cv cop fsoxp_6 wbr isoxp_4 cv fsoxp_2 wcel isoxp_2 cv fsoxp_2 wcel wa isoxp_5 cv fsoxp_3 wcel isoxp_3 cv fsoxp_3 wcel wa wa isoxp_4 cv isoxp_2 cv fsoxp_4 wbr isoxp_4 cv isoxp_2 cv wceq isoxp_5 cv isoxp_3 cv fsoxp_5 wbr wa wo wa fsoxp_0 fsoxp_1 fsoxp_2 fsoxp_3 fsoxp_4 fsoxp_5 fsoxp_6 isoxp_2 isoxp_3 isoxp_4 isoxp_5 esoxp_0 xporderlem isoxp_2 cv isoxp_3 cv isoxp_4 cv isoxp_5 cv isoxp_2 vex isoxp_3 vex opth fsoxp_0 fsoxp_1 fsoxp_2 fsoxp_3 fsoxp_4 fsoxp_5 fsoxp_6 isoxp_4 isoxp_5 isoxp_2 isoxp_3 esoxp_0 xporderlem 3orbi123i syl6bb biimprcd syl6 com3r imp an4s expcom exlimivv com12 exlimivv imp syl2anb com12 ralrimivv isoxp_1 isoxp_0 fsoxp_2 fsoxp_3 cxp fsoxp_6 df-so sylanbrc $.
$}
$( A lexicographical ordering of two well-ordered classes.  (Contributed by
       Scott Fenton, 17-Mar-2011.)  (Revised by Mario Carneiro, 7-Mar-2013.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v T $.
	$d A x y $.
	$d B x y $.
	$d R x y $.
	$d S x y $.
	fwexp_0 $f set x $.
	fwexp_1 $f set y $.
	fwexp_2 $f class A $.
	fwexp_3 $f class B $.
	fwexp_4 $f class R $.
	fwexp_5 $f class S $.
	fwexp_6 $f class T $.
	ewexp_0 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
	wexp $p |- ( ( R We A /\ S We B ) -> T We ( A X. B ) ) $= fwexp_2 fwexp_4 wwe fwexp_3 fwexp_5 wwe wa fwexp_2 fwexp_3 cxp fwexp_6 wfr fwexp_2 fwexp_3 cxp fwexp_6 wor fwexp_2 fwexp_3 cxp fwexp_6 wwe fwexp_2 fwexp_4 wwe fwexp_2 fwexp_4 wfr fwexp_3 fwexp_5 wfr fwexp_2 fwexp_3 cxp fwexp_6 wfr fwexp_3 fwexp_5 wwe fwexp_2 fwexp_4 wefr fwexp_3 fwexp_5 wefr fwexp_0 fwexp_1 fwexp_2 fwexp_3 fwexp_4 fwexp_5 fwexp_6 ewexp_0 frxp syl2an fwexp_2 fwexp_4 wwe fwexp_2 fwexp_4 wor fwexp_3 fwexp_5 wor fwexp_2 fwexp_3 cxp fwexp_6 wor fwexp_3 fwexp_5 wwe fwexp_2 fwexp_4 weso fwexp_3 fwexp_5 weso fwexp_0 fwexp_1 fwexp_2 fwexp_3 fwexp_4 fwexp_5 fwexp_6 ewexp_0 soxp syl2an fwexp_2 fwexp_3 cxp fwexp_6 df-we sylanbrc $.
$}
$( Lemma for ~ fnwe .  (Contributed by Mario Carneiro, 10-Mar-2013.)
         (Revised by Mario Carneiro, 18-Nov-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v u $.
	$v A $.
	$v B $.
	$v Q $.
	$v R $.
	$v S $.
	$v T $.
	$v F $.
	$v G $.
	$d u v w x y z A $.
	$d u v w x y z B $.
	$d w x y G $.
	$d w x z ph $.
	$d u v w x y z F $.
	$d w x y Q $.
	$d u v w x y R $.
	$d u v w x y S $.
	$d w T $.
	ffnwelem_0 $f wff ph $.
	ffnwelem_1 $f set x $.
	ffnwelem_2 $f set y $.
	ffnwelem_3 $f set z $.
	ffnwelem_4 $f set w $.
	ffnwelem_5 $f set v $.
	ffnwelem_6 $f set u $.
	ffnwelem_7 $f class A $.
	ffnwelem_8 $f class B $.
	ffnwelem_9 $f class Q $.
	ffnwelem_10 $f class R $.
	ffnwelem_11 $f class S $.
	ffnwelem_12 $f class T $.
	ffnwelem_13 $f class F $.
	ffnwelem_14 $f class G $.
	efnwelem_0 $e |- T = { <. x , y >. | ( ( x e. A /\ y e. A ) /\ ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x S y ) ) ) } $.
	efnwelem_1 $e |- ( ph -> F : A --> B ) $.
	efnwelem_2 $e |- ( ph -> R We B ) $.
	efnwelem_3 $e |- ( ph -> S We A ) $.
	efnwelem_4 $e |- ( ph -> ( F " w ) e. _V ) $.
	efnwelem_5 $e |- Q = { <. u , v >. | ( ( u e. ( B X. A ) /\ v e. ( B X. A ) ) /\ ( ( 1st ` u ) R ( 1st ` v ) \/ ( ( 1st ` u ) = ( 1st ` v ) /\ ( 2nd ` u ) S ( 2nd ` v ) ) ) ) } $.
	efnwelem_6 $e |- G = ( z e. A |-> <. ( F ` z ) , z >. ) $.
	fnwelem $p |- ( ph -> T We A ) $= ffnwelem_0 ffnwelem_14 crn ffnwelem_9 wwe ffnwelem_7 ffnwelem_12 wwe ffnwelem_0 ffnwelem_14 crn ffnwelem_8 ffnwelem_7 cxp wss ffnwelem_8 ffnwelem_7 cxp ffnwelem_9 wwe ffnwelem_14 crn ffnwelem_9 wwe ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_14 crn ffnwelem_8 ffnwelem_7 cxp wss efnwelem_1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 ffnwelem_7 ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel wa ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_3 cv ffnwelem_7 wcel ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_7 ffnwelem_8 ffnwelem_3 cv ffnwelem_13 ffvelrn ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel simpr ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_8 ffnwelem_7 opelxp sylanbrc efnwelem_6 fmptd ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 frn 3syl ffnwelem_0 ffnwelem_8 ffnwelem_10 wwe ffnwelem_7 ffnwelem_11 wwe ffnwelem_8 ffnwelem_7 cxp ffnwelem_9 wwe efnwelem_2 efnwelem_3 ffnwelem_6 ffnwelem_5 ffnwelem_8 ffnwelem_7 ffnwelem_10 ffnwelem_11 ffnwelem_9 efnwelem_5 wexp syl2anc ffnwelem_14 crn ffnwelem_8 ffnwelem_7 cxp ffnwelem_9 wess sylc ffnwelem_0 ffnwelem_7 ffnwelem_14 crn ffnwelem_12 ffnwelem_9 ffnwelem_14 ccnv ccnv wiso ffnwelem_14 ccnv ccnv ffnwelem_4 cv cima cvv wcel ffnwelem_4 wal ffnwelem_14 crn ffnwelem_9 wwe ffnwelem_7 ffnwelem_12 wwe wi ffnwelem_0 ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_12 ffnwelem_14 ccnv wiso ffnwelem_7 ffnwelem_14 crn ffnwelem_12 ffnwelem_9 ffnwelem_14 ccnv ccnv wiso ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_14 crn ffnwelem_7 ffnwelem_14 ccnv wf1o ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_12 ffnwelem_14 ccnv wiso efnwelem_1 ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 ffnwelem_7 ffnwelem_14 crn ffnwelem_14 wf1o ffnwelem_14 crn ffnwelem_7 ffnwelem_14 ccnv wf1o ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 efnwelem_1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_2 ffnwelem_7 wral ffnwelem_1 ffnwelem_7 wral ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 ffnwelem_7 ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel wa ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_3 cv ffnwelem_7 wcel ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_7 ffnwelem_8 ffnwelem_3 cv ffnwelem_13 ffvelrn ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel simpr ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_8 ffnwelem_7 opelxp sylanbrc efnwelem_6 fmptd ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_2 ffnwelem_7 wral ffnwelem_1 ffnwelem_7 wral ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_2 cv wceq ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_3 ffnwelem_1 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_1 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_1 cv wceq id opeq12d efnwelem_6 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv opex fvmpt ffnwelem_3 ffnwelem_2 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_2 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_2 cv wceq id opeq12d efnwelem_6 ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv opex fvmpt eqeqan12d ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_1 cv ffnwelem_13 fvex ffnwelem_1 vex opth simprbi syl6bi rgen2a a1i ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 dff13 sylanbrc syl ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 f1f1orn ffnwelem_7 ffnwelem_14 crn ffnwelem_14 f1ocnv 3syl ffnwelem_14 crn ffnwelem_7 ffnwelem_14 ccnv wf1o ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_12 ffnwelem_14 ccnv wiso ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr wa ffnwelem_1 ffnwelem_2 copab ffnwelem_14 ccnv wiso ffnwelem_1 ffnwelem_2 ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr wa ffnwelem_1 ffnwelem_2 copab ffnwelem_14 ccnv ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr wa ffnwelem_1 ffnwelem_2 copab eqid f1oiso2 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_12 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr wa ffnwelem_1 ffnwelem_2 copab wceq ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_12 ffnwelem_14 ccnv wiso ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr wa ffnwelem_1 ffnwelem_2 copab ffnwelem_14 ccnv wiso wb ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_12 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo wa ffnwelem_1 ffnwelem_2 copab ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr wa ffnwelem_1 ffnwelem_2 copab efnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo wa ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr wa ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_9 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_9 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_9 wbr wb ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_9 wbr wb ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 ffnwelem_7 ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel wa ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_3 cv ffnwelem_7 wcel ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_7 ffnwelem_8 ffnwelem_3 cv ffnwelem_13 ffvelrn ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel simpr ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_8 ffnwelem_7 opelxp sylanbrc efnwelem_6 fmptd ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_9 ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_1 cv ffnwelem_14 ccnv ccnv ffnwelem_14 ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_14 wrel ffnwelem_14 ccnv ccnv ffnwelem_14 wceq ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 frel ffnwelem_14 dfrel2 sylib fveq1d ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_2 cv ffnwelem_14 ccnv ccnv ffnwelem_14 ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_14 wrel ffnwelem_14 ccnv ccnv ffnwelem_14 wceq ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 frel ffnwelem_14 dfrel2 sylib fveq1d breq12d syl adantr ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_9 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_9 wbr wb ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_9 ffnwelem_3 ffnwelem_1 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_1 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_1 cv wceq id opeq12d efnwelem_6 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv opex fvmpt ffnwelem_3 ffnwelem_2 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_2 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_2 cv wceq id opeq12d efnwelem_6 ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv opex fvmpt breqan12d adantl ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_2 cv ffnwelem_7 wcel wa wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_9 wbr ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_2 cv ffnwelem_7 wcel wa wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_2 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_7 ffnwelem_8 ffnwelem_1 cv ffnwelem_13 ffvelrn ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_7 wcel simpr jca ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_2 cv ffnwelem_7 wcel ffnwelem_7 ffnwelem_8 ffnwelem_2 cv ffnwelem_13 ffvelrn ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_2 cv ffnwelem_7 wcel simpr jca anim12dan biantrurd ffnwelem_6 cv ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_5 cv ffnwelem_8 ffnwelem_7 cxp wcel wa ffnwelem_6 cv c1st cfv ffnwelem_5 cv c1st cfv ffnwelem_10 wbr ffnwelem_6 cv c1st cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_6 cv c2nd cfv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr wa wo wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_5 cv ffnwelem_8 ffnwelem_7 cxp wcel wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_1 cv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr wa wo wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_2 cv ffnwelem_7 wcel wa wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo wa ffnwelem_6 ffnwelem_5 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_9 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv opex ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv opex ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_6 cv ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_5 cv ffnwelem_8 ffnwelem_7 cxp wcel wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_5 cv ffnwelem_8 ffnwelem_7 cxp wcel wa ffnwelem_6 cv c1st cfv ffnwelem_5 cv c1st cfv ffnwelem_10 wbr ffnwelem_6 cv c1st cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_6 cv c2nd cfv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr wa wo ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_1 cv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr wa wo ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_6 cv ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_5 cv ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_6 cv ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_8 ffnwelem_7 cxp eleq1 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_8 ffnwelem_7 opelxp syl6bb anbi1d ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_6 cv c1st cfv ffnwelem_5 cv c1st cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv ffnwelem_10 wbr ffnwelem_6 cv c1st cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_6 cv c2nd cfv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_1 cv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr wa ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_6 cv c1st cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv ffnwelem_10 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 fvex ffnwelem_1 vex op1std breq1d ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_6 cv c1st cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_6 cv c2nd cfv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr ffnwelem_1 cv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_6 cv c1st cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 fvex ffnwelem_1 vex op1std eqeq1d ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_6 cv c2nd cfv ffnwelem_1 cv ffnwelem_5 cv c2nd cfv ffnwelem_11 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_6 cv ffnwelem_1 cv ffnwelem_13 fvex ffnwelem_1 vex op2ndd breq1d anbi12d orbi12d anbi12d ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_5 cv ffnwelem_8 ffnwelem_7 cxp wcel wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_2 cv ffnwelem_7 wcel wa wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_1 cv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr wa wo ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa wo ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_5 cv ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_1 cv ffnwelem_7 wcel wa ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_5 cv ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_8 ffnwelem_7 cxp eleq1 ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_8 ffnwelem_7 opelxp syl6bb anbi2d ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_10 wbr ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_1 cv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr wa ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_5 cv c1st cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_10 ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 fvex ffnwelem_2 vex op1std breq2d ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_5 cv c1st cfv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_5 cv c2nd cfv ffnwelem_11 wbr ffnwelem_1 cv ffnwelem_2 cv ffnwelem_11 wbr ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_5 cv c1st cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 fvex ffnwelem_2 vex op1std eqeq2d ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_5 cv c2nd cfv ffnwelem_2 cv ffnwelem_1 cv ffnwelem_11 ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_5 cv ffnwelem_2 cv ffnwelem_13 fvex ffnwelem_2 vex op2ndd breq2d anbi12d orbi12d anbi12d efnwelem_5 brab syl6rbbr 3bitrrd pm5.32da opabbidv syl5eq ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_12 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_2 cv ffnwelem_14 ccnv ccnv cfv ffnwelem_9 wbr wa ffnwelem_1 ffnwelem_2 copab ffnwelem_14 ccnv isoeq3 syl syl5ibr sylc ffnwelem_14 crn ffnwelem_7 ffnwelem_9 ffnwelem_12 ffnwelem_14 ccnv isocnv syl ffnwelem_0 ffnwelem_14 ccnv ccnv ffnwelem_4 cv cima cvv wcel ffnwelem_4 ffnwelem_0 ffnwelem_14 ccnv ccnv ffnwelem_4 cv cima ffnwelem_14 ffnwelem_4 cv cima cvv ffnwelem_14 ffnwelem_4 cv imacnvcnv ffnwelem_0 ffnwelem_14 ffnwelem_4 cv cima ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp wss ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp cvv wcel ffnwelem_14 ffnwelem_4 cv cima cvv wcel ffnwelem_0 ffnwelem_14 ffnwelem_4 cv cima ffnwelem_14 ffnwelem_14 ffnwelem_4 cv cres cdm cima ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp ffnwelem_14 ffnwelem_4 cv imadmres ffnwelem_0 ffnwelem_14 ffnwelem_14 ffnwelem_4 cv cres cdm cima ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp wss ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp wcel ffnwelem_1 ffnwelem_14 ffnwelem_4 cv cres cdm wral ffnwelem_0 ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp wcel ffnwelem_1 ffnwelem_14 ffnwelem_4 cv cres cdm ffnwelem_1 cv ffnwelem_14 ffnwelem_4 cv cres cdm wcel ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp wcel ffnwelem_1 cv ffnwelem_4 cv ffnwelem_14 cdm ffnwelem_14 ffnwelem_4 cv cres cdm ffnwelem_14 ffnwelem_4 cv dmres elin2 ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop wceq ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_1 cv ffnwelem_14 cdm ffnwelem_7 ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel simprr ffnwelem_0 ffnwelem_14 cdm ffnwelem_7 wceq ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 ffnwelem_14 cdm ffnwelem_7 wceq efnwelem_1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_2 ffnwelem_7 wral ffnwelem_1 ffnwelem_7 wral ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 ffnwelem_7 ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel wa ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_3 cv ffnwelem_7 wcel ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_7 ffnwelem_8 ffnwelem_3 cv ffnwelem_13 ffvelrn ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel simpr ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_8 ffnwelem_7 opelxp sylanbrc efnwelem_6 fmptd ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_2 ffnwelem_7 wral ffnwelem_1 ffnwelem_7 wral ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_2 cv wceq ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_3 ffnwelem_1 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_1 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_1 cv wceq id opeq12d efnwelem_6 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv opex fvmpt ffnwelem_3 ffnwelem_2 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_2 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_2 cv wceq id opeq12d efnwelem_6 ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv opex fvmpt eqeqan12d ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_1 cv ffnwelem_13 fvex ffnwelem_1 vex opth simprbi syl6bi rgen2a a1i ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 dff13 sylanbrc ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 f1dm 3syl adantr eleqtrd ffnwelem_3 ffnwelem_1 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_1 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_1 cv wceq id opeq12d efnwelem_6 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv opex fvmpt syl ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_13 ffnwelem_4 cv cima wcel ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp wcel ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_13 ffnwelem_13 ffnwelem_4 cv cres cdm cima ffnwelem_13 ffnwelem_4 cv cima ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_13 ffnwelem_7 wfn ffnwelem_13 ffnwelem_4 cv cres cdm ffnwelem_7 wss ffnwelem_1 cv ffnwelem_13 ffnwelem_4 cv cres cdm wcel ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_13 ffnwelem_13 ffnwelem_4 cv cres cdm cima wcel ffnwelem_0 ffnwelem_13 ffnwelem_7 wfn ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_13 ffnwelem_7 wfn efnwelem_1 ffnwelem_7 ffnwelem_8 ffnwelem_13 ffn syl adantr ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_13 ffnwelem_4 cv cres cdm ffnwelem_4 cv ffnwelem_13 cdm cin ffnwelem_7 ffnwelem_13 ffnwelem_4 cv dmres ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_13 cdm ffnwelem_4 cv ffnwelem_13 cdm cin ffnwelem_7 ffnwelem_4 cv ffnwelem_13 cdm inss2 ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_13 ffnwelem_7 wfn ffnwelem_13 cdm ffnwelem_7 wceq ffnwelem_0 ffnwelem_13 ffnwelem_7 wfn ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_13 ffnwelem_7 wfn efnwelem_1 ffnwelem_7 ffnwelem_8 ffnwelem_13 ffn syl adantr ffnwelem_7 ffnwelem_13 fndm syl syl5sseq syl5eqss ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_13 cdm wcel ffnwelem_1 cv ffnwelem_13 ffnwelem_4 cv cres cdm wcel ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel simprl ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_1 cv ffnwelem_7 ffnwelem_13 cdm ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_1 cv ffnwelem_14 cdm ffnwelem_7 ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel simprr ffnwelem_0 ffnwelem_14 cdm ffnwelem_7 wceq ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 ffnwelem_14 cdm ffnwelem_7 wceq efnwelem_1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_2 ffnwelem_7 wral ffnwelem_1 ffnwelem_7 wral ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 ffnwelem_7 ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel wa ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_3 cv ffnwelem_7 wcel ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_7 ffnwelem_8 ffnwelem_3 cv ffnwelem_13 ffvelrn ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel simpr ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_8 ffnwelem_7 opelxp sylanbrc efnwelem_6 fmptd ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_2 ffnwelem_7 wral ffnwelem_1 ffnwelem_7 wral ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_2 cv wceq ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_3 ffnwelem_1 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_1 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_1 cv wceq id opeq12d efnwelem_6 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv opex fvmpt ffnwelem_3 ffnwelem_2 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_2 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_2 cv wceq id opeq12d efnwelem_6 ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv opex fvmpt eqeqan12d ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_1 cv ffnwelem_13 fvex ffnwelem_1 vex opth simprbi syl6bi rgen2a a1i ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 dff13 sylanbrc ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 f1dm 3syl adantr eleqtrd ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa wa ffnwelem_13 ffnwelem_7 wfn ffnwelem_13 cdm ffnwelem_7 wceq ffnwelem_0 ffnwelem_13 ffnwelem_7 wfn ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel wa ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_13 ffnwelem_7 wfn efnwelem_1 ffnwelem_7 ffnwelem_8 ffnwelem_13 ffn syl adantr ffnwelem_7 ffnwelem_13 fndm syl eleqtrrd ffnwelem_1 cv ffnwelem_4 cv ffnwelem_13 cdm ffnwelem_13 ffnwelem_4 cv cres cdm ffnwelem_13 ffnwelem_4 cv dmres elin2 sylanbrc ffnwelem_7 ffnwelem_13 ffnwelem_4 cv cres cdm ffnwelem_13 ffnwelem_1 cv fnfvima syl3anc ffnwelem_13 ffnwelem_4 cv imadmres syl6eleq ffnwelem_0 ffnwelem_1 cv ffnwelem_4 cv wcel ffnwelem_1 cv ffnwelem_14 cdm wcel simprl ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv opelxpi syl2anc eqeltrd sylan2b ralrimiva ffnwelem_0 ffnwelem_14 wfun ffnwelem_14 ffnwelem_4 cv cres cdm ffnwelem_14 cdm wss ffnwelem_14 ffnwelem_14 ffnwelem_4 cv cres cdm cima ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp wss ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp wcel ffnwelem_1 ffnwelem_14 ffnwelem_4 cv cres cdm wral wb ffnwelem_0 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 ffnwelem_14 wfun efnwelem_1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_2 ffnwelem_7 wral ffnwelem_1 ffnwelem_7 wral ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 wf1 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 ffnwelem_7 ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel wa ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_8 wcel ffnwelem_3 cv ffnwelem_7 wcel ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_8 ffnwelem_7 cxp wcel ffnwelem_7 ffnwelem_8 ffnwelem_3 cv ffnwelem_13 ffvelrn ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_3 cv ffnwelem_7 wcel simpr ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_8 ffnwelem_7 opelxp sylanbrc efnwelem_6 fmptd ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_2 ffnwelem_7 wral ffnwelem_1 ffnwelem_7 wral ffnwelem_7 ffnwelem_8 ffnwelem_13 wf ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq wi ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel wa ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_14 cfv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_2 cv wceq ffnwelem_1 cv ffnwelem_7 wcel ffnwelem_2 cv ffnwelem_7 wcel ffnwelem_1 cv ffnwelem_14 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_14 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_3 ffnwelem_1 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_1 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_3 cv ffnwelem_1 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_1 cv wceq id opeq12d efnwelem_6 ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv opex fvmpt ffnwelem_3 ffnwelem_2 cv ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_3 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop ffnwelem_7 ffnwelem_14 ffnwelem_3 cv ffnwelem_2 cv wceq ffnwelem_3 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_3 cv ffnwelem_2 cv ffnwelem_13 fveq2 ffnwelem_3 cv ffnwelem_2 cv wceq id opeq12d efnwelem_6 ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv opex fvmpt eqeqan12d ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv cop ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv cop wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_13 cfv wceq ffnwelem_1 cv ffnwelem_2 cv wceq ffnwelem_1 cv ffnwelem_13 cfv ffnwelem_1 cv ffnwelem_2 cv ffnwelem_13 cfv ffnwelem_2 cv ffnwelem_1 cv ffnwelem_13 fvex ffnwelem_1 vex opth simprbi syl6bi rgen2a a1i ffnwelem_1 ffnwelem_2 ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 dff13 sylanbrc ffnwelem_7 ffnwelem_8 ffnwelem_7 cxp ffnwelem_14 f1fun 3syl ffnwelem_14 ffnwelem_4 cv cres ffnwelem_14 wss ffnwelem_14 ffnwelem_4 cv cres cdm ffnwelem_14 cdm wss ffnwelem_14 ffnwelem_4 cv resss ffnwelem_14 ffnwelem_4 cv cres ffnwelem_14 dmss ax-mp ffnwelem_1 ffnwelem_14 ffnwelem_4 cv cres cdm ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp ffnwelem_14 funimass4 sylancl mpbird syl5eqssr ffnwelem_0 ffnwelem_13 ffnwelem_4 cv cima cvv wcel ffnwelem_4 cv cvv wcel ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp cvv wcel efnwelem_4 ffnwelem_4 vex ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cvv cvv xpexg sylancl ffnwelem_14 ffnwelem_4 cv cima ffnwelem_13 ffnwelem_4 cv cima ffnwelem_4 cv cxp cvv ssexg syl2anc syl5eqel alrimiv ffnwelem_4 ffnwelem_7 ffnwelem_14 crn ffnwelem_12 ffnwelem_9 ffnwelem_14 ccnv ccnv isowe2 syl2anc mpd $.
$}
$( A variant on lexicographic order, which sorts first by some function of
       the base set, and then by a "backup" well-ordering when the function
       value is equal on both elements.  (Contributed by Mario Carneiro,
       10-Mar-2013.)  (Revised by Mario Carneiro, 18-Nov-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v v $.
	$v u $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v T $.
	$v F $.
	$d u v w x y z A $.
	$d u v w x y z B $.
	$d w x y $.
	$d w x z ph $.
	$d u v w x y z F $.
	$d w x y $.
	$d u v w x y R $.
	$d u v w x y S $.
	$d w T $.
	ifnwe_0 $f set z $.
	ifnwe_1 $f set v $.
	ifnwe_2 $f set u $.
	ffnwe_0 $f wff ph $.
	ffnwe_1 $f set x $.
	ffnwe_2 $f set y $.
	ffnwe_3 $f set w $.
	ffnwe_4 $f class A $.
	ffnwe_5 $f class B $.
	ffnwe_6 $f class R $.
	ffnwe_7 $f class S $.
	ffnwe_8 $f class T $.
	ffnwe_9 $f class F $.
	efnwe_0 $e |- T = { <. x , y >. | ( ( x e. A /\ y e. A ) /\ ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x S y ) ) ) } $.
	efnwe_1 $e |- ( ph -> F : A --> B ) $.
	efnwe_2 $e |- ( ph -> R We B ) $.
	efnwe_3 $e |- ( ph -> S We A ) $.
	efnwe_4 $e |- ( ph -> ( F " w ) e. _V ) $.
	fnwe $p |- ( ph -> T We A ) $= ffnwe_0 ffnwe_1 ffnwe_2 ifnwe_0 ffnwe_3 ifnwe_1 ifnwe_2 ffnwe_4 ffnwe_5 ifnwe_2 cv ffnwe_5 ffnwe_4 cxp wcel ifnwe_1 cv ffnwe_5 ffnwe_4 cxp wcel wa ifnwe_2 cv c1st cfv ifnwe_1 cv c1st cfv ffnwe_6 wbr ifnwe_2 cv c1st cfv ifnwe_1 cv c1st cfv wceq ifnwe_2 cv c2nd cfv ifnwe_1 cv c2nd cfv ffnwe_7 wbr wa wo wa ifnwe_2 ifnwe_1 copab ffnwe_6 ffnwe_7 ffnwe_8 ffnwe_9 ifnwe_0 ffnwe_4 ifnwe_0 cv ffnwe_9 cfv ifnwe_0 cv cop cmpt efnwe_0 efnwe_1 efnwe_2 efnwe_3 efnwe_4 ifnwe_2 cv ffnwe_5 ffnwe_4 cxp wcel ifnwe_1 cv ffnwe_5 ffnwe_4 cxp wcel wa ifnwe_2 cv c1st cfv ifnwe_1 cv c1st cfv ffnwe_6 wbr ifnwe_2 cv c1st cfv ifnwe_1 cv c1st cfv wceq ifnwe_2 cv c2nd cfv ifnwe_1 cv c2nd cfv ffnwe_7 wbr wa wo wa ifnwe_2 ifnwe_1 copab eqid ifnwe_0 ffnwe_4 ifnwe_0 cv ffnwe_9 cfv ifnwe_0 cv cop cmpt eqid fnwelem $.
$}
$( Condition for the well-order in ~ fnwe to be set-like.  (Contributed by
       Mario Carneiro, 25-Jun-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v u $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v T $.
	$v F $.
	$d x y z A $.
	$d u w B $.
	$d u w x y F $.
	$d w z ph $.
	$d u w x y R $.
	$d u z $.
	$d x y S $.
	$d w z T $.
	ifnse_0 $f set z $.
	ifnse_1 $f set u $.
	ffnse_0 $f wff ph $.
	ffnse_1 $f set x $.
	ffnse_2 $f set y $.
	ffnse_3 $f set w $.
	ffnse_4 $f class A $.
	ffnse_5 $f class B $.
	ffnse_6 $f class R $.
	ffnse_7 $f class S $.
	ffnse_8 $f class T $.
	ffnse_9 $f class F $.
	efnse_0 $e |- T = { <. x , y >. | ( ( x e. A /\ y e. A ) /\ ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x S y ) ) ) } $.
	efnse_1 $e |- ( ph -> F : A --> B ) $.
	efnse_2 $e |- ( ph -> R Se B ) $.
	efnse_3 $e |- ( ph -> ( `' F " w ) e. _V ) $.
	fnse $p |- ( ph -> T Se A ) $= ffnse_0 ffnse_4 ffnse_8 ccnv ifnse_0 cv csn cima cin cvv wcel ifnse_0 ffnse_4 wral ffnse_4 ffnse_8 wse ffnse_0 ffnse_4 ffnse_8 ccnv ifnse_0 cv csn cima cin cvv wcel ifnse_0 ffnse_4 ffnse_0 ifnse_0 cv ffnse_4 wcel wa ffnse_4 ffnse_8 ccnv ifnse_0 cv csn cima cin ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima wss ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima cvv wcel ffnse_4 ffnse_8 ccnv ifnse_0 cv csn cima cin cvv wcel ffnse_0 ffnse_4 ffnse_8 ccnv ifnse_0 cv csn cima cin ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima wss ifnse_0 cv ffnse_4 wcel ffnse_0 ffnse_4 ffnse_8 ccnv ifnse_0 cv csn cima cin ffnse_8 ccnv ifnse_0 cv csn cima ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima ffnse_4 ffnse_8 ccnv ifnse_0 cv csn cima inss2 ffnse_0 ffnse_3 ffnse_8 ccnv ifnse_0 cv csn cima ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima ffnse_3 cv ffnse_8 ccnv ifnse_0 cv csn cima wcel ffnse_3 cv ifnse_0 cv ffnse_8 wbr ffnse_0 ffnse_3 cv ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima wcel ifnse_0 cv cvv wcel ffnse_3 cv ffnse_8 ccnv ifnse_0 cv csn cima wcel ffnse_3 cv ifnse_0 cv ffnse_8 wbr wb ifnse_0 vex ffnse_8 ifnse_0 cv ffnse_3 cv cvv ffnse_3 vex eliniseg ax-mp ffnse_3 cv ifnse_0 cv ffnse_8 wbr ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa wo wa ffnse_0 ffnse_3 cv ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima wcel ffnse_1 cv ffnse_9 cfv ffnse_2 cv ffnse_9 cfv ffnse_6 wbr ffnse_1 cv ffnse_9 cfv ffnse_2 cv ffnse_9 cfv wceq ffnse_1 cv ffnse_2 cv ffnse_7 wbr wa wo ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa wo ffnse_1 ffnse_2 ffnse_3 cv ifnse_0 cv ffnse_4 ffnse_4 ffnse_8 ffnse_1 cv ffnse_3 cv wceq ffnse_2 cv ifnse_0 cv wceq wa ffnse_1 cv ffnse_9 cfv ffnse_2 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_1 cv ffnse_9 cfv ffnse_2 cv ffnse_9 cfv wceq ffnse_1 cv ffnse_2 cv ffnse_7 wbr wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa ffnse_1 cv ffnse_3 cv wceq ffnse_2 cv ifnse_0 cv wceq ffnse_1 cv ffnse_9 cfv ffnse_3 cv ffnse_9 cfv ffnse_2 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 ffnse_1 cv ffnse_3 cv ffnse_9 fveq2 ffnse_2 cv ifnse_0 cv ffnse_9 fveq2 breqan12d ffnse_1 cv ffnse_3 cv wceq ffnse_2 cv ifnse_0 cv wceq wa ffnse_1 cv ffnse_9 cfv ffnse_2 cv ffnse_9 cfv wceq ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_1 cv ffnse_2 cv ffnse_7 wbr ffnse_3 cv ifnse_0 cv ffnse_7 wbr ffnse_1 cv ffnse_3 cv wceq ffnse_2 cv ifnse_0 cv wceq ffnse_1 cv ffnse_9 cfv ffnse_3 cv ffnse_9 cfv ffnse_2 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_1 cv ffnse_3 cv ffnse_9 fveq2 ffnse_2 cv ifnse_0 cv ffnse_9 fveq2 eqeqan12d ffnse_1 cv ffnse_3 cv ffnse_2 cv ifnse_0 cv ffnse_7 breq12 anbi12d orbi12d efnse_0 brab2ga ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa wo ffnse_3 cv ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima wcel ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa wo ffnse_3 cv ffnse_4 wcel ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun wcel wa ffnse_3 cv ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima wcel ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa wo ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun wcel ffnse_3 cv ffnse_4 wcel ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa wo ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab wcel ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv csn wcel wo ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun wcel ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab wcel ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv csn wcel ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa wa ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab wcel ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa wa ffnse_3 cv ffnse_9 cfv ffnse_5 wcel ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab wcel ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr wb ffnse_0 ffnse_3 cv ffnse_4 wcel ffnse_3 cv ffnse_9 cfv ffnse_5 wcel ifnse_0 cv ffnse_4 wcel ffnse_0 ffnse_4 ffnse_5 ffnse_9 wf ffnse_3 cv ffnse_4 wcel ffnse_3 cv ffnse_9 cfv ffnse_5 wcel efnse_1 ffnse_4 ffnse_5 ffnse_3 cv ffnse_9 ffvelrn sylan adantrr ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_3 cv ffnse_9 cfv ffnse_5 ifnse_1 cv ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_6 breq1 elrab3 syl biimprd ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv csn wcel wi ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr wa ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv csn wcel ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv wceq ffnse_3 cv ifnse_0 cv ffnse_7 wbr simpl ffnse_3 cv ffnse_9 cfv ifnse_0 cv ffnse_9 cfv ffnse_3 cv ffnse_9 fvex elsnc sylibr a1i orim12d ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn elun syl6ibr ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel simprl jctild ffnse_0 ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa wa ffnse_9 ffnse_4 wfn ffnse_3 cv ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima wcel ffnse_3 cv ffnse_4 wcel ffnse_3 cv ffnse_9 cfv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun wcel wa wb ffnse_0 ffnse_9 ffnse_4 wfn ffnse_3 cv ffnse_4 wcel ifnse_0 cv ffnse_4 wcel wa ffnse_0 ffnse_4 ffnse_5 ffnse_9 wf ffnse_9 ffnse_4 wfn efnse_1 ffnse_4 ffnse_5 ffnse_9 ffn syl adantr ffnse_4 ffnse_3 cv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun ffnse_9 elpreima syl sylibrd expimpd syl5bi syl5bi ssrdv syl5ss adantr ffnse_0 ifnse_0 cv ffnse_4 wcel ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cvv wcel ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima cvv wcel ffnse_0 ifnse_0 cv ffnse_4 wcel wa ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab cvv wcel ifnse_0 cv ffnse_9 cfv csn cvv wcel ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cvv wcel ffnse_0 ifnse_0 cv ffnse_4 wcel ifnse_0 cv ffnse_9 cfv ffnse_5 wcel ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab cvv wcel ffnse_0 ffnse_4 ffnse_5 ffnse_9 wf ifnse_0 cv ffnse_4 wcel ifnse_0 cv ffnse_9 cfv ffnse_5 wcel efnse_1 ffnse_4 ffnse_5 ifnse_0 cv ffnse_9 ffvelrn sylan ffnse_0 ffnse_5 ffnse_6 wse ifnse_0 cv ffnse_9 cfv ffnse_5 wcel ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab cvv wcel efnse_2 ifnse_1 ffnse_5 ifnse_0 cv ffnse_9 cfv ffnse_6 seex sylan syldan ifnse_0 cv ffnse_9 cfv snex ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cvv cvv unexg sylancl ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cvv wcel ffnse_0 ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima cvv wcel ffnse_0 ffnse_9 ccnv ffnse_3 cv cima cvv wcel wi ffnse_0 ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima cvv wcel wi ffnse_3 ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cvv ffnse_3 cv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun wceq ffnse_9 ccnv ffnse_3 cv cima cvv wcel ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima cvv wcel ffnse_0 ffnse_3 cv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun wceq ffnse_9 ccnv ffnse_3 cv cima ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima cvv ffnse_3 cv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun ffnse_9 ccnv imaeq2 eleq1d imbi2d efnse_3 vtoclg impcom syldan ffnse_4 ffnse_8 ccnv ifnse_0 cv csn cima cin ffnse_9 ccnv ifnse_1 cv ifnse_0 cv ffnse_9 cfv ffnse_6 wbr ifnse_1 ffnse_5 crab ifnse_0 cv ffnse_9 cfv csn cun cima cvv ssexg syl2anc ralrimiva ifnse_0 ffnse_4 ffnse_8 dfse2 sylibr $.
$}

