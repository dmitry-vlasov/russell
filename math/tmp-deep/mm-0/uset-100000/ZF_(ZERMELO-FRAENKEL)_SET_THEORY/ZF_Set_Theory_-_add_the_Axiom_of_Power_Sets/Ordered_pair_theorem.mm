$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Derive_the_Axiom_of_Pairing.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Ordered pair theorem

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( An ordered pair is nonempty iff the arguments are sets.  (Contributed by
       NM, 24-Jan-2004.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	fopnz_0 $f class A $.
	fopnz_1 $f class B $.
	opnz $p |- ( <. A , B >. =/= (/) <-> ( A e. _V /\ B e. _V ) ) $= fopnz_0 fopnz_1 cop c0 wne fopnz_0 cvv wcel fopnz_1 cvv wcel wa fopnz_0 cvv wcel fopnz_1 cvv wcel wa fopnz_0 fopnz_1 cop c0 fopnz_0 fopnz_1 opprc necon1ai fopnz_0 cvv wcel fopnz_1 cvv wcel wa fopnz_0 fopnz_1 cop fopnz_0 csn fopnz_0 fopnz_1 cpr cpr c0 fopnz_0 fopnz_1 cvv cvv dfopg fopnz_0 csn fopnz_0 fopnz_1 cpr cpr c0 wne fopnz_0 cvv wcel fopnz_1 cvv wcel wa fopnz_0 csn fopnz_0 fopnz_1 cpr fopnz_0 snex prnz a1i eqnetrd impbii $.
$}
$( An ordered pair is nonempty if the arguments are sets.  (Contributed by
       Mario Carneiro, 26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	fopnzi_0 $f class A $.
	fopnzi_1 $f class B $.
	eopnzi_0 $e |- A e. _V $.
	eopnzi_1 $e |- B e. _V $.
	opnzi $p |- <. A , B >. =/= (/) $= fopnzi_0 fopnzi_1 cop c0 wne fopnzi_0 cvv wcel fopnzi_1 cvv wcel eopnzi_0 eopnzi_1 fopnzi_0 fopnzi_1 opnz mpbir2an $.
$}
$( Equality of the first members of equal ordered pairs.  (Contributed by
       NM, 28-May-2008.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fopth1_0 $f class A $.
	fopth1_1 $f class B $.
	fopth1_2 $f class C $.
	fopth1_3 $f class D $.
	eopth1_0 $e |- A e. _V $.
	eopth1_1 $e |- B e. _V $.
	opth1 $p |- ( <. A , B >. = <. C , D >. -> A = C ) $= fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_2 csn wceq fopth1_0 fopth1_2 wceq fopth1_0 csn fopth1_2 fopth1_3 cpr wceq fopth1_0 csn fopth1_2 csn wceq fopth1_0 fopth1_2 wceq wi fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 fopth1_2 eopth1_0 sneqr a1i fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_2 fopth1_3 cpr wceq fopth1_2 fopth1_0 csn wcel fopth1_0 fopth1_2 wceq fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_2 fopth1_0 csn wcel fopth1_0 csn fopth1_2 fopth1_3 cpr wceq fopth1_2 fopth1_2 fopth1_3 cpr wcel fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_2 cvv wcel fopth1_2 fopth1_2 fopth1_3 cpr wcel fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_2 cvv wcel fopth1_3 cvv wcel fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_2 fopth1_3 cop wcel fopth1_2 cvv wcel fopth1_3 cvv wcel wa fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop fopth1_0 fopth1_1 eopth1_0 eopth1_1 opi1 fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq id syl5eleq fopth1_2 fopth1_3 fopth1_0 csn oprcl syl simpld fopth1_2 fopth1_3 cvv prid1g syl fopth1_0 csn fopth1_2 fopth1_3 cpr fopth1_2 eleq2 syl5ibrcom fopth1_2 fopth1_0 csn wcel fopth1_2 fopth1_0 fopth1_2 fopth1_0 elsni eqcomd syl6 fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_2 csn fopth1_2 fopth1_3 cpr cpr wcel fopth1_0 csn fopth1_2 csn wceq fopth1_0 csn fopth1_2 fopth1_3 cpr wceq wo fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_2 fopth1_3 cop fopth1_2 csn fopth1_2 fopth1_3 cpr cpr fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop fopth1_0 fopth1_1 eopth1_0 eopth1_1 opi1 fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq id syl5eleq fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_2 fopth1_3 cop wcel fopth1_2 cvv wcel fopth1_3 cvv wcel wa fopth1_2 fopth1_3 cop fopth1_2 csn fopth1_2 fopth1_3 cpr cpr wceq fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq fopth1_0 csn fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop fopth1_0 fopth1_1 eopth1_0 eopth1_1 opi1 fopth1_0 fopth1_1 cop fopth1_2 fopth1_3 cop wceq id syl5eleq fopth1_2 fopth1_3 fopth1_0 csn oprcl fopth1_2 fopth1_3 cvv cvv dfopg 3syl eleqtrd fopth1_0 csn fopth1_2 csn fopth1_2 fopth1_3 cpr elpri syl mpjaod $.
$}
$( The ordered pair theorem.  If two ordered pairs are equal, their first
       elements are equal and their second elements are equal.  Exercise 6 of
       [TakeutiZaring] p. 16.  Note that ` C ` and ` D ` are not required to be
       sets due our specific ordered pair definition.  (Contributed by NM,
       28-May-1995.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x B $.
	$d x C $.
	$d x D $.
	iopth_0 $f set x $.
	fopth_0 $f class A $.
	fopth_1 $f class B $.
	fopth_2 $f class C $.
	fopth_3 $f class D $.
	eopth_0 $e |- A e. _V $.
	eopth_1 $e |- B e. _V $.
	opth $p |- ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) $= fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 fopth_2 wceq fopth_1 fopth_3 wceq wa fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 fopth_2 wceq fopth_1 fopth_3 wceq fopth_0 fopth_1 fopth_2 fopth_3 eopth_0 eopth_1 opth1 fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_3 cvv wcel fopth_2 fopth_1 cpr fopth_2 fopth_3 cpr wceq fopth_1 fopth_3 wceq fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_2 cvv wcel fopth_3 cvv wcel fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 csn fopth_2 fopth_3 cop wcel fopth_2 cvv wcel fopth_3 cvv wcel wa fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 csn fopth_0 fopth_1 cop fopth_2 fopth_3 cop fopth_0 fopth_1 eopth_0 eopth_1 opi1 fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq id syl5eleq fopth_2 fopth_3 fopth_0 csn oprcl syl simprd fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_2 csn fopth_2 fopth_1 cpr cpr fopth_2 csn fopth_2 fopth_3 cpr cpr wceq fopth_2 fopth_1 cpr fopth_2 fopth_3 cpr wceq fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_2 fopth_3 cop fopth_2 csn fopth_2 fopth_1 cpr cpr fopth_2 csn fopth_2 fopth_3 cpr cpr fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_2 fopth_1 cop fopth_2 fopth_3 cop fopth_2 csn fopth_2 fopth_1 cpr cpr fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 fopth_1 cop fopth_2 fopth_1 cop fopth_2 fopth_3 cop fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 fopth_2 fopth_1 fopth_0 fopth_1 fopth_2 fopth_3 eopth_0 eopth_1 opth1 opeq1d fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq id eqtr3d fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_2 cvv wcel fopth_1 cvv wcel fopth_2 fopth_1 cop fopth_2 csn fopth_2 fopth_1 cpr cpr wceq fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_2 cvv wcel fopth_3 cvv wcel fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 csn fopth_2 fopth_3 cop wcel fopth_2 cvv wcel fopth_3 cvv wcel wa fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 csn fopth_0 fopth_1 cop fopth_2 fopth_3 cop fopth_0 fopth_1 eopth_0 eopth_1 opi1 fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq id syl5eleq fopth_2 fopth_3 fopth_0 csn oprcl syl simpld eopth_1 fopth_2 fopth_1 cvv cvv dfopg sylancl eqtr3d fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_2 cvv wcel fopth_3 cvv wcel wa fopth_2 fopth_3 cop fopth_2 csn fopth_2 fopth_3 cpr cpr wceq fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 csn fopth_2 fopth_3 cop wcel fopth_2 cvv wcel fopth_3 cvv wcel wa fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq fopth_0 csn fopth_0 fopth_1 cop fopth_2 fopth_3 cop fopth_0 fopth_1 eopth_0 eopth_1 opi1 fopth_0 fopth_1 cop fopth_2 fopth_3 cop wceq id syl5eleq fopth_2 fopth_3 fopth_0 csn oprcl syl fopth_2 fopth_3 cvv cvv dfopg syl eqtr3d fopth_2 fopth_1 cpr fopth_2 fopth_3 cpr fopth_2 csn fopth_2 fopth_1 prex fopth_2 fopth_3 prex preqr2 syl fopth_2 fopth_1 cpr fopth_2 iopth_0 cv cpr wceq fopth_1 iopth_0 cv wceq wi fopth_2 fopth_1 cpr fopth_2 fopth_3 cpr wceq fopth_1 fopth_3 wceq wi iopth_0 fopth_3 cvv iopth_0 cv fopth_3 wceq fopth_2 fopth_1 cpr fopth_2 iopth_0 cv cpr wceq fopth_2 fopth_1 cpr fopth_2 fopth_3 cpr wceq fopth_1 iopth_0 cv wceq fopth_1 fopth_3 wceq iopth_0 cv fopth_3 wceq fopth_2 iopth_0 cv cpr fopth_2 fopth_3 cpr fopth_2 fopth_1 cpr iopth_0 cv fopth_3 fopth_2 preq2 eqeq2d iopth_0 cv fopth_3 fopth_1 eqeq2 imbi12d fopth_1 iopth_0 cv fopth_2 eopth_1 iopth_0 vex preqr2 vtoclg sylc jca fopth_0 fopth_1 fopth_2 fopth_3 opeq12 impbii $.
$}
$( Ordered pair theorem. ` C ` and ` D ` are not required to be sets under
       our specific ordered pair definition.  (Contributed by NM,
       14-Oct-2005.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$v W $.
	$d x y A $.
	$d y B $.
	$d x y C $.
	$d x y D $.
	iopthg_0 $f set x $.
	iopthg_1 $f set y $.
	fopthg_0 $f class A $.
	fopthg_1 $f class B $.
	fopthg_2 $f class C $.
	fopthg_3 $f class D $.
	fopthg_4 $f class V $.
	fopthg_5 $f class W $.
	opthg $p |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) ) $= iopthg_0 cv iopthg_1 cv cop fopthg_2 fopthg_3 cop wceq iopthg_0 cv fopthg_2 wceq iopthg_1 cv fopthg_3 wceq wa wb fopthg_0 iopthg_1 cv cop fopthg_2 fopthg_3 cop wceq fopthg_0 fopthg_2 wceq iopthg_1 cv fopthg_3 wceq wa wb fopthg_0 fopthg_1 cop fopthg_2 fopthg_3 cop wceq fopthg_0 fopthg_2 wceq fopthg_1 fopthg_3 wceq wa wb iopthg_0 iopthg_1 fopthg_0 fopthg_1 fopthg_4 fopthg_5 iopthg_0 cv fopthg_0 wceq iopthg_0 cv iopthg_1 cv cop fopthg_2 fopthg_3 cop wceq fopthg_0 iopthg_1 cv cop fopthg_2 fopthg_3 cop wceq iopthg_0 cv fopthg_2 wceq iopthg_1 cv fopthg_3 wceq wa fopthg_0 fopthg_2 wceq iopthg_1 cv fopthg_3 wceq wa iopthg_0 cv fopthg_0 wceq iopthg_0 cv iopthg_1 cv cop fopthg_0 iopthg_1 cv cop fopthg_2 fopthg_3 cop iopthg_0 cv fopthg_0 iopthg_1 cv opeq1 eqeq1d iopthg_0 cv fopthg_0 wceq iopthg_0 cv fopthg_2 wceq fopthg_0 fopthg_2 wceq iopthg_1 cv fopthg_3 wceq iopthg_0 cv fopthg_0 fopthg_2 eqeq1 anbi1d bibi12d iopthg_1 cv fopthg_1 wceq fopthg_0 iopthg_1 cv cop fopthg_2 fopthg_3 cop wceq fopthg_0 fopthg_1 cop fopthg_2 fopthg_3 cop wceq fopthg_0 fopthg_2 wceq iopthg_1 cv fopthg_3 wceq wa fopthg_0 fopthg_2 wceq fopthg_1 fopthg_3 wceq wa iopthg_1 cv fopthg_1 wceq fopthg_0 iopthg_1 cv cop fopthg_0 fopthg_1 cop fopthg_2 fopthg_3 cop iopthg_1 cv fopthg_1 fopthg_0 opeq2 eqeq1d iopthg_1 cv fopthg_1 wceq iopthg_1 cv fopthg_3 wceq fopthg_1 fopthg_3 wceq fopthg_0 fopthg_2 wceq iopthg_1 cv fopthg_1 fopthg_3 eqeq1 anbi2d bibi12d iopthg_0 cv iopthg_1 cv fopthg_2 fopthg_3 iopthg_0 vex iopthg_1 vex opth vtocl2g $.
$}
$( Ordered pair theorem.  (Contributed by NM, 14-Oct-2005.)  (Revised by
       Mario Carneiro, 26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$v W $.
	fopthg2_0 $f class A $.
	fopthg2_1 $f class B $.
	fopthg2_2 $f class C $.
	fopthg2_3 $f class D $.
	fopthg2_4 $f class V $.
	fopthg2_5 $f class W $.
	opthg2 $p |- ( ( C e. V /\ D e. W ) -> ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) ) $= fopthg2_2 fopthg2_4 wcel fopthg2_3 fopthg2_5 wcel wa fopthg2_2 fopthg2_3 cop fopthg2_0 fopthg2_1 cop wceq fopthg2_2 fopthg2_0 wceq fopthg2_3 fopthg2_1 wceq wa fopthg2_0 fopthg2_1 cop fopthg2_2 fopthg2_3 cop wceq fopthg2_0 fopthg2_2 wceq fopthg2_1 fopthg2_3 wceq wa fopthg2_2 fopthg2_3 fopthg2_0 fopthg2_1 fopthg2_4 fopthg2_5 opthg fopthg2_0 fopthg2_1 cop fopthg2_2 fopthg2_3 cop eqcom fopthg2_0 fopthg2_2 wceq fopthg2_2 fopthg2_0 wceq fopthg2_1 fopthg2_3 wceq fopthg2_3 fopthg2_1 wceq fopthg2_0 fopthg2_2 eqcom fopthg2_1 fopthg2_3 eqcom anbi12i 3bitr4g $.
$}
$( Ordered pair theorem.  (Contributed by NM, 21-Sep-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fopth2_0 $f class A $.
	fopth2_1 $f class B $.
	fopth2_2 $f class C $.
	fopth2_3 $f class D $.
	eopth2_0 $e |- C e. _V $.
	eopth2_1 $e |- D e. _V $.
	opth2 $p |- ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) $= fopth2_2 cvv wcel fopth2_3 cvv wcel fopth2_0 fopth2_1 cop fopth2_2 fopth2_3 cop wceq fopth2_0 fopth2_2 wceq fopth2_1 fopth2_3 wceq wa wb eopth2_0 eopth2_1 fopth2_0 fopth2_1 fopth2_2 fopth2_3 cvv cvv opthg2 mp2an $.
$}
$( Ordered triple theorem, with triple express with ordered pairs.
       (Contributed by NM, 1-May-1995.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	fotth2_0 $f class A $.
	fotth2_1 $f class B $.
	fotth2_2 $f class C $.
	fotth2_3 $f class D $.
	fotth2_4 $f class R $.
	fotth2_5 $f class S $.
	eotth2_0 $e |- A e. _V $.
	eotth2_1 $e |- B e. _V $.
	eotth2_2 $e |- R e. _V $.
	otth2 $p |- ( <. <. A , B >. , R >. = <. <. C , D >. , S >. <-> ( A = C /\ B = D /\ R = S ) ) $= fotth2_0 fotth2_1 cop fotth2_2 fotth2_3 cop wceq fotth2_4 fotth2_5 wceq wa fotth2_0 fotth2_2 wceq fotth2_1 fotth2_3 wceq wa fotth2_4 fotth2_5 wceq wa fotth2_0 fotth2_1 cop fotth2_4 cop fotth2_2 fotth2_3 cop fotth2_5 cop wceq fotth2_0 fotth2_2 wceq fotth2_1 fotth2_3 wceq fotth2_4 fotth2_5 wceq w3a fotth2_0 fotth2_1 cop fotth2_2 fotth2_3 cop wceq fotth2_0 fotth2_2 wceq fotth2_1 fotth2_3 wceq wa fotth2_4 fotth2_5 wceq fotth2_0 fotth2_1 fotth2_2 fotth2_3 eotth2_0 eotth2_1 opth anbi1i fotth2_0 fotth2_1 cop fotth2_4 fotth2_2 fotth2_3 cop fotth2_5 fotth2_0 fotth2_1 opex eotth2_2 opth fotth2_0 fotth2_2 wceq fotth2_1 fotth2_3 wceq fotth2_4 fotth2_5 wceq df-3an 3bitr4i $.
$}
$( Ordered triple theorem.  (Contributed by NM, 25-Sep-2014.)  (Revised by
       Mario Carneiro, 26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	fotth_0 $f class A $.
	fotth_1 $f class B $.
	fotth_2 $f class C $.
	fotth_3 $f class D $.
	fotth_4 $f class R $.
	fotth_5 $f class S $.
	eotth_0 $e |- A e. _V $.
	eotth_1 $e |- B e. _V $.
	eotth_2 $e |- R e. _V $.
	otth $p |- ( <. A , B , R >. = <. C , D , S >. <-> ( A = C /\ B = D /\ R = S ) ) $= fotth_0 fotth_1 fotth_4 cotp fotth_2 fotth_3 fotth_5 cotp wceq fotth_0 fotth_1 cop fotth_4 cop fotth_2 fotth_3 cop fotth_5 cop wceq fotth_0 fotth_2 wceq fotth_1 fotth_3 wceq fotth_4 fotth_5 wceq w3a fotth_0 fotth_1 fotth_4 cotp fotth_0 fotth_1 cop fotth_4 cop fotth_2 fotth_3 fotth_5 cotp fotth_2 fotth_3 cop fotth_5 cop fotth_0 fotth_1 fotth_4 df-ot fotth_2 fotth_3 fotth_5 df-ot eqeq12i fotth_0 fotth_1 fotth_2 fotth_3 fotth_4 fotth_5 eotth_0 eotth_1 eotth_2 otth2 bitri $.
$}
$( A variable introduction law for ordered pairs.  Analog of Lemma 15 of
       [Monk2] p. 109.  (Contributed by NM, 28-May-1995.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d x y B $.
	$d x y C $.
	feqvinop_0 $f set x $.
	feqvinop_1 $f set y $.
	feqvinop_2 $f class A $.
	feqvinop_3 $f class B $.
	feqvinop_4 $f class C $.
	eeqvinop_0 $e |- B e. _V $.
	eeqvinop_1 $e |- C e. _V $.
	eqvinop $p |- ( A = <. B , C >. <-> E. x E. y ( A = <. x , y >. /\ <. x , y >. = <. B , C >. ) ) $= feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_0 cv feqvinop_1 cv cop feqvinop_3 feqvinop_4 cop wceq wa feqvinop_1 wex feqvinop_0 wex feqvinop_0 cv feqvinop_3 wceq feqvinop_2 feqvinop_0 cv feqvinop_4 cop wceq wa feqvinop_0 wex feqvinop_2 feqvinop_3 feqvinop_4 cop wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_0 cv feqvinop_1 cv cop feqvinop_3 feqvinop_4 cop wceq wa feqvinop_1 wex feqvinop_0 cv feqvinop_3 wceq feqvinop_2 feqvinop_0 cv feqvinop_4 cop wceq wa feqvinop_0 feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_0 cv feqvinop_1 cv cop feqvinop_3 feqvinop_4 cop wceq wa feqvinop_1 wex feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq wa wa feqvinop_1 wex feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq wa feqvinop_1 wex wa feqvinop_0 cv feqvinop_3 wceq feqvinop_2 feqvinop_0 cv feqvinop_4 cop wceq wa feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_0 cv feqvinop_1 cv cop feqvinop_3 feqvinop_4 cop wceq wa feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq wa wa feqvinop_1 feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_0 cv feqvinop_1 cv cop feqvinop_3 feqvinop_4 cop wceq wa feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq wa wa feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq wa feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq wa feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq wa wa feqvinop_0 cv feqvinop_1 cv cop feqvinop_3 feqvinop_4 cop wceq feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq wa feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_0 cv feqvinop_1 cv feqvinop_3 feqvinop_4 eeqvinop_0 eeqvinop_1 opth2 anbi2i feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq wa ancom feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq anass 3bitri exbii feqvinop_0 cv feqvinop_3 wceq feqvinop_1 cv feqvinop_4 wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq wa feqvinop_1 19.42v feqvinop_1 cv feqvinop_4 wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq wa feqvinop_1 wex feqvinop_2 feqvinop_0 cv feqvinop_4 cop wceq feqvinop_0 cv feqvinop_3 wceq feqvinop_2 feqvinop_0 cv feqvinop_1 cv cop wceq feqvinop_2 feqvinop_0 cv feqvinop_4 cop wceq feqvinop_1 feqvinop_4 eeqvinop_1 feqvinop_1 cv feqvinop_4 wceq feqvinop_0 cv feqvinop_1 cv cop feqvinop_0 cv feqvinop_4 cop feqvinop_2 feqvinop_1 cv feqvinop_4 feqvinop_0 cv opeq2 eqeq2d ceqsexv anbi2i 3bitri exbii feqvinop_2 feqvinop_0 cv feqvinop_4 cop wceq feqvinop_2 feqvinop_3 feqvinop_4 cop wceq feqvinop_0 feqvinop_3 eeqvinop_0 feqvinop_0 cv feqvinop_3 wceq feqvinop_0 cv feqvinop_4 cop feqvinop_3 feqvinop_4 cop feqvinop_2 feqvinop_0 cv feqvinop_3 feqvinop_4 opeq1 eqeq2d ceqsexv bitr2i $.
$}
$( Substitution of class ` A ` for ordered pair ` <. x , y >. ` .
       (Contributed by NM, 27-Dec-1996.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v A $.
	$d x z w A $.
	$d y z w A $.
	$d z w ph $.
	icopsexg_0 $f set z $.
	icopsexg_1 $f set w $.
	fcopsexg_0 $f wff ph $.
	fcopsexg_1 $f set x $.
	fcopsexg_2 $f set y $.
	fcopsexg_3 $f class A $.
	copsexg $p |- ( A = <. x , y >. -> ( ph <-> E. x E. y ( A = <. x , y >. /\ ph ) ) ) $= fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex wb fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop wceq icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq wa icopsexg_1 wex icopsexg_0 wex fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex wb wi icopsexg_0 icopsexg_1 fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv fcopsexg_1 vex fcopsexg_2 vex eqvinop fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop wceq icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq wa fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex wb wi icopsexg_0 icopsexg_1 fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop wceq fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex wb wi icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop wceq fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex wb wi icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex wb wi icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex fcopsexg_2 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 19.8a 19.23bi ex icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex fcopsexg_0 wi icopsexg_0 cv icopsexg_1 cv fcopsexg_1 cv fcopsexg_2 cv icopsexg_0 vex icopsexg_1 vex opth icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa fcopsexg_1 fcopsexg_2 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 icopsexg_0 cv icopsexg_1 cv fcopsexg_1 cv fcopsexg_2 cv icopsexg_0 vex icopsexg_1 vex opth anbi1i 2exbii icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 wex fcopsexg_1 icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 nfe1 fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 wex wi fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 wex fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_2 fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 nfa1 icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa wa fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 anass fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wi fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 19.8a a1i anim2d syl5bi eximd icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_2 fcopsexg_1 fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa biidd drex1 sylibd fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal wn icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa wa fcopsexg_2 wex fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal wn icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq wa fcopsexg_0 wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa wa fcopsexg_2 icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 anass exbii icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq fcopsexg_2 wex icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal wn icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 19.40 fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal wn icopsexg_0 cv fcopsexg_1 cv wceq fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal wn fcopsexg_2 fcopsexg_2 cv fcopsexg_1 cv wceq fcopsexg_2 wal wn icopsexg_0 cv fcopsexg_1 cv wceq fcopsexg_2 fcopsexg_2 fcopsexg_1 fcopsexg_2 nfnae fcopsexg_2 fcopsexg_1 icopsexg_0 dveeq2 nfd 19.9d anim1d syl5 syl5bi icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 19.8a syl6 pm2.61i exlimi icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 wex icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex icopsexg_0 cv fcopsexg_1 cv wceq fcopsexg_1 weu icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wa fcopsexg_1 wex icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex wi fcopsexg_1 cv icopsexg_0 cv wceq fcopsexg_1 weu icopsexg_0 cv fcopsexg_1 cv wceq fcopsexg_1 weu fcopsexg_1 icopsexg_0 euequ1 fcopsexg_1 cv icopsexg_0 cv wceq icopsexg_0 cv fcopsexg_1 cv wceq fcopsexg_1 fcopsexg_1 icopsexg_0 equcom eubii mpbi icopsexg_0 cv fcopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 eupick mpan com12 icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_2 weu icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wa fcopsexg_2 wex icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 wi fcopsexg_2 cv icopsexg_1 cv wceq fcopsexg_2 weu icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_2 weu fcopsexg_2 icopsexg_1 euequ1 fcopsexg_2 cv icopsexg_1 cv wceq icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_2 fcopsexg_2 cv icopsexg_1 cv eqcom eubii mpbi icopsexg_1 cv fcopsexg_2 cv wceq fcopsexg_0 fcopsexg_2 eupick mpan com12 sylan9 syl5 syl5bi sylbi impbid fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop wceq fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex wb fcopsexg_0 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex wb fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop eqeq1 fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop wceq fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_2 wex fcopsexg_1 wex fcopsexg_0 fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop wceq fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 wa fcopsexg_1 fcopsexg_2 fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop wceq fcopsexg_3 fcopsexg_1 cv fcopsexg_2 cv cop wceq icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop wceq fcopsexg_0 fcopsexg_3 icopsexg_0 cv icopsexg_1 cv cop fcopsexg_1 cv fcopsexg_2 cv cop eqeq1 anbi1d 2exbidv bibi2d imbi12d mpbiri adantr exlimivv sylbi pm2.43i $.
$}
$( Closed theorem form of ~ copsex2g .  (Contributed by NM,
       17-Feb-2013.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$v W $.
	$d x y ps $.
	$d x y A $.
	$d x y B $.
	fcopsex2t_0 $f wff ph $.
	fcopsex2t_1 $f wff ps $.
	fcopsex2t_2 $f set x $.
	fcopsex2t_3 $f set y $.
	fcopsex2t_4 $f class A $.
	fcopsex2t_5 $f class B $.
	fcopsex2t_6 $f class V $.
	fcopsex2t_7 $f class W $.
	copsex2t $p |- ( ( A. x A. y ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) /\ ( A e. V /\ B e. W ) ) -> ( E. x E. y ( <. A , B >. = <. x , y >. /\ ph ) <-> ps ) ) $= fcopsex2t_4 fcopsex2t_6 wcel fcopsex2t_5 fcopsex2t_7 wcel wa fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_1 wb fcopsex2t_4 fcopsex2t_6 wcel fcopsex2t_5 fcopsex2t_7 wcel wa fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_2 wex fcopsex2t_3 cv fcopsex2t_5 wceq fcopsex2t_3 wex wa fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_4 fcopsex2t_6 wcel fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_2 wex fcopsex2t_5 fcopsex2t_7 wcel fcopsex2t_3 cv fcopsex2t_5 wceq fcopsex2t_3 wex fcopsex2t_2 fcopsex2t_4 fcopsex2t_6 elisset fcopsex2t_3 fcopsex2t_5 fcopsex2t_7 elisset anim12i fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq fcopsex2t_2 fcopsex2t_3 eeanv sylibr fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_1 wb fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_3 wex fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_1 wb fcopsex2t_2 fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 nfa1 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_1 fcopsex2t_2 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 nfe1 fcopsex2t_1 fcopsex2t_2 nfv nfbi fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_1 wb fcopsex2t_3 fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 fcopsex2t_2 nfa2 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_1 fcopsex2t_3 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_3 fcopsex2t_2 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 nfe1 nfex fcopsex2t_1 fcopsex2t_3 nfv nfbi fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_1 wb fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa wa fcopsex2t_0 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex fcopsex2t_1 fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex wb fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_2 cv fcopsex2t_3 cv cop fcopsex2t_4 fcopsex2t_5 cop wceq fcopsex2t_0 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex wb fcopsex2t_2 cv fcopsex2t_3 cv fcopsex2t_4 fcopsex2t_5 opeq12 fcopsex2t_0 fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop wceq fcopsex2t_0 wa fcopsex2t_3 wex fcopsex2t_2 wex wb fcopsex2t_4 fcopsex2t_5 cop fcopsex2t_2 cv fcopsex2t_3 cv cop fcopsex2t_0 fcopsex2t_2 fcopsex2t_3 fcopsex2t_4 fcopsex2t_5 cop copsexg eqcoms syl adantl fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 wal fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 fcopsex2t_2 cv fcopsex2t_4 wceq fcopsex2t_3 cv fcopsex2t_5 wceq wa fcopsex2t_0 fcopsex2t_1 wb wi fcopsex2t_3 wal fcopsex2t_2 sp 19.21bi imp bitr3d ex exlimd exlimd imp sylan2 $.
$}
$( Implicit substitution inference for ordered pairs.  (Contributed by NM,
       28-May-1995.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$v W $.
	$d x y ps $.
	$d x y A $.
	$d x y B $.
	fcopsex2g_0 $f wff ph $.
	fcopsex2g_1 $f wff ps $.
	fcopsex2g_2 $f set x $.
	fcopsex2g_3 $f set y $.
	fcopsex2g_4 $f class A $.
	fcopsex2g_5 $f class B $.
	fcopsex2g_6 $f class V $.
	fcopsex2g_7 $f class W $.
	ecopsex2g_0 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	copsex2g $p |- ( ( A e. V /\ B e. W ) -> ( E. x E. y ( <. A , B >. = <. x , y >. /\ ph ) <-> ps ) ) $= fcopsex2g_4 fcopsex2g_6 wcel fcopsex2g_2 cv fcopsex2g_4 wceq fcopsex2g_2 wex fcopsex2g_3 cv fcopsex2g_5 wceq fcopsex2g_3 wex fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex fcopsex2g_1 wb fcopsex2g_5 fcopsex2g_7 wcel fcopsex2g_2 fcopsex2g_4 fcopsex2g_6 elisset fcopsex2g_3 fcopsex2g_5 fcopsex2g_7 elisset fcopsex2g_2 cv fcopsex2g_4 wceq fcopsex2g_2 wex fcopsex2g_3 cv fcopsex2g_5 wceq fcopsex2g_3 wex wa fcopsex2g_2 cv fcopsex2g_4 wceq fcopsex2g_3 cv fcopsex2g_5 wceq wa fcopsex2g_3 wex fcopsex2g_2 wex fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex fcopsex2g_1 wb fcopsex2g_2 cv fcopsex2g_4 wceq fcopsex2g_3 cv fcopsex2g_5 wceq fcopsex2g_2 fcopsex2g_3 eeanv fcopsex2g_2 cv fcopsex2g_4 wceq fcopsex2g_3 cv fcopsex2g_5 wceq wa fcopsex2g_3 wex fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex fcopsex2g_1 wb fcopsex2g_2 fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex fcopsex2g_1 fcopsex2g_2 fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 nfe1 fcopsex2g_1 fcopsex2g_2 nfv nfbi fcopsex2g_2 cv fcopsex2g_4 wceq fcopsex2g_3 cv fcopsex2g_5 wceq wa fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex fcopsex2g_1 wb fcopsex2g_3 fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex fcopsex2g_1 fcopsex2g_3 fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_3 fcopsex2g_2 fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 nfe1 nfex fcopsex2g_1 fcopsex2g_3 nfv nfbi fcopsex2g_2 cv fcopsex2g_4 wceq fcopsex2g_3 cv fcopsex2g_5 wceq wa fcopsex2g_0 fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex fcopsex2g_1 fcopsex2g_2 cv fcopsex2g_4 wceq fcopsex2g_3 cv fcopsex2g_5 wceq wa fcopsex2g_2 cv fcopsex2g_3 cv cop fcopsex2g_4 fcopsex2g_5 cop wceq fcopsex2g_0 fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex wb fcopsex2g_2 cv fcopsex2g_3 cv fcopsex2g_4 fcopsex2g_5 opeq12 fcopsex2g_0 fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop wceq fcopsex2g_0 wa fcopsex2g_3 wex fcopsex2g_2 wex wb fcopsex2g_4 fcopsex2g_5 cop fcopsex2g_2 cv fcopsex2g_3 cv cop fcopsex2g_0 fcopsex2g_2 fcopsex2g_3 fcopsex2g_4 fcopsex2g_5 cop copsexg eqcoms syl ecopsex2g_0 bitr3d exlimi exlimi sylbir syl2an $.
$}
$( An implicit substitution inference for 2 ordered pairs.  (Contributed by
       NM, 5-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	$d x y z w A $.
	$d x y z w B $.
	$d x y z w C $.
	$d x y z w D $.
	$d x y z w ps $.
	$d x y z w R $.
	$d x y z w S $.
	fcopsex4g_0 $f wff ph $.
	fcopsex4g_1 $f wff ps $.
	fcopsex4g_2 $f set x $.
	fcopsex4g_3 $f set y $.
	fcopsex4g_4 $f set z $.
	fcopsex4g_5 $f set w $.
	fcopsex4g_6 $f class A $.
	fcopsex4g_7 $f class B $.
	fcopsex4g_8 $f class C $.
	fcopsex4g_9 $f class D $.
	fcopsex4g_10 $f class R $.
	fcopsex4g_11 $f class S $.
	ecopsex4g_0 $e |- ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) -> ( ph <-> ps ) ) $.
	copsex4g $p |- ( ( ( A e. R /\ B e. S ) /\ ( C e. R /\ D e. S ) ) -> ( E. x E. y E. z E. w ( ( <. A , B >. = <. x , y >. /\ <. C , D >. = <. z , w >. ) /\ ph ) <-> ps ) ) $= fcopsex4g_6 fcopsex4g_10 wcel fcopsex4g_7 fcopsex4g_11 wcel wa fcopsex4g_8 fcopsex4g_10 wcel fcopsex4g_9 fcopsex4g_11 wcel wa wa fcopsex4g_6 fcopsex4g_7 cop fcopsex4g_2 cv fcopsex4g_3 cv cop wceq fcopsex4g_8 fcopsex4g_9 cop fcopsex4g_4 cv fcopsex4g_5 cv cop wceq wa fcopsex4g_0 wa fcopsex4g_5 wex fcopsex4g_4 wex fcopsex4g_3 wex fcopsex4g_2 wex fcopsex4g_2 cv fcopsex4g_6 wceq fcopsex4g_3 cv fcopsex4g_7 wceq wa fcopsex4g_4 cv fcopsex4g_8 wceq fcopsex4g_5 cv fcopsex4g_9 wceq wa wa fcopsex4g_0 wa fcopsex4g_5 wex fcopsex4g_4 wex fcopsex4g_3 wex fcopsex4g_2 wex fcopsex4g_1 fcopsex4g_6 fcopsex4g_10 wcel fcopsex4g_7 fcopsex4g_11 wcel wa fcopsex4g_8 fcopsex4g_10 wcel fcopsex4g_9 fcopsex4g_11 wcel wa wa fcopsex4g_6 fcopsex4g_7 cop fcopsex4g_2 cv fcopsex4g_3 cv cop wceq fcopsex4g_8 fcopsex4g_9 cop fcopsex4g_4 cv fcopsex4g_5 cv cop wceq wa fcopsex4g_0 wa fcopsex4g_2 cv fcopsex4g_6 wceq fcopsex4g_3 cv fcopsex4g_7 wceq wa fcopsex4g_4 cv fcopsex4g_8 wceq fcopsex4g_5 cv fcopsex4g_9 wceq wa wa fcopsex4g_0 wa fcopsex4g_2 fcopsex4g_3 fcopsex4g_4 fcopsex4g_5 fcopsex4g_6 fcopsex4g_7 cop fcopsex4g_2 cv fcopsex4g_3 cv cop wceq fcopsex4g_8 fcopsex4g_9 cop fcopsex4g_4 cv fcopsex4g_5 cv cop wceq wa fcopsex4g_0 wa fcopsex4g_2 cv fcopsex4g_6 wceq fcopsex4g_3 cv fcopsex4g_7 wceq wa fcopsex4g_4 cv fcopsex4g_8 wceq fcopsex4g_5 cv fcopsex4g_9 wceq wa wa fcopsex4g_0 wa wb fcopsex4g_6 fcopsex4g_10 wcel fcopsex4g_7 fcopsex4g_11 wcel wa fcopsex4g_8 fcopsex4g_10 wcel fcopsex4g_9 fcopsex4g_11 wcel wa wa fcopsex4g_6 fcopsex4g_7 cop fcopsex4g_2 cv fcopsex4g_3 cv cop wceq fcopsex4g_8 fcopsex4g_9 cop fcopsex4g_4 cv fcopsex4g_5 cv cop wceq wa fcopsex4g_2 cv fcopsex4g_6 wceq fcopsex4g_3 cv fcopsex4g_7 wceq wa fcopsex4g_4 cv fcopsex4g_8 wceq fcopsex4g_5 cv fcopsex4g_9 wceq wa wa fcopsex4g_0 fcopsex4g_6 fcopsex4g_7 cop fcopsex4g_2 cv fcopsex4g_3 cv cop wceq fcopsex4g_2 cv fcopsex4g_6 wceq fcopsex4g_3 cv fcopsex4g_7 wceq wa fcopsex4g_8 fcopsex4g_9 cop fcopsex4g_4 cv fcopsex4g_5 cv cop wceq fcopsex4g_4 cv fcopsex4g_8 wceq fcopsex4g_5 cv fcopsex4g_9 wceq wa fcopsex4g_6 fcopsex4g_7 cop fcopsex4g_2 cv fcopsex4g_3 cv cop wceq fcopsex4g_2 cv fcopsex4g_3 cv cop fcopsex4g_6 fcopsex4g_7 cop wceq fcopsex4g_2 cv fcopsex4g_6 wceq fcopsex4g_3 cv fcopsex4g_7 wceq wa fcopsex4g_6 fcopsex4g_7 cop fcopsex4g_2 cv fcopsex4g_3 cv cop eqcom fcopsex4g_2 cv fcopsex4g_3 cv fcopsex4g_6 fcopsex4g_7 fcopsex4g_2 vex fcopsex4g_3 vex opth bitri fcopsex4g_8 fcopsex4g_9 cop fcopsex4g_4 cv fcopsex4g_5 cv cop wceq fcopsex4g_4 cv fcopsex4g_5 cv cop fcopsex4g_8 fcopsex4g_9 cop wceq fcopsex4g_4 cv fcopsex4g_8 wceq fcopsex4g_5 cv fcopsex4g_9 wceq wa fcopsex4g_8 fcopsex4g_9 cop fcopsex4g_4 cv fcopsex4g_5 cv cop eqcom fcopsex4g_4 cv fcopsex4g_5 cv fcopsex4g_8 fcopsex4g_9 fcopsex4g_4 vex fcopsex4g_5 vex opth bitri anbi12i anbi1i a1i 4exbidv fcopsex4g_0 fcopsex4g_1 fcopsex4g_2 cv fcopsex4g_6 wceq fcopsex4g_3 cv fcopsex4g_7 wceq wa fcopsex4g_4 cv fcopsex4g_8 wceq fcopsex4g_5 cv fcopsex4g_9 wceq wa wa fcopsex4g_2 fcopsex4g_3 fcopsex4g_4 fcopsex4g_5 fcopsex4g_6 fcopsex4g_7 fcopsex4g_8 fcopsex4g_9 fcopsex4g_10 fcopsex4g_11 fcopsex4g_2 cv fcopsex4g_6 wceq fcopsex4g_3 cv fcopsex4g_7 wceq wa fcopsex4g_4 cv fcopsex4g_8 wceq fcopsex4g_5 cv fcopsex4g_9 wceq wa wa id ecopsex4g_0 cgsex4g bitrd $.
$}
$( A property of ordered pairs.  (Contributed by Mario Carneiro,
     26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	f0nelop_0 $f class A $.
	f0nelop_1 $f class B $.
	0nelop $p |- -. (/) e. <. A , B >. $= c0 f0nelop_0 f0nelop_1 cop wcel c0 f0nelop_0 csn wceq c0 f0nelop_0 f0nelop_1 cpr wceq wo c0 f0nelop_0 f0nelop_1 cop wcel c0 f0nelop_0 csn f0nelop_0 f0nelop_1 cpr cpr wcel c0 f0nelop_0 csn wceq c0 f0nelop_0 f0nelop_1 cpr wceq wo c0 f0nelop_0 f0nelop_1 cop wcel c0 f0nelop_0 f0nelop_1 cop f0nelop_0 csn f0nelop_0 f0nelop_1 cpr cpr c0 f0nelop_0 f0nelop_1 cop wcel id c0 f0nelop_0 f0nelop_1 cop wcel f0nelop_0 cvv wcel f0nelop_1 cvv wcel wa f0nelop_0 f0nelop_1 cop f0nelop_0 csn f0nelop_0 f0nelop_1 cpr cpr wceq f0nelop_0 f0nelop_1 c0 oprcl f0nelop_0 f0nelop_1 cvv cvv dfopg syl eleqtrd c0 f0nelop_0 csn f0nelop_0 f0nelop_1 cpr elpri syl c0 f0nelop_0 f0nelop_1 cop wcel c0 f0nelop_0 csn wne c0 f0nelop_0 f0nelop_1 cpr wne wa c0 f0nelop_0 csn wceq c0 f0nelop_0 f0nelop_1 cpr wceq wo wn c0 f0nelop_0 f0nelop_1 cop wcel c0 f0nelop_0 csn wne c0 f0nelop_0 f0nelop_1 cpr wne c0 f0nelop_0 f0nelop_1 cop wcel f0nelop_0 csn c0 c0 f0nelop_0 f0nelop_1 cop wcel f0nelop_0 cvv wcel f0nelop_0 csn c0 wne c0 f0nelop_0 f0nelop_1 cop wcel f0nelop_0 cvv wcel f0nelop_1 cvv wcel f0nelop_0 f0nelop_1 c0 oprcl simpld f0nelop_0 cvv snnzg syl necomd c0 f0nelop_0 f0nelop_1 cop wcel f0nelop_0 f0nelop_1 cpr c0 c0 f0nelop_0 f0nelop_1 cop wcel f0nelop_0 cvv wcel f0nelop_0 f0nelop_1 cpr c0 wne c0 f0nelop_0 f0nelop_1 cop wcel f0nelop_0 cvv wcel f0nelop_1 cvv wcel f0nelop_0 f0nelop_1 c0 oprcl simpld f0nelop_0 f0nelop_1 cvv prnzg syl necomd jca c0 f0nelop_0 csn c0 f0nelop_0 f0nelop_1 cpr neanior sylib pm2.65i $.
$}
$( Equivalence of existence implied by equality of ordered pairs.
     (Contributed by NM, 28-May-2008.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fopeqex_0 $f class A $.
	fopeqex_1 $f class B $.
	fopeqex_2 $f class C $.
	fopeqex_3 $f class D $.
	opeqex $p |- ( <. A , B >. = <. C , D >. -> ( ( A e. _V /\ B e. _V ) <-> ( C e. _V /\ D e. _V ) ) ) $= fopeqex_0 fopeqex_1 cop fopeqex_2 fopeqex_3 cop wceq fopeqex_0 fopeqex_1 cop c0 wne fopeqex_2 fopeqex_3 cop c0 wne fopeqex_0 cvv wcel fopeqex_1 cvv wcel wa fopeqex_2 cvv wcel fopeqex_3 cvv wcel wa fopeqex_0 fopeqex_1 cop fopeqex_2 fopeqex_3 cop c0 neeq1 fopeqex_0 fopeqex_1 opnz fopeqex_2 fopeqex_3 opnz 3bitr3g $.
$}
$( Equivalence of existence implied by equality of ordered triples.
     (Contributed by NM, 26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v S $.
	$v T $.
	foteqex2_0 $f class A $.
	foteqex2_1 $f class B $.
	foteqex2_2 $f class C $.
	foteqex2_3 $f class R $.
	foteqex2_4 $f class S $.
	foteqex2_5 $f class T $.
	oteqex2 $p |- ( <. <. A , B >. , C >. = <. <. R , S >. , T >. -> ( C e. _V <-> T e. _V ) ) $= foteqex2_0 foteqex2_1 cop foteqex2_2 cop foteqex2_3 foteqex2_4 cop foteqex2_5 cop wceq foteqex2_0 foteqex2_1 cop cvv wcel foteqex2_2 cvv wcel wa foteqex2_3 foteqex2_4 cop cvv wcel foteqex2_5 cvv wcel wa foteqex2_2 cvv wcel foteqex2_5 cvv wcel foteqex2_0 foteqex2_1 cop foteqex2_2 foteqex2_3 foteqex2_4 cop foteqex2_5 opeqex foteqex2_0 foteqex2_1 cop cvv wcel foteqex2_2 cvv wcel foteqex2_0 foteqex2_1 opex biantrur foteqex2_3 foteqex2_4 cop cvv wcel foteqex2_5 cvv wcel foteqex2_3 foteqex2_4 opex biantrur 3bitr4g $.
$}
$( Equivalence of existence implied by equality of ordered triples.
     (Contributed by NM, 28-May-2008.)  (Revised by Mario Carneiro,
     26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v S $.
	$v T $.
	foteqex_0 $f class A $.
	foteqex_1 $f class B $.
	foteqex_2 $f class C $.
	foteqex_3 $f class R $.
	foteqex_4 $f class S $.
	foteqex_5 $f class T $.
	oteqex $p |- ( <. <. A , B >. , C >. = <. <. R , S >. , T >. -> ( ( A e. _V /\ B e. _V /\ C e. _V ) <-> ( R e. _V /\ S e. _V /\ T e. _V ) ) ) $= foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq foteqex_2 cvv wcel foteqex_0 cvv wcel foteqex_1 cvv wcel foteqex_2 cvv wcel w3a foteqex_3 cvv wcel foteqex_4 cvv wcel foteqex_5 cvv wcel w3a foteqex_0 cvv wcel foteqex_1 cvv wcel foteqex_2 cvv wcel w3a foteqex_2 cvv wcel wi foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq foteqex_0 cvv wcel foteqex_1 cvv wcel foteqex_2 cvv wcel simp3 a1i foteqex_3 cvv wcel foteqex_4 cvv wcel foteqex_5 cvv wcel w3a foteqex_2 cvv wcel foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq foteqex_5 cvv wcel foteqex_3 cvv wcel foteqex_4 cvv wcel foteqex_5 cvv wcel simp3 foteqex_0 foteqex_1 foteqex_2 foteqex_3 foteqex_4 foteqex_5 oteqex2 syl5ibr foteqex_2 cvv wcel foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq foteqex_0 cvv wcel foteqex_1 cvv wcel foteqex_2 cvv wcel w3a foteqex_3 cvv wcel foteqex_4 cvv wcel foteqex_5 cvv wcel w3a wb foteqex_2 cvv wcel foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq wa foteqex_0 cvv wcel foteqex_1 cvv wcel wa foteqex_2 cvv wcel wa foteqex_3 cvv wcel foteqex_4 cvv wcel wa foteqex_5 cvv wcel wa foteqex_0 cvv wcel foteqex_1 cvv wcel foteqex_2 cvv wcel w3a foteqex_3 cvv wcel foteqex_4 cvv wcel foteqex_5 cvv wcel w3a foteqex_2 cvv wcel foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq wa foteqex_0 cvv wcel foteqex_1 cvv wcel wa foteqex_3 cvv wcel foteqex_4 cvv wcel wa foteqex_2 cvv wcel foteqex_5 cvv wcel foteqex_2 cvv wcel foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq wa foteqex_0 foteqex_1 cop foteqex_3 foteqex_4 cop wceq foteqex_0 cvv wcel foteqex_1 cvv wcel wa foteqex_3 cvv wcel foteqex_4 cvv wcel wa wb foteqex_2 cvv wcel foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq foteqex_0 foteqex_1 cop foteqex_3 foteqex_4 cop wceq foteqex_2 foteqex_5 wceq foteqex_0 foteqex_1 cop cvv wcel foteqex_2 cvv wcel foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq foteqex_0 foteqex_1 cop foteqex_3 foteqex_4 cop wceq foteqex_2 foteqex_5 wceq wa wb foteqex_0 foteqex_1 opex foteqex_0 foteqex_1 cop foteqex_2 foteqex_3 foteqex_4 cop foteqex_5 cvv cvv opthg mpan simprbda foteqex_0 foteqex_1 foteqex_3 foteqex_4 opeqex syl foteqex_0 foteqex_1 cop foteqex_2 cop foteqex_3 foteqex_4 cop foteqex_5 cop wceq foteqex_2 cvv wcel foteqex_5 cvv wcel wb foteqex_2 cvv wcel foteqex_0 foteqex_1 foteqex_2 foteqex_3 foteqex_4 foteqex_5 oteqex2 adantl anbi12d foteqex_0 cvv wcel foteqex_1 cvv wcel foteqex_2 cvv wcel df-3an foteqex_3 cvv wcel foteqex_4 cvv wcel foteqex_5 cvv wcel df-3an 3bitr4g expcom pm5.21ndd $.
$}
$( An ordered pair commutes iff its members are equal.  (Contributed by NM,
       28-May-2009.) $)
${
	$v A $.
	$v B $.
	fopcom_0 $f class A $.
	fopcom_1 $f class B $.
	eopcom_0 $e |- A e. _V $.
	eopcom_1 $e |- B e. _V $.
	opcom $p |- ( <. A , B >. = <. B , A >. <-> A = B ) $= fopcom_0 fopcom_1 cop fopcom_1 fopcom_0 cop wceq fopcom_0 fopcom_1 wceq fopcom_1 fopcom_0 wceq wa fopcom_0 fopcom_1 wceq fopcom_0 fopcom_1 wceq wa fopcom_0 fopcom_1 wceq fopcom_0 fopcom_1 fopcom_1 fopcom_0 eopcom_0 eopcom_1 opth fopcom_1 fopcom_0 wceq fopcom_0 fopcom_1 wceq fopcom_0 fopcom_1 wceq fopcom_1 fopcom_0 eqcom anbi2i fopcom_0 fopcom_1 wceq anidm 3bitri $.
$}
$( "At most one" property of an ordered pair.  (Contributed by NM,
       11-Apr-2004.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d y B $.
	imoop2_0 $f set y $.
	fmoop2_0 $f set x $.
	fmoop2_1 $f class A $.
	fmoop2_2 $f class B $.
	emoop2_0 $e |- B e. _V $.
	moop2 $p |- E* x A = <. B , x >. $= fmoop2_1 fmoop2_2 fmoop2_0 cv cop wceq fmoop2_0 wmo fmoop2_1 fmoop2_2 fmoop2_0 cv cop wceq fmoop2_1 fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop wceq wa fmoop2_0 cv imoop2_0 cv wceq wi imoop2_0 wal fmoop2_0 wal fmoop2_1 fmoop2_2 fmoop2_0 cv cop wceq fmoop2_1 fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop wceq wa fmoop2_0 cv imoop2_0 cv wceq wi fmoop2_0 imoop2_0 fmoop2_1 fmoop2_2 fmoop2_0 cv cop wceq fmoop2_1 fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop wceq wa fmoop2_2 fmoop2_0 cv cop fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop wceq fmoop2_0 cv imoop2_0 cv wceq fmoop2_1 fmoop2_2 fmoop2_0 cv cop fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop eqtr2 fmoop2_2 fmoop2_0 cv cop fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop wceq fmoop2_2 fmoop2_0 imoop2_0 cv fmoop2_2 csb wceq fmoop2_0 cv imoop2_0 cv wceq fmoop2_2 fmoop2_0 cv fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv emoop2_0 fmoop2_0 vex opth simprbi syl gen2 fmoop2_1 fmoop2_2 fmoop2_0 cv cop wceq fmoop2_1 fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop wceq fmoop2_0 imoop2_0 fmoop2_0 fmoop2_1 fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop fmoop2_0 fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv fmoop2_0 imoop2_0 cv fmoop2_2 nfcsb1v fmoop2_0 imoop2_0 cv nfcv nfop nfeq2 fmoop2_0 cv imoop2_0 cv wceq fmoop2_2 fmoop2_0 cv cop fmoop2_0 imoop2_0 cv fmoop2_2 csb imoop2_0 cv cop fmoop2_1 fmoop2_0 cv imoop2_0 cv wceq fmoop2_2 fmoop2_0 imoop2_0 cv fmoop2_2 csb fmoop2_0 cv imoop2_0 cv fmoop2_0 imoop2_0 cv fmoop2_2 csbeq1a fmoop2_0 cv imoop2_0 cv wceq id opeq12d eqeq2d mo4f mpbir $.
$}
$( Equivalence for an ordered pair equal to a singleton.  (Contributed by
       NM, 3-Jun-2008.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fopeqsn_0 $f class A $.
	fopeqsn_1 $f class B $.
	fopeqsn_2 $f class C $.
	eopeqsn_0 $e |- A e. _V $.
	eopeqsn_1 $e |- B e. _V $.
	eopeqsn_2 $e |- C e. _V $.
	opeqsn $p |- ( <. A , B >. = { C } <-> ( A = B /\ C = { A } ) ) $= fopeqsn_0 fopeqsn_1 cop fopeqsn_2 csn wceq fopeqsn_0 csn fopeqsn_0 fopeqsn_1 cpr cpr fopeqsn_2 csn wceq fopeqsn_0 csn fopeqsn_0 fopeqsn_1 cpr wceq fopeqsn_0 fopeqsn_1 cpr fopeqsn_2 wceq wa fopeqsn_0 fopeqsn_1 wceq fopeqsn_2 fopeqsn_0 csn wceq wa fopeqsn_0 fopeqsn_1 cop fopeqsn_0 csn fopeqsn_0 fopeqsn_1 cpr cpr fopeqsn_2 csn fopeqsn_0 fopeqsn_1 eopeqsn_0 eopeqsn_1 dfop eqeq1i fopeqsn_0 csn fopeqsn_0 fopeqsn_1 cpr fopeqsn_2 fopeqsn_0 snex fopeqsn_0 fopeqsn_1 prex eopeqsn_2 preqsn fopeqsn_0 csn fopeqsn_0 fopeqsn_1 cpr wceq fopeqsn_0 fopeqsn_1 cpr fopeqsn_2 wceq wa fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 fopeqsn_1 cpr fopeqsn_2 wceq wa fopeqsn_0 fopeqsn_1 wceq fopeqsn_2 fopeqsn_0 csn wceq wa fopeqsn_0 csn fopeqsn_0 fopeqsn_1 cpr wceq fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 fopeqsn_1 cpr fopeqsn_2 wceq fopeqsn_0 csn fopeqsn_0 fopeqsn_1 cpr wceq fopeqsn_0 fopeqsn_1 cpr fopeqsn_0 csn wceq fopeqsn_0 fopeqsn_1 wceq fopeqsn_1 fopeqsn_0 wceq wa fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 csn fopeqsn_0 fopeqsn_1 cpr eqcom fopeqsn_0 fopeqsn_1 fopeqsn_0 eopeqsn_0 eopeqsn_1 eopeqsn_0 preqsn fopeqsn_0 fopeqsn_1 wceq fopeqsn_1 fopeqsn_0 wceq wa fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 fopeqsn_1 wceq wa fopeqsn_0 fopeqsn_1 wceq fopeqsn_1 fopeqsn_0 wceq fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 fopeqsn_1 wceq fopeqsn_1 fopeqsn_0 eqcom anbi2i fopeqsn_0 fopeqsn_1 wceq anidm bitri 3bitri anbi1i fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 fopeqsn_1 cpr fopeqsn_2 wceq fopeqsn_2 fopeqsn_0 csn wceq fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 fopeqsn_1 cpr fopeqsn_2 wceq fopeqsn_0 csn fopeqsn_2 wceq fopeqsn_2 fopeqsn_0 csn wceq fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 fopeqsn_1 cpr fopeqsn_0 csn fopeqsn_2 fopeqsn_0 fopeqsn_1 wceq fopeqsn_0 csn fopeqsn_0 fopeqsn_0 cpr fopeqsn_0 fopeqsn_1 cpr fopeqsn_0 dfsn2 fopeqsn_0 fopeqsn_1 fopeqsn_0 preq2 syl5req eqeq1d fopeqsn_0 csn fopeqsn_2 eqcom syl6bb pm5.32i bitri 3bitri $.
$}
$( Equivalence for an ordered pair equal to an unordered pair.
       (Contributed by NM, 3-Jun-2008.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fopeqpr_0 $f class A $.
	fopeqpr_1 $f class B $.
	fopeqpr_2 $f class C $.
	fopeqpr_3 $f class D $.
	eopeqpr_0 $e |- A e. _V $.
	eopeqpr_1 $e |- B e. _V $.
	eopeqpr_2 $e |- C e. _V $.
	eopeqpr_3 $e |- D e. _V $.
	opeqpr $p |- ( <. A , B >. = { C , D } <-> ( ( C = { A } /\ D = { A , B } ) \/ ( C = { A , B } /\ D = { A } ) ) ) $= fopeqpr_0 fopeqpr_1 cop fopeqpr_2 fopeqpr_3 cpr wceq fopeqpr_2 fopeqpr_3 cpr fopeqpr_0 fopeqpr_1 cop wceq fopeqpr_2 fopeqpr_3 cpr fopeqpr_0 csn fopeqpr_0 fopeqpr_1 cpr cpr wceq fopeqpr_2 fopeqpr_0 csn wceq fopeqpr_3 fopeqpr_0 fopeqpr_1 cpr wceq wa fopeqpr_2 fopeqpr_0 fopeqpr_1 cpr wceq fopeqpr_3 fopeqpr_0 csn wceq wa wo fopeqpr_0 fopeqpr_1 cop fopeqpr_2 fopeqpr_3 cpr eqcom fopeqpr_0 fopeqpr_1 cop fopeqpr_0 csn fopeqpr_0 fopeqpr_1 cpr cpr fopeqpr_2 fopeqpr_3 cpr fopeqpr_0 fopeqpr_1 eopeqpr_0 eopeqpr_1 dfop eqeq2i fopeqpr_2 fopeqpr_3 fopeqpr_0 csn fopeqpr_0 fopeqpr_1 cpr eopeqpr_2 eopeqpr_3 fopeqpr_0 snex fopeqpr_0 fopeqpr_1 prex preq12b 3bitri $.
$}
$( "At most one" remains true inside ordered pair quantification.
       (Contributed by NM, 28-Aug-2007.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$d x y z A $.
	fmosubopt_0 $f wff ph $.
	fmosubopt_1 $f set x $.
	fmosubopt_2 $f set y $.
	fmosubopt_3 $f set z $.
	fmosubopt_4 $f class A $.
	mosubopt $p |- ( A. y A. z E* x ph -> E* x E. y E. z ( A = <. y , z >. /\ ph ) ) $= fmosubopt_0 fmosubopt_1 wmo fmosubopt_3 wal fmosubopt_2 wal fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_3 wex fmosubopt_2 wex fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wmo fmosubopt_0 fmosubopt_1 wmo fmosubopt_3 wal fmosubopt_2 wal fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_3 wex fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wmo fmosubopt_2 fmosubopt_0 fmosubopt_1 wmo fmosubopt_3 wal fmosubopt_2 nfa1 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_2 fmosubopt_1 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 nfe1 nfmo fmosubopt_0 fmosubopt_1 wmo fmosubopt_3 wal fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_3 wex fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wmo wi fmosubopt_2 fmosubopt_0 fmosubopt_1 wmo fmosubopt_3 wal fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wmo fmosubopt_3 fmosubopt_0 fmosubopt_1 wmo fmosubopt_3 nfa1 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_3 fmosubopt_1 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_3 fmosubopt_2 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 nfe1 nfex nfmo fmosubopt_0 fmosubopt_1 wmo fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wmo wi fmosubopt_3 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 fmosubopt_1 wmo fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wmo fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 fmosubopt_0 fmosubopt_2 fmosubopt_3 fmosubopt_4 copsexg mobidv biimpcd sps exlimd sps exlimd fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_3 wex fmosubopt_2 wex wn fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wex wn fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wmo fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wex fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_3 wex fmosubopt_2 wex fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_2 fmosubopt_3 fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 simpl 2eximi exlimiv con3i fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wex fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 wmo fmosubopt_4 fmosubopt_2 cv fmosubopt_3 cv cop wceq fmosubopt_0 wa fmosubopt_3 wex fmosubopt_2 wex fmosubopt_1 exmo ori syl pm2.61d1 $.
$}
$( "At most one" remains true inside ordered pair quantification.
       (Contributed by NM, 28-May-1995.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$d x y z A $.
	fmosubop_0 $f wff ph $.
	fmosubop_1 $f set x $.
	fmosubop_2 $f set y $.
	fmosubop_3 $f set z $.
	fmosubop_4 $f class A $.
	emosubop_0 $e |- E* x ph $.
	mosubop $p |- E* x E. y E. z ( A = <. y , z >. /\ ph ) $= fmosubop_0 fmosubop_1 wmo fmosubop_3 wal fmosubop_2 wal fmosubop_4 fmosubop_2 cv fmosubop_3 cv cop wceq fmosubop_0 wa fmosubop_3 wex fmosubop_2 wex fmosubop_1 wmo fmosubop_0 fmosubop_1 wmo fmosubop_2 fmosubop_3 emosubop_0 gen2 fmosubop_0 fmosubop_1 fmosubop_2 fmosubop_3 fmosubop_4 mosubopt ax-mp $.
$}
$( Transfer existential uniqueness to second member of an ordered pair.
       (Contributed by NM, 10-Apr-2004.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$d x ph $.
	$d x A $.
	$d x y $.
	feuop2_0 $f wff ph $.
	feuop2_1 $f set x $.
	feuop2_2 $f set y $.
	feuop2_3 $f class A $.
	eeuop2_0 $e |- A e. _V $.
	euop2 $p |- ( E! x E. y ( x = <. A , y >. /\ ph ) <-> E! y ph ) $= feuop2_0 feuop2_1 feuop2_2 feuop2_3 feuop2_2 cv cop feuop2_3 feuop2_2 cv opex feuop2_2 feuop2_1 cv feuop2_3 eeuop2_0 moop2 euxfr2 $.
$}
$( Prove existential uniqueness for an ordered triple.  (Contributed by
       Mario Carneiro, 20-May-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v a $.
	$v b $.
	$v c $.
	$d a b c x y A $.
	$d a b c x y B $.
	$d a b c x y C $.
	$d a b c x ph $.
	$d y ps $.
	ieuotd_0 $f set y $.
	feuotd_0 $f wff ph $.
	feuotd_1 $f wff ps $.
	feuotd_2 $f set x $.
	feuotd_3 $f class A $.
	feuotd_4 $f class B $.
	feuotd_5 $f class C $.
	feuotd_6 $f set a $.
	feuotd_7 $f set b $.
	feuotd_8 $f set c $.
	eeuotd_0 $e |- ( ph -> A e. _V ) $.
	eeuotd_1 $e |- ( ph -> B e. _V ) $.
	eeuotd_2 $e |- ( ph -> C e. _V ) $.
	eeuotd_3 $e |- ( ph -> ( ps <-> ( a = A /\ b = B /\ c = C ) ) ) $.
	euotd $p |- ( ph -> E! x E. a E. b E. c ( x = <. a , b , c >. /\ ps ) ) $= feuotd_0 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv ieuotd_0 cv wceq wb feuotd_2 wal ieuotd_0 wex feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 weu feuotd_0 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq wb feuotd_2 wal feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv ieuotd_0 cv wceq wb feuotd_2 wal ieuotd_0 wex feuotd_0 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq wb feuotd_2 feuotd_0 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_0 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_6 feuotd_7 feuotd_0 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_8 feuotd_0 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_0 feuotd_1 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_0 feuotd_1 wa feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_0 feuotd_1 wa feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp feuotd_3 feuotd_4 feuotd_5 cotp feuotd_2 cv feuotd_0 feuotd_1 wa feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_0 feuotd_1 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a eeuotd_3 biimpa feuotd_6 cv feuotd_7 cv feuotd_3 feuotd_4 feuotd_8 cv feuotd_5 feuotd_6 vex feuotd_7 vex feuotd_8 vex otth sylibr eqeq2d biimpd impancom expimpd exlimdv exlimdvv feuotd_0 feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_0 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_6 wex feuotd_7 wex feuotd_8 wex feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_0 feuotd_5 cvv wcel feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_6 wex feuotd_7 wex feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_6 wex feuotd_7 wex feuotd_8 wex eeuotd_2 feuotd_0 feuotd_4 cvv wcel feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 wex feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_6 wex feuotd_7 wex eeuotd_1 feuotd_0 feuotd_3 cvv wcel feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 feuotd_3 wsbc feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 wex eeuotd_0 feuotd_0 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 feuotd_3 wsbc wtru tru feuotd_0 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc wtru feuotd_6 feuotd_3 cvv eeuotd_0 feuotd_0 feuotd_6 cv feuotd_3 wceq wa feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc wtru feuotd_7 feuotd_4 cvv feuotd_0 feuotd_4 cvv wcel feuotd_6 cv feuotd_3 wceq eeuotd_1 adantr feuotd_0 feuotd_6 cv feuotd_3 wceq wa feuotd_7 cv feuotd_4 wceq wa feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa wtru feuotd_8 feuotd_5 cvv feuotd_0 feuotd_5 cvv wcel feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq eeuotd_2 ad2antrr feuotd_0 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa wtru wb feuotd_0 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa wtru wb feuotd_0 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a wa feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa wtru feuotd_0 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a wa feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 feuotd_0 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a wa feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp feuotd_3 feuotd_4 feuotd_5 cotp feuotd_0 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a wa feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_0 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a simpr feuotd_6 cv feuotd_7 cv feuotd_3 feuotd_4 feuotd_8 cv feuotd_5 feuotd_6 vex feuotd_7 vex feuotd_8 vex otth sylibr eqcomd feuotd_0 feuotd_1 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a eeuotd_3 biimpar jca feuotd_0 feuotd_6 cv feuotd_3 wceq feuotd_7 cv feuotd_4 wceq feuotd_8 cv feuotd_5 wceq w3a wa a1tru 2thd 3exp2 imp41 sbcied sbcied sbcied mpbiri feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 feuotd_3 wsbc feuotd_6 feuotd_3 cvv feuotd_6 feuotd_3 nfcv feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 feuotd_3 nfsbc1v feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 feuotd_3 sbceq1a spcegf sylc feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_6 wex feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 wex feuotd_7 feuotd_4 cvv feuotd_7 feuotd_4 nfcv feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_7 feuotd_6 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 nfsbc1v nfex feuotd_7 cv feuotd_4 wceq feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 wsbc feuotd_6 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_4 sbceq1a exbidv spcegf sylc feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_6 wex feuotd_7 wex feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_6 wex feuotd_7 wex feuotd_8 feuotd_5 cvv feuotd_8 feuotd_5 nfcv feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_6 wex feuotd_8 feuotd_7 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_8 feuotd_6 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 nfsbc1v nfex nfex feuotd_8 cv feuotd_5 wceq feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 wsbc feuotd_7 feuotd_6 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_5 sbceq1a 2exbidv spcegf sylc feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 feuotd_7 feuotd_6 excom13 sylib feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_6 feuotd_7 feuotd_8 feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp eqeq1 anbi1d 3exbidv syl5ibrcom impbid alrimiv feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv ieuotd_0 cv wceq wb feuotd_2 wal feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq wb feuotd_2 wal ieuotd_0 feuotd_3 feuotd_4 feuotd_5 cotp feuotd_3 feuotd_4 feuotd_5 otex ieuotd_0 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv ieuotd_0 cv wceq wb feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq wb feuotd_2 ieuotd_0 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_2 cv ieuotd_0 cv wceq feuotd_2 cv feuotd_3 feuotd_4 feuotd_5 cotp wceq feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex ieuotd_0 cv feuotd_3 feuotd_4 feuotd_5 cotp feuotd_2 cv eqeq2 bibi2d albidv spcev syl feuotd_2 cv feuotd_6 cv feuotd_7 cv feuotd_8 cv cotp wceq feuotd_1 wa feuotd_8 wex feuotd_7 wex feuotd_6 wex feuotd_2 ieuotd_0 df-eu sylibr $.
$}
$( Justification theorem for the ordered pair definition in Norbert Wiener,
       "A simplification of the logic of relations," _Proc. of the Cambridge
       Philos.  Soc_., 1914, vol. 17, pp.387-390.  It is also shown as a
       definition in [Enderton] p. 36 and as Exercise 4.8(b) of [Mendelson]
       p. 230.  It is meaningful only for classes that exist as sets (i.e. are
       not proper classes).  See ~ df-op for other ordered pair definitions.
       (Contributed by NM, 28-Sep-2003.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fopthwiener_0 $f class A $.
	fopthwiener_1 $f class B $.
	fopthwiener_2 $f class C $.
	fopthwiener_3 $f class D $.
	eopthwiener_0 $e |- A e. _V $.
	eopthwiener_1 $e |- B e. _V $.
	opthwiener $p |- ( { { { A } , (/) } , { { B } } } = { { { C } , (/) } , { { D } } } <-> ( A = C /\ B = D ) ) $= fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_0 fopthwiener_2 wceq fopthwiener_1 fopthwiener_3 wceq wa fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_0 fopthwiener_2 wceq fopthwiener_1 fopthwiener_3 wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_0 csn fopthwiener_2 csn wceq fopthwiener_0 fopthwiener_2 wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_0 csn c0 cpr fopthwiener_2 csn c0 cpr wceq fopthwiener_0 csn fopthwiener_2 csn wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn cpr wceq fopthwiener_0 csn c0 cpr fopthwiener_2 csn c0 cpr wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq id fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn fopthwiener_2 csn c0 cpr fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq wo fopthwiener_1 csn csn fopthwiener_3 csn csn wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wcel fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq wo fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn csn fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr wcel fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wcel fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn fopthwiener_1 csn snex prid2 fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr fopthwiener_1 csn csn eleq2 mpbii fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn fopthwiener_1 csn snex elpr sylib fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq wn fopthwiener_1 csn csn fopthwiener_3 csn csn wceq fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq wo wb fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn wceq fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq c0 fopthwiener_2 csn c0 cpr wcel c0 fopthwiener_1 csn csn wcel wn fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn wceq wn fopthwiener_2 csn c0 0ex prid2 c0 fopthwiener_1 csn csn wcel fopthwiener_1 csn c0 fopthwiener_1 eopthwiener_1 snnz c0 fopthwiener_1 csn csn wcel c0 fopthwiener_1 csn wceq fopthwiener_1 csn c0 wceq c0 fopthwiener_1 csn 0ex elsnc c0 fopthwiener_1 csn eqcom bitri nemtbir c0 fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn nelneq2 mp2an fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn eqcom mtbi fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq biorf ax-mp sylibr preq2d eqtr4d fopthwiener_0 csn c0 cpr fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn fopthwiener_0 csn c0 prex fopthwiener_2 csn c0 prex preqr1 syl fopthwiener_0 csn fopthwiener_2 csn c0 fopthwiener_0 snex fopthwiener_2 snex preqr1 syl fopthwiener_0 fopthwiener_2 eopthwiener_0 sneqr syl fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn fopthwiener_3 csn wceq fopthwiener_1 fopthwiener_3 wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq fopthwiener_1 csn fopthwiener_3 csn wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq wo fopthwiener_1 csn csn fopthwiener_3 csn csn wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wcel fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq wo fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wceq fopthwiener_1 csn csn fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr wcel fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr wcel fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn fopthwiener_1 csn snex prid2 fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr fopthwiener_1 csn csn eleq2 mpbii fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn fopthwiener_1 csn snex elpr sylib fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq wn fopthwiener_1 csn csn fopthwiener_3 csn csn wceq fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq wo wb fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn wceq fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq c0 fopthwiener_2 csn c0 cpr wcel c0 fopthwiener_1 csn csn wcel wn fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn wceq wn fopthwiener_2 csn c0 0ex prid2 c0 fopthwiener_1 csn csn wcel fopthwiener_1 csn c0 fopthwiener_1 eopthwiener_1 snnz c0 fopthwiener_1 csn csn wcel c0 fopthwiener_1 csn wceq fopthwiener_1 csn c0 wceq c0 fopthwiener_1 csn 0ex elsnc c0 fopthwiener_1 csn eqcom bitri nemtbir c0 fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn nelneq2 mp2an fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn eqcom mtbi fopthwiener_1 csn csn fopthwiener_2 csn c0 cpr wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq biorf ax-mp sylibr fopthwiener_1 csn fopthwiener_3 csn fopthwiener_1 snex sneqr syl fopthwiener_1 fopthwiener_3 eopthwiener_1 sneqr syl jca fopthwiener_0 fopthwiener_2 wceq fopthwiener_1 fopthwiener_3 wceq fopthwiener_0 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn cpr fopthwiener_2 csn c0 cpr fopthwiener_3 csn csn cpr fopthwiener_0 fopthwiener_2 wceq fopthwiener_0 csn c0 cpr fopthwiener_2 csn c0 cpr fopthwiener_1 csn csn fopthwiener_0 fopthwiener_2 wceq fopthwiener_0 csn fopthwiener_2 csn c0 fopthwiener_0 fopthwiener_2 sneq preq1d preq1d fopthwiener_1 fopthwiener_3 wceq fopthwiener_1 csn csn fopthwiener_3 csn csn fopthwiener_2 csn c0 cpr fopthwiener_1 fopthwiener_3 wceq fopthwiener_1 csn fopthwiener_3 csn wceq fopthwiener_1 csn csn fopthwiener_3 csn csn wceq fopthwiener_1 fopthwiener_3 sneq fopthwiener_1 csn fopthwiener_3 csn sneq syl preq2d sylan9eq impbii $.
$}
$( The union of an ordered pair.  Theorem 65 of [Suppes] p. 39.
       (Contributed by NM, 17-Aug-2004.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	funiop_0 $f class A $.
	funiop_1 $f class B $.
	euniop_0 $e |- A e. _V $.
	euniop_1 $e |- B e. _V $.
	uniop $p |- U. <. A , B >. = { A , B } $= funiop_0 funiop_1 cop cuni funiop_0 csn funiop_0 funiop_1 cpr cpr cuni funiop_0 csn funiop_0 funiop_1 cpr cun funiop_0 funiop_1 cpr funiop_0 funiop_1 cop funiop_0 csn funiop_0 funiop_1 cpr cpr funiop_0 funiop_1 euniop_0 euniop_1 dfop unieqi funiop_0 csn funiop_0 funiop_1 cpr funiop_0 snex funiop_0 funiop_1 prex unipr funiop_0 csn funiop_0 funiop_1 cpr wss funiop_0 csn funiop_0 funiop_1 cpr cun funiop_0 funiop_1 cpr wceq funiop_0 funiop_1 snsspr1 funiop_0 csn funiop_0 funiop_1 cpr ssequn1 mpbi 3eqtri $.
$}
$( Ordered pair membership is inherited by class union.  (Contributed by
       NM, 13-May-2008.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	funiopel_0 $f class A $.
	funiopel_1 $f class B $.
	funiopel_2 $f class C $.
	euniopel_0 $e |- A e. _V $.
	euniopel_1 $e |- B e. _V $.
	uniopel $p |- ( <. A , B >. e. C -> U. <. A , B >. e. U. C ) $= funiopel_0 funiopel_1 cop funiopel_2 wcel funiopel_0 funiopel_1 cop cuni funiopel_0 funiopel_1 cop wcel funiopel_0 funiopel_1 cop cuni funiopel_2 cuni wcel funiopel_0 funiopel_1 cop cuni funiopel_0 funiopel_1 cpr funiopel_0 funiopel_1 cop funiopel_0 funiopel_1 euniopel_0 euniopel_1 uniop funiopel_0 funiopel_1 euniopel_0 euniopel_1 opi2 eqeltri funiopel_0 funiopel_1 cop funiopel_2 wcel funiopel_0 funiopel_1 cop funiopel_2 cuni funiopel_0 funiopel_1 cop cuni funiopel_0 funiopel_1 cop funiopel_2 elssuni sseld mpi $.
$}

