$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Power_class_of_union_and_intersection.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Epsilon and identity relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare new constant symbols. $)
$c _E  $.
$( Letter E (for epsilon relation) $)
$c _I  $.
$( Letter I (for identity relation) $)
$( Extend class notation to include the epsilon relation. $)
${
	cep $a class _E $.
$}
$( Extend the definition of a class to include identity relation. $)
${
	cid $a class _I $.
$}
$( Define the epsilon relation.  Similar to Definition 6.22 of
       [TakeutiZaring] p. 30.  The epsilon relation and set membership are the
       same, that is, ` ( A _E B <-> A e. B ) ` when ` B ` is a set by
       ~ epelg .  Thus, ` 5 _E { 1 , 5 } ` ( ~ ex-eprel ).  (Contributed by NM,
       13-Aug-1995.) $)
${
	$d x y $.
	fdf-eprel_0 $f set x $.
	fdf-eprel_1 $f set y $.
	df-eprel $a |- _E = { <. x , y >. | x e. y } $.
$}
$( The epsilon relation and membership are the same.  General version of
       ~ epel .  (Contributed by Scott Fenton, 27-Mar-2011.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
${
	$d A x y $.
	$d B x y $.
	iepelg_0 $f set x $.
	iepelg_1 $f set y $.
	fepelg_0 $f class A $.
	fepelg_1 $f class B $.
	fepelg_2 $f class V $.
	epelg $p |- ( B e. V -> ( A _E B <-> A e. B ) ) $= fepelg_1 fepelg_2 wcel fepelg_0 cvv wcel fepelg_0 fepelg_1 cep wbr fepelg_0 fepelg_1 wcel fepelg_0 fepelg_1 cep wbr fepelg_0 cvv wcel wi fepelg_1 fepelg_2 wcel fepelg_0 fepelg_1 cep wbr fepelg_0 fepelg_1 cop cep wcel fepelg_0 cvv wcel fepelg_0 fepelg_1 cep df-br fepelg_0 cvv wcel fepelg_0 fepelg_1 cop iepelg_0 cv iepelg_1 cv wcel iepelg_0 iepelg_1 copab cep fepelg_0 fepelg_1 cop iepelg_0 cv iepelg_1 cv wcel iepelg_0 iepelg_1 copab wcel fepelg_0 fepelg_1 cop iepelg_0 cv iepelg_1 cv cop wceq iepelg_0 cv iepelg_1 cv wcel wa iepelg_1 wex iepelg_0 wex fepelg_0 cvv wcel iepelg_0 cv iepelg_1 cv wcel iepelg_0 iepelg_1 fepelg_0 fepelg_1 cop elopab fepelg_0 fepelg_1 cop iepelg_0 cv iepelg_1 cv cop wceq iepelg_0 cv iepelg_1 cv wcel wa fepelg_0 cvv wcel iepelg_0 iepelg_1 fepelg_0 fepelg_1 cop iepelg_0 cv iepelg_1 cv cop wceq fepelg_0 cvv wcel iepelg_0 cv iepelg_1 cv wcel fepelg_0 fepelg_1 cop iepelg_0 cv iepelg_1 cv cop wceq fepelg_0 cvv wcel fepelg_1 cvv wcel fepelg_0 fepelg_1 cop iepelg_0 cv iepelg_1 cv cop wceq fepelg_0 cvv wcel fepelg_1 cvv wcel wa iepelg_0 cv cvv wcel iepelg_1 cv cvv wcel wa iepelg_0 cv cvv wcel iepelg_1 cv cvv wcel iepelg_0 vex iepelg_1 vex pm3.2i fepelg_0 fepelg_1 iepelg_0 cv iepelg_1 cv opeqex mpbiri simpld adantr exlimivv sylbi iepelg_0 iepelg_1 df-eprel eleq2s sylbi a1i fepelg_0 fepelg_1 wcel fepelg_0 cvv wcel wi fepelg_1 fepelg_2 wcel fepelg_0 fepelg_1 elex a1i fepelg_0 cvv wcel fepelg_1 fepelg_2 wcel fepelg_0 fepelg_1 cep wbr fepelg_0 fepelg_1 wcel wb iepelg_0 cv iepelg_1 cv wcel fepelg_0 fepelg_1 wcel iepelg_0 iepelg_1 fepelg_0 fepelg_1 cep cvv fepelg_2 iepelg_0 cv fepelg_0 iepelg_1 cv fepelg_1 eleq12 iepelg_0 iepelg_1 df-eprel brabga expcom pm5.21ndd $.
$}
$( The epsilon relationship and the membership relation are the same.
       (Contributed by Scott Fenton, 11-Apr-2012.) $)
${
	fepelc_0 $f class A $.
	fepelc_1 $f class B $.
	eepelc_0 $e |- B e. _V $.
	epelc $p |- ( A _E B <-> A e. B ) $= fepelc_1 cvv wcel fepelc_0 fepelc_1 cep wbr fepelc_0 fepelc_1 wcel wb eepelc_0 fepelc_0 fepelc_1 cvv epelg ax-mp $.
$}
$( The epsilon relation and the membership relation are the same.
     (Contributed by NM, 13-Aug-1995.) $)
${
	fepel_0 $f set x $.
	fepel_1 $f set y $.
	epel $p |- ( x _E y <-> x e. y ) $= fepel_0 cv fepel_1 cv fepel_1 vex epelc $.
$}
$( Define the identity relation.  Definition 9.15 of [Quine] p. 64.  For
       example, ` 5 _I 5 ` and ` -. 4 _I 5 ` ( ~ ex-id ).  (Contributed by NM,
       13-Aug-1995.) $)
${
	$d x y $.
	fdf-id_0 $f set x $.
	fdf-id_1 $f set y $.
	df-id $a |- _I = { <. x , y >. | x = y } $.
$}
$( A stronger version of ~ df-id that doesn't require ` x ` and ` y ` to be
       distinct.  Ordinarily, we wouldn't use this as a definition, since
       non-distinct dummy variables would make soundness verification more
       difficult (as the proof here shows).  The proof can be instructive in
       showing how distinct variable requirements may be eliminated, a task
       that is not necessarily obvious.  (Contributed by NM, 5-Feb-2008.)
       (Revised by Mario Carneiro, 18-Nov-2016.) $)
${
	$d w z x $.
	$d w z y $.
	idfid3_0 $f set z $.
	idfid3_1 $f set w $.
	fdfid3_0 $f set x $.
	fdfid3_1 $f set y $.
	dfid3 $p |- _I = { <. x , y >. | x = y } $= cid fdfid3_0 cv idfid3_0 cv wceq fdfid3_0 idfid3_0 copab fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 fdfid3_1 copab fdfid3_0 idfid3_0 df-id idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 wex fdfid3_0 wex idfid3_1 cab idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa fdfid3_1 wex fdfid3_0 wex idfid3_1 cab fdfid3_0 cv idfid3_0 cv wceq fdfid3_0 idfid3_0 copab fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 fdfid3_1 copab idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 wex fdfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa fdfid3_1 wex fdfid3_0 wex idfid3_1 fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 wex fdfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa fdfid3_1 wex fdfid3_0 wex wb idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 wex fdfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa fdfid3_0 wex fdfid3_0 wex fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa fdfid3_1 wex fdfid3_0 wex idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 wex fdfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa fdfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa fdfid3_0 wex fdfid3_0 wex idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa fdfid3_0 idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 wex idfid3_0 cv fdfid3_0 cv wceq idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq wa idfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 cv fdfid3_0 cv wceq idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq wa idfid3_0 idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa fdfid3_0 cv idfid3_0 cv wceq idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq wa idfid3_0 cv fdfid3_0 cv wceq idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq wa idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq ancom fdfid3_0 cv idfid3_0 cv wceq idfid3_0 cv fdfid3_0 cv wceq idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 idfid3_0 equcom anbi1i bitri exbii idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq idfid3_0 fdfid3_0 cv fdfid3_0 vex idfid3_0 cv fdfid3_0 cv wceq fdfid3_0 cv idfid3_0 cv cop fdfid3_0 cv fdfid3_0 cv cop idfid3_1 cv idfid3_0 cv fdfid3_0 cv fdfid3_0 cv opeq2 eqeq2d ceqsexv fdfid3_0 cv fdfid3_0 cv wceq idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 equid biantru 3bitri exbii idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa fdfid3_0 wex fdfid3_0 idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa fdfid3_0 nfe1 19.9 bitr4i idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa fdfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa fdfid3_1 wex fdfid3_0 fdfid3_1 fdfid3_0 idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa fdfid3_0 fdfid3_1 fdfid3_0 cv fdfid3_1 cv wceq idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq wa idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa wb fdfid3_0 fdfid3_0 cv fdfid3_1 cv wceq idfid3_1 cv fdfid3_0 cv fdfid3_0 cv cop wceq idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_0 cv wceq fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 cv fdfid3_0 cv cop fdfid3_0 cv fdfid3_1 cv cop idfid3_1 cv fdfid3_0 cv fdfid3_1 cv fdfid3_0 cv opeq2 eqeq2d fdfid3_0 fdfid3_1 fdfid3_0 equequ2 anbi12d sps drex1 drex2 syl5bb fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_0 wex idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa fdfid3_1 wex fdfid3_0 fdfid3_0 fdfid3_1 fdfid3_0 nfnae fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa idfid3_0 fdfid3_1 fdfid3_0 fdfid3_1 fdfid3_1 nfnae fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq fdfid3_1 fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn fdfid3_1 idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn fdfid3_1 idfid3_1 cv nfcvd fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn fdfid3_1 fdfid3_0 cv idfid3_0 cv fdfid3_0 fdfid3_1 nfcvf2 fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn fdfid3_1 idfid3_0 cv nfcvd nfopd nfeqd fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn fdfid3_1 fdfid3_0 cv idfid3_0 cv fdfid3_0 fdfid3_1 nfcvf2 fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn fdfid3_1 idfid3_0 cv nfcvd nfeqd nfand idfid3_0 cv fdfid3_1 cv wceq idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq wa idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv fdfid3_1 cv wceq wa wb wi fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 wal wn idfid3_0 cv fdfid3_1 cv wceq idfid3_1 cv fdfid3_0 cv idfid3_0 cv cop wceq idfid3_1 cv fdfid3_0 cv fdfid3_1 cv cop wceq fdfid3_0 cv idfid3_0 cv wceq fdfid3_0 cv fdfid3_1 cv wceq idfid3_0 cv fdfid3_1 cv wceq fdfid3_0 cv idfid3_0 cv cop fdfid3_0 cv fdfid3_1 cv cop idfid3_1 cv idfid3_0 cv fdfid3_1 cv fdfid3_0 cv opeq2 eqeq2d idfid3_0 fdfid3_1 fdfid3_0 equequ2 anbi12d a1i cbvexd exbid pm2.61i abbii fdfid3_0 cv idfid3_0 cv wceq fdfid3_0 idfid3_0 idfid3_1 df-opab fdfid3_0 cv fdfid3_1 cv wceq fdfid3_0 fdfid3_1 idfid3_1 df-opab 3eqtr4i eqtri $.
$}
$( Alternate definition of the identity relation.  (Contributed by NM,
     15-Mar-2007.) $)
${
	fdfid2_0 $f set x $.
	dfid2 $p |- _I = { <. x , x >. | x = x } $= fdfid2_0 fdfid2_0 dfid3 $.
$}

