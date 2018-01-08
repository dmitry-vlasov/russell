$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Ordered-pair_class_abstractions_(class_builders).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Transitive classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare a new symbol. $)
$c Tr  $.
$( Transitive predicate (read:  "the following class is
              transitive") $)
$( Extend wff notation to include transitive classes.  Notation from
     [TakeutiZaring] p. 35. $)
${
	fwtr_0 $f class A $.
	wtr $a wff Tr A $.
$}
$( Define the transitive class predicate.  Not to be confused with a
     transitive relation (see ~ cotr ).  Definition of [Enderton] p. 71
     extended to arbitrary classes.  For alternate definitions, see ~ dftr2
     (which is suggestive of the word "transitive"), ~ dftr3 , ~ dftr4 ,
     ~ dftr5 , and (when ` A ` is a set) ~ unisuc .  The term "complete" is
     used instead of "transitive" in Definition 3 of [Suppes] p. 130.
     (Contributed by NM, 29-Aug-1993.) $)
${
	fdf-tr_0 $f class A $.
	df-tr $a |- ( Tr A <-> U. A C_ A ) $.
$}
$( An alternate way of defining a transitive class.  Exercise 7 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 24-Apr-1994.) $)
${
	$d x y A $.
	fdftr2_0 $f set x $.
	fdftr2_1 $f set y $.
	fdftr2_2 $f class A $.
	dftr2 $p |- ( Tr A <-> A. x A. y ( ( x e. y /\ y e. A ) -> x e. A ) ) $= fdftr2_2 cuni fdftr2_2 wss fdftr2_0 cv fdftr2_2 cuni wcel fdftr2_0 cv fdftr2_2 wcel wi fdftr2_0 wal fdftr2_2 wtr fdftr2_0 cv fdftr2_1 cv wcel fdftr2_1 cv fdftr2_2 wcel wa fdftr2_0 cv fdftr2_2 wcel wi fdftr2_1 wal fdftr2_0 wal fdftr2_0 fdftr2_2 cuni fdftr2_2 dfss2 fdftr2_2 df-tr fdftr2_0 cv fdftr2_1 cv wcel fdftr2_1 cv fdftr2_2 wcel wa fdftr2_0 cv fdftr2_2 wcel wi fdftr2_1 wal fdftr2_0 cv fdftr2_2 cuni wcel fdftr2_0 cv fdftr2_2 wcel wi fdftr2_0 fdftr2_0 cv fdftr2_1 cv wcel fdftr2_1 cv fdftr2_2 wcel wa fdftr2_0 cv fdftr2_2 wcel wi fdftr2_1 wal fdftr2_0 cv fdftr2_1 cv wcel fdftr2_1 cv fdftr2_2 wcel wa fdftr2_1 wex fdftr2_0 cv fdftr2_2 wcel wi fdftr2_0 cv fdftr2_2 cuni wcel fdftr2_0 cv fdftr2_2 wcel wi fdftr2_0 cv fdftr2_1 cv wcel fdftr2_1 cv fdftr2_2 wcel wa fdftr2_0 cv fdftr2_2 wcel fdftr2_1 19.23v fdftr2_0 cv fdftr2_2 cuni wcel fdftr2_0 cv fdftr2_1 cv wcel fdftr2_1 cv fdftr2_2 wcel wa fdftr2_1 wex fdftr2_0 cv fdftr2_2 wcel fdftr2_1 fdftr2_0 cv fdftr2_2 eluni imbi1i bitr4i albii 3bitr4i $.
$}
$( An alternate way of defining a transitive class.  (Contributed by NM,
       20-Mar-2004.) $)
${
	$d x y A $.
	fdftr5_0 $f set x $.
	fdftr5_1 $f set y $.
	fdftr5_2 $f class A $.
	dftr5 $p |- ( Tr A <-> A. x e. A A. y e. x y e. A ) $= fdftr5_2 wtr fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_0 wal fdftr5_1 wal fdftr5_1 cv fdftr5_2 wcel fdftr5_1 fdftr5_0 cv wral fdftr5_0 fdftr5_2 wral fdftr5_1 fdftr5_0 fdftr5_2 dftr2 fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_0 wal fdftr5_1 wal fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 wal fdftr5_0 wal fdftr5_1 cv fdftr5_2 wcel fdftr5_1 fdftr5_0 cv wral fdftr5_0 fdftr5_2 wral fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 fdftr5_0 alcom fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 wal fdftr5_0 wal fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel fdftr5_1 fdftr5_0 cv wral wi fdftr5_0 wal fdftr5_1 cv fdftr5_2 wcel fdftr5_1 fdftr5_0 cv wral fdftr5_0 fdftr5_2 wral fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 wal fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel fdftr5_1 fdftr5_0 cv wral wi fdftr5_0 fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 wal fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 fdftr5_0 cv wral fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel fdftr5_1 fdftr5_0 cv wral wi fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 wal fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel wi wi fdftr5_1 wal fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 fdftr5_0 cv wral fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel wa fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel wi wi fdftr5_1 fdftr5_1 cv fdftr5_0 cv wcel fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel impexp albii fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel wi fdftr5_1 fdftr5_0 cv df-ral bitr4i fdftr5_0 cv fdftr5_2 wcel fdftr5_1 cv fdftr5_2 wcel fdftr5_1 fdftr5_0 cv r19.21v bitri albii fdftr5_1 cv fdftr5_2 wcel fdftr5_1 fdftr5_0 cv wral fdftr5_0 fdftr5_2 df-ral bitr4i bitri bitri $.
$}
$( An alternate way of defining a transitive class.  Definition 7.1 of
       [TakeutiZaring] p. 35.  (Contributed by NM, 29-Aug-1993.) $)
${
	$d x y A $.
	idftr3_0 $f set y $.
	fdftr3_0 $f set x $.
	fdftr3_1 $f class A $.
	dftr3 $p |- ( Tr A <-> A. x e. A x C_ A ) $= fdftr3_1 wtr idftr3_0 cv fdftr3_1 wcel idftr3_0 fdftr3_0 cv wral fdftr3_0 fdftr3_1 wral fdftr3_0 cv fdftr3_1 wss fdftr3_0 fdftr3_1 wral fdftr3_0 idftr3_0 fdftr3_1 dftr5 fdftr3_0 cv fdftr3_1 wss idftr3_0 cv fdftr3_1 wcel idftr3_0 fdftr3_0 cv wral fdftr3_0 fdftr3_1 idftr3_0 fdftr3_0 cv fdftr3_1 dfss3 ralbii bitr4i $.
$}
$( An alternate way of defining a transitive class.  Definition of [Enderton]
     p. 71.  (Contributed by NM, 29-Aug-1993.) $)
${
	fdftr4_0 $f class A $.
	dftr4 $p |- ( Tr A <-> A C_ ~P A ) $= fdftr4_0 wtr fdftr4_0 cuni fdftr4_0 wss fdftr4_0 fdftr4_0 cpw wss fdftr4_0 df-tr fdftr4_0 fdftr4_0 sspwuni bitr4i $.
$}
$( Equality theorem for the transitive class predicate.  (Contributed by NM,
     17-Sep-1993.) $)
${
	ftreq_0 $f class A $.
	ftreq_1 $f class B $.
	treq $p |- ( A = B -> ( Tr A <-> Tr B ) ) $= ftreq_0 ftreq_1 wceq ftreq_0 cuni ftreq_0 wss ftreq_1 cuni ftreq_1 wss ftreq_0 wtr ftreq_1 wtr ftreq_0 ftreq_1 wceq ftreq_0 cuni ftreq_0 wss ftreq_1 cuni ftreq_0 wss ftreq_1 cuni ftreq_1 wss ftreq_0 ftreq_1 wceq ftreq_0 cuni ftreq_1 cuni ftreq_0 ftreq_0 ftreq_1 unieq sseq1d ftreq_0 ftreq_1 ftreq_1 cuni sseq2 bitrd ftreq_0 df-tr ftreq_1 df-tr 3bitr4g $.
$}
$( In a transitive class, the membership relation is transitive.
       (Contributed by NM, 19-Apr-1994.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	itrel_0 $f set x $.
	itrel_1 $f set y $.
	ftrel_0 $f class A $.
	ftrel_1 $f class B $.
	ftrel_2 $f class C $.
	trel $p |- ( Tr A -> ( ( B e. C /\ C e. A ) -> B e. A ) ) $= ftrel_0 wtr itrel_1 cv itrel_0 cv wcel itrel_0 cv ftrel_0 wcel wa itrel_1 cv ftrel_0 wcel wi itrel_0 wal itrel_1 wal ftrel_1 ftrel_2 wcel ftrel_2 ftrel_0 wcel wa ftrel_1 ftrel_0 wcel wi itrel_1 itrel_0 ftrel_0 dftr2 itrel_1 cv itrel_0 cv wcel itrel_0 cv ftrel_0 wcel wa itrel_1 cv ftrel_0 wcel wi itrel_0 wal itrel_1 wal ftrel_1 ftrel_2 wcel ftrel_2 ftrel_0 wcel wa ftrel_1 ftrel_0 wcel itrel_1 cv itrel_0 cv wcel itrel_0 cv ftrel_0 wcel wa itrel_1 cv ftrel_0 wcel wi ftrel_1 ftrel_2 wcel ftrel_2 ftrel_0 wcel wa ftrel_1 ftrel_0 wcel wi itrel_1 itrel_0 ftrel_1 ftrel_2 ftrel_2 ftrel_0 itrel_1 cv ftrel_1 wceq itrel_0 cv ftrel_2 wceq wa itrel_1 cv itrel_0 cv wcel itrel_0 cv ftrel_0 wcel wa ftrel_1 ftrel_2 wcel ftrel_2 ftrel_0 wcel wa itrel_1 cv ftrel_0 wcel ftrel_1 ftrel_0 wcel itrel_1 cv ftrel_1 wceq itrel_0 cv ftrel_2 wceq wa itrel_1 cv itrel_0 cv wcel ftrel_1 ftrel_2 wcel itrel_0 cv ftrel_0 wcel ftrel_2 ftrel_0 wcel itrel_1 cv ftrel_1 itrel_0 cv ftrel_2 eleq12 itrel_0 cv ftrel_2 wceq itrel_0 cv ftrel_0 wcel ftrel_2 ftrel_0 wcel wb itrel_1 cv ftrel_1 wceq itrel_0 cv ftrel_2 ftrel_0 eleq1 adantl anbi12d itrel_1 cv ftrel_1 wceq itrel_1 cv ftrel_0 wcel ftrel_1 ftrel_0 wcel wb itrel_0 cv ftrel_2 wceq itrel_1 cv ftrel_1 ftrel_0 eleq1 adantr imbi12d spc2gv pm2.43b sylbi $.
$}
$( In a transitive class, the membership relation is transitive.
     (Contributed by NM, 19-Apr-1994.) $)
${
	ftrel3_0 $f class A $.
	ftrel3_1 $f class B $.
	ftrel3_2 $f class C $.
	ftrel3_3 $f class D $.
	trel3 $p |- ( Tr A -> ( ( B e. C /\ C e. D /\ D e. A ) -> B e. A ) ) $= ftrel3_0 wtr ftrel3_1 ftrel3_2 wcel ftrel3_2 ftrel3_3 wcel ftrel3_3 ftrel3_0 wcel w3a ftrel3_1 ftrel3_2 wcel ftrel3_2 ftrel3_0 wcel wa ftrel3_1 ftrel3_0 wcel ftrel3_1 ftrel3_2 wcel ftrel3_2 ftrel3_3 wcel ftrel3_3 ftrel3_0 wcel w3a ftrel3_1 ftrel3_2 wcel ftrel3_2 ftrel3_3 wcel ftrel3_3 ftrel3_0 wcel wa wa ftrel3_0 wtr ftrel3_1 ftrel3_2 wcel ftrel3_2 ftrel3_0 wcel wa ftrel3_1 ftrel3_2 wcel ftrel3_2 ftrel3_3 wcel ftrel3_3 ftrel3_0 wcel 3anass ftrel3_0 wtr ftrel3_2 ftrel3_3 wcel ftrel3_3 ftrel3_0 wcel wa ftrel3_2 ftrel3_0 wcel ftrel3_1 ftrel3_2 wcel ftrel3_0 ftrel3_2 ftrel3_3 trel anim2d syl5bi ftrel3_0 ftrel3_1 ftrel3_2 trel syld $.
$}
$( An element of a transitive class is a subset of the class.  (Contributed
       by NM, 7-Aug-1994.) $)
${
	$d x A $.
	$d x B $.
	itrss_0 $f set x $.
	ftrss_0 $f class A $.
	ftrss_1 $f class B $.
	trss $p |- ( Tr A -> ( B e. A -> B C_ A ) ) $= ftrss_0 wtr ftrss_1 ftrss_0 wcel ftrss_1 ftrss_0 wss ftrss_0 wtr itrss_0 cv ftrss_0 wcel itrss_0 cv ftrss_0 wss wi wi ftrss_0 wtr ftrss_1 ftrss_0 wcel ftrss_1 ftrss_0 wss wi wi itrss_0 ftrss_1 ftrss_0 itrss_0 cv ftrss_1 wceq itrss_0 cv ftrss_0 wcel itrss_0 cv ftrss_0 wss wi ftrss_1 ftrss_0 wcel ftrss_1 ftrss_0 wss wi ftrss_0 wtr itrss_0 cv ftrss_1 wceq itrss_0 cv ftrss_0 wcel ftrss_1 ftrss_0 wcel itrss_0 cv ftrss_0 wss ftrss_1 ftrss_0 wss itrss_0 cv ftrss_1 ftrss_0 eleq1 itrss_0 cv ftrss_1 ftrss_0 sseq1 imbi12d imbi2d ftrss_0 wtr itrss_0 cv ftrss_0 wss itrss_0 ftrss_0 wral itrss_0 cv ftrss_0 wcel itrss_0 cv ftrss_0 wss wi itrss_0 ftrss_0 dftr3 itrss_0 cv ftrss_0 wss itrss_0 ftrss_0 rsp sylbi vtoclg pm2.43b $.
$}
$( The intersection of transitive classes is transitive.  (Contributed by
       NM, 9-May-1994.) $)
${
	$d x A $.
	$d x B $.
	itrin_0 $f set x $.
	ftrin_0 $f class A $.
	ftrin_1 $f class B $.
	trin $p |- ( ( Tr A /\ Tr B ) -> Tr ( A i^i B ) ) $= ftrin_0 wtr ftrin_1 wtr wa itrin_0 cv ftrin_0 ftrin_1 cin wss itrin_0 ftrin_0 ftrin_1 cin wral ftrin_0 ftrin_1 cin wtr ftrin_0 wtr ftrin_1 wtr wa itrin_0 cv ftrin_0 ftrin_1 cin wss itrin_0 ftrin_0 ftrin_1 cin ftrin_0 wtr ftrin_1 wtr wa itrin_0 cv ftrin_0 ftrin_1 cin wcel itrin_0 cv ftrin_0 wss itrin_0 cv ftrin_1 wss wa itrin_0 cv ftrin_0 ftrin_1 cin wss itrin_0 cv ftrin_0 ftrin_1 cin wcel itrin_0 cv ftrin_0 wcel itrin_0 cv ftrin_1 wcel wa ftrin_0 wtr ftrin_1 wtr wa itrin_0 cv ftrin_0 wss itrin_0 cv ftrin_1 wss wa itrin_0 cv ftrin_0 ftrin_1 elin ftrin_0 wtr itrin_0 cv ftrin_0 wcel itrin_0 cv ftrin_0 wss ftrin_1 wtr itrin_0 cv ftrin_1 wcel itrin_0 cv ftrin_1 wss ftrin_0 itrin_0 cv trss ftrin_1 itrin_0 cv trss im2anan9 syl5bi itrin_0 cv ftrin_0 ftrin_1 ssin syl6ib ralrimiv itrin_0 ftrin_0 ftrin_1 cin dftr3 sylibr $.
$}
$( The empty set is transitive.  (Contributed by NM, 16-Sep-1993.) $)
${
	tr0 $p |- Tr (/) $= c0 wtr c0 c0 cpw wss c0 cpw 0ss c0 dftr4 mpbir $.
$}
$( The universe is transitive.  (Contributed by NM, 14-Sep-2003.) $)
${
	trv $p |- Tr _V $= cvv wtr cvv cuni cvv wss cvv cuni ssv cvv df-tr mpbir $.
$}
$( The indexed union of a class of transitive sets is transitive.
       (Contributed by Mario Carneiro, 16-Nov-2014.) $)
${
	$d x y A $.
	$d y B $.
	itriun_0 $f set y $.
	ftriun_0 $f set x $.
	ftriun_1 $f class A $.
	ftriun_2 $f class B $.
	triun $p |- ( A. x e. A Tr B -> Tr U_ x e. A B ) $= ftriun_2 wtr ftriun_0 ftriun_1 wral itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun wss itriun_0 ftriun_0 ftriun_1 ftriun_2 ciun wral ftriun_0 ftriun_1 ftriun_2 ciun wtr ftriun_2 wtr ftriun_0 ftriun_1 wral itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun wss itriun_0 ftriun_0 ftriun_1 ftriun_2 ciun itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun wcel ftriun_2 wtr ftriun_0 ftriun_1 wral itriun_0 cv ftriun_2 wcel ftriun_0 ftriun_1 wrex itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun wss ftriun_0 itriun_0 cv ftriun_1 ftriun_2 eliun ftriun_2 wtr ftriun_0 ftriun_1 wral itriun_0 cv ftriun_2 wcel ftriun_0 ftriun_1 wrex wa ftriun_2 wtr itriun_0 cv ftriun_2 wcel wa ftriun_0 ftriun_1 wrex itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun wss ftriun_2 wtr itriun_0 cv ftriun_2 wcel ftriun_0 ftriun_1 r19.29 ftriun_2 wtr itriun_0 cv ftriun_2 wcel wa itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun wss ftriun_0 ftriun_1 ftriun_0 itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun ftriun_0 itriun_0 cv nfcv ftriun_0 ftriun_1 ftriun_2 nfiu1 nfss ftriun_2 wtr itriun_0 cv ftriun_2 wcel wa itriun_0 cv ftriun_2 wss ftriun_0 cv ftriun_1 wcel itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun wss ftriun_2 wtr itriun_0 cv ftriun_2 wcel itriun_0 cv ftriun_2 wss ftriun_2 itriun_0 cv trss imp ftriun_0 cv ftriun_1 wcel ftriun_2 ftriun_0 ftriun_1 ftriun_2 ciun wss itriun_0 cv ftriun_2 wss itriun_0 cv ftriun_0 ftriun_1 ftriun_2 ciun wss ftriun_0 ftriun_1 ftriun_2 ssiun2 itriun_0 cv ftriun_2 ftriun_0 ftriun_1 ftriun_2 ciun sstr2 syl5com syl5 rexlimi syl sylan2b ralrimiva itriun_0 ftriun_0 ftriun_1 ftriun_2 ciun dftr3 sylibr $.
$}
$( The union of a class of transitive sets is transitive.  Exercise 5(a) of
       [Enderton] p. 73.  (Contributed by Scott Fenton, 21-Feb-2011.)  (Proof
       shortened by Mario Carneiro, 26-Apr-2014.) $)
${
	$d x A $.
	ftruni_0 $f set x $.
	ftruni_1 $f class A $.
	truni $p |- ( A. x e. A Tr x -> Tr U. A ) $= ftruni_0 cv wtr ftruni_0 ftruni_1 wral ftruni_0 ftruni_1 ftruni_0 cv ciun wtr ftruni_1 cuni wtr ftruni_0 ftruni_1 ftruni_0 cv triun ftruni_1 cuni ftruni_0 ftruni_1 ftruni_0 cv ciun wceq ftruni_1 cuni wtr ftruni_0 ftruni_1 ftruni_0 cv ciun wtr wb ftruni_0 ftruni_1 uniiun ftruni_1 cuni ftruni_0 ftruni_1 ftruni_0 cv ciun treq ax-mp sylibr $.
$}
$( The intersection of a class of transitive sets is transitive.  Exercise
       5(b) of [Enderton] p. 73.  (Contributed by Scott Fenton,
       25-Feb-2011.) $)
${
	$d x y A $.
	itrint_0 $f set y $.
	ftrint_0 $f set x $.
	ftrint_1 $f class A $.
	trint $p |- ( A. x e. A Tr x -> Tr |^| A ) $= ftrint_0 cv wtr ftrint_0 ftrint_1 wral itrint_0 ftrint_0 wel ftrint_0 ftrint_1 wral itrint_0 cv ftrint_0 cv wss ftrint_0 ftrint_1 wral wi itrint_0 wal ftrint_1 cint wtr ftrint_0 cv wtr ftrint_0 ftrint_1 wral itrint_0 ftrint_0 wel itrint_0 cv ftrint_0 cv wss wi ftrint_0 ftrint_1 wral itrint_0 wal itrint_0 ftrint_0 wel ftrint_0 ftrint_1 wral itrint_0 cv ftrint_0 cv wss ftrint_0 ftrint_1 wral wi itrint_0 wal ftrint_0 cv wtr ftrint_0 ftrint_1 wral itrint_0 cv ftrint_0 cv wss itrint_0 ftrint_0 cv wral ftrint_0 ftrint_1 wral itrint_0 ftrint_0 wel itrint_0 cv ftrint_0 cv wss wi ftrint_0 ftrint_1 wral itrint_0 wal ftrint_0 cv wtr ftrint_0 ftrint_1 wral itrint_0 cv ftrint_0 cv wss itrint_0 ftrint_0 cv wral ftrint_0 ftrint_1 wral ftrint_0 cv wtr itrint_0 cv ftrint_0 cv wss itrint_0 ftrint_0 cv wral ftrint_0 ftrint_1 itrint_0 ftrint_0 cv dftr3 ralbii biimpi itrint_0 cv ftrint_0 cv wss itrint_0 ftrint_0 cv wral ftrint_0 ftrint_1 wral itrint_0 ftrint_0 wel itrint_0 cv ftrint_0 cv wss wi itrint_0 wal ftrint_0 ftrint_1 wral itrint_0 ftrint_0 wel itrint_0 cv ftrint_0 cv wss wi ftrint_0 ftrint_1 wral itrint_0 wal itrint_0 cv ftrint_0 cv wss itrint_0 ftrint_0 cv wral itrint_0 ftrint_0 wel itrint_0 cv ftrint_0 cv wss wi itrint_0 wal ftrint_0 ftrint_1 itrint_0 cv ftrint_0 cv wss itrint_0 ftrint_0 cv df-ral ralbii itrint_0 ftrint_0 wel itrint_0 cv ftrint_0 cv wss wi ftrint_0 itrint_0 ftrint_1 ralcom4 bitri sylib itrint_0 ftrint_0 wel itrint_0 cv ftrint_0 cv wss wi ftrint_0 ftrint_1 wral itrint_0 ftrint_0 wel ftrint_0 ftrint_1 wral itrint_0 cv ftrint_0 cv wss ftrint_0 ftrint_1 wral wi itrint_0 itrint_0 ftrint_0 wel itrint_0 cv ftrint_0 cv wss ftrint_0 ftrint_1 ralim alimi syl ftrint_1 cint wtr itrint_0 cv ftrint_1 cint wss itrint_0 ftrint_1 cint wral itrint_0 ftrint_0 wel ftrint_0 ftrint_1 wral itrint_0 cv ftrint_0 cv wss ftrint_0 ftrint_1 wral wi itrint_0 wal itrint_0 ftrint_1 cint dftr3 itrint_0 cv ftrint_1 cint wss itrint_0 ftrint_1 cint wral itrint_0 cv ftrint_1 cint wcel itrint_0 cv ftrint_1 cint wss wi itrint_0 wal itrint_0 ftrint_0 wel ftrint_0 ftrint_1 wral itrint_0 cv ftrint_0 cv wss ftrint_0 ftrint_1 wral wi itrint_0 wal itrint_0 cv ftrint_1 cint wss itrint_0 ftrint_1 cint df-ral itrint_0 cv ftrint_1 cint wcel itrint_0 cv ftrint_1 cint wss wi itrint_0 ftrint_0 wel ftrint_0 ftrint_1 wral itrint_0 cv ftrint_0 cv wss ftrint_0 ftrint_1 wral wi itrint_0 itrint_0 cv ftrint_1 cint wcel itrint_0 ftrint_0 wel ftrint_0 ftrint_1 wral itrint_0 cv ftrint_1 cint wss itrint_0 cv ftrint_0 cv wss ftrint_0 ftrint_1 wral ftrint_0 itrint_0 cv ftrint_1 itrint_0 vex elint2 ftrint_0 itrint_0 cv ftrint_1 ssint imbi12i albii bitri bitri sylibr $.
$}
$( If ` A ` is transitive and non-null, then ` |^| A ` is a subset of
       ` A ` .  (Contributed by Scott Fenton, 3-Mar-2011.) $)
${
	$d x y A $.
	itrintss_0 $f set x $.
	itrintss_1 $f set y $.
	ftrintss_0 $f class A $.
	trintss $p |- ( ( A =/= (/) /\ Tr A ) -> |^| A C_ A ) $= ftrintss_0 c0 wne ftrintss_0 wtr wa itrintss_1 ftrintss_0 cint ftrintss_0 itrintss_1 cv ftrintss_0 cint wcel itrintss_1 itrintss_0 wel itrintss_0 ftrintss_0 wral ftrintss_0 c0 wne ftrintss_0 wtr wa itrintss_1 cv ftrintss_0 wcel itrintss_0 itrintss_1 cv ftrintss_0 itrintss_1 vex elint2 ftrintss_0 c0 wne itrintss_1 itrintss_0 wel itrintss_0 ftrintss_0 wral itrintss_1 itrintss_0 wel itrintss_0 ftrintss_0 wrex ftrintss_0 wtr itrintss_1 cv ftrintss_0 wcel ftrintss_0 c0 wne itrintss_1 itrintss_0 wel itrintss_0 ftrintss_0 wral itrintss_1 itrintss_0 wel itrintss_0 ftrintss_0 wrex itrintss_1 itrintss_0 wel itrintss_0 ftrintss_0 r19.2z ex ftrintss_0 wtr itrintss_1 itrintss_0 wel itrintss_1 cv ftrintss_0 wcel itrintss_0 ftrintss_0 ftrintss_0 wtr itrintss_1 itrintss_0 wel itrintss_0 cv ftrintss_0 wcel itrintss_1 cv ftrintss_0 wcel ftrintss_0 itrintss_1 cv itrintss_0 cv trel exp3acom23 rexlimdv sylan9 syl5bi ssrdv $.
$}
$( Any non-empty transitive class includes its intersection.  Exercise 2 in
       [TakeutiZaring] p. 44.  (Contributed by Andrew Salmon, 14-Nov-2011.) $)
${
	$d x A $.
	itrint0_0 $f set x $.
	ftrint0_0 $f class A $.
	trint0 $p |- ( ( Tr A /\ A =/= (/) ) -> |^| A C_ A ) $= ftrint0_0 c0 wne ftrint0_0 wtr ftrint0_0 cint ftrint0_0 wss ftrint0_0 c0 wne itrint0_0 cv ftrint0_0 wcel itrint0_0 wex ftrint0_0 wtr ftrint0_0 cint ftrint0_0 wss wi itrint0_0 ftrint0_0 n0 itrint0_0 cv ftrint0_0 wcel ftrint0_0 wtr ftrint0_0 cint ftrint0_0 wss wi itrint0_0 itrint0_0 cv ftrint0_0 wcel ftrint0_0 cint itrint0_0 cv wss ftrint0_0 wtr itrint0_0 cv ftrint0_0 wss ftrint0_0 cint ftrint0_0 wss itrint0_0 cv ftrint0_0 intss1 ftrint0_0 wtr itrint0_0 cv ftrint0_0 wcel itrint0_0 cv ftrint0_0 wss ftrint0_0 itrint0_0 cv trss com12 ftrint0_0 cint itrint0_0 cv ftrint0_0 sstr2 sylsyld exlimiv sylbi impcom $.
$}

