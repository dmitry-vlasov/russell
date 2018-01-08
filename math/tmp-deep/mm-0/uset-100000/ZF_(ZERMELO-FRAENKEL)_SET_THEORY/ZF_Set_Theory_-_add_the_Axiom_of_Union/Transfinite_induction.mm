$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Ordinals_(continued).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Transfinite induction

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( The Principle of Transfinite Induction.  Theorem 7.17 of [TakeutiZaring]
       p. 39.  This principle states that if ` A ` is a class of ordinal
       numbers with the property that every ordinal number included in ` A `
       also belongs to ` A ` , then every ordinal number is in ` A ` .

       See theorem ~ tfindes or ~ tfinds for the version involving basis and
       induction hypotheses.  (Contributed by NM, 18-Feb-2004.) $)
${
	$d x A $.
	ftfi_0 $f set x $.
	ftfi_1 $f class A $.
	tfi $p |- ( ( A C_ On /\ A. x e. On ( x C_ A -> x e. A ) ) -> A = On ) $= ftfi_1 con0 wss ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi ftfi_0 con0 wral wa ftfi_1 con0 wss con0 ftfi_1 wss wa ftfi_1 con0 wceq ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi ftfi_0 con0 wral con0 ftfi_1 wss ftfi_1 con0 wss ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi ftfi_0 con0 wral con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 con0 ftfi_1 cdif wrex con0 ftfi_1 wss ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi ftfi_0 con0 wral con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq wn ftfi_0 con0 ftfi_1 cdif wral con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 con0 ftfi_1 cdif wrex wn ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq wn ftfi_0 con0 con0 ftfi_1 cdif ftfi_0 cv con0 wcel ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi wi ftfi_0 cv con0 ftfi_1 cdif wcel con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq wn ftfi_0 cv con0 wcel ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi wi ftfi_0 cv con0 ftfi_1 cdif wcel wa con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 cv ftfi_1 wcel ftfi_0 cv con0 ftfi_1 cdif wcel ftfi_0 cv ftfi_1 wcel wn ftfi_0 cv con0 wcel ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi wi ftfi_0 cv con0 ftfi_1 eldifn adantl ftfi_0 cv con0 wcel ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi wi ftfi_0 cv con0 ftfi_1 cdif wcel con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 cv ftfi_1 wcel wi ftfi_0 cv con0 ftfi_1 cdif wcel ftfi_0 cv con0 wcel ftfi_0 cv con0 wcel ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi wi con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 cv ftfi_1 wcel wi ftfi_0 cv con0 ftfi_1 eldifi ftfi_0 cv con0 wcel ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel wi con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 cv ftfi_1 wcel wi ftfi_0 cv con0 wcel con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 cv ftfi_1 wss ftfi_0 cv ftfi_1 wcel ftfi_0 cv con0 wcel ftfi_0 cv con0 wss con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 cv ftfi_1 wss ftfi_0 cv onss con0 ftfi_1 ftfi_0 cv difin0ss syl5com imim1d a2i syl5 imp mtod ex ralimi2 con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 con0 ftfi_1 cdif ralnex sylib con0 ftfi_1 wss wn con0 ftfi_1 cdif c0 wne con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 con0 ftfi_1 cdif wrex con0 ftfi_1 wss con0 ftfi_1 cdif c0 con0 ftfi_1 ssdif0 necon3bbii con0 word con0 ftfi_1 cdif con0 wss con0 ftfi_1 cdif c0 wne con0 ftfi_1 cdif ftfi_0 cv cin c0 wceq ftfi_0 con0 ftfi_1 cdif wrex ordon con0 ftfi_1 difss ftfi_0 con0 con0 ftfi_1 cdif tz7.5 mp3an12 sylbi nsyl2 anim2i ftfi_1 con0 eqss sylibr $.
$}
$( Transfinite Induction Schema.  If all ordinal numbers less than a given
       number ` x ` have a property (induction hypothesis), then all ordinal
       numbers have the property (conclusion).  Exercise 25 of [Enderton]
       p. 200.  (Contributed by NM, 1-Aug-1994.)  (Revised by Mario Carneiro,
       20-Nov-2016.) $)
${
	$d w y z ph $.
	$d w x y z $.
	itfis_0 $f set z $.
	itfis_1 $f set w $.
	ftfis_0 $f wff ph $.
	ftfis_1 $f set x $.
	ftfis_2 $f set y $.
	etfis_0 $e |- ( x e. On -> ( A. y e. x [ y / x ] ph -> ph ) ) $.
	tfis $p |- ( x e. On -> ph ) $= ftfis_1 cv con0 wcel ftfis_1 cv con0 wcel ftfis_0 ftfis_0 ftfis_1 con0 con0 ftfis_0 ftfis_1 con0 crab con0 ftfis_0 ftfis_1 con0 crab con0 wss itfis_0 cv ftfis_0 ftfis_1 con0 crab wss itfis_0 cv ftfis_0 ftfis_1 con0 crab wcel wi itfis_0 con0 wral ftfis_0 ftfis_1 con0 crab con0 wceq ftfis_0 ftfis_1 con0 ssrab2 itfis_0 cv ftfis_0 ftfis_1 con0 crab wss itfis_0 cv ftfis_0 ftfis_1 con0 crab wcel wi itfis_0 con0 ftfis_2 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_2 ftfis_1 cv wral ftfis_1 cv con0 wcel ftfis_0 wa wi itfis_0 cv ftfis_0 ftfis_1 con0 crab wss itfis_0 cv ftfis_0 ftfis_1 con0 crab wcel wi ftfis_1 itfis_0 cv con0 ftfis_1 itfis_0 cv nfcv itfis_0 cv ftfis_0 ftfis_1 con0 crab wss itfis_0 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_1 ftfis_1 itfis_0 cv ftfis_0 ftfis_1 con0 crab ftfis_1 itfis_0 cv nfcv ftfis_0 ftfis_1 con0 nfrab1 nfss ftfis_1 itfis_0 ftfis_0 ftfis_1 con0 crab ftfis_0 ftfis_1 con0 nfrab1 nfcri nfim ftfis_1 cv itfis_0 cv wceq ftfis_2 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_2 ftfis_1 cv wral itfis_0 cv ftfis_0 ftfis_1 con0 crab wss ftfis_1 cv con0 wcel ftfis_0 wa itfis_0 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_2 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_2 ftfis_1 cv wral ftfis_1 cv ftfis_0 ftfis_1 con0 crab wss ftfis_1 cv itfis_0 cv wceq itfis_0 cv ftfis_0 ftfis_1 con0 crab wss ftfis_2 ftfis_1 cv ftfis_0 ftfis_1 con0 crab dfss3 ftfis_1 cv itfis_0 cv ftfis_0 ftfis_1 con0 crab sseq1 syl5bbr ftfis_1 cv con0 wcel ftfis_0 wa ftfis_1 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_1 cv itfis_0 cv wceq itfis_0 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_0 ftfis_1 con0 rabid ftfis_1 cv itfis_0 cv ftfis_0 ftfis_1 con0 crab eleq1 syl5bbr imbi12d ftfis_1 cv con0 wcel ftfis_2 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_2 ftfis_1 cv wral ftfis_0 ftfis_2 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_2 ftfis_1 cv wral ftfis_0 ftfis_1 ftfis_2 wsb ftfis_2 ftfis_1 cv wral ftfis_1 cv con0 wcel ftfis_0 ftfis_2 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_0 ftfis_1 ftfis_2 wsb ftfis_2 ftfis_1 cv ftfis_2 cv ftfis_0 ftfis_1 con0 crab wcel ftfis_2 cv con0 wcel ftfis_0 ftfis_1 ftfis_2 wsb ftfis_0 ftfis_1 itfis_1 wsb ftfis_0 ftfis_1 ftfis_2 wsb itfis_1 ftfis_2 cv con0 ftfis_0 ftfis_1 con0 crab ftfis_0 itfis_1 ftfis_2 ftfis_1 sbequ ftfis_0 ftfis_0 ftfis_1 itfis_1 wsb ftfis_1 itfis_1 con0 ftfis_1 con0 nfcv itfis_1 con0 nfcv ftfis_0 itfis_1 nfv ftfis_0 ftfis_1 itfis_1 nfs1v ftfis_0 ftfis_1 itfis_1 sbequ12 cbvrab elrab2 simprbi ralimi etfis_0 syl5 anc2li vtoclgaf rgen itfis_0 ftfis_0 ftfis_1 con0 crab tfi mp2an eqcomi rabeq2i simprbi $.
$}
$( Transfinite Induction Schema, using implicit substitution.  (Contributed
       by NM, 18-Aug-1994.) $)
${
	$d y ph $.
	$d x y $.
	ftfis2f_0 $f wff ph $.
	ftfis2f_1 $f wff ps $.
	ftfis2f_2 $f set x $.
	ftfis2f_3 $f set y $.
	etfis2f_0 $e |- F/ x ps $.
	etfis2f_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	etfis2f_2 $e |- ( x e. On -> ( A. y e. x ps -> ph ) ) $.
	tfis2f $p |- ( x e. On -> ph ) $= ftfis2f_0 ftfis2f_2 ftfis2f_3 ftfis2f_0 ftfis2f_2 ftfis2f_3 wsb ftfis2f_3 ftfis2f_2 cv wral ftfis2f_1 ftfis2f_3 ftfis2f_2 cv wral ftfis2f_2 cv con0 wcel ftfis2f_0 ftfis2f_0 ftfis2f_2 ftfis2f_3 wsb ftfis2f_1 ftfis2f_3 ftfis2f_2 cv ftfis2f_0 ftfis2f_1 ftfis2f_2 ftfis2f_3 etfis2f_0 etfis2f_1 sbie ralbii etfis2f_2 syl5bi tfis $.
$}
$( Transfinite Induction Schema, using implicit substitution.  (Contributed
       by NM, 18-Aug-1994.) $)
${
	$d x ps $.
	$d y ph $.
	$d x y $.
	ftfis2_0 $f wff ph $.
	ftfis2_1 $f wff ps $.
	ftfis2_2 $f set x $.
	ftfis2_3 $f set y $.
	etfis2_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	etfis2_1 $e |- ( x e. On -> ( A. y e. x ps -> ph ) ) $.
	tfis2 $p |- ( x e. On -> ph ) $= ftfis2_0 ftfis2_1 ftfis2_2 ftfis2_3 ftfis2_1 ftfis2_2 nfv etfis2_0 etfis2_1 tfis2f $.
$}
$( Transfinite Induction Schema, using implicit substitution.  (Contributed
       by NM, 4-Nov-2003.) $)
${
	$d x ps $.
	$d y ph $.
	$d x ch $.
	$d x A $.
	$d x y $.
	ftfis3_0 $f wff ph $.
	ftfis3_1 $f wff ps $.
	ftfis3_2 $f wff ch $.
	ftfis3_3 $f set x $.
	ftfis3_4 $f set y $.
	ftfis3_5 $f class A $.
	etfis3_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	etfis3_1 $e |- ( x = A -> ( ph <-> ch ) ) $.
	etfis3_2 $e |- ( x e. On -> ( A. y e. x ps -> ph ) ) $.
	tfis3 $p |- ( A e. On -> ch ) $= ftfis3_0 ftfis3_2 ftfis3_3 ftfis3_5 con0 etfis3_1 ftfis3_0 ftfis3_1 ftfis3_3 ftfis3_4 etfis3_0 etfis3_2 tfis2 vtoclga $.
$}
$( A transfinite induction scheme in "implicit" form where the induction is
       done on an object derived from the object of interest.  (Contributed by
       Stefan O'Rear, 24-Aug-2015.) $)
${
	$d x v w y z T $.
	$d v w y z R $.
	$d x v w z S $.
	$d x v w z ch $.
	$d x v w y z ph $.
	$d w y z ps $.
	$d x A $.
	$d x th $.
	itfisi_0 $f set z $.
	itfisi_1 $f set w $.
	itfisi_2 $f set v $.
	ftfisi_0 $f wff ph $.
	ftfisi_1 $f wff ps $.
	ftfisi_2 $f wff ch $.
	ftfisi_3 $f wff th $.
	ftfisi_4 $f set x $.
	ftfisi_5 $f set y $.
	ftfisi_6 $f class A $.
	ftfisi_7 $f class R $.
	ftfisi_8 $f class S $.
	ftfisi_9 $f class T $.
	ftfisi_10 $f class V $.
	etfisi_0 $e |- ( ph -> A e. V ) $.
	etfisi_1 $e |- ( ph -> T e. On ) $.
	etfisi_2 $e |- ( ( ph /\ ( R e. On /\ R C_ T ) /\ A. y ( S e. R -> ch ) ) -> ps ) $.
	etfisi_3 $e |- ( x = y -> ( ps <-> ch ) ) $.
	etfisi_4 $e |- ( x = A -> ( ps <-> th ) ) $.
	etfisi_5 $e |- ( x = y -> R = S ) $.
	etfisi_6 $e |- ( x = A -> R = T ) $.
	tfisi $p |- ( ph -> th ) $= ftfisi_0 ftfisi_9 ftfisi_9 wss ftfisi_3 ftfisi_9 ssid ftfisi_0 ftfisi_9 ftfisi_9 wss ftfisi_3 wi ftfisi_0 ftfisi_0 ftfisi_9 ftfisi_9 wss ftfisi_3 ftfisi_0 ftfisi_9 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_3 wi ftfisi_9 eqid ftfisi_0 ftfisi_6 ftfisi_10 wcel ftfisi_7 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 wal ftfisi_9 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_3 wi wi etfisi_0 ftfisi_0 ftfisi_9 con0 wcel ftfisi_7 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 wal etfisi_1 ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 wal ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal ftfisi_7 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 wal itfisi_0 itfisi_1 ftfisi_9 itfisi_0 cv itfisi_1 cv wceq ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 wal ftfisi_7 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 wal ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_0 cv itfisi_1 cv wceq ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_7 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 itfisi_0 cv itfisi_1 cv wceq ftfisi_7 itfisi_0 cv wceq ftfisi_7 itfisi_1 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 wi ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_1 wi itfisi_0 cv itfisi_1 cv ftfisi_7 eqeq2 itfisi_0 cv itfisi_1 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_1 itfisi_0 cv itfisi_1 cv wceq itfisi_0 cv ftfisi_9 wss itfisi_1 cv ftfisi_9 wss ftfisi_0 itfisi_0 cv itfisi_1 cv ftfisi_9 sseq1 anbi2d imbi1d imbi12d albidv ftfisi_7 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_4 ftfisi_5 ftfisi_4 cv ftfisi_5 cv wceq ftfisi_7 itfisi_1 cv wceq ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_1 wi ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi ftfisi_4 cv ftfisi_5 cv wceq ftfisi_7 ftfisi_8 itfisi_1 cv etfisi_5 eqeq1d ftfisi_4 cv ftfisi_5 cv wceq ftfisi_1 ftfisi_2 ftfisi_0 itfisi_1 cv ftfisi_9 wss wa etfisi_3 imbi2d imbi12d cbvalv syl6bb itfisi_0 cv ftfisi_9 wceq ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_7 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 itfisi_0 cv ftfisi_9 wceq ftfisi_7 itfisi_0 cv wceq ftfisi_7 ftfisi_9 wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 wi ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_1 wi itfisi_0 cv ftfisi_9 ftfisi_7 eqeq2 itfisi_0 cv ftfisi_9 wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_1 itfisi_0 cv ftfisi_9 wceq itfisi_0 cv ftfisi_9 wss ftfisi_9 ftfisi_9 wss ftfisi_0 itfisi_0 cv ftfisi_9 ftfisi_9 sseq1 anbi2d imbi1d imbi12d albidv itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 wal itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_4 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_1 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_0 ftfisi_7 con0 wcel ftfisi_7 ftfisi_9 wss ftfisi_8 ftfisi_7 wcel ftfisi_2 wi ftfisi_5 wal ftfisi_1 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss simp3l itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_7 itfisi_0 cv con0 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa simp2 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa simp1l eqeltrd itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_7 itfisi_0 cv ftfisi_9 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa simp2 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss simp3r eqsstrd itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel ftfisi_1 ftfisi_4 itfisi_2 wsb wi itfisi_2 wal ftfisi_8 ftfisi_7 wcel ftfisi_2 wi ftfisi_5 wal itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel ftfisi_1 ftfisi_4 itfisi_2 wsb wi itfisi_2 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel ftfisi_1 ftfisi_4 itfisi_2 wsb itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel wa ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss ftfisi_1 ftfisi_4 itfisi_2 wsb ftfisi_0 itfisi_0 cv ftfisi_9 wss itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel simpl3l itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel wa ftfisi_4 itfisi_2 cv ftfisi_7 csb itfisi_0 cv ftfisi_9 itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel wa itfisi_0 cv con0 wcel ftfisi_4 itfisi_2 cv ftfisi_7 csb itfisi_0 cv wcel ftfisi_4 itfisi_2 cv ftfisi_7 csb itfisi_0 cv wss itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel simpl1l itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel wa ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 itfisi_0 cv itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel simpr itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel simpl2 eleqtrd itfisi_0 cv ftfisi_4 itfisi_2 cv ftfisi_7 csb onelss sylc ftfisi_0 itfisi_0 cv ftfisi_9 wss itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel simpl3r sstrd itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel wa ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_1 ftfisi_4 itfisi_2 wsb wi itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel wa ftfisi_4 itfisi_2 cv ftfisi_7 csb itfisi_0 cv wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel wa ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 itfisi_0 cv itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel simpr itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel simpl2 eleqtrd itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel simpl1r ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 ftfisi_4 itfisi_2 cv ftfisi_7 csb itfisi_0 cv itfisi_1 cv ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 itfisi_1 cv ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_8 itfisi_1 cv wceq ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 wi itfisi_1 cv ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_8 eqeq2 itfisi_1 cv ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 itfisi_1 cv ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq itfisi_1 cv ftfisi_9 wss ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss ftfisi_0 itfisi_1 cv ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 sseq1 anbi2d imbi1d imbi12d albidv rspcva syl2anc itfisi_0 cv con0 wcel ftfisi_8 itfisi_1 cv wceq ftfisi_0 itfisi_1 cv ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_5 wal itfisi_1 itfisi_0 cv wral wa ftfisi_7 itfisi_0 cv wceq ftfisi_0 itfisi_0 cv ftfisi_9 wss wa w3a ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel wa ftfisi_4 itfisi_2 cv ftfisi_7 csb eqidd ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 wi wi ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_1 ftfisi_4 itfisi_2 wsb wi wi ftfisi_5 itfisi_2 ftfisi_5 cv itfisi_2 cv wceq ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 wi ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_1 ftfisi_4 itfisi_2 wsb wi ftfisi_5 cv itfisi_2 cv wceq ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_8 ftfisi_4 itfisi_2 cv ftfisi_7 csb wceq itfisi_2 cv ftfisi_5 cv itfisi_2 cv ftfisi_5 cv wceq ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_8 ftfisi_4 itfisi_2 ftfisi_5 cv ftfisi_7 ftfisi_8 ftfisi_4 ftfisi_5 cv nfcv ftfisi_4 ftfisi_8 nfcv etfisi_5 csbhypf eqcomd eqcoms eqeq1d ftfisi_5 cv itfisi_2 cv wceq ftfisi_2 ftfisi_1 ftfisi_4 itfisi_2 wsb ftfisi_0 ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_9 wss wa ftfisi_2 ftfisi_1 ftfisi_4 itfisi_2 wsb wb itfisi_2 cv ftfisi_5 cv itfisi_2 cv ftfisi_5 cv wceq ftfisi_1 ftfisi_4 itfisi_2 wsb ftfisi_2 itfisi_2 cv ftfisi_5 cv wceq ftfisi_1 ftfisi_4 itfisi_2 wsb ftfisi_1 ftfisi_4 ftfisi_5 wsb ftfisi_2 ftfisi_1 itfisi_2 ftfisi_5 ftfisi_4 sbequ ftfisi_1 ftfisi_2 ftfisi_4 ftfisi_5 ftfisi_2 ftfisi_4 nfv etfisi_3 sbie syl6bb bicomd eqcoms imbi2d imbi12d spv sylc mp2and ex alrimiv ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel ftfisi_1 ftfisi_4 itfisi_2 wsb wi ftfisi_8 ftfisi_7 wcel ftfisi_2 wi itfisi_2 ftfisi_5 itfisi_2 cv ftfisi_5 cv wceq ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_7 wcel ftfisi_8 ftfisi_7 wcel ftfisi_1 ftfisi_4 itfisi_2 wsb ftfisi_2 itfisi_2 cv ftfisi_5 cv wceq ftfisi_4 itfisi_2 cv ftfisi_7 csb ftfisi_8 ftfisi_7 ftfisi_4 itfisi_2 ftfisi_5 cv ftfisi_7 ftfisi_8 ftfisi_4 ftfisi_5 cv nfcv ftfisi_4 ftfisi_8 nfcv etfisi_5 csbhypf eleq1d itfisi_2 cv ftfisi_5 cv wceq ftfisi_1 ftfisi_4 itfisi_2 wsb ftfisi_1 ftfisi_4 ftfisi_5 wsb ftfisi_2 ftfisi_1 itfisi_2 ftfisi_5 ftfisi_4 sbequ ftfisi_1 ftfisi_2 ftfisi_4 ftfisi_5 ftfisi_2 ftfisi_4 nfv etfisi_3 sbie syl6bb imbi12d cbvalv sylib etfisi_2 syl121anc 3exp alrimiv ex tfis3 syl ftfisi_7 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_1 wi wi ftfisi_9 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_3 wi wi ftfisi_4 ftfisi_6 ftfisi_10 ftfisi_4 cv ftfisi_6 wceq ftfisi_7 ftfisi_9 wceq ftfisi_9 ftfisi_9 wceq ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_1 wi ftfisi_0 ftfisi_9 ftfisi_9 wss wa ftfisi_3 wi ftfisi_4 cv ftfisi_6 wceq ftfisi_7 ftfisi_9 ftfisi_9 etfisi_6 eqeq1d ftfisi_4 cv ftfisi_6 wceq ftfisi_1 ftfisi_3 ftfisi_0 ftfisi_9 ftfisi_9 wss wa etfisi_4 imbi2d imbi12d spcgv sylc mpi exp3a pm2.43i mpi $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis for successors. $)
$( Induction hypothesis for limit ordinals. $)
$( Principle of Transfinite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last three are the basis, the induction hypothesis for
       successors, and the induction hypothesis for limit ordinals.  Theorem
       Schema 4 of [Suppes] p. 197.  (Contributed by NM, 16-Apr-1995.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z $.
	$d x A $.
	$d x z ch $.
	$d x ta $.
	$d y z ph $.
	itfinds_0 $f set z $.
	ftfinds_0 $f wff ph $.
	ftfinds_1 $f wff ps $.
	ftfinds_2 $f wff ch $.
	ftfinds_3 $f wff th $.
	ftfinds_4 $f wff ta $.
	ftfinds_5 $f set x $.
	ftfinds_6 $f set y $.
	ftfinds_7 $f class A $.
	etfinds_0 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	etfinds_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	etfinds_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	etfinds_3 $e |- ( x = A -> ( ph <-> ta ) ) $.
	etfinds_4 $e |- ps $.
	etfinds_5 $e |- ( y e. On -> ( ch -> th ) ) $.
	etfinds_6 $e |- ( Lim x -> ( A. y e. x ch -> ph ) ) $.
	tfinds $p |- ( A e. On -> ta ) $= ftfinds_0 ftfinds_2 ftfinds_4 ftfinds_5 ftfinds_6 ftfinds_7 etfinds_1 etfinds_3 ftfinds_5 cv con0 wcel ftfinds_5 cv wlim ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 wi ftfinds_5 cv wlim wn ftfinds_5 cv word ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo wn wa wn ftfinds_5 cv con0 wcel ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 wi ftfinds_5 cv wlim ftfinds_5 cv word ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo wn wa ftfinds_6 ftfinds_5 cv dflim3 notbii ftfinds_5 cv word ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo wn wa wn ftfinds_5 cv word ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo wi ftfinds_5 cv con0 wcel ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 wi ftfinds_5 cv word ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo iman ftfinds_5 cv con0 wcel ftfinds_5 cv word ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo wi ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 wi ftfinds_5 cv con0 wcel ftfinds_5 cv word ftfinds_5 cv word ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo wi ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo wi ftfinds_5 cv eloni ftfinds_5 cv word ftfinds_5 cv c0 wceq ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex wo pm2.27 syl ftfinds_5 cv c0 wceq ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 wi ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_6 con0 wrex ftfinds_5 cv c0 wceq ftfinds_0 ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_5 cv c0 wceq ftfinds_0 ftfinds_1 etfinds_4 etfinds_0 mpbiri a1d ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 wi ftfinds_6 con0 ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 ftfinds_6 ftfinds_2 ftfinds_6 ftfinds_5 cv nfra1 ftfinds_0 ftfinds_6 nfv nfim ftfinds_6 cv con0 wcel ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_3 ftfinds_0 ftfinds_6 cv con0 wcel ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_3 wi ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_0 ftfinds_5 ftfinds_6 cv csuc wral ftfinds_3 wi ftfinds_0 ftfinds_5 ftfinds_6 cv csuc wral ftfinds_2 ftfinds_6 cv con0 wcel ftfinds_3 ftfinds_6 cv ftfinds_6 cv csuc wcel ftfinds_0 ftfinds_5 ftfinds_6 cv csuc wral ftfinds_2 wi ftfinds_6 cv ftfinds_6 vex sucid ftfinds_0 ftfinds_2 ftfinds_5 ftfinds_6 cv ftfinds_6 cv csuc etfinds_1 rspcv ax-mp etfinds_5 syl5 ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 ftfinds_5 ftfinds_6 cv csuc wral ftfinds_3 ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_0 ftfinds_5 itfinds_0 wsb itfinds_0 ftfinds_5 cv wral ftfinds_0 ftfinds_5 itfinds_0 wsb itfinds_0 ftfinds_6 cv csuc wral ftfinds_2 ftfinds_6 ftfinds_5 cv wral ftfinds_0 ftfinds_5 ftfinds_6 cv csuc wral ftfinds_0 ftfinds_5 itfinds_0 wsb itfinds_0 ftfinds_5 cv ftfinds_6 cv csuc raleq ftfinds_2 ftfinds_0 ftfinds_5 itfinds_0 wsb ftfinds_6 itfinds_0 ftfinds_5 cv ftfinds_2 ftfinds_0 ftfinds_5 ftfinds_6 wsb ftfinds_6 cv itfinds_0 cv wceq ftfinds_0 ftfinds_5 itfinds_0 wsb ftfinds_0 ftfinds_2 ftfinds_5 ftfinds_6 ftfinds_2 ftfinds_5 nfv etfinds_1 sbie ftfinds_0 ftfinds_6 itfinds_0 ftfinds_5 sbequ syl5bbr cbvralv ftfinds_0 ftfinds_5 itfinds_0 ftfinds_6 cv csuc cbvralsv 3bitr4g imbi1d syl5ibrcom ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_3 ftfinds_0 wi wi ftfinds_6 cv con0 wcel ftfinds_5 cv ftfinds_6 cv csuc wceq ftfinds_0 ftfinds_3 etfinds_2 biimprd a1i syldd rexlimi jaoi syl6 syl5bir syl5bi etfinds_6 pm2.61d2 tfis3 $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis for successor ordinals. $)
$( Induction hypothesis for limit ordinals. $)
$( Transfinite Induction (inference schema), using implicit substitutions.
       The first four hypotheses establish the substitutions we need.  The last
       three are the basis, the induction hypothesis for successors, and the
       induction hypothesis for limit ordinals.  The basis of this version is
       an arbitrary ordinal ` B ` instead of zero.  Remark in [TakeutiZaring]
       p. 57.  (Contributed by NM, 5-Mar-2004.) $)
${
	$d x A $.
	$d x y B $.
	$d x ch $.
	$d x th $.
	$d x ta $.
	$d y ph $.
	ftfindsg_0 $f wff ph $.
	ftfindsg_1 $f wff ps $.
	ftfindsg_2 $f wff ch $.
	ftfindsg_3 $f wff th $.
	ftfindsg_4 $f wff ta $.
	ftfindsg_5 $f set x $.
	ftfindsg_6 $f set y $.
	ftfindsg_7 $f class A $.
	ftfindsg_8 $f class B $.
	etfindsg_0 $e |- ( x = B -> ( ph <-> ps ) ) $.
	etfindsg_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	etfindsg_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	etfindsg_3 $e |- ( x = A -> ( ph <-> ta ) ) $.
	etfindsg_4 $e |- ( B e. On -> ps ) $.
	etfindsg_5 $e |- ( ( ( y e. On /\ B e. On ) /\ B C_ y ) -> ( ch -> th ) ) $.
	etfindsg_6 $e |- ( ( ( Lim x /\ B e. On ) /\ B C_ x ) -> ( A. y e. x ( B C_ y -> ch ) -> ph ) ) $.
	tfindsg $p |- ( ( ( A e. On /\ B e. On ) /\ B C_ A ) -> ta ) $= ftfindsg_7 con0 wcel ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_7 wss ftfindsg_4 ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_5 cv wss ftfindsg_0 wi wi ftfindsg_8 con0 wcel ftfindsg_8 c0 wss ftfindsg_1 wi wi ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi wi ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi wi ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_7 wss ftfindsg_4 wi wi ftfindsg_5 ftfindsg_6 ftfindsg_7 ftfindsg_5 cv c0 wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_0 wi ftfindsg_8 c0 wss ftfindsg_1 wi ftfindsg_8 con0 wcel ftfindsg_8 c0 wceq ftfindsg_5 cv c0 wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_0 wi ftfindsg_8 c0 wss ftfindsg_1 wi wb ftfindsg_8 c0 wceq ftfindsg_5 cv c0 wceq wa ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 c0 wss ftfindsg_0 ftfindsg_1 ftfindsg_5 cv c0 wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 c0 wss wb ftfindsg_8 c0 wceq ftfindsg_5 cv c0 ftfindsg_8 sseq2 adantl ftfindsg_8 c0 wceq ftfindsg_5 cv c0 wceq ftfindsg_0 ftfindsg_1 wb ftfindsg_8 c0 wceq ftfindsg_5 cv c0 wceq ftfindsg_5 cv ftfindsg_8 wceq ftfindsg_0 ftfindsg_1 wb ftfindsg_8 c0 ftfindsg_5 cv eqeq2 etfindsg_0 syl6bir imp imbi12d ftfindsg_5 cv c0 wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_0 wi ftfindsg_8 c0 wss ftfindsg_0 wi ftfindsg_8 c0 wceq wn ftfindsg_8 c0 wss ftfindsg_1 wi ftfindsg_5 cv c0 wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 c0 wss ftfindsg_0 ftfindsg_5 cv c0 ftfindsg_8 sseq2 imbi1d ftfindsg_8 c0 wceq wn ftfindsg_8 c0 wss ftfindsg_0 ftfindsg_1 ftfindsg_8 c0 wceq wn ftfindsg_8 c0 wss ftfindsg_0 ftfindsg_1 wb ftfindsg_8 c0 wss ftfindsg_8 c0 wceq ftfindsg_8 ss0 con3i pm2.21d pm5.74d sylan9bbr pm2.61ian imbi2d ftfindsg_5 cv ftfindsg_6 cv wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_0 wi ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 con0 wcel ftfindsg_5 cv ftfindsg_6 cv wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 ftfindsg_6 cv wss ftfindsg_0 ftfindsg_2 ftfindsg_5 cv ftfindsg_6 cv ftfindsg_8 sseq2 etfindsg_1 imbi12d imbi2d ftfindsg_5 cv ftfindsg_6 cv csuc wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_0 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi ftfindsg_8 con0 wcel ftfindsg_5 cv ftfindsg_6 cv csuc wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_0 ftfindsg_3 ftfindsg_5 cv ftfindsg_6 cv csuc ftfindsg_8 sseq2 etfindsg_2 imbi12d imbi2d ftfindsg_5 cv ftfindsg_7 wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_0 wi ftfindsg_8 ftfindsg_7 wss ftfindsg_4 wi ftfindsg_8 con0 wcel ftfindsg_5 cv ftfindsg_7 wceq ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 ftfindsg_7 wss ftfindsg_0 ftfindsg_4 ftfindsg_5 cv ftfindsg_7 ftfindsg_8 sseq2 etfindsg_3 imbi12d imbi2d ftfindsg_8 con0 wcel ftfindsg_1 ftfindsg_8 c0 wss etfindsg_4 a1d ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi wi ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel wa ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wceq wi ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi wi ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wceq wi ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi wi wi ftfindsg_6 cv con0 wcel ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wceq wi ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 con0 wcel ftfindsg_3 ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wceq wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 con0 wcel ftfindsg_3 wi wi ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv csuc wceq ftfindsg_8 con0 wcel ftfindsg_3 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 con0 wcel ftfindsg_3 wi ftfindsg_6 cv csuc ftfindsg_8 ftfindsg_6 cv csuc ftfindsg_8 wceq ftfindsg_5 cv ftfindsg_6 cv csuc wceq ftfindsg_5 cv ftfindsg_8 wceq wa ftfindsg_5 wex ftfindsg_8 con0 wcel ftfindsg_3 wi ftfindsg_5 ftfindsg_6 cv csuc ftfindsg_8 ftfindsg_6 cv ftfindsg_6 vex sucex eqvinc ftfindsg_5 cv ftfindsg_6 cv csuc wceq ftfindsg_5 cv ftfindsg_8 wceq wa ftfindsg_8 con0 wcel ftfindsg_3 wi ftfindsg_5 ftfindsg_5 cv ftfindsg_8 wceq ftfindsg_8 con0 wcel ftfindsg_0 ftfindsg_5 cv ftfindsg_6 cv csuc wceq ftfindsg_3 ftfindsg_8 con0 wcel ftfindsg_0 ftfindsg_5 cv ftfindsg_8 wceq ftfindsg_1 etfindsg_4 etfindsg_0 syl5ibr ftfindsg_5 cv ftfindsg_6 cv csuc wceq ftfindsg_0 ftfindsg_3 etfindsg_2 biimpd sylan9r exlimiv sylbi eqcoms imim2i a1d com4r adantl ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wceq wi wn ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wne wa ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel wa ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wne wa ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wceq wn wa ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wceq wi wn ftfindsg_8 ftfindsg_6 cv csuc wne ftfindsg_8 ftfindsg_6 cv csuc wceq wn ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc df-ne anbi2i ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wceq annim bitri ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel wa ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wne wa ftfindsg_8 ftfindsg_6 cv wss ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi wi ftfindsg_8 con0 wcel ftfindsg_6 cv con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wne wa wb ftfindsg_8 con0 wcel ftfindsg_6 cv con0 wcel wa ftfindsg_8 ftfindsg_6 cv wss ftfindsg_8 ftfindsg_6 cv csuc wcel ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wne wa ftfindsg_8 ftfindsg_6 cv onsssuc ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel ftfindsg_6 cv csuc con0 wcel ftfindsg_8 ftfindsg_6 cv csuc wcel ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_8 ftfindsg_6 cv csuc wne wa wb ftfindsg_6 cv suceloni ftfindsg_8 ftfindsg_6 cv csuc onelpss sylan2 bitrd ancoms ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel wa ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_8 ftfindsg_6 cv wss ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel wa ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel wa ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 ftfindsg_3 ftfindsg_8 ftfindsg_6 cv csuc wss ftfindsg_3 wi ftfindsg_6 cv con0 wcel ftfindsg_8 con0 wcel wa ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 ftfindsg_3 wi etfindsg_5 ex ftfindsg_3 ftfindsg_8 ftfindsg_6 cv csuc wss ax-1 syl8 a2d com23 sylbird syl5bir pm2.61d ex a2d ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_5 cv wss ftfindsg_5 cv wlim ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi wi ftfindsg_6 ftfindsg_5 cv wral ftfindsg_0 ftfindsg_5 cv wlim ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi wi ftfindsg_6 ftfindsg_5 cv wral ftfindsg_0 wi ftfindsg_5 cv wlim ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi wi ftfindsg_6 ftfindsg_5 cv wral ftfindsg_0 wi ftfindsg_5 cv wlim ftfindsg_8 con0 wcel wa ftfindsg_8 ftfindsg_5 cv wss wa ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi wi ftfindsg_6 ftfindsg_5 cv wral ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_6 ftfindsg_5 cv wral ftfindsg_0 ftfindsg_8 con0 wcel ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi wi ftfindsg_6 ftfindsg_5 cv wral ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_6 ftfindsg_5 cv wral wi ftfindsg_5 cv wlim ftfindsg_8 ftfindsg_5 cv wss ftfindsg_8 con0 wcel ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi wi ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi ftfindsg_6 ftfindsg_5 cv ftfindsg_8 con0 wcel ftfindsg_8 ftfindsg_6 cv wss ftfindsg_2 wi pm2.27 ralimdv ad2antlr etfindsg_6 syld exp31 com3l com4t tfinds imp31 $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis for successor ordinals. $)
$( Induction hypothesis for limit ordinals. $)
$( Transfinite Induction (inference schema), using implicit substitutions.
       The first four hypotheses establish the substitutions we need.  The last
       three are the basis, the induction hypothesis for successors, and the
       induction hypothesis for limit ordinals.  The basis of this version is
       an arbitrary ordinal ` suc B ` instead of zero.  (Unnecessary distinct
       variable restrictions were removed by David Abernethy, 19-Jun-2012.)
       (Contributed by NM, 5-Jan-2005.) $)
${
	$d x A $.
	$d x y B $.
	$d x ch $.
	$d x th $.
	$d x ta $.
	$d y ph $.
	ftfindsg2_0 $f wff ph $.
	ftfindsg2_1 $f wff ps $.
	ftfindsg2_2 $f wff ch $.
	ftfindsg2_3 $f wff th $.
	ftfindsg2_4 $f wff ta $.
	ftfindsg2_5 $f set x $.
	ftfindsg2_6 $f set y $.
	ftfindsg2_7 $f class A $.
	ftfindsg2_8 $f class B $.
	etfindsg2_0 $e |- ( x = suc B -> ( ph <-> ps ) ) $.
	etfindsg2_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	etfindsg2_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	etfindsg2_3 $e |- ( x = A -> ( ph <-> ta ) ) $.
	etfindsg2_4 $e |- ( B e. On -> ps ) $.
	etfindsg2_5 $e |- ( ( y e. On /\ B e. y ) -> ( ch -> th ) ) $.
	etfindsg2_6 $e |- ( ( Lim x /\ B e. x ) -> ( A. y e. x ( B e. y -> ch ) -> ph ) ) $.
	tfindsg2 $p |- ( ( A e. On /\ B e. A ) -> ta ) $= ftfindsg2_7 con0 wcel ftfindsg2_8 ftfindsg2_7 wcel wa ftfindsg2_8 csuc con0 wcel ftfindsg2_8 csuc ftfindsg2_7 wss ftfindsg2_4 ftfindsg2_7 con0 wcel ftfindsg2_8 ftfindsg2_7 wcel wa ftfindsg2_8 con0 wcel ftfindsg2_8 csuc con0 wcel ftfindsg2_7 ftfindsg2_8 onelon ftfindsg2_8 sucelon sylib ftfindsg2_7 con0 wcel ftfindsg2_8 ftfindsg2_7 wcel ftfindsg2_8 csuc ftfindsg2_7 wss ftfindsg2_7 con0 wcel ftfindsg2_7 word ftfindsg2_8 ftfindsg2_7 wcel ftfindsg2_8 csuc ftfindsg2_7 wss wi ftfindsg2_7 eloni ftfindsg2_8 ftfindsg2_7 ordsucss syl imp ftfindsg2_7 con0 wcel ftfindsg2_8 csuc con0 wcel ftfindsg2_8 csuc ftfindsg2_7 wss wa ftfindsg2_4 wi ftfindsg2_8 ftfindsg2_7 wcel ftfindsg2_7 con0 wcel ftfindsg2_8 csuc con0 wcel ftfindsg2_8 csuc ftfindsg2_7 wss ftfindsg2_4 ftfindsg2_0 ftfindsg2_1 ftfindsg2_2 ftfindsg2_3 ftfindsg2_4 ftfindsg2_5 ftfindsg2_6 ftfindsg2_7 ftfindsg2_8 csuc etfindsg2_0 etfindsg2_1 etfindsg2_2 etfindsg2_3 ftfindsg2_8 csuc con0 wcel ftfindsg2_8 con0 wcel ftfindsg2_1 ftfindsg2_8 sucelon etfindsg2_4 sylbir ftfindsg2_6 cv con0 wcel ftfindsg2_8 csuc con0 wcel wa ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 ftfindsg2_3 wi ftfindsg2_8 csuc con0 wcel ftfindsg2_6 cv con0 wcel ftfindsg2_8 con0 wcel ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 ftfindsg2_3 wi wi ftfindsg2_8 sucelon ftfindsg2_6 cv con0 wcel ftfindsg2_8 con0 wcel wa ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 ftfindsg2_3 wi ftfindsg2_8 con0 wcel ftfindsg2_6 cv con0 wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_8 csuc ftfindsg2_6 cv wss wb ftfindsg2_6 cv con0 wcel ftfindsg2_8 con0 wcel ftfindsg2_6 cv word ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_8 csuc ftfindsg2_6 cv wss wb ftfindsg2_6 cv eloni ftfindsg2_8 ftfindsg2_6 cv con0 ordelsuc sylan2 ancoms ftfindsg2_6 cv con0 wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 ftfindsg2_3 wi wi ftfindsg2_8 con0 wcel ftfindsg2_6 cv con0 wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 ftfindsg2_3 wi etfindsg2_5 ex adantr sylbird sylan2br imp ftfindsg2_5 cv wlim ftfindsg2_8 csuc con0 wcel wa ftfindsg2_8 csuc ftfindsg2_5 cv wss ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi ftfindsg2_8 csuc con0 wcel ftfindsg2_5 cv wlim ftfindsg2_8 con0 wcel ftfindsg2_8 csuc ftfindsg2_5 cv wss ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi wi ftfindsg2_8 sucelon ftfindsg2_5 cv wlim ftfindsg2_8 con0 wcel wa ftfindsg2_8 ftfindsg2_5 cv wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi wi ftfindsg2_8 csuc ftfindsg2_5 cv wss ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi wi ftfindsg2_5 cv wlim ftfindsg2_8 ftfindsg2_5 cv wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi wi ftfindsg2_8 con0 wcel ftfindsg2_5 cv wlim ftfindsg2_8 ftfindsg2_5 cv wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi etfindsg2_6 ex adantr ftfindsg2_8 con0 wcel ftfindsg2_5 cv wlim ftfindsg2_8 ftfindsg2_5 cv wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi wi ftfindsg2_8 csuc ftfindsg2_5 cv wss ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi wi wb ftfindsg2_5 cv wlim ftfindsg2_8 con0 wcel ftfindsg2_5 cv con0 wcel ftfindsg2_8 ftfindsg2_5 cv wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi wi ftfindsg2_8 csuc ftfindsg2_5 cv wss ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi wi wb ftfindsg2_5 cv cvv wcel ftfindsg2_5 cv wlim ftfindsg2_5 cv con0 wcel ftfindsg2_5 vex ftfindsg2_5 cv cvv limelon mpan ftfindsg2_8 con0 wcel ftfindsg2_5 cv con0 wcel wa ftfindsg2_8 ftfindsg2_5 cv wcel ftfindsg2_8 csuc ftfindsg2_5 cv wss ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 wi ftfindsg2_5 cv con0 wcel ftfindsg2_8 con0 wcel ftfindsg2_5 cv word ftfindsg2_8 ftfindsg2_5 cv wcel ftfindsg2_8 csuc ftfindsg2_5 cv wss wb ftfindsg2_5 cv eloni ftfindsg2_8 ftfindsg2_5 cv con0 ordelsuc sylan2 ftfindsg2_8 con0 wcel ftfindsg2_5 cv con0 wcel wa ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv wral ftfindsg2_0 ftfindsg2_8 con0 wcel ftfindsg2_5 cv con0 wcel wa ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_2 wi ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 wi ftfindsg2_6 ftfindsg2_5 cv ftfindsg2_8 con0 wcel ftfindsg2_5 cv con0 wcel wa ftfindsg2_6 cv ftfindsg2_5 cv wcel wa ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_8 csuc ftfindsg2_6 cv wss ftfindsg2_2 ftfindsg2_8 con0 wcel ftfindsg2_5 cv con0 wcel ftfindsg2_6 cv ftfindsg2_5 cv wcel ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_8 csuc ftfindsg2_6 cv wss wb ftfindsg2_5 cv con0 wcel ftfindsg2_6 cv ftfindsg2_5 cv wcel wa ftfindsg2_8 con0 wcel ftfindsg2_6 cv word ftfindsg2_8 ftfindsg2_6 cv wcel ftfindsg2_8 csuc ftfindsg2_6 cv wss wb ftfindsg2_5 cv con0 wcel ftfindsg2_6 cv ftfindsg2_5 cv wcel wa ftfindsg2_6 cv con0 wcel ftfindsg2_6 cv word ftfindsg2_5 cv ftfindsg2_6 cv onelon ftfindsg2_6 cv eloni syl ftfindsg2_8 ftfindsg2_6 cv con0 ordelsuc sylan2 anassrs imbi1d ralbidva imbi1d imbi12d sylan2 ancoms mpbid sylan2br imp tfindsg expl adantr mp2and $.
$}
$( Transfinite Induction with explicit substitution.  The first hypothesis
       is the basis, the second is the induction hypothesis for successors, and
       the third is the induction hypothesis for limit ordinals.  Theorem
       Schema 4 of [Suppes] p. 197.  (Contributed by NM, 5-Mar-2004.) $)
${
	$d x y z $.
	$d y z ph $.
	itfindes_0 $f set z $.
	ftfindes_0 $f wff ph $.
	ftfindes_1 $f set x $.
	ftfindes_2 $f set y $.
	etfindes_0 $e |- [. (/) / x ]. ph $.
	etfindes_1 $e |- ( x e. On -> ( ph -> [. suc x / x ]. ph ) ) $.
	etfindes_2 $e |- ( Lim y -> ( A. x e. y ph -> [. y / x ]. ph ) ) $.
	tfindes $p |- ( x e. On -> ph ) $= ftfindes_0 ftfindes_1 ftfindes_2 cv wsbc ftfindes_0 ftfindes_1 c0 wsbc ftfindes_0 ftfindes_1 itfindes_0 cv wsbc ftfindes_0 ftfindes_1 itfindes_0 cv csuc wsbc ftfindes_0 ftfindes_2 itfindes_0 ftfindes_1 cv ftfindes_0 ftfindes_1 ftfindes_2 cv c0 dfsbcq ftfindes_0 ftfindes_1 ftfindes_2 cv itfindes_0 cv dfsbcq ftfindes_0 ftfindes_1 ftfindes_2 cv itfindes_0 cv csuc dfsbcq ftfindes_0 ftfindes_1 ftfindes_2 cv sbceq2a etfindes_0 ftfindes_1 cv con0 wcel ftfindes_0 ftfindes_0 ftfindes_1 ftfindes_1 cv csuc wsbc wi wi itfindes_0 cv con0 wcel ftfindes_0 ftfindes_1 itfindes_0 cv wsbc ftfindes_0 ftfindes_1 itfindes_0 cv csuc wsbc wi wi ftfindes_1 itfindes_0 itfindes_0 cv con0 wcel ftfindes_0 ftfindes_1 itfindes_0 cv wsbc ftfindes_0 ftfindes_1 itfindes_0 cv csuc wsbc wi ftfindes_1 itfindes_0 cv con0 wcel ftfindes_1 nfv ftfindes_0 ftfindes_1 itfindes_0 cv wsbc ftfindes_0 ftfindes_1 itfindes_0 cv csuc wsbc ftfindes_1 ftfindes_0 ftfindes_1 itfindes_0 cv nfsbc1v ftfindes_0 ftfindes_1 itfindes_0 cv csuc nfsbc1v nfim nfim ftfindes_1 itfindes_0 weq ftfindes_1 cv con0 wcel itfindes_0 cv con0 wcel ftfindes_0 ftfindes_0 ftfindes_1 ftfindes_1 cv csuc wsbc wi ftfindes_0 ftfindes_1 itfindes_0 cv wsbc ftfindes_0 ftfindes_1 itfindes_0 cv csuc wsbc wi ftfindes_1 cv itfindes_0 cv con0 eleq1 ftfindes_1 itfindes_0 weq ftfindes_0 ftfindes_0 ftfindes_1 itfindes_0 cv wsbc ftfindes_0 ftfindes_1 ftfindes_1 cv csuc wsbc ftfindes_0 ftfindes_1 itfindes_0 cv csuc wsbc ftfindes_0 ftfindes_1 itfindes_0 cv sbceq1a ftfindes_1 itfindes_0 weq ftfindes_1 cv csuc itfindes_0 cv csuc wceq ftfindes_0 ftfindes_1 ftfindes_1 cv csuc wsbc ftfindes_0 ftfindes_1 itfindes_0 cv csuc wsbc wb ftfindes_1 cv itfindes_0 cv suceq ftfindes_0 ftfindes_1 ftfindes_1 cv csuc itfindes_0 cv csuc dfsbcq syl imbi12d imbi12d etfindes_1 chvar ftfindes_0 ftfindes_1 itfindes_0 cv wsbc itfindes_0 ftfindes_2 cv wral ftfindes_0 ftfindes_1 ftfindes_2 cv wral ftfindes_2 cv wlim ftfindes_0 ftfindes_1 ftfindes_2 cv wsbc ftfindes_0 ftfindes_1 ftfindes_2 cv wral ftfindes_0 ftfindes_1 itfindes_0 wsb itfindes_0 ftfindes_2 cv wral ftfindes_0 ftfindes_1 itfindes_0 cv wsbc itfindes_0 ftfindes_2 cv wral ftfindes_0 ftfindes_1 itfindes_0 ftfindes_2 cv cbvralsv ftfindes_0 ftfindes_1 itfindes_0 wsb ftfindes_0 ftfindes_1 itfindes_0 cv wsbc itfindes_0 ftfindes_2 cv ftfindes_0 ftfindes_1 itfindes_0 sbsbc ralbii bitri etfindes_2 syl5bir tfinds $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis for successors. $)
$( Induction hypothesis for limit ordinals. $)
$( Transfinite Induction (inference schema), using implicit substitutions.
       The first three hypotheses establish the substitutions we need.  The
       last three are the basis and the induction hypotheses (for successor and
       limit ordinals respectively).  Theorem Schema 4 of [Suppes] p. 197.  The
       wff ` ta ` is an auxiliary antecedent to help shorten proofs using this
       theorem.  (Contributed by NM, 4-Sep-2004.) $)
${
	$d x y ta $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	$d y ph $.
	ftfinds2_0 $f wff ph $.
	ftfinds2_1 $f wff ps $.
	ftfinds2_2 $f wff ch $.
	ftfinds2_3 $f wff th $.
	ftfinds2_4 $f wff ta $.
	ftfinds2_5 $f set x $.
	ftfinds2_6 $f set y $.
	etfinds2_0 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	etfinds2_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	etfinds2_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	etfinds2_3 $e |- ( ta -> ps ) $.
	etfinds2_4 $e |- ( y e. On -> ( ta -> ( ch -> th ) ) ) $.
	etfinds2_5 $e |- ( Lim x -> ( ta -> ( A. y e. x ch -> ph ) ) ) $.
	tfinds2 $p |- ( x e. On -> ( ta -> ph ) ) $= ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 ftfinds2_4 ftfinds2_0 wi ftfinds2_5 c0 wsbc ftfinds2_4 ftfinds2_1 wi etfinds2_3 ftfinds2_4 ftfinds2_0 wi ftfinds2_4 ftfinds2_1 wi ftfinds2_5 c0 0ex ftfinds2_5 cv c0 wceq ftfinds2_0 ftfinds2_1 ftfinds2_4 etfinds2_0 imbi2d sbcie mpbir ftfinds2_5 cv con0 wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_3 wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_0 wi ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_5 cv csuc wsbc ftfinds2_6 cv con0 wcel ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_5 cv con0 wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_3 wi ftfinds2_6 ftfinds2_5 cv wsbc wi ftfinds2_6 cv con0 wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_6 cv con0 wcel ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi ftfinds2_6 ftfinds2_5 cv wsbc wi ftfinds2_5 cv cvv wcel ftfinds2_6 cv con0 wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_5 vex ftfinds2_6 cv con0 wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi wi ftfinds2_6 ftfinds2_5 cv cvv ftfinds2_6 cv con0 wcel ftfinds2_4 ftfinds2_2 ftfinds2_3 etfinds2_4 a2d sbcth ax-mp ftfinds2_5 cv cvv wcel ftfinds2_6 cv con0 wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_6 cv con0 wcel ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi ftfinds2_6 ftfinds2_5 cv wsbc wi wb ftfinds2_5 vex ftfinds2_6 cv con0 wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi ftfinds2_6 ftfinds2_5 cv cvv sbcimg ax-mp mpbi ftfinds2_5 cv cvv wcel ftfinds2_6 cv con0 wcel ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_5 cv con0 wcel wb ftfinds2_5 vex ftfinds2_6 ftfinds2_5 cv con0 cvv sbcel1gv ax-mp ftfinds2_5 cv cvv wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_3 wi ftfinds2_6 ftfinds2_5 cv wsbc wi wb ftfinds2_5 vex ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_3 wi ftfinds2_6 ftfinds2_5 cv cvv sbcimg ax-mp 3imtr3i ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_0 wi ftfinds2_6 ftfinds2_5 cv ftfinds2_5 vex ftfinds2_6 ftfinds2_5 weq ftfinds2_2 ftfinds2_0 ftfinds2_4 ftfinds2_2 ftfinds2_0 wb ftfinds2_5 ftfinds2_6 ftfinds2_5 ftfinds2_6 weq ftfinds2_0 ftfinds2_2 etfinds2_1 bicomd equcoms imbi2d sbcie ftfinds2_4 ftfinds2_3 wi ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 cv csuc wsbc ftfinds2_6 ftfinds2_5 cv wsbc ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_5 cv csuc wsbc ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 cv csuc wsbc ftfinds2_4 ftfinds2_3 wi ftfinds2_6 ftfinds2_5 cv ftfinds2_4 ftfinds2_0 wi ftfinds2_4 ftfinds2_3 wi ftfinds2_5 ftfinds2_6 cv csuc ftfinds2_6 cv ftfinds2_6 vex sucex ftfinds2_5 cv ftfinds2_6 cv csuc wceq ftfinds2_0 ftfinds2_3 ftfinds2_4 etfinds2_2 imbi2d sbcie sbcbii ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 ftfinds2_5 cv csuc ftfinds2_6 cv csuc ftfinds2_5 cv ftfinds2_6 cv suceq sbcco2 bitr3i 3imtr3g ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 cv wral ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_6 cv wlim ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_5 ftfinds2_6 wsb ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 cv wral ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_5 ftfinds2_6 sbsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_4 ftfinds2_0 wi ftfinds2_6 ftfinds2_5 ftfinds2_6 ftfinds2_5 weq ftfinds2_2 ftfinds2_0 ftfinds2_4 ftfinds2_2 ftfinds2_0 wb ftfinds2_5 ftfinds2_6 ftfinds2_5 ftfinds2_6 weq ftfinds2_0 ftfinds2_2 etfinds2_1 bicomd equcoms imbi2d sbralie bitr3i ftfinds2_5 cv wlim ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_6 cv wlim ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 cv wsbc wi ftfinds2_5 cv wlim ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi wi ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_5 cv wlim ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi ftfinds2_5 ftfinds2_6 cv wsbc wi ftfinds2_6 cv cvv wcel ftfinds2_5 cv wlim ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi wi ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_6 vex ftfinds2_5 cv wlim ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi wi ftfinds2_5 ftfinds2_6 cv cvv ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_2 ftfinds2_6 ftfinds2_5 cv wral wi ftfinds2_5 cv wlim ftfinds2_4 ftfinds2_0 wi ftfinds2_4 ftfinds2_2 ftfinds2_6 ftfinds2_5 cv r19.21v ftfinds2_5 cv wlim ftfinds2_4 ftfinds2_2 ftfinds2_6 ftfinds2_5 cv wral ftfinds2_0 etfinds2_5 a2d syl5bi sbcth ax-mp ftfinds2_6 cv cvv wcel ftfinds2_5 cv wlim ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi wi ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_5 cv wlim ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi ftfinds2_5 ftfinds2_6 cv wsbc wi wb ftfinds2_6 vex ftfinds2_5 cv wlim ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi ftfinds2_5 ftfinds2_6 cv cvv sbcimg ax-mp mpbi ftfinds2_5 cv wlim ftfinds2_6 cv wlim ftfinds2_5 ftfinds2_6 cv ftfinds2_6 vex ftfinds2_5 cv ftfinds2_6 cv limeq sbcie ftfinds2_6 cv cvv wcel ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi wi ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_5 ftfinds2_6 cv wsbc ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 cv wsbc wi wb ftfinds2_6 vex ftfinds2_4 ftfinds2_2 wi ftfinds2_6 ftfinds2_5 cv wral ftfinds2_4 ftfinds2_0 wi ftfinds2_5 ftfinds2_6 cv cvv sbcimg ax-mp 3imtr3i syl5bir tfindes $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis for successors. $)
$( Induction hypothesis for limit ordinals. $)
$( Principle of Transfinite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last three are the basis, the induction hypothesis for
       successors, and the induction hypothesis for limit ordinals.
       (Contributed by NM, 6-Jan-2005.)  (Revised by David Abernethy,
       21-Jun-2011.) $)
${
	$d x A $.
	$d y ph $.
	$d x ch $.
	$d x ta $.
	$d x y et $.
	ftfinds3_0 $f wff ph $.
	ftfinds3_1 $f wff ps $.
	ftfinds3_2 $f wff ch $.
	ftfinds3_3 $f wff th $.
	ftfinds3_4 $f wff ta $.
	ftfinds3_5 $f wff et $.
	ftfinds3_6 $f set x $.
	ftfinds3_7 $f set y $.
	ftfinds3_8 $f class A $.
	etfinds3_0 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	etfinds3_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	etfinds3_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	etfinds3_3 $e |- ( x = A -> ( ph <-> ta ) ) $.
	etfinds3_4 $e |- ( et -> ps ) $.
	etfinds3_5 $e |- ( y e. On -> ( et -> ( ch -> th ) ) ) $.
	etfinds3_6 $e |- ( Lim x -> ( et -> ( A. y e. x ch -> ph ) ) ) $.
	tfinds3 $p |- ( A e. On -> ( et -> ta ) ) $= ftfinds3_5 ftfinds3_0 wi ftfinds3_5 ftfinds3_1 wi ftfinds3_5 ftfinds3_2 wi ftfinds3_5 ftfinds3_3 wi ftfinds3_5 ftfinds3_4 wi ftfinds3_6 ftfinds3_7 ftfinds3_8 ftfinds3_6 cv c0 wceq ftfinds3_0 ftfinds3_1 ftfinds3_5 etfinds3_0 imbi2d ftfinds3_6 cv ftfinds3_7 cv wceq ftfinds3_0 ftfinds3_2 ftfinds3_5 etfinds3_1 imbi2d ftfinds3_6 cv ftfinds3_7 cv csuc wceq ftfinds3_0 ftfinds3_3 ftfinds3_5 etfinds3_2 imbi2d ftfinds3_6 cv ftfinds3_8 wceq ftfinds3_0 ftfinds3_4 ftfinds3_5 etfinds3_3 imbi2d etfinds3_4 ftfinds3_7 cv con0 wcel ftfinds3_5 ftfinds3_2 ftfinds3_3 etfinds3_5 a2d ftfinds3_5 ftfinds3_2 wi ftfinds3_7 ftfinds3_6 cv wral ftfinds3_5 ftfinds3_2 ftfinds3_7 ftfinds3_6 cv wral wi ftfinds3_6 cv wlim ftfinds3_5 ftfinds3_0 wi ftfinds3_5 ftfinds3_2 ftfinds3_7 ftfinds3_6 cv r19.21v ftfinds3_6 cv wlim ftfinds3_5 ftfinds3_2 ftfinds3_7 ftfinds3_6 cv wral ftfinds3_0 etfinds3_6 a2d syl5bi tfinds $.
$}

