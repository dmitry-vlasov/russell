$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Introduce the Axiom of Union

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Union.  An axiom of Zermelo-Fraenkel set theory.  It states
       that a set ` y ` exists that includes the union of a given set ` x `
       i.e. the collection of all members of the members of ` x ` .  The
       variant ~ axun2 states that the union itself exists.  A version with the
       standard abbreviation for union is ~ uniex2 .  A version using class
       notation is ~ uniex .

       The union of a class ~ df-uni should not be confused with the union of
       two classes ~ df-un .  Their relationship is shown in ~ unipr .
       (Contributed by NM, 23-Dec-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y z $.
	fax-un_0 $f set x $.
	fax-un_1 $f set y $.
	fax-un_2 $f set z $.
	fax-un_3 $f set w $.
	ax-un $a |- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y ) $.
$}
$( Axiom of Union expressed with the fewest number of different variables.
       (Contributed by NM, 14-Aug-2003.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y z $.
	izfun_0 $f set w $.
	fzfun_0 $f set x $.
	fzfun_1 $f set y $.
	fzfun_2 $f set z $.
	zfun $p |- E. x A. y ( E. x ( y e. x /\ x e. z ) -> y e. x ) $= fzfun_1 sup_set_class izfun_0 sup_set_class wcel izfun_0 sup_set_class fzfun_2 sup_set_class wcel wa izfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel wi fzfun_1 wal fzfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel fzfun_0 sup_set_class fzfun_2 sup_set_class wcel wa fzfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel wi fzfun_1 wal fzfun_0 wex fzfun_2 fzfun_0 fzfun_1 izfun_0 ax-un fzfun_1 sup_set_class izfun_0 sup_set_class wcel izfun_0 sup_set_class fzfun_2 sup_set_class wcel wa izfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel wi fzfun_1 wal fzfun_1 sup_set_class fzfun_0 sup_set_class wcel fzfun_0 sup_set_class fzfun_2 sup_set_class wcel wa fzfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel wi fzfun_1 wal fzfun_0 fzfun_1 sup_set_class izfun_0 sup_set_class wcel izfun_0 sup_set_class fzfun_2 sup_set_class wcel wa izfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel wi fzfun_1 sup_set_class fzfun_0 sup_set_class wcel fzfun_0 sup_set_class fzfun_2 sup_set_class wcel wa fzfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel wi fzfun_1 fzfun_1 sup_set_class izfun_0 sup_set_class wcel izfun_0 sup_set_class fzfun_2 sup_set_class wcel wa izfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel fzfun_0 sup_set_class fzfun_2 sup_set_class wcel wa fzfun_0 wex fzfun_1 sup_set_class fzfun_0 sup_set_class wcel fzfun_1 sup_set_class izfun_0 sup_set_class wcel izfun_0 sup_set_class fzfun_2 sup_set_class wcel wa fzfun_1 sup_set_class fzfun_0 sup_set_class wcel fzfun_0 sup_set_class fzfun_2 sup_set_class wcel wa izfun_0 fzfun_0 izfun_0 sup_set_class fzfun_0 sup_set_class wceq fzfun_1 sup_set_class izfun_0 sup_set_class wcel fzfun_1 sup_set_class fzfun_0 sup_set_class wcel izfun_0 sup_set_class fzfun_2 sup_set_class wcel fzfun_0 sup_set_class fzfun_2 sup_set_class wcel izfun_0 fzfun_0 fzfun_1 elequ2 izfun_0 fzfun_0 fzfun_2 elequ1 anbi12d cbvexv imbi1i albii exbii mpbi $.
$}
$( A variant of the Axiom of Union ~ ax-un .  For any set ` x ` , there
       exists a set ` y ` whose members are exactly the members of the members
       of ` x ` i.e. the union of ` x ` .  Axiom Union of [BellMachover]
       p. 466.  (Contributed by NM, 4-Jun-2006.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y z $.
	faxun2_0 $f set x $.
	faxun2_1 $f set y $.
	faxun2_2 $f set z $.
	faxun2_3 $f set w $.
	axun2 $p |- E. y A. z ( z e. y <-> E. w ( z e. w /\ w e. x ) ) $= faxun2_2 sup_set_class faxun2_3 sup_set_class wcel faxun2_3 sup_set_class faxun2_0 sup_set_class wcel wa faxun2_3 wex faxun2_1 faxun2_2 faxun2_0 faxun2_1 faxun2_2 faxun2_3 ax-un bm1.3ii $.
$}
$( The Axiom of Union using the standard abbreviation for union.  Given any
       set ` x ` , its union ` y ` exists.  (Contributed by NM, 4-Jun-2006.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	iuniex2_0 $f set z $.
	funiex2_0 $f set x $.
	funiex2_1 $f set y $.
	uniex2 $p |- E. y y = U. x $= funiex2_1 sup_set_class funiex2_0 sup_set_class cuni wceq funiex2_1 wex iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel iuniex2_0 sup_set_class funiex2_0 sup_set_class cuni wcel wb iuniex2_0 wal funiex2_1 wex iuniex2_0 sup_set_class funiex2_0 sup_set_class cuni wcel funiex2_1 iuniex2_0 iuniex2_0 sup_set_class funiex2_0 sup_set_class cuni wcel iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel wi iuniex2_0 wal funiex2_1 wex iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel funiex2_1 sup_set_class funiex2_0 sup_set_class wcel wa funiex2_1 wex iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel wi iuniex2_0 wal funiex2_1 wex funiex2_1 iuniex2_0 funiex2_0 zfun iuniex2_0 sup_set_class funiex2_0 sup_set_class cuni wcel iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel wi iuniex2_0 wal iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel funiex2_1 sup_set_class funiex2_0 sup_set_class wcel wa funiex2_1 wex iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel wi iuniex2_0 wal funiex2_1 iuniex2_0 sup_set_class funiex2_0 sup_set_class cuni wcel iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel wi iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel funiex2_1 sup_set_class funiex2_0 sup_set_class wcel wa funiex2_1 wex iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel wi iuniex2_0 iuniex2_0 sup_set_class funiex2_0 sup_set_class cuni wcel iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel funiex2_1 sup_set_class funiex2_0 sup_set_class wcel wa funiex2_1 wex iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel funiex2_1 iuniex2_0 sup_set_class funiex2_0 sup_set_class eluni imbi1i albii exbii mpbir bm1.3ii funiex2_1 sup_set_class funiex2_0 sup_set_class cuni wceq iuniex2_0 sup_set_class funiex2_1 sup_set_class wcel iuniex2_0 sup_set_class funiex2_0 sup_set_class cuni wcel wb iuniex2_0 wal funiex2_1 iuniex2_0 funiex2_1 sup_set_class funiex2_0 sup_set_class cuni dfcleq exbii mpbir $.
$}
$( The Axiom of Union in class notation.  This says that if ` A ` is a set
       i.e. ` A e. _V ` (see ~ isset ), then the union of ` A ` is also a set.
       Same as Axiom 3 of [TakeutiZaring] p. 16.  (Contributed by NM,
       11-Aug-1993.) $)
${
	$v A $.
	$v x $.
	$v y $.
	$d x y A $.
	iuniex_0 $f set x $.
	iuniex_1 $f set y $.
	funiex_0 $f class A $.
	euniex_0 $e |- A e. _V $.
	uniex $p |- U. A e. _V $= iuniex_0 sup_set_class cuni cvv wcel funiex_0 cuni cvv wcel iuniex_0 funiex_0 euniex_0 iuniex_0 sup_set_class funiex_0 wceq iuniex_0 sup_set_class cuni funiex_0 cuni cvv iuniex_0 sup_set_class funiex_0 unieq eleq1d iuniex_1 iuniex_0 sup_set_class cuni iuniex_0 iuniex_1 uniex2 issetri vtocl $.
$}
$( The ZF Axiom of Union in class notation, in the form of a theorem
       instead of an inference.  We use the antecedent ` A e. V ` instead of
       ` A e. _V ` to make the theorem more general and thus shorten some
       proofs; obviously the universal class constant ` _V ` is one possible
       substitution for class variable ` V ` .  (Contributed by NM,
       25-Nov-1994.) $)
${
	$v A $.
	$v V $.
	$v x $.
	$d x A $.
	iuniexg_0 $f set x $.
	funiexg_0 $f class A $.
	funiexg_1 $f class V $.
	uniexg $p |- ( A e. V -> U. A e. _V ) $= iuniexg_0 sup_set_class cuni cvv wcel funiexg_0 cuni cvv wcel iuniexg_0 funiexg_0 funiexg_1 iuniexg_0 sup_set_class funiexg_0 wceq iuniexg_0 sup_set_class cuni funiexg_0 cuni cvv iuniexg_0 sup_set_class funiexg_0 unieq eleq1d iuniexg_0 sup_set_class iuniexg_0 vex uniex vtoclg $.
$}
$( The union of two sets is a set.  Corollary 5.8 of [TakeutiZaring]
       p. 16.  (Contributed by NM, 1-Jul-1994.) $)
${
	$v A $.
	$v B $.
	funex_0 $f class A $.
	funex_1 $f class B $.
	eunex_0 $e |- A e. _V $.
	eunex_1 $e |- B e. _V $.
	unex $p |- ( A u. B ) e. _V $= funex_0 funex_1 cpr cuni funex_0 funex_1 cun cvv funex_0 funex_1 eunex_0 eunex_1 unipr funex_0 funex_1 cpr funex_0 funex_1 prex uniex eqeltrri $.
$}
$( A triple of classes exists.  (Contributed by NM, 10-Apr-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	ftpex_0 $f class A $.
	ftpex_1 $f class B $.
	ftpex_2 $f class C $.
	tpex $p |- { A , B , C } e. _V $= ftpex_0 ftpex_1 ftpex_2 ctp ftpex_0 ftpex_1 cpr ftpex_2 csn cun cvv ftpex_0 ftpex_1 ftpex_2 df-tp ftpex_0 ftpex_1 cpr ftpex_2 csn ftpex_0 ftpex_1 prex ftpex_2 snex unex eqeltri $.
$}
$( Existence of union is equivalent to existence of its components.
       (Contributed by NM, 11-Jun-1998.) $)
${
	$v A $.
	$v B $.
	$v x $.
	$v y $.
	$d x y A $.
	$d x y B $.
	iunexb_0 $f set x $.
	iunexb_1 $f set y $.
	funexb_0 $f class A $.
	funexb_1 $f class B $.
	unexb $p |- ( ( A e. _V /\ B e. _V ) <-> ( A u. B ) e. _V ) $= funexb_0 cvv wcel funexb_1 cvv wcel wa funexb_0 funexb_1 cun cvv wcel iunexb_0 sup_set_class iunexb_1 sup_set_class cun cvv wcel funexb_0 iunexb_1 sup_set_class cun cvv wcel funexb_0 funexb_1 cun cvv wcel iunexb_0 iunexb_1 funexb_0 funexb_1 cvv cvv iunexb_0 sup_set_class funexb_0 wceq iunexb_0 sup_set_class iunexb_1 sup_set_class cun funexb_0 iunexb_1 sup_set_class cun cvv iunexb_0 sup_set_class funexb_0 iunexb_1 sup_set_class uneq1 eleq1d iunexb_1 sup_set_class funexb_1 wceq funexb_0 iunexb_1 sup_set_class cun funexb_0 funexb_1 cun cvv iunexb_1 sup_set_class funexb_1 funexb_0 uneq2 eleq1d iunexb_0 sup_set_class iunexb_1 sup_set_class iunexb_0 vex iunexb_1 vex unex vtocl2g funexb_0 funexb_1 cun cvv wcel funexb_0 cvv wcel funexb_1 cvv wcel funexb_0 funexb_0 funexb_1 cun wss funexb_0 funexb_1 cun cvv wcel funexb_0 cvv wcel funexb_0 funexb_1 ssun1 funexb_0 funexb_0 funexb_1 cun cvv ssexg mpan funexb_1 funexb_0 funexb_1 cun wss funexb_0 funexb_1 cun cvv wcel funexb_1 cvv wcel funexb_1 funexb_0 ssun2 funexb_1 funexb_0 funexb_1 cun cvv ssexg mpan jca impbii $.
$}
$( A union of two sets is a set.  Corollary 5.8 of [TakeutiZaring] p. 16.
     (Contributed by NM, 18-Sep-2006.) $)
${
	$v A $.
	$v B $.
	$v V $.
	$v W $.
	funexg_0 $f class A $.
	funexg_1 $f class B $.
	funexg_2 $f class V $.
	funexg_3 $f class W $.
	unexg $p |- ( ( A e. V /\ B e. W ) -> ( A u. B ) e. _V ) $= funexg_0 funexg_2 wcel funexg_0 cvv wcel funexg_1 cvv wcel funexg_0 funexg_1 cun cvv wcel funexg_1 funexg_3 wcel funexg_0 funexg_2 elex funexg_1 funexg_3 elex funexg_0 cvv wcel funexg_1 cvv wcel wa funexg_0 funexg_1 cun cvv wcel funexg_0 funexg_1 unexb biimpi syl2an $.
$}
$( A version of ~ unisn without the ` A e. _V ` hypothesis.  (Contributed
       by Stefan Allan, 14-Mar-2006.) $)
${
	$v A $.
	funisn2_0 $f class A $.
	unisn2 $p |- U. { A } e. { (/) , A } $= funisn2_0 cvv wcel funisn2_0 csn cuni c0 funisn2_0 cpr wcel funisn2_0 cvv wcel funisn2_0 csn cuni funisn2_0 c0 funisn2_0 cpr funisn2_0 cvv unisng c0 funisn2_0 cvv prid2g eqeltrd funisn2_0 cvv wcel wn funisn2_0 csn cuni c0 cuni c0 funisn2_0 cpr funisn2_0 cvv wcel wn funisn2_0 csn c0 funisn2_0 cvv wcel wn funisn2_0 csn c0 wceq funisn2_0 snprc biimpi unieqd c0 cuni c0 c0 funisn2_0 cpr uni0 c0 funisn2_0 0ex prid1 eqeltri syl6eqel pm2.61i $.
$}
$( Union of a singleton in the form of a restricted class abstraction.
       (Contributed by NM, 3-Jul-2008.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	funisn3_0 $f set x $.
	funisn3_1 $f class A $.
	funisn3_2 $f class B $.
	unisn3 $p |- ( A e. B -> U. { x e. B | x = A } = A ) $= funisn3_1 funisn3_2 wcel funisn3_0 sup_set_class funisn3_1 wceq funisn3_0 funisn3_2 crab cuni funisn3_1 csn cuni funisn3_1 funisn3_1 funisn3_2 wcel funisn3_0 sup_set_class funisn3_1 wceq funisn3_0 funisn3_2 crab funisn3_1 csn funisn3_0 funisn3_2 funisn3_1 rabsn unieqd funisn3_1 funisn3_2 unisng eqtrd $.
$}
$( The class of all singletons is a proper class.  (Contributed by NM,
       10-Oct-2008.)  (Proof shortened by Eric Schmidt, 7-Dec-2008.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	isnnex_0 $f set z $.
	fsnnex_0 $f set x $.
	fsnnex_1 $f set y $.
	snnex $p |- { x | E. y x = { y } } e/ _V $= fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cvv wnel fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cvv wcel wn fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cvv wcel fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cuni cvv wcel fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cuni cvv wcel cvv cvv wcel vprc fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cuni cvv cvv isnnex_0 fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cuni cvv isnnex_0 sup_set_class fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cuni wcel isnnex_0 sup_set_class cvv wcel isnnex_0 sup_set_class fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cuni wcel isnnex_0 sup_set_class fsnnex_0 sup_set_class wcel fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex wa fsnnex_0 wex isnnex_0 sup_set_class isnnex_0 sup_set_class csn wcel isnnex_0 sup_set_class csn fsnnex_1 sup_set_class csn wceq fsnnex_1 wex isnnex_0 sup_set_class fsnnex_0 sup_set_class wcel fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex wa fsnnex_0 wex isnnex_0 sup_set_class isnnex_0 vex snid fsnnex_1 sup_set_class isnnex_0 sup_set_class wceq fsnnex_1 wex isnnex_0 sup_set_class csn fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_1 isnnex_0 a9ev fsnnex_1 sup_set_class isnnex_0 sup_set_class wceq isnnex_0 sup_set_class csn fsnnex_1 sup_set_class csn wceq fsnnex_1 isnnex_0 sup_set_class csn fsnnex_1 sup_set_class csn wceq isnnex_0 sup_set_class fsnnex_1 sup_set_class isnnex_0 sup_set_class fsnnex_1 sup_set_class sneq eqcoms eximi ax-mp isnnex_0 sup_set_class fsnnex_0 sup_set_class wcel fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex wa isnnex_0 sup_set_class isnnex_0 sup_set_class csn wcel isnnex_0 sup_set_class csn fsnnex_1 sup_set_class csn wceq fsnnex_1 wex wa fsnnex_0 isnnex_0 sup_set_class csn isnnex_0 sup_set_class snex fsnnex_0 sup_set_class isnnex_0 sup_set_class csn wceq isnnex_0 sup_set_class fsnnex_0 sup_set_class wcel isnnex_0 sup_set_class isnnex_0 sup_set_class csn wcel fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex isnnex_0 sup_set_class csn fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 sup_set_class isnnex_0 sup_set_class csn isnnex_0 sup_set_class eleq2 fsnnex_0 sup_set_class isnnex_0 sup_set_class csn wceq fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq isnnex_0 sup_set_class csn fsnnex_1 sup_set_class csn wceq fsnnex_1 fsnnex_0 sup_set_class isnnex_0 sup_set_class csn fsnnex_1 sup_set_class csn eqeq1 exbidv anbi12d spcev mp2an fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 isnnex_0 sup_set_class eluniab mpbir isnnex_0 vex 2th eqriv eleq1i mtbir fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cvv uniexg mto fsnnex_0 sup_set_class fsnnex_1 sup_set_class csn wceq fsnnex_1 wex fsnnex_0 cab cvv df-nel mpbir $.
$}
$( If the subtrahend of a class difference exists, then the minuend exists
     iff the difference exists.  (Contributed by NM, 12-Nov-2003.)  (Proof
     shortened by Andrew Salmon, 12-Aug-2011.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifex2_0 $f class A $.
	fdifex2_1 $f class B $.
	fdifex2_2 $f class C $.
	difex2 $p |- ( B e. C -> ( A e. _V <-> ( A \ B ) e. _V ) ) $= fdifex2_1 fdifex2_2 wcel fdifex2_0 cvv wcel fdifex2_0 fdifex2_1 cdif cvv wcel fdifex2_0 fdifex2_1 cvv difexg fdifex2_0 fdifex2_1 cdif cvv wcel fdifex2_1 fdifex2_2 wcel fdifex2_0 cvv wcel fdifex2_0 fdifex2_1 cdif cvv wcel fdifex2_1 fdifex2_2 wcel wa fdifex2_0 fdifex2_0 fdifex2_1 cdif fdifex2_1 cun wss fdifex2_0 fdifex2_1 cdif fdifex2_1 cun cvv wcel fdifex2_0 cvv wcel fdifex2_0 fdifex2_1 fdifex2_0 cun fdifex2_0 fdifex2_1 cdif fdifex2_1 cun fdifex2_0 fdifex2_1 ssun2 fdifex2_0 fdifex2_1 cdif fdifex2_1 cun fdifex2_1 fdifex2_0 fdifex2_1 cdif cun fdifex2_1 fdifex2_0 cun fdifex2_0 fdifex2_1 cdif fdifex2_1 uncom fdifex2_1 fdifex2_0 undif2 eqtr2i sseqtri fdifex2_0 fdifex2_1 cdif fdifex2_1 cvv fdifex2_2 unexg fdifex2_0 fdifex2_0 fdifex2_1 cdif fdifex2_1 cun cvv ssexg sylancr expcom impbid2 $.
$}
$( Each member of an ordered pair belongs to the union of the union of a
       class to which the ordered pair belongs.  Lemma 3D of [Enderton] p. 41.
       (Contributed by NM, 31-Mar-1995.)  (Revised by Mario Carneiro,
       27-Feb-2016.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fopeluu_0 $f class A $.
	fopeluu_1 $f class B $.
	fopeluu_2 $f class C $.
	eopeluu_0 $e |- A e. _V $.
	eopeluu_1 $e |- B e. _V $.
	opeluu $p |- ( <. A , B >. e. C -> ( A e. U. U. C /\ B e. U. U. C ) ) $= fopeluu_0 fopeluu_1 cop fopeluu_2 wcel fopeluu_0 fopeluu_2 cuni cuni wcel fopeluu_1 fopeluu_2 cuni cuni wcel fopeluu_0 fopeluu_1 cop fopeluu_2 wcel fopeluu_0 fopeluu_0 fopeluu_1 cpr wcel fopeluu_0 fopeluu_1 cpr fopeluu_2 cuni wcel fopeluu_0 fopeluu_2 cuni cuni wcel fopeluu_0 fopeluu_1 eopeluu_0 prid1 fopeluu_0 fopeluu_1 cpr fopeluu_0 fopeluu_1 cop wcel fopeluu_0 fopeluu_1 cop fopeluu_2 wcel fopeluu_0 fopeluu_1 cpr fopeluu_2 cuni wcel fopeluu_0 fopeluu_1 eopeluu_0 eopeluu_1 opi2 fopeluu_0 fopeluu_1 cpr fopeluu_0 fopeluu_1 cop fopeluu_2 elunii mpan fopeluu_0 fopeluu_0 fopeluu_1 cpr fopeluu_2 cuni elunii sylancr fopeluu_0 fopeluu_1 cop fopeluu_2 wcel fopeluu_1 fopeluu_0 fopeluu_1 cpr wcel fopeluu_0 fopeluu_1 cpr fopeluu_2 cuni wcel fopeluu_1 fopeluu_2 cuni cuni wcel fopeluu_0 fopeluu_1 eopeluu_1 prid2 fopeluu_0 fopeluu_1 cpr fopeluu_0 fopeluu_1 cop wcel fopeluu_0 fopeluu_1 cop fopeluu_2 wcel fopeluu_0 fopeluu_1 cpr fopeluu_2 cuni wcel fopeluu_0 fopeluu_1 eopeluu_0 eopeluu_1 opi2 fopeluu_0 fopeluu_1 cpr fopeluu_0 fopeluu_1 cop fopeluu_2 elunii mpan fopeluu_1 fopeluu_0 fopeluu_1 cpr fopeluu_2 cuni elunii sylancr jca $.
$}
$( Expression for double union that moves union into a class builder.
       (Contributed by FL, 28-May-2007.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v z $.
	$v v $.
	$v u $.
	$d A x y v z $.
	$d A x y u z $.
	iuniuni_0 $f set z $.
	iuniuni_1 $f set v $.
	iuniuni_2 $f set u $.
	funiuni_0 $f set x $.
	funiuni_1 $f set y $.
	funiuni_2 $f class A $.
	uniuni $p |- U. U. A = U. { x | E. y ( x = U. y /\ y e. A ) } $= iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_2 cuni wcel wa iuniuni_2 wex iuniuni_0 cab iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab wcel wa iuniuni_1 wex iuniuni_0 cab funiuni_2 cuni cuni funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab cuni iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_2 cuni wcel wa iuniuni_2 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab wcel wa iuniuni_1 wex iuniuni_0 iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_2 cuni wcel wa iuniuni_2 wex iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex wa iuniuni_2 wex funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel wa funiuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab wcel wa iuniuni_1 wex iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_2 cuni wcel wa iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex wa iuniuni_2 iuniuni_2 sup_set_class funiuni_2 cuni wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel funiuni_1 iuniuni_2 sup_set_class funiuni_2 eluni anbi2i exbii iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex wa iuniuni_2 wex iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 wex iuniuni_2 wex funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa iuniuni_2 wex wa funiuni_1 wex funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel wa funiuni_1 wex iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex wa iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 wex iuniuni_2 iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 wex iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex wa iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 19.42v bicomi exbii iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 wex iuniuni_2 wex iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa wa iuniuni_2 wex funiuni_1 wex funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa wa iuniuni_2 wex funiuni_1 wex funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa iuniuni_2 wex wa funiuni_1 wex iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa wa iuniuni_2 funiuni_1 excom iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa wa funiuni_1 iuniuni_2 iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel wa wa iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa wa iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel funiuni_1 sup_set_class funiuni_2 wcel anass iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa funiuni_1 sup_set_class funiuni_2 wcel ancom bitr3i 2exbii funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa funiuni_1 iuniuni_2 exdistr 3bitri funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa iuniuni_2 wex wa funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel wa funiuni_1 iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa iuniuni_2 wex iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel iuniuni_0 sup_set_class iuniuni_2 sup_set_class wcel iuniuni_2 sup_set_class funiuni_1 sup_set_class wcel wa iuniuni_2 wex iuniuni_2 iuniuni_0 sup_set_class funiuni_1 sup_set_class eluni bicomi anbi2i exbii 3bitri funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel wa funiuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa wa iuniuni_1 wex funiuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 wex iuniuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab wcel wa iuniuni_1 wex funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel wa iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa wa iuniuni_1 wex funiuni_1 funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel wa funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa iuniuni_1 wex wa funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa wa iuniuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa wa iuniuni_1 wex iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa iuniuni_1 wex funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel wa iuniuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa iuniuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_0 sup_set_class funiuni_1 sup_set_class cuni wcel iuniuni_1 funiuni_1 sup_set_class cuni funiuni_1 sup_set_class funiuni_1 vex uniex iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni iuniuni_0 sup_set_class eleq2 ceqsexv iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 exancom bitr3i anbi2i funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa iuniuni_1 19.42v funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa wa iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa wa iuniuni_1 funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa wa iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa funiuni_1 sup_set_class funiuni_2 wcel wa iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 sup_set_class funiuni_2 wcel iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq wa ancom iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel anass bitri exbii 3bitr2i exbii iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 iuniuni_1 excom iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa wa funiuni_1 wex iuniuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex wa iuniuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab wcel wa iuniuni_1 wex iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa iuniuni_1 funiuni_1 exdistr iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex wa iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab wcel wa iuniuni_1 iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex iuniuni_1 sup_set_class funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab wcel iuniuni_0 sup_set_class iuniuni_1 sup_set_class wcel iuniuni_1 sup_set_class funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab wcel iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 iuniuni_1 sup_set_class iuniuni_1 vex funiuni_0 sup_set_class iuniuni_1 sup_set_class wceq funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 funiuni_0 sup_set_class iuniuni_1 sup_set_class wceq funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel funiuni_0 sup_set_class iuniuni_1 sup_set_class funiuni_1 sup_set_class cuni eqeq1 anbi1d exbidv elab bicomi anbi2i exbii bitri 3bitri 3bitri abbii iuniuni_0 iuniuni_2 funiuni_2 cuni df-uni iuniuni_0 iuniuni_1 funiuni_0 sup_set_class funiuni_1 sup_set_class cuni wceq funiuni_1 sup_set_class funiuni_2 wcel wa funiuni_1 wex funiuni_0 cab df-uni 3eqtr4i $.
$}
$( Two ways to express single-valuedness of a class expression
       ` A ( x ) ` .  (Contributed by NM, 14-Oct-2010.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v z $.
	$d x y z $.
	$d A y z $.
	ieusv1_0 $f set z $.
	feusv1_0 $f set x $.
	feusv1_1 $f set y $.
	feusv1_2 $f class A $.
	eusv1 $p |- ( E! y A. x y = A <-> E. y A. x y = A ) $= feusv1_1 sup_set_class feusv1_2 wceq feusv1_0 wal feusv1_1 weu feusv1_1 sup_set_class feusv1_2 wceq feusv1_0 wal feusv1_1 wex feusv1_1 sup_set_class feusv1_2 wceq feusv1_0 wal ieusv1_0 sup_set_class feusv1_2 wceq feusv1_0 wal wa feusv1_1 sup_set_class ieusv1_0 sup_set_class wceq wi ieusv1_0 wal feusv1_1 wal feusv1_1 sup_set_class feusv1_2 wceq feusv1_0 wal ieusv1_0 sup_set_class feusv1_2 wceq feusv1_0 wal wa feusv1_1 sup_set_class ieusv1_0 sup_set_class wceq wi feusv1_1 ieusv1_0 feusv1_1 sup_set_class feusv1_2 wceq feusv1_0 wal feusv1_1 sup_set_class feusv1_2 wceq ieusv1_0 sup_set_class feusv1_2 wceq feusv1_1 sup_set_class ieusv1_0 sup_set_class wceq ieusv1_0 sup_set_class feusv1_2 wceq feusv1_0 wal feusv1_1 sup_set_class feusv1_2 wceq feusv1_0 sp ieusv1_0 sup_set_class feusv1_2 wceq feusv1_0 sp feusv1_1 sup_set_class ieusv1_0 sup_set_class feusv1_2 eqtr3 syl2an gen2 feusv1_1 sup_set_class feusv1_2 wceq feusv1_0 wal ieusv1_0 sup_set_class feusv1_2 wceq feusv1_0 wal feusv1_1 ieusv1_0 feusv1_1 sup_set_class ieusv1_0 sup_set_class wceq feusv1_1 sup_set_class feusv1_2 wceq ieusv1_0 sup_set_class feusv1_2 wceq feusv1_0 feusv1_1 sup_set_class ieusv1_0 sup_set_class feusv1_2 eqeq1 albidv eu4 mpbiran2 $.
$}
$( Even if ` x ` is free in ` A ` , it is effectively bound when
       ` A ( x ) ` is single-valued.  (Contributed by NM, 14-Oct-2010.)
       (Revised by Mario Carneiro, 14-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v z $.
	$v w $.
	$d x y z w $.
	$d A y z w $.
	ieusvnf_0 $f set z $.
	ieusvnf_1 $f set w $.
	feusvnf_0 $f set x $.
	feusvnf_1 $f set y $.
	feusvnf_2 $f class A $.
	eusvnf $p |- ( E! y A. x y = A -> F/_ x A ) $= feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_1 weu feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_1 wex feusvnf_0 feusvnf_2 wnfc feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_1 euex feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_0 feusvnf_2 wnfc feusvnf_1 feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 csb feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 csb wceq ieusvnf_1 wal ieusvnf_0 wal feusvnf_0 feusvnf_2 wnfc feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 csb feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 csb wceq ieusvnf_0 ieusvnf_1 feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_1 sup_set_class feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 csb feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 csb ieusvnf_0 sup_set_class cvv wcel feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_1 sup_set_class feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 csb wceq wi ieusvnf_0 vex feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_1 sup_set_class feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 csb wceq feusvnf_0 ieusvnf_0 sup_set_class cvv feusvnf_0 ieusvnf_0 sup_set_class nfcv feusvnf_0 feusvnf_1 sup_set_class feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 csb feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 nfcsb1v nfeq2 feusvnf_0 sup_set_class ieusvnf_0 sup_set_class wceq feusvnf_2 feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 csb feusvnf_1 sup_set_class feusvnf_0 ieusvnf_0 sup_set_class feusvnf_2 csbeq1a eqeq2d spcgf ax-mp ieusvnf_1 sup_set_class cvv wcel feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_0 wal feusvnf_1 sup_set_class feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 csb wceq wi ieusvnf_1 vex feusvnf_1 sup_set_class feusvnf_2 wceq feusvnf_1 sup_set_class feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 csb wceq feusvnf_0 ieusvnf_1 sup_set_class cvv feusvnf_0 ieusvnf_1 sup_set_class nfcv feusvnf_0 feusvnf_1 sup_set_class feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 csb feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 nfcsb1v nfeq2 feusvnf_0 sup_set_class ieusvnf_1 sup_set_class wceq feusvnf_2 feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 csb feusvnf_1 sup_set_class feusvnf_0 ieusvnf_1 sup_set_class feusvnf_2 csbeq1a eqeq2d spcgf ax-mp eqtr3d alrimivv feusvnf_0 ieusvnf_0 ieusvnf_1 feusvnf_2 sbnfc2 sylibr exlimiv syl $.
$}
$( Two ways to say that ` A ( x ) ` is a set expression that does not
       depend on ` x ` .  (Contributed by Mario Carneiro, 18-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d A y $.
	feusvnfb_0 $f set x $.
	feusvnfb_1 $f set y $.
	feusvnfb_2 $f class A $.
	eusvnfb $p |- ( E! y A. x y = A <-> ( F/_ x A /\ A e. _V ) ) $= feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 weu feusvnfb_0 feusvnfb_2 wnfc feusvnfb_2 cvv wcel wa feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 weu feusvnfb_0 feusvnfb_2 wnfc feusvnfb_2 cvv wcel feusvnfb_0 feusvnfb_1 feusvnfb_2 eusvnf feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 weu feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 wex feusvnfb_2 cvv wcel feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 euex feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_2 cvv wcel feusvnfb_1 feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_2 cvv wcel feusvnfb_0 feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_2 feusvnfb_1 sup_set_class cvv feusvnfb_1 sup_set_class feusvnfb_2 wceq id feusvnfb_1 vex syl6eqelr sps exlimiv syl jca feusvnfb_0 feusvnfb_2 wnfc feusvnfb_2 cvv wcel wa feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 wex feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 weu feusvnfb_0 feusvnfb_2 wnfc feusvnfb_2 cvv wcel feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 wex feusvnfb_2 cvv wcel feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_1 wex feusvnfb_0 feusvnfb_2 wnfc feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 wex feusvnfb_1 feusvnfb_2 isset feusvnfb_0 feusvnfb_2 wnfc feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 wal feusvnfb_1 feusvnfb_0 feusvnfb_2 wnfc feusvnfb_1 sup_set_class feusvnfb_2 wceq feusvnfb_0 feusvnfb_0 feusvnfb_2 wnfc feusvnfb_0 feusvnfb_1 sup_set_class feusvnfb_2 feusvnfb_0 feusvnfb_2 wnfc feusvnfb_0 feusvnfb_1 sup_set_class nfcvd feusvnfb_0 feusvnfb_2 wnfc id nfeqd nfrd eximdv syl5bi imp feusvnfb_0 feusvnfb_1 feusvnfb_2 eusv1 sylibr impbii $.
$}
$( Two ways to express single-valuedness of a class expression
       ` A ( x ) ` .  (Contributed by NM, 14-Oct-2010.)  (Revised by Mario
       Carneiro, 18-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d A y $.
	feusv2i_0 $f set x $.
	feusv2i_1 $f set y $.
	feusv2i_2 $f class A $.
	eusv2i $p |- ( E! y A. x y = A -> E! y E. x y = A ) $= feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 weu feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wex feusv2i_1 weu feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 weu feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wex feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 nfeu1 feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 weu feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wex feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 weu feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wnf feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wex feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal wi feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 weu feusv2i_0 feusv2i_1 sup_set_class feusv2i_2 feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 wal feusv2i_1 weu feusv2i_0 feusv2i_1 sup_set_class nfcvd feusv2i_0 feusv2i_1 feusv2i_2 eusvnf nfeqd feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 nf2 sylib feusv2i_1 sup_set_class feusv2i_2 wceq feusv2i_0 19.2 impbid1 eubid ibir $.
$}
$( Two ways to express single-valuedness of a class expression
       ` A ( x ) ` .  (Contributed by Mario Carneiro, 18-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d A y $.
	feusv2nf_0 $f set x $.
	feusv2nf_1 $f set y $.
	feusv2nf_2 $f class A $.
	eeusv2nf_0 $e |- A e. _V $.
	eusv2nf $p |- ( E! y E. x y = A <-> F/_ x A ) $= feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 weu feusv2nf_0 feusv2nf_2 wnfc feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 weu feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wnf feusv2nf_1 wal feusv2nf_0 feusv2nf_2 wnfc feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 weu feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wnf feusv2nf_1 feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 nfeu1 feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 weu feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq wi feusv2nf_0 wal feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wnf feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 weu feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq wi feusv2nf_0 feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_0 feusv2nf_1 feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 nfe1 nfeu feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 weu feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq wa feusv2nf_1 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq wi feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_1 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq wa feusv2nf_1 wex feusv2nf_1 feusv2nf_2 eeusv2nf_0 isseti feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq wa feusv2nf_1 feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 19.8a ancri eximi ax-mp feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_1 eupick mpan2 alrimi feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 nf3 sylibr alrimi feusv2nf_2 cvv wcel feusv2nf_0 feusv2nf_2 wnfc feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wnf feusv2nf_1 wal wb feusv2nf_0 feusv2nf_0 feusv2nf_1 feusv2nf_2 cvv dfnfc2 eeusv2nf_0 mpg sylibr feusv2nf_0 feusv2nf_2 wnfc feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wal feusv2nf_1 weu feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wex feusv2nf_1 weu feusv2nf_1 sup_set_class feusv2nf_2 wceq feusv2nf_0 wal feusv2nf_1 weu feusv2nf_0 feusv2nf_2 wnfc feusv2nf_2 cvv wcel eeusv2nf_0 feusv2nf_0 feusv2nf_1 feusv2nf_2 eusvnfb mpbiran2 feusv2nf_0 feusv2nf_1 feusv2nf_2 eusv2i sylbir impbii $.
$}
$( Two ways to express single-valuedness of a class expression
       ` A ( x ) ` .  (Contributed by NM, 15-Oct-2010.)  (Proof shortened by
       Mario Carneiro, 18-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d A y $.
	feusv2_0 $f set x $.
	feusv2_1 $f set y $.
	feusv2_2 $f class A $.
	eeusv2_0 $e |- A e. _V $.
	eusv2 $p |- ( E! y E. x y = A <-> E! y A. x y = A ) $= feusv2_1 sup_set_class feusv2_2 wceq feusv2_0 wex feusv2_1 weu feusv2_0 feusv2_2 wnfc feusv2_1 sup_set_class feusv2_2 wceq feusv2_0 wal feusv2_1 weu feusv2_0 feusv2_1 feusv2_2 eeusv2_0 eusv2nf feusv2_1 sup_set_class feusv2_2 wceq feusv2_0 wal feusv2_1 weu feusv2_0 feusv2_2 wnfc feusv2_2 cvv wcel eeusv2_0 feusv2_0 feusv2_1 feusv2_2 eusvnfb mpbiran2 bitr4i $.
$}
$( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  (Contributed by NM, 16-Dec-2012.)  (Proof shortened by
       Mario Carneiro, 18-Nov-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x ph $.
	$d x y $.
	freusv1_0 $f wff ph $.
	freusv1_1 $f set x $.
	freusv1_2 $f set y $.
	freusv1_3 $f class A $.
	freusv1_4 $f class B $.
	freusv1_5 $f class C $.
	reusv1 $p |- ( E. y e. B ph -> ( E! x e. A A. y e. B ( ph -> x = C ) <-> E. x e. A A. y e. B ( ph -> x = C ) ) ) $= freusv1_0 freusv1_2 freusv1_4 wrex freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 wmo freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 freusv1_3 wrmo freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 freusv1_3 wreu freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 freusv1_3 wrex wb freusv1_0 freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 wmo freusv1_2 freusv1_4 freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_2 freusv1_1 freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 nfra1 nfmo freusv1_2 sup_set_class freusv1_4 wcel freusv1_0 freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 wmo freusv1_2 sup_set_class freusv1_4 wcel freusv1_0 wa freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_1 wal freusv1_1 sup_set_class freusv1_5 wceq freusv1_1 wmo freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 wmo freusv1_2 sup_set_class freusv1_4 wcel freusv1_0 wa freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_1 freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_2 sup_set_class freusv1_4 wcel freusv1_0 wa freusv1_1 sup_set_class freusv1_5 wceq freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_2 sup_set_class freusv1_4 wcel freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 rsp imp3a com12 alrimiv freusv1_1 freusv1_5 moeq freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 sup_set_class freusv1_5 wceq freusv1_1 moim ee10 ex rexlimi freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 freusv1_3 mormo freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 freusv1_3 wreu freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 freusv1_3 wrex freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 freusv1_3 wrmo freusv1_0 freusv1_1 sup_set_class freusv1_5 wceq wi freusv1_2 freusv1_4 wral freusv1_1 freusv1_3 reu5 rbaib 3syl $.
$}
$( Lemma for ~ reusv2 .  (Contributed by NM, 22-Oct-2010.)  (Proof
       shortened by Mario Carneiro, 19-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x B $.
	freusv2lem1_0 $f set x $.
	freusv2lem1_1 $f set y $.
	freusv2lem1_2 $f class A $.
	freusv2lem1_3 $f class B $.
	reusv2lem1 $p |- ( A =/= (/) -> ( E! x A. y e. A x = B <-> E. x A. y e. A x = B ) ) $= freusv2lem1_2 c0 wne freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 wmo freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 weu freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 wex wb freusv2lem1_2 c0 wne freusv2lem1_1 sup_set_class freusv2lem1_2 wcel freusv2lem1_1 wex freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 wmo freusv2lem1_1 freusv2lem1_2 n0 freusv2lem1_1 sup_set_class freusv2lem1_2 wcel freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 wmo freusv2lem1_1 freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_1 freusv2lem1_0 freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 nfra1 nfmo freusv2lem1_1 sup_set_class freusv2lem1_2 wcel freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 sup_set_class freusv2lem1_3 wceq wi freusv2lem1_0 wal freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_0 wmo freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 wmo freusv2lem1_1 sup_set_class freusv2lem1_2 wcel freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 sup_set_class freusv2lem1_3 wceq wi freusv2lem1_0 freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_1 sup_set_class freusv2lem1_2 wcel freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 rsp com12 alrimiv freusv2lem1_0 freusv2lem1_3 moeq freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_0 moim ee10 exlimi sylbi freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 weu freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 wex freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 wmo freusv2lem1_0 sup_set_class freusv2lem1_3 wceq freusv2lem1_1 freusv2lem1_2 wral freusv2lem1_0 eu5 rbaib syl $.
$}
$( Lemma for ~ reusv2 .  (Contributed by NM, 27-Oct-2010.)  (Proof
       shortened by Mario Carneiro, 19-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v z $.
	$d x y z A $.
	$d x z B $.
	$d x z $.
	$d x z $.
	ireusv2lem2_0 $f set z $.
	freusv2lem2_0 $f set x $.
	freusv2lem2_1 $f set y $.
	freusv2lem2_2 $f class A $.
	freusv2lem2_3 $f class B $.
	reusv2lem2 $p |- ( E! x A. y e. A x = B -> E! x E. y e. A x = B ) $= freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 weu wi freusv2lem2_2 c0 freusv2lem2_2 c0 wceq freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 wal freusv2lem2_2 c0 wceq freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wn freusv2lem2_0 wex freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 wal wn freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 eunex freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 exnal sylib freusv2lem2_2 c0 wceq freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 rzal alrimiv nsyl3 pm2.21d freusv2lem2_2 c0 wne freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 weu freusv2lem2_2 c0 wne freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu wa freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu freusv2lem2_2 c0 wne freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu simpr freusv2lem2_2 c0 wne freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu wb freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral ireusv2lem2_0 wex freusv2lem2_2 c0 wne freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu wb freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 wex ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral ireusv2lem2_0 wex freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 euex freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 ireusv2lem2_0 freusv2lem2_0 sup_set_class ireusv2lem2_0 sup_set_class wceq freusv2lem2_0 sup_set_class freusv2lem2_3 wceq ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 freusv2lem2_0 sup_set_class ireusv2lem2_0 sup_set_class freusv2lem2_3 eqeq1 ralbidv cbvexv sylib freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu wb ireusv2lem2_0 freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 weu freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 weu wb freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wa freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wa freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wa freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_1 freusv2lem2_2 freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_1 freusv2lem2_2 c0 wne freusv2lem2_1 nfv ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 nfra1 nfan freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 nfra1 freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wa freusv2lem2_1 sup_set_class freusv2lem2_2 wcel freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wa freusv2lem2_1 sup_set_class freusv2lem2_2 wcel freusv2lem2_0 sup_set_class freusv2lem2_3 wceq wa wa freusv2lem2_0 sup_set_class ireusv2lem2_0 sup_set_class wceq freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wa freusv2lem2_1 sup_set_class freusv2lem2_2 wcel freusv2lem2_0 sup_set_class freusv2lem2_3 wceq wa wa freusv2lem2_0 sup_set_class freusv2lem2_3 ireusv2lem2_0 sup_set_class freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wa freusv2lem2_1 sup_set_class freusv2lem2_2 wcel freusv2lem2_0 sup_set_class freusv2lem2_3 wceq simprr ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_1 sup_set_class freusv2lem2_2 wcel ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_2 c0 wne freusv2lem2_0 sup_set_class freusv2lem2_3 wceq ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_1 sup_set_class freusv2lem2_2 wcel ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 rsp imp ad2ant2lr eqtr4d freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral wa freusv2lem2_1 sup_set_class freusv2lem2_2 wcel freusv2lem2_0 sup_set_class freusv2lem2_3 wceq wa wa freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 sup_set_class ireusv2lem2_0 sup_set_class wceq ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_2 c0 wne ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_1 sup_set_class freusv2lem2_2 wcel freusv2lem2_0 sup_set_class freusv2lem2_3 wceq wa simplr freusv2lem2_0 sup_set_class ireusv2lem2_0 sup_set_class wceq freusv2lem2_0 sup_set_class freusv2lem2_3 wceq ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 freusv2lem2_0 sup_set_class ireusv2lem2_0 sup_set_class freusv2lem2_3 eqeq1 ralbidv syl5ibrcom mpd exp32 rexlimd freusv2lem2_2 c0 wne freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex wi ireusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_2 c0 wne freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wral freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 wrex freusv2lem2_0 sup_set_class freusv2lem2_3 wceq freusv2lem2_1 freusv2lem2_2 r19.2z ex adantr impbid eubidv ex exlimdv syl5 imp mpbird ex pm2.61ine $.
$}
$( Lemma for ~ reusv2 .  (Contributed by NM, 14-Dec-2012.)  (Proof
       shortened by Mario Carneiro, 19-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x B $.
	freusv2lem3_0 $f set x $.
	freusv2lem3_1 $f set y $.
	freusv2lem3_2 $f class A $.
	freusv2lem3_3 $f class B $.
	reusv2lem3 $p |- ( A. y e. A B e. _V -> ( E! x E. y e. A x = B <-> E! x A. y e. A x = B ) ) $= freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 weu freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 weu freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 weu freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu simpr freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_0 freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 nfv freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 nfeu1 nfan freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_2 c0 wne freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex wi freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_2 c0 wne freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 wex freusv2lem3_2 c0 wne freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 euex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_2 c0 wne freusv2lem3_0 freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 rexn0 exlimiv syl adantl freusv2lem3_2 c0 wne freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 r19.2z ex syl freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_1 freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 nfra1 freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_1 freusv2lem3_0 freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 nfre1 nfeu nfan freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 nfre1 freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_1 sup_set_class freusv2lem3_2 wcel freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_1 sup_set_class freusv2lem3_2 wcel freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq wi freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_1 sup_set_class freusv2lem3_2 wcel wa freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq wa freusv2lem3_0 wex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq wi freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_1 sup_set_class freusv2lem3_2 wcel simplr freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_1 sup_set_class freusv2lem3_2 wcel wa freusv2lem3_1 sup_set_class freusv2lem3_2 wcel freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_0 wex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq wa freusv2lem3_0 wex freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_1 sup_set_class freusv2lem3_2 wcel simpr freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_1 sup_set_class freusv2lem3_2 wcel wa freusv2lem3_3 cvv wcel freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_0 wex freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu wa freusv2lem3_1 sup_set_class freusv2lem3_2 wcel freusv2lem3_3 cvv wcel freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 wral freusv2lem3_1 sup_set_class freusv2lem3_2 wcel freusv2lem3_3 cvv wcel wi freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 weu freusv2lem3_3 cvv wcel freusv2lem3_1 freusv2lem3_2 rsp adantr imp freusv2lem3_0 freusv2lem3_3 isset sylib freusv2lem3_1 sup_set_class freusv2lem3_2 wcel freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq wa freusv2lem3_0 freusv2lem3_1 sup_set_class freusv2lem3_2 wcel freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_1 sup_set_class freusv2lem3_2 wcel freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 rspe ex ancrd eximdv sylc freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_1 freusv2lem3_2 wrex freusv2lem3_0 sup_set_class freusv2lem3_3 wceq freusv2lem3_0 eupick syl2anc ex com23 ralrimd impbid eubid mpbird ex freusv2lem3_0 freusv2lem3_1 freusv2lem3_2 freusv2lem3_3 reusv2lem2 impbid1 $.
$}
$( Lemma for ~ reusv2 .  (Contributed by NM, 13-Dec-2012.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v z $.
	$d x y z A $.
	$d x z B $.
	$d x z C $.
	$d x z ph $.
	ireusv2lem4_0 $f set z $.
	freusv2lem4_0 $f wff ph $.
	freusv2lem4_1 $f set x $.
	freusv2lem4_2 $f set y $.
	freusv2lem4_3 $f class A $.
	freusv2lem4_4 $f class B $.
	freusv2lem4_5 $f class C $.
	reusv2lem4 $p |- ( E! x e. A E. y e. B ( ph /\ x = C ) <-> E! x A. y e. B ( ( C e. A /\ ph ) -> x = C ) ) $= freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 freusv2lem4_4 wrex freusv2lem4_1 freusv2lem4_3 wreu freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 freusv2lem4_4 wrex wa freusv2lem4_1 weu freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wrex freusv2lem4_1 weu freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 freusv2lem4_4 wral freusv2lem4_1 weu freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 freusv2lem4_4 wrex freusv2lem4_1 freusv2lem4_3 df-reu freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 freusv2lem4_4 wrex wa freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wrex freusv2lem4_1 freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa wa freusv2lem4_2 freusv2lem4_4 wrex freusv2lem4_1 sup_set_class freusv2lem4_5 wceq freusv2lem4_2 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wrex freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 freusv2lem4_4 wrex wa freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wrex freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq freusv2lem4_2 freusv2lem4_4 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa wa freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa wa wa freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa wa freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq anass bicomi freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa wa freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa wa freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq anass freusv2lem4_1 sup_set_class freusv2lem4_5 wceq freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 freusv2lem4_3 eleq1 anbi1d pm5.32ri bitr3i anbi2i freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 rabid anbi1i 3bitr4i rexbii2 freusv2lem4_1 sup_set_class freusv2lem4_3 wcel freusv2lem4_0 freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wa freusv2lem4_2 freusv2lem4_4 r19.42v freusv2lem4_1 sup_set_class freusv2lem4_5 wceq freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq freusv2lem4_2 ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 nfrab1 ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab nfcv freusv2lem4_1 sup_set_class freusv2lem4_5 wceq ireusv2lem4_0 nfv freusv2lem4_2 freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 nfcsb1v nfeq2 freusv2lem4_2 sup_set_class ireusv2lem4_0 sup_set_class wceq freusv2lem4_5 freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csbeq1a eqeq2d cbvrexf 3bitr3i eubii freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wrex freusv2lem4_1 weu freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wral freusv2lem4_1 weu freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 freusv2lem4_4 wral freusv2lem4_1 weu freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb cvv wcel ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wral freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wrex freusv2lem4_1 weu freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wral freusv2lem4_1 weu wb freusv2lem4_5 cvv wcel freusv2lem4_2 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wral freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb cvv wcel ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wral freusv2lem4_5 cvv wcel freusv2lem4_2 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa wa freusv2lem4_5 cvv wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 rabid freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_5 cvv wcel freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_0 freusv2lem4_5 freusv2lem4_3 elex ad2antrl sylbi rgen freusv2lem4_5 cvv wcel freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb cvv wcel freusv2lem4_2 ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 nfrab1 ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab nfcv freusv2lem4_5 cvv wcel ireusv2lem4_0 nfv freusv2lem4_2 freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb cvv freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 nfcsb1v nfel1 freusv2lem4_2 sup_set_class ireusv2lem4_0 sup_set_class wceq freusv2lem4_5 freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb cvv freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csbeq1a eleq1d cbvralf mpbi freusv2lem4_1 ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb reusv2lem3 ax-mp freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wral freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 freusv2lem4_4 wral freusv2lem4_1 freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wral ireusv2lem4_0 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq wi ireusv2lem4_0 wal freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 wal freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 freusv2lem4_4 wral freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq ireusv2lem4_0 freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab df-ral freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi ireusv2lem4_0 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq wi freusv2lem4_2 ireusv2lem4_0 freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi ireusv2lem4_0 nfv ireusv2lem4_0 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq freusv2lem4_2 freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 nfrab1 nfel2 freusv2lem4_2 freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 nfcsb1v nfeq2 nfim freusv2lem4_2 sup_set_class ireusv2lem4_0 sup_set_class wceq freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel ireusv2lem4_0 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_5 wceq freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb wceq freusv2lem4_2 sup_set_class ireusv2lem4_0 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab eleq1 freusv2lem4_2 sup_set_class ireusv2lem4_0 sup_set_class wceq freusv2lem4_5 freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csb freusv2lem4_1 sup_set_class freusv2lem4_2 ireusv2lem4_0 sup_set_class freusv2lem4_5 csbeq1a eqeq2d imbi12d cbval freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 wal freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi wi freusv2lem4_2 wal freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 freusv2lem4_4 wral freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi wi freusv2lem4_2 freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi wi freusv2lem4_2 sup_set_class freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 crab wcel freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_2 freusv2lem4_4 rabid imbi1i freusv2lem4_2 sup_set_class freusv2lem4_4 wcel freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq impexp bitri albii freusv2lem4_5 freusv2lem4_3 wcel freusv2lem4_0 wa freusv2lem4_1 sup_set_class freusv2lem4_5 wceq wi freusv2lem4_2 freusv2lem4_4 df-ral bitr4i 3bitr2i eubii bitri 3bitri $.
$}
$( Lemma for ~ reusv2 .  (Contributed by NM, 4-Jan-2013.)  (Proof shortened
       by Mario Carneiro, 19-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d x y B $.
	$d x C $.
	freusv2lem5_0 $f set x $.
	freusv2lem5_1 $f set y $.
	freusv2lem5_2 $f class A $.
	freusv2lem5_3 $f class B $.
	freusv2lem5_4 $f class C $.
	reusv2lem5 $p |- ( ( A. y e. B C e. A /\ B =/= (/) ) -> ( E! x e. A E. y e. B x = C <-> E! x e. A A. y e. B x = C ) ) $= freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_3 c0 wne wa freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 weu freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 wral wa freusv2lem5_0 weu freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 wrex freusv2lem5_0 freusv2lem5_2 wreu freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 freusv2lem5_2 wreu freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 weu freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 weu freusv2lem5_3 c0 wne freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 wral wa freusv2lem5_0 weu freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa wb freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_1 freusv2lem5_3 wral wb freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa wb freusv2lem5_1 freusv2lem5_3 freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_4 freusv2lem5_2 wcel wtru freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi wb tru freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq biimt mpan2 freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq ibar bitr3d freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_4 freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 freusv2lem5_2 eleq1 pm5.32ri syl6bbr ralimi freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_1 freusv2lem5_3 ralbi syl eubidv freusv2lem5_3 c0 wne freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 wral wa freusv2lem5_0 freusv2lem5_0 sup_set_class freusv2lem5_2 wcel freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 r19.28zv eubidv sylan9bb freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 wrex freusv2lem5_0 freusv2lem5_2 wreu wtru freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_1 freusv2lem5_3 wrex freusv2lem5_0 freusv2lem5_2 wreu freusv2lem5_4 freusv2lem5_2 wcel wtru wa freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wi freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 weu freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 wrex wtru freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_1 freusv2lem5_3 wrex freusv2lem5_0 freusv2lem5_2 freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wtru freusv2lem5_0 sup_set_class freusv2lem5_4 wceq wa freusv2lem5_1 freusv2lem5_3 wtru freusv2lem5_0 sup_set_class freusv2lem5_4 wceq tru biantrur rexbii reubii wtru freusv2lem5_0 freusv2lem5_1 freusv2lem5_2 freusv2lem5_3 freusv2lem5_4 reusv2lem4 bitri freusv2lem5_0 sup_set_class freusv2lem5_4 wceq freusv2lem5_1 freusv2lem5_3 wral freusv2lem5_0 freusv2lem5_2 df-reu 3bitr4g $.
$}
$( Two ways to express single-valuedness of a class expression ` C ( y ) `
       that is constant for those ` y e. B ` such that ` ph ` .  The first
       antecedent ensures that the constant value belongs to the existential
       uniqueness domain ` A ` , and the second ensures that ` C ( y ) ` is
       evaluated for at least one ` y ` .  (Contributed by NM, 4-Jan-2013.)
       (Proof shortened by Mario Carneiro, 19-Nov-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v z $.
	$d x y z A $.
	$d x z B $.
	$d x z C $.
	$d x z ph $.
	ireusv2_0 $f set z $.
	freusv2_0 $f wff ph $.
	freusv2_1 $f set x $.
	freusv2_2 $f set y $.
	freusv2_3 $f class A $.
	freusv2_4 $f class B $.
	freusv2_5 $f class C $.
	reusv2 $p |- ( ( A. y e. B ( ph -> C e. A ) /\ E. y e. B ph ) -> ( E! x e. A E. y e. B ( ph /\ x = C ) <-> E! x e. A A. y e. B ( ph -> x = C ) ) ) $= freusv2_0 freusv2_5 freusv2_3 wcel wi freusv2_2 freusv2_4 wral freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_3 wcel ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wral freusv2_0 freusv2_2 freusv2_4 crab c0 wne freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wa freusv2_2 freusv2_4 wrex freusv2_1 freusv2_3 wreu freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wi freusv2_2 freusv2_4 wral freusv2_1 freusv2_3 wreu wb freusv2_0 freusv2_2 freusv2_4 wrex freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_3 wcel ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wral freusv2_5 freusv2_3 wcel freusv2_2 freusv2_0 freusv2_2 freusv2_4 crab wral freusv2_0 freusv2_5 freusv2_3 wcel wi freusv2_2 freusv2_4 wral freusv2_5 freusv2_3 wcel freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_3 wcel freusv2_2 ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab freusv2_0 freusv2_2 freusv2_4 nfrab1 ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab nfcv freusv2_5 freusv2_3 wcel ireusv2_0 nfv freusv2_2 freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_3 freusv2_2 ireusv2_0 sup_set_class freusv2_5 nfcsb1v nfel1 freusv2_2 sup_set_class ireusv2_0 sup_set_class wceq freusv2_5 freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_3 freusv2_2 ireusv2_0 sup_set_class freusv2_5 csbeq1a eleq1d cbvralf freusv2_5 freusv2_3 wcel freusv2_0 freusv2_5 freusv2_3 wcel wi freusv2_2 freusv2_0 freusv2_2 freusv2_4 crab freusv2_4 freusv2_2 sup_set_class freusv2_0 freusv2_2 freusv2_4 crab wcel freusv2_5 freusv2_3 wcel wi freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 wa freusv2_5 freusv2_3 wcel wi freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 freusv2_5 freusv2_3 wcel wi wi freusv2_2 sup_set_class freusv2_0 freusv2_2 freusv2_4 crab wcel freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 wa freusv2_5 freusv2_3 wcel freusv2_0 freusv2_2 freusv2_4 rabid imbi1i freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 freusv2_5 freusv2_3 wcel impexp bitri ralbii2 bitr3i freusv2_0 freusv2_2 freusv2_4 rabn0 freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_3 wcel ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wral freusv2_0 freusv2_2 freusv2_4 crab c0 wne wa freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb wceq ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wrex freusv2_1 freusv2_3 wreu freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb wceq ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wral freusv2_1 freusv2_3 wreu freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wa freusv2_2 freusv2_4 wrex freusv2_1 freusv2_3 wreu freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wi freusv2_2 freusv2_4 wral freusv2_1 freusv2_3 wreu freusv2_1 ireusv2_0 freusv2_3 freusv2_0 freusv2_2 freusv2_4 crab freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb reusv2lem5 freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb wceq ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wrex freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wa freusv2_2 freusv2_4 wrex freusv2_1 freusv2_3 freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb wceq ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wrex freusv2_1 sup_set_class freusv2_5 wceq freusv2_2 freusv2_0 freusv2_2 freusv2_4 crab wrex freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wa freusv2_2 freusv2_4 wrex freusv2_1 sup_set_class freusv2_5 wceq freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb wceq freusv2_2 ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab freusv2_0 freusv2_2 freusv2_4 nfrab1 ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab nfcv freusv2_1 sup_set_class freusv2_5 wceq ireusv2_0 nfv freusv2_2 freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_2 ireusv2_0 sup_set_class freusv2_5 nfcsb1v nfeq2 freusv2_2 sup_set_class ireusv2_0 sup_set_class wceq freusv2_5 freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csbeq1a eqeq2d cbvrexf freusv2_1 sup_set_class freusv2_5 wceq freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wa freusv2_2 freusv2_0 freusv2_2 freusv2_4 crab freusv2_4 freusv2_2 sup_set_class freusv2_0 freusv2_2 freusv2_4 crab wcel freusv2_1 sup_set_class freusv2_5 wceq wa freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 wa freusv2_1 sup_set_class freusv2_5 wceq wa freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wa wa freusv2_2 sup_set_class freusv2_0 freusv2_2 freusv2_4 crab wcel freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 wa freusv2_1 sup_set_class freusv2_5 wceq freusv2_0 freusv2_2 freusv2_4 rabid anbi1i freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq anass bitri rexbii2 bitr3i reubii freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb wceq ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wral freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wi freusv2_2 freusv2_4 wral freusv2_1 freusv2_3 freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb wceq ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab wral freusv2_1 sup_set_class freusv2_5 wceq freusv2_2 freusv2_0 freusv2_2 freusv2_4 crab wral freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wi freusv2_2 freusv2_4 wral freusv2_1 sup_set_class freusv2_5 wceq freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb wceq freusv2_2 ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab freusv2_0 freusv2_2 freusv2_4 nfrab1 ireusv2_0 freusv2_0 freusv2_2 freusv2_4 crab nfcv freusv2_1 sup_set_class freusv2_5 wceq ireusv2_0 nfv freusv2_2 freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_2 ireusv2_0 sup_set_class freusv2_5 nfcsb1v nfeq2 freusv2_2 sup_set_class ireusv2_0 sup_set_class wceq freusv2_5 freusv2_2 ireusv2_0 sup_set_class freusv2_5 csb freusv2_1 sup_set_class freusv2_2 ireusv2_0 sup_set_class freusv2_5 csbeq1a eqeq2d cbvralf freusv2_1 sup_set_class freusv2_5 wceq freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wi freusv2_2 freusv2_0 freusv2_2 freusv2_4 crab freusv2_4 freusv2_2 sup_set_class freusv2_0 freusv2_2 freusv2_4 crab wcel freusv2_1 sup_set_class freusv2_5 wceq wi freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 wa freusv2_1 sup_set_class freusv2_5 wceq wi freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq wi wi freusv2_2 sup_set_class freusv2_0 freusv2_2 freusv2_4 crab wcel freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 wa freusv2_1 sup_set_class freusv2_5 wceq freusv2_0 freusv2_2 freusv2_4 rabid imbi1i freusv2_2 sup_set_class freusv2_4 wcel freusv2_0 freusv2_1 sup_set_class freusv2_5 wceq impexp bitri ralbii2 bitr3i reubii 3bitr3g syl2anbr $.
$}
$( Two ways of expressing existential uniqueness via an indirect equality.
       (Contributed by NM, 23-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x y z B $.
	$d x z C $.
	$d x y D $.
	$d x z ph $.
	$d x y ps $.
	freusv3i_0 $f wff ph $.
	freusv3i_1 $f wff ps $.
	freusv3i_2 $f set x $.
	freusv3i_3 $f set y $.
	freusv3i_4 $f set z $.
	freusv3i_5 $f class A $.
	freusv3i_6 $f class B $.
	freusv3i_7 $f class C $.
	freusv3i_8 $f class D $.
	ereusv3i_0 $e |- ( y = z -> ( ph <-> ps ) ) $.
	ereusv3i_1 $e |- ( y = z -> C = D ) $.
	reusv3i $p |- ( E. x e. A A. y e. B ( ph -> x = C ) -> A. y e. B A. z e. B ( ( ph /\ ps ) -> C = D ) ) $= freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_3 freusv3i_6 wral freusv3i_0 freusv3i_1 wa freusv3i_7 freusv3i_8 wceq wi freusv3i_4 freusv3i_6 wral freusv3i_3 freusv3i_6 wral freusv3i_2 freusv3i_5 freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_3 freusv3i_6 wral freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi freusv3i_4 freusv3i_6 wral freusv3i_0 freusv3i_1 wa freusv3i_7 freusv3i_8 wceq wi freusv3i_4 freusv3i_6 wral freusv3i_3 freusv3i_6 wral freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_3 freusv3i_6 wral freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi freusv3i_4 freusv3i_6 wral freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi freusv3i_3 freusv3i_4 freusv3i_6 freusv3i_3 sup_set_class freusv3i_4 sup_set_class wceq freusv3i_0 freusv3i_1 freusv3i_2 sup_set_class freusv3i_7 wceq freusv3i_2 sup_set_class freusv3i_8 wceq ereusv3i_0 freusv3i_3 sup_set_class freusv3i_4 sup_set_class wceq freusv3i_7 freusv3i_8 freusv3i_2 sup_set_class ereusv3i_1 eqeq2d imbi12d cbvralv biimpi freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_3 freusv3i_6 wral freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi freusv3i_4 freusv3i_6 wral wa freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi wa freusv3i_4 freusv3i_6 wral freusv3i_3 freusv3i_6 wral freusv3i_0 freusv3i_1 wa freusv3i_7 freusv3i_8 wceq wi freusv3i_4 freusv3i_6 wral freusv3i_3 freusv3i_6 wral freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi freusv3i_3 freusv3i_4 freusv3i_6 raaanv freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi wa freusv3i_4 freusv3i_6 wral freusv3i_0 freusv3i_1 wa freusv3i_7 freusv3i_8 wceq wi freusv3i_4 freusv3i_6 wral freusv3i_3 freusv3i_6 freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi wa freusv3i_0 freusv3i_1 wa freusv3i_7 freusv3i_8 wceq wi freusv3i_4 freusv3i_6 freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq wi freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq wi wa freusv3i_0 freusv3i_1 wa freusv3i_2 sup_set_class freusv3i_7 wceq freusv3i_2 sup_set_class freusv3i_8 wceq wa freusv3i_7 freusv3i_8 wceq freusv3i_0 freusv3i_2 sup_set_class freusv3i_7 wceq freusv3i_1 freusv3i_2 sup_set_class freusv3i_8 wceq prth freusv3i_2 sup_set_class freusv3i_7 freusv3i_8 eqtr2 syl6 ralimi ralimi sylbir mpdan rexlimivw $.
$}
$( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  See ~ reusv1 for the connection to uniqueness.
       (Contributed by NM, 27-Dec-2012.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x y z B $.
	$d x z C $.
	$d x y D $.
	$d x z ph $.
	$d x y ps $.
	$d x y z A $.
	freusv3_0 $f wff ph $.
	freusv3_1 $f wff ps $.
	freusv3_2 $f set x $.
	freusv3_3 $f set y $.
	freusv3_4 $f set z $.
	freusv3_5 $f class A $.
	freusv3_6 $f class B $.
	freusv3_7 $f class C $.
	freusv3_8 $f class D $.
	ereusv3_0 $e |- ( y = z -> ( ph <-> ps ) ) $.
	ereusv3_1 $e |- ( y = z -> C = D ) $.
	reusv3 $p |- ( E. y e. B ( ph /\ C e. A ) -> ( A. y e. B A. z e. B ( ( ph /\ ps ) -> C = D ) <-> E. x e. A A. y e. B ( ph -> x = C ) ) ) $= freusv3_0 freusv3_7 freusv3_5 wcel wa freusv3_3 freusv3_6 wrex freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex freusv3_0 freusv3_7 freusv3_5 wcel wa freusv3_3 freusv3_6 wrex freusv3_1 freusv3_8 freusv3_5 wcel wa freusv3_4 freusv3_6 wrex freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex wi freusv3_0 freusv3_7 freusv3_5 wcel wa freusv3_1 freusv3_8 freusv3_5 wcel wa freusv3_3 freusv3_4 freusv3_6 freusv3_3 sup_set_class freusv3_4 sup_set_class wceq freusv3_0 freusv3_1 freusv3_7 freusv3_5 wcel freusv3_8 freusv3_5 wcel ereusv3_0 freusv3_3 sup_set_class freusv3_4 sup_set_class wceq freusv3_7 freusv3_8 freusv3_5 ereusv3_1 eleq1d anbi12d cbvrexv freusv3_1 freusv3_8 freusv3_5 wcel wa freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex wi freusv3_4 freusv3_6 freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex freusv3_4 freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_4 freusv3_6 freusv3_6 nfra2 freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex freusv3_4 nfv nfim freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 freusv3_8 freusv3_5 wcel freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex wi freusv3_8 freusv3_5 wcel freusv3_2 sup_set_class freusv3_8 wceq freusv3_2 freusv3_5 wrex freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 wa freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex wi freusv3_2 freusv3_8 freusv3_5 risset freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 wa freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_2 sup_set_class freusv3_8 wceq freusv3_2 freusv3_5 wrex freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 wa freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_2 sup_set_class freusv3_8 wceq freusv3_2 freusv3_5 wrex freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 wrex wi freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 wa freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral wa freusv3_2 sup_set_class freusv3_8 wceq freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 freusv3_5 freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 wa freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral wa freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_3 freusv3_6 wral freusv3_2 sup_set_class freusv3_8 wceq freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral wi freusv3_4 freusv3_6 wral freusv3_4 sup_set_class freusv3_6 wcel freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral wi wi freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_4 freusv3_6 wral freusv3_3 freusv3_6 wral freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral freusv3_4 freusv3_6 wral freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral wi freusv3_4 freusv3_6 wral freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_4 freusv3_6 freusv3_6 ralcom freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral wi freusv3_4 freusv3_6 freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi wi freusv3_3 freusv3_6 wral freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral wi freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi wi freusv3_3 freusv3_6 freusv3_0 freusv3_1 wa freusv3_7 freusv3_8 wceq wi freusv3_0 freusv3_1 freusv3_7 freusv3_8 wceq wi wi freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi wi freusv3_0 freusv3_1 freusv3_7 freusv3_8 wceq impexp freusv3_0 freusv3_1 freusv3_7 freusv3_8 wceq bi2.04 bitri ralbii freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 r19.21v bitri ralbii bitri freusv3_1 freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 wral wi freusv3_4 freusv3_6 rsp sylbi com3l imp31 freusv3_2 sup_set_class freusv3_8 wceq freusv3_0 freusv3_2 sup_set_class freusv3_7 wceq wi freusv3_0 freusv3_7 freusv3_8 wceq wi freusv3_3 freusv3_6 freusv3_2 sup_set_class freusv3_8 wceq freusv3_2 sup_set_class freusv3_7 wceq freusv3_7 freusv3_8 wceq freusv3_0 freusv3_2 sup_set_class freusv3_8 wceq freusv3_2 sup_set_class freusv3_7 wceq freusv3_8 freusv3_7 wceq freusv3_7 freusv3_8 wceq freusv3_2 sup_set_class freusv3_8 freusv3_7 eqeq1 freusv3_8 freusv3_7 eqcom syl6bb imbi2d ralbidv syl5ibrcom reximdv ex com23 syl5bi expimpd rexlimi sylbi freusv3_0 freusv3_1 freusv3_2 freusv3_3 freusv3_4 freusv3_5 freusv3_6 freusv3_7 freusv3_8 ereusv3_0 ereusv3_1 reusv3i impbid1 $.
$}
$( Two ways to express single-valuedness of a class expression
       ` B ( x ) ` .  (Contributed by NM, 27-Oct-2010.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x B $.
	feusv4_0 $f set x $.
	feusv4_1 $f set y $.
	feusv4_2 $f class A $.
	feusv4_3 $f class B $.
	eeusv4_0 $e |- B e. _V $.
	eusv4 $p |- ( E! x E. y e. A x = B <-> E! x A. y e. A x = B ) $= feusv4_3 cvv wcel feusv4_0 sup_set_class feusv4_3 wceq feusv4_1 feusv4_2 wrex feusv4_0 weu feusv4_0 sup_set_class feusv4_3 wceq feusv4_1 feusv4_2 wral feusv4_0 weu wb feusv4_1 feusv4_2 feusv4_0 feusv4_1 feusv4_2 feusv4_3 reusv2lem3 feusv4_3 cvv wcel feusv4_1 sup_set_class feusv4_2 wcel eeusv4_0 a1i mprg $.
$}
$( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  (Contributed by NM, 16-Dec-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x y B $.
	$d x C $.
	$d x y $.
	freusv5OLD_0 $f set x $.
	freusv5OLD_1 $f set y $.
	freusv5OLD_2 $f class A $.
	freusv5OLD_3 $f class B $.
	freusv5OLD_4 $f class C $.
	reusv5OLD $p |- ( B =/= (/) -> ( E! x e. A A. y e. B x = C <-> E. x e. A A. y e. B x = C ) ) $= freusv5OLD_3 c0 wne freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_1 freusv5OLD_3 wrex freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_0 freusv5OLD_2 wreu freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_0 freusv5OLD_2 wrex wb freusv5OLD_1 sup_set_class freusv5OLD_3 wcel freusv5OLD_1 wex freusv5OLD_1 sup_set_class freusv5OLD_3 wcel freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq wa freusv5OLD_1 wex freusv5OLD_3 c0 wne freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_1 freusv5OLD_3 wrex freusv5OLD_1 sup_set_class freusv5OLD_3 wcel freusv5OLD_1 sup_set_class freusv5OLD_3 wcel freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq wa freusv5OLD_1 freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_1 sup_set_class freusv5OLD_3 wcel freusv5OLD_1 equid biantru exbii freusv5OLD_1 freusv5OLD_3 n0 freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_1 freusv5OLD_3 df-rex 3bitr4i freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_1 freusv5OLD_3 wrex freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 sup_set_class freusv5OLD_4 wceq wi freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_0 freusv5OLD_2 wreu freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 sup_set_class freusv5OLD_4 wceq wi freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_0 freusv5OLD_2 wrex freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_0 freusv5OLD_2 wreu freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_0 freusv5OLD_2 wrex freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 freusv5OLD_1 freusv5OLD_2 freusv5OLD_3 freusv5OLD_4 reusv1 freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 sup_set_class freusv5OLD_4 wceq wi freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_0 freusv5OLD_2 freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 sup_set_class freusv5OLD_4 wceq wi freusv5OLD_1 freusv5OLD_3 freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 equid a1bi ralbii reubii freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 sup_set_class freusv5OLD_4 wceq wi freusv5OLD_1 freusv5OLD_3 wral freusv5OLD_0 freusv5OLD_2 freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 sup_set_class freusv5OLD_4 wceq wi freusv5OLD_1 freusv5OLD_3 freusv5OLD_1 sup_set_class freusv5OLD_1 sup_set_class wceq freusv5OLD_0 sup_set_class freusv5OLD_4 wceq freusv5OLD_1 equid a1bi ralbii rexbii 3bitr4g sylbi $.
$}
$( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  The converse does not hold.  Note that ` U. A = |^| A `
       means ` A ` is a singleton ( ~ uniintsn ).  (Contributed by NM,
       30-Oct-2010.)  (Proof shortened by Mario Carneiro, 24-Dec-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v z $.
	$d x y z A $.
	$d x y z B $.
	$d x z C $.
	ireusv6OLD_0 $f set z $.
	freusv6OLD_0 $f set x $.
	freusv6OLD_1 $f set y $.
	freusv6OLD_2 $f class A $.
	freusv6OLD_3 $f class B $.
	freusv6OLD_4 $f class C $.
	reusv6OLD $p |- ( ( U. A =/= |^| A \/ B =/= (/) ) -> ( E! x e. A A. y e. B x = C -> E! x e. A E. y e. B x = C ) ) $= freusv6OLD_2 cuni freusv6OLD_2 cint wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 wreu wi freusv6OLD_3 c0 wne freusv6OLD_2 cuni freusv6OLD_2 cint wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 wreu wi wi freusv6OLD_3 c0 freusv6OLD_3 c0 wceq freusv6OLD_2 cuni freusv6OLD_2 cint wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu wn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 wreu wi freusv6OLD_3 c0 wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_2 cuni freusv6OLD_2 cint freusv6OLD_3 c0 wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 c0 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_2 cuni freusv6OLD_2 cint wceq freusv6OLD_3 c0 wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 c0 wral freusv6OLD_0 freusv6OLD_2 freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 c0 raleq reubidv freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 c0 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 c0 wral wa freusv6OLD_0 weu freusv6OLD_2 cuni freusv6OLD_2 cint wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 c0 wral freusv6OLD_0 freusv6OLD_2 df-reu freusv6OLD_2 cuni freusv6OLD_2 cint wceq freusv6OLD_2 freusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 wex freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_0 weu freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 c0 wral wa freusv6OLD_0 weu freusv6OLD_0 freusv6OLD_2 uniintsn freusv6OLD_0 freusv6OLD_2 eusn freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 c0 wral wa freusv6OLD_0 freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 c0 wral freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 ral0 biantru eubii 3bitr2i bitr4i syl6bb necon3bbid freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 wreu pm2.21 syl6bir freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 wreu wi freusv6OLD_2 cuni freusv6OLD_2 cint wne freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq ireusv6OLD_0 wex freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq ireusv6OLD_0 wex freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq ireusv6OLD_0 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel wi freusv6OLD_0 freusv6OLD_2 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wss freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel wi freusv6OLD_0 freusv6OLD_2 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 freusv6OLD_3 c0 wne freusv6OLD_0 nfv freusv6OLD_0 freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 nfrab1 nfeq1 nfan freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel wi freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel freusv6OLD_1 freusv6OLD_3 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_1 freusv6OLD_3 c0 wne freusv6OLD_1 nfv freusv6OLD_1 freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_1 freusv6OLD_0 freusv6OLD_2 freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 nfra1 freusv6OLD_1 freusv6OLD_2 nfcv nfrab nfeq1 freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_1 nfv nf3an freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel freusv6OLD_1 nfv freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_1 sup_set_class freusv6OLD_3 wcel freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel wi freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_1 sup_set_class freusv6OLD_3 wcel wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class wceq freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_1 sup_set_class freusv6OLD_3 wcel wa freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_1 sup_set_class freusv6OLD_3 wcel wa ireusv6OLD_0 sup_set_class freusv6OLD_4 freusv6OLD_0 sup_set_class freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a ireusv6OLD_0 sup_set_class freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab wcel ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a ireusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class ireusv6OLD_0 vex snid freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel simp2 syl5eleqr ireusv6OLD_0 sup_set_class freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab wcel ireusv6OLD_0 sup_set_class freusv6OLD_2 wcel ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 ireusv6OLD_0 sup_set_class freusv6OLD_2 freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class freusv6OLD_4 eqeq1 ralbidv elrab simprbi syl r19.21bi eqeq2d biimprd freusv6OLD_0 ireusv6OLD_0 sup_set_class elsn syl6ibr ex rexlimd 3expia ralrimi freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 ireusv6OLD_0 sup_set_class csn rabss sylibr freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq simpr sseqtr4d freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab wss freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex wi freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 r19.2z ex adantr ss2rabdv adantr eqssd freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq simpr eqtrd ex eximdv freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 ireusv6OLD_0 freusv6OLD_2 reusn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 ireusv6OLD_0 freusv6OLD_2 reusn 3imtr4g a1d pm2.61ine freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq ireusv6OLD_0 wex freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq ireusv6OLD_0 wex freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 wreu freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq ireusv6OLD_0 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel wi freusv6OLD_0 freusv6OLD_2 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wss freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel wi freusv6OLD_0 freusv6OLD_2 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 freusv6OLD_3 c0 wne freusv6OLD_0 nfv freusv6OLD_0 freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 nfrab1 nfeq1 nfan freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel wi freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel freusv6OLD_1 freusv6OLD_3 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_1 freusv6OLD_3 c0 wne freusv6OLD_1 nfv freusv6OLD_1 freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_1 freusv6OLD_0 freusv6OLD_2 freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 nfra1 freusv6OLD_1 freusv6OLD_2 nfcv nfrab nfeq1 freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_1 nfv nf3an freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel freusv6OLD_1 nfv freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_1 sup_set_class freusv6OLD_3 wcel freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel wi freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_1 sup_set_class freusv6OLD_3 wcel wa freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class wceq freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn wcel freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_1 sup_set_class freusv6OLD_3 wcel wa freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a freusv6OLD_1 sup_set_class freusv6OLD_3 wcel wa ireusv6OLD_0 sup_set_class freusv6OLD_4 freusv6OLD_0 sup_set_class freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a ireusv6OLD_0 sup_set_class freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab wcel ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel w3a ireusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class csn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class ireusv6OLD_0 vex snid freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_0 sup_set_class freusv6OLD_2 wcel simp2 syl5eleqr ireusv6OLD_0 sup_set_class freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab wcel ireusv6OLD_0 sup_set_class freusv6OLD_2 wcel ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 ireusv6OLD_0 sup_set_class freusv6OLD_2 freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class wceq freusv6OLD_0 sup_set_class freusv6OLD_4 wceq ireusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 freusv6OLD_0 sup_set_class ireusv6OLD_0 sup_set_class freusv6OLD_4 eqeq1 ralbidv elrab simprbi syl r19.21bi eqeq2d biimprd freusv6OLD_0 ireusv6OLD_0 sup_set_class elsn syl6ibr ex rexlimd 3expia ralrimi freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 ireusv6OLD_0 sup_set_class csn rabss sylibr freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq simpr sseqtr4d freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 crab wss freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 freusv6OLD_2 freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex wi freusv6OLD_0 sup_set_class freusv6OLD_2 wcel freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 r19.2z ex adantr ss2rabdv adantr eqssd freusv6OLD_3 c0 wne freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 freusv6OLD_2 crab ireusv6OLD_0 sup_set_class csn wceq simpr eqtrd ex eximdv freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wral freusv6OLD_0 ireusv6OLD_0 freusv6OLD_2 reusn freusv6OLD_0 sup_set_class freusv6OLD_4 wceq freusv6OLD_1 freusv6OLD_3 wrex freusv6OLD_0 ireusv6OLD_0 freusv6OLD_2 reusn 3imtr4g jaoi $.
$}
$( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  Note that ` U. A = |^| A ` means ` A ` is a singleton
       ( ~ uniintsn ).  (Contributed by NM, 14-Dec-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y A $.
	$d x y B $.
	$d x C $.
	freusv7OLD_0 $f set x $.
	freusv7OLD_1 $f set y $.
	freusv7OLD_2 $f class A $.
	freusv7OLD_3 $f class B $.
	freusv7OLD_4 $f class C $.
	ereusv7OLD_0 $e |- ( y e. B -> C e. A ) $.
	reusv7OLD $p |- ( ( U. A =/= |^| A \/ B =/= (/) ) -> ( E! x e. A E. y e. B x = C <-> E! x e. A A. y e. B x = C ) ) $= freusv7OLD_2 cuni freusv7OLD_2 cint wne freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu wb freusv7OLD_3 c0 wne freusv7OLD_2 cuni freusv7OLD_2 cint wne freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu wb wi freusv7OLD_3 c0 freusv7OLD_3 c0 wceq freusv7OLD_2 cuni freusv7OLD_2 cint wne freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu wn freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu wn wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu wb freusv7OLD_3 c0 wceq freusv7OLD_2 cuni freusv7OLD_2 cint wne freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu wn freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu wn freusv7OLD_3 c0 wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu wn freusv7OLD_2 cuni freusv7OLD_2 cint wne freusv7OLD_3 c0 wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_2 cuni freusv7OLD_2 cint freusv7OLD_3 c0 wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 c0 wral freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_2 cuni freusv7OLD_2 cint wceq freusv7OLD_3 c0 wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 c0 wral freusv7OLD_0 freusv7OLD_2 freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 c0 raleq reubidv freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 c0 wral freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 c0 wral wa freusv7OLD_0 weu freusv7OLD_2 cuni freusv7OLD_2 cint wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 c0 wral freusv7OLD_0 freusv7OLD_2 df-reu freusv7OLD_2 cuni freusv7OLD_2 cint wceq freusv7OLD_2 freusv7OLD_0 sup_set_class csn wceq freusv7OLD_0 wex freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 weu freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 c0 wral wa freusv7OLD_0 weu freusv7OLD_0 freusv7OLD_2 uniintsn freusv7OLD_0 freusv7OLD_2 eusn freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 c0 wral wa freusv7OLD_0 freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 c0 wral freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 ral0 biantru eubii 3bitr2i bitr4i syl6bb necon3bbid biimprd freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_3 c0 freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wrex freusv7OLD_3 c0 wne freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 reurex freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_3 c0 wne freusv7OLD_0 freusv7OLD_2 freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 rexn0 rexlimivw syl necon2bi jctild freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu pm5.21 syl6 freusv7OLD_3 c0 wne freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu wb freusv7OLD_2 cuni freusv7OLD_2 cint wne freusv7OLD_3 c0 wne freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 weu freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral wa freusv7OLD_0 weu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_3 c0 wne freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral wa freusv7OLD_0 freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 r19.28zv eubidv freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 weu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 weu freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 freusv7OLD_1 freusv7OLD_2 freusv7OLD_3 freusv7OLD_4 reusv2lem4 freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 equid biantrur rexbii reubii freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 freusv7OLD_3 freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq ereusv7OLD_0 biantrurd freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 freusv7OLD_2 eleq1 pm5.32ri syl6rbbr freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi wb ereusv7OLD_0 freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq biimt syl bitrd freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 equid biantru imbi1i syl6bb ralbiia eubii 3bitr4i freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 df-reu 3bitr4g a1d pm2.61ine freusv7OLD_3 c0 wne freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 weu freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral wa freusv7OLD_0 weu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_3 c0 wne freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral wa freusv7OLD_0 freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 r19.28zv eubidv freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 weu freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 wreu freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 weu freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 freusv7OLD_1 freusv7OLD_2 freusv7OLD_3 freusv7OLD_4 reusv2lem4 freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wrex freusv7OLD_0 freusv7OLD_2 freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 equid biantrur rexbii reubii freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 freusv7OLD_3 freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wa freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq ereusv7OLD_0 biantrurd freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_0 sup_set_class freusv7OLD_2 wcel freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 freusv7OLD_2 eleq1 pm5.32ri syl6rbbr freusv7OLD_1 sup_set_class freusv7OLD_3 wcel freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq wi wb ereusv7OLD_0 freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_0 sup_set_class freusv7OLD_4 wceq biimt syl bitrd freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq wa freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 sup_set_class freusv7OLD_1 sup_set_class wceq freusv7OLD_4 freusv7OLD_2 wcel freusv7OLD_1 equid biantru imbi1i syl6bb ralbiia eubii 3bitr4i freusv7OLD_0 sup_set_class freusv7OLD_4 wceq freusv7OLD_1 freusv7OLD_3 wral freusv7OLD_0 freusv7OLD_2 df-reu 3bitr4g jaoi $.
$}
$( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       18-Feb-2007.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x A $.
	$d y ph $.
	$d x ps $.
	$d x y $.
	falxfr_0 $f wff ph $.
	falxfr_1 $f wff ps $.
	falxfr_2 $f set x $.
	falxfr_3 $f set y $.
	falxfr_4 $f class A $.
	falxfr_5 $f class B $.
	ealxfr_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	alxfr $p |- ( ( A. y A e. B /\ A. x E. y x = A ) -> ( A. x ph <-> A. y ps ) ) $= falxfr_4 falxfr_5 wcel falxfr_3 wal falxfr_2 sup_set_class falxfr_4 wceq falxfr_3 wex falxfr_2 wal wa falxfr_0 falxfr_2 wal falxfr_1 falxfr_3 wal falxfr_4 falxfr_5 wcel falxfr_3 wal falxfr_0 falxfr_2 wal falxfr_1 falxfr_3 wal wi falxfr_2 sup_set_class falxfr_4 wceq falxfr_3 wex falxfr_2 wal falxfr_0 falxfr_2 wal falxfr_4 falxfr_5 wcel falxfr_3 wal falxfr_1 falxfr_3 wal falxfr_0 falxfr_2 wal falxfr_4 falxfr_5 wcel falxfr_1 falxfr_3 falxfr_4 falxfr_5 wcel falxfr_0 falxfr_2 wal falxfr_1 falxfr_0 falxfr_1 falxfr_2 falxfr_4 falxfr_5 ealxfr_0 spcgv com12 alimdv com12 adantr falxfr_2 sup_set_class falxfr_4 wceq falxfr_3 wex falxfr_2 wal falxfr_1 falxfr_3 wal falxfr_0 falxfr_2 wal wi falxfr_4 falxfr_5 wcel falxfr_3 wal falxfr_1 falxfr_3 wal falxfr_2 sup_set_class falxfr_4 wceq falxfr_3 wex falxfr_2 wal falxfr_0 falxfr_2 wal falxfr_1 falxfr_3 wal falxfr_2 sup_set_class falxfr_4 wceq falxfr_3 wex falxfr_0 falxfr_2 falxfr_1 falxfr_3 wal falxfr_2 sup_set_class falxfr_4 wceq falxfr_0 falxfr_3 falxfr_1 falxfr_3 nfa1 falxfr_0 falxfr_3 nfv falxfr_1 falxfr_3 wal falxfr_0 falxfr_2 sup_set_class falxfr_4 wceq falxfr_1 falxfr_1 falxfr_3 sp ealxfr_0 syl5ibrcom exlimd alimdv com12 adantl impbid $.
$}
$( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       15-Aug-2014.)  (Proof shortened by Mario Carneiro, 19-Nov-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x y B $.
	$d x C $.
	$d x ch $.
	$d x y ph $.
	$d y ps $.
	fralxfrd_0 $f wff ph $.
	fralxfrd_1 $f wff ps $.
	fralxfrd_2 $f wff ch $.
	fralxfrd_3 $f set x $.
	fralxfrd_4 $f set y $.
	fralxfrd_5 $f class A $.
	fralxfrd_6 $f class B $.
	fralxfrd_7 $f class C $.
	eralxfrd_0 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
	eralxfrd_1 $e |- ( ( ph /\ x e. B ) -> E. y e. C x = A ) $.
	eralxfrd_2 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	ralxfrd $p |- ( ph -> ( A. x e. B ps <-> A. y e. C ch ) ) $= fralxfrd_0 fralxfrd_1 fralxfrd_3 fralxfrd_6 wral fralxfrd_2 fralxfrd_4 fralxfrd_7 wral fralxfrd_0 fralxfrd_1 fralxfrd_3 fralxfrd_6 wral fralxfrd_2 fralxfrd_4 fralxfrd_7 fralxfrd_0 fralxfrd_4 sup_set_class fralxfrd_7 wcel wa fralxfrd_1 fralxfrd_2 fralxfrd_3 fralxfrd_5 fralxfrd_6 eralxfrd_0 fralxfrd_0 fralxfrd_3 sup_set_class fralxfrd_5 wceq fralxfrd_1 fralxfrd_2 wb fralxfrd_4 sup_set_class fralxfrd_7 wcel eralxfrd_2 adantlr rspcdv ralrimdva fralxfrd_0 fralxfrd_2 fralxfrd_4 fralxfrd_7 wral fralxfrd_1 fralxfrd_3 fralxfrd_6 fralxfrd_0 fralxfrd_3 sup_set_class fralxfrd_6 wcel wa fralxfrd_2 fralxfrd_4 fralxfrd_7 wral fralxfrd_3 sup_set_class fralxfrd_5 wceq fralxfrd_4 fralxfrd_7 wrex fralxfrd_1 eralxfrd_1 fralxfrd_2 fralxfrd_4 fralxfrd_7 wral fralxfrd_3 sup_set_class fralxfrd_5 wceq fralxfrd_4 fralxfrd_7 wrex wa fralxfrd_2 fralxfrd_3 sup_set_class fralxfrd_5 wceq wa fralxfrd_4 fralxfrd_7 wrex fralxfrd_0 fralxfrd_3 sup_set_class fralxfrd_6 wcel wa fralxfrd_1 fralxfrd_2 fralxfrd_3 sup_set_class fralxfrd_5 wceq fralxfrd_4 fralxfrd_7 r19.29 fralxfrd_0 fralxfrd_3 sup_set_class fralxfrd_6 wcel wa fralxfrd_2 fralxfrd_3 sup_set_class fralxfrd_5 wceq wa fralxfrd_1 fralxfrd_4 fralxfrd_7 fralxfrd_0 fralxfrd_2 fralxfrd_3 sup_set_class fralxfrd_5 wceq wa fralxfrd_1 wi fralxfrd_3 sup_set_class fralxfrd_6 wcel fralxfrd_4 sup_set_class fralxfrd_7 wcel fralxfrd_0 fralxfrd_3 sup_set_class fralxfrd_5 wceq fralxfrd_2 fralxfrd_1 fralxfrd_0 fralxfrd_3 sup_set_class fralxfrd_5 wceq fralxfrd_2 fralxfrd_1 fralxfrd_0 fralxfrd_3 sup_set_class fralxfrd_5 wceq wa fralxfrd_1 fralxfrd_2 eralxfrd_2 biimprd expimpd ancomsd ad2antrr rexlimdva syl5 mpan2d ralrimdva impbid $.
$}
$( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by FL,
       10-Apr-2007.)  (Revised by Mario Carneiro, 15-Aug-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x y B $.
	$d x C $.
	$d x ch $.
	$d x y ph $.
	$d y ps $.
	frexxfrd_0 $f wff ph $.
	frexxfrd_1 $f wff ps $.
	frexxfrd_2 $f wff ch $.
	frexxfrd_3 $f set x $.
	frexxfrd_4 $f set y $.
	frexxfrd_5 $f class A $.
	frexxfrd_6 $f class B $.
	frexxfrd_7 $f class C $.
	erexxfrd_0 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
	erexxfrd_1 $e |- ( ( ph /\ x e. B ) -> E. y e. C x = A ) $.
	erexxfrd_2 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	rexxfrd $p |- ( ph -> ( E. x e. B ps <-> E. y e. C ch ) ) $= frexxfrd_0 frexxfrd_1 wn frexxfrd_3 frexxfrd_6 wral wn frexxfrd_2 wn frexxfrd_4 frexxfrd_7 wral wn frexxfrd_1 frexxfrd_3 frexxfrd_6 wrex frexxfrd_2 frexxfrd_4 frexxfrd_7 wrex frexxfrd_0 frexxfrd_1 wn frexxfrd_3 frexxfrd_6 wral frexxfrd_2 wn frexxfrd_4 frexxfrd_7 wral frexxfrd_0 frexxfrd_1 wn frexxfrd_2 wn frexxfrd_3 frexxfrd_4 frexxfrd_5 frexxfrd_6 frexxfrd_7 erexxfrd_0 erexxfrd_1 frexxfrd_0 frexxfrd_3 sup_set_class frexxfrd_5 wceq wa frexxfrd_1 frexxfrd_2 erexxfrd_2 notbid ralxfrd notbid frexxfrd_1 frexxfrd_3 frexxfrd_6 dfrex2 frexxfrd_2 frexxfrd_4 frexxfrd_7 dfrex2 3bitr4g $.
$}
$( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by Mario
       Carneiro, 20-Aug-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x A $.
	$d x y B $.
	$d x C $.
	$d x ch $.
	$d x y ph $.
	$d y ps $.
	fralxfr2d_0 $f wff ph $.
	fralxfr2d_1 $f wff ps $.
	fralxfr2d_2 $f wff ch $.
	fralxfr2d_3 $f set x $.
	fralxfr2d_4 $f set y $.
	fralxfr2d_5 $f class A $.
	fralxfr2d_6 $f class B $.
	fralxfr2d_7 $f class C $.
	fralxfr2d_8 $f class V $.
	eralxfr2d_0 $e |- ( ( ph /\ y e. C ) -> A e. V ) $.
	eralxfr2d_1 $e |- ( ph -> ( x e. B <-> E. y e. C x = A ) ) $.
	eralxfr2d_2 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	ralxfr2d $p |- ( ph -> ( A. x e. B ps <-> A. y e. C ch ) ) $= fralxfr2d_0 fralxfr2d_1 fralxfr2d_2 fralxfr2d_3 fralxfr2d_4 fralxfr2d_5 fralxfr2d_6 fralxfr2d_7 fralxfr2d_0 fralxfr2d_4 sup_set_class fralxfr2d_7 wcel wa fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_3 wex fralxfr2d_5 fralxfr2d_6 wcel fralxfr2d_0 fralxfr2d_4 sup_set_class fralxfr2d_7 wcel wa fralxfr2d_5 fralxfr2d_8 wcel fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_3 wex eralxfr2d_0 fralxfr2d_3 fralxfr2d_5 fralxfr2d_8 elisset syl fralxfr2d_0 fralxfr2d_4 sup_set_class fralxfr2d_7 wcel wa fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_5 fralxfr2d_6 wcel fralxfr2d_3 fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_3 sup_set_class fralxfr2d_6 wcel fralxfr2d_5 fralxfr2d_6 wcel fralxfr2d_0 fralxfr2d_4 sup_set_class fralxfr2d_7 wcel wa fralxfr2d_0 fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_3 sup_set_class fralxfr2d_6 wcel wi fralxfr2d_4 fralxfr2d_7 fralxfr2d_0 fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_4 fralxfr2d_7 wrex fralxfr2d_3 sup_set_class fralxfr2d_6 wcel wi fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_3 sup_set_class fralxfr2d_6 wcel wi fralxfr2d_4 fralxfr2d_7 wral fralxfr2d_0 fralxfr2d_3 sup_set_class fralxfr2d_6 wcel fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_4 fralxfr2d_7 wrex eralxfr2d_1 biimprd fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_3 sup_set_class fralxfr2d_6 wcel fralxfr2d_4 fralxfr2d_7 r19.23v sylibr r19.21bi fralxfr2d_3 sup_set_class fralxfr2d_5 fralxfr2d_6 eleq1 mpbidi exlimdv mpd fralxfr2d_0 fralxfr2d_3 sup_set_class fralxfr2d_6 wcel fralxfr2d_3 sup_set_class fralxfr2d_5 wceq fralxfr2d_4 fralxfr2d_7 wrex eralxfr2d_1 biimpa eralxfr2d_2 ralxfrd $.
$}
$( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by Mario
       Carneiro, 20-Aug-2014.)  (Proof shortened by Mario Carneiro,
       19-Nov-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x A $.
	$d x y B $.
	$d x C $.
	$d x ch $.
	$d x y ph $.
	$d y ps $.
	frexxfr2d_0 $f wff ph $.
	frexxfr2d_1 $f wff ps $.
	frexxfr2d_2 $f wff ch $.
	frexxfr2d_3 $f set x $.
	frexxfr2d_4 $f set y $.
	frexxfr2d_5 $f class A $.
	frexxfr2d_6 $f class B $.
	frexxfr2d_7 $f class C $.
	frexxfr2d_8 $f class V $.
	erexxfr2d_0 $e |- ( ( ph /\ y e. C ) -> A e. V ) $.
	erexxfr2d_1 $e |- ( ph -> ( x e. B <-> E. y e. C x = A ) ) $.
	erexxfr2d_2 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
	rexxfr2d $p |- ( ph -> ( E. x e. B ps <-> E. y e. C ch ) ) $= frexxfr2d_0 frexxfr2d_1 wn frexxfr2d_3 frexxfr2d_6 wral wn frexxfr2d_2 wn frexxfr2d_4 frexxfr2d_7 wral wn frexxfr2d_1 frexxfr2d_3 frexxfr2d_6 wrex frexxfr2d_2 frexxfr2d_4 frexxfr2d_7 wrex frexxfr2d_0 frexxfr2d_1 wn frexxfr2d_3 frexxfr2d_6 wral frexxfr2d_2 wn frexxfr2d_4 frexxfr2d_7 wral frexxfr2d_0 frexxfr2d_1 wn frexxfr2d_2 wn frexxfr2d_3 frexxfr2d_4 frexxfr2d_5 frexxfr2d_6 frexxfr2d_7 frexxfr2d_8 erexxfr2d_0 erexxfr2d_1 frexxfr2d_0 frexxfr2d_3 sup_set_class frexxfr2d_5 wceq wa frexxfr2d_1 frexxfr2d_2 erexxfr2d_2 notbid ralxfr2d notbid frexxfr2d_1 frexxfr2d_3 frexxfr2d_6 dfrex2 frexxfr2d_2 frexxfr2d_4 frexxfr2d_7 dfrex2 3bitr4g $.
$}
$( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       10-Jun-2005.)  (Revised by Mario Carneiro, 15-Aug-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x ps $.
	$d y ph $.
	$d x A $.
	$d x y B $.
	$d x C $.
	fralxfr_0 $f wff ph $.
	fralxfr_1 $f wff ps $.
	fralxfr_2 $f set x $.
	fralxfr_3 $f set y $.
	fralxfr_4 $f class A $.
	fralxfr_5 $f class B $.
	fralxfr_6 $f class C $.
	eralxfr_0 $e |- ( y e. C -> A e. B ) $.
	eralxfr_1 $e |- ( x e. B -> E. y e. C x = A ) $.
	eralxfr_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ralxfr $p |- ( A. x e. B ph <-> A. y e. C ps ) $= fralxfr_0 fralxfr_2 fralxfr_5 wral fralxfr_1 fralxfr_3 fralxfr_6 wral wb wtru fralxfr_0 fralxfr_1 fralxfr_2 fralxfr_3 fralxfr_4 fralxfr_5 fralxfr_6 fralxfr_3 sup_set_class fralxfr_6 wcel fralxfr_4 fralxfr_5 wcel wtru eralxfr_0 adantl fralxfr_2 sup_set_class fralxfr_5 wcel fralxfr_2 sup_set_class fralxfr_4 wceq fralxfr_3 fralxfr_6 wrex wtru eralxfr_1 adantl fralxfr_2 sup_set_class fralxfr_4 wceq fralxfr_0 fralxfr_1 wb wtru eralxfr_2 adantl ralxfrd trud $.
$}
$( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  This proof does not use
       ~ ralxfrd .  (Contributed by NM, 10-Jun-2005.)  (Revised by Mario
       Carneiro, 15-Aug-2014.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x ps $.
	$d y ph $.
	$d x A $.
	$d x y B $.
	$d x C $.
	fralxfrALT_0 $f wff ph $.
	fralxfrALT_1 $f wff ps $.
	fralxfrALT_2 $f set x $.
	fralxfrALT_3 $f set y $.
	fralxfrALT_4 $f class A $.
	fralxfrALT_5 $f class B $.
	fralxfrALT_6 $f class C $.
	eralxfrALT_0 $e |- ( y e. C -> A e. B ) $.
	eralxfrALT_1 $e |- ( x e. B -> E. y e. C x = A ) $.
	eralxfrALT_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ralxfrALT $p |- ( A. x e. B ph <-> A. y e. C ps ) $= fralxfrALT_0 fralxfrALT_2 fralxfrALT_5 wral fralxfrALT_1 fralxfrALT_3 fralxfrALT_6 wral fralxfrALT_0 fralxfrALT_2 fralxfrALT_5 wral fralxfrALT_1 fralxfrALT_3 fralxfrALT_6 fralxfrALT_3 sup_set_class fralxfrALT_6 wcel fralxfrALT_0 fralxfrALT_2 fralxfrALT_5 wral fralxfrALT_1 fralxfrALT_3 sup_set_class fralxfrALT_6 wcel fralxfrALT_4 fralxfrALT_5 wcel fralxfrALT_0 fralxfrALT_2 fralxfrALT_5 wral fralxfrALT_1 wi eralxfrALT_0 fralxfrALT_0 fralxfrALT_1 fralxfrALT_2 fralxfrALT_4 fralxfrALT_5 eralxfrALT_2 rspcv syl com12 ralrimiv fralxfrALT_1 fralxfrALT_3 fralxfrALT_6 wral fralxfrALT_0 fralxfrALT_2 fralxfrALT_5 fralxfrALT_2 sup_set_class fralxfrALT_5 wcel fralxfrALT_2 sup_set_class fralxfrALT_4 wceq fralxfrALT_3 fralxfrALT_6 wrex fralxfrALT_1 fralxfrALT_3 fralxfrALT_6 wral fralxfrALT_0 eralxfrALT_1 fralxfrALT_1 fralxfrALT_3 fralxfrALT_6 wral fralxfrALT_2 sup_set_class fralxfrALT_4 wceq fralxfrALT_0 fralxfrALT_3 fralxfrALT_6 fralxfrALT_1 fralxfrALT_3 fralxfrALT_6 nfra1 fralxfrALT_0 fralxfrALT_3 nfv fralxfrALT_1 fralxfrALT_3 fralxfrALT_6 wral fralxfrALT_3 sup_set_class fralxfrALT_6 wcel fralxfrALT_1 fralxfrALT_2 sup_set_class fralxfrALT_4 wceq fralxfrALT_0 wi fralxfrALT_1 fralxfrALT_3 fralxfrALT_6 rsp fralxfrALT_2 sup_set_class fralxfrALT_4 wceq fralxfrALT_0 fralxfrALT_1 eralxfrALT_2 biimprcd syl6 rexlimd syl5 ralrimiv impbii $.
$}
$( Transfer existence from a variable ` x ` to another variable ` y `
       contained in expression ` A ` .  (Contributed by NM, 10-Jun-2005.)
       (Revised by Mario Carneiro, 15-Aug-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x ps $.
	$d y ph $.
	$d x A $.
	$d x y B $.
	$d x C $.
	frexxfr_0 $f wff ph $.
	frexxfr_1 $f wff ps $.
	frexxfr_2 $f set x $.
	frexxfr_3 $f set y $.
	frexxfr_4 $f class A $.
	frexxfr_5 $f class B $.
	frexxfr_6 $f class C $.
	erexxfr_0 $e |- ( y e. C -> A e. B ) $.
	erexxfr_1 $e |- ( x e. B -> E. y e. C x = A ) $.
	erexxfr_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rexxfr $p |- ( E. x e. B ph <-> E. y e. C ps ) $= frexxfr_0 frexxfr_2 frexxfr_5 wrex frexxfr_0 wn frexxfr_2 frexxfr_5 wral wn frexxfr_1 frexxfr_3 frexxfr_6 wrex frexxfr_0 frexxfr_2 frexxfr_5 dfrex2 frexxfr_1 frexxfr_3 frexxfr_6 wrex frexxfr_1 wn frexxfr_3 frexxfr_6 wral frexxfr_0 wn frexxfr_2 frexxfr_5 wral frexxfr_1 frexxfr_3 frexxfr_6 dfrex2 frexxfr_0 wn frexxfr_1 wn frexxfr_2 frexxfr_3 frexxfr_4 frexxfr_5 frexxfr_6 erexxfr_0 erexxfr_1 frexxfr_2 sup_set_class frexxfr_4 wceq frexxfr_0 frexxfr_1 erexxfr_2 notbid ralxfr xchbinxr bitr4i $.
$}
$( Class builder membership after substituting an expression ` A `
       (containing ` y ` ) for ` x ` in the class expression ` ch ` .
       (Contributed by NM, 16-Jan-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x A $.
	$d x y D $.
	$d y ph $.
	$d y ps $.
	$d x ch $.
	frabxfrd_0 $f wff ph $.
	frabxfrd_1 $f wff ps $.
	frabxfrd_2 $f wff ch $.
	frabxfrd_3 $f set x $.
	frabxfrd_4 $f set y $.
	frabxfrd_5 $f class A $.
	frabxfrd_6 $f class B $.
	frabxfrd_7 $f class C $.
	frabxfrd_8 $f class D $.
	erabxfrd_0 $e |- F/_ y B $.
	erabxfrd_1 $e |- F/_ y C $.
	erabxfrd_2 $e |- ( ( ph /\ y e. D ) -> A e. D ) $.
	erabxfrd_3 $e |- ( x = A -> ( ps <-> ch ) ) $.
	erabxfrd_4 $e |- ( y = B -> A = C ) $.
	rabxfrd $p |- ( ( ph /\ B e. D ) -> ( C e. { x e. D | ps } <-> B e. { y e. D | ch } ) ) $= frabxfrd_0 frabxfrd_6 frabxfrd_8 wcel frabxfrd_7 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_6 frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel wb frabxfrd_0 frabxfrd_6 frabxfrd_8 wcel frabxfrd_7 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel wa frabxfrd_6 frabxfrd_8 wcel frabxfrd_6 frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel wa wb frabxfrd_6 frabxfrd_8 wcel frabxfrd_7 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_6 frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel wb wi frabxfrd_0 frabxfrd_6 frabxfrd_5 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_4 frabxfrd_8 crab wcel frabxfrd_6 frabxfrd_4 sup_set_class frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel frabxfrd_4 frabxfrd_8 crab wcel frabxfrd_6 frabxfrd_8 wcel frabxfrd_7 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel wa frabxfrd_6 frabxfrd_8 wcel frabxfrd_6 frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel wa frabxfrd_0 frabxfrd_5 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_4 frabxfrd_8 crab frabxfrd_4 sup_set_class frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel frabxfrd_4 frabxfrd_8 crab frabxfrd_6 frabxfrd_0 frabxfrd_5 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_4 sup_set_class frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel frabxfrd_4 frabxfrd_8 frabxfrd_0 frabxfrd_4 sup_set_class frabxfrd_8 wcel wa frabxfrd_5 frabxfrd_8 wcel frabxfrd_2 wa frabxfrd_4 sup_set_class frabxfrd_8 wcel frabxfrd_2 wa frabxfrd_5 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_4 sup_set_class frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel frabxfrd_0 frabxfrd_4 sup_set_class frabxfrd_8 wcel wa frabxfrd_5 frabxfrd_8 wcel frabxfrd_4 sup_set_class frabxfrd_8 wcel frabxfrd_2 frabxfrd_0 frabxfrd_4 sup_set_class frabxfrd_8 wcel frabxfrd_5 frabxfrd_8 wcel frabxfrd_4 sup_set_class frabxfrd_8 wcel wb frabxfrd_0 frabxfrd_4 sup_set_class frabxfrd_8 wcel frabxfrd_5 frabxfrd_8 wcel wi frabxfrd_4 sup_set_class frabxfrd_8 wcel frabxfrd_5 frabxfrd_8 wcel frabxfrd_4 sup_set_class frabxfrd_8 wcel wb wi frabxfrd_0 frabxfrd_4 sup_set_class frabxfrd_8 wcel frabxfrd_5 frabxfrd_8 wcel erabxfrd_2 ex frabxfrd_4 sup_set_class frabxfrd_8 wcel frabxfrd_5 frabxfrd_8 wcel ibibr sylib imp anbi1d frabxfrd_1 frabxfrd_2 frabxfrd_3 frabxfrd_5 frabxfrd_8 erabxfrd_3 elrab frabxfrd_2 frabxfrd_4 frabxfrd_8 rabid 3bitr4g rabbidva eleq2d frabxfrd_5 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_7 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_4 frabxfrd_6 frabxfrd_8 erabxfrd_0 frabxfrd_4 frabxfrd_8 nfcv frabxfrd_4 frabxfrd_7 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab erabxfrd_1 nfel1 frabxfrd_4 sup_set_class frabxfrd_6 wceq frabxfrd_5 frabxfrd_7 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab erabxfrd_4 eleq1d elrabf frabxfrd_4 sup_set_class frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel frabxfrd_6 frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel frabxfrd_4 frabxfrd_6 frabxfrd_8 erabxfrd_0 frabxfrd_4 frabxfrd_8 nfcv frabxfrd_4 frabxfrd_6 frabxfrd_2 frabxfrd_4 frabxfrd_8 crab erabxfrd_0 frabxfrd_2 frabxfrd_4 frabxfrd_8 nfrab1 nfel frabxfrd_4 sup_set_class frabxfrd_6 frabxfrd_2 frabxfrd_4 frabxfrd_8 crab eleq1 elrabf 3bitr3g frabxfrd_6 frabxfrd_8 wcel frabxfrd_7 frabxfrd_1 frabxfrd_3 frabxfrd_8 crab wcel frabxfrd_6 frabxfrd_2 frabxfrd_4 frabxfrd_8 crab wcel pm5.32 sylibr imp $.
$}
$( Class builder membership after substituting an expression ` A `
       (containing ` y ` ) for ` x ` in the class expression ` ph ` .
       (Contributed by NM, 10-Jun-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x A $.
	$d x y D $.
	$d y ph $.
	$d x ps $.
	frabxfr_0 $f wff ph $.
	frabxfr_1 $f wff ps $.
	frabxfr_2 $f set x $.
	frabxfr_3 $f set y $.
	frabxfr_4 $f class A $.
	frabxfr_5 $f class B $.
	frabxfr_6 $f class C $.
	frabxfr_7 $f class D $.
	erabxfr_0 $e |- F/_ y B $.
	erabxfr_1 $e |- F/_ y C $.
	erabxfr_2 $e |- ( y e. D -> A e. D ) $.
	erabxfr_3 $e |- ( x = A -> ( ph <-> ps ) ) $.
	erabxfr_4 $e |- ( y = B -> A = C ) $.
	rabxfr $p |- ( B e. D -> ( C e. { x e. D | ph } <-> B e. { y e. D | ps } ) ) $= wtru frabxfr_5 frabxfr_7 wcel frabxfr_6 frabxfr_0 frabxfr_2 frabxfr_7 crab wcel frabxfr_5 frabxfr_1 frabxfr_3 frabxfr_7 crab wcel wb tru wtru frabxfr_0 frabxfr_1 frabxfr_2 frabxfr_3 frabxfr_4 frabxfr_5 frabxfr_6 frabxfr_7 erabxfr_0 erabxfr_1 frabxfr_3 sup_set_class frabxfr_7 wcel frabxfr_4 frabxfr_7 wcel wtru erabxfr_2 adantl erabxfr_3 erabxfr_4 rabxfrd mpan $.
$}
$( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       16-Jan-2012.)  (Revised by NM, 16-Jun-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y ph $.
	$d x ps $.
	$d x A $.
	$d x y B $.
	freuxfr2d_0 $f wff ph $.
	freuxfr2d_1 $f wff ps $.
	freuxfr2d_2 $f set x $.
	freuxfr2d_3 $f set y $.
	freuxfr2d_4 $f class A $.
	freuxfr2d_5 $f class B $.
	ereuxfr2d_0 $e |- ( ( ph /\ y e. B ) -> A e. B ) $.
	ereuxfr2d_1 $e |- ( ( ph /\ x e. B ) -> E* y e. B x = A ) $.
	reuxfr2d $p |- ( ph -> ( E! x e. B E. y e. B ( x = A /\ ps ) <-> E! y e. B ps ) ) $= freuxfr2d_0 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 wrex freuxfr2d_2 freuxfr2d_5 wreu freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrex freuxfr2d_3 freuxfr2d_5 wreu freuxfr2d_1 freuxfr2d_3 freuxfr2d_5 wreu freuxfr2d_0 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 wrex freuxfr2d_2 freuxfr2d_5 wreu freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrex freuxfr2d_3 freuxfr2d_5 wreu freuxfr2d_0 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 wrmo freuxfr2d_2 freuxfr2d_5 wral freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 wrex freuxfr2d_2 freuxfr2d_5 wreu freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrex freuxfr2d_3 freuxfr2d_5 wreu wi freuxfr2d_0 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 wrmo freuxfr2d_2 freuxfr2d_5 freuxfr2d_0 freuxfr2d_2 sup_set_class freuxfr2d_5 wcel wa freuxfr2d_1 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq wa freuxfr2d_3 freuxfr2d_5 wrmo freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 wrmo freuxfr2d_0 freuxfr2d_2 sup_set_class freuxfr2d_5 wcel wa freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_3 freuxfr2d_5 wrmo freuxfr2d_1 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq wa freuxfr2d_3 freuxfr2d_5 wrmo ereuxfr2d_1 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 freuxfr2d_3 freuxfr2d_5 rmoan syl freuxfr2d_1 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq wa freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 freuxfr2d_1 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq ancom rmobii sylib ralrimiva freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_3 freuxfr2d_5 freuxfr2d_5 2reuswap syl freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa wa freuxfr2d_2 wmo freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrex freuxfr2d_3 freuxfr2d_5 wreu freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 wrex freuxfr2d_2 freuxfr2d_5 wreu wi freuxfr2d_3 freuxfr2d_5 freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa wa freuxfr2d_2 wmo freuxfr2d_3 freuxfr2d_5 wral freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrmo freuxfr2d_3 freuxfr2d_5 wral freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrex freuxfr2d_3 freuxfr2d_5 wreu freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_5 wrex freuxfr2d_2 freuxfr2d_5 wreu wi freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrmo freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa wa freuxfr2d_2 wmo freuxfr2d_3 freuxfr2d_5 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 df-rmo ralbii freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_3 freuxfr2d_2 freuxfr2d_5 freuxfr2d_5 2reuswap sylbir freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa wa freuxfr2d_2 wmo freuxfr2d_3 sup_set_class freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_1 wa freuxfr2d_2 sup_set_class freuxfr2d_4 wceq wa freuxfr2d_2 wmo freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa wa freuxfr2d_2 wmo freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_2 freuxfr2d_4 moeq moani freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_1 wa freuxfr2d_2 sup_set_class freuxfr2d_4 wceq wa freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa wa freuxfr2d_2 freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_1 wa freuxfr2d_2 sup_set_class freuxfr2d_4 wceq wa freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_1 wa wa freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa wa freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_1 wa freuxfr2d_2 sup_set_class freuxfr2d_4 wceq ancom freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_2 sup_set_class freuxfr2d_5 wcel freuxfr2d_1 an12 bitri mobii mpbi a1i mprg impbid1 freuxfr2d_0 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrex freuxfr2d_1 freuxfr2d_3 freuxfr2d_5 freuxfr2d_0 freuxfr2d_3 sup_set_class freuxfr2d_5 wcel wa freuxfr2d_4 freuxfr2d_5 wcel freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 wa freuxfr2d_2 freuxfr2d_5 wrex freuxfr2d_1 wb ereuxfr2d_0 freuxfr2d_1 freuxfr2d_1 freuxfr2d_2 freuxfr2d_4 freuxfr2d_5 freuxfr2d_2 sup_set_class freuxfr2d_4 wceq freuxfr2d_1 biidd ceqsrexv syl reubidva bitrd $.
$}
$( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       14-Nov-2004.)  (Revised by NM, 16-Jun-2017.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x ph $.
	$d x A $.
	$d x y B $.
	freuxfr2_0 $f wff ph $.
	freuxfr2_1 $f set x $.
	freuxfr2_2 $f set y $.
	freuxfr2_3 $f class A $.
	freuxfr2_4 $f class B $.
	ereuxfr2_0 $e |- ( y e. B -> A e. B ) $.
	ereuxfr2_1 $e |- ( x e. B -> E* y e. B x = A ) $.
	reuxfr2 $p |- ( E! x e. B E. y e. B ( x = A /\ ph ) <-> E! y e. B ph ) $= freuxfr2_1 sup_set_class freuxfr2_3 wceq freuxfr2_0 wa freuxfr2_2 freuxfr2_4 wrex freuxfr2_1 freuxfr2_4 wreu freuxfr2_0 freuxfr2_2 freuxfr2_4 wreu wb wtru freuxfr2_0 freuxfr2_1 freuxfr2_2 freuxfr2_3 freuxfr2_4 freuxfr2_2 sup_set_class freuxfr2_4 wcel freuxfr2_3 freuxfr2_4 wcel wtru ereuxfr2_0 adantl freuxfr2_1 sup_set_class freuxfr2_4 wcel freuxfr2_1 sup_set_class freuxfr2_3 wceq freuxfr2_2 freuxfr2_4 wrmo wtru ereuxfr2_1 adantl reuxfr2d trud $.
$}
$( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Use ~ reuhypd to
       eliminate the second hypothesis.  (Contributed by NM, 16-Jan-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y ph $.
	$d y ps $.
	$d x ch $.
	$d x A $.
	$d x y B $.
	freuxfrd_0 $f wff ph $.
	freuxfrd_1 $f wff ps $.
	freuxfrd_2 $f wff ch $.
	freuxfrd_3 $f set x $.
	freuxfrd_4 $f set y $.
	freuxfrd_5 $f class A $.
	freuxfrd_6 $f class B $.
	ereuxfrd_0 $e |- ( ( ph /\ y e. B ) -> A e. B ) $.
	ereuxfrd_1 $e |- ( ( ph /\ x e. B ) -> E! y e. B x = A ) $.
	ereuxfrd_2 $e |- ( x = A -> ( ps <-> ch ) ) $.
	reuxfrd $p |- ( ph -> ( E! x e. B ps <-> E! y e. B ch ) ) $= freuxfrd_0 freuxfrd_1 freuxfrd_3 freuxfrd_6 wreu freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_2 wa freuxfrd_4 freuxfrd_6 wrex freuxfrd_3 freuxfrd_6 wreu freuxfrd_2 freuxfrd_4 freuxfrd_6 wreu freuxfrd_0 freuxfrd_1 freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_2 wa freuxfrd_4 freuxfrd_6 wrex freuxfrd_3 freuxfrd_6 freuxfrd_0 freuxfrd_3 sup_set_class freuxfrd_6 wcel wa freuxfrd_1 freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 wrex freuxfrd_1 wa freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_2 wa freuxfrd_4 freuxfrd_6 wrex freuxfrd_0 freuxfrd_3 sup_set_class freuxfrd_6 wcel wa freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 wrex freuxfrd_1 freuxfrd_0 freuxfrd_3 sup_set_class freuxfrd_6 wcel wa freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 wreu freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 wrex ereuxfrd_1 freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 reurex syl biantrurd freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 wrex freuxfrd_1 wa freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_1 wa freuxfrd_4 freuxfrd_6 wrex freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_2 wa freuxfrd_4 freuxfrd_6 wrex freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_1 freuxfrd_4 freuxfrd_6 r19.41v freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_1 wa freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_2 wa freuxfrd_4 freuxfrd_6 freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_1 freuxfrd_2 ereuxfrd_2 pm5.32i rexbii bitr3i syl6bb reubidva freuxfrd_0 freuxfrd_2 freuxfrd_3 freuxfrd_4 freuxfrd_5 freuxfrd_6 ereuxfrd_0 freuxfrd_0 freuxfrd_3 sup_set_class freuxfrd_6 wcel wa freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 wreu freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 wrmo ereuxfrd_1 freuxfrd_3 sup_set_class freuxfrd_5 wceq freuxfrd_4 freuxfrd_6 reurmo syl reuxfr2d bitrd $.
$}
$( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Use ~ reuhyp to
       eliminate the second hypothesis.  (Contributed by NM, 14-Nov-2004.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x ps $.
	$d y ph $.
	$d x A $.
	$d x y B $.
	freuxfr_0 $f wff ph $.
	freuxfr_1 $f wff ps $.
	freuxfr_2 $f set x $.
	freuxfr_3 $f set y $.
	freuxfr_4 $f class A $.
	freuxfr_5 $f class B $.
	ereuxfr_0 $e |- ( y e. B -> A e. B ) $.
	ereuxfr_1 $e |- ( x e. B -> E! y e. B x = A ) $.
	ereuxfr_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	reuxfr $p |- ( E! x e. B ph <-> E! y e. B ps ) $= freuxfr_0 freuxfr_2 freuxfr_5 wreu freuxfr_1 freuxfr_3 freuxfr_5 wreu wb wtru freuxfr_0 freuxfr_1 freuxfr_2 freuxfr_3 freuxfr_4 freuxfr_5 freuxfr_3 sup_set_class freuxfr_5 wcel freuxfr_4 freuxfr_5 wcel wtru ereuxfr_0 adantl freuxfr_2 sup_set_class freuxfr_5 wcel freuxfr_2 sup_set_class freuxfr_4 wceq freuxfr_3 freuxfr_5 wreu wtru ereuxfr_1 adantl ereuxfr_2 reuxfrd trud $.
$}
$( A theorem useful for eliminating the restricted existential uniqueness
       hypotheses in ~ riotaxfrd .  (Contributed by NM, 16-Jan-2012.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d y ph $.
	$d y B $.
	$d y C $.
	$d x y $.
	freuhypd_0 $f wff ph $.
	freuhypd_1 $f set x $.
	freuhypd_2 $f set y $.
	freuhypd_3 $f class A $.
	freuhypd_4 $f class B $.
	freuhypd_5 $f class C $.
	ereuhypd_0 $e |- ( ( ph /\ x e. C ) -> B e. C ) $.
	ereuhypd_1 $e |- ( ( ph /\ x e. C /\ y e. C ) -> ( x = A <-> y = B ) ) $.
	reuhypd $p |- ( ( ph /\ x e. C ) -> E! y e. C x = A ) $= freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_1 sup_set_class freuhypd_3 wceq wa freuhypd_2 weu freuhypd_1 sup_set_class freuhypd_3 wceq freuhypd_2 freuhypd_5 wreu freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_2 sup_set_class freuhypd_4 wceq freuhypd_2 weu freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_1 sup_set_class freuhypd_3 wceq wa freuhypd_2 weu freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_4 cvv wcel freuhypd_2 sup_set_class freuhypd_4 wceq freuhypd_2 weu freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_4 freuhypd_5 wcel freuhypd_4 cvv wcel ereuhypd_0 freuhypd_4 freuhypd_5 elex syl freuhypd_2 freuhypd_4 eueq sylib freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_2 sup_set_class freuhypd_4 wceq freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_1 sup_set_class freuhypd_3 wceq wa freuhypd_2 freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_2 sup_set_class freuhypd_4 wceq freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_2 sup_set_class freuhypd_4 wceq wa freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_1 sup_set_class freuhypd_3 wceq wa freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_2 sup_set_class freuhypd_4 wceq freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_2 sup_set_class freuhypd_4 wceq freuhypd_4 freuhypd_5 wcel ereuhypd_0 freuhypd_2 sup_set_class freuhypd_4 freuhypd_5 eleq1 syl5ibrcom pm4.71rd freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel wa freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_1 sup_set_class freuhypd_3 wceq freuhypd_2 sup_set_class freuhypd_4 wceq freuhypd_0 freuhypd_1 sup_set_class freuhypd_5 wcel freuhypd_2 sup_set_class freuhypd_5 wcel freuhypd_1 sup_set_class freuhypd_3 wceq freuhypd_2 sup_set_class freuhypd_4 wceq wb ereuhypd_1 3expa pm5.32da bitr4d eubidv mpbid freuhypd_1 sup_set_class freuhypd_3 wceq freuhypd_2 freuhypd_5 df-reu sylibr $.
$}
$( A theorem useful for eliminating the restricted existential uniqueness
       hypotheses in ~ reuxfr .  (Contributed by NM, 15-Nov-2004.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d y B $.
	$d y C $.
	$d x y $.
	freuhyp_0 $f set x $.
	freuhyp_1 $f set y $.
	freuhyp_2 $f class A $.
	freuhyp_3 $f class B $.
	freuhyp_4 $f class C $.
	ereuhyp_0 $e |- ( x e. C -> B e. C ) $.
	ereuhyp_1 $e |- ( ( x e. C /\ y e. C ) -> ( x = A <-> y = B ) ) $.
	reuhyp $p |- ( x e. C -> E! y e. C x = A ) $= wtru freuhyp_0 sup_set_class freuhyp_4 wcel freuhyp_0 sup_set_class freuhyp_2 wceq freuhyp_1 freuhyp_4 wreu tru wtru freuhyp_0 freuhyp_1 freuhyp_2 freuhyp_3 freuhyp_4 freuhyp_0 sup_set_class freuhyp_4 wcel freuhyp_3 freuhyp_4 wcel wtru ereuhyp_0 adantl freuhyp_0 sup_set_class freuhyp_4 wcel freuhyp_1 sup_set_class freuhyp_4 wcel freuhyp_0 sup_set_class freuhyp_2 wceq freuhyp_1 sup_set_class freuhyp_3 wceq wb wtru ereuhyp_1 3adant1 reuhypd mpan $.
$}
$( The Axiom of Union and its converse.  A class is a set iff its union is a
     set.  (Contributed by NM, 11-Nov-2003.) $)
${
	$v A $.
	funiexb_0 $f class A $.
	uniexb $p |- ( A e. _V <-> U. A e. _V ) $= funiexb_0 cvv wcel funiexb_0 cuni cvv wcel funiexb_0 cvv uniexg funiexb_0 cuni cvv wcel funiexb_0 funiexb_0 cuni cpw wss funiexb_0 cuni cpw cvv wcel funiexb_0 cvv wcel funiexb_0 pwuni funiexb_0 cuni cvv pwexg funiexb_0 funiexb_0 cuni cpw cvv ssexg sylancr impbii $.
$}
$( The Axiom of Power Sets and its converse.  A class is a set iff its power
     class is a set.  (Contributed by NM, 11-Nov-2003.) $)
${
	$v A $.
	fpwexb_0 $f class A $.
	pwexb $p |- ( A e. _V <-> ~P A e. _V ) $= fpwexb_0 cpw cvv wcel fpwexb_0 cpw cuni cvv wcel fpwexb_0 cvv wcel fpwexb_0 cpw uniexb fpwexb_0 cpw cuni fpwexb_0 cvv fpwexb_0 unipw eleq1i bitr2i $.
$}
$( The union of the universe is the universe.  Exercise 4.12(c) of
     [Mendelson] p. 235.  (Contributed by NM, 14-Sep-2003.) $)
${
	univ $p |- U. _V = _V $= cvv cpw cuni cvv cuni cvv cvv cpw cvv pwv unieqi cvv unipw eqtr3i $.
$}
$( Membership in a power class difference.  (Contributed by NM,
       25-Mar-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	feldifpw_0 $f class A $.
	feldifpw_1 $f class B $.
	feldifpw_2 $f class C $.
	eeldifpw_0 $e |- C e. _V $.
	eldifpw $p |- ( ( A e. ~P B /\ -. C C_ B ) -> ( A u. C ) e. ( ~P ( B u. C ) \ ~P B ) ) $= feldifpw_0 feldifpw_1 cpw wcel feldifpw_2 feldifpw_1 wss wn wa feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun cpw wcel feldifpw_0 feldifpw_2 cun feldifpw_1 cpw wcel wn wa feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun cpw feldifpw_1 cpw cdif wcel feldifpw_0 feldifpw_1 cpw wcel feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun cpw wcel feldifpw_2 feldifpw_1 wss wn feldifpw_0 feldifpw_2 cun feldifpw_1 cpw wcel wn feldifpw_0 feldifpw_1 cpw wcel feldifpw_0 feldifpw_1 wss feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun cpw wcel feldifpw_0 feldifpw_1 elpwi feldifpw_0 feldifpw_1 wss feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun cpw wcel feldifpw_0 feldifpw_1 cpw wcel feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun wss feldifpw_0 feldifpw_1 feldifpw_2 unss1 feldifpw_0 feldifpw_1 cpw wcel feldifpw_0 feldifpw_2 cun cvv wcel feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun cpw wcel feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun wss wb feldifpw_0 feldifpw_1 cpw wcel feldifpw_2 cvv wcel feldifpw_0 feldifpw_2 cun cvv wcel eeldifpw_0 feldifpw_0 feldifpw_2 feldifpw_1 cpw cvv unexg mpan2 feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun cvv elpwg syl syl5ibr mpd feldifpw_0 feldifpw_2 cun feldifpw_1 cpw wcel feldifpw_2 feldifpw_1 wss feldifpw_0 feldifpw_2 cun feldifpw_1 cpw wcel feldifpw_0 feldifpw_2 cun feldifpw_1 wss feldifpw_2 feldifpw_1 wss feldifpw_0 feldifpw_2 cun feldifpw_1 elpwi feldifpw_0 feldifpw_2 cun feldifpw_1 wss feldifpw_0 feldifpw_1 wss feldifpw_2 feldifpw_1 wss wa feldifpw_2 feldifpw_1 wss feldifpw_0 feldifpw_2 feldifpw_1 unss feldifpw_0 feldifpw_1 wss feldifpw_2 feldifpw_1 wss simpr sylbir syl con3i anim12i feldifpw_0 feldifpw_2 cun feldifpw_1 feldifpw_2 cun cpw feldifpw_1 cpw eldif sylibr $.
$}
$( Membership in the power class of a union.  (Contributed by NM,
       26-Mar-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	felpwun_0 $f class A $.
	felpwun_1 $f class B $.
	felpwun_2 $f class C $.
	eelpwun_0 $e |- C e. _V $.
	elpwun $p |- ( A e. ~P ( B u. C ) <-> ( A \ C ) e. ~P B ) $= felpwun_0 felpwun_1 felpwun_2 cun cpw wcel felpwun_0 cvv wcel felpwun_0 felpwun_2 cdif felpwun_1 cpw wcel felpwun_0 felpwun_1 felpwun_2 cun cpw elex felpwun_0 felpwun_2 cdif felpwun_1 cpw wcel felpwun_0 felpwun_2 cdif cvv wcel felpwun_0 cvv wcel felpwun_0 felpwun_2 cdif felpwun_1 cpw elex felpwun_2 cvv wcel felpwun_0 cvv wcel felpwun_0 felpwun_2 cdif cvv wcel wb eelpwun_0 felpwun_0 felpwun_2 cvv difex2 ax-mp sylibr felpwun_0 cvv wcel felpwun_0 felpwun_1 felpwun_2 cun cpw wcel felpwun_0 felpwun_1 felpwun_2 cun wss felpwun_0 felpwun_2 cdif felpwun_1 cpw wcel felpwun_0 felpwun_1 felpwun_2 cun cvv elpwg felpwun_0 cvv wcel felpwun_0 felpwun_2 cdif felpwun_1 cpw wcel felpwun_0 felpwun_2 cdif felpwun_1 wss felpwun_0 felpwun_1 felpwun_2 cun wss felpwun_0 cvv wcel felpwun_0 felpwun_2 cdif cvv wcel felpwun_0 felpwun_2 cdif felpwun_1 cpw wcel felpwun_0 felpwun_2 cdif felpwun_1 wss wb felpwun_0 felpwun_2 cvv difexg felpwun_0 felpwun_2 cdif felpwun_1 cvv elpwg syl felpwun_0 felpwun_1 felpwun_2 cun wss felpwun_0 felpwun_2 felpwun_1 cun wss felpwun_0 felpwun_2 cdif felpwun_1 wss felpwun_1 felpwun_2 cun felpwun_2 felpwun_1 cun felpwun_0 felpwun_1 felpwun_2 uncom sseq2i felpwun_0 felpwun_2 felpwun_1 ssundif bitri syl6rbbr bitrd pm5.21nii $.
$}
$( Membership in an extension of a power class.  (Contributed by NM,
       26-Mar-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v x $.
	$d x A $.
	$d x B $.
	$d x C $.
	ielpwunsn_0 $f set x $.
	felpwunsn_0 $f class A $.
	felpwunsn_1 $f class B $.
	felpwunsn_2 $f class C $.
	elpwunsn $p |- ( A e. ( ~P ( B u. { C } ) \ ~P B ) -> C e. A ) $= felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw felpwunsn_1 cpw cdif wcel felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel felpwunsn_0 felpwunsn_1 cpw wcel wn wa felpwunsn_2 felpwunsn_0 wcel felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw felpwunsn_1 cpw eldif felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel felpwunsn_0 felpwunsn_1 cpw wcel wn ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn ielpwunsn_0 felpwunsn_0 wrex felpwunsn_2 felpwunsn_0 wcel felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel felpwunsn_0 felpwunsn_1 cpw wcel wn wa ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 felpwunsn_0 wral wn ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn ielpwunsn_0 felpwunsn_0 wrex felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel felpwunsn_0 felpwunsn_1 cpw wcel wn ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 felpwunsn_0 wral wn felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel felpwunsn_0 felpwunsn_1 cpw wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 felpwunsn_0 wral felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel felpwunsn_0 felpwunsn_1 cpw wcel felpwunsn_0 felpwunsn_1 wss ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 felpwunsn_0 wral felpwunsn_0 felpwunsn_1 felpwunsn_1 felpwunsn_2 csn cun cpw elpwg ielpwunsn_0 felpwunsn_0 felpwunsn_1 dfss3 syl6bb notbid biimpa ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 felpwunsn_0 rexnal sylibr felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn ielpwunsn_0 felpwunsn_0 wrex felpwunsn_2 felpwunsn_0 wcel felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn felpwunsn_2 felpwunsn_0 wcel ielpwunsn_0 felpwunsn_0 felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn felpwunsn_2 felpwunsn_0 wcel wi felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn ielpwunsn_0 sup_set_class felpwunsn_0 wcel felpwunsn_2 felpwunsn_0 wcel felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn ielpwunsn_0 sup_set_class felpwunsn_0 wcel felpwunsn_2 felpwunsn_0 wcel wi felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn wa ielpwunsn_0 sup_set_class felpwunsn_2 wceq ielpwunsn_0 sup_set_class felpwunsn_0 wcel felpwunsn_2 felpwunsn_0 wcel wi felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun cpw wcel felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun wss ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 felpwunsn_2 csn cun wcel wi ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn wa ielpwunsn_0 sup_set_class felpwunsn_2 wceq wi felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun elpwi felpwunsn_0 felpwunsn_1 felpwunsn_2 csn cun ielpwunsn_0 sup_set_class ssel ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 felpwunsn_2 csn cun wcel wi ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn ielpwunsn_0 sup_set_class felpwunsn_2 wceq ielpwunsn_0 sup_set_class felpwunsn_1 felpwunsn_2 csn cun wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn ielpwunsn_0 sup_set_class felpwunsn_2 wceq wi ielpwunsn_0 sup_set_class felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_1 felpwunsn_2 csn cun wcel ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 sup_set_class felpwunsn_2 csn wcel wo ielpwunsn_0 sup_set_class felpwunsn_1 wcel wn ielpwunsn_0 sup_set_class felpwunsn_2 wceq wi ielpwunsn_0 sup_set_class felpwunsn_1 felpwunsn_2 csn elun ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 sup_set_class felpwunsn_2 csn wcel wo ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 sup_set_class felpwunsn_2 wceq ielpwunsn_0 sup_set_class felpwunsn_2 csn wcel ielpwunsn_0 sup_set_class felpwunsn_2 wceq ielpwunsn_0 sup_set_class felpwunsn_1 wcel ielpwunsn_0 sup_set_class felpwunsn_2 elsni orim2i ord sylbi imim2i imp3a 3syl ielpwunsn_0 sup_set_class felpwunsn_2 wceq ielpwunsn_0 sup_set_class felpwunsn_0 wcel felpwunsn_2 felpwunsn_0 wcel ielpwunsn_0 sup_set_class felpwunsn_2 felpwunsn_0 eleq1 biimpd syl6 exp3a com4r pm2.43b rexlimdv imp syldan sylbi $.
$}
$( Extract the first member of an ordered pair.  Theorem 73 of [Suppes]
       p. 42.  (See ~ op2ndb to extract the second member, ~ op1sta for an
       alternate version, and ~ op1st for the preferred version.)  (Contributed
       by NM, 25-Nov-2003.) $)
${
	$v A $.
	$v B $.
	fop1stb_0 $f class A $.
	fop1stb_1 $f class B $.
	eop1stb_0 $e |- A e. _V $.
	eop1stb_1 $e |- B e. _V $.
	op1stb $p |- |^| |^| <. A , B >. = A $= fop1stb_0 fop1stb_1 cop cint cint fop1stb_0 csn cint fop1stb_0 fop1stb_0 fop1stb_1 cop cint fop1stb_0 csn fop1stb_0 fop1stb_1 cop cint fop1stb_0 csn fop1stb_0 fop1stb_1 cpr cpr cint fop1stb_0 csn fop1stb_0 fop1stb_1 cop fop1stb_0 csn fop1stb_0 fop1stb_1 cpr cpr fop1stb_0 fop1stb_1 eop1stb_0 eop1stb_1 dfop inteqi fop1stb_0 csn fop1stb_0 fop1stb_1 cpr cpr cint fop1stb_0 csn fop1stb_0 fop1stb_1 cpr cin fop1stb_0 csn fop1stb_0 csn fop1stb_0 fop1stb_1 cpr fop1stb_0 snex fop1stb_0 fop1stb_1 prex intpr fop1stb_0 csn fop1stb_0 fop1stb_1 cpr wss fop1stb_0 csn fop1stb_0 fop1stb_1 cpr cin fop1stb_0 csn wceq fop1stb_0 fop1stb_1 snsspr1 fop1stb_0 csn fop1stb_0 fop1stb_1 cpr df-ss mpbi eqtri eqtri inteqi fop1stb_0 eop1stb_0 intsn eqtri $.
$}
$( An indexed union of a power class in terms of the power class of the
       union of its index.  Part of Exercise 24(b) of [Enderton] p. 33.
       (Contributed by NM, 29-Nov-2003.) $)
${
	$v x $.
	$v A $.
	$v y $.
	$d x y A $.
	iiunpw_0 $f set y $.
	fiunpw_0 $f set x $.
	fiunpw_1 $f class A $.
	eiunpw_0 $e |- A e. _V $.
	iunpw $p |- ( E. x e. A x = U. A <-> ~P U. A = U_ x e. A ~P x ) $= fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 fiunpw_1 wrex fiunpw_1 cuni cpw fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wceq fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 fiunpw_1 wrex iiunpw_0 fiunpw_1 cuni cpw fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 fiunpw_1 wrex iiunpw_0 sup_set_class fiunpw_1 cuni wss iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss fiunpw_0 fiunpw_1 wrex iiunpw_0 sup_set_class fiunpw_1 cuni cpw wcel iiunpw_0 sup_set_class fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wcel fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 fiunpw_1 wrex iiunpw_0 sup_set_class fiunpw_1 cuni wss iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss fiunpw_0 fiunpw_1 wrex iiunpw_0 sup_set_class fiunpw_1 cuni wss fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 fiunpw_1 wrex iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss fiunpw_0 fiunpw_1 wrex iiunpw_0 sup_set_class fiunpw_1 cuni wss fiunpw_0 sup_set_class fiunpw_1 cuni wceq iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class fiunpw_1 cuni wceq iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss iiunpw_0 sup_set_class fiunpw_1 cuni wss fiunpw_0 sup_set_class fiunpw_1 cuni iiunpw_0 sup_set_class sseq2 biimprcd reximdv com12 iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss fiunpw_0 fiunpw_1 wrex iiunpw_0 sup_set_class fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class ciun fiunpw_1 cuni fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class iiunpw_0 sup_set_class ssiun fiunpw_0 fiunpw_1 uniiun syl6sseqr impbid1 iiunpw_0 sup_set_class fiunpw_1 cuni iiunpw_0 vex elpw iiunpw_0 sup_set_class fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wcel iiunpw_0 sup_set_class fiunpw_0 sup_set_class cpw wcel fiunpw_0 fiunpw_1 wrex iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss fiunpw_0 fiunpw_1 wrex fiunpw_0 iiunpw_0 sup_set_class fiunpw_1 fiunpw_0 sup_set_class cpw eliun iiunpw_0 sup_set_class fiunpw_0 sup_set_class cpw wcel iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss fiunpw_0 fiunpw_1 iiunpw_0 sup_set_class fiunpw_0 sup_set_class wss iiunpw_0 fiunpw_0 sup_set_class cpw iiunpw_0 fiunpw_0 sup_set_class df-pw abeq2i rexbii bitri 3bitr4g eqrdv fiunpw_1 cuni cpw fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wceq fiunpw_1 cuni fiunpw_0 sup_set_class cpw wcel fiunpw_0 fiunpw_1 wrex fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 fiunpw_1 wrex fiunpw_1 cuni cpw fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wceq fiunpw_1 cuni fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wcel fiunpw_1 cuni fiunpw_0 sup_set_class cpw wcel fiunpw_0 fiunpw_1 wrex fiunpw_1 cuni cpw fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wceq fiunpw_1 cuni fiunpw_1 cuni wss fiunpw_1 cuni fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wcel fiunpw_1 cuni ssid fiunpw_1 cuni fiunpw_1 cuni wss fiunpw_1 cuni fiunpw_1 cuni cpw wcel fiunpw_1 cuni cpw fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wceq fiunpw_1 cuni fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun wcel fiunpw_1 cuni fiunpw_1 cuni fiunpw_1 eiunpw_0 uniex elpw fiunpw_1 cuni cpw fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class cpw ciun fiunpw_1 cuni eleq2 syl5bbr mpbii fiunpw_0 fiunpw_1 cuni fiunpw_1 fiunpw_0 sup_set_class cpw eliun sylib fiunpw_1 cuni fiunpw_0 sup_set_class cpw wcel fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 fiunpw_1 fiunpw_0 sup_set_class fiunpw_1 wcel fiunpw_1 cuni fiunpw_0 sup_set_class cpw wcel fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 sup_set_class fiunpw_1 wcel fiunpw_1 cuni fiunpw_0 sup_set_class cpw wcel wa fiunpw_0 sup_set_class fiunpw_1 cuni wss fiunpw_1 cuni fiunpw_0 sup_set_class wss wa fiunpw_0 sup_set_class fiunpw_1 cuni wceq fiunpw_0 sup_set_class fiunpw_1 wcel fiunpw_0 sup_set_class fiunpw_1 cuni wss fiunpw_1 cuni fiunpw_0 sup_set_class cpw wcel fiunpw_1 cuni fiunpw_0 sup_set_class wss fiunpw_0 sup_set_class fiunpw_1 elssuni fiunpw_1 cuni fiunpw_0 sup_set_class elpwi anim12i fiunpw_0 sup_set_class fiunpw_1 cuni eqss sylibr ex reximia syl impbii $.
$}
$( A well-founded relation has no 3-cycle loops.  Special case of
       Proposition 6.23 of [TakeutiZaring] p. 30.  (Contributed by NM,
       10-Apr-1994.)  (Revised by Mario Carneiro, 22-Jun-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v x $.
	$v y $.
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	$d x y R $.
	ifr3nr_0 $f set x $.
	ifr3nr_1 $f set y $.
	ffr3nr_0 $f class A $.
	ffr3nr_1 $f class B $.
	ffr3nr_2 $f class C $.
	ffr3nr_3 $f class D $.
	ffr3nr_4 $f class R $.
	fr3nr $p |- ( ( R Fr A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B R C /\ C R D /\ D R B ) ) $= ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr w3a ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr w3a ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr wn ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr wn ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr wn w3o ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr w3a wn ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral w3o ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr wn ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr wn ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr wn w3o ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_0 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wrex ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral w3o ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp cvv wcel ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ffr3nr_0 wss ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp c0 wne ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_0 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wrex ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp cvv wcel ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_2 ffr3nr_3 tpex a1i ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a simpl ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ffr3nr_1 ffr3nr_2 cpr ffr3nr_3 csn cun ffr3nr_0 ffr3nr_1 ffr3nr_2 ffr3nr_3 df-tp ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_2 cpr ffr3nr_3 csn ffr3nr_0 ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_1 ffr3nr_2 cpr ffr3nr_0 wss ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel simpr1 ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel simpr2 ffr3nr_1 ffr3nr_2 ffr3nr_0 prssi syl2anc ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_3 ffr3nr_0 ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel simpr3 snssd unssd syl5eqss ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp c0 wne ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_1 csn ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wss ffr3nr_1 ffr3nr_2 ffr3nr_3 snsstp1 ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_0 wcel ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_1 csn ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wss wb ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel simpr1 ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ffr3nr_0 snssg syl mpbiri ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ffr3nr_1 ne0i syl ifr3nr_0 ifr3nr_1 ffr3nr_0 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp cvv ffr3nr_4 fri syl22anc ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_0 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wrex ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral w3o wb ffr3nr_0 ffr3nr_4 wfr ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ifr3nr_0 ffr3nr_1 ffr3nr_2 ffr3nr_3 ffr3nr_0 ffr3nr_0 ffr3nr_0 ifr3nr_0 sup_set_class ffr3nr_1 wceq ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr wn ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ifr3nr_0 sup_set_class ffr3nr_1 wceq ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr ifr3nr_0 sup_set_class ffr3nr_1 ifr3nr_1 sup_set_class ffr3nr_4 breq2 notbid ralbidv ifr3nr_0 sup_set_class ffr3nr_2 wceq ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr wn ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ifr3nr_0 sup_set_class ffr3nr_2 wceq ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr ifr3nr_0 sup_set_class ffr3nr_2 ifr3nr_1 sup_set_class ffr3nr_4 breq2 notbid ralbidv ifr3nr_0 sup_set_class ffr3nr_3 wceq ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr wn ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ifr3nr_0 sup_set_class ffr3nr_3 wceq ifr3nr_1 sup_set_class ifr3nr_0 sup_set_class ffr3nr_4 wbr ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr ifr3nr_0 sup_set_class ffr3nr_3 ifr3nr_1 sup_set_class ffr3nr_4 breq2 notbid ralbidv rextpg adantl mpbid ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr wn ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_3 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr wn wi ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_3 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_3 csn ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wss ffr3nr_1 ffr3nr_2 ffr3nr_3 snsstp3 ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_3 ffr3nr_0 wcel ffr3nr_3 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_3 csn ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wss wb ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel simpr3 ffr3nr_3 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ffr3nr_0 snssg syl mpbiri ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr wn ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_3 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ifr3nr_1 sup_set_class ffr3nr_3 wceq ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_4 wbr ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_1 ffr3nr_4 breq1 notbid rspcv syl ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr wn wi ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_1 csn ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wss ffr3nr_1 ffr3nr_2 ffr3nr_3 snsstp1 ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_1 ffr3nr_0 wcel ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_1 csn ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wss wb ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel simpr1 ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ffr3nr_0 snssg syl mpbiri ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr wn ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ifr3nr_1 sup_set_class ffr3nr_1 wceq ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_4 wbr ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr ifr3nr_1 sup_set_class ffr3nr_1 ffr3nr_2 ffr3nr_4 breq1 notbid rspcv syl ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_2 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wral ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr wn wi ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_2 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_2 csn ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wss ffr3nr_1 ffr3nr_2 ffr3nr_3 snsstp2 ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel w3a wa ffr3nr_2 ffr3nr_0 wcel ffr3nr_2 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wcel ffr3nr_2 csn ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp wss wb ffr3nr_0 ffr3nr_4 wfr ffr3nr_1 ffr3nr_0 wcel ffr3nr_2 ffr3nr_0 wcel ffr3nr_3 ffr3nr_0 wcel simpr2 ffr3nr_2 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ffr3nr_0 snssg syl mpbiri ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr wn ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr wn ifr3nr_1 ffr3nr_2 ffr3nr_1 ffr3nr_2 ffr3nr_3 ctp ifr3nr_1 sup_set_class ffr3nr_2 wceq ifr3nr_1 sup_set_class ffr3nr_3 ffr3nr_4 wbr ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr ifr3nr_1 sup_set_class ffr3nr_2 ffr3nr_3 ffr3nr_4 breq1 notbid rspcv syl 3orim123d mpd ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr 3ianor sylibr ffr3nr_3 ffr3nr_1 ffr3nr_4 wbr ffr3nr_1 ffr3nr_2 ffr3nr_4 wbr ffr3nr_2 ffr3nr_3 ffr3nr_4 wbr 3anrot sylnib $.
$}
$( A set well-founded by epsilon contains no 3-cycle loops.  (Contributed by
     NM, 19-Apr-1994.)  (Revised by Mario Carneiro, 22-Jun-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fepne3_0 $f class A $.
	fepne3_1 $f class B $.
	fepne3_2 $f class C $.
	fepne3_3 $f class D $.
	epne3 $p |- ( ( _E Fr A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B e. C /\ C e. D /\ D e. B ) ) $= fepne3_0 cep wfr fepne3_1 fepne3_0 wcel fepne3_2 fepne3_0 wcel fepne3_3 fepne3_0 wcel w3a wa fepne3_1 fepne3_2 cep wbr fepne3_2 fepne3_3 cep wbr fepne3_3 fepne3_1 cep wbr w3a fepne3_1 fepne3_2 wcel fepne3_2 fepne3_3 wcel fepne3_3 fepne3_1 wcel w3a fepne3_0 fepne3_1 fepne3_2 fepne3_3 cep fr3nr fepne3_1 fepne3_0 wcel fepne3_2 fepne3_0 wcel fepne3_3 fepne3_0 wcel w3a fepne3_1 fepne3_2 cep wbr fepne3_2 fepne3_3 cep wbr fepne3_3 fepne3_1 cep wbr w3a fepne3_1 fepne3_2 wcel fepne3_2 fepne3_3 wcel fepne3_3 fepne3_1 wcel w3a wb fepne3_0 cep wfr fepne3_1 fepne3_0 wcel fepne3_2 fepne3_0 wcel fepne3_3 fepne3_0 wcel w3a fepne3_1 fepne3_2 cep wbr fepne3_1 fepne3_2 wcel fepne3_2 fepne3_3 cep wbr fepne3_2 fepne3_3 wcel fepne3_3 fepne3_1 cep wbr fepne3_3 fepne3_1 wcel fepne3_2 fepne3_0 wcel fepne3_1 fepne3_0 wcel fepne3_1 fepne3_2 cep wbr fepne3_1 fepne3_2 wcel wb fepne3_3 fepne3_0 wcel fepne3_1 fepne3_2 fepne3_0 epelg 3ad2ant2 fepne3_3 fepne3_0 wcel fepne3_1 fepne3_0 wcel fepne3_2 fepne3_3 cep wbr fepne3_2 fepne3_3 wcel wb fepne3_2 fepne3_0 wcel fepne3_2 fepne3_3 fepne3_0 epelg 3ad2ant3 fepne3_1 fepne3_0 wcel fepne3_2 fepne3_0 wcel fepne3_3 fepne3_1 cep wbr fepne3_3 fepne3_1 wcel wb fepne3_3 fepne3_0 wcel fepne3_3 fepne3_1 fepne3_0 epelg 3ad2ant1 3anbi123d adantl mtbid $.
$}
$( Alternate definition of well-ordering.  Definition 6.24(2) of
       [TakeutiZaring] p. 30.  (Contributed by NM, 16-Mar-1997.)  (Proof
       shortened by Andrew Salmon, 12-Aug-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v R $.
	$v z $.
	$d x y z R $.
	$d x y z A $.
	idfwe2_0 $f set z $.
	fdfwe2_0 $f set x $.
	fdfwe2_1 $f set y $.
	fdfwe2_2 $f class A $.
	fdfwe2_3 $f class R $.
	dfwe2 $p |- ( R We A <-> ( R Fr A /\ A. x e. A A. y e. A ( x R y \/ x = y \/ y R x ) ) ) $= fdfwe2_2 fdfwe2_3 wwe fdfwe2_2 fdfwe2_3 wfr fdfwe2_2 fdfwe2_3 wor wa fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral wa fdfwe2_2 fdfwe2_3 df-we fdfwe2_2 fdfwe2_3 wfr fdfwe2_2 fdfwe2_3 wor fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_2 fdfwe2_3 wor fdfwe2_2 fdfwe2_3 wpo fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral wa fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_0 fdfwe2_1 fdfwe2_2 fdfwe2_3 df-so fdfwe2_2 fdfwe2_3 wfr fdfwe2_2 fdfwe2_3 wpo fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral wa fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_2 fdfwe2_3 wpo fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral simpr fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_2 fdfwe2_3 wpo fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o idfwe2_0 fdfwe2_2 wral fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wa idfwe2_0 fdfwe2_2 wral fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_2 fdfwe2_3 wpo fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o wi idfwe2_0 wal fdfwe2_1 wal fdfwe2_0 wal fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wa wi idfwe2_0 wal fdfwe2_1 wal fdfwe2_0 wal fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o idfwe2_0 fdfwe2_2 wral fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wa idfwe2_0 fdfwe2_2 wral fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 wral fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o wi idfwe2_0 wal fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wa wi idfwe2_0 wal fdfwe2_0 fdfwe2_1 fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o wi fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wa wi idfwe2_0 fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wa fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wa wi fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wi fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa ax-1 a1i fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a wa fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wa wn fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa wn fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wa wn idfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_2 fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 fr2nr 3adantr3 fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 breq2 anbi2d notbid syl5ibcom fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr pm2.21 syl6 fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a wa idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a wa idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_2 fdfwe2_3 wfr fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_1 sup_set_class fdfwe2_2 wcel idfwe2_0 sup_set_class fdfwe2_2 wcel w3a wa fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3a idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa wa fdfwe2_2 fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 fr3nr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3a fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3a fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr df-3an biimpri ancoms nsyl pm2.21d exp3a 3jaod fdfwe2_2 fdfwe2_3 wfr fdfwe2_1 sup_set_class fdfwe2_2 wcel fdfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn idfwe2_0 sup_set_class fdfwe2_2 wcel fdfwe2_2 fdfwe2_0 sup_set_class fdfwe2_3 frirr 3ad2antr1 jctild ex a2d alimdv 2alimdv fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_0 fdfwe2_1 idfwe2_0 fdfwe2_2 fdfwe2_2 fdfwe2_2 r3al fdfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr wn fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wa fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr wi wa fdfwe2_0 fdfwe2_1 idfwe2_0 fdfwe2_2 fdfwe2_2 fdfwe2_2 r3al 3imtr4g fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o idfwe2_0 fdfwe2_2 wral fdfwe2_1 fdfwe2_2 wral fdfwe2_0 fdfwe2_2 fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_1 fdfwe2_2 wral fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o idfwe2_0 fdfwe2_2 wral fdfwe2_1 fdfwe2_2 wral fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 ralidm fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 fdfwe2_2 wral fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o idfwe2_0 fdfwe2_2 wral fdfwe2_1 fdfwe2_2 fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr w3o fdfwe2_1 idfwe2_0 fdfwe2_2 fdfwe2_1 sup_set_class idfwe2_0 sup_set_class wceq fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class idfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_0 sup_set_class fdfwe2_1 sup_set_class wceq fdfwe2_0 sup_set_class idfwe2_0 sup_set_class wceq fdfwe2_1 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 wbr fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 breq2 fdfwe2_1 idfwe2_0 fdfwe2_0 equequ2 fdfwe2_1 sup_set_class idfwe2_0 sup_set_class fdfwe2_0 sup_set_class fdfwe2_3 breq1 3orbi123d cbvralv ralbii bitr3i ralbii fdfwe2_0 fdfwe2_1 idfwe2_0 fdfwe2_2 fdfwe2_3 df-po 3imtr4g ancrd impbid2 syl5bb pm5.32i bitri $.
$}

