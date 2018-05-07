$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Cantor_s_Theorem.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Undefined values and restricted iota (description binder)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c Undef  $.
$c iota_  $.
$( Extend class notation with undefined value function. $)
${
	cund $a class Undef $.
$}
$( Extend class notation with restricted description binder. $)
${
	$v ph $.
	$v x $.
	$v A $.
	fcrio_0 $f wff ph $.
	fcrio_1 $f set x $.
	fcrio_2 $f class A $.
	crio $a class ( iota_ x e. A ph ) $.
$}
$( Define the undefined value function, whose value at set ` s ` is
     guaranteed not to be a member of ` s ` (see ~ pwuninel ).  (Contributed by
     NM, 15-Sep-2011.) $)
${
	$v s $.
	fdf-undef_0 $f set s $.
	df-undef $a |- Undef = ( s e. _V |-> ~P U. s ) $.
$}
$( Direct proof of ~ pwuninel avoiding functions and thus several ZF axioms.
     (Contributed by Stefan O'Rear, 22-Feb-2015.) $)
${
	$v A $.
	$v V $.
	fpwuninel2_0 $f class A $.
	fpwuninel2_1 $f class V $.
	pwuninel2 $p |- ( U. A e. V -> -. ~P U. A e. A ) $= fpwuninel2_0 cuni fpwuninel2_1 wcel fpwuninel2_0 cuni cpw fpwuninel2_0 cuni wss fpwuninel2_0 cuni cpw fpwuninel2_0 wcel fpwuninel2_0 cuni fpwuninel2_1 pwnss fpwuninel2_0 cuni cpw fpwuninel2_0 elssuni nsyl $.
$}
$( The power set of the union of a set does not belong to the set.  This
     theorem provides a way of constructing a new set that doesn't belong to a
     given set.  See also ~ pwuninel2 .  (Contributed by NM, 27-Jun-2008.)
     (Proof shortened by Mario Carneiro, 23-Dec-2016.) $)
${
	$v A $.
	fpwuninel_0 $f class A $.
	pwuninel $p |- -. ~P U. A e. A $= fpwuninel_0 cuni cpw fpwuninel_0 wcel fpwuninel_0 cuni cpw fpwuninel_0 wcel wn fpwuninel_0 cuni cpw fpwuninel_0 wcel fpwuninel_0 cuni cvv wcel fpwuninel_0 cuni cpw fpwuninel_0 wcel wn fpwuninel_0 cuni cpw fpwuninel_0 wcel fpwuninel_0 cuni cpw cvv wcel fpwuninel_0 cuni cvv wcel fpwuninel_0 cuni cpw fpwuninel_0 elex fpwuninel_0 cuni pwexb sylibr fpwuninel_0 cvv pwuninel2 syl fpwuninel_0 cuni cpw fpwuninel_0 wcel wn id pm2.61i $.
$}
$( Value of the undefined value function.  Normally we will not reference
       the explicit value but will use ~ undefnel instead.  (Contributed by NM,
       15-Sep-2011.)  (Revised by Mario Carneiro, 24-Dec-2016.) $)
${
	$v S $.
	$v V $.
	$v s $.
	$d s S $.
	iundefval_0 $f set s $.
	fundefval_0 $f class S $.
	fundefval_1 $f class V $.
	undefval $p |- ( S e. V -> ( Undef ` S ) = ~P U. S ) $= fundefval_0 fundefval_1 wcel fundefval_0 cvv wcel fundefval_0 cuni cpw cvv wcel fundefval_0 cund cfv fundefval_0 cuni cpw wceq fundefval_0 fundefval_1 elex fundefval_0 fundefval_1 wcel fundefval_0 cuni cvv wcel fundefval_0 cuni cpw cvv wcel fundefval_0 fundefval_1 uniexg fundefval_0 cuni cvv pwexg syl iundefval_0 fundefval_0 iundefval_0 cv cuni cpw fundefval_0 cuni cpw cvv cvv cund iundefval_0 cv fundefval_0 wceq iundefval_0 cv cuni fundefval_0 cuni iundefval_0 cv fundefval_0 unieq pweqd iundefval_0 df-undef fvmptg syl2anc $.
$}
$( The undefined value generated from a set is not a member of the set.
     (Contributed by NM, 15-Sep-2011.) $)
${
	$v S $.
	$v V $.
	fundefnel2_0 $f class S $.
	fundefnel2_1 $f class V $.
	undefnel2 $p |- ( S e. V -> -. ( Undef ` S ) e. S ) $= fundefnel2_0 fundefnel2_1 wcel fundefnel2_0 cund cfv fundefnel2_0 wcel fundefnel2_0 cuni cpw fundefnel2_0 wcel fundefnel2_0 pwuninel fundefnel2_0 fundefnel2_1 wcel fundefnel2_0 cund cfv fundefnel2_0 cuni cpw fundefnel2_0 fundefnel2_0 fundefnel2_1 undefval eleq1d mtbiri $.
$}
$( The undefined value generated from a set is not a member of the set.
     (Contributed by NM, 15-Sep-2011.) $)
${
	$v S $.
	$v V $.
	fundefnel_0 $f class S $.
	fundefnel_1 $f class V $.
	undefnel $p |- ( S e. V -> ( Undef ` S ) e/ S ) $= fundefnel_0 fundefnel_1 wcel fundefnel_0 cund cfv fundefnel_0 wcel wn fundefnel_0 cund cfv fundefnel_0 wnel fundefnel_0 fundefnel_1 undefnel2 fundefnel_0 cund cfv fundefnel_0 df-nel sylibr $.
$}
$( Define restricted description binder.  In case it doesn't exist, we
       return a set which is not a member of the domain of discourse ` A ` .
       See also comments for ~ df-iota .  (Contributed by NM, 15-Sep-2011.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	fdf-riota_0 $f wff ph $.
	fdf-riota_1 $f set x $.
	fdf-riota_2 $f class A $.
	df-riota $a |- ( iota_ x e. A ph ) = if ( E! x e. A ph , ( iota x ( x e. A /\ ph ) ) , ( Undef ` { x | x e. A } ) ) $.
$}
$( Formula-building deduction rule for iota.  (Contributed by NM,
       15-Sep-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x ph $.
	friotaeqdv_0 $f wff ph $.
	friotaeqdv_1 $f wff ps $.
	friotaeqdv_2 $f set x $.
	friotaeqdv_3 $f class A $.
	friotaeqdv_4 $f class B $.
	eriotaeqdv_0 $e |- ( ph -> A = B ) $.
	riotaeqdv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ps ) ) $= friotaeqdv_0 friotaeqdv_1 friotaeqdv_2 friotaeqdv_3 wreu friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_1 wa friotaeqdv_2 cio friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_2 cab cund cfv cif friotaeqdv_1 friotaeqdv_2 friotaeqdv_4 wreu friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_1 wa friotaeqdv_2 cio friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_2 cab cund cfv cif friotaeqdv_1 friotaeqdv_2 friotaeqdv_3 crio friotaeqdv_1 friotaeqdv_2 friotaeqdv_4 crio friotaeqdv_0 friotaeqdv_1 friotaeqdv_2 friotaeqdv_3 wreu friotaeqdv_1 friotaeqdv_2 friotaeqdv_4 wreu friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_1 wa friotaeqdv_2 cio friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_2 cab cund cfv friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_1 wa friotaeqdv_2 cio friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_2 cab cund cfv friotaeqdv_0 friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_1 wa friotaeqdv_2 weu friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_1 wa friotaeqdv_2 weu friotaeqdv_1 friotaeqdv_2 friotaeqdv_3 wreu friotaeqdv_1 friotaeqdv_2 friotaeqdv_4 wreu friotaeqdv_0 friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_1 wa friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_1 wa friotaeqdv_2 friotaeqdv_0 friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_1 friotaeqdv_0 friotaeqdv_3 friotaeqdv_4 friotaeqdv_2 cv eriotaeqdv_0 eleq2d anbi1d eubidv friotaeqdv_1 friotaeqdv_2 friotaeqdv_3 df-reu friotaeqdv_1 friotaeqdv_2 friotaeqdv_4 df-reu 3bitr4g friotaeqdv_0 friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_1 wa friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_1 wa friotaeqdv_2 friotaeqdv_0 friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_1 friotaeqdv_0 friotaeqdv_3 friotaeqdv_4 friotaeqdv_2 cv eriotaeqdv_0 eleq2d anbi1d iotabidv friotaeqdv_0 friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_2 cab friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_2 cab cund friotaeqdv_0 friotaeqdv_2 cv friotaeqdv_3 wcel friotaeqdv_2 cv friotaeqdv_4 wcel friotaeqdv_2 friotaeqdv_0 friotaeqdv_3 friotaeqdv_4 friotaeqdv_2 cv eriotaeqdv_0 eleq2d abbidv fveq2d ifbieq12d friotaeqdv_1 friotaeqdv_2 friotaeqdv_3 df-riota friotaeqdv_1 friotaeqdv_2 friotaeqdv_4 df-riota 3eqtr4g $.
$}
$( Formula-building deduction rule for restricted iota.  (Contributed by
       NM, 15-Sep-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v A $.
	$d x ph $.
	friotabidv_0 $f wff ph $.
	friotabidv_1 $f wff ps $.
	friotabidv_2 $f wff ch $.
	friotabidv_3 $f set x $.
	friotabidv_4 $f class A $.
	eriotabidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	riotabidv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. A ch ) ) $= friotabidv_0 friotabidv_1 friotabidv_3 friotabidv_4 wreu friotabidv_3 cv friotabidv_4 wcel friotabidv_1 wa friotabidv_3 cio friotabidv_3 cv friotabidv_4 wcel friotabidv_3 cab cund cfv cif friotabidv_2 friotabidv_3 friotabidv_4 wreu friotabidv_3 cv friotabidv_4 wcel friotabidv_2 wa friotabidv_3 cio friotabidv_3 cv friotabidv_4 wcel friotabidv_3 cab cund cfv cif friotabidv_1 friotabidv_3 friotabidv_4 crio friotabidv_2 friotabidv_3 friotabidv_4 crio friotabidv_0 friotabidv_1 friotabidv_3 friotabidv_4 wreu friotabidv_2 friotabidv_3 friotabidv_4 wreu friotabidv_3 cv friotabidv_4 wcel friotabidv_1 wa friotabidv_3 cio friotabidv_3 cv friotabidv_4 wcel friotabidv_3 cab cund cfv friotabidv_3 cv friotabidv_4 wcel friotabidv_2 wa friotabidv_3 cio friotabidv_3 cv friotabidv_4 wcel friotabidv_3 cab cund cfv friotabidv_0 friotabidv_1 friotabidv_2 friotabidv_3 friotabidv_4 eriotabidv_0 reubidv friotabidv_0 friotabidv_3 cv friotabidv_4 wcel friotabidv_1 wa friotabidv_3 cv friotabidv_4 wcel friotabidv_2 wa friotabidv_3 friotabidv_0 friotabidv_1 friotabidv_2 friotabidv_3 cv friotabidv_4 wcel eriotabidv_0 anbi2d iotabidv friotabidv_0 friotabidv_3 cv friotabidv_4 wcel friotabidv_3 cab cund cfv eqidd ifbieq12d friotabidv_1 friotabidv_3 friotabidv_4 df-riota friotabidv_2 friotabidv_3 friotabidv_4 df-riota 3eqtr4g $.
$}
$( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 15-Sep-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v A $.
	$v B $.
	$d x ph $.
	friotaeqbidv_0 $f wff ph $.
	friotaeqbidv_1 $f wff ps $.
	friotaeqbidv_2 $f wff ch $.
	friotaeqbidv_3 $f set x $.
	friotaeqbidv_4 $f class A $.
	friotaeqbidv_5 $f class B $.
	eriotaeqbidv_0 $e |- ( ph -> A = B ) $.
	eriotaeqbidv_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	riotaeqbidv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ch ) ) $= friotaeqbidv_0 friotaeqbidv_1 friotaeqbidv_3 friotaeqbidv_4 crio friotaeqbidv_2 friotaeqbidv_3 friotaeqbidv_4 crio friotaeqbidv_2 friotaeqbidv_3 friotaeqbidv_5 crio friotaeqbidv_0 friotaeqbidv_1 friotaeqbidv_2 friotaeqbidv_3 friotaeqbidv_4 eriotaeqbidv_1 riotabidv friotaeqbidv_0 friotaeqbidv_2 friotaeqbidv_3 friotaeqbidv_4 friotaeqbidv_5 eriotaeqbidv_0 riotaeqdv eqtrd $.
$}
$( Restricted iota is a set.  (Contributed by NM, 15-Sep-2011.) $)
${
	$v ps $.
	$v x $.
	$v A $.
	friotaex_0 $f wff ps $.
	friotaex_1 $f set x $.
	friotaex_2 $f class A $.
	riotaex $p |- ( iota_ x e. A ps ) e. _V $= friotaex_0 friotaex_1 friotaex_2 crio friotaex_0 friotaex_1 friotaex_2 wreu friotaex_1 cv friotaex_2 wcel friotaex_0 wa friotaex_1 cio friotaex_1 cv friotaex_2 wcel friotaex_1 cab cund cfv cif cvv friotaex_0 friotaex_1 friotaex_2 df-riota friotaex_0 friotaex_1 friotaex_2 wreu friotaex_1 cv friotaex_2 wcel friotaex_0 wa friotaex_1 cio friotaex_1 cv friotaex_2 wcel friotaex_1 cab cund cfv friotaex_1 cv friotaex_2 wcel friotaex_0 wa friotaex_1 iotaex friotaex_1 cv friotaex_2 wcel friotaex_1 cab cund fvex ifex eqeltri $.
$}
$( An iota restricted to the universe is unrestricted.  (Contributed by NM,
     18-Sep-2011.) $)
${
	$v ph $.
	$v x $.
	friotav_0 $f wff ph $.
	friotav_1 $f set x $.
	riotav $p |- ( iota_ x e. _V ph ) = ( iota x ph ) $= friotav_0 friotav_1 cvv crio friotav_0 friotav_1 cvv wreu friotav_1 cv cvv wcel friotav_0 wa friotav_1 cio friotav_1 cv cvv wcel friotav_1 cab cund cfv cif friotav_0 friotav_1 cio friotav_0 friotav_1 cvv df-riota friotav_0 friotav_1 cvv wreu friotav_0 friotav_1 cio friotav_0 friotav_1 cvv wreu friotav_1 cv cvv wcel friotav_0 wa friotav_1 cio friotav_1 cv cvv wcel friotav_1 cab cund cfv cif wceq friotav_0 friotav_1 cvv wreu friotav_0 friotav_1 cvv wreu friotav_1 cv cvv wcel friotav_0 wa friotav_1 cio friotav_1 cv cvv wcel friotav_1 cab cund cfv cif friotav_1 cv cvv wcel friotav_0 wa friotav_1 cio friotav_0 friotav_1 cio friotav_0 friotav_1 cvv wreu friotav_1 cv cvv wcel friotav_0 wa friotav_1 cio friotav_1 cv cvv wcel friotav_1 cab cund cfv iftrue friotav_0 friotav_1 cv cvv wcel friotav_0 wa friotav_1 friotav_1 cv cvv wcel friotav_0 friotav_1 vex biantrur iotabii syl6reqr friotav_0 friotav_1 cvv wreu wn friotav_0 friotav_1 cio friotav_1 cv cvv wcel friotav_1 cab cund cfv friotav_0 friotav_1 cvv wreu friotav_1 cv cvv wcel friotav_0 wa friotav_1 cio friotav_1 cv cvv wcel friotav_1 cab cund cfv cif friotav_0 friotav_1 cvv wreu wn friotav_0 friotav_1 cio c0 friotav_1 cv cvv wcel friotav_1 cab cund cfv friotav_0 friotav_1 cvv wreu friotav_0 friotav_1 weu friotav_0 friotav_1 cio c0 wceq friotav_0 friotav_1 reuv friotav_0 friotav_1 iotanul sylnbi friotav_1 cv cvv wcel friotav_1 cab cund cfv cvv cund cfv c0 friotav_1 cv cvv wcel friotav_1 cab cvv cund friotav_1 cvv abid2 fveq2i cvv cvv wcel wn cvv cund cfv c0 wceq vprc cvv cund fvprc ax-mp eqtri syl6eqr friotav_0 friotav_1 cvv wreu friotav_1 cv cvv wcel friotav_0 wa friotav_1 cio friotav_1 cv cvv wcel friotav_1 cab cund cfv iffalse eqtr4d pm2.61i eqtr4i $.
$}
$( Restricted iota in terms of iota.  (Contributed by NM, 15-Sep-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	friotaiota_0 $f wff ph $.
	friotaiota_1 $f set x $.
	friotaiota_2 $f class A $.
	riotaiota $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) = ( iota x ( x e. A /\ ph ) ) ) $= friotaiota_0 friotaiota_1 friotaiota_2 wreu friotaiota_0 friotaiota_1 friotaiota_2 crio friotaiota_0 friotaiota_1 friotaiota_2 wreu friotaiota_1 cv friotaiota_2 wcel friotaiota_0 wa friotaiota_1 cio friotaiota_1 cv friotaiota_2 wcel friotaiota_1 cab cund cfv cif friotaiota_1 cv friotaiota_2 wcel friotaiota_0 wa friotaiota_1 cio friotaiota_0 friotaiota_1 friotaiota_2 df-riota friotaiota_0 friotaiota_1 friotaiota_2 wreu friotaiota_1 cv friotaiota_2 wcel friotaiota_0 wa friotaiota_1 cio friotaiota_1 cv friotaiota_2 wcel friotaiota_1 cab cund cfv iftrue syl5eq $.
$}
$( Restricted iota in terms of class union.  (Contributed by NM,
     11-Oct-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	friotauni_0 $f wff ph $.
	friotauni_1 $f set x $.
	friotauni_2 $f class A $.
	riotauni $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) = U. { x e. A | ph } ) $= friotauni_0 friotauni_1 friotauni_2 wreu friotauni_0 friotauni_1 friotauni_2 crio friotauni_1 cv friotauni_2 wcel friotauni_0 wa friotauni_1 cio friotauni_0 friotauni_1 friotauni_2 crab cuni friotauni_0 friotauni_1 friotauni_2 riotaiota friotauni_0 friotauni_1 friotauni_2 wreu friotauni_1 cv friotauni_2 wcel friotauni_0 wa friotauni_1 cio friotauni_1 cv friotauni_2 wcel friotauni_0 wa friotauni_1 cab cuni friotauni_0 friotauni_1 friotauni_2 crab cuni friotauni_0 friotauni_1 friotauni_2 wreu friotauni_1 cv friotauni_2 wcel friotauni_0 wa friotauni_1 weu friotauni_1 cv friotauni_2 wcel friotauni_0 wa friotauni_1 cio friotauni_1 cv friotauni_2 wcel friotauni_0 wa friotauni_1 cab cuni wceq friotauni_0 friotauni_1 friotauni_2 df-reu friotauni_1 cv friotauni_2 wcel friotauni_0 wa friotauni_1 iotauni sylbi friotauni_0 friotauni_1 friotauni_2 crab friotauni_1 cv friotauni_2 wcel friotauni_0 wa friotauni_1 cab friotauni_0 friotauni_1 friotauni_2 df-rab unieqi syl6eqr eqtrd $.
$}
$( The abstraction variable in a restricted iota descriptor isn't free.
       (Contributed by NM, 12-Oct-2011.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fnfriota1_0 $f wff ph $.
	fnfriota1_1 $f set x $.
	fnfriota1_2 $f class A $.
	nfriota1 $p |- F/_ x ( iota_ x e. A ph ) $= fnfriota1_1 fnfriota1_0 fnfriota1_1 fnfriota1_2 crio fnfriota1_0 fnfriota1_1 fnfriota1_2 wreu fnfriota1_1 cv fnfriota1_2 wcel fnfriota1_0 wa fnfriota1_1 cio fnfriota1_1 cv fnfriota1_2 wcel fnfriota1_1 cab cund cfv cif fnfriota1_0 fnfriota1_1 fnfriota1_2 df-riota fnfriota1_0 fnfriota1_1 fnfriota1_2 wreu fnfriota1_1 fnfriota1_1 cv fnfriota1_2 wcel fnfriota1_0 wa fnfriota1_1 cio fnfriota1_1 cv fnfriota1_2 wcel fnfriota1_1 cab cund cfv fnfriota1_0 fnfriota1_1 fnfriota1_2 nfreu1 fnfriota1_1 cv fnfriota1_2 wcel fnfriota1_0 wa fnfriota1_1 nfiota1 fnfriota1_1 fnfriota1_1 cv fnfriota1_2 wcel fnfriota1_1 cab cund fnfriota1_1 cund nfcv fnfriota1_1 cv fnfriota1_2 wcel fnfriota1_1 nfab1 nffv nfif nfcxfr $.
$}
$( Deduction version of ~ nfriota .  (Contributed by NM, 18-Feb-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	fnfriotad_0 $f wff ph $.
	fnfriotad_1 $f wff ps $.
	fnfriotad_2 $f set x $.
	fnfriotad_3 $f set y $.
	fnfriotad_4 $f class A $.
	enfriotad_0 $e |- F/ y ph $.
	enfriotad_1 $e |- ( ph -> F/ x ps ) $.
	enfriotad_2 $e |- ( ph -> F/_ x A ) $.
	nfriotad $p |- ( ph -> F/_ x ( iota_ y e. A ps ) ) $= fnfriotad_0 fnfriotad_2 fnfriotad_1 fnfriotad_3 fnfriotad_4 crio fnfriotad_1 fnfriotad_3 fnfriotad_4 wreu fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_3 cab cund cfv cif fnfriotad_1 fnfriotad_3 fnfriotad_4 df-riota fnfriotad_0 fnfriotad_1 fnfriotad_3 fnfriotad_4 wreu fnfriotad_2 fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_3 cab cund cfv fnfriotad_0 fnfriotad_1 fnfriotad_2 fnfriotad_3 fnfriotad_4 enfriotad_0 enfriotad_2 enfriotad_1 nfreud fnfriotad_0 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal fnfriotad_2 fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio wnfc fnfriotad_0 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn fnfriotad_2 fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio wnfc fnfriotad_0 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn wa fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_2 fnfriotad_3 fnfriotad_0 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn fnfriotad_3 enfriotad_0 fnfriotad_2 fnfriotad_3 fnfriotad_3 nfnae nfan fnfriotad_0 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn wa fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 fnfriotad_2 fnfriotad_0 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn wa fnfriotad_2 fnfriotad_3 cv fnfriotad_4 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn fnfriotad_2 fnfriotad_3 cv wnfc fnfriotad_0 fnfriotad_2 fnfriotad_3 nfcvf adantl fnfriotad_0 fnfriotad_2 fnfriotad_4 wnfc fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn enfriotad_2 adantr nfeld fnfriotad_0 fnfriotad_1 fnfriotad_2 wnf fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn enfriotad_1 adantr nfand nfiotad ex fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal fnfriotad_2 fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio wnfc fnfriotad_3 fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio wnfc fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 nfiota1 fnfriotad_2 fnfriotad_3 fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_1 wa fnfriotad_3 cio eqidd drnfc1 mpbiri pm2.61d2 fnfriotad_0 fnfriotad_2 fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_3 cab cund fnfriotad_0 fnfriotad_2 cund nfcvd fnfriotad_0 fnfriotad_3 cv fnfriotad_4 wcel fnfriotad_2 fnfriotad_3 enfriotad_0 fnfriotad_0 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn wa fnfriotad_2 fnfriotad_3 cv fnfriotad_4 fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn fnfriotad_2 fnfriotad_3 cv wnfc fnfriotad_0 fnfriotad_2 fnfriotad_3 nfcvf adantl fnfriotad_0 fnfriotad_2 fnfriotad_4 wnfc fnfriotad_2 cv fnfriotad_3 cv wceq fnfriotad_2 wal wn enfriotad_2 adantr nfeld nfabd2 nffvd nfifd nfcxfrd $.
$}
$( A variable not free in a wff remains so in a restricted iota
       descriptor.  (Contributed by NM, 12-Oct-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	fnfriota_0 $f wff ph $.
	fnfriota_1 $f set x $.
	fnfriota_2 $f set y $.
	fnfriota_3 $f class A $.
	enfriota_0 $e |- F/ x ph $.
	enfriota_1 $e |- F/_ x A $.
	nfriota $p |- F/_ x ( iota_ y e. A ph ) $= fnfriota_1 fnfriota_0 fnfriota_2 fnfriota_3 crio wnfc wtru fnfriota_0 fnfriota_1 fnfriota_2 fnfriota_3 fnfriota_2 nftru fnfriota_0 fnfriota_1 wnf wtru enfriota_0 a1i fnfriota_1 fnfriota_3 wnfc wtru enfriota_1 a1i nfriotad trud $.
$}
$( Change bound variable in a restricted description binder.  (Contributed
       by NM, 18-Mar-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$d x z A $.
	$d y z A $.
	$d z ph $.
	$d z ps $.
	icbvriota_0 $f set z $.
	fcbvriota_0 $f wff ph $.
	fcbvriota_1 $f wff ps $.
	fcbvriota_2 $f set x $.
	fcbvriota_3 $f set y $.
	fcbvriota_4 $f class A $.
	ecbvriota_0 $e |- F/ y ph $.
	ecbvriota_1 $e |- F/ x ps $.
	ecbvriota_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvriota $p |- ( iota_ x e. A ph ) = ( iota_ y e. A ps ) $= fcbvriota_0 fcbvriota_2 fcbvriota_4 wreu fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_0 wa fcbvriota_2 cio fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_2 cab cund cfv cif fcbvriota_1 fcbvriota_3 fcbvriota_4 wreu fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_1 wa fcbvriota_3 cio fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_3 cab cund cfv cif fcbvriota_0 fcbvriota_2 fcbvriota_4 crio fcbvriota_1 fcbvriota_3 fcbvriota_4 crio fcbvriota_0 fcbvriota_2 fcbvriota_4 wreu fcbvriota_1 fcbvriota_3 fcbvriota_4 wreu fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_0 wa fcbvriota_2 cio fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_2 cab cund cfv fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_1 wa fcbvriota_3 cio fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_3 cab cund cfv fcbvriota_0 fcbvriota_1 fcbvriota_2 fcbvriota_3 fcbvriota_4 ecbvriota_0 ecbvriota_1 ecbvriota_2 cbvreu fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_0 wa fcbvriota_2 cio icbvriota_0 cv fcbvriota_4 wcel fcbvriota_0 fcbvriota_2 icbvriota_0 wsb wa icbvriota_0 cio fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_1 wa fcbvriota_3 cio fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_0 wa icbvriota_0 cv fcbvriota_4 wcel fcbvriota_0 fcbvriota_2 icbvriota_0 wsb wa fcbvriota_2 icbvriota_0 fcbvriota_2 cv icbvriota_0 cv wceq fcbvriota_2 cv fcbvriota_4 wcel icbvriota_0 cv fcbvriota_4 wcel fcbvriota_0 fcbvriota_0 fcbvriota_2 icbvriota_0 wsb fcbvriota_2 cv icbvriota_0 cv fcbvriota_4 eleq1 fcbvriota_0 fcbvriota_2 icbvriota_0 sbequ12 anbi12d fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_0 wa icbvriota_0 nfv icbvriota_0 cv fcbvriota_4 wcel fcbvriota_0 fcbvriota_2 icbvriota_0 wsb fcbvriota_2 icbvriota_0 cv fcbvriota_4 wcel fcbvriota_2 nfv fcbvriota_0 fcbvriota_2 icbvriota_0 nfs1v nfan cbviota icbvriota_0 cv fcbvriota_4 wcel fcbvriota_0 fcbvriota_2 icbvriota_0 wsb wa fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_1 wa icbvriota_0 fcbvriota_3 icbvriota_0 cv fcbvriota_3 cv wceq icbvriota_0 cv fcbvriota_4 wcel fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_0 fcbvriota_2 icbvriota_0 wsb fcbvriota_1 icbvriota_0 cv fcbvriota_3 cv fcbvriota_4 eleq1 icbvriota_0 cv fcbvriota_3 cv wceq fcbvriota_0 fcbvriota_2 icbvriota_0 wsb fcbvriota_0 fcbvriota_2 fcbvriota_3 wsb fcbvriota_1 fcbvriota_0 icbvriota_0 fcbvriota_3 fcbvriota_2 sbequ fcbvriota_0 fcbvriota_1 fcbvriota_2 fcbvriota_3 ecbvriota_1 ecbvriota_2 sbie syl6bb anbi12d icbvriota_0 cv fcbvriota_4 wcel fcbvriota_0 fcbvriota_2 icbvriota_0 wsb fcbvriota_3 icbvriota_0 cv fcbvriota_4 wcel fcbvriota_3 nfv fcbvriota_0 fcbvriota_2 icbvriota_0 fcbvriota_3 ecbvriota_0 nfsb nfan fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_1 wa icbvriota_0 nfv cbviota eqtri fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_2 cab fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_3 cab cund fcbvriota_2 cv fcbvriota_4 wcel fcbvriota_2 cab fcbvriota_4 fcbvriota_3 cv fcbvriota_4 wcel fcbvriota_3 cab fcbvriota_2 fcbvriota_4 abid2 fcbvriota_3 fcbvriota_4 abid2 eqtr4i fveq2i ifbieq12i fcbvriota_0 fcbvriota_2 fcbvriota_4 df-riota fcbvriota_1 fcbvriota_3 fcbvriota_4 df-riota 3eqtr4i $.
$}
$( Change bound variable in a restricted description binder.  (Contributed
       by NM, 18-Mar-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$d x A $.
	$d y A $.
	$d y ph $.
	$d x ps $.
	fcbvriotav_0 $f wff ph $.
	fcbvriotav_1 $f wff ps $.
	fcbvriotav_2 $f set x $.
	fcbvriotav_3 $f set y $.
	fcbvriotav_4 $f class A $.
	ecbvriotav_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvriotav $p |- ( iota_ x e. A ph ) = ( iota_ y e. A ps ) $= fcbvriotav_0 fcbvriotav_1 fcbvriotav_2 fcbvriotav_3 fcbvriotav_4 fcbvriotav_0 fcbvriotav_3 nfv fcbvriotav_1 fcbvriotav_2 nfv ecbvriotav_0 cbvriota $.
$}
$( Interchange class substitution and restricted description binder.
       (Contributed by NM, 24-Feb-2013.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v V $.
	$d y z A $.
	$d x z B $.
	$d z ph $.
	$d x y $.
	icsbriotag_0 $f set z $.
	fcsbriotag_0 $f wff ph $.
	fcsbriotag_1 $f set x $.
	fcsbriotag_2 $f set y $.
	fcsbriotag_3 $f class A $.
	fcsbriotag_4 $f class B $.
	fcsbriotag_5 $f class V $.
	csbriotag $p |- ( A e. V -> [_ A / x ]_ ( iota_ y e. B ph ) = ( iota_ y e. B [. A / x ]. ph ) ) $= fcsbriotag_1 icsbriotag_0 cv fcsbriotag_0 fcsbriotag_2 fcsbriotag_4 crio csb fcsbriotag_0 fcsbriotag_1 icsbriotag_0 wsb fcsbriotag_2 fcsbriotag_4 crio wceq fcsbriotag_1 fcsbriotag_3 fcsbriotag_0 fcsbriotag_2 fcsbriotag_4 crio csb fcsbriotag_0 fcsbriotag_1 fcsbriotag_3 wsbc fcsbriotag_2 fcsbriotag_4 crio wceq icsbriotag_0 fcsbriotag_3 fcsbriotag_5 icsbriotag_0 cv fcsbriotag_3 wceq fcsbriotag_1 icsbriotag_0 cv fcsbriotag_0 fcsbriotag_2 fcsbriotag_4 crio csb fcsbriotag_1 fcsbriotag_3 fcsbriotag_0 fcsbriotag_2 fcsbriotag_4 crio csb fcsbriotag_0 fcsbriotag_1 icsbriotag_0 wsb fcsbriotag_2 fcsbriotag_4 crio fcsbriotag_0 fcsbriotag_1 fcsbriotag_3 wsbc fcsbriotag_2 fcsbriotag_4 crio fcsbriotag_1 icsbriotag_0 cv fcsbriotag_3 fcsbriotag_0 fcsbriotag_2 fcsbriotag_4 crio csbeq1 icsbriotag_0 cv fcsbriotag_3 wceq fcsbriotag_0 fcsbriotag_1 icsbriotag_0 wsb fcsbriotag_0 fcsbriotag_1 fcsbriotag_3 wsbc fcsbriotag_2 fcsbriotag_4 fcsbriotag_0 fcsbriotag_1 icsbriotag_0 fcsbriotag_3 dfsbcq2 riotabidv eqeq12d fcsbriotag_1 icsbriotag_0 cv fcsbriotag_0 fcsbriotag_2 fcsbriotag_4 crio fcsbriotag_0 fcsbriotag_1 icsbriotag_0 wsb fcsbriotag_2 fcsbriotag_4 crio icsbriotag_0 vex fcsbriotag_0 fcsbriotag_1 icsbriotag_0 wsb fcsbriotag_1 fcsbriotag_2 fcsbriotag_4 fcsbriotag_0 fcsbriotag_1 icsbriotag_0 nfs1v fcsbriotag_1 fcsbriotag_4 nfcv nfriota fcsbriotag_1 icsbriotag_0 weq fcsbriotag_0 fcsbriotag_0 fcsbriotag_1 icsbriotag_0 wsb fcsbriotag_2 fcsbriotag_4 fcsbriotag_0 fcsbriotag_1 icsbriotag_0 sbequ12 riotabidv csbief vtoclg $.
$}
$( Membership law for "the unique element in ` A ` such that ` ph ` ."

     This can useful for expanding an iota-based definition (see ~ df-iota ).
     If you have an unbounded iota, ~ iotacl may be useful.

     (Contributed by NM, 21-Aug-2011.)  (Revised by Mario Carneiro,
     23-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	friotacl2_0 $f wff ph $.
	friotacl2_1 $f set x $.
	friotacl2_2 $f class A $.
	riotacl2 $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) e. { x e. A | ph } ) $= friotacl2_0 friotacl2_1 friotacl2_2 wreu friotacl2_0 friotacl2_1 friotacl2_2 crio friotacl2_1 cv friotacl2_2 wcel friotacl2_0 wa friotacl2_1 cio friotacl2_0 friotacl2_1 friotacl2_2 crab friotacl2_0 friotacl2_1 friotacl2_2 riotaiota friotacl2_0 friotacl2_1 friotacl2_2 wreu friotacl2_1 cv friotacl2_2 wcel friotacl2_0 wa friotacl2_1 cio friotacl2_1 cv friotacl2_2 wcel friotacl2_0 wa friotacl2_1 cab friotacl2_0 friotacl2_1 friotacl2_2 crab friotacl2_0 friotacl2_1 friotacl2_2 wreu friotacl2_1 cv friotacl2_2 wcel friotacl2_0 wa friotacl2_1 weu friotacl2_1 cv friotacl2_2 wcel friotacl2_0 wa friotacl2_1 cio friotacl2_1 cv friotacl2_2 wcel friotacl2_0 wa friotacl2_1 cab wcel friotacl2_0 friotacl2_1 friotacl2_2 df-reu friotacl2_1 cv friotacl2_2 wcel friotacl2_0 wa friotacl2_1 iotacl sylbi friotacl2_0 friotacl2_1 friotacl2_2 df-rab syl6eleqr eqeltrd $.
$}
$( Closure of restricted iota.  (Contributed by NM, 21-Aug-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	friotacl_0 $f wff ph $.
	friotacl_1 $f set x $.
	friotacl_2 $f class A $.
	riotacl $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) e. A ) $= friotacl_0 friotacl_1 friotacl_2 wreu friotacl_0 friotacl_1 friotacl_2 crab friotacl_2 friotacl_0 friotacl_1 friotacl_2 crio friotacl_0 friotacl_1 friotacl_2 ssrab2 friotacl_0 friotacl_1 friotacl_2 riotacl2 sseldi $.
$}
$( Substitution law for descriptions.  Compare ~ iotasbc .  (Contributed by
     NM, 23-Aug-2011.)  (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	friotasbc_0 $f wff ph $.
	friotasbc_1 $f set x $.
	friotasbc_2 $f class A $.
	riotasbc $p |- ( E! x e. A ph -> [. ( iota_ x e. A ph ) / x ]. ph ) $= friotasbc_0 friotasbc_1 friotasbc_2 wreu friotasbc_0 friotasbc_1 friotasbc_2 crio friotasbc_0 friotasbc_1 cab wcel friotasbc_0 friotasbc_1 friotasbc_0 friotasbc_1 friotasbc_2 crio wsbc friotasbc_0 friotasbc_1 friotasbc_2 wreu friotasbc_0 friotasbc_1 friotasbc_2 crab friotasbc_0 friotasbc_1 cab friotasbc_0 friotasbc_1 friotasbc_2 crio friotasbc_0 friotasbc_1 friotasbc_2 rabssab friotasbc_0 friotasbc_1 friotasbc_2 riotacl2 sseldi friotasbc_0 friotasbc_1 friotasbc_0 friotasbc_1 friotasbc_2 crio df-sbc sylibr $.
$}
$( Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  ( ~ rabbidva analog.)  (Contributed by NM, 17-Jan-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v A $.
	$d x ph $.
	friotabidva_0 $f wff ph $.
	friotabidva_1 $f wff ps $.
	friotabidva_2 $f wff ch $.
	friotabidva_3 $f set x $.
	friotabidva_4 $f class A $.
	eriotabidva_0 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	riotabidva $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. A ch ) ) $= friotabidva_0 friotabidva_1 friotabidva_3 friotabidva_4 wreu friotabidva_3 cv friotabidva_4 wcel friotabidva_1 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_3 cab cund cfv cif friotabidva_2 friotabidva_3 friotabidva_4 wreu friotabidva_3 cv friotabidva_4 wcel friotabidva_2 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_3 cab cund cfv cif friotabidva_1 friotabidva_3 friotabidva_4 crio friotabidva_2 friotabidva_3 friotabidva_4 crio friotabidva_0 friotabidva_1 friotabidva_3 friotabidva_4 wreu friotabidva_3 cv friotabidva_4 wcel friotabidva_1 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_3 cab cund cfv cif friotabidva_1 friotabidva_3 friotabidva_4 wreu friotabidva_3 cv friotabidva_4 wcel friotabidva_2 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_3 cab cund cfv cif friotabidva_2 friotabidva_3 friotabidva_4 wreu friotabidva_3 cv friotabidva_4 wcel friotabidva_2 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_3 cab cund cfv cif friotabidva_0 friotabidva_1 friotabidva_3 friotabidva_4 wreu friotabidva_3 cv friotabidva_4 wcel friotabidva_1 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_2 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_3 cab cund cfv friotabidva_0 friotabidva_3 cv friotabidva_4 wcel friotabidva_1 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_2 wa friotabidva_3 cio wceq friotabidva_1 friotabidva_3 friotabidva_4 wreu friotabidva_0 friotabidva_3 cv friotabidva_4 wcel friotabidva_1 wa friotabidva_3 cv friotabidva_4 wcel friotabidva_2 wa friotabidva_3 friotabidva_0 friotabidva_3 cv friotabidva_4 wcel friotabidva_1 friotabidva_2 eriotabidva_0 pm5.32da iotabidv adantr ifeq1da friotabidva_0 friotabidva_1 friotabidva_3 friotabidva_4 wreu friotabidva_2 friotabidva_3 friotabidva_4 wreu friotabidva_3 cv friotabidva_4 wcel friotabidva_2 wa friotabidva_3 cio friotabidva_3 cv friotabidva_4 wcel friotabidva_3 cab cund cfv friotabidva_0 friotabidva_1 friotabidva_2 friotabidva_3 friotabidva_4 eriotabidva_0 reubidva ifbid eqtrd friotabidva_1 friotabidva_3 friotabidva_4 df-riota friotabidva_2 friotabidva_3 friotabidva_4 df-riota 3eqtr4g $.
$}
$( Equivalent wff's yield equal restricted iotas (inference rule).
       ( ~ rabbiia analog.)  (Contributed by NM, 16-Jan-2012.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	friotabiia_0 $f wff ph $.
	friotabiia_1 $f wff ps $.
	friotabiia_2 $f set x $.
	friotabiia_3 $f class A $.
	eriotabiia_0 $e |- ( x e. A -> ( ph <-> ps ) ) $.
	riotabiia $p |- ( iota_ x e. A ph ) = ( iota_ x e. A ps ) $= cvv cvv wceq friotabiia_0 friotabiia_2 friotabiia_3 crio friotabiia_1 friotabiia_2 friotabiia_3 crio wceq cvv eqid cvv cvv wceq friotabiia_0 friotabiia_1 friotabiia_2 friotabiia_3 friotabiia_2 cv friotabiia_3 wcel friotabiia_0 friotabiia_1 wb cvv cvv wceq eriotabiia_0 adantl riotabidva ax-mp $.
$}
$( Property of restricted iota.  Compare ~ iota1 .  (Contributed by Mario
       Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	friota1_0 $f wff ph $.
	friota1_1 $f set x $.
	friota1_2 $f class A $.
	riota1 $p |- ( E! x e. A ph -> ( ( x e. A /\ ph ) <-> ( iota_ x e. A ph ) = x ) ) $= friota1_0 friota1_1 friota1_2 wreu friota1_1 cv friota1_2 wcel friota1_0 wa friota1_1 cv friota1_2 wcel friota1_0 wa friota1_1 cio friota1_1 cv wceq friota1_0 friota1_1 friota1_2 crio friota1_1 cv wceq friota1_0 friota1_1 friota1_2 wreu friota1_1 cv friota1_2 wcel friota1_0 wa friota1_1 weu friota1_1 cv friota1_2 wcel friota1_0 wa friota1_1 cv friota1_2 wcel friota1_0 wa friota1_1 cio friota1_1 cv wceq wb friota1_0 friota1_1 friota1_2 df-reu friota1_1 cv friota1_2 wcel friota1_0 wa friota1_1 iota1 sylbi friota1_0 friota1_1 friota1_2 wreu friota1_0 friota1_1 friota1_2 crio friota1_1 cv friota1_2 wcel friota1_0 wa friota1_1 cio friota1_1 cv friota1_0 friota1_1 friota1_2 riotaiota eqeq1d bitr4d $.
$}
$( Property of iota.  (Contributed by NM, 23-Aug-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	friota1a_0 $f wff ph $.
	friota1a_1 $f set x $.
	friota1a_2 $f class A $.
	riota1a $p |- ( ( x e. A /\ E! x e. A ph ) -> ( ph <-> ( iota x ( x e. A /\ ph ) ) = x ) ) $= friota1a_1 cv friota1a_2 wcel friota1a_0 friota1a_1 cv friota1a_2 wcel friota1a_0 wa friota1a_0 friota1a_1 friota1a_2 wreu friota1a_1 cv friota1a_2 wcel friota1a_0 wa friota1a_1 cio friota1a_1 cv wceq friota1a_1 cv friota1a_2 wcel friota1a_0 ibar friota1a_0 friota1a_1 friota1a_2 wreu friota1a_1 cv friota1a_2 wcel friota1a_0 wa friota1a_1 weu friota1a_1 cv friota1a_2 wcel friota1a_0 wa friota1a_1 cv friota1a_2 wcel friota1a_0 wa friota1a_1 cio friota1a_1 cv wceq wb friota1a_0 friota1a_1 friota1a_2 df-reu friota1a_1 cv friota1a_2 wcel friota1a_0 wa friota1a_1 iota1 sylbi sylan9bb $.
$}
$( A deduction version of ~ riota2f .  (Contributed by NM, 17-Feb-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	friota2df_0 $f wff ph $.
	friota2df_1 $f wff ps $.
	friota2df_2 $f wff ch $.
	friota2df_3 $f set x $.
	friota2df_4 $f class A $.
	friota2df_5 $f class B $.
	eriota2df_0 $e |- F/ x ph $.
	eriota2df_1 $e |- ( ph -> F/_ x B ) $.
	eriota2df_2 $e |- ( ph -> F/ x ch ) $.
	eriota2df_3 $e |- ( ph -> B e. A ) $.
	eriota2df_4 $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
	riota2df $p |- ( ( ph /\ E! x e. A ps ) -> ( ch <-> ( iota_ x e. A ps ) = B ) ) $= friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_2 friota2df_3 cv friota2df_4 wcel friota2df_1 wa friota2df_3 cio friota2df_5 wceq friota2df_1 friota2df_3 friota2df_4 crio friota2df_5 wceq friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_3 cv friota2df_4 wcel friota2df_1 wa friota2df_2 friota2df_3 friota2df_5 friota2df_4 friota2df_0 friota2df_5 friota2df_4 wcel friota2df_1 friota2df_3 friota2df_4 wreu eriota2df_3 adantr friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_1 friota2df_3 friota2df_4 wreu friota2df_3 cv friota2df_4 wcel friota2df_1 wa friota2df_3 weu friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu simpr friota2df_1 friota2df_3 friota2df_4 df-reu sylib friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_3 cv friota2df_5 wceq wa friota2df_1 friota2df_3 cv friota2df_4 wcel friota2df_1 wa friota2df_2 friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_3 cv friota2df_5 wceq wa friota2df_3 cv friota2df_4 wcel friota2df_1 friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_3 cv friota2df_5 wceq wa friota2df_3 cv friota2df_5 friota2df_4 friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_3 cv friota2df_5 wceq simpr friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_5 friota2df_4 wcel friota2df_3 cv friota2df_5 wceq friota2df_0 friota2df_5 friota2df_4 wcel friota2df_1 friota2df_3 friota2df_4 wreu eriota2df_3 adantr adantr eqeltrd biantrurd friota2df_0 friota2df_3 cv friota2df_5 wceq friota2df_1 friota2df_2 wb friota2df_1 friota2df_3 friota2df_4 wreu eriota2df_4 adantlr bitr3d friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu friota2df_3 eriota2df_0 friota2df_1 friota2df_3 friota2df_4 nfreu1 nfan friota2df_0 friota2df_2 friota2df_3 wnf friota2df_1 friota2df_3 friota2df_4 wreu eriota2df_2 adantr friota2df_0 friota2df_3 friota2df_5 wnfc friota2df_1 friota2df_3 friota2df_4 wreu eriota2df_1 adantr iota2df friota2df_0 friota2df_1 friota2df_3 friota2df_4 wreu wa friota2df_1 friota2df_3 friota2df_4 crio friota2df_3 cv friota2df_4 wcel friota2df_1 wa friota2df_3 cio friota2df_5 friota2df_1 friota2df_3 friota2df_4 wreu friota2df_1 friota2df_3 friota2df_4 crio friota2df_3 cv friota2df_4 wcel friota2df_1 wa friota2df_3 cio wceq friota2df_0 friota2df_1 friota2df_3 friota2df_4 riotaiota adantl eqeq1d bitr4d $.
$}
$( This theorem shows a condition that allows us to represent a descriptor
       with a class expression ` B ` .  (Contributed by NM, 23-Aug-2011.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	friota2f_0 $f wff ph $.
	friota2f_1 $f wff ps $.
	friota2f_2 $f set x $.
	friota2f_3 $f class A $.
	friota2f_4 $f class B $.
	eriota2f_0 $e |- F/_ x B $.
	eriota2f_1 $e |- F/ x ps $.
	eriota2f_2 $e |- ( x = B -> ( ph <-> ps ) ) $.
	riota2f $p |- ( ( B e. A /\ E! x e. A ph ) -> ( ps <-> ( iota_ x e. A ph ) = B ) ) $= friota2f_4 friota2f_3 wcel friota2f_0 friota2f_1 friota2f_2 friota2f_3 friota2f_4 friota2f_2 friota2f_4 friota2f_3 eriota2f_0 nfel1 friota2f_2 friota2f_4 wnfc friota2f_4 friota2f_3 wcel eriota2f_0 a1i friota2f_1 friota2f_2 wnf friota2f_4 friota2f_3 wcel eriota2f_1 a1i friota2f_4 friota2f_3 wcel id friota2f_2 cv friota2f_4 wceq friota2f_0 friota2f_1 wb friota2f_4 friota2f_3 wcel eriota2f_2 adantl riota2df $.
$}
$( This theorem shows a condition that allows us to represent a descriptor
       with a class expression ` B ` .  (Contributed by NM, 23-Aug-2011.)
       (Revised by Mario Carneiro, 10-Dec-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x ps $.
	$d x A $.
	$d x B $.
	friota2_0 $f wff ph $.
	friota2_1 $f wff ps $.
	friota2_2 $f set x $.
	friota2_3 $f class A $.
	friota2_4 $f class B $.
	eriota2_0 $e |- ( x = B -> ( ph <-> ps ) ) $.
	riota2 $p |- ( ( B e. A /\ E! x e. A ph ) -> ( ps <-> ( iota_ x e. A ph ) = B ) ) $= friota2_0 friota2_1 friota2_2 friota2_3 friota2_4 friota2_2 friota2_4 nfcv friota2_1 friota2_2 nfv eriota2_0 riota2f $.
$}
$( Properties of a restricted definite description operator.  Todo: can
       some uses of ~ riota2f be shortened with this?  (Contributed by NM,
       23-Nov-2013.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	friotaprop_0 $f wff ph $.
	friotaprop_1 $f wff ps $.
	friotaprop_2 $f set x $.
	friotaprop_3 $f class A $.
	friotaprop_4 $f class B $.
	eriotaprop_0 $e |- F/ x ps $.
	eriotaprop_1 $e |- B = ( iota_ x e. A ph ) $.
	eriotaprop_2 $e |- ( x = B -> ( ph <-> ps ) ) $.
	riotaprop $p |- ( E! x e. A ph -> ( B e. A /\ ps ) ) $= friotaprop_0 friotaprop_2 friotaprop_3 wreu friotaprop_4 friotaprop_3 wcel friotaprop_1 friotaprop_0 friotaprop_2 friotaprop_3 wreu friotaprop_4 friotaprop_0 friotaprop_2 friotaprop_3 crio friotaprop_3 eriotaprop_1 friotaprop_0 friotaprop_2 friotaprop_3 riotacl syl5eqel friotaprop_4 friotaprop_3 wcel friotaprop_0 friotaprop_2 friotaprop_3 wreu friotaprop_1 friotaprop_0 friotaprop_2 friotaprop_3 wreu friotaprop_4 friotaprop_0 friotaprop_2 friotaprop_3 crio friotaprop_3 eriotaprop_1 friotaprop_0 friotaprop_2 friotaprop_3 riotacl syl5eqel friotaprop_4 friotaprop_3 wcel friotaprop_0 friotaprop_2 friotaprop_3 wreu wa friotaprop_1 friotaprop_0 friotaprop_2 friotaprop_3 crio friotaprop_4 wceq friotaprop_4 friotaprop_0 friotaprop_2 friotaprop_3 crio eriotaprop_1 eqcomi friotaprop_0 friotaprop_1 friotaprop_2 friotaprop_3 friotaprop_4 friotaprop_2 friotaprop_4 friotaprop_0 friotaprop_2 friotaprop_3 crio eriotaprop_1 friotaprop_0 friotaprop_2 friotaprop_3 nfriota1 nfcxfr eriotaprop_0 eriotaprop_2 riota2f mpbiri mpancom jca $.
$}
$( A method for computing restricted iota.  (Contributed by NM,
       16-Apr-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d y B $.
	$d x y ph $.
	$d y ps $.
	iriota5f_0 $f set y $.
	friota5f_0 $f wff ph $.
	friota5f_1 $f wff ps $.
	friota5f_2 $f set x $.
	friota5f_3 $f class A $.
	friota5f_4 $f class B $.
	eriota5f_0 $e |- ( ph -> F/_ x B ) $.
	eriota5f_1 $e |- ( ph -> B e. A ) $.
	eriota5f_2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) ) $.
	riota5f $p |- ( ph -> ( iota_ x e. A ps ) = B ) $= friota5f_0 friota5f_1 friota5f_2 cv friota5f_4 wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio friota5f_4 wceq friota5f_0 friota5f_1 friota5f_2 cv friota5f_4 wceq wb friota5f_2 friota5f_3 eriota5f_2 ralrimiva friota5f_0 friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq wi iriota5f_0 friota5f_4 wsbc friota5f_1 friota5f_2 cv friota5f_4 wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio friota5f_4 wceq wi friota5f_0 friota5f_4 friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq wi iriota5f_0 friota5f_3 wral friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq wi iriota5f_0 friota5f_4 wsbc eriota5f_1 friota5f_0 friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq wi iriota5f_0 friota5f_3 friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa wtru friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa a1tru friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_1 friota5f_2 friota5f_3 wreu wtru friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq wb iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa friota5f_1 friota5f_2 friota5f_3 wreu friota5f_0 friota5f_1 friota5f_2 friota5f_3 iriota5f_0 cv reu6i adantl friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_1 wtru friota5f_2 friota5f_3 iriota5f_0 cv friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa friota5f_2 friota5f_0 friota5f_2 nfv iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_2 iriota5f_0 cv friota5f_3 wcel friota5f_2 nfv friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 nfra1 nfan nfan friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_2 iriota5f_0 cv nfcvd friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa wtru friota5f_2 nfvd friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral simprl friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_2 cv iriota5f_0 cv wceq wa friota5f_1 wtru friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_2 cv iriota5f_0 cv wceq wa friota5f_1 friota5f_2 cv iriota5f_0 cv wceq friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_2 cv iriota5f_0 cv wceq simpr friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_2 cv iriota5f_0 cv wceq wa friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_2 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_2 cv iriota5f_0 cv wceq simplrr friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_2 cv iriota5f_0 cv wceq wa friota5f_2 cv iriota5f_0 cv friota5f_3 friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_2 cv iriota5f_0 cv wceq simpr friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_2 cv iriota5f_0 cv wceq simplrl eqeltrd friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 rsp sylc mpbird friota5f_0 iriota5f_0 cv friota5f_3 wcel friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral wa wa friota5f_2 cv iriota5f_0 cv wceq wa a1tru 2thd riota2df mpdan mpbid expr ralrimiva friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq wi iriota5f_0 friota5f_4 friota5f_3 rspsbc sylc friota5f_0 friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq wi friota5f_1 friota5f_2 cv friota5f_4 wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio friota5f_4 wceq wi iriota5f_0 friota5f_4 friota5f_3 eriota5f_1 friota5f_0 iriota5f_0 cv friota5f_4 wceq wa friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 cv friota5f_4 wceq wb friota5f_2 friota5f_3 wral friota5f_1 friota5f_2 friota5f_3 crio iriota5f_0 cv wceq friota5f_1 friota5f_2 friota5f_3 crio friota5f_4 wceq friota5f_0 iriota5f_0 cv friota5f_4 wceq wa friota5f_1 friota5f_2 cv iriota5f_0 cv wceq wb friota5f_1 friota5f_2 cv friota5f_4 wceq wb friota5f_2 friota5f_3 friota5f_0 iriota5f_0 cv friota5f_4 wceq friota5f_2 friota5f_0 friota5f_2 nfv friota5f_0 friota5f_2 iriota5f_0 cv friota5f_4 friota5f_0 friota5f_2 iriota5f_0 cv nfcvd eriota5f_0 nfeqd nfan1 friota5f_0 iriota5f_0 cv friota5f_4 wceq wa friota5f_2 cv iriota5f_0 cv wceq friota5f_2 cv friota5f_4 wceq friota5f_1 friota5f_0 iriota5f_0 cv friota5f_4 wceq wa iriota5f_0 cv friota5f_4 friota5f_2 cv friota5f_0 iriota5f_0 cv friota5f_4 wceq simpr eqeq2d bibi2d ralbid friota5f_0 iriota5f_0 cv friota5f_4 wceq wa iriota5f_0 cv friota5f_4 friota5f_1 friota5f_2 friota5f_3 crio friota5f_0 iriota5f_0 cv friota5f_4 wceq simpr eqeq2d imbi12d sbcied mpbid mpd $.
$}
$( A method for computing restricted iota.  (Contributed by NM,
       20-Oct-2011.)  (Revised by Mario Carneiro, 6-Dec-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	$d x ph $.
	friota5_0 $f wff ph $.
	friota5_1 $f wff ps $.
	friota5_2 $f set x $.
	friota5_3 $f class A $.
	friota5_4 $f class B $.
	eriota5_0 $e |- ( ph -> B e. A ) $.
	eriota5_1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) ) $.
	riota5 $p |- ( ph -> ( iota_ x e. A ps ) = B ) $= friota5_0 friota5_1 friota5_2 friota5_3 friota5_4 friota5_0 friota5_2 friota5_4 nfcvd eriota5_0 eriota5_1 riota5f $.
$}
$( A method for computing restricted iota.  (Contributed by NM,
       20-Oct-2011.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	$d x ph $.
	friota5OLD_0 $f wff ph $.
	friota5OLD_1 $f wff ps $.
	friota5OLD_2 $f set x $.
	friota5OLD_3 $f class A $.
	friota5OLD_4 $f class B $.
	eriota5OLD_0 $e |- ( ( ph /\ B e. A /\ x e. A ) -> ( ps <-> x = B ) ) $.
	riota5OLD $p |- ( ( ph /\ B e. A ) -> ( iota_ x e. A ps ) = B ) $= friota5OLD_0 friota5OLD_4 friota5OLD_3 wcel wa friota5OLD_1 friota5OLD_2 friota5OLD_3 friota5OLD_4 friota5OLD_0 friota5OLD_4 friota5OLD_3 wcel simpr friota5OLD_0 friota5OLD_4 friota5OLD_3 wcel friota5OLD_2 cv friota5OLD_3 wcel friota5OLD_1 friota5OLD_2 cv friota5OLD_4 wceq wb eriota5OLD_0 3expa riota5 $.
$}
$( Restriction of a unique element to a smaller class.  (Contributed by NM,
       21-Aug-2011.)  (Revised by NM, 22-Mar-2013.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	friotass2_0 $f wff ph $.
	friotass2_1 $f wff ps $.
	friotass2_2 $f set x $.
	friotass2_3 $f class A $.
	friotass2_4 $f class B $.
	riotass2 $p |- ( ( ( A C_ B /\ A. x e. A ( ph -> ps ) ) /\ ( E. x e. A ph /\ E! x e. B ps ) ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ps ) ) $= friotass2_3 friotass2_4 wss friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral wa friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu wa wa friotass2_1 friotass2_2 friotass2_4 crio friotass2_0 friotass2_2 friotass2_3 crio friotass2_3 friotass2_4 wss friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral wa friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu wa wa friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_1 friotass2_2 friotass2_4 crio friotass2_0 friotass2_2 friotass2_3 crio wceq friotass2_3 friotass2_4 wss friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral wa friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu wa wa friotass2_0 friotass2_2 friotass2_3 wreu friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_0 friotass2_1 friotass2_2 friotass2_3 friotass2_4 reuss2 friotass2_3 friotass2_4 wss friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu wa simplr friotass2_0 friotass2_2 friotass2_3 wreu friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral friotass2_0 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_0 friotass2_2 friotass2_3 riotasbc friotass2_0 friotass2_2 friotass2_3 wreu friotass2_0 friotass2_2 friotass2_3 crio friotass2_3 wcel friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral friotass2_0 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc wi wi friotass2_0 friotass2_2 friotass2_3 riotacl friotass2_0 friotass2_2 friotass2_3 crio friotass2_3 wcel friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral friotass2_0 friotass2_1 wi friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_0 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc wi friotass2_0 friotass2_1 wi friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio friotass2_3 rspsbc friotass2_0 friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio friotass2_3 sbcimg sylibd syl mpid sylc friotass2_3 friotass2_4 wss friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral wa friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu wa wa friotass2_0 friotass2_2 friotass2_3 crio friotass2_4 wcel friotass2_1 friotass2_2 friotass2_4 wreu friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_1 friotass2_2 friotass2_4 crio friotass2_0 friotass2_2 friotass2_3 crio wceq wb friotass2_3 friotass2_4 wss friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral wa friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu wa wa friotass2_0 friotass2_2 friotass2_3 crio friotass2_3 wcel friotass2_0 friotass2_2 friotass2_3 crio friotass2_4 wcel friotass2_3 friotass2_4 wss friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral wa friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu wa wa friotass2_0 friotass2_2 friotass2_3 wreu friotass2_0 friotass2_2 friotass2_3 crio friotass2_3 wcel friotass2_0 friotass2_1 friotass2_2 friotass2_3 friotass2_4 reuss2 friotass2_0 friotass2_2 friotass2_3 riotacl syl friotass2_3 friotass2_4 wss friotass2_0 friotass2_2 friotass2_3 crio friotass2_3 wcel friotass2_0 friotass2_2 friotass2_3 crio friotass2_4 wcel wi friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu wa friotass2_3 friotass2_4 friotass2_0 friotass2_2 friotass2_3 crio ssel ad2antrr mpd friotass2_3 friotass2_4 wss friotass2_0 friotass2_1 wi friotass2_2 friotass2_3 wral wa friotass2_0 friotass2_2 friotass2_3 wrex friotass2_1 friotass2_2 friotass2_4 wreu simprr friotass2_1 friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio wsbc friotass2_2 friotass2_4 friotass2_0 friotass2_2 friotass2_3 crio friotass2_0 friotass2_2 friotass2_3 nfriota1 friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio friotass2_0 friotass2_2 friotass2_3 nfriota1 nfsbc1 friotass2_1 friotass2_2 friotass2_0 friotass2_2 friotass2_3 crio sbceq1a riota2f syl2anc mpbid eqcomd $.
$}
$( Restriction of a unique element to a smaller class.  (Contributed by NM,
       19-Oct-2005.)  (Revised by Mario Carneiro, 24-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	friotass_0 $f wff ph $.
	friotass_1 $f set x $.
	friotass_2 $f class A $.
	friotass_3 $f class B $.
	riotass $p |- ( ( A C_ B /\ E. x e. A ph /\ E! x e. B ph ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ph ) ) $= friotass_2 friotass_3 wss friotass_0 friotass_1 friotass_2 wrex friotass_0 friotass_1 friotass_3 wreu w3a friotass_0 friotass_1 friotass_3 crio friotass_0 friotass_1 friotass_2 crio friotass_2 friotass_3 wss friotass_0 friotass_1 friotass_2 wrex friotass_0 friotass_1 friotass_3 wreu w3a friotass_0 friotass_1 friotass_0 friotass_1 friotass_2 crio wsbc friotass_0 friotass_1 friotass_3 crio friotass_0 friotass_1 friotass_2 crio wceq friotass_2 friotass_3 wss friotass_0 friotass_1 friotass_2 wrex friotass_0 friotass_1 friotass_3 wreu w3a friotass_0 friotass_1 friotass_2 wreu friotass_0 friotass_1 friotass_0 friotass_1 friotass_2 crio wsbc friotass_0 friotass_1 friotass_2 friotass_3 reuss friotass_0 friotass_1 friotass_2 riotasbc syl friotass_2 friotass_3 wss friotass_0 friotass_1 friotass_2 wrex friotass_0 friotass_1 friotass_3 wreu w3a friotass_0 friotass_1 friotass_2 crio friotass_3 wcel friotass_0 friotass_1 friotass_3 wreu friotass_0 friotass_1 friotass_0 friotass_1 friotass_2 crio wsbc friotass_0 friotass_1 friotass_3 crio friotass_0 friotass_1 friotass_2 crio wceq wb friotass_2 friotass_3 wss friotass_0 friotass_1 friotass_2 wrex friotass_0 friotass_1 friotass_3 wreu w3a friotass_2 friotass_3 friotass_0 friotass_1 friotass_2 crio friotass_2 friotass_3 wss friotass_0 friotass_1 friotass_2 wrex friotass_0 friotass_1 friotass_3 wreu simp1 friotass_2 friotass_3 wss friotass_0 friotass_1 friotass_2 wrex friotass_0 friotass_1 friotass_3 wreu w3a friotass_0 friotass_1 friotass_2 wreu friotass_0 friotass_1 friotass_2 crio friotass_2 wcel friotass_0 friotass_1 friotass_2 friotass_3 reuss friotass_0 friotass_1 friotass_2 riotacl syl sseldd friotass_2 friotass_3 wss friotass_0 friotass_1 friotass_2 wrex friotass_0 friotass_1 friotass_3 wreu simp3 friotass_0 friotass_0 friotass_1 friotass_0 friotass_1 friotass_2 crio wsbc friotass_1 friotass_3 friotass_0 friotass_1 friotass_2 crio friotass_0 friotass_1 friotass_2 nfriota1 friotass_0 friotass_1 friotass_0 friotass_1 friotass_2 crio friotass_0 friotass_1 friotass_2 nfriota1 nfsbc1 friotass_0 friotass_1 friotass_0 friotass_1 friotass_2 crio sbceq1a riota2f syl2anc mpbid eqcomd $.
$}
$( Restriction of a unique element to a smaller class.  (Contributed by NM,
       19-Feb-2006.)  (Revised by NM, 16-Jun-2017.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fmoriotass_0 $f wff ph $.
	fmoriotass_1 $f set x $.
	fmoriotass_2 $f class A $.
	fmoriotass_3 $f class B $.
	moriotass $p |- ( ( A C_ B /\ E. x e. A ph /\ E* x e. B ph ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ph ) ) $= fmoriotass_2 fmoriotass_3 wss fmoriotass_0 fmoriotass_1 fmoriotass_2 wrex fmoriotass_0 fmoriotass_1 fmoriotass_3 wrmo fmoriotass_0 fmoriotass_1 fmoriotass_3 wreu fmoriotass_0 fmoriotass_1 fmoriotass_2 crio fmoriotass_0 fmoriotass_1 fmoriotass_3 crio wceq fmoriotass_2 fmoriotass_3 wss fmoriotass_0 fmoriotass_1 fmoriotass_2 wrex fmoriotass_0 fmoriotass_1 fmoriotass_3 wrmo w3a fmoriotass_0 fmoriotass_1 fmoriotass_3 wrex fmoriotass_0 fmoriotass_1 fmoriotass_3 wrmo fmoriotass_0 fmoriotass_1 fmoriotass_3 wreu fmoriotass_2 fmoriotass_3 wss fmoriotass_0 fmoriotass_1 fmoriotass_2 wrex fmoriotass_0 fmoriotass_1 fmoriotass_3 wrex fmoriotass_0 fmoriotass_1 fmoriotass_3 wrmo fmoriotass_2 fmoriotass_3 wss fmoriotass_0 fmoriotass_1 fmoriotass_2 wrex fmoriotass_0 fmoriotass_1 fmoriotass_3 wrex fmoriotass_0 fmoriotass_1 fmoriotass_2 fmoriotass_3 ssrexv imp 3adant3 fmoriotass_2 fmoriotass_3 wss fmoriotass_0 fmoriotass_1 fmoriotass_2 wrex fmoriotass_0 fmoriotass_1 fmoriotass_3 wrmo simp3 fmoriotass_0 fmoriotass_1 fmoriotass_3 reu5 sylanbrc fmoriotass_0 fmoriotass_1 fmoriotass_2 fmoriotass_3 riotass syld3an3 $.
$}
$( A restricted class abstraction with a unique member can be expressed as
       a singleton.  (Contributed by NM, 30-May-2006.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	fsnriota_0 $f wff ph $.
	fsnriota_1 $f set x $.
	fsnriota_2 $f class A $.
	snriota $p |- ( E! x e. A ph -> { x e. A | ph } = { ( iota_ x e. A ph ) } ) $= fsnriota_0 fsnriota_1 fsnriota_2 wreu fsnriota_0 fsnriota_1 fsnriota_2 crab fsnriota_1 cv fsnriota_2 wcel fsnriota_0 wa fsnriota_1 cio csn fsnriota_0 fsnriota_1 fsnriota_2 crio csn fsnriota_0 fsnriota_1 fsnriota_2 wreu fsnriota_0 fsnriota_1 fsnriota_2 crab fsnriota_1 cv fsnriota_2 wcel fsnriota_0 wa fsnriota_1 cab fsnriota_1 cv fsnriota_2 wcel fsnriota_0 wa fsnriota_1 cio csn fsnriota_0 fsnriota_1 fsnriota_2 df-rab fsnriota_0 fsnriota_1 fsnriota_2 wreu fsnriota_1 cv fsnriota_2 wcel fsnriota_0 wa fsnriota_1 weu fsnriota_1 cv fsnriota_2 wcel fsnriota_0 wa fsnriota_1 cab fsnriota_1 cv fsnriota_2 wcel fsnriota_0 wa fsnriota_1 cio csn wceq fsnriota_0 fsnriota_1 fsnriota_2 df-reu fsnriota_1 cv fsnriota_2 wcel fsnriota_0 wa fsnriota_1 sniota sylbi syl5eq fsnriota_0 fsnriota_1 fsnriota_2 wreu fsnriota_0 fsnriota_1 fsnriota_2 crio fsnriota_1 cv fsnriota_2 wcel fsnriota_0 wa fsnriota_1 cio fsnriota_0 fsnriota_1 fsnriota_2 riotaiota sneqd eqtr4d $.
$}
$( Change the variable ` x ` in the expression for "the unique ` x ` such
       that ` ps ` " to another variable ` y ` contained in expression ` B ` .
       Use ~ reuhypd to eliminate the last hypothesis.  (Contributed by NM,
       16-Jan-2012.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x B $.
	$d x C $.
	$d x y A $.
	$d x y ph $.
	$d ps y $.
	$d ch x $.
	friotaxfrd_0 $f wff ph $.
	friotaxfrd_1 $f wff ps $.
	friotaxfrd_2 $f wff ch $.
	friotaxfrd_3 $f set x $.
	friotaxfrd_4 $f set y $.
	friotaxfrd_5 $f class A $.
	friotaxfrd_6 $f class B $.
	friotaxfrd_7 $f class C $.
	eriotaxfrd_0 $e |- F/_ y C $.
	eriotaxfrd_1 $e |- ( ( ph /\ y e. A ) -> B e. A ) $.
	eriotaxfrd_2 $e |- ( ( ph /\ ( iota_ y e. A ch ) e. A ) -> C e. A ) $.
	eriotaxfrd_3 $e |- ( x = B -> ( ps <-> ch ) ) $.
	eriotaxfrd_4 $e |- ( y = ( iota_ y e. A ch ) -> B = C ) $.
	eriotaxfrd_5 $e |- ( ( ph /\ x e. A ) -> E! y e. A x = B ) $.
	riotaxfrd $p |- ( ( ph /\ E! x e. A ps ) -> ( iota_ x e. A ps ) = C ) $= friotaxfrd_0 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu wa friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crio friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 friotaxfrd_5 crio friotaxfrd_7 friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 cv friotaxfrd_5 wcel friotaxfrd_1 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 rabid baib riotabiia friotaxfrd_0 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu wa friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 friotaxfrd_5 crio friotaxfrd_7 wceq friotaxfrd_0 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_0 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 wreu friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_0 friotaxfrd_1 friotaxfrd_2 friotaxfrd_3 friotaxfrd_4 friotaxfrd_6 friotaxfrd_5 eriotaxfrd_1 eriotaxfrd_5 eriotaxfrd_3 reuxfrd friotaxfrd_0 friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 wreu friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_0 friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 wreu wa friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crio friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crab wcel friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 wreu friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crio friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crab wcel friotaxfrd_0 friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 riotacl2 adantl friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 wreu friotaxfrd_0 friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crio friotaxfrd_5 wcel friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crio friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crab wcel wb friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 riotacl friotaxfrd_0 friotaxfrd_1 friotaxfrd_2 friotaxfrd_3 friotaxfrd_4 friotaxfrd_6 friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crio friotaxfrd_7 friotaxfrd_5 friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 nfriota1 eriotaxfrd_0 eriotaxfrd_1 eriotaxfrd_3 eriotaxfrd_4 rabxfrd sylan2 mpbird ex sylbid imp friotaxfrd_0 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu wa friotaxfrd_7 friotaxfrd_5 wcel friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 friotaxfrd_5 crio friotaxfrd_7 wceq wb friotaxfrd_0 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_7 friotaxfrd_5 wcel friotaxfrd_0 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 wreu friotaxfrd_7 friotaxfrd_5 wcel friotaxfrd_0 friotaxfrd_1 friotaxfrd_2 friotaxfrd_3 friotaxfrd_4 friotaxfrd_6 friotaxfrd_5 eriotaxfrd_1 eriotaxfrd_5 eriotaxfrd_3 reuxfrd friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 wreu friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crio friotaxfrd_5 wcel friotaxfrd_0 friotaxfrd_7 friotaxfrd_5 wcel friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 riotacl friotaxfrd_0 friotaxfrd_2 friotaxfrd_4 friotaxfrd_5 crio friotaxfrd_5 wcel friotaxfrd_7 friotaxfrd_5 wcel eriotaxfrd_2 ex syl5 sylbid imp friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_0 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 friotaxfrd_5 wreu friotaxfrd_1 friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 friotaxfrd_5 friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 cv friotaxfrd_5 wcel friotaxfrd_1 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 rabid baibr reubiia biimpi adantl friotaxfrd_3 cv friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab wcel friotaxfrd_3 friotaxfrd_5 friotaxfrd_7 friotaxfrd_3 friotaxfrd_7 nfcv friotaxfrd_3 friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 nfrab1 nfel2 friotaxfrd_3 cv friotaxfrd_7 friotaxfrd_1 friotaxfrd_3 friotaxfrd_5 crab eleq1 riota2f syl2anc mpbid syl5eqr $.
$}
$( Specify the same property in two ways when class ` B ( y ) ` is
       single-valued.  (Contributed by NM, 1-Nov-2010.)  (Proof shortened by
       Mario Carneiro, 24-Dec-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d x y z A $.
	$d x z B $.
	ieusvobj2_0 $f set z $.
	feusvobj2_0 $f set x $.
	feusvobj2_1 $f set y $.
	feusvobj2_2 $f class A $.
	feusvobj2_3 $f class B $.
	eeusvobj2_0 $e |- B e. _V $.
	eusvobj2 $p |- ( E! x E. y e. A x = B -> ( E. y e. A x = B <-> A. y e. A x = B ) ) $= feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 weu feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wral feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 weu feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn wceq ieusvobj2_0 wex feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wral wi feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 ieusvobj2_0 euabsn2 feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn wceq feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wral wi ieusvobj2_0 feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn wceq feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cv ieusvobj2_0 cv wceq feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wral feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn wceq feusvobj2_0 cv feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab wcel feusvobj2_0 cv ieusvobj2_0 cv csn wcel feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cv ieusvobj2_0 cv wceq feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn feusvobj2_0 cv eleq2 feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 abid feusvobj2_0 ieusvobj2_0 cv elsn 3bitr3g feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn wceq feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wral feusvobj2_0 cv ieusvobj2_0 cv wceq ieusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wral feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn wceq ieusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 feusvobj2_1 feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_1 feusvobj2_0 feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 nfre1 nfab nfeq1 feusvobj2_1 cv feusvobj2_2 wcel feusvobj2_3 feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab wcel feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn wceq ieusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_0 feusvobj2_2 feusvobj2_3 eeusvobj2_0 elabrex feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn wceq feusvobj2_3 feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab wcel feusvobj2_3 ieusvobj2_0 cv csn wcel ieusvobj2_0 cv feusvobj2_3 wceq feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cab ieusvobj2_0 cv csn feusvobj2_3 eleq2 feusvobj2_3 ieusvobj2_0 cv csn wcel feusvobj2_3 ieusvobj2_0 cv wceq ieusvobj2_0 cv feusvobj2_3 wceq feusvobj2_3 ieusvobj2_0 cv eeusvobj2_0 elsnc feusvobj2_3 ieusvobj2_0 cv eqcom bitri syl6bb syl5ib ralrimi feusvobj2_0 cv ieusvobj2_0 cv wceq feusvobj2_0 cv feusvobj2_3 wceq ieusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 feusvobj2_0 cv ieusvobj2_0 cv feusvobj2_3 eqeq1 ralbidv syl5ibrcom sylbid exlimiv sylbi feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 weu feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 wex feusvobj2_2 c0 wne feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wral feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex wi feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 euex feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_2 c0 wne feusvobj2_0 feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 rexn0 exlimiv feusvobj2_2 c0 wne feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wral feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 wrex feusvobj2_0 cv feusvobj2_3 wceq feusvobj2_1 feusvobj2_2 r19.2z ex 3syl impbid $.
$}
$( Specify the same object in two ways when class ` B ( y ) ` is
       single-valued.  (Contributed by NM, 1-Nov-2010.)  (Proof shortened by
       Mario Carneiro, 19-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d x B $.
	feusvobj1_0 $f set x $.
	feusvobj1_1 $f set y $.
	feusvobj1_2 $f class A $.
	feusvobj1_3 $f class B $.
	eeusvobj1_0 $e |- B e. _V $.
	eusvobj1 $p |- ( E! x E. y e. A x = B -> ( iota x E. y e. A x = B ) = ( iota x A. y e. A x = B ) ) $= feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wrex feusvobj1_0 weu feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wrex feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wral wb feusvobj1_0 wal feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wrex feusvobj1_0 cio feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wral feusvobj1_0 cio wceq feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wrex feusvobj1_0 weu feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wrex feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wral wb feusvobj1_0 feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wrex feusvobj1_0 nfeu1 feusvobj1_0 feusvobj1_1 feusvobj1_2 feusvobj1_3 eeusvobj1_0 eusvobj2 alrimi feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wrex feusvobj1_0 cv feusvobj1_3 wceq feusvobj1_1 feusvobj1_2 wral feusvobj1_0 iotabi syl $.
$}
$( There is one domain element for each value of a one-to-one onto
       function.  (Contributed by NM, 26-May-2006.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x F $.
	ff1ofveu_0 $f set x $.
	ff1ofveu_1 $f class A $.
	ff1ofveu_2 $f class B $.
	ff1ofveu_3 $f class C $.
	ff1ofveu_4 $f class F $.
	f1ofveu $p |- ( ( F : A -1-1-onto-> B /\ C e. B ) -> E! x e. A ( F ` x ) = C ) $= ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_3 ff1ofveu_2 wcel wa ff1ofveu_0 cv ff1ofveu_4 cfv ff1ofveu_3 wceq ff1ofveu_0 ff1ofveu_1 wreu ff1ofveu_3 ff1ofveu_0 cv cop ff1ofveu_4 ccnv wcel ff1ofveu_0 ff1ofveu_1 wreu ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_2 ff1ofveu_1 ff1ofveu_4 ccnv wf ff1ofveu_3 ff1ofveu_2 wcel ff1ofveu_3 ff1ofveu_0 cv cop ff1ofveu_4 ccnv wcel ff1ofveu_0 ff1ofveu_1 wreu ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_2 ff1ofveu_1 ff1ofveu_4 ccnv wf1o ff1ofveu_2 ff1ofveu_1 ff1ofveu_4 ccnv wf ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 f1ocnv ff1ofveu_2 ff1ofveu_1 ff1ofveu_4 ccnv f1of syl ff1ofveu_0 ff1ofveu_2 ff1ofveu_1 ff1ofveu_3 ff1ofveu_4 ccnv feu sylan ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_3 ff1ofveu_2 wcel wa ff1ofveu_0 cv ff1ofveu_4 cfv ff1ofveu_3 wceq ff1ofveu_3 ff1ofveu_0 cv cop ff1ofveu_4 ccnv wcel ff1ofveu_0 ff1ofveu_1 ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_3 ff1ofveu_2 wcel ff1ofveu_0 cv ff1ofveu_1 wcel ff1ofveu_0 cv ff1ofveu_4 cfv ff1ofveu_3 wceq ff1ofveu_3 ff1ofveu_0 cv cop ff1ofveu_4 ccnv wcel wb ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_3 ff1ofveu_2 wcel ff1ofveu_0 cv ff1ofveu_1 wcel w3a ff1ofveu_0 cv ff1ofveu_4 cfv ff1ofveu_3 wceq ff1ofveu_3 ff1ofveu_4 ccnv cfv ff1ofveu_0 cv wceq ff1ofveu_3 ff1ofveu_0 cv cop ff1ofveu_4 ccnv wcel ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_0 cv ff1ofveu_1 wcel ff1ofveu_3 ff1ofveu_2 wcel ff1ofveu_0 cv ff1ofveu_4 cfv ff1ofveu_3 wceq ff1ofveu_3 ff1ofveu_4 ccnv cfv ff1ofveu_0 cv wceq wb ff1ofveu_1 ff1ofveu_2 ff1ofveu_0 cv ff1ofveu_3 ff1ofveu_4 f1ocnvfvb 3com23 ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_4 ccnv ff1ofveu_2 wfn ff1ofveu_3 ff1ofveu_2 wcel ff1ofveu_0 cv ff1ofveu_1 wcel ff1ofveu_3 ff1ofveu_4 ccnv cfv ff1ofveu_0 cv wceq ff1ofveu_3 ff1ofveu_0 cv cop ff1ofveu_4 ccnv wcel wb ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 wf1o ff1ofveu_4 ff1ofveu_1 wfn ff1ofveu_4 ccnv ff1ofveu_2 wfn ff1ofveu_1 ff1ofveu_2 ff1ofveu_4 dff1o4 simprbi ff1ofveu_4 ccnv ff1ofveu_2 wfn ff1ofveu_3 ff1ofveu_2 wcel ff1ofveu_3 ff1ofveu_4 ccnv cfv ff1ofveu_0 cv wceq ff1ofveu_3 ff1ofveu_0 cv cop ff1ofveu_4 ccnv wcel wb ff1ofveu_0 cv ff1ofveu_1 wcel ff1ofveu_2 ff1ofveu_3 ff1ofveu_0 cv ff1ofveu_4 ccnv fnopfvb 3adant3 syl3an1 bitrd 3expa reubidva mpbird $.
$}
$( Value of the converse of a one-to-one onto function.  (Contributed by
       NM, 26-May-2006.)  (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x F $.
	ff1ocnvfv3_0 $f set x $.
	ff1ocnvfv3_1 $f class A $.
	ff1ocnvfv3_2 $f class B $.
	ff1ocnvfv3_3 $f class C $.
	ff1ocnvfv3_4 $f class F $.
	f1ocnvfv3 $p |- ( ( F : A -1-1-onto-> B /\ C e. B ) -> ( `' F ` C ) = ( iota_ x e. A ( F ` x ) = C ) ) $= ff1ocnvfv3_1 ff1ocnvfv3_2 ff1ocnvfv3_4 wf1o ff1ocnvfv3_3 ff1ocnvfv3_2 wcel wa ff1ocnvfv3_0 cv ff1ocnvfv3_4 cfv ff1ocnvfv3_3 wceq ff1ocnvfv3_0 ff1ocnvfv3_1 crio ff1ocnvfv3_3 ff1ocnvfv3_4 ccnv cfv ff1ocnvfv3_1 ff1ocnvfv3_2 ff1ocnvfv3_4 wf1o ff1ocnvfv3_3 ff1ocnvfv3_2 wcel wa ff1ocnvfv3_0 cv ff1ocnvfv3_4 cfv ff1ocnvfv3_3 wceq ff1ocnvfv3_0 ff1ocnvfv3_1 ff1ocnvfv3_3 ff1ocnvfv3_4 ccnv cfv ff1ocnvfv3_1 ff1ocnvfv3_2 ff1ocnvfv3_3 ff1ocnvfv3_4 f1ocnvdm ff1ocnvfv3_1 ff1ocnvfv3_2 ff1ocnvfv3_4 wf1o ff1ocnvfv3_3 ff1ocnvfv3_2 wcel wa ff1ocnvfv3_0 cv ff1ocnvfv3_1 wcel wa ff1ocnvfv3_0 cv ff1ocnvfv3_4 cfv ff1ocnvfv3_3 wceq ff1ocnvfv3_3 ff1ocnvfv3_4 ccnv cfv ff1ocnvfv3_0 cv wceq ff1ocnvfv3_0 cv ff1ocnvfv3_3 ff1ocnvfv3_4 ccnv cfv wceq ff1ocnvfv3_1 ff1ocnvfv3_2 ff1ocnvfv3_4 wf1o ff1ocnvfv3_0 cv ff1ocnvfv3_1 wcel ff1ocnvfv3_3 ff1ocnvfv3_2 wcel ff1ocnvfv3_0 cv ff1ocnvfv3_4 cfv ff1ocnvfv3_3 wceq ff1ocnvfv3_3 ff1ocnvfv3_4 ccnv cfv ff1ocnvfv3_0 cv wceq wb ff1ocnvfv3_1 ff1ocnvfv3_2 ff1ocnvfv3_4 wf1o ff1ocnvfv3_0 cv ff1ocnvfv3_1 wcel ff1ocnvfv3_3 ff1ocnvfv3_2 wcel ff1ocnvfv3_0 cv ff1ocnvfv3_4 cfv ff1ocnvfv3_3 wceq ff1ocnvfv3_3 ff1ocnvfv3_4 ccnv cfv ff1ocnvfv3_0 cv wceq wb ff1ocnvfv3_1 ff1ocnvfv3_2 ff1ocnvfv3_0 cv ff1ocnvfv3_3 ff1ocnvfv3_4 f1ocnvfvb 3expa an32s ff1ocnvfv3_0 cv ff1ocnvfv3_3 ff1ocnvfv3_4 ccnv cfv eqcom syl6bbr riota5 eqcomd $.
$}
$( Restricted iota equals the undefined value of its domain of discourse
       ` A ` when not meaningful.  (Contributed by NM, 16-Jan-2012.)  (Revised
       by Mario Carneiro, 15-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	friotaund_0 $f wff ph $.
	friotaund_1 $f set x $.
	friotaund_2 $f class A $.
	riotaund $p |- ( -. E! x e. A ph -> ( iota_ x e. A ph ) = ( Undef ` A ) ) $= friotaund_0 friotaund_1 friotaund_2 wreu wn friotaund_0 friotaund_1 friotaund_2 wreu friotaund_1 cv friotaund_2 wcel friotaund_0 wa friotaund_1 cio friotaund_1 cv friotaund_2 wcel friotaund_1 cab cund cfv cif friotaund_1 cv friotaund_2 wcel friotaund_1 cab cund cfv friotaund_0 friotaund_1 friotaund_2 crio friotaund_2 cund cfv friotaund_0 friotaund_1 friotaund_2 wreu friotaund_1 cv friotaund_2 wcel friotaund_0 wa friotaund_1 cio friotaund_1 cv friotaund_2 wcel friotaund_1 cab cund cfv iffalse friotaund_0 friotaund_1 friotaund_2 df-riota friotaund_2 friotaund_1 cv friotaund_2 wcel friotaund_1 cab cund friotaund_1 cv friotaund_2 wcel friotaund_1 cab friotaund_2 friotaund_1 friotaund_2 abid2 eqcomi fveq2i 3eqtr4g $.
$}
$( For proper classes, restricted and unrestricted iota are the same.
       (Contributed by NM, 15-Sep-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	friotaprc_0 $f wff ph $.
	friotaprc_1 $f set x $.
	friotaprc_2 $f class A $.
	riotaprc $p |- ( -. A e. _V -> ( iota_ x e. A ph ) = ( iota x ( x e. A /\ ph ) ) ) $= friotaprc_2 cvv wcel wn friotaprc_0 friotaprc_1 friotaprc_2 wreu friotaprc_0 friotaprc_1 friotaprc_2 crio friotaprc_1 cv friotaprc_2 wcel friotaprc_0 wa friotaprc_1 cio wceq friotaprc_2 cvv wcel wn friotaprc_0 friotaprc_1 friotaprc_2 wreu wn friotaprc_0 friotaprc_1 friotaprc_2 crio friotaprc_1 cv friotaprc_2 wcel friotaprc_0 wa friotaprc_1 cio wceq friotaprc_2 cvv wcel wn friotaprc_0 friotaprc_1 friotaprc_2 wreu wn wa friotaprc_2 cund cfv c0 friotaprc_0 friotaprc_1 friotaprc_2 crio friotaprc_1 cv friotaprc_2 wcel friotaprc_0 wa friotaprc_1 cio friotaprc_2 cvv wcel wn friotaprc_2 cund cfv c0 wceq friotaprc_0 friotaprc_1 friotaprc_2 wreu wn friotaprc_2 cund fvprc adantr friotaprc_0 friotaprc_1 friotaprc_2 wreu wn friotaprc_0 friotaprc_1 friotaprc_2 crio friotaprc_2 cund cfv wceq friotaprc_2 cvv wcel wn friotaprc_0 friotaprc_1 friotaprc_2 riotaund adantl friotaprc_0 friotaprc_1 friotaprc_2 wreu wn friotaprc_1 cv friotaprc_2 wcel friotaprc_0 wa friotaprc_1 cio c0 wceq friotaprc_2 cvv wcel wn friotaprc_0 friotaprc_1 friotaprc_2 wreu friotaprc_1 cv friotaprc_2 wcel friotaprc_0 wa friotaprc_1 weu friotaprc_1 cv friotaprc_2 wcel friotaprc_0 wa friotaprc_1 cio c0 wceq friotaprc_0 friotaprc_1 friotaprc_2 df-reu friotaprc_1 cv friotaprc_2 wcel friotaprc_0 wa friotaprc_1 iotanul sylnbi adantl 3eqtr4d ex friotaprc_0 friotaprc_1 friotaprc_2 riotaiota pm2.61d2 $.
$}
$( The restricted iota class is limited in size by the base set.
       (Contributed by Mario Carneiro, 24-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	friotassuni_0 $f wff ph $.
	friotassuni_1 $f set x $.
	friotassuni_2 $f class A $.
	riotassuni $p |- ( iota_ x e. A ph ) C_ ( ~P U. A u. U. A ) $= friotassuni_0 friotassuni_1 friotassuni_2 wreu friotassuni_0 friotassuni_1 friotassuni_2 crio friotassuni_2 cuni cpw friotassuni_2 cuni cun wss friotassuni_0 friotassuni_1 friotassuni_2 wreu friotassuni_0 friotassuni_1 friotassuni_2 crio friotassuni_0 friotassuni_1 friotassuni_2 crab cuni friotassuni_2 cuni cpw friotassuni_2 cuni cun friotassuni_0 friotassuni_1 friotassuni_2 riotauni friotassuni_0 friotassuni_1 friotassuni_2 crab cuni friotassuni_2 cuni cpw friotassuni_2 cuni cun wss friotassuni_0 friotassuni_1 friotassuni_2 wreu friotassuni_0 friotassuni_1 friotassuni_2 crab cuni friotassuni_2 cuni friotassuni_2 cuni cpw friotassuni_2 cuni cun friotassuni_0 friotassuni_1 friotassuni_2 crab friotassuni_2 wss friotassuni_0 friotassuni_1 friotassuni_2 crab cuni friotassuni_2 cuni wss friotassuni_0 friotassuni_1 friotassuni_2 ssrab2 friotassuni_0 friotassuni_1 friotassuni_2 crab friotassuni_2 uniss ax-mp friotassuni_2 cuni friotassuni_2 cuni cpw ssun2 sstri a1i eqsstrd friotassuni_0 friotassuni_1 friotassuni_2 wreu wn friotassuni_0 friotassuni_1 friotassuni_2 crio friotassuni_2 cund cfv friotassuni_2 cuni cpw friotassuni_2 cuni cun friotassuni_0 friotassuni_1 friotassuni_2 riotaund friotassuni_0 friotassuni_1 friotassuni_2 wreu wn friotassuni_2 cvv wcel friotassuni_2 cund cfv friotassuni_2 cuni cpw friotassuni_2 cuni cun wss friotassuni_0 friotassuni_1 friotassuni_2 wreu wn friotassuni_2 cvv wcel wa friotassuni_2 cund cfv friotassuni_2 cuni cpw friotassuni_2 cuni cpw friotassuni_2 cuni cun friotassuni_2 cvv wcel friotassuni_2 cund cfv friotassuni_2 cuni cpw wceq friotassuni_0 friotassuni_1 friotassuni_2 wreu wn friotassuni_2 cvv undefval adantl friotassuni_2 cuni cpw friotassuni_2 cuni cpw friotassuni_2 cuni cun wss friotassuni_0 friotassuni_1 friotassuni_2 wreu wn friotassuni_2 cvv wcel wa friotassuni_2 cuni cpw friotassuni_2 cuni ssun1 a1i eqsstrd friotassuni_0 friotassuni_1 friotassuni_2 wreu wn friotassuni_2 cvv wcel wn wa friotassuni_2 cund cfv c0 friotassuni_2 cuni cpw friotassuni_2 cuni cun friotassuni_2 cvv wcel wn friotassuni_2 cund cfv c0 wceq friotassuni_0 friotassuni_1 friotassuni_2 wreu wn friotassuni_2 cund fvprc adantl c0 friotassuni_2 cuni cpw friotassuni_2 cuni cun wss friotassuni_0 friotassuni_1 friotassuni_2 wreu wn friotassuni_2 cvv wcel wn wa friotassuni_2 cuni cpw friotassuni_2 cuni cun 0ss a1i eqsstrd pm2.61dan eqsstrd pm2.61i $.
$}
$( Closure of restricted iota.  (Contributed by NM, 28-Feb-2013.)  (Revised
       by Mario Carneiro, 24-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v V $.
	$d x A $.
	friotaclbg_0 $f wff ph $.
	friotaclbg_1 $f set x $.
	friotaclbg_2 $f class A $.
	friotaclbg_3 $f class V $.
	riotaclbg $p |- ( A e. V -> ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A ) ) $= friotaclbg_2 friotaclbg_3 wcel friotaclbg_0 friotaclbg_1 friotaclbg_2 wreu friotaclbg_0 friotaclbg_1 friotaclbg_2 crio friotaclbg_2 wcel friotaclbg_0 friotaclbg_1 friotaclbg_2 riotacl friotaclbg_2 friotaclbg_3 wcel friotaclbg_0 friotaclbg_1 friotaclbg_2 wreu friotaclbg_0 friotaclbg_1 friotaclbg_2 crio friotaclbg_2 wcel friotaclbg_2 friotaclbg_3 wcel friotaclbg_0 friotaclbg_1 friotaclbg_2 crio friotaclbg_2 wcel wn friotaclbg_0 friotaclbg_1 friotaclbg_2 wreu wn friotaclbg_2 cund cfv friotaclbg_2 wcel wn friotaclbg_2 friotaclbg_3 undefnel2 friotaclbg_0 friotaclbg_1 friotaclbg_2 wreu wn friotaclbg_0 friotaclbg_1 friotaclbg_2 crio friotaclbg_2 wcel friotaclbg_2 cund cfv friotaclbg_2 wcel friotaclbg_0 friotaclbg_1 friotaclbg_2 wreu wn friotaclbg_0 friotaclbg_1 friotaclbg_2 crio friotaclbg_2 cund cfv friotaclbg_2 friotaclbg_0 friotaclbg_1 friotaclbg_2 riotaund eleq1d notbid syl5ibrcom con4d impbid2 $.
$}
$( Closure of restricted iota.  (Contributed by NM, 15-Sep-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	friotaclb_0 $f wff ph $.
	friotaclb_1 $f set x $.
	friotaclb_2 $f class A $.
	eriotaclb_0 $e |- A e. _V $.
	riotaclb $p |- ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A ) $= friotaclb_2 cvv wcel friotaclb_0 friotaclb_1 friotaclb_2 wreu friotaclb_0 friotaclb_1 friotaclb_2 crio friotaclb_2 wcel wb eriotaclb_0 friotaclb_0 friotaclb_1 friotaclb_2 cvv riotaclbg ax-mp $.
$}
$( Restricted iota equals the undefined value of its domain of discourse
       ` A ` when not meaningful.  (Contributed by NM, 26-Sep-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	friotaundb_0 $f wff ph $.
	friotaundb_1 $f set x $.
	friotaundb_2 $f class A $.
	eriotaundb_0 $e |- A e. _V $.
	riotaundb $p |- ( -. E! x e. A ph <-> ( iota_ x e. A ph ) = ( Undef ` A ) ) $= friotaundb_0 friotaundb_1 friotaundb_2 wreu wn friotaundb_0 friotaundb_1 friotaundb_2 crio friotaundb_2 cund cfv wceq friotaundb_0 friotaundb_1 friotaundb_2 riotaund friotaundb_0 friotaundb_1 friotaundb_2 wreu friotaundb_0 friotaundb_1 friotaundb_2 crio friotaundb_2 cund cfv friotaundb_0 friotaundb_1 friotaundb_2 wreu friotaundb_0 friotaundb_1 friotaundb_2 crio friotaundb_2 wcel friotaundb_2 cund cfv friotaundb_2 wcel wn friotaundb_0 friotaundb_1 friotaundb_2 crio friotaundb_2 cund cfv wne friotaundb_0 friotaundb_1 friotaundb_2 riotacl friotaundb_2 cvv wcel friotaundb_2 cund cfv friotaundb_2 wcel wn eriotaundb_0 friotaundb_2 cvv undefnel2 ax-mp friotaundb_0 friotaundb_1 friotaundb_2 crio friotaundb_2 cund cfv friotaundb_2 nelne2 sylancl necon2bi impbii $.
$}
$( Deduction version of ~ riotasv .  (Contributed by NM, 4-Mar-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
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
	$v V $.
	$d x y z A $.
	$d x z B $.
	$d x z C $.
	$d z D $.
	$d z ph $.
	$d x z ps $.
	iriotasvd_0 $f set z $.
	friotasvd_0 $f wff ph $.
	friotasvd_1 $f wff ps $.
	friotasvd_2 $f set x $.
	friotasvd_3 $f set y $.
	friotasvd_4 $f class A $.
	friotasvd_5 $f class B $.
	friotasvd_6 $f class C $.
	friotasvd_7 $f class D $.
	friotasvd_8 $f class V $.
	eriotasvd_0 $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	eriotasvd_1 $e |- ( ph -> D e. A ) $.
	riotasvd $p |- ( ( ph /\ A e. V ) -> ( ( y e. B /\ ps ) -> D = C ) ) $= friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_3 cv friotasvd_5 wcel friotasvd_1 wa friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq friotasvd_7 friotasvd_6 wceq friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_3 cv friotasvd_5 wcel friotasvd_1 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_1 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_3 cv friotasvd_5 wcel friotasvd_1 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq wi wi friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio wsbc friotasvd_1 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 wreu friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio wsbc friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 wreu friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_4 wcel friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_7 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_4 friotasvd_0 friotasvd_7 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio wceq friotasvd_4 friotasvd_8 wcel eriotasvd_0 adantr friotasvd_0 friotasvd_7 friotasvd_4 wcel friotasvd_4 friotasvd_8 wcel eriotasvd_1 adantr eqeltrrd friotasvd_4 friotasvd_8 wcel friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 wreu friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_4 wcel wb friotasvd_0 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 friotasvd_8 riotaclbg adantl mpbird friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 riotasbc syl friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_4 wcel friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio wsbc friotasvd_1 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral wb friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_7 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_4 friotasvd_0 friotasvd_7 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio wceq friotasvd_4 friotasvd_8 wcel eriotasvd_0 adantr friotasvd_0 friotasvd_7 friotasvd_4 wcel friotasvd_4 friotasvd_8 wcel eriotasvd_1 adantr eqeltrrd friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_1 iriotasvd_0 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_1 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 iriotasvd_0 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_4 friotasvd_2 cv iriotasvd_0 cv wceq friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_1 iriotasvd_0 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 friotasvd_2 cv iriotasvd_0 cv wceq friotasvd_2 cv friotasvd_6 wceq iriotasvd_0 cv friotasvd_6 wceq friotasvd_1 friotasvd_2 cv iriotasvd_0 cv friotasvd_6 eqeq1 imbi2d ralbidv iriotasvd_0 cv friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio wceq friotasvd_1 iriotasvd_0 cv friotasvd_6 wceq wi friotasvd_1 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq wi friotasvd_3 friotasvd_5 friotasvd_3 iriotasvd_0 cv friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_3 friotasvd_2 friotasvd_4 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 nfra1 friotasvd_3 friotasvd_4 nfcv nfriota nfeq2 iriotasvd_0 cv friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio wceq iriotasvd_0 cv friotasvd_6 wceq friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq friotasvd_1 iriotasvd_0 cv friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 eqeq1 imbi2d ralbid sbcie2g syl mpbid friotasvd_1 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 wceq wi friotasvd_3 friotasvd_5 rsp syl imp3a friotasvd_0 friotasvd_4 friotasvd_8 wcel wa friotasvd_7 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio friotasvd_6 friotasvd_0 friotasvd_7 friotasvd_1 friotasvd_2 cv friotasvd_6 wceq wi friotasvd_3 friotasvd_5 wral friotasvd_2 friotasvd_4 crio wceq friotasvd_4 friotasvd_8 wcel eriotasvd_0 adantr eqeq1d sylibrd $.
$}
$( Deduction version of ~ riotasv .  (Contributed by NM, 1-Feb-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$d x y A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	friotasvdOLD_0 $f wff ph $.
	friotasvdOLD_1 $f wff ps $.
	friotasvdOLD_2 $f set x $.
	friotasvdOLD_3 $f set y $.
	friotasvdOLD_4 $f class A $.
	friotasvdOLD_5 $f class B $.
	friotasvdOLD_6 $f class C $.
	friotasvdOLD_7 $f class D $.
	friotasvdOLD_8 $f class V $.
	eriotasvdOLD_0 $e |- ( ph -> A. x ph ) $.
	eriotasvdOLD_1 $e |- ( ph -> A. y ph ) $.
	eriotasvdOLD_2 $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	riotasvdOLD $p |- ( ( ( ph /\ A e. V ) /\ D e. A /\ ( y e. B /\ ps ) ) -> D = C ) $= friotasvdOLD_0 friotasvdOLD_4 friotasvdOLD_8 wcel wa friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_3 cv friotasvdOLD_5 wcel friotasvdOLD_1 wa friotasvdOLD_7 friotasvdOLD_6 wceq friotasvdOLD_0 friotasvdOLD_4 friotasvdOLD_8 wcel wa friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_3 cv friotasvdOLD_5 wcel friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq friotasvdOLD_0 friotasvdOLD_4 friotasvdOLD_8 wcel wa friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_3 cv friotasvdOLD_5 wcel friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi wi friotasvdOLD_0 friotasvdOLD_4 friotasvdOLD_8 wcel wa friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_0 friotasvdOLD_4 friotasvdOLD_8 wcel wa friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_7 wceq friotasvdOLD_0 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_7 wceq friotasvdOLD_4 friotasvdOLD_8 wcel friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio eriotasvdOLD_2 eqcomd ad2antrr friotasvdOLD_0 friotasvdOLD_4 friotasvdOLD_8 wcel wa friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 wreu friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_7 wceq wb friotasvdOLD_0 friotasvdOLD_4 friotasvdOLD_8 wcel wa friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 wreu friotasvdOLD_0 friotasvdOLD_4 friotasvdOLD_8 wcel wa friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_4 wcel friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 wreu friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_4 wcel wb friotasvdOLD_4 friotasvdOLD_8 wcel friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_4 eriotasvdOLD_2 eleq1d adantr friotasvdOLD_4 friotasvdOLD_8 wcel friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 wreu friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_4 wcel wb friotasvdOLD_0 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 friotasvdOLD_8 riotaclbg adantl bitr4d biimpa friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 wreu friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_7 wceq wb friotasvdOLD_4 friotasvdOLD_8 wcel friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 friotasvdOLD_7 friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_2 friotasvdOLD_0 friotasvdOLD_2 eriotasvdOLD_0 nfi friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 friotasvdOLD_4 friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 wnfc friotasvdOLD_2 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio wnfc friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 nfriota1 friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_0 friotasvdOLD_2 eriotasvdOLD_0 nfi eriotasvdOLD_2 nfceqdf mpbiri friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_4 nfcvd nfeld nfan1 friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 wnfc friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 wnfc friotasvdOLD_2 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio wnfc friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 nfriota1 friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_0 friotasvdOLD_2 eriotasvdOLD_0 nfi eriotasvdOLD_2 nfceqdf mpbiri adantr friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_2 friotasvdOLD_3 friotasvdOLD_5 friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_3 friotasvdOLD_0 friotasvdOLD_3 eriotasvdOLD_1 nfi friotasvdOLD_0 friotasvdOLD_3 friotasvdOLD_7 friotasvdOLD_4 friotasvdOLD_0 friotasvdOLD_3 friotasvdOLD_7 wnfc friotasvdOLD_3 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio wnfc friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_3 friotasvdOLD_2 friotasvdOLD_4 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 nfra1 friotasvdOLD_3 friotasvdOLD_4 nfcv nfriota friotasvdOLD_0 friotasvdOLD_3 friotasvdOLD_7 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_0 friotasvdOLD_3 eriotasvdOLD_1 nfi eriotasvdOLD_2 nfceqdf mpbiri friotasvdOLD_0 friotasvdOLD_3 friotasvdOLD_4 nfcvd nfeld nfan1 friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_2 friotasvdOLD_5 nfcvd friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq friotasvdOLD_2 friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_1 friotasvdOLD_2 nfvd friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_2 friotasvdOLD_7 friotasvdOLD_6 friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 wnfc friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 wnfc friotasvdOLD_2 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio wnfc friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 nfriota1 friotasvdOLD_0 friotasvdOLD_2 friotasvdOLD_7 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_0 friotasvdOLD_2 eriotasvdOLD_0 nfi eriotasvdOLD_2 nfceqdf mpbiri adantr friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel wa friotasvdOLD_2 friotasvdOLD_6 nfcvd nfeqd nfimd nfrald friotasvdOLD_0 friotasvdOLD_7 friotasvdOLD_4 wcel simpr friotasvdOLD_0 friotasvdOLD_2 cv friotasvdOLD_7 wceq friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral wb friotasvdOLD_7 friotasvdOLD_4 wcel friotasvdOLD_0 friotasvdOLD_2 cv friotasvdOLD_7 wceq wa friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 friotasvdOLD_0 friotasvdOLD_2 cv friotasvdOLD_7 wceq friotasvdOLD_3 friotasvdOLD_0 friotasvdOLD_3 eriotasvdOLD_1 nfi friotasvdOLD_0 friotasvdOLD_3 friotasvdOLD_2 cv friotasvdOLD_7 friotasvdOLD_0 friotasvdOLD_3 friotasvdOLD_2 cv nfcvd friotasvdOLD_0 friotasvdOLD_3 friotasvdOLD_7 wnfc friotasvdOLD_3 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio wnfc friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_3 friotasvdOLD_2 friotasvdOLD_4 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 nfra1 friotasvdOLD_3 friotasvdOLD_4 nfcv nfriota friotasvdOLD_0 friotasvdOLD_3 friotasvdOLD_7 friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 wral friotasvdOLD_2 friotasvdOLD_4 crio friotasvdOLD_0 friotasvdOLD_3 eriotasvdOLD_1 nfi eriotasvdOLD_2 nfceqdf mpbiri nfeqd nfan1 friotasvdOLD_0 friotasvdOLD_2 cv friotasvdOLD_7 wceq wa friotasvdOLD_2 cv friotasvdOLD_6 wceq friotasvdOLD_7 friotasvdOLD_6 wceq friotasvdOLD_1 friotasvdOLD_2 cv friotasvdOLD_7 wceq friotasvdOLD_2 cv friotasvdOLD_6 wceq friotasvdOLD_7 friotasvdOLD_6 wceq wb friotasvdOLD_0 friotasvdOLD_2 cv friotasvdOLD_7 friotasvdOLD_6 eqeq1 adantl imbi2d ralbid adantlr riota2df adantllr mpdan mpbird ex friotasvdOLD_1 friotasvdOLD_7 friotasvdOLD_6 wceq wi friotasvdOLD_3 friotasvdOLD_5 rsp syl6 imp4a 3imp $.
$}
$( Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 2-Mar-2013.) $)
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
	$v E $.
	$v F $.
	$v V $.
	$d x y A $.
	$d x y B $.
	$d x C $.
	$d y E $.
	$d x ps $.
	friotasv2d_0 $f wff ph $.
	friotasv2d_1 $f wff ps $.
	friotasv2d_2 $f wff ch $.
	friotasv2d_3 $f set x $.
	friotasv2d_4 $f set y $.
	friotasv2d_5 $f class A $.
	friotasv2d_6 $f class B $.
	friotasv2d_7 $f class C $.
	friotasv2d_8 $f class D $.
	friotasv2d_9 $f class E $.
	friotasv2d_10 $f class F $.
	friotasv2d_11 $f class V $.
	eriotasv2d_0 $e |- F/ y ph $.
	eriotasv2d_1 $e |- ( ph -> F/_ y F ) $.
	eriotasv2d_2 $e |- ( ph -> F/ y ch ) $.
	eriotasv2d_3 $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	eriotasv2d_4 $e |- ( ( ph /\ y = E ) -> ( ps <-> ch ) ) $.
	eriotasv2d_5 $e |- ( ( ph /\ y = E ) -> C = F ) $.
	eriotasv2d_6 $e |- ( ph -> D e. A ) $.
	eriotasv2d_7 $e |- ( ph -> E e. B ) $.
	eriotasv2d_8 $e |- ( ph -> ch ) $.
	riotasv2d $p |- ( ( ph /\ A e. V ) -> D = F ) $= friotasv2d_5 friotasv2d_11 wcel friotasv2d_0 friotasv2d_5 cvv wcel friotasv2d_8 friotasv2d_10 wceq friotasv2d_5 friotasv2d_11 elex friotasv2d_0 friotasv2d_5 cvv wcel wa friotasv2d_9 friotasv2d_6 wcel friotasv2d_2 friotasv2d_8 friotasv2d_10 wceq friotasv2d_0 friotasv2d_9 friotasv2d_6 wcel friotasv2d_5 cvv wcel eriotasv2d_7 adantr friotasv2d_0 friotasv2d_2 friotasv2d_5 cvv wcel eriotasv2d_8 adantr friotasv2d_0 friotasv2d_5 cvv wcel wa friotasv2d_4 cv friotasv2d_6 wcel friotasv2d_1 wa friotasv2d_8 friotasv2d_7 wceq wi friotasv2d_9 friotasv2d_6 wcel friotasv2d_2 wa friotasv2d_8 friotasv2d_10 wceq wi friotasv2d_4 friotasv2d_9 friotasv2d_6 friotasv2d_0 friotasv2d_9 friotasv2d_6 wcel friotasv2d_5 cvv wcel eriotasv2d_7 adantr friotasv2d_0 friotasv2d_4 cv friotasv2d_9 wceq friotasv2d_4 cv friotasv2d_6 wcel friotasv2d_1 wa friotasv2d_8 friotasv2d_7 wceq wi friotasv2d_9 friotasv2d_6 wcel friotasv2d_2 wa friotasv2d_8 friotasv2d_10 wceq wi wb friotasv2d_5 cvv wcel friotasv2d_0 friotasv2d_4 cv friotasv2d_9 wceq wa friotasv2d_4 cv friotasv2d_6 wcel friotasv2d_1 wa friotasv2d_9 friotasv2d_6 wcel friotasv2d_2 wa friotasv2d_8 friotasv2d_7 wceq friotasv2d_8 friotasv2d_10 wceq friotasv2d_0 friotasv2d_4 cv friotasv2d_9 wceq wa friotasv2d_4 cv friotasv2d_6 wcel friotasv2d_9 friotasv2d_6 wcel friotasv2d_1 friotasv2d_2 friotasv2d_4 cv friotasv2d_9 wceq friotasv2d_4 cv friotasv2d_6 wcel friotasv2d_9 friotasv2d_6 wcel wb friotasv2d_0 friotasv2d_4 cv friotasv2d_9 friotasv2d_6 eleq1 adantl eriotasv2d_4 anbi12d friotasv2d_0 friotasv2d_4 cv friotasv2d_9 wceq wa friotasv2d_7 friotasv2d_10 friotasv2d_8 eriotasv2d_5 eqeq2d imbi12d adantlr friotasv2d_0 friotasv2d_1 friotasv2d_3 friotasv2d_4 friotasv2d_5 friotasv2d_6 friotasv2d_7 friotasv2d_8 cvv eriotasv2d_3 eriotasv2d_6 riotasvd friotasv2d_0 friotasv2d_5 cvv wcel friotasv2d_4 eriotasv2d_0 friotasv2d_5 cvv wcel friotasv2d_4 nfv nfan friotasv2d_0 friotasv2d_5 cvv wcel wa friotasv2d_4 friotasv2d_9 nfcvd friotasv2d_0 friotasv2d_9 friotasv2d_6 wcel friotasv2d_2 wa friotasv2d_8 friotasv2d_10 wceq wi friotasv2d_4 wnf friotasv2d_5 cvv wcel friotasv2d_0 friotasv2d_9 friotasv2d_6 wcel friotasv2d_2 wa friotasv2d_8 friotasv2d_10 wceq friotasv2d_4 friotasv2d_0 friotasv2d_9 friotasv2d_6 wcel friotasv2d_2 friotasv2d_4 friotasv2d_0 friotasv2d_9 friotasv2d_6 wcel friotasv2d_4 nfvd eriotasv2d_2 nfand friotasv2d_0 friotasv2d_4 friotasv2d_8 friotasv2d_10 friotasv2d_0 friotasv2d_4 friotasv2d_8 wnfc friotasv2d_4 friotasv2d_1 friotasv2d_3 cv friotasv2d_7 wceq wi friotasv2d_4 friotasv2d_6 wral friotasv2d_3 friotasv2d_5 crio wnfc friotasv2d_1 friotasv2d_3 cv friotasv2d_7 wceq wi friotasv2d_4 friotasv2d_6 wral friotasv2d_4 friotasv2d_3 friotasv2d_5 friotasv2d_1 friotasv2d_3 cv friotasv2d_7 wceq wi friotasv2d_4 friotasv2d_6 nfra1 friotasv2d_4 friotasv2d_5 nfcv nfriota friotasv2d_0 friotasv2d_4 friotasv2d_8 friotasv2d_1 friotasv2d_3 cv friotasv2d_7 wceq wi friotasv2d_4 friotasv2d_6 wral friotasv2d_3 friotasv2d_5 crio eriotasv2d_0 eriotasv2d_3 nfceqdf mpbiri eriotasv2d_1 nfeqd nfimd adantr vtocldf mp2and sylan2 $.
$}
$( Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 1-Feb-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v E $.
	$v F $.
	$v V $.
	$d x y z A $.
	$d x y z B $.
	$d x z C $.
	$d z D $.
	$d y z E $.
	$d z F $.
	$d z ph $.
	$d x z ps $.
	friotasv2dOLD_0 $f wff ph $.
	friotasv2dOLD_1 $f wff ps $.
	friotasv2dOLD_2 $f wff ch $.
	friotasv2dOLD_3 $f set x $.
	friotasv2dOLD_4 $f set y $.
	friotasv2dOLD_5 $f set z $.
	friotasv2dOLD_6 $f class A $.
	friotasv2dOLD_7 $f class B $.
	friotasv2dOLD_8 $f class C $.
	friotasv2dOLD_9 $f class D $.
	friotasv2dOLD_10 $f class E $.
	friotasv2dOLD_11 $f class F $.
	friotasv2dOLD_12 $f class V $.
	eriotasv2dOLD_0 $e |- ( ph -> A. x ph ) $.
	eriotasv2dOLD_1 $e |- ( ph -> A. y ph ) $.
	eriotasv2dOLD_2 $e |- ( ph -> ( z e. F -> A. y z e. F ) ) $.
	eriotasv2dOLD_3 $e |- ( ph -> ( ch -> A. y ch ) ) $.
	eriotasv2dOLD_4 $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	eriotasv2dOLD_5 $e |- ( ph -> ( y = E -> ( ps <-> ch ) ) ) $.
	eriotasv2dOLD_6 $e |- ( ph -> ( y = E -> C = F ) ) $.
	riotasv2dOLD $p |- ( ( ( ph /\ A e. V ) /\ ( D e. A /\ E e. B /\ ch ) ) -> D = F ) $= friotasv2dOLD_6 friotasv2dOLD_12 wcel friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq friotasv2dOLD_6 friotasv2dOLD_12 elex friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 friotasv2dOLD_9 friotasv2dOLD_11 wceq friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_2 friotasv2dOLD_9 friotasv2dOLD_11 wceq wi friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_2 friotasv2dOLD_9 friotasv2dOLD_11 wceq wi wi friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_2 friotasv2dOLD_9 friotasv2dOLD_11 wceq wi wi wi friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 friotasv2dOLD_9 friotasv2dOLD_11 wceq wi friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 friotasv2dOLD_9 friotasv2dOLD_11 wceq friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_10 wnfc friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq wi friotasv2dOLD_4 wnf friotasv2dOLD_4 cv friotasv2dOLD_10 wceq friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq wi friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq wi wb wi friotasv2dOLD_4 wal friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq wi friotasv2dOLD_4 wal friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq wi friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_10 nfcvd friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_9 friotasv2dOLD_6 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_9 wnfc friotasv2dOLD_4 friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 wral friotasv2dOLD_3 friotasv2dOLD_6 crio wnfc friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 wral friotasv2dOLD_4 friotasv2dOLD_3 friotasv2dOLD_6 friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 nfra1 friotasv2dOLD_4 friotasv2dOLD_6 nfcv nfriota friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_9 friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 wral friotasv2dOLD_3 friotasv2dOLD_6 crio friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_4 eriotasv2dOLD_1 nfi friotasv2dOLD_6 cvv wcel friotasv2dOLD_4 nfv nfan friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_4 nfv nfan friotasv2dOLD_0 friotasv2dOLD_9 friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 wral friotasv2dOLD_3 friotasv2dOLD_6 crio wceq friotasv2dOLD_6 cvv wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel eriotasv2dOLD_4 ad2antrr nfceqdf mpbiri friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_6 nfcvd nfeld friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_4 nfvd friotasv2dOLD_0 friotasv2dOLD_2 friotasv2dOLD_4 wnf friotasv2dOLD_6 cvv wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_0 friotasv2dOLD_2 friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_4 eriotasv2dOLD_1 nfi eriotasv2dOLD_3 nfd ad2antrr nf3and friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_9 friotasv2dOLD_11 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_9 wnfc friotasv2dOLD_4 friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 wral friotasv2dOLD_3 friotasv2dOLD_6 crio wnfc friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 wral friotasv2dOLD_4 friotasv2dOLD_3 friotasv2dOLD_6 friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 nfra1 friotasv2dOLD_4 friotasv2dOLD_6 nfcv nfriota friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 friotasv2dOLD_9 friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 wral friotasv2dOLD_3 friotasv2dOLD_6 crio friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_4 eriotasv2dOLD_1 nfi friotasv2dOLD_6 cvv wcel friotasv2dOLD_4 nfv nfan friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_4 nfv nfan friotasv2dOLD_0 friotasv2dOLD_9 friotasv2dOLD_1 friotasv2dOLD_3 cv friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_7 wral friotasv2dOLD_3 friotasv2dOLD_6 crio wceq friotasv2dOLD_6 cvv wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel eriotasv2dOLD_4 ad2antrr nfceqdf mpbiri friotasv2dOLD_0 friotasv2dOLD_4 friotasv2dOLD_11 wnfc friotasv2dOLD_6 cvv wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_0 friotasv2dOLD_4 friotasv2dOLD_5 friotasv2dOLD_11 friotasv2dOLD_0 friotasv2dOLD_5 nfv friotasv2dOLD_0 friotasv2dOLD_5 cv friotasv2dOLD_11 wcel friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_4 eriotasv2dOLD_1 nfi eriotasv2dOLD_2 nfd nfcd ad2antrr nfeqd nfimd friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel wa friotasv2dOLD_4 cv friotasv2dOLD_10 wceq friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq wi friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq wi wb wi friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_4 eriotasv2dOLD_1 nfi friotasv2dOLD_6 cvv wcel friotasv2dOLD_4 nfv nfan friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_4 nfv nfan friotasv2dOLD_0 friotasv2dOLD_4 cv friotasv2dOLD_10 wceq friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq wi friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq wi wb wi friotasv2dOLD_6 cvv wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_0 friotasv2dOLD_4 cv friotasv2dOLD_10 wceq friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq wi friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq wi wb friotasv2dOLD_0 friotasv2dOLD_4 cv friotasv2dOLD_10 wceq wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq friotasv2dOLD_9 friotasv2dOLD_11 wceq friotasv2dOLD_0 friotasv2dOLD_4 cv friotasv2dOLD_10 wceq wa friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_1 friotasv2dOLD_2 friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_10 wceq friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel wb friotasv2dOLD_0 friotasv2dOLD_4 cv friotasv2dOLD_10 friotasv2dOLD_7 eleq1 adantl friotasv2dOLD_0 friotasv2dOLD_4 cv friotasv2dOLD_10 wceq friotasv2dOLD_1 friotasv2dOLD_2 wb eriotasv2dOLD_5 imp 3anbi23d friotasv2dOLD_0 friotasv2dOLD_4 cv friotasv2dOLD_10 wceq wa friotasv2dOLD_8 friotasv2dOLD_11 friotasv2dOLD_9 friotasv2dOLD_0 friotasv2dOLD_4 cv friotasv2dOLD_10 wceq friotasv2dOLD_8 friotasv2dOLD_11 wceq eriotasv2dOLD_6 imp eqeq2d imbi12d ex ad2antrr alrimi friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq wi friotasv2dOLD_4 wal friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq wi friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel friotasv2dOLD_4 friotasv2dOLD_0 friotasv2dOLD_4 eriotasv2dOLD_1 nfi friotasv2dOLD_6 cvv wcel friotasv2dOLD_4 nfv nfan friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 friotasv2dOLD_9 friotasv2dOLD_8 wceq friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 friotasv2dOLD_9 friotasv2dOLD_8 wceq friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 wa friotasv2dOLD_9 friotasv2dOLD_8 wceq friotasv2dOLD_0 friotasv2dOLD_1 friotasv2dOLD_3 friotasv2dOLD_4 friotasv2dOLD_6 friotasv2dOLD_7 friotasv2dOLD_8 friotasv2dOLD_9 cvv eriotasv2dOLD_0 eriotasv2dOLD_1 eriotasv2dOLD_4 riotasvdOLD 3exp exp4a 3impd alrimi adantr friotasv2dOLD_0 friotasv2dOLD_6 cvv wcel wa friotasv2dOLD_10 friotasv2dOLD_7 wcel simpr friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_4 cv friotasv2dOLD_7 wcel friotasv2dOLD_1 w3a friotasv2dOLD_9 friotasv2dOLD_8 wceq wi friotasv2dOLD_9 friotasv2dOLD_6 wcel friotasv2dOLD_10 friotasv2dOLD_7 wcel friotasv2dOLD_2 w3a friotasv2dOLD_9 friotasv2dOLD_11 wceq wi friotasv2dOLD_4 friotasv2dOLD_10 friotasv2dOLD_7 vtoclgft syl221anc 3expd com23 ex pm2.43d com23 3imp2 sylanl2 $.
$}
$( The value of description binder ` D ` for a single-valued class
       expression ` C ( y ) ` (as in e.g. ~ reusv2 ) in the form of a
       substitution instance.  Special case of ~ riota2f .  (Contributed by NM,
       3-Mar-2013.)  (Proof shortened by Mario Carneiro, 6-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v E $.
	$v V $.
	$d x y A $.
	$d x y B $.
	$d x C $.
	$d x y E $.
	$d x ph $.
	friotasv2s_0 $f wff ph $.
	friotasv2s_1 $f set x $.
	friotasv2s_2 $f set y $.
	friotasv2s_3 $f class A $.
	friotasv2s_4 $f class B $.
	friotasv2s_5 $f class C $.
	friotasv2s_6 $f class D $.
	friotasv2s_7 $f class E $.
	friotasv2s_8 $f class V $.
	eriotasv2s_0 $e |- D = ( iota_ x e. A A. y e. B ( ph -> x = C ) ) $.
	riotasv2s $p |- ( ( A e. V /\ D e. A /\ ( E e. B /\ [. E / y ]. ph ) ) -> D = [_ E / y ]_ C ) $= friotasv2s_3 friotasv2s_8 wcel friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa w3a friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa wa friotasv2s_3 friotasv2s_8 wcel friotasv2s_6 friotasv2s_2 friotasv2s_7 friotasv2s_5 csb wceq friotasv2s_3 friotasv2s_8 wcel friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa 3simpc friotasv2s_3 friotasv2s_8 wcel friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa simp1 friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa wa friotasv2s_0 friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc friotasv2s_1 friotasv2s_2 friotasv2s_3 friotasv2s_4 friotasv2s_5 friotasv2s_6 friotasv2s_7 friotasv2s_2 friotasv2s_7 friotasv2s_5 csb friotasv2s_8 friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa friotasv2s_2 friotasv2s_2 friotasv2s_6 friotasv2s_3 friotasv2s_2 friotasv2s_6 friotasv2s_0 friotasv2s_1 cv friotasv2s_5 wceq wi friotasv2s_2 friotasv2s_4 wral friotasv2s_1 friotasv2s_3 crio eriotasv2s_0 friotasv2s_0 friotasv2s_1 cv friotasv2s_5 wceq wi friotasv2s_2 friotasv2s_4 wral friotasv2s_2 friotasv2s_1 friotasv2s_3 friotasv2s_0 friotasv2s_1 cv friotasv2s_5 wceq wi friotasv2s_2 friotasv2s_4 nfra1 friotasv2s_2 friotasv2s_3 nfcv nfriota nfcxfr nfel1 friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc friotasv2s_2 friotasv2s_7 friotasv2s_4 wcel friotasv2s_2 nfv friotasv2s_0 friotasv2s_2 friotasv2s_7 nfsbc1v nfan nfan friotasv2s_2 friotasv2s_2 friotasv2s_7 friotasv2s_5 csb wnfc friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa wa friotasv2s_2 friotasv2s_7 friotasv2s_5 nfcsb1v a1i friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc friotasv2s_2 wnf friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa wa friotasv2s_0 friotasv2s_2 friotasv2s_7 nfsbc1v a1i friotasv2s_6 friotasv2s_0 friotasv2s_1 cv friotasv2s_5 wceq wi friotasv2s_2 friotasv2s_4 wral friotasv2s_1 friotasv2s_3 crio wceq friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa wa eriotasv2s_0 a1i friotasv2s_2 cv friotasv2s_7 wceq friotasv2s_0 friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wb friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa wa friotasv2s_0 friotasv2s_2 friotasv2s_7 sbceq1a adantl friotasv2s_2 cv friotasv2s_7 wceq friotasv2s_5 friotasv2s_2 friotasv2s_7 friotasv2s_5 csb wceq friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa wa friotasv2s_2 friotasv2s_7 friotasv2s_5 csbeq1a adantl friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc wa simpl friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc simprl friotasv2s_6 friotasv2s_3 wcel friotasv2s_7 friotasv2s_4 wcel friotasv2s_0 friotasv2s_2 friotasv2s_7 wsbc simprr riotasv2d syl2anc $.
$}
$( Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 26-Jan-2013.)  (Proof shortened by Mario Carneiro,
       6-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x y A $.
	$d x B $.
	$d x C $.
	$d x ph $.
	friotasv_0 $f wff ph $.
	friotasv_1 $f set x $.
	friotasv_2 $f set y $.
	friotasv_3 $f class A $.
	friotasv_4 $f class B $.
	friotasv_5 $f class C $.
	friotasv_6 $f class D $.
	eriotasv_0 $e |- A e. _V $.
	eriotasv_1 $e |- D = ( iota_ x e. A A. y e. B ( ph -> x = C ) ) $.
	riotasv $p |- ( ( D e. A /\ y e. B /\ ph ) -> D = C ) $= friotasv_6 friotasv_3 wcel friotasv_2 cv friotasv_4 wcel friotasv_0 friotasv_6 friotasv_5 wceq friotasv_6 friotasv_3 wcel friotasv_3 cvv wcel friotasv_2 cv friotasv_4 wcel friotasv_0 wa friotasv_6 friotasv_5 wceq wi eriotasv_0 friotasv_6 friotasv_3 wcel friotasv_0 friotasv_1 friotasv_2 friotasv_3 friotasv_4 friotasv_5 friotasv_6 cvv friotasv_6 friotasv_0 friotasv_1 cv friotasv_5 wceq wi friotasv_2 friotasv_4 wral friotasv_1 friotasv_3 crio wceq friotasv_6 friotasv_3 wcel eriotasv_1 a1i friotasv_6 friotasv_3 wcel id riotasvd mpan2 3impib $.
$}
$( A property ` ch ` holding for a representative of a single-valued class
       expression ` C ( y ) ` (see e.g. ~ reusv2 ) also holds for its
       description binder ` D ` (in the form of property ` th ` ).
       (Contributed by NM, 5-Mar-2013.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$d x y A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	friotasv3d_0 $f wff ph $.
	friotasv3d_1 $f wff ps $.
	friotasv3d_2 $f wff ch $.
	friotasv3d_3 $f wff th $.
	friotasv3d_4 $f set x $.
	friotasv3d_5 $f set y $.
	friotasv3d_6 $f class A $.
	friotasv3d_7 $f class B $.
	friotasv3d_8 $f class C $.
	friotasv3d_9 $f class D $.
	friotasv3d_10 $f class V $.
	eriotasv3d_0 $e |- F/ y ph $.
	eriotasv3d_1 $e |- ( ph -> F/ y th ) $.
	eriotasv3d_2 $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	eriotasv3d_3 $e |- ( ( ph /\ C = D ) -> ( ch <-> th ) ) $.
	eriotasv3d_4 $e |- ( ph -> ( ( y e. B /\ ps ) -> ch ) ) $.
	eriotasv3d_5 $e |- ( ph -> D e. A ) $.
	eriotasv3d_6 $e |- ( ph -> E. y e. B ps ) $.
	riotasv3d $p |- ( ( ph /\ A e. V ) -> th ) $= friotasv3d_6 friotasv3d_10 wcel friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_3 friotasv3d_6 friotasv3d_10 elex friotasv3d_0 friotasv3d_6 cvv wcel wa friotasv3d_1 friotasv3d_5 friotasv3d_7 wrex friotasv3d_3 friotasv3d_0 friotasv3d_1 friotasv3d_5 friotasv3d_7 wrex friotasv3d_6 cvv wcel eriotasv3d_6 adantr friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_1 friotasv3d_5 friotasv3d_7 wrex friotasv3d_3 wi friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_1 friotasv3d_3 wi friotasv3d_5 friotasv3d_7 wral friotasv3d_1 friotasv3d_5 friotasv3d_7 wrex friotasv3d_3 wi friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_1 friotasv3d_3 wi friotasv3d_5 friotasv3d_7 eriotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_5 nfv friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_5 cv friotasv3d_7 wcel friotasv3d_1 friotasv3d_3 friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_5 cv friotasv3d_7 wcel friotasv3d_1 wa wa wa friotasv3d_2 friotasv3d_3 friotasv3d_0 friotasv3d_5 cv friotasv3d_7 wcel friotasv3d_1 wa friotasv3d_2 friotasv3d_6 cvv wcel friotasv3d_0 friotasv3d_5 cv friotasv3d_7 wcel friotasv3d_1 wa friotasv3d_2 eriotasv3d_4 imp adantrl friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_5 cv friotasv3d_7 wcel friotasv3d_1 wa wa friotasv3d_8 friotasv3d_9 wceq friotasv3d_2 friotasv3d_3 wb friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_5 cv friotasv3d_7 wcel friotasv3d_1 wa wa wa friotasv3d_9 friotasv3d_8 friotasv3d_0 friotasv3d_6 cvv wcel friotasv3d_5 cv friotasv3d_7 wcel friotasv3d_1 wa friotasv3d_9 friotasv3d_8 wceq friotasv3d_0 friotasv3d_1 friotasv3d_4 friotasv3d_5 friotasv3d_6 friotasv3d_7 friotasv3d_8 friotasv3d_9 cvv eriotasv3d_2 eriotasv3d_5 riotasvd impr eqcomd eriotasv3d_3 syldan mpbid exp45 ralrimd friotasv3d_0 friotasv3d_3 friotasv3d_5 wnf friotasv3d_1 friotasv3d_3 wi friotasv3d_5 friotasv3d_7 wral friotasv3d_1 friotasv3d_5 friotasv3d_7 wrex friotasv3d_3 wi wb eriotasv3d_1 friotasv3d_1 friotasv3d_3 friotasv3d_5 friotasv3d_7 r19.23t syl sylibd imp mpd sylan2 $.
$}
$( A property ` ch ` holding for a representative of a single-valued class
       expression ` C ( y ) ` (see e.g. ~ reusv2 ) also holds for its
       description binder ` D ` (in the form of property ` th ` ).
       (Contributed by NM, 1-Feb-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$d x y A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	friotasv3dOLD_0 $f wff ph $.
	friotasv3dOLD_1 $f wff ps $.
	friotasv3dOLD_2 $f wff ch $.
	friotasv3dOLD_3 $f wff th $.
	friotasv3dOLD_4 $f set x $.
	friotasv3dOLD_5 $f set y $.
	friotasv3dOLD_6 $f class A $.
	friotasv3dOLD_7 $f class B $.
	friotasv3dOLD_8 $f class C $.
	friotasv3dOLD_9 $f class D $.
	friotasv3dOLD_10 $f class V $.
	eriotasv3dOLD_0 $e |- ( ph -> A. x ph ) $.
	eriotasv3dOLD_1 $e |- ( ph -> A. y ph ) $.
	eriotasv3dOLD_2 $e |- ( ph -> ( th -> A. y th ) ) $.
	eriotasv3dOLD_3 $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	eriotasv3dOLD_4 $e |- ( ph -> ( C = D -> ( ch <-> th ) ) ) $.
	eriotasv3dOLD_5 $e |- ( ph -> ( ( y e. B /\ ps ) -> ch ) ) $.
	riotasv3dOLD $p |- ( ( ph /\ ( A e. V /\ D e. A /\ E. y e. B ps ) ) -> th ) $= friotasv3dOLD_0 friotasv3dOLD_6 friotasv3dOLD_10 wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel friotasv3dOLD_1 friotasv3dOLD_5 friotasv3dOLD_7 wrex friotasv3dOLD_3 friotasv3dOLD_6 friotasv3dOLD_10 wcel friotasv3dOLD_6 cvv wcel friotasv3dOLD_0 friotasv3dOLD_9 friotasv3dOLD_6 wcel friotasv3dOLD_1 friotasv3dOLD_5 friotasv3dOLD_7 wrex friotasv3dOLD_3 wi wi friotasv3dOLD_6 friotasv3dOLD_10 elex friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel friotasv3dOLD_1 friotasv3dOLD_5 friotasv3dOLD_7 wrex friotasv3dOLD_3 wi friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_1 friotasv3dOLD_3 wi friotasv3dOLD_5 friotasv3dOLD_7 wral friotasv3dOLD_1 friotasv3dOLD_5 friotasv3dOLD_7 wrex friotasv3dOLD_3 wi friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_1 friotasv3dOLD_3 wi wi friotasv3dOLD_5 friotasv3dOLD_7 wral friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_1 friotasv3dOLD_3 wi friotasv3dOLD_5 friotasv3dOLD_7 wral wi friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_1 friotasv3dOLD_3 wi wi friotasv3dOLD_5 friotasv3dOLD_7 friotasv3dOLD_0 friotasv3dOLD_5 eriotasv3dOLD_1 nfi friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 friotasv3dOLD_3 wi friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 friotasv3dOLD_3 friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa wa wa friotasv3dOLD_2 friotasv3dOLD_3 friotasv3dOLD_0 friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa friotasv3dOLD_2 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_0 friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa friotasv3dOLD_2 eriotasv3dOLD_5 imp adantrl friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa wa friotasv3dOLD_2 friotasv3dOLD_3 wb friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa wa friotasv3dOLD_8 friotasv3dOLD_9 wceq friotasv3dOLD_2 friotasv3dOLD_3 wb friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa friotasv3dOLD_8 friotasv3dOLD_9 wceq friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa friotasv3dOLD_8 friotasv3dOLD_9 wceq wi wi friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel wa friotasv3dOLD_9 friotasv3dOLD_6 wcel friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa friotasv3dOLD_8 friotasv3dOLD_9 wceq friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel wa friotasv3dOLD_9 friotasv3dOLD_6 wcel friotasv3dOLD_5 cv friotasv3dOLD_7 wcel friotasv3dOLD_1 wa w3a friotasv3dOLD_9 friotasv3dOLD_8 friotasv3dOLD_0 friotasv3dOLD_1 friotasv3dOLD_4 friotasv3dOLD_5 friotasv3dOLD_6 friotasv3dOLD_7 friotasv3dOLD_8 friotasv3dOLD_9 cvv eriotasv3dOLD_0 eriotasv3dOLD_1 eriotasv3dOLD_3 riotasvdOLD eqcomd 3exp ex imp4c eriotasv3dOLD_4 syld imp mpbid exp45 com23 ralrimi friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_5 wnf friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_1 friotasv3dOLD_3 wi wi friotasv3dOLD_5 friotasv3dOLD_7 wral friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_1 friotasv3dOLD_3 wi friotasv3dOLD_5 friotasv3dOLD_7 wral wi wb friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel friotasv3dOLD_5 friotasv3dOLD_0 friotasv3dOLD_6 cvv wcel friotasv3dOLD_5 nfvd friotasv3dOLD_0 friotasv3dOLD_5 friotasv3dOLD_9 friotasv3dOLD_6 friotasv3dOLD_0 friotasv3dOLD_5 friotasv3dOLD_9 wnfc friotasv3dOLD_5 friotasv3dOLD_1 friotasv3dOLD_4 cv friotasv3dOLD_8 wceq wi friotasv3dOLD_5 friotasv3dOLD_7 wral friotasv3dOLD_4 friotasv3dOLD_6 crio wnfc friotasv3dOLD_1 friotasv3dOLD_4 cv friotasv3dOLD_8 wceq wi friotasv3dOLD_5 friotasv3dOLD_7 wral friotasv3dOLD_5 friotasv3dOLD_4 friotasv3dOLD_6 friotasv3dOLD_1 friotasv3dOLD_4 cv friotasv3dOLD_8 wceq wi friotasv3dOLD_5 friotasv3dOLD_7 nfra1 friotasv3dOLD_5 friotasv3dOLD_6 nfcv nfriota friotasv3dOLD_0 friotasv3dOLD_5 friotasv3dOLD_9 friotasv3dOLD_1 friotasv3dOLD_4 cv friotasv3dOLD_8 wceq wi friotasv3dOLD_5 friotasv3dOLD_7 wral friotasv3dOLD_4 friotasv3dOLD_6 crio friotasv3dOLD_0 friotasv3dOLD_5 eriotasv3dOLD_1 nfi eriotasv3dOLD_3 nfceqdf mpbiri friotasv3dOLD_0 friotasv3dOLD_5 friotasv3dOLD_6 nfcvd nfeld nfand friotasv3dOLD_6 cvv wcel friotasv3dOLD_9 friotasv3dOLD_6 wcel wa friotasv3dOLD_1 friotasv3dOLD_3 wi friotasv3dOLD_5 friotasv3dOLD_7 r19.21t syl mpbid friotasv3dOLD_0 friotasv3dOLD_3 friotasv3dOLD_5 wnf friotasv3dOLD_1 friotasv3dOLD_3 wi friotasv3dOLD_5 friotasv3dOLD_7 wral friotasv3dOLD_1 friotasv3dOLD_5 friotasv3dOLD_7 wrex friotasv3dOLD_3 wi wb friotasv3dOLD_0 friotasv3dOLD_3 friotasv3dOLD_5 friotasv3dOLD_0 friotasv3dOLD_5 eriotasv3dOLD_1 nfi eriotasv3dOLD_2 nfd friotasv3dOLD_1 friotasv3dOLD_3 friotasv3dOLD_5 friotasv3dOLD_7 r19.23t syl sylibd exp3a syl5 3imp2 $.
$}

