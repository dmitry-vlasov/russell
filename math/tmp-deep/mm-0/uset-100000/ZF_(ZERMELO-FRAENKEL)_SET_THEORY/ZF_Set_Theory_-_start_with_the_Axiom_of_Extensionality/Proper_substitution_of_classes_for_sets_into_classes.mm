$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Proper_substitution_of_classes_for_sets.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Proper substitution of classes for sets into classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c [_  $.
$( Underlined left bracket $)
$c ]_  $.
$( Underlined right bracket $)
$( Extend class notation to include the proper substitution of a class for a
     set into another class. $)
${
	$v x $.
	$v A $.
	$v B $.
	fcsb_0 $f set x $.
	fcsb_1 $f class A $.
	fcsb_2 $f class B $.
	csb $a class [_ A / x ]_ B $.
$}
$( Define the proper substitution of a class for a set into another class.
       The underlined brackets distinguish it from the substitution into a wff,
       ~ wsbc , to prevent ambiguity.  Theorem ~ sbcel1g shows an example of
       how ambiguity could arise if we didn't use distinguished brackets.
       Theorem ~ sbccsbg recreates substitution into a wff from this
       definition.  (Contributed by NM, 10-Nov-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d y A $.
	$d y B $.
	$d x y $.
	fdf-csb_0 $f set x $.
	fdf-csb_1 $f set y $.
	fdf-csb_2 $f class A $.
	fdf-csb_3 $f class B $.
	df-csb $a |- [_ A / x ]_ B = { y | [. A / x ]. y e. B } $.
$}
$( Alternate expression for the proper substitution into a class, without
       referencing substitution into a wff.  Note that ` x ` can be free in
       ` B ` but cannot occur in ` A ` .  (Contributed by NM, 2-Dec-2013.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y A $.
	$d y B $.
	$d x y $.
	fcsb2_0 $f set x $.
	fcsb2_1 $f set y $.
	fcsb2_2 $f class A $.
	fcsb2_3 $f class B $.
	csb2 $p |- [_ A / x ]_ B = { y | E. x ( x = A /\ y e. B ) } $= fcsb2_0 fcsb2_2 fcsb2_3 csb fcsb2_1 cv fcsb2_3 wcel fcsb2_0 fcsb2_2 wsbc fcsb2_1 cab fcsb2_0 cv fcsb2_2 wceq fcsb2_1 cv fcsb2_3 wcel wa fcsb2_0 wex fcsb2_1 cab fcsb2_0 fcsb2_1 fcsb2_2 fcsb2_3 df-csb fcsb2_1 cv fcsb2_3 wcel fcsb2_0 fcsb2_2 wsbc fcsb2_0 cv fcsb2_2 wceq fcsb2_1 cv fcsb2_3 wcel wa fcsb2_0 wex fcsb2_1 fcsb2_1 cv fcsb2_3 wcel fcsb2_0 fcsb2_2 sbc5 abbii eqtri $.
$}
$( Analog of ~ dfsbcq for proper substitution into a class.  (Contributed
       by NM, 10-Nov-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	$d y A $.
	$d y B $.
	$d y C $.
	icsbeq1_0 $f set y $.
	fcsbeq1_0 $f set x $.
	fcsbeq1_1 $f class A $.
	fcsbeq1_2 $f class B $.
	fcsbeq1_3 $f class C $.
	csbeq1 $p |- ( A = B -> [_ A / x ]_ C = [_ B / x ]_ C ) $= fcsbeq1_1 fcsbeq1_2 wceq icsbeq1_0 cv fcsbeq1_3 wcel fcsbeq1_0 fcsbeq1_1 wsbc icsbeq1_0 cab icsbeq1_0 cv fcsbeq1_3 wcel fcsbeq1_0 fcsbeq1_2 wsbc icsbeq1_0 cab fcsbeq1_0 fcsbeq1_1 fcsbeq1_3 csb fcsbeq1_0 fcsbeq1_2 fcsbeq1_3 csb fcsbeq1_1 fcsbeq1_2 wceq icsbeq1_0 cv fcsbeq1_3 wcel fcsbeq1_0 fcsbeq1_1 wsbc icsbeq1_0 cv fcsbeq1_3 wcel fcsbeq1_0 fcsbeq1_2 wsbc icsbeq1_0 icsbeq1_0 cv fcsbeq1_3 wcel fcsbeq1_0 fcsbeq1_1 fcsbeq1_2 dfsbcq abbidv fcsbeq1_0 icsbeq1_0 fcsbeq1_1 fcsbeq1_3 df-csb fcsbeq1_0 icsbeq1_0 fcsbeq1_2 fcsbeq1_3 df-csb 3eqtr4g $.
$}
$( Change bound variables in a class substitution.  Interestingly, this
       does not require any bound variable conditions on ` A ` .  (Contributed
       by Jeff Hankins, 13-Sep-2009.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v C $.
	$v D $.
	$d x z $.
	$d y z $.
	$d z A $.
	$d z C $.
	$d z D $.
	icbvcsb_0 $f set z $.
	fcbvcsb_0 $f set x $.
	fcbvcsb_1 $f set y $.
	fcbvcsb_2 $f class A $.
	fcbvcsb_3 $f class C $.
	fcbvcsb_4 $f class D $.
	ecbvcsb_0 $e |- F/_ y C $.
	ecbvcsb_1 $e |- F/_ x D $.
	ecbvcsb_2 $e |- ( x = y -> C = D ) $.
	cbvcsb $p |- [_ A / x ]_ C = [_ A / y ]_ D $= icbvcsb_0 cv fcbvcsb_3 wcel fcbvcsb_0 fcbvcsb_2 wsbc icbvcsb_0 cab icbvcsb_0 cv fcbvcsb_4 wcel fcbvcsb_1 fcbvcsb_2 wsbc icbvcsb_0 cab fcbvcsb_0 fcbvcsb_2 fcbvcsb_3 csb fcbvcsb_1 fcbvcsb_2 fcbvcsb_4 csb icbvcsb_0 cv fcbvcsb_3 wcel fcbvcsb_0 fcbvcsb_2 wsbc icbvcsb_0 cv fcbvcsb_4 wcel fcbvcsb_1 fcbvcsb_2 wsbc icbvcsb_0 icbvcsb_0 cv fcbvcsb_3 wcel icbvcsb_0 cv fcbvcsb_4 wcel fcbvcsb_0 fcbvcsb_1 fcbvcsb_2 fcbvcsb_1 icbvcsb_0 fcbvcsb_3 ecbvcsb_0 nfcri fcbvcsb_0 icbvcsb_0 fcbvcsb_4 ecbvcsb_1 nfcri fcbvcsb_0 cv fcbvcsb_1 cv wceq fcbvcsb_3 fcbvcsb_4 icbvcsb_0 cv ecbvcsb_2 eleq2d cbvsbc abbii fcbvcsb_0 icbvcsb_0 fcbvcsb_2 fcbvcsb_3 df-csb fcbvcsb_1 icbvcsb_0 fcbvcsb_2 fcbvcsb_4 df-csb 3eqtr4i $.
$}
$( Change the bound variable of a proper substitution into a class using
       implicit substitution.  (Contributed by NM, 30-Sep-2008.)  (Revised by
       Mario Carneiro, 13-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	$d y B $.
	$d x C $.
	fcbvcsbv_0 $f set x $.
	fcbvcsbv_1 $f set y $.
	fcbvcsbv_2 $f class A $.
	fcbvcsbv_3 $f class B $.
	fcbvcsbv_4 $f class C $.
	ecbvcsbv_0 $e |- ( x = y -> B = C ) $.
	cbvcsbv $p |- [_ A / x ]_ B = [_ A / y ]_ C $= fcbvcsbv_0 fcbvcsbv_1 fcbvcsbv_2 fcbvcsbv_3 fcbvcsbv_4 fcbvcsbv_1 fcbvcsbv_3 nfcv fcbvcsbv_0 fcbvcsbv_4 nfcv ecbvcsbv_0 cbvcsb $.
$}
$( Equality deduction for proper substitution into a class.  (Contributed
       by NM, 3-Dec-2005.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	fcsbeq1d_0 $f wff ph $.
	fcsbeq1d_1 $f set x $.
	fcsbeq1d_2 $f class A $.
	fcsbeq1d_3 $f class B $.
	fcsbeq1d_4 $f class C $.
	ecsbeq1d_0 $e |- ( ph -> A = B ) $.
	csbeq1d $p |- ( ph -> [_ A / x ]_ C = [_ B / x ]_ C ) $= fcsbeq1d_0 fcsbeq1d_2 fcsbeq1d_3 wceq fcsbeq1d_1 fcsbeq1d_2 fcsbeq1d_4 csb fcsbeq1d_1 fcsbeq1d_3 fcsbeq1d_4 csb wceq ecsbeq1d_0 fcsbeq1d_1 fcsbeq1d_2 fcsbeq1d_3 fcsbeq1d_4 csbeq1 syl $.
$}
$( Analog of ~ sbid for proper substitution into a class.  (Contributed by
       NM, 10-Nov-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$d x y $.
	$d y A $.
	icsbid_0 $f set y $.
	fcsbid_0 $f set x $.
	fcsbid_1 $f class A $.
	csbid $p |- [_ x / x ]_ A = A $= fcsbid_0 fcsbid_0 cv fcsbid_1 csb icsbid_0 cv fcsbid_1 wcel fcsbid_0 fcsbid_0 cv wsbc icsbid_0 cab icsbid_0 cv fcsbid_1 wcel icsbid_0 cab fcsbid_1 fcsbid_0 icsbid_0 fcsbid_0 cv fcsbid_1 df-csb icsbid_0 cv fcsbid_1 wcel fcsbid_0 fcsbid_0 cv wsbc icsbid_0 cv fcsbid_1 wcel icsbid_0 icsbid_0 cv fcsbid_1 wcel fcsbid_0 fcsbid_0 cv wsbc icsbid_0 cv fcsbid_1 wcel fcsbid_0 fcsbid_0 wsb icsbid_0 cv fcsbid_1 wcel icsbid_0 cv fcsbid_1 wcel fcsbid_0 fcsbid_0 sbsbc icsbid_0 cv fcsbid_1 wcel fcsbid_0 sbid bitr3i abbii icsbid_0 fcsbid_1 abid2 3eqtri $.
$}
$( Equality theorem for proper substitution into a class.  (Contributed by
       NM, 10-Nov-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	fcsbeq1a_0 $f set x $.
	fcsbeq1a_1 $f class A $.
	fcsbeq1a_2 $f class B $.
	csbeq1a $p |- ( x = A -> B = [_ A / x ]_ B ) $= fcsbeq1a_0 cv fcsbeq1a_1 wceq fcsbeq1a_2 fcsbeq1a_0 fcsbeq1a_0 cv fcsbeq1a_2 csb fcsbeq1a_0 fcsbeq1a_1 fcsbeq1a_2 csb fcsbeq1a_0 fcsbeq1a_2 csbid fcsbeq1a_0 fcsbeq1a_0 cv fcsbeq1a_1 fcsbeq1a_2 csbeq1 syl5eqr $.
$}
$( Composition law for chained substitutions into a class.  (Contributed by
       NM, 10-Nov-2005.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d z A $.
	$d y z B $.
	$d x z $.
	icsbco_0 $f set z $.
	fcsbco_0 $f set x $.
	fcsbco_1 $f set y $.
	fcsbco_2 $f class A $.
	fcsbco_3 $f class B $.
	csbco $p |- [_ A / y ]_ [_ y / x ]_ B = [_ A / x ]_ B $= icsbco_0 cv fcsbco_0 fcsbco_1 cv fcsbco_3 csb wcel fcsbco_1 fcsbco_2 wsbc icsbco_0 cab icsbco_0 cv fcsbco_3 wcel fcsbco_0 fcsbco_2 wsbc icsbco_0 cab fcsbco_1 fcsbco_2 fcsbco_0 fcsbco_1 cv fcsbco_3 csb csb fcsbco_0 fcsbco_2 fcsbco_3 csb icsbco_0 cv fcsbco_0 fcsbco_1 cv fcsbco_3 csb wcel fcsbco_1 fcsbco_2 wsbc icsbco_0 cv fcsbco_3 wcel fcsbco_0 fcsbco_2 wsbc icsbco_0 icsbco_0 cv fcsbco_0 fcsbco_1 cv fcsbco_3 csb wcel fcsbco_1 fcsbco_2 wsbc icsbco_0 cv fcsbco_3 wcel fcsbco_0 fcsbco_1 cv wsbc fcsbco_1 fcsbco_2 wsbc icsbco_0 cv fcsbco_3 wcel fcsbco_0 fcsbco_2 wsbc icsbco_0 cv fcsbco_0 fcsbco_1 cv fcsbco_3 csb wcel icsbco_0 cv fcsbco_3 wcel fcsbco_0 fcsbco_1 cv wsbc fcsbco_1 fcsbco_2 icsbco_0 cv fcsbco_3 wcel fcsbco_0 fcsbco_1 cv wsbc icsbco_0 fcsbco_0 fcsbco_1 cv fcsbco_3 csb fcsbco_0 icsbco_0 fcsbco_1 cv fcsbco_3 df-csb abeq2i sbcbii icsbco_0 cv fcsbco_3 wcel fcsbco_0 fcsbco_1 fcsbco_2 sbcco bitri abbii fcsbco_1 icsbco_0 fcsbco_2 fcsbco_0 fcsbco_1 cv fcsbco_3 csb df-csb fcsbco_0 icsbco_0 fcsbco_2 fcsbco_3 df-csb 3eqtr4i $.
$}
$( The existence of proper substitution into a class.  (Contributed by NM,
       10-Nov-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$v W $.
	$d y A $.
	$d y B $.
	$d x y $.
	icsbexg_0 $f set y $.
	fcsbexg_0 $f set x $.
	fcsbexg_1 $f class A $.
	fcsbexg_2 $f class B $.
	fcsbexg_3 $f class V $.
	fcsbexg_4 $f class W $.
	csbexg $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ B e. _V ) $= fcsbexg_1 fcsbexg_3 wcel fcsbexg_2 fcsbexg_4 wcel fcsbexg_0 wal wa fcsbexg_0 fcsbexg_1 fcsbexg_2 csb icsbexg_0 cv fcsbexg_2 wcel fcsbexg_0 fcsbexg_1 wsbc icsbexg_0 cab cvv fcsbexg_0 icsbexg_0 fcsbexg_1 fcsbexg_2 df-csb fcsbexg_1 fcsbexg_3 wcel fcsbexg_2 fcsbexg_4 wcel fcsbexg_0 wal wa icsbexg_0 cv fcsbexg_2 wcel icsbexg_0 cab cvv wcel fcsbexg_0 fcsbexg_1 wsbc icsbexg_0 cv fcsbexg_2 wcel fcsbexg_0 fcsbexg_1 wsbc icsbexg_0 cab cvv wcel fcsbexg_1 fcsbexg_3 wcel fcsbexg_2 fcsbexg_4 wcel fcsbexg_0 wal icsbexg_0 cv fcsbexg_2 wcel icsbexg_0 cab cvv wcel fcsbexg_0 fcsbexg_1 wsbc fcsbexg_2 fcsbexg_4 wcel fcsbexg_0 wal icsbexg_0 cv fcsbexg_2 wcel icsbexg_0 cab cvv wcel fcsbexg_0 wal fcsbexg_1 fcsbexg_3 wcel icsbexg_0 cv fcsbexg_2 wcel icsbexg_0 cab cvv wcel fcsbexg_0 fcsbexg_1 wsbc fcsbexg_2 fcsbexg_4 wcel icsbexg_0 cv fcsbexg_2 wcel icsbexg_0 cab cvv wcel fcsbexg_0 fcsbexg_2 fcsbexg_4 wcel icsbexg_0 cv fcsbexg_2 wcel icsbexg_0 cab fcsbexg_2 cvv icsbexg_0 fcsbexg_2 abid2 fcsbexg_2 fcsbexg_4 elex syl5eqel alimi icsbexg_0 cv fcsbexg_2 wcel icsbexg_0 cab cvv wcel fcsbexg_0 fcsbexg_1 fcsbexg_3 spsbc syl5 imp fcsbexg_1 fcsbexg_3 wcel icsbexg_0 cv fcsbexg_2 wcel icsbexg_0 cab cvv wcel fcsbexg_0 fcsbexg_1 wsbc icsbexg_0 cv fcsbexg_2 wcel fcsbexg_0 fcsbexg_1 wsbc icsbexg_0 cab cvv wcel wb fcsbexg_2 fcsbexg_4 wcel fcsbexg_0 wal icsbexg_0 cv fcsbexg_2 wcel fcsbexg_0 icsbexg_0 fcsbexg_1 cvv fcsbexg_3 fcsbexg_0 cvv nfcv sbcabel adantr mpbid syl5eqel $.
$}
$( The existence of proper substitution into a class.  (Contributed by NM,
       7-Aug-2007.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	fcsbex_0 $f set x $.
	fcsbex_1 $f class A $.
	fcsbex_2 $f class B $.
	ecsbex_0 $e |- A e. _V $.
	ecsbex_1 $e |- B e. _V $.
	csbex $p |- [_ A / x ]_ B e. _V $= fcsbex_2 cvv wcel fcsbex_0 fcsbex_1 fcsbex_2 csb cvv wcel fcsbex_0 fcsbex_1 cvv wcel fcsbex_2 cvv wcel fcsbex_0 wal fcsbex_0 fcsbex_1 fcsbex_2 csb cvv wcel ecsbex_0 fcsbex_0 fcsbex_1 fcsbex_2 cvv cvv csbexg mpan ecsbex_1 mpg $.
$}
$( Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free).  (Contributed by Mario Carneiro, 14-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$d y A $.
	$d y B $.
	$d y V $.
	$d x y $.
	icsbtt_0 $f set y $.
	fcsbtt_0 $f set x $.
	fcsbtt_1 $f class A $.
	fcsbtt_2 $f class B $.
	fcsbtt_3 $f class V $.
	csbtt $p |- ( ( A e. V /\ F/_ x B ) -> [_ A / x ]_ B = B ) $= fcsbtt_1 fcsbtt_3 wcel fcsbtt_0 fcsbtt_2 wnfc wa fcsbtt_0 fcsbtt_1 fcsbtt_2 csb icsbtt_0 cv fcsbtt_2 wcel fcsbtt_0 fcsbtt_1 wsbc icsbtt_0 cab fcsbtt_2 fcsbtt_0 icsbtt_0 fcsbtt_1 fcsbtt_2 df-csb fcsbtt_1 fcsbtt_3 wcel fcsbtt_0 fcsbtt_2 wnfc wa icsbtt_0 cv fcsbtt_2 wcel fcsbtt_0 fcsbtt_1 wsbc icsbtt_0 fcsbtt_2 fcsbtt_0 fcsbtt_2 wnfc fcsbtt_1 fcsbtt_3 wcel icsbtt_0 cv fcsbtt_2 wcel fcsbtt_0 wnf icsbtt_0 cv fcsbtt_2 wcel fcsbtt_0 fcsbtt_1 wsbc icsbtt_0 cv fcsbtt_2 wcel wb fcsbtt_0 icsbtt_0 fcsbtt_2 nfcr icsbtt_0 cv fcsbtt_2 wcel fcsbtt_0 fcsbtt_1 fcsbtt_3 sbctt sylan2 abbi1dv syl5eq $.
$}
$( Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free).  (Contributed by NM, 10-Nov-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v V $.
	fcsbconstgf_0 $f set x $.
	fcsbconstgf_1 $f class A $.
	fcsbconstgf_2 $f class B $.
	fcsbconstgf_3 $f class V $.
	ecsbconstgf_0 $e |- F/_ x B $.
	csbconstgf $p |- ( A e. V -> [_ A / x ]_ B = B ) $= fcsbconstgf_1 fcsbconstgf_3 wcel fcsbconstgf_0 fcsbconstgf_2 wnfc fcsbconstgf_0 fcsbconstgf_1 fcsbconstgf_2 csb fcsbconstgf_2 wceq ecsbconstgf_0 fcsbconstgf_0 fcsbconstgf_1 fcsbconstgf_2 fcsbconstgf_3 csbtt mpan2 $.
$}
$( Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free). ~ csbconstgf with distinct variable requirement.  (Contributed by
       Alan Sare, 22-Jul-2012.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v V $.
	$d B x $.
	fcsbconstg_0 $f set x $.
	fcsbconstg_1 $f class A $.
	fcsbconstg_2 $f class B $.
	fcsbconstg_3 $f class V $.
	csbconstg $p |- ( A e. V -> [_ A / x ]_ B = B ) $= fcsbconstg_0 fcsbconstg_1 fcsbconstg_2 fcsbconstg_3 fcsbconstg_0 fcsbconstg_2 nfcv csbconstgf $.
$}
$( Distribute proper substitution through a membership relation.
       (Contributed by NM, 10-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x y z $.
	$d y z A $.
	$d y z B $.
	$d y z C $.
	isbcel12g_0 $f set y $.
	isbcel12g_1 $f set z $.
	fsbcel12g_0 $f set x $.
	fsbcel12g_1 $f class A $.
	fsbcel12g_2 $f class B $.
	fsbcel12g_3 $f class C $.
	fsbcel12g_4 $f class V $.
	sbcel12g $p |- ( A e. V -> ( [. A / x ]. B e. C <-> [_ A / x ]_ B e. [_ A / x ]_ C ) ) $= fsbcel12g_1 fsbcel12g_4 wcel fsbcel12g_2 fsbcel12g_3 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cab wcel fsbcel12g_0 fsbcel12g_1 fsbcel12g_2 csb fsbcel12g_0 fsbcel12g_1 fsbcel12g_3 csb wcel fsbcel12g_2 fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab wcel fsbcel12g_2 fsbcel12g_3 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cab wcel isbcel12g_1 fsbcel12g_1 fsbcel12g_4 fsbcel12g_2 fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 fsbcel12g_1 dfsbcq2 isbcel12g_1 cv fsbcel12g_1 wceq isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cab isbcel12g_1 cv fsbcel12g_1 wceq isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 fsbcel12g_1 dfsbcq2 abbidv isbcel12g_1 cv fsbcel12g_1 wceq isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 fsbcel12g_1 dfsbcq2 abbidv eleq12d fsbcel12g_2 fsbcel12g_3 wcel isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab wcel fsbcel12g_0 isbcel12g_1 fsbcel12g_0 isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 wsb fsbcel12g_0 isbcel12g_0 isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 nfs1v nfab isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 wsb fsbcel12g_0 isbcel12g_0 isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 nfs1v nfab nfel fsbcel12g_0 isbcel12g_1 weq fsbcel12g_2 isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab fsbcel12g_3 isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 isbcel12g_1 wsb isbcel12g_0 cab fsbcel12g_0 isbcel12g_1 isbcel12g_0 fsbcel12g_2 sbab fsbcel12g_0 isbcel12g_1 isbcel12g_0 fsbcel12g_3 sbab eleq12d sbie vtoclbg fsbcel12g_0 fsbcel12g_1 fsbcel12g_2 csb isbcel12g_0 cv fsbcel12g_2 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cab fsbcel12g_0 fsbcel12g_1 fsbcel12g_3 csb isbcel12g_0 cv fsbcel12g_3 wcel fsbcel12g_0 fsbcel12g_1 wsbc isbcel12g_0 cab fsbcel12g_0 isbcel12g_0 fsbcel12g_1 fsbcel12g_2 df-csb fsbcel12g_0 isbcel12g_0 fsbcel12g_1 fsbcel12g_3 df-csb eleq12i syl6bbr $.
$}
$( Distribute proper substitution through an equality relation.
       (Contributed by NM, 10-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x y z $.
	$d y z A $.
	$d y z B $.
	$d y z C $.
	isbceqg_0 $f set y $.
	isbceqg_1 $f set z $.
	fsbceqg_0 $f set x $.
	fsbceqg_1 $f class A $.
	fsbceqg_2 $f class B $.
	fsbceqg_3 $f class C $.
	fsbceqg_4 $f class V $.
	sbceqg $p |- ( A e. V -> ( [. A / x ]. B = C <-> [_ A / x ]_ B = [_ A / x ]_ C ) ) $= fsbceqg_1 fsbceqg_4 wcel fsbceqg_2 fsbceqg_3 wceq fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cab isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cab wceq fsbceqg_0 fsbceqg_1 fsbceqg_2 csb fsbceqg_0 fsbceqg_1 fsbceqg_3 csb wceq fsbceqg_2 fsbceqg_3 wceq fsbceqg_0 isbceqg_1 wsb isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab wceq fsbceqg_2 fsbceqg_3 wceq fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cab isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cab wceq isbceqg_1 fsbceqg_1 fsbceqg_4 fsbceqg_2 fsbceqg_3 wceq fsbceqg_0 isbceqg_1 fsbceqg_1 dfsbcq2 isbceqg_1 cv fsbceqg_1 wceq isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cab isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cab isbceqg_1 cv fsbceqg_1 wceq isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 fsbceqg_1 dfsbcq2 abbidv isbceqg_1 cv fsbceqg_1 wceq isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 fsbceqg_1 dfsbcq2 abbidv eqeq12d fsbceqg_2 fsbceqg_3 wceq isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab wceq fsbceqg_0 isbceqg_1 fsbceqg_0 isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 wsb fsbceqg_0 isbceqg_0 isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 nfs1v nfab isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 wsb fsbceqg_0 isbceqg_0 isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 nfs1v nfab nfeq fsbceqg_0 isbceqg_1 weq fsbceqg_2 isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab fsbceqg_3 isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 isbceqg_1 wsb isbceqg_0 cab fsbceqg_0 isbceqg_1 isbceqg_0 fsbceqg_2 sbab fsbceqg_0 isbceqg_1 isbceqg_0 fsbceqg_3 sbab eqeq12d sbie vtoclbg fsbceqg_0 fsbceqg_1 fsbceqg_2 csb isbceqg_0 cv fsbceqg_2 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cab fsbceqg_0 fsbceqg_1 fsbceqg_3 csb isbceqg_0 cv fsbceqg_3 wcel fsbceqg_0 fsbceqg_1 wsbc isbceqg_0 cab fsbceqg_0 isbceqg_0 fsbceqg_1 fsbceqg_2 df-csb fsbceqg_0 isbceqg_0 fsbceqg_1 fsbceqg_3 df-csb eqeq12i syl6bbr $.
$}
$( Distribute proper substitution through negated membership.  (Contributed
     by Andrew Salmon, 18-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	fsbcnel12g_0 $f set x $.
	fsbcnel12g_1 $f class A $.
	fsbcnel12g_2 $f class B $.
	fsbcnel12g_3 $f class C $.
	fsbcnel12g_4 $f class V $.
	sbcnel12g $p |- ( A e. V -> ( [. A / x ]. B e/ C <-> [_ A / x ]_ B e/ [_ A / x ]_ C ) ) $= fsbcnel12g_1 fsbcnel12g_4 wcel fsbcnel12g_2 fsbcnel12g_3 wnel fsbcnel12g_0 fsbcnel12g_1 wsbc fsbcnel12g_2 fsbcnel12g_3 wcel wn fsbcnel12g_0 fsbcnel12g_1 wsbc fsbcnel12g_2 fsbcnel12g_3 wcel fsbcnel12g_0 fsbcnel12g_1 wsbc wn fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_2 csb fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_3 csb wnel fsbcnel12g_2 fsbcnel12g_3 wnel fsbcnel12g_0 fsbcnel12g_1 wsbc fsbcnel12g_2 fsbcnel12g_3 wcel wn fsbcnel12g_0 fsbcnel12g_1 wsbc wb fsbcnel12g_1 fsbcnel12g_4 wcel fsbcnel12g_2 fsbcnel12g_3 wnel fsbcnel12g_2 fsbcnel12g_3 wcel wn fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_2 fsbcnel12g_3 df-nel sbcbii a1i fsbcnel12g_2 fsbcnel12g_3 wcel fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_4 sbcng fsbcnel12g_1 fsbcnel12g_4 wcel fsbcnel12g_2 fsbcnel12g_3 wcel fsbcnel12g_0 fsbcnel12g_1 wsbc wn fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_2 csb fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_3 csb wcel wn fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_2 csb fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_3 csb wnel fsbcnel12g_1 fsbcnel12g_4 wcel fsbcnel12g_2 fsbcnel12g_3 wcel fsbcnel12g_0 fsbcnel12g_1 wsbc fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_2 csb fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_3 csb wcel fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_2 fsbcnel12g_3 fsbcnel12g_4 sbcel12g notbid fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_2 csb fsbcnel12g_0 fsbcnel12g_1 fsbcnel12g_3 csb df-nel syl6bbr 3bitrd $.
$}
$( Distribute proper substitution through an inequality.  (Contributed by
     Andrew Salmon, 18-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	fsbcne12g_0 $f set x $.
	fsbcne12g_1 $f class A $.
	fsbcne12g_2 $f class B $.
	fsbcne12g_3 $f class C $.
	fsbcne12g_4 $f class V $.
	sbcne12g $p |- ( A e. V -> ( [. A / x ]. B =/= C <-> [_ A / x ]_ B =/= [_ A / x ]_ C ) ) $= fsbcne12g_1 fsbcne12g_4 wcel fsbcne12g_2 fsbcne12g_3 wne fsbcne12g_0 fsbcne12g_1 wsbc fsbcne12g_0 fsbcne12g_1 fsbcne12g_2 csb fsbcne12g_0 fsbcne12g_1 fsbcne12g_3 csb wne fsbcne12g_1 fsbcne12g_4 wcel fsbcne12g_2 fsbcne12g_3 wne wn fsbcne12g_0 fsbcne12g_1 wsbc fsbcne12g_2 fsbcne12g_3 wceq fsbcne12g_0 fsbcne12g_1 wsbc fsbcne12g_2 fsbcne12g_3 wne fsbcne12g_0 fsbcne12g_1 wsbc wn fsbcne12g_0 fsbcne12g_1 fsbcne12g_2 csb fsbcne12g_0 fsbcne12g_1 fsbcne12g_3 csb wne wn fsbcne12g_2 fsbcne12g_3 wne wn fsbcne12g_0 fsbcne12g_1 wsbc fsbcne12g_2 fsbcne12g_3 wceq fsbcne12g_0 fsbcne12g_1 wsbc wb fsbcne12g_1 fsbcne12g_4 wcel fsbcne12g_2 fsbcne12g_3 wne wn fsbcne12g_2 fsbcne12g_3 wceq fsbcne12g_0 fsbcne12g_1 fsbcne12g_2 fsbcne12g_3 nne sbcbii a1i fsbcne12g_2 fsbcne12g_3 wne fsbcne12g_0 fsbcne12g_1 fsbcne12g_4 sbcng fsbcne12g_1 fsbcne12g_4 wcel fsbcne12g_2 fsbcne12g_3 wceq fsbcne12g_0 fsbcne12g_1 wsbc fsbcne12g_0 fsbcne12g_1 fsbcne12g_2 csb fsbcne12g_0 fsbcne12g_1 fsbcne12g_3 csb wceq fsbcne12g_0 fsbcne12g_1 fsbcne12g_2 csb fsbcne12g_0 fsbcne12g_1 fsbcne12g_3 csb wne wn fsbcne12g_0 fsbcne12g_1 fsbcne12g_2 fsbcne12g_3 fsbcne12g_4 sbceqg fsbcne12g_0 fsbcne12g_1 fsbcne12g_2 csb fsbcne12g_0 fsbcne12g_1 fsbcne12g_3 csb nne syl6bbr 3bitr3d con4bid $.
$}
$( Move proper substitution in and out of a membership relation.  Note that
       the scope of ` [. A / x ]. ` is the wff ` B e. C ` , whereas the scope
       of ` [_ A / x ]_ ` is the class ` B ` .  (Contributed by NM,
       10-Nov-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x C $.
	fsbcel1g_0 $f set x $.
	fsbcel1g_1 $f class A $.
	fsbcel1g_2 $f class B $.
	fsbcel1g_3 $f class C $.
	fsbcel1g_4 $f class V $.
	sbcel1g $p |- ( A e. V -> ( [. A / x ]. B e. C <-> [_ A / x ]_ B e. C ) ) $= fsbcel1g_1 fsbcel1g_4 wcel fsbcel1g_2 fsbcel1g_3 wcel fsbcel1g_0 fsbcel1g_1 wsbc fsbcel1g_0 fsbcel1g_1 fsbcel1g_2 csb fsbcel1g_0 fsbcel1g_1 fsbcel1g_3 csb wcel fsbcel1g_0 fsbcel1g_1 fsbcel1g_2 csb fsbcel1g_3 wcel fsbcel1g_0 fsbcel1g_1 fsbcel1g_2 fsbcel1g_3 fsbcel1g_4 sbcel12g fsbcel1g_1 fsbcel1g_4 wcel fsbcel1g_0 fsbcel1g_1 fsbcel1g_3 csb fsbcel1g_3 fsbcel1g_0 fsbcel1g_1 fsbcel1g_2 csb fsbcel1g_0 fsbcel1g_1 fsbcel1g_3 fsbcel1g_4 csbconstg eleq2d bitrd $.
$}
$( Move proper substitution to first argument of an equality.  (Contributed
       by NM, 30-Nov-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x C $.
	fsbceq1g_0 $f set x $.
	fsbceq1g_1 $f class A $.
	fsbceq1g_2 $f class B $.
	fsbceq1g_3 $f class C $.
	fsbceq1g_4 $f class V $.
	sbceq1g $p |- ( A e. V -> ( [. A / x ]. B = C <-> [_ A / x ]_ B = C ) ) $= fsbceq1g_1 fsbceq1g_4 wcel fsbceq1g_2 fsbceq1g_3 wceq fsbceq1g_0 fsbceq1g_1 wsbc fsbceq1g_0 fsbceq1g_1 fsbceq1g_2 csb fsbceq1g_0 fsbceq1g_1 fsbceq1g_3 csb wceq fsbceq1g_0 fsbceq1g_1 fsbceq1g_2 csb fsbceq1g_3 wceq fsbceq1g_0 fsbceq1g_1 fsbceq1g_2 fsbceq1g_3 fsbceq1g_4 sbceqg fsbceq1g_1 fsbceq1g_4 wcel fsbceq1g_0 fsbceq1g_1 fsbceq1g_3 csb fsbceq1g_3 fsbceq1g_0 fsbceq1g_1 fsbceq1g_2 csb fsbceq1g_0 fsbceq1g_1 fsbceq1g_3 fsbceq1g_4 csbconstg eqeq2d bitrd $.
$}
$( Move proper substitution in and out of a membership relation.
       (Contributed by NM, 14-Nov-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x B $.
	fsbcel2g_0 $f set x $.
	fsbcel2g_1 $f class A $.
	fsbcel2g_2 $f class B $.
	fsbcel2g_3 $f class C $.
	fsbcel2g_4 $f class V $.
	sbcel2g $p |- ( A e. V -> ( [. A / x ]. B e. C <-> B e. [_ A / x ]_ C ) ) $= fsbcel2g_1 fsbcel2g_4 wcel fsbcel2g_2 fsbcel2g_3 wcel fsbcel2g_0 fsbcel2g_1 wsbc fsbcel2g_0 fsbcel2g_1 fsbcel2g_2 csb fsbcel2g_0 fsbcel2g_1 fsbcel2g_3 csb wcel fsbcel2g_2 fsbcel2g_0 fsbcel2g_1 fsbcel2g_3 csb wcel fsbcel2g_0 fsbcel2g_1 fsbcel2g_2 fsbcel2g_3 fsbcel2g_4 sbcel12g fsbcel2g_1 fsbcel2g_4 wcel fsbcel2g_0 fsbcel2g_1 fsbcel2g_2 csb fsbcel2g_2 fsbcel2g_0 fsbcel2g_1 fsbcel2g_3 csb fsbcel2g_0 fsbcel2g_1 fsbcel2g_2 fsbcel2g_4 csbconstg eleq1d bitrd $.
$}
$( Move proper substitution to second argument of an equality.
       (Contributed by NM, 30-Nov-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x B $.
	fsbceq2g_0 $f set x $.
	fsbceq2g_1 $f class A $.
	fsbceq2g_2 $f class B $.
	fsbceq2g_3 $f class C $.
	fsbceq2g_4 $f class V $.
	sbceq2g $p |- ( A e. V -> ( [. A / x ]. B = C <-> B = [_ A / x ]_ C ) ) $= fsbceq2g_1 fsbceq2g_4 wcel fsbceq2g_2 fsbceq2g_3 wceq fsbceq2g_0 fsbceq2g_1 wsbc fsbceq2g_0 fsbceq2g_1 fsbceq2g_2 csb fsbceq2g_0 fsbceq2g_1 fsbceq2g_3 csb wceq fsbceq2g_2 fsbceq2g_0 fsbceq2g_1 fsbceq2g_3 csb wceq fsbceq2g_0 fsbceq2g_1 fsbceq2g_2 fsbceq2g_3 fsbceq2g_4 sbceqg fsbceq2g_1 fsbceq2g_4 wcel fsbceq2g_0 fsbceq2g_1 fsbceq2g_2 csb fsbceq2g_2 fsbceq2g_0 fsbceq2g_1 fsbceq2g_3 csb fsbceq2g_0 fsbceq2g_1 fsbceq2g_2 fsbceq2g_4 csbconstg eqeq1d bitrd $.
$}
$( Commutative law for double substitution into a class.  (Contributed by
       NM, 14-Nov-2005.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	$d y z A $.
	$d x z B $.
	$d z C $.
	$d x y $.
	icsbcomg_0 $f set z $.
	fcsbcomg_0 $f set x $.
	fcsbcomg_1 $f set y $.
	fcsbcomg_2 $f class A $.
	fcsbcomg_3 $f class B $.
	fcsbcomg_4 $f class C $.
	fcsbcomg_5 $f class V $.
	fcsbcomg_6 $f class W $.
	csbcomg $p |- ( ( A e. V /\ B e. W ) -> [_ A / x ]_ [_ B / y ]_ C = [_ B / y ]_ [_ A / x ]_ C ) $= fcsbcomg_2 fcsbcomg_5 wcel fcsbcomg_2 cvv wcel fcsbcomg_3 cvv wcel fcsbcomg_0 fcsbcomg_2 fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb csb fcsbcomg_1 fcsbcomg_3 fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb csb wceq fcsbcomg_3 fcsbcomg_6 wcel fcsbcomg_2 fcsbcomg_5 elex fcsbcomg_3 fcsbcomg_6 elex fcsbcomg_2 cvv wcel fcsbcomg_3 cvv wcel wa icsbcomg_0 fcsbcomg_0 fcsbcomg_2 fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb csb fcsbcomg_1 fcsbcomg_3 fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb csb fcsbcomg_2 cvv wcel fcsbcomg_3 cvv wcel wa icsbcomg_0 cv fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb wcel fcsbcomg_0 fcsbcomg_2 wsbc icsbcomg_0 cv fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb wcel fcsbcomg_1 fcsbcomg_3 wsbc icsbcomg_0 cv fcsbcomg_0 fcsbcomg_2 fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb csb wcel icsbcomg_0 cv fcsbcomg_1 fcsbcomg_3 fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb csb wcel fcsbcomg_2 cvv wcel fcsbcomg_3 cvv wcel wa icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_1 fcsbcomg_3 wsbc fcsbcomg_0 fcsbcomg_2 wsbc icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_0 fcsbcomg_2 wsbc fcsbcomg_1 fcsbcomg_3 wsbc icsbcomg_0 cv fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb wcel fcsbcomg_0 fcsbcomg_2 wsbc icsbcomg_0 cv fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb wcel fcsbcomg_1 fcsbcomg_3 wsbc icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_1 fcsbcomg_3 wsbc fcsbcomg_0 fcsbcomg_2 wsbc icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_0 fcsbcomg_2 wsbc fcsbcomg_1 fcsbcomg_3 wsbc wb fcsbcomg_2 cvv wcel fcsbcomg_3 cvv wcel wa icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_0 fcsbcomg_1 fcsbcomg_2 fcsbcomg_3 sbccom a1i fcsbcomg_3 cvv wcel icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_1 fcsbcomg_3 wsbc fcsbcomg_0 fcsbcomg_2 wsbc icsbcomg_0 cv fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb wcel fcsbcomg_0 fcsbcomg_2 wsbc wb fcsbcomg_2 cvv wcel fcsbcomg_3 cvv wcel icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_1 fcsbcomg_3 wsbc icsbcomg_0 cv fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb wcel fcsbcomg_0 fcsbcomg_2 fcsbcomg_1 fcsbcomg_3 icsbcomg_0 cv fcsbcomg_4 cvv sbcel2g sbcbidv adantl fcsbcomg_2 cvv wcel icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_0 fcsbcomg_2 wsbc fcsbcomg_1 fcsbcomg_3 wsbc icsbcomg_0 cv fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb wcel fcsbcomg_1 fcsbcomg_3 wsbc wb fcsbcomg_3 cvv wcel fcsbcomg_2 cvv wcel icsbcomg_0 cv fcsbcomg_4 wcel fcsbcomg_0 fcsbcomg_2 wsbc icsbcomg_0 cv fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb wcel fcsbcomg_1 fcsbcomg_3 fcsbcomg_0 fcsbcomg_2 icsbcomg_0 cv fcsbcomg_4 cvv sbcel2g sbcbidv adantr 3bitr3d fcsbcomg_2 cvv wcel icsbcomg_0 cv fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb wcel fcsbcomg_0 fcsbcomg_2 wsbc icsbcomg_0 cv fcsbcomg_0 fcsbcomg_2 fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb csb wcel wb fcsbcomg_3 cvv wcel fcsbcomg_0 fcsbcomg_2 icsbcomg_0 cv fcsbcomg_1 fcsbcomg_3 fcsbcomg_4 csb cvv sbcel2g adantr fcsbcomg_3 cvv wcel icsbcomg_0 cv fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb wcel fcsbcomg_1 fcsbcomg_3 wsbc icsbcomg_0 cv fcsbcomg_1 fcsbcomg_3 fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb csb wcel wb fcsbcomg_2 cvv wcel fcsbcomg_1 fcsbcomg_3 icsbcomg_0 cv fcsbcomg_0 fcsbcomg_2 fcsbcomg_4 csb cvv sbcel2g adantl 3bitr3d eqrdv syl2an $.
$}
$( Formula-building deduction rule for class substitution.  (Contributed by
       NM, 22-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	$d y A $.
	$d y B $.
	$d y C $.
	$d y ph $.
	icsbeq2d_0 $f set y $.
	fcsbeq2d_0 $f wff ph $.
	fcsbeq2d_1 $f set x $.
	fcsbeq2d_2 $f class A $.
	fcsbeq2d_3 $f class B $.
	fcsbeq2d_4 $f class C $.
	ecsbeq2d_0 $e |- F/ x ph $.
	ecsbeq2d_1 $e |- ( ph -> B = C ) $.
	csbeq2d $p |- ( ph -> [_ A / x ]_ B = [_ A / x ]_ C ) $= fcsbeq2d_0 icsbeq2d_0 cv fcsbeq2d_3 wcel fcsbeq2d_1 fcsbeq2d_2 wsbc icsbeq2d_0 cab icsbeq2d_0 cv fcsbeq2d_4 wcel fcsbeq2d_1 fcsbeq2d_2 wsbc icsbeq2d_0 cab fcsbeq2d_1 fcsbeq2d_2 fcsbeq2d_3 csb fcsbeq2d_1 fcsbeq2d_2 fcsbeq2d_4 csb fcsbeq2d_0 icsbeq2d_0 cv fcsbeq2d_3 wcel fcsbeq2d_1 fcsbeq2d_2 wsbc icsbeq2d_0 cv fcsbeq2d_4 wcel fcsbeq2d_1 fcsbeq2d_2 wsbc icsbeq2d_0 fcsbeq2d_0 icsbeq2d_0 cv fcsbeq2d_3 wcel icsbeq2d_0 cv fcsbeq2d_4 wcel fcsbeq2d_1 fcsbeq2d_2 ecsbeq2d_0 fcsbeq2d_0 fcsbeq2d_3 fcsbeq2d_4 icsbeq2d_0 cv ecsbeq2d_1 eleq2d sbcbid abbidv fcsbeq2d_1 icsbeq2d_0 fcsbeq2d_2 fcsbeq2d_3 df-csb fcsbeq2d_1 icsbeq2d_0 fcsbeq2d_2 fcsbeq2d_4 df-csb 3eqtr4g $.
$}
$( Formula-building deduction rule for class substitution.  (Contributed by
       NM, 10-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x ph $.
	fcsbeq2dv_0 $f wff ph $.
	fcsbeq2dv_1 $f set x $.
	fcsbeq2dv_2 $f class A $.
	fcsbeq2dv_3 $f class B $.
	fcsbeq2dv_4 $f class C $.
	ecsbeq2dv_0 $e |- ( ph -> B = C ) $.
	csbeq2dv $p |- ( ph -> [_ A / x ]_ B = [_ A / x ]_ C ) $= fcsbeq2dv_0 fcsbeq2dv_1 fcsbeq2dv_2 fcsbeq2dv_3 fcsbeq2dv_4 fcsbeq2dv_0 fcsbeq2dv_1 nfv ecsbeq2dv_0 csbeq2d $.
$}
$( Formula-building inference rule for class substitution.  (Contributed by
       NM, 10-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	fcsbeq2i_0 $f set x $.
	fcsbeq2i_1 $f class A $.
	fcsbeq2i_2 $f class B $.
	fcsbeq2i_3 $f class C $.
	ecsbeq2i_0 $e |- B = C $.
	csbeq2i $p |- [_ A / x ]_ B = [_ A / x ]_ C $= fcsbeq2i_0 fcsbeq2i_1 fcsbeq2i_2 csb fcsbeq2i_0 fcsbeq2i_1 fcsbeq2i_3 csb wceq wtru fcsbeq2i_0 fcsbeq2i_1 fcsbeq2i_2 fcsbeq2i_3 fcsbeq2i_2 fcsbeq2i_3 wceq wtru ecsbeq2i_0 a1i csbeq2dv trud $.
$}
$( The proper substitution of a class for set variable results in the class
       (if the class exists).  (Contributed by NM, 10-Nov-2005.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v V $.
	$d y z A $.
	$d x y z $.
	icsbvarg_0 $f set y $.
	icsbvarg_1 $f set z $.
	fcsbvarg_0 $f set x $.
	fcsbvarg_1 $f class A $.
	fcsbvarg_2 $f class V $.
	csbvarg $p |- ( A e. V -> [_ A / x ]_ x = A ) $= fcsbvarg_1 fcsbvarg_2 wcel fcsbvarg_1 cvv wcel fcsbvarg_0 fcsbvarg_1 fcsbvarg_0 cv csb fcsbvarg_1 wceq fcsbvarg_1 fcsbvarg_2 elex fcsbvarg_1 cvv wcel fcsbvarg_0 fcsbvarg_1 fcsbvarg_0 cv csb icsbvarg_1 cv icsbvarg_0 cv wcel icsbvarg_0 fcsbvarg_1 wsbc icsbvarg_1 cab fcsbvarg_1 icsbvarg_0 fcsbvarg_1 fcsbvarg_0 icsbvarg_0 cv fcsbvarg_0 cv csb csb icsbvarg_0 fcsbvarg_1 icsbvarg_0 cv csb fcsbvarg_0 fcsbvarg_1 fcsbvarg_0 cv csb icsbvarg_1 cv icsbvarg_0 cv wcel icsbvarg_0 fcsbvarg_1 wsbc icsbvarg_1 cab icsbvarg_0 fcsbvarg_1 fcsbvarg_0 icsbvarg_0 cv fcsbvarg_0 cv csb icsbvarg_0 cv icsbvarg_0 cv cvv wcel fcsbvarg_0 icsbvarg_0 cv fcsbvarg_0 cv csb icsbvarg_0 cv wceq icsbvarg_0 vex icsbvarg_0 cv cvv wcel fcsbvarg_0 icsbvarg_0 cv fcsbvarg_0 cv csb icsbvarg_1 cv fcsbvarg_0 cv wcel fcsbvarg_0 icsbvarg_0 cv wsbc icsbvarg_1 cab icsbvarg_0 cv fcsbvarg_0 icsbvarg_1 icsbvarg_0 cv fcsbvarg_0 cv df-csb icsbvarg_0 cv cvv wcel icsbvarg_1 cv fcsbvarg_0 cv wcel fcsbvarg_0 icsbvarg_0 cv wsbc icsbvarg_1 icsbvarg_0 cv fcsbvarg_0 icsbvarg_1 cv icsbvarg_0 cv cvv sbcel2gv abbi1dv syl5eq ax-mp csbeq2i fcsbvarg_0 icsbvarg_0 fcsbvarg_1 fcsbvarg_0 cv csbco icsbvarg_0 icsbvarg_1 fcsbvarg_1 icsbvarg_0 cv df-csb 3eqtr3i fcsbvarg_1 cvv wcel icsbvarg_1 cv icsbvarg_0 cv wcel icsbvarg_0 fcsbvarg_1 wsbc icsbvarg_1 fcsbvarg_1 icsbvarg_0 icsbvarg_1 cv fcsbvarg_1 cvv sbcel2gv abbi1dv syl5eq syl $.
$}
$( Substitution into a wff expressed in terms of substitution into a
       class.  (Contributed by NM, 15-Aug-2007.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v V $.
	$d x y $.
	fsbccsbg_0 $f wff ph $.
	fsbccsbg_1 $f set x $.
	fsbccsbg_2 $f set y $.
	fsbccsbg_3 $f class A $.
	fsbccsbg_4 $f class V $.
	sbccsbg $p |- ( A e. V -> ( [. A / x ]. ph <-> y e. [_ A / x ]_ { y | ph } ) ) $= fsbccsbg_0 fsbccsbg_1 fsbccsbg_3 wsbc fsbccsbg_2 cv fsbccsbg_0 fsbccsbg_2 cab wcel fsbccsbg_1 fsbccsbg_3 wsbc fsbccsbg_3 fsbccsbg_4 wcel fsbccsbg_2 cv fsbccsbg_1 fsbccsbg_3 fsbccsbg_0 fsbccsbg_2 cab csb wcel fsbccsbg_2 cv fsbccsbg_0 fsbccsbg_2 cab wcel fsbccsbg_0 fsbccsbg_1 fsbccsbg_3 fsbccsbg_0 fsbccsbg_2 abid sbcbii fsbccsbg_1 fsbccsbg_3 fsbccsbg_2 cv fsbccsbg_0 fsbccsbg_2 cab fsbccsbg_4 sbcel2g syl5bbr $.
$}
$( Substitution into a wff expressed in using substitution into a class.
     (Contributed by NM, 27-Nov-2005.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v V $.
	fsbccsb2g_0 $f wff ph $.
	fsbccsb2g_1 $f set x $.
	fsbccsb2g_2 $f class A $.
	fsbccsb2g_3 $f class V $.
	sbccsb2g $p |- ( A e. V -> ( [. A / x ]. ph <-> A e. [_ A / x ]_ { x | ph } ) ) $= fsbccsb2g_0 fsbccsb2g_1 fsbccsb2g_2 wsbc fsbccsb2g_1 cv fsbccsb2g_0 fsbccsb2g_1 cab wcel fsbccsb2g_1 fsbccsb2g_2 wsbc fsbccsb2g_2 fsbccsb2g_3 wcel fsbccsb2g_2 fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_0 fsbccsb2g_1 cab csb wcel fsbccsb2g_1 cv fsbccsb2g_0 fsbccsb2g_1 cab wcel fsbccsb2g_0 fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_0 fsbccsb2g_1 abid sbcbii fsbccsb2g_2 fsbccsb2g_3 wcel fsbccsb2g_1 cv fsbccsb2g_0 fsbccsb2g_1 cab wcel fsbccsb2g_1 fsbccsb2g_2 wsbc fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_1 cv csb fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_0 fsbccsb2g_1 cab csb wcel fsbccsb2g_2 fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_0 fsbccsb2g_1 cab csb wcel fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_1 cv fsbccsb2g_0 fsbccsb2g_1 cab fsbccsb2g_3 sbcel12g fsbccsb2g_2 fsbccsb2g_3 wcel fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_1 cv csb fsbccsb2g_2 fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_0 fsbccsb2g_1 cab csb fsbccsb2g_1 fsbccsb2g_2 fsbccsb2g_3 csbvarg eleq1d bitrd syl5bbr $.
$}
$( Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y $.
	$d y A $.
	$d y B $.
	$d y ph $.
	infcsb1d_0 $f set y $.
	fnfcsb1d_0 $f wff ph $.
	fnfcsb1d_1 $f set x $.
	fnfcsb1d_2 $f class A $.
	fnfcsb1d_3 $f class B $.
	enfcsb1d_0 $e |- ( ph -> F/_ x A ) $.
	nfcsb1d $p |- ( ph -> F/_ x [_ A / x ]_ B ) $= fnfcsb1d_0 fnfcsb1d_1 fnfcsb1d_1 fnfcsb1d_2 fnfcsb1d_3 csb infcsb1d_0 cv fnfcsb1d_3 wcel fnfcsb1d_1 fnfcsb1d_2 wsbc infcsb1d_0 cab fnfcsb1d_1 infcsb1d_0 fnfcsb1d_2 fnfcsb1d_3 df-csb fnfcsb1d_0 infcsb1d_0 cv fnfcsb1d_3 wcel fnfcsb1d_1 fnfcsb1d_2 wsbc fnfcsb1d_1 infcsb1d_0 fnfcsb1d_0 infcsb1d_0 nfv fnfcsb1d_0 infcsb1d_0 cv fnfcsb1d_3 wcel fnfcsb1d_1 fnfcsb1d_2 enfcsb1d_0 nfsbc1d nfabd nfcxfrd $.
$}
$( Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	fnfcsb1_0 $f set x $.
	fnfcsb1_1 $f class A $.
	fnfcsb1_2 $f class B $.
	enfcsb1_0 $e |- F/_ x A $.
	nfcsb1 $p |- F/_ x [_ A / x ]_ B $= fnfcsb1_0 fnfcsb1_0 fnfcsb1_1 fnfcsb1_2 csb wnfc wtru fnfcsb1_0 fnfcsb1_1 fnfcsb1_2 fnfcsb1_0 fnfcsb1_1 wnfc wtru enfcsb1_0 a1i nfcsb1d trud $.
$}
$( Bound-variable hypothesis builder for substitution into a class.
       (Contributed by NM, 17-Aug-2006.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	fnfcsb1v_0 $f set x $.
	fnfcsb1v_1 $f class A $.
	fnfcsb1v_2 $f class B $.
	nfcsb1v $p |- F/_ x [_ A / x ]_ B $= fnfcsb1v_0 fnfcsb1v_1 fnfcsb1v_2 fnfcsb1v_0 fnfcsb1v_1 nfcv nfcsb1 $.
$}
$( Deduction version of ~ nfcsb .  (Contributed by NM, 21-Nov-2005.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d x z $.
	$d y z $.
	$d z A $.
	$d z B $.
	$d z ph $.
	infcsbd_0 $f set z $.
	fnfcsbd_0 $f wff ph $.
	fnfcsbd_1 $f set x $.
	fnfcsbd_2 $f set y $.
	fnfcsbd_3 $f class A $.
	fnfcsbd_4 $f class B $.
	enfcsbd_0 $e |- F/ y ph $.
	enfcsbd_1 $e |- ( ph -> F/_ x A ) $.
	enfcsbd_2 $e |- ( ph -> F/_ x B ) $.
	nfcsbd $p |- ( ph -> F/_ x [_ A / y ]_ B ) $= fnfcsbd_0 fnfcsbd_1 fnfcsbd_2 fnfcsbd_3 fnfcsbd_4 csb infcsbd_0 cv fnfcsbd_4 wcel fnfcsbd_2 fnfcsbd_3 wsbc infcsbd_0 cab fnfcsbd_2 infcsbd_0 fnfcsbd_3 fnfcsbd_4 df-csb fnfcsbd_0 infcsbd_0 cv fnfcsbd_4 wcel fnfcsbd_2 fnfcsbd_3 wsbc fnfcsbd_1 infcsbd_0 fnfcsbd_0 infcsbd_0 nfv fnfcsbd_0 infcsbd_0 cv fnfcsbd_4 wcel fnfcsbd_1 fnfcsbd_2 fnfcsbd_3 enfcsbd_0 enfcsbd_1 fnfcsbd_0 fnfcsbd_1 infcsbd_0 fnfcsbd_4 enfcsbd_2 nfcrd nfsbcd nfabd nfcxfrd $.
$}
$( Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	fnfcsb_0 $f set x $.
	fnfcsb_1 $f set y $.
	fnfcsb_2 $f class A $.
	fnfcsb_3 $f class B $.
	enfcsb_0 $e |- F/_ x A $.
	enfcsb_1 $e |- F/_ x B $.
	nfcsb $p |- F/_ x [_ A / y ]_ B $= fnfcsb_0 fnfcsb_1 fnfcsb_2 fnfcsb_3 csb wnfc wtru fnfcsb_0 fnfcsb_1 fnfcsb_2 fnfcsb_3 fnfcsb_1 nftru fnfcsb_0 fnfcsb_2 wnfc wtru enfcsb_0 a1i fnfcsb_0 fnfcsb_3 wnfc wtru enfcsb_1 a1i nfcsbd trud $.
$}
$( Introduce an explicit substitution into an implicit substitution
       hypothesis.  See ~ sbhypf for class substitution version.  (Contributed
       by NM, 19-Dec-2008.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$d x y $.
	fcsbhypf_0 $f set x $.
	fcsbhypf_1 $f set y $.
	fcsbhypf_2 $f class A $.
	fcsbhypf_3 $f class B $.
	fcsbhypf_4 $f class C $.
	ecsbhypf_0 $e |- F/_ x A $.
	ecsbhypf_1 $e |- F/_ x C $.
	ecsbhypf_2 $e |- ( x = A -> B = C ) $.
	csbhypf $p |- ( y = A -> [_ y / x ]_ B = C ) $= fcsbhypf_0 cv fcsbhypf_2 wceq fcsbhypf_3 fcsbhypf_4 wceq wi fcsbhypf_1 cv fcsbhypf_2 wceq fcsbhypf_0 fcsbhypf_1 cv fcsbhypf_3 csb fcsbhypf_4 wceq wi fcsbhypf_0 fcsbhypf_1 fcsbhypf_1 cv fcsbhypf_2 wceq fcsbhypf_0 fcsbhypf_1 cv fcsbhypf_3 csb fcsbhypf_4 wceq fcsbhypf_0 fcsbhypf_0 fcsbhypf_1 cv fcsbhypf_2 ecsbhypf_0 nfeq2 fcsbhypf_0 fcsbhypf_0 fcsbhypf_1 cv fcsbhypf_3 csb fcsbhypf_4 fcsbhypf_0 fcsbhypf_1 cv fcsbhypf_3 nfcsb1v ecsbhypf_1 nfeq nfim fcsbhypf_0 cv fcsbhypf_1 cv wceq fcsbhypf_0 cv fcsbhypf_2 wceq fcsbhypf_1 cv fcsbhypf_2 wceq fcsbhypf_3 fcsbhypf_4 wceq fcsbhypf_0 fcsbhypf_1 cv fcsbhypf_3 csb fcsbhypf_4 wceq fcsbhypf_0 cv fcsbhypf_1 cv fcsbhypf_2 eqeq1 fcsbhypf_0 cv fcsbhypf_1 cv wceq fcsbhypf_3 fcsbhypf_0 fcsbhypf_1 cv fcsbhypf_3 csb fcsbhypf_4 fcsbhypf_0 fcsbhypf_1 cv fcsbhypf_3 csbeq1a eqeq1d imbi12d ecsbhypf_2 chvar $.
$}
$( Conversion of implicit substitution to explicit substitution into a
       class.  (Closed theorem version of ~ csbiegf .)  (Contributed by NM,
       11-Nov-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x A $.
	fcsbiebt_0 $f set x $.
	fcsbiebt_1 $f class A $.
	fcsbiebt_2 $f class B $.
	fcsbiebt_3 $f class C $.
	fcsbiebt_4 $f class V $.
	csbiebt $p |- ( ( A e. V /\ F/_ x C ) -> ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) ) $= fcsbiebt_1 fcsbiebt_4 wcel fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 wal fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq wb fcsbiebt_1 fcsbiebt_4 elex fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc wa fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 wal fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc wa fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 wal fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 fcsbiebt_1 wsbc fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_1 cvv wcel fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 wal fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 fcsbiebt_1 wsbc wi fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 fcsbiebt_1 cvv spsbc adantr fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc wa fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_0 fcsbiebt_1 cvv fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc simpl fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq wb fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc wa fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq biimt fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csbeq1a eqeq1d bitr3d adantl fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 fcsbiebt_1 cvv wcel fcsbiebt_0 nfv fcsbiebt_0 fcsbiebt_3 nfnfc1 nfan fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc wa fcsbiebt_0 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 fcsbiebt_0 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb wnfc fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc wa fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 nfcsb1v a1i fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc simpr nfeqd sbciedf sylibd fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 wal wi fcsbiebt_1 cvv wcel fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 wal fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq wa fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_0 fcsbiebt_0 fcsbiebt_3 nfnfc1 fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 fcsbiebt_0 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb wnfc fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 nfcsb1v a1i fcsbiebt_0 fcsbiebt_3 wnfc id nfeqd nfan1 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq wi fcsbiebt_0 fcsbiebt_3 wnfc fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_3 wceq fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 wceq fcsbiebt_0 cv fcsbiebt_1 wceq fcsbiebt_2 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csb fcsbiebt_3 fcsbiebt_0 fcsbiebt_1 fcsbiebt_2 csbeq1a eqeq1d biimprcd adantl alrimi ex adantl impbid sylan $.
$}
$( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by Mario Carneiro, 13-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x A $.
	fcsbiedf_0 $f wff ph $.
	fcsbiedf_1 $f set x $.
	fcsbiedf_2 $f class A $.
	fcsbiedf_3 $f class B $.
	fcsbiedf_4 $f class C $.
	fcsbiedf_5 $f class V $.
	ecsbiedf_0 $e |- F/ x ph $.
	ecsbiedf_1 $e |- ( ph -> F/_ x C ) $.
	ecsbiedf_2 $e |- ( ph -> A e. V ) $.
	ecsbiedf_3 $e |- ( ( ph /\ x = A ) -> B = C ) $.
	csbiedf $p |- ( ph -> [_ A / x ]_ B = C ) $= fcsbiedf_0 fcsbiedf_1 cv fcsbiedf_2 wceq fcsbiedf_3 fcsbiedf_4 wceq wi fcsbiedf_1 wal fcsbiedf_1 fcsbiedf_2 fcsbiedf_3 csb fcsbiedf_4 wceq fcsbiedf_0 fcsbiedf_1 cv fcsbiedf_2 wceq fcsbiedf_3 fcsbiedf_4 wceq wi fcsbiedf_1 ecsbiedf_0 fcsbiedf_0 fcsbiedf_1 cv fcsbiedf_2 wceq fcsbiedf_3 fcsbiedf_4 wceq ecsbiedf_3 ex alrimi fcsbiedf_0 fcsbiedf_2 fcsbiedf_5 wcel fcsbiedf_1 fcsbiedf_4 wnfc fcsbiedf_1 cv fcsbiedf_2 wceq fcsbiedf_3 fcsbiedf_4 wceq wi fcsbiedf_1 wal fcsbiedf_1 fcsbiedf_2 fcsbiedf_3 csb fcsbiedf_4 wceq wb ecsbiedf_2 ecsbiedf_1 fcsbiedf_1 fcsbiedf_2 fcsbiedf_3 fcsbiedf_4 fcsbiedf_5 csbiebt syl2anc mpbid $.
$}
$( Bidirectional conversion between an implicit class substitution
       hypothesis ` x = A -> B = C ` and its explicit substitution equivalent.
       (Contributed by NM, 2-Mar-2008.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	fcsbieb_0 $f set x $.
	fcsbieb_1 $f class A $.
	fcsbieb_2 $f class B $.
	fcsbieb_3 $f class C $.
	ecsbieb_0 $e |- A e. _V $.
	ecsbieb_1 $e |- F/_ x C $.
	csbieb $p |- ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) $= fcsbieb_1 cvv wcel fcsbieb_0 fcsbieb_3 wnfc fcsbieb_0 cv fcsbieb_1 wceq fcsbieb_2 fcsbieb_3 wceq wi fcsbieb_0 wal fcsbieb_0 fcsbieb_1 fcsbieb_2 csb fcsbieb_3 wceq wb ecsbieb_0 ecsbieb_1 fcsbieb_0 fcsbieb_1 fcsbieb_2 fcsbieb_3 cvv csbiebt mp2an $.
$}
$( Bidirectional conversion between an implicit class substitution
       hypothesis ` x = A -> B = C ` and its explicit substitution equivalent.
       (Contributed by NM, 24-Mar-2013.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v a $.
	$d a x A $.
	$d a B $.
	$d a C $.
	icsbiebg_0 $f set a $.
	fcsbiebg_0 $f set x $.
	fcsbiebg_1 $f class A $.
	fcsbiebg_2 $f class B $.
	fcsbiebg_3 $f class C $.
	fcsbiebg_4 $f class V $.
	ecsbiebg_0 $e |- F/_ x C $.
	csbiebg $p |- ( A e. V -> ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) ) $= fcsbiebg_0 cv icsbiebg_0 cv wceq fcsbiebg_2 fcsbiebg_3 wceq wi fcsbiebg_0 wal fcsbiebg_0 icsbiebg_0 cv fcsbiebg_2 csb fcsbiebg_3 wceq fcsbiebg_0 cv fcsbiebg_1 wceq fcsbiebg_2 fcsbiebg_3 wceq wi fcsbiebg_0 wal fcsbiebg_0 fcsbiebg_1 fcsbiebg_2 csb fcsbiebg_3 wceq icsbiebg_0 fcsbiebg_1 fcsbiebg_4 icsbiebg_0 cv fcsbiebg_1 wceq fcsbiebg_0 cv icsbiebg_0 cv wceq fcsbiebg_2 fcsbiebg_3 wceq wi fcsbiebg_0 cv fcsbiebg_1 wceq fcsbiebg_2 fcsbiebg_3 wceq wi fcsbiebg_0 icsbiebg_0 cv fcsbiebg_1 wceq fcsbiebg_0 cv icsbiebg_0 cv wceq fcsbiebg_0 cv fcsbiebg_1 wceq fcsbiebg_2 fcsbiebg_3 wceq icsbiebg_0 cv fcsbiebg_1 fcsbiebg_0 cv eqeq2 imbi1d albidv icsbiebg_0 cv fcsbiebg_1 wceq fcsbiebg_0 icsbiebg_0 cv fcsbiebg_2 csb fcsbiebg_0 fcsbiebg_1 fcsbiebg_2 csb fcsbiebg_3 fcsbiebg_0 icsbiebg_0 cv fcsbiebg_1 fcsbiebg_2 csbeq1 eqeq1d fcsbiebg_0 icsbiebg_0 cv fcsbiebg_2 fcsbiebg_3 icsbiebg_0 vex ecsbiebg_0 csbieb vtoclbg $.
$}
$( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 11-Nov-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x A $.
	$d x V $.
	fcsbiegf_0 $f set x $.
	fcsbiegf_1 $f class A $.
	fcsbiegf_2 $f class B $.
	fcsbiegf_3 $f class C $.
	fcsbiegf_4 $f class V $.
	ecsbiegf_0 $e |- ( A e. V -> F/_ x C ) $.
	ecsbiegf_1 $e |- ( x = A -> B = C ) $.
	csbiegf $p |- ( A e. V -> [_ A / x ]_ B = C ) $= fcsbiegf_1 fcsbiegf_4 wcel fcsbiegf_0 cv fcsbiegf_1 wceq fcsbiegf_2 fcsbiegf_3 wceq wi fcsbiegf_0 wal fcsbiegf_0 fcsbiegf_1 fcsbiegf_2 csb fcsbiegf_3 wceq fcsbiegf_0 cv fcsbiegf_1 wceq fcsbiegf_2 fcsbiegf_3 wceq wi fcsbiegf_0 ecsbiegf_1 ax-gen fcsbiegf_1 fcsbiegf_4 wcel fcsbiegf_0 fcsbiegf_3 wnfc fcsbiegf_0 cv fcsbiegf_1 wceq fcsbiegf_2 fcsbiegf_3 wceq wi fcsbiegf_0 wal fcsbiegf_0 fcsbiegf_1 fcsbiegf_2 csb fcsbiegf_3 wceq wb ecsbiegf_0 fcsbiegf_0 fcsbiegf_1 fcsbiegf_2 fcsbiegf_3 fcsbiegf_4 csbiebt mpdan mpbii $.
$}
$( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 26-Nov-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	fcsbief_0 $f set x $.
	fcsbief_1 $f class A $.
	fcsbief_2 $f class B $.
	fcsbief_3 $f class C $.
	ecsbief_0 $e |- A e. _V $.
	ecsbief_1 $e |- F/_ x C $.
	ecsbief_2 $e |- ( x = A -> B = C ) $.
	csbief $p |- [_ A / x ]_ B = C $= fcsbief_1 cvv wcel fcsbief_0 fcsbief_1 fcsbief_2 csb fcsbief_3 wceq ecsbief_0 fcsbief_0 fcsbief_1 fcsbief_2 fcsbief_3 cvv fcsbief_0 fcsbief_3 wnfc fcsbief_1 cvv wcel ecsbief_1 a1i ecsbief_2 csbiegf ax-mp $.
$}
$( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by Mario Carneiro, 2-Dec-2014.)  (Revised by Mario
       Carneiro, 13-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x A $.
	$d x C $.
	$d x ph $.
	fcsbied_0 $f wff ph $.
	fcsbied_1 $f set x $.
	fcsbied_2 $f class A $.
	fcsbied_3 $f class B $.
	fcsbied_4 $f class C $.
	fcsbied_5 $f class V $.
	ecsbied_0 $e |- ( ph -> A e. V ) $.
	ecsbied_1 $e |- ( ( ph /\ x = A ) -> B = C ) $.
	csbied $p |- ( ph -> [_ A / x ]_ B = C ) $= fcsbied_0 fcsbied_1 fcsbied_2 fcsbied_3 fcsbied_4 fcsbied_5 fcsbied_0 fcsbied_1 nfv fcsbied_0 fcsbied_1 fcsbied_4 nfcvd ecsbied_0 ecsbied_1 csbiedf $.
$}
$( Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$d x A $.
	$d x ph $.
	$d x D $.
	fcsbied2_0 $f wff ph $.
	fcsbied2_1 $f set x $.
	fcsbied2_2 $f class A $.
	fcsbied2_3 $f class B $.
	fcsbied2_4 $f class C $.
	fcsbied2_5 $f class D $.
	fcsbied2_6 $f class V $.
	ecsbied2_0 $e |- ( ph -> A e. V ) $.
	ecsbied2_1 $e |- ( ph -> A = B ) $.
	ecsbied2_2 $e |- ( ( ph /\ x = B ) -> C = D ) $.
	csbied2 $p |- ( ph -> [_ A / x ]_ C = D ) $= fcsbied2_0 fcsbied2_1 fcsbied2_2 fcsbied2_4 fcsbied2_5 fcsbied2_6 ecsbied2_0 fcsbied2_0 fcsbied2_1 cv fcsbied2_2 wceq fcsbied2_1 cv fcsbied2_3 wceq fcsbied2_4 fcsbied2_5 wceq fcsbied2_1 cv fcsbied2_2 wceq fcsbied2_0 fcsbied2_1 cv fcsbied2_2 fcsbied2_3 fcsbied2_1 cv fcsbied2_2 wceq id ecsbied2_1 sylan9eqr ecsbied2_2 syldan csbied $.
$}
$( Conversion of implicit substitution to explicit substitution into a
       class (closed form of ~ csbie2 ).  (Contributed by NM, 3-Sep-2007.)
       (Revised by Mario Carneiro, 13-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x y A $.
	$d x y B $.
	$d x y D $.
	fcsbie2t_0 $f set x $.
	fcsbie2t_1 $f set y $.
	fcsbie2t_2 $f class A $.
	fcsbie2t_3 $f class B $.
	fcsbie2t_4 $f class C $.
	fcsbie2t_5 $f class D $.
	ecsbie2t_0 $e |- A e. _V $.
	ecsbie2t_1 $e |- B e. _V $.
	csbie2t $p |- ( A. x A. y ( ( x = A /\ y = B ) -> C = D ) -> [_ A / x ]_ [_ B / y ]_ C = D ) $= fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 wal fcsbie2t_0 fcsbie2t_2 fcsbie2t_1 fcsbie2t_3 fcsbie2t_4 csb fcsbie2t_5 cvv fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 nfa1 fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 wal fcsbie2t_0 fcsbie2t_5 nfcvd fcsbie2t_2 cvv wcel fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 wal ecsbie2t_0 a1i fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 wal fcsbie2t_0 cv fcsbie2t_2 wceq wa fcsbie2t_1 fcsbie2t_3 fcsbie2t_4 fcsbie2t_5 cvv fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 wal fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 fcsbie2t_0 nfa2 fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 nfv nfan fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 wal fcsbie2t_0 cv fcsbie2t_2 wceq wa fcsbie2t_1 fcsbie2t_5 nfcvd fcsbie2t_3 cvv wcel fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 wal fcsbie2t_0 cv fcsbie2t_2 wceq wa ecsbie2t_1 a1i fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 wal fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq fcsbie2t_4 fcsbie2t_5 wceq fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 wal fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_0 fcsbie2t_0 cv fcsbie2t_2 wceq fcsbie2t_1 cv fcsbie2t_3 wceq wa fcsbie2t_4 fcsbie2t_5 wceq wi fcsbie2t_1 sp sps impl csbiedf csbiedf $.
$}
$( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 27-Aug-2007.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x y A $.
	$d x y B $.
	$d x y D $.
	fcsbie2_0 $f set x $.
	fcsbie2_1 $f set y $.
	fcsbie2_2 $f class A $.
	fcsbie2_3 $f class B $.
	fcsbie2_4 $f class C $.
	fcsbie2_5 $f class D $.
	ecsbie2_0 $e |- A e. _V $.
	ecsbie2_1 $e |- B e. _V $.
	ecsbie2_2 $e |- ( ( x = A /\ y = B ) -> C = D ) $.
	csbie2 $p |- [_ A / x ]_ [_ B / y ]_ C = D $= fcsbie2_0 cv fcsbie2_2 wceq fcsbie2_1 cv fcsbie2_3 wceq wa fcsbie2_4 fcsbie2_5 wceq wi fcsbie2_1 wal fcsbie2_0 wal fcsbie2_0 fcsbie2_2 fcsbie2_1 fcsbie2_3 fcsbie2_4 csb csb fcsbie2_5 wceq fcsbie2_0 cv fcsbie2_2 wceq fcsbie2_1 cv fcsbie2_3 wceq wa fcsbie2_4 fcsbie2_5 wceq wi fcsbie2_0 fcsbie2_1 ecsbie2_2 gen2 fcsbie2_0 fcsbie2_1 fcsbie2_2 fcsbie2_3 fcsbie2_4 fcsbie2_5 ecsbie2_0 ecsbie2_1 csbie2t ax-mp $.
$}
$( Conversion of implicit substitution to explicit class substitution.
       This version of ~ sbcie avoids a disjointness condition on ` x , A ` by
       substituting twice.  (Contributed by Mario Carneiro, 11-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$d x y z $.
	$d A y z $.
	$d B y z $.
	$d C x $.
	$d D y z $.
	$d V z $.
	icsbie2g_0 $f set z $.
	fcsbie2g_0 $f set x $.
	fcsbie2g_1 $f set y $.
	fcsbie2g_2 $f class A $.
	fcsbie2g_3 $f class B $.
	fcsbie2g_4 $f class C $.
	fcsbie2g_5 $f class D $.
	fcsbie2g_6 $f class V $.
	ecsbie2g_0 $e |- ( x = y -> B = C ) $.
	ecsbie2g_1 $e |- ( y = A -> C = D ) $.
	csbie2g $p |- ( A e. V -> [_ A / x ]_ B = D ) $= fcsbie2g_2 fcsbie2g_6 wcel fcsbie2g_0 fcsbie2g_2 fcsbie2g_3 csb icsbie2g_0 cv fcsbie2g_3 wcel fcsbie2g_0 fcsbie2g_2 wsbc icsbie2g_0 cab fcsbie2g_5 fcsbie2g_0 icsbie2g_0 fcsbie2g_2 fcsbie2g_3 df-csb fcsbie2g_2 fcsbie2g_6 wcel icsbie2g_0 cv fcsbie2g_3 wcel fcsbie2g_0 fcsbie2g_2 wsbc icsbie2g_0 fcsbie2g_5 icsbie2g_0 cv fcsbie2g_3 wcel icsbie2g_0 cv fcsbie2g_4 wcel icsbie2g_0 cv fcsbie2g_5 wcel fcsbie2g_0 fcsbie2g_1 fcsbie2g_2 fcsbie2g_6 fcsbie2g_0 cv fcsbie2g_1 cv wceq fcsbie2g_3 fcsbie2g_4 icsbie2g_0 cv ecsbie2g_0 eleq2d fcsbie2g_1 cv fcsbie2g_2 wceq fcsbie2g_4 fcsbie2g_5 icsbie2g_0 cv ecsbie2g_1 eleq2d sbcie2g abbi1dv syl5eq $.
$}
$( Nest the composition of two substitutions.  (Contributed by Mario
       Carneiro, 11-Nov-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v V $.
	$d x z $.
	$d y z $.
	$d z A $.
	$d z B $.
	$d z ph $.
	isbcnestgf_0 $f set z $.
	fsbcnestgf_0 $f wff ph $.
	fsbcnestgf_1 $f set x $.
	fsbcnestgf_2 $f set y $.
	fsbcnestgf_3 $f class A $.
	fsbcnestgf_4 $f class B $.
	fsbcnestgf_5 $f class V $.
	sbcnestgf $p |- ( ( A e. V /\ A. y F/ x ph ) -> ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. ph ) ) $= fsbcnestgf_3 fsbcnestgf_5 wcel fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_1 fsbcnestgf_3 wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 fsbcnestgf_3 fsbcnestgf_4 csb wsbc wb fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_1 isbcnestgf_0 cv wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wsbc wb wi fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_1 fsbcnestgf_3 wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 fsbcnestgf_3 fsbcnestgf_4 csb wsbc wb wi isbcnestgf_0 fsbcnestgf_3 fsbcnestgf_5 isbcnestgf_0 cv fsbcnestgf_3 wceq fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_1 isbcnestgf_0 cv wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wsbc wb fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_1 fsbcnestgf_3 wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 fsbcnestgf_3 fsbcnestgf_4 csb wsbc wb fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal isbcnestgf_0 cv fsbcnestgf_3 wceq fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_1 isbcnestgf_0 cv wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_1 fsbcnestgf_3 wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 fsbcnestgf_3 fsbcnestgf_4 csb wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_3 dfsbcq isbcnestgf_0 cv fsbcnestgf_3 wceq fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb fsbcnestgf_1 fsbcnestgf_3 fsbcnestgf_4 csb wceq fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 fsbcnestgf_3 fsbcnestgf_4 csb wsbc wb fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_3 fsbcnestgf_4 csbeq1 fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb fsbcnestgf_1 fsbcnestgf_3 fsbcnestgf_4 csb dfsbcq syl bibi12d imbi2d fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wsbc fsbcnestgf_1 isbcnestgf_0 cv cvv isbcnestgf_0 cv cvv wcel fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal isbcnestgf_0 vex a1i fsbcnestgf_1 cv isbcnestgf_0 cv wceq fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wsbc wb fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal fsbcnestgf_1 cv isbcnestgf_0 cv wceq fsbcnestgf_4 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wceq fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 wsbc fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wsbc wb fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csbeq1a fsbcnestgf_0 fsbcnestgf_2 fsbcnestgf_4 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb dfsbcq syl adantl fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_1 fsbcnestgf_2 fsbcnestgf_0 fsbcnestgf_1 nfnf1 nfal fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal fsbcnestgf_0 fsbcnestgf_1 fsbcnestgf_2 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 nfa1 fsbcnestgf_1 fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 csb wnfc fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 wal fsbcnestgf_1 isbcnestgf_0 cv fsbcnestgf_4 nfcsb1v a1i fsbcnestgf_0 fsbcnestgf_1 wnf fsbcnestgf_2 sp nfsbcd sbciedf vtoclg imp $.
$}
$( Nest the composition of two substitutions.  (Contributed by NM,
       23-Nov-2005.)  (Proof shortened by Mario Carneiro, 10-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x z $.
	$d y z $.
	$d z A $.
	$d z B $.
	$d z C $.
	icsbnestgf_0 $f set z $.
	fcsbnestgf_0 $f set x $.
	fcsbnestgf_1 $f set y $.
	fcsbnestgf_2 $f class A $.
	fcsbnestgf_3 $f class B $.
	fcsbnestgf_4 $f class C $.
	fcsbnestgf_5 $f class V $.
	csbnestgf $p |- ( ( A e. V /\ A. y F/_ x C ) -> [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $= fcsbnestgf_2 fcsbnestgf_5 wcel fcsbnestgf_0 fcsbnestgf_4 wnfc fcsbnestgf_1 wal wa icsbnestgf_0 cv fcsbnestgf_1 fcsbnestgf_3 fcsbnestgf_4 csb wcel fcsbnestgf_0 fcsbnestgf_2 wsbc icsbnestgf_0 cab icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_0 fcsbnestgf_2 fcsbnestgf_3 csb wsbc icsbnestgf_0 cab fcsbnestgf_0 fcsbnestgf_2 fcsbnestgf_1 fcsbnestgf_3 fcsbnestgf_4 csb csb fcsbnestgf_1 fcsbnestgf_0 fcsbnestgf_2 fcsbnestgf_3 csb fcsbnestgf_4 csb fcsbnestgf_2 fcsbnestgf_5 wcel fcsbnestgf_2 cvv wcel fcsbnestgf_0 fcsbnestgf_4 wnfc fcsbnestgf_1 wal icsbnestgf_0 cv fcsbnestgf_1 fcsbnestgf_3 fcsbnestgf_4 csb wcel fcsbnestgf_0 fcsbnestgf_2 wsbc icsbnestgf_0 cab icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_0 fcsbnestgf_2 fcsbnestgf_3 csb wsbc icsbnestgf_0 cab wceq fcsbnestgf_2 fcsbnestgf_5 elex fcsbnestgf_2 cvv wcel fcsbnestgf_0 fcsbnestgf_4 wnfc fcsbnestgf_1 wal wa icsbnestgf_0 cv fcsbnestgf_1 fcsbnestgf_3 fcsbnestgf_4 csb wcel fcsbnestgf_0 fcsbnestgf_2 wsbc icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_0 fcsbnestgf_2 fcsbnestgf_3 csb wsbc icsbnestgf_0 icsbnestgf_0 cv fcsbnestgf_1 fcsbnestgf_3 fcsbnestgf_4 csb wcel fcsbnestgf_0 fcsbnestgf_2 wsbc icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_3 wsbc fcsbnestgf_0 fcsbnestgf_2 wsbc fcsbnestgf_2 cvv wcel fcsbnestgf_0 fcsbnestgf_4 wnfc fcsbnestgf_1 wal wa icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_0 fcsbnestgf_2 fcsbnestgf_3 csb wsbc icsbnestgf_0 cv fcsbnestgf_1 fcsbnestgf_3 fcsbnestgf_4 csb wcel icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_3 wsbc fcsbnestgf_0 fcsbnestgf_2 icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_3 wsbc icsbnestgf_0 fcsbnestgf_1 fcsbnestgf_3 fcsbnestgf_4 csb fcsbnestgf_1 icsbnestgf_0 fcsbnestgf_3 fcsbnestgf_4 df-csb abeq2i sbcbii fcsbnestgf_0 fcsbnestgf_4 wnfc fcsbnestgf_1 wal fcsbnestgf_2 cvv wcel icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_0 wnf fcsbnestgf_1 wal icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_3 wsbc fcsbnestgf_0 fcsbnestgf_2 wsbc icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_1 fcsbnestgf_0 fcsbnestgf_2 fcsbnestgf_3 csb wsbc wb fcsbnestgf_0 fcsbnestgf_4 wnfc icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_0 wnf fcsbnestgf_1 fcsbnestgf_0 icsbnestgf_0 fcsbnestgf_4 nfcr alimi icsbnestgf_0 cv fcsbnestgf_4 wcel fcsbnestgf_0 fcsbnestgf_1 fcsbnestgf_2 fcsbnestgf_3 cvv sbcnestgf sylan2 syl5bb abbidv sylan fcsbnestgf_0 icsbnestgf_0 fcsbnestgf_2 fcsbnestgf_1 fcsbnestgf_3 fcsbnestgf_4 csb df-csb fcsbnestgf_1 icsbnestgf_0 fcsbnestgf_0 fcsbnestgf_2 fcsbnestgf_3 csb fcsbnestgf_4 df-csb 3eqtr4g $.
$}
$( Nest the composition of two substitutions.  (Contributed by NM,
       27-Nov-2005.)  (Proof shortened by Mario Carneiro, 11-Nov-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v V $.
	$d x ph $.
	fsbcnestg_0 $f wff ph $.
	fsbcnestg_1 $f set x $.
	fsbcnestg_2 $f set y $.
	fsbcnestg_3 $f class A $.
	fsbcnestg_4 $f class B $.
	fsbcnestg_5 $f class V $.
	sbcnestg $p |- ( A e. V -> ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. ph ) ) $= fsbcnestg_3 fsbcnestg_5 wcel fsbcnestg_0 fsbcnestg_1 wnf fsbcnestg_2 wal fsbcnestg_0 fsbcnestg_2 fsbcnestg_4 wsbc fsbcnestg_1 fsbcnestg_3 wsbc fsbcnestg_0 fsbcnestg_2 fsbcnestg_1 fsbcnestg_3 fsbcnestg_4 csb wsbc wb fsbcnestg_0 fsbcnestg_1 wnf fsbcnestg_2 fsbcnestg_0 fsbcnestg_1 nfv ax-gen fsbcnestg_0 fsbcnestg_1 fsbcnestg_2 fsbcnestg_3 fsbcnestg_4 fsbcnestg_5 sbcnestgf mpan2 $.
$}
$( Nest the composition of two substitutions.  (Contributed by NM,
       23-Nov-2005.)  (Proof shortened by Mario Carneiro, 10-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x C $.
	fcsbnestg_0 $f set x $.
	fcsbnestg_1 $f set y $.
	fcsbnestg_2 $f class A $.
	fcsbnestg_3 $f class B $.
	fcsbnestg_4 $f class C $.
	fcsbnestg_5 $f class V $.
	csbnestg $p |- ( A e. V -> [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $= fcsbnestg_2 fcsbnestg_5 wcel fcsbnestg_0 fcsbnestg_4 wnfc fcsbnestg_1 wal fcsbnestg_0 fcsbnestg_2 fcsbnestg_1 fcsbnestg_3 fcsbnestg_4 csb csb fcsbnestg_1 fcsbnestg_0 fcsbnestg_2 fcsbnestg_3 csb fcsbnestg_4 csb wceq fcsbnestg_0 fcsbnestg_4 wnfc fcsbnestg_1 fcsbnestg_0 fcsbnestg_4 nfcv ax-gen fcsbnestg_0 fcsbnestg_1 fcsbnestg_2 fcsbnestg_3 fcsbnestg_4 fcsbnestg_5 csbnestgf mpan2 $.
$}
$( Nest the composition of two substitutions.  (New usage is discouraged.)
       (Contributed by NM, 23-Nov-2005.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	$d x C $.
	fcsbnestgOLD_0 $f set x $.
	fcsbnestgOLD_1 $f set y $.
	fcsbnestgOLD_2 $f class A $.
	fcsbnestgOLD_3 $f class B $.
	fcsbnestgOLD_4 $f class C $.
	fcsbnestgOLD_5 $f class V $.
	fcsbnestgOLD_6 $f class W $.
	csbnestgOLD $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $= fcsbnestgOLD_2 fcsbnestgOLD_5 wcel fcsbnestgOLD_0 fcsbnestgOLD_2 fcsbnestgOLD_1 fcsbnestgOLD_3 fcsbnestgOLD_4 csb csb fcsbnestgOLD_1 fcsbnestgOLD_0 fcsbnestgOLD_2 fcsbnestgOLD_3 csb fcsbnestgOLD_4 csb wceq fcsbnestgOLD_3 fcsbnestgOLD_6 wcel fcsbnestgOLD_0 wal fcsbnestgOLD_0 fcsbnestgOLD_1 fcsbnestgOLD_2 fcsbnestgOLD_3 fcsbnestgOLD_4 fcsbnestgOLD_5 csbnestg adantr $.
$}
$( Nest the composition of two substitutions.  (Contributed by NM,
       23-May-2006.)  (Proof shortened by Mario Carneiro, 11-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x y $.
	$d y C $.
	icsbnest1g_0 $f set y $.
	fcsbnest1g_0 $f set x $.
	fcsbnest1g_1 $f class A $.
	fcsbnest1g_2 $f class B $.
	fcsbnest1g_3 $f class C $.
	fcsbnest1g_4 $f class V $.
	csbnest1g $p |- ( A e. V -> [_ A / x ]_ [_ B / x ]_ C = [_ [_ A / x ]_ B / x ]_ C ) $= fcsbnest1g_1 fcsbnest1g_4 wcel fcsbnest1g_0 fcsbnest1g_1 icsbnest1g_0 fcsbnest1g_2 fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 csb csb csb icsbnest1g_0 fcsbnest1g_0 fcsbnest1g_1 fcsbnest1g_2 csb fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 csb csb fcsbnest1g_0 fcsbnest1g_1 fcsbnest1g_0 fcsbnest1g_2 fcsbnest1g_3 csb csb fcsbnest1g_0 fcsbnest1g_0 fcsbnest1g_1 fcsbnest1g_2 csb fcsbnest1g_3 csb fcsbnest1g_1 fcsbnest1g_4 wcel fcsbnest1g_0 fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 csb wnfc icsbnest1g_0 wal fcsbnest1g_0 fcsbnest1g_1 icsbnest1g_0 fcsbnest1g_2 fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 csb csb csb icsbnest1g_0 fcsbnest1g_0 fcsbnest1g_1 fcsbnest1g_2 csb fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 csb csb wceq fcsbnest1g_0 fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 csb wnfc icsbnest1g_0 fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 nfcsb1v ax-gen fcsbnest1g_0 icsbnest1g_0 fcsbnest1g_1 fcsbnest1g_2 fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 csb fcsbnest1g_4 csbnestgf mpan2 fcsbnest1g_0 fcsbnest1g_1 icsbnest1g_0 fcsbnest1g_2 fcsbnest1g_0 icsbnest1g_0 cv fcsbnest1g_3 csb csb fcsbnest1g_0 fcsbnest1g_2 fcsbnest1g_3 csb fcsbnest1g_0 icsbnest1g_0 fcsbnest1g_2 fcsbnest1g_3 csbco csbeq2i fcsbnest1g_0 icsbnest1g_0 fcsbnest1g_0 fcsbnest1g_1 fcsbnest1g_2 csb fcsbnest1g_3 csbco 3eqtr3g $.
$}
$( Nest the composition of two substitutions.  Obsolete as of 11-Nov-2016.
       (Contributed by NM, 23-May-2006.)  (New usage is discouraged.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	$d x A $.
	fcsbnest1gOLD_0 $f set x $.
	fcsbnest1gOLD_1 $f class A $.
	fcsbnest1gOLD_2 $f class B $.
	fcsbnest1gOLD_3 $f class C $.
	fcsbnest1gOLD_4 $f class V $.
	fcsbnest1gOLD_5 $f class W $.
	csbnest1gOLD $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ [_ B / x ]_ C = [_ [_ A / x ]_ B / x ]_ C ) $= fcsbnest1gOLD_1 fcsbnest1gOLD_4 wcel fcsbnest1gOLD_0 fcsbnest1gOLD_1 fcsbnest1gOLD_0 fcsbnest1gOLD_2 fcsbnest1gOLD_3 csb csb fcsbnest1gOLD_0 fcsbnest1gOLD_0 fcsbnest1gOLD_1 fcsbnest1gOLD_2 csb fcsbnest1gOLD_3 csb wceq fcsbnest1gOLD_2 fcsbnest1gOLD_5 wcel fcsbnest1gOLD_0 wal fcsbnest1gOLD_0 fcsbnest1gOLD_1 fcsbnest1gOLD_2 fcsbnest1gOLD_3 fcsbnest1gOLD_4 csbnest1g adantr $.
$}
$( Idempotent law for class substitutions.  (Contributed by NM,
       1-Mar-2008.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v V $.
	$d x A $.
	fcsbidmg_0 $f set x $.
	fcsbidmg_1 $f class A $.
	fcsbidmg_2 $f class B $.
	fcsbidmg_3 $f class V $.
	csbidmg $p |- ( A e. V -> [_ A / x ]_ [_ A / x ]_ B = [_ A / x ]_ B ) $= fcsbidmg_1 fcsbidmg_3 wcel fcsbidmg_1 cvv wcel fcsbidmg_0 fcsbidmg_1 fcsbidmg_0 fcsbidmg_1 fcsbidmg_2 csb csb fcsbidmg_0 fcsbidmg_1 fcsbidmg_2 csb wceq fcsbidmg_1 fcsbidmg_3 elex fcsbidmg_1 cvv wcel fcsbidmg_0 fcsbidmg_1 fcsbidmg_0 fcsbidmg_1 fcsbidmg_2 csb csb fcsbidmg_0 fcsbidmg_0 fcsbidmg_1 fcsbidmg_1 csb fcsbidmg_2 csb fcsbidmg_0 fcsbidmg_1 fcsbidmg_2 csb fcsbidmg_0 fcsbidmg_1 fcsbidmg_1 fcsbidmg_2 cvv csbnest1g fcsbidmg_1 cvv wcel fcsbidmg_0 fcsbidmg_0 fcsbidmg_1 fcsbidmg_1 csb fcsbidmg_1 fcsbidmg_2 fcsbidmg_0 fcsbidmg_1 fcsbidmg_1 cvv csbconstg csbeq1d eqtrd syl $.
$}
$( Composition of two substitutions.  (Contributed by NM, 27-Nov-2005.)
       (Revised by Mario Carneiro, 11-Nov-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$d x A $.
	$d x ph $.
	$d x C $.
	fsbcco3g_0 $f wff ph $.
	fsbcco3g_1 $f set x $.
	fsbcco3g_2 $f set y $.
	fsbcco3g_3 $f class A $.
	fsbcco3g_4 $f class B $.
	fsbcco3g_5 $f class C $.
	fsbcco3g_6 $f class V $.
	esbcco3g_0 $e |- ( x = A -> B = C ) $.
	sbcco3g $p |- ( A e. V -> ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ph ) ) $= fsbcco3g_3 fsbcco3g_6 wcel fsbcco3g_0 fsbcco3g_2 fsbcco3g_4 wsbc fsbcco3g_1 fsbcco3g_3 wsbc fsbcco3g_0 fsbcco3g_2 fsbcco3g_1 fsbcco3g_3 fsbcco3g_4 csb wsbc fsbcco3g_0 fsbcco3g_2 fsbcco3g_5 wsbc fsbcco3g_0 fsbcco3g_1 fsbcco3g_2 fsbcco3g_3 fsbcco3g_4 fsbcco3g_6 sbcnestg fsbcco3g_3 fsbcco3g_6 wcel fsbcco3g_3 cvv wcel fsbcco3g_1 fsbcco3g_3 fsbcco3g_4 csb fsbcco3g_5 wceq fsbcco3g_0 fsbcco3g_2 fsbcco3g_1 fsbcco3g_3 fsbcco3g_4 csb wsbc fsbcco3g_0 fsbcco3g_2 fsbcco3g_5 wsbc wb fsbcco3g_3 fsbcco3g_6 elex fsbcco3g_1 fsbcco3g_3 fsbcco3g_4 fsbcco3g_5 cvv fsbcco3g_3 cvv wcel fsbcco3g_1 fsbcco3g_5 nfcvd esbcco3g_0 csbiegf fsbcco3g_0 fsbcco3g_2 fsbcco3g_1 fsbcco3g_3 fsbcco3g_4 csb fsbcco3g_5 dfsbcq 3syl bitrd $.
$}
$( Composition of two substitutions.  (Contributed by NM, 27-Nov-2005.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v V $.
	$v W $.
	$d x A $.
	$d x ph $.
	$d x C $.
	fsbcco3gOLD_0 $f wff ph $.
	fsbcco3gOLD_1 $f set x $.
	fsbcco3gOLD_2 $f set y $.
	fsbcco3gOLD_3 $f class A $.
	fsbcco3gOLD_4 $f class B $.
	fsbcco3gOLD_5 $f class C $.
	fsbcco3gOLD_6 $f class V $.
	fsbcco3gOLD_7 $f class W $.
	esbcco3gOLD_0 $e |- ( x = A -> B = C ) $.
	sbcco3gOLD $p |- ( ( A e. V /\ A. x B e. W ) -> ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ph ) ) $= fsbcco3gOLD_3 fsbcco3gOLD_6 wcel fsbcco3gOLD_0 fsbcco3gOLD_2 fsbcco3gOLD_4 wsbc fsbcco3gOLD_1 fsbcco3gOLD_3 wsbc fsbcco3gOLD_0 fsbcco3gOLD_2 fsbcco3gOLD_5 wsbc wb fsbcco3gOLD_4 fsbcco3gOLD_7 wcel fsbcco3gOLD_1 wal fsbcco3gOLD_0 fsbcco3gOLD_1 fsbcco3gOLD_2 fsbcco3gOLD_3 fsbcco3gOLD_4 fsbcco3gOLD_5 fsbcco3gOLD_6 esbcco3gOLD_0 sbcco3g adantr $.
$}
$( Composition of two class substitutions.  (Contributed by NM,
       27-Nov-2005.)  (Revised by Mario Carneiro, 11-Nov-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$d x A $.
	$d x C $.
	$d x D $.
	fcsbco3g_0 $f set x $.
	fcsbco3g_1 $f set y $.
	fcsbco3g_2 $f class A $.
	fcsbco3g_3 $f class B $.
	fcsbco3g_4 $f class C $.
	fcsbco3g_5 $f class D $.
	fcsbco3g_6 $f class V $.
	ecsbco3g_0 $e |- ( x = A -> B = C ) $.
	csbco3g $p |- ( A e. V -> [_ A / x ]_ [_ B / y ]_ D = [_ C / y ]_ D ) $= fcsbco3g_2 fcsbco3g_6 wcel fcsbco3g_0 fcsbco3g_2 fcsbco3g_1 fcsbco3g_3 fcsbco3g_5 csb csb fcsbco3g_1 fcsbco3g_0 fcsbco3g_2 fcsbco3g_3 csb fcsbco3g_5 csb fcsbco3g_1 fcsbco3g_4 fcsbco3g_5 csb fcsbco3g_0 fcsbco3g_1 fcsbco3g_2 fcsbco3g_3 fcsbco3g_5 fcsbco3g_6 csbnestg fcsbco3g_2 fcsbco3g_6 wcel fcsbco3g_1 fcsbco3g_0 fcsbco3g_2 fcsbco3g_3 csb fcsbco3g_4 fcsbco3g_5 fcsbco3g_2 fcsbco3g_6 wcel fcsbco3g_2 cvv wcel fcsbco3g_0 fcsbco3g_2 fcsbco3g_3 csb fcsbco3g_4 wceq fcsbco3g_2 fcsbco3g_6 elex fcsbco3g_0 fcsbco3g_2 fcsbco3g_3 fcsbco3g_4 cvv fcsbco3g_2 cvv wcel fcsbco3g_0 fcsbco3g_4 nfcvd ecsbco3g_0 csbiegf syl csbeq1d eqtrd $.
$}
$( Composition of two class substitutions.  Obsolete as of 11-Nov-2016.
       (Contributed by NM, 27-Nov-2005.)  (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v V $.
	$v W $.
	$d x A $.
	$d x C $.
	$d x D $.
	$d x y $.
	fcsbco3gOLD_0 $f set x $.
	fcsbco3gOLD_1 $f set y $.
	fcsbco3gOLD_2 $f class A $.
	fcsbco3gOLD_3 $f class B $.
	fcsbco3gOLD_4 $f class C $.
	fcsbco3gOLD_5 $f class D $.
	fcsbco3gOLD_6 $f class V $.
	fcsbco3gOLD_7 $f class W $.
	ecsbco3gOLD_0 $e |- ( x = A -> B = D ) $.
	csbco3gOLD $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ [_ B / y ]_ C = [_ D / y ]_ C ) $= fcsbco3gOLD_2 fcsbco3gOLD_6 wcel fcsbco3gOLD_0 fcsbco3gOLD_2 fcsbco3gOLD_1 fcsbco3gOLD_3 fcsbco3gOLD_4 csb csb fcsbco3gOLD_1 fcsbco3gOLD_5 fcsbco3gOLD_4 csb wceq fcsbco3gOLD_3 fcsbco3gOLD_7 wcel fcsbco3gOLD_0 wal fcsbco3gOLD_0 fcsbco3gOLD_1 fcsbco3gOLD_2 fcsbco3gOLD_3 fcsbco3gOLD_5 fcsbco3gOLD_4 fcsbco3gOLD_6 ecsbco3gOLD_0 csbco3g adantr $.
$}
$( Special case related to ~ rspsbc .  (Contributed by NM, 10-Dec-2005.)
       (Proof shortened by Eric Schmidt, 17-Jan-2007.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x B $.
	$d x D $.
	frspcsbela_0 $f set x $.
	frspcsbela_1 $f class A $.
	frspcsbela_2 $f class B $.
	frspcsbela_3 $f class C $.
	frspcsbela_4 $f class D $.
	rspcsbela $p |- ( ( A e. B /\ A. x e. B C e. D ) -> [_ A / x ]_ C e. D ) $= frspcsbela_1 frspcsbela_2 wcel frspcsbela_3 frspcsbela_4 wcel frspcsbela_0 frspcsbela_2 wral frspcsbela_0 frspcsbela_1 frspcsbela_3 csb frspcsbela_4 wcel frspcsbela_1 frspcsbela_2 wcel frspcsbela_3 frspcsbela_4 wcel frspcsbela_0 frspcsbela_2 wral frspcsbela_3 frspcsbela_4 wcel frspcsbela_0 frspcsbela_1 wsbc frspcsbela_0 frspcsbela_1 frspcsbela_3 csb frspcsbela_4 wcel frspcsbela_3 frspcsbela_4 wcel frspcsbela_0 frspcsbela_1 frspcsbela_2 rspsbc frspcsbela_0 frspcsbela_1 frspcsbela_3 frspcsbela_4 frspcsbela_2 sbcel1g sylibd imp $.
$}
$( Two ways of expressing " ` x ` is (effectively) not free in ` A ` ."
       (Contributed by Mario Carneiro, 14-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$v A $.
	$d w x y z $.
	$d w y z A $.
	isbnfc2_0 $f set w $.
	fsbnfc2_0 $f set x $.
	fsbnfc2_1 $f set y $.
	fsbnfc2_2 $f set z $.
	fsbnfc2_3 $f class A $.
	sbnfc2 $p |- ( F/_ x A <-> A. y A. z [_ y / x ]_ A = [_ z / x ]_ A ) $= fsbnfc2_0 fsbnfc2_3 wnfc fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wceq fsbnfc2_2 wal fsbnfc2_1 wal fsbnfc2_0 fsbnfc2_3 wnfc fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wceq fsbnfc2_1 fsbnfc2_2 fsbnfc2_0 fsbnfc2_3 wnfc fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_3 fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb fsbnfc2_1 cv cvv wcel fsbnfc2_0 fsbnfc2_3 wnfc fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_3 wceq fsbnfc2_1 vex fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 cvv csbtt mpan fsbnfc2_2 cv cvv wcel fsbnfc2_0 fsbnfc2_3 wnfc fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb fsbnfc2_3 wceq fsbnfc2_2 vex fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 cvv csbtt mpan eqtr4d alrimivv fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wceq fsbnfc2_2 wal fsbnfc2_1 wal fsbnfc2_0 isbnfc2_0 fsbnfc2_3 fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wceq fsbnfc2_2 wal fsbnfc2_1 wal isbnfc2_0 nfv fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wceq fsbnfc2_2 wal fsbnfc2_1 wal isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_1 wsb isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_2 wsb wb fsbnfc2_2 wal fsbnfc2_1 wal isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 wnf fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wceq isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_1 wsb isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_2 wsb wb fsbnfc2_1 fsbnfc2_2 fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wceq isbnfc2_0 cv fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb wcel isbnfc2_0 cv fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wcel isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_1 wsb isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_2 wsb fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb isbnfc2_0 cv eleq2 isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_1 wsb isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_1 cv wsbc isbnfc2_0 cv fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb wcel isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_1 sbsbc fsbnfc2_1 cv cvv wcel isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_1 cv wsbc isbnfc2_0 cv fsbnfc2_0 fsbnfc2_1 cv fsbnfc2_3 csb wcel wb fsbnfc2_1 vex fsbnfc2_0 fsbnfc2_1 cv isbnfc2_0 cv fsbnfc2_3 cvv sbcel2g ax-mp bitri isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_2 wsb isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_2 cv wsbc isbnfc2_0 cv fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wcel isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_2 sbsbc fsbnfc2_2 cv cvv wcel isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_2 cv wsbc isbnfc2_0 cv fsbnfc2_0 fsbnfc2_2 cv fsbnfc2_3 csb wcel wb fsbnfc2_2 vex fsbnfc2_0 fsbnfc2_2 cv isbnfc2_0 cv fsbnfc2_3 cvv sbcel2g ax-mp bitri 3bitr4g 2alimi isbnfc2_0 cv fsbnfc2_3 wcel fsbnfc2_0 fsbnfc2_1 fsbnfc2_2 sbnf2 sylibr nfcd impbii $.
$}
$( Move substitution into a class abstraction.  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v V $.
	$d y z A $.
	$d z ph $.
	$d x y z $.
	$d V z $.
	icsbabg_0 $f set z $.
	fcsbabg_0 $f wff ph $.
	fcsbabg_1 $f set x $.
	fcsbabg_2 $f set y $.
	fcsbabg_3 $f class A $.
	fcsbabg_4 $f class V $.
	csbabg $p |- ( A e. V -> [_ A / x ]_ { y | ph } = { y | [. A / x ]. ph } ) $= fcsbabg_3 fcsbabg_4 wcel icsbabg_0 fcsbabg_1 fcsbabg_3 fcsbabg_0 fcsbabg_2 cab csb fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc fcsbabg_2 cab icsbabg_0 cv fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc fcsbabg_2 cab wcel icsbabg_0 cv fcsbabg_0 fcsbabg_2 cab wcel fcsbabg_1 fcsbabg_3 wsbc fcsbabg_3 fcsbabg_4 wcel icsbabg_0 cv fcsbabg_1 fcsbabg_3 fcsbabg_0 fcsbabg_2 cab csb wcel fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc fcsbabg_2 icsbabg_0 cv wsbc fcsbabg_0 fcsbabg_2 icsbabg_0 cv wsbc fcsbabg_1 fcsbabg_3 wsbc icsbabg_0 cv fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc fcsbabg_2 cab wcel icsbabg_0 cv fcsbabg_0 fcsbabg_2 cab wcel fcsbabg_1 fcsbabg_3 wsbc fcsbabg_0 fcsbabg_2 fcsbabg_1 icsbabg_0 cv fcsbabg_3 sbccom icsbabg_0 cv fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc fcsbabg_2 cab wcel fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc fcsbabg_2 icsbabg_0 wsb fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc fcsbabg_2 icsbabg_0 cv wsbc fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc icsbabg_0 fcsbabg_2 df-clab fcsbabg_0 fcsbabg_1 fcsbabg_3 wsbc fcsbabg_2 icsbabg_0 sbsbc bitri icsbabg_0 cv fcsbabg_0 fcsbabg_2 cab wcel fcsbabg_0 fcsbabg_2 icsbabg_0 cv wsbc fcsbabg_1 fcsbabg_3 icsbabg_0 cv fcsbabg_0 fcsbabg_2 cab wcel fcsbabg_0 fcsbabg_2 icsbabg_0 wsb fcsbabg_0 fcsbabg_2 icsbabg_0 cv wsbc fcsbabg_0 icsbabg_0 fcsbabg_2 df-clab fcsbabg_0 fcsbabg_2 icsbabg_0 sbsbc bitri sbcbii 3bitr4i fcsbabg_1 fcsbabg_3 icsbabg_0 cv fcsbabg_0 fcsbabg_2 cab fcsbabg_4 sbcel2g syl5rbb eqrdv $.
$}
$( A more general version of ~ cbvralf that doesn't require ` A ` and ` B `
       to be distinct from ` x ` or ` y ` .  Changes bound variables using
       implicit substitution.  (Contributed by Andrew Salmon, 13-Jul-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v v $.
	$v A $.
	$v B $.
	$d x v z $.
	$d y v z $.
	$d A v z $.
	$d B v z $.
	$d ph v z $.
	$d ps v z $.
	icbvralcsf_0 $f set z $.
	icbvralcsf_1 $f set v $.
	fcbvralcsf_0 $f wff ph $.
	fcbvralcsf_1 $f wff ps $.
	fcbvralcsf_2 $f set x $.
	fcbvralcsf_3 $f set y $.
	fcbvralcsf_4 $f class A $.
	fcbvralcsf_5 $f class B $.
	ecbvralcsf_0 $e |- F/_ y A $.
	ecbvralcsf_1 $e |- F/_ x B $.
	ecbvralcsf_2 $e |- F/ y ph $.
	ecbvralcsf_3 $e |- F/ x ps $.
	ecbvralcsf_4 $e |- ( x = y -> A = B ) $.
	ecbvralcsf_5 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvralcsf $p |- ( A. x e. A ph <-> A. y e. B ps ) $= fcbvralcsf_2 cv fcbvralcsf_4 wcel fcbvralcsf_0 wi fcbvralcsf_2 wal fcbvralcsf_3 cv fcbvralcsf_5 wcel fcbvralcsf_1 wi fcbvralcsf_3 wal fcbvralcsf_0 fcbvralcsf_2 fcbvralcsf_4 wral fcbvralcsf_1 fcbvralcsf_3 fcbvralcsf_5 wral fcbvralcsf_2 cv fcbvralcsf_4 wcel fcbvralcsf_0 wi fcbvralcsf_2 wal icbvralcsf_0 cv fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb wcel fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv wsbc wi icbvralcsf_0 wal fcbvralcsf_3 cv fcbvralcsf_5 wcel fcbvralcsf_1 wi fcbvralcsf_3 wal fcbvralcsf_2 cv fcbvralcsf_4 wcel fcbvralcsf_0 wi icbvralcsf_0 cv fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb wcel fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv wsbc wi fcbvralcsf_2 icbvralcsf_0 fcbvralcsf_2 cv fcbvralcsf_4 wcel fcbvralcsf_0 wi icbvralcsf_0 nfv icbvralcsf_0 cv fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb wcel fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv wsbc fcbvralcsf_2 fcbvralcsf_2 icbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 nfcsb1v nfcri fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv nfsbc1v nfim fcbvralcsf_2 cv icbvralcsf_0 cv wceq fcbvralcsf_2 cv fcbvralcsf_4 wcel icbvralcsf_0 cv fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb wcel fcbvralcsf_0 fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv wsbc fcbvralcsf_2 cv icbvralcsf_0 cv wceq fcbvralcsf_2 cv icbvralcsf_0 cv fcbvralcsf_4 fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb fcbvralcsf_2 cv icbvralcsf_0 cv wceq id fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csbeq1a eleq12d fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv sbceq1a imbi12d cbval icbvralcsf_0 cv fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb wcel fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv wsbc wi fcbvralcsf_3 cv fcbvralcsf_5 wcel fcbvralcsf_1 wi icbvralcsf_0 fcbvralcsf_3 icbvralcsf_0 cv fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb wcel fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv wsbc fcbvralcsf_3 fcbvralcsf_3 icbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb fcbvralcsf_3 fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 fcbvralcsf_3 icbvralcsf_0 cv nfcv ecbvralcsf_0 nfcsb nfcri fcbvralcsf_0 fcbvralcsf_3 fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_3 icbvralcsf_0 cv nfcv ecbvralcsf_2 nfsbc nfim fcbvralcsf_3 cv fcbvralcsf_5 wcel fcbvralcsf_1 wi icbvralcsf_0 nfv icbvralcsf_0 cv fcbvralcsf_3 cv wceq icbvralcsf_0 cv fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb wcel fcbvralcsf_3 cv fcbvralcsf_5 wcel fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv wsbc fcbvralcsf_1 icbvralcsf_0 cv fcbvralcsf_3 cv wceq icbvralcsf_0 cv fcbvralcsf_3 cv fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb fcbvralcsf_5 icbvralcsf_0 cv fcbvralcsf_3 cv wceq id icbvralcsf_0 cv fcbvralcsf_3 cv wceq fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_4 csb fcbvralcsf_2 fcbvralcsf_3 cv fcbvralcsf_4 csb fcbvralcsf_5 fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_3 cv fcbvralcsf_4 csbeq1 fcbvralcsf_2 fcbvralcsf_3 cv fcbvralcsf_4 csb icbvralcsf_1 cv fcbvralcsf_4 wcel fcbvralcsf_2 fcbvralcsf_3 cv wsbc icbvralcsf_1 cab fcbvralcsf_5 fcbvralcsf_2 icbvralcsf_1 fcbvralcsf_3 cv fcbvralcsf_4 df-csb icbvralcsf_1 cv fcbvralcsf_4 wcel fcbvralcsf_2 fcbvralcsf_3 cv wsbc icbvralcsf_1 fcbvralcsf_5 icbvralcsf_1 cv fcbvralcsf_5 wcel icbvralcsf_1 cv fcbvralcsf_4 wcel fcbvralcsf_2 fcbvralcsf_3 wsb icbvralcsf_1 cv fcbvralcsf_4 wcel fcbvralcsf_2 fcbvralcsf_3 cv wsbc icbvralcsf_1 cv fcbvralcsf_4 wcel icbvralcsf_1 cv fcbvralcsf_5 wcel fcbvralcsf_2 fcbvralcsf_3 fcbvralcsf_2 icbvralcsf_1 fcbvralcsf_5 ecbvralcsf_1 nfcri fcbvralcsf_2 fcbvralcsf_3 weq fcbvralcsf_4 fcbvralcsf_5 icbvralcsf_1 cv ecbvralcsf_4 eleq2d sbie icbvralcsf_1 cv fcbvralcsf_4 wcel fcbvralcsf_2 fcbvralcsf_3 sbsbc bitr3i abbi2i eqtr4i syl6eq eleq12d icbvralcsf_0 cv fcbvralcsf_3 cv wceq fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv wsbc fcbvralcsf_0 fcbvralcsf_2 fcbvralcsf_3 cv wsbc fcbvralcsf_1 fcbvralcsf_0 fcbvralcsf_2 icbvralcsf_0 cv fcbvralcsf_3 cv dfsbcq fcbvralcsf_0 fcbvralcsf_2 fcbvralcsf_3 cv wsbc fcbvralcsf_0 fcbvralcsf_2 fcbvralcsf_3 wsb fcbvralcsf_1 fcbvralcsf_0 fcbvralcsf_2 fcbvralcsf_3 sbsbc fcbvralcsf_0 fcbvralcsf_1 fcbvralcsf_2 fcbvralcsf_3 ecbvralcsf_3 ecbvralcsf_5 sbie bitr3i syl6bb imbi12d cbval bitri fcbvralcsf_0 fcbvralcsf_2 fcbvralcsf_4 df-ral fcbvralcsf_1 fcbvralcsf_3 fcbvralcsf_5 df-ral 3bitr4i $.
$}
$( A more general version of ~ cbvrexf that has no distinct variable
       restrictions.  Changes bound variables using implicit substitution.
       (Contributed by Andrew Salmon, 13-Jul-2011.)  (Proof shortened by Mario
       Carneiro, 7-Dec-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	fcbvrexcsf_0 $f wff ph $.
	fcbvrexcsf_1 $f wff ps $.
	fcbvrexcsf_2 $f set x $.
	fcbvrexcsf_3 $f set y $.
	fcbvrexcsf_4 $f class A $.
	fcbvrexcsf_5 $f class B $.
	ecbvrexcsf_0 $e |- F/_ y A $.
	ecbvrexcsf_1 $e |- F/_ x B $.
	ecbvrexcsf_2 $e |- F/ y ph $.
	ecbvrexcsf_3 $e |- F/ x ps $.
	ecbvrexcsf_4 $e |- ( x = y -> A = B ) $.
	ecbvrexcsf_5 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrexcsf $p |- ( E. x e. A ph <-> E. y e. B ps ) $= fcbvrexcsf_0 wn fcbvrexcsf_2 fcbvrexcsf_4 wral wn fcbvrexcsf_1 wn fcbvrexcsf_3 fcbvrexcsf_5 wral wn fcbvrexcsf_0 fcbvrexcsf_2 fcbvrexcsf_4 wrex fcbvrexcsf_1 fcbvrexcsf_3 fcbvrexcsf_5 wrex fcbvrexcsf_0 wn fcbvrexcsf_2 fcbvrexcsf_4 wral fcbvrexcsf_1 wn fcbvrexcsf_3 fcbvrexcsf_5 wral fcbvrexcsf_0 wn fcbvrexcsf_1 wn fcbvrexcsf_2 fcbvrexcsf_3 fcbvrexcsf_4 fcbvrexcsf_5 ecbvrexcsf_0 ecbvrexcsf_1 fcbvrexcsf_0 fcbvrexcsf_3 ecbvrexcsf_2 nfn fcbvrexcsf_1 fcbvrexcsf_2 ecbvrexcsf_3 nfn ecbvrexcsf_4 fcbvrexcsf_2 cv fcbvrexcsf_3 cv wceq fcbvrexcsf_0 fcbvrexcsf_1 ecbvrexcsf_5 notbid cbvralcsf notbii fcbvrexcsf_0 fcbvrexcsf_2 fcbvrexcsf_4 dfrex2 fcbvrexcsf_1 fcbvrexcsf_3 fcbvrexcsf_5 dfrex2 3bitr4i $.
$}
$( A more general version of ~ cbvreuv that has no distinct variable
       rextrictions.  Changes bound variables using implicit substitution.
       (Contributed by Andrew Salmon, 13-Jul-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v v $.
	$v A $.
	$v B $.
	$d x v z $.
	$d y v z $.
	$d A v z $.
	$d B v z $.
	$d ph v z $.
	$d ps v z $.
	icbvreucsf_0 $f set z $.
	icbvreucsf_1 $f set v $.
	fcbvreucsf_0 $f wff ph $.
	fcbvreucsf_1 $f wff ps $.
	fcbvreucsf_2 $f set x $.
	fcbvreucsf_3 $f set y $.
	fcbvreucsf_4 $f class A $.
	fcbvreucsf_5 $f class B $.
	ecbvreucsf_0 $e |- F/_ y A $.
	ecbvreucsf_1 $e |- F/_ x B $.
	ecbvreucsf_2 $e |- F/ y ph $.
	ecbvreucsf_3 $e |- F/ x ps $.
	ecbvreucsf_4 $e |- ( x = y -> A = B ) $.
	ecbvreucsf_5 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvreucsf $p |- ( E! x e. A ph <-> E! y e. B ps ) $= fcbvreucsf_2 cv fcbvreucsf_4 wcel fcbvreucsf_0 wa fcbvreucsf_2 weu fcbvreucsf_3 cv fcbvreucsf_5 wcel fcbvreucsf_1 wa fcbvreucsf_3 weu fcbvreucsf_0 fcbvreucsf_2 fcbvreucsf_4 wreu fcbvreucsf_1 fcbvreucsf_3 fcbvreucsf_5 wreu fcbvreucsf_2 cv fcbvreucsf_4 wcel fcbvreucsf_0 wa fcbvreucsf_2 weu icbvreucsf_0 cv fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb wcel fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 wsb wa icbvreucsf_0 weu fcbvreucsf_3 cv fcbvreucsf_5 wcel fcbvreucsf_1 wa fcbvreucsf_3 weu fcbvreucsf_2 cv fcbvreucsf_4 wcel fcbvreucsf_0 wa icbvreucsf_0 cv fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb wcel fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 wsb wa fcbvreucsf_2 icbvreucsf_0 fcbvreucsf_2 cv fcbvreucsf_4 wcel fcbvreucsf_0 wa icbvreucsf_0 nfv icbvreucsf_0 cv fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb wcel fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 wsb fcbvreucsf_2 fcbvreucsf_2 icbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 nfcsb1v nfcri fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 nfs1v nfan fcbvreucsf_2 cv icbvreucsf_0 cv wceq fcbvreucsf_2 cv fcbvreucsf_4 wcel icbvreucsf_0 cv fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb wcel fcbvreucsf_0 fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 wsb fcbvreucsf_2 cv icbvreucsf_0 cv wceq fcbvreucsf_2 cv icbvreucsf_0 cv fcbvreucsf_4 fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb fcbvreucsf_2 cv icbvreucsf_0 cv wceq id fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csbeq1a eleq12d fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 sbequ12 anbi12d cbveu icbvreucsf_0 cv fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb wcel fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 wsb wa fcbvreucsf_3 cv fcbvreucsf_5 wcel fcbvreucsf_1 wa icbvreucsf_0 fcbvreucsf_3 icbvreucsf_0 cv fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb wcel fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 wsb fcbvreucsf_3 fcbvreucsf_3 icbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb fcbvreucsf_3 fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 fcbvreucsf_3 icbvreucsf_0 cv nfcv ecbvreucsf_0 nfcsb nfcri fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 fcbvreucsf_3 ecbvreucsf_2 nfsb nfan fcbvreucsf_3 cv fcbvreucsf_5 wcel fcbvreucsf_1 wa icbvreucsf_0 nfv icbvreucsf_0 cv fcbvreucsf_3 cv wceq icbvreucsf_0 cv fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb wcel fcbvreucsf_3 cv fcbvreucsf_5 wcel fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 wsb fcbvreucsf_1 icbvreucsf_0 cv fcbvreucsf_3 cv wceq icbvreucsf_0 cv fcbvreucsf_3 cv fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb fcbvreucsf_5 icbvreucsf_0 cv fcbvreucsf_3 cv wceq id icbvreucsf_0 cv fcbvreucsf_3 cv wceq fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_4 csb fcbvreucsf_2 fcbvreucsf_3 cv fcbvreucsf_4 csb fcbvreucsf_5 fcbvreucsf_2 icbvreucsf_0 cv fcbvreucsf_3 cv fcbvreucsf_4 csbeq1 icbvreucsf_1 cv fcbvreucsf_4 wcel fcbvreucsf_2 fcbvreucsf_3 wsb icbvreucsf_1 cab icbvreucsf_1 cv fcbvreucsf_4 wcel fcbvreucsf_2 fcbvreucsf_3 cv wsbc icbvreucsf_1 cab fcbvreucsf_5 fcbvreucsf_2 fcbvreucsf_3 cv fcbvreucsf_4 csb icbvreucsf_1 cv fcbvreucsf_4 wcel fcbvreucsf_2 fcbvreucsf_3 wsb icbvreucsf_1 cv fcbvreucsf_4 wcel fcbvreucsf_2 fcbvreucsf_3 cv wsbc icbvreucsf_1 icbvreucsf_1 cv fcbvreucsf_4 wcel fcbvreucsf_2 fcbvreucsf_3 sbsbc abbii icbvreucsf_1 cv fcbvreucsf_4 wcel fcbvreucsf_2 fcbvreucsf_3 wsb icbvreucsf_1 fcbvreucsf_5 icbvreucsf_1 cv fcbvreucsf_4 wcel fcbvreucsf_2 fcbvreucsf_3 wsb icbvreucsf_1 cv fcbvreucsf_5 wcel icbvreucsf_1 cv fcbvreucsf_4 wcel icbvreucsf_1 cv fcbvreucsf_5 wcel fcbvreucsf_2 fcbvreucsf_3 fcbvreucsf_2 icbvreucsf_1 fcbvreucsf_5 ecbvreucsf_1 nfcri fcbvreucsf_2 cv fcbvreucsf_3 cv wceq fcbvreucsf_4 fcbvreucsf_5 icbvreucsf_1 cv ecbvreucsf_4 eleq2d sbie bicomi abbi2i fcbvreucsf_2 icbvreucsf_1 fcbvreucsf_3 cv fcbvreucsf_4 df-csb 3eqtr4ri syl6eq eleq12d icbvreucsf_0 cv fcbvreucsf_3 cv wceq fcbvreucsf_0 fcbvreucsf_2 icbvreucsf_0 wsb fcbvreucsf_0 fcbvreucsf_2 fcbvreucsf_3 wsb fcbvreucsf_1 fcbvreucsf_0 icbvreucsf_0 fcbvreucsf_3 fcbvreucsf_2 sbequ fcbvreucsf_0 fcbvreucsf_1 fcbvreucsf_2 fcbvreucsf_3 ecbvreucsf_3 ecbvreucsf_5 sbie syl6bb anbi12d cbveu bitri fcbvreucsf_0 fcbvreucsf_2 fcbvreucsf_4 df-reu fcbvreucsf_1 fcbvreucsf_3 fcbvreucsf_5 df-reu 3bitr4i $.
$}
$( A more general version of ~ cbvrab with no distinct variable
       restrictions.  (Contributed by Andrew Salmon, 13-Jul-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$v v $.
	$v A $.
	$v B $.
	$d x v z $.
	$d y v z $.
	$d A v z $.
	$d B v z $.
	$d ph v z $.
	$d ps v z $.
	icbvrabcsf_0 $f set z $.
	icbvrabcsf_1 $f set v $.
	fcbvrabcsf_0 $f wff ph $.
	fcbvrabcsf_1 $f wff ps $.
	fcbvrabcsf_2 $f set x $.
	fcbvrabcsf_3 $f set y $.
	fcbvrabcsf_4 $f class A $.
	fcbvrabcsf_5 $f class B $.
	ecbvrabcsf_0 $e |- F/_ y A $.
	ecbvrabcsf_1 $e |- F/_ x B $.
	ecbvrabcsf_2 $e |- F/ y ph $.
	ecbvrabcsf_3 $e |- F/ x ps $.
	ecbvrabcsf_4 $e |- ( x = y -> A = B ) $.
	ecbvrabcsf_5 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvrabcsf $p |- { x e. A | ph } = { y e. B | ps } $= fcbvrabcsf_2 cv fcbvrabcsf_4 wcel fcbvrabcsf_0 wa fcbvrabcsf_2 cab fcbvrabcsf_3 cv fcbvrabcsf_5 wcel fcbvrabcsf_1 wa fcbvrabcsf_3 cab fcbvrabcsf_0 fcbvrabcsf_2 fcbvrabcsf_4 crab fcbvrabcsf_1 fcbvrabcsf_3 fcbvrabcsf_5 crab fcbvrabcsf_2 cv fcbvrabcsf_4 wcel fcbvrabcsf_0 wa fcbvrabcsf_2 cab icbvrabcsf_0 cv fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb wcel fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 wsb wa icbvrabcsf_0 cab fcbvrabcsf_3 cv fcbvrabcsf_5 wcel fcbvrabcsf_1 wa fcbvrabcsf_3 cab fcbvrabcsf_2 cv fcbvrabcsf_4 wcel fcbvrabcsf_0 wa icbvrabcsf_0 cv fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb wcel fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 wsb wa fcbvrabcsf_2 icbvrabcsf_0 fcbvrabcsf_2 cv fcbvrabcsf_4 wcel fcbvrabcsf_0 wa icbvrabcsf_0 nfv icbvrabcsf_0 cv fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb wcel fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 wsb fcbvrabcsf_2 fcbvrabcsf_2 icbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 nfcsb1v nfcri fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 nfs1v nfan fcbvrabcsf_2 cv icbvrabcsf_0 cv wceq fcbvrabcsf_2 cv fcbvrabcsf_4 wcel icbvrabcsf_0 cv fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb wcel fcbvrabcsf_0 fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 wsb fcbvrabcsf_2 cv icbvrabcsf_0 cv wceq fcbvrabcsf_2 cv icbvrabcsf_0 cv fcbvrabcsf_4 fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb fcbvrabcsf_2 cv icbvrabcsf_0 cv wceq id fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csbeq1a eleq12d fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 sbequ12 anbi12d cbvab icbvrabcsf_0 cv fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb wcel fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 wsb wa fcbvrabcsf_3 cv fcbvrabcsf_5 wcel fcbvrabcsf_1 wa icbvrabcsf_0 fcbvrabcsf_3 icbvrabcsf_0 cv fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb wcel fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 wsb fcbvrabcsf_3 fcbvrabcsf_3 icbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb fcbvrabcsf_3 fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 fcbvrabcsf_3 icbvrabcsf_0 cv nfcv ecbvrabcsf_0 nfcsb nfcri fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 fcbvrabcsf_3 ecbvrabcsf_2 nfsb nfan fcbvrabcsf_3 cv fcbvrabcsf_5 wcel fcbvrabcsf_1 wa icbvrabcsf_0 nfv icbvrabcsf_0 cv fcbvrabcsf_3 cv wceq icbvrabcsf_0 cv fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb wcel fcbvrabcsf_3 cv fcbvrabcsf_5 wcel fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 wsb fcbvrabcsf_1 icbvrabcsf_0 cv fcbvrabcsf_3 cv wceq icbvrabcsf_0 cv fcbvrabcsf_3 cv fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb fcbvrabcsf_5 icbvrabcsf_0 cv fcbvrabcsf_3 cv wceq id icbvrabcsf_0 cv fcbvrabcsf_3 cv wceq fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_4 csb fcbvrabcsf_2 fcbvrabcsf_3 cv fcbvrabcsf_4 csb fcbvrabcsf_5 fcbvrabcsf_2 icbvrabcsf_0 cv fcbvrabcsf_3 cv fcbvrabcsf_4 csbeq1 fcbvrabcsf_2 fcbvrabcsf_3 cv fcbvrabcsf_4 csb icbvrabcsf_1 cv fcbvrabcsf_4 wcel fcbvrabcsf_2 fcbvrabcsf_3 cv wsbc icbvrabcsf_1 cab fcbvrabcsf_5 fcbvrabcsf_2 icbvrabcsf_1 fcbvrabcsf_3 cv fcbvrabcsf_4 df-csb icbvrabcsf_1 cv fcbvrabcsf_4 wcel fcbvrabcsf_2 fcbvrabcsf_3 cv wsbc icbvrabcsf_1 fcbvrabcsf_5 icbvrabcsf_1 cv fcbvrabcsf_5 wcel icbvrabcsf_1 cv fcbvrabcsf_4 wcel fcbvrabcsf_2 fcbvrabcsf_3 wsb icbvrabcsf_1 cv fcbvrabcsf_4 wcel fcbvrabcsf_2 fcbvrabcsf_3 cv wsbc icbvrabcsf_1 cv fcbvrabcsf_4 wcel icbvrabcsf_1 cv fcbvrabcsf_5 wcel fcbvrabcsf_2 fcbvrabcsf_3 fcbvrabcsf_2 icbvrabcsf_1 fcbvrabcsf_5 ecbvrabcsf_1 nfcri fcbvrabcsf_2 fcbvrabcsf_3 weq fcbvrabcsf_4 fcbvrabcsf_5 icbvrabcsf_1 cv ecbvrabcsf_4 eleq2d sbie icbvrabcsf_1 cv fcbvrabcsf_4 wcel fcbvrabcsf_2 fcbvrabcsf_3 sbsbc bitr3i abbi2i eqtr4i syl6eq eleq12d icbvrabcsf_0 cv fcbvrabcsf_3 cv wceq fcbvrabcsf_0 fcbvrabcsf_2 icbvrabcsf_0 wsb fcbvrabcsf_0 fcbvrabcsf_2 fcbvrabcsf_3 wsb fcbvrabcsf_1 fcbvrabcsf_0 icbvrabcsf_0 fcbvrabcsf_3 fcbvrabcsf_2 sbequ fcbvrabcsf_0 fcbvrabcsf_1 fcbvrabcsf_2 fcbvrabcsf_3 ecbvrabcsf_3 ecbvrabcsf_5 sbie syl6bb anbi12d cbvab eqtri fcbvrabcsf_0 fcbvrabcsf_2 fcbvrabcsf_4 df-rab fcbvrabcsf_1 fcbvrabcsf_3 fcbvrabcsf_5 df-rab 3eqtr4i $.
$}
$( Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution which also changes the quantifier
       domain.  (Contributed by David Moews, 1-May-2017.) $)
${
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d A y $.
	$d ps y $.
	$d B x $.
	$d ch x $.
	fcbvralv2_0 $f wff ps $.
	fcbvralv2_1 $f wff ch $.
	fcbvralv2_2 $f set x $.
	fcbvralv2_3 $f set y $.
	fcbvralv2_4 $f class A $.
	fcbvralv2_5 $f class B $.
	ecbvralv2_0 $e |- ( x = y -> ( ps <-> ch ) ) $.
	ecbvralv2_1 $e |- ( x = y -> A = B ) $.
	cbvralv2 $p |- ( A. x e. A ps <-> A. y e. B ch ) $= fcbvralv2_0 fcbvralv2_1 fcbvralv2_2 fcbvralv2_3 fcbvralv2_4 fcbvralv2_5 fcbvralv2_3 fcbvralv2_4 nfcv fcbvralv2_2 fcbvralv2_5 nfcv fcbvralv2_0 fcbvralv2_3 nfv fcbvralv2_1 fcbvralv2_2 nfv ecbvralv2_1 ecbvralv2_0 cbvralcsf $.
$}
$( Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution which also changes the quantifier
       domain.  (Contributed by David Moews, 1-May-2017.) $)
${
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d A y $.
	$d ps y $.
	$d B x $.
	$d ch x $.
	fcbvrexv2_0 $f wff ps $.
	fcbvrexv2_1 $f wff ch $.
	fcbvrexv2_2 $f set x $.
	fcbvrexv2_3 $f set y $.
	fcbvrexv2_4 $f class A $.
	fcbvrexv2_5 $f class B $.
	ecbvrexv2_0 $e |- ( x = y -> ( ps <-> ch ) ) $.
	ecbvrexv2_1 $e |- ( x = y -> A = B ) $.
	cbvrexv2 $p |- ( E. x e. A ps <-> E. y e. B ch ) $= fcbvrexv2_0 fcbvrexv2_1 fcbvrexv2_2 fcbvrexv2_3 fcbvrexv2_4 fcbvrexv2_5 fcbvrexv2_3 fcbvrexv2_4 nfcv fcbvrexv2_2 fcbvrexv2_5 nfcv fcbvrexv2_0 fcbvrexv2_3 nfv fcbvrexv2_1 fcbvrexv2_2 nfv ecbvrexv2_1 ecbvrexv2_0 cbvrexcsf $.
$}

