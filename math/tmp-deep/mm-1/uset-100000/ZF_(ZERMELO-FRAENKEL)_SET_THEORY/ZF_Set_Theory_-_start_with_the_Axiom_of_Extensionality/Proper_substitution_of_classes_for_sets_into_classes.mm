$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Proper_substitution_of_classes_for_sets.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Proper substitution of classes for sets into classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c [_ $.

$(Underlined left bracket $)

$c ]_ $.

$(Underlined right bracket $)

$(Extend class notation to include the proper substitution of a class for a
     set into another class. $)

${
	$v x A B  $.
	f0_csb $f set x $.
	f1_csb $f class A $.
	f2_csb $f class B $.
	a_csb $a class [_ A / x ]_ B $.
$}

$(Define the proper substitution of a class for a set into another class.
       The underlined brackets distinguish it from the substitution into a wff,
       ~ wsbc , to prevent ambiguity.  Theorem ~ sbcel1g shows an example of
       how ambiguity could arise if we didn't use distinguished brackets.
       Theorem ~ sbccsbg recreates substitution into a wff from this
       definition.  (Contributed by NM, 10-Nov-2005.) $)

${
	$v x y A B  $.
	$d y A  $.
	$d y B  $.
	$d x y  $.
	f0_df-csb $f set x $.
	f1_df-csb $f set y $.
	f2_df-csb $f class A $.
	f3_df-csb $f class B $.
	a_df-csb $a |- [_ A / x ]_ B = { y | [. A / x ]. y e. B } $.
$}

$(Alternate expression for the proper substitution into a class, without
       referencing substitution into a wff.  Note that ` x ` can be free in
       ` B ` but cannot occur in ` A ` .  (Contributed by NM, 2-Dec-2013.) $)

${
	$v x y A B  $.
	$d x y A  $.
	$d y B  $.
	$d x y  $.
	f0_csb2 $f set x $.
	f1_csb2 $f set y $.
	f2_csb2 $f class A $.
	f3_csb2 $f class B $.
	p_csb2 $p |- [_ A / x ]_ B = { y | E. x ( x = A /\ y e. B ) } $= f0_csb2 f1_csb2 f2_csb2 f3_csb2 a_df-csb f1_csb2 a_sup_set_class f3_csb2 a_wcel f0_csb2 f2_csb2 p_sbc5 f1_csb2 a_sup_set_class f3_csb2 a_wcel f0_csb2 f2_csb2 a_wsbc f0_csb2 a_sup_set_class f2_csb2 a_wceq f1_csb2 a_sup_set_class f3_csb2 a_wcel a_wa f0_csb2 a_wex f1_csb2 p_abbii f0_csb2 f2_csb2 f3_csb2 a_csb f1_csb2 a_sup_set_class f3_csb2 a_wcel f0_csb2 f2_csb2 a_wsbc f1_csb2 a_cab f0_csb2 a_sup_set_class f2_csb2 a_wceq f1_csb2 a_sup_set_class f3_csb2 a_wcel a_wa f0_csb2 a_wex f1_csb2 a_cab p_eqtri $.
$}

$(Analog of ~ dfsbcq for proper substitution into a class.  (Contributed
       by NM, 10-Nov-2005.) $)

${
	$v x A B C  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	f0_csbeq1 $f set x $.
	f1_csbeq1 $f class A $.
	f2_csbeq1 $f class B $.
	f3_csbeq1 $f class C $.
	i0_csbeq1 $f set y $.
	p_csbeq1 $p |- ( A = B -> [_ A / x ]_ C = [_ B / x ]_ C ) $= i0_csbeq1 a_sup_set_class f3_csbeq1 a_wcel f0_csbeq1 f1_csbeq1 f2_csbeq1 p_dfsbcq f1_csbeq1 f2_csbeq1 a_wceq i0_csbeq1 a_sup_set_class f3_csbeq1 a_wcel f0_csbeq1 f1_csbeq1 a_wsbc i0_csbeq1 a_sup_set_class f3_csbeq1 a_wcel f0_csbeq1 f2_csbeq1 a_wsbc i0_csbeq1 p_abbidv f0_csbeq1 i0_csbeq1 f1_csbeq1 f3_csbeq1 a_df-csb f0_csbeq1 i0_csbeq1 f2_csbeq1 f3_csbeq1 a_df-csb f1_csbeq1 f2_csbeq1 a_wceq i0_csbeq1 a_sup_set_class f3_csbeq1 a_wcel f0_csbeq1 f1_csbeq1 a_wsbc i0_csbeq1 a_cab i0_csbeq1 a_sup_set_class f3_csbeq1 a_wcel f0_csbeq1 f2_csbeq1 a_wsbc i0_csbeq1 a_cab f0_csbeq1 f1_csbeq1 f3_csbeq1 a_csb f0_csbeq1 f2_csbeq1 f3_csbeq1 a_csb p_3eqtr4g $.
$}

$(Change bound variables in a class substitution.  Interestingly, this
       does not require any bound variable conditions on ` A ` .  (Contributed
       by Jeff Hankins, 13-Sep-2009.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)

${
	$v x y A C D  $.
	$d x z  $.
	$d y z  $.
	$d z A  $.
	$d z C  $.
	$d z D  $.
	f0_cbvcsb $f set x $.
	f1_cbvcsb $f set y $.
	f2_cbvcsb $f class A $.
	f3_cbvcsb $f class C $.
	f4_cbvcsb $f class D $.
	i0_cbvcsb $f set z $.
	e0_cbvcsb $e |- F/_ y C $.
	e1_cbvcsb $e |- F/_ x D $.
	e2_cbvcsb $e |- ( x = y -> C = D ) $.
	p_cbvcsb $p |- [_ A / x ]_ C = [_ A / y ]_ D $= e0_cbvcsb f1_cbvcsb i0_cbvcsb f3_cbvcsb p_nfcri e1_cbvcsb f0_cbvcsb i0_cbvcsb f4_cbvcsb p_nfcri e2_cbvcsb f0_cbvcsb a_sup_set_class f1_cbvcsb a_sup_set_class a_wceq f3_cbvcsb f4_cbvcsb i0_cbvcsb a_sup_set_class p_eleq2d i0_cbvcsb a_sup_set_class f3_cbvcsb a_wcel i0_cbvcsb a_sup_set_class f4_cbvcsb a_wcel f0_cbvcsb f1_cbvcsb f2_cbvcsb p_cbvsbc i0_cbvcsb a_sup_set_class f3_cbvcsb a_wcel f0_cbvcsb f2_cbvcsb a_wsbc i0_cbvcsb a_sup_set_class f4_cbvcsb a_wcel f1_cbvcsb f2_cbvcsb a_wsbc i0_cbvcsb p_abbii f0_cbvcsb i0_cbvcsb f2_cbvcsb f3_cbvcsb a_df-csb f1_cbvcsb i0_cbvcsb f2_cbvcsb f4_cbvcsb a_df-csb i0_cbvcsb a_sup_set_class f3_cbvcsb a_wcel f0_cbvcsb f2_cbvcsb a_wsbc i0_cbvcsb a_cab i0_cbvcsb a_sup_set_class f4_cbvcsb a_wcel f1_cbvcsb f2_cbvcsb a_wsbc i0_cbvcsb a_cab f0_cbvcsb f2_cbvcsb f3_cbvcsb a_csb f1_cbvcsb f2_cbvcsb f4_cbvcsb a_csb p_3eqtr4i $.
$}

$(Change the bound variable of a proper substitution into a class using
       implicit substitution.  (Contributed by NM, 30-Sep-2008.)  (Revised by
       Mario Carneiro, 13-Oct-2016.) $)

${
	$v x y A B C  $.
	$d x y  $.
	$d A  $.
	$d y B  $.
	$d x C  $.
	f0_cbvcsbv $f set x $.
	f1_cbvcsbv $f set y $.
	f2_cbvcsbv $f class A $.
	f3_cbvcsbv $f class B $.
	f4_cbvcsbv $f class C $.
	e0_cbvcsbv $e |- ( x = y -> B = C ) $.
	p_cbvcsbv $p |- [_ A / x ]_ B = [_ A / y ]_ C $= f1_cbvcsbv f3_cbvcsbv p_nfcv f0_cbvcsbv f4_cbvcsbv p_nfcv e0_cbvcsbv f0_cbvcsbv f1_cbvcsbv f2_cbvcsbv f3_cbvcsbv f4_cbvcsbv p_cbvcsb $.
$}

$(Equality deduction for proper substitution into a class.  (Contributed
       by NM, 3-Dec-2005.) $)

${
	$v ph x A B C  $.
	f0_csbeq1d $f wff ph $.
	f1_csbeq1d $f set x $.
	f2_csbeq1d $f class A $.
	f3_csbeq1d $f class B $.
	f4_csbeq1d $f class C $.
	e0_csbeq1d $e |- ( ph -> A = B ) $.
	p_csbeq1d $p |- ( ph -> [_ A / x ]_ C = [_ B / x ]_ C ) $= e0_csbeq1d f1_csbeq1d f2_csbeq1d f3_csbeq1d f4_csbeq1d p_csbeq1 f0_csbeq1d f2_csbeq1d f3_csbeq1d a_wceq f1_csbeq1d f2_csbeq1d f4_csbeq1d a_csb f1_csbeq1d f3_csbeq1d f4_csbeq1d a_csb a_wceq p_syl $.
$}

$(Analog of ~ sbid for proper substitution into a class.  (Contributed by
       NM, 10-Nov-2005.) $)

${
	$v x A  $.
	$d x y  $.
	$d y A  $.
	f0_csbid $f set x $.
	f1_csbid $f class A $.
	i0_csbid $f set y $.
	p_csbid $p |- [_ x / x ]_ A = A $= f0_csbid i0_csbid f0_csbid a_sup_set_class f1_csbid a_df-csb i0_csbid a_sup_set_class f1_csbid a_wcel f0_csbid f0_csbid p_sbsbc i0_csbid a_sup_set_class f1_csbid a_wcel f0_csbid p_sbid i0_csbid a_sup_set_class f1_csbid a_wcel f0_csbid f0_csbid a_sup_set_class a_wsbc i0_csbid a_sup_set_class f1_csbid a_wcel f0_csbid f0_csbid a_wsb i0_csbid a_sup_set_class f1_csbid a_wcel p_bitr3i i0_csbid a_sup_set_class f1_csbid a_wcel f0_csbid f0_csbid a_sup_set_class a_wsbc i0_csbid a_sup_set_class f1_csbid a_wcel i0_csbid p_abbii i0_csbid f1_csbid p_abid2 f0_csbid f0_csbid a_sup_set_class f1_csbid a_csb i0_csbid a_sup_set_class f1_csbid a_wcel f0_csbid f0_csbid a_sup_set_class a_wsbc i0_csbid a_cab i0_csbid a_sup_set_class f1_csbid a_wcel i0_csbid a_cab f1_csbid p_3eqtri $.
$}

$(Equality theorem for proper substitution into a class.  (Contributed by
       NM, 10-Nov-2005.) $)

${
	$v x A B  $.
	$d x  $.
	$d A  $.
	$d B  $.
	f0_csbeq1a $f set x $.
	f1_csbeq1a $f class A $.
	f2_csbeq1a $f class B $.
	p_csbeq1a $p |- ( x = A -> B = [_ A / x ]_ B ) $= f0_csbeq1a f2_csbeq1a p_csbid f0_csbeq1a f0_csbeq1a a_sup_set_class f1_csbeq1a f2_csbeq1a p_csbeq1 f0_csbeq1a a_sup_set_class f1_csbeq1a a_wceq f2_csbeq1a f0_csbeq1a f0_csbeq1a a_sup_set_class f2_csbeq1a a_csb f0_csbeq1a f1_csbeq1a f2_csbeq1a a_csb p_syl5eqr $.
$}

$(Composition law for chained substitutions into a class.  (Contributed by
       NM, 10-Nov-2005.) $)

${
	$v x y A B  $.
	$d z A  $.
	$d y z B  $.
	$d z  $.
	$d x z  $.
	f0_csbco $f set x $.
	f1_csbco $f set y $.
	f2_csbco $f class A $.
	f3_csbco $f class B $.
	i0_csbco $f set z $.
	p_csbco $p |- [_ A / y ]_ [_ y / x ]_ B = [_ A / x ]_ B $= f0_csbco i0_csbco f1_csbco a_sup_set_class f3_csbco a_df-csb i0_csbco a_sup_set_class f3_csbco a_wcel f0_csbco f1_csbco a_sup_set_class a_wsbc i0_csbco f0_csbco f1_csbco a_sup_set_class f3_csbco a_csb p_abeq2i i0_csbco a_sup_set_class f0_csbco f1_csbco a_sup_set_class f3_csbco a_csb a_wcel i0_csbco a_sup_set_class f3_csbco a_wcel f0_csbco f1_csbco a_sup_set_class a_wsbc f1_csbco f2_csbco p_sbcbii i0_csbco a_sup_set_class f3_csbco a_wcel f0_csbco f1_csbco f2_csbco p_sbcco i0_csbco a_sup_set_class f0_csbco f1_csbco a_sup_set_class f3_csbco a_csb a_wcel f1_csbco f2_csbco a_wsbc i0_csbco a_sup_set_class f3_csbco a_wcel f0_csbco f1_csbco a_sup_set_class a_wsbc f1_csbco f2_csbco a_wsbc i0_csbco a_sup_set_class f3_csbco a_wcel f0_csbco f2_csbco a_wsbc p_bitri i0_csbco a_sup_set_class f0_csbco f1_csbco a_sup_set_class f3_csbco a_csb a_wcel f1_csbco f2_csbco a_wsbc i0_csbco a_sup_set_class f3_csbco a_wcel f0_csbco f2_csbco a_wsbc i0_csbco p_abbii f1_csbco i0_csbco f2_csbco f0_csbco f1_csbco a_sup_set_class f3_csbco a_csb a_df-csb f0_csbco i0_csbco f2_csbco f3_csbco a_df-csb i0_csbco a_sup_set_class f0_csbco f1_csbco a_sup_set_class f3_csbco a_csb a_wcel f1_csbco f2_csbco a_wsbc i0_csbco a_cab i0_csbco a_sup_set_class f3_csbco a_wcel f0_csbco f2_csbco a_wsbc i0_csbco a_cab f1_csbco f2_csbco f0_csbco f1_csbco a_sup_set_class f3_csbco a_csb a_csb f0_csbco f2_csbco f3_csbco a_csb p_3eqtr4i $.
$}

$(The existence of proper substitution into a class.  (Contributed by NM,
       10-Nov-2005.) $)

${
	$v x A B V W  $.
	$d y A  $.
	$d y B  $.
	$d x y  $.
	f0_csbexg $f set x $.
	f1_csbexg $f class A $.
	f2_csbexg $f class B $.
	f3_csbexg $f class V $.
	f4_csbexg $f class W $.
	i0_csbexg $f set y $.
	p_csbexg $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ B e. _V ) $= f0_csbexg i0_csbexg f1_csbexg f2_csbexg a_df-csb i0_csbexg f2_csbexg p_abid2 f2_csbexg f4_csbexg p_elex f2_csbexg f4_csbexg a_wcel i0_csbexg a_sup_set_class f2_csbexg a_wcel i0_csbexg a_cab f2_csbexg a_cvv p_syl5eqel f2_csbexg f4_csbexg a_wcel i0_csbexg a_sup_set_class f2_csbexg a_wcel i0_csbexg a_cab a_cvv a_wcel f0_csbexg p_alimi i0_csbexg a_sup_set_class f2_csbexg a_wcel i0_csbexg a_cab a_cvv a_wcel f0_csbexg f1_csbexg f3_csbexg p_spsbc f2_csbexg f4_csbexg a_wcel f0_csbexg a_wal i0_csbexg a_sup_set_class f2_csbexg a_wcel i0_csbexg a_cab a_cvv a_wcel f0_csbexg a_wal f1_csbexg f3_csbexg a_wcel i0_csbexg a_sup_set_class f2_csbexg a_wcel i0_csbexg a_cab a_cvv a_wcel f0_csbexg f1_csbexg a_wsbc p_syl5 f1_csbexg f3_csbexg a_wcel f2_csbexg f4_csbexg a_wcel f0_csbexg a_wal i0_csbexg a_sup_set_class f2_csbexg a_wcel i0_csbexg a_cab a_cvv a_wcel f0_csbexg f1_csbexg a_wsbc p_imp f0_csbexg a_cvv p_nfcv i0_csbexg a_sup_set_class f2_csbexg a_wcel f0_csbexg i0_csbexg f1_csbexg a_cvv f3_csbexg p_sbcabel f1_csbexg f3_csbexg a_wcel i0_csbexg a_sup_set_class f2_csbexg a_wcel i0_csbexg a_cab a_cvv a_wcel f0_csbexg f1_csbexg a_wsbc i0_csbexg a_sup_set_class f2_csbexg a_wcel f0_csbexg f1_csbexg a_wsbc i0_csbexg a_cab a_cvv a_wcel a_wb f2_csbexg f4_csbexg a_wcel f0_csbexg a_wal p_adantr f1_csbexg f3_csbexg a_wcel f2_csbexg f4_csbexg a_wcel f0_csbexg a_wal a_wa i0_csbexg a_sup_set_class f2_csbexg a_wcel i0_csbexg a_cab a_cvv a_wcel f0_csbexg f1_csbexg a_wsbc i0_csbexg a_sup_set_class f2_csbexg a_wcel f0_csbexg f1_csbexg a_wsbc i0_csbexg a_cab a_cvv a_wcel p_mpbid f1_csbexg f3_csbexg a_wcel f2_csbexg f4_csbexg a_wcel f0_csbexg a_wal a_wa f0_csbexg f1_csbexg f2_csbexg a_csb i0_csbexg a_sup_set_class f2_csbexg a_wcel f0_csbexg f1_csbexg a_wsbc i0_csbexg a_cab a_cvv p_syl5eqel $.
$}

$(The existence of proper substitution into a class.  (Contributed by NM,
       7-Aug-2007.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v x A B  $.
	f0_csbex $f set x $.
	f1_csbex $f class A $.
	f2_csbex $f class B $.
	e0_csbex $e |- A e. _V $.
	e1_csbex $e |- B e. _V $.
	p_csbex $p |- [_ A / x ]_ B e. _V $= e0_csbex f0_csbex f1_csbex f2_csbex a_cvv a_cvv p_csbexg f1_csbex a_cvv a_wcel f2_csbex a_cvv a_wcel f0_csbex a_wal f0_csbex f1_csbex f2_csbex a_csb a_cvv a_wcel p_mpan e1_csbex f2_csbex a_cvv a_wcel f0_csbex f1_csbex f2_csbex a_csb a_cvv a_wcel f0_csbex p_mpg $.
$}

$(Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free).  (Contributed by Mario Carneiro, 14-Oct-2016.) $)

${
	$v x A B V  $.
	$d y A  $.
	$d y B  $.
	$d y V  $.
	$d x y  $.
	f0_csbtt $f set x $.
	f1_csbtt $f class A $.
	f2_csbtt $f class B $.
	f3_csbtt $f class V $.
	i0_csbtt $f set y $.
	p_csbtt $p |- ( ( A e. V /\ F/_ x B ) -> [_ A / x ]_ B = B ) $= f0_csbtt i0_csbtt f1_csbtt f2_csbtt a_df-csb f0_csbtt i0_csbtt f2_csbtt p_nfcr i0_csbtt a_sup_set_class f2_csbtt a_wcel f0_csbtt f1_csbtt f3_csbtt p_sbctt f0_csbtt f2_csbtt a_wnfc f1_csbtt f3_csbtt a_wcel i0_csbtt a_sup_set_class f2_csbtt a_wcel f0_csbtt a_wnf i0_csbtt a_sup_set_class f2_csbtt a_wcel f0_csbtt f1_csbtt a_wsbc i0_csbtt a_sup_set_class f2_csbtt a_wcel a_wb p_sylan2 f1_csbtt f3_csbtt a_wcel f0_csbtt f2_csbtt a_wnfc a_wa i0_csbtt a_sup_set_class f2_csbtt a_wcel f0_csbtt f1_csbtt a_wsbc i0_csbtt f2_csbtt p_abbi1dv f1_csbtt f3_csbtt a_wcel f0_csbtt f2_csbtt a_wnfc a_wa f0_csbtt f1_csbtt f2_csbtt a_csb i0_csbtt a_sup_set_class f2_csbtt a_wcel f0_csbtt f1_csbtt a_wsbc i0_csbtt a_cab f2_csbtt p_syl5eq $.
$}

$(Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free).  (Contributed by NM, 10-Nov-2005.) $)

${
	$v x A B V  $.
	f0_csbconstgf $f set x $.
	f1_csbconstgf $f class A $.
	f2_csbconstgf $f class B $.
	f3_csbconstgf $f class V $.
	e0_csbconstgf $e |- F/_ x B $.
	p_csbconstgf $p |- ( A e. V -> [_ A / x ]_ B = B ) $= e0_csbconstgf f0_csbconstgf f1_csbconstgf f2_csbconstgf f3_csbconstgf p_csbtt f1_csbconstgf f3_csbconstgf a_wcel f0_csbconstgf f2_csbconstgf a_wnfc f0_csbconstgf f1_csbconstgf f2_csbconstgf a_csb f2_csbconstgf a_wceq p_mpan2 $.
$}

$(Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free). ~ csbconstgf with distinct variable requirement.  (Contributed by
       Alan Sare, 22-Jul-2012.) $)

${
	$v x A B V  $.
	$d A  $.
	$d B x  $.
	$d V  $.
	f0_csbconstg $f set x $.
	f1_csbconstg $f class A $.
	f2_csbconstg $f class B $.
	f3_csbconstg $f class V $.
	p_csbconstg $p |- ( A e. V -> [_ A / x ]_ B = B ) $= f0_csbconstg f2_csbconstg p_nfcv f0_csbconstg f1_csbconstg f2_csbconstg f3_csbconstg p_csbconstgf $.
$}

$(Distribute proper substitution through a membership relation.
       (Contributed by NM, 10-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v x A B C V  $.
	$d x y z  $.
	$d y z A  $.
	$d y z B  $.
	$d y z C  $.
	f0_sbcel12g $f set x $.
	f1_sbcel12g $f class A $.
	f2_sbcel12g $f class B $.
	f3_sbcel12g $f class C $.
	f4_sbcel12g $f class V $.
	i0_sbcel12g $f set y $.
	i1_sbcel12g $f set z $.
	p_sbcel12g $p |- ( A e. V -> ( [. A / x ]. B e. C <-> [_ A / x ]_ B e. [_ A / x ]_ C ) ) $= f2_sbcel12g f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g f1_sbcel12g p_dfsbcq2 i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g f1_sbcel12g p_dfsbcq2 i1_sbcel12g a_sup_set_class f1_sbcel12g a_wceq i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g p_abbidv i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g f1_sbcel12g p_dfsbcq2 i1_sbcel12g a_sup_set_class f1_sbcel12g a_wceq i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g p_abbidv i1_sbcel12g a_sup_set_class f1_sbcel12g a_wceq i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_cab i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_cab p_eleq12d i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g p_nfs1v i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb f0_sbcel12g i0_sbcel12g p_nfab i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g p_nfs1v i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb f0_sbcel12g i0_sbcel12g p_nfab f0_sbcel12g i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab p_nfel f0_sbcel12g i1_sbcel12g i0_sbcel12g f2_sbcel12g p_sbab f0_sbcel12g i1_sbcel12g i0_sbcel12g f3_sbcel12g p_sbab f0_sbcel12g a_sup_set_class i1_sbcel12g a_sup_set_class a_wceq f2_sbcel12g i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab f3_sbcel12g i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab p_eleq12d f2_sbcel12g f3_sbcel12g a_wcel i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab a_wcel f0_sbcel12g i1_sbcel12g p_sbie f2_sbcel12g f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g i1_sbcel12g a_wsb i0_sbcel12g a_cab a_wcel f2_sbcel12g f3_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_cab i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_cab a_wcel i1_sbcel12g f1_sbcel12g f4_sbcel12g p_vtoclbg f0_sbcel12g i0_sbcel12g f1_sbcel12g f2_sbcel12g a_df-csb f0_sbcel12g i0_sbcel12g f1_sbcel12g f3_sbcel12g a_df-csb f0_sbcel12g f1_sbcel12g f2_sbcel12g a_csb i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_cab f0_sbcel12g f1_sbcel12g f3_sbcel12g a_csb i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_cab p_eleq12i f1_sbcel12g f4_sbcel12g a_wcel f2_sbcel12g f3_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_sup_set_class f2_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_cab i0_sbcel12g a_sup_set_class f3_sbcel12g a_wcel f0_sbcel12g f1_sbcel12g a_wsbc i0_sbcel12g a_cab a_wcel f0_sbcel12g f1_sbcel12g f2_sbcel12g a_csb f0_sbcel12g f1_sbcel12g f3_sbcel12g a_csb a_wcel p_syl6bbr $.
$}

$(Distribute proper substitution through an equality relation.
       (Contributed by NM, 10-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v x A B C V  $.
	$d x y z  $.
	$d y z A  $.
	$d y z B  $.
	$d y z C  $.
	f0_sbceqg $f set x $.
	f1_sbceqg $f class A $.
	f2_sbceqg $f class B $.
	f3_sbceqg $f class C $.
	f4_sbceqg $f class V $.
	i0_sbceqg $f set y $.
	i1_sbceqg $f set z $.
	p_sbceqg $p |- ( A e. V -> ( [. A / x ]. B = C <-> [_ A / x ]_ B = [_ A / x ]_ C ) ) $= f2_sbceqg f3_sbceqg a_wceq f0_sbceqg i1_sbceqg f1_sbceqg p_dfsbcq2 i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg f1_sbceqg p_dfsbcq2 i1_sbceqg a_sup_set_class f1_sbceqg a_wceq i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg p_abbidv i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg f1_sbceqg p_dfsbcq2 i1_sbceqg a_sup_set_class f1_sbceqg a_wceq i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg p_abbidv i1_sbceqg a_sup_set_class f1_sbceqg a_wceq i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_cab i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_cab p_eqeq12d i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg p_nfs1v i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb f0_sbceqg i0_sbceqg p_nfab i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg p_nfs1v i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb f0_sbceqg i0_sbceqg p_nfab f0_sbceqg i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab p_nfeq f0_sbceqg i1_sbceqg i0_sbceqg f2_sbceqg p_sbab f0_sbceqg i1_sbceqg i0_sbceqg f3_sbceqg p_sbab f0_sbceqg a_sup_set_class i1_sbceqg a_sup_set_class a_wceq f2_sbceqg i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab f3_sbceqg i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab p_eqeq12d f2_sbceqg f3_sbceqg a_wceq i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab a_wceq f0_sbceqg i1_sbceqg p_sbie f2_sbceqg f3_sbceqg a_wceq f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg i1_sbceqg a_wsb i0_sbceqg a_cab a_wceq f2_sbceqg f3_sbceqg a_wceq f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_cab i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_cab a_wceq i1_sbceqg f1_sbceqg f4_sbceqg p_vtoclbg f0_sbceqg i0_sbceqg f1_sbceqg f2_sbceqg a_df-csb f0_sbceqg i0_sbceqg f1_sbceqg f3_sbceqg a_df-csb f0_sbceqg f1_sbceqg f2_sbceqg a_csb i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_cab f0_sbceqg f1_sbceqg f3_sbceqg a_csb i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_cab p_eqeq12i f1_sbceqg f4_sbceqg a_wcel f2_sbceqg f3_sbceqg a_wceq f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_sup_set_class f2_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_cab i0_sbceqg a_sup_set_class f3_sbceqg a_wcel f0_sbceqg f1_sbceqg a_wsbc i0_sbceqg a_cab a_wceq f0_sbceqg f1_sbceqg f2_sbceqg a_csb f0_sbceqg f1_sbceqg f3_sbceqg a_csb a_wceq p_syl6bbr $.
$}

$(Distribute proper substitution through negated membership.  (Contributed
     by Andrew Salmon, 18-Jun-2011.) $)

${
	$v x A B C V  $.
	f0_sbcnel12g $f set x $.
	f1_sbcnel12g $f class A $.
	f2_sbcnel12g $f class B $.
	f3_sbcnel12g $f class C $.
	f4_sbcnel12g $f class V $.
	p_sbcnel12g $p |- ( A e. V -> ( [. A / x ]. B e/ C <-> [_ A / x ]_ B e/ [_ A / x ]_ C ) ) $= f2_sbcnel12g f3_sbcnel12g a_df-nel f2_sbcnel12g f3_sbcnel12g a_wnel f2_sbcnel12g f3_sbcnel12g a_wcel a_wn f0_sbcnel12g f1_sbcnel12g p_sbcbii f2_sbcnel12g f3_sbcnel12g a_wnel f0_sbcnel12g f1_sbcnel12g a_wsbc f2_sbcnel12g f3_sbcnel12g a_wcel a_wn f0_sbcnel12g f1_sbcnel12g a_wsbc a_wb f1_sbcnel12g f4_sbcnel12g a_wcel p_a1i f2_sbcnel12g f3_sbcnel12g a_wcel f0_sbcnel12g f1_sbcnel12g f4_sbcnel12g p_sbcng f0_sbcnel12g f1_sbcnel12g f2_sbcnel12g f3_sbcnel12g f4_sbcnel12g p_sbcel12g f1_sbcnel12g f4_sbcnel12g a_wcel f2_sbcnel12g f3_sbcnel12g a_wcel f0_sbcnel12g f1_sbcnel12g a_wsbc f0_sbcnel12g f1_sbcnel12g f2_sbcnel12g a_csb f0_sbcnel12g f1_sbcnel12g f3_sbcnel12g a_csb a_wcel p_notbid f0_sbcnel12g f1_sbcnel12g f2_sbcnel12g a_csb f0_sbcnel12g f1_sbcnel12g f3_sbcnel12g a_csb a_df-nel f1_sbcnel12g f4_sbcnel12g a_wcel f2_sbcnel12g f3_sbcnel12g a_wcel f0_sbcnel12g f1_sbcnel12g a_wsbc a_wn f0_sbcnel12g f1_sbcnel12g f2_sbcnel12g a_csb f0_sbcnel12g f1_sbcnel12g f3_sbcnel12g a_csb a_wcel a_wn f0_sbcnel12g f1_sbcnel12g f2_sbcnel12g a_csb f0_sbcnel12g f1_sbcnel12g f3_sbcnel12g a_csb a_wnel p_syl6bbr f1_sbcnel12g f4_sbcnel12g a_wcel f2_sbcnel12g f3_sbcnel12g a_wnel f0_sbcnel12g f1_sbcnel12g a_wsbc f2_sbcnel12g f3_sbcnel12g a_wcel a_wn f0_sbcnel12g f1_sbcnel12g a_wsbc f2_sbcnel12g f3_sbcnel12g a_wcel f0_sbcnel12g f1_sbcnel12g a_wsbc a_wn f0_sbcnel12g f1_sbcnel12g f2_sbcnel12g a_csb f0_sbcnel12g f1_sbcnel12g f3_sbcnel12g a_csb a_wnel p_3bitrd $.
$}

$(Distribute proper substitution through an inequality.  (Contributed by
     Andrew Salmon, 18-Jun-2011.) $)

${
	$v x A B C V  $.
	f0_sbcne12g $f set x $.
	f1_sbcne12g $f class A $.
	f2_sbcne12g $f class B $.
	f3_sbcne12g $f class C $.
	f4_sbcne12g $f class V $.
	p_sbcne12g $p |- ( A e. V -> ( [. A / x ]. B =/= C <-> [_ A / x ]_ B =/= [_ A / x ]_ C ) ) $= f2_sbcne12g f3_sbcne12g p_nne f2_sbcne12g f3_sbcne12g a_wne a_wn f2_sbcne12g f3_sbcne12g a_wceq f0_sbcne12g f1_sbcne12g p_sbcbii f2_sbcne12g f3_sbcne12g a_wne a_wn f0_sbcne12g f1_sbcne12g a_wsbc f2_sbcne12g f3_sbcne12g a_wceq f0_sbcne12g f1_sbcne12g a_wsbc a_wb f1_sbcne12g f4_sbcne12g a_wcel p_a1i f2_sbcne12g f3_sbcne12g a_wne f0_sbcne12g f1_sbcne12g f4_sbcne12g p_sbcng f0_sbcne12g f1_sbcne12g f2_sbcne12g f3_sbcne12g f4_sbcne12g p_sbceqg f0_sbcne12g f1_sbcne12g f2_sbcne12g a_csb f0_sbcne12g f1_sbcne12g f3_sbcne12g a_csb p_nne f1_sbcne12g f4_sbcne12g a_wcel f2_sbcne12g f3_sbcne12g a_wceq f0_sbcne12g f1_sbcne12g a_wsbc f0_sbcne12g f1_sbcne12g f2_sbcne12g a_csb f0_sbcne12g f1_sbcne12g f3_sbcne12g a_csb a_wceq f0_sbcne12g f1_sbcne12g f2_sbcne12g a_csb f0_sbcne12g f1_sbcne12g f3_sbcne12g a_csb a_wne a_wn p_syl6bbr f1_sbcne12g f4_sbcne12g a_wcel f2_sbcne12g f3_sbcne12g a_wne a_wn f0_sbcne12g f1_sbcne12g a_wsbc f2_sbcne12g f3_sbcne12g a_wceq f0_sbcne12g f1_sbcne12g a_wsbc f2_sbcne12g f3_sbcne12g a_wne f0_sbcne12g f1_sbcne12g a_wsbc a_wn f0_sbcne12g f1_sbcne12g f2_sbcne12g a_csb f0_sbcne12g f1_sbcne12g f3_sbcne12g a_csb a_wne a_wn p_3bitr3d f1_sbcne12g f4_sbcne12g a_wcel f2_sbcne12g f3_sbcne12g a_wne f0_sbcne12g f1_sbcne12g a_wsbc f0_sbcne12g f1_sbcne12g f2_sbcne12g a_csb f0_sbcne12g f1_sbcne12g f3_sbcne12g a_csb a_wne p_con4bid $.
$}

$(Move proper substitution in and out of a membership relation.  Note that
       the scope of ` [. A / x ]. ` is the wff ` B e. C ` , whereas the scope
       of ` [_ A / x ]_ ` is the class ` B ` .  (Contributed by NM,
       10-Nov-2005.) $)

${
	$v x A B C V  $.
	$d A  $.
	$d x C  $.
	$d V  $.
	f0_sbcel1g $f set x $.
	f1_sbcel1g $f class A $.
	f2_sbcel1g $f class B $.
	f3_sbcel1g $f class C $.
	f4_sbcel1g $f class V $.
	p_sbcel1g $p |- ( A e. V -> ( [. A / x ]. B e. C <-> [_ A / x ]_ B e. C ) ) $= f0_sbcel1g f1_sbcel1g f2_sbcel1g f3_sbcel1g f4_sbcel1g p_sbcel12g f0_sbcel1g f1_sbcel1g f3_sbcel1g f4_sbcel1g p_csbconstg f1_sbcel1g f4_sbcel1g a_wcel f0_sbcel1g f1_sbcel1g f3_sbcel1g a_csb f3_sbcel1g f0_sbcel1g f1_sbcel1g f2_sbcel1g a_csb p_eleq2d f1_sbcel1g f4_sbcel1g a_wcel f2_sbcel1g f3_sbcel1g a_wcel f0_sbcel1g f1_sbcel1g a_wsbc f0_sbcel1g f1_sbcel1g f2_sbcel1g a_csb f0_sbcel1g f1_sbcel1g f3_sbcel1g a_csb a_wcel f0_sbcel1g f1_sbcel1g f2_sbcel1g a_csb f3_sbcel1g a_wcel p_bitrd $.
$}

$(Move proper substitution to first argument of an equality.  (Contributed
       by NM, 30-Nov-2005.) $)

${
	$v x A B C V  $.
	$d A  $.
	$d x C  $.
	$d V  $.
	f0_sbceq1g $f set x $.
	f1_sbceq1g $f class A $.
	f2_sbceq1g $f class B $.
	f3_sbceq1g $f class C $.
	f4_sbceq1g $f class V $.
	p_sbceq1g $p |- ( A e. V -> ( [. A / x ]. B = C <-> [_ A / x ]_ B = C ) ) $= f0_sbceq1g f1_sbceq1g f2_sbceq1g f3_sbceq1g f4_sbceq1g p_sbceqg f0_sbceq1g f1_sbceq1g f3_sbceq1g f4_sbceq1g p_csbconstg f1_sbceq1g f4_sbceq1g a_wcel f0_sbceq1g f1_sbceq1g f3_sbceq1g a_csb f3_sbceq1g f0_sbceq1g f1_sbceq1g f2_sbceq1g a_csb p_eqeq2d f1_sbceq1g f4_sbceq1g a_wcel f2_sbceq1g f3_sbceq1g a_wceq f0_sbceq1g f1_sbceq1g a_wsbc f0_sbceq1g f1_sbceq1g f2_sbceq1g a_csb f0_sbceq1g f1_sbceq1g f3_sbceq1g a_csb a_wceq f0_sbceq1g f1_sbceq1g f2_sbceq1g a_csb f3_sbceq1g a_wceq p_bitrd $.
$}

$(Move proper substitution in and out of a membership relation.
       (Contributed by NM, 14-Nov-2005.) $)

${
	$v x A B C V  $.
	$d A  $.
	$d x B  $.
	$d V  $.
	f0_sbcel2g $f set x $.
	f1_sbcel2g $f class A $.
	f2_sbcel2g $f class B $.
	f3_sbcel2g $f class C $.
	f4_sbcel2g $f class V $.
	p_sbcel2g $p |- ( A e. V -> ( [. A / x ]. B e. C <-> B e. [_ A / x ]_ C ) ) $= f0_sbcel2g f1_sbcel2g f2_sbcel2g f3_sbcel2g f4_sbcel2g p_sbcel12g f0_sbcel2g f1_sbcel2g f2_sbcel2g f4_sbcel2g p_csbconstg f1_sbcel2g f4_sbcel2g a_wcel f0_sbcel2g f1_sbcel2g f2_sbcel2g a_csb f2_sbcel2g f0_sbcel2g f1_sbcel2g f3_sbcel2g a_csb p_eleq1d f1_sbcel2g f4_sbcel2g a_wcel f2_sbcel2g f3_sbcel2g a_wcel f0_sbcel2g f1_sbcel2g a_wsbc f0_sbcel2g f1_sbcel2g f2_sbcel2g a_csb f0_sbcel2g f1_sbcel2g f3_sbcel2g a_csb a_wcel f2_sbcel2g f0_sbcel2g f1_sbcel2g f3_sbcel2g a_csb a_wcel p_bitrd $.
$}

$(Move proper substitution to second argument of an equality.
       (Contributed by NM, 30-Nov-2005.) $)

${
	$v x A B C V  $.
	$d A  $.
	$d x B  $.
	$d V  $.
	f0_sbceq2g $f set x $.
	f1_sbceq2g $f class A $.
	f2_sbceq2g $f class B $.
	f3_sbceq2g $f class C $.
	f4_sbceq2g $f class V $.
	p_sbceq2g $p |- ( A e. V -> ( [. A / x ]. B = C <-> B = [_ A / x ]_ C ) ) $= f0_sbceq2g f1_sbceq2g f2_sbceq2g f3_sbceq2g f4_sbceq2g p_sbceqg f0_sbceq2g f1_sbceq2g f2_sbceq2g f4_sbceq2g p_csbconstg f1_sbceq2g f4_sbceq2g a_wcel f0_sbceq2g f1_sbceq2g f2_sbceq2g a_csb f2_sbceq2g f0_sbceq2g f1_sbceq2g f3_sbceq2g a_csb p_eqeq1d f1_sbceq2g f4_sbceq2g a_wcel f2_sbceq2g f3_sbceq2g a_wceq f0_sbceq2g f1_sbceq2g a_wsbc f0_sbceq2g f1_sbceq2g f2_sbceq2g a_csb f0_sbceq2g f1_sbceq2g f3_sbceq2g a_csb a_wceq f2_sbceq2g f0_sbceq2g f1_sbceq2g f3_sbceq2g a_csb a_wceq p_bitrd $.
$}

$(Commutative law for double substitution into a class.  (Contributed by
       NM, 14-Nov-2005.) $)

${
	$v x y A B C V W  $.
	$d y z A  $.
	$d x z B  $.
	$d z C  $.
	$d x y  $.
	f0_csbcomg $f set x $.
	f1_csbcomg $f set y $.
	f2_csbcomg $f class A $.
	f3_csbcomg $f class B $.
	f4_csbcomg $f class C $.
	f5_csbcomg $f class V $.
	f6_csbcomg $f class W $.
	i0_csbcomg $f set z $.
	p_csbcomg $p |- ( ( A e. V /\ B e. W ) -> [_ A / x ]_ [_ B / y ]_ C = [_ B / y ]_ [_ A / x ]_ C ) $= f2_csbcomg f5_csbcomg p_elex f3_csbcomg f6_csbcomg p_elex i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f0_csbcomg f1_csbcomg f2_csbcomg f3_csbcomg p_sbccom i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f1_csbcomg f3_csbcomg a_wsbc f0_csbcomg f2_csbcomg a_wsbc i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f0_csbcomg f2_csbcomg a_wsbc f1_csbcomg f3_csbcomg a_wsbc a_wb f2_csbcomg a_cvv a_wcel f3_csbcomg a_cvv a_wcel a_wa p_a1i f1_csbcomg f3_csbcomg i0_csbcomg a_sup_set_class f4_csbcomg a_cvv p_sbcel2g f3_csbcomg a_cvv a_wcel i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f1_csbcomg f3_csbcomg a_wsbc i0_csbcomg a_sup_set_class f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_wcel f0_csbcomg f2_csbcomg p_sbcbidv f3_csbcomg a_cvv a_wcel i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f1_csbcomg f3_csbcomg a_wsbc f0_csbcomg f2_csbcomg a_wsbc i0_csbcomg a_sup_set_class f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_wcel f0_csbcomg f2_csbcomg a_wsbc a_wb f2_csbcomg a_cvv a_wcel p_adantl f0_csbcomg f2_csbcomg i0_csbcomg a_sup_set_class f4_csbcomg a_cvv p_sbcel2g f2_csbcomg a_cvv a_wcel i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f0_csbcomg f2_csbcomg a_wsbc i0_csbcomg a_sup_set_class f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_wcel f1_csbcomg f3_csbcomg p_sbcbidv f2_csbcomg a_cvv a_wcel i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f0_csbcomg f2_csbcomg a_wsbc f1_csbcomg f3_csbcomg a_wsbc i0_csbcomg a_sup_set_class f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_wcel f1_csbcomg f3_csbcomg a_wsbc a_wb f3_csbcomg a_cvv a_wcel p_adantr f2_csbcomg a_cvv a_wcel f3_csbcomg a_cvv a_wcel a_wa i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f1_csbcomg f3_csbcomg a_wsbc f0_csbcomg f2_csbcomg a_wsbc i0_csbcomg a_sup_set_class f4_csbcomg a_wcel f0_csbcomg f2_csbcomg a_wsbc f1_csbcomg f3_csbcomg a_wsbc i0_csbcomg a_sup_set_class f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_wcel f0_csbcomg f2_csbcomg a_wsbc i0_csbcomg a_sup_set_class f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_wcel f1_csbcomg f3_csbcomg a_wsbc p_3bitr3d f0_csbcomg f2_csbcomg i0_csbcomg a_sup_set_class f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_cvv p_sbcel2g f2_csbcomg a_cvv a_wcel i0_csbcomg a_sup_set_class f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_wcel f0_csbcomg f2_csbcomg a_wsbc i0_csbcomg a_sup_set_class f0_csbcomg f2_csbcomg f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_csb a_wcel a_wb f3_csbcomg a_cvv a_wcel p_adantr f1_csbcomg f3_csbcomg i0_csbcomg a_sup_set_class f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_cvv p_sbcel2g f3_csbcomg a_cvv a_wcel i0_csbcomg a_sup_set_class f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_wcel f1_csbcomg f3_csbcomg a_wsbc i0_csbcomg a_sup_set_class f1_csbcomg f3_csbcomg f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_csb a_wcel a_wb f2_csbcomg a_cvv a_wcel p_adantl f2_csbcomg a_cvv a_wcel f3_csbcomg a_cvv a_wcel a_wa i0_csbcomg a_sup_set_class f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_wcel f0_csbcomg f2_csbcomg a_wsbc i0_csbcomg a_sup_set_class f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_wcel f1_csbcomg f3_csbcomg a_wsbc i0_csbcomg a_sup_set_class f0_csbcomg f2_csbcomg f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_csb a_wcel i0_csbcomg a_sup_set_class f1_csbcomg f3_csbcomg f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_csb a_wcel p_3bitr3d f2_csbcomg a_cvv a_wcel f3_csbcomg a_cvv a_wcel a_wa i0_csbcomg f0_csbcomg f2_csbcomg f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_csb f1_csbcomg f3_csbcomg f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_csb p_eqrdv f2_csbcomg f5_csbcomg a_wcel f2_csbcomg a_cvv a_wcel f3_csbcomg a_cvv a_wcel f0_csbcomg f2_csbcomg f1_csbcomg f3_csbcomg f4_csbcomg a_csb a_csb f1_csbcomg f3_csbcomg f0_csbcomg f2_csbcomg f4_csbcomg a_csb a_csb a_wceq f3_csbcomg f6_csbcomg a_wcel p_syl2an $.
$}

$(Formula-building deduction rule for class substitution.  (Contributed by
       NM, 22-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)

${
	$v ph x A B C  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	$d y ph  $.
	f0_csbeq2d $f wff ph $.
	f1_csbeq2d $f set x $.
	f2_csbeq2d $f class A $.
	f3_csbeq2d $f class B $.
	f4_csbeq2d $f class C $.
	i0_csbeq2d $f set y $.
	e0_csbeq2d $e |- F/ x ph $.
	e1_csbeq2d $e |- ( ph -> B = C ) $.
	p_csbeq2d $p |- ( ph -> [_ A / x ]_ B = [_ A / x ]_ C ) $= e0_csbeq2d e1_csbeq2d f0_csbeq2d f3_csbeq2d f4_csbeq2d i0_csbeq2d a_sup_set_class p_eleq2d f0_csbeq2d i0_csbeq2d a_sup_set_class f3_csbeq2d a_wcel i0_csbeq2d a_sup_set_class f4_csbeq2d a_wcel f1_csbeq2d f2_csbeq2d p_sbcbid f0_csbeq2d i0_csbeq2d a_sup_set_class f3_csbeq2d a_wcel f1_csbeq2d f2_csbeq2d a_wsbc i0_csbeq2d a_sup_set_class f4_csbeq2d a_wcel f1_csbeq2d f2_csbeq2d a_wsbc i0_csbeq2d p_abbidv f1_csbeq2d i0_csbeq2d f2_csbeq2d f3_csbeq2d a_df-csb f1_csbeq2d i0_csbeq2d f2_csbeq2d f4_csbeq2d a_df-csb f0_csbeq2d i0_csbeq2d a_sup_set_class f3_csbeq2d a_wcel f1_csbeq2d f2_csbeq2d a_wsbc i0_csbeq2d a_cab i0_csbeq2d a_sup_set_class f4_csbeq2d a_wcel f1_csbeq2d f2_csbeq2d a_wsbc i0_csbeq2d a_cab f1_csbeq2d f2_csbeq2d f3_csbeq2d a_csb f1_csbeq2d f2_csbeq2d f4_csbeq2d a_csb p_3eqtr4g $.
$}

$(Formula-building deduction rule for class substitution.  (Contributed by
       NM, 10-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)

${
	$v ph x A B C  $.
	$d x ph  $.
	f0_csbeq2dv $f wff ph $.
	f1_csbeq2dv $f set x $.
	f2_csbeq2dv $f class A $.
	f3_csbeq2dv $f class B $.
	f4_csbeq2dv $f class C $.
	e0_csbeq2dv $e |- ( ph -> B = C ) $.
	p_csbeq2dv $p |- ( ph -> [_ A / x ]_ B = [_ A / x ]_ C ) $= f0_csbeq2dv f1_csbeq2dv p_nfv e0_csbeq2dv f0_csbeq2dv f1_csbeq2dv f2_csbeq2dv f3_csbeq2dv f4_csbeq2dv p_csbeq2d $.
$}

$(Formula-building inference rule for class substitution.  (Contributed by
       NM, 10-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)

${
	$v x A B C  $.
	f0_csbeq2i $f set x $.
	f1_csbeq2i $f class A $.
	f2_csbeq2i $f class B $.
	f3_csbeq2i $f class C $.
	e0_csbeq2i $e |- B = C $.
	p_csbeq2i $p |- [_ A / x ]_ B = [_ A / x ]_ C $= e0_csbeq2i f2_csbeq2i f3_csbeq2i a_wceq a_wtru p_a1i a_wtru f0_csbeq2i f1_csbeq2i f2_csbeq2i f3_csbeq2i p_csbeq2dv f0_csbeq2i f1_csbeq2i f2_csbeq2i a_csb f0_csbeq2i f1_csbeq2i f3_csbeq2i a_csb a_wceq p_trud $.
$}

$(The proper substitution of a class for set variable results in the class
       (if the class exists).  (Contributed by NM, 10-Nov-2005.) $)

${
	$v x A V  $.
	$d y z A  $.
	$d x y z  $.
	f0_csbvarg $f set x $.
	f1_csbvarg $f class A $.
	f2_csbvarg $f class V $.
	i0_csbvarg $f set y $.
	i1_csbvarg $f set z $.
	p_csbvarg $p |- ( A e. V -> [_ A / x ]_ x = A ) $= f1_csbvarg f2_csbvarg p_elex i0_csbvarg p_vex f0_csbvarg i1_csbvarg i0_csbvarg a_sup_set_class f0_csbvarg a_sup_set_class a_df-csb f0_csbvarg i1_csbvarg a_sup_set_class i0_csbvarg a_sup_set_class a_cvv p_sbcel2gv i0_csbvarg a_sup_set_class a_cvv a_wcel i1_csbvarg a_sup_set_class f0_csbvarg a_sup_set_class a_wcel f0_csbvarg i0_csbvarg a_sup_set_class a_wsbc i1_csbvarg i0_csbvarg a_sup_set_class p_abbi1dv i0_csbvarg a_sup_set_class a_cvv a_wcel f0_csbvarg i0_csbvarg a_sup_set_class f0_csbvarg a_sup_set_class a_csb i1_csbvarg a_sup_set_class f0_csbvarg a_sup_set_class a_wcel f0_csbvarg i0_csbvarg a_sup_set_class a_wsbc i1_csbvarg a_cab i0_csbvarg a_sup_set_class p_syl5eq i0_csbvarg a_sup_set_class a_cvv a_wcel f0_csbvarg i0_csbvarg a_sup_set_class f0_csbvarg a_sup_set_class a_csb i0_csbvarg a_sup_set_class a_wceq a_ax-mp i0_csbvarg f1_csbvarg f0_csbvarg i0_csbvarg a_sup_set_class f0_csbvarg a_sup_set_class a_csb i0_csbvarg a_sup_set_class p_csbeq2i f0_csbvarg i0_csbvarg f1_csbvarg f0_csbvarg a_sup_set_class p_csbco i0_csbvarg i1_csbvarg f1_csbvarg i0_csbvarg a_sup_set_class a_df-csb i0_csbvarg f1_csbvarg f0_csbvarg i0_csbvarg a_sup_set_class f0_csbvarg a_sup_set_class a_csb a_csb i0_csbvarg f1_csbvarg i0_csbvarg a_sup_set_class a_csb f0_csbvarg f1_csbvarg f0_csbvarg a_sup_set_class a_csb i1_csbvarg a_sup_set_class i0_csbvarg a_sup_set_class a_wcel i0_csbvarg f1_csbvarg a_wsbc i1_csbvarg a_cab p_3eqtr3i i0_csbvarg i1_csbvarg a_sup_set_class f1_csbvarg a_cvv p_sbcel2gv f1_csbvarg a_cvv a_wcel i1_csbvarg a_sup_set_class i0_csbvarg a_sup_set_class a_wcel i0_csbvarg f1_csbvarg a_wsbc i1_csbvarg f1_csbvarg p_abbi1dv f1_csbvarg a_cvv a_wcel f0_csbvarg f1_csbvarg f0_csbvarg a_sup_set_class a_csb i1_csbvarg a_sup_set_class i0_csbvarg a_sup_set_class a_wcel i0_csbvarg f1_csbvarg a_wsbc i1_csbvarg a_cab f1_csbvarg p_syl5eq f1_csbvarg f2_csbvarg a_wcel f1_csbvarg a_cvv a_wcel f0_csbvarg f1_csbvarg f0_csbvarg a_sup_set_class a_csb f1_csbvarg a_wceq p_syl $.
$}

$(Substitution into a wff expressed in terms of substitution into a
       class.  (Contributed by NM, 15-Aug-2007.) $)

${
	$v ph x y A V  $.
	$d x y  $.
	f0_sbccsbg $f wff ph $.
	f1_sbccsbg $f set x $.
	f2_sbccsbg $f set y $.
	f3_sbccsbg $f class A $.
	f4_sbccsbg $f class V $.
	p_sbccsbg $p |- ( A e. V -> ( [. A / x ]. ph <-> y e. [_ A / x ]_ { y | ph } ) ) $= f0_sbccsbg f2_sbccsbg p_abid f2_sbccsbg a_sup_set_class f0_sbccsbg f2_sbccsbg a_cab a_wcel f0_sbccsbg f1_sbccsbg f3_sbccsbg p_sbcbii f1_sbccsbg f3_sbccsbg f2_sbccsbg a_sup_set_class f0_sbccsbg f2_sbccsbg a_cab f4_sbccsbg p_sbcel2g f0_sbccsbg f1_sbccsbg f3_sbccsbg a_wsbc f2_sbccsbg a_sup_set_class f0_sbccsbg f2_sbccsbg a_cab a_wcel f1_sbccsbg f3_sbccsbg a_wsbc f3_sbccsbg f4_sbccsbg a_wcel f2_sbccsbg a_sup_set_class f1_sbccsbg f3_sbccsbg f0_sbccsbg f2_sbccsbg a_cab a_csb a_wcel p_syl5bbr $.
$}

$(Substitution into a wff expressed in using substitution into a class.
     (Contributed by NM, 27-Nov-2005.) $)

${
	$v ph x A V  $.
	f0_sbccsb2g $f wff ph $.
	f1_sbccsb2g $f set x $.
	f2_sbccsb2g $f class A $.
	f3_sbccsb2g $f class V $.
	p_sbccsb2g $p |- ( A e. V -> ( [. A / x ]. ph <-> A e. [_ A / x ]_ { x | ph } ) ) $= f0_sbccsb2g f1_sbccsb2g p_abid f1_sbccsb2g a_sup_set_class f0_sbccsb2g f1_sbccsb2g a_cab a_wcel f0_sbccsb2g f1_sbccsb2g f2_sbccsb2g p_sbcbii f1_sbccsb2g f2_sbccsb2g f1_sbccsb2g a_sup_set_class f0_sbccsb2g f1_sbccsb2g a_cab f3_sbccsb2g p_sbcel12g f1_sbccsb2g f2_sbccsb2g f3_sbccsb2g p_csbvarg f2_sbccsb2g f3_sbccsb2g a_wcel f1_sbccsb2g f2_sbccsb2g f1_sbccsb2g a_sup_set_class a_csb f2_sbccsb2g f1_sbccsb2g f2_sbccsb2g f0_sbccsb2g f1_sbccsb2g a_cab a_csb p_eleq1d f2_sbccsb2g f3_sbccsb2g a_wcel f1_sbccsb2g a_sup_set_class f0_sbccsb2g f1_sbccsb2g a_cab a_wcel f1_sbccsb2g f2_sbccsb2g a_wsbc f1_sbccsb2g f2_sbccsb2g f1_sbccsb2g a_sup_set_class a_csb f1_sbccsb2g f2_sbccsb2g f0_sbccsb2g f1_sbccsb2g a_cab a_csb a_wcel f2_sbccsb2g f1_sbccsb2g f2_sbccsb2g f0_sbccsb2g f1_sbccsb2g a_cab a_csb a_wcel p_bitrd f0_sbccsb2g f1_sbccsb2g f2_sbccsb2g a_wsbc f1_sbccsb2g a_sup_set_class f0_sbccsb2g f1_sbccsb2g a_cab a_wcel f1_sbccsb2g f2_sbccsb2g a_wsbc f2_sbccsb2g f3_sbccsb2g a_wcel f2_sbccsb2g f1_sbccsb2g f2_sbccsb2g f0_sbccsb2g f1_sbccsb2g a_cab a_csb a_wcel p_syl5bbr $.
$}

$(Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph x A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y ph  $.
	f0_nfcsb1d $f wff ph $.
	f1_nfcsb1d $f set x $.
	f2_nfcsb1d $f class A $.
	f3_nfcsb1d $f class B $.
	i0_nfcsb1d $f set y $.
	e0_nfcsb1d $e |- ( ph -> F/_ x A ) $.
	p_nfcsb1d $p |- ( ph -> F/_ x [_ A / x ]_ B ) $= f1_nfcsb1d i0_nfcsb1d f2_nfcsb1d f3_nfcsb1d a_df-csb f0_nfcsb1d i0_nfcsb1d p_nfv e0_nfcsb1d f0_nfcsb1d i0_nfcsb1d a_sup_set_class f3_nfcsb1d a_wcel f1_nfcsb1d f2_nfcsb1d p_nfsbc1d f0_nfcsb1d i0_nfcsb1d a_sup_set_class f3_nfcsb1d a_wcel f1_nfcsb1d f2_nfcsb1d a_wsbc f1_nfcsb1d i0_nfcsb1d p_nfabd f0_nfcsb1d f1_nfcsb1d f1_nfcsb1d f2_nfcsb1d f3_nfcsb1d a_csb i0_nfcsb1d a_sup_set_class f3_nfcsb1d a_wcel f1_nfcsb1d f2_nfcsb1d a_wsbc i0_nfcsb1d a_cab p_nfcxfrd $.
$}

$(Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)

${
	$v x A B  $.
	$d A  $.
	$d B  $.
	$d x  $.
	f0_nfcsb1 $f set x $.
	f1_nfcsb1 $f class A $.
	f2_nfcsb1 $f class B $.
	e0_nfcsb1 $e |- F/_ x A $.
	p_nfcsb1 $p |- F/_ x [_ A / x ]_ B $= e0_nfcsb1 f0_nfcsb1 f1_nfcsb1 a_wnfc a_wtru p_a1i a_wtru f0_nfcsb1 f1_nfcsb1 f2_nfcsb1 p_nfcsb1d f0_nfcsb1 f0_nfcsb1 f1_nfcsb1 f2_nfcsb1 a_csb a_wnfc p_trud $.
$}

$(Bound-variable hypothesis builder for substitution into a class.
       (Contributed by NM, 17-Aug-2006.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)

${
	$v x A B  $.
	$d x A  $.
	f0_nfcsb1v $f set x $.
	f1_nfcsb1v $f class A $.
	f2_nfcsb1v $f class B $.
	p_nfcsb1v $p |- F/_ x [_ A / x ]_ B $= f0_nfcsb1v f1_nfcsb1v p_nfcv f0_nfcsb1v f1_nfcsb1v f2_nfcsb1v p_nfcsb1 $.
$}

$(Deduction version of ~ nfcsb .  (Contributed by NM, 21-Nov-2005.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)

${
	$v ph x y A B  $.
	$d x z  $.
	$d y z  $.
	$d z A  $.
	$d z B  $.
	$d z ph  $.
	f0_nfcsbd $f wff ph $.
	f1_nfcsbd $f set x $.
	f2_nfcsbd $f set y $.
	f3_nfcsbd $f class A $.
	f4_nfcsbd $f class B $.
	i0_nfcsbd $f set z $.
	e0_nfcsbd $e |- F/ y ph $.
	e1_nfcsbd $e |- ( ph -> F/_ x A ) $.
	e2_nfcsbd $e |- ( ph -> F/_ x B ) $.
	p_nfcsbd $p |- ( ph -> F/_ x [_ A / y ]_ B ) $= f2_nfcsbd i0_nfcsbd f3_nfcsbd f4_nfcsbd a_df-csb f0_nfcsbd i0_nfcsbd p_nfv e0_nfcsbd e1_nfcsbd e2_nfcsbd f0_nfcsbd f1_nfcsbd i0_nfcsbd f4_nfcsbd p_nfcrd f0_nfcsbd i0_nfcsbd a_sup_set_class f4_nfcsbd a_wcel f1_nfcsbd f2_nfcsbd f3_nfcsbd p_nfsbcd f0_nfcsbd i0_nfcsbd a_sup_set_class f4_nfcsbd a_wcel f2_nfcsbd f3_nfcsbd a_wsbc f1_nfcsbd i0_nfcsbd p_nfabd f0_nfcsbd f1_nfcsbd f2_nfcsbd f3_nfcsbd f4_nfcsbd a_csb i0_nfcsbd a_sup_set_class f4_nfcsbd a_wcel f2_nfcsbd f3_nfcsbd a_wsbc i0_nfcsbd a_cab p_nfcxfrd $.
$}

$(Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)

${
	$v x y A B  $.
	f0_nfcsb $f set x $.
	f1_nfcsb $f set y $.
	f2_nfcsb $f class A $.
	f3_nfcsb $f class B $.
	e0_nfcsb $e |- F/_ x A $.
	e1_nfcsb $e |- F/_ x B $.
	p_nfcsb $p |- F/_ x [_ A / y ]_ B $= f1_nfcsb p_nftru e0_nfcsb f0_nfcsb f2_nfcsb a_wnfc a_wtru p_a1i e1_nfcsb f0_nfcsb f3_nfcsb a_wnfc a_wtru p_a1i a_wtru f0_nfcsb f1_nfcsb f2_nfcsb f3_nfcsb p_nfcsbd f0_nfcsb f1_nfcsb f2_nfcsb f3_nfcsb a_csb a_wnfc p_trud $.
$}

$(Introduce an explicit substitution into an implicit substitution
       hypothesis.  See ~ sbhypf for class substitution version.  (Contributed
       by NM, 19-Dec-2008.) $)

${
	$v x y A B C  $.
	$d x y  $.
	f0_csbhypf $f set x $.
	f1_csbhypf $f set y $.
	f2_csbhypf $f class A $.
	f3_csbhypf $f class B $.
	f4_csbhypf $f class C $.
	e0_csbhypf $e |- F/_ x A $.
	e1_csbhypf $e |- F/_ x C $.
	e2_csbhypf $e |- ( x = A -> B = C ) $.
	p_csbhypf $p |- ( y = A -> [_ y / x ]_ B = C ) $= e0_csbhypf f0_csbhypf f1_csbhypf a_sup_set_class f2_csbhypf p_nfeq2 f0_csbhypf f1_csbhypf a_sup_set_class f3_csbhypf p_nfcsb1v e1_csbhypf f0_csbhypf f0_csbhypf f1_csbhypf a_sup_set_class f3_csbhypf a_csb f4_csbhypf p_nfeq f1_csbhypf a_sup_set_class f2_csbhypf a_wceq f0_csbhypf f1_csbhypf a_sup_set_class f3_csbhypf a_csb f4_csbhypf a_wceq f0_csbhypf p_nfim f0_csbhypf a_sup_set_class f1_csbhypf a_sup_set_class f2_csbhypf p_eqeq1 f0_csbhypf f1_csbhypf a_sup_set_class f3_csbhypf p_csbeq1a f0_csbhypf a_sup_set_class f1_csbhypf a_sup_set_class a_wceq f3_csbhypf f0_csbhypf f1_csbhypf a_sup_set_class f3_csbhypf a_csb f4_csbhypf p_eqeq1d f0_csbhypf a_sup_set_class f1_csbhypf a_sup_set_class a_wceq f0_csbhypf a_sup_set_class f2_csbhypf a_wceq f1_csbhypf a_sup_set_class f2_csbhypf a_wceq f3_csbhypf f4_csbhypf a_wceq f0_csbhypf f1_csbhypf a_sup_set_class f3_csbhypf a_csb f4_csbhypf a_wceq p_imbi12d e2_csbhypf f0_csbhypf a_sup_set_class f2_csbhypf a_wceq f3_csbhypf f4_csbhypf a_wceq a_wi f1_csbhypf a_sup_set_class f2_csbhypf a_wceq f0_csbhypf f1_csbhypf a_sup_set_class f3_csbhypf a_csb f4_csbhypf a_wceq a_wi f0_csbhypf f1_csbhypf p_chvar $.
$}

$(Conversion of implicit substitution to explicit substitution into a
       class.  (Closed theorem version of ~ csbiegf .)  (Contributed by NM,
       11-Nov-2005.) $)

${
	$v x A B C V  $.
	$d x A  $.
	f0_csbiebt $f set x $.
	f1_csbiebt $f class A $.
	f2_csbiebt $f class B $.
	f3_csbiebt $f class C $.
	f4_csbiebt $f class V $.
	p_csbiebt $p |- ( ( A e. V /\ F/_ x C ) -> ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) ) $= f1_csbiebt f4_csbiebt p_elex f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt f1_csbiebt a_cvv p_spsbc f1_csbiebt a_cvv a_wcel f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt a_wal f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt f1_csbiebt a_wsbc a_wi f0_csbiebt f3_csbiebt a_wnfc p_adantr f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc p_simpl f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq p_biimt f0_csbiebt f1_csbiebt f2_csbiebt p_csbeq1a f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt p_eqeq1d f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq p_bitr3d f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq a_wb f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc a_wa p_adantl f1_csbiebt a_cvv a_wcel f0_csbiebt p_nfv f0_csbiebt f3_csbiebt p_nfnfc1 f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc f0_csbiebt p_nfan f0_csbiebt f1_csbiebt f2_csbiebt p_nfcsb1v f0_csbiebt f0_csbiebt f1_csbiebt f2_csbiebt a_csb a_wnfc f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc a_wa p_a1i f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc p_simpr f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc a_wa f0_csbiebt f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt p_nfeqd f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc a_wa f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq f0_csbiebt f1_csbiebt a_cvv p_sbciedf f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc a_wa f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt a_wal f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt f1_csbiebt a_wsbc f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq p_sylibd f0_csbiebt f3_csbiebt p_nfnfc1 f0_csbiebt f1_csbiebt f2_csbiebt p_nfcsb1v f0_csbiebt f0_csbiebt f1_csbiebt f2_csbiebt a_csb a_wnfc f0_csbiebt f3_csbiebt a_wnfc p_a1i f0_csbiebt f3_csbiebt a_wnfc p_id f0_csbiebt f3_csbiebt a_wnfc f0_csbiebt f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt p_nfeqd f0_csbiebt f3_csbiebt a_wnfc f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq f0_csbiebt p_nfan1 f0_csbiebt f1_csbiebt f2_csbiebt p_csbeq1a f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt p_eqeq1d f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq p_biimprcd f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt f3_csbiebt a_wnfc p_adantl f0_csbiebt f3_csbiebt a_wnfc f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq a_wa f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt p_alrimi f0_csbiebt f3_csbiebt a_wnfc f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt a_wal p_ex f0_csbiebt f3_csbiebt a_wnfc f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt a_wal a_wi f1_csbiebt a_cvv a_wcel p_adantl f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc a_wa f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt a_wal f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq p_impbid f1_csbiebt f4_csbiebt a_wcel f1_csbiebt a_cvv a_wcel f0_csbiebt f3_csbiebt a_wnfc f0_csbiebt a_sup_set_class f1_csbiebt a_wceq f2_csbiebt f3_csbiebt a_wceq a_wi f0_csbiebt a_wal f0_csbiebt f1_csbiebt f2_csbiebt a_csb f3_csbiebt a_wceq a_wb p_sylan $.
$}

$(Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph x A B C V  $.
	$d x A  $.
	f0_csbiedf $f wff ph $.
	f1_csbiedf $f set x $.
	f2_csbiedf $f class A $.
	f3_csbiedf $f class B $.
	f4_csbiedf $f class C $.
	f5_csbiedf $f class V $.
	e0_csbiedf $e |- F/ x ph $.
	e1_csbiedf $e |- ( ph -> F/_ x C ) $.
	e2_csbiedf $e |- ( ph -> A e. V ) $.
	e3_csbiedf $e |- ( ( ph /\ x = A ) -> B = C ) $.
	p_csbiedf $p |- ( ph -> [_ A / x ]_ B = C ) $= e0_csbiedf e3_csbiedf f0_csbiedf f1_csbiedf a_sup_set_class f2_csbiedf a_wceq f3_csbiedf f4_csbiedf a_wceq p_ex f0_csbiedf f1_csbiedf a_sup_set_class f2_csbiedf a_wceq f3_csbiedf f4_csbiedf a_wceq a_wi f1_csbiedf p_alrimi e2_csbiedf e1_csbiedf f1_csbiedf f2_csbiedf f3_csbiedf f4_csbiedf f5_csbiedf p_csbiebt f0_csbiedf f2_csbiedf f5_csbiedf a_wcel f1_csbiedf f4_csbiedf a_wnfc f1_csbiedf a_sup_set_class f2_csbiedf a_wceq f3_csbiedf f4_csbiedf a_wceq a_wi f1_csbiedf a_wal f1_csbiedf f2_csbiedf f3_csbiedf a_csb f4_csbiedf a_wceq a_wb p_syl2anc f0_csbiedf f1_csbiedf a_sup_set_class f2_csbiedf a_wceq f3_csbiedf f4_csbiedf a_wceq a_wi f1_csbiedf a_wal f1_csbiedf f2_csbiedf f3_csbiedf a_csb f4_csbiedf a_wceq p_mpbid $.
$}

$(Bidirectional conversion between an implicit class substitution
       hypothesis ` x = A -> B = C ` and its explicit substitution equivalent.
       (Contributed by NM, 2-Mar-2008.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d B  $.
	$d C  $.
	$d x  $.
	f0_csbieb $f set x $.
	f1_csbieb $f class A $.
	f2_csbieb $f class B $.
	f3_csbieb $f class C $.
	e0_csbieb $e |- A e. _V $.
	e1_csbieb $e |- F/_ x C $.
	p_csbieb $p |- ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) $= e0_csbieb e1_csbieb f0_csbieb f1_csbieb f2_csbieb f3_csbieb a_cvv p_csbiebt f1_csbieb a_cvv a_wcel f0_csbieb f3_csbieb a_wnfc f0_csbieb a_sup_set_class f1_csbieb a_wceq f2_csbieb f3_csbieb a_wceq a_wi f0_csbieb a_wal f0_csbieb f1_csbieb f2_csbieb a_csb f3_csbieb a_wceq a_wb p_mp2an $.
$}

$(Bidirectional conversion between an implicit class substitution
       hypothesis ` x = A -> B = C ` and its explicit substitution equivalent.
       (Contributed by NM, 24-Mar-2013.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)

${
	$v x A B C V  $.
	$d a x A  $.
	$d a B  $.
	$d a C  $.
	$d x  $.
	f0_csbiebg $f set x $.
	f1_csbiebg $f class A $.
	f2_csbiebg $f class B $.
	f3_csbiebg $f class C $.
	f4_csbiebg $f class V $.
	i0_csbiebg $f set a $.
	e0_csbiebg $e |- F/_ x C $.
	p_csbiebg $p |- ( A e. V -> ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) ) $= i0_csbiebg a_sup_set_class f1_csbiebg f0_csbiebg a_sup_set_class p_eqeq2 i0_csbiebg a_sup_set_class f1_csbiebg a_wceq f0_csbiebg a_sup_set_class i0_csbiebg a_sup_set_class a_wceq f0_csbiebg a_sup_set_class f1_csbiebg a_wceq f2_csbiebg f3_csbiebg a_wceq p_imbi1d i0_csbiebg a_sup_set_class f1_csbiebg a_wceq f0_csbiebg a_sup_set_class i0_csbiebg a_sup_set_class a_wceq f2_csbiebg f3_csbiebg a_wceq a_wi f0_csbiebg a_sup_set_class f1_csbiebg a_wceq f2_csbiebg f3_csbiebg a_wceq a_wi f0_csbiebg p_albidv f0_csbiebg i0_csbiebg a_sup_set_class f1_csbiebg f2_csbiebg p_csbeq1 i0_csbiebg a_sup_set_class f1_csbiebg a_wceq f0_csbiebg i0_csbiebg a_sup_set_class f2_csbiebg a_csb f0_csbiebg f1_csbiebg f2_csbiebg a_csb f3_csbiebg p_eqeq1d i0_csbiebg p_vex e0_csbiebg f0_csbiebg i0_csbiebg a_sup_set_class f2_csbiebg f3_csbiebg p_csbieb f0_csbiebg a_sup_set_class i0_csbiebg a_sup_set_class a_wceq f2_csbiebg f3_csbiebg a_wceq a_wi f0_csbiebg a_wal f0_csbiebg i0_csbiebg a_sup_set_class f2_csbiebg a_csb f3_csbiebg a_wceq f0_csbiebg a_sup_set_class f1_csbiebg a_wceq f2_csbiebg f3_csbiebg a_wceq a_wi f0_csbiebg a_wal f0_csbiebg f1_csbiebg f2_csbiebg a_csb f3_csbiebg a_wceq i0_csbiebg f1_csbiebg f4_csbiebg p_vtoclbg $.
$}

$(Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 11-Nov-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) $)

${
	$v x A B C V  $.
	$d x A  $.
	$d C  $.
	$d x V  $.
	f0_csbiegf $f set x $.
	f1_csbiegf $f class A $.
	f2_csbiegf $f class B $.
	f3_csbiegf $f class C $.
	f4_csbiegf $f class V $.
	e0_csbiegf $e |- ( A e. V -> F/_ x C ) $.
	e1_csbiegf $e |- ( x = A -> B = C ) $.
	p_csbiegf $p |- ( A e. V -> [_ A / x ]_ B = C ) $= e1_csbiegf f0_csbiegf a_sup_set_class f1_csbiegf a_wceq f2_csbiegf f3_csbiegf a_wceq a_wi f0_csbiegf a_ax-gen e0_csbiegf f0_csbiegf f1_csbiegf f2_csbiegf f3_csbiegf f4_csbiegf p_csbiebt f1_csbiegf f4_csbiegf a_wcel f0_csbiegf f3_csbiegf a_wnfc f0_csbiegf a_sup_set_class f1_csbiegf a_wceq f2_csbiegf f3_csbiegf a_wceq a_wi f0_csbiegf a_wal f0_csbiegf f1_csbiegf f2_csbiegf a_csb f3_csbiegf a_wceq a_wb p_mpdan f1_csbiegf f4_csbiegf a_wcel f0_csbiegf a_sup_set_class f1_csbiegf a_wceq f2_csbiegf f3_csbiegf a_wceq a_wi f0_csbiegf a_wal f0_csbiegf f1_csbiegf f2_csbiegf a_csb f3_csbiegf a_wceq p_mpbii $.
$}

$(Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 26-Nov-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d C  $.
	$d x  $.
	f0_csbief $f set x $.
	f1_csbief $f class A $.
	f2_csbief $f class B $.
	f3_csbief $f class C $.
	e0_csbief $e |- A e. _V $.
	e1_csbief $e |- F/_ x C $.
	e2_csbief $e |- ( x = A -> B = C ) $.
	p_csbief $p |- [_ A / x ]_ B = C $= e0_csbief e1_csbief f0_csbief f3_csbief a_wnfc f1_csbief a_cvv a_wcel p_a1i e2_csbief f0_csbief f1_csbief f2_csbief f3_csbief a_cvv p_csbiegf f1_csbief a_cvv a_wcel f0_csbief f1_csbief f2_csbief a_csb f3_csbief a_wceq a_ax-mp $.
$}

$(Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by Mario Carneiro, 2-Dec-2014.)  (Revised by Mario
       Carneiro, 13-Oct-2016.) $)

${
	$v ph x A B C V  $.
	$d x A  $.
	$d x C  $.
	$d x ph  $.
	f0_csbied $f wff ph $.
	f1_csbied $f set x $.
	f2_csbied $f class A $.
	f3_csbied $f class B $.
	f4_csbied $f class C $.
	f5_csbied $f class V $.
	e0_csbied $e |- ( ph -> A e. V ) $.
	e1_csbied $e |- ( ( ph /\ x = A ) -> B = C ) $.
	p_csbied $p |- ( ph -> [_ A / x ]_ B = C ) $= f0_csbied f1_csbied p_nfv f0_csbied f1_csbied f4_csbied p_nfcvd e0_csbied e1_csbied f0_csbied f1_csbied f2_csbied f3_csbied f4_csbied f5_csbied p_csbiedf $.
$}

$(Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)

${
	$v ph x A B C D V  $.
	$d x A  $.
	$d x ph  $.
	$d x D  $.
	f0_csbied2 $f wff ph $.
	f1_csbied2 $f set x $.
	f2_csbied2 $f class A $.
	f3_csbied2 $f class B $.
	f4_csbied2 $f class C $.
	f5_csbied2 $f class D $.
	f6_csbied2 $f class V $.
	e0_csbied2 $e |- ( ph -> A e. V ) $.
	e1_csbied2 $e |- ( ph -> A = B ) $.
	e2_csbied2 $e |- ( ( ph /\ x = B ) -> C = D ) $.
	p_csbied2 $p |- ( ph -> [_ A / x ]_ C = D ) $= e0_csbied2 f1_csbied2 a_sup_set_class f2_csbied2 a_wceq p_id e1_csbied2 f1_csbied2 a_sup_set_class f2_csbied2 a_wceq f0_csbied2 f1_csbied2 a_sup_set_class f2_csbied2 f3_csbied2 p_sylan9eqr e2_csbied2 f0_csbied2 f1_csbied2 a_sup_set_class f2_csbied2 a_wceq f1_csbied2 a_sup_set_class f3_csbied2 a_wceq f4_csbied2 f5_csbied2 a_wceq p_syldan f0_csbied2 f1_csbied2 f2_csbied2 f4_csbied2 f5_csbied2 f6_csbied2 p_csbied $.
$}

$(Conversion of implicit substitution to explicit substitution into a
       class (closed form of ~ csbie2 ).  (Contributed by NM, 3-Sep-2007.)
       (Revised by Mario Carneiro, 13-Oct-2016.) $)

${
	$v x y A B C D  $.
	$d x y A  $.
	$d x y B  $.
	$d C  $.
	$d x y D  $.
	f0_csbie2t $f set x $.
	f1_csbie2t $f set y $.
	f2_csbie2t $f class A $.
	f3_csbie2t $f class B $.
	f4_csbie2t $f class C $.
	f5_csbie2t $f class D $.
	e0_csbie2t $e |- A e. _V $.
	e1_csbie2t $e |- B e. _V $.
	p_csbie2t $p |- ( A. x A. y ( ( x = A /\ y = B ) -> C = D ) -> [_ A / x ]_ [_ B / y ]_ C = D ) $= f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t p_nfa1 f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_wal f0_csbie2t f5_csbie2t p_nfcvd e0_csbie2t f2_csbie2t a_cvv a_wcel f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_wal p_a1i f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t f0_csbie2t p_nfa2 f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t p_nfv f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_wal f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t p_nfan f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_wal f0_csbie2t a_sup_set_class f2_csbie2t a_wceq a_wa f1_csbie2t f5_csbie2t p_nfcvd e1_csbie2t f3_csbie2t a_cvv a_wcel f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_wal f0_csbie2t a_sup_set_class f2_csbie2t a_wceq a_wa p_a1i f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t p_sp f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f0_csbie2t p_sps f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_wal f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq f4_csbie2t f5_csbie2t a_wceq p_impl f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_wal f0_csbie2t a_sup_set_class f2_csbie2t a_wceq a_wa f1_csbie2t f3_csbie2t f4_csbie2t f5_csbie2t a_cvv p_csbiedf f0_csbie2t a_sup_set_class f2_csbie2t a_wceq f1_csbie2t a_sup_set_class f3_csbie2t a_wceq a_wa f4_csbie2t f5_csbie2t a_wceq a_wi f1_csbie2t a_wal f0_csbie2t a_wal f0_csbie2t f2_csbie2t f1_csbie2t f3_csbie2t f4_csbie2t a_csb f5_csbie2t a_cvv p_csbiedf $.
$}

$(Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 27-Aug-2007.) $)

${
	$v x y A B C D  $.
	$d x y A  $.
	$d x y B  $.
	$d C  $.
	$d x y D  $.
	f0_csbie2 $f set x $.
	f1_csbie2 $f set y $.
	f2_csbie2 $f class A $.
	f3_csbie2 $f class B $.
	f4_csbie2 $f class C $.
	f5_csbie2 $f class D $.
	e0_csbie2 $e |- A e. _V $.
	e1_csbie2 $e |- B e. _V $.
	e2_csbie2 $e |- ( ( x = A /\ y = B ) -> C = D ) $.
	p_csbie2 $p |- [_ A / x ]_ [_ B / y ]_ C = D $= e2_csbie2 f0_csbie2 a_sup_set_class f2_csbie2 a_wceq f1_csbie2 a_sup_set_class f3_csbie2 a_wceq a_wa f4_csbie2 f5_csbie2 a_wceq a_wi f0_csbie2 f1_csbie2 p_gen2 e0_csbie2 e1_csbie2 f0_csbie2 f1_csbie2 f2_csbie2 f3_csbie2 f4_csbie2 f5_csbie2 p_csbie2t f0_csbie2 a_sup_set_class f2_csbie2 a_wceq f1_csbie2 a_sup_set_class f3_csbie2 a_wceq a_wa f4_csbie2 f5_csbie2 a_wceq a_wi f1_csbie2 a_wal f0_csbie2 a_wal f0_csbie2 f2_csbie2 f1_csbie2 f3_csbie2 f4_csbie2 a_csb a_csb f5_csbie2 a_wceq a_ax-mp $.
$}

$(Conversion of implicit substitution to explicit class substitution.
       This version of ~ sbcie avoids a disjointness condition on ` x , A ` by
       substituting twice.  (Contributed by Mario Carneiro, 11-Nov-2016.) $)

${
	$v x y A B C D V  $.
	$d x y z  $.
	$d A y z  $.
	$d B y z  $.
	$d C x  $.
	$d D y z  $.
	$d V z  $.
	f0_csbie2g $f set x $.
	f1_csbie2g $f set y $.
	f2_csbie2g $f class A $.
	f3_csbie2g $f class B $.
	f4_csbie2g $f class C $.
	f5_csbie2g $f class D $.
	f6_csbie2g $f class V $.
	i0_csbie2g $f set z $.
	e0_csbie2g $e |- ( x = y -> B = C ) $.
	e1_csbie2g $e |- ( y = A -> C = D ) $.
	p_csbie2g $p |- ( A e. V -> [_ A / x ]_ B = D ) $= f0_csbie2g i0_csbie2g f2_csbie2g f3_csbie2g a_df-csb e0_csbie2g f0_csbie2g a_sup_set_class f1_csbie2g a_sup_set_class a_wceq f3_csbie2g f4_csbie2g i0_csbie2g a_sup_set_class p_eleq2d e1_csbie2g f1_csbie2g a_sup_set_class f2_csbie2g a_wceq f4_csbie2g f5_csbie2g i0_csbie2g a_sup_set_class p_eleq2d i0_csbie2g a_sup_set_class f3_csbie2g a_wcel i0_csbie2g a_sup_set_class f4_csbie2g a_wcel i0_csbie2g a_sup_set_class f5_csbie2g a_wcel f0_csbie2g f1_csbie2g f2_csbie2g f6_csbie2g p_sbcie2g f2_csbie2g f6_csbie2g a_wcel i0_csbie2g a_sup_set_class f3_csbie2g a_wcel f0_csbie2g f2_csbie2g a_wsbc i0_csbie2g f5_csbie2g p_abbi1dv f2_csbie2g f6_csbie2g a_wcel f0_csbie2g f2_csbie2g f3_csbie2g a_csb i0_csbie2g a_sup_set_class f3_csbie2g a_wcel f0_csbie2g f2_csbie2g a_wsbc i0_csbie2g a_cab f5_csbie2g p_syl5eq $.
$}

$(Nest the composition of two substitutions.  (Contributed by Mario
       Carneiro, 11-Nov-2016.) $)

${
	$v ph x y A B V  $.
	$d x z  $.
	$d y z  $.
	$d z A  $.
	$d z B  $.
	$d z  $.
	$d z ph  $.
	f0_sbcnestgf $f wff ph $.
	f1_sbcnestgf $f set x $.
	f2_sbcnestgf $f set y $.
	f3_sbcnestgf $f class A $.
	f4_sbcnestgf $f class B $.
	f5_sbcnestgf $f class V $.
	i0_sbcnestgf $f set z $.
	p_sbcnestgf $p |- ( ( A e. V /\ A. y F/ x ph ) -> ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. ph ) ) $= f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f1_sbcnestgf i0_sbcnestgf a_sup_set_class f3_sbcnestgf p_dfsbcq f1_sbcnestgf i0_sbcnestgf a_sup_set_class f3_sbcnestgf f4_sbcnestgf p_csbeq1 f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb f1_sbcnestgf f3_sbcnestgf f4_sbcnestgf a_csb p_dfsbcq i0_sbcnestgf a_sup_set_class f3_sbcnestgf a_wceq f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb f1_sbcnestgf f3_sbcnestgf f4_sbcnestgf a_csb a_wceq f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf f3_sbcnestgf f4_sbcnestgf a_csb a_wsbc a_wb p_syl i0_sbcnestgf a_sup_set_class f3_sbcnestgf a_wceq f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f1_sbcnestgf i0_sbcnestgf a_sup_set_class a_wsbc f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f1_sbcnestgf f3_sbcnestgf a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf f3_sbcnestgf f4_sbcnestgf a_csb a_wsbc p_bibi12d i0_sbcnestgf a_sup_set_class f3_sbcnestgf a_wceq f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f1_sbcnestgf i0_sbcnestgf a_sup_set_class a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wsbc a_wb f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f1_sbcnestgf f3_sbcnestgf a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf f3_sbcnestgf f4_sbcnestgf a_csb a_wsbc a_wb f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal p_imbi2d i0_sbcnestgf p_vex i0_sbcnestgf a_sup_set_class a_cvv a_wcel f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal p_a1i f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf p_csbeq1a f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb p_dfsbcq f1_sbcnestgf a_sup_set_class i0_sbcnestgf a_sup_set_class a_wceq f4_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wceq f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wsbc a_wb p_syl f1_sbcnestgf a_sup_set_class i0_sbcnestgf a_sup_set_class a_wceq f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wsbc a_wb f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal p_adantl f0_sbcnestgf f1_sbcnestgf p_nfnf1 f0_sbcnestgf f1_sbcnestgf a_wnf f1_sbcnestgf f2_sbcnestgf p_nfal f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf p_nfa1 f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf p_nfcsb1v f1_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wnfc f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal p_a1i f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf p_sp f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal f0_sbcnestgf f1_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb p_nfsbcd f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wsbc f1_sbcnestgf i0_sbcnestgf a_sup_set_class a_cvv p_sbciedf f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f1_sbcnestgf i0_sbcnestgf a_sup_set_class a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf i0_sbcnestgf a_sup_set_class f4_sbcnestgf a_csb a_wsbc a_wb a_wi f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f1_sbcnestgf f3_sbcnestgf a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf f3_sbcnestgf f4_sbcnestgf a_csb a_wsbc a_wb a_wi i0_sbcnestgf f3_sbcnestgf f5_sbcnestgf p_vtoclg f3_sbcnestgf f5_sbcnestgf a_wcel f0_sbcnestgf f1_sbcnestgf a_wnf f2_sbcnestgf a_wal f0_sbcnestgf f2_sbcnestgf f4_sbcnestgf a_wsbc f1_sbcnestgf f3_sbcnestgf a_wsbc f0_sbcnestgf f2_sbcnestgf f1_sbcnestgf f3_sbcnestgf f4_sbcnestgf a_csb a_wsbc a_wb p_imp $.
$}

$(Nest the composition of two substitutions.  (Contributed by NM,
       23-Nov-2005.)  (Proof shortened by Mario Carneiro, 10-Nov-2016.) $)

${
	$v x y A B C V  $.
	$d x z  $.
	$d y z  $.
	$d z A  $.
	$d z B  $.
	$d z C  $.
	$d z  $.
	f0_csbnestgf $f set x $.
	f1_csbnestgf $f set y $.
	f2_csbnestgf $f class A $.
	f3_csbnestgf $f class B $.
	f4_csbnestgf $f class C $.
	f5_csbnestgf $f class V $.
	i0_csbnestgf $f set z $.
	p_csbnestgf $p |- ( ( A e. V /\ A. y F/_ x C ) -> [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $= f2_csbnestgf f5_csbnestgf p_elex f1_csbnestgf i0_csbnestgf f3_csbnestgf f4_csbnestgf a_df-csb i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f3_csbnestgf a_wsbc i0_csbnestgf f1_csbnestgf f3_csbnestgf f4_csbnestgf a_csb p_abeq2i i0_csbnestgf a_sup_set_class f1_csbnestgf f3_csbnestgf f4_csbnestgf a_csb a_wcel i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f3_csbnestgf a_wsbc f0_csbnestgf f2_csbnestgf p_sbcbii f0_csbnestgf i0_csbnestgf f4_csbnestgf p_nfcr f0_csbnestgf f4_csbnestgf a_wnfc i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f0_csbnestgf a_wnf f1_csbnestgf p_alimi i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f0_csbnestgf f1_csbnestgf f2_csbnestgf f3_csbnestgf a_cvv p_sbcnestgf f0_csbnestgf f4_csbnestgf a_wnfc f1_csbnestgf a_wal f2_csbnestgf a_cvv a_wcel i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f0_csbnestgf a_wnf f1_csbnestgf a_wal i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f3_csbnestgf a_wsbc f0_csbnestgf f2_csbnestgf a_wsbc i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f0_csbnestgf f2_csbnestgf f3_csbnestgf a_csb a_wsbc a_wb p_sylan2 i0_csbnestgf a_sup_set_class f1_csbnestgf f3_csbnestgf f4_csbnestgf a_csb a_wcel f0_csbnestgf f2_csbnestgf a_wsbc i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f3_csbnestgf a_wsbc f0_csbnestgf f2_csbnestgf a_wsbc f2_csbnestgf a_cvv a_wcel f0_csbnestgf f4_csbnestgf a_wnfc f1_csbnestgf a_wal a_wa i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f0_csbnestgf f2_csbnestgf f3_csbnestgf a_csb a_wsbc p_syl5bb f2_csbnestgf a_cvv a_wcel f0_csbnestgf f4_csbnestgf a_wnfc f1_csbnestgf a_wal a_wa i0_csbnestgf a_sup_set_class f1_csbnestgf f3_csbnestgf f4_csbnestgf a_csb a_wcel f0_csbnestgf f2_csbnestgf a_wsbc i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f0_csbnestgf f2_csbnestgf f3_csbnestgf a_csb a_wsbc i0_csbnestgf p_abbidv f2_csbnestgf f5_csbnestgf a_wcel f2_csbnestgf a_cvv a_wcel f0_csbnestgf f4_csbnestgf a_wnfc f1_csbnestgf a_wal i0_csbnestgf a_sup_set_class f1_csbnestgf f3_csbnestgf f4_csbnestgf a_csb a_wcel f0_csbnestgf f2_csbnestgf a_wsbc i0_csbnestgf a_cab i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f0_csbnestgf f2_csbnestgf f3_csbnestgf a_csb a_wsbc i0_csbnestgf a_cab a_wceq p_sylan f0_csbnestgf i0_csbnestgf f2_csbnestgf f1_csbnestgf f3_csbnestgf f4_csbnestgf a_csb a_df-csb f1_csbnestgf i0_csbnestgf f0_csbnestgf f2_csbnestgf f3_csbnestgf a_csb f4_csbnestgf a_df-csb f2_csbnestgf f5_csbnestgf a_wcel f0_csbnestgf f4_csbnestgf a_wnfc f1_csbnestgf a_wal a_wa i0_csbnestgf a_sup_set_class f1_csbnestgf f3_csbnestgf f4_csbnestgf a_csb a_wcel f0_csbnestgf f2_csbnestgf a_wsbc i0_csbnestgf a_cab i0_csbnestgf a_sup_set_class f4_csbnestgf a_wcel f1_csbnestgf f0_csbnestgf f2_csbnestgf f3_csbnestgf a_csb a_wsbc i0_csbnestgf a_cab f0_csbnestgf f2_csbnestgf f1_csbnestgf f3_csbnestgf f4_csbnestgf a_csb a_csb f1_csbnestgf f0_csbnestgf f2_csbnestgf f3_csbnestgf a_csb f4_csbnestgf a_csb p_3eqtr4g $.
$}

$(Nest the composition of two substitutions.  (Contributed by NM,
       27-Nov-2005.)  (Proof shortened by Mario Carneiro, 11-Nov-2016.) $)

${
	$v ph x y A B V  $.
	$d x  $.
	$d y  $.
	$d A  $.
	$d B  $.
	$d ph  $.
	$d x ph  $.
	f0_sbcnestg $f wff ph $.
	f1_sbcnestg $f set x $.
	f2_sbcnestg $f set y $.
	f3_sbcnestg $f class A $.
	f4_sbcnestg $f class B $.
	f5_sbcnestg $f class V $.
	p_sbcnestg $p |- ( A e. V -> ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. ph ) ) $= f0_sbcnestg f1_sbcnestg p_nfv f0_sbcnestg f1_sbcnestg a_wnf f2_sbcnestg a_ax-gen f0_sbcnestg f1_sbcnestg f2_sbcnestg f3_sbcnestg f4_sbcnestg f5_sbcnestg p_sbcnestgf f3_sbcnestg f5_sbcnestg a_wcel f0_sbcnestg f1_sbcnestg a_wnf f2_sbcnestg a_wal f0_sbcnestg f2_sbcnestg f4_sbcnestg a_wsbc f1_sbcnestg f3_sbcnestg a_wsbc f0_sbcnestg f2_sbcnestg f1_sbcnestg f3_sbcnestg f4_sbcnestg a_csb a_wsbc a_wb p_mpan2 $.
$}

$(Nest the composition of two substitutions.  (Contributed by NM,
       23-Nov-2005.)  (Proof shortened by Mario Carneiro, 10-Nov-2016.) $)

${
	$v x y A B C V  $.
	$d x  $.
	$d y  $.
	$d A  $.
	$d B  $.
	$d C  $.
	$d x  $.
	$d x C  $.
	f0_csbnestg $f set x $.
	f1_csbnestg $f set y $.
	f2_csbnestg $f class A $.
	f3_csbnestg $f class B $.
	f4_csbnestg $f class C $.
	f5_csbnestg $f class V $.
	p_csbnestg $p |- ( A e. V -> [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $= f0_csbnestg f4_csbnestg p_nfcv f0_csbnestg f4_csbnestg a_wnfc f1_csbnestg a_ax-gen f0_csbnestg f1_csbnestg f2_csbnestg f3_csbnestg f4_csbnestg f5_csbnestg p_csbnestgf f2_csbnestg f5_csbnestg a_wcel f0_csbnestg f4_csbnestg a_wnfc f1_csbnestg a_wal f0_csbnestg f2_csbnestg f1_csbnestg f3_csbnestg f4_csbnestg a_csb a_csb f1_csbnestg f0_csbnestg f2_csbnestg f3_csbnestg a_csb f4_csbnestg a_csb a_wceq p_mpan2 $.
$}

$(Nest the composition of two substitutions.  (New usage is discouraged.)
       (Contributed by NM, 23-Nov-2005.) $)

${
	$v x y A B C V W  $.
	$d x C  $.
	f0_csbnestgOLD $f set x $.
	f1_csbnestgOLD $f set y $.
	f2_csbnestgOLD $f class A $.
	f3_csbnestgOLD $f class B $.
	f4_csbnestgOLD $f class C $.
	f5_csbnestgOLD $f class V $.
	f6_csbnestgOLD $f class W $.
	p_csbnestgOLD $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $= f0_csbnestgOLD f1_csbnestgOLD f2_csbnestgOLD f3_csbnestgOLD f4_csbnestgOLD f5_csbnestgOLD p_csbnestg f2_csbnestgOLD f5_csbnestgOLD a_wcel f0_csbnestgOLD f2_csbnestgOLD f1_csbnestgOLD f3_csbnestgOLD f4_csbnestgOLD a_csb a_csb f1_csbnestgOLD f0_csbnestgOLD f2_csbnestgOLD f3_csbnestgOLD a_csb f4_csbnestgOLD a_csb a_wceq f3_csbnestgOLD f6_csbnestgOLD a_wcel f0_csbnestgOLD a_wal p_adantr $.
$}

$(Nest the composition of two substitutions.  (Contributed by NM,
       23-May-2006.)  (Proof shortened by Mario Carneiro, 11-Nov-2016.) $)

${
	$v x A B C V  $.
	$d x y  $.
	$d y C  $.
	f0_csbnest1g $f set x $.
	f1_csbnest1g $f class A $.
	f2_csbnest1g $f class B $.
	f3_csbnest1g $f class C $.
	f4_csbnest1g $f class V $.
	i0_csbnest1g $f set y $.
	p_csbnest1g $p |- ( A e. V -> [_ A / x ]_ [_ B / x ]_ C = [_ [_ A / x ]_ B / x ]_ C ) $= f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g p_nfcsb1v f0_csbnest1g f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g a_csb a_wnfc i0_csbnest1g a_ax-gen f0_csbnest1g i0_csbnest1g f1_csbnest1g f2_csbnest1g f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g a_csb f4_csbnest1g p_csbnestgf f1_csbnest1g f4_csbnest1g a_wcel f0_csbnest1g f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g a_csb a_wnfc i0_csbnest1g a_wal f0_csbnest1g f1_csbnest1g i0_csbnest1g f2_csbnest1g f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g a_csb a_csb a_csb i0_csbnest1g f0_csbnest1g f1_csbnest1g f2_csbnest1g a_csb f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g a_csb a_csb a_wceq p_mpan2 f0_csbnest1g i0_csbnest1g f2_csbnest1g f3_csbnest1g p_csbco f0_csbnest1g f1_csbnest1g i0_csbnest1g f2_csbnest1g f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g a_csb a_csb f0_csbnest1g f2_csbnest1g f3_csbnest1g a_csb p_csbeq2i f0_csbnest1g i0_csbnest1g f0_csbnest1g f1_csbnest1g f2_csbnest1g a_csb f3_csbnest1g p_csbco f1_csbnest1g f4_csbnest1g a_wcel f0_csbnest1g f1_csbnest1g i0_csbnest1g f2_csbnest1g f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g a_csb a_csb a_csb i0_csbnest1g f0_csbnest1g f1_csbnest1g f2_csbnest1g a_csb f0_csbnest1g i0_csbnest1g a_sup_set_class f3_csbnest1g a_csb a_csb f0_csbnest1g f1_csbnest1g f0_csbnest1g f2_csbnest1g f3_csbnest1g a_csb a_csb f0_csbnest1g f0_csbnest1g f1_csbnest1g f2_csbnest1g a_csb f3_csbnest1g a_csb p_3eqtr3g $.
$}

$(Nest the composition of two substitutions.  Obsolete as of 11-Nov-2016.
       (Contributed by NM, 23-May-2006.)  (New usage is discouraged.) $)

${
	$v x A B C V W  $.
	$d x A  $.
	$d B  $.
	$d C  $.
	$d W  $.
	f0_csbnest1gOLD $f set x $.
	f1_csbnest1gOLD $f class A $.
	f2_csbnest1gOLD $f class B $.
	f3_csbnest1gOLD $f class C $.
	f4_csbnest1gOLD $f class V $.
	f5_csbnest1gOLD $f class W $.
	p_csbnest1gOLD $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ [_ B / x ]_ C = [_ [_ A / x ]_ B / x ]_ C ) $= f0_csbnest1gOLD f1_csbnest1gOLD f2_csbnest1gOLD f3_csbnest1gOLD f4_csbnest1gOLD p_csbnest1g f1_csbnest1gOLD f4_csbnest1gOLD a_wcel f0_csbnest1gOLD f1_csbnest1gOLD f0_csbnest1gOLD f2_csbnest1gOLD f3_csbnest1gOLD a_csb a_csb f0_csbnest1gOLD f0_csbnest1gOLD f1_csbnest1gOLD f2_csbnest1gOLD a_csb f3_csbnest1gOLD a_csb a_wceq f2_csbnest1gOLD f5_csbnest1gOLD a_wcel f0_csbnest1gOLD a_wal p_adantr $.
$}

$(Idempotent law for class substitutions.  (Contributed by NM,
       1-Mar-2008.) $)

${
	$v x A B V  $.
	$d x A  $.
	f0_csbidmg $f set x $.
	f1_csbidmg $f class A $.
	f2_csbidmg $f class B $.
	f3_csbidmg $f class V $.
	p_csbidmg $p |- ( A e. V -> [_ A / x ]_ [_ A / x ]_ B = [_ A / x ]_ B ) $= f1_csbidmg f3_csbidmg p_elex f0_csbidmg f1_csbidmg f1_csbidmg f2_csbidmg a_cvv p_csbnest1g f0_csbidmg f1_csbidmg f1_csbidmg a_cvv p_csbconstg f1_csbidmg a_cvv a_wcel f0_csbidmg f0_csbidmg f1_csbidmg f1_csbidmg a_csb f1_csbidmg f2_csbidmg p_csbeq1d f1_csbidmg a_cvv a_wcel f0_csbidmg f1_csbidmg f0_csbidmg f1_csbidmg f2_csbidmg a_csb a_csb f0_csbidmg f0_csbidmg f1_csbidmg f1_csbidmg a_csb f2_csbidmg a_csb f0_csbidmg f1_csbidmg f2_csbidmg a_csb p_eqtrd f1_csbidmg f3_csbidmg a_wcel f1_csbidmg a_cvv a_wcel f0_csbidmg f1_csbidmg f0_csbidmg f1_csbidmg f2_csbidmg a_csb a_csb f0_csbidmg f1_csbidmg f2_csbidmg a_csb a_wceq p_syl $.
$}

$(Composition of two substitutions.  (Contributed by NM, 27-Nov-2005.)
       (Revised by Mario Carneiro, 11-Nov-2016.) $)

${
	$v ph x y A B C V  $.
	$d x A  $.
	$d x ph  $.
	$d x C  $.
	$d x  $.
	f0_sbcco3g $f wff ph $.
	f1_sbcco3g $f set x $.
	f2_sbcco3g $f set y $.
	f3_sbcco3g $f class A $.
	f4_sbcco3g $f class B $.
	f5_sbcco3g $f class C $.
	f6_sbcco3g $f class V $.
	e0_sbcco3g $e |- ( x = A -> B = C ) $.
	p_sbcco3g $p |- ( A e. V -> ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ph ) ) $= f0_sbcco3g f1_sbcco3g f2_sbcco3g f3_sbcco3g f4_sbcco3g f6_sbcco3g p_sbcnestg f3_sbcco3g f6_sbcco3g p_elex f3_sbcco3g a_cvv a_wcel f1_sbcco3g f5_sbcco3g p_nfcvd e0_sbcco3g f1_sbcco3g f3_sbcco3g f4_sbcco3g f5_sbcco3g a_cvv p_csbiegf f0_sbcco3g f2_sbcco3g f1_sbcco3g f3_sbcco3g f4_sbcco3g a_csb f5_sbcco3g p_dfsbcq f3_sbcco3g f6_sbcco3g a_wcel f3_sbcco3g a_cvv a_wcel f1_sbcco3g f3_sbcco3g f4_sbcco3g a_csb f5_sbcco3g a_wceq f0_sbcco3g f2_sbcco3g f1_sbcco3g f3_sbcco3g f4_sbcco3g a_csb a_wsbc f0_sbcco3g f2_sbcco3g f5_sbcco3g a_wsbc a_wb p_3syl f3_sbcco3g f6_sbcco3g a_wcel f0_sbcco3g f2_sbcco3g f4_sbcco3g a_wsbc f1_sbcco3g f3_sbcco3g a_wsbc f0_sbcco3g f2_sbcco3g f1_sbcco3g f3_sbcco3g f4_sbcco3g a_csb a_wsbc f0_sbcco3g f2_sbcco3g f5_sbcco3g a_wsbc p_bitrd $.
$}

$(Composition of two substitutions.  (Contributed by NM, 27-Nov-2005.)
       (New usage is discouraged.) $)

${
	$v ph x y A B C V W  $.
	$d x A  $.
	$d x ph  $.
	$d x C  $.
	$d x  $.
	f0_sbcco3gOLD $f wff ph $.
	f1_sbcco3gOLD $f set x $.
	f2_sbcco3gOLD $f set y $.
	f3_sbcco3gOLD $f class A $.
	f4_sbcco3gOLD $f class B $.
	f5_sbcco3gOLD $f class C $.
	f6_sbcco3gOLD $f class V $.
	f7_sbcco3gOLD $f class W $.
	e0_sbcco3gOLD $e |- ( x = A -> B = C ) $.
	p_sbcco3gOLD $p |- ( ( A e. V /\ A. x B e. W ) -> ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ph ) ) $= e0_sbcco3gOLD f0_sbcco3gOLD f1_sbcco3gOLD f2_sbcco3gOLD f3_sbcco3gOLD f4_sbcco3gOLD f5_sbcco3gOLD f6_sbcco3gOLD p_sbcco3g f3_sbcco3gOLD f6_sbcco3gOLD a_wcel f0_sbcco3gOLD f2_sbcco3gOLD f4_sbcco3gOLD a_wsbc f1_sbcco3gOLD f3_sbcco3gOLD a_wsbc f0_sbcco3gOLD f2_sbcco3gOLD f5_sbcco3gOLD a_wsbc a_wb f4_sbcco3gOLD f7_sbcco3gOLD a_wcel f1_sbcco3gOLD a_wal p_adantr $.
$}

$(Composition of two class substitutions.  (Contributed by NM,
       27-Nov-2005.)  (Revised by Mario Carneiro, 11-Nov-2016.) $)

${
	$v x y A B C D V  $.
	$d x A  $.
	$d x  $.
	$d x C  $.
	$d x D  $.
	f0_csbco3g $f set x $.
	f1_csbco3g $f set y $.
	f2_csbco3g $f class A $.
	f3_csbco3g $f class B $.
	f4_csbco3g $f class C $.
	f5_csbco3g $f class D $.
	f6_csbco3g $f class V $.
	e0_csbco3g $e |- ( x = A -> B = C ) $.
	p_csbco3g $p |- ( A e. V -> [_ A / x ]_ [_ B / y ]_ D = [_ C / y ]_ D ) $= f0_csbco3g f1_csbco3g f2_csbco3g f3_csbco3g f5_csbco3g f6_csbco3g p_csbnestg f2_csbco3g f6_csbco3g p_elex f2_csbco3g a_cvv a_wcel f0_csbco3g f4_csbco3g p_nfcvd e0_csbco3g f0_csbco3g f2_csbco3g f3_csbco3g f4_csbco3g a_cvv p_csbiegf f2_csbco3g f6_csbco3g a_wcel f2_csbco3g a_cvv a_wcel f0_csbco3g f2_csbco3g f3_csbco3g a_csb f4_csbco3g a_wceq p_syl f2_csbco3g f6_csbco3g a_wcel f1_csbco3g f0_csbco3g f2_csbco3g f3_csbco3g a_csb f4_csbco3g f5_csbco3g p_csbeq1d f2_csbco3g f6_csbco3g a_wcel f0_csbco3g f2_csbco3g f1_csbco3g f3_csbco3g f5_csbco3g a_csb a_csb f1_csbco3g f0_csbco3g f2_csbco3g f3_csbco3g a_csb f5_csbco3g a_csb f1_csbco3g f4_csbco3g f5_csbco3g a_csb p_eqtrd $.
$}

$(Composition of two class substitutions.  Obsolete as of 11-Nov-2016.
       (Contributed by NM, 27-Nov-2005.)  (New usage is discouraged.) $)

${
	$v x y A B C D V W  $.
	$d x A  $.
	$d x C  $.
	$d x D  $.
	$d x y  $.
	f0_csbco3gOLD $f set x $.
	f1_csbco3gOLD $f set y $.
	f2_csbco3gOLD $f class A $.
	f3_csbco3gOLD $f class B $.
	f4_csbco3gOLD $f class C $.
	f5_csbco3gOLD $f class D $.
	f6_csbco3gOLD $f class V $.
	f7_csbco3gOLD $f class W $.
	e0_csbco3gOLD $e |- ( x = A -> B = D ) $.
	p_csbco3gOLD $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ [_ B / y ]_ C = [_ D / y ]_ C ) $= e0_csbco3gOLD f0_csbco3gOLD f1_csbco3gOLD f2_csbco3gOLD f3_csbco3gOLD f5_csbco3gOLD f4_csbco3gOLD f6_csbco3gOLD p_csbco3g f2_csbco3gOLD f6_csbco3gOLD a_wcel f0_csbco3gOLD f2_csbco3gOLD f1_csbco3gOLD f3_csbco3gOLD f4_csbco3gOLD a_csb a_csb f1_csbco3gOLD f5_csbco3gOLD f4_csbco3gOLD a_csb a_wceq f3_csbco3gOLD f7_csbco3gOLD a_wcel f0_csbco3gOLD a_wal p_adantr $.
$}

$(Special case related to ~ rspsbc .  (Contributed by NM, 10-Dec-2005.)
       (Proof shortened by Eric Schmidt, 17-Jan-2007.) $)

${
	$v x A B C D  $.
	$d x B  $.
	$d x D  $.
	f0_rspcsbela $f set x $.
	f1_rspcsbela $f class A $.
	f2_rspcsbela $f class B $.
	f3_rspcsbela $f class C $.
	f4_rspcsbela $f class D $.
	p_rspcsbela $p |- ( ( A e. B /\ A. x e. B C e. D ) -> [_ A / x ]_ C e. D ) $= f3_rspcsbela f4_rspcsbela a_wcel f0_rspcsbela f1_rspcsbela f2_rspcsbela p_rspsbc f0_rspcsbela f1_rspcsbela f3_rspcsbela f4_rspcsbela f2_rspcsbela p_sbcel1g f1_rspcsbela f2_rspcsbela a_wcel f3_rspcsbela f4_rspcsbela a_wcel f0_rspcsbela f2_rspcsbela a_wral f3_rspcsbela f4_rspcsbela a_wcel f0_rspcsbela f1_rspcsbela a_wsbc f0_rspcsbela f1_rspcsbela f3_rspcsbela a_csb f4_rspcsbela a_wcel p_sylibd f1_rspcsbela f2_rspcsbela a_wcel f3_rspcsbela f4_rspcsbela a_wcel f0_rspcsbela f2_rspcsbela a_wral f0_rspcsbela f1_rspcsbela f3_rspcsbela a_csb f4_rspcsbela a_wcel p_imp $.
$}

$(Two ways of expressing " ` x ` is (effectively) not free in ` A ` ."
       (Contributed by Mario Carneiro, 14-Oct-2016.) $)

${
	$v x y z A  $.
	$d w x y z  $.
	$d w y z A  $.
	f0_sbnfc2 $f set x $.
	f1_sbnfc2 $f set y $.
	f2_sbnfc2 $f set z $.
	f3_sbnfc2 $f class A $.
	i0_sbnfc2 $f set w $.
	p_sbnfc2 $p |- ( F/_ x A <-> A. y A. z [_ y / x ]_ A = [_ z / x ]_ A ) $= f1_sbnfc2 p_vex f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_cvv p_csbtt f1_sbnfc2 a_sup_set_class a_cvv a_wcel f0_sbnfc2 f3_sbnfc2 a_wnfc f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f3_sbnfc2 a_wceq p_mpan f2_sbnfc2 p_vex f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_cvv p_csbtt f2_sbnfc2 a_sup_set_class a_cvv a_wcel f0_sbnfc2 f3_sbnfc2 a_wnfc f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f3_sbnfc2 a_wceq p_mpan f0_sbnfc2 f3_sbnfc2 a_wnfc f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f3_sbnfc2 f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb p_eqtr4d f0_sbnfc2 f3_sbnfc2 a_wnfc f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wceq f1_sbnfc2 f2_sbnfc2 p_alrimivv f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wceq f2_sbnfc2 a_wal f1_sbnfc2 a_wal i0_sbnfc2 p_nfv f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb i0_sbnfc2 a_sup_set_class p_eleq2 i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f1_sbnfc2 p_sbsbc f1_sbnfc2 p_vex f0_sbnfc2 f1_sbnfc2 a_sup_set_class i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_cvv p_sbcel2g f1_sbnfc2 a_sup_set_class a_cvv a_wcel i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f1_sbnfc2 a_sup_set_class a_wsbc i0_sbnfc2 a_sup_set_class f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wcel a_wb a_ax-mp i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f1_sbnfc2 a_wsb i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f1_sbnfc2 a_sup_set_class a_wsbc i0_sbnfc2 a_sup_set_class f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wcel p_bitri i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f2_sbnfc2 p_sbsbc f2_sbnfc2 p_vex f0_sbnfc2 f2_sbnfc2 a_sup_set_class i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_cvv p_sbcel2g f2_sbnfc2 a_sup_set_class a_cvv a_wcel i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f2_sbnfc2 a_sup_set_class a_wsbc i0_sbnfc2 a_sup_set_class f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wcel a_wb a_ax-mp i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f2_sbnfc2 a_wsb i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f2_sbnfc2 a_sup_set_class a_wsbc i0_sbnfc2 a_sup_set_class f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wcel p_bitri f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wceq i0_sbnfc2 a_sup_set_class f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wcel i0_sbnfc2 a_sup_set_class f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wcel i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f1_sbnfc2 a_wsb i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f2_sbnfc2 a_wsb p_3bitr4g f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wceq i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f1_sbnfc2 a_wsb i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f2_sbnfc2 a_wsb a_wb f1_sbnfc2 f2_sbnfc2 p_2alimi i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f1_sbnfc2 f2_sbnfc2 p_sbnf2 f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wceq f2_sbnfc2 a_wal f1_sbnfc2 a_wal i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f1_sbnfc2 a_wsb i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 f2_sbnfc2 a_wsb a_wb f2_sbnfc2 a_wal f1_sbnfc2 a_wal i0_sbnfc2 a_sup_set_class f3_sbnfc2 a_wcel f0_sbnfc2 a_wnf p_sylibr f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wceq f2_sbnfc2 a_wal f1_sbnfc2 a_wal f0_sbnfc2 i0_sbnfc2 f3_sbnfc2 p_nfcd f0_sbnfc2 f3_sbnfc2 a_wnfc f0_sbnfc2 f1_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb f0_sbnfc2 f2_sbnfc2 a_sup_set_class f3_sbnfc2 a_csb a_wceq f2_sbnfc2 a_wal f1_sbnfc2 a_wal p_impbii $.
$}

$(Move substitution into a class abstraction.  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph x y A V  $.
	$d y z A  $.
	$d z ph  $.
	$d x y z  $.
	$d V z  $.
	f0_csbabg $f wff ph $.
	f1_csbabg $f set x $.
	f2_csbabg $f set y $.
	f3_csbabg $f class A $.
	f4_csbabg $f class V $.
	i0_csbabg $f set z $.
	p_csbabg $p |- ( A e. V -> [_ A / x ]_ { y | ph } = { y | [. A / x ]. ph } ) $= f0_csbabg f2_csbabg f1_csbabg i0_csbabg a_sup_set_class f3_csbabg p_sbccom f0_csbabg f1_csbabg f3_csbabg a_wsbc i0_csbabg f2_csbabg a_df-clab f0_csbabg f1_csbabg f3_csbabg a_wsbc f2_csbabg i0_csbabg p_sbsbc i0_csbabg a_sup_set_class f0_csbabg f1_csbabg f3_csbabg a_wsbc f2_csbabg a_cab a_wcel f0_csbabg f1_csbabg f3_csbabg a_wsbc f2_csbabg i0_csbabg a_wsb f0_csbabg f1_csbabg f3_csbabg a_wsbc f2_csbabg i0_csbabg a_sup_set_class a_wsbc p_bitri f0_csbabg i0_csbabg f2_csbabg a_df-clab f0_csbabg f2_csbabg i0_csbabg p_sbsbc i0_csbabg a_sup_set_class f0_csbabg f2_csbabg a_cab a_wcel f0_csbabg f2_csbabg i0_csbabg a_wsb f0_csbabg f2_csbabg i0_csbabg a_sup_set_class a_wsbc p_bitri i0_csbabg a_sup_set_class f0_csbabg f2_csbabg a_cab a_wcel f0_csbabg f2_csbabg i0_csbabg a_sup_set_class a_wsbc f1_csbabg f3_csbabg p_sbcbii f0_csbabg f1_csbabg f3_csbabg a_wsbc f2_csbabg i0_csbabg a_sup_set_class a_wsbc f0_csbabg f2_csbabg i0_csbabg a_sup_set_class a_wsbc f1_csbabg f3_csbabg a_wsbc i0_csbabg a_sup_set_class f0_csbabg f1_csbabg f3_csbabg a_wsbc f2_csbabg a_cab a_wcel i0_csbabg a_sup_set_class f0_csbabg f2_csbabg a_cab a_wcel f1_csbabg f3_csbabg a_wsbc p_3bitr4i f1_csbabg f3_csbabg i0_csbabg a_sup_set_class f0_csbabg f2_csbabg a_cab f4_csbabg p_sbcel2g i0_csbabg a_sup_set_class f0_csbabg f1_csbabg f3_csbabg a_wsbc f2_csbabg a_cab a_wcel i0_csbabg a_sup_set_class f0_csbabg f2_csbabg a_cab a_wcel f1_csbabg f3_csbabg a_wsbc f3_csbabg f4_csbabg a_wcel i0_csbabg a_sup_set_class f1_csbabg f3_csbabg f0_csbabg f2_csbabg a_cab a_csb a_wcel p_syl5rbb f3_csbabg f4_csbabg a_wcel i0_csbabg f1_csbabg f3_csbabg f0_csbabg f2_csbabg a_cab a_csb f0_csbabg f1_csbabg f3_csbabg a_wsbc f2_csbabg a_cab p_eqrdv $.
$}

$(A more general version of ~ cbvralf that doesn't require ` A ` and ` B `
       to be distinct from ` x ` or ` y ` .  Changes bound variables using
       implicit substitution.  (Contributed by Andrew Salmon, 13-Jul-2011.) $)

${
	$v ph ps x y A B  $.
	$d x v z  $.
	$d y v z  $.
	$d A v z  $.
	$d B v z  $.
	$d ph v z  $.
	$d ps v z  $.
	f0_cbvralcsf $f wff ph $.
	f1_cbvralcsf $f wff ps $.
	f2_cbvralcsf $f set x $.
	f3_cbvralcsf $f set y $.
	f4_cbvralcsf $f class A $.
	f5_cbvralcsf $f class B $.
	i0_cbvralcsf $f set z $.
	i1_cbvralcsf $f set v $.
	e0_cbvralcsf $e |- F/_ y A $.
	e1_cbvralcsf $e |- F/_ x B $.
	e2_cbvralcsf $e |- F/ y ph $.
	e3_cbvralcsf $e |- F/ x ps $.
	e4_cbvralcsf $e |- ( x = y -> A = B ) $.
	e5_cbvralcsf $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvralcsf $p |- ( A. x e. A ph <-> A. y e. B ps ) $= f2_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f0_cbvralcsf a_wi i0_cbvralcsf p_nfv f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf p_nfcsb1v f2_cbvralcsf i0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb p_nfcri f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class p_nfsbc1v i0_cbvralcsf a_sup_set_class f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb a_wcel f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class a_wsbc f2_cbvralcsf p_nfim f2_cbvralcsf a_sup_set_class i0_cbvralcsf a_sup_set_class a_wceq p_id f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf p_csbeq1a f2_cbvralcsf a_sup_set_class i0_cbvralcsf a_sup_set_class a_wceq f2_cbvralcsf a_sup_set_class i0_cbvralcsf a_sup_set_class f4_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb p_eleq12d f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class p_sbceq1a f2_cbvralcsf a_sup_set_class i0_cbvralcsf a_sup_set_class a_wceq f2_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel i0_cbvralcsf a_sup_set_class f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb a_wcel f0_cbvralcsf f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class a_wsbc p_imbi12d f2_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f0_cbvralcsf a_wi i0_cbvralcsf a_sup_set_class f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb a_wcel f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class a_wsbc a_wi f2_cbvralcsf i0_cbvralcsf p_cbval f3_cbvralcsf i0_cbvralcsf a_sup_set_class p_nfcv e0_cbvralcsf f3_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf p_nfcsb f3_cbvralcsf i0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb p_nfcri f3_cbvralcsf i0_cbvralcsf a_sup_set_class p_nfcv e2_cbvralcsf f0_cbvralcsf f3_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class p_nfsbc i0_cbvralcsf a_sup_set_class f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb a_wcel f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class a_wsbc f3_cbvralcsf p_nfim f3_cbvralcsf a_sup_set_class f5_cbvralcsf a_wcel f1_cbvralcsf a_wi i0_cbvralcsf p_nfv i0_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class a_wceq p_id f2_cbvralcsf i0_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class f4_cbvralcsf p_csbeq1 f2_cbvralcsf i1_cbvralcsf f3_cbvralcsf a_sup_set_class f4_cbvralcsf a_df-csb e1_cbvralcsf f2_cbvralcsf i1_cbvralcsf f5_cbvralcsf p_nfcri e4_cbvralcsf f2_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class a_wceq f4_cbvralcsf f5_cbvralcsf i1_cbvralcsf a_sup_set_class p_eleq2d i1_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel i1_cbvralcsf a_sup_set_class f5_cbvralcsf a_wcel f2_cbvralcsf f3_cbvralcsf p_sbie i1_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f2_cbvralcsf f3_cbvralcsf p_sbsbc i1_cbvralcsf a_sup_set_class f5_cbvralcsf a_wcel i1_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f2_cbvralcsf f3_cbvralcsf a_wsb i1_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f2_cbvralcsf f3_cbvralcsf a_sup_set_class a_wsbc p_bitr3i i1_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f2_cbvralcsf f3_cbvralcsf a_sup_set_class a_wsbc i1_cbvralcsf f5_cbvralcsf p_abbi2i f2_cbvralcsf f3_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb i1_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f2_cbvralcsf f3_cbvralcsf a_sup_set_class a_wsbc i1_cbvralcsf a_cab f5_cbvralcsf p_eqtr4i i0_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class a_wceq f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb f2_cbvralcsf f3_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb f5_cbvralcsf p_syl6eq i0_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class a_wceq i0_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb f5_cbvralcsf p_eleq12d f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class p_dfsbcq f0_cbvralcsf f2_cbvralcsf f3_cbvralcsf p_sbsbc e3_cbvralcsf e5_cbvralcsf f0_cbvralcsf f1_cbvralcsf f2_cbvralcsf f3_cbvralcsf p_sbie f0_cbvralcsf f2_cbvralcsf f3_cbvralcsf a_sup_set_class a_wsbc f0_cbvralcsf f2_cbvralcsf f3_cbvralcsf a_wsb f1_cbvralcsf p_bitr3i i0_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class a_wceq f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class a_wsbc f0_cbvralcsf f2_cbvralcsf f3_cbvralcsf a_sup_set_class a_wsbc f1_cbvralcsf p_syl6bb i0_cbvralcsf a_sup_set_class f3_cbvralcsf a_sup_set_class a_wceq i0_cbvralcsf a_sup_set_class f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb a_wcel f3_cbvralcsf a_sup_set_class f5_cbvralcsf a_wcel f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class a_wsbc f1_cbvralcsf p_imbi12d i0_cbvralcsf a_sup_set_class f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb a_wcel f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class a_wsbc a_wi f3_cbvralcsf a_sup_set_class f5_cbvralcsf a_wcel f1_cbvralcsf a_wi i0_cbvralcsf f3_cbvralcsf p_cbval f2_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f0_cbvralcsf a_wi f2_cbvralcsf a_wal i0_cbvralcsf a_sup_set_class f2_cbvralcsf i0_cbvralcsf a_sup_set_class f4_cbvralcsf a_csb a_wcel f0_cbvralcsf f2_cbvralcsf i0_cbvralcsf a_sup_set_class a_wsbc a_wi i0_cbvralcsf a_wal f3_cbvralcsf a_sup_set_class f5_cbvralcsf a_wcel f1_cbvralcsf a_wi f3_cbvralcsf a_wal p_bitri f0_cbvralcsf f2_cbvralcsf f4_cbvralcsf a_df-ral f1_cbvralcsf f3_cbvralcsf f5_cbvralcsf a_df-ral f2_cbvralcsf a_sup_set_class f4_cbvralcsf a_wcel f0_cbvralcsf a_wi f2_cbvralcsf a_wal f3_cbvralcsf a_sup_set_class f5_cbvralcsf a_wcel f1_cbvralcsf a_wi f3_cbvralcsf a_wal f0_cbvralcsf f2_cbvralcsf f4_cbvralcsf a_wral f1_cbvralcsf f3_cbvralcsf f5_cbvralcsf a_wral p_3bitr4i $.
$}

$(A more general version of ~ cbvrexf that has no distinct variable
       restrictions.  Changes bound variables using implicit substitution.
       (Contributed by Andrew Salmon, 13-Jul-2011.)  (Proof shortened by Mario
       Carneiro, 7-Dec-2014.) $)

${
	$v ph ps x y A B  $.
	$d x  $.
	$d y  $.
	$d A  $.
	$d B  $.
	$d ph  $.
	$d ps  $.
	f0_cbvrexcsf $f wff ph $.
	f1_cbvrexcsf $f wff ps $.
	f2_cbvrexcsf $f set x $.
	f3_cbvrexcsf $f set y $.
	f4_cbvrexcsf $f class A $.
	f5_cbvrexcsf $f class B $.
	e0_cbvrexcsf $e |- F/_ y A $.
	e1_cbvrexcsf $e |- F/_ x B $.
	e2_cbvrexcsf $e |- F/ y ph $.
	e3_cbvrexcsf $e |- F/ x ps $.
	e4_cbvrexcsf $e |- ( x = y -> A = B ) $.
	e5_cbvrexcsf $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrexcsf $p |- ( E. x e. A ph <-> E. y e. B ps ) $= e0_cbvrexcsf e1_cbvrexcsf e2_cbvrexcsf f0_cbvrexcsf f3_cbvrexcsf p_nfn e3_cbvrexcsf f1_cbvrexcsf f2_cbvrexcsf p_nfn e4_cbvrexcsf e5_cbvrexcsf f2_cbvrexcsf a_sup_set_class f3_cbvrexcsf a_sup_set_class a_wceq f0_cbvrexcsf f1_cbvrexcsf p_notbid f0_cbvrexcsf a_wn f1_cbvrexcsf a_wn f2_cbvrexcsf f3_cbvrexcsf f4_cbvrexcsf f5_cbvrexcsf p_cbvralcsf f0_cbvrexcsf a_wn f2_cbvrexcsf f4_cbvrexcsf a_wral f1_cbvrexcsf a_wn f3_cbvrexcsf f5_cbvrexcsf a_wral p_notbii f0_cbvrexcsf f2_cbvrexcsf f4_cbvrexcsf p_dfrex2 f1_cbvrexcsf f3_cbvrexcsf f5_cbvrexcsf p_dfrex2 f0_cbvrexcsf a_wn f2_cbvrexcsf f4_cbvrexcsf a_wral a_wn f1_cbvrexcsf a_wn f3_cbvrexcsf f5_cbvrexcsf a_wral a_wn f0_cbvrexcsf f2_cbvrexcsf f4_cbvrexcsf a_wrex f1_cbvrexcsf f3_cbvrexcsf f5_cbvrexcsf a_wrex p_3bitr4i $.
$}

$(A more general version of ~ cbvreuv that has no distinct variable
       rextrictions.  Changes bound variables using implicit substitution.
       (Contributed by Andrew Salmon, 13-Jul-2011.) $)

${
	$v ph ps x y A B  $.
	$d x v z  $.
	$d y v z  $.
	$d A v z  $.
	$d B v z  $.
	$d ph v z  $.
	$d ps v z  $.
	f0_cbvreucsf $f wff ph $.
	f1_cbvreucsf $f wff ps $.
	f2_cbvreucsf $f set x $.
	f3_cbvreucsf $f set y $.
	f4_cbvreucsf $f class A $.
	f5_cbvreucsf $f class B $.
	i0_cbvreucsf $f set z $.
	i1_cbvreucsf $f set v $.
	e0_cbvreucsf $e |- F/_ y A $.
	e1_cbvreucsf $e |- F/_ x B $.
	e2_cbvreucsf $e |- F/ y ph $.
	e3_cbvreucsf $e |- F/ x ps $.
	e4_cbvreucsf $e |- ( x = y -> A = B ) $.
	e5_cbvreucsf $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvreucsf $p |- ( E! x e. A ph <-> E! y e. B ps ) $= f2_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f0_cbvreucsf a_wa i0_cbvreucsf p_nfv f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf p_nfcsb1v f2_cbvreucsf i0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb p_nfcri f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf p_nfs1v i0_cbvreucsf a_sup_set_class f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb a_wcel f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_wsb f2_cbvreucsf p_nfan f2_cbvreucsf a_sup_set_class i0_cbvreucsf a_sup_set_class a_wceq p_id f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf p_csbeq1a f2_cbvreucsf a_sup_set_class i0_cbvreucsf a_sup_set_class a_wceq f2_cbvreucsf a_sup_set_class i0_cbvreucsf a_sup_set_class f4_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb p_eleq12d f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf p_sbequ12 f2_cbvreucsf a_sup_set_class i0_cbvreucsf a_sup_set_class a_wceq f2_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel i0_cbvreucsf a_sup_set_class f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb a_wcel f0_cbvreucsf f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_wsb p_anbi12d f2_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f0_cbvreucsf a_wa i0_cbvreucsf a_sup_set_class f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb a_wcel f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_wsb a_wa f2_cbvreucsf i0_cbvreucsf p_cbveu f3_cbvreucsf i0_cbvreucsf a_sup_set_class p_nfcv e0_cbvreucsf f3_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf p_nfcsb f3_cbvreucsf i0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb p_nfcri e2_cbvreucsf f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf f3_cbvreucsf p_nfsb i0_cbvreucsf a_sup_set_class f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb a_wcel f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_wsb f3_cbvreucsf p_nfan f3_cbvreucsf a_sup_set_class f5_cbvreucsf a_wcel f1_cbvreucsf a_wa i0_cbvreucsf p_nfv i0_cbvreucsf a_sup_set_class f3_cbvreucsf a_sup_set_class a_wceq p_id f2_cbvreucsf i0_cbvreucsf a_sup_set_class f3_cbvreucsf a_sup_set_class f4_cbvreucsf p_csbeq1 i1_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f2_cbvreucsf f3_cbvreucsf p_sbsbc i1_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f2_cbvreucsf f3_cbvreucsf a_wsb i1_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f2_cbvreucsf f3_cbvreucsf a_sup_set_class a_wsbc i1_cbvreucsf p_abbii e1_cbvreucsf f2_cbvreucsf i1_cbvreucsf f5_cbvreucsf p_nfcri e4_cbvreucsf f2_cbvreucsf a_sup_set_class f3_cbvreucsf a_sup_set_class a_wceq f4_cbvreucsf f5_cbvreucsf i1_cbvreucsf a_sup_set_class p_eleq2d i1_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel i1_cbvreucsf a_sup_set_class f5_cbvreucsf a_wcel f2_cbvreucsf f3_cbvreucsf p_sbie i1_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f2_cbvreucsf f3_cbvreucsf a_wsb i1_cbvreucsf a_sup_set_class f5_cbvreucsf a_wcel p_bicomi i1_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f2_cbvreucsf f3_cbvreucsf a_wsb i1_cbvreucsf f5_cbvreucsf p_abbi2i f2_cbvreucsf i1_cbvreucsf f3_cbvreucsf a_sup_set_class f4_cbvreucsf a_df-csb i1_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f2_cbvreucsf f3_cbvreucsf a_wsb i1_cbvreucsf a_cab i1_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f2_cbvreucsf f3_cbvreucsf a_sup_set_class a_wsbc i1_cbvreucsf a_cab f5_cbvreucsf f2_cbvreucsf f3_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb p_3eqtr4ri i0_cbvreucsf a_sup_set_class f3_cbvreucsf a_sup_set_class a_wceq f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb f2_cbvreucsf f3_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb f5_cbvreucsf p_syl6eq i0_cbvreucsf a_sup_set_class f3_cbvreucsf a_sup_set_class a_wceq i0_cbvreucsf a_sup_set_class f3_cbvreucsf a_sup_set_class f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb f5_cbvreucsf p_eleq12d f0_cbvreucsf i0_cbvreucsf f3_cbvreucsf f2_cbvreucsf p_sbequ e3_cbvreucsf e5_cbvreucsf f0_cbvreucsf f1_cbvreucsf f2_cbvreucsf f3_cbvreucsf p_sbie i0_cbvreucsf a_sup_set_class f3_cbvreucsf a_sup_set_class a_wceq f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_wsb f0_cbvreucsf f2_cbvreucsf f3_cbvreucsf a_wsb f1_cbvreucsf p_syl6bb i0_cbvreucsf a_sup_set_class f3_cbvreucsf a_sup_set_class a_wceq i0_cbvreucsf a_sup_set_class f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb a_wcel f3_cbvreucsf a_sup_set_class f5_cbvreucsf a_wcel f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_wsb f1_cbvreucsf p_anbi12d i0_cbvreucsf a_sup_set_class f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb a_wcel f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_wsb a_wa f3_cbvreucsf a_sup_set_class f5_cbvreucsf a_wcel f1_cbvreucsf a_wa i0_cbvreucsf f3_cbvreucsf p_cbveu f2_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f0_cbvreucsf a_wa f2_cbvreucsf a_weu i0_cbvreucsf a_sup_set_class f2_cbvreucsf i0_cbvreucsf a_sup_set_class f4_cbvreucsf a_csb a_wcel f0_cbvreucsf f2_cbvreucsf i0_cbvreucsf a_wsb a_wa i0_cbvreucsf a_weu f3_cbvreucsf a_sup_set_class f5_cbvreucsf a_wcel f1_cbvreucsf a_wa f3_cbvreucsf a_weu p_bitri f0_cbvreucsf f2_cbvreucsf f4_cbvreucsf a_df-reu f1_cbvreucsf f3_cbvreucsf f5_cbvreucsf a_df-reu f2_cbvreucsf a_sup_set_class f4_cbvreucsf a_wcel f0_cbvreucsf a_wa f2_cbvreucsf a_weu f3_cbvreucsf a_sup_set_class f5_cbvreucsf a_wcel f1_cbvreucsf a_wa f3_cbvreucsf a_weu f0_cbvreucsf f2_cbvreucsf f4_cbvreucsf a_wreu f1_cbvreucsf f3_cbvreucsf f5_cbvreucsf a_wreu p_3bitr4i $.
$}

$(A more general version of ~ cbvrab with no distinct variable
       restrictions.  (Contributed by Andrew Salmon, 13-Jul-2011.) $)

${
	$v ph ps x y A B  $.
	$d x v z  $.
	$d y v z  $.
	$d A v z  $.
	$d B v z  $.
	$d ph v z  $.
	$d ps v z  $.
	f0_cbvrabcsf $f wff ph $.
	f1_cbvrabcsf $f wff ps $.
	f2_cbvrabcsf $f set x $.
	f3_cbvrabcsf $f set y $.
	f4_cbvrabcsf $f class A $.
	f5_cbvrabcsf $f class B $.
	i0_cbvrabcsf $f set z $.
	i1_cbvrabcsf $f set v $.
	e0_cbvrabcsf $e |- F/_ y A $.
	e1_cbvrabcsf $e |- F/_ x B $.
	e2_cbvrabcsf $e |- F/ y ph $.
	e3_cbvrabcsf $e |- F/ x ps $.
	e4_cbvrabcsf $e |- ( x = y -> A = B ) $.
	e5_cbvrabcsf $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvrabcsf $p |- { x e. A | ph } = { y e. B | ps } $= f2_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f0_cbvrabcsf a_wa i0_cbvrabcsf p_nfv f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf p_nfcsb1v f2_cbvrabcsf i0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb p_nfcri f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf p_nfs1v i0_cbvrabcsf a_sup_set_class f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb a_wcel f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_wsb f2_cbvrabcsf p_nfan f2_cbvrabcsf a_sup_set_class i0_cbvrabcsf a_sup_set_class a_wceq p_id f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf p_csbeq1a f2_cbvrabcsf a_sup_set_class i0_cbvrabcsf a_sup_set_class a_wceq f2_cbvrabcsf a_sup_set_class i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb p_eleq12d f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf p_sbequ12 f2_cbvrabcsf a_sup_set_class i0_cbvrabcsf a_sup_set_class a_wceq f2_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel i0_cbvrabcsf a_sup_set_class f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb a_wcel f0_cbvrabcsf f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_wsb p_anbi12d f2_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f0_cbvrabcsf a_wa i0_cbvrabcsf a_sup_set_class f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb a_wcel f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_wsb a_wa f2_cbvrabcsf i0_cbvrabcsf p_cbvab f3_cbvrabcsf i0_cbvrabcsf a_sup_set_class p_nfcv e0_cbvrabcsf f3_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf p_nfcsb f3_cbvrabcsf i0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb p_nfcri e2_cbvrabcsf f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf f3_cbvrabcsf p_nfsb i0_cbvrabcsf a_sup_set_class f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb a_wcel f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_wsb f3_cbvrabcsf p_nfan f3_cbvrabcsf a_sup_set_class f5_cbvrabcsf a_wcel f1_cbvrabcsf a_wa i0_cbvrabcsf p_nfv i0_cbvrabcsf a_sup_set_class f3_cbvrabcsf a_sup_set_class a_wceq p_id f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f3_cbvrabcsf a_sup_set_class f4_cbvrabcsf p_csbeq1 f2_cbvrabcsf i1_cbvrabcsf f3_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_df-csb e1_cbvrabcsf f2_cbvrabcsf i1_cbvrabcsf f5_cbvrabcsf p_nfcri e4_cbvrabcsf f2_cbvrabcsf a_sup_set_class f3_cbvrabcsf a_sup_set_class a_wceq f4_cbvrabcsf f5_cbvrabcsf i1_cbvrabcsf a_sup_set_class p_eleq2d i1_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel i1_cbvrabcsf a_sup_set_class f5_cbvrabcsf a_wcel f2_cbvrabcsf f3_cbvrabcsf p_sbie i1_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f2_cbvrabcsf f3_cbvrabcsf p_sbsbc i1_cbvrabcsf a_sup_set_class f5_cbvrabcsf a_wcel i1_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f2_cbvrabcsf f3_cbvrabcsf a_wsb i1_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f2_cbvrabcsf f3_cbvrabcsf a_sup_set_class a_wsbc p_bitr3i i1_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f2_cbvrabcsf f3_cbvrabcsf a_sup_set_class a_wsbc i1_cbvrabcsf f5_cbvrabcsf p_abbi2i f2_cbvrabcsf f3_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb i1_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f2_cbvrabcsf f3_cbvrabcsf a_sup_set_class a_wsbc i1_cbvrabcsf a_cab f5_cbvrabcsf p_eqtr4i i0_cbvrabcsf a_sup_set_class f3_cbvrabcsf a_sup_set_class a_wceq f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb f2_cbvrabcsf f3_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb f5_cbvrabcsf p_syl6eq i0_cbvrabcsf a_sup_set_class f3_cbvrabcsf a_sup_set_class a_wceq i0_cbvrabcsf a_sup_set_class f3_cbvrabcsf a_sup_set_class f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb f5_cbvrabcsf p_eleq12d f0_cbvrabcsf i0_cbvrabcsf f3_cbvrabcsf f2_cbvrabcsf p_sbequ e3_cbvrabcsf e5_cbvrabcsf f0_cbvrabcsf f1_cbvrabcsf f2_cbvrabcsf f3_cbvrabcsf p_sbie i0_cbvrabcsf a_sup_set_class f3_cbvrabcsf a_sup_set_class a_wceq f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_wsb f0_cbvrabcsf f2_cbvrabcsf f3_cbvrabcsf a_wsb f1_cbvrabcsf p_syl6bb i0_cbvrabcsf a_sup_set_class f3_cbvrabcsf a_sup_set_class a_wceq i0_cbvrabcsf a_sup_set_class f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb a_wcel f3_cbvrabcsf a_sup_set_class f5_cbvrabcsf a_wcel f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_wsb f1_cbvrabcsf p_anbi12d i0_cbvrabcsf a_sup_set_class f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb a_wcel f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_wsb a_wa f3_cbvrabcsf a_sup_set_class f5_cbvrabcsf a_wcel f1_cbvrabcsf a_wa i0_cbvrabcsf f3_cbvrabcsf p_cbvab f2_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f0_cbvrabcsf a_wa f2_cbvrabcsf a_cab i0_cbvrabcsf a_sup_set_class f2_cbvrabcsf i0_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_csb a_wcel f0_cbvrabcsf f2_cbvrabcsf i0_cbvrabcsf a_wsb a_wa i0_cbvrabcsf a_cab f3_cbvrabcsf a_sup_set_class f5_cbvrabcsf a_wcel f1_cbvrabcsf a_wa f3_cbvrabcsf a_cab p_eqtri f0_cbvrabcsf f2_cbvrabcsf f4_cbvrabcsf a_df-rab f1_cbvrabcsf f3_cbvrabcsf f5_cbvrabcsf a_df-rab f2_cbvrabcsf a_sup_set_class f4_cbvrabcsf a_wcel f0_cbvrabcsf a_wa f2_cbvrabcsf a_cab f3_cbvrabcsf a_sup_set_class f5_cbvrabcsf a_wcel f1_cbvrabcsf a_wa f3_cbvrabcsf a_cab f0_cbvrabcsf f2_cbvrabcsf f4_cbvrabcsf a_crab f1_cbvrabcsf f3_cbvrabcsf f5_cbvrabcsf a_crab p_3eqtr4i $.
$}

$(Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution which also changes the quantifier
       domain.  (Contributed by David Moews, 1-May-2017.) $)

${
	$v ps ch x y A B  $.
	$d A y  $.
	$d ps y  $.
	$d B x  $.
	$d ch x  $.
	f0_cbvralv2 $f wff ps $.
	f1_cbvralv2 $f wff ch $.
	f2_cbvralv2 $f set x $.
	f3_cbvralv2 $f set y $.
	f4_cbvralv2 $f class A $.
	f5_cbvralv2 $f class B $.
	e0_cbvralv2 $e |- ( x = y -> ( ps <-> ch ) ) $.
	e1_cbvralv2 $e |- ( x = y -> A = B ) $.
	p_cbvralv2 $p |- ( A. x e. A ps <-> A. y e. B ch ) $= f3_cbvralv2 f4_cbvralv2 p_nfcv f2_cbvralv2 f5_cbvralv2 p_nfcv f0_cbvralv2 f3_cbvralv2 p_nfv f1_cbvralv2 f2_cbvralv2 p_nfv e1_cbvralv2 e0_cbvralv2 f0_cbvralv2 f1_cbvralv2 f2_cbvralv2 f3_cbvralv2 f4_cbvralv2 f5_cbvralv2 p_cbvralcsf $.
$}

$(Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution which also changes the quantifier
       domain.  (Contributed by David Moews, 1-May-2017.) $)

${
	$v ps ch x y A B  $.
	$d A y  $.
	$d ps y  $.
	$d B x  $.
	$d ch x  $.
	f0_cbvrexv2 $f wff ps $.
	f1_cbvrexv2 $f wff ch $.
	f2_cbvrexv2 $f set x $.
	f3_cbvrexv2 $f set y $.
	f4_cbvrexv2 $f class A $.
	f5_cbvrexv2 $f class B $.
	e0_cbvrexv2 $e |- ( x = y -> ( ps <-> ch ) ) $.
	e1_cbvrexv2 $e |- ( x = y -> A = B ) $.
	p_cbvrexv2 $p |- ( E. x e. A ps <-> E. y e. B ch ) $= f3_cbvrexv2 f4_cbvrexv2 p_nfcv f2_cbvrexv2 f5_cbvrexv2 p_nfcv f0_cbvrexv2 f3_cbvrexv2 p_nfv f1_cbvrexv2 f2_cbvrexv2 p_nfv e1_cbvrexv2 e0_cbvrexv2 f0_cbvrexv2 f1_cbvrexv2 f2_cbvrexv2 f3_cbvrexv2 f4_cbvrexv2 f5_cbvrexv2 p_cbvrexcsf $.
$}


