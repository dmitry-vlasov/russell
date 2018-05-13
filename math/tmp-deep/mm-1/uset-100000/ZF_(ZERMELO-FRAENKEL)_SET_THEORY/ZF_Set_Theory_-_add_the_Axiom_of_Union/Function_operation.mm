$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/_Maps_to__notation.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                             Function operation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c oF $.

$c oR $.

$(Extend class notation to include mapping of an operation to a function
     operation. $)

${
	$v R  $.
	f0_cof $f class R $.
	a_cof $a class oF R $.
$}

$(Extend class notation to include mapping of a binary relation to a
     function relation. $)

${
	$v R  $.
	f0_cofr $f class R $.
	a_cofr $a class oR R $.
$}

$(Define the function operation map.  The definition is designed so that
       if ` R ` is a binary operation, then ` oF R ` is the analogous operation
       on functions which corresponds to applying ` R ` pointwise to the values
       of the functions.  (Contributed by Mario Carneiro, 20-Jul-2014.) $)

${
	$v x R f g  $.
	$d f g x R  $.
	f0_df-of $f set x $.
	f1_df-of $f class R $.
	f2_df-of $f set f $.
	f3_df-of $f set g $.
	a_df-of $a |- oF R = ( f e. _V , g e. _V |-> ( x e. ( dom f i^i dom g ) |-> ( ( f ` x ) R ( g ` x ) ) ) ) $.
$}

$(Define the function relation map.  The definition is designed so that if
       ` R ` is a binary relation, then ` oF R ` is the analogous relation on
       functions which is true when each element of the left function relates
       to the corresponding element of the right function.  (Contributed by
       Mario Carneiro, 28-Jul-2014.) $)

${
	$v x R f g  $.
	$d f g x R  $.
	f0_df-ofr $f set x $.
	f1_df-ofr $f class R $.
	f2_df-ofr $f set f $.
	f3_df-ofr $f set g $.
	a_df-ofr $a |- oR R = { <. f , g >. | A. x e. ( dom f i^i dom g ) ( f ` x ) R ( g ` x ) } $.
$}

$(Equality theorem for function operation.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)

${
	$v R S  $.
	$d f g x R  $.
	$d f g x S  $.
	f0_ofeq $f class R $.
	f1_ofeq $f class S $.
	i0_ofeq $f set x $.
	i1_ofeq $f set f $.
	i2_ofeq $f set g $.
	p_ofeq $p |- ( R = S -> oF R = oF S ) $= f0_ofeq f1_ofeq a_wceq i1_ofeq a_sup_set_class a_cvv a_wcel i2_ofeq a_sup_set_class a_cvv a_wcel p_simp1 f0_ofeq f1_ofeq a_wceq i1_ofeq a_sup_set_class a_cvv a_wcel i2_ofeq a_sup_set_class a_cvv a_wcel a_w3a f0_ofeq f1_ofeq i0_ofeq a_sup_set_class i1_ofeq a_sup_set_class a_cfv i0_ofeq a_sup_set_class i2_ofeq a_sup_set_class a_cfv p_oveqd f0_ofeq f1_ofeq a_wceq i1_ofeq a_sup_set_class a_cvv a_wcel i2_ofeq a_sup_set_class a_cvv a_wcel a_w3a i0_ofeq i1_ofeq a_sup_set_class a_cdm i2_ofeq a_sup_set_class a_cdm a_cin i0_ofeq a_sup_set_class i1_ofeq a_sup_set_class a_cfv i0_ofeq a_sup_set_class i2_ofeq a_sup_set_class a_cfv f0_ofeq a_co i0_ofeq a_sup_set_class i1_ofeq a_sup_set_class a_cfv i0_ofeq a_sup_set_class i2_ofeq a_sup_set_class a_cfv f1_ofeq a_co p_mpteq2dv f0_ofeq f1_ofeq a_wceq i1_ofeq i2_ofeq a_cvv a_cvv i0_ofeq i1_ofeq a_sup_set_class a_cdm i2_ofeq a_sup_set_class a_cdm a_cin i0_ofeq a_sup_set_class i1_ofeq a_sup_set_class a_cfv i0_ofeq a_sup_set_class i2_ofeq a_sup_set_class a_cfv f0_ofeq a_co a_cmpt i0_ofeq i1_ofeq a_sup_set_class a_cdm i2_ofeq a_sup_set_class a_cdm a_cin i0_ofeq a_sup_set_class i1_ofeq a_sup_set_class a_cfv i0_ofeq a_sup_set_class i2_ofeq a_sup_set_class a_cfv f1_ofeq a_co a_cmpt p_mpt2eq3dva i0_ofeq f0_ofeq i1_ofeq i2_ofeq a_df-of i0_ofeq f1_ofeq i1_ofeq i2_ofeq a_df-of f0_ofeq f1_ofeq a_wceq i1_ofeq i2_ofeq a_cvv a_cvv i0_ofeq i1_ofeq a_sup_set_class a_cdm i2_ofeq a_sup_set_class a_cdm a_cin i0_ofeq a_sup_set_class i1_ofeq a_sup_set_class a_cfv i0_ofeq a_sup_set_class i2_ofeq a_sup_set_class a_cfv f0_ofeq a_co a_cmpt a_cmpt2 i1_ofeq i2_ofeq a_cvv a_cvv i0_ofeq i1_ofeq a_sup_set_class a_cdm i2_ofeq a_sup_set_class a_cdm a_cin i0_ofeq a_sup_set_class i1_ofeq a_sup_set_class a_cfv i0_ofeq a_sup_set_class i2_ofeq a_sup_set_class a_cfv f1_ofeq a_co a_cmpt a_cmpt2 f0_ofeq a_cof f1_ofeq a_cof p_3eqtr4g $.
$}

$(Equality theorem for function relation.  (Contributed by Mario Carneiro,
       28-Jul-2014.) $)

${
	$v R S  $.
	$d f g x R  $.
	$d f g x S  $.
	f0_ofreq $f class R $.
	f1_ofreq $f class S $.
	i0_ofreq $f set x $.
	i1_ofreq $f set f $.
	i2_ofreq $f set g $.
	p_ofreq $p |- ( R = S -> oR R = oR S ) $= i0_ofreq a_sup_set_class i1_ofreq a_sup_set_class a_cfv i0_ofreq a_sup_set_class i2_ofreq a_sup_set_class a_cfv f0_ofreq f1_ofreq p_breq f0_ofreq f1_ofreq a_wceq i0_ofreq a_sup_set_class i1_ofreq a_sup_set_class a_cfv i0_ofreq a_sup_set_class i2_ofreq a_sup_set_class a_cfv f0_ofreq a_wbr i0_ofreq a_sup_set_class i1_ofreq a_sup_set_class a_cfv i0_ofreq a_sup_set_class i2_ofreq a_sup_set_class a_cfv f1_ofreq a_wbr i0_ofreq i1_ofreq a_sup_set_class a_cdm i2_ofreq a_sup_set_class a_cdm a_cin p_ralbidv f0_ofreq f1_ofreq a_wceq i0_ofreq a_sup_set_class i1_ofreq a_sup_set_class a_cfv i0_ofreq a_sup_set_class i2_ofreq a_sup_set_class a_cfv f0_ofreq a_wbr i0_ofreq i1_ofreq a_sup_set_class a_cdm i2_ofreq a_sup_set_class a_cdm a_cin a_wral i0_ofreq a_sup_set_class i1_ofreq a_sup_set_class a_cfv i0_ofreq a_sup_set_class i2_ofreq a_sup_set_class a_cfv f1_ofreq a_wbr i0_ofreq i1_ofreq a_sup_set_class a_cdm i2_ofreq a_sup_set_class a_cdm a_cin a_wral i1_ofreq i2_ofreq p_opabbidv i0_ofreq f0_ofreq i1_ofreq i2_ofreq a_df-ofr i0_ofreq f1_ofreq i1_ofreq i2_ofreq a_df-ofr f0_ofreq f1_ofreq a_wceq i0_ofreq a_sup_set_class i1_ofreq a_sup_set_class a_cfv i0_ofreq a_sup_set_class i2_ofreq a_sup_set_class a_cfv f0_ofreq a_wbr i0_ofreq i1_ofreq a_sup_set_class a_cdm i2_ofreq a_sup_set_class a_cdm a_cin a_wral i1_ofreq i2_ofreq a_copab i0_ofreq a_sup_set_class i1_ofreq a_sup_set_class a_cfv i0_ofreq a_sup_set_class i2_ofreq a_sup_set_class a_cfv f1_ofreq a_wbr i0_ofreq i1_ofreq a_sup_set_class a_cdm i2_ofreq a_sup_set_class a_cdm a_cin a_wral i1_ofreq i2_ofreq a_copab f0_ofreq a_cofr f1_ofreq a_cofr p_3eqtr4g $.
$}

$(A function operation restricted to a set is a set.  (Contributed by NM,
       28-Jul-2014.) $)

${
	$v A R V  $.
	$d f g x R  $.
	$d f g x  $.
	f0_ofexg $f class A $.
	f1_ofexg $f class R $.
	f2_ofexg $f class V $.
	i0_ofexg $f set x $.
	i1_ofexg $f set f $.
	i2_ofexg $f set g $.
	p_ofexg $p |- ( A e. V -> ( oF R |` A ) e. _V ) $= i0_ofexg f1_ofexg i1_ofexg i2_ofexg a_df-of i1_ofexg i2_ofexg a_cvv a_cvv i0_ofexg i1_ofexg a_sup_set_class a_cdm i2_ofexg a_sup_set_class a_cdm a_cin i0_ofexg a_sup_set_class i1_ofexg a_sup_set_class a_cfv i0_ofexg a_sup_set_class i2_ofexg a_sup_set_class a_cfv f1_ofexg a_co a_cmpt f1_ofexg a_cof p_mpt2fun f1_ofexg a_cof f0_ofexg f2_ofexg p_resfunexg f1_ofexg a_cof a_wfun f0_ofexg f2_ofexg a_wcel f1_ofexg a_cof f0_ofexg a_cres a_cvv a_wcel p_mpan $.
$}

$(Hypothesis builder for function operation.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)

${
	$v x R  $.
	$d f g x y R  $.
	$d f g x y  $.
	f0_nfof $f set x $.
	f1_nfof $f class R $.
	i0_nfof $f set y $.
	i1_nfof $f set f $.
	i2_nfof $f set g $.
	e0_nfof $e |- F/_ x R $.
	p_nfof $p |- F/_ x oF R $= i0_nfof f1_nfof i1_nfof i2_nfof a_df-of f0_nfof a_cvv p_nfcv f0_nfof a_cvv p_nfcv f0_nfof i1_nfof a_sup_set_class a_cdm i2_nfof a_sup_set_class a_cdm a_cin p_nfcv f0_nfof i0_nfof a_sup_set_class i1_nfof a_sup_set_class a_cfv p_nfcv e0_nfof f0_nfof i0_nfof a_sup_set_class i2_nfof a_sup_set_class a_cfv p_nfcv f0_nfof i0_nfof a_sup_set_class i1_nfof a_sup_set_class a_cfv i0_nfof a_sup_set_class i2_nfof a_sup_set_class a_cfv f1_nfof p_nfov f0_nfof i0_nfof i1_nfof a_sup_set_class a_cdm i2_nfof a_sup_set_class a_cdm a_cin i0_nfof a_sup_set_class i1_nfof a_sup_set_class a_cfv i0_nfof a_sup_set_class i2_nfof a_sup_set_class a_cfv f1_nfof a_co p_nfmpt i1_nfof i2_nfof f0_nfof a_cvv a_cvv i0_nfof i1_nfof a_sup_set_class a_cdm i2_nfof a_sup_set_class a_cdm a_cin i0_nfof a_sup_set_class i1_nfof a_sup_set_class a_cfv i0_nfof a_sup_set_class i2_nfof a_sup_set_class a_cfv f1_nfof a_co a_cmpt p_nfmpt2 f0_nfof f1_nfof a_cof i1_nfof i2_nfof a_cvv a_cvv i0_nfof i1_nfof a_sup_set_class a_cdm i2_nfof a_sup_set_class a_cdm a_cin i0_nfof a_sup_set_class i1_nfof a_sup_set_class a_cfv i0_nfof a_sup_set_class i2_nfof a_sup_set_class a_cfv f1_nfof a_co a_cmpt a_cmpt2 p_nfcxfr $.
$}

$(Hypothesis builder for function relation.  (Contributed by Mario
       Carneiro, 28-Jul-2014.) $)

${
	$v x R  $.
	$d f g x y R  $.
	$d f g x y  $.
	f0_nfofr $f set x $.
	f1_nfofr $f class R $.
	i0_nfofr $f set y $.
	i1_nfofr $f set f $.
	i2_nfofr $f set g $.
	e0_nfofr $e |- F/_ x R $.
	p_nfofr $p |- F/_ x oR R $= i0_nfofr f1_nfofr i1_nfofr i2_nfofr a_df-ofr f0_nfofr i1_nfofr a_sup_set_class a_cdm i2_nfofr a_sup_set_class a_cdm a_cin p_nfcv f0_nfofr i0_nfofr a_sup_set_class i1_nfofr a_sup_set_class a_cfv p_nfcv e0_nfofr f0_nfofr i0_nfofr a_sup_set_class i2_nfofr a_sup_set_class a_cfv p_nfcv f0_nfofr i0_nfofr a_sup_set_class i1_nfofr a_sup_set_class a_cfv i0_nfofr a_sup_set_class i2_nfofr a_sup_set_class a_cfv f1_nfofr p_nfbr i0_nfofr a_sup_set_class i1_nfofr a_sup_set_class a_cfv i0_nfofr a_sup_set_class i2_nfofr a_sup_set_class a_cfv f1_nfofr a_wbr f0_nfofr i0_nfofr i1_nfofr a_sup_set_class a_cdm i2_nfofr a_sup_set_class a_cdm a_cin p_nfral i0_nfofr a_sup_set_class i1_nfofr a_sup_set_class a_cfv i0_nfofr a_sup_set_class i2_nfofr a_sup_set_class a_cfv f1_nfofr a_wbr i0_nfofr i1_nfofr a_sup_set_class a_cdm i2_nfofr a_sup_set_class a_cdm a_cin a_wral i1_nfofr i2_nfofr f0_nfofr p_nfopab f0_nfofr f1_nfofr a_cofr i0_nfofr a_sup_set_class i1_nfofr a_sup_set_class a_cfv i0_nfofr a_sup_set_class i2_nfofr a_sup_set_class a_cfv f1_nfofr a_wbr i0_nfofr i1_nfofr a_sup_set_class a_cdm i2_nfofr a_sup_set_class a_cdm a_cin a_wral i1_nfofr i2_nfofr a_copab p_nfcxfr $.
$}

$(Value of an operation applied to two functions.  (Contributed by Mario
         Carneiro, 20-Jul-2014.) $)

${
	$v ph x A B C D R S F G V W  $.
	$d x A  $.
	$d f g x F  $.
	$d f g x G  $.
	$d x ph  $.
	$d x S  $.
	$d x  $.
	$d f g x R  $.
	f0_offval $f wff ph $.
	f1_offval $f set x $.
	f2_offval $f class A $.
	f3_offval $f class B $.
	f4_offval $f class C $.
	f5_offval $f class D $.
	f6_offval $f class R $.
	f7_offval $f class S $.
	f8_offval $f class F $.
	f9_offval $f class G $.
	f10_offval $f class V $.
	f11_offval $f class W $.
	i0_offval $f set f $.
	i1_offval $f set g $.
	e0_offval $e |- ( ph -> F Fn A ) $.
	e1_offval $e |- ( ph -> G Fn B ) $.
	e2_offval $e |- ( ph -> A e. V ) $.
	e3_offval $e |- ( ph -> B e. W ) $.
	e4_offval $e |- ( A i^i B ) = S $.
	e5_offval $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = C ) $.
	e6_offval $e |- ( ( ph /\ x e. B ) -> ( G ` x ) = D ) $.
	p_offval $p |- ( ph -> ( F oF R G ) = ( x e. S |-> ( C R D ) ) ) $= e0_offval e2_offval f2_offval f10_offval f8_offval p_fnex f0_offval f8_offval f2_offval a_wfn f2_offval f10_offval a_wcel f8_offval a_cvv a_wcel p_syl2anc e1_offval e3_offval f3_offval f11_offval f9_offval p_fnex f0_offval f9_offval f3_offval a_wfn f3_offval f11_offval a_wcel f9_offval a_cvv a_wcel p_syl2anc e0_offval f2_offval f8_offval p_fndm f0_offval f8_offval f2_offval a_wfn f8_offval a_cdm f2_offval a_wceq p_syl e1_offval f3_offval f9_offval p_fndm f0_offval f9_offval f3_offval a_wfn f9_offval a_cdm f3_offval a_wceq p_syl f0_offval f8_offval a_cdm f2_offval f9_offval a_cdm f3_offval p_ineq12d e4_offval f0_offval f8_offval a_cdm f9_offval a_cdm a_cin f2_offval f3_offval a_cin f7_offval p_syl6eq f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co p_mpteq1 f0_offval f8_offval a_cdm f9_offval a_cdm a_cin f7_offval a_wceq f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt f1_offval f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt a_wceq p_syl e2_offval e4_offval f2_offval f3_offval f10_offval p_inex1g f2_offval f10_offval a_wcel f7_offval f2_offval f3_offval a_cin a_cvv p_syl5eqelr f1_offval f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cvv p_mptexg f0_offval f2_offval f10_offval a_wcel f7_offval a_cvv a_wcel f1_offval f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt a_cvv a_wcel p_3syl f0_offval f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt f1_offval f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt a_cvv p_eqeltrd i0_offval a_sup_set_class f8_offval p_dmeq i1_offval a_sup_set_class f9_offval p_dmeq i0_offval a_sup_set_class f8_offval a_wceq i1_offval a_sup_set_class f9_offval a_wceq i0_offval a_sup_set_class a_cdm f8_offval a_cdm i1_offval a_sup_set_class a_cdm f9_offval a_cdm p_ineqan12d f1_offval a_sup_set_class i0_offval a_sup_set_class f8_offval p_fveq1 f1_offval a_sup_set_class i1_offval a_sup_set_class f9_offval p_fveq1 i0_offval a_sup_set_class f8_offval a_wceq i1_offval a_sup_set_class f9_offval a_wceq f1_offval a_sup_set_class i0_offval a_sup_set_class a_cfv f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class i1_offval a_sup_set_class a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval p_oveqan12d i0_offval a_sup_set_class f8_offval a_wceq i1_offval a_sup_set_class f9_offval a_wceq a_wa f1_offval i0_offval a_sup_set_class a_cdm i1_offval a_sup_set_class a_cdm a_cin f1_offval a_sup_set_class i0_offval a_sup_set_class a_cfv f1_offval a_sup_set_class i1_offval a_sup_set_class a_cfv f6_offval a_co f8_offval a_cdm f9_offval a_cdm a_cin f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co p_mpteq12dv f1_offval f6_offval i0_offval i1_offval a_df-of i0_offval i1_offval f8_offval f9_offval a_cvv a_cvv f1_offval i0_offval a_sup_set_class a_cdm i1_offval a_sup_set_class a_cdm a_cin f1_offval a_sup_set_class i0_offval a_sup_set_class a_cfv f1_offval a_sup_set_class i1_offval a_sup_set_class a_cfv f6_offval a_co a_cmpt f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt f6_offval a_cof a_cvv p_ovmpt2ga f0_offval f8_offval a_cvv a_wcel f9_offval a_cvv a_wcel f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt a_cvv a_wcel f8_offval f9_offval f6_offval a_cof a_co f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt a_wceq p_syl3anc e0_offval f2_offval f8_offval p_fndm f0_offval f8_offval f2_offval a_wfn f8_offval a_cdm f2_offval a_wceq p_syl e1_offval f3_offval f9_offval p_fndm f0_offval f9_offval f3_offval a_wfn f9_offval a_cdm f3_offval a_wceq p_syl f0_offval f8_offval a_cdm f2_offval f9_offval a_cdm f3_offval p_ineq12d e4_offval f0_offval f8_offval a_cdm f9_offval a_cdm a_cin f2_offval f3_offval a_cin f7_offval p_syl6eq f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co p_mpteq1 f0_offval f8_offval a_cdm f9_offval a_cdm a_cin f7_offval a_wceq f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt f1_offval f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt a_wceq p_syl e4_offval f2_offval f3_offval a_cin f7_offval f1_offval a_sup_set_class p_eleq2i f1_offval a_sup_set_class f2_offval f3_offval p_elin f1_offval a_sup_set_class f7_offval a_wcel f1_offval a_sup_set_class f2_offval f3_offval a_cin a_wcel f1_offval a_sup_set_class f2_offval a_wcel f1_offval a_sup_set_class f3_offval a_wcel a_wa p_bitr3i e5_offval f0_offval f1_offval a_sup_set_class f2_offval a_wcel f1_offval a_sup_set_class f8_offval a_cfv f4_offval a_wceq f1_offval a_sup_set_class f3_offval a_wcel p_adantrr e6_offval f0_offval f1_offval a_sup_set_class f3_offval a_wcel f1_offval a_sup_set_class f9_offval a_cfv f5_offval a_wceq f1_offval a_sup_set_class f2_offval a_wcel p_adantrl f0_offval f1_offval a_sup_set_class f2_offval a_wcel f1_offval a_sup_set_class f3_offval a_wcel a_wa a_wa f1_offval a_sup_set_class f8_offval a_cfv f4_offval f1_offval a_sup_set_class f9_offval a_cfv f5_offval f6_offval p_oveq12d f1_offval a_sup_set_class f7_offval a_wcel f0_offval f1_offval a_sup_set_class f2_offval a_wcel f1_offval a_sup_set_class f3_offval a_wcel a_wa f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co f4_offval f5_offval f6_offval a_co a_wceq p_sylan2b f0_offval f1_offval f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co f4_offval f5_offval f6_offval a_co p_mpteq2dva f0_offval f8_offval f9_offval f6_offval a_cof a_co f1_offval f8_offval a_cdm f9_offval a_cdm a_cin f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt f1_offval f7_offval f1_offval a_sup_set_class f8_offval a_cfv f1_offval a_sup_set_class f9_offval a_cfv f6_offval a_co a_cmpt f1_offval f7_offval f4_offval f5_offval f6_offval a_co a_cmpt p_3eqtrd $.
$}

$(Value of a relation applied to two functions.  (Contributed by Mario
         Carneiro, 28-Jul-2014.) $)

${
	$v ph x A B C D R S F G V W  $.
	$d x A  $.
	$d f g x F  $.
	$d f g x G  $.
	$d x ph  $.
	$d x S  $.
	$d x  $.
	$d f g x R  $.
	f0_ofrfval $f wff ph $.
	f1_ofrfval $f set x $.
	f2_ofrfval $f class A $.
	f3_ofrfval $f class B $.
	f4_ofrfval $f class C $.
	f5_ofrfval $f class D $.
	f6_ofrfval $f class R $.
	f7_ofrfval $f class S $.
	f8_ofrfval $f class F $.
	f9_ofrfval $f class G $.
	f10_ofrfval $f class V $.
	f11_ofrfval $f class W $.
	i0_ofrfval $f set f $.
	i1_ofrfval $f set g $.
	e0_ofrfval $e |- ( ph -> F Fn A ) $.
	e1_ofrfval $e |- ( ph -> G Fn B ) $.
	e2_ofrfval $e |- ( ph -> A e. V ) $.
	e3_ofrfval $e |- ( ph -> B e. W ) $.
	e4_ofrfval $e |- ( A i^i B ) = S $.
	e5_ofrfval $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = C ) $.
	e6_ofrfval $e |- ( ( ph /\ x e. B ) -> ( G ` x ) = D ) $.
	p_ofrfval $p |- ( ph -> ( F oR R G <-> A. x e. S C R D ) ) $= e0_ofrfval e2_ofrfval f2_ofrfval f10_ofrfval f8_ofrfval p_fnex f0_ofrfval f8_ofrfval f2_ofrfval a_wfn f2_ofrfval f10_ofrfval a_wcel f8_ofrfval a_cvv a_wcel p_syl2anc e1_ofrfval e3_ofrfval f3_ofrfval f11_ofrfval f9_ofrfval p_fnex f0_ofrfval f9_ofrfval f3_ofrfval a_wfn f3_ofrfval f11_ofrfval a_wcel f9_ofrfval a_cvv a_wcel p_syl2anc i0_ofrfval a_sup_set_class f8_ofrfval p_dmeq i1_ofrfval a_sup_set_class f9_ofrfval p_dmeq i0_ofrfval a_sup_set_class f8_ofrfval a_wceq i1_ofrfval a_sup_set_class f9_ofrfval a_wceq i0_ofrfval a_sup_set_class a_cdm f8_ofrfval a_cdm i1_ofrfval a_sup_set_class a_cdm f9_ofrfval a_cdm p_ineqan12d f1_ofrfval a_sup_set_class i0_ofrfval a_sup_set_class f8_ofrfval p_fveq1 f1_ofrfval a_sup_set_class i1_ofrfval a_sup_set_class f9_ofrfval p_fveq1 i0_ofrfval a_sup_set_class f8_ofrfval a_wceq i1_ofrfval a_sup_set_class f9_ofrfval a_wceq f1_ofrfval a_sup_set_class i0_ofrfval a_sup_set_class a_cfv f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f1_ofrfval a_sup_set_class i1_ofrfval a_sup_set_class a_cfv f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f6_ofrfval p_breqan12d i0_ofrfval a_sup_set_class f8_ofrfval a_wceq i1_ofrfval a_sup_set_class f9_ofrfval a_wceq a_wa f1_ofrfval a_sup_set_class i0_ofrfval a_sup_set_class a_cfv f1_ofrfval a_sup_set_class i1_ofrfval a_sup_set_class a_cfv f6_ofrfval a_wbr f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f6_ofrfval a_wbr f1_ofrfval i0_ofrfval a_sup_set_class a_cdm i1_ofrfval a_sup_set_class a_cdm a_cin f8_ofrfval a_cdm f9_ofrfval a_cdm a_cin p_raleqbidv f1_ofrfval f6_ofrfval i0_ofrfval i1_ofrfval a_df-ofr f1_ofrfval a_sup_set_class i0_ofrfval a_sup_set_class a_cfv f1_ofrfval a_sup_set_class i1_ofrfval a_sup_set_class a_cfv f6_ofrfval a_wbr f1_ofrfval i0_ofrfval a_sup_set_class a_cdm i1_ofrfval a_sup_set_class a_cdm a_cin a_wral f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f6_ofrfval a_wbr f1_ofrfval f8_ofrfval a_cdm f9_ofrfval a_cdm a_cin a_wral i0_ofrfval i1_ofrfval f8_ofrfval f9_ofrfval f6_ofrfval a_cofr a_cvv a_cvv p_brabga f0_ofrfval f8_ofrfval a_cvv a_wcel f9_ofrfval a_cvv a_wcel f8_ofrfval f9_ofrfval f6_ofrfval a_cofr a_wbr f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f6_ofrfval a_wbr f1_ofrfval f8_ofrfval a_cdm f9_ofrfval a_cdm a_cin a_wral a_wb p_syl2anc e0_ofrfval f2_ofrfval f8_ofrfval p_fndm f0_ofrfval f8_ofrfval f2_ofrfval a_wfn f8_ofrfval a_cdm f2_ofrfval a_wceq p_syl e1_ofrfval f3_ofrfval f9_ofrfval p_fndm f0_ofrfval f9_ofrfval f3_ofrfval a_wfn f9_ofrfval a_cdm f3_ofrfval a_wceq p_syl f0_ofrfval f8_ofrfval a_cdm f2_ofrfval f9_ofrfval a_cdm f3_ofrfval p_ineq12d e4_ofrfval f0_ofrfval f8_ofrfval a_cdm f9_ofrfval a_cdm a_cin f2_ofrfval f3_ofrfval a_cin f7_ofrfval p_syl6eq f0_ofrfval f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f6_ofrfval a_wbr f1_ofrfval f8_ofrfval a_cdm f9_ofrfval a_cdm a_cin f7_ofrfval p_raleqdv e4_ofrfval f2_ofrfval f3_ofrfval p_inss1 f7_ofrfval f2_ofrfval f3_ofrfval a_cin f2_ofrfval p_eqsstr3i f7_ofrfval f2_ofrfval f1_ofrfval a_sup_set_class p_sseli e5_ofrfval f1_ofrfval a_sup_set_class f7_ofrfval a_wcel f0_ofrfval f1_ofrfval a_sup_set_class f2_ofrfval a_wcel f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f4_ofrfval a_wceq p_sylan2 e4_ofrfval f2_ofrfval f3_ofrfval p_inss2 f7_ofrfval f2_ofrfval f3_ofrfval a_cin f3_ofrfval p_eqsstr3i f7_ofrfval f3_ofrfval f1_ofrfval a_sup_set_class p_sseli e6_ofrfval f1_ofrfval a_sup_set_class f7_ofrfval a_wcel f0_ofrfval f1_ofrfval a_sup_set_class f3_ofrfval a_wcel f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f5_ofrfval a_wceq p_sylan2 f0_ofrfval f1_ofrfval a_sup_set_class f7_ofrfval a_wcel a_wa f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f4_ofrfval f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f5_ofrfval f6_ofrfval p_breq12d f0_ofrfval f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f6_ofrfval a_wbr f4_ofrfval f5_ofrfval f6_ofrfval a_wbr f1_ofrfval f7_ofrfval p_ralbidva f0_ofrfval f8_ofrfval f9_ofrfval f6_ofrfval a_cofr a_wbr f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f6_ofrfval a_wbr f1_ofrfval f8_ofrfval a_cdm f9_ofrfval a_cdm a_cin a_wral f1_ofrfval a_sup_set_class f8_ofrfval a_cfv f1_ofrfval a_sup_set_class f9_ofrfval a_cfv f6_ofrfval a_wbr f1_ofrfval f7_ofrfval a_wral f4_ofrfval f5_ofrfval f6_ofrfval a_wbr f1_ofrfval f7_ofrfval a_wral p_3bitrd $.
$}

$(Evaluate a function operation at a point.  (Contributed by Mario
         Carneiro, 20-Jul-2014.) $)

${
	$v ph A B C D R S F G V W X  $.
	$d x A  $.
	$d x F  $.
	$d x G  $.
	$d x ph  $.
	$d x S  $.
	$d x X  $.
	$d x R  $.
	f0_ofval $f wff ph $.
	f1_ofval $f class A $.
	f2_ofval $f class B $.
	f3_ofval $f class C $.
	f4_ofval $f class D $.
	f5_ofval $f class R $.
	f6_ofval $f class S $.
	f7_ofval $f class F $.
	f8_ofval $f class G $.
	f9_ofval $f class V $.
	f10_ofval $f class W $.
	f11_ofval $f class X $.
	i0_ofval $f set x $.
	e0_ofval $e |- ( ph -> F Fn A ) $.
	e1_ofval $e |- ( ph -> G Fn B ) $.
	e2_ofval $e |- ( ph -> A e. V ) $.
	e3_ofval $e |- ( ph -> B e. W ) $.
	e4_ofval $e |- ( A i^i B ) = S $.
	e5_ofval $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
	e6_ofval $e |- ( ( ph /\ X e. B ) -> ( G ` X ) = D ) $.
	p_ofval $p |- ( ( ph /\ X e. S ) -> ( ( F oF R G ) ` X ) = ( C R D ) ) $= e0_ofval e1_ofval e2_ofval e3_ofval e4_ofval f0_ofval i0_ofval a_sup_set_class f1_ofval a_wcel a_wa i0_ofval a_sup_set_class f7_ofval a_cfv p_eqidd f0_ofval i0_ofval a_sup_set_class f2_ofval a_wcel a_wa i0_ofval a_sup_set_class f8_ofval a_cfv p_eqidd f0_ofval i0_ofval f1_ofval f2_ofval i0_ofval a_sup_set_class f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f5_ofval f6_ofval f7_ofval f8_ofval f9_ofval f10_ofval p_offval f0_ofval f11_ofval f7_ofval f8_ofval f5_ofval a_cof a_co i0_ofval f6_ofval i0_ofval a_sup_set_class f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f5_ofval a_co a_cmpt p_fveq1d f0_ofval f11_ofval f7_ofval f8_ofval f5_ofval a_cof a_co a_cfv f11_ofval i0_ofval f6_ofval i0_ofval a_sup_set_class f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f5_ofval a_co a_cmpt a_cfv a_wceq f11_ofval f6_ofval a_wcel p_adantr i0_ofval a_sup_set_class f11_ofval f7_ofval p_fveq2 i0_ofval a_sup_set_class f11_ofval f8_ofval p_fveq2 i0_ofval a_sup_set_class f11_ofval a_wceq i0_ofval a_sup_set_class f7_ofval a_cfv f11_ofval f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f11_ofval f8_ofval a_cfv f5_ofval p_oveq12d i0_ofval f6_ofval i0_ofval a_sup_set_class f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f5_ofval a_co a_cmpt p_eqid f11_ofval f7_ofval a_cfv f11_ofval f8_ofval a_cfv f5_ofval p_ovex i0_ofval f11_ofval i0_ofval a_sup_set_class f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f5_ofval a_co f11_ofval f7_ofval a_cfv f11_ofval f8_ofval a_cfv f5_ofval a_co f6_ofval i0_ofval f6_ofval i0_ofval a_sup_set_class f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f5_ofval a_co a_cmpt p_fvmpt f11_ofval f6_ofval a_wcel f11_ofval i0_ofval f6_ofval i0_ofval a_sup_set_class f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f5_ofval a_co a_cmpt a_cfv f11_ofval f7_ofval a_cfv f11_ofval f8_ofval a_cfv f5_ofval a_co a_wceq f0_ofval p_adantl e4_ofval f1_ofval f2_ofval p_inss1 f6_ofval f1_ofval f2_ofval a_cin f1_ofval p_eqsstr3i f6_ofval f1_ofval f11_ofval p_sseli e5_ofval f11_ofval f6_ofval a_wcel f0_ofval f11_ofval f1_ofval a_wcel f11_ofval f7_ofval a_cfv f3_ofval a_wceq p_sylan2 e4_ofval f1_ofval f2_ofval p_inss2 f6_ofval f1_ofval f2_ofval a_cin f2_ofval p_eqsstr3i f6_ofval f2_ofval f11_ofval p_sseli e6_ofval f11_ofval f6_ofval a_wcel f0_ofval f11_ofval f2_ofval a_wcel f11_ofval f8_ofval a_cfv f4_ofval a_wceq p_sylan2 f0_ofval f11_ofval f6_ofval a_wcel a_wa f11_ofval f7_ofval a_cfv f3_ofval f11_ofval f8_ofval a_cfv f4_ofval f5_ofval p_oveq12d f0_ofval f11_ofval f6_ofval a_wcel a_wa f11_ofval f7_ofval f8_ofval f5_ofval a_cof a_co a_cfv f11_ofval i0_ofval f6_ofval i0_ofval a_sup_set_class f7_ofval a_cfv i0_ofval a_sup_set_class f8_ofval a_cfv f5_ofval a_co a_cmpt a_cfv f11_ofval f7_ofval a_cfv f11_ofval f8_ofval a_cfv f5_ofval a_co f3_ofval f4_ofval f5_ofval a_co p_3eqtrd $.
$}

$(Exhibit a function relation at a point.  (Contributed by Mario
         Carneiro, 28-Jul-2014.) $)

${
	$v ph A B C D R S F G V W X  $.
	$d x A  $.
	$d x F  $.
	$d x G  $.
	$d x ph  $.
	$d x S  $.
	$d x X  $.
	$d x R  $.
	f0_ofrval $f wff ph $.
	f1_ofrval $f class A $.
	f2_ofrval $f class B $.
	f3_ofrval $f class C $.
	f4_ofrval $f class D $.
	f5_ofrval $f class R $.
	f6_ofrval $f class S $.
	f7_ofrval $f class F $.
	f8_ofrval $f class G $.
	f9_ofrval $f class V $.
	f10_ofrval $f class W $.
	f11_ofrval $f class X $.
	i0_ofrval $f set x $.
	e0_ofrval $e |- ( ph -> F Fn A ) $.
	e1_ofrval $e |- ( ph -> G Fn B ) $.
	e2_ofrval $e |- ( ph -> A e. V ) $.
	e3_ofrval $e |- ( ph -> B e. W ) $.
	e4_ofrval $e |- ( A i^i B ) = S $.
	e5_ofrval $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
	e6_ofrval $e |- ( ( ph /\ X e. B ) -> ( G ` X ) = D ) $.
	p_ofrval $p |- ( ( ph /\ F oR R G /\ X e. S ) -> C R D ) $= e0_ofrval e1_ofrval e2_ofrval e3_ofrval e4_ofrval f0_ofrval i0_ofrval a_sup_set_class f1_ofrval a_wcel a_wa i0_ofrval a_sup_set_class f7_ofrval a_cfv p_eqidd f0_ofrval i0_ofrval a_sup_set_class f2_ofrval a_wcel a_wa i0_ofrval a_sup_set_class f8_ofrval a_cfv p_eqidd f0_ofrval i0_ofrval f1_ofrval f2_ofrval i0_ofrval a_sup_set_class f7_ofrval a_cfv i0_ofrval a_sup_set_class f8_ofrval a_cfv f5_ofrval f6_ofrval f7_ofrval f8_ofrval f9_ofrval f10_ofrval p_ofrfval f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr i0_ofrval a_sup_set_class f7_ofrval a_cfv i0_ofrval a_sup_set_class f8_ofrval a_cfv f5_ofrval a_wbr i0_ofrval f6_ofrval a_wral p_biimpa i0_ofrval a_sup_set_class f11_ofrval f7_ofrval p_fveq2 i0_ofrval a_sup_set_class f11_ofrval f8_ofrval p_fveq2 i0_ofrval a_sup_set_class f11_ofrval a_wceq i0_ofrval a_sup_set_class f7_ofrval a_cfv f11_ofrval f7_ofrval a_cfv i0_ofrval a_sup_set_class f8_ofrval a_cfv f11_ofrval f8_ofrval a_cfv f5_ofrval p_breq12d i0_ofrval a_sup_set_class f7_ofrval a_cfv i0_ofrval a_sup_set_class f8_ofrval a_cfv f5_ofrval a_wbr f11_ofrval f7_ofrval a_cfv f11_ofrval f8_ofrval a_cfv f5_ofrval a_wbr i0_ofrval f11_ofrval f6_ofrval p_rspccv f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr a_wa i0_ofrval a_sup_set_class f7_ofrval a_cfv i0_ofrval a_sup_set_class f8_ofrval a_cfv f5_ofrval a_wbr i0_ofrval f6_ofrval a_wral f11_ofrval f6_ofrval a_wcel f11_ofrval f7_ofrval a_cfv f11_ofrval f8_ofrval a_cfv f5_ofrval a_wbr a_wi p_syl f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel f11_ofrval f7_ofrval a_cfv f11_ofrval f8_ofrval a_cfv f5_ofrval a_wbr p_3impia f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel p_simp1 e4_ofrval f1_ofrval f2_ofrval p_inss1 f6_ofrval f1_ofrval f2_ofrval a_cin f1_ofrval p_eqsstr3i f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel p_simp3 f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel a_w3a f6_ofrval f1_ofrval f11_ofrval p_sseldi e5_ofrval f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel a_w3a f0_ofrval f11_ofrval f1_ofrval a_wcel f11_ofrval f7_ofrval a_cfv f3_ofrval a_wceq p_syl2anc f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel p_simp1 e4_ofrval f1_ofrval f2_ofrval p_inss2 f6_ofrval f1_ofrval f2_ofrval a_cin f2_ofrval p_eqsstr3i f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel p_simp3 f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel a_w3a f6_ofrval f2_ofrval f11_ofrval p_sseldi e6_ofrval f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel a_w3a f0_ofrval f11_ofrval f2_ofrval a_wcel f11_ofrval f8_ofrval a_cfv f4_ofrval a_wceq p_syl2anc f0_ofrval f7_ofrval f8_ofrval f5_ofrval a_cofr a_wbr f11_ofrval f6_ofrval a_wcel a_w3a f11_ofrval f7_ofrval a_cfv f11_ofrval f8_ofrval a_cfv f3_ofrval f4_ofrval f5_ofrval p_3brtr3d $.
$}

$(The function operation produces a function.  (Contributed by Mario
       Carneiro, 22-Jul-2014.) $)

${
	$v ph A B R S F G V W  $.
	$d x A  $.
	$d x F  $.
	$d x G  $.
	$d x ph  $.
	$d x S  $.
	$d x  $.
	$d x R  $.
	f0_offn $f wff ph $.
	f1_offn $f class A $.
	f2_offn $f class B $.
	f3_offn $f class R $.
	f4_offn $f class S $.
	f5_offn $f class F $.
	f6_offn $f class G $.
	f7_offn $f class V $.
	f8_offn $f class W $.
	i0_offn $f set x $.
	e0_offn $e |- ( ph -> F Fn A ) $.
	e1_offn $e |- ( ph -> G Fn B ) $.
	e2_offn $e |- ( ph -> A e. V ) $.
	e3_offn $e |- ( ph -> B e. W ) $.
	e4_offn $e |- ( A i^i B ) = S $.
	p_offn $p |- ( ph -> ( F oF R G ) Fn S ) $= i0_offn a_sup_set_class f5_offn a_cfv i0_offn a_sup_set_class f6_offn a_cfv f3_offn p_ovex i0_offn f4_offn i0_offn a_sup_set_class f5_offn a_cfv i0_offn a_sup_set_class f6_offn a_cfv f3_offn a_co a_cmpt p_eqid i0_offn f4_offn i0_offn a_sup_set_class f5_offn a_cfv i0_offn a_sup_set_class f6_offn a_cfv f3_offn a_co i0_offn f4_offn i0_offn a_sup_set_class f5_offn a_cfv i0_offn a_sup_set_class f6_offn a_cfv f3_offn a_co a_cmpt p_fnmpti e0_offn e1_offn e2_offn e3_offn e4_offn f0_offn i0_offn a_sup_set_class f1_offn a_wcel a_wa i0_offn a_sup_set_class f5_offn a_cfv p_eqidd f0_offn i0_offn a_sup_set_class f2_offn a_wcel a_wa i0_offn a_sup_set_class f6_offn a_cfv p_eqidd f0_offn i0_offn f1_offn f2_offn i0_offn a_sup_set_class f5_offn a_cfv i0_offn a_sup_set_class f6_offn a_cfv f3_offn f4_offn f5_offn f6_offn f7_offn f8_offn p_offval f0_offn f4_offn f5_offn f6_offn f3_offn a_cof a_co i0_offn f4_offn i0_offn a_sup_set_class f5_offn a_cfv i0_offn a_sup_set_class f6_offn a_cfv f3_offn a_co a_cmpt p_fneq1d f0_offn f5_offn f6_offn f3_offn a_cof a_co f4_offn a_wfn i0_offn f4_offn i0_offn a_sup_set_class f5_offn a_cfv i0_offn a_sup_set_class f6_offn a_cfv f3_offn a_co a_cmpt f4_offn a_wfn p_mpbiri $.
$}

$(Function value of a pointwise composition.  (Contributed by Stefan O'Rear,
     5-Oct-2014.)  (Proof shortened by Mario Carneiro, 5-Jun-2015.) $)

${
	$v A R F G V X  $.
	f0_fnfvof $f class A $.
	f1_fnfvof $f class R $.
	f2_fnfvof $f class F $.
	f3_fnfvof $f class G $.
	f4_fnfvof $f class V $.
	f5_fnfvof $f class X $.
	p_fnfvof $p |- ( ( ( F Fn A /\ G Fn A ) /\ ( A e. V /\ X e. A ) ) -> ( ( F oF R G ) ` X ) = ( ( F ` X ) R ( G ` X ) ) ) $= f2_fnfvof f0_fnfvof a_wfn f3_fnfvof f0_fnfvof a_wfn f0_fnfvof f4_fnfvof a_wcel p_simpll f2_fnfvof f0_fnfvof a_wfn f3_fnfvof f0_fnfvof a_wfn f0_fnfvof f4_fnfvof a_wcel p_simplr f2_fnfvof f0_fnfvof a_wfn f3_fnfvof f0_fnfvof a_wfn a_wa f0_fnfvof f4_fnfvof a_wcel p_simpr f2_fnfvof f0_fnfvof a_wfn f3_fnfvof f0_fnfvof a_wfn a_wa f0_fnfvof f4_fnfvof a_wcel p_simpr f0_fnfvof p_inidm f2_fnfvof f0_fnfvof a_wfn f3_fnfvof f0_fnfvof a_wfn a_wa f0_fnfvof f4_fnfvof a_wcel a_wa f5_fnfvof f0_fnfvof a_wcel a_wa f5_fnfvof f2_fnfvof a_cfv p_eqidd f2_fnfvof f0_fnfvof a_wfn f3_fnfvof f0_fnfvof a_wfn a_wa f0_fnfvof f4_fnfvof a_wcel a_wa f5_fnfvof f0_fnfvof a_wcel a_wa f5_fnfvof f3_fnfvof a_cfv p_eqidd f2_fnfvof f0_fnfvof a_wfn f3_fnfvof f0_fnfvof a_wfn a_wa f0_fnfvof f4_fnfvof a_wcel a_wa f0_fnfvof f0_fnfvof f5_fnfvof f2_fnfvof a_cfv f5_fnfvof f3_fnfvof a_cfv f1_fnfvof f0_fnfvof f2_fnfvof f3_fnfvof f4_fnfvof f4_fnfvof f5_fnfvof p_ofval f2_fnfvof f0_fnfvof a_wfn f3_fnfvof f0_fnfvof a_wfn a_wa f0_fnfvof f4_fnfvof a_wcel f5_fnfvof f0_fnfvof a_wcel f5_fnfvof f2_fnfvof f3_fnfvof f1_fnfvof a_cof a_co a_cfv f5_fnfvof f2_fnfvof a_cfv f5_fnfvof f3_fnfvof a_cfv f1_fnfvof a_co a_wceq p_anasss $.
$}

$(General value of ` ( F oF R G ) ` with no assumptions on functionality
       of ` F ` and ` G ` .  (Contributed by Stefan O'Rear, 24-Jan-2015.) $)

${
	$v x R F G V W  $.
	$d F x a b  $.
	$d G x a b  $.
	$d V x  $.
	$d W x  $.
	$d R x a b  $.
	$d x  $.
	f0_offval3 $f set x $.
	f1_offval3 $f class R $.
	f2_offval3 $f class F $.
	f3_offval3 $f class G $.
	f4_offval3 $f class V $.
	f5_offval3 $f class W $.
	i0_offval3 $f set a $.
	i1_offval3 $f set b $.
	p_offval3 $p |- ( ( F e. V /\ G e. W ) -> ( F oF R G ) = ( x e. ( dom F i^i dom G ) |-> ( ( F ` x ) R ( G ` x ) ) ) ) $= f2_offval3 f4_offval3 p_elex f2_offval3 f4_offval3 a_wcel f2_offval3 a_cvv a_wcel f3_offval3 f5_offval3 a_wcel p_adantr f3_offval3 f5_offval3 p_elex f3_offval3 f5_offval3 a_wcel f3_offval3 a_cvv a_wcel f2_offval3 f4_offval3 a_wcel p_adantl f2_offval3 f4_offval3 p_dmexg f2_offval3 a_cdm f3_offval3 a_cdm a_cvv p_inex1g f0_offval3 f2_offval3 a_cdm f3_offval3 a_cdm a_cin f0_offval3 a_sup_set_class f2_offval3 a_cfv f0_offval3 a_sup_set_class f3_offval3 a_cfv f1_offval3 a_co a_cvv p_mptexg f2_offval3 f4_offval3 a_wcel f2_offval3 a_cdm a_cvv a_wcel f2_offval3 a_cdm f3_offval3 a_cdm a_cin a_cvv a_wcel f0_offval3 f2_offval3 a_cdm f3_offval3 a_cdm a_cin f0_offval3 a_sup_set_class f2_offval3 a_cfv f0_offval3 a_sup_set_class f3_offval3 a_cfv f1_offval3 a_co a_cmpt a_cvv a_wcel p_3syl f2_offval3 f4_offval3 a_wcel f0_offval3 f2_offval3 a_cdm f3_offval3 a_cdm a_cin f0_offval3 a_sup_set_class f2_offval3 a_cfv f0_offval3 a_sup_set_class f3_offval3 a_cfv f1_offval3 a_co a_cmpt a_cvv a_wcel f3_offval3 f5_offval3 a_wcel p_adantr i0_offval3 a_sup_set_class f2_offval3 p_dmeq i1_offval3 a_sup_set_class f3_offval3 p_dmeq i0_offval3 a_sup_set_class f2_offval3 a_wceq i1_offval3 a_sup_set_class f3_offval3 a_wceq i0_offval3 a_sup_set_class a_cdm f2_offval3 a_cdm i1_offval3 a_sup_set_class a_cdm f3_offval3 a_cdm p_ineqan12d f0_offval3 a_sup_set_class i0_offval3 a_sup_set_class f2_offval3 p_fveq1 f0_offval3 a_sup_set_class i1_offval3 a_sup_set_class f3_offval3 p_fveq1 i0_offval3 a_sup_set_class f2_offval3 a_wceq i1_offval3 a_sup_set_class f3_offval3 a_wceq f0_offval3 a_sup_set_class i0_offval3 a_sup_set_class a_cfv f0_offval3 a_sup_set_class f2_offval3 a_cfv f0_offval3 a_sup_set_class i1_offval3 a_sup_set_class a_cfv f0_offval3 a_sup_set_class f3_offval3 a_cfv f1_offval3 p_oveqan12d i0_offval3 a_sup_set_class f2_offval3 a_wceq i1_offval3 a_sup_set_class f3_offval3 a_wceq a_wa f0_offval3 i0_offval3 a_sup_set_class a_cdm i1_offval3 a_sup_set_class a_cdm a_cin f0_offval3 a_sup_set_class i0_offval3 a_sup_set_class a_cfv f0_offval3 a_sup_set_class i1_offval3 a_sup_set_class a_cfv f1_offval3 a_co f2_offval3 a_cdm f3_offval3 a_cdm a_cin f0_offval3 a_sup_set_class f2_offval3 a_cfv f0_offval3 a_sup_set_class f3_offval3 a_cfv f1_offval3 a_co p_mpteq12dv f0_offval3 f1_offval3 i0_offval3 i1_offval3 a_df-of i0_offval3 i1_offval3 f2_offval3 f3_offval3 a_cvv a_cvv f0_offval3 i0_offval3 a_sup_set_class a_cdm i1_offval3 a_sup_set_class a_cdm a_cin f0_offval3 a_sup_set_class i0_offval3 a_sup_set_class a_cfv f0_offval3 a_sup_set_class i1_offval3 a_sup_set_class a_cfv f1_offval3 a_co a_cmpt f0_offval3 f2_offval3 a_cdm f3_offval3 a_cdm a_cin f0_offval3 a_sup_set_class f2_offval3 a_cfv f0_offval3 a_sup_set_class f3_offval3 a_cfv f1_offval3 a_co a_cmpt f1_offval3 a_cof a_cvv p_ovmpt2ga f2_offval3 f4_offval3 a_wcel f3_offval3 f5_offval3 a_wcel a_wa f2_offval3 a_cvv a_wcel f3_offval3 a_cvv a_wcel f0_offval3 f2_offval3 a_cdm f3_offval3 a_cdm a_cin f0_offval3 a_sup_set_class f2_offval3 a_cfv f0_offval3 a_sup_set_class f3_offval3 a_cfv f1_offval3 a_co a_cmpt a_cvv a_wcel f2_offval3 f3_offval3 f1_offval3 a_cof a_co f0_offval3 f2_offval3 a_cdm f3_offval3 a_cdm a_cin f0_offval3 a_sup_set_class f2_offval3 a_cfv f0_offval3 a_sup_set_class f3_offval3 a_cfv f1_offval3 a_co a_cmpt a_wceq p_syl3anc $.
$}

$(Pointwise combination commutes with restriction.  (Contributed by Stefan
       O'Rear, 24-Jan-2015.) $)

${
	$v D R F G V W  $.
	$d F x  $.
	$d G x  $.
	$d V x  $.
	$d W x  $.
	$d R x  $.
	$d D x  $.
	f0_offres $f class D $.
	f1_offres $f class R $.
	f2_offres $f class F $.
	f3_offres $f class G $.
	f4_offres $f class V $.
	f5_offres $f class W $.
	i0_offres $f set x $.
	p_offres $p |- ( ( F e. V /\ G e. W ) -> ( ( F oF R G ) |` D ) = ( ( F |` D ) oF R ( G |` D ) ) ) $= f2_offres a_cdm f3_offres a_cdm a_cin f0_offres p_inss2 f2_offres a_cdm f3_offres a_cdm a_cin f0_offres a_cin f0_offres i0_offres a_sup_set_class p_sseli i0_offres a_sup_set_class f0_offres f2_offres p_fvres i0_offres a_sup_set_class f0_offres f3_offres p_fvres i0_offres a_sup_set_class f0_offres a_wcel i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f2_offres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres a_cfv f1_offres p_oveq12d i0_offres a_sup_set_class f2_offres a_cdm f3_offres a_cdm a_cin f0_offres a_cin a_wcel i0_offres a_sup_set_class f0_offres a_wcel i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co i0_offres a_sup_set_class f2_offres a_cfv i0_offres a_sup_set_class f3_offres a_cfv f1_offres a_co a_wceq p_syl i0_offres f2_offres a_cdm f3_offres a_cdm a_cin f0_offres a_cin i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co i0_offres a_sup_set_class f2_offres a_cfv i0_offres a_sup_set_class f3_offres a_cfv f1_offres a_co p_mpteq2ia f0_offres f2_offres a_cdm f3_offres a_cdm p_inindi f2_offres a_cdm f3_offres a_cdm a_cin f0_offres p_incom f2_offres f0_offres p_dmres f3_offres f0_offres p_dmres f2_offres f0_offres a_cres a_cdm f0_offres f2_offres a_cdm a_cin f3_offres f0_offres a_cres a_cdm f0_offres f3_offres a_cdm a_cin p_ineq12i f0_offres f2_offres a_cdm f3_offres a_cdm a_cin a_cin f0_offres f2_offres a_cdm a_cin f0_offres f3_offres a_cdm a_cin a_cin f2_offres a_cdm f3_offres a_cdm a_cin f0_offres a_cin f2_offres f0_offres a_cres a_cdm f3_offres f0_offres a_cres a_cdm a_cin p_3eqtr4ri i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co p_eqid i0_offres f2_offres f0_offres a_cres a_cdm f3_offres f0_offres a_cres a_cdm a_cin i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co f2_offres a_cdm f3_offres a_cdm a_cin f0_offres a_cin i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co p_mpteq12i i0_offres f2_offres a_cdm f3_offres a_cdm a_cin f0_offres i0_offres a_sup_set_class f2_offres a_cfv i0_offres a_sup_set_class f3_offres a_cfv f1_offres a_co p_resmpt3 i0_offres f2_offres a_cdm f3_offres a_cdm a_cin f0_offres a_cin i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co a_cmpt i0_offres f2_offres a_cdm f3_offres a_cdm a_cin f0_offres a_cin i0_offres a_sup_set_class f2_offres a_cfv i0_offres a_sup_set_class f3_offres a_cfv f1_offres a_co a_cmpt i0_offres f2_offres f0_offres a_cres a_cdm f3_offres f0_offres a_cres a_cdm a_cin i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co a_cmpt i0_offres f2_offres a_cdm f3_offres a_cdm a_cin i0_offres a_sup_set_class f2_offres a_cfv i0_offres a_sup_set_class f3_offres a_cfv f1_offres a_co a_cmpt f0_offres a_cres p_3eqtr4ri i0_offres f1_offres f2_offres f3_offres f4_offres f5_offres p_offval3 f2_offres f4_offres a_wcel f3_offres f5_offres a_wcel a_wa f2_offres f3_offres f1_offres a_cof a_co i0_offres f2_offres a_cdm f3_offres a_cdm a_cin i0_offres a_sup_set_class f2_offres a_cfv i0_offres a_sup_set_class f3_offres a_cfv f1_offres a_co a_cmpt f0_offres p_reseq1d f2_offres f0_offres f4_offres p_resexg f3_offres f0_offres f5_offres p_resexg i0_offres f1_offres f2_offres f0_offres a_cres f3_offres f0_offres a_cres a_cvv a_cvv p_offval3 f2_offres f4_offres a_wcel f2_offres f0_offres a_cres a_cvv a_wcel f3_offres f0_offres a_cres a_cvv a_wcel f2_offres f0_offres a_cres f3_offres f0_offres a_cres f1_offres a_cof a_co i0_offres f2_offres f0_offres a_cres a_cdm f3_offres f0_offres a_cres a_cdm a_cin i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co a_cmpt a_wceq f3_offres f5_offres a_wcel p_syl2an f2_offres f4_offres a_wcel f3_offres f5_offres a_wcel a_wa i0_offres f2_offres a_cdm f3_offres a_cdm a_cin i0_offres a_sup_set_class f2_offres a_cfv i0_offres a_sup_set_class f3_offres a_cfv f1_offres a_co a_cmpt f0_offres a_cres i0_offres f2_offres f0_offres a_cres a_cdm f3_offres f0_offres a_cres a_cdm a_cin i0_offres a_sup_set_class f2_offres f0_offres a_cres a_cfv i0_offres a_sup_set_class f3_offres f0_offres a_cres a_cfv f1_offres a_co a_cmpt f2_offres f3_offres f1_offres a_cof a_co f0_offres a_cres f2_offres f0_offres a_cres f3_offres f0_offres a_cres f1_offres a_cof a_co p_3eqtr4a $.
$}

$(The function operation produces a function.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)

${
	$v ph x y A B C R S T U F G V W  $.
	$d z A  $.
	$d z C  $.
	$d y z G  $.
	$d x y z ph  $.
	$d x y S  $.
	$d x y T  $.
	$d x y z F  $.
	$d x y z R  $.
	$d x y z U  $.
	f0_off $f wff ph $.
	f1_off $f set x $.
	f2_off $f set y $.
	f3_off $f class A $.
	f4_off $f class B $.
	f5_off $f class C $.
	f6_off $f class R $.
	f7_off $f class S $.
	f8_off $f class T $.
	f9_off $f class U $.
	f10_off $f class F $.
	f11_off $f class G $.
	f12_off $f class V $.
	f13_off $f class W $.
	i0_off $f set z $.
	e0_off $e |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U ) $.
	e1_off $e |- ( ph -> F : A --> S ) $.
	e2_off $e |- ( ph -> G : B --> T ) $.
	e3_off $e |- ( ph -> A e. V ) $.
	e4_off $e |- ( ph -> B e. W ) $.
	e5_off $e |- ( A i^i B ) = C $.
	p_off $p |- ( ph -> ( F oF R G ) : C --> U ) $= e1_off e5_off f3_off f4_off p_inss1 f5_off f3_off f4_off a_cin f3_off p_eqsstr3i f5_off f3_off i0_off a_sup_set_class p_sseli f3_off f7_off i0_off a_sup_set_class f10_off p_ffvelrn f0_off f3_off f7_off f10_off a_wf i0_off a_sup_set_class f3_off a_wcel i0_off a_sup_set_class f10_off a_cfv f7_off a_wcel i0_off a_sup_set_class f5_off a_wcel p_syl2an e2_off e5_off f3_off f4_off p_inss2 f5_off f3_off f4_off a_cin f4_off p_eqsstr3i f5_off f4_off i0_off a_sup_set_class p_sseli f4_off f8_off i0_off a_sup_set_class f11_off p_ffvelrn f0_off f4_off f8_off f11_off a_wf i0_off a_sup_set_class f4_off a_wcel i0_off a_sup_set_class f11_off a_cfv f8_off a_wcel i0_off a_sup_set_class f5_off a_wcel p_syl2an e0_off f0_off f1_off a_sup_set_class f2_off a_sup_set_class f6_off a_co f9_off a_wcel f1_off f2_off f7_off f8_off p_ralrimivva f0_off f1_off a_sup_set_class f2_off a_sup_set_class f6_off a_co f9_off a_wcel f2_off f8_off a_wral f1_off f7_off a_wral i0_off a_sup_set_class f5_off a_wcel p_adantr f1_off a_sup_set_class i0_off a_sup_set_class f10_off a_cfv f2_off a_sup_set_class f6_off p_oveq1 f1_off a_sup_set_class i0_off a_sup_set_class f10_off a_cfv a_wceq f1_off a_sup_set_class f2_off a_sup_set_class f6_off a_co i0_off a_sup_set_class f10_off a_cfv f2_off a_sup_set_class f6_off a_co f9_off p_eleq1d f2_off a_sup_set_class i0_off a_sup_set_class f11_off a_cfv i0_off a_sup_set_class f10_off a_cfv f6_off p_oveq2 f2_off a_sup_set_class i0_off a_sup_set_class f11_off a_cfv a_wceq i0_off a_sup_set_class f10_off a_cfv f2_off a_sup_set_class f6_off a_co i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off a_co f9_off p_eleq1d f1_off a_sup_set_class f2_off a_sup_set_class f6_off a_co f9_off a_wcel i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off a_co f9_off a_wcel i0_off a_sup_set_class f10_off a_cfv f2_off a_sup_set_class f6_off a_co f9_off a_wcel f1_off f2_off i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f7_off f8_off p_rspc2va f0_off i0_off a_sup_set_class f5_off a_wcel a_wa i0_off a_sup_set_class f10_off a_cfv f7_off a_wcel i0_off a_sup_set_class f11_off a_cfv f8_off a_wcel f1_off a_sup_set_class f2_off a_sup_set_class f6_off a_co f9_off a_wcel f2_off f8_off a_wral f1_off f7_off a_wral i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off a_co f9_off a_wcel p_syl21anc i0_off f5_off i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off a_co a_cmpt p_eqid f0_off i0_off f5_off i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off a_co f9_off i0_off f5_off i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off a_co a_cmpt p_fmptd e1_off f3_off f7_off f10_off p_ffn f0_off f3_off f7_off f10_off a_wf f10_off f3_off a_wfn p_syl e2_off f4_off f8_off f11_off p_ffn f0_off f4_off f8_off f11_off a_wf f11_off f4_off a_wfn p_syl e3_off e4_off e5_off f0_off i0_off a_sup_set_class f3_off a_wcel a_wa i0_off a_sup_set_class f10_off a_cfv p_eqidd f0_off i0_off a_sup_set_class f4_off a_wcel a_wa i0_off a_sup_set_class f11_off a_cfv p_eqidd f0_off i0_off f3_off f4_off i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off f5_off f10_off f11_off f12_off f13_off p_offval f0_off f5_off f9_off f10_off f11_off f6_off a_cof a_co i0_off f5_off i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off a_co a_cmpt p_feq1d f0_off f5_off f9_off f10_off f11_off f6_off a_cof a_co a_wf f5_off f9_off i0_off f5_off i0_off a_sup_set_class f10_off a_cfv i0_off a_sup_set_class f11_off a_cfv f6_off a_co a_cmpt a_wf p_mpbird $.
$}

$(Restrict the operands of a function operation to the same domain as that
       of the operation itself.  (Contributed by Mario Carneiro,
       15-Sep-2014.) $)

${
	$v ph A B C R F G V W  $.
	$d x A  $.
	$d x C  $.
	$d x F  $.
	$d x G  $.
	$d x ph  $.
	$d x R  $.
	f0_ofres $f wff ph $.
	f1_ofres $f class A $.
	f2_ofres $f class B $.
	f3_ofres $f class C $.
	f4_ofres $f class R $.
	f5_ofres $f class F $.
	f6_ofres $f class G $.
	f7_ofres $f class V $.
	f8_ofres $f class W $.
	i0_ofres $f set x $.
	e0_ofres $e |- ( ph -> F Fn A ) $.
	e1_ofres $e |- ( ph -> G Fn B ) $.
	e2_ofres $e |- ( ph -> A e. V ) $.
	e3_ofres $e |- ( ph -> B e. W ) $.
	e4_ofres $e |- ( A i^i B ) = C $.
	p_ofres $p |- ( ph -> ( F oF R G ) = ( ( F |` C ) oF R ( G |` C ) ) ) $= e0_ofres e1_ofres e2_ofres e3_ofres e4_ofres f0_ofres i0_ofres a_sup_set_class f1_ofres a_wcel a_wa i0_ofres a_sup_set_class f5_ofres a_cfv p_eqidd f0_ofres i0_ofres a_sup_set_class f2_ofres a_wcel a_wa i0_ofres a_sup_set_class f6_ofres a_cfv p_eqidd f0_ofres i0_ofres f1_ofres f2_ofres i0_ofres a_sup_set_class f5_ofres a_cfv i0_ofres a_sup_set_class f6_ofres a_cfv f4_ofres f3_ofres f5_ofres f6_ofres f7_ofres f8_ofres p_offval e0_ofres e4_ofres f1_ofres f2_ofres p_inss1 f3_ofres f1_ofres f2_ofres a_cin f1_ofres p_eqsstr3i f1_ofres f3_ofres f5_ofres p_fnssres f0_ofres f5_ofres f1_ofres a_wfn f3_ofres f1_ofres a_wss f5_ofres f3_ofres a_cres f3_ofres a_wfn p_sylancl e1_ofres e4_ofres f1_ofres f2_ofres p_inss2 f3_ofres f1_ofres f2_ofres a_cin f2_ofres p_eqsstr3i f2_ofres f3_ofres f6_ofres p_fnssres f0_ofres f6_ofres f2_ofres a_wfn f3_ofres f2_ofres a_wss f6_ofres f3_ofres a_cres f3_ofres a_wfn p_sylancl e4_ofres f1_ofres f2_ofres p_inss1 f3_ofres f1_ofres f2_ofres a_cin f1_ofres p_eqsstr3i e2_ofres f3_ofres f1_ofres f7_ofres p_ssexg f0_ofres f3_ofres f1_ofres a_wss f1_ofres f7_ofres a_wcel f3_ofres a_cvv a_wcel p_sylancr e4_ofres f1_ofres f2_ofres p_inss1 f3_ofres f1_ofres f2_ofres a_cin f1_ofres p_eqsstr3i e2_ofres f3_ofres f1_ofres f7_ofres p_ssexg f0_ofres f3_ofres f1_ofres a_wss f1_ofres f7_ofres a_wcel f3_ofres a_cvv a_wcel p_sylancr f3_ofres p_inidm i0_ofres a_sup_set_class f3_ofres f5_ofres p_fvres i0_ofres a_sup_set_class f3_ofres a_wcel i0_ofres a_sup_set_class f5_ofres f3_ofres a_cres a_cfv i0_ofres a_sup_set_class f5_ofres a_cfv a_wceq f0_ofres p_adantl i0_ofres a_sup_set_class f3_ofres f6_ofres p_fvres i0_ofres a_sup_set_class f3_ofres a_wcel i0_ofres a_sup_set_class f6_ofres f3_ofres a_cres a_cfv i0_ofres a_sup_set_class f6_ofres a_cfv a_wceq f0_ofres p_adantl f0_ofres i0_ofres f3_ofres f3_ofres i0_ofres a_sup_set_class f5_ofres a_cfv i0_ofres a_sup_set_class f6_ofres a_cfv f4_ofres f3_ofres f5_ofres f3_ofres a_cres f6_ofres f3_ofres a_cres a_cvv a_cvv p_offval f0_ofres f5_ofres f6_ofres f4_ofres a_cof a_co i0_ofres f3_ofres i0_ofres a_sup_set_class f5_ofres a_cfv i0_ofres a_sup_set_class f6_ofres a_cfv f4_ofres a_co a_cmpt f5_ofres f3_ofres a_cres f6_ofres f3_ofres a_cres f4_ofres a_cof a_co p_eqtr4d $.
$}

$(The function operation expressed as a mapping.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)

${
	$v ph x A B C R F G V W X  $.
	$d x y A  $.
	$d y B  $.
	$d y C  $.
	$d y F  $.
	$d y G  $.
	$d x y ph  $.
	$d x y R  $.
	f0_offval2 $f wff ph $.
	f1_offval2 $f set x $.
	f2_offval2 $f class A $.
	f3_offval2 $f class B $.
	f4_offval2 $f class C $.
	f5_offval2 $f class R $.
	f6_offval2 $f class F $.
	f7_offval2 $f class G $.
	f8_offval2 $f class V $.
	f9_offval2 $f class W $.
	f10_offval2 $f class X $.
	i0_offval2 $f set y $.
	e0_offval2 $e |- ( ph -> A e. V ) $.
	e1_offval2 $e |- ( ( ph /\ x e. A ) -> B e. W ) $.
	e2_offval2 $e |- ( ( ph /\ x e. A ) -> C e. X ) $.
	e3_offval2 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
	e4_offval2 $e |- ( ph -> G = ( x e. A |-> C ) ) $.
	p_offval2 $p |- ( ph -> ( F oF R G ) = ( x e. A |-> ( B R C ) ) ) $= e1_offval2 f0_offval2 f3_offval2 f9_offval2 a_wcel f1_offval2 f2_offval2 p_ralrimiva f1_offval2 f2_offval2 f3_offval2 a_cmpt p_eqid f1_offval2 f2_offval2 f3_offval2 f1_offval2 f2_offval2 f3_offval2 a_cmpt f9_offval2 p_fnmpt f0_offval2 f3_offval2 f9_offval2 a_wcel f1_offval2 f2_offval2 a_wral f1_offval2 f2_offval2 f3_offval2 a_cmpt f2_offval2 a_wfn p_syl e3_offval2 f0_offval2 f2_offval2 f6_offval2 f1_offval2 f2_offval2 f3_offval2 a_cmpt p_fneq1d f0_offval2 f6_offval2 f2_offval2 a_wfn f1_offval2 f2_offval2 f3_offval2 a_cmpt f2_offval2 a_wfn p_mpbird e2_offval2 f0_offval2 f4_offval2 f10_offval2 a_wcel f1_offval2 f2_offval2 p_ralrimiva f1_offval2 f2_offval2 f4_offval2 a_cmpt p_eqid f1_offval2 f2_offval2 f4_offval2 f1_offval2 f2_offval2 f4_offval2 a_cmpt f10_offval2 p_fnmpt f0_offval2 f4_offval2 f10_offval2 a_wcel f1_offval2 f2_offval2 a_wral f1_offval2 f2_offval2 f4_offval2 a_cmpt f2_offval2 a_wfn p_syl e4_offval2 f0_offval2 f2_offval2 f7_offval2 f1_offval2 f2_offval2 f4_offval2 a_cmpt p_fneq1d f0_offval2 f7_offval2 f2_offval2 a_wfn f1_offval2 f2_offval2 f4_offval2 a_cmpt f2_offval2 a_wfn p_mpbird e0_offval2 e0_offval2 f2_offval2 p_inidm e3_offval2 f0_offval2 f6_offval2 f1_offval2 f2_offval2 f3_offval2 a_cmpt a_wceq i0_offval2 a_sup_set_class f2_offval2 a_wcel p_adantr f0_offval2 i0_offval2 a_sup_set_class f2_offval2 a_wcel a_wa i0_offval2 a_sup_set_class f6_offval2 f1_offval2 f2_offval2 f3_offval2 a_cmpt p_fveq1d e4_offval2 f0_offval2 f7_offval2 f1_offval2 f2_offval2 f4_offval2 a_cmpt a_wceq i0_offval2 a_sup_set_class f2_offval2 a_wcel p_adantr f0_offval2 i0_offval2 a_sup_set_class f2_offval2 a_wcel a_wa i0_offval2 a_sup_set_class f7_offval2 f1_offval2 f2_offval2 f4_offval2 a_cmpt p_fveq1d f0_offval2 i0_offval2 f2_offval2 f2_offval2 i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 f2_offval2 f6_offval2 f7_offval2 f8_offval2 f8_offval2 p_offval f1_offval2 f2_offval2 f3_offval2 p_nfmpt1 f1_offval2 i0_offval2 a_sup_set_class p_nfcv f1_offval2 i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt p_nffv f1_offval2 f5_offval2 p_nfcv f1_offval2 f2_offval2 f4_offval2 p_nfmpt1 f1_offval2 i0_offval2 a_sup_set_class p_nfcv f1_offval2 i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt p_nffv f1_offval2 i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 p_nfov i0_offval2 f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 a_co p_nfcv i0_offval2 a_sup_set_class f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt p_fveq2 i0_offval2 a_sup_set_class f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt p_fveq2 i0_offval2 a_sup_set_class f1_offval2 a_sup_set_class a_wceq i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 p_oveq12d i0_offval2 f1_offval2 f2_offval2 i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 a_co f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 a_co p_cbvmpt f0_offval2 f1_offval2 a_sup_set_class f2_offval2 a_wcel p_simpr e1_offval2 f1_offval2 f2_offval2 f3_offval2 a_cmpt p_eqid f1_offval2 f2_offval2 f3_offval2 f9_offval2 f1_offval2 f2_offval2 f3_offval2 a_cmpt p_fvmpt2 f0_offval2 f1_offval2 a_sup_set_class f2_offval2 a_wcel a_wa f1_offval2 a_sup_set_class f2_offval2 a_wcel f3_offval2 f9_offval2 a_wcel f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv f3_offval2 a_wceq p_syl2anc f0_offval2 f1_offval2 a_sup_set_class f2_offval2 a_wcel p_simpr e2_offval2 f1_offval2 f2_offval2 f4_offval2 a_cmpt p_eqid f1_offval2 f2_offval2 f4_offval2 f10_offval2 f1_offval2 f2_offval2 f4_offval2 a_cmpt p_fvmpt2 f0_offval2 f1_offval2 a_sup_set_class f2_offval2 a_wcel a_wa f1_offval2 a_sup_set_class f2_offval2 a_wcel f4_offval2 f10_offval2 a_wcel f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f4_offval2 a_wceq p_syl2anc f0_offval2 f1_offval2 a_sup_set_class f2_offval2 a_wcel a_wa f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv f3_offval2 f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f4_offval2 f5_offval2 p_oveq12d f0_offval2 f1_offval2 f2_offval2 f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 a_co f3_offval2 f4_offval2 f5_offval2 a_co p_mpteq2dva f0_offval2 i0_offval2 f2_offval2 i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 a_co a_cmpt f1_offval2 f2_offval2 f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv f1_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 a_co a_cmpt f1_offval2 f2_offval2 f3_offval2 f4_offval2 f5_offval2 a_co a_cmpt p_syl5eq f0_offval2 f6_offval2 f7_offval2 f5_offval2 a_cof a_co i0_offval2 f2_offval2 i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f3_offval2 a_cmpt a_cfv i0_offval2 a_sup_set_class f1_offval2 f2_offval2 f4_offval2 a_cmpt a_cfv f5_offval2 a_co a_cmpt f1_offval2 f2_offval2 f3_offval2 f4_offval2 f5_offval2 a_co a_cmpt p_eqtrd $.
$}

$(The function relation acting on maps.  (Contributed by Mario Carneiro,
       20-Jul-2014.) $)

${
	$v ph x A B C R F G V W X  $.
	$d x y A  $.
	$d y B  $.
	$d y C  $.
	$d y F  $.
	$d y G  $.
	$d x y ph  $.
	$d x y R  $.
	f0_ofrfval2 $f wff ph $.
	f1_ofrfval2 $f set x $.
	f2_ofrfval2 $f class A $.
	f3_ofrfval2 $f class B $.
	f4_ofrfval2 $f class C $.
	f5_ofrfval2 $f class R $.
	f6_ofrfval2 $f class F $.
	f7_ofrfval2 $f class G $.
	f8_ofrfval2 $f class V $.
	f9_ofrfval2 $f class W $.
	f10_ofrfval2 $f class X $.
	i0_ofrfval2 $f set y $.
	e0_ofrfval2 $e |- ( ph -> A e. V ) $.
	e1_ofrfval2 $e |- ( ( ph /\ x e. A ) -> B e. W ) $.
	e2_ofrfval2 $e |- ( ( ph /\ x e. A ) -> C e. X ) $.
	e3_ofrfval2 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
	e4_ofrfval2 $e |- ( ph -> G = ( x e. A |-> C ) ) $.
	p_ofrfval2 $p |- ( ph -> ( F oR R G <-> A. x e. A B R C ) ) $= e1_ofrfval2 f0_ofrfval2 f3_ofrfval2 f9_ofrfval2 a_wcel f1_ofrfval2 f2_ofrfval2 p_ralrimiva f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt p_eqid f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt f9_ofrfval2 p_fnmpt f0_ofrfval2 f3_ofrfval2 f9_ofrfval2 a_wcel f1_ofrfval2 f2_ofrfval2 a_wral f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt f2_ofrfval2 a_wfn p_syl e3_ofrfval2 f0_ofrfval2 f2_ofrfval2 f6_ofrfval2 f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt p_fneq1d f0_ofrfval2 f6_ofrfval2 f2_ofrfval2 a_wfn f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt f2_ofrfval2 a_wfn p_mpbird e2_ofrfval2 f0_ofrfval2 f4_ofrfval2 f10_ofrfval2 a_wcel f1_ofrfval2 f2_ofrfval2 p_ralrimiva f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt p_eqid f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt f10_ofrfval2 p_fnmpt f0_ofrfval2 f4_ofrfval2 f10_ofrfval2 a_wcel f1_ofrfval2 f2_ofrfval2 a_wral f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt f2_ofrfval2 a_wfn p_syl e4_ofrfval2 f0_ofrfval2 f2_ofrfval2 f7_ofrfval2 f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt p_fneq1d f0_ofrfval2 f7_ofrfval2 f2_ofrfval2 a_wfn f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt f2_ofrfval2 a_wfn p_mpbird e0_ofrfval2 e0_ofrfval2 f2_ofrfval2 p_inidm e3_ofrfval2 f0_ofrfval2 f6_ofrfval2 f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_wceq i0_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel p_adantr f0_ofrfval2 i0_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel a_wa i0_ofrfval2 a_sup_set_class f6_ofrfval2 f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt p_fveq1d e4_ofrfval2 f0_ofrfval2 f7_ofrfval2 f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_wceq i0_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel p_adantr f0_ofrfval2 i0_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel a_wa i0_ofrfval2 a_sup_set_class f7_ofrfval2 f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt p_fveq1d f0_ofrfval2 i0_ofrfval2 f2_ofrfval2 f2_ofrfval2 i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 f2_ofrfval2 f6_ofrfval2 f7_ofrfval2 f8_ofrfval2 f8_ofrfval2 p_ofrfval f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 p_nfmpt1 f1_ofrfval2 i0_ofrfval2 a_sup_set_class p_nfcv f1_ofrfval2 i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt p_nffv f1_ofrfval2 f5_ofrfval2 p_nfcv f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 p_nfmpt1 f1_ofrfval2 i0_ofrfval2 a_sup_set_class p_nfcv f1_ofrfval2 i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt p_nffv f1_ofrfval2 i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 p_nfbr f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 a_wbr i0_ofrfval2 p_nfv i0_ofrfval2 a_sup_set_class f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt p_fveq2 i0_ofrfval2 a_sup_set_class f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt p_fveq2 i0_ofrfval2 a_sup_set_class f1_ofrfval2 a_sup_set_class a_wceq i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 p_breq12d i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 a_wbr f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 a_wbr i0_ofrfval2 f1_ofrfval2 f2_ofrfval2 p_cbvral f0_ofrfval2 f1_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel p_simpr e1_ofrfval2 f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt p_eqid f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 f9_ofrfval2 f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt p_fvmpt2 f0_ofrfval2 f1_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel a_wa f1_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel f3_ofrfval2 f9_ofrfval2 a_wcel f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv f3_ofrfval2 a_wceq p_syl2anc f0_ofrfval2 f1_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel p_simpr e2_ofrfval2 f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt p_eqid f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 f10_ofrfval2 f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt p_fvmpt2 f0_ofrfval2 f1_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel a_wa f1_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel f4_ofrfval2 f10_ofrfval2 a_wcel f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f4_ofrfval2 a_wceq p_syl2anc f0_ofrfval2 f1_ofrfval2 a_sup_set_class f2_ofrfval2 a_wcel a_wa f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv f3_ofrfval2 f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f4_ofrfval2 f5_ofrfval2 p_breq12d f0_ofrfval2 f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 a_wbr f3_ofrfval2 f4_ofrfval2 f5_ofrfval2 a_wbr f1_ofrfval2 f2_ofrfval2 p_ralbidva i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 a_wbr i0_ofrfval2 f2_ofrfval2 a_wral f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv f1_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 a_wbr f1_ofrfval2 f2_ofrfval2 a_wral f0_ofrfval2 f3_ofrfval2 f4_ofrfval2 f5_ofrfval2 a_wbr f1_ofrfval2 f2_ofrfval2 a_wral p_syl5bb f0_ofrfval2 f6_ofrfval2 f7_ofrfval2 f5_ofrfval2 a_cofr a_wbr i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f3_ofrfval2 a_cmpt a_cfv i0_ofrfval2 a_sup_set_class f1_ofrfval2 f2_ofrfval2 f4_ofrfval2 a_cmpt a_cfv f5_ofrfval2 a_wbr i0_ofrfval2 f2_ofrfval2 a_wral f3_ofrfval2 f4_ofrfval2 f5_ofrfval2 a_wbr f1_ofrfval2 f2_ofrfval2 a_wral p_bitrd $.
$}

$(The composition of a function operation with another function.
       (Contributed by Mario Carneiro, 19-Dec-2014.) $)

${
	$v ph A B C D R F G H V W X  $.
	$d y A  $.
	$d x y C  $.
	$d x y F  $.
	$d x y G  $.
	$d x y H  $.
	$d x y ph  $.
	$d x D  $.
	$d x y R  $.
	f0_ofco $f wff ph $.
	f1_ofco $f class A $.
	f2_ofco $f class B $.
	f3_ofco $f class C $.
	f4_ofco $f class D $.
	f5_ofco $f class R $.
	f6_ofco $f class F $.
	f7_ofco $f class G $.
	f8_ofco $f class H $.
	f9_ofco $f class V $.
	f10_ofco $f class W $.
	f11_ofco $f class X $.
	i0_ofco $f set x $.
	i1_ofco $f set y $.
	e0_ofco $e |- ( ph -> F Fn A ) $.
	e1_ofco $e |- ( ph -> G Fn B ) $.
	e2_ofco $e |- ( ph -> H : D --> C ) $.
	e3_ofco $e |- ( ph -> A e. V ) $.
	e4_ofco $e |- ( ph -> B e. W ) $.
	e5_ofco $e |- ( ph -> D e. X ) $.
	e6_ofco $e |- ( A i^i B ) = C $.
	p_ofco $p |- ( ph -> ( ( F oF R G ) o. H ) = ( ( F o. H ) oF R ( G o. H ) ) ) $= e2_ofco f4_ofco f3_ofco i0_ofco a_sup_set_class f8_ofco p_ffvelrn f0_ofco f4_ofco f3_ofco f8_ofco a_wf i0_ofco a_sup_set_class f4_ofco a_wcel i0_ofco a_sup_set_class f8_ofco a_cfv f3_ofco a_wcel p_sylan e2_ofco f0_ofco i0_ofco f4_ofco f3_ofco f8_ofco p_feqmptd e0_ofco e1_ofco e3_ofco e4_ofco e6_ofco f0_ofco i1_ofco a_sup_set_class f1_ofco a_wcel a_wa i1_ofco a_sup_set_class f6_ofco a_cfv p_eqidd f0_ofco i1_ofco a_sup_set_class f2_ofco a_wcel a_wa i1_ofco a_sup_set_class f7_ofco a_cfv p_eqidd f0_ofco i1_ofco f1_ofco f2_ofco i1_ofco a_sup_set_class f6_ofco a_cfv i1_ofco a_sup_set_class f7_ofco a_cfv f5_ofco f3_ofco f6_ofco f7_ofco f9_ofco f10_ofco p_offval i1_ofco a_sup_set_class i0_ofco a_sup_set_class f8_ofco a_cfv f6_ofco p_fveq2 i1_ofco a_sup_set_class i0_ofco a_sup_set_class f8_ofco a_cfv f7_ofco p_fveq2 i1_ofco a_sup_set_class i0_ofco a_sup_set_class f8_ofco a_cfv a_wceq i1_ofco a_sup_set_class f6_ofco a_cfv i0_ofco a_sup_set_class f8_ofco a_cfv f6_ofco a_cfv i1_ofco a_sup_set_class f7_ofco a_cfv i0_ofco a_sup_set_class f8_ofco a_cfv f7_ofco a_cfv f5_ofco p_oveq12d f0_ofco i0_ofco i1_ofco f4_ofco f3_ofco i0_ofco a_sup_set_class f8_ofco a_cfv i1_ofco a_sup_set_class f6_ofco a_cfv i1_ofco a_sup_set_class f7_ofco a_cfv f5_ofco a_co i0_ofco a_sup_set_class f8_ofco a_cfv f6_ofco a_cfv i0_ofco a_sup_set_class f8_ofco a_cfv f7_ofco a_cfv f5_ofco a_co f8_ofco f6_ofco f7_ofco f5_ofco a_cof a_co p_fmptco e0_ofco e2_ofco e6_ofco f1_ofco f2_ofco p_inss1 f3_ofco f1_ofco f2_ofco a_cin f1_ofco p_eqsstr3i f4_ofco f3_ofco f1_ofco f8_ofco p_fss f0_ofco f4_ofco f3_ofco f8_ofco a_wf f3_ofco f1_ofco a_wss f4_ofco f1_ofco f8_ofco a_wf p_sylancl f1_ofco f4_ofco f6_ofco f8_ofco p_fnfco f0_ofco f6_ofco f1_ofco a_wfn f4_ofco f1_ofco f8_ofco a_wf f6_ofco f8_ofco a_ccom f4_ofco a_wfn p_syl2anc e1_ofco e2_ofco e6_ofco f1_ofco f2_ofco p_inss2 f3_ofco f1_ofco f2_ofco a_cin f2_ofco p_eqsstr3i f4_ofco f3_ofco f2_ofco f8_ofco p_fss f0_ofco f4_ofco f3_ofco f8_ofco a_wf f3_ofco f2_ofco a_wss f4_ofco f2_ofco f8_ofco a_wf p_sylancl f2_ofco f4_ofco f7_ofco f8_ofco p_fnfco f0_ofco f7_ofco f2_ofco a_wfn f4_ofco f2_ofco f8_ofco a_wf f7_ofco f8_ofco a_ccom f4_ofco a_wfn p_syl2anc e5_ofco e5_ofco f4_ofco p_inidm e2_ofco f4_ofco f3_ofco f8_ofco p_ffn f0_ofco f4_ofco f3_ofco f8_ofco a_wf f8_ofco f4_ofco a_wfn p_syl f4_ofco f6_ofco f8_ofco i0_ofco a_sup_set_class p_fvco2 f0_ofco f8_ofco f4_ofco a_wfn i0_ofco a_sup_set_class f4_ofco a_wcel i0_ofco a_sup_set_class f6_ofco f8_ofco a_ccom a_cfv i0_ofco a_sup_set_class f8_ofco a_cfv f6_ofco a_cfv a_wceq p_sylan e2_ofco f4_ofco f3_ofco f8_ofco p_ffn f0_ofco f4_ofco f3_ofco f8_ofco a_wf f8_ofco f4_ofco a_wfn p_syl f4_ofco f7_ofco f8_ofco i0_ofco a_sup_set_class p_fvco2 f0_ofco f8_ofco f4_ofco a_wfn i0_ofco a_sup_set_class f4_ofco a_wcel i0_ofco a_sup_set_class f7_ofco f8_ofco a_ccom a_cfv i0_ofco a_sup_set_class f8_ofco a_cfv f7_ofco a_cfv a_wceq p_sylan f0_ofco i0_ofco f4_ofco f4_ofco i0_ofco a_sup_set_class f8_ofco a_cfv f6_ofco a_cfv i0_ofco a_sup_set_class f8_ofco a_cfv f7_ofco a_cfv f5_ofco f4_ofco f6_ofco f8_ofco a_ccom f7_ofco f8_ofco a_ccom f11_ofco f11_ofco p_offval f0_ofco f6_ofco f7_ofco f5_ofco a_cof a_co f8_ofco a_ccom i0_ofco f4_ofco i0_ofco a_sup_set_class f8_ofco a_cfv f6_ofco a_cfv i0_ofco a_sup_set_class f8_ofco a_cfv f7_ofco a_cfv f5_ofco a_co a_cmpt f6_ofco f8_ofco a_ccom f7_ofco f8_ofco a_ccom f5_ofco a_cof a_co p_eqtr4d $.
$}

$(Convert an identity of the operation to the analogous identity on the
         function operation.  (Contributed by Mario Carneiro, 24-Jul-2014.) $)

${
	$v ph x A B C R F G H V  $.
	$d x A  $.
	$d x F  $.
	$d x G  $.
	$d x H  $.
	$d x ph  $.
	$d x R  $.
	f0_offveq $f wff ph $.
	f1_offveq $f set x $.
	f2_offveq $f class A $.
	f3_offveq $f class B $.
	f4_offveq $f class C $.
	f5_offveq $f class R $.
	f6_offveq $f class F $.
	f7_offveq $f class G $.
	f8_offveq $f class H $.
	f9_offveq $f class V $.
	e0_offveq $e |- ( ph -> A e. V ) $.
	e1_offveq $e |- ( ph -> F Fn A ) $.
	e2_offveq $e |- ( ph -> G Fn A ) $.
	e3_offveq $e |- ( ph -> H Fn A ) $.
	e4_offveq $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = B ) $.
	e5_offveq $e |- ( ( ph /\ x e. A ) -> ( G ` x ) = C ) $.
	e6_offveq $e |- ( ( ph /\ x e. A ) -> ( B R C ) = ( H ` x ) ) $.
	p_offveq $p |- ( ph -> ( F oF R G ) = H ) $= e1_offveq e2_offveq e0_offveq e0_offveq f2_offveq p_inidm f0_offveq f2_offveq f2_offveq f5_offveq f2_offveq f6_offveq f7_offveq f9_offveq f9_offveq p_offn e3_offveq e1_offveq e2_offveq e0_offveq e0_offveq f2_offveq p_inidm e4_offveq e5_offveq f0_offveq f2_offveq f2_offveq f3_offveq f4_offveq f5_offveq f2_offveq f6_offveq f7_offveq f9_offveq f9_offveq f1_offveq a_sup_set_class p_ofval e6_offveq f0_offveq f1_offveq a_sup_set_class f2_offveq a_wcel a_wa f1_offveq a_sup_set_class f6_offveq f7_offveq f5_offveq a_cof a_co a_cfv f3_offveq f4_offveq f5_offveq a_co f1_offveq a_sup_set_class f8_offveq a_cfv p_eqtrd f0_offveq f1_offveq f2_offveq f6_offveq f7_offveq f5_offveq a_cof a_co f8_offveq p_eqfnfvd $.
$}

$(Equivalent expressions for equality with a function operation.
       (Contributed by NM, 9-Oct-2014.)  (Proof shortened by Mario Carneiro,
       5-Dec-2016.) $)

${
	$v ph x A B C R F G H V  $.
	$d x A  $.
	$d x F  $.
	$d x G  $.
	$d x H  $.
	$d x ph  $.
	$d x R  $.
	$d A  $.
	$d B  $.
	$d C  $.
	$d x F  $.
	$d G  $.
	$d H  $.
	$d R  $.
	$d ph  $.
	f0_offveqb $f wff ph $.
	f1_offveqb $f set x $.
	f2_offveqb $f class A $.
	f3_offveqb $f class B $.
	f4_offveqb $f class C $.
	f5_offveqb $f class R $.
	f6_offveqb $f class F $.
	f7_offveqb $f class G $.
	f8_offveqb $f class H $.
	f9_offveqb $f class V $.
	e0_offveqb $e |- ( ph -> A e. V ) $.
	e1_offveqb $e |- ( ph -> F Fn A ) $.
	e2_offveqb $e |- ( ph -> G Fn A ) $.
	e3_offveqb $e |- ( ph -> H Fn A ) $.
	e4_offveqb $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = B ) $.
	e5_offveqb $e |- ( ( ph /\ x e. A ) -> ( G ` x ) = C ) $.
	p_offveqb $p |- ( ph -> ( H = ( F oF R G ) <-> A. x e. A ( H ` x ) = ( B R C ) ) ) $= e3_offveqb f1_offveqb f2_offveqb f8_offveqb p_dffn5 f0_offveqb f8_offveqb f2_offveqb a_wfn f8_offveqb f1_offveqb f2_offveqb f1_offveqb a_sup_set_class f8_offveqb a_cfv a_cmpt a_wceq p_sylib e1_offveqb e2_offveqb e0_offveqb e0_offveqb f2_offveqb p_inidm e4_offveqb e5_offveqb f0_offveqb f1_offveqb f2_offveqb f2_offveqb f3_offveqb f4_offveqb f5_offveqb f2_offveqb f6_offveqb f7_offveqb f9_offveqb f9_offveqb p_offval f0_offveqb f8_offveqb f1_offveqb f2_offveqb f1_offveqb a_sup_set_class f8_offveqb a_cfv a_cmpt f6_offveqb f7_offveqb f5_offveqb a_cof a_co f1_offveqb f2_offveqb f3_offveqb f4_offveqb f5_offveqb a_co a_cmpt p_eqeq12d f1_offveqb a_sup_set_class f8_offveqb p_fvex f1_offveqb a_sup_set_class f8_offveqb a_cfv a_cvv a_wcel f0_offveqb p_a1i f0_offveqb f1_offveqb a_sup_set_class f8_offveqb a_cfv a_cvv a_wcel f1_offveqb f2_offveqb p_ralrimivw f1_offveqb f2_offveqb f1_offveqb a_sup_set_class f8_offveqb a_cfv f3_offveqb f4_offveqb f5_offveqb a_co a_cvv p_mpteqb f0_offveqb f1_offveqb a_sup_set_class f8_offveqb a_cfv a_cvv a_wcel f1_offveqb f2_offveqb a_wral f1_offveqb f2_offveqb f1_offveqb a_sup_set_class f8_offveqb a_cfv a_cmpt f1_offveqb f2_offveqb f3_offveqb f4_offveqb f5_offveqb a_co a_cmpt a_wceq f1_offveqb a_sup_set_class f8_offveqb a_cfv f3_offveqb f4_offveqb f5_offveqb a_co a_wceq f1_offveqb f2_offveqb a_wral a_wb p_syl f0_offveqb f8_offveqb f6_offveqb f7_offveqb f5_offveqb a_cof a_co a_wceq f1_offveqb f2_offveqb f1_offveqb a_sup_set_class f8_offveqb a_cfv a_cmpt f1_offveqb f2_offveqb f3_offveqb f4_offveqb f5_offveqb a_co a_cmpt a_wceq f1_offveqb a_sup_set_class f8_offveqb a_cfv f3_offveqb f4_offveqb f5_offveqb a_co a_wceq f1_offveqb f2_offveqb a_wral p_bitrd $.
$}

$(Left operation by a constant.  (Contributed by Mario Carneiro,
       24-Jul-2014.) $)

${
	$v ph A B C R F V W X  $.
	f0_ofc1 $f wff ph $.
	f1_ofc1 $f class A $.
	f2_ofc1 $f class B $.
	f3_ofc1 $f class C $.
	f4_ofc1 $f class R $.
	f5_ofc1 $f class F $.
	f6_ofc1 $f class V $.
	f7_ofc1 $f class W $.
	f8_ofc1 $f class X $.
	e0_ofc1 $e |- ( ph -> A e. V ) $.
	e1_ofc1 $e |- ( ph -> B e. W ) $.
	e2_ofc1 $e |- ( ph -> F Fn A ) $.
	e3_ofc1 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
	p_ofc1 $p |- ( ( ph /\ X e. A ) -> ( ( ( A X. { B } ) oF R F ) ` X ) = ( B R C ) ) $= e1_ofc1 f1_ofc1 f2_ofc1 f7_ofc1 p_fnconstg f0_ofc1 f2_ofc1 f7_ofc1 a_wcel f1_ofc1 f2_ofc1 a_csn a_cxp f1_ofc1 a_wfn p_syl e2_ofc1 e0_ofc1 e0_ofc1 f1_ofc1 p_inidm e1_ofc1 f1_ofc1 f2_ofc1 f8_ofc1 f7_ofc1 p_fvconst2g f0_ofc1 f2_ofc1 f7_ofc1 a_wcel f8_ofc1 f1_ofc1 a_wcel f8_ofc1 f1_ofc1 f2_ofc1 a_csn a_cxp a_cfv f2_ofc1 a_wceq p_sylan e3_ofc1 f0_ofc1 f1_ofc1 f1_ofc1 f2_ofc1 f3_ofc1 f4_ofc1 f1_ofc1 f1_ofc1 f2_ofc1 a_csn a_cxp f5_ofc1 f6_ofc1 f6_ofc1 f8_ofc1 p_ofval $.
$}

$(Right operation by a constant.  (Contributed by NM, 7-Oct-2014.) $)

${
	$v ph A B C R F V W X  $.
	f0_ofc2 $f wff ph $.
	f1_ofc2 $f class A $.
	f2_ofc2 $f class B $.
	f3_ofc2 $f class C $.
	f4_ofc2 $f class R $.
	f5_ofc2 $f class F $.
	f6_ofc2 $f class V $.
	f7_ofc2 $f class W $.
	f8_ofc2 $f class X $.
	e0_ofc2 $e |- ( ph -> A e. V ) $.
	e1_ofc2 $e |- ( ph -> B e. W ) $.
	e2_ofc2 $e |- ( ph -> F Fn A ) $.
	e3_ofc2 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
	p_ofc2 $p |- ( ( ph /\ X e. A ) -> ( ( F oF R ( A X. { B } ) ) ` X ) = ( C R B ) ) $= e2_ofc2 e1_ofc2 f1_ofc2 f2_ofc2 f7_ofc2 p_fnconstg f0_ofc2 f2_ofc2 f7_ofc2 a_wcel f1_ofc2 f2_ofc2 a_csn a_cxp f1_ofc2 a_wfn p_syl e0_ofc2 e0_ofc2 f1_ofc2 p_inidm e3_ofc2 e1_ofc2 f1_ofc2 f2_ofc2 f8_ofc2 f7_ofc2 p_fvconst2g f0_ofc2 f2_ofc2 f7_ofc2 a_wcel f8_ofc2 f1_ofc2 a_wcel f8_ofc2 f1_ofc2 f2_ofc2 a_csn a_cxp a_cfv f2_ofc2 a_wceq p_sylan f0_ofc2 f1_ofc2 f1_ofc2 f3_ofc2 f2_ofc2 f4_ofc2 f1_ofc2 f5_ofc2 f1_ofc2 f2_ofc2 a_csn a_cxp f6_ofc2 f6_ofc2 f8_ofc2 p_ofval $.
$}

$(Function operation on two constant functions.  (Contributed by Mario
       Carneiro, 28-Jul-2014.) $)

${
	$v ph A B C R V W X  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x ph  $.
	$d x R  $.
	$d x W  $.
	$d x X  $.
	f0_ofc12 $f wff ph $.
	f1_ofc12 $f class A $.
	f2_ofc12 $f class B $.
	f3_ofc12 $f class C $.
	f4_ofc12 $f class R $.
	f5_ofc12 $f class V $.
	f6_ofc12 $f class W $.
	f7_ofc12 $f class X $.
	i0_ofc12 $f set x $.
	e0_ofc12 $e |- ( ph -> A e. V ) $.
	e1_ofc12 $e |- ( ph -> B e. W ) $.
	e2_ofc12 $e |- ( ph -> C e. X ) $.
	p_ofc12 $p |- ( ph -> ( ( A X. { B } ) oF R ( A X. { C } ) ) = ( A X. { ( B R C ) } ) ) $= e0_ofc12 e1_ofc12 f0_ofc12 f2_ofc12 f6_ofc12 a_wcel i0_ofc12 a_sup_set_class f1_ofc12 a_wcel p_adantr e2_ofc12 f0_ofc12 f3_ofc12 f7_ofc12 a_wcel i0_ofc12 a_sup_set_class f1_ofc12 a_wcel p_adantr i0_ofc12 f1_ofc12 f2_ofc12 p_fconstmpt f1_ofc12 f2_ofc12 a_csn a_cxp i0_ofc12 f1_ofc12 f2_ofc12 a_cmpt a_wceq f0_ofc12 p_a1i i0_ofc12 f1_ofc12 f3_ofc12 p_fconstmpt f1_ofc12 f3_ofc12 a_csn a_cxp i0_ofc12 f1_ofc12 f3_ofc12 a_cmpt a_wceq f0_ofc12 p_a1i f0_ofc12 i0_ofc12 f1_ofc12 f2_ofc12 f3_ofc12 f4_ofc12 f1_ofc12 f2_ofc12 a_csn a_cxp f1_ofc12 f3_ofc12 a_csn a_cxp f5_ofc12 f6_ofc12 f7_ofc12 p_offval2 i0_ofc12 f1_ofc12 f2_ofc12 f3_ofc12 f4_ofc12 a_co p_fconstmpt f0_ofc12 f1_ofc12 f2_ofc12 a_csn a_cxp f1_ofc12 f3_ofc12 a_csn a_cxp f4_ofc12 a_cof a_co i0_ofc12 f1_ofc12 f2_ofc12 f3_ofc12 f4_ofc12 a_co a_cmpt f1_ofc12 f2_ofc12 f3_ofc12 f4_ofc12 a_co a_csn a_cxp p_syl6eqr $.
$}

$(Transfer a reflexive law to the function relation.  (Contributed by
         Mario Carneiro, 28-Jul-2014.) $)

${
	$v ph x A R S F V  $.
	$d w x  $.
	$d w x  $.
	$d w x F  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x ph  $.
	$d w x R  $.
	$d w A  $.
	$d w x S  $.
	$d w x  $.
	$d w x  $.
	f0_caofref $f wff ph $.
	f1_caofref $f set x $.
	f2_caofref $f class A $.
	f3_caofref $f class R $.
	f4_caofref $f class S $.
	f5_caofref $f class F $.
	f6_caofref $f class V $.
	i0_caofref $f set w $.
	e0_caofref $e |- ( ph -> A e. V ) $.
	e1_caofref $e |- ( ph -> F : A --> S ) $.
	e2_caofref $e |- ( ( ph /\ x e. S ) -> x R x ) $.
	p_caofref $p |- ( ph -> F oR R F ) $= e1_caofref f2_caofref f4_caofref i0_caofref a_sup_set_class f5_caofref p_ffvelrn f0_caofref f2_caofref f4_caofref f5_caofref a_wf i0_caofref a_sup_set_class f2_caofref a_wcel i0_caofref a_sup_set_class f5_caofref a_cfv f4_caofref a_wcel p_sylan e2_caofref f0_caofref f1_caofref a_sup_set_class f1_caofref a_sup_set_class f3_caofref a_wbr f1_caofref f4_caofref p_ralrimiva f0_caofref f1_caofref a_sup_set_class f1_caofref a_sup_set_class f3_caofref a_wbr f1_caofref f4_caofref a_wral i0_caofref a_sup_set_class f2_caofref a_wcel p_adantr f1_caofref a_sup_set_class i0_caofref a_sup_set_class f5_caofref a_cfv a_wceq p_id f1_caofref a_sup_set_class i0_caofref a_sup_set_class f5_caofref a_cfv a_wceq p_id f1_caofref a_sup_set_class i0_caofref a_sup_set_class f5_caofref a_cfv a_wceq f1_caofref a_sup_set_class i0_caofref a_sup_set_class f5_caofref a_cfv f1_caofref a_sup_set_class i0_caofref a_sup_set_class f5_caofref a_cfv f3_caofref p_breq12d f1_caofref a_sup_set_class f1_caofref a_sup_set_class f3_caofref a_wbr i0_caofref a_sup_set_class f5_caofref a_cfv i0_caofref a_sup_set_class f5_caofref a_cfv f3_caofref a_wbr f1_caofref i0_caofref a_sup_set_class f5_caofref a_cfv f4_caofref p_rspcv f0_caofref i0_caofref a_sup_set_class f2_caofref a_wcel a_wa i0_caofref a_sup_set_class f5_caofref a_cfv f4_caofref a_wcel f1_caofref a_sup_set_class f1_caofref a_sup_set_class f3_caofref a_wbr f1_caofref f4_caofref a_wral i0_caofref a_sup_set_class f5_caofref a_cfv i0_caofref a_sup_set_class f5_caofref a_cfv f3_caofref a_wbr p_sylc f0_caofref i0_caofref a_sup_set_class f5_caofref a_cfv i0_caofref a_sup_set_class f5_caofref a_cfv f3_caofref a_wbr i0_caofref f2_caofref p_ralrimiva e1_caofref f2_caofref f4_caofref f5_caofref p_ffn f0_caofref f2_caofref f4_caofref f5_caofref a_wf f5_caofref f2_caofref a_wfn p_syl e1_caofref f2_caofref f4_caofref f5_caofref p_ffn f0_caofref f2_caofref f4_caofref f5_caofref a_wf f5_caofref f2_caofref a_wfn p_syl e0_caofref e0_caofref f2_caofref p_inidm f0_caofref i0_caofref a_sup_set_class f2_caofref a_wcel a_wa i0_caofref a_sup_set_class f5_caofref a_cfv p_eqidd f0_caofref i0_caofref a_sup_set_class f2_caofref a_wcel a_wa i0_caofref a_sup_set_class f5_caofref a_cfv p_eqidd f0_caofref i0_caofref f2_caofref f2_caofref i0_caofref a_sup_set_class f5_caofref a_cfv i0_caofref a_sup_set_class f5_caofref a_cfv f3_caofref f2_caofref f5_caofref f5_caofref f6_caofref f6_caofref p_ofrfval f0_caofref f5_caofref f5_caofref f3_caofref a_cofr a_wbr i0_caofref a_sup_set_class f5_caofref a_cfv i0_caofref a_sup_set_class f5_caofref a_cfv f3_caofref a_wbr i0_caofref f2_caofref a_wral p_mpbird $.
$}

$(Transfer a left inverse law to the function operation.  (Contributed
           by NM, 22-Oct-2014.) $)

${
	$v ph x v A B R S F G N V W  $.
	$d w x B  $.
	$d w x  $.
	$d w x F  $.
	$d w x G  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x ph  $.
	$d w x R  $.
	$d w A  $.
	$d w x S  $.
	$d w x  $.
	$d w x  $.
	$d v A  $.
	$d v F  $.
	$d x v N  $.
	$d v S  $.
	$d v ph  $.
	$d v w  $.
	f0_caofinvl $f wff ph $.
	f1_caofinvl $f set x $.
	f2_caofinvl $f set v $.
	f3_caofinvl $f class A $.
	f4_caofinvl $f class B $.
	f5_caofinvl $f class R $.
	f6_caofinvl $f class S $.
	f7_caofinvl $f class F $.
	f8_caofinvl $f class G $.
	f9_caofinvl $f class N $.
	f10_caofinvl $f class V $.
	f11_caofinvl $f class W $.
	i0_caofinvl $f set w $.
	e0_caofinvl $e |- ( ph -> A e. V ) $.
	e1_caofinvl $e |- ( ph -> F : A --> S ) $.
	e2_caofinvl $e |- ( ph -> B e. W ) $.
	e3_caofinvl $e |- ( ph -> N : S --> S ) $.
	e4_caofinvl $e |- ( ph -> G = ( v e. A |-> ( N ` ( F ` v ) ) ) ) $.
	e5_caofinvl $e |- ( ( ph /\ x e. S ) -> ( ( N ` x ) R x ) = B ) $.
	p_caofinvl $p |- ( ph -> ( G oF R F ) = ( A X. { B } ) ) $= e0_caofinvl e3_caofinvl f0_caofinvl f6_caofinvl f6_caofinvl f9_caofinvl a_wf f2_caofinvl a_sup_set_class f3_caofinvl a_wcel p_adantr e1_caofinvl f3_caofinvl f6_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl p_ffvelrn f0_caofinvl f3_caofinvl f6_caofinvl f7_caofinvl a_wf f2_caofinvl a_sup_set_class f3_caofinvl a_wcel f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f6_caofinvl a_wcel p_sylan f6_caofinvl f6_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl p_ffvelrn f0_caofinvl f2_caofinvl a_sup_set_class f3_caofinvl a_wcel a_wa f6_caofinvl f6_caofinvl f9_caofinvl a_wf f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f6_caofinvl a_wcel f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv f6_caofinvl a_wcel p_syl2anc f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_eqid f0_caofinvl f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv f6_caofinvl f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_fmptd e4_caofinvl f0_caofinvl f3_caofinvl f6_caofinvl f8_caofinvl f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_feq1d f0_caofinvl f3_caofinvl f6_caofinvl f8_caofinvl a_wf f3_caofinvl f6_caofinvl f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt a_wf p_mpbird f3_caofinvl f6_caofinvl i0_caofinvl a_sup_set_class f8_caofinvl p_ffvelrn f0_caofinvl f3_caofinvl f6_caofinvl f8_caofinvl a_wf i0_caofinvl a_sup_set_class f3_caofinvl a_wcel i0_caofinvl a_sup_set_class f8_caofinvl a_cfv f6_caofinvl a_wcel p_sylan e1_caofinvl f3_caofinvl f6_caofinvl i0_caofinvl a_sup_set_class f7_caofinvl p_ffvelrn f0_caofinvl f3_caofinvl f6_caofinvl f7_caofinvl a_wf i0_caofinvl a_sup_set_class f3_caofinvl a_wcel i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f6_caofinvl a_wcel p_sylan f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl p_fvex f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_eqid f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_fnmpti e4_caofinvl f0_caofinvl f3_caofinvl f8_caofinvl f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_fneq1d f0_caofinvl f8_caofinvl f3_caofinvl a_wfn f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt f3_caofinvl a_wfn p_mpbiri i0_caofinvl f3_caofinvl f8_caofinvl p_dffn5 f0_caofinvl f8_caofinvl f3_caofinvl a_wfn f8_caofinvl i0_caofinvl f3_caofinvl i0_caofinvl a_sup_set_class f8_caofinvl a_cfv a_cmpt a_wceq p_sylib e1_caofinvl f0_caofinvl i0_caofinvl f3_caofinvl f6_caofinvl f7_caofinvl p_feqmptd f0_caofinvl i0_caofinvl f3_caofinvl i0_caofinvl a_sup_set_class f8_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl f8_caofinvl f7_caofinvl f10_caofinvl f6_caofinvl f6_caofinvl p_offval2 e4_caofinvl f0_caofinvl i0_caofinvl a_sup_set_class f8_caofinvl f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_fveq1d f2_caofinvl a_sup_set_class i0_caofinvl a_sup_set_class f7_caofinvl p_fveq2 f2_caofinvl a_sup_set_class i0_caofinvl a_sup_set_class a_wceq f2_caofinvl a_sup_set_class f7_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl p_fveq2d f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_eqid i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl p_fvex f2_caofinvl i0_caofinvl a_sup_set_class f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv f3_caofinvl f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt p_fvmpt f0_caofinvl i0_caofinvl a_sup_set_class f3_caofinvl a_wcel i0_caofinvl a_sup_set_class f8_caofinvl a_cfv i0_caofinvl a_sup_set_class f2_caofinvl f3_caofinvl f2_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv a_cmpt a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv p_sylan9eq f0_caofinvl i0_caofinvl a_sup_set_class f3_caofinvl a_wcel a_wa i0_caofinvl a_sup_set_class f8_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl p_oveq1d e1_caofinvl f3_caofinvl f6_caofinvl i0_caofinvl a_sup_set_class f7_caofinvl p_ffvelrn f0_caofinvl f3_caofinvl f6_caofinvl f7_caofinvl a_wf i0_caofinvl a_sup_set_class f3_caofinvl a_wcel i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f6_caofinvl a_wcel p_sylan e5_caofinvl f0_caofinvl f1_caofinvl a_sup_set_class f9_caofinvl a_cfv f1_caofinvl a_sup_set_class f5_caofinvl a_co f4_caofinvl a_wceq f1_caofinvl f6_caofinvl p_ralrimiva f0_caofinvl f1_caofinvl a_sup_set_class f9_caofinvl a_cfv f1_caofinvl a_sup_set_class f5_caofinvl a_co f4_caofinvl a_wceq f1_caofinvl f6_caofinvl a_wral i0_caofinvl a_sup_set_class f3_caofinvl a_wcel p_adantr f1_caofinvl a_sup_set_class i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl p_fveq2 f1_caofinvl a_sup_set_class i0_caofinvl a_sup_set_class f7_caofinvl a_cfv a_wceq p_id f1_caofinvl a_sup_set_class i0_caofinvl a_sup_set_class f7_caofinvl a_cfv a_wceq f1_caofinvl a_sup_set_class f9_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv f1_caofinvl a_sup_set_class i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl p_oveq12d f1_caofinvl a_sup_set_class i0_caofinvl a_sup_set_class f7_caofinvl a_cfv a_wceq f1_caofinvl a_sup_set_class f9_caofinvl a_cfv f1_caofinvl a_sup_set_class f5_caofinvl a_co i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl a_co f4_caofinvl p_eqeq1d f1_caofinvl a_sup_set_class f9_caofinvl a_cfv f1_caofinvl a_sup_set_class f5_caofinvl a_co f4_caofinvl a_wceq i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl a_co f4_caofinvl a_wceq f1_caofinvl i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f6_caofinvl p_rspcva f0_caofinvl i0_caofinvl a_sup_set_class f3_caofinvl a_wcel a_wa i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f6_caofinvl a_wcel f1_caofinvl a_sup_set_class f9_caofinvl a_cfv f1_caofinvl a_sup_set_class f5_caofinvl a_co f4_caofinvl a_wceq f1_caofinvl f6_caofinvl a_wral i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl a_co f4_caofinvl a_wceq p_syl2anc f0_caofinvl i0_caofinvl a_sup_set_class f3_caofinvl a_wcel a_wa i0_caofinvl a_sup_set_class f8_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl a_co i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f9_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl a_co f4_caofinvl p_eqtrd f0_caofinvl i0_caofinvl f3_caofinvl i0_caofinvl a_sup_set_class f8_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl a_co f4_caofinvl p_mpteq2dva f0_caofinvl f8_caofinvl f7_caofinvl f5_caofinvl a_cof a_co i0_caofinvl f3_caofinvl i0_caofinvl a_sup_set_class f8_caofinvl a_cfv i0_caofinvl a_sup_set_class f7_caofinvl a_cfv f5_caofinvl a_co a_cmpt i0_caofinvl f3_caofinvl f4_caofinvl a_cmpt p_eqtrd i0_caofinvl f3_caofinvl f4_caofinvl p_fconstmpt f0_caofinvl f8_caofinvl f7_caofinvl f5_caofinvl a_cof a_co i0_caofinvl f3_caofinvl f4_caofinvl a_cmpt f3_caofinvl f4_caofinvl a_csn a_cxp p_syl6eqr $.
$}

$(Transfer a left identity law to the function operation.
           (Contributed by NM, 21-Oct-2014.) $)

${
	$v ph x A B R S F V W  $.
	$d w x B  $.
	$d w x  $.
	$d w x F  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x ph  $.
	$d w x R  $.
	$d w A  $.
	$d w x S  $.
	$d w x  $.
	$d w x  $.
	f0_caofid0l $f wff ph $.
	f1_caofid0l $f set x $.
	f2_caofid0l $f class A $.
	f3_caofid0l $f class B $.
	f4_caofid0l $f class R $.
	f5_caofid0l $f class S $.
	f6_caofid0l $f class F $.
	f7_caofid0l $f class V $.
	f8_caofid0l $f class W $.
	i0_caofid0l $f set w $.
	e0_caofid0l $e |- ( ph -> A e. V ) $.
	e1_caofid0l $e |- ( ph -> F : A --> S ) $.
	e2_caofid0l $e |- ( ph -> B e. W ) $.
	e3_caofid0l $e |- ( ( ph /\ x e. S ) -> ( B R x ) = x ) $.
	p_caofid0l $p |- ( ph -> ( ( A X. { B } ) oF R F ) = F ) $= e0_caofid0l e2_caofid0l f2_caofid0l f3_caofid0l f8_caofid0l p_fnconstg f0_caofid0l f3_caofid0l f8_caofid0l a_wcel f2_caofid0l f3_caofid0l a_csn a_cxp f2_caofid0l a_wfn p_syl e1_caofid0l f2_caofid0l f5_caofid0l f6_caofid0l p_ffn f0_caofid0l f2_caofid0l f5_caofid0l f6_caofid0l a_wf f6_caofid0l f2_caofid0l a_wfn p_syl e1_caofid0l f2_caofid0l f5_caofid0l f6_caofid0l p_ffn f0_caofid0l f2_caofid0l f5_caofid0l f6_caofid0l a_wf f6_caofid0l f2_caofid0l a_wfn p_syl e2_caofid0l f2_caofid0l f3_caofid0l i0_caofid0l a_sup_set_class f8_caofid0l p_fvconst2g f0_caofid0l f3_caofid0l f8_caofid0l a_wcel i0_caofid0l a_sup_set_class f2_caofid0l a_wcel i0_caofid0l a_sup_set_class f2_caofid0l f3_caofid0l a_csn a_cxp a_cfv f3_caofid0l a_wceq p_sylan f0_caofid0l i0_caofid0l a_sup_set_class f2_caofid0l a_wcel a_wa i0_caofid0l a_sup_set_class f6_caofid0l a_cfv p_eqidd e1_caofid0l f2_caofid0l f5_caofid0l i0_caofid0l a_sup_set_class f6_caofid0l p_ffvelrn f0_caofid0l f2_caofid0l f5_caofid0l f6_caofid0l a_wf i0_caofid0l a_sup_set_class f2_caofid0l a_wcel i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f5_caofid0l a_wcel p_sylan e3_caofid0l f0_caofid0l f3_caofid0l f1_caofid0l a_sup_set_class f4_caofid0l a_co f1_caofid0l a_sup_set_class a_wceq f1_caofid0l f5_caofid0l p_ralrimiva f1_caofid0l a_sup_set_class i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f3_caofid0l f4_caofid0l p_oveq2 f1_caofid0l a_sup_set_class i0_caofid0l a_sup_set_class f6_caofid0l a_cfv a_wceq p_id f1_caofid0l a_sup_set_class i0_caofid0l a_sup_set_class f6_caofid0l a_cfv a_wceq f3_caofid0l f1_caofid0l a_sup_set_class f4_caofid0l a_co f3_caofid0l i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f4_caofid0l a_co f1_caofid0l a_sup_set_class i0_caofid0l a_sup_set_class f6_caofid0l a_cfv p_eqeq12d f3_caofid0l f1_caofid0l a_sup_set_class f4_caofid0l a_co f1_caofid0l a_sup_set_class a_wceq f3_caofid0l i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f4_caofid0l a_co i0_caofid0l a_sup_set_class f6_caofid0l a_cfv a_wceq f1_caofid0l i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f5_caofid0l p_rspccva f0_caofid0l f3_caofid0l f1_caofid0l a_sup_set_class f4_caofid0l a_co f1_caofid0l a_sup_set_class a_wceq f1_caofid0l f5_caofid0l a_wral i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f5_caofid0l a_wcel f3_caofid0l i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f4_caofid0l a_co i0_caofid0l a_sup_set_class f6_caofid0l a_cfv a_wceq p_sylan f0_caofid0l i0_caofid0l a_sup_set_class f2_caofid0l a_wcel i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f5_caofid0l a_wcel f3_caofid0l i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f4_caofid0l a_co i0_caofid0l a_sup_set_class f6_caofid0l a_cfv a_wceq p_syldan f0_caofid0l i0_caofid0l f2_caofid0l f3_caofid0l i0_caofid0l a_sup_set_class f6_caofid0l a_cfv f4_caofid0l f2_caofid0l f3_caofid0l a_csn a_cxp f6_caofid0l f6_caofid0l f7_caofid0l p_offveq $.
$}

$(Transfer a right identity law to the function operation.
           (Contributed by NM, 21-Oct-2014.) $)

${
	$v ph x A B R S F V W  $.
	$d w x B  $.
	$d w x  $.
	$d w x F  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x ph  $.
	$d w x R  $.
	$d w A  $.
	$d w x S  $.
	$d w x  $.
	$d w x  $.
	f0_caofid0r $f wff ph $.
	f1_caofid0r $f set x $.
	f2_caofid0r $f class A $.
	f3_caofid0r $f class B $.
	f4_caofid0r $f class R $.
	f5_caofid0r $f class S $.
	f6_caofid0r $f class F $.
	f7_caofid0r $f class V $.
	f8_caofid0r $f class W $.
	i0_caofid0r $f set w $.
	e0_caofid0r $e |- ( ph -> A e. V ) $.
	e1_caofid0r $e |- ( ph -> F : A --> S ) $.
	e2_caofid0r $e |- ( ph -> B e. W ) $.
	e3_caofid0r $e |- ( ( ph /\ x e. S ) -> ( x R B ) = x ) $.
	p_caofid0r $p |- ( ph -> ( F oF R ( A X. { B } ) ) = F ) $= e0_caofid0r e1_caofid0r f2_caofid0r f5_caofid0r f6_caofid0r p_ffn f0_caofid0r f2_caofid0r f5_caofid0r f6_caofid0r a_wf f6_caofid0r f2_caofid0r a_wfn p_syl e2_caofid0r f2_caofid0r f3_caofid0r f8_caofid0r p_fnconstg f0_caofid0r f3_caofid0r f8_caofid0r a_wcel f2_caofid0r f3_caofid0r a_csn a_cxp f2_caofid0r a_wfn p_syl e1_caofid0r f2_caofid0r f5_caofid0r f6_caofid0r p_ffn f0_caofid0r f2_caofid0r f5_caofid0r f6_caofid0r a_wf f6_caofid0r f2_caofid0r a_wfn p_syl f0_caofid0r i0_caofid0r a_sup_set_class f2_caofid0r a_wcel a_wa i0_caofid0r a_sup_set_class f6_caofid0r a_cfv p_eqidd e2_caofid0r f2_caofid0r f3_caofid0r i0_caofid0r a_sup_set_class f8_caofid0r p_fvconst2g f0_caofid0r f3_caofid0r f8_caofid0r a_wcel i0_caofid0r a_sup_set_class f2_caofid0r a_wcel i0_caofid0r a_sup_set_class f2_caofid0r f3_caofid0r a_csn a_cxp a_cfv f3_caofid0r a_wceq p_sylan e1_caofid0r f2_caofid0r f5_caofid0r i0_caofid0r a_sup_set_class f6_caofid0r p_ffvelrn f0_caofid0r f2_caofid0r f5_caofid0r f6_caofid0r a_wf i0_caofid0r a_sup_set_class f2_caofid0r a_wcel i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f5_caofid0r a_wcel p_sylan e3_caofid0r f0_caofid0r f1_caofid0r a_sup_set_class f3_caofid0r f4_caofid0r a_co f1_caofid0r a_sup_set_class a_wceq f1_caofid0r f5_caofid0r p_ralrimiva f1_caofid0r a_sup_set_class i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f3_caofid0r f4_caofid0r p_oveq1 f1_caofid0r a_sup_set_class i0_caofid0r a_sup_set_class f6_caofid0r a_cfv a_wceq p_id f1_caofid0r a_sup_set_class i0_caofid0r a_sup_set_class f6_caofid0r a_cfv a_wceq f1_caofid0r a_sup_set_class f3_caofid0r f4_caofid0r a_co i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f3_caofid0r f4_caofid0r a_co f1_caofid0r a_sup_set_class i0_caofid0r a_sup_set_class f6_caofid0r a_cfv p_eqeq12d f1_caofid0r a_sup_set_class f3_caofid0r f4_caofid0r a_co f1_caofid0r a_sup_set_class a_wceq i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f3_caofid0r f4_caofid0r a_co i0_caofid0r a_sup_set_class f6_caofid0r a_cfv a_wceq f1_caofid0r i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f5_caofid0r p_rspccva f0_caofid0r f1_caofid0r a_sup_set_class f3_caofid0r f4_caofid0r a_co f1_caofid0r a_sup_set_class a_wceq f1_caofid0r f5_caofid0r a_wral i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f5_caofid0r a_wcel i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f3_caofid0r f4_caofid0r a_co i0_caofid0r a_sup_set_class f6_caofid0r a_cfv a_wceq p_sylan f0_caofid0r i0_caofid0r a_sup_set_class f2_caofid0r a_wcel i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f5_caofid0r a_wcel i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f3_caofid0r f4_caofid0r a_co i0_caofid0r a_sup_set_class f6_caofid0r a_cfv a_wceq p_syldan f0_caofid0r i0_caofid0r f2_caofid0r i0_caofid0r a_sup_set_class f6_caofid0r a_cfv f3_caofid0r f4_caofid0r f6_caofid0r f2_caofid0r f3_caofid0r a_csn a_cxp f6_caofid0r f7_caofid0r p_offveq $.
$}

$(Transfer a right absorption law to the function operation.
           (Contributed by Mario Carneiro, 28-Jul-2014.) $)

${
	$v ph x A B C R S F V W X  $.
	$d w x B  $.
	$d w x C  $.
	$d w x F  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x ph  $.
	$d w x R  $.
	$d w A  $.
	$d w x S  $.
	$d w x  $.
	$d w x  $.
	f0_caofid1 $f wff ph $.
	f1_caofid1 $f set x $.
	f2_caofid1 $f class A $.
	f3_caofid1 $f class B $.
	f4_caofid1 $f class C $.
	f5_caofid1 $f class R $.
	f6_caofid1 $f class S $.
	f7_caofid1 $f class F $.
	f8_caofid1 $f class V $.
	f9_caofid1 $f class W $.
	f10_caofid1 $f class X $.
	i0_caofid1 $f set w $.
	e0_caofid1 $e |- ( ph -> A e. V ) $.
	e1_caofid1 $e |- ( ph -> F : A --> S ) $.
	e2_caofid1 $e |- ( ph -> B e. W ) $.
	e3_caofid1 $e |- ( ph -> C e. X ) $.
	e4_caofid1 $e |- ( ( ph /\ x e. S ) -> ( x R B ) = C ) $.
	p_caofid1 $p |- ( ph -> ( F oF R ( A X. { B } ) ) = ( A X. { C } ) ) $= e0_caofid1 e1_caofid1 f2_caofid1 f6_caofid1 f7_caofid1 p_ffn f0_caofid1 f2_caofid1 f6_caofid1 f7_caofid1 a_wf f7_caofid1 f2_caofid1 a_wfn p_syl e2_caofid1 f2_caofid1 f3_caofid1 f9_caofid1 p_fnconstg f0_caofid1 f3_caofid1 f9_caofid1 a_wcel f2_caofid1 f3_caofid1 a_csn a_cxp f2_caofid1 a_wfn p_syl e3_caofid1 f2_caofid1 f4_caofid1 f10_caofid1 p_fnconstg f0_caofid1 f4_caofid1 f10_caofid1 a_wcel f2_caofid1 f4_caofid1 a_csn a_cxp f2_caofid1 a_wfn p_syl f0_caofid1 i0_caofid1 a_sup_set_class f2_caofid1 a_wcel a_wa i0_caofid1 a_sup_set_class f7_caofid1 a_cfv p_eqidd e2_caofid1 f2_caofid1 f3_caofid1 i0_caofid1 a_sup_set_class f9_caofid1 p_fvconst2g f0_caofid1 f3_caofid1 f9_caofid1 a_wcel i0_caofid1 a_sup_set_class f2_caofid1 a_wcel i0_caofid1 a_sup_set_class f2_caofid1 f3_caofid1 a_csn a_cxp a_cfv f3_caofid1 a_wceq p_sylan e1_caofid1 f2_caofid1 f6_caofid1 i0_caofid1 a_sup_set_class f7_caofid1 p_ffvelrn f0_caofid1 f2_caofid1 f6_caofid1 f7_caofid1 a_wf i0_caofid1 a_sup_set_class f2_caofid1 a_wcel i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f6_caofid1 a_wcel p_sylan e4_caofid1 f0_caofid1 f1_caofid1 a_sup_set_class f3_caofid1 f5_caofid1 a_co f4_caofid1 a_wceq f1_caofid1 f6_caofid1 p_ralrimiva f1_caofid1 a_sup_set_class i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f3_caofid1 f5_caofid1 p_oveq1 f1_caofid1 a_sup_set_class i0_caofid1 a_sup_set_class f7_caofid1 a_cfv a_wceq f1_caofid1 a_sup_set_class f3_caofid1 f5_caofid1 a_co i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f3_caofid1 f5_caofid1 a_co f4_caofid1 p_eqeq1d f1_caofid1 a_sup_set_class f3_caofid1 f5_caofid1 a_co f4_caofid1 a_wceq i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f3_caofid1 f5_caofid1 a_co f4_caofid1 a_wceq f1_caofid1 i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f6_caofid1 p_rspccva f0_caofid1 f1_caofid1 a_sup_set_class f3_caofid1 f5_caofid1 a_co f4_caofid1 a_wceq f1_caofid1 f6_caofid1 a_wral i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f6_caofid1 a_wcel i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f3_caofid1 f5_caofid1 a_co f4_caofid1 a_wceq p_sylan f0_caofid1 i0_caofid1 a_sup_set_class f2_caofid1 a_wcel i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f6_caofid1 a_wcel i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f3_caofid1 f5_caofid1 a_co f4_caofid1 a_wceq p_syldan e3_caofid1 f2_caofid1 f4_caofid1 i0_caofid1 a_sup_set_class f10_caofid1 p_fvconst2g f0_caofid1 f4_caofid1 f10_caofid1 a_wcel i0_caofid1 a_sup_set_class f2_caofid1 a_wcel i0_caofid1 a_sup_set_class f2_caofid1 f4_caofid1 a_csn a_cxp a_cfv f4_caofid1 a_wceq p_sylan f0_caofid1 i0_caofid1 a_sup_set_class f2_caofid1 a_wcel a_wa i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f3_caofid1 f5_caofid1 a_co f4_caofid1 i0_caofid1 a_sup_set_class f2_caofid1 f4_caofid1 a_csn a_cxp a_cfv p_eqtr4d f0_caofid1 i0_caofid1 f2_caofid1 i0_caofid1 a_sup_set_class f7_caofid1 a_cfv f3_caofid1 f5_caofid1 f7_caofid1 f2_caofid1 f3_caofid1 a_csn a_cxp f2_caofid1 f4_caofid1 a_csn a_cxp f8_caofid1 p_offveq $.
$}

$(Transfer a right absorption law to the function operation.
         (Contributed by Mario Carneiro, 28-Jul-2014.) $)

${
	$v ph x A B C R S F V W X  $.
	$d w x B  $.
	$d w x C  $.
	$d w x F  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x  $.
	$d w x ph  $.
	$d w x R  $.
	$d w A  $.
	$d w x S  $.
	$d w x  $.
	$d w x  $.
	f0_caofid2 $f wff ph $.
	f1_caofid2 $f set x $.
	f2_caofid2 $f class A $.
	f3_caofid2 $f class B $.
	f4_caofid2 $f class C $.
	f5_caofid2 $f class R $.
	f6_caofid2 $f class S $.
	f7_caofid2 $f class F $.
	f8_caofid2 $f class V $.
	f9_caofid2 $f class W $.
	f10_caofid2 $f class X $.
	i0_caofid2 $f set w $.
	e0_caofid2 $e |- ( ph -> A e. V ) $.
	e1_caofid2 $e |- ( ph -> F : A --> S ) $.
	e2_caofid2 $e |- ( ph -> B e. W ) $.
	e3_caofid2 $e |- ( ph -> C e. X ) $.
	e4_caofid2 $e |- ( ( ph /\ x e. S ) -> ( B R x ) = C ) $.
	p_caofid2 $p |- ( ph -> ( ( A X. { B } ) oF R F ) = ( A X. { C } ) ) $= e0_caofid2 e2_caofid2 f2_caofid2 f3_caofid2 f9_caofid2 p_fnconstg f0_caofid2 f3_caofid2 f9_caofid2 a_wcel f2_caofid2 f3_caofid2 a_csn a_cxp f2_caofid2 a_wfn p_syl e1_caofid2 f2_caofid2 f6_caofid2 f7_caofid2 p_ffn f0_caofid2 f2_caofid2 f6_caofid2 f7_caofid2 a_wf f7_caofid2 f2_caofid2 a_wfn p_syl e3_caofid2 f2_caofid2 f4_caofid2 f10_caofid2 p_fnconstg f0_caofid2 f4_caofid2 f10_caofid2 a_wcel f2_caofid2 f4_caofid2 a_csn a_cxp f2_caofid2 a_wfn p_syl e2_caofid2 f2_caofid2 f3_caofid2 i0_caofid2 a_sup_set_class f9_caofid2 p_fvconst2g f0_caofid2 f3_caofid2 f9_caofid2 a_wcel i0_caofid2 a_sup_set_class f2_caofid2 a_wcel i0_caofid2 a_sup_set_class f2_caofid2 f3_caofid2 a_csn a_cxp a_cfv f3_caofid2 a_wceq p_sylan f0_caofid2 i0_caofid2 a_sup_set_class f2_caofid2 a_wcel a_wa i0_caofid2 a_sup_set_class f7_caofid2 a_cfv p_eqidd e1_caofid2 f2_caofid2 f6_caofid2 i0_caofid2 a_sup_set_class f7_caofid2 p_ffvelrn f0_caofid2 f2_caofid2 f6_caofid2 f7_caofid2 a_wf i0_caofid2 a_sup_set_class f2_caofid2 a_wcel i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f6_caofid2 a_wcel p_sylan e4_caofid2 f0_caofid2 f3_caofid2 f1_caofid2 a_sup_set_class f5_caofid2 a_co f4_caofid2 a_wceq f1_caofid2 f6_caofid2 p_ralrimiva f1_caofid2 a_sup_set_class i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f3_caofid2 f5_caofid2 p_oveq2 f1_caofid2 a_sup_set_class i0_caofid2 a_sup_set_class f7_caofid2 a_cfv a_wceq f3_caofid2 f1_caofid2 a_sup_set_class f5_caofid2 a_co f3_caofid2 i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f5_caofid2 a_co f4_caofid2 p_eqeq1d f3_caofid2 f1_caofid2 a_sup_set_class f5_caofid2 a_co f4_caofid2 a_wceq f3_caofid2 i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f5_caofid2 a_co f4_caofid2 a_wceq f1_caofid2 i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f6_caofid2 p_rspccva f0_caofid2 f3_caofid2 f1_caofid2 a_sup_set_class f5_caofid2 a_co f4_caofid2 a_wceq f1_caofid2 f6_caofid2 a_wral i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f6_caofid2 a_wcel f3_caofid2 i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f5_caofid2 a_co f4_caofid2 a_wceq p_sylan f0_caofid2 i0_caofid2 a_sup_set_class f2_caofid2 a_wcel i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f6_caofid2 a_wcel f3_caofid2 i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f5_caofid2 a_co f4_caofid2 a_wceq p_syldan e3_caofid2 f2_caofid2 f4_caofid2 i0_caofid2 a_sup_set_class f10_caofid2 p_fvconst2g f0_caofid2 f4_caofid2 f10_caofid2 a_wcel i0_caofid2 a_sup_set_class f2_caofid2 a_wcel i0_caofid2 a_sup_set_class f2_caofid2 f4_caofid2 a_csn a_cxp a_cfv f4_caofid2 a_wceq p_sylan f0_caofid2 i0_caofid2 a_sup_set_class f2_caofid2 a_wcel a_wa f3_caofid2 i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f5_caofid2 a_co f4_caofid2 i0_caofid2 a_sup_set_class f2_caofid2 f4_caofid2 a_csn a_cxp a_cfv p_eqtr4d f0_caofid2 i0_caofid2 f2_caofid2 f3_caofid2 i0_caofid2 a_sup_set_class f7_caofid2 a_cfv f5_caofid2 f2_caofid2 f3_caofid2 a_csn a_cxp f7_caofid2 f2_caofid2 f4_caofid2 a_csn a_cxp f8_caofid2 p_offveq $.
$}

$(Transfer a commutative law to the function operation.  (Contributed by
         Mario Carneiro, 26-Jul-2014.) $)

${
	$v ph x y A R S F G V  $.
	$d w x  $.
	$d w x  $.
	$d w x y F  $.
	$d w x y G  $.
	$d w x y  $.
	$d w x y  $.
	$d w x y  $.
	$d w x y ph  $.
	$d w x y R  $.
	$d w A  $.
	$d w x y S  $.
	$d w x y  $.
	$d w x y  $.
	f0_caofcom $f wff ph $.
	f1_caofcom $f set x $.
	f2_caofcom $f set y $.
	f3_caofcom $f class A $.
	f4_caofcom $f class R $.
	f5_caofcom $f class S $.
	f6_caofcom $f class F $.
	f7_caofcom $f class G $.
	f8_caofcom $f class V $.
	i0_caofcom $f set w $.
	e0_caofcom $e |- ( ph -> A e. V ) $.
	e1_caofcom $e |- ( ph -> F : A --> S ) $.
	e2_caofcom $e |- ( ph -> G : A --> S ) $.
	e3_caofcom $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x R y ) = ( y R x ) ) $.
	p_caofcom $p |- ( ph -> ( F oF R G ) = ( G oF R F ) ) $= e1_caofcom f3_caofcom f5_caofcom i0_caofcom a_sup_set_class f6_caofcom p_ffvelrn f0_caofcom f3_caofcom f5_caofcom f6_caofcom a_wf i0_caofcom a_sup_set_class f3_caofcom a_wcel i0_caofcom a_sup_set_class f6_caofcom a_cfv f5_caofcom a_wcel p_sylan e2_caofcom f3_caofcom f5_caofcom i0_caofcom a_sup_set_class f7_caofcom p_ffvelrn f0_caofcom f3_caofcom f5_caofcom f7_caofcom a_wf i0_caofcom a_sup_set_class f3_caofcom a_wcel i0_caofcom a_sup_set_class f7_caofcom a_cfv f5_caofcom a_wcel p_sylan f0_caofcom i0_caofcom a_sup_set_class f3_caofcom a_wcel a_wa i0_caofcom a_sup_set_class f6_caofcom a_cfv f5_caofcom a_wcel i0_caofcom a_sup_set_class f7_caofcom a_cfv f5_caofcom a_wcel p_jca e3_caofcom f0_caofcom f1_caofcom f2_caofcom i0_caofcom a_sup_set_class f6_caofcom a_cfv i0_caofcom a_sup_set_class f7_caofcom a_cfv f5_caofcom f4_caofcom p_caovcomg f0_caofcom i0_caofcom a_sup_set_class f3_caofcom a_wcel i0_caofcom a_sup_set_class f6_caofcom a_cfv f5_caofcom a_wcel i0_caofcom a_sup_set_class f7_caofcom a_cfv f5_caofcom a_wcel a_wa i0_caofcom a_sup_set_class f6_caofcom a_cfv i0_caofcom a_sup_set_class f7_caofcom a_cfv f4_caofcom a_co i0_caofcom a_sup_set_class f7_caofcom a_cfv i0_caofcom a_sup_set_class f6_caofcom a_cfv f4_caofcom a_co a_wceq p_syldan f0_caofcom i0_caofcom f3_caofcom i0_caofcom a_sup_set_class f6_caofcom a_cfv i0_caofcom a_sup_set_class f7_caofcom a_cfv f4_caofcom a_co i0_caofcom a_sup_set_class f7_caofcom a_cfv i0_caofcom a_sup_set_class f6_caofcom a_cfv f4_caofcom a_co p_mpteq2dva e0_caofcom e1_caofcom f3_caofcom f5_caofcom i0_caofcom a_sup_set_class f6_caofcom p_ffvelrn f0_caofcom f3_caofcom f5_caofcom f6_caofcom a_wf i0_caofcom a_sup_set_class f3_caofcom a_wcel i0_caofcom a_sup_set_class f6_caofcom a_cfv f5_caofcom a_wcel p_sylan e2_caofcom f3_caofcom f5_caofcom i0_caofcom a_sup_set_class f7_caofcom p_ffvelrn f0_caofcom f3_caofcom f5_caofcom f7_caofcom a_wf i0_caofcom a_sup_set_class f3_caofcom a_wcel i0_caofcom a_sup_set_class f7_caofcom a_cfv f5_caofcom a_wcel p_sylan e1_caofcom f0_caofcom i0_caofcom f3_caofcom f5_caofcom f6_caofcom p_feqmptd e2_caofcom f0_caofcom i0_caofcom f3_caofcom f5_caofcom f7_caofcom p_feqmptd f0_caofcom i0_caofcom f3_caofcom i0_caofcom a_sup_set_class f6_caofcom a_cfv i0_caofcom a_sup_set_class f7_caofcom a_cfv f4_caofcom f6_caofcom f7_caofcom f8_caofcom f5_caofcom f5_caofcom p_offval2 e0_caofcom e2_caofcom f3_caofcom f5_caofcom i0_caofcom a_sup_set_class f7_caofcom p_ffvelrn f0_caofcom f3_caofcom f5_caofcom f7_caofcom a_wf i0_caofcom a_sup_set_class f3_caofcom a_wcel i0_caofcom a_sup_set_class f7_caofcom a_cfv f5_caofcom a_wcel p_sylan e1_caofcom f3_caofcom f5_caofcom i0_caofcom a_sup_set_class f6_caofcom p_ffvelrn f0_caofcom f3_caofcom f5_caofcom f6_caofcom a_wf i0_caofcom a_sup_set_class f3_caofcom a_wcel i0_caofcom a_sup_set_class f6_caofcom a_cfv f5_caofcom a_wcel p_sylan e2_caofcom f0_caofcom i0_caofcom f3_caofcom f5_caofcom f7_caofcom p_feqmptd e1_caofcom f0_caofcom i0_caofcom f3_caofcom f5_caofcom f6_caofcom p_feqmptd f0_caofcom i0_caofcom f3_caofcom i0_caofcom a_sup_set_class f7_caofcom a_cfv i0_caofcom a_sup_set_class f6_caofcom a_cfv f4_caofcom f7_caofcom f6_caofcom f8_caofcom f5_caofcom f5_caofcom p_offval2 f0_caofcom i0_caofcom f3_caofcom i0_caofcom a_sup_set_class f6_caofcom a_cfv i0_caofcom a_sup_set_class f7_caofcom a_cfv f4_caofcom a_co a_cmpt i0_caofcom f3_caofcom i0_caofcom a_sup_set_class f7_caofcom a_cfv i0_caofcom a_sup_set_class f6_caofcom a_cfv f4_caofcom a_co a_cmpt f6_caofcom f7_caofcom f4_caofcom a_cof a_co f7_caofcom f6_caofcom f4_caofcom a_cof a_co p_3eqtr4d $.
$}

$(Transfer a relation subset law to the function relation.  (Contributed
         by Mario Carneiro, 28-Jul-2014.) $)

${
	$v ph x y A R S T F G V  $.
	$d w x  $.
	$d w x  $.
	$d w x y F  $.
	$d w x y G  $.
	$d w x y  $.
	$d w x y  $.
	$d w x y  $.
	$d w x y ph  $.
	$d w x y R  $.
	$d w A  $.
	$d w x y S  $.
	$d w x y T  $.
	$d w x y  $.
	f0_caofrss $f wff ph $.
	f1_caofrss $f set x $.
	f2_caofrss $f set y $.
	f3_caofrss $f class A $.
	f4_caofrss $f class R $.
	f5_caofrss $f class S $.
	f6_caofrss $f class T $.
	f7_caofrss $f class F $.
	f8_caofrss $f class G $.
	f9_caofrss $f class V $.
	i0_caofrss $f set w $.
	e0_caofrss $e |- ( ph -> A e. V ) $.
	e1_caofrss $e |- ( ph -> F : A --> S ) $.
	e2_caofrss $e |- ( ph -> G : A --> S ) $.
	e3_caofrss $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x R y -> x T y ) ) $.
	p_caofrss $p |- ( ph -> ( F oR R G -> F oR T G ) ) $= e1_caofrss f3_caofrss f5_caofrss i0_caofrss a_sup_set_class f7_caofrss p_ffvelrn f0_caofrss f3_caofrss f5_caofrss f7_caofrss a_wf i0_caofrss a_sup_set_class f3_caofrss a_wcel i0_caofrss a_sup_set_class f7_caofrss a_cfv f5_caofrss a_wcel p_sylan e2_caofrss f3_caofrss f5_caofrss i0_caofrss a_sup_set_class f8_caofrss p_ffvelrn f0_caofrss f3_caofrss f5_caofrss f8_caofrss a_wf i0_caofrss a_sup_set_class f3_caofrss a_wcel i0_caofrss a_sup_set_class f8_caofrss a_cfv f5_caofrss a_wcel p_sylan e3_caofrss f0_caofrss f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f4_caofrss a_wbr f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f6_caofrss a_wbr a_wi f1_caofrss f2_caofrss f5_caofrss f5_caofrss p_ralrimivva f0_caofrss f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f4_caofrss a_wbr f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f6_caofrss a_wbr a_wi f2_caofrss f5_caofrss a_wral f1_caofrss f5_caofrss a_wral i0_caofrss a_sup_set_class f3_caofrss a_wcel p_adantr f1_caofrss a_sup_set_class i0_caofrss a_sup_set_class f7_caofrss a_cfv f2_caofrss a_sup_set_class f4_caofrss p_breq1 f1_caofrss a_sup_set_class i0_caofrss a_sup_set_class f7_caofrss a_cfv f2_caofrss a_sup_set_class f6_caofrss p_breq1 f1_caofrss a_sup_set_class i0_caofrss a_sup_set_class f7_caofrss a_cfv a_wceq f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f4_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv f2_caofrss a_sup_set_class f4_caofrss a_wbr f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f6_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv f2_caofrss a_sup_set_class f6_caofrss a_wbr p_imbi12d f2_caofrss a_sup_set_class i0_caofrss a_sup_set_class f8_caofrss a_cfv i0_caofrss a_sup_set_class f7_caofrss a_cfv f4_caofrss p_breq2 f2_caofrss a_sup_set_class i0_caofrss a_sup_set_class f8_caofrss a_cfv i0_caofrss a_sup_set_class f7_caofrss a_cfv f6_caofrss p_breq2 f2_caofrss a_sup_set_class i0_caofrss a_sup_set_class f8_caofrss a_cfv a_wceq i0_caofrss a_sup_set_class f7_caofrss a_cfv f2_caofrss a_sup_set_class f4_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f4_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv f2_caofrss a_sup_set_class f6_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f6_caofrss a_wbr p_imbi12d f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f4_caofrss a_wbr f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f6_caofrss a_wbr a_wi i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f4_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f6_caofrss a_wbr a_wi i0_caofrss a_sup_set_class f7_caofrss a_cfv f2_caofrss a_sup_set_class f4_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv f2_caofrss a_sup_set_class f6_caofrss a_wbr a_wi f1_caofrss f2_caofrss i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f5_caofrss f5_caofrss p_rspc2va f0_caofrss i0_caofrss a_sup_set_class f3_caofrss a_wcel a_wa i0_caofrss a_sup_set_class f7_caofrss a_cfv f5_caofrss a_wcel i0_caofrss a_sup_set_class f8_caofrss a_cfv f5_caofrss a_wcel f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f4_caofrss a_wbr f1_caofrss a_sup_set_class f2_caofrss a_sup_set_class f6_caofrss a_wbr a_wi f2_caofrss f5_caofrss a_wral f1_caofrss f5_caofrss a_wral i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f4_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f6_caofrss a_wbr a_wi p_syl21anc f0_caofrss i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f4_caofrss a_wbr i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f6_caofrss a_wbr i0_caofrss f3_caofrss p_ralimdva e1_caofrss f3_caofrss f5_caofrss f7_caofrss p_ffn f0_caofrss f3_caofrss f5_caofrss f7_caofrss a_wf f7_caofrss f3_caofrss a_wfn p_syl e2_caofrss f3_caofrss f5_caofrss f8_caofrss p_ffn f0_caofrss f3_caofrss f5_caofrss f8_caofrss a_wf f8_caofrss f3_caofrss a_wfn p_syl e0_caofrss e0_caofrss f3_caofrss p_inidm f0_caofrss i0_caofrss a_sup_set_class f3_caofrss a_wcel a_wa i0_caofrss a_sup_set_class f7_caofrss a_cfv p_eqidd f0_caofrss i0_caofrss a_sup_set_class f3_caofrss a_wcel a_wa i0_caofrss a_sup_set_class f8_caofrss a_cfv p_eqidd f0_caofrss i0_caofrss f3_caofrss f3_caofrss i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f4_caofrss f3_caofrss f7_caofrss f8_caofrss f9_caofrss f9_caofrss p_ofrfval e1_caofrss f3_caofrss f5_caofrss f7_caofrss p_ffn f0_caofrss f3_caofrss f5_caofrss f7_caofrss a_wf f7_caofrss f3_caofrss a_wfn p_syl e2_caofrss f3_caofrss f5_caofrss f8_caofrss p_ffn f0_caofrss f3_caofrss f5_caofrss f8_caofrss a_wf f8_caofrss f3_caofrss a_wfn p_syl e0_caofrss e0_caofrss f3_caofrss p_inidm f0_caofrss i0_caofrss a_sup_set_class f3_caofrss a_wcel a_wa i0_caofrss a_sup_set_class f7_caofrss a_cfv p_eqidd f0_caofrss i0_caofrss a_sup_set_class f3_caofrss a_wcel a_wa i0_caofrss a_sup_set_class f8_caofrss a_cfv p_eqidd f0_caofrss i0_caofrss f3_caofrss f3_caofrss i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f6_caofrss f3_caofrss f7_caofrss f8_caofrss f9_caofrss f9_caofrss p_ofrfval f0_caofrss i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f4_caofrss a_wbr i0_caofrss f3_caofrss a_wral i0_caofrss a_sup_set_class f7_caofrss a_cfv i0_caofrss a_sup_set_class f8_caofrss a_cfv f6_caofrss a_wbr i0_caofrss f3_caofrss a_wral f7_caofrss f8_caofrss f4_caofrss a_cofr a_wbr f7_caofrss f8_caofrss f6_caofrss a_cofr a_wbr p_3imtr4d $.
$}

$(Transfer an associative law to the function operation.  (Contributed
         by Mario Carneiro, 26-Jul-2014.) $)

${
	$v ph x y z A P R S T F G H O V  $.
	$d w x  $.
	$d w x  $.
	$d w x y z F  $.
	$d w x y z G  $.
	$d w x y z H  $.
	$d w x y z O  $.
	$d w x y z P  $.
	$d w x y z ph  $.
	$d w x y z R  $.
	$d w A  $.
	$d w x y z S  $.
	$d w x y z T  $.
	$d w x y z  $.
	f0_caofass $f wff ph $.
	f1_caofass $f set x $.
	f2_caofass $f set y $.
	f3_caofass $f set z $.
	f4_caofass $f class A $.
	f5_caofass $f class P $.
	f6_caofass $f class R $.
	f7_caofass $f class S $.
	f8_caofass $f class T $.
	f9_caofass $f class F $.
	f10_caofass $f class G $.
	f11_caofass $f class H $.
	f12_caofass $f class O $.
	f13_caofass $f class V $.
	i0_caofass $f set w $.
	e0_caofass $e |- ( ph -> A e. V ) $.
	e1_caofass $e |- ( ph -> F : A --> S ) $.
	e2_caofass $e |- ( ph -> G : A --> S ) $.
	e3_caofass $e |- ( ph -> H : A --> S ) $.
	e4_caofass $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x R y ) T z ) = ( x O ( y P z ) ) ) $.
	p_caofass $p |- ( ph -> ( ( F oF R G ) oF T H ) = ( F oF O ( G oF P H ) ) ) $= e4_caofass f0_caofass f1_caofass a_sup_set_class f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co f1_caofass a_sup_set_class f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co a_wceq f1_caofass f2_caofass f3_caofass f7_caofass f7_caofass f7_caofass p_ralrimivvva f0_caofass f1_caofass a_sup_set_class f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co f1_caofass a_sup_set_class f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co a_wceq f3_caofass f7_caofass a_wral f2_caofass f7_caofass a_wral f1_caofass f7_caofass a_wral i0_caofass a_sup_set_class f4_caofass a_wcel p_adantr e1_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f9_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f9_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f9_caofass a_cfv f7_caofass a_wcel p_sylan e2_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f10_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f10_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f10_caofass a_cfv f7_caofass a_wcel p_sylan e3_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f11_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f11_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f11_caofass a_cfv f7_caofass a_wcel p_sylan f1_caofass a_sup_set_class i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f6_caofass p_oveq1 f1_caofass a_sup_set_class i0_caofass a_sup_set_class f9_caofass a_cfv a_wceq f1_caofass a_sup_set_class f2_caofass a_sup_set_class f6_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass p_oveq1d f1_caofass a_sup_set_class i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass p_oveq1 f1_caofass a_sup_set_class i0_caofass a_sup_set_class f9_caofass a_cfv a_wceq f1_caofass a_sup_set_class f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co f1_caofass a_sup_set_class f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co p_eqeq12d f2_caofass a_sup_set_class i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f9_caofass a_cfv f6_caofass p_oveq2 f2_caofass a_sup_set_class i0_caofass a_sup_set_class f10_caofass a_cfv a_wceq i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f6_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co f3_caofass a_sup_set_class f8_caofass p_oveq1d f2_caofass a_sup_set_class i0_caofass a_sup_set_class f10_caofass a_cfv f3_caofass a_sup_set_class f5_caofass p_oveq1 f2_caofass a_sup_set_class i0_caofass a_sup_set_class f10_caofass a_cfv a_wceq f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co i0_caofass a_sup_set_class f10_caofass a_cfv f3_caofass a_sup_set_class f5_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv f12_caofass p_oveq2d f2_caofass a_sup_set_class i0_caofass a_sup_set_class f10_caofass a_cfv a_wceq i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co p_eqeq12d f3_caofass a_sup_set_class i0_caofass a_sup_set_class f11_caofass a_cfv i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co f8_caofass p_oveq2 f3_caofass a_sup_set_class i0_caofass a_sup_set_class f11_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f5_caofass p_oveq2 f3_caofass a_sup_set_class i0_caofass a_sup_set_class f11_caofass a_cfv a_wceq i0_caofass a_sup_set_class f10_caofass a_cfv f3_caofass a_sup_set_class f5_caofass a_co i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv f12_caofass p_oveq2d f3_caofass a_sup_set_class i0_caofass a_sup_set_class f11_caofass a_cfv a_wceq i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co i0_caofass a_sup_set_class f11_caofass a_cfv f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co f12_caofass a_co p_eqeq12d f1_caofass a_sup_set_class f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co f1_caofass a_sup_set_class f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co a_wceq i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co i0_caofass a_sup_set_class f11_caofass a_cfv f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co f12_caofass a_co a_wceq i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co a_wceq i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co a_wceq f1_caofass f2_caofass f3_caofass i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f7_caofass f7_caofass f7_caofass p_rspc3v f0_caofass i0_caofass a_sup_set_class f4_caofass a_wcel a_wa i0_caofass a_sup_set_class f9_caofass a_cfv f7_caofass a_wcel i0_caofass a_sup_set_class f10_caofass a_cfv f7_caofass a_wcel i0_caofass a_sup_set_class f11_caofass a_cfv f7_caofass a_wcel f1_caofass a_sup_set_class f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co f1_caofass a_sup_set_class f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co a_wceq f3_caofass f7_caofass a_wral f2_caofass f7_caofass a_wral f1_caofass f7_caofass a_wral i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co i0_caofass a_sup_set_class f11_caofass a_cfv f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co f12_caofass a_co a_wceq a_wi p_syl3anc f0_caofass i0_caofass a_sup_set_class f4_caofass a_wcel a_wa f1_caofass a_sup_set_class f2_caofass a_sup_set_class f6_caofass a_co f3_caofass a_sup_set_class f8_caofass a_co f1_caofass a_sup_set_class f2_caofass a_sup_set_class f3_caofass a_sup_set_class f5_caofass a_co f12_caofass a_co a_wceq f3_caofass f7_caofass a_wral f2_caofass f7_caofass a_wral f1_caofass f7_caofass a_wral i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co i0_caofass a_sup_set_class f11_caofass a_cfv f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co f12_caofass a_co a_wceq p_mpd f0_caofass i0_caofass f4_caofass i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co i0_caofass a_sup_set_class f11_caofass a_cfv f8_caofass a_co i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co f12_caofass a_co p_mpteq2dva e0_caofass i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass p_ovex i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co a_cvv a_wcel f0_caofass i0_caofass a_sup_set_class f4_caofass a_wcel a_wa p_a1i e3_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f11_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f11_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f11_caofass a_cfv f7_caofass a_wcel p_sylan e0_caofass e1_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f9_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f9_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f9_caofass a_cfv f7_caofass a_wcel p_sylan e2_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f10_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f10_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f10_caofass a_cfv f7_caofass a_wcel p_sylan e1_caofass f0_caofass i0_caofass f4_caofass f7_caofass f9_caofass p_feqmptd e2_caofass f0_caofass i0_caofass f4_caofass f7_caofass f10_caofass p_feqmptd f0_caofass i0_caofass f4_caofass i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass f9_caofass f10_caofass f13_caofass f7_caofass f7_caofass p_offval2 e3_caofass f0_caofass i0_caofass f4_caofass f7_caofass f11_caofass p_feqmptd f0_caofass i0_caofass f4_caofass i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co i0_caofass a_sup_set_class f11_caofass a_cfv f8_caofass f9_caofass f10_caofass f6_caofass a_cof a_co f11_caofass f13_caofass a_cvv f7_caofass p_offval2 e0_caofass e1_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f9_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f9_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f9_caofass a_cfv f7_caofass a_wcel p_sylan i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass p_ovex i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co a_cvv a_wcel f0_caofass i0_caofass a_sup_set_class f4_caofass a_wcel a_wa p_a1i e1_caofass f0_caofass i0_caofass f4_caofass f7_caofass f9_caofass p_feqmptd e0_caofass e2_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f10_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f10_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f10_caofass a_cfv f7_caofass a_wcel p_sylan e3_caofass f4_caofass f7_caofass i0_caofass a_sup_set_class f11_caofass p_ffvelrn f0_caofass f4_caofass f7_caofass f11_caofass a_wf i0_caofass a_sup_set_class f4_caofass a_wcel i0_caofass a_sup_set_class f11_caofass a_cfv f7_caofass a_wcel p_sylan e2_caofass f0_caofass i0_caofass f4_caofass f7_caofass f10_caofass p_feqmptd e3_caofass f0_caofass i0_caofass f4_caofass f7_caofass f11_caofass p_feqmptd f0_caofass i0_caofass f4_caofass i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass f10_caofass f11_caofass f13_caofass f7_caofass f7_caofass p_offval2 f0_caofass i0_caofass f4_caofass i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co f12_caofass f9_caofass f10_caofass f11_caofass f5_caofass a_cof a_co f13_caofass f7_caofass a_cvv p_offval2 f0_caofass i0_caofass f4_caofass i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv f6_caofass a_co i0_caofass a_sup_set_class f11_caofass a_cfv f8_caofass a_co a_cmpt i0_caofass f4_caofass i0_caofass a_sup_set_class f9_caofass a_cfv i0_caofass a_sup_set_class f10_caofass a_cfv i0_caofass a_sup_set_class f11_caofass a_cfv f5_caofass a_co f12_caofass a_co a_cmpt f9_caofass f10_caofass f6_caofass a_cof a_co f11_caofass f8_caofass a_cof a_co f9_caofass f10_caofass f11_caofass f5_caofass a_cof a_co f12_caofass a_cof a_co p_3eqtr4d $.
$}

$(Transfer a transitivity law to the function relation.  (Contributed by
         Mario Carneiro, 28-Jul-2014.) $)

${
	$v ph x y z A R S T U F G H V  $.
	$d w x  $.
	$d w x  $.
	$d w x y z F  $.
	$d w x y z G  $.
	$d w x y z H  $.
	$d w x y z  $.
	$d w x y z  $.
	$d w x y z ph  $.
	$d w x y z R  $.
	$d w A  $.
	$d w x y z S  $.
	$d w x y z T  $.
	$d w x y z U  $.
	f0_caoftrn $f wff ph $.
	f1_caoftrn $f set x $.
	f2_caoftrn $f set y $.
	f3_caoftrn $f set z $.
	f4_caoftrn $f class A $.
	f5_caoftrn $f class R $.
	f6_caoftrn $f class S $.
	f7_caoftrn $f class T $.
	f8_caoftrn $f class U $.
	f9_caoftrn $f class F $.
	f10_caoftrn $f class G $.
	f11_caoftrn $f class H $.
	f12_caoftrn $f class V $.
	i0_caoftrn $f set w $.
	e0_caoftrn $e |- ( ph -> A e. V ) $.
	e1_caoftrn $e |- ( ph -> F : A --> S ) $.
	e2_caoftrn $e |- ( ph -> G : A --> S ) $.
	e3_caoftrn $e |- ( ph -> H : A --> S ) $.
	e4_caoftrn $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x R y /\ y T z ) -> x U z ) ) $.
	p_caoftrn $p |- ( ph -> ( ( F oR R G /\ G oR T H ) -> F oR U H ) ) $= e4_caoftrn f0_caoftrn f1_caoftrn a_sup_set_class f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa f1_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f8_caoftrn a_wbr a_wi f1_caoftrn f2_caoftrn f3_caoftrn f6_caoftrn f6_caoftrn f6_caoftrn p_ralrimivvva f0_caoftrn f1_caoftrn a_sup_set_class f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa f1_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f8_caoftrn a_wbr a_wi f3_caoftrn f6_caoftrn a_wral f2_caoftrn f6_caoftrn a_wral f1_caoftrn f6_caoftrn a_wral i0_caoftrn a_sup_set_class f4_caoftrn a_wcel p_adantr e1_caoftrn f4_caoftrn f6_caoftrn i0_caoftrn a_sup_set_class f9_caoftrn p_ffvelrn f0_caoftrn f4_caoftrn f6_caoftrn f9_caoftrn a_wf i0_caoftrn a_sup_set_class f4_caoftrn a_wcel i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f6_caoftrn a_wcel p_sylan e2_caoftrn f4_caoftrn f6_caoftrn i0_caoftrn a_sup_set_class f10_caoftrn p_ffvelrn f0_caoftrn f4_caoftrn f6_caoftrn f10_caoftrn a_wf i0_caoftrn a_sup_set_class f4_caoftrn a_wcel i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f6_caoftrn a_wcel p_sylan e3_caoftrn f4_caoftrn f6_caoftrn i0_caoftrn a_sup_set_class f11_caoftrn p_ffvelrn f0_caoftrn f4_caoftrn f6_caoftrn f11_caoftrn a_wf i0_caoftrn a_sup_set_class f4_caoftrn a_wcel i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f6_caoftrn a_wcel p_sylan f1_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f2_caoftrn a_sup_set_class f5_caoftrn p_breq1 f1_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f9_caoftrn a_cfv a_wceq f1_caoftrn a_sup_set_class f2_caoftrn a_sup_set_class f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr p_anbi1d f1_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f3_caoftrn a_sup_set_class f8_caoftrn p_breq1 f1_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f9_caoftrn a_cfv a_wceq f1_caoftrn a_sup_set_class f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa f1_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f8_caoftrn a_wbr i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f3_caoftrn a_sup_set_class f8_caoftrn a_wbr p_imbi12d f2_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f5_caoftrn p_breq2 f2_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f3_caoftrn a_sup_set_class f7_caoftrn p_breq1 f2_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f10_caoftrn a_cfv a_wceq i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f2_caoftrn a_sup_set_class f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f3_caoftrn a_sup_set_class f7_caoftrn a_wbr p_anbi12d f2_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f10_caoftrn a_cfv a_wceq i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f3_caoftrn a_sup_set_class f8_caoftrn a_wbr p_imbi1d f3_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f11_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f7_caoftrn p_breq2 f3_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f11_caoftrn a_cfv a_wceq i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f3_caoftrn a_sup_set_class f7_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr p_anbi2d f3_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f11_caoftrn a_cfv i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f8_caoftrn p_breq2 f3_caoftrn a_sup_set_class i0_caoftrn a_sup_set_class f11_caoftrn a_cfv a_wceq i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f3_caoftrn a_sup_set_class f8_caoftrn a_wbr i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f8_caoftrn a_wbr p_imbi12d f1_caoftrn a_sup_set_class f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa f1_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f8_caoftrn a_wbr a_wi i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f8_caoftrn a_wbr a_wi i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f3_caoftrn a_sup_set_class f8_caoftrn a_wbr a_wi i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f3_caoftrn a_sup_set_class f8_caoftrn a_wbr a_wi f1_caoftrn f2_caoftrn f3_caoftrn i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f6_caoftrn f6_caoftrn f6_caoftrn p_rspc3v f0_caoftrn i0_caoftrn a_sup_set_class f4_caoftrn a_wcel a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv f6_caoftrn a_wcel i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f6_caoftrn a_wcel i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f6_caoftrn a_wcel f1_caoftrn a_sup_set_class f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa f1_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f8_caoftrn a_wbr a_wi f3_caoftrn f6_caoftrn a_wral f2_caoftrn f6_caoftrn a_wral f1_caoftrn f6_caoftrn a_wral i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f8_caoftrn a_wbr a_wi a_wi p_syl3anc f0_caoftrn i0_caoftrn a_sup_set_class f4_caoftrn a_wcel a_wa f1_caoftrn a_sup_set_class f2_caoftrn a_sup_set_class f5_caoftrn a_wbr f2_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f7_caoftrn a_wbr a_wa f1_caoftrn a_sup_set_class f3_caoftrn a_sup_set_class f8_caoftrn a_wbr a_wi f3_caoftrn f6_caoftrn a_wral f2_caoftrn f6_caoftrn a_wral f1_caoftrn f6_caoftrn a_wral i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f8_caoftrn a_wbr a_wi p_mpd f0_caoftrn i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f8_caoftrn a_wbr i0_caoftrn f4_caoftrn p_ralimdva e1_caoftrn f4_caoftrn f6_caoftrn f9_caoftrn p_ffn f0_caoftrn f4_caoftrn f6_caoftrn f9_caoftrn a_wf f9_caoftrn f4_caoftrn a_wfn p_syl e2_caoftrn f4_caoftrn f6_caoftrn f10_caoftrn p_ffn f0_caoftrn f4_caoftrn f6_caoftrn f10_caoftrn a_wf f10_caoftrn f4_caoftrn a_wfn p_syl e0_caoftrn e0_caoftrn f4_caoftrn p_inidm f0_caoftrn i0_caoftrn a_sup_set_class f4_caoftrn a_wcel a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv p_eqidd f0_caoftrn i0_caoftrn a_sup_set_class f4_caoftrn a_wcel a_wa i0_caoftrn a_sup_set_class f10_caoftrn a_cfv p_eqidd f0_caoftrn i0_caoftrn f4_caoftrn f4_caoftrn i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn f4_caoftrn f9_caoftrn f10_caoftrn f12_caoftrn f12_caoftrn p_ofrfval e2_caoftrn f4_caoftrn f6_caoftrn f10_caoftrn p_ffn f0_caoftrn f4_caoftrn f6_caoftrn f10_caoftrn a_wf f10_caoftrn f4_caoftrn a_wfn p_syl e3_caoftrn f4_caoftrn f6_caoftrn f11_caoftrn p_ffn f0_caoftrn f4_caoftrn f6_caoftrn f11_caoftrn a_wf f11_caoftrn f4_caoftrn a_wfn p_syl e0_caoftrn e0_caoftrn f4_caoftrn p_inidm f0_caoftrn i0_caoftrn a_sup_set_class f4_caoftrn a_wcel a_wa i0_caoftrn a_sup_set_class f10_caoftrn a_cfv p_eqidd f0_caoftrn i0_caoftrn a_sup_set_class f4_caoftrn a_wcel a_wa i0_caoftrn a_sup_set_class f11_caoftrn a_cfv p_eqidd f0_caoftrn i0_caoftrn f4_caoftrn f4_caoftrn i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn f4_caoftrn f10_caoftrn f11_caoftrn f12_caoftrn f12_caoftrn p_ofrfval f0_caoftrn f9_caoftrn f10_caoftrn f5_caoftrn a_cofr a_wbr i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn f4_caoftrn a_wral f10_caoftrn f11_caoftrn f7_caoftrn a_cofr a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr i0_caoftrn f4_caoftrn a_wral p_anbi12d i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr i0_caoftrn f4_caoftrn p_r19.26 f0_caoftrn f9_caoftrn f10_caoftrn f5_caoftrn a_cofr a_wbr f10_caoftrn f11_caoftrn f7_caoftrn a_cofr a_wbr a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn f4_caoftrn a_wral i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr i0_caoftrn f4_caoftrn a_wral a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr a_wa i0_caoftrn f4_caoftrn a_wral p_syl6bbr e1_caoftrn f4_caoftrn f6_caoftrn f9_caoftrn p_ffn f0_caoftrn f4_caoftrn f6_caoftrn f9_caoftrn a_wf f9_caoftrn f4_caoftrn a_wfn p_syl e3_caoftrn f4_caoftrn f6_caoftrn f11_caoftrn p_ffn f0_caoftrn f4_caoftrn f6_caoftrn f11_caoftrn a_wf f11_caoftrn f4_caoftrn a_wfn p_syl e0_caoftrn e0_caoftrn f4_caoftrn p_inidm f0_caoftrn i0_caoftrn a_sup_set_class f4_caoftrn a_wcel a_wa i0_caoftrn a_sup_set_class f9_caoftrn a_cfv p_eqidd f0_caoftrn i0_caoftrn a_sup_set_class f4_caoftrn a_wcel a_wa i0_caoftrn a_sup_set_class f11_caoftrn a_cfv p_eqidd f0_caoftrn i0_caoftrn f4_caoftrn f4_caoftrn i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f8_caoftrn f4_caoftrn f9_caoftrn f11_caoftrn f12_caoftrn f12_caoftrn p_ofrfval f0_caoftrn i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f10_caoftrn a_cfv f5_caoftrn a_wbr i0_caoftrn a_sup_set_class f10_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f7_caoftrn a_wbr a_wa i0_caoftrn f4_caoftrn a_wral i0_caoftrn a_sup_set_class f9_caoftrn a_cfv i0_caoftrn a_sup_set_class f11_caoftrn a_cfv f8_caoftrn a_wbr i0_caoftrn f4_caoftrn a_wral f9_caoftrn f10_caoftrn f5_caoftrn a_cofr a_wbr f10_caoftrn f11_caoftrn f7_caoftrn a_cofr a_wbr a_wa f9_caoftrn f11_caoftrn f8_caoftrn a_cofr a_wbr p_3imtr4d $.
$}

$(Transfer a distributive law to the function operation.  (Contributed
         by Mario Carneiro, 26-Jul-2014.) $)

${
	$v ph x y z A R S T F G H K O V  $.
	$d w x y z A  $.
	$d w x y z F  $.
	$d w x y z G  $.
	$d w x y z ph  $.
	$d w x y z H  $.
	$d w x y z K  $.
	$d w x y z O  $.
	$d w x y z R  $.
	$d w x y z S  $.
	$d w x y z T  $.
	f0_caofdi $f wff ph $.
	f1_caofdi $f set x $.
	f2_caofdi $f set y $.
	f3_caofdi $f set z $.
	f4_caofdi $f class A $.
	f5_caofdi $f class R $.
	f6_caofdi $f class S $.
	f7_caofdi $f class T $.
	f8_caofdi $f class F $.
	f9_caofdi $f class G $.
	f10_caofdi $f class H $.
	f11_caofdi $f class K $.
	f12_caofdi $f class O $.
	f13_caofdi $f class V $.
	i0_caofdi $f set w $.
	e0_caofdi $e |- ( ph -> A e. V ) $.
	e1_caofdi $e |- ( ph -> F : A --> K ) $.
	e2_caofdi $e |- ( ph -> G : A --> S ) $.
	e3_caofdi $e |- ( ph -> H : A --> S ) $.
	e4_caofdi $e |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x T ( y R z ) ) = ( ( x T y ) O ( x T z ) ) ) $.
	p_caofdi $p |- ( ph -> ( F oF T ( G oF R H ) ) = ( ( F oF T G ) oF O ( F oF T H ) ) ) $= e4_caofdi f0_caofdi f1_caofdi a_sup_set_class f11_caofdi a_wcel f2_caofdi a_sup_set_class f6_caofdi a_wcel f3_caofdi a_sup_set_class f6_caofdi a_wcel a_w3a f1_caofdi a_sup_set_class f2_caofdi a_sup_set_class f3_caofdi a_sup_set_class f5_caofdi a_co f7_caofdi a_co f1_caofdi a_sup_set_class f2_caofdi a_sup_set_class f7_caofdi a_co f1_caofdi a_sup_set_class f3_caofdi a_sup_set_class f7_caofdi a_co f12_caofdi a_co a_wceq i0_caofdi a_sup_set_class f4_caofdi a_wcel p_adantlr e1_caofdi f4_caofdi f11_caofdi i0_caofdi a_sup_set_class f8_caofdi p_ffvelrn f0_caofdi f4_caofdi f11_caofdi f8_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f8_caofdi a_cfv f11_caofdi a_wcel p_sylan e2_caofdi f4_caofdi f6_caofdi i0_caofdi a_sup_set_class f9_caofdi p_ffvelrn f0_caofdi f4_caofdi f6_caofdi f9_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f9_caofdi a_cfv f6_caofdi a_wcel p_sylan e3_caofdi f4_caofdi f6_caofdi i0_caofdi a_sup_set_class f10_caofdi p_ffvelrn f0_caofdi f4_caofdi f6_caofdi f10_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f10_caofdi a_cfv f6_caofdi a_wcel p_sylan f0_caofdi i0_caofdi a_sup_set_class f4_caofdi a_wcel a_wa f1_caofdi f2_caofdi f3_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f6_caofdi f5_caofdi f7_caofdi f12_caofdi f11_caofdi p_caovdid f0_caofdi i0_caofdi f4_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f5_caofdi a_co f7_caofdi a_co i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv f7_caofdi a_co i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f7_caofdi a_co f12_caofdi a_co p_mpteq2dva e0_caofdi e1_caofdi f4_caofdi f11_caofdi i0_caofdi a_sup_set_class f8_caofdi p_ffvelrn f0_caofdi f4_caofdi f11_caofdi f8_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f8_caofdi a_cfv f11_caofdi a_wcel p_sylan i0_caofdi a_sup_set_class f9_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f5_caofdi p_ovex i0_caofdi a_sup_set_class f9_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f5_caofdi a_co a_cvv a_wcel f0_caofdi i0_caofdi a_sup_set_class f4_caofdi a_wcel a_wa p_a1i e1_caofdi f0_caofdi i0_caofdi f4_caofdi f11_caofdi f8_caofdi p_feqmptd e0_caofdi e2_caofdi f4_caofdi f6_caofdi i0_caofdi a_sup_set_class f9_caofdi p_ffvelrn f0_caofdi f4_caofdi f6_caofdi f9_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f9_caofdi a_cfv f6_caofdi a_wcel p_sylan e3_caofdi f4_caofdi f6_caofdi i0_caofdi a_sup_set_class f10_caofdi p_ffvelrn f0_caofdi f4_caofdi f6_caofdi f10_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f10_caofdi a_cfv f6_caofdi a_wcel p_sylan e2_caofdi f0_caofdi i0_caofdi f4_caofdi f6_caofdi f9_caofdi p_feqmptd e3_caofdi f0_caofdi i0_caofdi f4_caofdi f6_caofdi f10_caofdi p_feqmptd f0_caofdi i0_caofdi f4_caofdi i0_caofdi a_sup_set_class f9_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f5_caofdi f9_caofdi f10_caofdi f13_caofdi f6_caofdi f6_caofdi p_offval2 f0_caofdi i0_caofdi f4_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f5_caofdi a_co f7_caofdi f8_caofdi f9_caofdi f10_caofdi f5_caofdi a_cof a_co f13_caofdi f11_caofdi a_cvv p_offval2 e0_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv f7_caofdi p_ovex i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv f7_caofdi a_co a_cvv a_wcel f0_caofdi i0_caofdi a_sup_set_class f4_caofdi a_wcel a_wa p_a1i i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f7_caofdi p_ovex i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f7_caofdi a_co a_cvv a_wcel f0_caofdi i0_caofdi a_sup_set_class f4_caofdi a_wcel a_wa p_a1i e0_caofdi e1_caofdi f4_caofdi f11_caofdi i0_caofdi a_sup_set_class f8_caofdi p_ffvelrn f0_caofdi f4_caofdi f11_caofdi f8_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f8_caofdi a_cfv f11_caofdi a_wcel p_sylan e2_caofdi f4_caofdi f6_caofdi i0_caofdi a_sup_set_class f9_caofdi p_ffvelrn f0_caofdi f4_caofdi f6_caofdi f9_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f9_caofdi a_cfv f6_caofdi a_wcel p_sylan e1_caofdi f0_caofdi i0_caofdi f4_caofdi f11_caofdi f8_caofdi p_feqmptd e2_caofdi f0_caofdi i0_caofdi f4_caofdi f6_caofdi f9_caofdi p_feqmptd f0_caofdi i0_caofdi f4_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv f7_caofdi f8_caofdi f9_caofdi f13_caofdi f11_caofdi f6_caofdi p_offval2 e0_caofdi e1_caofdi f4_caofdi f11_caofdi i0_caofdi a_sup_set_class f8_caofdi p_ffvelrn f0_caofdi f4_caofdi f11_caofdi f8_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f8_caofdi a_cfv f11_caofdi a_wcel p_sylan e3_caofdi f4_caofdi f6_caofdi i0_caofdi a_sup_set_class f10_caofdi p_ffvelrn f0_caofdi f4_caofdi f6_caofdi f10_caofdi a_wf i0_caofdi a_sup_set_class f4_caofdi a_wcel i0_caofdi a_sup_set_class f10_caofdi a_cfv f6_caofdi a_wcel p_sylan e1_caofdi f0_caofdi i0_caofdi f4_caofdi f11_caofdi f8_caofdi p_feqmptd e3_caofdi f0_caofdi i0_caofdi f4_caofdi f6_caofdi f10_caofdi p_feqmptd f0_caofdi i0_caofdi f4_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f7_caofdi f8_caofdi f10_caofdi f13_caofdi f11_caofdi f6_caofdi p_offval2 f0_caofdi i0_caofdi f4_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv f7_caofdi a_co i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f7_caofdi a_co f12_caofdi f8_caofdi f9_caofdi f7_caofdi a_cof a_co f8_caofdi f10_caofdi f7_caofdi a_cof a_co f13_caofdi a_cvv a_cvv p_offval2 f0_caofdi i0_caofdi f4_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f5_caofdi a_co f7_caofdi a_co a_cmpt i0_caofdi f4_caofdi i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f9_caofdi a_cfv f7_caofdi a_co i0_caofdi a_sup_set_class f8_caofdi a_cfv i0_caofdi a_sup_set_class f10_caofdi a_cfv f7_caofdi a_co f12_caofdi a_co a_cmpt f8_caofdi f9_caofdi f10_caofdi f5_caofdi a_cof a_co f7_caofdi a_cof a_co f8_caofdi f9_caofdi f7_caofdi a_cof a_co f8_caofdi f10_caofdi f7_caofdi a_cof a_co f12_caofdi a_cof a_co p_3eqtr4d $.
$}

$(Transfer a reverse distributive law to the function operation.
         (Contributed by NM, 19-Oct-2014.) $)

${
	$v ph x y z A R S T F G H K O V  $.
	$d w x y z A  $.
	$d w x y z F  $.
	$d w x y z G  $.
	$d w x y z ph  $.
	$d w x y z H  $.
	$d w x y z K  $.
	$d w x y z O  $.
	$d w x y z R  $.
	$d w x y z S  $.
	$d w x y z T  $.
	f0_caofdir $f wff ph $.
	f1_caofdir $f set x $.
	f2_caofdir $f set y $.
	f3_caofdir $f set z $.
	f4_caofdir $f class A $.
	f5_caofdir $f class R $.
	f6_caofdir $f class S $.
	f7_caofdir $f class T $.
	f8_caofdir $f class F $.
	f9_caofdir $f class G $.
	f10_caofdir $f class H $.
	f11_caofdir $f class K $.
	f12_caofdir $f class O $.
	f13_caofdir $f class V $.
	i0_caofdir $f set w $.
	e0_caofdir $e |- ( ph -> A e. V ) $.
	e1_caofdir $e |- ( ph -> F : A --> K ) $.
	e2_caofdir $e |- ( ph -> G : A --> S ) $.
	e3_caofdir $e |- ( ph -> H : A --> S ) $.
	e4_caofdir $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x R y ) T z ) = ( ( x T z ) O ( y T z ) ) ) $.
	p_caofdir $p |- ( ph -> ( ( G oF R H ) oF T F ) = ( ( G oF T F ) oF O ( H oF T F ) ) ) $= e4_caofdir f0_caofdir f1_caofdir a_sup_set_class f6_caofdir a_wcel f2_caofdir a_sup_set_class f6_caofdir a_wcel f3_caofdir a_sup_set_class f11_caofdir a_wcel a_w3a f1_caofdir a_sup_set_class f2_caofdir a_sup_set_class f5_caofdir a_co f3_caofdir a_sup_set_class f7_caofdir a_co f1_caofdir a_sup_set_class f3_caofdir a_sup_set_class f7_caofdir a_co f2_caofdir a_sup_set_class f3_caofdir a_sup_set_class f7_caofdir a_co f12_caofdir a_co a_wceq i0_caofdir a_sup_set_class f4_caofdir a_wcel p_adantlr e2_caofdir f4_caofdir f6_caofdir i0_caofdir a_sup_set_class f9_caofdir p_ffvelrn f0_caofdir f4_caofdir f6_caofdir f9_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f9_caofdir a_cfv f6_caofdir a_wcel p_sylan e3_caofdir f4_caofdir f6_caofdir i0_caofdir a_sup_set_class f10_caofdir p_ffvelrn f0_caofdir f4_caofdir f6_caofdir f10_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f10_caofdir a_cfv f6_caofdir a_wcel p_sylan e1_caofdir f4_caofdir f11_caofdir i0_caofdir a_sup_set_class f8_caofdir p_ffvelrn f0_caofdir f4_caofdir f11_caofdir f8_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f8_caofdir a_cfv f11_caofdir a_wcel p_sylan f0_caofdir i0_caofdir a_sup_set_class f4_caofdir a_wcel a_wa f1_caofdir f2_caofdir f3_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f10_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f6_caofdir f5_caofdir f7_caofdir f12_caofdir f11_caofdir p_caovdird f0_caofdir i0_caofdir f4_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f10_caofdir a_cfv f5_caofdir a_co i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co i0_caofdir a_sup_set_class f10_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co f12_caofdir a_co p_mpteq2dva e0_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f10_caofdir a_cfv f5_caofdir p_ovex i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f10_caofdir a_cfv f5_caofdir a_co a_cvv a_wcel f0_caofdir i0_caofdir a_sup_set_class f4_caofdir a_wcel a_wa p_a1i e1_caofdir f4_caofdir f11_caofdir i0_caofdir a_sup_set_class f8_caofdir p_ffvelrn f0_caofdir f4_caofdir f11_caofdir f8_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f8_caofdir a_cfv f11_caofdir a_wcel p_sylan e0_caofdir e2_caofdir f4_caofdir f6_caofdir i0_caofdir a_sup_set_class f9_caofdir p_ffvelrn f0_caofdir f4_caofdir f6_caofdir f9_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f9_caofdir a_cfv f6_caofdir a_wcel p_sylan e3_caofdir f4_caofdir f6_caofdir i0_caofdir a_sup_set_class f10_caofdir p_ffvelrn f0_caofdir f4_caofdir f6_caofdir f10_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f10_caofdir a_cfv f6_caofdir a_wcel p_sylan e2_caofdir f0_caofdir i0_caofdir f4_caofdir f6_caofdir f9_caofdir p_feqmptd e3_caofdir f0_caofdir i0_caofdir f4_caofdir f6_caofdir f10_caofdir p_feqmptd f0_caofdir i0_caofdir f4_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f10_caofdir a_cfv f5_caofdir f9_caofdir f10_caofdir f13_caofdir f6_caofdir f6_caofdir p_offval2 e1_caofdir f0_caofdir i0_caofdir f4_caofdir f11_caofdir f8_caofdir p_feqmptd f0_caofdir i0_caofdir f4_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f10_caofdir a_cfv f5_caofdir a_co i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir f9_caofdir f10_caofdir f5_caofdir a_cof a_co f8_caofdir f13_caofdir a_cvv f11_caofdir p_offval2 e0_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir p_ovex i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co a_cvv a_wcel f0_caofdir i0_caofdir a_sup_set_class f4_caofdir a_wcel a_wa p_a1i i0_caofdir a_sup_set_class f10_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir p_ovex i0_caofdir a_sup_set_class f10_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co a_cvv a_wcel f0_caofdir i0_caofdir a_sup_set_class f4_caofdir a_wcel a_wa p_a1i e0_caofdir e2_caofdir f4_caofdir f6_caofdir i0_caofdir a_sup_set_class f9_caofdir p_ffvelrn f0_caofdir f4_caofdir f6_caofdir f9_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f9_caofdir a_cfv f6_caofdir a_wcel p_sylan e1_caofdir f4_caofdir f11_caofdir i0_caofdir a_sup_set_class f8_caofdir p_ffvelrn f0_caofdir f4_caofdir f11_caofdir f8_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f8_caofdir a_cfv f11_caofdir a_wcel p_sylan e2_caofdir f0_caofdir i0_caofdir f4_caofdir f6_caofdir f9_caofdir p_feqmptd e1_caofdir f0_caofdir i0_caofdir f4_caofdir f11_caofdir f8_caofdir p_feqmptd f0_caofdir i0_caofdir f4_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir f9_caofdir f8_caofdir f13_caofdir f6_caofdir f11_caofdir p_offval2 e0_caofdir e3_caofdir f4_caofdir f6_caofdir i0_caofdir a_sup_set_class f10_caofdir p_ffvelrn f0_caofdir f4_caofdir f6_caofdir f10_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f10_caofdir a_cfv f6_caofdir a_wcel p_sylan e1_caofdir f4_caofdir f11_caofdir i0_caofdir a_sup_set_class f8_caofdir p_ffvelrn f0_caofdir f4_caofdir f11_caofdir f8_caofdir a_wf i0_caofdir a_sup_set_class f4_caofdir a_wcel i0_caofdir a_sup_set_class f8_caofdir a_cfv f11_caofdir a_wcel p_sylan e3_caofdir f0_caofdir i0_caofdir f4_caofdir f6_caofdir f10_caofdir p_feqmptd e1_caofdir f0_caofdir i0_caofdir f4_caofdir f11_caofdir f8_caofdir p_feqmptd f0_caofdir i0_caofdir f4_caofdir i0_caofdir a_sup_set_class f10_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir f10_caofdir f8_caofdir f13_caofdir f6_caofdir f11_caofdir p_offval2 f0_caofdir i0_caofdir f4_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co i0_caofdir a_sup_set_class f10_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co f12_caofdir f9_caofdir f8_caofdir f7_caofdir a_cof a_co f10_caofdir f8_caofdir f7_caofdir a_cof a_co f13_caofdir a_cvv a_cvv p_offval2 f0_caofdir i0_caofdir f4_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f10_caofdir a_cfv f5_caofdir a_co i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co a_cmpt i0_caofdir f4_caofdir i0_caofdir a_sup_set_class f9_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co i0_caofdir a_sup_set_class f10_caofdir a_cfv i0_caofdir a_sup_set_class f8_caofdir a_cfv f7_caofdir a_co f12_caofdir a_co a_cmpt f9_caofdir f10_caofdir f5_caofdir a_cof a_co f8_caofdir f7_caofdir a_cof a_co f9_caofdir f8_caofdir f7_caofdir a_cof a_co f10_caofdir f8_caofdir f7_caofdir a_cof a_co f12_caofdir a_cof a_co p_3eqtr4d $.
$}

$(Transfer ~ nncan -shaped laws to vectors of numbers.  (Contributed by
       Stefan O'Rear, 27-Mar-2015.) $)

${
	$v ph x y A B S I M V  $.
	$d ph x y z  $.
	$d A x y z  $.
	$d B y z  $.
	$d I z  $.
	$d M x y z  $.
	$d S x y  $.
	f0_caonncan $f wff ph $.
	f1_caonncan $f set x $.
	f2_caonncan $f set y $.
	f3_caonncan $f class A $.
	f4_caonncan $f class B $.
	f5_caonncan $f class S $.
	f6_caonncan $f class I $.
	f7_caonncan $f class M $.
	f8_caonncan $f class V $.
	i0_caonncan $f set z $.
	e0_caonncan $e |- ( ph -> I e. V ) $.
	e1_caonncan $e |- ( ph -> A : I --> S ) $.
	e2_caonncan $e |- ( ph -> B : I --> S ) $.
	e3_caonncan $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x M ( x M y ) ) = y ) $.
	p_caonncan $p |- ( ph -> ( A oF M ( A oF M B ) ) = B ) $= e1_caonncan f6_caonncan f5_caonncan i0_caonncan a_sup_set_class f3_caonncan p_ffvelrn f0_caonncan f6_caonncan f5_caonncan f3_caonncan a_wf i0_caonncan a_sup_set_class f6_caonncan a_wcel i0_caonncan a_sup_set_class f3_caonncan a_cfv f5_caonncan a_wcel p_sylan e2_caonncan f6_caonncan f5_caonncan i0_caonncan a_sup_set_class f4_caonncan p_ffvelrn f0_caonncan f6_caonncan f5_caonncan f4_caonncan a_wf i0_caonncan a_sup_set_class f6_caonncan a_wcel i0_caonncan a_sup_set_class f4_caonncan a_cfv f5_caonncan a_wcel p_sylan e3_caonncan f0_caonncan f1_caonncan a_sup_set_class f1_caonncan a_sup_set_class f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan a_co f2_caonncan a_sup_set_class a_wceq f1_caonncan f2_caonncan f5_caonncan f5_caonncan p_ralrimivva f0_caonncan f1_caonncan a_sup_set_class f1_caonncan a_sup_set_class f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan a_co f2_caonncan a_sup_set_class a_wceq f2_caonncan f5_caonncan a_wral f1_caonncan f5_caonncan a_wral i0_caonncan a_sup_set_class f6_caonncan a_wcel p_adantr f1_caonncan a_sup_set_class i0_caonncan a_sup_set_class f3_caonncan a_cfv a_wceq p_id f1_caonncan a_sup_set_class i0_caonncan a_sup_set_class f3_caonncan a_cfv f2_caonncan a_sup_set_class f7_caonncan p_oveq1 f1_caonncan a_sup_set_class i0_caonncan a_sup_set_class f3_caonncan a_cfv a_wceq f1_caonncan a_sup_set_class i0_caonncan a_sup_set_class f3_caonncan a_cfv f1_caonncan a_sup_set_class f2_caonncan a_sup_set_class f7_caonncan a_co i0_caonncan a_sup_set_class f3_caonncan a_cfv f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan p_oveq12d f1_caonncan a_sup_set_class i0_caonncan a_sup_set_class f3_caonncan a_cfv a_wceq f1_caonncan a_sup_set_class f1_caonncan a_sup_set_class f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan a_co i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan a_co f2_caonncan a_sup_set_class p_eqeq1d f2_caonncan a_sup_set_class i0_caonncan a_sup_set_class f4_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv f7_caonncan p_oveq2 f2_caonncan a_sup_set_class i0_caonncan a_sup_set_class f4_caonncan a_cfv a_wceq i0_caonncan a_sup_set_class f3_caonncan a_cfv f2_caonncan a_sup_set_class f7_caonncan a_co i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan a_co i0_caonncan a_sup_set_class f3_caonncan a_cfv f7_caonncan p_oveq2d f2_caonncan a_sup_set_class i0_caonncan a_sup_set_class f4_caonncan a_cfv a_wceq p_id f2_caonncan a_sup_set_class i0_caonncan a_sup_set_class f4_caonncan a_cfv a_wceq i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan a_co i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan a_co f7_caonncan a_co f2_caonncan a_sup_set_class i0_caonncan a_sup_set_class f4_caonncan a_cfv p_eqeq12d f1_caonncan a_sup_set_class f1_caonncan a_sup_set_class f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan a_co f2_caonncan a_sup_set_class a_wceq i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan a_co f7_caonncan a_co i0_caonncan a_sup_set_class f4_caonncan a_cfv a_wceq i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan a_co f2_caonncan a_sup_set_class a_wceq f1_caonncan f2_caonncan i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f5_caonncan f5_caonncan p_rspc2va f0_caonncan i0_caonncan a_sup_set_class f6_caonncan a_wcel a_wa i0_caonncan a_sup_set_class f3_caonncan a_cfv f5_caonncan a_wcel i0_caonncan a_sup_set_class f4_caonncan a_cfv f5_caonncan a_wcel f1_caonncan a_sup_set_class f1_caonncan a_sup_set_class f2_caonncan a_sup_set_class f7_caonncan a_co f7_caonncan a_co f2_caonncan a_sup_set_class a_wceq f2_caonncan f5_caonncan a_wral f1_caonncan f5_caonncan a_wral i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan a_co f7_caonncan a_co i0_caonncan a_sup_set_class f4_caonncan a_cfv a_wceq p_syl21anc f0_caonncan i0_caonncan f6_caonncan i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan a_co f7_caonncan a_co i0_caonncan a_sup_set_class f4_caonncan a_cfv p_mpteq2dva e0_caonncan i0_caonncan a_sup_set_class f3_caonncan p_fvex i0_caonncan a_sup_set_class f3_caonncan a_cfv a_cvv a_wcel f0_caonncan i0_caonncan a_sup_set_class f6_caonncan a_wcel a_wa p_a1i i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan p_ovex i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan a_co a_cvv a_wcel f0_caonncan i0_caonncan a_sup_set_class f6_caonncan a_wcel a_wa p_a1i e1_caonncan f0_caonncan i0_caonncan f6_caonncan f5_caonncan f3_caonncan p_feqmptd e0_caonncan i0_caonncan a_sup_set_class f3_caonncan p_fvex i0_caonncan a_sup_set_class f3_caonncan a_cfv a_cvv a_wcel f0_caonncan i0_caonncan a_sup_set_class f6_caonncan a_wcel a_wa p_a1i i0_caonncan a_sup_set_class f4_caonncan p_fvex i0_caonncan a_sup_set_class f4_caonncan a_cfv a_cvv a_wcel f0_caonncan i0_caonncan a_sup_set_class f6_caonncan a_wcel a_wa p_a1i e1_caonncan f0_caonncan i0_caonncan f6_caonncan f5_caonncan f3_caonncan p_feqmptd e2_caonncan f0_caonncan i0_caonncan f6_caonncan f5_caonncan f4_caonncan p_feqmptd f0_caonncan i0_caonncan f6_caonncan i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan f3_caonncan f4_caonncan f8_caonncan a_cvv a_cvv p_offval2 f0_caonncan i0_caonncan f6_caonncan i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan a_co f7_caonncan f3_caonncan f3_caonncan f4_caonncan f7_caonncan a_cof a_co f8_caonncan a_cvv a_cvv p_offval2 e2_caonncan f0_caonncan i0_caonncan f6_caonncan f5_caonncan f4_caonncan p_feqmptd f0_caonncan i0_caonncan f6_caonncan i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f3_caonncan a_cfv i0_caonncan a_sup_set_class f4_caonncan a_cfv f7_caonncan a_co f7_caonncan a_co a_cmpt i0_caonncan f6_caonncan i0_caonncan a_sup_set_class f4_caonncan a_cfv a_cmpt f3_caonncan f3_caonncan f4_caonncan f7_caonncan a_cof a_co f7_caonncan a_cof a_co f4_caonncan p_3eqtr4d $.
$}

$(Equivalent expressions for a restriction of the function operation map.
       Unlike ` oF R ` which is a proper class, ` ( oF R | `` ( A X. B ) ) `
       can be a set by ~ ofmresex , allowing it to be used as a function or
       structure argument.  By ~ ofmresval , the restricted operation map
       values are the same as the original values, allowing theorems for
       ` oF R ` to be reused.  (Contributed by NM, 20-Oct-2014.) $)

${
	$v A B R f g  $.
	$d f g A  $.
	$d f g B  $.
	$d f g x R  $.
	f0_ofmres $f class A $.
	f1_ofmres $f class B $.
	f2_ofmres $f class R $.
	f3_ofmres $f set f $.
	f4_ofmres $f set g $.
	i0_ofmres $f set x $.
	p_ofmres $p |- ( oF R |` ( A X. B ) ) = ( f e. A , g e. B |-> ( f oF R g ) ) $= f0_ofmres p_ssv f1_ofmres p_ssv f3_ofmres f4_ofmres a_cvv a_cvv f0_ofmres f1_ofmres i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt p_resmpt2 f0_ofmres a_cvv a_wss f1_ofmres a_cvv a_wss f3_ofmres f4_ofmres a_cvv a_cvv i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt a_cmpt2 f0_ofmres f1_ofmres a_cxp a_cres f3_ofmres f4_ofmres f0_ofmres f1_ofmres i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt a_cmpt2 a_wceq p_mp2an i0_ofmres f2_ofmres f3_ofmres f4_ofmres a_df-of f2_ofmres a_cof f3_ofmres f4_ofmres a_cvv a_cvv i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt a_cmpt2 f0_ofmres f1_ofmres a_cxp p_reseq1i f0_ofmres p_eqid f1_ofmres p_eqid f3_ofmres p_vex f4_ofmres p_vex f3_ofmres p_vex f3_ofmres a_sup_set_class p_dmex f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm p_inex1 i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co p_mptex i0_ofmres f2_ofmres f3_ofmres f4_ofmres a_df-of f3_ofmres f4_ofmres a_cvv a_cvv i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt f2_ofmres a_cof a_cvv p_ovmpt4g f3_ofmres a_sup_set_class a_cvv a_wcel f4_ofmres a_sup_set_class a_cvv a_wcel i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt a_cvv a_wcel f3_ofmres a_sup_set_class f4_ofmres a_sup_set_class f2_ofmres a_cof a_co i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt a_wceq p_mp3an f3_ofmres f4_ofmres f0_ofmres f1_ofmres f3_ofmres a_sup_set_class f4_ofmres a_sup_set_class f2_ofmres a_cof a_co f0_ofmres f1_ofmres i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt p_mpt2eq123i f3_ofmres f4_ofmres a_cvv a_cvv i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt a_cmpt2 f0_ofmres f1_ofmres a_cxp a_cres f3_ofmres f4_ofmres f0_ofmres f1_ofmres i0_ofmres f3_ofmres a_sup_set_class a_cdm f4_ofmres a_sup_set_class a_cdm a_cin i0_ofmres a_sup_set_class f3_ofmres a_sup_set_class a_cfv i0_ofmres a_sup_set_class f4_ofmres a_sup_set_class a_cfv f2_ofmres a_co a_cmpt a_cmpt2 f2_ofmres a_cof f0_ofmres f1_ofmres a_cxp a_cres f3_ofmres f4_ofmres f0_ofmres f1_ofmres f3_ofmres a_sup_set_class f4_ofmres a_sup_set_class f2_ofmres a_cof a_co a_cmpt2 p_3eqtr4i $.
$}

$(Value of a restriction of the function operation map.  (Contributed by
       NM, 20-Oct-2014.) $)

${
	$v ph A B R F G  $.
	$d A  $.
	$d B  $.
	$d R  $.
	f0_ofmresval $f wff ph $.
	f1_ofmresval $f class A $.
	f2_ofmresval $f class B $.
	f3_ofmresval $f class R $.
	f4_ofmresval $f class F $.
	f5_ofmresval $f class G $.
	e0_ofmresval $e |- ( ph -> F e. A ) $.
	e1_ofmresval $e |- ( ph -> G e. B ) $.
	p_ofmresval $p |- ( ph -> ( F ( oF R |` ( A X. B ) ) G ) = ( F oF R G ) ) $= e0_ofmresval e1_ofmresval f4_ofmresval f5_ofmresval f1_ofmresval f2_ofmresval f3_ofmresval a_cof p_ovres f0_ofmresval f4_ofmresval f1_ofmresval a_wcel f5_ofmresval f2_ofmresval a_wcel f4_ofmresval f5_ofmresval f3_ofmresval a_cof f1_ofmresval f2_ofmresval a_cxp a_cres a_co f4_ofmresval f5_ofmresval f3_ofmresval a_cof a_co a_wceq p_syl2anc $.
$}

$(Existence of a restriction of the function operation map.  (Contributed
       by NM, 20-Oct-2014.) $)

${
	$v ph A B R V W  $.
	$d A  $.
	$d B  $.
	$d R  $.
	f0_ofmresex $f wff ph $.
	f1_ofmresex $f class A $.
	f2_ofmresex $f class B $.
	f3_ofmresex $f class R $.
	f4_ofmresex $f class V $.
	f5_ofmresex $f class W $.
	e0_ofmresex $e |- ( ph -> A e. V ) $.
	e1_ofmresex $e |- ( ph -> B e. W ) $.
	p_ofmresex $p |- ( ph -> ( oF R |` ( A X. B ) ) e. _V ) $= e0_ofmresex e1_ofmresex f1_ofmresex f2_ofmresex f4_ofmresex f5_ofmresex p_xpexg f0_ofmresex f1_ofmresex f4_ofmresex a_wcel f2_ofmresex f5_ofmresex a_wcel f1_ofmresex f2_ofmresex a_cxp a_cvv a_wcel p_syl2anc f1_ofmresex f2_ofmresex a_cxp f3_ofmresex a_cvv p_ofexg f0_ofmresex f1_ofmresex f2_ofmresex a_cxp a_cvv a_wcel f3_ofmresex a_cof f1_ofmresex f2_ofmresex a_cxp a_cres a_cvv a_wcel p_syl $.
$}

$(Formula building theorem for support restrictions: vector operation with
       left annihilator.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)

${
	$v ph v A B D R L O V W Y Z  $.
	$d ph v x  $.
	$d A x  $.
	$d B v x  $.
	$d D x  $.
	$d O v x  $.
	$d R v  $.
	$d Y v x  $.
	$d Z v x  $.
	f0_suppssof1 $f wff ph $.
	f1_suppssof1 $f set v $.
	f2_suppssof1 $f class A $.
	f3_suppssof1 $f class B $.
	f4_suppssof1 $f class D $.
	f5_suppssof1 $f class R $.
	f6_suppssof1 $f class L $.
	f7_suppssof1 $f class O $.
	f8_suppssof1 $f class V $.
	f9_suppssof1 $f class W $.
	f10_suppssof1 $f class Y $.
	f11_suppssof1 $f class Z $.
	i0_suppssof1 $f set x $.
	e0_suppssof1 $e |- ( ph -> ( `' A " ( _V \ { Y } ) ) C_ L ) $.
	e1_suppssof1 $e |- ( ( ph /\ v e. R ) -> ( Y O v ) = Z ) $.
	e2_suppssof1 $e |- ( ph -> A : D --> V ) $.
	e3_suppssof1 $e |- ( ph -> B : D --> R ) $.
	e4_suppssof1 $e |- ( ph -> D e. W ) $.
	p_suppssof1 $p |- ( ph -> ( `' ( A oF O B ) " ( _V \ { Z } ) ) C_ L ) $= e2_suppssof1 f4_suppssof1 f8_suppssof1 f2_suppssof1 p_ffn f0_suppssof1 f4_suppssof1 f8_suppssof1 f2_suppssof1 a_wf f2_suppssof1 f4_suppssof1 a_wfn p_syl e3_suppssof1 f4_suppssof1 f5_suppssof1 f3_suppssof1 p_ffn f0_suppssof1 f4_suppssof1 f5_suppssof1 f3_suppssof1 a_wf f3_suppssof1 f4_suppssof1 a_wfn p_syl e4_suppssof1 e4_suppssof1 f4_suppssof1 p_inidm f0_suppssof1 i0_suppssof1 a_sup_set_class f4_suppssof1 a_wcel a_wa i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv p_eqidd f0_suppssof1 i0_suppssof1 a_sup_set_class f4_suppssof1 a_wcel a_wa i0_suppssof1 a_sup_set_class f3_suppssof1 a_cfv p_eqidd f0_suppssof1 i0_suppssof1 f4_suppssof1 f4_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv i0_suppssof1 a_sup_set_class f3_suppssof1 a_cfv f7_suppssof1 f4_suppssof1 f2_suppssof1 f3_suppssof1 f9_suppssof1 f9_suppssof1 p_offval f0_suppssof1 f2_suppssof1 f3_suppssof1 f7_suppssof1 a_cof a_co i0_suppssof1 f4_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv i0_suppssof1 a_sup_set_class f3_suppssof1 a_cfv f7_suppssof1 a_co a_cmpt p_cnveqd f0_suppssof1 f2_suppssof1 f3_suppssof1 f7_suppssof1 a_cof a_co a_ccnv i0_suppssof1 f4_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv i0_suppssof1 a_sup_set_class f3_suppssof1 a_cfv f7_suppssof1 a_co a_cmpt a_ccnv a_cvv f11_suppssof1 a_csn a_cdif p_imaeq1d e2_suppssof1 f0_suppssof1 i0_suppssof1 f4_suppssof1 f8_suppssof1 f2_suppssof1 p_feqmptd f0_suppssof1 f2_suppssof1 i0_suppssof1 f4_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv a_cmpt p_cnveqd f0_suppssof1 f2_suppssof1 a_ccnv i0_suppssof1 f4_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv a_cmpt a_ccnv a_cvv f10_suppssof1 a_csn a_cdif p_imaeq1d e0_suppssof1 f0_suppssof1 i0_suppssof1 f4_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv a_cmpt a_ccnv a_cvv f10_suppssof1 a_csn a_cdif a_cima f2_suppssof1 a_ccnv a_cvv f10_suppssof1 a_csn a_cdif a_cima f6_suppssof1 p_eqsstr3d e1_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 p_fvex i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv a_cvv a_wcel f0_suppssof1 i0_suppssof1 a_sup_set_class f4_suppssof1 a_wcel a_wa p_a1i e3_suppssof1 f4_suppssof1 f5_suppssof1 i0_suppssof1 a_sup_set_class f3_suppssof1 p_ffvelrn f0_suppssof1 f4_suppssof1 f5_suppssof1 f3_suppssof1 a_wf i0_suppssof1 a_sup_set_class f4_suppssof1 a_wcel i0_suppssof1 a_sup_set_class f3_suppssof1 a_cfv f5_suppssof1 a_wcel p_sylan f0_suppssof1 i0_suppssof1 f1_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv i0_suppssof1 a_sup_set_class f3_suppssof1 a_cfv f4_suppssof1 f5_suppssof1 f6_suppssof1 f7_suppssof1 a_cvv f10_suppssof1 f11_suppssof1 p_suppssov1 f0_suppssof1 f2_suppssof1 f3_suppssof1 f7_suppssof1 a_cof a_co a_ccnv a_cvv f11_suppssof1 a_csn a_cdif a_cima i0_suppssof1 f4_suppssof1 i0_suppssof1 a_sup_set_class f2_suppssof1 a_cfv i0_suppssof1 a_sup_set_class f3_suppssof1 a_cfv f7_suppssof1 a_co a_cmpt a_ccnv a_cvv f11_suppssof1 a_csn a_cdif a_cima f6_suppssof1 p_eqsstrd $.
$}


